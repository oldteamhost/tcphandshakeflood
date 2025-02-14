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
