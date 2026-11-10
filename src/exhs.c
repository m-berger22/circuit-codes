// exhs.c -- S160: SNAKE (open path) variant of exhr2.c: longest reflection-symmetric k-snake, centre = fixed vertex (A) or flipped edge (B).
// (original header follows)
// exhr.c -- S160: EXHAUSTIVE search of spread-k circuit codes with a REFLECTION symmetry (not covered by exh/exhg,
// which need a rotation v_{i+L} = g(v_i)).  h(v) = sigma(v) ^ t, sigma = m disjoint coordinate swaps (bits 2j,2j+1).
//  type A (vertex reflection): v_{-i} = h(v_i), h = sigma, v_0 = 0 (fixed);   closes at the next fixed point v_H, N = 2H.
//  type B (edge reflection):   v_{1-i} = h(v_i), h = sigma ^ e_{n-1}, v_1 = 0, v_0 = e_{n-1}; closes when a(x)=0, N = 2H.
// (up to conjugation these are all reflections: t can be moved off the swapped pairs, fixed points need t=0, a flipped
//  edge needs weight(t)=1.)  a(x) = number of asymmetric pairs = steps still needed, so N >= 2(s+a).
// Canonical labelling under the centralizer (S_2 wr S_m) x S_fixed: pairs / fixed coords are first used in index order,
// first touch of a pair uses its even bit.
// usage: exhr n k m A|B   env MAXNODES, COUNT=1 (validate+count every closure; default only N > best), ALL=1 (with COUNT)
// print closure counts per N, SEED=s RESTARTS=r: random bit order, r dives of MAXNODES nodes (stochastic, NOT exhaustive)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
static int n, k, m, typeB, nfix, fbit;
static uint32_t tvec, pairmaskE; // even bits of pairs
static inline uint32_t sig(uint32_t v){ uint32_t e = v & pairmaskE, o = (v>>1) & pairmaskE; uint32_t rest = v & ~(pairmaskE*3u); return rest | (e<<1) | o; }
static inline uint32_t hh(uint32_t v){ return sig(v) ^ tvec; }
static inline int asym(uint32_t v){ return __builtin_popcount((v ^ (v>>1)) & pairmaskE); }
static inline int H(uint32_t a, uint32_t b){ return __builtin_popcount(a^b); }
#define MAXS 2048
static uint32_t p[MAXS], q[MAXS], cyc[2*MAXS], best[2*MAXS];
static int COUNT, RAND, NOCANON; static uint64_t rs = 88172645463325252ull;
static inline uint64_t rnd(void){ rs ^= rs<<13; rs ^= rs>>7; rs ^= rs<<17; return rs; }
static long nodes, maxnodes, nclose, ncl[2*MAXS]; static int bestN;
static int valid(uint32_t *c, int N){
  if (N < 2*k) return 0;
  for (int i=0;i<N;i++){ if (H(c[i], c[(i+1)%N]) != 1) return 0;
    for (int j=i+1;j<N;j++){ int d=j-i; if (N-d<d) d=N-d; int dh=H(c[i],c[j]); if (d<k ? dh!=d : dh<k) return 0; } }
  return 1;
}
static inline int okpair(uint32_t x, uint32_t y, int d){ int dh = H(x,y); return d < k ? dh == d : dh >= k; }
static int bestS; static uint32_t bestp[MAXS];
static void dfs(int s, int ntp, int nft){  // p[first..s] placed; symmetric OPEN path (snake): edges = 2s (A) or 2s-1 (B)
  nodes++; if (maxnodes && nodes > maxnodes) return;
  if (s > bestS){ bestS = s; memcpy(bestp, p, 4*(s+1)); }
  uint32_t head = p[s]; int first = typeB ? 1 : 0;
  for (int b=0;b<n;b++){
    int ntp2 = ntp, nft2 = nft;
    if (NOCANON) { }
    else if (b < 2*m){ int j = b>>1; if (j > ntp) continue; if (j == ntp){ if (b&1) continue; ntp2++; } }
    else if (typeB && b == fbit) { }
    else { int j = b - 2*m; if (j > nft) continue; if (j == nft) nft2++; }
    uint32_t x = head ^ (1u<<b); int s1 = s+1, ok = 1;
    for (int j=s; j>=first && ok; j--){
      if (!okpair(x, p[j], s1-j)) ok = 0;
      else if (!okpair(x, q[j], typeB ? s1+j-1 : s1+j)) ok = 0;
    }
    if (!ok) continue;
    uint32_t hx = hh(x);
    if (!okpair(x, hx, typeB ? 2*s1-1 : 2*s1)) continue;
    if (s1 >= MAXS-1) continue;
    p[s1] = x; q[s1] = hx; dfs(s1, ntp2, nft2);
    if (maxnodes && nodes > maxnodes) return;
  }
}
static double now(void){ struct timespec ts; clock_gettime(CLOCK_MONOTONIC,&ts); return ts.tv_sec+1e-9*ts.tv_nsec; }
int main(int argc, char **argv){
  if (argc < 5){ fprintf(stderr, "usage: exhr n k m A|B\n"); return 1; }
  n = atoi(argv[1]); k = atoi(argv[2]); m = atoi(argv[3]); typeB = argv[4][0]=='B';
  if (2*m > n || (typeB && 2*m >= n) || m < 1){ fprintf(stderr, "bad m\n"); return 1; }
  for (int j=0;j<m;j++) pairmaskE |= 1u<<(2*j);
  fbit = n-1; tvec = typeB ? 1u<<fbit : 0;
  maxnodes = getenv("MAXNODES") ? atol(getenv("MAXNODES")) : 0;
  COUNT = getenv("COUNT") != 0; NOCANON = getenv("NOCANON") != 0;  // NOCANON=1: no symmetry breaking (exhaustiveness test) RAND = getenv("SEED") ? atoi(getenv("SEED")) : 0; if (RAND) rs ^= (uint64_t)RAND * 0x9E3779B97F4A7C15ull;
  int RESTARTS = getenv("RESTARTS") ? atoi(getenv("RESTARTS")) : 1; long tot = 0;   // RAND: RESTARTS x MAXNODES random-order dives
  double t0 = now();
  for (int r=0;r<RESTARTS;r++){ tot += nodes; nodes = 0;
  if (!typeB){ p[0] = 0; q[0] = 0; dfs(0, 0, 0); }
  else { p[1] = 0; q[1] = tvec; dfs(1, 0, 0); }
  if (!RAND) break; }
  if (RAND && RESTARTS > 1) nodes += tot;
  int E = typeB ? 2*bestS-1 : 2*bestS;
  printf("n %d k %d m %d type %c bestE %d nodes %ld secs %.2f%s\n", n, k, m, typeB?'B':'A', E, nodes, now()-t0, (maxnodes && nodes > maxnodes) ? " TRUNCATED" : "");
  printf("code"); int f0 = typeB ? 1 : 0;
  for (int i=bestS;i>=f0;i--) printf(" %x", hh(bestp[i])); for (int i=f0+(typeB?0:1);i<=bestS;i++) printf(" %x", bestp[i]); printf("\n");
  return 0;
}
