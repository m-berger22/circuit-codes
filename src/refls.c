// refls.c -- S160: SNAKE (open path) version of refl.c. Half path u[0..M]: u[0] = FREE outer end, u[M] = centre (fixed by h
// for type A, moved to a neighbour for type B). Moves: interior window, CENTRE window [a,M] (as refl's end window), and
// FREE-END window [0,b] (replace the last b steps by Wn = b+D steps, any parity). Input: exhs output ('code' line = full path).
// (refl.c header follows)
// refl.c -- S160: REFLECTION-symmetric spread-k circuit codes by windowed rerouting (local search inside the classes
// that exhr2.c searches exhaustively).  h(v) = sigma(v) ^ t, sigma = m coordinate swaps (bits 2j,2j+1);
//   type A: t = 0, half path u[0..M], u[0] and u[M] fixed by h, cycle = u[0..M] + h(u[M-1..1]), N = 2M
//   type B: t = e_{n-1}, half path u[0..M], h(u[0]) adj u[0], h(u[M]) adj u[M], cycle = u[0..M] + h(u[M..0]), N = 2M+2
// Move: window [a,b] of the half path (W=b-a >= k), or an END window [a,M] (the end may move to any vertex with no
// asymmetric pair); DFS a replacement of EXACT length W+D (D in -2,0,2,4), every new vertex checked exactly against the
// whole new cycle (positions are known because the target length is fixed); the mirror half follows automatically.
// Every accepted cycle is re-validated in full (O(N^2/2)); 'BUG' lines = a move passed the DFS but failed that.
// usage: refl n k m A|B infile   (infile: '#' comments, or exhr2 output with a 'code ...' line; full cycle, half first)
// env: SECS(60) NODES(3000) WMAX(3k+8) SEED OUT PLAT(.3) SHRINK(.02) P4(.15)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
static int n, k, m, typeB; static uint32_t tvec, pairmaskE;
static inline uint32_t sig(uint32_t v){ uint32_t e = v & pairmaskE, o = (v>>1) & pairmaskE; uint32_t rest = v & ~(pairmaskE*3u); return rest | (e<<1) | o; }
static inline uint32_t hh(uint32_t v){ return sig(v) ^ tvec; }
static inline int asym(uint32_t v){ return __builtin_popcount((v ^ (v>>1)) & pairmaskE); }
static inline int H(uint32_t a, uint32_t b){ return __builtin_popcount(a^b); }
static uint64_t rng = 88172645463325252ULL;
static inline uint64_t rnd(void){ rng ^= rng<<13; rng ^= rng>>7; rng ^= rng<<17; return rng; }
static double now(void){ struct timespec ts; clock_gettime(CLOCK_MONOTONIC,&ts); return ts.tv_sec+1e-9*ts.tv_nsec; }
#define MAXM 200000
static uint32_t u[MAXM], hu[MAXM], nu[MAXM], path[4096], hpath[4096], full[2*MAXM+4];
static int M;
static inline int NofM(int MM){ return typeB ? 2*MM+2 : 2*MM; }
static int buildfull(uint32_t *hp, int MM, uint32_t *out){
  int c = 0; for (int i=0;i<=MM;i++) out[c++] = hp[i];
  if (typeB){ for (int i=MM;i>=0;i--) out[c++] = hh(hp[i]); } else { for (int i=MM-1;i>=0;i--) out[c++] = hh(hp[i]); }
  return c;
}
static int validfull(uint32_t *c, int N){
  for (int i=0;i<N;i++){ if (i+1<N && H(c[i], c[i+1]) != 1) return 0;
    for (int j=i+1;j<N;j++){ int d=j-i; int dh=H(c[i],c[j]); if (d<k ? dh!=d : dh<k) return 0; } }
  return 1;
}
// DFS state
static int wa, wb, Wn, Np, Delta, endwin; static long nodes, maxnodes;
static inline int test(uint32_t x, uint32_t y, int pi, int pj){
  int d = pi > pj ? pi - pj : pj - pi; int dh = H(x,y);
  return d < k ? dh == d : dh >= k;
}
static inline int mpos(int p){ return typeB ? Np-1-p : Np-p; }
static int check(uint32_t x, int d){   // x is new vertex number d of the window (position wa+d)
  int pi = wa + d; uint32_t hx = hh(x);
  // new path vertices so far (nearest first)
  for (int e=d-1;e>=1;e--){ if (!test(x, path[e], pi, wa+e)) return 0; if (!test(x, hpath[e], pi, mpos(wa+e))) return 0; }
  // own mirror (skip the type-A end vertex, which is its own mirror)
  if (!(endwin && d == Wn && !typeB)){ if (!test(x, hx, pi, mpos(pi))) return 0; }
  for (int j=wa;j>=0;j--){ if (!test(x, u[j], pi, j)) return 0; if (!test(x, hu[j], pi, mpos(j))) return 0; }
  if (!endwin) for (int j=wb;j<=M;j++){ int pj = j + Delta; if (!test(x, u[j], pi, pj)) return 0;
    if (!(j==M && !typeB)) if (!test(x, hu[j], pi, mpos(pj))) return 0; }
  return 1;
}
static int dfs(int d, uint32_t prev){  // place vertex number d (1..Wn)
  if (++nodes > maxnodes) return 0;
  int off = rnd() % n;
  for (int bb=0;bb<n;bb++){ int b = bb+off; if (b>=n) b-=n; uint32_t x = prev ^ (1u<<b);
    int rem = Wn - d;
    if (!endwin){ int dt = H(x, u[wb]); if (dt > rem) continue;
      if (rem == 0){ path[d] = x; return 1; } if (dt == 0) continue; }
    else { int a = asym(x); if (a > rem) continue; if (a == 0 && rem > 0) continue; }
    if (!check(x, d)) continue;
    path[d] = x; hpath[d] = hh(x);
    if (rem == 0) return 1;
    if (dfs(d+1, x)) return 1;
    if (nodes > maxnodes) return 0;
  }
  return 0;
}
// FREE-END move: keep u[fb..M], grow Wn new vertices outward from u[fb]. Positions = distance from the centre along the half.
static int fb;
static inline int testc(uint32_t x, uint32_t y, int cx, int cy){ int d = cx > cy ? cx - cy : cy - cx; int dh = H(x,y); return d < k ? dh == d : dh >= k; }
static inline int mc(int c){ return typeB ? -c-1 : -c; }
static int dfsfree(int d, uint32_t prev){
  if (++nodes > maxnodes) return 0;
  int off = rnd() % n;
  for (int bb=0;bb<n;bb++){ int b = bb+off; if (b>=n) b-=n; uint32_t x = prev ^ (1u<<b); int cx = M - fb + d, ok = 1;
    for (int e=d-1;e>=1 && ok;e--){ int ce = M - fb + e; if (!testc(x, path[e], cx, ce) || !testc(x, hpath[e], cx, mc(ce))) ok = 0; }
    for (int j=fb;j<=M && ok;j++){ int cj = M - j; if (!testc(x, u[j], cx, cj)) ok = 0; else if (!(j==M && !typeB) && !testc(x, hu[j], cx, mc(cj))) ok = 0; }
    if (!ok) continue;
    uint32_t hx = hh(x); if (!testc(x, hx, cx, mc(cx))) continue;
    path[d] = x; hpath[d] = hx;
    if (d == Wn) return 1;
    if (dfsfree(d+1, x)) return 1;
    if (nodes > maxnodes) return 0;
  }
  return 0;
}
static void reverse_half(void){ for (int i=0,j=M;i<j;i++,j--){ uint32_t tt=u[i]; u[i]=u[j]; u[j]=tt; } for (int i=0;i<=M;i++) hu[i]=hh(u[i]); }
int main(int argc, char **argv){
  if (argc < 6){ fprintf(stderr, "usage: refl n k m A|B infile\n"); return 1; }
  n = atoi(argv[1]); k = atoi(argv[2]); m = atoi(argv[3]); typeB = argv[4][0]=='B';
  for (int j=0;j<m;j++) pairmaskE |= 1u<<(2*j);
  tvec = typeB ? 1u<<(n-1) : 0;
  double SECS = getenv("SECS") ? atof(getenv("SECS")) : 60; long NODES = getenv("NODES") ? atol(getenv("NODES")) : 3000;
  int WMAX = getenv("WMAX") ? atoi(getenv("WMAX")) : 3*k+8; double PLAT = getenv("PLAT") ? atof(getenv("PLAT")) : 0.3;
  double SHRINK = getenv("SHRINK") ? atof(getenv("SHRINK")) : 0.02, P4 = getenv("P4") ? atof(getenv("P4")) : 0.15;
  if (getenv("SEED")) rng ^= (uint64_t)atol(getenv("SEED")) * 0x9E3779B97F4A7C15ull; for (int i=0;i<10;i++) rnd();
  // read
  FILE *f = fopen(argv[5], "r"); if (!f){ perror("infile"); return 1; }
  static char line[1<<22]; int cnt = 0;
  while (fgets(line, sizeof line, f)){ char *s = line; if (*s=='#') continue; if (!strncmp(s,"code",4)) s += 4; else if (*s=='n' || *s==' ' ) { if (*s=='n') continue; }
    char *tok = strtok(s, " \t\n"); while (tok){ full[cnt++] = strtoul(tok, 0, 16); tok = strtok(0, " \t\n"); } }
  fclose(f);
  int N = cnt; M = typeB ? N/2 - 1 : (N-1)/2;
  for (int i=0;i<=M;i++){ u[i] = full[N-1-i]; hu[i] = hh(u[i]); }
  { int c = buildfull(u, M, full); if (c != N || !validfull(full, N) || (endwin=0)){ fprintf(stderr, "input is not a valid class member (N=%d rebuilt %d)\n", N, c); return 1; } }
  if (asym(u[M])){ fprintf(stderr, "bad centre\n"); return 1; }
  fprintf(stderr, "start N=%d M=%d\n", N, M);
  double t0 = now(), tlast = t0; long it = 0, acc = 0, accp = 0, bug = 0; int bestN = N; const char *OUT = getenv("OUT");
  static uint32_t bestfull[2*MAXM+4]; memcpy(bestfull, full, 4*N);
  while (now() - t0 < SECS){
    it++;
    if (rnd() % 3 == 0){   // free-end move
      int b = rnd() % (WMAX+1); if (b > M-1) b = M-1; if (b < 0) continue;
      double r = (rnd() % 1000000) / 1e6; int D = r < SHRINK ? -1 : r < SHRINK+PLAT ? 0 : r < SHRINK+PLAT+0.4 ? 1 : 2;
      fb = b; Wn = b + D; if (Wn < 1 || Wn > 4000) continue;
      nodes = 0; maxnodes = NODES; path[0] = u[fb];
      if (!dfsfree(1, u[fb])) continue;
      int Mp = M - b + Wn, c = 0; for (int e=Wn;e>=1;e--) nu[c++] = path[e]; for (int j=fb;j<=M;j++) nu[c++] = u[j];
      if (c != Mp+1){ bug++; continue; }
      int NN = buildfull(nu, Mp, full);
      if (!validfull(full, NN)){ bug++; if (bug < 5) fprintf(stderr, "BUG: free-end move failed full validation (D=%d b=%d)\n", D, b); continue; }
      memcpy(u, nu, 4*(Mp+1)); M = Mp; for (int i=0;i<=M;i++) hu[i] = hh(u[i]);
      if (D > 0) acc++; else accp++;
      if (NN > bestN){ bestN = NN; memcpy(bestfull, full, 4*NN); }
      continue;
    }
    double r = (rnd() % 1000000) / 1e6;
    Delta = r < SHRINK ? -2 : r < SHRINK+PLAT ? 0 : r < SHRINK+PLAT+P4 ? 4 : 2;
    int W = k + rnd() % (WMAX - k + 1);
    endwin = (rnd() % (M/ (W>0?W:1) + 2)) == 0;     // end windows about as often as any other position
    if (endwin){ if (W > M) W = M; wa = M - W; wb = M; if (2*W + (typeB?1:0) < k) continue; }
    else { if (W > M) continue; wa = rnd() % (M - W + 1); wb = wa + W; }
    Wn = W + Delta; if (Wn < 1 || Wn > 4000) continue;
    if (!endwin && H(u[wa], u[wb]) > Wn) continue;
    int Mp = M + Delta; Np = NofM(Mp); if (Mp < 1) continue;
    nodes = 0; maxnodes = NODES; path[0] = u[wa];
    if (!dfs(1, u[wa])) continue;
    if (Delta == 0){ int same = 1; for (int e=1;e<Wn;e++) if (path[e] != u[wa+e]){ same = 0; break; } if (same && !endwin) continue;
      if (same && endwin && path[Wn] == u[M]) continue; }
    // splice
    int c = 0; for (int j=0;j<=wa;j++) nu[c++] = u[j]; for (int e=1;e<=Wn;e++) nu[c++] = path[e];
    if (!endwin) for (int j=wb+1;j<=M;j++) nu[c++] = u[j];
    if (c != Mp+1){ bug++; continue; }
    int NN = buildfull(nu, Mp, full);
    if (!validfull(full, NN)){ bug++; if (bug < 5) fprintf(stderr, "BUG: move failed full validation (D=%d W=%d end=%d)\n", Delta, W, endwin); continue; }
    memcpy(u, nu, 4*(Mp+1)); M = Mp; for (int i=0;i<=M;i++) hu[i] = hh(u[i]);
    if (Delta > 0) acc++; else accp++;
    if (NN > bestN){ bestN = NN; memcpy(bestfull, full, 4*NN);
      if (0){ tlast = now(); FILE *o = fopen(OUT, "w"); fprintf(o, "# n %d k %d N %d snake, reflection class m %d type %c (refls.c)\n", n, k, bestN, m, typeB?'B':'A'); for (int i=0;i<bestN;i++) fprintf(o, "%x ", bestfull[i]); fprintf(o, "\n"); fclose(o); } }
  }
  if (OUT){ FILE *o = fopen(OUT, "w"); fprintf(o, "# n %d k %d N %d snake, reflection class m %d type %c (refls.c)\n", n, k, bestN, m, typeB?'B':'A'); for (int i=0;i<bestN;i++) fprintf(o, "%x ", bestfull[i]); fprintf(o, "\n"); fclose(o); }
  printf("n %d k %d m %d type %c bestE %d finalM %d it %ld acc %ld plat %ld bug %ld t %.1f\n", n, k, m, typeB?'B':'A', bestN-1, M, it, acc, accp, bug, now()-t0);
  return 0;
}
