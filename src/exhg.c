// exhg.c -- S135: EXHAUSTIVE search of spread-k circuit codes invariant under g(v) = sigma(v) ^ t, sigma = any
// coordinate permutation given by its CYCLE TYPE (env SIGMA="8,8" etc; default n = rotation, then = exh.c).
// v_{i+L} = g(v_i), N = R*L, R = order of g. WLOG v_0 = 0; t canonical under the centralizer subgroup C
// (independent rotations of each cycle x permutations of equal-length cycles; if |C| > GMAX only rotations).
// Base-point canonicity prune: base y gives t' = t ^ y ^ sigma(y); prune if min_C(t') < t.
// usage: exhg n k [tlo thi]   env: SIGMA, ONLYT=hex, MAXNODES, CANONP, STRIDE/OFF, GMAX, MINR (skip t with R<MINR)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

static int n, k, R; static uint32_t t, MASK;
static int perm[32];          // sigma: bit b -> bit perm[b]
static uint32_t *sigT;        // table sigma(v)
static inline int H(uint32_t a, uint32_t b){ return __builtin_popcount(a^b); }
static uint32_t sig_slow(uint32_t v){ uint32_t w = 0; for (int b=0;b<n;b++) if (v>>b&1) w |= 1u<<perm[b]; return w; }
static inline uint32_t sig(uint32_t v){ return sigT[v]; }
static inline uint32_t g(uint32_t v){ return sig(v) ^ t; }
// centralizer group elements as bit permutations
static int ng; static unsigned char (*grp)[32];
static uint32_t applyp(unsigned char *p, uint32_t v){ uint32_t w = 0; while (v){ int b = __builtin_ctz(v); v &= v-1; w |= 1u<<p[b]; } return w; }
static uint32_t cmin(uint32_t x){ uint32_t m = x; for (int i=0;i<ng;i++){ uint32_t y = applyp(grp[i], x); if (y < m) m = y; } return m; }
static int CANONP = 1; static long npr;
static int cdist(int i, int j, int NN){ int d = abs(i-j); return d < NN-d ? d : NN-d; }

#define MAXS 4096
#define MAXR 512
static uint32_t seg[MAXS]; static uint32_t (*im)[MAXR];
static uint32_t *tmpc; static long nodes, maxnodes; static int bestN, bestL, ncl[MAXS]; static long nclose;
static uint32_t bestseg[MAXS];

static int build(uint32_t *out, int LL){
  int M = 0;
  for (int r=0;;r++){
    for (int i=0;i<LL;i++){ if (M >= (1<<n)) return 0; out[M] = r==0 ? seg[i] : g(out[M-LL]); M++; }
    if (g(out[M-LL]) == out[0]) return M;
    if (r > MAXR) return 0;
  }
}
static int valid_sym(uint32_t *cy, int NN, int LL){
  if (NN < 2*k) return 0;
  for (int i=0;i<LL;i++){
    if (H(cy[i], cy[(i+1)%NN]) != 1) return 0;
    for (int j=0;j<NN;j++){ if (j==i) continue; int dc = cdist(i,j,NN), dh = H(cy[i],cy[j]);
      if (dc < k ? dh != dc : dh < k) return 0; } }
  return 1;
}
static void dfs(int s){   // seg[0..s-1] placed
  nodes++;
  if (maxnodes && nodes > maxnodes) return;
  uint32_t head = seg[s-1];
  if (s >= 2 && H(head, t) == 1){
    int M = build(tmpc, s);
    if (M == R*s && valid_sym(tmpc, M, s)){ nclose++; ncl[s]++;
      if (M > bestN){ bestN = M; bestL = s; memcpy(bestseg, seg, 4*s); } }
  }
  if (s >= MAXS-1) return;
  for (int b=0;b<n;b++){ uint32_t x = head ^ (1u<<b);
    if (x == t) continue;
    int ok = 1;
    for (int i=0;i<s;i++){ int d = s-i, h = H(x,seg[i]); if (d < k ? h != d : h < k){ ok=0; break; } }
    if (!ok) continue;
    int dt = H(x, t); if (dt < 1) dt = 1;     // L >= s + dt
    uint32_t y = x;
    for (int j=1;j<R;j++){ y = g(y); im[s][j] = y; if (s+dt >= k && H(x,y) < k){ ok = 0; break; } }
    if (!ok) continue;
    for (int m=0; m<s && ok; m++){
      int fwd = dt + m, bwd = 2*s + dt - m;
      for (int j=1;j<R;j++){
        int lb = (j==1) ? fwd : (j==R-1 ? bwd : s+dt);
        if (R==2 && bwd < lb) lb = bwd;
        if (lb >= k && H(x, im[m][j]) < k){ ok = 0; break; } } }
    if (!ok) continue;
    if (CANONP){
      if (cmin(t ^ x ^ sig(x)) < t){ npr++; continue; }
      if (CANONP > 1){ for (int j=1;j<R;j++){ uint32_t z = im[s][j]; if (cmin(t ^ z ^ sig(z)) < t){ ok = 0; break; } }
        if (!ok){ npr++; continue; } } }
    seg[s] = x; dfs(s+1);
    if (maxnodes && nodes > maxnodes) return;
  }
}
static double now(void){ struct timespec ts; clock_gettime(CLOCK_MONOTONIC,&ts); return ts.tv_sec+1e-9*ts.tv_nsec; }

// build centralizer: cycles (start,len); elements = per-cycle rotation x (optionally) permutations of equal-len cycles
static int ncyc, cst[32], clen[32];
static long GMAX = 200000;
static void gen_rot(int ci, unsigned char *base, int full){
  // recursive over cycles, choosing rotation amount; base maps bits
  if (ci == ncyc){ memcpy(grp[ng++], base, 32); return; }
  for (int r=0;r<clen[ci];r++){
    unsigned char b2[32]; memcpy(b2, base, 32);
    for (int i=0;i<clen[ci];i++){ int src = cst[ci]+i; b2[src] = base[cst[ci] + (i + r) % clen[ci]]; }
    gen_rot(ci+1, b2, full);
  }
}
static long fact(int m){ long f=1; for(int i=2;i<=m;i++) f*=i; return f; }
// enumerate permutations of cycles of equal length: done by composing with all orderings
static int cyc_perm[32]; static unsigned char (*pgrp)[32]; static int npg;
static void gen_cperm(int ci, int *used, unsigned char *base){
  if (ci == ncyc){ memcpy(pgrp[npg++], base, 32); return; }
  for (int cj=0;cj<ncyc;cj++){ if (used[cj] || clen[cj]!=clen[ci]) continue; used[cj]=1;
    unsigned char b2[32]; memcpy(b2, base, 32);
    for (int i=0;i<clen[ci];i++) b2[cst[ci]+i] = cst[cj]+i;
    gen_cperm(ci+1, used, b2); used[cj]=0; }
}

int main(int argc, char **argv){
  n = atoi(argv[1]); k = atoi(argv[2]); MASK = (1u<<n)-1;
  // cycle type
  char sbuf[256]; if (getenv("SIGMA")) snprintf(sbuf, sizeof sbuf, "%s", getenv("SIGMA")); else snprintf(sbuf, sizeof sbuf, "%d", n);
  { int pos = 0; char *tok = strtok(sbuf, ",");
    while (tok){ int c = atoi(tok); cst[ncyc] = pos; clen[ncyc] = c; ncyc++; pos += c; tok = strtok(0, ","); }
    if (pos != n){ fprintf(stderr, "SIGMA sums to %d != n\n", pos); return 1; } }
  // sigma: within cycle, bit cst+i -> cst+(i+1)%len  (matches rot: bit b -> b+1 mod n for type [n])
  for (int c=0;c<ncyc;c++) for (int i=0;i<clen[c];i++) perm[cst[c]+i] = cst[c] + (i+1)%clen[c];
  sigT = malloc(4ul<<n); for (uint32_t v=0; v<=MASK; v++) sigT[v] = sig_slow(v);
  if (getenv("GMAX")) GMAX = atol(getenv("GMAX"));
  long nrot = 1; for (int c=0;c<ncyc;c++) nrot *= clen[c];
  long ncp = 1; { int done[32]={0}; for (int c=0;c<ncyc;c++){ if (done[c]) continue; int m=0; for (int d=c; d<ncyc; d++) if (clen[d]==clen[c]){ done[d]=1; m++; } ncp *= fact(m);} }
  int usecp = nrot*ncp <= GMAX;
  if (nrot > GMAX){ fprintf(stderr, "rotation group too big %ld\n", nrot); return 1; }
  grp = malloc(32*(size_t)(usecp ? nrot*ncp : nrot));
  { unsigned char id[32]; for (int i=0;i<32;i++) id[i]=i; ng = 0; gen_rot(0, id, 0); }
  if (usecp && ncp > 1){
    pgrp = malloc(32*(size_t)ncp); npg = 0; int used[32]={0}; unsigned char id[32]; for (int i=0;i<32;i++) id[i]=i;
    gen_cperm(0, used, id);
    int nr = ng; unsigned char (*g2)[32] = malloc(32*(size_t)nr*npg); int m = 0;
    for (int a=0;a<nr;a++) for (int b=0;b<npg;b++){ for (int i=0;i<n;i++) g2[m][i] = pgrp[b][grp[a][i]]; m++; }
    free(grp); grp = g2; ng = m;
  }
  // check every group element commutes with sigma
  for (int e=0;e<ng;e++) for (int b=0;b<n;b++) if (grp[e][perm[b]] != perm[grp[e][b]]){ fprintf(stderr,"centralizer bug\n"); return 1; }
  fprintf(stderr, "# sigma %s  |C| = %d (cycle perms %s)\n", getenv("SIGMA")?getenv("SIGMA"):"rot", ng, usecp?"yes":"no");
  im = malloc(sizeof(*im) * MAXS);
  uint32_t tlo = argc>3 ? strtoul(argv[3],0,16) : 0, thi = argc>4 ? strtoul(argv[4],0,16) : MASK;
  if (getenv("CANONP")) CANONP = atoi(getenv("CANONP"));
  maxnodes = getenv("MAXNODES") ? atol(getenv("MAXNODES")) : 0;
  int MINR = getenv("MINR") ? atoi(getenv("MINR")) : 2;
  if (getenv("ONLYT")) tlo = thi = cmin(strtoul(getenv("ONLYT"),0,16));
  tmpc = malloc(4u<<n);
  int gbest = 0; long gnodes = 0; double t0 = now(); int ntr = 0;
  int STRIDE = getenv("STRIDE") ? atoi(getenv("STRIDE")) : 1, OFF = getenv("OFF") ? atoi(getenv("OFF")) : 0, ci = -1;
  for (uint32_t tt = tlo; tt <= thi; tt++){
    if (cmin(tt) != tt) continue;
    t = tt;
    // order of g: smallest R with sigma^R = id and g^R(0) = 0; also need g^j(0) != 0 for 0<j<R
    int sord = 1; { int ok; do { ok = 1; for (int b=0;b<n;b++){ int x=b; for (int j=0;j<sord;j++) x = perm[x]; if (x!=b){ok=0;break;} } if (!ok) sord++; } while(!ok); }
    uint32_t y = 0; int bad = 0; R = 0;
    for (int j=1;j<=2*sord;j++){ y = g(y); if (y == 0){ if (j % sord){ bad = 1; } else { R = j; } break; } }
    if (bad || R == 0 || R < MINR || R > MAXR-1) continue;
    ci++; if (ci % STRIDE != OFF) continue;
    nodes = 0; bestN = 0; bestL = 0; nclose = 0; memset(ncl, 0, sizeof ncl);
    seg[0] = 0; { uint32_t z = 0; for (int j=1;j<R;j++){ z = g(z); im[0][j] = z; } } double t1 = now();
    dfs(1);
    gnodes += nodes; if (bestN > gbest) gbest = bestN;
    printf("t %x R %d bestN %d L %d nodes %ld closes %ld secs %.2f", t, R, bestN, bestL, nodes, nclose, now()-t1);
    if (maxnodes && nodes > maxnodes){ printf(" TRUNCATED"); ntr++; }
    printf("\n");
    if (bestN){ printf("  seg"); for (int i=0;i<bestL;i++) printf(" %x", bestseg[i]); printf("\n"); }
    fflush(stdout);
  }
  printf("# n %d k %d sigma %s range %x-%x MAX N %d total nodes %ld truncated %d secs %.1f\n", n, k,
         getenv("SIGMA")?getenv("SIGMA"):"rot", tlo, thi, gbest, gnodes, ntr, now()-t0);
  return 0;
}
