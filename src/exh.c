// exh.c -- EXHAUSTIVE search of rotation-symmetric spread-k circuit codes (S134).
// Class: cycle invariant under g(v) = rot1(v) ^ t acting as shift by L (v_{i+L} = g(v_i)), N = R*L,
// R = order of g (n for even t, 2n for odd t). WLOG v_0 = 0 (translate), c = 1 (relabel coords), and
// t canonical under coordinate rotation (conjugation by rot fixes 0 and rotates t).
// For each t: complete DFS over paths 0 = u_0, u_1, ... with exact pruning wherever the cyclic distance
// is provably >= k (L unknown: L >= s + H(u_s, t)); closing (u_{s-1} adjacent to t) validated EXACTLY
// with the full symmetric check. Reports max N per t and over all t.
// usage: exh n k [tlo thi]   env: ONLYT=hex (single t), RCLASS=0|1|2 (both|even t|odd t), MAXNODES
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

static int n, k, R; static uint32_t t, MASK;
static inline int H(uint32_t a, uint32_t b){ return __builtin_popcount(a^b); }
static inline uint32_t rot(uint32_t v){ return ((v<<1)|(v>>(n-1))) & MASK; }
static inline uint32_t g(uint32_t v){ return rot(v) ^ t; }
static uint32_t cmin(uint32_t x){ uint32_t y = x, m = x; for (int i=1;i<n;i++){ y = rot(y); if (y < m) m = y; } return m; }
static int CANONP = 1; static long npr;
static int canon(uint32_t x){ return cmin(x) == x; }
static int cdist(int i, int j, int NN){ int d = abs(i-j); return d < NN-d ? d : NN-d; }

#define MAXS 4096
static uint32_t seg[MAXS]; static uint32_t im[MAXS][72];
static uint32_t *tmpc; static long nodes, maxnodes; static int bestN, bestL, ncl[MAXS]; static long nclose;
static uint32_t bestseg[MAXS];

static int build(uint32_t *out, int LL){
  int M = 0;
  for (int r=0;;r++){
    for (int i=0;i<LL;i++){ if (M >= (1<<n)) return 0; out[M] = r==0 ? seg[i] : g(out[M-LL]); M++; }
    if (g(out[M-LL]) == out[0]) return M;
    if (r > 4*n) return 0;
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
      int fwd = dt + m, bwd = 2*s + dt - m;   // j=1: L+m-s >= dt+m ; j=R-1: s+L-m >= 2s+dt-m
      for (int j=1;j<R;j++){
        int lb = (j==1) ? fwd : (j==R-1 ? bwd : s+dt);
        if (R==2 && bwd < lb) lb = bwd;
        if (lb >= k && H(x, im[m][j]) < k){ ok = 0; break; } } }
    if (!ok) continue;
    if (CANONP){   // base-point canonicity: any cycle vertex y as base gives t' = cmin(t^y^rot y); prune if < t
      if (cmin(t ^ x ^ rot(x)) < t){ npr++; continue; }
      if (CANONP > 1){ for (int j=1;j<R;j++){ uint32_t z = im[s][j]; if (cmin(t ^ z ^ rot(z)) < t){ ok = 0; break; } }
        if (!ok){ npr++; continue; } } }
    seg[s] = x; dfs(s+1);
    if (maxnodes && nodes > maxnodes) return;
  }
}
static double now(void){ struct timespec ts; clock_gettime(CLOCK_MONOTONIC,&ts); return ts.tv_sec+1e-9*ts.tv_nsec; }

int main(int argc, char **argv){
  n = atoi(argv[1]); k = atoi(argv[2]); MASK = (1u<<n)-1;
  uint32_t tlo = argc>3 ? strtoul(argv[3],0,16) : 1, thi = argc>4 ? strtoul(argv[4],0,16) : MASK;
  int rc = getenv("RCLASS") ? atoi(getenv("RCLASS")) : 0;
  if (getenv("CANONP")) CANONP = atoi(getenv("CANONP"));
  maxnodes = getenv("MAXNODES") ? atol(getenv("MAXNODES")) : 0;
  if (getenv("ONLYT")) tlo = thi = strtoul(getenv("ONLYT"),0,16);
  tmpc = malloc(4u<<n);
  int gbest = 0; long gnodes = 0; double t0 = now();
  int STRIDE = getenv("STRIDE") ? atoi(getenv("STRIDE")) : 1, OFF = getenv("OFF") ? atoi(getenv("OFF")) : 0, ci = -1;
  for (uint32_t tt = tlo; tt <= thi; tt++){
    if (!canon(tt)) continue;
    ci++; if (ci % STRIDE != OFF) continue;
    int odd = __builtin_popcount(tt) & 1;
    if (rc == 1 && odd) continue; if (rc == 2 && !odd) continue;
    t = tt; R = odd ? 2*n : n;
    // order of g must be R on v0=0: g^j(0) != 0 for j<R (else 0 is periodic: invalid)
    nodes = 0; bestN = 0; bestL = 0; nclose = 0; memset(ncl, 0, sizeof ncl);
    seg[0] = 0; { uint32_t y = 0; for (int j=1;j<R;j++){ y = g(y); im[0][j] = y; } } double t1 = now();
    dfs(1);
    gnodes += nodes; if (bestN > gbest) gbest = bestN;
    printf("t %x R %d bestN %d L %d nodes %ld closes %ld secs %.2f", t, R, bestN, bestL, nodes, nclose, now()-t1);
    if (maxnodes && nodes > maxnodes) printf(" TRUNCATED");
    printf("\n");
    if (bestN){ printf("  seg"); for (int i=0;i<bestL;i++) printf(" %x", bestseg[i]); printf("\n"); }
    fflush(stdout);
  }
  printf("# n %d k %d range %x-%x MAX N %d total nodes %ld secs %.1f\n", n, k, tlo, thi, gbest, gnodes, now()-t0);
  return 0;
}
