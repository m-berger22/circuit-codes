// sym.c -- SYMMETRIC spread-k circuit codes by windowed rerouting (S133).
// The cycle is invariant under g(v) = rot_c(v) ^ t with v_{i+L} = g(v_i), N = R*L
// (rot_c = rotate the n coordinates left by c; Hood/Paterson-Tuliani k=3,4 records have c=1, R=n).
// State: full cycle cyc[0..N-1]. Move: window [a, a+W] inside one segment (W <= L-2k-2 so the R images
// are disjoint and far apart); DFS a new path a->b checking x against (i) frozen ball counts (everything
// outside all R windows, incl. the images' near sets), (ii) g^j(path vertices so far, incl. x), j=1..R-1.
// Splice all R images at once. Every accepted cycle is validated EXACTLY (O(L*N), symmetry-reduced).
// Bootstrap (segment too short for windows): random DFS over whole segments from v_0, exact closure test.
// usage: sym n k c seed iters [infile]   env: LMIN LMAX NODES PLAT GAIN SECS OUT SHRINK SLACK BNODES LB
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdint.h>

static int n, k, c, N, L, R; static uint32_t t, MASK;
static uint32_t *cyc, *ncyc, *seg;
static uint16_t *cnt; static uint32_t *ball; static int nball;
static uint64_t rng = 88172645463325252ULL;
static inline uint64_t rnd(void){ rng ^= rng<<13; rng ^= rng>>7; rng ^= rng<<17; return rng; }
static inline int H(uint32_t a, uint32_t b){ return __builtin_popcount(a^b); }
static inline uint32_t rot(uint32_t v){ return ((v<<c)|(v>>(n-c))) & MASK; }
static inline uint32_t g(uint32_t v){ return rot(v) ^ t; }
static void addball(uint32_t x, int d){ for (int i=0;i<nball;i++) cnt[x^ball[i]] += d; }
static int cdist(int i, int j, int NN){ int d = abs(i-j); return d < NN-d ? d : NN-d; }

// build full cycle from seg[0..LL-1] with g fixed (global t); returns N or 0 if orbit doesn't close / too long
static int build(uint32_t *out, uint32_t *sg, int LL, long maxN){
  int M = 0;
  for (int r=0;;r++){
    for (int i=0;i<LL;i++){ if (M >= maxN) return 0; uint32_t v = r==0 ? sg[i] : g(out[M-LL]); out[M] = v; M++; }
    uint32_t nx = g(out[M-LL]);
    if (nx == out[0]) return M;
    if (r > 4*n) return 0;
  }
}
// exact validation using symmetry: pairs (i<LL, any j)
static int valid_sym(uint32_t *cy, int NN, int LL){
  if (NN < 2*k) return 0;
  for (int i=0;i<LL;i++){
    if (H(cy[i], cy[(i+1)%NN]) != 1) return 0;
    for (int j=0;j<NN;j++){ if (j==i) continue; int dc = cdist(i,j,NN), dh = H(cy[i],cy[j]);
      if (dc < k ? dh != dc : dh < k) return 0; }
  }
  return 1;
}
static int LOCALV;
// local exact check: only the new window region of segment 0 (indices -(k-2) .. bw+k-2) against everything
static int valid_symloc(uint32_t *cy, int NN, int bw){
  for (int o=-(k-1); o<=bw+k-1; o++){ int i = ((o%NN)+NN)%NN;
    if (H(cy[i], cy[(i+1)%NN]) != 1) return 0;
    for (int j=0;j<NN;j++){ if (j==i) continue; int dc = cdist(i,j,NN), dh = H(cy[i],cy[j]);
      if (dc < k ? dh != dc : dh < k) return 0; } }
  return 1;
}
static int valid_full(uint32_t *cy, int NN){  // independent O(N^2) (used at saves)
  for (int i=0;i<NN;i++){ if (H(cy[i], cy[(i+1)%NN]) != 1) return 0;
    for (int j=i+1;j<NN;j++){ int dc = cdist(i,j,NN), dh = H(cy[i],cy[j]); if (dc < k ? dh != dc : dh < k) return 0; } }
  return 1;
}

// ---- window DFS ----
static uint32_t seq[1<<14]; static int nseq, na, nb;
static uint32_t bnear[64], target_b;
static uint32_t img[1<<14][72];   // img[s][j] = g^j(path vertex s), j=1..R-1
static long nodes, nodelim; static int Lmaxnew;
static uint32_t best[1<<14]; static int bestlen;

static int final_ok(int LW){
  for (int s=1;s<LW;s++){ uint32_t x = seq[na-1+s];
    for (int j=0;j<nb;j++){ int d = (LW-s)+j; int h = H(x,bnear[j]); if (d < k){ if (h != d) return 0; } else if (h < k) return 0; } }
  for (int i=0;i<na;i++) for (int j=0;j<nb;j++){ int d = (na-1-i) + LW + j; int h = H(seq[i], bnear[j]);
      if (d < k){ if (h != d) return 0; } else if (h < k) return 0; }
  return 1;
}
static int symok(uint32_t x, int s){   // x would be path vertex s (0-based index into path); check vs images
  uint32_t im[72]; uint32_t y = x;
  for (int j=1;j<R;j++){ y = g(y); im[j] = y; if (H(x,y) < k) return 0; }
  for (int p=0;p<s;p++) for (int j=1;j<R;j++) if (H(x, img[p][j]) < k) return 0;
  // also x vs images of the target b itself is covered by frozen (images of near sets)
  memcpy(img[s], im, sizeof(uint32_t)*R);
  return 1;
}
static void dfs(int s){
  if (nodes++ > nodelim) return;
  uint32_t head = seq[nseq-1];
  int hb = H(head, target_b);
  if (hb == 1 && s+1 > bestlen && s+1 <= Lmaxnew && final_ok(s+1)){ bestlen = s+1; memcpy(best, seq+na, 4*s); best[s] = target_b; }
  if (s + hb > Lmaxnew) return;
  int nc = 0; uint32_t cand[32];
  for (int b=0;b<n;b++){ uint32_t x = head ^ (1u<<b);
    if (x == target_b || cnt[x]) continue;
    int ok = 1;
    for (int i=0;i<=nseq-k;i++) if (H(x,seq[i])<k){ ok=0; break; }
    if (!ok) continue;
    for (int d=2; d<k && d<=nseq; d++) if (H(x, seq[nseq-d]) != d){ ok=0; break; }
    if (!ok) continue;
    for (int j=0;j<nb;j++){ int h = H(x,bnear[j]); if (h==0 || (h < k && h - j < H(x,target_b))){ ok=0; break; } }
    if (!ok) continue;
    cand[nc++] = x;
  }
  for (int i=1;i<nc;i++){ int j = rnd()%(i+1); uint32_t tt=cand[i]; cand[i]=cand[j]; cand[j]=tt; }
  for (int ci=0;ci<nc;ci++){ uint32_t x = cand[ci];
    if (symok(x, s)){ seq[nseq++] = x; dfs(s+1); nseq--; }
    if (nodes > nodelim) return; }
}

// ---- bootstrap (fixed g): DFS over segments u_0=v0 -> ... with u_L = g(u_0) = target; closing when adjacent ----
static uint32_t bseg[8192]; static long bnodes, bnodelim; static int bbestL, bbestN; static uint32_t *bbest; static int LB;
static uint32_t *tmpc; static int RWANT; static double BGREEDY; static uint32_t btarget;
static uint32_t bimg[8192][72];
static void bdfs(int s){   // bseg[0..s-1] placed (s vertices); head = bseg[s-1]
  if (bnodes++ > bnodelim) return;
  uint32_t head = bseg[s-1];
  if (H(head, btarget) == 1 && s >= 2){   // close: segment = bseg[0..s-1], L' = s
    int M = build(tmpc, bseg, s, 1L<<n);
    if (M > bbestN && (!RWANT || M == RWANT*s) && valid_sym(tmpc, M, s)){ bbestN = M; bbestL = s; memcpy(bbest, tmpc, 4*(size_t)M); }
  }
  if (s >= LB) return;
  int order[32]; for (int i=0;i<n;i++) order[i]=i;
  for (int i=1;i<n;i++){ int j=rnd()%(i+1); int tt=order[i]; order[i]=order[j]; order[j]=tt; }
  if (BGREEDY > 0 && (rnd()%1000) < BGREEDY*1000){   // stable sort by distance to target (random tie-break kept)
    for (int i=1;i<n;i++){ int o=order[i], h=H(head^(1u<<o),btarget), j=i-1;
      while (j>=0 && H(head^(1u<<order[j]),btarget) > h){ order[j+1]=order[j]; j--; } order[j+1]=o; } }
  for (int bi=0;bi<n;bi++){ uint32_t x = head ^ (1u<<order[bi]);
    if (x == btarget) continue;
    int ok = 1;
    for (int i=0;i<s;i++){ int d = s-i, h = H(x,bseg[i]); if (d < k ? h != d : h < k){ ok=0; break; } }
    if (!ok) continue;
    int dt = H(x, btarget); if (dt < 1) dt = 1;   // remaining steps >= dt, so L' >= s + dt
    // images: x at pos s vs g^j(bseg[m]) at jL'+m. j=1: dist >= dt+m (forward), j=R-1 backward >= s+dt+s-m ... use safe bounds
    uint32_t im[72]; uint32_t y = x;
    for (int j=1;j<R && ok;j++){ y = g(y); im[j] = y;
      // x vs g^j(x): positions s and jL'+s: distance >= min(j,R-j)*L' >= s+dt >= k typically
      if ((s+dt) >= k && H(x,y) < k) ok = 0; }
    for (int m=0; m<s && ok; m++){
      int fwd = dt + m;          // lower bound on distance x -> g(bseg[m])   (j=1)
      int bwd = 2*s + dt - m;    // lower bound on distance x -> g^{R-1}(bseg[m]) (j=R-1)
      for (int j=1;j<R;j++){
        int lb = (j==1) ? fwd : (j==R-1 ? bwd : s+dt);
        if (j==1 && R==2 && bwd < lb) lb = bwd;
        if (lb >= k && H(x, bimg[m][j]) < k){ ok = 0; break; } } }
    if (!ok) continue;
    bseg[s] = x; memcpy(bimg[s], im, 4*R); bdfs(s+1);
    if (bnodes > bnodelim) return;
  }
}

static int cntok; static double lastsave, SAVEINT;
static void excl(int a, int W, int d){
  for (int o=-(k-2); o<=W+k-2; o++) addball(cyc[((a+o)%N+N)%N], d);
  for (int j=1;j<R;j++) for (int o=1;o<=W-1;o++) addball(cyc[(a+j*L+o)%N], d);
}
static double now(void){ struct timespec ts; clock_gettime(CLOCK_MONOTONIC,&ts); return ts.tv_sec+1e-9*ts.tv_nsec; }
static void save(const char *fn){
  FILE *f = fopen(fn,"w"); if(!f) return;
  fprintf(f,"# n %d k %d N %d sym c %d R %d L %d t %x\n", n, k, N, c, R, L, t);
  for (int i=0;i<N;i++) fprintf(f,"%x%c", cyc[i], i==N-1?'\n':' ');
  fclose(f);
}

int main(int argc, char **argv){
  if (argc < 6){ fprintf(stderr,"usage: sym n k c seed iters [infile]\n"); return 1; }
  n = atoi(argv[1]); k = atoi(argv[2]); c = atoi(argv[3]); int seed = atoi(argv[4]); long iters = atol(argv[5]);
  MASK = n==32 ? 0xFFFFFFFFu : (1u<<n)-1;
  rng ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL; for(int i=0;i<20;i++) rnd();
  int LMIN = getenv("LMIN")?atoi(getenv("LMIN")):k+2;
  int LMAX = getenv("LMAX")?atoi(getenv("LMAX")):24;
  nodelim = getenv("NODES")?atol(getenv("NODES")):20000;
  bnodelim = getenv("BNODES")?atol(getenv("BNODES")):200000;
  LB = getenv("LB")?atoi(getenv("LB")):2*k+LMIN+4;
  double PLAT = getenv("PLAT")?atof(getenv("PLAT")):0.5;
  int GAIN = getenv("GAIN")?atoi(getenv("GAIN")):8;
  double SECS = getenv("SECS")?atof(getenv("SECS")):1e18;
  double SHRINK = getenv("SHRINK")?atof(getenv("SHRINK")):0.0;
  int SLACK = getenv("SLACK")?atoi(getenv("SLACK")):4;
  const char *OUT = getenv("OUT")?getenv("OUT"):"symbest.txt";
  uint32_t V = 1u<<n; long MAXN = V < (1u<<22) ? (long)V+8 : (1L<<22);
  cyc = malloc(4*MAXN); ncyc = malloc(4*MAXN); seg = malloc(4*MAXN); tmpc = malloc(4*MAXN); bbest = malloc(4*MAXN);
  uint32_t *bestcyc = malloc(4*MAXN);
  cnt = calloc(V,2); { int nb2=0; for (uint32_t m=0;m<V;m++) if (__builtin_popcount(m) < k) nb2++; nball = nb2;
    ball = malloc(4*(size_t)nball); nb2=0; for (uint32_t m=0;m<V;m++) if (__builtin_popcount(m) < k) ball[nb2++] = m; }
  if (argc > 6){   // infile: must carry a '# ... L <L> t <hex>' header, or we detect L from the shift
    FILE *f = fopen(argv[6],"r"); if (!f){ perror("in"); return 1; } char line[256]; N = 0;
    while (fscanf(f," %255s", line)==1){ if (line[0]=='#'){ fgets(line,255,f); continue; } cyc[N++] = strtoul(line,0,16); }
    fclose(f);
    int Lin = getenv("LIN")?atoi(getenv("LIN")):0; if (!Lin){ fprintf(stderr,"need LIN=segment length for infile\n"); return 1; }
    L = Lin; R = N/L; t = cyc[L] ^ rot(cyc[0]);
    for (int i=0;i<N;i++) if (cyc[(i+L)%N] != g(cyc[i])){ fprintf(stderr,"infile not g-invariant at %d\n", i); return 1; }
  } else {   // trivial cycle with transitions 0,1,..,n-1,0,1.. : invariant under rot_c with L=c, needs c | 2n
    if ((2*n) % c){ fprintf(stderr,"c must divide 2n for the trivial start\n"); return 1; }
    N = 2*n; for (int i=0;i<=n;i++) cyc[i] = (1u<<i)-1; for (int i=1;i<n;i++) cyc[n+i] = MASK & ~((1u<<i)-1);
    L = c; R = N/L; t = cyc[L] ^ rot(cyc[0]);
  }
  for (int i=0;i<N;i++) if (cyc[(i+L)%N] != g(cyc[i])){ fprintf(stderr,"start not g-invariant\n"); return 1; }
  if (!valid_full(cyc, N)){ fprintf(stderr,"start INVALID\n"); return 1; }
  fprintf(stderr,"start N=%d L=%d R=%d t=%x\n", N, L, R, t);
  double t0 = now(); int bestN = N; memcpy(bestcyc, cyc, 4*(size_t)N); int bestL = L, bestR = R; uint32_t bestt = t;
  LOCALV = getenv("LOCALV")?atoi(getenv("LOCALV")):1;
  long acc = 0; SAVEINT = getenv("SAVEINT")?atof(getenv("SAVEINT")):30;
  int WSLK = getenv("WSLK")?atoi(getenv("WSLK")):-1; int Wneed = LMIN + 2*k - WSLK; RWANT = getenv("RWANT")?atoi(getenv("RWANT")):0; BGREEDY = getenv("BGREEDY")?atof(getenv("BGREEDY")):0;
  int BTRIES = getenv("BTRIES")?atoi(getenv("BTRIES")):1000000;
  double RESTART = getenv("RESTART")?atof(getenv("RESTART")):1e18;
  int N0 = N, L0 = L, R0s = R; uint32_t t0g = t; uint32_t *cyc0 = malloc(4*(size_t)N0); memcpy(cyc0, cyc, 4*(size_t)N0);
  int nrest = 0;
  long itg = 0;
  while (now()-t0 < SECS && itg < iters){
  double tr = now(); nrest++;
  memcpy(cyc, cyc0, 4*(size_t)N0); N = N0; L = L0; R = R0s; t = t0g; cntok = 0;
  // bootstrap
  for (int tries=0; L < Wneed && tries < BTRIES && now()-tr < RESTART && now()-t0 < SECS; tries++){
    uint32_t tsave = t; int Rsave = R;
    if (getenv("T")) t = strtoul(getenv("T"),0,16);
    else { do { t = rnd() & MASK; } while (RWANT == n && c == 1 && (__builtin_popcount(t) & 1)); }
    // orbit length of g on v0
    { uint32_t y = cyc[0]; int r = 0; do { y = g(y); r++; } while (y != cyc[0] && r <= 4*n); R = r; }
    if ((RWANT && R != RWANT) || R > 4*n){ t = tsave; R = Rsave; continue; }
    bnodes = 0; bbestN = N; bbestL = 0; bseg[0] = cyc[0]; btarget = g(cyc[0]);
    { uint32_t y = cyc[0]; for (int j=1;j<R;j++){ y = g(y); bimg[0][j] = y; } }
    bdfs(1);
    if (bbestL > 0){ memcpy(cyc, bbest, 4*(size_t)bbestN); N = bbestN; L = bbestL; R = N/L;
      fprintf(stderr,"boot try %d: N=%d L=%d R=%d t=%x nodes %ld\n", tries, N, L, R, t, bnodes); }
    else { t = tsave; R = Rsave; }
  }
  if (L < Wneed && getenv("VERB")){ fprintf(stderr,"bootstrap: L=%d < Wneed\n", L); }
  if (!valid_full(cyc,N)){ fprintf(stderr,"BUG boot invalid\n"); return 2; }
  if (N > bestN){ bestN = N; memcpy(bestcyc, cyc, 4*(size_t)N); bestL = L; bestR = R; bestt = t; save(OUT); }
  for (; itg<iters && L >= Wneed; itg++){ long it = itg;
    if (((it & 63) == 0 || N > 20000) && (now()-t0 > SECS || now()-tr > RESTART)) break;
    int Wmax = L - 2*k + WSLK; if (Wmax > LMAX) Wmax = LMAX;
    int W = LMIN + rnd()%(Wmax-LMIN+1);
    int a = rnd()%L;
    // frozen counts (incremental): cnt = whole cycle minus excluded = window-0 [a-(k-2), a+W+k-2] + image interiors
    if (!cntok){ memset(cnt, 0, 2*(size_t)V); for (int i=0;i<N;i++) addball(cyc[i], 1); cntok = 1; }
    excl(a, W, -1);
    na = nb = k-1; nseq = 0;
    for (int j=k-2;j>=0;j--) seq[nseq++] = cyc[(a - j + N)%N];
    for (int j=0;j<k-1;j++) bnear[j] = cyc[(a+W+j)%N];
    target_b = cyc[(a+W)%N];
    int shrink = SHRINK > 0 && N - 2*R >= bestN - SLACK*R && (rnd()%100000) < SHRINK*100000;
    nodes = 0; bestlen = 0; Lmaxnew = shrink ? W-2 : W + GAIN;
    if (Lmaxnew > L - 2*k + WSLK + GAIN) Lmaxnew = L - 2*k + WSLK + GAIN;   // keep windows from crowding (soft)
    dfs(0);
    if (bestlen == 0){ excl(a, W, 1); continue; }
    int accept = (shrink && N - R*(W-bestlen) >= bestN - SLACK*R) || bestlen > W || (bestlen == W && (rnd()%1000) < PLAT*1000);
    if (!accept){ excl(a, W, 1); continue; }
    // new segment starting at v_a: v_a, best[0..bestlen-1] (ends at v_{a+W}), v_{a+W+1}..v_{a+L-1}
    int LL = 0; seg[LL++] = cyc[a]; for (int i=0;i<bestlen;i++) seg[LL++] = best[i];
    for (int i=W+1;i<L;i++) seg[LL++] = cyc[(a+i)%N];
    int M = build(ncyc, seg, LL, MAXN);
    if (M != R*LL || !(LOCALV ? valid_symloc(ncyc, M, bestlen) : valid_sym(ncyc, M, LL))){ fprintf(stderr,"BUG/REJECT: invalid after sym splice (W=%d new=%d M=%d)\n", W, bestlen, M); excl(a, W, 1); continue; }
    uint32_t *tt = cyc; cyc = ncyc; ncyc = tt; N = M; L = LL; acc++;
    excl(0, bestlen, 1);
    if (N > bestN){ bestN = N; memcpy(bestcyc, cyc, 4*(size_t)N); bestL = L; bestR = R; bestt = t;
      if (now() - lastsave > SAVEINT){
        if (!valid_full(cyc,N)){ fprintf(stderr,"BUG full validation failed\n"); return 2; }
        save(OUT); lastsave = now(); fprintf(stderr,"it %ld t %.1fs N=%d L=%d\n", it, now()-t0, N, L); } }
  }
  }
  memcpy(cyc, bestcyc, 4*(size_t)bestN); N = bestN; L = bestL; R = bestR; t = bestt;
  if (!valid_full(cyc,N)){ fprintf(stderr,"BUG final\n"); return 2; } save(OUT);
  printf("n %d k %d c %d seed %d best %d L %d R %d acc %ld restarts %d t %.1f\n", n, k, c, seed, bestN, L, R, acc, nrest, now()-t0);
  return 0;
}
