// cc.c -- spread-k circuit codes in Q_n by windowed rerouting (S132).
// A circuit code of spread k: cycle v_0..v_{N-1} in Q_n (consecutive differ in 1 bit) such that
// for all i,j: cyclic distance d_C(i,j) >= k  =>  Hamming(v_i,v_j) >= k   (Klee's lemma; N >= 2k).
// We also verify d_C < k => Hamming == d_C (implied, checked anyway).
// Move: pick window [a, a+L] on the cycle, delete interior, DFS for a replacement path a->b of
// length L' (same parity), keep the longest found within a node budget; accept if L' > L, or
// L' == L (plateau, a different path) with probability PLAT.
// usage: cc n k seed iters [infile] ; env: LMIN LMAX NODES PLAT OUT TARGET SECS
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdint.h>

static int n, k, N;                 // N = cycle length
static uint32_t *cyc, *ncyc;
static int32_t *pos;                // pos[x] = index in cycle or -1
static uint16_t *cnt;               // frozen-vertex Hamming-ball counts
static uint32_t *ball; static int nball;  // masks with popcount 0..k-1
static uint64_t rng = 88172645463325252ULL;
static inline uint64_t rnd(void){ rng ^= rng<<13; rng ^= rng>>7; rng ^= rng<<17; return rng; }
static inline int H(uint32_t a, uint32_t b){ return __builtin_popcount(a^b); }

static void addball(uint32_t x, int d){ for (int i=0;i<nball;i++) cnt[x^ball[i]] += d; }

static int OPEN, na, nb, tailmode;
static int cdist(int i, int j){ int d = abs(i-j); if (OPEN) return d; return d < N-d ? d : N-d; }

// full validation of cyc[0..N-1]  (O(N^2), independent of the ball tables)
static int valid(void){
  if (!OPEN && N < 2*k) return 0;
  for (int i=0;i<N;i++){
    if ((!OPEN || i+1<N) && H(cyc[i], cyc[(i+1)%N]) != 1) return 0;
    for (int j=i+1;j<N;j++){ int dc = cdist(i,j), dh = H(cyc[i],cyc[j]);
      if (dc < k ? dh != dc : dh < k) return 0; }
  }
  return 1;
}

// local validation after a coil splice: only pairs involving changed indices can change status
static int valid_local(int lo, int hi){   // changed indices: lo..N-1 (wrapping) and 0..hi
  if (N < 2*k) return 0;
  for (int c=0;c<2;c++){ int i0 = c? 0 : lo, i1 = c? hi : N-1;
    for (int i=i0;i<=i1;i++){
      if (H(cyc[i], cyc[(i+1)%N]) != 1) return 0;
      if (H(cyc[i], cyc[(i-1+N)%N]) != 1) return 0;
      for (int j=0;j<N;j++){ if (j==i) continue; int dc = cdist(i,j), dh = H(cyc[i],cyc[j]);
        if (dc < k ? dh != dc : dh < k) return 0; }
    }
  }
  return 1;
}

// ---- DFS state ----
static uint32_t seq[1<<16];   // [near-a (k-1 vertices: a-(k-2)..a)] + path
static int nseq;
static uint32_t bnear[64];    // b, b+1, ..., b+(k-2)
static uint32_t target_b;
static long nodes, nodelim;
static int Lmaxnew;           // max new path length
static uint32_t best[1<<16]; static int bestlen;  // best path (steps incl. final b)
static int direct, cntok, FULLV, dirty; static uint32_t *bestcyc; static double lastsave, SAVEINT; static uint32_t *frz; static int nfrz;
static inline int blockedx(uint32_t x){
  if (!direct){ if (cnt[x]) return 1; }
  else for (int i=0;i<nfrz;i++) if (H(x,frz[i])<k) return 1;
  for (int i=0;i<=nseq-k;i++) if (H(x,seq[i])<k) return 1;
  return 0; }

static int final_ok(int L){   // seq[k-1 .. k-1+L-1] = path vertices p1..p_{L-1}, then b
  // check path vertices vs near-b set: path vertex at step s (1..L-1) vs b+j: distance (L-s)+j
  for (int s=1;s<L;s++){ uint32_t x = seq[na-1+s];
    for (int j=0;j<nb;j++){ int d = (L-s)+j; int h = H(x,bnear[j]);
      if (d < k){ if (h != d) return 0; } else if (h < k) return 0; }
  }
  // near-a vs near-b (distance changes with L)
  for (int i=0;i<na;i++) for (int j=0;j<nb;j++){ int d = (na-1-i) + L + j; int h = H(seq[i], bnear[j]);
      if (d < k){ if (h != d) return 0; } else if (h < k) return 0; }
  return 1;
}

static void dfs(int s){   // s = number of path steps taken so far; head = seq[nseq-1]
  if (nodes++ > nodelim) return;
  uint32_t head = seq[nseq-1];
  if (tailmode){
    if (s > bestlen){ bestlen = s; memcpy(best, seq+na, sizeof(uint32_t)*s); }
    if (s >= Lmaxnew) return;
  }
  int hb = tailmode ? 0 : H(head, target_b);
  if (!tailmode && hb == 1 && s+1 > bestlen && s+1 <= Lmaxnew){
    if (final_ok(s+1)){ bestlen = s+1; memcpy(best, seq+na, sizeof(uint32_t)*s); best[s] = target_b; }
  }
  if (s + hb > Lmaxnew) return;    // can't finish within budget (need >= hb more steps after next... approx)
  // candidates
  int nc = 0; uint32_t cand[32]; int deg[32];
  for (int b=0;b<n;b++){ uint32_t x = head ^ (1u<<b);
    if (x == target_b) continue;
    if (!direct){ if (cnt[x]) continue; int bl=0; for (int i=0;i<nseq-k;i++) if (H(x,seq[i])<k){bl=1;break;} if (bl) continue; }
    // recent seq vertices (sequence distance d = nseq - idx, < k): Hamming must equal d
    int ok = 1;
    for (int d=2; d<k && d<=nseq; d++){ if (H(x, seq[nseq-d]) != d){ ok=0; break; } }
    if (!ok) continue;
    // near-b: if H(x,b+j) < k, then must end with the right remaining (checked at end); prune obvious
    for (int j=0;j<nb;j++){ int h = H(x,bnear[j]); if (h < k && h - j < H(x,target_b)) { ok=0; break; } if (h==0){ok=0;break;} }
    if (!ok) continue;
    cand[nc] = x; deg[nc] = (int)(rnd()&1023); nc++;
  }
  // random order
  for (int i=1;i<nc;i++){ int j = rnd()%(i+1); uint32_t t=cand[i]; cand[i]=cand[j]; cand[j]=t; }
  for (int c=0;c<nc;c++){
    uint32_t x = cand[c];
    // freeze the seq vertex that is now at distance k from the new head
    int fr = nseq - k;        // index of vertex at seq distance k from x
    (void)fr;
    if (!blockedx(x)){ seq[nseq++] = x; dfs(s+1); nseq--; }
    if (nodes > nodelim) return;
  }
}

static double now(void){ struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t); return t.tv_sec+1e-9*t.tv_nsec; }

static void save(const char *fn){
  FILE *f = fopen(fn,"w"); if(!f) return;
  fprintf(f,"# n %d k %d N %d\n", n, k, N);
  for (int i=0;i<N;i++) fprintf(f,"%x%c", cyc[i], i==N-1?'\n':' ');
  fclose(f);
}

int main(int argc, char **argv){
  if (argc < 5){ fprintf(stderr,"usage: cc n k seed iters [infile]\n"); return 1; }
  n = atoi(argv[1]); k = atoi(argv[2]); int seed = atoi(argv[3]); long iters = atol(argv[4]);
  rng ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL; for(int i=0;i<20;i++) rnd();
  int LMIN = getenv("LMIN")?atoi(getenv("LMIN")):k+2;
  int LMAX = getenv("LMAX")?atoi(getenv("LMAX")):24;
  nodelim = getenv("NODES")?atol(getenv("NODES")):20000;
  double PLAT = getenv("PLAT")?atof(getenv("PLAT")):0.5;
  int GAIN = getenv("GAIN")?atoi(getenv("GAIN")):8;
  double SECS = getenv("SECS")?atof(getenv("SECS")):1e18;
  double DROP = getenv("DROP")?atof(getenv("DROP")):0.0;   // prob of accepting a shorter reroute
  int DROPMAX = getenv("DROPMAX")?atoi(getenv("DROPMAX")):1; // max loss in units of 2
  double SHRINK = getenv("SHRINK")?atof(getenv("SHRINK")):0.0;  // prob of a forced-shorter reroute (coils)
  int SLACK = getenv("SLACK")?atoi(getenv("SLACK")):4;       // never fall more than SLACK below best
  FULLV = getenv("FULLV")?atoi(getenv("FULLV")):0;
  int DIRECT = getenv("DIRECT")?atoi(getenv("DIRECT")):-1;  // -1 auto
  const char *OUT = getenv("OUT")?getenv("OUT"):"best.txt";
  int TARGET = getenv("TARGET")?atoi(getenv("TARGET")):1<<30;
  uint32_t V = 1u<<n;
  OPEN = getenv("OPEN")?atoi(getenv("OPEN")):0;
  double TAILP = getenv("TAILP")?atof(getenv("TAILP")):0.3;
  long MAXN = V < (1u<<22) ? (long)V+8 : (1L<<22);
  cyc = malloc(4*MAXN); bestcyc = malloc(4*MAXN); SAVEINT = getenv("SAVEINT")?atof(getenv("SAVEINT")):10; ncyc = malloc(4*MAXN); frz = malloc(4*MAXN); (void)pos;
  { double bs = 0, c = 1; for (int i=0;i<k;i++){ bs += c; c = c*(n-i)/(i+1); } nball = bs > 2e9 ? 2000000000 : (int)bs; }
  int CNTMAX = getenv("CNTMAX")?atoi(getenv("CNTMAX")):24;
  if (n > CNTMAX){ if (DIRECT == 0){ fprintf(stderr,"n>CNTMAX needs DIRECT\n"); return 1; } DIRECT = 1; }
  else { cnt = calloc(V,2); ball = malloc(4*(size_t)nball); int nb2 = 0;
    for (uint32_t m=0;m<V;m++) if (__builtin_popcount(m) < k) ball[nb2++] = m; }
  if (argc > 5){
    FILE *f = fopen(argv[5],"r"); char line[256]; N=0;
    if (!f){ perror("in"); return 1; }
    while (fscanf(f," %255s", line)==1){ if (line[0]=='#'){ fgets(line,255,f); continue; } cyc[N++] = strtoul(line,0,16); }
    fclose(f);
  } else if (getenv("OPEN") && atoi(getenv("OPEN"))) { N = n+1; for (int i=0;i<=n;i++) cyc[i] = (1u<<i)-1;
  } else { N = 2*n; for (int i=0;i<=n;i++) cyc[i] = (1u<<i)-1; for (int i=1;i<n;i++) cyc[n+i] = ((1u<<n)-1) & ~((1u<<i)-1); }
  if (!valid()){ fprintf(stderr,"initial cycle INVALID (N=%d)\n", N); return 1; }
  fprintf(stderr,"start N=%d valid\n", N);
  int bestN = N; (void)0; double t0 = now(); long acc=0, imp=0;
  for (long it=0; it<iters && N < TARGET; it++){
    if ((it & 255) == 0 && now()-t0 > SECS) break;
    if (OPEN){
      int L = 1 + rnd()%LMAX; int tail = (rnd()%1000) < TAILP*1000;
      if (!tail){ L = LMIN + rnd()%(LMAX-LMIN+1); }
      if (L > N-2) L = N-2;
      if (L < 1) L = 1;
      if (tail && (rnd()&1)){ for (int i=0;i<N/2;i++){ uint32_t t=cyc[i]; cyc[i]=cyc[N-1-i]; cyc[N-1-i]=t; } }
      int a = tail ? N-1-L : (int)(rnd()%(N-L));
      if (a < 0) continue;
      int b = a + L;  // for tail: b = N-1 (removed)
      direct = DIRECT >= 0 ? DIRECT : (2L*n*N < nball);
      if (!direct) memset(cnt, 0, 2*V);
      nfrz = 0;
      for (int i=0;i<N;i++){
        if (i > a-(k-1) && (tail || i < b+(k-1))) continue;
        if (direct) frz[nfrz++] = cyc[i]; else addball(cyc[i], 1);
      }
      na = a+1 < k-1 ? a+1 : k-1;
      nseq = 0; for (int i=a-na+1;i<=a;i++) seq[nseq++] = cyc[i];
      tailmode = tail;
      if (tail){ nb = 0; target_b = 0xFFFFFFFFu; }
      else { nb = N-b < k-1 ? N-b : k-1; for (int j=0;j<nb;j++) bnear[j] = cyc[b+j]; target_b = cyc[b]; }
      nodes = 0; bestlen = 0; Lmaxnew = L + GAIN;
      dfs(0);
      if (bestlen == 0) continue;
      int accept = bestlen > L || (bestlen == L && (rnd()%1000) < PLAT*1000)
               || (bestlen < L && bestlen >= L-2*DROPMAX && N - (L-bestlen) >= bestN - SLACK && (rnd()%100000) < DROP*100000);
      if (!accept) continue;
      int M = 0; for (int i=0;i<=a;i++) ncyc[M++] = cyc[i];
      for (int i=0;i<bestlen;i++) ncyc[M++] = best[i];
      if (!tail) for (int i=b+1;i<N;i++) ncyc[M++] = cyc[i];
      uint32_t *t = cyc; cyc = ncyc; ncyc = t; int oldN = N; N = M;
      if (!valid()){ fprintf(stderr,"BUG: invalid after open splice (tail=%d L=%d new=%d)\n", tail, L, bestlen); t = cyc; cyc = ncyc; ncyc = t; N = oldN; continue; }
      acc++; if (N > oldN) imp++;
      if (N > bestN){ bestN = N; save(OUT); fprintf(stderr,"it %ld t %.1fs N=%d (len %d)\n", it, now()-t0, N, N-1); }
      continue;
    }
    na = nb = k-1; tailmode = 0;
    int L = LMIN + rnd()%(LMAX-LMIN+1);
    if (L > N - 2*k - 2) L = N - 2*k - 2;
    if (L < 2) continue;
    int a = rnd()%N;
    // build frozen counts: all vertices except window interior, near-a (a-(k-2)..a), near-b (b..b+k-2)
    direct = DIRECT >= 0 ? DIRECT : (2L*n*N < nball);
    if (direct){
      cntok = 0; nfrz = 0;
      for (int i=0;i<N;i++){
        int off = (i - a + N) % N;  // a at off 0, b at off L
        if (off <= L + k-2 || off >= N-(k-2)) continue;
        frz[nfrz++] = cyc[i];
      }
    } else {
      if (!cntok){ memset(cnt, 0, 2*V); for (int i=0;i<N;i++) addball(cyc[i], 1); cntok = 1; }
      for (int o=-(k-2); o<=L+k-2; o++) addball(cyc[(a+o+2*N)%N], -1);   // exclude window + near sets
    }
    nseq = 0;
    for (int j=k-2;j>=0;j--) seq[nseq++] = cyc[(a - j + N)%N];
    for (int j=0;j<k-1;j++) bnear[j] = cyc[(a+L+j)%N];
    target_b = cyc[(a+L)%N];
    nodes = 0; bestlen = 0; Lmaxnew = L + GAIN; int shrink = SHRINK > 0 && N - 2 >= bestN - SLACK && (rnd()%100000) < SHRINK*100000; if (shrink) Lmaxnew = L - 2;
    if (Lmaxnew > (int)V - N + L) Lmaxnew = V - N + L;
    dfs(0);
    int accept = bestlen > 0 && ((shrink && N-(L-bestlen) >= bestN-SLACK) || bestlen > L || (bestlen == L && (rnd()%1000) < PLAT*1000)
               || (bestlen < L && bestlen >= L-2*DROPMAX && N - (L-bestlen) >= bestN - SLACK && (rnd()%100000) < DROP*100000));
    if (!accept){ if (!direct) for (int o=-(k-2); o<=L+k-2; o++) addball(cyc[(a+o+2*N)%N], 1); continue; }
    // splice: new cycle = a, best[0..bestlen-1] (ends at b), then b+1 .. a-1
    int M = 0; ncyc[M++] = cyc[a];
    for (int i=0;i<bestlen;i++) ncyc[M++] = best[i];
    for (int i=L+1; i<N; i++) ncyc[M++] = cyc[(a+i)%N];
    uint32_t *t = cyc; cyc = ncyc; ncyc = t; int oldN = N; N = M;
    int vok = FULLV ? valid() : valid_local(N-(k-2), bestlen+k-2);
    if (vok && !FULLV && (acc % 20000) == 0) vok = valid();
    if (!vok){ fprintf(stderr,"BUG: invalid after splice (L=%d new=%d)\n", L, bestlen); t = cyc; cyc = ncyc; ncyc = t; N = oldN; cntok = 0; continue; }
    if (!direct) for (int i=N-(k-2); i<N; i++) addball(cyc[i], 1);
    if (!direct) for (int i=0; i<=bestlen+k-2; i++) addball(cyc[i], 1);
    acc++; if (N > oldN) imp++;
    if (N > bestN){ bestN = N; memcpy(bestcyc, cyc, 4*(size_t)N); dirty = 1;
      if (now() - lastsave > SAVEINT){
        if (!valid()){ fprintf(stderr,"BUG: full validation failed at new best\n"); return 2; }
        save(OUT); lastsave = now(); dirty = 0; fprintf(stderr,"it %ld t %.1fs N=%d\n", it, now()-t0, N); } }
  }
  if (dirty){ uint32_t *t = cyc; cyc = bestcyc; bestcyc = t; N = bestN;
    if (!valid()){ fprintf(stderr,"BUG: final validation failed\n"); return 2; } save(OUT); fprintf(stderr,"final save N=%d\n", N); }
  if (OPEN) printf("SNAKE (best = #vertices; length = best-1) ");
  printf("n %d k %d seed %d best %d final %d acc %ld imp %ld t %.1f\n", n, k, seed, bestN, N, acc, imp, now()-t0);
  return 0;
}
