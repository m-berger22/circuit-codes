// checkfast.c -- O(N * |ball|) validator for spread-k circuit codes (S133). Third independent checker.
// Coil condition (all pairs): d_H(v_i,v_j) < k  =>  d_C(i,j) = d_H   AND   d_C < k  =>  d_H = d_C.
// (1) vertices distinct, consecutive (cyclic) differ in exactly one bit;
// (2) d_C < k pairs: for d=1..k-1, H(v_i, v_{i+d}) == d (direct);
// (3) d_H < k pairs: for each i and each mask with 1 <= popcount < k, if v_i^mask is on the cycle at j, need d_C(i,j) == popcount.
// usage: checkfast file n k
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
int main(int argc, char **argv){
  if (argc < 4){ fprintf(stderr,"usage: checkfast file n k\n"); return 1; }
  int n = atoi(argv[2]), k = atoi(argv[3]); uint32_t V = 1u<<n;
  FILE *f = fopen(argv[1],"r"); if (!f){ perror("open"); return 1; }
  size_t cap = 1<<20, N = 0; uint32_t *v = malloc(4*cap); char tok[256];
  while (fscanf(f," %255s", tok)==1){
    if (tok[0]=='#'){ int ch; while ((ch=fgetc(f))!='\n' && ch!=EOF); continue; }
    if (N==cap){ cap*=2; v = realloc(v,4*cap); }
    char *e; unsigned long x = strtoul(tok,&e,16); if (*e || x >= V){ printf("%s: BAD TOKEN %s INVALID\n", argv[1], tok); return 1; }
    v[N++] = (uint32_t)x; }
  fclose(f);
  int32_t *pos = malloc(4*(size_t)V); memset(pos, 0xff, 4*(size_t)V);
  for (size_t i=0;i<N;i++){ if (pos[v[i]] >= 0){ printf("%s: repeated vertex INVALID\n", argv[1]); return 1; } pos[v[i]] = i; }
  if (N < (size_t)2*k){ printf("%s: too short INVALID\n", argv[1]); return 1; }
  for (size_t i=0;i<N;i++) for (int d=1; d<k; d++)
    if (__builtin_popcount(v[i]^v[(i+d)%N]) != d){ printf("%s: near pair i=%zu d=%d INVALID\n", argv[1], i, d); return 1; }
  // masks of popcount 1..k-1
  size_t nm = 0, mcap = 1024; uint32_t *ms = malloc(4*mcap);
  for (int w=1; w<k; w++){ // enumerate combinations of w bits out of n (Gosper)
    uint32_t m = (1u<<w)-1; while (m < V){ if (nm==mcap){ mcap*=2; ms = realloc(ms,4*mcap); } ms[nm++] = m;
      uint32_t c = m & -m, r = m + c; m = (((r^m)>>2)/c) | r; } }
  for (size_t i=0;i<N;i++) for (size_t q=0;q<nm;q++){ int32_t j = pos[v[i]^ms[q]]; if (j < 0) continue;
      long d = labs((long)i - j); if ((size_t)d > N-d) d = N-d;
      if (d != __builtin_popcount(ms[q])){ printf("%s: pair %zu %d dH=%d dC=%ld INVALID\n", argv[1], i, j, __builtin_popcount(ms[q]), d); return 1; } }
  printf("%s: COIL n=%d k=%d N=%zu VALID\n", argv[1], n, k, N);
  return 0;
}
