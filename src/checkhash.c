// S140 checkhash.c -- O(N*|ball|) validator for spread-k circuit codes using a hash table (memory O(N), not 2^n).
// Written fresh (no code from checkfast/cc/sym). usage: checkhash file n k
// Coil conditions (cyclic distance d_C, Hamming d_H):  for all i != j:  d_C < k => d_H == d_C ;  d_H < k => d_C == d_H.
// Equivalent check: (1) entries in range, distinct; consecutive differ in one bit (cyclic);
// (2) for d=1..k-1: H(v_i,v_{i+d}) == d;  (3) for each i and each nonzero mask of weight < k: if v_i^mask = v_j then d_C(i,j)==weight.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static uint64_t *hk; static int64_t *hv; static uint64_t hmask;
static inline uint64_t hh(uint64_t x){ x^=x>>31; x*=0x7fb5d329728ea185ULL; x^=x>>27; x*=0x81dadef4bc2dd44dULL; x^=x>>33; return x; }
static int64_t look(uint64_t key){ uint64_t p=hh(key)&hmask; while(hv[p]>=0){ if(hk[p]==key) return hv[p]; p=(p+1)&hmask; } return -1; }
static int ins(uint64_t key, int64_t val){ uint64_t p=hh(key)&hmask; while(hv[p]>=0){ if(hk[p]==key) return 0; p=(p+1)&hmask; } hk[p]=key; hv[p]=val; return 1; }
int n,k; int64_t N; uint64_t *v; long bad=0;
static void rec(int64_t i, uint64_t m, int w, int start){   // enumerate masks of weight 1..k-1
  for(int b=start;b<n;b++){ uint64_t mm=m|(1ULL<<b); int64_t j=look(v[i]^mm);
    if(j>=0){ int64_t d=j>i?j-i:i-j; if(N-d<d) d=N-d; if(d!=w+1){ if(bad<5) printf("bad pair %lld %lld dH %d dC %lld\n",(long long)i,(long long)j,w+1,(long long)d); bad++; } }
    if(w+1<k-1) rec(i,mm,w+1,b+1); }
}
int main(int c,char**a){ if(c<4){fprintf(stderr,"usage\n");return 1;} n=atoi(a[2]); k=atoi(a[3]);
  FILE*f=fopen(a[1],"r"); if(!f){printf("cannot open\n");return 1;} size_t cap=1<<20; v=malloc(cap*8); char tok[128]; N=0;
  while(fscanf(f," %127s",tok)==1){ if(tok[0]=='#'){int ch; while((ch=fgetc(f))!='\n'&&ch!=EOF); continue;} if((size_t)N==cap){cap*=2; v=realloc(v,cap*8);} v[N++]=strtoull(tok,0,16); }
  uint64_t sz=1; while(sz<2*(uint64_t)N) sz<<=1; hmask=sz-1; hk=malloc(sz*8); hv=malloc(sz*8); for(uint64_t p=0;p<sz;p++) hv[p]=-1;
  for(int64_t i=0;i<N;i++){ if(n<64 && (v[i]>>n)){ printf("INVALID out of range\n"); return 1; } if(!ins(v[i],i)){ printf("INVALID duplicate at %lld\n",(long long)i); return 1; } }
  for(int64_t i=0;i<N;i++) for(int d=1;d<k;d++){ int h=__builtin_popcountll(v[i]^v[(i+d)%N]); if(h!=d){ if(bad<5) printf("bad near %lld d %d H %d\n",(long long)i,d,h); bad++; } }
  for(int64_t i=0;i<N;i++) rec(i,0,0,0);
  if(bad) printf("INVALID %ld violations N %lld\n",bad,(long long)N); else printf("VALID N %lld n %d k %d\n",(long long)N,n,k);
  return bad?1:0; }
