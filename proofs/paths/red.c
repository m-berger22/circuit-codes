// S179 red.c : C version of reduced.py for ANY number of pieces (reduced boundary model; costs in Plotkin units, see PROOF_threshold.md section 7). usage: red PAR CC G M E [maxsol]
// G = string of 0/m (piece length K or K-1). Output: nodes, solutions. Coordinates <= 64.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef uint64_t u64;
int PAR,CC,NP,NV,M,E,G[8],off[9],base[9][9],MAXSEP,B; long MAXS=1000000000L;
int NT,TY[256],COST[256],INP[256][9],SEP[256][9][9];
int nlet[9],let[9][40],ctype[64],nc,budget,X[9][9];
int ordj[400],orde[400],nord; long nodes,sols;
static inline int reqrel(int a,int r){ return -1 + ((((a-1)*PAR + r + 1)%2+2)%2); }
u64 pre(int j,int e){ u64 m=0; for(int i=0;i<e;i++) m|=1ULL<<let[j][i]; return m; }
int checkvertex(int j,int e){
  u64 A=pre(j,e);
  for(int j2=0;j2<NV;j2++){ if(j2==j) continue; u64 Bm=0;
    for(int e2=0;e2<=nlet[j2];e2++){
      if(e2>0){ if(let[j2][e2-1]<0) break; Bm|=1ULL<<let[j2][e2-1]; }
      int ja,ea,jb,eb; if(j<j2){ja=j;ea=e;jb=j2;eb=e2;} else {ja=j2;ea=e2;jb=j;eb=e;}
      int r=off[jb]-off[ja]+eb-ea; if(jb==ja+1 && r<-1) continue;
      int s=base[j][j2]+2*X[j][j2]; u64 D=A^Bm;
      while(D){ int c=__builtin_ctzll(D); D&=D-1; s+= SEP[ctype[c]][j][j2]? -1:1; }
      if(s<reqrel(jb-ja,r)) return 0;
    } }
  return 1;
}
void rec(int i){
  if(sols>=MAXS) return;
  if(i==nord){ sols++; return; }
  int j=ordj[i],e=orde[i]; nodes++;
  u64 inj=pre(j,e);
  for(int c=0;c<nc;c++){ int t=ctype[c];
    if(!INP[t][j] || (inj>>c&1)) continue;
    if(j>=1 && INP[t][j-1]){ int lim=e+G[j-1]+1; if(lim<0) lim=0; if(lim>nlet[j-1]) lim=nlet[j-1]; int ok=0; for(int q=0;q<lim;q++) if(let[j-1][q]==c) ok=1; if(!ok) continue; }
    let[j][e]=c; if(checkvertex(j,e+1)) rec(i+1); let[j][e]=-1; }
  if(nc<64) for(int t=0;t<NT;t++){
    if(!INP[t][j] || COST[t]>budget) continue;
    if(j>=1 && INP[t][j-1]) continue;
    ctype[nc]=t; let[j][e]=nc; nc++; budget-=COST[t];
    if(checkvertex(j,e+1)) rec(i+1);
    nc--; let[j][e]=-1; budget+=COST[t]; }
  else { fprintf(stderr,"coordinate overflow\n"); exit(1); }
}
int NAi[40],NAj[40],nna; long nx;
void xrec(int q,int rem){
  if(q==nna){ nx++; nc=0; int sx=0; for(int a=0;a<nna;a++) sx+=X[NAi[a]][NAj[a]]; budget=B-2*sx;
    for(int j=0;j<NV;j++) for(int e=0;e<40;e++) let[j][e]=-1;
    if(checkvertex(0,0)) rec(0); return; }
  for(int v=0;v<=rem;v++){ X[NAi[q]][NAj[q]]=X[NAj[q]][NAi[q]]=v; xrec(q+1,rem-v); }
  X[NAi[q]][NAj[q]]=X[NAj[q]][NAi[q]]=0;
}
int main(int argc,char**argv){
  PAR=atoi(argv[1]); CC=atoi(argv[2]); NP=strlen(argv[3]); NV=NP+1; for(int i=0;i<NP;i++) G[i]=argv[3][i]=='0'?0:-1;
  M=atoi(argv[4]); E=atoi(argv[5]); if(argc>6) MAXS=atol(argv[6]);
  MAXSEP=NV*NV/4; off[0]=0; for(int i=0;i<NP;i++) off[i+1]=off[i]+G[i];
  int tot=0; for(int i=0;i<NV;i++) for(int j=i+1;j<NV;j++){ int b=(j==i+1)?G[i]:reqrel(j-i,off[j]-off[i]); base[i][j]=base[j][i]=b; tot+=b; }
  if(CC-tot<0){ printf("PAR %d CC %d G %s: Plotkin impossible outright (deficit %d)\n",PAR,CC,argv[3],tot-CC); return 0; }
  B=CC-tot;
  for(int s=0;s<(1<<NV);s++){ int w=__builtin_popcount(s); if(2*w>NV) continue; if(2*w==NV && !(s&1)) continue;
    TY[NT]=s; COST[NT]=MAXSEP-w*(NV-w);
    for(int j=0;j<NP;j++) INP[NT][j]=((s>>j)&1)!=((s>>(j+1))&1); INP[NT][NP]=1;
    for(int a=0;a<NV;a++) for(int b=0;b<NV;b++) SEP[NT][a][b]=((s>>a)&1)!=((s>>b)&1);
    NT++; }
  for(int j=0;j<NP;j++) nlet[j]=M; nlet[NP]=E;
  for(int e=0;e<M;e++) for(int j=0;j<NV;j++) if(j<NP||e<E){ ordj[nord]=j; orde[nord]=e; nord++; }
  for(int i=0;i<NV;i++) for(int j=i+2;j<NV;j++){ NAi[nna]=i; NAj[nna]=j; nna++; }
  xrec(0,B/2);
  printf("PAR %d CC %d G %s B %d M %d E %d len %dK%+d xconfigs %ld nodes %ld solutions %ld%s\n",PAR,CC,argv[3],B,M,E,NP,off[NP]+E,nx,nodes,sols,sols>=MAXS?" (capped)":"");
  return 0;
}
