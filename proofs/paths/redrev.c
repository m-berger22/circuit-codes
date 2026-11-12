// redrev.c: the reduced boundary model (PROOF_threshold.md), column order tail,3,2,1,0. usage: redrev PAR CC G M E [maxsol] [cap]; env NTAB, CAPS, COLT
// G = string of 0/m (piece length K or K-1). Output: nodes, solutions. Coordinates <= 64.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef uint64_t u64;
int PAR,CC,NP,NV,M,E,G[8],off[9],base[9][9],MAXSEP,B; long MAXS=1000000000L;
int NT,TY[256],COST[256],INP[256][9],SEP[256][9][9];
int nlet[9],let[9][40],ctype[64],nc,budget,X[9][9];
signed char sv[9*41][9*41]; int occ[64][9],filled[9];
#define VID(j,e) ((j)*41+(e))
int ordj[400],orde[400],nord; long nodes,sols; int CAP=1000,used[256]; int NTAB=-1,XI=-1,XJ=-1,singIdx=-1;
int CAPT[256],HASCAPS=0;
static inline int capfor(int t){ if(HASCAPS) return CAPT[t]; if(NTAB<0) return CAP; int m=TY[t]; if(COST[t]>0) return 1;
  if(XI>=0) return ((m>>XI&1)||(m>>XJ&1))? NTAB+1 : NTAB;
  if(singIdx>=0) return (m>>singIdx&1)? NTAB : NTAB+1; return NTAB+1; }
static inline int reqrel(int a,int r){ return -1 + ((((a-1)*PAR + r + 1)%2+2)%2); }
u64 pre(int j,int e){ u64 m=0; for(int i=0;i<e;i++) m|=1ULL<<let[j][i]; return m; }
int checkvertex(int j,int e){ return 1; }
// place letter c at (j,e): build the row of the new vertex (j,e+1) from that of (j,e); 1 = all requirements hold
static inline int place(int j,int e,int c){
  int V=VID(j,e),V2=VID(j,e+1),t=ctype[c];
  for(int j2=0;j2<NV;j2++){ if(j2==j) continue; int sg=SEP[t][j][j2]?-1:1; int oc=occ[c][j2]; int top=filled[j2];
    for(int e2=0;e2<=top;e2++){ int w=VID(j2,e2); int s=sv[V][w]+((oc<e2)?-sg:sg);
      int ja,ea,jb,eb; if(j<j2){ja=j;ea=e+1;jb=j2;eb=e2;} else {ja=j2;ea=e2;jb=j;eb=e+1;}
      int r=off[jb]-off[ja]+eb-ea;
      if(!(jb==ja+1 && r<-1) && s<reqrel(jb-ja,r)) return 0;
      sv[V2][w]=s; sv[w][V2]=s; } }
  return 1;
}
#define HS 262144
char hkey[HS][260]; long hcnt[HS];
void hadd(const char*k){ unsigned h=5381; for(const char*p=k;*p;p++) h=h*33+*p; h%=HS; while(hkey[h][0] && strcmp(hkey[h],k)) h=(h+1)%HS; if(!hkey[h][0]) strncpy(hkey[h],k,259); hcnt[h]++; }
int CT0=-1,CT1=-1;
static void pname(char*o,int m){ if(__builtin_popcount(m)>2) m^=(1<<NV)-1; int q=0; for(int j=0;j<NV;j++) if(m>>j&1) o[q++]='0'+j; o[q]=0; }
void coltype(char*out,int col){ char parts[5][24]; int np=0;
  for(int c=0;c<nc;c++){ int m=TY[ctype[c]],lab=0,past=0; for(int j=0;j<NV;j++){ if(occ[c][j]<col){ m^=1<<j; past=1; } else if(occ[c][j]==col) lab|=1<<j; }
    if(!lab) continue; char a[8],b[8],l[8]; int q=0; for(int j=0;j<NV;j++) if(lab>>j&1) l[q++]='0'+j; l[q]=0; pname(a,m); pname(b,m^lab);
    sprintf(parts[np++],"%s%s-%s>%s",past?"":"*",a,l,b); }
  for(int i=0;i<np;i++) for(int j=i+1;j<np;j++) if(strcmp(parts[i],parts[j])>0){ char t[24]; strcpy(t,parts[i]); strcpy(parts[i],parts[j]); strcpy(parts[j],t); }
  out[0]=0; for(int i=0;i<np;i++){ strcat(out,parts[i]); strcat(out," "); } }
int pendc[9][41];
void rec(int i){
  if(sols>=MAXS) return;
  if(i==nord){ sols++; if(CT0>=0){ char k[260]="",k2[60]; for(int col=CT0;col<=CT1;col++){ coltype(k2,col); strcat(k,k2); if(col<CT1) strcat(k,"| "); } hadd(k); } return; }
  int j=ordj[i],e=orde[i]; nodes++;
  int pc=pendc[j][e];
  for(int c=(pc>=0?pc:0);c<(pc>=0?pc+1:nc);c++){ int t=ctype[c];
    if(!INP[t][j] || occ[c][j]<99) continue;
    int setp=0;
    if(j>=1 && INP[t][j-1]){ if(occ[c][j-1]==99){ pendc[j-1][e]=c; setp=1; } }   /* else already placed in an earlier column */
    let[j][e]=c; if(place(j,e,c)){ occ[c][j]=e; filled[j]=e+1; rec(i+1); filled[j]=e; occ[c][j]=99; } let[j][e]=-1;
    if(setp) pendc[j-1][e]=-1; }
  if(pc>=0) return;
  if(nc<64) for(int t=0;t<NT;t++){
    if(!INP[t][j] || COST[t]>budget || used[t]>=capfor(t)) continue;
    int oldsing=singIdx; if(NTAB>=0 && COST[t]>0){ int si=__builtin_ctz(TY[t]); int bad=0; for(int u=0;u<NT;u++) if(COST[u]==0 && (TY[u]>>si&1) && used[u]>NTAB) bad=1; if(bad) continue; singIdx=si; }
    ctype[nc]=t; let[j][e]=nc; nc++; budget-=COST[t]; used[t]++;
    for(int q=0;q<NV;q++) occ[nc-1][q]=99;
    int setp=0; if(j>=1 && INP[t][j-1]){ pendc[j-1][e]=nc-1; setp=1; }
    if(place(j,e,nc-1)){ occ[nc-1][j]=e; filled[j]=e+1; rec(i+1); filled[j]=e; occ[nc-1][j]=99; }
    if(setp) pendc[j-1][e]=-1;
    nc--; let[j][e]=-1; budget+=COST[t]; used[t]--; singIdx=oldsing; }
  else { fprintf(stderr,"coordinate overflow\n"); exit(1); }
}
int NAi[40],NAj[40],nna; long nx;
void xrec(int q,int rem){
  if(q==nna){ nx++; nc=0; XI=XJ=-1; singIdx=-1; for(int a=0;a<nna;a++) if(X[NAi[a]][NAj[a]]){ XI=NAi[a]; XJ=NAj[a]; } int sx=0; for(int a=0;a<nna;a++) sx+=X[NAi[a]][NAj[a]]; budget=B-2*sx;
    for(int j=0;j<NV;j++) for(int e=0;e<40;e++) let[j][e]=-1;
    for(int j=0;j<NV;j++){ filled[j]=0; for(int j2=0;j2<NV;j2++) if(j2!=j) sv[VID(j,0)][VID(j2,0)]=base[j][j2]+2*X[j][j2]; }
    { int ok=1; for(int j=0;j<NV;j++) for(int j2=j+1;j2<NV;j2++){ int r=off[j2]-off[j]; if(!(j2==j+1&&r<-1) && sv[VID(j,0)][VID(j2,0)]<reqrel(j2-j,r)) ok=0; } if(ok) rec(0); } return; }
  for(int v=0;v<=rem;v++){ X[NAi[q]][NAj[q]]=X[NAj[q]][NAi[q]]=v; xrec(q+1,rem-v); }
  X[NAi[q]][NAj[q]]=X[NAj[q]][NAi[q]]=0;
}
int main(int argc,char**argv){
  PAR=atoi(argv[1]); CC=atoi(argv[2]); NP=strlen(argv[3]); NV=NP+1; for(int i=0;i<NP;i++) G[i]=argv[3][i]=='0'?0:-1;
  M=atoi(argv[4]); E=atoi(argv[5]); if(argc>6) MAXS=atol(argv[6]); if(argc>7) CAP=atoi(argv[7]); if(getenv("NTAB")) NTAB=atoi(getenv("NTAB"));
  MAXSEP=NV*NV/4; off[0]=0; for(int i=0;i<NP;i++) off[i+1]=off[i]+G[i];
  int tot=0; for(int i=0;i<NV;i++) for(int j=i+1;j<NV;j++){ int b=(j==i+1)?G[i]:reqrel(j-i,off[j]-off[i]); base[i][j]=base[j][i]=b; tot+=b; }
  if(CC-tot<0){ printf("PAR %d CC %d G %s: Plotkin impossible outright (deficit %d)\n",PAR,CC,argv[3],tot-CC); return 0; }
  B=CC-tot;
  for(int s=0;s<(1<<NV);s++){ int w=__builtin_popcount(s); if(2*w>NV) continue; if(2*w==NV && !(s&1)) continue;
    TY[NT]=s; COST[NT]=MAXSEP-w*(NV-w);
    for(int j=0;j<NP;j++) INP[NT][j]=((s>>j)&1)!=((s>>(j+1))&1); INP[NT][NP]=1;
    for(int a=0;a<NV;a++) for(int b=0;b<NV;b++) SEP[NT][a][b]=((s>>a)&1)!=((s>>b)&1);
    NT++; }
  if(getenv("COLT")) sscanf(getenv("COLT"),"%d,%d",&CT0,&CT1);
  { char*cs=getenv("CAPS"); if(cs){ HASCAPS=1; for(int t=0;t<NT;t++) CAPT[t]=1000; char buf[256]; strcpy(buf,cs); for(char*p=strtok(buf,",");p;p=strtok(NULL,",")){ int mk,cv; sscanf(p,"%d:%d",&mk,&cv); for(int t=0;t<NT;t++) if(TY[t]==mk) CAPT[t]=cv; } } }
  for(int j=0;j<NP;j++) nlet[j]=M; nlet[NP]=E;
  for(int i=0;i<NP;i++) if(G[i]!=0){ fprintf(stderr,"redrev: G must be all 0\n"); return 1; }
  memset(pendc,-1,sizeof pendc);
  for(int e=0;e<M;e++) for(int j=NV-1;j>=0;j--) if(j<NP||e<E){ ordj[nord]=j; orde[nord]=e; nord++; }
  for(int i=0;i<NV;i++) for(int j=i+2;j<NV;j++){ NAi[nna]=i; NAj[nna]=j; nna++; }
  xrec(0,B/2);
  printf("PAR %d CC %d G %s B %d M %d E %d len %dK%+d xconfigs %ld nodes %ld solutions %ld%s\n",PAR,CC,argv[3],B,M,E,NP,off[NP]+E,nx,nodes,sols,sols>=MAXS?" (capped)":"");
  if(CT0>=0){ for(int h=0;h<HS;h++) if(hkey[h][0]) printf("COLT %ld %s\n",hcnt[h],hkey[h]); }
  return 0;
}
