#!/usr/bin/env python3
# S179 reduced.py PAR C G M E [maxsol] : general K-independent reduced boundary model.
#   PAR = K mod 2 (K = k+1), C = 6d - 10K, G = 4 piece lengths relative to K as a string of 0/m (m = K-1), e.g. 000m,
#   M boundary letters per piece, E tail letters. Word length = sum(G) + E. u_j = piece boundaries.
# Facts used: (F1) index distance D >= k => d_H >= k, parity => req(D) = k + [(D-k) odd]; (F2) equal letters are >= K apart;
# Plotkin on u_0..u_4: sum d(u_i,u_j) = 6d - 2 y1 - 6 y0.  d(u_i,u_j) = req + 2 x_ij (non-adjacent), = piece length (adjacent).
# 0 solutions => no path word of that length for ANY K of that parity with that C (K > M).
import sys, itertools
sys.setrecursionlimit(100000)
PAR=int(sys.argv[1]); C=int(sys.argv[2]); G=[0 if ch=='0' else -1 for ch in sys.argv[3]]; M=int(sys.argv[4]); E=int(sys.argv[5])
MAXS=int(sys.argv[6]) if len(sys.argv)>6 else 10**9
def reqrel(a,r):          # req(D) - K for D = a*K + r
    return -1 + (((a-1)*PAR + r + 1) % 2)
off=[0]; 
for g in G: off.append(off[-1]+g)        # position of u_j = j*K + off[j]
base=[[0]*5 for _ in range(5)]
tot=0
for i in range(5):
    for j in range(i+1,5):
        b = G[i] if j==i+1 else reqrel(j-i, off[j]-off[i])
        base[i][j]=base[j][i]=b; tot+=b
if (C-tot)%2 or C-tot<0:
    print('PAR',PAR,'C',C,'G',sys.argv[3],': Plotkin sum of lower bounds exceeds 6d by',tot-C,'=> impossible outright' if C-tot<0 else 'ODD?'); sys.exit()
B=(C-tot)//2
TYPES=[frozenset(s) for r in (2,1,0) for s in itertools.combinations(range(5),r)]
COST=[{2:0,1:1,0:3}[len(s)] for s in TYPES]
NT=len(TYPES)
INP=[[ (j in p)!=(j+1 in p) for j in range(4)]+[True] for p in TYPES]
SEP=[[[ (a in p)!=(b in p) for b in range(5)] for a in range(5)] for p in TYPES]
order=[(j,e) for e in range(M) for j in range(5) if (j<4 or e<E)]
nlet=[M]*4+[E]
NA=[(i,j) for i in range(5) for j in range(i+2,5)]
tot_nodes=0; tot_sols=0; first=[]
def run(x):
    global tot_nodes,tot_sols
    X=[[0]*5 for _ in range(5)]
    for (a,b),v in zip(NA,x): X[a][b]=X[b][a]=v
    let=[[None]*nlet[j] for j in range(5)]
    ctype=[]; budget=[B-sum(x)]
    def checkvertex(j,e):
        A=set(let[j][:e])
        for j2 in range(5):
            if j2==j: continue
            for e2 in range(nlet[j2]+1):
                if e2>0 and let[j2][e2-1] is None: break
                (ja,ea),(jb,eb)=((j,e),(j2,e2)) if j<j2 else ((j2,e2),(j,e))
                r=off[jb]-off[ja]+eb-ea
                if jb==ja+1 and r<-1: continue
                s=base[j][j2]+2*X[j][j2]
                for c in A.symmetric_difference(let[j2][:e2]): s+= -1 if SEP[ctype[c]][j][j2] else 1
                if s < reqrel(jb-ja,r): return False
        return True
    def rec(i):
        global tot_nodes,tot_sols
        if tot_sols>=MAXS: return
        if i==len(order):
            tot_sols+=1
            if len(first)<3: first.append((x,[[ ''.join(map(str,sorted(TYPES[ctype[c]])))+'.%d'%c for c in let[j]] for j in range(5)]))
            return
        j,e=order[i]; tot_nodes+=1
        for c in range(len(ctype)):
            tau=ctype[c]
            if not INP[tau][j] or c in let[j]: continue
            if j>=1 and INP[tau][j-1] and c not in let[j-1][:max(0,e+G[j-1]+1)]: continue
            let[j][e]=c
            if checkvertex(j,e+1): rec(i+1)
            let[j][e]=None
        for tau in range(NT):
            if not INP[tau][j] or COST[tau]>budget[0]: continue
            if j>=1 and INP[tau][j-1]: continue
            ctype.append(tau); let[j][e]=len(ctype)-1; budget[0]-=COST[tau]
            if checkvertex(j,e+1): rec(i+1)
            let[j][e]=None; ctype.pop(); budget[0]+=COST[tau]
    if checkvertex(0,0): rec(0)
def dists(n,t):
    if n==0: yield (); return
    for v in range(t+1):
        for r in dists(n-1,t-v): yield (v,)+r
nx=0
for x in dists(6,B):
    nx+=1; run(x)
for f in first: print('SOL x=',f[0],f[1])
print('PAR',PAR,'C',C,'G',sys.argv[3],'B',B,'M',M,'E',E,'len 4K%+d'%(sum(G)+E),'xconfigs',nx,'nodes',tot_nodes,'solutions',tot_sols,'(capped)' if tot_sols>=MAXS else '')
