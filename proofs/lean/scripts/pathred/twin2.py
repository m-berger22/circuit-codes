#!/usr/bin/env python3
# python twin of Ccformal/PathReduced.lean (finite layer, v2).  usage: twin2.py par d1 d2 d3 d4 M E B [split]
# slots s = 5e+j (j = s%5 piece, e = s//5 offset); dummy iff j==4 and e>=E; value (pat,id):
# pat = sum_{j=1..4} 2^j [coordinate differs between u_0 and u_j] (even, < 32), id = first non-dummy slot with the same coordinate.
# state packed: TY = sum pat_s 32^s, ID = sum id_s 32^s.
import sys
par,d1,d2,d3,d4,M,E,B=map(int,sys.argv[1:9]); SPLIT=int(sys.argv[9]) if len(sys.argv)>9 else 0
df=[0,d1,d2,d3,d4]
def nl(j): return M if j<4 else E
def sepn(pat,j,j2): return (pat//2**j+pat//2**j2)%2
def req1(j,j2,e,e2): return ((j2-j+1)*par+df[j]+df[j2]+e+e2+1)%2
def xidx(j,j2): return j+(0 if j2-j==2 else 3 if j2-j==3 else 5)
def D1(x,j,j2):
    if j2==j+1: return 1+df[j]-df[j2]
    return req1(j,j2,0,0)+2*x[xidx(j,j2)]
cost=[3-sum(sepn(p,i,j) for i in range(5) for j in range(i+1,5))//2 for p in range(32)]
def dummy(s): return s%5==4 and s//5>=E
def used(j,j2,e,e2): return j2!=j+1 or e+df[j2]<=e2+1+df[j]
def maskA(get,j,e):
    m=0
    for t in range(e): m|=2**get(5*t+j)[1]
    return m
def S(get,j,e,m2,a,b): return sum(1 if m2//2**get(5*t+j)[1]%2==1 else 2*(1-sepn(get(5*t+j)[0],a,b)) for t in range(e))
def pairok(x,get,j,e,m,j2,e2,m2):
    return (not used(j,j2,e,e2)) or req1(j,j2,e,e2)+e+e2 <= D1(x,j,j2)+S(get,j,e,m2,j,j2)+S(get,j2,e2,m,j,j2)
def isrep(get,t): return get(t)[1]==t and not dummy(t)
def budget(x,get,n): return sum(x)+sum(cost[get(t)[0]] for t in range(n) if isrep(get,t))<=B
def pairs(x,get,s,j,e):
    m=maskA(get,j,e+1)
    for j2 in range(5):
        if j2==j: continue
        for e2 in range(nl(j2)+1):
            if e2>0 and s<5*(e2-1)+j2: continue
            m2=maskA(get,j2,e2)
            if not (pairok(x,get,j,e+1,m,j2,e2,m2) if j<j2 else pairok(x,get,j2,e2,m2,j,e+1,m)): return False
    return True
def stepok(x,s,get):
    j=s%5; e=s//5; ty,i=get(s)
    if dummy(s): return ty==0 and i==s
    return ty<32 and ty%2==0 and (4<=j or sepn(ty,j,j+1)==1) and i<=s and isrep(get,i) and get(i)[0]==ty \
        and budget(x,get,s+1) and pairs(x,get,s,j,e)
def gty(TY,t): return TY//32**t%32
N=5*M; nodes=0; sols=0; per={}
def dfs(x,n,s,TY,ID,key):
    global nodes,sols
    if n==0: sols+=1; return
    if not dummy(s): nodes+=1; per[key]=per.get(key,0)+1
    def tr(ty,i,ci):
        TY2=TY+ty*32**s; ID2=ID+i*32**s
        if stepok(x,s,lambda t:(gty(TY2,t),gty(ID2,t))): dfs(x,n-1,s+1,TY2,ID2,key+(ci,) if len(key)<SPLIT else key)
    if dummy(s): tr(0,s,0)
    else:
        for q in range(16): tr(2*q,s,q)
        for t in range(s): tr(gty(TY,t),t,16+t)
nx=0
import itertools
for x in itertools.product(range(B+1),repeat=6):
    x=x[::-1]   # x0 fastest? (order irrelevant)
    if sum(x)<=B: nx+=1; dfs(x,N,0,0,0,(x,))
print(sys.argv[1:],'xconfigs',nx,'nodes',nodes,'solutions',sols)
if SPLIT:
    for k in sorted(per): print(k,per[k])
print('cost',cost[0:32:2])
