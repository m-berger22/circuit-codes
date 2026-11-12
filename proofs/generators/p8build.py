#!/usr/bin/env python3
# S171 p8build.py j [OUTFILE]: EXPLICIT code (no solver) at the p=8 equality point for even j >= 4 ("family 8"):
# (n,k,N) = (33j, 20j-1, 96j) = Byrnes 4k+2l + 4j.  Gap function g on Z_N, invariant under x -> x+P, P = 8j, h = 4j, u = 8j, K = 20j:
#   F residues r (gap K+e[r]) from p8fam.py (two single-serve chains, 2i-1 ladders, 2i-4 E runs);
#   dots: gap N/2 (antipodal), except residue 1: gap N/2-2 and residue P-1: gap N/2+2.
# Checks from the definition (all pairs) and writes hex vertices for snake/check.py.
import sys
sys.argv=[sys.argv[0]]+sys.argv[1:]; j=int(sys.argv[1])
import importlib; sys_argv=sys.argv; sys.argv=[sys.argv[0],str(j)]; f=importlib.import_module('p8fam'); sys.argv=sys_argv
P,K,N,n,k,e=f.P,f.K,f.N,f.n,f.k,f.e
g=[K+e[x%P] if x%P in e else N//2+(-2 if x%P==1 else 2 if x%P==P-1 else 0) for x in range(N)]
lab=[-1]*N; c=0
for t in range(N):
    if lab[t]<0:
        x=t
        while lab[x]<0: lab[x]=c; x=(x+g[x])%N
        assert x==t; c+=1
assert c==n,(c,n)
v=[0]
for t in lab: v.append(v[-1]^(1<<t))
assert v[-1]==0; v=v[:-1]
def valid():
    for a in range(N):
        va=v[a]
        for b in range(a+1,N):
            dc=min(b-a,N-(b-a)); dh=(va^v[b]).bit_count()
            if (dc<k and dh!=dc) or (dc>=k and dh<k): return False
    return True
ok=valid(); print(f'j={j} (n,k,N)=({n},{k},{N}) excess {N-(4*k+2*(2*n-3*k-1))}:', 'VALID' if ok else 'INVALID',flush=True)
if ok and len(sys.argv)>2:
    with open(sys.argv[2],'w') as o:
        o.write(f'# n {n} k {k} N {N} explicit family 8 (p=8 equality point, even j={j}; theory/struct/ex4/p8/p8build.py, S171); transition word: '+' '.join(map(str,lab))+'\n')
        for x in v: o.write(f'{x:x}\n')
