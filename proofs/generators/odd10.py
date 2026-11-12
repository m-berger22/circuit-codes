#!/usr/bin/env python3
# S171 odd10.py p i [OUT]: EXPLICIT two-parameter odd-line family ("family 10"; proved: Theorems 36, 36', Lean K_family10; p = 9 is family 9 with
# antipodal dots).  p = 1 mod 4, p >= 9, i >= 0:  l = p+(2p-2)i, k = (p^2-1)/2 + p(p+1)i, e = 4i+2, N = 4k+2l+e, n = (3k+l+1)/2,
# K = k+1, u = l+(e-4)/2 = p-1+2pi.  Gap function of period p (residues r mod p):
#   r = p-3 and r = (p-5)/2 : K          r = p-2 : K+u+(p-5)/2          r = p-5 : K+u-(p-5)/2
#   every other even r <= p-7 : N/4 (E runs)          odd r <= p-4 and r = p-1 : N/2 (dots, all antipodal)
# Checks the definition by all pairs (or, with FAST=1, only pairs at cyclic distance >= k via windows: not implemented -> all pairs).
import sys
p,i=int(sys.argv[1]),int(sys.argv[2]); assert p%4==1 and p>=9
l=p+(2*p-2)*i; k=(p*p-1)//2+p*(p+1)*i; e=4*i+2; N=4*k+2*l+e; n=(3*k+l+1)//2; K=k+1; u=l+(e-4)//2
assert N%p==0 and N%4==0 and (N//4)%p==0 and (2*K)%p==1
gp={}
for r in range(p):
    if r%2==1 and r!=p-2: gp[r]=N//2
    elif r==p-1: gp[r]=N//2
    elif r in (p-3,(p-5)//2): gp[r]=K
    elif r==p-2: gp[r]=K+u+(p-5)//2
    elif r==p-5: gp[r]=K+u-(p-5)//2
    else: gp[r]=N//4
g=[gp[x%p] for x in range(N)]
lab=[-1]*N; c=0
for t in range(N):
    if lab[t]<0:
        x=t
        while lab[x]<0: lab[x]=c; x=(x+g[x])%N
        assert x==t,(p,i,t); c+=1
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
ok=valid()
# upper bound (Lemma 2 + Lemma 1 at L = 2K-1), as in PROOF15 sec. 1
L=2*K-1; ub=(k>3*l-3) and (N-2*n)*(4*L-N)-2*N*(k//2)==0 and all((N2-2*n)*(4*L-N2)-2*N2*(k//2)>0 for N2 in range(N+2,5*k+4,2))
print(f'p={p} i={i} e={e} l={l} (n,k,N)=({n},{k},{N}):','VALID' if ok else 'INVALID','| upper bound', 'ok' if ub else 'NOT ok',flush=True)
if ok and len(sys.argv)>3:
    with open(sys.argv[3],'w') as o:
        o.write(f'# n {n} k {k} N {N} explicit odd-line family 10 (p={p}, i={i}, excess {e}; theory/struct/ex4/p8/odd10.py, S171); transition word: '+' '.join(map(str,lab))+'\n')
        for x in v: o.write(f'{x:x}\n')
