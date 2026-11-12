#!/usr/bin/env python3
# S171 odd9.py i [OUT]: EXPLICIT odd-line family "p = 9" (guessed from the i = 1 solver code): e = 4i+2, l = 16i+9, u = 18i+8,
# K = 90i+41, k = K-1, N = 396i+180 = 4k+2l+e, n = (3k+l+1)/2. Shift-9 invariant; residues mod 9:
#   E run  : 0 (gap K+u/2);     chain: 2 (K) -> 7 (K+u+2) -> 4 (K+u-2) -> 6 (K) -> 2;
#   dots   : 1, 3 antipodal (gap N/2); 5: gap N/2+3 (partner on residue 8), 8: gap N/2-3.
import sys
i=int(sys.argv[1]); e=4*i+2; l=16*i+9; u=18*i+8; K=90*i+41; k=K-1; N=396*i+180; n=(3*k+l+1)//2
assert N==4*k+2*l+e and N%9==0
gp={0:K+u//2,2:K,7:K+u+2,4:K+u-2,6:K,1:N//2,3:N//2,5:N//2+3,8:N//2-3}
g=[gp[x%9] for x in range(N)]
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
ok=valid(); print(f'i={i} e={e} l={l} (n,k,N)=({n},{k},{N}):','VALID' if ok else 'INVALID',flush=True)
if ok and len(sys.argv)>2:
    with open(sys.argv[2],'w') as o:
        o.write(f'# n {n} k {k} N {N} explicit odd-line family p=9 (excess {e}; theory/struct/ex4/p8/odd9.py, S171); transition word: '+' '.join(map(str,lab))+'\n')
        for x in v: o.write(f'{x:x}\n')
