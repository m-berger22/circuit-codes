#!/usr/bin/env python3
# S170 fam6m.py p m [out] : family-6 residue design of period p (p = 0 mod 4, p >= 8) with K = m*p(p+2)/4, N = m*p(p+4), m ODD:
# u = m*p, excess e = 4m, k = K-1, l = u-(e-4)/2, n = N(3p-2)/(8p).  Gaps on residues mod p: 1: K | 2: K+X, X = N-4K-2 = 2u-2 |
# p/2, p/2+1: K+1 | E (even 4..p/2-2, odd p/2+3..p-1): N/4 | others: dots N/2.   m = 1 is family 6 (ex4fam.py).
import sys
from ex4fam import check, verts
from gapcode import build
def gaps(p,m):
    K=m*p*(p+2)//4; N=m*p*(p+4); g=[N//2]*p
    g[1]=K; g[2]=N-3*K-2; g[p//2]=g[p//2+1]=K+1
    for r in list(range(4,p//2-1,2))+list(range(p//2+3,p,2)): g[r]=N//4
    return K-1,N,g
if __name__=='__main__':
    p,m=int(sys.argv[1]),int(sys.argv[2]); k,N,g=gaps(p,m)
    try: T=build(N,g)
    except AssertionError: print(f'p={p} m={m}: orbits do not close'); sys.exit()
    n=max(T)+1; l=2*n-3*k-1; ok=check(T,k,p)
    print(f'p={p} m={m} n={n} k={k} l={l} N={N} excess={N-4*k-2*l}: {"VALID" if ok else "INVALID"}',flush=True)
    if ok and len(sys.argv)>3: open(sys.argv[3],'w').write(f'# n {n} k {k} N {N} family 6 design x m (fam6m.py p={p} m={m}, S170); transition word: '+' '.join(map(str,T))+'\n'+' '.join(verts(T))+'\n')
