#!/usr/bin/env python3
# S169 ex4fam.py l [out] : EXPLICIT zero-slack EXCESS-4 family, l = 0 mod 4, l >= 8:
#   k = (l^2+2l-4)/4, K = k+1, n = (3k+l+1)/2, N = l(l+4) = 4k+2l+4.  The code is invariant under t -> t+l; gap function on residues:
#   r=0: dot | r=1: K | r=2: K+2l-2 | r=3: dot | r = 4..l/2-1: even -> N/4, odd -> dot | r=l/2, l/2+1: K+1 |
#   r = l/2+2..l-1: even -> dot, odd -> N/4.   dots antipodal (gap N/2).
# So: one 'ladder' orbit with gaps (K, K+1, K+2l-2, K+1), l/2-3 orbits of equally spaced coordinates (gap N/4), l/2-1 antipodal dot orbits.
import sys
def gaps(l):
    assert l%4==0 and l>=8
    k=(l*l+2*l-4)//4; K=k+1; N=l*(l+4); g=[0]*l
    for r in range(l):
        if r in (0,3): g[r]=N//2
        elif r==1: g[r]=K
        elif r==2: g[r]=K+2*l-2
        elif r in (l//2,l//2+1): g[r]=K+1
        elif r<l//2: g[r]=N//4 if r%2==0 else N//2
        else: g[r]=N//2 if r%2==0 else N//4
    return k,N,g
def word(l):
    k,N,g=gaps(l); T=[-1]*N; c=0
    for t in range(N):
        if T[t]<0:
            u=t
            while T[u]<0: T[u]=c; u=(u+g[u%l])%N
            assert u==t; c+=1
    return k,N,T
def check(T,k,rows=None):
    N=len(T); n=max(T)+1
    for i in range(rows or N):
        par=[0]*n; odd=0
        for d in range(1,N):
            c=T[(i+d-1)%N]; par[c]^=1; odd+=1 if par[c] else -1
            if odd<min(d,N-d,k): return False
    return True
def verts(T):
    v=0; out=[]
    for c in T: out.append('%x'%v); v^=1<<c
    assert v==0; return out
if __name__=='__main__':
    l=int(sys.argv[1]); k,N,T=word(l); n=max(T)+1
    assert n==(3*k+l+1)//2 and N==4*k+2*l+4, (n,N)
    ok=check(T,k,l)
    print(f'l={l} n={n} k={k} N={N} = 4k+2l+4: {"VALID" if ok else "INVALID"} (own check, shift-reduced)')
    if len(sys.argv)>2:
        open(sys.argv[2],'w').write(f'# n {n} k {k} N {N} explicit zero-slack excess-4 family (ex4fam.py l={l}, S169); transition word: '+' '.join(map(str,T))+'\n'+' '.join(verts(T))+'\n')
