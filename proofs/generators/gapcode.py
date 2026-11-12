#!/usr/bin/env python3
# S169 gapcode.py n k N "g_0 g_1 .. g_{s-1}" [out] : build the code invariant under x -> x+s from its gap function on residues
# (next occurrence of the coordinate at x is x+g(x mod s)), check the definition (shift-reduced), optionally write a code file.
import sys
from ex4fam import check, verts
def build(N,g):
    s=len(g); T=[-1]*N; c=0
    for t in range(N):
        if T[t]<0:
            u=t
            while T[u]<0: T[u]=c; u=(u+g[u%s])%N
            assert u==t,'orbit does not close'; c+=1
    return T
if __name__=='__main__':
    n,k,N=map(int,sys.argv[1:4]); g=list(map(int,sys.argv[4].split())); s=len(g); assert N%s==0
    T=build(N,g); l=2*n-3*k-1
    from collections import Counter
    use=Counter(Counter(T).values())
    ok=check(T,k,s)
    print(f'n={max(T)+1} (want {n}) k={k} l={l} N={N} excess={N-4*k-2*l} usage={dict(use)} period={s}: {"VALID" if ok and max(T)+1==n else "INVALID"}')
    if ok and len(sys.argv)>5:
        open(sys.argv[5],'w').write(f'# n {n} k {k} N {N} shift-{s} invariant code from its gap function (gapcode.py, S169); gaps: {sys.argv[4]}; transition word: '+' '.join(map(str,T))+'\n'+' '.join(verts(T))+'\n')
