#!/usr/bin/env python3
# S169 ex4fam7.py q [out] : EXPLICIT zero-slack EXCESS-4 family 7, l = 8q+2 (q >= 1): k=(l^2+2l-4)/4, K=k+1, n=(3k+l+1)/2,
#   N = l(l+4) = 4k+2l+4.  Invariant under x -> x+2l.  One period (2l positions) = blocks
#       FF. FF. (F.)^(2q-2) FF. (F.)^(2q-1) FF. (F.)^(4q-1)
#   F gaps K+e with e, block by block:
#       (1,1) (1,3l/2) (l/2-1)^(2q-2) (0,1) (l/2-1),(3l/2)^(2q-2) (0,2l-2) 0^(2q-1),1,2l-2,1^(2q-2)
#   dots (first-half residue r -> partner, gap): r=2: gap N/2+1; odd r in [5,4q+1]: gap N/2 (partner r+l);
#       even r in [4q+4, l]: gap N/2-1 (partner r+l-1); the partners get the complementary gap.
import sys
from ex4fam2 import skeleton
from ex4fam import check, verts
def gaps(q):
    l,k,K,N,per,g=skeleton(q); p=2*l; H=N//2
    def pair(r,a):
        u=(r+a)%p; assert per[r]=='.' and per[u]=='.' and g[r] is None and g[u] is None,(q,r,u); g[r]=a; g[u]=N-a
    pair(2,H+1)
    for r in range(5,4*q+2,2): pair(r,H)
    for r in range(4*q+4,l+1,2): pair(r,H-1)
    assert all(x is not None for x in g)
    return l,k,N,per,g
def word(q):
    l,k,N,per,g=gaps(q); p=2*l; T=[-1]*N; c=0
    for t in range(N):
        if T[t]<0:
            u=t
            while T[u]<0: T[u]=c; u=(u+g[u%p])%N
            assert u==t; c+=1
    return l,k,N,T
if __name__=='__main__':
    q=int(sys.argv[1]); l,k,N,T=word(q); n=max(T)+1
    assert n==(3*k+l+1)//2 and N==4*k+2*l+4,(n,N)
    ok=check(T,k,2*l)
    print(f'q={q} l={l} n={n} k={k} N={N} = 4k+2l+4: {"VALID" if ok else "INVALID"} (own check, shift-reduced)',flush=True)
    if len(sys.argv)>2:
        open(sys.argv[2],'w').write(f'# n {n} k {k} N {N} explicit zero-slack excess-4 family 7 (ex4fam7.py q={q}, l={l}, S169); transition word: '+' '.join(map(str,T))+'\n'+' '.join(verts(T))+'\n')
