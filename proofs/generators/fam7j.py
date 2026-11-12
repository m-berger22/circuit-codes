#!/usr/bin/env python3
# S170 fam7j.py q j [out] : UNIFORM 'j x family 7' family (j = 1 is family 7 of PROOF7, j = 2 is fam9.py).
# l0 = 8q+2, u = j*l0, P = 2u (period), K = j*l0(l0+2)/4 (= P/2 mod P iff ... see assert), N = 4K+2u = j*l0(l0+4), e = 4j,
# k = K-1, l = u-(e-4)/2, n = (3k+l+1)/2 = j(3 l0-2)(l0+4)/8.   X = 2u-2, a = 4q, b = 2u-1-a.
# Ladders (start residue: gap excesses over K), each repeated at +l0*c, c = 0..j-1:
#   B@0 (1,1,X,0) | C@4q (1,0,1,X) | Wf@4q+4+u (0,b,a,1) | Wc@-2i (0,a,1,b), i = 1..2q-2.
# Dots: r in {odd 1..4q-1} u {4q+2}, +l0*c: gap N/2+1 (partner r+N/2+1 gets N/2-1); all other dots antipodal.
import sys
from ex4fam import check, verts
def design(q,j):
    l0=8*q+2; u=j*l0; P=2*u; K=j*l0*(l0+2)//4; N=4*K+2*u; X=2*u-2; a=4*q; b=2*u-1-a
    lad=[(0,(1,1,X,0)),(4*q,(1,0,1,X)),(4*q+4+u,(0,b,a,1))]+[(-2*i,(0,a,1,b)) for i in range(1,2*q-1)]
    g=[None]*P
    for r0,tp in lad:
        for c in range(j):
            x=r0+l0*c
            for ex in tp:
                if g[x%P] is not None: return None
                g[x%P]=K+ex; x+=K+ex
            if (x-r0-l0*c)%P: return None
    for c in range(j):
        for r in list(range(1,4*q,2))+[4*q+2]:
            x=(r+l0*c)%P; y=(x+N//2+1)%P
            if g[x] is not None or g[y] is not None: return None
            g[x]=N//2+1; g[y]=N//2-1
    g=[N//2 if v is None else v for v in g]
    return l0,u,P,K,N,g
def full(g,N,P):
    T=[-1]*N; cid=0
    for t in range(N):
        if T[t]<0:
            x=t
            while T[x]<0: T[x]=cid; x=(x+g[x%P])%N
            if x!=t: return None
            cid+=1
    return T
if __name__=='__main__':
    q,j=int(sys.argv[1]),int(sys.argv[2]); d=design(q,j)
    if d is None: print(f'q={q} j={j}: residues collide / ladders do not close'); sys.exit()
    l0,u,P,K,N,g=d; k=K-1; e=4*j; l=u-(e-4)//2; n=(3*k+l+1)//2
    T=full(g,N,P)
    ok=T is not None and max(T)+1==n and check(T,k,P)
    print(f'q={q} j={j} l0={l0} u={u} P={P} (n,k,N)=({n},{k},{N}) l={l} excess={N-4*k-2*l if ok else "?"}: {"VALID" if ok else "INVALID"}',flush=True)
    if ok and len(sys.argv)>3: open(sys.argv[3],'w').write(f'# n {n} k {k} N {N} j x family 7 (fam7j.py q={q} j={j}, S170); gaps mod {P}: '+' '.join(map(str,g))+'; transition word: '+' '.join(map(str,T))+'\n'+' '.join(verts(T))+'\n')
