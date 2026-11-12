#!/usr/bin/env python3
# S170 ladfam.py j i [m] [ladders] : design from a ladder list with FORCED E fill (design3.py logic), then the definition check.
# e0 = 4j, p = 4j*i (design period), u = m*p, e = m*e0, K = m*p(2i+1)/2, N = 4K+2u.   Default ladders = the uniform family
#   j even: A0 B4 C8 C13 .. C(8+5t), t = 0..j-2          j odd: C0 C5 .. C(5t), t = 0..j-1
# ladders given as e.g. "A0,B4,C8".  Ladder types (gap excesses over K from the start residue a, steps h+excess mod p):
#   A = (1,1,0,X), B = (1,1,X,0), C = (1,0,1,X), X = 2u-2.
import sys
from ex4fam import check, verts
from gapcode import build
TY={'A':(1,1,0,-2),'B':(1,1,-2,0),'C':(1,0,1,-2)}
def default_ladders(j):
    return [('A',0),('B',4)]+[('C',8+5*t) for t in range(j-1)] if j%2==0 else [('C',5*t) for t in range(j)]
def design(j,i,m,lads):
    p=4*j*i; h=p//2; u=m*p; K=m*p*(2*i+1)//2; N=4*K+2*u; X=2*u-2
    g=[N//2]*p; own=set(); M=set()
    for ty,a in lads:
        r=a%p
        for ex in TY[ty]:
            if r in own: return None,'ladder residues collide'
            own.add(r); x=(r+ex)%p
            if x in M: return None,'M collides'
            M.add(x); g[r]=K+(ex if ex>=0 else X); r=(r+h+ex)%p
        if r!=a%p: return None,'ladder does not close'
    start=min(M); run=[]; E1=[]
    for t in range(1,p+1):
        r=(start+t)%p
        if r in M:
            if run:
                if len(run)%2==0: return None,'even run of non-members'
                E1+=run[1::2]; run=[]
        else: run.append(r)
    for x in E1:
        r=(x-h)%p
        if r in own: return None,'E residue collides with a ladder'
        own.add(r); g[r]=N//4
    nF=h+j
    if len(own)!=nF: return None,f'F count {len(own)} != {nF}'
    return (p,K,N,g),'ok'
if __name__=='__main__':
    j,i=int(sys.argv[1]),int(sys.argv[2]); m=int(sys.argv[3]) if len(sys.argv)>3 else 1
    lads=[(x[0],int(x[1:])) for x in sys.argv[4].split(',')] if len(sys.argv)>4 and sys.argv[4] else default_ladders(j)
    d,msg=design(j,i,m,lads)
    if d is None: print(f'j={j} i={i} m={m}: NO DESIGN ({msg})'); sys.exit()
    p,K,N,g=d; k=K-1
    try: T=build(N,g)
    except AssertionError: print(f'j={j} i={i} m={m}: orbits do not close'); sys.exit()
    n=max(T)+1; l=2*n-3*k-1; ok=check(T,k,p)
    print(f'j={j} i={i} m={m} p={p} (n,k,N)=({n},{k},{N}) l={l} excess={N-4*k-2*l}: {"VALID" if ok else "INVALID"}  word '+(''.join('.' if x==N//2 else ('E' if x==N//4 else 'F') for x in g) if p<=100 else ''),flush=True)
    if ok and len(sys.argv)>5: open(sys.argv[5],'w').write(f'# n {n} k {k} N {N} ladder family (ladfam.py j={j} i={i} m={m}, S170); transition word: '+' '.join(map(str,T))+'\n'+' '.join(verts(T))+'\n')
