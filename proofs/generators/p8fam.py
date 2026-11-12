#!/usr/bin/env python3
# S171 p8fam.py j [DOTR]: conjectured F-skeleton at the p=8 equality point for EVEN j = 2i >= 4: (n,k,N) = (33j, 20j-1, 96j), K=20j,
# u = P = 8j, h = 4j, invariant under x -> x+P.  Residues mod P (excess of the gap in brackets):
#   single D : h-1(+1) -> 0(+0) -> h(+u-5) -> P-5(+u+4)         single E': h+2(+0) -> 2(+1) -> h+3(+u+4) -> 7(+u-5)
#   ladders  : a(+1) -> a+h+1(+0) -> a+1(+1) -> a+h+2(+2u-2)  for a = 4+8t (t=0..i-1) and a = h+8+8t (t=0..i-2)
#   E runs   : r(+u/2) x4 for r = 7+8t (t=1..i-2) and r = h+11+8t (t=0..i-3)
# Dots are left to the solver (genlazy2, FIX on all F gaps); prints the dot excesses per residue.
import sys,os,subprocess,re
j=int(sys.argv[1]); DOTR=int(sys.argv[2]) if len(sys.argv)>2 else 4*j
assert j%2==0 and j>=4; i=j//2; P=8*j; h=4*j; u=P; K=20*j; N=96*j; n=33*j; k=K-1
e={}
def chain(r0,exs):
    r=r0
    for x in exs:
        assert r%P not in e,(r%P); e[r%P]=x; r=r+h+x
    assert (r-r0)%P==0 and sum(exs)==2*u
chain(h-1,[1,0,u-5,u+4]); chain(h+2,[0,1,u+4,u-5])
for a in [4+8*t for t in range(i)]+[h+8+8*t for t in range(i-1)]: chain(a,[1,0,1,2*u-2])
for r in [7+8*t for t in range(1,i-1)]+[h+11+8*t for t in range(i-2)]: e[r]=u//2
w=''.join('F' if r in e else '.' for r in range(P))
assert len(e)==5*j and '..' not in w+w[0], (len(e),w)
if __name__=='__main__':
    print('word',w)
    fix=','.join(f'{x}:{K+e[x%P]}' for x in range(N) if x%P in e)
    out=f'runs/p8fam_{j}.sol'
    if os.path.exists(out): os.remove(out)
    env=dict(os.environ,EXTRA='c1.py',DOTR=str(DOTR),QUIET='1',OUT=out,FIX=fix,ALLOW=','.join(map(str,sorted(set(e.values())))),EQP=str(P),EQR=f'0-{N+P}')
    o=subprocess.run(['python3','genlazy2.py',str(n),str(k),w*12],capture_output=True,text=True,env=env).stdout
    m=re.search(r'(UNSAT after.*|SAT it \d+ \S+ windows \d+ check from definition: \w+)',o); print(f'j={j}',m.group(1) if m else '?? '+o[-300:])
    m=re.search(r'VALID  gaps (.*)',o)
    if m:
        g=[int(x.split(':')[1]) for x in m.group(1).split()[:P]]
        print('dots (residue:d): '+' '.join(f'{r}:{g[r]-N//2}' for r in range(P) if r not in e))
