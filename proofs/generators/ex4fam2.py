#!/usr/bin/env python3
# S169 ex4fam2.py q : candidate F skeleton for the zero-slack excess-4 code on l = 8q+2 (k=(l^2+2l-4)/4, N=l(l+4), period 2l).
# One period = blocks  FF. FF. (F.)^(2q-2) FF. (F.)^(2q-1) FF. (F.)^(4q-1)  with F gap excesses (over K)
#   (1,1) (1,3l/2) (l/2-1)^(2q-2) (0,1) (l/2-1),(3l/2)^(2q-2) (0,2l-2) 0^(2q-1),1,2l-2,1^(2q-2).
# Prints the word, the excess list, whether every F orbit closes after 4 steps with gap sum N; with 'sat' as 2nd arg asks
# refl/genlazy.py (shift-2l class, F gaps FIXed) for the dots.
import sys,os,subprocess
def skeleton(q):
    l=8*q+2; k=(l*l+2*l-4)//4; K=k+1; N=l*(l+4); h=l//2-1; b=3*l//2; w=2*l-2
    blocks=[('FF.',[1,1]),('FF.',[1,b])]+[('F.',[h])]*(2*q-2)+[('FF.',[0,1]),('F.',[h])]+[('F.',[b])]*(2*q-2)+[('FF.',[0,w])]+[('F.',[0])]*(2*q-1)+[('F.',[1]),('F.',[w])]+[('F.',[1])]*(2*q-2)
    per=''.join(x for x,_ in blocks); es=[e for _,ee in blocks for e in ee]
    assert len(per)==2*l, (len(per),2*l)
    g=[None]*(2*l); i=0
    for r,c in enumerate(per):
        if c=='F': g[r]=K+es[i]; i+=1
    return l,k,K,N,per,g
if __name__=='__main__':
    q=int(sys.argv[1]); l,k,K,N,per,g=skeleton(q); p=2*l
    ok=True
    for r in range(p):
        if g[r] is None: continue
        x=r; tot=0
        for _ in range(4):
            if g[x%p] is None: ok=False; break
            tot+=g[x%p]; x+=g[x%p]
        if tot!=N: ok=False
    print(f'q={q} l={l} k={k} N={N} word {per}'); print('e:',' '.join('.' if x is None else str(x-K) for x in g)); print('F orbits close:',ok)
    if ok and len(sys.argv)>2:
        n=(3*k+l+1)//2; W=per*(N//p)
        fix=','.join(f'{r}:{g[r]}' for r in range(p) if g[r] is not None)
        env=dict(os.environ,EQP=str(p),EQR=f'0-{N+p}',DOTR=str(l),FIX=fix)
        out=subprocess.run(['python3','../refl/genlazy.py',str(n),str(k),W],capture_output=True,text=True,env=env).stdout
        print(out.strip().split('\n')[-2][:60] if 'VALID' in out else out[-300:])
        import re
        m=re.search(r'VALID  gaps (.*)',out)
        if m:
            gg=[int(x.split(':')[1]) for x in m.group(1).split()[:p]]
            print('dots (gap - N/2):',' '.join(str(gg[r]-N//2) for r in range(p) if per[r]=='.'))
            open(f'runs/fam2_q{q}.g','w').write(' '.join(map(str,gg))+'\n')
