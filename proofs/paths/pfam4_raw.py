#!/usr/bin/env python3
# S179 pfam4_raw.py : builder for the odd-K second-step family (pfam4.py picks the options; `python3 pfam4_raw.py scan` = the search
# over order choices that selected them). K = 6n+1, d = 10n+2, k = K-1, length 4K+2n+3 = (13K+8)/3, n >= 2.
# Types 14, 34 have n+1 coordinates, all other pair types n.
import sys, itertools
from chk import check
TYPES=['01','02','03','04','12','13','14','23','24','34']
def build(n,opt):
    oS,p04,o12t,o14a,o23,o14b,o13,o12p=opt
    K=6*n+1; E=2*n+3; z=n+1
    cnt={t:(n+1 if t in ('14','34') else n) for t in TYPES}
    base={}; b=0
    for t in TYPES: base[t]=b; b+=cnt[t]
    w=[None]*(4*K+E)
    def put(j,e,ty,i):
        assert 1<=i<=cnt[ty],(ty,i); assert w[j*K+e] is None,(j,e); w[j*K+e]=base[ty]+i-1
    def order(lst,o): return lst if o==0 else lst[::-1]
    sig=order(list(range(1,n+1)),oS)
    put(0,0,'13',1); put(1,0,'23',1); put(2,0,'34',1); put(3,0,'14',z); put(4,0,'02',1)
    put(0,1,'14',1); put(1,1,'13',1); put(2,1,'13',1); put(3,1,'04',n); put(4,1,'01',1)
    # tail even rows 2i (i=1..n) and 2n+2: one 04_n at block p04, the others 12 in order
    t12=order(list(range(1,n+1)),o12t); slots=[2*i for i in range(1,n+1)]+[2*n+2]
    pos04={'f':2,'l':2*n,'e':2*n+2}[p04]; q=0
    for r in slots:
        if r==pos04: put(4,r,'04',n)
        else: put(4,r,'12',t12[q]); q+=1
    for i in range(1,n+1):
        X=('02',1) if i==1 else ('13',i)
        put(0,2*i,*X); put(1,2*i+1,*X); put(2,2*i+1,*X)
        if i<n: put(1,2*i,'23',i+1); put(0,2*i+1,'14',i+1); put(3,2*i+1,'04',i)
        else: put(1,2*i,'01',1); put(0,2*i+1,'12',1); put(3,2*i+1,'23',1)
        put(2,2*i,'03',sig[i-1]); put(3,2*i,'03',sig[i-1]); put(4,2*i+1,'03',sig[i-1])
    a14=order(list(range(1,n+1)),o14a)     # piece 1: row 2n+2, zone 2 i=2..n-1, zone 3 last even row
    put(0,2*n+2,'03',1); put(1,2*n+2,'14',a14[0]); put(2,2*n+2,'34',2); put(3,2*n+2,'13',1)
    put(0,2*n+3,'04',1)
    for j in (1,2,3): put(j,2*n+3,'24',1)
    s23=order(list(range(2,n+1)),o23)
    for i in range(1,n):
        r=2*n+2+2*i
        if i==1: put(0,r,'02',2); put(1,r,'02',2)
        else: put(0,r,'03',i); put(1,r,'14',a14[i-1])
        put(2,r,'34',i+2); put(3,r,'23',s23[i-1])
        put(0,r+1,'12',i+1)
        for j in (1,2,3): put(j,r+1,'24',i+1)
    b14=order(list(range(1,n+1)),o14b); s13=order(list(range(2,n+1)),o13)
    p12=order(list(range(1,n+1)),o12p)
    for i in range(1,n):
        r=4*n+2*i
        if i<n-1: put(0,r,'02',i+2); put(1,r,'02',i+2)
        else: put(0,r,'03',n); put(1,r,'14',a14[n-1])
        put(2,r,'12',p12[i-1]); put(3,r,'14',b14[i-1])
        put(0,r+1,'04',i+1); put(1,r+1,'01',i+1)
        put(2,r+1,'02',i+2 if i<n-1 else 2); put(3,r+1,'13',s13[i-1])
    put(0,6*n,'14',z); put(1,6*n,'14',z); put(2,6*n,'12',p12[n-1]); put(3,6*n,'14',b14[n-1])
    assert None not in w, [i for i,x in enumerate(w) if x is None][:5]
    return w
if __name__=='__main__' and len(sys.argv)>1 and sys.argv[1]=='scan':
    good=[]; tot=0
    for opt in itertools.product((0,1),'fle',(0,1),(0,1),(0,1),(0,1),(0,1),(0,1)):
        tot+=1; res=[]
        for n in (2,3,4):
            try: res.append(len(check(build(n,opt),6*n)))
            except AssertionError as e: res.append(-1)
        if all(r==0 for r in res): good.append(opt)
    print(tot,'option sets,',len(good),'valid'); print(good[:8])
