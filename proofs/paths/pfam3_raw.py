#!/usr/bin/env python3
# S179 pfam3_raw.py : builder for the second-step family (pfam3.py picks the options). `python3 pfam3_raw.py scan` = the search over
# order choices that selected them. K = 6n+4, d = 10n+7, length 4K+2n+4. Types with n+1 coords: 01 02 03 04 14 24 34; n coords: 12 13 23.
import sys, itertools
from chk import check
TYPES=['01','02','03','04','12','13','14','23','24','34']
def build(n,opt):
    oS,oT,oP,ex14,o14,o13,o12=opt
    K=6*n+4; E=2*n+4; z=n+1
    cnt={t:(n if t in ('12','13','23') else n+1) for t in TYPES}
    base={}; b=0
    for t in TYPES: base[t]=b; b+=cnt[t]
    w=[None]*(4*K+E)
    def put(j,e,ty,i):
        assert 1<=i<=cnt[ty],(ty,i); assert w[j*K+e] is None,(j,e); w[j*K+e]=base[ty]+i-1
    def order(lst,o): return lst if o==0 else lst[::-1]
    sig=order(list(range(1,n+1)),oS); tau=order(list(range(1,n+1)),oT)
    put(0,0,'14',1); put(1,0,'23',1); put(2,0,'03',z); put(3,0,'04',z); put(4,0,'02',1)
    for j in range(3): put(j,1,'02',1)
    put(3,1,'03',z); put(4,1,'01',1)
    t12=order(list(range(1,n+1)),o12)
    for i in range(1,n+1):
        put(0,2*i,'14',i+1)
        if i<n: put(1,2*i,'23',i+1)
        else: put(1,2*i,'01',1)
        put(2,2*i,'03',sig[i-1]); put(3,2*i,'04',tau[i-1])
        if i==1: put(4,2,'04',z)
        else: put(4,2*i,'12',t12[i-2])
        for j in range(3): put(j,2*i+1,'13',i)
        put(3,2*i+1,'03',sig[i-1]); put(4,2*i+1,'03',sig[i-1])
    put(0,2*n+2,'12',1); put(1,2*n+2,'14',1); put(2,2*n+2,'34',1); put(3,2*n+2,'23',1); put(4,2*n+2,'12',t12[n-1])
    put(0,2*n+3,'03',1)
    for j in (1,2,3): put(j,2*n+3,'24',1)
    put(4,2*n+3,'03',z)
    p1=order(list(range(2,n+2)),oP)
    L14=[i for i in range(1,n+2) if i!=ex14]; L14=order(L14,o14)
    for i in range(1,n+1):
        r=2*n+2+2*i
        put(0,r,'04',i); put(1,r,'14',p1[i-1]); put(2,r,'34',i+1); put(3,r,'14',L14[i-1])
        put(0,r+1,'03',i+1) if i<n else put(0,r+1,'02',2)
        for j in (1,2,3): put(j,r+1,'24',i+1)
    s13=order(list(range(1,n+1)),o13)
    p3=[('14',ex14),('13',s13[0])]
    for q in range(1,n): p3 += [('13',s13[q]),('23',q+1)]
    for i in range(1,n+1):
        r=4*n+2+2*i
        if i<n: put(0,r,'12',i+1)
        else: put(0,r,'04',z)
        put(1,r,'02',i+1); put(2,r,'12',i)
        if i<n: put(0,r+1,'02',i+2)
        else: put(0,r+1,'03',z)
        put(1,r+1,'01',i+1); put(2,r+1,'02',i+1)
    for q,(ty,i) in enumerate(p3): put(3,4*n+4+q,ty,i)
    assert None not in w
    return w
if __name__=='__main__' and len(sys.argv)>1 and sys.argv[1]=='scan':
    good=[]
    for opt in itertools.product((0,1),(0,1),(0,1),('1','z','2'),(0,1),(0,1),(0,1)):
        res=[]
        for n in (2,3,4):
            o=list(opt); o[3]={'1':1,'z':n+1,'2':2}[opt[3]]
            try: res.append(len(check(build(n,tuple(o)),6*n+3)))
            except AssertionError as e: res.append(-1)
        if all(r==0 for r in res): good.append(opt)
        elif sum(res)<20: print('near',opt,res)
    print(len(good),'valid option sets'); print(good[:12])
