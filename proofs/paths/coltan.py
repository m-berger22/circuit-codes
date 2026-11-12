#!/usr/bin/env python3
"""analyse a COLT census file: column kinds (fresh flags ignored), transitions, departures from state 23 / 12.
usage: coltan.py FILE"""
import sys,re
kinds={}; trans={}; ncol=None; tot=0; nodep={}
for l in open(sys.argv[1]):
    if not l.startswith('COLT'): continue
    p=l.split(None,2); n=int(p[1]); cols=[c.strip() for c in p[2].strip().split('|')]
    ks=[' '.join(sorted(m.lstrip('*') for m in c.split())) for c in cols]; tot+=n
    for k in ks: kinds[k]=kinds.get(k,0)+n
    for a,b in zip(ks,ks[1:]): trans[(a,b)]=trans.get((a,b),0)+n
names={k:'K%d'%i for i,(k,v) in enumerate(sorted(kinds.items(),key=lambda x:-x[1]))}
dep=lambda k,st: any(m.startswith(st+'-') for m in k.split())
print('solutions',tot,'; kinds',len(kinds))
for k,v in sorted(kinds.items(),key=lambda x:-x[1]): print(f"  {names[k]:4s} {v:9d}  dep23={int(dep(k,'23'))} dep12={int(dep(k,'12'))}  {k}")
print('transitions',len(trans))
bad23=bad12=0
for (a,b),v in sorted(trans.items(),key=lambda x:-x[1]):
    f23=dep(a,'23') or dep(b,'23'); f12=dep(a,'12') or dep(b,'12')
    bad23+= (not f23)*v; bad12+=(not f12)*v
    print(f"  {names[a]:4s} > {names[b]:4s} {v:9d}"+("" if f23 else "  NO-23-DEPARTURE")+("" if f12 else "  NO-12-DEPARTURE"))
print('adjacent pairs without departure from 23:',bad23,'; from 12:',bad12)
