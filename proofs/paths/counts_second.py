#!/usr/bin/env python3
"""type counts for K=6n+4 (d=10n+7) per budget config: excess pair (i,j) [D_ij=K+2] or one singleton coordinate {i}."""
import itertools, numpy as np, sys
from fractions import Fraction
n=int(sys.argv[1]) if len(sys.argv)>1 else 3; K=6*n+4
pairs=list(itertools.combinations(range(5),2))
A=np.array([[1 if ((i in T)!=(j in T)) else 0 for T in pairs] for (i,j) in pairs],dtype=float)
def solve(rhs):
    x=np.linalg.solve(A,rhs); return x
for cfg in pairs:
    rhs=np.array([K+(2 if p==cfg else 0) for p in pairs],dtype=float); x=solve(rhs)
    ok=np.allclose(x,np.round(x)) and (x>=-1e-9).all()
    print("excess",cfg, "integral" if ok else "non-integral", {''.join(map(str,T)):round(v,2) for T,v in zip(pairs,x)} if ok else '')
for i in range(5):
    rhs=np.array([K-(1 if i in p else 0) for p in pairs],dtype=float); x=solve(rhs)
    ok=np.allclose(x,np.round(x)) and (x>=-1e-9).all()
    print("singleton",i, "integral" if ok else "non-integral", {''.join(map(str,T)):round(v,2) for T,v in zip(pairs,x)} if ok else '')
