#!/usr/bin/env python3
"""type counts for ODD K = 6n+1 (d = 10n+2, budget 6 = 3 units: each unit = an excess +2 on a non-adjacent pair or a singleton coordinate).
Prints the range of each pair-type count over all configurations with integral nonnegative solution."""
import itertools, sys
from fractions import Fraction
import numpy as np
n=int(sys.argv[1]) if len(sys.argv)>1 else 4; K=6*n+1
pairs=list(itertools.combinations(range(5),2))
A=np.array([[1 if ((i in T)!=(j in T)) else 0 for T in pairs] for (i,j) in pairs],dtype=float)
Ainv=np.linalg.inv(A)
nonadj=[p for p in pairs if p[1]-p[0]>=2]
units=[('X',p) for p in nonadj]+[('S',i) for i in range(5)]
lo={T:10**9 for T in pairs}; hi={T:-1 for T in pairs}; cnt=0; ex={}
for combo in itertools.combinations_with_replacement(units,3):
    D=np.array([K if (p[1]-p[0])%2==1 else K-1 for p in pairs],dtype=float)
    for kind,v in combo:
        if kind=='X': D[pairs.index(v)]+=2
        else:
            for q,p in enumerate(pairs):
                if v in p: D[q]-=1
    x=Ainv@D
    if np.allclose(x,np.round(x)) and (x>-1e-9).all():
        cnt+=1
        tot=int(round(x.sum()))+sum(1 for k,v in combo if k=='S')
        assert tot==10*n+2,(tot,combo)
        for T,v in zip(pairs,x):
            v=int(round(v)); lo[T]=min(lo[T],v); hi[T]=max(hi[T],v)
            if T==(2,3): ex.setdefault(v,combo)
print('n',n,'K',K,'integral configurations',cnt)
print({''.join(map(str,T)):(lo[T]-n,hi[T]-n) for T in pairs},'(min-n, max-n)')
print('examples for #23:',ex)
