#!/usr/bin/env python3
"""seglp_odd.py: the segment LP of PROOF_second_upper_odd.md, Section 4 (works for any census file).
Input: a census file printed by `COLT=a,b redrev PAR 2 0000 M M` (lines 'COLT count col|col|...').
Kinds = move multisets of a column; windows = W consecutive kinds (env W, default 2). For each strongly connected part of the
window graph: variables = segments (deep histories of coordinates: state-chained, each piece once, order rule) and window
frequencies; constraints: circulation, move counts, starts <= n+1 (n+2 for state 13), conservation +-3, repeat inequality
(m+1)/2 and reverse (m-6)/2 [OPT letters L = reverse, C = conservation, P = long-window parity]. Prints max m for n = NN (env).
EXACT=1: rationalizes the dual and checks it exactly; prints the bound m <= slope*n + const valid for every n (weak duality).
NOPASS='move1,move2;...': forbid these consecutive move pairs in segments.
usage: EXACT=1 NN=1000 W=10 python3 seglp_odd.py colt16_odd.out LC"""
import sys, itertools, re, os
from scipy.optimize import linprog
kinds={}; trans=set(); wins=set(); OPT=sys.argv[2] if len(sys.argv)>2 else 'LC'
for l in open(sys.argv[1]):
    if not l.startswith('COLT'): continue
    p=l.split(None,2); cols=[c.strip() for c in p[2].strip().split('|')]
    ks=[tuple(sorted(m.lstrip('*') for m in c.split())) for c in cols]
    for k in ks: kinds[k]=kinds.get(k,0)+int(p[1])
    for a,b in zip(ks,ks[1:]): trans.add((a,b))
    W=int(os.environ.get('W','2'))
    for i in range(len(ks)-W+1): wins.add(tuple(ks[i:i+W]))
K=sorted(kinds,key=lambda k:-kinds[k]); idx={k:i for i,k in enumerate(K)}
def pm(m):
    a,rest=m.split('-'); ps,b=rest.split('>'); return (a,tuple(int(c) for c in ps),b,m)
moves=sorted({m for k in K for m in k})
M={m:pm(m) for m in moves}
print(len(K),'kinds,',len(trans),'transitions,',len(moves),'moves')
# SCCs of the transition graph
adj={i:set() for i in range(len(K))}
for a,b in trans: adj[idx[a]].add(idx[b])
def reach(i):
    seen={i}; st=[i]
    while st:
        u=st.pop()
        for v in adj[u]:
            if v not in seen: seen.add(v); st.append(v)
    return seen
R={i:reach(i) for i in adj}
sccs=[]
for i in adj:
    c=frozenset(j for j in adj if j in R[i] and i in R[j])
    if c not in sccs and any(j in adj[i] for j in c): sccs.append(c)
def ok_after(prev_moves,m):
    a,ps,b,_=M[m]
    used=[p for x in prev_moves for p in M[x][1]]
    if set(ps)&set(used): return False
    for q in ps:
        if q+1 in used: return False      # later letter in piece q, earlier in q+1: order rule
    return True
def segments(avail):
    out=[]
    def ext(seg):
        out.append(tuple(seg)); st=M[seg[-1]][2]
        for m in avail:
            if M[m][0]==st and ok_after(seg,m): ext(seg+[m])
    for m in avail: ext([m])
    return out
for c in sccs:
    ks=sorted(c); avail=sorted({m for i in ks for m in K[i]})
    segs=segments(avail)
    if os.environ.get('NOPASS'):
        ST=os.environ['NOPASS']
        bad=[tuple(x.split(',')) for x in ST.split(';')]   # pairs 'move1,move2' forbidden as consecutive moves
        segs=[sg for sg in segs if not any((sg[i],sg[i+1]) in bad for i in range(len(sg)-1))]
    states=sorted({M[m][0] for m in avail}|{M[m][2] for m in avail})
    E=[tuple(idx[x] for x in w) for w in wins if all(idx[x] in c for x in w)]
    nS=len(segs); nE=len(E); nv=nS+nE; Wn=len(E[0])   # variables: segments, edge freqs; column count m = sum of edge freqs
    A_eq=[];b_eq=[];A_ub=[];b_ub=[];lab=[]; NN=float(os.environ.get('NN','100'))
    for i in ks:   # circulation
        pass
    nodes=sorted({e[1:] for e in E}|{e[:-1] for e in E})
    for nd in nodes:
        row=[0]*nS+[int(e[1:]==nd)-int(e[:-1]==nd) for e in E]; A_ub.append(row); b_ub.append(1); A_ub.append([-v for v in row]); b_ub.append(1)
    for m in avail:  # move counts: uses of move m = sum over kinds containing m of kind frequency (= out-edge freq)
        row=[sum(x==m for x in s) for s in segs]+[-K[e[-1]].count(m) for e in E]
        A_ub.append(row); b_ub.append(Wn-1); A_ub.append([-v for v in row]); b_ub.append(0)
    for X in states:
        A_ub.append([int(M[s[0]][0]==X) for s in segs]+[0]*nE); b_ub.append(NN+(2 if X=='13' else 1)); lab.append('start '+X)
    for j in range(4):   # repeat inequality R_j <= ceil(m/2): coordinates with letters in pieces j and j+1, both deep
        A_ub.append([int(any(j in M[x][1] for x in s) and any(j+1 in M[x][1] for x in s)) for s in segs]+[-0.5]*nE); b_ub.append(Wn/2.0); lab.append('R%d'%j)
        if 'L' in OPT: A_ub.append([-int(any(j in M[x][1] for x in s) and any(j+1 in M[x][1] for x in s)) for s in segs]+[0.5]*nE); b_ub.append(-(Wn-7)/2.0); lab.append('R%d>='%j)
    if 'C' in OPT:
        for X in states:
            row=[int(M[s[-1]][2]==X)-int(M[s[0]][0]==X) for s in segs]+[0]*nE
            A_ub.append(row); b_ub.append(3); A_ub.append([-v for v in row]); b_ub.append(3)

    r=linprog([0]*nS+[-1]*nE,A_ub=A_ub,b_ub=b_ub,A_eq=A_eq or None,b_eq=b_eq or None,bounds=[(0,None)]*nv,method='highs')
    if os.environ.get('EXACT') and r.status==0:
        from fractions import Fraction as F
        assert not A_eq, 'equalities present'
        nb=len(b_ub); N0=NN
        # b_ub as affine function of NN: entries equal to NN+c are the start rows
        b1=[1 if lab_i.startswith('start') else 0 for lab_i in labs] if False else None
        y=[F(-v).limit_denominator(10**6) if -v>1e-12 else F(0) for v in r.ineqlin.marginals]
        cvec=[0]*nS+[1]*nE
        ok=True; worst=None
        for col in range(nv):
            t=sum(y[i]*A_ub[i][col] for i in range(nb) if A_ub[i][col]!=0 and y[i]!=0)
            if t<cvec[col]: ok=False; worst=(col,t,cvec[col]); break
        # affine bound: b_ub at NN plus dependence: start rows are NN+1 or NN+2
        bconst=[F(b).limit_denominator(10**6) for b in b_ub]
        isstart=[1 if (abs(b_ub[i]-(NN+1))<1e-9 or abs(b_ub[i]-(NN+2))<1e-9) else 0 for i in range(nb)]
        slope=sum(y[i]*isstart[i] for i in range(nb)); const=sum(y[i]*(bconst[i]-NN*isstart[i]) for i in range(nb))
        print('   EXACT dual check:', 'VALID' if ok else 'FAILS at %s'%(worst,), ' bound: sum(edges) <=', slope,'* n +', const, ' => m <= %s n + %s'%(slope, const+Wn-1), '(%.4f n + %.4f)'%(float(slope),float(const+Wn-1)))
    print('SCC kinds',[f'K{i}' for i in ks],'segments',nS,'->', 'status',r.status, 'max m =',round(-r.fun+Wn-1,4) if r.status==0 else None)
    if r.status==0:
        print('   binding starts:',[(l,round(-y,3)) for l,y in zip(lab,r.ineqlin.marginals) if abs(y)>1e-9])
        for i in ks: print('   K%d'%i,' '.join(K[i]))
        for sg,v in zip(segs,r.x[:nS]):
            if v>1e-9: print('     seg %.3f  %s'%(v,'  '.join(sg)))
        for e,v in zip(E,r.x[nS:]):
            if v>1e-9: print('     win '+'>'.join('K%d'%x for x in e)+' %.3f'%v)
