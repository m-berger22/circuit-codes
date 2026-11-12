#!/usr/bin/env python3
# S179 pfam2.py [TMAX] : the FIRST-EXCESS family: a spread-k path of length 4K+2 = 24t+2 in Q_d, d = 10t, K = 6t, k = K-1 (t >= 3).
# (Line l = 2t+2, k = 3l-7: one step below the range of the Four-Piece theorem; the line value is 4K+1. Upper bound 4K+2:
#  PROOF_threshold.md Theorem A. t = 2: the word below fails; (20,11,50) exists by SAT: word_20_11_50.txt.)
# Coordinates = (type, i), type = one of the ten 2-subsets of {0..4}, i = 1..t.  Vertex v_{jK} has bit (xy,i) = [j in {x,y}]
# (up to a global xor): the five vertices v_0, v_K, .., v_4K are pairwise at distance K (perfect simplex).
# Word = P0 P1 P2 P3 tail, each piece P_j given by COLUMNS e = 0..6t-1 (letter of P_j at offset e):
#   e = 0:              13_1    | 13_1     | 03_t     | 03_t        tail: 03_t
#   e = 1:              14_1    | 23_1     | 13_1     | 04_1        tail: 12_t
#   e = 2i   (1<=i<t):  13_{i+1}| 13_{i+1} | 13_{i+1} | 14_{i+1}
#   e = 2i+1 (1<=i<t):  03_i    | 23_{i+1} | 34_i     | 04_{i+1}
#   e = 2t+2n   (0<=n<t): X     | 24_{n+1} | 24_{n+1} | 24_{n+1}    X = 03_t (n = 0), 14_{n+1} (n >= 1)
#   e = 2t+2n+1 (0<=n<t): 12_{n+1} | 14_{n+1} | Y     | Z           Y = 03_1 (n=0), 34_t (n=1), 03_n (n>=2);  Z = 14_1 (n=0), 13_{n+1} (n>=1)
#   e = 4t+2n   (0<=n<t): 02_{n+1} | 02_{n+1} | 02_{n+1} | 23_{n+1}
#   e = 4t+2n+1 (0<=n<t): 04_{n+1} | 01_{n+1} | 12_{n+1} | W        W = 13_1 (n=0), 03_n (n>=1)
import sys, itertools
PAIRS=['%d%d'%p for p in itertools.combinations(range(5),2)]
def fam(t):
    K=6*t; w=[None]*(4*K+2)
    def put(j,e,ty,i): w[j*K+e]=PAIRS.index(ty)*t+(i-1)
    put(0,0,'13',1); put(1,0,'13',1); put(2,0,'03',t); put(3,0,'03',t); put(4,0,'03',t)
    put(0,1,'14',1); put(1,1,'23',1); put(2,1,'13',1); put(3,1,'04',1); put(4,1,'12',t)
    for i in range(1,t):
        for j in range(3): put(j,2*i,'13',i+1)
        put(3,2*i,'14',i+1)
        put(0,2*i+1,'03',i); put(1,2*i+1,'23',i+1); put(2,2*i+1,'34',i); put(3,2*i+1,'04',i+1)
    for n in range(t):
        e=2*t+2*n
        if n==0: put(0,e,'03',t)
        else: put(0,e,'14',n+1)
        for j in (1,2,3): put(j,e,'24',n+1)
        put(0,e+1,'12',n+1); put(1,e+1,'14',n+1)
        if n==0: put(2,e+1,'03',1); put(3,e+1,'14',1)
        else:
            if n==1: put(2,e+1,'34',t)
            else: put(2,e+1,'03',n)
            put(3,e+1,'13',n+1)
    for n in range(t):
        e=4*t+2*n
        for j in range(3): put(j,e,'02',n+1)
        put(3,e,'23',n+1)
        put(0,e+1,'04',n+1); put(1,e+1,'01',n+1); put(2,e+1,'12',n+1)
        if n==0: put(3,e+1,'13',1)
        else: put(3,e+1,'03',n)
    return w
def violations(w,k):
    vs=[0]
    for c in w: vs.append(vs[-1]^(1<<c))
    bad=0; L=len(w)
    for i in range(L+1):
        for j in range(i+1,L+1):
            dh=bin(vs[i]^vs[j]).count('1')
            if (j-i<k and dh!=j-i) or (j-i>=k and dh<k): bad+=1
    return bad
if __name__=='__main__':
    TMAX=int(sys.argv[1]) if len(sys.argv)>1 else 12
    for t in range(3,TMAX+1):
        w=fam(t); K=6*t
        assert len(w)==4*K+2 and None not in w and max(w)<10*t
        print(f't {t} d {10*t} k {K-1} L {len(w)} = 4K+2 violations {violations(w,K-1)}',flush=True)
