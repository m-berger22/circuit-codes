#!/usr/bin/env python3
# S179 pfam4.py [NMAX] : the ODD-K second-step family: a spread-k path of length 4K + (K+8)/3 = (13K+8)/3 in Q_d,
#   K = 6n+1, k = K-1, d = (5K+1)/3 = 10n+2, n >= 2   [odd l = 2n+3, k = 3l-9; length = line + l - 3 = 3k+4l-5].
# (n = 1: K = 7, P(12,6) = 33 = (13K+8)/3 by SAT, the family's template does not apply.)  Same formula as pfam3.py (even K = 6n+4).
# Checked by the definition for n = 2..14; hand proof PROOF_family_second_odd.md (all n >= 2; case tables generated and certified by
# program). EXACT at K = 7 (P(12,6) = 33) and K = 13 (P(22,12) = 59: length 60 is UNSAT in all 287 type configurations, typed SAT, program not included).
# Structure: the cut vertices v_jK have d(v_0,v_4K) = d(v_K,v_3K) = d(v_2K,v_4K) = K+1, d(v_0,v_2K) = K-1, all other distances K
# [config x = {(0,4),(1,3),(2,4)}: excess 2 over the forced minima K-1 of these three pairs]; types 14, 34 have n+1 coordinates, the other eight pair types n. Columns: see pfam4_raw.py build(n, OPT):
#   head rows 0, 1; n blocks (rows 2i, 2i+1) with SHIFTED triples X_i at (P0,2i), (P1,2i+1), (P2,2i+1), X_1 = 02_1, X_i = 13_i,
#   and 03 at (P2,2i), (P3,2i), (tail,2i+1); rows 2n+2, 2n+3; zone 2 (n-1 row pairs, 24-triples at odd rows); zone 3 (n-1 row
#   pairs); last row 14_z 14_z 12 14.  Tail = 02_1, 01_1, then (04_n | 12, 03)..., 2n+3 letters.
import sys
from pfam4_raw import build
from chk import check
OPT=(1,'f',1,0,0,1,0,0)
def fam(n): return build(n,OPT)
if __name__=='__main__':
    NMAX=int(sys.argv[1]) if len(sys.argv)>1 else 10
    for n in range(2,NMAX+1):
        w=fam(n); K=6*n+1
        assert len(w)==(13*K+8)//3 and len(set(w))==10*n+2
        print(f'n {n} d {10*n+2} k {K-1} L {len(w)} violations {len(check(w,K-1))}',flush=True)
