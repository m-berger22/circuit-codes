#!/usr/bin/env python3
# S179 pfam3.py [NMAX] : the SECOND-STEP family: a spread-k path of length 4K + (K+8)/3 = (13K+8)/3 in Q_d,
#   K = 6n+4, k = K-1, d = (5K+1)/3 = 10n+7, n >= 1   [even l = 2n+4, k = 3l-9; length = line + l - 3 = 3k+4l-5 = (13d+9)/5].
# EXACT for n = 1, 2: P(17,9) = 46 (SAT), P(27,15) = 72 (SAT restricted by the type reduction of PROOF_threshold.md: one more edge is
# UNSAT in all 11 type configurations of the first window; computer-assisted, program not included).
# Conjecture: P(d,k) = (13K+8)/3 for every n.  Checked by the definition for n = 1..14 (this script).
# Structure: window 0 is a near-simplex with d(v_0, v_4K) = K+2 (all other distances between the v_jK are K); coordinates (type, i),
# types 01 02 03 04 14 24 34 with n+1 coordinates, types 12 13 23 with n. Word = P0 P1 P2 P3 + tail of 2n+4 letters, by COLUMNS
# (offset e in each piece; z = n+1):
#   e = 0:      14_1 | 23_1 | 03_z | 04_z | tail 02_1
#   e = 1:      02_1 | 02_1 | 02_1 | 03_z | tail 01_1
#   e = 2i   (1<=i<=n): 14_{i+1} | 23_{i+1} (i<n), 01_1 (i=n) | 03_i | 04_i | tail 04_z (i=1), 12_{i-1} (i>=2)
#   e = 2i+1 (1<=i<=n): 13_i | 13_i | 13_i | 03_i | tail 03_i
#   e = 2n+2:   12_1 | 14_1 | 34_1 | 23_1 | tail 12_n
#   e = 2n+3:   03_1 | 24_1 | 24_1 | 24_1 | tail 03_z
#   e = 2n+2+2i (1<=i<=n): 04_i | 14_{i+1} | 34_{i+1} | 14_{i+1}
#   e = 2n+3+2i (1<=i<=n): 03_{i+1} (i<n), 02_2 (i=n) | 24_{i+1} | 24_{i+1} | 24_{i+1}
#   e = 4n+2+2i (1<=i<=n): 12_{i+1} (i<n), 04_z (i=n) | 02_{i+1} | 12_i | Q_{2i-2}
#   e = 4n+3+2i (1<=i<=n): 02_{i+2} (i<n), 03_z (i=n) | 01_{i+1} | 02_{i+1} | Q_{2i-1}
#   with Q = 14_1, 13_n, then (13_{n-q}, 23_{q+1}) for q = 1..n-1.
import sys
from pfam3_raw import build
from chk import check
def fam(n): return build(n,(0,0,0,1,0,1,0))
if __name__=='__main__':
    NMAX=int(sys.argv[1]) if len(sys.argv)>1 else 14
    for n in range(1,NMAX+1):
        w=fam(n); K=6*n+4
        assert len(w)==4*K+2*n+4 and len(set(w))==10*n+7
        print(f'n {n} d {10*n+7} k {K-1} L {len(w)} violations {len(check(w,K-1))}',flush=True)
