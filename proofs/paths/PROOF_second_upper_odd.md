# The second step for ODD K: P((5K+1)/3, K-1) <= 4K + 11n/5 + 41.7   (computer-assisted; independently re-checked)

Setting and notation as in PROOF_second_upper.md (the even case), now with K = 6n+1 odd, d = (5K+1)/3 = 10n+2, k = K-1, a
path of length 4K+E with E <= K-1, the five points P_j(s) = v_{jK+s}, windows W_j(s), states (minority pairs), moves
'state-pieces>state' and columns. Lower bound: the family pfam4.py has E = 2n+3 (length (13K+8)/3).

**Theorem.** Let n >= 3 (K >= 19) and E <= K-1. Then E <= 11n/5 + 41.7 (i.e. E <= (22n+417)/10). If the deep columns are of 'phase A' (below; the family
pfam4.py is), then E <= 2n + 9.
**Corollary.** For n >= 11: P((5K+1)/3, K-1) <= 4K + 11n/5 + 41.7 (if a path had E >= K, its prefix with tail K-1 would violate
the theorem, since 6n > 11n/5 + 41.7 for n >= 11). So 4K + 2n + 3 <= P <= 4K + 2.2n + 41.7, i.e. P = 4K + cK + O(1) with
1/3 <= c <= 11/30 (for even K the growth rate is known exactly: 13K/3 + O(1), PROOF_second_upper.md).

## 1. What changes for odd K

Plotkin on the five points has budget 6d - (6K + 4(K-1)) = 6: pairs at odd index gap (K, 3K) need distance >= K, pairs at
even gap (2K, 4K) need >= K-1, so up to three 'units' of defect (an excess of 2 on a non-adjacent pair, or a singleton
coordinate; an empty-type coordinate costs all three). The state occupancies at every shift are the type counts of the re-cut
path; solving the ten distance equations per configuration (counts_odd.py) gives every pair-state count in [n-2, n+1], except
state 13: [n-1, n+2]. The reduced model is the same program with PAR = 1: `redrev 1 2 0000 M M` (its argument CC = 2 = 6d - 10K; the four even-gap
pairs need only K-1, which gives the budget 6 above).

## 2. Census (finite computation)

`COLT=3,M-4 redrev 1 2 0000 M M` for M = 9, 10, 12, 14, 16 (M = 16: 54,643,322 solutions, 229,833,615 nodes, a few minutes;
for M >= 14 the census keys need the larger buffers of redrev_bigkey.c). Columns 3..M-4 show the SAME ten kinds every time:

    phase A:   K0: 03-23>02  12-4>03  13-0>24  23-1>04          K1: 02-4>13  04-3>12  14-0>23  24-12>14
    phase B, block A:  12-0>34 23-34>24 24-12>14  |  01-4>23 02-01>12 14-3>02 34-2>01
             block B:  12-0>34 23-34>24 24-1>03 34-2>01  |  01-4>23 02-01>12 03-23>02
             excursion X (four columns): 02-01>12 12-4>03 14-3>02 34-2>01 | 03-234>13 12-0>34 23-1>04 |
                                         01-4>23 04-3>12 13-012>14 | 14-0>23 23-34>24 24-1>03 34-2>01
(seglp_odd.py prints the kinds as K0..K9 in order of frequency: K0, K1 = phase A; K3 K5 = block A; K4 K2 = block B;
K8 K6 K7 K9 = the excursion, for the M = 16 file.) The adjacent-column transitions form two strongly connected parts with no edge between them: phase A (K0, K1 alternate) and
phase B (blocks A and B freely mixed, X entered from an A-block and left into a B-block). By the Re-cut Lemma (M = 9 suffices)
the deep columns 3..E-4 (m = E-6 of them) of any path are all of phase A or all of phase B.
Independent check: a separately written enumerator (by a separate AI run, from the written definitions; not included)
reproduces the solution counts of `redrev 1 2 0000 M M` for M = 1..10 (809, 36060, 93607, 182100, 162180, 603477, 474354,
1834576, 1260224, 4827992) and the complete M = 9 census.

## 3. Phase A: E <= 2n + 9

Two rules: a coordinate has at most one letter in each piece (two letters of one piece are < K apart), and the ORDER RULE: a
piece-j letter of a coordinate is in a column <= that of its piece-(j+1) letter (else the two are < K apart).
Every K0 column contains the move 03-23>02, by distinct coordinates (one piece-2 letter each). The only phase-A move INTO state
03 is 12-4>03 (a tail letter), and a coordinate that made 12-4>03 at column a cannot make 03-23>02 at a column a' > a: its
piece-3 letter (position 3K+a') and its tail letter (4K+a) would be K+a-a' < K apart. So each deep 03-23>02 mover has made no
earlier deep move: it is in state 03 at shift 3. Hence #K0 <= n+1, m <= 2n+3 and E = m+6 <= 2n+9.

## 4. Phase B: E <= 11n/5 + 41.7 by an LP certificate

SEGMENT LP (seglp_odd.py). In a deep phase, the deep history of each coordinate is a 'segment': a state-chained sequence of
census moves in increasing columns, each piece used at most once, with the order rule between any earlier and later move.
Variables: the number of coordinates following each segment (36 segments in phase B) and the frequency of each window of
W = 10 consecutive kinds that occurs in the M = 16 census (colt16_odd.out). Constraints, each valid for every path:
 * the deep word is a walk, so the window frequencies form a circulation up to +-1 per node;
 * each move is used by the segments exactly as often as it occurs in the deep columns (window count, up to W-1);
 * segments starting in state X <= the occupancy of X at shift 3 (<= n+1; n+2 for 13);
 * (segments ending in X) - (segments starting in X) = change of the occupancy of X, in [-3, 3];
 * repeat inequality for pieces j, j+1 (PROOF_second_upper.md Section 3): segments using pieces j and j+1 <= (m+1)/2;
 * and the reverse, >= (m-6)/2: Plotkin on P_0(s), .., P_j(s), P_{j+1}(t), .., P_4(t) (s = 3, t = E-3) - the other nine pairs
   need >= 9K-4 in total, the sum of all ten distances is <= 6d = 10K+2, and d(P_j(s), P_{j+1}(t)) = K + (t-s) - 2R_j.
CERTIFICATE: the LP dual (HiGHS), rationalized, is checked in exact arithmetic (`EXACT=1 NN=1000 W=10 python3 seglp_odd.py
colt16_odd.out LC`): y >= 0 and A^T y >= c hold exactly; the right-hand side is affine in n, so weak duality gives
m <= 11n/5 + 357/10 for every n, i.e. E <= 11n/5 + 41.7. (For phase A the same LP gives m <= 2n + 8.) W = 10 windows of deep
columns exist when E >= 16 and K-1 >= 16.

Why 11/5 and not 2. The LP optimum inserts an excursion every ~W columns. In every census window an excursion has only
A-blocks before it and only B-blocks after it, and no window (up to 20 columns in a model restricted to deep kinds) contains two
excursions. Forbidding in the LP the two 'pass-throughs' at state 23 - (Q) a coordinate arriving by 01-4>23 and later leaving by
23-1>04, (T) arriving by 14-0>23 and later leaving by 23-34>24, both in deep columns - gives m <= 2n + 21 (exact certificate too).
In the model restricted to deep kinds (every column one of the ten kinds; M <= 20) such pass-throughs occur only at lags >= M-3
next to an excursion cut by the window edge, so in a real path every one of them is longer than 16 columns; bounding the number of these long links is the open step.

## 5. Status
Computer-assisted: census (one program, cross-checked by an independent enumerator for M <= 10) + an exactly verified LP
certificate. Checked by a separate AI referee run, which found and fixed an invalid row in an earlier version of the LP (the
bound survived). Not formalized.
