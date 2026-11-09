# New lower bounds for spread-k circuit codes in the hypercube

**Who made this.** These codes were found by Claude, an AI model made by Anthropic, running autonomously
on a research machine that Matt runs as a home lab. Matt approved publishing them. This work is
not peer-reviewed; the codes come with a checker precisely so that nobody has to trust us.

## What is here
A circuit code of spread k in the n-cube Q_n (Byrnes 2016, Def. 1.1) is a cycle v_0 ... v_(N-1) in Q_n such that
for all i, j:   d_H(v_i, v_j) < k  implies  d_C(i, j) = d_H(v_i, v_j),
where d_C is the distance along the cycle. Spread 2 is coil-in-the-box. K(n,k) is the maximum length. A k-snake is the
same with a path instead of a cycle (length = number of edges).

This repository improves **106 entries** of the K(n,k) lower-bound table in
K. M. Byrnes, *A new method for constructing circuit codes*, arXiv:1604.02755 (2016), Table 3
(n = 11..30, k = 3..9), and **12 entries** of the spread-k snake table in
K. J. Hood, D. Recoskie, J. Sawada, D. Wong, *Snakes, coils, and single-track circuit codes with spread k*,
J. Comb. Optim. 30 (2015). Before publishing we checked the later literature we could find (Byrnes 2018-2021 on
codes with long bit runs and isomorphism; the 2026 snake-in-the-box papers, which are spread 2 only) and found no
entry that already beats these. If we missed one, please tell us.

`records.tsv` lists every improved entry: kind, n, k, previous best, new bound, code file.
`codes/` has one file per entry: hexadecimal vertex labels, in order along the cycle (or path). Large files are gzipped.
One entry (30/3) is only the code from a smaller cube, since Q_m is a subcube of Q_n;
they are listed because they still beat the previous value.

## Updates
- **2026-11-09**: added the spread-3 entries for n = 27..30 (the first version stopped at n = 26 by mistake; Byrnes' table
  goes to n = 30), e.g. K(29,3) >= 4194270 (previous 250114). Symmetric rerouting also beat our first-version spread-4 and
  spread-5 entries for n = 26..30 (e.g. K(30,4) >= 1153860, was 154930 here, 97846 in the table), and an exhaustive class
  search improved K(25,9) and K(26,9). New entries are marked in the git history; all files pass `verify.py --all`.
  A fourth checker, `src/checkhash.c` (hash table, memory O(N)), was added for the multi-million-vertex codes.

## Checking
`python3 verify.py --all` checks every file (requires numpy 2; about an hour on one core since the multi-million-vertex spread-3 and spread-4 codes were added). `python3 verify.py FILE n k [open]`
checks one. It tests that consecutive vertices are adjacent, vertices are distinct, and the spread condition for every
pair (either all pairs directly, or a Hamming ball of radius k-1 around each vertex, whichever is cheaper). It rejects
swapped or flipped vertices and the same codes checked with spread k+1. Each code was also accepted by two other
independent checkers written earlier (an O(N^2) pair check in Python and an O(N x ball) check in C).

## Coils (circuit codes)
| n | k | previous best | new lower bound | file | note |
|---|---|---|---|---|---|
| 11 | 3 | 160 | **192** | [coil_11_3_192.txt](codes/coil_11_3_192.txt) |  |
| 15 | 3 | 1380 | **1410** | [coil_15_3_1410.txt](codes/coil_15_3_1410.txt) |  |
| 16 | 3 | 2240 | **2336** | [coil_16_3_2336.txt](codes/coil_16_3_2336.txt) |  |
| 18 | 3 | 5212 | **6876** | [coil_18_3_6876.txt](codes/coil_18_3_6876.txt) |  |
| 19 | 3 | 7818 | **12046** | [coil_19_3_12046.txt](codes/coil_19_3_12046.txt) |  |
| 20 | 3 | 10424 | **21080** | [coil_20_3_21080.txt](codes/coil_20_3_21080.txt) |  |
| 21 | 3 | 15634 | **37674** | [coil_21_3_37674.txt](codes/coil_21_3_37674.txt) |  |
| 22 | 3 | 20848 | **67364** | [coil_22_3_67364.txt.gz](codes/coil_22_3_67364.txt.gz) |  |
| 23 | 3 | 31266 | **123050** | [coil_23_3_123050.txt.gz](codes/coil_23_3_123050.txt.gz) |  |
| 24 | 3 | 41696 | **219888** | [coil_24_3_219888.txt.gz](codes/coil_24_3_219888.txt.gz) |  |
| 25 | 3 | 62530 | **392050** | [coil_25_3_392050.txt.gz](codes/coil_25_3_392050.txt.gz) |  |
| 26 | 3 | 83392 | **688428** | [coil_26_3_688428.txt.gz](codes/coil_26_3_688428.txt.gz) |  |
| 27 | 3 | 125058 | **1354050** | [coil_27_3_1354050.txt.gz](codes/coil_27_3_1354050.txt.gz) |  |
| 28 | 3 | 166784 | **2464504** | [coil_28_3_2464504.txt.gz](codes/coil_28_3_2464504.txt.gz) |  |
| 29 | 3 | 250114 | **4194270** | [coil_29_3_4194270.txt.gz](codes/coil_29_3_4194270.txt.gz) |  |
| 30 | 3 | 333568 | **4194270** | [coil_30_3_4194270.txt.gz](codes/coil_30_3_4194270.txt.gz) | same code as n=29 (Q_29 is a subcube of Q_30) |
| 11 | 4 | 70 | **72** | [coil_11_4_72.txt](codes/coil_11_4_72.txt) |  |
| 12 | 4 | 102 | **120** | [coil_12_4_120.txt](codes/coil_12_4_120.txt) |  |
| 14 | 4 | 280 | **286** | [coil_14_4_286.txt](codes/coil_14_4_286.txt) |  |
| 18 | 4 | 1530 | **1908** | [coil_18_4_1908.txt](codes/coil_18_4_1908.txt) |  |
| 19 | 4 | 2040 | **3078** | [coil_19_4_3078.txt](codes/coil_19_4_3078.txt) |  |
| 20 | 4 | 2688 | **5080** | [coil_20_4_5080.txt](codes/coil_20_4_5080.txt) |  |
| 21 | 4 | 3400 | **8274** | [coil_21_4_8274.txt](codes/coil_21_4_8274.txt) |  |
| 22 | 4 | 4488 | **13860** | [coil_22_4_13860.txt](codes/coil_22_4_13860.txt) |  |
| 23 | 4 | 5910 | **23690** | [coil_23_4_23690.txt](codes/coil_23_4_23690.txt) |  |
| 24 | 4 | 7480 | **41136** | [coil_24_4_41136.txt](codes/coil_24_4_41136.txt) |  |
| 25 | 4 | 9870 | **67196** | [coil_25_4_67196.txt.gz](codes/coil_25_4_67196.txt.gz) |  |
| 26 | 4 | 13248 | **122564** | [coil_26_4_122564.txt.gz](codes/coil_26_4_122564.txt.gz) |  |
| 27 | 4 | 20304 | **215514** | [coil_27_4_215514.txt.gz](codes/coil_27_4_215514.txt.gz) |  |
| 28 | 4 | 34704 | **376376** | [coil_28_4_376376.txt.gz](codes/coil_28_4_376376.txt.gz) |  |
| 29 | 4 | 57246 | **659518** | [coil_29_4_659518.txt.gz](codes/coil_29_4_659518.txt.gz) |  |
| 30 | 4 | 97846 | **1153860** | [coil_30_4_1153860.txt.gz](codes/coil_30_4_1153860.txt.gz) |  |
| 13 | 5 | 80 | **84** | [coil_13_5_84.txt](codes/coil_13_5_84.txt) |  |
| 14 | 5 | 106 | **128** | [coil_14_5_128.txt](codes/coil_14_5_128.txt) |  |
| 18 | 5 | 570 | **648** | [coil_18_5_648.txt](codes/coil_18_5_648.txt) |  |
| 19 | 5 | 712 | **950** | [coil_19_5_950.txt](codes/coil_19_5_950.txt) |  |
| 20 | 5 | 950 | **1480** | [coil_20_5_1480.txt](codes/coil_20_5_1480.txt) |  |
| 21 | 5 | 1140 | **2394** | [coil_21_5_2394.txt](codes/coil_21_5_2394.txt) |  |
| 22 | 5 | 1422 | **3610** | [coil_22_5_3610.txt](codes/coil_22_5_3610.txt) |  |
| 23 | 5 | 1898 | **5804** | [coil_23_5_5804.txt](codes/coil_23_5_5804.txt) |  |
| 24 | 5 | 2280 | **9428** | [coil_24_5_9428.txt](codes/coil_24_5_9428.txt) |  |
| 25 | 5 | 2846 | **15164** | [coil_25_5_15164.txt](codes/coil_25_5_15164.txt) |  |
| 26 | 5 | 3794 | **26156** | [coil_26_5_26156.txt](codes/coil_26_5_26156.txt) |  |
| 27 | 5 | 4560 | **44982** | [coil_27_5_44982.txt.gz](codes/coil_27_5_44982.txt.gz) |  |
| 28 | 5 | 5690 | **74872** | [coil_28_5_74872.txt.gz](codes/coil_28_5_74872.txt.gz) |  |
| 29 | 5 | 7586 | **124062** | [coil_29_5_124062.txt.gz](codes/coil_29_5_124062.txt.gz) |  |
| 30 | 5 | 9120 | **205500** | [coil_30_5_205500.txt.gz](codes/coil_30_5_205500.txt.gz) |  |
| 14 | 6 | 68 | **72** | [coil_14_6_72.txt](codes/coil_14_6_72.txt) |  |
| 15 | 6 | 88 | **104** | [coil_15_6_104.txt](codes/coil_15_6_104.txt) |  |
| 16 | 6 | 118 | **160** | [coil_16_6_160.txt](codes/coil_16_6_160.txt) |  |
| 17 | 6 | 204 | **224** | [coil_17_6_224.txt](codes/coil_17_6_224.txt) |  |
| 18 | 6 | 238 | **324** | [coil_18_6_324.txt](codes/coil_18_6_324.txt) |  |
| 19 | 6 | 284 | **456** | [coil_19_6_456.txt](codes/coil_19_6_456.txt) |  |
| 20 | 6 | 330 | **600** | [coil_20_6_600.txt](codes/coil_20_6_600.txt) |  |
| 21 | 6 | 436 | **882** | [coil_21_6_882.txt](codes/coil_21_6_882.txt) |  |
| 22 | 6 | 510 | **1276** | [coil_22_6_1276.txt](codes/coil_22_6_1276.txt) |  |
| 23 | 6 | 608 | **1932** | [coil_23_6_1932.txt](codes/coil_23_6_1932.txt) |  |
| 24 | 6 | 714 | **2980** | [coil_24_6_2980.txt](codes/coil_24_6_2980.txt) |  |
| 25 | 6 | 932 | **4546** | [coil_25_6_4546.txt](codes/coil_25_6_4546.txt) |  |
| 26 | 6 | 1086 | **7084** | [coil_26_6_7084.txt](codes/coil_26_6_7084.txt) |  |
| 27 | 6 | 1304 | **11076** | [coil_27_6_11076.txt](codes/coil_27_6_11076.txt) |  |
| 28 | 6 | 1530 | **16910** | [coil_28_6_16910.txt](codes/coil_28_6_16910.txt) |  |
| 29 | 6 | 1996 | **27034** | [coil_29_6_27034.txt](codes/coil_29_6_27034.txt) |  |
| 30 | 6 | 2328 | **37872** | [coil_30_6_37872.txt.gz](codes/coil_30_6_37872.txt.gz) |  |
| 16 | 7 | 76 | **84** | [coil_16_7_84.txt](codes/coil_16_7_84.txt) |  |
| 17 | 7 | 102 | **110** | [coil_17_7_110.txt](codes/coil_17_7_110.txt) |  |
| 18 | 7 | 116 | **162** | [coil_18_7_162.txt](codes/coil_18_7_162.txt) |  |
| 19 | 7 | 134 | **266** | [coil_19_7_266.txt](codes/coil_19_7_266.txt) |  |
| 20 | 7 | 152 | **360** | [coil_20_7_360.txt](codes/coil_20_7_360.txt) |  |
| 21 | 7 | 198 | **462** | [coil_21_7_462.txt](codes/coil_21_7_462.txt) |  |
| 22 | 7 | 234 | **660** | [coil_22_7_660.txt](codes/coil_22_7_660.txt) |  |
| 23 | 7 | 266 | **874** | [coil_23_7_874.txt](codes/coil_23_7_874.txt) |  |
| 24 | 7 | 310 | **1206** | [coil_24_7_1206.txt](codes/coil_24_7_1206.txt) |  |
| 25 | 7 | 390 | **1770** | [coil_25_7_1770.txt](codes/coil_25_7_1770.txt) |  |
| 26 | 7 | 466 | **2614** | [coil_26_7_2614.txt](codes/coil_26_7_2614.txt) |  |
| 27 | 7 | 532 | **3820** | [coil_27_7_3820.txt](codes/coil_27_7_3820.txt) |  |
| 28 | 7 | 618 | **5672** | [coil_28_7_5672.txt](codes/coil_28_7_5672.txt) |  |
| 29 | 7 | 774 | **8444** | [coil_29_7_8444.txt](codes/coil_29_7_8444.txt) |  |
| 30 | 7 | 930 | **10814** | [coil_30_7_10814.txt](codes/coil_30_7_10814.txt) |  |
| 16 | 8 | 46 | **52** | [coil_16_8_52.txt](codes/coil_16_8_52.txt) |  |
| 17 | 8 | 54 | **72** | [coil_17_8_72.txt](codes/coil_17_8_72.txt) |  |
| 18 | 8 | 68 | **92** | [coil_18_8_92.txt](codes/coil_18_8_92.txt) |  |
| 19 | 8 | 78 | **122** | [coil_19_8_122.txt](codes/coil_19_8_122.txt) |  |
| 20 | 8 | 86 | **180** | [coil_20_8_180.txt](codes/coil_20_8_180.txt) |  |
| 21 | 8 | 116 | **252** | [coil_21_8_252.txt](codes/coil_21_8_252.txt) |  |
| 22 | 8 | 132 | **396** | [coil_22_8_396.txt](codes/coil_22_8_396.txt) |  |
| 23 | 8 | 148 | **506** | [coil_23_8_506.txt](codes/coil_23_8_506.txt) |  |
| 24 | 8 | 168 | **624** | [coil_24_8_624.txt](codes/coil_24_8_624.txt) |  |
| 25 | 8 | 188 | **824** | [coil_25_8_824.txt](codes/coil_25_8_824.txt) |  |
| 26 | 8 | 236 | **1158** | [coil_26_8_1158.txt](codes/coil_26_8_1158.txt) |  |
| 27 | 8 | 272 | **1646** | [coil_27_8_1646.txt](codes/coil_27_8_1646.txt) |  |
| 28 | 8 | 308 | **2322** | [coil_28_8_2322.txt](codes/coil_28_8_2322.txt) |  |
| 29 | 8 | 348 | **3356** | [coil_29_8_3356.txt](codes/coil_29_8_3356.txt) |  |
| 30 | 8 | 396 | **4806** | [coil_30_8_4806.txt](codes/coil_30_8_4806.txt) |  |
| 19 | 9 | 60 | **76** | [coil_19_9_76.txt](codes/coil_19_9_76.txt) |  |
| 20 | 9 | 80 | **90** | [coil_20_9_90.txt](codes/coil_20_9_90.txt) |  |
| 21 | 9 | 88 | **136** | [coil_21_9_136.txt](codes/coil_21_9_136.txt) |  |
| 22 | 9 | 100 | **184** | [coil_22_9_184.txt](codes/coil_22_9_184.txt) |  |
| 23 | 9 | 110 | **276** | [coil_23_9_276.txt](codes/coil_23_9_276.txt) |  |
| 24 | 9 | 124 | **432** | [coil_24_9_432.txt](codes/coil_24_9_432.txt) |  |
| 25 | 9 | 160 | **550** | [coil_25_9_550.txt](codes/coil_25_9_550.txt) |  |
| 26 | 9 | 176 | **676** | [coil_26_9_676.txt](codes/coil_26_9_676.txt) |  |
| 27 | 9 | 200 | **802** | [coil_27_9_802.txt](codes/coil_27_9_802.txt) |  |
| 28 | 9 | 222 | **1104** | [coil_28_9_1104.txt](codes/coil_28_9_1104.txt) |  |
| 29 | 9 | 248 | **1534** | [coil_29_9_1534.txt](codes/coil_29_9_1534.txt) |  |
| 30 | 9 | 320 | **2202** | [coil_30_9_2202.txt](codes/coil_30_9_2202.txt) |  |

## Snakes
| n | k | previous best | new lower bound | file | note |
|---|---|---|---|---|---|
| 11 | 3 | 157 | **189** | [snake_11_3_189.txt](codes/snake_11_3_189.txt) |  |
| 15 | 3 | 1379 | **1407** | [snake_15_3_1407.txt](codes/snake_15_3_1407.txt) |  |
| 16 | 3 | 2240 | **2333** | [snake_16_3_2333.txt](codes/snake_16_3_2333.txt) |  |
| 12 | 4 | 104 | **116** | [snake_12_4_116.txt](codes/snake_12_4_116.txt) |  |
| 14 | 4 | 279 | **282** | [snake_14_4_282.txt](codes/snake_14_4_282.txt) |  |
| 14 | 5 | 112 | **123** | [snake_14_5_123.txt](codes/snake_14_5_123.txt) |  |
| 14 | 6 | 66 | **67** | [snake_14_6_67.txt](codes/snake_14_6_67.txt) |  |
| 15 | 6 | 89 | **98** | [snake_15_6_98.txt](codes/snake_15_6_98.txt) |  |
| 16 | 6 | 117 | **154** | [snake_16_6_154.txt](codes/snake_16_6_154.txt) |  |
| 17 | 6 | 200 | **218** | [snake_17_6_218.txt](codes/snake_17_6_218.txt) |  |
| 16 | 7 | 72 | **77** | [snake_16_7_77.txt](codes/snake_16_7_77.txt) |  |
| 17 | 7 | 98 | **105** | [snake_17_7_105.txt](codes/snake_17_7_105.txt) |  |

## How they were found
Three methods, all of them plain search, none clever:
1. **Windowed rerouting** (most entries with n >= 18 and k >= 4): start from the trivial cycle of length 2n, repeatedly
   cut a stretch of the cycle and look by depth-first search for a longer replacement path that keeps every spread
   constraint with the rest; accept longer (sometimes equal) paths. Minutes per case. The old entries for n >= 18 came
   from constructions, and that is where this gains most.
2. **Symmetric rerouting** (spread 3, n >= 15): the old spread-3 records are invariant under rotating the coordinates.
   Searching only among cycles with v_(i+L) = rot(v_i) XOR t, and rerouting all R images at once, gives the n = 15, 16
   and 18..30 entries; with the same method at spread 4 and 5 (R = 2n), the n = 26..28 entries (2026-11-09 update).
3. **Exhaustive search inside one symmetry class**: for an automorphism g(v) = sigma(v) XOR t of Q_n (sigma a coordinate
   permutation of a chosen cycle type), search every cycle with v_(i+L) = g(v_i) completely (with exact pruning).
   This gives the n <= 17 entries such as K(11,3) >= 192 (sigma of cycle type 6+3+2), K(12,4) >= 120 (4+4+4),
   K(14,4) >= 286 (13+1), K(17,6) >= 224 (8+8+1), and most k >= 6 entries. As sanity checks, on every (n,k) whose optimum
   is proven, no class ever exceeds the optimum and the best class reaches it in 7 of 8 cases; and with rotation symmetry
   alone the old structured records K(12,3) = 288, K(13,4) = 182, K(14,4) = 280, K(15,5) = 210 come out exactly as the
   in-class optimum.

The search programs (C) are in `src/`. They are research code, not polished.

## Not claimed
Nothing here is an upper bound or an optimality proof. Table entries in the same range that we did NOT improve
(we reproduced some, fell short on others): k=3: n=9, 10, 12, 13, 14, 17; k=4: n=9, 10, 13, 15, 16, 17;
k=5: n=12, 15, 16, 17; k=6: n=12, 13; k=7: n=14, 15; k=8: n=14, 15; k=9: n=14..18. Several of these are proven optima.

## License and contact
Everything here is CC0 (public domain). Questions or corrections: open an issue on this repository.
