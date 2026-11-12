# Spread-k paths near d = 3k/2:  P(d,k) <= 6(d-k) - 5  up to d ~ 5k/3   (S177, 2026-11-12)

Status (S178): MACHINE-CHECKED in Lean 4 (../lean/Ccformal/Path.lean: `four_piece`, `path_bound_odd`, `twelve_windows`, `path_bound_even`,
`path_length_bound`); the text below is the hand proof it was formalized from (written S177, every step machine-tested, section 6).
In Lean, (i) also covers k = 1, and (ii) is `path_bound_even` for d >= 3k/2+2; the case d = 3k/2+1 of (ii) follows from the
stronger `path_bound_douglas_even` (2k+3 <= 3k+1).  The scripts and data files named below are not included in the repository.
Prior art: Douglas 1969, remark (8), gives the values for d <= 3k/2 + 1 without proof; Singleton 1966 and Wyner 1971 not accessed.

Notation: spread-k path v_0..v_L in Q_d, transition word T[0..L), window [s,e), odd[s,e) = d_H(v_s,v_e), K = k+1,
l = 2d-3k-1 (so 6(d-k)-5 = 3k+3l-2), P(d,k) = max L.

## 1. Statement

THEOREM. Let k >= 2.
 (i)  k odd  and (4k+3)/3 <= d <= (5k+4)/3   [in terms of l: k >= 3-3l and k >= 3l-5]:   P(d,k) <= 6(d-k) - 5.
 (ii) k even and  3k/2+1  <= d <= (5k+3)/3   [in terms of l: l >= 1    and k >= 3l-3]:   P(d,k) <= 6(d-k) - 5.

Per line (the bound is 3k+3l-2):
   l = 2: all odd k >= 3.   l = 3: even k >= 6.   l = 4: odd k >= 7.   l = 5: even k >= 12.   l = 6: odd k >= 13.
   l = 7: even k >= 18.     general l >= 2: k >= 3l-5 (l even), k >= 3l-3 (l odd).
(For l <= 1, in the range of the Theorem, the bound is true but weak: Douglas' values 2d-k (+1) are smaller, except (4,2) and (5,3) where both give 7.)

## 2. Facts

(F1) A window W of length w >= k has odd(W) >= k, and odd(W) = w (mod 2); so odd(W) >= k+1 if w, k have different parity.
(F2) T[i] != T[i+j] for 1 <= j <= k; a window of length <= K contains each coordinate at most once.
(F3) Subwords of path words are path words.
Proofs. (F1): if odd(W) < k then odd(W) = w >= k by the path property, a contradiction; odd(W) = w (mod 2) because the
occurrence counts sum to w. (F2): a window of length j <= k-1 has odd <= j < k, hence odd = j: all letters distinct; a window
of length k has odd >= k = its length; a window of length k+1 has odd >= k and odd = k+1 (mod 2), so odd = k+1; in each case
no letter occurs twice. (F3) is immediate from the definition. (Lean: `IsPathWord.ge`, `.gt`, `.cnt_le_one`, `.mono`.)

## 3. Four-Piece Lemma

X_1..X_4 consecutive windows (possibly empty), each of length <= K, total length u; W_ij = X_i u..u X_j (i < j: six windows).
For a coordinate with membership pattern a in {0,1}^4, s = |a|, f(a) = number of the six windows containing it an odd number
of times, sigma(a) = 6 - s - f(a) >= 0:

    pattern  0000 | 1000 0001 | 0100 0010 | 1100 0110 0011 | 1010 0101 1001 | s = 3 | 1111
    f          0  |   3    3  |   5    5  |   2    2    2  |   4    4    4  |   3   |   2
    sigma      6  |   2    2  |   0    0  |   2    2    2  |   0    0    0  |   0   |   0

Hence   sum_{i<j} odd(W_ij) = 6d - u - sum_c sigma(a(c)) <= 6d - u.                                              (*)
TIGHT patterns (sigma = 0): 0100, 0010, 1010, 0101, 1001, and every pattern with s >= 3.

(This is the path analogue of the 'local Lemma 2' of the circuit proof; it was read off the dual of the full window LP,
lpfull.py: six windows with weight 1/6, every position 1/6, the dimension constraint 1.)

## 4. Proof of (i)  (k odd, K even)

Suppose L >= 6(d-k)-4 =: u. By (F3) take a path word of length exactly u; u is even and 2K <= u <= 4K by hypothesis.
Choose even x_1, x_4 with 0 <= x_1, x_4 <= K and x_1 + x_4 = u - 2K (possible: u - 2K is even and <= 2K, K is even), and
x_2 = x_3 = K. The six windows have lengths x_1+K, 2K, K+x_4, x_1+2K, 2K+x_4, u: all even and >= K > k. By (F1) each has
odd >= k+1 = K. With (*):   6K <= 6d - u = 6k + 4 = 6K - 2.   Contradiction. QED

## 5. Proof of (ii)  (k even, K odd)

Suppose L >= 6(d-k)-4 =: L0; take a path word T of length exactly L0 (even; 3k+2 <= L0 <= 4k+2 by hypothesis), and write L = L0,
so 6d - L = 6k+4.  Put a = k, b = 2k+1, c = 3k+1, r = L - 3k - 2 (0 <= r <= k).

Cut A of [0,L-1): [0,a), [a,b), [b,c), [c,L-1), lengths k, k+1, k, r (all <= K).
   Windows [0,b), [0,c), [0,L-1), [a,c), [a,L-1): lengths 2k+1, 3k+1, L-1, 2k+1, L-1-k: odd and >= k, so odd-count >= k+1.
   Window [b,L-1): length L-2k-2 = k+r, even, >= k: odd-count >= k.
   Sum >= 6k+5; by (*) sum <= 6d - (L-1) = 6k+5. Equality:   (A1) all A-patterns tight;   (A2) odd[b,L-1) = k.
Cut B of [1,L): [1,a+1), [a+1,b), [b,c+1), [c+1,L), lengths k, k, k+1, r.
   Windows [b,L), [a+1,L), [1,L), [a+1,c+1), [1,c+1): lengths L-2k-1, L-k-1, L-1, 2k+1, 3k+1: odd, >= k. Window [1,b): 2k, even.
   Same count:   (B2) odd[1,b) = k.
Let x = T[b-1] = T[2k].
 (1) [1,b-1) has odd length 2k-1 >= k: odd-count >= k+1 = odd[1,b) + 1, so removing the last letter x of [1,b) raises the
     odd-count: x occurs an even number of times in [1,b), hence also at some q in [1,b-1); (F2): q <= b-1-K = k-1 < a.
     So x has A-pattern 11**.
 (2) (A1): tight patterns 11** are 1110, 1101, 1111: x occurs in [b,L-1).
 (3) [b-1,L-1) has odd length k+r+1 >= k: odd-count >= k+1 = odd[b,L-1) + 1, so x occurs an even number of times in [b,L-1):
     at least twice by (2).
 (4) (F2): occurrences of x after 2k are at positions >= 2k+K = c, so they lie in [c,L-1), a window of length r <= K, which
     contains x at most once. Contradiction. QED

Equivalent linear form (this is what the LP found; cert12.py checks it for every admissible occurrence set S, k <= 22):
   over the 12 odd-length windows  [0,b) [0,c) [0,L-1) [a,c) [a,L-1) [b,L) [a+1,L) [1,L) [a+1,c+1) [1,c+1) [1,b-1) [b-1,L-1):
       #{W : |S n W| odd}  <=  12 - 2|S| + [0 in S] + [L-1 in S],
   so  12(k+1) <= sum_W odd(W) <= 12d - 2L + 2,  i.e.  L <= 6(d-k) - 5  for every even L in [3k+2, 4k+2].

## 6. Tests (all 0 failures; scripts in this directory)

 * verify.py: (F2), identity (*) on 3.4 million random four-cuts of sub-windows of real path words of ALL lengths >= X
   (12 exhaustive word sets, 6 SAT words; verify.out); mechanism of steps (1), (3) on 4.0 million windows (C3);
   equality statements (every admissible cut of every window of length 6(d-k)-5 resp. 6(d-k)-6 is tight: C4, C5);
   no word longer than the bound in range (C6).
 * verify2.py: C4/C5 on ALL maximal words of (4,2), (6,3), (9,5), (12,7), (15,9), (11,6), (14,8), (13,7) [1100 words] and on
   the fam2 families k = 3..30.
 * cert12.py: the two linear certificates for every admissible occurrence set (k even <= 22: 393,338 sets; k odd <= 23: 663,117).
 * check_data.py: all 50 known values (ptable.out SAT, own exhaustive DFS dfs.out, the exceptional values): 34 points lie in the
   theorem's range, none exceeds the bound, 24 attain it; all 7 points with P > 6(d-k)-5 (for (11,5), (14,7) only lower bounds are known) ((7,5), (6,4), (7,3), (9,4), (12,6),
   (11,5), (14,7)) are outside the range.
 * lpfull.py (full window-parity LP: one variable per admissible occurrence set, all windows): infeasible at L = 3k+3l-1
   exactly in the theorem's range among all 31 tested (k,l) (l = 2..6), feasible at every tested point below the thresholds
   (lpscan1.out, lpsub.out).

## 7. What is NOT proved (honest list)

 1. LOWER BOUNDS: SOLVED in S178. One explicit family (pfam.py) attains 3k+3l-2 for every l >= 2 and every k >= 2l-5 (l even)
    / 2l-6 (l odd); proofs: PROOF_family_even.md (even l; Lean: PathFamEven.lean), PROOF_family_odd.md (odd l).
    Hence P(d,k) = 3k+3l-2 exactly in the whole range of the Theorem.
 2. THRESHOLDS k0(l) (the first k from which P = 3k+3l-2 holds on line l). Proved: k0(l) <= 3l-5 (l even), <= 3l-3 (l odd)
    as far as the UPPER bound is concerned. Truth from data:
       l = 2: k0 = 3 (all k).   l = 3: k0 = 2 (all k; k = 2, 4 by DFS only).
       l = 4: k0 = 5  (k = 3: P = 21 > 19; k = 5: P = 25 by SAT; theorem from 7).  Threshold NOT sharp.
       l = 5: k0 = 8  (k = 4: 28 > 25, k = 6: 33 > 31; k = 8, 10 by SAT; theorem from 12).  NOT sharp.
       l = 6: k0 = 13 = 3l-5: SHARP. New SAT paths: (17,9) length 44 > 43 and (20,11) length 50 > 49
              (words/sat_17_9_44.txt, sat_20_11_50.txt), plus (11,5) >= 39, (14,7) >= 43 (computed tables).
       S178 SAT values: P(17,9) = 46, P(20,11) = 50, P(23,13) = 55 (line);  l = 7: P(22,12) >= 58 > 55, P(25,14) = 61 and
       P(28,16) = 67 (line holds although k < 18).
    So k0(l) is not a simple function of the window LP: at (10,5), (15,8), (18,10) the bound holds although the full
    window LP is feasible (integrality is needed there; only SAT proves them), while at (20,11) -- the same position
    k = 3l-7 as (10,5) -- the bound FAILS. No formula for k0(l) is claimed.
 3. Below the thresholds the method gives only the weak LP bounds of lpsub.out ((8,4): <= 20 [true 19]; (10,5): <= 31 [25];
    (18,10): <= 44 [43]); these are floating-point LP results, not written proofs.
 4. A K-independent finite reduction for the case k = 3l-7 (reduce.py: boundary letters + bulk blocks, MILP) is FEASIBLE,
    i.e. inconclusive -- consistent with item 2 (the statement is false at K = 12).
 5. Equality structure (what an extremal word must look like): in every admissible cut every coordinate has a tight pattern
    (in particular every coordinate occurs in every such window; no pattern 1000/0001/1100/0110/0011) and all six windows meet
    (F1) with equality. For u = 4K, d = 5K/3 this forces exactly K/6 coordinates of each of the 10 tight patterns
    (check_data.py rank computation; seen in all 1140 windows of the 570 maximal (10,5) words, pat105.py). Usage profiles of
    extremal words (usage.py): every coordinate used 1..4 times, never unused. Not turned into a classification.
