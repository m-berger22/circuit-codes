# What is machine-checked (Lean 4.35 + Mathlib; S172-S174, 2026-11-11)

Every statement below is a Lean theorem in Ccformal/ whose proof the Lean kernel has checked; the only axioms are
Lean's standard three (propext, Classical.choice, Quot.sound). No `sorry`, no `native_decide`.
Check: `lake build` in this folder (Values/ takes hours; everything else < 5 min), `#print axioms` at the end of each file.

HEADLINES (item numbers below; K(n,k) = maximum length of a spread-k circuit code in Q_n, l = 2n−3k−1, S(n,k,r) = maximum
length of a SYMMETRIC one with a bit run of length ≥ r; Byrnes' Conjecture 4.2: S(n,k,k+l) = K(n,k) for k ≥ 2l+1 / 2l−2):
 A. K(n,k) ≤ 4k+2l as soon as 2k > l²−1 (k even, and k > 3l−3) or 2k > (l−2)(l+1) (k odd).                              [3]
 B. Byrnes' sequence is a code of length 4k+2l for all k ≥ l−1, so K(n,k) = S(n,k,k+l) = 4k+2l in the region of A:
    the conjecture is TRUE there.                                                                                    [20, 25]
 C. The exact threshold: k_max(l) = (l²−1)/2 for every l ≡ 1 (mod 4), l ≥ 9; upper bounds (l²−l−6)/2 (l ≡ 0, 3) and
    (l²−l−4)/2 (l ≡ 2) for all l; K = 4k+2l beyond the threshold on every line; the table k_max(l) is complete
    for l = 6..31.                                                    [16, 19, 21, 28, 30]
 D. The conjecture is FALSE: for EVERY l ≥ 6 there is k ≥ 2l+1 with S(n,k,k+l) = 4k+2l < K(n,k);
    and K − S is unbounded.                                                                                  [23, 26, 27, 29, 31]
 D'. S(n,k,k+l) = 4k+2l for ALL k ≥ l−1, so the conjecture holds at (n,k) exactly when K(n,k) = 4k+2l.             [33]
 E. Two infinite two-parameter families of exact values above Byrnes' formula: K = 4k+2l+4i+2 (odd lines) and
    K = 4k+2l+4m (even lines); 94 further exact values by a verified checker.                                        [19, 24, 5]
 F. Tools: the chord inequality (Lemma 1), Lemma 2, Lemma 3 and the block lemma for any number of blocks (an explicit
    upper bound for K(n,k) whenever n ≤ 2k−1), the gap criterion, Deimer's contraction.                      [1, 2, 31, 32, 18, 22]

DEFINITION (Basic.lean `IsCoil k N v`). v : ℕ → (Fin n → Bool) with v(i+N) = v(i), d_H(v(i), v(i+1)) = 1 for all i, and for all i and
0 ≤ L < N:  d_H(v(i), v(i+L)) < k  ⇒  d_H(v(i), v(i+L)) = min(L, N−L).   "K(n,k) = N" is `IsMaxLength n k N`: such a v exists for N,
and every N' admitting one is ≤ N.     Notation: K = k+1, l = 2n−3k−1.

1. `chord_inequality` (Lemma 1).  N < 6K, max(k, N/4) ≤ L ≤ min(2K, N−k):  (N−2n)(4L−N) ≤ 2N⌊(L−k)/2⌋.
2. `no_long` (Lemma 2).  N ≥ 5k+4  ⇒  k + (k mod 2) + 12K ≤ 6n + 6⌊(k+2)/2⌋.
3. `coil_length_bound` (MAIN THEOREM).  l ≥ 2; k even, 2k > l²−1, k > 3l−3, or k odd, 2k > (l−2)(l+1):  N ≤ 4k+2l.
4. `counterexample_23_13`, `K_23_13`.  A spread-13 code of length 66 in Q_23 exists, and K(23,13) = 66  (Byrnes' Conj. 4.2 says 64).
5. `Values/K_n_k` (94 pairs, values.list).  K(n,k) = N exactly, e.g. K(33,19) = 96, K(98,59) = 280, K(208,130) = 576,
   K(700,450) = 1904, K(1071,701) = 2882: the code is checked by a verified checker (`check_sound`), the upper bound is Lemma 1 + 2.
6. `equality_case`.  If Lemma 1 is an equality at L: exactly N/2−n coordinates are used four times (F), every window of length L
   contains exactly ⌊(L−k)/2⌋ repeated coordinates, every F coordinate occurs in every such window, no other coordinate twice.
7. `thm7`, `thm7_bound` (Theorem 7).  l = 4q, k = (l²−l−2)/2: no code of length 4k+2l+2; for q ≥ 2: N ≤ 4k+2l.
8. `thm33a` (first half of Theorem 33; contains Thms 15, 17, 24, Cor 25).  k odd, N = 4K+2u, 2n+ρ = 3K+u, 2ρK = u(u+ρ) (equality
   in Lemma 1 at L = 2K), 2 ≤ u < K:  if K/gcd(K,u) is even there is no code.   `cor25`: ρ odd ⇒ no code.   `thm15`: l = 8q+6,
   k = (l²+2l−4)/4: no code of length l(l+4).   `parity_obstruction` (Theorem 24): gcd(2K,N) | K and N/gcd(2K,N) odd ⇒ no code.
9. `odd_line_condition`, `thm26` (Theorem 26; contains Thm 16).  k even, equality in Lemma 1 at L = 2k+1, 3K ≤ N < min(6K, 8K−4):
   4n−N is an EVEN multiple of N/gcd(2k+1, N); in particular no code if N ≡ 2 (mod 4).
10. `l3_zero_slack`, `l3_bound`.  l = 4j+3, k = (l²−1)/2: no code of length 4k+2l+2; for j ≥ 1: N ≤ 4k+2l.
11. `propU_even`, `propU_odd` (Proposition U).  At every equality point (k odd: 2ρK = u(u+ρ), 3u < K+3ρ, u+ρ ≤ K+1; k even:
    2ρK = u²+u+uρ+2ρ, 3u+4 < K+3ρ, u+ρ+2 ≤ K) every code has N ≤ 4K+2u.
12. `thm8`, `thm8_bound` (Theorem 8).  l = 4c+3 ≥ 7, k = (l²−1)/2 − 2j, 1 ≤ j ≤ c: no code of length 4k+2l+2, and N ≤ 4k+2l.
    (`typeWord_of_coil` + `no_typeWord`: the statement about periodic binary words is proved separately.)
    With 10: for l ≡ 3 (mod 4), k_max(l) ≤ (l²−l−2)/2 is formal; the last step to (l²−l−6)/2 is Theorem 9.
13. `structure_S1`, `balanced`.  Under (H) exactly N/2−n coordinates are used four times, all others twice; the type word is balanced.
14. `thm9`, `thm9_bound` (Theorem 9).  l = 4c+3 ≥ 11, k = (l²−l−2)/2: no code of length 4k+2l+2, and N ≤ 4k+2l.
    So with 10 and 12: for l ≡ 3 (mod 4), l ≥ 11: every code with k > (l²−l−6)/2 has N ≤ 4k+2l, i.e. k_max(l) ≤ (l²−l−6)/2.
    ALL upper bounds of the k_max table (STATUS.md) are now machine-checked: l ≡ 1: item 3; l ≡ 0: item 7; l ≡ 3: items 10, 12, 14;
    l ≡ 2: item 3.
15. `kmax_8`, `kmax_9`, `kmax_11`, `kmax_12`, `kmax_13`, `kmax_15` (complete lines).  For l = 8, 9, 11, 12, 13, 15 and
    k* = 25, 40, 52, 63, 84, 102:  K(n,k*) = 4k*+2l+2 exactly, and K(n,k) ≤ 4k+2l for every k > k* on the line (n = (3k+l+1)/2).
    E.g. l = 11:  K(84,52) = 232, and K((3k+12)/2, k) ≤ 4k+22 for all even k ≥ 54.  So Byrnes' Conjecture 4.2 fails at k* and
    its upper-bound half holds beyond it -- with no informal step.
16. `kmax_upper_l0`, `kmax_upper_l3`, `kmax_upper_l1`, `kmax_upper_l2` (the k_max table for ALL lines, upper bounds).
    l = 4q ≥ 8, k odd, k > (l²−l−6)/2;   l = 4c+3 ≥ 11, k even, k > (l²−l−6)/2;   l = 4c+1, k even, k > (l²−1)/2 (and k > 3l−3);
    l = 4c+2, k odd, k > (l²−l−4)/2:   in each case every spread-k circuit code in Q_n, n = (3k+l+1)/2, has N ≤ 4k+2l.
17. `K_trivial`.  K(n,k) = 2n for k ≥ 2, k+1 ≤ n, 2n+2 ≤ 3k (classical range; lower bound = the trivial code, formal for all (n,k)).
    `isCoilWord_of_windows`: a general sufficient criterion for transition words (for future family proofs).

18. `isCoilWord_of_gaps` (the gap criterion, S173).  T a word, g a gap function with T(x+g x) = T x, no occurrence of T x strictly
    between, g ≥ k+1, three consecutive gaps ≥ N/2, every orbit closing after 2 or 4 gaps; if for all windows W = [t,t+L),
    k+1 ≤ L ≤ N/2,  2·#{x ∈ W : x+g(x) ∈ W, x+g(x)+g(x+g(x)) ∉ W} ≤ L−k,  then T is the transition word of a spread-k circuit code.
19. `K_family10` (Theorems 36 and 36', ALL parameters, both bounds).  For a, i ≥ 0, p = 4a+9, l = p+(2p−2)i,
    k = (p²−1)/2 + p(p+1)i, n = (3k+l+1)/2:   K(n,k) = 4k+2l+4i+2.     E.g. K(65,40) = 180, K(208,130) = 576, K(418,266) = 1144.
    `kmax_exact_l1`: for every l = 4c+1 ≥ 9:  K(n,k) = 4k+2l+2 at k = (l²−1)/2  -- the Main Theorem (item 3) is sharp on all
    these lines, i.e. k_max(l) = (l²−1)/2 EXACTLY, with no informal step.
20. `byrnes_lower`.  For all l ≥ 2 and k ≥ l−1 of opposite parity, n = (3k+l+1)/2: a spread-k circuit code of length 4k+2l
    exists in Q_n (the sequence of Byrnes, arXiv 2008.04839 eq. (8); his theorem is stated for k ≥ 2l+1 / 2l−2).
    `K_beyond`:  **K(n,k) = 4k+2l whenever item 3 applies** (k even: l² < 2k+1, 3l < k+3; k odd: l² < 2k+l+2), l ≥ 2.
    So K(n,k) equals the value 4k+2l that Byrnes' Conjecture 4.2 (S(d,k,k+l) = K(d,k), with his Theorem 1.3: S = 4k+2l) predicts,
    in that whole two-parameter region; below it K(n,k) > 4k+2l occurs (items 15, 19, 23).  [Audit S173, D1: the conjecture
    itself is about S; see items 25-28 for the statements about S.]
21. `exact_l0`, `exact_l1`, `exact_l2`, `exact_l3`:  K(n,k) = 4k+2l for every k beyond the thresholds of item 16 (l >= 8 for
    l = 0 mod 4, l >= 11 for l = 3 mod 4; the line l = 7 is item 28).
    `line_l1`: for l = 4c+1 ≥ 9 and EVERY even k ≥ (l²−1)/2:  K(n,k) = 4k+2l+2 if k = (l²−1)/2, and 4k+2l otherwise.

22. `contraction`, `contraction_fin` (Deimer 1984, for a set).  If a spread-k circuit code of length N in Q_n uses each coordinate
    of a set C (|C| = j < k) exactly twice and N ≥ 2k+2, deleting them gives a spread-(k−j) circuit code of length N−2j in Q_(n−j).
    (On the lines: l → l+j, k → k−j, same excess N−4k−2l.)
23. `conj42_fails`.  **For every l ≥ 6 there exist k ≥ 2l+1 and n with 2n = 3k+l+1 and a spread-k circuit code in Q_n of length
    > 4k+2l.**  (l ≥ 9: `excess2_lines`: l = 4c+1+j, 0 ≤ j ≤ 3, k = 8c²+4c−j, length 4k+2l+2; l = 6, 7, 8: (23,13,66), (28,16,80),
    (33,19,96).)   Together with item 20: K(n,k) > 4k+2l somewhere in the range k ≥ 2l+1 on every line l ≥ 6, and K(n,k) = 4k+2l
    beyond the Main Theorem's threshold (~l²/2) -- both machine-checked.  With S = 4k+2l (Byrnes' Theorem 1.3; formal in the
    range of Lemma 2, item 26) the first statement says that his Conjecture 4.2 (S = K) fails: item 27.

24. `K_family6` (Theorem 18; m = 1: Theorem 13; ALL parameters, both bounds).  For p ≡ 0 (mod 4), p ≥ 8, and m odd:
    k = m p(p+2)/4 − 1, n = m(3p−2)(p+4)/8 (so l = m(p−2)+2):   K(n,k) = m p(p+4) = 4k+2l+4m.
    E.g. K(33,19) = 96, K(68,41) = 192, K(99,59) = 288, K(115,71) = 320, K(204,125) = 576.  Excess over 4k+2l unbounded on even lines.
25. `byrnes_word`, `conj42_region`.  Byrnes' word is symmetric (T(i+N/2) = T(i)) and its first k+l transitions are distinct.
    Hence in the region of item 20:  4k+2l = K(n,k) is attained by a symmetric code with a bit run of length k+l, i.e.
    S(n,k,k+l) = K(n,k) = 4k+2l -- **Byrnes' Conjecture 4.2 itself is a machine-checked theorem in that region.**
    (Its failure at the points of items 19, 23, 24: see items 26, 27, 29, 31.)

26. `symRun_le` (Byrnes' upper bound, restated).  Let T be the transition word of a SYMMETRIC spread-k circuit code of length N
    in Q_n (T(i+N/2) = T(i)) with a bit run of length k+l, 2n = 3k+l+1, k ≥ 2, l ≥ 1, and k > 3l−3 (k even) / k > 3l−7 (k odd).
    Then N ≤ 4k+2l.   [Byrnes: for k ≥ 2l−2 / 2l+1, via Douglas' bounds; here via Lemma 2.]
    `symRun_gap`: for ALL k ≥ 2, l ≥ 1 (no relation between k and l): such a code has N ≤ 4k+2l or N ≥ 6k+6.
27. `conj42_false`.  **For EVERY l ≥ 6 there are k ≥ 2l+1 and n = (3k+l+1)/2 with: every symmetric spread-k code in Q_n
    with bit run k+l has length ≤ 4k+2l, one of length 4k+2l exists, and some spread-k code in Q_n is longer than 4k+2l.**
    I.e. S(n,k,k+l) = 4k+2l < K(n,k): Byrnes' Conjecture 4.2 is FALSE on every line l ≥ 6, with no quoted step.
    (With item 25: the conjecture is true beyond ~l²/2 and false at these points. The bound for symmetric codes is item 26
    for l ≠ 7 and item 31 at the l = 7 witness (28,16).)

28. `thm9_seven`, `K_34_20`, `exact_l7` (Theorem 9 at l = 7).  No spread-20 code of length 96 in Q_34; K(34,20) = 94; and
    K(n,k) = 4k+14 for EVERY even k ≥ 20 on the line l = 7.  With items 20, 21: K(n,k) = 4k+2l is machine-checked beyond the
    k_max thresholds on every line (l ≡ 0: k > (l²−l−6)/2, l ≥ 8; l ≡ 3: k > (l²−l−6)/2, l ≥ 7; l ≡ 1: k > (l²−1)/2; l ≡ 2: k > (l²−l−4)/2).
29. `conj42_gap_family6`, `conj42_gap_family10`, `conj42_gap_unbounded`.  At every point of family 6 × m (item 24) and of family 10
    (item 19):  S(n,k,k+l) = 4k+2l exactly, while K(n,k) = 4k+2l+4m resp. 4k+2l+4i+2.  So inside the range k ≥ 2l+1 of
    Conjecture 4.2 the difference K − S is unbounded.

30. `kmax_table`.  For every l = 6, 7, .., 31 and k* = k_max(l) =
    13, 18, 25, 40, 43, 52, 63, 84, 89, 102, 117, 144, 151, 168, 187, 220, 229, 250, 273, 312, 323, 348, 375, 420, 433, 462:
    a spread-k* circuit code longer than 4k*+2l exists in Q_n, n = (3k*+l+1)/2, and K(n,k) = 4k+2l for EVERY k > k* on the line.
    I.e. the table of k_max(l) for the first 26 lines, complete (k* = (l²−1)/2, (l²−l−6)/2, (l²−l−4)/2 for l ≡ 1; 0, 3; 2 mod 4).

31. `no_long6`, `length_le_seven` (LEMMA 3, new).  N ≥ 7k+6 ⇒ 21k+12+9(k mod 2) ≤ 12n.  Hence, with 2n = 3k+l+1: a spread-k
    circuit code with k ≥ 2l (k even) or k ≥ 2l−3 (k odd) has N ≤ 7k+5.  (Six consecutive blocks of length K: for every
    coordinate, #occurrences + #{windows of ≥ 2 consecutive blocks containing it an odd number of times} ≤ 12.)
    `symRun_le2`: a symmetric code with a bit run of length k+l (2n = 3k+l+1) has N ≤ 4k+2l whenever k > 3l−7, k ≥ l+1 and
    k ≥ 2l (k even) / k ≥ 2l−3 (k odd) -- by `symRun_gap`, Lemma 3 and Byrnes' alternation lemma (`alt`, `fwd_new`, `bwd_new`,
    `new_odd`, `IsCoilWord.rev`); no Lemma 2.

32. `blocks_bound` (the block lemma, any number of blocks).  For every j:  N ≥ j(k+1)+k  ⇒
        j(k+1) + (j(j+1)/2 − j)·k  ≤  ⌊(j+1)/2⌋⌊(j+2)/2⌋·n.
    `length_le_blocks`: 2n = 3k+l+1, s ≥ 1, (s+1)(l+1) < (s−1)k+4  ⇒  N ≤ (2s+1)k + 2s − 1.   So K(n,k) has an explicit upper
    bound for every n ≤ 2k−1 (take s > (k+l−3)/(k−l−1)); s = 2, 3 are Lemma 2 / Lemma 3 up to the parity refinements.
    `blocks_bound_odd`: for odd k (every window has δ ≥ k+1):  N ≥ j(k+1)+k ⇒ (j(j+1)/2)(k+1) ≤ ⌊(j+1)/2⌋⌊(j+2)/2⌋·n;
    j = 4 and j = 6 are exactly Lemma 2 and Lemma 3 for odd k (k ≤ 3l−7, k ≤ 2l−5).   `blocks_bound_even`: for even k the
    left side gains `oddWindows j` = number of windows of an odd number ≥ 3 of blocks (2 for j = 4, 6 for j = 6): again exactly
    Lemma 2 and Lemma 3.  So Lemmas 2 and 3 are the cases j = 4, 6 of one lemma.   (Prior art not checked.)

33. `symRun_all`, `symRun_le_all`, `symRun_exact`, `conj42_iff` (S174, NEW: SymRun3.lean, SymExact.lean).  A symmetric
    spread-k code (T(i+N/2) = T(i)) with a bit run of length a and 2n ≤ a+2k+1 has N ≤ 2a+2k.  Hence
    **S(n,k,k+l) = 4k+2l exactly for EVERY l ≥ 2 and k ≥ l−1** (2n = 3k+l+1; Byrnes proved ≤ only for k ≥ 2l−2 / 2l+1), and
    Conjecture 4.2 holds at (n,k) iff K(n,k) = 4k+2l.  Proof: two-centre count (odd coordinates of [0,p) and of [a,p) sum to
    ≤ 2n−a) forces k ≤ |odd set of [0,p)| ≤ k+1 on [a+k, N−k]; at p = H−1..H+2 with the symmetry this gives a window with only
    k−1 odd coordinates.  Supersedes items 26/31's role for S (Lemma 2, Lemma 3, alternation lemma not needed).

34. SPREAD-k PATHS (S178, NEW: Path.lean, PathDouglas.lean, PathWalk.lean, PathDouglasWord.lean; `IsPath k L v`: walk v on ℕ,
    d_H(v_i, v_{i+w}) < k ⇒ = w for i+w ≤ L; `IsMaxPath d k L`: P(d,k) = L).  Written proofs: ../paths/.
    `maxPath_low`:  P(d,k) = 2d−k for k ≤ d ≤ (3k+1)/2   and   `maxPath_douglas_even`:  P(3k/2+1, k) = 2k+3 (k even ≥ 2)
       -- together Douglas 1969, 'Further remarks' (8), which he states without proof.
    `four_piece` (Four-Piece Lemma: four consecutive pieces of length ≤ k+1; the six windows made of ≥ 2 consecutive pieces
       have odd-counts summing to ≤ 6d − total length; = Plotkin on the five piece boundaries),
    `path_bound_odd` (k odd, 8k+6 ≤ 6d ≤ 10k+8 ⇒ L ≤ 6(d−k)−5), `twelve_windows` + `path_bound_even` (k even,
       9k+7 ≤ 6d ≤ 10k+6 ⇒ L ≤ 6(d−k)−5), `path_length_bound` (vertex version: l = 2d−3k−1 ≥ 2, k ≥ 3l−5 (k odd) / 3l−3 (k even)
       ⇒ L ≤ 3k+3l−2).
    `isPathWord_of_walk`, `isPathWord_of_height` (Walk Lemma: a word is a path word if the walk w ↦ oddc T s w is at height
       ≥ k+1 before every down-step), `cnt_three`, `oddc_snoc`.
    `famEven_isPathWord` (PathFamEven*.lean, 900 lines; famT κ h = ../paths/pfam.py fam(2κ−1, 2h), checked by #eval at 4
       sizes): the even-l family A B C D is a spread-k path word of length 6κ+6h+1 = 3k+3l−2 over 3κ+h coordinates for ALL
       κ ≥ max(1, 2h) (k = 2κ−1, l = 2h+2);   **`maxPath_even_l`: P(d,k) = 6(d−k)−5 = 3k+3l−2 for k odd, l even, k ≥ 3l−5**
       (IsMaxPath (3κ+h) k (6κ+6h+1) for κ ≥ 3h+1).  Proof = Walk Lemma + Sign Table (17 rows) + block heights.
    NOT formal yet: the odd-l family (hand proof ../paths/PROOF_family_odd.md).

NOT machine-checked: the second half of Theorem 33 (u ≥ 2e), Theorem 30, and the lower bounds "the family is a code for ALL
parameters" other than families 10 and 6 × odd m (Theorems 10-12, 14, 19-22, 27-29, 31): there only the single instances in
Values/.  So k_max(l) is formal as an exact value for l ≡ 1 (mod 4) and for l = 8, 9, 11, 12, 13, 15; for the other lines only
as an upper bound.  S(n,k,k+l) = 4k+2l is formal for ALL k ≥ l−1 (item 33, S174).
