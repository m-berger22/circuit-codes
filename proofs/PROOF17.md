# PROOF17 (S173, 2026-11-11): the gap criterion, Byrnes' sequence for all k >= l-1, and exact values beyond k_max

Everything in this file is MACHINE-CHECKED (Lean 4 + Mathlib, lean/: GapCriterion.lean, CountP.lean,
Fam10Count/Word.lean, Fam10.lean, Byrnes.lean, Lines.lean, Contraction.lean, Conj42.lean, SymRun.lean, SymRun2.lean, Lemma3.lean, Blocks.lean, Line7.lean, Gap.lean, KmaxTable.lean, Fam6*.lean; axioms: Lean's three standard ones). The text below is the
human-readable version of what the Lean files prove. Notation: K = k+1, l = 2n-3k-1, T_x = coordinate flipped at position x.

## 1. The gap criterion (Lean: `isCoilWord_of_gaps`)

Let T be a word and g a function on positions with
 (G1) T(x + g(x)) = T(x);  (G2) T(x+d) != T(x) for 0 < d < g(x)   [so s(x) = x+g(x) is the next occurrence of T(x)];
 (G3) g >= K;  (G4) g(x) + g(sx) + g(ssx) >= N/2;  (G5) every orbit of s closes after 2 or 4 steps: the gaps sum to N.
For a window W = [t, t+L) call a position x of W COUNTED if sx is in W and ssx is not. If for all t and K <= L <= N/2

        2 #{counted x in W} <= L - k,                                                                  (*)

then T is the transition word of a spread-k circuit code of length N.

Proof. Peel W from the left: adding the position x in front of a window changes the number odd(.) of coordinates with an
odd count by -1 if T(x) occurs an odd number of times in the rest, and by +1 otherwise. Hence
   odd(W) = L - 2 #{x in W : T(x) occurs an odd number of times in W after x}.
By (G2), (G4) and L <= N/2 the coordinate T(x) occurs at most twice after x inside W (at sx and ssx), so 'odd' means: sx in W,
ssx not in W. So (*) gives odd(W) >= k for K <= L <= N/2. Windows of length <= K have distinct coordinates (G2, G3); (G5) gives
even usage per period; a window and its complement have the same odd coordinates. QED
[This is P - T of PROOF16 sec. 3 with x = start of the chord. In these START coordinates a chord from x of length K + e(x)
lies in W = [t, t+K+y) iff x + e(x) < t + y: the excluded chords are those too close to the RIGHT end of the window.]

## 2. Theorem 36/36' again (Lean: `Fam10.count_le`, `K_family10`): one proof for all i >= 0

Family 10 (PROOF16 sec. 2), p = 4a+9: F residues = the even r <= p-3 and r = p-2; excess e = g-K: 0 at p-3 and c = (p-5)/2,
u+c at p-2, u-c at p-5, u/2 at the other even residues (E), and K+u at dots (never counted). Triples: only from p-3 (two-gap
sum 2K) and p-5 (2K+u-c).
 (a) y <= u+c: a counted x has even residue <= p-3 (p-2 needs e = u+c <= y-1). No two such positions are adjacent: <= ceil(y/2).
 (b) y = K - m, 0 <= m <= K-u-c: the window [t, t+y) splits, from the right end, into zones of lengths u/2 | (u-c)-u/2 = pi+2 |
     2c = p-5 | the rest, in which the counted positions have residues in {c, p-3} | even <= p-3 except p-5 | even <= p-3 | F.
     For m = 0 the four zone counts add up (full periods + windows of length 4, 5, 2 and 2a+4) to at most (K+1)/2 - 1 + [F(t)]
     (`Zlem`, `Blem`; this is D(t) = [..] - 1 of PROOF16). For m > 0 compare with the K-window with the same right end: it has
     m more positions at its left end, all F positions of which are counted, and F has no two adjacent non-members: >= floor(m/2),
     and >= ceil(m/2) if its first position is F.
 (c) y = K + d, 1 <= d <= u: the last K positions form a K-window (same right end); in the first d positions the residue p-3
     is not counted (its triple is inside), and F \ {p-3} has no two adjacent members: <= ceil(d/2), and <= floor(d/2) if position
     t+d is F (then t+d-1 is not in F \ {p-3}).
In (b), (c) the parities work out because K is odd. There is no separate case i = 0. QED

## 3. Byrnes' sequence is a circuit code for ALL k >= l-1 (Lean: `byrnes_lower`)

**Theorem 37.** Let l >= 2, k >= l-1, k+l odd, n = (3k+l+1)/2. The sequence of Byrnes (arXiv 2008.04839, eq. (8)),
        (w1 w2A w2B)^2,   w1 = 1, 2, .., k+l;   w2A = 2, 4, .., 2(l-1);   w2B = g_1, 2l, g_2, 2l+2, .., g_m, k+l-1
(g_i = k+l+i, m = (k-l+1)/2), is the transition sequence of a spread-k circuit code of length 4k+2l in Q_n.
[Byrnes states S(d,k,k+l) = 4k+2l for k >= 2l+1 (k odd) / k >= 2l-2 (k even); the lower-bound proof is in his 2019 paper,
which I have not seen. The proof below is mine and needs only k >= l-1.]

Proof. Half period H = 2k+l, a := k+l, w := a+l-1, positions 0..H-1 (0-based). Gap function (period H):
   w1: even position: H (a coordinate used twice, 'dot');  odd r <= 2l-3: a-(r+1)/2 (to position a+(r-1)/2 of w2A);
       odd r >= 2l-1: K (to w2B);     w2A: position a+j: K+j (to position 2j+1 of the next half);
   w2B: position w+q: q even: H (dot); q odd: a-1 = k+l-1.
(G1)-(G5) are immediate (every F coordinate has gaps g, H-g, g, H-g with K <= g <= k+l-1; two-gap sums are H).
No triple fits into a window of length <= H, so x is counted in W = [t, t+K+y), y <= k+l-1, iff x is an F position of
J = [t, t+y) and x + e(x) < t+y, with the excess e = g-K:
   w1 odd r <= 2l-3: e = l-2-(r-1)/2;   w1 odd r >= 2l-1: e = 0;   w2A position a+j: e = j;   w2B F positions: e = l-2.
The F positions alternate with dots except for the RUN w2A (l-1 consecutive F positions, preceded and followed by a dot).
Let s = t mod H.
 (T) J contains no counted run position (s >= w, or s+y <= a): the counted positions are pairwise non-adjacent: <= ceil(y/2).
 (alpha) s <= a < s+y. Map a counted x to psi(x) = x (x in w1), psi(x) = x + e(x) (x in w2A or w2B). All images lie in J, are
     congruent to a mod 2, and psi is injective (increasing); positions of the next half are never counted (their excess is too
     large for y <= k+l-1). So the count is at most the number of z in J with z = a mod 2, which is <= ceil(y/2).
 (beta) a < s < w (J starts inside the run), sigma := s-a. Counted positions: run positions x = s+i (mark x+e = s+2i+sigma),
     F positions of w2B (mark = x+l-2, same parity), and early odd positions H+2j+1 of the next half (marks Z+j, consecutive,
     Z := H-s+l-1 as an offset in J). Map: run position s+i -> i; w2B position with offset i -> (i+l-2-sigma)/2; next-half
     position 2j+1 -> (Z-sigma)/2 + j. This is injective, and every image is < (y+1)/2 because y <= k+l-1. QED
(Checked in exact conventions before formalizing: byr.py (all pairs, l <= 9, k <= 3l+5), byrplan.py.)

## 4. Consequences (Lean: `K_beyond`, `exact_l0..l3`, `kmax_exact_l1`, `line_l1`)

**Corollary 38.** K(n,k) = 4k+2l whenever the Main Theorem (PROOF.md) applies: l >= 2 and
[k even, 2k > l^2-1, k > 3l-3] or [k odd, 2k > (l-2)(l+1)]. With Theorems 7-9: K(n,k) = 4k+2l for every k beyond the
thresholds of the k_max table (l = 0 mod 4: l >= 8; l = 3 mod 4: l >= 7, with sec. 7 for l = 7).  [Conjecture 4.2 itself reads S(d,k,k+l) = K(d,k); with Byrnes' Theorem 1.3 (S = 4k+2l) it predicts K = 4k+2l; sec. 6.]
**Corollary 39.** For l = 1 (mod 4), l >= 9 and every even k >= (l^2-1)/2:  K(n,k) = 4k+2l+2 if k = (l^2-1)/2, else 4k+2l.

## 5. Contraction and "Conjecture 4.2 fails on every line" (Lean: `contraction_fin`, `excess2_lines`, `conj42_fails`)

**Lemma (Deimer 1984, set version).** If a spread-k code of length N in Q_n uses each coordinate of a set C, |C| = j < k,
exactly twice (N >= 2k+2), then deleting these coordinates and their 2j steps gives a spread-(k-j) code of length N-2j in Q_(n-j).
Proof (as formalized). A window W' of the new word with L' steps is a window W of the old word with L = L' + a + 2b steps, where
a (b, z) = number of coordinates of C occurring once (twice, not at all) in W, a+b+z = j; odd(W') = odd(W) - a. Suppose
odd(W') < k-j. Then odd(W) < k, so odd(W) = min(L, N-L). If it is L: odd(W') = L' + 2b <= L' forces b = 0 and odd(W') = L',
which is the smaller arc since L' < k-j. If it is N-L: odd(W') = (N-2j-L') + 2z, and odd(W') <= N-2j-L' (complement window)
forces z = 0 and odd(W') = N-2j-L', again the smaller arc. QED

**Theorem 40.** For c >= 2 and 0 <= j <= 3 there is a spread-k circuit code of length 4k+2l+2 on the line l = 4c+1+j at
k = 8c^2+4c-j (family 10 with i = 0 has dots; contract j of them). Hence for EVERY l >= 6 there is k >= 2l+1 with
K(n,k) > 4k+2l (l = 6, 7, 8: the codes (23,13,66), (28,16,80), (33,19,96)). With S = 4k+2l (Byrnes' Theorem 1.3; sec. 6:
formal except at l = 7): Conjecture 4.2 fails on every line l >= 6; and by Corollary 38 K = 4k+2l beyond ~l^2/2.

## 6. Byrnes' upper bound for symmetric codes, and the conjecture itself (Lean: `symRun_le`, `conj42_region`, `conj42_false`)

Conjecture 4.2 reads S(d,k,k+l) = K(d,k), S = maximum length of a SYMMETRIC (d,k) code with a bit run of length >= k+l.
**Theorem 41 (Byrnes; here in the range of Lemma 2).** 2n = 3k+l+1, k >= 2, l >= 1, k > 3l-3 (k even) / k > 3l-7 (k odd).
A symmetric spread-k code in Q_n whose transition word has k+l consecutive distinct transitions has length N <= 4k+2l.
Proof (Byrnes' argument, 1809.08428 Lemma 3.5-3.6 and 2008.04839 Lemma 2.1, 2.3, Cor. 2.4, with window counts; H = N/2,
bit run at positions 0..k+l-1). (i) The window W1 = [0, 2k+l+1) has every coordinate at most twice, n1 + 2 n2 = 2k+l+1,
n1 = odd(W1) >= k, n1 + n2 <= n, so 2n >= n1 + 2k+l+1 >= 3k+l+1 = 2n: odd(W1) = k and every coordinate occurs in W1.
(ii) H >= 2k+l+2: odd([0, 2k+l+2)) = k+1, so alpha = T(2k+l+1) occurs twice in W1, once in the run and once in the next k+1
positions; windows of length k+1 are bit runs, so alpha = T(k+l) and alpha = T(j) with j < l. By symmetry alpha = T(H+j), and
the window [2k+l+1, H+j] has length <= H-2k <= k+1 (N <= 5k+3 by Lemma 2; Byrnes quotes Douglas here) and contains alpha
twice: contradiction. (iii) H = 2k+l+1: odd([0,H+1)) = k+1 and T(H) = T(0), so T(0) occurs twice in [0,H), hence in
[k+l, H). The window [k+l, H+1] (length k+2) has k odd coordinates, so adding T(H+1) = T(1) gives k+1: T(1) does not
occur in [k+l, H], i.e. exactly once in [0,H). Then [2, H+1) = [0,H) with one T(1) removed has k-1 odd coordinates and
length 2k+l: contradiction. QED
**Corollary 42.** (a) In the region of Corollary 38, S(n,k,k+l) = K(n,k) = 4k+2l (the word of Theorem 37 is symmetric with
bit run k+l): Conjecture 4.2 holds there. (b) For EVERY l >= 6 there is k >= 2l+1 with S(n,k,k+l) = 4k+2l < K(n,k):
Conjecture 4.2 fails there. (l = 7: (28,16), with Theorem 41' of sec. 8 instead of Theorem 41.)

**Corollary 43 (unbounded gap).** At every point of family 6 x m (Theorem 18) and of family 10 (Theorem 36) the hypotheses
of Theorem 41 hold (k >= 2l+1 and the Lemma-2 condition), so S(n,k,k+l) = 4k+2l there while K(n,k) = 4k+2l+4m resp.
4k+2l+4i+2: inside the range of Conjecture 4.2, K - S is unbounded. (Lean: `conj42_gap_family6`, `conj42_gap_family10`,
`conj42_gap_unbounded`.)

## 7. Theorem 9 at l = 7 (Lean: `no_xi9_four`, `thm9_seven`, `K_34_20`, `exact_l7`)

Step 2' of Theorem 9 (PROOF2 sec. 9) was formal for a = (l+1)/2 >= 6 only; the proof uses a >= 6 in one place, the exclusion of
'bipolar' configurations (two disjoint windows of length a or a+1, each carrying half of the total mass 4a). For a = 4 the gap
lemma (each gap <= 4) leaves four geometries on Z_16: windows of length 4 with gaps 4, 4, and windows of length 5 with gaps
(2,4), (3,3), (4,2). In each of them two or three of the gap zeros have no admissible option whatever the mass distribution is
(zeros 4, 6 / 12, 14 / 5, 7, 14 / 5, 7 when the first window starts at 0; found by bip4.py, proved by omega).
Hence K(34,20) = 94 and K(n,k) = 4k+14 for every even k >= 20 on the line l = 7: Theorem 9 holds for all l = 3 (mod 4), l >= 7.

## 8. Lemma 3 and the symmetric bound without Lemma 2 (Lean: `no_long6`, `length_le_seven`, `symRun_le2`)

**Lemma 3.** If N >= 7k+6 then 21k + 12 + 9 (k mod 2) <= 12 n. With 2n = 3k+l+1: a spread-k circuit code with k >= 2l (k even)
or k >= 2l-3 (k odd) has N <= 7k+5.   [Lemma 2: N <= 5k+3, but only for k > 3l-3 / 3l-7.]
Proof. Take six consecutive blocks of length K = k+1 (total 6K <= N-k). A coordinate occurs at most once per block; let
pi in {0,1}^6 be its pattern. For every pi:  |pi| + #{windows of m >= 2 consecutive blocks with an odd number of ones} <= 12
(15 windows; 64 patterns, checked one by one; equality e.g. for 111111). Summing over the coordinates:
6K + sum over the 15 windows of delta(window) <= 12 n, and delta >= k, with delta = (length) mod 2: delta >= k+1 for m odd, and
delta >= k + (k mod 2) for m even. The sum of these lower bounds is 15k + 6 + 9 (k mod 2). QED
(Found by linear programming over the block patterns: lp5.py; with 4 or 5 blocks the LP is feasible at (28,16).)

**Theorem 41'.** Let 2n = 3k+l+1, k >= l+1, k > 3l-7, and k >= 2l (k even) or k >= 2l-3 (k odd). A symmetric spread-k code in
Q_n with a bit run of length k+l has N <= 4k+2l.
Proof. By sec. 6 (ii)-(iii) the length is <= 4k+2l or >= 6k+6 (no hypothesis on k, l needed: `symRun_gap`), and <= 7k+5 by
Lemma 3. Let 6k+6 <= N <= 7k+5, A = the bit run, Omega = the rest of the half period, r = |Omega| in [2k+3-l, 4k+2], and call
a coordinate NEW if it is not in A (there are n-(k+l) = (k-l+1)/2 >= 1 of them).
(a) [Byrnes' Lemma 2.3] The k+1 transitions Omega[k..2k] are old: by induction on i = 1..k+1 for alpha_i = Omega[k-1+i],
    delta(A, Omega[0..k-1+i]) = k (i odd), k+1 (i even) and delta(Omega[0..k-1+i]) = k+1 (i odd), k (i even), and alpha_i is in A
    (each step: the odd count cannot drop below k, alpha_{i+1} is not among the k transitions before it, and every coordinate
    occurs in A u Omega[0..k]). Hence a new coordinate occurs exactly once in Omega[0..k-1] and not in Omega[k..2k]; by
    reversal, exactly once in the last k positions of Omega and not in the k+1 positions before them.
(b) A new coordinate occurs an odd number of times in Omega: delta(half) + delta(Omega) <= 2n - (k+l) = 2k+1 with equality iff
    all new coordinates are odd in Omega; both are >= k and their sum is odd.
(c) r >= 2k: Omega is covered by its first k, the next k+1, the k+1 before the last k, and the last k positions, so a new
    coordinate occurs exactly twice: contradiction with (b). r <= 2k-1: by (a), (b) every new coordinate occurs exactly once, in
    the overlap of the first and the last k positions (2k-r positions): (k-l+1)/2 <= 2k-r <= l-3, i.e. k <= 3l-7. QED
(This closes l = 7: at (28,16) every symmetric code with bit run 23 has length <= 78 < 80 <= K(28,16).)

## 9. The block lemma for any number of blocks (Lean: `blocks_bound`, `length_le_blocks`)

**Theorem 44.** Let j >= 1 and N >= j(k+1) + k. Then   j(k+1) + (j(j+1)/2 - j) k  <=  floor((j+1)/2) floor((j+2)/2) n.
Proof. Cut a window of length jK (K = k+1) into j blocks with boundaries 0, 1, .., j. For a coordinate c let v_a(c) be the
parity of its count in the first a blocks. The window between the boundaries a < b contains c an odd number of times iff
v_a(c) != v_b(c). So the sum of delta over all j(j+1)/2 windows equals the sum over the coordinates of
#{a < b : v_a != v_b} = (#zeros)(#ones) of the sequence v_0..v_j, which is at most floor((j+1)^2/4). On the other hand
delta = K for the j single blocks (bit runs) and delta >= k for the other windows (length between 2K and N-k). QED
**Corollary 45.** 2n = 3k+l+1, s >= 1 and (s+1)(l+1) < (s-1)k + 4  =>  N <= (2s+1)k + 2s - 1.  (j = 2s.)
So for every (n,k) with n <= 2k-1 (i.e. k >= l+2) K(n,k) is at most (2s+1)k + 2s - 1 with s = floor((k+l-3)/(k-l-1)) + 1.
s = 2: k > 3l-1, N <= 5k+3 (Lemma 2 has k > 3l-3 / 3l-7 thanks to the parity of delta); s = 3: k > 2l, N <= 7k+5 (Lemma 3).
(Found from the LP certificate of Lemma 3, whose multipliers were all equal. Checked against Byrnes' record table (224
entries) and 158 code files: no violation; tight for s = 1. PRIOR ART NOT CHECKED: Singleton 1966, Douglas 1969, Deimer 1984.)

NO HUMAN HAS READ THIS; but every statement above is kernel-checked (see lean/FORMAL.md items 18-32).

**Remark (S174): Theorem 44 is the PLOTKIN bound.** The j+1 vertices of the code at the block boundaries 0, K, 2K, .., jK
are pairwise at Hamming distance >= k (adjacent ones K), and v_a(c) is just coordinate c of the a-th of them (relative to the
first). 'Sum of pairwise distances of M = j+1 binary words <= n floor(M^2/4)' is exactly Plotkin's count. So the lemma should
be described as 'Plotkin's argument applied to equally spaced code vertices', NOT as a new counting idea; what is specific to
circuit codes is the extra +1 on adjacent pairs and the parity of delta (Lemma 2/3). General form: any m vertices of the
circuit pairwise >= k apart along the circuit form a binary code of minimum distance >= k, so K(n,k) <= k A(n,k) + k - 1
(and with even spacings, distance >= k+1 for odd k). For n >= 2k this is weak (n=17, k=7: 295 vs record 102); for n < 2k
Plotkin is tight for A(n,d), so table values of A(n,d) give nothing beyond Theorem 44. A bound of this shape is very likely in
Singleton 1966 / Douglas 1969 (unread).
