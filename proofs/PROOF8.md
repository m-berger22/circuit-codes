# PROOF8 (S169, 2026-11-11 night): where the excess-4 bound is NOT attained

Notation as in PROOF.md / PROOF6.md: spread-k circuit code of length N in Q_n, l = 2n-3k-1, K = k+1, transition word T_x
(x in Z_N). A coordinate used four times is an "F coordinate", its positions are "F positions"; a coordinate used twice is a
"dot". For a position x, x+ is the next position of the same coordinate, g(x) = x+ - x >= K its gap (all gaps are >= K because
windows of length <= k have distinct coordinates). A "chord" inside a window W is a pair (x, x+) with both positions in W;
P(W) = number of chords inside W. The "type word" is the F/dot pattern of the positions.

Lemma 1 (PROOF.md) for N < 6K and max(k, N/4) <= L <= min(2K, N-k):  (N/2 - n)(4L - N) <= N floor((L-k)/2).
For N = 4k+2l+4 it gives  k <= (l^2+2l-4)/4 (l even, k odd, L = 2K)  and  k <= l(l+3)/4 (l odd, k even, L = 2K-1).
Theorems 13, 14 (PROOF6, PROOF7): for l = 0, 2, 4 (mod 8), l >= 8, the even bound is attained. Here:

## Theorem 15 (even lines, l = 6 mod 8)
Let l = 8q+6, q >= 1, k = (l^2+2l-4)/4, n = (3k+l+1)/2. There is no spread-k circuit code of length 4k+2l+4 in Q_n.
Hence K(n,k) <= 4k+2l+2. (The case q = 0, l = 6, is not covered by the proof; there K(20,11) = 58 < 60 is known by computer.)

## Theorem 16 (odd lines)
Let l = 8j+5, j >= 1, k = l(l+3)/4, n = (3k+l+1)/2 (the only case in which the odd bound holds with equality, since
l(l+3)/4 must be an even integer). There is no spread-k circuit code of length 4k+2l+4 in Q_n. Hence K(n,k) <= 4k+2l+2.
(j = 0, l = 5, is excluded because K = 11 < 2l+3; there K(18,10) = 50 < 54 is known.)

So, for even l >= 8 and odd l >= 13: a code of length 4k+2l+4 with EQUALITY in Lemma 1 (k = (l^2+2l-4)/4 resp. l(l+3)/4)
exists iff l = 0, 2 or 4 (mod 8). (Smaller lines: l = 4, 5, 6 by the known values K(10,5) = 28, K(18,10) = 50, K(20,11) = 58: none.)
(On odd lines with l != 5 mod 8 the bound l(l+3)/4 is not an even integer and the largest admissible k is not settled here.)

('Hence': in both theorems Lemma 2 gives N <= 5k+3 (k > 3l-7 for k odd, k > 3l-3 for k even), and Lemma 1 at L = 2K resp. 2K-1
excludes N = 4k+2l+e for 6 <= e <= 5k+3-4k-2l, as in PROOF6 section 1: f(4) = 0 and
f(e) - f(4) is a positive multiple of (e-4)(2k+c-3l-e) with c = 4 (even l) or c = 1 (odd l), which is positive on that range. Checked in exact
integers by struct/ex4/ex4lem8.py.)

## 0. What equality in Lemma 1 forces  (both parities)

Let N = 4k+2l+4, N < 6K, and let L0 = 2K (k odd) or L0 = 2K-1 (k even) with equality in Lemma 1 at L = L0.
Recall the proof of Lemma 1: every coordinate is used 0, 2 or 4 times; with n_2 coordinates used four times, n_2 >= N/2-n;
a window of length L <= 2K holds each coordinate at most twice, so odd(W) = L - 2P(W) and P(W) <= floor((L-k)/2); and
n_2 (4L-N) <= sum over 4-coordinates of sum_gaps (L-g)^+  <=  sum_W P(W)  <=  N floor((L-k)/2).
Equality throughout gives:

 (Z1) P(W) = floor((L0-k)/2) =: c0 for EVERY window of length L0 (c0 = K/2 for k odd, where K is even in Theorem 15;
      c0 = k/2 for k even);
 (Z2) no dot has both positions in a window of length L0 (dot gaps >= L0), and exactly N/2-n coordinates are F coordinates,
      all others dots (none unused);
 (Z3) every F gap is <= N-3K = K+2l (the other three gaps are >= K).

In both theorems K >= 2l+3 (Thm 15: K = 2l(q+1) and q >= 1, or K = 12 = 2l for q = 0, see the remark at the end of section 1;
Thm 16: K - (2l+3) = (l^2-5l-8)/4 > 0 for l >= 7), so every F gap is <= L0-2.

 (Z4) The type word has period L0. Proof: compare the windows [t, t+L0) and [t+1, t+1+L0). The chords of the first that are
      not in the second are those starting at t: one if t is an F position (its gap is <= L0-1, so the chord is inside), none
      if t is a dot (Z2). The chords of the second not in the first are those ending at t+L0: one if t+L0 is an F position
      (the chord starts at >= t+L0-(L0-2) > t), none otherwise. By (Z1) the two counts agree: t in F iff t+L0 in F.
      As the word also has period N, it has period p := gcd(L0, N).

 (Z5) FF pairs. Let t, t+1 both be F positions, and W = [t, t+L0+2). The chords inside W are the c0 chords inside
      [t, t+L0), plus the chords ending at t+L0 and at t+L0+1; these two positions are F positions by (Z4), and their chords
      start at >= t+L0-(L0-2) > t. So W holds at least c0+2 chords of F coordinates. In W (length <= 2K+2 < 3K) every coordinate
      occurs at most 3 times; a coordinate occurring 3 times contributes 2 chords and one "triple" (x, x+, x++), so
      odd(W) = (L0+2) - 2(P(W) - T(W)) with T = number of triples inside W. From odd(W) >= k:
      P(W) - T(W) <= floor((L0+2-k)/2) = c0+1. Hence T(W) >= 1: there is an F position x >= t with x++ <= t+L0+1.

## 1. Proof of Theorem 15  (l = 8q+6, k odd, L0 = 2K)

K = l(l+2)/4 = (8q+6)(2q+2) = 2l(q+1) is even, N = l(l+4) = 4K+2l, and equality holds in Lemma 1 at L = 2K (PROOF6 sec. 1).
p = gcd(2K, N) = gcd(2K, 2l) = 2l, since 2l divides K. So the type word has period 2l, and N/2l = (l+4)/2 = 4q+5 is odd.
The number of F positions is 4(N/2-n) = 2(k+l+3) = (l+2)(l+4)/2, i.e. l+2 > l in each period of length 2l. Hence the type word has
two adjacent F positions; fix residues a, a+1 (mod 2l) of such a pair, and call B the set of the 2(4q+5) positions = a or a+1
(mod 2l). The positions of B come in 4q+5 pairs (t, t+1), t = a (mod 2l); call the pair with floor(t/2l) = j (j in Z_{4q+5}) "pair j".
Adding K to a position keeps its residue mod 2l and moves it q+1 periods forward.

By (Z5) applied to pair j = (t,t+1) there is a triple (x, x+, x++) with x >= t and x++ <= t+2K+1. The two gaps are >= K, so
either both are K and x = t or x = t+1, or they are (K, K+1) or (K+1, K) and x = t. In every case x, x+, x++ are in B
(residues a,a,a / a+1,a+1,a+1 / a,a,a+1 / a,a+1,a+1), x is in pair j, x+ in pair j+(q+1), x++ in pair j+2(q+1), and the two
gaps g(x), g(x+) are in {K, K+1} with at most one of them K+1. Call a triple (x, x+, x++) with x in pair j = (t,t+1) and x++ <= t+2K+1 a "serve" of pair j.
Every pair is served at least once: at least 4q+5 serves in all.

A coordinate c has 4 positions x1 < x1+ < .. with gaps g1..g4, g1+g2+g3+g4 = N = 4K+2l. Its serves are among the four
cyclically consecutive triples; a serve needs two consecutive gaps with sum <= 2K+1. Two "opposite" pairs of gaps
(g1+g2 and g3+g4) cannot both be <= 2K+1 (their sum is N > 4K+2), and three of the four consecutive sums cannot be <= 2K+1 either
(they would include two opposite ones). So a coordinate has at most 2 serves, and if it has 2 they are (x, x+, x++) and
(x+, x++, x+++): they start in pairs j and j+(q+1) for some j, and all four positions of c are in B.
A coordinate with a serve has at least 3 positions in B. So if s_c is the number of serves of c and b_c its number of positions
in B, then s_c <= b_c/2, with equality only if s_c = 2, b_c = 4 (or s_c = b_c = 0). Summing,
4q+5 <= sum_c s_c <= (1/2) sum_c b_c = (1/2) |B| = 4q+5.
So equality holds everywhere: every coordinate has s_c = 0 or s_c = 2, and the total number of serves is exactly 4q+5.
That is impossible because 4q+5 is odd. QED

(Remark on q = 0, l = 6, (20,11), N = 60, K = 12 = 2l: (Z3) gives F gaps <= K+2l = 2K = L0, not L0-2, so (Z4), (Z5) need the
gaps <= L0-2 separately; we do not need this case: K(20,11) = 58 was proved by SAT in S162.)

## 2. Proof of Theorem 16  (l = 8j+5, k even, L0 = 2K-1)

k = l(l+3)/4 = (8j+5)(2j+2) is even, K = k+1 is odd, N = 4k+2l+4 = (l+1)(l+4), and with N/2-n = (k+l+3)/2 and L = 2k+1:
(N/2-n)(4L-N) - N k/2 = (k+l+3)(2k-l) - (2k+l+2)k = 4k - l^2 - 3l = 0: equality in Lemma 1 at L0 = 2K-1 = (l+1)(l+2)/2.
p = gcd(L0, N) = ((l+1)/2) gcd(l+2, 2(l+4)) = (l+1)/2 = 4j+3  (l+2 is odd and gcd(l+2, l+4) = 1).
F positions: 4(N/2-n) = 2(k+l+3) = (l+3)(l+4)/2, i.e. (l+3)/4 = 2j+2 per period p (N/p = 2(l+4)); dots: 2j+1 per period.

 (Z6) No two adjacent dots. Proof: for the window [t, t+L0-2), of length 2K-3, P <= floor((2K-3-k)/2) = k/2 - 1 = c0 - 1.
      The window [t, t+L0) holds c0 chords, so at least one chord inside [t, t+L0) ends at t+L0-2 or t+L0-1. By (Z2) no dot
      chord lies inside a window of length L0, so that end point is an F position: at least one of t+L0-2, t+L0-1 is an F
      position; t is arbitrary.

In a cyclic word of length 4j+3 with 2j+1 dots, no two adjacent, the dots cut the F positions into 2j+1 non-empty runs with
2j+2 elements in total: one run of length 2, all others of length 1. Up to rotation the type word is  FF.(F.)^(2j):
F positions 0, 1 and the odd numbers 3, 5, .., 4j+1; dots 2, 4, .., 4j+2 (mod p).
By (Z5) for the FF pair t = 0 (mod p): there is x >= t with x++ <= t+L0+1 = t+2K; as both gaps are >= K, x = t and
g(t) = g(t+) = K. In particular t+K is an F position. But
K = (8j+5)(2j+2) + 1 = (2(4j+3) - 1)(2j+2) + 1 = -(2j+2) + 1 = 2j+2  (mod 4j+3)   [ -(2j+1) = 2j+2 mod 4j+3 ],
and 2j+2 is an even number in [2, 4j+2], a dot. Contradiction. QED

## 3. Checks

struct/ex4/ex4lem8.py: (i) the arithmetic of both theorems (equality in Lemma 1, p, K mod p, counts per period, the
exclusion of e >= 6, Lemma 2 hypotheses) in exact integers for q, j <= 300; (ii) (Z1)-(Z5) on real zero-slack codes: families 6
and 7 (PROOF6/7) for several l: every 2K-window holds K/2 chords, dot gaps >= 2K, F gaps <= K+2l, type word period, and every
FF pair has a serve; (iii) the counting step of section 1 on those codes (where 2l does not divide K the serves leave the
residues {a, a+1}, which is why the argument does not apply to l = 0, 2, 4 mod 8).
Consistent computer results: K(20,11) = 58 (l = 6), K(18,10) = 50 (l = 5, the j = 0 case), no (90,55) code of length 252 found
in any symmetric class tried, and for (85,52), N = 238, shift-7, shift-14 and half-turn classes UNSAT (S169).

## 4. General form of Theorem 15: larger excess  (added after referee report #17; see the second report below)

Let l be even, k odd, e >= 2 even, N = 4k+2l+e, K = k+1, n = (3k+l+1)/2, and u = l + (e-4)/2, so that N = 4K+2u and
N/2 - n = (K+u+e/2)/2. Lemma 1 at L = 2K (c0 = floor((2K-k)/2) = K/2, K even) reads (K+u+e/2)(2K-u) <= K(2K+u), i.e.
e K <= u(u+e/2), with equality iff

        K = u(2u+e)/(2e).                                                        (E)

## Theorem 17
Let l be even, k odd, n = (3k+l+1)/2, e >= 2 even, N = 4k+2l+e = 4K+2u. Assume (E), K >= 2u+2, and that 2u divides K.
Then there is no spread-k circuit code of length N in Q_n.
(K >= 2u+2 implies N < 6K and the hypotheses of Lemma 1 at L = 2K; with (E) it gives 2u^2 >= 3eu+4e, so u >= 4 and N > 4K+2.)

Proof. Section 0 applies verbatim with L0 = 2K: (Z1) every 2K-window holds K/2 chords, (Z2) dot gaps >= 2K, (Z3) F gaps
<= N-3K = K+2u <= L0-2, (Z4) the type word has period p = gcd(2K, N) = gcd(2K, 2u) = 2u (as 2u | K), (Z5) adjacent F positions
t, t+1 force a triple (x, x+, x++) with x >= t, x++ <= t+2K+1 (floor((2K+2-k)/2) = K/2+1; a dot chord inside the window
only raises P(W), and dots make no triples, so T(W) >= 1 still follows).
The number of F positions is 4(N/2-n) = 2(K+u+e/2) = 2K(2K+u)/(2K-u) by (E), i.e. eK/u = u + e/2 > u = p/2 per period:
adjacent F positions exist. N/p = 2K/u + 1 is odd (2K/u is even). Now section 1 goes through with l replaced by u and 4q+5 by
N/p: K-steps preserve residues mod p; a serve has gaps (K,K), (K,K+1) or (K+1,K) and stays in the residues a, a+1; a
coordinate has gap sum N = 4K+2u > 4K+2, hence at most two serves, two only if all four positions are in B; so
N/p <= sum s_c <= |B|/2 = N/p with every s_c in {0, 2}: impossible, N/p is odd. QED

## Corollary 18 (excess 6, 10, and any e = 2r with r odd and squarefree)
For e = 2r, r odd squarefree: whenever (E) holds (K is even since l is even) and K >= 2u+2, there is no code of length N.
In words: on even lines the bound of Lemma 1 at L = 2K for excess 6, 10, 14, 22, .. is never attained with equality (in the
range K >= 2u+2; for each r exactly one equality case lies outside it, K = 2u, l = 2r+2: (30,17,90) for e = 6 -- excluded by
SAT --, (50,29,150) for e = 10, (70,41,210) for e = 14, not settled). Squarefree is needed: e = 18 has equality cases with 2u not dividing K.
For r = 1 (e = 2) this is Theorem 7 again: l = 0 (mod 4), k = (l^2-l-2)/2, no code of length 4k+2l+2 -- a second, shorter proof. For e = 6: k = (l^2+5l-2)/6, l = 8 (mod 12), l >= 20 (and l = 8, the (30,17) code of length 90, where K = 2u, is
excluded by SAT).
Proof. u = l + r - 2 is odd. (E) reads K = u(u+r)/(2r), so r divides u(u+r), hence r | u^2, hence r | u (squarefree).
Write u = r v, v odd: K = r v (v+1)/2 = u (v+1)/2. K is even and u is odd, so (v+1)/2 is even and 2u divides K. Theorem 17. QED

For e = 4 the condition 2u | K is l = 6 (mod 8) (Theorem 15). For e = 8, 12 one class of l in four has 2u | K
(struct/ex4/zs_general.py); in the other classes K = p/2 (mod p), as for families 6 and 7, and existence is open. The first
excess-8 equality case with K >= 2u+2 is (66,39), N = 192 (l = 14, p = 16; smaller ones: (20,11,64), moot, and (40,23,120) with
K = 2u, open): no code invariant under x -> x+16 (exhaustive over the type
words, which have no two adjacent dots by the argument of (Z6)); the general case is open.

## Referee report (#17, S169)

A fresh AI agent (own scripts theory/referee17/arith.py, zcheck.py): Theorem 15 PASS for q >= 1; Theorem 16 PASS WITH FIXES (the
justification of K >= 2l+3 was wrong for l >= 25, and the wording of (Z6) was a non sequitur; both repaired above); 'Hence' paragraph
PASS; the summary sentence needed the small lines stated (done). It re-derived (Z1)-(Z3) from the proof of Lemma 1, checked
(Z1)-(Z5) on 8 real codes with equality in Lemma 1 (two solver codes, families 6 and 7), confirmed that the counting of section 1
gives no false contradiction there (2l does not divide K, so serves leave the residues {a, a+1}), and checked all arithmetic for
q, j <= 400. No independent SAT confirmation at l = 13 or 14 (too large). NO HUMAN HAS READ THIS.

## Second referee report (#18, S169) on section 4

A fresh AI agent (theory/referee18/arith18.py): PASS, no error; nits applied (standing hypotheses in the statement, the F count as
u + e/2 per period, dot chords in (Z5), the K = 2u boundary cases, the remark that squarefree is needed and that e = 2 gives
Theorem 7 again). It checked the arithmetic for e = 2..60 and even l <= 3000, brute-forced 'opposite gap sums' for small K, u, and
read skelfree.py's constraints for the (30,17,90) data point (single kissat run, no DRAT certificate). For e >= 6 there is no real
code with equality to test (Z1)-(Z5) on: the evidence is the proof plus arithmetic. NO HUMAN HAS READ THIS.
