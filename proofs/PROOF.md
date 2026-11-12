# An upper bound for circuit codes near n = 3k/2  (S164, 2026-11-10)

Status: derived S164; every inequality machine-tested on 18,902 real coils (0 failures); arithmetic checked for
l <= 40, k <= 3000; consistent with every exact value I know. REFEREE PASS (independent agent, S164 08:34): all steps re-derived, no mathematical error in the lemmas; one wrong
justification in the Main Theorem (odd-k endpoint) fixed below; its own random-coil test: 4,787 coils, 0 violations
(Lemma 2 only tested for k <= 5 there; my thmA_check covers larger k). Not read by a human. Prior art: an agent read
Byrnes 2008.04839, 1809.08428, 1604.02755 in full and found nothing like it; Douglas 1969 (both papers), Singleton 1966
and Deimer 1984 are paywalled and were NOT read, so "new" is unverified.

## Statement

A spread-k circuit code (coil) of length N in Q_n is a cycle v_0..v_{N-1} in the n-cube with
d_H(v_i,v_j) < k  =>  d_C(i,j) = d_H(v_i,v_j)   (d_C = cyclic distance). K(n,k) = maximum N.
Write l = 2n - 3k - 1 (so n = (3k+l+1)/2; k and l have opposite parity) and K = k+1.

**Main Theorem.** Let l >= 2 and
  * l odd  (k even):  k > (l^2-1)/2  and k > 3l-3   (the second only matters for l = 3: k >= 8),
  * l even (k odd):   k > (l-2)(l+1)/2.
Then every spread-k coil in Q_n has length N <= 4k + 2l.

Byrnes (2008.04839, Thm 1.3) constructs coils of length 4k+2l for k >= 2l+1 (k odd) / k >= 2l-2 (k even), so in the
theorem's range (l >= 5) K(n,k) = 4k+2l: his Conjecture 4.2 is TRUE once k exceeds about l^2/2.
(And it is FALSE at its stated threshold for l = 6..11: optcensus/README S162-S163.)

Thresholds (largest k NOT covered):  l=2: -, 3: 6, 4: 5, 5: 12, 6: 13, 7: 24, 8: 27, 9: 40, 10: 43, 11: 60, 12: 65.
Sharp at l=6: a (23,13) coil of length 66 = 4k+2l+2 exists (codes/sat_23_13_66.txt), k = 13 is the last uncovered k.

## Notation and three facts

T = (T_0..T_{N-1}) the cyclic transition word (T_i = coordinate flipped between v_i and v_{i+1}).
A *window* of length L is L cyclically consecutive transitions; it joins v_t to v_{t+L}.
odd(W) = number of coordinates occurring an odd number of times in W = d_H(v_t, v_{t+L}).

(F1) If k <= L <= N-k then odd(W) >= k, and odd(W) = L mod 2. So odd(W) >= k + ((L-k) mod 2).
(F2) Any K = k+1 consecutive transitions are distinct (N >= 2k+1): a window of length j <= k-1 joins vertices at cyclic
     distance j < k; if d_H < j then d_H < k forces d_C = d_H < j, contradiction; so d_H = j for j <= k-1, and j = k,
     k+1 follow from (F1) (odd >= k, parity).  Hence consecutive occurrences of one coordinate are >= K apart.
(F3) For each position i let g_i >= K be the distance to the next occurrence of the same coordinate T_i (cyclically;
     'i+' = i + g_i denotes that next occurrence), and e_i = g_i - K >= 0. Then sum_i g_i = N * (number of used
     coordinates) <= N n.  A window of length L contains j consecutive occurrences i, i+, .., of one coordinate
     (total span G = g_i + g_{i+} + ..) for exactly (L - G)^+ of its N positions (valid for L < N).
     A window of length L <= jK contains each coordinate at most j times (j+1 occurrences span >= jK+1 transitions).

x^+ = max(x,0).  Elementary: (a+b)^+ <= a^+ + b^+ ;  and if c >= a, c >= b then (a+b-c)^+ >= a^+ + b^+ - c^+.
(Proof of the second. If a >= 0 and b >= 0: then c >= 0 and the right side is a+b-c <= (a+b-c)^+.
 If a < 0 <= b: the right side is b - c^+ = b - c <= 0 (c >= b >= 0). Symmetrically for b < 0 <= a.
 If a < 0 and b < 0: the right side is -c^+ <= 0. In the last three cases the left side is >= 0.)
Throughout N >= 2k+2 (shorter coils are irrelevant: N = 2k makes Lemma 1 trivial).
For a coordinate used exactly twice, i++ = i, the "triple" (i,i+,i++) has span G = N and (L-G)^+ = 0, as it should.

## Lemma 1 (chord inequality)

For a spread-k coil with N < 6K and any L with max(k, N/4) <= L <= min(2K, N-k):
        (N/2 - n) (4L - N)  <=  N * floor((L-k)/2).

Proof. L <= 2K: every coordinate occurs at most twice in a window (F3), so odd(W) = L - 2 P(W), P(W) = number of
coordinates occurring twice = number of pairs (i, i+) inside W ("chords"). By (F1) P(W) <= floor((L-k)/2).
Summing over the N windows, sum_W P(W) = sum_i (L - g_i)^+  (F3).
N < 6K: by (F2) every coordinate is used 0, 2 or 4 times (uses are even since the walk closes; 6 uses need N >= 6K).
With n_1 coordinates used twice and n_2 used four times: n_1 + n_2 <= n and 2 n_1 + 4 n_2 = N, so n_2 >= N/2 - n.
A coordinate used four times has four gaps summing to N, so its four terms give
sum (L - g)^+ >= sum (L - g) = 4L - N >= 0.  All other terms are >= 0.  Hence
        n_2 (4L - N) <= sum_W P(W) <= N floor((L-k)/2),
and since 4L - N >= 0 and n_2 >= N/2 - n the claim follows. QED

## Lemma 2 (Theorem A: no long codes)

For a spread-k coil with N >= 5k+4 (so that windows of length 2K, 3K, 4K all satisfy k <= L <= N-k):
        k + (k mod 2)  <=  6n - 12K + 6 floor((k+2)/2).
With n = (3k+l+1)/2 the right side is 3l-3 (k even) and 3l-6 (k odd). So a coil with k > 3l-3 (k even) or
k > 3l-7 (k odd) has N <= 5k+3.

Proof. Put x_i = (K - e_i)^+, b_i = (K - e_i - e_{i+})^+, A = floor((k+2)/2).

(a) L = 2K. As in Lemma 1 (this part needs no bound on N: a window of length 2K holds each coordinate <= 2 times), P(W) <= floor((2K-k)/2) = A and sum_W P(W) = sum_i (2K - g_i)^+ = sum_i x_i. So
        sum_i x_i <= N A.                                                   (1)
(b) L = 3K. Each coordinate occurs <= 3 times; let c_j = number of coordinates occurring exactly j times in W.
    3K = c_1 + 2c_2 + 3c_3, odd = c_1 + c_3, and the number of distinct coordinates c_1+c_2+c_3 <= n.
    Then c_2 + c_3 = (3K - odd)/2 and c_1+c_2+c_3 = odd + c_2 = (3K + odd)/2 - c_3 <= n, so
    c_3 >= (3K + odd)/2 - n >= ceil((3K + k)/2) - n = 2K - n   (odd >= k, odd = 3K mod 2; (4k+3)/2 rounds up to 2k+2).
    c_3(W) = number of triples (i, i+, i++) inside W, so by (F3)
        sum_i b_i = sum_i (3K - g_i - g_{i+})^+ = sum_W c_3(W) >= N (2K - n).            (2)
(c) L = 4K. Each coordinate occurs <= 4 times. 4K = c_1 + 2c_2 + 3c_3 + 4c_4 and
    odd = c_1 + c_3 = 4K - 2(c_2 + 2c_3 + 3c_4) + 2(c_3 + c_4) = 4K - 2 ch(W) + 2 t(W) - 2 q(W),
    where ch = c_2+2c_3+3c_4 = number of chords (i,i+) inside W, t = c_3 + 2c_4 = number of triples inside W,
    q = c_4 = number of quadruples (i,i+,i++,i+++) inside W.  Summing over windows with (F3):
      sum_W ch = sum_i (4K - g_i)^+ >= sum_i (4K - g_i) >= N (4K - n);
      sum_W t  = sum_i (4K - g_i - g_{i+})^+ = sum_i ((K-e_i) + (K-e_{i+}))^+ <= sum_i (x_i + x_{i+}) = 2 sum_i x_i <= 2NA
                 (i -> i+ is a bijection of positions; (1));
      sum_W q  = sum_i (4K - g_i - g_{i+} - g_{i++})^+ = sum_i (K - e_i - e_{i+} - e_{i++})^+
               >= sum_i ( b_i + b_{i+} - x_{i+} ) = 2 sum b_i - sum x_i >= 2N(2K - n) - NA
                 (second elementary inequality with a = K-e_i-e_{i+}, b = K-e_{i+}-e_{i++}, c = K-e_{i+}; (1), (2)).
    Therefore  sum_W odd(W) <= N [ 4K - 2(4K-n) + 4A - 4(2K-n) + 2A ] = N [ 6n - 12K + 6A ].
    By (F1) with L = 4K (even): odd(W) >= k + (k mod 2) for every W. QED
    (k even: 6A = 3K+3, 6n = 9K + 3l - 6: bound 3l-3.  k odd: 6A = 3K: bound 3l-6.)

## Proof of the Main Theorem

Suppose a coil has N = 4k + 2l + e with e >= 2 (N is even).
Case N >= 5k+4: excluded by Lemma 2, since k > 3l-3 (k even; for l >= 5 implied by k > (l^2-1)/2, for l = 3 assumed) or
k > 3l-7 (k odd; implied by k > (l-2)(l+1)/2 because (l-3)(l-4) >= 0).
Case 4k+2l < N <= 5k+4, i.e. 2 <= e <= k+4-2l: N < 6K, so Lemma 1 applies. N/2 - n = (k+l-1+e)/2.
 * k even: take L = 2k+1 (k <= L <= N-k, floor((L-k)/2) = k/2, 4L - N = 4k+4-2l-e > 0). Lemma 1 requires f(e) <= 0 with
     f(e) = (k+l-1+e)(4k+4-2l-e) - (4k+2l+e) k = -e^2 + (2k+5-3l) e - (2l^2 - 6l + 4).
   f is concave, f(2) = 4k + 2 - 2l^2 > 0 iff k > (l^2-1)/2, and f(k+4-2l) = k (k+5-3l) > 0 because
   k > (l^2-1)/2 >= 3l-5 (as (l-3)^2 >= 0). So f > 0 on the whole range:
   contradiction.
 * k odd: take L = 2k+2 (floor((L-k)/2) = (k+1)/2, 4L - N = 4k+8-2l-e > 0). Lemma 1 requires f(e) <= 0 with
     f(e) = (k+l-1+e)(4k+8-2l-e) - (4k+2l+e)(k+1) = -e^2 + (2k+8-3l) e - (2l^2 - 8l + 8).
   f(2) = 4k + 4 + 2l - 2l^2 > 0 iff k > (l-2)(l+1)/2, and f(k+4-2l) = k^2 + (8-3l) k + 8 - 4l > 0:
   for l = 2 it is k(k+2); for even l >= 4 the hypothesis k >= (l-2)(l+1)/2 + 1 gives k+8-3l >= (l^2-7l+16)/2 >= 2,
   so f >= 2k - (4l-8) >= l^2 - 5l + 8 > 0.  (k odd: the largest admissible e is k+3-2l; concavity covers it.)
   (Fix supplied by the referee pass; also checked with exact integers, l <= 60, k <= 4000.)
   Contradiction again. QED

## Consequences (with the SAT results of S161-S163)

 * l = 5: K((3k+6)/2, k) = 4k+10 for every even k >= 8  (k = 8,10,12,14 by SAT+DRAT: K(15,8)=42, K(18,10)=50,
   K(21,12)=58, K(24,14)=66; k >= 14 by the theorem). The l=5 line of Conjecture 4.2 is completely settled (true).
 * l = 6: K(23,13) = 66 = 4k+14 (SAT; the conjecture's boundary case fails) and K((3k+7)/2, k) = 4k+12 for every odd
   k >= 15 (theorem; K(26,15)=72 was also proved by SAT). Completely settled.
 * Every line: codes longer than 4k+2l exist for at most finitely many k (k <= 24, 27, 40, 43, 60 for l = 7..11).
   Known: l=7 up to k=18, l=8 up to 19, l=9 up to 22, l=10 up to 23, l=11 up to 22. Open k in between.
 * Small l: re-derives Douglas' l = 2 (all odd k >= 3), l = 3 (even k >= 8), l = 4 (odd k >= 7; Douglas needs k >= 9).

## Machine checks (theory/)

 thmcheck.py      Lemma 1's two sides computed from real codes (sum over windows vs the bound): 0 violations on all
                  release coils and the S163 code sets; (23,13,66) and Byrnes' codes are within 2 of equality.
 thmA_check.py    Lemma 2: (1), (2), the 4K identity and the final bound on 18,902 coils with N >= 5k+4 (18,796 of them are (22,11,66) codes, the rest
                  release records with many different (n,k)): 0 failures
                  (tightest: (17,9,50): mean odd 10.0 vs bound 12).
 mainthm_check.py the arithmetic of the Main Theorem, exact integers, l <= 40, k <= 3000: 0 failures.
 lpbound.py / lpscan.py   the full window-parity LP (all window lengths, all gap types): independent numerical
                  confirmation ((24,14): every N = 68..100 infeasible; (23,13,68), (26,15,74) infeasible), and extra
                  upper bounds below the thresholds (e.g. (34,20): N=98 infeasible; (25,14): N=78 infeasible).
 bound.py, bound2.py, bound3.py   which N the inequalities exclude, per line.

## S172 addendum (2026-11-11): machine-checked; Lemma 2 is local

Lemma 1, Lemma 2 and the Main Theorem are kernel-checked in Lean 4 (lean/, Basic.lean; statement for genuine vertex
sequences: `coil_length_bound`). Two simplifications found while formalizing:
* Lemma 1 without gaps: for a window W of length L <= 2K, count_c(W) <= 1 + [count_c(W) = 2]; summing over the N windows gives
  sum_W [count_c(W) = 2] >= L m_c - N for a coordinate used m_c times.
* Lemma 2 needs NO averaging over windows: it holds for every single window W of length 4K. Split W into four K-blocks with
  counts a_1..a_4 in {0,1} per coordinate, s = a_1+..+a_4. Pointwise (16 cases):
      [s odd] + s + 2[a_1+a_2+a_3 = 3] + 2[a_2+a_3+a_4 = 3]  <=  2 + 2[a_1+a_2 = 2] + 2[a_3+a_4 = 2] + 2[a_2+a_3 = 2].
  Summing over coordinates: odd(W) + 4K + 2c_3(W') + 2c_3(W'') <= 2n + 2P(B_1B_2) + 2P(B_3B_4) + 2P(B_2B_3) <= 2n + 6A, and
  c_3 >= 2K-n for the two 3K-windows W', W''. Hence odd(W) <= 6n - 12K + 6A for every such window.
