# PROOF15 (S171, 2026-11-11): odd lines — excess 6, 10, 14, .. with exact values (family 9, period 9)

Notation as in PROOF7.md / PROOF13.md: a spread-k circuit code ("coil") of length N in Q_n, K = k+1, l = 2n-3k-1, excess
e = N-4k-2l, T_x = coordinate flipped at position x in Z_N, g(x) = gap from x to the next position x+ of the same coordinate.
Lemma 1, Lemma 2: PROOF.md. Here l is ODD and k is EVEN (an "odd line"). Until now the only codes known at the equality
points of Lemma 1 on odd lines had excess 2 (family 1, PROOF2 sec. 5), and excess 0 mod 4 is impossible there (Theorem 26).

**Theorem 35.** For every i >= 1 let

        k = 90i+40,     n = 143i+65,     (l = 2n-3k-1 = 16i+9).
Then
        K(n, k) = 396i+180 = 4k + 2l + (4i+2).

So on odd lines the excess over Byrnes' value 4k+2l is unbounded as well, with exact values:
K(208,130) = 576 (excess 6), K(351,220) = 972 (excess 10), K(494,310) = 1368 (excess 14).

Parameters: e = 4i+2, u := l+(e-4)/2 = 18i+8, K = 90i+41 (odd), N = 396i+180 = 4K+2u, N/2 = 2K+u = 198i+90, N/4 = 99i+45.
Residues mod 9:  K = 5,  2K = 1,  N = N/2 = N/4 = 0,  u/2 = 9i+4 = 4,  u-2 = 6,  u+2 = 1,  K+u-2 = 2,  K+u+2 = 6.
K > u+2 and u >= 26.

## 1. Upper bound

k > 3l-3 (90i+40 > 48i+24), so Lemma 2 (k even) gives N' <= 5k+3 for every coil. For a coil of length N' Lemma 1 at
L = 2K-1 = 2k+1 (floor((L-k)/2) = k/2; the hypotheses N' < 6K, max(k, N'/4) <= L <= min(2K, N'-k) hold for N <= N' <= 5k+3)
requires G(N') <= 0, where G(x) = (x/2 - n)(4L - x) - x k/2 = -x^2/2 + x(2L + n - k/2) - 4Ln. G(N) = 0:
(N/2-n)(4L-N) = (55i+25)(324i+144) = 180(11i+5)(9i+4) = (396i+180)(45i+20) = N k/2. The other root of G is
N* = 4L+2n-k-N, and N* - (5k+3) = k-l-e+2 = 70i+31 > 0. So G > 0 on (N, 5k+3]: no coil is longer than N.

## 2. The code

The code is invariant under x -> x+9 (9 divides N): g(x) depends on r = x mod 9.

   r = 0 :           g = N/4 = K + u/2          ("E run": the four positions x, x+N/4, x+N/2, x+3N/4, all of residue 0)
   r = 2, 6 :        g = K
   r = 7 :           g = K + u + 2
   r = 4 :           g = K + u - 2
   r = 1, 3 :        g = N/2                    (dots; partner on the same residue)
   r = 5 :           g = N/2 + 3                (dot; partner on residue 8)
   r = 8 :           g = N/2 - 3                (dot; partner on residue 5)

s(x) = x+g(x) permutes Z_N. On residues: 2 -> 7 -> 4 -> 6 -> 2 (steps K, K+u+2, K+u-2, K = 5, 6, 2, 5 mod 9) with gap sum
4K+2u = N; 0 -> 0 with 4 gaps N/4; 1 -> 1, 3 -> 3 (two gaps N/2); 5 -> 8 -> 5 (gaps N/2+3, N/2-3). So the orbits of s on the
residues F = {0,2,4,6,7} have exactly 4 elements ("F coordinates") and those on D = {1,3,5,8} exactly 2 ("dots").
T_x := the orbit of x. Number of coordinates: (N/9)(5/4 + 4/2) = (44i+20)(13/4) = 143i+65 = n.
The walk v_0 = 0, v_{x+1} = v_x xor T_x is closed (every coordinate is used an even number of times).
(struct/ex4/p8/odd9.py builds it and checks the definition.)

## 3. Reduction

All gaps are >= K. A window and its complement have the same odd coordinates, and a window of length <= k has distinct
coordinates, so it suffices to show odd(W) >= k for W = [t, t+L), K <= L <= N/2 = 2K+u. Write L = K+y, 0 <= y <= K+u.

Dots: both positions of a dot lie in W only if its gap is <= L-1 <= N/2-1: the dot starts at a position x of residue 8
(gap N/2-3) with t <= x and x+N/2-3 <= t+L-1, i.e. x in [t, t+y-K-u+2]. This interval has at most 3 elements, so the number
Dd of dots occurring twice is 0 or 1, and Dd = 0 unless y >= K+u-2.
F coordinates: three consecutive gaps sum to at least N-(K+u+2) = 3K+u-2 > N/2 (for the E run: 3N/4), so an F coordinate occurs
at most 3 times; its occurrences in W are consecutive in its orbit (W is shorter than N), so a coordinate occurring twice
contributes one chord, one occurring three times two chords and one triple.
With P = number of F chords (x, s x) inside W and T = number of F triples (x, s x, s^2 x) inside W:
odd(W) = L - 2(P - T + Dd), and the claim is

    (*)     P - T + Dd <= floor((y+1)/2) = ceil(y/2)        for all t and 0 <= y <= K+u.

Chords. The chord from x lies in W iff x >= t and x+g(x) <= t+K+y-1, i.e. the point z = x+g(x)-K lies in [t, t+y) and
z-(g(x)-K) >= t. By residue of x: r = 2: z = 2 (mod 9), z >= t;  r = 6: z = 6, z >= t;  r = 0: z = 4, z >= t+u/2;
r = 4: z = 1 (4+6), z >= t+u-2;  r = 7: z = 8 (7+1), z >= t+u+2. So with J = [t, t+y) and S := {1,2,4,6,8} (mod 9):

    P = |S n J| - X4 - X1 - X8,   X4 = #{z in J: z = 4 (9), z < t+u/2},  X1 = #{z in J: z = 1, z < t+u-2},  X8 = #{z in J: z = 8, z < t+u+2}.

Triples. The triple from x lies in W iff x >= t and x+g(x)+g(s x) <= t+K+y-1. Two-gap sums: r = 6: 2K;  r = 4: 2K+u-2;
r = 2: 2K+u+2;  r = 0: 2K+u;  r = 7: 2K+2u. As y <= K+u, only r = 6 and r = 4 can occur:
    T = X2 + X6,   X2 = #{z in J: z = 2 (9), z >= t+K}   [z = x+K, x = 6],     X6 = #{z in J: z = 6, z >= t+K+u-2}   [z = x+K+u-2, x = 4].
In particular T = 0 for y <= K.

Two facts about residues mod 9:  (S1) S has no two adjacent NON-members (the non-members are 0, 3, 5, 7), and its only two
adjacent members are 1, 2.  (S2) S' := {1,4,6,8} has no two adjacent members; {2,4,6} has no two adjacent members.

## 4. Proof of (*)

**(a) 0 <= y < u-2.** T = Dd = 0 and P = #{z in J : z = 2 or 6} + #{z in J : z = 4, z >= t+u/2} <= |{2,4,6} n J| <= ceil(y/2) by (S2).

**(b) u-2 <= y < u+2.** T = Dd = 0, X8 = |{8} n J|, and P <= |{2,4,6} n J| + #{z = 1 in [t+u-2, t+y)} <= 3 ceil(y/9) + 1
(the last interval has at most 3 elements) <= (y+8)/3 + 1 <= y/2 because y >= u-2 >= 24 > 22.

**(c) y = K.** Now X4, X1, X8 count over the full intervals [t, t+u/2), [t, t+u-2), [t, t+u+2) (all inside J), of lengths
9i+4, 9(2i)+6, 9(2i+1)+1:
    X4 = i + [(4-t) mod 9 <= 3],   X1 = 2i + [(1-t) mod 9 <= 5],   X8 = 2i+1 + [t = 8 (9)].
K = 9(10i+4)+5, so |S n J| = 5(10i+4) + s5(t), where s5(t) = number of members of S among the residues t, t+1, .., t+4:
s5 = 3, 3, 3, 2, 3, 2, 3, 3, 3 for t = 0, .., 8 (mod 9). ceil(K/2) = 45i+21. Hence

    D(t) := P(t,K) - ceil(K/2) = s5(t) - 2 - [t in {1,2,3,4}] - [t in {0,1,5,6,7,8}] - [t = 8]   =   0, -1, 0, -1, 0, -1, 0, 0, -1   (t = 0..8).

In particular P(t,K) <= ceil(K/2) = (K+1)/2, and D(t) = 0 exactly for t in {0, 2, 4, 6, 7} (mod 9).

**(d) u+2 <= y < K.** T = Dd = 0 and X4, X1, X8 are as in (c), so P(t,K) - P(t,y) = |S n I'| with I' = [t+y, t+K), of length
m = K-y, and ceil(K/2) - ceil(y/2) = ceil(m/2) (K odd). So P(t,y) - ceil(y/2) = D(t) + ceil(m/2) - |S n I'|.
By (S1), |S n I'| >= floor(m/2): done if m is even or D(t) = -1. If m is odd and D(t) = 0: the last element of I' is
t+K-1 = t+4 (mod 9), which is 4, 6, 8, 1, 2 for t = 0, 2, 4, 6, 7: a member of S; pairing the other m-1 elements of I' from
the end, |S n I'| >= 1 + (m-1)/2 = ceil(m/2). So P(t,y) <= ceil(y/2).

**(e) y = K+d, 1 <= d <= u.** P(t,y) = P(t,K) + |S n I|, I = [t+K, t+K+d) (every member of S in I is counted: K >= u+2).
T = X2 + X6 and X2 = #{z in I : z = 2 (9)}. So

    P - T + Dd = P(t,K) + |S' n I| - X6 + Dd <= (K+1)/2 + D(t) + |S' n I| + Dd,

and ceil(y/2) = (K+1)/2 + floor(d/2). It remains to show  D(t) + |S' n I| + Dd <= floor(d/2).
 * d < u-2: Dd = 0. By (S2) |S' n I| <= ceil(d/2): done if d is even or D(t) = -1. If d is odd and D(t) = 0: the first element
   of I is t+K = t+5 (mod 9), which is 5, 7, 0, 2, 3 for t = 0, 2, 4, 6, 7: not in S'; so |S' n I| <= (d-1)/2 = floor(d/2).
 * u-2 <= d <= u (then Dd <= 1, D(t) <= 0): write d = 9a+b, 0 <= b <= 8; a >= 2i (d >= 18i+6). S' has 4 members per 9
   consecutive residues and at most ceil(b/2) among b consecutive ones (S2): |S' n I| <= 4a + ceil(b/2). And
   floor(d/2) = 4a + floor((a+b)/2). For a >= 3 (true if i >= 2): floor((a+b)/2) >= ceil(b/2) + 1, so
   |S' n I| + 1 <= floor(d/2).
   For i = 1 (u = 26; d = 24, 25, 26 = 18+6, 18+7, 18+8; 8 members in the first 18 elements of I): a window of 6 residues holds
   at most 3 members of S', one of 8 residues at most 4, so |S' n I| <= 11 (d = 24) and <= 12 (d = 26), while floor(d/2) = 12, 13:
   fine. A window of 7 residues holds 4 members only if it starts at residue 4 (4,6,8,1), otherwise at most 3. So for d = 25:
   |S' n I| <= 11 and 11+1 <= 12, unless I starts at residue 4, i.e. t = 8 (mod 9); then D(t) = -1 and -1+12+1 <= 12.

(a)-(e) cover all 0 <= y <= K+u and give (*). So the walk of section 2 is a spread-k circuit code of length N in Q_n; with
section 1, K(n,k) = N. QED

## Checks

struct/ex4/p8/odd9.py i: the code from section 2, definition by all pairs: VALID for i = 1..16, 18, 20, 24, 30 (see
p8/runs/odd9_check.out); snake/check.py VALID for i = 1, 2, 3 (codes/fam9_*). struct/ex4/p8/lem15.py IMAX: the formulas for P, T,
Dd against direct counts, the table D(t), every inequality of (a)-(e) for all t, y. The upper bound: exact integers i <= 400.
How it was found: at an odd-line equality point the type word has period p = gcd(2K-1, N) and every FF pair t, t+1 forces
g(t) = g(t+K) = K; with these forced gaps as clauses the lazy SAT (p8/oddpt.py, oddsh.py) decides a point in seconds. It
refuted (108,66,304), (87,52,252), (119,72,340), (168,102,480) and found shift-9 codes at (208,130,576), (351,220,972),
(494,310,1368), which share one 9-residue design. Other periods carry codes too ((418,266,1144), p = 13; (270,170,744), p = 31):


## Referee report (#29, S171)

A fresh AI agent (own program theory/referee29/ref.py, written from this text only): PASS; three cosmetic fixes (applied:
"at most 3 elements" in (b), "=" in (e), one sentence on consecutive occurrences in section 3). Hand check of sections 1-4,
case by case, including the table D(t) and the coverage of 0 <= y <= K+u for every i >= 1: correct. By program: the code
rebuilt for i = 1..8 (all pairs VALID, snake/check.py VALID for i = 1, 4, mutants rejected); every formula and inequality of
sections 3-4 for i = 1..6, all t, y; the upper bound in exact integers for i <= 2000. Not checked: Lemma 1, Lemma 2 themselves,
the 'how it was found' paragraph, prior art.
NO HUMAN HAS READ THIS.
