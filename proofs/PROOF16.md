# PROOF16 (S171, 2026-11-11): odd lines — a two-parameter family (family 10) with exact values

Notation as in PROOF15.md (which is the case p = 9 with a different choice of dot gaps): a spread-k circuit code ("coil") of
length N in Q_n, K = k+1, l = 2n-3k-1 (odd), k even, excess e = N-4k-2l; T_x = coordinate flipped at position x in Z_N;
g(x) = gap to the next position of the same coordinate. Lemma 1, Lemma 2: PROOF.md.

**Theorem 36.** Let p = 4j+1 with j >= 2 (p = 9, 13, 17, ..) and i >= 1. Put

        l = p + (2p-2) i,       k = (p^2-1)/2 + p(p+1) i,       n = (3k+l+1)/2.
Then
        K(n, k) = 4k + 2l + (4i+2) = 2p(p+1) + 4p(p+2) i.

(i = 0 are the points of family 1, Theorem 5: K = 4k+2l+2 at l = p, k = (l^2-1)/2. p = 9 gives the values of Theorem 35, by a different code; for i = 0 see section 5.)
First new values: K(418,266) = 1144, K(700,450) = 1904 (excess 6), K(703,448) = 1924 (excess 10).

Parameters. e = 4i+2, u := l+(e-4)/2 = p-1+2pi, K = (p^2+1)/2 + p(p+1)i, N = 2p(p+1) + 4p(p+2)i = 4K+2u, N/2 = 2K+u,
N/4 = K+u/2 = p(p+1)/2 + p(p+2)i (an integer: p is odd). c := (p-5)/2 = 2j-2 (even, >= 2).
Residues mod p:  N = N/2 = N/4 = 0,   K = (p+1)/2 = 2j+1,   2K = 1,   u = -1,   u/2 = (p-1)/2 = 2j.
[k = (p-1)(p+1)/2 + .. = (p-1)/2 mod p, as (p+1)/2 * (p-1) = -(p+1)/2 = (p-1)/2 mod p.]
Sizes: K > u+c, and u-c = 2pi+2j+2 >= p+4 (i >= 1).

## 1. Upper bound

k > 3l-3: (p^2-1)/2 > 3p-3 and p(p+1) > 6p-6 for p >= 9. So Lemma 2 (k even) gives N' <= 5k+3 for every coil. Lemma 1 at
L = 2K-1 = 2k+1 (floor((L-k)/2) = k/2; its hypotheses N' < 6K, max(k, N'/4) <= L <= min(2K, N'-k) hold for N <= N' <= 5k+3)
requires G(N') <= 0 with G(x) = (x/2-n)(4L-x) - xk/2 = -x^2/2 + x(2L+n-k/2) - 4Ln, a concave quadratic.
G(N) = 0: put A := (p+1)/2 + (p+2)i and B := (p-1)/2 + pi. Then N = 4pA, k = (p+1)B, n = (N/p)(3p-1)/8 = (3p-1)A/2
(section 2), N/2-n = (p+1)A/2, and 4L-N = 8k+4-N = 8(p+1)B + 4 - 4pA = 2p(p-1) + 4p^2 i = 4pB. So
(N/2-n)(4L-N) = 2p(p+1)AB = N k/2.
The other root of G is N* = 4L+2n-k-N, and N*-(5k+3) = k-l-e+2 = (p^2-2p-1)/2 + (p^2-p-2)i > 0. So G > 0 on (N, 5k+3]:
no coil is longer than N.

## 2. The code

Invariant under x -> x+p (p divides N); g depends on r = x mod p, 0 <= r < p:

   r = p-3  and  r = c = (p-5)/2 :     g = K
   r = p-2 :                           g = K + u + c
   r = p-5 :                           g = K + u - c
   every other even r <= p-7 :         g = N/4 = K + u/2        ("E runs")
   odd r <= p-4, and r = p-1 :         g = N/2                  (dots)

F residues: the even r <= p-3 and r = p-2 ((p+1)/2 residues); dot residues: the odd r <= p-4 and p-1 ((p-1)/2 residues).
s(x) = x+g(x) on residues: p-3 -> c -> p-2 -> p-5 -> p-3 (steps K, K, K+u+c, K+u-c = 2j+1, 2j+1, 4j-2, 2 mod p; the four
residues are distinct as j >= 2), gap sum 4K+2u = N; an E residue is fixed (N/4 = 0 mod p), four gaps N/4; a dot residue is
fixed, two gaps N/2. So every orbit of s on F residues has 4 elements, every orbit on dot residues 2; T_x := the orbit of x.
Number of coordinates: (N/p)((p+1)/8 + (p-1)/4) = (N/p)(3p-1)/8 = n. The walk v_{x+1} = v_x xor T_x is closed.
(struct/ex4/p8/odd10.py p i builds it and checks the definition.)

## 3. Reduction

All gaps are >= K. A window of length <= k has distinct coordinates, and a window and its complement have the same odd
coordinates; so (as in PROOF15 sec. 3) it suffices to show odd(W) >= k for W = [t, t+L), K <= L <= N/2, L = K+y, 0 <= y <= K+u.
A dot never occurs twice in W (its gap is N/2 > L-1). Three consecutive gaps of an F coordinate sum to at least
N-(K+u+c) = 3K+u-c > N/2 (E runs: 3N/4), so an F coordinate occurs at most 3 times, in consecutive positions of its orbit.
With P = number of F chords (x, s x) inside W and T = number of F triples inside W: odd(W) = L - 2(P-T), and the claim is

    (*)     P - T <= ceil(y/2)        for all t and 0 <= y <= K+u.

Chords: the chord from x lies in W iff the point z = x+g(x)-K lies in J := [t, t+y) and z-(g(x)-K) >= t. Residue of z and
the threshold:
    x = p-3:  z = p-3 = 4j-2, no threshold;        x = c:  z = c = 2j-2, no threshold;
    x = p-5:  z = p-5+u-c = 2j-3,  z >= t+u-c;     x = p-2:  z = p-2+u+c = 2j-5 (mod p; this is p-1 if j = 2),  z >= t+u+c;
    x = r (E run):  z = r+2j,  z >= t+u/2.
The E residues are the even r in [0, 4j-6] other than 2j-2, so r+2j runs over the even numbers in [2j, 4j-4] and (for
r >= 2j) over r+2j-p = the odd numbers in [-1, 2j-7], where -1 means p-1 = 4j. Altogether the set of marked residues is

    S = { odd z : 1 <= z <= 2j-3 }  u  { even z : 2j-2 <= z <= 4j }           (|S| = 2j+1; for j = 2: S = {1,2,4,6,8}),

each residue of S being the z of exactly one F residue. Let S_E = S \\ {4j-2, 2j-2, 2j-3, (2j-5) mod p} (the E marks). Then

    P = |S n J| - X_E - X_3 - X_5,    X_E = #{z in J : z in S_E, z < t+u/2},   X_3 = #{z in J : z = 2j-3, z < t+u-c},
                                       X_5 = #{z in J : z = 2j-5, z < t+u+c}.
Triples: two-gap sums from x = p-3: 2K (z = x+K = 2j-2);  x = p-5: 2K+u-c (z = x+K+u-c = 4j-2);  x = c: 2K+u+c;  x = p-2: 2K+2u;
E runs: 2K+u. A triple lies in W iff x >= t and x + (two-gap sum) <= t+K+y-1; as y <= K+u only the first two occur:
    T = #{z in J : z = 2j-2 (p), z >= t+K} + #{z in J : z = 4j-2 (p), z >= t+K+u-c}.       (T = 0 for y <= K.)

Facts (mod p): (S1) S has no two adjacent non-members, and its only adjacent members are 2j-3, 2j-2.
(S2) S' := S \\ {2j-2} and S'' := S \\ {2j-3, (2j-5) mod p} have no two adjacent members; the four consecutive residues
2j-6, 2j-5, 2j-4, 2j-3 (mod p) are not in S''.

## 4. Proof of (*)

**(a) y < u-c.** T = 0 and no point of residue 2j-3 or 2j-5 is counted: P <= |S'' n J| <= ceil(y/2) (S2).

**(b) u-c <= y < u+c.** T = 0; no point of residue 2j-5 is counted, and the counted points of residue 2j-3 lie in
[t+u-c, t+y), an interval of length < 2c = p-5: at most one. So P <= |S'' n J| + 1. J has length y >= u-c >= p+4 (p+3 would
suffice), so it contains
four consecutive positions with residues 2j-6, .., 2j-3, none in S''; the a positions of J before them and the b positions
after them hold at most ceil(a/2) + ceil(b/2) <= (a+b)/2 + 1 = y/2 - 1 points of S''. So P <= y/2 <= ceil(y/2).

**(c) y = K.** X_E, X_3, X_5 count over the full intervals [t, t+u/2), [t, t+u-c), [t, t+u+c), of lengths pi+2j, 2pi+(2j+2),
(2i+1)p+(2j-3). With [a, b] denoting residues of a cyclic interval (mod p):
    X_E = (2j-3) i + |S_E n [t, t+2j-1]|,    X_3 = 2i + [2j-3 in [t, t+2j+1]],    X_5 = 2i+1 + [2j-5 in [t, t+2j-4]].
K = pQ + (2j+1) with Q = 2j + (4j+2)i, so |S n J| = (2j+1)Q + |S n [t, t+2j]|, and ceil(K/2) = (K+1)/2 = (pQ+2j+2)/2.
(2j+1)Q - pQ/2 = Q/2 = j + (2j+1)i. Hence

    D(t) := P(t,K) - ceil(K/2) = |S n [t, t+2j]| - |S_E n [t, t+2j-1]| - 2 - [2j-3 in [t, t+2j+1]] - [2j-5 in [t, t+2j-4]].

|S n [t,t+2j]| - |S_E n [t,t+2j-1]| = [t+2j in S] + (number of the four residues 4j-2, 2j-2, 2j-3, 2j-5 in [t, t+2j-1]). Now
  [4j-2 in [t,t+2j-1]] + [2j-2 in [t,t+2j-1]] = [t in [2j-1, 4j-2]] + [t in [-1, 2j-2]] = 1 - [t = p-2],
  [2j-3 in [t,t+2j-1]] - [2j-3 in [t,t+2j+1]] = -[t = p-3 or p-4],
  [2j-5 in [t,t+2j-1]] - [2j-5 in [t,t+2j-4]] = [t in {p-2, p-3, p-4}].
Adding up:        D(t) = [t+2j in S] - 1.
So P(t,K) <= ceil(K/2), with equality iff t+2j is in S; and then t+2j+1 is not in S' (two adjacent members of S are
2j-3, 2j-2, and 2j-2 is not in S').

**(d) u+c <= y < K.** T = 0, the X's are as in (c): P(t,K) - P(t,y) = |S n I'|, I' = [t+y, t+K), m := K-y, and
ceil(K/2) - ceil(y/2) = ceil(m/2) (K odd). So P(t,y) - ceil(y/2) = D(t) + ceil(m/2) - |S n I'|. By (S1) |S n I'| >= floor(m/2):
done if m is even or D(t) = -1. If m is odd and D(t) = 0, the last element t+K-1 = t+2j (mod p) of I' is in S, and pairing the
other m-1 elements from the end gives |S n I'| >= ceil(m/2).

**(e) y = K+d, 1 <= d <= u.** P(t,y) = P(t,K) + |S n I|, I = [t+K, t+K+d) (K >= u+c: every member of S in I is counted), and
T >= #{z in I : z = 2j-2}. So P - T <= (K+1)/2 + D(t) + |S' n I|, and ceil(y/2) = (K+1)/2 + floor(d/2). By (S2)
|S' n I| <= ceil(d/2): done if d is even or D(t) = -1. If d is odd and D(t) = 0, the first element t+K = t+2j+1 (mod p) of I
is not in S' (by (c)), so |S' n I| <= floor(d/2).

(a)-(e) cover 0 <= y <= K+u (u-c < u+c < K). So the walk is a spread-k circuit code of length N in Q_n, and with section 1
K(n,k) = N. QED

## Checks

struct/ex4/p8/odd10.py p i: definition by all pairs + the upper bound of section 1 in exact integers: VALID / ok for
(p,i) = (9,0..2), (13,0..2), (17,0..1), (21,1), (25,1) and the list in p8/runs/odd10_check.out. struct/ex4/p8/lem16.py: residues,
S, (S1), (S2), the formulas for P and T against direct counts, D(t) = [t+2j in S] - 1, and every inequality of (a)-(e), all t,
all y (sampled for large N): ok for (9,1), (9,2), (13,1), (13,2), (17,1), (21,1).
How it was found: the solver codes with period 9, 13, 17 (p8/oddsh.py) all contain the chain p-3 -> c -> p-2 -> w; a scan
(p8/odd2p.py) showed that EVERY choice of w and of the excess at p-2 completes to a code when the other F residues are E
runs, and that for w = p-5 with excess u+c all dots can be antipodal.

## 5. Addendum: i = 0 (a short proof of Theorem 5, including l = 9)

**Theorem 36'.** The construction of section 2 with i = 0 (l = p = 4j+1 >= 9, k = (p^2-1)/2, u = p-1, N = 2p(p+1) = 4k+2l+2)
is also a spread-k circuit code. So K(n,k) = 4k+2l+2 at k = (l^2-1)/2 for every l = 1 (mod 4), l >= 9 (the upper bound is
section 1 with i = 0; Theorem 1 itself needs k > (l^2-1)/2). This is the statement of Theorem 5 (PROOF2 sec. 5), by a
different period-l code (ladder gaps K, K, K+u+c, K+u-c instead of family 1's K, K, K+1, N-3K-1), with a proof that includes
l = 9.

Proof. Sections 1-3 and the cases (a), (c), (d), (e) of section 4 never use i >= 1 (the sizes needed are K > u+c, true for
i = 0: (p^2+1)/2 > 6j-2; in (c) the interval lengths are 2j, 2j+2, p+(2j-3)). Only case (b) used u-c >= p+4. For i = 0,
u/2 = 2j, u-c = 2j+2, u+c = 6j-2, and case (b) is 2j+2 <= y < 6j-2. There T = 0, no point of residue 2j-5 is counted, a point
of S_E or of residue 2j-3 is counted only if z >= t+2j, and the two residues without threshold, 4j-2 and 2j-2, are 2j apart
(and p-2j = 2j+1 apart the other way), so at most one of their points lies in [t, t+2j). Hence, with I = [t+2j, t+y) and
S''' := S \ {(2j-5) mod p}:   P <= 1 + |S''' n I|.  I has length y-2j < 4j-2 < p, and the only two adjacent members of S''' are
2j-3, 2j-2 (S1), so |S''' n I| <= ceil((y-2j)/2) + 1. Therefore P <= ceil((y-2j)/2) + 2 <= ceil(y/2), because j >= 2. QED

(Checked: struct/ex4/p8/odd10.py p 0 VALID for p = 9, 13, 17; (*) for all t, y and the three inequalities of this case (b)
for p = 9, 13, .., 33 by a script, S171.)

## Referee report (#30, S171)

A fresh AI agent (own programs in theory/referee30/: gen.py, lem.py, res.py; the author's scripts not read): PASS, no
mathematical error in sections 1-4; three wording fixes (applied). Hand re-derivation for general j >= 2 and i >= 1, including
j = 2 where 2j-5 = p-1: every case correct, coverage complete. By program: the code rebuilt from the text, all pairs VALID for
(p,i) = (9,0..3), (13,0..3), (17,1..2), (21,1), (25,1), (29,1), (33,1); every formula and inequality of sections 3-4 for seven
(p,i), all t and y without sampling; the residue facts and D(t) for j = 2..399, i = 1..59; section 1 in exact arithmetic.
Section 5 (the addendum, written after the first report) was refereed by the same agent in a second round: PASS WITH FIXES
(two sentences reworded, applied); hand check of every use of i in sections 1-4 with i = 0 and of the new case (b); by program
(referee30/lem0.py): all pairs VALID for i = 0, p = 9..29, every formula and inequality for p = 9..33, all t, y.
NO HUMAN HAS READ THIS.
