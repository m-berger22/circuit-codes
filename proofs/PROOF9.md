# PROOF9 (S170, 2026-11-11): circuit codes of UNBOUNDED excess over Byrnes' value, with K(n,k) determined exactly

Notation as in PROOF.md / PROOF6.md: a spread-k circuit code ("coil") of length N in Q_n is a closed walk v_0..v_{N-1} with
d_H(v_i, v_j) >= min(k, cyclic distance(i,j)); K(n,k) = the maximum N; the line of (n,k) is l = 2n-3k-1 (n = (3k+l+1)/2);
Byrnes' value is 4k+2l; the excess of a code is e = N-4k-2l. T_x = the coordinate flipped between v_x and v_{x+1}
(transition word, x in Z_N); K = k+1. Lemma 1 and Lemma 2 are those of PROOF.md.

## Theorem 18 (excess 4m)

Let p = 0 (mod 4), p >= 8, and let m >= 1 be ODD. Put

        k = m p(p+2)/4 - 1,      n = m (3p-2)(p+4)/8,      l = 2n-3k-1 = mp - 2m + 2.
Then
        K(n,k) = m p(p+4) = 4k + 2l + 4m.

## Theorem 19 (excess 8m)

Let p = 0 (mod 8), p >= 24, and let m >= 1 be ODD. Put

        k = m p(p+4)/8 - 1,      n = m (3p-4)(p+8)/16,     l = 2n-3k-1 = mp - 4m + 2.
Then
        K(n,k) = m p(p+8)/2 = 4k + 2l + 8m.

m = 1 in Theorem 18 is Theorem 13 (PROOF6.md). First new cases: K(99,59) = 288 (p=8, m=3, excess 12), K(165,99) = 480 (excess 20),
K(136,83) = 384 (Thm 19, p=24, m=1, excess 8), K(230,143) = 640, K(408,251) = 1152 (excess 24).
So the excess over Byrnes' formula is unbounded, and at all these (n,k) the exact value of K(n,k) is known.

Common notation: u = mp, h = p/2, e = the excess (4m resp. 8m), N = 4K+2u, X = 2u-2.

    Thm 18:  K = m p(p+2)/4,   N = m p(p+4),     e = 4m
    Thm 19:  K = m p(p+4)/8,   N = m p(p+8)/2,   e = 8m

Arithmetic used throughout (both cases):
 (a) K = h (mod p).  [Thm 18: p(p+2)/4 = p*(p/4) + p/2, times the odd m. Thm 19: p(p+4)/8 = p*(p/8) + p/2, times odd m.]
 (b) K is even.      [Thm 18: p = 4q gives K = m q (4q+2). Thm 19: p = 8q gives K = m q (8q+4).]
 (c) u/2 = mh = h (mod p) (m odd), N/4 = K + u/2 = 0 (mod p), N/2 = 2K+u = 0 (mod p), X = -2 (mod p).
 (d) K >= X = 2u-2 and K + 2 > u.   [Thm 18: K >= 2u iff (p+2)/4 >= 2. Thm 19: K >= 2u iff (p+4)/8 >= 2.]
 (e) e K = u(u + e/2).   [Thm 18: 4m * m p(p+2)/4 = m^2 p(p+2) = mp(mp+2m). Thm 19: 8m * m p(p+4)/8 = m^2 p(p+4) = mp(mp+4m).]
 (f) k is odd (by (b)), and n = (3k+l+1)/2, N = 4k+2l+e with the stated l (direct substitution).

## 1. Upper bound (both theorems)

Lemma 2 (k odd): a coil with k > 3l-7 has N <= 5k+3.
 Thm 18: k - (3l-7) = m(p(p+2)/4 - 3p + 6) = m(p-4)(p-6)/4 > 0.     Thm 19: k - (3l-7) = m(p(p+4)/8 - 3p + 12) = m(p-8)(p-12)/8 > 0.
So let N' = 4k+2l+e' be the length of a coil with e' > e; e' is even (N' is even: the cube is bipartite) and e' <= k+3-2l. Lemma 1 with L = 2K applies
(N' <= 5k+3 < 6K; N'/4 <= 2K; 2K <= N'-k as N' > 4k) and requires f(e') <= 0, where, with N'/2 - n = (k+l-1+e')/2,
4L-N' = 4k+8-2l-e', floor((L-k)/2) = (k+1)/2:

        2 f(e') = (k+l-1+e')(4k+8-2l-e') - (4k+2l+e')(k+1),       2f(e') - 2f(e) = (e'-e)(2k+8-3l-e-e').

f(e) = 0: in terms of K, u (l = u-(e-4)/2): k+l-1+e = K+u+e/2, 4k+8-2l-e = 4K-2u, 4k+2l+e = 4K+2u, so
2f(e) = (K+u+e/2)(4K-2u) - (4K+2u)K = 2eK - 2u^2 - eu = 0 by (e).
The second factor: 2k+8-3l-e-e' >= k+5-l-e, and
 Thm 18: k+5-l-e = m(p-4)(p+2)/4 + 2 > 0.          Thm 19: k+5-l-e = m(p-8)(p+4)/8 + 2 > 0.
Hence f(e') > 0 for every admissible e' > e: no coil is longer than 4k+2l+e.

## 2. The codes: residue designs

A DESIGN of period p is a partition of Z_p into five sets S0, S1, SX, E, D. It defines a gap function on Z_N (N is a multiple
of p by (c)) depending only on r = x mod p:

    r in S0: g = K      r in S1: g = K+1      r in SX: g = K+X = N-3K-2      r in E: g = N/4      r in D: g = N/2,

and s(x) = x + g(x). On residues s acts as r -> r+h (S0), r+h+1 (S1), r+h-2 (SX), r (E and D), by (a), (c).

DESIGN 6 (Theorem 18; p = 0 mod 4, p >= 8):
    S0 = {1},   S1 = {h, h+1},   SX = {2},
    E  = {even r, 4 <= r <= h-2} u {odd r, h+3 <= r <= p-1}          (|E| = h-3),
    D  = the rest = {0, 3} u {odd r, 5 <= r <= h-1} u {even r, h+2 <= r <= p-2}     (|D| = h-1).
  s on residues: 1 -> h+1 -> 2 -> h -> 1 (one "ladder", gap excesses over K: 0, 1, X, 1).

DESIGN 8 (Theorem 19; p = 0 mod 8, p >= 24):
    S0 = {2, h+4, h+9},   S1 = {0, 4, 8, 9, h+1, h+5},   SX = {6, h+2, h+10},
    E  = {odd r, 11 <= r <= h-1} u {h+7} u {even r, h+12 <= r <= p-2}       (|E| = h-10),
    D  = the rest                                                             (|D| = h-2).
  s on residues: three ladders
      A:  0 -> h+1 -> 2 -> h+2 -> 0       (excesses 1, 1, 0, X)
      B:  4 -> h+5 -> 6 -> h+4 -> 4       (excesses 1, 1, X, 0)
      C:  8 -> h+9 -> 9 -> h+10 -> 8      (excesses 1, 0, 1, X)
  i.e. the three cyclic orders of (1, 1, 0, X).

In both designs s permutes the ladder residues in 4-cycles whose gap sum is 4K + X + 2 = N, and fixes the residues in E and D.
So s is a permutation of Z_N with orbits of size 4 (ladder coordinates; consecutive gaps as listed), of size 4 with all
gaps N/4 (E), and of size 2 with gaps N/2 (D, "dots"). Let T_x = the orbit of x. Every coordinate is used an even number of
times, so the walk closes. Number of coordinates, with N/p positions per residue:
 Design 6: (N/p)(4/4 + (h-3)/4 + (h-1)/2) = m(p+4)(3p-2)/8 = n.     Design 8: (N/p)(12/4 + (h-10)/4 + (h-2)/2) = (m(p+8)/2)(3p-4)/8 = n.
(Generators: struct/ex4/fam6m.py p m; struct/ex4/fam8.py for m = 1; struct/ex4/lem9.py builds both for any odd m.)

## 3. Reduction to a counting statement (both designs)

All gaps are >= K, so a window of length <= k has distinct coordinates. Every coordinate is used an even number of times, so
a window and its complement have the same set of odd coordinates; it suffices to show odd(W) >= k for every window
W = [t, t+L) with K <= L <= N/2 = 2K+u. Write L = K+y, 0 <= y <= K+u.

Multiplicities in such a window. A dot occurs at most once (L <= N/2). An E coordinate occurs at most twice (three positions
span N/2+1 > L). A ladder coordinate occurs at most 3 times: four positions span at least N - (K+X) + 1 = 3K+3 > 2K+u >= L by (d).
It occurs 3 times only as x, s(x), s^2(x) with g(x) + g(s(x)) <= L-1 <= 2K+u-1; a pair containing the gap K+X has sum
>= 2K+2u-2 > 2K+u-1, so both gaps are in {K, K+1}. Let T1 = {residues x: g(x)+g(s(x)) = 2K+1}, T2 = {.. = 2K+2}
(no ladder has two consecutive gaps K):

    Design 6:  T1 = {1, h},                    T2 = {}
    Design 8:  T1 = {8, h+1, h+4, h+9},        T2 = {0, 4}.

For a set S of residues let |S n [a,b)| = the number of integers x in [a,b) with x mod p in S (0 if b <= a).
Let P(W) = number of chords (x, s(x) both in W) and T(W) = number of triples. A coordinate occurring twice contributes one
chord, one occurring three times two chords and one triple, so odd(W) = L - 2(P - T), and the claim is

    (*)     P(t,y) - T(t,y) <= floor((y+1)/2)      for all t and all 0 <= y <= K+u

(then odd(W) >= K+y-2 floor((y+1)/2) >= K-1 = k).

(A coordinate occurring exactly twice in W does so at orbit-consecutive positions x, s(x) with the arc from x to s(x) inside W:
W is an interval and contains one of the two arcs between the positions; the other arc has N-g+1 >= N/2+1 > L positions when g <= N/2,
and for the long ladder gap g = K+X the complementary arc of span N-g = 3K+2 > L does not fit either. So chords never wrap.)
A chord of length K+c starting at x lies in W iff t <= x < t+y-c; a triple of span 2K+c iff t <= x < t+y-K-c. Dots give no
chord. Hence (N/4 = K + u/2):

    P(t,y) = |S0 n [t,t+y)| + |S1 n [t,t+y-1)| + |E n [t,t+y-u/2)| + |SX n [t,t+y-X)|,
    T(t,y) = |T1 n [t,t+y-K-1)| + |T2 n [t,t+y-K-2)|.

Shift each class so that its strip ends at t+y. By (c) the shifts are 1, h, -2 on residues. Put

    D1 = S1 + 1,     E' = E + h,     MX = SX - 2,     M = S0 u D1 u E' u MX     (a disjoint union, see the lists below),

    (1)   P(t,y) = |M n [t,t+y)| - R(t,y),
          R(t,y) = [y >= 1 and t in D1] + |E' n [t, t+min(y, u/2))| + |MX n [t, t+min(y, X))|.

    Design 6:  D1 = {h+1, h+2},  MX = {0},  E' = {odd r, 3 <= r <= h-1} u {even r, h+4 <= r <= p-2},
               M  = {0, 1} u {odd 3..h-1} u {h+1, h+2} u {even h+4..p-2}                                   (|M| = h+1)
    Design 8:  D1 = {1, 5, 9, 10, h+2, h+6},  MX = {4, h, h+8},  E' = {7} u {even r, 12 <= r <= h-2} u {odd r, h+11 <= r <= p-1},
               M  = {1, 2, 4, 5, 7, 9, 10} u {even 12..h-2} u {h, h+2, h+4, h+6, h+8, h+9} u {odd h+11..p-1}  (|M| = h+2)

Facts about M (read off the lists; Z1 := T1 + h):
    (M-a)  M has no two cyclically adjacent NON-members.
    (M-b)  Z1 is contained in M; M'' = M \ Z1 has no two cyclically adjacent MEMBERS; and for every z in Z1, z-1 is not in M''.
           Design 6: Z1 = {h+1, 0} (= 1+h, h+h);  z-1 = h, p-1 are non-members;  M'' = {1} u {odd 3..h-1} u {h+2} u {even h+4..p-2}.
           Design 8: Z1 = {1, 4, 9, h+8};  M'' = {2, 5, 7, 10} u {even 12..h-2} u {h, h+2, h+4, h+6, h+9} u {odd h+11..p-1};
                     z-1 = 0, 3, 8, h+7 are non-members.
    (M-c)  M' = M \ MX.
           Design 6: M' = {1} u {odd 3..h-1} u {h+1, h+2} u {even h+4..p-2}; the only adjacent members are (h+1, h+2), the
                     only adjacent non-members are (p-1, 0).
           Design 8: M' = {1, 2, 5, 7, 9, 10} u {even 12..h-2} u {h+2, h+4, h+6, h+9} u {odd h+11..p-1}. The pairs
                     (o, o+1) with o ODD: both members only for o = 1 and o = 9; both non-members only for o = 3, o = h-1 and o = h+7.
                     The only adjacent members of M' are (1,2) and (9,10) (so no pair starting at an EVEN residue has two members).

## 4. Proof of (*)

Write K = a p + h (by (a)); a = (m(p+2)-2)/4 in Design 6 and (m(p+4)-4)/8 in Design 8.

(A1) y = K: P(t,K) = K/2 for every t (and T = 0).
|M n [t,t+K)| = a|M| + |M n [t,t+h)|.  In R(t,K): min(K, u/2) = u/2 = ((m-1)/2) p + h, so the E' term is
((m-1)/2)|E| + |E' n [t,t+h)|; min(K, X) = X = 2mp - 2 by (d), and [t, t+2mp-2) is 2m full periods minus the two positions
t-2, t-1, so the MX term is 2m|MX| - c(t), c(t) = |MX n {t-2, t-1}|. With M0 = M \ E' = S0 u D1 u MX and d(t) = [t in D1]:

        P(t,K) = a|M| - ((m-1)/2)|E| - 2m|MX| + ( |M0 n [t,t+h)| - d(t) + c(t) ).

Claim: |M0 n [t,t+h)| - d(t) + c(t) = 2|MX| for every t.
 Design 6: M0 = {0, 1, h+1, h+2}, d = [t in {h+1,h+2}], c = [t in {1, 2}] (residues r = t mod p in [1,p]):
   r = 1: 1-0+1;  r = 2: 1-0+1;  3 <= r <= h: 2-0+0;  r = h+1: 3-1+0;  r = h+2: 3-1+0;  h+3 <= r <= p: 2-0+0.   Always 2.
 Design 8: M0 = A u (B+h) with A = {1,2,4,5,9,10}, B = {0,2,4,6,8,9}, both inside [0,h) (h >= 12). For 0 <= r < h:
   |M0 n [r, r+h)| = |A n [r,h)| + |B n [0,r)| =: w(r), and |M0 n [h+r, h+r+h)| = |A n [0,r)| + |B n [r,h)| = 12 - w(r).
        r     0  1  2  3  4  5  6  7  8  9  10  11..h-1
        w(r)  6  7  6  6  6  6  5  6  6  7  7   6
   d(t) = 1 for t in {1, 5, 9, 10, h+2, h+6}; c(t) = 1 for t in {5, 6, h+1, h+2, h+9, h+10} (MX+1 and MX+2).
   t = r:   w - d + c = 6 for every r (r=1: 7-1; r=5: 6-1+1; r=6: 5+1; r=9, 10: 7-1).
   t = h+r: 12 - w - d + c = 6 for every r (r=1: 5+1; r=2: 6-1+1; r=6: 7-1; r=9, 10: 5+1).                    Always 6.
So P(t,K) = a|M| - ((m-1)/2)|E| - 2m|MX| + 2|MX|, and this equals K/2 = a h + h/2:
 Design 6: a(h+1) - (m-1)(h-3)/2 - 2m + 2 - ah - h/2 = [m(p+2) - 2 - (m-1)(p-6) - 8m + 8 - p]/4 = 0.
 Design 8: a(h+2) - (m-1)(h-10)/2 - 6m + 6 - ah - h/2 = [m(p+4) - 4 - (m-1)(p-20) - 24m + 24 - p]/4 = 0.
T(t,K) = 0 since the strips [t, t+y-K-c) are empty.  QED (A1)

(A2) X <= y <= K. R(t,y) does not depend on y in this range (y >= X >= u/2 >= 1), so by (1) and (A1)
P(t,K) - P(t,y) = |M n [t+y, t+K)| >= floor((K-y)/2) by (M-a). Hence P(t,y) <= K/2 - floor((K-y)/2) = ceil(y/2); T = 0.

(A3) 0 <= y <= X. The MX term of R is |MX n [t,t+y)|, so P(t,y) = |M' n J| - R'(t,y), J = [t,t+y),
R'(t,y) = [y >= 1 and t in D1] + |E' n [t, t+min(y, u/2))|; T = 0.
Cut J into consecutive pairs {t,t+1}, {t+2,t+3}, .. (ceil(y/2) blocks; the last may be a single position). Then
|M' n J| <= ceil(y/2) + (number of blocks with two members) - (number of full blocks with no member).
If t is even, the full blocks start at even residues (p is even) and by (M-c) none has two members: P <= ceil(y/2).
If t is odd, call a block special if it is a pair (o, o+1) of (M-c).
 Design 6: the specials are +(h+1,h+2) and -(p-1,0); they alternate along Z, so (two-member blocks) - (full no-member blocks)
   <= 1, with equality only if the first special block met by J is a full block (h+1, h+2). Then r = t mod p is odd,
   1 <= r <= h+1, and y >= h+3-r. In that case R' >= 1: r = h+1: t in D1; 3 <= r <= h-1: t in E'; r = 1: t+2 = 3 in E'
   (3 <= h-1) and t+2 < t+min(y, u/2) since y >= h+2 and u/2 >= h >= 4.
 Design 8: the specials in cyclic order are +(1,2), -(3,4), +(9,10), -(h-1,h), -(h+7,h+8). Along Z the running value of
   (two-member blocks) - (full no-member blocks) is therefore at most 1 [starting from +(1,2): 1,0,1,0,-1,0,-1,..; from +(9,10):
   1,0,-1,0,-1,..; from a - block: <= 0 throughout; a block cut to a single position is the last block of J, holds at most one member and is not counted], and it
   reaches 1 only if the first special block met by J is a full +(1,2) or a full +(9,10).
   First special = (1,2): r = t mod p is odd and lies after h+7, i.e. r in {h+9, h+11, .., p-1} or r = 1.
       r = 1: t in D1.   r odd in [h+11, p-1]: t in E'.   r = h+9: t+2 = h+11 is in E' (h+11 <= p-1 as h >= 12), and
       t+2 < t+min(y, u/2) because J contains the block (p+1, p+2), so y >= h-6 >= 6, and u/2 >= h.
   First special = (9,10): r in {5, 7, 9}.  r = 5, 9: t in D1.  r = 7: t in E'.
   So R' >= 1 whenever the value 1 is reached.
Hence P(t,y) <= ceil(y/2) = floor((y+1)/2).

(B) K < y <= K+u. Put d = y-K in [1, u], s = t+K, I = [s, s+d). R is constant for y >= X, so by (1) and (A1)
P(t,y) = K/2 + |M n I|. By (a), T(t,y) >= |T1 n [t, t+d-1)| = |Z1 n [s, s+d-1)|. Since Z1 is a subset of M,
        |M n I| - |Z1 n [s,s+d-1)| = |M'' n I| + [s+d-1 in Z1].
By (M-b) |M'' n I| <= ceil(d/2). If the last position s+d-1 of I is in Z1, then s+d-1 and s+d-2 are both non-members of M'',
so |M'' n I| <= ceil((d-2)/2) = ceil(d/2) - 1 (for d = 1: |M'' n I| = 0 and 0 + 1 = ceil(1/2)).
In both cases P - T <= K/2 + ceil(d/2) = floor((K+d+1)/2) = floor((y+1)/2), as K is even.

(A1)-(A3), (B) give (*) for all 0 <= y <= K+u: the walks of section 2 are spread-k circuit codes of length N = 4k+2l+e in Q_n.
With section 1, K(n,k) = N. QED (Theorems 18, 19)

## 5. Remarks

* Why m must be odd: for even m, K = 0 (mod p), the ladders do not close (and Theorem 17 of PROOF8 excludes equality codes with 2u | K).
* Both families attain equality in Lemma 1 at L = 2K ((e) is condition (E) of PROOF8 sec. 4), with type-word period p,
  a proper divisor of the forced period gcd(2K, N) = u when m > 1.
* How found (S170): one SAT code (136,83,384) (S169) -> its three ladders are the three cyclic orders of (1,1,0,X) -> guessed
  residue rule, confirmed by lazy SAT at p = 32, 40, then built directly. A "design-level" search (struct/ex4/design.py: L ladders
  of those three types + N/4 coordinates + antipodal dots, filtered by (M-a)) at excess 12 returned the family-6 design of period 8
  at (99,59,288): the same residue design with K and N multiplied by 3.
* Machine checks: struct/ex4/lem9.py tests every displayed identity and inequality of sections 1-4 for all t, y
  (Design 6: p = 8..40, m = 1..7; Design 8: p = 24..56, m = 1..5; see struct/ex4/runs/lem9_*.out); snake/check.py (independent
  validator) VALID on (99,59,288), (204,125,576), (165,99,480), (230,143,640), (348,219,960), (490,311,1344).

## 6. Theorem 20: the same statement for p = 2 (mod 8)   (added after referee report #19; refereed separately, see below)

**Theorem 20.** Let p = 8q+2, q >= 1, and let m >= 1 be odd. With k = m p(p+2)/4 - 1, n = m(3p-2)(p+4)/8 (the formulas of
Theorem 18; l = 2n-3k-1 = mp-2m+2):   K(n,k) = m p(p+4) = 4k+2l+4m.
m = 1 is Theorem 14 (PROOF7.md). First new cases: K(147,89) = 420 (p=10, m=3, excess 12), K(245,149) = 700, K(429,269) = 1188.

**Corollary 21.** Let m be odd, p >= 8 even, k = m p(p+2)/4 - 1, n = m(3p-2)(p+4)/8, l = mp-2m+2 (the Lemma-1 equality point
of excess e = 4m with u = l+(e-4)/2 = mp; for m not squarefree there are further equality points of excess 4m, with u not a
multiple of m, e.g. e = 36, u = 120: not covered). A spread-k circuit code of length 4k+2l+4m in Q_n exists if and only if p is not
6 (mod 8). [p = 0 mod 4: Theorem 18. p = 2 mod 8: Theorem 20. p = 8j+6: K = m p(p+2)/4 = 2u(j+1) is a multiple of 2u and
K >= 2u+2, so Theorem 17 (PROOF8) excludes it.]

Proof of Theorem 20. Notation of this file: u = mp, K = m p(p+2)/4, N = 4K+2u = m p(p+4), e = 4m, X = 2u-2.
Upper bound: section 1 above, case "Thm 18", used only these formulas, (e), k odd, (p-4)(p-6) > 0 and (p-4)(p+2) > 0; here
K = m(8q+2)(2q+1) is even, so k is odd, and p >= 10.

The code. Take PROOF7.md section 2 with l := p (so PROOF7's period is P = 2p = 16q+4, and h = p/2-1 = 4q), with the same
residue sets (F residues by excess class, dot residues and dot partners), and replace the VALUES

    K -> mK_7 = K,    N -> N (so N/2 = 2K+u),    w = 2p-2  ->  w = X = 2u-2,    b = 3p/2  ->  b = 2u-1-h = 2u - p/2,

keeping the excesses 0, 1 and h = p/2-1 and the dot gaps N/2+1, N/2, N/2-1. (For m = 1 this is PROOF7's code.)
Residues are unchanged: K = p (mod 2p) because K = p * m(p+2)/4 and m(p+2)/4 = m(2q+1) is odd; N/2 = 2K+mp = p (mod 2p);
w = -2 and b = -p/2 = 3p/2 (mod 2p) since 2u = 0 (mod 2p). So s(x) = x+g(x) acts on residues mod 2p exactly as in PROOF7:
the same 4-cycles L1, L2, C, E_j and dot pairs. Each 4-cycle has excess sum 2u (L1, L2: 0+1+1+w; C, E_j: 0+b+h+1), i.e. gap
sum 4K+2u = N, and each dot pair has gap sum N. Number of coordinates: (N/2p)((p+2)/4 + (p-2)/2) = (m(p+4)/2)(3p-2)/4 = n.
(struct/ex4/fam7m.py q m 0.)

Validity (as in PROOF7: windows with L < K have distinct coordinates, and (*) gives odd(W) >= k): PROOF7 sections 3-4 go through with l replaced by u in the window range (K <= L <= N/2 = 2K+u, 0 <= y <= K+u,
1 <= d <= u in (B)) and the new values of w, b; residue sets, e', e'' tables (with the new values w, b) and the sets D^-, F°, F'
are unchanged. The points where a value enters:
 * All gaps >= K; three consecutive F gaps sum to at least N-(K+w) = 3K+2 > 2K+u = N/2 since K+2 > u (K >= 2u as (p+2)/4 >= 2).
   Dots occur twice only if L = N/2, forward gap N/2-1, start t: Dd(t,y) = [y = K+u and t mod 2p in D^-].
 * (1), (2): unchanged (2K = 0 mod 2p). T = 0 for y <= K+1.
 * (A1): needs K >= w = max excess (b < w as h > 1) - true - and gives P(t,y) = |M n [t,t+y)| - X(t) for y >= w with
   X(t) - |M n [t,t+K)| constant; sum over one period (2p residues): sum_t X(t) = (number of 4-cycles)(2u) = ((p+2)/4)(2u),
   sum_t |M n [t,t+K)| = K(p+2); constant = (u(p+2)/2 - K(p+2))/(2p) = (p+2)(2u-4K)/(8p) = -m(p+2)p/8 = -K/2. So P(t,K) = K/2.
 * (A2): w <= y <= K, unchanged (M = F+p has no two adjacent non-members).
 * (A3): 0 <= y <= w. Points with e' = w are never counted. The block argument is about the periodic set F° and holds for
   any length of J (over several periods the count is <= #blocks + #two-member blocks - #full no-member blocks, and the two kinds alternate). The uncounted member in the equality case: r = 1 or 3: the point of residue 3 has e' = h = 4q >= 4 > 3-r
   (h is unchanged); r = p+1: e' = 1; 4q+3 <= r <= p-1 odd: f = t' has e' >= 1 (e' = 1 or b). Unchanged.
 * (B): y = K+d, 1 <= d <= u. P(t,K+d) = K/2 + |F n I|, I = [t,t+d); T >= #{f in F n I: e''(f) = 1, f-1 >= t} (e'' = 1 exactly
   at the second elements of the four FF pairs, as the excesses 0, 1 are unchanged and h, b, w >= 2); G <= ceil(d/2) as in
   PROOF7, for any d. If Dd = 1: d = u (even, u/2 full blocks {t,t+1}, ..), r = t mod 2p in D^-; a block with no member of F'
   exists as in PROOF7 within the first p positions of I (r in ev[4q+4, p]: the block (p+2, p+3); r = p+3: the block
   (t+p-2, t+p-1) = (1, 2) mod 2p), and u >= p. So G <= u/2-1 and P-T+Dd <= K/2+u/2 = floor((K+u+1)/2) (K, u even).
QED

Machine check: struct/ex4/lem9b.py (PROOF7's step-by-step test with m; q = 1..3, m = 1..5 and more in runs/lem9b.out).
Remark: for even m the construction fails (K = 0 mod 2p: the orbits do not have gap sum N). Numerically the wide-ladder excess h may also be replaced by h + 2pJ (b = 2u-1-h-2pJ) for J up to about m/2
(fam7m.py q m J); only J = 0 is claimed and proved.

## Referee report (#20, S170) on section 6

A fresh AI agent (own generator from PROOF7 sec. 2 + the replacements above, own all-pairs checker; theory/referee20/): Theorem 20
PASS, Corollary 21 PASS with one wording fix (other equality points for non-squarefree m; applied) and three nits (applied).
Checks: all-pairs validity for (p,m) = (10,1..7), (18,1..5), (26,1), (26,3); even m is not a code; every step of PROOF7 sec. 3-4
with the new values by brute force over ~340,000 windows ((10,1..11), (18,1..5), (26,1), (26,3), (34,1)); section 1 in exact
integers for q = 1..119, m < 60; Theorem 17's hypotheses for p = 8j+6, j >= 1.

## Referee report (#19, S170)

A fresh AI agent, working from this text only (own generator and all-pairs checker, theory/referee19/gen.py, check_code.py,
check_ids.py, sec1.py, mutate.py): PASS for Theorem 18 and PASS for Theorem 19, no error found; five one-line omissions
(parity of e', chords never wrap, twice-occurring ladder coordinates are orbit-consecutive, the last step (*) => odd >= k, cut
two-member block) were added to the text afterwards. Its checks: definition by all pairs on vertices for Design 6
(p,m) = (8,1..7), (12,1..5), (16,1..5), (20,1), (20,3), (24,3) and Design 8 (24,1..5), (32,1), (32,3), (40,1), (40,3), (48,1); even m and
p below the stated ranges are INVALID (no partition / walk does not close); every displayed identity of sections 2-4 with P, T
counted directly on the walk (70 runs, Design 6 p = 8..48, m up to 11; Design 8 p = 24..80, m up to 7); section 1 in exact
integers for Design 6 p = 8..300, Design 8 p = 24..600, m = 1..39.
