# PROOF11 (S170, 2026-11-11): all multiples of family 7 — Theorem 27, and the combined statement

Notation as in PROOF9/PROOF10: spread-k circuit code ("coil") of length N in Q_n = closed walk v_0..v_{N-1} of distinct vertices with
d_H(v_i, v_j) >= min(k, cyclic distance(i,j)); K(n,k) = the maximum N; l = 2n-3k-1; Byrnes' value 4k+2l; excess e = N-4k-2l;
T_x = the coordinate flipped at step x (x in Z_N); K = k+1. Lemma 1, Lemma 2: PROOF.md.

## Theorem 27

Let q >= 1, lam = 8q+2, and let j >= 1 be ANY integer. Put

        k = j lam(lam+2)/4 - 1,       n = j (3 lam-2)(lam+4)/8,       l = 2n-3k-1 = j lam - 2j + 2.
Then
        K(n,k) = j lam(lam+4) = 4k + 2l + 4j.

j = 1 is Theorem 14 (PROOF7.md); for odd j the value is Theorem 20 (PROOF9.md), here with a different code; even j is new.
First new cases: K(98,59) = 280 (q=1, j=2, excess 8), K(196,119) = 560 (excess 16), K(286,179) = 792.

## Corollary 28 (combined with Corollary 23)

Let p >= 10 be even and j >= 1. Put k = j p(p+2)/4 - 1, n = j(3p-2)(p+4)/8 (so l = jp-2j+2; this is the Lemma-1 equality point
of excess e = 4j with u = l+(e-4)/2 = jp).
  * If p = 0, 2 or 4 (mod 8):  K(n,k) = j p(p+4) = 4k+2l+4j.     [p = 0 mod 4: Cor 23 with i = p/4 >= 3.  p = 2 mod 8: Thm 27.]
  * If p = 6 (mod 8):          there is no code of length 4k+2l+4j, so K(n,k) <= 4k+2l+4j-2.
                               [K = jp(p+2)/4 = 2u(t+1) for p = 8t+6, t >= 1: Theorem 17 excludes the length 4k+2l+4j; longer
                               codes are excluded by section 1 below with p in place of lam (it uses only k odd,
                               (p-4)(p-6) > 0 and (p-4)(p+2) > 0).]
(For p = 8 the first statement holds for odd j (Theorem 18) and is open for even j.)

Common notation: u = j lam, P = 2u (the period), K = j lam(lam+2)/4 = u(2q+1), N = 4K+2u = P(4q+3), e = 4j,
X = 2u-2, a = 4q, b = 2u-1-a.

Arithmetic:
 (a) K = u (mod P) (odd multiple of u), 2K = 0 (mod P), N/2 = 2K+u = u (mod P).      (b) K is even (lam is even); k is odd.
 (c) K >= 2u > X > b >= a+1, a >= 4, and K+2 > u.
 (d) eK = u(u+e/2)   [eK = 4j * j lam(lam+2)/4 = j^2 lam(lam+2) = j lam (j lam + 2j)].
 (e) n = (3k+l+1)/2, N = 4k+2l+e (direct substitution); n = j(6q+1)(4q+3).

## 1. Upper bound

Exactly as PROOF9 section 1, case "Thm 18", with p = lam and m = j (that computation uses only the formulas for k, l, e, u, K,
(d), k odd, and (lam-4)(lam-6) > 0, (lam-4)(lam+2) > 0): Lemma 2 gives N' <= 5k+3 for any coil (k - (3l-7) = j(lam-4)(lam-6)/4 > 0);
for N' = 4k+2l+e' with e < e' <= k+3-2l (e' even), Lemma 1 at L = 2K requires f(e') <= 0, but f(e) = 0 by (d) and
2f(e')-2f(e) = (e'-e)(2k+8-3l-e-e') > 0 since 2k+8-3l-e-e' >= k+5-l-e = j(lam-4)(lam+2)/4 + 2 > 0.

## 2. The code

Residues are taken mod P = 2 j lam. Let O1 = {lam*c : 0 <= c < j} and O2 = O1 + u = {lam*c : j <= c < 2j}. Every residue is
uniquely o + rho with o in O1 u O2 and -4q+4 <= rho <= 4q+5 (a window of lam consecutive values); we say the residue is of the
FIRST KIND if o is in O1 and of the SECOND KIND if o is in O2, and describe everything by rho. ev[x,y] / od[x,y] = the even / odd
integers in [x,y] (empty if x > y).

F residues and their gaps g = K + (excess):

  first kind:   excess 0:  rho in ev[-4q+4, -2]                 excess 1:  rho in {0} u ev[4, 4q-2] u {4q, 4q+1, 4q+3}
                excess X:  rho = 2                               excess b:  rho = 4q+4
  second kind:  excess a:  rho in ev[-4q+4, -2] u {3}            excess 0:  rho in {0, 4q+1, 4q+4}
                excess 1:  rho = 1                               excess b:  rho in od[5, 4q-1]         excess X:  rho = 4q+2

So F1 = ev[-4q+4, 4q-2] u {4q, 4q+1, 4q+3, 4q+4} (first kind) and F2 = ev[-4q+4, -2] u {0, 1, 3} u od[5, 4q-1] u {4q+1, 4q+2, 4q+4}
(second kind), 4q+2 residues each; F = (O1 + F1) u (O2 + F2), |F| = j(8q+4). All other residues are dots, with gaps

  first kind,  rho in od[1, 4q-1] u {4q+2}:   g = N/2+1   (set D+;  partner r+u+1, second kind with rho in ev[2,4q] u {4q+3})
  second kind, rho in ev[2, 4q] u {4q+3}:     g = N/2-1   (set D-)
  both kinds,  rho in od[-4q+5, -1] u {4q+5}: g = N/2     (partner r+u, same rho, other kind).

One window of the type word reads, for rho = -4q+4 .. 4q+5:
  first kind:   (F.)^(4q-2) FF. FF.               second kind:   (F.)^(2q-2) FF. (F.)^(2q-1) FF. F.
so the type word is H1^j H2^j with these two blocks (for j = 1 this is family 7's word); there are no two adjacent dots, no three
adjacent F's, and the adjacent F pairs are (4q, 4q+1), (4q+3, 4q+4) in each first-kind window and (0, 1), (4q+1, 4q+2) in each
second-kind window, each followed by a dot.

s(x) = x + g(x). On residues an F step adds u + excess (by (a)). For each o in O1 the following are 4-cycles of s on residues
(written residue: excess):

  B_o:    o: 1  ->  o+u+1: 1  ->  o+2: X  ->  o+u: 0  ->  o
  C_o:    o+4q: 1  ->  o+u+4q+1: 0  ->  o+4q+1: 1  ->  o+u+4q+2: X  ->  o+4q
  W_o:    o+u+4q+4: 0  ->  o+4q+4: b  ->  o+u+3: a  ->  o+4q+3: 1  ->  o+u+4q+4
  V_o,i:  o-2i: 0  ->  o+u-2i: a  ->  o+4q-2i: 1  ->  o+u+4q+1-2i: b  ->  o-2i             (i = 1, .., 2q-2)

(check: each excess sum is 2u: 1+1+X+0, 1+0+1+X, 0+b+a+1, 0+a+1+b; the residues and excesses agree with the table above, and
these j(2q+1) cycles cover F exactly once). So every F orbit of s in Z_N has 4 elements and gap sum 4K+2u = N. The dot pairs
r <-> r+u+1 (D+ with D-) and r <-> r+u have gap sums N. T_x = the orbit of x; every coordinate is used an even number of times,
so the walk closes. Number of coordinates: (N/P)(j(2q+1) + j*4q) = (4q+3) j (6q+1) = n.   (struct/ex4/fam7j.py q j.)

## 3. Reduction

All gaps are >= K, a window and its complement have the same odd coordinates, and windows of length <= k have distinct
coordinates. So it suffices to show odd(W) >= k for W = [t, t+L), K <= L <= N/2 = 2K+u. Write L = K+y, 0 <= y <= K+u.

Dots: the two positions are N/2-1, N/2 or N/2+1 apart; a dot occurs twice in W only if L = N/2, its forward gap is N/2-1 and
it starts at t. So the number of dots occurring twice is Dd(t,y) = [y = K+u and t mod P in D-].
F coordinates: three consecutive gaps sum to at least N-(K+X) = 3K+2 > N/2 (by (c)), so an F coordinate occurs at most 3 times,
and occurrences inside W are consecutive in the orbit (W is an interval shorter than N; the complementary arc is too long).
P = number of F chords (x, s(x)) in W, T = number of F triples (x, s(x), s^2(x)) in W:

        odd(W) = L - 2(P - T + Dd),     and the claim is

    (*)     P(t,y) - T(t,y) + Dd(t,y) <= floor((y+1)/2)        for all t, 0 <= y <= K+u       (then odd(W) >= K+y-2floor((y+1)/2) >= k).

For an F position f let e'(f) = excess of s^-1(f), e''(f) = e'(f) + e'(s^-1 f). From the cycles (rho-values; first / second kind):

  e' = 0:  first {0, 4q+1, 4q+4};  second ev[-4q+4, -2]          e' = 1:  first {2};  second {1, 4q+1, 4q+2, 4q+4} u od[5, 4q-1]
  e' = a:  first ev[4, 4q-2] u {4q+3}                             e' = b:  first ev[-4q+4, -2];  second {3}
  e' = X:  first {4q};  second {0}                                [the first elements of the pairs (4q,4q+1) and (0,1)]
  e'' = 1: first {4q+1, 4q+4};  second {1, 4q+2}                  [exactly the second elements of the four adjacent F pairs:
           C_o: 0+1 at o+4q+1 and 1+0 at o+u+4q+2;  W_o: 0+1 at o+4q+4;  B_o: 1+0 at o+u+1.  Every other e'' is >= 2.]

A chord starting at x lies in W iff t <= x and x+K+e(x) <= t+K+y-1; with m = x+e(x) = s(x)-K: iff m-e(x) >= t and m < t+y.
m runs over M := F-K = F+u (mod P), each point once:

    (1)     P(t,y) = #{ m in M n [t, t+y) :  m - e'(m+K) >= t }.

A triple starting at x lies in [t, t+2K+d) iff t <= x and f := x+e(x)+e(s x) <= t+d-1; f = s^2(x) (mod P) as 2K = 0 (mod P):

    (2)     T(t, K+d) = #{ f in F n [t, t+d) :  f - e''(f) >= t }      (d >= 1);        T = 0 for y <= K+1.

## 4. Proof of (*)

(A1) P(t,K) = K/2 for every t.
Let Xc(t) = #{x in F : x < t <= x+e(x)}. A point m = x+e(x) of M n [t,t+y) fails the condition of (1) iff x < t; and every x
counted in Xc(t) has m <= t-1+X, inside [t,t+y) once y >= X. So P(t,y) = |M n [t,t+y)| - Xc(t) for y >= X, in particular for
y = K (c). Now Xc(t+1)-Xc(t) = [t in F, e(t) >= 1] - #{x: x+e(x) = t, e(x) >= 1} = [t in F] - [t in M] (chords with e = 0 cancel), and
|M n [t+1,t+1+K)| - |M n [t,t+K)| = [t+K in M] - [t in M] = [t in F] - [t in M] (M+K = F+2K = F). So Xc(t) - |M n [t,t+K)| does not
depend on t. Summing over one period: sum_t Xc(t) = sum of e over F residues = j(2q+1) * 2u; sum_t |M n [t,t+K)| = K |F| = K j(8q+4).
The constant is ( j(2q+1)2u - K j(8q+4) )/P = j(2q+1)(2u-4K)/(2u) = -j(2q+1)(4q+1) = -K/2  (K = j(8q+2)(2q+1)). QED (A1)

(A2) X <= y <= K: P(t,K) - P(t,y) = |M n [t+y,t+K)| >= floor((K-y)/2), because M = F+u has no two adjacent non-members.
So P(t,y) <= K/2 - floor((K-y)/2) = ceil(y/2). T = Dd = 0.

(A3) 0 <= y <= X. T = Dd = 0. By (1) with f = m+K, t' = t+K, J = [t', t'+y):  P(t,y) = #{ f in F n J : f - e'(f) >= t' }.
Points with e' = X are never counted (f - X >= t' and f < t'+y need y > X). Let F° = F minus those points (first kind 4q,
second kind 0). In F° the adjacent member pairs are (4q+3, 4q+4) [first kind] and (4q+1, 4q+2) [second kind]; the adjacent
non-member pairs are (4q-1, 4q) [first kind] and (-1, 0) [second kind; i.e. the residues o-1, o for o in O2 -- for q = 1 the
value rho = -1 is rho = 4q+5 of the preceding window]. All of them start at an odd position (lam and u are
even, so position parity = parity of rho), and along the cycle they alternate: in each first-kind window -(4q-1,4q) then
+(4q+3,4q+4), in each second-kind window -(-1,0) then +(4q+1,4q+2).
Cut J into consecutive pairs {t',t'+1}, {t'+2,t'+3}, .. (the last possibly a single position, holding at most one member).
If t' is even every block holds at most one member of F°: P <= ceil(y/2). If t' is odd, a block holds two members iff it is
a + pair, none iff it is a full - pair, one otherwise; by the alternation |F° n J| <= ceil(y/2) + 1, with equality only if the
first special block meeting J is a full + pair. Then r = t' mod P is odd and lies after the preceding - pair:
  first kind, rho(r) = 4q+1 or 4q+3:  the point f of residue o+4q+3 is in J (the + pair is) and has e' = a = 4q >= 4 > 2 >= f-t':
                                      not counted.
  second kind, rho(r) in od[1, 4q+1]: f = t' itself is in F° (rho = 1, 3, od[5,4q-1], 4q+1) with e' = 1, b, 1, 1 >= 1: not counted.
So P <= ceil(y/2) = floor((y+1)/2).

(B) y = K+d, 1 <= d <= u. By (A1) and its formula for y >= X: P(t,K+d) = K/2 + |M n [t+K, t+K+d)| = K/2 + |F n I|, I = [t,t+d).
By (2), T >= #{f in F n I : e''(f) = 1, f-1 >= t}. So P - T <= K/2 + G with G = #{f in F n I : not(e''(f) = 1 and f-1 >= t)}.
Let F' = F minus the second elements of the adjacent F pairs (first kind 4q+1, 4q+4; second kind 1, 4q+2). F' has no two adjacent
members, so |F' n I| <= ceil(d/2). A point of F \ F' is counted in G only if it equals t; then t+1 is a dot (first kind 4q+2,
4q+5; second kind 2, 4q+3), so |F' n I| = |F' n [t+2,t+d)| <= ceil(d/2)-1 (for d = 1 the interval is empty and G = 1 = ceil(1/2)). In both cases G <= ceil(d/2), which gives (*) when
Dd = 0 (floor((K+d+1)/2) = K/2 + ceil(d/2), K even).
If Dd = 1: d = u (even; u/2 full blocks {t,t+1}, {t+2,t+3}, ..), and r = t mod P is in D-, i.e. second kind with
rho in ev[2,4q] u {4q+3}; r is not in F, so G = |F' n I|, and we need one block of I with no member of F':
  rho even, 2 <= rho <= 4q:  the block (4q+2, 4q+3) of the same second-kind window (even start; 4q+2 is removed from F', 4q+3 is
                             a dot); it lies at offsets 4q+2-rho, 4q+3-rho <= 4q+1 < u from t.
  rho = 4q+3 (t odd):        look at the NEXT window (a position at offset x from t has rho-value x+4q+3-lam there). If it is of the second kind: the block at offsets 4q, 4q+1 from t, i.e. rho = 1, 2 of the
                             next window (1 is removed from F', 2 is a dot; 4q is even and 4q+1 < u). If it is of the first kind
                             (t lies in the last second-kind window): the block at offsets lam-2, lam-1 from t, i.e. rho = 4q+1, 4q+2 of
                             the next window (4q+1 is removed from F', 4q+2 is a dot; lam-2 is even and lam-1 < u).
So G <= u/2 - 1 and P - T + Dd <= K/2 + u/2 = floor((K+u+1)/2).

(A1)-(A3), (B) give (*): the walk is a spread-k circuit code of length N = 4k+2l+4j in Q_n; with section 1, K(n,k) = N. QED

## 5. Remarks

* How found (S170): a design-level lazy SAT (struct/ex4/design4.py: one Boolean per ladder placement; a violated window gives the
  cut "not all ladders with two or more positions in it") found (98,59,280) designs in a second; restricted to ladders in pairs
  (r, r+lam) it solved q = 2, 3 as well, and the placements read off after rotating B to 0 were family 7's own ladders (PROOF7's
  L1, L2, C, E_j are B, C, W, V here), repeated at +lam. The same rule with j copies was then valid at the first try for every j.
* Machine checks: struct/ex4/lem7j.py tests every displayed set, table, identity and inequality of sections 2-4 for all t, y
  (runs/lem7j_*.out); snake/check.py VALID on codes/x8fam9_q1.txt (98,59,280), x8fam9_q2.txt (286,179,792), f7j_q1_j4.txt (196,119,560),
  f7j_q2_j4.txt (572,359,1584), f7j_q1_j6.txt (294,179,840).
* Status of the even-line equality points after Cor 28 (struct/ex4/eqtable2.py): for e = 4j with j squarefree, (E) forces j | u,
  so every equality point is (j, p) with u = jp, and all of them with p >= 10 are settled. Open: p = 8 with j even (u = 2e;
  first (66,39,192)), and for j not squarefree the points where j does not divide u (first e = 36).

## Referee report (#24, S170)

A fresh AI agent, from the text of section 2 only (theory/referee24/ref.py, sec1.py): Theorem 27 PASS (one wording fix: the pair
(-1,0) for q = 1), Corollary 28 PASS WITH FIXES (the p = 6 mod 8 bracket must also cite section 1 for longer codes); a cosmetic
note on d = 1 in (B). All applied. No mathematical error. Checks: all-pairs validity on vertices (minimum distance exactly k) and
every displayed item of sections 2-4 by brute force on the walk for (q,j) = (1,1..5), (1,7), (1,8), (2,1..4), (3,1), (3,2), (4,1), all y;
each equality and Dd sub-case occurs and the named blocks are pairing blocks inside I; section 1 in exact integers for q, j <= 14;
Corollary 28's substitutions for p = 10..198, j < 30.
