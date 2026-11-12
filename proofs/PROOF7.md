# PROOF7 (S169, 2026-11-11 night): excess-4 codes on the lines l = 2 (mod 8) -- family 7

Notation as in PROOF6.md (which treats l = 0 mod 4): spread-k circuit code of length N in Q_n, K(n,k) the maximum length,
l = 2n-3k-1, K = k+1, T_x = coordinate flipped at step x (x in Z_N).

## Theorem 14

Let l = 8q+2, q >= 1, k = (l^2+2l-4)/4, n = (3k+l+1)/2. Then

        K(n,k) = 4k + 2l + 4 = l(l+4).

First cases: K(49,29) = 140, K(143,89) = 396, K(285,181) = 780.
With Theorem 13: K(n,k) = 4k+2l+4 at k = (l^2+2l-4)/4 for every even l >= 8 with l = 0, 2 or 4 (mod 8); open: l = 6 (mod 8).

## 1. Upper bound

As in PROOF6 section 1, which uses only that l is even, k = (l^2+2l-4)/4 is odd (l = 2m with m odd gives k = m^2+m-1),
and k > 3l-7, k+1-l > 0 (true for l >= 10): Lemma 2 gives N <= 5k+3, and Lemma 1 at L = 2K excludes N = 4k+2l+e for 6 <= e <= k+3-2l because
2f(e) - 2f(4) = (e-4)(2k+4-3l-e) > 0 and f(4) = 0.

## 2. The code

K = l(l+2)/4 = (8q+2)(2q+1) is even, N = l(l+4) = 4K+2l, N/2 = 2K+l. Put p = 2l = 16q+4; p divides N (N/p = (l+4)/2 = 4q+3). Then K = l (mod p) (K = p*q + l)
and N/2 = l (mod p). Put  h = l/2-1 = 4q,  b = 3l/2 = 12q+3,  w = 2l-2 = 16q+2.
The code is invariant under x -> x+p; the gap g(x) depends on r = x mod p in [0, p). Write ev[a,b] / od[a,b] for the even / odd
integers in [a,b].

F residues and their gaps g = K + e:

    e = 0:  r in {4q+2, l+1, l+4}  u  ev[l+6, 12q+2]
    e = 1:  r in {0, 1, 3, 4q+3, 12q+4}  u  ev[12q+8, 16q+2]
    e = h:  r in ev[6, 4q]  u  {4q+5}
    e = b:  r in {4}  u  od[4q+7, 8q+1]
    e = w:  r in {l+2, 12q+6}

so  F = {0,1,3,4} u ev[6,4q] u {4q+2, 4q+3} u od[4q+5, 8q+1] u {l+1, l+2} u ev[l+4, 2l-2]   (|F| = l+2).
All other residues are dots (|D| = l-2), with gaps

    r = 2:              g = N/2+1   (partner l+3, which gets N/2-1)
    r in od[5, 4q+1]:   g = N/2     (partner r+l, also N/2)
    r in ev[4q+4, l]:   g = N/2-1   (partner r+l-1, which gets N/2+1).

(One period reads  FF. FF. (F.)^(2q-2) FF. (F.)^(2q-1) FF. (F.)^(4q-1);  there are no two adjacent dots, and the only adjacent
F's are the four pairs (0,1), (3,4), (4q+2,4q+3), (l+1,l+2), each followed by a dot.)

s(x) = x+g(x) is a permutation of Z_N. On F residues (mod p) it consists of the 4-cycles

    L1:  4q+2 -> 12q+4 -> 4q+3 -> 12q+6 -> 4q+2            e = (0, 1, 1, w)
    L2:  l+1 -> 1 -> l+2 -> 0 -> l+1                        e = (0, 1, w, 1)
    C :  l+4 -> 4 -> 4q+5 -> 3 -> l+4                       e = (0, b, h, 1)
    E_j: l+6+2j -> 6+2j -> 12q+8+2j -> 4q+7+2j -> l+6+2j    e = (0, h, 1, b),   j = 0, .., 2q-3

(each step adds K+e = l+e mod p), and every cycle has e-sum 2l, i.e. gap sum 4K+2l = N: every F orbit of s in Z_N has exactly 4
elements. On dots: 2 <-> l+3, r <-> r+l (r in od[5,4q+1]), r <-> r+l-1 (r in ev[4q+4,l]) are disjoint pairs covering all dot
residues (od[5,4q+1]+l = od[l+5, 12q+3], ev[4q+4,l]+l-1 = od[12q+5, 2l-1]), and the two gaps of a pair sum to N: orbits of 2 elements.
T_x = the orbit of x. Number of coordinates: (N/p) * ((l+2)/4 + (l-2)/2) = ((l+4)/2)(3l-2)/4 = n.
(struct/ex4/ex4fam7.py builds the code.)

## 3. Reduction

All gaps are >= K, and a window and its complement have the same odd coordinates, so it suffices to show odd(W) >= k for
W = [t, t+L), K <= L <= N/2 = 2K+l (a complement of length <= k has distinct coordinates). Write L = K+y, 0 <= y <= K+l.

Multiplicities in W. Dots: the two positions are N/2-1, N/2 or N/2+1 apart, so a dot occurs twice only if L = N/2, its
forward gap is N/2-1 and it starts at t. The dot residues with forward gap N/2-1 are D^- = ev[4q+4, l] u {l+3}. So the number
of dots occurring twice is  Dd(t,y) = 1 if y = K+l and t mod p in D^-, and 0 otherwise.
F coordinates: three consecutive gaps sum to at least N - (K+w) = 3K+2 > N/2, so an F coordinate occurs at most 3 times,
and 3 times iff W contains x, s(x), s^2(x) for some x.
Let P = number of F chords (x, s(x)) inside W and T = number of F triples (x, s(x), s^2(x)) inside W (occurrences of a
coordinate inside a window shorter than N are consecutive in its orbit: a coordinate occurring twice contributes one chord,
one occurring three times two chords and one triple). Then

        odd(W) = L - 2 (P - T + Dd),

and the claim is

    (*)     P(t,y) - T(t,y) + Dd(t,y) <= floor((y+1)/2)      for all t, 0 <= y <= K+l.

For an F position f let  e'(f) = e(s^-1 f)  and  e''(f) = e(s^-1 f) + e(s^-2 f)  (the excesses of the one / two gaps before f).
From the cycles:

    e' = 0:  f in {1, 4, 12q+4} u ev[6,4q]            e' = 1:  f in {4q+3, 12q+6, l+1, l+2, l+4} u od[4q+7, 8q+1]
    e' = h:  f in {3} u ev[12q+8, 16q+2]              e' = b:  f in {4q+5} u ev[l+6, 12q+2]          e' = w:  f in {0, 4q+2}
    e'' = 1: f in {1, 4, 4q+3, l+2}   (exactly the second elements of the four FF pairs).

A chord starting at x lies in W iff t <= x and x+K+e(x) <= t+K+y-1, i.e. iff the point m = x+e(x) satisfies t <= m-e(x) and
m < t+y. Here m = s(x) - K, so m runs over M := F - K = F + l (mod p), each point once, and

    (1)     P(t,y) = #{ m in M n [t, t+y) :  m - e'(m+K) >= t }.

Likewise a triple starting at x lies in W = [t, t+2K+d) iff t <= x and x + e(x) + e(s x) <= t+d-1; the point f = x+e(x)+e(s x)
is congruent to s^2(x) mod p (2K = 0 mod p), so

    (2)     T(t, K+d) = #{ f in F n [t, t+d) :  f - e''(f) >= t }          (d >= 1)

(x -> f is a bijection onto the F positions, as in (1)); T = 0 for y <= K+1, since e'' >= 1.

## 4. Proof of (*)

(A1) P(t,K) = K/2 for every t.
Let X(t) = #{x in F : x < t <= x+e(x)}. A point m = x+e(x) of M n [t,t+y) fails the condition of (1) iff x < t; conversely
every x counted in X(t) has m = x+e(x) <= t-1+w, which is in [t, t+y) as soon as y >= w. So
P(t,y) = |M n [t,t+y)| - X(t) for y >= w  (and K >= w: K = (8q+2)(2q+1)). Now
X(t+1) - X(t) = [t in F, e(t) >= 1] - #{x : x+e(x) = t, e(x) >= 1} = [t in F] - [t in M] (the chords with e = 0 cancel), and
|M n [t+1,t+1+K)| - |M n [t,t+K)| = [t+K in M] - [t in M] = [t in F] - [t in M]. So X(t) - |M n [t,t+K)| is independent of t.
Summing over one period: sum_t X(t) = sum of e over the F residues = ((l+2)/4) * 2l, and sum_t |M n [t,t+K)| = K(l+2). Hence the
constant is ( l(l+2)/2 - K(l+2) ) / p = -K/2  (K = l(l+2)/4), i.e. P(t,K) = |M n [t,t+K)| - X(t) = K/2.

(A2) w <= y <= K. P(t,K) - P(t,y) = |M n [t+y, t+K)| >= floor((K-y)/2), because M = F+l has no two adjacent non-members
(no two adjacent dots). So P(t,y) <= K/2 - floor((K-y)/2) = ceil(y/2) = floor((y+1)/2)  (K even). T = Dd = 0.

(A3) 0 <= y <= w. T = Dd = 0. By (1), with f = m+K, t' = t+K, J = [t', t'+y):
P(t,y) = #{ f in F n J : f - e'(f) >= t' }.  The points f = 0 and f = 4q+2 (mod p) have e' = w, and f - w >= t' with f < t'+y would need y > w: they are never counted. Let
F° = F \ {0, 4q+2}. In F° the only adjacent members are (3,4) and (l+1,l+2), the only adjacent non-members are (4q+1, 4q+2)
and (2l-1, 2l); all four pairs start at an odd position, and around the cycle they alternate:
(3,4), (4q+1,4q+2), (l+1,l+2), (2l-1,2l), (3,4), ...
Cut J into consecutive blocks {t',t'+1}, {t'+2,t'+3}, .. (the last possibly a single position, which holds at most one member).
If t' is even, every block holds at most one member of F°, so P <= ceil(y/2). If t' is odd, a block holds two members iff it is
(3,4) or (l+1,l+2) (mod p), none iff it is a full block (4q+1,4q+2) or (2l-1,2l), and one otherwise; by the alternation
|F° n J| <= ceil(y/2) + 1 (a trailing single position can only lower the count), with equality only if the first of the four special blocks that meets J is a full block (3,4) or
(l+1,l+2), i.e. r = t' mod p is odd with r in {1, 3} or 4q+3 <= r <= l+1. In that case one member of F° n J is not counted:
  r = 1 or 3:  the point f = t'+3-r (residue 3; it is in J, since the block (3,4) is) has e' = h = 4q >= 4 > 3-r, so f - e'(f) < t';
  r = l+1:     f = l+1 has e' = 1, f - 1 < t';
  4q+3 <= r <= l-1 (r odd): f = t' itself is in F° (r = 4q+3 or r in od[4q+5, 8q+1]) and has e' >= 1.
Hence P <= ceil(y/2) = floor((y+1)/2) in all cases.

(B) y = K+d, 1 <= d <= l. By (A1) and the formula for y >= w, P(t,K+d) = K/2 + |M n [t+K, t+K+d)| = K/2 + |F n I|,
I = [t, t+d) (M = F+K and 2K = 0 mod p). By (2), T >= #{ f in F n I : e''(f) = 1, f-1 >= t }. So

        P - T <= K/2 + G,     G = #{ f in F n I : not (e''(f) = 1 and f-1 >= t) }.

Let F' = F \ {1, 4, 4q+3, l+2} (the second elements of the FF pairs removed). F' has no two adjacent members, so
|F' n I| <= ceil(d/2). A point f of F \ F' is counted in G only if f = t; then t+1 is a dot, so
|F' n I| = |F' n [t+2, t+d)| <= ceil(d/2) - 1. In both cases G <= ceil(d/2), which gives (*) when Dd = 0
(floor((K+d+1)/2) = K/2 + ceil(d/2)).
If Dd = 1, then d = l and r = t mod p in D^-; r is not in F, so G = |F' n I|, and it remains to find one block of the pairing
{t,t+1}, {t+2,t+3}, .. of I (l/2 full blocks) with no member of F':
  r in ev[4q+4, l]:  the block (l+2, l+3) in the period of t  (t is even and l+2 is even; l+2 is removed from F', l+3 is a dot;
                     r <= l < l+3 <= r+l-1);
  r = l+3:           the last block of I, (t+l-2, t+l-1) = (1, 2) mod p  (1 is removed from F', 2 is a dot).
So G <= l/2 - 1 and P - T + Dd <= K/2 + l/2 = floor((K+l+1)/2).

(A1)-(A3) and (B) give (*); so the walk is a spread-k circuit code of length l(l+4) in Q_n, and with section 1
K(n,k) = l(l+4) = 4k+2l+4. QED

## 5. Remarks

* (A1) used little about the particular code: for ANY gap function invariant under x -> x+p with 2K = 0 (mod p), K >= max e,
  |F| = l+2 per period and 4-element F orbits of e-sum 2l, P(t,K) = K/2 for all t; and (A2) only needs 'no two adjacent dots'. So for shift-invariant candidates the whole
  content of validity is (A3) (windows shorter than K + the largest e) and (B) (windows longer than 2K).
* How it was found: the l = 10 solver codes use only the gap excesses {0, 1, l/2-1, 3l/2, 2l-2}; restricting the lazy SAT
  (refl/genlazy.py, shift-2l class) to that alphabet decides a type word in seconds, and gave one word at l = 18; the l = 10 and
  l = 18 skeletons differ by repeating blocks, the extrapolation to l = 26 was confirmed by SAT, and the dots by
  struct/ex4/dotenum.c (the completion with all dot gaps within 1 of N/2 is unique for q = 1, 2, 3).
* l = 6 (mod 8): K = 0 (mod 2l), so a code invariant under x -> x+2l cannot have a gap equal to K (it would preserve the residue,
  so all four gaps would be K, with sum 4K < N). But ANY zero-slack code has such a gap: every 2K-window holds exactly K/2 chords
  and the type word has period 2K, so for adjacent F positions t, t+1 the window [t, t+2K+2) holds K/2+2 chords and must contain
  a triple, i.e. two consecutive gaps (K,K), (K,K+1) or (K+1,K). Hence for l = 6 (mod 8) no zero-slack code is invariant under
  x -> x+2l; other shifts are multiples 2l*d with d | (l+4)/2 (none for l = 22, 30). No code found yet (l = 14).
* Machine checks: ex4fam7.py (definition, q = 1..8, 10, 12), snake/check.py VALID for q = 2, 3, 4 (codes/x4fam7_*),
  struct/ex4/ex4lem7.py tests every displayed identity and inequality for all t, y (q = 1..4).

## Referee report (#16, S169)

A fresh AI agent, working from this text only (own generator and checker, theory/referee16/gen.py, lem.py, sec1.py): PASS, no error
and no gap; seven wording nits (applied). Its checks: definition by all pairs without symmetry q = 1..5, with the shift symmetry
q = 6..12; all lists of section 2 for q = 1..7; every identity and inequality of sections 3-4 for all t and y, q = 1..7
(264,000 windows); section 1 in exact integers q = 1..399. The remarks of section 5 are not part of the theorem (the FF-pair
remark was added after the report). NO HUMAN HAS READ THIS.
