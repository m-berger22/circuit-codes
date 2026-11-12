# PROOF12 (S170, 2026-11-11): the uniform ladder designs for general (j, p, m) — Theorem 29

This file contains Theorems 13, 18, 19, 22 (PROOF6, PROOF9, PROOF10) as special cases and is self-contained except for
Lemma 1 and Lemma 2 of PROOF.md. Notation: a spread-k circuit code ("coil") of length N in Q_n is a closed walk v_0..v_{N-1} of
distinct vertices with d_H(v_i, v_j) >= min(k, cyclic distance(i,j)); K(n,k) = the maximum N; l = 2n-3k-1; Byrnes' value is 4k+2l;
the excess is e = N-4k-2l. T_x = the coordinate flipped at step x (x in Z_N); K = k+1.

## Theorem 29

Let j >= 1, m >= 1 odd, and p be positive integers (p = 0 mod 4 follows from (H1), as m is odd) such that

    (H1)   4j divides mp        [then K := m p(p+2j)/(4j) is an integer and K = p/2 (mod p), see (a)]
    (H2)   p/2 >= 5j+2 if j is even,   p/2 >= 5j+1 if j is odd.

Put k = K-1, u = mp, e = 4jm, l = u - (e-4)/2 = mp - 2jm + 2, n = (3k+l+1)/2. Then

        K(n,k) = 4K + 2mp = 4k + 2l + 4jm.

Special cases: j = 1 (p >= 12): Theorems 13, 18. j = 2 (p = 0 mod 8, p >= 24): Theorem 19. m = 1 (p = 4ji, i >= 3): Theorem 22
(j even) and a second code at the parameters of Corollary 23 (j odd). New: e.g. j = 3, m = 3 (excess 36), p = 32, 40, 44, 52, ..:
K(495,303) = 1408, K(882,549) = 2464 -- equality points of Lemma 1 where e/4 = 9 does not divide u.

Common notation: h = p/2 (even), u = mp, N = 4K+2u, X = 2u-2, a = (K-h)/p.

Arithmetic:
 (a) K = (mp/(4j)) (p+2j) = (mp/(4j)) p + mp/2 is an integer by (H1), and K = mh = h (mod p) as m is odd: K = ap + h with a an
     integer. (Conversely K = h mod p forces 4j | mp.)
 (b) K is even (p = 0 mod 4 makes ap and h even); k is odd; l is even.
 (c) u/2 = mh = h (mod p) (m odd); N/4 = K + u/2 = 0 (mod p); N/2 = 0 (mod p); X = -2 (mod p).
 (d) K >= 2u > X and K+2 > u.   [K >= 2u iff p+2j >= 8j iff p >= 6j; (H2) gives p >= 10j+2.]
 (e) e K = u(u+e/2).            [4jm * mp(p+2j)/(4j) = m^2 p(p+2j) = mp(mp+2jm).]
 (f) N = 4k+2l+e (substitution), and n = (3K + mp - 2jm)/2 = N(3p-2j)/(8p).
 (g) 2ja = mh + (m-1)j.         [from K = ap+h and the formula for K.]

## 1. Upper bound

Lemma 2 (k odd): a coil with k > 3l-7 has N <= 5k+3; here k-(3l-7) = K - 3mp + 6jm = m(p-4j)(p-6j)/(4j) > 0 by (H2).
Let N' = 4k+2l+e' be the length of a coil with e' > e; e' is even (the cube is bipartite) and e' <= k+3-2l. Lemma 1 with L = 2K
applies (N' <= 5k+3 < 6K; N'/4 <= 2K; 2K <= N'-k) and requires f(e') <= 0 where
2f(e') = (k+l-1+e')(4k+8-2l-e') - (4k+2l+e')(k+1), 2f(e')-2f(e) = (e'-e)(2k+8-3l-e-e').
f(e) = 0: k+l-1+e = K+u+e/2, 4k+8-2l-e = 4K-2u, 4k+2l+e = 4K+2u, so 2f(e) = 2eK-2u^2-eu = 0 by (e).
2k+8-3l-e-e' >= k+5-l-e = K - mp - 2jm + 2 = m(p-4j)(p+2j)/(4j) + 2 > 0. Hence f(e') > 0: no coil is longer than 4k+2l+e.

## 2. The code

A LADDER of type A, B or C at the residue c (mod p) is a 4-cycle of residues with gap excesses over K:

    A at c:   c -> c+h+1 -> c+2 -> c+h+2 -> c           excesses (1, 1, 0, X)
    B at c:   c -> c+h+1 -> c+2 -> c+h -> c             excesses (1, 1, X, 0)
    C at c:   c -> c+h+1 -> c+1 -> c+h+2 -> c           excesses (1, 0, 1, X)

(a step with excess x adds K+x = h+x mod p; X = -2 mod p; each excess sum is X+2 = 2u, i.e. gap sum 4K+2u = N.)

    j EVEN:  ladders A at 0, B at 4, C at c_t = 8+5t (t = 0..j-2);        L = j+1 ladders.
    j ODD:   ladders C at c_t = 5t (t = 0..j-1);                            L = j ladders.

Let S1, S0, SX be the sets of ladder residues with excess 1, 0, X, and D1 = S1+1, MX = SX-2, M0 = S0 u D1 u MX (the points
x + excess(x) over the ladder residues x; 4L distinct residues, listed below). Define E' as follows: in every maximal cyclic run
of residues outside M0, E' takes every second residue, starting with the second (all runs have odd length, see below).
Let E = E' - h. Residues in E get the gap N/4, all residues outside S0 u S1 u SX u E the gap N/2 ("dots").

Explicitly (d_t := c_t+1; ev/od[x,y] = even/odd integers in [x,y]):

  j even:  M0 n [0,h) = {1, 2, 4, 5} u {d_t, d_t+1 : t <= j-2}      (d_t = 9+5t; the last is d_{j-2}+1 = 5j)
           M0 n [h,p) = {h, h+2, h+4, h+6} u {h+c_t, h+c_t+1}       (h+c_t = h+8+5t; the last is h+5j-1)
           E' = {7} u {12+5t : t <= j-3} u ev[5j+2, h-2] u {h+11+5t : t <= j-3} u od[h+5j+1, p-1]            |E'| = h-3j-4
  j odd:   M0 n [0,h) = {d_t, d_t+1 : t <= j-1}                     (d_t = 5t+1; the last is 5j-3)
           M0 n [h,p) = {h+c_t, h+c_t+1}                            (h+c_t = h+5t; the last is h+5j-4)
           E' = {5t+4 : t <= j-2} u ev[5j-1, h-2] u {h+5t+3 : t <= j-2} u od[h+5j-2, p-1]                       |E'| = h-3j

(The maximal runs outside M0. j even: {3}; {6,7,8} -> 7; {d_t+2, d_t+3, d_t+4} -> d_t+3 for t <= j-3; [5j+1, h-1] -> its even
elements; {h+1}, {h+3}, {h+5}, {h+7}; {h+c_t+2, h+c_t+3, h+c_t+4} -> h+c_t+3 for t <= j-3; [h+5j, p] (ending at the residue 0) -> its
odd elements. j odd: {d_t+2, d_t+3, d_t+4} -> d_t+3 = 5t+4 for t <= j-2; [5j-2, h-1] -> its even elements; {h+c_t+2, h+c_t+3, h+c_t+4}
-> h+5t+3 for t <= j-2; [h+5j-3, p] (ending at 0) -> its odd elements. The long runs have odd length because h is even, and
length >= 1 by (H2).)
E = E'-h is disjoint from the ladder residues: for j even the ladder residues are 0, 2, 4, 6, c_t, c_t+1 (= 3, 4 mod 5, in [8, 5j-1])
and h+1, h+2, h+4, h+5, h+c_t+1, h+c_t+2 (in [h+9, h+5j]), while E = {11+5t} (= 1 mod 5) u od[5j+1, h-1] u {h+7} u {h+12+5t} u ev[h+5j+2, p-2];
for j odd the ladder residues are c_t, c_t+1 (= 0, 1 mod 5, in [0, 5j-4]) and h+c_t+1, h+c_t+2 (in [h+1, h+5j-3]), while
E = {5t+3 : t <= j-2} (= 3 mod 5) u od[5j-2, h-1] u {h+5t+4 : t <= j-2} (= h+4 mod 5 offset) u ev[h+5j-1, p-2].
So the F residues are S0 u S1 u SX u E (4L + |E'| = h+j of them), and the dots are the other h-j residues.

s(x) = x+g(x) is a permutation of Z_N: 4-element orbits on ladder residues (gap sum N), 4-element orbits with gaps N/4 on E
(N/4 = 0 mod p), 2-element orbits on dots. T_x = the orbit of x; every coordinate is used an even number of times, so the walk
closes. Number of coordinates: (N/p)(L + |E|/4 + (h-j)/2) = (N/p)(3h-j)/4 = N(3p-2j)/(8p) = n by (f).
(struct/ex4/ladfam2.py; lem29.py builds every case.)

## 3. Reduction (identical for both parities)

All gaps are >= K; a window and its complement have the same odd coordinates; windows of length <= k have distinct coordinates.
So it suffices to show odd(W) >= k for W = [t,t+L), K <= L <= N/2 = 2K+u; write L = K+y, 0 <= y <= K+u.
In W a dot occurs at most once (L <= N/2), an E coordinate at most twice (three positions span N/2+1), a ladder coordinate at
most 3 times (four positions span >= N-(K+X)+1 = 3K+3 > 2K+u by (d)), and 3 times only as x, s(x), s^2(x) with both gaps in
{K, K+1} (a pair containing K+X has sum >= 2K+2u-2 > 2K+u-1 >= L-1). A coordinate occurring twice does so at orbit-consecutive
positions x, s(x) with the arc from x to s(x) inside W (the complementary arc is longer than L; two non-consecutive positions
x, s^2(x) in an interval would force s(x) or s^3(x) into it). Let
T1 = {ladder residues x: g(x)+g(s x) = 2K+1}, T2 = {.. = 2K+2}:

    A at c:  T1 = {c+h+1} (1,0),  T2 = {c} (1,1)      B at c:  T1 = {c+h} (0,1),  T2 = {c} (1,1)      C at c:  T1 = {c, c+h+1},  T2 = {}.

P = number of chords, T = number of triples in W: odd(W) = L-2(P-T), and the claim is

    (*)     P(t,y) - T(t,y) <= floor((y+1)/2)       for all t, 0 <= y <= K+u       (then odd(W) >= K+y-2floor((y+1)/2) >= k).

With |S n [x,y)| = number of integers in [x,y) whose residue is in S:

    P(t,y) = |S0 n [t,t+y)| + |S1 n [t,t+y-1)| + |E n [t,t+y-u/2)| + |SX n [t,t+y-X)|,
    T(t,y) = |T1 n [t,t+y-K-1)| + |T2 n [t,t+y-K-2)|.

Shifting each class to the end of its strip (shifts 1, u/2 = h, X = -2 on residues): M := S0 u D1 u E' u MX = M0 u E' (|M| = h+j),

    (1)   P(t,y) = |M n [t,t+y)| - R(t,y),    R(t,y) = [y >= 1 and t in D1] + |E' n [t,t+min(y,u/2))| + |MX n [t,t+min(y,X))|.

Per ladder (class of each point of M0 in brackets):
    A at c:  c+1 [D1], c+2 [S0], c+h [MX], c+h+2 [D1]
    B at c:  c [MX], c+1 [D1], c+h [S0], c+h+2 [D1]
    C at c:  c+1 [D1], c+2 [D1], c+h [MX], c+h+1 [S0]

Facts (from the lists of section 2):
    (M-a)  M has no two cyclically adjacent non-members (E' fills every run of non-members of M0 alternately).
    (M-b)  The adjacent member pairs of M are exactly the 2j pairs inside M0: j even: (1,2), (4,5), (d_t,d_t+1), (h+c_t,h+c_t+1);
           j odd: (d_t,d_t+1), (h+c_t,h+c_t+1). Their first elements form Z1 := T1+h. So M'' = M \ Z1 has no two adjacent
           members, and for every z in Z1 the residue z-1 is a non-member of M (the element before an adjacent pair).
    (M-c)  M' := M \ MX. Adjacent member pairs of M': j even: (1,2), (d_t,d_t+1) (t = 0..j-2); j odd: (d_t,d_t+1) (t = 0..j-1).
           Adjacent non-member pairs of M': j even: (3,4), (h-1,h), (h,h+1), (h+c_t-1,h+c_t) (t = 0..j-2);
           j odd: (h+c_t-1, h+c_t) (t = 0..j-1; for t = 0 this is (h-1,h)).
    (L)    Lam := S0 u D1 (3 points per ladder). j even: Lam = {1,2,5} u {d_t,d_t+1} u {h+2,h+4,h+6} u {h+d_t};
           j odd: Lam = {d_t, d_t+1} u {h+d_t}. Its adjacent member pairs are those of (M-c): (d', d'+1) with d' in D1, and
           d'-1, d'-2 are not in Lam (d'-1 is not in M; d'-2 is in E'; for d' = 1 these are the residues 0 and p-1).

## 4. Proof of (*)

(A1) P(t,K) = K/2 for all t (T = 0).  By (a), |M n [t,t+K)| = a|M| + |M n [t,t+h)|. In R(t,K): min(K,u/2) = u/2 = ((m-1)/2)p + h,
so the E' term is ((m-1)/2)|E'| + |E' n [t,t+h)|; min(K,X) = X = 2mp-2, and [t,t+X) is 2m periods minus the positions t-2, t-1,
so the MX term is 2m|MX| - c(t), c(t) = |MX n {t-2,t-1}|. With d(t) = [t in D1]:

        P(t,K) = a|M| - ((m-1)/2)|E'| - 2m L + ( |M0 n [t,t+h)| - d(t) + c(t) ).

Claim: for each ladder separately (M0, D1, MX restricted to its four points), |M0 n [t,t+h)| - d(t) + c(t) = 2 for every t (h >= 3):
 A at c: d = 1 at c+1, c+h+2; c = 1 at c+h+1, c+h+2.  t = c+1: 3-1 (c+1, c+2, c+h).  t = c+2: 2 (c+2, c+h).  c+3 <= t <= c+h: 2 (c+h, c+h+2).
         t = c+h+1: 1+1 (c+h+2).  t = c+h+2: 2-1+1 (c+h+2, c+p+1).  c+h+3 <= t <= c+p: 2 (c+p+1, c+p+2).
 B at c: d = 1 at c+1, c+h+2; c = 1 at c+1, c+2.  t = c: 2 (c, c+1).  t = c+1: 2-1+1 (c+1, c+h).  t = c+2: 1+1 (c+h).
         c+3 <= t <= c+h: 2 (c+h, c+h+2).  t = c+h+1: 2 (c+h+2, c+p).  t = c+h+2: 3-1 (c+h+2, c+p, c+p+1).  c+h+3 <= t <= c+p-1: 2 (c+p, c+p+1).
 C at c: d = 1 at c+1, c+2; c = 1 at c+h+1, c+h+2.  t = c+1: 3-1 (c+1, c+2, c+h).  t = c+2: 3-1 (c+2, c+h, c+h+1).  c+3 <= t <= c+h: 2 (c+h, c+h+1).
         t = c+h+1: 1+1 (c+h+1).  t = c+h+2: 1+1 (c+p+1).  c+h+3 <= t <= c+p: 2 (c+p+1, c+p+2).
So the bracket is 2L and P(t,K) = a(h+j) - ((m-1)/2)(h+j-4L) - 2(m-1)L = a(h+j) - ((m-1)/2)(h+j) = ah + [2ja - (m-1)(h+j)]/2 = ah + h/2
= K/2, using (g): 2ja - (m-1)(h+j) = mh + (m-1)j - (m-1)h - (m-1)j = h. QED (A1)

(A2) X <= y <= K: R(t,y) is constant in y, so P(t,K)-P(t,y) = |M n [t+y,t+K)| >= floor((K-y)/2) by (M-a): P(t,y) <= ceil(y/2); T = 0.

(A3) 0 <= y <= X. T = 0; the MX term of R is |MX n [t,t+y)|; with d = [y >= 1 and t in D1]:
        P(t,y) = |M' n [t,t+y)| - d - |E' n [t,t+min(y,u/2))|.
(A3a) y <= u/2: P(t,y) = |Lam n I| - d, I = [t,t+y). Cut I into consecutive pairs {t,t+1}, {t+2,t+3}, .. (the last possibly
single). A block with two members of Lam is a pair (d',d'+1) of (L); if it is not the first block, the block before it,
(d'-2,d'-1), is a full block of I without members of Lam, and different two-member blocks have different predecessors. So
|Lam n I| <= ceil(y/2) + [the first block is such a pair], and then t = d' is in D1, y >= 2, d = 1. Hence P <= ceil(y/2).
(A3b) u/2 < y <= X: P(t,y) = ( |Lam n [t,t+u/2)| - d ) + |M' n [t+u/2, t+y)|.
 (L1) |Lam n [t,t+h)| <= H, where H = 2j+1 (j even), H = 2j (j odd). Put Lam1 = Lam n [0,h), Lam2 = (Lam n [h,p)) - h and
      A(x) = |Lam1 n [0,x)|, B(x) = |Lam2 n [0,x)| for 0 <= x <= h.
      j even: Lam1 = {1,2,5} u {d_t,d_t+1} (2j+1 elements), Lam2 = {2,4,6} u {d_t} (j+2). The injection phi: 2->1, 4->2, 6->5, d_t->d_t
        has phi(z) <= z, so B <= A; A(x)-B(x) = #{z in Lam1 \ phi(Lam2): z < x} + #{z in Lam2: phi(z) < x <= z}; the first set is
        inside {d_t+1} (j-1 elements, all >= 10), the second is non-empty only for x in {2,3,4,6} (one element). So 0 <= A-B <= j-1.
      j odd:  Lam1 = {d_t, d_t+1} (2j elements), Lam2 = {d_t} (j), a subset of Lam1: 0 <= A(x)-B(x) = #{d_t+1 < x} <= j.
      For t = x in [0,h): |Lam n [t,t+h)| = |Lam1| - A(x) + B(x) <= |Lam1| = H. For t = h+x: = |Lam2| - B(x) + A(x) <= H
      (j+2+j-1 resp. j+j).
      Hence |Lam n [t,t+u/2)| <= ((m-1)/2)|Lam| + H = 3L(m-1)/2 + H   (u/2 = ((m-1)/2)p + h).
 (L2) For every interval I: |M' n I| <= ceil(|I|/2) + c0, c0 = j/2 (j even), (j+1)/2 (j odd). Cut I into pairs from its start:
      |M' n I| <= ceil(|I|/2) + (#two-member blocks) - (#full no-member blocks). By (M-c) the special pairs are, in cyclic order,
      j even, pairs starting at odd residues:  +(1,2), -(3,4), +(d_t,d_t+1) for even t (j/2 of them), -(h-1,h), -(h+c_t-1,h+c_t) for
                                              even t (j/2 of them);       period sum -1, largest cyclic partial sum j/2;
      j even, starting at even residues:      +(d_t,d_t+1) for odd t (j/2-1), -(h,h+1), -(h+c_t-1,h+c_t) for odd t (j/2-1); period sum -1, max j/2-1;
      j odd,  starting at odd residues:       +(d_t,d_t+1) for even t ((j+1)/2), then -(h+c_t-1,h+c_t) for even t ((j+1)/2);
                                              period sum 0, largest cyclic partial sum (j+1)/2;
      j odd,  starting at even residues:      +(d_t,d_t+1) for odd t ((j-1)/2), then -(h+c_t-1,h+c_t) for odd t ((j-1)/2); max (j-1)/2.
      (parities: j even: d_t = 9+5t and h+c_t-1 = h+7+5t are odd iff t is even; j odd: d_t = 5t+1 and h+c_t-1 = h+5t-1 are odd
      iff t is even; h and p are even, so the parity of a position is the parity of its residue.) In each case all + pairs of a
      period come before all - pairs of that period (apart from the pair +(1,2), -(3,4) for j even), and the period sum is <= 0,
      so no stretch of consecutive special blocks, of any length, has sum above c0; a block cut to a single position holds at
      most one member.
 With (L1), (L2): P(t,y) <= 3L(m-1)/2 + H + ceil((y-u/2)/2) + c0, and ceil(y/2) = mh/2 + ceil((y-u/2)/2) (u/2 = mh is even).
 Now 3L <= h and H + c0 <= h/2:  j even: 3j+3 <= 5j+2 <= h and 2j+1+j/2 <= (5j+2)/2 <= h/2;
                                  j odd:  3j <= h and 2j+(j+1)/2 = (5j+1)/2 <= h/2   -- by (H2).
 So 3L(m-1)/2 + H + c0 <= (m-1)h/2 + h/2 = mh/2, and P(t,y) <= ceil(y/2).

(B) K < y <= K+u. d := y-K in [1,u], s = t+K, I = [s,s+d). R is constant for y >= X, so P(t,y) = K/2 + |M n I| by (1), (A1).
By (a), T(t,y) >= |T1 n [t,t+d-1)| = |Z1 n [s,s+d-1)|, and since Z1 is a subset of M:
|M n I| - |Z1 n [s,s+d-1)| = |M'' n I| + [s+d-1 in Z1]. By (M-b), |M'' n I| <= ceil(d/2), and if s+d-1 is in Z1 then s+d-1 and
s+d-2 are non-members of M'', so |M'' n I| <= ceil((d-2)/2) = ceil(d/2)-1 (d = 1: 0+1). So P-T <= K/2+ceil(d/2) = floor((y+1)/2).

(A1)-(A3), (B) give (*): the walk is a spread-k circuit code of length N = 4k+2l+4jm in Q_n. With section 1, K(n,k) = N. QED

## 5. Remarks

* Which equality points are covered: (e, u) with u = l+(e-4)/2 and K = u(2u+e)/(2e). Theorem 29 applies when there is an odd m
  dividing both e/4 and u with (e/m) | u, u/m = 0 mod 4 and u/(2m) >= 5e/(4m) + 2 (resp. +1): with j = e/(4m), p = u/m.
  m = 1: e | u (Corollary 23). m > 1 gives more when e/4 is not squarefree, e.g. e = 36: u = 0 mod 12 (u >= 96; also 84 by
  computation: (H2) is not sharp for odd j, p/2 = 5j-1 works in all computed cases).
* (H2) for j odd could be weakened to p/2 >= 5j-1 (all computed cases are codes); the proof of (A3b) above needs 5j+1.
* Machine checks: struct/ex4/lem29.py tests every displayed set, identity and inequality for all t, y in all admissible cases with
  j <= 7, p <= 100, m <= 9, N <= 6000 (runs/lem29.out); snake/check.py VALID on codes/lad2_j3_p28_m3.txt (390,237,1120) [p/2 = 5j-1].

## 6. Addendum (after referee report #25; refereed separately, report #26 below): j odd, p/2 = 5j-1

For j odd the hypothesis (H2) can be weakened to p/2 >= 5j-1, provided m >= 3; the only new case is p = 10j-2 with j | m,
m >= 3 odd (p/2 = 5j is impossible: p = 10j is 2 mod 4). [At p/2 = 5j-1, i.e. p = 10j-2, (H1) reads
4j | m(10j-2), i.e. 2j | m(5j-1), which forces j | m; so m >= 3 unless j = 1, and (j, m, p) = (1, 1, 8) is Theorem 13.]
Where (H2) was used for j odd: (i) the long runs [5j-2, h-1] and [h+5j-3, p] are non-empty and of odd length -- true for
h >= 5j-1 (for h = 5j-1 they are {h-1}, with no E' element, and {p-2, p-1, 0}, where E' takes p-1); (ii) 3L = 3j <= h -- true;
(iii) p > 6j in section 1 and (d) -- true (10j-2 > 6j); (iv) the last line of (A3b), H + c0 <= h/2, which fails by 1 at h = 5j-1.
But (A3b) only needs  3L(m-1)/2 + H + c0 <= mh/2,  i.e. (3jm + 2j + 1)/2 <= m(5j-1)/2,  i.e.  m(2j-1) >= 2j+1,
which holds for m >= 3. Everything else is unchanged.
Machine check: all steps of sections 2-4 for (j,p,m) = (1,8,3), (1,8,5), (1,8,7), (1,8,9), (3,28,3), (3,28,9), (5,48,5)
(lem29.py with the (H2) filter replaced by 'h = 5j-1, j odd, m >= 3'). New points: e = 36, u = 84: K(390,237) = 1120.

## Referee report (#25, S170)

A fresh AI agent, from the text of section 2 only (theory/referee25/ref25.py, sweep.py; E' built from its definition and compared
with the explicit lists): PASS, no mathematical error; five cosmetic points (applied). Checks: all-pairs validity on vertices for
19 cases (j <= 6, including (3,32,3), (3,40,3), (3,44,3), (5,52,5) with 4j not dividing p); every displayed item of sections 2-4 for
all t, y in those cases and in a sweep of all 118 admissible cases with j <= 8, p <= 120, m <= 9, N <= 6000 (c0 of (L2) and H of (L1)
are attained); section 1 and (a)-(g) in exact integers for 10,320 cases. Outside the hypotheses: j odd with p/2 = 5j-1 are valid
codes ((1,8,1), (3,28,3), (5,48,5), (7,68,7)); smaller p: ladder residues collide; even m: s is not a permutation; (H2) is sharp for
even j. Not checked by the referee: the identification with Theorems 13, 18, 19, 22.

## Referee report (#26, S170) on section 6

A fresh AI agent (theory/referee26/ref26.py): PASS WITH FIXES -- one wrong sentence in (i) (the run [h+5j-3, p] is {p-2, p-1, 0}),
the hypothesis stated explicitly, a superfluous remark deleted; all applied. It checked the arithmetic (j | m at p = 10j-2; p/2 = 5j
impossible), every use of (H2) for general odd j at h = 5j-1, the replacement inequality, and by its own generator and all-pairs
checker the cases (1,8,3), (1,8,5), (3,28,3), (5,48,5), (3,28,9); (1,8,1) is a code although the combined inequality fails there.
