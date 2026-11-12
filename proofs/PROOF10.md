# PROOF10 (S170, 2026-11-11): every excess e = 0 (mod 4) is attained exactly — a uniform ladder family

Notation as in PROOF9.md: a spread-k circuit code ("coil") of length N in Q_n is a closed walk v_0..v_{N-1} of distinct vertices
with d_H(v_i, v_j) >= min(k, cyclic distance(i,j)); K(n,k) = the maximum N; l = 2n-3k-1; Byrnes' value is 4k+2l; the excess is
e = N-4k-2l. T_x = the coordinate flipped between v_x and v_{x+1} (x in Z_N); K = k+1. Lemma 1, Lemma 2: PROOF.md.

## Theorem 22

Let j >= 2 be EVEN and i >= 3. Put

        k = 2ji(2i+1) - 1,       n = j(6i-1)(i+1),       l = 2n-3k-1 = 4ji - 2j + 2.
Then
        K(n,k) = 16ji(i+1) = 4k + 2l + 4j.

## Corollary 23

For every j >= 1 and i >= 3:   K( j(6i-1)(i+1), 2ji(2i+1) - 1 ) = 16 j i(i+1),  which is Byrnes' value plus 4j.
In other words (n, k+1, K(n,k)) = j * ( (6i-1)(i+1), 2i(2i+1), 16i(i+1) ) for every multiplier j >= 1.
[j even: Theorem 22. j odd: Theorem 18 of PROOF9.md with p = 4i >= 12 and m = j: k = j*4i(4i+2)/4 - 1, n = j(12i-2)(4i+4)/8,
K(n,k) = j*4i(4i+4). (For odd j also i = 2.)]
So for every e = 0 mod 4 and every u = e*i, i >= 3, the Lemma-1 equality point (e, u) [K = u(2u+e)/(2e), u = l+(e-4)/2] carries a code.
First cases: K(136,83) = 384 (j=2, i=3), K(272,167) = 768 (excess 16), K(408,251) = 1152 (excess 24), K(544,335) = 1536 (excess 32).

Common notation: p = u = 4ji (the period), h = p/2 = 2ji, e = 4j, K = 2ji(2i+1), N = 16ji(i+1), X = 2p-2, J = j-2 >= 0.

Arithmetic:
 (a) K = p*i + h, so K = h (mod p).   (b) K is even, k is odd.
 (c) N = 4K+2p; N/4 = K+h = p(i+1) = 0 (mod p); N/2 = 0 (mod p); X = -2 (mod p).
 (d) K >= 2p > X (as i >= 2) and K+2 > p.
 (e) eK = 8j^2 i(2i+1) = p(p + e/2).
 (f) n = (3k+l+1)/2 and N = 4k+2l+e (direct substitution); h >= 5j+2 (as i >= 3, j >= 2: 6j >= 5j+2).

## 1. Upper bound

Lemma 2 (k odd): a coil with k > 3l-7 has N <= 5k+3. Here k-(3l-7) = 2j(2i-3)(i-1) > 0.
Let N' = 4k+2l+e' be the length of a coil with e' > e; e' is even (N' is even: the cube is bipartite) and e' <= k+3-2l.
Lemma 1 with L = 2K applies (N' <= 5k+3 < 6K; N'/4 <= 2K; 2K <= N'-k) and requires f(e') <= 0 where
2f(e') = (k+l-1+e')(4k+8-2l-e') - (4k+2l+e')(k+1), and 2f(e')-2f(e) = (e'-e)(2k+8-3l-e-e').
f(e) = 0: k+l-1+e = K+p+e/2, 4k+8-2l-e = 4K-2p, 4k+2l+e = 4K+2p, so 2f(e) = (K+p+e/2)(4K-2p) - (4K+2p)K = 2eK-2p^2-ep = 0 by (e).
2k+8-3l-e-e' >= k+5-l-e = 2j(2i+1)(i-1) + 2 > 0. Hence f(e') > 0: no coil is longer than 4k+2l+e.

## 2. The code

Let a_t = 8+5t for t = 0, .., J (J+1 = j-1 values; a_J = 5j-2). Partition Z_p into

    S1 = {0, h+1, 4, h+5} u {a_t, a_t+1 : t = 0..J}                     gap g = K+1
    S0 = {2, h+4} u {h+a_t+1 : t = 0..J}                                gap g = K
    SX = {h+2, 6} u {h+a_t+2 : t = 0..J}                                gap g = K+X = N-3K-2
    E  = {11+5t : 0 <= t <= J-1} u {odd r, 5j+1 <= r <= h-1} u {h+7} u {h+12+5t : 0 <= t <= J-1} u {even r, h+5j+2 <= r <= p-2}
                                                                        gap g = N/4
    D  = the rest                                                       gap g = N/2

(these sets are pairwise disjoint: in [0,h) the ladder residues are 0, 2, 4, 6 and a_t, a_t+1 = 3, 4 (mod 5) between 8 and 5j-1,
while 11+5t = 1 (mod 5) and the odd r are >= 5j+1; in [h,p) the ladder residues are h+1, h+2, h+4, h+5 and h+a_t+1, h+a_t+2 =
h+4, h+0 (mod 5 after subtracting h) between h+9 and h+5j, while h+7, h+12+5t = h+2 (mod 5) and the even r are >= h+5j+2).
The gap function on Z_N depends only on r = x mod p, and s(x) = x+g(x). On residues s is r -> r+h (S0), r+h+1 (S1), r+h-2 (SX),
r (E, D), by (a), (c); it consists of the j+1 "ladders" (4-cycles)

    A:    0 -> h+1 -> 2 -> h+2 -> 0                           gap excesses over K: (1, 1, 0, X)
    B:    4 -> h+5 -> 6 -> h+4 -> 4                                                (1, 1, X, 0)
    C_t:  a_t -> a_t+h+1 -> a_t+1 -> a_t+h+2 -> a_t                                (1, 0, 1, X)      t = 0..J

and fixed points. Each ladder has gap sum 4K+X+2 = N. So s is a permutation of Z_N with 4-element orbits on ladder residues,
4-element orbits (gaps N/4) on E, 2-element orbits (gaps N/2, "dots") on D. T_x = the orbit of x; every coordinate is used an
even number of times, so the walk closes. |E| = (J) + (h-5j)/2 + 1 + J + (h-5j-2)/2 = h-3j-4, |D| = p - 4(j+1) - |E| = h-j.
Number of coordinates: (N/p)( (j+1) + |E|/4 + |D|/2 ) = 4(i+1)(3h-j)/4 = (i+1)(6ji-j) = n.
(struct/ex4/ladfam.py j i builds it; j = 2 is the code of Theorem 19 with m = 1.)

## 3. Reduction (as in PROOF9 sec. 3)

All gaps are >= K, so windows of length <= k have distinct coordinates; a window and its complement have the same odd
coordinates; so it suffices to show odd(W) >= k for W = [t, t+L), K <= L <= N/2 = 2K+p. Write L = K+y, 0 <= y <= K+p.

A dot occurs at most once in W (L <= N/2). An E coordinate at most twice (three positions span N/2+1 > L). A ladder coordinate
at most 3 times (four positions span >= N-(K+X)+1 = 3K+3 > 2K+p by (d)), and 3 times only as x, s(x), s^2(x) with
g(x)+g(s(x)) <= L-1 <= 2K+p-1; a pair containing the gap K+X has sum >= 2K+2p-2 > 2K+p-1, so both gaps are in {K, K+1}.
A coordinate occurring exactly twice does so at orbit-consecutive positions x, s(x) with the arc from x to s(x) inside W
(W is an interval; the complementary arc has more than L positions). Let

    T1 = {residues x: g(x)+g(s(x)) = 2K+1} = {h+1, h+4} u {a_t, a_t+h+1 : t = 0..J},       T2 = {.. = 2K+2} = {0, 4}

(from the ladders: A has consecutive excess pairs (1,1) at 0 and (1,0) at h+1; B has (1,1) at 4 and (0,1) at h+4; C_t has (1,0)
at a_t and (0,1) at a_t+h+1; no two consecutive gaps K). With P(W) = number of chords (x, s(x) in W), T(W) = number of triples:
odd(W) = L - 2(P-T), and the claim is

    (*)     P(t,y) - T(t,y) <= floor((y+1)/2)          for all t and 0 <= y <= K+p        (then odd(W) >= K+y-2floor((y+1)/2) >= k).

For a set S of residues, |S n [a,b)| = number of integers x in [a,b) with x mod p in S (0 if b <= a). Then

    P(t,y) = |S0 n [t,t+y)| + |S1 n [t,t+y-1)| + |E n [t,t+y-h)| + |SX n [t,t+y-X)|,
    T(t,y) = |T1 n [t,t+y-K-1)| + |T2 n [t,t+y-K-2)|.

Shifted sets (shifts 1, h, -2 on residues):

    D1 = S1+1 = {1, h+2, 5, h+6} u {a_t+1, a_t+2},      MX = SX-2 = {h, 4} u {h+a_t},
    E' = E+h = {7} u {12+5t : t <= J-1} u {even r, 5j+2 <= r <= h-2} u {h+11+5t : t <= J-1} u {odd r, h+5j+1 <= r <= p-1},
    M  = S0 u D1 u E' u MX   (disjoint; |M| = h+j),

    (1)   P(t,y) = |M n [t,t+y)| - R(t,y),    R(t,y) = [y >= 1 and t in D1] + |E' n [t,t+min(y,h))| + |MX n [t,t+min(y,X))|.

M in cyclic order (m = member, n = non-member; d_t := a_t+1 = 9+5t):

    [0,h):   0n 1m 2m 3n 4m 5m 6n 7m 8n | for t = 0..J-1:  (d_t)m (d_t+1)m (d_t+2)n (d_t+3)m (d_t+4)n | (d_J)m (d_J+1)m ,
             then 5j+1 n, 5j+2 m, 5j+3 n, .., h-2 m, h-1 n                      (d_J + 1 = 5j)
    [h,p):   h m, h+1 n, h+2 m, h+3 n, h+4 m, h+5 n, h+6 m, h+7 n | for t = 0..J-1: (h+a_t)m (h+a_t+1)m (h+a_t+2)n (h+a_t+3)m (h+a_t+4)n |
             (h+a_J)m (h+a_J+1)m, then h+5j n, h+5j+1 m, .., p-1 m              (h+a_J+1 = h+5j-1)

Facts:
    (M-a)  M has no two cyclically adjacent non-members.
    (M-b)  Z1 := T1+h = {1, 4} u {h+a_t, a_t+1 : t = 0..J} is contained in M; these are exactly the first elements of the
           adjacent member pairs (1,2), (4,5), (d_t, d_t+1), (h+a_t, h+a_t+1). So M'' = M \ Z1 has no two adjacent members,
           and for every z in Z1, z-1 is not in M'' (z-1 = 0, 3, a_t = d_t - 1, h+a_t-1 are non-members of M).
    (M-c)  M' := M \ MX = S0 u D1 u E'. Its adjacent member pairs are (1,2) and (d_t, d_t+1), t = 0..J; its adjacent
           non-member pairs are (3,4), (h-1,h), (h,h+1) and (h+a_t-1, h+a_t), t = 0..J.
    (L)    The "light" set Lam := S0 u D1 = {1, 2, 5} u {d_t, d_t+1 : t = 0..J} u {h+2, h+4, h+6} u {h+a_t+1 : t = 0..J}.
           Its adjacent member pairs are (1,2) and (d_t, d_t+1); each starts with an element d of D1, and d-1, d-2 are not in Lam
           (for d = 1: p-1, 0; for d = d_0 = 9: 8, 7; for d = d_t, t >= 1: d_t-1 = a_t, d_t-2 = d_{t-1}+3; the Lam-member before
           d_t is d_{t-1}+1).

## 4. Proof of (*)

(A1) y = K: P(t,K) = K/2 for all t; T = 0.
By (a), |M n [t,t+K)| = i|M| + |M n [t,t+h)|. In R(t,K): min(K,h) = h; min(K,X) = X = 2p-2, and [t,t+2p-2) is two periods minus
the positions t-2, t-1, so the MX term is 2|MX| - c(t), c(t) = |MX n {t-2,t-1}|. With M0 = M \ E' = S0 u D1 u MX, d(t) = [t in D1]:

        P(t,K) = i|M| - 2|MX| + ( |M0 n [t,t+h)| - d(t) + c(t) ).

Claim: for EACH ladder, with M0, D1, MX restricted to the four points coming from that ladder,
|M0 n [t,t+h)| - d(t) + c(t) = 2 for every t. (Points listed with their class; a = the start residue of the ladder.)
 A (a = 0): M0 = {a+1 (D1), a+2 (S0), a+h (MX), a+h+2 (D1)};  d = 1 at a+1, a+h+2;  c = 1 at a+h+1, a+h+2.
     t = a+1: 3-1+0.  t = a+2: 2 (a+2, a+h).  a+3 <= t <= a+h: 2 (a+h, a+h+2).  t = a+h+1: 1+1 (a+h+2).  t = a+h+2: 2-1+1 (a+h+2, a+p+1).
     a+h+3 <= t <= a+p: 2 (a+p+1, a+p+2).
 B (a = 4): M0 = {a (MX), a+1 (D1), a+h (S0), a+h+2 (D1)};  d = 1 at a+1, a+h+2;  c = 1 at a+1, a+2.
     t = a: 2 (a, a+1).  t = a+1: 2-1+1 (a+1, a+h).  t = a+2: 1+1 (a+h).  a+3 <= t <= a+h: 2 (a+h, a+h+2).  t = a+h+1: 2 (a+h+2, a+p).
     t = a+h+2: 3-1 (a+h+2, a+p, a+p+1).  a+h+3 <= t <= a+p-1: 2 (a+p, a+p+1).
 C (a = a_t): M0 = {a+1 (D1), a+2 (D1), a+h (MX), a+h+1 (S0)};  d = 1 at a+1, a+2;  c = 1 at a+h+1, a+h+2.
     t = a+1: 3-1 (a+1, a+2, a+h).  t = a+2: 3-1 (a+2, a+h, a+h+1).  a+3 <= t <= a+h: 2 (a+h, a+h+1).  t = a+h+1: 1+1 (a+h+1).
     t = a+h+2: 1+1 (a+p+1).  a+h+3 <= t <= a+p: 2 (a+p+1, a+p+2).
Summing over the j+1 = |MX| ladders: the bracket is 2|MX|, so P(t,K) = i|M| = i(h+j) = K/2 (K/2 = (pi+h)/2 = ih + ij). QED (A1)

(A2) X <= y <= K: R(t,y) does not depend on y (y >= X > h), so P(t,K) - P(t,y) = |M n [t+y,t+K)| >= floor((K-y)/2) by (M-a);
hence P(t,y) <= K/2 - floor((K-y)/2) = ceil(y/2). T = 0.

(A3) 0 <= y <= X. T = 0, and the MX term of R is |MX n [t,t+y)|, so with d = [y >= 1 and t in D1]:
        P(t,y) = |M' n [t,t+y)| - d - |E' n [t, t+min(y,h))|.
(A3a) y <= h:  P(t,y) = |Lam n I| - d, I = [t,t+y). Cut I into consecutive pairs {t,t+1}, {t+2,t+3}, .. (ceil(y/2) blocks, the
last possibly a single position). A block holds two members of Lam only if it is a pair (d', d'+1) of (L). If such a block is
not the first block, the block before it, (d'-2, d'-1), is a full block of I with no member of Lam (by (L)); different
two-member blocks have different predecessors. So |Lam n I| <= ceil(y/2) + [the first block is a pair (d', d'+1) of (L)], and in
that case t = d' is in D1 and y >= 2, so d = 1. Hence P(t,y) <= ceil(y/2).   [This argument does not use y <= h.]
(A3b) h < y <= X:  P(t,y) = ( |Lam n [t,t+h)| - d ) + |M' n [t+h, t+y)|.
 (L1) |Lam n [t,t+h)| <= 2j+1 for every t. Write Lam1 = Lam n [0,h) = {1, 2, 5} u {d_t, d_t+1 : t = 0..J} (2j+1 elements),
      Lam2 = (Lam n [h,p)) - h = {2, 4, 6} u {d_t : t = 0..J} (j+2 elements; h+a_t+1 = h+d_t), and for 0 <= tau <= h let
      A(tau) = |Lam1 n [0,tau)|, B(tau) = |Lam2 n [0,tau)|. Claim: 0 <= A(tau) - B(tau) <= j-1.
      The map phi: 2 -> 1, 4 -> 2, 6 -> 5, d_t -> d_t is an injection Lam2 -> Lam1 with phi(x) <= x, so B <= A; and
      A(tau) - B(tau) = #{x in Lam1 \ phi(Lam2): x < tau} + #{x in Lam2: phi(x) < tau <= x}. The first set is contained in
      {d_t+1 : t = 0..J} (j-1 elements, all >= 10); the second is non-empty only for tau in {2, 3, 4, 6} and then has one element
      (x = 2, 4, 4, 6), while the first is empty for tau <= 10. So A - B <= max(j-1, 1) = j-1.
      For t = tau in [0,h):  |Lam n [t,t+h)| = |Lam1| - A(tau) + B(tau) <= |Lam1| = 2j+1.
      For t = h+tau:         |Lam n [t,t+h)| = |Lam2| - B(tau) + A(tau) <= j+2 + j-1 = 2j+1.
 (L2) |M' n I| <= ceil(|I|/2) + j/2 for every interval I. Cut I into consecutive pairs from its start; then
      |M' n I| <= ceil(|I|/2) + (#two-member blocks) - (#full no-member blocks). By (M-c), if the blocks start at odd residues the
      special blocks are, in cyclic order,  +(1,2), -(3,4), +(d_t,d_t+1) for even t (j/2 of them), -(h-1,h), -(h+a_t-1,h+a_t) for
      even t (j/2 of them); if they start at even residues: +(d_t,d_t+1) for odd t (j/2-1 of them), -(h,h+1), -(h+a_t-1,h+a_t) for
      odd t (j/2-1). (d_t = 9+5t is odd iff t is even; h+a_t-1 = h+7+5t likewise; h is even.) In both cases the sum over a full
      period is negative (-1) and the largest sum of a cyclically consecutive stretch is j/2 (odd: the j/2 consecutive + blocks,
      or 1-1+j/2) resp. j/2-1; a block cut to a single position holds at most one member. So the excess is at most j/2.
 With (L1), (L2): P(t,y) <= 2j+1 + ceil((y-h)/2) + j/2 <= h/2 + ceil((y-h)/2) = ceil(y/2), because h/2 = ji >= 3j >= 5j/2 + 1
 (i >= 3, j >= 2) and h is even.

(B) K < y <= K+p. Put d = y-K in [1,p], s = t+K, I = [s,s+d). R is constant for y >= X, so by (1), (A1): P(t,y) = K/2 + |M n I|.
By (a), T(t,y) >= |T1 n [t,t+d-1)| = |Z1 n [s,s+d-1)|. As Z1 is a subset of M:
        |M n I| - |Z1 n [s,s+d-1)| = |M'' n I| + [s+d-1 in Z1].
By (M-b) |M'' n I| <= ceil(d/2); and if s+d-1 is in Z1 then s+d-1 and s+d-2 are non-members of M'', so |M'' n I| <= ceil((d-2)/2)
= ceil(d/2)-1 (d = 1: 0+1 = ceil(1/2)). So P-T <= K/2 + ceil(d/2) = floor((y+1)/2) (K even).

(A1)-(A3), (B) give (*): the walk of section 2 is a spread-k circuit code of length N = 4k+2l+4j in Q_n; with section 1,
K(n,k) = N. QED

## 6. The parity obstruction in general form: excess e = 2 (mod 4) never attains the bound   (added later in S170; refereed separately)

Setting of PROOF8.md section 4: l even, k odd, n = (3k+l+1)/2, e >= 2 even, N = 4k+2l+e = 4K+2u with u = l+(e-4)/2; Lemma 1 at
L = 2K holds with equality iff  (E)  K = u(2u+e)/(2e).

**Theorem 24.** (k odd, K even, as above.) Assume (E) and K >= 2u+2 (then u >= 4 and N > 4K+2). Let p = gcd(2K, N). If p divides K and N/p is odd, then there is no spread-k circuit
code of length N in Q_n.
(Theorem 17 is the special case 2u | K, where p = 2u and N/p = 2K/u+1.)

Proof. Exactly the proof of Theorem 17 / Theorem 15 with the period 2u replaced by p. By PROOF8 section 0 (valid as K >= 2u+2,
see the proof of Theorem 17): (Z1) every window of length 2K holds K/2 chords, (Z2) dot gaps are >= 2K, (Z3) F gaps are
<= K+2u <= 2K-2, (Z4) the type word has period gcd(2K, N) = p, (Z5) if t, t+1 are F positions there is a triple (x, x+, x++)
with x >= t and x++ <= t+2K+1. The fraction of F positions is 4(N/2-n)/N = (2K+2u+e)/(4K+2u) > 1/2, so in one period of the
type word there are two cyclically adjacent F positions (p is even; p = 2 would make every position an F position, but there are
2n-N/2 = K-e/2 > 0 dot coordinates [K >= 2u+2 and (E) give e < u < K]; so p >= 4 and the residues a, a+1 are distinct from a+2, a-1); fix their residues a, a+1 (mod p) and let
B be the set of the 2N/p positions with residue a or a+1; they form N/p pairs (t, t+1), t = a (mod p).
By (Z5) every pair (t,t+1) has a "serve": a triple (x, x+, x++) with x in {t, t+1}, x++ <= t+2K+1; its gaps are (K,K), (K,K+1)
or (K+1,K) (with x = t in the last two cases). As p | K, adding K preserves residues mod p, so x, x+, x++ all lie in B, and a
triple serves only one pair (x determines t: t = x or x-1 according to the residue of x; if a-1 or a+2 is also an F residue we
still only count serves of the pairs with t = a mod p). A coordinate has four positions with gap sum N = 4K+2u > 4K+2, so two
opposite pairs of consecutive gaps cannot both have sum <= 2K+1: it has at most two serves, and two only if they are
(x, x+, x++), (x+, x++, x+++), in which case all four positions are in B. A coordinate with one serve has at least 3 positions
in B. So s_c <= b_c/2 for every coordinate (s_c serves, b_c positions in B), with equality only for (s_c, b_c) = (2,4) or (0,0).
Summing: N/p <= sum s_c <= |B|/2 = N/p. Hence every s_c is 0 or 2 and sum s_c = N/p is even: contradiction. QED

**Corollary 25.** Let e = 2 (mod 4). On even lines the bound of Lemma 1 at L = 2K for excess e is never attained: if (E) holds
and K >= 2u+2 (with k odd, i.e. K even) there is no code of length 4k+2l+e.
(This removes "squarefree" from Corollary 18. For each e exactly the equality points with K <= 2u+1 are not covered.)

Proof. e = 2r with r odd; l = u-r+2 is even, so u is odd. K is even. p = gcd(2K, 4K+2u) = gcd(2K, 2u) = 2g with g = gcd(K,u),
g odd. K/g is even (K even, g odd), so p = 2g divides K. N/p = (4K+2u)/(2g) = 2(K/g) + u/g is odd because u/g is odd. Theorem 24. QED

Status of all equality points on even lines (struct/ex4/eqtable2.py EMAX UMAX; e <= 64, u <= 3000):
    e = 2 mod 4:               none (Cor 25).
    e = 4 mod 8, e/4 squarefree (4, 12, 20, 28, 44, 52, 60): every point settled: code (Cor 23, Thm 20) or none (Thm 24).
    e = 0 mod 8 (8, 16, 24, 40, 48, 56): code for u = e*i, i >= 3 (Cor 23); none when Thm 24 applies (K/u even);
                                OPEN: u = 2e, and the points with K/u odd (u = e(4w+1)/2, w >= 1: 20, 36, .. for e = 8).
    e = 32, 36, 64 (e/4 not squarefree .. more periods): further open points with p < u.

## 7. Odd lines: excess e = 0 (mod 4) never attains the bound   (added later in S170; refereed separately)

Setting: l odd, k even (K = k+1 odd), n = (3k+l+1)/2, e >= 2 even, N = 4k+2l+e = 4K+2u with u = l+(e-4)/2. On odd lines Lemma 1 is
used at L0 = 2K-1 (floor((L0-k)/2) = k/2). With N/2-n = (K+u+e/2)/2 and 4L0-N = 4K-2u-4 it reads
(K+u+e/2)(4K-2u-4) <= (4K+2u)(K-1), i.e. 2eK <= 2u^2+2u+eu+2e, with equality iff

        (E')    K = u(u+1)/e + (u+2)/2.

**Theorem 26.** Let l be odd, k even, e = 0 (mod 4), and assume (E') and K >= 2u+3. Then there is no spread-k circuit code of
length N = 4k+2l+e in Q_n. (e = 4 is Theorem 16 of PROOF8.md.)
More generally, for any even e: under (E') and K >= 2u+3, a code of length N can exist only if the number
d_p = (2K-e)p/N of dot positions per period p = gcd(2K-1, N) of the type word is EVEN. (For e = 2 mod 4 this excludes about half
of the equality points, e.g. e = 2, l = 3 mod 4; struct/ex4/oddeq.py.)

Proof. K >= 2u+3 gives N = 4K+2u < 5K < 6K and max(k, N/4) <= 2K-1 <= min(2K, N-k), so Lemma 1 applies at L0 = 2K-1, and with
(E') it is an equality; 4L0-N = 4K-2u-4 > 0. As in PROOF8 section 0 (the argument there does not use the value of e): (Z1) every window of length L0
holds exactly c0 = k/2 chords; (Z2) dot gaps are >= L0, exactly N/2-n coordinates are used four times (F), all others twice
(dots), none is unused; (Z3) F gaps are <= N-3K = K+2u <= L0-2; (Z4) the type word has period L0, hence period
p = gcd(2K-1, N), which is odd; (Z5) if t and t+1 are F positions, the window [t, t+L0+2) (length 2K+1 <= N-k; P-T <= floor((2K+1-k)/2) = c0+1 as K is odd;
dot chords inside it are harmless) contains a triple (x, x+, x++) with x >= t and x++ <= t+L0+1 = t+2K; as both gaps are >= K this forces x = t and gaps (K, K): so t+K is an F position.
(Z6) No two adjacent dots: a window [t, t+L0) holds c0 chords and [t, t+L0-2) at most floor((L0-2-k)/2) = c0-1, so a chord ends
at t+L0-2 or t+L0-1, i.e. one of any two adjacent positions is an F position.

Let w(r) in {0,1} (r in Z_p) be the type word (1 = F). Since 2K = 1 (mod p), K is invertible mod p; put v(m) = w(Km mod p). For
a = Km we have a+1 = K(m+2) and a+K = K(m+1). So (Z5) says: v(m) = v(m+2) = 1 implies v(m+1) = 1 (no "101"), and (Z6) says:
v(m) = v(m+2) = 0 never happens (no "0?0").
Claim: the number of zeros of v (= d_p) is even. If p = 1 there is no zero (F positions exist). If p = 3, two zeros would be at
distance 2 in one direction, and a single zero would give 101 around it (m-1, m, m+1); so there is no zero. Let p >= 5 and
v(m) = 0. Then v(m-2) = v(m+2) = 1 (no 0?0). If v(m-1) = v(m+1) = 1 we have 101; if v(m-1) = v(m+1) = 0 we have 0?0. So exactly
one of the two neighbours m-1, m+1 of m is a zero: "is an adjacent zero" is a perfect matching on the zeros. QED (claim)
The number of dot positions is N - 4(N/2-n) = 4n-N = 2K-e, so d_p = (2K-e)p/N.
Now let e = 0 (mod 4). d_p = (K-e/2) p / (2K+u). Here u = l+(e-4)/2 is odd (l odd, (e-4)/2 even), K is odd, so K-e/2 is odd,
p is odd and 2K+u is odd: d_p is an integer quotient of odd numbers, hence odd. Contradiction. QED

Data: (38,22), N = 114 (l = 9, e = 8) is the first such point: UNSAT by SAT in 78 s (struct/ex4/runs/skf_38_22_114.out).
Open on odd lines: the equality points with e = 2 (mod 4), e >= 6, and d_p even; the first is (70,42), N = 200 (l = 13, e = 6,
p = 5, type word .FF.F): no code invariant under x -> x+5, x+10 or x+25 (lazy SAT).

## Referee report (#23, S170) on section 7

A fresh AI agent (theory/referee23/chk.py, code.py): Theorem 26 PASS, the general 'd_p even' statement PASS; three cosmetic
additions (applied). It re-derived (E') and (Z1)-(Z6) for general e, enumerated all cyclic binary words for odd p <= 21 (zero
counts always even), verified d_p odd at all 18,887 equality points with e = 0 mod 4, e <= 200, l <= 20001, and checked every
claimed fact on two family-1 codes (e = 2, l = 9, 13), where d_p = 4, 6 and the zeros pair up as stated.

## Referee report (#21, S170) on sections 1-4 (Theorem 22, Corollary 23)

A fresh AI agent, from the text of section 2 only (theory/referee21/gen.py, ids.py, sec1.py, mut.py): Theorem 22 PASS,
Corollary 23 PASS, no error; cosmetic notes only (for (j,i) = (2,3) the 'even r' parts of E, E' are empty; (L2) uses that p is
even for the parity across periods; the section-2 rule with odd j gives a valid code in dimension n+i+1, not n -- the odd-j
family of section 5 is a different rule). Checks: all-pairs validity on vertices for (j,i) = (2,3..6), (4,3..5), (6,3), (6,4), (8,3);
every identity of sections 2-4 with P, T, odd counted on the walk for 16 cases up to (16,3), all y, (L2) for lengths up to 3p
(the bound j/2 is attained); section 1 in exact integers for j <= 12, i <= 14; i = 2 is not a partition.

## Referee report (#22, S170) on section 6

A fresh AI agent (theory/referee22/arith.py, zcheck.py): Theorem 24 PASS, Corollary 25 PASS; one wrong formula in the status list
(u = e(4w+1)/2; fixed). It re-derived (Z1)-(Z5) in the general setting, checked the counting, verified by brute force that all
21956 equality points with e = 2 mod 4, e <= 400, u <= 20000, K >= 2u+2 satisfy Theorem 24's hypotheses, that no known code is
excluded (8 codes), and (Z1)-(Z5) numerically on six code files.

## 5. Remarks

* (A1) holds for ANY disjoint union of ladders of the three types (the identity is per ladder), with any E; (A2) is (M-a).
  So a "design" (ladders + E + antipodal dots, period p, K = h mod p) is a code iff (A3) and (B) hold. Necessary: every adjacent
  member pair of M is one ladder's own pair (B with d = 2), hence E' is forced (alternate in every run between ladder points).
  struct/ex4/design3.py enumerates designs this way: e = 16, p = 48: 46 designs; p = 64: 1036. The family above (the excess-8
  design A0 B4 C8 plus C ladders at spacing 5) is one convenient choice.
* For odd j the analogous family is C(5t), t = 0..j-1 (ladfam.py; VALID j = 1, 3, 5, 7, i = 3, 4; not needed for Corollary 23).
* i = 2: no code of this kind (e = 16, p = 32: design3 finds none with 3, 4 or 5 ladders); the equality point (132,79,384) is open.
* Machine checks: struct/ex4/lem22.py tests every displayed set, identity and inequality of sections 1-4 for all t, y
  (runs/lem22_*.out); snake/check.py VALID on codes/lad_j4_i3.txt (272,167,768), lad_j6_i3.txt (408,251,1152), lad_j8_i3.txt (544,335,1536).

## S172 addendum (2026-11-11): Theorems 24 and 26 are machine-checked, with weaker hypotheses and a new counting step

Lean 4 files lean/Ccformal/Parity.lean, Cor25.lean, Thm26.lean, Thm33a.lean (kernel-checked).
(1) Theorem 24 holds under 2 <= u < K (i.e. 4K+2 < N < 6K) instead of K >= 2u+2. (Z3) is not needed: "every F coordinate occurs in
    every window of length 2K" follows directly from equality in Lemma 1 (count_c(W) <= 1 + [count_c(W) = 2], summed over windows).
    So e.g. (40,23,120) [K = 2u; formerly SAT] is covered. In general (Thm33a.lean): at an even-line equality point with 2 <= u < K,
    K/gcd(K,u) even => no code.
(2) New proof of the counting step (replaces 's_c <= b_c/2'): choose one serve (x_t, y_t, z_t) for every pair t = a (mod p).
    X = {x_t}, Z = {z_t} (mod N) are subsets of B (the 2N/p positions of residues a, a+1), each of size N/p (a start determines its
    pair; z determines y and x because congruent occurrences have the same previous occurrence), and they are disjoint (x_t' = z_t
    would give five occurrences of one coordinate in one period, span <= 4K+2 < N). Hence B = X u Z. Every middle y_t lies in B:
    if y_t = x_t' the serve of t' starts where the serve of t has its middle; if y_t = z_t'' then y_t'' = x_t. Not both (that would
    put z_s in X). So 'y_t = x_t'' is a perfect matching on the N/p pairs, and N/p is even.
(3) Theorem 26 holds for 3K <= N < min(6K, 8K-4) (no K >= 2u+3). The matching on dots is stated without v(m) = w(Km): for a dot t
    exactly one of the adjacent positions t+k, t+k+1 is a dot (not both: Z6; not none: FF at t+k forces F at t+k+K = t+L0 = t mod p).
