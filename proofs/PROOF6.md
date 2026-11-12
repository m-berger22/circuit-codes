# PROOF6 (S169, 2026-11-10 night): an explicit family of EXCESS-4 codes; the excess-4 bound of Lemma 1 is sharp

Notation as in PROOF.md / STATUS.md: a spread-k circuit code ("coil") of length N in Q_n is a closed walk v_0..v_{N-1} with
d_H(v_i, v_j) >= min(k, cyclic distance(i,j)); K(n,k) = the maximum N; the line of (n,k) is l = 2n-3k-1; Byrnes' value is
4k+2l. T_x = the coordinate flipped between v_x and v_{x+1} (transition word, x in Z_N); K = k+1.

## Theorem 13

Let l = 0 (mod 4), l >= 8, k = (l^2+2l-4)/4, n = (3k+l+1)/2 = (3l-2)(l+4)/8. Then

        K(n,k) = 4k + 2l + 4 = l(l+4).

So Byrnes' formula is exceeded by 4 for infinitely many (n,k), and the bound "a code of length 4k+2l+4 on an even line needs
k <= (l^2+2l-4)/4" (Lemma 1 with L = 2K; PROOF2 sec. 4) is attained for every l = 0 mod 4.
First cases: (33,19) 96 [found by SAT in S165], (68,41) 192, (115,71) 320, (174,109) 480.

## 1. Upper bound

k is odd (l = 4q gives k = 4q^2+2q-1).
k > 3l-7 for l >= 8 (k - 3l + 7 = (l^2-10l+24)/4 = (l-4)(l-6)/4 > 0), so Lemma 2 (PROOF.md) gives N <= 5k+3.
For an even N = 4k+2l+e with 4 <= e <= k+3-2l apply Lemma 1 with L = 2K = 2k+2 (N < 6K, N/4 <= L <= min(2K, N-k)):
it requires  f(e) := (N/2-n)(4L-N) - N floor((L-k)/2) <= 0, where N/2-n = (k+l-1+e)/2, 4L-N = 4k+8-2l-e,
floor((L-k)/2) = (k+1)/2.  Expanding, 2 f(e) = (k+l-1+e)(4k+8-2l-e) - (4k+2l+e)(k+1), and
        2f(e) - 2f(4) = (e-4)(2k+4-3l-e),        f(4) = 4k+4-l^2-2l = 0   for k = (l^2+2l-4)/4.
For 6 <= e <= k+3-2l the second factor is >= 2k+4-3l-(k+3-2l) = k+1-l > 0, so f(e) > 0: every such length is excluded.
Hence K(n,k) <= 4k+2l+4.

## 2. The code

K = k+1 = l(l+2)/4, N = l(l+4) = 4K+2l, N/4 = K + l/2, N/2 = 2K + l, and K = l/2 (mod l) (K = l*(l/4) + l/2).
Define a gap function g on Z_N that depends only on the residue r = x mod l:

    r = 1:                 g = K
    r = 2:                 g = K + 2l - 2
    r = l/2, l/2+1:        g = K + 1
    r in E:                g = N/4          E = {even r, 4 <= r <= l/2-2}  u  {odd r, l/2+3 <= r <= l-1}      (|E| = l/2-3)
    r in D:                g = N/2          D = {0, 3}  u  {odd r, 5 <= r <= l/2-1}  u  {even r, l/2+2 <= r <= l-2}   (|D| = l/2-1)

and s(x) = x + g(x). On residues s acts as 1 -> l/2+1 -> 2 -> l/2 -> 1 (1+K = l/2+1; l/2+1+K+1 = 2; 2+K+2l-2 = l/2;
l/2+K+1 = 1, all mod l) and fixes every residue in E and D (N/4 = l(l+4)/4 and N/2 are multiples of l). So s is a
permutation of Z_N; its orbits have 4 elements on the residues {1, 2, l/2, l/2+1} (gap sum K+(K+1)+(K+2l-2)+(K+1) = N:
"ladder" coordinates, l+4 of them), 4 elements on E (equally spaced, gap N/4) and 2 elements on D (antipodal "dots").
Let T_x = the orbit of x. Every coordinate is used an even number of times, so the walk closes; the number of coordinates is
(l+4) + (l/2-3)(l+4)/4 + (l/2-1)(l+4)/2 = (l+4)(3l-2)/8 = n. The code is invariant under x -> x+l (up to relabelling).
(struct/ex4/ex4fam.py builds it.)

## 3. Reduction to a counting statement

All gaps are >= K, so a window of length <= k has distinct coordinates. Since every coordinate is used an even number of
times, a window and its complement have the same set of odd coordinates; so it suffices to show odd(W) >= k for every window
W = [t, t+L) with K <= L <= N/2 = 2K+l (a complement of length <= k has distinct coordinates). Write L = K+y, 0 <= y <= K+l.

Multiplicities in such a window: a dot occurs at most once (its two positions are N/2 apart and L <= N/2). An E coordinate
occurs at most twice (three positions span N/2+1 > L positions). A ladder coordinate occurs at most 3 times (three consecutive gaps sum to at
least N-(K+2l-2) = 3K+2 > N/2), and 3 times only as x, s(x), s^2(x) with consecutive gaps (K, K+1) or (K+1, K), i.e.
x = 1 or l/2 (mod l), span 2K+1 (the other two-gap sums are 2K+2l-1 > N/2 - 1).
Let P(W) = number of "chords" x with x and s(x) both in W (x >= t, x+g(x) <= t+L-1) and T(W) = number of triples
x, s(x), s^2(x) in W. A coordinate occurring twice contributes one chord, one occurring three times two chords and one
triple; so  odd(W) = L - 2(P(W) - T(W)),  and the claim odd(W) >= k is

    (*)     P(t,y) - T(t,y) <= floor((y+1)/2)      for all t and 0 <= y <= K+l.

For a set S of residues let |S n [a,b)| be the number of integers x in [a,b) with x mod l in S (0 if b <= a). A chord of
length c starting at x lies in W iff t <= x < t+L-c. Hence

    P(t,y) = |{1} n [t,t+y)| + |{l/2, l/2+1} n [t,t+y-1)| + |E n [t,t+y-l/2)| + |{2} n [t,t+y-2l+2)|,
    T(t,y) = |{1, l/2} n [t, t+y-K-1)|.

Shift each family so that its strip ends at t+y (x -> x+1, x+l/2, x+2l-2 respectively). With

    E' = E + l/2 = {odd r, 3 <= r <= l/2-1}  u  {even r, l/2+4 <= r <= l-2},
    M  = {0, 1, l/2+1, l/2+2}  u  E'            (|M| = l/2+1),

    (1)     P(t,y) = |M n [t,t+y)| - R(t,y),
            R(t,y) = [y >= 1 and t = l/2+1 or l/2+2 (mod l)] + |E' n [t, t+min(y, l/2))| + |{0} n [t, t+min(y, 2l-2))|

(R counts the members of M in [t,t+y) that lie before the start of their shifted strip).
In residue order M is  0, 1, 3, 5, .., l/2-1, l/2+1, l/2+2, l/2+4, .., l-2: the odd numbers of [1, l/2+1] and the even numbers of
[l/2+2, l]. Three facts:
    (M-a) M has no two cyclically adjacent NON-members.
    (M-b) M'' = M \ {0, l/2+1} = {odd r in [1, l/2-1]} u {even r in [l/2+2, l-2]} has no two adjacent MEMBERS, and
          l-1, 0 and l/2, l/2+1 are two pairs of adjacent non-members of M''.
    (M-c) M' = M \ {0}: the only adjacent members are l/2+1, l/2+2; the only adjacent non-members are l-1, 0.

## 4. Proof of (*)

K is even (K = 2q(2q+1), l = 4q) and K >= 2l-2 (l >= 8).

(A1) y = K: P(t,K) = K/2 for every t (and T = 0).
K = l*(l/4) + l/2, so |M n [t,t+K)| = (l/4)(l/2+1) + |M n [t,t+l/2)|, and R(t,K) = |E' n [t,t+l/2)| + z(t) + d(t), z(t) = number of
multiples of l in [t, t+2l-2), d(t) = 1 if t = l/2+1, l/2+2 (mod l), else 0. So P(t,K) = l^2/8 + l/4 + |{0,1,l/2+1,l/2+2} n [t,t+l/2)| - z(t) - d(t),
and K/2 = l^2/8 + l/4. With r = t mod l in [1, l]: z = 1 for r = 1, 2 and z = 2 for 3 <= r <= l. The set {0,1,l/2+1,l/2+2}
meets [t, t+l/2) in: r = 1: {1}; r = 2: {l/2+1}; 3 <= r <= l/2: {l/2+1, l/2+2}; r = l/2+1: {l/2+1, l/2+2, l}; r = l/2+2:
{l/2+2, l, l+1}; l/2+3 <= r <= l: {l, l+1}. In every case the count equals z + d. QED (A1)

(A2) 2l-2 <= y <= K. R(t,y) does not depend on y in this range, so by (1) P(t,K) - P(t,y) = |M n [t+y, t+K)| >= floor((K-y)/2)
by (M-a). Hence P(t,y) <= K/2 - floor((K-y)/2) = ceil(y/2) = floor((y+1)/2); T = 0.

(A3) 0 <= y <= 2l-2. The last term of P vanishes, so P(t,y) = |M' n J| - R'(t,y), J = [t,t+y),
R'(t,y) = [y >= 1 and t = l/2+1 or l/2+2] + |E' n [t, t+min(y,l/2))|; T = 0.
Cut J into consecutive pairs {t,t+1}, {t+2,t+3}, .. (ceil(y/2) blocks, the last possibly a single position, which holds at most one member and is never counted as special). Then
|M' n J| <= ceil(y/2) + (number of blocks with two members) - (number of full blocks with no member).
If t is even no block has two members (by (M-c) such a block is {l/2+1, l/2+2} + jl, which starts at an odd position), so
P <= ceil(y/2). If t is odd, the blocks start at odd residues; by (M-c) the blocks starting at l/2+1 have two members, those
starting at l-1 have none, all others exactly one, and these two special kinds alternate along Z. So the difference is <= 1,
and it is 1 only if the first special block in J is a full block starting at l/2+1 (mod l); then r = t mod l is odd with
1 <= r <= l/2+1 and y >= l/2+3-r. In that case R' >= 1:  r = l/2+1 gives the first term; 3 <= r <= l/2-1 gives t in E' (y >= 1);
r = 1 gives t+2 in E' (3 <= l/2-1) with t+2 < t+min(y, l/2) since y >= l/2+2 and l/2 >= 4.
Hence P <= ceil(y/2) = floor((y+1)/2).

(B) K < y <= K+l. Put d = y-K in [1, l], s = t+K, I = [s, s+d). R is constant for y >= 2l-2, so by (1) and (A1)
P(t,y) = K/2 + |M n I|. Since K = l/2 (mod l), T(t,y) = |{1, l/2} n [t, t+d-1)| = |Z n [s, s+d-1)| with Z = {l/2+1, 0}.
Therefore   P - T = K/2 + |M'' n I| + [s+d-1 in Z].
By (M-b) |M'' n I| <= ceil(d/2). If the last position s+d-1 of I is in Z, then s+d-1 and s+d-2 are both non-members of M''
(the pairs l-1, 0 and l/2, l/2+1), so |M'' n I| <= ceil((d-2)/2) = ceil(d/2) - 1 (for d = 1 simply |M'' n I| = 0).
In both cases P - T <= K/2 + ceil(d/2) = floor((K+d+1)/2) = floor((y+1)/2), as K is even.

(A1)-(A3), (B) give (*) for all 0 <= y <= K+l, so the walk of section 2 is a spread-k circuit code of length l(l+4) in Q_n.
With section 1, K(n,k) = l(l+4) = 4k+2l+4. QED

## 5. Remarks

* Zero slack: equality in Lemma 1 at L = 2K forces every 2K-window to hold exactly K/2 chords (this is (A1)), every dot
  gap >= 2K, and therefore a type word of period gcd(2K, N) = 2 gcd(K, l): = l for l = 0 mod 4, = 2l for l = 2 mod 4.
* How it was found (S169): the SAT code (33,19,96) of S165 turned out to be invariant under x -> x+8; an exhaustive search of
  codes invariant under x -> x+l (struct/ex4/shsearch3.c: the code is a gap function on residues) gave 4 skeletons at l = 12,
  and the pattern above was read off from l = 8 and 12.
* l = 2 mod 4: the same k = (l^2+2l-4)/4 is zero slack. l = 10: no code invariant under x -> x+10 (exhaustive), but
  K(49,29) = 140 = 4k+2l+4 (codes/skel_49_29_140.txt, SAT), with type word (FF.FF.FF.FF.F.F.F.F.)^7 of period 20.
* Machine checks: ex4fam.py builds the code and checks the definition (l = 8..120, 200, 300); snake/check.py (independent)
  VALID for l = 12, 16, 20, 24, 40 (codes/x4fam_*); struct/ex4/ex4lem.py tests every displayed identity and inequality of
  sections 1-4 for all t, y (l = 8..44).

## Referee report (#15, S169)

A fresh AI agent, working from this text only (own generator and checker, theory/referee15/gen.py, lem.py): PASS. One fix
(sec. 1: 'f(4) = ..', not '2f(4) = ..'; applied) and four wording nits (applied). Its checks: definition by all pairs, no symmetry
shortcut, l = 8..64; brute force of odd = L-2(P-T) and the P, T formulas for every t in Z_N and every L, l = 8..24; every
identity and inequality of (1), (M-a/b/c), (A1)-(A3), (B) for l = 8..76; section 1 in exact integers l = 8..76.
The first remark of section 5 (zero slack forces the type-word period) is not used in the theorem and was not refereed.
NO HUMAN HAS READ THIS.
