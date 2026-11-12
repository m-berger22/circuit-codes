# Family 4 is valid for every l = 2 (mod 4), l >= 10                                   (S168, 2026-11-10 23:05)

Continuation of PROOF3.md / PROOF4.md (same notation and the same three steps). Checks: struct/even/fam5lem.py (third argument 4),
fam4cyc.py, evenfam2.py.

THEOREM 12. Let l = 2 (mod 4), l >= 10, k = (l^2-l-8)/2, n = (3k+l+1)/2. The word T defined below is the transition sequence of
a spread-k circuit code of length N = 4k+2l+2 = 2l^2-14 in Q_n.
COROLLARY. K(n,k) = 4k+2l+2 there (upper bound: Lemma 1 with f(4) = 2l^2-8l-24 > 0, f(k+4-2l) > 0, Lemma 2), and
(l^2-l-8)/2 <= k_max(l) <= (l^2-l-4)/2 for EVERY l = 2 (mod 4), l >= 10 (the upper bound is the Main Theorem; the upper value is
attained for l = 6, 10, .., 30 and 38 by the solver codes of S167; whether it is attained for all l is open).

## Definition (evenfam2.py)
p = l-1, h = l/2 (odd, >= 5), K = k+1 = p h - 3, H = N/2 = p l + p - 6 = 2K + p, N - 4K = 2p.
Positions (i,r) = p i + r: periods i = 0..l-1 of length p and a short period i = l of length p-6 (r = 0..p-7). TYPE: in a period r is F
iff r is odd or r = p-1; in the short period iff r is odd (<= p-8) or r = p-7. Dots are antipodal (gap H). F rows, x+ = x + K + e:
   A (i < h):        r=1: 1;  r=3: h-2;  r=5: 2p-4 (p-1 if i = h-1);  odd 7 <= r <= h: p-1;  odd h+2 <= r <= p-4: 1;  r=p-2: 1;
                     r=p-1: 5 (3 if i = h-1)
   B (h <= i < l):   r=1: 2p-6;  odd 3 <= r <= h-4: 1 (h-2 if i = h);  r=h-2: h+1;  odd h <= r <= p-6: p-1;  r=p-4, p-2: 0;
                     r=p-1: 3 (2p-4 if i = l-1)
   S (i = l):        odd 1 <= r <= h-4: 1;  odd h-2 <= r <= p-8: h+1;  r=p-7: 5.
(In evenfam2.py q = (l-10)/4 and 2q+3 = h-2, p-2q-3 = h+1. For l = 10: h = 5, the ranges 7..h and 3..h-4 are empty; row 3 of A has
e = h-2 = 3 and row 3 = h-2 of B has e = h+1 = 6.) The second half repeats the first; primes = other half.

## Step C
(i,r) + K + e = p(i+h) + (r-3+e);  p(l+1) + c = H + c + 6.  2-cycles need e + e' = p (= H - 2K):
 (D1) A, 7 <= r <= h [p-1], and (h-1,5) [p-1]: -> (i+h+1, r-4), a row 1 <= r-4 <= h-4 of B (periods h+1..l-1) or of S (i = h-1), e' = 1.
 (D2) A, h+2 <= r <= p-4 [1]: -> (i+h, r-2), a row h <= r-2 <= p-6 of B, e' = p-1.
 (D3) (i,3), A [h-2] -> (i+h, h-2), B, e' = h+1.
 (D4) (h,r), 3 <= r <= h-4 [h-2] -> (l, r+h-5), a row h-2 <= r+h-5 <= p-8 of S, e' = h+1.
 4-cycles (e sum to 2p = N-4K):
 (E1) 1 <= i <= h-1: (i,1) [1] -> (i+h-1, p-1) [B, i+h-1 <= l-2: 3] -> p(i+l)-1 = H + (i-1,5) [A, i-1 <= h-2: 2p-4]
      -> (i+h, p-2)' [0] -> H + p(i+l)+p-5 = N + (i,1).
 (E2) (0,1) [1] -> (h-1,p-1) [3] -> (l-1,p-1) [2p-4] -> p(l+h+1)+p-8 = H + (h,p-2) [0] -> H + p l + p - 5 = N + (0,1).
 (E3) i <= h-2: (i,p-1) [5] -> (i+h+1,1) [2p-6] -> p(i+l+2)+p-8 = H + (i+1,p-2) [A, 1] -> (i+h+1,p-4)' [0]
      -> H + p(i+l+1)+p-7 = N + (i,p-1).
 (E4) (0,p-2) [1] -> (h,p-4) [0] -> (l,p-7) [S, 5] -> p l + p h + p - 5 = H + (h,1) [2p-6] -> H + p l + 2p - 8 = N + (0,p-2).
 Coverage. A: 1 (E1, E2), 3 (D3), 5 (E1; i = h-1: D1), 7..h (D1), h+2..p-4 (D2), p-2 (E3 for i >= 1, E4 for i = 0), p-1 (E3; i = h-1: E2).
 B: 1 (E3; i = h: E4), 3..h-4 (D1; i = h: D4), h-2 (D3), h..p-6 (D2), p-4 (E3; i = h: E4), p-2 (E1; i = h: E2), p-1 (E1; i = l-1: E2).
 S: 1..h-4 (D1), h-2..p-8 (D4), p-7 (E4). Every F row occurs once; F positions per half: l h + h - 3 = (l^2+l-6)/2 = 2(n-k).

(As in PROOF3 'What has to be shown': gaps >= K settle L <= K, and for K < L <= H we need ch(W) - tr(W) <= floor((L-k)/2).)

## Steps 2 and 3 (K+2p < L <= H; all gaps are <= K+2p-4)
No two adjacent dots; FF pairs: the last two letters of every period (short one included); spacings p, except p-6 from period l-1
to the short period; l+1 pairs per half. Delta(W) = c + (eps(first)+eps(last))/2; needed: Delta <= l + 2tr (L even), l+1+2tr (L odd).
 Step 2 (L <= 2K = p l - 6): l+1 pairs span >= p l - 4 > 2K, so c <= l, Delta <= l+1, and Delta <= l for even L (parity).
 Step 3 (L <= H): l+2 pairs span H+2, so c <= l+1; only even L with c = l+1 and both ends F needs a triple. W0 as in PROOF3:
   |W0| = 2K+2, or 2K+8 if its first pair u is the pair (l,p-8),(l,p-7) of the short period; condition x-u+e(x)+e(x+) <= |W0|-1-2K.
     u = (i,p-2), i < h: e = 1, u+ = (i+h,p-4) with e = 0 (E3, E4): 1 <= 1.
     u = (i,p-2), i >= h: e = 0, u+ is a row 1 of A with e = 1 (E1, E2): 1 <= 1.
     u = (l,p-8): x = u+3 = (0,1)' [1], x+ = (h-1,p-1) [3] (E2): 3 + 4 <= 7.

## Step 1 (1 <= y <= 2p): X(J) >= floor(Delta(J)/2), X(J) = number of F positions x of J = [t,end] with x + e(x) > end (PROOF4)
 (i) Three FF pairs span >= 2p-4 positions and then include the short spacing; four span > 2p. So c <= 3, Delta <= 4, and two
   leaving chords are needed only if c = 3 and both ends of J are F.
 (ii) For every end, the positions after the start of the nearest leaving chord (the 'dead stretch') contain no FF pair:
   A period, end at residue rho: rho odd or rho = p-1: the row rho itself leaves (e >= 1). rho = 0: the last row of the previous
   period leaves (it is a row p-1 with e = 5, or the row p-7 of the short period, e = 5, at distance 1). rho = 2: row 1 is dead
   (e = 1) and the same row of the previous period leaves (5 > 3; the period before an A period is an A period with i <= h-2 or
   the short period); the stretch after it is {0,1,2}. rho = 4: row 3 (h-2 > 1). 6 <= rho <= h+1: row rho-1 (2p-4 or p-1).
   h+3 <= rho <= p-3: the rows h+2..rho-1 are dead (e = 1); row h (p-1) leaves, or row 5 if h = 5; the stretch lies in [h+1, p-3].
   B period: rho odd or rho = p-1: the row leaves unless e = 0 (rho = p-4, p-2): then row p-6 leaves (e = p-1, or h+1 = 6 > 4 if
   l = 10). rho = 0: the row p-1 before it leaves (3 > 1). rho = 2: row 1 (2p-6) leaves. 4 <= rho <= h-3 (for i = h the row rho-1
   already leaves): row 1 leaves, stretch in [2, h-3]; h-1 <= rho <= p-3: row h-2 (h+1) or a row >= h (p-1)
   leaves from distance <= h, the stretch lies in [h-1, p-3].
   S: rho odd or p-7: the row leaves. rho even, rho <= h-3: rows 1..h-4 are dead, the row (l-1,p-1) (2p-4) leaves, the stretch
   is (l,0..rho);
   rho >= h-1: a row >= h-2 (h+1) leaves from distance 1.
   Hence if J contains an FF pair, the nearest leaving chord starts in J:  c >= 1  =>  X(J) >= 1.
 (iii) c = 3, both ends F. The three pairs are (l-2,p-2), (l-1,p-2), (l,p-8), or (l-1,p-2), (l,p-8), (0,p-2)'.
   First case: end is an F position of S or of the period 0' and t <= (l-2,p-2), so end <= (l-1,p-1) + p - 2. S and A have no row with
   e = 0, so end leaves; and (l-1,p-1) [2p-4] leaves as well.
   Second case: end is one of (0,p-1)', (1,1)', (1,3)' (J has at most 2p positions). end leaves (e >= 1). If end != (0,p-1)' then
   (0,p-1)' [5] leaves too (distance <= 4); if end = (0,p-1)' then (0,5)' [2p-4] leaves.
 So X(J) >= floor(Delta(J)/2) always. QED

REFEREE #14 (independent agent, S168 22:53): NO MATHEMATICAL ERROR; three wording defects in Step 1 (ii) and two elsewhere, fixed above.
It rebuilt the code from the written definition only (identical to evenfam2.py up to renaming, l = 10..102), validated it with its
own all-windows C checker for all 24 values of l, re-derived (D1)-(D4), (E1)-(E4) and checked them and the coverage by program,
brute-forced Steps 2-3 for l = 10..102 (1.05e8 windows at l = 102; the windows needing a triple are exactly the claimed ones),
compared Step 1 (ii) with the code residue by residue, and checked ch <= floor((y+1)/2), X >= floor(Delta/2), 'c >= 1 => X >= 1'
directly for all t, y, l = 10..102 (floor(Delta/2) = 2 occurs in exactly 24 windows per l, the two cases of (iii)).
