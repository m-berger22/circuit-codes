# Family 5 is valid for every l = 3 (mod 4), l >= 15: k_max(l) = (l^2-l-6)/2 on these lines   (S168, 2026-11-10 23:00)

Continuation of PROOF.md / PROOF2.md / PROOF3.md (same notation). Lemma checks: struct/even/fam5lem.py, fam5cyc.py, fam5tab.py.

THEOREM 11. Let l = 3 (mod 4), l >= 15, k = (l^2-l-6)/2, n = (3k+l+1)/2. The word T defined below is the transition sequence of
a spread-k circuit code of length N = 4k+2l+2 = 2l^2-10 in Q_n.
COROLLARY. For l = 3 (mod 4), l >= 15: K(n,k) = 4k+2l+2 at k = (l^2-l-6)/2 (upper bound: Lemma 1 with f(4) = 2l^2-10l-24 > 0,
f(k+4-2l) = k(k+5-3l) > 0, and Lemma 2, which needs k > 3l-3: true for l >= 8), and with Theorems 8, 9 and section 2 of PROOF2:  k_max(l) = (l^2-l-6)/2  exactly.
(l = 7, 11: the same value, by the solver codes (31,18,88), (84,52,232).)
Proof status: Steps C, 2, 3 by hand for all l >= 15; Step 1 by hand for l >= 27 (inspection of the rows with e <= 10),
l = 15, 19, 23 by the direct computer check.

## Definition (oddfam.py)
h = (l-1)/2 (odd), K = k+1 = l h - 2, H = N/2 = l^2 - 5 = 2K + l - 1, N - 4K = 2l-2.
Positions of the first half: (i,r) = l i + r; periods i = 0..l-2 of length l (r = 0..l-1) and a short period i = l-1 of length l-5
(r = 0..l-6). TYPE: in a full period r is F iff r = 0 or r is odd (word FF(.F)^((l-3)/2).); in the short period iff r = 0,
r odd <= l-8, or r = l-7. Dots at t and t+H carry the same coordinate. For an F position x the next occurrence of its coordinate
is x + K + e(x); regimes A: i <= h-2, a: i = h-1, b: i = h, B: h+1 <= i <= l-2, S: i = l-1:
   A, a:  r=0: 0;  r=1: l+6;  r=3: 0;  r=5: l-7 (a: 2l-8);  odd 7 <= r <= (l+3)/2 ['lo']: l+3-2r;
          odd (l+7)/2 <= r <= l-6 ['hi']: 2l+3-2r;  r=l-4: l+6 (a: 7);  r=l-2: 7 (a: 0)
   B:     r=0: 0;  r=1,3,5: l-8;  odd 7 <= r <= h-2 ['lo']: l-2-2r;  odd h <= r <= l-4 ['hi']: 2l-2-2r;  r=l-2: 0
   b:     r=0: 0;  r=1: 4;  odd 3 <= r <= h-4: h-1;  r=h-2: h-2;  odd h <= r <= l-4 ['hi']: 2l-2-2r;  r=l-2: 0
   S:     r=0: 0;  r=1: l-8;  r=3: 2l-6;  r=5: l-8;  odd 7 <= r <= h-2 ['lo']: l-2-2r;  odd h <= r <= l-8 ['mid']: h+1;  r=l-7: h+2.
(For l = 15 the b rows are 0, 1, 3 [e = h-1], 5 = h-2, hi, l-2.) The second half has the same rule (e(x+H) = e(x); its F coordinates are different ones, its dots the same); primes = other half.

## Step C: every F coordinate is used exactly 4 times, gaps sum to N
(i,r) + K + e = l(i+h) + (r-2+e), and l*l + c = H + (c+5). A pair x, x+ with e(x) + e(x+) = l-1 gives x++ = x + H ('2-cycle':
the cycle is x, x+, x+H, x+ + H).
 2-cycles:
 (T1) A or a, lo row r:  -> (i+h, l+1-r), a hi row (h <= l+1-r <= l-6) of b (i = 0) or B, with e' = 2r-4.   e+e' = l-1.
 (T2) (i,5), i <= h-2 [l-7] -> (i+h, l-4), hi row with e' = 6.
 (T3) A, hi row r: -> (i+h, 2l+1-r) = (i+h+1, l+1-r), a lo row (7 <= l+1-r <= h-2) of B (periods h+1..l-2), e' = 2r-l-4.
 (T4) (i,l-2), i <= h-2 [7] -> (i+h, l+3) = (i+h+1, 3), B, e' = l-8.
 (T5) (l-1,1) [S, l-8] -> l(l+h) - 9 = H + l h - 4 = (h-1, l-4)', a, e' = 7.
 (T6) (l-1,l-7) [h+2] -> l(l+h) + h - 7 = H + (h, h-2), b, e' = h-2.
 (T7) S, mid row r [h+1] -> l(l-1+h) + r + h - 1 = H + (h, r-h+3), b, 3 <= r-h+3 <= h-4, e' = h-1.
 (T8) S, lo row r [l-2-2r] -> l(l+h) - 4 - r = H + (h-1, l+1-r), a hi row of a (h+4 <= l+1-r <= l-6), e' = 2r+1.
     (T3 for i = h-1 is T8 read backwards: a hi row of a goes to (l-1, l+1-r), a lo row of S.)
 4-cycles (the four e sum to 2l-2 = N-4K):
 (Q1) for 1 <= i <= h:  (i,0) [0] -> (i+h-1, l-2) [b or B, 0] -> l(i+l-2)+l-4 = H + (i-1, 1) [A or a, l+6]
      -> (i+h-1, l+5)' = (i+h, 5)' [B, or S for i = h; l-8] -> l(i+l-1)+l-5 + H = N + (i,0).
 (Q2) (0,0) [0] -> (h-1, l-2) [a, 0] -> (l-2, l-4) [B hi, 6] -> l(l+h-1) = H + (h-1, 5) [a, 2l-8] -> H + l(l-2)+2l-5 = N + (0,0).
 (Q3) for 1 <= i <= h-1:  (i,3) [0] -> (i+h, 1) [B, l-8] -> l(i+l-1)+l-9 = H + (i-1, l-4) [A, l+6]
      -> (i+h-1, 2l)' = (i+h+1, 0)' [B, or S for i = h-1; 0] -> H + l(i+l)-2 = N + (i,3).
 (Q4) (0,3) [0] -> (h, 1) [b, 4] -> (l-1, 3) [S, 2l-6] -> l(l+h+1) - 5 = H + (h+1, 0) [B, 0] -> H + l*l - 2 = N + (0,3).
 Coverage: rows 0: period 0 (Q2), 1..h (Q1), h+1 (Q4), h+2..l-1 (Q3). Rows 1: A, a (Q1), b (Q4), B (Q3), S (T5). Rows 3: (0,3) Q4,
 periods 1..h-1 Q3, b T7, B T4, S Q4. Rows 5: A T2, a Q2, b T7 (T6 if l = 15), B and S Q1. A: lo T1, hi T3, l-4 Q3, l-2 T4.
 a: lo T1, hi T8, l-4 T5, l-2 Q2. b: 3..h-4 T7, h-2 T6, hi T1/T2, l-2 Q1. B: lo T3, hi T1/T2 and (l-2,l-4) Q2, l-2 Q1.
 S: lo T8, mid T7, l-7 T6. Each F row occurs exactly once, so every F coordinate is used 4 times with gaps >= K summing to N.
 F positions per half: (l-1)(h+1) + (h-1) = (l^2+l-4)/2, i.e. 4(n-k) in all; k dot coordinates; t -> t+H is an automorphism.

## What has to be shown (as in PROOF3)
For every window W = [t,t+L), K < L <= H:  ch(W) - tr(W) <= floor((L-k)/2)   (odd(W) = L - 2ch(W) + 2tr(W); dots occur at most
once, F coordinates at most 3 times since 3K > H). L = K+y.

## Step 2 and Step 3: K+2l-2 < L <= H  (every F coordinate occurs in W: all gaps are <= K+2l-6)
odd(W) >= k iff Delta(W) := 2F(W) - L <= l + 2tr(W) (L odd), l+1+2tr(W) (L even).
The type word has no two adjacent dots; its FF pairs are (i,0),(i,1) for every period i (including the short one) and
(l-1,l-8),(l-1,l-7). Consecutive FF pairs are l apart, except: l-8 from the start of the short period to its second pair, and 3
from there to the start of the next half. There are l+1 pairs per half, the l+1 spacings add up to H.
Delta(W) = c + (eps(first)+eps(last))/2, c = number of FF pairs inside W.
 Step 2 (L <= 2K): l+1 pairs span H - (one spacing) + 2 >= H - l + 2 = 2K+1 positions, so c <= l, Delta <= l+1, and by parity
   Delta <= l for odd L. tr = 0.
 Step 3 (2K < L <= H): l+2 pairs span H+2 positions, so c <= l+1, Delta <= l+2; for even L, Delta <= l+1 by parity. For odd L,
   Delta = l+2 needs c = l+1 and both ends F; then W contains the window W0 from the first letter u of its first FF pair to the
   second letter of the l-th pair after it, |W0| = H + 2 - (spacing before u), and a triple (x,x+,x++) lies in W0 iff
   x - u + e(x) + e(x+) <= |W0| - 1 - 2K.
     u = (i,0), i >= 1: |W0| = 2K+1; e(u) = 0 and e(u+) = 0 (see below).
     u = (0,0): |W0| = 2K+l-2; e(u) = 0, e(u+) = 0 (Q2).
     u = (l-1,l-8): |W0| = 2K+9; x = u+3 = (0,0)' with e(x) = e(x+) = 0: 3 <= 8.
   (Row 0 of any period has e = 0 and its successor has e = 0: in Q1, Q2 the successor is a row l-2 of a, b or B; in Q3, Q4 the
   successor of the row (i+h+1,0) resp. (h+1,0) is a row 3 of A or a, e = 0.)

## Step 1: K < L <= K+2l-2 (1 <= y <= 2l-2):  ch(W) <= floor((y+1)/2)
Let J = [t, end] be the y positions t..t+y-1 and call the interval [x, x+e(x)] the chord of the F position x. ch(W) is the number
of chords contained in J. Every F position of J starts a chord, so ch(W) = F(J) - X(J), X(J) = number of x in J with
x + e(x) > end ('leaving' chords). With Delta(J) = 2F(J) - y = c + (eps(t)+eps(end))/2 (for y >= 2) the claim is
        X(J) >= floor(Delta(J)/2).
 (i) c <= 4 for y <= 2l-2 (three pairs span >= l-8+3+2 = l-3 positions and contain the second pair of a short period; five pairs
   span >= 2l+2 > y). So Delta <= 5 and at most two leaving chords are needed; none if c = 0; one if c <= 2; two only if c >= 3,
   and then y >= l-3.
 (ii) Rows with e <= 3: e = 0: rows 0 of all periods, rows 3 and (l+3)/2 of A, a, rows l-2 of a, b, B; e = 3: row h-2 of B, S
   (for l >= 19; for l = 15 that row is row 5 with e = l-8 = 7).
   All other F rows have e >= 4.
   NEAREST LEAVING CHORD. Fix end and let x be the last F position <= end (x = end or end-1). If e(x) > end - x, x leaves.
   Otherwise e(x) = 0. Then x is not a row 1, x-1 is a dot and x' = x-2 is F with end - x' <= 3:
     x = (i,0): x' = (i-1,l-2), e = 7 if period i-1 is in A, and x' = (l-1,l-7) [e = h+2] if i = 0. If period i-1 is a, b or B then
       e(x') = 0, and x'' = (i-1,l-4) has e = 7 or 6 > end - x'' (which is 4; if end = x+1 then end is a row 1, which leaves itself).
     x = (i,3), A or a: x' = (i,1), e = l+6.     x = (i,(l+3)/2): x' = (i,(l-1)/2), e = 4 > 3.
     x = (i,l-2), a, b, B: x' = (i,l-4), e = 7 or 6.
   So some chord leaves from one of the last 5 positions, and the positions after the nearest leaving one form a stretch of at
   most 4 positions that contains no FF pair (it is inside {l-3,l-2,l-1,0}, {2,3,4}, {(l+1)/2,..,(l+5)/2} or {l-3,l-2,l-1}).
   Hence if c >= 1 the nearest leaving chord starts inside J: X(J) >= 1.
 (iii) SECOND LEAVING CHORD: for every end at least two chords leave from the last 11 positions (l >= 27; l = 15, 19, 23 by
   computer: fam5lem.py, maxD2 <= 10). Rows with e <= 10 for l >= 27: A: 0, 3 [0], (l-5)/2 [8], (l-1)/2 [4], (l+3)/2 [0], l-2 [7];
   a: the same and l-4 [7], l-2 [0]; B: 0 [0], h-4 [7], h-2 [3], l-6 [10], l-4 [6], l-2 [0]; b: 0 [0], 1 [4], l-6 [10], l-4 [6],
   l-2 [0]; S: 0 [0], h-4 [7], h-2 [3]. Any other F row leaves from distance <= 10. Going through the ends at or after each
   group of small rows (the two F rows before each group are large except as listed):
     ... l-6, l-4, l-2 | 0, 1 or 3 (B or b, then any): ends l-6..l-3: the rows at distance <= 3 leave (10 > 2, 6 > 1, and the row
       l-8 before them is large); end l-2 / l-1: rows l-4 (6 > 3) and l-6 (10 > 5); end (next,0): l-4 (6 > 4), l-6 (10 > 6);
       end (next,1): row 1 and l-4 (6 > 5); end (next,2): row 1 and l-6 (10 > 8); end (next,3), (next,4): rows 3 or 1 (4 > 3) ...
     ... l-4, l-2 | 0 (a then b): the same with 7 instead of 6 and the large row l-6.   A: l-2 [7] | 0, 1, 3: ends up to
       (next,4): rows l-2 (7 > 6) and l-4 or 1.
     (l-5)/2, (l-1)/2, (l+3)/2 (A, a): end (l+3)/2, (l+5)/2: rows (l-1)/2 (4 > 3) and (l-5)/2 (8 > 5); end (l+7)/2, (l+9)/2:
       the large row (l+7)/2 and (l-5)/2 (8 > 7).
     h-4, h-2 (B, S): ends h-2..h+1: rows h-2 or h (large) and h-4 (7 > 5).
     0, 1, 3 at the start of a half (after the short period, whose last F rows l-8, l-7 are large): end (0,0)': rows l-7, l-8 of S;
       ends (0,1)..(0,4): row 1 (l+6) and row l-7 of S (h+2 > 7).
     ends (i,5), (i,6) of A, a periods: row 5 (large) and row 1 (l+6, distance <= 5), row 3 being dead.
   Everywhere else the last two F rows before end are large. In all cases two chords leave from distance <= 8 (10 for l = 15),
   which is <= l-4 <= y-1.
 So X(J) >= floor(Delta(J)/2) in all cases. QED

REFEREE #13 (independent agent, S168 22:51): NO MATHEMATICAL ERROR; four presentational defects, fixed above. It rebuilt the code from
the written definition only (identical to oddfam.py up to relabelling, l = 15..103), validated it with its own all-windows C checker
for all 23 values l = 15..103, re-derived (T1)-(T8), (Q1)-(Q4) by hand and checked them and the coverage list by program
(0 bad, 0 double, 0 missed), brute-forced Steps 2-3 for l = 15..47 (4.5 million windows at l = 47), and checked Step 1 directly
(ch <= floor((y+1)/2) and X >= floor(Delta/2), all t, y, l = 15..103), claims (i)-(iii) included (second leaving chord at
distance <= 8 for l >= 19, 10 for l = 15).
