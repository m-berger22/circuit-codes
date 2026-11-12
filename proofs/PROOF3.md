# Family 3 is valid for every l = 0 (mod 4): k_max(l) = (l^2-l-6)/2 on these lines   (S168, 2026-11-10 22:45)

Continuation of PROOF.md / PROOF2.md (same notation). Status: written S168; lemma checks struct/even/famlem3.py, famlem3b.py
(l = 8..100); referee: see the end.

THEOREM 10. Let l = 0 (mod 4), l >= 8, k = (l^2-l-6)/2, n = (3k+l+1)/2. The word T defined below is the transition sequence of
a spread-k circuit code of length N = 4k+2l+2 = 2l^2-10 in Q_n.
COROLLARY. For l = 0 (mod 4), l >= 8: K(n,k) = 4k+2l+2 at k = (l^2-l-6)/2 (upper bound: Lemma 1 for 4 <= e <= k+4-2l [k odd: f(4) = 2l^2-8l-16 > 0, f(k+4-2l) = k(k+8-3l)-(4l-8) > 0, f concave], Lemma 2),
and with Theorem 7 (PROOF2 sec. 7) and the Main Theorem:  k_max(l) = (l^2-l-6)/2  exactly; Conjecture 4.2 fails at this k and
holds for every larger k on the line.
Proof status: Steps C, 2, 3 are by hand for all l. Step 1 is by hand for l >= 60 except for windows with y <= 24, which are a
finite, l-independent list of local patterns checked by computer; l = 8..56 is the direct computer check of evenfam.py.

## Definition (evenfam.py)
p = l-1 (so p = 3 mod 4), h = l/2, K = k+1 = p h - 2, H = N/2 = p l + p - 4 = 2K + p, N - 4K = 2p.
Positions 0..H-1 of the first half are written (i,r) = p i + r: periods i = 0..l-1 of length p (r = 0..p-1) and a short period
i = l of length p-4 (r = 0..p-5). TYPE: in a period, r is F iff r is odd or r = p-1; in the short period, iff r is odd or r = p-5
(period word P = (.F)^(h-1) F, short P' = (.F)^(h-3) F). Dots at t and t+H carry the same coordinate (gap H). For an F position x
the next occurrence of its coordinate is x + K + e(x), with e depending on the row (regime A: i < h; regime B: h <= i < l; S: i = l):
   A:  r=1: 0;   r=3: 2p-3 (p if i = h-1);   r = 1 mod 4, 5 <= r <= p-6: 0;   r = 3 mod 4, 7 <= r <= p-4: p;   r=p-2: 0;
       r=p-1: 4 (2 if i = h-1)
   B:  r=1: 2p-5;   r = 3 mod 4, 3 <= r <= p-8: p;   r = 1 mod 4, 5 <= r <= p-6: 0;   r=p-4: 1;   r=p-2: 1;
       r=p-1: 2 (2p-3 if i = l-1)
   S:  r = 1 mod 4, 1 <= r <= p-6: 0;   r = 3 mod 4, 3 <= r <= p-8: p;   r=p-5: 4.
The second half repeats the first (e(x+H) = e(x)); positions are taken mod N. Primes below denote 'in the other half'.

## Step C: T is well defined (every F coordinate is used exactly 4 times, gaps sum to N)
(x) + K + e = p(i+h) + (r-2+e). Positions p l .. p l+p-5 are the short period, and p(l+1)+c = H + c + 4.
 (C1) zero rows and p rows. A zero row of A (r = 1 mod 4, 5 <= r <= p-6) goes to (i+h, r-2): a p row of B, and this is a bijection onto
   the p rows of B. A zero row of B (same r, h <= i <= l-1) goes to (i+h, r-2): for i = h this is the p row (l, r-2) of S (all of them);
   for i >= h+1 it is p(i+h)+r-2-H = (i-h-1, r+2)', a p row of A with i-h-1 <= h-2 (all of them). A zero row (l,r) of S goes to
   p l + r + K - H = (h-1, r+2)', a p row of period h-1 (r+2 = 3 or 7 <= r+2 <= p-4; all of them). So x -> x+K maps these zero rows
   bijectively onto ALL p rows, and a p row y = x+K goes to y + K + p = x + H. Cycles: x, x+K, x+H, x+H+K; gaps K, K+p, K, K+p.
 (C2) (i,1), 1 <= i <= h-1 [e=0] -> (i+h-1, p-1) [B, not last period, e=2] -> p(i+l)-1 = (i-1, 3)' [A, i-1 <= h-2, e=2p-3]
   -> (i+h, p-2)' [e=1] -> p(i+l)+p-3 = (i,1)''.      e: 0, 2, 2p-3, 1.
 (C3) (0,1) [0] -> (h-1, p-1) [e=2] -> (l-1, p-1) [e=2p-3] -> p(l+h+1)+p-6 = (h, p-2)' [1] -> p l + p - 3 = H+1 = (0,1)''.
 (C4) (i,p-1), i <= h-2 [e=4] -> (i+h+1, 1) [B, e=2p-5] -> p(i+l+2)+p-6 = (i+1, p-2)' [A, e=0] -> (i+h+1, p-4)' [e=1]
   -> p(i+l+1)+p-5 = (i, p-1)''.                       e: 4, 2p-5, 0, 1.
 (C5) (0,p-2) [0] -> (h, p-4) [1] -> (l, p-5) [S, e=4] -> p l + p - 5 + K + 4 = H + p h + 1 = (h,1)' [2p-5] -> H + p l + 2p - 6
   = (0,p-2)''.                                        e: 0, 1, 4, 2p-5.
 Every F row occurs exactly once: A: r=1 (C2,C3), r=3 (C2; i=h-1 in C1), zero and p rows (C1), r=p-2 (C4 for i >= 1, C5 for i = 0),
 r=p-1 (C4; i=h-1 in C3). B: r=1 (C4 for i >= h+1, C5 for i = h), p-4 (C4, C5), p-2 (C2, C3), p-1 (C2; i = l-1 in C3), others C1.
 S: p-5 (C5), others C1. In each cycle the four e sum to 2p, so the gaps (all >= K) sum to 4K+2p = N: each F coordinate is used
 4 times. F positions: 2(l h + h - 2) = l^2+l-4 = 4(n-k); dots: k coordinates. T has n coordinates and t -> t+H is an automorphism.

## What has to be shown
Any K consecutive transitions are distinct (gaps >= K). So it suffices that odd(W) >= k for every window W = [t,t+L), K < L <= H
(longer arcs have the same odd count as their complement). A dot never occurs twice in W (gap H >= L); an F coordinate occurs at
most 3 times (3K > H). With ch(W) = number of pairs (x,x+) inside W, tr(W) = number of triples (x,x+,x++) inside W:
        odd(W) = L - 2 ch(W) + 2 tr(W),         and we need   ch(W) - tr(W) <= floor((L-k)/2).
Write L = K+y, 1 <= y <= K+p.

## Step 2 and Step 3: gmax < L <= H  (gmax = N-3K = K+2p >= every gap, the largest being K+2p-3; y > 2p)
Every F coordinate occurs in W, so odd(W) = L + 2(n-k) - 2F(W) + 2tr(W) (PROOF2 (S2)), and odd >= k iff
Delta(W) := 2F(W) - L <= l + 2 tr(W) for even L, <= l+1+2tr(W) for odd L (2(n-k)-k = l+1).
The type word has no two adjacent dots and its FF pairs are exactly the last two letters of each period; consecutive FF pairs are
p apart, except p-4 from period l-1 to the short period. So Delta(W) = c + (eps(first)+eps(last))/2, c = number of FF pairs inside
W, eps = +1 for F, -1 for a dot. c pairs span at least (c-1)p - 4 + 2 positions (at most one short spacing, as L <= H).
 Step 2 (L <= 2K = p l - 4): c <= l, since l+1 pairs span >= lp-2 > 2K. So Delta <= l+1, and Delta = l+1 only for odd L
   (Delta = L mod 2, l even). So Delta <= l (L even), l+1 (L odd). tr = 0.
 Step 3 (2K < L <= H): l+2 pairs span >= (l+1)p - 2 > H, so c <= l+1 and Delta <= l+2. For odd L, Delta <= l+1 by parity. For even
   L, Delta = l+2 needs c = l+1; then W contains the window W0 from the first letter u of its first FF pair to the second letter of
   the (l+1)-th FF pair after it, and we show W0 contains a triple (so tr(W) >= 1). The l spacings after u miss exactly the spacing
   before u (there are l+1 per half), so |W0| = lp-2 = 2K+2 unless u is the FF pair of the short period, where |W0| = lp+2 = 2K+6.
   A triple (x,x+,x++) lies in W0 iff x - u + e(x) + e(x+) <= |W0| - 1 - 2K.
     u = (i,p-2), i < h:  e = 0, u+ = (i+h, p-4) with e = 1 (C4, C5): sum 1 <= 1.
     u = (i,p-2), i >= h: e = 1, u+ is a row (.,1) of A with e = 0 (C2, C3): sum 1 <= 1.
     u = (l,p-6):  x = u+3 = (0,1)' has e = 0 and x+ = (h-1,p-1) with e = 2 (C3): 3 + 2 <= 5.

## Step 1: K < L <= gmax (1 <= y <= 2p): ch(W) <= floor((y+1)/2)       (tr = 0 since y <= 2p < K)
ch(W) = #{x in [t,t+y) : x - t + e(x) <= y-1}.
 (a) y <= 24. Only the values min(e,24) on [t,t+24) matter. For p >= 31 a stretch of 24 positions meets at most two periods, and
   min(e,24) (dots count as 24) depends only on: r for r <= 3, the distance to the end of the period for the last 7 rows, r mod 4
   otherwise, the regime, and whether the period is h-1, l-1 or the short one; a stretch meets one period or two consecutive ones,
   and the same types of consecutive periods (A A, (h-1) B, B B, (l-1) S, S A) occur for every l >= 32. So the set of sequences (min(e(t+d),24))_{d<24} is the same for all l >= 32; it has 103 elements, and for each of
   them and each y <= 24 the inequality holds (famlem3b.py: l = 32..100 give the same 103 patterns; equality occurs only for
   y = 1, 2, 4, 6, 8).
 (b) y >= 25, l >= 60 (p >= 59). Let q(m) be the number of periods met by m consecutive positions; periods have >= p-4 positions, so
   q <= 2 for m <= p-4, q <= 3 for m <= p, q <= 4 for m <= 2p.
   sigma(m) := number of positions with e <= 4 among m consecutive positions <= m/4 + 2.75 q:  such rows have r = 1 (mod 4) [at most
   ceil(m'/4) <= m'/4 + 3/4 in a stretch of m' positions of one period] or are one of (B,p-4), (.,p-1), (S,p-5) [at most 2 per period].
   pi(m) := number of positions with e = p <= m/4 + 0.75 q  (rows with r = 3 mod 4).
   Rows with e = 2p-3 or 2p-5 are (A,3), (B,1), (l-1,p-1): any two of them are at least p-2 > 5 apart, so at most one lies in the
   first y-2p+5 <= 5 positions.  Now ch(W) <= sigma(y) + pi(y-p) + 1 (the last two terms only if y > p resp. y > 2p-5):
     25 <= y <= p-4:  ch <= y/4 + 5.5 <= y/2 - 0.75.
     p-4 < y <= p:    ch <= y/4 + 8.25 <= y/2  (needs y >= 33; here y >= 56).
     p < y <= 2p:     ch <= y/4 + 11 + (y-p)/4 + 2.25 + 1 = y/2 - p/4 + 14.25 <= y/2  (p >= 57).
   In all cases ch <= floor(y/2) <= floor((y+1)/2).
 (c) l <= 56: direct check of the definition (evenfam.py, l = 8..100: VALID; famlem3b.py (a): all t, all y <= 2p, l = 8..100).
QED
(Notation: in C2-C4 the closing positions are written modulo H; e.g. in C3 the cycle closes at N+1.)
REFEREE #12 (independent agent, S168 22:50): NO ERROR FOUND. It rebuilt the code from the written definition only (identical
to evenfam.py for l = 8..100), validated it with its own C checker (all windows, no symmetry) for l = 8..100, verified every
cycle of Step C by program, the Delta formula and both c bounds by brute force (l <= 48), the triples of Step 3, the 103 patterns
(its own computation, l = 32..100), and the sigma/pi/q bounds (l <= 100); four wording fixes applied above.

Machine checks: struct/even/evenfam.py (the whole definition, l = 8..100); famlem3.py: the cycle types of Step C (22 symbolic
types, the same for all l >= 20: exactly C1-C5 with their boundary variants), Step 2 and Step 3 per window for l = 8..44
(the windows with Delta = l+2 all contain a triple); famlem3b.py: Step 1 (a), the 103 patterns, and the bounds on sigma, pi
and the big rows used in (b), for l = 8..100.
