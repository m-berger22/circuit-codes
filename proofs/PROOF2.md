# Excess-2 codes: the type word, and K(34,20), K(37,22), K(40,24)   (S165, 2026-11-10)

Continuation of PROOF.md (same notation: spread-k coil of length N in Q_n, l = 2n-3k-1, K = k+1, windows, odd(W), (F1)-(F3)).
Status: derived S165. Identities machine-tested on ~2,400 real excess-2 codes (structcheck.py, wordcheck.py: 0 failures).
REFEREE PASS (independent agent, 13:21; report summarised under "Checks"): no error affecting any result; its own enumerator
and its own skeleton encoder reproduce the counts and the UNSATs; four wording fixes applied.

## 0. What is proved here

PROOF.md shows K(n,k) <= 4k+2l once k > ~l^2/2. Below that, Lemma 1 leaves a little room for codes of length
N = 4k+2l+2 ("excess 2"; almost all counterexamples to Byrnes' Conjecture 4.2 found so far are of this kind). This note shows that an
excess-2 code has a very rigid shape, and uses it to decide the remaining cases on the line l = 7:

    K(34,20) = 94,   K(37,22) = 102,   K(40,24) = 110      (= 4k+2l; Byrnes' codes attain it)

so, with PROOF.md (k >= 26) and the codes of S162-163 (k = 12,14,16,18 have length 4k+16):

    LINE l = 7 COMPLETE:  K((3k+8)/2, k) = 4k+14 for every even k >= 20, and > 4k+14 for k = 12, 14, 16, 18.
    Conjecture 4.2 on this line (range k >= 12) fails exactly for k = 12..18.     kmax(7) = 18.

Also no excess-2 code exists for (l,k) = (11,58), (11,60) [type words: none], (8,27) [4 type-word classes, skeleton UNSAT]; see RESULTS.

## 1. Structure of an excess-2 code

Let C be a spread-k coil with N = 4k+2l+2 < 6K, L0 = 2k+1 (k even) or 2k+2 (k odd), c0 = floor((L0-k)/2), and assume

    (H)   (n-k+1) (4 L0 - N)  >  N c0 .

(H) holds in all cases treated here (the programs assert it); e.g. (34,20): 15*68 = 1020 > 960.

(S1) Exactly n-k coordinates are used four times ("F coordinates"), exactly k are used twice ("dots", D), none is unused.
     Every gap of an F coordinate is at most gmax := N - 3K = k+2l-1.
Proof. N < 6K: uses are 0, 2 or 4 (PROOF.md). With n_2 four-times coordinates, n_2 >= N/2 - n = n-k, and the proof of
Lemma 1 gives n_2 (4L0-N) <= N c0, so n_2 <= n-k by (H). Then n_1 = (N-4n_2)/2 = k and n_1+n_2 = n. The four gaps of an
F coordinate are >= K and sum to N. QED

Call a position F or D according to its coordinate; the cyclic 0/1 word phi (1 = F) is the TYPE WORD. It has 4(n-k) ones.

(S2) Window identity. Let W be a window of length Lw with gmax <= Lw <= 3K. Let F(W) = number of F positions in W,
     sd(W) = number of dots occurring twice in W, tr(W) = number of F coordinates occurring three times in W. Then
            odd(W) = Lw + 2(n-k) - 2 F(W) - 2 sd(W) + 2 tr(W).
Proof. Lw >= gmax >= every F gap, so every F coordinate occurs in W; Lw <= 3K, so it occurs 1, 2 or 3 times
(four occurrences span >= 3K+1 positions). With a_j = number of F coordinates occurring j times: a_1+a_2+a_3 = n-k and
F(W) = a_1+2a_2+3a_3, hence a_1 + a_3 = 2(n-k) - F(W) + 2a_3. Dots contribute (Lw - F(W)) - 2 sd(W) odd coordinates. QED

(S3) Consequently, for gmax <= Lw <= min(3K, N-k), by (F1) (odd >= k + ((Lw-k) mod 2)) and 2(n-k) - k = l+1:
            F(W) + sd(W)  <=  floor((Lw+l+1)/2) + tr(W).
     (a) Lw <= 2K:  tr(W) = 0, so  F(W) <= floor((Lw+l+1)/2).
     (b) Lw = 2K+1+j (j >= 0), W = [s, s+Lw): three occurrences p < p' < p'' of one coordinate in W have p <= s+j,
         p'' >= s+2K and s+K <= p' <= s+Lw-1-K (gaps >= K), and different coordinates use different positions, so
            tr(W) <= min( F[s, s+j],  F[s+2K, s+2K+j],  F[s+K, s+Lw-1-K] )      (numbers of F positions in these ranges).
     Summing (a) over all windows of length L0 gives Lemma 1; (a) says much more: the F/D word is BALANCED.
     (Referee: given (a), (b) is equivalent to F[s,s+K) + F[s+K+j+1, s+2K+j+1) <= floor((2K+j+l+2)/2): only the middle term of the min matters.)

(S4) Skeleton conditions. For every window W with k <= Lw <= N-k:   D(W) + oddF(W) >= k + ((Lw-k) mod 2),
     where D(W) = number of dot positions in W and oddF(W) = number of F coordinates occurring an odd number of times in W
     (because odd(W) = D(W) - 2 sd(W) + oddF(W)). Also: an F coordinate never occurs twice among K consecutive positions (F2),
     occurs in every window of gmax consecutive positions, and is used an even number of times.

## 2. Example by hand: K(40,24) = 110

(n,k,l) = (40,24,7), N = 112, K = 25, L0 = 49, 16 F coordinates (64 positions, gaps in [25,37]), 24 dots (48 positions).
(S3a) with Lw = 49: F(W) <= 28 for all 112 windows, and the mean of F(W) is 49*64/112 = 28. So F(W) = 28 for every
49-window, hence phi(t) = phi(t+49) for all t, i.e. phi has period gcd(49,112) = 7, with 4 F and 3 D per period.
(S3a) with Lw = 47 (bound 27): the 47-window [t+1,t+47] is the 49-window [t,t+48] minus its two ends, so the ends t and
t+48 = t-1 (mod 7) are not both D: no two cyclically adjacent D's. So the period is D F F D F D F: there is exactly one
residue s with phi(s) = phi(s+1) = F, and then phi(s+4) = D.
(S3b) with Lw = 51, j = 0, window [p, p+50] with p = s (mod 7): F(W) = 28 + phi(p) + phi(p+50) = 30 > 29 = floor(59/2), so
tr(W) >= 1, which needs F at p+K = p+25 = s+4 (mod 7). But phi(s+4) = D. Contradiction: no (40,24) code of length 112.
Lengths 114..: excluded by Lemma 1 (f(e) > 0 for 4 <= e <= k+4-2l) and Lemma 2. Hence K(40,24) = 110.
(stage1.c reproduces this: one word class under (a), none under (a)+(b), 357 nodes.)

The same three steps prove that no excess-2 code exists whenever 2k+1 = l^2, l = 3 (mod 4), l >= 7 (stage1.c: l = 7, 11, 15: no word; l = 13: one class) (period l; one FF pair at
residues s, s+1; the triple needs F at s+K = s+(l+1)/2, which is a D residue when (l+1)/2 is even).
For l = 5 (K(21,12) = 58, proved by SAT in S161): the period is D F D F F, every position p = s (mod 5) starts a triple
T_p = T_{p+13} = T_{p+26}; these are 12 positions, no F coordinate contains two of them (the other occurrences have residues
s+3, s+1, and a fourth occurrence starting another triple would have residue s+2), but there are only 9 F coordinates.

## 3. The general procedure (programs in struct/)

Stage 1 (stage1.c n k): enumerate all cyclic 0/1 words with 4(n-k) ones satisfying (S3a) for gmax <= Lw <= 2K and (S3b)
for 2K < Lw <= min(3K, N-k)  [sd(W) >= 0 is dropped]. DFS over positions; pruning by bounds fmn(w) <= F(any window of
length w) <= fmx(w) derived from (S3a) by complement (F(W) + F(complement) = 4(n-k)) and additivity, and by the deficit
budget sum_W (B0 - F(W)) = N*B0 - L0*4(n-k) over L0-windows. Output: one word per rotation class.
Stage 2 (skel.py n k PHI): SAT for the F skeleton of a given type word: which F coordinate sits at each F position,
subject to (S4) for ALL windows (dots are relaxed to anonymous positions). UNSAT => no code with this type word.
If stage 1 finds no word, or stage 2 is UNSAT for every word, no excess-2 code exists, and K(n,k) <= 4k+2l provided larger
lengths are excluded (PROOF.md: Lemma 1 excludes 4 <= e <= k+4-2l when f(4) > 0 AND f(k+4-2l) > 0 [f concave; the second holds
for k > 3l-5 (k even), and in all cases used: (34,20) f(4)=20, f(10)=80; (37,22) 36, 132; (40,24) 52, 192], i.e. k > l(l+3)/4 (k even) /
k > (l^2+2l-4)/4 (k odd); Lemma 2 excludes N >= 5k+4 when k > 3l-3 / 3l-7).

## 4. Any length N < 6K (added 12:45): exact values, excess 4

Nothing in section 1 needs N = 4k+2l+2. For any even N with 2K <= N < 6K put m = N/2 - n. If
    (H_N)   (m+1)(4 L0 - N) > N c0      (and N/4 <= L0 <= N-k)
then exactly m coordinates are used four times, n-m twice, none unused, F gaps <= N-3K, and (S2)-(S4) hold with n-k
replaced by m:  odd(W) = Lw + 2m - 2F(W) - 2sd(W) + 2tr(W),  F(W) <= floor((Lw+2m-k)/2) + tr(W).
skelfree.py n k N and stage3.py implement this (they assert (H_N)). So for a pair (n,k) where Lemma 2 applies
(k > 3l-3 even / k > 3l-7 odd: N <= 5k+3 < 6K) the exact value K(n,k) is decided by finitely many small SAT queries,
N = 5k+3 (or 5k+2) down to 4k+2l+2 (most are refuted at once by the window bounds = Lemma 1).
First use: (33,19), l = 8, S = 4k+2l = 92: N = 98 has no balanced word, N = 96 is SAT and completes to a real code
(codes/skel_33_19_96.txt, 3 checks): K(33,19) = 96 = S+4, the first code exceeding Byrnes' formula by 4 in the range of
his conjecture. (Lemma 1 at L0 = 40 holds with equality for it: f(4) = 0.)
Exactness of the excess-2 values: for l = 8, k = 21, 23, 25 and l = 7, k >= 20, f(4) > 0 and f(k+4-2l) > 0, so Lemma 1
excludes 4k+2l+4 <= N <= 5k+3 and Lemma 2 the rest: K(36,21) = 102, K(39,23) = 110, K(42,25) = 118.

## 5. An explicit family: the Main Theorem is sharp for l = 9, 13, 17, ... (added 13:30)

Let l = 1 (mod 4), l >= 9, k = (l^2-1)/2 (the largest k NOT covered by the Main Theorem: 2k+1 = l^2, 'zero slack'),
K = k+1 = (l^2+1)/2, N = 2l(l+1) = 4k+2l+2, n = (3k+l+1)/2 = (3l-1)(l+1)/4. Define the transition word T on Z_N:
  (A) for j = 0..2l+1:   T(lj) = T(lj+K) = T(lj+2K) = T(lj+3K+1) = A_j          (2l+2 coordinates; gaps K, K, K+1, N-3K-1;
                          residues mod l: 0, (l+1)/2, 1, (l+5)/2)
  (B) for t mod l in {3,5,..,l-2} minus {(l+1)/2, (l+5)/2}:   T(t) = B_{t mod N/4}   ((l-7)(l+1)/4 coordinates, all gaps N/4)
  (D) for t mod l in {2,4,..,l-1}:                             T(t) = D_{t mod N/2}   (k coordinates, antipodal 'dots')
(2l+2 + (l-7)(l+1)/4 = (l+1)^2/4 = n-k F coordinates; the type word has period l = F F . F . F ... F .)
CLAIM: T is the transition sequence of a spread-k circuit code of length N in Q_n. Hence K(n,k) = 4k+2l+2 (the upper bound is
Lemma 1 for 4 <= e <= k+4-2l [f(2) = 0, f concave, f(k+4-2l) > 0] and Lemma 2), Conjecture 4.2 fails at (l, (l^2-1)/2), and the
hypothesis k > (l^2-1)/2 of the Main Theorem cannot be weakened.
STATUS: (i) VERIFIED BY COMPUTER from the definition for every l = 1 mod 4, 9 <= l <= 161 (struct/zfamver.py -> zfamver_9_61.out,
zfamver_65_161.out; it uses the automorphism t -> t+l, which it checks first; l <= 37 also by the full O(N^2) check zfam2.py;
(65,40,180), (133,84,364), (225,144,612) also by check.py: codes/zfam_*.txt).  (ii) PROOF for all l >= 13 below (S165 13:40;
steps tested numerically by struct/zfamlem.py).  REFEREE #3 (independent agent, 13:38, files theory/referee3/): NO ERROR FOUND;
own construction from (A),(B),(D) + from-scratch check l = 9..29 (0 violations), every intermediate claim of Steps 1-3 tested
per window for l = 13..41 (0 failures; each step is tight somewhere), upper-bound half re-derived. Its wording nits are applied.

PROOF OF THE CLAIM (l = 1 mod 4, l >= 13; l = 9 by computer).  Put h = (l-1)/2 and Q = N/4 = l(l+1)/2, so K = Q-h, Q = 0 (mod l).
Gaps: A: K, K, K+1, g4 := N-3K-1 = Q+3h-1;  B: Q;  D: 2Q.  All gaps are >= K, every symbol is used an even number of times, so T
closes up and any K consecutive transitions are distinct. It remains to show odd(W) >= k for every window W = [t, t+L) with
K < L <= N/2 = 2Q (then d_H = d_C for L < K, d_H >= k for k <= L <= N/2, and the two arcs between two vertices have the same d_H).
Throughout, c_R(t,x) = number of positions p in [t, t+x) with p mod l in R (0 if x <= 0); a window of length <= N/2 never
contains both occurrences of a D symbol.
 Step 1 (K < L <= g4; write L = K+y, 1 <= y <= 4h-1 = 2l-3).  Three occurrences of a symbol span >= 2K+1 > L positions, so none occurs three times and
   odd(W) = L - 2 ch(W), ch(W) = number of pairs of consecutive equal symbols inside W
          = c_{0}(t,y) + c_{(l+1)/2}(t,y) + c_{1}(t,y-1) + c_Bres(t, y-h)        (pairs with gap K, K, K+1, Q; g4 >= L)
   and we need 2 ch <= y+1.  The residues that can start a pair lie in {0} + {odd residues}, so two adjacent positions both
   start pairs only for residues (0,1).
   y <= h-1: only residues 0, 1, (l+1)/2 count; (l+1)/2 is at cyclic distance h+1 after 0 and h before 0, so a window of
   y <= h-1 positions contains at most the pair (0,1): ch <= 2, and ch <= 1 for y <= 2 (residue 1 only counts at p < t+y-1).
   So 2ch <= y+1.
   y >= h: the last h positions [t+y-h, t+y) start no B pair and contain at most two of the residues 0, 1, (l+1)/2 (same
   distances), so they contribute <= 2. In the first y-h positions the pair-starting positions are pairwise non-adjacent
   except for J <= 2 pairs (0,1) (y-h < 2l), so they contribute <= ceil((y-h-J)/2) + J <= (y-h+J+1)/2.
   Hence 2ch <= y - h + J + 5 <= y + 1 because h >= 6.
 Step 2 (g4 < L <= 2K).  Every F symbol occurs in W (all F gaps <= g4 < L) at most twice (L <= 2K), dots at most once, so by
   the counting in the proof of (S2) (pure counting; it does not need T to be a code) odd(W) = L + 2(n-k) - 2F(W), and odd >= k iff F(W) <= floor((L+l+1)/2).  Write L = lq + rho, 0 <= rho < l (q <= l).
   The type word has (l+1)/2 letters F per period and at most floor(rho/2)+1 in rho >= 1 consecutive positions (it alternates
   except for the single pair FF).  So F(W) <= q(l+1)/2 + floor(rho/2) + 1 (rho >= 1), = q(l+1)/2 (rho = 0), and the required
   inequality reads  q <= l-1 + (rho mod 2) - ((q+rho) mod 2)  (rho >= 1),  q <= l+1 - (q mod 2)  (rho = 0).
   It holds for q <= l-2; for q = l-1 (even) the right side is l-1; q = l occurs only for L = l^2, l^2+1 (rho = 0, 1), where
   the right sides are l and l.
 Step 3 (2K < L <= 2Q; L = 2K+z, 1 <= z <= l-1).  Now a symbol can occur three times only as (p, p+K, p+2K) with p = 0 (mod l),
   p in [t, t+z), or as (p, p+K, p+2K+1) with p = (l+1)/2 (mod l), p in [t, t+z-1).  By (S2) with tr = c_{0}(t,z) + c_{(l+1)/2}(t,z-1):
   odd >= k iff F(W) <= floor((L+l+1)/2) + tr.  Here L = l*l + (z+1), F(W) = l(l+1)/2 + F', F' = number of F letters among the
   z+1 residues t, .., t+z, and floor((L+l+1)/2) = l(l+1)/2 + 1 + floor(z/2).  If these residues do not contain 0 followed
   by 1 they alternate and F' <= floor(z/2)+1.  If they do, F' <= floor((z-1)/2) + 2 <= floor(z/2) + 2, and the residue 0
   lies in [t, t+z), so tr >= 1.  In both cases F' <= 1 + floor(z/2) + tr.  QED
(Where l = 1 mod 4 enters: (l+1)/2 and (l+5)/2 are odd residues, so the A positions fall on F residues, and k is even (Lemma 1
branch L0 = 2k+1); l >= 9 makes (l+5)/2 <= l-2; h >= 6 is used once, in the last line of Step 1 -- for l = 9 that line fails
although 2ch <= y+1 still holds: computer.)
COROLLARY. For every l = 1 (mod 4), l >= 9, and k = (l^2-1)/2, n = (3k+l+1)/2:  K(n,k) = 4k+2l+2.  So the hypothesis of the Main Theorem (PROOF.md)
cannot be weakened for l = 1 (mod 4), l >= 9 (for l = 3 mod 4 it can: sec. 2), and Conjecture 4.2 fails for infinitely many pairs.
With Deimer contraction (an excess-2 code at (l,k) gives one at (l+1,k-1)), applied j <= 3 times to the member with the largest
l0 = 1 (mod 4), l0 <= l': a code of length 4k'+2l'+2 at k' = (l0^2-1)/2 - j >= 2l'+1 on EVERY line l' >= 9; with the codes on
l' = 6, 7, 8: Conjecture 4.2 fails on every line l >= 6, and kmax(l) >= ((l-3)^2-1)/2 - 3, i.e. kmax(l) = l^2/2 - O(l).
Variants: the 4th occurrence may sit at 2K+a for any a in [K, N-3K] with (1+a) mod l an odd residue in [3, l-2] other than
(l+1)/2 (struct/zfamscan.py: all 4, 8, 12 admissible a are valid for l = 9, 13, 17).
How it was found: the hand analysis of the zero-slack shape (section 2) predicted the period-l type word, the 2l+2 'triple'
coordinates (gaps K, K, ., .) and the residues; the SAT solution for (65,40) matched; imposing the shift-by-l symmetry and
antipodal dots left nothing to search.
Consequences: (i) k_max(l) = (l^2-1)/2 for l = 9, 13, ..., 61 (for l = 3 mod 4, l >= 7, the zero-slack case is impossible: sec. 2);
(ii) by Deimer contraction each member gives codes of length 4k'+2l'+2 at (l', k') = (l+j, k-j), j >= 0: an explicit infinite
family of counterexamples to Conjecture 4.2 (as far as the claim is verified).

## 6. l = 3 (mod 4): a 'defect' template (added 13:55; computer-found codes, NO general formula or proof yet)

For l = 3 (mod 4) the zero-slack case is impossible (sec. 2). The symmetric (31,18,88) codes [l = 7, k = k_max] have this shape:
type word = the period-l word W0 = FF.F.F...F. repeated P times with an extra 'FF' inserted after the FF of two antipodal periods;
counting then forces P = 2(l-1), k = (l-1)^2/2, N = 2l^2-2l+4 = 4k+2l+2. Template (struct/l3/enum7.py, enum11.py):
  - half-turn automorphism t -> t+N/2, antipodal dots;
  - 'triple' coordinates A_j = {s, s+K, s+2K, s+2K+a_j} for s = first F of each period's FF (2(l-1) of them);
  - the leftover F positions are matched into coordinates {p, q, p+N/2, q+N/2}.
DFS with the necessary window test, full check from the definition at the leaves:
  l = 7:  exactly 10 solutions (a_j not uniform);
  l = 11: (81,50) coil of length 224, all a_j = K+1 (codes/dfam_81_50_224.txt; 82 nodes)   => k_max(11) >= 50 (<= 54);
  l = 15: (155,98) coil of length 424, all a_j = K+1 (codes/dfam_155_98_424.txt; 43 nodes) => k_max(15) >= 98 (<= 112);
  l = 19, 23, 27: unit l3fam165 -> struct/l3/out*.txt.
SEARCH-FREE CONSTRUCTOR (13:56; struct/l3/dfam2.py), l = 3 (mod 4), l >= 15; H = N/2, half-turn t -> t+H, antipodal dots; half 1:
  positions 0,1 = F F, 2,3 = inserted F F, p >= 4 has W0-residue r = (p-2) mod l and is F iff r in {0,1} or r odd in [3, l-2];
  A: for s = 0 and s = 2+l*i (i = 1..l-2):  {s, s+K, s+2K, s+3K+1}  (and +H);
  B: every remaining F position p of half 1, in increasing order and if still free, is joined with q = p + N/4 + d,
     d = -2 (p = 1), +2 (p = 2), +4 (r = l-2), +3 (r = (l+3)/2), +1 otherwise;  coordinate {p, q, p+H, q+H}.
(Readings: r is used only for p >= 4, p = 3 gets d = +1; half 2 = translate of half 1 by H, all positions mod N; 'still free' = not yet
 covered by an A coordinate, its translate, or an earlier B coordinate; dots = every non-F position t with t+H.)
INDEPENDENT REBUILD from this paragraph alone (agent, theory/referee4/build.py, 14:01): l = 15, 19, 23, 27, 31 all valid, 0 violating pairs.
VERIFIED from the definition (dfam2.py; half-turn automorphism checked first) for l = 15, 19, ..., 43 (-> 99: l3/dfam2_15_99.out);
also by the DFS for l <= 59 (l3/verify_l3.out) and by check.py for l = 11, 15, 19, 23 (codes/dfam_*.txt).
l = 7 and l = 11: same template, but the uniform rule fails; codes by DFS (10 symmetric solutions at l = 7).
=> k_max(l) >= (l-1)^2/2 for l = 3 (mod 4), 7 <= l <= 43 (gap l-1 to the Main Theorem; equality at l = 7).  NO PROOF YET
(expected: the argument of sec. 5 with the two defects carried along).

### 6b. Closed form and PROOF for l = 3 (mod 4), l >= 43 (written 14:10; l = 15..39 (and to 99) by computer)

REFEREE #5 (independent agent, 14:16, files theory/referee5/): NO proof-breaking error. Built the word from this closed form alone
(l = 15..31: 0 violating pairs; A list and B matching exact) and tested 71 named intermediate claims per window (l = 15..31): all
hold except 'a window meets at most one extra pair' at L = H (2 windows; fixed below by treating L = H separately); one sign slip
and two wording gaps fixed.  Not run for l >= 35 by the referee (my dfam2.py check covers l = 15..99).

Write h = (l-1)/2 (odd), k = 2h^2, K = 2h^2+1 = l(h-1)+(h+2), N = 4lh+4, H = N/2 = 2lh+2, Qh = N/4 = lh+1, W0 = FF.F.F...F. (length l).
The type word is (FF W0^(l-1))^2: each half is an extra pair FF (positions 0,1) followed by l-1 = 2h periods W0.  For p >= 2 in half 1
write p = 2 + l*i + r ('period' i = 0..2h-1, 'residue' r = 0..l-1); position (i,r) is F iff r in {0,1} or r odd in [3, l-2].
Everything below is taken together with its translate by H; coordinates {p,q,p+H,q+H} are their own translates.
 A coordinates: for s in S0 := {0} + {(i,0) : i = 1..2h-1}:  {s, s+K, s+2K, s+3K+1}.  Using K = l(h-1)+h+2, 2K = l(2h-1)+3,
   3K+1 = l(3h-2)+h+6, H = 2lh+2, the positions reduced to half 1 (mod H) are:
     s = (i,0), i >= 1:  s+K = (i+h-1, h+2) if i <= h, else (i-h-1, h);   s+2K = (i-1, 1);   s+3K+1 = (i+h-2, h+4) if i <= h+1, else (i-h-2, h+2);
     s = 0:              s+K = (h-1, h);   s+2K = (2h-1, 1);   s+3K+1 = (h-2, h+2).
   So A occupies exactly: position 0; residue 0, periods 1..2h-1; residue 1, all periods; residue h, periods 0..h-1; residue h+2,
   all periods except h-1; residue h+4, periods h-1..2h-1  (8h = 4(l-1) positions, pairwise distinct, all F since h, h+2, h+4 are odd
   and <= l-2).
 B coordinates {p, q, p+H, q+H}, q = p + Qh + d (i.e. period + h, residue + 1 + d):
     p = 1,  d = -2:  q = (h-1, l-2);                    p = 2 = (0,0),  d = +2:  q = (h, 3);
     p = (i, r), r odd in [3, l-4], r not in {h, h+2, h+4}, i = 0..h-1,  d = +1:  q = (i+h, r+2);
     p = (i, h+4), i = 0..h-2,  d = +1:  q = (i+h, h+6);        p = (h-1, h+2),  d = +3:  q = (2h-1, h+6);
     p = (i, l-2), i = 0..h-2,  d = +4:  q = (i+h+1, 3).
   These are exactly the F positions not used by A, each once: residue 3 seconds = periods h (from p = 2) and h+1..2h-1 (from residue l-2);
   residue r+2 seconds = periods h..2h-1 (from residue r); residue h seconds = periods h..2h-1 (from residue h-2); residue h+6 seconds =
   periods h..2h-2 (from h+4) and 2h-1 (from (h-1,h+2)); residue l-2: period h-1 is the partner of p = 1.  (Needs h+6 <= l-2, i.e. l >= 15.)
   This is the rule of dfam2.py ('ascending, if still free').
 Dots: {t, t+H} on the non-F positions.
Gaps.  A: K, K, K+1, K+4h-1.   B: Qh+d and Qh-d = K+h+d, K+h-d with |d| <= 4.   Dots: H.   All >= K (h >= 4): any K consecutive
transitions are distinct, the word closes, and a window of length <= H contains no dot twice.  As in sec. 5 it remains to show
odd(W) >= k for W = [t, t+L), K < L <= H.
 Step 1 (L = K+y, 1 <= y <= 4h-1).  No symbol occurs three times (three occurrences span >= 2K+1 > L), so odd(W) = L - 2ch(W) and we
   need 2ch <= y+1.  A position x starts a pair inside W iff x in [t, t+y-e(x)), e(x) = (gap after x) - K:  e = 0 on S0 and S1 := S0+K,
   e = 1 on S2 := S0+2K, e = 4h-1 >= y on S0+3K+1, e >= h-4 on B positions, e = H-K > y on dots.
   (i) S0 (with its translate) has consecutive spacings l+2, l, l, ..., l; so S0, S1, S2 each have <= ceil(y/l) points among y
   consecutive positions.  (ii) B positions are F positions, and x0 consecutive positions (x0 < 2l) contain <= (x0+adj+1)/2 <= x0/2 + 5/2
   letters F (adj = number of adjacent FF inside <= 4: one per period pair, three in a block FFFF).
   y <= h-4: only S0, S1, S2 count, at most one point each.  The only adjacent positions among them are (i,0) in S0 and (i,1) in S2, and S2
   needs x < t+y-1.  So ch <= 1 for y <= 2, ch <= 2 for y = 3, 4 (a point of S1, residue h or h+2, is more than 4 positions
   away from residues 0, 1 because h >= 5), ch <= 3 for y >= 5: 2ch <= y+1.
   h-4 < y <= l:  2ch <= 2*3 + 2*((y-h+4)/2 + 5/2) = y-h+15 <= y+1  as h >= 14.
   l < y <= 4h-1: 2ch <= 2*6 + (y-h+4) + 5 = y-h+21 <= y+1  as h >= 20.        [this is where l >= 43 is used]
 Step 2 (K+4h-1 < L <= 2K = l(l-2)+3).  All F gaps are <= K+4h-1 < L and L <= 2K, so every F symbol occurs once or twice and (counting of
   (S2)) odd >= k iff F(W) <= floor((L+l+1)/2).  For L < H, W meets at most one extra pair (the two pairs are H apart; L = H occurs only in Step 3 and is treated there);
   let e in {0,1,2} be the number of its letters in W
   and W' = W without them, a window of the periodic word W0^infinity of length L-e = lq'+rho' (the extra pair sits between two periods,
   i.e. right after '.'  and right before 'FF').  F(W') <= q'(l+1)/2 + floor(rho'/2) + 1 (rho' >= 1), = q'(l+1)/2 (rho' = 0).
   e = 0: as in sec. 5 with q <= l-2: true.
   e = 2: need q'(l+1)/2 + floor(rho'/2) + 3 <= floor((lq'+rho'+l+3)/2), i.e. q' <= l-3 + (rho' mod 2) - ((q'+rho') mod 2) for rho' >= 1 and
          q' <= l-1-(q' mod 2) for rho' = 0.  Here lq'+rho' <= l(l-2)+1, so q' <= l-2, and q' = l-2 forces rho' in {0,1}: both hold (equality).
          q' = l-3 (even): right side l-3.  q' <= l-4: clear.
   e = 1: W ends with the first letter of the extra pair, or begins with its second letter; then W' ends just before / begins just at a
          period start.  Need F(W') + 1 <= floor((lq'+rho'+l+2)/2).  If W' ends at a period end, its first rho' letters are the last rho'
          letters of a period (. F . F ... F .): floor(rho'/2) letters F, so F(W') <= q'(l+1)/2 + floor(rho'/2) and the inequality reads
          q' <= l + (rho' mod 2) - ((q'+rho'+1) mod 2), true for q' <= l-1.  If W' begins at a period start, its last rho' letters are
          FF.F.. : at most floor(rho'/2)+1 letters F: need q' <= l-2+(rho' mod 2)-((q'+rho'+1) mod 2): true for q' <= l-3; for q' = l-2 (odd)
          the right side is l-2.
 Step 3 (L = 2K+z, 1 <= z <= 2h = H-2K).  If L = H: every window of length H has F(W) = 2h^2+2h+2 = floor((H+l+1)/2) (the word has
   period H): done; so let L < H, z <= 2h-1.  A symbol occurs three times in W exactly for the triples (s, s+K, s+2K), s in S0 cap [t, t+z), and
   (s+K, s+2K, s+3K+1), s+K in [t, t+z-1); tr = their number; need F(W) <= floor((L+l+1)/2) + tr.  Here L = l(l-2)+3+z.
   e = 0: L <= H-2 = l(l-1), q = l-2 (or q = l-1, rho = 0): true without tr (sec. 5 algebra, q <= l-1).
   e = 2: L-2 = l(l-2)+(z+1): q' = l-2, rho' = z+1 (or q' = l-1, rho' = 0 when z = l-1: equality).  The inequality reads
          (rho' mod 2) + tr >= 1 if F(W') is maximal, and holds otherwise.  For rho' even, F(W') = q'(l+1)/2 + rho'/2 + 1 forces the first
          rho' letters of W' to contain a period pair FF whose first letter x is at index u <= rho'-2 = z-1 of W' (count floor(u/2)+2+
          floor((rho'-2-u)/2) with u even).  If x != 2 (mod H), then x is in S0, and its index in W is u (or the extra pair precedes
          it, and then that pair's first letter 0 or H, also in S0, has a smaller index): a point of S0 in [t, t+z).  If x = 2 (mod H),
          the extra pair inside W is the one immediately before x, at W-index u < z, and its first letter (0 or H) is in S0.  So tr >= 1.
   e = 1: q' = l-2, rho' = z+2 or q' = l-1, rho' in {0,1}: the e = 1 inequalities of Step 2 hold for q' <= l-2 without tr; for q' = l-1:
          W' ends at a period end: q' <= l - ... holds (right side >= l-1); W' begins at a period start with rho' in {0,1}: F(W') =
          q'(l+1)/2 + rho', need q'(l+1)/2 + rho' + 1 <= floor((lq'+rho'+l+2)/2) + tr: rho' = 0: q' <= l - ((q'+1) mod 2) true;
          rho' = 1: q' + 4 <= l + 3 - (q' mod 2) + 2tr, i.e. q' <= l-1 + 2tr: true.   QED (pending referee)
CONSEQUENCE: K(n,k) >= 4k+2l+2 for k = (l-1)^2/2, n = (3k+l+1)/2, for every l = 3 (mod 4), l >= 15 (proof l >= 43, computer 15..39), and
for l = 7, 11 by the DFS codes: k_max(l) >= (l-1)^2/2 for all l = 3 (mod 4), l >= 7.  With sec. 5: k_max(l) >= (l-1)^2/2 for ALL odd l >= 7.

## RESULTS (S165; regenerate with struct/results.py and struct/exacttab.py)

Existence of a code of length 4k+2l+2 for every k in the range of Conjecture 4.2 (state at 13:40; C = code on file, validated;
c = code by Deimer contraction of one on file; X = proved none (skeleton UNSAT / no type word / S161-162 SAT proofs);
T = none by the Main Theorem; ? = open or still running):

    l= 5 (thr 12) largest k with a code: None  | 8X 10X 12X 14T
    l= 6 (thr 14) largest k with a code: 13  | 13C 15T
    l= 7 (thr 24) largest k with a code: 18  | 12C 14C 16C 18C 20X 22X 24X 26T
    l= 8 (thr 27) largest k with a code: 25  | 17C 19C 21C 23C 25C 27X 29T
    l= 9 (thr 40) largest k with a code: 40  | 16C 18C 20C 22C 24C 26C 28C 30C 32C 34C 36C 38C 40C 42T
    l=10 (thr 44) largest k with a code: 39  | 21C 23C 25C 27C 29C 31C 33C 35C 37C 39C 41? 43? 45T
    l=11 (thr 60) largest k with a code: 38  | 20C 22C 24C 26C 28C 30C 32C 34C 36C 38C 40? 42? 44? 46? 48? 50? 52? 54? 56X 58X 60X 62T
    l=12 (thr 65) largest k with a code: 37  | 25C 27C 29C 31C 33C 35C 37C 39? 41? 43? 45? 47? 49? 51? 53? 55? 57? 59? 61? 63? 65? 67T
    l=13 (thr 84) largest k with a code: 84  | 24C 26C 28C 30C 32C 34C 36C 38? 40? 42? 44? 46? 48? 50? 52? 54? 56? 58? 60? 62? 64? 66? 68? 70? 72? 74? 76? 78? 80? 82? 84C 86T

LINES COMPLETE: l=5 (none for k>=8), l=6 (k=13 only), l=7 (k=12..18), l=8 (k=17..25), l=9 (EVERY k=16..40: the Main Theorem is
sharp at l=9: (65,40) has 2k+1 = l^2 and a code of length 180 exists, codes/skel_65_40_180.txt).

Exact values in the Lemma-2 region (candidates = lengths not excluded by Lemma 1 at L0):

    l= 7 k=20  K(34,20) = 94  (= 4k+2l+0)  candidates ['+2']
    l= 7 k=22  K(37,22) = 102  (= 4k+2l+0)  candidates ['+2']
    l= 7 k=24  K(40,24) = 110  (= 4k+2l+0)  candidates ['+2']
    l= 7 k=26  K(43,26) = 118  (= 4k+2l+0)  theorem
    l= 8 k=19  K(33,19) = 96  (= 4k+2l+4)  candidates ['+2', '+4']
    l= 8 k=21  K(36,21) = 102  (= 4k+2l+2)  candidates ['+2']
    l= 8 k=23  K(39,23) = 110  (= 4k+2l+2)  candidates ['+2']
    l= 8 k=25  K(42,25) = 118  (= 4k+2l+2)  candidates ['+2']
    l= 8 k=27  K(45,27) = 124  (= 4k+2l+0)  candidates ['+2']
    l= 8 k=29  K(48,29) = 132  (= 4k+2l+0)  theorem
    l= 9 k=26  K(44,26) = 124  (= 4k+2l+2)  candidates ['+2', '+4']
    l= 9 k=28  K(47,28) = 132  (= 4k+2l+2)  candidates ['+2']
    l= 9 k=30  K(50,30) = 140  (= 4k+2l+2)  candidates ['+2']
    l= 9 k=32  K(53,32) = 148  (= 4k+2l+2)  candidates ['+2']
    l= 9 k=34  K(56,34) = 156  (= 4k+2l+2)  candidates ['+2']
    l= 9 k=36  K(59,36) = 164  (= 4k+2l+2)  candidates ['+2']
    l= 9 k=38  K(62,38) = 172  (= 4k+2l+2)  candidates ['+2']
    l= 9 k=40  K(65,40) = 180  (= 4k+2l+2)  candidates ['+2']
    l= 9 k=42  K(68,42) = 186  (= 4k+2l+0)  theorem
    l=10 k=25  K(43,25) = 124  (= 4k+2l+4)  candidates ['+2', '+4']
    l=10 k=27  K(46,27) = 132  (= 4k+2l+4)  candidates ['+2', '+4']
    l=10 k=29  K(49,29) in [138,140]  (= 4k+2l+2..4)  candidates ['+2', '+4']
    l=10 k=31  K(52,31) = 146  (= 4k+2l+2)  candidates ['+2']
    l=10 k=33  K(55,33) = 154  (= 4k+2l+2)  candidates ['+2']
    l=10 k=35  K(58,35) = 162  (= 4k+2l+2)  candidates ['+2']
    l=10 k=37  K(61,37) = 170  (= 4k+2l+2)  candidates ['+2']
    l=10 k=39  K(64,39) = 178  (= 4k+2l+2)  candidates ['+2']
    l=10 k=41  K(67,41) in [184,186]  (= 4k+2l+0..2)  candidates ['+2']
    l=10 k=43  K(70,43) in [192,194]  (= 4k+2l+0..2)  candidates ['+2']
    l=10 k=45  K(73,45) = 200  (= 4k+2l+0)  theorem
    l=11 k=32  K(54,32) in [152,156]  (= 4k+2l+2..6)  candidates ['+2', '+4', '+6']
    l=11 k=34  K(57,34) in [160,162]  (= 4k+2l+2..4)  candidates ['+2', '+4']
    l=11 k=36  K(60,36) in [168,170]  (= 4k+2l+2..4)  candidates ['+2', '+4']
    l=11 k=38  K(63,38) in [176,178]  (= 4k+2l+2..4)  candidates ['+2', '+4']
    l=11 k=40  K(66,40) in [182,184]  (= 4k+2l+0..2)  candidates ['+2']
    l=11 k=42  K(69,42) in [190,192]  (= 4k+2l+0..2)  candidates ['+2']
    l=11 k=44  K(72,44) in [198,200]  (= 4k+2l+0..2)  candidates ['+2']
    l=11 k=46  K(75,46) in [206,208]  (= 4k+2l+0..2)  candidates ['+2']
    l=11 k=48  K(78,48) in [214,216]  (= 4k+2l+0..2)  candidates ['+2']
    l=11 k=50  K(81,50) in [222,224]  (= 4k+2l+0..2)  candidates ['+2']
    l=11 k=52  K(84,52) in [230,232]  (= 4k+2l+0..2)  candidates ['+2']
    l=11 k=54  K(87,54) in [238,240]  (= 4k+2l+0..2)  candidates ['+2']
    l=11 k=56  K(90,56) = 246  (= 4k+2l+0)  candidates ['+2']
    l=11 k=58  K(93,58) = 254  (= 4k+2l+0)  candidates ['+2']
    l=11 k=60  K(96,60) = 262  (= 4k+2l+0)  candidates ['+2']
    l=11 k=62  K(99,62) = 270  (= 4k+2l+0)  theorem
    exact values listed: 31

Timings of the skeleton SAT (skelfree.py, kissat): (21,12) 2 s, (15,8) 2.6 s, (18,10) 1.8 s, (40,24) 38 s, (37,22) 51 s,
(34,20) 134 s, (45,27) 221 s [all UNSAT; DRAT-verified: struct/certskel.out for 21/12, 37/22, 40/24, 34/20, 45/27];
SAT side: (36,21) 26 s ... (62,38) 380 s, (65,40) 948 s; dots (stage3.py) 0.3-46 s.
Type-word route (stage1.c + skel.py): (40,24) 0 words; (37,22) 0 words; (34,20) 46 classes, 46/46 UNSAT; (45,27) 4 classes, 4/4 UNSAT;
(96,60), (93,58), (90,56) 0 words (=> kmax(11) <= 54). The two routes agree wherever both were run.
Excess 4: codes (33,19) N=96 [K=96], (43,25) N=124 [K=124], (46,27) N=132 [K=132], (22,12) N=66; none at (44,26,126) [K(44,26)=124], (25,14,74), (28,16,82).
The zero-slack code (65,40,180) has the shape predicted by the hand analysis of section 2 (struct/zshape.py): type word of
period 9 = FF.F.F.F. ; 20 coordinates with gaps (41,41,a,b), (a,b) in {(42,56),(47,51),(51,47),(56,42)}; 5 coordinates with gaps
(41,45,49,45) x3, (41,49,45,45), (45,45,45,45); dots with gaps 84..90.

CAUTION: a SAT skeleton need not complete: (51,30,144): stage3 UNSAT for the first skeleton (a code exists, by contraction).
A 'no code' conclusion always needs skelfree UNSAT; a 'code' conclusion always needs the completed, validated code.

## Checks

 * REFEREE (fresh agent, adversarial, files in theory/referee2/): mathematics of (S1)-(S4), section 2 and the l=5 counting argument
   re-derived, no error. Own SAT enumerator of type words (wenum.py; every model re-checked by a literal checker; brute.c for
   small cases): (40,24) 0 words; (37,22) 0 words (kissat + cadical, DRAT VERIFIED); (34,20) 46 classes / 4128 words, list identical
   to words_34_20.txt, and UNSAT with the 46 classes blocked (DRAT VERIFIED); (21,12) 1/5; (23,13) 14/891; (45,27) 4/49.
   skel.py read clause by clause: every clause necessary, UNSAT is a valid proof; 36 real codes SAT, also with the real skeleton
   forced. Own skeleton encoder myskel.py (different window bookkeeping, cadical): (34,20) 46/46 UNSAT, (21,12) UNSAT, 16 real
   codes SAT. FOUND: stage1.c is wrong when gmax > 2K+1 (k < 2l-4; e.g. (7,3), (9,4)) -- no case used is affected; stage1 now
   refuses such input. Not verified by the referee: skelfree.py (written after its brief), stage-2 UNSATs for (45,27), the large
   stage-1 counts ((93,58), (96,60)), Byrnes' constructions.
 * skelfree.py (not seen by the referee): agrees with the type-word route on (34,20), (37,22), (40,24), (45,27), (21,12);
   regression on 8 known answers ((15,8,44), (18,10,52), (21,12,60) UNSAT; (12,6,36), (14,7,42), (17,9,50), (20,11,58), (23,13,66) SAT);
   every SAT answer was turned into a real code and validated from the definition; UNSATs (21,12), (37,22), (40,24), (34,20),
   (45,27) have DRAT proofs checked by drat-trim (struct/certskel.out). NO DRAT yet for (25,14,74), (28,16,82), (44,26,126).
 * n >= 65: checkc (64-bit) cannot check; (65,40,180) has the inline checks + check.py only.
 * structcheck.py: (S1), (S2) (identity incl. sd and the j=0 triple term) on real excess-2 codes of (23,13), (25,14), (31,18), (42,24): 0 failures.
 * wordcheck.py (python, written separately from stage1.c): conditions (S3a),(S3b) on the type words of ~2,400 real codes
   on lines l = 6..11, both parities of k: 0 violations (and (b) is active: thousands of windows exceed the plain bound).
 * skel.py: UNSAT on the (21,12) word (agrees with the DRAT-certified SAT proof of K(21,12)=58), SAT on a real (31,18) word.
 * NOT yet done at the time of writing: an enumerator for stage 1 written by someone else; DRAT for the stage-2 UNSATs;
   a human reading. (Referee pass: S165.)

## 7. l = 0 (mod 4): the zero-slack case is impossible  (S168, 2026-11-10 20:50; hand proof)

THEOREM 7. Let l = 0 (mod 4), l >= 8, k = (l^2-l-2)/2 (the largest k NOT covered by the Main Theorem for even l; k is odd),
n = (3k+l+1)/2. Then no spread-k coil of length 4k+2l+2 exists in Q_n, and K(n,k) = 4k+2l (Byrnes' codes attain it).
So k_max(l) <= (l^2-l-6)/2 for l = 0 (mod 4); family 3 (struct/even/evenfam.py) gives equality for 8 <= l <= 100.

Numbers. K = k+1 = l(l-1)/2 (even), N = 4k+2l+2 = 2(l-1)(l+1), L0 = 2k+2 = 2K = l(l-1), n-k = l(l+1)/4, so there are
l(l+1) F positions; gmax = N-3K = (l+4)(l-1)/2 < 2K. Put p = N-4K = 2l-2. Then N = (l+1) p and K = (l/4) p: K = 0 (mod p).
(This is where l = 0 mod 4 enters; for l = 2 mod 4, (l^2-l-2)/2 is even, so zero slack does not occur on those lines.)
(H) of section 1 holds: (n-k)(4L0-N) = l(l+1)/4 * 2(l-1)^2 = N * l(l-1)/4 = N c0 (c0 = floor((L0-k)/2) = K/2), so
(n-k+1)(4L0-N) > N c0. Hence (S1)-(S3) apply to a hypothetical code C of length N.
Notation as in PROOF.md: g_i = distance from position i to the next occurrence i+ of the same coordinate, e_i = g_i - K >= 0,
and E_i = e_i + e_{i+}. For an F coordinate the four gaps sum to N, so e_i + e_{i+} + e_{i++} + e_{i+++} = p.

Step A (the type word has period p and contains FF). (S3a) with Lw = 2K: F(W) <= floor((2K+l+1)/2) = l^2/2 for each of the
  N windows of length 2K, and the mean of F(W) is 2K * l(l+1) / N = l^2/2. So F(W) = l^2/2 for every 2K-window; comparing the
  windows starting at t and t+1: phi(t) = phi(t+2K) for all t. So phi has period gcd(2K, N) = (l-1) gcd(l, 2l+2) = 2(l-1) = p,
  with l(l+1) p / N = l letters F among the p = 2l-2 letters of a period. Since l > p/2, two cyclically adjacent positions of
  a period are both F: there is s with phi(s) = phi(s+1) = F ("FF pair at s"), and then, because K = 0 (mod p), there are FF
  pairs at s+K, s+2K, s+3K as well.
Step B (C1: every FF pair starts a triple). Let (s, s+1) be an FF pair and W = [s, s+2K+2). Then F(W) = F[s, s+2K) + phi(s+2K)
  + phi(s+2K+1) = l^2/2 + 2, while floor((Lw+l+1)/2) = floor((l^2+3)/2) = l^2/2 + 1 (gmax <= Lw = 2K+2 <= min(3K, N-k)). By (S3),
  with sd(W) >= 0: tr(W) >= 1. Three occurrences of one coordinate inside W are consecutive occurrences i < i+ < i++ (a
  skipped occurrence would give a span >= 3K > 2K+1) with i >= s and i + 2K + E_i <= s+2K+1. Hence
        (C1)   E_s <= 1   or   E_{s+1} = 0,
  i.e. (e_s, e_{s+}) is (0,0), (0,1) or (1,0), or (e_{s+1}, e_{(s+1)+}) = (0,0).
Step C (Y2). For any t the window [t, t+K+2) has length K+2 = k+3, so odd >= k+1 by (F1); no coordinate occurs three times in
  it and odd = K+2 - 2 ch, ch = number of pairs (i, i+) inside. So ch <= 1. The pair (t, t+) is inside iff e_t <= 1 and the
  pair (t+1, (t+1)+) is inside iff e_{t+1} = 0. Hence
        (Y2)   not both  e_t <= 1  and  e_{t+1} = 0.
Step D (chase). Take an FF pair at s; by Step A there are FF pairs at s+K and s+2K, and C1, Y2 apply to them. Four cases from C1 at s:
  (0,0): e_s = e_{s+K} = 0; the coordinate sits at s, s+K, s+2K. C1 at the pair s+K: E_{s+K+1} = 0 would give e_{s+K+1} = 0
         together with e_{s+K} = 0, against Y2 (t = s+K); so E_{s+K} <= 1, i.e. e_{s+2K} <= 1. The fourth occurrence q of the
         coordinate then has e_q = p - e_{s+2K} >= p-1. C1 at the pair s+2K: E_{s+2K} = e_{s+2K} + e_q >= p-1 > 1, so
         E_{s+2K+1} = 0, in particular e_{s+2K+1} = 0, which with e_{s+2K} <= 1 contradicts Y2 (t = s+2K).
  (0,1): e_s = 0, e_{s+K} = 1; occurrences s, s+K, s+2K+1. C1 at the pair s+K: e_{s+K+1} = 0 is against Y2 (e_{s+K} = 1), so
         E_{s+K} <= 1, i.e. e_{s+2K+1} = 0; the fourth occurrence is s+3K+1 with e = p-1. C1 at the pair s+2K:
         E_{s+2K+1} = 0 + (p-1) > 0, so E_{s+2K} <= 1, so e_{s+2K} <= 1, which with e_{s+2K+1} = 0 contradicts Y2.
  (1,0): e_s = 1, so s+ = s+K+1, and e_{s+K+1} = 0; occurrences s, s+K+1, s+2K+1. Y2 at t = s+K: e_{s+K} >= 2, so
         E_{s+K} >= 2 and C1 at the pair s+K gives E_{s+K+1} = 0, i.e. e_{s+2K+1} = 0; the fourth occurrence is s+3K+1 with
         e = p-1. Y2 at t = s+2K: e_{s+2K} >= 2, so C1 at the pair s+2K needs E_{s+2K+1} = 0; but E_{s+2K+1} = p-1 > 0.
  (b):   e_{s+1} = e_{s+K+1} = 0; occurrences s+1, s+K+1, s+2K+1. Y2 at t = s+K: e_{s+K} >= 2, so C1 at the pair s+K gives
         E_{s+K+1} = 0, i.e. e_{s+2K+1} = 0. Y2 at t = s+2K: e_{s+2K} >= 2, so C1 at the pair s+2K gives E_{s+2K+1} = 0, i.e.
         e_{s+3K+1} = 0. Then four consecutive gaps of an F coordinate are K, K, K, K, with sum 4K < N. Contradiction.
  (p - 1 = 2l-3 > 1 is used; only two window lengths, K+2 and 2K+2, enter besides Step A.)
All four cases are contradictory, so C does not exist.
Upper bound for longer codes: N = 4k+2l+e, 4 <= e <= k+4-2l is excluded by Lemma 1 (PROOF.md: f(2) = 0 here, f concave,
f(k+4-2l) = k(k+8-3l) - (4l-8) > 0 because k+8-3l = (l^2-7l+14)/2 >= 11 and k >= 27 for l >= 8; so f > 0 for
2 < e <= k+4-2l), N >= 5k+4 by Lemma 2 (k > 3l-7). Hence K(n,k) = 4k+2l. QED
(Steps A-D also work verbatim for l = 4: no (10,5) coil of length 30, consistent with K(10,5) = 28; l >= 8 is needed only for
Lemma 2 and for Byrnes' lower bound. In case (0,0) E_{s+2K} is exactly p; in case (b) e_{s+3K+1} would have to be p, not 0.)
REFEREE #9 (independent agent, S168 20:53): NO ERROR FOUND; all steps re-derived; the one gap (f(k+4-2l) > 0 was cited from
PROOF.md under a different hypothesis) is fixed above. Its tests (theory/referee9/): arith.py identities l = 8..400; codes_test.py
Y2 on 154 code files (48,022 windows), (S3) at Lw = 2K, 2K+2 on 112 excess-2 codes, 'triple at s or s+1 whenever F(W) exceeds
the floor' 1,323 windows: 0 violations; stepD_sat.py (C1 at the FF pairs s, s+K, s+2K + Y2 + gap sum, written from the text):
UNSAT for l = 4..20, and SAT as soon as any one ingredient is dropped. Referee's side remark: 'family 3 gives equality' rests on
computer-built codes (l <= 100), not on a proof; and (H) of section 1 fails for 17 con_* files (those are not excess-2 'skeleton' codes).

Remark (why l = 1 mod 4 escapes): there the period is l, K = (l+1)/2 (mod l), and the pairs/triples of the A coordinates
(gaps K, K, K+1) land on DIFFERENT residues, so the chase never returns to an FF pair with a constrained neighbour.
Machine checks: (45,27) [l=8]: stage1 gives 4 type words, all period p = 14 (FF at distance 1, 3, 5, 7); for each of them
refl/genlazy.py with EAGER=K+2,2K+2 SEEDY=0 (ONLY the windows of these two lengths + the gap structure) is UNSAT, as the proof
says. (104,65) [l=12]: 6 type words, all period 22.

## 8. l = 3 (mod 4): no excess-2 code for (l^2-l+2)/2 <= k <= (l^2-5)/2   (S168, 2026-11-10 21:50; hand proof)

THEOREM 8. Let l = 3 (mod 4), l >= 11, and k = (l^2-1)/2 - 2j with 1 <= j <= (l-3)/4 (k even), n = (3k+l+1)/2.
Then no spread-k coil of length 4k+2l+2 exists in Q_n; hence K(n,k) = 4k+2l.
(j = 0 is section 2. So for l = 3 mod 4 an excess-2 code needs k <= (l^2-l-2)/2. The boundary value k = (l^2-l-2)/2, j = (l+1)/4,
is NOT covered by this proof; it is refuted by computer for l = 7, 11, 15, 19 (struct/odd3/wfree.py), which gives
k_max(l) = (l^2-l-6)/2 for l = 7, 11, 15, 19 [codes: (31,18), (84,52), family 5 for l = 15, 19].)

Numbers. K = k+1 = (l^2+1)/2 - 2j is odd; N = 4k+2l+2 = 4K+2l-2; L0 = 2k+1 = 2K-1 = l^2-4j; there are 4(n-k) = 2K+2l F positions;
gmax = N-3K = K+2l-2. (H) of section 1: (n-k+1)(4L0-N) - N c0 = 6k+3-2l-l^2 > 0. So (S1)-(S3) hold for a hypothetical code C.
K >= (l^2-l+4)/2 >= 4l-2 for l >= 11.

Walk. Put eps(t) = +1 if position t is F, -1 if it is a dot, and let w: Z -> Z be the walk with w(t+1) = w(t) + eps(t) (indices
of the cyclic word unrolled). Delta(a,b) = w(b) - w(a) = 2 F[a,b) - (b-a). One turn: w(t+N) = w(t) + 2(2K+2l) - N = w(t) + 2l+2.
(U1) (S3a), gmax <= L <= 2K: Delta(t,t+L) <= l for odd L, <= l+1 for even L.
(U2) L = 2K+1: (S3b) with ITS index equal to 0 (i.e. Lw = 2K+1) gives F(W) <= K+(l+1)/2+tr(W) and tr(W) <= 1, so Delta(t,t+2K+1) <= l+2; and if equality holds
     then tr = 1: positions t, t+K, t+2K carry the same F coordinate (three occurrences in 2K+1 positions with gaps >= K).
     In particular position t+K is F.
(L1) Delta(t,t+B) >= 2 for even B in [2l, 2K-2l+2] and >= 1 for odd B in [2l-1, 2K-2l+1]: the complement of the block in the
     cycle splits into two windows of lengths L1 + L2 = N-B in [gmax, 2K], both odd (Delta <= l each) resp. one odd and one even
     (<= l and <= l+1), and the three pieces add up to 2l+2. Concatenating blocks: Delta(t,t+B) >= 1 for EVERY B >= 2l-1
     (every integer >= 2l-1 is a sum of integers from [2l-1, 2K-2l+1], as 2K-2l+1 >= 4l-3).
(U3) Delta(t,t+B) <= l+1 for every 0 <= B <= 2K: for B >= gmax this is (U1); for B < gmax take B' = 2K, then
     Delta(t,t+B) = Delta(t,t+2K) - Delta(t+B,t+2K) <= l+1-1 by (L1) (2K-B > 2K-gmax = K-2l+2 >= 2l-1).
(L2) Delta(t,t') >= -l for all t < t': if t'-t >= 2l-1 this is (L1); otherwise Delta(t,t') = Delta(t-2K+1,t') - Delta(t-2K+1,t)
     >= 1 - (l+1) by (L1) and (U3).

Last exits. By (L1) the walk tends to +infinity as t -> +infinity and to -infinity as t -> -infinity, so u_m := max{t : w(t) = m} exists for every level m; the walk steps up twice
after u_m (FF at u_m, u_m+1); u_m < u_{m+1}; u_{m+2l+2} = u_m + N. Also v_m := min{t : w(t) = m} (first passage).
Put  x_m := u_{m+l} - u_m - (2K-1).
(X1) x_m >= 0 and x_m is even: Delta(u_m, u_m+2K-1) <= l by (U1), so the level m+l is still visited at or after u_m+2K-1;
     u_{m+l} - u_m = l (mod 2) since the walk changes parity at every step.
(X2) Sum of x_m over 2l+2 consecutive levels = l N - (2l+2)(2K-1) = 2l^2+2-4K = 8j   (the sum of u_{m+l}-u_m is l N).
(X3) If x_m = 0 then position u_m + K is F: w(u_m+2K-1) = m+l and u_m+2K-1 = u_{m+l} is a last exit, so
     w(u_m+2K+1) = m+l+2, i.e. Delta(u_m, u_m+2K+1) = l+2; apply (U2).
(X4) For every level m: v_{m+2} >= u_{m-l} + 2K+1, hence  x_{m-l} >= u_m + 2 - v_{m+2}.
     Proof: let a = u_{m-l}. For a <= t <= a+2K: w(t) <= m-l+l+1 = m+1 by (U3). For t < a: w(t) <= w(a)+l = m by (L2).
     So the level m+2 is not reached before a+2K+1, and x_{m-l} = u_m - a - (2K-1) >= u_m - v_{m+2} + 2.
Gaps: d_m := u_{m+1} - u_m, f_m := d_m - l. Then (pure algebra, indices of x mod 2l+2):
(G1) f_m + f_{m+1} + .. + f_{m+l-1} = u_{m+l} - u_m - l^2 = x_m - 4j.
(G2) f_{m-2} + f_{m-1} = -(x_m + x_{m+l}) =: -y_m <= 0, because
     u_m - u_{m-2} = N - (u_{m+2l} - u_{m+l}) - (u_{m+l} - u_m) = N - 2(2K-1) - x_{m+l} - x_m = 2l - x_m - x_{m+l}.

Step 1 (what a level with x_m = 0 needs). Let x_m = 0, q = u_m + K; q is F by (X3). w(q) = m+1 (mod 2) because K is odd, and
(l+1)/2 is even, so w(q) != m + (l+1)/2: either LOW: w(q) <= m+(l-1)/2, or HIGH: w(q) >= m+(l+3)/2.
Write l = 4c+3, a = (l+1)/2 = 2c+2, m0 := a + 2j, and X(S) := sum of x over the index set S (mod 2l+2).
 LOW. The level m+(l-1)/2 is visited at or after q, so u_{m+(l-1)/2} >= q = u_m + K: the first (l-1)/2 = 2c+1 gaps satisfy
   f_m + .. + f_{m+2c} >= K - l(l-1)/2 = a - 2j. By (G2) the pairs (m+1,m+2), .., (m+2c-1,m+2c) contribute -y_{m+3}, -y_{m+5}, ..,
   -y_{m+2c+1}; by (G1) and (G2) with x_m = 0: f_m = -4j + y_{m+3} + y_{m+5} + .. + y_{m+l}. Hence
        y_{m+2c+3} + y_{m+2c+5} + .. + y_{m+l}  >=  a + 2j = m0,      i.e.   X(m + P0) >= m0,
   P0 := O u (O + l),  O := {odd numbers in [(l+3)/2, l]}   (y_t = x_t + x_{t+l}; O and O+l are disjoint mod 2l+2).
 HIGH. q is F, so w(q+1) >= m' + 2 with m' := m + a. Put g := u_{m'} - q (odd, since u_{m'} - u_m = a = 0 and K = 1 mod 2).
   Then f_m + .. + f_{m+2c+1} (the first a gaps) = K + g - l a = g - (l-1)/2 - 2j, and by (G1) the last 2c+1 gaps satisfy
   f_{m+a} + .. + f_{m+l-1} = (l-1)/2 - 2j - g. As before (pairs from the left, and f_{m+l-1} = -4j + y_{m+2} + y_{m+4} + .. + y_{m+l-1}):
        y_{m+2} + y_{m+4} + .. + y_{m+a}  =  (l-1)/2 + 2j - g  =  m0 - 1 - g.
   If g <= -1 this is >= m0. If g >= 1: then u_{m'} > q+1 (w(q+1) != m'), while the level m'+2 was reached at q+1 or before:
   v_{m'+2} <= q+1. By (X4): x_{m'-l} >= u_{m'} + 2 - (q+1) = g+1. In both cases
        X(m + Q0) >= m0,    Q0 := E u (E + l) u {a - l},  E := {even numbers in [2, a]}
   (a - l = (3l+5)/2 mod 2l+2 is odd and lies in neither E nor E+l = {odd numbers in [l+2, (3l+1)/2]}).
Step 2 (the sets are intervals; note 2l+2 = 4a). l^2 = 1 (mod 2l+2), so m -> tau = l m is a bijection of Z_{2l+2} with m + l -> tau + 1 and
   m + 2 -> tau - 2. In the coordinate tau:  O = {l - 2i : 0 <= i <= c} -> {1, 3, .., 2c+1} and O+l -> {2, 4, .., 2c+2}, so
   P0 -> [1, a];   E = {2i : 1 <= i <= c+1} -> {-2, -4, .., -(2c+2)}, E+l -> {-1, -3, .., -(2c+1)}, a-l = (2c+2) - l -> l(2c+2) - 1
   = -(2c+3) (as 2l = -2), so Q0 -> [-(a+1), -1].  With xi(tau) := x_m (tau = l m):
        every tau with xi(tau) = 0 has   xi[tau+1, tau+a] >= m0   or   xi[tau-a-1, tau-1] >= m0       (cyclic intervals in Z_{4a}).
Step 3 (counting). The total mass is M = 8j < 2 m0 = l+1+4j (because 4j < l+1). So two 'chosen' intervals (one per zero of xi,
   one that satisfies the inequality) are never disjoint. They have at most a+1 points each, on a cycle of 4a points, and any
   of them meets a fixed one I, so all lie in a stretch of at most (a+1)+2a < 4a points: they are pairwise intersecting
   intervals of a line and have a common point p (Helly). A zero tau whose chosen interval [tau+1,tau+a] contains p lies in
   [p-a, p-1]; if [tau-a-1,tau-1] contains p then tau lies in [p+1, p+a+1]. So xi has at most 2a+1 zeros. But xi is even
   with sum 8j, so it has at most 4j nonzero values and at least 4a - 4j zeros; 4a - 4j <= 2a+1 gives 4j >= 2a-1 = l,
   i.e. j >= (l+1)/4, contradicting j <= (l-3)/4.  So C does not exist.
Longer codes: Lemma 1 excludes N = 4k+2l+e for 4 <= e <= k+4-2l (f(4) = 8k-6l-2l^2 > 0 and f(k+4-2l) = k(k+5-3l) > 0, f concave),
Lemma 2 excludes N >= 5k+4. Hence K(n,k) = 4k+2l (lower bound: Byrnes' codes, k >= 2l-2). QED
(Step 3 uses that xi has a zero: 4a-4j > 0. The proof uses only word-level facts ((U1), and (U2) => F at t+K), so it shows that
no TYPE WORD exists in this range. In HIGH, g >= 1 in fact forces g >= 3.)
REFEREE #10 (independent agent, S168 22:05): NO ERROR FOUND; every step re-derived; wording nits applied above. Its own tests
(theory/referee10/): arith.py l = 11..199 all j (39,696 checks); step23.py = Step 2/3 statement by brute force + its own SAT:
no solution for l = 11..23 (all j in range) and l = 27 (j <= 3), solutions exist at j = (l+1)/4; codes_test.py/walk.py: all facts
(U1)-(L2), (X1)-(X4), (G1), (G2) and the Step 1 conclusion on 64 real excess-2 codes with odd l (551 zero levels: 275 LOW, 276
HIGH) and on the 2,181 type words of (87,54) (2,156 of them contain adjacent dots; 42,038 zero levels: 20,228 LOW, 21,810 HIGH,
1,582 with a dip g >= 1): 0 violations.

Remarks. (i) Where l = 3 mod 4 enters: (l+1)/2 is even, so the middle occurrence of a triple can never sit at the 'balanced'
level m+(l+1)/2; for l = 1 mod 4 it can, and family 1 (section 5) lives there. (ii) At j = (l+1)/4 (k = (l^2-l-2)/2) the
reduced statement of Step 2 is satisfiable (two clusters of mass M/2 in two disjoint intervals), so a proof of that case must use
more (the SAT refutation needs the rule 'u, u+K-1 are not both starts of (K,K) triples' from the window of length K+2).
(iii) Machine checks: struct/odd3/xmodel2.py = Step 2 statement as a MILP: infeasible for every 1 <= j <= (l-3)/4, 11 <= l <= 35,
feasible at j = (l+1)/4; wfree.py = SAT over the type word (constraints (U1) at L0, L0-2, (U2), triple => F, Y2 rules):
UNSAT for l = 11 (k = 54), l = 15 (k = 104, 106, 108), l = 19 (k = 170, 178; 172-176 running); stage1 (all type words) had none
for l = 11, k = 56, 58 and l = 15, k = 110.

## 9. l = 3 (mod 4): the boundary case k = (l^2-l-2)/2   (S168, 2026-11-10 22:10; hand proof)

THEOREM 9. Let l = 3 (mod 4), l >= 11, k = (l^2-l-2)/2 (i.e. j = (l+1)/4 in the notation of section 8), n = (3k+l+1)/2.
Then no spread-k coil of length 4k+2l+2 exists in Q_n, and K(n,k) = 4k+2l.
COROLLARY (sections 2, 8, 9). For l = 3 (mod 4), l >= 11: an excess-2 code needs k <= (l^2-l-6)/2, i.e. k_max(l) <= (l^2-l-6)/2.
Equality holds for l = 11 ((84,52,232)) and l = 15, 19, .., 103 (family 5, computer-verified); l = 7: k_max = 18 = (l^2-l-6)/2 too.
(Same value as for l = 0 mod 4, section 7. Here K = l(l-1)/2 and N = 2(l^2-1) are the SAME numbers as in section 7.)

Everything in section 8 up to and including Step 2 holds verbatim for j = (l+1)/4 (K = l(l-1)/2 >= 4l-2 for l >= 11; (H) holds;
the range of j was used only in Step 3). Now a = (l+1)/2 = 2j, the total mass is M = 8j = 4a = 2l+2, m0 = 2a = M/2, and
K = l(l-1)/2 = a+1 (mod 4a) (K = (2a-1)(a-1) and 2a^2 = 0 mod 4a since a is even), l a = -a (mod 4a).
Besides the type-word facts we use (Y2) of section 7 (window of length K+2 = k+3: not both e_t <= 1 and e_{t+1} = 0; it holds
for every t, k even or odd), and: if x_m = 0 then by (X3) the positions u_m, u_m+K, u_m+2K carry one coordinate, i.e.
e_{u_m} = e_{u_m+K} = 0.

Step 1' (refined). Let x_m = 0, s = u_m, q = s+K, tau = l m. The identities in Step 1 of section 8 are exact:
 LOW (w(q) <= m+(l-1)/2):  xi[tau+1, tau+a] = 2a + G,  G := u_{m+(l-1)/2} - q >= 0, G even.
   G >= 2:  (LOWb)  xi[tau+1,tau+a] >= 2a+2.
   G = 0:   q = u_{m*} is the last exit of the level m* = m+(l-1)/2, whose coordinate is tau* = tau + K = tau+a+1.
            If x_{m*} != 0:  (LOWa1)  xi(tau+a+1) != 0.
            If x_{m*} = 0: the triple of m* is (q, q+K, q+2K), and q also lies in the triple (s, q, s+2K) of m; so one
            coordinate sits at s, s+K, s+2K, s+3K and e_{s+2K} = 0. Now s+2K-1 = u_{m+l} (x_m = 0) and s+2K-1, s+2K are an FF
            pair; (Y2) at t = s+2K-1 gives e_{s+2K-1} >= 2, so s+2K-1 does not start a triple: x_{m+l} != 0, i.e.
            (LOWa2)  xi(tau+1) != 0.
 HIGH (w(q) >= m+(l+3)/2):  xi[tau-a, tau-1] = 2a - 1 - g,  g := u_{m+a} - q odd  (E u (E+l) -> [-a,-1] in the coordinate tau).
   g <= -3: (HIGHb)  xi[tau-a,tau-1] >= 2a+2.
   g = -1:  u_{m+a} = q-1, so q-1, q is an FF pair and q-1 is a last exit. e_q = 0 (q is the middle of the triple of m). If
            x_{m+a} = 0 then q-1 starts a triple, e_{q-1} = 0, against (Y2) at t = q-1. So x_{m+a} != 0:
            (HIGHa)  xi[tau-a,tau-1] = 2a and xi(tau-a) != 0      (l(m+a) = tau - a).
   g >= 1:  x_{m+a-l} >= g+1 (section 8):  (HIGHc)  xi(tau-a-1) != 0 and xi[tau-a-1,tau-1] >= 2a    (l(m+a-l) = tau-a-1).
 So: xi is even, >= 0, of total mass 4a on the cycle Z_{4a}, and EVERY ZERO tau of xi satisfies one of
   LOWa1: xi[tau+1,tau+a] >= 2a and xi(tau+a+1) != 0        HIGHa: xi[tau-a,tau-1] >= 2a and xi(tau-a) != 0
   LOWa2: xi[tau+1,tau+a] >= 2a and xi(tau+1) != 0          HIGHb: xi[tau-a,tau-1] >= 2a+2
   LOWb : xi[tau+1,tau+a] >= 2a+2                           HIGHc: xi[tau-a-1,tau-1] >= 2a and xi(tau-a-1) != 0.
Step 2' (no such xi for a >= 6). Fix for every zero one option that holds and call its interval ([tau+1,tau+a], [tau-a,tau-1] or
 [tau-a-1,tau-1]; at most a+1 points, mass >= 2a = M/2) the chosen interval. xi has at most 2a nonzero values, so >= 2a zeros.
 (i) Suppose the chosen intervals pairwise intersect. As in section 8 they have a common point p, the zeros lie in
   [p-a,p-1] (LOW options) or [p+1,p+a+1] (HIGH options), so there are at most 2a+1 zeros, at least 2a-1 nonzero values, hence
   every nonzero value is 2 except at most one 4. p is not a zero, and the 2a-2 points outside [p-a,p+a+1] are nonzero, so at
   most one of the 2a+1 slots is nonzero. Two of p-3, p-2, p-1 are zeros; for such a zero tau the chosen interval is
   [tau+1,tau+a], inside [p-2,p+a-1], which contains at most two nonzero points: mass <= 6 < 2a. Contradiction.
 (ii) So two chosen intervals I1, I2 are disjoint: each has mass exactly 2a and xi vanishes outside them. Let H1, H2 be the
   hulls of the supports inside I1, I2 (s1, s2 <= a+1 points, mass 2a each) and let the two arcs between them, of g1 and g2
   points (all zeros), be the gaps; s1+s2+g1+g2 = 4a.
   Take a gap Gam going from the last point p' of a hull X to the first point p of the other hull Y, with gam points, and let
   gam' be the size of the other gap. Suf(t) := mass of the t points ending at p', Pre(t) := mass of the t points starting at p
   (t <= a+1). tH+ := least t with Suf(t) >= 2a+2, tH := least t with Suf(t) >= 2a; tL+, tL likewise for Pre.
   Suf exceeds 2a only when the t points contain X, the other gap and a point of Y: tH+ >= sX + gam' + 1; likewise
   tL+ >= sY + gam' + 1.   For the zero tau = p'+i = p-i' (i+i' = gam+1, 1 <= i <= gam):
     HIGH options: the interval [tau-a,tau-1] has mass Suf(a-i+1) and first point p'-(a-i+1)+1; for HIGHc the same with a-i+2.
       HIGHb: a-i+1 >= tH+.  HIGHa / HIGHc: t = a-i+1 / a-i+2 satisfies Suf(t) >= 2a and the point p'-t+1 is nonzero; since
       Suf is constant (= 2a) on [tH, tH+ - 1], such t is tH or >= tH+.   So i <= a+2-tH+ or i in {a+1-tH, a+2-tH}.
     LOW options: [tau+1,tau+a] has mass Pre(a-i'+1) and the point after it is p+(a-i'+1).  LOWb: a-i'+1 >= tL+.
       LOWa2: tau+1 nonzero means i' = 1.  LOWa1: t = a-i'+1 has Pre(t) >= 2a and the point p+t nonzero, i.e. Pre(t+1) > Pre(t);
       as Pre is constant on [tL, tL+ - 1], t = tL+ - 1 or t >= tL+.   So i' <= a+2-tL+ or i' = 1.
   All gam points of the gap are zeros, hence
        gam  <=  (a+1-sX-gam')^+ + (a+1-sY-gam')^+ + 3          (and the same with gam, gam' exchanged).
   Let gam >= gam' and s = s1+s2 >= 2, gam + gam' = 4a - s.  If gam' >= a both positive parts vanish: gam <= 3 < a. If gam' <= a-1:
   the right side is <= 3 + max(a - gam', 2a+2-s-2gam'), so either 4a - s - gam' <= 3 + a - gam', i.e. 3a <= 3+s <= 2a+5, a <= 5;
   or 4a - s - gam' <= 2a+5-s-2gam', i.e. 2a + gam' <= 5. Both are false for a >= 6.  QED (Step 2')
Longer codes as in section 8 (f(4) = 2l^2-10l-8 > 0, f(k+4-2l) = k(k+5-3l) > 0, Lemma 2). Hence K(n,k) = 4k+2l. QED

(In the option list '>= 2a' is used where Step 1' gives '= 2a' for LOWa, HIGHa: weaker, which is all Step 2' needs. Step 2' is
true for a = 4, 5 as well (machine); l = 7 is excluded only because section 8 needs K >= 4l-2. The corollary uses section 2.)
REFEREE #11 (independent agent, S168 22:25): NO ERROR FOUND; every step re-derived, all six admissible-index lists checked
separately; one unused false parenthetical removed. Its tests (theory/referee11/): Step 2' by its own SAT (cross-checked against
full enumeration for a <= 4): UNSAT for a = 5, 6, 8, 10, 12, 14, while the unrefined statement is SAT; either Y2 chase alone
(LOW or HIGH side) already suffices; Step 1' identities on the 2,181 words of (87,54): 42,038 zero levels, 0 violations, and
EVERY word has a zero level failing all six options (the reduction is complete on real data); on 38 real codes (l = 3 mod 4):
551 zero levels, both chase implications hold (premises occur 6 times, all at l = 7: thin, they rest on the hand argument).
Own check: struct/odd3/step2p.py (SAT): UNSAT a = 4..10.
Machine checks: struct/odd3/wfree.py (SAT over the type word with the rules A, C, E): UNSAT for l = 7, 11, 15, 19 at this k;
struct/odd3/xenum2.py (all two-cluster xi against the six options): 0 solutions for l = 7, 11 (xenum.py: 323 solutions at l = 11
when only 'LOW or HIGH with mass >= 2a' is asked); refl/zconf.py: each of the 2,181 type words of (87,54) has a pair u, u+K-1 of
triple starts.
