# PROOF14 (S171, 2026-11-11): the Lemma-1 bound for excess e is attained only if u >= 2e

Notation and setting as in PROOF13.md Part A (which this file continues; Lemmas A1-A4 are used). Even line: l even, k odd,
K = k+1 even, e >= 2 even, N = 4k+2l+e = 4K+2u with u = l+(e-4)/2, n = (3k+l+1)/2. Lemma 1 at L = 2K says that a code of
length N can exist only if K >= u(2u+e)/(2e); the "equality point" (e,u) is

    (E)   K = u(2u+e)/(2e).

**Theorem 33.** (Even lines: l even, k odd.) Assume (E) and K >= 2u+2. If u < 2e, there is no spread-k circuit code of length N = 4k+2l+e in Q_n.
More precisely: a code of that length exists only if  (a) K/gcd(K,u) is odd  and  (b) u >= 2e.

**Corollary 34.** (Even lines.) For every even e >= 2 the bound of Lemma 1 (L = 2K) for excess e is attained at most at the
equality points with u >= 2e and K/gcd(K,u) odd (those with K <= 2u+1, i.e. u < (3e + sqrt(9e^2+32e))/4, are not covered). For e = 0 (mod 4) it IS attained at
u = 2e, 3e, 4e, .. with the single exception (e, u) = (8, 16)  [PROOF10 Cor. 23: u = e*i, i >= 3; PROOF13 Cor. 32: u = 2e].
So among the equality points with K >= 2u+2, u = 2e is the exact threshold for every e = 0 mod 4, e != 8.

**Proposition U** (upper bound at equality points; even lines). Assume (E) and K >= 2u+2 (this implies u > 3e/2:
2e(K-2u-2) = 2u^2-3ue-4e >= 0). Then K(n,k) <= 4k+2l+e.
So wherever a code is exhibited at such a point, K(n,k) = 4k+2l+e; and where Theorem 33 excludes it, K(n,k) <= 4k+2l+e-2.

New single values (section 4): K(325,197) = 936 (e = 32, u = 72); no code of the Lemma-1 length at (209,125,616),
(216,129,640), (255,153,748), (418,251,1232), (432,259,1280), .. (all have u < 2e).

---------------------------------------------------------------------------------------------------------------------------

## 1. Proof of (a)

P = gcd(2K, N) = gcd(2K, 4K+2u) = gcd(2K, 2u) = 2g with g = gcd(K,u). If K/g is even, then P divides K, u/g is odd (K/g and
u/g are coprime), and N/P = 2K/g + u/g is odd: Theorem 24 (PROOF10 sec. 6; hypotheses (E), K >= 2u+2) says there is no code.
So for a code K/g is odd, i.e. P does not divide K, K = h (mod P) with h = P/2, and PROOF13 Part A applies to it.

## 2. Ladder runs need spacers

From now on C is a code in the setting (S) of PROOF13 Part A with P not dividing K. Recall: the type word has period P and
consists of 1-runs and 2-runs separated by single dots (Z6, A2); a 2-run {a,a+1} is of type (i) [a+h is F, a+h+1 a dot; every
position x of residue a starts the serve x -> x+K -> x+2K+1] or type (ii) [a+h a dot, a+h+1 F; x -> x+K+1 -> x+2K+1] (A3);
every position of residue a is the start, every position of residue a+1 the end of a serve of the class (A1, A3).
The "middle residue" of the 2-run a is mu(a) = a+h (type (i)) or a+h+1 (type (ii)). e(x) := g(x)-K ("excess"),
e'(x) := g(x-)-K, where x- is the previous position of the coordinate of x ("incoming excess").

(W') For every position t and 0 <= D <= K-1:
        #{ 0 <= i <= D : t+i is an F position and i + e(t+i) <= D }  <=  floor(D/2) + 1,
        #{ 0 <= i <= D : t-i is an F position and i + e'(t-i) <= D }  <=  floor(D/2) + 1.
Proof. The window W = [t, t+K+D+1) has length <= 2K, so every coordinate occurs at most twice in it and
odd(W) = (K+D+1) - 2 #(chords inside W) >= k: at most (D+2)/2 chords. The chord (x, x+) with x = t+i lies in W iff
x+K+e(x) <= t+K+D, i.e. i+e(x) <= D (dot chords are never inside: their gaps are >= 2K). The second line is the same for the
window (t-K-D-1, t] and the chords (y-, y), y = t-i.

**Lemma A5** (ladders). Let {a,a+1} be a 2-run of type (ii) whose middle residue b := a+h+1 lies in a 2-run. Then that 2-run
is {b, b+1}, it is of type (i) with middle residue a+1, and
        e = 1 on the residues a and a+1,  e = 0 on the residue b;      e' = 1 on the residues b and b+1.
Conversely, if a 2-run {b,b+1} of type (i) has its middle residue b+h in a 2-run, that 2-run is {a,a+1} with a = b+h-1 =
b-h-1, of type (ii) with middle residue b. Call such runs **ladder runs** ((ii)-ladder run a, (i)-ladder run b, partners).
Proof. a+h is a dot, so b = a+h+1 is the first element of its run: the run is {b,b+1}, and b+2 is a dot. b+h = a+1 is F and
b+h+1 = a+2 is a dot: type (i), middle residue a+1. Let x be a position of residue a; its serve is S = (x, x+K+1, x+2K+1) (A3),
so e(x) = 1 and e(x+K+1) = 0; x+K+1 runs over all positions of residue b as x runs over residue a. The position y = x+K+1 has
residue b, so it is the start of a serve of class b (A3: starts at offset 0), which is y -> y+K -> y+2K+1: hence
g(x+2K+1) = K+1, and x+2K+1 runs over all positions of residue a+1: e = 1 there. Incoming: the gap into y = x+K+1 is K+1
(e' = 1 on residue b), and the gap into y+2K+1 (residue b+1) is K+1 (e' = 1 on residue b+1).
Converse: b+h+1 is a dot, so b+h is the last element of its run {b+h-1, b+h} =: {a,a+1}; a+h = b-1 is a dot and a+h+1 = b is
F: type (ii) with middle residue b, which lies in the 2-run {b,b+1}. QED

A 2-run that is not a ladder run has its middle residue in a 1-run {r}; then r+h lies in that 2-run (mu(a)+h = a or a+1), so
{r} is saturated; call the 2-run a **single run** ((i)-single or (ii)-single). Different single runs have different middle
residues (mu(a) = mu(a') with a != a' would need a' = a-1 or a+1: overlapping 2-runs). Conversely every saturated 1-run is the
middle residue of a single run (proof of A4). So, per period:
        r2 = 2 Lad + s,      s = s_i + s_ii,
where r2 = number of 2-runs, Lad = number of ladder pairs, s = number of saturated 1-runs = number of single runs,
s_i / s_ii = number of (i)- / (ii)-single runs; and the number of unsaturated 1-runs is r1 - s.

**Lemma A6** (spacers). (1) Let {a,a+1} be a (ii)-ladder run. The run that follows it (it starts at a+3) is an unsaturated
1-run or a (ii)-single run.  (2) Let {b,b+1} be a (i)-ladder run. The run that precedes it (it ends at b-2) is an unsaturated
1-run or a (i)-single run.
Proof. (1) a+2 is a dot, a+3 is F (Z6) and starts a run. The partner is {b,b+1} with b = a+h+1, so b+2 = a+h+3 is a dot.
If the run is a 1-run {a+3}: it is not saturated, because (a+3)+h is a dot.
If it is a 2-run {a+3,a+4}: (a+3)+h is a dot, so it is of type (ii). If it were a ladder run, e = 1 on the residues a+3, a+4
(A5), and e = 1 on a, a+1: for a position t of residue a the first count of (W') with D = 5 contains i = 0, 1, 3, 4
(i+e = 1, 2, 4, 5): four > 3. So it is a (ii)-single run.   (K-1 >= 5 as K >= 2u+2 and u >= 2.)
(2) b-1 is a dot, b-2 is F and ends a run. The partner is {a,a+1} with a = b-h-1, so a-1 = (b-2)+h is a dot.
If the run is a 1-run {b-2}: not saturated. If it is a 2-run {b-3,b-2} =: {c,c+1}: c+h+1 = a-1 is a dot, so it is of type (i).
If it were a ladder run, e' = 1 on the residues c, c+1 and on b, b+1 (A5): for a position t of residue b+1 the second count of
(W') with D = 5 contains i = 0, 1, 3, 4 (positions b+1, b, c+1, c; i+e' = 1, 2, 4, 5): four > 3. So it is a (i)-single run. QED

## 3. Proof of (b)

Go around one period of the type word. By A6 (1) the map "(ii)-ladder run -> the run following it" is an injection of the Lad
(ii)-ladder runs into the set of unsaturated 1-runs and (ii)-single runs: Lad <= (r1 - s) + s_ii. By A6 (2), Lad <=
(r1 - s) + s_i. Adding: 2 Lad <= 2 r1 - s, and

        r2 = 2 Lad + s <= 2 r1.

Counting positions: the number of F coordinates is N/2 - n = (K + u + e/2)/2  (n = (3K + u - e/2)/2), so there are
2K+2u+e F positions and 2K-e dot positions in Z_N. Every run is followed by exactly one dot: M(r1 + r2) = 2K - e, and
M(r1 + 2 r2) = 2K+2u+e  (M = N/P periods). Hence M r2 = 2u+2e and M r1 = 2K-2u-3e, and with 2eK = u(2u+e):
        r2 <= 2 r1   <=>   2u+2e <= 4K-4u-6e   <=>   e(6u+8e) <= 2u(2u+e)   <=>   (u-2e)(u+e) >= 0   <=>   u >= 2e.   QED

Remarks. (1) At u = 2e (the points (33j, 20j-1, 96j) of PROOF13) all inequalities are equalities: s_i = s_ii, every
unsaturated 1-run follows a (ii)-ladder run and precedes a (i)-ladder run, every (ii)-single follows a (ii)-ladder run, every
(i)-single precedes a (i)-ladder run. Family 8 has s_i = s_ii = 1, the period-8 codes (j odd) s = 0.
(2) struct/ex4/p8/struc14.py tests A5, A6, the three inequalities and the position counts on every library code at an even
equality point (families 6, 7, 8, ladder families, solver codes): all pass; u/e ranges from 2 to 10.

## 4. Proposition U, and single points

Proof of Proposition U. k > 3l-7: k-3l+7 = K - 3u + 3e/2, and 2e(K - 3u + 3e/2) = 2u^2 - 5ue + 3e^2 = (2u-3e)(u-e) > 0. So
Lemma 2 (k odd) gives N' <= 5k+3 for every coil. Let N' = 4k+2l+e' with e' > e (e' even), so e' <= k+3-2l. Lemma 1 at L = 2K
applies (N' <= 5k+3 < 6K, N'/4 <= 2K <= N'-k) and requires f(e') <= 0, where (PROOF10 sec. 1)
2f(e') = (k+l-1+e')(4k+8-2l-e') - (4k+2l+e')(k+1) and 2f(e')-2f(e) = (e'-e)(2k+8-3l-e-e').
2f(e) = (K+u+e/2)(4K-2u) - (4K+2u)K = 2eK - 2u^2 - eu = 0 by (E). And 2k+8-3l-e-e' >= k+5-l-e = K+2-u-e/2 > 0 (K >= 2u+2).
So f(e') > 0: no coil is longer than 4k+2l+e. QED

Decision tool. struct/ex4/p8/eqpt.py e u: enumerates the type words (period P, runs 1/2) of an equality point and filters them
by Part A (no exactly antipodal 2-runs; 2s <= r1; (W') on the excesses forced by A3, A5); with 'sat' the surviving words go to
a lazy SAT (genlazy2.py with "exactly one serve per FF pair", optionally a shift symmetry). Results:

    (e,u) = (32,56)  (209,125,616):   5 words, none passes [also Theorem 33: u < 2e]
    (36,60)  (216,129,640), (36,66) (255,153,748), (64,112) (418,251,1232), (72,120) (432,259,1280),
    (100,160), (100,170), (100,180), (108,180):  no word passes [all u < 2e]
    (32,72)  (325,197,936):  7 of 126 words pass, and each of the 7 carries a code invariant under x -> x+36
             (codes/eq_325_197_936.txt, snake/check.py VALID).  With Proposition U: K(325,197) = 936 = Byrnes + 32.
    p = 8 points (u = 2e): words passing for j = 2..8: 0, 1, 1, 2, 1, 2, 4; each carries a code.
In every case so far, a word passes the filter iff it carries a code.

## Referee report (#28, S171)

A fresh AI agent (own programs in theory/referee28/: ref.py, grid.py; the author's scripts not read): PASS, no mathematical
error; three wording fixes (applied: 'even lines' and condition (a) in the statements, 'among points with K >= 2u+2' in
Cor. 34, the redundancy of u > 3e/2 in Prop. U). Re-derived by hand: section 1, (W'), A5 (with converse and e'), the single-run
bijection, A6 (1), (2) including degenerate periods, section 3, Prop. U. By program: all 194 library files valid; the 39 at
even-line equality points with K >= 2u+2 (e = 4..48, u/e = 2..10, N <= 2464) pass every lemma, inequality and count, and (W')
for all t, D <= 40; no library code at a point with u < 2e; exact-integer grid e <= 400, u <= 3000 (13,042 points) for Prop. U
and the algebra of sections 1, 3. Remarks: Lemma A4 is not needed for (b); in all 39 codes s_i = s_ii (not claimed).
Not checked: PROOF13 Part A and Theorem 24 (taken as given), the eqpt.py results of section 4.
NO HUMAN HAS READ THIS.
