# Circuit codes on the lines l = 2n-3k-1: where everything stands (written S168, 2026-11-10 night)

K(n,k) = maximum length of a spread-k circuit code in Q_n; l = 2n-3k-1 (k and l of opposite parity). Byrnes (arXiv 2008.04839)
constructs length 4k+2l for k >= 2l+1 (k odd) / 2l-2 (k even) and conjectures (Conj. 4.2) S(n,k,k+l) = K(n,k); since
S(n,k,k+l) = 4k+2l (his Theorem 1.3; formal for all k >= l-1, FORMAL.md item 33) this is equivalent to K(n,k) = 4k+2l.
k_max(l) := the largest k on the line l for which a code of length 4k+2l+2 exists (so the conjecture fails at k_max and, by the
theorems below, holds for every k > k_max).

| l mod 4 | k_max(l)                      | upper bound                              | lower bound (codes)                               |
|---------|-------------------------------|------------------------------------------|---------------------------------------------------|
| 1       | (l^2-1)/2,  l >= 9            | Thm 1 (PROOF.md)                         | family 1, Thm 5 (PROOF2 sec 5; l >= 13, l = 9 computer) |
| 0       | (l^2-l-6)/2,  l >= 8          | Thm 1 + Thm 7 (PROOF2 sec 7)             | family 3, Thm 10 (PROOF3.md)                       |
| 3       | (l^2-l-6)/2,  l >= 7          | Thm 1 + sec 2 + Thms 8, 9 (PROOF2 sec 8, 9; l >= 11) | family 5, Thm 11 (PROOF4.md; l >= 15); l = 7, 11: solver codes |
| 2       | in {(l^2-l-8)/2, (l^2-l-4)/2} | Thm 1                                    | family 4, Thm 12 (PROOF5.md; l >= 10); the upper value is attained for l = 6, 10, .., 38 (solver codes, S167) |

Theorems (numbering of the proof files):
 1  Main Theorem (PROOF.md): K(n,k) <= 4k+2l if k > (l^2-1)/2 and k > 3l-3 (l odd) / k > (l-2)(l+1)/2 (l even). Window counting, Lemmas 1, 2.
 -  PROOF2 sec 1-4: shape of excess-2 codes (type word, F-skeleton SAT), lines l = 7, 8, 9 by computer + hand examples.
 5  PROOF2 sec 5: family 1 (l = 1 mod 4, k = (l^2-1)/2) is a code; sec 6b: family 2 (superseded by family 5).
 7  PROOF2 sec 7: l = 0 mod 4, k = (l^2-l-2)/2: no code of length 4k+2l+2.
 8  PROOF2 sec 8: l = 3 mod 4, (l^2-l+2)/2 <= k <= (l^2-5)/2: none (no type word).
 9  PROOF2 sec 9: l = 3 mod 4, k = (l^2-l-2)/2: none.
 10 PROOF3.md: family 3 (l = 0 mod 4, k = (l^2-l-6)/2) is a code for all l >= 8.
 11 PROOF4.md: family 5 (l = 3 mod 4, k = (l^2-l-6)/2) is a code for all l >= 15.
 12 PROOF5.md: family 4 (l = 2 mod 4, k = (l^2-l-8)/2) is a code for all l >= 10.
 13 PROOF6.md (S169): EXCESS 4. l = 0 mod 4, l >= 8, k = (l^2+2l-4)/4: K(n,k) = 4k+2l+4 = l(l+4) exactly (family 6, ex4fam.py,
    invariant under x -> x+l; upper bound = Lemma 1 at L = 2K + Lemma 2). Referee #15 PASS. Also K(49,29) = 140 (l = 10, solver).
 14 PROOF7.md (S169): EXCESS 4 on l = 2 mod 8 (l = 8q+2 >= 10), k = (l^2+2l-4)/4: K(n,k) = 4k+2l+4 exactly (family 7, ex4fam7.py,
    invariant under x -> x+2l). Referee #16 PASS. So the excess-4 bound k <= (l^2+2l-4)/4 is attained for every even l >= 8 except
    l = 6 mod 8 (see 15). Excess 6: first zero-slack case (30,17,90) has NO code.
 15 PROOF8.md (S169): l = 6 mod 8, l >= 14, k = (l^2+2l-4)/4: NO code of length 4k+2l+4 (parity of the number of periods; referee #17 PASS).
 16 PROOF8.md: odd l = 5 mod 8, l >= 13, k = l(l+3)/4 (the only odd-line equality case): NO code of length 4k+2l+4 (referee #17 PASS
    with fixes). => a code of length 4k+2l+4 with equality in Lemma 1 exists iff l = 0, 2, 4 mod 8 (l >= 8). General form (not
    refereed): see 17.
 17 PROOF8.md sec 4 (referee #18 PASS): general excess e on even lines, N = 4K+2u, u = l+(e-4)/2, equality in Lemma 1 at L = 2K iff
    K = u(2u+e)/(2e); if 2u | K and K >= 2u+2 there is NO code. Cor 18: for e/2 odd squarefree (e = 6, 10, 14, ..) equality is never
    attained; e = 2 gives Theorem 7 again. e = 8, 12: one class of l in four excluded, the rest open (first: (66,39,192)).
 18 PROOF9.md (S170, referee #19 PASS): UNBOUNDED EXCESS with exact values. p = 0 mod 4, p >= 8, m ODD: k = m p(p+2)/4 - 1,
    n = m(3p-2)(p+4)/8 (l = mp-2m+2): K(n,k) = m p(p+4) = 4k+2l+4m. The family-6 residue design of period p, with K and N
    multiplied by m (m = 1 is Thm 13). First: K(99,59) = 288 (excess 12), K(165,99) = 480 (excess 20).
 19 PROOF9.md (referee #19 PASS): p = 0 mod 8, p >= 24, m odd: k = m p(p+4)/8 - 1, n = m(3p-4)(p+8)/16: K(n,k) = m p(p+8)/2 =
    4k+2l+8m. Design 8: three ladders = the three cyclic orders of the gap excesses (1,1,0,2u-2). K(136,83) = 384, K(230,143) = 640.
 20 PROOF9.md sec 6 (referee #20 PASS): Thm 18's statement also for p = 2 mod 8, p >= 10 (family 7 x m). Cor 21: at
    the equality point of excess 4m (m odd, u = mp) a code exists iff p != 6 mod 8. K(147,89) = 420.
 22 PROOF10.md (S170; referee #21 PASS): UNIFORM LADDER FAMILY, every excess e = 4j. Even j >= 2, i >= 3, period p = 4ji:
    ladders A at 0, B at 4, C at 8+5t (t = 0..j-2), forced N/4 fill, antipodal dots. Cor 23: for ALL j >= 1, i >= 3:
        K( j(6i-1)(i+1), 2ji(2i+1)-1 ) = 16ji(i+1) = Byrnes + 4j,   i.e. (n, k+1, K(n,k)) = j * ((6i-1)(i+1), 2i(2i+1), 16i(i+1)).
    So the Lemma-1 bound for excess e is attained at every equality point with u = l+(e-4)/2 = e*i, i >= 3, for every e = 0 mod 4.
    K(272,167) = 768 (excess 16), K(544,335) = 1536 (excess 32).
 24 PROOF10.md sec 6 (referee #22 PASS): general parity obstruction: (E), K >= 2u+2, p = gcd(2K,N) | K, N/p odd => no code.
    Cor 25: for EVERY e = 2 mod 4 the even-line bound of Lemma 1 is never attained (no 'squarefree' needed).
 26 PROOF10.md sec 7 (referee #23 PASS): ODD LINES: for e = 0 mod 4 the bound (Lemma 1 at L0 = 2K-1, equality K = u(u+1)/e+(u+2)/2,
    K >= 2u+3) is NEVER attained (generalises Thm 16): dots per type-word period must be even, and it is odd. e = 2 mod 4: half the
    points survive (struct/ex4/oddeq.py); e = 2: l = 1 mod 4 (family 1); first open e = 6 point (70,42,200).
    Also K(98,59) = 280 (excess 8, the 'K/u odd' class = 2 x family 7; SAT code, no family yet).
 27 PROOF11.md (S170; referee #24 PASS): ALL MULTIPLES OF FAMILY 7. lam = 8q+2, ANY j >= 1: the type word is H1^j H2^j
    (H1 H2 = family 7's word), ladders B, C, W, V of family 7 repeated at +lam*c (c < j), period 2j*lam.
    Cor 28 (with Cor 23): for every even p >= 10 and every j >= 1, at k = j p(p+2)/4 - 1, n = j(3p-2)(p+4)/8:
        K(n,k) = j p(p+4) = 4k+2l+4j  if p = 0, 2, 4 mod 8;     no code of that length if p = 6 mod 8.
    K(98,59) = 280, K(196,119) = 560, K(286,179) = 792.
 29 PROOF12.md (S170; referee #25 PASS): the uniform ladder designs for GENERAL (j, p, m): m odd, p = 0 mod 4, 4j | mp,
    p/2 >= 5j+2 (j even) / 5j+1 (j odd): K(n,k) = 4K+2mp = 4k+2l+4jm, K = mp(p+2j)/(4j). Contains Thms 13, 18, 19, 22; new points
    for e/4 not squarefree (e = 36, u = 0 mod 12: K(495,303) = 1408).
    Open equality points (struct/ex4/eqtable2.py): for e = 4j with j squarefree only u = 2e with j even (p = 8: (66,39,192),
    (132,79,384), ..; no A/B/C/E design in the shift-16/32 classes); for j not squarefree the points with j not dividing u (e = 36, ..).
 30 PROOF13.md Part B (S171; referee #27 PASS with cosmetic fixes): NO code of length 192 at (66,39): K(66,39) <= 190. By hand, from
    Part A = STRUCTURE at any equality point whose type-word period P does not divide K (K = P/2 mod P): every FF pair has
    exactly one serve (A1), runs of F's have length <= 2 (A2), a 2-run is of type (i)/(ii), never exactly antipodal to a 2-run
    (A3), saturated 1-runs (antipode inside a 2-run) are at most half of the 1-runs (A4).
 31 PROOF13.md Part C (referee #27): FAMILY 8 (struct/ex4/p8/p8fam.py, p8build.py; explicit, shift-P invariant, P = 8j): for every
    EVEN j >= 4:  K(33j, 20j-1) = 96j = 4k+2l+4j  (hand proof j >= 8; j = 4, 6 by computer). Cor 32: K(33j, 20j-1) = 96j for all
    j >= 1 except j = 2; so at u = jp (p even >= 8): code iff p != 6 mod 8 and (p,j) != (8,2). K(132,79) = 384, K(198,119) = 576.
 33 PROOF14.md (S171; referee #28 PASS, 3 wording fixes): at an even-line equality point (E) with K >= 2u+2 a code exists ONLY IF
    K/gcd(K,u) is odd AND u >= 2e. (Ladder runs need spacers: A5, A6; r2 <= 2 r1 <=> u >= 2e.) Cor 34: for e = 0 mod 4, e != 8,
    u = 2e is the exact threshold. Prop U: K(n,k) <= 4k+2l+e at every equality point with u > 3e/2, K >= 2u+2.
    Solver codes at formerly open points (struct/ex4/p8/eqpt.py = Part-A word filter + lazy SAT): K(325,197) = 936,
    K(465,285) = 1320 (e = 32, u = 72, 88). Status of every equality point: struct/ex4/eqtable3.py EMAX UMAX: for e <= 130 the
    only undecided points have u > 2e and e in {32, 36, 64, 72, 96, 100, 108, 128} (e/4 divisible by 8 or by an odd square).
 35 PROOF15.md (S171; referee #29 PASS): ODD LINES, UNBOUNDED EXCESS. FAMILY 9 (struct/ex4/p8/odd9.py; gap function of period 9):
    for every i >= 1:  K(143i+65, 90i+40) = 396i+180 = 4k+2l+(4i+2)  (l = 16i+9). K(208,130) = 576, K(351,220) = 972.
    Computer only (struct/ex4/p8/oddpt.py, oddsh.py = all type words + forced gaps K at FF pairs): NO code at the odd equality
    points (108,66,304), (87,52,252), (119,72,340), (168,102,480); codes at (418,266,1144) [p = 13], (270,170,744) [p = 31]
    (codes/odd_*). Pattern: (l,k) = (p,(p^2-1)/2) + i(2p-2, p(p+1)), p = 1 mod 4: i = 0 is family 1, p = 9 is family 9.
 36 PROOF16.md (S171; referee #30 PASS): FAMILY 10 (struct/ex4/p8/odd10.py p i; gap function of period p, all dots antipodal):
    for p = 1 mod 4, p >= 9, i >= 1:  l = p+(2p-2)i, k = (p^2-1)/2 + p(p+1)i:  K(n,k) = 4k+2l+4i+2 = 2p(p+1) + 4p(p+2)i.
    (p = 9: Thm 35. Thm 36' (PROOF16 sec 5, refereed): the same construction at i = 0 is a code => a short proof of Theorem 5
    (K = 4k+2l+2 at k = (l^2-1)/2, l = 1 mod 4) that includes l = 9, formerly computer-only.)
    K(418,266) = 1144, K(700,450) = 1904, K(703,448) = 1924.
Every proof was refereed by a fresh AI agent that re-derived it and wrote its own programs (reports summarised at the end of each
section/file; scripts in theory/referee3 .. referee14). NO HUMAN HAS READ ANY OF THIS. Prior art: Byrnes' three papers and both
Douglas 1969 papers were read in full. Douglas (J. Combin. Theory 6, 323-339) proves K = 4k+2l on the lines l = 2 (all odd k,
unique code), l = 3 (all even k), l = 4 (odd k >= 9) by case analysis of transition sequences, and states (no proof) the
bounds 4k+3l-1 / 4k+3l+2 for codes with a block of k+l distinct transitions; nothing for general l. So Theorem 1 is new only
for l >= 5 and at (13,7) (as far as we know). Singleton 1966 and Deimer 1984 were not accessible (Deimer's contraction is quoted from Byrnes).
Computer-only parts: Thm 5 at l = 9; Thm 10 Step 1 uses a finite list of 103 local patterns and direct checks for l <= 56;
Thm 11 Step 1 direct for l = 15, 19, 23; the solver codes; all exact values K(n,k) quoted for single pairs.

Open: (1) l = 2 mod 4: is k_max(l) = (l^2-l-4)/2 for all l? (codes found by lazy SAT in a reflection-symmetric class up to
l = 38; no formula; structure notes in README 'S167'). (2) Codes of length 4k+2l+4 and more ('excess >= 4': (33,19,96),
(22,12,66)): where do they exist? Lemma 1 allows them only for k <= ~l^2/4. (3) k <= 3l-3: Lemma 2 gives nothing.
Explicit codes: optcensus/codes/ (zfam_* family 1, efam_* families 3/4, ofam_* family 5, skel_*/sat_*/hsym_* solver codes);
generators theory/struct/zfam2.py, even/evenfam.py, evenfam2.py, oddfam.py; checkers snake/check.py, checkc.c.

FORMAL, S173 (PROOF17.md = written version): (a) the GAP CRITERION (one lemma that every family proof reduces to);
(b) FAMILY 10 for all parameters, lower and upper bound: K(n,k) = 4k+2l+4i+2 (Thms 36, 36'), so k_max(l) = (l^2-1)/2 EXACTLY for
every l = 1 mod 4, l >= 9; (c) THEOREM 37: Byrnes' sequence (2008.04839 eq. (8)) is a spread-k circuit code of length 4k+2l for
ALL l >= 2, k >= l-1 (own proof; his stated range is k >= 2l+1 / 2l-2); (d) COROLLARY 38: K(n,k) = 4k+2l whenever the Main
Theorem applies (the value Conjecture 4.2 predicts; the conjecture itself is S(d,k,k+l) = K(d,k): see (h), (i)) -- both
bounds machine-checked beyond ~l^2/2; (e) Cor 39: for l = 1 mod 4, l >= 9, the whole
half-line k >= (l^2-1)/2 is known exactly; (f) Deimer's contraction (set version) and THEOREM 40 = `conj42_fails`: for every
l >= 6 some k >= 2l+1 has a code longer than 4k+2l. (g) FAMILY 6 x m (Thm 18, all p = 0 mod 4, p >= 8, all odd m): K(n,k) = 4k+2l+4m, both bounds; (h) `conj42_region`: in the
Main-Theorem region S(n,k,k+l) = K(n,k) = 4k+2l (Byrnes' word is symmetric with bit run k+l): Conjecture 4.2 itself, formal.
(i) `symRun_le` / `symRun_le2` = Byrnes' upper bound S(n,k,k+l) <= 4k+2l (in Lemma 2's range, resp. for k > 3l-7 with the new
LEMMA 3: N <= 7k+5 for k >= 2l / 2l-3, six-block windows) and `conj42_false`: for EVERY l >= 6:
S(n,k,k+l) = 4k+2l < K(n,k) at some k >= 2l+1 -- the conjecture is false there with NO quoted step.
(j) Theorem 9 at l = 7 (K(34,20) = 94, formerly SAT) and `exact_l7`: K = 4k+2l beyond the thresholds on every line l >= 5
(l = 2: exact_l2; l = 3, 4: K_beyond only);
(k) `conj42_gap_family6` / `_family10`: at the points of families 6 x m and 10, S(n,k,k+l) = 4k+2l while K = S + 4m resp.
S + 4i+2; `conj42_gap_unbounded` (family 6 with p = 8): K - S is unbounded.
(l) `kmax_table`: k_max(l) for every l = 6..31 (13, 18, 25, 40, 43, 52, 63, 84, 89, 102, 117, 144, 151, 168, 187, 220, 229, 250, 273, 312, 323, 348, 375, 420, 433, 462), complete.
(m) THE BLOCK LEMMA (PROOF17 sec. 9, `blocks_bound`): N >= j(k+1)+k => j(k+1) + (j(j+1)/2-j)k <= floor((j+1)/2)floor((j+2)/2) n for
every j; so N <= (2s+1)k+2s-1 whenever (s+1)(l+1) < (s-1)k+4: an explicit upper bound for K(n,k) for all n <= 2k-1
(prior art not checked).
Still informal: the lower bounds of families 2-5, 7-9 and the even multiples (only instances are kernel-checked).

FORMAL VERIFICATION (S172, 2026-11-11): lean/ (Lean 4 + Mathlib; FORMAL.md = list of machine-checked statements).
Kernel-checked: Lemma 1, Lemma 2, Main Theorem (Thm 1), Theorem 7, THEOREMS 8 (incl. l = 7) and 9 (l >= 11; new proof of Step 2'), Theorems 15, 16, 17, 24, 26, Cor 25, the first half of
Theorem 33 (K/gcd(K,u) odd is necessary), PROOF2 sec 2 (l = 3 mod 4 zero slack), Prop U (both parities, all parameters), the
counterexample (23,13,66), and 94 exact values K(n,k) (code by a verified checker + Lemma 1/2). The formal Theorems 24 and 26 need
only 2 <= u < K resp. 3K <= N < min(6K, 8K-4) instead of K >= 2u+2 / 2u+3. Lemma 2 turned out to be a purely local statement
(one window of length 4K). Independent audit of the definitions and statements (agent; ccformal/audit/REPORT.md): no error,
IsCoil = the standard definition for n >= 2, k >= 1, N >= 4; 0 contradictions with 689 known lengths. => EVERY UPPER BOUND OF THE k_max TABLE ABOVE IS MACHINE-CHECKED (KmaxUpper.lean: kmax_upper_l0/l1/l2/l3; l = 3 mod 4 for l >= 11;
complete lines incl. the exact value at k_max: kmax_8, 9, 11, 12, 13, 15). NOT formal: Thms 30, 33(b), and all 'valid for every parameter' lower bounds.

EQUALITY IN LEMMA 1 (S169 summary; 'exists' = a code of that length exists at the k where Lemma 1 at L = 2K / 2K-1 is an equality):
  excess 2, odd l (>= 7):  exists iff l = 1 mod 4 (Thm 5 family 1, l >= 9; l = 3 mod 4: PROOF2 sec 2 hand proof)
  excess 2, even l: never (l = 0 mod 4: Thm 7 = Thm 17 with e = 2; l = 2 mod 4: k has the wrong parity)
  excess 4, even l: exists iff l = 0, 2, 4 mod 8 (Thms 13, 14, 15), l >= 8
  excess 4, odd l:  never (only equality case l = 5 mod 8: Thm 16)
  excess e = 2 mod 4 (6, 10, 14, 18, ..), even l: never (Cor 25, S170; K <= 2u+1 boundary cases aside)
  excess 4m, m odd, u = l+2m-2 = mp: exists iff p = 0, 2, 4 mod 8 (p >= 8)  (Thms 18, 20, 17; S170)   [e = 12, 20, 28: complete]
  excess 8m, m odd, u = l+4m-2 = mp, p = 0 mod 8, p >= 24: exists (Thm 19); u = 12 mod 16 (m = 1): never (Thm 17);
           OPEN: e = 8 at u = 4 mod 16 (l = 18, 34, ..) and u = 16 ((66,39,192)); (40,23,120) [K = 2u] has none (SAT).
  excess e = 4j, u = jp (all equality points when j is squarefree), p >= 10 even: exists iff p = 0, 2, 4 mod 8 (Cor 28, S170);
           p = 8: exists for odd j, OPEN for even j.   Odd lines, e = 0 mod 4: never (Thm 26).
  S171 (PROOF13, PROOF14): p = 8 (u = 2e): exists for every j = e/4 except j = 2 (family 8 for even j >= 4).
  GENERAL: on even lines (K >= 2u+2) a code at the equality point (e,u) exists only if u >= 2e and K/gcd(K,u) is odd (Thm 33);
  CONJECTURE: 'if and only if', except (e,u) = (8,16). The 'if' part is proved at every point that struct/ex4/eqtable3.py lists
  as decided: for e <= 130, u <= 1500 everything except points with u > 2e and e in {32, 36, 64, 72, 96, 100, 108, 128}
  (two of those, (32,72) and (32,88), have solver codes).
  ODD lines (S171, PROOF15): excess e = 2 mod 4 IS attained for arbitrarily large e: family 9, e = 4i+2 at l = 16i+9 (Thm 35);
  solver codes at other periods; the small points ((70,42), (108,66), (87,52), (119,72), (168,102)) carry no code.
