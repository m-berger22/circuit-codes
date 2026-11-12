# The second step: P((5K+1)/3, K-1) = 13K/3 + O(1) for K = 4 (mod 6)   (computer-assisted; independently re-checked, see the end)

Notation as in PROOF_threshold.md: a spread-k path, K = k+1, word T (letter T_x = coordinate flipped at step x),
vertices v_0, v_1, ...; any K consecutive letters are distinct, and d(v_x, v_y) >= K-1 whenever |x-y| >= K-1.
Here K is even, K = 6n+4, d = (5K+1)/3 = 10n+7, and the path has length 4K+E: four pieces of K letters and a tail of E.

**Theorem.** Let n >= 1 (K >= 10). If 0 <= E <= K-1 then E <= 2c + 39, where c = number of coordinates of type 23 (below).
(For E <= 39 there is nothing to prove; so below E >= 40, in particular E >= 8 and the number m = E-6 of deep columns is >= 34.)

**Corollary.** P((5K+1)/3, K-1) <= (13K+119)/3 for every K = 6n+4 >= 10, hence, with the family pfam3.py (length (13K+8)/3),
P((5K+1)/3, K-1) = 13K/3 + O(1) for K = 4 mod 6 (the family has length (13K+8)/3 for every n >= 1, proof PROOF_family_second.md).
Proof of the corollary. Paths of length < 4K satisfy the bound trivially. c <= n+1 (Section 4, last paragraph). Let n >= 10. If a path had E >= K, its prefix with tail K-1 is a
path with the same pieces, so K-1 = 6n+3 <= 2(n+1)+39, i.e. n <= 9: contradiction. So for n >= 10: E <= K-1, hence E <= 2n+41, i.e.
P <= 4K + 2n + 41 = (13K+119)/3. For 16 <= K <= 58 the bound follows from Theorem D of PROOF_threshold.md (P <= 5K-1 <= (13K+119)/3
exactly when K <= 61), and for K = 10 from P(17,9) = 46. So the corollary is NEW only for K >= 64; below that it is weaker than
what was known.

The constant 39 is crude (the conjecture is E <= 2n+4, attained by pfam3.py; it is the exact value for n = 1..5, see the README). The proof has three parts: a finite exhaustive computation
(Section 2), an elementary inequality (Section 3), and a count (Section 4).

## 1. States, moves, re-cutting

Throughout E <= K-1 (so every column index is < K and a tail letter and a piece letter of the same column are K apart).
For a shift 0 <= s <= E put P_j(s) = v_{jK+s}, j = 0..4 (five points) and W_j(s) = the window of the K letters between
P_j(s) and P_{j+1}(s), j = 0..3. Plotkin on the five points (PROOF_threshold.md Section 2, budget 6d - 10K = 2): every
coordinate splits the five points 2|3 ('pair state', named by the minority pair, ten of them), except that EITHER one
coordinate splits them 1|4 (a 'singleton') OR exactly one non-adjacent pair of points is at distance K+2; all other
distances are exactly K. Equivalently the state is the set of windows W_j(s) containing the coordinate (each window
contains it at most once): 01 = {W_1}, 34 = {W_2}, 12 = {W_0,W_2}, 23 = {W_1,W_3}, 04 = {W_0,W_3}, 02 = {W_0,W_1,W_2},
24 = {W_1,W_2,W_3}, 03 = {W_0,W_2,W_3}, 14 = {W_0,W_1,W_3}, 13 = all four.

The TYPE of a coordinate is its state at s = 0. Column s = the five letters at offset s of pieces 0, 1, 2, 3 and of the
tail ('piece 4'); passing from shift s to s+1 moves the letter of piece j from W_j to W_{j-1} (piece 0: out of W_0, tail:
into W_3). A coordinate that has no letter in columns 0..s-1 is in its type state at shift s.
A coordinate of type 23 has letters only in pieces 1 and 3 (and possibly the tail); once it has had a letter in some
column it is never in state 23 again (its W_1 occurrence can only move to W_0, its W_3 occurrence only to W_2).

**Re-cut Lemma.** The reduced boundary model R(M) of PROOF_threshold.md (four pieces of length K, budget 2, M columns, no bound
on the number of coordinates per type; program: `redrev 0 2 0000 M M`, compiled from redrev.c)
is the set of all assignments of typed coordinates to the cells (j, e), j = 0..4, e < M, that satisfy the distance
requirements between the points P_j(e), e <= M, the order rule (a coordinate in pieces j-1 and j occurs in piece j-1
at a column <= its column in piece j) and the budget. For a path as above, M <= K-1 and any 0 <= s0 <= E-M, the columns
s0..s0+M-1, with every coordinate typed by its STATE at shift s0, form a solution of R(M): the requirements are a
subset of the path's, and the Plotkin count applies verbatim to the five points P_j(s0).

## 2. Interior rigidity (finite computation)

`COLT=3,4 ./redrev 0 2 0000 8 8` (redrev.c, 24 s) enumerates all 4,739,254 solutions of R(8)
(51,012,176 nodes; an earlier enumerator with another column order needed 860,999,335 nodes for the same solutions; a 'solution' is a pair (budget configuration, assignment): an assignment without a singleton coordinate
that is valid in several configurations is counted once for each; harmless for kinds and transitions) and prints, for columns 3 and 4, the multiset of moves 'state before - pieces - state after' of the
coordinates that have a letter in the column (colt8.out; `python3 coltan.py colt8.out` lists the kinds and transitions,
numbered by frequency, so its names differ from the ones below). Result: only seven column kinds occur,

    K1: 03-2>14  04-3>12  12-4>03  14-0>23  23-1>04          (five coordinates, one letter each)
    K5: 34-2>01  04-3>12  12-4>03  14-0>23  23-1>04
    K2: 03-234>13  13-01>03                                  (two coordinates)
    K3: 13-012>14  14-34>13
    K4: 13-01>03  14-34>13  34-2>01
    K6: 01-4>23  12-0>34  {2}-1>12  23-3>{2}  34-2>01        ({2} = singleton state)
    K7: 02-0>{2}  {2}-4>24  24-123>02

and the pairs (column 3, column 4) are exactly K1>K2, K1>K3, K1>K4, K2>K1, K3>K1, K3>K5, K4>K1, K5>K2, K6>K7, K7>K6.

By the Re-cut Lemma (s0 = s-3, M = 8 <= K-1; needs E >= 8): in ANY path, every column s with 3 <= s <= E-4 is of one of the seven kinds (states
taken at the time of the column), and consecutive columns s, s+1 with 3 <= s <= E-5 follow the transition list.
Hence the deep columns 3..E-4 (m = E-6 of them) are either all of 'phase A' (K1..K5), alternating between {K1,K5}
and {K2,K3,K4}, or all of 'phase B', alternating K6, K7.

## 3. The repeat inequality

For s < t <= E let R(s,t) = number of coordinates that have a letter in piece 0 at a column in [s,t) AND a letter in
piece 1 at a column < t. Then R(s,t) <= ceil((t-s)/2).
Proof. The word between P_0(s) and P_1(t) has K + (t-s) <= 2K letters. A coordinate occurs in it at most twice, and twice
exactly if it is counted by R (two occurrences are >= K apart). So d(P_0(s), P_1(t)) = K + (t-s) - 2R, which must be
>= K-1. QED

## 4. Counting

Phase A. Every column of kind K2, K3, K4 contains a coordinate with letters in pieces 0 and 1 of that same column
(13-01>03 or 13-012>14): a 'lag-0 repeat'. There are >= floor(m/2) such columns among the deep ones, so by Section 3
with [s,t) = the deep columns, at most ceil(m/2) - floor(m/2) <= 1 other coordinate has letters in piece 0 and in piece 1
both in deep columns (*).
Every column of kind K1, K5 (>= floor(m/2) deep columns) contains the move 23-1>04: a coordinate in state 23 has its
piece-1 letter there. These are distinct coordinates. Let x be one of them.
 (a) x has no earlier letter: then x is of type 23.
 (b) x has a letter in columns 0, 1, 2: at most 15 coordinates.
 (c) otherwise x has earlier letters, all in deep columns; its last move before the departure ends in state 23, and
     the only such move in K1..K5 is 14-0>23. So x has a piece-0 letter and a piece-1 letter in two different deep
     columns: by (*) at most one such x.
So c >= floor(m/2) - 16, i.e. E <= 2c + 39.

Phase B. Every K6 column contains 23-3>{2}: a coordinate in state 23 has its piece-3 letter there; distinct
coordinates. Case (c) cannot occur: the only move into state 23 in K6, K7 is 01-4>23, made by a coordinate whose W_3
occurrence is a tail letter, and such a coordinate has no piece-3 letter in a later column. So c >= floor(m/2) - 15.

Finally c <= n+1: the ten type counts are the unique solution of the ten distance equations (counts_second.py); type 23 has n
or n+1 coordinates in each budget configuration (the six non-adjacent excess pairs and the five singletons;
counts_second.py also prints the four adjacent pairs, which cannot occur).   QED

## 5. Remarks

* What is used from the model: only Section 2. Everything else is two lines of counting.
* Why two columns per 23: K1/K5 and K6 are the columns that are NOT made of 'K-periodic' moves (K2, K3 are
  contractions of the 5-cycle C3 = 13>24>03>14>02>13 of single-letter moves, along which a coordinate recurs with period K); they alternate with them (K7 is the C3 moves 24>03>14>02 by one coordinate plus a singleton detour 02-0>{2}-4>24), and each contains exactly one
  departure from the 2K-periodic state 23 (and, symmetrically, one from 12).
* Consistent with exhaustive values of the model in which only the number of type-23 coordinates is bounded (by c), all
  other types unlimited (redrev.c, env CAPS=12:c): c = 0, 1, 2, 3, 4 give E_max = 5, 7, 9, 11, 13.
* Deeper confirmation (not needed for the proof): R(9) has 75,305,973 solutions (1,674,254,652 nodes); columns 3, 4, 5 show the
  same seven kinds and the same ten transitions (data file not included). R(10): 17,675,726 solutions,
  columns 3..6: again the same seven kinds and ten transitions (redrev.c). All 1800 solutions
  of the model with the exact type counts of n = 3 and E = 10 have only K1, K2, K3 in columns 3..6.
* In case (b) only coordinates of types 14 and 01 can ever be in state 23 with an unused piece-1 letter, so 15 can probably be replaced
  by 6 (three piece-0 letters, three tail letters): E <= 2c + 21 (unproved; not pursued); the sharp statement needs the boundary columns.
* Empirically case (c) never occurs: in all 75,305,973 solutions of R(9) no coordinate arrives in state 23 by a move in a deep
  column and leaves it in a later deep column (a variant of redrev.c, not included); the same holds for odd K at M = 9..12.
* Odd K (K = 6n+1, budget 6): the census is rigid as well (ten kinds, thirteen transitions, a departure from state 23 in every
  second deep column; data not included), but there the 0->1 repeats have lag 1 and are not forced (the 24-12>14
  move can be made by a new 24-type), so Section 4 does not go through as it stands.
* INDEPENDENT CHECK (2026-11-12, by a separate AI run with its own two enumerators, written from this text only; programs not
  included): solution counts R(1..9) = 1170, 5148, 273013, 138544, 1713500, 971378, 13467942, 4739254, 75305973 reproduced by
  both enumerators; all 107 census lines of R(8) identical; R(9) column pairs (3,4), (4,5): same kinds and transitions;
  Sections 1, 3, 4 checked line by line, no error; gaps it found are fixed in this text (the hypotheses E <= K-1, K >= 10, the
  truncation step of the Corollary, the meaning of 'solution', the K7 remark). Real paths (pfam3 n = 1..5, SAT words, their
  reversals): deep columns K1/K2/K3 only, repeat inequality never violated, E - 2c <= 4; they do not exercise K4, K5, phase B or
  cases (b), (c). Enumerating the pieces of a column in the order tail, 3, 2, 1, 0 is ~15x cheaper (this is redrev.c).
  A second audit of the statements found no mathematical error.
* OPEN: odd K (K = 6n+1), the sharp constant (39 -> 4, needs the boundary columns), a machine-checkable certificate.
