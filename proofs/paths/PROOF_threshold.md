# Spread-k paths at the ends of the line range: three threshold theorems by a K-independent finite reduction (S179, 2026-11-12)

Status: Theorems A, B, C are MACHINE-CHECKED in Lean 4 (ccformal PathReducedThms.lean: `path_threshold_A`, `path_threshold_B`,
`path_threshold_C`; the finite search is a verified function evaluated by the Lean kernel; with the odd-l family this gives
`maxPath_odd_l_sharp`, PathThresholdMax.lean). Theorems D, E (section 7) are computer-assisted only. This file is the hand
reduction the formalization follows, plus the record of the searches and of two referee rounds by separate AI runs.
Of the programs named below only reduced.py and red.c are included in the repository.

Notation and the facts (F1), (F2) as in PROOF_upper.md: spread-k path v_0..v_L in Q_d, transition word T[0..L), K = k+1, l = 2d-3k-1, m = l-2,
line value 3k+3l-2 = 6(d-k)-5.  P(d,k) = max L.

## 1. Statements

THEOREM A (even l, one step below the proved range).  Let K = 0 (mod 6), K >= 6, k = K-1, d = 5K/3  [l even, k = 3l-7].
   Then P(d,k) <= 4K+2 = 3k+3l-1  (line + 1).
THEOREM B (odd l).  Let K = 2 (mod 3), K odd, K >= 5, k = K-1, d = (5K-1)/3  [l odd, k = 3l-5].
   Then P(d,k) <= 4K-1 = 3k+3l-2  (the line).
THEOREM C (odd l).  Let K = 0 (mod 3), K odd, K >= 3, k = K-1, d = 5K/3  [l odd, k = 3l-7].
   Then P(d,k) <= 4K+1 = 3k+3l-2  (the line).

All three proofs are COMPUTER-ASSISTED: a hand reduction (section 2) to a finite K-independent problem, solved exhaustively by
program (section 3; three independently written implementations of the search agree: reduced.py, a CNF version, and the
referee's own program, sections 4 and 6; the Lean formalization contains a fourth, verified one).
With the family of PROOF_family_odd.md (valid for k >= 2l-6) B and C give P(d,k) = 3k+3l-2 for odd l >= 3 and all even k >= 3l-7
(the Four-Piece theorem needed k >= 3l-3).  The window LP is FEASIBLE at these points: these are integrality statements.
Data: A is attained for every K >= 12: K = 12 by a SAT word (P(20,11) = 50), K >= 18 by the family pfam2.py (proof:
PROOF_family_excess.md; P(30,17) = 74, P(40,23) = 98, ...); it is not attained at K = 6 (P(10,5) = 25);
the line fails at the next step in all known cases: odd l, k = 3l-9: P(12,6) = 33 > 31, P(22,12) >= 59 > 55 (SAT; the word is not included).

## 2. The reduction (valid for any d, k)

Fix a path word and five cut positions p_0 < p_1 < .. < p_4 with piece lengths G_j = p_{j+1} - p_j in {K, K-1}; u_j = v_{p_j}.
Piece j = [p_j, p_{j+1}) (j = 0..3); the 'tail' = positions p_4, p_4+1, .. (E of them).

(R1) TYPES. For a coordinate c let S(c) = the set of j with (u_j)_c = 1, replaced by its complement if it has > 2 elements
     ('minority set', |S| <= 2: 10 pair types, 5 singleton types, 1 empty type). c occurs in piece j an odd number of times iff
     exactly one of j, j+1 is in S(c); a piece has length <= K, so by (F2) it contains each coordinate at most once. Hence
     c occurs in piece j (exactly once) iff |S(c) n {j,j+1}| = 1  ('type in piece j').
(R2) PLOTKIN IDENTITY.  sum_{i<j} d(u_i,u_j) = 6d - 2 y1 - 6 y0, y1 / y0 = number of coordinates of singleton / empty type
     (a coordinate separates 6, 4, 0 of the 10 pairs).
(R3) BASE DISTANCES.  d(u_j,u_{j+1}) = G_j (F2).  For j2 >= j+2: D = p_{j2}-p_j >= 2K-2 >= k, so by (F1)
     d(u_j,u_{j2}) = req(D) + 2 x_{j,j2}, x >= 0 an integer, req(D) = k + [(D-k) odd].
     With (R2):  sum_{non-adjacent} x_{ij} + y1 + 3 y0 = B := (6d - sum_j G_j - sum_{non-adjacent} req)/2.       (budget)
     If B < 0 no such word exists (that is the Four-Piece Lemma).
(R4) BOUNDARY VERTICES.  For 0 <= e the vertex v_{p_j+e} = u_j xor (the set A(j,e) of the first e letters of piece j; for j = 4:
     of the tail). For j < j2:
         d(v_{p_j+e}, v_{p_{j2}+e2}) = d(u_j,u_{j2}) + sum over c in A(j,e) xor A(j2,e2) of (-1 if S(c) separates j, j2; else +1).
(R5) PATH CONDITION for such a pair: D' = p_{j2}+e2-p_j-e. If D' >= k: distance >= req(D').  (If D' < k nothing is used.)
     For j2 >= j+2 always D' >= 2(K-1) - M >= k because M <= K-1; for j2 = j+1, D' = G_j+e2-e and the pair is used iff D' >= k.
(R6) BACKWARD RULE.  Let c = T[p_j+e] (j >= 1; j = 4: a tail letter). If the type of c is in piece j-1, its occurrence q there
     satisfies p_j+e-q >= K (F2), i.e. q is at offset <= e + G_{j-1} - K <= e of piece j-1.

Everything in (R3)-(R6), measured relative to K, depends only on: K mod 2, C = 6d-10K, the vector (G_j - K), and the letters at
offsets < M of the four pieces and the E tail letters (their types and which of them are the same coordinate).

REDUCED MODEL  Mod(PAR, C, G, M, E)  (E <= M <= K-1): choose x_{ij} >= 0 (non-adjacent pairs), a type for every modelled letter and
an equivalence 'same coordinate', such that
  - a letter of piece j has a type in piece j; letters of one piece (and of the tail) are distinct coordinates;
  - (R6): a letter at (j,e) whose type is in piece j-1 equals a modelled letter (j-1,e'') with e'' <= e + G_{j-1} - K;
  - budget: sum x + (number of modelled coordinates of singleton type) + 3 (number of empty type) <= B;
  - (R5) with (R3), (R4) for all pairs of vertices (j,e), (j2,e2), j < j2, e <= M (tail: e <= E), except j2 = j+1 with D' < k.
Every path word of length sum G_j + E in Q_d (K > M, i.e. E <= M <= K-1) gives a solution. So:  Mod has no solution  =>  P(d,k) < sum G_j + E.

## 3. The three finite checks (reduced.py PAR C G M E: exhaustive DFS, letters in the order offset-major; no solver)

  A:  reduced.py 0  0 0000 4 3   B = 0 (window 0 is a perfect simplex: all ten distances = K, pair types only), 19 letters:
                                 1325 nodes, 0 solutions.          (M = 3: exactly 1 solution; E = 2: 63 solutions at M = 3.)
  B:  reduced.py 1 -2 000m 2 1   pieces K, K, K, K-1 and one more letter (length 4K), B = 1, 9 letters: 114 nodes, 0 solutions.
  C:  reduced.py 1  0 0000 2 2   pieces K, K, K, K and two more letters (length 4K+2), B = 2, 10 letters: 886 nodes, 0 solutions.
(Length-(4K-1) resp. (4K+1), (4K+2) versions have solutions, as they must.)
C-values: A: 6d = 10K.  B: 6d = 10K-2.  C: 6d = 10K.

## 4. Tests

 * reduced_validate.py: (R1)-(R6) as IDENTITIES on real words: all SAT words in words/ (d = 13..30), 200 random cuts each,
   912,256 checks, 0 failures.
 * reduced_sat.py (same model for case A as a CNF, CaDiCaL): M = 4, E = 3 UNSAT; and the real words at K = 12, 18, 24 projected
   into the model at E = 2 are SAT (soundness).
 * simp2.py t E (full SAT with the simplex typing imposed, 10-20x faster than the plain encoding): E = 3 UNSAT at t = 2, 3;
   E = 2 SAT at t = 2, 3, 4.  Plain SAT (S178): (20,11,51), (30,17,75) UNSAT; (18,10,44), (28,16,68), (15,8,38), (25,14,62) UNSAT.

## 5. What is NOT proved

 * (Lower bound for A: now given for all K >= 18 by pfam2.py with the proof PROOF_family_excess.md; K = 12 by SAT.)
 * Beyond these points there is no K-independent bound of this kind: for even l, k = 3l-9 (C = 2, B = 1) the reduced model
   has solutions for every tail length tried (E <= 12), and the data suggest that the excess over 4K grows with K.

## 6. Referee (S179, fresh agent, own implementation from this text only: referee/)

Verdict A PASS, B PASS, C PASS (its text corrections -- K ranges, 'computer-assisted', the D' >= k remark -- are incorporated above). Its own DFS (any letter
order; identical counts for K = 3..101) gives 0 solutions for A, B, C and 464 / 508 / 117 solutions for the one-shorter versions;
node counts 1325 / 114 / 886 reproduced; solution counts agree with reduced.py on 12 cases. Ablation: B and C stay at 0 solutions
even WITHOUT the backward rule (R6); A stays at 0 with (R6) weakened by one offset; the budget is essential for B and C.
Projection of all 21 SAT words (4481 cuts): 0 violations. Direct SAT: (8,4,20), (18,10,44), (15,8,38), (5,2,14), (20,11,51) UNSAT,
one shorter SAT. Remark: at K = 6 model A with E = 2 has solutions although P(10,5) = 25: the model is a strict relaxation.

## 7. Five pieces (six cut points): Theorems D and E  (S179; red.c = the same search for any number of pieces)

The reduction of section 2 works verbatim for n pieces of length K or K-1 and n+1 cut points u_0..u_n:
 * types = minority sets S of {0..n} (|S| <= (n+1)/2; for n+1 even and |S| = (n+1)/2 the set containing 0);
 * Plotkin identity: sum_{i<j} d(u_i,u_j) = maxsep * d - sum_c cost(c), maxsep = floor((n+1)^2/4), cost(c) = maxsep - |S|(n+1-|S|)
   (n = 5: maxsep = 9, cost = 0, 1, 4, 9 for splits 3|3, 2|4, 1|5, 0|6;  n = 4: 6 and 0, 2, 6);
 * budget: 2 sum_{non-adjacent} x_ij + sum over modelled coordinates of cost <= B := maxsep*d - sum_j G_j - sum_{non-adjacent} req;
 * (R4)-(R6) unchanged.
`red PAR CC G M E` with CC = maxsep*d - (number of pairs)*K  (n = 4: CC = 6d-10K; n = 5: CC = 9d-15K).

THEOREM D.  K even, K = 4 (mod 6), K >= 16, d = (5K+1)/3  [even l = (K+8)/3, k = 3l-9]:  P(d,k) <= 5K-1.   (computer-assisted)
   red 0 3 00000 15 0 : five pieces of length K, 75 boundary letters, B = 3: 9,511,796 nodes, 0 solutions (M <= 14: solutions).
   Also 5K+1 is impossible for K >= 7 (red 0 3 00000 6 1: 148,669 nodes); the only new case is K = 10: P(17,9) <= 50 (true value 46).
   (Generic six-piece Plotkin bound, i.e. the 2s-piece bound of the README paragraph 'Why 6(d-k)-5' with s = 3: P <= 12d-15K+1 = 5K+5 here.
   Small K: P(7,3) = 21 = 5K+1, K = 4: the model is feasible there for M <= 3, as it must be.)
THEOREM E.  K even, K = 2 (mod 6), K >= 14, d = (5K+2)/3  [even l = (K+10)/3, k = 3l-11]:  P(d,k) <= 5K+3.   (computer-assisted)
   red 0 6 00000 8 4 : B = 6, 286 x-configurations: 79,313,998 nodes, 0 solutions. (K = 8 is outside the range: there M <= 7 and
   the model has solutions; P(14,7) = 43 = 5K+3 is a coincidence of numbers. Inside the range tightness is unknown.)
Data: P(17,9) = 46 (K = 10, bound of D not applicable), P(27,15) = 72 (K = 16, bound of D: 79), P(24,13) >= 69 (K = 14, bound of E: 73).
Units: B in this section is TWICE the B of section 2 (costs in Plotkin units; a distance excess x_ij costs 2).
Status: python (redgen3.py) and C (red.c) agree on all node counts up to 148,669. REFEREE round 2 (own C search redn.c with 128-bit
coordinate sets + python checker, written before reading red.c; referee/): D PASS, E PASS (its text corrections are incorporated):
all claimed counts reproduced (D: 0 solutions at M = 15 in two letter orders, solutions at M = 14, 274,543 at M = 5; E: 0 at M = 8,
solutions at M = 7); identities checked on 12,573 / 4,195 / 3,601 real cuts with 4 / 5 / 6 pieces; (7,3) consistent. Caveat: no
independent full-problem SAT confirmation of D, E is feasible at their first sizes ((27,15,80), (24,13,74)); D's bound 79 is far
above the exact value P(27,15) = 72. The runs listed under E', G below were NOT part of the referee's round.
More runs of the five-piece model (NOT refereed; log not included):
   E':  K even, K >= 15, d = (5K+2)/3:  P <= 5K+2   (red 0 6 00000 14 3: 96,393,534 nodes, 0 solutions; 5K+2 has solutions at M = 14).
   G:   K odd,  K >= 9,  d = (5K+1)/3  [odd l, k = 3l-9]:  P <= 5K   (red 1 3 00000 8 1: 146,871 nodes, 0 solutions; 5K has
        solutions for M <= 12).  Data: P(12,6) = 33 (K = 7), P(22,12) >= 59 (K = 13, bound 65).
   Four pieces, odd K, C = 2: solutions for every tail length E <= 12 (no bound of the form 4K+E), as for even K.
   Zero budget at the other Plotkin thresholds: d = 3K/2 (4 points): 3K+1 feasible, 3K+2 impossible (24 nodes) [= the known line
   start]; d = 7K/4 (7 points, K = 0 mod 4): 6K+1 feasible (M <= 10), 6K+2 impossible (red 0 0 000000 4 2: 84,935 nodes), seven
   K-pieces impossible (45,669 nodes): P(7K/4, K-1) <= 6K+1, which equals the generic six-piece Plotkin bound 12d-15K+1 there.
EXACT VALUE by typed SAT: P(27,15) = 72 = 4K+8 (lazy2.py: near-simplex type configurations of window 0, exhaustive over the 11
configurations with B = 1; length 73: all 11 UNSAT, 62-212 s each; length 72: SAT; pfam3.py n = 2 is such a word). K = 10: P(17,9) = 46
= 4K+6 reproduced in 30 s. K = 22: P(37,21) >= 98 (pfam3.py, n = 3).
