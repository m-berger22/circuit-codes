# Spread-k paths in the d-cube for d up to about 5k/3: the exact maximum length

Added 2026-11-12. Everything in this folder was produced by Claude (an AI model made by Anthropic) working
autonomously. **No human has read the proofs.** What stands in for a referee: the statements marked [Lean] are checked
by the Lean 4 kernel (project in `../lean/`, files `Ccformal/Path*.lean`; items 34-35 of `../lean/FORMAL.md`), the families
are checked from the definition by `pfam.py`, `pfam2.py`, `pfam3.py`, `pfam4.py`, and each hand proof comes with brute-force tests of every step (the test scripts are not included).
Corrections are welcome.

## Setting
A spread-k path with L edges in the d-cube is a path v_0, ..., v_L such that d_H(v_i, v_j) < k implies
|i - j| = d_H(v_i, v_j) (the open version of a spread-k circuit code; Douglas' definition). P(d,k) is the
maximum L. (The 'k-snake' of the computational literature asks only that vertices at path distance >= k are at Hamming
distance >= k. A k-snake with L >= k edges is a spread-k path in the sense above, so the two maxima agree whenever
d >= k, i.e. everywhere below.)
Write K = k+1 and l = 2d-3k-1, the same 'lines' as in the circuit-code part of this repository.

## Results

| range of d | P(d,k) | upper bound | lower bound |
|---|---|---|---|
| k <= d <= (3k+1)/2 | 2d - k | [Lean] `path_bound_low` | [Lean] `trivial_path` (the word 0 1 .. d-1 0 1 .. d-k-1) |
| d = 3k/2 + 1, k even | 2k + 3 | [Lean] `path_bound_douglas_even` | [Lean] `maxPath_douglas_even` |
| (3k+3)/2 <= d <= (5k+4)/3, k odd | 6(d-k) - 5 | [Lean] `path_bound_odd` | [Lean] `famEven_isPathWord`, `maxPath_even_l` |
| 3k/2 + 2 <= d <= (5k+3)/3, k even | 6(d-k) - 5 | [Lean] `path_bound_even` | [Lean] `famOdd_isPathWord`, `maxPath_odd_l` |

In terms of l: P(d,k) = 3k + 3l - 2 for every l >= 2 and k >= 3l-5 (k odd, l even) resp. k >= 3l-3 (k even, l odd).

Rows 1-2 are the values stated by R. J. Douglas (J. Combin. Theory 6 (1969) 323-339, 'Further remarks' (8)) without
proof; `maxPath_low` and `maxPath_douglas_even` are complete formal proofs. Rows 3-4 continue his formula to the
next range of dimensions.

**Why 6(d-k)-5** (`PROOF_upper.md`). Cut a path word into four consecutive pieces of length <= K. Inside a piece every
coordinate occurs at most once, so each coordinate separates the five piece boundaries P_0..P_4 into at most 2|3, and
the ten pairwise distances sum to at most 6d (Plotkin's count). The four adjacent pairs have distance = piece length;
the six others are >= k, and >= K when the parity is right. For k odd this gives the bound at once; for k even one
more unit is needed and comes from a twelve-window inequality found by linear programming.
The same count with 2s pieces gives, for k odd and 2s^2 K - 2 <= s(s+1)d <= s(2s+1)K - 2, the bound
P <= s(s+1)d - s(2s-1)K + 1 (not formalized for s >= 3): s = 1 is Douglas' 2d-k, s = 2 is 6(d-k)-5. For s = 3 it is
not attained at any computed point beyond the line l = 2, e.g. P(17,9) = 46 (SAT) against the s = 3 bound 55 (the
s = 2 formula, not valid there, would give 43).

**The family** (`pfam.py`, which also re-checks it from the definition: `python3 pfam.py 14 60`). Let m = l-2,
h = floor(m/2), and
- A = 0 1 .. k,
- B = A with every odd coordinate 2i+1 replaced by a new coordinate n_i,
- C = 0 .. m-1, then (N_i, n_{h+i}, m+2i, m+2i+1) for i < h, then the rest of A,
- D = (2i, n_{h+i}, 2i+1, n_i) for i < h, then 2h.

For m even the word is A B C D; for m odd it is z A z B C z D with one more coordinate z. It has 3K+3m+1 = 3k+3l-2
letters over (3K+m)/2 = d coordinates and is a spread-k path word for all k >= 2m-1 (m even) / 2m-2 (m odd).
It was found by asking a SAT solver for the lexicographically first maximal path at two sizes.
Proofs: `PROOF_family_even.md`, `PROOF_family_odd.md`. Idea (Walk Lemma): fix the start s and follow e -> d_H(v_s, v_e);
the word is a path word iff this walk is at height >= K before every down-step, and for the family the down-steps and
the heights at the boundaries of pairs/quadruples of letters are explicit.

## The edge of the range (added later on 2026-11-12)

The table above stops at k = 3l-5 (l even) resp. k = 3l-3 (l odd). What happens at the next values of k is now known:

| point | P(d,k) | upper bound | lower bound |
|---|---|---|---|
| l odd, k = 3l-5 and k = 3l-7 (k even) | 3k + 3l - 2 (the formula still holds) | [Lean] `path_threshold_B`, `path_threshold_C` | [Lean] `famOdd_isPathWord`; together `maxPath_odd_l_sharp` |
| l even, k = 3l-7 (K = 6t, d = 10t, t >= 2) | 3k + 3l - 1 = 4K + 2 (formula + 1) | [Lean] `path_threshold_A` | `pfam2.py` (t >= 3; hand proof `PROOF_family_excess.md`; [Lean] `famX_isPathWord`, together with `path_threshold_A`: `maxPath_excess`, P(10t, 6t-1) = 24t+2 for all t >= 3; checked from the definition for t <= 30); t = 2: SAT word `word_20_11_50.txt` |
| l even, k = 3l-9 (K = 6n+4, d = 10n+7, n >= 1) | 13K/3 + O(1); >= 3k + 4l - 5 = (13K+8)/3, with equality for n = 1..6 | (13K+119)/3 for all n (computer-assisted, `PROOF_second_upper.md`; new for K >= 64); 5K - 1 for K >= 16 (`PROOF_threshold.md` Theorem D) | `pfam3.py` (checked from the definition for n <= 14; proof `PROOF_family_second.md`, a case analysis whose 343 cases were generated and certified by program) |
| l odd, k = 3l-9 (K = 6n+1, d = 10n+2, n >= 1) | >= (13K+8)/3 = 4K + 2n + 3, and <= 4K + 11n/5 + 41.7 for n >= 11; equality with (13K+8)/3 for n = 1, 2 | 4K + 11n/5 + 41.7 for n >= 11; 4K + 2n + 9 for paths whose interior is of the type of the family (computer-assisted, `PROOF_second_upper_odd.md`) | n >= 2: `pfam4.py` (checked from the definition for n <= 14; proof `PROOF_family_second_odd.md`, 441 cases generated and certified by program); n = 1: SAT |

So for odd l the formula 3k+3l-2 holds for all even k >= 3l-7 [Lean], and at k = 3l-9 it fails for every odd l >= 5 (l >= 7: family
`pfam4.py`, proof `PROOF_family_second_odd.md`, not formalized, checked from the definition for l <= 31; l = 5: P(12,6) = 33 > 31). For even l >= 6 it holds exactly for k >= 3l-5 (at l = 4
it still holds at k = 5: P(10,5) = 25); one step further the maximum is the formula plus one. At k = 3l-9, for both parities of l, the maximum
is at least the formula plus l-3, i.e. (13K+8)/3, and this is the exact value in the eight cases that could be decided:
P(12,6) = 33 and P(17,9) = 46 by plain SAT; P(22,12) = 59 and P(27,15) = 72 by SAT restricted by the type reduction of
`PROOF_threshold.md` (one more edge is unsatisfiable in every type configuration of the first window; program not included);
P(37,21) = 98 by the reduced model with a bound on the number of coordinates per type (`redcap 0 2 0000 11 11 1 4`, compiled from `redcap.c`; about an
hour); P(47,27) = 124, P(57,33) = 150 and P(67,39) = 176 by the same model with the exact number of coordinates of each type prescribed per
budget configuration (`NTAB=n redrev 0 2 0000 E E` with E = 2n+5 for n = 4, 5, 6, compiled from `redrev.c`; 0 solutions; for n = 6:
4,705,984,421 nodes, 90 minutes). All of these upper bounds are computer-assisted, none is formalized. Conjecture: P((5K+1)/3, K-1) = (13K+8)/3 for
every K = 1 (mod 3), K >= 7.

**Method** (`PROOF_threshold.md`). At these points the Plotkin count on the five cut vertices v_0, v_K, .., v_4K is tight or
has slack 1 or 2. Tightness forces a rigid structure: every coordinate splits the five cut vertices 2|3, so it has one of
ten 'types' (for slack: a bounded number of exceptions). The Hamming distance between two vertices just after two cuts
is then K plus a signed count over the few letters that follow the cuts, and the path condition for these vertices
becomes a finite problem about the types and coincidences of the first M letters of each piece (M = 4, 2, 2 in the three
theorems) in which K does not occur. An exhaustive search (1325, 114, 886 nodes) finds no solution, which proves the
bounds for all sizes at once. In Lean: `PathReduced.lean` (the finite model and a verified search), `PathReducedProj.lean`
(every path word projects to a solution), `PathReducedA/B/C.lean` (the three searches, evaluated by the kernel).
A second, independently written implementation of the search (by a separate AI referee run; not included) agrees on all counts.
The same reduction with five pieces gives Theorem D (computer-assisted only, not formalized).

**The new families** are given by columns in the headers of `pfam2.py` and `pfam3.py` (for `pfam4.py`: in the code of
`pfam4_raw.py` and in section 1 of its proof); all were read off solver output
printed 'in columns' (the letters at the same offset of the four pieces side by side), where coordinates recurring with
period K become visible.

**The growth rate at the second step** (`PROOF_second_upper.md`). For K = 4 (mod 6) the maximum at d = (5K+1)/3 is
13K/3 + O(1): P <= (13K+119)/3 for every K. Proof: re-cutting the path at every shift s turns each stretch of 8 consecutive
columns (the letters at the same offset of the four pieces and the tail) into a solution of the finite reduced model R(8);
an exhaustive census of all 4,739,254 solutions of R(8) (`COLT=3,4 redrev 0 2 0000 8 8`, 24 s; data `colt8.out`, analysis
`coltan.py`) shows that deep columns come in only seven kinds with ten possible transitions ('interior rigidity'), and in
every second deep column a coordinate of type 23 is used up (there are at most n+1 of them); a one-line distance
inequality shows that, up to O(1), no other coordinate can take its place. Exact value: open. Odd K (`PROOF_second_upper_odd.md`): the census of the odd model is just as rigid but has two
'phases'; in the phase of the known family a three-line argument gives E <= 2n+9; in general an LP over the census windows,
with an exactly verified dual certificate (`seglp_odd.py`), gives E <= 11n/5 + 41.7. The missing step is to bound a kind of
long-range link that no finite census window can see.

**Beyond.** At d = (5K+1)/3 the maximum is no longer 4K + O(1): it is 4K + K/3 + O(1) (proved for K = 4 mod 6, at least
4K + (K+8)/3 for all K = 1 mod 3 by `pfam3.py` / `pfam4.py`; at most 4K + 11K/30 + O(1) for odd K). No formula is proved
for larger d.

## Prior work
Douglas (1969) as above. Byrnes' three papers on circuit codes (arXiv:1809.08428, 2008.04839, 2101.00642) and
Hood, Recoskie, Sawada, Wong (J. Comb. Optim. 30 (2015)) contain no formula or bound for paths in this range.
We could NOT access R. C. Singleton (IEEE Trans. Electron. Comput. EC-15 (1966) 596-602) and A. D. Wyner, 'Note on
circuits and chains of spread k in the n-cube' (IEEE Trans. Comput. C-20 (1971) 474); the results of rows 3-4 may
overlap with the latter.

## Contents
- `PROOF_upper.md`: the upper bound (Four-Piece Lemma, both parities), as formalized (working notes; the scripts and
  data files it names are not included).
- `PROOF_family_even.md`, `PROOF_family_odd.md`: the family is a path word (working notes: complete, tested step by
  step, not polished; they refer to test scripts that are not included).
- `pfam.py`: the family and a checker from the definition (pure Python).
- `PROOF_threshold.md`: the threshold theorems A, B, C (and D, E with five pieces), the reduction and the list of searches;
  `reduced.py` (the search, Python), `red.c` (the same for any number of pieces, C).
- `pfam2.py`, `PROOF_family_excess.md`, `word_20_11_50.txt`: the family of length 4K+2, its proof, and the SAT word for t = 2;
  `pfam3.py` (+ `pfam3_raw.py`, `chk.py`), `PROOF_family_second.md`: the family of length (13K+8)/3 and its proof. Both proofs are
  working notes: complete, tested step by step, not polished; the test scripts and data files they name are not included, and
  in the second one the 343 cases of the main table were generated and certified by a program that is not included.
- `pfam4.py` (+ `pfam4_raw.py`), `PROOF_family_second_odd.md`: the odd-K family of length (13K+8)/3 and its proof (same status as
  `PROOF_family_second.md`; 441 generated cases). `redcap.c`: `red.c` with a bound on the number of coordinates per type.
- `PROOF_second_upper.md`: the upper bound 13K/3 + O(1) at the second step (interior rigidity); `redrev.c` (the reduced model
  with a faster column order, per-type caps CAPS, per-configuration exact counts NTAB, census output COLT), `colt8.out` (the
  census), `coltan.py` (its analysis), `counts_second.py` (the type counts per budget configuration).
- `PROOF_second_upper_odd.md`: the odd case; `seglp_odd.py` (segment LP + exact dual check), `colt16_odd.out` (odd census,
  M = 16), `redrev_bigkey.c` (redrev.c with larger census buffers), `counts_odd.py` (odd type counts).
- `values.txt`: the exact values of P(d,k) computed by SAT / exhaustive search that are quoted above.
- Lean: `../lean/Ccformal/Path.lean` (upper bound), `PathDouglas.lean`, `PathDouglasWord.lean` (rows 1-2),
  `PathWalk.lean` (Walk Lemma), `PathFamEven*.lean` (the family, even l), `PathFamOdd*.lean` (the family, odd l).
  `PathReduced*.lean`, `PathThresholdMax.lean` (threshold theorems; generator and python twin of the search: `../lean/scripts/pathred/`),
  `PathFamX*.lean` (the family pfam2: 583 small generated modules, one lemma each; the generator is not included) and
  `PathExcessMax.lean` (`maxPath_excess`).
- Labels such as S177 .. S180 in the files are internal session numbers.
