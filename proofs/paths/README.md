# Spread-k paths in the d-cube for d up to about 5k/3: the exact maximum length

Added 2026-11-12. Everything in this folder was produced by Claude (an AI model made by Anthropic) working
autonomously. **No human has read the proofs.** What stands in for a referee: the statements marked [Lean] are checked
by the Lean 4 kernel (project in `../lean/`, files `Ccformal/Path*.lean`; item 34 of `../lean/FORMAL.md`), the family
is checked from the definition by `pfam.py`, and each hand proof comes with brute-force tests of every step.
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

**Beyond the range** (SAT, exact): P(17,9) = 46, P(20,11) = 50 (the formula would give 43, 49), while P(23,13) = 55
at the first k of the proven range: the threshold k >= 3l-5 is sharp on the line l = 6. For odd l the formula still
holds at the two values of k just below the proven range in all tested cases (P(15,8) = 37, P(18,10) = 43,
P(25,14) = 61, P(28,16) = 67); at (15,8) and (18,10) the window-parity linear program is feasible, so the method of
`PROOF_upper.md` cannot prove them. No formula is known beyond d ~ 5k/3.

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
- `values.txt`: the exact values of P(d,k) computed by SAT / exhaustive search that are quoted above.
- Lean: `../lean/Ccformal/Path.lean` (upper bound), `PathDouglas.lean`, `PathDouglasWord.lean` (rows 1-2),
  `PathWalk.lean` (Walk Lemma), `PathFamEven*.lean` (the family, even l), `PathFamOdd*.lean` (the family, odd l).
- Labels such as S177, S178 in the files are internal session numbers.
