# Circuit codes of dimension near 3k/2: bounds, counterexamples, machine-checked proofs

Added 2026-11-12. Everything in this folder was produced by Claude (an AI model made by Anthropic) working
autonomously. **No human has read the proofs.** What stands in for a referee: the main statements are checked by the
Lean 4 kernel (`lean/`), every code is checked from the definition by independent programs (`check.py`), and each
hand proof was re-derived by a separate AI instance that wrote its own test programs. Corrections are welcome.

## Setting
K(n,k) = maximum length of a spread-k circuit code in the n-cube. Write l = 2n-3k-1 (so n = (3k+l+1)/2; k and l have
opposite parity). K(n,k) = 2n for l <= 1 (Singleton 1966), and Douglas (1969) proved K = 4k+2l on the lines l = 2, 3 and,
for odd k >= 9, l = 4. K. M. Byrnes (arXiv:2008.04839) constructs codes
of length 4k+2l for k >= 2l+1 (k odd) / k >= 2l-2 (k even), proves they are optimal among symmetric codes with a bit
run of length k+l (S(n,k,k+l) = 4k+2l), and conjectures (Conjecture 4.2) S(n,k,k+l) = K(n,k) in that range.

## Results (item numbers [L n] refer to `lean/FORMAL.md`, the list of kernel-checked statements)
1. **Upper bound.** K(n,k) <= 4k+2l if l >= 2 and either k is even, 2k > l^2-1 and k > 3l-3, or k is odd and
   2k > (l-2)(l+1). [L 3]
   Proof: a double count over all windows of one length of the transition sequence (`PROOF.md`, 2 pages).
2. **The conjecture holds beyond ~l^2/2.** Byrnes' sequence is a code for all k >= l-1, so K = S = 4k+2l in the
   region of item 1. [L 20, 25]
3. **The conjecture fails on every line l >= 6**: for every l >= 6 there is k >= 2l+1 with S(n,k,k+l) = 4k+2l < K(n,k).
   First case on the line l = 6 (k = 2l+1): K(23,13) = 66, not 64 (`codes/sat_23_13_66.txt`). [L 4, 26, 27, 31, 33]
4. **Where it stops failing.** k_max(l) = the last k with K(n,k) > 4k+2l:
   (l^2-1)/2 for l = 1 mod 4, l >= 9 [L 19, 21]; (l^2-l-6)/2 for l = 0, 3 mod 4, l >= 7 (upper bound [L 16], l = 7: [L 28];
   codes: explicit families, hand proofs `PROOF3.md`, `PROOF4.md`, solver codes at l = 7, 11); for l = 2 mod 4 the upper bound (l^2-l-4)/2 [L 16] is attained for
   l = 6..38 by solver codes, no formula. The table for l = 6..31 is machine-checked completely. [L 30]
5. **Unbounded excess.** K(n,k) - (4k+2l) is unbounded: two-parameter families with exact values
   K = 4k+2l+4i+2 (odd lines) and K = 4k+2l+4m (even lines), e.g. K(33,19) = 96, K(99,59) = 288, K(208,130) = 576.
   [L 19, 24]; further families and the complete picture of when the counting bound is attained: `STATUS.md`.
6. 94 exact values K(n,k) for single pairs by a verified checker plus the counting bound. [L 5]

`STATUS.md` is the one-page summary of all theorems (numbering of the proof files) and of what is open.

## Prior work
Douglas (J. Combin. Theory 6 (1969) 323-339) proves K = 4k+2l on the lines l = 2 (all odd k), l = 3 (all even k) and
l = 4 (odd k >= 9); on those lines item 1 is his theorem (he covers more k on l = 3; item 1 adds only k = 7 on l = 4);
for l >= 5 we found no earlier bound of this kind (Singleton 1966 and Deimer 1984 could not be accessed).
The contraction used to pass between lines is Deimer's (1984, as quoted by Byrnes). The 'block lemma' of
`PROOF17.md` sec. 9 is Plotkin's bound applied to block boundaries. The symmetric-code bound S <= 4k+2l in Byrnes'
range is his theorem (re-proved here without the quoted Douglas bounds, and for all k >= l-1).

## Contents
- `note/note.pdf` (+ .tex): an 18-page write-up of the main line (draft).
- `PROOF.md` .. `PROOF17.md`: the hand proofs, in the order they were found (working notes: complete, but not polished;
  they refer to scripts, referee reports and audit files by their original names, most of which are not in this
  repository; `ccformal/` there means `lean/` here).
- `lean/`: the Lean 4 (v4.35.0) + Mathlib project. `FORMAL.md` lists every checked statement; `README.md` is the
  file table. Build with `lake build` (the 94 `Values/` files take hours; everything else a few minutes after
  Mathlib is fetched). `lake env lean Headlines.lean` prints the headline statements and their axioms
  (propext, Classical.choice, Quot.sound only; no `sorry`, no `native_decide`).
- `codes/`: 207 circuit codes (first line: `# n <n> k <k> N <N>` and provenance; then the vertices in hexadecimal).
  File name = `<origin>_<n>_<k>_<N>.txt` (a few family files are named by their parameters); origin `sat`, `skel`, `hsym`, `pump`, `con`, ... = found by a solver or derived
  from one, `zfam`, `efam`, `ofam`, `fam*`, `x*fam*`, `lad*` = written by a family generator.
- `generators/`: the explicit families as short Python programs (gap function on residues -> code -> check from the
  definition), e.g. `python3 odd10.py 13 1`, `python3 ex4fam.py 8`, `python3 evenfam.py 8`. The header of each file
  states the family. (`p8fam.py` and `ex4fam2.py` are imported for their residue tables; run on their own they call a
  solver script that is not included.)
- `paths/`: the OPEN version (spread-k paths): exact maximum length for dimension up to about 5k/3, with its own
  README (added later the same day).
- `check.py`: `python3 check.py` re-checks every file in `codes/` from the definition (pure Python, a few minutes)
  and prints l, 4k+2l and the excess for each.

## Not machine-checked
The lower bounds of the families other than 6 and 10 for general parameters (instances are checked), Theorems 30 and
33(b), and the solver-found codes' *optimality* outside the 94 listed values. See the end of `STATUS.md`.
