import Ccformal

/-!
# Headline theorems: statements and axioms in one place
Run: `lake env lean Headlines.lean`   (prints every statement; ~30 s once the project is built).
-/

open Coil

#check @coil_length_bound      -- A  Main Theorem: N ≤ 4k+2l beyond ~l²/2
#check @byrnes_word            -- B  Byrnes' sequence: a symmetric code with bit run k+l of length 4k+2l, all k ≥ l-1
#check @K_beyond               -- B  K(n,k) = 4k+2l in the region of A
#check @conj42_region          -- B  S = K = 4k+2l there (Conjecture 4.2 holds)
#check @kmax_exact_l1          -- C  k_max(l) = (l²-1)/2 for l = 4c+1 ≥ 9
#check @kmax_upper_l0          -- C  upper bounds of the k_max table
#check @kmax_upper_l3
#check @kmax_upper_l2
#check @line_l1                -- C  the whole half-line for l = 4c+1
#check @exact_l7               -- C  line 7
#check @kmax_table             -- C  k_max(l) for l = 6..31
#check @symRun_gap             -- D  symmetric bit-run codes: N ≤ 4k+2l or N ≥ 6k+6
#check @symRun_le              -- D  S(n,k,k+l) ≤ 4k+2l (range of Lemma 2)
#check @symRun_le2             -- D  S(n,k,k+l) ≤ 4k+2l for k > 3l-7, k ≥ l+1, k ≥ 2l (even) / 2l-3 (odd); no Lemma 2
#check @conj42_fails           -- D  a code longer than 4k+2l on every line l ≥ 6
#check @conj42_false           -- D  S = 4k+2l < K at some k ≥ 2l+1, EVERY l ≥ 6
#check @conj42_gap_unbounded   -- D  K - S unbounded
#check @K_family10             -- E  K = 4k+2l+4i+2
#check @K_family6              -- E  K = 4k+2l+4m
#check @chord_inequality       -- F  Lemma 1
#check @no_long                -- F  Lemma 2
#check @no_long6               -- F  Lemma 3 (six blocks)
#check @length_le_seven
#check @blocks_bound           -- F  the block lemma, any number of blocks
#check @blocks_bound_odd
#check @length_le_blocks       -- F  N ≤ (2s+1)k + 2s - 1 if (s+1)(l+1) < (s-1)k + 4
#check @isCoilWord_of_gaps     -- F  the gap criterion
#check @contraction_fin        -- F  Deimer's contraction

#print axioms coil_length_bound
#print axioms conj42_region
#print axioms conj42_false
#print axioms conj42_gap_unbounded
#print axioms kmax_table
#print axioms K_family10
#print axioms K_family6
