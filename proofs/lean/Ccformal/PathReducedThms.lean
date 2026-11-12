import Ccformal.PathReducedProj
import Ccformal.PathReducedA
import Ccformal.PathReducedB
import Ccformal.PathReducedC

/-!
# Three threshold theorems for spread-`k` paths      (S179)

`K = k+1`, `d = Fintype.card α`.  Written proof: `PROOF_threshold.md` (paths folder), Theorems A, B, C.

* `path_threshold_B`: `K` odd, `K ≥ 5`, `3d = 5K - 1`:  `L ≤ 4K - 1`.
* `path_threshold_C`: `K` odd, `K ≥ 3`, `3d = 5K`:      `L ≤ 4K + 1`.
* `path_threshold_A`: `K` even, `K ≥ 6`, `3d = 5K`:     `L ≤ 4K + 2`.

In `(d,k,l)` form (`l = 2d - 3k - 1`): `path_length_threshold_B/C/A`:
`L ≤ 3k + 3l - 2` for `k` even, `k = 3l - 5` or `k = 3l - 7`; `L ≤ 3k + 3l - 1` for `k` odd, `k = 3l - 7`.

Each is `Red.reduced_bound` (projection of a path word into the reduced model, `PathReducedProj.lean`) applied to
`Red.noSolB`, `Red.noSolC`, `Red.noSolA` (exhaustive search evaluated by the kernel, generated files).
-/

namespace Coil

variable {α : Type*} [Fintype α] [DecidableEq α] {k L : ℕ} {T : ℕ → α}

/-- **Theorem B.** `K = k+1` odd, `K ≥ 5`, `3d = 5K - 1`: a spread-`k` path in the `d`-cube has at most `4K - 1` edges. -/
theorem path_threshold_B (h : IsPathWord k L T) (hk : Even k) (hk4 : 4 ≤ k)
    (hd : 3 * Fintype.card α + 1 = 5 * (k + 1)) : L < 4 * (k + 1) := by
  have hk2 : k % 2 = 0 := Nat.even_iff.mp hk
  have hR : Red.Rsum Red.parB = 3 := by decide
  have H := Red.reduced_bound (P := Red.parB) Red.noSolB (by decide) h (show 1 = (k + 1) % 2 by omega)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (show 2 + 1 + 1 ≤ k + 1 by omega) (by decide)
    (by rw [hR]; show 6 * Fintype.card α + 1 + 6 ≤ 10 * (k + 1) + 3 + 2 * 1; omega)
  have H' : L + 1 < 4 * (k + 1) + 1 := H
  omega

/-- **Theorem C.** `K = k+1` odd, `K ≥ 3`, `3d = 5K`: a spread-`k` path in the `d`-cube has at most `4K + 1` edges. -/
theorem path_threshold_C (h : IsPathWord k L T) (hk : Even k) (hk2' : 2 ≤ k)
    (hd : 3 * Fintype.card α = 5 * (k + 1)) : L ≤ 4 * (k + 1) + 1 := by
  have hk2 : k % 2 = 0 := Nat.even_iff.mp hk
  have hR : Red.Rsum Red.parC = 2 := by decide
  have H := Red.reduced_bound (P := Red.parC) Red.noSolC (by decide) h (show 1 = (k + 1) % 2 by omega)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (show 2 + 0 + 1 ≤ k + 1 by omega) (by decide)
    (by rw [hR]; show 6 * Fintype.card α + 0 + 6 ≤ 10 * (k + 1) + 2 + 2 * 2; omega)
  have H' : L + 0 < 4 * (k + 1) + 2 := H
  omega

/-- **Theorem A.** `K = k+1` even, `K ≥ 6`, `3d = 5K`: a spread-`k` path in the `d`-cube has at most `4K + 2` edges. -/
theorem path_threshold_A (h : IsPathWord k L T) (hk : Odd k) (hk5 : 5 ≤ k)
    (hd : 3 * Fintype.card α = 5 * (k + 1)) : L ≤ 4 * (k + 1) + 2 := by
  have hk2 : k % 2 = 1 := Nat.odd_iff.mp hk
  have hR : Red.Rsum Red.parA = 6 := by decide
  have H := Red.reduced_bound (P := Red.parA) Red.noSolA (by decide) h (show 0 = (k + 1) % 2 by omega)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (show 4 + 0 + 1 ≤ k + 1 by omega) (by decide)
    (by rw [hR]; show 6 * Fintype.card α + 0 + 6 ≤ 10 * (k + 1) + 6 + 2 * 0; omega)
  have H' : L + 0 < 4 * (k + 1) + 3 := H
  omega

/-! ## Vertex versions in `(d, k, l)` form, `l = 2d - 3k - 1` -/

/-- **Theorem B**: `k` even, `k = 3l - 5` (`l` odd): `L ≤ 3k + 3l - 2`. -/
theorem path_length_threshold_B {v : ℕ → α → Bool} (h : IsPath k L v) (l : ℕ)
    (hd' : 2 * Fintype.card α = 3 * k + l + 1) (hk : Even k) (hk4 : 4 ≤ k) (hl : 3 * l = k + 5) :
    L + 2 ≤ 3 * k + 3 * l := by
  obtain ⟨T, hT, _⟩ := h.exists_word
  have := path_threshold_B hT hk hk4 (by omega)
  omega

/-- **Theorem C**: `k` even, `k = 3l - 7` (`l` odd): `L ≤ 3k + 3l - 2`. -/
theorem path_length_threshold_C {v : ℕ → α → Bool} (h : IsPath k L v) (l : ℕ)
    (hd' : 2 * Fintype.card α = 3 * k + l + 1) (hk : Even k) (hk2 : 2 ≤ k) (hl : 3 * l = k + 7) :
    L + 2 ≤ 3 * k + 3 * l := by
  obtain ⟨T, hT, _⟩ := h.exists_word
  have := path_threshold_C hT hk hk2 (by omega)
  omega

/-- **Theorem A**: `k` odd, `k = 3l - 7` (`l` even), `k ≥ 5`: `L ≤ 3k + 3l - 1`. -/
theorem path_length_threshold_A {v : ℕ → α → Bool} (h : IsPath k L v) (l : ℕ)
    (hd' : 2 * Fintype.card α = 3 * k + l + 1) (hk : Odd k) (hk5 : 5 ≤ k) (hl : 3 * l = k + 7) :
    L + 1 ≤ 3 * k + 3 * l := by
  obtain ⟨T, hT, _⟩ := h.exists_word
  have := path_threshold_A hT hk hk5 (by omega)
  omega

end Coil

#print axioms Coil.path_threshold_A
#print axioms Coil.path_threshold_B
#print axioms Coil.path_threshold_C
#print axioms Coil.path_length_threshold_A
#print axioms Coil.path_length_threshold_B
#print axioms Coil.path_length_threshold_C
