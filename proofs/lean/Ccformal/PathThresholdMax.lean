import Ccformal.PathReducedThms
import Ccformal.PathFamOdd

/-!
# Sharp thresholds on odd lines      (S179)

`maxPath_odd_l` (PathFamOdd.lean) gives `P(d,k) = 3k + 3l - 2` for even `k`, odd `l = 2h+3`, `k ≥ 3l - 3` (`κ ≥ 3h+3`, `k = 2κ`).
The family `famOdd` is a path word for all `κ ≥ 2h`, and Theorems B, C (`PathReducedThms.lean`) give the upper bound at
`k = 3l - 5` (`κ = 3h+2`) and `k = 3l - 7` (`κ = 3h+1`).  Hence the formula holds for all even `k ≥ 3l - 7`.
-/

namespace Coil

/-- **`P(d,k) = 3k + 3l - 2`** for even `k = 2κ`, odd `l = 2h + 3`, `2d = 3k + l + 1`, and all `k ≥ 3l - 7`
(i.e. `κ ≥ 3h + 1`). -/
theorem maxPath_odd_l_sharp {κ h : ℕ} (hκ : 3 * h + 1 ≤ κ) {k : ℕ} (hk : k = 2 * κ) :
    IsMaxPath (3 * κ + h + 2) k (6 * κ + 6 * h + 7) := by
  by_cases h3 : 3 * h + 3 ≤ κ
  · exact maxPath_odd_l h3 hk
  refine ⟨famOdd_path (by omega) hk, fun L' v' h' => ?_⟩
  have heven : Even k := ⟨κ, by omega⟩
  by_cases h2 : κ = 3 * h + 2
  · have := path_length_threshold_B h' (2 * h + 3) (by simp only [Fintype.card_fin]; omega) heven (by omega) (by omega)
    omega
  · have hκ1 : κ = 3 * h + 1 := by omega
    have := path_length_threshold_C h' (2 * h + 3) (by simp only [Fintype.card_fin]; omega) heven (by omega) (by omega)
    omega

end Coil

#print axioms Coil.maxPath_odd_l_sharp
