import Ccformal.PathReducedThms
import Ccformal.PathFamX

/-!
# The first point past the line range on even lines is exact      (S179-S180)

`path_threshold_A` (PathReducedThms.lean, verified search of the reduced boundary model) gives `L ≤ 4(k+1) + 2` for odd `k`,
`3d = 5(k+1)`; `famX_path` (PathFamX.lean, the family `fam(t)` of `pfam2.py`) attains it for `k + 1 = 6t`, `t ≥ 3`.
-/

namespace Coil

/-- **`P(10t, 6t-1) = 24t + 2`** for every `t ≥ 3`: with `k = 6t - 1`, `l = 2d - 3k - 1 = 2t + 2` (so `k = 3l - 7`) this is
`3k + 3l - 1`, one more than the line value `3k + 3l - 2`. -/
theorem maxPath_excess {t : ℕ} (ht : 3 ≤ t) : IsMaxPath (10 * t) (6 * t - 1) (24 * t + 2) := by
  refine ⟨famX_path ht, fun L' v' h' => ?_⟩
  obtain ⟨T, hT, _⟩ := h'.exists_word
  have hodd : Odd (6 * t - 1) := ⟨3 * t - 1, by omega⟩
  have := path_threshold_A hT hodd (by omega) (by simp only [Fintype.card_fin]; omega)
  omega

end Coil

#print axioms Coil.maxPath_excess
