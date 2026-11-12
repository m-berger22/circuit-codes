import Ccformal.Thm9
import Ccformal.Values.K_84_52

/-!
# The line `l = 11` (n = (3k+12)/2), completely settled above `k = 52`

`K(84,52) = 232 = 4k + 2l + 2`, and for every even `k ≥ 54`:  `K((3k+12)/2, k) ≤ 4k + 22 = 4k + 2l`.
So `k_max(11) = 52`: Byrnes' Conjecture 4.2 (`K = 4k + 2l` for `k ≥ 2l-2`) fails at `k = 52` on this line, and its
upper-bound half holds for all `k ≥ 54`.  (k = 54: Theorem 9; 56, 58: Theorem 8; 60: `l3_bound`; ≥ 62: Main Theorem.)
-/

namespace Coil

theorem line11_bound (k n N : ℕ) (v : ℕ → Fin n → Bool) (h : IsCoil k N v) (hk : 54 ≤ k)
    (hn : 2 * n = 3 * k + 12) : N ≤ 4 * k + 22 := by
  by_cases hbig : 62 ≤ k
  · have hke : Even k := ⟨k / 2, by omega⟩
    have := coil_length_bound h (by omega) 11 (by norm_num) (by rw [Fintype.card_fin]; omega)
      (by simp only [hke, if_true]; omega)
    omega
  · have hk2 : k = 54 ∨ k = 56 ∨ k = 58 ∨ k = 60 := by omega
    rcases hk2 with rfl | rfl | rfl | rfl
    · obtain rfl : n = 87 := by omega
      exact thm9_bound 2 (by norm_num) N v h
    · obtain rfl : n = 90 := by omega
      exact thm8_bound 2 2 (by norm_num) (by norm_num) N v h
    · obtain rfl : n = 93 := by omega
      exact thm8_bound 2 1 (by norm_num) (by norm_num) N v h
    · obtain rfl : n = 96 := by omega
      exact l3_bound 2 (by norm_num) N v h

/-- `k_max(11) = 52`. -/
theorem kmax_11 : IsMaxLength 84 52 232 ∧
    ∀ (k n N : ℕ) (v : ℕ → Fin n → Bool), IsCoil k N v → 54 ≤ k → 2 * n = 3 * k + 12 →
      N ≤ 4 * k + 22 :=
  ⟨K_84_52, fun k n N v h hk hn => line11_bound k n N v h hk hn⟩

end Coil

#print axioms Coil.kmax_11
