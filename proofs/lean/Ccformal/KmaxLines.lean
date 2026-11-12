import Ccformal.LineEleven
import Ccformal.Values.K_42_25
import Ccformal.Values.K_65_40
import Ccformal.Values.K_101_63
import Ccformal.Values.K_133_84
import Ccformal.Values.K_161_102

/-!
# Complete lines: `k_max(l)` for `l = 8, 9, 12, 13, 15` (and `l = 11` in LineEleven.lean)

For each line `l` (n = (3k+l+1)/2): the exact value `K = 4k + 2l + 2` at `k = k_max(l)` (a kernel-checked code + Lemma 1/2),
and `K ≤ 4k + 2l` for every larger `k` on the line.
`k_max = 25, 40, 52, 63, 84, 102` for `l = 8, 9, 11, 12, 13, 15`  (= (l²-l-6)/2 for l ≡ 0, 3 mod 4; (l²-1)/2 for l ≡ 1 mod 4).
-/

namespace Coil

set_option linter.deprecated false

/-- `l = 8`: `K(42,25) = 118`, and `K ≤ 4k+16` for odd `k ≥ 27`. -/
theorem kmax_8 : IsMaxLength 42 25 118 ∧
    ∀ (k n N : ℕ) (v : ℕ → Fin n → Bool), IsCoil k N v → 27 ≤ k → 2 * n = 3 * k + 9 →
      N ≤ 4 * k + 16 := by
  refine ⟨K_42_25, fun k n N v h hk hn => ?_⟩
  by_cases hbig : 29 ≤ k
  · have hko : ¬ Even k := by
      rw [Nat.not_even_iff_odd, Nat.odd_iff]; omega
    have := coil_length_bound h (by omega) 8 (by norm_num) (by rw [Fintype.card_fin]; omega)
      (by simp only [hko, if_false]; omega)
    omega
  · obtain rfl : k = 27 := by omega
    obtain rfl : n = 45 := by omega
    exact thm7_bound 2 (by norm_num) N v h

/-- `l = 9`: `K(65,40) = 180`, and `K ≤ 4k+18` for even `k ≥ 42`. -/
theorem kmax_9 : IsMaxLength 65 40 180 ∧
    ∀ (k n N : ℕ) (v : ℕ → Fin n → Bool), IsCoil k N v → 42 ≤ k → 2 * n = 3 * k + 10 →
      N ≤ 4 * k + 18 := by
  refine ⟨K_65_40, fun k n N v h hk hn => ?_⟩
  have hke : Even k := ⟨k / 2, by omega⟩
  have := coil_length_bound h (by omega) 9 (by norm_num) (by rw [Fintype.card_fin]; omega)
    (by simp only [hke, if_true]; omega)
  omega

/-- `l = 12`: `K(101,63) = 278`, and `K ≤ 4k+24` for odd `k ≥ 65`. -/
theorem kmax_12 : IsMaxLength 101 63 278 ∧
    ∀ (k n N : ℕ) (v : ℕ → Fin n → Bool), IsCoil k N v → 65 ≤ k → 2 * n = 3 * k + 13 →
      N ≤ 4 * k + 24 := by
  refine ⟨K_101_63, fun k n N v h hk hn => ?_⟩
  by_cases hbig : 67 ≤ k
  · have hko : ¬ Even k := by
      rw [Nat.not_even_iff_odd, Nat.odd_iff]; omega
    have := coil_length_bound h (by omega) 12 (by norm_num) (by rw [Fintype.card_fin]; omega)
      (by simp only [hko, if_false]; omega)
    omega
  · obtain rfl : k = 65 := by omega
    obtain rfl : n = 104 := by omega
    exact thm7_bound 3 (by norm_num) N v h

/-- `l = 13`: `K(133,84) = 364`, and `K ≤ 4k+26` for even `k ≥ 86`. -/
theorem kmax_13 : IsMaxLength 133 84 364 ∧
    ∀ (k n N : ℕ) (v : ℕ → Fin n → Bool), IsCoil k N v → 86 ≤ k → 2 * n = 3 * k + 14 →
      N ≤ 4 * k + 26 := by
  refine ⟨K_133_84, fun k n N v h hk hn => ?_⟩
  have hke : Even k := ⟨k / 2, by omega⟩
  have := coil_length_bound h (by omega) 13 (by norm_num) (by rw [Fintype.card_fin]; omega)
    (by simp only [hke, if_true]; omega)
  omega

/-- `l = 15`: `K(161,102) = 440`, and `K ≤ 4k+30` for even `k ≥ 104`. -/
theorem kmax_15 : IsMaxLength 161 102 440 ∧
    ∀ (k n N : ℕ) (v : ℕ → Fin n → Bool), IsCoil k N v → 104 ≤ k → 2 * n = 3 * k + 16 →
      N ≤ 4 * k + 30 := by
  refine ⟨K_161_102, fun k n N v h hk hn => ?_⟩
  by_cases hbig : 114 ≤ k
  · have hke : Even k := ⟨k / 2, by omega⟩
    have := coil_length_bound h (by omega) 15 (by norm_num) (by rw [Fintype.card_fin]; omega)
      (by simp only [hke, if_true]; omega)
    omega
  · have hk2 : k = 104 ∨ k = 106 ∨ k = 108 ∨ k = 110 ∨ k = 112 := by omega
    rcases hk2 with rfl | rfl | rfl | rfl | rfl
    · obtain rfl : n = 164 := by omega
      exact thm9_bound 3 (by norm_num) N v h
    · obtain rfl : n = 167 := by omega
      exact thm8_bound 3 3 (by norm_num) (by norm_num) N v h
    · obtain rfl : n = 170 := by omega
      exact thm8_bound 3 2 (by norm_num) (by norm_num) N v h
    · obtain rfl : n = 173 := by omega
      exact thm8_bound 3 1 (by norm_num) (by norm_num) N v h
    · obtain rfl : n = 176 := by omega
      exact l3_bound 3 (by norm_num) N v h

end Coil

#print axioms Coil.kmax_8
#print axioms Coil.kmax_15
