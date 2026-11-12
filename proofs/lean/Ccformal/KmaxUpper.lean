import Ccformal.KmaxLines

/-!
# The upper bounds of the `k_max` table, for ALL lines in a residue class

Notation: `l = 2n - 3k - 1`.  Byrnes' value is `4k + 2l`.
* `kmax_upper_l0`: `l = 4q ≥ 8`,   `k` odd,  `k > (l²-l-6)/2`  ⇒  `N ≤ 4k + 2l`.      (Theorem 7 + Main Theorem)
* `kmax_upper_l3`: `l = 4c+3 ≥ 11`, `k` even, `k > (l²-l-6)/2`  ⇒  `N ≤ 4k + 2l`.      (Theorems 9, 8, sec. 2, Main Theorem)
* `kmax_upper_l1`: `l = 4c+1`,      `k` even, `k > (l²-1)/2`, `k > 3l-3`  ⇒  `N ≤ 4k + 2l`.   (Main Theorem)
* `kmax_upper_l2`: `l = 4c+2`,      `k` odd,  `k > (l²-l-4)/2`  ⇒  `N ≤ 4k + 2l`.      (Main Theorem)
-/

namespace Coil

set_option linter.deprecated false

theorem kmax_upper_l0 (q k n N : ℕ) (hq : 2 ≤ q) (v : ℕ → Fin n → Bool) (h : IsCoil k N v)
    (hko : Odd k) (hn : 2 * n = 3 * k + 4 * q + 1) (hk : 8 * q * q ≤ k + 2 * q + 1) :
    N ≤ 4 * k + 2 * (4 * q) := by
  obtain ⟨T, hT, _⟩ := h.exists_word
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = q * q := ⟨_, rfl⟩
  have e1 : 8 * q * q = 8 * Q := by rw [hQ]; ring
  have hQq : 2 * q ≤ Q := by rw [hQ]; exact Nat.mul_le_mul_right q hq
  have hcard : 2 * Fintype.card (Fin n) = 3 * k + 4 * q + 1 := by rw [Fintype.card_fin]; exact hn
  by_cases hbig : 8 * Q ≤ k + 2 * q
  · have hke : ¬ Even k := Nat.not_even_iff_odd.mpr hko
    have e2 : 4 * q * (4 * q) = 16 * Q := by rw [hQ]; ring
    exact main_theorem hT (by omega) (4 * q) (by omega) hcard (by simp only [hke, if_false]; omega)
  · have := thm7_bound_aux hT q Q hq hQ (by omega) (by rw [Fintype.card_fin]; omega)
    omega

theorem kmax_upper_l3 (c k n N : ℕ) (hc : 2 ≤ c) (v : ℕ → Fin n → Bool) (h : IsCoil k N v)
    (hke : Even k) (hn : 2 * n = 3 * k + (4 * c + 3) + 1) (hk : 8 * c * c + 10 * c + 2 ≤ k) :
    N ≤ 4 * k + 2 * (4 * c + 3) := by
  obtain ⟨T, hT, _⟩ := h.exists_word
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = c * c := ⟨_, rfl⟩
  have e1 : 8 * c * c = 8 * Q := by rw [hQ]; ring
  have hQc : 2 * c ≤ Q := by rw [hQ]; exact Nat.mul_le_mul_right c hc
  obtain ⟨r, hr⟩ := hke
  have hcard : 2 * Fintype.card (Fin n) = 3 * k + (4 * c + 3) + 1 := by
    rw [Fintype.card_fin]; exact hn
  by_cases h1 : 8 * Q + 12 * c + 5 ≤ k
  · have e2 : (4 * c + 3) * (4 * c + 3) = 16 * Q + 24 * c + 9 := by rw [hQ]; ring
    have hke' : Even k := ⟨r, hr⟩
    exact main_theorem hT (by omega) (4 * c + 3) (by omega) hcard
      (by rw [if_pos hke']; omega)
  · by_cases h2 : k = 8 * Q + 12 * c + 4
    · have := l3_bound_aux hT c Q (by omega) hQ h2 (by rw [Fintype.card_fin]; omega)
      omega
    · by_cases h3 : k = 8 * Q + 10 * c + 2
      · exact thm9_bound_aux hT c Q hQ hc (by omega) hcard
      · obtain ⟨j, hj⟩ : ∃ j, k + 2 * j = 8 * Q + 12 * c + 4 := ⟨(8 * Q + 12 * c + 4 - k) / 2, by omega⟩
        exact thm8_bound_aux hT c j Q hQ (by omega) (by omega) (by omega) hcard

theorem kmax_upper_l1 (c k n N : ℕ) (v : ℕ → Fin n → Bool) (h : IsCoil k N v) (hc : 1 ≤ c)
    (hke : Even k) (hn : 2 * n = 3 * k + (4 * c + 1) + 1) (hk : 8 * c * c + 4 * c < k)
    (hk3 : 3 * (4 * c + 1) < k + 3) : N ≤ 4 * k + 2 * (4 * c + 1) := by
  have e2 : (4 * c + 1) * (4 * c + 1) = 2 * (8 * c * c + 4 * c) + 1 := by ring
  exact coil_length_bound h (by omega) (4 * c + 1) (by omega) (by rw [Fintype.card_fin]; exact hn)
    (by simp only [hke, if_true]; omega)

theorem kmax_upper_l2 (c k n N : ℕ) (v : ℕ → Fin n → Bool) (h : IsCoil k N v)
    (hko : Odd k) (hn : 2 * n = 3 * k + (4 * c + 2) + 1) (hk : 8 * c * c + 6 * c < k) :
    N ≤ 4 * k + 2 * (4 * c + 2) := by
  have hke : ¬ Even k := Nat.not_even_iff_odd.mpr hko
  have e2 : (4 * c + 2) * (4 * c + 2) = 2 * (8 * c * c + 6 * c) + 4 * c + 4 := by ring
  obtain ⟨r, hr⟩ := hko
  exact coil_length_bound h (by omega) (4 * c + 2) (by omega) (by rw [Fintype.card_fin]; exact hn)
    (by simp only [hke, if_false]; omega)

end Coil

#print axioms Coil.kmax_upper_l0
#print axioms Coil.kmax_upper_l3
#print axioms Coil.kmax_upper_l1
#print axioms Coil.kmax_upper_l2
