import Ccformal.Thm8Step

/-!
# Theorem 8 (PROOF2.md sec. 8)

`l = 4c+3`, `k = (l²-1)/2 - 2j` with `1 ≤ j ≤ c = (l-3)/4`, `n = (3k+l+1)/2`: there is no spread-`k`
circuit code of length `4k+2l+2` in `Q_n`, and `K(n,k) ≤ 4k+2l`.
(`k = 8c²+12c+4-2j`, `n = 12c²+20c+8-3j`, `4k+2l+2 = 32c²+56c+24-8j`.)
The formal statement covers `l = 7` as well (the written theorem assumes `l ≥ 11`).
-/

open Finset

namespace Coil

set_option linter.unusedSectionVars false

variable {α : Type*} [Fintype α] [DecidableEq α] {k N : ℕ} {T : ℕ → α}

theorem thm8_aux (h : IsCoilWord k N T) (c j Q : ℕ) (hQ : Q = c * c) (hj1 : 1 ≤ j) (hj2 : j ≤ c)
    (hk : k + 1 + 2 * j = 8 * Q + 12 * c + 5) (hN : N + 2 = 4 * (k + 1) + 2 * (4 * c + 3))
    (hn : 2 * Fintype.card α = 3 * k + (4 * c + 3) + 1) : False := by
  have hQc : c ≤ Q := by rw [hQ]; exact Nat.le_mul_self c
  have e : (4 * c + 3) * (4 * c + 3) = 16 * Q + 24 * c + 9 := by rw [hQ]; ring
  have hW := typeWord_of_coil h (by omega) ⟨4 * Q + 6 * c + 2 - j, by omega⟩ (4 * c + 3) hN hn
    (by omega) (by omega)
  exact no_typeWord _ c j Q (k + 1) (4 * c + 3) N hQ rfl hj1 hj2 hk hN hW

/-- **Theorem 8.** -/
theorem thm8 (c j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ c)
    (v : ℕ → Fin (12 * c * c + 20 * c + 8 - 3 * j) → Bool) :
    ¬ IsCoil (8 * c * c + 12 * c + 4 - 2 * j) (32 * c * c + 56 * c + 24 - 8 * j) v := by
  intro h
  obtain ⟨T, hT, _⟩ := h.exists_word
  have hQc : c ≤ c * c := Nat.le_mul_self c
  have e1 : 8 * c * c = 8 * (c * c) := by ring
  have e2 : 32 * c * c = 32 * (c * c) := by ring
  have e3 : 12 * c * c = 12 * (c * c) := by ring
  refine thm8_aux hT c j (c * c) rfl hj1 hj2 ?_ ?_ ?_
  · omega
  · omega
  · rw [Fintype.card_fin]; omega

theorem thm8_bound_aux (h : IsCoilWord k N T) (c j Q : ℕ) (hQ : Q = c * c) (hj1 : 1 ≤ j)
    (hj2 : j ≤ c) (hk : k + 1 + 2 * j = 8 * Q + 12 * c + 5)
    (hn : 2 * Fintype.card α = 3 * k + (4 * c + 3) + 1) : N ≤ 4 * k + 2 * (4 * c + 3) := by
  by_contra hcon
  rw [not_le] at hcon
  have hQc : c ≤ Q := by rw [hQ]; exact Nat.le_mul_self c
  obtain ⟨m, hm⟩ := even_length h
  by_cases hNeq : N + 2 = 4 * (k + 1) + 2 * (4 * c + 3)
  · exact thm8_aux h c j Q hQ hj1 hj2 hk hNeq hn
  · have hk1 : 1 ≤ k := by omega
    have hN5 : N < 5 * k + 4 := by
      by_contra h5
      have := no_long h hk1 (by omega)
      omega
    obtain ⟨r, hr⟩ : ∃ r, k = 2 * r := ⟨4 * Q + 6 * c + 2 - j, by omega⟩
    have C := chord_inequality h hk1 (by omega) (by omega) (L := 2 * k + 1) (by omega)
      (by omega) (by omega) (by omega)
    have e : (2 * k + 1 - k) / 2 = r := by omega
    rw [e] at C
    have hn' : (2 : ℤ) * Fintype.card α = 3 * k + (4 * c + 3) + 1 := by exact_mod_cast hn
    have a1 : (0 : ℤ) ≤ N - 4 * k - 2 * (4 * c + 3) - 2 := by
      have : (4 * k + 2 * (4 * c + 3) + 2 : ℤ) ≤ N := by
        exact_mod_cast (by omega : 4 * k + 2 * (4 * c + 3) + 2 ≤ N)
      linarith
    have a1' : (0 : ℤ) ≤ N - 4 * k - 2 * (4 * c + 3) - 4 := by
      have : (4 * k + 2 * (4 * c + 3) + 4 : ℤ) ≤ N := by
        exact_mod_cast (by omega : 4 * k + 2 * (4 * c + 3) + 4 ≤ N)
      linarith
    have a2 : (0 : ℤ) ≤ 5 * k + 4 - N := by
      have : (N : ℤ) ≤ 5 * k + 3 := by exact_mod_cast (by omega : N ≤ 5 * k + 3)
      linarith
    have a3 : (0 : ℤ) ≤ k - 1 - (4 * c + 3) := by
      have : (4 * c + 3 + 1 : ℤ) ≤ k := by exact_mod_cast (by omega : 4 * c + 3 + 1 ≤ k)
      linarith
    have a4 : ((4 : ℤ) * c + 3) * (4 * c + 3) = 2 * k + 1 + 4 * j := by
      have e' : (4 * c + 3) * (4 * c + 3) = 2 * k + 1 + 4 * j := by
        have : (4 * c + 3) * (4 * c + 3) = 16 * Q + 24 * c + 9 := by rw [hQ]; ring
        omega
      exact_mod_cast e'
    have a5 : (0 : ℤ) < (k : ℤ) - 1 - (4 * c + 3) - 4 * j := by
      have : (4 * c + 3 + 1 + 4 * j : ℤ) < k := by
        exact_mod_cast (by omega : 4 * c + 3 + 1 + 4 * j < k)
      linarith
    have hkr : (k : ℤ) = 2 * r := by exact_mod_cast hr
    push_cast at C
    rw [hn'] at C
    nlinarith [mul_nonneg a1 a2, mul_nonneg a3 a1', a4, a5]

/-- **Theorem 8, upper bound**: `K(n,k) ≤ 4k + 2l` for `l = 4c+3`, `k = (l²-1)/2 - 2j`, `1 ≤ j ≤ c`. -/
theorem thm8_bound (c j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ c) (N : ℕ)
    (v : ℕ → Fin (12 * c * c + 20 * c + 8 - 3 * j) → Bool)
    (h : IsCoil (8 * c * c + 12 * c + 4 - 2 * j) N v) :
    N ≤ 32 * c * c + 56 * c + 22 - 8 * j := by
  obtain ⟨T, hT, _⟩ := h.exists_word
  have hQc : c ≤ c * c := Nat.le_mul_self c
  have e1 : 8 * c * c = 8 * (c * c) := by ring
  have e2 : 32 * c * c = 32 * (c * c) := by ring
  have e3 : 12 * c * c = 12 * (c * c) := by ring
  have := thm8_bound_aux hT c j (c * c) rfl hj1 hj2 (by omega) (by rw [Fintype.card_fin]; omega)
  omega

end Coil

#print axioms Coil.thm8
#print axioms Coil.thm8_bound
