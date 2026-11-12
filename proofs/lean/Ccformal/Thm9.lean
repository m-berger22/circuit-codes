import Ccformal.Thm9Comb

/-!
# Theorem 9 (PROOF2.md sec. 9)

`l = 4c+3 ≥ 11`, `k = (l²-l-2)/2 = 8c²+10c+2`, `n = (3k+l+1)/2 = 12c²+17c+5`: there is no spread-`k` circuit code of length
`4k+2l+2 = 32c²+48c+16` in `Q_n`, and `K(n,k) ≤ 4k+2l`.
With `l3_zero_slack`/`l3_bound` and Theorem 8: for `l ≡ 3 (mod 4)`, `l ≥ 11`, a code longer than `4k+2l` needs
`k ≤ (l²-l-6)/2`, i.e. `k_max(l) ≤ (l²-l-6)/2`.
-/

open Finset

namespace Coil

set_option linter.unusedSectionVars false

variable {α : Type*} [Fintype α] [DecidableEq α] {k N : ℕ} {T : ℕ → α}

theorem thm9_aux (h : IsCoilWord k N T) (c Q : ℕ) (hQ : Q = c * c) (hc : 2 ≤ c)
    (hk : k + 1 + 2 * (c + 1) = 8 * Q + 12 * c + 5) (hN : N + 2 = 4 * (k + 1) + 2 * (4 * c + 3))
    (hn : 2 * Fintype.card α = 3 * k + (4 * c + 3) + 1) : False := by
  have hQc : 2 * c ≤ Q := by rw [hQ]; exact Nat.mul_le_mul_right c hc
  have e : (4 * c + 3) * (4 * c + 3) = 16 * Q + 24 * c + 9 := by rw [hQ]; ring
  have hW := typeWordT_of_coil h (by omega) ⟨4 * Q + 5 * c + 1, by omega⟩ (4 * c + 3) hN hn
    (by omega) (by omega)
  obtain ⟨ξ, X⟩ := xi9_of_typeWordT _ _ _ c Q (k + 1) (4 * c + 3) N (by omega) hQ rfl hk hN hW
  exact no_xi9 X (by omega)

/-- **Theorem 9.** -/
theorem thm9 (c : ℕ) (hc : 2 ≤ c) (v : ℕ → Fin (12 * c * c + 17 * c + 5) → Bool) :
    ¬ IsCoil (8 * c * c + 10 * c + 2) (32 * c * c + 48 * c + 16) v := by
  intro h
  obtain ⟨T, hT, _⟩ := h.exists_word
  have e1 : 8 * c * c = 8 * (c * c) := by ring
  have e2 : 32 * c * c = 32 * (c * c) := by ring
  have e3 : 12 * c * c = 12 * (c * c) := by ring
  refine thm9_aux hT c (c * c) rfl hc ?_ ?_ ?_
  · omega
  · omega
  · rw [Fintype.card_fin]; omega

theorem thm9_bound_aux (h : IsCoilWord k N T) (c Q : ℕ) (hQ : Q = c * c) (hc : 2 ≤ c)
    (hk : k + 1 + 2 * (c + 1) = 8 * Q + 12 * c + 5)
    (hn : 2 * Fintype.card α = 3 * k + (4 * c + 3) + 1) : N ≤ 4 * k + 2 * (4 * c + 3) := by
  by_contra hcon
  rw [not_le] at hcon
  have hQc : 2 * c ≤ Q := by rw [hQ]; exact Nat.mul_le_mul_right c hc
  obtain ⟨m, hm⟩ := even_length h
  by_cases hNeq : N + 2 = 4 * (k + 1) + 2 * (4 * c + 3)
  · exact thm9_aux h c Q hQ hc hk hNeq hn
  · have hk1 : 1 ≤ k := by omega
    have hN5 : N < 5 * k + 4 := by
      by_contra h5
      have := no_long h hk1 (by omega)
      omega
    obtain ⟨r, hr⟩ : ∃ r, k = 2 * r := ⟨4 * Q + 5 * c + 1, by omega⟩
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
    have a4 : ((4 : ℤ) * c + 3) * (4 * c + 3) = 2 * k + 1 + 4 * (c + 1) := by
      have e' : (4 * c + 3) * (4 * c + 3) = 2 * k + 1 + 4 * (c + 1) := by
        have : (4 * c + 3) * (4 * c + 3) = 16 * Q + 24 * c + 9 := by rw [hQ]; ring
        omega
      exact_mod_cast e'
    have a5 : (0 : ℤ) < (k : ℤ) - 1 - (4 * c + 3) - 4 * (c + 1) := by
      have : (4 * c + 3 + 1 + 4 * (c + 1) : ℤ) < k := by
        exact_mod_cast (by omega : 4 * c + 3 + 1 + 4 * (c + 1) < k)
      linarith
    have hkr : (k : ℤ) = 2 * r := by exact_mod_cast hr
    push_cast at C
    rw [hn'] at C
    nlinarith [mul_nonneg a1 a2, mul_nonneg a3 a1', a4, a5]

/-- **Theorem 9, upper bound**: `K(n,k) ≤ 4k + 2l` for `l = 4c+3 ≥ 11`, `k = (l²-l-2)/2`. -/
theorem thm9_bound (c : ℕ) (hc : 2 ≤ c) (N : ℕ) (v : ℕ → Fin (12 * c * c + 17 * c + 5) → Bool)
    (h : IsCoil (8 * c * c + 10 * c + 2) N v) : N ≤ 32 * c * c + 48 * c + 14 := by
  obtain ⟨T, hT, _⟩ := h.exists_word
  have e1 : 8 * c * c = 8 * (c * c) := by ring
  have e2 : 32 * c * c = 32 * (c * c) := by ring
  have e3 : 12 * c * c = 12 * (c * c) := by ring
  have := thm9_bound_aux hT c (c * c) rfl hc (by omega) (by rw [Fintype.card_fin]; omega)
  omega

end Coil

#print axioms Coil.thm9
#print axioms Coil.thm9_bound
