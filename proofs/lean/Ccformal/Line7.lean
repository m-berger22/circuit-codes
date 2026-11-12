import Ccformal.Thm9Four
import Ccformal.Lines

/-!
# Theorem 9 at `l = 7`, and the line `l = 7` beyond `k_max = 18`

`K(34,20) = 94` (formerly SAT only): no code of length 96 (`thm9_seven`, via `no_xi9_four`), and `N ≤ 94` (`thm9_bound_seven`).
`exact_l7`: `K(n,k) = 4k + 14` for EVERY even `k ≥ 20` on the line `l = 7` (k = 20: Theorem 9; 22: Theorem 8; 24: PROOF2 sec. 2;
`k ≥ 26`: Main Theorem; lower bound: Byrnes' sequence).  With this, `K(n,k) = 4k + 2l` is formal beyond the `k_max` thresholds
on every line.
-/

namespace Coil

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {α : Type*} [Fintype α] [DecidableEq α] {k N : ℕ} {T : ℕ → α}

theorem thm9_aux7 (h : IsCoilWord k N T) (hk : k + 1 + 2 * (1 + 1) = 8 * 1 + 12 * 1 + 5)
    (hN : N + 2 = 4 * (k + 1) + 2 * (4 * 1 + 3)) (hn : 2 * Fintype.card α = 3 * k + (4 * 1 + 3) + 1) : False := by
  have hW := typeWordT_of_coil h (by omega) ⟨10, by omega⟩ (4 * 1 + 3) hN hn (by omega) (by omega)
  obtain ⟨ξ, X⟩ := xi9_of_typeWordT _ _ _ 1 1 (k + 1) (4 * 1 + 3) N (by omega) rfl rfl hk hN hW
  exact no_xi9_four X

/-- **Theorem 9 at `l = 7`**: no spread-20 circuit code of length 96 in `Q_34`. -/
theorem thm9_seven (v : ℕ → Fin 34 → Bool) : ¬ IsCoil 20 96 v := by
  intro h
  obtain ⟨T, hT, _⟩ := h.exists_word
  exact thm9_aux7 hT (by norm_num) (by norm_num) (by rw [Fintype.card_fin])

theorem thm9_bound_aux7 (h : IsCoilWord k N T) (hk : k = 20) (hn : Fintype.card α = 34) : N ≤ 94 := by
  by_contra hcon
  rw [not_le] at hcon
  subst hk
  obtain ⟨m, hm⟩ := even_length h
  by_cases hNeq : N = 96
  · exact thm9_aux7 h (by norm_num) (by omega) (by omega)
  · have hN5 : N < 5 * 20 + 4 := by
      by_contra h5
      have := no_long h (by norm_num) (by omega)
      omega
    have C := chord_inequality h (by norm_num) (by omega) (by omega) (L := 2 * 20 + 1) (by omega)
      (by omega) (by omega) (by omega)
    rw [hn] at C
    norm_num at C
    -- (N/2 - 34)(164 - N) ≤ 10 N for even N in [98, 102]
    have h98 : N = 98 ∨ N = 100 ∨ N = 102 := by omega
    rcases h98 with rfl | rfl | rfl <;> norm_num at C

/-- `K(34,20) ≤ 94` -/
theorem thm9_bound_seven (N : ℕ) (v : ℕ → Fin 34 → Bool) (h : IsCoil 20 N v) : N ≤ 94 := by
  obtain ⟨T, hT, _⟩ := h.exists_word
  exact thm9_bound_aux7 hT rfl (by rw [Fintype.card_fin])

/-- **The line `l = 7` beyond `k_max = 18`:** `K(n,k) = 4k + 14` for every even `k ≥ 20`, `n = (3k+8)/2`. -/
theorem exact_l7 (k n : ℕ) (hke : Even k) (hk : 20 ≤ k) (hn : 2 * n = 3 * k + 8) :
    IsMaxLength n k (4 * k + 2 * 7) := by
  refine ⟨byrnes_lower k 7 n (by norm_num) (by omega) (by omega), fun N v h => ?_⟩
  by_cases hbig : 26 ≤ k
  · exact coil_length_bound h (by omega) 7 (by norm_num) (by rw [Fintype.card_fin]; omega)
      (by simp only [hke, if_true]; omega)
  · obtain ⟨r, hr⟩ := hke
    have hk3 : k = 20 ∨ k = 22 ∨ k = 24 := by omega
    rcases hk3 with rfl | rfl | rfl
    · obtain rfl : n = 34 := by omega
      exact thm9_bound_seven N v h
    · obtain rfl : n = 37 := by omega
      exact thm8_bound 1 1 (by norm_num) (by norm_num) N v h
    · obtain rfl : n = 40 := by omega
      exact l3_bound 1 (by norm_num) N v h

/-- `K(34,20) = 94` -/
theorem K_34_20 : IsMaxLength 34 20 94 := exact_l7 20 34 ⟨10, rfl⟩ (by norm_num) (by norm_num)

end Coil

#print axioms Coil.thm9_seven
#print axioms Coil.exact_l7
