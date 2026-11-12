import Ccformal.Thm26

/-!
# Odd lines `l = 3 (mod 4)`: the Main Theorem is not sharp

`l = 4j+3`, `k = (l²-1)/2 = 8j²+12j+4` (the largest `k` not covered by the Main Theorem),
`n = (3k+l+1)/2 = 12j²+20j+8`: there is NO code of length `4k+2l+2 = 32j²+56j+24`
(PROOF2.md sec. 2; here a corollary of `odd_line_condition`: the type word has period `l` and would
have `(l-1)/2` dots per period, an odd number).  Hence `K(n,k) ≤ 4k+2l` there (`j ≥ 1`).
For `l = 1 (mod 4)` the length `4k+2l+2` IS attained (family 1).
-/

open Finset

namespace Coil

set_option linter.unusedSectionVars false

variable {α : Type*} [Fintype α] [DecidableEq α] {k N : ℕ} {T : ℕ → α}

theorem l3_zero_slack_aux (h : IsCoilWord k N T) (j Q : ℕ) (hQ : Q = j * j)
    (hk : k = 8 * Q + 12 * j + 4) (hNj : N = 32 * Q + 56 * j + 24)
    (hn : Fintype.card α = 12 * Q + 20 * j + 8) : False := by
  obtain ⟨L, hL⟩ : ∃ L, L = 2 * k + 1 := ⟨_, rfl⟩
  have hke : Even k := ⟨4 * Q + 6 * j + 2, by omega⟩
  have hz : ((N : ℤ) - 2 * Fintype.card α) * (4 * L - N) = 2 * N * ((L - k) / 2 : ℕ) := by
    have hc0 : (L - k) / 2 = 4 * Q + 6 * j + 2 := by omega
    rw [hc0, hn, hNj, hL, hk, hQ]
    push_cast
    ring
  obtain ⟨m, hm⟩ := odd_line_condition h (by omega) hke hL (by omega) (by omega) (by omega) hz
  -- gcd(L, N) = l = 4j+3
  have hLl : L = (4 * j + 3) * (4 * j + 3) := by rw [hL, hk, hQ]; ring
  have hNl : N = (4 * j + 3) * (2 + 2 * (4 * j + 3)) := by rw [hNj, hQ]; ring
  have hg : Nat.gcd L N = 4 * j + 3 := by
    rw [hLl, hNl, Nat.gcd_mul_left, Nat.gcd_add_mul_right_right]
    have : Nat.Coprime (4 * j + 3) 2 := Nat.coprime_two_right.mpr ⟨2 * j + 1, by ring⟩
    rw [this, mul_one]
  have hNq : N / (4 * j + 3) = 8 * j + 8 := by
    rw [hNl]
    rw [Nat.mul_div_cancel_left _ (by omega)]
    ring
  rw [hg, hNq, hn, hNj] at hm
  have h1 : (8 * j + 8) * (2 * m) = (8 * j + 8) * (2 * j + 1) := by
    have e : (8 * j + 8) * (2 * j + 1) = 16 * Q + 24 * j + 8 := by rw [hQ]; ring
    omega
  have h2 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < 8 * j + 8) h1
  omega

/-- `l = 4j+3`, `k = (l²-1)/2`: no spread-`k` circuit code of length `4k+2l+2` in `Q_n`. -/
theorem l3_zero_slack (j : ℕ) (v : ℕ → Fin (12 * j * j + 20 * j + 8) → Bool) :
    ¬ IsCoil (8 * j * j + 12 * j + 4) (32 * j * j + 56 * j + 24) v := by
  intro h
  obtain ⟨T, hT, _⟩ := h.exists_word
  exact l3_zero_slack_aux hT j (j * j) rfl (by ring) (by ring) (by rw [Fintype.card_fin]; ring)

theorem l3_bound_aux (h : IsCoilWord k N T) (j Q : ℕ) (hj : 1 ≤ j) (hQ : Q = j * j)
    (hk : k = 8 * Q + 12 * j + 4) (hn : Fintype.card α = 12 * Q + 20 * j + 8) :
    N ≤ 32 * Q + 56 * j + 22 := by
  by_contra hcon
  rw [not_le] at hcon
  have hQj : j ≤ Q := by rw [hQ]; exact Nat.le_mul_self j
  obtain ⟨m, hm⟩ := even_length h
  by_cases hNeq : N = 32 * Q + 56 * j + 24
  · exact l3_zero_slack_aux h j Q hQ hk hNeq hn
  · have hN5 : N < 5 * k + 4 := by
      by_contra h5
      have := no_long h (by omega) (by omega)
      omega
    have C := chord_inequality h (by omega) (by omega) (by omega) (L := 2 * k + 1) (by omega)
      (by omega) (by omega) (by omega)
    have hc0 : (2 * k + 1 - k) / 2 = 4 * Q + 6 * j + 2 := by omega
    rw [hc0, hn] at C
    obtain ⟨e, he⟩ : ∃ e, N = 32 * Q + 56 * j + 24 + e := ⟨N - (32 * Q + 56 * j + 24), by omega⟩
    have he1 : (0 : ℤ) < e := by exact_mod_cast (by omega : 0 < e)
    have he2 : (0 : ℤ) < 16 * j * j + 8 * j - 2 - e := by
      have : e + 2 < 16 * Q + 8 * j := by omega
      have : (e : ℤ) + 2 < 16 * Q + 8 * j := by exact_mod_cast this
      rw [hQ] at this; push_cast at this; linarith
    rw [he, hk, hQ] at C
    push_cast at C
    nlinarith [mul_pos he1 he2]

/-- `l = 4j+3 ≥ 7`, `k = (l²-1)/2`: `K(n,k) ≤ 4k + 2l`. -/
theorem l3_bound (j : ℕ) (hj : 1 ≤ j) (N : ℕ) (v : ℕ → Fin (12 * j * j + 20 * j + 8) → Bool)
    (h : IsCoil (8 * j * j + 12 * j + 4) N v) : N ≤ 32 * j * j + 56 * j + 22 := by
  obtain ⟨T, hT, _⟩ := h.exists_word
  have := l3_bound_aux hT j (j * j) hj rfl (by ring) (by rw [Fintype.card_fin]; ring)
  have e : 32 * j * j = 32 * (j * j) := by ring
  omega

end Coil

#print axioms Coil.l3_zero_slack
#print axioms Coil.l3_bound
