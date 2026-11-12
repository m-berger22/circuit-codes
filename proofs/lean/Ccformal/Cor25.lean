import Ccformal.Parity

/-!
# Corollary 25: on even lines an excess `e = 2 (mod 4)` never attains the bound of Lemma 1

Setting: `k` odd, `K = k+1`, `N = 4k + 2l + e = 4K + 2u` with `e = 2ρ`, `ρ` odd, `u = l + ρ - 2`,
`n = (3k+l+1)/2`, i.e. `2n + ρ = 3K + u`.  Lemma 1 at `L = 2K` reads `2ρK ≤ u(u+ρ)`; if equality
holds (and `2 ≤ u < K`) there is no code.  (Theorem 7 is `ρ = 1`.)
-/

open Finset

namespace Coil

set_option linter.unusedSectionVars false

variable {α : Type*} [Fintype α] [DecidableEq α] {k N : ℕ} {T : ℕ → α}

theorem cor25_aux (h : IsCoilWord k N T) (u ρ : ℕ) (hρ : Odd ρ) (hKe : Even (k + 1))
    (hu2 : 2 ≤ u) (huK : u < k + 1) (hNu : N = 4 * (k + 1) + 2 * u)
    (hn : 2 * Fintype.card α + ρ = 3 * (k + 1) + u)
    (hE : 2 * ρ * (k + 1) = u * (u + ρ)) : False := by
  obtain ⟨c, hc⟩ := hKe
  obtain ⟨ρ', hρ'⟩ := hρ
  have hk : 1 ≤ k := by omega
  have huodd : Odd u := by
    rw [Nat.odd_iff]
    omega
  obtain ⟨L, hL⟩ : ∃ L, L = 2 * (k + 1) := ⟨_, rfl⟩
  -- zero slack
  have hz : ((N : ℤ) - 2 * Fintype.card α) * (4 * L - N) = 2 * N * ((L - k) / 2 : ℕ) := by
    have hc0 : (L - k) / 2 = c := by omega
    rw [hc0]
    have z1 : (N : ℤ) = 8 * c + 2 * u := by exact_mod_cast (by omega : N = 8 * c + 2 * u)
    have z2 : (2 : ℤ) * Fintype.card α = 6 * c + u - ρ := by
      have : ((2 * Fintype.card α + ρ : ℕ) : ℤ) = ((6 * c + u : ℕ) : ℤ) := by
        exact_mod_cast (by omega : 2 * Fintype.card α + ρ = 6 * c + u)
      push_cast at this
      linarith
    have z3 : (L : ℤ) = 4 * c := by exact_mod_cast (by omega : L = 4 * c)
    have z4 : (2 : ℤ) * ρ * (2 * c) = u * (u + ρ) := by
      have : ((2 * ρ * (k + 1) : ℕ) : ℤ) = ((u * (u + ρ) : ℕ) : ℤ) := by rw [hE]
      rw [show k + 1 = 2 * c by omega] at this
      push_cast at this
      linarith
    rw [z1, z2, z3]
    linear_combination 2 * z4
  -- the gcd
  obtain ⟨g, hg⟩ : ∃ g, g = Nat.gcd (k + 1) u := ⟨_, rfl⟩
  have hp : 2 * g = Nat.gcd L N := by
    rw [hNu, hL, hg, show 4 * (k + 1) + 2 * u = 2 * u + 2 * (2 * (k + 1)) by ring,
      Nat.gcd_add_mul_right_right, Nat.gcd_mul_left]
  have hgu : g ∣ u := hg ▸ Nat.gcd_dvd_right _ _
  have hgK : g ∣ k + 1 := hg ▸ Nat.gcd_dvd_left _ _
  have hgodd : Odd g := Odd.of_dvd_nat huodd hgu
  have hpK : 2 * g ∣ k + 1 :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.coprime_two_left.mpr hgodd) ⟨c, by omega⟩ hgK
  obtain ⟨K', hK'⟩ := hgK
  obtain ⟨u', hu'⟩ := hgu
  have hu'odd : Odd u' := by
    rw [hu'] at huodd
    exact (Nat.odd_mul.mp huodd).2
  have hgpos : 0 < g := by
    rcases Nat.eq_zero_or_pos g with h0 | h0
    · rw [h0] at hu'; omega
    · exact h0
  have hNp : N / (2 * g) = 2 * K' + u' := by
    have : N = (2 * g) * (2 * K' + u') := by
      rw [hNu, hK', hu']
      ring
    rw [this]
    exact Nat.mul_div_cancel_left _ (by omega)
  have hodd : Odd (N / (2 * g)) := by
    rw [hNp, Nat.odd_iff]
    rw [Nat.odd_iff] at hu'odd
    omega
  exact parity_obstruction_aux h hk ⟨c, hc⟩ hL (by omega) (by omega) hz (2 * g) hp hpK hodd

/-- **Corollary 25** for circuit codes in `Q_n`.  `k` odd, `ρ` odd, `e = 2ρ`, `u = l + ρ - 2`:
if `N = 4(k+1) + 2u`, `2n + ρ = 3(k+1) + u` and `2ρ(k+1) = u(u+ρ)` (equality in Lemma 1 at `L = 2k+2`)
with `2 ≤ u ≤ k`, then no spread-`k` circuit code of length `N` exists in `Q_n`. -/
theorem cor25 {n : ℕ} (v : ℕ → Fin n → Bool) (h : IsCoil k N v) (u ρ : ℕ) (hρ : Odd ρ)
    (hKe : Even (k + 1)) (hu2 : 2 ≤ u) (huK : u < k + 1) (hNu : N = 4 * (k + 1) + 2 * u)
    (hn : 2 * n + ρ = 3 * (k + 1) + u) (hE : 2 * ρ * (k + 1) = u * (u + ρ)) : False := by
  obtain ⟨T, hT, _⟩ := h.exists_word
  exact cor25_aux hT u ρ hρ hKe hu2 huK hNu (by rw [Fintype.card_fin]; exact hn) hE

/-- **Theorem 24** for circuit codes in `Q_n`. -/
theorem parity_obstruction {n : ℕ} (v : ℕ → Fin n → Bool) (h : IsCoil k N v) (hk : 1 ≤ k)
    (hKe : Even (k + 1)) (hN1 : 4 * (k + 1) + 2 < N) (hN6 : N < 6 * (k + 1))
    (hz : ((N : ℤ) - 2 * n) * (4 * (2 * (k + 1) : ℕ) - N) = 2 * N * ((2 * (k + 1) - k) / 2 : ℕ))
    (hpK : Nat.gcd (2 * (k + 1)) N ∣ k + 1) (hodd : Odd (N / Nat.gcd (2 * (k + 1)) N)) : False := by
  obtain ⟨T, hT, _⟩ := h.exists_word
  exact parity_obstruction_aux hT hk hKe (L := 2 * (k + 1)) rfl (by omega) hN6
    (by rw [Fintype.card_fin]; exact hz) _ rfl hpK hodd

/-- sanity check of the statement: `(n,k,N) = (30,17,90)` (excess 6, `u = 9`, `ρ = 3`, `l = 8`):
no code of length 90 (formerly SAT-only). -/
example (v : ℕ → Fin 30 → Bool) : ¬ IsCoil 17 90 v := fun h =>
  cor25 v h 9 3 (by decide) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

end Coil

#print axioms Coil.cor25
#print axioms Coil.parity_obstruction
