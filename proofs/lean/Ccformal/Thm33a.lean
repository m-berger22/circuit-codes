import Ccformal.PropU

/-!
# Even lines: at an equality point a code exists only if `K / gcd(K,u)` is odd

General form of Theorems 15, 17, 24 and Corollary 25, and the first half of Theorem 33 (PROOF14.md):
`k` odd, `K = k+1`, `N = 4K + 2u`, `2n + ρ = 3K + u`, equality `2ρK = u(u+ρ)` in Lemma 1 at `L = 2K`,
`2 ≤ u < K`.  If `K / gcd(K,u)` is even there is no spread-`k` circuit code of length `N` in `Q_n`.
(For `ρ` odd this quotient is always even: Corollary 25.)
-/

open Finset

namespace Coil

set_option linter.unusedSectionVars false

variable {α : Type*} [Fintype α] [DecidableEq α] {k N : ℕ} {T : ℕ → α}

theorem thm33a_aux (h : IsCoilWord k N T) (u ρ : ℕ) (hKe : Even (k + 1))
    (hu2 : 2 ≤ u) (huK : u < k + 1) (hNu : N = 4 * (k + 1) + 2 * u)
    (hn : 2 * Fintype.card α + ρ = 3 * (k + 1) + u)
    (hE : 2 * ρ * (k + 1) = u * (u + ρ))
    (hq : Even ((k + 1) / Nat.gcd (k + 1) u)) : False := by
  obtain ⟨c, hc⟩ := hKe
  have hk : 1 ≤ k := by omega
  obtain ⟨L, hL⟩ : ∃ L, L = 2 * (k + 1) := ⟨_, rfl⟩
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
  obtain ⟨g, hg⟩ : ∃ g, g = Nat.gcd (k + 1) u := ⟨_, rfl⟩
  rw [← hg] at hq
  have hp : 2 * g = Nat.gcd L N := by
    rw [hNu, hL, hg, show 4 * (k + 1) + 2 * u = 2 * u + 2 * (2 * (k + 1)) by ring,
      Nat.gcd_add_mul_right_right, Nat.gcd_mul_left]
  have hgu : g ∣ u := hg ▸ Nat.gcd_dvd_right _ _
  have hgK : g ∣ k + 1 := hg ▸ Nat.gcd_dvd_left _ _
  have hgpos : 0 < g := by
    rw [hg]
    exact Nat.gcd_pos_of_pos_right _ (by omega)
  obtain ⟨K', hK'⟩ := hgK
  obtain ⟨u', hu'⟩ := hgu
  have hKq : (k + 1) / g = K' := by rw [hK']; exact Nat.mul_div_cancel_left _ hgpos
  rw [hKq] at hq
  have hcop : Nat.Coprime K' u' := by
    have h1 := Nat.coprime_div_gcd_div_gcd (m := k + 1) (n := u) (by rw [← hg]; exact hgpos)
    rw [← hg, hKq] at h1
    have h2 : u / g = u' := by rw [hu']; exact Nat.mul_div_cancel_left _ hgpos
    rw [h2] at h1
    exact h1
  have hu'odd : Odd u' := by
    by_contra hne
    have he : Even u' := Nat.not_odd_iff_even.mp hne
    have h2K : 2 ∣ K' := even_iff_two_dvd.mp hq
    have h2u : 2 ∣ u' := even_iff_two_dvd.mp he
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2K hcop) h2u
    omega
  have hpK : 2 * g ∣ k + 1 := by
    obtain ⟨K'', hK''⟩ := hq
    exact ⟨K'', by rw [hK', hK'']; ring⟩
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

/-- **Theorem 33, first half** (contains Theorems 15, 17, 24, Corollary 25). -/
theorem thm33a {n : ℕ} (v : ℕ → Fin n → Bool) (h : IsCoil k N v) (u ρ : ℕ)
    (hKe : Even (k + 1)) (hu2 : 2 ≤ u) (huK : u < k + 1) (hNu : N = 4 * (k + 1) + 2 * u)
    (hn : 2 * n + ρ = 3 * (k + 1) + u) (hE : 2 * ρ * (k + 1) = u * (u + ρ))
    (hq : Even ((k + 1) / Nat.gcd (k + 1) u)) : False := by
  obtain ⟨T, hT, _⟩ := h.exists_word
  exact thm33a_aux hT u ρ hKe hu2 huK hNu (by rw [Fintype.card_fin]; exact hn) hE hq

/-- **Theorem 15**: `l = 8q+6`, `k = (l²+2l-4)/4 = 16q²+28q+11`, `n = (3k+l+1)/2 = 24q²+46q+20`:
no spread-`k` circuit code of length `4k+2l+4 = l(l+4) = 64q²+128q+60`. -/
theorem thm15 (q : ℕ) (v : ℕ → Fin (24 * q * q + 46 * q + 20) → Bool) :
    ¬ IsCoil (16 * q * q + 28 * q + 11) (64 * q * q + 128 * q + 60) v := by
  intro h
  have hKu : 16 * q * q + 28 * q + 11 + 1 = (8 * q + 6) * (2 * q + 2) := by ring
  refine thm33a v h (8 * q + 6) 2 ?_ (by omega) ?_ (by ring) (by ring) (by ring) ?_
  · exact ⟨8 * q * q + 14 * q + 6, by ring⟩
  · rw [hKu]; nlinarith
  · rw [hKu, Nat.gcd_mul_right_left, Nat.mul_div_cancel_left _ (by omega)]
    exact ⟨q + 1, by ring⟩

end Coil

#print axioms Coil.thm33a
#print axioms Coil.thm15
