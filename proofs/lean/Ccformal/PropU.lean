import Ccformal.OddL3

/-!
# Proposition U: the upper bound at every equality point of Lemma 1, for all parameters

Parametrisation: `K = k+1`, `2n + ρ = 3K + u` (i.e. `l = u - ρ + 2`), candidate length `4K + 2u`
(= `4k + 2l + e` with `e = 2ρ`).
* even lines (`k` odd):  if `2ρK = u(u+ρ)`   (equality in Lemma 1 at `L = 2K`),   `3u < K + 3ρ` and
  `u + ρ ≤ K + 1`, then every spread-`k` circuit code in `Q_n` has length `≤ 4K + 2u`;
* odd lines (`k` even):  if `2ρK = u² + u + uρ + 2ρ` (equality at `L = 2K-1`), `3u + 4 < K + 3ρ` and
  `u + ρ + 2 ≤ K`, the same conclusion.
These are the upper halves of Theorems 13, 14, 18-22, 27-29, 31 (even) and 35, 36 (odd).
-/

open Finset

namespace Coil

set_option linter.unusedSectionVars false

variable {α : Type*} [Fintype α] [DecidableEq α] {k N : ℕ} {T : ℕ → α}

theorem propU_even_aux (h : IsCoilWord k N T) (u ρ : ℕ) (hKe : Even (k + 1))
    (hn : 2 * Fintype.card α + ρ = 3 * (k + 1) + u) (hE : 2 * ρ * (k + 1) = u * (u + ρ))
    (h1 : 3 * u < k + 1 + 3 * ρ) (h2 : u + ρ ≤ k + 2) : N ≤ 4 * (k + 1) + 2 * u := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨c, hc⟩ := hKe
  obtain ⟨m, hm⟩ := even_length h
  have hk : 1 ≤ k := by omega
  have hN5 : N < 5 * k + 4 := by
    by_contra h5
    have := no_long h hk (by omega)
    omega
  have C := chord_inequality h hk (by omega) (by omega) (L := 2 * (k + 1)) (by omega)
    (by omega) (by omega) (by omega)
  have hc0 : (2 * (k + 1) - k) / 2 = c := by omega
  rw [hc0] at C
  obtain ⟨d, hd⟩ : ∃ d, N = 8 * c + 2 * u + 2 * d + 2 := ⟨m - 4 * c - u - 1, by omega⟩
  have z1 : (N : ℤ) = 8 * c + 2 * u + 2 * d + 2 := by exact_mod_cast hd
  have z2 : (2 : ℤ) * Fintype.card α = 6 * c + u - ρ := by
    have : ((2 * Fintype.card α + ρ : ℕ) : ℤ) = ((6 * c + u : ℕ) : ℤ) := by
      exact_mod_cast (by omega : 2 * Fintype.card α + ρ = 6 * c + u)
    push_cast at this
    linarith
  have z3 : ((2 * (k + 1) : ℕ) : ℤ) = 4 * c := by exact_mod_cast (by omega : 2 * (k + 1) = 4 * c)
  have z4 : (2 : ℤ) * ρ * (2 * c) = u * (u + ρ) := by
    have : ((2 * ρ * (k + 1) : ℕ) : ℤ) = ((u * (u + ρ) : ℕ) : ℤ) := by rw [hE]
    rw [show k + 1 = 2 * c by omega] at this
    push_cast at this
    linarith
  have hd1 : (0 : ℤ) < (d : ℤ) + 1 := by positivity
  have hd2 : (0 : ℤ) < 8 * c - 6 * u - 2 * ρ - 4 * (d + 1) := by
    have : 6 * u + 2 * ρ + 4 * (d + 1) < 8 * c := by omega
    have : ((6 * u + 2 * ρ + 4 * (d + 1) : ℕ) : ℤ) < ((8 * c : ℕ) : ℤ) := by exact_mod_cast this
    push_cast at this
    linarith
  rw [z1, z2, z3] at C
  nlinarith [mul_pos hd1 hd2, z4]

theorem propU_odd_aux (h : IsCoilWord k N T) (u ρ : ℕ) (hk : 1 ≤ k) (hke : Even k)
    (hn : 2 * Fintype.card α + ρ = 3 * (k + 1) + u)
    (hE : 2 * ρ * (k + 1) = u * u + u + u * ρ + 2 * ρ)
    (h1 : 3 * u + 4 < k + 1 + 3 * ρ) (h2 : u + ρ + 2 ≤ k + 1) : N ≤ 4 * (k + 1) + 2 * u := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨c, hc⟩ := hke
  obtain ⟨m, hm⟩ := even_length h
  have hN5 : N < 5 * k + 4 := by
    by_contra h5
    have := no_long h hk (by omega)
    omega
  have C := chord_inequality h hk (by omega) (by omega) (L := 2 * k + 1) (by omega)
    (by omega) (by omega) (by omega)
  have hc0 : (2 * k + 1 - k) / 2 = c := by omega
  rw [hc0] at C
  obtain ⟨d, hd⟩ : ∃ d, N = 8 * c + 4 + 2 * u + 2 * d + 2 := ⟨m - 4 * c - 2 - u - 1, by omega⟩
  have z1 : (N : ℤ) = 8 * c + 4 + 2 * u + 2 * d + 2 := by exact_mod_cast hd
  have z2 : (2 : ℤ) * Fintype.card α = 6 * c + 3 + u - ρ := by
    have : ((2 * Fintype.card α + ρ : ℕ) : ℤ) = ((6 * c + 3 + u : ℕ) : ℤ) := by
      exact_mod_cast (by omega : 2 * Fintype.card α + ρ = 6 * c + 3 + u)
    push_cast at this
    linarith
  have z3 : ((2 * k + 1 : ℕ) : ℤ) = 4 * c + 1 := by exact_mod_cast (by omega : 2 * k + 1 = 4 * c + 1)
  have z4 : (2 : ℤ) * ρ * (2 * c + 1) = u * u + u + u * ρ + 2 * ρ := by
    have : ((2 * ρ * (k + 1) : ℕ) : ℤ) = ((u * u + u + u * ρ + 2 * ρ : ℕ) : ℤ) := by rw [hE]
    rw [show k + 1 = 2 * c + 1 by omega] at this
    push_cast at this
    linarith
  have hd1 : (0 : ℤ) < (d : ℤ) + 1 := by positivity
  have hd2 : (0 : ℤ) < 8 * c - 6 * u - 2 * ρ - 2 - 4 * (d + 1) := by
    have : 6 * u + 2 * ρ + 2 + 4 * (d + 1) < 8 * c := by omega
    have : ((6 * u + 2 * ρ + 2 + 4 * (d + 1) : ℕ) : ℤ) < ((8 * c : ℕ) : ℤ) := by exact_mod_cast this
    push_cast at this
    linarith
  rw [z1, z2, z3] at C
  nlinarith [mul_pos hd1 hd2, z4]

/-- **Proposition U, even lines** (`k` odd). -/
theorem propU_even {n : ℕ} (v : ℕ → Fin n → Bool) (h : IsCoil k N v) (u ρ : ℕ)
    (hKe : Even (k + 1)) (hn : 2 * n + ρ = 3 * (k + 1) + u) (hE : 2 * ρ * (k + 1) = u * (u + ρ))
    (h1 : 3 * u < k + 1 + 3 * ρ) (h2 : u + ρ ≤ k + 2) : N ≤ 4 * (k + 1) + 2 * u := by
  obtain ⟨T, hT, _⟩ := h.exists_word
  exact propU_even_aux hT u ρ hKe (by rw [Fintype.card_fin]; exact hn) hE h1 h2

/-- **Proposition U, odd lines** (`k` even). -/
theorem propU_odd {n : ℕ} (v : ℕ → Fin n → Bool) (h : IsCoil k N v) (u ρ : ℕ) (hk : 1 ≤ k)
    (hke : Even k) (hn : 2 * n + ρ = 3 * (k + 1) + u)
    (hE : 2 * ρ * (k + 1) = u * u + u + u * ρ + 2 * ρ)
    (h1 : 3 * u + 4 < k + 1 + 3 * ρ) (h2 : u + ρ + 2 ≤ k + 1) : N ≤ 4 * (k + 1) + 2 * u := by
  obtain ⟨T, hT, _⟩ := h.exists_word
  exact propU_odd_aux hT u ρ hk hke (by rw [Fintype.card_fin]; exact hn) hE h1 h2

/-- instance check, even: `(n,k) = (33,19)`, `u = 8`, `ρ = 2`: `N ≤ 96` -/
example (N : ℕ) (v : ℕ → Fin 33 → Bool) (h : IsCoil 19 N v) : N ≤ 96 :=
  propU_even v h 8 2 (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- instance check, odd: `(n,k) = (208,130)`, `u = 26`, `ρ = 3`: `N ≤ 576` -/
example (N : ℕ) (v : ℕ → Fin 208 → Bool) (h : IsCoil 130 N v) : N ≤ 576 :=
  propU_odd v h 26 3 (by norm_num) (by decide) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

end Coil

#print axioms Coil.propU_even
#print axioms Coil.propU_odd
