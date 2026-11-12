import Ccformal.Thm8Setup

/-!
# Theorem 8, Step 3: a counting lemma on periodic sequences

`ξ : ℕ → ℤ` is nonnegative with period `Λ = 4a` and mass `M` per period, every nonzero value is `≥ 2`,
and every zero `τ` has mass `≥ m0` in `(τ, τ+a]` or in `[τ-a-1, τ-1]`.  If `M < 2 m0` and `M < 4a - 2`
this is impossible: zeros of the first kind are pairwise at cyclic distance `< a`, those of the second
kind at distance `≤ a`, so there are at most `2a + 1` zeros, but at least `4a - M/2`.
-/

open Finset

namespace Coil

set_option linter.deprecated false

/-- window sum -/
def Sw (ξ : ℕ → ℤ) (t n : ℕ) : ℤ := ∑ i ∈ range n, ξ (t + i)

lemma Sw_add (ξ : ℕ → ℤ) (t a b : ℕ) : Sw ξ t (a + b) = Sw ξ t a + Sw ξ (t + a) b := by
  simp only [Sw, sum_range_add, add_assoc]

lemma Sw_nonneg (ξ : ℕ → ℤ) (h : ∀ τ, 0 ≤ ξ τ) (t n : ℕ) : 0 ≤ Sw ξ t n :=
  sum_nonneg (fun i _ => h (t + i))

/-- points of a window of length `Λ` that are pairwise at cyclic distance `< b`: at most `b` -/
lemma arc_card (S : Finset ℕ) (b Λ : ℕ) (hb : 0 < b) (h2b : 2 * b ≤ Λ)
    (hS : ∀ x ∈ S, x < Λ)
    (hpair : ∀ x ∈ S, ∀ y ∈ S, x < y → y - x < b ∨ Λ < y - x + b) : #S ≤ b := by
  rcases S.eq_empty_or_nonempty with he | hne
  · rw [he]; simp
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = S.min' hne := ⟨_, rfl⟩
  have hρS : ρ ∈ S := hρ ▸ S.min'_mem hne
  have hρle : ∀ x ∈ S, ρ ≤ x := fun x hx => hρ ▸ S.min'_le x hx
  let f : ℕ → ℕ := fun x => if x - ρ < b then x - ρ else x - ρ + b - Λ
  have hfar : ∀ x ∈ S, ¬ x - ρ < b → Λ < x - ρ + b := by
    intro x hx hnb
    have h1 := hρle x hx
    have h2 : ρ < x := by omega
    rcases hpair ρ hρS x hx h2 with h3 | h3
    · exact absurd h3 hnb
    · exact h3
  have hmaps : Set.MapsTo f ↑S ↑(range b) := by
    intro x hx
    have hxS : x ∈ S := mem_coe.mp hx
    simp only [coe_range, Set.mem_Iio, f]
    split_ifs with h1
    · exact h1
    · have := hfar x hxS h1
      have := hS x hxS
      omega
  have hinj : Set.InjOn f ↑S := by
    intro x hx y hy hxy
    have hxS : x ∈ S := mem_coe.mp hx
    have hyS : y ∈ S := mem_coe.mp hy
    have hx1 := hρle x hxS
    have hy1 := hρle y hyS
    have hx2 := hS x hxS
    have hy2 := hS y hyS
    simp only [f] at hxy
    by_cases h1 : x - ρ < b <;> by_cases h2 : y - ρ < b
    · rw [if_pos h1, if_pos h2] at hxy; omega
    · rw [if_pos h1, if_neg h2] at hxy
      have h3 := hfar y hyS h2
      exfalso
      have hlt : x < y := by omega
      rcases hpair x hxS y hyS hlt with h4 | h4 <;> omega
    · rw [if_neg h1, if_pos h2] at hxy
      have h3 := hfar x hxS h1
      exfalso
      have hlt : y < x := by omega
      rcases hpair y hyS x hxS hlt with h4 | h4 <;> omega
    · rw [if_neg h1, if_neg h2] at hxy
      have h3 := hfar x hxS h1
      have h4 := hfar y hyS h2
      omega
  have := card_le_card_of_injOn f hmaps hinj
  rwa [card_range] at this

theorem no_xi (ξ : ℕ → ℤ) (a : ℕ) (M m0 : ℤ) (ha : 1 ≤ a)
    (hnn : ∀ τ, 0 ≤ ξ τ) (hev : ∀ τ, ξ τ ≠ 0 → 2 ≤ ξ τ)
    (hmass : ∀ t, Sw ξ t (4 * a) = M) (hM1 : M < 2 * m0) (hM2 : M < 4 * a - 2)
    (hzero : ∀ σ, ξ (a + 1 + σ) = 0 → (m0 ≤ Sw ξ (a + 1 + σ + 1) a ∨ m0 ≤ Sw ξ σ (a + 1))) :
    False := by
  obtain ⟨Λ, hΛ⟩ : ∃ Λ, Λ = 4 * a := ⟨_, rfl⟩
  rw [← hΛ] at hmass
  obtain ⟨Zs, hZs⟩ : ∃ Zs : Finset ℕ, Zs = (range Λ).filter (fun σ => ξ (a + 1 + σ) = 0) :=
    ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : Finset ℕ, R = Zs.filter (fun σ => m0 ≤ Sw ξ (a + 1 + σ + 1) a) :=
    ⟨_, rfl⟩
  obtain ⟨Lz, hLz⟩ : ∃ Lz : Finset ℕ, Lz = Zs.filter (fun σ => ¬ m0 ≤ Sw ξ (a + 1 + σ + 1) a) :=
    ⟨_, rfl⟩
  have hcardZ : #R + #Lz = #Zs := by
    rw [hR, hLz]
    exact card_filter_add_card_filter_not _
  -- R: pairwise close
  have hRle : #R ≤ a := by
    apply arc_card R a Λ (by omega) (by omega)
    · intro x hx
      rw [hR, hZs] at hx
      simp only [mem_filter, mem_range] at hx
      exact hx.1.1
    · intro x hx y hy hxy
      rw [hR, hZs] at hx hy
      simp only [mem_filter, mem_range] at hx hy
      by_contra hcon
      rw [not_or, not_lt, not_lt] at hcon
      obtain ⟨d, hd⟩ : ∃ d, y = x + d := ⟨y - x, by omega⟩
      have hda : a ≤ d := by omega
      have hdΛ : d + a ≤ Λ := by omega
      have e : Sw ξ (a + 1 + x + 1) Λ = Sw ξ (a + 1 + x + 1) a + Sw ξ (a + 1 + x + 1 + a) (d - a)
          + Sw ξ (a + 1 + y + 1) a + Sw ξ (a + 1 + y + 1 + a) (Λ - d - a) := by
        rw [show Λ = a + (d - a) + a + (Λ - d - a) by omega, Sw_add, Sw_add, Sw_add,
          show a + 1 + x + 1 + (a + (d - a)) = a + 1 + y + 1 by omega,
          show a + (d - a) + a + (Λ - d - a) = Λ by omega,
          show a + 1 + x + 1 + (a + (d - a) + a) = a + 1 + y + 1 + a by omega]
      have n1 := Sw_nonneg ξ hnn (a + 1 + x + 1 + a) (d - a)
      have n2 := Sw_nonneg ξ hnn (a + 1 + y + 1 + a) (Λ - d - a)
      have := hmass (a + 1 + x + 1)
      have := hx.2
      have := hy.2
      linarith
  -- Lz: pairwise close
  have hLle : #Lz ≤ a + 1 := by
    apply arc_card Lz (a + 1) Λ (by omega) (by omega)
    · intro x hx
      rw [hLz, hZs] at hx
      simp only [mem_filter, mem_range] at hx
      exact hx.1.1
    · intro x hx y hy hxy
      rw [hLz, hZs] at hx hy
      simp only [mem_filter, mem_range] at hx hy
      have lx : m0 ≤ Sw ξ x (a + 1) := by
        rcases hzero x hx.1.2 with h1 | h1
        · exact absurd h1 hx.2
        · exact h1
      have ly : m0 ≤ Sw ξ y (a + 1) := by
        rcases hzero y hy.1.2 with h1 | h1
        · exact absurd h1 hy.2
        · exact h1
      by_contra hcon
      rw [not_or, not_lt, not_lt] at hcon
      obtain ⟨d, hd⟩ : ∃ d, y = x + d := ⟨y - x, by omega⟩
      have hda : a + 1 ≤ d := by omega
      have hdΛ : d + (a + 1) ≤ Λ := by omega
      have e : Sw ξ x Λ = Sw ξ x (a + 1) + Sw ξ (x + (a + 1)) (d - (a + 1))
          + Sw ξ y (a + 1) + Sw ξ (y + (a + 1)) (Λ - d - (a + 1)) := by
        rw [show Λ = (a + 1) + (d - (a + 1)) + (a + 1) + (Λ - d - (a + 1)) by omega, Sw_add,
          Sw_add, Sw_add,
          show x + (a + 1 + (d - (a + 1))) = y by omega,
          show (a + 1) + (d - (a + 1)) + (a + 1) + (Λ - d - (a + 1)) = Λ by omega,
          show x + (a + 1 + (d - (a + 1)) + (a + 1)) = y + (a + 1) by omega]
      have n1 := Sw_nonneg ξ hnn (x + (a + 1)) (d - (a + 1))
      have n2 := Sw_nonneg ξ hnn (y + (a + 1)) (Λ - d - (a + 1))
      have := hmass x
      linarith
  -- many zeros
  have hsum : (2 : ℤ) * (Λ - #Zs) ≤ M := by
    have h1 := hmass (a + 1)
    rw [Sw] at h1
    have h2 : ∑ σ ∈ range Λ, (if ξ (a + 1 + σ) = 0 then (0 : ℤ) else 2) ≤ ∑ σ ∈ range Λ, ξ (a + 1 + σ) := by
      apply sum_le_sum
      intro σ _
      split_ifs with h0
      · rw [h0]
      · exact hev _ h0
    have h3 : ∑ σ ∈ range Λ, (if ξ (a + 1 + σ) = 0 then (0 : ℤ) else 2)
        = 2 * ((Λ : ℤ) - #Zs) := by
      have h4 : ∀ σ ∈ range Λ, (if ξ (a + 1 + σ) = 0 then (0 : ℤ) else 2)
          = 2 - 2 * (if ξ (a + 1 + σ) = 0 then (1 : ℤ) else 0) := by
        intro σ _
        split_ifs <;> norm_num
      rw [sum_congr rfl h4, sum_sub_distrib, ← mul_sum, hZs, card_filter]
      simp
      ring
    linarith
  have hZle : (#Zs : ℤ) ≤ 2 * a + 1 := by
    have : #Zs ≤ 2 * a + 1 := by omega
    exact_mod_cast this
  have hΛz : (Λ : ℤ) = 4 * a := by exact_mod_cast hΛ
  linarith

end Coil

#print axioms Coil.no_xi
