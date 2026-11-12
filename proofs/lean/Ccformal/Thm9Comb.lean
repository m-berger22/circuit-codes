import Ccformal.Thm9Step

/-!
# Theorem 9, Step 2': no sequence with `Xi9 a ξ` exists for `a ≥ 6`

Two cases.  (Bipolar) two disjoint windows of length `ℓ ∈ {a, a+1}` carry mass `≥ 2a` each: then everything else is zero
and each of the two gaps has at most 4 positions (`bipolar_gap`), so `4a ≤ 2ℓ + 8`.
(Otherwise) zeros with a heavy right window are pairwise close, likewise those with a heavy left window (`arc_card`):
at most `2a+1` zeros; for the last left-type zero `y₀` the `a` positions before it hold `≥ a-1` zeros, so the other
`3a-1` positions of the period hold `≥ 2a-3` nonzero values, mass `≥ 4a-6`, while the window of `y₀` has mass `≥ 2a`.
-/

open Finset

namespace Coil

set_option linter.deprecated false
set_option linter.unusedVariables false

lemma Sw_one (ξ : ℕ → ℤ) (t : ℕ) : Sw ξ t 1 = ξ t := by simp [Sw]

lemma Sw_split3 (ξ : ℕ → ℤ) (hnn : ∀ τ, 0 ≤ ξ τ) (A w n B : ℕ) (h1 : A ≤ w) (h2 : w + n ≤ B) :
    Sw ξ w n ≤ Sw ξ A (B - A) := by
  have e : Sw ξ A (B - A) = Sw ξ A (w - A) + Sw ξ w n + Sw ξ (w + n) (B - (w + n)) := by
    rw [show B - A = (w - A) + n + (B - (w + n)) by omega, Sw_add, Sw_add,
      show A + (w - A) = w by omega, show A + (w - A + n) = w + n by omega]
  have n1 := Sw_nonneg ξ hnn A (w - A)
  have n2 := Sw_nonneg ξ hnn (w + n) (B - (w + n))
  linarith

/-- the options at a zero `τ ≥ a+1`, in `τ`-form -/
lemma Xi9.opt' {a : ℕ} {ξ : ℕ → ℤ} (X : Xi9 a ξ) (τ : ℕ) (hτ : a + 1 ≤ τ) (h0 : ξ τ = 0) :
    (2 * (a : ℤ) ≤ Sw ξ (τ + 1) a ∧ ξ (τ + a + 1) ≠ 0) ∨
    (2 * (a : ℤ) ≤ Sw ξ (τ + 1) a ∧ ξ (τ + 1) ≠ 0) ∨
    (2 * (a : ℤ) + 2 ≤ Sw ξ (τ + 1) a) ∨
    (2 * (a : ℤ) ≤ Sw ξ (τ - a) a ∧ ξ (τ - a) ≠ 0) ∨
    (2 * (a : ℤ) + 2 ≤ Sw ξ (τ - a) a) ∨
    (2 * (a : ℤ) ≤ Sw ξ (τ - a - 1) (a + 1) ∧ ξ (τ - a - 1) ≠ 0) := by
  obtain ⟨σ, hσ⟩ : ∃ σ, τ = a + 1 + σ := ⟨τ - (a + 1), by omega⟩
  have := X.opt σ (by rw [← hσ]; exact h0)
  rw [← hσ] at this
  rw [show τ - a - 1 = σ by omega, show τ - a = σ + 1 by omega]
  exact this

lemma Xi9.per {a : ℕ} {ξ : ℕ → ℤ} (X : Xi9 a ξ) (t : ℕ) : ξ (t + 4 * a) = ξ t := by
  have h1 := Sw_add ξ t 1 (4 * a)
  have h2 := Sw_add ξ t (4 * a) 1
  rw [show 1 + 4 * a = 4 * a + 1 by ring, h2, X.mass, X.mass, Sw_one, Sw_one] at h1
  linarith

lemma Xi9.two {a : ℕ} {ξ : ℕ → ℤ} (X : Xi9 a ξ) (t : ℕ) (h : ξ t ≠ 0) : 2 ≤ ξ t := by
  obtain ⟨z, hz⟩ := X.ev t
  have := X.nn t
  omega

/-- **Gap lemma.** Two disjoint heavy windows: the gap after the first has at most 4 positions. -/
lemma bipolar_gap {a : ℕ} {ξ : ℕ → ℤ} (X : Xi9 a ξ) (ha : 1 ≤ a) (A1 A2 ℓ : ℕ) (hA1 : a + 1 ≤ A1)
    (hℓ1 : a ≤ ℓ) (hℓ2 : ℓ ≤ a + 1) (h12 : A1 + ℓ ≤ A2) (h21 : A2 + ℓ ≤ A1 + 4 * a)
    (m1 : 2 * (a : ℤ) ≤ Sw ξ A1 ℓ) (m2 : 2 * (a : ℤ) ≤ Sw ξ A2 ℓ) : A2 ≤ A1 + ℓ + 4 := by
  by_contra hcon
  rw [not_le] at hcon
  have hnn := X.nn
  -- the period splits into W1, G1, W2, G2
  have e : Sw ξ A1 (4 * a) = Sw ξ A1 ℓ + Sw ξ (A1 + ℓ) (A2 - (A1 + ℓ)) + Sw ξ A2 ℓ
      + Sw ξ (A2 + ℓ) (A1 + 4 * a - (A2 + ℓ)) := by
    rw [show 4 * a = ℓ + (A2 - (A1 + ℓ)) + ℓ + (A1 + 4 * a - (A2 + ℓ)) by omega, Sw_add, Sw_add,
      Sw_add, show A1 + (ℓ + (A2 - (A1 + ℓ))) = A2 by omega,
      show A1 + (ℓ + (A2 - (A1 + ℓ)) + ℓ) = A2 + ℓ by omega,
      show ℓ + (A2 - (A1 + ℓ)) + ℓ + (A1 + 4 * a - (A2 + ℓ)) = 4 * a by omega]
  have hm := X.mass A1
  have g1 := Sw_nonneg ξ hnn (A1 + ℓ) (A2 - (A1 + ℓ))
  have g2 := Sw_nonneg ξ hnn (A2 + ℓ) (A1 + 4 * a - (A2 + ℓ))
  have hW1 : Sw ξ A1 ℓ = 2 * a := by linarith
  have hG1 : Sw ξ (A1 + ℓ) (A2 - (A1 + ℓ)) = 0 := by linarith
  have hW2 : Sw ξ A2 ℓ = 2 * a := by linarith
  have hG2 : Sw ξ (A2 + ℓ) (A1 + 4 * a - (A2 + ℓ)) = 0 := by linarith
  -- (K1): windows inside [A1, A2) have mass ≤ 2a;  (K2): windows inside [A1+ℓ, A1+4a) too
  have K1 : ∀ w n, A1 ≤ w → w + n ≤ A2 → Sw ξ w n ≤ 2 * a := by
    intro w n h1 h2
    have := Sw_split3 ξ hnn A1 w n A2 h1 h2
    have e1 : Sw ξ A1 (A2 - A1) = Sw ξ A1 ℓ + Sw ξ (A1 + ℓ) (A2 - (A1 + ℓ)) := by
      rw [show A2 - A1 = ℓ + (A2 - (A1 + ℓ)) by omega, Sw_add]
    linarith
  have K2 : ∀ w n, A1 + ℓ ≤ w → w + n ≤ A1 + 4 * a → Sw ξ w n ≤ 2 * a := by
    intro w n h1 h2
    have := Sw_split3 ξ hnn (A1 + ℓ) w n (A1 + 4 * a) h1 h2
    have e1 : Sw ξ (A1 + ℓ) (A1 + 4 * a - (A1 + ℓ)) = Sw ξ (A1 + ℓ) (A2 - (A1 + ℓ)) + Sw ξ A2 ℓ
        + Sw ξ (A2 + ℓ) (A1 + 4 * a - (A2 + ℓ)) := by
      rw [show A1 + 4 * a - (A1 + ℓ) = (A2 - (A1 + ℓ)) + ℓ + (A1 + 4 * a - (A2 + ℓ)) by omega,
        Sw_add, Sw_add, show A1 + ℓ + (A2 - (A1 + ℓ)) = A2 by omega,
        show A1 + ℓ + (A2 - (A1 + ℓ) + ℓ) = A2 + ℓ by omega]
    linarith
  -- gap positions are zeros
  have hz : ∀ τ, A1 + ℓ ≤ τ → τ < A2 → ξ τ = 0 := by
    intro τ h1 h2
    have := Sw_split3 ξ hnn (A1 + ℓ) τ 1 A2 h1 (by omega)
    rw [Sw_one, hG1] at this
    have := hnn τ
    linarith
  -- an interior gap zero needs an L1 / L3 window starting at a nonzero point
  have key : ∀ τ, A1 + ℓ + 1 ≤ τ → τ + 2 ≤ A2 →
      ∃ w, (w = τ - a ∨ w = τ - a - 1) ∧ ξ w ≠ 0 ∧ 2 * (a : ℤ) ≤ Sw ξ w (τ - w) := by
    intro τ h1 h2
    rcases X.opt' τ (by omega) (hz τ (by omega) (by omega)) with
      ⟨r1, r2⟩ | ⟨r1, r2⟩ | r1 | ⟨l1, l2⟩ | l1 | ⟨l1, l2⟩
    · exfalso
      have h3 := K2 (τ + 1) (a + 1) (by omega) (by omega)
      rw [Sw_add, Sw_one, show τ + 1 + a = τ + a + 1 by ring] at h3
      have := X.two _ r2
      linarith
    · exfalso
      exact r2 (hz (τ + 1) (by omega) (by omega))
    · exfalso
      have h3 := K2 (τ + 1) a (by omega) (by omega)
      linarith
    · exact ⟨τ - a, Or.inl rfl, l2, by rw [show τ - (τ - a) = a by omega]; exact l1⟩
    · exfalso
      have h3 := K1 (τ - a) a (by omega) (by omega)
      linarith
    · exact ⟨τ - a - 1, Or.inr rfl, l2, by rw [show τ - (τ - a - 1) = a + 1 by omega]; exact l1⟩
  obtain ⟨w1, hw1, n1, s1⟩ := key (A1 + ℓ + 1) (by omega) (by omega)
  obtain ⟨w3, hw3, n3, s3⟩ := key (A1 + ℓ + 3) (by omega) (by omega)
  have hlt : w1 < w3 := by omega
  have hA : A1 ≤ w1 := by omega
  have k1 := K1 w1 (A1 + ℓ + 3 - w1) hA (by omega)
  have e2 : Sw ξ w1 (A1 + ℓ + 3 - w1) = ξ w1 + Sw ξ (w1 + 1) (w3 - (w1 + 1))
      + Sw ξ w3 (A1 + ℓ + 3 - w3) := by
    rw [show A1 + ℓ + 3 - w1 = 1 + (w3 - (w1 + 1)) + (A1 + ℓ + 3 - w3) by omega, Sw_add, Sw_add,
      Sw_one, show w1 + (1 + (w3 - (w1 + 1))) = w3 by omega]
  have n2 := Sw_nonneg ξ hnn (w1 + 1) (w3 - (w1 + 1))
  have := X.two _ n1
  linarith

lemma Sw_per {a : ℕ} {ξ : ℕ → ℤ} (X : Xi9 a ξ) (t n : ℕ) : Sw ξ (t + 4 * a) n = Sw ξ t n := by
  simp only [Sw]
  apply sum_congr rfl
  intro i _
  rw [show t + 4 * a + i = t + i + 4 * a by ring, X.per]

/-- two disjoint heavy windows of the same length `ℓ ∈ {a, a+1}` are impossible for `a ≥ 6` -/
lemma no_bipolar {a : ℕ} {ξ : ℕ → ℤ} (X : Xi9 a ξ) (ha : 6 ≤ a) (A1 A2 ℓ : ℕ) (hA1 : a + 1 ≤ A1)
    (hℓ1 : a ≤ ℓ) (hℓ2 : ℓ ≤ a + 1) (h12 : A1 + ℓ ≤ A2) (h21 : A2 + ℓ ≤ A1 + 4 * a)
    (m1 : 2 * (a : ℤ) ≤ Sw ξ A1 ℓ) (m2 : 2 * (a : ℤ) ≤ Sw ξ A2 ℓ) : False := by
  have g1 := bipolar_gap X (by omega) A1 A2 ℓ hA1 hℓ1 hℓ2 h12 h21 m1 m2
  have m1' : 2 * (a : ℤ) ≤ Sw ξ (A1 + 4 * a) ℓ := by rw [Sw_per X]; exact m1
  have g2 := bipolar_gap X (by omega) A2 (A1 + 4 * a) ℓ (by omega) hℓ1 hℓ2 h21 (by omega) m2 m1'
  omega

lemma Sw_ge_nonzero {a : ℕ} {ξ : ℕ → ℤ} (X : Xi9 a ξ) (t n : ℕ) :
    2 * ((n : ℤ) - (Fw (fun t => ξ t = 0) t n : ℕ)) ≤ Sw ξ t n := by
  rw [Sw, Fw, card_filter]
  have h : ∀ i ∈ range n, (2 : ℤ) - 2 * (if ξ (t + i) = 0 then (1 : ℤ) else 0) ≤ ξ (t + i) := by
    intro i _
    by_cases h0 : ξ (t + i) = 0
    · rw [if_pos h0, h0]; norm_num
    · rw [if_neg h0]
      have := X.two _ h0
      linarith
  have h2 := sum_le_sum h
  rw [sum_sub_distrib, ← mul_sum] at h2
  simp only [sum_const, card_range, nsmul_eq_mul] at h2
  push_cast
  linarith

lemma zeros_per_period {a : ℕ} {ξ : ℕ → ℤ} (X : Xi9 a ξ) (j : ℕ) :
    Fw (fun t => ξ t = 0) j (4 * a) = Fw (fun t => ξ t = 0) 0 (4 * a) := by
  rw [Fw, Fw, card_filter, card_filter]
  have hper : ∀ i, (if ξ (i + 4 * a) = 0 then 1 else 0) = (if ξ i = 0 then 1 else 0) := by
    intro i; rw [X.per]
  have h := sum_shift (fun i => if ξ i = 0 then 1 else 0) (4 * a) hper j
  simp only [zero_add]
  rw [← h]
  apply sum_congr rfl
  intro i _
  rw [add_comm]

set_option maxHeartbeats 3200000 in
/-- **Step 2' of Theorem 9**: no sequence satisfies `Xi9 a ξ` when `a ≥ 6`. -/
theorem no_xi9 {a : ℕ} {ξ : ℕ → ℤ} (X : Xi9 a ξ) (ha : 6 ≤ a) : False := by
  have hnn := X.nn
  obtain ⟨Λ, hΛ⟩ : ∃ Λ, Λ = 4 * a := ⟨_, rfl⟩
  obtain ⟨Zs, hZs⟩ : ∃ Zs : Finset ℕ, Zs = (range Λ).filter (fun σ => ξ (Λ + σ) = 0) := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : Finset ℕ,
      R = Zs.filter (fun σ => 2 * (a : ℤ) ≤ Sw ξ (Λ + σ + 1) a) := ⟨_, rfl⟩
  obtain ⟨Lz, hLz⟩ : ∃ Lz : Finset ℕ,
      Lz = Zs.filter (fun σ => ¬ 2 * (a : ℤ) ≤ Sw ξ (Λ + σ + 1) a) := ⟨_, rfl⟩
  have hcardZ : #R + #Lz = #Zs := by
    rw [hR, hLz]
    exact card_filter_add_card_filter_not _
  have memR : ∀ σ, σ ∈ R ↔ σ < Λ ∧ ξ (Λ + σ) = 0 ∧ 2 * (a : ℤ) ≤ Sw ξ (Λ + σ + 1) a := by
    intro σ
    rw [hR, hZs]
    simp only [mem_filter, mem_range]
    tauto
  have memL : ∀ σ, σ ∈ Lz ↔ σ < Λ ∧ ξ (Λ + σ) = 0 ∧ ¬ 2 * (a : ℤ) ≤ Sw ξ (Λ + σ + 1) a := by
    intro σ
    rw [hLz, hZs]
    simp only [mem_filter, mem_range]
    tauto
  -- left windows of L-zeros
  have hLw : ∀ σ ∈ Lz, 2 * (a : ℤ) ≤ Sw ξ (Λ + σ - a - 1) (a + 1) := by
    intro σ hσ
    obtain ⟨h1, h2, h3⟩ := (memL σ).mp hσ
    have e : Sw ξ (Λ + σ - a - 1) (a + 1) = ξ (Λ + σ - a - 1) + Sw ξ (Λ + σ - a) a := by
      rw [show a + 1 = 1 + a by ring, Sw_add, Sw_one, show Λ + σ - a - 1 + 1 = Λ + σ - a by omega]
    have hp := hnn (Λ + σ - a - 1)
    rcases X.opt' (Λ + σ) (by omega) h2 with ⟨r1, _⟩ | ⟨r1, _⟩ | r1 | ⟨l1, _⟩ | l1 | ⟨l1, _⟩
    · exact absurd r1 h3
    · exact absurd r1 h3
    · exact absurd (by linarith) h3
    · rw [e]; linarith
    · rw [e]; linarith
    · exact l1
  -- pairwise closeness (otherwise: bipolar)
  have hRpair : ∀ x ∈ R, ∀ y ∈ R, x < y → y - x < a ∨ Λ < y - x + a := by
    intro x hx y hy hxy
    obtain ⟨x1, x2, x3⟩ := (memR x).mp hx
    obtain ⟨y1, y2, y3⟩ := (memR y).mp hy
    by_contra hcon
    rw [not_or, not_lt, not_lt] at hcon
    exact no_bipolar X ha (Λ + x + 1) (Λ + y + 1) a (by omega) (le_refl _) (by omega) (by omega)
      (by omega) x3 y3
  have hLpair : ∀ x ∈ Lz, ∀ y ∈ Lz, x < y → y - x < a + 1 ∨ Λ < y - x + (a + 1) := by
    intro x hx y hy hxy
    have x3 := hLw x hx
    have y3 := hLw y hy
    have x1 := ((memL x).mp hx).1
    have y1 := ((memL y).mp hy).1
    by_contra hcon
    rw [not_or, not_lt, not_lt] at hcon
    exact no_bipolar X ha (Λ + x - a - 1) (Λ + y - a - 1) (a + 1) (by omega) (by omega) (le_refl _)
      (by omega) (by omega) x3 y3
  have hRle : #R ≤ a :=
    arc_card R a Λ (by omega) (by omega) (fun x hx => ((memR x).mp hx).1) hRpair
  have hLle : #Lz ≤ a + 1 :=
    arc_card Lz (a + 1) Λ (by omega) (by omega) (fun x hx => ((memL x).mp hx).1) hLpair
  -- many zeros
  have hsum : (2 : ℤ) * (Λ - #Zs) ≤ 4 * a := by
    have h1 := X.mass Λ
    rw [Sw, ← hΛ] at h1
    have h2 : ∑ σ ∈ range Λ, (if ξ (Λ + σ) = 0 then (0 : ℤ) else 2) ≤ ∑ σ ∈ range Λ, ξ (Λ + σ) := by
      apply sum_le_sum
      intro σ _
      split_ifs with h0
      · rw [h0]
      · exact X.two _ h0
    have h3 : ∑ σ ∈ range Λ, (if ξ (Λ + σ) = 0 then (0 : ℤ) else 2) = 2 * ((Λ : ℤ) - #Zs) := by
      have h4 : ∀ σ ∈ range Λ, (if ξ (Λ + σ) = 0 then (0 : ℤ) else 2)
          = 2 - 2 * (if ξ (Λ + σ) = 0 then (1 : ℤ) else 0) := by
        intro σ _
        split_ifs <;> norm_num
      rw [sum_congr rfl h4, sum_sub_distrib, ← mul_sum, hZs, card_filter]
      simp
      ring
    linarith
  have hZge : 2 * a ≤ #Zs := by
    have hΛz : (Λ : ℤ) = 4 * a := by exact_mod_cast hΛ
    have : (2 * a : ℤ) ≤ #Zs := by linarith
    exact_mod_cast this
  have hLa : a ≤ #Lz := by omega
  have hZle : #Zs ≤ 2 * a + 1 := by omega
  -- the last L-zero
  have hne : Lz.Nonempty := card_pos.mp (by omega)
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = Lz.min' hne := ⟨_, rfl⟩
  have hρL : ρ ∈ Lz := hρ ▸ Lz.min'_mem hne
  have hρle : ∀ x ∈ Lz, ρ ≤ x := fun x hx => hρ ▸ Lz.min'_le x hx
  obtain ⟨Nn, hNn⟩ : ∃ Nn : Finset ℕ, Nn = Lz.filter (fun x => x - ρ ≤ a) := ⟨_, rfl⟩
  have hNne : Nn.Nonempty := ⟨ρ, by rw [hNn]; exact mem_filter.mpr ⟨hρL, by omega⟩⟩
  obtain ⟨y0, hy0⟩ : ∃ y0, y0 = Nn.max' hNne := ⟨_, rfl⟩
  have hy0N : y0 ∈ Nn := hy0 ▸ Nn.max'_mem hNne
  have hy0L : y0 ∈ Lz := by rw [hNn] at hy0N; exact (mem_filter.mp hy0N).1
  have hy0ρ : y0 - ρ ≤ a := by rw [hNn] at hy0N; exact (mem_filter.mp hy0N).2
  have hy0max : ∀ x ∈ Lz, x - ρ ≤ a → x ≤ y0 := by
    intro x hx h1
    rw [hy0]
    exact Nn.le_max' x (by rw [hNn]; exact mem_filter.mpr ⟨hx, h1⟩)
  have hy0lt : y0 < Λ := ((memL y0).mp hy0L).1
  have hρy0 : ρ ≤ y0 := hρle y0 hy0L
  -- every other L-zero sits (cyclically) in the a positions before y0
  have fact : ∀ x ∈ Lz, x ≠ y0 →
      (x < y0 ∧ y0 - x ≤ a) ∨ (y0 < x ∧ Λ ≤ x - y0 + a ∧ x < Λ) := by
    intro x hx hxy
    have hxΛ := ((memL x).mp hx).1
    have hρx := hρle x hx
    rcases Nat.lt_or_gt_of_ne hxy with hlt | hgt
    · left
      exact ⟨hlt, by omega⟩
    · right
      have hnot : ¬ x - ρ ≤ a := fun h1 => by
        have := hy0max x hx h1
        omega
      have hρx' : ρ < x := by omega
      rcases hLpair ρ hρL x hx hρx' with h1 | h1
      · omega
      · rcases hLpair y0 hy0L x hx hgt with h2 | h2
        · omega
        · exact ⟨hgt, by omega, hxΛ⟩
  obtain ⟨Dz, hDz⟩ : ∃ Dz : Finset ℕ,
      Dz = (range a).filter (fun i => ξ (Λ + y0 - a + i) = 0) := ⟨_, rfl⟩
  have hinj : #(Lz.erase y0) ≤ #Dz := by
    apply card_le_card_of_injOn (fun x => if x < y0 then a + x - y0 else a + x - y0 - Λ)
    · intro x hx
      have hx' := mem_coe.mp hx
      have hxL := mem_of_mem_erase hx'
      have hxne := ne_of_mem_erase hx'
      have hz := ((memL x).mp hxL).2.1
      rw [hDz]
      simp only [coe_filter, mem_range, Set.mem_setOf_eq]
      rcases fact x hxL hxne with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
      · rw [if_pos h1]
        refine ⟨by omega, ?_⟩
        rw [show Λ + y0 - a + (a + x - y0) = Λ + x by omega]
        exact hz
      · rw [if_neg (by omega)]
        refine ⟨by omega, ?_⟩
        rw [show Λ + y0 - a + (a + x - y0 - Λ) = x by omega]
        have := X.per x
        rw [show x + 4 * a = Λ + x by omega] at this
        rw [← this]
        exact hz
    · intro x hx y hy hxy
      have hx' := mem_coe.mp hx
      have hy' := mem_coe.mp hy
      have fx := fact x (mem_of_mem_erase hx') (ne_of_mem_erase hx')
      have fy := fact y (mem_of_mem_erase hy') (ne_of_mem_erase hy')
      simp only at hxy
      rcases fx with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ <;> rcases fy with ⟨k1, k2⟩ | ⟨k1, k2, k3⟩
      · rw [if_pos h1, if_pos k1] at hxy; omega
      · rw [if_pos h1, if_neg (by omega)] at hxy; omega
      · rw [if_neg (by omega), if_pos k1] at hxy; omega
      · rw [if_neg (by omega), if_neg (by omega)] at hxy; omega
  have hDzge : a ≤ #Dz + 1 := by
    have := card_erase_of_mem hy0L
    omega
  -- zeros and mass in the period starting at P0 = Λ + y0 - a - 1
  obtain ⟨P0, hP0⟩ : ∃ P0, P0 = Λ + y0 - a - 1 := ⟨_, rfl⟩
  have hzP : Fw (fun t => ξ t = 0) P0 Λ = #Zs := by
    rw [hΛ, zeros_per_period X P0, ← zeros_per_period X Λ, ← hΛ, hZs, Fw]
  have hsplit : Fw (fun t => ξ t = 0) P0 Λ = Fw (fun t => ξ t = 0) P0 1
      + Fw (fun t => ξ t = 0) (P0 + 1) a + Fw (fun t => ξ t = 0) (P0 + 1 + a) (Λ - a - 1) := by
    rw [show Λ = 1 + a + (Λ - a - 1) by omega, Fw_add, Fw_add,
      show 1 + a + (Λ - a - 1) = Λ by omega, show P0 + (1 + a) = P0 + 1 + a by ring]
  have hmid : Fw (fun t => ξ t = 0) (P0 + 1) a = #Dz := by
    rw [hDz, show P0 + 1 = Λ + y0 - a by omega, Fw]
  have hrest := Sw_ge_nonzero X (P0 + 1 + a) (Λ - a - 1)
  have hwin := hLw y0 hy0L
  rw [← hP0] at hwin
  have htot := X.mass P0
  rw [show 4 * a = (a + 1) + (Λ - a - 1) by omega, Sw_add,
    show P0 + (a + 1) = P0 + 1 + a by ring] at htot
  have hzrest : (Fw (fun t => ξ t = 0) (P0 + 1 + a) (Λ - a - 1) : ℤ) ≤ (a : ℤ) + 2 := by
    have : Fw (fun t => ξ t = 0) (P0 + 1 + a) (Λ - a - 1) ≤ a + 2 := by omega
    exact_mod_cast this
  have hcast : ((Λ - a - 1 : ℕ) : ℤ) = 3 * a - 1 := by
    have : Λ - a - 1 + 1 = 3 * a := by omega
    have h' : ((Λ - a - 1 + 1 : ℕ) : ℤ) = ((3 * a : ℕ) : ℤ) := by rw [this]
    push_cast at h'
    linarith
  rw [hcast] at hrest
  have haz : (6 : ℤ) ≤ a := by exact_mod_cast ha
  linarith

end Coil

#print axioms Coil.no_xi9
