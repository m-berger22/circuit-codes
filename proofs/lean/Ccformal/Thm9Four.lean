import Ccformal.Thm9Comb

/-!
# Theorem 9, Step 2', for `a = 4` (the line `l = 7`)

`no_xi9` (Thm9Comb.lean) needs `a ≥ 6` only through `no_bipolar` (two disjoint heavy windows). For `a = 4` the gap lemma
leaves four bipolar geometries (window length 4 with gaps 4, 4; length 5 with gaps 2, 4 / 3, 3 / 4, 2); in each of them two
or three of the gap zeros already have no admissible option (found by bip4.py; here: `omega`).
-/

open Finset

namespace Coil

set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

/-- `Xi9` is invariant under shifts -/
lemma Xi9.shift {a : ℕ} {ξ : ℕ → ℤ} (X : Xi9 a ξ) (s : ℕ) : Xi9 a (fun m => ξ (s + m)) := by
  have hs : ∀ t n, Sw (fun m => ξ (s + m)) t n = Sw ξ (s + t) n := by
    intro t n
    simp only [Sw, add_assoc]
  refine ⟨fun τ => X.nn _, fun τ => X.ev _, fun t => by rw [hs]; exact X.mass _, fun σ h0 => ?_⟩
  have := X.opt (s + σ) (by rw [show a + 1 + (s + σ) = s + (a + 1 + σ) by omega]; exact h0)
  rw [show a + 1 + (s + σ) + 1 = s + (a + 1 + σ + 1) by omega,
    show a + 1 + (s + σ) + a + 1 = s + (a + 1 + σ + a + 1) by omega,
    show s + σ + 1 = s + (σ + 1) by omega] at this
  simp only [hs]
  exact this

lemma bip4_4_8 {w : ℕ → ℤ} (X : Xi9 4 w) (m1 : (8 : ℤ) ≤ Sw w 0 4) (m2 : (8 : ℤ) ≤ Sw w 8 4) : False := by
  have hp : ∀ m, w (m + 16) = w m := fun m => X.per m
  have hm := X.mass 0
  simp only [Sw, Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, Nat.reduceMul, zero_add, add_zero] at hm m1 m2
  have n0 := X.nn 0
  have n1 := X.nn 1
  have n2 := X.nn 2
  have n3 := X.nn 3
  have n4 := X.nn 4
  have n5 := X.nn 5
  have n6 := X.nn 6
  have n7 := X.nn 7
  have n8 := X.nn 8
  have n9 := X.nn 9
  have n10 := X.nn 10
  have n11 := X.nn 11
  have n12 := X.nn 12
  have n13 := X.nn 13
  have n14 := X.nn 14
  have n15 := X.nn 15
  obtain ⟨z0, e0⟩ := X.ev 0
  obtain ⟨z1, e1⟩ := X.ev 1
  obtain ⟨z2, e2⟩ := X.ev 2
  obtain ⟨z3, e3⟩ := X.ev 3
  obtain ⟨z4, e4⟩ := X.ev 4
  obtain ⟨z5, e5⟩ := X.ev 5
  obtain ⟨z6, e6⟩ := X.ev 6
  obtain ⟨z7, e7⟩ := X.ev 7
  obtain ⟨z8, e8⟩ := X.ev 8
  obtain ⟨z9, e9⟩ := X.ev 9
  obtain ⟨z10, e10⟩ := X.ev 10
  obtain ⟨z11, e11⟩ := X.ev 11
  obtain ⟨z12, e12⟩ := X.ev 12
  obtain ⟨z13, e13⟩ := X.ev 13
  obtain ⟨z14, e14⟩ := X.ev 14
  obtain ⟨z15, e15⟩ := X.ev 15
  have p16 : w 16 = w 0 := hp 0
  have p17 : w 17 = w 1 := hp 1
  have p18 : w 18 = w 2 := hp 2
  have p19 : w 19 = w 3 := hp 3
  have p20 : w 20 = w 4 := hp 4
  have p21 : w 21 = w 5 := hp 5
  have p22 : w 22 = w 6 := hp 6
  have p23 : w 23 = w 7 := hp 7
  have p24 : w 24 = w 8 := hp 8
  have p25 : w 25 = w 9 := hp 9
  have p26 : w 26 = w 10 := hp 10
  have p27 : w 27 = w 11 := hp 11
  have p28 : w 28 = w 12 := hp 12
  have p29 : w 29 = w 13 := hp 13
  have p30 : w 30 = w 14 := hp 14
  have p31 : w 31 = w 15 := hp 15
  have o4 := X.opt 15 (by show w 20 = 0; omega)
  have o6 := X.opt 1 (by show w 6 = 0; omega)
  simp only [Sw, Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, Nat.reduceMul, zero_add, add_zero] at o4 o6
  push_cast at hm o4 o6
  omega

lemma bip4_5_7 {w : ℕ → ℤ} (X : Xi9 4 w) (m1 : (8 : ℤ) ≤ Sw w 0 5) (m2 : (8 : ℤ) ≤ Sw w 7 5) : False := by
  have hp : ∀ m, w (m + 16) = w m := fun m => X.per m
  have hm := X.mass 0
  simp only [Sw, Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, Nat.reduceMul, zero_add, add_zero] at hm m1 m2
  have n0 := X.nn 0
  have n1 := X.nn 1
  have n2 := X.nn 2
  have n3 := X.nn 3
  have n4 := X.nn 4
  have n5 := X.nn 5
  have n6 := X.nn 6
  have n7 := X.nn 7
  have n8 := X.nn 8
  have n9 := X.nn 9
  have n10 := X.nn 10
  have n11 := X.nn 11
  have n12 := X.nn 12
  have n13 := X.nn 13
  have n14 := X.nn 14
  have n15 := X.nn 15
  obtain ⟨z0, e0⟩ := X.ev 0
  obtain ⟨z1, e1⟩ := X.ev 1
  obtain ⟨z2, e2⟩ := X.ev 2
  obtain ⟨z3, e3⟩ := X.ev 3
  obtain ⟨z4, e4⟩ := X.ev 4
  obtain ⟨z5, e5⟩ := X.ev 5
  obtain ⟨z6, e6⟩ := X.ev 6
  obtain ⟨z7, e7⟩ := X.ev 7
  obtain ⟨z8, e8⟩ := X.ev 8
  obtain ⟨z9, e9⟩ := X.ev 9
  obtain ⟨z10, e10⟩ := X.ev 10
  obtain ⟨z11, e11⟩ := X.ev 11
  obtain ⟨z12, e12⟩ := X.ev 12
  obtain ⟨z13, e13⟩ := X.ev 13
  obtain ⟨z14, e14⟩ := X.ev 14
  obtain ⟨z15, e15⟩ := X.ev 15
  have p16 : w 16 = w 0 := hp 0
  have p17 : w 17 = w 1 := hp 1
  have p18 : w 18 = w 2 := hp 2
  have p19 : w 19 = w 3 := hp 3
  have p20 : w 20 = w 4 := hp 4
  have p21 : w 21 = w 5 := hp 5
  have p22 : w 22 = w 6 := hp 6
  have p23 : w 23 = w 7 := hp 7
  have p24 : w 24 = w 8 := hp 8
  have p25 : w 25 = w 9 := hp 9
  have p26 : w 26 = w 10 := hp 10
  have p27 : w 27 = w 11 := hp 11
  have p28 : w 28 = w 12 := hp 12
  have p29 : w 29 = w 13 := hp 13
  have p30 : w 30 = w 14 := hp 14
  have p31 : w 31 = w 15 := hp 15
  have o12 := X.opt 7 (by show w 12 = 0; omega)
  have o14 := X.opt 9 (by show w 14 = 0; omega)
  simp only [Sw, Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, Nat.reduceMul, zero_add, add_zero] at o12 o14
  push_cast at hm o12 o14
  omega

lemma bip4_5_8 {w : ℕ → ℤ} (X : Xi9 4 w) (m1 : (8 : ℤ) ≤ Sw w 0 5) (m2 : (8 : ℤ) ≤ Sw w 8 5) : False := by
  have hp : ∀ m, w (m + 16) = w m := fun m => X.per m
  have hm := X.mass 0
  simp only [Sw, Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, Nat.reduceMul, zero_add, add_zero] at hm m1 m2
  have n0 := X.nn 0
  have n1 := X.nn 1
  have n2 := X.nn 2
  have n3 := X.nn 3
  have n4 := X.nn 4
  have n5 := X.nn 5
  have n6 := X.nn 6
  have n7 := X.nn 7
  have n8 := X.nn 8
  have n9 := X.nn 9
  have n10 := X.nn 10
  have n11 := X.nn 11
  have n12 := X.nn 12
  have n13 := X.nn 13
  have n14 := X.nn 14
  have n15 := X.nn 15
  obtain ⟨z0, e0⟩ := X.ev 0
  obtain ⟨z1, e1⟩ := X.ev 1
  obtain ⟨z2, e2⟩ := X.ev 2
  obtain ⟨z3, e3⟩ := X.ev 3
  obtain ⟨z4, e4⟩ := X.ev 4
  obtain ⟨z5, e5⟩ := X.ev 5
  obtain ⟨z6, e6⟩ := X.ev 6
  obtain ⟨z7, e7⟩ := X.ev 7
  obtain ⟨z8, e8⟩ := X.ev 8
  obtain ⟨z9, e9⟩ := X.ev 9
  obtain ⟨z10, e10⟩ := X.ev 10
  obtain ⟨z11, e11⟩ := X.ev 11
  obtain ⟨z12, e12⟩ := X.ev 12
  obtain ⟨z13, e13⟩ := X.ev 13
  obtain ⟨z14, e14⟩ := X.ev 14
  obtain ⟨z15, e15⟩ := X.ev 15
  have p16 : w 16 = w 0 := hp 0
  have p17 : w 17 = w 1 := hp 1
  have p18 : w 18 = w 2 := hp 2
  have p19 : w 19 = w 3 := hp 3
  have p20 : w 20 = w 4 := hp 4
  have p21 : w 21 = w 5 := hp 5
  have p22 : w 22 = w 6 := hp 6
  have p23 : w 23 = w 7 := hp 7
  have p24 : w 24 = w 8 := hp 8
  have p25 : w 25 = w 9 := hp 9
  have p26 : w 26 = w 10 := hp 10
  have p27 : w 27 = w 11 := hp 11
  have p28 : w 28 = w 12 := hp 12
  have p29 : w 29 = w 13 := hp 13
  have p30 : w 30 = w 14 := hp 14
  have p31 : w 31 = w 15 := hp 15
  have o5 := X.opt 0 (by show w 5 = 0; omega)
  have o7 := X.opt 2 (by show w 7 = 0; omega)
  have o14 := X.opt 9 (by show w 14 = 0; omega)
  simp only [Sw, Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, Nat.reduceMul, zero_add, add_zero] at o5 o7 o14
  push_cast at hm o5 o7 o14
  omega

lemma bip4_5_9 {w : ℕ → ℤ} (X : Xi9 4 w) (m1 : (8 : ℤ) ≤ Sw w 0 5) (m2 : (8 : ℤ) ≤ Sw w 9 5) : False := by
  have hp : ∀ m, w (m + 16) = w m := fun m => X.per m
  have hm := X.mass 0
  simp only [Sw, Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, Nat.reduceMul, zero_add, add_zero] at hm m1 m2
  have n0 := X.nn 0
  have n1 := X.nn 1
  have n2 := X.nn 2
  have n3 := X.nn 3
  have n4 := X.nn 4
  have n5 := X.nn 5
  have n6 := X.nn 6
  have n7 := X.nn 7
  have n8 := X.nn 8
  have n9 := X.nn 9
  have n10 := X.nn 10
  have n11 := X.nn 11
  have n12 := X.nn 12
  have n13 := X.nn 13
  have n14 := X.nn 14
  have n15 := X.nn 15
  obtain ⟨z0, e0⟩ := X.ev 0
  obtain ⟨z1, e1⟩ := X.ev 1
  obtain ⟨z2, e2⟩ := X.ev 2
  obtain ⟨z3, e3⟩ := X.ev 3
  obtain ⟨z4, e4⟩ := X.ev 4
  obtain ⟨z5, e5⟩ := X.ev 5
  obtain ⟨z6, e6⟩ := X.ev 6
  obtain ⟨z7, e7⟩ := X.ev 7
  obtain ⟨z8, e8⟩ := X.ev 8
  obtain ⟨z9, e9⟩ := X.ev 9
  obtain ⟨z10, e10⟩ := X.ev 10
  obtain ⟨z11, e11⟩ := X.ev 11
  obtain ⟨z12, e12⟩ := X.ev 12
  obtain ⟨z13, e13⟩ := X.ev 13
  obtain ⟨z14, e14⟩ := X.ev 14
  obtain ⟨z15, e15⟩ := X.ev 15
  have p16 : w 16 = w 0 := hp 0
  have p17 : w 17 = w 1 := hp 1
  have p18 : w 18 = w 2 := hp 2
  have p19 : w 19 = w 3 := hp 3
  have p20 : w 20 = w 4 := hp 4
  have p21 : w 21 = w 5 := hp 5
  have p22 : w 22 = w 6 := hp 6
  have p23 : w 23 = w 7 := hp 7
  have p24 : w 24 = w 8 := hp 8
  have p25 : w 25 = w 9 := hp 9
  have p26 : w 26 = w 10 := hp 10
  have p27 : w 27 = w 11 := hp 11
  have p28 : w 28 = w 12 := hp 12
  have p29 : w 29 = w 13 := hp 13
  have p30 : w 30 = w 14 := hp 14
  have p31 : w 31 = w 15 := hp 15
  have o5 := X.opt 0 (by show w 5 = 0; omega)
  have o7 := X.opt 2 (by show w 7 = 0; omega)
  simp only [Sw, Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd, Nat.reduceMul, zero_add, add_zero] at o5 o7
  push_cast at hm o5 o7
  omega

/-- two disjoint heavy windows are impossible for `a = 4` -/
lemma no_bipolar4 {ξ : ℕ → ℤ} (X : Xi9 4 ξ) (A1 A2 ℓ : ℕ) (hA1 : 4 + 1 ≤ A1)
    (hℓ1 : 4 ≤ ℓ) (hℓ2 : ℓ ≤ 4 + 1) (h12 : A1 + ℓ ≤ A2) (h21 : A2 + ℓ ≤ A1 + 4 * 4)
    (m1 : 2 * ((4 : ℕ) : ℤ) ≤ Sw ξ A1 ℓ) (m2 : 2 * ((4 : ℕ) : ℤ) ≤ Sw ξ A2 ℓ) : False := by
  have g1 := bipolar_gap X (by norm_num) A1 A2 ℓ hA1 hℓ1 hℓ2 h12 h21 m1 m2
  have m1' : 2 * ((4 : ℕ) : ℤ) ≤ Sw ξ (A1 + 4 * 4) ℓ := by rw [Sw_per X]; exact m1
  have g2 := bipolar_gap X (by norm_num) A2 (A1 + 4 * 4) ℓ (by omega) hℓ1 hℓ2 h21 (by omega) m2 m1'
  have hs : ∀ t n, Sw (fun m => ξ (A1 + m)) t n = Sw ξ (A1 + t) n := by
    intro t n
    simp only [Sw, add_assoc]
  have X' := X.shift A1
  have m1w : (8 : ℤ) ≤ Sw (fun m => ξ (A1 + m)) 0 ℓ := by rw [hs, add_zero]; push_cast at m1; linarith
  have hc : (ℓ = 4 ∧ A2 = A1 + 8) ∨ (ℓ = 5 ∧ A2 = A1 + 7) ∨ (ℓ = 5 ∧ A2 = A1 + 8) ∨ (ℓ = 5 ∧ A2 = A1 + 9) := by
    omega
  push_cast at m2
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact bip4_4_8 X' m1w (by rw [hs]; linarith)
  · exact bip4_5_7 X' m1w (by rw [hs]; linarith)
  · exact bip4_5_8 X' m1w (by rw [hs]; linarith)
  · exact bip4_5_9 X' m1w (by rw [hs]; linarith)


set_option maxHeartbeats 3200000 in
/-- Step 2' of Theorem 9 for `a ≥ 4`, given that bipolar configurations are impossible (same proof as `no_xi9`) -/
theorem no_xi9_of {a : ℕ} {ξ : ℕ → ℤ} (X : Xi9 a ξ) (ha : 4 ≤ a)
    (hb : ∀ (A1 A2 ℓ : ℕ), a + 1 ≤ A1 → a ≤ ℓ → ℓ ≤ a + 1 → A1 + ℓ ≤ A2 → A2 + ℓ ≤ A1 + 4 * a →
      2 * (a : ℤ) ≤ Sw ξ A1 ℓ → 2 * (a : ℤ) ≤ Sw ξ A2 ℓ → False) : False := by
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
    exact hb (Λ + x + 1) (Λ + y + 1) a (by omega) (le_refl _) (by omega) (by omega)
      (by omega) x3 y3
  have hLpair : ∀ x ∈ Lz, ∀ y ∈ Lz, x < y → y - x < a + 1 ∨ Λ < y - x + (a + 1) := by
    intro x hx y hy hxy
    have x3 := hLw x hx
    have y3 := hLw y hy
    have x1 := ((memL x).mp hx).1
    have y1 := ((memL y).mp hy).1
    by_contra hcon
    rw [not_or, not_lt, not_lt] at hcon
    exact hb (Λ + x - a - 1) (Λ + y - a - 1) (a + 1) (by omega) (by omega) (le_refl _)
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
  have haz : (4 : ℤ) ≤ a := by exact_mod_cast ha
  linarith


/-- **Step 2' of Theorem 9 for `a = 4`** -/
theorem no_xi9_four {ξ : ℕ → ℤ} (X : Xi9 4 ξ) : False :=
  no_xi9_of X (by norm_num) (fun A1 A2 ℓ h1 h2 h3 h4 h5 m1 m2 => no_bipolar4 X A1 A2 ℓ h1 h2 h3 h4 h5 m1 m2)

end Coil

#print axioms Coil.no_xi9_four
