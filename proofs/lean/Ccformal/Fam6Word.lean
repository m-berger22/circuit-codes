import Ccformal.Fam6Count
import Ccformal.Fam10Word

/-!
# Family 6 × m: the transition word (labels, (G1), (G2), orbits, at most `n` labels)
-/

open Finset

namespace Coil

namespace Fam6

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedVariables false

open Fam10 (modeq3 cP_odd card_eq_cP)

/-- the label of the coordinate flipped at position `x` -/
def lab (c p K hu : ℕ) (x : ℕ) : ℕ :=
  if x % p = 1 then x % (4 * K + 4 * hu)
  else if x % p = 2 * c + 5 then (x + (3 * K + 4 * hu)) % (4 * K + 4 * hu)
  else if x % p = 2 then (x + (2 * K + 4 * hu - 1)) % (4 * K + 4 * hu)
  else if x % p = 2 * c + 4 then (x + (K + 1)) % (4 * K + 4 * hu)
  else if E6 c p x then x % (K + hu)
  else x % (2 * K + 2 * hu)

abbrev Dt (c p x : ℕ) : Prop :=
  x % p ≠ 1 ∧ x % p ≠ 2 * c + 5 ∧ x % p ≠ 2 ∧ x % p ≠ 2 * c + 4 ∧ ¬ E6 c p x

variable {c μ p K hu Qk q3 : ℕ} (P : Par c μ p K hu Qk q3)

lemma lab_1 {x : ℕ} (h : x % p = 1) : lab c p K hu x = x % (4 * K + 4 * hu) := by
  unfold lab; rw [if_pos h]

lemma lab_b {x : ℕ} (h : x % p = 2 * c + 5) : lab c p K hu x = (x + (3 * K + 4 * hu)) % (4 * K + 4 * hu) := by
  unfold lab; rw [if_neg (by omega), if_pos h]

lemma lab_2 {x : ℕ} (h : x % p = 2) : lab c p K hu x = (x + (2 * K + 4 * hu - 1)) % (4 * K + 4 * hu) := by
  unfold lab; rw [if_neg (by omega), if_neg (by omega), if_pos h]

lemma lab_a {x : ℕ} (h : x % p = 2 * c + 4) : lab c p K hu x = (x + (K + 1)) % (4 * K + 4 * hu) := by
  unfold lab; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h]

lemma lab_E {x : ℕ} (h : E6 c p x) : lab c p K hu x = x % (K + hu) := by
  have h' := h
  unfold E6 at h'
  unfold lab; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h]

lemma lab_dot {x : ℕ} (h : Dt c p x) : lab c p K hu x = x % (2 * K + 2 * hu) := by
  unfold lab; rw [if_neg h.1, if_neg h.2.1, if_neg h.2.2.1, if_neg h.2.2.2.1, if_neg h.2.2.2.2]

include P

lemma dvdN : p ∣ 4 * K + 4 * hu :=
  ⟨4 * (Qk + μ + 1), by rw [show 4 * K + 4 * hu = 4 * (K + hu) by ring, hKhu P]; ring⟩

lemma dvd1 : p ∣ K + hu := ⟨_, hKhu P⟩

lemma dvd2 : p ∣ 2 * K + 2 * hu :=
  ⟨2 * (Qk + μ + 1), by rw [show 2 * K + 2 * hu = 2 * (K + hu) by ring, hKhu P]; ring⟩

/-- label, its residue, and the gap, by class -/
lemma lab_cases (x : ℕ) :
    (∃ o, lab c p K hu x = (x + o) % (4 * K + 4 * hu) ∧ lab c p K hu x % p = 1 ∧
      ((x % p = 1 ∧ o = 0 ∧ gF c p K hu x = K) ∨
       (x % p = 2 * c + 5 ∧ o = 3 * K + 4 * hu ∧ gF c p K hu x = K + 1) ∨
       (x % p = 2 ∧ o + 1 = 2 * K + 4 * hu ∧ gF c p K hu x + 2 = K + 4 * hu) ∨
       (x % p = 2 * c + 4 ∧ o = K + 1 ∧ gF c p K hu x = K + 1))) ∨
    (E6 c p x ∧ lab c p K hu x = x % (K + hu) ∧ lab c p K hu x % p = x % p ∧ gF c p K hu x = K + hu) ∨
    (Dt c p x ∧ lab c p K hu x = x % (2 * K + 2 * hu) ∧ lab c p K hu x % p = x % p ∧
      gF c p K hu x = 2 * K + 2 * hu) := by
  have hp := P.hp
  have hhu := P.hhu
  have hK := P.hK
  by_cases h1 : x % p = 1
  · left
    refine ⟨0, by rw [lab_1 h1, add_zero], ?_, Or.inl ⟨h1, rfl, gF_1 h1⟩⟩
    rw [lab_1 h1, Nat.mod_mod_of_dvd _ (dvdN P), h1]
  by_cases hb : x % p = 2 * c + 5
  · left
    refine ⟨_, lab_b hb, ?_, Or.inr (Or.inl ⟨hb, rfl, gF_b hb⟩)⟩
    rw [lab_b hb, Nat.mod_mod_of_dvd _ (dvdN P)]
    exact mod_of (q := 3 * Qk + 4 * μ + 4) hb (by rw [P.hK, P.hhu, P.hp]; ring) (by omega)
  by_cases h2 : x % p = 2
  · left
    refine ⟨_, lab_2 h2, ?_, Or.inr (Or.inr (Or.inl ⟨h2, by omega, by rw [gF_2 h2]; omega⟩))⟩
    rw [lab_2 h2, Nat.mod_mod_of_dvd _ (dvdN P)]
    have e : 2 * K + 4 * hu - 1 = 2 * (p * Qk) + 4 * (p * μ) + (12 * c + 23) := by omega
    exact mod_of (q := 2 * Qk + 4 * μ + 3) h2 (by rw [e, P.hp]; ring) (by omega)
  by_cases ha : x % p = 2 * c + 4
  · left
    refine ⟨_, lab_a ha, ?_, Or.inr (Or.inr (Or.inr ⟨ha, rfl, gF_a ha⟩))⟩
    rw [lab_a ha, Nat.mod_mod_of_dvd _ (dvdN P)]
    exact sta P ha
  by_cases hE : E6 c p x
  · right; left
    exact ⟨hE, lab_E hE, by rw [lab_E hE, Nat.mod_mod_of_dvd _ (dvd1 P)], gF_E hE⟩
  · right; right
    have hD : Dt c p x := ⟨h1, hb, h2, ha, hE⟩
    exact ⟨hD, lab_dot hD, by rw [lab_dot hD, Nat.mod_mod_of_dvd _ (dvd2 P)], gF_dot h1 hb h2 ha hE⟩

lemma E6_shift (x : ℕ) (h : E6 c p x) : E6 c p (x + (K + hu)) := by
  unfold E6; rw [stE P]; exact h

lemma Dt_shift (x : ℕ) (h : Dt c p x) : Dt c p (x + (2 * K + 2 * hu)) := by
  unfold Dt E6; rw [stD P]; exact h

/-- (G1) -/
lemma lab_succ (x : ℕ) : lab c p K hu (x + gF c p K hu x) = lab c p K hu x := by
  have hhu := P.hhu
  have hK := P.hK
  by_cases h1 : x % p = 1
  · rw [gF_1 h1, lab_b (st1 P h1), lab_1 h1, show x + K + (3 * K + 4 * hu) = x + (4 * K + 4 * hu) by omega,
      Nat.add_mod_right]
  by_cases hb : x % p = 2 * c + 5
  · rw [gF_b hb, lab_2 (stb P hb), lab_b hb, show x + (K + 1) + (2 * K + 4 * hu - 1) = x + (3 * K + 4 * hu) by omega]
  by_cases h2 : x % p = 2
  · rw [gF_2 h2, lab_a (st2 P h2), lab_2 h2,
      show x + (K + 4 * hu - 2) + (K + 1) = x + (2 * K + 4 * hu - 1) by omega]
  by_cases ha : x % p = 2 * c + 4
  · rw [gF_a ha, lab_1 (sta P ha), lab_a ha]
  by_cases hE : E6 c p x
  · rw [gF_E hE, lab_E (E6_shift P x hE), lab_E hE, Nat.add_mod_right]
  · have hD : Dt c p x := ⟨h1, hb, h2, ha, hE⟩
    rw [gF_dot h1 hb h2 ha hE, lab_dot (Dt_shift P x hD), lab_dot hD, Nat.add_mod_right]

/-- (G2) -/
lemma lab_gap (x d : ℕ) (hd0 : 0 < d) (hd : d < gF c p K hu x) : lab c p K hu (x + d) ≠ lab c p K hu x := by
  intro hl
  have hK := P.ha0
  have hhu := P.hhu
  have hp := P.hp
  have hres : lab c p K hu (x + d) % p = lab c p K hu x % p := by rw [hl]
  rcases lab_cases P x with ⟨o, e, r, hcl⟩ | ⟨h1, e, r, hg⟩ | ⟨h1, e, r, hg⟩
  · rcases lab_cases P (x + d) with ⟨o', e', r', hcl'⟩ | ⟨h1', e', r', hg'⟩ | ⟨h1', e', r', hg'⟩
    · rw [e, e'] at hl
      have := modeq3 (A := x) (u := d + o') (v := o) (by rw [← add_assoc]; exact hl)
      omega
    · unfold E6 at h1'; omega
    · unfold Dt at h1'; omega
  · rcases lab_cases P (x + d) with ⟨o', e', r', hcl'⟩ | ⟨h1', e', r', hg'⟩ | ⟨h1', e', r', hg'⟩
    · unfold E6 at h1; omega
    · rw [e, e'] at hl
      have := modeq3 (A := x) (u := d) (v := 0) (by rw [add_zero]; exact hl)
      omega
    · exfalso
      apply h1'.2.2.2.2
      unfold E6 at h1 ⊢
      rw [← r', hres, r]
      exact h1
  · rcases lab_cases P (x + d) with ⟨o', e', r', hcl'⟩ | ⟨h1', e', r', hg'⟩ | ⟨h1', e', r', hg'⟩
    · unfold Dt at h1; omega
    · exfalso
      apply h1.2.2.2.2
      unfold E6 at h1' ⊢
      rw [← r, ← hres, r']
      exact h1'
    · rw [e, e'] at hl
      have := modeq3 (A := x) (u := d) (v := 0) (by rw [add_zero]; exact hl)
      omega

/-- (G3) -/
lemma gF_ge (x : ℕ) : K ≤ gF c p K hu x := by
  have hhu := P.hhu
  rcases gF_two P x with ⟨hr, hg, hs⟩ | ⟨hr, hg, hs⟩ | ⟨hr, hg, hs⟩ | ⟨hr, hg, hs⟩ | ⟨hr, hg, hs⟩ |
    ⟨h1, h2, h3, h4, h5, hg, hs⟩ <;> omega

/-- (G4) and (G5) -/
lemma orbit (x : ℕ) :
    (4 * K + 4 * hu ≤ 2 * (gF c p K hu x + gF c p K hu (x + gF c p K hu x)
      + gF c p K hu (x + gF c p K hu x + gF c p K hu (x + gF c p K hu x)))) ∧
    (gF c p K hu x + (gF c p K hu (x + gF c p K hu x) + 0) = 4 * K + 4 * hu ∨
      gF c p K hu x + (gF c p K hu (x + gF c p K hu x) +
        (gF c p K hu (x + gF c p K hu x + gF c p K hu (x + gF c p K hu x)) +
        (gF c p K hu (x + gF c p K hu x + gF c p K hu (x + gF c p K hu x)
          + gF c p K hu (x + gF c p K hu x + gF c p K hu (x + gF c p K hu x))) + 0))) = 4 * K + 4 * hu) := by
  have hK := P.ha0
  have hhu := P.hhu
  by_cases h1 : x % p = 1
  · rw [gF_1 h1, gF_b (st1 P h1), gF_2 (stb P (st1 P h1)), gF_a (st2 P (stb P (st1 P h1)))]
    omega
  by_cases hb : x % p = 2 * c + 5
  · rw [gF_b hb, gF_2 (stb P hb), gF_a (st2 P (stb P hb)), gF_1 (sta P (st2 P (stb P hb)))]
    omega
  by_cases h2 : x % p = 2
  · rw [gF_2 h2, gF_a (st2 P h2), gF_1 (sta P (st2 P h2)), gF_b (st1 P (sta P (st2 P h2)))]
    omega
  by_cases ha : x % p = 2 * c + 4
  · rw [gF_a ha, gF_1 (sta P ha), gF_b (st1 P (sta P ha)), gF_2 (stb P (st1 P (sta P ha)))]
    omega
  by_cases hE : E6 c p x
  · have e0 := gF_E (K := K) (hu := hu) hE
    have e1 := gF_E (K := K) (hu := hu) (E6_shift P x hE)
    have e2 := gF_E (K := K) (hu := hu) (E6_shift P _ (E6_shift P x hE))
    have e3 := gF_E (K := K) (hu := hu) (E6_shift P _ (E6_shift P _ (E6_shift P x hE)))
    rw [e0, e1, e2, e3]
    omega
  · have hD : Dt c p x := ⟨h1, hb, h2, ha, hE⟩
    have hD1 := Dt_shift P x hD
    have hD2 := Dt_shift P _ hD1
    have e0 := gF_dot (K := K) (hu := hu) h1 hb h2 ha hE
    have e1 := gF_dot (K := K) (hu := hu) hD1.1 hD1.2.1 hD1.2.2.1 hD1.2.2.2.1 hD1.2.2.2.2
    have e2 := gF_dot (K := K) (hu := hu) hD2.1 hD2.2.1 hD2.2.2.1 hD2.2.2.2.1 hD2.2.2.2.2
    rw [e0, e1, e2]
    omega

/-! ### the set of labels -/

def labS (c p K hu : ℕ) : Finset ℕ :=
  {m ∈ range (4 * K + 4 * hu) | m % p = 1} ∪ {m ∈ range (K + hu) | E6 c p m} ∪
    {m ∈ range (2 * K + 2 * hu) | Dt c p m}

lemma lab_mem (x : ℕ) : lab c p K hu x ∈ labS c p K hu := by
  have hpos : 0 < K + hu := by have := P.hhu; omega
  unfold labS
  rcases lab_cases P x with ⟨o, e, r, hcl⟩ | ⟨h1, e, r, hg⟩ | ⟨h1, e, r, hg⟩
  · apply mem_union_left; apply mem_union_left
    simp only [mem_filter, mem_range]
    exact ⟨by rw [e]; exact Nat.mod_lt _ (by omega), r⟩
  · apply mem_union_left; apply mem_union_right
    simp only [mem_filter, mem_range]
    refine ⟨by rw [e]; exact Nat.mod_lt _ hpos, ?_⟩
    unfold E6 at h1 ⊢
    rw [r]; exact h1
  · apply mem_union_right
    simp only [mem_filter, mem_range]
    refine ⟨by rw [e]; exact Nat.mod_lt _ (by omega), ?_⟩
    unfold Dt E6 at h1 ⊢
    rw [r]; exact h1

lemma bD : cP (Dt c p) 0 p ≤ 2 * c + 3 := by
  have hp := P.hp
  have h1 := cP_or_le (Q := Dt c p) (Q1 := fun x => x % p = 0)
    (Q2 := fun x => x % p = 3 ∨ x % p = 2 * c + 6 ∨ (x % p % 2 = 1 ∧ 5 ≤ x % p ∧ x % p ≤ 2 * c + 3)
      ∨ (x % p % 2 = 0 ∧ 2 * c + 8 ≤ x % p)) (fun x h => by
        have := Nat.mod_lt x (by omega : 0 < p)
        unfold Dt E6 at h
        omega) 0 p
  have h2 := cP_or_le (Q := fun x => x % p = 3 ∨ x % p = 2 * c + 6 ∨ (x % p % 2 = 1 ∧ 5 ≤ x % p ∧ x % p ≤ 2 * c + 3)
      ∨ (x % p % 2 = 0 ∧ 2 * c + 8 ≤ x % p)) (Q1 := fun x => x % p = 3)
    (Q2 := fun x => x % p = 2 * c + 6 ∨ (x % p % 2 = 1 ∧ 5 ≤ x % p ∧ x % p ≤ 2 * c + 3)
      ∨ (x % p % 2 = 0 ∧ 2 * c + 8 ≤ x % p)) (fun x h => h) 0 p
  have h3 := cP_or_le (Q := fun x => x % p = 2 * c + 6 ∨ (x % p % 2 = 1 ∧ 5 ≤ x % p ∧ x % p ≤ 2 * c + 3)
      ∨ (x % p % 2 = 0 ∧ 2 * c + 8 ≤ x % p)) (Q1 := fun x => x % p = 2 * c + 6)
    (Q2 := fun x => (x % p % 2 = 1 ∧ 5 ≤ x % p ∧ x % p ≤ 2 * c + 3) ∨ (x % p % 2 = 0 ∧ 2 * c + 8 ≤ x % p))
    (fun x h => h) 0 p
  have h4 := cP_or_le (Q := fun x => (x % p % 2 = 1 ∧ 5 ≤ x % p ∧ x % p ≤ 2 * c + 3) ∨ (x % p % 2 = 0 ∧ 2 * c + 8 ≤ x % p))
    (Q1 := fun x => x % p % 2 = 1 ∧ 5 ≤ x % p ∧ x % p ≤ 2 * c + 3) (Q2 := fun x => x % p % 2 = 0 ∧ 2 * c + 8 ≤ x % p)
    (fun x h => h) 0 p
  have r0 := cR P 0
  have r3 := cR P 3
  have r6 := cR P (2 * c + 6)
  have ho : cP (fun x => x % p % 2 = 1 ∧ 5 ≤ x % p ∧ x % p ≤ 2 * c + 3) 0 p ≤ c := by
    rw [show p = 5 + ((2 * c) + (2 * c + 3)) by omega, cP_add, cP_add]
    have e1 : cP (fun x => x % (5 + ((2 * c) + (2 * c + 3))) % 2 = 1 ∧ 5 ≤ x % (5 + ((2 * c) + (2 * c + 3)))
        ∧ x % (5 + ((2 * c) + (2 * c + 3))) ≤ 2 * c + 3) 0 5 = 0 := by
      apply cP_eq_zero
      intro m hm h
      rw [Nat.mod_eq_of_lt (by omega : 0 + m < 5 + ((2 * c) + (2 * c + 3)))] at h
      omega
    have e2 : cP (fun x => x % (5 + ((2 * c) + (2 * c + 3))) % 2 = 1 ∧ 5 ≤ x % (5 + ((2 * c) + (2 * c + 3)))
        ∧ x % (5 + ((2 * c) + (2 * c + 3))) ≤ 2 * c + 3) (0 + 5) (2 * c)
        ≤ cP (fun x => x % 2 = 1) (0 + 5) (2 * c) := by
      rw [cP_eq_sum, cP_eq_sum]
      apply sum_le_sum
      intro m hm
      rw [mem_range] at hm
      rw [Nat.mod_eq_of_lt (by omega : 0 + 5 + m < 5 + ((2 * c) + (2 * c + 3)))]
      split_ifs <;> omega
    have e3 : cP (fun x => x % (5 + ((2 * c) + (2 * c + 3))) % 2 = 1 ∧ 5 ≤ x % (5 + ((2 * c) + (2 * c + 3)))
        ∧ x % (5 + ((2 * c) + (2 * c + 3))) ≤ 2 * c + 3) (0 + 5 + (2 * c)) (2 * c + 3) = 0 := by
      apply cP_eq_zero
      intro m hm h
      rw [Nat.mod_eq_of_lt (by omega : 0 + 5 + (2 * c) + m < 5 + ((2 * c) + (2 * c + 3)))] at h
      omega
    have e4 := cP_le_half (Q := fun x => x % 2 = 1) (fun x ⟨a, b⟩ => by omega) (0 + 5) (2 * c)
    omega
  have he : cP (fun x => x % p % 2 = 0 ∧ 2 * c + 8 ≤ x % p) 0 p ≤ c := by
    rw [show p = (2 * c + 8) + (2 * c) by omega, cP_add]
    have e1 : cP (fun x => x % ((2 * c + 8) + (2 * c)) % 2 = 0 ∧ 2 * c + 8 ≤ x % ((2 * c + 8) + (2 * c)))
        0 (2 * c + 8) = 0 := by
      apply cP_eq_zero
      intro m hm h
      rw [Nat.mod_eq_of_lt (by omega : 0 + m < (2 * c + 8) + (2 * c))] at h
      omega
    have e2 : cP (fun x => x % ((2 * c + 8) + (2 * c)) % 2 = 0 ∧ 2 * c + 8 ≤ x % ((2 * c + 8) + (2 * c)))
        (0 + (2 * c + 8)) (2 * c) ≤ cP (fun x => x % 2 = 0) (0 + (2 * c + 8)) (2 * c) := by
      rw [cP_eq_sum, cP_eq_sum]
      apply sum_le_sum
      intro m hm
      rw [mem_range] at hm
      rw [Nat.mod_eq_of_lt (by omega : 0 + (2 * c + 8) + m < (2 * c + 8) + (2 * c))]
      split_ifs <;> omega
    have e4 := cP_le_half (Q := fun x => x % 2 = 0) (fun x ⟨a, b⟩ => by omega) (0 + (2 * c + 8)) (2 * c)
    omega
  omega

lemma card_labS : (labS c p K hu).card ≤ (6 * c + 11) * (Qk + μ + 1) := by
  have hA := hKhu P
  have eN : 4 * K + 4 * hu = p * (4 * (Qk + μ + 1)) := by
    rw [show 4 * K + 4 * hu = 4 * (K + hu) by ring, hA]; ring
  have e2 : 2 * K + 2 * hu = p * (2 * (Qk + μ + 1)) := by
    rw [show 2 * K + 2 * hu = 2 * (K + hu) by ring, hA]; ring
  have perE : ∀ x, E6 c p (x + p) ↔ E6 c p x := by intro x; unfold E6; rw [Nat.add_mod_right]
  have perD : ∀ x, Dt c p (x + p) ↔ Dt c p x := by intro x; unfold Dt E6; rw [Nat.add_mod_right]
  unfold labS
  refine (card_union_le _ _).trans ?_
  refine (Nat.add_le_add_right (card_union_le _ _) _).trans ?_
  rw [card_eq_cP (fun m => m % p = 1), card_eq_cP (E6 c p), card_eq_cP (Dt c p), eN, hA, e2,
    cP_full (by intro x; simp only [Nat.add_mod_right]), cP_full perE, cP_full perD]
  have b6 := cP_res_le_one p 1 0 p le_rfl
  have h6 := Nat.mul_le_mul_left (4 * (Qk + μ + 1)) b6
  have hE := Nat.mul_le_mul_left (Qk + μ + 1) (cE P)
  have hD := Nat.mul_le_mul_left (2 * (Qk + μ + 1)) (bD P)
  nlinarith [h6, hE, hD]

/-- **The word of family 6 × m.** -/
theorem word_exists (n : ℕ) (hn : (6 * c + 11) * (Qk + μ + 1) ≤ n) :
    ∃ T : ℕ → Fin n, IsCoilWord (K - 1) (4 * K + 4 * hu) T := by
  have hK := P.ha0
  have hhu := P.hhu
  have hp := P.hp
  have hcard : (labS c p K hu).card ≤ n := (card_labS P).trans hn
  let T : ℕ → Fin n := fun x => Fin.castLE hcard ((labS c p K hu).equivFin ⟨lab c p K hu x, lab_mem P x⟩)
  have hT1 : ∀ x y, T x = T y → lab c p K hu x = lab c p K hu y := by
    intro x y h
    have h1 := Fin.castLE_injective hcard h
    have h2 := (labS c p K hu).equivFin.injective h1
    exact congrArg Subtype.val h2
  have hT2 : ∀ x y, lab c p K hu x = lab c p K hu y → T x = T y := by
    intro x y h
    have : (⟨lab c p K hu x, lab_mem P x⟩ : labS c p K hu) = ⟨lab c p K hu y, lab_mem P y⟩ := Subtype.ext h
    show Fin.castLE hcard ((labS c p K hu).equivFin ⟨lab c p K hu x, lab_mem P x⟩)
      = Fin.castLE hcard ((labS c p K hu).equivFin ⟨lab c p K hu y, lab_mem P y⟩)
    rw [this]
  refine ⟨T, isCoilWord_of_gaps (gF c p K hu) (fun x => hT2 _ _ (lab_succ P x))
    (fun x d h0 hd h => lab_gap P x d h0 hd (hT1 _ _ h)) (by omega) ?_ (fun x => (orbit P x).1)
    (fun x => (orbit P x).2) ?_⟩
  · intro x
    have := gF_ge P x
    omega
  · intro t L h1 h2
    have := count_le P t L (by omega) (by omega)
    unfold Wc at this
    exact this

end Fam6

end Coil

#print axioms Coil.Fam6.word_exists
