import Ccformal.Fam10Count

/-!
# Family 10: the transition word

Coordinates are named by a label `lab x ∈ ℕ` (a canonical position of the orbit of `x` under `x ↦ x + gF x`):
dots `x mod N/2`, E runs `x mod N/4`, chains `(x + offset) mod N` (the chain's element of residue `p-3`).
`lab_succ` = (G1), `lab_gap` = (G2), `card_labS` = at most `n = (6a+13)(Q+i+1)` labels; `word_exists` puts the
pieces into the gap criterion.
-/

open Finset

namespace Coil

namespace Fam10

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedVariables false

/-- the label of the coordinate flipped at position `x` -/
def lab (a p K hu : ℕ) (x : ℕ) : ℕ :=
  if x % p = 4 * a + 6 then x % (4 * K + 4 * hu)
  else if x % p = 2 * a + 2 then (x + (3 * K + 4 * hu)) % (4 * K + 4 * hu)
  else if x % p = 4 * a + 7 then (x + (2 * K + 4 * hu)) % (4 * K + 4 * hu)
  else if x % p = 4 * a + 4 then (x + (K + 2 * hu - (2 * a + 2))) % (4 * K + 4 * hu)
  else if x % p % 2 = 0 ∧ x % p ≤ 4 * a + 2 then x % (K + hu)
  else x % (2 * K + 2 * hu)

lemma modeq3 {N A u v : ℕ} (h : (A + u) % N = (A + v) % N) : u = v ∨ v + N ≤ u ∨ u + N ≤ v := by
  by_contra hc
  push_neg at hc
  rcases Nat.lt_or_gt_of_ne hc.1 with hlt | hgt
  · have := Nat.sub_mod_eq_zero_of_mod_eq h.symm
    rw [show A + v - (A + u) = v - u by omega, Nat.mod_eq_of_lt (by omega)] at this
    omega
  · have := Nat.sub_mod_eq_zero_of_mod_eq h
    rw [show A + u - (A + v) = u - v by omega, Nat.mod_eq_of_lt (by omega)] at this
    omega

lemma cP_odd (n : ℕ) : cP (fun x => x % 2 = 1) 0 n = n / 2 := by
  induction n with
  | zero => simp [cP]
  | succ n ih =>
    rw [cP_succ, ih, zero_add]
    split_ifs <;> omega

lemma card_eq_cP (Q : ℕ → Prop) [DecidablePred Q] (L : ℕ) : #{m ∈ range L | Q m} = cP Q 0 L := by
  simp [cP]

variable {a i p K hu Q q4 : ℕ} (P : Par a i p K hu Q q4)

lemma lab_3 {x : ℕ} (h : x % p = 4 * a + 6) : lab a p K hu x = x % (4 * K + 4 * hu) := by
  unfold lab; rw [if_pos h]

lemma lab_c {x : ℕ} (h : x % p = 2 * a + 2) : lab a p K hu x = (x + (3 * K + 4 * hu)) % (4 * K + 4 * hu) := by
  unfold lab; rw [if_neg (by omega), if_pos h]

lemma lab_2 {x : ℕ} (h : x % p = 4 * a + 7) : lab a p K hu x = (x + (2 * K + 4 * hu)) % (4 * K + 4 * hu) := by
  unfold lab; rw [if_neg (by omega), if_neg (by omega), if_pos h]

lemma lab_5 {x : ℕ} (h : x % p = 4 * a + 4) :
    lab a p K hu x = (x + (K + 2 * hu - (2 * a + 2))) % (4 * K + 4 * hu) := by
  unfold lab; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h]

lemma lab_E {x : ℕ} (h1 : x % p % 2 = 0) (h2 : x % p ≤ 4 * a + 2) (h3 : x % p ≠ 2 * a + 2) :
    lab a p K hu x = x % (K + hu) := by
  unfold lab; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos ⟨h1, h2⟩]

lemma lab_dot {x : ℕ} (h1 : ¬(x % p % 2 = 0 ∧ x % p ≤ 4 * a + 6)) (h2 : x % p ≠ 4 * a + 7) :
    lab a p K hu x = x % (2 * K + 2 * hu) := by
  unfold lab
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

include P

lemma hKhu : K + hu = p * (Q + i + 1) := by rw [P.hK, P.hhu, P.hp]; ring

lemma dvdN : p ∣ 4 * K + 4 * hu :=
  ⟨4 * (Q + i + 1), by rw [show 4 * K + 4 * hu = 4 * (K + hu) by ring, hKhu P]; ring⟩

lemma dvd1 : p ∣ K + hu := ⟨_, hKhu P⟩

lemma dvd2 : p ∣ 2 * K + 2 * hu :=
  ⟨2 * (Q + i + 1), by rw [show 2 * K + 2 * hu = 2 * (K + hu) by ring, hKhu P]; ring⟩

lemma st3 {x : ℕ} (h : x % p = 4 * a + 6) : (x + K) % p = 2 * a + 2 :=
  mod_of (q := Q + 1) h (by rw [P.hK, P.hp]; ring) (by have := P.hp; omega)

lemma stc {x : ℕ} (h : x % p = 2 * a + 2) : (x + K) % p = 4 * a + 7 :=
  mod_of (q := Q) h (by rw [P.hK, P.hp]; ring) (by have := P.hp; omega)

lemma st2 {x : ℕ} (h : x % p = 4 * a + 7) : (x + (K + 2 * hu + (2 * a + 2))) % p = 4 * a + 4 :=
  mod_of (q := Q + 2 * i + 2) h (by rw [P.hK, P.hhu, P.hp]; ring) (by have := P.hp; omega)

lemma st5 {x : ℕ} (h : x % p = 4 * a + 4) : (x + (K + 2 * hu - (2 * a + 2))) % p = 4 * a + 6 :=
  mod_of (q := Q + 2 * i + 1) h (by rw [hd5 P, P.hp]; ring) (by have := P.hp; omega)

lemma stE (y : ℕ) : (y + (K + hu)) % p = y % p := by
  rw [hKhu P, Nat.add_mul_mod_self_left]

lemma stD (y : ℕ) : (y + (2 * K + 2 * hu)) % p = y % p := by
  rw [show 2 * K + 2 * hu = p * (2 * (Q + i + 1)) by
    rw [show 2 * K + 2 * hu = 2 * (K + hu) by ring, hKhu P]; ring, Nat.add_mul_mod_self_left]

/-- label, its residue, and the gap, by class -/
lemma lab_cases (x : ℕ) :
    (∃ o, lab a p K hu x = (x + o) % (4 * K + 4 * hu) ∧ lab a p K hu x % p = 4 * a + 6 ∧
      ((x % p = 4 * a + 6 ∧ o = 0 ∧ gF a p K hu x = K) ∨
       (x % p = 2 * a + 2 ∧ o = 3 * K + 4 * hu ∧ gF a p K hu x = K) ∨
       (x % p = 4 * a + 7 ∧ o = 2 * K + 4 * hu ∧ gF a p K hu x = K + 2 * hu + (2 * a + 2)) ∨
       (x % p = 4 * a + 4 ∧ o + (2 * a + 2) = K + 2 * hu ∧ gF a p K hu x + (2 * a + 2) = K + 2 * hu))) ∨
    (x % p % 2 = 0 ∧ x % p ≤ 4 * a + 2 ∧ x % p ≠ 2 * a + 2 ∧ lab a p K hu x = x % (K + hu) ∧
      lab a p K hu x % p = x % p ∧ gF a p K hu x = K + hu) ∨
    (¬(x % p % 2 = 0 ∧ x % p ≤ 4 * a + 6) ∧ x % p ≠ 4 * a + 7 ∧ lab a p K hu x = x % (2 * K + 2 * hu) ∧
      lab a p K hu x % p = x % p ∧ gF a p K hu x = 2 * K + 2 * hu) := by
  have hp := P.hp
  have hhu := P.hhu
  by_cases h3 : x % p = 4 * a + 6
  · left
    refine ⟨0, by rw [lab_3 h3, add_zero], ?_, Or.inl ⟨h3, rfl, gF_3 h3⟩⟩
    rw [lab_3 h3, Nat.mod_mod_of_dvd _ (dvdN P), h3]
  by_cases hc : x % p = 2 * a + 2
  · left
    refine ⟨_, lab_c hc, ?_, Or.inr (Or.inl ⟨hc, rfl, gF_c hc⟩)⟩
    rw [lab_c hc, Nat.mod_mod_of_dvd _ (dvdN P)]
    exact mod_of (q := 3 * Q + 4 * i + 3) hc (by rw [P.hK, P.hhu, P.hp]; ring) (by omega)
  by_cases h2 : x % p = 4 * a + 7
  · left
    refine ⟨_, lab_2 h2, ?_, Or.inr (Or.inr (Or.inl ⟨h2, rfl, gF_2 h2⟩))⟩
    rw [lab_2 h2, Nat.mod_mod_of_dvd _ (dvdN P)]
    exact mod_of (q := 2 * Q + 4 * i + 3) h2 (by rw [P.hK, P.hhu, P.hp]; ring) (by omega)
  by_cases h5 : x % p = 4 * a + 4
  · left
    refine ⟨_, lab_5 h5, ?_, Or.inr (Or.inr (Or.inr ⟨h5, by omega, by rw [gF_5 h5]; omega⟩))⟩
    rw [lab_5 h5, Nat.mod_mod_of_dvd _ (dvdN P)]
    exact st5 P h5
  by_cases hE : x % p % 2 = 0 ∧ x % p ≤ 4 * a + 6
  · right; left
    have hE2 : x % p ≤ 4 * a + 2 := by omega
    exact ⟨hE.1, hE2, hc, lab_E hE.1 hE2 hc, by rw [lab_E hE.1 hE2 hc, Nat.mod_mod_of_dvd _ (dvd1 P)],
      gF_E hE.1 hE2 hc⟩
  · right; right
    exact ⟨hE, h2, lab_dot hE h2, by rw [lab_dot hE h2, Nat.mod_mod_of_dvd _ (dvd2 P)], gF_dot hE h2⟩

/-- (G1) -/
lemma lab_succ (x : ℕ) : lab a p K hu (x + gF a p K hu x) = lab a p K hu x := by
  have hhu := P.hhu
  rcases gF_cases P x with ⟨hr, hg, hs⟩ | ⟨hr, hg, hs⟩ | ⟨hr, hg, hs⟩ | ⟨hr, hg, hs⟩ | ⟨h1, h2, h3, hg, hs⟩ |
    ⟨h1, h2, hg, hs⟩
  · rw [hg, lab_c hs, lab_3 hr, show x + K + (3 * K + 4 * hu) = x + (4 * K + 4 * hu) by omega, Nat.add_mod_right]
  · rw [hg, lab_2 hs, lab_c hr, show x + K + (2 * K + 4 * hu) = x + (3 * K + 4 * hu) by omega]
  · rw [hg, lab_5 hs, lab_2 hr,
      show x + (K + 2 * hu + (2 * a + 2)) + (K + 2 * hu - (2 * a + 2)) = x + (2 * K + 4 * hu) by omega]
  · rw [hg, lab_3 hs, lab_5 hr]
  · rw [hg, lab_E (by rw [hs]; exact h1) (by rw [hs]; exact h2) (by rw [hs]; exact h3), lab_E h1 h2 h3,
      Nat.add_mod_right]
  · rw [hg, lab_dot (by rw [hs]; exact h1) (by rw [hs]; exact h2), lab_dot h1 h2, Nat.add_mod_right]

/-- (G2) -/
lemma lab_gap (x d : ℕ) (hd0 : 0 < d) (hd : d < gF a p K hu x) : lab a p K hu (x + d) ≠ lab a p K hu x := by
  intro hl
  have hK := P.ha0
  have hhu := P.hhu
  have hp := P.hp
  have hres : lab a p K hu (x + d) % p = lab a p K hu x % p := by rw [hl]
  rcases lab_cases P x with ⟨o, e, r, hcl⟩ | ⟨h1, h2, h3, e, r, hg⟩ | ⟨h1, h2, e, r, hg⟩
  · rcases lab_cases P (x + d) with ⟨o', e', r', hcl'⟩ | ⟨h1', h2', h3', e', r', hg'⟩ | ⟨h1', h2', e', r', hg'⟩
    · rw [e, e'] at hl
      have := modeq3 (A := x) (u := d + o') (v := o) (by rw [← add_assoc]; exact hl)
      omega
    · omega
    · omega
  · rcases lab_cases P (x + d) with ⟨o', e', r', hcl'⟩ | ⟨h1', h2', h3', e', r', hg'⟩ | ⟨h1', h2', e', r', hg'⟩
    · omega
    · rw [e, e'] at hl
      have := modeq3 (A := x) (u := d) (v := 0) (by rw [add_zero]; exact hl)
      omega
    · omega
  · rcases lab_cases P (x + d) with ⟨o', e', r', hcl'⟩ | ⟨h1', h2', h3', e', r', hg'⟩ | ⟨h1', h2', e', r', hg'⟩
    · omega
    · omega
    · rw [e, e'] at hl
      have := modeq3 (A := x) (u := d) (v := 0) (by rw [add_zero]; exact hl)
      omega

/-- (G3) -/
lemma gF_ge (x : ℕ) : K ≤ gF a p K hu x := by
  have hhu := P.hhu
  rcases gF_cases P x with ⟨hr, hg, hs⟩ | ⟨hr, hg, hs⟩ | ⟨hr, hg, hs⟩ | ⟨hr, hg, hs⟩ | ⟨h1, h2, h3, hg, hs⟩ |
    ⟨h1, h2, hg, hs⟩ <;> omega

/-- (G4) and (G5) -/
lemma orbit (x : ℕ) :
    (4 * K + 4 * hu ≤ 2 * (gF a p K hu x + gF a p K hu (x + gF a p K hu x)
      + gF a p K hu (x + gF a p K hu x + gF a p K hu (x + gF a p K hu x)))) ∧
    (gF a p K hu x + (gF a p K hu (x + gF a p K hu x) + 0) = 4 * K + 4 * hu ∨
      gF a p K hu x + (gF a p K hu (x + gF a p K hu x) +
        (gF a p K hu (x + gF a p K hu x + gF a p K hu (x + gF a p K hu x)) +
        (gF a p K hu (x + gF a p K hu x + gF a p K hu (x + gF a p K hu x)
          + gF a p K hu (x + gF a p K hu x + gF a p K hu (x + gF a p K hu x))) + 0))) = 4 * K + 4 * hu) := by
  have hK := P.ha0
  have hhu := P.hhu
  rcases gF_cases P x with ⟨hr, hg, hs⟩ | ⟨hr, hg, hs⟩ | ⟨hr, hg, hs⟩ | ⟨hr, hg, hs⟩ | ⟨h1, h2, h3, hg, hs⟩ |
    ⟨h1, h2, hg, hs⟩
  · rw [gF_3 hr, gF_c (st3 P hr), gF_2 (stc P (st3 P hr)), gF_5 (st2 P (stc P (st3 P hr)))]
    omega
  · rw [gF_c hr, gF_2 (stc P hr), gF_5 (st2 P (stc P hr)), gF_3 (st5 P (st2 P (stc P hr)))]
    omega
  · rw [gF_2 hr, gF_5 (st2 P hr), gF_3 (st5 P (st2 P hr)), gF_c (st3 P (st5 P (st2 P hr)))]
    omega
  · rw [gF_5 hr, gF_3 (st5 P hr), gF_c (st3 P (st5 P hr)), gF_2 (stc P (st3 P (st5 P hr)))]
    omega
  · have e0 := gF_E (K := K) (hu := hu) h1 h2 h3
    have e1 : gF a p K hu (x + (K + hu)) = K + hu :=
      gF_E (by rw [stE P]; exact h1) (by rw [stE P]; exact h2) (by rw [stE P]; exact h3)
    have e2 : gF a p K hu (x + (K + hu) + (K + hu)) = K + hu :=
      gF_E (by rw [stE P, stE P]; exact h1) (by rw [stE P, stE P]; exact h2) (by rw [stE P, stE P]; exact h3)
    have e3 : gF a p K hu (x + (K + hu) + (K + hu) + (K + hu)) = K + hu :=
      gF_E (by rw [stE P, stE P, stE P]; exact h1) (by rw [stE P, stE P, stE P]; exact h2)
        (by rw [stE P, stE P, stE P]; exact h3)
    rw [e0, e1, e2, e3]
    omega
  · have e0 := gF_dot (K := K) (hu := hu) h1 h2
    have e1 : gF a p K hu (x + (2 * K + 2 * hu)) = 2 * K + 2 * hu :=
      gF_dot (by rw [stD P]; exact h1) (by rw [stD P]; exact h2)
    have e2 : gF a p K hu (x + (2 * K + 2 * hu) + (2 * K + 2 * hu)) = 2 * K + 2 * hu :=
      gF_dot (by rw [stD P, stD P]; exact h1) (by rw [stD P, stD P]; exact h2)
    rw [e0, e1, e2]
    omega

/-! ### the set of labels -/

def labS (a p K hu : ℕ) : Finset ℕ :=
  {m ∈ range (4 * K + 4 * hu) | m % p = 4 * a + 6} ∪
    {m ∈ range (K + hu) | m % p % 2 = 0 ∧ m % p ≤ 4 * a + 2 ∧ m % p ≠ 2 * a + 2} ∪
    {m ∈ range (2 * K + 2 * hu) | ¬(m % p % 2 = 0 ∧ m % p ≤ 4 * a + 6) ∧ m % p ≠ 4 * a + 7}

lemma lab_mem (x : ℕ) : lab a p K hu x ∈ labS a p K hu := by
  have hpos : 0 < K + hu := by have := P.hhu; omega
  unfold labS
  rcases lab_cases P x with ⟨o, e, r, hcl⟩ | ⟨h1, h2, h3, e, r, hg⟩ | ⟨h1, h2, e, r, hg⟩
  · apply mem_union_left; apply mem_union_left
    simp only [mem_filter, mem_range]
    exact ⟨by rw [e]; exact Nat.mod_lt _ (by omega), r⟩
  · apply mem_union_left; apply mem_union_right
    simp only [mem_filter, mem_range]
    exact ⟨by rw [e]; exact Nat.mod_lt _ hpos, by rw [r]; exact ⟨h1, h2, h3⟩⟩
  · apply mem_union_right
    simp only [mem_filter, mem_range]
    exact ⟨by rw [e]; exact Nat.mod_lt _ (by omega), by rw [r]; exact ⟨h1, h2⟩⟩

lemma bE : cP (fun x => x % p % 2 = 0 ∧ x % p ≤ 4 * a + 2 ∧ x % p ≠ 2 * a + 2) 0 p ≤ 2 * a + 1 := by
  have hp := P.hp
  have h1 : cP (fun x => x % p % 2 = 0 ∧ x % p ≤ 4 * a + 2 ∧ x % p ≠ 2 * a + 2) 0 p
      + cP (fun x => x % p = 2 * a + 2) 0 p ≤ cP (fun x => x % p % 2 = 0 ∧ x % p ≤ 4 * a + 2) 0 p := by
    rw [cP_eq_sum, cP_eq_sum, cP_eq_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro m _
    split_ifs <;> omega
  have h2 : 1 ≤ cP (fun x => x % p = 2 * a + 2) 0 p := by
    rw [cP]
    exact card_pos.mpr ⟨2 * a + 2, by simp only [mem_filter, mem_range]; exact ⟨by omega, by
      rw [zero_add]; exact Nat.mod_eq_of_lt (by omega)⟩⟩
  have h3 : cP (fun x => x % p % 2 = 0 ∧ x % p ≤ 4 * a + 2) 0 p ≤ 2 * a + 2 := by
    rw [show p = (4 * a + 3) + 6 by omega, cP_add]
    have e1 : cP (fun x => x % (4 * a + 3 + 6) % 2 = 0 ∧ x % (4 * a + 3 + 6) ≤ 4 * a + 2) 0 (4 * a + 3)
        = cP (fun x => x % 2 = 0) 0 (4 * a + 3) := by
      apply cP_congr
      intro m hm
      rw [Nat.mod_eq_of_lt (by omega : 0 + m < 4 * a + 3 + 6)]
      omega
    have e2 : cP (fun x => x % (4 * a + 3 + 6) % 2 = 0 ∧ x % (4 * a + 3 + 6) ≤ 4 * a + 2) (0 + (4 * a + 3)) 6
        = 0 := by
      apply cP_eq_zero
      intro m hm h
      rw [Nat.mod_eq_of_lt (by omega : 0 + (4 * a + 3) + m < 4 * a + 3 + 6)] at h
      omega
    rw [e1, e2, cP_even]
    omega
  omega

lemma bD : cP (fun x => ¬(x % p % 2 = 0 ∧ x % p ≤ 4 * a + 6) ∧ x % p ≠ 4 * a + 7) 0 p ≤ 2 * a + 4 := by
  have hp := P.hp
  have hor := cP_or_le (Q := fun x => ¬(x % p % 2 = 0 ∧ x % p ≤ 4 * a + 6) ∧ x % p ≠ 4 * a + 7)
    (Q1 := fun x => x % p % 2 = 1 ∧ x % p ≤ 4 * a + 5) (Q2 := fun x => x % p = 4 * a + 8)
    (fun x h => by have := Nat.mod_lt x (by omega : 0 < p); omega) 0 p
  have h8 := cP_res_le_one p (4 * a + 8) 0 p le_rfl
  have h3 : cP (fun x => x % p % 2 = 1 ∧ x % p ≤ 4 * a + 5) 0 p ≤ 2 * a + 3 := by
    rw [show p = (4 * a + 6) + 3 by omega, cP_add]
    have e1 : cP (fun x => x % (4 * a + 6 + 3) % 2 = 1 ∧ x % (4 * a + 6 + 3) ≤ 4 * a + 5) 0 (4 * a + 6)
        = cP (fun x => x % 2 = 1) 0 (4 * a + 6) := by
      apply cP_congr
      intro m hm
      rw [Nat.mod_eq_of_lt (by omega : 0 + m < 4 * a + 6 + 3)]
      omega
    have e2 : cP (fun x => x % (4 * a + 6 + 3) % 2 = 1 ∧ x % (4 * a + 6 + 3) ≤ 4 * a + 5) (0 + (4 * a + 6)) 3
        = 0 := by
      apply cP_eq_zero
      intro m hm h
      rw [Nat.mod_eq_of_lt (by omega : 0 + (4 * a + 6) + m < 4 * a + 6 + 3)] at h
      omega
    rw [e1, e2, cP_odd]
    omega
  omega

lemma card_labS : (labS a p K hu).card ≤ (6 * a + 13) * (Q + i + 1) := by
  have hA := hKhu P
  have eN : 4 * K + 4 * hu = p * (4 * (Q + i + 1)) := by
    rw [show 4 * K + 4 * hu = 4 * (K + hu) by ring, hA]; ring
  have e2 : 2 * K + 2 * hu = p * (2 * (Q + i + 1)) := by
    rw [show 2 * K + 2 * hu = 2 * (K + hu) by ring, hA]; ring
  unfold labS
  refine (card_union_le _ _).trans ?_
  refine (Nat.add_le_add_right (card_union_le _ _) _).trans ?_
  rw [card_eq_cP (fun m => m % p = 4 * a + 6), card_eq_cP (fun m => m % p % 2 = 0 ∧ m % p ≤ 4 * a + 2 ∧ m % p ≠ 2 * a + 2),
    card_eq_cP (fun m => ¬(m % p % 2 = 0 ∧ m % p ≤ 4 * a + 6) ∧ m % p ≠ 4 * a + 7), eN, hA, e2,
    cP_full (by intro x; simp only [Nat.add_mod_right]), cP_full (by intro x; simp only [Nat.add_mod_right]),
    cP_full (by intro x; simp only [Nat.add_mod_right])]
  have b6 := cP_res_le_one p (4 * a + 6) 0 p le_rfl
  have h6 := Nat.mul_le_mul_left (4 * (Q + i + 1)) b6
  have hE := Nat.mul_le_mul_left (Q + i + 1) (bE P)
  have hD := Nat.mul_le_mul_left (2 * (Q + i + 1)) (bD P)
  nlinarith [h6, hE, hD]

lemma dot_orbit {x : ℕ} (h1 : ¬(x % p % 2 = 0 ∧ x % p ≤ 4 * a + 6)) (h2 : x % p ≠ 4 * a + 7) :
    gF a p K hu x + (gF a p K hu (x + gF a p K hu x) + 0) = 4 * K + 4 * hu := by
  have e0 := gF_dot (K := K) (hu := hu) h1 h2
  have e1 : gF a p K hu (x + (2 * K + 2 * hu)) = 2 * K + 2 * hu :=
    gF_dot (by rw [stD P]; exact h1) (by rw [stD P]; exact h2)
  rw [e0, e1]
  omega

/-- **The word of family 10** (and three of its coordinates that are used exactly twice). -/
theorem word_exists (n : ℕ) (hn : (6 * a + 13) * (Q + i + 1) ≤ n) :
    ∃ T : ℕ → Fin n, IsCoilWord (K - 1) (4 * K + 4 * hu) T ∧
      ∃ C : Finset (Fin n), #C = 3 ∧ ∀ c ∈ C, cnt T 0 (4 * K + 4 * hu) c = 2 := by
  have hK := P.ha0
  have hhu := P.hhu
  have hp := P.hp
  have hcard : (labS a p K hu).card ≤ n := (card_labS P).trans hn
  let T : ℕ → Fin n := fun x => Fin.castLE hcard ((labS a p K hu).equivFin ⟨lab a p K hu x, lab_mem P x⟩)
  have hT1 : ∀ x y, T x = T y → lab a p K hu x = lab a p K hu y := by
    intro x y h
    have h1 := Fin.castLE_injective hcard h
    have h2 := (labS a p K hu).equivFin.injective h1
    exact congrArg Subtype.val h2
  have hT2 : ∀ x y, lab a p K hu x = lab a p K hu y → T x = T y := by
    intro x y h
    have : (⟨lab a p K hu x, lab_mem P x⟩ : labS a p K hu) = ⟨lab a p K hu y, lab_mem P y⟩ := Subtype.ext h
    show Fin.castLE hcard ((labS a p K hu).equivFin ⟨lab a p K hu x, lab_mem P x⟩)
      = Fin.castLE hcard ((labS a p K hu).equivFin ⟨lab a p K hu y, lab_mem P y⟩)
    rw [this]
  have G1 : ∀ x, T (x + gF a p K hu x) = T x := fun x => hT2 _ _ (lab_succ P x)
  have G2 : ∀ x d, 0 < d → d < gF a p K hu x → T (x + d) ≠ T x :=
    fun x d h0 hd h => lab_gap P x d h0 hd (hT1 _ _ h)
  have G0 : ∀ x, 1 ≤ gF a p K hu x := fun x => by have := gF_ge P x; omega
  have hcoil : IsCoilWord (K - 1) (4 * K + 4 * hu) T := by
    refine isCoilWord_of_gaps (gF a p K hu) G1 G2 (by omega) ?_ (fun x => (orbit P x).1)
      (fun x => (orbit P x).2) ?_
    · intro x
      have := gF_ge P x
      omega
    · intro t L h1 h2
      have := count_le P t L (by omega) (by omega)
      unfold Wc at this
      exact this
  refine ⟨T, hcoil, {T 1, T 3, T 5}, ?_, ?_⟩
  · have m1 : 1 % p = 1 := Nat.mod_eq_of_lt (by omega)
    have m3 : 3 % p = 3 := Nat.mod_eq_of_lt (by omega)
    have m5 : 5 % p = 5 := Nat.mod_eq_of_lt (by omega)
    have l1 : lab a p K hu 1 = 1 := by
      rw [lab_dot (by rw [m1]; omega) (by rw [m1]; omega)]; exact Nat.mod_eq_of_lt (by omega)
    have l3 : lab a p K hu 3 = 3 := by
      rw [lab_dot (by rw [m3]; omega) (by rw [m3]; omega)]; exact Nat.mod_eq_of_lt (by omega)
    have l5 : lab a p K hu 5 = 5 := by
      rw [lab_dot (by rw [m5]; omega) (by rw [m5]; omega)]; exact Nat.mod_eq_of_lt (by omega)
    rw [card_eq_three]
    refine ⟨T 1, T 3, T 5, ?_, ?_, ?_, rfl⟩
    · intro h; have := hT1 _ _ h; omega
    · intro h; have := hT1 _ _ h; omega
    · intro h; have := hT1 _ _ h; omega
  · intro c hc
    have m1 : 1 % p = 1 := Nat.mod_eq_of_lt (by omega)
    have m3 : 3 % p = 3 := Nat.mod_eq_of_lt (by omega)
    have m5 : 5 % p = 5 := Nat.mod_eq_of_lt (by omega)
    simp only [mem_insert, mem_singleton] at hc
    rcases hc with rfl | rfl | rfl
    · exact cnt_two_of_gaps (gF a p K hu) G1 G2 G0 hcoil.per 1 (dot_orbit P (by rw [m1]; omega) (by rw [m1]; omega))
    · exact cnt_two_of_gaps (gF a p K hu) G1 G2 G0 hcoil.per 3 (dot_orbit P (by rw [m3]; omega) (by rw [m3]; omega))
    · exact cnt_two_of_gaps (gF a p K hu) G1 G2 G0 hcoil.per 5 (dot_orbit P (by rw [m5]; omega) (by rw [m5]; omega))

end Fam10

end Coil

#print axioms Coil.Fam10.word_exists
