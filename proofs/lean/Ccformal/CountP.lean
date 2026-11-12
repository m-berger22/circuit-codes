import Ccformal.GapCriterion

/-!
# Counting positions with a (periodic) property in a window: tools for the family proofs
-/

open Finset

namespace Coil

set_option linter.unusedSectionVars false
set_option linter.deprecated false

/-- number of positions `x ∈ [t, t+L)` with `Q x` -/
def cP (Q : ℕ → Prop) [DecidablePred Q] (t L : ℕ) : ℕ := #{m ∈ range L | Q (t + m)}

section
variable (Q Q1 Q2 : ℕ → Prop) [DecidablePred Q] [DecidablePred Q1] [DecidablePred Q2]

lemma cP_eq_sum (t L : ℕ) : cP Q t L = ∑ m ∈ range L, if Q (t + m) then 1 else 0 := by
  rw [cP, card_filter]

lemma cP_add (t a b : ℕ) : cP Q t (a + b) = cP Q t a + cP Q (t + a) b := by
  simp_rw [cP_eq_sum, sum_range_add, add_assoc]

lemma cP_zero (t : ℕ) : cP Q t 0 = 0 := by simp [cP]

lemma cP_one (t : ℕ) : cP Q t 1 = if Q t then 1 else 0 := by
  rw [cP_eq_sum, sum_range_one, add_zero]

lemma cP_succ (t L : ℕ) : cP Q t (L + 1) = cP Q t L + if Q (t + L) then 1 else 0 := by
  rw [cP_add, cP_one]

lemma cP_cons (t L : ℕ) : cP Q t (1 + L) = (if Q t then 1 else 0) + cP Q (t + 1) L := by
  rw [cP_add, cP_one]

lemma cP_two (t : ℕ) : cP Q t 2 = (if Q t then 1 else 0) + if Q (t + 1) then 1 else 0 := by
  rw [show 2 = 1 + 1 by rfl, cP_cons, cP_one]

lemma cP_le (t L : ℕ) : cP Q t L ≤ L := by
  rw [cP]
  exact (card_filter_le _ _).trans (by simp)

variable {Q Q1 Q2}

lemma cP_mono (h : ∀ x, Q x → Q1 x) (t L : ℕ) : cP Q t L ≤ cP Q1 t L := by
  apply card_le_card
  intro m hm
  simp only [mem_filter] at hm ⊢
  exact ⟨hm.1, h _ hm.2⟩

lemma cP_or_le (h : ∀ x, Q x → Q1 x ∨ Q2 x) (t L : ℕ) : cP Q t L ≤ cP Q1 t L + cP Q2 t L := by
  rw [cP_eq_sum, cP_eq_sum, cP_eq_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro m _
  have := h (t + m)
  split_ifs <;> first | omega | tauto

lemma cP_congr {t L : ℕ} (h : ∀ m, m < L → (Q (t + m) ↔ Q1 (t + m))) : cP Q t L = cP Q1 t L := by
  rw [cP_eq_sum, cP_eq_sum]
  apply sum_congr rfl
  intro m hm
  simp only [h m (mem_range.mp hm)]

lemma cP_eq_zero {t L : ℕ} (h : ∀ m, m < L → ¬ Q (t + m)) : cP Q t L = 0 := by
  rw [cP, card_eq_zero, filter_eq_empty_iff]
  intro m hm
  exact h m (mem_range.mp hm)

/-- no two adjacent members: at most half (rounded up) -/
lemma cP_le_half (h : ∀ x, ¬(Q x ∧ Q (x + 1))) (t L : ℕ) : cP Q t L ≤ (L + 1) / 2 := by
  induction L using Nat.strong_induction_on generalizing t with
  | _ L ih =>
    match L, ih with
    | 0, _ => simp [cP]
    | 1, _ => rw [cP_one]; split_ifs <;> omega
    | L + 2, ih =>
      have h1 := ih L (by omega) (t + 1 + 1)
      rw [show L + 2 = 1 + (1 + L) by omega, cP_cons, cP_cons]
      have hh := h t
      split_ifs <;> first | omega | (exfalso; exact hh ⟨by assumption, by assumption⟩)

/-- no two adjacent non-members: at least half (rounded down) -/
lemma cP_ge_half (h : ∀ x, Q x ∨ Q (x + 1)) (t L : ℕ) : L / 2 ≤ cP Q t L := by
  induction L using Nat.strong_induction_on generalizing t with
  | _ L ih =>
    match L, ih with
    | 0, _ => simp
    | 1, _ => simp
    | L + 2, ih =>
      have h1 := ih L (by omega) (t + 1 + 1)
      rw [show L + 2 = 1 + (1 + L) by omega, cP_cons, cP_cons]
      have hh := h t
      split_ifs <;> first | omega | (exfalso; tauto)

variable {p : ℕ} (hQ : ∀ x, Q (x + p) ↔ Q x)
include hQ

lemma cP_shift (t L : ℕ) : cP Q (t + p) L = cP Q t L := by
  rw [cP_eq_sum, cP_eq_sum]
  apply sum_congr rfl
  intro m _
  rw [show t + p + m = t + m + p by omega]
  simp only [hQ (t + m)]

lemma cP_shift_mul (t m L : ℕ) : cP Q (t + p * m) L = cP Q t L := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.mul_succ, ← add_assoc, cP_shift hQ, ih]

lemma cP_mod (t L : ℕ) : cP Q t L = cP Q (t % p) L := by
  conv_lhs => rw [← Nat.mod_add_div t p]
  exact cP_shift_mul hQ _ _ _

lemma cP_period (t : ℕ) : cP Q t p = cP Q 0 p := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have h1 := cP_cons Q t p
    have h2 := cP_succ Q t p
    have h3 : (if Q (t + p) then 1 else 0) = (if Q t then (1 : ℕ) else 0) := by simp only [hQ t]
    rw [Nat.add_comm 1 p] at h1
    omega

lemma cP_full (t m : ℕ) : cP Q t (p * m) = m * cP Q 0 p := by
  induction m generalizing t with
  | zero => simp [cP]
  | succ m ih => rw [Nat.mul_succ, cP_add, ih, cP_period hQ (t + p * m)]; ring

end

/-! ## residues -/

lemma res_add (p x m : ℕ) (hp : 0 < p) (hm : m ≤ p) :
    x % p < p ∧ (x + m) % p < p ∧ ((x + m) % p = x % p + m ∨ (x + m) % p + p = x % p + m) := by
  have h1 := Nat.mod_lt x hp
  have h2 := Nat.mod_lt (x + m) hp
  refine ⟨h1, h2, ?_⟩
  have e : (x + m) % p = (x % p + m) % p := by
    conv_lhs => rw [← Nat.mod_add_div x p, show x % p + p * (x / p) + m = x % p + m + p * (x / p) by omega,
      Nat.add_mul_mod_self_left]
  by_cases h : x % p + m < p
  · left
    rw [e, Nat.mod_eq_of_lt h]
  · right
    rw [e, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

/-- `x ≡ r`, `r + d = R + p q`, `R < p`  ⟹  `x + d ≡ R` -/
lemma mod_of {p x r d R q : ℕ} (hx : x % p = r) (h : r + d = R + p * q) (hR : R < p) : (x + d) % p = R := by
  have h1 := Nat.mod_add_div x p
  rw [show x + d = R + p * (x / p + q) by rw [mul_add]; omega, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hR]

lemma cP_res_le_one (p r t L : ℕ) (hL : L ≤ p) : cP (fun x => x % p = r) t L ≤ 1 := by
  rw [cP, card_le_one]
  intro m hm m' hm'
  simp only [mem_filter, mem_range] at hm hm'
  by_contra hne
  have e : (t + m) % p = (t + m') % p := by rw [hm.2, hm'.2]
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have := Nat.sub_mod_eq_zero_of_mod_eq e.symm
    rw [show t + m' - (t + m) = m' - m by omega, Nat.mod_eq_of_lt (by omega)] at this
    omega
  · have := Nat.sub_mod_eq_zero_of_mod_eq e
    rw [show t + m - (t + m') = m - m' by omega, Nat.mod_eq_of_lt (by omega)] at this
    omega

lemma cP_even (n : ℕ) : cP (fun x => x % 2 = 0) 0 n = (n + 1) / 2 := by
  induction n with
  | zero => simp [cP]
  | succ n ih =>
    rw [cP_succ, ih, zero_add]
    split_ifs <;> omega

/-- splitting a filtered range -/
lemma card_split (W : ℕ → Prop) [DecidablePred W] (A B : ℕ) :
    #{m ∈ range (A + B) | W m} = #{m ∈ range A | W m} + #{m ∈ range B | W (A + m)} := by
  simp_rw [card_filter, sum_range_add]

lemma card_le_cP {W Q : ℕ → Prop} [DecidablePred W] [DecidablePred Q] (t off A : ℕ)
    (h : ∀ m, m < A → W (off + m) → Q (t + off + m)) : #{m ∈ range A | W (off + m)} ≤ cP Q (t + off) A := by
  apply card_le_card
  intro m hm
  simp only [mem_filter, mem_range] at hm ⊢
  exact ⟨hm.1, h m hm.1 hm.2⟩

lemma card_filter_zero {W : ℕ → Prop} [DecidablePred W] (off A : ℕ) (h : ∀ m, m < A → ¬ W (off + m)) :
    #{m ∈ range A | W (off + m)} = 0 := by
  rw [card_eq_zero, filter_eq_empty_iff]
  intro m hm
  exact h m (mem_range.mp hm)

end Coil
