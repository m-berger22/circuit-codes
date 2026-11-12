import Ccformal.CountP

/-!
# Family 6 × m (PROOF9, Theorem 18; m = 1: Theorem 13): the counting part

`p = 4q`, `q = c + 2 ≥ 2`, `m = 2μ + 1` odd; `K = m p (p+2)/4`, `u = m p = 2 hu`, `N = 4K + 2u`.
Period-`p` gap function `gF6` on positions:

    residue 1 : K        residue 2q+1 : K+1        residue 2 : K + 2u - 2        residue 2q : K+1          (one chain)
    E residues (even 4..2q-2, odd 2q+3..p-1) : K + u/2 = N/4          all other residues (dots) : N/2

`count_le`: in every window of length `L`, `K ≤ L ≤ N/2`, at most `(L-K+1)/2` start positions are counted
(chord inside, triple not).  START-position proof as for family 10; zones from the right end of the window:
last `u/2` positions: only residues 1, 2q, 2q+1; next `3u/2 - 2`: all F except residue 2; beyond: all F.
Hypothesis `c ≥ 1 ∨ μ ≥ 1`: the single case (p, m) = (8, 1) is the code (33,19,96) (Values/K_33_19.lean).
-/

open Finset

namespace Coil

namespace Fam6

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedVariables false

abbrev E6 (c p x : ℕ) : Prop :=
  (x % p % 2 = 0 ∧ 4 ≤ x % p ∧ x % p ≤ 2 * c + 2) ∨ (x % p % 2 = 1 ∧ 2 * c + 7 ≤ x % p)

/-- the gap function -/
def gF (c p K hu : ℕ) (x : ℕ) : ℕ :=
  if x % p = 1 then K
  else if x % p = 2 * c + 5 then K + 1
  else if x % p = 2 then K + 4 * hu - 2
  else if x % p = 2 * c + 4 then K + 1
  else if E6 c p x then K + hu
  else 2 * K + 2 * hu

abbrev G0 (c p x : ℕ) : Prop := x % p = 1 ∨ x % p = 2 ∨ x % p = 2 * c + 4 ∨ x % p = 2 * c + 5 ∨ E6 c p x
abbrev GZ2 (c p x : ℕ) : Prop := x % p = 1 ∨ x % p = 2 * c + 4 ∨ x % p = 2 * c + 5 ∨ E6 c p x
abbrev GZ1 (c p x : ℕ) : Prop := x % p = 1 ∨ x % p = 2 * c + 4 ∨ x % p = 2 * c + 5
abbrev Gp (c p x : ℕ) : Prop := x % p = 2 ∨ x % p = 2 * c + 5 ∨ E6 c p x
abbrev I1 (c p x : ℕ) : Prop := x % p = 1 ∨ x % p = 2 * c + 4 ∨ x % p = 2 * c + 6

/-- the parameters -/
structure Par (c μ p K hu Qk q3 : ℕ) : Prop where
  hp : p = 4 * c + 8
  hK : K = p * Qk + (2 * c + 4)
  hhu : hu = p * μ + (2 * c + 4)
  ha0 : K + 2 = 4 * hu + (p * q3 + (2 * c + 6))
  hZ : 2 * (q3 * (2 * c + 5) + (3 * μ + 1) * (2 * c + 4) + 3 * μ + (2 * c + 6)) = K
  hs : 1 ≤ c ∨ 1 ≤ μ

variable {c μ p K hu Qk q3 : ℕ} (P : Par c μ p K hu Qk q3)

lemma gF_congr {x y : ℕ} (h : x % p = y % p) : gF c p K hu x = gF c p K hu y := by
  unfold gF E6; rw [h]

lemma gF_1 {x : ℕ} (h : x % p = 1) : gF c p K hu x = K := by
  unfold gF; rw [if_pos h]

lemma gF_b {x : ℕ} (h : x % p = 2 * c + 5) : gF c p K hu x = K + 1 := by
  unfold gF; rw [if_neg (by omega), if_pos h]

lemma gF_2 {x : ℕ} (h : x % p = 2) : gF c p K hu x = K + 4 * hu - 2 := by
  unfold gF; rw [if_neg (by omega), if_neg (by omega), if_pos h]

lemma gF_a {x : ℕ} (h : x % p = 2 * c + 4) : gF c p K hu x = K + 1 := by
  unfold gF; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h]

lemma gF_E {x : ℕ} (h : E6 c p x) : gF c p K hu x = K + hu := by
  have h' := h
  unfold E6 at h'
  unfold gF; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h]

lemma gF_dot {x : ℕ} (h1 : x % p ≠ 1) (h2 : x % p ≠ 2 * c + 5) (h3 : x % p ≠ 2) (h4 : x % p ≠ 2 * c + 4)
    (h : ¬ E6 c p x) : gF c p K hu x = 2 * K + 2 * hu := by
  unfold gF; rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h]

lemma card_le_cP' {W Q : ℕ → Prop} [DecidablePred W] [DecidablePred Q] (τ A : ℕ)
    (h : ∀ m, m < A → W m → Q (τ + m)) : #{m ∈ range A | W m} ≤ cP Q τ A := by
  apply card_le_card
  intro m hm
  simp only [mem_filter, mem_range] at hm ⊢
  exact ⟨hm.1, h m hm.1 hm.2⟩

lemma card_zero' {W : ℕ → Prop} [DecidablePred W] (A : ℕ) (h : ∀ m, m < A → ¬ W m) :
    #{m ∈ range A | W m} = 0 := by
  rw [card_eq_zero, filter_eq_empty_iff]
  intro m hm
  exact h m (mem_range.mp hm)

lemma cP_add_le {Q Q1 Q2 : ℕ → Prop} [DecidablePred Q] [DecidablePred Q1] [DecidablePred Q2]
    (h : ∀ x, (Q1 x → Q x) ∧ (Q2 x → Q x) ∧ ¬(Q1 x ∧ Q2 x)) (t L : ℕ) :
    cP Q1 t L + cP Q2 t L ≤ cP Q t L := by
  rw [cP_eq_sum, cP_eq_sum, cP_eq_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro m _
  have := h (t + m)
  split_ifs <;> first | omega | (exfalso; tauto)

include P

lemma hKhu : K + hu = p * (Qk + μ + 1) := by rw [P.hK, P.hhu, P.hp]; ring

lemma st1 {x : ℕ} (h : x % p = 1) : (x + K) % p = 2 * c + 5 :=
  mod_of (q := Qk) h (by rw [P.hK]; omega) (by have := P.hp; omega)

lemma stb {x : ℕ} (h : x % p = 2 * c + 5) : (x + (K + 1)) % p = 2 :=
  mod_of (q := Qk + 1) h (by rw [P.hK, P.hp]; ring) (by have := P.hp; omega)

lemma st2 {x : ℕ} (h : x % p = 2) : (x + (K + 4 * hu - 2)) % p = 2 * c + 4 := by
  have e : K + 4 * hu - 2 = p * Qk + 4 * (p * μ) + (10 * c + 18) := by rw [P.hK, P.hhu]; omega
  exact mod_of (q := Qk + 4 * μ + 2) h (by rw [e, P.hp]; ring) (by have := P.hp; omega)

lemma sta {x : ℕ} (h : x % p = 2 * c + 4) : (x + (K + 1)) % p = 1 :=
  mod_of (q := Qk + 1) h (by rw [P.hK, P.hp]; ring) (by have := P.hp; omega)

lemma stE (y : ℕ) : (y + (K + hu)) % p = y % p := by
  rw [hKhu P, Nat.add_mul_mod_self_left]

lemma stD (y : ℕ) : (y + (2 * K + 2 * hu)) % p = y % p := by
  rw [show 2 * K + 2 * hu = p * (2 * (Qk + μ + 1)) by
    rw [show 2 * K + 2 * hu = 2 * (K + hu) by ring, hKhu P]; ring, Nat.add_mul_mod_self_left]

/-- gap and next gap, by class -/
lemma gF_two (x : ℕ) :
    (x % p = 1 ∧ gF c p K hu x = K ∧ gF c p K hu (x + gF c p K hu x) = K + 1) ∨
    (x % p = 2 * c + 5 ∧ gF c p K hu x = K + 1 ∧ gF c p K hu (x + gF c p K hu x) = K + 4 * hu - 2) ∨
    (x % p = 2 ∧ gF c p K hu x = K + 4 * hu - 2 ∧ gF c p K hu (x + gF c p K hu x) = K + 1) ∨
    (x % p = 2 * c + 4 ∧ gF c p K hu x = K + 1 ∧ gF c p K hu (x + gF c p K hu x) = K) ∨
    (E6 c p x ∧ gF c p K hu x = K + hu ∧ gF c p K hu (x + gF c p K hu x) = K + hu) ∨
    (x % p ≠ 1 ∧ x % p ≠ 2 * c + 5 ∧ x % p ≠ 2 ∧ x % p ≠ 2 * c + 4 ∧ ¬ E6 c p x ∧
      gF c p K hu x = 2 * K + 2 * hu ∧ gF c p K hu (x + gF c p K hu x) = 2 * K + 2 * hu) := by
  by_cases h1 : x % p = 1
  · left; exact ⟨h1, gF_1 h1, by rw [gF_1 h1]; exact gF_b (st1 P h1)⟩
  by_cases hb : x % p = 2 * c + 5
  · right; left; exact ⟨hb, gF_b hb, by rw [gF_b hb]; exact gF_2 (stb P hb)⟩
  by_cases h2 : x % p = 2
  · right; right; left; exact ⟨h2, gF_2 h2, by rw [gF_2 h2]; exact gF_a (st2 P h2)⟩
  by_cases ha : x % p = 2 * c + 4
  · right; right; right; left; exact ⟨ha, gF_a ha, by rw [gF_a ha]; exact gF_1 (sta P ha)⟩
  by_cases hE : E6 c p x
  · right; right; right; right; left
    exact ⟨hE, gF_E hE, by rw [gF_E hE, gF_congr (stE P x)]; exact gF_E hE⟩
  · right; right; right; right; right
    exact ⟨h1, hb, h2, ha, hE, gF_dot h1 hb h2 ha hE, by
      rw [gF_dot h1 hb h2 ha hE, gF_congr (stD P x)]; exact gF_dot h1 hb h2 ha hE⟩

/-- the 'counted' start positions of the window `[t, t+L)` -/
def Wc (c p K hu t L m : ℕ) : Prop :=
  gF c p K hu (t + m) ≤ L - 1 - m ∧
    L - 1 - m < gF c p K hu (t + m) + gF c p K hu (t + m + gF c p K hu (t + m))

instance (c p K hu t L : ℕ) : DecidablePred (Wc c p K hu t L) := by
  intro m; unfold Wc; infer_instance

lemma Wc_class {t L m : ℕ} (hL : L ≤ 2 * K + 2 * hu) (hm : m < L) (h : Wc c p K hu t L m) :
    ((t + m) % p = 1 ∧ K ≤ L - 1 - m ∧ L - 1 - m ≤ 2 * K) ∨
    ((t + m) % p = 2 * c + 5 ∧ K + 1 ≤ L - 1 - m) ∨
    ((t + m) % p = 2 ∧ K + 4 * hu ≤ L - 1 - m + 2) ∨
    ((t + m) % p = 2 * c + 4 ∧ K + 1 ≤ L - 1 - m ∧ L - 1 - m ≤ 2 * K) ∨
    (E6 c p (t + m) ∧ K + hu ≤ L - 1 - m) := by
  have hhu := P.hhu
  unfold Wc at h
  rcases gF_two P (t + m) with ⟨hr, hg, hs⟩ | ⟨hr, hg, hs⟩ | ⟨hr, hg, hs⟩ | ⟨hr, hg, hs⟩ | ⟨hr, hg, hs⟩ |
    ⟨h1, h2, h3, h4, h5, hg, hs⟩ <;> rw [hs, hg] at h
  · left; omega
  · right; left; omega
  · right; right; left; omega
  · right; right; right; left; omega
  · right; right; right; right; exact ⟨hr, by omega⟩
  · omega

lemma perG0 : ∀ x, G0 c p (x + p) ↔ G0 c p x := by intro x; unfold G0 E6; rw [Nat.add_mod_right]
lemma perGZ2 : ∀ x, GZ2 c p (x + p) ↔ GZ2 c p x := by intro x; unfold GZ2 E6; rw [Nat.add_mod_right]
lemma perGZ1 : ∀ x, GZ1 c p (x + p) ↔ GZ1 c p x := by intro x; unfold GZ1; rw [Nat.add_mod_right]

/-! ### counts per period -/

lemma cE : cP (E6 c p) 0 p ≤ 2 * c + 1 := by
  have hp := P.hp
  have hor := cP_or_le (Q := E6 c p) (Q1 := fun x => x % p % 2 = 0 ∧ 4 ≤ x % p ∧ x % p ≤ 2 * c + 2)
    (Q2 := fun x => x % p % 2 = 1 ∧ 2 * c + 7 ≤ x % p) (fun x h => h) 0 p
  have h1 : cP (fun x => x % p % 2 = 0 ∧ 4 ≤ x % p ∧ x % p ≤ 2 * c + 2) 0 p ≤ c := by
    rw [show p = 4 + ((2 * c) + (2 * c + 4)) by omega, cP_add, cP_add]
    have e1 : cP (fun x => x % (4 + ((2 * c) + (2 * c + 4))) % 2 = 0 ∧ 4 ≤ x % (4 + ((2 * c) + (2 * c + 4)))
        ∧ x % (4 + ((2 * c) + (2 * c + 4))) ≤ 2 * c + 2) 0 4 = 0 := by
      apply cP_eq_zero
      intro m hm h
      rw [Nat.mod_eq_of_lt (by omega : 0 + m < 4 + ((2 * c) + (2 * c + 4)))] at h
      omega
    have e2 : cP (fun x => x % (4 + ((2 * c) + (2 * c + 4))) % 2 = 0 ∧ 4 ≤ x % (4 + ((2 * c) + (2 * c + 4)))
        ∧ x % (4 + ((2 * c) + (2 * c + 4))) ≤ 2 * c + 2) (0 + 4) (2 * c)
        ≤ cP (fun x => x % 2 = 0) (0 + 4) (2 * c) := by
      rw [cP_eq_sum, cP_eq_sum]
      apply sum_le_sum
      intro m hm
      rw [mem_range] at hm
      rw [Nat.mod_eq_of_lt (by omega : 0 + 4 + m < 4 + ((2 * c) + (2 * c + 4)))]
      split_ifs <;> omega
    have e3 : cP (fun x => x % (4 + ((2 * c) + (2 * c + 4))) % 2 = 0 ∧ 4 ≤ x % (4 + ((2 * c) + (2 * c + 4)))
        ∧ x % (4 + ((2 * c) + (2 * c + 4))) ≤ 2 * c + 2) (0 + 4 + (2 * c)) (2 * c + 4) = 0 := by
      apply cP_eq_zero
      intro m hm h
      rw [Nat.mod_eq_of_lt (by omega : 0 + 4 + (2 * c) + m < 4 + ((2 * c) + (2 * c + 4)))] at h
      omega
    have e4 := cP_le_half (Q := fun x => x % 2 = 0) (fun x ⟨a, b⟩ => by omega) (0 + 4) (2 * c)
    omega
  have h2 : cP (fun x => x % p % 2 = 1 ∧ 2 * c + 7 ≤ x % p) 0 p ≤ c + 1 := by
    rw [show p = (2 * c + 7) + (2 * c + 1) by omega, cP_add]
    have e1 : cP (fun x => x % ((2 * c + 7) + (2 * c + 1)) % 2 = 1 ∧ 2 * c + 7 ≤ x % ((2 * c + 7) + (2 * c + 1)))
        0 (2 * c + 7) = 0 := by
      apply cP_eq_zero
      intro m hm h
      rw [Nat.mod_eq_of_lt (by omega : 0 + m < (2 * c + 7) + (2 * c + 1))] at h
      omega
    have e2 : cP (fun x => x % ((2 * c + 7) + (2 * c + 1)) % 2 = 1 ∧ 2 * c + 7 ≤ x % ((2 * c + 7) + (2 * c + 1)))
        (0 + (2 * c + 7)) (2 * c + 1) ≤ cP (fun x => x % 2 = 1) (0 + (2 * c + 7)) (2 * c + 1) := by
      rw [cP_eq_sum, cP_eq_sum]
      apply sum_le_sum
      intro m hm
      rw [mem_range] at hm
      rw [Nat.mod_eq_of_lt (by omega : 0 + (2 * c + 7) + m < (2 * c + 7) + (2 * c + 1))]
      split_ifs <;> omega
    have e4 := cP_le_half (Q := fun x => x % 2 = 1) (fun x ⟨a, b⟩ => by omega) (0 + (2 * c + 7)) (2 * c + 1)
    omega
  omega

lemma cR (r : ℕ) : cP (fun x => x % p = r) 0 p ≤ 1 := cP_res_le_one p r 0 p le_rfl

lemma cG0 : cP (G0 c p) 0 p ≤ 2 * c + 5 := by
  have h1 := cP_or_le (Q := G0 c p) (Q1 := fun x => x % p = 1)
    (Q2 := fun x => x % p = 2 ∨ x % p = 2 * c + 4 ∨ x % p = 2 * c + 5 ∨ E6 c p x) (fun x h => h) 0 p
  have h2 := cP_or_le (Q := fun x => x % p = 2 ∨ x % p = 2 * c + 4 ∨ x % p = 2 * c + 5 ∨ E6 c p x)
    (Q1 := fun x => x % p = 2) (Q2 := fun x => x % p = 2 * c + 4 ∨ x % p = 2 * c + 5 ∨ E6 c p x) (fun x h => h) 0 p
  have h3 := cP_or_le (Q := fun x => x % p = 2 * c + 4 ∨ x % p = 2 * c + 5 ∨ E6 c p x)
    (Q1 := fun x => x % p = 2 * c + 4) (Q2 := fun x => x % p = 2 * c + 5 ∨ E6 c p x) (fun x h => h) 0 p
  have h4 := cP_or_le (Q := fun x => x % p = 2 * c + 5 ∨ E6 c p x)
    (Q1 := fun x => x % p = 2 * c + 5) (Q2 := E6 c p) (fun x h => h) 0 p
  have := cR P 1
  have := cR P 2
  have := cR P (2 * c + 4)
  have := cR P (2 * c + 5)
  have := cE P
  omega

lemma cGZ2 : cP (GZ2 c p) 0 p ≤ 2 * c + 4 := by
  have h1 := cP_or_le (Q := GZ2 c p) (Q1 := fun x => x % p = 1)
    (Q2 := fun x => x % p = 2 * c + 4 ∨ x % p = 2 * c + 5 ∨ E6 c p x) (fun x h => h) 0 p
  have h3 := cP_or_le (Q := fun x => x % p = 2 * c + 4 ∨ x % p = 2 * c + 5 ∨ E6 c p x)
    (Q1 := fun x => x % p = 2 * c + 4) (Q2 := fun x => x % p = 2 * c + 5 ∨ E6 c p x) (fun x h => h) 0 p
  have h4 := cP_or_le (Q := fun x => x % p = 2 * c + 5 ∨ E6 c p x)
    (Q1 := fun x => x % p = 2 * c + 5) (Q2 := E6 c p) (fun x h => h) 0 p
  have := cR P 1
  have := cR P (2 * c + 4)
  have := cR P (2 * c + 5)
  have := cE P
  omega

lemma cGZ1 : cP (GZ1 c p) 0 p ≤ 3 := by
  have h1 := cP_or_le (Q := GZ1 c p) (Q1 := fun x => x % p = 1)
    (Q2 := fun x => x % p = 2 * c + 4 ∨ x % p = 2 * c + 5) (fun x h => h) 0 p
  have h3 := cP_or_le (Q := fun x => x % p = 2 * c + 4 ∨ x % p = 2 * c + 5)
    (Q1 := fun x => x % p = 2 * c + 4) (Q2 := fun x => x % p = 2 * c + 5) (fun x h => h) 0 p
  have := cR P 1
  have := cR P (2 * c + 4)
  have := cR P (2 * c + 5)
  omega

/-! ### local facts -/

/-- a window of length `2c+4` (half a period) holds at most two positions of residue 1, 2q, 2q+1 -/
lemma GZ1_half (τ L : ℕ) (hL : L ≤ 2 * c + 4) : cP (GZ1 c p) τ L ≤ 2 := by
  have hp := P.hp
  have h1 := cP_or_le (Q := GZ1 c p) (Q1 := fun x => x % (2 * c + 4) = 1)
    (Q2 := fun x => x % p = 2 * c + 4) (fun x h => by
      have e : x % p % (2 * c + 4) = x % (2 * c + 4) :=
        Nat.mod_mod_of_dvd x ⟨2, by omega⟩
      unfold GZ1 at h
      rcases h with h | h | h
      · left; rw [← e, h]; exact Nat.mod_eq_of_lt (by omega)
      · right; exact h
      · left
        rw [← e, h, show 2 * c + 5 = 1 + (2 * c + 4) by omega, Nat.add_mod_right]
        exact Nat.mod_eq_of_lt (by omega)) τ L
  have := cP_res_le_one (2 * c + 4) 1 τ L hL
  have := cP_res_le_one p (2 * c + 4) τ L (by omega)
  omega

lemma I1_adj : ∀ x, ¬(I1 c p x ∧ I1 c p (x + 1)) := by
  intro x ⟨h1, h2⟩
  have hp := P.hp
  have r1 := res_add p x 1 (by omega) (by omega)
  unfold I1 at h1 h2
  omega

lemma Gp_adj : ∀ x, ¬(Gp c p x ∧ Gp c p (x + 1)) := by
  intro x ⟨h1, h2⟩
  have hp := P.hp
  have r1 := res_add p x 1 (by omega) (by omega)
  unfold Gp E6 at h1 h2
  omega

lemma G0_cov : ∀ x, G0 c p x ∨ G0 c p (x + 1) := by
  intro x
  have hp := P.hp
  have r1 := res_add p x 1 (by omega) (by omega)
  unfold G0 E6
  omega

/-- positions of `GZ2` (all F except residue 2): at most `(w+2)/2` in any window of length `w`
(shift the even residues one step to the left: the images have odd residue) -/
lemma GZ2_half (t w : ℕ) : 2 * cP (GZ2 c p) (t + 1) w ≤ w + 2 := by
  have hp := P.hp
  have hle : cP (GZ2 c p) (t + 1) w ≤ cP (fun x => x % p % 2 = 1) t (w + 1) := by
    rw [cP, cP]
    apply card_le_card_of_injOn (fun m => if (t + 1 + m) % p % 2 = 1 then m + 1 else m)
    · intro m hm
      simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hm ⊢
      have r1 := res_add p (t + m) 1 (by omega) (by omega)
      rw [show t + m + 1 = t + 1 + m by omega] at r1
      obtain ⟨hm1, hm2⟩ := hm
      unfold GZ2 E6 at hm2
      split_ifs with hodd
      · exact ⟨by omega, by rw [show t + (m + 1) = t + 1 + m by omega]; exact hodd⟩
      · exact ⟨by omega, by omega⟩
    · intro m1 hm1 m2 hm2 heq
      simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hm1 hm2
      have r1 := res_add p (t + m1) 1 (by omega) (by omega)
      rw [show t + m1 + 1 = t + 1 + m1 by omega] at r1
      have r2 := res_add p (t + m2) 1 (by omega) (by omega)
      rw [show t + m2 + 1 = t + 1 + m2 by omega] at r2
      obtain ⟨_, hm1'⟩ := hm1
      obtain ⟨_, hm2'⟩ := hm2
      unfold GZ2 E6 at hm1' hm2'
      simp only at heq
      split_ifs at heq with ha hb hb
      · omega
      · exfalso
        have e : t + 1 + m2 = t + 1 + m1 + 1 := by omega
        have r3 := res_add p (t + 1 + m1) 1 (by omega) (by omega)
        rw [← e] at r3
        omega
      · exfalso
        have e : t + 1 + m1 = t + 1 + m2 + 1 := by omega
        have r3 := res_add p (t + 1 + m2) 1 (by omega) (by omega)
        rw [← e] at r3
        omega
      · omega
  have hodd := cP_le_half (Q := fun x => x % p % 2 = 1) (fun x ⟨a, b⟩ => by
    have r1 := res_add p x 1 (by omega) (by omega)
    omega) t (w + 1)
  omega

/-! ### the exact count at `L = 2K` -/

lemma Blem (t0 : ℕ) :
    cP (GZ1 c p) t0 (2 * c + 3) + cP (fun x => x % p = 1) (t0 + (2 * c + 3)) 1
      ≤ 1 + cP (fun x => x % p = 2) (t0 + (2 * c + 6)) (2 * c + 2) := by
  have hp := P.hp
  have hs : t0 % p < p := Nat.mod_lt _ (by omega)
  have h1 := cP_or_le (Q := GZ1 c p) (Q1 := fun x => x % p = 1)
    (Q2 := fun x => x % p = 2 * c + 4 ∨ x % p = 2 * c + 5) (fun x h => h) t0 (2 * c + 3)
  have h3 := cP_or_le (Q := fun x => x % p = 2 * c + 4 ∨ x % p = 2 * c + 5)
    (Q1 := fun x => x % p = 2 * c + 4) (Q2 := fun x => x % p = 2 * c + 5) (fun x h => h) t0 (2 * c + 3)
  have b1 := cP_res_le_one p 1 t0 (2 * c + 3) (by omega)
  have ba := cP_res_le_one p (2 * c + 4) t0 (2 * c + 3) (by omega)
  have bb := cP_res_le_one p (2 * c + 5) t0 (2 * c + 3) (by omega)
  have bl := cP_res_le_one p 1 (t0 + (2 * c + 3)) 1 (by omega)
  have z1 : (t0 % p ≤ 1 ∨ 2 * c + 7 ≤ t0 % p) ∨ cP (fun x => x % p = 1) t0 (2 * c + 3) = 0 := by
    by_cases h : t0 % p ≤ 1 ∨ 2 * c + 7 ≤ t0 % p
    · left; exact h
    · right
      apply cP_eq_zero
      intro m hm hF
      have r1 := res_add p t0 m (by omega) (by omega)
      omega
  have za : (2 ≤ t0 % p ∧ t0 % p ≤ 2 * c + 4) ∨ cP (fun x => x % p = 2 * c + 4) t0 (2 * c + 3) = 0 := by
    by_cases h : 2 ≤ t0 % p ∧ t0 % p ≤ 2 * c + 4
    · left; exact h
    · right
      apply cP_eq_zero
      intro m hm hF
      have r1 := res_add p t0 m (by omega) (by omega)
      omega
  have zb : (3 ≤ t0 % p ∧ t0 % p ≤ 2 * c + 5) ∨ cP (fun x => x % p = 2 * c + 5) t0 (2 * c + 3) = 0 := by
    by_cases h : 3 ≤ t0 % p ∧ t0 % p ≤ 2 * c + 5
    · left; exact h
    · right
      apply cP_eq_zero
      intro m hm hF
      have r1 := res_add p t0 m (by omega) (by omega)
      omega
  have zl : t0 % p = 2 * c + 6 ∨ cP (fun x => x % p = 1) (t0 + (2 * c + 3)) 1 = 0 := by
    by_cases h : t0 % p = 2 * c + 6
    · left; exact h
    · right
      apply cP_eq_zero
      intro m hm hF
      have r1 := res_add p t0 (2 * c + 3) (by omega) (by omega)
      obtain rfl : m = 0 := by omega
      rw [add_zero] at hF
      omega
  have z2 : ¬(3 ≤ t0 % p ∧ t0 % p ≤ 2 * c + 4) ∨ 1 ≤ cP (fun x => x % p = 2) (t0 + (2 * c + 6)) (2 * c + 2) := by
    by_cases h : 3 ≤ t0 % p ∧ t0 % p ≤ 2 * c + 4
    · right
      rw [cP]
      apply card_pos.mpr
      refine ⟨2 * c + 4 - t0 % p, ?_⟩
      simp only [mem_filter, mem_range]
      refine ⟨by omega, ?_⟩
      rw [show t0 + (2 * c + 6) + (2 * c + 4 - t0 % p) = t0 + (4 * c + 10 - t0 % p) by omega]
      exact mod_of (q := 1) rfl (by omega) (by omega)
    · left; exact h
  omega

lemma Zlem (t0 : ℕ) :
    2 * (cP (G0 c p) t0 (p * q3 + (2 * c + 6)) + cP (GZ2 c p) (t0 + (p * q3 + (2 * c + 6))) (p * (3 * μ + 1) + (2 * c + 2))
      + cP (GZ1 c p) (t0 + (p * q3 + (2 * c + 6)) + (p * (3 * μ + 1) + (2 * c + 2))) (p * μ + (2 * c + 3))
      + cP (fun x => x % p = 1)
          (t0 + (p * q3 + (2 * c + 6)) + (p * (3 * μ + 1) + (2 * c + 2)) + (p * μ + (2 * c + 3))) 1) ≤ K := by
  have hp := P.hp
  have per1 : ∀ x, (fun x => x % p = 1) (x + p) ↔ (fun x => x % p = 1) x := by
    intro x; simp only [Nat.add_mod_right]
  have per2 : ∀ x, (fun x => x % p = 2) (x + p) ↔ (fun x => x % p = 2) x := by
    intro x; simp only [Nat.add_mod_right]
  have e0 : cP (G0 c p) t0 (p * q3 + (2 * c + 6)) = cP (G0 c p) t0 (2 * c + 6) + q3 * cP (G0 c p) 0 p := by
    rw [Nat.add_comm (p * q3) (2 * c + 6), cP_add, cP_full (perG0 P)]
  have e2 : cP (GZ2 c p) (t0 + (p * q3 + (2 * c + 6))) (p * (3 * μ + 1) + (2 * c + 2))
      = cP (GZ2 c p) (t0 + (2 * c + 6)) (2 * c + 2) + (3 * μ + 1) * cP (GZ2 c p) 0 p := by
    rw [show t0 + (p * q3 + (2 * c + 6)) = t0 + (2 * c + 6) + p * q3 by omega, cP_shift_mul (perGZ2 P),
      Nat.add_comm (p * (3 * μ + 1)) (2 * c + 2), cP_add, cP_full (perGZ2 P)]
  have e1 : cP (GZ1 c p) (t0 + (p * q3 + (2 * c + 6)) + (p * (3 * μ + 1) + (2 * c + 2))) (p * μ + (2 * c + 3))
      = cP (GZ1 c p) t0 (2 * c + 3) + μ * cP (GZ1 c p) 0 p := by
    rw [show t0 + (p * q3 + (2 * c + 6)) + (p * (3 * μ + 1) + (2 * c + 2)) = t0 + p * (q3 + (3 * μ + 1) + 1) by
      have e : p * (q3 + (3 * μ + 1) + 1) = p * q3 + p * (3 * μ + 1) + p := by ring
      omega, cP_shift_mul (perGZ1 P), Nat.add_comm (p * μ) (2 * c + 3), cP_add,
      cP_full (perGZ1 P)]
  have el : cP (fun x => x % p = 1)
      (t0 + (p * q3 + (2 * c + 6)) + (p * (3 * μ + 1) + (2 * c + 2)) + (p * μ + (2 * c + 3))) 1
      = cP (fun x => x % p = 1) (t0 + (2 * c + 3)) 1 := by
    rw [show t0 + (p * q3 + (2 * c + 6)) + (p * (3 * μ + 1) + (2 * c + 2)) + (p * μ + (2 * c + 3))
      = t0 + (2 * c + 3) + p * (q3 + (3 * μ + 1) + 1 + μ) by
        have e : p * (q3 + (3 * μ + 1) + 1 + μ) = p * q3 + p * (3 * μ + 1) + p + p * μ := by ring
        omega,
      cP_shift_mul per1]
  -- the two partial windows of G0 and GZ2 form one period, minus the positions of residue 2 in the second
  have hper : cP (G0 c p) t0 (2 * c + 6) + cP (GZ2 c p) (t0 + (2 * c + 6)) (2 * c + 2)
      + cP (fun x => x % p = 2) (t0 + (2 * c + 6)) (2 * c + 2) ≤ cP (G0 c p) 0 p := by
    have h1 := cP_add_le (Q := G0 c p) (Q1 := GZ2 c p) (Q2 := fun x => x % p = 2) (fun x => by
      unfold G0 GZ2 E6; omega) (t0 + (2 * c + 6)) (2 * c + 2)
    have h2 := cP_add (G0 c p) t0 (2 * c + 6) (2 * c + 2)
    rw [show 2 * c + 6 + (2 * c + 2) = p by omega, cP_period (perG0 P)] at h2
    omega
  have hB := Blem P t0
  have m0 : q3 * cP (G0 c p) 0 p ≤ q3 * (2 * c + 5) := Nat.mul_le_mul_left _ (cG0 P)
  have m2 : (3 * μ + 1) * cP (GZ2 c p) 0 p ≤ (3 * μ + 1) * (2 * c + 4) := Nat.mul_le_mul_left _ (cGZ2 P)
  have m1 : μ * cP (GZ1 c p) 0 p ≤ μ * 3 := Nat.mul_le_mul_left _ (cGZ1 P)
  have hc0 := cG0 P
  have hZ := P.hZ
  omega

/-! ### the cases -/

/-- very short windows: `y ≤ u/2` -/
lemma count_A (t y : ℕ) (hy : y ≤ hu) :
    2 * #{m ∈ range (y + K) | Wc c p K hu t (y + K) m} ≤ y + 1 := by
  have hp := P.hp
  have hhu := P.hhu
  have hK := P.ha0
  have hle : #{m ∈ range (y + K) | Wc c p K hu t (y + K) m} ≤ cP (I1 c p) t y := by
    rw [cP]
    apply card_le_card_of_injOn (fun m => if (t + m) % p = 2 * c + 5 then m + 1 else m)
    · intro m hm
      simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hm ⊢
      have r1 := res_add p (t + m) 1 (by omega) (by omega)
      have hcl := Wc_class P (by omega) hm.1 hm.2
      unfold I1
      unfold E6 at hcl
      split_ifs with hb
      · rw [show t + (m + 1) = t + m + 1 by omega]
        omega
      · omega
    · intro m1 hm1 m2 hm2 heq
      simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hm1 hm2
      have hc1 := Wc_class P (by omega) hm1.1 hm1.2
      have hc2 := Wc_class P (by omega) hm2.1 hm2.2
      unfold E6 at hc1 hc2
      simp only at heq
      split_ifs at heq with ha hb hb
      · omega
      · exfalso
        have r1 := res_add p (t + m1) 1 (by omega) (by omega)
        rw [show t + m1 + 1 = t + m2 by omega] at r1
        omega
      · exfalso
        have r1 := res_add p (t + m2) 1 (by omega) (by omega)
        rw [show t + m2 + 1 = t + m1 by omega] at r1
        omega
      · omega
  have := cP_le_half (I1_adj P) t y
  omega

/-- short windows: `u/2 < y ≤ 2u - 2` -/
lemma count_A2 (t w y : ℕ) (hy : y = w + hu) (hy2 : y + 2 ≤ 4 * hu) :
    2 * #{m ∈ range (y + K) | Wc c p K hu t (y + K) m} ≤ y + 1 := by
  have hp := P.hp
  have hhu := P.hhu
  have hK := P.ha0
  have hs := P.hs
  subst hy
  have s1 := card_split (Wc c p K hu t (w + hu + K)) w (hu + K)
  have s2 := card_split (fun m => Wc c p K hu t (w + hu + K) (w + m)) hu K
  beta_reduce at s2
  rw [show w + (hu + K) = w + hu + K by omega] at s1
  have b1 : #{m ∈ range w | Wc c p K hu t (w + hu + K) m} ≤ cP (GZ2 c p) t w := by
    apply card_le_cP'
    intro m hm h
    unfold GZ2
    rcases Wc_class P (by omega) (by omega) h with h | h | h | h | h
    · left; exact h.1
    · right; right; left; exact h.1
    · omega
    · right; left; exact h.1
    · right; right; right; exact h.1
  have b2 : #{m ∈ range hu | Wc c p K hu t (w + hu + K) (w + m)} ≤ cP (GZ1 c p) (t + w) hu := by
    apply card_le_cP'
    intro m hm h
    unfold GZ1
    rw [show t + w + m = t + (w + m) by omega]
    rcases Wc_class P (by omega) (by omega) h with h | h | h | h | h
    · left; exact h.1
    · right; right; exact h.1
    · omega
    · right; left; exact h.1
    · omega
  have b3 : #{m ∈ range K | Wc c p K hu t (w + hu + K) (w + (hu + m))} = 0 := by
    apply card_zero'
    intro m hm h
    rcases Wc_class P (by omega) (by omega) h with h | h | h | h | h <;> omega
  -- GZ2 in the first w positions
  have g2 : 2 * cP (GZ2 c p) t w ≤ w + 2 := by
    have := GZ2_half P (t + (p - 1)) w
    rw [show t + (p - 1) + 1 = t + p by omega, cP_shift (perGZ2 P)] at this
    exact this
  -- GZ1 in the last u/2 positions
  have g1 : cP (GZ1 c p) (t + w) hu ≤ 3 * μ + 2 := by
    rw [hhu, Nat.add_comm (p * μ), cP_add, cP_full (perGZ1 P)]
    have := GZ1_half P (t + w) (2 * c + 4) le_rfl
    have m1 : μ * cP (GZ1 c p) 0 p ≤ μ * 3 := Nat.mul_le_mul_left _ (cGZ1 P)
    omega
  have e4 : p * μ = (4 * c + 8) * μ := by rw [hp]
  have e5 : (4 * c + 8) * μ = 4 * (c * μ) + 8 * μ := by ring
  have e6 : 1 ≤ c → μ ≤ c * μ := fun h => Nat.le_mul_of_pos_left μ h
  rcases hs with h | h
  · have := e6 h
    omega
  · omega

/-- the zones of a long window -/
lemma count_zones (t d' a' : ℕ) (hd : d' = 0 ∨ a' = p * q3 + (2 * c + 6)) (ha : a' ≤ p * q3 + (2 * c + 6))
    (hd2 : d' ≤ 2 * hu) :
    #{m ∈ range (d' + (a' + ((p * (3 * μ + 1) + (2 * c + 2)) + ((p * μ + (2 * c + 3)) + (1 + K))))) |
        Wc c p K hu t (d' + (a' + ((p * (3 * μ + 1) + (2 * c + 2)) + ((p * μ + (2 * c + 3)) + (1 + K))))) m}
      ≤ #{m ∈ range d' |
          Wc c p K hu t (d' + (a' + ((p * (3 * μ + 1) + (2 * c + 2)) + ((p * μ + (2 * c + 3)) + (1 + K))))) m}
        + cP (G0 c p) (t + d') a' + cP (GZ2 c p) (t + d' + a') (p * (3 * μ + 1) + (2 * c + 2))
        + cP (GZ1 c p) (t + d' + a' + (p * (3 * μ + 1) + (2 * c + 2))) (p * μ + (2 * c + 3))
        + cP (fun x => x % p = 1) (t + d' + a' + (p * (3 * μ + 1) + (2 * c + 2)) + (p * μ + (2 * c + 3))) 1 := by
  have hp := P.hp
  have hhu := P.hhu
  have hK := P.ha0
  obtain ⟨L, hL⟩ : ∃ L, L = d' + (a' + ((p * (3 * μ + 1) + (2 * c + 2)) + ((p * μ + (2 * c + 3)) + (1 + K)))) :=
    ⟨_, rfl⟩
  rw [← hL]
  have e3 : p * (3 * μ + 1) = 3 * (p * μ) + p := by ring
  have hLle : L ≤ 2 * K + 2 * hu := by omega
  have s1 := card_split (Wc c p K hu t L) d' (a' + ((p * (3 * μ + 1) + (2 * c + 2)) + ((p * μ + (2 * c + 3)) + (1 + K))))
  have s2 := card_split (fun m => Wc c p K hu t L (d' + m)) a'
    ((p * (3 * μ + 1) + (2 * c + 2)) + ((p * μ + (2 * c + 3)) + (1 + K)))
  have s3 := card_split (fun m => Wc c p K hu t L (d' + (a' + m))) (p * (3 * μ + 1) + (2 * c + 2))
    ((p * μ + (2 * c + 3)) + (1 + K))
  have s4 := card_split (fun m => Wc c p K hu t L (d' + (a' + ((p * (3 * μ + 1) + (2 * c + 2)) + m))))
    (p * μ + (2 * c + 3)) (1 + K)
  have s5 := card_split
    (fun m => Wc c p K hu t L (d' + (a' + ((p * (3 * μ + 1) + (2 * c + 2)) + ((p * μ + (2 * c + 3)) + m))))) 1 K
  beta_reduce at s2 s3 s4 s5
  rw [← hL] at s1
  have b2 : #{m ∈ range a' | Wc c p K hu t L (d' + m)} ≤ cP (G0 c p) (t + d') a' := by
    apply card_le_cP'
    intro m hm h
    unfold G0
    rw [show t + d' + m = t + (d' + m) by omega]
    rcases Wc_class P hLle (by omega) h with h | h | h | h | h
    · left; exact h.1
    · right; right; right; left; exact h.1
    · right; left; exact h.1
    · right; right; left; exact h.1
    · right; right; right; right; exact h.1
  have b3 : #{m ∈ range (p * (3 * μ + 1) + (2 * c + 2)) | Wc c p K hu t L (d' + (a' + m))}
      ≤ cP (GZ2 c p) (t + d' + a') (p * (3 * μ + 1) + (2 * c + 2)) := by
    apply card_le_cP'
    intro m hm h
    unfold GZ2
    rw [show t + d' + a' + m = t + (d' + (a' + m)) by omega]
    rcases Wc_class P hLle (by omega) h with h | h | h | h | h
    · left; exact h.1
    · right; right; left; exact h.1
    · omega
    · right; left; exact h.1
    · right; right; right; exact h.1
  have b4 : #{m ∈ range (p * μ + (2 * c + 3)) | Wc c p K hu t L (d' + (a' + ((p * (3 * μ + 1) + (2 * c + 2)) + m)))}
      ≤ cP (GZ1 c p) (t + d' + a' + (p * (3 * μ + 1) + (2 * c + 2))) (p * μ + (2 * c + 3)) := by
    apply card_le_cP'
    intro m hm h
    unfold GZ1
    rw [show t + d' + a' + (p * (3 * μ + 1) + (2 * c + 2)) + m
      = t + (d' + (a' + ((p * (3 * μ + 1) + (2 * c + 2)) + m))) by omega]
    rcases Wc_class P hLle (by omega) h with h | h | h | h | h
    · left; exact h.1
    · right; right; exact h.1
    · omega
    · right; left; exact h.1
    · omega
  have b5 : #{m ∈ range 1 |
      Wc c p K hu t L (d' + (a' + ((p * (3 * μ + 1) + (2 * c + 2)) + ((p * μ + (2 * c + 3)) + m))))}
      ≤ cP (fun x => x % p = 1) (t + d' + a' + (p * (3 * μ + 1) + (2 * c + 2)) + (p * μ + (2 * c + 3))) 1 := by
    apply card_le_cP'
    intro m hm h
    rw [show t + d' + a' + (p * (3 * μ + 1) + (2 * c + 2)) + (p * μ + (2 * c + 3)) + m
      = t + (d' + (a' + ((p * (3 * μ + 1) + (2 * c + 2)) + ((p * μ + (2 * c + 3)) + m)))) by omega]
    rcases Wc_class P hLle (by omega) h with h | h | h | h | h
    · exact h.1
    · omega
    · omega
    · omega
    · omega
  have b6 : #{m ∈ range K |
      Wc c p K hu t L (d' + (a' + ((p * (3 * μ + 1) + (2 * c + 2)) + ((p * μ + (2 * c + 3)) + (1 + m)))))} = 0 := by
    apply card_zero'
    intro m hm h
    rcases Wc_class P hLle (by omega) h with h | h | h | h | h <;> omega
  omega

/-- the first `d` positions of a window of length `2K + d` -/
lemma count_first (t d L : ℕ) (hL : L = d + 2 * K) (hd : d ≤ 2 * hu) :
    2 * #{m ∈ range d | Wc c p K hu t L m} ≤ d + 1 := by
  have hp := P.hp
  have hhu := P.hhu
  have hK := P.ha0
  by_cases hd0 : d = 0
  · subst hd0; simp
  obtain ⟨d1, rfl⟩ : ∃ d1, d = d1 + 1 := ⟨d - 1, by omega⟩
  have s1 := card_split (Wc c p K hu t L) d1 1
  have b1 : #{m ∈ range d1 | Wc c p K hu t L m} ≤ cP (Gp c p) t d1 := by
    apply card_le_cP'
    intro m hm h
    unfold Gp
    rcases Wc_class P (by omega) (by omega) h with h | h | h | h | h
    · omega
    · right; left; exact h.1
    · left; exact h.1
    · omega
    · right; right; exact h.1
  have b2 : #{m ∈ range 1 | Wc c p K hu t L (d1 + m)} ≤ 1 := (card_filter_le _ _).trans (by simp)
  have hh := cP_le_half (Gp_adj P) t d1
  by_cases hlast : (t + d1) % p = 1 ∨ (t + d1) % p = 2 * c + 4
  · -- the position before is a dot
    by_cases hd1 : d1 = 0
    · subst hd1
      have : cP (Gp c p) t 0 = 0 := cP_zero _ _
      omega
    obtain ⟨d2, rfl⟩ : ∃ d2, d1 = d2 + 1 := ⟨d1 - 1, by omega⟩
    have hn : ¬ Gp c p (t + d2) := by
      intro hG
      have r1 := res_add p (t + d2) 1 (by omega) (by omega)
      rw [show t + d2 + 1 = t + (d2 + 1) by omega] at r1
      unfold Gp E6 at hG
      omega
    have e : cP (Gp c p) t (d2 + 1) = cP (Gp c p) t d2 := by
      rw [cP_succ, if_neg hn, add_zero]
    have hh2 := cP_le_half (Gp_adj P) t d2
    omega
  · -- the last position is counted only if it is in Gp
    have b2' : #{m ∈ range 1 | Wc c p K hu t L (d1 + m)} ≤ cP (Gp c p) (t + d1) 1 := by
      apply card_le_cP'
      intro m hm h
      obtain rfl : m = 0 := by omega
      unfold Gp
      rw [add_zero] at h ⊢
      rcases Wc_class P (by omega) (by omega) h with h | h | h | h | h
      · omega
      · right; left; exact h.1
      · left; exact h.1
      · omega
      · right; right; exact h.1
    have e := cP_add (Gp c p) t d1 1
    have hh3 := cP_le_half (Gp_adj P) t (d1 + 1)
    omega

/-- **the count** -/
theorem count_le (t L : ℕ) (h1 : K ≤ L) (h2 : L ≤ 2 * K + 2 * hu) :
    2 * #{m ∈ range L | Wc c p K hu t L m} ≤ L - (K - 1) := by
  have hp := P.hp
  have hhu := P.hhu
  have hK := P.ha0
  have hZ := P.hZ
  have e3 : p * (3 * μ + 1) = 3 * (p * μ) + p := by ring
  by_cases hA : L ≤ K + hu
  · obtain ⟨y, rfl⟩ : ∃ y, L = y + K := ⟨L - K, by omega⟩
    have := count_A P t y (by omega)
    omega
  by_cases hA2 : L + 2 ≤ K + 4 * hu
  · obtain ⟨y, rfl⟩ : ∃ y, L = y + K := ⟨L - K, by omega⟩
    have := count_A2 P t (y - hu) y (by omega) (by omega)
    omega
  by_cases hB : L ≤ 2 * K
  · -- d' = 0
    obtain ⟨a', ha'⟩ : ∃ a', L = 0 + (a' + ((p * (3 * μ + 1) + (2 * c + 2)) + ((p * μ + (2 * c + 3)) + (1 + K)))) :=
      ⟨L + 2 - (K + 4 * hu), by omega⟩
    obtain ⟨m, hm⟩ : ∃ m, a' + m = p * q3 + (2 * c + 6) := ⟨p * q3 + (2 * c + 6) - a', by omega⟩
    have hz := count_zones P t 0 a' (Or.inl rfl) (by omega) (by omega)
    rw [← ha'] at hz
    have hz0 : #{m ∈ range 0 | Wc c p K hu t L m} = 0 := by simp
    obtain ⟨t0, ht0⟩ : ∃ t0, t0 + m = t + p * m :=
      ⟨t + p * m - m, by have : m ≤ p * m := Nat.le_mul_of_pos_left m (by omega); omega⟩
    have hZ0 := Zlem P t0
    have per1 : ∀ x, (fun x => x % p = 1) (x + p) ↔ (fun x => x % p = 1) x := by
      intro x; simp only [Nat.add_mod_right]
    have e0 : cP (G0 c p) t0 (p * q3 + (2 * c + 6)) = cP (G0 c p) t0 m + cP (G0 c p) (t + 0) a' := by
      rw [← hm, Nat.add_comm a' m, cP_add, ht0, cP_shift_mul (perG0 P), add_zero]
    have e2 : cP (GZ2 c p) (t0 + (p * q3 + (2 * c + 6))) (p * (3 * μ + 1) + (2 * c + 2))
        = cP (GZ2 c p) (t + 0 + a') (p * (3 * μ + 1) + (2 * c + 2)) := by
      rw [show t0 + (p * q3 + (2 * c + 6)) = t + 0 + a' + p * m by omega, cP_shift_mul (perGZ2 P)]
    have e1 : cP (GZ1 c p) (t0 + (p * q3 + (2 * c + 6)) + (p * (3 * μ + 1) + (2 * c + 2))) (p * μ + (2 * c + 3))
        = cP (GZ1 c p) (t + 0 + a' + (p * (3 * μ + 1) + (2 * c + 2))) (p * μ + (2 * c + 3)) := by
      rw [show t0 + (p * q3 + (2 * c + 6)) + (p * (3 * μ + 1) + (2 * c + 2))
        = t + 0 + a' + (p * (3 * μ + 1) + (2 * c + 2)) + p * m by omega, cP_shift_mul (perGZ1 P)]
    have el : cP (fun x => x % p = 1)
        (t0 + (p * q3 + (2 * c + 6)) + (p * (3 * μ + 1) + (2 * c + 2)) + (p * μ + (2 * c + 3))) 1
        = cP (fun x => x % p = 1)
          (t + 0 + a' + (p * (3 * μ + 1) + (2 * c + 2)) + (p * μ + (2 * c + 3))) 1 := by
      rw [show t0 + (p * q3 + (2 * c + 6)) + (p * (3 * μ + 1) + (2 * c + 2)) + (p * μ + (2 * c + 3))
        = t + 0 + a' + (p * (3 * μ + 1) + (2 * c + 2)) + (p * μ + (2 * c + 3)) + p * m by omega,
        cP_shift_mul per1]
    have hge := cP_ge_half (G0_cov P) t0 m
    omega
  · -- a' = a0, d' ≥ 1
    obtain ⟨d', hd'⟩ : ∃ d', L = d' + ((p * q3 + (2 * c + 6)) +
        ((p * (3 * μ + 1) + (2 * c + 2)) + ((p * μ + (2 * c + 3)) + (1 + K)))) := ⟨L - 2 * K, by omega⟩
    have hz := count_zones P t d' (p * q3 + (2 * c + 6)) (Or.inr rfl) le_rfl (by omega)
    rw [← hd'] at hz
    have hZ0 := Zlem P (t + d')
    have hf := count_first P t d' L (by omega) (by omega)
    omega

end Fam6

end Coil

#print axioms Coil.Fam6.count_le
