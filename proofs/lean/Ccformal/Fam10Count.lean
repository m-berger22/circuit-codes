import Ccformal.CountP

/-!
# Family 10 (PROOF16, Theorems 36 and 36'): the counting part

`p = 4a+9` (`a = j-2`), period-`p` gap function `gF` on positions:

    residue 4a+6 (= p-3), 2a+2 (= c) : K          residue 4a+7 (= p-2) : K + u + c        residue 4a+4 (= p-5) : K + u - c
    even residues ≤ 4a+2 other than c : K + u/2    all other residues (dots) : 2K + u = N/2          (u = 2 hu, c = 2a+2)

Main result `count_le`: in every window of length `L`, `K ≤ L ≤ N/2`, the number of start positions `x` whose chord
lies in the window while its triple does not is at most `(L-K+1)/2`.  The proof is PROOF16 sec. 4 transposed to START
positions (which removes the case distinction `i = 0` / `i ≥ 1`):  the excluded chords are those too close to the right
end of the window, so for `L ≤ K+u+c` the counted positions have even residue `≤ p-3` (no two adjacent), and beyond that
everything is compared with the exact count at `L = 2K` (`Zlem`).
-/

open Finset

namespace Coil

namespace Fam10

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedVariables false

/-- the gap function -/
def gF (a p K hu : ℕ) (x : ℕ) : ℕ :=
  if x % p = 4 * a + 6 ∨ x % p = 2 * a + 2 then K
  else if x % p = 4 * a + 7 then K + 2 * hu + (2 * a + 2)
  else if x % p = 4 * a + 4 then K + 2 * hu - (2 * a + 2)
  else if x % p % 2 = 0 ∧ x % p ≤ 4 * a + 2 then K + hu
  else 2 * K + 2 * hu

abbrev F0 (a p x : ℕ) : Prop := (x % p % 2 = 0 ∧ x % p ≤ 4 * a + 6) ∨ x % p = 4 * a + 7
abbrev Fp (a p x : ℕ) : Prop := (x % p % 2 = 0 ∧ x % p ≤ 4 * a + 4) ∨ x % p = 4 * a + 7
abbrev F3 (a p x : ℕ) : Prop := x % p % 2 = 0 ∧ x % p ≤ 4 * a + 6
abbrev F2 (a p x : ℕ) : Prop := x % p % 2 = 0 ∧ x % p ≤ 4 * a + 6 ∧ x % p ≠ 4 * a + 4
abbrev F1 (a p x : ℕ) : Prop := x % p = 2 * a + 2 ∨ x % p = 4 * a + 6

/-- the parameters -/
structure Par (a i p K hu Q q4 : ℕ) : Prop where
  hp : p = 4 * a + 9
  hK : K = p * Q + (2 * a + 5)
  hhu : hu = p * i + (2 * a + 4)
  ha0 : K = 2 * hu + (2 * a + 2) + (p * q4 + 4)
  hZ : 2 * (q4 * (2 * a + 5) + (2 * a + 6) + i * (2 * a + 5)) = K + 1

variable {a i p K hu Q q4 : ℕ} (P : Par a i p K hu Q q4)

lemma gF_3 {x : ℕ} (h : x % p = 4 * a + 6) : gF a p K hu x = K := by
  unfold gF; rw [if_pos (Or.inl h)]

lemma gF_c {x : ℕ} (h : x % p = 2 * a + 2) : gF a p K hu x = K := by
  unfold gF; rw [if_pos (Or.inr h)]

lemma gF_2 {x : ℕ} (h : x % p = 4 * a + 7) : gF a p K hu x = K + 2 * hu + (2 * a + 2) := by
  unfold gF; rw [if_neg (by omega), if_pos h]

lemma gF_5 {x : ℕ} (h : x % p = 4 * a + 4) : gF a p K hu x = K + 2 * hu - (2 * a + 2) := by
  unfold gF; rw [if_neg (by omega), if_neg (by omega), if_pos h]

lemma gF_E {x : ℕ} (h1 : x % p % 2 = 0) (h2 : x % p ≤ 4 * a + 2) (h3 : x % p ≠ 2 * a + 2) :
    gF a p K hu x = K + hu := by
  unfold gF; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos ⟨h1, h2⟩]

lemma gF_dot {x : ℕ} (h1 : ¬(x % p % 2 = 0 ∧ x % p ≤ 4 * a + 6)) (h2 : x % p ≠ 4 * a + 7) :
    gF a p K hu x = 2 * K + 2 * hu := by
  unfold gF; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

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

include P

lemma hd5 : K + 2 * hu - (2 * a + 2) = p * Q + 2 * (p * i) + (4 * a + 11) := by
  rw [P.hK, P.hhu]; omega

/-- the six classes of positions: gap and residue of the next position of the same coordinate -/
lemma gF_cases (x : ℕ) :
    (x % p = 4 * a + 6 ∧ gF a p K hu x = K ∧ (x + K) % p = 2 * a + 2) ∨
    (x % p = 2 * a + 2 ∧ gF a p K hu x = K ∧ (x + K) % p = 4 * a + 7) ∨
    (x % p = 4 * a + 7 ∧ gF a p K hu x = K + 2 * hu + (2 * a + 2) ∧
      (x + (K + 2 * hu + (2 * a + 2))) % p = 4 * a + 4) ∨
    (x % p = 4 * a + 4 ∧ gF a p K hu x = K + 2 * hu - (2 * a + 2) ∧
      (x + (K + 2 * hu - (2 * a + 2))) % p = 4 * a + 6) ∨
    (x % p % 2 = 0 ∧ x % p ≤ 4 * a + 2 ∧ x % p ≠ 2 * a + 2 ∧ gF a p K hu x = K + hu ∧
      (x + (K + hu)) % p = x % p) ∨
    (¬(x % p % 2 = 0 ∧ x % p ≤ 4 * a + 6) ∧ x % p ≠ 4 * a + 7 ∧ gF a p K hu x = 2 * K + 2 * hu ∧
      (x + (2 * K + 2 * hu)) % p = x % p) := by
  have hp := P.hp
  have hlt : x % p < p := Nat.mod_lt _ (by omega)
  by_cases h3 : x % p = 4 * a + 6
  · left
    exact ⟨h3, gF_3 h3, mod_of (q := Q + 1) h3 (by rw [P.hK, P.hp]; ring) (by omega)⟩
  by_cases hc : x % p = 2 * a + 2
  · right; left
    exact ⟨hc, gF_c hc, mod_of (q := Q) hc (by rw [P.hK, P.hp]; ring) (by omega)⟩
  by_cases h2 : x % p = 4 * a + 7
  · right; right; left
    exact ⟨h2, gF_2 h2, mod_of (q := Q + 2 * i + 2) h2 (by rw [P.hK, P.hhu, P.hp]; ring) (by omega)⟩
  by_cases h5 : x % p = 4 * a + 4
  · right; right; right; left
    exact ⟨h5, gF_5 h5, mod_of (q := Q + 2 * i + 1) h5 (by rw [hd5 P, P.hp]; ring) (by omega)⟩
  by_cases hE : x % p % 2 = 0 ∧ x % p ≤ 4 * a + 6
  · right; right; right; right; left
    exact ⟨hE.1, by omega, hc, gF_E hE.1 (by omega) hc,
      mod_of (q := Q + i + 1) rfl (by rw [P.hK, P.hhu, P.hp]; ring) hlt⟩
  · right; right; right; right; right
    exact ⟨hE, h2, gF_dot hE h2, mod_of (q := 2 * Q + 2 * i + 2) rfl (by rw [P.hK, P.hhu, P.hp]; ring) hlt⟩

/-- gap and two-gap sum, by class -/
lemma gF_two (x : ℕ) :
    (x % p = 4 * a + 6 ∧ gF a p K hu x = K ∧ gF a p K hu (x + gF a p K hu x) = K) ∨
    (x % p = 2 * a + 2 ∧ gF a p K hu x = K ∧ gF a p K hu (x + gF a p K hu x) = K + 2 * hu + (2 * a + 2)) ∨
    (x % p = 4 * a + 7 ∧ gF a p K hu x = K + 2 * hu + (2 * a + 2) ∧
      gF a p K hu (x + gF a p K hu x) = K + 2 * hu - (2 * a + 2)) ∨
    (x % p = 4 * a + 4 ∧ gF a p K hu x = K + 2 * hu - (2 * a + 2) ∧ gF a p K hu (x + gF a p K hu x) = K) ∨
    (x % p % 2 = 0 ∧ x % p ≤ 4 * a + 2 ∧ x % p ≠ 2 * a + 2 ∧ gF a p K hu x = K + hu ∧
      gF a p K hu (x + gF a p K hu x) = K + hu) ∨
    (¬(x % p % 2 = 0 ∧ x % p ≤ 4 * a + 6) ∧ x % p ≠ 4 * a + 7 ∧ gF a p K hu x = 2 * K + 2 * hu ∧
      gF a p K hu (x + gF a p K hu x) = 2 * K + 2 * hu) := by
  rcases gF_cases P x with ⟨h, hg, hs⟩ | ⟨h, hg, hs⟩ | ⟨h, hg, hs⟩ | ⟨h, hg, hs⟩ | ⟨h1, h2, h3, hg, hs⟩ |
    ⟨h1, h2, hg, hs⟩
  · left; exact ⟨h, hg, by rw [hg]; exact gF_c hs⟩
  · right; left; exact ⟨h, hg, by rw [hg]; exact gF_2 hs⟩
  · right; right; left; exact ⟨h, hg, by rw [hg]; exact gF_5 hs⟩
  · right; right; right; left; exact ⟨h, hg, by rw [hg]; exact gF_3 hs⟩
  · right; right; right; right; left
    exact ⟨h1, h2, h3, hg, by rw [hg]; exact gF_E (by rw [hs]; exact h1) (by rw [hs]; exact h2) (by rw [hs]; exact h3)⟩
  · right; right; right; right; right
    exact ⟨h1, h2, hg, by rw [hg]; exact gF_dot (by rw [hs]; exact h1) (by rw [hs]; exact h2)⟩

/-- the 'counted' start positions of the window `[t, t+L)` -/
def Wc (a p K hu t L m : ℕ) : Prop :=
  gF a p K hu (t + m) ≤ L - 1 - m ∧
    L - 1 - m < gF a p K hu (t + m) + gF a p K hu (t + m + gF a p K hu (t + m))

instance (a p K hu t L : ℕ) : DecidablePred (Wc a p K hu t L) := by
  intro m; unfold Wc; infer_instance

lemma Wc_class {t L m : ℕ} (hL : L ≤ 2 * K + 2 * hu) (hm : m < L) (h : Wc a p K hu t L m) :
    ((t + m) % p = 4 * a + 6 ∧ K ≤ L - 1 - m ∧ L - 1 - m < 2 * K) ∨
    ((t + m) % p = 2 * a + 2 ∧ K ≤ L - 1 - m) ∨
    ((t + m) % p = 4 * a + 7 ∧ K + 2 * hu + (2 * a + 2) ≤ L - 1 - m) ∨
    ((t + m) % p = 4 * a + 4 ∧ K + 2 * hu ≤ L - 1 - m + (2 * a + 2) ∧ L - 1 - m + (2 * a + 2) < 2 * K + 2 * hu) ∨
    ((t + m) % p % 2 = 0 ∧ (t + m) % p ≤ 4 * a + 2 ∧ (t + m) % p ≠ 2 * a + 2 ∧ K + hu ≤ L - 1 - m) := by
  have hhu := P.hhu
  unfold Wc at h
  rcases gF_two P (t + m) with ⟨hr, hg, hs⟩ | ⟨hr, hg, hs⟩ | ⟨hr, hg, hs⟩ | ⟨hr, hg, hs⟩ | ⟨h1, h2, h3, hg, hs⟩ |
    ⟨h1, h2, hg, hs⟩ <;> rw [hs, hg] at h <;> omega

lemma per0 : ∀ x, F0 a p (x + p) ↔ F0 a p x := by intro x; unfold F0; rw [Nat.add_mod_right]
lemma per3 : ∀ x, F3 a p (x + p) ↔ F3 a p x := by intro x; unfold F3; rw [Nat.add_mod_right]
lemma per2 : ∀ x, F2 a p (x + p) ↔ F2 a p x := by intro x; unfold F2; rw [Nat.add_mod_right]
lemma per1 : ∀ x, F1 a p (x + p) ↔ F1 a p x := by intro x; unfold F1; rw [Nat.add_mod_right]

/-! ### counts per period -/

lemma c3 : cP (F3 a p) 0 p ≤ 2 * a + 4 := by
  have hp := P.hp
  rw [show p = (4 * a + 7) + 2 by omega, cP_add]
  have e1 : cP (F3 a (4 * a + 7 + 2)) 0 (4 * a + 7) = cP (fun x => x % 2 = 0) 0 (4 * a + 7) := by
    apply cP_congr
    intro m hm
    unfold F3
    rw [Nat.mod_eq_of_lt (by omega : 0 + m < 4 * a + 7 + 2)]
    omega
  have e2 : cP (F3 a (4 * a + 7 + 2)) (0 + (4 * a + 7)) 2 = 0 := by
    apply cP_eq_zero
    intro m hm h
    unfold F3 at h
    rw [Nat.mod_eq_of_lt (by omega : 0 + (4 * a + 7) + m < 4 * a + 7 + 2)] at h
    omega
  rw [e1, e2, cP_even]
  omega

lemma c0 : cP (F0 a p) 0 p ≤ 2 * a + 5 := by
  have h := cP_or_le (Q := F0 a p) (Q1 := F3 a p) (Q2 := fun x => x % p = 4 * a + 7) (fun x h => h) 0 p
  have := c3 P
  have := cP_res_le_one p (4 * a + 7) 0 p le_rfl
  omega

lemma c2 : cP (F2 a p) 0 p ≤ 2 * a + 3 := by
  have hp := P.hp
  have h1 : cP (F2 a p) 0 p + cP (fun x => x % p = 4 * a + 4) 0 p ≤ cP (F3 a p) 0 p := by
    rw [cP_eq_sum, cP_eq_sum, cP_eq_sum, ← sum_add_distrib]
    apply sum_le_sum
    intro m _
    unfold F2 F3
    split_ifs <;> omega
  have h2 : 1 ≤ cP (fun x => x % p = 4 * a + 4) 0 p := by
    rw [cP]
    exact card_pos.mpr ⟨4 * a + 4, by simp only [mem_filter, mem_range]; exact ⟨by omega, by
      rw [zero_add]; exact Nat.mod_eq_of_lt (by omega)⟩⟩
  have := c3 P
  omega

lemma c1 : cP (F1 a p) 0 p ≤ 2 := by
  have h := cP_or_le (Q := F1 a p) (Q1 := fun x => x % p = 2 * a + 2) (Q2 := fun x => x % p = 4 * a + 6)
    (fun x h => h) 0 p
  have := cP_res_le_one p (2 * a + 2) 0 p le_rfl
  have := cP_res_le_one p (4 * a + 6) 0 p le_rfl
  omega

/-! ### the window of length 2a+4 holds at most one of the residues c, p-3 -/

lemma F1_le_one (τ : ℕ) : cP (F1 a p) τ (2 * a + 4) ≤ 1 := by
  have hp := P.hp
  rw [cP, card_le_one]
  intro m hm m' hm'
  simp only [mem_filter, mem_range] at hm hm'
  obtain ⟨h1, h2⟩ := hm
  obtain ⟨h1', h2'⟩ := hm'
  have r1 := res_add p τ m (by omega) (by omega)
  have r2 := res_add p τ m' (by omega) (by omega)
  unfold F1 at h2 h2'
  omega

lemma F1_zero (τ : ℕ) (h : τ % p = 4 * a + 7) : cP (F1 a p) τ (2 * a + 4) = 0 := by
  have hp := P.hp
  apply cP_eq_zero
  intro m hm hF
  have r1 := res_add p τ m (by omega) (by omega)
  unfold F1 at hF
  omega

/-! ### the exact count at `L = 2K` -/

lemma Blem (t0 : ℕ) :
    cP (F0 a p) t0 4 + cP (F2 a p) (t0 + (4 * a + 8)) 2 + cP (F1 a p) (t0 + 1) (2 * a + 4)
      ≤ 1 + (if F0 a p t0 then 1 else 0) + cP (F3 a p) (t0 + (4 * a + 8)) 5 := by
  have hp := P.hp
  have hs : t0 % p < p := Nat.mod_lt _ (by omega)
  have h5 : cP (F3 a p) (t0 + (4 * a + 8)) 5
      = (if F3 a p (t0 + (4 * a + 8)) then 1 else 0) + cP (F3 a p) t0 4 := by
    rw [show 5 = 1 + 4 by rfl, cP_cons, show t0 + (4 * a + 8) + 1 = t0 + p by omega, cP_shift (per3 P)]
  have h4 : cP (F0 a p) t0 4 ≤ cP (F3 a p) t0 4 + cP (fun x => x % p = 4 * a + 7) t0 4 :=
    cP_or_le (fun x h => h) t0 4
  have h2 : cP (F2 a p) (t0 + (4 * a + 8)) 2
      = (if F2 a p (t0 + (4 * a + 8)) then 1 else 0) + (if F2 a p t0 then 1 else 0) := by
    rw [cP_two, show t0 + (4 * a + 8) + 1 = t0 + p by omega]
    simp only [per2 P t0]
  have hσ : (if F2 a p (t0 + (4 * a + 8)) then 1 else 0) + (if (t0 + (4 * a + 8)) % p = 4 * a + 4 then 1 else 0)
      ≤ (if F3 a p (t0 + (4 * a + 8)) then 1 else 0) := by
    unfold F2 F3
    split_ifs <;> omega
  have hσ5 : t0 % p ≠ 4 * a + 5 ∨ (t0 + (4 * a + 8)) % p = 4 * a + 4 := by
    by_cases h : t0 % p = 4 * a + 5
    · right
      exact mod_of (q := 1) h (by omega) (by omega)
    · left; exact h
  have hR1 : cP (fun x => x % p = 4 * a + 7) t0 4 ≤ 1 := cP_res_le_one p _ t0 4 (by omega)
  have hR0 : (4 * a + 4 ≤ t0 % p ∧ t0 % p ≤ 4 * a + 7) ∨ cP (fun x => x % p = 4 * a + 7) t0 4 = 0 := by
    by_cases h : 4 * a + 4 ≤ t0 % p ∧ t0 % p ≤ 4 * a + 7
    · left; exact h
    · right
      apply cP_eq_zero
      intro m hm hF
      have r1 := res_add p t0 m (by omega) (by omega)
      omega
  have hF1 : cP (F1 a p) (t0 + 1) (2 * a + 4) ≤ 1 := F1_le_one P _
  have hF10 : t0 % p ≠ 4 * a + 6 ∨ cP (F1 a p) (t0 + 1) (2 * a + 4) = 0 := by
    by_cases h : t0 % p = 4 * a + 6
    · right
      exact F1_zero P _ (mod_of (q := 0) h (by omega) (by omega))
    · left; exact h
  have key : cP (fun x => x % p = 4 * a + 7) t0 4 + (if F2 a p t0 then 1 else 0) + cP (F1 a p) (t0 + 1) (2 * a + 4)
      ≤ 1 + (if F0 a p t0 then 1 else 0) + (if (t0 + (4 * a + 8)) % p = 4 * a + 4 then 1 else 0) := by
    unfold F2 F0
    split_ifs <;> omega
  omega

lemma Zlem (t0 : ℕ) :
    2 * (cP (F0 a p) t0 (p * q4 + 4) + cP (F3 a p) (t0 + (p * q4 + 4)) (4 * a + 4)
      + cP (F2 a p) (t0 + (p * q4 + 4) + (4 * a + 4)) (p * i + 2)
      + cP (F1 a p) (t0 + (p * q4 + 4) + (4 * a + 4) + (p * i + 2)) hu) + 2
      ≤ K + 1 + 2 * (if F0 a p t0 then 1 else 0) := by
  have hp := P.hp
  have e0 : cP (F0 a p) t0 (p * q4 + 4) = cP (F0 a p) t0 4 + q4 * cP (F0 a p) 0 p := by
    rw [Nat.add_comm (p * q4) 4, cP_add, cP_full (per0 P)]
  have e3 : cP (F3 a p) (t0 + (p * q4 + 4)) (4 * a + 4) + cP (F3 a p) (t0 + (4 * a + 8)) 5 = cP (F3 a p) 0 p := by
    rw [show t0 + (p * q4 + 4) = t0 + 4 + p * q4 by omega, cP_shift_mul (per3 P),
      show t0 + (4 * a + 8) = t0 + 4 + (4 * a + 4) by omega, ← cP_add, show 4 * a + 4 + 5 = p by omega,
      cP_period (per3 P)]
  have e2 : cP (F2 a p) (t0 + (p * q4 + 4) + (4 * a + 4)) (p * i + 2)
      = cP (F2 a p) (t0 + (4 * a + 8)) 2 + i * cP (F2 a p) 0 p := by
    rw [show t0 + (p * q4 + 4) + (4 * a + 4) = t0 + (4 * a + 8) + p * q4 by omega, cP_shift_mul (per2 P),
      Nat.add_comm (p * i) 2, cP_add, cP_full (per2 P)]
  have e1 : cP (F1 a p) (t0 + (p * q4 + 4) + (4 * a + 4) + (p * i + 2)) hu
      = cP (F1 a p) (t0 + 1) (2 * a + 4) + i * cP (F1 a p) 0 p := by
    rw [show t0 + (p * q4 + 4) + (4 * a + 4) + (p * i + 2) = t0 + 1 + p * (q4 + i + 1) by
      rw [mul_add, mul_add]; omega, cP_shift_mul (per1 P), P.hhu, Nat.add_comm (p * i), cP_add,
      cP_full (per1 P)]
  have hB := Blem P t0
  have m0 : q4 * cP (F0 a p) 0 p ≤ q4 * (2 * a + 5) := Nat.mul_le_mul_left _ (c0 P)
  have m2 : i * cP (F2 a p) 0 p ≤ i * (2 * a + 3) := Nat.mul_le_mul_left _ (c2 P)
  have m1 : i * cP (F1 a p) 0 p ≤ i * 2 := Nat.mul_le_mul_left _ (c1 P)
  have hc3 := c3 P
  have r1 : i * (2 * a + 5) = i * (2 * a + 3) + i * 2 := by ring
  have hZ := P.hZ
  omega

/-! ### the zones -/

lemma F3_adj : ∀ x, ¬(F3 a p x ∧ F3 a p (x + 1)) := by
  intro x ⟨h1, h2⟩
  have hp := P.hp
  have r1 := res_add p x 1 (by omega) (by omega)
  unfold F3 at h1 h2
  omega

lemma Fp_adj : ∀ x, ¬(Fp a p x ∧ Fp a p (x + 1)) := by
  intro x ⟨h1, h2⟩
  have hp := P.hp
  have r1 := res_add p x 1 (by omega) (by omega)
  unfold Fp at h1 h2
  omega

lemma F0_cov : ∀ x, F0 a p x ∨ F0 a p (x + 1) := by
  intro x
  have hp := P.hp
  have r1 := res_add p x 1 (by omega) (by omega)
  unfold F0
  omega

lemma F0_Fp (x : ℕ) (h : F0 a p (x + 1)) : ¬ Fp a p x := by
  intro h2
  have hp := P.hp
  have r1 := res_add p x 1 (by omega) (by omega)
  unfold F0 at h
  unfold Fp at h2
  omega

/-- short windows: `L ≤ K + u + c` -/
lemma count_short (t y : ℕ) (hy : y ≤ 2 * hu + (2 * a + 2)) :
    2 * #{m ∈ range (y + K) | Wc a p K hu t (y + K) m} ≤ y + 1 := by
  have hhu := P.hhu
  have hK := P.ha0
  have s1 := card_split (Wc a p K hu t (y + K)) y K
  have b1 : #{m ∈ range y | Wc a p K hu t (y + K) m} ≤ cP (F3 a p) t y := by
    apply card_le_cP'
    intro m hm h
    unfold F3
    rcases Wc_class P (by omega) (by omega) h with h | h | h | h | h <;> omega
  have b2 : #{m ∈ range K | Wc a p K hu t (y + K) (y + m)} = 0 := by
    apply card_zero'
    intro m hm h
    rcases Wc_class P (by omega) (by omega) h with h | h | h | h | h <;> omega
  have := cP_le_half (F3_adj P) t y
  omega

/-- long windows: the five zones -/
lemma count_zones (t d' a' : ℕ) (hd : d' = 0 ∨ a' = p * q4 + 4) (ha : a' ≤ p * q4 + 4) (hd2 : d' ≤ 2 * hu) :
    #{m ∈ range (d' + (a' + ((4 * a + 4) + ((p * i + 2) + (hu + K))))) |
        Wc a p K hu t (d' + (a' + ((4 * a + 4) + ((p * i + 2) + (hu + K))))) m}
      ≤ cP (Fp a p) t d' + cP (F0 a p) (t + d') a' + cP (F3 a p) (t + d' + a') (4 * a + 4)
        + cP (F2 a p) (t + d' + a' + (4 * a + 4)) (p * i + 2)
        + cP (F1 a p) (t + d' + a' + (4 * a + 4) + (p * i + 2)) hu := by
  have hhu := P.hhu
  have hK := P.ha0
  set L := d' + (a' + ((4 * a + 4) + ((p * i + 2) + (hu + K)))) with hL
  have hLle : L ≤ 2 * K + 2 * hu := by omega
  have s1 := card_split (Wc a p K hu t L) d' (a' + ((4 * a + 4) + ((p * i + 2) + (hu + K))))
  have s2 := card_split (fun m => Wc a p K hu t L (d' + m)) a' ((4 * a + 4) + ((p * i + 2) + (hu + K)))
  have s3 := card_split (fun m => Wc a p K hu t L (d' + (a' + m))) (4 * a + 4) ((p * i + 2) + (hu + K))
  have s4 := card_split (fun m => Wc a p K hu t L (d' + (a' + ((4 * a + 4) + m)))) (p * i + 2) (hu + K)
  have s5 := card_split (fun m => Wc a p K hu t L (d' + (a' + ((4 * a + 4) + ((p * i + 2) + m))))) hu K
  beta_reduce at s2 s3 s4 s5
  rw [← hL] at s1
  have b1 : #{m ∈ range d' | Wc a p K hu t L m} ≤ cP (Fp a p) t d' := by
    apply card_le_cP'
    intro m hm h
    unfold Fp
    rcases Wc_class P hLle (by omega) h with h | h | h | h | h <;> omega
  have b2 : #{m ∈ range a' | Wc a p K hu t L (d' + m)} ≤ cP (F0 a p) (t + d') a' := by
    apply card_le_cP'
    intro m hm h
    unfold F0
    rw [show t + d' + m = t + (d' + m) by omega]
    rcases Wc_class P hLle (by omega) h with h | h | h | h | h <;> omega
  have b3 : #{m ∈ range (4 * a + 4) | Wc a p K hu t L (d' + (a' + m))} ≤ cP (F3 a p) (t + d' + a') (4 * a + 4) := by
    apply card_le_cP'
    intro m hm h
    unfold F3
    rw [show t + d' + a' + m = t + (d' + (a' + m)) by omega]
    rcases Wc_class P hLle (by omega) h with h | h | h | h | h <;> omega
  have b4 : #{m ∈ range (p * i + 2) | Wc a p K hu t L (d' + (a' + ((4 * a + 4) + m)))}
      ≤ cP (F2 a p) (t + d' + a' + (4 * a + 4)) (p * i + 2) := by
    apply card_le_cP'
    intro m hm h
    unfold F2
    rw [show t + d' + a' + (4 * a + 4) + m = t + (d' + (a' + ((4 * a + 4) + m))) by omega]
    rcases Wc_class P hLle (by omega) h with h | h | h | h | h <;> omega
  have b5 : #{m ∈ range hu | Wc a p K hu t L (d' + (a' + ((4 * a + 4) + ((p * i + 2) + m))))}
      ≤ cP (F1 a p) (t + d' + a' + (4 * a + 4) + (p * i + 2)) hu := by
    apply card_le_cP'
    intro m hm h
    unfold F1
    rw [show t + d' + a' + (4 * a + 4) + (p * i + 2) + m = t + (d' + (a' + ((4 * a + 4) + ((p * i + 2) + m)))) by
      omega]
    rcases Wc_class P hLle (by omega) h with h | h | h | h | h <;> omega
  have b6 : #{m ∈ range K | Wc a p K hu t L (d' + (a' + ((4 * a + 4) + ((p * i + 2) + (hu + m)))))} = 0 := by
    apply card_zero'
    intro m hm h
    rcases Wc_class P hLle (by omega) h with h | h | h | h | h <;> omega
  omega

/-- **the count** -/
theorem count_le (t L : ℕ) (h1 : K ≤ L) (h2 : L ≤ 2 * K + 2 * hu) :
    2 * #{m ∈ range L | Wc a p K hu t L m} ≤ L - (K - 1) := by
  have hp := P.hp
  have hhu := P.hhu
  have hK := P.ha0
  have hZ := P.hZ
  by_cases hA : L ≤ K + (2 * hu + (2 * a + 2))
  · obtain ⟨y, rfl⟩ : ∃ y, L = y + K := ⟨L - K, by omega⟩
    have := count_short P t y (by omega)
    omega
  · by_cases hB : L ≤ 2 * K
    · -- d' = 0
      obtain ⟨a', ha'⟩ : ∃ a', L = 0 + (a' + ((4 * a + 4) + ((p * i + 2) + (hu + K)))) :=
        ⟨L - (K + (2 * hu + (2 * a + 2))), by omega⟩
      obtain ⟨m, hm⟩ : ∃ m, a' + m = p * q4 + 4 := ⟨p * q4 + 4 - a', by omega⟩
      have hz := count_zones P t 0 a' (Or.inl rfl) (by omega) (by omega)
      rw [← ha'] at hz
      obtain ⟨t0, ht0⟩ : ∃ t0, t0 + m = t + p * m :=
        ⟨t + p * m - m, by have : m ≤ p * m := Nat.le_mul_of_pos_left m (by omega); omega⟩
      have hZ0 := Zlem P t0
      have e0 : cP (F0 a p) t0 (p * q4 + 4) = cP (F0 a p) t0 m + cP (F0 a p) (t + 0) a' := by
        rw [← hm, Nat.add_comm a' m, cP_add, ht0, cP_shift_mul (per0 P), add_zero]
      have e3 : cP (F3 a p) (t0 + (p * q4 + 4)) (4 * a + 4) = cP (F3 a p) (t + 0 + a') (4 * a + 4) := by
        rw [show t0 + (p * q4 + 4) = t + 0 + a' + p * m by omega, cP_shift_mul (per3 P)]
      have e2 : cP (F2 a p) (t0 + (p * q4 + 4) + (4 * a + 4)) (p * i + 2)
          = cP (F2 a p) (t + 0 + a' + (4 * a + 4)) (p * i + 2) := by
        rw [show t0 + (p * q4 + 4) + (4 * a + 4) = t + 0 + a' + (4 * a + 4) + p * m by omega,
          cP_shift_mul (per2 P)]
      have e1 : cP (F1 a p) (t0 + (p * q4 + 4) + (4 * a + 4) + (p * i + 2)) hu
          = cP (F1 a p) (t + 0 + a' + (4 * a + 4) + (p * i + 2)) hu := by
        rw [show t0 + (p * q4 + 4) + (4 * a + 4) + (p * i + 2) = t + 0 + a' + (4 * a + 4) + (p * i + 2) + p * m by
          omega, cP_shift_mul (per1 P)]
      have hz0 : cP (Fp a p) t 0 = 0 := cP_zero _ _
      have hge := cP_ge_half (F0_cov P) t0 m
      have hge1 : F0 a p t0 → 1 ≤ m → (m - 1) / 2 + 1 ≤ cP (F0 a p) t0 m := by
        intro hF hm1
        obtain ⟨m', rfl⟩ : ∃ m', m = 1 + m' := ⟨m - 1, by omega⟩
        rw [cP_cons, if_pos hF]
        have := cP_ge_half (F0_cov P) (t0 + 1) m'
        omega
      by_cases hF : F0 a p t0
      · rw [if_pos hF] at hZ0
        by_cases hm1 : 1 ≤ m
        · have := hge1 hF hm1
          omega
        · omega
      · rw [if_neg hF] at hZ0
        omega
    · -- a' = a0, d' ≥ 1
      obtain ⟨d', hd'⟩ : ∃ d', L = d' + ((p * q4 + 4) + ((4 * a + 4) + ((p * i + 2) + (hu + K)))) :=
        ⟨L - 2 * K, by omega⟩
      have hz := count_zones P t d' (p * q4 + 4) (Or.inr rfl) le_rfl (by omega)
      rw [← hd'] at hz
      have hZ0 := Zlem P (t + d')
      have hh := cP_le_half (Fp_adj P) t d'
      by_cases hF : F0 a p (t + d')
      · rw [if_pos hF] at hZ0
        obtain ⟨d'', rfl⟩ : ∃ d'', d' = d'' + 1 := ⟨d' - 1, by omega⟩
        have hn : ¬ Fp a p (t + d'') := F0_Fp P _ hF
        have e : cP (Fp a p) t (d'' + 1) = cP (Fp a p) t d'' := by
          rw [cP_succ, if_neg hn, add_zero]
        have hh2 := cP_le_half (Fp_adj P) t d''
        omega
      · rw [if_neg hF] at hZ0
        omega

end Fam10

end Coil

#print axioms Coil.Fam10.count_le
