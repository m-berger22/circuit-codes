import Ccformal.PathWalk

/-!
# Douglas' boundary case, lower bound (S178):  `P(3k/2+1, k) = 2k+3` for even `k`

`k = 2κ`, `d = 3κ+1`, `L = 4κ+3`.  Word: `0 1 … k | 0 | n_0 1 n_1 2 … n_{κ-1} κ | 0`  (`n_i = k+1+i`).
Proof by the Walk Lemma with an explicit height function (`isPathWord_of_height`); the plan was brute-forced in python first.  With `path_bound_douglas_even`: `maxPath_douglas_even`.
-/

open Finset

namespace Coil

namespace DW

/-- the word -/
def famT (κ p : ℕ) : ℕ :=
  if p ≤ 2 * κ then p
  else if p = 2 * κ + 1 then 0
  else if p ≤ 4 * κ + 1 then (if p % 2 = 0 then 2 * κ + 1 + (p - (2 * κ + 2)) / 2 else (p - (2 * κ + 1)) / 2)
  else 0

/-- previous occurrences of the letter at `j` (dummy values `> j` when there is none) -/
def P1 (κ j : ℕ) : ℕ :=
  if j = 2 * κ + 1 ∨ j = 4 * κ + 2 then 0
  else if 2 * κ + 3 ≤ j ∧ j ≤ 4 * κ + 1 ∧ j % 2 = 1 then (j - (2 * κ + 1)) / 2
  else j + 1

def P2 (κ j : ℕ) : ℕ := if j = 4 * κ + 2 then 2 * κ + 1 else j + 2

/-- `j` is a down-step for the start `s` -/
def dn (κ s j : ℕ) : Prop :=
  (j = 2 * κ + 1 ∧ s = 0) ∨ (2 * κ + 3 ≤ j ∧ j ≤ 4 * κ + 1 ∧ j % 2 = 1 ∧ 2 * s + 2 * κ + 1 ≤ j) ∨
    (j = 4 * κ + 2 ∧ 1 ≤ s ∧ s ≤ 2 * κ + 1)

/-- number of down-steps in `[s, p)` -/
def dH (κ s p : ℕ) : ℕ :=
  (if s = 0 ∧ 2 * κ + 2 ≤ p then 1 else 0)
    + (if 2 * κ + 2 ≤ p then min κ ((p - (2 * κ + 2)) / 2) + 1 - max s 1 else 0)
    + (if 1 ≤ s ∧ s ≤ 2 * κ + 1 ∧ 4 * κ + 3 ≤ p then 1 else 0)

def H (κ s p : ℕ) : ℕ := p - s - 2 * dH κ s p

lemma famT_lt (κ p : ℕ) : famT κ p < 3 * κ + 1 := by
  unfold famT
  split_ifs <;> omega

/-- the word with letters in `Fin (3κ+1)` -/
def famF (κ : ℕ) : ℕ → Fin (3 * κ + 1) := fun p => ⟨famT κ p, famT_lt κ p⟩

lemma occ (κ i j : ℕ) (hij : i < j) (hj : j < 4 * κ + 3) :
    famT κ i = famT κ j ↔ i = P1 κ j ∨ i = P2 κ j ∨ i = j + 3 := by
  unfold famT P1 P2
  split_ifs <;> omega

lemma hdn (κ s w : ℕ) (h : s + w < 4 * κ + 3) :
    Odd (cnt (famF κ) s w (famF κ (s + w))) ↔ dn κ s (s + w) := by
  have hc := cnt_three (T := famF κ) (s := s) (w := w) (c := famF κ (s + w))
    (p1 := P1 κ (s + w)) (p2 := P2 κ (s + w)) (p3 := s + w + 3)
    (by unfold P1 P2; split_ifs <;> omega) (by unfold P1; split_ifs <;> omega) (by unfold P2; split_ifs <;> omega)
    (by
      intro i h1 h2
      have := occ κ i (s + w) h2 h
      simp only [famF, Fin.ext_iff]
      exact this)
  rw [hc, Nat.odd_iff]
  have key : ∀ a b : ℕ, a = P1 κ (s + w) → b = P2 κ (s + w) →
      (((if s ≤ a ∧ a < s + w then 1 else 0) + (if s ≤ b ∧ b < s + w then 1 else 0)
        + (if s ≤ s + w + 3 ∧ s + w + 3 < s + w then 1 else 0)) % 2 = 1 ↔ dn κ s (s + w)) := by
    intro a b ha hb
    unfold P1 at ha
    unfold P2 at hb
    unfold dn
    split_ifs at ha hb ⊢ <;> first | omega | (simp only [false_iff]; omega) | (simp only [true_iff]; omega)
  exact key _ _ rfl rfl

lemma h0 (κ s : ℕ) : H κ s s = 0 := by
  unfold H
  omega

lemma hup (κ s j : ℕ) (hs : s ≤ j) (hj : j < 4 * κ + 3) (hd : ¬ dn κ s j) : H κ s (j + 1) = H κ s j + 1 := by
  unfold dn at hd
  unfold H dH
  split_ifs <;> omega

lemma hdown (κ s j : ℕ) (hs : s ≤ j) (hj : j < 4 * κ + 3) (hd : dn κ s j) :
    2 * κ + 1 ≤ H κ s j ∧ H κ s (j + 1) + 1 = H κ s j := by
  unfold dn at hd
  unfold H dH
  split_ifs <;> omega

theorem isPathWord (κ : ℕ) : IsPathWord (2 * κ) (4 * κ + 3) (famF κ) :=
  isPathWord_of_height (H κ) (dn κ) (fun s w h => hdn κ s w h) (fun s _ => h0 κ s)
    (fun s j hs hj hd => hup κ s j hs hj hd) (fun s j hs hj hd => hdown κ s j hs hj hd)

end DW

/-- **Douglas' remark (8), second part**: `P(3k/2+1, k) = 2k+3` for even `k ≥ 2`. -/
theorem maxPath_douglas_even (κ : ℕ) (hκ : 1 ≤ κ) : IsMaxPath (3 * κ + 1) (2 * κ) (4 * κ + 3) := by
  refine ⟨(DW.isPathWord κ).exists_path, fun L' v' h' => ?_⟩
  obtain ⟨T, hT, _⟩ := h'.exists_word
  have := path_bound_douglas_even hT ⟨κ, by omega⟩ (by omega) (by simp; omega)
  omega

end Coil

#print axioms Coil.maxPath_douglas_even
