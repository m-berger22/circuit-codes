import Ccformal.PathDouglas
import Ccformal.GapCriterion

/-!
# The Walk Lemma for path words (S178)

Fix a start `s` and follow `w ↦ oddc T s w`. Step `s+w` is a *down-step* iff `T (s+w)` occurs an odd number of times in
`[s, s+w)`. `T` is a spread-`k` path word iff the walk is at height `≥ k+1` before every down-step
(`isPathWord_of_walk`: the direction needed for constructions).  Also: counting occurrences through an explicit list of
positions (`cnt_three`).
-/

open Finset

namespace Coil

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.deprecated false

variable {α : Type*} [Fintype α] [DecidableEq α] {k L : ℕ} {T : ℕ → α}

/-- the window grows by one step at its right end -/
lemma oddc_snoc (T : ℕ → α) (s w : ℕ) :
    oddc T s (w + 1) = if Odd (cnt T s w (T (s + w))) then oddc T s w - 1 else oddc T s w + 1 := by
  set c := T (s + w) with hc
  have e : ∀ x, cnt T s (w + 1) x = cnt T s w x + if c = x then 1 else 0 := by
    intro x
    rw [cnt_add, cnt_one]
  rw [oddc_eq_sum, oddc_eq_sum]
  rw [← add_sum_erase univ _ (mem_univ c),
    ← add_sum_erase univ (fun x => if Odd (cnt T s w x) then 1 else 0) (mem_univ c)]
  have hrest : ∑ x ∈ univ.erase c, (if Odd (cnt T s (w + 1) x) then 1 else 0)
      = ∑ x ∈ univ.erase c, (if Odd (cnt T s w x) then 1 else 0) := by
    apply sum_congr rfl
    intro x hx
    have : c ≠ x := fun h' => (ne_of_mem_erase hx) h'.symm
    rw [e x, ite_cond_eq_false _ _ (eq_false this), add_zero]
  rw [hrest, e c]
  simp only [ite_true, Nat.odd_add_one]
  split_ifs <;> omega

lemma oddc_pos_of_odd {s w : ℕ} {c : α} (h : Odd (cnt T s w c)) : 1 ≤ oddc T s w := by
  rw [oddc]
  exact card_pos.mpr ⟨c, by simp [h]⟩

lemma oddc_snoc_up {s w : ℕ} (h : ¬ Odd (cnt T s w (T (s + w)))) : oddc T s (w + 1) = oddc T s w + 1 := by
  rw [oddc_snoc, if_neg h]

lemma oddc_snoc_down {s w : ℕ} (h : Odd (cnt T s w (T (s + w)))) : oddc T s (w + 1) + 1 = oddc T s w := by
  have := oddc_pos_of_odd h
  rw [oddc_snoc, if_pos h]
  omega

/-- **Walk Lemma** (sufficiency). -/
theorem isPathWord_of_walk
    (hW : ∀ s w, s + w < L → Odd (cnt T s w (T (s + w))) → k + 1 ≤ oddc T s w) : IsPathWord k L T := by
  have inv : ∀ s w, s + w ≤ L → (oddc T s w = w ∨ k ≤ oddc T s w) := by
    intro s w
    induction w with
    | zero => intro _; left; simp [oddc, cnt]
    | succ w ih =>
      intro hs
      have ih' := ih (by omega)
      by_cases hd : Odd (cnt T s w (T (s + w)))
      · have h1 := hW s w (by omega) hd
        have h2 := oddc_snoc_down hd
        right; omega
      · have h2 := oddc_snoc_up hd
        rcases ih' with h3 | h3
        · left; omega
        · right; omega
  refine ⟨fun s w hs hw => ?_⟩
  rcases inv s w hs with h | h
  · exact h
  · omega

/-- **Walk Lemma** with an explicit height function `H` and an explicit down-step predicate `dn`. -/
theorem isPathWord_of_height (H : ℕ → ℕ → ℕ) (dn : ℕ → ℕ → Prop)
    (hdn : ∀ s w, s + w < L → (Odd (cnt T s w (T (s + w))) ↔ dn s (s + w)))
    (h0 : ∀ s, s < L → H s s = 0)
    (hup : ∀ s j, s ≤ j → j < L → ¬ dn s j → H s (j + 1) = H s j + 1)
    (hdown : ∀ s j, s ≤ j → j < L → dn s j → k + 1 ≤ H s j ∧ H s (j + 1) + 1 = H s j) :
    IsPathWord k L T := by
  have hH : ∀ s w, s + w ≤ L → s < L → oddc T s w = H s (s + w) := by
    intro s w
    induction w with
    | zero => intro _ hs; rw [add_zero, h0 s hs]; simp [oddc, cnt]
    | succ w ih =>
      intro hs hsL
      have ih' := ih (by omega) hsL
      by_cases hd : Odd (cnt T s w (T (s + w)))
      · have h1 := (hdown s (s + w) (by omega) (by omega) ((hdn s w (by omega)).mp hd)).2
        have h2 := oddc_snoc_down hd
        rw [← add_assoc]; omega
      · have h1 := hup s (s + w) (by omega) (by omega) (fun h' => hd ((hdn s w (by omega)).mpr h'))
        have h2 := oddc_snoc_up hd
        rw [← add_assoc]; omega
  apply isPathWord_of_walk
  intro s w hs hd
  rw [hH s w (by omega) (by omega)]
  exact (hdown s (s + w) (by omega) hs ((hdn s w hs).mp hd)).1

/-- occurrences of `c` in a window, when its positions in the window are among three distinct known ones -/
lemma cnt_three {s w : ℕ} {c : α} {p1 p2 p3 : ℕ} (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3)
    (hocc : ∀ i, s ≤ i → i < s + w → (T i = c ↔ i = p1 ∨ i = p2 ∨ i = p3)) :
    cnt T s w c = (if s ≤ p1 ∧ p1 < s + w then 1 else 0) + (if s ≤ p2 ∧ p2 < s + w then 1 else 0)
      + (if s ≤ p3 ∧ p3 < s + w then 1 else 0) := by
  have ind : ∀ p, (∑ j ∈ range w, if s + j = p then 1 else 0) = if s ≤ p ∧ p < s + w then 1 else 0 := by
    intro p
    by_cases hp : s ≤ p ∧ p < s + w
    · rw [if_pos hp]
      rw [sum_eq_single_of_mem (p - s) (mem_range.mpr (by omega))]
      · rw [if_pos (by omega)]
      · intro b _ hb
        rw [if_neg (by omega)]
    · rw [if_neg hp]
      apply sum_eq_zero
      intro j hj
      rw [mem_range] at hj
      rw [if_neg (by omega)]
  rw [cnt_eq_sum, ← ind p1, ← ind p2, ← ind p3, ← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro j hj
  rw [mem_range] at hj
  have := hocc (s + j) (by omega) (by omega)
  by_cases hT : T (s + j) = c
  · rw [if_pos hT]
    rcases this.mp hT with h | h | h
    · rw [if_pos h, if_neg (by omega), if_neg (by omega)]
    · rw [if_neg (by omega), if_pos h, if_neg (by omega)]
    · rw [if_neg (by omega), if_neg (by omega), if_pos h]
  · rw [if_neg hT]
    have h' : ¬ (s + j = p1 ∨ s + j = p2 ∨ s + j = p3) := fun h' => hT (this.mpr h')
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

end Coil

#print axioms Coil.isPathWord_of_height
#print axioms Coil.cnt_three
