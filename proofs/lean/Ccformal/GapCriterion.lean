import Ccformal.Criterion

/-!
# The gap criterion (the 'Reduction' section of the family proofs, once and for all)

A transition word `T` given together with a gap function `g` (`x + g x` = the next position of the coordinate
`T x`).  If all gaps are `≥ k+1`, three consecutive gaps sum to `≥ N/2`, every coordinate closes after 2 or 4
gaps, and for every window `[t, t+L)`, `k+1 ≤ L ≤ N/2`,

    #{ x in the window : the chord (x, x + g x) lies in the window, the triple (x, sx, ssx) does not } ≤ (L-k)/2,

then `T` is the transition word of a spread-`k` circuit code.  (`odd(W) = L - 2 (P - T)` of PROOF16 sec. 3,
proved here by peeling the window from the left: `oddc_peel`.)
-/

open Finset

namespace Coil

set_option linter.unusedSectionVars false
set_option linter.deprecated false

variable {α : Type*} [Fintype α] [DecidableEq α] {k N : ℕ} {T : ℕ → α}

/-- the window grows by one step at its left end -/
lemma oddc_cons (T : ℕ → α) (t L : ℕ) :
    oddc T t (L + 1) = if Odd (cnt T (t + 1) L (T t)) then oddc T (t + 1) L - 1 else oddc T (t + 1) L + 1 := by
  set c := T t with hc
  have e : ∀ x, cnt T t (L + 1) x = cnt T (t + 1) L x + if c = x then 1 else 0 := by
    intro x
    rw [Nat.add_comm L 1, cnt_add, cnt_one, Nat.add_comm]
  rw [oddc_eq_sum, oddc_eq_sum]
  rw [← add_sum_erase univ _ (mem_univ c),
    ← add_sum_erase univ (fun x => if Odd (cnt T (t + 1) L x) then 1 else 0) (mem_univ c)]
  have hrest : ∑ x ∈ univ.erase c, (if Odd (cnt T t (L + 1) x) then 1 else 0)
      = ∑ x ∈ univ.erase c, (if Odd (cnt T (t + 1) L x) then 1 else 0) := by
    apply sum_congr rfl
    intro x hx
    have : c ≠ x := fun h' => (ne_of_mem_erase hx) h'.symm
    rw [e x, ite_cond_eq_false _ _ (eq_false this), add_zero]
  rw [hrest, e c]
  simp only [ite_true, Nat.odd_add_one]
  split_ifs <;> omega

/-- `odd(W) = L - 2 #{x ∈ W : T x occurs an odd number of times after x in W}` -/
lemma oddc_peel (T : ℕ → α) (t L : ℕ) :
    oddc T t L + 2 * #{m ∈ range L | Odd (cnt T (t + m + 1) (L - 1 - m) (T (t + m)))} = L := by
  induction L generalizing t with
  | zero => simp [oddc, cnt]
  | succ L ih =>
    have hodd : Odd (cnt T (t + 1) L (T t)) → 1 ≤ oddc T (t + 1) L := by
      intro h
      rw [oddc]
      exact card_pos.mpr ⟨T t, by simp [h]⟩
    have ih' := ih (t + 1)
    rw [card_filter] at ih' ⊢
    rw [sum_range_succ']
    have e1 : ∀ i ∈ range L,
        (if Odd (cnt T (t + (i + 1) + 1) (L + 1 - 1 - (i + 1)) (T (t + (i + 1)))) then 1 else 0)
        = (if Odd (cnt T (t + 1 + i + 1) (L - 1 - i) (T (t + 1 + i))) then 1 else 0) := by
      intro i _
      rw [show t + (i + 1) + 1 = t + 1 + i + 1 by omega, show L + 1 - 1 - (i + 1) = L - 1 - i by omega,
        show t + (i + 1) = t + 1 + i by omega]
    rw [sum_congr rfl e1, oddc_cons]
    simp only [add_zero, Nat.add_sub_cancel, Nat.sub_zero]
    split_ifs with h
    · have := hodd h
      omega
    · omega

lemma cnt_eq_zero {t L : ℕ} {c : α} (h : ∀ i, i < L → T (t + i) ≠ c) : cnt T t L c = 0 := by
  rw [cnt, card_eq_zero, filter_eq_empty_iff]
  intro i hi
  exact h i (mem_range.mp hi)

section gaps

variable (g : ℕ → ℕ) (G1 : ∀ x, T (x + g x) = T x) (G2 : ∀ x d, 0 < d → d < g x → T (x + d) ≠ T x)
  (G0 : ∀ x, 1 ≤ g x)

include G2 in
lemma cnt_gap (x M : ℕ) (hM : M < g x) : cnt T (x + 1) M (T x) = 0 := by
  apply cnt_eq_zero
  intro i hi
  rw [show x + 1 + i = x + (i + 1) by omega]
  exact G2 x (i + 1) (by omega) (by omega)

include G1 G2 G0 in
/-- peel one gap -/
lemma cnt_chain (x L : ℕ) : cnt T x (g x + L) (T x) = 1 + cnt T (x + g x) L (T (x + g x)) := by
  obtain ⟨r, hr⟩ : ∃ r, g x = 1 + r := ⟨g x - 1, by have := G0 x; omega⟩
  rw [cnt_add, G1 x]
  congr 1
  rw [hr, cnt_add, cnt_one, if_pos rfl, cnt_gap g G2 x r (by omega)]

include G1 G2 G0 in
lemma odd_cnt_gap (x M : ℕ) (hM : M < g x + g (x + g x) + g (x + g x + g (x + g x)))
    (h : Odd (cnt T (x + 1) M (T x))) : g x ≤ M ∧ M < g x + g (x + g x) := by
  constructor
  · by_contra hc
    rw [cnt_gap g G2 x M (by omega)] at h
    exact absurd h (by decide)
  · by_contra hc
    have h0 := G0 x
    obtain ⟨r, hr⟩ : ∃ r, M = (g x - 1) + (g (x + g x) + (1 + r)) :=
      ⟨M - g x - g (x + g x), by omega⟩
    have hT1 : T (x + g x) = T x := G1 x
    have hT2 : T (x + g x + g (x + g x)) = T x := by rw [G1 (x + g x), hT1]
    have e : cnt T (x + 1) M (T x) = 2 := by
      rw [hr, cnt_add, cnt_gap g G2 x (g x - 1) (by omega), show x + 1 + (g x - 1) = x + g x by omega]
      have h2 := cnt_chain g G1 G2 G0 (x + g x) (1 + r)
      rw [hT1] at h2
      rw [h2, G1 (x + g x), hT1, cnt_add, cnt_one, if_pos hT2]
      have h3 := cnt_gap g G2 (x + g x + g (x + g x)) r (by omega)
      rw [hT2] at h3
      rw [h3]
    rw [e] at h
    exact absurd h (by decide)

include G1 G2 G0 in
/-- a coordinate whose orbit closes after two gaps is used exactly twice per period -/
lemma cnt_two_of_gaps {N : ℕ} (per : ∀ i, T (i + N) = T i) (x : ℕ)
    (h2 : g x + (g (x + g x) + 0) = N) : cnt T 0 N (T x) = 2 := by
  rw [← cnt_period per x, ← h2, cnt_chain g G1 G2 G0, cnt_chain g G1 G2 G0]
  simp [cnt]

include G1 G2 in
/-- **The gap criterion.** -/
theorem isCoilWord_of_gaps (hN : 2 * k + 2 ≤ N)
    (G3 : ∀ x, k + 1 ≤ g x)
    (G4 : ∀ x, N ≤ 2 * (g x + g (x + g x) + g (x + g x + g (x + g x))))
    (G5 : ∀ x, g x + (g (x + g x) + 0) = N ∨
      g x + (g (x + g x) + (g (x + g x + g (x + g x)) +
        (g (x + g x + g (x + g x) + g (x + g x + g (x + g x))) + 0))) = N)
    (hcount : ∀ t L, k + 1 ≤ L → 2 * L ≤ N →
      2 * #{m ∈ range L | g (t + m) ≤ L - 1 - m ∧ L - 1 - m < g (t + m) + g (t + m + g (t + m))} ≤ L - k) :
    IsCoilWord k N T := by
  have G0 : ∀ x, 1 ≤ g x := fun x => by have := G3 x; omega
  have per : ∀ i, T (i + N) = T i := by
    intro x
    rcases G5 x with h2 | h4
    · rw [← h2, add_zero, ← add_assoc, G1, G1]
    · rw [← h4, add_zero, ← add_assoc, ← add_assoc, ← add_assoc, G1, G1, G1, G1]
  apply isCoilWord_of_windows hN per
  · intro c
    by_cases hc : ∃ x, T x = c
    · obtain ⟨x, rfl⟩ := hc
      rw [← cnt_period per x]
      rcases G5 x with h2 | h4
      · have e : cnt T x N (T x) = 2 := by
          rw [← h2, cnt_chain g G1 G2 G0, cnt_chain g G1 G2 G0]
          simp [cnt]
        rw [e]
        exact ⟨1, rfl⟩
      · have e : cnt T x N (T x) = 4 := by
          rw [← h4, cnt_chain g G1 G2 G0, cnt_chain g G1 G2 G0, cnt_chain g G1 G2 G0, cnt_chain g G1 G2 G0]
          simp [cnt]
        rw [e]
        exact ⟨2, rfl⟩
    · have : cnt T 0 N c = 0 := cnt_eq_zero (fun i _ h => hc ⟨_, h⟩)
      rw [this]
      exact ⟨0, rfl⟩
  · intro t c
    by_contra hcon
    rw [not_le, cnt] at hcon
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hcon
    simp only [mem_filter, mem_range] at hi hj
    rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
    · have := G2 (t + i) (j - i) (by omega) (by have := G3 (t + i); omega)
      rw [show t + i + (j - i) = t + j by omega, hj.2, hi.2] at this
      exact this rfl
    · have := G2 (t + j) (i - j) (by omega) (by have := G3 (t + j); omega)
      rw [show t + j + (i - j) = t + i by omega, hj.2, hi.2] at this
      exact this rfl
  · intro t L h1 h2
    have hp := oddc_peel T t L
    have hc := hcount t L h1 h2
    have hle : #{m ∈ range L | Odd (cnt T (t + m + 1) (L - 1 - m) (T (t + m)))}
        ≤ #{m ∈ range L | g (t + m) ≤ L - 1 - m ∧ L - 1 - m < g (t + m) + g (t + m + g (t + m))} := by
      apply card_le_card
      intro m hm
      simp only [mem_filter, mem_range] at hm ⊢
      refine ⟨hm.1, odd_cnt_gap g G1 G2 G0 (t + m) (L - 1 - m) ?_ hm.2⟩
      have := G4 (t + m)
      omega
    omega

end gaps

end Coil

#print axioms Coil.isCoilWord_of_gaps
