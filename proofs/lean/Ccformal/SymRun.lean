import Ccformal.GapCriterion

/-!
# Byrnes' upper bound for symmetric codes with a long bit run:  `S(n, k, k+l) ≤ 4k + 2l`

`S(d,k,r)` (Byrnes, arXiv 1809.08428 / 2008.04839) = maximum length of a SYMMETRIC `(d,k)` circuit code
(`T (i + N/2) = T i`) whose transition sequence has a BIT RUN of length `≥ r` (`r` consecutive distinct transitions).
Theorem (`symRun_le`): for `2n = 3k + l + 1`, `k ≥ 2`, `l ≥ 1`, and under the hypothesis of Lemma 2 (`k > 3l-3` for
even `k`, `k > 3l-7` for odd `k`; Byrnes uses Douglas' bounds instead, for `k ≥ 2l-2 / 2l+1`):  `N ≤ 4k + 2l`.

Proof (after Byrnes: Lemma 3.5/3.6 of 1809.08428 and Lemma 2.1/2.3, Cor. 2.4 of 2008.04839, restated with window counts):
* the bit run followed by `k+1` more transitions has exactly `k` odd coordinates and uses every coordinate once or
  twice (`run_window`: `2n ≥ 2(n₁+n₂) = n₁ + 2k+l+1 ≥ 3k+l+1 = 2n`);
* half period `H ≥ 2k+l+2`: the next transition `α` equals `T (k+l)` and some `T j`, `j < l`; by symmetry `α` occurs
  twice in a window of length `≤ k+1` if `N ≤ 6k+4` (`symRun_gap`: no such code has `4k+2l < N ≤ 6k+4`, for ALL `k, l`;
  Lemma 2 then excludes `N ≥ 6k+6` in its range);
* `H = 2k+l+1`: `T 0` occurs in the second block, then `T 1` does not, and the window `[2, H+1)` has `k-1` odd coordinates.
-/

open Finset

namespace Coil

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.deprecated false

variable {α : Type*} [Fintype α] [DecidableEq α] {k N : ℕ} {T : ℕ → α}

/-- the shifted word is again a coil word -/
theorem IsCoilWord.shift (h : IsCoilWord k N T) (s : ℕ) : IsCoilWord k N (fun i => T (i + s)) := by
  have hc : ∀ t L c, cnt (fun i => T (i + s)) t L c = cnt T (t + s) L c := by
    intro t L c
    rw [cnt, cnt]
    exact congrArg card (filter_congr fun j _ => by rw [add_right_comm])
  have ho : ∀ t L, oddc (fun i => T (i + s)) t L = oddc T (t + s) L := by
    intro t L
    rw [oddc, oddc]
    simp_rw [hc]
  refine ⟨fun i => ?_, fun c => ?_, fun t L h1 h2 h3 => ?_⟩
  · show T (i + N + s) = T (i + s)
    rw [add_right_comm, h.per]
  · rw [hc, cnt_period h.per]; exact h.closed c
  · rw [ho] at h3 ⊢; exact h.spread _ L h1 h2 h3

lemma exists_of_cnt_pos {t L : ℕ} {c : α} (h : 1 ≤ cnt T t L c) : ∃ i, i < L ∧ T (t + i) = c := by
  rw [cnt] at h
  obtain ⟨i, hi⟩ := card_pos.mp h
  simp only [mem_filter, mem_range] at hi
  exact ⟨i, hi⟩

lemma oddc_add_P_le (T : ℕ → α) (t L : ℕ) : oddc T t L + P T t L ≤ Fintype.card α := by
  rw [oddc_eq_sum, P_eq_sum, ← sum_add_distrib]
  have : ∀ c ∈ (univ : Finset α), ((if Odd (cnt T t L c) then 1 else 0) + if cnt T t L c = 2 then 1 else 0) ≤ 1 := by
    intro c _
    split_ifs with h1 h2
    · rw [h2] at h1; exact absurd h1 (by decide)
    · omega
    · omega
    · omega
  have := sum_le_sum this
  simpa using this

lemma oddc_add_P_lt (T : ℕ → α) (t L : ℕ) (c0 : α) (h0 : cnt T t L c0 = 0) :
    oddc T t L + P T t L < Fintype.card α := by
  rw [oddc_eq_sum, P_eq_sum, ← sum_add_distrib]
  have h1 : ∀ c ∈ (univ : Finset α),
      ((if Odd (cnt T t L c) then 1 else 0) + if cnt T t L c = 2 then 1 else 0) ≤ 1 := by
    intro c _
    split_ifs with h1 h2
    · rw [h2] at h1; exact absurd h1 (by decide)
    · omega
    · omega
    · omega
  have h2 : ∃ c ∈ (univ : Finset α),
      ((if Odd (cnt T t L c) then 1 else 0) + if cnt T t L c = 2 then 1 else 0) < 1 :=
    ⟨c0, mem_univ _, by rw [h0]; simp⟩
  have := sum_lt_sum h1 h2
  simpa using this

section

variable {l H : ℕ} (h : IsCoilWord k N T) (hk : 2 ≤ k) (hl : 1 ≤ l)
  (hn : 2 * Fintype.card α = 3 * k + l + 1)
  (run : ∀ i j, i < k + l → j < k + l → T i = T j → i = j)

include run in
lemma cnt_run_le (c : α) : cnt T 0 (k + l) c ≤ 1 := by
  rw [cnt, card_le_one]
  intro i hi j hj
  simp only [mem_filter, mem_range, zero_add] at hi hj
  exact run i j hi.1 hj.1 (by rw [hi.2, hj.2])

include h hk hl hn run in
/-- Lemma 3.5 / 2.1: the bit run plus `k+1` further transitions -/
lemma run_window (hN : 4 * k + 2 * l + 2 ≤ N) :
    oddc T 0 (k + l + (k + 1)) = k ∧ ∀ c, 1 ≤ cnt T 0 (k + l + (k + 1)) c ∧ cnt T 0 (k + l + (k + 1)) c ≤ 2 ∧
      cnt T 0 (k + l) c ≤ 1 ∧ cnt T (k + l) (k + 1) c ≤ 1 := by
  have hk1 : 1 ≤ k := by omega
  have hN2 : 2 * k + 2 ≤ N := by omega
  have hle2 : ∀ c, cnt T 0 (k + l + (k + 1)) c ≤ 2 := by
    intro c
    rw [cnt_add, zero_add]
    have := cnt_run_le run c
    have := cnt_short h hk1 hN2 (t := k + l) (L := k + 1) le_rfl c
    omega
  have hd := decomp (T := T) (t := 0) (L := k + l + (k + 1)) hle2
  have hf := f1 h hk1 (t := 0) (L := k + l + (k + 1)) (by omega) (by omega)
  have hP := oddc_add_P_le T 0 (k + l + (k + 1))
  refine ⟨by omega, fun c => ⟨?_, hle2 c, cnt_run_le run c, cnt_short h hk1 hN2 le_rfl c⟩⟩
  by_contra hc
  have := oddc_add_P_lt T 0 (k + l + (k + 1)) c (by omega)
  omega

include h hk hl hn run in
/-- **`S(n, k, k+l) ≤ 4k + 2l`** for a symmetric coil word whose first `k+l` transitions are distinct -/
theorem symRun_le_aux (hNH : N = 2 * H) (sym : ∀ i, T (i + H) = T i)
    (hN6 : N ≤ 6 * k + 4) : N ≤ 4 * k + 2 * l := by
  by_contra hcon
  have hk1 : 1 ≤ k := by omega
  have hN : 4 * k + 2 * l + 2 ≤ N := by omega
  have hN2 : 2 * k + 2 ≤ N := by omega
  obtain ⟨hodd, hall⟩ := run_window h hk hl hn run hN
  have h01 : T 0 ≠ T 1 := fun e => by have := run 0 1 (by omega) (by omega) e; omega
  have sym0 : T H = T 0 := by have := sym 0; rwa [zero_add] at this
  by_cases hH : H = k + l + (k + 1)
  · -- half period 2k+l+1
    -- (b) T 0 occurs twice in the half period
    have hb := oddc_succ T 0 H
    have hfb := f1 h hk1 (t := 0) (L := H + 1) (by omega) (by omega)
    rw [zero_add, sym0] at hb
    rw [← hH] at hodd hall
    have hev : ¬ Odd (cnt T 0 H (T 0)) := by
      intro ho
      rw [if_pos ho] at hb
      omega
    rw [if_neg hev] at hb
    obtain ⟨c1, c2, c3, c4⟩ := hall (T 0)
    have h2 : cnt T 0 H (T 0) = 2 := by
      rw [Nat.not_odd_iff_even, Nat.even_iff] at hev
      omega
    have hsplit : ∀ c, cnt T 0 H c = cnt T 0 (k + l) c + cnt T (k + l) (k + 1) c := by
      intro c; rw [hH, cnt_add, zero_add]
    have h0b : cnt T (k + l) (k + 1) (T 0) = 1 := by have := hsplit (T 0); omega
    -- (c) the window (ω2, α, T 0)
    have hc := oddc_succ T (k + l) (k + 1)
    rw [show k + l + (k + 1) = H from hH.symm, sym0, h0b,
      oddc_short h hk1 hN2 le_rfl, if_pos (by decide)] at hc
    -- (d) T 1 does not occur in (ω2, α)
    have hd := oddc_succ T (k + l) (k + 1 + 1)
    have hfd := f1 h hk1 (t := k + l) (L := k + 1 + 1 + 1) (by omega) (by omega)
    rw [show k + l + (k + 1 + 1) = 1 + H by omega, sym 1, hc] at hd
    have hev1 : ¬ Odd (cnt T (k + l) (k + 1 + 1) (T 1)) := by
      intro ho
      rw [if_pos ho] at hd
      omega
    have e1 : cnt T (k + l) (k + 1 + 1) (T 1) = cnt T (k + l) (k + 1) (T 1) := by
      rw [cnt_add, cnt_one, show k + l + (k + 1) = H from hH.symm, sym0, if_neg h01, add_zero]
    obtain ⟨d1, d2, d3, d4⟩ := hall (T 1)
    have h1b : cnt T (k + l) (k + 1) (T 1) = 0 := by
      rw [e1, Nat.not_odd_iff_even, Nat.even_iff] at hev1
      omega
    have h1H : cnt T 0 H (T 1) = 1 := by have := hsplit (T 1); omega
    -- (f) peel T 0 and T 1 from the left of [0, H+1)
    have p1 := oddc_cons T 0 H
    simp only [zero_add] at p1
    have q1 : cnt T 0 (1 + H) (T 0) = 1 + cnt T 1 H (T 0) := by rw [cnt_add, cnt_one, if_pos rfl, zero_add]
    have q2 : cnt T 0 (H + 1) (T 0) = 2 + 1 := by rw [cnt_add, cnt_one, zero_add, sym0, if_pos rfl, h2]
    rw [Nat.add_comm 1 H, q2] at q1
    rw [show cnt T 1 H (T 0) = 2 by omega, if_neg (by decide)] at p1
    have p2 := oddc_cons T 1 (H - 1)
    rw [show H - 1 + 1 = H by omega, show (1 : ℕ) + 1 = 2 from rfl] at p2
    have q3 : cnt T 0 (2 + (H - 1)) (T 1) = cnt T 0 2 (T 1) + cnt T 2 (H - 1) (T 1) := by rw [cnt_add, zero_add]
    have q4 : cnt T 0 2 (T 1) = 1 := by
      rw [show 2 = 1 + 1 by rfl, cnt_add, cnt_one, cnt_one, zero_add, if_neg h01, if_pos rfl]
    have q5 : cnt T 0 (H + 1) (T 1) = 1 := by
      rw [cnt_add, cnt_one, zero_add, sym0, if_neg h01, h1H]
    rw [show 2 + (H - 1) = H + 1 by omega, q5, q4] at q3
    rw [show cnt T 2 (H - 1) (T 1) = 0 by omega, if_neg (by decide)] at p2
    have hff := f1 h hk1 (t := 2) (L := H - 1) (by omega) (by omega)
    omega
  · -- half period ≥ 2k+l+2
    have hH2 : k + l + (k + 1) + 1 ≤ H := by omega
    have ha := oddc_succ T 0 (k + l + (k + 1))
    have hfa := f1 h hk1 (t := 0) (L := k + l + (k + 1) + 1) (by omega) (by omega)
    rw [zero_add, hodd] at ha
    have hev : ¬ Odd (cnt T 0 (k + l + (k + 1)) (T (k + l + (k + 1)))) := by
      intro ho
      rw [if_pos ho] at ha
      omega
    obtain ⟨c1, c2, c3, c4⟩ := hall (T (k + l + (k + 1)))
    have hsplit : cnt T 0 (k + l + (k + 1)) (T (k + l + (k + 1)))
        = cnt T 0 (k + l) (T (k + l + (k + 1))) + cnt T (k + l) (k + 1) (T (k + l + (k + 1))) := by
      rw [cnt_add, zero_add]
    rw [Nat.not_odd_iff_even, Nat.even_iff] at hev
    have ca : cnt T 0 (k + l) (T (k + l + (k + 1))) = 1 := by omega
    have cb : cnt T (k + l) (k + 1) (T (k + l + (k + 1))) = 1 := by omega
    -- (i) α = T (k+l)
    have hi : T (k + l) = T (k + l + (k + 1)) := by
      obtain ⟨i, hi1, hi2⟩ := exists_of_cnt_pos (le_of_eq cb.symm)
      by_contra hne
      have hi0 : i ≠ 0 := by
        rintro rfl
        exact hne (by simpa using hi2)
      have := two_le_cnt (T := T) (t := k + l + 1) (L := k + 1) (i := i - 1) (j := k)
        (c := T (k + l + (k + 1))) (by omega) (by omega)
        (by rw [show k + l + 1 + (i - 1) = k + l + i by omega]; exact hi2)
        (by rw [show k + l + 1 + k = k + l + (k + 1) by omega])
      have := cnt_short h hk1 hN2 (t := k + l + 1) (L := k + 1) le_rfl (T (k + l + (k + 1)))
      omega
    -- (ii) α = T j0 with j0 < l
    obtain ⟨j0, hj1, hj2⟩ := exists_of_cnt_pos (le_of_eq ca.symm)
    rw [zero_add] at hj2
    have hj0 : j0 < l := by
      by_contra hge
      have := two_le_cnt (T := T) (t := l) (L := k + 1) (i := j0 - l) (j := k)
        (c := T (k + l + (k + 1))) (by omega) (by omega)
        (by rw [show l + (j0 - l) = j0 by omega]; exact hj2)
        (by rw [show l + k = k + l by omega]; exact hi)
      have := cnt_short h hk1 hN2 (t := l) (L := k + 1) le_rfl (T (k + l + (k + 1)))
      omega
    -- (iii) α twice in a short window across the half period
    have hs : T (k + l + (k + 1) + (H + j0 - (k + l + (k + 1)))) = T (k + l + (k + 1)) := by
      rw [show k + l + (k + 1) + (H + j0 - (k + l + (k + 1))) = j0 + H by omega, sym j0, hj2]
    have := two_le_cnt (T := T) (t := k + l + (k + 1)) (L := H + j0 + 1 - (k + l + (k + 1))) (i := 0)
      (j := H + j0 - (k + l + (k + 1))) (c := T (k + l + (k + 1))) (by omega) (by omega) (by rw [add_zero]) hs
    have := cnt_short h hk1 hN2 (t := k + l + (k + 1)) (L := H + j0 + 1 - (k + l + (k + 1))) (by omega)
      (T (k + l + (k + 1)))
    omega

end

/-- `T` is the transition word of a SYMMETRIC spread-`k` circuit code of length `N` with a bit run of length `r` -/
def SymRun (k N r : ℕ) (T : ℕ → α) : Prop :=
  IsCoilWord k N T ∧ (∀ i, T (i + N / 2) = T i) ∧ ∃ t, ∀ i j, i < r → j < r → T (t + i) = T (t + j) → i = j

/-- **No symmetric code with a bit run of length `k+l` has length in `(4k+2l, 6k+4]`** -- for ALL `k ≥ 2`, `l ≥ 1`
(no hypothesis relating `k` and `l`). -/
theorem symRun_gap {l : ℕ} (hS : SymRun k N (k + l) T) (hk : 2 ≤ k) (hl : 1 ≤ l)
    (hn : 2 * Fintype.card α = 3 * k + l + 1) : N ≤ 4 * k + 2 * l ∨ 6 * k + 6 ≤ N := by
  obtain ⟨h, sym, t, run⟩ := hS
  obtain ⟨H, hH⟩ := even_length h
  have hNH : N = 2 * H := by omega
  have hH2 : N / 2 = H := by omega
  rw [hH2] at sym
  by_cases hN6 : N ≤ 6 * k + 4
  · left
    refine symRun_le_aux (T := fun i => T (i + t)) (h.shift t) hk hl hn (fun i j hi hj e => ?_) hNH
      (fun i => ?_) hN6
    · exact run i j hi hj (by rw [Nat.add_comm t i, Nat.add_comm t j]; exact e)
    · show T (i + H + t) = T (i + t)
      rw [add_right_comm, sym]
  · right; omega

/-- **Byrnes' upper bound `S(n, k, k+l) ≤ 4k + 2l`** (in the range of Lemma 2: `k > 3l - 3` for even `k`,
`k > 3l - 7` for odd `k`). -/
theorem symRun_le {l : ℕ} (hS : SymRun k N (k + l) T) (hk : 2 ≤ k) (hl : 1 ≤ l)
    (hn : 2 * Fintype.card α = 3 * k + l + 1)
    (hlong : 6 * Fintype.card α + 6 * ((k + 2) / 2) < k + k % 2 + 12 * (k + 1)) : N ≤ 4 * k + 2 * l := by
  rcases symRun_gap hS hk hl hn with h1 | h2
  · exact h1
  · exfalso
    have := no_long hS.1 (by omega) (by omega)
    omega

end Coil

#print axioms Coil.symRun_gap
#print axioms Coil.symRun_le
