import Ccformal.Basic

/-!
# Spread-`k` PATHS near `d = 3k/2`:  `P(d,k) ≤ 6(d-k) - 5`      (S178)

A spread-`k` path with `L` edges in the `d`-cube: vertices `v_0, …, v_L`, consecutive ones adjacent, and
`d_H(v_i, v_j) < k → |i - j| = d_H(v_i, v_j)`.  Its transition word `T` satisfies: every window `[s, s+w)`
inside `[0, L)` with fewer than `k` odd coordinates has exactly `w` odd coordinates (`IsPathWord`).

* `four_piece`: the Four-Piece Lemma. Four consecutive windows of length `≤ k+1`; the six unions of consecutive
  pieces have odd-counts summing to at most `6d - (total length)`.
* `path_bound_odd`:  `k` odd,  `8k+6 ≤ 6d ≤ 10k+8`:  `L ≤ 6(d-k) - 5`.
* `path_bound_even`: `k` even, `9k+7 ≤ 6d ≤ 10k+6`:  `L ≤ 6(d-k) - 5`  (twelve odd-length windows).
* `path_length_bound`: both, for vertex paths, with `l = 2d - 3k - 1 ≥ 2`:  `L ≤ 3k + 3l - 2` if `k ≥ 3l - 5` (k odd)
  resp. `k ≥ 3l - 3` (k even).

Written proof: `PROOF_upper.md` (paths folder; working name PROOF_general.md).
-/

open Finset

namespace Coil

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {α : Type*} [Fintype α] [DecidableEq α] {k L : ℕ} {T : ℕ → α}

/-- `T` (only `T 0, …, T (L-1)` matter) is the transition word of a spread-`k` path with `L` edges. -/
structure IsPathWord (k L : ℕ) (T : ℕ → α) : Prop where
  spread : ∀ s w, s + w ≤ L → oddc T s w < k → oddc T s w = w

namespace IsPathWord

lemma mono (h : IsPathWord k L T) {L' : ℕ} (hL : L' ≤ L) : IsPathWord k L' T :=
  ⟨fun s w hs hw => h.spread s w (by omega) hw⟩

/-- (F1) a window of length `≥ k` has at least `k` odd coordinates -/
lemma ge (h : IsPathWord k L T) {s w : ℕ} (hs : s + w ≤ L) (hw : k ≤ w) : k ≤ oddc T s w := by
  by_contra hc
  have := h.spread s w hs (by omega)
  omega

/-- (F1) … and at least `k+1` if its length has the other parity -/
lemma gt (h : IsPathWord k L T) {s w : ℕ} (hs : s + w ≤ L) (hw : k ≤ w) (hp : (w + k) % 2 = 1) :
    k + 1 ≤ oddc T s w := by
  have h1 := h.ge hs hw
  have h2 := oddc_parity T s w
  rw [Nat.odd_iff, Nat.odd_iff] at h2
  omega

/-- (F2) a window of length `≤ k+1` contains every coordinate at most once -/
lemma cnt_le_one (h : IsPathWord k L T) {s w : ℕ} (hs : s + w ≤ L) (hw : w ≤ k + 1) (c : α) :
    cnt T s w c ≤ 1 := by
  have e : oddc T s w = w := by
    by_cases h1 : oddc T s w < k
    · exact h.spread s w hs h1
    · have h2 := oddc_le T s w
      have h3 := oddc_parity T s w
      rw [Nat.odd_iff, Nat.odd_iff] at h3
      omega
  by_contra hc
  have : oddc T s w < w := by
    calc oddc T s w = ∑ c, if Odd (cnt T s w c) then 1 else 0 := oddc_eq_sum T s w
      _ < ∑ c, cnt T s w c := by
          apply sum_lt_sum
          · intro c _
            split_ifs with h'
            · exact h'.pos
            · exact Nat.zero_le _
          · refine ⟨c, mem_univ _, ?_⟩
            split_ifs <;> omega
      _ = w := sum_cnt T s w
  omega

end IsPathWord

/-- prefix form of `cnt_add` -/
lemma cnt_pre (T : ℕ → α) {x w y : ℕ} (hy : y = x + w) (c : α) :
    cnt T 0 y c = cnt T 0 x c + cnt T x w c := by
  subst hy
  rw [cnt_add, zero_add]

lemma cnt_split (T : ℕ → α) {s w : ℕ} (a : ℕ) {s' b : ℕ} (hw : w = a + b) (hs : s' = s + a) (c : α) :
    cnt T s w c = cnt T s a c + cnt T s' b c := by
  subst hw hs
  exact cnt_add T s a b c

lemma pat4 : ∀ a1 < 2, ∀ a2 < 2, ∀ a3 < 2, ∀ a4 < 2,
    (if Odd (a1 + a2) then 1 else 0) + (if Odd (a2 + a3) then 1 else 0) + (if Odd (a3 + a4) then 1 else 0)
      + (if Odd (a1 + a2 + a3) then 1 else 0) + (if Odd (a2 + a3 + a4) then 1 else 0)
      + (if Odd (a1 + a2 + a3 + a4) then 1 else 0) + (a1 + a2 + a3 + a4) ≤ 6 := by
  decide

/-- **Four-Piece Lemma.** -/
theorem four_piece (h : IsPathWord k L T) (t x1 x2 x3 x4 : ℕ) (hL : t + x1 + x2 + x3 + x4 ≤ L)
    (h1 : x1 ≤ k + 1) (h2 : x2 ≤ k + 1) (h3 : x3 ≤ k + 1) (h4 : x4 ≤ k + 1) :
    oddc T t (x1 + x2) + oddc T (t + x1) (x2 + x3) + oddc T (t + x1 + x2) (x3 + x4)
      + oddc T t (x1 + x2 + x3) + oddc T (t + x1) (x2 + x3 + x4) + oddc T t (x1 + x2 + x3 + x4)
      + (x1 + x2 + x3 + x4) ≤ 6 * Fintype.card α := by
  have key : ∀ c : α,
      (if Odd (cnt T t (x1 + x2) c) then 1 else 0) + (if Odd (cnt T (t + x1) (x2 + x3) c) then 1 else 0)
        + (if Odd (cnt T (t + x1 + x2) (x3 + x4) c) then 1 else 0)
        + (if Odd (cnt T t (x1 + x2 + x3) c) then 1 else 0)
        + (if Odd (cnt T (t + x1) (x2 + x3 + x4) c) then 1 else 0)
        + (if Odd (cnt T t (x1 + x2 + x3 + x4) c) then 1 else 0) + cnt T t (x1 + x2 + x3 + x4) c ≤ 6 := by
    intro c
    have b1 := h.cnt_le_one (s := t) (w := x1) (by omega) h1 c
    have b2 := h.cnt_le_one (s := t + x1) (w := x2) (by omega) h2 c
    have b3 := h.cnt_le_one (s := t + x1 + x2) (w := x3) (by omega) h3 c
    have b4 := h.cnt_le_one (s := t + x1 + x2 + x3) (w := x4) (by omega) h4 c
    have e12 : cnt T t (x1 + x2) c = cnt T t x1 c + cnt T (t + x1) x2 c := cnt_add T t x1 x2 c
    have e23 : cnt T (t + x1) (x2 + x3) c = cnt T (t + x1) x2 c + cnt T (t + x1 + x2) x3 c :=
      cnt_add T (t + x1) x2 x3 c
    have e34 : cnt T (t + x1 + x2) (x3 + x4) c = cnt T (t + x1 + x2) x3 c + cnt T (t + x1 + x2 + x3) x4 c :=
      cnt_add T (t + x1 + x2) x3 x4 c
    have e123 : cnt T t (x1 + x2 + x3) c = cnt T t x1 c + cnt T (t + x1) x2 c + cnt T (t + x1 + x2) x3 c := by
      rw [cnt_split T (x1 + x2) rfl (show t + x1 + x2 = t + (x1 + x2) by omega) c, e12]
    have e234 : cnt T (t + x1) (x2 + x3 + x4) c
        = cnt T (t + x1) x2 c + cnt T (t + x1 + x2) x3 c + cnt T (t + x1 + x2 + x3) x4 c := by
      rw [cnt_split T (x2 + x3) rfl (show t + x1 + x2 + x3 = t + x1 + (x2 + x3) by omega) c, e23]
    have e1234 : cnt T t (x1 + x2 + x3 + x4) c
        = cnt T t x1 c + cnt T (t + x1) x2 c + cnt T (t + x1 + x2) x3 c + cnt T (t + x1 + x2 + x3) x4 c := by
      rw [cnt_split T (x1 + x2 + x3) rfl (show t + x1 + x2 + x3 = t + (x1 + x2 + x3) by omega) c, e123]
    rw [e1234, e234, e123, e34, e23, e12]
    exact pat4 _ (by omega) _ (by omega) _ (by omega) _ (by omega)
  have S := sum_le_sum (fun c (_ : c ∈ (univ : Finset α)) => key c)
  simp only [sum_add_distrib, ← oddc_eq_sum, sum_cnt, sum_const, card_univ, smul_eq_mul] at S
  omega

/-- **Upper bound, `k` odd**: for `(4k+3)/3 ≤ d ≤ (5k+4)/3` a spread-`k` path in the `d`-cube has at most
`6(d-k) - 5` edges. -/
theorem path_bound_odd (h : IsPathWord k L T) (hk : Odd k) (h1 : 8 * k + 6 ≤ 6 * Fintype.card α)
    (h2 : 6 * Fintype.card α ≤ 10 * k + 8) : L + 6 * k + 5 ≤ 6 * Fintype.card α := by
  by_contra hc
  have hk2 : k % 2 = 1 := Nat.odd_iff.mp hk
  obtain ⟨m, hm⟩ : ∃ m, m + 8 * k + 6 = 6 * Fintype.card α := ⟨6 * Fintype.card α - 8 * k - 6, by omega⟩
  obtain ⟨x1, x4, hx, hx1, hx4, ex1, ex4⟩ :
      ∃ x1 x4, x1 + x4 = m ∧ x1 ≤ k + 1 ∧ x4 ≤ k + 1 ∧ x1 % 2 = 0 ∧ x4 % 2 = 0 := by
    by_cases hm' : m ≤ k + 1
    · exact ⟨m, 0, by omega, hm', by omega, by omega, rfl⟩
    · exact ⟨k + 1, m - (k + 1), by omega, le_refl _, by omega, by omega, by omega⟩
  have F := four_piece h 0 x1 (k + 1) (k + 1) x4 (by omega) hx1 le_rfl le_rfl hx4
  have g1 := h.gt (s := 0) (w := x1 + (k + 1)) (by omega) (by omega) (by omega)
  have g2 := h.gt (s := 0 + x1) (w := k + 1 + (k + 1)) (by omega) (by omega) (by omega)
  have g3 := h.gt (s := 0 + x1 + (k + 1)) (w := k + 1 + x4) (by omega) (by omega) (by omega)
  have g4 := h.gt (s := 0) (w := x1 + (k + 1) + (k + 1)) (by omega) (by omega) (by omega)
  have g5 := h.gt (s := 0 + x1) (w := k + 1 + (k + 1) + x4) (by omega) (by omega) (by omega)
  have g6 := h.gt (s := 0) (w := x1 + (k + 1) + (k + 1) + x4) (by omega) (by omega) (by omega)
  omega

/-- the twelve-window inequality for one coordinate, described by its counts in nine pieces -/
lemma pat12 : ∀ p1 < 2, ∀ p2 < 2, ∀ p3 < 2, ∀ p4 < 2, ∀ p5 < 2, ∀ p6 < 2, ∀ p7 < 2, ∀ p8 < 2, ∀ p9 < 2,
    p1 + p2 + p3 ≤ 1 → p3 + p4 + p5 ≤ 1 → p5 + p6 ≤ 1 → p6 + p7 ≤ 1 → p7 + p8 + p9 ≤ 1 →
    (if Odd (p1 + p2 + p3 + p4 + p5) then 1 else 0)
      + (if Odd (p1 + p2 + p3 + p4 + p5 + p6) then 1 else 0)
      + (if Odd (p1 + p2 + p3 + p4 + p5 + p6 + p7 + p8) then 1 else 0)
      + (if Odd (p3 + p4 + p5 + p6) then 1 else 0)
      + (if Odd (p3 + p4 + p5 + p6 + p7 + p8) then 1 else 0)
      + (if Odd (p6 + p7 + p8 + p9) then 1 else 0)
      + (if Odd (p4 + p5 + p6 + p7 + p8 + p9) then 1 else 0)
      + (if Odd (p2 + p3 + p4 + p5 + p6 + p7 + p8 + p9) then 1 else 0)
      + (if Odd (p4 + p5 + p6 + p7) then 1 else 0)
      + (if Odd (p2 + p3 + p4 + p5 + p6 + p7) then 1 else 0)
      + (if Odd (p2 + p3 + p4) then 1 else 0)
      + (if Odd (p5 + p6 + p7 + p8) then 1 else 0)
      + 2 * (p1 + p2 + p3 + p4 + p5 + p6 + p7 + p8 + p9) ≤ 12 + p1 + p9 := by
  intro p1 h1 p2 h2 p3 h3 p4 h4 p5 h5 p6 h6 p7 h7 p8 h8 p9 h9 c1 c2 c3 c4 c5
  interval_cases p1 <;> interval_cases p2 <;> interval_cases p3 <;> try omega
  all_goals (interval_cases p4 <;> interval_cases p5 <;> try omega)
  all_goals (interval_cases p6 <;> interval_cases p7 <;> try omega)
  all_goals (interval_cases p8 <;> interval_cases p9 <;> first | omega | decide)

set_option maxHeartbeats 1600000 in
/-- **Twelve-window lemma** (`k = j+1`, word length `3j+6+r = 3k+3+r`, `r ≤ j`). -/
theorem twelve_windows (h : IsPathWord (j + 1) (3 * j + 6 + r) T) (hr : r ≤ j) :
    oddc T 0 (2 * j + 3) + oddc T 0 (3 * j + 4) + oddc T 0 (3 * j + 5 + r) + oddc T (j + 1) (2 * j + 3)
      + oddc T (j + 1) (2 * j + 4 + r) + oddc T (2 * j + 3) (j + 3 + r) + oddc T (j + 2) (2 * j + 4 + r)
      + oddc T 1 (3 * j + 5 + r) + oddc T (j + 2) (2 * j + 3) + oddc T 1 (3 * j + 4) + oddc T 1 (2 * j + 1)
      + oddc T (2 * j + 2) (j + 3 + r) + 2 * (3 * j + 6 + r) ≤ 12 * Fintype.card α + 2 := by
  have key : ∀ c : α,
      (if Odd (cnt T 0 (2 * j + 3) c) then 1 else 0) + (if Odd (cnt T 0 (3 * j + 4) c) then 1 else 0)
        + (if Odd (cnt T 0 (3 * j + 5 + r) c) then 1 else 0) + (if Odd (cnt T (j + 1) (2 * j + 3) c) then 1 else 0)
        + (if Odd (cnt T (j + 1) (2 * j + 4 + r) c) then 1 else 0)
        + (if Odd (cnt T (2 * j + 3) (j + 3 + r) c) then 1 else 0)
        + (if Odd (cnt T (j + 2) (2 * j + 4 + r) c) then 1 else 0)
        + (if Odd (cnt T 1 (3 * j + 5 + r) c) then 1 else 0) + (if Odd (cnt T (j + 2) (2 * j + 3) c) then 1 else 0)
        + (if Odd (cnt T 1 (3 * j + 4) c) then 1 else 0) + (if Odd (cnt T 1 (2 * j + 1) c) then 1 else 0)
        + (if Odd (cnt T (2 * j + 2) (j + 3 + r) c) then 1 else 0)
        + 2 * cnt T 0 (3 * j + 6 + r) c ≤ 12 + cnt T 0 1 c + cnt T (3 * j + 5 + r) 1 c := by
    intro c
    -- prefix counts at the ten boundaries, as sums of the nine pieces
    have q2 := cnt_pre T (x := 1) (w := j) (y := j + 1) (by omega) c
    have q3 := cnt_pre T (x := j + 1) (w := 1) (y := j + 2) (by omega) c
    have q4 := cnt_pre T (x := j + 2) (w := j) (y := 2 * j + 2) (by omega) c
    have q5 := cnt_pre T (x := 2 * j + 2) (w := 1) (y := 2 * j + 3) (by omega) c
    have q6 := cnt_pre T (x := 2 * j + 3) (w := j + 1) (y := 3 * j + 4) (by omega) c
    have q7 := cnt_pre T (x := 3 * j + 4) (w := 1) (y := 3 * j + 5) (by omega) c
    have q8 := cnt_pre T (x := 3 * j + 5) (w := r) (y := 3 * j + 5 + r) (by omega) c
    have q9 := cnt_pre T (x := 3 * j + 5 + r) (w := 1) (y := 3 * j + 6 + r) (by omega) c
    -- the windows not starting at 0
    have w4 := cnt_pre T (x := j + 1) (w := 2 * j + 3) (y := 3 * j + 4) (by omega) c
    have w5 := cnt_pre T (x := j + 1) (w := 2 * j + 4 + r) (y := 3 * j + 5 + r) (by omega) c
    have w6 := cnt_pre T (x := 2 * j + 3) (w := j + 3 + r) (y := 3 * j + 6 + r) (by omega) c
    have w7 := cnt_pre T (x := j + 2) (w := 2 * j + 4 + r) (y := 3 * j + 6 + r) (by omega) c
    have w8 := cnt_pre T (x := 1) (w := 3 * j + 5 + r) (y := 3 * j + 6 + r) (by omega) c
    have w9 := cnt_pre T (x := j + 2) (w := 2 * j + 3) (y := 3 * j + 5) (by omega) c
    have w10 := cnt_pre T (x := 1) (w := 3 * j + 4) (y := 3 * j + 5) (by omega) c
    have w11 := cnt_pre T (x := 1) (w := 2 * j + 1) (y := 2 * j + 2) (by omega) c
    have w12 := cnt_pre T (x := 2 * j + 2) (w := j + 3 + r) (y := 3 * j + 5 + r) (by omega) c
    -- short windows: at most one occurrence
    have c1 := h.cnt_le_one (s := 0) (w := j + 2) (by omega) (by omega) c
    have c2 := h.cnt_le_one (s := j + 1) (w := j + 2) (by omega) (by omega) c
    have c3 := h.cnt_le_one (s := 2 * j + 2) (w := j + 2) (by omega) (by omega) c
    have c4 := h.cnt_le_one (s := 2 * j + 3) (w := j + 2) (by omega) (by omega) c
    have c5 := h.cnt_le_one (s := 3 * j + 4) (w := r + 2) (by omega) (by omega) c
    have d2 := cnt_pre T (x := j + 1) (w := j + 2) (y := 2 * j + 3) (by omega) c
    have d3 := cnt_pre T (x := 2 * j + 2) (w := j + 2) (y := 3 * j + 4) (by omega) c
    have d4 := cnt_pre T (x := 2 * j + 3) (w := j + 2) (y := 3 * j + 5) (by omega) c
    have d5 := cnt_pre T (x := 3 * j + 4) (w := r + 2) (y := 3 * j + 6 + r) (by omega) c
    have P := pat12 (cnt T 0 1 c) (by omega) (cnt T 1 j c) (by omega) (cnt T (j + 1) 1 c) (by omega)
      (cnt T (j + 2) j c) (by omega) (cnt T (2 * j + 2) 1 c) (by omega) (cnt T (2 * j + 3) (j + 1) c) (by omega)
      (cnt T (3 * j + 4) 1 c) (by omega) (cnt T (3 * j + 5) r c) (by omega) (cnt T (3 * j + 5 + r) 1 c) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
    rw [show cnt T 0 (2 * j + 3) c
          = cnt T 0 1 c + cnt T 1 j c + cnt T (j + 1) 1 c + cnt T (j + 2) j c + cnt T (2 * j + 2) 1 c by omega,
      show cnt T 0 (3 * j + 4) c
          = cnt T 0 1 c + cnt T 1 j c + cnt T (j + 1) 1 c + cnt T (j + 2) j c + cnt T (2 * j + 2) 1 c
            + cnt T (2 * j + 3) (j + 1) c by omega,
      show cnt T 0 (3 * j + 5 + r) c
          = cnt T 0 1 c + cnt T 1 j c + cnt T (j + 1) 1 c + cnt T (j + 2) j c + cnt T (2 * j + 2) 1 c
            + cnt T (2 * j + 3) (j + 1) c + cnt T (3 * j + 4) 1 c + cnt T (3 * j + 5) r c by omega,
      show cnt T (j + 1) (2 * j + 3) c
          = cnt T (j + 1) 1 c + cnt T (j + 2) j c + cnt T (2 * j + 2) 1 c + cnt T (2 * j + 3) (j + 1) c by omega,
      show cnt T (j + 1) (2 * j + 4 + r) c
          = cnt T (j + 1) 1 c + cnt T (j + 2) j c + cnt T (2 * j + 2) 1 c + cnt T (2 * j + 3) (j + 1) c
            + cnt T (3 * j + 4) 1 c + cnt T (3 * j + 5) r c by omega,
      show cnt T (2 * j + 3) (j + 3 + r) c
          = cnt T (2 * j + 3) (j + 1) c + cnt T (3 * j + 4) 1 c + cnt T (3 * j + 5) r c
            + cnt T (3 * j + 5 + r) 1 c by omega,
      show cnt T (j + 2) (2 * j + 4 + r) c
          = cnt T (j + 2) j c + cnt T (2 * j + 2) 1 c + cnt T (2 * j + 3) (j + 1) c
            + cnt T (3 * j + 4) 1 c + cnt T (3 * j + 5) r c + cnt T (3 * j + 5 + r) 1 c by omega,
      show cnt T 1 (3 * j + 5 + r) c
          = cnt T 1 j c + cnt T (j + 1) 1 c + cnt T (j + 2) j c + cnt T (2 * j + 2) 1 c
            + cnt T (2 * j + 3) (j + 1) c + cnt T (3 * j + 4) 1 c + cnt T (3 * j + 5) r c
            + cnt T (3 * j + 5 + r) 1 c by omega,
      show cnt T (j + 2) (2 * j + 3) c
          = cnt T (j + 2) j c + cnt T (2 * j + 2) 1 c + cnt T (2 * j + 3) (j + 1) c + cnt T (3 * j + 4) 1 c by omega,
      show cnt T 1 (3 * j + 4) c
          = cnt T 1 j c + cnt T (j + 1) 1 c + cnt T (j + 2) j c + cnt T (2 * j + 2) 1 c
            + cnt T (2 * j + 3) (j + 1) c + cnt T (3 * j + 4) 1 c by omega,
      show cnt T 1 (2 * j + 1) c = cnt T 1 j c + cnt T (j + 1) 1 c + cnt T (j + 2) j c by omega,
      show cnt T (2 * j + 2) (j + 3 + r) c
          = cnt T (2 * j + 2) 1 c + cnt T (2 * j + 3) (j + 1) c + cnt T (3 * j + 4) 1 c + cnt T (3 * j + 5) r c by omega,
      show cnt T 0 (3 * j + 6 + r) c
          = cnt T 0 1 c + cnt T 1 j c + cnt T (j + 1) 1 c + cnt T (j + 2) j c + cnt T (2 * j + 2) 1 c
            + cnt T (2 * j + 3) (j + 1) c + cnt T (3 * j + 4) 1 c + cnt T (3 * j + 5) r c
            + cnt T (3 * j + 5 + r) 1 c by omega]
    exact P
  have S := sum_le_sum (fun c (_ : c ∈ (univ : Finset α)) => key c)
  simp only [sum_add_distrib, ← oddc_eq_sum, ← mul_sum, sum_cnt, sum_const, card_univ, smul_eq_mul] at S
  omega

/-- **Upper bound, `k` even**: for `(9k+7)/6 ≤ d ≤ (5k+3)/3` a spread-`k` path in the `d`-cube has at most
`6(d-k) - 5` edges. -/
theorem path_bound_even (h : IsPathWord k L T) (hk : Even k) (hk1 : 1 ≤ k)
    (h1 : 9 * k + 7 ≤ 6 * Fintype.card α) (h2 : 6 * Fintype.card α ≤ 10 * k + 6) :
    L + 6 * k + 5 ≤ 6 * Fintype.card α := by
  by_contra hc
  have hk2 : k % 2 = 0 := Nat.even_iff.mp hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨r, hr⟩ : ∃ r, 3 * j + 6 + r + 6 * (j + 1) + 4 = 6 * Fintype.card α :=
    ⟨6 * Fintype.card α - 9 * j - 16, by omega⟩
  have h' : IsPathWord (j + 1) (3 * j + 6 + r) T := h.mono (by omega)
  have W := twelve_windows h' (by omega)
  have g1 := h'.gt (s := 0) (w := 2 * j + 3) (by omega) (by omega) (by omega)
  have g2 := h'.gt (s := 0) (w := 3 * j + 4) (by omega) (by omega) (by omega)
  have g3 := h'.gt (s := 0) (w := 3 * j + 5 + r) (by omega) (by omega) (by omega)
  have g4 := h'.gt (s := j + 1) (w := 2 * j + 3) (by omega) (by omega) (by omega)
  have g5 := h'.gt (s := j + 1) (w := 2 * j + 4 + r) (by omega) (by omega) (by omega)
  have g6 := h'.gt (s := 2 * j + 3) (w := j + 3 + r) (by omega) (by omega) (by omega)
  have g7 := h'.gt (s := j + 2) (w := 2 * j + 4 + r) (by omega) (by omega) (by omega)
  have g8 := h'.gt (s := 1) (w := 3 * j + 5 + r) (by omega) (by omega) (by omega)
  have g9 := h'.gt (s := j + 2) (w := 2 * j + 3) (by omega) (by omega) (by omega)
  have g10 := h'.gt (s := 1) (w := 3 * j + 4) (by omega) (by omega) (by omega)
  have g11 := h'.gt (s := 1) (w := 2 * j + 1) (by omega) (by omega) (by omega)
  have g12 := h'.gt (s := 2 * j + 2) (w := j + 3 + r) (by omega) (by omega) (by omega)
  omega

/-! ## Vertex version -/

/-- `v 0, …, v L` is a spread-`k` path with `L` edges in the cube `α → Bool`
(`v` is a walk on `ℕ`; only its first `L+1` vertices are constrained by the spread condition). -/
structure IsPath (k L : ℕ) (v : ℕ → α → Bool) : Prop where
  adj : ∀ i, hd (v i) (v (i + 1)) = 1
  spread : ∀ i w, i + w ≤ L → hd (v i) (v (i + w)) < k → hd (v i) (v (i + w)) = w

theorem IsPath.exists_word {v : ℕ → α → Bool} (h : IsPath k L v) :
    ∃ T : ℕ → α, IsPathWord k L T ∧ ∀ t w, hd (v t) (v (t + w)) = oddc T t w := by
  have hex : ∀ i, ∃ a, ∀ c, v i c ≠ v (i + 1) c ↔ c = a := by
    intro i
    have h1 := h.adj i
    unfold hd at h1
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
    refine ⟨a, fun c => ?_⟩
    simpa using Finset.ext_iff.mp ha c
  choose T hT using hex
  have hdo : ∀ t w, hd (v t) (v (t + w)) = oddc T t w := by
    intro t w
    rw [hd, oddc]
    exact congrArg card (filter_congr fun c _ => walk_parity hT t w c)
  refine ⟨T, ⟨?_⟩, hdo⟩
  intro s w hs hw
  rw [← hdo] at hw ⊢
  exact h.spread s w hs hw

/-- **Path bound.** A spread-`k` path with `L` edges in the `d`-cube, `l = 2d - 3k - 1`:
if `l ≥ 2` then `L ≤ 3k + 3l - 2 = 6(d-k) - 5` whenever `k ≥ 3l - 5` (`k` odd) resp. `k ≥ 3l - 3` (`k` even). -/
theorem path_length_bound {v : ℕ → α → Bool} (h : IsPath k L v) (hk : 1 ≤ k) (l : ℕ)
    (hd' : 2 * Fintype.card α = 3 * k + l + 1)
    (hl : 2 ≤ l) (hyp : if Even k then 3 * l ≤ k + 3 else 3 * l ≤ k + 5) :
    L + 2 ≤ 3 * k + 3 * l := by
  obtain ⟨T, hT, _⟩ := h.exists_word
  by_cases hE : Even k
  · simp only [hE, ite_true] at hyp
    have := path_bound_even hT hE hk (by omega) (by omega)
    omega
  · simp only [hE, ite_false] at hyp
    have hk2 : k % 2 = 1 := Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hE)
    have := path_bound_odd hT (Nat.not_even_iff_odd.mp hE) (by omega) (by omega)
    omega

end Coil

#print axioms Coil.path_length_bound
#print axioms Coil.four_piece
