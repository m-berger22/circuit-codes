import Ccformal.SymRun

/-!
# `S(n, k, a) ≤ 2a + 2k` whenever `2n ≤ a + 2k + 1`  (S174): Byrnes' bound for ALL `k ≥ l - 1`, in three steps

A symmetric spread-`k` code of length `N = 2H` in `Q_n` with a bit run of length `a`, where `2n ≤ a + 2k + 1`,
has `H ≤ a + k`.  With `a = k + l`, `2n = 3k + l + 1`:  `S(n, k, k+l) ≤ 4k + 2l` for every `k ≥ 1`, `l ≥ 1`
(no hypothesis relating `k` and `l`; no Lemma 2 / Lemma 3 / alternation lemma).

Proof.  Let the run be `[0, a)`, `f p = oddc T 0 p` (= distance from vertex `0` to vertex `p`).
* (`oddc_two_centres`) a coordinate of the run is odd in exactly one of `[0, p)`, `[a, p)`; the other coordinates in
  at most both:  `oddc [0,p) + oddc [a,p) ≤ 2n - a ≤ 2k + 1`.
* (`shell`) for `a + k ≤ p ≤ N - k` both distances are `≥ k`, so `k ≤ f p ≤ k + 1`.
* If `H ≥ a + k + 1`, the points `p = H-1, H, H+1, H+2` are in that range, so `f` alternates there.
  `f H = k+1`: `T H = T 0` is odd in `[0, H)` and `f (H-1) = k`; `T (H-1) ≠ T 0`, so `[1, H-1)` has `k - 1` odd coordinates.
  `f H = k`: `T 0` is even in `[0, H)`, `f (H+2) = k`, `T (H+1) = T 1 ≠ T 0`, so `T 0` is odd in `[0, H+2)` and
  `[1, H+2)` has `k - 1` odd coordinates.  Both contradict the spread.
-/

open Finset

namespace Coil

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.deprecated false

variable {α : Type*} [Fintype α] [DecidableEq α] {k N : ℕ} {T : ℕ → α}

/-- distances from the two ends of a bit run of length `a` add up to at most `2n - a` -/
lemma oddc_two_centres (T : ℕ → α) (a p : ℕ) (hrun : ∀ c, cnt T 0 a c ≤ 1) :
    oddc T 0 (a + p) + oddc T a p + a ≤ 2 * Fintype.card α := by
  have key : ∀ c ∈ (univ : Finset α),
      ((if Odd (cnt T 0 (a + p) c) then 1 else 0) + (if Odd (cnt T a p c) then 1 else 0)) + cnt T 0 a c ≤ 2 := by
    intro c _
    have h1 := hrun c
    have h2 := cnt_add T 0 a p c
    rw [zero_add] at h2
    simp only [Nat.odd_iff]
    split_ifs <;> omega
  have h := sum_le_sum key
  rw [sum_add_distrib, sum_add_distrib, ← oddc_eq_sum, ← oddc_eq_sum, sum_cnt] at h
  simp only [sum_const, card_univ, smul_eq_mul] at h
  omega

section

variable {a H : ℕ} (h : IsCoilWord k N T) (hk : 1 ≤ k) (ha : 2 ≤ a)
  (hn : 2 * Fintype.card α ≤ a + 2 * k + 1)
  (run : ∀ i j, i < a → j < a → T i = T j → i = j)

include run in
lemma cnt_run_le_one (c : α) : cnt T 0 a c ≤ 1 := by
  rw [cnt, card_le_one]
  intro i hi j hj
  simp only [mem_filter, mem_range, zero_add] at hi hj
  exact run i j hi.1 hj.1 (by rw [hi.2, hj.2])

include h hk hn run in
/-- far from both ends of the run the code stays at distance `k` or `k+1` from its start -/
lemma shell {p : ℕ} (hp1 : a + k ≤ p) (hp2 : p + k ≤ N) : k ≤ oddc T 0 p ∧ oddc T 0 p ≤ k + 1 := by
  have h1 := f1 h hk (t := 0) (L := p) (by omega) hp2
  have h2 := f1 h hk (t := a) (L := p - a) (by omega) (by omega)
  have h3 := oddc_two_centres T a (p - a) (cnt_run_le_one run)
  rw [show a + (p - a) = p by omega] at h3
  omega

include h hk ha hn run in
theorem symRun_all_aux (hNH : N = 2 * H) (sym : ∀ i, T (i + H) = T i) : H ≤ a + k := by
  by_contra hcon
  have hH : a + k + 1 ≤ H := by omega
  have hN2 : 2 * k + 2 ≤ N := by omega
  have sym0 : T H = T 0 := by have := sym 0; rwa [zero_add] at this
  have sym1 : T (H + 1) = T 1 := by have := sym 1; rwa [Nat.add_comm 1 H] at this
  have h01 : T 1 ≠ T 0 := fun e => by have := run 1 0 (by omega) (by omega) e; omega
  -- T (H-1) ≠ T 0
  have hm1 : T (H - 1) ≠ T 0 := by
    intro e
    have c1 := cnt_short h hk hN2 (t := H - 1) (L := 2) (by omega) (T 0)
    have c2 := cnt_add T (H - 1) 1 1 (T 0)
    rw [cnt_one, cnt_one, show H - 1 + 1 = H by omega, sym0, e] at c2
    simp at c2
    omega
  have s0 := shell h hk hn run (p := H - 1) (by omega) (by omega)
  have s1 := shell h hk hn run (p := H) (by omega) (by omega)
  have s2 := shell h hk hn run (p := H + 1) (by omega) (by omega)
  have s3 := shell h hk hn run (p := H + 2) (by omega) (by omega)
  have e1 := oddc_succ T 0 (H - 1)
  have e2 := oddc_succ T 0 H
  have e3 := oddc_succ T 0 (H + 1)
  rw [show H - 1 + 1 = H by omega] at e1
  simp only [zero_add] at e1 e2 e3
  rw [sym0] at e2
  rw [sym1] at e3
  by_cases hc : oddc T 0 H = k + 1
  · -- f H = k+1
    have o0 : Odd (cnt T 0 H (T 0)) := by
      by_contra hno
      rw [if_neg hno] at e2
      omega
    have f0 : oddc T 0 (H - 1) = k := by
      split_ifs at e1 <;> omega
    -- count of T 0 in [1, H-1)
    have d1 := cnt_add T 0 1 (H - 1) (T 0)
    have d2 := cnt_add T 1 (H - 2) 1 (T 0)
    rw [show 1 + (H - 1) = H by omega, cnt_one, zero_add] at d1
    rw [show H - 2 + 1 = H - 1 by omega, show 1 + (H - 2) = H - 1 by omega, cnt_one, if_neg hm1] at d2
    simp only [if_true] at d1
    have ev : ¬ Odd (cnt T 1 (H - 2) (T 0)) := by
      rw [Nat.odd_iff] at o0 ⊢
      omega
    have g := oddc_cons T 0 (H - 2)
    rw [show H - 2 + 1 = H - 1 by omega, zero_add, if_neg ev] at g
    have := f1 h hk (t := 1) (L := H - 2) (by omega) (by omega)
    omega
  · -- f H = k
    have fH : oddc T 0 H = k := by omega
    have o0 : ¬ Odd (cnt T 0 H (T 0)) := by
      intro ho
      rw [if_pos ho] at e2
      omega
    rw [if_neg o0] at e2
    have f2 : oddc T 0 (H + 2) = k := by
      rw [show H + 1 + 1 = H + 2 by omega] at e3
      split_ifs at e3 <;> omega
    -- count of T 0 in [1, H+2)
    have d1 := cnt_add T 0 1 (H + 1) (T 0)
    have d2 := cnt_add T 0 H 2 (T 0)
    have d3 := cnt_add T H 1 1 (T 0)
    rw [show 1 + (H + 1) = H + 2 by omega, cnt_one, zero_add] at d1
    rw [zero_add] at d2
    rw [show (1 : ℕ) + 1 = 2 by rfl, cnt_one, cnt_one, sym0, sym1, if_neg h01] at d3
    simp only [if_true] at d1 d3
    have ev : ¬ Odd (cnt T 1 (H + 1) (T 0)) := by
      rw [Nat.odd_iff] at o0 ⊢
      omega
    have g := oddc_cons T 0 (H + 1)
    rw [show H + 1 + 1 = H + 2 by omega, zero_add, if_neg ev] at g
    have := f1 h hk (t := 1) (L := H + 1) (by omega) (by omega)
    omega

end

/-- **`S(n, k, a) ≤ 2a + 2k` whenever `2n ≤ a + 2k + 1`**: a symmetric spread-`k` circuit code in `Q_n` with a
bit run of length `a ≥ 2n - 2k - 1` has length at most `2a + 2k`. -/
theorem symRun_all {a : ℕ} (hS : SymRun k N a T) (hk : 1 ≤ k) (ha : 2 ≤ a)
    (hn : 2 * Fintype.card α ≤ a + 2 * k + 1) : N ≤ 2 * a + 2 * k := by
  obtain ⟨h, sym, t, run⟩ := hS
  obtain ⟨H, hH⟩ := even_length h
  have hNH : N = 2 * H := by omega
  have hH2 : N / 2 = H := by omega
  rw [hH2] at sym
  have := symRun_all_aux (T := fun i => T (i + t)) (h.shift t) hk ha hn (fun i j hi hj e => ?_) hNH
    (fun i => ?_)
  · omega
  · exact run i j hi hj (by rw [Nat.add_comm t i, Nat.add_comm t j]; exact e)
  · show T (i + H + t) = T (i + t)
    rw [add_right_comm, sym]

/-- **Byrnes' upper bound `S(n, k, k+l) ≤ 4k + 2l` for ALL `k ≥ 1`, `l ≥ 1`** (`2n = 3k + l + 1`): no hypothesis
relating `k` and `l` (Byrnes: `k ≥ 2l - 2` / `2l + 1`; `symRun_le2`: `k > 3l - 7`). -/
theorem symRun_le_all {l : ℕ} (hS : SymRun k N (k + l) T) (hk : 1 ≤ k) (hl : 1 ≤ l)
    (hn : 2 * Fintype.card α = 3 * k + l + 1) : N ≤ 4 * k + 2 * l := by
  have := symRun_all hS hk (by omega) (by omega)
  omega

end Coil

#print axioms Coil.symRun_all
#print axioms Coil.symRun_le_all
