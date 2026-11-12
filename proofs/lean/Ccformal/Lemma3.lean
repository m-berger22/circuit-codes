import Ccformal.SymRun

/-!
# Lemma 3: windows of six blocks (found by an LP over block patterns, lp5.py)

For a coordinate let `π ∈ {0,1}⁶` be its counts in six consecutive blocks of length `K = k+1`. Then
`|π| + #{windows of ≥ 2 consecutive blocks with odd count} ≤ 12`  (15 windows; equality e.g. for π = 111111).
Summing over the coordinates: `6K + Σ_w odd(w) ≤ 12 n`, and `odd(w) ≥ k` (`≥ k+1` when the parity of the length demands it):

      N ≥ 7k + 6   ⟹   21k + 12 + 9 (k mod 2) ≤ 12 n.

With `2n = 3k + l + 1`: a spread-`k` circuit code with `k ≥ 2l` (k even) or `k ≥ 2l - 3` (k odd) has `N ≤ 7k + 5`
(`length_le_seven`).  Lemma 2 (windows of four blocks) gives `N ≤ 5k + 3`, but only for `k > 3l - 3` / `3l - 7`.
-/

open Finset

namespace Coil

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {α : Type*} [Fintype α] [DecidableEq α] {k N : ℕ} {T : ℕ → α}

/-- the pattern inequality -/
lemma pattern6 (b1 b2 b3 b4 b5 b6 : ℕ) (h1 : b1 ≤ 1) (h2 : b2 ≤ 1) (h3 : b3 ≤ 1) (h4 : b4 ≤ 1) (h5 : b5 ≤ 1)
    (h6 : b6 ≤ 1) :
    (if (b1 + b2 + b3 + b4 + b5 + b6) % 2 = 1 then 1 else 0)
      + (if (b1 + b2 + b3 + b4 + b5) % 2 = 1 then 1 else 0)
      + (if (b2 + b3 + b4 + b5 + b6) % 2 = 1 then 1 else 0)
      + (if (b1 + b2 + b3 + b4) % 2 = 1 then 1 else 0)
      + (if (b2 + b3 + b4 + b5) % 2 = 1 then 1 else 0)
      + (if (b3 + b4 + b5 + b6) % 2 = 1 then 1 else 0)
      + (if (b1 + b2 + b3) % 2 = 1 then 1 else 0)
      + (if (b2 + b3 + b4) % 2 = 1 then 1 else 0)
      + (if (b3 + b4 + b5) % 2 = 1 then 1 else 0)
      + (if (b4 + b5 + b6) % 2 = 1 then 1 else 0)
      + (if (b1 + b2) % 2 = 1 then 1 else 0)
      + (if (b2 + b3) % 2 = 1 then 1 else 0)
      + (if (b3 + b4) % 2 = 1 then 1 else 0)
      + (if (b4 + b5) % 2 = 1 then 1 else 0)
      + (if (b5 + b6) % 2 = 1 then 1 else 0)
      + (b1 + b2 + b3 + b4 + b5 + b6) ≤ 12 := by
  interval_cases b1 <;> interval_cases b2 <;> interval_cases b3 <;> interval_cases b4 <;> interval_cases b5 <;>
    interval_cases b6 <;> simp

set_option maxHeartbeats 2000000 in
/-- **Lemma 3** -/
theorem no_long6 (h : IsCoilWord k N T) (hk : 1 ≤ k) (hN7 : 7 * k + 6 ≤ N) :
    21 * k + 12 + 9 * (k % 2) ≤ 12 * Fintype.card α := by
  have hN : 2 * k + 2 ≤ N := by omega
  obtain ⟨K, hK⟩ : ∃ K, K = k + 1 := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : ℕ, t = 0 := ⟨_, rfl⟩
  have key : ∀ c,
      (if Odd (cnt T (t) (K + K + K + K + K + K) c) then 1 else 0)
      + (if Odd (cnt T (t) (K + K + K + K + K) c) then 1 else 0)
      + (if Odd (cnt T (t + K) (K + K + K + K + K) c) then 1 else 0)
      + (if Odd (cnt T (t) (K + K + K + K) c) then 1 else 0)
      + (if Odd (cnt T (t + K) (K + K + K + K) c) then 1 else 0)
      + (if Odd (cnt T (t + K + K) (K + K + K + K) c) then 1 else 0)
      + (if Odd (cnt T (t) (K + K + K) c) then 1 else 0)
      + (if Odd (cnt T (t + K) (K + K + K) c) then 1 else 0)
      + (if Odd (cnt T (t + K + K) (K + K + K) c) then 1 else 0)
      + (if Odd (cnt T (t + K + K + K) (K + K + K) c) then 1 else 0)
      + (if Odd (cnt T (t) (K + K) c) then 1 else 0)
      + (if Odd (cnt T (t + K) (K + K) c) then 1 else 0)
      + (if Odd (cnt T (t + K + K) (K + K) c) then 1 else 0)
      + (if Odd (cnt T (t + K + K + K) (K + K) c) then 1 else 0)
      + (if Odd (cnt T (t + K + K + K + K) (K + K) c) then 1 else 0)
      + cnt T t (K + K + K + K + K + K) c ≤ 12 := by
    intro c
    have h1 := cnt_short h hk hN (t := t) (L := K) (by omega) c
    have h2 := cnt_short h hk hN (t := t + K) (L := K) (by omega) c
    have h3 := cnt_short h hk hN (t := t + K + K) (L := K) (by omega) c
    have h4 := cnt_short h hk hN (t := t + K + K + K) (L := K) (by omega) c
    have h5 := cnt_short h hk hN (t := t + K + K + K + K) (L := K) (by omega) c
    have h6 := cnt_short h hk hN (t := t + K + K + K + K + K) (L := K) (by omega) c
    have := pattern6 _ _ _ _ _ _ h1 h2 h3 h4 h5 h6
    simp only [cnt_add, ← add_assoc, Nat.odd_iff]
    simp only [← add_assoc] at this
    exact this
  have S := sum_le_sum (s := univ) (fun c _ => key c)
  simp only [sum_add_distrib, ← oddc_eq_sum, sum_cnt, sum_const, card_univ, smul_eq_mul] at S
  have q0 : k + k % 2 ≤ oddc T (t) (K + K + K + K + K + K) := by
    have o := f1 h hk (t := t) (L := (K + K + K + K + K + K)) (by omega) (by omega)
    have p := oddc_parity T (t) (K + K + K + K + K + K)
    rw [Nat.odd_iff, Nat.odd_iff] at p
    omega
  have q1 : k + 1 ≤ oddc T (t) (K + K + K + K + K) := by
    have o := f1 h hk (t := t) (L := (K + K + K + K + K)) (by omega) (by omega)
    have p := oddc_parity T (t) (K + K + K + K + K)
    rw [Nat.odd_iff, Nat.odd_iff] at p
    omega
  have q2 : k + 1 ≤ oddc T (t + K) (K + K + K + K + K) := by
    have o := f1 h hk (t := t + K) (L := (K + K + K + K + K)) (by omega) (by omega)
    have p := oddc_parity T (t + K) (K + K + K + K + K)
    rw [Nat.odd_iff, Nat.odd_iff] at p
    omega
  have q3 : k + k % 2 ≤ oddc T (t) (K + K + K + K) := by
    have o := f1 h hk (t := t) (L := (K + K + K + K)) (by omega) (by omega)
    have p := oddc_parity T (t) (K + K + K + K)
    rw [Nat.odd_iff, Nat.odd_iff] at p
    omega
  have q4 : k + k % 2 ≤ oddc T (t + K) (K + K + K + K) := by
    have o := f1 h hk (t := t + K) (L := (K + K + K + K)) (by omega) (by omega)
    have p := oddc_parity T (t + K) (K + K + K + K)
    rw [Nat.odd_iff, Nat.odd_iff] at p
    omega
  have q5 : k + k % 2 ≤ oddc T (t + K + K) (K + K + K + K) := by
    have o := f1 h hk (t := t + K + K) (L := (K + K + K + K)) (by omega) (by omega)
    have p := oddc_parity T (t + K + K) (K + K + K + K)
    rw [Nat.odd_iff, Nat.odd_iff] at p
    omega
  have q6 : k + 1 ≤ oddc T (t) (K + K + K) := by
    have o := f1 h hk (t := t) (L := (K + K + K)) (by omega) (by omega)
    have p := oddc_parity T (t) (K + K + K)
    rw [Nat.odd_iff, Nat.odd_iff] at p
    omega
  have q7 : k + 1 ≤ oddc T (t + K) (K + K + K) := by
    have o := f1 h hk (t := t + K) (L := (K + K + K)) (by omega) (by omega)
    have p := oddc_parity T (t + K) (K + K + K)
    rw [Nat.odd_iff, Nat.odd_iff] at p
    omega
  have q8 : k + 1 ≤ oddc T (t + K + K) (K + K + K) := by
    have o := f1 h hk (t := t + K + K) (L := (K + K + K)) (by omega) (by omega)
    have p := oddc_parity T (t + K + K) (K + K + K)
    rw [Nat.odd_iff, Nat.odd_iff] at p
    omega
  have q9 : k + 1 ≤ oddc T (t + K + K + K) (K + K + K) := by
    have o := f1 h hk (t := t + K + K + K) (L := (K + K + K)) (by omega) (by omega)
    have p := oddc_parity T (t + K + K + K) (K + K + K)
    rw [Nat.odd_iff, Nat.odd_iff] at p
    omega
  have q10 : k + k % 2 ≤ oddc T (t) (K + K) := by
    have o := f1 h hk (t := t) (L := (K + K)) (by omega) (by omega)
    have p := oddc_parity T (t) (K + K)
    rw [Nat.odd_iff, Nat.odd_iff] at p
    omega
  have q11 : k + k % 2 ≤ oddc T (t + K) (K + K) := by
    have o := f1 h hk (t := t + K) (L := (K + K)) (by omega) (by omega)
    have p := oddc_parity T (t + K) (K + K)
    rw [Nat.odd_iff, Nat.odd_iff] at p
    omega
  have q12 : k + k % 2 ≤ oddc T (t + K + K) (K + K) := by
    have o := f1 h hk (t := t + K + K) (L := (K + K)) (by omega) (by omega)
    have p := oddc_parity T (t + K + K) (K + K)
    rw [Nat.odd_iff, Nat.odd_iff] at p
    omega
  have q13 : k + k % 2 ≤ oddc T (t + K + K + K) (K + K) := by
    have o := f1 h hk (t := t + K + K + K) (L := (K + K)) (by omega) (by omega)
    have p := oddc_parity T (t + K + K + K) (K + K)
    rw [Nat.odd_iff, Nat.odd_iff] at p
    omega
  have q14 : k + k % 2 ≤ oddc T (t + K + K + K + K) (K + K) := by
    have o := f1 h hk (t := t + K + K + K + K) (L := (K + K)) (by omega) (by omega)
    have p := oddc_parity T (t + K + K + K + K) (K + K)
    rw [Nat.odd_iff, Nat.odd_iff] at p
    omega
  omega

/-- a spread-`k` circuit code with `k ≥ 2l` (`k` even) or `k ≥ 2l - 3` (`k` odd), `2n = 3k + l + 1`, has `N ≤ 7k + 5` -/
theorem length_le_seven (h : IsCoilWord k N T) (hk : 1 ≤ k) (l : ℕ) (hn : 2 * Fintype.card α = 3 * k + l + 1)
    (hkl : if Even k then 2 * l ≤ k else 2 * l ≤ k + 3) : N ≤ 7 * k + 5 := by
  by_contra hcon
  have := no_long6 h hk (by omega)
  rcases Nat.even_or_odd k with he | ho
  · rw [if_pos he] at hkl
    obtain ⟨r, hr⟩ := he
    omega
  · rw [if_neg (Nat.not_even_iff_odd.mpr ho)] at hkl
    obtain ⟨r, hr⟩ := ho
    omega

end Coil

#print axioms Coil.no_long6
#print axioms Coil.length_le_seven
