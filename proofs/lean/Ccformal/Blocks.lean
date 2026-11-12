import Ccformal.Lemma3

/-!
# The block lemma for ANY number of blocks (contains Lemma 2- and Lemma 3-type bounds)

Cut a window into `j` blocks of length `K = k+1` (`N ≥ jK + k`). For a coordinate let `v_0, …, v_j ∈ {0,1}` be the parities of
its counts in the first `0, 1, …, j` blocks. The window from boundary `a` to boundary `b` contains it an odd number of times iff
`v_a ≠ v_b`; so

      Σ_{a<b} δ(window a..b)  =  Σ_coordinates #{a < b : v_a ≠ v_b}  =  Σ_coordinates (#zeros)(#ones)  ≤  n ⌊(j+1)²/4⌋,

while `δ = K` for the `j` single blocks and `δ ≥ k` for the other `j(j-1)/2` windows.  Hence (`blocks_bound`)

      N ≥ j(k+1) + k   ⟹   j(k+1) + (j(j+1)/2 - j) k  ≤  ⌊(j+1)/2⌋ ⌊(j+2)/2⌋ n        for every j ≥ 2.

With `j = 2s`, `2n = 3k+l+1`:  `(s-1) k + 4 ≤ (s+1)(l+1)`; so for `(s-1) k + 4 > (s+1)(l+1)` every code has
`N ≤ (2s+1)k + 2s - 1` (`length_le_blocks`): an explicit upper bound for `K(n,k)` whenever `k ≥ l + 2`, i.e. `n ≤ 2k - 1`.
(`s = 2`: `k > 3l-1`, `N ≤ 5k+3`, cf. Lemma 2;  `s = 3`: `k > 2l`, `N ≤ 7k+5`, cf. Lemma 3 -- those two have slightly better
constants because they also use the parity of `δ`.)
-/

open Finset

namespace Coil

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.deprecated false

/-- pairs `a < b < n` on which a predicate takes different values: `(#true)(#false)` of them -/
lemma pairs_eq (q : ℕ → Prop) [DecidablePred q] (n : ℕ) :
    ∑ b ∈ range n, ∑ a ∈ range b, (if (q a ↔ q b) then 0 else 1)
      = (∑ a ∈ range n, if q a then 1 else 0) * (∑ a ∈ range n, if q a then 0 else 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, sum_range_succ, sum_range_succ]
    by_cases hq : q n
    · have e : ∑ a ∈ range n, (if (q a ↔ q n) then 0 else 1) = ∑ a ∈ range n, if q a then 0 else 1 := by
        apply sum_congr rfl
        intro a _
        simp [hq]
      rw [e, if_pos hq, if_pos hq]
      ring
    · have e : ∑ a ∈ range n, (if (q a ↔ q n) then 0 else 1) = ∑ a ∈ range n, if q a then 1 else 0 := by
        apply sum_congr rfl
        intro a _
        by_cases ha : q a <;> simp [hq, ha]
      rw [e, if_neg hq, if_neg hq]
      ring

lemma zo_le (z o : ℕ) : z * o ≤ ((z + o) / 2) * ((z + o + 1) / 2) := by
  rcases Nat.even_or_odd' (z + o) with ⟨s, hs | hs⟩
  · rw [hs, show 2 * s / 2 = s by omega, show (2 * s + 1) / 2 = s by omega]
    have h1 : (z : ℤ) + o = 2 * s := by exact_mod_cast hs
    have : (z : ℤ) * o ≤ s * s := by nlinarith [sq_nonneg ((z : ℤ) - o)]
    exact_mod_cast this
  · rw [hs, show (2 * s + 1) / 2 = s by omega, show (2 * s + 1 + 1) / 2 = s + 1 by omega]
    have h1 : (z : ℤ) + o = 2 * s + 1 := by exact_mod_cast hs
    have h2 : (z : ℤ) - o ≤ -1 ∨ 1 ≤ (z : ℤ) - o := by omega
    have : (z : ℤ) * o ≤ s * (s + 1) := by
      rcases h2 with h2 | h2 <;> nlinarith
    exact_mod_cast this

lemma pairs_le (q : ℕ → Prop) [DecidablePred q] (n : ℕ) :
    ∑ b ∈ range n, ∑ a ∈ range b, (if (q a ↔ q b) then 0 else 1) ≤ (n / 2) * ((n + 1) / 2) := by
  rw [pairs_eq]
  have h1 : (∑ a ∈ range n, if q a then 1 else 0) + (∑ a ∈ range n, if q a then 0 else 1) = n := by
    rw [← sum_add_distrib]
    have : ∀ a ∈ range n, ((if q a then 1 else 0) + if q a then 0 else 1) = 1 := by
      intro a _; split_ifs <;> rfl
    rw [sum_congr rfl this]
    simp
  have := zo_le (∑ a ∈ range n, if q a then 1 else 0) (∑ a ∈ range n, if q a then 0 else 1)
  rw [h1] at this
  exact this

variable {α : Type*} [Fintype α] [DecidableEq α] {k N : ℕ} {T : ℕ → α}

/-- **The block lemma.** -/
theorem blocks_bound (h : IsCoilWord k N T) (hk : 1 ≤ k) (j : ℕ) (hN : j * (k + 1) + k ≤ N) :
    j * (k + 1) + (j * (j + 1) / 2 - j) * k ≤ ((j + 1) / 2) * ((j + 2) / 2) * Fintype.card α := by
  have hN2 : 2 * k + 2 ≤ N ∨ j ≤ 1 := by
    by_cases hj : j ≤ 1
    · right; exact hj
    · left
      have : 2 * (k + 1) ≤ j * (k + 1) := Nat.mul_le_mul_right _ (by omega)
      omega
  obtain ⟨K, hK⟩ : ∃ K, K = k + 1 := ⟨_, rfl⟩
  rw [← hK] at hN ⊢
  -- the sum of the odd counts over all windows between two block boundaries
  have hA : ∀ b ∈ range (j + 1), ∀ a ∈ range b,
      oddc T (a * K) ((b - a) * K) = ∑ c : α, (if (Odd (cnt T 0 (a * K) c) ↔ Odd (cnt T 0 (b * K) c)) then 0 else 1) := by
    intro b hb a ha
    rw [mem_range] at ha hb
    rw [oddc_eq_sum]
    apply sum_congr rfl
    intro c _
    have e : cnt T 0 (b * K) c = cnt T 0 (a * K) c + cnt T (a * K) ((b - a) * K) c := by
      rw [show b * K = a * K + (b - a) * K by rw [← add_mul]; congr 1; omega, cnt_add, zero_add]
    rw [e]
    simp only [Nat.odd_iff]
    split_ifs <;> omega
  -- lower bound
  have hB : ∀ b ∈ range (j + 1), ∀ a ∈ range b,
      k + (if a + 1 = b then 1 else 0) ≤ oddc T (a * K) ((b - a) * K) := by
    intro b hb a ha
    rw [mem_range] at ha hb
    have hbK : b * K ≤ j * K := Nat.mul_le_mul_right _ (by omega)
    have hsplit : b * K = a * K + (b - a) * K := by rw [← add_mul]; congr 1; omega
    by_cases hadj : a + 1 = b
    · rw [if_pos hadj, show b - a = 1 by omega, one_mul]
      have hj1 : ¬ j ≤ 1 ∨ j = 1 := by omega
      have hN2' : 2 * k + 2 ≤ N := by
        rcases hN2 with h2 | h2
        · exact h2
        · have : j = 1 := by omega
          subst this
          -- one block: N ≥ K + k = 2k+1, and N is even
          obtain ⟨m, hm⟩ := even_length h
          omega
      rw [oddc_short h hk hN2' (by omega)]
      omega
    · rw [if_neg hadj, add_zero]
      have h2 : 2 * K ≤ (b - a) * K := Nat.mul_le_mul_right _ (by omega)
      exact f1 h hk (by omega) (by omega)
  have hlow : ∑ b ∈ range (j + 1), ∑ a ∈ range b, (k + (if a + 1 = b then 1 else 0))
      ≤ ∑ b ∈ range (j + 1), ∑ a ∈ range b, oddc T (a * K) ((b - a) * K) :=
    sum_le_sum (fun b hb => sum_le_sum (fun a ha => hB b hb a ha))
  -- evaluate the lower bound
  have hinner : ∀ b, b * k + (if 1 ≤ b then 1 else 0) ≤ ∑ a ∈ range b, (k + (if a + 1 = b then 1 else 0)) := by
    intro b
    rcases b with _ | b'
    · simp
    · rw [sum_range_succ, if_pos rfl]
      have : ∑ a ∈ range b', k ≤ ∑ a ∈ range b', (k + (if a + 1 = b' + 1 then 1 else 0)) :=
        sum_le_sum (fun a _ => Nat.le_add_right _ _)
      rw [sum_const, card_range, smul_eq_mul] at this
      rw [if_pos (by omega)]
      have e : (b' + 1) * k = b' * k + k := by ring
      omega
  have hlow2 : ∑ b ∈ range (j + 1), (b * k + (if 1 ≤ b then 1 else 0))
      ≤ ∑ b ∈ range (j + 1), ∑ a ∈ range b, (k + (if a + 1 = b then 1 else 0)) :=
    sum_le_sum (fun b _ => hinner b)
  have hG : ∑ b ∈ range (j + 1), (b * k + (if 1 ≤ b then 1 else 0)) = (j * (j + 1) / 2) * k + j := by
    rw [sum_add_distrib, ← sum_mul, Finset.sum_range_id, show j + 1 - 1 = j by omega,
      show (j + 1) * j = j * (j + 1) by ring]
    congr 1
    rw [sum_range_succ', if_neg (by omega), add_zero]
    have : ∀ i ∈ range j, (if 1 ≤ i + 1 then 1 else 0) = 1 := fun i _ => by rw [if_pos (by omega)]
    rw [sum_congr rfl this]
    simp
  -- upper bound
  have hup : ∑ b ∈ range (j + 1), ∑ a ∈ range b, oddc T (a * K) ((b - a) * K)
      ≤ ((j + 1) / 2) * ((j + 2) / 2) * Fintype.card α := by
    have e1 : ∑ b ∈ range (j + 1), ∑ a ∈ range b, oddc T (a * K) ((b - a) * K)
        = ∑ b ∈ range (j + 1), ∑ a ∈ range b, ∑ c : α,
            (if (Odd (cnt T 0 (a * K) c) ↔ Odd (cnt T 0 (b * K) c)) then 0 else 1) :=
      sum_congr rfl (fun b hb => sum_congr rfl (fun a ha => hA b hb a ha))
    have e2 : ∑ b ∈ range (j + 1), ∑ a ∈ range b, ∑ c : α,
          (if (Odd (cnt T 0 (a * K) c) ↔ Odd (cnt T 0 (b * K) c)) then 0 else 1)
        = ∑ c : α, ∑ b ∈ range (j + 1), ∑ a ∈ range b,
            (if (Odd (cnt T 0 (a * K) c) ↔ Odd (cnt T 0 (b * K) c)) then 0 else 1) := by
      have e2a : ∀ b ∈ range (j + 1), ∑ a ∈ range b, ∑ c : α,
            (if (Odd (cnt T 0 (a * K) c) ↔ Odd (cnt T 0 (b * K) c)) then 0 else 1)
          = ∑ c : α, ∑ a ∈ range b, (if (Odd (cnt T 0 (a * K) c) ↔ Odd (cnt T 0 (b * K) c)) then 0 else 1) :=
        fun b _ => sum_comm
      rw [sum_congr rfl e2a, sum_comm]
    rw [e1, e2]
    have e3 : ∀ c ∈ (univ : Finset α), ∑ b ∈ range (j + 1), ∑ a ∈ range b,
          (if (Odd (cnt T 0 (a * K) c) ↔ Odd (cnt T 0 (b * K) c)) then 0 else 1)
        ≤ ((j + 1) / 2) * ((j + 2) / 2) := by
      intro c _
      exact pairs_le (fun a => Odd (cnt T 0 (a * K) c)) (j + 1)
    have := sum_le_sum e3
    rw [sum_const, card_univ, smul_eq_mul, mul_comm] at this
    exact this
  have e4 : j * (j + 1) / 2 - j + j = j * (j + 1) / 2 := by
    have : 2 * j ≤ j * (j + 1) ∨ j = 0 := by
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · right; exact h0
      · left; nlinarith
    rcases this with h2 | h2
    · omega
    · subst h2; simp
  have e5 : (j * (j + 1) / 2 - j + j) * k = (j * (j + 1) / 2 - j) * k + j * k := by ring
  have e6 : j * K = j * k + j := by rw [hK]; ring
  rw [e4] at e5
  omega

/-- with `j = 2s` blocks: every code with `(s-1) k + 4 > (s+1)(l+1)` has `N ≤ (2s+1) k + 2s - 1` -/
theorem length_le_blocks (h : IsCoilWord k N T) (hk : 1 ≤ k) (s l : ℕ) (hs : 1 ≤ s)
    (hn : 2 * Fintype.card α = 3 * k + l + 1) (hkl : (s + 1) * (l + 1) < (s - 1) * k + 4) :
    N ≤ (2 * s + 1) * k + 2 * s - 1 := by
  by_contra hcon
  have hb := blocks_bound h hk (2 * s) (by
    have : 2 * s * (k + 1) + k = (2 * s + 1) * k + 2 * s := by ring
    omega)
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  rw [show (2 * (s' + 1) + 1) / 2 = s' + 1 by omega, show (2 * (s' + 1) + 2) / 2 = s' + 2 by omega,
    show 2 * (s' + 1) * (2 * (s' + 1) + 1) / 2 = (s' + 1) * (2 * s' + 3) by
      rw [show 2 * (s' + 1) * (2 * (s' + 1) + 1) = 2 * ((s' + 1) * (2 * s' + 3)) by ring, Nat.mul_div_cancel_left _ (by norm_num)]] at hb
  rw [show s' + 1 - 1 = s' by omega] at hkl
  -- 2(s'+1)(k+1) + ((s'+1)(2s'+3) - 2(s'+1)) k ≤ (s'+1)(s'+2) n
  have e1 : (s' + 1) * (2 * s' + 3) - 2 * (s' + 1) = (s' + 1) * (2 * s' + 1) := by
    have : (s' + 1) * (2 * s' + 3) = (s' + 1) * (2 * s' + 1) + 2 * (s' + 1) := by ring
    omega
  rw [e1] at hb
  have hbZ : (2 * ((s' : ℤ) + 1) * (k + 1) + (s' + 1) * (2 * s' + 1) * k) * 2
      ≤ (s' + 1) * (s' + 2) * (3 * k + l + 1) := by
    have h1 : ((2 * (s' + 1) * (k + 1) + (s' + 1) * (2 * s' + 1) * k : ℕ) : ℤ)
        ≤ (((s' + 1) * (s' + 2) * Fintype.card α : ℕ) : ℤ) := by exact_mod_cast hb
    have h2 : (2 : ℤ) * Fintype.card α = 3 * k + l + 1 := by exact_mod_cast hn
    push_cast at h1
    nlinarith
  have hklZ : ((s' : ℤ) + 1 + 1) * (l + 1) < s' * k + 4 := by exact_mod_cast hkl
  have hs0 : (0 : ℤ) ≤ s' := by positivity
  nlinarith

/-- the counting half of the block lemma, for any word and any block length -/
lemma windows_sum_le (T : ℕ → α) (K j : ℕ) :
    ∑ b ∈ range (j + 1), ∑ a ∈ range b, oddc T (a * K) ((b - a) * K)
      ≤ ((j + 1) / 2) * ((j + 2) / 2) * Fintype.card α := by
  have hA : ∀ b ∈ range (j + 1), ∀ a ∈ range b,
      oddc T (a * K) ((b - a) * K) = ∑ c : α, (if (Odd (cnt T 0 (a * K) c) ↔ Odd (cnt T 0 (b * K) c)) then 0 else 1) := by
    intro b hb a ha
    rw [mem_range] at ha hb
    rw [oddc_eq_sum]
    apply sum_congr rfl
    intro c _
    have e : cnt T 0 (b * K) c = cnt T 0 (a * K) c + cnt T (a * K) ((b - a) * K) c := by
      rw [show b * K = a * K + (b - a) * K by rw [← add_mul]; congr 1; omega, cnt_add, zero_add]
    rw [e]
    simp only [Nat.odd_iff]
    split_ifs <;> omega
  have e1 : ∑ b ∈ range (j + 1), ∑ a ∈ range b, oddc T (a * K) ((b - a) * K)
      = ∑ b ∈ range (j + 1), ∑ a ∈ range b, ∑ c : α,
          (if (Odd (cnt T 0 (a * K) c) ↔ Odd (cnt T 0 (b * K) c)) then 0 else 1) :=
    sum_congr rfl (fun b hb => sum_congr rfl (fun a ha => hA b hb a ha))
  have e2a : ∀ b ∈ range (j + 1), ∑ a ∈ range b, ∑ c : α,
        (if (Odd (cnt T 0 (a * K) c) ↔ Odd (cnt T 0 (b * K) c)) then 0 else 1)
      = ∑ c : α, ∑ a ∈ range b, (if (Odd (cnt T 0 (a * K) c) ↔ Odd (cnt T 0 (b * K) c)) then 0 else 1) :=
    fun b _ => sum_comm
  rw [e1, sum_congr rfl e2a, sum_comm]
  have e3 : ∀ c ∈ (univ : Finset α), ∑ b ∈ range (j + 1), ∑ a ∈ range b,
        (if (Odd (cnt T 0 (a * K) c) ↔ Odd (cnt T 0 (b * K) c)) then 0 else 1)
      ≤ ((j + 1) / 2) * ((j + 2) / 2) := by
    intro c _
    exact pairs_le (fun a => Odd (cnt T 0 (a * K) c)) (j + 1)
  have := sum_le_sum e3
  rw [sum_const, card_univ, smul_eq_mul, mul_comm] at this
  exact this

/-- **The block lemma for odd `k`** (every window has `δ ≥ k+1`):
`N ≥ j(k+1) + k  ⟹  (j(j+1)/2)(k+1) ≤ ⌊(j+1)/2⌋⌊(j+2)/2⌋ n`.
(`j = 4`: `k ≤ 3l - 7`, exactly Lemma 2;  `j = 6`: `k ≤ 2l - 5`, exactly Lemma 3.) -/
theorem blocks_bound_odd (h : IsCoilWord k N T) (hko : Odd k) (j : ℕ) (hj : 2 ≤ j) (hN : j * (k + 1) + k ≤ N) :
    (j * (j + 1) / 2) * (k + 1) ≤ ((j + 1) / 2) * ((j + 2) / 2) * Fintype.card α := by
  obtain ⟨r, hr⟩ := hko
  have hk : 1 ≤ k := by omega
  have hN2 : 2 * k + 2 ≤ N := by
    have : 2 * (k + 1) ≤ j * (k + 1) := Nat.mul_le_mul_right _ hj
    omega
  have hup := windows_sum_le T (k + 1) j
  have hB : ∀ b ∈ range (j + 1), ∀ a ∈ range b, k + 1 ≤ oddc T (a * (k + 1)) ((b - a) * (k + 1)) := by
    intro b hb a ha
    rw [mem_range] at ha hb
    have hbK : b * (k + 1) ≤ j * (k + 1) := Nat.mul_le_mul_right _ (by omega)
    have hsplit : b * (k + 1) = a * (k + 1) + (b - a) * (k + 1) := by rw [← add_mul]; congr 1; omega
    by_cases hadj : a + 1 = b
    · rw [show b - a = 1 by omega, one_mul, oddc_short h hk hN2 le_rfl]
    · have h2 : 2 * (k + 1) ≤ (b - a) * (k + 1) := Nat.mul_le_mul_right _ (by omega)
      have hf := f1 h hk (t := a * (k + 1)) (L := (b - a) * (k + 1)) (by omega) (by omega)
      have hp := oddc_parity T (a * (k + 1)) ((b - a) * (k + 1))
      have hev : ((b - a) * (k + 1)) % 2 = 0 := by
        rw [show k + 1 = 2 * (r + 1) by omega, show (b - a) * (2 * (r + 1)) = 2 * ((b - a) * (r + 1)) by ring]
        exact Nat.mul_mod_right 2 _
      rw [Nat.odd_iff, Nat.odd_iff] at hp
      omega
  have hlow : ∑ b ∈ range (j + 1), ∑ a ∈ range b, (k + 1)
      ≤ ∑ b ∈ range (j + 1), ∑ a ∈ range b, oddc T (a * (k + 1)) ((b - a) * (k + 1)) :=
    sum_le_sum (fun b hb => sum_le_sum (fun a ha => hB b hb a ha))
  have hG : ∑ b ∈ range (j + 1), ∑ a ∈ range b, (k + 1) = (j * (j + 1) / 2) * (k + 1) := by
    have : ∀ b ∈ range (j + 1), ∑ a ∈ range b, (k + 1) = b * (k + 1) := by
      intro b _
      rw [sum_const, card_range, smul_eq_mul]
    rw [sum_congr rfl this, ← sum_mul, Finset.sum_range_id, show j + 1 - 1 = j by omega,
      show (j + 1) * j = j * (j + 1) by ring]
  omega

/-- number of windows of an odd number `≥ 3` of blocks: `2` for `j = 4`, `6` for `j = 6` -/
def oddWindows (j : ℕ) : ℕ :=
  ∑ b ∈ range (j + 1), ∑ a ∈ range b, (if (b - a) % 2 = 1 ∧ a + 1 ≠ b then 1 else 0)

example : oddWindows 4 = 2 := by decide
example : oddWindows 6 = 6 := by decide

/-- **The block lemma for even `k`** (windows of an odd number of blocks have odd length, so `δ ≥ k+1` there):
`N ≥ j(k+1) + k  ⟹  j(k+1) + (j(j+1)/2 - j) k + oddWindows j ≤ ⌊(j+1)/2⌋⌊(j+2)/2⌋ n`.
(`j = 4`: `k ≤ 3l - 3`, exactly Lemma 2;  `j = 6`: `k ≤ 2l - 2`, exactly Lemma 3.) -/
theorem blocks_bound_even (h : IsCoilWord k N T) (hk : 1 ≤ k) (hke : Even k) (j : ℕ) (hj : 2 ≤ j)
    (hN : j * (k + 1) + k ≤ N) :
    j * (k + 1) + (j * (j + 1) / 2 - j) * k + oddWindows j
      ≤ ((j + 1) / 2) * ((j + 2) / 2) * Fintype.card α := by
  obtain ⟨r, hr⟩ := hke
  have hN2 : 2 * k + 2 ≤ N := by
    have : 2 * (k + 1) ≤ j * (k + 1) := Nat.mul_le_mul_right _ hj
    omega
  have hup := windows_sum_le T (k + 1) j
  have hB : ∀ b ∈ range (j + 1), ∀ a ∈ range b,
      k + (if a + 1 = b then 1 else 0) + (if (b - a) % 2 = 1 ∧ a + 1 ≠ b then 1 else 0)
        ≤ oddc T (a * (k + 1)) ((b - a) * (k + 1)) := by
    intro b hb a ha
    rw [mem_range] at ha hb
    have hbK : b * (k + 1) ≤ j * (k + 1) := Nat.mul_le_mul_right _ (by omega)
    have hsplit : b * (k + 1) = a * (k + 1) + (b - a) * (k + 1) := by rw [← add_mul]; congr 1; omega
    by_cases hadj : a + 1 = b
    · rw [if_pos hadj, if_neg (by tauto), show b - a = 1 by omega, one_mul, oddc_short h hk hN2 le_rfl]
    · rw [if_neg hadj, add_zero]
      have h2 : 2 * (k + 1) ≤ (b - a) * (k + 1) := Nat.mul_le_mul_right _ (by omega)
      have hf := f1 h hk (t := a * (k + 1)) (L := (b - a) * (k + 1)) (by omega) (by omega)
      by_cases hodd : (b - a) % 2 = 1
      · rw [if_pos ⟨hodd, hadj⟩]
        have hp := oddc_parity T (a * (k + 1)) ((b - a) * (k + 1))
        have hL : ((b - a) * (k + 1)) % 2 = 1 := by
          rw [Nat.mul_mod, hodd, show (k + 1) % 2 = 1 by omega]
        rw [Nat.odd_iff, Nat.odd_iff] at hp
        omega
      · rw [if_neg (by tauto)]
        omega
  have hlow := sum_le_sum (fun b hb => sum_le_sum (fun a ha => hB b hb a ha))
    (s := range (j + 1))
  simp only [sum_add_distrib] at hlow
  have hinner : ∀ b, b * k + (if 1 ≤ b then 1 else 0) ≤ ∑ a ∈ range b, (k + (if a + 1 = b then 1 else 0)) := by
    intro b
    rcases b with _ | b'
    · simp
    · rw [sum_range_succ, if_pos rfl]
      have : ∑ a ∈ range b', k ≤ ∑ a ∈ range b', (k + (if a + 1 = b' + 1 then 1 else 0)) :=
        sum_le_sum (fun a _ => Nat.le_add_right _ _)
      rw [sum_const, card_range, smul_eq_mul] at this
      rw [if_pos (by omega)]
      have e : (b' + 1) * k = b' * k + k := by ring
      omega
  have hlow2 : ∑ b ∈ range (j + 1), (b * k + (if 1 ≤ b then 1 else 0))
      ≤ ∑ b ∈ range (j + 1), ∑ a ∈ range b, (k + (if a + 1 = b then 1 else 0)) :=
    sum_le_sum (fun b _ => hinner b)
  simp only [sum_add_distrib] at hlow2
  have hG : ∑ b ∈ range (j + 1), (b * k + (if 1 ≤ b then 1 else 0)) = (j * (j + 1) / 2) * k + j := by
    rw [sum_add_distrib, ← sum_mul, Finset.sum_range_id, show j + 1 - 1 = j by omega,
      show (j + 1) * j = j * (j + 1) by ring]
    congr 1
    rw [sum_range_succ', if_neg (by omega), add_zero]
    have : ∀ i ∈ range j, (if 1 ≤ i + 1 then 1 else 0) = 1 := fun i _ => by rw [if_pos (by omega)]
    rw [sum_congr rfl this]
    simp
  rw [sum_add_distrib] at hG
  have e4 : j * (j + 1) / 2 - j + j = j * (j + 1) / 2 := by
    have : 2 * j ≤ j * (j + 1) := by nlinarith
    omega
  have e5 : (j * (j + 1) / 2 - j + j) * k = (j * (j + 1) / 2 - j) * k + j * k := by ring
  have e6 : j * (k + 1) = j * k + j := by ring
  rw [e4] at e5
  unfold oddWindows
  omega

end Coil

#print axioms Coil.blocks_bound
#print axioms Coil.length_le_blocks
#print axioms Coil.blocks_bound_odd
#print axioms Coil.blocks_bound_even
