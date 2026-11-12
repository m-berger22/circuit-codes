import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.BigOperators.Ring.Nat

/-!
# Circuit codes: transition words and the chord inequality (Lemma 1 of PROOF.md)

A spread-`k` circuit code of length `N` in the `n`-cube is described by its cyclic transition
word `T : ℕ → α` (`α` = the set of `n` coordinates, `T i` = coordinate flipped at step `i`,
extended `N`-periodically).  The Hamming distance between vertices `t` and `t + L` is the number
of coordinates occurring an odd number of times in the window `T t, …, T (t+L-1)` (`oddc`).
-/

open Finset

namespace Coil

set_option linter.unusedSectionVars false
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- number of occurrences of `c` among `T t, …, T (t+L-1)` -/
def cnt (T : ℕ → α) (t L : ℕ) (c : α) : ℕ := #{j ∈ range L | T (t + j) = c}

/-- number of coordinates occurring an odd number of times in the window = Hamming distance
between the vertices `t` and `t+L` -/
def oddc (T : ℕ → α) (t L : ℕ) : ℕ := #{c : α | Odd (cnt T t L c)}

/-- number of coordinates occurring exactly twice in the window -/
def P (T : ℕ → α) (t L : ℕ) : ℕ := #{c : α | cnt T t L c = 2}

/-- `T` is the transition word of a spread-`k` circuit code of length `N`:
`N`-periodic, closed (every coordinate flipped an even number of times), and
`d_H < k → d_C = d_H` for every pair of vertices at cyclic offsets `L`, `N - L`. -/
structure IsCoilWord (k N : ℕ) (T : ℕ → α) : Prop where
  per : ∀ i, T (i + N) = T i
  closed : ∀ c, Even (cnt T 0 N c)
  spread : ∀ t L, 1 ≤ L → L < N → oddc T t L < k → oddc T t L = min L (N - L)

lemma cnt_eq_sum (T : ℕ → α) (t L : ℕ) (c : α) :
    cnt T t L c = ∑ j ∈ range L, if T (t + j) = c then 1 else 0 := by
  rw [cnt, card_filter]

lemma sum_cnt (T : ℕ → α) (t L : ℕ) : ∑ c, cnt T t L c = L := by
  simp_rw [cnt_eq_sum]
  rw [sum_comm]
  simp

lemma cnt_add (T : ℕ → α) (t a b : ℕ) (c : α) :
    cnt T t (a + b) c = cnt T t a c + cnt T (t + a) b c := by
  simp_rw [cnt_eq_sum, sum_range_add, add_assoc]

lemma oddc_eq_sum (T : ℕ → α) (t L : ℕ) :
    oddc T t L = ∑ c, if Odd (cnt T t L c) then 1 else 0 := by
  rw [oddc, card_filter]

lemma P_eq_sum (T : ℕ → α) (t L : ℕ) :
    P T t L = ∑ c, if cnt T t L c = 2 then 1 else 0 := by
  rw [P, card_filter]

lemma oddc_parity (T : ℕ → α) (t L : ℕ) : Odd (oddc T t L) ↔ Odd L := by
  have := Finset.odd_sum_iff_odd_card_odd (s := univ) (fun c => cnt T t L c)
  rw [sum_cnt] at this
  exact this.symm

lemma oddc_le (T : ℕ → α) (t L : ℕ) : oddc T t L ≤ L := by
  calc oddc T t L = ∑ c, if Odd (cnt T t L c) then 1 else 0 := oddc_eq_sum T t L
    _ ≤ ∑ c, cnt T t L c := by
        apply sum_le_sum
        intro c _
        split_ifs with h
        · exact h.pos
        · exact Nat.zero_le _
    _ = L := sum_cnt T t L

variable {k N : ℕ} {T : ℕ → α}

/-- (F1) -/
lemma f1 (h : IsCoilWord k N T) (hk : 1 ≤ k) {t L : ℕ} (h1 : k ≤ L) (h2 : L + k ≤ N) :
    k ≤ oddc T t L := by
  by_contra hc
  rw [not_le] at hc
  have := h.spread t L (by omega) (by omega) hc
  omega

lemma oddc_short (h : IsCoilWord k N T) (hk : 1 ≤ k) (hN : 2 * k + 2 ≤ N) {t L : ℕ}
    (hL : L ≤ k + 1) : oddc T t L = L := by
  have hle := oddc_le T t L
  rcases Nat.eq_zero_or_pos L with h0 | hpos
  · omega
  by_cases hlt : L < k
  · by_contra hne
    have h3 : oddc T t L < k := by omega
    have := h.spread t L hpos (by omega) h3
    omega
  · have hf := f1 h hk (t := t) (L := L) (by omega) (by omega)
    have hp := oddc_parity T t L
    rw [Nat.odd_iff, Nat.odd_iff] at hp
    omega

/-- (F2): any `k+1` consecutive transitions are distinct -/
lemma cnt_short (h : IsCoilWord k N T) (hk : 1 ≤ k) (hN : 2 * k + 2 ≤ N) {t L : ℕ}
    (hL : L ≤ k + 1) (c : α) : cnt T t L c ≤ 1 := by
  have h1 := oddc_short h hk hN (t := t) hL
  have h2 := sum_cnt T t L
  have h3 := oddc_eq_sum T t L
  by_contra hc
  rw [not_le] at hc
  have : ∑ c, (if Odd (cnt T t L c) then 1 else 0) < ∑ c, cnt T t L c := by
    apply sum_lt_sum
    · intro c _
      split_ifs with h
      · exact h.pos
      · exact Nat.zero_le _
    · exact ⟨c, mem_univ _, by split_ifs <;> omega⟩
  omega

lemma cnt_le_two (h : IsCoilWord k N T) (hk : 1 ≤ k) (hN : 2 * k + 2 ≤ N) {t L : ℕ}
    (hL : L ≤ 2 * (k + 1)) (c : α) : cnt T t L c ≤ 2 := by
  rcases le_total L (k + 1) with h' | h'
  · have := cnt_short h hk hN (t := t) h' c
    omega
  · obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le h'
    rw [cnt_add]
    have := cnt_short h hk hN (t := t) (le_refl (k + 1)) c
    have := cnt_short h hk hN (t := t + (k + 1)) (L := b) (by omega) c
    omega

/-- if every coordinate occurs at most twice, `L = odd(W) + 2 P(W)` -/
lemma decomp {t L : ℕ} (hall : ∀ c, cnt T t L c ≤ 2) : L = oddc T t L + 2 * P T t L := by
  have key : ∀ c, cnt T t L c =
      (if Odd (cnt T t L c) then 1 else 0) + 2 * (if cnt T t L c = 2 then 1 else 0) := by
    intro c
    have := hall c
    simp only [Nat.odd_iff]
    split_ifs <;> omega
  have hs := sum_cnt T t L
  rw [sum_congr rfl (fun c _ => key c), sum_add_distrib, ← mul_sum] at hs
  rw [oddc_eq_sum, P_eq_sum]
  exact hs.symm

lemma sum_shift (g : ℕ → ℕ) (N : ℕ) (hg : ∀ i, g (i + N) = g i) (j : ℕ) :
    ∑ t ∈ range N, g (t + j) = ∑ t ∈ range N, g t := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [← ih]
    have a := sum_range_succ (fun t => g (t + j)) N
    have b := sum_range_succ' (fun t => g (t + j)) N
    have e : g (N + j) = g (0 + j) := by rw [zero_add, add_comm, hg]
    have e2 : ∀ t, t + (j + 1) = t + 1 + j := by intro t; omega
    simp_rw [e2]
    linarith

/-- each position lies in exactly `L` windows of length `L` -/
lemma sum_cnt_windows (per : ∀ i, T (i + N) = T i) (L : ℕ) (c : α) :
    ∑ t ∈ range N, cnt T t L c = L * cnt T 0 N c := by
  simp_rw [cnt_eq_sum]
  rw [sum_comm]
  have : ∀ j, ∑ t ∈ range N, (if T (t + j) = c then 1 else 0)
      = ∑ t ∈ range N, if T (0 + t) = c then 1 else 0 := by
    intro j
    simpa using sum_shift (fun i => if T i = c then 1 else 0) N (by intro i; simp [per i]) j
  simp [this]

/-- **Lemma 1 (chord inequality)**, in the form
`(N - 2n)(4L - N) ≤ 2N ⌊(L-k)/2⌋` for `max(k, N/4) ≤ L ≤ min(2k+2, N-k)`, `N < 6(k+1)`. -/
theorem chord_inequality (h : IsCoilWord k N T) (hk : 1 ≤ k) (hN : 2 * k + 2 ≤ N)
    (hN6 : N < 6 * (k + 1)) {L : ℕ} (hL1 : k ≤ L) (hL2 : N ≤ 4 * L) (hL3 : L ≤ 2 * (k + 1))
    (hL4 : L + k ≤ N) :
    ((N : ℤ) - 2 * Fintype.card α) * (4 * L - N) ≤ 2 * N * ((L - k) / 2 : ℕ) := by
  -- uses of each coordinate: 0, 2 or 4
  have hm : ∀ c, cnt T 0 N c ≤ 4 := by
    intro c
    have h1 := sum_cnt_windows h.per (k + 1) c
    have h2 : ∑ t ∈ range N, cnt T t (k + 1) c ≤ ∑ _t ∈ range N, 1 :=
      sum_le_sum (fun t _ => cnt_short h hk hN (le_refl _) c)
    simp only [sum_const, card_range, smul_eq_mul, mul_one] at h2
    obtain ⟨r, hr⟩ := h.closed c
    by_contra hc
    have h6 : 6 ≤ cnt T 0 N c := by omega
    have := Nat.mul_le_mul_left (k + 1) h6
    omega
  -- number of coordinates used four times
  have hn2 : N ≤ 2 * Fintype.card α + 2 * #{c : α | cnt T 0 N c = 4} := by
    have hs := sum_cnt T 0 N
    have : ∑ c, cnt T 0 N c ≤ ∑ c : α, (2 + 2 * (if cnt T 0 N c = 4 then 1 else 0)) := by
      apply sum_le_sum
      intro c _
      have := hm c
      obtain ⟨r, hr⟩ := h.closed c
      split_ifs <;> omega
    rw [sum_add_distrib, ← mul_sum, ← card_filter] at this
    simp only [sum_const, card_univ, smul_eq_mul] at this
    omega
  -- chords per window
  have hP : ∀ t, P T t L ≤ (L - k) / 2 := by
    intro t
    have := decomp (T := T) (t := t) (L := L) (fun c => cnt_le_two h hk hN hL3 c)
    have := f1 h hk (t := t) hL1 hL4
    omega
  have hPs : ∑ t ∈ range N, P T t L ≤ N * ((L - k) / 2) := by
    calc ∑ t ∈ range N, P T t L ≤ ∑ _t ∈ range N, (L - k) / 2 := sum_le_sum (fun t _ => hP t)
      _ = N * ((L - k) / 2) := by simp
  -- double count
  have hc4 : ∀ c, cnt T 0 N c = 4 →
      4 * L ≤ (∑ t ∈ range N, if cnt T t L c = 2 then 1 else 0) + N := by
    intro c hc
    have h1 := sum_cnt_windows h.per L c
    rw [hc] at h1
    have h2 : ∑ t ∈ range N, cnt T t L c ≤
        ∑ t ∈ range N, ((if cnt T t L c = 2 then 1 else 0) + 1) := by
      apply sum_le_sum
      intro t _
      have := cnt_le_two h hk hN (t := t) hL3 c
      split_ifs <;> omega
    rw [sum_add_distrib] at h2
    simp only [sum_const, card_range, smul_eq_mul, mul_one] at h2
    omega
  have hdc : #{c : α | cnt T 0 N c = 4} * (4 * L - N) ≤ ∑ t ∈ range N, P T t L := by
    simp_rw [P_eq_sum]
    rw [sum_comm, card_filter, sum_mul]
    apply sum_le_sum
    intro c _
    split_ifs with hc
    · have := hc4 c hc
      omega
    · simp
  -- combine
  set n2 := #{c : α | cnt T 0 N c = 4} with hn2def
  have e1 : ((N : ℤ) - 2 * Fintype.card α) ≤ 2 * n2 := by
    have : (N : ℤ) ≤ 2 * Fintype.card α + 2 * n2 := by exact_mod_cast hn2
    linarith
  have e2 : (0 : ℤ) ≤ 4 * L - N := by
    have : (N : ℤ) ≤ 4 * L := by exact_mod_cast hL2
    linarith
  have e3 : (n2 : ℤ) * (4 * L - N) ≤ N * ((L - k) / 2 : ℕ) := by
    have : n2 * (4 * L - N) ≤ N * ((L - k) / 2) := le_trans hdc hPs
    have h' : ((n2 * (4 * L - N) : ℕ) : ℤ) ≤ ((N * ((L - k) / 2) : ℕ) : ℤ) := by exact_mod_cast this
    push_cast [Nat.cast_sub hL2] at h'
    exact h'
  calc ((N : ℤ) - 2 * Fintype.card α) * (4 * L - N) ≤ 2 * n2 * (4 * L - N) :=
        mul_le_mul_of_nonneg_right e1 e2
    _ = 2 * (n2 * (4 * L - N)) := by ring
    _ ≤ 2 * (N * ((L - k) / 2 : ℕ)) := by linarith
    _ = 2 * N * ((L - k) / 2 : ℕ) := by ring

/-! ## Lemma 2 (no long codes): a purely local argument on one window of length `4(k+1)` -/

/-- number of coordinates occurring exactly three times in the window -/
def C3 (T : ℕ → α) (t L : ℕ) : ℕ := #{c : α | cnt T t L c = 3}

lemma C3_eq_sum (T : ℕ → α) (t L : ℕ) :
    C3 T t L = ∑ c, if cnt T t L c = 3 then 1 else 0 := by
  rw [C3, card_filter]

lemma P_le (h : IsCoilWord k N T) (hk : 1 ≤ k) (hN : 2 * k + 2 ≤ N) {t L : ℕ}
    (hL1 : k ≤ L) (hL3 : L ≤ 2 * (k + 1)) (hL4 : L + k ≤ N) : P T t L ≤ (L - k) / 2 := by
  have := decomp (T := T) (t := t) (L := L) (fun c => cnt_le_two h hk hN hL3 c)
  have := f1 h hk (t := t) hL1 hL4
  omega

lemma cnt_le_three (h : IsCoilWord k N T) (hk : 1 ≤ k) (hN : 2 * k + 2 ≤ N) {t L : ℕ}
    (hL : L ≤ 3 * (k + 1)) (c : α) : cnt T t L c ≤ 3 := by
  rcases le_total L (k + 1) with h' | h'
  · have := cnt_short h hk hN (t := t) h' c
    omega
  · obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le h'
    rw [cnt_add]
    have := cnt_short h hk hN (t := t) (le_refl (k + 1)) c
    have := cnt_le_two h hk hN (t := t + (k + 1)) (L := b) (by omega) c
    omega

/-- a window of length `≤ 3(k+1)`: `L + odd(W) ≤ 2n + 2 c₃(W)` -/
lemma C3_ge (h : IsCoilWord k N T) (hk : 1 ≤ k) (hN : 2 * k + 2 ≤ N) {t L : ℕ}
    (hL : L ≤ 3 * (k + 1)) : L + oddc T t L ≤ 2 * Fintype.card α + 2 * C3 T t L := by
  have key : ∀ c, cnt T t L c + (if Odd (cnt T t L c) then 1 else 0)
      ≤ 2 + 2 * (if cnt T t L c = 3 then 1 else 0) := by
    intro c
    have := cnt_le_three h hk hN (t := t) hL c
    simp only [Nat.odd_iff]
    split_ifs <;> omega
  have S := sum_le_sum (s := univ) (fun c _ => key c)
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum, sum_cnt, ← oddc_eq_sum, ← C3_eq_sum] at S
  simp only [sum_const, card_univ, smul_eq_mul] at S
  omega

/-- **Lemma 2**: a spread-`k` coil with `N ≥ 5k+4` forces
`k + (k mod 2) ≤ 6n - 12(k+1) + 6⌊(k+2)/2⌋`. -/
theorem no_long (h : IsCoilWord k N T) (hk : 1 ≤ k) (hN5 : 5 * k + 4 ≤ N) :
    k + k % 2 + 12 * (k + 1) ≤ 6 * Fintype.card α + 6 * ((k + 2) / 2) := by
  have hN : 2 * k + 2 ≤ N := by omega
  obtain ⟨K, hK⟩ : ∃ K, K = k + 1 := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : ℕ, t = 0 := ⟨_, rfl⟩
  have key : ∀ c, (if Odd (cnt T t (K + K + K + K) c) then 1 else 0) + cnt T t (K + K + K + K) c
      + 2 * (if cnt T t (K + K + K) c = 3 then 1 else 0)
      + 2 * (if cnt T (t + K) (K + K + K) c = 3 then 1 else 0)
      ≤ 2 + 2 * (if cnt T t (K + K) c = 2 then 1 else 0)
        + 2 * (if cnt T (t + K + K) (K + K) c = 2 then 1 else 0)
        + 2 * (if cnt T (t + K) (K + K) c = 2 then 1 else 0) := by
    intro c
    have h1 := cnt_short h hk hN (t := t) (L := K) (by omega) c
    have h2 := cnt_short h hk hN (t := t + K) (L := K) (by omega) c
    have h3 := cnt_short h hk hN (t := t + K + K) (L := K) (by omega) c
    have h4 := cnt_short h hk hN (t := t + K + K + K) (L := K) (by omega) c
    simp only [cnt_add, ← add_assoc, Nat.odd_iff]
    split_ifs <;> omega
  have S := sum_le_sum (s := univ) (fun c _ => key c)
  simp only [sum_add_distrib, ← mul_sum, ← oddc_eq_sum, ← P_eq_sum, ← C3_eq_sum, sum_cnt,
    sum_const, card_univ, smul_eq_mul] at S
  have o4 := f1 h hk (t := t) (L := K + K + K + K) (by omega) (by omega)
  have p4 := oddc_parity T t (K + K + K + K)
  have o3 := f1 h hk (t := t) (L := K + K + K) (by omega) (by omega)
  have p3 := oddc_parity T t (K + K + K)
  have o3' := f1 h hk (t := t + K) (L := K + K + K) (by omega) (by omega)
  have p3' := oddc_parity T (t + K) (K + K + K)
  have c3 := C3_ge h hk hN (t := t) (L := K + K + K) (by omega)
  have c3' := C3_ge h hk hN (t := t + K) (L := K + K + K) (by omega)
  have q1 := P_le h hk hN (t := t) (L := K + K) (by omega) (by omega) (by omega)
  have q2 := P_le h hk hN (t := t + K + K) (L := K + K) (by omega) (by omega) (by omega)
  have q3 := P_le h hk hN (t := t + K) (L := K + K) (by omega) (by omega) (by omega)
  rw [Nat.odd_iff, Nat.odd_iff] at p4 p3 p3'
  omega

/-! ## Main Theorem -/

lemma even_length (h : IsCoilWord k N T) : Even N := by
  rw [← sum_cnt T 0 N]
  apply Finset.even_sum
  intro c _
  exact h.closed c

/-- **Main Theorem** (PROOF.md): with `l = 2n - 3k - 1 ≥ 2`, if
`k > (l²-1)/2` and `k > 3l-3` (`k` even), resp. `k > (l-2)(l+1)/2` (`k` odd),
every spread-`k` circuit code in the `n`-cube has length `N ≤ 4k + 2l`. -/
theorem main_theorem (h : IsCoilWord k N T) (hk : 1 ≤ k) (l : ℕ) (hl : 2 ≤ l)
    (hn : 2 * Fintype.card α = 3 * k + l + 1)
    (hyp : if Even k then (l * l < 2 * k + 1 ∧ 3 * l < k + 3) else l * l < 2 * k + l + 2) :
    N ≤ 4 * k + 2 * l := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨m, hm⟩ := even_length h
  have hNlo : 4 * k + 2 * l + 2 ≤ N := by omega
  have hN : 2 * k + 2 ≤ N := by omega
  by_cases hke : Even k
  · simp only [hke, ite_true] at hyp
    obtain ⟨r, hr⟩ := hke
    have hN5 : N ≤ 5 * k + 3 := by
      by_contra h5
      have := no_long h hk (by omega)
      omega
    have C := chord_inequality h hk hN (by omega) (L := 2 * k + 1) (by omega) (by omega)
      (by omega) (by omega)
    have e : (2 * k + 1 - k) / 2 = r := by omega
    rw [e] at C
    have hn' : (2 : ℤ) * Fintype.card α = 3 * k + l + 1 := by exact_mod_cast hn
    have a1 : (0 : ℤ) ≤ N - 4 * k - 2 * l - 2 := by
      have : (4 * k + 2 * l + 2 : ℤ) ≤ N := by exact_mod_cast hNlo
      linarith
    have a2 : (0 : ℤ) ≤ 5 * k + 4 - N := by
      have : (N : ℤ) ≤ 5 * k + 3 := by exact_mod_cast hN5
      linarith
    have a3 : (0 : ℤ) ≤ k - 1 - l := by
      have : (l + 1 : ℤ) ≤ k := by exact_mod_cast (by omega : l + 1 ≤ k)
      linarith
    have a4 : (l : ℤ) * l + 1 ≤ 2 * k + 1 := by exact_mod_cast hyp.1
    have hkr : (k : ℤ) = 2 * r := by exact_mod_cast (by omega : k = 2 * r)
    push_cast at C
    rw [hn'] at C
    nlinarith [mul_nonneg a1 a2, mul_nonneg a3 a1]
  · simp only [hke, ite_false] at hyp
    obtain ⟨r, hr⟩ := Nat.not_even_iff_odd.mp hke
    have hN5 : N ≤ 5 * k + 3 := by
      by_contra h5
      have := no_long h hk (by omega)
      have h7 : l * l + 13 ≤ 7 * l := by omega
      have h8 : l ≤ 7 := by nlinarith
      interval_cases l <;> omega
    have C := chord_inequality h hk hN (by omega) (L := 2 * k + 2) (by omega) (by omega)
      (by omega) (by omega)
    have e : (2 * k + 2 - k) / 2 = r + 1 := by omega
    rw [e] at C
    have hn' : (2 : ℤ) * Fintype.card α = 3 * k + l + 1 := by exact_mod_cast hn
    have a1 : (0 : ℤ) ≤ N - 4 * k - 2 * l - 2 := by
      have : (4 * k + 2 * l + 2 : ℤ) ≤ N := by exact_mod_cast hNlo
      linarith
    have a2 : (0 : ℤ) ≤ 5 * k + 3 - N := by
      have : (N : ℤ) ≤ 5 * k + 3 := by exact_mod_cast hN5
      linarith
    have a3 : (0 : ℤ) ≤ k + 3 - l := by
      have : l ≤ k + 3 := by nlinarith
      have : (l : ℤ) ≤ k + 3 := by exact_mod_cast this
      linarith
    have a4 : (l : ℤ) * l + 1 ≤ 2 * k + l + 2 := by exact_mod_cast hyp
    have hkr : (k : ℤ) = 2 * r + 1 := by exact_mod_cast hr
    push_cast at C
    rw [hn'] at C
    nlinarith [mul_nonneg a1 a2, mul_nonneg a3 a1]

/-! ## From vertices of the cube to transition words -/

/-- Hamming distance between two vertices of the cube `α → Bool` -/
def hd (x y : α → Bool) : ℕ := #{c : α | x c ≠ y c}

/-- `v` (extended `N`-periodically) is a spread-`k` circuit code of length `N` in the cube
`α → Bool`: consecutive vertices are adjacent, and `d_H(v_i, v_j) < k → d_C(i,j) = d_H(v_i,v_j)`
(`d_C` = cyclic distance `min(L, N-L)` for `j = i + L`, `0 ≤ L < N`). -/
structure IsCoil (k N : ℕ) (v : ℕ → α → Bool) : Prop where
  per : ∀ i, v (i + N) = v i
  adj : ∀ i, hd (v i) (v (i + 1)) = 1
  spread : ∀ i L, L < N → hd (v i) (v (i + L)) < k → hd (v i) (v (i + L)) = min L (N - L)

lemma cnt_one (T : ℕ → α) (s : ℕ) (c : α) : cnt T s 1 c = if T s = c then 1 else 0 := by
  rw [cnt_eq_sum, Finset.sum_range_one, add_zero]

lemma walk_parity {v : ℕ → α → Bool} {T : ℕ → α}
    (hT : ∀ i c, v i c ≠ v (i + 1) c ↔ c = T i) (t L : ℕ) (c : α) :
    v t c ≠ v (t + L) c ↔ Odd (cnt T t L c) := by
  induction L with
  | zero => simp [cnt]
  | succ L ih =>
    have h1 := hT (t + L) c
    rw [← add_assoc]
    by_cases hc : T (t + L) = c
    · have e : cnt T t (L + 1) c = cnt T t L c + 1 := by
        rw [cnt_add, cnt_one]
        simp [hc]
      rw [e, Nat.odd_add_one, ← ih]
      have : v (t + L) c ≠ v (t + L + 1) c := h1.mpr hc.symm
      revert this
      cases v (t + L) c <;> cases v (t + L + 1) c <;> cases v t c <;> simp
    · have e : cnt T t (L + 1) c = cnt T t L c := by
        rw [cnt_add, cnt_one]
        simp [hc]
      rw [e, ← ih]
      have : v (t + L) c = v (t + L + 1) c := by
        by_contra h'
        exact hc (h1.mp h').symm
      rw [this]

theorem IsCoil.exists_word {v : ℕ → α → Bool} (h : IsCoil k N v) :
    ∃ T : ℕ → α, IsCoilWord k N T ∧ ∀ t L, hd (v t) (v (t + L)) = oddc T t L := by
  have hex : ∀ i, ∃ a, ∀ c, v i c ≠ v (i + 1) c ↔ c = a := by
    intro i
    have h1 := h.adj i
    unfold hd at h1
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
    refine ⟨a, fun c => ?_⟩
    simpa using Finset.ext_iff.mp ha c
  choose T hT using hex
  have hdo : ∀ t L, hd (v t) (v (t + L)) = oddc T t L := by
    intro t L
    rw [hd, oddc]
    exact congrArg card (filter_congr fun c _ => walk_parity hT t L c)
  refine ⟨T, ⟨?_, ?_, ?_⟩, hdo⟩
  · intro i
    have h2 : v (i + N) (T i) ≠ v (i + N + 1) (T i) := by
      rw [h.per i, show i + N + 1 = i + 1 + N by omega, h.per (i + 1)]
      exact (hT i (T i)).mpr rfl
    exact ((hT (i + N) (T i)).mp h2).symm
  · intro c
    by_contra hc
    have h2 := (walk_parity hT 0 N c).mpr (Nat.not_even_iff_odd.mp hc)
    rw [h.per 0] at h2
    exact h2 rfl
  · intro t L _ h2 h3
    rw [← hdo] at h3 ⊢
    exact h.spread t L h2 h3

/-- **Main Theorem for circuit codes.**  Let `v` be a spread-`k` circuit code of length `N`
in the `n`-cube, `l = 2n - 3k - 1 ≥ 2`.  If `k` is even, `2k > l² - 1` and `k > 3l - 3`,
or `k` is odd and `2k > (l-2)(l+1)`, then `N ≤ 4k + 2l`. -/
theorem coil_length_bound {v : ℕ → α → Bool} (h : IsCoil k N v) (hk : 1 ≤ k) (l : ℕ)
    (hl : 2 ≤ l) (hn : 2 * Fintype.card α = 3 * k + l + 1)
    (hyp : if Even k then (l * l < 2 * k + 1 ∧ 3 * l < k + 3) else l * l < 2 * k + l + 2) :
    N ≤ 4 * k + 2 * l := by
  obtain ⟨T, hT, _⟩ := h.exists_word
  exact main_theorem hT hk l hl hn hyp

/-! ## Exact values: instance-level upper bounds from Lemma 1 + Lemma 2 -/

/-- Upper bound `N ≤ B` from Lemma 2 (`hlong`) and Lemma 1 at one window length `L`
(`hchk`, a finite numeric check). -/
theorem length_le_of_chord (h : IsCoilWord k N T) (hk : 1 ≤ k) (n B L : ℕ)
    (hn : Fintype.card α = n) (hB : 2 * k + 2 ≤ B)
    (hlong : 6 * n + 6 * ((k + 2) / 2) < k + k % 2 + 12 * (k + 1))
    (hchk : ∀ M, M < 5 * k + 4 → B < M → Even M →
      (k ≤ L ∧ M ≤ 4 * L ∧ L ≤ 2 * (k + 1) ∧ L + k ≤ M ∧
        2 * (M : ℤ) * ((L - k) / 2 : ℕ) < ((M : ℤ) - 2 * n) * (4 * L - M))) :
    N ≤ B := by
  by_contra hcon
  rw [not_le] at hcon
  have h5 : N < 5 * k + 4 := by
    by_contra h5
    have := no_long h hk (by omega)
    omega
  obtain ⟨c1, c2, c3, c4, c5⟩ := hchk N h5 hcon (even_length h)
  have C := chord_inequality h hk (by omega) (by omega) c1 c2 c3 c4
  rw [hn] at C
  linarith

/-- `N` is the maximum length of a spread-`k` circuit code in the `n`-cube: `K(n,k) = N` -/
def IsMaxLength (n k N : ℕ) : Prop :=
  (∃ v : ℕ → Fin n → Bool, IsCoil k N v) ∧
    ∀ (N' : ℕ) (v' : ℕ → Fin n → Bool), IsCoil k N' v' → N' ≤ N

theorem isMaxLength_of_chord {n k N : ℕ} (hv : ∃ v : ℕ → Fin n → Bool, IsCoil k N v)
    (hk : 1 ≤ k) (L : ℕ) (hB : 2 * k + 2 ≤ N)
    (hlong : 6 * n + 6 * ((k + 2) / 2) < k + k % 2 + 12 * (k + 1))
    (hchk : ∀ M, M < 5 * k + 4 → N < M → Even M →
      (k ≤ L ∧ M ≤ 4 * L ∧ L ≤ 2 * (k + 1) ∧ L + k ≤ M ∧
        2 * (M : ℤ) * ((L - k) / 2 : ℕ) < ((M : ℤ) - 2 * n) * (4 * L - M))) :
    IsMaxLength n k N := by
  refine ⟨hv, fun N' v' h' => ?_⟩
  obtain ⟨T, hT, _⟩ := h'.exists_word
  exact length_le_of_chord hT hk n N L (by simp) hB hlong hchk

end Coil

#print axioms Coil.chord_inequality
#print axioms Coil.no_long
#print axioms Coil.main_theorem
#print axioms Coil.coil_length_bound
