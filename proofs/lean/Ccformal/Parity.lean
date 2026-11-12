import Ccformal.Thm7
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.ZMod.Basic

/-!
# Theorem 24 (PROOF10.md sec. 6): the parity obstruction at equality points of Lemma 1

`k` odd, `K = k+1`, zero slack in Lemma 1 at `L = 2K`, `4K + 2 < N < 6K`, `p = gcd(2K, N)`.
If `p ∣ K` and `N / p` is odd there is no spread-`k` circuit code of length `N`.
(Contains Theorems 7, 15, 17 and Corollaries 18, 25.)
-/

open Finset

namespace Coil

set_option linter.unusedSectionVars false
set_option linter.deprecated false

variable {α : Type*} [Fintype α] [DecidableEq α] {k N : ℕ} {T : ℕ → α}

lemma per_mod (per : ∀ i, T (i + N) = T i) (i : ℕ) : T i = T (i % N) := by
  conv_lhs => rw [← Nat.mod_add_div i N, mul_comm]
  exact per_mul per _ _

lemma tmod (per : ∀ i, T (i + N) = T i) {a b : ℕ} (hab : a % N = b % N) : T a = T b := by
  rw [per_mod per a, per_mod per b, hab]

lemma adj_ne (h : IsCoilWord k N T) (hk : 1 ≤ k) (hN : 2 * k + 2 ≤ N) {a b : ℕ}
    (e : T a = T b) (hm : (a + 1) % N = b % N) : False := by
  have h1 : T (a + 1) = T b := tmod h.per hm
  have := gap_ge h hk hN (u := a) (d := 1) le_rfl (e.trans h1.symm)
  omega

/-- two occurrences that are congruent mod `N` have the same previous occurrence -/
lemma bwd (h : IsCoilWord k N T) (hk : 1 ≤ k) (hN : 2 * k + 2 ≤ N) {a b g g2 : ℕ}
    (hg : g = k + 1 ∨ g = k + 2) (hg2 : g2 = k + 1 ∨ g2 = k + 2)
    (ea : T a = T (a + g)) (eb : T b = T (b + g2)) (hm : (a + g) % N = (b + g2) % N) :
    g = g2 ∧ a % N = b % N := by
  have eab : T a = T b := ea.trans ((tmod h.per hm).trans eb.symm)
  rcases hg with rfl | rfl <;> rcases hg2 with rfl | rfl
  · exact ⟨rfl, Nat.ModEq.add_right_cancel' (k + 1) hm⟩
  · exfalso
    have : a % N = (b + 1) % N := by
      apply Nat.ModEq.add_right_cancel' (k + 1)
      rw [show b + 1 + (k + 1) = b + (k + 2) by omega]
      exact hm
    exact adj_ne h hk hN eab.symm this.symm
  · exfalso
    have : (a + 1) % N = b % N := by
      apply Nat.ModEq.add_right_cancel' (k + 1)
      rw [show a + 1 + (k + 1) = a + (k + 2) by omega]
      exact hm
    exact adj_ne h hk hN eab this
  · exact ⟨rfl, Nat.ModEq.add_right_cancel' (k + 2) hm⟩

/-- two occurrences that are congruent mod `N` have the same next occurrence -/
lemma fwd (h : IsCoilWord k N T) (hk : 1 ≤ k) (hN : 2 * k + 2 ≤ N) {a b g g2 : ℕ}
    (hg : g = k + 1 ∨ g = k + 2) (hg2 : g2 = k + 1 ∨ g2 = k + 2)
    (ea : T a = T (a + g)) (eb : T b = T (b + g2)) (hm : a % N = b % N) : g = g2 := by
  have eab : T a = T b := tmod h.per hm
  rcases hg with rfl | rfl <;> rcases hg2 with rfl | rfl
  · rfl
  · exfalso
    have h1 : T (b + (k + 1)) = T (a + (k + 1)) := tmod h.per (Nat.ModEq.add_right (k + 1) hm.symm)
    have h2 : T (b + (k + 1)) = T (b + (k + 1) + 1) := by
      rw [show b + (k + 1) + 1 = b + (k + 2) by omega]
      exact h1.trans (ea.symm.trans (eab.trans eb))
    have := gap_ge h hk hN (u := b + (k + 1)) (d := 1) le_rfl h2
    omega
  · exfalso
    have h1 : T (a + (k + 1)) = T (b + (k + 1)) := tmod h.per (Nat.ModEq.add_right (k + 1) hm)
    have h2 : T (a + (k + 1)) = T (a + (k + 1) + 1) := by
      rw [show a + (k + 1) + 1 = a + (k + 2) by omega]
      exact h1.trans (eb.symm.trans (eab.symm.trans ea))
    have := gap_ge h hk hN (u := a + (k + 1)) (d := 1) le_rfl h2
    omega
  · rfl

/-- (Z4) in the equality case the type word (F / not F) has period `L` -/
lemma typeword_period (h : IsCoilWord k N T) (hk : 1 ≤ k) (hN : 2 * k + 2 ≤ N) {L c0 : ℕ}
    (hL3 : L ≤ 2 * (k + 1)) (E2 : ∀ t, P T t L = c0)
    (E3 : ∀ c, cnt T 0 N c = 4 → ∀ t, 1 ≤ cnt T t L c)
    (E4 : ∀ c, cnt T 0 N c ≠ 4 → ∀ t, cnt T t L c ≠ 2) (t : ℕ) :
    (cnt T 0 N (T t) = 4 ↔ cnt T 0 N (T (t + L)) = 4) := by
    obtain ⟨c, hc⟩ : ∃ c, c = T t := ⟨_, rfl⟩
    obtain ⟨c', hc'⟩ : ∃ c', c' = T (t + L) := ⟨_, rfl⟩
    have slide := fun x => cnt_slide T t L x
    rw [← hc, ← hc'] at slide ⊢
    have Pt := E2 t
    have Pt1 := E2 (t + 1)
    constructor
    · intro hF
      by_contra hF'
      have hne : c ≠ c' := fun e => hF' (e ▸ hF)
      have a := E4 c' hF' (t + 1)
      have b := E3 c hF (t + 1)
      have hlt : P T (t + 1) L < P T t L := by
        rw [P_eq_sum, P_eq_sum]
        apply sum_lt_sum
        · intro x _
          have s := slide x
          have le2 := cnt_le_two h hk hN (t := t) hL3 x
          by_cases h1 : c = x
          · subst h1
            rw [if_pos rfl, if_neg (fun e => hne e.symm)] at s
            split_ifs <;> omega
          · by_cases h2 : c' = x
            · subst h2
              rw [if_neg h1, if_pos rfl] at s
              split_ifs <;> omega
            · rw [if_neg h1, if_neg h2] at s
              split_ifs <;> omega
        · refine ⟨c, mem_univ _, ?_⟩
          have s := slide c
          have le2 := cnt_le_two h hk hN (t := t) hL3 c
          rw [if_pos rfl, if_neg (fun e => hne e.symm)] at s
          split_ifs <;> omega
      omega
    · intro hF'
      by_contra hF
      have hne : c ≠ c' := fun e => hF (e ▸ hF')
      have a := E4 c hF t
      have b := E3 c' hF' t
      have hlt : P T t L < P T (t + 1) L := by
        rw [P_eq_sum, P_eq_sum]
        apply sum_lt_sum
        · intro x _
          have s := slide x
          have le2 := cnt_le_two h hk hN (t := t + 1) hL3 x
          by_cases h1 : c = x
          · subst h1
            rw [if_pos rfl, if_neg (fun e => hne e.symm)] at s
            split_ifs <;> omega
          · by_cases h2 : c' = x
            · subst h2
              rw [if_neg h1, if_pos rfl] at s
              split_ifs <;> omega
            · rw [if_neg h1, if_neg h2] at s
              split_ifs <;> omega
        · refine ⟨c', mem_univ _, ?_⟩
          have s := slide c'
          have le2 := cnt_le_two h hk hN (t := t + 1) hL3 c'
          rw [if_neg hne, if_pos rfl] at s
          split_ifs <;> omega
      omega

/-- more than half of the positions are F positions: two adjacent F positions exist -/
lemma exists_FF (h : IsCoilWord k N T) (hcount : N < 8 * #{c : α | cnt T 0 N c = 4}) :
    ∃ s, cnt T 0 N (T s) = 4 ∧ cnt T 0 N (T (s + 1)) = 4 := by
  by_contra hno
  have hno' : ∀ t, ¬(cnt T 0 N (T t) = 4 ∧ cnt T 0 N (T (t + 1)) = 4) :=
    fun t ht => hno ⟨t, ht⟩
  let Φ : ℕ → ℕ := fun t => if cnt T 0 N (T t) = 4 then 1 else 0
  have hΦc : ∀ c, ∑ t ∈ range N, (if T t = c then (if cnt T 0 N c = 4 then 1 else 0) else 0)
      = 4 * (if cnt T 0 N c = 4 then 1 else 0) := by
    intro c
    by_cases hc : cnt T 0 N c = 4
    · have := cnt_eq_sum T 0 N c
      simp only [zero_add] at this
      simp only [hc, if_true]
      rw [← this, hc]
    · simp [hc]
  have hΦsum : ∑ t ∈ range N, Φ t = 4 * #{c : α | cnt T 0 N c = 4} := by
    have e1 : ∀ t ∈ range N, Φ t
        = ∑ c, (if T t = c then (if cnt T 0 N c = 4 then 1 else 0) else 0) := by
      intro t _
      rw [sum_ite_eq]
      simp [Φ]
    rw [sum_congr rfl e1, sum_comm, sum_congr rfl (fun c _ => hΦc c), ← mul_sum, ← card_filter]
  have hΦper : ∀ i, Φ (i + N) = Φ i := by
    intro i
    simp only [Φ, h.per i]
  have hsh := sum_shift Φ N hΦper 1
  have hle : ∑ t ∈ range N, (Φ t + Φ (t + 1)) ≤ ∑ _t ∈ range N, 1 := by
    apply sum_le_sum
    intro t _
    have := hno' t
    simp only [Φ]
    split_ifs with a b
    · exact absurd ⟨a, b⟩ this
    · omega
    · omega
    · omega
  rw [sum_add_distrib, hsh, hΦsum] at hle
  simp only [sum_const, card_range, smul_eq_mul, mul_one] at hle
  omega

/-- (Z5) every FF pair starts a triple ("serve") -/
lemma serve (h : IsCoilWord k N T) (hk : 1 ≤ k) (hN : 2 * k + 2 ≤ N) (hKe : Even (k + 1))
    {L : ℕ} (hL : L = 2 * (k + 1)) (hN3 : L + 2 + k ≤ N)
    (hper : ∀ t, (cnt T 0 N (T t) = 4 ↔ cnt T 0 N (T (t + L)) = 4))
    (E3 : ∀ c, cnt T 0 N c = 4 → ∀ t, 1 ≤ cnt T t L c)
    (hodd : ∀ t, oddc T t L = k + 1) (u : ℕ)
    (Fu : cnt T 0 N (T u) = 4) (Fu1 : cnt T 0 N (T (u + 1)) = 4) :
    (T u = T (u + (k + 1)) ∧ T (u + (k + 1)) = T (u + L)) ∨
    (T u = T (u + (k + 1)) ∧ T (u + (k + 1)) = T (u + L + 1)) ∨
    (T u = T (u + (k + 1) + 1) ∧ T (u + (k + 1) + 1) = T (u + L + 1)) ∨
    (T (u + 1) = T (u + (k + 1) + 1) ∧ T (u + (k + 1) + 1) = T (u + L + 1)) := by
    obtain ⟨r, hr⟩ := hKe
    have hL3 : L ≤ 2 * (k + 1) := by omega
    obtain ⟨a, ha⟩ : ∃ a, a = T (u + L) := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, b = T (u + L + 1) := ⟨_, rfl⟩
    have Fa : cnt T 0 N a = 4 := by rw [ha]; exact (hper u).mp Fu
    have Fb : cnt T 0 N b = 4 := by
      rw [hb, show u + L + 1 = u + 1 + L by omega]; exact (hper (u + 1)).mp Fu1
    have hab : a ≠ b := by
      intro e
      have := gap_ge h hk hN (u := u + L) (d := 1) (by omega) (by rw [← ha, ← hb]; exact e)
      omega
    have key : cnt T u L a = 2 ∨ cnt T u L b = 2 := by
      by_contra hcon
      rw [not_or] at hcon
      have a1 : cnt T u L a = 1 := by
        have := E3 a Fa u
        have := cnt_le_two h hk hN (t := u) hL3 a
        omega
      have b1 : cnt T u L b = 1 := by
        have := E3 b Fb u
        have := cnt_le_two h hk hN (t := u) hL3 b
        omega
      have ext : ∀ x, cnt T u (L + 1 + 1) x
          = cnt T u L x + (if a = x then 1 else 0) + (if b = x then 1 else 0) := by
        intro x
        rw [cnt_add, cnt_add, cnt_one, cnt_one, show u + (L + 1) = u + L + 1 by omega, ← ha, ← hb]
      have o1 := f1 h hk (t := u) (L := L + 1 + 1) (by omega) (by omega)
      have p1 := oddc_parity T u (L + 1 + 1)
      rw [Nat.odd_iff, Nat.odd_iff] at p1
      have pw : ∀ x ∈ (univ : Finset α), (if Odd (cnt T u (L + 1 + 1) x) then 1 else 0)
          + (if a = x then 1 else 0) + (if b = x then 1 else 0)
          ≤ (if Odd (cnt T u L x) then 1 else 0) := by
        intro x _
        rw [ext x]
        by_cases h1 : a = x
        · subst h1
          have hb' : ¬ b = a := fun e => hab e.symm
          simp [hb', a1, Nat.odd_iff]
        · by_cases h2 : b = x
          · subst h2
            simp [h1, b1, Nat.odd_iff]
          · simp [h1, h2]
      have S := sum_le_sum pw
      rw [sum_add_distrib, sum_add_distrib, ← oddc_eq_sum, ← oddc_eq_sum, hodd u] at S
      simp only [sum_ite_eq, mem_univ, if_true] at S
      omega
    rcases key with h2 | h2
    · obtain ⟨i, j, hij, hj, ei, ej⟩ := exists_two_of_cnt h2
      have g1 := gap_ge h hk hN (u := u + i) (d := j - i) (by omega)
        (by rw [show u + i + (j - i) = u + j by omega]; exact ei.trans ej.symm)
      have g2 := gap_ge h hk hN (u := u + j) (d := L - j) (by omega)
        (by rw [show u + j + (L - j) = u + L by omega, ← ha]; exact ej)
      obtain ⟨rfl, rfl⟩ : i = 0 ∧ j = k + 1 := by omega
      left
      rw [add_zero] at ei
      exact ⟨ei.trans ej.symm, ej.trans ha⟩
    · obtain ⟨i, j, hij, hj, ei, ej⟩ := exists_two_of_cnt h2
      have g1 := gap_ge h hk hN (u := u + i) (d := j - i) (by omega)
        (by rw [show u + i + (j - i) = u + j by omega]; exact ei.trans ej.symm)
      have g2 := gap_ge h hk hN (u := u + j) (d := L + 1 - j) (by omega)
        (by rw [show u + j + (L + 1 - j) = u + L + 1 by omega, ← hb]; exact ej)
      rcases (by omega : (i = 0 ∧ j = k + 1) ∨ (i = 0 ∧ j = k + 1 + 1) ∨ (i = 1 ∧ j = k + 1 + 1))
        with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · right; left
        rw [add_zero] at ei
        exact ⟨ei.trans ej.symm, ej.trans hb⟩
      · right; right; left
        rw [add_zero] at ei
        rw [← add_assoc] at ej
        exact ⟨ei.trans ej.symm, ej.trans hb⟩
      · right; right; right
        rw [← add_assoc] at ej
        exact ⟨ei.trans ej.symm, ej.trans hb⟩

set_option maxHeartbeats 4000000 in
/-- **Theorem 24** (parity obstruction), for transition words. -/
theorem parity_obstruction_aux (h : IsCoilWord k N T) (hk : 1 ≤ k) (hKe : Even (k + 1))
    {L : ℕ} (hL : L = 2 * (k + 1)) (hN1 : 2 * L + 2 < N) (hN6 : N < 6 * (k + 1))
    (hz : ((N : ℤ) - 2 * Fintype.card α) * (4 * L - N) = 2 * N * ((L - k) / 2 : ℕ))
    (p : ℕ) (hp : p = Nat.gcd L N) (hpK : p ∣ k + 1) (hodd : Odd (N / p)) : False := by
  obtain ⟨r, hr⟩ := hKe
  obtain ⟨m', hm'⟩ := even_length h
  have hN : 2 * k + 2 ≤ N := by omega
  have hL3 : L ≤ 2 * (k + 1) := by omega
  obtain ⟨E1, E2, E3, E4⟩ := equality_case h hk hN hN6 (L := L) (by omega) (by omega) hL3
    (by omega) hz
  have hc0 : (L - k) / 2 = r := by omega
  rw [hc0] at E2
  have hoddc : ∀ t, oddc T t L = k + 1 := by
    intro t
    have := decomp (T := T) (t := t) (L := L) (fun c => cnt_le_two h hk hN hL3 c)
    rw [E2 t] at this
    omega
  have hper := typeword_period h hk hN hL3 E2 E3 E4
  have hNpos : 0 < N := by omega
  -- F positions are more than half of all positions
  have hcount : N < 8 * #{c : α | cnt T 0 N c = 4} := by
    by_contra hcon
    rw [not_lt] at hcon
    obtain ⟨n2, hn2⟩ : ∃ n2, n2 = #{c : α | cnt T 0 N c = 4} := ⟨_, rfl⟩
    rw [← hn2] at hcon E1
    have e1 : (2 * n2 : ℤ) = (N : ℤ) - 2 * Fintype.card α := by
      have : ((2 * n2 + 2 * Fintype.card α : ℕ) : ℤ) = N := by exact_mod_cast E1
      push_cast at this
      linarith
    rw [hc0, ← e1] at hz
    have hL4 : (L : ℤ) = 4 * r := by exact_mod_cast (by omega : L = 4 * r)
    have hA : (8 * n2 : ℤ) ≤ N := by exact_mod_cast hcon
    have hD : (0 : ℤ) ≤ 4 * L - N := by
      have : (N : ℤ) ≤ 4 * L := by exact_mod_cast (by omega : N ≤ 4 * L)
      linarith
    have A := mul_le_mul_of_nonneg_right hA hD
    have hNz : (0 : ℤ) < N := by exact_mod_cast hNpos
    have hN4 : (0 : ℤ) < (N : ℤ) - 2 * L := by
      have : (2 * L : ℤ) < N := by exact_mod_cast (by omega : 2 * L < N)
      linarith
    have B := mul_pos hNz hN4
    rw [hL4] at hz A B
    nlinarith [A, B, hz]
  obtain ⟨s, Fs, Fs1⟩ := exists_FF h hcount
  -- the type word has period p = gcd(L, N)
  have hpN : p ∣ N := hp ▸ Nat.gcd_dvd_right L N
  have hpL : p ∣ L := hp ▸ Nat.gcd_dvd_left L N
  have hppos : 0 < p := Nat.pos_of_dvd_of_pos hpN hNpos
  have hmulL : ∀ m t, (cnt T 0 N (T (t + m * L)) = 4 ↔ cnt T 0 N (T t) = 4) := by
    intro m
    induction m with
    | zero => intro t; simp
    | succ m ih =>
      intro t
      rw [Nat.succ_mul, ← add_assoc, ← hper (t + m * L), ih]
  have hperp : ∀ t, (cnt T 0 N (T (t + p)) = 4 ↔ cnt T 0 N (T t) = 4) := by
    intro t
    have hlt : Nat.gcd L N < N := by
      have : Nat.gcd L N ≤ L := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left L N)
      omega
    obtain ⟨m, _, hm⟩ := Nat.exists_mul_mod_eq_gcd hlt
    rw [← hp] at hm
    have e : N * (L * m / N) + p = L * m := by
      rw [← hm]
      exact Nat.div_add_mod _ _
    have e2 : t + m * L = t + p + (L * m / N) * N := by
      rw [mul_comm m L, mul_comm (L * m / N) N]
      omega
    rw [← hmulL m t, e2, per_mul h.per]
  have hmulp : ∀ m t, (cnt T 0 N (T (t + m * p)) = 4 ↔ cnt T 0 N (T t) = 4) := by
    intro m
    induction m with
    | zero => intro t; simp
    | succ m ih =>
      intro t
      rw [Nat.succ_mul, ← add_assoc, hperp, ih]
  have hFmod : ∀ t, (cnt T 0 N (T t) = 4 ↔ cnt T 0 N (T (t % p)) = 4) := by
    intro t
    have := hmulp (t / p) (t % p)
    rw [show t % p + t / p * p = t by rw [mul_comm]; exact Nat.mod_add_div t p] at this
    exact this
  obtain ⟨a, ha⟩ : ∃ a, a = s % p := ⟨_, rfl⟩
  have hap : a < p := by rw [ha]; exact Nat.mod_lt _ hppos
  have hFa : ∀ t, t % p = a → cnt T 0 N (T t) = 4 ∧ cnt T 0 N (T (t + 1)) = 4 := by
    intro t ht
    constructor
    · rw [hFmod t, ht, ha, ← hFmod s]
      exact Fs
    · have : (t + 1) % p = (s + 1) % p := by
        rw [Nat.add_mod t 1 p, Nat.add_mod s 1 p, ht, ha]
      rw [hFmod (t + 1), this, ← hFmod (s + 1)]
      exact Fs1
  have hp2 : 2 ≤ p := by
    have h2N : 2 ∣ N := (even_iff_two_dvd).mp (even_length h)
    have h2L : 2 ∣ L := by rw [hL]; exact Dvd.intro _ rfl
    have : 2 ∣ p := hp ▸ Nat.dvd_gcd h2L h2N
    exact Nat.le_of_dvd hppos this
  have ha1 : a ≠ (a + 1) % p := by
    intro e
    by_cases h' : a + 1 < p
    · rw [Nat.mod_eq_of_lt h'] at e
      omega
    · have : a + 1 = p := by omega
      rw [this, Nat.mod_self] at e
      omega
  -- serves
  obtain ⟨K, hKd⟩ : ∃ K, K = k + 1 := ⟨_, rfl⟩
  have hK3 : 3 ≤ K := by omega
  have cT : ∀ {i j : ℕ}, i = j → T i = T j := fun e => congrArg T e
  have hserve : ∀ t, ∃ d g g', t % p = a →
      ((d = 0 ∧ g = K ∧ g' = K) ∨ (d = 0 ∧ g = K ∧ g' = K + 1) ∨ (d = 0 ∧ g = K + 1 ∧ g' = K) ∨
        (d = 1 ∧ g = K ∧ g' = K)) ∧
      T (t + d) = T (t + d + g) ∧ T (t + d + g) = T (t + d + g + g') := by
    intro t
    by_cases ht : t % p = a
    · obtain ⟨F0, F1⟩ := hFa t ht
      rcases serve h hk hN ⟨r, hr⟩ hL (by omega) hper E3 hoddc t F0 F1 with
        ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact ⟨0, K, K, fun _ => ⟨Or.inl ⟨rfl, rfl, rfl⟩,
          (cT (by omega)).trans (e1.trans (cT (by omega))),
          (cT (by omega)).trans (e2.trans (cT (by omega)))⟩⟩
      · exact ⟨0, K, K + 1, fun _ => ⟨Or.inr (Or.inl ⟨rfl, rfl, rfl⟩),
          (cT (by omega)).trans (e1.trans (cT (by omega))),
          (cT (by omega)).trans (e2.trans (cT (by omega)))⟩⟩
      · exact ⟨0, K + 1, K, fun _ => ⟨Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)),
          (cT (by omega)).trans (e1.trans (cT (by omega))),
          (cT (by omega)).trans (e2.trans (cT (by omega)))⟩⟩
      · exact ⟨1, K, K, fun _ => ⟨Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)),
          (cT (by omega)).trans (e1.trans (cT (by omega))),
          (cT (by omega)).trans (e2.trans (cT (by omega)))⟩⟩
    · exact ⟨0, 0, 0, fun h' => absurd h' ht⟩
  choose d g g' hsv using hserve
  have facts : ∀ t, t % p = a →
      d t ≤ 1 ∧ (g t = k + 1 ∨ g t = k + 2) ∧ (g' t = k + 1 ∨ g' t = k + 2) ∧
      g t + g' t ≤ 2 * K + 1 ∧ K ≤ d t + g t ∧ d t + g t ≤ K + 1 ∧ 2 * K ≤ d t + g t + g' t ∧
      d t + g t + g' t ≤ 2 * K + 1 ∧
      T (t + d t) = T (t + d t + g t) ∧ T (t + d t + g t) = T (t + d t + g t + g' t) := by
    intro t ht
    obtain ⟨hc, e1, e2⟩ := hsv t ht
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, e1, e2⟩ <;> omega
  -- the sets Pt (pair starts), B (positions of the two residues), X (serve starts), Z (serve ends)
  obtain ⟨Pt, hPt⟩ : ∃ Pt : Finset ℕ, Pt = (range N).filter (fun t => t % p = a) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Finset ℕ,
      B = (range N).filter (fun r => r % p = a ∨ r % p = (a + 1) % p) := ⟨_, rfl⟩
  have memPt : ∀ t, t ∈ Pt ↔ t < N ∧ t % p = a := by
    intro t; rw [hPt]; simp
  have memB : ∀ r, r ∈ B ↔ r < N ∧ (r % p = a ∨ r % p = (a + 1) % p) := by
    intro r; rw [hB]; simp
  have hN0 : N % p = 0 := Nat.mod_eq_zero_of_dvd hpN
  have cardRes : ∀ v, #((range N).filter (fun t => t % p = v % p)) = N / p := by
    intro v
    have h1 := Nat.count_modEq_card N hppos v
    rw [Nat.count_eq_card_filter_range, hN0] at h1
    simp only [Nat.not_lt_zero, if_false, add_zero] at h1
    rw [← h1]
    rfl
  have cardPt : #Pt = N / p := by
    rw [hPt, ← cardRes a, Nat.mod_eq_of_lt hap]
  have cardB : #B = 2 * (N / p) := by
    have hdis : Disjoint ((range N).filter (fun r => r % p = a))
        ((range N).filter (fun r => r % p = (a + 1) % p)) :=
      disjoint_filter.mpr (fun t _ h1 h2 => ha1 (h1.symm.trans h2))
    rw [hB, filter_or, card_union_of_disjoint hdis, cardRes (a + 1), ← hPt, cardPt]
    omega
  have inB : ∀ t, t % p = a → ∀ pos e m, e ≤ 1 → p ∣ m → pos = t + e + m → pos % N ∈ B := by
    intro t ht pos e m he hm hpos
    obtain ⟨j, rfl⟩ := hm
    rw [memB]
    refine ⟨Nat.mod_lt _ hNpos, ?_⟩
    have e1 : pos % N % p = (a + e) % p := by
      rw [Nat.mod_mod_of_dvd _ hpN, hpos, Nat.add_mul_mod_self_left, ← ht, Nat.mod_add_mod]
    rw [e1]
    rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl
    · left
      rw [add_zero]
      exact Nat.mod_eq_of_lt hap
    · right
      rfl
  have hpK' : p ∣ K := hKd ▸ hpK
  have hXB : ∀ t ∈ Pt, (t + d t) % N ∈ B := by
    intro t ht
    have hta := ((memPt t).mp ht).2
    obtain ⟨f1, -⟩ := facts t hta
    exact inB t hta _ (d t) 0 f1 (dvd_zero p) (by omega)
  have hYB : ∀ t ∈ Pt, (t + d t + g t) % N ∈ B := by
    intro t ht
    have hta := ((memPt t).mp ht).2
    obtain ⟨-, -, -, -, f5, f6, -⟩ := facts t hta
    exact inB t hta _ (d t + g t - K) K (by omega) hpK' (by omega)
  have hZB : ∀ t ∈ Pt, (t + d t + g t + g' t) % N ∈ B := by
    intro t ht
    have hta := ((memPt t).mp ht).2
    obtain ⟨-, -, -, -, -, -, f7, f8, -⟩ := facts t hta
    exact inB t hta _ (d t + g t + g' t - L) L (by omega) hpL (by omega)
  have xinj : ∀ t t', t ∈ Pt → t' ∈ Pt → (t + d t) % N = (t' + d t') % N → t = t' := by
    intro t t' ht ht' hm
    obtain ⟨hlt, hta⟩ := (memPt t).mp ht
    obtain ⟨hlt', hta'⟩ := (memPt t').mp ht'
    have f1 := (facts t hta).1
    have f2 := (facts t' hta').1
    have hmp : (t + d t) % N % p = (t' + d t') % N % p := by rw [hm]
    rw [Nat.mod_mod_of_dvd _ hpN, Nat.mod_mod_of_dvd _ hpN] at hmp
    have r1 : (t + d t) % p = (a + d t) % p := by rw [← hta, Nat.mod_add_mod]
    have r2 : (t' + d t') % p = (a + d t') % p := by rw [← hta', Nat.mod_add_mod]
    rw [r1, r2] at hmp
    have hdd : d t = d t' := by
      rcases (by omega : d t = 0 ∨ d t = 1) with h0 | h0 <;>
        rcases (by omega : d t' = 0 ∨ d t' = 1) with h0' | h0'
      · omega
      · exfalso
        rw [h0, h0', add_zero, Nat.mod_eq_of_lt hap] at hmp
        exact ha1 hmp
      · exfalso
        rw [h0, h0', add_zero, Nat.mod_eq_of_lt hap] at hmp
        exact ha1 hmp.symm
      · omega
    rw [hdd] at hm
    have := Nat.ModEq.add_right_cancel' (d t') hm
    rw [Nat.ModEq, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hlt'] at this
    exact this
  have zinj : ∀ t t', t ∈ Pt → t' ∈ Pt →
      (t + d t + g t + g' t) % N = (t' + d t' + g t' + g' t') % N → t = t' := by
    intro t t' ht ht' hm
    have hta := ((memPt t).mp ht).2
    have hta' := ((memPt t').mp ht').2
    obtain ⟨-, hg, hg', -, -, -, -, -, e1, e2⟩ := facts t hta
    obtain ⟨-, hgb, hgb', -, -, -, -, -, e1b, e2b⟩ := facts t' hta'
    obtain ⟨-, hy⟩ := bwd h hk hN hg' hgb' e2 e2b hm
    obtain ⟨-, hx⟩ := bwd h hk hN hg hgb e1 e1b hy
    exact xinj t t' ht ht' hx
  have disj : ∀ t t', t ∈ Pt → t' ∈ Pt →
      (t' + d t') % N = (t + d t + g t + g' t) % N → False := by
    intro t t' ht ht' hm
    have hta := ((memPt t).mp ht).2
    have hta' := ((memPt t').mp ht').2
    obtain ⟨-, hg, hg', f4, -, -, -, -, e1, e2⟩ := facts t hta
    obtain ⟨-, hgb, hgb', f4b, -, -, -, -, e1b, e2b⟩ := facts t' hta'
    have h2 : T (t' + d t') = T (t + d t + g t + g' t) := tmod h.per hm
    have c3 : T (t + d t + g t + g' t + g t') = T (t + d t) := by
      have h1 : T (t + d t + g t + g' t + g t') = T (t' + d t' + g t') :=
        tmod h.per (Nat.ModEq.add_right (g t') hm.symm)
      exact h1.trans (e1b.symm.trans (h2.trans (e2.symm.trans e1.symm)))
    have c4 : T (t + d t + g t + g' t + g t' + g' t') = T (t + d t) := by
      have h1 : T (t + d t + g t + g' t + g t' + g' t') = T (t' + d t' + g t' + g' t') :=
        tmod h.per (Nat.ModEq.add_right (g' t') (Nat.ModEq.add_right (g t') hm.symm))
      exact h1.trans (e2b.symm.trans (e1b.symm.trans (h2.trans (e2.symm.trans e1.symm))))
    exact no_five h hk hN hN6 (s := t + d t) (K := K) (c := T (t + d t)) (x0 := t + d t)
      (x1 := t + d t + g t) (x2 := t + d t + g t + g' t) (x3 := t + d t + g t + g' t + g t')
      (x4 := t + d t + g t + g' t + g t' + g' t') (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) rfl e1.symm
      (e2.symm.trans e1.symm) c3 c4
  obtain ⟨X, hX⟩ : ∃ X : Finset ℕ, X = Pt.image (fun t => (t + d t) % N) := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : Finset ℕ, Z = Pt.image (fun t => (t + d t + g t + g' t) % N) :=
    ⟨_, rfl⟩
  have cardX : #X = N / p := by
    rw [hX, card_image_of_injOn, cardPt]
    intro t ht t' ht' e
    exact xinj t t' (mem_coe.mp ht) (mem_coe.mp ht') e
  have cardZ : #Z = N / p := by
    rw [hZ, card_image_of_injOn, cardPt]
    intro t ht t' ht' e
    exact zinj t t' (mem_coe.mp ht) (mem_coe.mp ht') e
  have hXZ : Disjoint X Z := by
    rw [Finset.disjoint_left]
    intro x hxX hxZ
    rw [hX, mem_image] at hxX
    rw [hZ, mem_image] at hxZ
    obtain ⟨t', ht', rfl⟩ := hxX
    obtain ⟨t, ht, e⟩ := hxZ
    exact disj t t' ht ht' e.symm
  have hsub : X ∪ Z ⊆ B := by
    intro x hx
    rcases mem_union.mp hx with hx | hx
    · rw [hX, mem_image] at hx
      obtain ⟨t, ht, rfl⟩ := hx
      exact hXB t ht
    · rw [hZ, mem_image] at hx
      obtain ⟨t, ht, rfl⟩ := hx
      exact hZB t ht
  have hBeq : X ∪ Z = B :=
    eq_of_subset_of_card_le hsub (by rw [card_union_of_disjoint hXZ, cardX, cardZ, cardB]; omega)
  -- the matching  t ~ t'  iff  y_t ≡ x_t'
  have MG : ∀ t ∈ Pt, (∃ t' ∈ Pt, (t + d t + g t) % N = (t' + d t') % N) ∨
      (∃ t' ∈ Pt, (t' + d t' + g t') % N = (t + d t) % N) := by
    intro t ht
    have hy := hYB t ht
    rw [← hBeq] at hy
    have hta := ((memPt t).mp ht).2
    obtain ⟨-, hg, hg', -, -, -, -, -, e1, e2⟩ := facts t hta
    rcases mem_union.mp hy with hy | hy
    · rw [hX, mem_image] at hy
      obtain ⟨t', ht', e⟩ := hy
      exact Or.inl ⟨t', ht', e.symm⟩
    · rw [hZ, mem_image] at hy
      obtain ⟨t', ht', e⟩ := hy
      have hta' := ((memPt t').mp ht').2
      obtain ⟨-, hgb, hgb', -, -, -, -, -, e1b, e2b⟩ := facts t' hta'
      obtain ⟨-, hy'⟩ := bwd h hk hN hgb' hg e2b e1 e
      exact Or.inr ⟨t', ht', hy'⟩
  have MH : ∀ s0 t t', s0 ∈ Pt → t ∈ Pt → t' ∈ Pt →
      (s0 + d s0 + g s0) % N = (t + d t) % N → (t + d t + g t) % N = (t' + d t') % N → False := by
    intro s0 t t' hs ht ht' r1 r2
    have hsa := ((memPt s0).mp hs).2
    have hta := ((memPt t).mp ht).2
    obtain ⟨-, hgs, hgs', -, -, -, -, -, e1s, e2s⟩ := facts s0 hsa
    obtain ⟨-, hg, hg', -, -, -, -, -, e1, e2⟩ := facts t hta
    have hgg := fwd h hk hN hgs' hg e2s e1 r1
    have : (t' + d t') % N = (s0 + d s0 + g s0 + g' s0) % N := by
      rw [← r2, hgg]
      exact (Nat.ModEq.add_right (g t) r1).symm
    exact disj s0 t' hs ht' this
  have Sex : ∀ t, ∃ t', t ∈ Pt → (t' ∈ Pt ∧ ((t + d t + g t) % N = (t' + d t') % N ∨
      (t' + d t' + g t') % N = (t + d t) % N)) := by
    intro t
    by_cases ht : t ∈ Pt
    · rcases MG t ht with ⟨t', ht', e⟩ | ⟨t', ht', e⟩
      · exact ⟨t', fun _ => ⟨ht', Or.inl e⟩⟩
      · exact ⟨t', fun _ => ⟨ht', Or.inr e⟩⟩
    · exact ⟨0, fun h' => absurd h' ht⟩
  choose f hf using Sex
  have Suniq : ∀ t t1 t2, t ∈ Pt → t1 ∈ Pt → t2 ∈ Pt →
      ((t + d t + g t) % N = (t1 + d t1) % N ∨ (t1 + d t1 + g t1) % N = (t + d t) % N) →
      ((t + d t + g t) % N = (t2 + d t2) % N ∨ (t2 + d t2 + g t2) % N = (t + d t) % N) →
      t1 = t2 := by
    intro t t1 t2 ht ht1 ht2 r1 r2
    rcases r1 with r1 | r1 <;> rcases r2 with r2 | r2
    · exact xinj t1 t2 ht1 ht2 (r1.symm.trans r2)
    · exact (MH t2 t t1 ht2 ht ht1 r2 r1).elim
    · exact (MH t1 t t2 ht1 ht ht2 r1 r2).elim
    · have hta1 := ((memPt t1).mp ht1).2
      have hta2 := ((memPt t2).mp ht2).2
      obtain ⟨-, hg1, -, -, -, -, -, -, e11, -⟩ := facts t1 hta1
      obtain ⟨-, hg2, -, -, -, -, -, -, e12, -⟩ := facts t2 hta2
      obtain ⟨-, hx⟩ := bwd h hk hN hg1 hg2 e11 e12 (r1.trans r2.symm)
      exact xinj t1 t2 ht1 ht2 hx
  have fmem : ∀ t ∈ Pt, f t ∈ Pt := fun t ht => (hf t ht).1
  have fne : ∀ t ∈ Pt, f t ≠ t := by
    intro t ht e
    have := (hf t ht).2
    rw [e] at this
    rcases this with r1 | r1
    · exact MH t t t ht ht ht r1 r1
    · exact MH t t t ht ht ht r1 r1
  have finv : ∀ t (ht : t ∈ Pt), f (f t) = t := by
    intro t ht
    have h1 := (hf t ht).2
    have h2 := (hf (f t) (fmem t ht)).2
    exact Suniq (f t) (f (f t)) t (fmem t ht) (fmem _ (fmem t ht)) ht h2 h1.symm
  have hsum : ∑ _t ∈ Pt, (1 : ZMod 2) = 0 :=
    Finset.sum_involution (fun t _ => f t) (fun t _ => by decide) (fun t ht _ => fne t ht)
      (fun t ht => fmem t ht) (fun t ht => finv t ht)
  simp only [sum_const, nsmul_eq_mul, mul_one] at hsum
  rw [ZMod.natCast_eq_zero_iff_even, cardPt] at hsum
  exact (Nat.not_even_iff_odd.mpr hodd) hsum

end Coil

#print axioms Coil.parity_obstruction_aux
