import Ccformal.Equality

/-!
# Theorem 7 (PROOF2.md sec. 7): on the lines `l = 0 (mod 4)` the zero-slack case is impossible

`l = 4q`, `k = (l² - l - 2)/2`, `n = (3k + l + 1)/2`: there is no spread-`k` circuit code of
length `4k + 2l + 2` in `Q_n`.   (`K = k+1 = 8q² - 2q`, `N = 32q² - 2`, `n = 12q² - q - 1`.)
-/

open Finset

namespace Coil

set_option linter.unusedSectionVars false
set_option linter.deprecated false

variable {α : Type*} [Fintype α] [DecidableEq α] {k N : ℕ} {T : ℕ → α}

/-- (Y2): a window of length `k+3` contains at most one repeated coordinate -/
lemma y2 (h : IsCoilWord k N T) (hk : 1 ≤ k) (hN : 2 * k + 3 ≤ N) (t : ℕ) :
    ¬((T t = T (t + (k + 1)) ∨ T t = T (t + (k + 2))) ∧ T (t + 1) = T (t + (k + 2))) := by
  rintro ⟨h1, h2⟩
  have hN' : 2 * k + 2 ≤ N := by omega
  have a1 : 2 ≤ cnt T t (k + 3) (T t) := by
    rcases h1 with e | e
    · exact two_le_cnt (i := 0) (j := k + 1) (by omega) (by omega) (by simp) e.symm
    · exact two_le_cnt (i := 0) (j := k + 2) (by omega) (by omega) (by simp) e.symm
  have a2 : 2 ≤ cnt T t (k + 3) (T (t + 1)) :=
    two_le_cnt (i := 1) (j := k + 2) (by omega) (by omega) rfl h2.symm
  have b1 := cnt_le_two h hk hN' (t := t) (L := k + 3) (by omega) (T t)
  have b2 := cnt_le_two h hk hN' (t := t) (L := k + 3) (by omega) (T (t + 1))
  have hne : T t ≠ T (t + 1) := by
    intro e
    have := gap_ge h hk hN' (u := t) (d := 1) (by omega) e
    omega
  have hsub : ({T t, T (t + 1)} : Finset α) ⊆ ({c : α | cnt T t (k + 3) c = 2} : Finset α) := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · simp; omega
    · simp; omega
  have hP2 : 2 ≤ P T t (k + 3) := by
    calc 2 = #({T t, T (t + 1)} : Finset α) := (card_pair hne).symm
      _ ≤ _ := card_le_card hsub
  have hP1 := P_le h hk hN' (t := t) (L := k + 3) (by omega) (by omega) (by omega)
  omega

/-- five occurrences of one coordinate within one period are impossible when `N < 6(k+1)` -/
lemma no_five (h : IsCoilWord k N T) (hk : 1 ≤ k) (hN : 2 * k + 2 ≤ N) (hN6 : N < 6 * (k + 1))
    {s K : ℕ} {c : α} {x0 x1 x2 x3 x4 : ℕ}
    (h0 : s ≤ x0) (h01 : x0 < s + K) (h1 : s + K ≤ x1) (h12 : x1 < s + 2 * K)
    (h2 : s + 2 * K ≤ x2) (h23 : x2 < s + 3 * K) (h3 : s + 3 * K ≤ x3) (h34 : x3 < s + 4 * K)
    (h4 : s + 4 * K ≤ x4) (h45 : x4 < s + N)
    (e0 : T x0 = c) (e1 : T x1 = c) (e2 : T x2 = c) (e3 : T x3 = c) (e4 : T x4 = c) : False := by
  obtain ⟨p, hp⟩ := Nat.exists_eq_add_of_le (by omega : 4 * K ≤ N)
  have hsplit : cnt T s N c = cnt T s K c + cnt T (s + K) K c + cnt T (s + K + K) K c
      + cnt T (s + K + K + K) K c + cnt T (s + K + K + K + K) p c := by
    rw [show N = K + K + K + K + p by omega, cnt_add, cnt_add, cnt_add, cnt_add]
    simp only [add_assoc]
  obtain ⟨d0, rfl⟩ := Nat.exists_eq_add_of_le h0
  obtain ⟨d1, rfl⟩ := Nat.exists_eq_add_of_le (by omega : s + K ≤ x1)
  obtain ⟨d2, rfl⟩ := Nat.exists_eq_add_of_le (by omega : s + K + K ≤ x2)
  obtain ⟨d3, rfl⟩ := Nat.exists_eq_add_of_le (by omega : s + K + K + K ≤ x3)
  obtain ⟨d4, rfl⟩ := Nat.exists_eq_add_of_le (by omega : s + K + K + K + K ≤ x4)
  have c0 := one_le_cnt (T := T) (t := s) (L := K) (i := d0) (by omega) e0
  have c1 := one_le_cnt (T := T) (t := s + K) (L := K) (i := d1) (by omega) e1
  have c2 := one_le_cnt (T := T) (t := s + K + K) (L := K) (i := d2) (by omega) e2
  have c3 := one_le_cnt (T := T) (t := s + K + K + K) (L := K) (i := d3) (by omega) e3
  have c4 := one_le_cnt (T := T) (t := s + K + K + K + K) (L := p) (i := d4) (by omega) e4
  have h4' := uses_le_four h hk hN hN6 c
  rw [← cnt_period h.per s c] at h4'
  omega

set_option maxHeartbeats 4000000 in
/-- **Theorem 7**, parametrised: `Q = q²`, `k + 1 = 8Q - 2q`, `N = 32Q - 2`, `n = 12Q - q - 1`. -/
theorem thm7_aux (h : IsCoilWord k N T) (q Q : ℕ) (hq : 1 ≤ q) (hQ : Q = q * q)
    (hK : k + 1 + 2 * q = 8 * Q) (hNq : N + 2 = 32 * Q)
    (hn : Fintype.card α + q + 1 = 12 * Q) : False := by
  have hQq : q ≤ Q := by rw [hQ]; exact Nat.le_mul_self q
  have hk : 1 ≤ k := by omega
  have hN : 2 * k + 2 ≤ N := by omega
  have hN6 : N < 6 * (k + 1) := by omega
  obtain ⟨L, hL⟩ : ∃ L, L = 2 * (k + 1) := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p, p + 2 = 8 * q := ⟨8 * q - 2, by omega⟩
  have hNLp : N = L + L + p := by omega
  obtain ⟨c0, hc0, hc0q⟩ : ∃ c0, (L - k) / 2 = c0 ∧ c0 + q = 4 * Q := ⟨_, rfl, by omega⟩
  have hL3 : L ≤ 2 * (k + 1) := by omega
  -- zero slack
  have hz : ((N : ℤ) - 2 * Fintype.card α) * (4 * L - N) = 2 * N * ((L - k) / 2 : ℕ) := by
    rw [hc0]
    have z1 : (N : ℤ) = 32 * q * q - 2 := by
      have : (N : ℤ) + 2 = 32 * Q := by exact_mod_cast hNq
      rw [hQ] at this; push_cast at this; linarith
    have z2 : (Fintype.card α : ℤ) = 12 * q * q - q - 1 := by
      have : (Fintype.card α : ℤ) + q + 1 = 12 * Q := by exact_mod_cast hn
      rw [hQ] at this; push_cast at this; linarith
    have z3 : (L : ℤ) = 16 * q * q - 4 * q := by
      have : (k : ℤ) + 1 + 2 * q = 8 * Q := by exact_mod_cast hK
      rw [hQ] at this; push_cast at this
      rw [hL]; push_cast; linarith
    have z4 : (c0 : ℤ) = 4 * q * q - q := by
      have : (c0 : ℤ) + q = 4 * Q := by exact_mod_cast hc0q
      rw [hQ] at this; push_cast at this; linarith
    rw [z1, z2, z3, z4]
    ring
  obtain ⟨E1, E2, E3, E4⟩ := equality_case h hk hN hN6 (L := L) (by omega) (by omega) hL3
    (by omega) hz
  rw [hc0] at E2
  have hodd : ∀ t, oddc T t L = k + 1 := by
    intro t
    have := decomp (T := T) (t := t) (L := L) (fun c => cnt_le_two h hk hN hL3 c)
    rw [E2 t] at this
    omega
  -- the type word has period L = 2K
  have hper : ∀ t, (cnt T 0 N (T t) = 4 ↔ cnt T 0 N (T (t + L)) = 4) := by
    intro t
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
  -- ... hence period p = N - 4K and period K = q p
  have hperp : ∀ t, (cnt T 0 N (T (t + p)) = 4 ↔ cnt T 0 N (T t) = 4) := by
    intro t
    rw [hper (t + p), hper (t + p + L), show t + p + L + L = t + N by omega, h.per]
  have hmul : ∀ m t, (cnt T 0 N (T (t + m * p)) = 4 ↔ cnt T 0 N (T t) = 4) := by
    intro m
    induction m with
    | zero => intro t; simp
    | succ m ih =>
      intro t
      rw [Nat.succ_mul, ← add_assoc, hperp, ih]
  have hqp : k + 1 = q * p := by
    have e1 : q * (p + 2) = q * (8 * q) := by rw [hp]
    have e2 : q * p + 2 * q = 8 * Q := by rw [hQ]; nlinarith [e1]
    omega
  have hperK : ∀ t, (cnt T 0 N (T (t + (k + 1))) = 4 ↔ cnt T 0 N (T t) = 4) := by
    intro t
    rw [hqp]
    exact hmul q t
  -- an FF pair exists
  have hn2 : #{c : α | cnt T 0 N c = 4} = 4 * Q + q := by omega
  obtain ⟨s, Fs, Fs1⟩ : ∃ s, cnt T 0 N (T s) = 4 ∧ cnt T 0 N (T (s + 1)) = 4 := by
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
    have hΦsum : ∑ t ∈ range N, Φ t = 4 * (4 * Q + q) := by
      have e1 : ∀ t ∈ range N, Φ t
          = ∑ c, (if T t = c then (if cnt T 0 N c = 4 then 1 else 0) else 0) := by
        intro t _
        rw [sum_ite_eq]
        simp [Φ]
      rw [sum_congr rfl e1, sum_comm, sum_congr rfl (fun c _ => hΦc c), ← mul_sum, ← card_filter,
        hn2]
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
  -- (C1): every FF pair starts a triple
  have c1 : ∀ u u1 v v1 w w1 : ℕ, u1 = u + 1 → v = u + (k + 1) → v1 = u + (k + 1) + 1 →
      w = u + L → w1 = u + L + 1 → cnt T 0 N (T u) = 4 → cnt T 0 N (T u1) = 4 →
      (T u = T v ∧ T v = T w) ∨ (T u = T v ∧ T v = T w1) ∨ (T u = T v1 ∧ T v1 = T w1) ∨
        (T u1 = T v1 ∧ T v1 = T w1) := by
    intro u u1 v v1 w w1 hu1 hv hv1 hw hw1 Fu Fu1
    subst hu1 hv hv1 hw hw1
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
  -- the chase (Step D)
  obtain ⟨K, hKd⟩ : ∃ K, K = k + 1 := ⟨_, rfl⟩
  have FK : cnt T 0 N (T (s + K)) = 4 := by rw [hKd]; exact (hperK s).mpr Fs
  have FK1 : cnt T 0 N (T (s + K + 1)) = 4 := by
    rw [hKd, show s + (k + 1) + 1 = s + 1 + (k + 1) by omega]; exact (hperK (s + 1)).mpr Fs1
  have F2K : cnt T 0 N (T (s + 2 * K)) = 4 := by
    rw [show s + 2 * K = s + L by omega]; exact (hper s).mp Fs
  have F2K1 : cnt T 0 N (T (s + 2 * K + 1)) = 4 := by
    rw [show s + 2 * K + 1 = s + 1 + L by omega]; exact (hper (s + 1)).mp Fs1
  have C0 := c1 s (s + 1) (s + K) (s + K + 1) (s + 2 * K) (s + 2 * K + 1) rfl (by omega)
    (by omega) (by omega) (by omega) Fs Fs1
  have C1 := c1 (s + K) (s + K + 1) (s + 2 * K) (s + 2 * K + 1) (s + 3 * K) (s + 3 * K + 1) rfl
    (by omega) (by omega) (by omega) (by omega) FK FK1
  have C2 := c1 (s + 2 * K) (s + 2 * K + 1) (s + 3 * K) (s + 3 * K + 1) (s + 4 * K)
    (s + 4 * K + 1) rfl (by omega) (by omega) (by omega) (by omega) F2K F2K1
  have Y1 := y2 h hk (by omega) (s + K)
  have Y2 := y2 h hk (by omega) (s + 2 * K)
  rw [show s + K + (k + 1) = s + 2 * K by omega, show s + K + (k + 2) = s + 2 * K + 1 by omega]
    at Y1
  rw [show s + 2 * K + (k + 1) = s + 3 * K by omega,
    show s + 2 * K + (k + 2) = s + 3 * K + 1 by omega] at Y2
  have adj : ∀ u, T u ≠ T (u + 1) := by
    intro u e
    have := gap_ge h hk hN (u := u) (d := 1) (by omega) e
    omega
  have n5 : ∀ (x0 x1 x2 x3 x4 : ℕ), (x0 = s ∨ x0 = s + 1) → (x1 = s + K ∨ x1 = s + K + 1) →
      (x2 = s + 2 * K ∨ x2 = s + 2 * K + 1) → (x3 = s + 3 * K ∨ x3 = s + 3 * K + 1) →
      (x4 = s + 4 * K ∨ x4 = s + 4 * K + 1) →
      T x0 = T x1 → T x1 = T x2 → T x2 = T x3 → T x3 = T x4 → False := by
    intro x0 x1 x2 x3 x4 h0 h1 h2 h3 h4 e1 e2 e3 e4
    exact no_five h hk hN hN6 (s := s) (K := K) (c := T x0) (x0 := x0) (x1 := x1) (x2 := x2)
      (x3 := x3) (x4 := x4) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) rfl e1.symm (e1.trans e2).symm
      ((e1.trans e2).trans e3).symm (((e1.trans e2).trans e3).trans e4).symm
  have A0 := adj s
  have A1 := adj (s + K)
  have A2 := adj (s + 2 * K)
  have A3 := adj (s + 3 * K)
  have A4 := adj (s + 4 * K)
  have n5_00000 := n5 (s) (s + K) (s + 2 * K) (s + 3 * K) (s + 4 * K) (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
  have n5_00001 := n5 (s) (s + K) (s + 2 * K) (s + 3 * K) (s + 4 * K + 1) (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) (Or.inr rfl)
  have n5_00010 := n5 (s) (s + K) (s + 2 * K) (s + 3 * K + 1) (s + 4 * K) (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) (Or.inr rfl) (Or.inl rfl)
  have n5_00011 := n5 (s) (s + K) (s + 2 * K) (s + 3 * K + 1) (s + 4 * K + 1) (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) (Or.inr rfl) (Or.inr rfl)
  have n5_00100 := n5 (s) (s + K) (s + 2 * K + 1) (s + 3 * K) (s + 4 * K) (Or.inl rfl) (Or.inl rfl) (Or.inr rfl) (Or.inl rfl) (Or.inl rfl)
  have n5_00101 := n5 (s) (s + K) (s + 2 * K + 1) (s + 3 * K) (s + 4 * K + 1) (Or.inl rfl) (Or.inl rfl) (Or.inr rfl) (Or.inl rfl) (Or.inr rfl)
  have n5_00110 := n5 (s) (s + K) (s + 2 * K + 1) (s + 3 * K + 1) (s + 4 * K) (Or.inl rfl) (Or.inl rfl) (Or.inr rfl) (Or.inr rfl) (Or.inl rfl)
  have n5_00111 := n5 (s) (s + K) (s + 2 * K + 1) (s + 3 * K + 1) (s + 4 * K + 1) (Or.inl rfl) (Or.inl rfl) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl)
  have n5_01000 := n5 (s) (s + K + 1) (s + 2 * K) (s + 3 * K) (s + 4 * K) (Or.inl rfl) (Or.inr rfl) (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
  have n5_01001 := n5 (s) (s + K + 1) (s + 2 * K) (s + 3 * K) (s + 4 * K + 1) (Or.inl rfl) (Or.inr rfl) (Or.inl rfl) (Or.inl rfl) (Or.inr rfl)
  have n5_01010 := n5 (s) (s + K + 1) (s + 2 * K) (s + 3 * K + 1) (s + 4 * K) (Or.inl rfl) (Or.inr rfl) (Or.inl rfl) (Or.inr rfl) (Or.inl rfl)
  have n5_01011 := n5 (s) (s + K + 1) (s + 2 * K) (s + 3 * K + 1) (s + 4 * K + 1) (Or.inl rfl) (Or.inr rfl) (Or.inl rfl) (Or.inr rfl) (Or.inr rfl)
  have n5_01100 := n5 (s) (s + K + 1) (s + 2 * K + 1) (s + 3 * K) (s + 4 * K) (Or.inl rfl) (Or.inr rfl) (Or.inr rfl) (Or.inl rfl) (Or.inl rfl)
  have n5_01101 := n5 (s) (s + K + 1) (s + 2 * K + 1) (s + 3 * K) (s + 4 * K + 1) (Or.inl rfl) (Or.inr rfl) (Or.inr rfl) (Or.inl rfl) (Or.inr rfl)
  have n5_01110 := n5 (s) (s + K + 1) (s + 2 * K + 1) (s + 3 * K + 1) (s + 4 * K) (Or.inl rfl) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) (Or.inl rfl)
  have n5_01111 := n5 (s) (s + K + 1) (s + 2 * K + 1) (s + 3 * K + 1) (s + 4 * K + 1) (Or.inl rfl) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl)
  have n5_10000 := n5 (s + 1) (s + K) (s + 2 * K) (s + 3 * K) (s + 4 * K) (Or.inr rfl) (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
  have n5_10001 := n5 (s + 1) (s + K) (s + 2 * K) (s + 3 * K) (s + 4 * K + 1) (Or.inr rfl) (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) (Or.inr rfl)
  have n5_10010 := n5 (s + 1) (s + K) (s + 2 * K) (s + 3 * K + 1) (s + 4 * K) (Or.inr rfl) (Or.inl rfl) (Or.inl rfl) (Or.inr rfl) (Or.inl rfl)
  have n5_10011 := n5 (s + 1) (s + K) (s + 2 * K) (s + 3 * K + 1) (s + 4 * K + 1) (Or.inr rfl) (Or.inl rfl) (Or.inl rfl) (Or.inr rfl) (Or.inr rfl)
  have n5_10100 := n5 (s + 1) (s + K) (s + 2 * K + 1) (s + 3 * K) (s + 4 * K) (Or.inr rfl) (Or.inl rfl) (Or.inr rfl) (Or.inl rfl) (Or.inl rfl)
  have n5_10101 := n5 (s + 1) (s + K) (s + 2 * K + 1) (s + 3 * K) (s + 4 * K + 1) (Or.inr rfl) (Or.inl rfl) (Or.inr rfl) (Or.inl rfl) (Or.inr rfl)
  have n5_10110 := n5 (s + 1) (s + K) (s + 2 * K + 1) (s + 3 * K + 1) (s + 4 * K) (Or.inr rfl) (Or.inl rfl) (Or.inr rfl) (Or.inr rfl) (Or.inl rfl)
  have n5_10111 := n5 (s + 1) (s + K) (s + 2 * K + 1) (s + 3 * K + 1) (s + 4 * K + 1) (Or.inr rfl) (Or.inl rfl) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl)
  have n5_11000 := n5 (s + 1) (s + K + 1) (s + 2 * K) (s + 3 * K) (s + 4 * K) (Or.inr rfl) (Or.inr rfl) (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
  have n5_11001 := n5 (s + 1) (s + K + 1) (s + 2 * K) (s + 3 * K) (s + 4 * K + 1) (Or.inr rfl) (Or.inr rfl) (Or.inl rfl) (Or.inl rfl) (Or.inr rfl)
  have n5_11010 := n5 (s + 1) (s + K + 1) (s + 2 * K) (s + 3 * K + 1) (s + 4 * K) (Or.inr rfl) (Or.inr rfl) (Or.inl rfl) (Or.inr rfl) (Or.inl rfl)
  have n5_11011 := n5 (s + 1) (s + K + 1) (s + 2 * K) (s + 3 * K + 1) (s + 4 * K + 1) (Or.inr rfl) (Or.inr rfl) (Or.inl rfl) (Or.inr rfl) (Or.inr rfl)
  have n5_11100 := n5 (s + 1) (s + K + 1) (s + 2 * K + 1) (s + 3 * K) (s + 4 * K) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) (Or.inl rfl) (Or.inl rfl)
  have n5_11101 := n5 (s + 1) (s + K + 1) (s + 2 * K + 1) (s + 3 * K) (s + 4 * K + 1) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) (Or.inl rfl) (Or.inr rfl)
  have n5_11110 := n5 (s + 1) (s + K + 1) (s + 2 * K + 1) (s + 3 * K + 1) (s + 4 * K) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) (Or.inl rfl)
  have n5_11111 := n5 (s + 1) (s + K + 1) (s + 2 * K + 1) (s + 3 * K + 1) (s + 4 * K + 1) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl)
  clear n5 adj c1 hper hperp hmul hperK E1 E2 E3 E4 hodd hz FK FK1 F2K F2K1 Fs Fs1
  generalize T (s + 4 * K + 1) = e1 at *
  generalize T (s + 4 * K) = e0 at *
  generalize T (s + 3 * K + 1) = d1 at *
  generalize T (s + 3 * K) = d0 at *
  generalize T (s + 2 * K + 1) = c1' at *
  generalize T (s + 2 * K) = c0' at *
  generalize T (s + K + 1) = b1 at *
  generalize T (s + K) = b0 at *
  generalize T (s + 1) = a1 at *
  generalize T s = a0 at *
  grind

/-- **Theorem 7.**  `l = 4q ≥ 4`, `k = (l² - l - 2)/2 = 8q² - 2q - 1`, `n = (3k + l + 1)/2 = 12q² - q - 1`:
no spread-`k` circuit code of length `4k + 2l + 2 = 32q² - 2` exists in `Q_n`. -/
theorem thm7 (q : ℕ) (hq : 1 ≤ q) (v : ℕ → Fin (12 * q * q - q - 1) → Bool) :
    ¬ IsCoil (8 * q * q - 2 * q - 1) (32 * q * q - 2) v := by
  intro h
  obtain ⟨T, hT, _⟩ := h.exists_word
  have hQq : q ≤ q * q := Nat.le_mul_self q
  have e1 : 8 * q * q = 8 * (q * q) := by ring
  have e2 : 32 * q * q = 32 * (q * q) := by ring
  have e3 : 12 * q * q = 12 * (q * q) := by ring
  refine thm7_aux hT q (q * q) hq rfl ?_ ?_ ?_
  · omega
  · omega
  · rw [Fintype.card_fin]; omega

theorem thm7_bound_aux (h : IsCoilWord k N T) (q Q : ℕ) (hq : 2 ≤ q) (hQ : Q = q * q)
    (hK : k + 1 + 2 * q = 8 * Q) (hn : Fintype.card α + q + 1 = 12 * Q) : N + 4 ≤ 32 * Q := by
  by_contra hcon
  rw [not_le] at hcon
  have hQq : 2 * q ≤ Q := by rw [hQ]; exact Nat.mul_le_mul_right q hq
  obtain ⟨m, hm⟩ := even_length h
  by_cases hNeq : N + 2 = 32 * Q
  · exact thm7_aux h q Q (by omega) hQ hK hNeq hn
  · have hNlo : 32 * Q ≤ N := by omega
    have hN5 : N < 5 * k + 4 := by
      by_contra h5
      have := no_long h (by omega) (by omega)
      omega
    have C := chord_inequality h (by omega) (by omega) (by omega) (L := 2 * (k + 1)) (by omega)
      (by omega) (by omega) (by omega)
    have hc0 : (2 * (k + 1) - k) / 2 + q = 4 * Q := by omega
    obtain ⟨c0, hc0'⟩ : ∃ c0, c0 = (2 * (k + 1) - k) / 2 := ⟨_, rfl⟩
    rw [← hc0'] at C hc0
    obtain ⟨e, he⟩ : ∃ e, N + 2 = 32 * Q + e := ⟨N + 2 - 32 * Q, by omega⟩
    have z1 : (N : ℤ) = 32 * q * q - 2 + e := by
      have : (N : ℤ) + 2 = 32 * Q + e := by exact_mod_cast he
      rw [hQ] at this; push_cast at this; linarith
    have z2 : (Fintype.card α : ℤ) = 12 * q * q - q - 1 := by
      have : (Fintype.card α : ℤ) + q + 1 = 12 * Q := by exact_mod_cast hn
      rw [hQ] at this; push_cast at this; linarith
    have z3 : (k : ℤ) = 8 * q * q - 2 * q - 1 := by
      have : (k : ℤ) + 1 + 2 * q = 8 * Q := by exact_mod_cast hK
      rw [hQ] at this; push_cast at this; linarith
    have z4 : (c0 : ℤ) = 4 * q * q - q := by
      have : (c0 : ℤ) + q = 4 * Q := by exact_mod_cast hc0
      rw [hQ] at this; push_cast at this; linarith
    have he1 : (0 : ℤ) < e := by exact_mod_cast (by omega : 0 < e)
    have he2 : (0 : ℤ) < 16 * q * q - 16 * q + 2 - e := by
      have : e + 16 * q < 16 * Q + 2 := by omega
      have : (e : ℤ) + 16 * q < 16 * Q + 2 := by exact_mod_cast this
      rw [hQ] at this; push_cast at this; linarith
    push_cast at C
    rw [z1, z2, z3, z4] at C
    nlinarith [mul_pos he1 he2]

/-- **Corollary** (`l = 4q ≥ 8`): `K(n,k) ≤ 4k + 2l = 32q² - 4` at `k = (l² - l - 2)/2`, the largest `k`
not covered by the Main Theorem on the line `l`.  (Byrnes' codes attain `4k + 2l`.) -/
theorem thm7_bound (q : ℕ) (hq : 2 ≤ q) (N : ℕ) (v : ℕ → Fin (12 * q * q - q - 1) → Bool)
    (h : IsCoil (8 * q * q - 2 * q - 1) N v) : N ≤ 32 * q * q - 4 := by
  obtain ⟨T, hT, _⟩ := h.exists_word
  have hQq : 2 * q ≤ q * q := Nat.mul_le_mul_right q hq
  have e1 : 8 * q * q = 8 * (q * q) := by ring
  have e2 : 32 * q * q = 32 * (q * q) := by ring
  have e3 : 12 * q * q = 12 * (q * q) := by ring
  have := thm7_bound_aux hT q (q * q) hq rfl (by omega) (by rw [Fintype.card_fin]; omega)
  omega

end Coil

#print axioms Coil.thm7
#print axioms Coil.thm7_bound
