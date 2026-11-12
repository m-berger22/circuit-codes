import Ccformal.Cor25

/-!
# Theorem 26 (PROOF10.md sec. 7): odd lines, the bound of Lemma 1 at `L0 = 2K - 1 = 2k + 1`

`k` even.  If Lemma 1 holds with equality at `L0 = 2k+1` then the number of dot positions per period
`p = gcd(2k+1, N)` of the type word is even (`dots_per_period_even`); in particular there is no code
when `N = 2 (mod 4)` (`thm26`: excess `e = 0 (mod 4)` never attains the bound on odd lines).
-/

open Finset

namespace Coil

set_option linter.unusedSectionVars false
set_option linter.deprecated false

variable {α : Type*} [Fintype α] [DecidableEq α] {k N : ℕ} {T : ℕ → α}

/-- the number of F positions in a period is four times the number of F coordinates -/
lemma F_positions (h : IsCoilWord k N T) :
    ∑ t ∈ range N, (if cnt T 0 N (T t) = 4 then 1 else 0) = 4 * #{c : α | cnt T 0 N c = 4} := by
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
  exact hΦsum

/-- a predicate with periods `L` and `N` has period `gcd L N` -/
lemma periodic_gcd (φ : ℕ → Prop) (L N : ℕ) (hL : ∀ t, φ t ↔ φ (t + L))
    (hN : ∀ t, φ (t + N) ↔ φ t) (hlt : Nat.gcd L N < N) (t : ℕ) :
    φ t ↔ φ (t % Nat.gcd L N) := by
  have hmulL : ∀ m t, (φ (t + m * L) ↔ φ t) := by
    intro m
    induction m with
    | zero => intro t; simp
    | succ m ih =>
      intro t
      rw [Nat.succ_mul, ← add_assoc, ← hL (t + m * L), ih]
  have hmulN : ∀ m t, (φ (t + m * N) ↔ φ t) := by
    intro m
    induction m with
    | zero => intro t; simp
    | succ m ih =>
      intro t
      rw [Nat.succ_mul, ← add_assoc, hN, ih]
  obtain ⟨p, hp⟩ : ∃ p, p = Nat.gcd L N := ⟨_, rfl⟩
  rw [← hp] at hlt ⊢
  have hperp : ∀ t, (φ (t + p) ↔ φ t) := by
    intro t
    obtain ⟨m, _, hm⟩ := Nat.exists_mul_mod_eq_gcd (hp ▸ hlt)
    rw [← hp] at hm
    have e : N * (L * m / N) + p = L * m := by
      rw [← hm]
      exact Nat.div_add_mod _ _
    have e2 : t + m * L = t + p + (L * m / N) * N := by
      rw [mul_comm m L, mul_comm (L * m / N) N]
      omega
    rw [← hmulL m t, e2, hmulN]
  have hmulp : ∀ m t, (φ (t + m * p) ↔ φ t) := by
    intro m
    induction m with
    | zero => intro t; simp
    | succ m ih =>
      intro t
      rw [Nat.succ_mul, ← add_assoc, hperp, ih]
  have := hmulp (t / p) (t % p)
  rw [show t % p + t / p * p = t by rw [mul_comm]; exact Nat.mod_add_div t p] at this
  exact this

lemma sum_periodic (f : ℕ → ℕ) (p : ℕ) (hf : ∀ t, f (t + p) = f t) (m : ℕ) :
    ∑ t ∈ range (p * m), f t = m * ∑ t ∈ range p, f t := by
  have hmul : ∀ j x, f (x + j * p) = f x := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih => intro x; rw [Nat.succ_mul, ← add_assoc, hf, ih]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, sum_range_add, ih, Nat.succ_mul]
    congr 1
    apply sum_congr rfl
    intro x _
    rw [show p * m + x = x + m * p by rw [mul_comm]; omega, hmul]

/-- (Z5) on odd lines: an FF pair at `u` forces the triple `u, u+K, u+2K` -/
lemma serve_odd (h : IsCoilWord k N T) (hk : 1 ≤ k) (hN : 2 * k + 2 ≤ N) (hke : Even k)
    {L : ℕ} (hL : L = 2 * k + 1) (hN3 : L + 2 + k ≤ N)
    (hper : ∀ t, (cnt T 0 N (T t) = 4 ↔ cnt T 0 N (T (t + L)) = 4))
    (E3 : ∀ c, cnt T 0 N c = 4 → ∀ t, 1 ≤ cnt T t L c)
    (hodd : ∀ t, oddc T t L = k + 1) (u : ℕ)
    (Fu : cnt T 0 N (T u) = 4) (Fu1 : cnt T 0 N (T (u + 1)) = 4) :
    T u = T (u + (k + 1)) ∧ T (u + (k + 1)) = T (u + L + 1) := by
    obtain ⟨r, hr⟩ := hke
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
    · exfalso
      obtain ⟨i, j, hij, hj, ei, ej⟩ := exists_two_of_cnt h2
      have g1 := gap_ge h hk hN (u := u + i) (d := j - i) (by omega)
        (by rw [show u + i + (j - i) = u + j by omega]; exact ei.trans ej.symm)
      have g2 := gap_ge h hk hN (u := u + j) (d := L - j) (by omega)
        (by rw [show u + j + (L - j) = u + L by omega, ← ha]; exact ej)
      omega
    · obtain ⟨i, j, hij, hj, ei, ej⟩ := exists_two_of_cnt h2
      have g1 := gap_ge h hk hN (u := u + i) (d := j - i) (by omega)
        (by rw [show u + i + (j - i) = u + j by omega]; exact ei.trans ej.symm)
      have g2 := gap_ge h hk hN (u := u + j) (d := L + 1 - j) (by omega)
        (by rw [show u + j + (L + 1 - j) = u + L + 1 by omega, ← hb]; exact ej)
      obtain ⟨rfl, rfl⟩ : i = 0 ∧ j = k + 1 := by omega
      rw [add_zero] at ei
      exact ⟨ei.trans ej.symm, ej.trans hb⟩

/-- (Z6) on odd lines: no two adjacent dot positions -/
lemma no_two_dots (h : IsCoilWord k N T) (hk : 1 ≤ k) (hN : 2 * k + 2 ≤ N) (hke : Even k)
    {L c0 : ℕ} (hL : L = 2 * k + 1) (hL4 : L + k ≤ N) (hc0 : 2 * c0 = k)
    (E2 : ∀ t, P T t L = c0) (E4 : ∀ c, cnt T 0 N c ≠ 4 → ∀ t, cnt T t L c ≠ 2) (s : ℕ) :
    cnt T 0 N (T s) = 4 ∨ cnt T 0 N (T (s + 1)) = 4 := by
  obtain ⟨t, ht⟩ : ∃ t, t + (L - 2) = s + N := ⟨s + N - (L - 2), by omega⟩
  have h1 := P_le h hk hN (t := t) (L := L - 2) (by omega) (by omega) (by omega)
  have h2 := E2 t
  have hex : ∃ x, cnt T t L x = 2 ∧ cnt T t (L - 2) x ≠ 2 := by
    by_contra hcon
    have hsub : ({c : α | cnt T t L c = 2} : Finset α) ⊆ ({c : α | cnt T t (L - 2) c = 2} : Finset α) := by
      intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx ⊢
      by_contra hne
      exact hcon ⟨x, hx, hne⟩
    have := card_le_card hsub
    rw [P] at h1 h2
    omega
  obtain ⟨x, hx2, hxne⟩ := hex
  have hF : cnt T 0 N x = 4 := by
    by_contra hx
    exact E4 x hx t hx2
  have e : cnt T t L x = cnt T t (L - 2) x + (if T (t + (L - 2)) = x then 1 else 0)
      + (if T (t + (L - 2) + 1) = x then 1 else 0) := by
    have a1 := cnt_add T t (L - 2) 1 x
    have a2 := cnt_add T t (L - 2 + 1) 1 x
    rw [cnt_one] at a1 a2
    rw [show L - 2 + 1 + 1 = L by omega, show t + (L - 2 + 1) = t + (L - 2) + 1 by omega] at a2
    omega
  rw [ht, h.per, show s + N + 1 = s + 1 + N by omega, h.per] at e
  by_cases e1 : T s = x
  · left; rw [e1]; exact hF
  · by_cases e2 : T (s + 1) = x
    · right; rw [e2]; exact hF
    · exfalso
      rw [if_neg e1, if_neg e2] at e
      omega

set_option maxHeartbeats 2000000 in
/-- In the equality case of Lemma 1 at `L = 2k+1` (`k` even) the type word has period
`p = gcd(L, N)` and the number of dot positions per period is EVEN. -/
theorem dots_per_period_even (h : IsCoilWord k N T) (hk : 1 ≤ k) (hke : Even k)
    {L : ℕ} (hL : L = 2 * k + 1) (hN3 : 3 * (k + 1) ≤ N) (hN6 : N < 6 * (k + 1))
    (hN4 : N < 4 * L)
    (hz : ((N : ℤ) - 2 * Fintype.card α) * (4 * L - N) = 2 * N * ((L - k) / 2 : ℕ)) :
    Even (#((range (Nat.gcd L N)).filter (fun t => ¬ cnt T 0 N (T t) = 4))) ∧
    2 * #{c : α | cnt T 0 N c = 4} + 2 * Fintype.card α = N ∧
    (∀ t, (cnt T 0 N (T t) = 4 ↔ cnt T 0 N (T (t % Nat.gcd L N)) = 4)) := by
  obtain ⟨r, hr⟩ := hke
  have hN : 2 * k + 2 ≤ N := by omega
  have hL3 : L ≤ 2 * (k + 1) := by omega
  obtain ⟨E1, E2, E3, E4⟩ := equality_case h hk hN hN6 (L := L) (by omega) hN4 hL3
    (by omega) hz
  have hc0 : (L - k) / 2 = r := by omega
  rw [hc0] at E2
  have hoddc : ∀ t, oddc T t L = k + 1 := by
    intro t
    have := decomp (T := T) (t := t) (L := L) (fun c => cnt_le_two h hk hN hL3 c)
    rw [E2 t] at this
    omega
  have hper := typeword_period h hk hN hL3 E2 E3 E4
  have hb := no_two_dots h hk hN ⟨r, hr⟩ hL (by omega) (by omega : 2 * r = k) E2 E4
  have ha : ∀ u, cnt T 0 N (T u) = 4 → cnt T 0 N (T (u + 1)) = 4 →
      cnt T 0 N (T (u + (k + 1))) = 4 := by
    intro u Fu Fu1
    have := (serve_odd h hk hN ⟨r, hr⟩ hL (by omega) hper E3 hoddc u Fu Fu1).1
    rw [← this]
    exact Fu
  obtain ⟨p, hp⟩ : ∃ p, p = Nat.gcd L N := ⟨_, rfl⟩
  have hNpos : 0 < N := by omega
  have hpN : p ∣ N := hp ▸ Nat.gcd_dvd_right L N
  have hpL : p ∣ L := hp ▸ Nat.gcd_dvd_left L N
  have hppos : 0 < p := Nat.pos_of_dvd_of_pos hpN hNpos
  have hlt : Nat.gcd L N < N := by
    have : Nat.gcd L N ≤ L := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left L N)
    omega
  have hmodp : ∀ t, (cnt T 0 N (T t) = 4 ↔ cnt T 0 N (T (t % p)) = 4) := by
    intro t
    rw [hp]
    exact periodic_gcd (fun t => cnt T 0 N (T t) = 4) L N hper
      (fun t => by show (cnt T 0 N (T (t + N)) = 4 ↔ cnt T 0 N (T t) = 4); rw [h.per]) hlt t
  rw [← hp]
  refine ⟨?_, E1, hmodp⟩
  have hLmod : ∀ t, (t + L) % p = t % p := by
    intro t
    obtain ⟨j, hj⟩ := hpL
    rw [hj, Nat.add_mul_mod_self_left]
  have nb : ∀ t, ¬ cnt T 0 N (T t) = 4 →
      ¬ (cnt T 0 N (T (t + k)) = 4 ∧ cnt T 0 N (T (t + k + 1)) = 4) := by
    intro t ht ⟨h1, h2⟩
    have := ha (t + k) h1 h2
    rw [show t + k + (k + 1) = t + L by omega, ← hper t] at this
    exact ht this
  obtain ⟨Zr, hZr⟩ : ∃ Zr : Finset ℕ,
      Zr = (range p).filter (fun t => ¬ cnt T 0 N (T t) = 4) := ⟨_, rfl⟩
  rw [← hZr]
  have memZr : ∀ t, t ∈ Zr ↔ t < p ∧ ¬ cnt T 0 N (T t) = 4 := by
    intro t; rw [hZr]; simp
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℕ, ∀ t, f t
      = if cnt T 0 N (T (t + k)) = 4 then (t + k + 1) % p else (t + k) % p := ⟨_, fun _ => rfl⟩
  have fmem : ∀ t ∈ Zr, f t ∈ Zr := by
    intro t ht
    obtain ⟨hlt', hd⟩ := (memZr t).mp ht
    rw [memZr, hf]
    by_cases hc : cnt T 0 N (T (t + k)) = 4
    · rw [if_pos hc]
      refine ⟨Nat.mod_lt _ hppos, ?_⟩
      rw [← hmodp]
      intro h2
      exact nb t hd ⟨hc, h2⟩
    · rw [if_neg hc]
      refine ⟨Nat.mod_lt _ hppos, ?_⟩
      rw [← hmodp]
      exact hc
  have finv : ∀ t (ht : t ∈ Zr), f (f t) = t := by
    intro t ht
    obtain ⟨hlt', hd⟩ := (memZr t).mp ht
    by_cases hc : cnt T 0 N (T (t + k)) = 4
    · have e0 : f t = (t + k + 1) % p := by rw [hf, if_pos hc]
      have e1 : ((t + k + 1) % p + k) % p = t := by
        rw [Nat.mod_add_mod, show t + k + 1 + k = t + L by omega, hLmod, Nat.mod_eq_of_lt hlt']
      have e2 : ¬ cnt T 0 N (T ((t + k + 1) % p + k)) = 4 := by
        rw [hmodp, e1]
        exact hd
      rw [e0, hf, if_neg e2, e1]
    · have e0 : f t = (t + k) % p := by rw [hf, if_neg hc]
      have e1 : ((t + k) % p + k + 1) % p = t := by
        rw [add_assoc, Nat.mod_add_mod, show t + k + (k + 1) = t + L by omega, hLmod,
          Nat.mod_eq_of_lt hlt']
      have e2 : cnt T 0 N (T ((t + k) % p + k)) = 4 := by
        rw [hmodp, Nat.mod_add_mod, ← hmodp]
        rcases hb (t + k + k) with h1 | h1
        · exact h1
        · exfalso
          rw [show t + k + k + 1 = t + L by omega, ← hper t] at h1
          exact hd h1
      rw [e0, hf, if_pos e2, e1]
  have fne : ∀ t ∈ Zr, f t ≠ t := by
    intro t ht e
    obtain ⟨hlt', hd⟩ := (memZr t).mp ht
    have hp1 : p = 1 := by
      rw [hf] at e
      by_cases hc : cnt T 0 N (T (t + k)) = 4
      · rw [if_pos hc] at e
        have h1 : (t + (k + 1)) % p = (t + 0) % p := by
          rw [add_zero, ← add_assoc, e, Nat.mod_eq_of_lt hlt']
        have h2 : p ∣ k + 1 := (Nat.modEq_zero_iff_dvd).mp (Nat.ModEq.add_left_cancel' t h1)
        have h3 : p ∣ 2 * (k + 1) - L := Nat.dvd_sub (dvd_mul_of_dvd_right h2 2) hpL
        rw [show 2 * (k + 1) - L = 1 by omega] at h3
        exact Nat.dvd_one.mp h3
      · rw [if_neg hc] at e
        have h1 : (t + k) % p = (t + 0) % p := by
          rw [add_zero, e, Nat.mod_eq_of_lt hlt']
        have h2 : p ∣ k := (Nat.modEq_zero_iff_dvd).mp (Nat.ModEq.add_left_cancel' t h1)
        have h3 : p ∣ L - 2 * k := Nat.dvd_sub hpL (dvd_mul_of_dvd_right h2 2)
        rw [show L - 2 * k = 1 by omega] at h3
        exact Nat.dvd_one.mp h3
    have h0 : ¬ cnt T 0 N (T 0) = 4 := by
      have := hmodp t
      rw [hp1, Nat.mod_one] at this
      exact fun h' => hd (this.mpr h')
    have h1 : ¬ cnt T 0 N (T 1) = 4 := by
      have := hmodp 1
      rw [hp1, Nat.mod_one] at this
      exact fun h' => h0 (this.mp h')
    rcases hb 0 with h' | h'
    · exact h0 h'
    · exact h1 h'
  have hsum : ∑ _t ∈ Zr, (1 : ZMod 2) = 0 :=
    Finset.sum_involution (fun t _ => f t) (fun t _ => by decide) (fun t ht _ => fne t ht)
      (fun t ht => fmem t ht) (fun t ht => finv t ht)
  simp only [sum_const, nsmul_eq_mul, mul_one] at hsum
  exact ZMod.natCast_eq_zero_iff_even.mp hsum

/-- **Necessary condition on odd lines** (general form of Theorem 26): `k` even, zero slack in
Lemma 1 at `L = 2k+1`, `p = gcd(L, N)`: the number `4n - N` of dot positions is an EVEN multiple
of `N / p`. -/
theorem odd_line_condition (h : IsCoilWord k N T) (hk : 1 ≤ k) (hke : Even k)
    {L : ℕ} (hL : L = 2 * k + 1) (hN3 : 3 * (k + 1) ≤ N) (hN6 : N < 6 * (k + 1))
    (hN4 : N < 4 * L)
    (hz : ((N : ℤ) - 2 * Fintype.card α) * (4 * L - N) = 2 * N * ((L - k) / 2 : ℕ)) :
    ∃ m, 4 * Fintype.card α = N + (N / Nat.gcd L N) * (2 * m) := by
  obtain ⟨hev, E1, hmodp⟩ := dots_per_period_even h hk hke hL hN3 hN6 hN4 hz
  obtain ⟨p, hp⟩ : ∃ p, p = Nat.gcd L N := ⟨_, rfl⟩
  rw [← hp] at hev hmodp ⊢
  have hpN : p ∣ N := hp ▸ Nat.gcd_dvd_right L N
  have hppos : 0 < p := Nat.pos_of_dvd_of_pos hpN (by omega)
  obtain ⟨q, hq⟩ := hpN
  obtain ⟨m, hm⟩ := hev
  obtain ⟨gd, hgd⟩ : ∃ gd : ℕ → ℕ, ∀ t, gd t = if ¬ cnt T 0 N (T t) = 4 then 1 else 0 :=
    ⟨_, fun _ => rfl⟩
  have hgper : ∀ t, gd (t + p) = gd t := by
    intro t
    have e1 := hmodp (t + p)
    rw [Nat.add_mod_right, ← hmodp t] at e1
    rw [hgd, hgd]
    by_cases hc : cnt T 0 N (T t) = 4
    · rw [if_neg (not_not.mpr hc), if_neg (not_not.mpr (e1.mpr hc))]
    · rw [if_pos hc, if_pos (fun h' => hc (e1.mp h'))]
  have h1 := sum_periodic gd p hgper q
  rw [← hq] at h1
  have h2 : ∑ t ∈ range p, gd t = m + m := by
    rw [← hm, card_filter]
    exact sum_congr rfl (fun t _ => hgd t)
  have h3 : ∑ t ∈ range N, gd t + 4 * #{c : α | cnt T 0 N c = 4} = N := by
    rw [← F_positions h, ← sum_add_distrib]
    have : ∀ t ∈ range N, gd t + (if cnt T 0 N (T t) = 4 then 1 else 0) = 1 := by
      intro t _
      rw [hgd]
      by_cases hc : cnt T 0 N (T t) = 4
      · rw [if_neg (not_not.mpr hc), if_pos hc]
      · rw [if_pos hc, if_neg hc]
    rw [sum_congr rfl this]
    simp
  rw [h1, h2] at h3
  refine ⟨m, ?_⟩
  have hNq : N / p = q := by rw [hq]; exact Nat.mul_div_cancel_left _ hppos
  rw [hNq, show 2 * m = m + m by ring]
  omega

/-- **Theorem 26** for transition words: `k` even, zero slack in Lemma 1 at `L = 2k+1`,
`N = 2 (mod 4)` (i.e. excess `e = 0 (mod 4)`): no code. -/
theorem thm26_aux (h : IsCoilWord k N T) (hk : 1 ≤ k) (hke : Even k)
    {L : ℕ} (hL : L = 2 * k + 1) (hN3 : 3 * (k + 1) ≤ N) (hN6 : N < 6 * (k + 1))
    (hN4 : N < 4 * L)
    (hz : ((N : ℤ) - 2 * Fintype.card α) * (4 * L - N) = 2 * N * ((L - k) / 2 : ℕ))
    (hmod : N % 4 = 2) : False := by
  obtain ⟨m, hm⟩ := odd_line_condition h hk hke hL hN3 hN6 hN4 hz
  obtain ⟨p, hp⟩ : ∃ p, p = Nat.gcd L N := ⟨_, rfl⟩
  rw [← hp] at hm
  have hpN : p ∣ N := hp ▸ Nat.gcd_dvd_right L N
  have hpL : p ∣ L := hp ▸ Nat.gcd_dvd_left L N
  have hpodd : Odd p := Odd.of_dvd_nat (by rw [hL]; exact ⟨k, by ring⟩) hpL
  have hppos : 0 < p := Nat.pos_of_dvd_of_pos hpN (by omega)
  obtain ⟨q, hq⟩ := hpN
  have hNq : N / p = q := by rw [hq]; exact Nat.mul_div_cancel_left _ hppos
  have hqev : Even q := by
    have : Even (p * q) := hq ▸ even_length h
    rcases Nat.even_mul.mp this with h1 | h1
    · exact absurd h1 (Nat.not_even_iff_odd.mpr hpodd)
    · exact h1
  obtain ⟨q', hq'⟩ := hqev
  rw [hNq, hq'] at hm
  have h4 : (q' + q') * (2 * m) = 4 * (q' * m) := by ring
  omega

/-- **Theorem 26** for circuit codes in `Q_n` (odd lines: `k` even). -/
theorem thm26 {n : ℕ} (v : ℕ → Fin n → Bool) (h : IsCoil k N v) (hk : 1 ≤ k) (hke : Even k)
    (hN3 : 3 * (k + 1) ≤ N) (hN6 : N < 6 * (k + 1)) (hN4 : N < 4 * (2 * k + 1))
    (hz : ((N : ℤ) - 2 * n) * (4 * (2 * k + 1 : ℕ) - N) = 2 * N * ((2 * k + 1 - k) / 2 : ℕ))
    (hmod : N % 4 = 2) : False := by
  obtain ⟨T, hT, _⟩ := h.exists_word
  exact thm26_aux hT hk hke (L := 2 * k + 1) rfl hN3 hN6 hN4
    (by rw [Fintype.card_fin]; exact hz) hmod

/-- the first such point: no spread-22 circuit code of length 114 in `Q_38` (formerly SAT-only) -/
example (v : ℕ → Fin 38 → Bool) : ¬ IsCoil 22 114 v := fun h =>
  thm26 v h (by norm_num) (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

end Coil

#print axioms Coil.thm26
#print axioms Coil.dots_per_period_even
#print axioms Coil.odd_line_condition
