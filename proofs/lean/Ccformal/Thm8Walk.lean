import Ccformal.Thm8Comb

/-!
# Theorem 8: the walk of a type word, last exits, and the masses `x_m`  (PROOF2.md sec. 8)
-/

open Finset

namespace Coil

set_option linter.deprecated false
set_option linter.unusedVariables false

section walk

variable (φ : ℕ → Prop) [DecidablePred φ]

lemma Fw_add (t a b : ℕ) : Fw φ t (a + b) = Fw φ t a + Fw φ (t + a) b := by
  simp only [Fw, card_filter, sum_range_add, add_assoc]

lemma Fw_one (t : ℕ) : Fw φ t 1 = if φ t then 1 else 0 := by
  rw [Fw, card_filter, sum_range_one, add_zero]

/-- the walk: `+1` on F positions, `-1` on dots -/
def wk (t : ℕ) : ℤ := 2 * (Fw φ 0 t : ℤ) - t

lemma wk_zero : wk φ 0 = 0 := by simp [wk, Fw]

lemma wk_diff (t L : ℕ) : wk φ (t + L) - wk φ t = 2 * (Fw φ t L : ℤ) - L := by
  have := Fw_add φ 0 t L
  rw [zero_add] at this
  simp only [wk, this]
  push_cast
  ring

lemma wk_succ (t : ℕ) : wk φ (t + 1) = wk φ t + (if φ t then 1 else -1) := by
  have h := wk_diff φ t 1
  rw [Fw_one] at h
  by_cases hc : φ t
  · rw [if_pos hc] at h ⊢
    push_cast at h
    linarith
  · rw [if_neg hc] at h ⊢
    push_cast at h
    linarith

lemma wk_parity (t : ℕ) : ∃ z : ℤ, wk φ t + t = 2 * z := ⟨Fw φ 0 t, by simp [wk]⟩

end walk

/-- hypotheses on the type word used throughout -/
structure WH (φ : ℕ → Prop) [DecidablePred φ] (K l N : ℕ) : Prop where
  hW : TypeWord K l N φ
  hNK : N + 2 = 4 * K + 2 * l
  hKodd : Odd K
  hlodd : Odd l
  hlK2 : 2 * l ≤ K

variable {φ : ℕ → Prop} [DecidablePred φ] {K l N : ℕ}

lemma wk_per (H : WH φ K l N) (t : ℕ) : wk φ (t + N) = wk φ t + (2 * l + 2) := by
  have h := wk_diff φ t N
  rw [H.hW.total t] at h
  have : (N : ℤ) + 2 = 4 * K + 2 * l := by exact_mod_cast H.hNK
  push_cast at h
  linarith

lemma wk_u1 (H : WH φ K l N) (t L : ℕ) (h1 : K ≤ L + 1) (h2 : L ≤ 2 * K) :
    wk φ (t + L) - wk φ t ≤ l + 1 - ((L % 2 : ℕ) : ℤ) := by
  have h := wk_diff φ t L
  have h3 := H.hW.u1 t L h1 h2
  have : 2 * (Fw φ t L : ℤ) + ((L % 2 : ℕ) : ℤ) ≤ (L : ℤ) + l + 1 := by exact_mod_cast h3
  linarith

lemma wk_u2 (H : WH φ K l N) (t : ℕ) :
    wk φ (t + (2 * K + 1)) - wk φ t ≤ l + 2 ∧
    (wk φ (t + (2 * K + 1)) - wk φ t = l + 2 → φ (t + K)) := by
  have h := wk_diff φ t (2 * K + 1)
  obtain ⟨h1, h2⟩ := H.hW.u2 t
  have h1' : ((2 * Fw φ t (2 * K + 1) : ℕ) : ℤ) ≤ ((2 * K + l + 3 : ℕ) : ℤ) := by exact_mod_cast h1
  push_cast at h h1'
  constructor
  · linarith
  · intro he
    apply h2
    have : ((2 * Fw φ t (2 * K + 1) : ℕ) : ℤ) = ((2 * K + l + 3 : ℕ) : ℤ) := by
      push_cast
      linarith
    exact_mod_cast this

lemma wk_l1 (H : WH φ K l N) : ∀ B, 2 * l ≤ B + 1 → ∀ t, 1 ≤ wk φ (t + B) - wk φ t := by
  obtain ⟨κ, hκ⟩ := H.hKodd
  obtain ⟨lam, hlam⟩ := H.hlodd
  have hNK := H.hNK
  have hlK2 := H.hlK2
  intro B
  induction B using Nat.strong_induction_on with
  | _ B ih =>
    intro hB t
    by_cases hbig : B + 1 ≤ 2 * K + 2 * l
    · obtain ⟨L1, L2, e1, a1, a2, a3, a4, a5⟩ : ∃ L1 L2, L1 + L2 + B = N ∧ K ≤ L1 + 1 ∧
          L1 ≤ 2 * K ∧ K ≤ L2 + 1 ∧ L2 ≤ 2 * K ∧ 1 ≤ L1 % 2 + L2 % 2 := by
        obtain ⟨R, hR⟩ : ∃ R, R + B = N := ⟨N - B, by omega⟩
        by_cases hodd : R % 2 = 1
        · exact ⟨(R + 1) / 2, R / 2, by omega, by omega, by omega, by omega, by omega, by omega⟩
        · by_cases h4 : R % 4 = 2
          · exact ⟨R / 2, R / 2, by omega, by omega, by omega, by omega, by omega, by omega⟩
          · exact ⟨R / 2 + 1, R / 2 - 1, by omega, by omega, by omega, by omega, by omega,
              by omega⟩
      have p := wk_per H t
      have u1 := wk_u1 H (t + B) L1 a1 a2
      have u2 := wk_u1 H (t + B + L1) L2 a3 a4
      rw [show t + N = t + B + L1 + L2 by omega] at p
      have : (1 : ℤ) ≤ ((L1 % 2 : ℕ) : ℤ) + ((L2 % 2 : ℕ) : ℤ) := by exact_mod_cast a5
      linarith
    · have h1 := ih (2 * l - 1) (by omega) (by omega) t
      have h2 := ih (B - (2 * l - 1)) (by omega) (by omega) (t + (2 * l - 1))
      rw [show t + (2 * l - 1) + (B - (2 * l - 1)) = t + B by omega] at h2
      linarith

lemma wk_u3 (H : WH φ K l N) (t B : ℕ) (hB : B ≤ 2 * K) : wk φ (t + B) - wk φ t ≤ l + 1 := by
  obtain ⟨lam, hlam⟩ := H.hlodd
  have hlK2 := H.hlK2
  by_cases h1 : K ≤ B + 1
  · have := wk_u1 H t B h1 hB
    have : (0 : ℤ) ≤ ((B % 2 : ℕ) : ℤ) := by positivity
    linarith
  · have a := wk_u1 H t (2 * K) (by omega) (le_refl _)
    have b := wk_l1 H (2 * K - B) (by omega) (t + B)
    rw [show t + B + (2 * K - B) = t + 2 * K by omega] at b
    rw [Nat.mul_mod_right] at a
    push_cast at a
    linarith

lemma wk_l2 (H : WH φ K l N) (t t' : ℕ) (htt : t ≤ t') : -(l : ℤ) ≤ wk φ t' - wk φ t := by
  obtain ⟨κ, hκ⟩ := H.hKodd
  obtain ⟨lam, hlam⟩ := H.hlodd
  have hNK := H.hNK
  have hlK2 := H.hlK2
  obtain ⟨D, rfl⟩ := Nat.exists_eq_add_of_le htt
  by_cases hD : 2 * l ≤ D + 1
  · have := wk_l1 H D hD t
    have : (0 : ℤ) ≤ (l : ℤ) := by positivity
    linarith
  · obtain ⟨s, hs⟩ : ∃ s, s + (2 * K - 1) = t + N := ⟨t + N - (2 * K - 1), by omega⟩
    have p1 := wk_per H t
    have p2 := wk_per H (t + D)
    have a := wk_u1 H s (2 * K - 1) (by omega) (by omega)
    rw [hs] at a
    have b := wk_l1 H (2 * K - 1 + D) (by omega) s
    rw [show s + (2 * K - 1 + D) = t + D + N by omega] at b
    have e : (2 * K - 1) % 2 = 1 := by omega
    rw [e] at a
    push_cast at a
    linarith

lemma wk_growth (H : WH φ K l N) : ∀ q t, q * (2 * l - 1) ≤ t → (q : ℤ) - l ≤ wk φ t := by
  obtain ⟨lam, hlam⟩ := H.hlodd
  intro q
  induction q with
  | zero =>
    intro t _
    have := wk_l2 H 0 t (Nat.zero_le _)
    rw [wk_zero] at this
    push_cast
    linarith
  | succ q ih =>
    intro t ht
    rw [Nat.succ_mul] at ht
    obtain ⟨t0, rfl⟩ : ∃ t0, t = t0 + (2 * l - 1) := ⟨t - (2 * l - 1), by omega⟩
    have h1 := ih t0 (by omega)
    have h2 := wk_l1 H (2 * l - 1) (by omega) t0
    push_cast
    linarith

/-- the last time the walk is at or below level `m` -/
def lastExit (φ : ℕ → Prop) [DecidablePred φ] (l m : ℕ) : ℕ :=
  Nat.findGreatest (fun t => wk φ t ≤ (m : ℤ)) ((m + l + 1) * (2 * l - 1))

lemma lastExit_spec (H : WH φ K l N) (m : ℕ) :
    wk φ (lastExit φ l m) = m ∧ ∀ t, lastExit φ l m < t → (m : ℤ) < wk φ t := by
  have hle : wk φ (lastExit φ l m) ≤ (m : ℤ) := by
    have h0 : wk φ 0 ≤ (m : ℤ) := by rw [wk_zero]; positivity
    exact Nat.findGreatest_spec (P := fun t => wk φ t ≤ (m : ℤ)) (Nat.zero_le _) h0
  have hgt : ∀ t, lastExit φ l m < t → (m : ℤ) < wk φ t := by
    intro t ht
    by_cases hb : t ≤ (m + l + 1) * (2 * l - 1)
    · have := Nat.findGreatest_is_greatest (P := fun t => wk φ t ≤ (m : ℤ)) ht hb
      exact not_le.mp this
    · have := wk_growth H (m + l + 1) t (by omega)
      push_cast at this
      linarith
  refine ⟨?_, hgt⟩
  have h1 := hgt (lastExit φ l m + 1) (Nat.lt_succ_self _)
  have h2 := wk_succ φ (lastExit φ l m)
  by_cases hc : φ (lastExit φ l m)
  · rw [if_pos hc] at h2; omega
  · rw [if_neg hc] at h2; omega

lemma lastExit_unique (H : WH φ K l N) (m s : ℕ) (h1 : wk φ s = m)
    (h2 : ∀ t, s < t → (m : ℤ) < wk φ t) : s = lastExit φ l m := by
  obtain ⟨e1, e2⟩ := lastExit_spec H m
  rcases Nat.lt_trichotomy s (lastExit φ l m) with h | h | h
  · have := h2 _ h; omega
  · exact h
  · have := e2 _ h; omega

lemma lastExit_ge (H : WH φ K l N) (m t : ℕ) (h : wk φ t ≤ (m : ℤ)) : t ≤ lastExit φ l m := by
  by_contra hc
  have := (lastExit_spec H m).2 t (by omega)
  omega

lemma lastExit_shift (H : WH φ K l N) (m : ℕ) :
    lastExit φ l (m + (2 * l + 2)) = lastExit φ l m + N := by
  obtain ⟨e1, e2⟩ := lastExit_spec H m
  symm
  apply lastExit_unique H
  · rw [wk_per H, e1]
    push_cast
    ring
  · intro t ht
    obtain ⟨t0, rfl⟩ : ∃ t0, t = t0 + N := ⟨t - N, by omega⟩
    have := e2 t0 (by omega)
    rw [wk_per H]
    push_cast
    linarith

lemma lastExit_shift_mul (H : WH φ K l N) (m q : ℕ) :
    lastExit φ l (m + q * (2 * l + 2)) = lastExit φ l m + q * N := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul, ← add_assoc, lastExit_shift H, ih, Nat.succ_mul]
    ring

lemma lastExit_FF (H : WH φ K l N) (m : ℕ) :
    φ (lastExit φ l m) ∧ φ (lastExit φ l m + 1) ∧ wk φ (lastExit φ l m + 2) = m + 2 := by
  obtain ⟨e1, e2⟩ := lastExit_spec H m
  have s1 := wk_succ φ (lastExit φ l m)
  have g1 := e2 (lastExit φ l m + 1) (by omega)
  have s2 := wk_succ φ (lastExit φ l m + 1)
  rw [show lastExit φ l m + 1 + 1 = lastExit φ l m + 2 by ring] at s2
  have g2 := e2 (lastExit φ l m + 2) (by omega)
  by_cases c1 : φ (lastExit φ l m)
  · rw [if_pos c1] at s1
    by_cases c2 : φ (lastExit φ l m + 1)
    · rw [if_pos c2] at s2
      exact ⟨c1, c2, by omega⟩
    · rw [if_neg c2] at s2
      exfalso; omega
  · rw [if_neg c1] at s1
    exfalso; omega

/-- `x_m = u_{m+l} - u_m - (2K-1)` -/
def xm (φ : ℕ → Prop) [DecidablePred φ] (K l m : ℕ) : ℤ :=
  (lastExit φ l (m + l) : ℤ) - lastExit φ l m - (2 * K - 1)

/-- `f_m = u_{m+1} - u_m - l` -/
def fm (φ : ℕ → Prop) [DecidablePred φ] (l m : ℕ) : ℤ :=
  (lastExit φ l (m + 1) : ℤ) - lastExit φ l m - l

lemma xm_nonneg (H : WH φ K l N) (m : ℕ) : 0 ≤ xm φ K l m ∧ ∃ z, xm φ K l m = 2 * z := by
  obtain ⟨κ, hκ⟩ := H.hKodd
  obtain ⟨lam, hlam⟩ := H.hlodd
  obtain ⟨e1, e2⟩ := lastExit_spec H m
  obtain ⟨e3, e4⟩ := lastExit_spec H (m + l)
  have a := wk_u1 H (lastExit φ l m) (2 * K - 1) (by omega) (by omega)
  have e : (2 * K - 1) % 2 = 1 := by omega
  rw [e] at a
  push_cast at a
  have hle := lastExit_ge H (m + l) (lastExit φ l m + (2 * K - 1)) (by push_cast; linarith)
  obtain ⟨z1, hz1⟩ := wk_parity φ (lastExit φ l m)
  obtain ⟨z2, hz2⟩ := wk_parity φ (lastExit φ l (m + l))
  rw [e1] at hz1
  rw [e3] at hz2
  push_cast at hz2
  constructor
  · unfold xm
    omega
  · refine ⟨z2 - z1 - K - lam, ?_⟩
    unfold xm
    have hl : (l : ℤ) = 2 * lam + 1 := by exact_mod_cast hlam
    linarith

lemma xm_per (H : WH φ K l N) (m q : ℕ) : xm φ K l (m + q * (2 * l + 2)) = xm φ K l m := by
  unfold xm
  rw [show m + q * (2 * l + 2) + l = m + l + q * (2 * l + 2) by ring, lastExit_shift_mul H,
    lastExit_shift_mul H]
  push_cast
  ring

lemma xm_zero (H : WH φ K l N) (m : ℕ) (h0 : xm φ K l m = 0) : φ (lastExit φ l m + K) := by
  obtain ⟨κ, hκ⟩ := H.hKodd
  obtain ⟨e1, e2⟩ := lastExit_spec H m
  obtain ⟨-, -, e5⟩ := lastExit_FF H (m + l)
  unfold xm at h0
  have hu : lastExit φ l (m + l) + 2 = lastExit φ l m + (2 * K + 1) := by omega
  rw [hu] at e5
  apply (wk_u2 H (lastExit φ l m)).2
  rw [e5, e1]
  push_cast
  ring

lemma xm_ge (H : WH φ K l N) (m : ℕ) (hm : l ≤ m) (t : ℕ) (ht : (m : ℤ) + 2 ≤ wk φ t) :
    (lastExit φ l m : ℤ) - t + 2 ≤ xm φ K l (m - l) := by
  obtain ⟨κ, hκ⟩ := H.hKodd
  obtain ⟨e1, e2⟩ := lastExit_spec H (m - l)
  have hcast : ((m - l : ℕ) : ℤ) = (m : ℤ) - l := by
    rw [Nat.cast_sub hm]
  rw [hcast] at e1
  have hge : lastExit φ l (m - l) + 2 * K + 1 ≤ t := by
    by_contra hcon
    by_cases h1 : t ≤ lastExit φ l (m - l)
    · have := wk_l2 H t _ h1
      linarith
    · obtain ⟨B, hB⟩ : ∃ B, t = lastExit φ l (m - l) + B := ⟨t - lastExit φ l (m - l), by omega⟩
      have := wk_u3 H (lastExit φ l (m - l)) B (by omega)
      rw [← hB] at this
      linarith
  unfold xm
  rw [Nat.sub_add_cancel hm]
  have : ((lastExit φ l (m - l) + 2 * K + 1 : ℕ) : ℤ) ≤ (t : ℤ) := by exact_mod_cast hge
  push_cast at this
  linarith

lemma fm_sum (H : WH φ K l N) (m n : ℕ) :
    ∑ i ∈ range n, fm φ l (m + i) = (lastExit φ l (m + n) : ℤ) - lastExit φ l m - n * l := by
  have h := Finset.sum_range_sub (fun i => (lastExit φ l (m + i) : ℤ)) n
  simp only [add_zero] at h
  unfold fm
  rw [sum_sub_distrib]
  simp only [← add_assoc] at h ⊢
  rw [h]
  simp

/-- (G2) -/
lemma fm_pair (H : WH φ K l N) (m : ℕ) :
    fm φ l m + fm φ l (m + 1) = -(xm φ K l (m + 2) + xm φ K l (m + 2 + l)) := by
  have hs := lastExit_shift H m
  have hNK : (N : ℤ) + 2 = 4 * K + 2 * l := by exact_mod_cast H.hNK
  unfold fm xm
  rw [show m + 2 + l + l = m + (2 * l + 2) by ring, hs, show m + 1 + 1 = m + 2 by ring]
  push_cast
  linarith

/-- `y_m = x_m + x_{m+l}` -/
def ym (φ : ℕ → Prop) [DecidablePred φ] (K l m : ℕ) : ℤ := xm φ K l m + xm φ K l (m + l)

lemma fm_pairs (H : WH φ K l N) (m n : ℕ) :
    ∑ i ∈ range (2 * n), fm φ l (m + i) = -∑ i ∈ range n, ym φ K l (m + 2 * i + 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ]
    have := fm_pair H (m + 2 * n)
    unfold ym
    rw [show m + 2 * n + 2 + l = m + 2 * n + 2 + l by rfl] at this
    rw [show m + (2 * n + 1) = m + 2 * n + 1 by ring]
    linarith

end Coil
