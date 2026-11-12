import Ccformal.Thm8Walk

/-!
# Theorem 8, Steps 1 and 2: what a level with `x_m = 0` needs; no type word exists
-/

open Finset

namespace Coil

set_option linter.deprecated false
set_option linter.unusedVariables false

variable {φ : ℕ → Prop} [DecidablePred φ] {K l N : ℕ}

set_option maxHeartbeats 1600000 in
/-- **Step 1** (LOW / HIGH). -/
theorem step1 (H : WH φ K l N) (c j : ℕ) (hl : l = 4 * c + 3)
    (hK : K + 2 * j = l * (2 * c + 1) + (2 * c + 2)) (hll : l * l + 1 = 2 * K + 4 * j)
    (m : ℕ) (hm : l ≤ m) (h0 : xm φ K l m = 0) :
    (2 * c + 2 + 2 * j : ℤ) ≤ ∑ i ∈ range (c + 1), ym φ K l (m + 2 * (c + i) + 3) ∨
    (2 * c + 2 + 2 * j : ℤ) ≤ ∑ i ∈ range (c + 1), ym φ K l (m + 2 * i + 2)
      + xm φ K l (m + 2 * c + 2 - l) := by
  obtain ⟨κ, hκ⟩ := H.hKodd
  have hKz : (K : ℤ) + 2 * j = l * (2 * c + 1) + (2 * c + 2) := by exact_mod_cast hK
  have hllz : (l : ℤ) * l + 1 = 2 * K + 4 * j := by exact_mod_cast hll
  have hlz : (l : ℤ) = 4 * c + 3 := by exact_mod_cast hl
  -- (G1)
  have hG1 : ∑ i ∈ range l, fm φ l (m + i) = -4 * j := by
    have := fm_sum H m l
    unfold xm at h0
    linarith
  have r1 : ∀ i, m + (i + 1) = m + 1 + i := by intro i; ring
  have P1 := fm_pairs H (m + 1)
  have P2 := fm_pairs H m
  have P3 := fm_pairs H (m + 2 * c + 2)
  have hrange : 2 * (2 * c + 1) + 1 = l := by omega
  -- f_m and f_{m+l-1}
  have hA3 : fm φ l m = -4 * j + ∑ i ∈ range (2 * c + 1), ym φ K l (m + 1 + 2 * i + 2) := by
    have e := sum_range_succ' (fun i => fm φ l (m + i)) (2 * (2 * c + 1))
    beta_reduce at e
    have e' : ∑ i ∈ range (2 * (2 * c + 1)), fm φ l (m + (i + 1))
        = ∑ i ∈ range (2 * (2 * c + 1)), fm φ l (m + 1 + i) :=
      sum_congr rfl (fun i _ => by rw [r1 i])
    rw [e', add_zero] at e
    rw [hrange, P1 (2 * c + 1), hG1] at e
    linarith
  have hA2 : fm φ l (m + 2 * (2 * c + 1)) = -4 * j + ∑ i ∈ range (2 * c + 1), ym φ K l (m + 2 * i + 2) := by
    have e := sum_range_succ (fun i => fm φ l (m + i)) (2 * (2 * c + 1))
    rw [hrange, P2 (2 * c + 1), hG1] at e
    linarith
  -- the middle position
  obtain ⟨e1, e2⟩ := lastExit_spec H m
  have hq : φ (lastExit φ l m + K) := xm_zero H m h0
  obtain ⟨z1, hz1⟩ := wk_parity φ (lastExit φ l m + K)
  obtain ⟨z2, hz2⟩ := wk_parity φ (lastExit φ l m)
  rw [e1] at hz2
  have hpar : wk φ (lastExit φ l m + K) ≠ (m : ℤ) + 2 * c + 2 := by
    intro he
    rw [he] at hz1
    push_cast at hz1
    have hKk : (K : ℤ) = 2 * κ + 1 := by exact_mod_cast hκ
    omega
  rcases lt_or_gt_of_ne hpar with hlow | hhigh
  · -- LOW
    left
    have hge := lastExit_ge H (m + (2 * c + 1)) (lastExit φ l m + K) (by push_cast; linarith)
    have s1 := fm_sum H m (2 * c + 1)
    have e := sum_range_succ' (fun i => fm φ l (m + i)) (2 * c)
    beta_reduce at e
    have e' : ∑ i ∈ range (2 * c), fm φ l (m + (i + 1))
        = ∑ i ∈ range (2 * c), fm φ l (m + 1 + i) :=
      sum_congr rfl (fun i _ => by rw [r1 i])
    rw [e', add_zero] at e
    rw [P1 c, hA3] at e
    have split := sum_range_add (fun i => ym φ K l (m + 1 + 2 * i + 2)) c (c + 1)
    rw [show c + (c + 1) = 2 * c + 1 by ring] at split
    have conv : ∑ i ∈ range (c + 1), ym φ K l (m + 1 + 2 * (c + i) + 2)
        = ∑ i ∈ range (c + 1), ym φ K l (m + 2 * (c + i) + 3) :=
      sum_congr rfl (fun i _ => by rw [show m + 1 + 2 * (c + i) + 2 = m + 2 * (c + i) + 3 by ring])
    have hgez : ((lastExit φ l m + K : ℕ) : ℤ) ≤ (lastExit φ l (m + (2 * c + 1)) : ℤ) := by
      exact_mod_cast hge
    push_cast at hgez s1
    rw [← conv]
    linarith
  · -- HIGH
    right
    obtain ⟨g, hg⟩ : ∃ g : ℤ, (lastExit φ l (m + (2 * c + 2)) : ℤ) = lastExit φ l m + K + g :=
      ⟨(lastExit φ l (m + (2 * c + 2)) : ℤ) - lastExit φ l m - K, by ring⟩
    have s1 := fm_sum H m (2 * c + 2)
    have e3 := sum_range_add (fun i => fm φ l (m + i)) (2 * c + 2) (2 * c + 1)
    rw [show 2 * c + 2 + (2 * c + 1) = l by omega, hG1] at e3
    have e4 := sum_range_succ (fun i => fm φ l (m + (2 * c + 2 + i))) (2 * c)
    simp only [← add_assoc] at e4 e3
    rw [P3 c, show m + 2 * c + 2 + 2 * c = m + 2 * (2 * c + 1) by ring, hA2] at e4
    have split := sum_range_add (fun i => ym φ K l (m + 2 * i + 2)) (c + 1) c
    rw [show c + 1 + c = 2 * c + 1 by ring] at split
    have conv : ∑ i ∈ range c, ym φ K l (m + 2 * c + 2 + 2 * i + 2)
        = ∑ i ∈ range c, ym φ K l (m + 2 * (c + 1 + i) + 2) :=
      sum_congr rfl (fun i _ => by
        rw [show m + 2 * c + 2 + 2 * i + 2 = m + 2 * (c + 1 + i) + 2 by ring])
    have hY : ∑ i ∈ range (c + 1), ym φ K l (m + 2 * i + 2) = 2 * c + 1 + 2 * j - g := by
      push_cast at s1
      rw [conv] at e4
      linarith
    have hx := (xm_nonneg H (m + 2 * c + 2 - l)).1
    by_cases hgneg : g ≤ -1
    · linarith
    · have hw := wk_succ φ (lastExit φ l m + K)
      rw [if_pos hq] at hw
      have hxg := xm_ge H (m + 2 * c + 2) (by omega) (lastExit φ l m + K + 1)
        (by rw [hw]; push_cast; linarith)
      rw [show m + (2 * c + 2) = m + 2 * c + 2 by ring] at hg
      push_cast at hxg
      linarith

lemma sum_pairs (g : ℕ → ℤ) (n : ℕ) :
    ∑ s ∈ range (2 * n), g s = ∑ i ∈ range n, (g (2 * i) + g (2 * i + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ]
    ring

set_option maxHeartbeats 1600000 in
/-- **Theorem 8 for type words**: `l = 4c+3`, `K = (l²+1)/2 - 2j`, `1 ≤ j ≤ c`: no type word. -/
theorem no_typeWord (φ : ℕ → Prop) [DecidablePred φ] (c j Q K l N : ℕ) (hQ : Q = c * c)
    (hl : l = 4 * c + 3) (hj1 : 1 ≤ j) (hj2 : j ≤ c) (hK : K + 2 * j = 8 * Q + 12 * c + 5)
    (hNK : N + 2 = 4 * K + 2 * l) (hW : TypeWord K l N φ) : False := by
  have hQc : c ≤ Q := by rw [hQ]; exact Nat.le_mul_self c
  have H : WH φ K l N := ⟨hW, hNK, ⟨4 * Q + 6 * c + 2 - j, by omega⟩, ⟨2 * c + 1, by omega⟩,
    by omega⟩
  have hK' : K + 2 * j = l * (2 * c + 1) + (2 * c + 2) := by
    have : l * (2 * c + 1) = 8 * Q + 10 * c + 3 := by rw [hl, hQ]; ring
    omega
  have hll : l * l + 1 = 2 * K + 4 * j := by
    have : l * l = 16 * Q + 24 * c + 9 := by rw [hl, hQ]; ring
    omega
  obtain ⟨ξ, hξ⟩ : ∃ ξ : ℕ → ℤ, ∀ τ, ξ τ = xm φ K l (τ * l) := ⟨_, fun _ => rfl⟩
  have hjz : (j : ℤ) ≤ c := by exact_mod_cast hj2
  have hj1z : (1 : ℤ) ≤ j := by exact_mod_cast hj1
  apply no_xi ξ (2 * c + 2) (8 * j) (2 * c + 2 + 2 * j) (by omega)
  · intro τ
    rw [hξ]
    exact (xm_nonneg H _).1
  · intro τ hne
    rw [hξ] at hne ⊢
    obtain ⟨h1, z, hz⟩ := xm_nonneg H (τ * l)
    omega
  · intro t
    rw [Sw]
    have h := Finset.sum_range_sub (fun i => (lastExit φ l ((t + i) * l) : ℤ)) (4 * (2 * c + 2))
    have hterm : ∀ i ∈ range (4 * (2 * c + 2)), ξ (t + i)
        = ((lastExit φ l ((t + (i + 1)) * l) : ℤ) - lastExit φ l ((t + i) * l)) - (2 * K - 1) := by
      intro i _
      rw [hξ, xm, show (t + i) * l + l = (t + (i + 1)) * l by ring]
    rw [sum_congr rfl hterm, sum_sub_distrib, h]
    have hsh := lastExit_shift_mul H (t * l) l
    rw [show (t + 4 * (2 * c + 2)) * l = t * l + l * (2 * l + 2) by rw [hl]; ring, hsh, add_zero]
    have hNKz : (N : ℤ) + 2 = 4 * K + 2 * l := by exact_mod_cast hNK
    have hllz : (l : ℤ) * l + 1 = 2 * K + 4 * j := by exact_mod_cast hll
    have hlz : (l : ℤ) = 4 * c + 3 := by exact_mod_cast hl
    simp only [sum_const, card_range, nsmul_eq_mul]
    push_cast
    have e8 : (4 : ℤ) * (2 * c + 2) = 2 * l + 2 := by rw [hlz]; ring
    rw [e8]
    linear_combination (l : ℤ) * hNKz + 2 * hllz
  · push_cast; linarith
  · push_cast; linarith
  · intro σ hσ
    obtain ⟨τ, hτ⟩ : ∃ τ, τ = 2 * c + 2 + 1 + σ := ⟨_, rfl⟩
    obtain ⟨m, hmd⟩ : ∃ m, m = τ * l := ⟨_, rfl⟩
    rw [← hτ] at hσ ⊢
    rw [hξ, ← hmd] at hσ
    have hml : l ≤ m := by
      rw [hmd]
      exact Nat.le_mul_of_pos_left l (by omega)
    rcases step1 H c j hl hK' hll m hml hσ with h1 | h1
    · left
      have e1 : Sw ξ (τ + 1) (2 * c + 2) = ∑ i ∈ range (c + 1), ym φ K l (m + 2 * (c + i) + 3) := by
        rw [Sw, show 2 * c + 2 = 2 * (c + 1) by ring, sum_pairs,
          ← sum_range_reflect (fun i => ym φ K l (m + 2 * (c + i) + 3)) (c + 1)]
        apply sum_congr rfl
        intro i hi
        rw [mem_range] at hi
        obtain ⟨d, hd⟩ : ∃ d, c = i + d := ⟨c - i, by omega⟩
        have hd' : c + 1 - 1 - i = d := by omega
        rw [hd', hξ, hξ, ym]
        have a1 : (τ + 1 + 2 * i) * l = m + 2 * (c + d) + 3 + i * (2 * l + 2) := by
          rw [hmd, hl, hd]; ring
        have a2 : (τ + 1 + (2 * i + 1)) * l = m + 2 * (c + d) + 3 + l + i * (2 * l + 2) := by
          rw [hmd, hl, hd]; ring
        rw [a1, a2, xm_per H, xm_per H]
      rw [e1]
      exact h1
    · right
      have e1 : Sw ξ σ (2 * c + 2 + 1) = ∑ i ∈ range (c + 1), ym φ K l (m + 2 * i + 2)
          + xm φ K l (m + 2 * c + 2 - l) := by
        rw [show 2 * c + 2 + 1 = 1 + 2 * (c + 1) by ring, Sw_add]
        have e0 : m + 2 * c + 2 - l = σ * l + (c + 1) * (2 * l + 2) := by
          have : m + 2 * c + 2 = σ * l + (c + 1) * (2 * l + 2) + l := by
            rw [hmd, hτ]; ring
          omega
        have es : Sw ξ σ 1 = xm φ K l (m + 2 * c + 2 - l) := by
          rw [Sw, sum_range_one, add_zero, hξ, e0, xm_per H]
        rw [es, Sw, sum_pairs,
          ← sum_range_reflect (fun i => ym φ K l (m + 2 * i + 2)) (c + 1), add_comm]
        congr 1
        apply sum_congr rfl
        intro i hi
        rw [mem_range] at hi
        obtain ⟨d, hd⟩ : ∃ d, c = i + d := ⟨c - i, by omega⟩
        have hd' : c + 1 - 1 - i = d := by omega
        rw [hd', hξ, hξ, ym]
        have a1 : m + 2 * d + 2 = (σ + 1 + 2 * i) * l + (d + 1) * (2 * l + 2) := by
          rw [hmd, hτ, hl, hd]; ring
        have a2 : m + 2 * d + 2 + l = (σ + 1 + (2 * i + 1)) * l + (d + 1) * (2 * l + 2) := by
          rw [hmd, hτ, hl, hd]; ring
        rw [a2, a1, xm_per H, xm_per H]
      rw [e1]
      exact h1

end Coil

#print axioms Coil.no_typeWord
