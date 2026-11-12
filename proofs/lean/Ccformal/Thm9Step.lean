import Ccformal.Thm9Setup

/-!
# Towards Theorem 9: Step 1' (PROOF2.md sec. 9) -- the six options at a zero level

For `l = 4c+3`, `K = l(l-1)/2` (i.e. `j = c+1`), a type word with triples gives a sequence `ξ` (`ξ τ = x_{τ l}`) with
`Xi9 (2c+2) ξ`: even, nonnegative, mass `4a` per period `4a` (`a = 2c+2`), and at every zero one of six options.
Theorem 9 is then equivalent to: `Xi9 a ξ` is impossible (for `a ≥ 4`; brute force `scripts/xi9.py`: 0 solutions for a = 4).
That last, purely combinatorial step (Step 2') is NOT formalized yet.
-/

open Finset

namespace Coil

set_option linter.deprecated false
set_option linter.unusedVariables false

variable {φ : ℕ → Prop} [DecidablePred φ] {K l N : ℕ}

set_option maxHeartbeats 1600000 in
/-- **Step 1, exact form** (LOW / HIGH with the identities). -/
theorem step1x (H : WH φ K l N) (c j : ℕ) (hl : l = 4 * c + 3)
    (hK : K + 2 * j = l * (2 * c + 1) + (2 * c + 2)) (hll : l * l + 1 = 2 * K + 4 * j)
    (m : ℕ) (hm : l ≤ m) (h0 : xm φ K l m = 0) :
    (wk φ (lastExit φ l m + K) ≤ (m : ℤ) + 2 * c + 1 ∧
      ∑ i ∈ range (c + 1), ym φ K l (m + 2 * (c + i) + 3)
        = (2 * c + 2 + 2 * j : ℤ) + ((lastExit φ l (m + (2 * c + 1)) : ℤ) - (lastExit φ l m + K))) ∨
    ((m : ℤ) + 2 * c + 3 ≤ wk φ (lastExit φ l m + K) ∧
      ∑ i ∈ range (c + 1), ym φ K l (m + 2 * i + 2)
        = (2 * c + 2 + 2 * j : ℤ) - 1 - ((lastExit φ l (m + 2 * c + 2) : ℤ) - (lastExit φ l m + K))) := by
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
    refine ⟨by omega, ?_⟩
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
    rw [show m + (2 * c + 2) = m + 2 * c + 2 by ring] at hg
    refine ⟨by omega, ?_⟩
    rw [hY, hg]
    ring


lemma xm_zero_tr (H : WH φ K l N) {tr e0 : ℕ → Prop} (hT : TypeWordT K l N φ tr e0) (m : ℕ)
    (h0 : xm φ K l m = 0) : tr (lastExit φ l m) := by
  obtain ⟨κ, hκ⟩ := H.hKodd
  obtain ⟨e1, e2⟩ := lastExit_spec H m
  obtain ⟨-, -, e5⟩ := lastExit_FF H (m + l)
  unfold xm at h0
  have hu : lastExit φ l (m + l) + 2 = lastExit φ l m + (2 * K + 1) := by omega
  rw [hu] at e5
  have hd := wk_diff φ (lastExit φ l m) (2 * K + 1)
  rw [e5, e1] at hd
  apply hT.u2tr
  have : (2 * (Fw φ (lastExit φ l m) (2 * K + 1) : ℤ)) = ((2 * K + l + 3 : ℕ) : ℤ) := by
    push_cast at hd ⊢
    linarith
  exact_mod_cast this

/-- the target structure of Step 1' -/
structure Xi9 (a : ℕ) (ξ : ℕ → ℤ) : Prop where
  nn : ∀ τ, 0 ≤ ξ τ
  ev : ∀ τ, ∃ z, ξ τ = 2 * z
  mass : ∀ t, Sw ξ t (4 * a) = 4 * a
  opt : ∀ σ, ξ (a + 1 + σ) = 0 →
      (2 * (a : ℤ) ≤ Sw ξ (a + 1 + σ + 1) a ∧ ξ (a + 1 + σ + a + 1) ≠ 0) ∨
      (2 * (a : ℤ) ≤ Sw ξ (a + 1 + σ + 1) a ∧ ξ (a + 1 + σ + 1) ≠ 0) ∨
      (2 * (a : ℤ) + 2 ≤ Sw ξ (a + 1 + σ + 1) a) ∨
      (2 * (a : ℤ) ≤ Sw ξ (σ + 1) a ∧ ξ (σ + 1) ≠ 0) ∨
      (2 * (a : ℤ) + 2 ≤ Sw ξ (σ + 1) a) ∨
      (2 * (a : ℤ) ≤ Sw ξ σ (a + 1) ∧ ξ σ ≠ 0)

set_option maxHeartbeats 3200000 in
theorem xi9_of_typeWordT (φ tr e0 : ℕ → Prop) [DecidablePred φ] (c Q K l N : ℕ) (hc : 1 ≤ c)
    (hQ : Q = c * c) (hl : l = 4 * c + 3) (hK : K + 2 * (c + 1) = 8 * Q + 12 * c + 5)
    (hNK : N + 2 = 4 * K + 2 * l) (hW : TypeWordT K l N φ tr e0) :
    ∃ ξ : ℕ → ℤ, Xi9 (2 * c + 2) ξ := by
  have hQc : c ≤ Q := by rw [hQ]; exact Nat.le_mul_self c
  have H : WH φ K l N := ⟨hW.base, hNK, ⟨4 * Q + 5 * c + 1, by omega⟩, ⟨2 * c + 1, by omega⟩,
    by omega⟩
  have hK' : K + 2 * (c + 1) = l * (2 * c + 1) + (2 * c + 2) := by
    have : l * (2 * c + 1) = 8 * Q + 10 * c + 3 := by rw [hl, hQ]; ring
    omega
  have hll : l * l + 1 = 2 * K + 4 * (c + 1) := by
    have : l * l = 16 * Q + 24 * c + 9 := by rw [hl, hQ]; ring
    omega
  obtain ⟨ξ, hξ⟩ : ∃ ξ : ℕ → ℤ, ∀ τ, ξ τ = xm φ K l (τ * l) := ⟨_, fun _ => rfl⟩
  have hK1 : 1 ≤ K := by omega
  have hSev : ∀ t n, ∃ z, Sw ξ t n = 2 * z := by
    intro t n
    induction n with
    | zero => exact ⟨0, by simp [Sw]⟩
    | succ n ih =>
      obtain ⟨z, hz⟩ := ih
      obtain ⟨z', hz'⟩ := (xm_nonneg H ((t + n) * l)).2
      refine ⟨z + z', ?_⟩
      rw [Sw, sum_range_succ, ← Sw, hz, hξ, hz']
      ring
  refine ⟨ξ, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro τ
    rw [hξ]
    exact (xm_nonneg H _).1
  · intro τ
    rw [hξ]
    exact (xm_nonneg H _).2
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
    have hllz : (l : ℤ) * l + 1 = 2 * K + 4 * (c + 1) := by exact_mod_cast hll
    have hlz : (l : ℤ) = 4 * c + 3 := by exact_mod_cast hl
    simp only [sum_const, card_range, nsmul_eq_mul]
    push_cast
    have e8 : (4 : ℤ) * (2 * c + 2) = 2 * l + 2 := by rw [hlz]; ring
    rw [e8]
    linear_combination (l : ℤ) * hNKz + 2 * hllz - 2 * hlz
  · intro σ hσ
    obtain ⟨τ, hτ⟩ : ∃ τ, τ = 2 * c + 2 + 1 + σ := ⟨_, rfl⟩
    obtain ⟨m, hmd⟩ : ∃ m, m = τ * l := ⟨_, rfl⟩
    rw [← hτ] at hσ ⊢
    rw [hξ, ← hmd] at hσ
    have hml : l ≤ m := by
      rw [hmd]
      exact Nat.le_mul_of_pos_left l (by omega)
    have trs : tr (lastExit φ l m) := xm_zero_tr H hW m hσ
    have hum : lastExit φ l (m + l) + 1 = lastExit φ l m + K + K := by
      unfold xm at hσ
      omega
    push_cast
    rcases step1x H c (c + 1) hl hK' hll m hml hσ with ⟨hlow, hsum⟩ | ⟨hhigh, hsum⟩
    · -- LOW
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
      rw [← e1] at hsum
      have hG := lastExit_ge H (m + (2 * c + 1)) (lastExit φ l m + K) (by push_cast; linarith)
      by_cases hG0 : lastExit φ l (m + (2 * c + 1)) = lastExit φ l m + K
      · have hS : Sw ξ (τ + 1) (2 * c + 2) = 2 * (2 * c + 2) := by
          rw [hsum, hG0]
          push_cast
          ring
        by_cases hx : xm φ K l (m + (2 * c + 1)) = 0
        · right; left
          refine ⟨by rw [hS], ?_⟩
          have trq : tr (lastExit φ l m + K) := hG0 ▸ xm_zero_tr H hW _ hx
          have e0q := (hW.tr_e0 _ trq).2
          rw [hξ, show (τ + 1) * l = m + l by rw [hmd]; ring]
          intro hx2
          have tr2 := xm_zero_tr H hW (m + l) hx2
          apply hW.y2 (lastExit φ l (m + l))
          exact ⟨tr2, by rw [hum]; exact e0q⟩
        · left
          refine ⟨by rw [hS], ?_⟩
          rw [hξ]
          have e3 : (τ + (2 * c + 2) + 1) * l = m + (2 * c + 1) + (c + 1) * (2 * l + 2) := by
            rw [hmd, hl]; ring
          rw [e3, xm_per H]
          exact hx
      · right; right; left
        obtain ⟨z, hz⟩ := hSev (τ + 1) (2 * c + 2)
        have hlt : ((lastExit φ l m + K : ℕ) : ℤ) < (lastExit φ l (m + (2 * c + 1)) : ℤ) := by
          exact_mod_cast (by omega : lastExit φ l m + K < lastExit φ l (m + (2 * c + 1)))
        push_cast at hlt hsum
        omega
    · -- HIGH
      have e1 : Sw ξ (σ + 1) (2 * c + 2) = ∑ i ∈ range (c + 1), ym φ K l (m + 2 * i + 2) := by
        rw [Sw, show 2 * c + 2 = 2 * (c + 1) by ring, sum_pairs,
          ← sum_range_reflect (fun i => ym φ K l (m + 2 * i + 2)) (c + 1)]
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
      rw [← e1] at hsum
      obtain ⟨z, hz⟩ := hSev (σ + 1) (2 * c + 2)
      push_cast at hsum
      rcases lt_trichotomy ((lastExit φ l (m + 2 * c + 2) : ℤ) + 1) ((lastExit φ l m : ℤ) + K)
        with hg | hg | hg
      · right; right; right; right; left
        omega
      · right; right; right; left
        refine ⟨by omega, ?_⟩
        rw [hξ]
        have e3 : m + 2 * c + 2 = (σ + 1) * l + (c + 1) * (2 * l + 2) := by
          rw [hmd, hτ, hl]; ring
        intro hx
        rw [← xm_per H ((σ + 1) * l) (c + 1), ← e3] at hx
        have tr2 := xm_zero_tr H hW (m + 2 * c + 2) hx
        have e0q := (hW.tr_e0 _ trs).2
        apply hW.y2 (lastExit φ l (m + 2 * c + 2))
        refine ⟨tr2, ?_⟩
        have hnat : lastExit φ l (m + 2 * c + 2) + 1 = lastExit φ l m + K := by exact_mod_cast hg
        rw [hnat]
        exact e0q
      · right; right; right; right; right
        have hq : φ (lastExit φ l m + K) := xm_zero H m hσ
        have hw := wk_succ φ (lastExit φ l m + K)
        rw [if_pos hq] at hw
        have hxg := xm_ge H (m + 2 * c + 2) (by omega) (lastExit φ l m + K + 1)
          (by rw [hw]; push_cast; linarith)
        have e0' : m + 2 * c + 2 - l = σ * l + (c + 1) * (2 * l + 2) := by
          have : m + 2 * c + 2 = σ * l + (c + 1) * (2 * l + 2) + l := by
            rw [hmd, hτ]; ring
          omega
        have es : ξ σ = xm φ K l (m + 2 * c + 2 - l) := by
          rw [hξ, e0', xm_per H]
        push_cast at hxg
        refine ⟨?_, ?_⟩
        · rw [show 2 * c + 2 + 1 = 1 + (2 * c + 2) by ring, Sw_add]
          have e5 : Sw ξ σ 1 = ξ σ := by simp [Sw]
          rw [e5, es]
          linarith
        · rw [es]
          linarith

end Coil

#print axioms Coil.xi9_of_typeWordT
