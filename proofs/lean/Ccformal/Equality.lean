import Ccformal.Checker

/-!
# Equality in Lemma 1: what a zero-slack code must look like

If `(N - 2n)(4L - N) = 2N⌊(L-k)/2⌋` then every inequality in the proof of Lemma 1 is an equality:
exactly `N/2 - n` coordinates are used four times ("F coordinates"), every window of length `L`
has exactly `⌊(L-k)/2⌋` repeated coordinates, an F coordinate occurs in every window of length `L`,
and no other coordinate occurs twice in such a window.
-/

open Finset

namespace Coil

set_option linter.unusedSectionVars false

variable {α : Type*} [Fintype α] [DecidableEq α] {k N : ℕ} {T : ℕ → α}

lemma per_mul (per : ∀ i, T (i + N) = T i) (i m : ℕ) : T (i + m * N) = T i := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.succ_mul, ← add_assoc, per, ih]

lemma cnt_mod (per : ∀ i, T (i + N) = T i) (t L : ℕ) (c : α) :
    cnt T t L c = cnt T (t % N) L c := by
  have : ∀ j, T (t + j) = T (t % N + j) := by
    intro j
    conv_lhs => rw [← Nat.mod_add_div t N, mul_comm, add_right_comm]
    exact per_mul per _ _
  simp only [cnt, this]

lemma one_le_cnt {t L i : ℕ} {c : α} (hi : i < L) (e : T (t + i) = c) : 1 ≤ cnt T t L c := by
  rw [cnt]
  exact card_pos.mpr ⟨i, by simp [hi, e]⟩

lemma two_le_cnt {t L i j : ℕ} {c : α} (hij : i < j) (hj : j < L) (hi : T (t + i) = c)
    (hj' : T (t + j) = c) : 2 ≤ cnt T t L c := by
  have hsub : ({i, j} : Finset ℕ) ⊆ {x ∈ range L | T (t + x) = c} := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · simp [hi]; omega
    · simp [hj', hj]
  calc 2 = #({i, j} : Finset ℕ) := (card_pair (ne_of_lt hij)).symm
    _ ≤ _ := card_le_card hsub

lemma exists_two_of_cnt {t L : ℕ} {c : α} (h2 : cnt T t L c = 2) :
    ∃ i j, i < j ∧ j < L ∧ T (t + i) = c ∧ T (t + j) = c := by
  rw [cnt] at h2
  obtain ⟨x, y, hxy, hs⟩ := card_eq_two.mp h2
  have hx : x ∈ ({j ∈ range L | T (t + j) = c} : Finset ℕ) := by rw [hs]; simp
  have hy : y ∈ ({j ∈ range L | T (t + j) = c} : Finset ℕ) := by rw [hs]; simp
  simp only [mem_filter, mem_range] at hx hy
  rcases Nat.lt_or_gt_of_ne hxy with h' | h'
  · exact ⟨x, y, h', hy.1, hx.2, hy.2⟩
  · exact ⟨y, x, h', hx.1, hy.2, hx.2⟩

/-- (F2) as a statement about positions: equal coordinates are at least `k+1` apart -/
lemma gap_ge (h : IsCoilWord k N T) (hk : 1 ≤ k) (hN : 2 * k + 2 ≤ N) {u d : ℕ} (hd : 1 ≤ d)
    (he : T u = T (u + d)) : k + 1 ≤ d := by
  by_contra hc
  have h1 := two_le_cnt (T := T) (t := u) (L := k + 1) (i := 0) (j := d) (c := T u)
    (by omega) (by omega) (by simp) he.symm
  have h2 := cnt_short h hk hN (t := u) (le_refl (k + 1)) (T u)
  omega

lemma uses_le_four (h : IsCoilWord k N T) (hk : 1 ≤ k) (hN : 2 * k + 2 ≤ N)
    (hN6 : N < 6 * (k + 1)) (c : α) : cnt T 0 N c ≤ 4 := by
  have h1 := sum_cnt_windows h.per (k + 1) c
  have h2 : ∑ t ∈ range N, cnt T t (k + 1) c ≤ ∑ _t ∈ range N, 1 :=
    sum_le_sum (fun t _ => cnt_short h hk hN (le_refl _) c)
  simp only [sum_const, card_range, smul_eq_mul, mul_one] at h2
  obtain ⟨r, hr⟩ := h.closed c
  by_contra hc
  have h6 : 6 ≤ cnt T 0 N c := by omega
  have := Nat.mul_le_mul_left (k + 1) h6
  omega

/-- the window slides by one step -/
lemma cnt_slide (T : ℕ → α) (t L : ℕ) (c : α) :
    cnt T (t + 1) L c + (if T t = c then 1 else 0) = cnt T t L c + (if T (t + L) = c then 1 else 0) := by
  have h1 := cnt_add T t 1 L c
  have h2 := cnt_add T t L 1 c
  rw [cnt_one] at h1 h2
  rw [Nat.add_comm 1 L] at h1
  omega

/-- **Equality case of Lemma 1.** -/
theorem equality_case (h : IsCoilWord k N T) (hk : 1 ≤ k) (hN : 2 * k + 2 ≤ N)
    (hN6 : N < 6 * (k + 1)) {L : ℕ} (hL1 : k ≤ L) (hL2 : N < 4 * L) (hL3 : L ≤ 2 * (k + 1))
    (hL4 : L + k ≤ N)
    (hz : ((N : ℤ) - 2 * Fintype.card α) * (4 * L - N) = 2 * N * ((L - k) / 2 : ℕ)) :
    2 * #{c : α | cnt T 0 N c = 4} + 2 * Fintype.card α = N ∧
    (∀ t, P T t L = (L - k) / 2) ∧
    (∀ c, cnt T 0 N c = 4 → ∀ t, 1 ≤ cnt T t L c) ∧
    (∀ c, cnt T 0 N c ≠ 4 → ∀ t, cnt T t L c ≠ 2) := by
  set c0 := (L - k) / 2 with hc0
  set n2 := #{c : α | cnt T 0 N c = 4} with hn2def
  set D := 4 * L - N with hD
  have hDpos : 0 < D := by omega
  have hm := uses_le_four h hk hN hN6
  have hn2 : N ≤ 2 * Fintype.card α + 2 * n2 := by
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
  have hP : ∀ t, P T t L ≤ c0 := fun t => P_le h hk hN hL1 hL3 hL4
  -- per-coordinate counts
  let S : α → ℕ := fun c => ∑ t ∈ range N, if cnt T t L c = 2 then 1 else 0
  let Z : α → ℕ := fun c => ∑ t ∈ range N, if cnt T t L c = 0 then 1 else 0
  have hSZ : ∀ c, L * cnt T 0 N c + Z c = S c + N := by
    intro c
    have h1 := sum_cnt_windows h.per L c
    have h2 : ∀ t ∈ range N, cnt T t L c + (if cnt T t L c = 0 then 1 else 0)
        = (if cnt T t L c = 2 then 1 else 0) + 1 := by
      intro t _
      have := cnt_le_two h hk hN (t := t) hL3 c
      split_ifs <;> omega
    have h3 := sum_congr rfl h2
    rw [sum_add_distrib, sum_add_distrib, h1] at h3
    simp only [sum_const, card_range, smul_eq_mul, mul_one] at h3
    exact h3
  let g : α → ℕ := fun c => if cnt T 0 N c = 4 then D else 0
  have hgS : ∀ c ∈ (univ : Finset α), g c ≤ S c := by
    intro c _
    simp only [g]
    split_ifs with hc
    · have := hSZ c
      rw [hc] at this
      omega
    · exact Nat.zero_le _
  have hg : ∑ c, g c = n2 * D := by
    have : ∀ c ∈ (univ : Finset α), g c = (if cnt T 0 N c = 4 then 1 else 0) * D := by
      intro c _
      simp only [g]
      split_ifs <;> simp
    rw [sum_congr rfl this, ← sum_mul, ← card_filter]
  have hS : ∑ c, S c = ∑ t ∈ range N, P T t L := by
    simp only [S, P_eq_sum]
    rw [sum_comm]
  have hPs : ∑ t ∈ range N, P T t L ≤ N * c0 := by
    calc ∑ t ∈ range N, P T t L ≤ ∑ _t ∈ range N, c0 := sum_le_sum (fun t _ => hP t)
      _ = N * c0 := by simp
  have hchain : n2 * D ≤ N * c0 := by
    calc n2 * D = ∑ c, g c := hg.symm
      _ ≤ ∑ c, S c := sum_le_sum hgS
      _ = ∑ t ∈ range N, P T t L := hS
      _ ≤ N * c0 := hPs
  -- the zero-slack hypothesis forces equality
  have hDz : ((D : ℕ) : ℤ) = 4 * L - N := by
    rw [hD, Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [← hDz] at hz
  have hz' : (2 * n2 : ℤ) * D ≤ ((N : ℤ) - 2 * Fintype.card α) * D := by
    have : ((n2 * D : ℕ) : ℤ) ≤ ((N * c0 : ℕ) : ℤ) := by exact_mod_cast hchain
    push_cast at this
    linarith
  have hDz0 : (0 : ℤ) < D := by exact_mod_cast hDpos
  have h1 : (2 * n2 : ℤ) ≤ (N : ℤ) - 2 * Fintype.card α := le_of_mul_le_mul_right hz' hDz0
  have h2 : (N : ℤ) ≤ 2 * Fintype.card α + 2 * n2 := by exact_mod_cast hn2
  have heq : 2 * n2 + 2 * Fintype.card α = N := by
    have : (2 * n2 : ℤ) + 2 * Fintype.card α = N := by linarith
    exact_mod_cast this
  have heq2 : n2 * D = N * c0 := by
    have h3 : (2 * n2 : ℤ) = (N : ℤ) - 2 * Fintype.card α := by linarith
    rw [← h3] at hz
    have : ((n2 * D : ℕ) : ℤ) = ((N * c0 : ℕ) : ℤ) := by
      push_cast
      linarith
    exact_mod_cast this
  have hsumP : ∑ t ∈ range N, P T t L = ∑ _t ∈ range N, c0 := by
    have : ∑ t ∈ range N, P T t L = N * c0 := by
      apply le_antisymm hPs
      calc N * c0 = n2 * D := heq2.symm
        _ = ∑ c, g c := hg.symm
        _ ≤ ∑ c, S c := sum_le_sum hgS
        _ = ∑ t ∈ range N, P T t L := hS
    rw [this]
    simp
  have hsumS : ∑ c, g c = ∑ c, S c := by
    apply le_antisymm (sum_le_sum hgS)
    calc ∑ c, S c = ∑ t ∈ range N, P T t L := hS
      _ ≤ N * c0 := hPs
      _ = n2 * D := heq2.symm
      _ = ∑ c, g c := hg.symm
  have hPall := (sum_eq_sum_iff_of_le (fun t _ => hP t)).mp hsumP
  have hgall := (sum_eq_sum_iff_of_le hgS).mp hsumS
  have hNpos : 0 < N := by omega
  refine ⟨heq, ?_, ?_, ?_⟩
  · intro t
    have := hPall (t % N) (mem_range.mpr (Nat.mod_lt _ hNpos))
    simp only [P, cnt_mod h.per t] at this ⊢
    exact this
  · intro c hc t
    have h3 := hgall c (mem_univ c)
    simp only [g, hc, if_true] at h3
    have h4 := hSZ c
    rw [hc, ← h3] at h4
    have hZ : Z c = 0 := by omega
    have h5 := (sum_eq_zero_iff.mp hZ) (t % N) (mem_range.mpr (Nat.mod_lt _ hNpos))
    rw [cnt_mod h.per t]
    by_contra h6
    have h7 : cnt T (t % N) L c = 0 := by omega
    simp [h7] at h5
  · intro c hc t
    have h3 := hgall c (mem_univ c)
    simp only [g, hc, if_false] at h3
    have h5 := (sum_eq_zero_iff.mp h3.symm) (t % N) (mem_range.mpr (Nat.mod_lt _ hNpos))
    rw [cnt_mod h.per t]
    intro h6
    simp [h6] at h5

end Coil
