import Ccformal.Thm33a

/-!
# Structure of near-extremal codes (PROOF2.md sec. 1: (S1), (S3a))

If Lemma 1 at `L` has slack less than one coordinate (hypothesis (H): `(m+1)(4L-N) > N⌊(L-k)/2⌋` with
`N = 2n + 2m`), then exactly `m` coordinates are used four times (F coordinates), all others exactly
twice (dots) -- none is unused -- and the F/dot type word is BALANCED: a window of length `Lw`,
`k ≤ Lw ≤ min(2K, N-k)`, contains at most `m + ⌊(Lw-k)/2⌋` F positions.
(Infrastructure for Theorems 8, 9 and the skeleton method; not yet used.)
-/

open Finset

namespace Coil

set_option linter.unusedSectionVars false
set_option linter.deprecated false

variable {α : Type*} [Fintype α] [DecidableEq α] {k N : ℕ} {T : ℕ → α}

/-- the double count in Lemma 1: `n₂ (4L - N) ≤ N ⌊(L-k)/2⌋` -/
lemma F_count_le (h : IsCoilWord k N T) (hk : 1 ≤ k) (hN : 2 * k + 2 ≤ N) {L : ℕ}
    (hL1 : k ≤ L) (hL3 : L ≤ 2 * (k + 1)) (hL4 : L + k ≤ N) :
    #{c : α | cnt T 0 N c = 4} * (4 * L - N) ≤ N * ((L - k) / 2) := by
  have hPs : ∑ t ∈ range N, P T t L ≤ N * ((L - k) / 2) := by
    calc ∑ t ∈ range N, P T t L ≤ ∑ _t ∈ range N, (L - k) / 2 :=
          sum_le_sum (fun t _ => P_le h hk hN hL1 hL3 hL4)
      _ = N * ((L - k) / 2) := by simp
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
  exact le_trans hdc hPs

/-- **(S1)**: under (H) exactly `m` coordinates are used four times and all others exactly twice. -/
theorem structure_S1 (h : IsCoilWord k N T) (hk : 1 ≤ k) (hN : 2 * k + 2 ≤ N)
    (hN6 : N < 6 * (k + 1)) {L m : ℕ} (hL1 : k ≤ L) (hL3 : L ≤ 2 * (k + 1))
    (hL4 : L + k ≤ N) (hm : N = 2 * Fintype.card α + 2 * m)
    (hH : N * ((L - k) / 2) < (m + 1) * (4 * L - N)) :
    #{c : α | cnt T 0 N c = 4} = m ∧ ∀ c, cnt T 0 N c = 4 ∨ cnt T 0 N c = 2 := by
  have hle := F_count_le h hk hN hL1 hL3 hL4
  have hm4 := uses_le_four h hk hN hN6
  have hsum := sum_cnt T 0 N
  have hpt : ∀ c ∈ (univ : Finset α), cnt T 0 N c ≤ 2 + 2 * (if cnt T 0 N c = 4 then 1 else 0) := by
    intro c _
    have := hm4 c
    obtain ⟨r, hr⟩ := h.closed c
    split_ifs <;> omega
  have hsum2 : ∑ c : α, (2 + 2 * (if cnt T 0 N c = 4 then 1 else 0))
      = 2 * Fintype.card α + 2 * #{c : α | cnt T 0 N c = 4} := by
    rw [sum_add_distrib, ← mul_sum, ← card_filter]
    simp only [sum_const, card_univ, smul_eq_mul]
    omega
  have hge : m ≤ #{c : α | cnt T 0 N c = 4} := by
    have := sum_le_sum hpt
    rw [hsum, hsum2] at this
    omega
  have hle2 : #{c : α | cnt T 0 N c = 4} ≤ m := by
    by_contra hcon
    rw [not_le] at hcon
    have h1 : (m + 1) * (4 * L - N) ≤ #{c : α | cnt T 0 N c = 4} * (4 * L - N) :=
      Nat.mul_le_mul_right _ hcon
    omega
  have heq : #{c : α | cnt T 0 N c = 4} = m := le_antisymm hle2 hge
  refine ⟨heq, ?_⟩
  have hsumeq : ∑ c, cnt T 0 N c = ∑ c : α, (2 + 2 * (if cnt T 0 N c = 4 then 1 else 0)) := by
    rw [hsum, hsum2, heq]
    exact hm
  have hall := (sum_eq_sum_iff_of_le hpt).mp hsumeq
  intro c
  have := hall c (mem_univ c)
  by_cases hc : cnt T 0 N c = 4
  · exact Or.inl hc
  · right
    rw [if_neg hc] at this
    omega

/-- number of F positions in the window `[t, t+Lw)` -/
def Fcount (T : ℕ → α) (N t Lw : ℕ) : ℕ := #{j ∈ range Lw | cnt T 0 N (T (t + j)) = 4}

/-- **(S3a)**: the type word is balanced. -/
theorem balanced (h : IsCoilWord k N T) (hk : 1 ≤ k) (hN : 2 * k + 2 ≤ N) {m : ℕ}
    (hF : #{c : α | cnt T 0 N c = 4} = m) {t Lw : ℕ} (h1 : k ≤ Lw) (h2 : Lw ≤ 2 * (k + 1))
    (h3 : Lw + k ≤ N) :
    Fcount T N t Lw ≤ m + (Lw - k) / 2 := by
  have hP := P_le h hk hN (t := t) h1 h2 h3
  -- F positions = sum over F coordinates of their counts
  have e1 : Fcount T N t Lw = ∑ c : α, if cnt T 0 N c = 4 then cnt T t Lw c else 0 := by
    rw [Fcount, card_filter]
    have : ∀ j ∈ range Lw, (if cnt T 0 N (T (t + j)) = 4 then 1 else 0)
        = ∑ c : α, if T (t + j) = c then (if cnt T 0 N c = 4 then 1 else 0) else 0 := by
      intro j _
      rw [sum_ite_eq]
      simp
    rw [sum_congr rfl this, sum_comm]
    apply sum_congr rfl
    intro c _
    by_cases hc : cnt T 0 N c = 4
    · simp only [hc, if_true]
      rw [cnt_eq_sum]
    · simp [hc]
  -- each F coordinate occurs once or twice in the window
  have e2 : ∀ c ∈ (univ : Finset α), (if cnt T 0 N c = 4 then cnt T t Lw c else 0)
      ≤ (if cnt T 0 N c = 4 then 1 else 0) + (if cnt T t Lw c = 2 then 1 else 0) := by
    intro c _
    by_cases hc : cnt T 0 N c = 4
    · have hle := cnt_le_two h hk hN (t := t) h2 c
      rw [if_pos hc, if_pos hc]
      split_ifs <;> omega
    · rw [if_neg hc, if_neg hc]
      omega
  have e3 := sum_le_sum e2
  rw [sum_add_distrib, ← card_filter, ← P_eq_sum, hF, ← e1] at e3
  omega

end Coil

#print axioms Coil.structure_S1
#print axioms Coil.balanced
