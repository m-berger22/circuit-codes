import Ccformal.Criterion
import Mathlib.Data.Nat.Nth

/-!
# Deimer's contraction (1984), for a set of coordinates

If a spread-`k` circuit code of length `N` uses each coordinate of a set `C` (`|C| = j < k`) exactly twice, then
deleting these coordinates (and the `2j` steps that flip them) gives a spread-`(k-j)` circuit code of length `N - 2j`
in the cube without the coordinates of `C`.  On the `(k,l)` lines: `(n,k,N) → (n-j, k-j, N-2j)`, `l → l+j`, same excess.
-/

open Finset

namespace Coil

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {α : Type*} [Fintype α] [DecidableEq α] {k N : ℕ} {T : ℕ → α}

/-- transport of a coil word along a bijection of the coordinates -/
theorem IsCoilWord.map_equiv {β : Type*} [Fintype β] [DecidableEq β] (e : α ≃ β) (h : IsCoilWord k N T) :
    IsCoilWord k N (fun i => e (T i)) := by
  have hc : ∀ t L y, cnt (fun i => e (T i)) t L y = cnt T t L (e.symm y) := by
    intro t L y
    rw [cnt, cnt]
    exact congrArg card (filter_congr fun i _ => (Equiv.eq_symm_apply e).symm)
  have ho : ∀ t L, oddc (fun i => e (T i)) t L = oddc T t L := by
    intro t L
    rw [oddc_eq_sum, oddc_eq_sum]
    simp_rw [hc]
    exact Equiv.sum_comp e.symm (fun x => if Odd (cnt T t L x) then 1 else 0)
  refine ⟨fun i => congrArg e (h.per i), fun c => ?_, fun t L h1 h2 h3 => ?_⟩
  · rw [hc]; exact h.closed _
  · rw [ho] at h3 ⊢; exact h.spread t L h1 h2 h3

/-- positions of the window whose coordinate lies in `C` -/
lemma card_mem_window (T : ℕ → α) (C : Finset α) (t L : ℕ) :
    #{i ∈ range L | T (t + i) ∈ C} = ∑ c ∈ C, cnt T t L c := by
  simp_rw [cnt_eq_sum]
  rw [card_filter, sum_comm]
  apply sum_congr rfl
  intro i _
  rw [Finset.sum_ite_eq]

lemma card_split_window (T : ℕ → α) (C : Finset α) (t L : ℕ) :
    #{i ∈ range L | T (t + i) ∉ C} + ∑ c ∈ C, cnt T t L c = L := by
  rw [← card_mem_window, card_filter, card_filter, ← sum_add_distrib]
  have : ∀ i ∈ range L, ((if T (t + i) ∉ C then 1 else 0) + if T (t + i) ∈ C then 1 else 0) = 1 := by
    intro i _
    split_ifs <;> simp_all
  rw [sum_congr rfl this]
  simp

section contraction

variable (C : Finset α) (h : IsCoilWord k N T) (hC : ∀ c ∈ C, cnt T 0 N c = 2) (hj : 2 * #C < N)

include h hC in
lemma count_shift (x : ℕ) : Nat.count (fun i => T i ∉ C) (x + N) = Nat.count (fun i => T i ∉ C) x + (N - 2 * #C) := by
  rw [Nat.count_add]
  congr 1
  rw [Nat.count_eq_card_filter_range]
  have h1 := card_split_window T C x N
  have h2 : ∑ c ∈ C, cnt T x N c = 2 * #C := by
    rw [sum_congr rfl (fun c hc => by rw [cnt_period h.per x c, hC c hc]), sum_const, smul_eq_mul, mul_comm]
  omega

include h hC hj in
lemma inf_notC : (Set.ofPred (fun i => T i ∉ C)).Infinite := by
  have h1 := card_split_window T C 0 N
  have h2 : ∑ c ∈ C, cnt T 0 N c = 2 * #C := by
    rw [sum_congr rfl (fun c hc => by rw [hC c hc]), sum_const, smul_eq_mul, mul_comm]
  have hpos : 0 < #{i ∈ range N | T (0 + i) ∉ C} := by omega
  obtain ⟨x0, hx0⟩ := card_pos.mp hpos
  simp only [mem_filter, mem_range, zero_add] at hx0
  apply Set.infinite_of_injective_forall_mem (f := fun m : ℕ => x0 + m * N)
  · intro m1 m2 he
    have hN : 0 < N := by omega
    simp only at he
    have : m1 * N = m2 * N := by omega
    exact Nat.eq_of_mul_eq_mul_right hN this
  · intro m
    show T (x0 + m * N) ∉ C
    rw [per_mul h.per]
    exact hx0.2

/-- the bijection between the surviving positions of a window and the positions of the contracted window -/
lemma card_window_nth (hinf : (Set.ofPred (fun i => T i ∉ C)).Infinite) (q : α → Prop) [DecidablePred q]
    (hq : ∀ x, q x → x ∉ C) (t' L' : ℕ) :
    #{j ∈ range L' | q (T (Nat.nth (fun i => T i ∉ C) (t' + j)))}
      = #{i ∈ range (Nat.nth (fun i => T i ∉ C) (t' + L') - Nat.nth (fun i => T i ∉ C) t') |
          q (T (Nat.nth (fun i => T i ∉ C) t' + i))} := by
  set σ := Nat.nth (fun i => T i ∉ C) with hσ
  have mono : ∀ {a b}, a ≤ b → σ a ≤ σ b := fun hab => (Nat.nth_le_nth hinf).mpr hab
  have smono : ∀ {a b}, a < b → σ a < σ b := fun hab => (Nat.nth_lt_nth hinf).mpr hab
  apply Finset.card_bij (fun j _ => σ (t' + j) - σ t')
  · intro j hj
    simp only [mem_filter, mem_range] at hj ⊢
    have h1 := mono (Nat.le_add_right t' j)
    have h2 := smono (Nat.add_lt_add_left hj.1 t')
    refine ⟨by omega, ?_⟩
    rw [Nat.add_sub_cancel' h1]
    exact hj.2
  · intro j1 hj1 j2 hj2 he
    have h1 := mono (Nat.le_add_right t' j1)
    have h2 := mono (Nat.le_add_right t' j2)
    have : σ (t' + j1) = σ (t' + j2) := by omega
    have := Nat.nth_injective hinf this
    omega
  · intro i hi
    simp only [mem_filter, mem_range] at hi
    have hp : T (σ t' + i) ∉ C := hq _ hi.2
    have hidx : σ (Nat.count (fun i => T i ∉ C) (σ t' + i)) = σ t' + i := Nat.nth_count hp
    set idx := Nat.count (fun i => T i ∉ C) (σ t' + i) with hidxdef
    have ha : t' ≤ idx := by
      rw [← Nat.nth_le_nth hinf, ← hσ, hidx]
      omega
    have hb : idx < t' + L' := by
      rw [← Nat.nth_lt_nth hinf, ← hσ, hidx]
      have := mono (Nat.le_add_right t' L')
      omega
    refine ⟨idx - t', ?_, ?_⟩
    · simp only [mem_filter, mem_range]
      refine ⟨by omega, ?_⟩
      rw [Nat.add_sub_cancel' ha, hidx]
      exact hi.2
    · rw [Nat.add_sub_cancel' ha, hidx]
      omega

include h hC hj in
/-- **Deimer's contraction.** -/
theorem contraction (hN : 2 * k + 2 ≤ N) (hjk : #C < k) :
    ∃ T' : ℕ → {x // x ∉ C}, IsCoilWord (k - #C) (N - 2 * #C) T' ∧
      ∀ y, cnt T' 0 (N - 2 * #C) y = cnt T 0 N y.1 := by
  have hinf := inf_notC C h hC hj
  set σ := Nat.nth (fun i => T i ∉ C) with hσ
  have mono : ∀ {a b}, a ≤ b → σ a ≤ σ b := fun hab => (Nat.nth_le_nth hinf).mpr hab
  have smono : ∀ {a b}, a < b → σ a < σ b := fun hab => (Nat.nth_lt_nth hinf).mpr hab
  have hmem : ∀ i, T (σ i) ∉ C := fun i => Nat.nth_mem_of_infinite hinf i
  -- σ is 'periodic'
  have hper : ∀ i, σ (i + (N - 2 * #C)) = σ i + N := by
    intro i
    have hp : T (σ i + N) ∉ C := by rw [h.per]; exact hmem i
    have h1 := Nat.nth_count (p := fun i => T i ∉ C) hp
    rw [count_shift C h hC, Nat.count_nth_of_infinite hinf] at h1
    exact h1
  let T' : ℕ → {x // x ∉ C} := fun i => ⟨T (σ i), hmem i⟩
  -- counts
  have hcnt : ∀ t' L' (y : {x // x ∉ C}), cnt T' t' L' y = cnt T (σ t') (σ (t' + L') - σ t') y.1 := by
    intro t' L' y
    rw [cnt, cnt]
    have := card_window_nth C hinf (fun x => x = y.1) (fun x hx => by rw [hx]; exact y.2) t' L'
    rw [← this]
    exact congrArg card (filter_congr fun j _ => Subtype.ext_iff)
  have hlen : ∀ t' L', L' + ∑ c ∈ C, cnt T (σ t') (σ (t' + L') - σ t') c = σ (t' + L') - σ t' := by
    intro t' L'
    have h1 := card_window_nth C hinf (fun x => x ∉ C) (fun x hx => hx) t' L'
    simp only [← hσ] at h1
    have h2 := card_split_window T C (σ t') (σ (t' + L') - σ t')
    have h3 : #{j ∈ range L' | T (σ (t' + j)) ∉ C} = L' := by
      rw [filter_true_of_mem (fun j _ => hmem _), card_range]
    omega
  have hodd : ∀ t' L', oddc T' t' L' + ∑ c ∈ C, (if Odd (cnt T (σ t') (σ (t' + L') - σ t') c) then 1 else 0)
      = oddc T (σ t') (σ (t' + L') - σ t') := by
    intro t' L'
    rw [oddc_eq_sum, oddc_eq_sum]
    simp_rw [hcnt]
    rw [← Finset.sum_subtype (univ.filter (fun x => x ∉ C)) (by simp)
      (fun x => if Odd (cnt T (σ t') (σ (t' + L') - σ t') x) then 1 else 0),
      ← Finset.sum_filter_add_sum_filter_not univ (fun x => x ∈ C)
        (fun x => if Odd (cnt T (σ t') (σ (t' + L') - σ t') x) then 1 else 0)]
    rw [show univ.filter (fun x => x ∈ C) = C by ext; simp]
    omega
  have hfull : ∀ y, cnt T' 0 (N - 2 * #C) y = cnt T 0 N y.1 := by
    intro y
    have h0 := hper 0
    rw [zero_add] at h0
    rw [hcnt, zero_add, h0, Nat.add_sub_cancel_left, cnt_period h.per]
  have per' : ∀ i, T' (i + (N - 2 * #C)) = T' i := by
    intro i
    apply Subtype.ext
    show T (σ (i + (N - 2 * #C))) = T (σ i)
    rw [hper, h.per]
  have closed' : ∀ y, Even (cnt T' 0 (N - 2 * #C) y) := fun y => by rw [hfull]; exact h.closed _
  refine ⟨T', ⟨per', closed', ?_⟩, hfull⟩
  intro t' L' hL1 hL2 hlt
  have hl := hlen t' L'
  have ho := hodd t' L'
  obtain ⟨L, hL⟩ : ∃ L, L = σ (t' + L') - σ t' := ⟨_, rfl⟩
  rw [← hL] at hl ho
  have hLN : L < N := by
    have h1 := smono (Nat.add_lt_add_left hL2 t')
    have h2 := hper t'
    have h3 := mono (Nat.le_add_right t' L')
    omega
  obtain ⟨t, ht⟩ : ∃ t, t = σ t' := ⟨_, rfl⟩
  rw [← ht] at hl ho
  -- A = odd ones, cC = all, cC = A + 2B, A + cC ≤ 2|C|
  have hAB : ∑ c ∈ C, cnt T t L c
      = ∑ c ∈ C, (if Odd (cnt T t L c) then 1 else 0) + 2 * ∑ c ∈ C, cnt T t L c / 2 := by
    rw [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro c _
    split_ifs with hoo
    · rw [Nat.odd_iff] at hoo; omega
    · rw [Nat.not_odd_iff_even, Nat.even_iff] at hoo; omega
  have hA2 : ∑ c ∈ C, (if Odd (cnt T t L c) then 1 else 0) + ∑ c ∈ C, cnt T t L c ≤ 2 * #C := by
    rw [← sum_add_distrib]
    have : ∀ c ∈ C, ((if Odd (cnt T t L c) then 1 else 0) + cnt T t L c) ≤ 2 := by
      intro c hc
      have h1 := cnt_mono T t (le_of_lt hLN) c
      rw [cnt_period h.per, hC c hc] at h1
      split_ifs with hoo
      · rw [Nat.odd_iff] at hoo; omega
      · omega
    have := sum_le_sum this
    rw [sum_const, smul_eq_mul] at this
    omega
  have hsp := h.spread t L (by omega) hLN (by omega)
  have b1 := oddc_le T' t' L'
  have b2 : oddc T' t' L' ≤ N - 2 * #C - L' := by
    rw [oddc_compl per' closed' t' (le_of_lt hL2)]
    exact oddc_le _ _ _
  omega

end contraction

/-- contraction for codes in `Q_n` (coordinates `Fin n`) -/
theorem contraction_fin {n : ℕ} {T : ℕ → Fin n} (h : IsCoilWord k N T) (hN : 2 * k + 2 ≤ N) (C : Finset (Fin n))
    (hC : ∀ c ∈ C, cnt T 0 N c = 2) (hjk : #C < k) :
    ∃ T'' : ℕ → Fin (n - #C), IsCoilWord (k - #C) (N - 2 * #C) T'' := by
  obtain ⟨T', hT', _⟩ := contraction C h hC (by omega) hN hjk
  have hcard : Fintype.card {x : Fin n // x ∉ C} = n - #C := by
    rw [Fintype.card_subtype, show univ.filter (fun x => x ∉ C) = Cᶜ by ext; simp, card_compl, Fintype.card_fin]
  exact ⟨_, hT'.map_equiv (Fintype.equivFinOfCardEq hcard)⟩

end Coil

#print axioms Coil.contraction_fin
