import Ccformal.KmaxUpper

/-!
# A sufficient criterion for transition words (the 'Reduction' step of every family proof)

To show that an `N`-periodic word is the transition word of a spread-`k` circuit code it suffices to check:
every coordinate is used an even number of times per period, any `k+1` consecutive transitions are distinct,
and `odd(W) ≥ k` for the windows with `k+1 ≤ L ≤ N/2`  (short windows are then automatic, and a window and its
complement have the same odd coordinates).   For the lower-bound (family) proofs, none of which is formalized yet.
-/

open Finset

namespace Coil

set_option linter.unusedSectionVars false

variable {α : Type*} [Fintype α] [DecidableEq α] {k N : ℕ} {T : ℕ → α}

lemma cnt_mono (T : ℕ → α) (t : ℕ) {L L' : ℕ} (h : L ≤ L') (c : α) : cnt T t L c ≤ cnt T t L' c := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [cnt_add]
  omega

lemma oddc_eq_of_le_one {t L : ℕ} (h : ∀ c, cnt T t L c ≤ 1) : oddc T t L = L := by
  rw [oddc_eq_sum]
  conv_rhs => rw [← sum_cnt T t L]
  apply sum_congr rfl
  intro c _
  have := h c
  simp only [Nat.odd_iff]
  split_ifs <;> omega

lemma oddc_compl (per : ∀ i, T (i + N) = T i) (closed : ∀ c, Even (cnt T 0 N c)) (t : ℕ) {L : ℕ}
    (hL : L ≤ N) : oddc T t L = oddc T (t + L) (N - L) := by
  rw [oddc, oddc]
  apply congrArg
  apply filter_congr
  intro c _
  obtain ⟨r, hr⟩ := closed c
  have e : cnt T t N c = cnt T t L c + cnt T (t + L) (N - L) c := by
    rw [← cnt_add, show L + (N - L) = N by omega]
  rw [cnt_period per] at e
  rw [Nat.odd_iff, Nat.odd_iff]
  omega

theorem isCoilWord_of_windows (hN : 2 * k + 2 ≤ N) (per : ∀ i, T (i + N) = T i)
    (closed : ∀ c, Even (cnt T 0 N c)) (hdist : ∀ t c, cnt T t (k + 1) c ≤ 1)
    (hmid : ∀ t L, k + 1 ≤ L → 2 * L ≤ N → k ≤ oddc T t L) : IsCoilWord k N T := by
  refine ⟨per, closed, ?_⟩
  intro t L h1 h2 h3
  have hshort : ∀ s M, M ≤ k + 1 → oddc T s M = M := by
    intro s M hM
    exact oddc_eq_of_le_one (fun c => le_trans (cnt_mono T s hM c) (hdist s c))
  by_cases hLk : L ≤ k
  · rw [hshort t L (by omega)]
    omega
  · by_cases hNL : N - L ≤ k
    · rw [oddc_compl per closed t (by omega), hshort (t + L) (N - L) (by omega)]
      omega
    · exfalso
      by_cases h2L : 2 * L ≤ N
      · have := hmid t L (by omega) h2L
        omega
      · have := hmid (t + L) (N - L) (by omega) (by omega)
        rw [← oddc_compl per closed t (by omega)] at this
        omega

/-- consequently such a word gives a circuit code in the cube -/
theorem exists_coil_of_windows (hN : 2 * k + 2 ≤ N) (per : ∀ i, T (i + N) = T i)
    (closed : ∀ c, Even (cnt T 0 N c)) (hdist : ∀ t c, cnt T t (k + 1) c ≤ 1)
    (hmid : ∀ t L, k + 1 ≤ L → 2 * L ≤ N → k ≤ oddc T t L) :
    ∃ v : ℕ → α → Bool, IsCoil k N v :=
  (isCoilWord_of_windows hN per closed hdist hmid).exists_coil

end Coil

#print axioms Coil.exists_coil_of_windows
