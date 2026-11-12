import Ccformal.Path
import Ccformal.Trivial

/-!
# Spread-`k` paths for `d ≤ 3k/2 + 1`: Douglas' remark (8)      (S178)

Douglas (1969, 'Further remarks' (8), stated without proof): the maximum length of a spread-`k` path in the `d`-cube is
`2d - k` for `d ≤ ⌊3k/2⌋` and for `d = ⌊3k/2⌋ + 1`, `k` odd; and `2d - k + 1 = 2k + 3` for `d = 3k/2 + 1`, `k` even.

* `path_bound_low`:  `k ≤ d`, `2d ≤ 3k + 1`  ⟹  `L ≤ 2d - k`               (two pieces + parity)
* `path_bound_douglas_even`: `k` even, `4d ≤ 6k + 5` ⟹ `L ≤ 2k + 3`          (three windows, LP certificate)
* `trivial_path`: the word `0 1 … d-1 0 1 … d-k-1` is a spread-`k` path with `2d - k` edges (`k ≤ d`)
* `maxPath_low`: `P(d,k) = 2d - k` for `k ≤ d`, `2d ≤ 3k + 1`.
(The path of length `2k+3` for `d = 3k/2+1`, `k` even: `PathDouglasWord.lean`, `maxPath_douglas_even`.)
-/

open Finset

namespace Coil

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {α : Type*} [Fintype α] [DecidableEq α] {k L : ℕ} {T : ℕ → α}

/-- a path word gives a path in the cube (vertex `i` = parity vector of the first `i` steps) -/
theorem IsPathWord.exists_path (h : IsPathWord k L T) : ∃ v : ℕ → α → Bool, IsPath k L v := by
  let v : ℕ → α → Bool := fun i c => decide (Odd (cnt T 0 i c))
  have key : ∀ t w c, v t c ≠ v (t + w) c ↔ Odd (cnt T t w c) := by
    intro t w c
    have e : cnt T 0 (t + w) c = cnt T 0 t c + cnt T t w c := by
      rw [cnt_add, zero_add]
    simp only [v, e, ne_eq, decide_eq_decide, Nat.odd_iff]
    omega
  have hdo : ∀ t w, hd (v t) (v (t + w)) = oddc T t w := by
    intro t w
    rw [hd, oddc]
    exact congrArg card (filter_congr fun c _ => key t w c)
  refine ⟨v, ?_, ?_⟩
  · intro i
    rw [hdo]
    have : ∀ c, Odd (cnt T i 1 c) ↔ T i = c := by
      intro c
      rw [cnt_one]
      split_ifs with h' <;> simp [h']
    rw [oddc, filter_congr (fun c _ => this c), Finset.filter_eq]
    simp
  · intro i w hw
    rw [hdo]
    exact h.spread i w hw

lemma pat2 : ∀ a1 < 2, ∀ a2 < 2, (if Odd (a1 + a2) then 1 else 0) + (a1 + a2) ≤ 2 := by decide

/-- **Douglas' range, upper bound**: `k ≤ d`, `2d ≤ 3k+1`: at most `2d - k` edges. -/
theorem path_bound_low (h : IsPathWord k L T) (hkd : k ≤ Fintype.card α)
    (hd : 2 * Fintype.card α ≤ 3 * k + 1) : L + k ≤ 2 * Fintype.card α := by
  by_contra hc
  obtain ⟨u, hu⟩ : ∃ u, u + k = 2 * Fintype.card α + 1 := ⟨2 * Fintype.card α + 1 - k, by omega⟩
  obtain ⟨x1, x2, hx, hx1, hx2⟩ : ∃ x1 x2, x1 + x2 = u ∧ x1 ≤ k + 1 ∧ x2 ≤ k + 1 := by
    by_cases hm : u ≤ k + 1
    · exact ⟨u, 0, by omega, hm, by omega⟩
    · exact ⟨k + 1, u - (k + 1), by omega, le_refl _, by omega⟩
  have key : ∀ c : α, (if Odd (cnt T 0 (x1 + x2) c) then 1 else 0) + cnt T 0 (x1 + x2) c ≤ 2 := by
    intro c
    have b1 := h.cnt_le_one (s := 0) (w := x1) (by omega) hx1 c
    have b2 := h.cnt_le_one (s := 0 + x1) (w := x2) (by omega) hx2 c
    rw [cnt_add T 0 x1 x2 c]
    exact pat2 _ (by omega) _ (by omega)
  have S := sum_le_sum (fun c (_ : c ∈ (univ : Finset α)) => key c)
  simp only [sum_add_distrib, ← oddc_eq_sum, sum_cnt, sum_const, card_univ, smul_eq_mul] at S
  have g := h.gt (s := 0) (w := x1 + x2) (by omega) (by omega) (by omega)
  omega

lemma pat6 : ∀ a0 < 2, ∀ a1 < 2, ∀ a2 < 2, ∀ a3 < 2, ∀ a4 < 2, ∀ a5 < 2,
    a0 + a1 ≤ 1 → a1 + a2 ≤ 1 → a2 + a3 ≤ 1 → a3 + a4 ≤ 1 → a4 + a5 ≤ 1 →
    (if Odd (a0 + a1 + a2 + a3 + a4) then 1 else 0) + (if Odd (a1 + a2 + a3 + a4 + a5) then 1 else 0)
      + (if Odd (a0 + a1 + a2 + a3) then 1 else 0) + (a1 + a2 + a3 + 2 * a4 + a5) ≤ 4 := by
  intro a0 h0 a1 h1 a2 h2 a3 h3 a4 h4 a5 h5 c1 c2 c3 c4 c5
  interval_cases a0 <;> interval_cases a1 <;> interval_cases a2 <;> interval_cases a3 <;> interval_cases a4 <;>
    interval_cases a5 <;> first | omega | decide

/-- three windows `[0, 2k+3)`, `[1, 2k+4)`, `[0, k+3)` of a path word of length `2k+4` -/
theorem three_windows (h : IsPathWord k (2 * k + 4) T) (hk1 : 1 ≤ k) :
    oddc T 0 (2 * k + 3) + oddc T 1 (2 * k + 3) + oddc T 0 (k + 3) + (3 * k + 3) ≤ 4 * Fintype.card α := by
  have key : ∀ c : α,
      (if Odd (cnt T 0 (2 * k + 3) c) then 1 else 0) + (if Odd (cnt T 1 (2 * k + 3) c) then 1 else 0)
        + (if Odd (cnt T 0 (k + 3) c) then 1 else 0)
        + (cnt T 1 k c + cnt T (k + 1) 1 c + cnt T (k + 2) 1 c + 2 * cnt T (k + 3) k c + cnt T (2 * k + 3) 1 c) ≤ 4 := by
    intro c
    have q1 := cnt_pre T (x := 1) (w := k) (y := k + 1) (by omega) c
    have q2 := cnt_pre T (x := k + 1) (w := 1) (y := k + 2) (by omega) c
    have q3 := cnt_pre T (x := k + 2) (w := 1) (y := k + 3) (by omega) c
    have q4 := cnt_pre T (x := k + 3) (w := k) (y := 2 * k + 3) (by omega) c
    have q5 := cnt_pre T (x := 2 * k + 3) (w := 1) (y := 2 * k + 4) (by omega) c
    have w2 := cnt_pre T (x := 1) (w := 2 * k + 3) (y := 2 * k + 4) (by omega) c
    have c1 := h.cnt_le_one (s := 0) (w := k + 1) (by omega) (by omega) c
    have c2 := h.cnt_le_one (s := 1) (w := k + 1) (by omega) (by omega) c
    have c3 := h.cnt_le_one (s := k + 1) (w := 2) (by omega) (by omega) c
    have c4 := h.cnt_le_one (s := k + 2) (w := k + 1) (by omega) (by omega) c
    have c5 := h.cnt_le_one (s := k + 3) (w := k + 1) (by omega) (by omega) c
    have d2 := cnt_pre T (x := 1) (w := k + 1) (y := k + 2) (by omega) c
    have d3 := cnt_pre T (x := k + 1) (w := 2) (y := k + 3) (by omega) c
    have d4 := cnt_pre T (x := k + 2) (w := k + 1) (y := 2 * k + 3) (by omega) c
    have d5 := cnt_pre T (x := k + 3) (w := k + 1) (y := 2 * k + 4) (by omega) c
    have P := pat6 (cnt T 0 1 c) (by omega) (cnt T 1 k c) (by omega) (cnt T (k + 1) 1 c) (by omega)
      (cnt T (k + 2) 1 c) (by omega) (cnt T (k + 3) k c) (by omega) (cnt T (2 * k + 3) 1 c) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
    rw [show cnt T 0 (2 * k + 3) c
          = cnt T 0 1 c + cnt T 1 k c + cnt T (k + 1) 1 c + cnt T (k + 2) 1 c + cnt T (k + 3) k c by omega,
      show cnt T 1 (2 * k + 3) c
          = cnt T 1 k c + cnt T (k + 1) 1 c + cnt T (k + 2) 1 c + cnt T (k + 3) k c + cnt T (2 * k + 3) 1 c by omega,
      show cnt T 0 (k + 3) c = cnt T 0 1 c + cnt T 1 k c + cnt T (k + 1) 1 c + cnt T (k + 2) 1 c by omega]
    exact P
  have S := sum_le_sum (fun c (_ : c ∈ (univ : Finset α)) => key c)
  simp only [sum_add_distrib, ← oddc_eq_sum, ← mul_sum, sum_cnt, sum_const, card_univ, smul_eq_mul] at S
  omega

/-- **Douglas' boundary case**: `k` even, `d ≤ 3k/2 + 1`: at most `2k + 3` edges. -/
theorem path_bound_douglas_even (h : IsPathWord k L T) (hk : Even k) (hk1 : 1 ≤ k)
    (hd : 4 * Fintype.card α ≤ 6 * k + 5) : L ≤ 2 * k + 3 := by
  by_contra hc
  have hk2 : k % 2 = 0 := Nat.even_iff.mp hk
  have h' : IsPathWord k (2 * k + 4) T := h.mono (by omega)
  have W := three_windows h' hk1
  have g1 := h'.gt (s := 0) (w := 2 * k + 3) (by omega) (by omega) (by omega)
  have g2 := h'.gt (s := 1) (w := 2 * k + 3) (by omega) (by omega) (by omega)
  have g3 := h'.gt (s := 0) (w := k + 3) (by omega) (by omega) (by omega)
  omega

/-! ## Lower bound: the word `0 1 … d-1 0 1 … d-k-1` -/

lemma trivWord_cnt_full (d : ℕ) [NeZero d] (t : ℕ) (c : Fin d) : cnt (trivWord d) t d c = 1 := by
  have h1 : ∀ c, cnt (trivWord d) t d c ≤ 1 := fun c => trivWord_cnt_le_one d t d le_rfl c
  have hs := sum_cnt (trivWord d) t d
  by_contra hne
  have hlt : ∑ c : Fin d, cnt (trivWord d) t d c < ∑ c : Fin d, 1 := by
    apply sum_lt_sum
    · intro c _; exact h1 c
    · exact ⟨c, mem_univ _, by have := h1 c; omega⟩
  simp at hlt
  omega

theorem trivial_pathWord (d k L : ℕ) [NeZero d] (hL : L + k ≤ 2 * d) : IsPathWord k L (trivWord d) := by
  refine ⟨fun s w hs hw => ?_⟩
  by_cases hwd : w ≤ d
  · exact oddc_eq_of_le_one (fun c => trivWord_cnt_le_one d s w hwd c)
  · exfalso
    obtain ⟨r, rfl⟩ : ∃ r, w = d + r := ⟨w - d, by omega⟩
    have h1 : ∀ c, cnt (trivWord d) (s + d) r c ≤ 1 := fun c => trivWord_cnt_le_one d (s + d) r (by omega) c
    have e : oddc (trivWord d) s (d + r) + r = d := by
      have e1 : oddc (trivWord d) s (d + r) = ∑ c : Fin d, (1 - cnt (trivWord d) (s + d) r c) := by
        rw [oddc_eq_sum]
        apply sum_congr rfl
        intro c _
        rw [cnt_add, trivWord_cnt_full]
        have := h1 c
        rcases Nat.lt_or_ge (cnt (trivWord d) (s + d) r c) 1 with h0 | h0
        · have : cnt (trivWord d) (s + d) r c = 0 := by omega
          simp [this]
        · have : cnt (trivWord d) (s + d) r c = 1 := by omega
          simp [this]
      have e2 : ∑ c : Fin d, (1 - cnt (trivWord d) (s + d) r c) + ∑ c : Fin d, cnt (trivWord d) (s + d) r c
          = ∑ c : Fin d, 1 := by
        rw [← sum_add_distrib]
        apply sum_congr rfl
        intro c _
        have := h1 c
        omega
      rw [sum_cnt] at e2
      simp at e2
      omega
    omega

theorem trivial_path (d k L : ℕ) [NeZero d] (hL : L + k ≤ 2 * d) : ∃ v : ℕ → Fin d → Bool, IsPath k L v :=
  (trivial_pathWord d k L hL).exists_path

/-- `L` is the maximum number of edges of a spread-`k` path in the `d`-cube: `P(d,k) = L` -/
def IsMaxPath (d k L : ℕ) : Prop :=
  (∃ v : ℕ → Fin d → Bool, IsPath k L v) ∧ ∀ (L' : ℕ) (v' : ℕ → Fin d → Bool), IsPath k L' v' → L' ≤ L

/-- **Douglas' remark (8), first part**: `P(d,k) = 2d - k` for `k ≤ d ≤ (3k+1)/2`. -/
theorem maxPath_low (d k L : ℕ) (hk : 1 ≤ k) (hkd : k ≤ d) (hd : 2 * d ≤ 3 * k + 1) (hL : L + k = 2 * d) :
    IsMaxPath d k L := by
  have : NeZero d := ⟨by omega⟩
  refine ⟨trivial_path d k L (by omega), fun L' v' h' => ?_⟩
  obtain ⟨T, hT, _⟩ := h'.exists_word
  have := path_bound_low hT (by simpa using hkd) (by simpa using hd)
  simp at this
  omega

end Coil

#print axioms Coil.maxPath_low
#print axioms Coil.path_bound_douglas_even
