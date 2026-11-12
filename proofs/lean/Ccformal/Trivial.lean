import Ccformal.Criterion

/-!
# The first exact value for infinitely many `(n,k)` with a formal LOWER bound: the trivial code

For `k + 1 ≤ n` and `2n + 2 ≤ 3k`:  `K(n,k) = 2n`  (the classical range `n < 3k/2`, Singleton / Douglas).
Lower bound: the code that flips the coordinates `0, 1, …, n-1, 0, 1, …, n-1` (via `exists_coil_of_windows`).
Upper bound: Lemma 1 at `L = k+1` (for `N ≤ 4k+3`) and at `L = 2k` (for `4k+4 ≤ N ≤ 5k+3`), Lemma 2 beyond.
This is not new mathematics; it is the template for the family (lower-bound) proofs.
-/

open Finset

namespace Coil

set_option linter.unusedSectionVars false
set_option linter.deprecated false

/-- the trivial transition word `0, 1, …, n-1, 0, 1, …` -/
def trivWord (n : ℕ) [NeZero n] : ℕ → Fin n := fun i => ⟨i % n, Nat.mod_lt _ (NeZero.pos n)⟩

lemma trivWord_cnt_le_one (n : ℕ) [NeZero n] (t L : ℕ) (hL : L ≤ n) (c : Fin n) :
    cnt (trivWord n) t L c ≤ 1 := by
  by_contra hcon
  rw [not_le, cnt] at hcon
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hcon
  simp only [mem_filter, mem_range] at hi hj
  have e : (t + i) % n = (t + j) % n := by
    have h1 := congrArg Fin.val hi.2
    have h2 := congrArg Fin.val hj.2
    simp only [trivWord] at h1 h2
    rw [h1, h2]
  rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
  · have := Nat.sub_mod_eq_zero_of_mod_eq e.symm
    rw [show t + j - (t + i) = j - i by omega, Nat.mod_eq_of_lt (by omega)] at this
    omega
  · have := Nat.sub_mod_eq_zero_of_mod_eq e
    rw [show t + i - (t + j) = i - j by omega, Nat.mod_eq_of_lt (by omega)] at this
    omega

theorem trivial_coil (n k : ℕ) [NeZero n] (hkn : k + 1 ≤ n) :
    ∃ v : ℕ → Fin n → Bool, IsCoil k (n + n) v := by
  apply exists_coil_of_windows (T := trivWord n) (by omega)
  · intro i
    apply Fin.ext
    simp [trivWord, ← add_assoc]
  · intro c
    refine ⟨cnt (trivWord n) 0 n c, ?_⟩
    rw [cnt_add]
    congr 1
    simp only [cnt, trivWord]
    congr 1
    apply filter_congr
    intro j _
    simp
  · intro t c
    exact trivWord_cnt_le_one n t (k + 1) hkn c
  · intro t L h1 h2
    rw [oddc_eq_of_le_one (fun c => trivWord_cnt_le_one n t L (by omega) c)]
    omega

variable {α : Type*} [Fintype α] [DecidableEq α] {k N : ℕ} {T : ℕ → α}

theorem trivial_upper (h : IsCoilWord k N T) (n : ℕ) (hk : 2 ≤ k) (hkn : k + 1 ≤ n)
    (hn : Fintype.card α = n) (h3 : 2 * n + 2 ≤ 3 * k) : N ≤ 2 * n := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨m, hm⟩ := even_length h
  have hk1 : 1 ≤ k := by omega
  have hNz : (2 * n : ℤ) + 2 ≤ N := by exact_mod_cast (by omega : 2 * n + 2 ≤ N)
  have h3z : (2 * n : ℤ) + 2 ≤ 3 * k := by exact_mod_cast h3
  by_cases hA : N ≤ 4 * k + 3
  · have C := chord_inequality h hk1 (by omega) (by omega) (L := k + 1) (by omega) (by omega)
      (by omega) (by omega)
    rw [hn, show (k + 1 - k) / 2 = 0 by omega] at C
    have p1 : (0 : ℤ) < (N : ℤ) - 2 * n := by linarith
    have p2 : (0 : ℤ) < 4 * ((k + 1 : ℕ) : ℤ) - N := by
      have : (N : ℤ) ≤ 4 * k + 3 := by exact_mod_cast hA
      push_cast
      linarith
    have := mul_pos p1 p2
    rw [Nat.cast_zero, mul_zero] at C
    linarith
  · by_cases hB : N ≤ 5 * k + 3
    · have C := chord_inequality h hk1 (by omega) (by omega) (L := 2 * k) (by omega) (by omega)
        (by omega) (by omega)
      rw [hn, show (2 * k - k) / 2 = k / 2 by omega] at C
      have hhalf : (2 : ℤ) * ((k / 2 : ℕ) : ℤ) ≤ k := by exact_mod_cast Nat.mul_div_le k 2
      have a1 : (0 : ℤ) ≤ (N : ℤ) - 4 * k - 4 := by
        have : (4 * k + 4 : ℤ) ≤ N := by exact_mod_cast (by omega : 4 * k + 4 ≤ N)
        linarith
      have a2 : (0 : ℤ) ≤ 5 * (k : ℤ) + 3 - N := by
        have : (N : ℤ) ≤ 5 * k + 3 := by exact_mod_cast hB
        linarith
      have hkz : (2 : ℤ) ≤ k := by exact_mod_cast hk
      have p2 : (0 : ℤ) < 8 * (k : ℤ) - N := by linarith
      have hNpos : (0 : ℤ) ≤ N := by positivity
      -- (N - 3k + 2)(8k - N) ≤ (N - 2n)(8k - N) ≤ N k
      have s1 : ((N : ℤ) - 3 * k + 2) * (8 * k - N) ≤ ((N : ℤ) - 2 * n) * (8 * k - N) :=
        mul_le_mul_of_nonneg_right (by linarith) (le_of_lt p2)
      have s2 : ((N : ℤ) - 2 * n) * (8 * k - N) ≤ N * k := by
        have e2 : ((2 * k : ℕ) : ℤ) = 2 * k := by push_cast; ring
        rw [e2] at C
        have : 2 * (N : ℤ) * ((k / 2 : ℕ) : ℤ) ≤ N * k := by nlinarith
        have e : (4 : ℤ) * (2 * k) - N = 8 * k - N := by ring
        rw [e] at C
        linarith
      have q1 := mul_nonneg a1 a2
      by_cases h9 : 9 ≤ k
      · have hk9 : (0 : ℤ) ≤ (k : ℤ) - 9 := by
          have : (9 : ℤ) ≤ k := by exact_mod_cast h9
          linarith
        nlinarith [mul_nonneg a1 hk9]
      · have hk8 : (0 : ℤ) ≤ 9 - (k : ℤ) := by
          have : (k : ℤ) ≤ 8 := by exact_mod_cast (by omega : k ≤ 8)
          linarith
        have q2 := mul_nonneg hk8 a2
        have hpos : (0 : ℤ) < (k : ℤ) * k + 6 * k - 15 := by nlinarith
        nlinarith
    · have := no_long h hk1 (by omega)
      rw [hn] at this
      omega

/-- **`K(n,k) = 2n` for `k + 1 ≤ n ≤ (3k-2)/2`** -- lower AND upper bound formal, for all such `(n,k)`. -/
theorem K_trivial (n k : ℕ) (hk : 2 ≤ k) (hkn : k + 1 ≤ n) (h3 : 2 * n + 2 ≤ 3 * k) :
    IsMaxLength n k (2 * n) := by
  have : NeZero n := ⟨by omega⟩
  refine ⟨?_, fun N' v' h' => ?_⟩
  · rw [show 2 * n = n + n by ring]
    exact trivial_coil n k hkn
  · obtain ⟨T, hT, _⟩ := h'.exists_word
    exact trivial_upper hT n hk hkn (Fintype.card_fin n) h3

end Coil

#print axioms Coil.K_trivial
