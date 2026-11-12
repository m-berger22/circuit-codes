import Ccformal.Basic

/-!
# A verified checker for circuit codes given by their transition word

`check f n k N = true` (a kernel computation, `O(N²)` cheap steps) implies that
`i ↦ f (i % N) % n` is the transition word of a spread-`k` circuit code of length `N` in `Q_n`,
hence that such a code exists (`IsCoil`).
-/

open Finset

namespace Coil

set_option linter.unusedSectionVars false

section word_to_coil

variable {α : Type*} [Fintype α] [DecidableEq α] {k N : ℕ} {T : ℕ → α}

lemma cnt_period (per : ∀ i, T (i + N) = T i) (i : ℕ) (c : α) : cnt T i N c = cnt T 0 N c := by
  rw [cnt_eq_sum, cnt_eq_sum]
  have := sum_shift (fun j => if T j = c then 1 else 0) N (by intro j; simp [per j]) i
  simp only [zero_add]
  simpa [add_comm] using this

/-- a transition word gives a circuit code (vertex `i` = parity vector of the first `i` steps) -/
theorem IsCoilWord.exists_coil (h : IsCoilWord k N T) : ∃ v : ℕ → α → Bool, IsCoil k N v := by
  let v : ℕ → α → Bool := fun i c => decide (Odd (cnt T 0 i c))
  have key : ∀ t L c, v t c ≠ v (t + L) c ↔ Odd (cnt T t L c) := by
    intro t L c
    have e : cnt T 0 (t + L) c = cnt T 0 t c + cnt T t L c := by
      rw [cnt_add, zero_add]
    simp only [v, e, ne_eq, decide_eq_decide, Nat.odd_iff]
    omega
  have hdo : ∀ t L, hd (v t) (v (t + L)) = oddc T t L := by
    intro t L
    rw [hd, oddc]
    exact congrArg card (filter_congr fun c _ => key t L c)
  refine ⟨v, ?_, ?_, ?_⟩
  · intro i
    funext c
    by_contra hne
    have h1 := (key i N c).mp (fun h' => hne h'.symm)
    rw [cnt_period h.per] at h1
    exact (Nat.not_even_iff_odd.mpr h1) (h.closed c)
  · intro i
    rw [hdo]
    have : ∀ c, Odd (cnt T i 1 c) ↔ T i = c := by
      intro c
      rw [cnt_one]
      split_ifs with h' <;> simp [h']
    rw [oddc, filter_congr (fun c _ => this c), Finset.filter_eq]
    simp
  · intro i L hL
    rw [hdo]
    rcases Nat.eq_zero_or_pos L with h0 | hpos
    · subst h0
      intro _
      simp [oddc, cnt]
    · exact h.spread i L hpos hL

end word_to_coil

section checker

variable {n : ℕ} [NeZero n]

/-- state `(mask, distance, ok)` after `L` steps starting at position `t` -/
def run (f : ℕ → ℕ) (n k N t : ℕ) : ℕ → ℕ × ℕ × Bool
  | 0 => (0, 0, true)
  | L + 1 =>
    let s := run f n k N t L
    let c := f ((t + L) % N) % n
    let d := if s.1.testBit c then s.2.1 - 1 else s.2.1 + 1
    (s.1 ^^^ (1 <<< c), d,
      s.2.2 && (decide (N ≤ L + 1) || decide (k ≤ d) || decide (d = min (L + 1) (N - (L + 1)))))

def allBelow (p : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | m + 1 => allBelow p m && p m

lemma allBelow_iff (p : ℕ → Bool) (m : ℕ) : allBelow p m = true ↔ ∀ t < m, p t = true := by
  induction m with
  | zero => simp [allBelow]
  | succ m ih =>
    simp only [allBelow, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ t ht
      rcases Nat.lt_succ_iff_lt_or_eq.mp ht with h' | h'
      · exact h1 t h'
      · rw [h']; exact h2
    · intro h
      exact ⟨fun t ht => h t (by omega), h m (by omega)⟩

/-- window check for the start position `t` -/
def okAt (f : ℕ → ℕ) (n k N t : ℕ) : Bool := (run f n k N t N).2.2

/-- `p` holds on `a, a+1, …, a+m-1` -/
def allRange (p : ℕ → Bool) (a : ℕ) : ℕ → Bool
  | 0 => true
  | m + 1 => allRange p a m && p (a + m)

lemma allRange_extend {p : ℕ → Bool} {a m : ℕ} (h1 : ∀ t < a, p t = true)
    (h2 : allRange p a m = true) : ∀ t < a + m, p t = true := by
  induction m with
  | zero => simpa using h1
  | succ m ih =>
    simp only [allRange, Bool.and_eq_true] at h2
    intro t ht
    rcases Nat.lt_succ_iff_lt_or_eq.mp (by omega : t < (a + m) + 1) with h' | h'
    · exact ih h2.1 t h'
    · rw [h']; exact h2.2

lemma allRange_zero {p : ℕ → Bool} : ∀ t < 0, p t = true := by
  intro t ht; omega

/-- the word as a function into `Fin n` -/
def wordOf (f : ℕ → ℕ) (n N : ℕ) [NeZero n] : ℕ → Fin n :=
  fun i => ⟨f (i % N) % n, Nat.mod_lt _ (NeZero.pos n)⟩

lemma oddc_succ {α : Type*} [Fintype α] [DecidableEq α] (T : ℕ → α) (t L : ℕ) :
    oddc T t (L + 1) = if Odd (cnt T t L (T (t + L))) then oddc T t L - 1 else oddc T t L + 1 := by
  set c := T (t + L) with hc
  have e : ∀ x, cnt T t (L + 1) x = cnt T t L x + if c = x then 1 else 0 := by
    intro x
    rw [cnt_add, cnt_one]
  rw [oddc_eq_sum, oddc_eq_sum]
  rw [← add_sum_erase univ _ (mem_univ c), ← add_sum_erase univ (fun x => if Odd (cnt T t L x) then 1 else 0) (mem_univ c)]
  have hrest : ∑ x ∈ univ.erase c, (if Odd (cnt T t (L + 1) x) then 1 else 0)
      = ∑ x ∈ univ.erase c, (if Odd (cnt T t L x) then 1 else 0) := by
    apply sum_congr rfl
    intro x hx
    have : c ≠ x := fun h' => (ne_of_mem_erase hx) h'.symm
    rw [e x, ite_cond_eq_false _ _ (eq_false this), add_zero]
  rw [hrest, e c]
  simp only [ite_true, Nat.odd_add_one]
  split_ifs <;> omega

lemma run_spec (f : ℕ → ℕ) (k N t L : ℕ) :
    (∀ x : Fin n, (run f n k N t L).1.testBit x = decide (Odd (cnt (wordOf f n N) t L x))) ∧
    (run f n k N t L).2.1 = oddc (wordOf f n N) t L ∧
    ((run f n k N t L).2.2 = true → ∀ L', 1 ≤ L' → L' ≤ L → L' < N →
      oddc (wordOf f n N) t L' < k → oddc (wordOf f n N) t L' = min L' (N - L')) := by
  induction L with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro x; simp [run, cnt]
    · simp [run, oddc, cnt]
    · intro _ L' h1 h2; omega
  | succ L ih =>
    obtain ⟨i1, i2, i3⟩ := ih
    set c : Fin n := wordOf f n N (t + L) with hc
    have hcv : f ((t + L) % N) % n = c.val := rfl
    have e : ∀ x, cnt (wordOf f n N) t (L + 1) x
        = cnt (wordOf f n N) t L x + if c = x then 1 else 0 := by
      intro x
      rw [cnt_add, cnt_one]
    have hd' : (if (run f n k N t L).1.testBit c.val then (run f n k N t L).2.1 - 1
        else (run f n k N t L).2.1 + 1) = oddc (wordOf f n N) t (L + 1) := by
      rw [oddc_succ, i1 c, i2]
      simp only [decide_eq_true_eq]
      rfl
    refine ⟨?_, ?_, ?_⟩
    · intro x
      simp only [run, hcv, Nat.testBit_xor, i1 x, e x, Nat.one_shiftLeft, Nat.testBit_two_pow]
      by_cases hcx : c = x
      · subst hcx
        simp [Nat.odd_add_one, ← Nat.not_odd_iff_even]
      · have : c.val ≠ x.val := fun h' => hcx (Fin.ext h')
        simp [hcx, this]
    · simp only [run, hcv]
      exact hd'
    · intro hok L' h1 h2 h3 h4
      simp only [run, hcv, hd', Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le h2) with h' | h'
      · exact i3 hok.1 L' h1 (by omega) h3 h4
      · subst h'
        rcases hok.2 with (h5 | h5) | h5
        · omega
        · omega
        · exact h5

/-- soundness of the checker -/
theorem check_sound (f : ℕ → ℕ) (k N : ℕ) (hpos : 0 < N)
    (hall : ∀ t < N, okAt f n k N t = true) (hclosed : (run f n k N 0 N).2.1 = 0) :
    IsCoilWord k N (wordOf f n N) := by
  simp only [okAt] at hall
  have per : ∀ i, wordOf f n N (i + N) = wordOf f n N i := by
    intro i
    simp [wordOf]
  have hshift : ∀ t L, oddc (wordOf f n N) t L = oddc (wordOf f n N) (t % N) L := by
    intro t L
    have : ∀ x, cnt (wordOf f n N) t L x = cnt (wordOf f n N) (t % N) L x := by
      intro x
      have hw : ∀ j, wordOf f n N (t + j) = wordOf f n N (t % N + j) := by
        intro j
        simp [wordOf, Nat.mod_add_mod]
      simp only [cnt, hw]
    simp [oddc, this]
  refine ⟨per, ?_, ?_⟩
  · intro c
    have h0 := (run_spec (n := n) f k N 0 N).2.1
    rw [hclosed] at h0
    by_contra hc
    have hodd := Nat.not_even_iff_odd.mp hc
    have : c ∈ ({c : Fin n | Odd (cnt (wordOf f n N) 0 N c)} : Finset (Fin n)) := by simp [hodd]
    rw [oddc] at h0
    have h1 := Finset.card_eq_zero.mp h0.symm
    rw [h1] at this
    simp at this
  · intro t L h1 h2 h3
    rw [hshift] at h3 ⊢
    have hr := (run_spec (n := n) f k N (t % N) N).2.2 (hall (t % N) (Nat.mod_lt _ hpos))
    exact hr L h1 (by omega) h2 h3

theorem exists_coil_of_check (f : ℕ → ℕ) (k N : ℕ) (hpos : 0 < N)
    (hall : ∀ t < N, okAt f n k N t = true) (hclosed : (run f n k N 0 N).2.1 = 0) :
    ∃ v : ℕ → Fin n → Bool, IsCoil k N v :=
  (check_sound f k N hpos hall hclosed).exists_coil

end checker

end Coil

#print axioms Coil.exists_coil_of_check
