import Ccformal.PathReduced

/-!
# Projection of a path word into the reduced model      (S179)

`valid_wf`: a spread-`k` path word of length `≥ 4K - d4 + E` (hypotheses `Fits`) gives a valid assignment `wf` of the
reduced model `P` (`PathReduced.lean`), with `x = xvec`; `reduced_bound`: if the model has no solution (`NoSol P`),
then `L + d4 < 4K + E`.  Ingredients: `win_id` (window identity (R4)), `base_dist` ((R3)), `plotkin` / `budget_sum`
((R2)), `pairok_word` ((R5)).  The backward rule (R6) and 'distinct letters in a piece' are not needed by the search.
Written proof: `PROOF_threshold.md`, (R1)-(R5).
-/

open Finset

namespace Coil

namespace Red

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {α : Type*} [Fintype α] [DecidableEq α] {k L : ℕ} {T : ℕ → α}

theorem r_add (a b : ℕ) : Nat.add a b = a + b := rfl
theorem r_mul (a b : ℕ) : Nat.mul a b = a * b := rfl
theorem r_sub (a b : ℕ) : Nat.sub a b = a - b := rfl
theorem r_div (a b : ℕ) : Nat.div a b = a / b := rfl
theorem r_mod (a b : ℕ) : Nat.mod a b = a % b := rfl
theorem r_pow (a b : ℕ) : Nat.pow a b = a ^ b := rfl
theorem r_lor (a b : ℕ) : Nat.lor a b = a ||| b := rfl
theorem r_succ (a : ℕ) : Nat.succ a = a + 1 := rfl

/-! ### counting lemmas -/

lemma cnt_ne_zero_iff (T : ℕ → α) (s w : ℕ) (c : α) : cnt T s w c ≠ 0 ↔ ∃ t < w, T (s + t) = c := by
  rw [cnt, Finset.card_ne_zero]
  constructor
  · rintro ⟨t, ht⟩
    rw [mem_filter, mem_range] at ht
    exact ⟨t, ht.1, ht.2⟩
  · rintro ⟨t, ht, h⟩
    exact ⟨t, by rw [mem_filter, mem_range]; exact ⟨ht, h⟩⟩

lemma sum_comp (T : ℕ → α) (s e : ℕ) (g : α → ℕ) :
    ∑ t ∈ range e, g (T (s + t)) = ∑ c, cnt T s e c * g c := by
  simp_rw [cnt_eq_sum, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun t _ => ?_
  simp

lemma win_coord (a a' m w : ℕ) (ha : a ≤ 1) (ha' : a' ≤ 1) (h : a + w = m + a') :
    (if Odd w then 1 else 0) + a + a' = (if Odd m then 1 else 0)
      + a * (if a' ≠ 0 then 1 else 2 * (1 - m % 2)) + a' * (if a ≠ 0 then 1 else 2 * (1 - m % 2)) := by
  simp only [Nat.odd_iff]
  interval_cases a <;> interval_cases a' <;> split_ifs <;> omega

/-- the window identity (R4): moving the two ends of a window by `e`, `e2` letters -/
lemma win_id (T : ℕ → α) (s n e e2 : ℕ) (he : e ≤ n) (ha : ∀ c, cnt T s e c ≤ 1)
    (ha' : ∀ c, cnt T (s + n) e2 c ≤ 1) :
    oddc T (s + e) (n + e2 - e) + e + e2 = oddc T s n
      + ∑ t ∈ range e, (if cnt T (s + n) e2 (T (s + t)) ≠ 0 then 1 else 2 * (1 - cnt T s n (T (s + t)) % 2))
      + ∑ t ∈ range e2, (if cnt T s e (T (s + n + t)) ≠ 0 then 1 else 2 * (1 - cnt T s n (T (s + n + t)) % 2)) := by
  have key : ∀ c, (if Odd (cnt T (s + e) (n + e2 - e) c) then 1 else 0) + cnt T s e c + cnt T (s + n) e2 c
      = (if Odd (cnt T s n c) then 1 else 0)
        + cnt T s e c * (if cnt T (s + n) e2 c ≠ 0 then 1 else 2 * (1 - cnt T s n c % 2))
        + cnt T (s + n) e2 c * (if cnt T s e c ≠ 0 then 1 else 2 * (1 - cnt T s n c % 2)) := by
    intro c
    refine win_coord _ _ _ _ (ha c) (ha' c) ?_
    rw [← cnt_split T e (show n + e2 = e + (n + e2 - e) by omega) rfl c, cnt_add]
  have S := Finset.sum_congr rfl (fun c (_ : c ∈ (univ : Finset α)) => key c)
  simp only [sum_add_distrib] at S
  rw [sum_cnt, sum_cnt] at S
  have E1 := sum_comp T s e (fun c => if cnt T (s + n) e2 c ≠ 0 then 1 else 2 * (1 - cnt T s n c % 2))
  have E2 := sum_comp T (s + n) e2 (fun c => if cnt T s e c ≠ 0 then 1 else 2 * (1 - cnt T s n c % 2))
  beta_reduce at E1 E2
  rw [E1, E2, oddc_eq_sum, oddc_eq_sum]
  exact S

/-- a window of length `≤ k+1` of a path word has all letters distinct -/
lemma oddc_short (h : IsPathWord k L T) {s w : ℕ} (hs : s + w ≤ L) (hw : w ≤ k + 1) : oddc T s w = w := by
  rw [oddc_eq_sum]
  conv_rhs => rw [← sum_cnt T s w]
  refine sum_congr rfl fun c _ => ?_
  have := h.cnt_le_one hs hw c
  simp only [Nat.odd_iff]
  split_ifs <;> omega

/-! ### masks -/

lemma maskA_succ (get : ℕ → ℕ × ℕ) (j e : ℕ) :
    maskA get j (e + 1) = maskA get j e ||| 2 ^ (get (5 * e + j)).2 := rfl

lemma maskA_bit (get : ℕ → ℕ × ℕ) (j e i : ℕ) :
    maskA get j e / 2 ^ i % 2 = 1 ↔ ∃ t < e, (get (5 * t + j)).2 = i := by
  have key : ∀ m : ℕ, m / 2 ^ i % 2 = 1 ↔ m.testBit i = true := by
    intro m
    rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq]
  rw [key]
  induction e with
  | zero =>
    rw [show maskA get j 0 = 0 from rfl]
    simp
  | succ e ih =>
    rw [maskA_succ, Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow, decide_eq_true_eq]
    constructor
    · rintro (h | h)
      · obtain ⟨t, ht, h⟩ := ih.mp h
        exact ⟨t, by omega, h⟩
      · exact ⟨e, by omega, h⟩
    · rintro ⟨t, ht, h⟩
      by_cases hte : t = e
      · subst hte; exact Or.inr h
      · exact Or.inl (ih.mpr ⟨t, by omega, h⟩)

lemma maskA_congr {get get' : ℕ → ℕ × ℕ} {j e : ℕ} (h : ∀ t < e, get (5 * t + j) = get' (5 * t + j)) :
    maskA get j e = maskA get' j e := by
  induction e with
  | zero => rfl
  | succ e ih =>
    rw [maskA_succ, maskA_succ, ih (fun t ht => h t (by omega)), h e (by omega)]

lemma sumr_congr {n : ℕ} {f g : ℕ → ℕ} (h : ∀ t < n, f t = g t) : sumr n f = sumr n g := by
  rw [sumr_eq, sumr_eq]
  exact sum_congr rfl fun t ht => h t (mem_range.mp ht)

lemma S_congr {get get' : ℕ → ℕ × ℕ} {j e : ℕ} (m' a b : ℕ) (h : ∀ t < e, get (5 * t + j) = get' (5 * t + j)) :
    S get j e m' a b = S get' j e m' a b := by
  unfold S
  refine sumr_congr fun t ht => ?_
  simp only [r_add, r_mul]
  rw [h t ht]

lemma pairok_congr (P : Params) (x : ℕ → ℕ) {get get' : ℕ → ℕ × ℕ} {j e j2 e2 : ℕ}
    (h : ∀ t < e, get (5 * t + j) = get' (5 * t + j)) (h2 : ∀ t < e2, get (5 * t + j2) = get' (5 * t + j2)) :
    pairok P x get j e (maskA get j e) j2 e2 (maskA get j2 e2)
      = pairok P x get' j e (maskA get' j e) j2 e2 (maskA get' j2 e2) := by
  unfold pairok
  rw [maskA_congr h, maskA_congr h2, S_congr _ _ _ h, S_congr _ _ _ h2]

/-! ### the word-level objects -/

/-- cut positions -/
def pos (P : Params) (k j : ℕ) : ℕ := j * (k + 1) - P.df j

/-- sum of the six `req - K + 1` of the non-adjacent pairs of cut vertices -/
noncomputable def Rsum (P : Params) : ℕ :=
  req1 P 0 2 0 0 + req1 P 1 3 0 0 + req1 P 2 4 0 0 + req1 P 0 3 0 0 + req1 P 1 4 0 0 + req1 P 0 4 0 0

/-- hypotheses of the projection: a path word of length `≥ 4K - d4 + E`, cut at `p_j = j*K - df j` -/
structure Fits (P : Params) (k L : ℕ) (T : ℕ → α) : Prop where
  word : IsPathWord k L T
  par : P.par = (k + 1) % 2
  d1 : P.d1 ≤ 1
  d2l : P.d1 ≤ P.d2
  d2u : P.d2 ≤ P.d1 + 1
  d3l : P.d2 ≤ P.d3
  d3u : P.d3 ≤ P.d2 + 1
  d4l : P.d3 ≤ P.d4
  d4u : P.d4 ≤ P.d3 + 1
  hM : P.M + P.d4 + 1 ≤ k + 1
  hE : P.E ≤ P.M
  hL : 4 * (k + 1) + P.E ≤ L + P.d4
  hB : 6 * Fintype.card α + P.d4 + 6 ≤ 10 * (k + 1) + Rsum P + 2 * P.B

theorem df0 (P : Params) : P.df 0 = 0 := rfl
theorem df1 (P : Params) : P.df 1 = P.d1 := rfl
theorem df2 (P : Params) : P.df 2 = P.d2 := rfl
theorem df3 (P : Params) : P.df 3 = P.d3 := rfl
theorem df4 (P : Params) : P.df 4 = P.d4 := rfl

lemma pos0 (P : Params) (k : ℕ) : pos P k 0 = 0 := by simp [pos]
lemma pos1 (P : Params) (k : ℕ) : pos P k 1 = (k + 1) - P.d1 := by simp [pos, df1]
lemma pos2 (P : Params) (k : ℕ) : pos P k 2 = 2 * (k + 1) - P.d2 := by simp [pos, df2]
lemma pos3 (P : Params) (k : ℕ) : pos P k 3 = 3 * (k + 1) - P.d3 := by simp [pos, df3]
lemma pos4 (P : Params) (k : ℕ) : pos P k 4 = 4 * (k + 1) - P.d4 := by simp [pos, df4]

lemma nl_lt (P : Params) {j : ℕ} (hj : j < 4) : P.nl j = P.M := by
  have : Nat.blt j 4 = true := by rw [Nat.blt_eq]; exact hj
  rw [Params.nl, this]; rfl

lemma nl_ge (P : Params) {j : ℕ} (hj : 4 ≤ j) : P.nl j = P.E := by
  have : Nat.blt j 4 = false := by rw [← Bool.not_eq_true, Nat.blt_eq]; omega
  rw [Params.nl, this]; rfl

lemma used_iff (P : Params) (j j2 e e2 : ℕ) :
    used P j j2 e e2 = true ↔ (j2 ≠ j + 1 ∨ e + P.df j2 ≤ e2 + 1 + P.df j) := by
  have h1 : Nat.beq j2 (j + 1) = false ↔ j2 ≠ j + 1 := by rw [← Bool.not_eq_true, Nat.beq_eq]
  unfold used
  simp only [r_add, r_succ]
  rw [Bool.or_eq_true, Bool.not_eq_true', Nat.ble_eq, h1]

lemma dummy_iff (P : Params) (s : ℕ) : dummy P s = true ↔ s % 5 = 4 ∧ P.E ≤ s / 5 := by
  simp [dummy, r_mod, r_div]

lemma dummy_slot (P : Params) {j t : ℕ} (hj : j < 5) (h : j < 4 ∨ t < P.E) : dummy P (5 * t + j) = false := by
  rw [← Bool.not_eq_true, dummy_iff]
  omega

lemma nd_of (P : Params) {j t : ℕ} (he : t < P.nl j) : j < 4 ∨ t < P.E := by
  by_cases hj : j < 4
  · exact Or.inl hj
  · rw [nl_ge P (by omega)] at he
    exact Or.inr he

section geom

variable {P : Params}

lemma pos_adj (hf : Fits P k L T) {j : ℕ} (hj : j < 4) :
    pos P k (j + 1) + P.df (j + 1) = pos P k j + P.df j + (k + 1) ∧ P.df j ≤ P.df (j + 1)
      ∧ P.df (j + 1) ≤ P.df j + 1 ∧ P.df j ≤ pos P k j ∧ pos P k (j + 1) ≤ L := by
  obtain ⟨-, -, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, -⟩ := hf
  have p0 := pos0 P k
  have p1 := pos1 P k
  have p2 := pos2 P k
  have p3 := pos3 P k
  have p4 := pos4 P k
  have c0 := df0 P
  have c1 := df1 P
  have c2 := df2 P
  have c3 := df3 P
  have c4 := df4 P
  interval_cases j <;> simp only [Nat.reduceAdd] <;> omega

lemma df_le (hf : Fits P k L T) {j : ℕ} (hj : j ≤ 4) : P.df j ≤ P.d4 := by
  obtain ⟨-, -, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, -⟩ := hf
  have c0 := df0 P
  have c1 := df1 P
  have c2 := df2 P
  have c3 := df3 P
  have c4 := df4 P
  interval_cases j <;> omega

lemma pos_mono (hf : Fits P k L T) {j j2 : ℕ} (hj : j ≤ j2) (hj2 : j2 ≤ 4) : pos P k j ≤ pos P k j2 := by
  obtain ⟨-, -, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, -⟩ := hf
  have p0 := pos0 P k
  have p1 := pos1 P k
  have p2 := pos2 P k
  have p3 := pos3 P k
  have p4 := pos4 P k
  interval_cases j2 <;> interval_cases j <;> omega

lemma pos_eq (hf : Fits P k L T) :
    pos P k 0 = 0 ∧ pos P k 1 + P.d1 = k + 1 ∧ pos P k 2 + P.d2 = 2 * (k + 1) ∧ pos P k 3 + P.d3 = 3 * (k + 1)
      ∧ pos P k 4 + P.d4 = 4 * (k + 1) := by
  obtain ⟨-, -, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, -⟩ := hf
  have p0 := pos0 P k
  have p1 := pos1 P k
  have p2 := pos2 P k
  have p3 := pos3 P k
  have p4 := pos4 P k
  omega

/-- arithmetic of one pair of cut positions, with `n = p_j2 - p_j` -/
lemma pair_arith (par d d2 M E k L pj n e e2 j j2 : ℕ) (hj : j < j2) (hj2 : j2 ≤ 4)
    (hpar : par = (k + 1) % 2) (hpj : pj + d = j * (k + 1)) (hpj2 : pj + n + d2 = j2 * (k + 1))
    (hd : d ≤ d2) (hd2 : d2 ≤ d + (j2 - j)) (hdd : d2 ≤ j2) (hM : M + d2 + 1 ≤ k + 1)
    (hL : pj + n + (if j2 = 4 then E else M) ≤ L) (n1 : e ≤ M) (n2 : e2 ≤ M) (n3 : j2 < 4 ∨ e2 ≤ E) (hE : E ≤ M)
    (hu : j2 ≠ j + 1 ∨ e + d2 ≤ e2 + 1 + d) :
    e ≤ n ∧ pj + n + e2 ≤ L ∧ e ≤ k + 1 ∧ e2 ≤ k + 1 ∧ k ≤ n + e2 - e
      ∧ ((j2 - j + 1) * par + d + d2 + e + e2 + 1) % 2 ≤ 1
      ∧ ((n + e2 - e + k) % 2 = 1 ↔ ((j2 - j + 1) * par + d + d2 + e + e2 + 1) % 2 = 1) := by
  subst hpar
  interval_cases j2 <;> interval_cases j <;> simp only [Nat.reduceSub, Nat.reduceAdd, Nat.reduceEqDiff,
    if_true, if_false] at hL hd2 hpj hpj2 ⊢ <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

lemma pair_geom (hf : Fits P k L T) {j j2 e e2 : ℕ} (hj : j < j2) (hj2 : j2 ≤ 4) (he : e ≤ P.nl j)
    (he2 : e2 ≤ P.nl j2) (hu : used P j j2 e e2 = true) :
    e ≤ pos P k j2 - pos P k j ∧ pos P k j ≤ pos P k j2 ∧ pos P k j2 + e2 ≤ L ∧ e ≤ k + 1 ∧ e2 ≤ k + 1
      ∧ k ≤ pos P k j2 - pos P k j + e2 - e ∧ req1 P j j2 e e2 ≤ 1
      ∧ ((pos P k j2 - pos P k j + e2 - e + k) % 2 = 1 ↔ req1 P j j2 e e2 = 1) := by
  rw [used_iff] at hu
  have hmono := pos_mono hf hj.le hj2
  obtain ⟨q0, q1, q2, q3, q4⟩ := pos_eq hf
  have hpar := hf.par
  obtain ⟨-, -, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, -⟩ := hf
  have n1 : e ≤ P.M := by
    by_cases h : j < 4
    · rw [nl_lt P h] at he; exact he
    · rw [nl_ge P (by omega)] at he; omega
  have n2 : e2 ≤ P.M := by
    by_cases h : j2 < 4
    · rw [nl_lt P h] at he2; exact he2
    · rw [nl_ge P (by omega)] at he2; omega
  have n3 : j2 < 4 ∨ e2 ≤ P.E := by
    by_cases h : j2 < 4
    · exact Or.inl h
    · rw [nl_ge P (by omega)] at he2; exact Or.inr he2
  have hreq : req1 P j j2 e e2 = ((j2 - j + 1) * P.par + P.df j + P.df j2 + e + e2 + 1) % 2 := rfl
  rw [hreq]
  obtain ⟨n, hn⟩ : ∃ n, pos P k j2 = pos P k j + n := ⟨_, (Nat.add_sub_cancel' hmono).symm⟩
  rw [hn, Nat.add_sub_cancel_left]
  have c0 := df0 P
  have c1 := df1 P
  have c2 := df2 P
  have c3 := df3 P
  have c4 := df4 P
  have hj4 : j < 4 := by omega
  have hpj : pos P k j + P.df j = j * (k + 1) := by
    interval_cases j <;> omega
  have hpj2 : pos P k j + n + P.df j2 = j2 * (k + 1) := by
    rw [← hn]
    interval_cases j2 <;> omega
  have hd : P.df j ≤ P.df j2 := by
    interval_cases j2 <;> interval_cases j <;> omega
  have hd2 : P.df j2 ≤ P.df j + (j2 - j) := by
    interval_cases j2 <;> interval_cases j <;> omega
  have hdd : P.df j2 ≤ j2 := by
    interval_cases j2 <;> omega
  have hd4 : P.df j2 ≤ P.d4 := by
    interval_cases j2 <;> omega
  have hL : pos P k j + n + (if j2 = 4 then P.E else P.M) ≤ L := by
    rw [← hn]
    interval_cases j2 <;> simp only [Nat.reduceEqDiff, if_true, if_false] <;> omega
  have A := pair_arith P.par (P.df j) (P.df j2) P.M P.E k L (pos P k j) n e e2 j j2 hj hj2 hpar hpj hpj2 hd hd2 hdd
    (by omega) hL n1 n2 n3 h9 hu
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := A
  exact ⟨a1, by omega, a2, a3, a4, a5, a6, a7⟩

lemma used00 (hf : Fits P k L T) {j j2 : ℕ} (hj : j < j2) (hj2 : j2 ≤ 4) : used P j j2 0 0 = true := by
  rw [used_iff]
  by_cases h : j2 = j + 1
  · subst h
    have := (pos_adj hf (j := j) (by omega)).2.2.1
    right; omega
  · exact Or.inl h

end geom

/-! ### the assignment of a word -/

/-- the coordinate at slot `s` -/
def co (P : Params) (k : ℕ) (T : ℕ → α) (s : ℕ) : α := T (pos P k (s % 5) + s / 5)

/-- pattern of a coordinate: bit `j` = parity of its number of occurrences before cut `j` -/
def patc (P : Params) (k : ℕ) (T : ℕ → α) (c : α) : ℕ :=
  2 * (cnt T 0 (pos P k 1) c % 2) + 4 * (cnt T 0 (pos P k 2) c % 2) + 8 * (cnt T 0 (pos P k 3) c % 2)
    + 16 * (cnt T 0 (pos P k 4) c % 2)

open Classical in
/-- identity of a coordinate: the first non-dummy slot carrying it -/
noncomputable def idc (P : Params) (k : ℕ) (T : ℕ → α) (c : α) : ℕ :=
  if h : ∃ t, dummy P t = false ∧ co P k T t = c then Nat.find h else 0

noncomputable def wf (P : Params) (k : ℕ) (T : ℕ → α) (s : ℕ) : ℕ × ℕ :=
  if dummy P s = true then (0, s) else (patc P k T (co P k T s), idc P k T (co P k T s))

section word

variable {P : Params}

lemma idc_spec {c : α} (h : ∃ t, dummy P t = false ∧ co P k T t = c) :
    dummy P (idc P k T c) = false ∧ co P k T (idc P k T c) = c ∧ ∀ t, dummy P t = false → co P k T t = c →
      idc P k T c ≤ t := by
  unfold idc
  rw [dif_pos h]
  exact ⟨(Nat.find_spec h).1, (Nat.find_spec h).2, fun t h1 h2 => Nat.find_min' h ⟨h1, h2⟩⟩

lemma idc_inj {c c' : α} (h : ∃ t, dummy P t = false ∧ co P k T t = c)
    (h' : ∃ t, dummy P t = false ∧ co P k T t = c') (e : idc P k T c = idc P k T c') : c = c' := by
  have h1 := (idc_spec h).2.1
  have h2 := (idc_spec h').2.1
  rw [e] at h1
  exact h1.symm.trans h2

lemma co_slot {j : ℕ} (hj : j < 5) (t : ℕ) : co P k T (5 * t + j) = T (pos P k j + t) := by
  unfold co
  rw [show (5 * t + j) % 5 = j by omega, show (5 * t + j) / 5 = t by omega]

lemma wit {j t : ℕ} (hj : j < 5) (h : j < 4 ∨ t < P.E) :
    ∃ s, dummy P s = false ∧ co P k T s = T (pos P k j + t) :=
  ⟨5 * t + j, dummy_slot P hj h, co_slot hj t⟩

lemma wf_slot {j t : ℕ} (hj : j < 5) (h : j < 4 ∨ t < P.E) :
    wf P k T (5 * t + j) = (patc P k T (T (pos P k j + t)), idc P k T (T (pos P k j + t))) := by
  unfold wf
  rw [dummy_slot P hj h, co_slot hj t]
  simp

lemma wf_idc {c : α} (h : ∃ t, dummy P t = false ∧ co P k T t = c) :
    wf P k T (idc P k T c) = (patc P k T c, idc P k T c) := by
  obtain ⟨h1, h2, -⟩ := idc_spec h
  unfold wf
  rw [h1, h2]
  simp

lemma patc_lt (c : α) : patc P k T c < 32 := by unfold patc; omega

lemma patc_even (c : α) : patc P k T c % 2 = 0 := by unfold patc; omega

lemma patc_bit {j : ℕ} (hj : j ≤ 4) (c : α) : patc P k T c / 2 ^ j % 2 = cnt T 0 (pos P k j) c % 2 := by
  have h0 : cnt T 0 (pos P k 0) c = 0 := by rw [pos0]; simp [cnt]
  unfold patc
  interval_cases j <;> simp only [h0, Nat.reducePow] <;> omega

lemma sepn_patc (hf : Fits P k L T) {j j2 : ℕ} (hj : j ≤ j2) (hj2 : j2 ≤ 4) (c : α) :
    sepn (patc P k T c) j j2 = cnt T (pos P k j) (pos P k j2 - pos P k j) c % 2 := by
  have b1 := patc_bit (P := P) (k := k) (T := T) (j := j) (by omega) c
  have b2 := patc_bit (P := P) (k := k) (T := T) (j := j2) hj2 c
  have hp := pos_mono hf hj hj2
  have h3 := cnt_pre T (x := pos P k j) (w := pos P k j2 - pos P k j) (y := pos P k j2) (by omega) c
  simp only [sepn, r_add, r_div, r_mod, r_pow]
  omega

/-- the sum `S` of the word's assignment, in terms of the word -/
lemma S_word (hf : Fits P k L T) {j j' e e' a b : ℕ} (hj : j < 5) (hj' : j' < 5) (he : e ≤ P.nl j)
    (he' : e' ≤ P.nl j') (hab : a ≤ b) (hb : b ≤ 4) :
    S (wf P k T) j e (maskA (wf P k T) j' e') a b
      = ∑ t ∈ range e, (if cnt T (pos P k j') e' (T (pos P k j + t)) ≠ 0 then 1
          else 2 * (1 - cnt T (pos P k a) (pos P k b - pos P k a) (T (pos P k j + t)) % 2)) := by
  unfold S
  rw [sumr_eq]
  refine sum_congr rfl fun t ht => ?_
  rw [mem_range] at ht
  have hnd := nd_of P (lt_of_lt_of_le ht he)
  simp only [r_add, r_mul, r_sub, r_div, r_mod, r_pow]
  rw [wf_slot hj hnd]
  simp only []
  rw [sepn_patc hf hab hb]
  have hm := maskA_bit (wf P k T) j' e' (idc P k T (T (pos P k j + t)))
  by_cases hc : cnt T (pos P k j') e' (T (pos P k j + t)) ≠ 0
  · have h1 : maskA (wf P k T) j' e' / 2 ^ idc P k T (T (pos P k j + t)) % 2 = 1 := by
      rw [hm]
      obtain ⟨t', ht', h⟩ := (cnt_ne_zero_iff _ _ _ _).mp hc
      refine ⟨t', ht', ?_⟩
      rw [wf_slot hj' (nd_of P (lt_of_lt_of_le ht' he')), h]
    rw [h1, if_pos hc]
    rfl
  · have h1 : Nat.beq (maskA (wf P k T) j' e' / 2 ^ idc P k T (T (pos P k j + t)) % 2) 1 = false := by
      rw [← Bool.not_eq_true, Nat.beq_eq, hm]
      rintro ⟨t', ht', h⟩
      have hnd' := nd_of P (lt_of_lt_of_le ht' he')
      rw [wf_slot hj' hnd'] at h
      have := idc_inj (wit hj' hnd') (wit hj hnd) h
      exact hc ((cnt_ne_zero_iff _ _ _ _).mpr ⟨t', ht', this⟩)
    rw [h1, if_neg hc]
    rfl

end word

/-! ### base distances and the pair inequalities -/

/-- the excess `x_{j,j2}` of a non-adjacent pair of cut vertices -/
noncomputable def xw (P : Params) (k : ℕ) (T : ℕ → α) (j j2 : ℕ) : ℕ :=
  (oddc T (pos P k j) (pos P k j2 - pos P k j) - k - req1 P j j2 0 0) / 2

noncomputable def xvec (P : Params) (k : ℕ) (T : ℕ → α) : ℕ → ℕ :=
  xfun (xw P k T 0 2) (xw P k T 1 3) (xw P k T 2 4) (xw P k T 0 3) (xw P k T 1 4) (xw P k T 0 4)

section word2

variable {P : Params}

lemma base_dist (hf : Fits P k L T) {j j2 : ℕ} (hj : j < j2) (hj2 : j2 ≤ 4) :
    oddc T (pos P k j) (pos P k j2 - pos P k j) = k + D1 P (xvec P k T) j j2 := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ :=
    pair_geom hf hj hj2 (Nat.zero_le _) (Nat.zero_le _) (used00 hf hj hj2)
  by_cases hadj : j2 = j + 1
  · subst hadj
    obtain ⟨a1, a2, a3, a4, a5⟩ := pos_adj hf (j := j) (by omega)
    have hD : D1 P (xvec P k T) j (j + 1) = 1 + P.df j - P.df (j + 1) := by
      have : Nat.beq (j + 1) (Nat.succ j) = true := by rw [Nat.beq_eq]
      rw [D1, this]; rfl
    rw [hD, oddc_short hf.word (by omega) (by omega)]
    omega
  · have hD : D1 P (xvec P k T) j j2 = req1 P j j2 0 0 + 2 * xw P k T j j2 := by
      have h1 : Nat.beq j2 (Nat.succ j) = false := by
        rw [← Bool.not_eq_true, Nat.beq_eq]; exact hadj
      have h2 : xvec P k T (xidx j j2) = xw P k T j j2 := by
        interval_cases j2 <;> interval_cases j <;> first | omega | rfl
      rw [D1, h1, Bool.cond_false, r_add, r_mul, h2]
    have hge := hf.word.ge (s := pos P k j) (w := pos P k j2 - pos P k j) (by omega) (by omega)
    have hpar := oddc_parity T (pos P k j) (pos P k j2 - pos P k j)
    rw [Nat.odd_iff, Nat.odd_iff] at hpar
    rw [hD, xw]
    rcases Nat.lt_or_ge (req1 P j j2 0 0) 1 with hr | hr
    · omega
    · have hgt := hf.word.gt (s := pos P k j) (w := pos P k j2 - pos P k j) (by omega) (by omega) (by omega)
      omega

lemma pairok_word (hf : Fits P k L T) {j j2 e e2 : ℕ} (hj : j < j2) (hj2 : j2 ≤ 4) (he : e ≤ P.nl j)
    (he2 : e2 ≤ P.nl j2) :
    pairok P (xvec P k T) (wf P k T) j e (maskA (wf P k T) j e) j2 e2 (maskA (wf P k T) j2 e2) = true := by
  unfold pairok
  by_cases hu : used P j j2 e e2 = true
  swap
  · rw [Bool.not_eq_true] at hu
    rw [hu]; rfl
  rw [hu, Bool.not_true, Bool.false_or, Nat.ble_eq]
  simp only [r_add]
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := pair_geom hf hj hj2 he he2 hu
  rw [S_word hf (j := j) (j' := j2) (by omega) (by omega) he he2 hj.le hj2,
    S_word hf (j := j2) (j' := j) (by omega) (by omega) he2 he hj.le hj2]
  have e1 : pos P k j + (pos P k j2 - pos P k j) = pos P k j2 := by omega
  have W := win_id T (pos P k j) (pos P k j2 - pos P k j) e e2 g1
    (fun c => hf.word.cnt_le_one (by omega) g4 c)
    (fun c => hf.word.cnt_le_one (by omega) g5 c)
  rw [e1] at W
  have hbase := base_dist hf hj hj2
  have hge := hf.word.ge (s := pos P k j + e) (w := pos P k j2 - pos P k j + e2 - e) (by omega) g6
  rcases Nat.lt_or_ge (req1 P j j2 e e2) 1 with hr | hr
  · omega
  · have hgt := hf.word.gt (s := pos P k j + e) (w := pos P k j2 - pos P k j + e2 - e) (by omega) g6
      (g8.mpr (by omega))
    omega

/-! ### the budget (Plotkin identity) -/

lemma cost_spec : ∀ p < 32, p % 2 = 0 →
    sepn p 0 1 + sepn p 1 2 + sepn p 2 3 + sepn p 3 4 + sepn p 0 2 + sepn p 1 3 + sepn p 2 4
      + sepn p 0 3 + sepn p 1 4 + sepn p 0 4 + 2 * cost p = 6 := by
  decide

lemma odd_ite (m : ℕ) : (if Odd m then 1 else 0) = m % 2 := by
  simp only [Nat.odd_iff]
  split_ifs <;> omega

lemma plotkin (hf : Fits P k L T) :
    oddc T (pos P k 0) (pos P k 1 - pos P k 0) + oddc T (pos P k 1) (pos P k 2 - pos P k 1)
      + oddc T (pos P k 2) (pos P k 3 - pos P k 2) + oddc T (pos P k 3) (pos P k 4 - pos P k 3)
      + oddc T (pos P k 0) (pos P k 2 - pos P k 0) + oddc T (pos P k 1) (pos P k 3 - pos P k 1)
      + oddc T (pos P k 2) (pos P k 4 - pos P k 2) + oddc T (pos P k 0) (pos P k 3 - pos P k 0)
      + oddc T (pos P k 1) (pos P k 4 - pos P k 1) + oddc T (pos P k 0) (pos P k 4 - pos P k 0)
      + 2 * ∑ c, cost (patc P k T c) = 6 * Fintype.card α := by
  have key : ∀ c : α,
      (if Odd (cnt T (pos P k 0) (pos P k 1 - pos P k 0) c) then 1 else 0)
        + (if Odd (cnt T (pos P k 1) (pos P k 2 - pos P k 1) c) then 1 else 0)
        + (if Odd (cnt T (pos P k 2) (pos P k 3 - pos P k 2) c) then 1 else 0)
        + (if Odd (cnt T (pos P k 3) (pos P k 4 - pos P k 3) c) then 1 else 0)
        + (if Odd (cnt T (pos P k 0) (pos P k 2 - pos P k 0) c) then 1 else 0)
        + (if Odd (cnt T (pos P k 1) (pos P k 3 - pos P k 1) c) then 1 else 0)
        + (if Odd (cnt T (pos P k 2) (pos P k 4 - pos P k 2) c) then 1 else 0)
        + (if Odd (cnt T (pos P k 0) (pos P k 3 - pos P k 0) c) then 1 else 0)
        + (if Odd (cnt T (pos P k 1) (pos P k 4 - pos P k 1) c) then 1 else 0)
        + (if Odd (cnt T (pos P k 0) (pos P k 4 - pos P k 0) c) then 1 else 0)
        + 2 * cost (patc P k T c) = 6 := by
    intro c
    have C := cost_spec (patc P k T c) (patc_lt c) (patc_even c)
    rw [sepn_patc hf (by omega) (by omega), sepn_patc hf (by omega) (by omega),
      sepn_patc hf (by omega) (by omega), sepn_patc hf (by omega) (by omega),
      sepn_patc hf (by omega) (by omega), sepn_patc hf (by omega) (by omega),
      sepn_patc hf (by omega) (by omega), sepn_patc hf (by omega) (by omega),
      sepn_patc hf (by omega) (by omega), sepn_patc hf (by omega) (by omega)] at C
    simp only [odd_ite]
    exact C
  have S := Finset.sum_congr rfl (fun c (_ : c ∈ (univ : Finset α)) => key c)
  simp only [sum_add_distrib, ← oddc_eq_sum, ← mul_sum, sum_const, card_univ, smul_eq_mul] at S
  omega

lemma budget_sum (hf : Fits P k L T) :
    xvec P k T 0 + xvec P k T 1 + xvec P k T 2 + xvec P k T 3 + xvec P k T 4 + xvec P k T 5
      + ∑ c, cost (patc P k T c) ≤ P.B := by
  have H := plotkin hf
  have hB := hf.hB
  rw [base_dist hf (j := 0) (j2 := 1) (by omega) (by omega), base_dist hf (j := 1) (j2 := 2) (by omega) (by omega),
    base_dist hf (j := 2) (j2 := 3) (by omega) (by omega), base_dist hf (j := 3) (j2 := 4) (by omega) (by omega),
    base_dist hf (j := 0) (j2 := 2) (by omega) (by omega), base_dist hf (j := 1) (j2 := 3) (by omega) (by omega),
    base_dist hf (j := 2) (j2 := 4) (by omega) (by omega), base_dist hf (j := 0) (j2 := 3) (by omega) (by omega),
    base_dist hf (j := 1) (j2 := 4) (by omega) (by omega), base_dist hf (j := 0) (j2 := 4) (by omega) (by omega)] at H
  have a01 : D1 P (xvec P k T) 0 1 = 1 + 0 - P.d1 := rfl
  have a12 : D1 P (xvec P k T) 1 2 = 1 + P.d1 - P.d2 := rfl
  have a23 : D1 P (xvec P k T) 2 3 = 1 + P.d2 - P.d3 := rfl
  have a34 : D1 P (xvec P k T) 3 4 = 1 + P.d3 - P.d4 := rfl
  have n02 : D1 P (xvec P k T) 0 2 = req1 P 0 2 0 0 + 2 * xvec P k T 0 := rfl
  have n13 : D1 P (xvec P k T) 1 3 = req1 P 1 3 0 0 + 2 * xvec P k T 1 := rfl
  have n24 : D1 P (xvec P k T) 2 4 = req1 P 2 4 0 0 + 2 * xvec P k T 2 := rfl
  have n03 : D1 P (xvec P k T) 0 3 = req1 P 0 3 0 0 + 2 * xvec P k T 3 := rfl
  have n14 : D1 P (xvec P k T) 1 4 = req1 P 1 4 0 0 + 2 * xvec P k T 4 := rfl
  have n04 : D1 P (xvec P k T) 0 4 = req1 P 0 4 0 0 + 2 * xvec P k T 5 := rfl
  rw [a01, a12, a23, a34, n02, n13, n24, n03, n14, n04] at H
  obtain ⟨-, -, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, -⟩ := hf
  unfold Rsum at hB
  omega

lemma budget_word (hf : Fits P k L T) {get : ℕ → ℕ × ℕ} {n : ℕ} (h : ∀ t < n, get t = wf P k T t) :
    budget P (xvec P k T) get n = true := by
  unfold budget
  rw [Nat.ble_eq]
  simp only [r_add]
  have key : sumr n (fun t => bif isrep P get t then cost (get t).1 else 0) ≤ ∑ c, cost (patc P k T c) := by
    rw [sumr_eq]
    calc ∑ t ∈ range n, (bif isrep P get t then cost (get t).1 else 0)
        = ∑ t ∈ range n, (if dummy P t = false ∧ idc P k T (co P k T t) = t
            then cost (patc P k T (co P k T t)) else 0) := by
          refine sum_congr rfl fun t ht => ?_
          rw [mem_range] at ht
          unfold isrep
          rw [h t ht]
          unfold wf
          by_cases hd : dummy P t = true
          · simp [hd]
          · rw [Bool.not_eq_true] at hd
            by_cases hi : idc P k T (co P k T t) = t
            · simp [hd, hi]
            · have : Nat.beq (idc P k T (co P k T t)) t = false := by
                rw [← Bool.not_eq_true, Nat.beq_eq]; exact hi
              simp [hd, hi, this]
      _ = ∑ t ∈ (range n).filter (fun t => dummy P t = false ∧ idc P k T (co P k T t) = t),
            cost (patc P k T (co P k T t)) := (sum_filter _ _).symm
      _ = ∑ c ∈ ((range n).filter (fun t => dummy P t = false ∧ idc P k T (co P k T t) = t)).image (co P k T),
            cost (patc P k T c) := by
          rw [sum_image]
          intro t ht t' ht' e
          rw [mem_coe, mem_filter] at ht ht'
          rw [← ht.2.2, ← ht'.2.2, e]
      _ ≤ ∑ c, cost (patc P k T c) := sum_le_sum_of_subset (subset_univ _)
  have := budget_sum hf
  omega

/-! ### the assignment of a path word is valid -/

theorem valid_wf (hf : Fits P k L T) : Valid P (xvec P k T) (wf P k T) := by
  intro s hs
  have agree : ∀ t ≤ s, trunc (wf P k T) (s + 1) t = wf P k T t := by
    intro t ht
    simp [trunc, Nat.lt_succ_of_le ht]
  generalize trunc (wf P k T) (s + 1) = get at agree
  unfold stepok
  simp only [force_eq, r_mod, r_div, r_succ]
  by_cases hd : dummy P s = true
  · rw [hd, Bool.cond_true, agree s le_rfl]
    unfold wf
    rw [if_pos hd]
    simp
  · rw [Bool.not_eq_true] at hd
    rw [hd, Bool.cond_false, agree s le_rfl]
    obtain ⟨j, e, rfl, hj⟩ : ∃ j e, s = 5 * e + j ∧ j < 5 := ⟨s % 5, s / 5, by omega, by omega⟩
    have hnd : j < 4 ∨ e < P.E := by
      have := (dummy_iff P (5 * e + j)).not.mp (by rw [hd]; simp)
      omega
    have heM : e < P.M := by omega
    have henl : e + 1 ≤ P.nl j := by
      by_cases h4 : j < 4
      · rw [nl_lt P h4]; omega
      · rw [nl_ge P (by omega)]; omega
    rw [wf_slot hj hnd, show (5 * e + j) % 5 = j by omega, show (5 * e + j) / 5 = e by omega]
    simp only []
    have hw := wit (k := k) (T := T) hj hnd
    obtain ⟨i1, i2, i3⟩ := idc_spec hw
    have i4 : idc P k T (T (pos P k j + e)) ≤ 5 * e + j := i3 _ (dummy_slot P hj hnd) (co_slot hj e)
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · rw [Nat.blt_eq]; exact patc_lt _
    · rw [Nat.beq_eq]; exact patc_even _
    · rw [Bool.or_eq_true, Nat.ble_eq, Nat.beq_eq]
      by_cases h4 : 4 ≤ j
      · exact Or.inl h4
      · right
        obtain ⟨a1, a2, a3, a4, a5⟩ := pos_adj hf (j := j) (by omega)
        have hM := hf.hM
        have d4 : P.df (j + 1) ≤ P.d4 := df_le hf (by omega)
        rw [sepn_patc hf (by omega) (by omega)]
        have le1 := hf.word.cnt_le_one (s := pos P k j) (w := pos P k (j + 1) - pos P k j) (by omega) (by omega)
          (T (pos P k j + e))
        have ne0 : cnt T (pos P k j) (pos P k (j + 1) - pos P k j) (T (pos P k j + e)) ≠ 0 :=
          (cnt_ne_zero_iff _ _ _ _).mpr ⟨e, by omega, rfl⟩
        omega
    · rw [Nat.ble_eq]; exact i4
    · unfold isrep
      rw [agree _ i4, wf_idc hw, i1]
      simp
    · rw [agree _ i4, wf_idc hw]
      simp
    · exact budget_word hf (fun t ht => agree t (by omega))
    · unfold pairs
      simp only [force_eq, r_add, r_mul, r_sub, r_succ]
      rw [allr_iff]
      intro j2 hj2
      rw [Bool.or_eq_true, Nat.beq_eq]
      by_cases hjj : j2 = j
      · exact Or.inl hjj
      right
      rw [allr_iff]
      intro e2 he2
      rw [Bool.or_eq_true]
      by_cases hg : 0 < e2 ∧ 5 * e + j < 5 * (e2 - 1) + j2
      · left
        rw [Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq]
        exact hg
      right
      have ag1 : ∀ t < e + 1, get (5 * t + j) = wf P k T (5 * t + j) := fun t ht => agree _ (by omega)
      have ag2 : ∀ t < e2, get (5 * t + j2) = wf P k T (5 * t + j2) := fun t ht => agree _ (by omega)
      by_cases hlt : j < j2
      · have : Nat.blt j j2 = true := by rw [Nat.blt_eq]; exact hlt
        rw [this, Bool.cond_true, pairok_congr P _ ag1 ag2]
        exact pairok_word hf hlt (by omega) henl (by omega)
      · have : Nat.blt j j2 = false := by rw [← Bool.not_eq_true, Nat.blt_eq]; exact hlt
        rw [this, Bool.cond_false, pairok_congr P _ ag2 ag1]
        exact pairok_word hf (by omega) (by omega) (by omega) henl

/-- **Reduction theorem.** If the reduced model `P` has no solution, no path word of length `4K - d4 + E` exists. -/
theorem reduced_bound (hns : NoSol P) (h5 : 5 * P.M ≤ 32) (h : IsPathWord k L T) (hpar : P.par = (k + 1) % 2)
    (d1 : P.d1 ≤ 1) (d2l : P.d1 ≤ P.d2) (d2u : P.d2 ≤ P.d1 + 1) (d3l : P.d2 ≤ P.d3) (d3u : P.d3 ≤ P.d2 + 1)
    (d4l : P.d3 ≤ P.d4) (d4u : P.d4 ≤ P.d3 + 1) (hM : P.M + P.d4 + 1 ≤ k + 1) (hE : P.E ≤ P.M)
    (hB : 6 * Fintype.card α + P.d4 + 6 ≤ 10 * (k + 1) + Rsum P + 2 * P.B) :
    L + P.d4 < 4 * (k + 1) + P.E := by
  by_contra hc
  have hf : Fits P k L T := ⟨h, hpar, d1, d2l, d2u, d3l, d3u, d4l, d4u, hM, hE, by omega, hB⟩
  have hb := budget_sum hf
  have hx : xw P k T 0 2 + xw P k T 1 3 + xw P k T 2 4 + xw P k T 0 3 + xw P k T 1 4 + xw P k T 0 4 ≤ P.B := by
    have : xvec P k T 0 + xvec P k T 1 + xvec P k T 2 + xvec P k T 3 + xvec P k T 4 + xvec P k T 5 ≤ P.B := by
      omega
    exact this
  exact hns.not_valid h5 hx (valid_wf hf)

end word2

end Red

end Coil
