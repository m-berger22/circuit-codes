import Ccformal.Lemma3

/-!
# Symmetric codes with a long bit run, second part: no length in `[6k+6, 7k+5]`

`symRun_gap` excludes `4k+2l < N ≤ 6k+4`, Lemma 3 excludes `N ≥ 7k+6` (for `k ≥ 2l` / `2l-3`). Here the window in between:
`Ω` = the part of a half period after the bit run `A` (`r = H - (k+l)` positions), `γ` a NEW coordinate (not in `A`).
* `alt` (Byrnes' Lemma 2.3, with window counts): the `k+1` transitions after the first `k` transitions of `Ω` are OLD, and
  `γ` occurs exactly once among the first `k` (`fwd_new`); by reversal (`rev`) the same holds at the end of `Ω` (`bwd_new`);
* `new_odd`: `γ` occurs an odd number of times in `Ω` (`δ(half) ≥ k`, `δ(Ω) ≥ k`, parity);
* so for `2k ≤ r ≤ 4k+2` it occurs exactly twice (contradiction), and for `r ≤ 2k-1` all new coordinates sit in the overlap of
  the first and the last `k` positions of `Ω`: `n - (k+l) ≤ 2k - r`, impossible for `r ≥ 2k+3-l` when `k > 3l-7`.
Result `symRun_le2`: `S(n,k,k+l) ≤ 4k+2l` for `k > 3l-7`, `k ≥ 2l` (`k` even) / `k ≥ 2l-3` (`k` odd) -- no Lemma 2 needed.
-/

open Finset

namespace Coil

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.deprecated false

variable {α : Type*} [Fintype α] [DecidableEq α] {k N : ℕ} {T : ℕ → α}

/-! ### reversal -/

/-- the reversed word -/
def rev (N : ℕ) (T : ℕ → α) : ℕ → α := fun i => T (N * (i + 1) - 1 - i)

lemma rev_cnt (per : ∀ i, T (i + N) = T i) (hN : 1 ≤ N) (t L : ℕ) (c : α) :
    cnt (rev N T) t L c = cnt T (N * (t + L) - (t + L)) L c := by
  rw [cnt_eq_sum, cnt_eq_sum, ← Finset.sum_range_reflect (fun j => if T (N * (t + L) - (t + L) + j) = c then 1 else 0)]
  apply sum_congr rfl
  intro j hj
  rw [mem_range] at hj
  have e : T (N * (t + L) - (t + L) + (L - 1 - j)) = rev N T (t + j) := by
    unfold rev
    have h1 : t + j + 1 ≤ N * (t + j + 1) := Nat.le_mul_of_pos_left _ hN
    have h2 : N * (t + L) = N * (t + j + 1) + (L - 1 - j) * N := by
      rw [show t + L = (t + j + 1) + (L - 1 - j) by omega, mul_add, mul_comm N (L - 1 - j)]
    have h3 : N * (t + L) - (t + L) + (L - 1 - j) = N * (t + j + 1) - 1 - (t + j) + (L - 1 - j) * N := by
      obtain ⟨X, hX⟩ : ∃ X, X = N * (t + j + 1) := ⟨_, rfl⟩
      obtain ⟨Y, hY⟩ : ∃ Y, Y = (L - 1 - j) * N := ⟨_, rfl⟩
      obtain ⟨Z, hZ⟩ : ∃ Z, Z = N * (t + L) := ⟨_, rfl⟩
      have h4 : L - 1 - j ≤ (L - 1 - j) * N := Nat.le_mul_of_pos_right _ hN
      rw [← hY] at h4
      rw [← hX, ← hY, ← hZ] at h2
      rw [← hX] at h1
      rw [← hX, ← hY, ← hZ]
      omega
    rw [h3, per_mul per]
  simp only [e]

theorem IsCoilWord.rev (h : IsCoilWord k N T) (hN : 1 ≤ N) : IsCoilWord k N (rev N T) := by
  have ho : ∀ t L, oddc (Coil.rev N T) t L = oddc T (N * (t + L) - (t + L)) L := by
    intro t L
    rw [oddc, oddc]
    simp_rw [rev_cnt h.per hN]
  refine ⟨fun i => ?_, fun c => ?_, fun t L h1 h2 h3 => ?_⟩
  · unfold Coil.rev
    have h1 : i + 1 ≤ N * (i + 1) := Nat.le_mul_of_pos_left _ hN
    have h2 : N * (i + N + 1) = N * (i + 1) + N * N := by ring
    have h3 : N ≤ N * N := Nat.le_mul_of_pos_left _ hN
    obtain ⟨M, hM⟩ : ∃ M, N * N = N + M * N := ⟨N - 1, by
      rw [show N + (N - 1) * N = (1 + (N - 1)) * N by ring, show 1 + (N - 1) = N by omega]⟩
    rw [show N * (i + N + 1) - 1 - (i + N) = N * (i + 1) - 1 - i + M * N by omega, per_mul h.per]
  · rw [rev_cnt h.per hN, cnt_period h.per]; exact h.closed c
  · rw [ho] at h3 ⊢; exact h.spread _ L h1 h2 h3

/-! ### the alternation lemma (forward) -/

section

variable {l : ℕ} (h : IsCoilWord k N T) (hk : 2 ≤ k) (hl : 1 ≤ l)
  (hn : 2 * Fintype.card α = 3 * k + l + 1)
  (run : ∀ i j, i < k + l → j < k + l → T i = T j → i = j)

include h hk hl hn run in
/-- Byrnes' Lemma 2.3: after the bit run `A` and `k` further transitions, the next `k+1` transitions are old
(they lie in `A`), and the odd counts of the two tracked windows alternate. -/
lemma alt (hN : 4 * k + 2 * l + 2 ≤ N) (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ k + 1) :
    oddc T 0 (k + l + k + i) = k + (i + 1) % 2 ∧ oddc T (k + l) (k + i) = k + i % 2 ∧
      cnt T 0 (k + l) (T (k + l + k + i - 1)) = 1 := by
  have hk1 : 1 ≤ k := by omega
  have hN2 : 2 * k + 2 ≤ N := by omega
  obtain ⟨hodd, hall⟩ := run_window h hk hl hn run (by omega)
  induction i, hi1 using Nat.le_induction with
  | base =>
    have e1 : oddc T (k + l) (k + 1) = k + 1 := oddc_short h hk1 hN2 le_rfl
    have hs := oddc_succ T 0 (k + l + k)
    have hf := f1 h hk1 (t := 0) (L := k + l + k) (by omega) (by omega)
    rw [zero_add, show k + l + k + 1 = k + l + (k + 1) by omega, hodd] at hs
    obtain ⟨c1, c2, c3, c4⟩ := hall (T (k + l + k))
    have e2 : cnt T (k + l) (k + 1) (T (k + l + k)) = cnt T (k + l) k (T (k + l + k)) + 1 := by
      rw [cnt_add, cnt_one, if_pos rfl]
    have e3 : cnt T 0 (k + l + k) (T (k + l + k)) = cnt T 0 (k + l) (T (k + l + k)) + cnt T (k + l) k (T (k + l + k)) := by
      rw [show k + l + k = (k + l) + k by omega, cnt_add, zero_add]
    have hodd' : Odd (cnt T 0 (k + l + k) (T (k + l + k))) := by
      by_contra hne
      rw [if_neg hne] at hs
      omega
    rw [Nat.odd_iff] at hodd'
    have b1 : oddc T 0 (k + l + k + 1) = k + (1 + 1) % 2 := by
      have : oddc T 0 (k + l + k + 1) = k := by rw [show k + l + k + 1 = k + l + (k + 1) by omega, hodd]
      omega
    have b2 : oddc T (k + l) (k + 1) = k + 1 % 2 := by omega
    refine ⟨b1, b2, ?_⟩
    rw [show k + l + k + 1 - 1 = k + l + k by omega]
    omega
  | succ i hi1 ih =>
    obtain ⟨ihP, ihQ, _⟩ := ih (by omega)
    obtain ⟨x, hx⟩ : ∃ x, x = T (k + l + k + i) := ⟨_, rfl⟩
    obtain ⟨c1, c2, c3, c4⟩ := hall x
    -- x does not occur among the k transitions before it
    have hlast : cnt T (k + l + i) k x = 0 := by
      have h1 := cnt_short h hk1 hN2 (t := k + l + i) (L := k + 1) le_rfl x
      rw [cnt_add, cnt_one, show k + l + i + k = k + l + k + i by omega, ← hx, if_pos rfl] at h1
      omega
    have hu := cnt_short h hk1 hN2 (t := k + l) (L := i) (by omega) x
    have eQ : cnt T (k + l) (k + i) x = cnt T (k + l) i x := by
      rw [show k + i = i + k by omega, cnt_add, hlast, add_zero]
    have eP : cnt T 0 (k + l + k + i) x = cnt T 0 (k + l) x + cnt T (k + l) i x := by
      rw [show k + l + k + i = (k + l) + (k + i) by omega, cnt_add, zero_add, eQ]
    have happ : 1 ≤ cnt T 0 (k + l + k + i) x :=
      le_trans c1 (cnt_mono T 0 (by omega) x)
    have E1 := oddc_succ T 0 (k + l + k + i)
    have E2 := oddc_succ T (k + l) (k + i)
    rw [zero_add, ← hx] at E1
    rw [show k + l + (k + i) = k + l + k + i by omega, ← hx] at E2
    have f1P := f1 h hk1 (t := 0) (L := k + l + k + i + 1) (by omega) (by omega)
    have f1Q := f1 h hk1 (t := k + l) (L := k + i + 1) (by omega) (by omega)
    rw [show k + l + k + (i + 1) = k + l + k + i + 1 by omega, show k + (i + 1) = k + i + 1 by omega,
      show k + l + k + i + 1 - 1 = k + l + k + i by omega, ← hx]
    rw [eP] at E1
    rw [eQ] at E2
    rcases Nat.mod_two_eq_zero_or_one i with hpar | hpar
    · -- i even: P = k+1, Q = k
      have hi2 : (i + 1) % 2 = 1 := by omega
      have hi3 : (i + 1 + 1) % 2 = 0 := by omega
      rw [hi2] at ihP
      rw [hpar] at ihQ
      rw [ihP] at E1
      rw [ihQ] at E2
      have hu0 : ¬ Odd (cnt T (k + l) i x) := by
        intro ho
        rw [if_pos ho] at E2
        omega
      rw [if_neg hu0] at E2
      rw [Nat.odd_iff] at hu0
      have hcA : cnt T 0 (k + l) x = 1 := by omega
      rw [hcA, show cnt T (k + l) i x = 0 by omega, if_pos (by decide)] at E1
      omega
    · -- i odd: P = k, Q = k+1
      have hi2 : (i + 1) % 2 = 0 := by omega
      have hi3 : (i + 1 + 1) % 2 = 1 := by omega
      rw [hi2] at ihP
      rw [hpar] at ihQ
      rw [ihP] at E1
      rw [ihQ] at E2
      have hev : ¬ Odd (cnt T 0 (k + l) x + cnt T (k + l) i x) := by
        intro ho
        rw [if_pos ho] at E1
        omega
      rw [if_neg hev] at E1
      rw [Nat.odd_iff] at hev
      have hcA : cnt T 0 (k + l) x = 1 := by omega
      have hcu : cnt T (k + l) i x = 1 := by omega
      rw [hcu, if_pos (by decide)] at E2
      omega

include h hk hl hn run in
/-- a new coordinate occurs exactly once among the first `k` transitions after the bit run and not among the next `k+1` -/
lemma fwd_new (hN : 4 * k + 2 * l + 2 ≤ N) (γ : α) (hγ : cnt T 0 (k + l) γ = 0) :
    cnt T (k + l) k γ = 1 ∧ cnt T (k + l + k) (k + 1) γ = 0 := by
  have hk1 : 1 ≤ k := by omega
  have hN2 : 2 * k + 2 ≤ N := by omega
  obtain ⟨hodd, hall⟩ := run_window h hk hl hn run (by omega)
  have hz : cnt T (k + l + k) (k + 1) γ = 0 := by
    apply cnt_eq_zero
    intro j hj he
    have := (alt h hk hl hn run hN (j + 1) (by omega) (by omega)).2.2
    rw [show k + l + k + (j + 1) - 1 = k + l + k + j by omega, he] at this
    omega
  refine ⟨?_, hz⟩
  obtain ⟨c1, c2, c3, c4⟩ := hall γ
  have e : cnt T 0 (k + l + (k + 1)) γ = cnt T 0 (k + l) γ + (cnt T (k + l) k γ + cnt T (k + l + k) 1 γ) := by
    rw [cnt_add T 0 (k + l) (k + 1), zero_add, cnt_add T (k + l) k 1]
  have e1 : cnt T (k + l + k) 1 γ = 0 := by
    have := cnt_mono T (k + l + k) (show 1 ≤ k + 1 by omega) γ
    omega
  have := cnt_short h hk1 hN2 (t := k + l) (L := k) (by omega) γ
  omega

end

/-! ### new coordinates occur an odd number of times after the bit run -/

section

variable {l : ℕ} (h : IsCoilWord k N T) (hk : 2 ≤ k) (hl : 1 ≤ l)
  (hn : 2 * Fintype.card α = 3 * k + l + 1)
  (run : ∀ i j, i < k + l → j < k + l → T i = T j → i = j)

include h hk hl hn run in
lemma new_odd (r : ℕ) (hr : k ≤ r) (hN : k + l + r + k ≤ N) (γ : α) (hγ : cnt T 0 (k + l) γ = 0) :
    Odd (cnt T (k + l) r γ) := by
  have hk1 : 1 ≤ k := by omega
  by_contra hno
  have hf1 := f1 h hk1 (t := 0) (L := k + l + r) (by omega) (by omega)
  have hf2 := f1 h hk1 (t := k + l) (L := r) hr (by omega)
  have p1 := oddc_parity T 0 (k + l + r)
  have p2 := oddc_parity T (k + l) r
  have key : ∀ c ∈ (univ : Finset α), ((if Odd (cnt T 0 (k + l + r) c) then 1 else 0)
      + (if Odd (cnt T (k + l) r c) then 1 else 0) + cnt T 0 (k + l) c) ≤ 2 := by
    intro c _
    have := cnt_run_le run c
    rw [cnt_add, zero_add]
    simp only [Nat.odd_iff]
    split_ifs <;> omega
  have key2 : ∃ c ∈ (univ : Finset α), ((if Odd (cnt T 0 (k + l + r) c) then 1 else 0)
      + (if Odd (cnt T (k + l) r c) then 1 else 0) + cnt T 0 (k + l) c) < 2 := by
    refine ⟨γ, mem_univ _, ?_⟩
    have e : cnt T 0 (k + l + r) γ = cnt T (k + l) r γ := by rw [cnt_add, zero_add, hγ, zero_add]
    rw [e, if_neg hno, hγ]
    norm_num
  have S := sum_lt_sum key key2
  simp only [sum_add_distrib, ← oddc_eq_sum, sum_cnt, sum_const, card_univ, smul_eq_mul] at S
  rw [Nat.odd_iff, Nat.odd_iff] at p1 p2
  omega

end

/-! ### the end of the half period (reversal) -/

lemma idx_rev (H L' : ℕ) (hL : L' ≤ H) (hH : 1 ≤ H) :
    2 * H * (2 * H + L') - (2 * H + L') = (H - L') + (4 * H + 2 * L' - 3) * H := by
  obtain ⟨Q, hQ⟩ : ∃ Q, Q + 3 = 4 * H + 2 * L' := ⟨4 * H + 2 * L' - 3, by omega⟩
  have e1 : (Q + 3) * H = 2 * H * (2 * H + L') := by rw [hQ]; ring
  have e2 : (Q + 3) * H = Q * H + 3 * H := by ring
  rw [show 4 * H + 2 * L' - 3 = Q by omega]
  omega

lemma cnt_shiftH {H : ℕ} (sym : ∀ i, T (i + H) = T i) (s q L : ℕ) (c : α) :
    cnt T (s + q * H) L c = cnt T s L c := by
  rw [cnt, cnt]
  exact congrArg card (filter_congr fun j _ => by rw [add_right_comm, per_mul sym])

section

variable {l H : ℕ} (h : IsCoilWord k N T) (hk : 2 ≤ k) (hl : 1 ≤ l)
  (hn : 2 * Fintype.card α = 3 * k + l + 1)
  (run : ∀ i j, i < k + l → j < k + l → T i = T j → i = j)
  (hNH : N = 2 * H) (sym : ∀ i, T (i + H) = T i)

include h hk hl hn run hNH sym in
/-- mirror image of `fwd_new`: a new coordinate occurs exactly once among the last `k` transitions of the half period,
and not among the `k+1` transitions before them -/
lemma bwd_new (hN : 4 * k + 2 * l + 2 ≤ N) (γ : α) (hγ : cnt T 0 (k + l) γ = 0) :
    cnt T (H - k) k γ = 1 ∧ cnt T (H - (2 * k + 1)) (k + 1) γ = 0 := by
  have hN1 : 1 ≤ N := by omega
  have hH1 : 1 ≤ H := by omega
  have haN : k + l ≤ N := by omega
  -- the reversed word, shifted so that its bit run starts at 0
  have hR : IsCoilWord k N (fun i => rev N T (i + (N - (k + l)))) := (h.rev hN1).shift _
  have hval : ∀ i, i < k + l → rev N T (i + (N - (k + l))) = T (k + l - 1 - i) := by
    intro i hi
    unfold rev
    have h1 : N * (i + (N - (k + l)) + 1) = (i + (N - (k + l))) * N + N := by ring
    rw [show N * (i + (N - (k + l)) + 1) - 1 - (i + (N - (k + l))) = k + l - 1 - i + (i + (N - (k + l))) * N by
      have h2 : i + (N - (k + l)) ≤ (i + (N - (k + l))) * N := Nat.le_mul_of_pos_right _ hN1
      generalize (i + (N - (k + l))) * N = Z at *
      omega, per_mul h.per]
  have runR : ∀ i j, i < k + l → j < k + l →
      rev N T (i + (N - (k + l))) = rev N T (j + (N - (k + l))) → i = j := by
    intro i j hi hj e
    rw [hval i hi, hval j hj] at e
    have := run _ _ (by omega) (by omega) e
    omega
  have hc : ∀ t L c, cnt (fun i => rev N T (i + (N - (k + l)))) t L c
      = cnt T (N * (t + (N - (k + l)) + L) - (t + (N - (k + l)) + L)) L c := by
    intro t L c
    have e : cnt (fun i => rev N T (i + (N - (k + l)))) t L c = cnt (rev N T) (t + (N - (k + l))) L c := by
      rw [cnt, cnt]
      exact congrArg card (filter_congr fun j _ => by rw [add_right_comm])
    rw [e, rev_cnt h.per hN1]
  have hγR : cnt (fun i => rev N T (i + (N - (k + l)))) 0 (k + l) γ = 0 := by
    rw [hc, show 0 + (N - (k + l)) + (k + l) = N by omega]
    have e : N * N - N = 0 + (2 * (N - 1)) * H := by
      have : N * N = N + (N - 1) * N := by
        rw [show N + (N - 1) * N = (1 + (N - 1)) * N by ring, show 1 + (N - 1) = N by omega]
      have e2 : (2 * (N - 1)) * H = (N - 1) * N := by rw [hNH]; ring
      omega
    rw [e, cnt_shiftH sym]
    exact hγ
  obtain ⟨f1', f2'⟩ := fwd_new hR hk hl hn runR hN γ hγR
  rw [hc] at f1' f2'
  constructor
  · rw [show k + l + (N - (k + l)) + k = N + k by omega, hNH, idx_rev H k (by omega) hH1, cnt_shiftH sym] at f1'
    exact f1'
  · rw [show k + l + k + (N - (k + l)) + (k + 1) = N + (2 * k + 1) by omega, hNH,
      idx_rev H (2 * k + 1) (by omega) hH1, cnt_shiftH sym] at f2'
    exact f2'

include h hk hl hn run hNH sym in
/-- **no symmetric code with a bit run of length `k+l` has `6k+6 ≤ N ≤ 7k+5`** (`k > 3l-7`, `k ≥ l+1`) -/
theorem symRun_mid_aux (h6 : 6 * k + 6 ≤ N) (h7 : N ≤ 7 * k + 5) (hk3 : 3 * l < k + 7) (hkl : l + 1 ≤ k) :
    False := by
  have hk1 : 1 ≤ k := by omega
  have hN : 4 * k + 2 * l + 2 ≤ N := by omega
  obtain ⟨r, hr⟩ : ∃ r, H = k + l + r := ⟨H - (k + l), by omega⟩
  have hrk : k ≤ r := by omega
  have hodd := fun γ hγ => new_odd h hk hl hn run r hrk (by omega) γ hγ
  have hfwd := fun γ hγ => fwd_new h hk hl hn run hN γ hγ
  have hbwd := fun γ hγ => bwd_new h hk hl hn run hNH sym hN γ hγ
  by_cases hr2 : 2 * k ≤ r
  · -- a new coordinate would occur exactly twice
    have hex : ∃ γ, cnt T 0 (k + l) γ = 0 := by
      by_contra hall
      push_neg at hall
      have h1 : ∑ c : α, 1 ≤ ∑ c, cnt T 0 (k + l) c :=
        sum_le_sum (fun c _ => Nat.one_le_iff_ne_zero.mpr (hall c))
      rw [sum_cnt] at h1
      simp only [sum_const, card_univ, smul_eq_mul, mul_one] at h1
      omega
    obtain ⟨γ, hγ⟩ := hex
    obtain ⟨a1, a2⟩ := hfwd γ hγ
    obtain ⟨b1, b2⟩ := hbwd γ hγ
    have ho := hodd γ hγ
    obtain ⟨m0, hm0⟩ : ∃ m0, r = k + (m0 + k) := ⟨r - 2 * k, by omega⟩
    have e : cnt T (k + l) r γ = cnt T (k + l) k γ + cnt T (k + l + k) m0 γ + cnt T (H - k) k γ := by
      rw [hm0, cnt_add, cnt_add, show k + l + k + m0 = H - k by omega]
      omega
    have hmid : cnt T (k + l + k) m0 γ = 0 := by
      by_cases hsmall : m0 ≤ k + 1
      · have := cnt_mono T (k + l + k) hsmall γ
        omega
      · obtain ⟨m2, hm2⟩ : ∃ m2, m0 = (k + 1) + m2 := ⟨m0 - (k + 1), by omega⟩
        obtain ⟨d0, hd0⟩ : ∃ d0, k + 1 = d0 + m2 := ⟨k + 1 - m2, by omega⟩
        have e2 := cnt_add T (H - (2 * k + 1)) d0 m2 γ
        rw [← hd0, show H - (2 * k + 1) + d0 = k + l + k + (k + 1) by omega] at e2
        rw [hm2, cnt_add, a2, zero_add]
        omega
    rw [e, a1, hmid, b1] at ho
    exact absurd ho (by decide)
  · -- all new coordinates lie in the overlap of the first and the last k positions
    obtain ⟨p1, hp1⟩ : ∃ p1, r = k + p1 := ⟨r - k, by omega⟩
    obtain ⟨q1, hq1⟩ : ∃ q1, k = p1 + q1 := ⟨k - p1, by omega⟩
    have hy : ∀ c, cnt T 0 (k + l) c = 0 → cnt T (k + l + p1) q1 c = 1 := by
      intro c hc0
      obtain ⟨a1, _⟩ := hfwd c hc0
      obtain ⟨b1, _⟩ := hbwd c hc0
      have ho := hodd c hc0
      have ex := cnt_add T (k + l) p1 q1 c
      rw [← hq1] at ex
      have ez := cnt_add T (k + l + p1) q1 p1 c
      rw [show q1 + p1 = k by omega, show k + l + p1 + q1 = k + l + k by omega,
        show k + l + p1 = H - k by omega] at ez
      have er := cnt_add T (k + l) k p1 c
      rw [← hp1] at er
      rw [er, Nat.odd_iff] at ho
      rw [show k + l + p1 = H - k by omega]
      omega
    have h1 : ∑ c : α, 1 ≤ ∑ c, (cnt T (k + l + p1) q1 c + cnt T 0 (k + l) c) := by
      apply sum_le_sum
      intro c _
      by_cases hc0 : cnt T 0 (k + l) c = 0
      · have := hy c hc0
        omega
      · omega
    rw [sum_add_distrib, sum_cnt, sum_cnt] at h1
    simp only [sum_const, card_univ, smul_eq_mul, mul_one] at h1
    omega

end

/-- **`S(n, k, k+l) ≤ 4k + 2l` without Lemma 2:** for `k > 3l - 7`, `k ≥ l + 1`, and `k ≥ 2l` (`k` even) or
`k ≥ 2l - 3` (`k` odd). -/
theorem symRun_le2 {l : ℕ} (hS : SymRun k N (k + l) T) (hk : 2 ≤ k) (hl : 1 ≤ l)
    (hn : 2 * Fintype.card α = 3 * k + l + 1) (hk3 : 3 * l < k + 7) (hkl : l + 1 ≤ k)
    (hL3 : if Even k then 2 * l ≤ k else 2 * l ≤ k + 3) : N ≤ 4 * k + 2 * l := by
  rcases symRun_gap hS hk hl hn with h1 | h2
  · exact h1
  · exfalso
    have h7 := length_le_seven hS.1 (by omega) l hn hL3
    obtain ⟨h, sym, t, run⟩ := hS
    obtain ⟨H, hH⟩ := even_length h
    have hNH : N = 2 * H := by omega
    have hH2 : N / 2 = H := by omega
    rw [hH2] at sym
    exact symRun_mid_aux (T := fun i => T (i + t)) (h.shift t) hk hl hn
      (fun i j hi hj e => run i j hi hj (by rw [Nat.add_comm t i, Nat.add_comm t j]; exact e)) hNH
      (fun i => by show T (i + H + t) = T (i + t); rw [add_right_comm, sym]) h2 h7 hk3 hkl

end Coil

#print axioms Coil.symRun_le2
