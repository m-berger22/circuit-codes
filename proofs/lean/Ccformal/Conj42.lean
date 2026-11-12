import Ccformal.Lines
import Ccformal.Contraction
import Ccformal.SymRun2
import Ccformal.Example
import Ccformal.Values.C_28_16
import Ccformal.Values.K_33_19

/-!
# Byrnes' Conjecture 4.2 fails on every line `l ≥ 6` -- and holds beyond `~ l²/2`

Conjecture 4.2 (arXiv 2008.04839) says `K(n,k) = 4k + 2l` (`l = 2n - 3k - 1`) in the range of his Theorem 1.3
(`k ≥ 2l+1`, resp. `k ≥ 2l-2` for even `k`).

* `excess2_lines`: for `c ≥ 2`, `j ≤ 3`: a code of length `4k + 2l + 2` on the line `l = 4c+1+j` at `k = 8c²+4c-j`
  (family 10 at `l₀ = 4c+1`, `k₀ = (l₀²-1)/2`, contracted `j` times: Deimer).
* `conj42_fails`: for EVERY `l ≥ 6` there are `k ≥ 2l+1`, `n = (3k+l+1)/2` and a spread-`k` circuit code in `Q_n`
  longer than `4k + 2l`.   (`l = 6, 7, 8`: kernel-checked codes (23,13,66), (28,16,80), (33,19,96).)
* `K_beyond` (Byrnes.lean): `K(n,k) = 4k + 2l` whenever the Main Theorem applies.
-/

open Finset

namespace Coil

set_option linter.unusedVariables false

/-- contraction of `j ≤ 3` twice-used coordinates, with the parameters as free variables -/
lemma contract_j {n k N : ℕ} {T : ℕ → Fin n} (hT : IsCoilWord k N T) (hN : 2 * k + 2 ≤ N) (C : Finset (Fin n))
    (hC3 : #C = 3) (hC : ∀ c ∈ C, cnt T 0 N c = 2) (j : ℕ) (hj : j ≤ 3) (hjk : j < k) (n' k' N' : ℕ)
    (hn' : n' = n - j) (hk' : k' = k - j) (hN' : N' = N - 2 * j) :
    ∃ v : ℕ → Fin n' → Bool, IsCoil k' N' v := by
  obtain ⟨C', hsub, hcard⟩ := Finset.exists_subset_card_eq (s := C) (n := j) (by omega)
  subst hcard
  obtain ⟨T'', hT''⟩ := contraction_fin hT hN C' (fun c hc => hC c (hsub hc)) hjk
  subst hn' hk' hN'
  exact hT''.exists_coil

/-- excess-2 codes on the lines `l = 4c+1+j`, `j ≤ 3` -/
theorem excess2_lines (c j : ℕ) (hc : 2 ≤ c) (hj : j ≤ 3) :
    ∃ v : ℕ → Fin (12 * c * c + 8 * c + 1 - j) → Bool,
      IsCoil (8 * c * c + 4 * c - j) (32 * c * c + 24 * c + 4 - 2 * j) v := by
  obtain ⟨a, rfl⟩ : ∃ a, c = a + 2 := ⟨c - 2, by omega⟩
  obtain ⟨T, hT, C, hC3, hC⟩ := fam10_word a 0
  have en : f10n a 0 = 12 * (a + 2) * (a + 2) + 8 * (a + 2) + 1 := by unfold f10n; ring
  have ek : f10k a 0 = 8 * (a + 2) * (a + 2) + 4 * (a + 2) := by unfold f10k; ring
  have eN : f10N a 0 = 32 * (a + 2) * (a + 2) + 24 * (a + 2) + 4 := by unfold f10N; ring
  have ek' : f10k a 0 = 8 * (a * a) + 36 * a + 40 := by unfold f10k; ring
  have eN' : f10N a 0 = 32 * (a * a) + 152 * a + 180 := by unfold f10N; ring
  exact contract_j hT (by omega) C hC3 hC j hj (by omega) _ _ _ (by rw [en]) (by rw [ek]) (by rw [eN])

/-- **Byrnes' Conjecture 4.2 fails on every line `l ≥ 6`.** -/
theorem conj42_fails (l : ℕ) (hl : 6 ≤ l) :
    ∃ k n N, 2 * n = 3 * k + l + 1 ∧ 2 * l + 1 ≤ k ∧ 4 * k + 2 * l < N ∧
      ∃ v : ℕ → Fin n → Bool, IsCoil k N v := by
  by_cases h9 : 9 ≤ l
  · obtain ⟨c, j, hj, rfl⟩ : ∃ c j, j ≤ 3 ∧ l = 4 * c + 1 + j := ⟨(l - 1) / 4, (l - 1) % 4, by omega, by omega⟩
    have hc : 2 ≤ c := by omega
    have h8 : 8 * c * 2 ≤ 8 * c * c := Nat.mul_le_mul_left _ hc
    have e12 : 12 * c * c = 12 * (c * c) := by ring
    have e8 : 8 * c * c = 8 * (c * c) := by ring
    have e32 : 32 * c * c = 32 * (c * c) := by ring
    exact ⟨8 * c * c + 4 * c - j, 12 * c * c + 8 * c + 1 - j, 32 * c * c + 24 * c + 4 - 2 * j,
      by omega, by omega, by omega, excess2_lines c j hc hj⟩
  · have h : l = 6 ∨ l = 7 ∨ l = 8 := by omega
    rcases h with rfl | rfl | rfl
    · obtain ⟨v, hv, _⟩ := counterexample_23_13
      exact ⟨13, 23, 66, by norm_num, by norm_num, by norm_num, v, hv⟩
    · exact ⟨16, 28, 80, by norm_num, by norm_num, by norm_num, coil_28_16⟩
    · exact ⟨19, 33, 96, by norm_num, by norm_num, by norm_num, coil_33_19⟩

/-- **Byrnes' Conjecture 4.2 (`S(n,k,k+l) = K(n,k)` for `k ≥ 2l+1`) is FALSE on EVERY line `l ≥ 6`, with no quoted
step:**  there are `k ≥ 2l+1` and `n = (3k+l+1)/2` such that
* every SYMMETRIC spread-`k` circuit code in `Q_n` with a bit run of length `k+l` has length `≤ 4k+2l`,
  and one of length exactly `4k+2l` exists  (`S(n,k,k+l) = 4k+2l`);
* there is a spread-`k` circuit code in `Q_n` of length `> 4k+2l`  (`K(n,k) > 4k+2l`).
(Upper bound for symmetric codes: `symRun_le` (Lemma 2) for `l ≠ 7`, `symRun_le2` (Lemma 3 + alternation) at `(28,16)`.) -/
theorem conj42_false (l : ℕ) (hl : 6 ≤ l) :
    ∃ k n, 2 * n = 3 * k + l + 1 ∧ 2 * l + 1 ≤ k ∧
      (∀ (N : ℕ) (T : ℕ → Fin n), SymRun k N (k + l) T → N ≤ 4 * k + 2 * l) ∧
      (∃ T : ℕ → Fin n, SymRun k (4 * k + 2 * l) (k + l) T) ∧
      ∃ N, 4 * k + 2 * l < N ∧ ∃ v : ℕ → Fin n → Bool, IsCoil k N v := by
  -- the witnesses, with the upper bound for symmetric codes
  have key : ∃ k n N, 2 * n = 3 * k + l + 1 ∧ 2 * l + 1 ≤ k ∧ 4 * k + 2 * l < N ∧
      (∀ (N' : ℕ) (T : ℕ → Fin n), SymRun k N' (k + l) T → N' ≤ 4 * k + 2 * l) ∧
      ∃ v : ℕ → Fin n → Bool, IsCoil k N v := by
    by_cases h7 : l = 7
    · subst h7
      refine ⟨16, 28, 80, by norm_num, by norm_num, by norm_num, fun N' T hS => ?_, coil_28_16⟩
      exact symRun_le2 hS (by norm_num) (by norm_num) (by rw [Fintype.card_fin]) (by norm_num) (by norm_num)
        (by rw [if_pos (by decide)]; norm_num)
    · have key2 : ∃ k n N, 2 * n = 3 * k + l + 1 ∧ 2 * l + 1 ≤ k ∧ 4 * k + 2 * l < N ∧
          6 * n + 6 * ((k + 2) / 2) < k + k % 2 + 12 * (k + 1) ∧ ∃ v : ℕ → Fin n → Bool, IsCoil k N v := by
        by_cases h9 : 9 ≤ l
        · obtain ⟨c, j, hj, rfl⟩ : ∃ c j, j ≤ 3 ∧ l = 4 * c + 1 + j :=
            ⟨(l - 1) / 4, (l - 1) % 4, by omega, by omega⟩
          have hc : 2 ≤ c := by omega
          have h8 : 8 * c * 2 ≤ 8 * c * c := Nat.mul_le_mul_left _ hc
          have e12 : 12 * c * c = 12 * (c * c) := by ring
          have e8 : 8 * c * c = 8 * (c * c) := by ring
          have e32 : 32 * c * c = 32 * (c * c) := by ring
          exact ⟨8 * c * c + 4 * c - j, 12 * c * c + 8 * c + 1 - j, 32 * c * c + 24 * c + 4 - 2 * j,
            by omega, by omega, by omega, by omega, excess2_lines c j hc hj⟩
        · have h : l = 6 ∨ l = 8 := by omega
          rcases h with rfl | rfl
          · obtain ⟨v, hv, _⟩ := counterexample_23_13
            exact ⟨13, 23, 66, by norm_num, by norm_num, by norm_num, by norm_num, v, hv⟩
          · exact ⟨19, 33, 96, by norm_num, by norm_num, by norm_num, by norm_num, coil_33_19⟩
      obtain ⟨k, n, N, hn, hk, hN, hlong, hv⟩ := key2
      refine ⟨k, n, N, hn, hk, hN, fun N' T hS => ?_, hv⟩
      exact symRun_le hS (by omega) (by omega) (by rw [Fintype.card_fin]; exact hn)
        (by rw [Fintype.card_fin]; exact hlong)
  obtain ⟨k, n, N, hn, hk, hN, hS, hv⟩ := key
  refine ⟨k, n, hn, hk, hS, ?_, N, hN, hv⟩
  obtain ⟨T, hT, hsym, hrun⟩ := byrnes_word k l n (by omega) (by omega) hn
  refine ⟨T, hT, fun i => ?_, 0, fun i j hi hj e => hrun i j hi hj (by simpa using e)⟩
  rw [show (4 * k + 2 * l) / 2 = 2 * k + l by omega]
  exact hsym i

end Coil

#print axioms Coil.excess2_lines
#print axioms Coil.conj42_fails
#print axioms Coil.conj42_false
