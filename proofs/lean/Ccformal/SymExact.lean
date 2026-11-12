import Ccformal.SymRun3
import Ccformal.Byrnes

/-!
# `S(n, k, k+l) = 4k + 2l` for ALL `l ≥ 2`, `k ≥ l - 1`  (S174)

Upper bound: `symRun_le_all` (SymRun3.lean).  Lower bound: Byrnes' word (`byrnes_word`).
So Byrnes' Conjecture 4.2 (`S(n,k,k+l) = K(n,k)`) holds at `(n,k)` IFF `K(n,k) = 4k + 2l`.
-/

namespace Coil

/-- **`S(n, k, k+l) = 4k + 2l` exactly, for every `l ≥ 2` and every `k ≥ l - 1`** (`2n = 3k + l + 1`): every symmetric
spread-`k` circuit code in `Q_n` with a bit run of length `k+l` has length `≤ 4k+2l`, and one of length `4k+2l` exists.
(Byrnes, arXiv 2008.04839: for `k ≥ 2l-2` / `2l+1`.) -/
theorem symRun_exact (k l n : ℕ) (hl : 2 ≤ l) (hkl : l ≤ k + 1) (hn : 2 * n = 3 * k + l + 1) :
    (∀ (N : ℕ) (T : ℕ → Fin n), SymRun k N (k + l) T → N ≤ 4 * k + 2 * l) ∧
      ∃ T : ℕ → Fin n, SymRun k (4 * k + 2 * l) (k + l) T := by
  refine ⟨fun N T hS => symRun_le_all hS (by omega) (by omega) (by rw [Fintype.card_fin]; exact hn), ?_⟩
  obtain ⟨T, hT, hsym, hrun⟩ := byrnes_word k l n hl hkl hn
  refine ⟨T, hT, fun i => ?_, 0, fun i j hi hj e => ?_⟩
  · rw [show (4 * k + 2 * l) / 2 = 2 * k + l by omega]; exact hsym i
  · rw [zero_add, zero_add] at e; exact hrun i j hi hj e

/-- **Conjecture 4.2 fails wherever a code longer than `4k + 2l` exists:** then `S(n,k,k+l) = 4k+2l < K(n,k)`. -/
theorem conj42_iff (k l n : ℕ) (hl : 2 ≤ l) (hkl : l ≤ k + 1) (hn : 2 * n = 3 * k + l + 1)
    (N : ℕ) (v : ℕ → Fin n → Bool) (hv : IsCoil k N v) (hN : 4 * k + 2 * l < N) :
    ∀ (N' : ℕ) (T : ℕ → Fin n), SymRun k N' (k + l) T → N' < N := by
  intro N' T hS
  have := (symRun_exact k l n hl hkl hn).1 N' T hS
  omega

end Coil

#print axioms Coil.symRun_exact
#print axioms Coil.conj42_iff
