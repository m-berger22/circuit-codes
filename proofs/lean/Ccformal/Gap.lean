import Ccformal.Conj42
import Ccformal.Fam6

/-!
# `K(n,k) - S(n,k,k+l)` is unbounded

At every point of family 6 × m (`p = 4c+8`, `m = 2μ+1`, `l = m(p-2)+2`, `k = m p(p+2)/4 - 1`) and of family 10
(`p = 4a+9`, `l = p + (2p-2)i`, `k = (p²-1)/2 + p(p+1)i`):
* every symmetric spread-`k` circuit code with a bit run of length `k+l` has length `≤ 4k+2l`, and one of length `4k+2l`
  exists (`S(n,k,k+l) = 4k+2l`: `symRun_le`, `byrnes_word`);
* `K(n,k) = 4k+2l+4m` resp. `4k+2l+4i+2` (`K_family6`, `K_family10`).
So Byrnes' Conjecture 4.2 (`S = K` for `k ≥ 2l+1`) fails by an arbitrarily large amount (`conj42_gap_unbounded`).
-/

namespace Coil

set_option linter.unusedVariables false

/-- family 6 × m: `S(n,k,k+l) = 4k+2l` and `K(n,k) = 4k+2l+4m` -/
theorem conj42_gap_family6 (c μ : ℕ) :
    2 * f6n c μ = 3 * f6k c μ + ((2 * μ + 1) * (4 * c + 6) + 2) + 1 ∧
    2 * ((2 * μ + 1) * (4 * c + 6) + 2) + 1 ≤ f6k c μ ∧
    (∀ (N : ℕ) (T : ℕ → Fin (f6n c μ)), SymRun (f6k c μ) N (f6k c μ + ((2 * μ + 1) * (4 * c + 6) + 2)) T →
      N ≤ 4 * f6k c μ + 2 * ((2 * μ + 1) * (4 * c + 6) + 2)) ∧
    (∃ T : ℕ → Fin (f6n c μ), SymRun (f6k c μ) (4 * f6k c μ + 2 * ((2 * μ + 1) * (4 * c + 6) + 2))
      (f6k c μ + ((2 * μ + 1) * (4 * c + 6) + 2)) T) ∧
    IsMaxLength (f6n c μ) (f6k c μ) (4 * f6k c μ + 2 * ((2 * μ + 1) * (4 * c + 6) + 2) + 4 * (2 * μ + 1)) := by
  obtain ⟨_, _, h2n, hN⟩ := f6_params c μ
  have ek : f6k c μ = 4 * (c * c) + 18 * c + 19 + 8 * (c * c * μ) + 36 * (c * μ) + 40 * μ := by
    unfold f6k; ring
  have en : f6n c μ = 6 * (c * c) + 29 * c + 33 + 12 * (c * c * μ) + 58 * (c * μ) + 66 * μ := by
    unfold f6n; ring
  have el : (2 * μ + 1) * (4 * c + 6) + 2 = 8 * (c * μ) + 12 * μ + 4 * c + 8 := by ring
  obtain ⟨l, hl⟩ : ∃ l, l = (2 * μ + 1) * (4 * c + 6) + 2 := ⟨_, rfl⟩
  rw [← hl] at h2n hN el ⊢
  refine ⟨h2n, by omega, fun N T hS => ?_, ?_, ?_⟩
  · exact symRun_le hS (by omega) (by omega) (by rw [Fintype.card_fin]; exact h2n)
      (by rw [Fintype.card_fin]; omega)
  · obtain ⟨T, hT, hsym, hrun⟩ := byrnes_word (f6k c μ) l (f6n c μ) (by omega) (by omega) h2n
    refine ⟨T, hT, fun i => ?_, 0, fun i j hi hj e => hrun i j hi hj (by simpa using e)⟩
    rw [show (4 * f6k c μ + 2 * l) / 2 = 2 * f6k c μ + l by omega]
    exact hsym i
  · rw [← hN]
    exact K_family6 c μ

/-- family 10: `S(n,k,k+l) = 4k+2l` and `K(n,k) = 4k+2l+4i+2` -/
theorem conj42_gap_family10 (a i : ℕ) :
    2 * f10n a i = 3 * f10k a i + ((4 * a + 9) + (8 * a + 16) * i) + 1 ∧
    2 * ((4 * a + 9) + (8 * a + 16) * i) + 1 ≤ f10k a i ∧
    (∀ (N : ℕ) (T : ℕ → Fin (f10n a i)), SymRun (f10k a i) N (f10k a i + ((4 * a + 9) + (8 * a + 16) * i)) T →
      N ≤ 4 * f10k a i + 2 * ((4 * a + 9) + (8 * a + 16) * i)) ∧
    (∃ T : ℕ → Fin (f10n a i), SymRun (f10k a i) (4 * f10k a i + 2 * ((4 * a + 9) + (8 * a + 16) * i))
      (f10k a i + ((4 * a + 9) + (8 * a + 16) * i)) T) ∧
    IsMaxLength (f10n a i) (f10k a i) (4 * f10k a i + 2 * ((4 * a + 9) + (8 * a + 16) * i) + 4 * i + 2) := by
  have ek : f10k a i = 8 * (a * a) + 36 * a + 40 + 16 * (a * a * i) + 76 * (a * i) + 90 * i := by
    unfold f10k; ring
  have en : f10n a i = 12 * (a * a) + 56 * a + 65 + 24 * (a * a * i) + 118 * (a * i) + 143 * i := by
    unfold f10n; ring
  have eN : f10N a i = 32 * (a * a) + 152 * a + 180 + 64 * (a * a * i) + 320 * (a * i) + 396 * i := by
    unfold f10N; ring
  have el : (4 * a + 9) + (8 * a + 16) * i = 8 * (a * i) + 16 * i + 4 * a + 9 := by ring
  obtain ⟨l, hl⟩ : ∃ l, l = (4 * a + 9) + (8 * a + 16) * i := ⟨_, rfl⟩
  rw [← hl] at el ⊢
  have h2n : 2 * f10n a i = 3 * f10k a i + l + 1 := by omega
  refine ⟨h2n, by omega, fun N T hS => ?_, ?_, ?_⟩
  · exact symRun_le hS (by omega) (by omega) (by rw [Fintype.card_fin]; exact h2n)
      (by rw [Fintype.card_fin]; omega)
  · obtain ⟨T, hT, hsym, hrun⟩ := byrnes_word (f10k a i) l (f10n a i) (by omega) (by omega) h2n
    refine ⟨T, hT, fun i' => ?_, 0, fun i' j hi hj e => hrun i' j hi hj (by simpa using e)⟩
    rw [show (4 * f10k a i + 2 * l) / 2 = 2 * f10k a i + l by omega]
    exact hsym i'
  · rw [show 4 * f10k a i + 2 * l + 4 * i + 2 = f10N a i by omega]
    exact K_family10 a i

/-- **`K - S` is unbounded:** for every `g` there are `k ≥ 2l+1`, `n = (3k+l+1)/2` with
`S(n,k,k+l) ≤ 4k+2l` and `K(n,k) = 4k+2l+4(2g+1)`. -/
theorem conj42_gap_unbounded (g : ℕ) :
    ∃ k l n, 2 * n = 3 * k + l + 1 ∧ 2 * l + 1 ≤ k ∧
      (∀ (N : ℕ) (T : ℕ → Fin n), SymRun k N (k + l) T → N ≤ 4 * k + 2 * l) ∧
      IsMaxLength n k (4 * k + 2 * l + 4 * (2 * g + 1)) := by
  obtain ⟨h1, h2, h3, _, h5⟩ := conj42_gap_family6 0 g
  exact ⟨_, _, _, h1, h2, h3, h5⟩

end Coil

#print axioms Coil.conj42_gap_family6
#print axioms Coil.conj42_gap_family10
#print axioms Coil.conj42_gap_unbounded
