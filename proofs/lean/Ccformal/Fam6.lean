import Ccformal.Fam6Word
import Ccformal.Fam10
import Ccformal.Values.K_33_19

/-!
# Family 6 × m = Theorem 18 of PROOF9.md (m = 1: Theorem 13), fully formal: unbounded excess on even lines

For `c, μ ≥ 0` put `p = 4c + 8` (`p ≡ 0 mod 4`, `p ≥ 8`), `m = 2μ + 1` (odd),

      k = m p (p+2)/4 - 1,      n = m (3p-2)(p+4)/8,      l = 2n - 3k - 1 = m (p-2) + 2.

Then  `K(n,k) = m p (p+4) = 4k + 2l + 4m`  (`K_family6`): exact values with excess `4m` over Byrnes' `4k + 2l`.
`(p, m) = (8, 1)` is the kernel-checked code (33,19,96); all other cases: the gap criterion (Fam6Count/Word).
-/

open Finset

namespace Coil

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

def f6k (c μ : ℕ) : ℕ := 4 * c * c + 18 * c + 19 + (8 * c * c + 36 * c + 40) * μ
def f6n (c μ : ℕ) : ℕ := (2 * μ + 1) * (c + 3) * (6 * c + 11)
def f6N (c μ : ℕ) : ℕ := 16 * (c + 2) * (c + 3) * (2 * μ + 1)

lemma f6_par (c μ : ℕ) (hs : 1 ≤ c ∨ 1 ≤ μ) :
    Fam6.Par c μ (4 * c + 8) (f6k c μ + 1) ((4 * c + 8) * μ + (2 * c + 4)) (μ * (2 * c + 5) + c + 2)
      (μ * (2 * c + 1) + c) :=
  ⟨rfl, by unfold f6k; ring, rfl, by unfold f6k; ring, by unfold f6k; ring, hs⟩

/-- the lower bound: the code exists -/
theorem fam6_coil (c μ : ℕ) (hs : 1 ≤ c ∨ 1 ≤ μ) :
    ∃ v : ℕ → Fin (f6n c μ) → Bool, IsCoil (f6k c μ) (f6N c μ) v := by
  obtain ⟨T, hT⟩ := Fam6.word_exists (f6_par c μ hs) (f6n c μ) (le_of_eq (by unfold f6n; ring))
  rw [show 4 * (f6k c μ + 1) + 4 * ((4 * c + 8) * μ + (2 * c + 4)) = f6N c μ by unfold f6k f6N; ring,
    Nat.add_sub_cancel] at hT
  exact hT.exists_coil

/-- upper bound at a zero of the Lemma-1 quadratic for `L = 2k+2`, `k` odd -/
theorem isMaxLength_of_root_odd {n k N : ℕ} (hv : ∃ v : ℕ → Fin n → Bool, IsCoil k N v) (hk : 1 ≤ k) (hko : Odd k)
    (h3 : 3 * k + 2 ≤ N) (hlong : 6 * n < 10 * k + 10) (hNs : N ≤ 2 * k + 2 * n + 3)
    (hid : (N : ℤ) * (7 * (k + 1) + 2 * n - N) = 16 * n * (k + 1)) : IsMaxLength n k N := by
  obtain ⟨h, hh⟩ := hko
  apply isMaxLength_of_chord hv hk (2 * k + 2) (by omega) (by omega)
  intro M hM1 hM2 _
  refine ⟨by omega, by omega, by omega, by omega, ?_⟩
  rw [show (2 * k + 2 - k) / 2 = h + 1 by omega]
  have e : ((M : ℤ) - 2 * n) * (4 * ((2 * k + 2 : ℕ) : ℤ) - M) - 2 * (M : ℤ) * ((h + 1 : ℕ) : ℤ)
      = ((M : ℤ) - N) * (7 * (k + 1) + 2 * n - N - M) := by
    have hk' : (k : ℤ) = 2 * h + 1 := by exact_mod_cast hh
    push_cast
    rw [hk'] at hid ⊢
    linear_combination hid
  have p1 : (0 : ℤ) < (M : ℤ) - N := by
    have : (N : ℤ) < M := by exact_mod_cast hM2
    linarith
  have p2 : (0 : ℤ) < 7 * ((k : ℤ) + 1) + 2 * n - N - M := by
    have a1 : (M : ℤ) < 5 * k + 4 := by exact_mod_cast hM1
    have a2 : (N : ℤ) ≤ 2 * k + 2 * n + 3 := by exact_mod_cast hNs
    linarith
  have := mul_pos p1 p2
  linarith

/-- **Theorem 18 (family 6 × m): `K(n,k) = 4k + 2l + 4m`**, for all `p = 4c+8`, `m = 2μ+1`. -/
theorem K_family6 (c μ : ℕ) : IsMaxLength (f6n c μ) (f6k c μ) (f6N c μ) := by
  by_cases hs : 1 ≤ c ∨ 1 ≤ μ
  · have ek : f6k c μ = 4 * (c * c) + 18 * c + 19 + 8 * (c * c * μ) + 36 * (c * μ) + 40 * μ := by
      unfold f6k; ring
    have en : f6n c μ = 6 * (c * c) + 29 * c + 33 + 12 * (c * c * μ) + 58 * (c * μ) + 66 * μ := by
      unfold f6n; ring
    have eN : f6N c μ = 16 * (c * c) + 80 * c + 96 + 32 * (c * c * μ) + 160 * (c * μ) + 192 * μ := by
      unfold f6N; ring
    apply isMaxLength_of_root_odd (fam6_coil c μ hs) (by omega)
      ⟨2 * (c * c) + 9 * c + 9 + 4 * (c * c * μ) + 18 * (c * μ) + 20 * μ, by omega⟩ (by omega) (by omega) (by omega)
    unfold f6k f6n f6N
    push_cast
    ring
  · obtain rfl : c = 0 := by omega
    obtain rfl : μ = 0 := by omega
    exact K_33_19

/-- the parameters in the usual notation: `p = 4c+8`, `m = 2μ+1` -/
lemma f6_params (c μ : ℕ) :
    4 * (f6k c μ + 1) = (2 * μ + 1) * (4 * c + 8) * (4 * c + 10) ∧
    8 * f6n c μ = (2 * μ + 1) * (3 * (4 * c + 8) - 2) * (4 * c + 12) ∧
    2 * f6n c μ = 3 * f6k c μ + ((2 * μ + 1) * (4 * c + 6) + 2) + 1 ∧
    f6N c μ = 4 * f6k c μ + 2 * ((2 * μ + 1) * (4 * c + 6) + 2) + 4 * (2 * μ + 1) := by
  have e : 3 * (4 * c + 8) - 2 = 12 * c + 22 := by omega
  rw [e]
  unfold f6n f6k f6N
  refine ⟨by ring, by ring, by ring, by ring⟩

end Coil

#print axioms Coil.K_family6
