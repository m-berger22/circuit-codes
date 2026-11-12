import Ccformal.Fam10Word

/-!
# Family 10 = Theorems 36 and 36' of PROOF16.md, fully formal (lower AND upper bound, all parameters)

For `a, i ≥ 0` put `p = 4a+9`, `l = p + (2p-2) i`, `k = (p²-1)/2 + p(p+1) i`, `n = (3k+l+1)/2`.  Then

      K(n, k) = 4k + 2l + 4i + 2.

`i = 0`:  `K = 4k + 2l + 2` at `k = (l²-1)/2` for every `l ≡ 1 (mod 4)`, `l ≥ 9`: the Main Theorem (`coil_length_bound`,
which needs `k > (l²-1)/2`) is sharp on all these lines (`kmax_exact_l1`).  `i ≥ 1`: exact values with excess `4i+2`.
-/

open Finset

namespace Coil

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

def f10k (a i : ℕ) : ℕ := 8 * a * a + 36 * a + 40 + (16 * a * a + 76 * a + 90) * i
def f10n (a i : ℕ) : ℕ := (6 * a + 13) * (2 * a + 5 + (4 * a + 11) * i)
def f10N (a i : ℕ) : ℕ := 32 * a * a + 152 * a + 180 + (64 * a * a + 320 * a + 396) * i

lemma f10_par (a i : ℕ) :
    Fam10.Par a i (4 * a + 9) (f10k a i + 1) ((4 * a + 9) * i + (2 * a + 4)) (2 * a + 4 + (4 * a + 10) * i)
      (2 * a + 3 + (4 * a + 8) * i) :=
  ⟨rfl, by unfold f10k; ring, rfl, by unfold f10k; ring, by unfold f10k; ring⟩

/-- the word of family 10, with three coordinates that are used exactly twice -/
theorem fam10_word (a i : ℕ) : ∃ T : ℕ → Fin (f10n a i), IsCoilWord (f10k a i) (f10N a i) T ∧
    ∃ C : Finset (Fin (f10n a i)), C.card = 3 ∧ ∀ c ∈ C, cnt T 0 (f10N a i) c = 2 := by
  obtain ⟨T, hT, C, hC3, hC⟩ := Fam10.word_exists (f10_par a i) (f10n a i) (le_of_eq (by unfold f10n; ring))
  have e : 4 * (f10k a i + 1) + 4 * ((4 * a + 9) * i + (2 * a + 4)) = f10N a i := by unfold f10k f10N; ring
  rw [e, Nat.add_sub_cancel] at hT
  rw [e] at hC
  exact ⟨T, hT, C, hC3, hC⟩

/-- the lower bound: the code exists -/
theorem fam10_coil (a i : ℕ) : ∃ v : ℕ → Fin (f10n a i) → Bool, IsCoil (f10k a i) (f10N a i) v := by
  obtain ⟨T, hT, _⟩ := fam10_word a i
  exact hT.exists_coil

/-- upper bound at a zero of the Lemma-1 quadratic for `L = 2k+1` (PROOF16 sec. 1) -/
theorem isMaxLength_of_root {n k N : ℕ} (hv : ∃ v : ℕ → Fin n → Bool, IsCoil k N v) (hk : 1 ≤ k) (hke : Even k)
    (h3 : 3 * k + 1 ≤ N) (hlong : 6 * n < 10 * k + 6) (hNs : N ≤ 2 * k + 2 * n)
    (hid : (N : ℤ) * (7 * k + 4 + 2 * n - N) = 2 * n * (8 * k + 4)) : IsMaxLength n k N := by
  obtain ⟨h, hh⟩ := hke
  apply isMaxLength_of_chord hv hk (2 * k + 1) (by omega) (by omega)
  intro M hM1 hM2 _
  refine ⟨by omega, by omega, by omega, by omega, ?_⟩
  rw [show (2 * k + 1 - k) / 2 = h by omega]
  have e : ((M : ℤ) - 2 * n) * (4 * ((2 * k + 1 : ℕ) : ℤ) - M) - 2 * (M : ℤ) * h
      = ((M : ℤ) - N) * (7 * k + 4 + 2 * n - N - M) := by
    have hk' : (k : ℤ) = 2 * h := by exact_mod_cast (by omega : k = 2 * h)
    push_cast
    rw [hk'] at hid ⊢
    linear_combination hid
  have p1 : (0 : ℤ) < (M : ℤ) - N := by
    have : (N : ℤ) < M := by exact_mod_cast hM2
    linarith
  have p2 : (0 : ℤ) < 7 * (k : ℤ) + 4 + 2 * n - N - M := by
    have a1 : (M : ℤ) < 5 * k + 4 := by exact_mod_cast hM1
    have a2 : (N : ℤ) ≤ 2 * k + 2 * n := by exact_mod_cast hNs
    linarith
  have := mul_pos p1 p2
  linarith

/-- **Theorems 36 and 36' (family 10): `K(n,k) = 4k + 2l + 4i + 2`**, for all `a, i ≥ 0`
(`p = 4a+9`, `l = p + (2p-2)i`, `k = (p²-1)/2 + p(p+1)i`, `n = (3k+l+1)/2`). -/
theorem K_family10 (a i : ℕ) : IsMaxLength (f10n a i) (f10k a i) (f10N a i) := by
  have ek : f10k a i = 8 * (a * a) + 36 * a + 40 + 16 * (a * a * i) + 76 * (a * i) + 90 * i := by
    unfold f10k; ring
  have en : f10n a i = 12 * (a * a) + 56 * a + 65 + 24 * (a * a * i) + 118 * (a * i) + 143 * i := by
    unfold f10n; ring
  have eN : f10N a i = 32 * (a * a) + 152 * a + 180 + 64 * (a * a * i) + 320 * (a * i) + 396 * i := by
    unfold f10N; ring
  apply isMaxLength_of_root (fam10_coil a i) (by omega)
    ⟨4 * (a * a) + 18 * a + 20 + 8 * (a * a * i) + 38 * (a * i) + 45 * i, by omega⟩ (by omega) (by omega) (by omega)
  unfold f10k f10n f10N
  push_cast
  ring

/-- the parameters in the usual notation -/
lemma f10_params (a i : ℕ) :
    2 * f10n a i = 3 * f10k a i + ((4 * a + 9) + (2 * (4 * a + 9) - 2) * i) + 1 ∧
    2 * f10k a i + 1 = (4 * a + 9) * (4 * a + 9) + 2 * (4 * a + 9) * (4 * a + 10) * i ∧
    f10N a i = 4 * f10k a i + 2 * ((4 * a + 9) + (2 * (4 * a + 9) - 2) * i) + 4 * i + 2 := by
  have e : 2 * (4 * a + 9) - 2 = 8 * a + 16 := by omega
  rw [e]
  unfold f10n f10k f10N
  refine ⟨by ring, by ring, by ring⟩

/-- **The Main Theorem is sharp on every line `l = 4c+1 ≥ 9`:**  `K(n,k) = 4k + 2l + 2` at `k = (l²-1)/2`. -/
theorem kmax_exact_l1 (c : ℕ) (hc : 2 ≤ c) :
    IsMaxLength (12 * c * c + 8 * c + 1) (8 * c * c + 4 * c) (4 * (8 * c * c + 4 * c) + 2 * (4 * c + 1) + 2) := by
  obtain ⟨a, rfl⟩ : ∃ a, c = a + 2 := ⟨c - 2, by omega⟩
  have h := K_family10 a 0
  rw [show f10n a 0 = 12 * (a + 2) * (a + 2) + 8 * (a + 2) + 1 by unfold f10n; ring,
    show f10k a 0 = 8 * (a + 2) * (a + 2) + 4 * (a + 2) by unfold f10k; ring,
    show f10N a 0 = 4 * (8 * (a + 2) * (a + 2) + 4 * (a + 2)) + 2 * (4 * (a + 2) + 1) + 2 by unfold f10N; ring] at h
  exact h

end Coil

#print axioms Coil.K_family10
#print axioms Coil.kmax_exact_l1
