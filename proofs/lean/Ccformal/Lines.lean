import Ccformal.Byrnes
import Ccformal.Fam10

/-!
# Exact values on whole lines (lower AND upper bound formal)

`l = 2n - 3k - 1`.  Beyond the proven `k_max` upper bounds Byrnes' sequence gives the matching code, so
`K(n,k) = 4k + 2l` there, on EVERY line (`exact_l0`, `exact_l1`, `exact_l2`, `exact_l3`); and for `l = 4c+1 ≥ 9` the
whole half-line `k ≥ (l²-1)/2` is known (`line_l1`): `K = 4k+2l+2` at `k = (l²-1)/2` (family 10), `4k+2l` above.
-/

namespace Coil

set_option linter.deprecated false

/-- `l = 4q ≥ 8`, `k` odd, `k > (l²-l-6)/2`:  `K(n,k) = 4k + 2l`. -/
theorem exact_l0 (q k n : ℕ) (hq : 2 ≤ q) (hko : Odd k) (hn : 2 * n = 3 * k + 4 * q + 1)
    (hk : 8 * q * q ≤ k + 2 * q + 1) : IsMaxLength n k (4 * k + 2 * (4 * q)) := by
  have h8 : 8 * q * 2 ≤ 8 * q * q := Nat.mul_le_mul_left _ hq
  exact ⟨byrnes_lower k (4 * q) n (by omega) (by omega) (by omega),
    fun N v h => kmax_upper_l0 q k n N hq v h hko hn hk⟩

/-- `l = 4c+3 ≥ 11`, `k` even, `k > (l²-l-6)/2`:  `K(n,k) = 4k + 2l`. -/
theorem exact_l3 (c k n : ℕ) (hc : 2 ≤ c) (hke : Even k) (hn : 2 * n = 3 * k + (4 * c + 3) + 1)
    (hk : 8 * c * c + 10 * c + 2 ≤ k) : IsMaxLength n k (4 * k + 2 * (4 * c + 3)) :=
  ⟨byrnes_lower k (4 * c + 3) n (by omega) (by omega) hn,
    fun N v h => kmax_upper_l3 c k n N hc v h hke hn hk⟩

/-- `l = 4c+2`, `k` odd, `k > (l²-l-4)/2`:  `K(n,k) = 4k + 2l`. -/
theorem exact_l2 (c k n : ℕ) (hko : Odd k) (hn : 2 * n = 3 * k + (4 * c + 2) + 1)
    (hk : 8 * c * c + 6 * c < k) : IsMaxLength n k (4 * k + 2 * (4 * c + 2)) :=
  ⟨byrnes_lower k (4 * c + 2) n (by omega) (by omega) hn,
    fun N v h => kmax_upper_l2 c k n N v h hko hn hk⟩

/-- `l = 4c+1 ≥ 5`, `k` even, `k > (l²-1)/2`, `k > 3l-3`:  `K(n,k) = 4k + 2l`. -/
theorem exact_l1 (c k n : ℕ) (hc : 1 ≤ c) (hke : Even k) (hn : 2 * n = 3 * k + (4 * c + 1) + 1)
    (hk : 8 * c * c + 4 * c < k) (hk3 : 3 * (4 * c + 1) < k + 3) : IsMaxLength n k (4 * k + 2 * (4 * c + 1)) :=
  ⟨byrnes_lower k (4 * c + 1) n (by omega) (by omega) hn,
    fun N v h => kmax_upper_l1 c k n N v h hc hke hn hk hk3⟩

/-- **A complete half-line for every `l = 4c+1 ≥ 9`:** for all even `k ≥ (l²-1)/2 = 8c²+4c`,
`K(n,k) = 4k+2l+2` if `k = (l²-1)/2` and `K(n,k) = 4k+2l` otherwise. -/
theorem line_l1 (c k n : ℕ) (hc : 2 ≤ c) (hke : Even k) (hn : 2 * n = 3 * k + (4 * c + 1) + 1)
    (hk : 8 * c * c + 4 * c ≤ k) :
    IsMaxLength n k (if k = 8 * c * c + 4 * c then 4 * k + 2 * (4 * c + 1) + 2 else 4 * k + 2 * (4 * c + 1)) := by
  split_ifs with h
  · subst h
    have e1 : 12 * c * c = 12 * (c * c) := by ring
    have e2 : 8 * c * c = 8 * (c * c) := by ring
    obtain rfl : n = 12 * c * c + 8 * c + 1 := by omega
    exact kmax_exact_l1 c hc
  · have h8 : 8 * c * 2 ≤ 8 * c * c := Nat.mul_le_mul_left _ hc
    exact exact_l1 c k n (by omega) hke hn (by omega) (by omega)

end Coil

#print axioms Coil.exact_l0
#print axioms Coil.exact_l3
#print axioms Coil.line_l1
