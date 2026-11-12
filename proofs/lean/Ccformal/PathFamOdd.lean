import Ccformal.PathFamOddStepA
import Ccformal.PathFamOddStepB
import Ccformal.PathFamOddStepC
import Ccformal.PathFamOddSign

/-!
# The odd family fam(k, m), m odd, is a spread-k path: `P(d,k) = 3k + 3l - 2` on odd lines `l`      (S178)

STATUS: everything in this file and in `PathFamOddDefs.lean`, `PathFamOddStepA/B/C.lean`, `PathFamOddSign.lean` is PROVED
(no `sorry`).

Hand proof: `PROOF_family_odd.md` (paths folder); python twin of the definitions (brute-force tested, all
hypotheses of `isPathWord_of_height`): not included; generated parts (scripts not included): Defs + step
lemmas, Sign.

Parameters: `K = 2κ + 1`, `m = 2h + 1`, `k = 2κ`, `K ≥ 2m - 1` (`2h ≤ κ`), `d = 3κ + h + 2`, `L = 6κ + 6h + 7`.
Word `z A z B C z D` with the letter numbering of `pfam.fam` (`famFo κ h hh : ℕ → Fin (3κ+h+2)`).

* `famOdd_isPathWord : 2h ≤ κ → k = 2κ → IsPathWord k (6κ+6h+7) (famFo κ h _)`
* `famOdd_path`       : a vertex path `ℕ → Fin (3κ+h+2) → Bool`
* `maxPath_odd_l`     : `3h + 3 ≤ κ` (k ≥ 3l − 3, l = 2h + 3):  `IsMaxPath (3κ+h+2) k (6κ+6h+7)`.
-/

namespace Coil

namespace FamOdd

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.style.longLine false
set_option linter.deprecated false

/-! ### glue between the blocks -/

lemma HBA_zero {K s : ℕ} (hs : s ≤ K) : HBA K s 0 = K + 1 - s := by
  unfold HBA; split_ifs <;> omega

set_option maxHeartbeats 1000000 in
lemma HCA_zero {K m s : ℕ} (hK : K % 2 = 1) (hm : m % 2 = 1) (hKm : 2 * m ≤ K + 1) (hs : s ≤ K) :
    HCA K m s 0 = HBA K s (K + 1) := by
  have f0 : (0 : ℕ) < m := by omega
  have f1 : ¬ (K + 1 ≤ s) := by omega
  simp only [HCA, HBA, f0, f1, ↓reduceIte, Nat.reduceMod, Nat.reduceAdd]
  split_ifs <;> first | omega | contradiction

set_option maxHeartbeats 1000000 in
lemma HDA_zero {K m s : ℕ} (hK : K % 2 = 1) (hm : m % 2 = 1) (hKm : 2 * m ≤ K + 1) (hs : s ≤ K) :
    HDA K m s 0 = HCA K m s (K + m) := by
  have f0 : ¬ (K + m < m) := by omega
  have f1 : ¬ (K + m + 2 < 3 * m) := by omega
  have f2 : ¬ (K + m < K + m) := by omega
  simp only [HDA, HCA, f0, f1, f2, ↓reduceIte, Nat.reduceMod, Nat.reduceDiv, Nat.reduceAdd, Nat.reduceMul]
  split_ifs <;> first | omega | contradiction

set_option maxHeartbeats 1000000 in
lemma HCB_zero {K m sp : ℕ} (hK : K % 2 = 1) (hm : m % 2 = 1) (hKm : 2 * m ≤ K + 1) (hsp : sp ≤ K) :
    HCB K m sp 0 = K + 1 - sp := by
  have f0 : (0 : ℕ) < m := by omega
  simp only [HCB, EC, f0, ↓reduceIte, Nat.reduceMod, Nat.reduceAdd]
  split_ifs <;> first | omega | contradiction

set_option maxHeartbeats 1000000 in
lemma HDB_zero {K m sp : ℕ} (hK : K % 2 = 1) (hm : m % 2 = 1) (hKm : 2 * m ≤ K + 1) (hsp : sp ≤ K) :
    HDB K m sp 0 = HCB K m sp (K + m) := by
  have f0 : ¬ (K + m < m) := by omega
  have f1 : ¬ (K + m + 2 < 3 * m) := by omega
  have f2 : ¬ (K + m < K + m) := by omega
  simp only [HDB, HCB, EC, f0, f1, f2, ↓reduceIte, Nat.reduceMod, Nat.reduceDiv, Nat.reduceAdd, Nat.reduceMul]
  split_ifs <;> first | omega | contradiction

set_option maxHeartbeats 1000000 in
lemma HDC_zero {K m u : ℕ} (hK : K % 2 = 1) (hm : m % 2 = 1) (hKm : 2 * m ≤ K + 1) (hu : u + 1 < K + m) :
    HDC K m u 0 = K + m - u := by
  simp only [HDC, Nat.reduceMod, Nat.reduceDiv, Nat.reduceAdd, Nat.reduceMul]
  split_ifs <;> first | omega | contradiction

/-! ### evaluation of `H` by blocks -/

variable {κ h : ℕ}

lemma H_AA {s p : ℕ} (hs : s ≤ 2 * κ + 1) (hp : p ≤ 2 * κ + 2) : H κ h s p = p - s := by
  unfold H; rw [if_pos hs, if_pos hp]

lemma H_AB {s p : ℕ} (hs : s ≤ 2 * κ + 1) (h1 : 2 * κ + 2 ≤ p) (h2 : p ≤ 4 * κ + 4) :
    H κ h s p = HBA (2 * κ + 1) s (p - (2 * κ + 2)) := by
  unfold H; rw [if_pos hs]
  by_cases hp : p ≤ 2 * κ + 2
  · obtain rfl : p = 2 * κ + 2 := by omega
    rw [if_pos hp, Nat.sub_self, HBA_zero hs]
  · rw [if_neg hp, if_pos h2]

lemma H_AC (hh : 2 * h ≤ κ) {s p : ℕ} (hs : s ≤ 2 * κ + 1) (h1 : 4 * κ + 4 ≤ p) (h2 : p ≤ 6 * κ + 2 * h + 6) :
    H κ h s p = HCA (2 * κ + 1) (2 * h + 1) s (p - (4 * κ + 4)) := by
  unfold H; rw [if_pos hs, if_neg (by omega)]
  by_cases hp : p ≤ 4 * κ + 4
  · obtain rfl : p = 4 * κ + 4 := by omega
    rw [if_pos hp, Nat.sub_self, HCA_zero (by omega) (by omega) (by omega) hs]
    congr 1; omega
  · rw [if_neg hp, if_pos h2]

lemma H_AD (hh : 2 * h ≤ κ) {s p : ℕ} (hs : s ≤ 2 * κ + 1) (h1 : 6 * κ + 2 * h + 6 ≤ p) :
    H κ h s p = HDA (2 * κ + 1) (2 * h + 1) s (p - (6 * κ + 2 * h + 6)) := by
  unfold H; rw [if_pos hs, if_neg (by omega), if_neg (by omega)]
  by_cases hp : p ≤ 6 * κ + 2 * h + 6
  · obtain rfl : p = 6 * κ + 2 * h + 6 := by omega
    rw [if_pos hp, Nat.sub_self, HDA_zero (by omega) (by omega) (by omega) hs]
    congr 1; omega
  · rw [if_neg hp]

lemma H_BB {s p : ℕ} (h1 : 2 * κ + 2 ≤ s) (hs : s ≤ 4 * κ + 3) (hp : p ≤ 4 * κ + 4) : H κ h s p = p - s := by
  unfold H; rw [if_neg (by omega), if_pos hs, if_pos hp]

lemma H_BC (hh : 2 * h ≤ κ) {s p : ℕ} (h0 : 2 * κ + 2 ≤ s) (hs : s ≤ 4 * κ + 3) (h1 : 4 * κ + 4 ≤ p)
    (h2 : p ≤ 6 * κ + 2 * h + 6) :
    H κ h s p = HCB (2 * κ + 1) (2 * h + 1) (s - (2 * κ + 2)) (p - (4 * κ + 4)) := by
  unfold H; rw [if_neg (by omega), if_pos hs]
  by_cases hp : p ≤ 4 * κ + 4
  · obtain rfl : p = 4 * κ + 4 := by omega
    rw [if_pos hp, Nat.sub_self, HCB_zero (by omega) (by omega) (by omega) (by omega)]
    omega
  · rw [if_neg hp, if_pos h2]

lemma H_BD (hh : 2 * h ≤ κ) {s p : ℕ} (h0 : 2 * κ + 2 ≤ s) (hs : s ≤ 4 * κ + 3) (h1 : 6 * κ + 2 * h + 6 ≤ p) :
    H κ h s p = HDB (2 * κ + 1) (2 * h + 1) (s - (2 * κ + 2)) (p - (6 * κ + 2 * h + 6)) := by
  unfold H; rw [if_neg (by omega), if_pos hs, if_neg (by omega)]
  by_cases hp : p ≤ 6 * κ + 2 * h + 6
  · obtain rfl : p = 6 * κ + 2 * h + 6 := by omega
    rw [if_pos hp, Nat.sub_self, HDB_zero (by omega) (by omega) (by omega) (by omega)]
    congr 1; omega
  · rw [if_neg hp]

lemma H_CC {s p : ℕ} (h1 : 4 * κ + 4 ≤ s) (hs : s ≤ 6 * κ + 2 * h + 4) (hp : p ≤ 6 * κ + 2 * h + 6) :
    H κ h s p = p - s := by
  unfold H; rw [if_neg (by omega), if_neg (by omega), if_pos hs, if_pos hp]

lemma H_CD (hh : 2 * h ≤ κ) {s p : ℕ} (h0 : 4 * κ + 4 ≤ s) (hs : s ≤ 6 * κ + 2 * h + 4)
    (h1 : 6 * κ + 2 * h + 6 ≤ p) :
    H κ h s p = HDC (2 * κ + 1) (2 * h + 1) (s - (4 * κ + 4)) (p - (6 * κ + 2 * h + 6)) := by
  unfold H; rw [if_neg (by omega), if_neg (by omega), if_pos hs]
  by_cases hp : p ≤ 6 * κ + 2 * h + 6
  · obtain rfl : p = 6 * κ + 2 * h + 6 := by omega
    rw [if_pos hp, Nat.sub_self, HDC_zero (by omega) (by omega) (by omega) (by omega)]
    omega
  · rw [if_neg hp]

lemma H_DD {s p : ℕ} (h1 : 6 * κ + 2 * h + 5 ≤ s) : H κ h s p = p - s := by
  unfold H; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-! ### the step lemma for `H` -/

theorem fam_step (hh : 2 * h ≤ κ) (s j : ℕ) (hsj : s ≤ j) (hj : j < 6 * κ + 6 * h + 7) :
    (¬ dn κ h s j → H κ h s (j + 1) = H κ h s j + 1)
      ∧ (dn κ h s j → 2 * κ + 1 ≤ H κ h s j ∧ H κ h s (j + 1) + 1 = H κ h s j) := by
  have hK : (2 * κ + 1) % 2 = 1 := by omega
  have hm : (2 * h + 1) % 2 = 1 := by omega
  have hKm : 2 * (2 * h + 1) ≤ 2 * κ + 1 + 1 := by omega
  rcases Nat.lt_or_ge s (2 * κ + 2) with hs1 | hs1
  · -- s in z A
    have hs1' : s ≤ 2 * κ + 1 := by omega
    rcases Nat.lt_or_ge j (2 * κ + 2) with hj1 | hj1
    · rw [H_AA hs1' (by omega), H_AA hs1' (by omega)]
      exact ⟨fun _ => by omega, fun hd => absurd hd (dn_A hj1)⟩
    rcases Nat.lt_or_ge j (4 * κ + 4) with hj2 | hj2
    · rw [H_AB hs1' (by omega) (by omega), H_AB hs1' hj1 (by omega), dn_B hj1 hj2,
        show j + 1 - (2 * κ + 2) = (j - (2 * κ + 2)) + 1 by omega]
      exact stepBA hK hs1' (by omega)
    rcases Nat.lt_or_ge j (6 * κ + 2 * h + 6) with hj3 | hj3
    · rw [H_AC hh hs1' (by omega) (by omega), H_AC hh hs1' hj2 (by omega), dn_C hj2 hj3,
        show j + 1 - (4 * κ + 4) = (j - (4 * κ + 4)) + 1 by omega]
      exact stepCA hK hm hKm hs1' (by omega)
    · rw [H_AD hh hs1' (by omega), H_AD hh hs1' hj3, dn_D hj3,
        show j + 1 - (6 * κ + 2 * h + 6) = (j - (6 * κ + 2 * h + 6)) + 1 by omega]
      exact stepDA hK hm hKm hs1' (by omega)
  rcases Nat.lt_or_ge s (4 * κ + 4) with hs2 | hs2
  · -- s in z' B
    have hs2' : s ≤ 4 * κ + 3 := by omega
    have es : s = 2 * κ + 1 + 1 + (s - (2 * κ + 2)) := by omega
    rcases Nat.lt_or_ge j (4 * κ + 4) with hj2 | hj2
    · rw [H_BB hs1 hs2' (by omega), H_BB hs1 hs2' (by omega)]
      refine ⟨fun _ => by omega, fun hd => ?_⟩
      exfalso
      rw [dn_B (by omega) hj2] at hd
      unfold dnB at hd
      split_ifs at hd <;> omega
    rcases Nat.lt_or_ge j (6 * κ + 2 * h + 6) with hj3 | hj3
    · rw [H_BC hh hs1 hs2' (by omega) (by omega), H_BC hh hs1 hs2' hj2 (by omega), dn_C hj2 hj3,
        show j + 1 - (4 * κ + 4) = (j - (4 * κ + 4)) + 1 by omega]
      have := stepCB (sp := s - (2 * κ + 2)) (y := j - (4 * κ + 4)) hK hm hKm (by omega) (by omega)
      rw [← es] at this
      exact this
    · rw [H_BD hh hs1 hs2' (by omega), H_BD hh hs1 hs2' hj3, dn_D hj3,
        show j + 1 - (6 * κ + 2 * h + 6) = (j - (6 * κ + 2 * h + 6)) + 1 by omega]
      have := stepDB (sp := s - (2 * κ + 2)) (w := j - (6 * κ + 2 * h + 6)) hK hm hKm (by omega) (by omega)
      rw [← es] at this
      exact this
  rcases Nat.lt_or_ge s (6 * κ + 2 * h + 5) with hs3 | hs3
  · -- s in C
    have hs3' : s ≤ 6 * κ + 2 * h + 4 := by omega
    have es : s = 2 * (2 * κ + 1) + 2 + (s - (4 * κ + 4)) := by omega
    rcases Nat.lt_or_ge j (6 * κ + 2 * h + 6) with hj3 | hj3
    · rw [H_CC hs2 hs3' (by omega), H_CC hs2 hs3' (by omega)]
      refine ⟨fun _ => by omega, fun hd => ?_⟩
      exfalso
      rw [dn_C (by omega) hj3] at hd
      unfold dnC at hd
      split_ifs at hd <;> omega
    · rw [H_CD hh hs2 hs3' (by omega), H_CD hh hs2 hs3' hj3, dn_D hj3,
        show j + 1 - (6 * κ + 2 * h + 6) = (j - (6 * κ + 2 * h + 6)) + 1 by omega]
      have := stepDC (u := s - (4 * κ + 4)) (w := j - (6 * κ + 2 * h + 6)) hK hm hKm (by omega) (by omega)
      rw [← es] at this
      exact this
  · -- s in z'' D
    rw [H_DD hs3, H_DD hs3]
    refine ⟨fun _ => by omega, fun hd => ?_⟩
    exfalso
    rcases Nat.lt_or_ge j (6 * κ + 2 * h + 6) with hj3 | hj3
    · rw [dn_C (by omega) hj3] at hd
      unfold dnC at hd
      split_ifs at hd <;> omega
    · rw [dn_D hj3] at hd
      unfold dnD at hd
      split_ifs at hd <;> omega

lemma fam_h0 (s : ℕ) : H κ h s s = 0 := by
  unfold H; split_ifs <;> omega

end FamOdd

set_option linter.deprecated false

/-- the word of the odd family, letters in `Fin (3κ + h + 2)` -/
abbrev famFo (κ h : ℕ) (hh : 2 * h ≤ κ) : ℕ → Fin (3 * κ + h + 2) := FamOdd.famF κ h hh

/-- **The odd family is a spread-`k` path word** of length `3K + 3m + 1` over `(3K + m)/2` letters. -/
theorem famOdd_isPathWord {κ h : ℕ} (hh : 2 * h ≤ κ) {k : ℕ} (hk : k = 2 * κ) :
    IsPathWord k (6 * κ + 6 * h + 7) (famFo κ h hh) :=
  isPathWord_of_height (FamOdd.H κ h) (FamOdd.dn κ h) (fun s w hw => FamOdd.fam_hdn hh s w hw)
    (fun s _ => FamOdd.fam_h0 s)
    (fun s j hsj hj hd => (FamOdd.fam_step hh s j hsj hj).1 hd)
    (fun s j hsj hj hd => by
      have := (FamOdd.fam_step hh s j hsj hj).2 hd
      exact ⟨by omega, this.2⟩)

theorem famOdd_path {κ h : ℕ} (hh : 2 * h ≤ κ) {k : ℕ} (hk : k = 2 * κ) :
    ∃ v : ℕ → Fin (3 * κ + h + 2) → Bool, IsPath k (6 * κ + 6 * h + 7) v :=
  (famOdd_isPathWord hh hk).exists_path

/-- **`P(d,k) = 3k + 3l - 2`** for even `k`, odd `l = 2h + 3`, `2d = 3k + l + 1`, `k ≥ 3l - 3`. -/
theorem maxPath_odd_l {κ h : ℕ} (hκ : 3 * h + 3 ≤ κ) {k : ℕ} (hk : k = 2 * κ) :
    IsMaxPath (3 * κ + h + 2) k (6 * κ + 6 * h + 7) := by
  refine ⟨famOdd_path (by omega) hk, fun L' v' h' => ?_⟩
  have heven : Even k := ⟨κ, by omega⟩
  have := path_length_bound h' (by omega) (2 * h + 3) (by simp only [Fintype.card_fin]; omega) (by omega)
    (by rw [if_pos heven]; omega)
  omega

end Coil

#print axioms Coil.famOdd_isPathWord
#print axioms Coil.maxPath_odd_l
