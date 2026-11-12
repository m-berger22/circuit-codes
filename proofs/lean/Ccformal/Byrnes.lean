import Ccformal.CountP

/-!
# Byrnes' circuit codes of length `4k + 2l` (lower bound), and exact values beyond `k_max`

Transition sequence of K. Byrnes, arXiv 2008.04839, eq. (8) (half period `H = 2k + l`, the code is `(ω1 ω2A ω2B)²`):

    ω1 = 1, 2, …, k+l        ω2A = 2, 4, …, 2(l-1)        ω2B = γ_1, 2l, γ_2, 2l+2, …, γ_m, k+l-1     (γ_i new, m = (k-l+1)/2).

Here: `l = lam + 2`, `k = lam + 1 + 2m` (any `lam, m ≥ 0`, i.e. ALL `l ≥ 2`, `k ≥ l - 1` of opposite parity -- more than the
range `k ≥ 2l+1 / 2l-2` of Byrnes' theorem), `a = k + l`, `K = k + 1`, `w = a + l - 1`, positions `0 … H-1`:

    gap function `gB`:  ω1 even position: H (dot);  ω1 odd position r ≤ 2l-3: a - (r+1)/2;  ω1 odd r ≥ 2l-1: K;
                        ω2A position a + j: K + j;   ω2B: γ: H (dot),  even number: a - 1.

Proof of validity by the gap criterion; the count (`countB`) by three injections (PROOF17.md).
Consequence (`K_beyond`): **`K(n,k) = 4k + 2l` whenever the Main Theorem applies** -- lower and upper bound formal.
-/

open Finset

namespace Coil

namespace Byr

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedVariables false

def gB (lam a K w H x : ℕ) : ℕ :=
  if x % H < a then
    (if x % H % 2 = 0 then H else if x % H ≤ 2 * lam + 1 then a - (x % H + 1) / 2 else K)
  else if x % H < w then K + (x % H - a)
  else if (x % H - w) % 2 = 0 then H else a - 1

def labB (lam a K w H x : ℕ) : ℕ :=
  if x % H < a then x % H
  else if x % H < w then 2 * (x % H - a) + 1
  else if (x % H - w) % 2 = 0 then x % H else 2 * lam + 2 + (x % H - w)

structure BPar (lam m a K w H : ℕ) : Prop where
  hH : H = 3 * lam + 4 + 4 * m
  ha : a = 2 * lam + 3 + 2 * m
  hK : K = lam + 2 + 2 * m
  hw : w = 3 * lam + 4 + 2 * m

variable {lam m a K w H : ℕ} (P : BPar lam m a K w H)

lemma gB_per (x : ℕ) : gB lam a K w H (x + H) = gB lam a K w H x := by
  unfold gB; rw [Nat.add_mod_right]

include P

/-- the six classes of positions (stated without natural subtraction) -/
lemma gB_cases (x : ℕ) :
    x % H < H ∧
    ((x % H < a ∧ x % H % 2 = 0 ∧ gB lam a K w H x = H ∧ labB lam a K w H x = x % H) ∨
     (x % H ≤ 2 * lam + 1 ∧ x % H % 2 = 1 ∧ 2 * gB lam a K w H x + x % H + 1 = 2 * a ∧
        labB lam a K w H x = x % H) ∨
     (2 * lam + 3 ≤ x % H ∧ x % H < a ∧ x % H % 2 = 1 ∧ gB lam a K w H x = K ∧ labB lam a K w H x = x % H) ∨
     (a ≤ x % H ∧ x % H < w ∧ gB lam a K w H x + a = K + x % H ∧ labB lam a K w H x + 2 * a = 2 * (x % H) + 1) ∨
     (w ≤ x % H ∧ (x % H + w) % 2 = 0 ∧ gB lam a K w H x = H ∧ labB lam a K w H x = x % H) ∨
     (w ≤ x % H ∧ (x % H + w) % 2 = 1 ∧ gB lam a K w H x + 1 = a ∧ labB lam a K w H x + w = 2 * lam + 2 + x % H)) := by
  obtain ⟨hH, ha, hK, hw⟩ := P
  have hlt : x % H < H := Nat.mod_lt _ (by omega)
  refine ⟨hlt, ?_⟩
  by_cases h1 : x % H < a
  · have el : labB lam a K w H x = x % H := by unfold labB; rw [if_pos h1]
    by_cases h2 : x % H % 2 = 0
    · left
      exact ⟨h1, h2, by unfold gB; rw [if_pos h1, if_pos h2], el⟩
    · by_cases h3 : x % H ≤ 2 * lam + 1
      · right; left
        have eg : gB lam a K w H x = a - (x % H + 1) / 2 := by unfold gB; rw [if_pos h1, if_neg h2, if_pos h3]
        exact ⟨h3, by omega, by omega, el⟩
      · right; right; left
        have eg : gB lam a K w H x = K := by unfold gB; rw [if_pos h1, if_neg h2, if_neg h3]
        exact ⟨by omega, h1, by omega, eg, el⟩
  · by_cases h4 : x % H < w
    · right; right; right; left
      have eg : gB lam a K w H x = K + (x % H - a) := by unfold gB; rw [if_neg h1, if_pos h4]
      have el : labB lam a K w H x = 2 * (x % H - a) + 1 := by unfold labB; rw [if_neg h1, if_pos h4]
      exact ⟨by omega, h4, by omega, by omega⟩
    · by_cases h5 : (x % H - w) % 2 = 0
      · right; right; right; right; left
        have eg : gB lam a K w H x = H := by unfold gB; rw [if_neg h1, if_neg h4, if_pos h5]
        have el : labB lam a K w H x = x % H := by unfold labB; rw [if_neg h1, if_neg h4, if_pos h5]
        exact ⟨by omega, by omega, eg, el⟩
      · right; right; right; right; right
        have eg : gB lam a K w H x = a - 1 := by unfold gB; rw [if_neg h1, if_neg h4, if_neg h5]
        have el : labB lam a K w H x = 2 * lam + 2 + (x % H - w) := by
          unfold labB; rw [if_neg h1, if_neg h4, if_neg h5]
        exact ⟨by omega, by omega, by omega, by omega⟩

lemma gB_ge (x : ℕ) : K ≤ gB lam a K w H x ∧ gB lam a K w H x ≤ H := by
  have h := gB_cases P x
  obtain ⟨hH, ha, hK, hw⟩ := P
  omega

/-- (G1) and the two-gap sums -/
lemma gB_succ (x : ℕ) :
    labB lam a K w H (x + gB lam a K w H x) = labB lam a K w H x ∧
    (gB lam a K w H x + gB lam a K w H (x + gB lam a K w H x) = H ∨
      (gB lam a K w H x = H ∧ gB lam a K w H (x + gB lam a K w H x) = H)) := by
  have h1 := gB_cases P x
  have h2 := gB_cases P (x + gB lam a K w H x)
  have hg := gB_ge P x
  have hr := res_add H x (gB lam a K w H x) (by have := P.hH; omega) hg.2
  obtain ⟨hH, ha, hK, hw⟩ := P
  omega

/-- (G2) -/
lemma labB_gap (x d : ℕ) (hd0 : 0 < d) (hd : d < gB lam a K w H x) :
    labB lam a K w H (x + d) ≠ labB lam a K w H x := by
  intro hl
  have h1 := gB_cases P x
  have h2 := gB_cases P (x + d)
  have hg := gB_ge P x
  have hr := res_add H x d (by have := P.hH; omega) (by omega)
  obtain ⟨hH, ha, hK, hw⟩ := P
  omega

/-- (G4), (G5) -/
lemma orbitB (x : ℕ) :
    (2 * H ≤ 2 * (gB lam a K w H x + gB lam a K w H (x + gB lam a K w H x)
      + gB lam a K w H (x + gB lam a K w H x + gB lam a K w H (x + gB lam a K w H x)))) ∧
    (gB lam a K w H x + (gB lam a K w H (x + gB lam a K w H x) + 0) = 2 * H ∨
      gB lam a K w H x + (gB lam a K w H (x + gB lam a K w H x) +
        (gB lam a K w H (x + gB lam a K w H x + gB lam a K w H (x + gB lam a K w H x)) +
        (gB lam a K w H (x + gB lam a K w H x + gB lam a K w H (x + gB lam a K w H x)
          + gB lam a K w H (x + gB lam a K w H x + gB lam a K w H (x + gB lam a K w H x))) + 0))) = 2 * H) := by
  rcases (gB_succ P x).2 with h | ⟨h1, h2⟩
  · have e : x + gB lam a K w H x + gB lam a K w H (x + gB lam a K w H x) = x + H := by omega
    rw [e, gB_per, show x + H + gB lam a K w H x = x + gB lam a K w H x + H by omega, gB_per]
    omega
  · omega

/-! ### the count -/

def Wb (lam a K w H t L m' : ℕ) : Prop :=
  gB lam a K w H (t + m') ≤ L - 1 - m' ∧
    L - 1 - m' < gB lam a K w H (t + m') + gB lam a K w H (t + m' + gB lam a K w H (t + m'))

instance (t L : ℕ) : DecidablePred (Wb lam a K w H t L) := by
  intro m'; unfold Wb; infer_instance

/-- a counted start position: its residue `ρ` (in terms of `s = t mod H`) and its class -/
lemma Wb_facts {t y m' : ℕ} (hy : y + K ≤ H) (hm : m' < y + K) (h : Wb lam a K w H t (y + K) m') :
    ∃ ρ, (ρ = t % H + m' ∨ ρ + H = t % H + m') ∧ ρ < H ∧ ρ = (t + m') % H ∧
      ((ρ ≤ 2 * lam + 1 ∧ ρ % 2 = 1 ∧ 2 * m' + 2 * lam + 2 < 2 * y + ρ + 1) ∨
       (2 * lam + 3 ≤ ρ ∧ ρ < a ∧ ρ % 2 = 1 ∧ m' < y) ∨
       (a ≤ ρ ∧ ρ < w ∧ ρ + m' < y + a) ∨
       (w ≤ ρ ∧ (ρ + w) % 2 = 1 ∧ m' + lam < y)) := by
  obtain ⟨hlt, h1⟩ := gB_cases P (t + m')
  have hr := res_add H t m' (by have := P.hH; omega) (by omega)
  have h0 : gB lam a K w H (t + m') + m' + 1 ≤ y + K := by
    have := h.1
    omega
  obtain ⟨hH, ha, hK, hw⟩ := P
  refine ⟨(t + m') % H, by omega, hlt, rfl, ?_⟩
  rcases h1 with c | c | c | c | c | c
  · omega
  · left; omega
  · right; left; omega
  · right; right; left; omega
  · omega
  · right; right; right; omega

abbrev AB (a w H x : ℕ) : Prop := (x % H < a ∧ x % H % 2 = 1) ∨ (w ≤ x % H ∧ (x % H + w) % 2 = 1)

lemma AB_adj : ∀ x, ¬(AB a w H x ∧ AB a w H (x + 1)) := by
  intro x ⟨h1, h2⟩
  have hr := res_add H x 1 (by have := P.hH; omega) (by have := P.hH; omega)
  obtain ⟨hH, ha, hK, hw⟩ := P
  unfold AB at h1 h2
  omega

set_option maxHeartbeats 4000000 in
/-- **the count for Byrnes' sequence** -/
theorem countB (t y : ℕ) (hy : y + K ≤ H) :
    2 * #{m' ∈ range (y + K) | Wb lam a K w H t (y + K) m'} ≤ y + 1 := by
  have hPH := P.hH
  have hPa := P.ha
  have hPK := P.hK
  have hPw := P.hw
  have hs : t % H < H := Nat.mod_lt _ (by omega)
  by_cases hT : w ≤ t % H ∨ t % H + y ≤ a
  · -- no position of the run ω2A is counted
    have hsub : #{m' ∈ range (y + K) | Wb lam a K w H t (y + K) m'} ≤ cP (AB a w H) t y := by
      apply card_le_card
      intro m' hm
      simp only [mem_filter, mem_range] at hm ⊢
      obtain ⟨ρ, hρ, hlt, hρe, hc⟩ := Wb_facts P hy hm.1 hm.2
      unfold AB
      rw [← hρe]
      omega
    have := cP_le_half (AB_adj P) t y
    omega
  · by_cases hα : t % H ≤ a
    · -- the window starts in ω1 and reaches the run
      have hle : #{m' ∈ range (y + K) | Wb lam a K w H t (y + K) m'} ≤ #(range ((y + 1) / 2)) := by
        apply card_le_card_of_injOn (fun m' => if t % H + m' < a then m' / 2
          else if t % H + m' < w then (2 * m' + t % H - a) / 2 else (m' + lam) / 2)
        · intro m' hm
          simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hm
          obtain ⟨ρ, hρ, hlt, hρe, hc⟩ := Wb_facts P hy hm.1 hm.2
          simp only [coe_range, Set.mem_Iio]
          split_ifs <;> omega
        · intro m1 hm1 m2 hm2 heq
          simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hm1 hm2
          obtain ⟨ρ1, hρ1, hlt1, hρe1, hc1⟩ := Wb_facts P hy hm1.1 hm1.2
          obtain ⟨ρ2, hρ2, hlt2, hρe2, hc2⟩ := Wb_facts P hy hm2.1 hm2.2
          simp only at heq
          split_ifs at heq <;> omega
      rw [card_range] at hle
      omega
    · -- the window starts inside the run
      have hle : #{m' ∈ range (y + K) | Wb lam a K w H t (y + K) m'} ≤ #(range ((y + 1) / 2)) := by
        apply card_le_card_of_injOn (fun m' => if t % H + m' < w then m'
          else if t % H + m' < H then (m' + lam + a - t % H) / 2
          else (H + lam + 1 + a - 2 * (t % H)) / 2 + (t % H + m' - H - 1) / 2)
        · intro m' hm
          simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hm
          obtain ⟨ρ, hρ, hlt, hρe, hc⟩ := Wb_facts P hy hm.1 hm.2
          simp only [coe_range, Set.mem_Iio]
          split_ifs <;> omega
        · intro m1 hm1 m2 hm2 heq
          simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hm1 hm2
          obtain ⟨ρ1, hρ1, hlt1, hρe1, hc1⟩ := Wb_facts P hy hm1.1 hm1.2
          obtain ⟨ρ2, hρ2, hlt2, hρe2, hc2⟩ := Wb_facts P hy hm2.1 hm2.2
          simp only at heq
          split_ifs at heq <;> omega
      rw [card_range] at hle
      omega

/-! ### the labels -/

lemma labB_mem (x : ℕ) : labB lam a K w H x ∈ range a ∪ image (fun q => w + 2 * q) (range m) := by
  obtain ⟨hlt, h⟩ := gB_cases P x
  obtain ⟨hH, ha, hK, hw⟩ := P
  rcases h with c | c | c | c | c | c
  · apply mem_union_left; rw [mem_range]; omega
  · apply mem_union_left; rw [mem_range]; omega
  · apply mem_union_left; rw [mem_range]; omega
  · apply mem_union_left; rw [mem_range]; omega
  · apply mem_union_right
    rw [mem_image]
    refine ⟨(x % H - w) / 2, by rw [mem_range]; omega, ?_⟩
    show w + 2 * ((x % H - w) / 2) = labB lam a K w H x
    omega
  · apply mem_union_left; rw [mem_range]; omega

/-- **Byrnes' word**: a coil word which is symmetric (`T (i + H) = T i`, `H = N/2`) and starts with a bit run of
length `a = k + l` -/
theorem word_exists (n : ℕ) (hn : a + m ≤ n) : ∃ T : ℕ → Fin n, IsCoilWord (K - 1) (2 * H) T ∧
    (∀ i, T (i + H) = T i) ∧ (∀ i j, i < a → j < a → T i = T j → i = j) := by
  have hPH := P.hH
  have hPa := P.ha
  have hPK := P.hK
  have hPw := P.hw
  have hcard : (range a ∪ image (fun q => w + 2 * q) (range m)).card ≤ n := by
    refine (card_union_le _ _).trans ?_
    have := card_image_le (s := range m) (f := fun q => w + 2 * q)
    rw [card_range] at this ⊢
    omega
  let S := range a ∪ image (fun q => w + 2 * q) (range m)
  let T : ℕ → Fin n := fun x => Fin.castLE hcard (S.equivFin ⟨labB lam a K w H x, labB_mem P x⟩)
  have hT1 : ∀ x y, T x = T y → labB lam a K w H x = labB lam a K w H y := by
    intro x y h
    have h1 := Fin.castLE_injective hcard h
    have h2 := S.equivFin.injective h1
    exact congrArg Subtype.val h2
  have hT2 : ∀ x y, labB lam a K w H x = labB lam a K w H y → T x = T y := by
    intro x y h
    have : (⟨labB lam a K w H x, labB_mem P x⟩ : S) = ⟨labB lam a K w H y, labB_mem P y⟩ := Subtype.ext h
    show Fin.castLE hcard (S.equivFin ⟨labB lam a K w H x, labB_mem P x⟩)
      = Fin.castLE hcard (S.equivFin ⟨labB lam a K w H y, labB_mem P y⟩)
    rw [this]
  refine ⟨T, isCoilWord_of_gaps (gB lam a K w H) (fun x => hT2 _ _ (gB_succ P x).1)
    (fun x d h0 hd h => labB_gap P x d h0 hd (hT1 _ _ h)) (by omega) ?_ (fun x => (orbitB P x).1)
    (fun x => (orbitB P x).2) ?_, ?_, ?_⟩
  · intro x
    have := gB_ge P x
    omega
  · intro t L h1 h2
    obtain ⟨y, rfl⟩ : ∃ y, L = y + K := ⟨L - K, by omega⟩
    have := countB P t y (by omega)
    unfold Wb at this
    omega
  · intro i
    apply hT2
    unfold labB
    rw [Nat.add_mod_right]
  · intro i j hi hj h
    have hl := hT1 _ _ h
    have ei : labB lam a K w H i = i := by
      unfold labB; rw [Nat.mod_eq_of_lt (by omega : i < H), if_pos hi]
    have ej : labB lam a K w H j = j := by
      unfold labB; rw [Nat.mod_eq_of_lt (by omega : j < H), if_pos hj]
    omega

end Byr

/-- **Byrnes' codes, for all `l ≥ 2`, `k ≥ l - 1` of opposite parity:** a transition word of a spread-`k` circuit code of
length `4k + 2l` in the `n`-cube (`2n = 3k + l + 1`) which is SYMMETRIC (`T (i + N/2) = T i`) and has a BIT RUN of length
`k + l` (the first `k+l` transitions are distinct) -- i.e. `S(n, k, k+l) ≥ 4k + 2l` in Byrnes' notation. -/
theorem byrnes_word (k l n : ℕ) (hl : 2 ≤ l) (hkl : l ≤ k + 1) (hn : 2 * n = 3 * k + l + 1) :
    ∃ T : ℕ → Fin n, IsCoilWord k (4 * k + 2 * l) T ∧ (∀ i, T (i + (2 * k + l)) = T i) ∧
      (∀ i j, i < k + l → j < k + l → T i = T j → i = j) := by
  obtain ⟨lam, rfl⟩ : ∃ lam, l = lam + 2 := ⟨l - 2, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, k = lam + 1 + 2 * m := ⟨(k - lam - 1) / 2, by omega⟩
  have P : Byr.BPar lam m (2 * lam + 3 + 2 * m) (lam + 2 + 2 * m) (3 * lam + 4 + 2 * m) (3 * lam + 4 + 4 * m) :=
    ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨T, hT, hsym, hrun⟩ := Byr.word_exists P n (by omega)
  rw [show lam + 2 + 2 * m - 1 = lam + 1 + 2 * m by omega,
    show 2 * (3 * lam + 4 + 4 * m) = 4 * (lam + 1 + 2 * m) + 2 * (lam + 2) by omega] at hT
  refine ⟨T, hT, ?_, ?_⟩
  · intro i
    rw [show 2 * (lam + 1 + 2 * m) + (lam + 2) = 3 * lam + 4 + 4 * m by omega]
    exact hsym i
  · intro i j hi hj
    exact hrun i j (by omega) (by omega)

/-- **Byrnes' lower bound, for all `l ≥ 2`, `k ≥ l - 1` of opposite parity:** a spread-`k` circuit code of length
`4k + 2l` in the `n`-cube, `2n = 3k + l + 1`. -/
theorem byrnes_lower (k l n : ℕ) (hl : 2 ≤ l) (hkl : l ≤ k + 1) (hn : 2 * n = 3 * k + l + 1) :
    ∃ v : ℕ → Fin n → Bool, IsCoil k (4 * k + 2 * l) v := by
  obtain ⟨T, hT, _⟩ := byrnes_word k l n hl hkl hn
  exact hT.exists_coil

/-- **Exact values beyond `k_max`:  `K(n,k) = 4k + 2l` whenever the Main Theorem applies**
(`l = 2n - 3k - 1 ≥ 2`; `k` even: `2k > l² - 1` and `k > 3l - 3`; `k` odd: `2k > (l-2)(l+1)`).
Lower bound: Byrnes' sequence (`byrnes_lower`); upper bound: `coil_length_bound`. -/
theorem K_beyond (k l n : ℕ) (hk : 1 ≤ k) (hl : 2 ≤ l) (hn : 2 * n = 3 * k + l + 1)
    (hyp : if Even k then (l * l < 2 * k + 1 ∧ 3 * l < k + 3) else l * l < 2 * k + l + 2) :
    IsMaxLength n k (4 * k + 2 * l) := by
  have hkl : l ≤ k + 1 := by
    split_ifs at hyp with he
    · omega
    · by_contra hc
      have : k + 2 ≤ l := by omega
      nlinarith
  refine ⟨byrnes_lower k l n hl hkl hn, fun N' v' h' => ?_⟩
  exact coil_length_bound h' hk l hl (by rw [Fintype.card_fin]; exact hn) hyp

/-- **Conjecture 4.2 of Byrnes (arXiv 2008.04839), `S(n,k,k+l) = K(n,k)`, in the region of the Main Theorem:**
`4k + 2l` is the maximum length of a spread-`k` circuit code in `Q_n`, AND it is attained by a symmetric code with a bit
run of length `k + l`. -/
theorem conj42_region (k l n : ℕ) (hk : 1 ≤ k) (hl : 2 ≤ l) (hn : 2 * n = 3 * k + l + 1)
    (hyp : if Even k then (l * l < 2 * k + 1 ∧ 3 * l < k + 3) else l * l < 2 * k + l + 2) :
    IsMaxLength n k (4 * k + 2 * l) ∧
    ∃ T : ℕ → Fin n, IsCoilWord k (4 * k + 2 * l) T ∧ (∀ i, T (i + (2 * k + l)) = T i) ∧
      (∀ i j, i < k + l → j < k + l → T i = T j → i = j) := by
  refine ⟨K_beyond k l n hk hl hn hyp, ?_⟩
  have hkl : l ≤ k + 1 := by
    split_ifs at hyp with he
    · omega
    · by_contra hc
      have : k + 2 ≤ l := by omega
      nlinarith
  exact byrnes_word k l n hl hkl hn

end Coil

#print axioms Coil.byrnes_lower
#print axioms Coil.K_beyond
#print axioms Coil.conj42_region
