import Ccformal.Structure

/-!
# Reduction of Theorem 8 / 9 to a statement about the type word (PROOF2.md sec. 8: (U1), (U2))

Odd line (`l` odd, `k` even), excess 2: `N = 4k + 2l + 2 = 4K + 2l - 2`, `2n = 3k + l + 1`, and (H), which here reads
`l² + 2l + 3 < 6K`.  For a code of this length the F/dot word `φ` (`φ t` = "position `t` carries a coordinate used four
times") satisfies `TypeWord K l N φ`:
* period `N`, and exactly `2K + 2l` F positions per period;
* (U1) a window of length `L`, `k ≤ L ≤ 2K`:  `2 F(W) ≤ L + l` (`L` odd), `≤ L + l + 1` (`L` even);
* (U2) a window of length `2K+1`: `2 F(W) ≤ 2K + l + 3`, and equality forces `φ (t + K)`.
Theorem 8 (and 9) then say: no such word exists for certain `(K, l)`.  That part is NOT formalized yet.
-/

open Finset

namespace Coil

set_option linter.unusedSectionVars false
set_option linter.deprecated false

/-- number of positions `t ≤ i < t + L` with `φ i` -/
def Fw (φ : ℕ → Prop) [DecidablePred φ] (t L : ℕ) : ℕ := #{i ∈ range L | φ (t + i)}

/-- the word-level conditions (U1), (U2) for an excess-2 code on an odd line -/
structure TypeWord (K l N : ℕ) (φ : ℕ → Prop) [DecidablePred φ] : Prop where
  per : ∀ t, φ (t + N) ↔ φ t
  total : ∀ t, Fw φ t N = 2 * K + 2 * l
  u1 : ∀ t L, K ≤ L + 1 → L ≤ 2 * K → 2 * Fw φ t L + L % 2 ≤ L + l + 1
  u2 : ∀ t, 2 * Fw φ t (2 * K + 1) ≤ 2 * K + l + 3 ∧
    (2 * Fw φ t (2 * K + 1) = 2 * K + l + 3 → φ (t + K))

variable {α : Type*} [Fintype α] [DecidableEq α] {k N : ℕ} {T : ℕ → α}

lemma exists_of_one_le_cnt {t L : ℕ} {c : α} (h1 : 1 ≤ cnt T t L c) : ∃ i < L, T (t + i) = c := by
  rw [cnt] at h1
  obtain ⟨i, hi⟩ := card_pos.mp h1
  simp only [mem_filter, mem_range] at hi
  exact ⟨i, hi.1, hi.2⟩

theorem typeWord_of_coil (h : IsCoilWord k N T) (hk : 2 ≤ k) (hke : Even k) (l : ℕ)
    (hNl : N + 2 = 4 * (k + 1) + 2 * l) (hn : 2 * Fintype.card α = 3 * k + l + 1)
    (hH : l * l + 2 * l + 3 < 6 * (k + 1)) (hlk : 2 * l + 2 ≤ k) :
    TypeWord (k + 1) l N (fun t => cnt T 0 N (T t) = 4) := by
  obtain ⟨r, hr⟩ := hke
  have hk1 : 1 ≤ k := by omega
  have hN : 2 * k + 2 ≤ N := by omega
  have hN6 : N < 6 * (k + 1) := by omega
  -- (S1)
  obtain ⟨m, hm⟩ : ∃ m, k + 1 + l = 2 * m := ⟨(k + 1 + l) / 2, by omega⟩
  have hH' : N * ((2 * k + 1 - k) / 2) < (m + 1) * (4 * (2 * k + 1) - N) := by
    have e1 : (2 * k + 1 - k) / 2 = r := by omega
    have e2 : 4 * (2 * k + 1) - N = 8 * r + 2 - 2 * l := by omega
    rw [e1, e2]
    have hl2 : 2 * l ≤ 8 * r + 2 := by omega
    zify [hl2]
    have z1 : (N : ℤ) = 8 * r + 2 + 2 * l := by exact_mod_cast (by omega : N = 8 * r + 2 + 2 * l)
    have z2 : (2 : ℤ) * (m + 1) = 2 * r + 3 + l := by
      exact_mod_cast (by omega : 2 * (m + 1) = 2 * r + 3 + l)
    have z3 : (l : ℤ) * l + 2 * l + 3 < 6 * (2 * r + 1) := by
      exact_mod_cast (by omega : l * l + 2 * l + 3 < 6 * (2 * r + 1))
    rw [z1]
    have key : 2 * ((8 * (r : ℤ) + 2 + 2 * l) * r) < (2 * r + 3 + l) * (8 * r + 2 - 2 * l) := by
      nlinarith [z3]
    have e := congrArg (fun x => x * (8 * (r : ℤ) + 2 - 2 * l)) z2
    nlinarith [key, e]
  obtain ⟨S1a, S1b⟩ := structure_S1 h hk1 hN hN6 (L := 2 * k + 1) (m := m) (by omega) (by omega)
    (by omega) (by omega) hH'
  have hFw : ∀ t L, Fw (fun t => cnt T 0 N (T t) = 4) t L = Fcount T N t L := fun t L => rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t
    show (cnt T 0 N (T (t + N)) = 4 ↔ cnt T 0 N (T t) = 4)
    rw [h.per]
  · intro t
    rw [hFw, Fcount, card_filter]
    have hper : ∀ i, (if cnt T 0 N (T (i + N)) = 4 then 1 else 0)
        = (if cnt T 0 N (T i) = 4 then 1 else 0) := by
      intro i; rw [h.per]
    have h1 := sum_shift (fun i => if cnt T 0 N (T i) = 4 then 1 else 0) N hper t
    have h2 := F_positions h
    rw [S1a] at h2
    simp only [add_comm t] at h1 ⊢
    rw [h1, h2]
    omega
  · intro t L hL1 hL2
    have hb := balanced h hk1 hN S1a (t := t) (Lw := L) (by omega) (by omega) (by omega)
    rw [hFw]
    omega
  · intro t
    obtain ⟨K, hK⟩ : ∃ K, K = k + 1 := ⟨_, rfl⟩
    rw [← hK, hFw]
    -- the window of length 2K+1 = K + K + 1
    have hsplit : ∀ c, cnt T t (K + K + 1) c
        = cnt T t K c + cnt T (t + K) K c + (if T (t + K + K) = c then 1 else 0) := by
      intro c
      rw [cnt_add, cnt_add, cnt_one, ← Nat.add_assoc]
    have hs1 : ∀ s c, cnt T s K c ≤ 1 := fun s c => cnt_short h hk1 hN (by omega) c
    have o1 := f1 h hk1 (t := t) (L := K + K + 1) (by omega) (by omega)
    have p1 := oddc_parity T t (K + K + 1)
    rw [Nat.odd_iff, Nat.odd_iff] at p1
    have hsum := sum_cnt T t (K + K + 1)
    -- F positions as a sum over coordinates
    have e1 : Fcount T N t (K + K + 1)
        = ∑ c : α, if cnt T 0 N c = 4 then cnt T t (K + K + 1) c else 0 := by
      rw [Fcount, card_filter]
      have : ∀ i ∈ range (K + K + 1), (if cnt T 0 N (T (t + i)) = 4 then 1 else 0)
          = ∑ c : α, if T (t + i) = c then (if cnt T 0 N c = 4 then 1 else 0) else 0 := by
        intro i _
        rw [sum_ite_eq]
        simp
      rw [sum_congr rfl this, sum_comm]
      apply sum_congr rfl
      intro c _
      by_cases hc : cnt T 0 N c = 4
      · simp only [hc, if_true]
        rw [cnt_eq_sum]
      · simp [hc]
    have pw : ∀ c ∈ (univ : Finset α),
        2 * (if cnt T 0 N c = 4 then cnt T t (K + K + 1) c else 0)
          + (if Odd (cnt T t (K + K + 1) c) then 1 else 0)
        ≤ 2 * (if cnt T 0 N c = 4 then 1 else 0) + cnt T t (K + K + 1) c
          + 2 * (if cnt T t (K + K + 1) c = 3 then 1 else 0) := by
      intro c _
      have a1 := hs1 t c
      have a2 := hs1 (t + K) c
      rw [hsplit c]
      simp only [Nat.odd_iff]
      split_ifs <;> omega
    have S := sum_le_sum pw
    simp only [sum_add_distrib, ← mul_sum] at S
    rw [← e1, ← oddc_eq_sum, hsum, ← card_filter, ← card_filter, S1a] at S
    -- at most one coordinate occurs three times, and then T t = T (t+K) = T (t+2K)
    have h3 : ∀ c, cnt T t (K + K + 1) c = 3 → T (t + K) = c := by
      intro c hc
      have a1 := hs1 t c
      have a2 := hs1 (t + K) c
      rw [hsplit c] at hc
      have b2 : 1 ≤ cnt T (t + K) K c := by split_ifs at hc <;> omega
      have b3 : T (t + K + K) = c := by
        by_contra hne
        rw [if_neg hne] at hc
        omega
      obtain ⟨i, hi, ei⟩ := exists_of_one_le_cnt b2
      by_cases hi0 : i = 0
      · rw [hi0, add_zero] at ei
        exact ei
      · exfalso
        have := gap_ge h hk1 hN (u := t + K + i) (d := K - i) (by omega)
          (by rw [show t + K + i + (K - i) = t + K + K by omega]; exact ei.trans b3.symm)
        omega
    have htr : #{c : α | cnt T t (K + K + 1) c = 3} ≤ 1 := by
      have : ({c : α | cnt T t (K + K + 1) c = 3} : Finset α) ⊆ {T (t + K)} := by
        intro c hc
        simp only [mem_filter, mem_univ, true_and] at hc
        rw [mem_singleton]
        exact (h3 c hc).symm
      calc _ ≤ #({T (t + K)} : Finset α) := card_le_card this
        _ = 1 := card_singleton _
    rw [show 2 * K + 1 = K + K + 1 by omega]
    constructor
    · omega
    · intro heq
      have htr1 : 0 < #{c : α | cnt T t (K + K + 1) c = 3} := by omega
      obtain ⟨c, hc⟩ := card_pos.mp htr1
      simp only [mem_filter, mem_univ, true_and] at hc
      have hTc := h3 c hc
      show cnt T 0 N (T (t + K)) = 4
      rw [hTc]
      -- c occurs three times in a window shorter than N, so it is used four times
      rcases S1b c with h4 | h2
      · exact h4
      · exfalso
        have e : cnt T t N c = cnt T t (K + K + 1) c + cnt T (t + (K + K + 1)) (N - (K + K + 1)) c := by
          rw [← cnt_add, show K + K + 1 + (N - (K + K + 1)) = N by omega]
        rw [cnt_period h.per, h2, hc] at e
        omega

end Coil

#print axioms Coil.typeWord_of_coil
