import Ccformal.Basic

/-!
# A counterexample to Byrnes' Conjecture 4.2: a spread-13 circuit code of length 66 in Q_23
(the conjecture predicts K(23,13) = 4k + 2l = 64; code found by SAT, S162)
-/

open Finset

namespace Coil

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- a finite check suffices -/
theorem IsCoil.of_fin {k N : ℕ} (w : ℕ → α → Bool) (hpos : 0 < N)
    (hadj : ∀ i < N, hd (w (i % N)) (w ((i + 1) % N)) = 1)
    (hsp : ∀ i < N, ∀ L < N, hd (w (i % N)) (w ((i + L) % N)) < k →
      hd (w (i % N)) (w ((i + L) % N)) = min L (N - L)) :
    IsCoil k N (fun i => w (i % N)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simp only [Nat.add_mod_right]
  · intro i
    have := hadj (i % N) (Nat.mod_lt _ hpos)
    rwa [Nat.mod_mod, Nat.mod_add_mod] at this
  · intro i L hL
    have := hsp (i % N) (Nat.mod_lt _ hpos) L hL
    rwa [Nat.mod_mod, Nat.mod_add_mod] at this

def w66 : List ℕ := [0x0, 0x1, 0x3, 0x7, 0xf, 0x1f, 0x3f, 0x7f, 0xff, 0x1ff, 0x3ff, 0x7ff, 0xfff, 0x1fff, 0x3fff, 0x7fff, 0xffff, 0x1ffff, 0x1fff7, 0x3fff7, 0x3fff5, 0x7fff5, 0x7ff75, 0x7ff35, 0xfff35, 0xffd35, 0x1ffd35, 0x1ffd25, 0x1fdd25, 0x3fdd25, 0x3fd525, 0x7fd525, 0x7ed525, 0x7ed52d, 0x7ed52c, 0x7ed52e, 0x7ed52a, 0x7ed56a, 0x7e956a, 0x7e954a, 0x7e974a, 0x7e964a, 0x7e965a, 0x7eb65a, 0x7eb25a, 0x7eb2da, 0x7fb2da, 0x7fa2da, 0x7faada, 0x7f2ada, 0x7f2ad8, 0x7d2ad8, 0x7d6ad8, 0x7d6a98, 0x796a98, 0x796a90, 0x796a80, 0x716a80, 0x716880, 0x616880, 0x616800, 0x606800, 0x206800, 0x206000, 0x6000, 0x4000]

def v66 (i : ℕ) (c : Fin 23) : Bool := (w66.getD i 0).testBit c

theorem adj66 : ∀ i < 66, hd (v66 (i % 66)) (v66 ((i + 1) % 66)) = 1 := by decide +kernel

theorem spread66 : ∀ i < 66, ∀ L < 66, hd (v66 (i % 66)) (v66 ((i + L) % 66)) < 13 →
    hd (v66 (i % 66)) (v66 ((i + L) % 66)) = min L (66 - L) := by decide +kernel

/-- a spread-13 circuit code of length 66 in the 23-cube -/
theorem coil66 : IsCoil 13 66 (fun i => v66 (i % 66)) :=
  IsCoil.of_fin v66 (by norm_num) adj66 spread66

/-- Byrnes' Conjecture 4.2 fails at (n,k) = (23,13): `l = 2n-3k-1 = 6`, `4k+2l = 64 < 66`. -/
theorem counterexample_23_13 :
    ∃ v : ℕ → Fin 23 → Bool, IsCoil 13 66 v ∧ 4 * 13 + 2 * (2 * 23 - 3 * 13 - 1) < 66 :=
  ⟨_, coil66, by norm_num⟩

/-- **K(23,13) = 66** (Byrnes' Conjecture 4.2 predicts 64). -/
theorem K_23_13_example : IsMaxLength 23 13 66 :=
  isMaxLength_of_chord ⟨_, coil66⟩ (by norm_num) 28 (by norm_num) (by norm_num) (by decide +kernel)


end Coil

#print axioms Coil.counterexample_23_13
#print axioms Coil.K_23_13_example
