import Ccformal.Checker

namespace Coil

def W_23_13 : ℕ := 0xe000d0015000b0016001000070014000900130004000300120006000e00110001000f000b000c00100007000a000d0004000800090005000e0006000200010000000300100016000b0015000d00040014000900130006000700120001001100030010000f000e000d000c000b000a0009000800070006000500040003000200010000

def f_23_13 (i : ℕ) : ℕ := (W_23_13 >>> (16 * i)) &&& 0xFFFF

theorem ok_23_13_0 : ∀ t < 0, okAt f_23_13 23 13 66 t = true := allRange_zero

theorem blk_23_13_0 : allRange (okAt f_23_13 23 13 66) 0 66 = true := by decide +kernel
theorem ok_23_13_66 : ∀ t < 66, okAt f_23_13 23 13 66 t = true := allRange_extend ok_23_13_0 blk_23_13_0

theorem coil_23_13 : ∃ v : ℕ → Fin 23 → Bool, IsCoil 13 66 v :=
  exists_coil_of_check f_23_13 13 66 (by norm_num) ok_23_13_66 (by decide +kernel)

/-- K(23,13) = 66  (= 4k+2l+2, l = 6; code: sat_23_13_66.txt) -/
theorem K_23_13 : IsMaxLength 23 13 66 :=
  isMaxLength_of_chord coil_23_13 (by norm_num) 28 (by norm_num) (by norm_num) (by decide +kernel)


end Coil
