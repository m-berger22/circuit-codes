import Ccformal.Checker

namespace Coil

def W_36_21 : ℕ := 0x22000d0020000c0023000e001f00080021000b00090006001d0005001e000a001b0003001a0001001c00040007000d001700000019000e001800020008000b00150009001400050016000c00110003000a0001001000040012000700130006000f000e002300000022000b000200090021000d0020000c001f0005001e000a001d000800040007001c0006001b0003001a000e001900010002001800000017000d000c0016000b0015000a00090008001400070013000600120005001100040010000300020001000f0000

def f_36_21 (i : ℕ) : ℕ := (W_36_21 >>> (16 * i)) &&& 0xFFFF

theorem ok_36_21_0 : ∀ t < 0, okAt f_36_21 36 21 102 t = true := allRange_zero

theorem blk_36_21_0 : allRange (okAt f_36_21 36 21 102) 0 102 = true := by decide +kernel
theorem ok_36_21_102 : ∀ t < 102, okAt f_36_21 36 21 102 t = true := allRange_extend ok_36_21_0 blk_36_21_0

theorem coil_36_21 : ∃ v : ℕ → Fin 36 → Bool, IsCoil 21 102 v :=
  exists_coil_of_check f_36_21 21 102 (by norm_num) ok_36_21_102 (by decide +kernel)

/-- K(36,21) = 102  (= 4k+2l+2, l = 8; code: skel_36_21_102.txt) -/
theorem K_36_21 : IsMaxLength 36 21 102 :=
  isMaxLength_of_chord coil_36_21 (by norm_num) 44 (by norm_num) (by norm_num) (by decide +kernel)


end Coil
