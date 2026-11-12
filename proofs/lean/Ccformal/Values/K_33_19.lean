import Ccformal.Checker

namespace Coil

def W_33_19 : ℕ := 0x1f000d0020000b000a001e000e0008001c0009001d00060005001b000c000300190004001a0001000000180007000b0016000d0017000e0008001500020006001300090014000c00030012000a00010010000400110007000b000f0005000e0020000d001f00020006001e0000000c001d0009001c000a0001001b00080007001a000400190005000e0018000300020017000d00160000000c0015000b000a0014000900130008000700120006000500110004001000030002000f00010000

def f_33_19 (i : ℕ) : ℕ := (W_33_19 >>> (16 * i)) &&& 0xFFFF

theorem ok_33_19_0 : ∀ t < 0, okAt f_33_19 33 19 96 t = true := allRange_zero

theorem blk_33_19_0 : allRange (okAt f_33_19 33 19 96) 0 96 = true := by decide +kernel
theorem ok_33_19_96 : ∀ t < 96, okAt f_33_19 33 19 96 t = true := allRange_extend ok_33_19_0 blk_33_19_0

theorem coil_33_19 : ∃ v : ℕ → Fin 33 → Bool, IsCoil 19 96 v :=
  exists_coil_of_check f_33_19 19 96 (by norm_num) ok_33_19_96 (by decide +kernel)

/-- K(33,19) = 96  (= 4k+2l+4, l = 8; code: skel_33_19_96.txt) -/
theorem K_33_19 : IsMaxLength 33 19 96 :=
  isMaxLength_of_chord coil_33_19 (by norm_num) 40 (by norm_num) (by norm_num) (by decide +kernel)


end Coil
