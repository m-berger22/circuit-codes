import Ccformal.Checker

namespace Coil

def W_709_462 : ℕ := 0x2c401dc01da02c301d802c201d602c101d402c001d202bf01c502be01c702bd01c902bc01cb02bb01d002ba01e602b901cd01b502b801b302b701b702b601b902b501bb02b401bd02b301bf02b201c102b101c302b001a602af01a802ae01aa02ad01ac02ac01b202ab01b002aa01ae019602a9019402a8019802a7019a02a6019c02a5019e02a401a002a301a202a201a402a1018702a00189029f018b029e018d029d0193029c0191029b018f0177029a0175029901790298017b0297017d0296017f029501810294018302930185029201680291016a0290016c028f016e028e0174028d0172028c01700158028b0156028a015a0289015c0288015e02870160028601620285016402840166028301490282014b0281014d0280014f027f0155027e0153027d01510139027c0137027b013b027a013d0279013f027801410277014302760145027501470274012a0273012c0272012e0271013002700136026f0134026e0132011a026d0118026c011c026b011e026a0120026901220268012402670126026601280265010b0264010d0263010f026201110261011702600115025f011300fb025e00f9025d00fd025c00ff025b0101025a0103025901050258010702570109025600ec025500ee025400f0025300f2025200f8025100f6025000f400dc024f00da024e00de024d00e0024c00e2024b00e4024a00e6024900e8024800ea024700cd024600cf024500d1024400d3024300d9024200d7024100d500bd024000bb023f00bf023e00c1023d00c3023c00c5023b00c7023a00c9023900cb023800ae023700b0023600b2023500b4023400ba023300b8023200b6009e0231009c023000a0022f00a2022e00a4022d00a6022c00a8022b00aa022a00ac0229008f0228009102270093022600950225009b0224009902230097007f0222007d0221008102200083021f0085021e0087021d0089021c008b021b008d021a00700219007202180074021700760216007c0215007a0214007800600213005e021200620211006402100066020f0068020e006a020d006c020c006e020b0051020a005302090055020800570207005d0206005b0205005900410204003f0203004302020045020100470200004901ff004b01fe004d01fd004f01fc003201fb003401fa003601f9003801f8003e01f7003c01f6003a002201f5002001f4002401f3002601f2002801f1002a01f0002c01ef002e01ee003001ed001301ec001501eb001701ea001901e9001f01e8001d01e7001b000301e5000101e4000501e3000701e2000901e1000b01e0000d01df000f01de001101dd01dc01db01da01d901d801d701d601d501d401d301d201d101e601b301cf01b701ce01cd01cc01cb01ca01c901c801c701c601c501c401c301c201c101c001bf01be01bd01bc01bb01ba01b901b8000001b601ae01b401d0019401b101b001af01b501ad01ac01ab01aa01a901a801a701a601a501a401a301a201a101a0019f019e019d019c019b019a019901980197018f019501b201750192019101900196018e018d018c018b018a0189018801870186018501840183018201810180017f017e017d017c017b017a0179017801700176019301560173017201710177016f016e016d016c016b016a0169016801670166016501640163016201610160015f015e015d015c015b015a0159015101570174013701540153015201580150014f014e014d014c014b014a0149014801470146014501440143014201410140013f013e013d013c013b013a0132013801550118013501340133013901310130012f012e012d012c012b012a0129012801270126012501240123012201210120011f011e011d011c011b01130119013600f9011601150114011a011201110110010f010e010d010c010b010a010901080107010601050104010301020101010000ff00fe00fd00fc00f400fa011700da00f700f600f500fb00f300f200f100f000ef00ee00ed00ec00eb00ea00e900e800e700e600e500e400e300e200e100e000df00de00dd00d500db00f800bb00d800d700d600dc00d400d300d200d100d000cf00ce00cd00cc00cb00ca00c900c800c700c600c500c400c300c200c100c000bf00be00b600bc00d9009c00b900b800b700bd00b500b400b300b200b100b000af00ae00ad00ac00ab00aa00a900a800a700a600a500a400a300a200a100a0009f0097009d00ba007d009a00990098009e0096009500940093009200910090008f008e008d008c008b008a00890088008700860085008400830082008100800078007e009b005e007b007a0079007f00770076007500740073007200710070006f006e006d006c006b006a0069006800670066006500640063006200610059005f007c003f005c005b005a0060005800570056005500540053005200510050004f004e004d004c004b004a00490048004700460045004400430042003a0040005d0020003d003c003b00410039003800370036003500340033003200310030002f002e002d002c002b002a0029002800270026002500240023001b0021003e0001001e001d001c0022001a0019001800170016001500140013001200110010000f000e000d000c000b000a00090008000700060005000401e60002001f01b702c401dc01da02c301d802c201d602c101d402c001d202bf01c502be01c702bd01c902bc01cb02bb01b302ba000302b901cd01ae02b801d002b7000002b601b902b501bb02b401bd02b301bf02b201c102b101c302b001a602af01a802ae01aa02ad01ac02ac019402ab01b002aa01b5018f02a901b202a8019802a7019a02a6019c02a5019e02a401a002a301a202a201a402a1018702a00189029f018b029e018d029d0175029c0191029b01960170029a0193029901790298017b0297017d0296017f029501810294018302930185029201680291016a0290016c028f016e028e0156028d0172028c01770151028b0174028a015a0289015c0288015e02870160028601620285016402840166028301490282014b0281014d0280014f027f0137027e0153027d01580132027c0155027b013b027a013d0279013f027801410277014302760145027501470274012a0273012c0272012e0271013002700118026f0134026e01390113026d0136026c011c026b011e026a0120026901220268012402670126026601280265010b0264010d0263010f02620111026100f902600115025f011a00f4025e0117025d00fd025c00ff025b0101025a0103025901050258010702570109025600ec025500ee025400f0025300f2025200da025100f6025000fb00d5024f00f8024e00de024d00e0024c00e2024b00e4024a00e6024900e8024800ea024700cd024600cf024500d1024400d3024300bb024200d7024100dc00b6024000d9023f00bf023e00c1023d00c3023c00c5023b00c7023a00c9023900cb023800ae023700b0023600b2023500b40234009c023300b8023200bd0097023100ba023000a0022f00a2022e00a4022d00a6022c00a8022b00aa022a00ac0229008f0228009102270093022600950225007d022400990223009e00780222009b0221008102200083021f0085021e0087021d0089021c008b021b008d021a00700219007202180074021700760216005e0215007a0214007f00590213007c021200620211006402100066020f0068020e006a020d006c020c006e020b0051020a005302090055020800570207003f0206005b02050060003a0204005d0203004302020045020100470200004901ff004b01fe004d01fd004f01fc003201fb003401fa003601f9003801f8002001f7003c01f60041001b01f5003e01f4002401f3002601f2002801f1002a01f0002c01ef002e01ee003001ed001301ec001501eb001701ea001901e9000101e8001d01e7002201e601e5001f01e4000501e3000701e2000901e1000b01e0000d01df000f01de001101dd01dc01db01da01d901d801d701d601d501d401d301d201d1000301d001cf000001ce01cd01cc01cb01ca01c901c801c701c601c501c401c301c201c101c001bf01be01bd01bc01bb01ba01b901b801b701b601b501b401b301b201b101b001af01ae01ad01ac01ab01aa01a901a801a701a601a501a401a301a201a101a0019f019e019d019c019b019a0199019801970196019501940193019201910190018f018e018d018c018b018a0189018801870186018501840183018201810180017f017e017d017c017b017a0179017801770176017501740173017201710170016f016e016d016c016b016a0169016801670166016501640163016201610160015f015e015d015c015b015a0159015801570156015501540153015201510150014f014e014d014c014b014a0149014801470146014501440143014201410140013f013e013d013c013b013a0139013801370136013501340133013201310130012f012e012d012c012b012a0129012801270126012501240123012201210120011f011e011d011c011b011a0119011801170116011501140113011201110110010f010e010d010c010b010a010901080107010601050104010301020101010000ff00fe00fd00fc00fb00fa00f900f800f700f600f500f400f300f200f100f000ef00ee00ed00ec00eb00ea00e900e800e700e600e500e400e300e200e100e000df00de00dd00dc00db00da00d900d800d700d600d500d400d300d200d100d000cf00ce00cd00cc00cb00ca00c900c800c700c600c500c400c300c200c100c000bf00be00bd00bc00bb00ba00b900b800b700b600b500b400b300b200b100b000af00ae00ad00ac00ab00aa00a900a800a700a600a500a400a300a200a100a0009f009e009d009c009b009a0099009800970096009500940093009200910090008f008e008d008c008b008a0089008800870086008500840083008200810080007f007e007d007c007b007a0079007800770076007500740073007200710070006f006e006d006c006b006a0069006800670066006500640063006200610060005f005e005d005c005b005a0059005800570056005500540053005200510050004f004e004d004c004b004a0049004800470046004500440043004200410040003f003e003d003c003b003a0039003800370036003500340033003200310030002f002e002d002c002b002a0029002800270026002500240023002200210020001f001e001d001c001b001a0019001800170016001500140013001200110010000f000e000d000c000b000a0009000800070006000500040003000200010000

def f_709_462 (i : ℕ) : ℕ := (W_709_462 >>> (16 * i)) &&& 0xFFFF

theorem ok_709_462_0 : ∀ t < 0, okAt f_709_462 709 462 1912 t = true := allRange_zero

theorem blk_709_462_0 : allRange (okAt f_709_462 709 462 1912) 0 10 = true := by decide +kernel
theorem ok_709_462_10 : ∀ t < 10, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_0 blk_709_462_0
theorem blk_709_462_10 : allRange (okAt f_709_462 709 462 1912) 10 10 = true := by decide +kernel
theorem ok_709_462_20 : ∀ t < 20, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_10 blk_709_462_10
theorem blk_709_462_20 : allRange (okAt f_709_462 709 462 1912) 20 10 = true := by decide +kernel
theorem ok_709_462_30 : ∀ t < 30, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_20 blk_709_462_20
theorem blk_709_462_30 : allRange (okAt f_709_462 709 462 1912) 30 10 = true := by decide +kernel
theorem ok_709_462_40 : ∀ t < 40, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_30 blk_709_462_30
theorem blk_709_462_40 : allRange (okAt f_709_462 709 462 1912) 40 10 = true := by decide +kernel
theorem ok_709_462_50 : ∀ t < 50, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_40 blk_709_462_40
theorem blk_709_462_50 : allRange (okAt f_709_462 709 462 1912) 50 10 = true := by decide +kernel
theorem ok_709_462_60 : ∀ t < 60, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_50 blk_709_462_50
theorem blk_709_462_60 : allRange (okAt f_709_462 709 462 1912) 60 10 = true := by decide +kernel
theorem ok_709_462_70 : ∀ t < 70, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_60 blk_709_462_60
theorem blk_709_462_70 : allRange (okAt f_709_462 709 462 1912) 70 10 = true := by decide +kernel
theorem ok_709_462_80 : ∀ t < 80, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_70 blk_709_462_70
theorem blk_709_462_80 : allRange (okAt f_709_462 709 462 1912) 80 10 = true := by decide +kernel
theorem ok_709_462_90 : ∀ t < 90, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_80 blk_709_462_80
theorem blk_709_462_90 : allRange (okAt f_709_462 709 462 1912) 90 10 = true := by decide +kernel
theorem ok_709_462_100 : ∀ t < 100, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_90 blk_709_462_90
theorem blk_709_462_100 : allRange (okAt f_709_462 709 462 1912) 100 10 = true := by decide +kernel
theorem ok_709_462_110 : ∀ t < 110, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_100 blk_709_462_100
theorem blk_709_462_110 : allRange (okAt f_709_462 709 462 1912) 110 10 = true := by decide +kernel
theorem ok_709_462_120 : ∀ t < 120, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_110 blk_709_462_110
theorem blk_709_462_120 : allRange (okAt f_709_462 709 462 1912) 120 10 = true := by decide +kernel
theorem ok_709_462_130 : ∀ t < 130, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_120 blk_709_462_120
theorem blk_709_462_130 : allRange (okAt f_709_462 709 462 1912) 130 10 = true := by decide +kernel
theorem ok_709_462_140 : ∀ t < 140, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_130 blk_709_462_130
theorem blk_709_462_140 : allRange (okAt f_709_462 709 462 1912) 140 10 = true := by decide +kernel
theorem ok_709_462_150 : ∀ t < 150, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_140 blk_709_462_140
theorem blk_709_462_150 : allRange (okAt f_709_462 709 462 1912) 150 10 = true := by decide +kernel
theorem ok_709_462_160 : ∀ t < 160, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_150 blk_709_462_150
theorem blk_709_462_160 : allRange (okAt f_709_462 709 462 1912) 160 10 = true := by decide +kernel
theorem ok_709_462_170 : ∀ t < 170, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_160 blk_709_462_160
theorem blk_709_462_170 : allRange (okAt f_709_462 709 462 1912) 170 10 = true := by decide +kernel
theorem ok_709_462_180 : ∀ t < 180, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_170 blk_709_462_170
theorem blk_709_462_180 : allRange (okAt f_709_462 709 462 1912) 180 10 = true := by decide +kernel
theorem ok_709_462_190 : ∀ t < 190, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_180 blk_709_462_180
theorem blk_709_462_190 : allRange (okAt f_709_462 709 462 1912) 190 10 = true := by decide +kernel
theorem ok_709_462_200 : ∀ t < 200, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_190 blk_709_462_190
theorem blk_709_462_200 : allRange (okAt f_709_462 709 462 1912) 200 10 = true := by decide +kernel
theorem ok_709_462_210 : ∀ t < 210, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_200 blk_709_462_200
theorem blk_709_462_210 : allRange (okAt f_709_462 709 462 1912) 210 10 = true := by decide +kernel
theorem ok_709_462_220 : ∀ t < 220, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_210 blk_709_462_210
theorem blk_709_462_220 : allRange (okAt f_709_462 709 462 1912) 220 10 = true := by decide +kernel
theorem ok_709_462_230 : ∀ t < 230, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_220 blk_709_462_220
theorem blk_709_462_230 : allRange (okAt f_709_462 709 462 1912) 230 10 = true := by decide +kernel
theorem ok_709_462_240 : ∀ t < 240, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_230 blk_709_462_230
theorem blk_709_462_240 : allRange (okAt f_709_462 709 462 1912) 240 10 = true := by decide +kernel
theorem ok_709_462_250 : ∀ t < 250, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_240 blk_709_462_240
theorem blk_709_462_250 : allRange (okAt f_709_462 709 462 1912) 250 10 = true := by decide +kernel
theorem ok_709_462_260 : ∀ t < 260, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_250 blk_709_462_250
theorem blk_709_462_260 : allRange (okAt f_709_462 709 462 1912) 260 10 = true := by decide +kernel
theorem ok_709_462_270 : ∀ t < 270, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_260 blk_709_462_260
theorem blk_709_462_270 : allRange (okAt f_709_462 709 462 1912) 270 10 = true := by decide +kernel
theorem ok_709_462_280 : ∀ t < 280, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_270 blk_709_462_270
theorem blk_709_462_280 : allRange (okAt f_709_462 709 462 1912) 280 10 = true := by decide +kernel
theorem ok_709_462_290 : ∀ t < 290, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_280 blk_709_462_280
theorem blk_709_462_290 : allRange (okAt f_709_462 709 462 1912) 290 10 = true := by decide +kernel
theorem ok_709_462_300 : ∀ t < 300, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_290 blk_709_462_290
theorem blk_709_462_300 : allRange (okAt f_709_462 709 462 1912) 300 10 = true := by decide +kernel
theorem ok_709_462_310 : ∀ t < 310, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_300 blk_709_462_300
theorem blk_709_462_310 : allRange (okAt f_709_462 709 462 1912) 310 10 = true := by decide +kernel
theorem ok_709_462_320 : ∀ t < 320, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_310 blk_709_462_310
theorem blk_709_462_320 : allRange (okAt f_709_462 709 462 1912) 320 10 = true := by decide +kernel
theorem ok_709_462_330 : ∀ t < 330, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_320 blk_709_462_320
theorem blk_709_462_330 : allRange (okAt f_709_462 709 462 1912) 330 10 = true := by decide +kernel
theorem ok_709_462_340 : ∀ t < 340, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_330 blk_709_462_330
theorem blk_709_462_340 : allRange (okAt f_709_462 709 462 1912) 340 10 = true := by decide +kernel
theorem ok_709_462_350 : ∀ t < 350, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_340 blk_709_462_340
theorem blk_709_462_350 : allRange (okAt f_709_462 709 462 1912) 350 10 = true := by decide +kernel
theorem ok_709_462_360 : ∀ t < 360, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_350 blk_709_462_350
theorem blk_709_462_360 : allRange (okAt f_709_462 709 462 1912) 360 10 = true := by decide +kernel
theorem ok_709_462_370 : ∀ t < 370, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_360 blk_709_462_360
theorem blk_709_462_370 : allRange (okAt f_709_462 709 462 1912) 370 10 = true := by decide +kernel
theorem ok_709_462_380 : ∀ t < 380, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_370 blk_709_462_370
theorem blk_709_462_380 : allRange (okAt f_709_462 709 462 1912) 380 10 = true := by decide +kernel
theorem ok_709_462_390 : ∀ t < 390, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_380 blk_709_462_380
theorem blk_709_462_390 : allRange (okAt f_709_462 709 462 1912) 390 10 = true := by decide +kernel
theorem ok_709_462_400 : ∀ t < 400, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_390 blk_709_462_390
theorem blk_709_462_400 : allRange (okAt f_709_462 709 462 1912) 400 10 = true := by decide +kernel
theorem ok_709_462_410 : ∀ t < 410, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_400 blk_709_462_400
theorem blk_709_462_410 : allRange (okAt f_709_462 709 462 1912) 410 10 = true := by decide +kernel
theorem ok_709_462_420 : ∀ t < 420, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_410 blk_709_462_410
theorem blk_709_462_420 : allRange (okAt f_709_462 709 462 1912) 420 10 = true := by decide +kernel
theorem ok_709_462_430 : ∀ t < 430, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_420 blk_709_462_420
theorem blk_709_462_430 : allRange (okAt f_709_462 709 462 1912) 430 10 = true := by decide +kernel
theorem ok_709_462_440 : ∀ t < 440, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_430 blk_709_462_430
theorem blk_709_462_440 : allRange (okAt f_709_462 709 462 1912) 440 10 = true := by decide +kernel
theorem ok_709_462_450 : ∀ t < 450, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_440 blk_709_462_440
theorem blk_709_462_450 : allRange (okAt f_709_462 709 462 1912) 450 10 = true := by decide +kernel
theorem ok_709_462_460 : ∀ t < 460, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_450 blk_709_462_450
theorem blk_709_462_460 : allRange (okAt f_709_462 709 462 1912) 460 10 = true := by decide +kernel
theorem ok_709_462_470 : ∀ t < 470, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_460 blk_709_462_460
theorem blk_709_462_470 : allRange (okAt f_709_462 709 462 1912) 470 10 = true := by decide +kernel
theorem ok_709_462_480 : ∀ t < 480, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_470 blk_709_462_470
theorem blk_709_462_480 : allRange (okAt f_709_462 709 462 1912) 480 10 = true := by decide +kernel
theorem ok_709_462_490 : ∀ t < 490, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_480 blk_709_462_480
theorem blk_709_462_490 : allRange (okAt f_709_462 709 462 1912) 490 10 = true := by decide +kernel
theorem ok_709_462_500 : ∀ t < 500, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_490 blk_709_462_490
theorem blk_709_462_500 : allRange (okAt f_709_462 709 462 1912) 500 10 = true := by decide +kernel
theorem ok_709_462_510 : ∀ t < 510, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_500 blk_709_462_500
theorem blk_709_462_510 : allRange (okAt f_709_462 709 462 1912) 510 10 = true := by decide +kernel
theorem ok_709_462_520 : ∀ t < 520, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_510 blk_709_462_510
theorem blk_709_462_520 : allRange (okAt f_709_462 709 462 1912) 520 10 = true := by decide +kernel
theorem ok_709_462_530 : ∀ t < 530, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_520 blk_709_462_520
theorem blk_709_462_530 : allRange (okAt f_709_462 709 462 1912) 530 10 = true := by decide +kernel
theorem ok_709_462_540 : ∀ t < 540, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_530 blk_709_462_530
theorem blk_709_462_540 : allRange (okAt f_709_462 709 462 1912) 540 10 = true := by decide +kernel
theorem ok_709_462_550 : ∀ t < 550, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_540 blk_709_462_540
theorem blk_709_462_550 : allRange (okAt f_709_462 709 462 1912) 550 10 = true := by decide +kernel
theorem ok_709_462_560 : ∀ t < 560, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_550 blk_709_462_550
theorem blk_709_462_560 : allRange (okAt f_709_462 709 462 1912) 560 10 = true := by decide +kernel
theorem ok_709_462_570 : ∀ t < 570, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_560 blk_709_462_560
theorem blk_709_462_570 : allRange (okAt f_709_462 709 462 1912) 570 10 = true := by decide +kernel
theorem ok_709_462_580 : ∀ t < 580, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_570 blk_709_462_570
theorem blk_709_462_580 : allRange (okAt f_709_462 709 462 1912) 580 10 = true := by decide +kernel
theorem ok_709_462_590 : ∀ t < 590, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_580 blk_709_462_580
theorem blk_709_462_590 : allRange (okAt f_709_462 709 462 1912) 590 10 = true := by decide +kernel
theorem ok_709_462_600 : ∀ t < 600, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_590 blk_709_462_590
theorem blk_709_462_600 : allRange (okAt f_709_462 709 462 1912) 600 10 = true := by decide +kernel
theorem ok_709_462_610 : ∀ t < 610, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_600 blk_709_462_600
theorem blk_709_462_610 : allRange (okAt f_709_462 709 462 1912) 610 10 = true := by decide +kernel
theorem ok_709_462_620 : ∀ t < 620, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_610 blk_709_462_610
theorem blk_709_462_620 : allRange (okAt f_709_462 709 462 1912) 620 10 = true := by decide +kernel
theorem ok_709_462_630 : ∀ t < 630, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_620 blk_709_462_620
theorem blk_709_462_630 : allRange (okAt f_709_462 709 462 1912) 630 10 = true := by decide +kernel
theorem ok_709_462_640 : ∀ t < 640, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_630 blk_709_462_630
theorem blk_709_462_640 : allRange (okAt f_709_462 709 462 1912) 640 10 = true := by decide +kernel
theorem ok_709_462_650 : ∀ t < 650, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_640 blk_709_462_640
theorem blk_709_462_650 : allRange (okAt f_709_462 709 462 1912) 650 10 = true := by decide +kernel
theorem ok_709_462_660 : ∀ t < 660, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_650 blk_709_462_650
theorem blk_709_462_660 : allRange (okAt f_709_462 709 462 1912) 660 10 = true := by decide +kernel
theorem ok_709_462_670 : ∀ t < 670, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_660 blk_709_462_660
theorem blk_709_462_670 : allRange (okAt f_709_462 709 462 1912) 670 10 = true := by decide +kernel
theorem ok_709_462_680 : ∀ t < 680, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_670 blk_709_462_670
theorem blk_709_462_680 : allRange (okAt f_709_462 709 462 1912) 680 10 = true := by decide +kernel
theorem ok_709_462_690 : ∀ t < 690, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_680 blk_709_462_680
theorem blk_709_462_690 : allRange (okAt f_709_462 709 462 1912) 690 10 = true := by decide +kernel
theorem ok_709_462_700 : ∀ t < 700, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_690 blk_709_462_690
theorem blk_709_462_700 : allRange (okAt f_709_462 709 462 1912) 700 10 = true := by decide +kernel
theorem ok_709_462_710 : ∀ t < 710, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_700 blk_709_462_700
theorem blk_709_462_710 : allRange (okAt f_709_462 709 462 1912) 710 10 = true := by decide +kernel
theorem ok_709_462_720 : ∀ t < 720, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_710 blk_709_462_710
theorem blk_709_462_720 : allRange (okAt f_709_462 709 462 1912) 720 10 = true := by decide +kernel
theorem ok_709_462_730 : ∀ t < 730, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_720 blk_709_462_720
theorem blk_709_462_730 : allRange (okAt f_709_462 709 462 1912) 730 10 = true := by decide +kernel
theorem ok_709_462_740 : ∀ t < 740, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_730 blk_709_462_730
theorem blk_709_462_740 : allRange (okAt f_709_462 709 462 1912) 740 10 = true := by decide +kernel
theorem ok_709_462_750 : ∀ t < 750, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_740 blk_709_462_740
theorem blk_709_462_750 : allRange (okAt f_709_462 709 462 1912) 750 10 = true := by decide +kernel
theorem ok_709_462_760 : ∀ t < 760, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_750 blk_709_462_750
theorem blk_709_462_760 : allRange (okAt f_709_462 709 462 1912) 760 10 = true := by decide +kernel
theorem ok_709_462_770 : ∀ t < 770, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_760 blk_709_462_760
theorem blk_709_462_770 : allRange (okAt f_709_462 709 462 1912) 770 10 = true := by decide +kernel
theorem ok_709_462_780 : ∀ t < 780, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_770 blk_709_462_770
theorem blk_709_462_780 : allRange (okAt f_709_462 709 462 1912) 780 10 = true := by decide +kernel
theorem ok_709_462_790 : ∀ t < 790, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_780 blk_709_462_780
theorem blk_709_462_790 : allRange (okAt f_709_462 709 462 1912) 790 10 = true := by decide +kernel
theorem ok_709_462_800 : ∀ t < 800, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_790 blk_709_462_790
theorem blk_709_462_800 : allRange (okAt f_709_462 709 462 1912) 800 10 = true := by decide +kernel
theorem ok_709_462_810 : ∀ t < 810, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_800 blk_709_462_800
theorem blk_709_462_810 : allRange (okAt f_709_462 709 462 1912) 810 10 = true := by decide +kernel
theorem ok_709_462_820 : ∀ t < 820, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_810 blk_709_462_810
theorem blk_709_462_820 : allRange (okAt f_709_462 709 462 1912) 820 10 = true := by decide +kernel
theorem ok_709_462_830 : ∀ t < 830, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_820 blk_709_462_820
theorem blk_709_462_830 : allRange (okAt f_709_462 709 462 1912) 830 10 = true := by decide +kernel
theorem ok_709_462_840 : ∀ t < 840, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_830 blk_709_462_830
theorem blk_709_462_840 : allRange (okAt f_709_462 709 462 1912) 840 10 = true := by decide +kernel
theorem ok_709_462_850 : ∀ t < 850, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_840 blk_709_462_840
theorem blk_709_462_850 : allRange (okAt f_709_462 709 462 1912) 850 10 = true := by decide +kernel
theorem ok_709_462_860 : ∀ t < 860, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_850 blk_709_462_850
theorem blk_709_462_860 : allRange (okAt f_709_462 709 462 1912) 860 10 = true := by decide +kernel
theorem ok_709_462_870 : ∀ t < 870, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_860 blk_709_462_860
theorem blk_709_462_870 : allRange (okAt f_709_462 709 462 1912) 870 10 = true := by decide +kernel
theorem ok_709_462_880 : ∀ t < 880, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_870 blk_709_462_870
theorem blk_709_462_880 : allRange (okAt f_709_462 709 462 1912) 880 10 = true := by decide +kernel
theorem ok_709_462_890 : ∀ t < 890, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_880 blk_709_462_880
theorem blk_709_462_890 : allRange (okAt f_709_462 709 462 1912) 890 10 = true := by decide +kernel
theorem ok_709_462_900 : ∀ t < 900, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_890 blk_709_462_890
theorem blk_709_462_900 : allRange (okAt f_709_462 709 462 1912) 900 10 = true := by decide +kernel
theorem ok_709_462_910 : ∀ t < 910, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_900 blk_709_462_900
theorem blk_709_462_910 : allRange (okAt f_709_462 709 462 1912) 910 10 = true := by decide +kernel
theorem ok_709_462_920 : ∀ t < 920, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_910 blk_709_462_910
theorem blk_709_462_920 : allRange (okAt f_709_462 709 462 1912) 920 10 = true := by decide +kernel
theorem ok_709_462_930 : ∀ t < 930, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_920 blk_709_462_920
theorem blk_709_462_930 : allRange (okAt f_709_462 709 462 1912) 930 10 = true := by decide +kernel
theorem ok_709_462_940 : ∀ t < 940, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_930 blk_709_462_930
theorem blk_709_462_940 : allRange (okAt f_709_462 709 462 1912) 940 10 = true := by decide +kernel
theorem ok_709_462_950 : ∀ t < 950, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_940 blk_709_462_940
theorem blk_709_462_950 : allRange (okAt f_709_462 709 462 1912) 950 10 = true := by decide +kernel
theorem ok_709_462_960 : ∀ t < 960, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_950 blk_709_462_950
theorem blk_709_462_960 : allRange (okAt f_709_462 709 462 1912) 960 10 = true := by decide +kernel
theorem ok_709_462_970 : ∀ t < 970, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_960 blk_709_462_960
theorem blk_709_462_970 : allRange (okAt f_709_462 709 462 1912) 970 10 = true := by decide +kernel
theorem ok_709_462_980 : ∀ t < 980, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_970 blk_709_462_970
theorem blk_709_462_980 : allRange (okAt f_709_462 709 462 1912) 980 10 = true := by decide +kernel
theorem ok_709_462_990 : ∀ t < 990, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_980 blk_709_462_980
theorem blk_709_462_990 : allRange (okAt f_709_462 709 462 1912) 990 10 = true := by decide +kernel
theorem ok_709_462_1000 : ∀ t < 1000, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_990 blk_709_462_990
theorem blk_709_462_1000 : allRange (okAt f_709_462 709 462 1912) 1000 10 = true := by decide +kernel
theorem ok_709_462_1010 : ∀ t < 1010, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1000 blk_709_462_1000
theorem blk_709_462_1010 : allRange (okAt f_709_462 709 462 1912) 1010 10 = true := by decide +kernel
theorem ok_709_462_1020 : ∀ t < 1020, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1010 blk_709_462_1010
theorem blk_709_462_1020 : allRange (okAt f_709_462 709 462 1912) 1020 10 = true := by decide +kernel
theorem ok_709_462_1030 : ∀ t < 1030, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1020 blk_709_462_1020
theorem blk_709_462_1030 : allRange (okAt f_709_462 709 462 1912) 1030 10 = true := by decide +kernel
theorem ok_709_462_1040 : ∀ t < 1040, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1030 blk_709_462_1030
theorem blk_709_462_1040 : allRange (okAt f_709_462 709 462 1912) 1040 10 = true := by decide +kernel
theorem ok_709_462_1050 : ∀ t < 1050, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1040 blk_709_462_1040
theorem blk_709_462_1050 : allRange (okAt f_709_462 709 462 1912) 1050 10 = true := by decide +kernel
theorem ok_709_462_1060 : ∀ t < 1060, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1050 blk_709_462_1050
theorem blk_709_462_1060 : allRange (okAt f_709_462 709 462 1912) 1060 10 = true := by decide +kernel
theorem ok_709_462_1070 : ∀ t < 1070, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1060 blk_709_462_1060
theorem blk_709_462_1070 : allRange (okAt f_709_462 709 462 1912) 1070 10 = true := by decide +kernel
theorem ok_709_462_1080 : ∀ t < 1080, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1070 blk_709_462_1070
theorem blk_709_462_1080 : allRange (okAt f_709_462 709 462 1912) 1080 10 = true := by decide +kernel
theorem ok_709_462_1090 : ∀ t < 1090, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1080 blk_709_462_1080
theorem blk_709_462_1090 : allRange (okAt f_709_462 709 462 1912) 1090 10 = true := by decide +kernel
theorem ok_709_462_1100 : ∀ t < 1100, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1090 blk_709_462_1090
theorem blk_709_462_1100 : allRange (okAt f_709_462 709 462 1912) 1100 10 = true := by decide +kernel
theorem ok_709_462_1110 : ∀ t < 1110, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1100 blk_709_462_1100
theorem blk_709_462_1110 : allRange (okAt f_709_462 709 462 1912) 1110 10 = true := by decide +kernel
theorem ok_709_462_1120 : ∀ t < 1120, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1110 blk_709_462_1110
theorem blk_709_462_1120 : allRange (okAt f_709_462 709 462 1912) 1120 10 = true := by decide +kernel
theorem ok_709_462_1130 : ∀ t < 1130, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1120 blk_709_462_1120
theorem blk_709_462_1130 : allRange (okAt f_709_462 709 462 1912) 1130 10 = true := by decide +kernel
theorem ok_709_462_1140 : ∀ t < 1140, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1130 blk_709_462_1130
theorem blk_709_462_1140 : allRange (okAt f_709_462 709 462 1912) 1140 10 = true := by decide +kernel
theorem ok_709_462_1150 : ∀ t < 1150, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1140 blk_709_462_1140
theorem blk_709_462_1150 : allRange (okAt f_709_462 709 462 1912) 1150 10 = true := by decide +kernel
theorem ok_709_462_1160 : ∀ t < 1160, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1150 blk_709_462_1150
theorem blk_709_462_1160 : allRange (okAt f_709_462 709 462 1912) 1160 10 = true := by decide +kernel
theorem ok_709_462_1170 : ∀ t < 1170, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1160 blk_709_462_1160
theorem blk_709_462_1170 : allRange (okAt f_709_462 709 462 1912) 1170 10 = true := by decide +kernel
theorem ok_709_462_1180 : ∀ t < 1180, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1170 blk_709_462_1170
theorem blk_709_462_1180 : allRange (okAt f_709_462 709 462 1912) 1180 10 = true := by decide +kernel
theorem ok_709_462_1190 : ∀ t < 1190, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1180 blk_709_462_1180
theorem blk_709_462_1190 : allRange (okAt f_709_462 709 462 1912) 1190 10 = true := by decide +kernel
theorem ok_709_462_1200 : ∀ t < 1200, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1190 blk_709_462_1190
theorem blk_709_462_1200 : allRange (okAt f_709_462 709 462 1912) 1200 10 = true := by decide +kernel
theorem ok_709_462_1210 : ∀ t < 1210, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1200 blk_709_462_1200
theorem blk_709_462_1210 : allRange (okAt f_709_462 709 462 1912) 1210 10 = true := by decide +kernel
theorem ok_709_462_1220 : ∀ t < 1220, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1210 blk_709_462_1210
theorem blk_709_462_1220 : allRange (okAt f_709_462 709 462 1912) 1220 10 = true := by decide +kernel
theorem ok_709_462_1230 : ∀ t < 1230, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1220 blk_709_462_1220
theorem blk_709_462_1230 : allRange (okAt f_709_462 709 462 1912) 1230 10 = true := by decide +kernel
theorem ok_709_462_1240 : ∀ t < 1240, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1230 blk_709_462_1230
theorem blk_709_462_1240 : allRange (okAt f_709_462 709 462 1912) 1240 10 = true := by decide +kernel
theorem ok_709_462_1250 : ∀ t < 1250, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1240 blk_709_462_1240
theorem blk_709_462_1250 : allRange (okAt f_709_462 709 462 1912) 1250 10 = true := by decide +kernel
theorem ok_709_462_1260 : ∀ t < 1260, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1250 blk_709_462_1250
theorem blk_709_462_1260 : allRange (okAt f_709_462 709 462 1912) 1260 10 = true := by decide +kernel
theorem ok_709_462_1270 : ∀ t < 1270, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1260 blk_709_462_1260
theorem blk_709_462_1270 : allRange (okAt f_709_462 709 462 1912) 1270 10 = true := by decide +kernel
theorem ok_709_462_1280 : ∀ t < 1280, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1270 blk_709_462_1270
theorem blk_709_462_1280 : allRange (okAt f_709_462 709 462 1912) 1280 10 = true := by decide +kernel
theorem ok_709_462_1290 : ∀ t < 1290, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1280 blk_709_462_1280
theorem blk_709_462_1290 : allRange (okAt f_709_462 709 462 1912) 1290 10 = true := by decide +kernel
theorem ok_709_462_1300 : ∀ t < 1300, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1290 blk_709_462_1290
theorem blk_709_462_1300 : allRange (okAt f_709_462 709 462 1912) 1300 10 = true := by decide +kernel
theorem ok_709_462_1310 : ∀ t < 1310, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1300 blk_709_462_1300
theorem blk_709_462_1310 : allRange (okAt f_709_462 709 462 1912) 1310 10 = true := by decide +kernel
theorem ok_709_462_1320 : ∀ t < 1320, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1310 blk_709_462_1310
theorem blk_709_462_1320 : allRange (okAt f_709_462 709 462 1912) 1320 10 = true := by decide +kernel
theorem ok_709_462_1330 : ∀ t < 1330, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1320 blk_709_462_1320
theorem blk_709_462_1330 : allRange (okAt f_709_462 709 462 1912) 1330 10 = true := by decide +kernel
theorem ok_709_462_1340 : ∀ t < 1340, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1330 blk_709_462_1330
theorem blk_709_462_1340 : allRange (okAt f_709_462 709 462 1912) 1340 10 = true := by decide +kernel
theorem ok_709_462_1350 : ∀ t < 1350, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1340 blk_709_462_1340
theorem blk_709_462_1350 : allRange (okAt f_709_462 709 462 1912) 1350 10 = true := by decide +kernel
theorem ok_709_462_1360 : ∀ t < 1360, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1350 blk_709_462_1350
theorem blk_709_462_1360 : allRange (okAt f_709_462 709 462 1912) 1360 10 = true := by decide +kernel
theorem ok_709_462_1370 : ∀ t < 1370, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1360 blk_709_462_1360
theorem blk_709_462_1370 : allRange (okAt f_709_462 709 462 1912) 1370 10 = true := by decide +kernel
theorem ok_709_462_1380 : ∀ t < 1380, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1370 blk_709_462_1370
theorem blk_709_462_1380 : allRange (okAt f_709_462 709 462 1912) 1380 10 = true := by decide +kernel
theorem ok_709_462_1390 : ∀ t < 1390, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1380 blk_709_462_1380
theorem blk_709_462_1390 : allRange (okAt f_709_462 709 462 1912) 1390 10 = true := by decide +kernel
theorem ok_709_462_1400 : ∀ t < 1400, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1390 blk_709_462_1390
theorem blk_709_462_1400 : allRange (okAt f_709_462 709 462 1912) 1400 10 = true := by decide +kernel
theorem ok_709_462_1410 : ∀ t < 1410, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1400 blk_709_462_1400
theorem blk_709_462_1410 : allRange (okAt f_709_462 709 462 1912) 1410 10 = true := by decide +kernel
theorem ok_709_462_1420 : ∀ t < 1420, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1410 blk_709_462_1410
theorem blk_709_462_1420 : allRange (okAt f_709_462 709 462 1912) 1420 10 = true := by decide +kernel
theorem ok_709_462_1430 : ∀ t < 1430, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1420 blk_709_462_1420
theorem blk_709_462_1430 : allRange (okAt f_709_462 709 462 1912) 1430 10 = true := by decide +kernel
theorem ok_709_462_1440 : ∀ t < 1440, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1430 blk_709_462_1430
theorem blk_709_462_1440 : allRange (okAt f_709_462 709 462 1912) 1440 10 = true := by decide +kernel
theorem ok_709_462_1450 : ∀ t < 1450, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1440 blk_709_462_1440
theorem blk_709_462_1450 : allRange (okAt f_709_462 709 462 1912) 1450 10 = true := by decide +kernel
theorem ok_709_462_1460 : ∀ t < 1460, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1450 blk_709_462_1450
theorem blk_709_462_1460 : allRange (okAt f_709_462 709 462 1912) 1460 10 = true := by decide +kernel
theorem ok_709_462_1470 : ∀ t < 1470, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1460 blk_709_462_1460
theorem blk_709_462_1470 : allRange (okAt f_709_462 709 462 1912) 1470 10 = true := by decide +kernel
theorem ok_709_462_1480 : ∀ t < 1480, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1470 blk_709_462_1470
theorem blk_709_462_1480 : allRange (okAt f_709_462 709 462 1912) 1480 10 = true := by decide +kernel
theorem ok_709_462_1490 : ∀ t < 1490, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1480 blk_709_462_1480
theorem blk_709_462_1490 : allRange (okAt f_709_462 709 462 1912) 1490 10 = true := by decide +kernel
theorem ok_709_462_1500 : ∀ t < 1500, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1490 blk_709_462_1490
theorem blk_709_462_1500 : allRange (okAt f_709_462 709 462 1912) 1500 10 = true := by decide +kernel
theorem ok_709_462_1510 : ∀ t < 1510, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1500 blk_709_462_1500
theorem blk_709_462_1510 : allRange (okAt f_709_462 709 462 1912) 1510 10 = true := by decide +kernel
theorem ok_709_462_1520 : ∀ t < 1520, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1510 blk_709_462_1510
theorem blk_709_462_1520 : allRange (okAt f_709_462 709 462 1912) 1520 10 = true := by decide +kernel
theorem ok_709_462_1530 : ∀ t < 1530, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1520 blk_709_462_1520
theorem blk_709_462_1530 : allRange (okAt f_709_462 709 462 1912) 1530 10 = true := by decide +kernel
theorem ok_709_462_1540 : ∀ t < 1540, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1530 blk_709_462_1530
theorem blk_709_462_1540 : allRange (okAt f_709_462 709 462 1912) 1540 10 = true := by decide +kernel
theorem ok_709_462_1550 : ∀ t < 1550, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1540 blk_709_462_1540
theorem blk_709_462_1550 : allRange (okAt f_709_462 709 462 1912) 1550 10 = true := by decide +kernel
theorem ok_709_462_1560 : ∀ t < 1560, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1550 blk_709_462_1550
theorem blk_709_462_1560 : allRange (okAt f_709_462 709 462 1912) 1560 10 = true := by decide +kernel
theorem ok_709_462_1570 : ∀ t < 1570, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1560 blk_709_462_1560
theorem blk_709_462_1570 : allRange (okAt f_709_462 709 462 1912) 1570 10 = true := by decide +kernel
theorem ok_709_462_1580 : ∀ t < 1580, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1570 blk_709_462_1570
theorem blk_709_462_1580 : allRange (okAt f_709_462 709 462 1912) 1580 10 = true := by decide +kernel
theorem ok_709_462_1590 : ∀ t < 1590, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1580 blk_709_462_1580
theorem blk_709_462_1590 : allRange (okAt f_709_462 709 462 1912) 1590 10 = true := by decide +kernel
theorem ok_709_462_1600 : ∀ t < 1600, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1590 blk_709_462_1590
theorem blk_709_462_1600 : allRange (okAt f_709_462 709 462 1912) 1600 10 = true := by decide +kernel
theorem ok_709_462_1610 : ∀ t < 1610, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1600 blk_709_462_1600
theorem blk_709_462_1610 : allRange (okAt f_709_462 709 462 1912) 1610 10 = true := by decide +kernel
theorem ok_709_462_1620 : ∀ t < 1620, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1610 blk_709_462_1610
theorem blk_709_462_1620 : allRange (okAt f_709_462 709 462 1912) 1620 10 = true := by decide +kernel
theorem ok_709_462_1630 : ∀ t < 1630, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1620 blk_709_462_1620
theorem blk_709_462_1630 : allRange (okAt f_709_462 709 462 1912) 1630 10 = true := by decide +kernel
theorem ok_709_462_1640 : ∀ t < 1640, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1630 blk_709_462_1630
theorem blk_709_462_1640 : allRange (okAt f_709_462 709 462 1912) 1640 10 = true := by decide +kernel
theorem ok_709_462_1650 : ∀ t < 1650, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1640 blk_709_462_1640
theorem blk_709_462_1650 : allRange (okAt f_709_462 709 462 1912) 1650 10 = true := by decide +kernel
theorem ok_709_462_1660 : ∀ t < 1660, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1650 blk_709_462_1650
theorem blk_709_462_1660 : allRange (okAt f_709_462 709 462 1912) 1660 10 = true := by decide +kernel
theorem ok_709_462_1670 : ∀ t < 1670, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1660 blk_709_462_1660
theorem blk_709_462_1670 : allRange (okAt f_709_462 709 462 1912) 1670 10 = true := by decide +kernel
theorem ok_709_462_1680 : ∀ t < 1680, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1670 blk_709_462_1670
theorem blk_709_462_1680 : allRange (okAt f_709_462 709 462 1912) 1680 10 = true := by decide +kernel
theorem ok_709_462_1690 : ∀ t < 1690, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1680 blk_709_462_1680
theorem blk_709_462_1690 : allRange (okAt f_709_462 709 462 1912) 1690 10 = true := by decide +kernel
theorem ok_709_462_1700 : ∀ t < 1700, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1690 blk_709_462_1690
theorem blk_709_462_1700 : allRange (okAt f_709_462 709 462 1912) 1700 10 = true := by decide +kernel
theorem ok_709_462_1710 : ∀ t < 1710, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1700 blk_709_462_1700
theorem blk_709_462_1710 : allRange (okAt f_709_462 709 462 1912) 1710 10 = true := by decide +kernel
theorem ok_709_462_1720 : ∀ t < 1720, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1710 blk_709_462_1710
theorem blk_709_462_1720 : allRange (okAt f_709_462 709 462 1912) 1720 10 = true := by decide +kernel
theorem ok_709_462_1730 : ∀ t < 1730, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1720 blk_709_462_1720
theorem blk_709_462_1730 : allRange (okAt f_709_462 709 462 1912) 1730 10 = true := by decide +kernel
theorem ok_709_462_1740 : ∀ t < 1740, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1730 blk_709_462_1730
theorem blk_709_462_1740 : allRange (okAt f_709_462 709 462 1912) 1740 10 = true := by decide +kernel
theorem ok_709_462_1750 : ∀ t < 1750, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1740 blk_709_462_1740
theorem blk_709_462_1750 : allRange (okAt f_709_462 709 462 1912) 1750 10 = true := by decide +kernel
theorem ok_709_462_1760 : ∀ t < 1760, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1750 blk_709_462_1750
theorem blk_709_462_1760 : allRange (okAt f_709_462 709 462 1912) 1760 10 = true := by decide +kernel
theorem ok_709_462_1770 : ∀ t < 1770, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1760 blk_709_462_1760
theorem blk_709_462_1770 : allRange (okAt f_709_462 709 462 1912) 1770 10 = true := by decide +kernel
theorem ok_709_462_1780 : ∀ t < 1780, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1770 blk_709_462_1770
theorem blk_709_462_1780 : allRange (okAt f_709_462 709 462 1912) 1780 10 = true := by decide +kernel
theorem ok_709_462_1790 : ∀ t < 1790, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1780 blk_709_462_1780
theorem blk_709_462_1790 : allRange (okAt f_709_462 709 462 1912) 1790 10 = true := by decide +kernel
theorem ok_709_462_1800 : ∀ t < 1800, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1790 blk_709_462_1790
theorem blk_709_462_1800 : allRange (okAt f_709_462 709 462 1912) 1800 10 = true := by decide +kernel
theorem ok_709_462_1810 : ∀ t < 1810, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1800 blk_709_462_1800
theorem blk_709_462_1810 : allRange (okAt f_709_462 709 462 1912) 1810 10 = true := by decide +kernel
theorem ok_709_462_1820 : ∀ t < 1820, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1810 blk_709_462_1810
theorem blk_709_462_1820 : allRange (okAt f_709_462 709 462 1912) 1820 10 = true := by decide +kernel
theorem ok_709_462_1830 : ∀ t < 1830, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1820 blk_709_462_1820
theorem blk_709_462_1830 : allRange (okAt f_709_462 709 462 1912) 1830 10 = true := by decide +kernel
theorem ok_709_462_1840 : ∀ t < 1840, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1830 blk_709_462_1830
theorem blk_709_462_1840 : allRange (okAt f_709_462 709 462 1912) 1840 10 = true := by decide +kernel
theorem ok_709_462_1850 : ∀ t < 1850, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1840 blk_709_462_1840
theorem blk_709_462_1850 : allRange (okAt f_709_462 709 462 1912) 1850 10 = true := by decide +kernel
theorem ok_709_462_1860 : ∀ t < 1860, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1850 blk_709_462_1850
theorem blk_709_462_1860 : allRange (okAt f_709_462 709 462 1912) 1860 10 = true := by decide +kernel
theorem ok_709_462_1870 : ∀ t < 1870, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1860 blk_709_462_1860
theorem blk_709_462_1870 : allRange (okAt f_709_462 709 462 1912) 1870 10 = true := by decide +kernel
theorem ok_709_462_1880 : ∀ t < 1880, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1870 blk_709_462_1870
theorem blk_709_462_1880 : allRange (okAt f_709_462 709 462 1912) 1880 10 = true := by decide +kernel
theorem ok_709_462_1890 : ∀ t < 1890, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1880 blk_709_462_1880
theorem blk_709_462_1890 : allRange (okAt f_709_462 709 462 1912) 1890 10 = true := by decide +kernel
theorem ok_709_462_1900 : ∀ t < 1900, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1890 blk_709_462_1890
theorem blk_709_462_1900 : allRange (okAt f_709_462 709 462 1912) 1900 10 = true := by decide +kernel
theorem ok_709_462_1910 : ∀ t < 1910, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1900 blk_709_462_1900
theorem blk_709_462_1910 : allRange (okAt f_709_462 709 462 1912) 1910 2 = true := by decide +kernel
theorem ok_709_462_1912 : ∀ t < 1912, okAt f_709_462 709 462 1912 t = true := allRange_extend ok_709_462_1910 blk_709_462_1910

theorem coil_709_462 : ∃ v : ℕ → Fin 709 → Bool, IsCoil 462 1912 v :=
  exists_coil_of_check f_709_462 462 1912 (by norm_num) ok_709_462_1912 (by decide +kernel)

/-- K(709,462) = 1912  (= 4k+2l+2, l = 31; code: ofam_709_462_1912.txt) -/
theorem K_709_462 : IsMaxLength 709 462 1912 :=
  isMaxLength_of_chord coil_709_462 (by norm_num) 925 (by norm_num) (by norm_num) (by decide +kernel)


end Coil
