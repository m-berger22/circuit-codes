import Ccformal.Checker

namespace Coil

def W_703_448 : ℕ := 0x2be01f001be02bd01ea02bc01d602bb01b802ba01d302b901d102b801e801b102b701e202b601cb02b501ab02b401c802b301c602b201e001a402b101da02b001c002af019e02ae01bc02ad01ba02ac01d8019702ab01cf02aa01b302a9019102a801af02a701ad02a601cd018a02a501c402a401a602a3018402a201a202a101a002a001c2017d029f01b7029e0199029d0177029c0195029b0193029a01b50170029901aa0298018c0297016a0296018802950186029401a801630293019d0292017f0291015d0290017b028f0179028e019b0156028d0190028c0172028b0150028a016e0289016c0288018e0149028701830286016502850143028401610283015f02820181013c0281017602800158027f0136027e0154027d0152027c0174012f027b0169027a014b0279012902780147027701450276016701220275015c0274013e0273011c0272013a027101380270015a0115026f014f026e0131026d010f026c012d026b012b026a014d0108026901420268012402670102026601200265011e0264014000fb0263013502620117026100f502600113025f0111025e013300ee025d0128025c010a025b00e8025a0106025901040258012600e10257011b025600fd025500db025400f9025300f70252011900d40251010e025000f0024f00ce024e00ec024d00ea024c010c00c7024b0101024a00e3024900c1024800df024700dd024600ff00ba024500f4024400d6024300b4024200d2024100d0024000f200ad023f00e7023e00c9023d00a7023c00c5023b00c3023a00e500a0023900da023800bc0237009a023600b8023500b6023400d80093023300cd023200af0231008d023000ab022f00a9022e00cb0086022d00c0022c00a2022b0080022a009e0229009c022800be0079022700b30226009502250073022400910223008f022200b1006c022100a602200088021f0066021e0084021d0082021c00a4005f021b0099021a007b0219005902180077021700750216009700520215008c0214006e0213004c0212006a021100680210008a0045020f007f020e0061020d003f020c005d020b005b020a007d0038020900720208005402070032020600500205004e02040070002b0203006502020047020100250200004301ff004101fe0063001e01fd005801fc003a01fb001801fa003601f9003401f80056001101f7004b01f6002d01f5000b01f4002901f3002701f20049000401f1003e01ef002001ee01f001ed001c01ec001a01eb003c01b801e9003101e7001301e601e801e5000f01e4000d01e3002f01ab01e1002401df000601de01e001dd000201dc000001db0022019e01d9001701d701d601d501d801d401d301d201d101d00015019101ce000a01cc01cb01ca01cd01c901c801c701c601c50008018401c301be01c101c001bf01c201bd01bc01bb01ba01b901ea017701b601b101b401b301b201b501b001af01ae01ad01ac01e2016a01a901a401a701a601a501a801a301a201a101a0019f01da015d019c0197019a01990198019b0196019501940193019201cf0150018f018a018d018c018b018e0189018801870186018501c401430182017d0180017f017e0181017c017b017a0179017801b70136017501700173017201710174016f016e016d016c016b01aa0129016801630166016501640167016201610160015f015e019d011c015b0156015901580157015a015501540153015201510190010f014e0149014c014b014a014d01480147014601450144018301020141013c013f013e013d0140013b013a013901380137017600f50134012f0132013101300133012e012d012c012b012a016900e801270122012501240123012601210120011f011e011d015c00db011a0115011801170116011901140113011201110110014f00ce010d0108010b010a0109010c01070106010501040103014200c1010000fb00fe00fd00fc00ff00fa00f900f800f700f6013500b400f300ee00f100f000ef00f200ed00ec00eb00ea00e9012800a700e600e100e400e300e200e500e000df00de00dd00dc011b009a00d900d400d700d600d500d800d300d200d100d000cf010e008d00cc00c700ca00c900c800cb00c600c500c400c300c20101008000bf00ba00bd00bc00bb00be00b900b800b700b600b500f4007300b200ad00b000af00ae00b100ac00ab00aa00a900a800e7006600a500a000a300a200a100a4009f009e009d009c009b00da0059009800930096009500940097009200910090008f008e00cd004c008b0086008900880087008a0085008400830082008100c0003f007e0079007c007b007a007d0078007700760075007400b300320071006c006f006e006d0070006b006a00690068006700a600250064005f0062006100600063005e005d005c005b005a0099001800570052005500540053005600510050004f004e004d008c000b004a0045004800470046004900440043004200410040007f01f0003d0038003b003a0039003c00370036003500340033007201e80030002b002e002d002c002f002a0029002800270026006501e00023001e00210020001f0022001d001c001b001a0019005801d80016001100140013001200150010000f000e000d000c004b01cd000900040007000600050008000300020001000002be003e01c202bd01b802bc01d602bb01ea02ba01d302b901d102b8003101b502b701ab02b601cb02b501e202b401c802b301c602b2002401a802b1019e02b001c002af01da02ae01bc02ad01ba02ac0017019b02ab019102aa01b302a901cf02a801af02a701ad02a6000a018e02a5018402a401a602a301c402a201a202a101a002a001be0181029f0177029e0199029d01b7029c0195029b0193029a01b101740299016a0298018c029701aa0296018802950186029401a401670293015d0292017f0291019d0290017b028f0179028e0197015a028d0150028c0172028b0190028a016e0289016c0288018a014d028701430286016502850183028401610283015f0282017d01400281013602800158027f0176027e0154027d0152027c01700133027b0129027a014b0279016902780147027701450276016301260275011c0274013e0273015c0272013a02710138027001560119026f010f026e0131026d014f026c012d026b012b026a0149010c026901020268012402670142026601200265011e0264013c00ff026300f5026201170261013502600113025f0111025e012f00f2025d00e8025c010a025b0128025a0106025901040258012200e5025700db025600fd0255011b025400f9025300f70252011500d8025100ce025000f0024f010e024e00ec024d00ea024c010800cb024b00c1024a00e302490101024800df024700dd024600fb00be024500b4024400d6024300f4024200d2024100d0024000ee00b1023f00a7023e00c9023d00e7023c00c5023b00c3023a00e100a40239009a023800bc023700da023600b8023500b6023400d400970233008d023200af023100cd023000ab022f00a9022e00c7008a022d0080022c00a2022b00c0022a009e0229009c022800ba007d0227007302260095022500b3022400910223008f022200ad00700221006602200088021f00a6021e0084021d0082021c00a00063021b0059021a007b0219009902180077021700750216009300560215004c0214006e0213008c0212006a02110068021000860049020f003f020e0061020d007f020c005d020b005b020a0079003c020900320208005402070072020600500205004e0204006c002f0203002502020047020100650200004301ff004101fe005f002201fd001801fc003a01fb005801fa003601f9003401f80052001501f7000b01f6002d01f5004b01f4002901f3002701f20045000801f101f001ef002001ee003e01ed001c01ec001a01eb003801ea01e901e801e7001301e6003101e5000f01e4000d01e3002b01e201e101e001df000601de002401dd000201dc000001db001e01da01d901d801d701d601d5001701d401d301d201d101d0001101cf01ce01cd01cc01cb01ca000a01c901c801c701c601c5000401c401c301c201c101c001bf01be01bd01bc01bb01ba01b901b801b701b601b501b401b301b201b101b001af01ae01ad01ac01ab01aa01a901a801a701a601a501a401a301a201a101a0019f019e019d019c019b019a0199019801970196019501940193019201910190018f018e018d018c018b018a0189018801870186018501840183018201810180017f017e017d017c017b017a0179017801770176017501740173017201710170016f016e016d016c016b016a0169016801670166016501640163016201610160015f015e015d015c015b015a0159015801570156015501540153015201510150014f014e014d014c014b014a0149014801470146014501440143014201410140013f013e013d013c013b013a0139013801370136013501340133013201310130012f012e012d012c012b012a0129012801270126012501240123012201210120011f011e011d011c011b011a0119011801170116011501140113011201110110010f010e010d010c010b010a010901080107010601050104010301020101010000ff00fe00fd00fc00fb00fa00f900f800f700f600f500f400f300f200f100f000ef00ee00ed00ec00eb00ea00e900e800e700e600e500e400e300e200e100e000df00de00dd00dc00db00da00d900d800d700d600d500d400d300d200d100d000cf00ce00cd00cc00cb00ca00c900c800c700c600c500c400c300c200c100c000bf00be00bd00bc00bb00ba00b900b800b700b600b500b400b300b200b100b000af00ae00ad00ac00ab00aa00a900a800a700a600a500a400a300a200a100a0009f009e009d009c009b009a0099009800970096009500940093009200910090008f008e008d008c008b008a0089008800870086008500840083008200810080007f007e007d007c007b007a0079007800770076007500740073007200710070006f006e006d006c006b006a0069006800670066006500640063006200610060005f005e005d005c005b005a0059005800570056005500540053005200510050004f004e004d004c004b004a0049004800470046004500440043004200410040003f003e003d003c003b003a0039003800370036003500340033003200310030002f002e002d002c002b002a0029002800270026002500240023002200210020001f001e001d001c001b001a0019001800170016001500140013001200110010000f000e000d000c000b000a0009000800070006000500040003000200010000

def f_703_448 (i : ℕ) : ℕ := (W_703_448 >>> (16 * i)) &&& 0xFFFF

theorem ok_703_448_0 : ∀ t < 0, okAt f_703_448 703 448 1924 t = true := allRange_zero

theorem blk_703_448_0 : allRange (okAt f_703_448 703 448 1924) 0 10 = true := by decide +kernel
theorem ok_703_448_10 : ∀ t < 10, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_0 blk_703_448_0
theorem blk_703_448_10 : allRange (okAt f_703_448 703 448 1924) 10 10 = true := by decide +kernel
theorem ok_703_448_20 : ∀ t < 20, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_10 blk_703_448_10
theorem blk_703_448_20 : allRange (okAt f_703_448 703 448 1924) 20 10 = true := by decide +kernel
theorem ok_703_448_30 : ∀ t < 30, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_20 blk_703_448_20
theorem blk_703_448_30 : allRange (okAt f_703_448 703 448 1924) 30 10 = true := by decide +kernel
theorem ok_703_448_40 : ∀ t < 40, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_30 blk_703_448_30
theorem blk_703_448_40 : allRange (okAt f_703_448 703 448 1924) 40 10 = true := by decide +kernel
theorem ok_703_448_50 : ∀ t < 50, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_40 blk_703_448_40
theorem blk_703_448_50 : allRange (okAt f_703_448 703 448 1924) 50 10 = true := by decide +kernel
theorem ok_703_448_60 : ∀ t < 60, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_50 blk_703_448_50
theorem blk_703_448_60 : allRange (okAt f_703_448 703 448 1924) 60 10 = true := by decide +kernel
theorem ok_703_448_70 : ∀ t < 70, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_60 blk_703_448_60
theorem blk_703_448_70 : allRange (okAt f_703_448 703 448 1924) 70 10 = true := by decide +kernel
theorem ok_703_448_80 : ∀ t < 80, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_70 blk_703_448_70
theorem blk_703_448_80 : allRange (okAt f_703_448 703 448 1924) 80 10 = true := by decide +kernel
theorem ok_703_448_90 : ∀ t < 90, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_80 blk_703_448_80
theorem blk_703_448_90 : allRange (okAt f_703_448 703 448 1924) 90 10 = true := by decide +kernel
theorem ok_703_448_100 : ∀ t < 100, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_90 blk_703_448_90
theorem blk_703_448_100 : allRange (okAt f_703_448 703 448 1924) 100 10 = true := by decide +kernel
theorem ok_703_448_110 : ∀ t < 110, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_100 blk_703_448_100
theorem blk_703_448_110 : allRange (okAt f_703_448 703 448 1924) 110 10 = true := by decide +kernel
theorem ok_703_448_120 : ∀ t < 120, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_110 blk_703_448_110
theorem blk_703_448_120 : allRange (okAt f_703_448 703 448 1924) 120 10 = true := by decide +kernel
theorem ok_703_448_130 : ∀ t < 130, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_120 blk_703_448_120
theorem blk_703_448_130 : allRange (okAt f_703_448 703 448 1924) 130 10 = true := by decide +kernel
theorem ok_703_448_140 : ∀ t < 140, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_130 blk_703_448_130
theorem blk_703_448_140 : allRange (okAt f_703_448 703 448 1924) 140 10 = true := by decide +kernel
theorem ok_703_448_150 : ∀ t < 150, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_140 blk_703_448_140
theorem blk_703_448_150 : allRange (okAt f_703_448 703 448 1924) 150 10 = true := by decide +kernel
theorem ok_703_448_160 : ∀ t < 160, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_150 blk_703_448_150
theorem blk_703_448_160 : allRange (okAt f_703_448 703 448 1924) 160 10 = true := by decide +kernel
theorem ok_703_448_170 : ∀ t < 170, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_160 blk_703_448_160
theorem blk_703_448_170 : allRange (okAt f_703_448 703 448 1924) 170 10 = true := by decide +kernel
theorem ok_703_448_180 : ∀ t < 180, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_170 blk_703_448_170
theorem blk_703_448_180 : allRange (okAt f_703_448 703 448 1924) 180 10 = true := by decide +kernel
theorem ok_703_448_190 : ∀ t < 190, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_180 blk_703_448_180
theorem blk_703_448_190 : allRange (okAt f_703_448 703 448 1924) 190 10 = true := by decide +kernel
theorem ok_703_448_200 : ∀ t < 200, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_190 blk_703_448_190
theorem blk_703_448_200 : allRange (okAt f_703_448 703 448 1924) 200 10 = true := by decide +kernel
theorem ok_703_448_210 : ∀ t < 210, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_200 blk_703_448_200
theorem blk_703_448_210 : allRange (okAt f_703_448 703 448 1924) 210 10 = true := by decide +kernel
theorem ok_703_448_220 : ∀ t < 220, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_210 blk_703_448_210
theorem blk_703_448_220 : allRange (okAt f_703_448 703 448 1924) 220 10 = true := by decide +kernel
theorem ok_703_448_230 : ∀ t < 230, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_220 blk_703_448_220
theorem blk_703_448_230 : allRange (okAt f_703_448 703 448 1924) 230 10 = true := by decide +kernel
theorem ok_703_448_240 : ∀ t < 240, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_230 blk_703_448_230
theorem blk_703_448_240 : allRange (okAt f_703_448 703 448 1924) 240 10 = true := by decide +kernel
theorem ok_703_448_250 : ∀ t < 250, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_240 blk_703_448_240
theorem blk_703_448_250 : allRange (okAt f_703_448 703 448 1924) 250 10 = true := by decide +kernel
theorem ok_703_448_260 : ∀ t < 260, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_250 blk_703_448_250
theorem blk_703_448_260 : allRange (okAt f_703_448 703 448 1924) 260 10 = true := by decide +kernel
theorem ok_703_448_270 : ∀ t < 270, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_260 blk_703_448_260
theorem blk_703_448_270 : allRange (okAt f_703_448 703 448 1924) 270 10 = true := by decide +kernel
theorem ok_703_448_280 : ∀ t < 280, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_270 blk_703_448_270
theorem blk_703_448_280 : allRange (okAt f_703_448 703 448 1924) 280 10 = true := by decide +kernel
theorem ok_703_448_290 : ∀ t < 290, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_280 blk_703_448_280
theorem blk_703_448_290 : allRange (okAt f_703_448 703 448 1924) 290 10 = true := by decide +kernel
theorem ok_703_448_300 : ∀ t < 300, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_290 blk_703_448_290
theorem blk_703_448_300 : allRange (okAt f_703_448 703 448 1924) 300 10 = true := by decide +kernel
theorem ok_703_448_310 : ∀ t < 310, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_300 blk_703_448_300
theorem blk_703_448_310 : allRange (okAt f_703_448 703 448 1924) 310 10 = true := by decide +kernel
theorem ok_703_448_320 : ∀ t < 320, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_310 blk_703_448_310
theorem blk_703_448_320 : allRange (okAt f_703_448 703 448 1924) 320 10 = true := by decide +kernel
theorem ok_703_448_330 : ∀ t < 330, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_320 blk_703_448_320
theorem blk_703_448_330 : allRange (okAt f_703_448 703 448 1924) 330 10 = true := by decide +kernel
theorem ok_703_448_340 : ∀ t < 340, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_330 blk_703_448_330
theorem blk_703_448_340 : allRange (okAt f_703_448 703 448 1924) 340 10 = true := by decide +kernel
theorem ok_703_448_350 : ∀ t < 350, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_340 blk_703_448_340
theorem blk_703_448_350 : allRange (okAt f_703_448 703 448 1924) 350 10 = true := by decide +kernel
theorem ok_703_448_360 : ∀ t < 360, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_350 blk_703_448_350
theorem blk_703_448_360 : allRange (okAt f_703_448 703 448 1924) 360 10 = true := by decide +kernel
theorem ok_703_448_370 : ∀ t < 370, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_360 blk_703_448_360
theorem blk_703_448_370 : allRange (okAt f_703_448 703 448 1924) 370 10 = true := by decide +kernel
theorem ok_703_448_380 : ∀ t < 380, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_370 blk_703_448_370
theorem blk_703_448_380 : allRange (okAt f_703_448 703 448 1924) 380 10 = true := by decide +kernel
theorem ok_703_448_390 : ∀ t < 390, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_380 blk_703_448_380
theorem blk_703_448_390 : allRange (okAt f_703_448 703 448 1924) 390 10 = true := by decide +kernel
theorem ok_703_448_400 : ∀ t < 400, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_390 blk_703_448_390
theorem blk_703_448_400 : allRange (okAt f_703_448 703 448 1924) 400 10 = true := by decide +kernel
theorem ok_703_448_410 : ∀ t < 410, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_400 blk_703_448_400
theorem blk_703_448_410 : allRange (okAt f_703_448 703 448 1924) 410 10 = true := by decide +kernel
theorem ok_703_448_420 : ∀ t < 420, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_410 blk_703_448_410
theorem blk_703_448_420 : allRange (okAt f_703_448 703 448 1924) 420 10 = true := by decide +kernel
theorem ok_703_448_430 : ∀ t < 430, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_420 blk_703_448_420
theorem blk_703_448_430 : allRange (okAt f_703_448 703 448 1924) 430 10 = true := by decide +kernel
theorem ok_703_448_440 : ∀ t < 440, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_430 blk_703_448_430
theorem blk_703_448_440 : allRange (okAt f_703_448 703 448 1924) 440 10 = true := by decide +kernel
theorem ok_703_448_450 : ∀ t < 450, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_440 blk_703_448_440
theorem blk_703_448_450 : allRange (okAt f_703_448 703 448 1924) 450 10 = true := by decide +kernel
theorem ok_703_448_460 : ∀ t < 460, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_450 blk_703_448_450
theorem blk_703_448_460 : allRange (okAt f_703_448 703 448 1924) 460 10 = true := by decide +kernel
theorem ok_703_448_470 : ∀ t < 470, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_460 blk_703_448_460
theorem blk_703_448_470 : allRange (okAt f_703_448 703 448 1924) 470 10 = true := by decide +kernel
theorem ok_703_448_480 : ∀ t < 480, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_470 blk_703_448_470
theorem blk_703_448_480 : allRange (okAt f_703_448 703 448 1924) 480 10 = true := by decide +kernel
theorem ok_703_448_490 : ∀ t < 490, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_480 blk_703_448_480
theorem blk_703_448_490 : allRange (okAt f_703_448 703 448 1924) 490 10 = true := by decide +kernel
theorem ok_703_448_500 : ∀ t < 500, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_490 blk_703_448_490
theorem blk_703_448_500 : allRange (okAt f_703_448 703 448 1924) 500 10 = true := by decide +kernel
theorem ok_703_448_510 : ∀ t < 510, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_500 blk_703_448_500
theorem blk_703_448_510 : allRange (okAt f_703_448 703 448 1924) 510 10 = true := by decide +kernel
theorem ok_703_448_520 : ∀ t < 520, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_510 blk_703_448_510
theorem blk_703_448_520 : allRange (okAt f_703_448 703 448 1924) 520 10 = true := by decide +kernel
theorem ok_703_448_530 : ∀ t < 530, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_520 blk_703_448_520
theorem blk_703_448_530 : allRange (okAt f_703_448 703 448 1924) 530 10 = true := by decide +kernel
theorem ok_703_448_540 : ∀ t < 540, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_530 blk_703_448_530
theorem blk_703_448_540 : allRange (okAt f_703_448 703 448 1924) 540 10 = true := by decide +kernel
theorem ok_703_448_550 : ∀ t < 550, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_540 blk_703_448_540
theorem blk_703_448_550 : allRange (okAt f_703_448 703 448 1924) 550 10 = true := by decide +kernel
theorem ok_703_448_560 : ∀ t < 560, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_550 blk_703_448_550
theorem blk_703_448_560 : allRange (okAt f_703_448 703 448 1924) 560 10 = true := by decide +kernel
theorem ok_703_448_570 : ∀ t < 570, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_560 blk_703_448_560
theorem blk_703_448_570 : allRange (okAt f_703_448 703 448 1924) 570 10 = true := by decide +kernel
theorem ok_703_448_580 : ∀ t < 580, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_570 blk_703_448_570
theorem blk_703_448_580 : allRange (okAt f_703_448 703 448 1924) 580 10 = true := by decide +kernel
theorem ok_703_448_590 : ∀ t < 590, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_580 blk_703_448_580
theorem blk_703_448_590 : allRange (okAt f_703_448 703 448 1924) 590 10 = true := by decide +kernel
theorem ok_703_448_600 : ∀ t < 600, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_590 blk_703_448_590
theorem blk_703_448_600 : allRange (okAt f_703_448 703 448 1924) 600 10 = true := by decide +kernel
theorem ok_703_448_610 : ∀ t < 610, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_600 blk_703_448_600
theorem blk_703_448_610 : allRange (okAt f_703_448 703 448 1924) 610 10 = true := by decide +kernel
theorem ok_703_448_620 : ∀ t < 620, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_610 blk_703_448_610
theorem blk_703_448_620 : allRange (okAt f_703_448 703 448 1924) 620 10 = true := by decide +kernel
theorem ok_703_448_630 : ∀ t < 630, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_620 blk_703_448_620
theorem blk_703_448_630 : allRange (okAt f_703_448 703 448 1924) 630 10 = true := by decide +kernel
theorem ok_703_448_640 : ∀ t < 640, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_630 blk_703_448_630
theorem blk_703_448_640 : allRange (okAt f_703_448 703 448 1924) 640 10 = true := by decide +kernel
theorem ok_703_448_650 : ∀ t < 650, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_640 blk_703_448_640
theorem blk_703_448_650 : allRange (okAt f_703_448 703 448 1924) 650 10 = true := by decide +kernel
theorem ok_703_448_660 : ∀ t < 660, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_650 blk_703_448_650
theorem blk_703_448_660 : allRange (okAt f_703_448 703 448 1924) 660 10 = true := by decide +kernel
theorem ok_703_448_670 : ∀ t < 670, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_660 blk_703_448_660
theorem blk_703_448_670 : allRange (okAt f_703_448 703 448 1924) 670 10 = true := by decide +kernel
theorem ok_703_448_680 : ∀ t < 680, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_670 blk_703_448_670
theorem blk_703_448_680 : allRange (okAt f_703_448 703 448 1924) 680 10 = true := by decide +kernel
theorem ok_703_448_690 : ∀ t < 690, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_680 blk_703_448_680
theorem blk_703_448_690 : allRange (okAt f_703_448 703 448 1924) 690 10 = true := by decide +kernel
theorem ok_703_448_700 : ∀ t < 700, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_690 blk_703_448_690
theorem blk_703_448_700 : allRange (okAt f_703_448 703 448 1924) 700 10 = true := by decide +kernel
theorem ok_703_448_710 : ∀ t < 710, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_700 blk_703_448_700
theorem blk_703_448_710 : allRange (okAt f_703_448 703 448 1924) 710 10 = true := by decide +kernel
theorem ok_703_448_720 : ∀ t < 720, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_710 blk_703_448_710
theorem blk_703_448_720 : allRange (okAt f_703_448 703 448 1924) 720 10 = true := by decide +kernel
theorem ok_703_448_730 : ∀ t < 730, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_720 blk_703_448_720
theorem blk_703_448_730 : allRange (okAt f_703_448 703 448 1924) 730 10 = true := by decide +kernel
theorem ok_703_448_740 : ∀ t < 740, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_730 blk_703_448_730
theorem blk_703_448_740 : allRange (okAt f_703_448 703 448 1924) 740 10 = true := by decide +kernel
theorem ok_703_448_750 : ∀ t < 750, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_740 blk_703_448_740
theorem blk_703_448_750 : allRange (okAt f_703_448 703 448 1924) 750 10 = true := by decide +kernel
theorem ok_703_448_760 : ∀ t < 760, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_750 blk_703_448_750
theorem blk_703_448_760 : allRange (okAt f_703_448 703 448 1924) 760 10 = true := by decide +kernel
theorem ok_703_448_770 : ∀ t < 770, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_760 blk_703_448_760
theorem blk_703_448_770 : allRange (okAt f_703_448 703 448 1924) 770 10 = true := by decide +kernel
theorem ok_703_448_780 : ∀ t < 780, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_770 blk_703_448_770
theorem blk_703_448_780 : allRange (okAt f_703_448 703 448 1924) 780 10 = true := by decide +kernel
theorem ok_703_448_790 : ∀ t < 790, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_780 blk_703_448_780
theorem blk_703_448_790 : allRange (okAt f_703_448 703 448 1924) 790 10 = true := by decide +kernel
theorem ok_703_448_800 : ∀ t < 800, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_790 blk_703_448_790
theorem blk_703_448_800 : allRange (okAt f_703_448 703 448 1924) 800 10 = true := by decide +kernel
theorem ok_703_448_810 : ∀ t < 810, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_800 blk_703_448_800
theorem blk_703_448_810 : allRange (okAt f_703_448 703 448 1924) 810 10 = true := by decide +kernel
theorem ok_703_448_820 : ∀ t < 820, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_810 blk_703_448_810
theorem blk_703_448_820 : allRange (okAt f_703_448 703 448 1924) 820 10 = true := by decide +kernel
theorem ok_703_448_830 : ∀ t < 830, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_820 blk_703_448_820
theorem blk_703_448_830 : allRange (okAt f_703_448 703 448 1924) 830 10 = true := by decide +kernel
theorem ok_703_448_840 : ∀ t < 840, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_830 blk_703_448_830
theorem blk_703_448_840 : allRange (okAt f_703_448 703 448 1924) 840 10 = true := by decide +kernel
theorem ok_703_448_850 : ∀ t < 850, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_840 blk_703_448_840
theorem blk_703_448_850 : allRange (okAt f_703_448 703 448 1924) 850 10 = true := by decide +kernel
theorem ok_703_448_860 : ∀ t < 860, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_850 blk_703_448_850
theorem blk_703_448_860 : allRange (okAt f_703_448 703 448 1924) 860 10 = true := by decide +kernel
theorem ok_703_448_870 : ∀ t < 870, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_860 blk_703_448_860
theorem blk_703_448_870 : allRange (okAt f_703_448 703 448 1924) 870 10 = true := by decide +kernel
theorem ok_703_448_880 : ∀ t < 880, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_870 blk_703_448_870
theorem blk_703_448_880 : allRange (okAt f_703_448 703 448 1924) 880 10 = true := by decide +kernel
theorem ok_703_448_890 : ∀ t < 890, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_880 blk_703_448_880
theorem blk_703_448_890 : allRange (okAt f_703_448 703 448 1924) 890 10 = true := by decide +kernel
theorem ok_703_448_900 : ∀ t < 900, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_890 blk_703_448_890
theorem blk_703_448_900 : allRange (okAt f_703_448 703 448 1924) 900 10 = true := by decide +kernel
theorem ok_703_448_910 : ∀ t < 910, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_900 blk_703_448_900
theorem blk_703_448_910 : allRange (okAt f_703_448 703 448 1924) 910 10 = true := by decide +kernel
theorem ok_703_448_920 : ∀ t < 920, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_910 blk_703_448_910
theorem blk_703_448_920 : allRange (okAt f_703_448 703 448 1924) 920 10 = true := by decide +kernel
theorem ok_703_448_930 : ∀ t < 930, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_920 blk_703_448_920
theorem blk_703_448_930 : allRange (okAt f_703_448 703 448 1924) 930 10 = true := by decide +kernel
theorem ok_703_448_940 : ∀ t < 940, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_930 blk_703_448_930
theorem blk_703_448_940 : allRange (okAt f_703_448 703 448 1924) 940 10 = true := by decide +kernel
theorem ok_703_448_950 : ∀ t < 950, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_940 blk_703_448_940
theorem blk_703_448_950 : allRange (okAt f_703_448 703 448 1924) 950 10 = true := by decide +kernel
theorem ok_703_448_960 : ∀ t < 960, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_950 blk_703_448_950
theorem blk_703_448_960 : allRange (okAt f_703_448 703 448 1924) 960 10 = true := by decide +kernel
theorem ok_703_448_970 : ∀ t < 970, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_960 blk_703_448_960
theorem blk_703_448_970 : allRange (okAt f_703_448 703 448 1924) 970 10 = true := by decide +kernel
theorem ok_703_448_980 : ∀ t < 980, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_970 blk_703_448_970
theorem blk_703_448_980 : allRange (okAt f_703_448 703 448 1924) 980 10 = true := by decide +kernel
theorem ok_703_448_990 : ∀ t < 990, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_980 blk_703_448_980
theorem blk_703_448_990 : allRange (okAt f_703_448 703 448 1924) 990 10 = true := by decide +kernel
theorem ok_703_448_1000 : ∀ t < 1000, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_990 blk_703_448_990
theorem blk_703_448_1000 : allRange (okAt f_703_448 703 448 1924) 1000 10 = true := by decide +kernel
theorem ok_703_448_1010 : ∀ t < 1010, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1000 blk_703_448_1000
theorem blk_703_448_1010 : allRange (okAt f_703_448 703 448 1924) 1010 10 = true := by decide +kernel
theorem ok_703_448_1020 : ∀ t < 1020, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1010 blk_703_448_1010
theorem blk_703_448_1020 : allRange (okAt f_703_448 703 448 1924) 1020 10 = true := by decide +kernel
theorem ok_703_448_1030 : ∀ t < 1030, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1020 blk_703_448_1020
theorem blk_703_448_1030 : allRange (okAt f_703_448 703 448 1924) 1030 10 = true := by decide +kernel
theorem ok_703_448_1040 : ∀ t < 1040, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1030 blk_703_448_1030
theorem blk_703_448_1040 : allRange (okAt f_703_448 703 448 1924) 1040 10 = true := by decide +kernel
theorem ok_703_448_1050 : ∀ t < 1050, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1040 blk_703_448_1040
theorem blk_703_448_1050 : allRange (okAt f_703_448 703 448 1924) 1050 10 = true := by decide +kernel
theorem ok_703_448_1060 : ∀ t < 1060, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1050 blk_703_448_1050
theorem blk_703_448_1060 : allRange (okAt f_703_448 703 448 1924) 1060 10 = true := by decide +kernel
theorem ok_703_448_1070 : ∀ t < 1070, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1060 blk_703_448_1060
theorem blk_703_448_1070 : allRange (okAt f_703_448 703 448 1924) 1070 10 = true := by decide +kernel
theorem ok_703_448_1080 : ∀ t < 1080, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1070 blk_703_448_1070
theorem blk_703_448_1080 : allRange (okAt f_703_448 703 448 1924) 1080 10 = true := by decide +kernel
theorem ok_703_448_1090 : ∀ t < 1090, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1080 blk_703_448_1080
theorem blk_703_448_1090 : allRange (okAt f_703_448 703 448 1924) 1090 10 = true := by decide +kernel
theorem ok_703_448_1100 : ∀ t < 1100, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1090 blk_703_448_1090
theorem blk_703_448_1100 : allRange (okAt f_703_448 703 448 1924) 1100 10 = true := by decide +kernel
theorem ok_703_448_1110 : ∀ t < 1110, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1100 blk_703_448_1100
theorem blk_703_448_1110 : allRange (okAt f_703_448 703 448 1924) 1110 10 = true := by decide +kernel
theorem ok_703_448_1120 : ∀ t < 1120, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1110 blk_703_448_1110
theorem blk_703_448_1120 : allRange (okAt f_703_448 703 448 1924) 1120 10 = true := by decide +kernel
theorem ok_703_448_1130 : ∀ t < 1130, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1120 blk_703_448_1120
theorem blk_703_448_1130 : allRange (okAt f_703_448 703 448 1924) 1130 10 = true := by decide +kernel
theorem ok_703_448_1140 : ∀ t < 1140, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1130 blk_703_448_1130
theorem blk_703_448_1140 : allRange (okAt f_703_448 703 448 1924) 1140 10 = true := by decide +kernel
theorem ok_703_448_1150 : ∀ t < 1150, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1140 blk_703_448_1140
theorem blk_703_448_1150 : allRange (okAt f_703_448 703 448 1924) 1150 10 = true := by decide +kernel
theorem ok_703_448_1160 : ∀ t < 1160, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1150 blk_703_448_1150
theorem blk_703_448_1160 : allRange (okAt f_703_448 703 448 1924) 1160 10 = true := by decide +kernel
theorem ok_703_448_1170 : ∀ t < 1170, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1160 blk_703_448_1160
theorem blk_703_448_1170 : allRange (okAt f_703_448 703 448 1924) 1170 10 = true := by decide +kernel
theorem ok_703_448_1180 : ∀ t < 1180, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1170 blk_703_448_1170
theorem blk_703_448_1180 : allRange (okAt f_703_448 703 448 1924) 1180 10 = true := by decide +kernel
theorem ok_703_448_1190 : ∀ t < 1190, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1180 blk_703_448_1180
theorem blk_703_448_1190 : allRange (okAt f_703_448 703 448 1924) 1190 10 = true := by decide +kernel
theorem ok_703_448_1200 : ∀ t < 1200, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1190 blk_703_448_1190
theorem blk_703_448_1200 : allRange (okAt f_703_448 703 448 1924) 1200 10 = true := by decide +kernel
theorem ok_703_448_1210 : ∀ t < 1210, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1200 blk_703_448_1200
theorem blk_703_448_1210 : allRange (okAt f_703_448 703 448 1924) 1210 10 = true := by decide +kernel
theorem ok_703_448_1220 : ∀ t < 1220, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1210 blk_703_448_1210
theorem blk_703_448_1220 : allRange (okAt f_703_448 703 448 1924) 1220 10 = true := by decide +kernel
theorem ok_703_448_1230 : ∀ t < 1230, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1220 blk_703_448_1220
theorem blk_703_448_1230 : allRange (okAt f_703_448 703 448 1924) 1230 10 = true := by decide +kernel
theorem ok_703_448_1240 : ∀ t < 1240, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1230 blk_703_448_1230
theorem blk_703_448_1240 : allRange (okAt f_703_448 703 448 1924) 1240 10 = true := by decide +kernel
theorem ok_703_448_1250 : ∀ t < 1250, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1240 blk_703_448_1240
theorem blk_703_448_1250 : allRange (okAt f_703_448 703 448 1924) 1250 10 = true := by decide +kernel
theorem ok_703_448_1260 : ∀ t < 1260, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1250 blk_703_448_1250
theorem blk_703_448_1260 : allRange (okAt f_703_448 703 448 1924) 1260 10 = true := by decide +kernel
theorem ok_703_448_1270 : ∀ t < 1270, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1260 blk_703_448_1260
theorem blk_703_448_1270 : allRange (okAt f_703_448 703 448 1924) 1270 10 = true := by decide +kernel
theorem ok_703_448_1280 : ∀ t < 1280, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1270 blk_703_448_1270
theorem blk_703_448_1280 : allRange (okAt f_703_448 703 448 1924) 1280 10 = true := by decide +kernel
theorem ok_703_448_1290 : ∀ t < 1290, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1280 blk_703_448_1280
theorem blk_703_448_1290 : allRange (okAt f_703_448 703 448 1924) 1290 10 = true := by decide +kernel
theorem ok_703_448_1300 : ∀ t < 1300, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1290 blk_703_448_1290
theorem blk_703_448_1300 : allRange (okAt f_703_448 703 448 1924) 1300 10 = true := by decide +kernel
theorem ok_703_448_1310 : ∀ t < 1310, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1300 blk_703_448_1300
theorem blk_703_448_1310 : allRange (okAt f_703_448 703 448 1924) 1310 10 = true := by decide +kernel
theorem ok_703_448_1320 : ∀ t < 1320, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1310 blk_703_448_1310
theorem blk_703_448_1320 : allRange (okAt f_703_448 703 448 1924) 1320 10 = true := by decide +kernel
theorem ok_703_448_1330 : ∀ t < 1330, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1320 blk_703_448_1320
theorem blk_703_448_1330 : allRange (okAt f_703_448 703 448 1924) 1330 10 = true := by decide +kernel
theorem ok_703_448_1340 : ∀ t < 1340, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1330 blk_703_448_1330
theorem blk_703_448_1340 : allRange (okAt f_703_448 703 448 1924) 1340 10 = true := by decide +kernel
theorem ok_703_448_1350 : ∀ t < 1350, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1340 blk_703_448_1340
theorem blk_703_448_1350 : allRange (okAt f_703_448 703 448 1924) 1350 10 = true := by decide +kernel
theorem ok_703_448_1360 : ∀ t < 1360, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1350 blk_703_448_1350
theorem blk_703_448_1360 : allRange (okAt f_703_448 703 448 1924) 1360 10 = true := by decide +kernel
theorem ok_703_448_1370 : ∀ t < 1370, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1360 blk_703_448_1360
theorem blk_703_448_1370 : allRange (okAt f_703_448 703 448 1924) 1370 10 = true := by decide +kernel
theorem ok_703_448_1380 : ∀ t < 1380, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1370 blk_703_448_1370
theorem blk_703_448_1380 : allRange (okAt f_703_448 703 448 1924) 1380 10 = true := by decide +kernel
theorem ok_703_448_1390 : ∀ t < 1390, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1380 blk_703_448_1380
theorem blk_703_448_1390 : allRange (okAt f_703_448 703 448 1924) 1390 10 = true := by decide +kernel
theorem ok_703_448_1400 : ∀ t < 1400, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1390 blk_703_448_1390
theorem blk_703_448_1400 : allRange (okAt f_703_448 703 448 1924) 1400 10 = true := by decide +kernel
theorem ok_703_448_1410 : ∀ t < 1410, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1400 blk_703_448_1400
theorem blk_703_448_1410 : allRange (okAt f_703_448 703 448 1924) 1410 10 = true := by decide +kernel
theorem ok_703_448_1420 : ∀ t < 1420, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1410 blk_703_448_1410
theorem blk_703_448_1420 : allRange (okAt f_703_448 703 448 1924) 1420 10 = true := by decide +kernel
theorem ok_703_448_1430 : ∀ t < 1430, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1420 blk_703_448_1420
theorem blk_703_448_1430 : allRange (okAt f_703_448 703 448 1924) 1430 10 = true := by decide +kernel
theorem ok_703_448_1440 : ∀ t < 1440, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1430 blk_703_448_1430
theorem blk_703_448_1440 : allRange (okAt f_703_448 703 448 1924) 1440 10 = true := by decide +kernel
theorem ok_703_448_1450 : ∀ t < 1450, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1440 blk_703_448_1440
theorem blk_703_448_1450 : allRange (okAt f_703_448 703 448 1924) 1450 10 = true := by decide +kernel
theorem ok_703_448_1460 : ∀ t < 1460, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1450 blk_703_448_1450
theorem blk_703_448_1460 : allRange (okAt f_703_448 703 448 1924) 1460 10 = true := by decide +kernel
theorem ok_703_448_1470 : ∀ t < 1470, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1460 blk_703_448_1460
theorem blk_703_448_1470 : allRange (okAt f_703_448 703 448 1924) 1470 10 = true := by decide +kernel
theorem ok_703_448_1480 : ∀ t < 1480, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1470 blk_703_448_1470
theorem blk_703_448_1480 : allRange (okAt f_703_448 703 448 1924) 1480 10 = true := by decide +kernel
theorem ok_703_448_1490 : ∀ t < 1490, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1480 blk_703_448_1480
theorem blk_703_448_1490 : allRange (okAt f_703_448 703 448 1924) 1490 10 = true := by decide +kernel
theorem ok_703_448_1500 : ∀ t < 1500, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1490 blk_703_448_1490
theorem blk_703_448_1500 : allRange (okAt f_703_448 703 448 1924) 1500 10 = true := by decide +kernel
theorem ok_703_448_1510 : ∀ t < 1510, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1500 blk_703_448_1500
theorem blk_703_448_1510 : allRange (okAt f_703_448 703 448 1924) 1510 10 = true := by decide +kernel
theorem ok_703_448_1520 : ∀ t < 1520, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1510 blk_703_448_1510
theorem blk_703_448_1520 : allRange (okAt f_703_448 703 448 1924) 1520 10 = true := by decide +kernel
theorem ok_703_448_1530 : ∀ t < 1530, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1520 blk_703_448_1520
theorem blk_703_448_1530 : allRange (okAt f_703_448 703 448 1924) 1530 10 = true := by decide +kernel
theorem ok_703_448_1540 : ∀ t < 1540, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1530 blk_703_448_1530
theorem blk_703_448_1540 : allRange (okAt f_703_448 703 448 1924) 1540 10 = true := by decide +kernel
theorem ok_703_448_1550 : ∀ t < 1550, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1540 blk_703_448_1540
theorem blk_703_448_1550 : allRange (okAt f_703_448 703 448 1924) 1550 10 = true := by decide +kernel
theorem ok_703_448_1560 : ∀ t < 1560, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1550 blk_703_448_1550
theorem blk_703_448_1560 : allRange (okAt f_703_448 703 448 1924) 1560 10 = true := by decide +kernel
theorem ok_703_448_1570 : ∀ t < 1570, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1560 blk_703_448_1560
theorem blk_703_448_1570 : allRange (okAt f_703_448 703 448 1924) 1570 10 = true := by decide +kernel
theorem ok_703_448_1580 : ∀ t < 1580, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1570 blk_703_448_1570
theorem blk_703_448_1580 : allRange (okAt f_703_448 703 448 1924) 1580 10 = true := by decide +kernel
theorem ok_703_448_1590 : ∀ t < 1590, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1580 blk_703_448_1580
theorem blk_703_448_1590 : allRange (okAt f_703_448 703 448 1924) 1590 10 = true := by decide +kernel
theorem ok_703_448_1600 : ∀ t < 1600, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1590 blk_703_448_1590
theorem blk_703_448_1600 : allRange (okAt f_703_448 703 448 1924) 1600 10 = true := by decide +kernel
theorem ok_703_448_1610 : ∀ t < 1610, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1600 blk_703_448_1600
theorem blk_703_448_1610 : allRange (okAt f_703_448 703 448 1924) 1610 10 = true := by decide +kernel
theorem ok_703_448_1620 : ∀ t < 1620, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1610 blk_703_448_1610
theorem blk_703_448_1620 : allRange (okAt f_703_448 703 448 1924) 1620 10 = true := by decide +kernel
theorem ok_703_448_1630 : ∀ t < 1630, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1620 blk_703_448_1620
theorem blk_703_448_1630 : allRange (okAt f_703_448 703 448 1924) 1630 10 = true := by decide +kernel
theorem ok_703_448_1640 : ∀ t < 1640, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1630 blk_703_448_1630
theorem blk_703_448_1640 : allRange (okAt f_703_448 703 448 1924) 1640 10 = true := by decide +kernel
theorem ok_703_448_1650 : ∀ t < 1650, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1640 blk_703_448_1640
theorem blk_703_448_1650 : allRange (okAt f_703_448 703 448 1924) 1650 10 = true := by decide +kernel
theorem ok_703_448_1660 : ∀ t < 1660, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1650 blk_703_448_1650
theorem blk_703_448_1660 : allRange (okAt f_703_448 703 448 1924) 1660 10 = true := by decide +kernel
theorem ok_703_448_1670 : ∀ t < 1670, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1660 blk_703_448_1660
theorem blk_703_448_1670 : allRange (okAt f_703_448 703 448 1924) 1670 10 = true := by decide +kernel
theorem ok_703_448_1680 : ∀ t < 1680, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1670 blk_703_448_1670
theorem blk_703_448_1680 : allRange (okAt f_703_448 703 448 1924) 1680 10 = true := by decide +kernel
theorem ok_703_448_1690 : ∀ t < 1690, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1680 blk_703_448_1680
theorem blk_703_448_1690 : allRange (okAt f_703_448 703 448 1924) 1690 10 = true := by decide +kernel
theorem ok_703_448_1700 : ∀ t < 1700, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1690 blk_703_448_1690
theorem blk_703_448_1700 : allRange (okAt f_703_448 703 448 1924) 1700 10 = true := by decide +kernel
theorem ok_703_448_1710 : ∀ t < 1710, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1700 blk_703_448_1700
theorem blk_703_448_1710 : allRange (okAt f_703_448 703 448 1924) 1710 10 = true := by decide +kernel
theorem ok_703_448_1720 : ∀ t < 1720, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1710 blk_703_448_1710
theorem blk_703_448_1720 : allRange (okAt f_703_448 703 448 1924) 1720 10 = true := by decide +kernel
theorem ok_703_448_1730 : ∀ t < 1730, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1720 blk_703_448_1720
theorem blk_703_448_1730 : allRange (okAt f_703_448 703 448 1924) 1730 10 = true := by decide +kernel
theorem ok_703_448_1740 : ∀ t < 1740, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1730 blk_703_448_1730
theorem blk_703_448_1740 : allRange (okAt f_703_448 703 448 1924) 1740 10 = true := by decide +kernel
theorem ok_703_448_1750 : ∀ t < 1750, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1740 blk_703_448_1740
theorem blk_703_448_1750 : allRange (okAt f_703_448 703 448 1924) 1750 10 = true := by decide +kernel
theorem ok_703_448_1760 : ∀ t < 1760, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1750 blk_703_448_1750
theorem blk_703_448_1760 : allRange (okAt f_703_448 703 448 1924) 1760 10 = true := by decide +kernel
theorem ok_703_448_1770 : ∀ t < 1770, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1760 blk_703_448_1760
theorem blk_703_448_1770 : allRange (okAt f_703_448 703 448 1924) 1770 10 = true := by decide +kernel
theorem ok_703_448_1780 : ∀ t < 1780, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1770 blk_703_448_1770
theorem blk_703_448_1780 : allRange (okAt f_703_448 703 448 1924) 1780 10 = true := by decide +kernel
theorem ok_703_448_1790 : ∀ t < 1790, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1780 blk_703_448_1780
theorem blk_703_448_1790 : allRange (okAt f_703_448 703 448 1924) 1790 10 = true := by decide +kernel
theorem ok_703_448_1800 : ∀ t < 1800, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1790 blk_703_448_1790
theorem blk_703_448_1800 : allRange (okAt f_703_448 703 448 1924) 1800 10 = true := by decide +kernel
theorem ok_703_448_1810 : ∀ t < 1810, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1800 blk_703_448_1800
theorem blk_703_448_1810 : allRange (okAt f_703_448 703 448 1924) 1810 10 = true := by decide +kernel
theorem ok_703_448_1820 : ∀ t < 1820, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1810 blk_703_448_1810
theorem blk_703_448_1820 : allRange (okAt f_703_448 703 448 1924) 1820 10 = true := by decide +kernel
theorem ok_703_448_1830 : ∀ t < 1830, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1820 blk_703_448_1820
theorem blk_703_448_1830 : allRange (okAt f_703_448 703 448 1924) 1830 10 = true := by decide +kernel
theorem ok_703_448_1840 : ∀ t < 1840, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1830 blk_703_448_1830
theorem blk_703_448_1840 : allRange (okAt f_703_448 703 448 1924) 1840 10 = true := by decide +kernel
theorem ok_703_448_1850 : ∀ t < 1850, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1840 blk_703_448_1840
theorem blk_703_448_1850 : allRange (okAt f_703_448 703 448 1924) 1850 10 = true := by decide +kernel
theorem ok_703_448_1860 : ∀ t < 1860, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1850 blk_703_448_1850
theorem blk_703_448_1860 : allRange (okAt f_703_448 703 448 1924) 1860 10 = true := by decide +kernel
theorem ok_703_448_1870 : ∀ t < 1870, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1860 blk_703_448_1860
theorem blk_703_448_1870 : allRange (okAt f_703_448 703 448 1924) 1870 10 = true := by decide +kernel
theorem ok_703_448_1880 : ∀ t < 1880, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1870 blk_703_448_1870
theorem blk_703_448_1880 : allRange (okAt f_703_448 703 448 1924) 1880 10 = true := by decide +kernel
theorem ok_703_448_1890 : ∀ t < 1890, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1880 blk_703_448_1880
theorem blk_703_448_1890 : allRange (okAt f_703_448 703 448 1924) 1890 10 = true := by decide +kernel
theorem ok_703_448_1900 : ∀ t < 1900, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1890 blk_703_448_1890
theorem blk_703_448_1900 : allRange (okAt f_703_448 703 448 1924) 1900 10 = true := by decide +kernel
theorem ok_703_448_1910 : ∀ t < 1910, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1900 blk_703_448_1900
theorem blk_703_448_1910 : allRange (okAt f_703_448 703 448 1924) 1910 10 = true := by decide +kernel
theorem ok_703_448_1920 : ∀ t < 1920, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1910 blk_703_448_1910
theorem blk_703_448_1920 : allRange (okAt f_703_448 703 448 1924) 1920 4 = true := by decide +kernel
theorem ok_703_448_1924 : ∀ t < 1924, okAt f_703_448 703 448 1924 t = true := allRange_extend ok_703_448_1920 blk_703_448_1920

theorem coil_703_448 : ∃ v : ℕ → Fin 703 → Bool, IsCoil 448 1924 v :=
  exists_coil_of_check f_703_448 448 1924 (by norm_num) ok_703_448_1924 (by decide +kernel)

/-- K(703,448) = 1924  (= 4k+2l+10, l = 61; code: fam10_703_448_1924.txt) -/
theorem K_703_448 : IsMaxLength 703 448 1924 :=
  isMaxLength_of_chord coil_703_448 (by norm_num) 897 (by norm_num) (by norm_num) (by decide +kernel)


end Coil
