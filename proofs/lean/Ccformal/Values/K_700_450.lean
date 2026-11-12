import Ccformal.Checker

namespace Coil

def W_700_450 : ℕ := 0x2bb01e901c002ba01e102b901d302b801d102b701b802b601ce02b501cc02b401ca02b301df01af02b201d702b101c402b001c202af01a702ae01be02ad01bc02ac01ba02ab01d5019e02aa01c802a901b302a801b102a7019602a601ad02a501ab02a401a902a301c6018d02a201b702a101a202a001a0029f0185029e019c029d019a029c0198029b01b5017c029a01a6029901910298018f029701740296018b0295018902940187029301a4016b02920195029101800290017e028f0163028e017a028d0178028c0176028b0193015a028a01840289016f0288016d02870152028601690285016702840165028301820149028201730281015e0280015c027f0141027e0158027d0156027c0154027b01710138027a01620279014d0278014b02770130027601470275014502740143027301600127027201510271013c0270013a026f011f026e0136026d0134026c0132026b014f0116026a01400269012b026801290267010e0266012502650123026401210263013e01050262012f0261011a02600118025f00fd025e0114025d0112025c0110025b012d00f4025a011e0259010902580107025700ec0256010302550101025400ff0253011c00e30252010d025100f8025000f6024f00db024e00f2024d00f0024c00ee024b010b00d2024a00fc024900e7024800e5024700ca024600e1024500df024400dd024300fa00c1024200eb024100d6024000d4023f00b9023e00d0023d00ce023c00cc023b00e900b0023a00da023900c5023800c3023700a8023600bf023500bd023400bb023300d8009f023200c9023100b4023000b2022f0097022e00ae022d00ac022c00aa022b00c7008e022a00b8022900a3022800a1022700860226009d0225009b02240099022300b6007d022200a70221009202200090021f0075021e008c021d008a021c0088021b00a5006c021a0096021900810218007f021700640216007b021500790214007702130094005b02120085021100700210006e020f0053020e006a020d0068020c0066020b0083004a020a00740209005f0208005d02070042020600590205005702040055020300720039020200630201004e0200004c01ff003101fe004801fd004601fc004401fb0061002801fa005201f9003d01f8003b01f7002001f6003701f5003501f4003301f30050001701f2004101f1002c01f0002a01ef000f01ee002601ed002401ec002201eb003f000601ea003001e8001b01e7001901e601e901e5001501e4001301e3001101e2002e01b801e0001f01de000a01dd000801dc01df01db000401da000201d9000001d8001d01a701d6000e01d401d301d201d101d001d501cf01ce01cd01cc01cb01ca01c9000c019601c701c001c501c401c301c201c101c601bf01be01bd01bc01bb01ba01b901e1018501b601af01b401b301b201b101b001b501ae01ad01ac01ab01aa01a901a801d7017401a5019e01a301a201a101a0019f01a4019d019c019b019a01990198019701c801630194018d019201910190018f018e0193018c018b018a018901880187018601b701520183017c01810180017f017e017d0182017b017a0179017801770176017501a601410172016b0170016f016e016d016c0171016a016901680167016601650164019501300161015a015f015e015d015c015b016001590158015701560155015401530184011f01500149014e014d014c014b014a014f01480147014601450144014301420173010e013f0138013d013c013b013a0139013e0137013601350134013301320131016200fd012e0127012c012b012a01290128012d0126012501240123012201210120015100ec011d0116011b011a011901180117011c011501140113011201110110010f014000db010c0105010a0109010801070106010b0104010301020101010000ff00fe012f00ca00fb00f400f900f800f700f600f500fa00f300f200f100f000ef00ee00ed011e00b900ea00e300e800e700e600e500e400e900e200e100e000df00de00dd00dc010d00a800d900d200d700d600d500d400d300d800d100d000cf00ce00cd00cc00cb00fc009700c800c100c600c500c400c300c200c700c000bf00be00bd00bc00bb00ba00eb008600b700b000b500b400b300b200b100b600af00ae00ad00ac00ab00aa00a900da007500a6009f00a400a300a200a100a000a5009e009d009c009b009a0099009800c900640095008e0093009200910090008f0094008d008c008b008a00890088008700b800530084007d008200810080007f007e0083007c007b007a007900780077007600a700420073006c00710070006f006e006d0072006b006a00690068006700660065009600310062005b0060005f005e005d005c0061005a005900580057005600550054008500200051004a004f004e004d004c004b005000490048004700460045004400430074000f00400039003e003d003c003b003a003f0038003700360035003400330032006301e9002f0028002d002c002b002a0029002e0027002600250024002300220021005201df001e0017001c001b001a00190018001d0016001500140013001200110010004101d5000d0006000b000a000900080007000c00050004000300020001000002bb003001c602ba01b802b901d302b801d102b701e102b601ce02b501cc02b401ca02b3001f01b502b201a702b101c402b001c202af01d702ae01be02ad01bc02ac01ba02ab000e01a402aa019602a901b302a801b102a701c802a601ad02a501ab02a401a902a301c0019302a2018502a101a202a001a0029f01b7029e019c029d019a029c0198029b01af0182029a0174029901910298018f029701a60296018b02950189029401870293019e017102920163029101800290017e028f0195028e017a028d0178028c0176028b018d0160028a01520289016f0288016d028701840286016902850167028401650283017c014f028201410281015e0280015c027f0173027e0158027d0156027c0154027b016b013e027a01300279014d0278014b027701620276014702750145027401430273015a012d0272011f0271013c0270013a026f0151026e0136026d0134026c0132026b0149011c026a010e0269012b026801290267014002660125026501230264012102630138010b026200fd0261011a02600118025f012f025e0114025d0112025c0110025b012700fa025a00ec02590109025801070257011e0256010302550101025400ff0253011600e9025200db025100f8025000f6024f010d024e00f2024d00f0024c00ee024b010500d8024a00ca024900e7024800e5024700fc024600e1024500df024400dd024300f400c7024200b9024100d6024000d4023f00eb023e00d0023d00ce023c00cc023b00e300b6023a00a8023900c5023800c3023700da023600bf023500bd023400bb023300d200a502320097023100b4023000b2022f00c9022e00ae022d00ac022c00aa022b00c10094022a0086022900a3022800a1022700b80226009d0225009b02240099022300b00083022200750221009202200090021f00a7021e008c021d008a021c0088021b009f0072021a0064021900810218007f021700960216007b02150079021400770213008e006102120053021100700210006e020f0085020e006a020d0068020c0066020b007d0050020a00420209005f0208005d020700740206005902050057020400550203006c003f020200310201004e0200004c01ff006301fe004801fd004601fc004401fb005b002e01fa002001f9003d01f8003b01f7005201f6003701f5003501f4003301f3004a001d01f2000f01f1002c01f0002a01ef004101ee002601ed002401ec002201eb0039000c01ea01e901e8001b01e7001901e6003001e5001501e4001301e3001101e2002801e101e001df01de000a01dd000801dc001f01db000401da000201d9000001d8001701d701d601d501d401d301d201d101d0000e01cf01ce01cd01cc01cb01ca01c9000601c801c701c601c501c401c301c201c101c001bf01be01bd01bc01bb01ba01b901b801b701b601b501b401b301b201b101b001af01ae01ad01ac01ab01aa01a901a801a701a601a501a401a301a201a101a0019f019e019d019c019b019a0199019801970196019501940193019201910190018f018e018d018c018b018a0189018801870186018501840183018201810180017f017e017d017c017b017a0179017801770176017501740173017201710170016f016e016d016c016b016a0169016801670166016501640163016201610160015f015e015d015c015b015a0159015801570156015501540153015201510150014f014e014d014c014b014a0149014801470146014501440143014201410140013f013e013d013c013b013a0139013801370136013501340133013201310130012f012e012d012c012b012a0129012801270126012501240123012201210120011f011e011d011c011b011a0119011801170116011501140113011201110110010f010e010d010c010b010a010901080107010601050104010301020101010000ff00fe00fd00fc00fb00fa00f900f800f700f600f500f400f300f200f100f000ef00ee00ed00ec00eb00ea00e900e800e700e600e500e400e300e200e100e000df00de00dd00dc00db00da00d900d800d700d600d500d400d300d200d100d000cf00ce00cd00cc00cb00ca00c900c800c700c600c500c400c300c200c100c000bf00be00bd00bc00bb00ba00b900b800b700b600b500b400b300b200b100b000af00ae00ad00ac00ab00aa00a900a800a700a600a500a400a300a200a100a0009f009e009d009c009b009a0099009800970096009500940093009200910090008f008e008d008c008b008a0089008800870086008500840083008200810080007f007e007d007c007b007a0079007800770076007500740073007200710070006f006e006d006c006b006a0069006800670066006500640063006200610060005f005e005d005c005b005a0059005800570056005500540053005200510050004f004e004d004c004b004a0049004800470046004500440043004200410040003f003e003d003c003b003a0039003800370036003500340033003200310030002f002e002d002c002b002a0029002800270026002500240023002200210020001f001e001d001c001b001a0019001800170016001500140013001200110010000f000e000d000c000b000a0009000800070006000500040003000200010000

def f_700_450 (i : ℕ) : ℕ := (W_700_450 >>> (16 * i)) &&& 0xFFFF

theorem ok_700_450_0 : ∀ t < 0, okAt f_700_450 700 450 1904 t = true := allRange_zero

theorem blk_700_450_0 : allRange (okAt f_700_450 700 450 1904) 0 10 = true := by decide +kernel
theorem ok_700_450_10 : ∀ t < 10, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_0 blk_700_450_0
theorem blk_700_450_10 : allRange (okAt f_700_450 700 450 1904) 10 10 = true := by decide +kernel
theorem ok_700_450_20 : ∀ t < 20, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_10 blk_700_450_10
theorem blk_700_450_20 : allRange (okAt f_700_450 700 450 1904) 20 10 = true := by decide +kernel
theorem ok_700_450_30 : ∀ t < 30, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_20 blk_700_450_20
theorem blk_700_450_30 : allRange (okAt f_700_450 700 450 1904) 30 10 = true := by decide +kernel
theorem ok_700_450_40 : ∀ t < 40, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_30 blk_700_450_30
theorem blk_700_450_40 : allRange (okAt f_700_450 700 450 1904) 40 10 = true := by decide +kernel
theorem ok_700_450_50 : ∀ t < 50, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_40 blk_700_450_40
theorem blk_700_450_50 : allRange (okAt f_700_450 700 450 1904) 50 10 = true := by decide +kernel
theorem ok_700_450_60 : ∀ t < 60, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_50 blk_700_450_50
theorem blk_700_450_60 : allRange (okAt f_700_450 700 450 1904) 60 10 = true := by decide +kernel
theorem ok_700_450_70 : ∀ t < 70, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_60 blk_700_450_60
theorem blk_700_450_70 : allRange (okAt f_700_450 700 450 1904) 70 10 = true := by decide +kernel
theorem ok_700_450_80 : ∀ t < 80, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_70 blk_700_450_70
theorem blk_700_450_80 : allRange (okAt f_700_450 700 450 1904) 80 10 = true := by decide +kernel
theorem ok_700_450_90 : ∀ t < 90, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_80 blk_700_450_80
theorem blk_700_450_90 : allRange (okAt f_700_450 700 450 1904) 90 10 = true := by decide +kernel
theorem ok_700_450_100 : ∀ t < 100, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_90 blk_700_450_90
theorem blk_700_450_100 : allRange (okAt f_700_450 700 450 1904) 100 10 = true := by decide +kernel
theorem ok_700_450_110 : ∀ t < 110, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_100 blk_700_450_100
theorem blk_700_450_110 : allRange (okAt f_700_450 700 450 1904) 110 10 = true := by decide +kernel
theorem ok_700_450_120 : ∀ t < 120, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_110 blk_700_450_110
theorem blk_700_450_120 : allRange (okAt f_700_450 700 450 1904) 120 10 = true := by decide +kernel
theorem ok_700_450_130 : ∀ t < 130, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_120 blk_700_450_120
theorem blk_700_450_130 : allRange (okAt f_700_450 700 450 1904) 130 10 = true := by decide +kernel
theorem ok_700_450_140 : ∀ t < 140, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_130 blk_700_450_130
theorem blk_700_450_140 : allRange (okAt f_700_450 700 450 1904) 140 10 = true := by decide +kernel
theorem ok_700_450_150 : ∀ t < 150, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_140 blk_700_450_140
theorem blk_700_450_150 : allRange (okAt f_700_450 700 450 1904) 150 10 = true := by decide +kernel
theorem ok_700_450_160 : ∀ t < 160, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_150 blk_700_450_150
theorem blk_700_450_160 : allRange (okAt f_700_450 700 450 1904) 160 10 = true := by decide +kernel
theorem ok_700_450_170 : ∀ t < 170, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_160 blk_700_450_160
theorem blk_700_450_170 : allRange (okAt f_700_450 700 450 1904) 170 10 = true := by decide +kernel
theorem ok_700_450_180 : ∀ t < 180, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_170 blk_700_450_170
theorem blk_700_450_180 : allRange (okAt f_700_450 700 450 1904) 180 10 = true := by decide +kernel
theorem ok_700_450_190 : ∀ t < 190, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_180 blk_700_450_180
theorem blk_700_450_190 : allRange (okAt f_700_450 700 450 1904) 190 10 = true := by decide +kernel
theorem ok_700_450_200 : ∀ t < 200, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_190 blk_700_450_190
theorem blk_700_450_200 : allRange (okAt f_700_450 700 450 1904) 200 10 = true := by decide +kernel
theorem ok_700_450_210 : ∀ t < 210, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_200 blk_700_450_200
theorem blk_700_450_210 : allRange (okAt f_700_450 700 450 1904) 210 10 = true := by decide +kernel
theorem ok_700_450_220 : ∀ t < 220, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_210 blk_700_450_210
theorem blk_700_450_220 : allRange (okAt f_700_450 700 450 1904) 220 10 = true := by decide +kernel
theorem ok_700_450_230 : ∀ t < 230, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_220 blk_700_450_220
theorem blk_700_450_230 : allRange (okAt f_700_450 700 450 1904) 230 10 = true := by decide +kernel
theorem ok_700_450_240 : ∀ t < 240, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_230 blk_700_450_230
theorem blk_700_450_240 : allRange (okAt f_700_450 700 450 1904) 240 10 = true := by decide +kernel
theorem ok_700_450_250 : ∀ t < 250, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_240 blk_700_450_240
theorem blk_700_450_250 : allRange (okAt f_700_450 700 450 1904) 250 10 = true := by decide +kernel
theorem ok_700_450_260 : ∀ t < 260, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_250 blk_700_450_250
theorem blk_700_450_260 : allRange (okAt f_700_450 700 450 1904) 260 10 = true := by decide +kernel
theorem ok_700_450_270 : ∀ t < 270, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_260 blk_700_450_260
theorem blk_700_450_270 : allRange (okAt f_700_450 700 450 1904) 270 10 = true := by decide +kernel
theorem ok_700_450_280 : ∀ t < 280, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_270 blk_700_450_270
theorem blk_700_450_280 : allRange (okAt f_700_450 700 450 1904) 280 10 = true := by decide +kernel
theorem ok_700_450_290 : ∀ t < 290, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_280 blk_700_450_280
theorem blk_700_450_290 : allRange (okAt f_700_450 700 450 1904) 290 10 = true := by decide +kernel
theorem ok_700_450_300 : ∀ t < 300, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_290 blk_700_450_290
theorem blk_700_450_300 : allRange (okAt f_700_450 700 450 1904) 300 10 = true := by decide +kernel
theorem ok_700_450_310 : ∀ t < 310, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_300 blk_700_450_300
theorem blk_700_450_310 : allRange (okAt f_700_450 700 450 1904) 310 10 = true := by decide +kernel
theorem ok_700_450_320 : ∀ t < 320, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_310 blk_700_450_310
theorem blk_700_450_320 : allRange (okAt f_700_450 700 450 1904) 320 10 = true := by decide +kernel
theorem ok_700_450_330 : ∀ t < 330, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_320 blk_700_450_320
theorem blk_700_450_330 : allRange (okAt f_700_450 700 450 1904) 330 10 = true := by decide +kernel
theorem ok_700_450_340 : ∀ t < 340, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_330 blk_700_450_330
theorem blk_700_450_340 : allRange (okAt f_700_450 700 450 1904) 340 10 = true := by decide +kernel
theorem ok_700_450_350 : ∀ t < 350, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_340 blk_700_450_340
theorem blk_700_450_350 : allRange (okAt f_700_450 700 450 1904) 350 10 = true := by decide +kernel
theorem ok_700_450_360 : ∀ t < 360, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_350 blk_700_450_350
theorem blk_700_450_360 : allRange (okAt f_700_450 700 450 1904) 360 10 = true := by decide +kernel
theorem ok_700_450_370 : ∀ t < 370, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_360 blk_700_450_360
theorem blk_700_450_370 : allRange (okAt f_700_450 700 450 1904) 370 10 = true := by decide +kernel
theorem ok_700_450_380 : ∀ t < 380, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_370 blk_700_450_370
theorem blk_700_450_380 : allRange (okAt f_700_450 700 450 1904) 380 10 = true := by decide +kernel
theorem ok_700_450_390 : ∀ t < 390, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_380 blk_700_450_380
theorem blk_700_450_390 : allRange (okAt f_700_450 700 450 1904) 390 10 = true := by decide +kernel
theorem ok_700_450_400 : ∀ t < 400, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_390 blk_700_450_390
theorem blk_700_450_400 : allRange (okAt f_700_450 700 450 1904) 400 10 = true := by decide +kernel
theorem ok_700_450_410 : ∀ t < 410, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_400 blk_700_450_400
theorem blk_700_450_410 : allRange (okAt f_700_450 700 450 1904) 410 10 = true := by decide +kernel
theorem ok_700_450_420 : ∀ t < 420, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_410 blk_700_450_410
theorem blk_700_450_420 : allRange (okAt f_700_450 700 450 1904) 420 10 = true := by decide +kernel
theorem ok_700_450_430 : ∀ t < 430, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_420 blk_700_450_420
theorem blk_700_450_430 : allRange (okAt f_700_450 700 450 1904) 430 10 = true := by decide +kernel
theorem ok_700_450_440 : ∀ t < 440, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_430 blk_700_450_430
theorem blk_700_450_440 : allRange (okAt f_700_450 700 450 1904) 440 10 = true := by decide +kernel
theorem ok_700_450_450 : ∀ t < 450, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_440 blk_700_450_440
theorem blk_700_450_450 : allRange (okAt f_700_450 700 450 1904) 450 10 = true := by decide +kernel
theorem ok_700_450_460 : ∀ t < 460, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_450 blk_700_450_450
theorem blk_700_450_460 : allRange (okAt f_700_450 700 450 1904) 460 10 = true := by decide +kernel
theorem ok_700_450_470 : ∀ t < 470, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_460 blk_700_450_460
theorem blk_700_450_470 : allRange (okAt f_700_450 700 450 1904) 470 10 = true := by decide +kernel
theorem ok_700_450_480 : ∀ t < 480, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_470 blk_700_450_470
theorem blk_700_450_480 : allRange (okAt f_700_450 700 450 1904) 480 10 = true := by decide +kernel
theorem ok_700_450_490 : ∀ t < 490, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_480 blk_700_450_480
theorem blk_700_450_490 : allRange (okAt f_700_450 700 450 1904) 490 10 = true := by decide +kernel
theorem ok_700_450_500 : ∀ t < 500, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_490 blk_700_450_490
theorem blk_700_450_500 : allRange (okAt f_700_450 700 450 1904) 500 10 = true := by decide +kernel
theorem ok_700_450_510 : ∀ t < 510, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_500 blk_700_450_500
theorem blk_700_450_510 : allRange (okAt f_700_450 700 450 1904) 510 10 = true := by decide +kernel
theorem ok_700_450_520 : ∀ t < 520, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_510 blk_700_450_510
theorem blk_700_450_520 : allRange (okAt f_700_450 700 450 1904) 520 10 = true := by decide +kernel
theorem ok_700_450_530 : ∀ t < 530, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_520 blk_700_450_520
theorem blk_700_450_530 : allRange (okAt f_700_450 700 450 1904) 530 10 = true := by decide +kernel
theorem ok_700_450_540 : ∀ t < 540, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_530 blk_700_450_530
theorem blk_700_450_540 : allRange (okAt f_700_450 700 450 1904) 540 10 = true := by decide +kernel
theorem ok_700_450_550 : ∀ t < 550, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_540 blk_700_450_540
theorem blk_700_450_550 : allRange (okAt f_700_450 700 450 1904) 550 10 = true := by decide +kernel
theorem ok_700_450_560 : ∀ t < 560, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_550 blk_700_450_550
theorem blk_700_450_560 : allRange (okAt f_700_450 700 450 1904) 560 10 = true := by decide +kernel
theorem ok_700_450_570 : ∀ t < 570, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_560 blk_700_450_560
theorem blk_700_450_570 : allRange (okAt f_700_450 700 450 1904) 570 10 = true := by decide +kernel
theorem ok_700_450_580 : ∀ t < 580, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_570 blk_700_450_570
theorem blk_700_450_580 : allRange (okAt f_700_450 700 450 1904) 580 10 = true := by decide +kernel
theorem ok_700_450_590 : ∀ t < 590, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_580 blk_700_450_580
theorem blk_700_450_590 : allRange (okAt f_700_450 700 450 1904) 590 10 = true := by decide +kernel
theorem ok_700_450_600 : ∀ t < 600, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_590 blk_700_450_590
theorem blk_700_450_600 : allRange (okAt f_700_450 700 450 1904) 600 10 = true := by decide +kernel
theorem ok_700_450_610 : ∀ t < 610, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_600 blk_700_450_600
theorem blk_700_450_610 : allRange (okAt f_700_450 700 450 1904) 610 10 = true := by decide +kernel
theorem ok_700_450_620 : ∀ t < 620, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_610 blk_700_450_610
theorem blk_700_450_620 : allRange (okAt f_700_450 700 450 1904) 620 10 = true := by decide +kernel
theorem ok_700_450_630 : ∀ t < 630, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_620 blk_700_450_620
theorem blk_700_450_630 : allRange (okAt f_700_450 700 450 1904) 630 10 = true := by decide +kernel
theorem ok_700_450_640 : ∀ t < 640, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_630 blk_700_450_630
theorem blk_700_450_640 : allRange (okAt f_700_450 700 450 1904) 640 10 = true := by decide +kernel
theorem ok_700_450_650 : ∀ t < 650, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_640 blk_700_450_640
theorem blk_700_450_650 : allRange (okAt f_700_450 700 450 1904) 650 10 = true := by decide +kernel
theorem ok_700_450_660 : ∀ t < 660, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_650 blk_700_450_650
theorem blk_700_450_660 : allRange (okAt f_700_450 700 450 1904) 660 10 = true := by decide +kernel
theorem ok_700_450_670 : ∀ t < 670, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_660 blk_700_450_660
theorem blk_700_450_670 : allRange (okAt f_700_450 700 450 1904) 670 10 = true := by decide +kernel
theorem ok_700_450_680 : ∀ t < 680, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_670 blk_700_450_670
theorem blk_700_450_680 : allRange (okAt f_700_450 700 450 1904) 680 10 = true := by decide +kernel
theorem ok_700_450_690 : ∀ t < 690, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_680 blk_700_450_680
theorem blk_700_450_690 : allRange (okAt f_700_450 700 450 1904) 690 10 = true := by decide +kernel
theorem ok_700_450_700 : ∀ t < 700, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_690 blk_700_450_690
theorem blk_700_450_700 : allRange (okAt f_700_450 700 450 1904) 700 10 = true := by decide +kernel
theorem ok_700_450_710 : ∀ t < 710, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_700 blk_700_450_700
theorem blk_700_450_710 : allRange (okAt f_700_450 700 450 1904) 710 10 = true := by decide +kernel
theorem ok_700_450_720 : ∀ t < 720, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_710 blk_700_450_710
theorem blk_700_450_720 : allRange (okAt f_700_450 700 450 1904) 720 10 = true := by decide +kernel
theorem ok_700_450_730 : ∀ t < 730, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_720 blk_700_450_720
theorem blk_700_450_730 : allRange (okAt f_700_450 700 450 1904) 730 10 = true := by decide +kernel
theorem ok_700_450_740 : ∀ t < 740, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_730 blk_700_450_730
theorem blk_700_450_740 : allRange (okAt f_700_450 700 450 1904) 740 10 = true := by decide +kernel
theorem ok_700_450_750 : ∀ t < 750, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_740 blk_700_450_740
theorem blk_700_450_750 : allRange (okAt f_700_450 700 450 1904) 750 10 = true := by decide +kernel
theorem ok_700_450_760 : ∀ t < 760, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_750 blk_700_450_750
theorem blk_700_450_760 : allRange (okAt f_700_450 700 450 1904) 760 10 = true := by decide +kernel
theorem ok_700_450_770 : ∀ t < 770, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_760 blk_700_450_760
theorem blk_700_450_770 : allRange (okAt f_700_450 700 450 1904) 770 10 = true := by decide +kernel
theorem ok_700_450_780 : ∀ t < 780, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_770 blk_700_450_770
theorem blk_700_450_780 : allRange (okAt f_700_450 700 450 1904) 780 10 = true := by decide +kernel
theorem ok_700_450_790 : ∀ t < 790, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_780 blk_700_450_780
theorem blk_700_450_790 : allRange (okAt f_700_450 700 450 1904) 790 10 = true := by decide +kernel
theorem ok_700_450_800 : ∀ t < 800, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_790 blk_700_450_790
theorem blk_700_450_800 : allRange (okAt f_700_450 700 450 1904) 800 10 = true := by decide +kernel
theorem ok_700_450_810 : ∀ t < 810, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_800 blk_700_450_800
theorem blk_700_450_810 : allRange (okAt f_700_450 700 450 1904) 810 10 = true := by decide +kernel
theorem ok_700_450_820 : ∀ t < 820, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_810 blk_700_450_810
theorem blk_700_450_820 : allRange (okAt f_700_450 700 450 1904) 820 10 = true := by decide +kernel
theorem ok_700_450_830 : ∀ t < 830, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_820 blk_700_450_820
theorem blk_700_450_830 : allRange (okAt f_700_450 700 450 1904) 830 10 = true := by decide +kernel
theorem ok_700_450_840 : ∀ t < 840, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_830 blk_700_450_830
theorem blk_700_450_840 : allRange (okAt f_700_450 700 450 1904) 840 10 = true := by decide +kernel
theorem ok_700_450_850 : ∀ t < 850, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_840 blk_700_450_840
theorem blk_700_450_850 : allRange (okAt f_700_450 700 450 1904) 850 10 = true := by decide +kernel
theorem ok_700_450_860 : ∀ t < 860, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_850 blk_700_450_850
theorem blk_700_450_860 : allRange (okAt f_700_450 700 450 1904) 860 10 = true := by decide +kernel
theorem ok_700_450_870 : ∀ t < 870, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_860 blk_700_450_860
theorem blk_700_450_870 : allRange (okAt f_700_450 700 450 1904) 870 10 = true := by decide +kernel
theorem ok_700_450_880 : ∀ t < 880, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_870 blk_700_450_870
theorem blk_700_450_880 : allRange (okAt f_700_450 700 450 1904) 880 10 = true := by decide +kernel
theorem ok_700_450_890 : ∀ t < 890, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_880 blk_700_450_880
theorem blk_700_450_890 : allRange (okAt f_700_450 700 450 1904) 890 10 = true := by decide +kernel
theorem ok_700_450_900 : ∀ t < 900, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_890 blk_700_450_890
theorem blk_700_450_900 : allRange (okAt f_700_450 700 450 1904) 900 10 = true := by decide +kernel
theorem ok_700_450_910 : ∀ t < 910, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_900 blk_700_450_900
theorem blk_700_450_910 : allRange (okAt f_700_450 700 450 1904) 910 10 = true := by decide +kernel
theorem ok_700_450_920 : ∀ t < 920, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_910 blk_700_450_910
theorem blk_700_450_920 : allRange (okAt f_700_450 700 450 1904) 920 10 = true := by decide +kernel
theorem ok_700_450_930 : ∀ t < 930, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_920 blk_700_450_920
theorem blk_700_450_930 : allRange (okAt f_700_450 700 450 1904) 930 10 = true := by decide +kernel
theorem ok_700_450_940 : ∀ t < 940, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_930 blk_700_450_930
theorem blk_700_450_940 : allRange (okAt f_700_450 700 450 1904) 940 10 = true := by decide +kernel
theorem ok_700_450_950 : ∀ t < 950, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_940 blk_700_450_940
theorem blk_700_450_950 : allRange (okAt f_700_450 700 450 1904) 950 10 = true := by decide +kernel
theorem ok_700_450_960 : ∀ t < 960, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_950 blk_700_450_950
theorem blk_700_450_960 : allRange (okAt f_700_450 700 450 1904) 960 10 = true := by decide +kernel
theorem ok_700_450_970 : ∀ t < 970, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_960 blk_700_450_960
theorem blk_700_450_970 : allRange (okAt f_700_450 700 450 1904) 970 10 = true := by decide +kernel
theorem ok_700_450_980 : ∀ t < 980, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_970 blk_700_450_970
theorem blk_700_450_980 : allRange (okAt f_700_450 700 450 1904) 980 10 = true := by decide +kernel
theorem ok_700_450_990 : ∀ t < 990, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_980 blk_700_450_980
theorem blk_700_450_990 : allRange (okAt f_700_450 700 450 1904) 990 10 = true := by decide +kernel
theorem ok_700_450_1000 : ∀ t < 1000, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_990 blk_700_450_990
theorem blk_700_450_1000 : allRange (okAt f_700_450 700 450 1904) 1000 10 = true := by decide +kernel
theorem ok_700_450_1010 : ∀ t < 1010, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1000 blk_700_450_1000
theorem blk_700_450_1010 : allRange (okAt f_700_450 700 450 1904) 1010 10 = true := by decide +kernel
theorem ok_700_450_1020 : ∀ t < 1020, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1010 blk_700_450_1010
theorem blk_700_450_1020 : allRange (okAt f_700_450 700 450 1904) 1020 10 = true := by decide +kernel
theorem ok_700_450_1030 : ∀ t < 1030, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1020 blk_700_450_1020
theorem blk_700_450_1030 : allRange (okAt f_700_450 700 450 1904) 1030 10 = true := by decide +kernel
theorem ok_700_450_1040 : ∀ t < 1040, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1030 blk_700_450_1030
theorem blk_700_450_1040 : allRange (okAt f_700_450 700 450 1904) 1040 10 = true := by decide +kernel
theorem ok_700_450_1050 : ∀ t < 1050, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1040 blk_700_450_1040
theorem blk_700_450_1050 : allRange (okAt f_700_450 700 450 1904) 1050 10 = true := by decide +kernel
theorem ok_700_450_1060 : ∀ t < 1060, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1050 blk_700_450_1050
theorem blk_700_450_1060 : allRange (okAt f_700_450 700 450 1904) 1060 10 = true := by decide +kernel
theorem ok_700_450_1070 : ∀ t < 1070, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1060 blk_700_450_1060
theorem blk_700_450_1070 : allRange (okAt f_700_450 700 450 1904) 1070 10 = true := by decide +kernel
theorem ok_700_450_1080 : ∀ t < 1080, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1070 blk_700_450_1070
theorem blk_700_450_1080 : allRange (okAt f_700_450 700 450 1904) 1080 10 = true := by decide +kernel
theorem ok_700_450_1090 : ∀ t < 1090, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1080 blk_700_450_1080
theorem blk_700_450_1090 : allRange (okAt f_700_450 700 450 1904) 1090 10 = true := by decide +kernel
theorem ok_700_450_1100 : ∀ t < 1100, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1090 blk_700_450_1090
theorem blk_700_450_1100 : allRange (okAt f_700_450 700 450 1904) 1100 10 = true := by decide +kernel
theorem ok_700_450_1110 : ∀ t < 1110, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1100 blk_700_450_1100
theorem blk_700_450_1110 : allRange (okAt f_700_450 700 450 1904) 1110 10 = true := by decide +kernel
theorem ok_700_450_1120 : ∀ t < 1120, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1110 blk_700_450_1110
theorem blk_700_450_1120 : allRange (okAt f_700_450 700 450 1904) 1120 10 = true := by decide +kernel
theorem ok_700_450_1130 : ∀ t < 1130, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1120 blk_700_450_1120
theorem blk_700_450_1130 : allRange (okAt f_700_450 700 450 1904) 1130 10 = true := by decide +kernel
theorem ok_700_450_1140 : ∀ t < 1140, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1130 blk_700_450_1130
theorem blk_700_450_1140 : allRange (okAt f_700_450 700 450 1904) 1140 10 = true := by decide +kernel
theorem ok_700_450_1150 : ∀ t < 1150, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1140 blk_700_450_1140
theorem blk_700_450_1150 : allRange (okAt f_700_450 700 450 1904) 1150 10 = true := by decide +kernel
theorem ok_700_450_1160 : ∀ t < 1160, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1150 blk_700_450_1150
theorem blk_700_450_1160 : allRange (okAt f_700_450 700 450 1904) 1160 10 = true := by decide +kernel
theorem ok_700_450_1170 : ∀ t < 1170, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1160 blk_700_450_1160
theorem blk_700_450_1170 : allRange (okAt f_700_450 700 450 1904) 1170 10 = true := by decide +kernel
theorem ok_700_450_1180 : ∀ t < 1180, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1170 blk_700_450_1170
theorem blk_700_450_1180 : allRange (okAt f_700_450 700 450 1904) 1180 10 = true := by decide +kernel
theorem ok_700_450_1190 : ∀ t < 1190, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1180 blk_700_450_1180
theorem blk_700_450_1190 : allRange (okAt f_700_450 700 450 1904) 1190 10 = true := by decide +kernel
theorem ok_700_450_1200 : ∀ t < 1200, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1190 blk_700_450_1190
theorem blk_700_450_1200 : allRange (okAt f_700_450 700 450 1904) 1200 10 = true := by decide +kernel
theorem ok_700_450_1210 : ∀ t < 1210, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1200 blk_700_450_1200
theorem blk_700_450_1210 : allRange (okAt f_700_450 700 450 1904) 1210 10 = true := by decide +kernel
theorem ok_700_450_1220 : ∀ t < 1220, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1210 blk_700_450_1210
theorem blk_700_450_1220 : allRange (okAt f_700_450 700 450 1904) 1220 10 = true := by decide +kernel
theorem ok_700_450_1230 : ∀ t < 1230, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1220 blk_700_450_1220
theorem blk_700_450_1230 : allRange (okAt f_700_450 700 450 1904) 1230 10 = true := by decide +kernel
theorem ok_700_450_1240 : ∀ t < 1240, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1230 blk_700_450_1230
theorem blk_700_450_1240 : allRange (okAt f_700_450 700 450 1904) 1240 10 = true := by decide +kernel
theorem ok_700_450_1250 : ∀ t < 1250, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1240 blk_700_450_1240
theorem blk_700_450_1250 : allRange (okAt f_700_450 700 450 1904) 1250 10 = true := by decide +kernel
theorem ok_700_450_1260 : ∀ t < 1260, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1250 blk_700_450_1250
theorem blk_700_450_1260 : allRange (okAt f_700_450 700 450 1904) 1260 10 = true := by decide +kernel
theorem ok_700_450_1270 : ∀ t < 1270, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1260 blk_700_450_1260
theorem blk_700_450_1270 : allRange (okAt f_700_450 700 450 1904) 1270 10 = true := by decide +kernel
theorem ok_700_450_1280 : ∀ t < 1280, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1270 blk_700_450_1270
theorem blk_700_450_1280 : allRange (okAt f_700_450 700 450 1904) 1280 10 = true := by decide +kernel
theorem ok_700_450_1290 : ∀ t < 1290, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1280 blk_700_450_1280
theorem blk_700_450_1290 : allRange (okAt f_700_450 700 450 1904) 1290 10 = true := by decide +kernel
theorem ok_700_450_1300 : ∀ t < 1300, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1290 blk_700_450_1290
theorem blk_700_450_1300 : allRange (okAt f_700_450 700 450 1904) 1300 10 = true := by decide +kernel
theorem ok_700_450_1310 : ∀ t < 1310, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1300 blk_700_450_1300
theorem blk_700_450_1310 : allRange (okAt f_700_450 700 450 1904) 1310 10 = true := by decide +kernel
theorem ok_700_450_1320 : ∀ t < 1320, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1310 blk_700_450_1310
theorem blk_700_450_1320 : allRange (okAt f_700_450 700 450 1904) 1320 10 = true := by decide +kernel
theorem ok_700_450_1330 : ∀ t < 1330, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1320 blk_700_450_1320
theorem blk_700_450_1330 : allRange (okAt f_700_450 700 450 1904) 1330 10 = true := by decide +kernel
theorem ok_700_450_1340 : ∀ t < 1340, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1330 blk_700_450_1330
theorem blk_700_450_1340 : allRange (okAt f_700_450 700 450 1904) 1340 10 = true := by decide +kernel
theorem ok_700_450_1350 : ∀ t < 1350, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1340 blk_700_450_1340
theorem blk_700_450_1350 : allRange (okAt f_700_450 700 450 1904) 1350 10 = true := by decide +kernel
theorem ok_700_450_1360 : ∀ t < 1360, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1350 blk_700_450_1350
theorem blk_700_450_1360 : allRange (okAt f_700_450 700 450 1904) 1360 10 = true := by decide +kernel
theorem ok_700_450_1370 : ∀ t < 1370, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1360 blk_700_450_1360
theorem blk_700_450_1370 : allRange (okAt f_700_450 700 450 1904) 1370 10 = true := by decide +kernel
theorem ok_700_450_1380 : ∀ t < 1380, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1370 blk_700_450_1370
theorem blk_700_450_1380 : allRange (okAt f_700_450 700 450 1904) 1380 10 = true := by decide +kernel
theorem ok_700_450_1390 : ∀ t < 1390, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1380 blk_700_450_1380
theorem blk_700_450_1390 : allRange (okAt f_700_450 700 450 1904) 1390 10 = true := by decide +kernel
theorem ok_700_450_1400 : ∀ t < 1400, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1390 blk_700_450_1390
theorem blk_700_450_1400 : allRange (okAt f_700_450 700 450 1904) 1400 10 = true := by decide +kernel
theorem ok_700_450_1410 : ∀ t < 1410, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1400 blk_700_450_1400
theorem blk_700_450_1410 : allRange (okAt f_700_450 700 450 1904) 1410 10 = true := by decide +kernel
theorem ok_700_450_1420 : ∀ t < 1420, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1410 blk_700_450_1410
theorem blk_700_450_1420 : allRange (okAt f_700_450 700 450 1904) 1420 10 = true := by decide +kernel
theorem ok_700_450_1430 : ∀ t < 1430, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1420 blk_700_450_1420
theorem blk_700_450_1430 : allRange (okAt f_700_450 700 450 1904) 1430 10 = true := by decide +kernel
theorem ok_700_450_1440 : ∀ t < 1440, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1430 blk_700_450_1430
theorem blk_700_450_1440 : allRange (okAt f_700_450 700 450 1904) 1440 10 = true := by decide +kernel
theorem ok_700_450_1450 : ∀ t < 1450, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1440 blk_700_450_1440
theorem blk_700_450_1450 : allRange (okAt f_700_450 700 450 1904) 1450 10 = true := by decide +kernel
theorem ok_700_450_1460 : ∀ t < 1460, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1450 blk_700_450_1450
theorem blk_700_450_1460 : allRange (okAt f_700_450 700 450 1904) 1460 10 = true := by decide +kernel
theorem ok_700_450_1470 : ∀ t < 1470, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1460 blk_700_450_1460
theorem blk_700_450_1470 : allRange (okAt f_700_450 700 450 1904) 1470 10 = true := by decide +kernel
theorem ok_700_450_1480 : ∀ t < 1480, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1470 blk_700_450_1470
theorem blk_700_450_1480 : allRange (okAt f_700_450 700 450 1904) 1480 10 = true := by decide +kernel
theorem ok_700_450_1490 : ∀ t < 1490, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1480 blk_700_450_1480
theorem blk_700_450_1490 : allRange (okAt f_700_450 700 450 1904) 1490 10 = true := by decide +kernel
theorem ok_700_450_1500 : ∀ t < 1500, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1490 blk_700_450_1490
theorem blk_700_450_1500 : allRange (okAt f_700_450 700 450 1904) 1500 10 = true := by decide +kernel
theorem ok_700_450_1510 : ∀ t < 1510, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1500 blk_700_450_1500
theorem blk_700_450_1510 : allRange (okAt f_700_450 700 450 1904) 1510 10 = true := by decide +kernel
theorem ok_700_450_1520 : ∀ t < 1520, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1510 blk_700_450_1510
theorem blk_700_450_1520 : allRange (okAt f_700_450 700 450 1904) 1520 10 = true := by decide +kernel
theorem ok_700_450_1530 : ∀ t < 1530, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1520 blk_700_450_1520
theorem blk_700_450_1530 : allRange (okAt f_700_450 700 450 1904) 1530 10 = true := by decide +kernel
theorem ok_700_450_1540 : ∀ t < 1540, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1530 blk_700_450_1530
theorem blk_700_450_1540 : allRange (okAt f_700_450 700 450 1904) 1540 10 = true := by decide +kernel
theorem ok_700_450_1550 : ∀ t < 1550, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1540 blk_700_450_1540
theorem blk_700_450_1550 : allRange (okAt f_700_450 700 450 1904) 1550 10 = true := by decide +kernel
theorem ok_700_450_1560 : ∀ t < 1560, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1550 blk_700_450_1550
theorem blk_700_450_1560 : allRange (okAt f_700_450 700 450 1904) 1560 10 = true := by decide +kernel
theorem ok_700_450_1570 : ∀ t < 1570, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1560 blk_700_450_1560
theorem blk_700_450_1570 : allRange (okAt f_700_450 700 450 1904) 1570 10 = true := by decide +kernel
theorem ok_700_450_1580 : ∀ t < 1580, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1570 blk_700_450_1570
theorem blk_700_450_1580 : allRange (okAt f_700_450 700 450 1904) 1580 10 = true := by decide +kernel
theorem ok_700_450_1590 : ∀ t < 1590, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1580 blk_700_450_1580
theorem blk_700_450_1590 : allRange (okAt f_700_450 700 450 1904) 1590 10 = true := by decide +kernel
theorem ok_700_450_1600 : ∀ t < 1600, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1590 blk_700_450_1590
theorem blk_700_450_1600 : allRange (okAt f_700_450 700 450 1904) 1600 10 = true := by decide +kernel
theorem ok_700_450_1610 : ∀ t < 1610, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1600 blk_700_450_1600
theorem blk_700_450_1610 : allRange (okAt f_700_450 700 450 1904) 1610 10 = true := by decide +kernel
theorem ok_700_450_1620 : ∀ t < 1620, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1610 blk_700_450_1610
theorem blk_700_450_1620 : allRange (okAt f_700_450 700 450 1904) 1620 10 = true := by decide +kernel
theorem ok_700_450_1630 : ∀ t < 1630, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1620 blk_700_450_1620
theorem blk_700_450_1630 : allRange (okAt f_700_450 700 450 1904) 1630 10 = true := by decide +kernel
theorem ok_700_450_1640 : ∀ t < 1640, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1630 blk_700_450_1630
theorem blk_700_450_1640 : allRange (okAt f_700_450 700 450 1904) 1640 10 = true := by decide +kernel
theorem ok_700_450_1650 : ∀ t < 1650, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1640 blk_700_450_1640
theorem blk_700_450_1650 : allRange (okAt f_700_450 700 450 1904) 1650 10 = true := by decide +kernel
theorem ok_700_450_1660 : ∀ t < 1660, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1650 blk_700_450_1650
theorem blk_700_450_1660 : allRange (okAt f_700_450 700 450 1904) 1660 10 = true := by decide +kernel
theorem ok_700_450_1670 : ∀ t < 1670, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1660 blk_700_450_1660
theorem blk_700_450_1670 : allRange (okAt f_700_450 700 450 1904) 1670 10 = true := by decide +kernel
theorem ok_700_450_1680 : ∀ t < 1680, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1670 blk_700_450_1670
theorem blk_700_450_1680 : allRange (okAt f_700_450 700 450 1904) 1680 10 = true := by decide +kernel
theorem ok_700_450_1690 : ∀ t < 1690, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1680 blk_700_450_1680
theorem blk_700_450_1690 : allRange (okAt f_700_450 700 450 1904) 1690 10 = true := by decide +kernel
theorem ok_700_450_1700 : ∀ t < 1700, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1690 blk_700_450_1690
theorem blk_700_450_1700 : allRange (okAt f_700_450 700 450 1904) 1700 10 = true := by decide +kernel
theorem ok_700_450_1710 : ∀ t < 1710, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1700 blk_700_450_1700
theorem blk_700_450_1710 : allRange (okAt f_700_450 700 450 1904) 1710 10 = true := by decide +kernel
theorem ok_700_450_1720 : ∀ t < 1720, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1710 blk_700_450_1710
theorem blk_700_450_1720 : allRange (okAt f_700_450 700 450 1904) 1720 10 = true := by decide +kernel
theorem ok_700_450_1730 : ∀ t < 1730, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1720 blk_700_450_1720
theorem blk_700_450_1730 : allRange (okAt f_700_450 700 450 1904) 1730 10 = true := by decide +kernel
theorem ok_700_450_1740 : ∀ t < 1740, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1730 blk_700_450_1730
theorem blk_700_450_1740 : allRange (okAt f_700_450 700 450 1904) 1740 10 = true := by decide +kernel
theorem ok_700_450_1750 : ∀ t < 1750, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1740 blk_700_450_1740
theorem blk_700_450_1750 : allRange (okAt f_700_450 700 450 1904) 1750 10 = true := by decide +kernel
theorem ok_700_450_1760 : ∀ t < 1760, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1750 blk_700_450_1750
theorem blk_700_450_1760 : allRange (okAt f_700_450 700 450 1904) 1760 10 = true := by decide +kernel
theorem ok_700_450_1770 : ∀ t < 1770, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1760 blk_700_450_1760
theorem blk_700_450_1770 : allRange (okAt f_700_450 700 450 1904) 1770 10 = true := by decide +kernel
theorem ok_700_450_1780 : ∀ t < 1780, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1770 blk_700_450_1770
theorem blk_700_450_1780 : allRange (okAt f_700_450 700 450 1904) 1780 10 = true := by decide +kernel
theorem ok_700_450_1790 : ∀ t < 1790, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1780 blk_700_450_1780
theorem blk_700_450_1790 : allRange (okAt f_700_450 700 450 1904) 1790 10 = true := by decide +kernel
theorem ok_700_450_1800 : ∀ t < 1800, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1790 blk_700_450_1790
theorem blk_700_450_1800 : allRange (okAt f_700_450 700 450 1904) 1800 10 = true := by decide +kernel
theorem ok_700_450_1810 : ∀ t < 1810, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1800 blk_700_450_1800
theorem blk_700_450_1810 : allRange (okAt f_700_450 700 450 1904) 1810 10 = true := by decide +kernel
theorem ok_700_450_1820 : ∀ t < 1820, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1810 blk_700_450_1810
theorem blk_700_450_1820 : allRange (okAt f_700_450 700 450 1904) 1820 10 = true := by decide +kernel
theorem ok_700_450_1830 : ∀ t < 1830, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1820 blk_700_450_1820
theorem blk_700_450_1830 : allRange (okAt f_700_450 700 450 1904) 1830 10 = true := by decide +kernel
theorem ok_700_450_1840 : ∀ t < 1840, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1830 blk_700_450_1830
theorem blk_700_450_1840 : allRange (okAt f_700_450 700 450 1904) 1840 10 = true := by decide +kernel
theorem ok_700_450_1850 : ∀ t < 1850, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1840 blk_700_450_1840
theorem blk_700_450_1850 : allRange (okAt f_700_450 700 450 1904) 1850 10 = true := by decide +kernel
theorem ok_700_450_1860 : ∀ t < 1860, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1850 blk_700_450_1850
theorem blk_700_450_1860 : allRange (okAt f_700_450 700 450 1904) 1860 10 = true := by decide +kernel
theorem ok_700_450_1870 : ∀ t < 1870, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1860 blk_700_450_1860
theorem blk_700_450_1870 : allRange (okAt f_700_450 700 450 1904) 1870 10 = true := by decide +kernel
theorem ok_700_450_1880 : ∀ t < 1880, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1870 blk_700_450_1870
theorem blk_700_450_1880 : allRange (okAt f_700_450 700 450 1904) 1880 10 = true := by decide +kernel
theorem ok_700_450_1890 : ∀ t < 1890, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1880 blk_700_450_1880
theorem blk_700_450_1890 : allRange (okAt f_700_450 700 450 1904) 1890 10 = true := by decide +kernel
theorem ok_700_450_1900 : ∀ t < 1900, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1890 blk_700_450_1890
theorem blk_700_450_1900 : allRange (okAt f_700_450 700 450 1904) 1900 4 = true := by decide +kernel
theorem ok_700_450_1904 : ∀ t < 1904, okAt f_700_450 700 450 1904 t = true := allRange_extend ok_700_450_1900 blk_700_450_1900

theorem coil_700_450 : ∃ v : ℕ → Fin 700 → Bool, IsCoil 450 1904 v :=
  exists_coil_of_check f_700_450 450 1904 (by norm_num) ok_700_450_1904 (by decide +kernel)

/-- K(700,450) = 1904  (= 4k+2l+6, l = 49; code: fam10_700_450_1904.txt) -/
theorem K_700_450 : IsMaxLength 700 450 1904 :=
  isMaxLength_of_chord coil_700_450 (by norm_num) 901 (by norm_num) (by norm_num) (by decide +kernel)


end Coil
