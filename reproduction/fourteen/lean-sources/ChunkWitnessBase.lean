import FiniteWitnesses

namespace FinitePolygonWitnesses

def point14 : Nat → Pt
  | 0 => (0, -4000005000001)
  | 1 => (0, 0)
  | 2 => (198313, -413703)
  | 3 => (217163, -523272)
  | 4 => (281997, -585571)
  | 5 => (292094, -1946865)
  | 6 => (292095, -2000000)
  | 7 => (345830, -1359865)
  | 8 => (353575, -1344581)
  | 9 => (408919, -1609494)
  | 10 => (408920, -598328)
  | 11 => (716722, -716031)
  | 12 => (747409, -636573)
  | 13 => (1000000, 0)
  | _ => (0, 0)

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem general_position_14 : (triples 14).all (noncollinear point14) = true := by decide +kernel
def bad14 : List Nat := [23, 1031, 2055, 4103, 8199, 27, 1035, 2059, 4107, 8203, 1043, 2067, 4115, 8211, 163, 291, 547, 1059, 2083, 4131, 8227, 195, 323, 579, 1091, 2115, 4163, 8259, 387, 1155, 2179, 4227, 8323, 1283, 2307, 4355, 8451, 1539, 2563, 4611, 8707, 3075, 5123, 9219, 6147, 10243, 12291, 29, 525, 1037, 2061, 4109, 8205, 1045, 2069, 4117, 8213, 165, 293, 549, 1061, 2085, 4133, 8229, 197, 325, 581, 1093, 2117, 4165, 8261, 389, 645, 1157, 2181, 4229, 8325, 773, 1285, 2309, 4357, 8453, 1541, 2565, 4613, 8709, 3077, 5125, 9221, 6149, 10245, 12293, 1049, 2073, 4121, 8217, 169, 297, 553, 1065, 2089, 4137, 8233, 201, 329, 585, 1097, 2121, 4169, 8265, 393, 649, 1161, 2185, 4233, 8329, 777, 1289, 2313, 4361, 8457, 1545, 2569, 4617, 8713, 3081, 5129, 9225, 6153, 10249, 12297, 177, 305, 561, 1073, 2097, 4145, 8241, 209, 337, 593, 1105, 2129, 4177, 8273, 401, 657, 1169, 2193, 4241, 8337, 785, 1297, 2321, 4369, 8465, 1553, 2577, 4625, 8721, 9233, 6161, 10257, 12305, 225, 353, 609, 1121, 2145, 4193, 8289, 1185, 1313, 1569, 2593, 1217, 1345, 1601, 1409, 8577, 1665, 2689, 4737, 8833, 6273, 10369, 12417, 1793, 2817, 4865, 8961, 6401, 10497, 12545, 7169, 11265, 13313, 30, 526, 1038, 2062, 4110, 8206, 54, 86, 150, 278, 534, 1062, 2086, 4134, 8230, 1094, 2118, 4166, 8262, 646, 1158, 2182, 4230, 8326, 774, 1286, 2310, 4358, 8454, 1542, 2566, 4614, 8710, 58, 90, 154, 282, 538, 1066, 2090, 4138, 8234, 1098, 2122, 4170, 8266, 650, 1162, 2186, 4234, 8330, 778, 1290, 2314, 4362, 8458, 1546, 2570, 4618, 8714, 1074, 2098, 4146, 8242, 1106, 2130, 4178, 8274, 658, 1170, 2194, 4242, 8338, 786, 1298, 2322, 4370, 8466, 1554, 2578, 4626, 8722, 3090, 5138, 226, 354, 610, 1122, 2146, 4194, 8290, 418, 2210, 4258, 8354, 2338, 4386, 8482, 4642, 8738, 3106, 5154, 9250, 6178, 10274, 12322, 450, 2242, 4290, 8386, 2370, 4418, 8514, 2626, 4674, 8770, 3138, 5186, 9282, 6210, 10306, 12354, 898, 2434, 4482, 1666, 2690, 4738, 8834, 3202, 5250, 9346, 1794, 2818, 4866, 8962, 3330, 5378, 9474, 3586, 5634, 9730, 6658, 10754, 12802, 14338, 60, 92, 156, 284, 556, 1068, 2092, 4140, 8236, 588, 1100, 2124, 4172, 8268, 652, 1164, 2188, 4236, 8332, 780, 1292, 2316, 4364, 8460, 1076, 2100, 4148, 8244, 1108, 2132, 4180, 8276, 1172, 2196, 4244, 8340, 1300, 2324, 4372, 8468, 1556, 2580, 4628, 8724, 3092, 5140, 228, 356, 612, 1124, 2148, 4196, 8292, 420, 676, 2212, 4260, 8356, 804, 2340, 4388, 8484, 4644, 8740, 3108, 5156, 9252, 6180, 10276, 12324, 452, 708, 2244, 4292, 8388, 836, 2372, 4420, 8516, 2628, 4676, 8772, 3140, 5188, 9284, 6212, 10308, 12356, 900, 2436, 4484, 3204, 5252, 9348, 3332, 5380, 9476, 3588, 5636, 9732, 6660, 10756, 12804, 14340, 1080, 2104, 4152, 8248, 1112, 2136, 4184, 8280, 1176, 2200, 4248, 8344, 1304, 2328, 4376, 8472, 1560, 2584, 4632, 8728, 3096, 5144, 232, 360, 616, 1128, 2152, 4200, 8296, 424, 680, 2216, 4264, 8360, 808, 2344, 4392, 8488, 4648, 8744, 3112, 5160, 9256, 6184, 10280, 12328, 456, 712, 2248, 4296, 8392, 840, 2376, 4424, 8520, 2632, 4680, 8776, 3144, 5192, 9288, 6216, 10312, 12360, 904, 2440, 4488, 3208, 5256, 9352, 3336, 5384, 9480, 3592, 5640, 9736, 6664, 10760, 12808, 14344, 240, 368, 624, 1136, 2160, 4208, 8304, 432, 688, 2224, 4272, 8368, 816, 2352, 4400, 8496, 4656, 8752, 9264, 6192, 10288, 12336, 464, 720, 2256, 4304, 8400, 848, 2384, 4432, 8528, 2640, 4688, 8784, 9296, 6224, 10320, 12368, 912, 2448, 4496, 9360, 9488, 9744, 6672, 10768, 12816, 11280, 13328, 14352, 2656, 1440, 8608, 1696, 4768, 8864, 3232, 5280, 9376, 6304, 10400, 12448, 1824, 4896, 8992, 3360, 5408, 9504, 6432, 10528, 12576, 5664, 9760, 6688, 10784, 7200, 11296, 13344, 1472, 8640, 1728, 2752, 4800, 8896, 3264, 5312, 9408, 6336, 10432, 12480, 1856, 2880, 4928, 9024, 3392, 5440, 9536, 6464, 10560, 12608, 3648, 5696, 9792, 7232, 11328, 13376, 1920, 9088, 3456, 5504, 10624, 12672, 6784, 10880, 12928, 14464, 6912, 11008, 13056, 14592, 7680, 11776, 13824, 15360]
theorem bad14_eq : forbidden point14 14 = bad14 := by decide +kernel
def passes14 (m : Nat) := bad14.all (fun q => (m &&& q) != q)
def valid0 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 24, 25, 26, 28, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 56, 57, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 88, 89, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 120, 121]
theorem chunk0 : (List.range' 0 128).filter passes14 = valid0 := by decide +kernel
def valid1 : List Nat := [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 152, 153, 160, 161, 162, 164, 166, 168, 170, 172, 174, 176, 178, 180, 184, 192, 193, 194, 196, 198, 200, 202, 204, 206, 208, 210, 212, 216, 224]
theorem chunk1 : (List.range' 128 128).filter passes14 = valid1 := by decide +kernel
def valid2 : List Nat := [256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 280, 281, 288, 289, 290, 292, 294, 296, 298, 300, 302, 304, 306, 308, 312, 320, 321, 322, 324, 326, 328, 330, 332, 334, 336, 338, 340, 344, 352]
theorem chunk2 : (List.range' 256 128).filter passes14 = valid2 := by decide +kernel
def valid3 : List Nat := [384, 385, 386, 388, 390, 392, 394, 396, 398, 400, 402, 404, 408, 416, 417, 448, 449, 480]
theorem chunk3 : (List.range' 384 128).filter passes14 = valid3 := by decide +kernel
def valid4 : List Nat := [512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 528, 529, 530, 531, 532, 533, 536, 537, 540, 544, 545, 546, 548, 550, 552, 554, 560, 562, 564, 568, 576, 577, 578, 580, 582, 584, 586, 592, 594, 596, 600, 608]
theorem chunk4 : (List.range' 512 128).filter passes14 = valid4 := by decide +kernel
def valid5 : List Nat := [640, 641, 642, 643, 644, 648, 656, 660, 664, 672, 673, 674, 704, 705, 706, 736]
theorem chunk5 : (List.range' 640 128).filter passes14 = valid5 := by decide +kernel
def valid6 : List Nat := [768, 769, 770, 771, 772, 776, 784, 788, 792, 800, 801, 802, 832, 833, 834, 864]
theorem chunk6 : (List.range' 768 128).filter passes14 = valid6 := by decide +kernel
def valid7 : List Nat := [896, 897, 928, 929, 960, 961, 992]
theorem chunk7 : (List.range' 896 128).filter passes14 = valid7 := by decide +kernel
def valid8 : List Nat := [1024, 1025, 1026, 1027, 1028, 1029, 1030, 1032, 1033, 1034, 1036, 1040, 1041, 1042, 1044, 1046, 1048, 1050, 1052, 1056, 1057, 1058, 1060, 1064, 1072, 1088, 1089, 1090, 1092, 1096, 1104, 1120]
theorem chunk8 : (List.range' 1024 128).filter passes14 = valid8 := by decide +kernel
def valid9 : List Nat := [1152, 1153, 1154, 1156, 1160, 1168, 1184, 1186, 1188, 1192, 1200, 1216, 1218, 1220, 1224, 1232, 1248]
theorem chunk9 : (List.range' 1152 128).filter passes14 = valid9 := by decide +kernel
def valid10 : List Nat := [1280, 1281, 1282, 1284, 1288, 1296, 1312, 1314, 1316, 1320, 1328, 1344, 1346, 1348, 1352, 1360, 1376]
theorem chunk10 : (List.range' 1280 128).filter passes14 = valid10 := by decide +kernel
def valid11 : List Nat := [1408, 1410, 1412, 1416, 1424]
theorem chunk11 : (List.range' 1408 128).filter passes14 = valid11 := by decide +kernel
def valid12 : List Nat := [1536, 1537, 1538, 1540, 1544, 1548, 1552, 1568, 1570, 1572, 1576, 1584, 1600, 1602, 1604, 1608, 1616, 1632]
theorem chunk12 : (List.range' 1536 128).filter passes14 = valid12 := by decide +kernel
def valid13 : List Nat := [1664, 1668, 1672, 1680]
theorem chunk13 : (List.range' 1664 128).filter passes14 = valid13 := by decide +kernel
def valid14 : List Nat := [1792, 1796, 1800, 1808]
theorem chunk14 : (List.range' 1792 128).filter passes14 = valid14 := by decide +kernel
def valid15 : List Nat := []
theorem chunk15 : (List.range' 1920 128).filter passes14 = valid15 := by decide +kernel
def valid16 : List Nat := [2048, 2049, 2050, 2051, 2052, 2053, 2054, 2056, 2057, 2058, 2060, 2064, 2065, 2066, 2068, 2070, 2072, 2074, 2076, 2080, 2081, 2082, 2084, 2088, 2096, 2112, 2113, 2114, 2116, 2120, 2128, 2144]
theorem chunk16 : (List.range' 2048 128).filter passes14 = valid16 := by decide +kernel
def valid17 : List Nat := [2176, 2177, 2178, 2180, 2184, 2192, 2208, 2209, 2240, 2241, 2272]
theorem chunk17 : (List.range' 2176 128).filter passes14 = valid17 := by decide +kernel
def valid18 : List Nat := [2304, 2305, 2306, 2308, 2312, 2320, 2336, 2337, 2368, 2369, 2400]
theorem chunk18 : (List.range' 2304 128).filter passes14 = valid18 := by decide +kernel
def valid19 : List Nat := [2432, 2433, 2464, 2465, 2496, 2497, 2528]
theorem chunk19 : (List.range' 2432 128).filter passes14 = valid19 := by decide +kernel
def valid20 : List Nat := [2560, 2561, 2562, 2564, 2568, 2572, 2576, 2592, 2594, 2596, 2600, 2608, 2624, 2625]
theorem chunk20 : (List.range' 2560 128).filter passes14 = valid20 := by decide +kernel
def valid21 : List Nat := [2688, 2692, 2696, 2704, 2720]
theorem chunk21 : (List.range' 2688 128).filter passes14 = valid21 := by decide +kernel
def valid22 : List Nat := [2816, 2820, 2824, 2832, 2848]
theorem chunk22 : (List.range' 2816 128).filter passes14 = valid22 := by decide +kernel
def valid23 : List Nat := [2944, 2976]
theorem chunk23 : (List.range' 2944 128).filter passes14 = valid23 := by decide +kernel
def valid24 : List Nat := [3072, 3073, 3074, 3076, 3078, 3080, 3082, 3084, 3088, 3089, 3104, 3105, 3120, 3136, 3137, 3152, 3168]
theorem chunk24 : (List.range' 3072 128).filter passes14 = valid24 := by decide +kernel
def valid25 : List Nat := [3200, 3201, 3216]
theorem chunk25 : (List.range' 3200 128).filter passes14 = valid25 := by decide +kernel
def valid26 : List Nat := [3328, 3329, 3344]
theorem chunk26 : (List.range' 3328 128).filter passes14 = valid26 := by decide +kernel
def valid27 : List Nat := []
theorem chunk27 : (List.range' 3456 128).filter passes14 = valid27 := by decide +kernel
def valid28 : List Nat := [3584, 3585, 3600, 3616, 3632]
theorem chunk28 : (List.range' 3584 128).filter passes14 = valid28 := by decide +kernel
def valid29 : List Nat := [3712, 3728]
theorem chunk29 : (List.range' 3712 128).filter passes14 = valid29 := by decide +kernel
def valid30 : List Nat := [3840, 3856]
theorem chunk30 : (List.range' 3840 128).filter passes14 = valid30 := by decide +kernel
def valid31 : List Nat := []
theorem chunk31 : (List.range' 3968 128).filter passes14 = valid31 := by decide +kernel
def valid32 : List Nat := [4096, 4097, 4098, 4099, 4100, 4101, 4102, 4104, 4105, 4106, 4108, 4112, 4113, 4114, 4116, 4118, 4120, 4122, 4124, 4128, 4129, 4130, 4132, 4136, 4144, 4160, 4161, 4162, 4164, 4168, 4176, 4192]
theorem chunk32 : (List.range' 4096 128).filter passes14 = valid32 := by decide +kernel
def valid33 : List Nat := [4224, 4225, 4226, 4228, 4232, 4240, 4256, 4257, 4288, 4289, 4320]
theorem chunk33 : (List.range' 4224 128).filter passes14 = valid33 := by decide +kernel
def valid34 : List Nat := [4352, 4353, 4354, 4356, 4360, 4368, 4384, 4385, 4416, 4417, 4448]
theorem chunk34 : (List.range' 4352 128).filter passes14 = valid34 := by decide +kernel
def valid35 : List Nat := [4480, 4481, 4512, 4513, 4544, 4545, 4576]
theorem chunk35 : (List.range' 4480 128).filter passes14 = valid35 := by decide +kernel
def valid36 : List Nat := [4608, 4609, 4610, 4612, 4616, 4620, 4624, 4640, 4641, 4672, 4673, 4704]
theorem chunk36 : (List.range' 4608 128).filter passes14 = valid36 := by decide +kernel
def valid37 : List Nat := [4736, 4740, 4744, 4752]
theorem chunk37 : (List.range' 4736 128).filter passes14 = valid37 := by decide +kernel
def valid38 : List Nat := [4864, 4868, 4872, 4880]
theorem chunk38 : (List.range' 4864 128).filter passes14 = valid38 := by decide +kernel
def valid39 : List Nat := [4992]
theorem chunk39 : (List.range' 4992 128).filter passes14 = valid39 := by decide +kernel
def valid40 : List Nat := [5120, 5121, 5122, 5124, 5126, 5128, 5130, 5132, 5136, 5137, 5152, 5153, 5168, 5184, 5185, 5200, 5216]
theorem chunk40 : (List.range' 5120 128).filter passes14 = valid40 := by decide +kernel
def valid41 : List Nat := [5248, 5249, 5264]
theorem chunk41 : (List.range' 5248 128).filter passes14 = valid41 := by decide +kernel
def valid42 : List Nat := [5376, 5377, 5392]
theorem chunk42 : (List.range' 5376 128).filter passes14 = valid42 := by decide +kernel
def valid43 : List Nat := []
theorem chunk43 : (List.range' 5504 128).filter passes14 = valid43 := by decide +kernel
def valid44 : List Nat := [5632, 5633, 5648]
theorem chunk44 : (List.range' 5632 128).filter passes14 = valid44 := by decide +kernel
def valid45 : List Nat := [5760, 5776]
theorem chunk45 : (List.range' 5760 128).filter passes14 = valid45 := by decide +kernel
def valid46 : List Nat := [5888, 5904]
theorem chunk46 : (List.range' 5888 128).filter passes14 = valid46 := by decide +kernel
def valid47 : List Nat := []
theorem chunk47 : (List.range' 6016 128).filter passes14 = valid47 := by decide +kernel
def valid48 : List Nat := [6144, 6145, 6146, 6148, 6150, 6152, 6154, 6156, 6160, 6162, 6164, 6166, 6168, 6170, 6172, 6176, 6177, 6208, 6209, 6240]
theorem chunk48 : (List.range' 6144 128).filter passes14 = valid48 := by decide +kernel
def valid49 : List Nat := [6272, 6274, 6276, 6280, 6288]
theorem chunk49 : (List.range' 6272 128).filter passes14 = valid49 := by decide +kernel
def valid50 : List Nat := [6400, 6402, 6404, 6408, 6416]
theorem chunk50 : (List.range' 6400 128).filter passes14 = valid50 := by decide +kernel
def valid51 : List Nat := [6528]
theorem chunk51 : (List.range' 6528 128).filter passes14 = valid51 := by decide +kernel
def valid52 : List Nat := [6656, 6657, 6720, 6721]
theorem chunk52 : (List.range' 6656 128).filter passes14 = valid52 := by decide +kernel
def valid53 : List Nat := []
theorem chunk53 : (List.range' 6784 128).filter passes14 = valid53 := by decide +kernel
def valid54 : List Nat := []
theorem chunk54 : (List.range' 6912 128).filter passes14 = valid54 := by decide +kernel
def valid55 : List Nat := []
theorem chunk55 : (List.range' 7040 128).filter passes14 = valid55 := by decide +kernel
def valid56 : List Nat := [7168, 7170, 7172, 7174, 7176, 7178, 7180, 7184]
theorem chunk56 : (List.range' 7168 128).filter passes14 = valid56 := by decide +kernel
def valid57 : List Nat := [7296, 7312]
theorem chunk57 : (List.range' 7296 128).filter passes14 = valid57 := by decide +kernel
def valid58 : List Nat := [7424, 7440]
theorem chunk58 : (List.range' 7424 128).filter passes14 = valid58 := by decide +kernel
def valid59 : List Nat := []
theorem chunk59 : (List.range' 7552 128).filter passes14 = valid59 := by decide +kernel
def valid60 : List Nat := []
theorem chunk60 : (List.range' 7680 128).filter passes14 = valid60 := by decide +kernel
def valid61 : List Nat := []
theorem chunk61 : (List.range' 7808 128).filter passes14 = valid61 := by decide +kernel
def valid62 : List Nat := []
theorem chunk62 : (List.range' 7936 128).filter passes14 = valid62 := by decide +kernel
def valid63 : List Nat := []
theorem chunk63 : (List.range' 8064 128).filter passes14 = valid63 := by decide +kernel
def valid64 : List Nat := [8192, 8193, 8194, 8195, 8196, 8197, 8198, 8200, 8201, 8202, 8204, 8208, 8209, 8210, 8212, 8214, 8216, 8218, 8220, 8224, 8225, 8226, 8228, 8232, 8240, 8256, 8257, 8258, 8260, 8264, 8272, 8288]
theorem chunk64 : (List.range' 8192 128).filter passes14 = valid64 := by decide +kernel
def valid65 : List Nat := [8320, 8321, 8322, 8324, 8328, 8336, 8352, 8353, 8384, 8385, 8416]
theorem chunk65 : (List.range' 8320 128).filter passes14 = valid65 := by decide +kernel
def valid66 : List Nat := [8448, 8449, 8450, 8452, 8456, 8464, 8480, 8481, 8512, 8513, 8544]
theorem chunk66 : (List.range' 8448 128).filter passes14 = valid66 := by decide +kernel
def valid67 : List Nat := [8576, 8578, 8580, 8584, 8592]
theorem chunk67 : (List.range' 8576 128).filter passes14 = valid67 := by decide +kernel
def valid68 : List Nat := [8704, 8705, 8706, 8708, 8712, 8716, 8720, 8736, 8737, 8768, 8769, 8800]
theorem chunk68 : (List.range' 8704 128).filter passes14 = valid68 := by decide +kernel
def valid69 : List Nat := [8832, 8836, 8840, 8848]
theorem chunk69 : (List.range' 8832 128).filter passes14 = valid69 := by decide +kernel
def valid70 : List Nat := [8960, 8964, 8968, 8976]
theorem chunk70 : (List.range' 8960 128).filter passes14 = valid70 := by decide +kernel
def valid71 : List Nat := []
theorem chunk71 : (List.range' 9088 128).filter passes14 = valid71 := by decide +kernel
def valid72 : List Nat := [9216, 9217, 9218, 9220, 9222, 9224, 9226, 9228, 9232, 9234, 9236, 9238, 9240, 9242, 9244, 9248, 9249, 9280, 9281, 9312]
theorem chunk72 : (List.range' 9216 128).filter passes14 = valid72 := by decide +kernel
def valid73 : List Nat := [9344, 9345]
theorem chunk73 : (List.range' 9344 128).filter passes14 = valid73 := by decide +kernel
def valid74 : List Nat := [9472, 9473]
theorem chunk74 : (List.range' 9472 128).filter passes14 = valid74 := by decide +kernel
def valid75 : List Nat := [9600]
theorem chunk75 : (List.range' 9600 128).filter passes14 = valid75 := by decide +kernel
def valid76 : List Nat := [9728, 9729]
theorem chunk76 : (List.range' 9728 128).filter passes14 = valid76 := by decide +kernel
def valid77 : List Nat := [9856]
theorem chunk77 : (List.range' 9856 128).filter passes14 = valid77 := by decide +kernel
def valid78 : List Nat := [9984]
theorem chunk78 : (List.range' 9984 128).filter passes14 = valid78 := by decide +kernel
def valid79 : List Nat := []
theorem chunk79 : (List.range' 10112 128).filter passes14 = valid79 := by decide +kernel
def valid80 : List Nat := [10240, 10241, 10242, 10244, 10246, 10248, 10250, 10252, 10256, 10258, 10260, 10262, 10264, 10266, 10268, 10272, 10273, 10304, 10305, 10336]
theorem chunk80 : (List.range' 10240 128).filter passes14 = valid80 := by decide +kernel
def valid81 : List Nat := [10368, 10370, 10372, 10376, 10384]
theorem chunk81 : (List.range' 10368 128).filter passes14 = valid81 := by decide +kernel
def valid82 : List Nat := [10496, 10498, 10500, 10504, 10512]
theorem chunk82 : (List.range' 10496 128).filter passes14 = valid82 := by decide +kernel
def valid83 : List Nat := []
theorem chunk83 : (List.range' 10624 128).filter passes14 = valid83 := by decide +kernel
def valid84 : List Nat := [10752, 10753, 10816, 10817]
theorem chunk84 : (List.range' 10752 128).filter passes14 = valid84 := by decide +kernel
def valid85 : List Nat := []
theorem chunk85 : (List.range' 10880 128).filter passes14 = valid85 := by decide +kernel
def valid86 : List Nat := []
theorem chunk86 : (List.range' 11008 128).filter passes14 = valid86 := by decide +kernel
def valid87 : List Nat := []
theorem chunk87 : (List.range' 11136 128).filter passes14 = valid87 := by decide +kernel
def valid88 : List Nat := [11264, 11266, 11268, 11270, 11272, 11274, 11276]
theorem chunk88 : (List.range' 11264 128).filter passes14 = valid88 := by decide +kernel
def valid89 : List Nat := [11392]
theorem chunk89 : (List.range' 11392 128).filter passes14 = valid89 := by decide +kernel
def valid90 : List Nat := [11520]
theorem chunk90 : (List.range' 11520 128).filter passes14 = valid90 := by decide +kernel
def valid91 : List Nat := []
theorem chunk91 : (List.range' 11648 128).filter passes14 = valid91 := by decide +kernel
def valid92 : List Nat := []
theorem chunk92 : (List.range' 11776 128).filter passes14 = valid92 := by decide +kernel
def valid93 : List Nat := []
theorem chunk93 : (List.range' 11904 128).filter passes14 = valid93 := by decide +kernel
def valid94 : List Nat := []
theorem chunk94 : (List.range' 12032 128).filter passes14 = valid94 := by decide +kernel
def valid95 : List Nat := []
theorem chunk95 : (List.range' 12160 128).filter passes14 = valid95 := by decide +kernel
def valid96 : List Nat := [12288, 12289, 12290, 12292, 12294, 12296, 12298, 12300, 12304, 12306, 12308, 12310, 12312, 12314, 12316, 12320, 12321, 12352, 12353, 12384]
theorem chunk96 : (List.range' 12288 128).filter passes14 = valid96 := by decide +kernel
def valid97 : List Nat := [12416, 12418, 12420, 12424, 12432]
theorem chunk97 : (List.range' 12416 128).filter passes14 = valid97 := by decide +kernel
def valid98 : List Nat := [12544, 12546, 12548, 12552, 12560]
theorem chunk98 : (List.range' 12544 128).filter passes14 = valid98 := by decide +kernel
def valid99 : List Nat := []
theorem chunk99 : (List.range' 12672 128).filter passes14 = valid99 := by decide +kernel
def valid100 : List Nat := [12800, 12801, 12832, 12833, 12864, 12865, 12896]
theorem chunk100 : (List.range' 12800 128).filter passes14 = valid100 := by decide +kernel
def valid101 : List Nat := []
theorem chunk101 : (List.range' 12928 128).filter passes14 = valid101 := by decide +kernel
def valid102 : List Nat := []
theorem chunk102 : (List.range' 13056 128).filter passes14 = valid102 := by decide +kernel
def valid103 : List Nat := []
theorem chunk103 : (List.range' 13184 128).filter passes14 = valid103 := by decide +kernel
def valid104 : List Nat := [13312, 13314, 13316, 13318, 13320, 13322, 13324]
theorem chunk104 : (List.range' 13312 128).filter passes14 = valid104 := by decide +kernel
def valid105 : List Nat := [13440]
theorem chunk105 : (List.range' 13440 128).filter passes14 = valid105 := by decide +kernel
def valid106 : List Nat := [13568]
theorem chunk106 : (List.range' 13568 128).filter passes14 = valid106 := by decide +kernel
def valid107 : List Nat := []
theorem chunk107 : (List.range' 13696 128).filter passes14 = valid107 := by decide +kernel
def valid108 : List Nat := []
theorem chunk108 : (List.range' 13824 128).filter passes14 = valid108 := by decide +kernel
def valid109 : List Nat := []
theorem chunk109 : (List.range' 13952 128).filter passes14 = valid109 := by decide +kernel
def valid110 : List Nat := []
theorem chunk110 : (List.range' 14080 128).filter passes14 = valid110 := by decide +kernel
def valid111 : List Nat := []
theorem chunk111 : (List.range' 14208 128).filter passes14 = valid111 := by decide +kernel
def valid112 : List Nat := [14336, 14337, 14368, 14369, 14400, 14401, 14432]
theorem chunk112 : (List.range' 14336 128).filter passes14 = valid112 := by decide +kernel
def valid113 : List Nat := []
theorem chunk113 : (List.range' 14464 128).filter passes14 = valid113 := by decide +kernel
def valid114 : List Nat := []
theorem chunk114 : (List.range' 14592 128).filter passes14 = valid114 := by decide +kernel
def valid115 : List Nat := []
theorem chunk115 : (List.range' 14720 128).filter passes14 = valid115 := by decide +kernel
def valid116 : List Nat := [14848, 14849, 14912, 14913]
theorem chunk116 : (List.range' 14848 128).filter passes14 = valid116 := by decide +kernel
def valid117 : List Nat := []
theorem chunk117 : (List.range' 14976 128).filter passes14 = valid117 := by decide +kernel
def valid118 : List Nat := []
theorem chunk118 : (List.range' 15104 128).filter passes14 = valid118 := by decide +kernel
def valid119 : List Nat := []
theorem chunk119 : (List.range' 15232 128).filter passes14 = valid119 := by decide +kernel
def valid120 : List Nat := []
theorem chunk120 : (List.range' 15360 128).filter passes14 = valid120 := by decide +kernel
def valid121 : List Nat := []
theorem chunk121 : (List.range' 15488 128).filter passes14 = valid121 := by decide +kernel
def valid122 : List Nat := []
theorem chunk122 : (List.range' 15616 128).filter passes14 = valid122 := by decide +kernel
def valid123 : List Nat := []
theorem chunk123 : (List.range' 15744 128).filter passes14 = valid123 := by decide +kernel
def valid124 : List Nat := []
theorem chunk124 : (List.range' 15872 128).filter passes14 = valid124 := by decide +kernel
def valid125 : List Nat := []
theorem chunk125 : (List.range' 16000 128).filter passes14 = valid125 := by decide +kernel
def valid126 : List Nat := []
theorem chunk126 : (List.range' 16128 128).filter passes14 = valid126 := by decide +kernel
def valid127 : List Nat := []
theorem chunk127 : (List.range' 16256 128).filter passes14 = valid127 := by decide +kernel
def vals2_0 := valid0 ++ valid1
theorem block2_0 : (List.range' 0 256).filter passes14 = vals2_0 := by
  have split : List.range' 0 256 = List.range' 0 128 ++ List.range' 128 128 := (List.range'_append (s := 0) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk0, chunk1] <;> rfl
def vals2_2 := valid2 ++ valid3
theorem block2_2 : (List.range' 256 256).filter passes14 = vals2_2 := by
  have split : List.range' 256 256 = List.range' 256 128 ++ List.range' 384 128 := (List.range'_append (s := 256) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk2, chunk3] <;> rfl
def vals2_4 := valid4 ++ valid5
theorem block2_4 : (List.range' 512 256).filter passes14 = vals2_4 := by
  have split : List.range' 512 256 = List.range' 512 128 ++ List.range' 640 128 := (List.range'_append (s := 512) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk4, chunk5] <;> rfl
def vals2_6 := valid6 ++ valid7
theorem block2_6 : (List.range' 768 256).filter passes14 = vals2_6 := by
  have split : List.range' 768 256 = List.range' 768 128 ++ List.range' 896 128 := (List.range'_append (s := 768) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk6, chunk7] <;> rfl
def vals2_8 := valid8 ++ valid9
theorem block2_8 : (List.range' 1024 256).filter passes14 = vals2_8 := by
  have split : List.range' 1024 256 = List.range' 1024 128 ++ List.range' 1152 128 := (List.range'_append (s := 1024) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk8, chunk9] <;> rfl
def vals2_10 := valid10 ++ valid11
theorem block2_10 : (List.range' 1280 256).filter passes14 = vals2_10 := by
  have split : List.range' 1280 256 = List.range' 1280 128 ++ List.range' 1408 128 := (List.range'_append (s := 1280) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk10, chunk11] <;> rfl
def vals2_12 := valid12 ++ valid13
theorem block2_12 : (List.range' 1536 256).filter passes14 = vals2_12 := by
  have split : List.range' 1536 256 = List.range' 1536 128 ++ List.range' 1664 128 := (List.range'_append (s := 1536) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk12, chunk13] <;> rfl
def vals2_14 := valid14 ++ valid15
theorem block2_14 : (List.range' 1792 256).filter passes14 = vals2_14 := by
  have split : List.range' 1792 256 = List.range' 1792 128 ++ List.range' 1920 128 := (List.range'_append (s := 1792) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk14, chunk15] <;> rfl
def vals2_16 := valid16 ++ valid17
theorem block2_16 : (List.range' 2048 256).filter passes14 = vals2_16 := by
  have split : List.range' 2048 256 = List.range' 2048 128 ++ List.range' 2176 128 := (List.range'_append (s := 2048) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk16, chunk17] <;> rfl
def vals2_18 := valid18 ++ valid19
theorem block2_18 : (List.range' 2304 256).filter passes14 = vals2_18 := by
  have split : List.range' 2304 256 = List.range' 2304 128 ++ List.range' 2432 128 := (List.range'_append (s := 2304) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk18, chunk19] <;> rfl
def vals2_20 := valid20 ++ valid21
theorem block2_20 : (List.range' 2560 256).filter passes14 = vals2_20 := by
  have split : List.range' 2560 256 = List.range' 2560 128 ++ List.range' 2688 128 := (List.range'_append (s := 2560) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk20, chunk21] <;> rfl
def vals2_22 := valid22 ++ valid23
theorem block2_22 : (List.range' 2816 256).filter passes14 = vals2_22 := by
  have split : List.range' 2816 256 = List.range' 2816 128 ++ List.range' 2944 128 := (List.range'_append (s := 2816) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk22, chunk23] <;> rfl
def vals2_24 := valid24 ++ valid25
theorem block2_24 : (List.range' 3072 256).filter passes14 = vals2_24 := by
  have split : List.range' 3072 256 = List.range' 3072 128 ++ List.range' 3200 128 := (List.range'_append (s := 3072) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk24, chunk25] <;> rfl
def vals2_26 := valid26 ++ valid27
theorem block2_26 : (List.range' 3328 256).filter passes14 = vals2_26 := by
  have split : List.range' 3328 256 = List.range' 3328 128 ++ List.range' 3456 128 := (List.range'_append (s := 3328) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk26, chunk27] <;> rfl
def vals2_28 := valid28 ++ valid29
theorem block2_28 : (List.range' 3584 256).filter passes14 = vals2_28 := by
  have split : List.range' 3584 256 = List.range' 3584 128 ++ List.range' 3712 128 := (List.range'_append (s := 3584) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk28, chunk29] <;> rfl
def vals2_30 := valid30 ++ valid31
theorem block2_30 : (List.range' 3840 256).filter passes14 = vals2_30 := by
  have split : List.range' 3840 256 = List.range' 3840 128 ++ List.range' 3968 128 := (List.range'_append (s := 3840) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk30, chunk31] <;> rfl
def vals2_32 := valid32 ++ valid33
theorem block2_32 : (List.range' 4096 256).filter passes14 = vals2_32 := by
  have split : List.range' 4096 256 = List.range' 4096 128 ++ List.range' 4224 128 := (List.range'_append (s := 4096) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk32, chunk33] <;> rfl
def vals2_34 := valid34 ++ valid35
theorem block2_34 : (List.range' 4352 256).filter passes14 = vals2_34 := by
  have split : List.range' 4352 256 = List.range' 4352 128 ++ List.range' 4480 128 := (List.range'_append (s := 4352) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk34, chunk35] <;> rfl
def vals2_36 := valid36 ++ valid37
theorem block2_36 : (List.range' 4608 256).filter passes14 = vals2_36 := by
  have split : List.range' 4608 256 = List.range' 4608 128 ++ List.range' 4736 128 := (List.range'_append (s := 4608) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk36, chunk37] <;> rfl
def vals2_38 := valid38 ++ valid39
theorem block2_38 : (List.range' 4864 256).filter passes14 = vals2_38 := by
  have split : List.range' 4864 256 = List.range' 4864 128 ++ List.range' 4992 128 := (List.range'_append (s := 4864) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk38, chunk39] <;> rfl
def vals2_40 := valid40 ++ valid41
theorem block2_40 : (List.range' 5120 256).filter passes14 = vals2_40 := by
  have split : List.range' 5120 256 = List.range' 5120 128 ++ List.range' 5248 128 := (List.range'_append (s := 5120) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk40, chunk41] <;> rfl
def vals2_42 := valid42 ++ valid43
theorem block2_42 : (List.range' 5376 256).filter passes14 = vals2_42 := by
  have split : List.range' 5376 256 = List.range' 5376 128 ++ List.range' 5504 128 := (List.range'_append (s := 5376) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk42, chunk43] <;> rfl
def vals2_44 := valid44 ++ valid45
theorem block2_44 : (List.range' 5632 256).filter passes14 = vals2_44 := by
  have split : List.range' 5632 256 = List.range' 5632 128 ++ List.range' 5760 128 := (List.range'_append (s := 5632) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk44, chunk45] <;> rfl
def vals2_46 := valid46 ++ valid47
theorem block2_46 : (List.range' 5888 256).filter passes14 = vals2_46 := by
  have split : List.range' 5888 256 = List.range' 5888 128 ++ List.range' 6016 128 := (List.range'_append (s := 5888) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk46, chunk47] <;> rfl
def vals2_48 := valid48 ++ valid49
theorem block2_48 : (List.range' 6144 256).filter passes14 = vals2_48 := by
  have split : List.range' 6144 256 = List.range' 6144 128 ++ List.range' 6272 128 := (List.range'_append (s := 6144) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk48, chunk49] <;> rfl
def vals2_50 := valid50 ++ valid51
theorem block2_50 : (List.range' 6400 256).filter passes14 = vals2_50 := by
  have split : List.range' 6400 256 = List.range' 6400 128 ++ List.range' 6528 128 := (List.range'_append (s := 6400) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk50, chunk51] <;> rfl
def vals2_52 := valid52 ++ valid53
theorem block2_52 : (List.range' 6656 256).filter passes14 = vals2_52 := by
  have split : List.range' 6656 256 = List.range' 6656 128 ++ List.range' 6784 128 := (List.range'_append (s := 6656) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk52, chunk53] <;> rfl
def vals2_54 := valid54 ++ valid55
theorem block2_54 : (List.range' 6912 256).filter passes14 = vals2_54 := by
  have split : List.range' 6912 256 = List.range' 6912 128 ++ List.range' 7040 128 := (List.range'_append (s := 6912) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk54, chunk55] <;> rfl
def vals2_56 := valid56 ++ valid57
theorem block2_56 : (List.range' 7168 256).filter passes14 = vals2_56 := by
  have split : List.range' 7168 256 = List.range' 7168 128 ++ List.range' 7296 128 := (List.range'_append (s := 7168) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk56, chunk57] <;> rfl
def vals2_58 := valid58 ++ valid59
theorem block2_58 : (List.range' 7424 256).filter passes14 = vals2_58 := by
  have split : List.range' 7424 256 = List.range' 7424 128 ++ List.range' 7552 128 := (List.range'_append (s := 7424) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk58, chunk59] <;> rfl
def vals2_60 := valid60 ++ valid61
theorem block2_60 : (List.range' 7680 256).filter passes14 = vals2_60 := by
  have split : List.range' 7680 256 = List.range' 7680 128 ++ List.range' 7808 128 := (List.range'_append (s := 7680) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk60, chunk61] <;> rfl
def vals2_62 := valid62 ++ valid63
theorem block2_62 : (List.range' 7936 256).filter passes14 = vals2_62 := by
  have split : List.range' 7936 256 = List.range' 7936 128 ++ List.range' 8064 128 := (List.range'_append (s := 7936) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk62, chunk63] <;> rfl
def vals2_64 := valid64 ++ valid65
theorem block2_64 : (List.range' 8192 256).filter passes14 = vals2_64 := by
  have split : List.range' 8192 256 = List.range' 8192 128 ++ List.range' 8320 128 := (List.range'_append (s := 8192) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk64, chunk65] <;> rfl
def vals2_66 := valid66 ++ valid67
theorem block2_66 : (List.range' 8448 256).filter passes14 = vals2_66 := by
  have split : List.range' 8448 256 = List.range' 8448 128 ++ List.range' 8576 128 := (List.range'_append (s := 8448) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk66, chunk67] <;> rfl
def vals2_68 := valid68 ++ valid69
theorem block2_68 : (List.range' 8704 256).filter passes14 = vals2_68 := by
  have split : List.range' 8704 256 = List.range' 8704 128 ++ List.range' 8832 128 := (List.range'_append (s := 8704) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk68, chunk69] <;> rfl
def vals2_70 := valid70 ++ valid71
theorem block2_70 : (List.range' 8960 256).filter passes14 = vals2_70 := by
  have split : List.range' 8960 256 = List.range' 8960 128 ++ List.range' 9088 128 := (List.range'_append (s := 8960) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk70, chunk71] <;> rfl
def vals2_72 := valid72 ++ valid73
theorem block2_72 : (List.range' 9216 256).filter passes14 = vals2_72 := by
  have split : List.range' 9216 256 = List.range' 9216 128 ++ List.range' 9344 128 := (List.range'_append (s := 9216) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk72, chunk73] <;> rfl
def vals2_74 := valid74 ++ valid75
theorem block2_74 : (List.range' 9472 256).filter passes14 = vals2_74 := by
  have split : List.range' 9472 256 = List.range' 9472 128 ++ List.range' 9600 128 := (List.range'_append (s := 9472) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk74, chunk75] <;> rfl
def vals2_76 := valid76 ++ valid77
theorem block2_76 : (List.range' 9728 256).filter passes14 = vals2_76 := by
  have split : List.range' 9728 256 = List.range' 9728 128 ++ List.range' 9856 128 := (List.range'_append (s := 9728) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk76, chunk77] <;> rfl
def vals2_78 := valid78 ++ valid79
theorem block2_78 : (List.range' 9984 256).filter passes14 = vals2_78 := by
  have split : List.range' 9984 256 = List.range' 9984 128 ++ List.range' 10112 128 := (List.range'_append (s := 9984) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk78, chunk79] <;> rfl
def vals2_80 := valid80 ++ valid81
theorem block2_80 : (List.range' 10240 256).filter passes14 = vals2_80 := by
  have split : List.range' 10240 256 = List.range' 10240 128 ++ List.range' 10368 128 := (List.range'_append (s := 10240) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk80, chunk81] <;> rfl
def vals2_82 := valid82 ++ valid83
theorem block2_82 : (List.range' 10496 256).filter passes14 = vals2_82 := by
  have split : List.range' 10496 256 = List.range' 10496 128 ++ List.range' 10624 128 := (List.range'_append (s := 10496) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk82, chunk83] <;> rfl
def vals2_84 := valid84 ++ valid85
theorem block2_84 : (List.range' 10752 256).filter passes14 = vals2_84 := by
  have split : List.range' 10752 256 = List.range' 10752 128 ++ List.range' 10880 128 := (List.range'_append (s := 10752) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk84, chunk85] <;> rfl
def vals2_86 := valid86 ++ valid87
theorem block2_86 : (List.range' 11008 256).filter passes14 = vals2_86 := by
  have split : List.range' 11008 256 = List.range' 11008 128 ++ List.range' 11136 128 := (List.range'_append (s := 11008) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk86, chunk87] <;> rfl
def vals2_88 := valid88 ++ valid89
theorem block2_88 : (List.range' 11264 256).filter passes14 = vals2_88 := by
  have split : List.range' 11264 256 = List.range' 11264 128 ++ List.range' 11392 128 := (List.range'_append (s := 11264) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk88, chunk89] <;> rfl
def vals2_90 := valid90 ++ valid91
theorem block2_90 : (List.range' 11520 256).filter passes14 = vals2_90 := by
  have split : List.range' 11520 256 = List.range' 11520 128 ++ List.range' 11648 128 := (List.range'_append (s := 11520) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk90, chunk91] <;> rfl
def vals2_92 := valid92 ++ valid93
theorem block2_92 : (List.range' 11776 256).filter passes14 = vals2_92 := by
  have split : List.range' 11776 256 = List.range' 11776 128 ++ List.range' 11904 128 := (List.range'_append (s := 11776) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk92, chunk93] <;> rfl
def vals2_94 := valid94 ++ valid95
theorem block2_94 : (List.range' 12032 256).filter passes14 = vals2_94 := by
  have split : List.range' 12032 256 = List.range' 12032 128 ++ List.range' 12160 128 := (List.range'_append (s := 12032) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk94, chunk95] <;> rfl
def vals2_96 := valid96 ++ valid97
theorem block2_96 : (List.range' 12288 256).filter passes14 = vals2_96 := by
  have split : List.range' 12288 256 = List.range' 12288 128 ++ List.range' 12416 128 := (List.range'_append (s := 12288) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk96, chunk97] <;> rfl
def vals2_98 := valid98 ++ valid99
theorem block2_98 : (List.range' 12544 256).filter passes14 = vals2_98 := by
  have split : List.range' 12544 256 = List.range' 12544 128 ++ List.range' 12672 128 := (List.range'_append (s := 12544) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk98, chunk99] <;> rfl
def vals2_100 := valid100 ++ valid101
theorem block2_100 : (List.range' 12800 256).filter passes14 = vals2_100 := by
  have split : List.range' 12800 256 = List.range' 12800 128 ++ List.range' 12928 128 := (List.range'_append (s := 12800) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk100, chunk101] <;> rfl
def vals2_102 := valid102 ++ valid103
theorem block2_102 : (List.range' 13056 256).filter passes14 = vals2_102 := by
  have split : List.range' 13056 256 = List.range' 13056 128 ++ List.range' 13184 128 := (List.range'_append (s := 13056) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk102, chunk103] <;> rfl
def vals2_104 := valid104 ++ valid105
theorem block2_104 : (List.range' 13312 256).filter passes14 = vals2_104 := by
  have split : List.range' 13312 256 = List.range' 13312 128 ++ List.range' 13440 128 := (List.range'_append (s := 13312) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk104, chunk105] <;> rfl
def vals2_106 := valid106 ++ valid107
theorem block2_106 : (List.range' 13568 256).filter passes14 = vals2_106 := by
  have split : List.range' 13568 256 = List.range' 13568 128 ++ List.range' 13696 128 := (List.range'_append (s := 13568) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk106, chunk107] <;> rfl
def vals2_108 := valid108 ++ valid109
theorem block2_108 : (List.range' 13824 256).filter passes14 = vals2_108 := by
  have split : List.range' 13824 256 = List.range' 13824 128 ++ List.range' 13952 128 := (List.range'_append (s := 13824) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk108, chunk109] <;> rfl
def vals2_110 := valid110 ++ valid111
theorem block2_110 : (List.range' 14080 256).filter passes14 = vals2_110 := by
  have split : List.range' 14080 256 = List.range' 14080 128 ++ List.range' 14208 128 := (List.range'_append (s := 14080) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk110, chunk111] <;> rfl
def vals2_112 := valid112 ++ valid113
theorem block2_112 : (List.range' 14336 256).filter passes14 = vals2_112 := by
  have split : List.range' 14336 256 = List.range' 14336 128 ++ List.range' 14464 128 := (List.range'_append (s := 14336) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk112, chunk113] <;> rfl
def vals2_114 := valid114 ++ valid115
theorem block2_114 : (List.range' 14592 256).filter passes14 = vals2_114 := by
  have split : List.range' 14592 256 = List.range' 14592 128 ++ List.range' 14720 128 := (List.range'_append (s := 14592) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk114, chunk115] <;> rfl
def vals2_116 := valid116 ++ valid117
theorem block2_116 : (List.range' 14848 256).filter passes14 = vals2_116 := by
  have split : List.range' 14848 256 = List.range' 14848 128 ++ List.range' 14976 128 := (List.range'_append (s := 14848) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk116, chunk117] <;> rfl
def vals2_118 := valid118 ++ valid119
theorem block2_118 : (List.range' 15104 256).filter passes14 = vals2_118 := by
  have split : List.range' 15104 256 = List.range' 15104 128 ++ List.range' 15232 128 := (List.range'_append (s := 15104) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk118, chunk119] <;> rfl
def vals2_120 := valid120 ++ valid121
theorem block2_120 : (List.range' 15360 256).filter passes14 = vals2_120 := by
  have split : List.range' 15360 256 = List.range' 15360 128 ++ List.range' 15488 128 := (List.range'_append (s := 15360) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk120, chunk121] <;> rfl
def vals2_122 := valid122 ++ valid123
theorem block2_122 : (List.range' 15616 256).filter passes14 = vals2_122 := by
  have split : List.range' 15616 256 = List.range' 15616 128 ++ List.range' 15744 128 := (List.range'_append (s := 15616) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk122, chunk123] <;> rfl
def vals2_124 := valid124 ++ valid125
theorem block2_124 : (List.range' 15872 256).filter passes14 = vals2_124 := by
  have split : List.range' 15872 256 = List.range' 15872 128 ++ List.range' 16000 128 := (List.range'_append (s := 15872) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk124, chunk125] <;> rfl
def vals2_126 := valid126 ++ valid127
theorem block2_126 : (List.range' 16128 256).filter passes14 = vals2_126 := by
  have split : List.range' 16128 256 = List.range' 16128 128 ++ List.range' 16256 128 := (List.range'_append (s := 16128) (m := 128) (n := 128) (step := 1)).symm
  rw [split, List.filter_append, chunk126, chunk127] <;> rfl
def vals4_0 := vals2_0 ++ vals2_2
theorem block4_0 : (List.range' 0 512).filter passes14 = vals4_0 := by
  have split : List.range' 0 512 = List.range' 0 256 ++ List.range' 256 256 := (List.range'_append (s := 0) (m := 256) (n := 256) (step := 1)).symm
  rw [split, List.filter_append, block2_0, block2_2] <;> rfl
def vals4_4 := vals2_4 ++ vals2_6
theorem block4_4 : (List.range' 512 512).filter passes14 = vals4_4 := by
  have split : List.range' 512 512 = List.range' 512 256 ++ List.range' 768 256 := (List.range'_append (s := 512) (m := 256) (n := 256) (step := 1)).symm
  rw [split, List.filter_append, block2_4, block2_6] <;> rfl
def vals4_8 := vals2_8 ++ vals2_10
theorem block4_8 : (List.range' 1024 512).filter passes14 = vals4_8 := by
  have split : List.range' 1024 512 = List.range' 1024 256 ++ List.range' 1280 256 := (List.range'_append (s := 1024) (m := 256) (n := 256) (step := 1)).symm
  rw [split, List.filter_append, block2_8, block2_10] <;> rfl
def vals4_12 := vals2_12 ++ vals2_14
theorem block4_12 : (List.range' 1536 512).filter passes14 = vals4_12 := by
  have split : List.range' 1536 512 = List.range' 1536 256 ++ List.range' 1792 256 := (List.range'_append (s := 1536) (m := 256) (n := 256) (step := 1)).symm
  rw [split, List.filter_append, block2_12, block2_14] <;> rfl
def vals4_16 := vals2_16 ++ vals2_18
theorem block4_16 : (List.range' 2048 512).filter passes14 = vals4_16 := by
  have split : List.range' 2048 512 = List.range' 2048 256 ++ List.range' 2304 256 := (List.range'_append (s := 2048) (m := 256) (n := 256) (step := 1)).symm
  rw [split, List.filter_append, block2_16, block2_18] <;> rfl
def vals4_20 := vals2_20 ++ vals2_22
theorem block4_20 : (List.range' 2560 512).filter passes14 = vals4_20 := by
  have split : List.range' 2560 512 = List.range' 2560 256 ++ List.range' 2816 256 := (List.range'_append (s := 2560) (m := 256) (n := 256) (step := 1)).symm
  rw [split, List.filter_append, block2_20, block2_22] <;> rfl
def vals4_24 := vals2_24 ++ vals2_26
theorem block4_24 : (List.range' 3072 512).filter passes14 = vals4_24 := by
  have split : List.range' 3072 512 = List.range' 3072 256 ++ List.range' 3328 256 := (List.range'_append (s := 3072) (m := 256) (n := 256) (step := 1)).symm
  rw [split, List.filter_append, block2_24, block2_26] <;> rfl
def vals4_28 := vals2_28 ++ vals2_30
theorem block4_28 : (List.range' 3584 512).filter passes14 = vals4_28 := by
  have split : List.range' 3584 512 = List.range' 3584 256 ++ List.range' 3840 256 := (List.range'_append (s := 3584) (m := 256) (n := 256) (step := 1)).symm
  rw [split, List.filter_append, block2_28, block2_30] <;> rfl
def vals4_32 := vals2_32 ++ vals2_34
theorem block4_32 : (List.range' 4096 512).filter passes14 = vals4_32 := by
  have split : List.range' 4096 512 = List.range' 4096 256 ++ List.range' 4352 256 := (List.range'_append (s := 4096) (m := 256) (n := 256) (step := 1)).symm
  rw [split, List.filter_append, block2_32, block2_34] <;> rfl
def vals4_36 := vals2_36 ++ vals2_38
theorem block4_36 : (List.range' 4608 512).filter passes14 = vals4_36 := by
  have split : List.range' 4608 512 = List.range' 4608 256 ++ List.range' 4864 256 := (List.range'_append (s := 4608) (m := 256) (n := 256) (step := 1)).symm
  rw [split, List.filter_append, block2_36, block2_38] <;> rfl
def vals4_40 := vals2_40 ++ vals2_42
theorem block4_40 : (List.range' 5120 512).filter passes14 = vals4_40 := by
  have split : List.range' 5120 512 = List.range' 5120 256 ++ List.range' 5376 256 := (List.range'_append (s := 5120) (m := 256) (n := 256) (step := 1)).symm
  rw [split, List.filter_append, block2_40, block2_42] <;> rfl
def vals4_44 := vals2_44 ++ vals2_46
theorem block4_44 : (List.range' 5632 512).filter passes14 = vals4_44 := by
  have split : List.range' 5632 512 = List.range' 5632 256 ++ List.range' 5888 256 := (List.range'_append (s := 5632) (m := 256) (n := 256) (step := 1)).symm
  rw [split, List.filter_append, block2_44, block2_46] <;> rfl
def vals4_48 := vals2_48 ++ vals2_50
theorem block4_48 : (List.range' 6144 512).filter passes14 = vals4_48 := by
  have split : List.range' 6144 512 = List.range' 6144 256 ++ List.range' 6400 256 := (List.range'_append (s := 6144) (m := 256) (n := 256) (step := 1)).symm
  rw [split, List.filter_append, block2_48, block2_50] <;> rfl
def vals4_52 := vals2_52 ++ vals2_54
theorem block4_52 : (List.range' 6656 512).filter passes14 = vals4_52 := by
  have split : List.range' 6656 512 = List.range' 6656 256 ++ List.range' 6912 256 := (List.range'_append (s := 6656) (m := 256) (n := 256) (step := 1)).symm
  rw [split, List.filter_append, block2_52, block2_54] <;> rfl
def vals4_56 := vals2_56 ++ vals2_58
theorem block4_56 : (List.range' 7168 512).filter passes14 = vals4_56 := by
  have split : List.range' 7168 512 = List.range' 7168 256 ++ List.range' 7424 256 := (List.range'_append (s := 7168) (m := 256) (n := 256) (step := 1)).symm
  rw [split, List.filter_append, block2_56, block2_58] <;> rfl
def vals4_60 := vals2_60 ++ vals2_62
theorem block4_60 : (List.range' 7680 512).filter passes14 = vals4_60 := by
  have split : List.range' 7680 512 = List.range' 7680 256 ++ List.range' 7936 256 := (List.range'_append (s := 7680) (m := 256) (n := 256) (step := 1)).symm
  rw [split, List.filter_append, block2_60, block2_62] <;> rfl
def vals4_64 := vals2_64 ++ vals2_66
theorem block4_64 : (List.range' 8192 512).filter passes14 = vals4_64 := by
  have split : List.range' 8192 512 = List.range' 8192 256 ++ List.range' 8448 256 := (List.range'_append (s := 8192) (m := 256) (n := 256) (step := 1)).symm
  rw [split, List.filter_append, block2_64, block2_66] <;> rfl
def vals4_68 := vals2_68 ++ vals2_70
theorem block4_68 : (List.range' 8704 512).filter passes14 = vals4_68 := by
  have split : List.range' 8704 512 = List.range' 8704 256 ++ List.range' 8960 256 := (List.range'_append (s := 8704) (m := 256) (n := 256) (step := 1)).symm
  rw [split, List.filter_append, block2_68, block2_70] <;> rfl
def vals4_72 := vals2_72 ++ vals2_74
theorem block4_72 : (List.range' 9216 512).filter passes14 = vals4_72 := by
  have split : List.range' 9216 512 = List.range' 9216 256 ++ List.range' 9472 256 := (List.range'_append (s := 9216) (m := 256) (n := 256) (step := 1)).symm
  rw [split, List.filter_append, block2_72, block2_74] <;> rfl
def vals4_76 := vals2_76 ++ vals2_78
theorem block4_76 : (List.range' 9728 512).filter passes14 = vals4_76 := by
  have split : List.range' 9728 512 = List.range' 9728 256 ++ List.range' 9984 256 := (List.range'_append (s := 9728) (m := 256) (n := 256) (step := 1)).symm
  rw [split, List.filter_append, block2_76, block2_78] <;> rfl
def vals4_80 := vals2_80 ++ vals2_82
theorem block4_80 : (List.range' 10240 512).filter passes14 = vals4_80 := by
  have split : List.range' 10240 512 = List.range' 10240 256 ++ List.range' 10496 256 := (List.range'_append (s := 10240) (m := 256) (n := 256) (step := 1)).symm
  rw [split, List.filter_append, block2_80, block2_82] <;> rfl
def vals4_84 := vals2_84 ++ vals2_86
theorem block4_84 : (List.range' 10752 512).filter passes14 = vals4_84 := by
  have split : List.range' 10752 512 = List.range' 10752 256 ++ List.range' 11008 256 := (List.range'_append (s := 10752) (m := 256) (n := 256) (step := 1)).symm
  rw [split, List.filter_append, block2_84, block2_86] <;> rfl
def vals4_88 := vals2_88 ++ vals2_90
theorem block4_88 : (List.range' 11264 512).filter passes14 = vals4_88 := by
  have split : List.range' 11264 512 = List.range' 11264 256 ++ List.range' 11520 256 := (List.range'_append (s := 11264) (m := 256) (n := 256) (step := 1)).symm
  rw [split, List.filter_append, block2_88, block2_90] <;> rfl
def vals4_92 := vals2_92 ++ vals2_94
theorem block4_92 : (List.range' 11776 512).filter passes14 = vals4_92 := by
  have split : List.range' 11776 512 = List.range' 11776 256 ++ List.range' 12032 256 := (List.range'_append (s := 11776) (m := 256) (n := 256) (step := 1)).symm
  rw [split, List.filter_append, block2_92, block2_94] <;> rfl
def vals4_96 := vals2_96 ++ vals2_98
theorem block4_96 : (List.range' 12288 512).filter passes14 = vals4_96 := by
  have split : List.range' 12288 512 = List.range' 12288 256 ++ List.range' 12544 256 := (List.range'_append (s := 12288) (m := 256) (n := 256) (step := 1)).symm
  rw [split, List.filter_append, block2_96, block2_98] <;> rfl
def vals4_100 := vals2_100 ++ vals2_102
theorem block4_100 : (List.range' 12800 512).filter passes14 = vals4_100 := by
  have split : List.range' 12800 512 = List.range' 12800 256 ++ List.range' 13056 256 := (List.range'_append (s := 12800) (m := 256) (n := 256) (step := 1)).symm
  rw [split, List.filter_append, block2_100, block2_102] <;> rfl
def vals4_104 := vals2_104 ++ vals2_106
theorem block4_104 : (List.range' 13312 512).filter passes14 = vals4_104 := by
  have split : List.range' 13312 512 = List.range' 13312 256 ++ List.range' 13568 256 := (List.range'_append (s := 13312) (m := 256) (n := 256) (step := 1)).symm
  rw [split, List.filter_append, block2_104, block2_106] <;> rfl
def vals4_108 := vals2_108 ++ vals2_110
theorem block4_108 : (List.range' 13824 512).filter passes14 = vals4_108 := by
  have split : List.range' 13824 512 = List.range' 13824 256 ++ List.range' 14080 256 := (List.range'_append (s := 13824) (m := 256) (n := 256) (step := 1)).symm
  rw [split, List.filter_append, block2_108, block2_110] <;> rfl
def vals4_112 := vals2_112 ++ vals2_114
theorem block4_112 : (List.range' 14336 512).filter passes14 = vals4_112 := by
  have split : List.range' 14336 512 = List.range' 14336 256 ++ List.range' 14592 256 := (List.range'_append (s := 14336) (m := 256) (n := 256) (step := 1)).symm
  rw [split, List.filter_append, block2_112, block2_114] <;> rfl
def vals4_116 := vals2_116 ++ vals2_118
theorem block4_116 : (List.range' 14848 512).filter passes14 = vals4_116 := by
  have split : List.range' 14848 512 = List.range' 14848 256 ++ List.range' 15104 256 := (List.range'_append (s := 14848) (m := 256) (n := 256) (step := 1)).symm
  rw [split, List.filter_append, block2_116, block2_118] <;> rfl
def vals4_120 := vals2_120 ++ vals2_122
theorem block4_120 : (List.range' 15360 512).filter passes14 = vals4_120 := by
  have split : List.range' 15360 512 = List.range' 15360 256 ++ List.range' 15616 256 := (List.range'_append (s := 15360) (m := 256) (n := 256) (step := 1)).symm
  rw [split, List.filter_append, block2_120, block2_122] <;> rfl
def vals4_124 := vals2_124 ++ vals2_126
theorem block4_124 : (List.range' 15872 512).filter passes14 = vals4_124 := by
  have split : List.range' 15872 512 = List.range' 15872 256 ++ List.range' 16128 256 := (List.range'_append (s := 15872) (m := 256) (n := 256) (step := 1)).symm
  rw [split, List.filter_append, block2_124, block2_126] <;> rfl
def vals8_0 := vals4_0 ++ vals4_4
theorem block8_0 : (List.range' 0 1024).filter passes14 = vals8_0 := by
  have split : List.range' 0 1024 = List.range' 0 512 ++ List.range' 512 512 := (List.range'_append (s := 0) (m := 512) (n := 512) (step := 1)).symm
  rw [split, List.filter_append, block4_0, block4_4] <;> rfl
def vals8_8 := vals4_8 ++ vals4_12
theorem block8_8 : (List.range' 1024 1024).filter passes14 = vals8_8 := by
  have split : List.range' 1024 1024 = List.range' 1024 512 ++ List.range' 1536 512 := (List.range'_append (s := 1024) (m := 512) (n := 512) (step := 1)).symm
  rw [split, List.filter_append, block4_8, block4_12] <;> rfl
def vals8_16 := vals4_16 ++ vals4_20
theorem block8_16 : (List.range' 2048 1024).filter passes14 = vals8_16 := by
  have split : List.range' 2048 1024 = List.range' 2048 512 ++ List.range' 2560 512 := (List.range'_append (s := 2048) (m := 512) (n := 512) (step := 1)).symm
  rw [split, List.filter_append, block4_16, block4_20] <;> rfl
def vals8_24 := vals4_24 ++ vals4_28
theorem block8_24 : (List.range' 3072 1024).filter passes14 = vals8_24 := by
  have split : List.range' 3072 1024 = List.range' 3072 512 ++ List.range' 3584 512 := (List.range'_append (s := 3072) (m := 512) (n := 512) (step := 1)).symm
  rw [split, List.filter_append, block4_24, block4_28] <;> rfl
def vals8_32 := vals4_32 ++ vals4_36
theorem block8_32 : (List.range' 4096 1024).filter passes14 = vals8_32 := by
  have split : List.range' 4096 1024 = List.range' 4096 512 ++ List.range' 4608 512 := (List.range'_append (s := 4096) (m := 512) (n := 512) (step := 1)).symm
  rw [split, List.filter_append, block4_32, block4_36] <;> rfl
def vals8_40 := vals4_40 ++ vals4_44
theorem block8_40 : (List.range' 5120 1024).filter passes14 = vals8_40 := by
  have split : List.range' 5120 1024 = List.range' 5120 512 ++ List.range' 5632 512 := (List.range'_append (s := 5120) (m := 512) (n := 512) (step := 1)).symm
  rw [split, List.filter_append, block4_40, block4_44] <;> rfl
def vals8_48 := vals4_48 ++ vals4_52
theorem block8_48 : (List.range' 6144 1024).filter passes14 = vals8_48 := by
  have split : List.range' 6144 1024 = List.range' 6144 512 ++ List.range' 6656 512 := (List.range'_append (s := 6144) (m := 512) (n := 512) (step := 1)).symm
  rw [split, List.filter_append, block4_48, block4_52] <;> rfl
def vals8_56 := vals4_56 ++ vals4_60
theorem block8_56 : (List.range' 7168 1024).filter passes14 = vals8_56 := by
  have split : List.range' 7168 1024 = List.range' 7168 512 ++ List.range' 7680 512 := (List.range'_append (s := 7168) (m := 512) (n := 512) (step := 1)).symm
  rw [split, List.filter_append, block4_56, block4_60] <;> rfl
def vals8_64 := vals4_64 ++ vals4_68
theorem block8_64 : (List.range' 8192 1024).filter passes14 = vals8_64 := by
  have split : List.range' 8192 1024 = List.range' 8192 512 ++ List.range' 8704 512 := (List.range'_append (s := 8192) (m := 512) (n := 512) (step := 1)).symm
  rw [split, List.filter_append, block4_64, block4_68] <;> rfl
def vals8_72 := vals4_72 ++ vals4_76
theorem block8_72 : (List.range' 9216 1024).filter passes14 = vals8_72 := by
  have split : List.range' 9216 1024 = List.range' 9216 512 ++ List.range' 9728 512 := (List.range'_append (s := 9216) (m := 512) (n := 512) (step := 1)).symm
  rw [split, List.filter_append, block4_72, block4_76] <;> rfl
def vals8_80 := vals4_80 ++ vals4_84
theorem block8_80 : (List.range' 10240 1024).filter passes14 = vals8_80 := by
  have split : List.range' 10240 1024 = List.range' 10240 512 ++ List.range' 10752 512 := (List.range'_append (s := 10240) (m := 512) (n := 512) (step := 1)).symm
  rw [split, List.filter_append, block4_80, block4_84] <;> rfl
def vals8_88 := vals4_88 ++ vals4_92
theorem block8_88 : (List.range' 11264 1024).filter passes14 = vals8_88 := by
  have split : List.range' 11264 1024 = List.range' 11264 512 ++ List.range' 11776 512 := (List.range'_append (s := 11264) (m := 512) (n := 512) (step := 1)).symm
  rw [split, List.filter_append, block4_88, block4_92] <;> rfl
def vals8_96 := vals4_96 ++ vals4_100
theorem block8_96 : (List.range' 12288 1024).filter passes14 = vals8_96 := by
  have split : List.range' 12288 1024 = List.range' 12288 512 ++ List.range' 12800 512 := (List.range'_append (s := 12288) (m := 512) (n := 512) (step := 1)).symm
  rw [split, List.filter_append, block4_96, block4_100] <;> rfl
def vals8_104 := vals4_104 ++ vals4_108
theorem block8_104 : (List.range' 13312 1024).filter passes14 = vals8_104 := by
  have split : List.range' 13312 1024 = List.range' 13312 512 ++ List.range' 13824 512 := (List.range'_append (s := 13312) (m := 512) (n := 512) (step := 1)).symm
  rw [split, List.filter_append, block4_104, block4_108] <;> rfl
def vals8_112 := vals4_112 ++ vals4_116
theorem block8_112 : (List.range' 14336 1024).filter passes14 = vals8_112 := by
  have split : List.range' 14336 1024 = List.range' 14336 512 ++ List.range' 14848 512 := (List.range'_append (s := 14336) (m := 512) (n := 512) (step := 1)).symm
  rw [split, List.filter_append, block4_112, block4_116] <;> rfl
def vals8_120 := vals4_120 ++ vals4_124
theorem block8_120 : (List.range' 15360 1024).filter passes14 = vals8_120 := by
  have split : List.range' 15360 1024 = List.range' 15360 512 ++ List.range' 15872 512 := (List.range'_append (s := 15360) (m := 512) (n := 512) (step := 1)).symm
  rw [split, List.filter_append, block4_120, block4_124] <;> rfl
def vals16_0 := vals8_0 ++ vals8_8
theorem block16_0 : (List.range' 0 2048).filter passes14 = vals16_0 := by
  have split : List.range' 0 2048 = List.range' 0 1024 ++ List.range' 1024 1024 := (List.range'_append (s := 0) (m := 1024) (n := 1024) (step := 1)).symm
  rw [split, List.filter_append, block8_0, block8_8] <;> rfl
def vals16_16 := vals8_16 ++ vals8_24
theorem block16_16 : (List.range' 2048 2048).filter passes14 = vals16_16 := by
  have split : List.range' 2048 2048 = List.range' 2048 1024 ++ List.range' 3072 1024 := (List.range'_append (s := 2048) (m := 1024) (n := 1024) (step := 1)).symm
  rw [split, List.filter_append, block8_16, block8_24] <;> rfl
def vals16_32 := vals8_32 ++ vals8_40
theorem block16_32 : (List.range' 4096 2048).filter passes14 = vals16_32 := by
  have split : List.range' 4096 2048 = List.range' 4096 1024 ++ List.range' 5120 1024 := (List.range'_append (s := 4096) (m := 1024) (n := 1024) (step := 1)).symm
  rw [split, List.filter_append, block8_32, block8_40] <;> rfl
def vals16_48 := vals8_48 ++ vals8_56
theorem block16_48 : (List.range' 6144 2048).filter passes14 = vals16_48 := by
  have split : List.range' 6144 2048 = List.range' 6144 1024 ++ List.range' 7168 1024 := (List.range'_append (s := 6144) (m := 1024) (n := 1024) (step := 1)).symm
  rw [split, List.filter_append, block8_48, block8_56] <;> rfl
def vals16_64 := vals8_64 ++ vals8_72
theorem block16_64 : (List.range' 8192 2048).filter passes14 = vals16_64 := by
  have split : List.range' 8192 2048 = List.range' 8192 1024 ++ List.range' 9216 1024 := (List.range'_append (s := 8192) (m := 1024) (n := 1024) (step := 1)).symm
  rw [split, List.filter_append, block8_64, block8_72] <;> rfl
def vals16_80 := vals8_80 ++ vals8_88
theorem block16_80 : (List.range' 10240 2048).filter passes14 = vals16_80 := by
  have split : List.range' 10240 2048 = List.range' 10240 1024 ++ List.range' 11264 1024 := (List.range'_append (s := 10240) (m := 1024) (n := 1024) (step := 1)).symm
  rw [split, List.filter_append, block8_80, block8_88] <;> rfl
def vals16_96 := vals8_96 ++ vals8_104
theorem block16_96 : (List.range' 12288 2048).filter passes14 = vals16_96 := by
  have split : List.range' 12288 2048 = List.range' 12288 1024 ++ List.range' 13312 1024 := (List.range'_append (s := 12288) (m := 1024) (n := 1024) (step := 1)).symm
  rw [split, List.filter_append, block8_96, block8_104] <;> rfl
def vals16_112 := vals8_112 ++ vals8_120
theorem block16_112 : (List.range' 14336 2048).filter passes14 = vals16_112 := by
  have split : List.range' 14336 2048 = List.range' 14336 1024 ++ List.range' 15360 1024 := (List.range'_append (s := 14336) (m := 1024) (n := 1024) (step := 1)).symm
  rw [split, List.filter_append, block8_112, block8_120] <;> rfl
def vals32_0 := vals16_0 ++ vals16_16
theorem block32_0 : (List.range' 0 4096).filter passes14 = vals32_0 := by
  have split : List.range' 0 4096 = List.range' 0 2048 ++ List.range' 2048 2048 := (List.range'_append (s := 0) (m := 2048) (n := 2048) (step := 1)).symm
  rw [split, List.filter_append, block16_0, block16_16] <;> rfl
def vals32_32 := vals16_32 ++ vals16_48
theorem block32_32 : (List.range' 4096 4096).filter passes14 = vals32_32 := by
  have split : List.range' 4096 4096 = List.range' 4096 2048 ++ List.range' 6144 2048 := (List.range'_append (s := 4096) (m := 2048) (n := 2048) (step := 1)).symm
  rw [split, List.filter_append, block16_32, block16_48] <;> rfl
def vals32_64 := vals16_64 ++ vals16_80
theorem block32_64 : (List.range' 8192 4096).filter passes14 = vals32_64 := by
  have split : List.range' 8192 4096 = List.range' 8192 2048 ++ List.range' 10240 2048 := (List.range'_append (s := 8192) (m := 2048) (n := 2048) (step := 1)).symm
  rw [split, List.filter_append, block16_64, block16_80] <;> rfl
def vals32_96 := vals16_96 ++ vals16_112
theorem block32_96 : (List.range' 12288 4096).filter passes14 = vals32_96 := by
  have split : List.range' 12288 4096 = List.range' 12288 2048 ++ List.range' 14336 2048 := (List.range'_append (s := 12288) (m := 2048) (n := 2048) (step := 1)).symm
  rw [split, List.filter_append, block16_96, block16_112] <;> rfl
def vals64_0 := vals32_0 ++ vals32_32
theorem block64_0 : (List.range' 0 8192).filter passes14 = vals64_0 := by
  have split : List.range' 0 8192 = List.range' 0 4096 ++ List.range' 4096 4096 := (List.range'_append (s := 0) (m := 4096) (n := 4096) (step := 1)).symm
  rw [split, List.filter_append, block32_0, block32_32] <;> rfl
def vals64_64 := vals32_64 ++ vals32_96
theorem block64_64 : (List.range' 8192 8192).filter passes14 = vals64_64 := by
  have split : List.range' 8192 8192 = List.range' 8192 4096 ++ List.range' 12288 4096 := (List.range'_append (s := 8192) (m := 4096) (n := 4096) (step := 1)).symm
  rw [split, List.filter_append, block32_64, block32_96] <;> rfl
def vals128_0 := vals64_0 ++ vals64_64
theorem block128_0 : (List.range' 0 16384).filter passes14 = vals128_0 := by
  have split : List.range' 0 16384 = List.range' 0 8192 ++ List.range' 8192 8192 := (List.range'_append (s := 0) (m := 8192) (n := 8192) (step := 1)).symm
  rw [split, List.filter_append, block64_0, block64_64] <;> rfl

end FinitePolygonWitnesses
