import ReflectZphi.Data.Cert5.C142.Base

namespace ReflectZphi.Data.Cert5.C142

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd15_2_1056 : subd15_2 [3, 4, -5] = true := by decide +kernel
theorem subd15_2_1057 : subd15_2 [3, 4, -4] = true := by decide +kernel
theorem subd15_2_1058 : subd15_2 [3, 4, -3] = true := by decide +kernel
theorem subd15_2_1059 : subd15_2 [3, 4, -2] = true := by decide +kernel
theorem subd15_2_1060 : subd15_2 [3, 4, -1] = true := by decide +kernel
theorem subd15_2_1061 : subd15_2 [3, 4, 0] = true := by decide +kernel
theorem subd15_2_1062 : subd15_2 [3, 4, 1] = true := by decide +kernel
theorem subd15_2_1063 : subd15_2 [3, 4, 2] = true := by decide +kernel
theorem subd15_2_1064 : subd15_2 [3, 4, 3] = true := by decide +kernel
theorem subd15_2_1065 : subd15_2 [3, 4, 4] = true := by decide +kernel
theorem subd15_2_1066 : subd15_2 [3, 4, 5] = true := by decide +kernel
theorem subd15_2_1067 : subd15_2 [3, 4, 6] = true := by decide +kernel
theorem subd15_2_1068 : subd15_2 [3, 4, 7] = true := by decide +kernel
theorem subd15_2_1069 : subd15_2 [3, 5] = true := by decide +kernel
theorem subd15_2_1070 : subd15_2 [3, 6] = true := by decide +kernel
theorem subd15_2_1071 : subd15_2 [3, 7] = true := by decide +kernel
theorem subd15_2_1072 : subd15_2 [4, -4] = true := by decide +kernel
theorem subd15_2_1073 : subd15_2 [4, -3] = true := by decide +kernel
theorem subd15_2_1074 : subd15_2 [4, -2] = true := by decide +kernel
theorem subd15_2_1075 : subd15_2 [4, -1] = true := by decide +kernel
theorem subd15_2_1076 : subd15_2 [4, 0] = true := by decide +kernel
theorem subd15_2_1077 : subd15_2 [4, 1, -6] = true := by decide +kernel
theorem subd15_2_1078 : subd15_2 [4, 1, -5] = true := by decide +kernel
theorem subd15_2_1079 : subd15_2 [4, 1, -4] = true := by decide +kernel
theorem subd15_2_1080 : subd15_2 [4, 1, -3] = true := by decide +kernel
theorem subd15_2_1081 : subd15_2 [4, 1, -2] = true := by decide +kernel
theorem subd15_2_1082 : subd15_2 [4, 1, -1] = true := by decide +kernel
theorem subd15_2_1083 : subd15_2 [4, 1, 0] = true := by decide +kernel
theorem subd15_2_1084 : subd15_2 [4, 1, 1] = true := by decide +kernel
theorem subd15_2_1085 : subd15_2 [4, 1, 2] = true := by decide +kernel
theorem subd15_2_1086 : subd15_2 [4, 1, 3] = true := by decide +kernel
theorem subd15_2_1087 : subd15_2 [4, 1, 4] = true := by decide +kernel
theorem sbd15_2_33 : ∀ q ∈ blkd15_2_33, subd15_2 q = true := by
  unfold blkd15_2_33
  exact List.forall_mem_cons.2 ⟨subd15_2_1056, List.forall_mem_cons.2 ⟨subd15_2_1057, List.forall_mem_cons.2 ⟨subd15_2_1058, List.forall_mem_cons.2 ⟨subd15_2_1059, List.forall_mem_cons.2 ⟨subd15_2_1060, List.forall_mem_cons.2 ⟨subd15_2_1061, List.forall_mem_cons.2 ⟨subd15_2_1062, List.forall_mem_cons.2 ⟨subd15_2_1063, List.forall_mem_cons.2 ⟨subd15_2_1064, List.forall_mem_cons.2 ⟨subd15_2_1065, List.forall_mem_cons.2 ⟨subd15_2_1066, List.forall_mem_cons.2 ⟨subd15_2_1067, List.forall_mem_cons.2 ⟨subd15_2_1068, List.forall_mem_cons.2 ⟨subd15_2_1069, List.forall_mem_cons.2 ⟨subd15_2_1070, List.forall_mem_cons.2 ⟨subd15_2_1071, List.forall_mem_cons.2 ⟨subd15_2_1072, List.forall_mem_cons.2 ⟨subd15_2_1073, List.forall_mem_cons.2 ⟨subd15_2_1074, List.forall_mem_cons.2 ⟨subd15_2_1075, List.forall_mem_cons.2 ⟨subd15_2_1076, List.forall_mem_cons.2 ⟨subd15_2_1077, List.forall_mem_cons.2 ⟨subd15_2_1078, List.forall_mem_cons.2 ⟨subd15_2_1079, List.forall_mem_cons.2 ⟨subd15_2_1080, List.forall_mem_cons.2 ⟨subd15_2_1081, List.forall_mem_cons.2 ⟨subd15_2_1082, List.forall_mem_cons.2 ⟨subd15_2_1083, List.forall_mem_cons.2 ⟨subd15_2_1084, List.forall_mem_cons.2 ⟨subd15_2_1085, List.forall_mem_cons.2 ⟨subd15_2_1086, List.forall_mem_cons.2 ⟨subd15_2_1087, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_2_1088 : subd15_2 [4, 1, 5] = true := by decide +kernel
theorem subd15_2_1089 : subd15_2 [4, 1, 6] = true := by decide +kernel
theorem subd15_2_1090 : subd15_2 [4, 1, 7] = true := by decide +kernel
theorem subd15_2_1091 : subd15_2 [4, 2, -6] = true := by decide +kernel
theorem subd15_2_1092 : subd15_2 [4, 2, -5] = true := by decide +kernel
theorem subd15_2_1093 : subd15_2 [4, 2, -4] = true := by decide +kernel
theorem subd15_2_1094 : subd15_2 [4, 2, -3] = true := by decide +kernel
theorem subd15_2_1095 : subd15_2 [4, 2, -2] = true := by decide +kernel
theorem subd15_2_1096 : subd15_2 [4, 2, -1] = true := by decide +kernel
theorem subd15_2_1097 : subd15_2 [4, 2, 0] = true := by decide +kernel
theorem subd15_2_1098 : subd15_2 [4, 2, 1] = true := by decide +kernel
theorem subd15_2_1099 : subd15_2 [4, 2, 2] = true := by decide +kernel
theorem subd15_2_1100 : subd15_2 [4, 2, 3] = true := by decide +kernel
theorem subd15_2_1101 : subd15_2 [4, 2, 4] = true := by decide +kernel
theorem subd15_2_1102 : subd15_2 [4, 2, 5] = true := by decide +kernel
theorem subd15_2_1103 : subd15_2 [4, 2, 6] = true := by decide +kernel
theorem subd15_2_1104 : subd15_2 [4, 2, 7] = true := by decide +kernel
theorem subd15_2_1105 : subd15_2 [4, 3, -6] = true := by decide +kernel
theorem subd15_2_1106 : subd15_2 [4, 3, -5] = true := by decide +kernel
theorem subd15_2_1107 : subd15_2 [4, 3, -4] = true := by decide +kernel
theorem subd15_2_1108 : subd15_2 [4, 3, -3] = true := by decide +kernel
theorem subd15_2_1109 : subd15_2 [4, 3, -2] = true := by decide +kernel
theorem subd15_2_1110 : subd15_2 [4, 3, -1] = true := by decide +kernel
theorem subd15_2_1111 : subd15_2 [4, 3, 0] = true := by decide +kernel
theorem subd15_2_1112 : subd15_2 [4, 3, 1] = true := by decide +kernel
theorem subd15_2_1113 : subd15_2 [4, 3, 2] = true := by decide +kernel
theorem subd15_2_1114 : subd15_2 [4, 3, 3] = true := by decide +kernel
theorem subd15_2_1115 : subd15_2 [4, 3, 4] = true := by decide +kernel
theorem subd15_2_1116 : subd15_2 [4, 3, 5] = true := by decide +kernel
theorem subd15_2_1117 : subd15_2 [4, 3, 6] = true := by decide +kernel
theorem subd15_2_1118 : subd15_2 [4, 3, 7] = true := by decide +kernel
theorem subd15_2_1119 : subd15_2 [4, 4] = true := by decide +kernel
theorem sbd15_2_34 : ∀ q ∈ blkd15_2_34, subd15_2 q = true := by
  unfold blkd15_2_34
  exact List.forall_mem_cons.2 ⟨subd15_2_1088, List.forall_mem_cons.2 ⟨subd15_2_1089, List.forall_mem_cons.2 ⟨subd15_2_1090, List.forall_mem_cons.2 ⟨subd15_2_1091, List.forall_mem_cons.2 ⟨subd15_2_1092, List.forall_mem_cons.2 ⟨subd15_2_1093, List.forall_mem_cons.2 ⟨subd15_2_1094, List.forall_mem_cons.2 ⟨subd15_2_1095, List.forall_mem_cons.2 ⟨subd15_2_1096, List.forall_mem_cons.2 ⟨subd15_2_1097, List.forall_mem_cons.2 ⟨subd15_2_1098, List.forall_mem_cons.2 ⟨subd15_2_1099, List.forall_mem_cons.2 ⟨subd15_2_1100, List.forall_mem_cons.2 ⟨subd15_2_1101, List.forall_mem_cons.2 ⟨subd15_2_1102, List.forall_mem_cons.2 ⟨subd15_2_1103, List.forall_mem_cons.2 ⟨subd15_2_1104, List.forall_mem_cons.2 ⟨subd15_2_1105, List.forall_mem_cons.2 ⟨subd15_2_1106, List.forall_mem_cons.2 ⟨subd15_2_1107, List.forall_mem_cons.2 ⟨subd15_2_1108, List.forall_mem_cons.2 ⟨subd15_2_1109, List.forall_mem_cons.2 ⟨subd15_2_1110, List.forall_mem_cons.2 ⟨subd15_2_1111, List.forall_mem_cons.2 ⟨subd15_2_1112, List.forall_mem_cons.2 ⟨subd15_2_1113, List.forall_mem_cons.2 ⟨subd15_2_1114, List.forall_mem_cons.2 ⟨subd15_2_1115, List.forall_mem_cons.2 ⟨subd15_2_1116, List.forall_mem_cons.2 ⟨subd15_2_1117, List.forall_mem_cons.2 ⟨subd15_2_1118, List.forall_mem_cons.2 ⟨subd15_2_1119, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd15_2_1120 : subd15_2 [4, 5] = true := by decide +kernel
theorem subd15_2_1121 : subd15_2 [4, 6] = true := by decide +kernel
theorem subd15_2_1122 : subd15_2 [5, -2] = true := by decide +kernel
theorem subd15_2_1123 : subd15_2 [5, -1] = true := by decide +kernel
theorem subd15_2_1124 : subd15_2 [5, 0] = true := by decide +kernel
theorem subd15_2_1125 : subd15_2 [5, 1] = true := by decide +kernel
theorem subd15_2_1126 : subd15_2 [5, 2] = true := by decide +kernel
theorem subd15_2_1127 : subd15_2 [5, 3] = true := by decide +kernel
theorem subd15_2_1128 : subd15_2 [5, 4] = true := by decide +kernel
theorem subd15_2_1129 : subd15_2 [5, 5] = true := by decide +kernel
theorem subd15_2_1130 : subd15_2 [5, 6] = true := by decide +kernel
theorem sbd15_2_35 : ∀ q ∈ blkd15_2_35, subd15_2 q = true := by
  unfold blkd15_2_35
  exact List.forall_mem_cons.2 ⟨subd15_2_1120, List.forall_mem_cons.2 ⟨subd15_2_1121, List.forall_mem_cons.2 ⟨subd15_2_1122, List.forall_mem_cons.2 ⟨subd15_2_1123, List.forall_mem_cons.2 ⟨subd15_2_1124, List.forall_mem_cons.2 ⟨subd15_2_1125, List.forall_mem_cons.2 ⟨subd15_2_1126, List.forall_mem_cons.2 ⟨subd15_2_1127, List.forall_mem_cons.2 ⟨subd15_2_1128, List.forall_mem_cons.2 ⟨subd15_2_1129, List.forall_mem_cons.2 ⟨subd15_2_1130, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd15_3 : ldCheck G d15_3.U d15_3.ms ldd15_3 = true := by decide +kernel
theorem pre_okd15_3 : subPre G cell15 d15_3 = true := by decide +kernel
theorem subd15_3_0 : subd15_3 [-2] = true := by decide +kernel
theorem subd15_3_1 : subd15_3 [-1, -2] = true := by decide +kernel
theorem subd15_3_2 : subd15_3 [-1, -1] = true := by decide +kernel
theorem subd15_3_3 : subd15_3 [-1, 0] = true := by decide +kernel
theorem subd15_3_4 : subd15_3 [-1, 1] = true := by decide +kernel
theorem subd15_3_5 : subd15_3 [-1, 2] = true := by decide +kernel
theorem subd15_3_6 : subd15_3 [0, -3] = true := by decide +kernel
theorem subd15_3_7 : subd15_3 [0, -2] = true := by decide +kernel
theorem subd15_3_8 : subd15_3 [0, -1] = true := by decide +kernel
theorem subd15_3_9 : subd15_3 [0, 0, -7] = true := by decide +kernel
theorem subd15_3_10 : subd15_3 [0, 0, -6] = true := by decide +kernel
theorem subd15_3_11 : subd15_3 [0, 0, -5] = true := by decide +kernel
theorem subd15_3_12 : subd15_3 [0, 0, -4] = true := by decide +kernel
theorem subd15_3_13 : subd15_3 [0, 0, -3] = true := by decide +kernel
theorem subd15_3_14 : subd15_3 [0, 0, -2] = true := by decide +kernel
theorem subd15_3_15 : subd15_3 [0, 0, -1] = true := by decide +kernel
theorem subd15_3_16 : subd15_3 [0, 0, 0] = true := by decide +kernel
theorem subd15_3_17 : subd15_3 [0, 0, 1] = true := by decide +kernel
theorem subd15_3_18 : subd15_3 [0, 0, 2] = true := by decide +kernel
theorem subd15_3_19 : subd15_3 [0, 0, 3] = true := by decide +kernel
theorem subd15_3_20 : subd15_3 [0, 0, 4] = true := by decide +kernel
theorem subd15_3_21 : subd15_3 [0, 0, 5] = true := by decide +kernel
theorem subd15_3_22 : subd15_3 [0, 0, 6] = true := by decide +kernel
theorem subd15_3_23 : subd15_3 [0, 1] = true := by decide +kernel
theorem subd15_3_24 : subd15_3 [0, 2] = true := by decide +kernel
theorem subd15_3_25 : subd15_3 [1, -3] = true := by decide +kernel
theorem subd15_3_26 : subd15_3 [1, -2] = true := by decide +kernel
theorem subd15_3_27 : subd15_3 [1, -1] = true := by decide +kernel
theorem subd15_3_28 : subd15_3 [1, 0] = true := by decide +kernel
theorem subd15_3_29 : subd15_3 [1, 1] = true := by decide +kernel
theorem subd15_3_30 : subd15_3 [2] = true := by decide +kernel
theorem sbd15_3_0 : ∀ q ∈ blkd15_3_0, subd15_3 q = true := by
  unfold blkd15_3_0
  exact List.forall_mem_cons.2 ⟨subd15_3_0, List.forall_mem_cons.2 ⟨subd15_3_1, List.forall_mem_cons.2 ⟨subd15_3_2, List.forall_mem_cons.2 ⟨subd15_3_3, List.forall_mem_cons.2 ⟨subd15_3_4, List.forall_mem_cons.2 ⟨subd15_3_5, List.forall_mem_cons.2 ⟨subd15_3_6, List.forall_mem_cons.2 ⟨subd15_3_7, List.forall_mem_cons.2 ⟨subd15_3_8, List.forall_mem_cons.2 ⟨subd15_3_9, List.forall_mem_cons.2 ⟨subd15_3_10, List.forall_mem_cons.2 ⟨subd15_3_11, List.forall_mem_cons.2 ⟨subd15_3_12, List.forall_mem_cons.2 ⟨subd15_3_13, List.forall_mem_cons.2 ⟨subd15_3_14, List.forall_mem_cons.2 ⟨subd15_3_15, List.forall_mem_cons.2 ⟨subd15_3_16, List.forall_mem_cons.2 ⟨subd15_3_17, List.forall_mem_cons.2 ⟨subd15_3_18, List.forall_mem_cons.2 ⟨subd15_3_19, List.forall_mem_cons.2 ⟨subd15_3_20, List.forall_mem_cons.2 ⟨subd15_3_21, List.forall_mem_cons.2 ⟨subd15_3_22, List.forall_mem_cons.2 ⟨subd15_3_23, List.forall_mem_cons.2 ⟨subd15_3_24, List.forall_mem_cons.2 ⟨subd15_3_25, List.forall_mem_cons.2 ⟨subd15_3_26, List.forall_mem_cons.2 ⟨subd15_3_27, List.forall_mem_cons.2 ⟨subd15_3_28, List.forall_mem_cons.2 ⟨subd15_3_29, List.forall_mem_cons.2 ⟨subd15_3_30, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd16_0 : ldCheck G d16_0.U d16_0.ms ldd16_0 = true := by decide +kernel
theorem pre_okd16_0 : subPre G cell16 d16_0 = true := by decide +kernel
theorem subd16_0_0 : subd16_0 [-3] = true := by decide +kernel
theorem subd16_0_1 : subd16_0 [-2] = true := by decide +kernel
theorem subd16_0_2 : subd16_0 [-1] = true := by decide +kernel
theorem subd16_0_3 : subd16_0 [0] = true := by decide +kernel
theorem subd16_0_4 : subd16_0 [1] = true := by decide +kernel
theorem subd16_0_5 : subd16_0 [2] = true := by decide +kernel
theorem subd16_0_6 : subd16_0 [3] = true := by decide +kernel
theorem sbd16_0_0 : ∀ q ∈ blkd16_0_0, subd16_0 q = true := by
  unfold blkd16_0_0
  exact List.forall_mem_cons.2 ⟨subd16_0_0, List.forall_mem_cons.2 ⟨subd16_0_1, List.forall_mem_cons.2 ⟨subd16_0_2, List.forall_mem_cons.2 ⟨subd16_0_3, List.forall_mem_cons.2 ⟨subd16_0_4, List.forall_mem_cons.2 ⟨subd16_0_5, List.forall_mem_cons.2 ⟨subd16_0_6, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd16_1 : ldCheck G d16_1.U d16_1.ms ldd16_1 = true := by decide +kernel
theorem pre_okd16_1 : subPre G cell16 d16_1 = true := by decide +kernel
theorem subd16_1_0 : subd16_1 [-1] = true := by decide +kernel
theorem subd16_1_1 : subd16_1 [0, -2] = true := by decide +kernel
theorem subd16_1_2 : subd16_1 [0, -1] = true := by decide +kernel
theorem subd16_1_3 : subd16_1 [0, 0] = true := by decide +kernel
theorem subd16_1_4 : subd16_1 [0, 1] = true := by decide +kernel
theorem subd16_1_5 : subd16_1 [1] = true := by decide +kernel
theorem sbd16_1_0 : ∀ q ∈ blkd16_1_0, subd16_1 q = true := by
  unfold blkd16_1_0
  exact List.forall_mem_cons.2 ⟨subd16_1_0, List.forall_mem_cons.2 ⟨subd16_1_1, List.forall_mem_cons.2 ⟨subd16_1_2, List.forall_mem_cons.2 ⟨subd16_1_3, List.forall_mem_cons.2 ⟨subd16_1_4, List.forall_mem_cons.2 ⟨subd16_1_5, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd16_2 : ldCheck G d16_2.U d16_2.ms ldd16_2 = true := by decide +kernel
theorem pre_okd16_2 : subPre G cell16 d16_2 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C142
