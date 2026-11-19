import ReflectZphi.Data.Cert5.C125.Base

namespace ReflectZphi.Data.Cert5.C125
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub9_1056 : sub9 [4, 1, -2] = true := by decide +kernel
theorem sub9_1057 : sub9 [4, 1, -1] = true := by decide +kernel
theorem sub9_1058 : sub9 [4, 1, 0] = true := by decide +kernel
theorem sub9_1059 : sub9 [4, 1, 1] = true := by decide +kernel
theorem sub9_1060 : sub9 [4, 1, 2] = true := by decide +kernel
theorem sub9_1061 : sub9 [4, 1, 3] = true := by decide +kernel
theorem sub9_1062 : sub9 [4, 1, 4] = true := by decide +kernel
theorem sub9_1063 : sub9 [4, 1, 5] = true := by decide +kernel
theorem sub9_1064 : sub9 [4, 1, 6] = true := by decide +kernel
theorem sub9_1065 : sub9 [4, 1, 7] = true := by decide +kernel
theorem sub9_1066 : sub9 [4, 2, -6] = true := by decide +kernel
theorem sub9_1067 : sub9 [4, 2, -5] = true := by decide +kernel
theorem sub9_1068 : sub9 [4, 2, -4] = true := by decide +kernel
theorem sub9_1069 : sub9 [4, 2, -3] = true := by decide +kernel
theorem sub9_1070 : sub9 [4, 2, -2] = true := by decide +kernel
theorem sub9_1071 : sub9 [4, 2, -1] = true := by decide +kernel
theorem sub9_1072 : sub9 [4, 2, 0] = true := by decide +kernel
theorem sub9_1073 : sub9 [4, 2, 1] = true := by decide +kernel
theorem sub9_1074 : sub9 [4, 2, 2] = true := by decide +kernel
theorem sub9_1075 : sub9 [4, 2, 3] = true := by decide +kernel
theorem sub9_1076 : sub9 [4, 2, 4] = true := by decide +kernel
theorem sub9_1077 : sub9 [4, 2, 5] = true := by decide +kernel
theorem sub9_1078 : sub9 [4, 2, 6] = true := by decide +kernel
theorem sub9_1079 : sub9 [4, 2, 7] = true := by decide +kernel
theorem sub9_1080 : sub9 [4, 3, -5] = true := by decide +kernel
theorem sub9_1081 : sub9 [4, 3, -4] = true := by decide +kernel
theorem sub9_1082 : sub9 [4, 3, -3] = true := by decide +kernel
theorem sub9_1083 : sub9 [4, 3, -2] = true := by decide +kernel
theorem sub9_1084 : sub9 [4, 3, -1] = true := by decide +kernel
theorem sub9_1085 : sub9 [4, 3, 0] = true := by decide +kernel
theorem sub9_1086 : sub9 [4, 3, 1] = true := by decide +kernel
theorem sub9_1087 : sub9 [4, 3, 2] = true := by decide +kernel
theorem sb9_33 : ∀ q ∈ blk9_33, sub9 q = true := by
  unfold blk9_33
  exact List.forall_mem_cons.2 ⟨sub9_1056, List.forall_mem_cons.2 ⟨sub9_1057, List.forall_mem_cons.2 ⟨sub9_1058, List.forall_mem_cons.2 ⟨sub9_1059, List.forall_mem_cons.2 ⟨sub9_1060, List.forall_mem_cons.2 ⟨sub9_1061, List.forall_mem_cons.2 ⟨sub9_1062, List.forall_mem_cons.2 ⟨sub9_1063, List.forall_mem_cons.2 ⟨sub9_1064, List.forall_mem_cons.2 ⟨sub9_1065, List.forall_mem_cons.2 ⟨sub9_1066, List.forall_mem_cons.2 ⟨sub9_1067, List.forall_mem_cons.2 ⟨sub9_1068, List.forall_mem_cons.2 ⟨sub9_1069, List.forall_mem_cons.2 ⟨sub9_1070, List.forall_mem_cons.2 ⟨sub9_1071, List.forall_mem_cons.2 ⟨sub9_1072, List.forall_mem_cons.2 ⟨sub9_1073, List.forall_mem_cons.2 ⟨sub9_1074, List.forall_mem_cons.2 ⟨sub9_1075, List.forall_mem_cons.2 ⟨sub9_1076, List.forall_mem_cons.2 ⟨sub9_1077, List.forall_mem_cons.2 ⟨sub9_1078, List.forall_mem_cons.2 ⟨sub9_1079, List.forall_mem_cons.2 ⟨sub9_1080, List.forall_mem_cons.2 ⟨sub9_1081, List.forall_mem_cons.2 ⟨sub9_1082, List.forall_mem_cons.2 ⟨sub9_1083, List.forall_mem_cons.2 ⟨sub9_1084, List.forall_mem_cons.2 ⟨sub9_1085, List.forall_mem_cons.2 ⟨sub9_1086, List.forall_mem_cons.2 ⟨sub9_1087, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_1088 : sub9 [4, 3, 3] = true := by decide +kernel
theorem sub9_1089 : sub9 [4, 3, 4] = true := by decide +kernel
theorem sub9_1090 : sub9 [4, 3, 5] = true := by decide +kernel
theorem sub9_1091 : sub9 [4, 3, 6] = true := by decide +kernel
theorem sub9_1092 : sub9 [4, 3, 7] = true := by decide +kernel
theorem sub9_1093 : sub9 [4, 4] = true := by decide +kernel
theorem sub9_1094 : sub9 [4, 5] = true := by decide +kernel
theorem sub9_1095 : sub9 [4, 6] = true := by decide +kernel
theorem sub9_1096 : sub9 [4, 7] = true := by decide +kernel
theorem sub9_1097 : sub9 [5, -6] = true := by decide +kernel
theorem sub9_1098 : sub9 [5, -5] = true := by decide +kernel
theorem sub9_1099 : sub9 [5, -4] = true := by decide +kernel
theorem sub9_1100 : sub9 [5, -3] = true := by decide +kernel
theorem sub9_1101 : sub9 [5, -2] = true := by decide +kernel
theorem sub9_1102 : sub9 [5, -1] = true := by decide +kernel
theorem sub9_1103 : sub9 [5, 0] = true := by decide +kernel
theorem sub9_1104 : sub9 [5, 1] = true := by decide +kernel
theorem sub9_1105 : sub9 [5, 2] = true := by decide +kernel
theorem sub9_1106 : sub9 [5, 3] = true := by decide +kernel
theorem sub9_1107 : sub9 [5, 4] = true := by decide +kernel
theorem sub9_1108 : sub9 [5, 5] = true := by decide +kernel
theorem sub9_1109 : sub9 [5, 6] = true := by decide +kernel
theorem sub9_1110 : sub9 [5, 7] = true := by decide +kernel
theorem sub9_1111 : sub9 [6, -5] = true := by decide +kernel
theorem sub9_1112 : sub9 [6, -4] = true := by decide +kernel
theorem sub9_1113 : sub9 [6, -3] = true := by decide +kernel
theorem sub9_1114 : sub9 [6, -2] = true := by decide +kernel
theorem sub9_1115 : sub9 [6, -1] = true := by decide +kernel
theorem sub9_1116 : sub9 [6, 0] = true := by decide +kernel
theorem sub9_1117 : sub9 [6, 1] = true := by decide +kernel
theorem sub9_1118 : sub9 [6, 2] = true := by decide +kernel
theorem sub9_1119 : sub9 [6, 3] = true := by decide +kernel
theorem sb9_34 : ∀ q ∈ blk9_34, sub9 q = true := by
  unfold blk9_34
  exact List.forall_mem_cons.2 ⟨sub9_1088, List.forall_mem_cons.2 ⟨sub9_1089, List.forall_mem_cons.2 ⟨sub9_1090, List.forall_mem_cons.2 ⟨sub9_1091, List.forall_mem_cons.2 ⟨sub9_1092, List.forall_mem_cons.2 ⟨sub9_1093, List.forall_mem_cons.2 ⟨sub9_1094, List.forall_mem_cons.2 ⟨sub9_1095, List.forall_mem_cons.2 ⟨sub9_1096, List.forall_mem_cons.2 ⟨sub9_1097, List.forall_mem_cons.2 ⟨sub9_1098, List.forall_mem_cons.2 ⟨sub9_1099, List.forall_mem_cons.2 ⟨sub9_1100, List.forall_mem_cons.2 ⟨sub9_1101, List.forall_mem_cons.2 ⟨sub9_1102, List.forall_mem_cons.2 ⟨sub9_1103, List.forall_mem_cons.2 ⟨sub9_1104, List.forall_mem_cons.2 ⟨sub9_1105, List.forall_mem_cons.2 ⟨sub9_1106, List.forall_mem_cons.2 ⟨sub9_1107, List.forall_mem_cons.2 ⟨sub9_1108, List.forall_mem_cons.2 ⟨sub9_1109, List.forall_mem_cons.2 ⟨sub9_1110, List.forall_mem_cons.2 ⟨sub9_1111, List.forall_mem_cons.2 ⟨sub9_1112, List.forall_mem_cons.2 ⟨sub9_1113, List.forall_mem_cons.2 ⟨sub9_1114, List.forall_mem_cons.2 ⟨sub9_1115, List.forall_mem_cons.2 ⟨sub9_1116, List.forall_mem_cons.2 ⟨sub9_1117, List.forall_mem_cons.2 ⟨sub9_1118, List.forall_mem_cons.2 ⟨sub9_1119, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_1120 : sub9 [6, 4] = true := by decide +kernel
theorem sub9_1121 : sub9 [6, 5] = true := by decide +kernel
theorem sub9_1122 : sub9 [6, 6] = true := by decide +kernel
theorem sub9_1123 : sub9 [6, 7] = true := by decide +kernel
theorem sub9_1124 : sub9 [7, -4] = true := by decide +kernel
theorem sub9_1125 : sub9 [7, -3] = true := by decide +kernel
theorem sub9_1126 : sub9 [7, -2] = true := by decide +kernel
theorem sub9_1127 : sub9 [7, -1] = true := by decide +kernel
theorem sub9_1128 : sub9 [7, 0] = true := by decide +kernel
theorem sub9_1129 : sub9 [7, 1] = true := by decide +kernel
theorem sub9_1130 : sub9 [7, 2] = true := by decide +kernel
theorem sub9_1131 : sub9 [7, 3] = true := by decide +kernel
theorem sub9_1132 : sub9 [7, 4] = true := by decide +kernel
theorem sub9_1133 : sub9 [7, 5] = true := by decide +kernel
theorem sub9_1134 : sub9 [7, 6] = true := by decide +kernel
theorem sub9_1135 : sub9 [8, -3] = true := by decide +kernel
theorem sub9_1136 : sub9 [8, -2] = true := by decide +kernel
theorem sub9_1137 : sub9 [8, -1] = true := by decide +kernel
theorem sub9_1138 : sub9 [8, 0] = true := by decide +kernel
theorem sub9_1139 : sub9 [8, 1] = true := by decide +kernel
theorem sub9_1140 : sub9 [8, 2] = true := by decide +kernel
theorem sub9_1141 : sub9 [8, 3] = true := by decide +kernel
theorem sub9_1142 : sub9 [8, 4] = true := by decide +kernel
theorem sub9_1143 : sub9 [8, 5] = true := by decide +kernel
theorem sub9_1144 : sub9 [9] = true := by decide +kernel
theorem sb9_35 : ∀ q ∈ blk9_35, sub9 q = true := by
  unfold blk9_35
  exact List.forall_mem_cons.2 ⟨sub9_1120, List.forall_mem_cons.2 ⟨sub9_1121, List.forall_mem_cons.2 ⟨sub9_1122, List.forall_mem_cons.2 ⟨sub9_1123, List.forall_mem_cons.2 ⟨sub9_1124, List.forall_mem_cons.2 ⟨sub9_1125, List.forall_mem_cons.2 ⟨sub9_1126, List.forall_mem_cons.2 ⟨sub9_1127, List.forall_mem_cons.2 ⟨sub9_1128, List.forall_mem_cons.2 ⟨sub9_1129, List.forall_mem_cons.2 ⟨sub9_1130, List.forall_mem_cons.2 ⟨sub9_1131, List.forall_mem_cons.2 ⟨sub9_1132, List.forall_mem_cons.2 ⟨sub9_1133, List.forall_mem_cons.2 ⟨sub9_1134, List.forall_mem_cons.2 ⟨sub9_1135, List.forall_mem_cons.2 ⟨sub9_1136, List.forall_mem_cons.2 ⟨sub9_1137, List.forall_mem_cons.2 ⟨sub9_1138, List.forall_mem_cons.2 ⟨sub9_1139, List.forall_mem_cons.2 ⟨sub9_1140, List.forall_mem_cons.2 ⟨sub9_1141, List.forall_mem_cons.2 ⟨sub9_1142, List.forall_mem_cons.2 ⟨sub9_1143, List.forall_mem_cons.2 ⟨sub9_1144, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_0 : sub10 [-4, -4] = true := by decide +kernel
theorem sub10_1 : sub10 [-4, -3] = true := by decide +kernel
theorem sub10_2 : sub10 [-4, -2] = true := by decide +kernel
theorem sub10_3 : sub10 [-4, -1] = true := by decide +kernel
theorem sub10_4 : sub10 [-4, 0] = true := by decide +kernel
theorem sub10_5 : sub10 [-4, 1] = true := by decide +kernel
theorem sub10_6 : sub10 [-3, -5] = true := by decide +kernel
theorem sub10_7 : sub10 [-3, -4] = true := by decide +kernel
theorem sub10_8 : sub10 [-3, -3] = true := by decide +kernel
theorem sub10_9 : sub10 [-3, -2] = true := by decide +kernel
theorem sub10_10 : sub10 [-3, -1] = true := by decide +kernel
theorem sub10_11 : sub10 [-3, 0] = true := by decide +kernel
theorem sub10_12 : sub10 [-3, 1] = true := by decide +kernel
theorem sub10_13 : sub10 [-3, 2] = true := by decide +kernel
theorem sub10_14 : sub10 [-3, 3] = true := by decide +kernel
theorem sub10_15 : sub10 [-2, -6] = true := by decide +kernel
theorem sub10_16 : sub10 [-2, -5] = true := by decide +kernel
theorem sub10_17 : sub10 [-2, -4] = true := by decide +kernel
theorem sub10_18 : sub10 [-2, -3] = true := by decide +kernel
theorem sub10_19 : sub10 [-2, -2, -8] = true := by decide +kernel
theorem sub10_20 : sub10 [-2, -2, -7] = true := by decide +kernel
theorem sub10_21 : sub10 [-2, -2, -6] = true := by decide +kernel
theorem sub10_22 : sub10 [-2, -2, -5] = true := by decide +kernel
theorem sub10_23 : sub10 [-2, -2, -4] = true := by decide +kernel
theorem sub10_24 : sub10 [-2, -2, -3] = true := by decide +kernel
theorem sub10_25 : sub10 [-2, -2, -2] = true := by decide +kernel
theorem sub10_26 : sub10 [-2, -2, -1] = true := by decide +kernel
theorem sub10_27 : sub10 [-2, -2, 0] = true := by decide +kernel
theorem sub10_28 : sub10 [-2, -2, 1] = true := by decide +kernel
theorem sub10_29 : sub10 [-2, -2, 2] = true := by decide +kernel
theorem sub10_30 : sub10 [-2, -2, 3] = true := by decide +kernel
theorem sub10_31 : sub10 [-2, -2, 4] = true := by decide +kernel
theorem sb10_0 : ∀ q ∈ blk10_0, sub10 q = true := by
  unfold blk10_0
  exact List.forall_mem_cons.2 ⟨sub10_0, List.forall_mem_cons.2 ⟨sub10_1, List.forall_mem_cons.2 ⟨sub10_2, List.forall_mem_cons.2 ⟨sub10_3, List.forall_mem_cons.2 ⟨sub10_4, List.forall_mem_cons.2 ⟨sub10_5, List.forall_mem_cons.2 ⟨sub10_6, List.forall_mem_cons.2 ⟨sub10_7, List.forall_mem_cons.2 ⟨sub10_8, List.forall_mem_cons.2 ⟨sub10_9, List.forall_mem_cons.2 ⟨sub10_10, List.forall_mem_cons.2 ⟨sub10_11, List.forall_mem_cons.2 ⟨sub10_12, List.forall_mem_cons.2 ⟨sub10_13, List.forall_mem_cons.2 ⟨sub10_14, List.forall_mem_cons.2 ⟨sub10_15, List.forall_mem_cons.2 ⟨sub10_16, List.forall_mem_cons.2 ⟨sub10_17, List.forall_mem_cons.2 ⟨sub10_18, List.forall_mem_cons.2 ⟨sub10_19, List.forall_mem_cons.2 ⟨sub10_20, List.forall_mem_cons.2 ⟨sub10_21, List.forall_mem_cons.2 ⟨sub10_22, List.forall_mem_cons.2 ⟨sub10_23, List.forall_mem_cons.2 ⟨sub10_24, List.forall_mem_cons.2 ⟨sub10_25, List.forall_mem_cons.2 ⟨sub10_26, List.forall_mem_cons.2 ⟨sub10_27, List.forall_mem_cons.2 ⟨sub10_28, List.forall_mem_cons.2 ⟨sub10_29, List.forall_mem_cons.2 ⟨sub10_30, List.forall_mem_cons.2 ⟨sub10_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_32 : sub10 [-2, -2, 5] = true := by decide +kernel
theorem sub10_33 : sub10 [-2, -2, 6] = true := by decide +kernel
theorem sub10_34 : sub10 [-2, -1, -8] = true := by decide +kernel
theorem sub10_35 : sub10 [-2, -1, -7] = true := by decide +kernel
theorem sub10_36 : sub10 [-2, -1, -6] = true := by decide +kernel
theorem sub10_37 : sub10 [-2, -1, -5] = true := by decide +kernel
theorem sub10_38 : sub10 [-2, -1, -4] = true := by decide +kernel
theorem sub10_39 : sub10 [-2, -1, -3] = true := by decide +kernel
theorem sub10_40 : sub10 [-2, -1, -2] = true := by decide +kernel
theorem sub10_41 : sub10 [-2, -1, -1] = true := by decide +kernel
theorem sub10_42 : sub10 [-2, -1, 0] = true := by decide +kernel
theorem sub10_43 : sub10 [-2, -1, 1] = true := by decide +kernel
theorem sub10_44 : sub10 [-2, -1, 2] = true := by decide +kernel
theorem sub10_45 : sub10 [-2, -1, 3] = true := by decide +kernel
theorem sub10_46 : sub10 [-2, -1, 4] = true := by decide +kernel
theorem sub10_47 : sub10 [-2, -1, 5] = true := by decide +kernel
theorem sub10_48 : sub10 [-2, -1, 6] = true := by decide +kernel
theorem sub10_49 : sub10 [-2, -1, 7] = true := by decide +kernel
theorem sub10_50 : sub10 [-2, 0, -8] = true := by decide +kernel
theorem sub10_51 : sub10 [-2, 0, -7] = true := by decide +kernel
theorem sub10_52 : sub10 [-2, 0, -6] = true := by decide +kernel
theorem sub10_53 : sub10 [-2, 0, -5] = true := by decide +kernel
theorem sub10_54 : sub10 [-2, 0, -4] = true := by decide +kernel
theorem sub10_55 : sub10 [-2, 0, -3] = true := by decide +kernel
theorem sub10_56 : sub10 [-2, 0, -2] = true := by decide +kernel
theorem sub10_57 : sub10 [-2, 0, -1] = true := by decide +kernel
theorem sub10_58 : sub10 [-2, 0, 0] = true := by decide +kernel
theorem sub10_59 : sub10 [-2, 0, 1] = true := by decide +kernel
theorem sub10_60 : sub10 [-2, 0, 2] = true := by decide +kernel
theorem sub10_61 : sub10 [-2, 0, 3] = true := by decide +kernel
theorem sub10_62 : sub10 [-2, 0, 4] = true := by decide +kernel
theorem sub10_63 : sub10 [-2, 0, 5] = true := by decide +kernel
theorem sb10_1 : ∀ q ∈ blk10_1, sub10 q = true := by
  unfold blk10_1
  exact List.forall_mem_cons.2 ⟨sub10_32, List.forall_mem_cons.2 ⟨sub10_33, List.forall_mem_cons.2 ⟨sub10_34, List.forall_mem_cons.2 ⟨sub10_35, List.forall_mem_cons.2 ⟨sub10_36, List.forall_mem_cons.2 ⟨sub10_37, List.forall_mem_cons.2 ⟨sub10_38, List.forall_mem_cons.2 ⟨sub10_39, List.forall_mem_cons.2 ⟨sub10_40, List.forall_mem_cons.2 ⟨sub10_41, List.forall_mem_cons.2 ⟨sub10_42, List.forall_mem_cons.2 ⟨sub10_43, List.forall_mem_cons.2 ⟨sub10_44, List.forall_mem_cons.2 ⟨sub10_45, List.forall_mem_cons.2 ⟨sub10_46, List.forall_mem_cons.2 ⟨sub10_47, List.forall_mem_cons.2 ⟨sub10_48, List.forall_mem_cons.2 ⟨sub10_49, List.forall_mem_cons.2 ⟨sub10_50, List.forall_mem_cons.2 ⟨sub10_51, List.forall_mem_cons.2 ⟨sub10_52, List.forall_mem_cons.2 ⟨sub10_53, List.forall_mem_cons.2 ⟨sub10_54, List.forall_mem_cons.2 ⟨sub10_55, List.forall_mem_cons.2 ⟨sub10_56, List.forall_mem_cons.2 ⟨sub10_57, List.forall_mem_cons.2 ⟨sub10_58, List.forall_mem_cons.2 ⟨sub10_59, List.forall_mem_cons.2 ⟨sub10_60, List.forall_mem_cons.2 ⟨sub10_61, List.forall_mem_cons.2 ⟨sub10_62, List.forall_mem_cons.2 ⟨sub10_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_64 : sub10 [-2, 0, 6] = true := by decide +kernel
theorem sub10_65 : sub10 [-2, 0, 7] = true := by decide +kernel
theorem sub10_66 : sub10 [-2, 1, -7] = true := by decide +kernel
theorem sub10_67 : sub10 [-2, 1, -6] = true := by decide +kernel
theorem sub10_68 : sub10 [-2, 1, -5] = true := by decide +kernel
theorem sub10_69 : sub10 [-2, 1, -4] = true := by decide +kernel
theorem sub10_70 : sub10 [-2, 1, -3] = true := by decide +kernel
theorem sub10_71 : sub10 [-2, 1, -2] = true := by decide +kernel
theorem sub10_72 : sub10 [-2, 1, -1] = true := by decide +kernel
theorem sub10_73 : sub10 [-2, 1, 0] = true := by decide +kernel
theorem sub10_74 : sub10 [-2, 1, 1] = true := by decide +kernel
theorem sub10_75 : sub10 [-2, 1, 2] = true := by decide +kernel
theorem sub10_76 : sub10 [-2, 1, 3] = true := by decide +kernel
theorem sub10_77 : sub10 [-2, 1, 4] = true := by decide +kernel
theorem sub10_78 : sub10 [-2, 1, 5] = true := by decide +kernel
theorem sub10_79 : sub10 [-2, 1, 6] = true := by decide +kernel
theorem sub10_80 : sub10 [-2, 1, 7] = true := by decide +kernel
theorem sub10_81 : sub10 [-2, 2] = true := by decide +kernel
theorem sub10_82 : sub10 [-2, 3] = true := by decide +kernel
theorem sub10_83 : sub10 [-2, 4] = true := by decide +kernel
theorem sub10_84 : sub10 [-1, -6] = true := by decide +kernel
theorem sub10_85 : sub10 [-1, -5] = true := by decide +kernel
theorem sub10_86 : sub10 [-1, -4] = true := by decide +kernel
theorem sub10_87 : sub10 [-1, -3, -8] = true := by decide +kernel
theorem sub10_88 : sub10 [-1, -3, -7] = true := by decide +kernel
theorem sub10_89 : sub10 [-1, -3, -6] = true := by decide +kernel
theorem sub10_90 : sub10 [-1, -3, -5] = true := by decide +kernel
theorem sub10_91 : sub10 [-1, -3, -4] = true := by decide +kernel
theorem sub10_92 : sub10 [-1, -3, -3] = true := by decide +kernel
theorem sub10_93 : sub10 [-1, -3, -2] = true := by decide +kernel
theorem sub10_94 : sub10 [-1, -3, -1] = true := by decide +kernel
theorem sub10_95 : sub10 [-1, -3, 0] = true := by decide +kernel
theorem sb10_2 : ∀ q ∈ blk10_2, sub10 q = true := by
  unfold blk10_2
  exact List.forall_mem_cons.2 ⟨sub10_64, List.forall_mem_cons.2 ⟨sub10_65, List.forall_mem_cons.2 ⟨sub10_66, List.forall_mem_cons.2 ⟨sub10_67, List.forall_mem_cons.2 ⟨sub10_68, List.forall_mem_cons.2 ⟨sub10_69, List.forall_mem_cons.2 ⟨sub10_70, List.forall_mem_cons.2 ⟨sub10_71, List.forall_mem_cons.2 ⟨sub10_72, List.forall_mem_cons.2 ⟨sub10_73, List.forall_mem_cons.2 ⟨sub10_74, List.forall_mem_cons.2 ⟨sub10_75, List.forall_mem_cons.2 ⟨sub10_76, List.forall_mem_cons.2 ⟨sub10_77, List.forall_mem_cons.2 ⟨sub10_78, List.forall_mem_cons.2 ⟨sub10_79, List.forall_mem_cons.2 ⟨sub10_80, List.forall_mem_cons.2 ⟨sub10_81, List.forall_mem_cons.2 ⟨sub10_82, List.forall_mem_cons.2 ⟨sub10_83, List.forall_mem_cons.2 ⟨sub10_84, List.forall_mem_cons.2 ⟨sub10_85, List.forall_mem_cons.2 ⟨sub10_86, List.forall_mem_cons.2 ⟨sub10_87, List.forall_mem_cons.2 ⟨sub10_88, List.forall_mem_cons.2 ⟨sub10_89, List.forall_mem_cons.2 ⟨sub10_90, List.forall_mem_cons.2 ⟨sub10_91, List.forall_mem_cons.2 ⟨sub10_92, List.forall_mem_cons.2 ⟨sub10_93, List.forall_mem_cons.2 ⟨sub10_94, List.forall_mem_cons.2 ⟨sub10_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_96 : sub10 [-1, -3, 1] = true := by decide +kernel
theorem sub10_97 : sub10 [-1, -3, 2] = true := by decide +kernel
theorem sub10_98 : sub10 [-1, -3, 3] = true := by decide +kernel
theorem sub10_99 : sub10 [-1, -3, 4] = true := by decide +kernel
theorem sub10_100 : sub10 [-1, -3, 5] = true := by decide +kernel
theorem sub10_101 : sub10 [-1, -2, -9] = true := by decide +kernel
theorem sub10_102 : sub10 [-1, -2, -8] = true := by decide +kernel
theorem sub10_103 : sub10 [-1, -2, -7] = true := by decide +kernel
theorem sub10_104 : sub10 [-1, -2, -6] = true := by decide +kernel
theorem sub10_105 : sub10 [-1, -2, -5] = true := by decide +kernel
theorem sub10_106 : sub10 [-1, -2, -4] = true := by decide +kernel
theorem sub10_107 : sub10 [-1, -2, -3] = true := by decide +kernel
theorem sub10_108 : sub10 [-1, -2, -2] = true := by decide +kernel
theorem sub10_109 : sub10 [-1, -2, -1] = true := by decide +kernel
theorem sub10_110 : sub10 [-1, -2, 0] = true := by decide +kernel
theorem sub10_111 : sub10 [-1, -2, 1] = true := by decide +kernel
theorem sub10_112 : sub10 [-1, -2, 2] = true := by decide +kernel
theorem sub10_113 : sub10 [-1, -2, 3] = true := by decide +kernel
theorem sub10_114 : sub10 [-1, -2, 4] = true := by decide +kernel
theorem sub10_115 : sub10 [-1, -2, 5] = true := by decide +kernel
theorem sub10_116 : sub10 [-1, -2, 6] = true := by decide +kernel
theorem sub10_117 : sub10 [-1, -1, -9] = true := by decide +kernel
theorem sub10_118 : sub10 [-1, -1, -8] = true := by decide +kernel
theorem sub10_119 : sub10 [-1, -1, -7] = true := by decide +kernel
theorem sub10_120 : sub10 [-1, -1, -6] = true := by decide +kernel
theorem sub10_121 : sub10 [-1, -1, -5] = true := by decide +kernel
theorem sub10_122 : sub10 [-1, -1, -4] = true := by decide +kernel
theorem sub10_123 : sub10 [-1, -1, -3] = true := by decide +kernel
theorem sub10_124 : sub10 [-1, -1, -2] = true := by decide +kernel
theorem sub10_125 : sub10 [-1, -1, -1] = true := by decide +kernel
theorem sub10_126 : sub10 [-1, -1, 0] = true := by decide +kernel
theorem sub10_127 : sub10 [-1, -1, 1] = true := by decide +kernel
theorem sb10_3 : ∀ q ∈ blk10_3, sub10 q = true := by
  unfold blk10_3
  exact List.forall_mem_cons.2 ⟨sub10_96, List.forall_mem_cons.2 ⟨sub10_97, List.forall_mem_cons.2 ⟨sub10_98, List.forall_mem_cons.2 ⟨sub10_99, List.forall_mem_cons.2 ⟨sub10_100, List.forall_mem_cons.2 ⟨sub10_101, List.forall_mem_cons.2 ⟨sub10_102, List.forall_mem_cons.2 ⟨sub10_103, List.forall_mem_cons.2 ⟨sub10_104, List.forall_mem_cons.2 ⟨sub10_105, List.forall_mem_cons.2 ⟨sub10_106, List.forall_mem_cons.2 ⟨sub10_107, List.forall_mem_cons.2 ⟨sub10_108, List.forall_mem_cons.2 ⟨sub10_109, List.forall_mem_cons.2 ⟨sub10_110, List.forall_mem_cons.2 ⟨sub10_111, List.forall_mem_cons.2 ⟨sub10_112, List.forall_mem_cons.2 ⟨sub10_113, List.forall_mem_cons.2 ⟨sub10_114, List.forall_mem_cons.2 ⟨sub10_115, List.forall_mem_cons.2 ⟨sub10_116, List.forall_mem_cons.2 ⟨sub10_117, List.forall_mem_cons.2 ⟨sub10_118, List.forall_mem_cons.2 ⟨sub10_119, List.forall_mem_cons.2 ⟨sub10_120, List.forall_mem_cons.2 ⟨sub10_121, List.forall_mem_cons.2 ⟨sub10_122, List.forall_mem_cons.2 ⟨sub10_123, List.forall_mem_cons.2 ⟨sub10_124, List.forall_mem_cons.2 ⟨sub10_125, List.forall_mem_cons.2 ⟨sub10_126, List.forall_mem_cons.2 ⟨sub10_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C125
