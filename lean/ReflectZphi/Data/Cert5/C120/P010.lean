import ReflectZphi.Data.Cert5.C120.Base

namespace ReflectZphi.Data.Cert5.C120
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub8_1056 : sub8 [3, 0, 5] = true := by decide +kernel
theorem sub8_1057 : sub8 [3, 0, 6] = true := by decide +kernel
theorem sub8_1058 : sub8 [3, 0, 7] = true := by decide +kernel
theorem sub8_1059 : sub8 [3, 0, 8] = true := by decide +kernel
theorem sub8_1060 : sub8 [3, 0, 9] = true := by decide +kernel
theorem sub8_1061 : sub8 [3, 1, -9] = true := by decide +kernel
theorem sub8_1062 : sub8 [3, 1, -8] = true := by decide +kernel
theorem sub8_1063 : sub8 [3, 1, -7] = true := by decide +kernel
theorem sub8_1064 : sub8 [3, 1, -6] = true := by decide +kernel
theorem sub8_1065 : sub8 [3, 1, -5] = true := by decide +kernel
theorem sub8_1066 : sub8 [3, 1, -4] = true := by decide +kernel
theorem sub8_1067 : sub8 [3, 1, -3] = true := by decide +kernel
theorem sub8_1068 : sub8 [3, 1, -2] = true := by decide +kernel
theorem sub8_1069 : sub8 [3, 1, -1] = true := by decide +kernel
theorem sub8_1070 : sub8 [3, 1, 0] = true := by decide +kernel
theorem sub8_1071 : sub8 [3, 1, 1] = true := by decide +kernel
theorem sub8_1072 : sub8 [3, 1, 2] = true := by decide +kernel
theorem sub8_1073 : sub8 [3, 1, 3] = true := by decide +kernel
theorem sub8_1074 : sub8 [3, 1, 4] = true := by decide +kernel
theorem sub8_1075 : sub8 [3, 1, 5] = true := by decide +kernel
theorem sub8_1076 : sub8 [3, 1, 6] = true := by decide +kernel
theorem sub8_1077 : sub8 [3, 1, 7] = true := by decide +kernel
theorem sub8_1078 : sub8 [3, 1, 8] = true := by decide +kernel
theorem sub8_1079 : sub8 [3, 2, -8] = true := by decide +kernel
theorem sub8_1080 : sub8 [3, 2, -7] = true := by decide +kernel
theorem sub8_1081 : sub8 [3, 2, -6] = true := by decide +kernel
theorem sub8_1082 : sub8 [3, 2, -5] = true := by decide +kernel
theorem sub8_1083 : sub8 [3, 2, -4] = true := by decide +kernel
theorem sub8_1084 : sub8 [3, 2, -3] = true := by decide +kernel
theorem sub8_1085 : sub8 [3, 2, -2] = true := by decide +kernel
theorem sub8_1086 : sub8 [3, 2, -1] = true := by decide +kernel
theorem sub8_1087 : sub8 [3, 2, 0] = true := by decide +kernel
theorem sb8_33 : ∀ q ∈ blk8_33, sub8 q = true := by
  unfold blk8_33
  exact List.forall_mem_cons.2 ⟨sub8_1056, List.forall_mem_cons.2 ⟨sub8_1057, List.forall_mem_cons.2 ⟨sub8_1058, List.forall_mem_cons.2 ⟨sub8_1059, List.forall_mem_cons.2 ⟨sub8_1060, List.forall_mem_cons.2 ⟨sub8_1061, List.forall_mem_cons.2 ⟨sub8_1062, List.forall_mem_cons.2 ⟨sub8_1063, List.forall_mem_cons.2 ⟨sub8_1064, List.forall_mem_cons.2 ⟨sub8_1065, List.forall_mem_cons.2 ⟨sub8_1066, List.forall_mem_cons.2 ⟨sub8_1067, List.forall_mem_cons.2 ⟨sub8_1068, List.forall_mem_cons.2 ⟨sub8_1069, List.forall_mem_cons.2 ⟨sub8_1070, List.forall_mem_cons.2 ⟨sub8_1071, List.forall_mem_cons.2 ⟨sub8_1072, List.forall_mem_cons.2 ⟨sub8_1073, List.forall_mem_cons.2 ⟨sub8_1074, List.forall_mem_cons.2 ⟨sub8_1075, List.forall_mem_cons.2 ⟨sub8_1076, List.forall_mem_cons.2 ⟨sub8_1077, List.forall_mem_cons.2 ⟨sub8_1078, List.forall_mem_cons.2 ⟨sub8_1079, List.forall_mem_cons.2 ⟨sub8_1080, List.forall_mem_cons.2 ⟨sub8_1081, List.forall_mem_cons.2 ⟨sub8_1082, List.forall_mem_cons.2 ⟨sub8_1083, List.forall_mem_cons.2 ⟨sub8_1084, List.forall_mem_cons.2 ⟨sub8_1085, List.forall_mem_cons.2 ⟨sub8_1086, List.forall_mem_cons.2 ⟨sub8_1087, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_1088 : sub8 [3, 2, 1] = true := by decide +kernel
theorem sub8_1089 : sub8 [3, 2, 2] = true := by decide +kernel
theorem sub8_1090 : sub8 [3, 2, 3] = true := by decide +kernel
theorem sub8_1091 : sub8 [3, 2, 4] = true := by decide +kernel
theorem sub8_1092 : sub8 [3, 2, 5] = true := by decide +kernel
theorem sub8_1093 : sub8 [3, 2, 6] = true := by decide +kernel
theorem sub8_1094 : sub8 [3, 2, 7] = true := by decide +kernel
theorem sub8_1095 : sub8 [3, 3] = true := by decide +kernel
theorem sub8_1096 : sub8 [4, -4] = true := by decide +kernel
theorem sub8_1097 : sub8 [4, -3] = true := by decide +kernel
theorem sub8_1098 : sub8 [4, -2] = true := by decide +kernel
theorem sub8_1099 : sub8 [4, -1, -7] = true := by decide +kernel
theorem sub8_1100 : sub8 [4, -1, -6] = true := by decide +kernel
theorem sub8_1101 : sub8 [4, -1, -5] = true := by decide +kernel
theorem sub8_1102 : sub8 [4, -1, -4] = true := by decide +kernel
theorem sub8_1103 : sub8 [4, -1, -3] = true := by decide +kernel
theorem sub8_1104 : sub8 [4, -1, -2] = true := by decide +kernel
theorem sub8_1105 : sub8 [4, -1, -1] = true := by decide +kernel
theorem sub8_1106 : sub8 [4, -1, 0] = true := by decide +kernel
theorem sub8_1107 : sub8 [4, -1, 1] = true := by decide +kernel
theorem sub8_1108 : sub8 [4, -1, 2] = true := by decide +kernel
theorem sub8_1109 : sub8 [4, -1, 3] = true := by decide +kernel
theorem sub8_1110 : sub8 [4, -1, 4] = true := by decide +kernel
theorem sub8_1111 : sub8 [4, -1, 5] = true := by decide +kernel
theorem sub8_1112 : sub8 [4, -1, 6] = true := by decide +kernel
theorem sub8_1113 : sub8 [4, 0, -7] = true := by decide +kernel
theorem sub8_1114 : sub8 [4, 0, -6] = true := by decide +kernel
theorem sub8_1115 : sub8 [4, 0, -5] = true := by decide +kernel
theorem sub8_1116 : sub8 [4, 0, -4] = true := by decide +kernel
theorem sub8_1117 : sub8 [4, 0, -3] = true := by decide +kernel
theorem sub8_1118 : sub8 [4, 0, -2] = true := by decide +kernel
theorem sub8_1119 : sub8 [4, 0, -1] = true := by decide +kernel
theorem sb8_34 : ∀ q ∈ blk8_34, sub8 q = true := by
  unfold blk8_34
  exact List.forall_mem_cons.2 ⟨sub8_1088, List.forall_mem_cons.2 ⟨sub8_1089, List.forall_mem_cons.2 ⟨sub8_1090, List.forall_mem_cons.2 ⟨sub8_1091, List.forall_mem_cons.2 ⟨sub8_1092, List.forall_mem_cons.2 ⟨sub8_1093, List.forall_mem_cons.2 ⟨sub8_1094, List.forall_mem_cons.2 ⟨sub8_1095, List.forall_mem_cons.2 ⟨sub8_1096, List.forall_mem_cons.2 ⟨sub8_1097, List.forall_mem_cons.2 ⟨sub8_1098, List.forall_mem_cons.2 ⟨sub8_1099, List.forall_mem_cons.2 ⟨sub8_1100, List.forall_mem_cons.2 ⟨sub8_1101, List.forall_mem_cons.2 ⟨sub8_1102, List.forall_mem_cons.2 ⟨sub8_1103, List.forall_mem_cons.2 ⟨sub8_1104, List.forall_mem_cons.2 ⟨sub8_1105, List.forall_mem_cons.2 ⟨sub8_1106, List.forall_mem_cons.2 ⟨sub8_1107, List.forall_mem_cons.2 ⟨sub8_1108, List.forall_mem_cons.2 ⟨sub8_1109, List.forall_mem_cons.2 ⟨sub8_1110, List.forall_mem_cons.2 ⟨sub8_1111, List.forall_mem_cons.2 ⟨sub8_1112, List.forall_mem_cons.2 ⟨sub8_1113, List.forall_mem_cons.2 ⟨sub8_1114, List.forall_mem_cons.2 ⟨sub8_1115, List.forall_mem_cons.2 ⟨sub8_1116, List.forall_mem_cons.2 ⟨sub8_1117, List.forall_mem_cons.2 ⟨sub8_1118, List.forall_mem_cons.2 ⟨sub8_1119, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_1120 : sub8 [4, 0, 0] = true := by decide +kernel
theorem sub8_1121 : sub8 [4, 0, 1] = true := by decide +kernel
theorem sub8_1122 : sub8 [4, 0, 2] = true := by decide +kernel
theorem sub8_1123 : sub8 [4, 0, 3] = true := by decide +kernel
theorem sub8_1124 : sub8 [4, 0, 4] = true := by decide +kernel
theorem sub8_1125 : sub8 [4, 0, 5] = true := by decide +kernel
theorem sub8_1126 : sub8 [4, 0, 6] = true := by decide +kernel
theorem sub8_1127 : sub8 [4, 1] = true := by decide +kernel
theorem sub8_1128 : sub8 [4, 2] = true := by decide +kernel
theorem sb8_35 : ∀ q ∈ blk8_35, sub8 q = true := by
  unfold blk8_35
  exact List.forall_mem_cons.2 ⟨sub8_1120, List.forall_mem_cons.2 ⟨sub8_1121, List.forall_mem_cons.2 ⟨sub8_1122, List.forall_mem_cons.2 ⟨sub8_1123, List.forall_mem_cons.2 ⟨sub8_1124, List.forall_mem_cons.2 ⟨sub8_1125, List.forall_mem_cons.2 ⟨sub8_1126, List.forall_mem_cons.2 ⟨sub8_1127, List.forall_mem_cons.2 ⟨sub8_1128, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_0 : sub9 [-6] = true := by decide +kernel
theorem sub9_1 : sub9 [-5, -5] = true := by decide +kernel
theorem sub9_2 : sub9 [-5, -4] = true := by decide +kernel
theorem sub9_3 : sub9 [-5, -3] = true := by decide +kernel
theorem sub9_4 : sub9 [-5, -2] = true := by decide +kernel
theorem sub9_5 : sub9 [-5, -1] = true := by decide +kernel
theorem sub9_6 : sub9 [-5, 0] = true := by decide +kernel
theorem sub9_7 : sub9 [-5, 1] = true := by decide +kernel
theorem sub9_8 : sub9 [-5, 2] = true := by decide +kernel
theorem sub9_9 : sub9 [-4, -6] = true := by decide +kernel
theorem sub9_10 : sub9 [-4, -5] = true := by decide +kernel
theorem sub9_11 : sub9 [-4, -4] = true := by decide +kernel
theorem sub9_12 : sub9 [-4, -3] = true := by decide +kernel
theorem sub9_13 : sub9 [-4, -2] = true := by decide +kernel
theorem sub9_14 : sub9 [-4, -1] = true := by decide +kernel
theorem sub9_15 : sub9 [-4, 0] = true := by decide +kernel
theorem sub9_16 : sub9 [-4, 1] = true := by decide +kernel
theorem sub9_17 : sub9 [-4, 2] = true := by decide +kernel
theorem sub9_18 : sub9 [-4, 3] = true := by decide +kernel
theorem sub9_19 : sub9 [-3, -6] = true := by decide +kernel
theorem sub9_20 : sub9 [-3, -5] = true := by decide +kernel
theorem sub9_21 : sub9 [-3, -4] = true := by decide +kernel
theorem sub9_22 : sub9 [-3, -3] = true := by decide +kernel
theorem sub9_23 : sub9 [-3, -2] = true := by decide +kernel
theorem sub9_24 : sub9 [-3, -1] = true := by decide +kernel
theorem sub9_25 : sub9 [-3, 0] = true := by decide +kernel
theorem sub9_26 : sub9 [-3, 1] = true := by decide +kernel
theorem sub9_27 : sub9 [-3, 2] = true := by decide +kernel
theorem sub9_28 : sub9 [-3, 3] = true := by decide +kernel
theorem sub9_29 : sub9 [-3, 4] = true := by decide +kernel
theorem sub9_30 : sub9 [-2, -6] = true := by decide +kernel
theorem sub9_31 : sub9 [-2, -5] = true := by decide +kernel
theorem sb9_0 : ∀ q ∈ blk9_0, sub9 q = true := by
  unfold blk9_0
  exact List.forall_mem_cons.2 ⟨sub9_0, List.forall_mem_cons.2 ⟨sub9_1, List.forall_mem_cons.2 ⟨sub9_2, List.forall_mem_cons.2 ⟨sub9_3, List.forall_mem_cons.2 ⟨sub9_4, List.forall_mem_cons.2 ⟨sub9_5, List.forall_mem_cons.2 ⟨sub9_6, List.forall_mem_cons.2 ⟨sub9_7, List.forall_mem_cons.2 ⟨sub9_8, List.forall_mem_cons.2 ⟨sub9_9, List.forall_mem_cons.2 ⟨sub9_10, List.forall_mem_cons.2 ⟨sub9_11, List.forall_mem_cons.2 ⟨sub9_12, List.forall_mem_cons.2 ⟨sub9_13, List.forall_mem_cons.2 ⟨sub9_14, List.forall_mem_cons.2 ⟨sub9_15, List.forall_mem_cons.2 ⟨sub9_16, List.forall_mem_cons.2 ⟨sub9_17, List.forall_mem_cons.2 ⟨sub9_18, List.forall_mem_cons.2 ⟨sub9_19, List.forall_mem_cons.2 ⟨sub9_20, List.forall_mem_cons.2 ⟨sub9_21, List.forall_mem_cons.2 ⟨sub9_22, List.forall_mem_cons.2 ⟨sub9_23, List.forall_mem_cons.2 ⟨sub9_24, List.forall_mem_cons.2 ⟨sub9_25, List.forall_mem_cons.2 ⟨sub9_26, List.forall_mem_cons.2 ⟨sub9_27, List.forall_mem_cons.2 ⟨sub9_28, List.forall_mem_cons.2 ⟨sub9_29, List.forall_mem_cons.2 ⟨sub9_30, List.forall_mem_cons.2 ⟨sub9_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_32 : sub9 [-2, -4] = true := by decide +kernel
theorem sub9_33 : sub9 [-2, -3] = true := by decide +kernel
theorem sub9_34 : sub9 [-2, -2] = true := by decide +kernel
theorem sub9_35 : sub9 [-2, -1, -8] = true := by decide +kernel
theorem sub9_36 : sub9 [-2, -1, -7] = true := by decide +kernel
theorem sub9_37 : sub9 [-2, -1, -6] = true := by decide +kernel
theorem sub9_38 : sub9 [-2, -1, -5] = true := by decide +kernel
theorem sub9_39 : sub9 [-2, -1, -4] = true := by decide +kernel
theorem sub9_40 : sub9 [-2, -1, -3] = true := by decide +kernel
theorem sub9_41 : sub9 [-2, -1, -2] = true := by decide +kernel
theorem sub9_42 : sub9 [-2, -1, -1] = true := by decide +kernel
theorem sub9_43 : sub9 [-2, -1, 0] = true := by decide +kernel
theorem sub9_44 : sub9 [-2, -1, 1] = true := by decide +kernel
theorem sub9_45 : sub9 [-2, -1, 2] = true := by decide +kernel
theorem sub9_46 : sub9 [-2, -1, 3] = true := by decide +kernel
theorem sub9_47 : sub9 [-2, -1, 4] = true := by decide +kernel
theorem sub9_48 : sub9 [-2, -1, 5] = true := by decide +kernel
theorem sub9_49 : sub9 [-2, 0, -8] = true := by decide +kernel
theorem sub9_50 : sub9 [-2, 0, -7] = true := by decide +kernel
theorem sub9_51 : sub9 [-2, 0, -6] = true := by decide +kernel
theorem sub9_52 : sub9 [-2, 0, -5] = true := by decide +kernel
theorem sub9_53 : sub9 [-2, 0, -4] = true := by decide +kernel
theorem sub9_54 : sub9 [-2, 0, -3] = true := by decide +kernel
theorem sub9_55 : sub9 [-2, 0, -2] = true := by decide +kernel
theorem sub9_56 : sub9 [-2, 0, -1] = true := by decide +kernel
theorem sub9_57 : sub9 [-2, 0, 0] = true := by decide +kernel
theorem sub9_58 : sub9 [-2, 0, 1] = true := by decide +kernel
theorem sub9_59 : sub9 [-2, 0, 2] = true := by decide +kernel
theorem sub9_60 : sub9 [-2, 0, 3] = true := by decide +kernel
theorem sub9_61 : sub9 [-2, 0, 4] = true := by decide +kernel
theorem sub9_62 : sub9 [-2, 0, 5] = true := by decide +kernel
theorem sub9_63 : sub9 [-2, 1] = true := by decide +kernel
theorem sb9_1 : ∀ q ∈ blk9_1, sub9 q = true := by
  unfold blk9_1
  exact List.forall_mem_cons.2 ⟨sub9_32, List.forall_mem_cons.2 ⟨sub9_33, List.forall_mem_cons.2 ⟨sub9_34, List.forall_mem_cons.2 ⟨sub9_35, List.forall_mem_cons.2 ⟨sub9_36, List.forall_mem_cons.2 ⟨sub9_37, List.forall_mem_cons.2 ⟨sub9_38, List.forall_mem_cons.2 ⟨sub9_39, List.forall_mem_cons.2 ⟨sub9_40, List.forall_mem_cons.2 ⟨sub9_41, List.forall_mem_cons.2 ⟨sub9_42, List.forall_mem_cons.2 ⟨sub9_43, List.forall_mem_cons.2 ⟨sub9_44, List.forall_mem_cons.2 ⟨sub9_45, List.forall_mem_cons.2 ⟨sub9_46, List.forall_mem_cons.2 ⟨sub9_47, List.forall_mem_cons.2 ⟨sub9_48, List.forall_mem_cons.2 ⟨sub9_49, List.forall_mem_cons.2 ⟨sub9_50, List.forall_mem_cons.2 ⟨sub9_51, List.forall_mem_cons.2 ⟨sub9_52, List.forall_mem_cons.2 ⟨sub9_53, List.forall_mem_cons.2 ⟨sub9_54, List.forall_mem_cons.2 ⟨sub9_55, List.forall_mem_cons.2 ⟨sub9_56, List.forall_mem_cons.2 ⟨sub9_57, List.forall_mem_cons.2 ⟨sub9_58, List.forall_mem_cons.2 ⟨sub9_59, List.forall_mem_cons.2 ⟨sub9_60, List.forall_mem_cons.2 ⟨sub9_61, List.forall_mem_cons.2 ⟨sub9_62, List.forall_mem_cons.2 ⟨sub9_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_64 : sub9 [-2, 2] = true := by decide +kernel
theorem sub9_65 : sub9 [-2, 3] = true := by decide +kernel
theorem sub9_66 : sub9 [-2, 4] = true := by decide +kernel
theorem sub9_67 : sub9 [-1, -6] = true := by decide +kernel
theorem sub9_68 : sub9 [-1, -5] = true := by decide +kernel
theorem sub9_69 : sub9 [-1, -4] = true := by decide +kernel
theorem sub9_70 : sub9 [-1, -3] = true := by decide +kernel
theorem sub9_71 : sub9 [-1, -2, -7] = true := by decide +kernel
theorem sub9_72 : sub9 [-1, -2, -6] = true := by decide +kernel
theorem sub9_73 : sub9 [-1, -2, -5] = true := by decide +kernel
theorem sub9_74 : sub9 [-1, -2, -4] = true := by decide +kernel
theorem sub9_75 : sub9 [-1, -2, -3] = true := by decide +kernel
theorem sub9_76 : sub9 [-1, -2, -2] = true := by decide +kernel
theorem sub9_77 : sub9 [-1, -2, -1] = true := by decide +kernel
theorem sub9_78 : sub9 [-1, -2, 0] = true := by decide +kernel
theorem sub9_79 : sub9 [-1, -2, 1] = true := by decide +kernel
theorem sub9_80 : sub9 [-1, -2, 2] = true := by decide +kernel
theorem sub9_81 : sub9 [-1, -2, 3] = true := by decide +kernel
theorem sub9_82 : sub9 [-1, -2, 4] = true := by decide +kernel
theorem sub9_83 : sub9 [-1, -2, 5] = true := by decide +kernel
theorem sub9_84 : sub9 [-1, -2, 6] = true := by decide +kernel
theorem sub9_85 : sub9 [-1, -1, -8] = true := by decide +kernel
theorem sub9_86 : sub9 [-1, -1, -7] = true := by decide +kernel
theorem sub9_87 : sub9 [-1, -1, -6] = true := by decide +kernel
theorem sub9_88 : sub9 [-1, -1, -5] = true := by decide +kernel
theorem sub9_89 : sub9 [-1, -1, -4] = true := by decide +kernel
theorem sub9_90 : sub9 [-1, -1, -3] = true := by decide +kernel
theorem sub9_91 : sub9 [-1, -1, -2] = true := by decide +kernel
theorem sub9_92 : sub9 [-1, -1, -1] = true := by decide +kernel
theorem sub9_93 : sub9 [-1, -1, 0] = true := by decide +kernel
theorem sub9_94 : sub9 [-1, -1, 1] = true := by decide +kernel
theorem sub9_95 : sub9 [-1, -1, 2] = true := by decide +kernel
theorem sb9_2 : ∀ q ∈ blk9_2, sub9 q = true := by
  unfold blk9_2
  exact List.forall_mem_cons.2 ⟨sub9_64, List.forall_mem_cons.2 ⟨sub9_65, List.forall_mem_cons.2 ⟨sub9_66, List.forall_mem_cons.2 ⟨sub9_67, List.forall_mem_cons.2 ⟨sub9_68, List.forall_mem_cons.2 ⟨sub9_69, List.forall_mem_cons.2 ⟨sub9_70, List.forall_mem_cons.2 ⟨sub9_71, List.forall_mem_cons.2 ⟨sub9_72, List.forall_mem_cons.2 ⟨sub9_73, List.forall_mem_cons.2 ⟨sub9_74, List.forall_mem_cons.2 ⟨sub9_75, List.forall_mem_cons.2 ⟨sub9_76, List.forall_mem_cons.2 ⟨sub9_77, List.forall_mem_cons.2 ⟨sub9_78, List.forall_mem_cons.2 ⟨sub9_79, List.forall_mem_cons.2 ⟨sub9_80, List.forall_mem_cons.2 ⟨sub9_81, List.forall_mem_cons.2 ⟨sub9_82, List.forall_mem_cons.2 ⟨sub9_83, List.forall_mem_cons.2 ⟨sub9_84, List.forall_mem_cons.2 ⟨sub9_85, List.forall_mem_cons.2 ⟨sub9_86, List.forall_mem_cons.2 ⟨sub9_87, List.forall_mem_cons.2 ⟨sub9_88, List.forall_mem_cons.2 ⟨sub9_89, List.forall_mem_cons.2 ⟨sub9_90, List.forall_mem_cons.2 ⟨sub9_91, List.forall_mem_cons.2 ⟨sub9_92, List.forall_mem_cons.2 ⟨sub9_93, List.forall_mem_cons.2 ⟨sub9_94, List.forall_mem_cons.2 ⟨sub9_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_96 : sub9 [-1, -1, 3] = true := by decide +kernel
theorem sub9_97 : sub9 [-1, -1, 4] = true := by decide +kernel
theorem sub9_98 : sub9 [-1, -1, 5] = true := by decide +kernel
theorem sub9_99 : sub9 [-1, -1, 6] = true := by decide +kernel
theorem sub9_100 : sub9 [-1, 0, -8] = true := by decide +kernel
theorem sub9_101 : sub9 [-1, 0, -7] = true := by decide +kernel
theorem sub9_102 : sub9 [-1, 0, -6] = true := by decide +kernel
theorem sub9_103 : sub9 [-1, 0, -5] = true := by decide +kernel
theorem sub9_104 : sub9 [-1, 0, -4] = true := by decide +kernel
theorem sub9_105 : sub9 [-1, 0, -3] = true := by decide +kernel
theorem sub9_106 : sub9 [-1, 0, -2] = true := by decide +kernel
theorem sub9_107 : sub9 [-1, 0, -1] = true := by decide +kernel
theorem sub9_108 : sub9 [-1, 0, 0] = true := by decide +kernel
theorem sub9_109 : sub9 [-1, 0, 1] = true := by decide +kernel
theorem sub9_110 : sub9 [-1, 0, 2] = true := by decide +kernel
theorem sub9_111 : sub9 [-1, 0, 3] = true := by decide +kernel
theorem sub9_112 : sub9 [-1, 0, 4] = true := by decide +kernel
theorem sub9_113 : sub9 [-1, 0, 5] = true := by decide +kernel
theorem sub9_114 : sub9 [-1, 0, 6] = true := by decide +kernel
theorem sub9_115 : sub9 [-1, 1, -8] = true := by decide +kernel
theorem sub9_116 : sub9 [-1, 1, -7] = true := by decide +kernel
theorem sub9_117 : sub9 [-1, 1, -6] = true := by decide +kernel
theorem sub9_118 : sub9 [-1, 1, -5] = true := by decide +kernel
theorem sub9_119 : sub9 [-1, 1, -4] = true := by decide +kernel
theorem sub9_120 : sub9 [-1, 1, -3] = true := by decide +kernel
theorem sub9_121 : sub9 [-1, 1, -2] = true := by decide +kernel
theorem sub9_122 : sub9 [-1, 1, -1] = true := by decide +kernel
theorem sub9_123 : sub9 [-1, 1, 0] = true := by decide +kernel
theorem sub9_124 : sub9 [-1, 1, 1] = true := by decide +kernel
theorem sub9_125 : sub9 [-1, 1, 2] = true := by decide +kernel
theorem sub9_126 : sub9 [-1, 1, 3] = true := by decide +kernel
theorem sub9_127 : sub9 [-1, 1, 4] = true := by decide +kernel
theorem sb9_3 : ∀ q ∈ blk9_3, sub9 q = true := by
  unfold blk9_3
  exact List.forall_mem_cons.2 ⟨sub9_96, List.forall_mem_cons.2 ⟨sub9_97, List.forall_mem_cons.2 ⟨sub9_98, List.forall_mem_cons.2 ⟨sub9_99, List.forall_mem_cons.2 ⟨sub9_100, List.forall_mem_cons.2 ⟨sub9_101, List.forall_mem_cons.2 ⟨sub9_102, List.forall_mem_cons.2 ⟨sub9_103, List.forall_mem_cons.2 ⟨sub9_104, List.forall_mem_cons.2 ⟨sub9_105, List.forall_mem_cons.2 ⟨sub9_106, List.forall_mem_cons.2 ⟨sub9_107, List.forall_mem_cons.2 ⟨sub9_108, List.forall_mem_cons.2 ⟨sub9_109, List.forall_mem_cons.2 ⟨sub9_110, List.forall_mem_cons.2 ⟨sub9_111, List.forall_mem_cons.2 ⟨sub9_112, List.forall_mem_cons.2 ⟨sub9_113, List.forall_mem_cons.2 ⟨sub9_114, List.forall_mem_cons.2 ⟨sub9_115, List.forall_mem_cons.2 ⟨sub9_116, List.forall_mem_cons.2 ⟨sub9_117, List.forall_mem_cons.2 ⟨sub9_118, List.forall_mem_cons.2 ⟨sub9_119, List.forall_mem_cons.2 ⟨sub9_120, List.forall_mem_cons.2 ⟨sub9_121, List.forall_mem_cons.2 ⟨sub9_122, List.forall_mem_cons.2 ⟨sub9_123, List.forall_mem_cons.2 ⟨sub9_124, List.forall_mem_cons.2 ⟨sub9_125, List.forall_mem_cons.2 ⟨sub9_126, List.forall_mem_cons.2 ⟨sub9_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_128 : sub9 [-1, 1, 5] = true := by decide +kernel
theorem sub9_129 : sub9 [-1, 1, 6] = true := by decide +kernel
theorem sub9_130 : sub9 [-1, 2] = true := by decide +kernel
theorem sub9_131 : sub9 [-1, 3] = true := by decide +kernel
theorem sub9_132 : sub9 [-1, 4] = true := by decide +kernel
theorem sub9_133 : sub9 [-1, 5] = true := by decide +kernel
theorem sub9_134 : sub9 [0, -6] = true := by decide +kernel
theorem sub9_135 : sub9 [0, -5] = true := by decide +kernel
theorem sub9_136 : sub9 [0, -4] = true := by decide +kernel
theorem sub9_137 : sub9 [0, -3] = true := by decide +kernel
theorem sub9_138 : sub9 [0, -2, -7] = true := by decide +kernel
theorem sub9_139 : sub9 [0, -2, -6] = true := by decide +kernel
theorem sub9_140 : sub9 [0, -2, -5] = true := by decide +kernel
theorem sub9_141 : sub9 [0, -2, -4] = true := by decide +kernel
theorem sub9_142 : sub9 [0, -2, -3] = true := by decide +kernel
theorem sub9_143 : sub9 [0, -2, -2] = true := by decide +kernel
theorem sub9_144 : sub9 [0, -2, -1] = true := by decide +kernel
theorem sub9_145 : sub9 [0, -2, 0] = true := by decide +kernel
theorem sub9_146 : sub9 [0, -2, 1] = true := by decide +kernel
theorem sub9_147 : sub9 [0, -2, 2] = true := by decide +kernel
theorem sub9_148 : sub9 [0, -2, 3] = true := by decide +kernel
theorem sub9_149 : sub9 [0, -2, 4] = true := by decide +kernel
theorem sub9_150 : sub9 [0, -2, 5] = true := by decide +kernel
theorem sub9_151 : sub9 [0, -2, 6] = true := by decide +kernel
theorem sub9_152 : sub9 [0, -1, -7] = true := by decide +kernel
theorem sub9_153 : sub9 [0, -1, -6] = true := by decide +kernel
theorem sub9_154 : sub9 [0, -1, -5] = true := by decide +kernel
theorem sub9_155 : sub9 [0, -1, -4] = true := by decide +kernel
theorem sub9_156 : sub9 [0, -1, -3] = true := by decide +kernel
theorem sub9_157 : sub9 [0, -1, -2] = true := by decide +kernel
theorem sub9_158 : sub9 [0, -1, -1] = true := by decide +kernel
theorem sub9_159 : sub9 [0, -1, 0] = true := by decide +kernel
theorem sb9_4 : ∀ q ∈ blk9_4, sub9 q = true := by
  unfold blk9_4
  exact List.forall_mem_cons.2 ⟨sub9_128, List.forall_mem_cons.2 ⟨sub9_129, List.forall_mem_cons.2 ⟨sub9_130, List.forall_mem_cons.2 ⟨sub9_131, List.forall_mem_cons.2 ⟨sub9_132, List.forall_mem_cons.2 ⟨sub9_133, List.forall_mem_cons.2 ⟨sub9_134, List.forall_mem_cons.2 ⟨sub9_135, List.forall_mem_cons.2 ⟨sub9_136, List.forall_mem_cons.2 ⟨sub9_137, List.forall_mem_cons.2 ⟨sub9_138, List.forall_mem_cons.2 ⟨sub9_139, List.forall_mem_cons.2 ⟨sub9_140, List.forall_mem_cons.2 ⟨sub9_141, List.forall_mem_cons.2 ⟨sub9_142, List.forall_mem_cons.2 ⟨sub9_143, List.forall_mem_cons.2 ⟨sub9_144, List.forall_mem_cons.2 ⟨sub9_145, List.forall_mem_cons.2 ⟨sub9_146, List.forall_mem_cons.2 ⟨sub9_147, List.forall_mem_cons.2 ⟨sub9_148, List.forall_mem_cons.2 ⟨sub9_149, List.forall_mem_cons.2 ⟨sub9_150, List.forall_mem_cons.2 ⟨sub9_151, List.forall_mem_cons.2 ⟨sub9_152, List.forall_mem_cons.2 ⟨sub9_153, List.forall_mem_cons.2 ⟨sub9_154, List.forall_mem_cons.2 ⟨sub9_155, List.forall_mem_cons.2 ⟨sub9_156, List.forall_mem_cons.2 ⟨sub9_157, List.forall_mem_cons.2 ⟨sub9_158, List.forall_mem_cons.2 ⟨sub9_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_160 : sub9 [0, -1, 1] = true := by decide +kernel
theorem sub9_161 : sub9 [0, -1, 2] = true := by decide +kernel
theorem sub9_162 : sub9 [0, -1, 3] = true := by decide +kernel
theorem sub9_163 : sub9 [0, -1, 4] = true := by decide +kernel
theorem sub9_164 : sub9 [0, -1, 5] = true := by decide +kernel
theorem sub9_165 : sub9 [0, -1, 6] = true := by decide +kernel
theorem sub9_166 : sub9 [0, 0, -7] = true := by decide +kernel
theorem sub9_167 : sub9 [0, 0, -6] = true := by decide +kernel
theorem sub9_168 : sub9 [0, 0, -5] = true := by decide +kernel
theorem sub9_169 : sub9 [0, 0, -4] = true := by decide +kernel
theorem sub9_170 : sub9 [0, 0, -3] = true := by decide +kernel
theorem sub9_171 : sub9 [0, 0, -2] = true := by decide +kernel
theorem sub9_172 : sub9 [0, 0, -1] = true := by decide +kernel
theorem sub9_173 : sub9 [0, 0, 0] = true := by decide +kernel
theorem sub9_174 : sub9 [0, 0, 1] = true := by decide +kernel
theorem sub9_175 : sub9 [0, 0, 2] = true := by decide +kernel
theorem sub9_176 : sub9 [0, 0, 3] = true := by decide +kernel
theorem sub9_177 : sub9 [0, 0, 4] = true := by decide +kernel
theorem sub9_178 : sub9 [0, 0, 5] = true := by decide +kernel
theorem sub9_179 : sub9 [0, 0, 6] = true := by decide +kernel
theorem sub9_180 : sub9 [0, 1, -7] = true := by decide +kernel
theorem sub9_181 : sub9 [0, 1, -6] = true := by decide +kernel
theorem sub9_182 : sub9 [0, 1, -5] = true := by decide +kernel
theorem sub9_183 : sub9 [0, 1, -4] = true := by decide +kernel
theorem sub9_184 : sub9 [0, 1, -3] = true := by decide +kernel
theorem sub9_185 : sub9 [0, 1, -2] = true := by decide +kernel
theorem sub9_186 : sub9 [0, 1, -1] = true := by decide +kernel
theorem sub9_187 : sub9 [0, 1, 0] = true := by decide +kernel
theorem sub9_188 : sub9 [0, 1, 1] = true := by decide +kernel
theorem sub9_189 : sub9 [0, 1, 2] = true := by decide +kernel
theorem sub9_190 : sub9 [0, 1, 3] = true := by decide +kernel
theorem sub9_191 : sub9 [0, 1, 4] = true := by decide +kernel
theorem sb9_5 : ∀ q ∈ blk9_5, sub9 q = true := by
  unfold blk9_5
  exact List.forall_mem_cons.2 ⟨sub9_160, List.forall_mem_cons.2 ⟨sub9_161, List.forall_mem_cons.2 ⟨sub9_162, List.forall_mem_cons.2 ⟨sub9_163, List.forall_mem_cons.2 ⟨sub9_164, List.forall_mem_cons.2 ⟨sub9_165, List.forall_mem_cons.2 ⟨sub9_166, List.forall_mem_cons.2 ⟨sub9_167, List.forall_mem_cons.2 ⟨sub9_168, List.forall_mem_cons.2 ⟨sub9_169, List.forall_mem_cons.2 ⟨sub9_170, List.forall_mem_cons.2 ⟨sub9_171, List.forall_mem_cons.2 ⟨sub9_172, List.forall_mem_cons.2 ⟨sub9_173, List.forall_mem_cons.2 ⟨sub9_174, List.forall_mem_cons.2 ⟨sub9_175, List.forall_mem_cons.2 ⟨sub9_176, List.forall_mem_cons.2 ⟨sub9_177, List.forall_mem_cons.2 ⟨sub9_178, List.forall_mem_cons.2 ⟨sub9_179, List.forall_mem_cons.2 ⟨sub9_180, List.forall_mem_cons.2 ⟨sub9_181, List.forall_mem_cons.2 ⟨sub9_182, List.forall_mem_cons.2 ⟨sub9_183, List.forall_mem_cons.2 ⟨sub9_184, List.forall_mem_cons.2 ⟨sub9_185, List.forall_mem_cons.2 ⟨sub9_186, List.forall_mem_cons.2 ⟨sub9_187, List.forall_mem_cons.2 ⟨sub9_188, List.forall_mem_cons.2 ⟨sub9_189, List.forall_mem_cons.2 ⟨sub9_190, List.forall_mem_cons.2 ⟨sub9_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_192 : sub9 [0, 1, 5] = true := by decide +kernel
theorem sub9_193 : sub9 [0, 1, 6] = true := by decide +kernel
theorem sub9_194 : sub9 [0, 2, -7] = true := by decide +kernel
theorem sub9_195 : sub9 [0, 2, -6] = true := by decide +kernel
theorem sub9_196 : sub9 [0, 2, -5] = true := by decide +kernel
theorem sub9_197 : sub9 [0, 2, -4] = true := by decide +kernel
theorem sub9_198 : sub9 [0, 2, -3] = true := by decide +kernel
theorem sub9_199 : sub9 [0, 2, -2] = true := by decide +kernel
theorem sub9_200 : sub9 [0, 2, -1] = true := by decide +kernel
theorem sub9_201 : sub9 [0, 2, 0] = true := by decide +kernel
theorem sub9_202 : sub9 [0, 2, 1] = true := by decide +kernel
theorem sub9_203 : sub9 [0, 2, 2] = true := by decide +kernel
theorem sub9_204 : sub9 [0, 2, 3] = true := by decide +kernel
theorem sub9_205 : sub9 [0, 2, 4] = true := by decide +kernel
theorem sub9_206 : sub9 [0, 2, 5] = true := by decide +kernel
theorem sub9_207 : sub9 [0, 2, 6] = true := by decide +kernel
theorem sub9_208 : sub9 [0, 3] = true := by decide +kernel
theorem sub9_209 : sub9 [0, 4] = true := by decide +kernel
theorem sub9_210 : sub9 [0, 5] = true := by decide +kernel
theorem sub9_211 : sub9 [1, -6] = true := by decide +kernel
theorem sub9_212 : sub9 [1, -5] = true := by decide +kernel
theorem sub9_213 : sub9 [1, -4] = true := by decide +kernel
theorem sub9_214 : sub9 [1, -3] = true := by decide +kernel
theorem sub9_215 : sub9 [1, -2] = true := by decide +kernel
theorem sub9_216 : sub9 [1, -1, -7] = true := by decide +kernel
theorem sub9_217 : sub9 [1, -1, -6] = true := by decide +kernel
theorem sub9_218 : sub9 [1, -1, -5] = true := by decide +kernel
theorem sub9_219 : sub9 [1, -1, -4] = true := by decide +kernel
theorem sub9_220 : sub9 [1, -1, -3] = true := by decide +kernel
theorem sub9_221 : sub9 [1, -1, -2] = true := by decide +kernel
theorem sub9_222 : sub9 [1, -1, -1] = true := by decide +kernel
theorem sub9_223 : sub9 [1, -1, 0] = true := by decide +kernel
theorem sb9_6 : ∀ q ∈ blk9_6, sub9 q = true := by
  unfold blk9_6
  exact List.forall_mem_cons.2 ⟨sub9_192, List.forall_mem_cons.2 ⟨sub9_193, List.forall_mem_cons.2 ⟨sub9_194, List.forall_mem_cons.2 ⟨sub9_195, List.forall_mem_cons.2 ⟨sub9_196, List.forall_mem_cons.2 ⟨sub9_197, List.forall_mem_cons.2 ⟨sub9_198, List.forall_mem_cons.2 ⟨sub9_199, List.forall_mem_cons.2 ⟨sub9_200, List.forall_mem_cons.2 ⟨sub9_201, List.forall_mem_cons.2 ⟨sub9_202, List.forall_mem_cons.2 ⟨sub9_203, List.forall_mem_cons.2 ⟨sub9_204, List.forall_mem_cons.2 ⟨sub9_205, List.forall_mem_cons.2 ⟨sub9_206, List.forall_mem_cons.2 ⟨sub9_207, List.forall_mem_cons.2 ⟨sub9_208, List.forall_mem_cons.2 ⟨sub9_209, List.forall_mem_cons.2 ⟨sub9_210, List.forall_mem_cons.2 ⟨sub9_211, List.forall_mem_cons.2 ⟨sub9_212, List.forall_mem_cons.2 ⟨sub9_213, List.forall_mem_cons.2 ⟨sub9_214, List.forall_mem_cons.2 ⟨sub9_215, List.forall_mem_cons.2 ⟨sub9_216, List.forall_mem_cons.2 ⟨sub9_217, List.forall_mem_cons.2 ⟨sub9_218, List.forall_mem_cons.2 ⟨sub9_219, List.forall_mem_cons.2 ⟨sub9_220, List.forall_mem_cons.2 ⟨sub9_221, List.forall_mem_cons.2 ⟨sub9_222, List.forall_mem_cons.2 ⟨sub9_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C120
