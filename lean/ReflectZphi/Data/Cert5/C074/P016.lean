import ReflectZphi.Data.Cert5.C074.Base

namespace ReflectZphi.Data.Cert5.C074
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub10_992 : sub10 [0, 6, -4] = true := by decide +kernel
theorem sub10_993 : sub10 [0, 6, -3] = true := by decide +kernel
theorem sub10_994 : sub10 [0, 6, -2] = true := by decide +kernel
theorem sub10_995 : sub10 [0, 6, -1] = true := by decide +kernel
theorem sub10_996 : sub10 [0, 6, 0] = true := by decide +kernel
theorem sub10_997 : sub10 [0, 6, 1] = true := by decide +kernel
theorem sub10_998 : sub10 [0, 6, 2] = true := by decide +kernel
theorem sub10_999 : sub10 [0, 6, 3] = true := by decide +kernel
theorem sub10_1000 : sub10 [0, 6, 4] = true := by decide +kernel
theorem sub10_1001 : sub10 [0, 7] = true := by decide +kernel
theorem sub10_1002 : sub10 [0, 8] = true := by decide +kernel
theorem sub10_1003 : sub10 [1, -9] = true := by decide +kernel
theorem sub10_1004 : sub10 [1, -8] = true := by decide +kernel
theorem sub10_1005 : sub10 [1, -7] = true := by decide +kernel
theorem sub10_1006 : sub10 [1, -6, -5] = true := by decide +kernel
theorem sub10_1007 : sub10 [1, -6, -4] = true := by decide +kernel
theorem sub10_1008 : sub10 [1, -6, -3] = true := by decide +kernel
theorem sub10_1009 : sub10 [1, -6, -2] = true := by decide +kernel
theorem sub10_1010 : sub10 [1, -6, -1] = true := by decide +kernel
theorem sub10_1011 : sub10 [1, -6, 0] = true := by decide +kernel
theorem sub10_1012 : sub10 [1, -6, 1] = true := by decide +kernel
theorem sub10_1013 : sub10 [1, -6, 2] = true := by decide +kernel
theorem sub10_1014 : sub10 [1, -6, 3] = true := by decide +kernel
theorem sub10_1015 : sub10 [1, -6, 4] = true := by decide +kernel
theorem sub10_1016 : sub10 [1, -6, 5] = true := by decide +kernel
theorem sub10_1017 : sub10 [1, -6, 6] = true := by decide +kernel
theorem sub10_1018 : sub10 [1, -6, 7] = true := by decide +kernel
theorem sub10_1019 : sub10 [1, -6, 8] = true := by decide +kernel
theorem sub10_1020 : sub10 [1, -5, -6] = true := by decide +kernel
theorem sub10_1021 : sub10 [1, -5, -5] = true := by decide +kernel
theorem sub10_1022 : sub10 [1, -5, -4] = true := by decide +kernel
theorem sub10_1023 : sub10 [1, -5, -3] = true := by decide +kernel
theorem sb10_31 : ∀ q ∈ blk10_31, sub10 q = true := by
  unfold blk10_31
  exact List.forall_mem_cons.2 ⟨sub10_992, List.forall_mem_cons.2 ⟨sub10_993, List.forall_mem_cons.2 ⟨sub10_994, List.forall_mem_cons.2 ⟨sub10_995, List.forall_mem_cons.2 ⟨sub10_996, List.forall_mem_cons.2 ⟨sub10_997, List.forall_mem_cons.2 ⟨sub10_998, List.forall_mem_cons.2 ⟨sub10_999, List.forall_mem_cons.2 ⟨sub10_1000, List.forall_mem_cons.2 ⟨sub10_1001, List.forall_mem_cons.2 ⟨sub10_1002, List.forall_mem_cons.2 ⟨sub10_1003, List.forall_mem_cons.2 ⟨sub10_1004, List.forall_mem_cons.2 ⟨sub10_1005, List.forall_mem_cons.2 ⟨sub10_1006, List.forall_mem_cons.2 ⟨sub10_1007, List.forall_mem_cons.2 ⟨sub10_1008, List.forall_mem_cons.2 ⟨sub10_1009, List.forall_mem_cons.2 ⟨sub10_1010, List.forall_mem_cons.2 ⟨sub10_1011, List.forall_mem_cons.2 ⟨sub10_1012, List.forall_mem_cons.2 ⟨sub10_1013, List.forall_mem_cons.2 ⟨sub10_1014, List.forall_mem_cons.2 ⟨sub10_1015, List.forall_mem_cons.2 ⟨sub10_1016, List.forall_mem_cons.2 ⟨sub10_1017, List.forall_mem_cons.2 ⟨sub10_1018, List.forall_mem_cons.2 ⟨sub10_1019, List.forall_mem_cons.2 ⟨sub10_1020, List.forall_mem_cons.2 ⟨sub10_1021, List.forall_mem_cons.2 ⟨sub10_1022, List.forall_mem_cons.2 ⟨sub10_1023, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_1024 : sub10 [1, -5, -2] = true := by decide +kernel
theorem sub10_1025 : sub10 [1, -5, -1] = true := by decide +kernel
theorem sub10_1026 : sub10 [1, -5, 0] = true := by decide +kernel
theorem sub10_1027 : sub10 [1, -5, 1] = true := by decide +kernel
theorem sub10_1028 : sub10 [1, -5, 2] = true := by decide +kernel
theorem sub10_1029 : sub10 [1, -5, 3] = true := by decide +kernel
theorem sub10_1030 : sub10 [1, -5, 4] = true := by decide +kernel
theorem sub10_1031 : sub10 [1, -5, 5] = true := by decide +kernel
theorem sub10_1032 : sub10 [1, -5, 6] = true := by decide +kernel
theorem sub10_1033 : sub10 [1, -5, 7] = true := by decide +kernel
theorem sub10_1034 : sub10 [1, -5, 8] = true := by decide +kernel
theorem sub10_1035 : sub10 [1, -4, -7] = true := by decide +kernel
theorem sub10_1036 : sub10 [1, -4, -6] = true := by decide +kernel
theorem sub10_1037 : sub10 [1, -4, -5] = true := by decide +kernel
theorem sub10_1038 : sub10 [1, -4, -4] = true := by decide +kernel
theorem sub10_1039 : sub10 [1, -4, -3] = true := by decide +kernel
theorem sub10_1040 : sub10 [1, -4, -2] = true := by decide +kernel
theorem sub10_1041 : sub10 [1, -4, -1] = true := by decide +kernel
theorem sub10_1042 : sub10 [1, -4, 0] = true := by decide +kernel
theorem sub10_1043 : sub10 [1, -4, 1] = true := by decide +kernel
theorem sub10_1044 : sub10 [1, -4, 2] = true := by decide +kernel
theorem sub10_1045 : sub10 [1, -4, 3] = true := by decide +kernel
theorem sub10_1046 : sub10 [1, -4, 4] = true := by decide +kernel
theorem sub10_1047 : sub10 [1, -4, 5] = true := by decide +kernel
theorem sub10_1048 : sub10 [1, -4, 6] = true := by decide +kernel
theorem sub10_1049 : sub10 [1, -4, 7] = true := by decide +kernel
theorem sub10_1050 : sub10 [1, -4, 8] = true := by decide +kernel
theorem sub10_1051 : sub10 [1, -4, 9] = true := by decide +kernel
theorem sub10_1052 : sub10 [1, -3, -8] = true := by decide +kernel
theorem sub10_1053 : sub10 [1, -3, -7] = true := by decide +kernel
theorem sub10_1054 : sub10 [1, -3, -6] = true := by decide +kernel
theorem sub10_1055 : sub10 [1, -3, -5] = true := by decide +kernel
theorem sb10_32 : ∀ q ∈ blk10_32, sub10 q = true := by
  unfold blk10_32
  exact List.forall_mem_cons.2 ⟨sub10_1024, List.forall_mem_cons.2 ⟨sub10_1025, List.forall_mem_cons.2 ⟨sub10_1026, List.forall_mem_cons.2 ⟨sub10_1027, List.forall_mem_cons.2 ⟨sub10_1028, List.forall_mem_cons.2 ⟨sub10_1029, List.forall_mem_cons.2 ⟨sub10_1030, List.forall_mem_cons.2 ⟨sub10_1031, List.forall_mem_cons.2 ⟨sub10_1032, List.forall_mem_cons.2 ⟨sub10_1033, List.forall_mem_cons.2 ⟨sub10_1034, List.forall_mem_cons.2 ⟨sub10_1035, List.forall_mem_cons.2 ⟨sub10_1036, List.forall_mem_cons.2 ⟨sub10_1037, List.forall_mem_cons.2 ⟨sub10_1038, List.forall_mem_cons.2 ⟨sub10_1039, List.forall_mem_cons.2 ⟨sub10_1040, List.forall_mem_cons.2 ⟨sub10_1041, List.forall_mem_cons.2 ⟨sub10_1042, List.forall_mem_cons.2 ⟨sub10_1043, List.forall_mem_cons.2 ⟨sub10_1044, List.forall_mem_cons.2 ⟨sub10_1045, List.forall_mem_cons.2 ⟨sub10_1046, List.forall_mem_cons.2 ⟨sub10_1047, List.forall_mem_cons.2 ⟨sub10_1048, List.forall_mem_cons.2 ⟨sub10_1049, List.forall_mem_cons.2 ⟨sub10_1050, List.forall_mem_cons.2 ⟨sub10_1051, List.forall_mem_cons.2 ⟨sub10_1052, List.forall_mem_cons.2 ⟨sub10_1053, List.forall_mem_cons.2 ⟨sub10_1054, List.forall_mem_cons.2 ⟨sub10_1055, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_1056 : sub10 [1, -3, -4] = true := by decide +kernel
theorem sub10_1057 : sub10 [1, -3, -3] = true := by decide +kernel
theorem sub10_1058 : sub10 [1, -3, -2] = true := by decide +kernel
theorem sub10_1059 : sub10 [1, -3, -1] = true := by decide +kernel
theorem sub10_1060 : sub10 [1, -3, 0] = true := by decide +kernel
theorem sub10_1061 : sub10 [1, -3, 1] = true := by decide +kernel
theorem sub10_1062 : sub10 [1, -3, 2] = true := by decide +kernel
theorem sub10_1063 : sub10 [1, -3, 3] = true := by decide +kernel
theorem sub10_1064 : sub10 [1, -3, 4] = true := by decide +kernel
theorem sub10_1065 : sub10 [1, -3, 5] = true := by decide +kernel
theorem sub10_1066 : sub10 [1, -3, 6] = true := by decide +kernel
theorem sub10_1067 : sub10 [1, -3, 7] = true := by decide +kernel
theorem sub10_1068 : sub10 [1, -3, 8] = true := by decide +kernel
theorem sub10_1069 : sub10 [1, -3, 9] = true := by decide +kernel
theorem sub10_1070 : sub10 [1, -2, -8] = true := by decide +kernel
theorem sub10_1071 : sub10 [1, -2, -7] = true := by decide +kernel
theorem sub10_1072 : sub10 [1, -2, -6] = true := by decide +kernel
theorem sub10_1073 : sub10 [1, -2, -5] = true := by decide +kernel
theorem sub10_1074 : sub10 [1, -2, -4] = true := by decide +kernel
theorem sub10_1075 : sub10 [1, -2, -3] = true := by decide +kernel
theorem sub10_1076 : sub10 [1, -2, -2] = true := by decide +kernel
theorem sub10_1077 : sub10 [1, -2, -1] = true := by decide +kernel
theorem sub10_1078 : sub10 [1, -2, 0] = true := by decide +kernel
theorem sub10_1079 : sub10 [1, -2, 1] = true := by decide +kernel
theorem sub10_1080 : sub10 [1, -2, 2] = true := by decide +kernel
theorem sub10_1081 : sub10 [1, -2, 3] = true := by decide +kernel
theorem sub10_1082 : sub10 [1, -2, 4] = true := by decide +kernel
theorem sub10_1083 : sub10 [1, -2, 5] = true := by decide +kernel
theorem sub10_1084 : sub10 [1, -2, 6] = true := by decide +kernel
theorem sub10_1085 : sub10 [1, -2, 7] = true := by decide +kernel
theorem sub10_1086 : sub10 [1, -2, 8] = true := by decide +kernel
theorem sub10_1087 : sub10 [1, -2, 9] = true := by decide +kernel
theorem sb10_33 : ∀ q ∈ blk10_33, sub10 q = true := by
  unfold blk10_33
  exact List.forall_mem_cons.2 ⟨sub10_1056, List.forall_mem_cons.2 ⟨sub10_1057, List.forall_mem_cons.2 ⟨sub10_1058, List.forall_mem_cons.2 ⟨sub10_1059, List.forall_mem_cons.2 ⟨sub10_1060, List.forall_mem_cons.2 ⟨sub10_1061, List.forall_mem_cons.2 ⟨sub10_1062, List.forall_mem_cons.2 ⟨sub10_1063, List.forall_mem_cons.2 ⟨sub10_1064, List.forall_mem_cons.2 ⟨sub10_1065, List.forall_mem_cons.2 ⟨sub10_1066, List.forall_mem_cons.2 ⟨sub10_1067, List.forall_mem_cons.2 ⟨sub10_1068, List.forall_mem_cons.2 ⟨sub10_1069, List.forall_mem_cons.2 ⟨sub10_1070, List.forall_mem_cons.2 ⟨sub10_1071, List.forall_mem_cons.2 ⟨sub10_1072, List.forall_mem_cons.2 ⟨sub10_1073, List.forall_mem_cons.2 ⟨sub10_1074, List.forall_mem_cons.2 ⟨sub10_1075, List.forall_mem_cons.2 ⟨sub10_1076, List.forall_mem_cons.2 ⟨sub10_1077, List.forall_mem_cons.2 ⟨sub10_1078, List.forall_mem_cons.2 ⟨sub10_1079, List.forall_mem_cons.2 ⟨sub10_1080, List.forall_mem_cons.2 ⟨sub10_1081, List.forall_mem_cons.2 ⟨sub10_1082, List.forall_mem_cons.2 ⟨sub10_1083, List.forall_mem_cons.2 ⟨sub10_1084, List.forall_mem_cons.2 ⟨sub10_1085, List.forall_mem_cons.2 ⟨sub10_1086, List.forall_mem_cons.2 ⟨sub10_1087, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_1088 : sub10 [1, -1, -9] = true := by decide +kernel
theorem sub10_1089 : sub10 [1, -1, -8] = true := by decide +kernel
theorem sub10_1090 : sub10 [1, -1, -7] = true := by decide +kernel
theorem sub10_1091 : sub10 [1, -1, -6] = true := by decide +kernel
theorem sub10_1092 : sub10 [1, -1, -5] = true := by decide +kernel
theorem sub10_1093 : sub10 [1, -1, -4] = true := by decide +kernel
theorem sub10_1094 : sub10 [1, -1, -3] = true := by decide +kernel
theorem sub10_1095 : sub10 [1, -1, -2] = true := by decide +kernel
theorem sub10_1096 : sub10 [1, -1, -1] = true := by decide +kernel
theorem sub10_1097 : sub10 [1, -1, 0] = true := by decide +kernel
theorem sub10_1098 : sub10 [1, -1, 1] = true := by decide +kernel
theorem sub10_1099 : sub10 [1, -1, 2] = true := by decide +kernel
theorem sub10_1100 : sub10 [1, -1, 3] = true := by decide +kernel
theorem sub10_1101 : sub10 [1, -1, 4] = true := by decide +kernel
theorem sub10_1102 : sub10 [1, -1, 5] = true := by decide +kernel
theorem sub10_1103 : sub10 [1, -1, 6] = true := by decide +kernel
theorem sub10_1104 : sub10 [1, -1, 7] = true := by decide +kernel
theorem sub10_1105 : sub10 [1, -1, 8] = true := by decide +kernel
theorem sub10_1106 : sub10 [1, -1, 9] = true := by decide +kernel
theorem sub10_1107 : sub10 [1, 0, -9] = true := by decide +kernel
theorem sub10_1108 : sub10 [1, 0, -8] = true := by decide +kernel
theorem sub10_1109 : sub10 [1, 0, -7] = true := by decide +kernel
theorem sub10_1110 : sub10 [1, 0, -6] = true := by decide +kernel
theorem sub10_1111 : sub10 [1, 0, -5] = true := by decide +kernel
theorem sub10_1112 : sub10 [1, 0, -4] = true := by decide +kernel
theorem sub10_1113 : sub10 [1, 0, -3] = true := by decide +kernel
theorem sub10_1114 : sub10 [1, 0, -2] = true := by decide +kernel
theorem sub10_1115 : sub10 [1, 0, -1] = true := by decide +kernel
theorem sub10_1116 : sub10 [1, 0, 0] = true := by decide +kernel
theorem sub10_1117 : sub10 [1, 0, 1] = true := by decide +kernel
theorem sub10_1118 : sub10 [1, 0, 2] = true := by decide +kernel
theorem sub10_1119 : sub10 [1, 0, 3] = true := by decide +kernel
theorem sb10_34 : ∀ q ∈ blk10_34, sub10 q = true := by
  unfold blk10_34
  exact List.forall_mem_cons.2 ⟨sub10_1088, List.forall_mem_cons.2 ⟨sub10_1089, List.forall_mem_cons.2 ⟨sub10_1090, List.forall_mem_cons.2 ⟨sub10_1091, List.forall_mem_cons.2 ⟨sub10_1092, List.forall_mem_cons.2 ⟨sub10_1093, List.forall_mem_cons.2 ⟨sub10_1094, List.forall_mem_cons.2 ⟨sub10_1095, List.forall_mem_cons.2 ⟨sub10_1096, List.forall_mem_cons.2 ⟨sub10_1097, List.forall_mem_cons.2 ⟨sub10_1098, List.forall_mem_cons.2 ⟨sub10_1099, List.forall_mem_cons.2 ⟨sub10_1100, List.forall_mem_cons.2 ⟨sub10_1101, List.forall_mem_cons.2 ⟨sub10_1102, List.forall_mem_cons.2 ⟨sub10_1103, List.forall_mem_cons.2 ⟨sub10_1104, List.forall_mem_cons.2 ⟨sub10_1105, List.forall_mem_cons.2 ⟨sub10_1106, List.forall_mem_cons.2 ⟨sub10_1107, List.forall_mem_cons.2 ⟨sub10_1108, List.forall_mem_cons.2 ⟨sub10_1109, List.forall_mem_cons.2 ⟨sub10_1110, List.forall_mem_cons.2 ⟨sub10_1111, List.forall_mem_cons.2 ⟨sub10_1112, List.forall_mem_cons.2 ⟨sub10_1113, List.forall_mem_cons.2 ⟨sub10_1114, List.forall_mem_cons.2 ⟨sub10_1115, List.forall_mem_cons.2 ⟨sub10_1116, List.forall_mem_cons.2 ⟨sub10_1117, List.forall_mem_cons.2 ⟨sub10_1118, List.forall_mem_cons.2 ⟨sub10_1119, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_1120 : sub10 [1, 0, 4] = true := by decide +kernel
theorem sub10_1121 : sub10 [1, 0, 5] = true := by decide +kernel
theorem sub10_1122 : sub10 [1, 0, 6] = true := by decide +kernel
theorem sub10_1123 : sub10 [1, 0, 7] = true := by decide +kernel
theorem sub10_1124 : sub10 [1, 0, 8] = true := by decide +kernel
theorem sub10_1125 : sub10 [1, 0, 9] = true := by decide +kernel
theorem sub10_1126 : sub10 [1, 1, -9] = true := by decide +kernel
theorem sub10_1127 : sub10 [1, 1, -8] = true := by decide +kernel
theorem sub10_1128 : sub10 [1, 1, -7] = true := by decide +kernel
theorem sub10_1129 : sub10 [1, 1, -6] = true := by decide +kernel
theorem sub10_1130 : sub10 [1, 1, -5] = true := by decide +kernel
theorem sub10_1131 : sub10 [1, 1, -4] = true := by decide +kernel
theorem sub10_1132 : sub10 [1, 1, -3] = true := by decide +kernel
theorem sub10_1133 : sub10 [1, 1, -2] = true := by decide +kernel
theorem sub10_1134 : sub10 [1, 1, -1] = true := by decide +kernel
theorem sub10_1135 : sub10 [1, 1, 0] = true := by decide +kernel
theorem sub10_1136 : sub10 [1, 1, 1] = true := by decide +kernel
theorem sub10_1137 : sub10 [1, 1, 2] = true := by decide +kernel
theorem sub10_1138 : sub10 [1, 1, 3] = true := by decide +kernel
theorem sub10_1139 : sub10 [1, 1, 4] = true := by decide +kernel
theorem sub10_1140 : sub10 [1, 1, 5] = true := by decide +kernel
theorem sub10_1141 : sub10 [1, 1, 6] = true := by decide +kernel
theorem sub10_1142 : sub10 [1, 1, 7] = true := by decide +kernel
theorem sub10_1143 : sub10 [1, 1, 8] = true := by decide +kernel
theorem sub10_1144 : sub10 [1, 2, -9] = true := by decide +kernel
theorem sub10_1145 : sub10 [1, 2, -8] = true := by decide +kernel
theorem sub10_1146 : sub10 [1, 2, -7] = true := by decide +kernel
theorem sub10_1147 : sub10 [1, 2, -6] = true := by decide +kernel
theorem sub10_1148 : sub10 [1, 2, -5] = true := by decide +kernel
theorem sub10_1149 : sub10 [1, 2, -4] = true := by decide +kernel
theorem sub10_1150 : sub10 [1, 2, -3] = true := by decide +kernel
theorem sub10_1151 : sub10 [1, 2, -2] = true := by decide +kernel
theorem sb10_35 : ∀ q ∈ blk10_35, sub10 q = true := by
  unfold blk10_35
  exact List.forall_mem_cons.2 ⟨sub10_1120, List.forall_mem_cons.2 ⟨sub10_1121, List.forall_mem_cons.2 ⟨sub10_1122, List.forall_mem_cons.2 ⟨sub10_1123, List.forall_mem_cons.2 ⟨sub10_1124, List.forall_mem_cons.2 ⟨sub10_1125, List.forall_mem_cons.2 ⟨sub10_1126, List.forall_mem_cons.2 ⟨sub10_1127, List.forall_mem_cons.2 ⟨sub10_1128, List.forall_mem_cons.2 ⟨sub10_1129, List.forall_mem_cons.2 ⟨sub10_1130, List.forall_mem_cons.2 ⟨sub10_1131, List.forall_mem_cons.2 ⟨sub10_1132, List.forall_mem_cons.2 ⟨sub10_1133, List.forall_mem_cons.2 ⟨sub10_1134, List.forall_mem_cons.2 ⟨sub10_1135, List.forall_mem_cons.2 ⟨sub10_1136, List.forall_mem_cons.2 ⟨sub10_1137, List.forall_mem_cons.2 ⟨sub10_1138, List.forall_mem_cons.2 ⟨sub10_1139, List.forall_mem_cons.2 ⟨sub10_1140, List.forall_mem_cons.2 ⟨sub10_1141, List.forall_mem_cons.2 ⟨sub10_1142, List.forall_mem_cons.2 ⟨sub10_1143, List.forall_mem_cons.2 ⟨sub10_1144, List.forall_mem_cons.2 ⟨sub10_1145, List.forall_mem_cons.2 ⟨sub10_1146, List.forall_mem_cons.2 ⟨sub10_1147, List.forall_mem_cons.2 ⟨sub10_1148, List.forall_mem_cons.2 ⟨sub10_1149, List.forall_mem_cons.2 ⟨sub10_1150, List.forall_mem_cons.2 ⟨sub10_1151, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_1152 : sub10 [1, 2, -1] = true := by decide +kernel
theorem sub10_1153 : sub10 [1, 2, 0] = true := by decide +kernel
theorem sub10_1154 : sub10 [1, 2, 1] = true := by decide +kernel
theorem sub10_1155 : sub10 [1, 2, 2] = true := by decide +kernel
theorem sub10_1156 : sub10 [1, 2, 3] = true := by decide +kernel
theorem sub10_1157 : sub10 [1, 2, 4] = true := by decide +kernel
theorem sub10_1158 : sub10 [1, 2, 5] = true := by decide +kernel
theorem sub10_1159 : sub10 [1, 2, 6] = true := by decide +kernel
theorem sub10_1160 : sub10 [1, 2, 7] = true := by decide +kernel
theorem sub10_1161 : sub10 [1, 2, 8] = true := by decide +kernel
theorem sub10_1162 : sub10 [1, 3, -9] = true := by decide +kernel
theorem sub10_1163 : sub10 [1, 3, -8] = true := by decide +kernel
theorem sub10_1164 : sub10 [1, 3, -7] = true := by decide +kernel
theorem sub10_1165 : sub10 [1, 3, -6] = true := by decide +kernel
theorem sub10_1166 : sub10 [1, 3, -5] = true := by decide +kernel
theorem sub10_1167 : sub10 [1, 3, -4] = true := by decide +kernel
theorem sub10_1168 : sub10 [1, 3, -3] = true := by decide +kernel
theorem sub10_1169 : sub10 [1, 3, -2] = true := by decide +kernel
theorem sub10_1170 : sub10 [1, 3, -1] = true := by decide +kernel
theorem sub10_1171 : sub10 [1, 3, 0] = true := by decide +kernel
theorem sub10_1172 : sub10 [1, 3, 1] = true := by decide +kernel
theorem sub10_1173 : sub10 [1, 3, 2] = true := by decide +kernel
theorem sub10_1174 : sub10 [1, 3, 3] = true := by decide +kernel
theorem sub10_1175 : sub10 [1, 3, 4] = true := by decide +kernel
theorem sub10_1176 : sub10 [1, 3, 5] = true := by decide +kernel
theorem sub10_1177 : sub10 [1, 3, 6] = true := by decide +kernel
theorem sub10_1178 : sub10 [1, 3, 7] = true := by decide +kernel
theorem sub10_1179 : sub10 [1, 4, -9] = true := by decide +kernel
theorem sub10_1180 : sub10 [1, 4, -8] = true := by decide +kernel
theorem sub10_1181 : sub10 [1, 4, -7] = true := by decide +kernel
theorem sub10_1182 : sub10 [1, 4, -6] = true := by decide +kernel
theorem sub10_1183 : sub10 [1, 4, -5] = true := by decide +kernel
theorem sb10_36 : ∀ q ∈ blk10_36, sub10 q = true := by
  unfold blk10_36
  exact List.forall_mem_cons.2 ⟨sub10_1152, List.forall_mem_cons.2 ⟨sub10_1153, List.forall_mem_cons.2 ⟨sub10_1154, List.forall_mem_cons.2 ⟨sub10_1155, List.forall_mem_cons.2 ⟨sub10_1156, List.forall_mem_cons.2 ⟨sub10_1157, List.forall_mem_cons.2 ⟨sub10_1158, List.forall_mem_cons.2 ⟨sub10_1159, List.forall_mem_cons.2 ⟨sub10_1160, List.forall_mem_cons.2 ⟨sub10_1161, List.forall_mem_cons.2 ⟨sub10_1162, List.forall_mem_cons.2 ⟨sub10_1163, List.forall_mem_cons.2 ⟨sub10_1164, List.forall_mem_cons.2 ⟨sub10_1165, List.forall_mem_cons.2 ⟨sub10_1166, List.forall_mem_cons.2 ⟨sub10_1167, List.forall_mem_cons.2 ⟨sub10_1168, List.forall_mem_cons.2 ⟨sub10_1169, List.forall_mem_cons.2 ⟨sub10_1170, List.forall_mem_cons.2 ⟨sub10_1171, List.forall_mem_cons.2 ⟨sub10_1172, List.forall_mem_cons.2 ⟨sub10_1173, List.forall_mem_cons.2 ⟨sub10_1174, List.forall_mem_cons.2 ⟨sub10_1175, List.forall_mem_cons.2 ⟨sub10_1176, List.forall_mem_cons.2 ⟨sub10_1177, List.forall_mem_cons.2 ⟨sub10_1178, List.forall_mem_cons.2 ⟨sub10_1179, List.forall_mem_cons.2 ⟨sub10_1180, List.forall_mem_cons.2 ⟨sub10_1181, List.forall_mem_cons.2 ⟨sub10_1182, List.forall_mem_cons.2 ⟨sub10_1183, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_1184 : sub10 [1, 4, -4] = true := by decide +kernel
theorem sub10_1185 : sub10 [1, 4, -3] = true := by decide +kernel
theorem sub10_1186 : sub10 [1, 4, -2] = true := by decide +kernel
theorem sub10_1187 : sub10 [1, 4, -1] = true := by decide +kernel
theorem sub10_1188 : sub10 [1, 4, 0] = true := by decide +kernel
theorem sub10_1189 : sub10 [1, 4, 1] = true := by decide +kernel
theorem sub10_1190 : sub10 [1, 4, 2] = true := by decide +kernel
theorem sub10_1191 : sub10 [1, 4, 3] = true := by decide +kernel
theorem sub10_1192 : sub10 [1, 4, 4] = true := by decide +kernel
theorem sub10_1193 : sub10 [1, 4, 5] = true := by decide +kernel
theorem sub10_1194 : sub10 [1, 4, 6] = true := by decide +kernel
theorem sub10_1195 : sub10 [1, 5, -8] = true := by decide +kernel
theorem sub10_1196 : sub10 [1, 5, -7] = true := by decide +kernel
theorem sub10_1197 : sub10 [1, 5, -6] = true := by decide +kernel
theorem sub10_1198 : sub10 [1, 5, -5] = true := by decide +kernel
theorem sub10_1199 : sub10 [1, 5, -4] = true := by decide +kernel
theorem sub10_1200 : sub10 [1, 5, -3] = true := by decide +kernel
theorem sub10_1201 : sub10 [1, 5, -2] = true := by decide +kernel
theorem sub10_1202 : sub10 [1, 5, -1] = true := by decide +kernel
theorem sub10_1203 : sub10 [1, 5, 0] = true := by decide +kernel
theorem sub10_1204 : sub10 [1, 5, 1] = true := by decide +kernel
theorem sub10_1205 : sub10 [1, 5, 2] = true := by decide +kernel
theorem sub10_1206 : sub10 [1, 5, 3] = true := by decide +kernel
theorem sub10_1207 : sub10 [1, 5, 4] = true := by decide +kernel
theorem sub10_1208 : sub10 [1, 5, 5] = true := by decide +kernel
theorem sub10_1209 : sub10 [1, 6] = true := by decide +kernel
theorem sub10_1210 : sub10 [1, 7] = true := by decide +kernel
theorem sub10_1211 : sub10 [2, -9] = true := by decide +kernel
theorem sub10_1212 : sub10 [2, -8] = true := by decide +kernel
theorem sub10_1213 : sub10 [2, -7] = true := by decide +kernel
theorem sub10_1214 : sub10 [2, -6, -5] = true := by decide +kernel
theorem sub10_1215 : sub10 [2, -6, -4] = true := by decide +kernel
theorem sb10_37 : ∀ q ∈ blk10_37, sub10 q = true := by
  unfold blk10_37
  exact List.forall_mem_cons.2 ⟨sub10_1184, List.forall_mem_cons.2 ⟨sub10_1185, List.forall_mem_cons.2 ⟨sub10_1186, List.forall_mem_cons.2 ⟨sub10_1187, List.forall_mem_cons.2 ⟨sub10_1188, List.forall_mem_cons.2 ⟨sub10_1189, List.forall_mem_cons.2 ⟨sub10_1190, List.forall_mem_cons.2 ⟨sub10_1191, List.forall_mem_cons.2 ⟨sub10_1192, List.forall_mem_cons.2 ⟨sub10_1193, List.forall_mem_cons.2 ⟨sub10_1194, List.forall_mem_cons.2 ⟨sub10_1195, List.forall_mem_cons.2 ⟨sub10_1196, List.forall_mem_cons.2 ⟨sub10_1197, List.forall_mem_cons.2 ⟨sub10_1198, List.forall_mem_cons.2 ⟨sub10_1199, List.forall_mem_cons.2 ⟨sub10_1200, List.forall_mem_cons.2 ⟨sub10_1201, List.forall_mem_cons.2 ⟨sub10_1202, List.forall_mem_cons.2 ⟨sub10_1203, List.forall_mem_cons.2 ⟨sub10_1204, List.forall_mem_cons.2 ⟨sub10_1205, List.forall_mem_cons.2 ⟨sub10_1206, List.forall_mem_cons.2 ⟨sub10_1207, List.forall_mem_cons.2 ⟨sub10_1208, List.forall_mem_cons.2 ⟨sub10_1209, List.forall_mem_cons.2 ⟨sub10_1210, List.forall_mem_cons.2 ⟨sub10_1211, List.forall_mem_cons.2 ⟨sub10_1212, List.forall_mem_cons.2 ⟨sub10_1213, List.forall_mem_cons.2 ⟨sub10_1214, List.forall_mem_cons.2 ⟨sub10_1215, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_1216 : sub10 [2, -6, -3] = true := by decide +kernel
theorem sub10_1217 : sub10 [2, -6, -2] = true := by decide +kernel
theorem sub10_1218 : sub10 [2, -6, -1] = true := by decide +kernel
theorem sub10_1219 : sub10 [2, -6, 0] = true := by decide +kernel
theorem sub10_1220 : sub10 [2, -6, 1] = true := by decide +kernel
theorem sub10_1221 : sub10 [2, -6, 2] = true := by decide +kernel
theorem sub10_1222 : sub10 [2, -6, 3] = true := by decide +kernel
theorem sub10_1223 : sub10 [2, -6, 4] = true := by decide +kernel
theorem sub10_1224 : sub10 [2, -6, 5] = true := by decide +kernel
theorem sub10_1225 : sub10 [2, -6, 6] = true := by decide +kernel
theorem sub10_1226 : sub10 [2, -6, 7] = true := by decide +kernel
theorem sub10_1227 : sub10 [2, -6, 8] = true := by decide +kernel
theorem sub10_1228 : sub10 [2, -5, -6] = true := by decide +kernel
theorem sub10_1229 : sub10 [2, -5, -5] = true := by decide +kernel
theorem sub10_1230 : sub10 [2, -5, -4] = true := by decide +kernel
theorem sub10_1231 : sub10 [2, -5, -3] = true := by decide +kernel
theorem sub10_1232 : sub10 [2, -5, -2] = true := by decide +kernel
theorem sub10_1233 : sub10 [2, -5, -1] = true := by decide +kernel
theorem sub10_1234 : sub10 [2, -5, 0] = true := by decide +kernel
theorem sub10_1235 : sub10 [2, -5, 1] = true := by decide +kernel
theorem sub10_1236 : sub10 [2, -5, 2] = true := by decide +kernel
theorem sub10_1237 : sub10 [2, -5, 3] = true := by decide +kernel
theorem sub10_1238 : sub10 [2, -5, 4] = true := by decide +kernel
theorem sub10_1239 : sub10 [2, -5, 5] = true := by decide +kernel
theorem sub10_1240 : sub10 [2, -5, 6] = true := by decide +kernel
theorem sub10_1241 : sub10 [2, -5, 7] = true := by decide +kernel
theorem sub10_1242 : sub10 [2, -5, 8] = true := by decide +kernel
theorem sub10_1243 : sub10 [2, -5, 9] = true := by decide +kernel
theorem sub10_1244 : sub10 [2, -4, -7] = true := by decide +kernel
theorem sub10_1245 : sub10 [2, -4, -6] = true := by decide +kernel
theorem sub10_1246 : sub10 [2, -4, -5] = true := by decide +kernel
theorem sub10_1247 : sub10 [2, -4, -4] = true := by decide +kernel
theorem sb10_38 : ∀ q ∈ blk10_38, sub10 q = true := by
  unfold blk10_38
  exact List.forall_mem_cons.2 ⟨sub10_1216, List.forall_mem_cons.2 ⟨sub10_1217, List.forall_mem_cons.2 ⟨sub10_1218, List.forall_mem_cons.2 ⟨sub10_1219, List.forall_mem_cons.2 ⟨sub10_1220, List.forall_mem_cons.2 ⟨sub10_1221, List.forall_mem_cons.2 ⟨sub10_1222, List.forall_mem_cons.2 ⟨sub10_1223, List.forall_mem_cons.2 ⟨sub10_1224, List.forall_mem_cons.2 ⟨sub10_1225, List.forall_mem_cons.2 ⟨sub10_1226, List.forall_mem_cons.2 ⟨sub10_1227, List.forall_mem_cons.2 ⟨sub10_1228, List.forall_mem_cons.2 ⟨sub10_1229, List.forall_mem_cons.2 ⟨sub10_1230, List.forall_mem_cons.2 ⟨sub10_1231, List.forall_mem_cons.2 ⟨sub10_1232, List.forall_mem_cons.2 ⟨sub10_1233, List.forall_mem_cons.2 ⟨sub10_1234, List.forall_mem_cons.2 ⟨sub10_1235, List.forall_mem_cons.2 ⟨sub10_1236, List.forall_mem_cons.2 ⟨sub10_1237, List.forall_mem_cons.2 ⟨sub10_1238, List.forall_mem_cons.2 ⟨sub10_1239, List.forall_mem_cons.2 ⟨sub10_1240, List.forall_mem_cons.2 ⟨sub10_1241, List.forall_mem_cons.2 ⟨sub10_1242, List.forall_mem_cons.2 ⟨sub10_1243, List.forall_mem_cons.2 ⟨sub10_1244, List.forall_mem_cons.2 ⟨sub10_1245, List.forall_mem_cons.2 ⟨sub10_1246, List.forall_mem_cons.2 ⟨sub10_1247, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_1248 : sub10 [2, -4, -3] = true := by decide +kernel
theorem sub10_1249 : sub10 [2, -4, -2] = true := by decide +kernel
theorem sub10_1250 : sub10 [2, -4, -1] = true := by decide +kernel
theorem sub10_1251 : sub10 [2, -4, 0] = true := by decide +kernel
theorem sub10_1252 : sub10 [2, -4, 1] = true := by decide +kernel
theorem sub10_1253 : sub10 [2, -4, 2] = true := by decide +kernel
theorem sub10_1254 : sub10 [2, -4, 3] = true := by decide +kernel
theorem sub10_1255 : sub10 [2, -4, 4] = true := by decide +kernel
theorem sub10_1256 : sub10 [2, -4, 5] = true := by decide +kernel
theorem sub10_1257 : sub10 [2, -4, 6] = true := by decide +kernel
theorem sub10_1258 : sub10 [2, -4, 7] = true := by decide +kernel
theorem sub10_1259 : sub10 [2, -4, 8] = true := by decide +kernel
theorem sub10_1260 : sub10 [2, -4, 9] = true := by decide +kernel
theorem sub10_1261 : sub10 [2, -3, -7] = true := by decide +kernel
theorem sub10_1262 : sub10 [2, -3, -6] = true := by decide +kernel
theorem sub10_1263 : sub10 [2, -3, -5] = true := by decide +kernel
theorem sub10_1264 : sub10 [2, -3, -4] = true := by decide +kernel
theorem sub10_1265 : sub10 [2, -3, -3] = true := by decide +kernel
theorem sub10_1266 : sub10 [2, -3, -2] = true := by decide +kernel
theorem sub10_1267 : sub10 [2, -3, -1] = true := by decide +kernel
theorem sub10_1268 : sub10 [2, -3, 0] = true := by decide +kernel
theorem sub10_1269 : sub10 [2, -3, 1] = true := by decide +kernel
theorem sub10_1270 : sub10 [2, -3, 2] = true := by decide +kernel
theorem sub10_1271 : sub10 [2, -3, 3] = true := by decide +kernel
theorem sub10_1272 : sub10 [2, -3, 4] = true := by decide +kernel
theorem sub10_1273 : sub10 [2, -3, 5] = true := by decide +kernel
theorem sub10_1274 : sub10 [2, -3, 6] = true := by decide +kernel
theorem sub10_1275 : sub10 [2, -3, 7] = true := by decide +kernel
theorem sub10_1276 : sub10 [2, -3, 8] = true := by decide +kernel
theorem sub10_1277 : sub10 [2, -3, 9] = true := by decide +kernel
theorem sub10_1278 : sub10 [2, -2, -8] = true := by decide +kernel
theorem sub10_1279 : sub10 [2, -2, -7] = true := by decide +kernel
theorem sb10_39 : ∀ q ∈ blk10_39, sub10 q = true := by
  unfold blk10_39
  exact List.forall_mem_cons.2 ⟨sub10_1248, List.forall_mem_cons.2 ⟨sub10_1249, List.forall_mem_cons.2 ⟨sub10_1250, List.forall_mem_cons.2 ⟨sub10_1251, List.forall_mem_cons.2 ⟨sub10_1252, List.forall_mem_cons.2 ⟨sub10_1253, List.forall_mem_cons.2 ⟨sub10_1254, List.forall_mem_cons.2 ⟨sub10_1255, List.forall_mem_cons.2 ⟨sub10_1256, List.forall_mem_cons.2 ⟨sub10_1257, List.forall_mem_cons.2 ⟨sub10_1258, List.forall_mem_cons.2 ⟨sub10_1259, List.forall_mem_cons.2 ⟨sub10_1260, List.forall_mem_cons.2 ⟨sub10_1261, List.forall_mem_cons.2 ⟨sub10_1262, List.forall_mem_cons.2 ⟨sub10_1263, List.forall_mem_cons.2 ⟨sub10_1264, List.forall_mem_cons.2 ⟨sub10_1265, List.forall_mem_cons.2 ⟨sub10_1266, List.forall_mem_cons.2 ⟨sub10_1267, List.forall_mem_cons.2 ⟨sub10_1268, List.forall_mem_cons.2 ⟨sub10_1269, List.forall_mem_cons.2 ⟨sub10_1270, List.forall_mem_cons.2 ⟨sub10_1271, List.forall_mem_cons.2 ⟨sub10_1272, List.forall_mem_cons.2 ⟨sub10_1273, List.forall_mem_cons.2 ⟨sub10_1274, List.forall_mem_cons.2 ⟨sub10_1275, List.forall_mem_cons.2 ⟨sub10_1276, List.forall_mem_cons.2 ⟨sub10_1277, List.forall_mem_cons.2 ⟨sub10_1278, List.forall_mem_cons.2 ⟨sub10_1279, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_1280 : sub10 [2, -2, -6] = true := by decide +kernel
theorem sub10_1281 : sub10 [2, -2, -5] = true := by decide +kernel
theorem sub10_1282 : sub10 [2, -2, -4] = true := by decide +kernel
theorem sub10_1283 : sub10 [2, -2, -3] = true := by decide +kernel
theorem sub10_1284 : sub10 [2, -2, -2] = true := by decide +kernel
theorem sub10_1285 : sub10 [2, -2, -1] = true := by decide +kernel
theorem sub10_1286 : sub10 [2, -2, 0] = true := by decide +kernel
theorem sub10_1287 : sub10 [2, -2, 1] = true := by decide +kernel
theorem sub10_1288 : sub10 [2, -2, 2] = true := by decide +kernel
theorem sub10_1289 : sub10 [2, -2, 3] = true := by decide +kernel
theorem sub10_1290 : sub10 [2, -2, 4] = true := by decide +kernel
theorem sub10_1291 : sub10 [2, -2, 5] = true := by decide +kernel
theorem sub10_1292 : sub10 [2, -2, 6] = true := by decide +kernel
theorem sub10_1293 : sub10 [2, -2, 7] = true := by decide +kernel
theorem sub10_1294 : sub10 [2, -2, 8] = true := by decide +kernel
theorem sub10_1295 : sub10 [2, -2, 9] = true := by decide +kernel
theorem sub10_1296 : sub10 [2, -1, -8] = true := by decide +kernel
theorem sub10_1297 : sub10 [2, -1, -7] = true := by decide +kernel
theorem sub10_1298 : sub10 [2, -1, -6] = true := by decide +kernel
theorem sub10_1299 : sub10 [2, -1, -5] = true := by decide +kernel
theorem sub10_1300 : sub10 [2, -1, -4] = true := by decide +kernel
theorem sub10_1301 : sub10 [2, -1, -3] = true := by decide +kernel
theorem sub10_1302 : sub10 [2, -1, -2] = true := by decide +kernel
theorem sub10_1303 : sub10 [2, -1, -1] = true := by decide +kernel
theorem sub10_1304 : sub10 [2, -1, 0] = true := by decide +kernel
theorem sub10_1305 : sub10 [2, -1, 1] = true := by decide +kernel
theorem sub10_1306 : sub10 [2, -1, 2] = true := by decide +kernel
theorem sub10_1307 : sub10 [2, -1, 3] = true := by decide +kernel
theorem sub10_1308 : sub10 [2, -1, 4] = true := by decide +kernel
theorem sub10_1309 : sub10 [2, -1, 5] = true := by decide +kernel
theorem sub10_1310 : sub10 [2, -1, 6] = true := by decide +kernel
theorem sub10_1311 : sub10 [2, -1, 7] = true := by decide +kernel
theorem sb10_40 : ∀ q ∈ blk10_40, sub10 q = true := by
  unfold blk10_40
  exact List.forall_mem_cons.2 ⟨sub10_1280, List.forall_mem_cons.2 ⟨sub10_1281, List.forall_mem_cons.2 ⟨sub10_1282, List.forall_mem_cons.2 ⟨sub10_1283, List.forall_mem_cons.2 ⟨sub10_1284, List.forall_mem_cons.2 ⟨sub10_1285, List.forall_mem_cons.2 ⟨sub10_1286, List.forall_mem_cons.2 ⟨sub10_1287, List.forall_mem_cons.2 ⟨sub10_1288, List.forall_mem_cons.2 ⟨sub10_1289, List.forall_mem_cons.2 ⟨sub10_1290, List.forall_mem_cons.2 ⟨sub10_1291, List.forall_mem_cons.2 ⟨sub10_1292, List.forall_mem_cons.2 ⟨sub10_1293, List.forall_mem_cons.2 ⟨sub10_1294, List.forall_mem_cons.2 ⟨sub10_1295, List.forall_mem_cons.2 ⟨sub10_1296, List.forall_mem_cons.2 ⟨sub10_1297, List.forall_mem_cons.2 ⟨sub10_1298, List.forall_mem_cons.2 ⟨sub10_1299, List.forall_mem_cons.2 ⟨sub10_1300, List.forall_mem_cons.2 ⟨sub10_1301, List.forall_mem_cons.2 ⟨sub10_1302, List.forall_mem_cons.2 ⟨sub10_1303, List.forall_mem_cons.2 ⟨sub10_1304, List.forall_mem_cons.2 ⟨sub10_1305, List.forall_mem_cons.2 ⟨sub10_1306, List.forall_mem_cons.2 ⟨sub10_1307, List.forall_mem_cons.2 ⟨sub10_1308, List.forall_mem_cons.2 ⟨sub10_1309, List.forall_mem_cons.2 ⟨sub10_1310, List.forall_mem_cons.2 ⟨sub10_1311, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_1312 : sub10 [2, -1, 8] = true := by decide +kernel
theorem sub10_1313 : sub10 [2, -1, 9] = true := by decide +kernel
theorem sub10_1314 : sub10 [2, 0, -8] = true := by decide +kernel
theorem sub10_1315 : sub10 [2, 0, -7] = true := by decide +kernel
theorem sub10_1316 : sub10 [2, 0, -6] = true := by decide +kernel
theorem sub10_1317 : sub10 [2, 0, -5] = true := by decide +kernel
theorem sub10_1318 : sub10 [2, 0, -4] = true := by decide +kernel
theorem sub10_1319 : sub10 [2, 0, -3] = true := by decide +kernel
theorem sub10_1320 : sub10 [2, 0, -2] = true := by decide +kernel
theorem sub10_1321 : sub10 [2, 0, -1] = true := by decide +kernel
theorem sub10_1322 : sub10 [2, 0, 0] = true := by decide +kernel
theorem sub10_1323 : sub10 [2, 0, 1] = true := by decide +kernel
theorem sub10_1324 : sub10 [2, 0, 2] = true := by decide +kernel
theorem sub10_1325 : sub10 [2, 0, 3] = true := by decide +kernel
theorem sub10_1326 : sub10 [2, 0, 4] = true := by decide +kernel
theorem sub10_1327 : sub10 [2, 0, 5] = true := by decide +kernel
theorem sub10_1328 : sub10 [2, 0, 6] = true := by decide +kernel
theorem sub10_1329 : sub10 [2, 0, 7] = true := by decide +kernel
theorem sub10_1330 : sub10 [2, 0, 8] = true := by decide +kernel
theorem sub10_1331 : sub10 [2, 0, 9] = true := by decide +kernel
theorem sub10_1332 : sub10 [2, 1, -8] = true := by decide +kernel
theorem sub10_1333 : sub10 [2, 1, -7] = true := by decide +kernel
theorem sub10_1334 : sub10 [2, 1, -6] = true := by decide +kernel
theorem sub10_1335 : sub10 [2, 1, -5] = true := by decide +kernel
theorem sub10_1336 : sub10 [2, 1, -4] = true := by decide +kernel
theorem sub10_1337 : sub10 [2, 1, -3] = true := by decide +kernel
theorem sub10_1338 : sub10 [2, 1, -2] = true := by decide +kernel
theorem sub10_1339 : sub10 [2, 1, -1] = true := by decide +kernel
theorem sub10_1340 : sub10 [2, 1, 0] = true := by decide +kernel
theorem sub10_1341 : sub10 [2, 1, 1] = true := by decide +kernel
theorem sub10_1342 : sub10 [2, 1, 2] = true := by decide +kernel
theorem sub10_1343 : sub10 [2, 1, 3] = true := by decide +kernel
theorem sb10_41 : ∀ q ∈ blk10_41, sub10 q = true := by
  unfold blk10_41
  exact List.forall_mem_cons.2 ⟨sub10_1312, List.forall_mem_cons.2 ⟨sub10_1313, List.forall_mem_cons.2 ⟨sub10_1314, List.forall_mem_cons.2 ⟨sub10_1315, List.forall_mem_cons.2 ⟨sub10_1316, List.forall_mem_cons.2 ⟨sub10_1317, List.forall_mem_cons.2 ⟨sub10_1318, List.forall_mem_cons.2 ⟨sub10_1319, List.forall_mem_cons.2 ⟨sub10_1320, List.forall_mem_cons.2 ⟨sub10_1321, List.forall_mem_cons.2 ⟨sub10_1322, List.forall_mem_cons.2 ⟨sub10_1323, List.forall_mem_cons.2 ⟨sub10_1324, List.forall_mem_cons.2 ⟨sub10_1325, List.forall_mem_cons.2 ⟨sub10_1326, List.forall_mem_cons.2 ⟨sub10_1327, List.forall_mem_cons.2 ⟨sub10_1328, List.forall_mem_cons.2 ⟨sub10_1329, List.forall_mem_cons.2 ⟨sub10_1330, List.forall_mem_cons.2 ⟨sub10_1331, List.forall_mem_cons.2 ⟨sub10_1332, List.forall_mem_cons.2 ⟨sub10_1333, List.forall_mem_cons.2 ⟨sub10_1334, List.forall_mem_cons.2 ⟨sub10_1335, List.forall_mem_cons.2 ⟨sub10_1336, List.forall_mem_cons.2 ⟨sub10_1337, List.forall_mem_cons.2 ⟨sub10_1338, List.forall_mem_cons.2 ⟨sub10_1339, List.forall_mem_cons.2 ⟨sub10_1340, List.forall_mem_cons.2 ⟨sub10_1341, List.forall_mem_cons.2 ⟨sub10_1342, List.forall_mem_cons.2 ⟨sub10_1343, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_1344 : sub10 [2, 1, 4] = true := by decide +kernel
theorem sub10_1345 : sub10 [2, 1, 5] = true := by decide +kernel
theorem sub10_1346 : sub10 [2, 1, 6] = true := by decide +kernel
theorem sub10_1347 : sub10 [2, 1, 7] = true := by decide +kernel
theorem sub10_1348 : sub10 [2, 1, 8] = true := by decide +kernel
theorem sub10_1349 : sub10 [2, 2, -8] = true := by decide +kernel
theorem sub10_1350 : sub10 [2, 2, -7] = true := by decide +kernel
theorem sub10_1351 : sub10 [2, 2, -6] = true := by decide +kernel
theorem sub10_1352 : sub10 [2, 2, -5] = true := by decide +kernel
theorem sub10_1353 : sub10 [2, 2, -4] = true := by decide +kernel
theorem sub10_1354 : sub10 [2, 2, -3] = true := by decide +kernel
theorem sub10_1355 : sub10 [2, 2, -2] = true := by decide +kernel
theorem sub10_1356 : sub10 [2, 2, -1] = true := by decide +kernel
theorem sub10_1357 : sub10 [2, 2, 0] = true := by decide +kernel
theorem sub10_1358 : sub10 [2, 2, 1] = true := by decide +kernel
theorem sub10_1359 : sub10 [2, 2, 2] = true := by decide +kernel
theorem sub10_1360 : sub10 [2, 2, 3] = true := by decide +kernel
theorem sub10_1361 : sub10 [2, 2, 4] = true := by decide +kernel
theorem sub10_1362 : sub10 [2, 2, 5] = true := by decide +kernel
theorem sub10_1363 : sub10 [2, 2, 6] = true := by decide +kernel
theorem sub10_1364 : sub10 [2, 2, 7] = true := by decide +kernel
theorem sub10_1365 : sub10 [2, 2, 8] = true := by decide +kernel
theorem sub10_1366 : sub10 [2, 3, -8] = true := by decide +kernel
theorem sub10_1367 : sub10 [2, 3, -7] = true := by decide +kernel
theorem sub10_1368 : sub10 [2, 3, -6] = true := by decide +kernel
theorem sub10_1369 : sub10 [2, 3, -5] = true := by decide +kernel
theorem sub10_1370 : sub10 [2, 3, -4] = true := by decide +kernel
theorem sub10_1371 : sub10 [2, 3, -3] = true := by decide +kernel
theorem sub10_1372 : sub10 [2, 3, -2] = true := by decide +kernel
theorem sub10_1373 : sub10 [2, 3, -1] = true := by decide +kernel
theorem sub10_1374 : sub10 [2, 3, 0] = true := by decide +kernel
theorem sub10_1375 : sub10 [2, 3, 1] = true := by decide +kernel
theorem sb10_42 : ∀ q ∈ blk10_42, sub10 q = true := by
  unfold blk10_42
  exact List.forall_mem_cons.2 ⟨sub10_1344, List.forall_mem_cons.2 ⟨sub10_1345, List.forall_mem_cons.2 ⟨sub10_1346, List.forall_mem_cons.2 ⟨sub10_1347, List.forall_mem_cons.2 ⟨sub10_1348, List.forall_mem_cons.2 ⟨sub10_1349, List.forall_mem_cons.2 ⟨sub10_1350, List.forall_mem_cons.2 ⟨sub10_1351, List.forall_mem_cons.2 ⟨sub10_1352, List.forall_mem_cons.2 ⟨sub10_1353, List.forall_mem_cons.2 ⟨sub10_1354, List.forall_mem_cons.2 ⟨sub10_1355, List.forall_mem_cons.2 ⟨sub10_1356, List.forall_mem_cons.2 ⟨sub10_1357, List.forall_mem_cons.2 ⟨sub10_1358, List.forall_mem_cons.2 ⟨sub10_1359, List.forall_mem_cons.2 ⟨sub10_1360, List.forall_mem_cons.2 ⟨sub10_1361, List.forall_mem_cons.2 ⟨sub10_1362, List.forall_mem_cons.2 ⟨sub10_1363, List.forall_mem_cons.2 ⟨sub10_1364, List.forall_mem_cons.2 ⟨sub10_1365, List.forall_mem_cons.2 ⟨sub10_1366, List.forall_mem_cons.2 ⟨sub10_1367, List.forall_mem_cons.2 ⟨sub10_1368, List.forall_mem_cons.2 ⟨sub10_1369, List.forall_mem_cons.2 ⟨sub10_1370, List.forall_mem_cons.2 ⟨sub10_1371, List.forall_mem_cons.2 ⟨sub10_1372, List.forall_mem_cons.2 ⟨sub10_1373, List.forall_mem_cons.2 ⟨sub10_1374, List.forall_mem_cons.2 ⟨sub10_1375, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_1376 : sub10 [2, 3, 2] = true := by decide +kernel
theorem sub10_1377 : sub10 [2, 3, 3] = true := by decide +kernel
theorem sub10_1378 : sub10 [2, 3, 4] = true := by decide +kernel
theorem sub10_1379 : sub10 [2, 3, 5] = true := by decide +kernel
theorem sub10_1380 : sub10 [2, 3, 6] = true := by decide +kernel
theorem sub10_1381 : sub10 [2, 3, 7] = true := by decide +kernel
theorem sub10_1382 : sub10 [2, 4, -8] = true := by decide +kernel
theorem sub10_1383 : sub10 [2, 4, -7] = true := by decide +kernel
theorem sub10_1384 : sub10 [2, 4, -6] = true := by decide +kernel
theorem sub10_1385 : sub10 [2, 4, -5] = true := by decide +kernel
theorem sub10_1386 : sub10 [2, 4, -4] = true := by decide +kernel
theorem sub10_1387 : sub10 [2, 4, -3] = true := by decide +kernel
theorem sub10_1388 : sub10 [2, 4, -2] = true := by decide +kernel
theorem sub10_1389 : sub10 [2, 4, -1] = true := by decide +kernel
theorem sub10_1390 : sub10 [2, 4, 0] = true := by decide +kernel
theorem sub10_1391 : sub10 [2, 4, 1] = true := by decide +kernel
theorem sub10_1392 : sub10 [2, 4, 2] = true := by decide +kernel
theorem sub10_1393 : sub10 [2, 4, 3] = true := by decide +kernel
theorem sub10_1394 : sub10 [2, 4, 4] = true := by decide +kernel
theorem sub10_1395 : sub10 [2, 4, 5] = true := by decide +kernel
theorem sub10_1396 : sub10 [2, 4, 6] = true := by decide +kernel
theorem sub10_1397 : sub10 [2, 5] = true := by decide +kernel
theorem sub10_1398 : sub10 [2, 6] = true := by decide +kernel
theorem sub10_1399 : sub10 [2, 7] = true := by decide +kernel
theorem sub10_1400 : sub10 [3, -9] = true := by decide +kernel
theorem sub10_1401 : sub10 [3, -8] = true := by decide +kernel
theorem sub10_1402 : sub10 [3, -7] = true := by decide +kernel
theorem sub10_1403 : sub10 [3, -6, -5] = true := by decide +kernel
theorem sub10_1404 : sub10 [3, -6, -4] = true := by decide +kernel
theorem sub10_1405 : sub10 [3, -6, -3] = true := by decide +kernel
theorem sub10_1406 : sub10 [3, -6, -2] = true := by decide +kernel
theorem sub10_1407 : sub10 [3, -6, -1] = true := by decide +kernel
theorem sb10_43 : ∀ q ∈ blk10_43, sub10 q = true := by
  unfold blk10_43
  exact List.forall_mem_cons.2 ⟨sub10_1376, List.forall_mem_cons.2 ⟨sub10_1377, List.forall_mem_cons.2 ⟨sub10_1378, List.forall_mem_cons.2 ⟨sub10_1379, List.forall_mem_cons.2 ⟨sub10_1380, List.forall_mem_cons.2 ⟨sub10_1381, List.forall_mem_cons.2 ⟨sub10_1382, List.forall_mem_cons.2 ⟨sub10_1383, List.forall_mem_cons.2 ⟨sub10_1384, List.forall_mem_cons.2 ⟨sub10_1385, List.forall_mem_cons.2 ⟨sub10_1386, List.forall_mem_cons.2 ⟨sub10_1387, List.forall_mem_cons.2 ⟨sub10_1388, List.forall_mem_cons.2 ⟨sub10_1389, List.forall_mem_cons.2 ⟨sub10_1390, List.forall_mem_cons.2 ⟨sub10_1391, List.forall_mem_cons.2 ⟨sub10_1392, List.forall_mem_cons.2 ⟨sub10_1393, List.forall_mem_cons.2 ⟨sub10_1394, List.forall_mem_cons.2 ⟨sub10_1395, List.forall_mem_cons.2 ⟨sub10_1396, List.forall_mem_cons.2 ⟨sub10_1397, List.forall_mem_cons.2 ⟨sub10_1398, List.forall_mem_cons.2 ⟨sub10_1399, List.forall_mem_cons.2 ⟨sub10_1400, List.forall_mem_cons.2 ⟨sub10_1401, List.forall_mem_cons.2 ⟨sub10_1402, List.forall_mem_cons.2 ⟨sub10_1403, List.forall_mem_cons.2 ⟨sub10_1404, List.forall_mem_cons.2 ⟨sub10_1405, List.forall_mem_cons.2 ⟨sub10_1406, List.forall_mem_cons.2 ⟨sub10_1407, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_1408 : sub10 [3, -6, 0] = true := by decide +kernel
theorem sub10_1409 : sub10 [3, -6, 1] = true := by decide +kernel
theorem sub10_1410 : sub10 [3, -6, 2] = true := by decide +kernel
theorem sub10_1411 : sub10 [3, -6, 3] = true := by decide +kernel
theorem sub10_1412 : sub10 [3, -6, 4] = true := by decide +kernel
theorem sub10_1413 : sub10 [3, -6, 5] = true := by decide +kernel
theorem sub10_1414 : sub10 [3, -6, 6] = true := by decide +kernel
theorem sub10_1415 : sub10 [3, -6, 7] = true := by decide +kernel
theorem sub10_1416 : sub10 [3, -6, 8] = true := by decide +kernel
theorem sub10_1417 : sub10 [3, -5, -6] = true := by decide +kernel
theorem sub10_1418 : sub10 [3, -5, -5] = true := by decide +kernel
theorem sub10_1419 : sub10 [3, -5, -4] = true := by decide +kernel
theorem sub10_1420 : sub10 [3, -5, -3] = true := by decide +kernel
theorem sub10_1421 : sub10 [3, -5, -2] = true := by decide +kernel
theorem sub10_1422 : sub10 [3, -5, -1] = true := by decide +kernel
theorem sub10_1423 : sub10 [3, -5, 0] = true := by decide +kernel
theorem sub10_1424 : sub10 [3, -5, 1] = true := by decide +kernel
theorem sub10_1425 : sub10 [3, -5, 2] = true := by decide +kernel
theorem sub10_1426 : sub10 [3, -5, 3] = true := by decide +kernel
theorem sub10_1427 : sub10 [3, -5, 4] = true := by decide +kernel
theorem sub10_1428 : sub10 [3, -5, 5] = true := by decide +kernel
theorem sub10_1429 : sub10 [3, -5, 6] = true := by decide +kernel
theorem sub10_1430 : sub10 [3, -5, 7] = true := by decide +kernel
theorem sub10_1431 : sub10 [3, -5, 8] = true := by decide +kernel
theorem sub10_1432 : sub10 [3, -5, 9] = true := by decide +kernel
theorem sub10_1433 : sub10 [3, -4, -6] = true := by decide +kernel
theorem sub10_1434 : sub10 [3, -4, -5] = true := by decide +kernel
theorem sub10_1435 : sub10 [3, -4, -4] = true := by decide +kernel
theorem sub10_1436 : sub10 [3, -4, -3] = true := by decide +kernel
theorem sub10_1437 : sub10 [3, -4, -2] = true := by decide +kernel
theorem sub10_1438 : sub10 [3, -4, -1] = true := by decide +kernel
theorem sub10_1439 : sub10 [3, -4, 0] = true := by decide +kernel
theorem sb10_44 : ∀ q ∈ blk10_44, sub10 q = true := by
  unfold blk10_44
  exact List.forall_mem_cons.2 ⟨sub10_1408, List.forall_mem_cons.2 ⟨sub10_1409, List.forall_mem_cons.2 ⟨sub10_1410, List.forall_mem_cons.2 ⟨sub10_1411, List.forall_mem_cons.2 ⟨sub10_1412, List.forall_mem_cons.2 ⟨sub10_1413, List.forall_mem_cons.2 ⟨sub10_1414, List.forall_mem_cons.2 ⟨sub10_1415, List.forall_mem_cons.2 ⟨sub10_1416, List.forall_mem_cons.2 ⟨sub10_1417, List.forall_mem_cons.2 ⟨sub10_1418, List.forall_mem_cons.2 ⟨sub10_1419, List.forall_mem_cons.2 ⟨sub10_1420, List.forall_mem_cons.2 ⟨sub10_1421, List.forall_mem_cons.2 ⟨sub10_1422, List.forall_mem_cons.2 ⟨sub10_1423, List.forall_mem_cons.2 ⟨sub10_1424, List.forall_mem_cons.2 ⟨sub10_1425, List.forall_mem_cons.2 ⟨sub10_1426, List.forall_mem_cons.2 ⟨sub10_1427, List.forall_mem_cons.2 ⟨sub10_1428, List.forall_mem_cons.2 ⟨sub10_1429, List.forall_mem_cons.2 ⟨sub10_1430, List.forall_mem_cons.2 ⟨sub10_1431, List.forall_mem_cons.2 ⟨sub10_1432, List.forall_mem_cons.2 ⟨sub10_1433, List.forall_mem_cons.2 ⟨sub10_1434, List.forall_mem_cons.2 ⟨sub10_1435, List.forall_mem_cons.2 ⟨sub10_1436, List.forall_mem_cons.2 ⟨sub10_1437, List.forall_mem_cons.2 ⟨sub10_1438, List.forall_mem_cons.2 ⟨sub10_1439, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C074
