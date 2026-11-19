import ReflectZphi.Data.Cert5.C125.Base

namespace ReflectZphi.Data.Cert5.C125
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub7_1024 : sub7 [3, -1, -9] = true := by decide +kernel
theorem sub7_1025 : sub7 [3, -1, -8] = true := by decide +kernel
theorem sub7_1026 : sub7 [3, -1, -7] = true := by decide +kernel
theorem sub7_1027 : sub7 [3, -1, -6] = true := by decide +kernel
theorem sub7_1028 : sub7 [3, -1, -5] = true := by decide +kernel
theorem sub7_1029 : sub7 [3, -1, -4] = true := by decide +kernel
theorem sub7_1030 : sub7 [3, -1, -3] = true := by decide +kernel
theorem sub7_1031 : sub7 [3, -1, -2] = true := by decide +kernel
theorem sub7_1032 : sub7 [3, -1, -1] = true := by decide +kernel
theorem sub7_1033 : sub7 [3, -1, 0] = true := by decide +kernel
theorem sub7_1034 : sub7 [3, -1, 1] = true := by decide +kernel
theorem sub7_1035 : sub7 [3, -1, 2] = true := by decide +kernel
theorem sub7_1036 : sub7 [3, -1, 3] = true := by decide +kernel
theorem sub7_1037 : sub7 [3, -1, 4] = true := by decide +kernel
theorem sub7_1038 : sub7 [3, -1, 5] = true := by decide +kernel
theorem sub7_1039 : sub7 [3, -1, 6] = true := by decide +kernel
theorem sub7_1040 : sub7 [3, -1, 7] = true := by decide +kernel
theorem sub7_1041 : sub7 [3, 0, -9] = true := by decide +kernel
theorem sub7_1042 : sub7 [3, 0, -8] = true := by decide +kernel
theorem sub7_1043 : sub7 [3, 0, -7] = true := by decide +kernel
theorem sub7_1044 : sub7 [3, 0, -6] = true := by decide +kernel
theorem sub7_1045 : sub7 [3, 0, -5] = true := by decide +kernel
theorem sub7_1046 : sub7 [3, 0, -4] = true := by decide +kernel
theorem sub7_1047 : sub7 [3, 0, -3] = true := by decide +kernel
theorem sub7_1048 : sub7 [3, 0, -2] = true := by decide +kernel
theorem sub7_1049 : sub7 [3, 0, -1] = true := by decide +kernel
theorem sub7_1050 : sub7 [3, 0, 0] = true := by decide +kernel
theorem sub7_1051 : sub7 [3, 0, 1] = true := by decide +kernel
theorem sub7_1052 : sub7 [3, 0, 2] = true := by decide +kernel
theorem sub7_1053 : sub7 [3, 0, 3] = true := by decide +kernel
theorem sub7_1054 : sub7 [3, 0, 4] = true := by decide +kernel
theorem sub7_1055 : sub7 [3, 0, 5] = true := by decide +kernel
theorem sb7_32 : ∀ q ∈ blk7_32, sub7 q = true := by
  unfold blk7_32
  exact List.forall_mem_cons.2 ⟨sub7_1024, List.forall_mem_cons.2 ⟨sub7_1025, List.forall_mem_cons.2 ⟨sub7_1026, List.forall_mem_cons.2 ⟨sub7_1027, List.forall_mem_cons.2 ⟨sub7_1028, List.forall_mem_cons.2 ⟨sub7_1029, List.forall_mem_cons.2 ⟨sub7_1030, List.forall_mem_cons.2 ⟨sub7_1031, List.forall_mem_cons.2 ⟨sub7_1032, List.forall_mem_cons.2 ⟨sub7_1033, List.forall_mem_cons.2 ⟨sub7_1034, List.forall_mem_cons.2 ⟨sub7_1035, List.forall_mem_cons.2 ⟨sub7_1036, List.forall_mem_cons.2 ⟨sub7_1037, List.forall_mem_cons.2 ⟨sub7_1038, List.forall_mem_cons.2 ⟨sub7_1039, List.forall_mem_cons.2 ⟨sub7_1040, List.forall_mem_cons.2 ⟨sub7_1041, List.forall_mem_cons.2 ⟨sub7_1042, List.forall_mem_cons.2 ⟨sub7_1043, List.forall_mem_cons.2 ⟨sub7_1044, List.forall_mem_cons.2 ⟨sub7_1045, List.forall_mem_cons.2 ⟨sub7_1046, List.forall_mem_cons.2 ⟨sub7_1047, List.forall_mem_cons.2 ⟨sub7_1048, List.forall_mem_cons.2 ⟨sub7_1049, List.forall_mem_cons.2 ⟨sub7_1050, List.forall_mem_cons.2 ⟨sub7_1051, List.forall_mem_cons.2 ⟨sub7_1052, List.forall_mem_cons.2 ⟨sub7_1053, List.forall_mem_cons.2 ⟨sub7_1054, List.forall_mem_cons.2 ⟨sub7_1055, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_1056 : sub7 [3, 0, 6] = true := by decide +kernel
theorem sub7_1057 : sub7 [3, 0, 7] = true := by decide +kernel
theorem sub7_1058 : sub7 [3, 1, -8] = true := by decide +kernel
theorem sub7_1059 : sub7 [3, 1, -7] = true := by decide +kernel
theorem sub7_1060 : sub7 [3, 1, -6] = true := by decide +kernel
theorem sub7_1061 : sub7 [3, 1, -5] = true := by decide +kernel
theorem sub7_1062 : sub7 [3, 1, -4] = true := by decide +kernel
theorem sub7_1063 : sub7 [3, 1, -3] = true := by decide +kernel
theorem sub7_1064 : sub7 [3, 1, -2] = true := by decide +kernel
theorem sub7_1065 : sub7 [3, 1, -1] = true := by decide +kernel
theorem sub7_1066 : sub7 [3, 1, 0] = true := by decide +kernel
theorem sub7_1067 : sub7 [3, 1, 1] = true := by decide +kernel
theorem sub7_1068 : sub7 [3, 1, 2] = true := by decide +kernel
theorem sub7_1069 : sub7 [3, 1, 3] = true := by decide +kernel
theorem sub7_1070 : sub7 [3, 1, 4] = true := by decide +kernel
theorem sub7_1071 : sub7 [3, 1, 5] = true := by decide +kernel
theorem sub7_1072 : sub7 [3, 1, 6] = true := by decide +kernel
theorem sub7_1073 : sub7 [3, 1, 7] = true := by decide +kernel
theorem sub7_1074 : sub7 [3, 2, -7] = true := by decide +kernel
theorem sub7_1075 : sub7 [3, 2, -6] = true := by decide +kernel
theorem sub7_1076 : sub7 [3, 2, -5] = true := by decide +kernel
theorem sub7_1077 : sub7 [3, 2, -4] = true := by decide +kernel
theorem sub7_1078 : sub7 [3, 2, -3] = true := by decide +kernel
theorem sub7_1079 : sub7 [3, 2, -2] = true := by decide +kernel
theorem sub7_1080 : sub7 [3, 2, -1] = true := by decide +kernel
theorem sub7_1081 : sub7 [3, 2, 0] = true := by decide +kernel
theorem sub7_1082 : sub7 [3, 2, 1] = true := by decide +kernel
theorem sub7_1083 : sub7 [3, 2, 2] = true := by decide +kernel
theorem sub7_1084 : sub7 [3, 2, 3] = true := by decide +kernel
theorem sub7_1085 : sub7 [3, 2, 4] = true := by decide +kernel
theorem sub7_1086 : sub7 [3, 2, 5] = true := by decide +kernel
theorem sub7_1087 : sub7 [3, 2, 6] = true := by decide +kernel
theorem sb7_33 : ∀ q ∈ blk7_33, sub7 q = true := by
  unfold blk7_33
  exact List.forall_mem_cons.2 ⟨sub7_1056, List.forall_mem_cons.2 ⟨sub7_1057, List.forall_mem_cons.2 ⟨sub7_1058, List.forall_mem_cons.2 ⟨sub7_1059, List.forall_mem_cons.2 ⟨sub7_1060, List.forall_mem_cons.2 ⟨sub7_1061, List.forall_mem_cons.2 ⟨sub7_1062, List.forall_mem_cons.2 ⟨sub7_1063, List.forall_mem_cons.2 ⟨sub7_1064, List.forall_mem_cons.2 ⟨sub7_1065, List.forall_mem_cons.2 ⟨sub7_1066, List.forall_mem_cons.2 ⟨sub7_1067, List.forall_mem_cons.2 ⟨sub7_1068, List.forall_mem_cons.2 ⟨sub7_1069, List.forall_mem_cons.2 ⟨sub7_1070, List.forall_mem_cons.2 ⟨sub7_1071, List.forall_mem_cons.2 ⟨sub7_1072, List.forall_mem_cons.2 ⟨sub7_1073, List.forall_mem_cons.2 ⟨sub7_1074, List.forall_mem_cons.2 ⟨sub7_1075, List.forall_mem_cons.2 ⟨sub7_1076, List.forall_mem_cons.2 ⟨sub7_1077, List.forall_mem_cons.2 ⟨sub7_1078, List.forall_mem_cons.2 ⟨sub7_1079, List.forall_mem_cons.2 ⟨sub7_1080, List.forall_mem_cons.2 ⟨sub7_1081, List.forall_mem_cons.2 ⟨sub7_1082, List.forall_mem_cons.2 ⟨sub7_1083, List.forall_mem_cons.2 ⟨sub7_1084, List.forall_mem_cons.2 ⟨sub7_1085, List.forall_mem_cons.2 ⟨sub7_1086, List.forall_mem_cons.2 ⟨sub7_1087, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_1088 : sub7 [3, 2, 7] = true := by decide +kernel
theorem sub7_1089 : sub7 [3, 3, -6] = true := by decide +kernel
theorem sub7_1090 : sub7 [3, 3, -5] = true := by decide +kernel
theorem sub7_1091 : sub7 [3, 3, -4] = true := by decide +kernel
theorem sub7_1092 : sub7 [3, 3, -3] = true := by decide +kernel
theorem sub7_1093 : sub7 [3, 3, -2] = true := by decide +kernel
theorem sub7_1094 : sub7 [3, 3, -1] = true := by decide +kernel
theorem sub7_1095 : sub7 [3, 3, 0] = true := by decide +kernel
theorem sub7_1096 : sub7 [3, 3, 1] = true := by decide +kernel
theorem sub7_1097 : sub7 [3, 3, 2] = true := by decide +kernel
theorem sub7_1098 : sub7 [3, 3, 3] = true := by decide +kernel
theorem sub7_1099 : sub7 [3, 3, 4] = true := by decide +kernel
theorem sub7_1100 : sub7 [3, 3, 5] = true := by decide +kernel
theorem sub7_1101 : sub7 [3, 3, 6] = true := by decide +kernel
theorem sub7_1102 : sub7 [3, 3, 7] = true := by decide +kernel
theorem sub7_1103 : sub7 [3, 4] = true := by decide +kernel
theorem sub7_1104 : sub7 [3, 5] = true := by decide +kernel
theorem sub7_1105 : sub7 [4, -6] = true := by decide +kernel
theorem sub7_1106 : sub7 [4, -5] = true := by decide +kernel
theorem sub7_1107 : sub7 [4, -4] = true := by decide +kernel
theorem sub7_1108 : sub7 [4, -3] = true := by decide +kernel
theorem sub7_1109 : sub7 [4, -2, -8] = true := by decide +kernel
theorem sub7_1110 : sub7 [4, -2, -7] = true := by decide +kernel
theorem sub7_1111 : sub7 [4, -2, -6] = true := by decide +kernel
theorem sub7_1112 : sub7 [4, -2, -5] = true := by decide +kernel
theorem sub7_1113 : sub7 [4, -2, -4] = true := by decide +kernel
theorem sub7_1114 : sub7 [4, -2, -3] = true := by decide +kernel
theorem sub7_1115 : sub7 [4, -2, -2] = true := by decide +kernel
theorem sub7_1116 : sub7 [4, -2, -1] = true := by decide +kernel
theorem sub7_1117 : sub7 [4, -2, 0] = true := by decide +kernel
theorem sub7_1118 : sub7 [4, -2, 1] = true := by decide +kernel
theorem sub7_1119 : sub7 [4, -2, 2] = true := by decide +kernel
theorem sb7_34 : ∀ q ∈ blk7_34, sub7 q = true := by
  unfold blk7_34
  exact List.forall_mem_cons.2 ⟨sub7_1088, List.forall_mem_cons.2 ⟨sub7_1089, List.forall_mem_cons.2 ⟨sub7_1090, List.forall_mem_cons.2 ⟨sub7_1091, List.forall_mem_cons.2 ⟨sub7_1092, List.forall_mem_cons.2 ⟨sub7_1093, List.forall_mem_cons.2 ⟨sub7_1094, List.forall_mem_cons.2 ⟨sub7_1095, List.forall_mem_cons.2 ⟨sub7_1096, List.forall_mem_cons.2 ⟨sub7_1097, List.forall_mem_cons.2 ⟨sub7_1098, List.forall_mem_cons.2 ⟨sub7_1099, List.forall_mem_cons.2 ⟨sub7_1100, List.forall_mem_cons.2 ⟨sub7_1101, List.forall_mem_cons.2 ⟨sub7_1102, List.forall_mem_cons.2 ⟨sub7_1103, List.forall_mem_cons.2 ⟨sub7_1104, List.forall_mem_cons.2 ⟨sub7_1105, List.forall_mem_cons.2 ⟨sub7_1106, List.forall_mem_cons.2 ⟨sub7_1107, List.forall_mem_cons.2 ⟨sub7_1108, List.forall_mem_cons.2 ⟨sub7_1109, List.forall_mem_cons.2 ⟨sub7_1110, List.forall_mem_cons.2 ⟨sub7_1111, List.forall_mem_cons.2 ⟨sub7_1112, List.forall_mem_cons.2 ⟨sub7_1113, List.forall_mem_cons.2 ⟨sub7_1114, List.forall_mem_cons.2 ⟨sub7_1115, List.forall_mem_cons.2 ⟨sub7_1116, List.forall_mem_cons.2 ⟨sub7_1117, List.forall_mem_cons.2 ⟨sub7_1118, List.forall_mem_cons.2 ⟨sub7_1119, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_1120 : sub7 [4, -2, 3] = true := by decide +kernel
theorem sub7_1121 : sub7 [4, -2, 4] = true := by decide +kernel
theorem sub7_1122 : sub7 [4, -2, 5] = true := by decide +kernel
theorem sub7_1123 : sub7 [4, -1, -8] = true := by decide +kernel
theorem sub7_1124 : sub7 [4, -1, -7] = true := by decide +kernel
theorem sub7_1125 : sub7 [4, -1, -6] = true := by decide +kernel
theorem sub7_1126 : sub7 [4, -1, -5] = true := by decide +kernel
theorem sub7_1127 : sub7 [4, -1, -4] = true := by decide +kernel
theorem sub7_1128 : sub7 [4, -1, -3] = true := by decide +kernel
theorem sub7_1129 : sub7 [4, -1, -2] = true := by decide +kernel
theorem sub7_1130 : sub7 [4, -1, -1] = true := by decide +kernel
theorem sub7_1131 : sub7 [4, -1, 0] = true := by decide +kernel
theorem sub7_1132 : sub7 [4, -1, 1] = true := by decide +kernel
theorem sub7_1133 : sub7 [4, -1, 2] = true := by decide +kernel
theorem sub7_1134 : sub7 [4, -1, 3] = true := by decide +kernel
theorem sub7_1135 : sub7 [4, -1, 4] = true := by decide +kernel
theorem sub7_1136 : sub7 [4, -1, 5] = true := by decide +kernel
theorem sub7_1137 : sub7 [4, -1, 6] = true := by decide +kernel
theorem sub7_1138 : sub7 [4, 0, -8] = true := by decide +kernel
theorem sub7_1139 : sub7 [4, 0, -7] = true := by decide +kernel
theorem sub7_1140 : sub7 [4, 0, -6] = true := by decide +kernel
theorem sub7_1141 : sub7 [4, 0, -5] = true := by decide +kernel
theorem sub7_1142 : sub7 [4, 0, -4] = true := by decide +kernel
theorem sub7_1143 : sub7 [4, 0, -3] = true := by decide +kernel
theorem sub7_1144 : sub7 [4, 0, -2] = true := by decide +kernel
theorem sub7_1145 : sub7 [4, 0, -1] = true := by decide +kernel
theorem sub7_1146 : sub7 [4, 0, 0] = true := by decide +kernel
theorem sub7_1147 : sub7 [4, 0, 1] = true := by decide +kernel
theorem sub7_1148 : sub7 [4, 0, 2] = true := by decide +kernel
theorem sub7_1149 : sub7 [4, 0, 3] = true := by decide +kernel
theorem sub7_1150 : sub7 [4, 0, 4] = true := by decide +kernel
theorem sub7_1151 : sub7 [4, 0, 5] = true := by decide +kernel
theorem sb7_35 : ∀ q ∈ blk7_35, sub7 q = true := by
  unfold blk7_35
  exact List.forall_mem_cons.2 ⟨sub7_1120, List.forall_mem_cons.2 ⟨sub7_1121, List.forall_mem_cons.2 ⟨sub7_1122, List.forall_mem_cons.2 ⟨sub7_1123, List.forall_mem_cons.2 ⟨sub7_1124, List.forall_mem_cons.2 ⟨sub7_1125, List.forall_mem_cons.2 ⟨sub7_1126, List.forall_mem_cons.2 ⟨sub7_1127, List.forall_mem_cons.2 ⟨sub7_1128, List.forall_mem_cons.2 ⟨sub7_1129, List.forall_mem_cons.2 ⟨sub7_1130, List.forall_mem_cons.2 ⟨sub7_1131, List.forall_mem_cons.2 ⟨sub7_1132, List.forall_mem_cons.2 ⟨sub7_1133, List.forall_mem_cons.2 ⟨sub7_1134, List.forall_mem_cons.2 ⟨sub7_1135, List.forall_mem_cons.2 ⟨sub7_1136, List.forall_mem_cons.2 ⟨sub7_1137, List.forall_mem_cons.2 ⟨sub7_1138, List.forall_mem_cons.2 ⟨sub7_1139, List.forall_mem_cons.2 ⟨sub7_1140, List.forall_mem_cons.2 ⟨sub7_1141, List.forall_mem_cons.2 ⟨sub7_1142, List.forall_mem_cons.2 ⟨sub7_1143, List.forall_mem_cons.2 ⟨sub7_1144, List.forall_mem_cons.2 ⟨sub7_1145, List.forall_mem_cons.2 ⟨sub7_1146, List.forall_mem_cons.2 ⟨sub7_1147, List.forall_mem_cons.2 ⟨sub7_1148, List.forall_mem_cons.2 ⟨sub7_1149, List.forall_mem_cons.2 ⟨sub7_1150, List.forall_mem_cons.2 ⟨sub7_1151, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_1152 : sub7 [4, 0, 6] = true := by decide +kernel
theorem sub7_1153 : sub7 [4, 1, -7] = true := by decide +kernel
theorem sub7_1154 : sub7 [4, 1, -6] = true := by decide +kernel
theorem sub7_1155 : sub7 [4, 1, -5] = true := by decide +kernel
theorem sub7_1156 : sub7 [4, 1, -4] = true := by decide +kernel
theorem sub7_1157 : sub7 [4, 1, -3] = true := by decide +kernel
theorem sub7_1158 : sub7 [4, 1, -2] = true := by decide +kernel
theorem sub7_1159 : sub7 [4, 1, -1] = true := by decide +kernel
theorem sub7_1160 : sub7 [4, 1, 0] = true := by decide +kernel
theorem sub7_1161 : sub7 [4, 1, 1] = true := by decide +kernel
theorem sub7_1162 : sub7 [4, 1, 2] = true := by decide +kernel
theorem sub7_1163 : sub7 [4, 1, 3] = true := by decide +kernel
theorem sub7_1164 : sub7 [4, 1, 4] = true := by decide +kernel
theorem sub7_1165 : sub7 [4, 1, 5] = true := by decide +kernel
theorem sub7_1166 : sub7 [4, 1, 6] = true := by decide +kernel
theorem sub7_1167 : sub7 [4, 2, -6] = true := by decide +kernel
theorem sub7_1168 : sub7 [4, 2, -5] = true := by decide +kernel
theorem sub7_1169 : sub7 [4, 2, -4] = true := by decide +kernel
theorem sub7_1170 : sub7 [4, 2, -3] = true := by decide +kernel
theorem sub7_1171 : sub7 [4, 2, -2] = true := by decide +kernel
theorem sub7_1172 : sub7 [4, 2, -1] = true := by decide +kernel
theorem sub7_1173 : sub7 [4, 2, 0] = true := by decide +kernel
theorem sub7_1174 : sub7 [4, 2, 1] = true := by decide +kernel
theorem sub7_1175 : sub7 [4, 2, 2] = true := by decide +kernel
theorem sub7_1176 : sub7 [4, 2, 3] = true := by decide +kernel
theorem sub7_1177 : sub7 [4, 2, 4] = true := by decide +kernel
theorem sub7_1178 : sub7 [4, 2, 5] = true := by decide +kernel
theorem sub7_1179 : sub7 [4, 2, 6] = true := by decide +kernel
theorem sub7_1180 : sub7 [4, 3] = true := by decide +kernel
theorem sub7_1181 : sub7 [4, 4] = true := by decide +kernel
theorem sub7_1182 : sub7 [4, 5] = true := by decide +kernel
theorem sub7_1183 : sub7 [5, -5] = true := by decide +kernel
theorem sb7_36 : ∀ q ∈ blk7_36, sub7 q = true := by
  unfold blk7_36
  exact List.forall_mem_cons.2 ⟨sub7_1152, List.forall_mem_cons.2 ⟨sub7_1153, List.forall_mem_cons.2 ⟨sub7_1154, List.forall_mem_cons.2 ⟨sub7_1155, List.forall_mem_cons.2 ⟨sub7_1156, List.forall_mem_cons.2 ⟨sub7_1157, List.forall_mem_cons.2 ⟨sub7_1158, List.forall_mem_cons.2 ⟨sub7_1159, List.forall_mem_cons.2 ⟨sub7_1160, List.forall_mem_cons.2 ⟨sub7_1161, List.forall_mem_cons.2 ⟨sub7_1162, List.forall_mem_cons.2 ⟨sub7_1163, List.forall_mem_cons.2 ⟨sub7_1164, List.forall_mem_cons.2 ⟨sub7_1165, List.forall_mem_cons.2 ⟨sub7_1166, List.forall_mem_cons.2 ⟨sub7_1167, List.forall_mem_cons.2 ⟨sub7_1168, List.forall_mem_cons.2 ⟨sub7_1169, List.forall_mem_cons.2 ⟨sub7_1170, List.forall_mem_cons.2 ⟨sub7_1171, List.forall_mem_cons.2 ⟨sub7_1172, List.forall_mem_cons.2 ⟨sub7_1173, List.forall_mem_cons.2 ⟨sub7_1174, List.forall_mem_cons.2 ⟨sub7_1175, List.forall_mem_cons.2 ⟨sub7_1176, List.forall_mem_cons.2 ⟨sub7_1177, List.forall_mem_cons.2 ⟨sub7_1178, List.forall_mem_cons.2 ⟨sub7_1179, List.forall_mem_cons.2 ⟨sub7_1180, List.forall_mem_cons.2 ⟨sub7_1181, List.forall_mem_cons.2 ⟨sub7_1182, List.forall_mem_cons.2 ⟨sub7_1183, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_1184 : sub7 [5, -4] = true := by decide +kernel
theorem sub7_1185 : sub7 [5, -3] = true := by decide +kernel
theorem sub7_1186 : sub7 [5, -2] = true := by decide +kernel
theorem sub7_1187 : sub7 [5, -1] = true := by decide +kernel
theorem sub7_1188 : sub7 [5, 0] = true := by decide +kernel
theorem sub7_1189 : sub7 [5, 1] = true := by decide +kernel
theorem sub7_1190 : sub7 [5, 2] = true := by decide +kernel
theorem sub7_1191 : sub7 [5, 3] = true := by decide +kernel
theorem sub7_1192 : sub7 [5, 4] = true := by decide +kernel
theorem sub7_1193 : sub7 [6, -3] = true := by decide +kernel
theorem sub7_1194 : sub7 [6, -2] = true := by decide +kernel
theorem sub7_1195 : sub7 [6, -1] = true := by decide +kernel
theorem sub7_1196 : sub7 [6, 0] = true := by decide +kernel
theorem sub7_1197 : sub7 [6, 1] = true := by decide +kernel
theorem sub7_1198 : sub7 [6, 2] = true := by decide +kernel
theorem sb7_37 : ∀ q ∈ blk7_37, sub7 q = true := by
  unfold blk7_37
  exact List.forall_mem_cons.2 ⟨sub7_1184, List.forall_mem_cons.2 ⟨sub7_1185, List.forall_mem_cons.2 ⟨sub7_1186, List.forall_mem_cons.2 ⟨sub7_1187, List.forall_mem_cons.2 ⟨sub7_1188, List.forall_mem_cons.2 ⟨sub7_1189, List.forall_mem_cons.2 ⟨sub7_1190, List.forall_mem_cons.2 ⟨sub7_1191, List.forall_mem_cons.2 ⟨sub7_1192, List.forall_mem_cons.2 ⟨sub7_1193, List.forall_mem_cons.2 ⟨sub7_1194, List.forall_mem_cons.2 ⟨sub7_1195, List.forall_mem_cons.2 ⟨sub7_1196, List.forall_mem_cons.2 ⟨sub7_1197, List.forall_mem_cons.2 ⟨sub7_1198, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_0 : sub8 [-5, -1] = true := by decide +kernel
theorem sub8_1 : sub8 [-5, 0] = true := by decide +kernel
theorem sub8_2 : sub8 [-5, 1] = true := by decide +kernel
theorem sub8_3 : sub8 [-5, 2] = true := by decide +kernel
theorem sub8_4 : sub8 [-5, 3] = true := by decide +kernel
theorem sub8_5 : sub8 [-5, 4] = true := by decide +kernel
theorem sub8_6 : sub8 [-4, -3] = true := by decide +kernel
theorem sub8_7 : sub8 [-4, -2] = true := by decide +kernel
theorem sub8_8 : sub8 [-4, -1] = true := by decide +kernel
theorem sub8_9 : sub8 [-4, 0] = true := by decide +kernel
theorem sub8_10 : sub8 [-4, 1] = true := by decide +kernel
theorem sub8_11 : sub8 [-4, 2] = true := by decide +kernel
theorem sub8_12 : sub8 [-4, 3] = true := by decide +kernel
theorem sub8_13 : sub8 [-4, 4] = true := by decide +kernel
theorem sub8_14 : sub8 [-4, 5] = true := by decide +kernel
theorem sub8_15 : sub8 [-4, 6] = true := by decide +kernel
theorem sub8_16 : sub8 [-3, -4] = true := by decide +kernel
theorem sub8_17 : sub8 [-3, -3] = true := by decide +kernel
theorem sub8_18 : sub8 [-3, -2] = true := by decide +kernel
theorem sub8_19 : sub8 [-3, -1] = true := by decide +kernel
theorem sub8_20 : sub8 [-3, 0] = true := by decide +kernel
theorem sub8_21 : sub8 [-3, 1, -6] = true := by decide +kernel
theorem sub8_22 : sub8 [-3, 1, -5] = true := by decide +kernel
theorem sub8_23 : sub8 [-3, 1, -4] = true := by decide +kernel
theorem sub8_24 : sub8 [-3, 1, -3] = true := by decide +kernel
theorem sub8_25 : sub8 [-3, 1, -2] = true := by decide +kernel
theorem sub8_26 : sub8 [-3, 1, -1] = true := by decide +kernel
theorem sub8_27 : sub8 [-3, 1, 0] = true := by decide +kernel
theorem sub8_28 : sub8 [-3, 1, 1] = true := by decide +kernel
theorem sub8_29 : sub8 [-3, 1, 2] = true := by decide +kernel
theorem sub8_30 : sub8 [-3, 1, 3] = true := by decide +kernel
theorem sub8_31 : sub8 [-3, 1, 4] = true := by decide +kernel
theorem sb8_0 : ∀ q ∈ blk8_0, sub8 q = true := by
  unfold blk8_0
  exact List.forall_mem_cons.2 ⟨sub8_0, List.forall_mem_cons.2 ⟨sub8_1, List.forall_mem_cons.2 ⟨sub8_2, List.forall_mem_cons.2 ⟨sub8_3, List.forall_mem_cons.2 ⟨sub8_4, List.forall_mem_cons.2 ⟨sub8_5, List.forall_mem_cons.2 ⟨sub8_6, List.forall_mem_cons.2 ⟨sub8_7, List.forall_mem_cons.2 ⟨sub8_8, List.forall_mem_cons.2 ⟨sub8_9, List.forall_mem_cons.2 ⟨sub8_10, List.forall_mem_cons.2 ⟨sub8_11, List.forall_mem_cons.2 ⟨sub8_12, List.forall_mem_cons.2 ⟨sub8_13, List.forall_mem_cons.2 ⟨sub8_14, List.forall_mem_cons.2 ⟨sub8_15, List.forall_mem_cons.2 ⟨sub8_16, List.forall_mem_cons.2 ⟨sub8_17, List.forall_mem_cons.2 ⟨sub8_18, List.forall_mem_cons.2 ⟨sub8_19, List.forall_mem_cons.2 ⟨sub8_20, List.forall_mem_cons.2 ⟨sub8_21, List.forall_mem_cons.2 ⟨sub8_22, List.forall_mem_cons.2 ⟨sub8_23, List.forall_mem_cons.2 ⟨sub8_24, List.forall_mem_cons.2 ⟨sub8_25, List.forall_mem_cons.2 ⟨sub8_26, List.forall_mem_cons.2 ⟨sub8_27, List.forall_mem_cons.2 ⟨sub8_28, List.forall_mem_cons.2 ⟨sub8_29, List.forall_mem_cons.2 ⟨sub8_30, List.forall_mem_cons.2 ⟨sub8_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_32 : sub8 [-3, 1, 5] = true := by decide +kernel
theorem sub8_33 : sub8 [-3, 1, 6] = true := by decide +kernel
theorem sub8_34 : sub8 [-3, 1, 7] = true := by decide +kernel
theorem sub8_35 : sub8 [-3, 2, -6] = true := by decide +kernel
theorem sub8_36 : sub8 [-3, 2, -5] = true := by decide +kernel
theorem sub8_37 : sub8 [-3, 2, -4] = true := by decide +kernel
theorem sub8_38 : sub8 [-3, 2, -3] = true := by decide +kernel
theorem sub8_39 : sub8 [-3, 2, -2] = true := by decide +kernel
theorem sub8_40 : sub8 [-3, 2, -1] = true := by decide +kernel
theorem sub8_41 : sub8 [-3, 2, 0] = true := by decide +kernel
theorem sub8_42 : sub8 [-3, 2, 1] = true := by decide +kernel
theorem sub8_43 : sub8 [-3, 2, 2] = true := by decide +kernel
theorem sub8_44 : sub8 [-3, 2, 3] = true := by decide +kernel
theorem sub8_45 : sub8 [-3, 2, 4] = true := by decide +kernel
theorem sub8_46 : sub8 [-3, 2, 5] = true := by decide +kernel
theorem sub8_47 : sub8 [-3, 2, 6] = true := by decide +kernel
theorem sub8_48 : sub8 [-3, 2, 7] = true := by decide +kernel
theorem sub8_49 : sub8 [-3, 3] = true := by decide +kernel
theorem sub8_50 : sub8 [-3, 4] = true := by decide +kernel
theorem sub8_51 : sub8 [-3, 5] = true := by decide +kernel
theorem sub8_52 : sub8 [-3, 6] = true := by decide +kernel
theorem sub8_53 : sub8 [-2, -5] = true := by decide +kernel
theorem sub8_54 : sub8 [-2, -4] = true := by decide +kernel
theorem sub8_55 : sub8 [-2, -3] = true := by decide +kernel
theorem sub8_56 : sub8 [-2, -2] = true := by decide +kernel
theorem sub8_57 : sub8 [-2, -1, -6] = true := by decide +kernel
theorem sub8_58 : sub8 [-2, -1, -5] = true := by decide +kernel
theorem sub8_59 : sub8 [-2, -1, -4] = true := by decide +kernel
theorem sub8_60 : sub8 [-2, -1, -3] = true := by decide +kernel
theorem sub8_61 : sub8 [-2, -1, -2] = true := by decide +kernel
theorem sub8_62 : sub8 [-2, -1, -1] = true := by decide +kernel
theorem sub8_63 : sub8 [-2, -1, 0] = true := by decide +kernel
theorem sb8_1 : ∀ q ∈ blk8_1, sub8 q = true := by
  unfold blk8_1
  exact List.forall_mem_cons.2 ⟨sub8_32, List.forall_mem_cons.2 ⟨sub8_33, List.forall_mem_cons.2 ⟨sub8_34, List.forall_mem_cons.2 ⟨sub8_35, List.forall_mem_cons.2 ⟨sub8_36, List.forall_mem_cons.2 ⟨sub8_37, List.forall_mem_cons.2 ⟨sub8_38, List.forall_mem_cons.2 ⟨sub8_39, List.forall_mem_cons.2 ⟨sub8_40, List.forall_mem_cons.2 ⟨sub8_41, List.forall_mem_cons.2 ⟨sub8_42, List.forall_mem_cons.2 ⟨sub8_43, List.forall_mem_cons.2 ⟨sub8_44, List.forall_mem_cons.2 ⟨sub8_45, List.forall_mem_cons.2 ⟨sub8_46, List.forall_mem_cons.2 ⟨sub8_47, List.forall_mem_cons.2 ⟨sub8_48, List.forall_mem_cons.2 ⟨sub8_49, List.forall_mem_cons.2 ⟨sub8_50, List.forall_mem_cons.2 ⟨sub8_51, List.forall_mem_cons.2 ⟨sub8_52, List.forall_mem_cons.2 ⟨sub8_53, List.forall_mem_cons.2 ⟨sub8_54, List.forall_mem_cons.2 ⟨sub8_55, List.forall_mem_cons.2 ⟨sub8_56, List.forall_mem_cons.2 ⟨sub8_57, List.forall_mem_cons.2 ⟨sub8_58, List.forall_mem_cons.2 ⟨sub8_59, List.forall_mem_cons.2 ⟨sub8_60, List.forall_mem_cons.2 ⟨sub8_61, List.forall_mem_cons.2 ⟨sub8_62, List.forall_mem_cons.2 ⟨sub8_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_64 : sub8 [-2, -1, 1] = true := by decide +kernel
theorem sub8_65 : sub8 [-2, -1, 2] = true := by decide +kernel
theorem sub8_66 : sub8 [-2, -1, 3] = true := by decide +kernel
theorem sub8_67 : sub8 [-2, -1, 4] = true := by decide +kernel
theorem sub8_68 : sub8 [-2, -1, 5] = true := by decide +kernel
theorem sub8_69 : sub8 [-2, -1, 6] = true := by decide +kernel
theorem sub8_70 : sub8 [-2, -1, 7] = true := by decide +kernel
theorem sub8_71 : sub8 [-2, 0, -7] = true := by decide +kernel
theorem sub8_72 : sub8 [-2, 0, -6] = true := by decide +kernel
theorem sub8_73 : sub8 [-2, 0, -5] = true := by decide +kernel
theorem sub8_74 : sub8 [-2, 0, -4] = true := by decide +kernel
theorem sub8_75 : sub8 [-2, 0, -3] = true := by decide +kernel
theorem sub8_76 : sub8 [-2, 0, -2] = true := by decide +kernel
theorem sub8_77 : sub8 [-2, 0, -1] = true := by decide +kernel
theorem sub8_78 : sub8 [-2, 0, 0] = true := by decide +kernel
theorem sub8_79 : sub8 [-2, 0, 1] = true := by decide +kernel
theorem sub8_80 : sub8 [-2, 0, 2] = true := by decide +kernel
theorem sub8_81 : sub8 [-2, 0, 3] = true := by decide +kernel
theorem sub8_82 : sub8 [-2, 0, 4] = true := by decide +kernel
theorem sub8_83 : sub8 [-2, 0, 5] = true := by decide +kernel
theorem sub8_84 : sub8 [-2, 0, 6] = true := by decide +kernel
theorem sub8_85 : sub8 [-2, 0, 7] = true := by decide +kernel
theorem sub8_86 : sub8 [-2, 1, -7] = true := by decide +kernel
theorem sub8_87 : sub8 [-2, 1, -6] = true := by decide +kernel
theorem sub8_88 : sub8 [-2, 1, -5] = true := by decide +kernel
theorem sub8_89 : sub8 [-2, 1, -4] = true := by decide +kernel
theorem sub8_90 : sub8 [-2, 1, -3] = true := by decide +kernel
theorem sub8_91 : sub8 [-2, 1, -2] = true := by decide +kernel
theorem sub8_92 : sub8 [-2, 1, -1] = true := by decide +kernel
theorem sub8_93 : sub8 [-2, 1, 0] = true := by decide +kernel
theorem sub8_94 : sub8 [-2, 1, 1] = true := by decide +kernel
theorem sub8_95 : sub8 [-2, 1, 2] = true := by decide +kernel
theorem sb8_2 : ∀ q ∈ blk8_2, sub8 q = true := by
  unfold blk8_2
  exact List.forall_mem_cons.2 ⟨sub8_64, List.forall_mem_cons.2 ⟨sub8_65, List.forall_mem_cons.2 ⟨sub8_66, List.forall_mem_cons.2 ⟨sub8_67, List.forall_mem_cons.2 ⟨sub8_68, List.forall_mem_cons.2 ⟨sub8_69, List.forall_mem_cons.2 ⟨sub8_70, List.forall_mem_cons.2 ⟨sub8_71, List.forall_mem_cons.2 ⟨sub8_72, List.forall_mem_cons.2 ⟨sub8_73, List.forall_mem_cons.2 ⟨sub8_74, List.forall_mem_cons.2 ⟨sub8_75, List.forall_mem_cons.2 ⟨sub8_76, List.forall_mem_cons.2 ⟨sub8_77, List.forall_mem_cons.2 ⟨sub8_78, List.forall_mem_cons.2 ⟨sub8_79, List.forall_mem_cons.2 ⟨sub8_80, List.forall_mem_cons.2 ⟨sub8_81, List.forall_mem_cons.2 ⟨sub8_82, List.forall_mem_cons.2 ⟨sub8_83, List.forall_mem_cons.2 ⟨sub8_84, List.forall_mem_cons.2 ⟨sub8_85, List.forall_mem_cons.2 ⟨sub8_86, List.forall_mem_cons.2 ⟨sub8_87, List.forall_mem_cons.2 ⟨sub8_88, List.forall_mem_cons.2 ⟨sub8_89, List.forall_mem_cons.2 ⟨sub8_90, List.forall_mem_cons.2 ⟨sub8_91, List.forall_mem_cons.2 ⟨sub8_92, List.forall_mem_cons.2 ⟨sub8_93, List.forall_mem_cons.2 ⟨sub8_94, List.forall_mem_cons.2 ⟨sub8_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_96 : sub8 [-2, 1, 3] = true := by decide +kernel
theorem sub8_97 : sub8 [-2, 1, 4] = true := by decide +kernel
theorem sub8_98 : sub8 [-2, 1, 5] = true := by decide +kernel
theorem sub8_99 : sub8 [-2, 1, 6] = true := by decide +kernel
theorem sub8_100 : sub8 [-2, 1, 7] = true := by decide +kernel
theorem sub8_101 : sub8 [-2, 2, -7] = true := by decide +kernel
theorem sub8_102 : sub8 [-2, 2, -6] = true := by decide +kernel
theorem sub8_103 : sub8 [-2, 2, -5] = true := by decide +kernel
theorem sub8_104 : sub8 [-2, 2, -4] = true := by decide +kernel
theorem sub8_105 : sub8 [-2, 2, -3] = true := by decide +kernel
theorem sub8_106 : sub8 [-2, 2, -2] = true := by decide +kernel
theorem sub8_107 : sub8 [-2, 2, -1] = true := by decide +kernel
theorem sub8_108 : sub8 [-2, 2, 0] = true := by decide +kernel
theorem sub8_109 : sub8 [-2, 2, 1] = true := by decide +kernel
theorem sub8_110 : sub8 [-2, 2, 2] = true := by decide +kernel
theorem sub8_111 : sub8 [-2, 2, 3] = true := by decide +kernel
theorem sub8_112 : sub8 [-2, 2, 4] = true := by decide +kernel
theorem sub8_113 : sub8 [-2, 2, 5] = true := by decide +kernel
theorem sub8_114 : sub8 [-2, 2, 6] = true := by decide +kernel
theorem sub8_115 : sub8 [-2, 2, 7] = true := by decide +kernel
theorem sub8_116 : sub8 [-2, 3, -6] = true := by decide +kernel
theorem sub8_117 : sub8 [-2, 3, -5] = true := by decide +kernel
theorem sub8_118 : sub8 [-2, 3, -4] = true := by decide +kernel
theorem sub8_119 : sub8 [-2, 3, -3] = true := by decide +kernel
theorem sub8_120 : sub8 [-2, 3, -2] = true := by decide +kernel
theorem sub8_121 : sub8 [-2, 3, -1] = true := by decide +kernel
theorem sub8_122 : sub8 [-2, 3, 0] = true := by decide +kernel
theorem sub8_123 : sub8 [-2, 3, 1] = true := by decide +kernel
theorem sub8_124 : sub8 [-2, 3, 2] = true := by decide +kernel
theorem sub8_125 : sub8 [-2, 3, 3] = true := by decide +kernel
theorem sub8_126 : sub8 [-2, 3, 4] = true := by decide +kernel
theorem sub8_127 : sub8 [-2, 3, 5] = true := by decide +kernel
theorem sb8_3 : ∀ q ∈ blk8_3, sub8 q = true := by
  unfold blk8_3
  exact List.forall_mem_cons.2 ⟨sub8_96, List.forall_mem_cons.2 ⟨sub8_97, List.forall_mem_cons.2 ⟨sub8_98, List.forall_mem_cons.2 ⟨sub8_99, List.forall_mem_cons.2 ⟨sub8_100, List.forall_mem_cons.2 ⟨sub8_101, List.forall_mem_cons.2 ⟨sub8_102, List.forall_mem_cons.2 ⟨sub8_103, List.forall_mem_cons.2 ⟨sub8_104, List.forall_mem_cons.2 ⟨sub8_105, List.forall_mem_cons.2 ⟨sub8_106, List.forall_mem_cons.2 ⟨sub8_107, List.forall_mem_cons.2 ⟨sub8_108, List.forall_mem_cons.2 ⟨sub8_109, List.forall_mem_cons.2 ⟨sub8_110, List.forall_mem_cons.2 ⟨sub8_111, List.forall_mem_cons.2 ⟨sub8_112, List.forall_mem_cons.2 ⟨sub8_113, List.forall_mem_cons.2 ⟨sub8_114, List.forall_mem_cons.2 ⟨sub8_115, List.forall_mem_cons.2 ⟨sub8_116, List.forall_mem_cons.2 ⟨sub8_117, List.forall_mem_cons.2 ⟨sub8_118, List.forall_mem_cons.2 ⟨sub8_119, List.forall_mem_cons.2 ⟨sub8_120, List.forall_mem_cons.2 ⟨sub8_121, List.forall_mem_cons.2 ⟨sub8_122, List.forall_mem_cons.2 ⟨sub8_123, List.forall_mem_cons.2 ⟨sub8_124, List.forall_mem_cons.2 ⟨sub8_125, List.forall_mem_cons.2 ⟨sub8_126, List.forall_mem_cons.2 ⟨sub8_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_128 : sub8 [-2, 3, 6] = true := by decide +kernel
theorem sub8_129 : sub8 [-2, 4] = true := by decide +kernel
theorem sub8_130 : sub8 [-2, 5] = true := by decide +kernel
theorem sub8_131 : sub8 [-2, 6] = true := by decide +kernel
theorem sub8_132 : sub8 [-1, -6] = true := by decide +kernel
theorem sub8_133 : sub8 [-1, -5] = true := by decide +kernel
theorem sub8_134 : sub8 [-1, -4] = true := by decide +kernel
theorem sub8_135 : sub8 [-1, -3] = true := by decide +kernel
theorem sub8_136 : sub8 [-1, -2, -7] = true := by decide +kernel
theorem sub8_137 : sub8 [-1, -2, -6] = true := by decide +kernel
theorem sub8_138 : sub8 [-1, -2, -5] = true := by decide +kernel
theorem sub8_139 : sub8 [-1, -2, -4] = true := by decide +kernel
theorem sub8_140 : sub8 [-1, -2, -3] = true := by decide +kernel
theorem sub8_141 : sub8 [-1, -2, -2] = true := by decide +kernel
theorem sub8_142 : sub8 [-1, -2, -1] = true := by decide +kernel
theorem sub8_143 : sub8 [-1, -2, 0] = true := by decide +kernel
theorem sub8_144 : sub8 [-1, -2, 1] = true := by decide +kernel
theorem sub8_145 : sub8 [-1, -2, 2] = true := by decide +kernel
theorem sub8_146 : sub8 [-1, -2, 3] = true := by decide +kernel
theorem sub8_147 : sub8 [-1, -2, 4] = true := by decide +kernel
theorem sub8_148 : sub8 [-1, -2, 5] = true := by decide +kernel
theorem sub8_149 : sub8 [-1, -2, 6] = true := by decide +kernel
theorem sub8_150 : sub8 [-1, -2, 7] = true := by decide +kernel
theorem sub8_151 : sub8 [-1, -1, -7] = true := by decide +kernel
theorem sub8_152 : sub8 [-1, -1, -6] = true := by decide +kernel
theorem sub8_153 : sub8 [-1, -1, -5] = true := by decide +kernel
theorem sub8_154 : sub8 [-1, -1, -4] = true := by decide +kernel
theorem sub8_155 : sub8 [-1, -1, -3] = true := by decide +kernel
theorem sub8_156 : sub8 [-1, -1, -2] = true := by decide +kernel
theorem sub8_157 : sub8 [-1, -1, -1] = true := by decide +kernel
theorem sub8_158 : sub8 [-1, -1, 0] = true := by decide +kernel
theorem sub8_159 : sub8 [-1, -1, 1] = true := by decide +kernel
theorem sb8_4 : ∀ q ∈ blk8_4, sub8 q = true := by
  unfold blk8_4
  exact List.forall_mem_cons.2 ⟨sub8_128, List.forall_mem_cons.2 ⟨sub8_129, List.forall_mem_cons.2 ⟨sub8_130, List.forall_mem_cons.2 ⟨sub8_131, List.forall_mem_cons.2 ⟨sub8_132, List.forall_mem_cons.2 ⟨sub8_133, List.forall_mem_cons.2 ⟨sub8_134, List.forall_mem_cons.2 ⟨sub8_135, List.forall_mem_cons.2 ⟨sub8_136, List.forall_mem_cons.2 ⟨sub8_137, List.forall_mem_cons.2 ⟨sub8_138, List.forall_mem_cons.2 ⟨sub8_139, List.forall_mem_cons.2 ⟨sub8_140, List.forall_mem_cons.2 ⟨sub8_141, List.forall_mem_cons.2 ⟨sub8_142, List.forall_mem_cons.2 ⟨sub8_143, List.forall_mem_cons.2 ⟨sub8_144, List.forall_mem_cons.2 ⟨sub8_145, List.forall_mem_cons.2 ⟨sub8_146, List.forall_mem_cons.2 ⟨sub8_147, List.forall_mem_cons.2 ⟨sub8_148, List.forall_mem_cons.2 ⟨sub8_149, List.forall_mem_cons.2 ⟨sub8_150, List.forall_mem_cons.2 ⟨sub8_151, List.forall_mem_cons.2 ⟨sub8_152, List.forall_mem_cons.2 ⟨sub8_153, List.forall_mem_cons.2 ⟨sub8_154, List.forall_mem_cons.2 ⟨sub8_155, List.forall_mem_cons.2 ⟨sub8_156, List.forall_mem_cons.2 ⟨sub8_157, List.forall_mem_cons.2 ⟨sub8_158, List.forall_mem_cons.2 ⟨sub8_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C125
