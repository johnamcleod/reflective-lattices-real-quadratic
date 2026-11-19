import ReflectZphi.Data.Cert5.C096.Base

namespace ReflectZphi.Data.Cert5.C096

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_2_1088 : subd7_2 [2, -3, -7] = true := by decide +kernel
theorem subd7_2_1089 : subd7_2 [2, -3, -6] = true := by decide +kernel
theorem subd7_2_1090 : subd7_2 [2, -3, -5] = true := by decide +kernel
theorem subd7_2_1091 : subd7_2 [2, -3, -4] = true := by decide +kernel
theorem subd7_2_1092 : subd7_2 [2, -3, -3] = true := by decide +kernel
theorem subd7_2_1093 : subd7_2 [2, -3, -2] = true := by decide +kernel
theorem subd7_2_1094 : subd7_2 [2, -3, -1] = true := by decide +kernel
theorem subd7_2_1095 : subd7_2 [2, -3, 0] = true := by decide +kernel
theorem subd7_2_1096 : subd7_2 [2, -3, 1] = true := by decide +kernel
theorem subd7_2_1097 : subd7_2 [2, -3, 2] = true := by decide +kernel
theorem subd7_2_1098 : subd7_2 [2, -3, 3] = true := by decide +kernel
theorem subd7_2_1099 : subd7_2 [2, -3, 4] = true := by decide +kernel
theorem subd7_2_1100 : subd7_2 [2, -3, 5] = true := by decide +kernel
theorem subd7_2_1101 : subd7_2 [2, -3, 6] = true := by decide +kernel
theorem subd7_2_1102 : subd7_2 [2, -3, 7] = true := by decide +kernel
theorem subd7_2_1103 : subd7_2 [2, -3, 8] = true := by decide +kernel
theorem subd7_2_1104 : subd7_2 [2, -3, 9] = true := by decide +kernel
theorem subd7_2_1105 : subd7_2 [2, -3, 10] = true := by decide +kernel
theorem subd7_2_1106 : subd7_2 [2, -3, 11] = true := by decide +kernel
theorem subd7_2_1107 : subd7_2 [2, -2, -16] = true := by decide +kernel
theorem subd7_2_1108 : subd7_2 [2, -2, -15] = true := by decide +kernel
theorem subd7_2_1109 : subd7_2 [2, -2, -14] = true := by decide +kernel
theorem subd7_2_1110 : subd7_2 [2, -2, -13] = true := by decide +kernel
theorem subd7_2_1111 : subd7_2 [2, -2, -12] = true := by decide +kernel
theorem subd7_2_1112 : subd7_2 [2, -2, -11] = true := by decide +kernel
theorem subd7_2_1113 : subd7_2 [2, -2, -10] = true := by decide +kernel
theorem subd7_2_1114 : subd7_2 [2, -2, -9] = true := by decide +kernel
theorem subd7_2_1115 : subd7_2 [2, -2, -8] = true := by decide +kernel
theorem subd7_2_1116 : subd7_2 [2, -2, -7] = true := by decide +kernel
theorem subd7_2_1117 : subd7_2 [2, -2, -6] = true := by decide +kernel
theorem subd7_2_1118 : subd7_2 [2, -2, -5] = true := by decide +kernel
theorem subd7_2_1119 : subd7_2 [2, -2, -4] = true := by decide +kernel
theorem sbd7_2_34 : ∀ q ∈ blkd7_2_34, subd7_2 q = true := by
  unfold blkd7_2_34
  exact List.forall_mem_cons.2 ⟨subd7_2_1088, List.forall_mem_cons.2 ⟨subd7_2_1089, List.forall_mem_cons.2 ⟨subd7_2_1090, List.forall_mem_cons.2 ⟨subd7_2_1091, List.forall_mem_cons.2 ⟨subd7_2_1092, List.forall_mem_cons.2 ⟨subd7_2_1093, List.forall_mem_cons.2 ⟨subd7_2_1094, List.forall_mem_cons.2 ⟨subd7_2_1095, List.forall_mem_cons.2 ⟨subd7_2_1096, List.forall_mem_cons.2 ⟨subd7_2_1097, List.forall_mem_cons.2 ⟨subd7_2_1098, List.forall_mem_cons.2 ⟨subd7_2_1099, List.forall_mem_cons.2 ⟨subd7_2_1100, List.forall_mem_cons.2 ⟨subd7_2_1101, List.forall_mem_cons.2 ⟨subd7_2_1102, List.forall_mem_cons.2 ⟨subd7_2_1103, List.forall_mem_cons.2 ⟨subd7_2_1104, List.forall_mem_cons.2 ⟨subd7_2_1105, List.forall_mem_cons.2 ⟨subd7_2_1106, List.forall_mem_cons.2 ⟨subd7_2_1107, List.forall_mem_cons.2 ⟨subd7_2_1108, List.forall_mem_cons.2 ⟨subd7_2_1109, List.forall_mem_cons.2 ⟨subd7_2_1110, List.forall_mem_cons.2 ⟨subd7_2_1111, List.forall_mem_cons.2 ⟨subd7_2_1112, List.forall_mem_cons.2 ⟨subd7_2_1113, List.forall_mem_cons.2 ⟨subd7_2_1114, List.forall_mem_cons.2 ⟨subd7_2_1115, List.forall_mem_cons.2 ⟨subd7_2_1116, List.forall_mem_cons.2 ⟨subd7_2_1117, List.forall_mem_cons.2 ⟨subd7_2_1118, List.forall_mem_cons.2 ⟨subd7_2_1119, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_1120 : subd7_2 [2, -2, -3] = true := by decide +kernel
theorem subd7_2_1121 : subd7_2 [2, -2, -2] = true := by decide +kernel
theorem subd7_2_1122 : subd7_2 [2, -2, -1] = true := by decide +kernel
theorem subd7_2_1123 : subd7_2 [2, -2, 0] = true := by decide +kernel
theorem subd7_2_1124 : subd7_2 [2, -2, 1] = true := by decide +kernel
theorem subd7_2_1125 : subd7_2 [2, -2, 2] = true := by decide +kernel
theorem subd7_2_1126 : subd7_2 [2, -2, 3] = true := by decide +kernel
theorem subd7_2_1127 : subd7_2 [2, -2, 4] = true := by decide +kernel
theorem subd7_2_1128 : subd7_2 [2, -2, 5] = true := by decide +kernel
theorem subd7_2_1129 : subd7_2 [2, -2, 6] = true := by decide +kernel
theorem subd7_2_1130 : subd7_2 [2, -2, 7] = true := by decide +kernel
theorem subd7_2_1131 : subd7_2 [2, -2, 8] = true := by decide +kernel
theorem subd7_2_1132 : subd7_2 [2, -2, 9] = true := by decide +kernel
theorem subd7_2_1133 : subd7_2 [2, -2, 10] = true := by decide +kernel
theorem subd7_2_1134 : subd7_2 [2, -2, 11] = true := by decide +kernel
theorem subd7_2_1135 : subd7_2 [2, -2, 12] = true := by decide +kernel
theorem subd7_2_1136 : subd7_2 [2, -2, 13] = true := by decide +kernel
theorem subd7_2_1137 : subd7_2 [2, -1, -16] = true := by decide +kernel
theorem subd7_2_1138 : subd7_2 [2, -1, -15] = true := by decide +kernel
theorem subd7_2_1139 : subd7_2 [2, -1, -14] = true := by decide +kernel
theorem subd7_2_1140 : subd7_2 [2, -1, -13] = true := by decide +kernel
theorem subd7_2_1141 : subd7_2 [2, -1, -12] = true := by decide +kernel
theorem subd7_2_1142 : subd7_2 [2, -1, -11] = true := by decide +kernel
theorem subd7_2_1143 : subd7_2 [2, -1, -10] = true := by decide +kernel
theorem subd7_2_1144 : subd7_2 [2, -1, -9] = true := by decide +kernel
theorem subd7_2_1145 : subd7_2 [2, -1, -8] = true := by decide +kernel
theorem subd7_2_1146 : subd7_2 [2, -1, -7] = true := by decide +kernel
theorem subd7_2_1147 : subd7_2 [2, -1, -6] = true := by decide +kernel
theorem subd7_2_1148 : subd7_2 [2, -1, -5] = true := by decide +kernel
theorem subd7_2_1149 : subd7_2 [2, -1, -4] = true := by decide +kernel
theorem subd7_2_1150 : subd7_2 [2, -1, -3] = true := by decide +kernel
theorem subd7_2_1151 : subd7_2 [2, -1, -2] = true := by decide +kernel
theorem sbd7_2_35 : ∀ q ∈ blkd7_2_35, subd7_2 q = true := by
  unfold blkd7_2_35
  exact List.forall_mem_cons.2 ⟨subd7_2_1120, List.forall_mem_cons.2 ⟨subd7_2_1121, List.forall_mem_cons.2 ⟨subd7_2_1122, List.forall_mem_cons.2 ⟨subd7_2_1123, List.forall_mem_cons.2 ⟨subd7_2_1124, List.forall_mem_cons.2 ⟨subd7_2_1125, List.forall_mem_cons.2 ⟨subd7_2_1126, List.forall_mem_cons.2 ⟨subd7_2_1127, List.forall_mem_cons.2 ⟨subd7_2_1128, List.forall_mem_cons.2 ⟨subd7_2_1129, List.forall_mem_cons.2 ⟨subd7_2_1130, List.forall_mem_cons.2 ⟨subd7_2_1131, List.forall_mem_cons.2 ⟨subd7_2_1132, List.forall_mem_cons.2 ⟨subd7_2_1133, List.forall_mem_cons.2 ⟨subd7_2_1134, List.forall_mem_cons.2 ⟨subd7_2_1135, List.forall_mem_cons.2 ⟨subd7_2_1136, List.forall_mem_cons.2 ⟨subd7_2_1137, List.forall_mem_cons.2 ⟨subd7_2_1138, List.forall_mem_cons.2 ⟨subd7_2_1139, List.forall_mem_cons.2 ⟨subd7_2_1140, List.forall_mem_cons.2 ⟨subd7_2_1141, List.forall_mem_cons.2 ⟨subd7_2_1142, List.forall_mem_cons.2 ⟨subd7_2_1143, List.forall_mem_cons.2 ⟨subd7_2_1144, List.forall_mem_cons.2 ⟨subd7_2_1145, List.forall_mem_cons.2 ⟨subd7_2_1146, List.forall_mem_cons.2 ⟨subd7_2_1147, List.forall_mem_cons.2 ⟨subd7_2_1148, List.forall_mem_cons.2 ⟨subd7_2_1149, List.forall_mem_cons.2 ⟨subd7_2_1150, List.forall_mem_cons.2 ⟨subd7_2_1151, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_1152 : subd7_2 [2, -1, -1] = true := by decide +kernel
theorem subd7_2_1153 : subd7_2 [2, -1, 0] = true := by decide +kernel
theorem subd7_2_1154 : subd7_2 [2, -1, 1] = true := by decide +kernel
theorem subd7_2_1155 : subd7_2 [2, -1, 2] = true := by decide +kernel
theorem subd7_2_1156 : subd7_2 [2, -1, 3] = true := by decide +kernel
theorem subd7_2_1157 : subd7_2 [2, -1, 4] = true := by decide +kernel
theorem subd7_2_1158 : subd7_2 [2, -1, 5] = true := by decide +kernel
theorem subd7_2_1159 : subd7_2 [2, -1, 6] = true := by decide +kernel
theorem subd7_2_1160 : subd7_2 [2, -1, 7] = true := by decide +kernel
theorem subd7_2_1161 : subd7_2 [2, -1, 8] = true := by decide +kernel
theorem subd7_2_1162 : subd7_2 [2, -1, 9] = true := by decide +kernel
theorem subd7_2_1163 : subd7_2 [2, -1, 10] = true := by decide +kernel
theorem subd7_2_1164 : subd7_2 [2, -1, 11] = true := by decide +kernel
theorem subd7_2_1165 : subd7_2 [2, -1, 12] = true := by decide +kernel
theorem subd7_2_1166 : subd7_2 [2, -1, 13] = true := by decide +kernel
theorem subd7_2_1167 : subd7_2 [2, -1, 14] = true := by decide +kernel
theorem subd7_2_1168 : subd7_2 [2, 0, -16] = true := by decide +kernel
theorem subd7_2_1169 : subd7_2 [2, 0, -15] = true := by decide +kernel
theorem subd7_2_1170 : subd7_2 [2, 0, -14] = true := by decide +kernel
theorem subd7_2_1171 : subd7_2 [2, 0, -13] = true := by decide +kernel
theorem subd7_2_1172 : subd7_2 [2, 0, -12] = true := by decide +kernel
theorem subd7_2_1173 : subd7_2 [2, 0, -11] = true := by decide +kernel
theorem subd7_2_1174 : subd7_2 [2, 0, -10] = true := by decide +kernel
theorem subd7_2_1175 : subd7_2 [2, 0, -9] = true := by decide +kernel
theorem subd7_2_1176 : subd7_2 [2, 0, -8] = true := by decide +kernel
theorem subd7_2_1177 : subd7_2 [2, 0, -7] = true := by decide +kernel
theorem subd7_2_1178 : subd7_2 [2, 0, -6] = true := by decide +kernel
theorem subd7_2_1179 : subd7_2 [2, 0, -5] = true := by decide +kernel
theorem subd7_2_1180 : subd7_2 [2, 0, -4] = true := by decide +kernel
theorem subd7_2_1181 : subd7_2 [2, 0, -3] = true := by decide +kernel
theorem subd7_2_1182 : subd7_2 [2, 0, -2] = true := by decide +kernel
theorem subd7_2_1183 : subd7_2 [2, 0, -1] = true := by decide +kernel
theorem sbd7_2_36 : ∀ q ∈ blkd7_2_36, subd7_2 q = true := by
  unfold blkd7_2_36
  exact List.forall_mem_cons.2 ⟨subd7_2_1152, List.forall_mem_cons.2 ⟨subd7_2_1153, List.forall_mem_cons.2 ⟨subd7_2_1154, List.forall_mem_cons.2 ⟨subd7_2_1155, List.forall_mem_cons.2 ⟨subd7_2_1156, List.forall_mem_cons.2 ⟨subd7_2_1157, List.forall_mem_cons.2 ⟨subd7_2_1158, List.forall_mem_cons.2 ⟨subd7_2_1159, List.forall_mem_cons.2 ⟨subd7_2_1160, List.forall_mem_cons.2 ⟨subd7_2_1161, List.forall_mem_cons.2 ⟨subd7_2_1162, List.forall_mem_cons.2 ⟨subd7_2_1163, List.forall_mem_cons.2 ⟨subd7_2_1164, List.forall_mem_cons.2 ⟨subd7_2_1165, List.forall_mem_cons.2 ⟨subd7_2_1166, List.forall_mem_cons.2 ⟨subd7_2_1167, List.forall_mem_cons.2 ⟨subd7_2_1168, List.forall_mem_cons.2 ⟨subd7_2_1169, List.forall_mem_cons.2 ⟨subd7_2_1170, List.forall_mem_cons.2 ⟨subd7_2_1171, List.forall_mem_cons.2 ⟨subd7_2_1172, List.forall_mem_cons.2 ⟨subd7_2_1173, List.forall_mem_cons.2 ⟨subd7_2_1174, List.forall_mem_cons.2 ⟨subd7_2_1175, List.forall_mem_cons.2 ⟨subd7_2_1176, List.forall_mem_cons.2 ⟨subd7_2_1177, List.forall_mem_cons.2 ⟨subd7_2_1178, List.forall_mem_cons.2 ⟨subd7_2_1179, List.forall_mem_cons.2 ⟨subd7_2_1180, List.forall_mem_cons.2 ⟨subd7_2_1181, List.forall_mem_cons.2 ⟨subd7_2_1182, List.forall_mem_cons.2 ⟨subd7_2_1183, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_1184 : subd7_2 [2, 0, 0] = true := by decide +kernel
theorem subd7_2_1185 : subd7_2 [2, 0, 1] = true := by decide +kernel
theorem subd7_2_1186 : subd7_2 [2, 0, 2] = true := by decide +kernel
theorem subd7_2_1187 : subd7_2 [2, 0, 3] = true := by decide +kernel
theorem subd7_2_1188 : subd7_2 [2, 0, 4] = true := by decide +kernel
theorem subd7_2_1189 : subd7_2 [2, 0, 5] = true := by decide +kernel
theorem subd7_2_1190 : subd7_2 [2, 0, 6] = true := by decide +kernel
theorem subd7_2_1191 : subd7_2 [2, 0, 7] = true := by decide +kernel
theorem subd7_2_1192 : subd7_2 [2, 0, 8] = true := by decide +kernel
theorem subd7_2_1193 : subd7_2 [2, 0, 9] = true := by decide +kernel
theorem subd7_2_1194 : subd7_2 [2, 0, 10] = true := by decide +kernel
theorem subd7_2_1195 : subd7_2 [2, 0, 11] = true := by decide +kernel
theorem subd7_2_1196 : subd7_2 [2, 0, 12] = true := by decide +kernel
theorem subd7_2_1197 : subd7_2 [2, 0, 13] = true := by decide +kernel
theorem subd7_2_1198 : subd7_2 [2, 1, -14] = true := by decide +kernel
theorem subd7_2_1199 : subd7_2 [2, 1, -13] = true := by decide +kernel
theorem subd7_2_1200 : subd7_2 [2, 1, -12] = true := by decide +kernel
theorem subd7_2_1201 : subd7_2 [2, 1, -11] = true := by decide +kernel
theorem subd7_2_1202 : subd7_2 [2, 1, -10] = true := by decide +kernel
theorem subd7_2_1203 : subd7_2 [2, 1, -9] = true := by decide +kernel
theorem subd7_2_1204 : subd7_2 [2, 1, -8] = true := by decide +kernel
theorem subd7_2_1205 : subd7_2 [2, 1, -7] = true := by decide +kernel
theorem subd7_2_1206 : subd7_2 [2, 1, -6] = true := by decide +kernel
theorem subd7_2_1207 : subd7_2 [2, 1, -5] = true := by decide +kernel
theorem subd7_2_1208 : subd7_2 [2, 1, -4] = true := by decide +kernel
theorem subd7_2_1209 : subd7_2 [2, 1, -3] = true := by decide +kernel
theorem subd7_2_1210 : subd7_2 [2, 1, -2] = true := by decide +kernel
theorem subd7_2_1211 : subd7_2 [2, 1, -1] = true := by decide +kernel
theorem subd7_2_1212 : subd7_2 [2, 1, 0] = true := by decide +kernel
theorem subd7_2_1213 : subd7_2 [2, 1, 1] = true := by decide +kernel
theorem subd7_2_1214 : subd7_2 [2, 1, 2] = true := by decide +kernel
theorem subd7_2_1215 : subd7_2 [2, 1, 3] = true := by decide +kernel
theorem sbd7_2_37 : ∀ q ∈ blkd7_2_37, subd7_2 q = true := by
  unfold blkd7_2_37
  exact List.forall_mem_cons.2 ⟨subd7_2_1184, List.forall_mem_cons.2 ⟨subd7_2_1185, List.forall_mem_cons.2 ⟨subd7_2_1186, List.forall_mem_cons.2 ⟨subd7_2_1187, List.forall_mem_cons.2 ⟨subd7_2_1188, List.forall_mem_cons.2 ⟨subd7_2_1189, List.forall_mem_cons.2 ⟨subd7_2_1190, List.forall_mem_cons.2 ⟨subd7_2_1191, List.forall_mem_cons.2 ⟨subd7_2_1192, List.forall_mem_cons.2 ⟨subd7_2_1193, List.forall_mem_cons.2 ⟨subd7_2_1194, List.forall_mem_cons.2 ⟨subd7_2_1195, List.forall_mem_cons.2 ⟨subd7_2_1196, List.forall_mem_cons.2 ⟨subd7_2_1197, List.forall_mem_cons.2 ⟨subd7_2_1198, List.forall_mem_cons.2 ⟨subd7_2_1199, List.forall_mem_cons.2 ⟨subd7_2_1200, List.forall_mem_cons.2 ⟨subd7_2_1201, List.forall_mem_cons.2 ⟨subd7_2_1202, List.forall_mem_cons.2 ⟨subd7_2_1203, List.forall_mem_cons.2 ⟨subd7_2_1204, List.forall_mem_cons.2 ⟨subd7_2_1205, List.forall_mem_cons.2 ⟨subd7_2_1206, List.forall_mem_cons.2 ⟨subd7_2_1207, List.forall_mem_cons.2 ⟨subd7_2_1208, List.forall_mem_cons.2 ⟨subd7_2_1209, List.forall_mem_cons.2 ⟨subd7_2_1210, List.forall_mem_cons.2 ⟨subd7_2_1211, List.forall_mem_cons.2 ⟨subd7_2_1212, List.forall_mem_cons.2 ⟨subd7_2_1213, List.forall_mem_cons.2 ⟨subd7_2_1214, List.forall_mem_cons.2 ⟨subd7_2_1215, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_1216 : subd7_2 [2, 1, 4] = true := by decide +kernel
theorem subd7_2_1217 : subd7_2 [2, 1, 5] = true := by decide +kernel
theorem subd7_2_1218 : subd7_2 [2, 1, 6] = true := by decide +kernel
theorem subd7_2_1219 : subd7_2 [2, 1, 7] = true := by decide +kernel
theorem subd7_2_1220 : subd7_2 [2, 1, 8] = true := by decide +kernel
theorem subd7_2_1221 : subd7_2 [2, 1, 9] = true := by decide +kernel
theorem subd7_2_1222 : subd7_2 [2, 1, 10] = true := by decide +kernel
theorem subd7_2_1223 : subd7_2 [2, 1, 11] = true := by decide +kernel
theorem subd7_2_1224 : subd7_2 [2, 1, 12] = true := by decide +kernel
theorem subd7_2_1225 : subd7_2 [2, 2, -11] = true := by decide +kernel
theorem subd7_2_1226 : subd7_2 [2, 2, -10] = true := by decide +kernel
theorem subd7_2_1227 : subd7_2 [2, 2, -9] = true := by decide +kernel
theorem subd7_2_1228 : subd7_2 [2, 2, -8] = true := by decide +kernel
theorem subd7_2_1229 : subd7_2 [2, 2, -7] = true := by decide +kernel
theorem subd7_2_1230 : subd7_2 [2, 2, -6] = true := by decide +kernel
theorem subd7_2_1231 : subd7_2 [2, 2, -5] = true := by decide +kernel
theorem subd7_2_1232 : subd7_2 [2, 2, -4] = true := by decide +kernel
theorem subd7_2_1233 : subd7_2 [2, 2, -3] = true := by decide +kernel
theorem subd7_2_1234 : subd7_2 [2, 2, -2] = true := by decide +kernel
theorem subd7_2_1235 : subd7_2 [2, 2, -1] = true := by decide +kernel
theorem subd7_2_1236 : subd7_2 [2, 2, 0] = true := by decide +kernel
theorem subd7_2_1237 : subd7_2 [2, 2, 1] = true := by decide +kernel
theorem subd7_2_1238 : subd7_2 [2, 2, 2] = true := by decide +kernel
theorem subd7_2_1239 : subd7_2 [2, 2, 3] = true := by decide +kernel
theorem subd7_2_1240 : subd7_2 [2, 2, 4] = true := by decide +kernel
theorem subd7_2_1241 : subd7_2 [2, 2, 5] = true := by decide +kernel
theorem subd7_2_1242 : subd7_2 [2, 2, 6] = true := by decide +kernel
theorem subd7_2_1243 : subd7_2 [2, 2, 7] = true := by decide +kernel
theorem subd7_2_1244 : subd7_2 [2, 2, 8] = true := by decide +kernel
theorem subd7_2_1245 : subd7_2 [2, 2, 9] = true := by decide +kernel
theorem subd7_2_1246 : subd7_2 [2, 2, 10] = true := by decide +kernel
theorem subd7_2_1247 : subd7_2 [2, 3] = true := by decide +kernel
theorem sbd7_2_38 : ∀ q ∈ blkd7_2_38, subd7_2 q = true := by
  unfold blkd7_2_38
  exact List.forall_mem_cons.2 ⟨subd7_2_1216, List.forall_mem_cons.2 ⟨subd7_2_1217, List.forall_mem_cons.2 ⟨subd7_2_1218, List.forall_mem_cons.2 ⟨subd7_2_1219, List.forall_mem_cons.2 ⟨subd7_2_1220, List.forall_mem_cons.2 ⟨subd7_2_1221, List.forall_mem_cons.2 ⟨subd7_2_1222, List.forall_mem_cons.2 ⟨subd7_2_1223, List.forall_mem_cons.2 ⟨subd7_2_1224, List.forall_mem_cons.2 ⟨subd7_2_1225, List.forall_mem_cons.2 ⟨subd7_2_1226, List.forall_mem_cons.2 ⟨subd7_2_1227, List.forall_mem_cons.2 ⟨subd7_2_1228, List.forall_mem_cons.2 ⟨subd7_2_1229, List.forall_mem_cons.2 ⟨subd7_2_1230, List.forall_mem_cons.2 ⟨subd7_2_1231, List.forall_mem_cons.2 ⟨subd7_2_1232, List.forall_mem_cons.2 ⟨subd7_2_1233, List.forall_mem_cons.2 ⟨subd7_2_1234, List.forall_mem_cons.2 ⟨subd7_2_1235, List.forall_mem_cons.2 ⟨subd7_2_1236, List.forall_mem_cons.2 ⟨subd7_2_1237, List.forall_mem_cons.2 ⟨subd7_2_1238, List.forall_mem_cons.2 ⟨subd7_2_1239, List.forall_mem_cons.2 ⟨subd7_2_1240, List.forall_mem_cons.2 ⟨subd7_2_1241, List.forall_mem_cons.2 ⟨subd7_2_1242, List.forall_mem_cons.2 ⟨subd7_2_1243, List.forall_mem_cons.2 ⟨subd7_2_1244, List.forall_mem_cons.2 ⟨subd7_2_1245, List.forall_mem_cons.2 ⟨subd7_2_1246, List.forall_mem_cons.2 ⟨subd7_2_1247, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_1248 : subd7_2 [3, -5] = true := by decide +kernel
theorem subd7_2_1249 : subd7_2 [3, -4, -10] = true := by decide +kernel
theorem subd7_2_1250 : subd7_2 [3, -4, -9] = true := by decide +kernel
theorem subd7_2_1251 : subd7_2 [3, -4, -8] = true := by decide +kernel
theorem subd7_2_1252 : subd7_2 [3, -4, -7] = true := by decide +kernel
theorem subd7_2_1253 : subd7_2 [3, -4, -6] = true := by decide +kernel
theorem subd7_2_1254 : subd7_2 [3, -4, -5] = true := by decide +kernel
theorem subd7_2_1255 : subd7_2 [3, -4, -4] = true := by decide +kernel
theorem subd7_2_1256 : subd7_2 [3, -4, -3] = true := by decide +kernel
theorem subd7_2_1257 : subd7_2 [3, -4, -2] = true := by decide +kernel
theorem subd7_2_1258 : subd7_2 [3, -4, -1] = true := by decide +kernel
theorem subd7_2_1259 : subd7_2 [3, -4, 0] = true := by decide +kernel
theorem subd7_2_1260 : subd7_2 [3, -4, 1] = true := by decide +kernel
theorem subd7_2_1261 : subd7_2 [3, -4, 2] = true := by decide +kernel
theorem subd7_2_1262 : subd7_2 [3, -4, 3] = true := by decide +kernel
theorem subd7_2_1263 : subd7_2 [3, -4, 4] = true := by decide +kernel
theorem subd7_2_1264 : subd7_2 [3, -4, 5] = true := by decide +kernel
theorem subd7_2_1265 : subd7_2 [3, -3, -13] = true := by decide +kernel
theorem subd7_2_1266 : subd7_2 [3, -3, -12] = true := by decide +kernel
theorem subd7_2_1267 : subd7_2 [3, -3, -11] = true := by decide +kernel
theorem subd7_2_1268 : subd7_2 [3, -3, -10] = true := by decide +kernel
theorem subd7_2_1269 : subd7_2 [3, -3, -9] = true := by decide +kernel
theorem subd7_2_1270 : subd7_2 [3, -3, -8] = true := by decide +kernel
theorem subd7_2_1271 : subd7_2 [3, -3, -7] = true := by decide +kernel
theorem subd7_2_1272 : subd7_2 [3, -3, -6] = true := by decide +kernel
theorem subd7_2_1273 : subd7_2 [3, -3, -5] = true := by decide +kernel
theorem subd7_2_1274 : subd7_2 [3, -3, -4] = true := by decide +kernel
theorem subd7_2_1275 : subd7_2 [3, -3, -3] = true := by decide +kernel
theorem subd7_2_1276 : subd7_2 [3, -3, -2] = true := by decide +kernel
theorem subd7_2_1277 : subd7_2 [3, -3, -1] = true := by decide +kernel
theorem subd7_2_1278 : subd7_2 [3, -3, 0] = true := by decide +kernel
theorem subd7_2_1279 : subd7_2 [3, -3, 1] = true := by decide +kernel
theorem sbd7_2_39 : ∀ q ∈ blkd7_2_39, subd7_2 q = true := by
  unfold blkd7_2_39
  exact List.forall_mem_cons.2 ⟨subd7_2_1248, List.forall_mem_cons.2 ⟨subd7_2_1249, List.forall_mem_cons.2 ⟨subd7_2_1250, List.forall_mem_cons.2 ⟨subd7_2_1251, List.forall_mem_cons.2 ⟨subd7_2_1252, List.forall_mem_cons.2 ⟨subd7_2_1253, List.forall_mem_cons.2 ⟨subd7_2_1254, List.forall_mem_cons.2 ⟨subd7_2_1255, List.forall_mem_cons.2 ⟨subd7_2_1256, List.forall_mem_cons.2 ⟨subd7_2_1257, List.forall_mem_cons.2 ⟨subd7_2_1258, List.forall_mem_cons.2 ⟨subd7_2_1259, List.forall_mem_cons.2 ⟨subd7_2_1260, List.forall_mem_cons.2 ⟨subd7_2_1261, List.forall_mem_cons.2 ⟨subd7_2_1262, List.forall_mem_cons.2 ⟨subd7_2_1263, List.forall_mem_cons.2 ⟨subd7_2_1264, List.forall_mem_cons.2 ⟨subd7_2_1265, List.forall_mem_cons.2 ⟨subd7_2_1266, List.forall_mem_cons.2 ⟨subd7_2_1267, List.forall_mem_cons.2 ⟨subd7_2_1268, List.forall_mem_cons.2 ⟨subd7_2_1269, List.forall_mem_cons.2 ⟨subd7_2_1270, List.forall_mem_cons.2 ⟨subd7_2_1271, List.forall_mem_cons.2 ⟨subd7_2_1272, List.forall_mem_cons.2 ⟨subd7_2_1273, List.forall_mem_cons.2 ⟨subd7_2_1274, List.forall_mem_cons.2 ⟨subd7_2_1275, List.forall_mem_cons.2 ⟨subd7_2_1276, List.forall_mem_cons.2 ⟨subd7_2_1277, List.forall_mem_cons.2 ⟨subd7_2_1278, List.forall_mem_cons.2 ⟨subd7_2_1279, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_1280 : subd7_2 [3, -3, 2] = true := by decide +kernel
theorem subd7_2_1281 : subd7_2 [3, -3, 3] = true := by decide +kernel
theorem subd7_2_1282 : subd7_2 [3, -3, 4] = true := by decide +kernel
theorem subd7_2_1283 : subd7_2 [3, -3, 5] = true := by decide +kernel
theorem subd7_2_1284 : subd7_2 [3, -3, 6] = true := by decide +kernel
theorem subd7_2_1285 : subd7_2 [3, -3, 7] = true := by decide +kernel
theorem subd7_2_1286 : subd7_2 [3, -3, 8] = true := by decide +kernel
theorem subd7_2_1287 : subd7_2 [3, -2, -14] = true := by decide +kernel
theorem subd7_2_1288 : subd7_2 [3, -2, -13] = true := by decide +kernel
theorem subd7_2_1289 : subd7_2 [3, -2, -12] = true := by decide +kernel
theorem subd7_2_1290 : subd7_2 [3, -2, -11] = true := by decide +kernel
theorem subd7_2_1291 : subd7_2 [3, -2, -10] = true := by decide +kernel
theorem subd7_2_1292 : subd7_2 [3, -2, -9] = true := by decide +kernel
theorem subd7_2_1293 : subd7_2 [3, -2, -8] = true := by decide +kernel
theorem subd7_2_1294 : subd7_2 [3, -2, -7] = true := by decide +kernel
theorem subd7_2_1295 : subd7_2 [3, -2, -6] = true := by decide +kernel
theorem subd7_2_1296 : subd7_2 [3, -2, -5] = true := by decide +kernel
theorem subd7_2_1297 : subd7_2 [3, -2, -4] = true := by decide +kernel
theorem subd7_2_1298 : subd7_2 [3, -2, -3] = true := by decide +kernel
theorem subd7_2_1299 : subd7_2 [3, -2, -2] = true := by decide +kernel
theorem subd7_2_1300 : subd7_2 [3, -2, -1] = true := by decide +kernel
theorem subd7_2_1301 : subd7_2 [3, -2, 0] = true := by decide +kernel
theorem subd7_2_1302 : subd7_2 [3, -2, 1] = true := by decide +kernel
theorem subd7_2_1303 : subd7_2 [3, -2, 2] = true := by decide +kernel
theorem subd7_2_1304 : subd7_2 [3, -2, 3] = true := by decide +kernel
theorem subd7_2_1305 : subd7_2 [3, -2, 4] = true := by decide +kernel
theorem subd7_2_1306 : subd7_2 [3, -2, 5] = true := by decide +kernel
theorem subd7_2_1307 : subd7_2 [3, -2, 6] = true := by decide +kernel
theorem subd7_2_1308 : subd7_2 [3, -2, 7] = true := by decide +kernel
theorem subd7_2_1309 : subd7_2 [3, -2, 8] = true := by decide +kernel
theorem subd7_2_1310 : subd7_2 [3, -2, 9] = true := by decide +kernel
theorem subd7_2_1311 : subd7_2 [3, -2, 10] = true := by decide +kernel
theorem sbd7_2_40 : ∀ q ∈ blkd7_2_40, subd7_2 q = true := by
  unfold blkd7_2_40
  exact List.forall_mem_cons.2 ⟨subd7_2_1280, List.forall_mem_cons.2 ⟨subd7_2_1281, List.forall_mem_cons.2 ⟨subd7_2_1282, List.forall_mem_cons.2 ⟨subd7_2_1283, List.forall_mem_cons.2 ⟨subd7_2_1284, List.forall_mem_cons.2 ⟨subd7_2_1285, List.forall_mem_cons.2 ⟨subd7_2_1286, List.forall_mem_cons.2 ⟨subd7_2_1287, List.forall_mem_cons.2 ⟨subd7_2_1288, List.forall_mem_cons.2 ⟨subd7_2_1289, List.forall_mem_cons.2 ⟨subd7_2_1290, List.forall_mem_cons.2 ⟨subd7_2_1291, List.forall_mem_cons.2 ⟨subd7_2_1292, List.forall_mem_cons.2 ⟨subd7_2_1293, List.forall_mem_cons.2 ⟨subd7_2_1294, List.forall_mem_cons.2 ⟨subd7_2_1295, List.forall_mem_cons.2 ⟨subd7_2_1296, List.forall_mem_cons.2 ⟨subd7_2_1297, List.forall_mem_cons.2 ⟨subd7_2_1298, List.forall_mem_cons.2 ⟨subd7_2_1299, List.forall_mem_cons.2 ⟨subd7_2_1300, List.forall_mem_cons.2 ⟨subd7_2_1301, List.forall_mem_cons.2 ⟨subd7_2_1302, List.forall_mem_cons.2 ⟨subd7_2_1303, List.forall_mem_cons.2 ⟨subd7_2_1304, List.forall_mem_cons.2 ⟨subd7_2_1305, List.forall_mem_cons.2 ⟨subd7_2_1306, List.forall_mem_cons.2 ⟨subd7_2_1307, List.forall_mem_cons.2 ⟨subd7_2_1308, List.forall_mem_cons.2 ⟨subd7_2_1309, List.forall_mem_cons.2 ⟨subd7_2_1310, List.forall_mem_cons.2 ⟨subd7_2_1311, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_1312 : subd7_2 [3, -1, -14] = true := by decide +kernel
theorem subd7_2_1313 : subd7_2 [3, -1, -13] = true := by decide +kernel
theorem subd7_2_1314 : subd7_2 [3, -1, -12] = true := by decide +kernel
theorem subd7_2_1315 : subd7_2 [3, -1, -11] = true := by decide +kernel
theorem subd7_2_1316 : subd7_2 [3, -1, -10] = true := by decide +kernel
theorem subd7_2_1317 : subd7_2 [3, -1, -9] = true := by decide +kernel
theorem subd7_2_1318 : subd7_2 [3, -1, -8] = true := by decide +kernel
theorem subd7_2_1319 : subd7_2 [3, -1, -7] = true := by decide +kernel
theorem subd7_2_1320 : subd7_2 [3, -1, -6] = true := by decide +kernel
theorem subd7_2_1321 : subd7_2 [3, -1, -5] = true := by decide +kernel
theorem subd7_2_1322 : subd7_2 [3, -1, -4] = true := by decide +kernel
theorem subd7_2_1323 : subd7_2 [3, -1, -3] = true := by decide +kernel
theorem subd7_2_1324 : subd7_2 [3, -1, -2] = true := by decide +kernel
theorem subd7_2_1325 : subd7_2 [3, -1, -1] = true := by decide +kernel
theorem subd7_2_1326 : subd7_2 [3, -1, 0] = true := by decide +kernel
theorem subd7_2_1327 : subd7_2 [3, -1, 1] = true := by decide +kernel
theorem subd7_2_1328 : subd7_2 [3, -1, 2] = true := by decide +kernel
theorem subd7_2_1329 : subd7_2 [3, -1, 3] = true := by decide +kernel
theorem subd7_2_1330 : subd7_2 [3, -1, 4] = true := by decide +kernel
theorem subd7_2_1331 : subd7_2 [3, -1, 5] = true := by decide +kernel
theorem subd7_2_1332 : subd7_2 [3, -1, 6] = true := by decide +kernel
theorem subd7_2_1333 : subd7_2 [3, -1, 7] = true := by decide +kernel
theorem subd7_2_1334 : subd7_2 [3, -1, 8] = true := by decide +kernel
theorem subd7_2_1335 : subd7_2 [3, -1, 9] = true := by decide +kernel
theorem subd7_2_1336 : subd7_2 [3, -1, 10] = true := by decide +kernel
theorem subd7_2_1337 : subd7_2 [3, 0, -12] = true := by decide +kernel
theorem subd7_2_1338 : subd7_2 [3, 0, -11] = true := by decide +kernel
theorem subd7_2_1339 : subd7_2 [3, 0, -10] = true := by decide +kernel
theorem subd7_2_1340 : subd7_2 [3, 0, -9] = true := by decide +kernel
theorem subd7_2_1341 : subd7_2 [3, 0, -8] = true := by decide +kernel
theorem subd7_2_1342 : subd7_2 [3, 0, -7] = true := by decide +kernel
theorem subd7_2_1343 : subd7_2 [3, 0, -6] = true := by decide +kernel
theorem sbd7_2_41 : ∀ q ∈ blkd7_2_41, subd7_2 q = true := by
  unfold blkd7_2_41
  exact List.forall_mem_cons.2 ⟨subd7_2_1312, List.forall_mem_cons.2 ⟨subd7_2_1313, List.forall_mem_cons.2 ⟨subd7_2_1314, List.forall_mem_cons.2 ⟨subd7_2_1315, List.forall_mem_cons.2 ⟨subd7_2_1316, List.forall_mem_cons.2 ⟨subd7_2_1317, List.forall_mem_cons.2 ⟨subd7_2_1318, List.forall_mem_cons.2 ⟨subd7_2_1319, List.forall_mem_cons.2 ⟨subd7_2_1320, List.forall_mem_cons.2 ⟨subd7_2_1321, List.forall_mem_cons.2 ⟨subd7_2_1322, List.forall_mem_cons.2 ⟨subd7_2_1323, List.forall_mem_cons.2 ⟨subd7_2_1324, List.forall_mem_cons.2 ⟨subd7_2_1325, List.forall_mem_cons.2 ⟨subd7_2_1326, List.forall_mem_cons.2 ⟨subd7_2_1327, List.forall_mem_cons.2 ⟨subd7_2_1328, List.forall_mem_cons.2 ⟨subd7_2_1329, List.forall_mem_cons.2 ⟨subd7_2_1330, List.forall_mem_cons.2 ⟨subd7_2_1331, List.forall_mem_cons.2 ⟨subd7_2_1332, List.forall_mem_cons.2 ⟨subd7_2_1333, List.forall_mem_cons.2 ⟨subd7_2_1334, List.forall_mem_cons.2 ⟨subd7_2_1335, List.forall_mem_cons.2 ⟨subd7_2_1336, List.forall_mem_cons.2 ⟨subd7_2_1337, List.forall_mem_cons.2 ⟨subd7_2_1338, List.forall_mem_cons.2 ⟨subd7_2_1339, List.forall_mem_cons.2 ⟨subd7_2_1340, List.forall_mem_cons.2 ⟨subd7_2_1341, List.forall_mem_cons.2 ⟨subd7_2_1342, List.forall_mem_cons.2 ⟨subd7_2_1343, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_1344 : subd7_2 [3, 0, -5] = true := by decide +kernel
theorem subd7_2_1345 : subd7_2 [3, 0, -4] = true := by decide +kernel
theorem subd7_2_1346 : subd7_2 [3, 0, -3] = true := by decide +kernel
theorem subd7_2_1347 : subd7_2 [3, 0, -2] = true := by decide +kernel
theorem subd7_2_1348 : subd7_2 [3, 0, -1] = true := by decide +kernel
theorem subd7_2_1349 : subd7_2 [3, 0, 0] = true := by decide +kernel
theorem subd7_2_1350 : subd7_2 [3, 0, 1] = true := by decide +kernel
theorem subd7_2_1351 : subd7_2 [3, 0, 2] = true := by decide +kernel
theorem subd7_2_1352 : subd7_2 [3, 0, 3] = true := by decide +kernel
theorem subd7_2_1353 : subd7_2 [3, 0, 4] = true := by decide +kernel
theorem subd7_2_1354 : subd7_2 [3, 0, 5] = true := by decide +kernel
theorem subd7_2_1355 : subd7_2 [3, 0, 6] = true := by decide +kernel
theorem subd7_2_1356 : subd7_2 [3, 0, 7] = true := by decide +kernel
theorem subd7_2_1357 : subd7_2 [3, 0, 8] = true := by decide +kernel
theorem subd7_2_1358 : subd7_2 [3, 0, 9] = true := by decide +kernel
theorem subd7_2_1359 : subd7_2 [3, 1, -10] = true := by decide +kernel
theorem subd7_2_1360 : subd7_2 [3, 1, -9] = true := by decide +kernel
theorem subd7_2_1361 : subd7_2 [3, 1, -8] = true := by decide +kernel
theorem subd7_2_1362 : subd7_2 [3, 1, -7] = true := by decide +kernel
theorem subd7_2_1363 : subd7_2 [3, 1, -6] = true := by decide +kernel
theorem subd7_2_1364 : subd7_2 [3, 1, -5] = true := by decide +kernel
theorem subd7_2_1365 : subd7_2 [3, 1, -4] = true := by decide +kernel
theorem subd7_2_1366 : subd7_2 [3, 1, -3] = true := by decide +kernel
theorem subd7_2_1367 : subd7_2 [3, 1, -2] = true := by decide +kernel
theorem subd7_2_1368 : subd7_2 [3, 1, -1] = true := by decide +kernel
theorem subd7_2_1369 : subd7_2 [3, 1, 0] = true := by decide +kernel
theorem subd7_2_1370 : subd7_2 [3, 1, 1] = true := by decide +kernel
theorem subd7_2_1371 : subd7_2 [3, 1, 2] = true := by decide +kernel
theorem subd7_2_1372 : subd7_2 [3, 1, 3] = true := by decide +kernel
theorem subd7_2_1373 : subd7_2 [3, 1, 4] = true := by decide +kernel
theorem subd7_2_1374 : subd7_2 [3, 1, 5] = true := by decide +kernel
theorem subd7_2_1375 : subd7_2 [3, 1, 6] = true := by decide +kernel
theorem sbd7_2_42 : ∀ q ∈ blkd7_2_42, subd7_2 q = true := by
  unfold blkd7_2_42
  exact List.forall_mem_cons.2 ⟨subd7_2_1344, List.forall_mem_cons.2 ⟨subd7_2_1345, List.forall_mem_cons.2 ⟨subd7_2_1346, List.forall_mem_cons.2 ⟨subd7_2_1347, List.forall_mem_cons.2 ⟨subd7_2_1348, List.forall_mem_cons.2 ⟨subd7_2_1349, List.forall_mem_cons.2 ⟨subd7_2_1350, List.forall_mem_cons.2 ⟨subd7_2_1351, List.forall_mem_cons.2 ⟨subd7_2_1352, List.forall_mem_cons.2 ⟨subd7_2_1353, List.forall_mem_cons.2 ⟨subd7_2_1354, List.forall_mem_cons.2 ⟨subd7_2_1355, List.forall_mem_cons.2 ⟨subd7_2_1356, List.forall_mem_cons.2 ⟨subd7_2_1357, List.forall_mem_cons.2 ⟨subd7_2_1358, List.forall_mem_cons.2 ⟨subd7_2_1359, List.forall_mem_cons.2 ⟨subd7_2_1360, List.forall_mem_cons.2 ⟨subd7_2_1361, List.forall_mem_cons.2 ⟨subd7_2_1362, List.forall_mem_cons.2 ⟨subd7_2_1363, List.forall_mem_cons.2 ⟨subd7_2_1364, List.forall_mem_cons.2 ⟨subd7_2_1365, List.forall_mem_cons.2 ⟨subd7_2_1366, List.forall_mem_cons.2 ⟨subd7_2_1367, List.forall_mem_cons.2 ⟨subd7_2_1368, List.forall_mem_cons.2 ⟨subd7_2_1369, List.forall_mem_cons.2 ⟨subd7_2_1370, List.forall_mem_cons.2 ⟨subd7_2_1371, List.forall_mem_cons.2 ⟨subd7_2_1372, List.forall_mem_cons.2 ⟨subd7_2_1373, List.forall_mem_cons.2 ⟨subd7_2_1374, List.forall_mem_cons.2 ⟨subd7_2_1375, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_1376 : subd7_2 [3, 1, 7] = true := by decide +kernel
theorem subd7_2_1377 : subd7_2 [4, -4] = true := by decide +kernel
theorem subd7_2_1378 : subd7_2 [4, -3] = true := by decide +kernel
theorem subd7_2_1379 : subd7_2 [4, -2] = true := by decide +kernel
theorem subd7_2_1380 : subd7_2 [4, -1] = true := by decide +kernel
theorem sbd7_2_43 : ∀ q ∈ blkd7_2_43, subd7_2 q = true := by
  unfold blkd7_2_43
  exact List.forall_mem_cons.2 ⟨subd7_2_1376, List.forall_mem_cons.2 ⟨subd7_2_1377, List.forall_mem_cons.2 ⟨subd7_2_1378, List.forall_mem_cons.2 ⟨subd7_2_1379, List.forall_mem_cons.2 ⟨subd7_2_1380, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd7_3 : ldCheck G d7_3.U d7_3.ms ldd7_3 = true := by decide +kernel
theorem pre_okd7_3 : subPre G cell7 d7_3 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C096
