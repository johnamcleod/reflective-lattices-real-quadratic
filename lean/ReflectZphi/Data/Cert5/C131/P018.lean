import ReflectZphi.Data.Cert5.C131.Base

namespace ReflectZphi.Data.Cert5.C131

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd11_0_1088 : subd11_0 [0, -1, 4] = true := by decide +kernel
theorem subd11_0_1089 : subd11_0 [0, -1, 5] = true := by decide +kernel
theorem subd11_0_1090 : subd11_0 [0, -1, 6] = true := by decide +kernel
theorem subd11_0_1091 : subd11_0 [0, -1, 7] = true := by decide +kernel
theorem subd11_0_1092 : subd11_0 [0, -1, 8] = true := by decide +kernel
theorem subd11_0_1093 : subd11_0 [0, 0, -9] = true := by decide +kernel
theorem subd11_0_1094 : subd11_0 [0, 0, -8] = true := by decide +kernel
theorem subd11_0_1095 : subd11_0 [0, 0, -7] = true := by decide +kernel
theorem subd11_0_1096 : subd11_0 [0, 0, -6] = true := by decide +kernel
theorem subd11_0_1097 : subd11_0 [0, 0, -5] = true := by decide +kernel
theorem subd11_0_1098 : subd11_0 [0, 0, -4] = true := by decide +kernel
theorem subd11_0_1099 : subd11_0 [0, 0, -3] = true := by decide +kernel
theorem subd11_0_1100 : subd11_0 [0, 0, -2] = true := by decide +kernel
theorem subd11_0_1101 : subd11_0 [0, 0, -1] = true := by decide +kernel
theorem subd11_0_1102 : subd11_0 [0, 0, 0] = true := by decide +kernel
theorem subd11_0_1103 : subd11_0 [0, 0, 1] = true := by decide +kernel
theorem subd11_0_1104 : subd11_0 [0, 0, 2] = true := by decide +kernel
theorem subd11_0_1105 : subd11_0 [0, 0, 3] = true := by decide +kernel
theorem subd11_0_1106 : subd11_0 [0, 0, 4] = true := by decide +kernel
theorem subd11_0_1107 : subd11_0 [0, 0, 5] = true := by decide +kernel
theorem subd11_0_1108 : subd11_0 [0, 0, 6] = true := by decide +kernel
theorem subd11_0_1109 : subd11_0 [0, 0, 7] = true := by decide +kernel
theorem subd11_0_1110 : subd11_0 [0, 0, 8] = true := by decide +kernel
theorem subd11_0_1111 : subd11_0 [0, 1, -9] = true := by decide +kernel
theorem subd11_0_1112 : subd11_0 [0, 1, -8] = true := by decide +kernel
theorem subd11_0_1113 : subd11_0 [0, 1, -7] = true := by decide +kernel
theorem subd11_0_1114 : subd11_0 [0, 1, -6] = true := by decide +kernel
theorem subd11_0_1115 : subd11_0 [0, 1, -5] = true := by decide +kernel
theorem subd11_0_1116 : subd11_0 [0, 1, -4] = true := by decide +kernel
theorem subd11_0_1117 : subd11_0 [0, 1, -3] = true := by decide +kernel
theorem subd11_0_1118 : subd11_0 [0, 1, -2] = true := by decide +kernel
theorem subd11_0_1119 : subd11_0 [0, 1, -1] = true := by decide +kernel
theorem sbd11_0_34 : ∀ q ∈ blkd11_0_34, subd11_0 q = true := by
  unfold blkd11_0_34
  exact List.forall_mem_cons.2 ⟨subd11_0_1088, List.forall_mem_cons.2 ⟨subd11_0_1089, List.forall_mem_cons.2 ⟨subd11_0_1090, List.forall_mem_cons.2 ⟨subd11_0_1091, List.forall_mem_cons.2 ⟨subd11_0_1092, List.forall_mem_cons.2 ⟨subd11_0_1093, List.forall_mem_cons.2 ⟨subd11_0_1094, List.forall_mem_cons.2 ⟨subd11_0_1095, List.forall_mem_cons.2 ⟨subd11_0_1096, List.forall_mem_cons.2 ⟨subd11_0_1097, List.forall_mem_cons.2 ⟨subd11_0_1098, List.forall_mem_cons.2 ⟨subd11_0_1099, List.forall_mem_cons.2 ⟨subd11_0_1100, List.forall_mem_cons.2 ⟨subd11_0_1101, List.forall_mem_cons.2 ⟨subd11_0_1102, List.forall_mem_cons.2 ⟨subd11_0_1103, List.forall_mem_cons.2 ⟨subd11_0_1104, List.forall_mem_cons.2 ⟨subd11_0_1105, List.forall_mem_cons.2 ⟨subd11_0_1106, List.forall_mem_cons.2 ⟨subd11_0_1107, List.forall_mem_cons.2 ⟨subd11_0_1108, List.forall_mem_cons.2 ⟨subd11_0_1109, List.forall_mem_cons.2 ⟨subd11_0_1110, List.forall_mem_cons.2 ⟨subd11_0_1111, List.forall_mem_cons.2 ⟨subd11_0_1112, List.forall_mem_cons.2 ⟨subd11_0_1113, List.forall_mem_cons.2 ⟨subd11_0_1114, List.forall_mem_cons.2 ⟨subd11_0_1115, List.forall_mem_cons.2 ⟨subd11_0_1116, List.forall_mem_cons.2 ⟨subd11_0_1117, List.forall_mem_cons.2 ⟨subd11_0_1118, List.forall_mem_cons.2 ⟨subd11_0_1119, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_1120 : subd11_0 [0, 1, 0] = true := by decide +kernel
theorem subd11_0_1121 : subd11_0 [0, 1, 1] = true := by decide +kernel
theorem subd11_0_1122 : subd11_0 [0, 1, 2] = true := by decide +kernel
theorem subd11_0_1123 : subd11_0 [0, 1, 3] = true := by decide +kernel
theorem subd11_0_1124 : subd11_0 [0, 1, 4] = true := by decide +kernel
theorem subd11_0_1125 : subd11_0 [0, 1, 5] = true := by decide +kernel
theorem subd11_0_1126 : subd11_0 [0, 1, 6] = true := by decide +kernel
theorem subd11_0_1127 : subd11_0 [0, 1, 7] = true := by decide +kernel
theorem subd11_0_1128 : subd11_0 [0, 1, 8] = true := by decide +kernel
theorem subd11_0_1129 : subd11_0 [0, 2, -9] = true := by decide +kernel
theorem subd11_0_1130 : subd11_0 [0, 2, -8] = true := by decide +kernel
theorem subd11_0_1131 : subd11_0 [0, 2, -7] = true := by decide +kernel
theorem subd11_0_1132 : subd11_0 [0, 2, -6] = true := by decide +kernel
theorem subd11_0_1133 : subd11_0 [0, 2, -5] = true := by decide +kernel
theorem subd11_0_1134 : subd11_0 [0, 2, -4] = true := by decide +kernel
theorem subd11_0_1135 : subd11_0 [0, 2, -3] = true := by decide +kernel
theorem subd11_0_1136 : subd11_0 [0, 2, -2] = true := by decide +kernel
theorem subd11_0_1137 : subd11_0 [0, 2, -1] = true := by decide +kernel
theorem subd11_0_1138 : subd11_0 [0, 2, 0] = true := by decide +kernel
theorem subd11_0_1139 : subd11_0 [0, 2, 1] = true := by decide +kernel
theorem subd11_0_1140 : subd11_0 [0, 2, 2] = true := by decide +kernel
theorem subd11_0_1141 : subd11_0 [0, 2, 3] = true := by decide +kernel
theorem subd11_0_1142 : subd11_0 [0, 2, 4] = true := by decide +kernel
theorem subd11_0_1143 : subd11_0 [0, 2, 5] = true := by decide +kernel
theorem subd11_0_1144 : subd11_0 [0, 2, 6] = true := by decide +kernel
theorem subd11_0_1145 : subd11_0 [0, 2, 7] = true := by decide +kernel
theorem subd11_0_1146 : subd11_0 [0, 2, 8] = true := by decide +kernel
theorem subd11_0_1147 : subd11_0 [0, 3, -9] = true := by decide +kernel
theorem subd11_0_1148 : subd11_0 [0, 3, -8] = true := by decide +kernel
theorem subd11_0_1149 : subd11_0 [0, 3, -7] = true := by decide +kernel
theorem subd11_0_1150 : subd11_0 [0, 3, -6] = true := by decide +kernel
theorem subd11_0_1151 : subd11_0 [0, 3, -5] = true := by decide +kernel
theorem sbd11_0_35 : ∀ q ∈ blkd11_0_35, subd11_0 q = true := by
  unfold blkd11_0_35
  exact List.forall_mem_cons.2 ⟨subd11_0_1120, List.forall_mem_cons.2 ⟨subd11_0_1121, List.forall_mem_cons.2 ⟨subd11_0_1122, List.forall_mem_cons.2 ⟨subd11_0_1123, List.forall_mem_cons.2 ⟨subd11_0_1124, List.forall_mem_cons.2 ⟨subd11_0_1125, List.forall_mem_cons.2 ⟨subd11_0_1126, List.forall_mem_cons.2 ⟨subd11_0_1127, List.forall_mem_cons.2 ⟨subd11_0_1128, List.forall_mem_cons.2 ⟨subd11_0_1129, List.forall_mem_cons.2 ⟨subd11_0_1130, List.forall_mem_cons.2 ⟨subd11_0_1131, List.forall_mem_cons.2 ⟨subd11_0_1132, List.forall_mem_cons.2 ⟨subd11_0_1133, List.forall_mem_cons.2 ⟨subd11_0_1134, List.forall_mem_cons.2 ⟨subd11_0_1135, List.forall_mem_cons.2 ⟨subd11_0_1136, List.forall_mem_cons.2 ⟨subd11_0_1137, List.forall_mem_cons.2 ⟨subd11_0_1138, List.forall_mem_cons.2 ⟨subd11_0_1139, List.forall_mem_cons.2 ⟨subd11_0_1140, List.forall_mem_cons.2 ⟨subd11_0_1141, List.forall_mem_cons.2 ⟨subd11_0_1142, List.forall_mem_cons.2 ⟨subd11_0_1143, List.forall_mem_cons.2 ⟨subd11_0_1144, List.forall_mem_cons.2 ⟨subd11_0_1145, List.forall_mem_cons.2 ⟨subd11_0_1146, List.forall_mem_cons.2 ⟨subd11_0_1147, List.forall_mem_cons.2 ⟨subd11_0_1148, List.forall_mem_cons.2 ⟨subd11_0_1149, List.forall_mem_cons.2 ⟨subd11_0_1150, List.forall_mem_cons.2 ⟨subd11_0_1151, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_1152 : subd11_0 [0, 3, -4] = true := by decide +kernel
theorem subd11_0_1153 : subd11_0 [0, 3, -3] = true := by decide +kernel
theorem subd11_0_1154 : subd11_0 [0, 3, -2] = true := by decide +kernel
theorem subd11_0_1155 : subd11_0 [0, 3, -1] = true := by decide +kernel
theorem subd11_0_1156 : subd11_0 [0, 3, 0] = true := by decide +kernel
theorem subd11_0_1157 : subd11_0 [0, 3, 1] = true := by decide +kernel
theorem subd11_0_1158 : subd11_0 [0, 3, 2] = true := by decide +kernel
theorem subd11_0_1159 : subd11_0 [0, 3, 3] = true := by decide +kernel
theorem subd11_0_1160 : subd11_0 [0, 3, 4] = true := by decide +kernel
theorem subd11_0_1161 : subd11_0 [0, 3, 5] = true := by decide +kernel
theorem subd11_0_1162 : subd11_0 [0, 3, 6] = true := by decide +kernel
theorem subd11_0_1163 : subd11_0 [0, 3, 7] = true := by decide +kernel
theorem subd11_0_1164 : subd11_0 [0, 3, 8] = true := by decide +kernel
theorem subd11_0_1165 : subd11_0 [0, 4, -9] = true := by decide +kernel
theorem subd11_0_1166 : subd11_0 [0, 4, -8] = true := by decide +kernel
theorem subd11_0_1167 : subd11_0 [0, 4, -7] = true := by decide +kernel
theorem subd11_0_1168 : subd11_0 [0, 4, -6] = true := by decide +kernel
theorem subd11_0_1169 : subd11_0 [0, 4, -5] = true := by decide +kernel
theorem subd11_0_1170 : subd11_0 [0, 4, -4] = true := by decide +kernel
theorem subd11_0_1171 : subd11_0 [0, 4, -3] = true := by decide +kernel
theorem subd11_0_1172 : subd11_0 [0, 4, -2] = true := by decide +kernel
theorem subd11_0_1173 : subd11_0 [0, 4, -1] = true := by decide +kernel
theorem subd11_0_1174 : subd11_0 [0, 4, 0] = true := by decide +kernel
theorem subd11_0_1175 : subd11_0 [0, 4, 1] = true := by decide +kernel
theorem subd11_0_1176 : subd11_0 [0, 4, 2] = true := by decide +kernel
theorem subd11_0_1177 : subd11_0 [0, 4, 3] = true := by decide +kernel
theorem subd11_0_1178 : subd11_0 [0, 4, 4] = true := by decide +kernel
theorem subd11_0_1179 : subd11_0 [0, 4, 5] = true := by decide +kernel
theorem subd11_0_1180 : subd11_0 [0, 4, 6] = true := by decide +kernel
theorem subd11_0_1181 : subd11_0 [0, 4, 7] = true := by decide +kernel
theorem subd11_0_1182 : subd11_0 [0, 5, -8] = true := by decide +kernel
theorem subd11_0_1183 : subd11_0 [0, 5, -7] = true := by decide +kernel
theorem sbd11_0_36 : ∀ q ∈ blkd11_0_36, subd11_0 q = true := by
  unfold blkd11_0_36
  exact List.forall_mem_cons.2 ⟨subd11_0_1152, List.forall_mem_cons.2 ⟨subd11_0_1153, List.forall_mem_cons.2 ⟨subd11_0_1154, List.forall_mem_cons.2 ⟨subd11_0_1155, List.forall_mem_cons.2 ⟨subd11_0_1156, List.forall_mem_cons.2 ⟨subd11_0_1157, List.forall_mem_cons.2 ⟨subd11_0_1158, List.forall_mem_cons.2 ⟨subd11_0_1159, List.forall_mem_cons.2 ⟨subd11_0_1160, List.forall_mem_cons.2 ⟨subd11_0_1161, List.forall_mem_cons.2 ⟨subd11_0_1162, List.forall_mem_cons.2 ⟨subd11_0_1163, List.forall_mem_cons.2 ⟨subd11_0_1164, List.forall_mem_cons.2 ⟨subd11_0_1165, List.forall_mem_cons.2 ⟨subd11_0_1166, List.forall_mem_cons.2 ⟨subd11_0_1167, List.forall_mem_cons.2 ⟨subd11_0_1168, List.forall_mem_cons.2 ⟨subd11_0_1169, List.forall_mem_cons.2 ⟨subd11_0_1170, List.forall_mem_cons.2 ⟨subd11_0_1171, List.forall_mem_cons.2 ⟨subd11_0_1172, List.forall_mem_cons.2 ⟨subd11_0_1173, List.forall_mem_cons.2 ⟨subd11_0_1174, List.forall_mem_cons.2 ⟨subd11_0_1175, List.forall_mem_cons.2 ⟨subd11_0_1176, List.forall_mem_cons.2 ⟨subd11_0_1177, List.forall_mem_cons.2 ⟨subd11_0_1178, List.forall_mem_cons.2 ⟨subd11_0_1179, List.forall_mem_cons.2 ⟨subd11_0_1180, List.forall_mem_cons.2 ⟨subd11_0_1181, List.forall_mem_cons.2 ⟨subd11_0_1182, List.forall_mem_cons.2 ⟨subd11_0_1183, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_1184 : subd11_0 [0, 5, -6] = true := by decide +kernel
theorem subd11_0_1185 : subd11_0 [0, 5, -5] = true := by decide +kernel
theorem subd11_0_1186 : subd11_0 [0, 5, -4] = true := by decide +kernel
theorem subd11_0_1187 : subd11_0 [0, 5, -3] = true := by decide +kernel
theorem subd11_0_1188 : subd11_0 [0, 5, -2] = true := by decide +kernel
theorem subd11_0_1189 : subd11_0 [0, 5, -1] = true := by decide +kernel
theorem subd11_0_1190 : subd11_0 [0, 5, 0] = true := by decide +kernel
theorem subd11_0_1191 : subd11_0 [0, 5, 1] = true := by decide +kernel
theorem subd11_0_1192 : subd11_0 [0, 5, 2] = true := by decide +kernel
theorem subd11_0_1193 : subd11_0 [0, 5, 3] = true := by decide +kernel
theorem subd11_0_1194 : subd11_0 [0, 5, 4] = true := by decide +kernel
theorem subd11_0_1195 : subd11_0 [0, 5, 5] = true := by decide +kernel
theorem subd11_0_1196 : subd11_0 [0, 5, 6] = true := by decide +kernel
theorem subd11_0_1197 : subd11_0 [0, 5, 7] = true := by decide +kernel
theorem subd11_0_1198 : subd11_0 [0, 6, -8] = true := by decide +kernel
theorem subd11_0_1199 : subd11_0 [0, 6, -7] = true := by decide +kernel
theorem subd11_0_1200 : subd11_0 [0, 6, -6] = true := by decide +kernel
theorem subd11_0_1201 : subd11_0 [0, 6, -5] = true := by decide +kernel
theorem subd11_0_1202 : subd11_0 [0, 6, -4] = true := by decide +kernel
theorem subd11_0_1203 : subd11_0 [0, 6, -3] = true := by decide +kernel
theorem subd11_0_1204 : subd11_0 [0, 6, -2] = true := by decide +kernel
theorem subd11_0_1205 : subd11_0 [0, 6, -1] = true := by decide +kernel
theorem subd11_0_1206 : subd11_0 [0, 6, 0] = true := by decide +kernel
theorem subd11_0_1207 : subd11_0 [0, 6, 1] = true := by decide +kernel
theorem subd11_0_1208 : subd11_0 [0, 6, 2] = true := by decide +kernel
theorem subd11_0_1209 : subd11_0 [0, 6, 3] = true := by decide +kernel
theorem subd11_0_1210 : subd11_0 [0, 6, 4] = true := by decide +kernel
theorem subd11_0_1211 : subd11_0 [0, 6, 5] = true := by decide +kernel
theorem subd11_0_1212 : subd11_0 [0, 6, 6] = true := by decide +kernel
theorem subd11_0_1213 : subd11_0 [0, 7] = true := by decide +kernel
theorem subd11_0_1214 : subd11_0 [0, 8] = true := by decide +kernel
theorem subd11_0_1215 : subd11_0 [0, 9] = true := by decide +kernel
theorem sbd11_0_37 : ∀ q ∈ blkd11_0_37, subd11_0 q = true := by
  unfold blkd11_0_37
  exact List.forall_mem_cons.2 ⟨subd11_0_1184, List.forall_mem_cons.2 ⟨subd11_0_1185, List.forall_mem_cons.2 ⟨subd11_0_1186, List.forall_mem_cons.2 ⟨subd11_0_1187, List.forall_mem_cons.2 ⟨subd11_0_1188, List.forall_mem_cons.2 ⟨subd11_0_1189, List.forall_mem_cons.2 ⟨subd11_0_1190, List.forall_mem_cons.2 ⟨subd11_0_1191, List.forall_mem_cons.2 ⟨subd11_0_1192, List.forall_mem_cons.2 ⟨subd11_0_1193, List.forall_mem_cons.2 ⟨subd11_0_1194, List.forall_mem_cons.2 ⟨subd11_0_1195, List.forall_mem_cons.2 ⟨subd11_0_1196, List.forall_mem_cons.2 ⟨subd11_0_1197, List.forall_mem_cons.2 ⟨subd11_0_1198, List.forall_mem_cons.2 ⟨subd11_0_1199, List.forall_mem_cons.2 ⟨subd11_0_1200, List.forall_mem_cons.2 ⟨subd11_0_1201, List.forall_mem_cons.2 ⟨subd11_0_1202, List.forall_mem_cons.2 ⟨subd11_0_1203, List.forall_mem_cons.2 ⟨subd11_0_1204, List.forall_mem_cons.2 ⟨subd11_0_1205, List.forall_mem_cons.2 ⟨subd11_0_1206, List.forall_mem_cons.2 ⟨subd11_0_1207, List.forall_mem_cons.2 ⟨subd11_0_1208, List.forall_mem_cons.2 ⟨subd11_0_1209, List.forall_mem_cons.2 ⟨subd11_0_1210, List.forall_mem_cons.2 ⟨subd11_0_1211, List.forall_mem_cons.2 ⟨subd11_0_1212, List.forall_mem_cons.2 ⟨subd11_0_1213, List.forall_mem_cons.2 ⟨subd11_0_1214, List.forall_mem_cons.2 ⟨subd11_0_1215, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_1216 : subd11_0 [1, -10] = true := by decide +kernel
theorem subd11_0_1217 : subd11_0 [1, -9] = true := by decide +kernel
theorem subd11_0_1218 : subd11_0 [1, -8] = true := by decide +kernel
theorem subd11_0_1219 : subd11_0 [1, -7] = true := by decide +kernel
theorem subd11_0_1220 : subd11_0 [1, -6, -6] = true := by decide +kernel
theorem subd11_0_1221 : subd11_0 [1, -6, -5] = true := by decide +kernel
theorem subd11_0_1222 : subd11_0 [1, -6, -4] = true := by decide +kernel
theorem subd11_0_1223 : subd11_0 [1, -6, -3] = true := by decide +kernel
theorem subd11_0_1224 : subd11_0 [1, -6, -2] = true := by decide +kernel
theorem subd11_0_1225 : subd11_0 [1, -6, -1] = true := by decide +kernel
theorem subd11_0_1226 : subd11_0 [1, -6, 0] = true := by decide +kernel
theorem subd11_0_1227 : subd11_0 [1, -6, 1] = true := by decide +kernel
theorem subd11_0_1228 : subd11_0 [1, -6, 2] = true := by decide +kernel
theorem subd11_0_1229 : subd11_0 [1, -6, 3] = true := by decide +kernel
theorem subd11_0_1230 : subd11_0 [1, -6, 4] = true := by decide +kernel
theorem subd11_0_1231 : subd11_0 [1, -6, 5] = true := by decide +kernel
theorem subd11_0_1232 : subd11_0 [1, -6, 6] = true := by decide +kernel
theorem subd11_0_1233 : subd11_0 [1, -5, -7] = true := by decide +kernel
theorem subd11_0_1234 : subd11_0 [1, -5, -6] = true := by decide +kernel
theorem subd11_0_1235 : subd11_0 [1, -5, -5] = true := by decide +kernel
theorem subd11_0_1236 : subd11_0 [1, -5, -4] = true := by decide +kernel
theorem subd11_0_1237 : subd11_0 [1, -5, -3] = true := by decide +kernel
theorem subd11_0_1238 : subd11_0 [1, -5, -2] = true := by decide +kernel
theorem subd11_0_1239 : subd11_0 [1, -5, -1] = true := by decide +kernel
theorem subd11_0_1240 : subd11_0 [1, -5, 0] = true := by decide +kernel
theorem subd11_0_1241 : subd11_0 [1, -5, 1] = true := by decide +kernel
theorem subd11_0_1242 : subd11_0 [1, -5, 2] = true := by decide +kernel
theorem subd11_0_1243 : subd11_0 [1, -5, 3] = true := by decide +kernel
theorem subd11_0_1244 : subd11_0 [1, -5, 4] = true := by decide +kernel
theorem subd11_0_1245 : subd11_0 [1, -5, 5] = true := by decide +kernel
theorem subd11_0_1246 : subd11_0 [1, -5, 6] = true := by decide +kernel
theorem subd11_0_1247 : subd11_0 [1, -5, 7] = true := by decide +kernel
theorem sbd11_0_38 : ∀ q ∈ blkd11_0_38, subd11_0 q = true := by
  unfold blkd11_0_38
  exact List.forall_mem_cons.2 ⟨subd11_0_1216, List.forall_mem_cons.2 ⟨subd11_0_1217, List.forall_mem_cons.2 ⟨subd11_0_1218, List.forall_mem_cons.2 ⟨subd11_0_1219, List.forall_mem_cons.2 ⟨subd11_0_1220, List.forall_mem_cons.2 ⟨subd11_0_1221, List.forall_mem_cons.2 ⟨subd11_0_1222, List.forall_mem_cons.2 ⟨subd11_0_1223, List.forall_mem_cons.2 ⟨subd11_0_1224, List.forall_mem_cons.2 ⟨subd11_0_1225, List.forall_mem_cons.2 ⟨subd11_0_1226, List.forall_mem_cons.2 ⟨subd11_0_1227, List.forall_mem_cons.2 ⟨subd11_0_1228, List.forall_mem_cons.2 ⟨subd11_0_1229, List.forall_mem_cons.2 ⟨subd11_0_1230, List.forall_mem_cons.2 ⟨subd11_0_1231, List.forall_mem_cons.2 ⟨subd11_0_1232, List.forall_mem_cons.2 ⟨subd11_0_1233, List.forall_mem_cons.2 ⟨subd11_0_1234, List.forall_mem_cons.2 ⟨subd11_0_1235, List.forall_mem_cons.2 ⟨subd11_0_1236, List.forall_mem_cons.2 ⟨subd11_0_1237, List.forall_mem_cons.2 ⟨subd11_0_1238, List.forall_mem_cons.2 ⟨subd11_0_1239, List.forall_mem_cons.2 ⟨subd11_0_1240, List.forall_mem_cons.2 ⟨subd11_0_1241, List.forall_mem_cons.2 ⟨subd11_0_1242, List.forall_mem_cons.2 ⟨subd11_0_1243, List.forall_mem_cons.2 ⟨subd11_0_1244, List.forall_mem_cons.2 ⟨subd11_0_1245, List.forall_mem_cons.2 ⟨subd11_0_1246, List.forall_mem_cons.2 ⟨subd11_0_1247, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_1248 : subd11_0 [1, -4, -8] = true := by decide +kernel
theorem subd11_0_1249 : subd11_0 [1, -4, -7] = true := by decide +kernel
theorem subd11_0_1250 : subd11_0 [1, -4, -6] = true := by decide +kernel
theorem subd11_0_1251 : subd11_0 [1, -4, -5] = true := by decide +kernel
theorem subd11_0_1252 : subd11_0 [1, -4, -4] = true := by decide +kernel
theorem subd11_0_1253 : subd11_0 [1, -4, -3] = true := by decide +kernel
theorem subd11_0_1254 : subd11_0 [1, -4, -2] = true := by decide +kernel
theorem subd11_0_1255 : subd11_0 [1, -4, -1] = true := by decide +kernel
theorem subd11_0_1256 : subd11_0 [1, -4, 0] = true := by decide +kernel
theorem subd11_0_1257 : subd11_0 [1, -4, 1] = true := by decide +kernel
theorem subd11_0_1258 : subd11_0 [1, -4, 2] = true := by decide +kernel
theorem subd11_0_1259 : subd11_0 [1, -4, 3] = true := by decide +kernel
theorem subd11_0_1260 : subd11_0 [1, -4, 4] = true := by decide +kernel
theorem subd11_0_1261 : subd11_0 [1, -4, 5] = true := by decide +kernel
theorem subd11_0_1262 : subd11_0 [1, -4, 6] = true := by decide +kernel
theorem subd11_0_1263 : subd11_0 [1, -4, 7] = true := by decide +kernel
theorem subd11_0_1264 : subd11_0 [1, -4, 8] = true := by decide +kernel
theorem subd11_0_1265 : subd11_0 [1, -3, -8] = true := by decide +kernel
theorem subd11_0_1266 : subd11_0 [1, -3, -7] = true := by decide +kernel
theorem subd11_0_1267 : subd11_0 [1, -3, -6] = true := by decide +kernel
theorem subd11_0_1268 : subd11_0 [1, -3, -5] = true := by decide +kernel
theorem subd11_0_1269 : subd11_0 [1, -3, -4] = true := by decide +kernel
theorem subd11_0_1270 : subd11_0 [1, -3, -3] = true := by decide +kernel
theorem subd11_0_1271 : subd11_0 [1, -3, -2] = true := by decide +kernel
theorem subd11_0_1272 : subd11_0 [1, -3, -1] = true := by decide +kernel
theorem subd11_0_1273 : subd11_0 [1, -3, 0] = true := by decide +kernel
theorem subd11_0_1274 : subd11_0 [1, -3, 1] = true := by decide +kernel
theorem subd11_0_1275 : subd11_0 [1, -3, 2] = true := by decide +kernel
theorem subd11_0_1276 : subd11_0 [1, -3, 3] = true := by decide +kernel
theorem subd11_0_1277 : subd11_0 [1, -3, 4] = true := by decide +kernel
theorem subd11_0_1278 : subd11_0 [1, -3, 5] = true := by decide +kernel
theorem subd11_0_1279 : subd11_0 [1, -3, 6] = true := by decide +kernel
theorem sbd11_0_39 : ∀ q ∈ blkd11_0_39, subd11_0 q = true := by
  unfold blkd11_0_39
  exact List.forall_mem_cons.2 ⟨subd11_0_1248, List.forall_mem_cons.2 ⟨subd11_0_1249, List.forall_mem_cons.2 ⟨subd11_0_1250, List.forall_mem_cons.2 ⟨subd11_0_1251, List.forall_mem_cons.2 ⟨subd11_0_1252, List.forall_mem_cons.2 ⟨subd11_0_1253, List.forall_mem_cons.2 ⟨subd11_0_1254, List.forall_mem_cons.2 ⟨subd11_0_1255, List.forall_mem_cons.2 ⟨subd11_0_1256, List.forall_mem_cons.2 ⟨subd11_0_1257, List.forall_mem_cons.2 ⟨subd11_0_1258, List.forall_mem_cons.2 ⟨subd11_0_1259, List.forall_mem_cons.2 ⟨subd11_0_1260, List.forall_mem_cons.2 ⟨subd11_0_1261, List.forall_mem_cons.2 ⟨subd11_0_1262, List.forall_mem_cons.2 ⟨subd11_0_1263, List.forall_mem_cons.2 ⟨subd11_0_1264, List.forall_mem_cons.2 ⟨subd11_0_1265, List.forall_mem_cons.2 ⟨subd11_0_1266, List.forall_mem_cons.2 ⟨subd11_0_1267, List.forall_mem_cons.2 ⟨subd11_0_1268, List.forall_mem_cons.2 ⟨subd11_0_1269, List.forall_mem_cons.2 ⟨subd11_0_1270, List.forall_mem_cons.2 ⟨subd11_0_1271, List.forall_mem_cons.2 ⟨subd11_0_1272, List.forall_mem_cons.2 ⟨subd11_0_1273, List.forall_mem_cons.2 ⟨subd11_0_1274, List.forall_mem_cons.2 ⟨subd11_0_1275, List.forall_mem_cons.2 ⟨subd11_0_1276, List.forall_mem_cons.2 ⟨subd11_0_1277, List.forall_mem_cons.2 ⟨subd11_0_1278, List.forall_mem_cons.2 ⟨subd11_0_1279, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_1280 : subd11_0 [1, -3, 7] = true := by decide +kernel
theorem subd11_0_1281 : subd11_0 [1, -3, 8] = true := by decide +kernel
theorem subd11_0_1282 : subd11_0 [1, -2, -9] = true := by decide +kernel
theorem subd11_0_1283 : subd11_0 [1, -2, -8] = true := by decide +kernel
theorem subd11_0_1284 : subd11_0 [1, -2, -7] = true := by decide +kernel
theorem subd11_0_1285 : subd11_0 [1, -2, -6] = true := by decide +kernel
theorem subd11_0_1286 : subd11_0 [1, -2, -5] = true := by decide +kernel
theorem subd11_0_1287 : subd11_0 [1, -2, -4] = true := by decide +kernel
theorem subd11_0_1288 : subd11_0 [1, -2, -3] = true := by decide +kernel
theorem subd11_0_1289 : subd11_0 [1, -2, -2] = true := by decide +kernel
theorem subd11_0_1290 : subd11_0 [1, -2, -1] = true := by decide +kernel
theorem subd11_0_1291 : subd11_0 [1, -2, 0] = true := by decide +kernel
theorem subd11_0_1292 : subd11_0 [1, -2, 1] = true := by decide +kernel
theorem subd11_0_1293 : subd11_0 [1, -2, 2] = true := by decide +kernel
theorem subd11_0_1294 : subd11_0 [1, -2, 3] = true := by decide +kernel
theorem subd11_0_1295 : subd11_0 [1, -2, 4] = true := by decide +kernel
theorem subd11_0_1296 : subd11_0 [1, -2, 5] = true := by decide +kernel
theorem subd11_0_1297 : subd11_0 [1, -2, 6] = true := by decide +kernel
theorem subd11_0_1298 : subd11_0 [1, -2, 7] = true := by decide +kernel
theorem subd11_0_1299 : subd11_0 [1, -2, 8] = true := by decide +kernel
theorem subd11_0_1300 : subd11_0 [1, -1, -9] = true := by decide +kernel
theorem subd11_0_1301 : subd11_0 [1, -1, -8] = true := by decide +kernel
theorem subd11_0_1302 : subd11_0 [1, -1, -7] = true := by decide +kernel
theorem subd11_0_1303 : subd11_0 [1, -1, -6] = true := by decide +kernel
theorem subd11_0_1304 : subd11_0 [1, -1, -5] = true := by decide +kernel
theorem subd11_0_1305 : subd11_0 [1, -1, -4] = true := by decide +kernel
theorem subd11_0_1306 : subd11_0 [1, -1, -3] = true := by decide +kernel
theorem subd11_0_1307 : subd11_0 [1, -1, -2] = true := by decide +kernel
theorem subd11_0_1308 : subd11_0 [1, -1, -1] = true := by decide +kernel
theorem subd11_0_1309 : subd11_0 [1, -1, 0] = true := by decide +kernel
theorem subd11_0_1310 : subd11_0 [1, -1, 1] = true := by decide +kernel
theorem subd11_0_1311 : subd11_0 [1, -1, 2] = true := by decide +kernel
theorem sbd11_0_40 : ∀ q ∈ blkd11_0_40, subd11_0 q = true := by
  unfold blkd11_0_40
  exact List.forall_mem_cons.2 ⟨subd11_0_1280, List.forall_mem_cons.2 ⟨subd11_0_1281, List.forall_mem_cons.2 ⟨subd11_0_1282, List.forall_mem_cons.2 ⟨subd11_0_1283, List.forall_mem_cons.2 ⟨subd11_0_1284, List.forall_mem_cons.2 ⟨subd11_0_1285, List.forall_mem_cons.2 ⟨subd11_0_1286, List.forall_mem_cons.2 ⟨subd11_0_1287, List.forall_mem_cons.2 ⟨subd11_0_1288, List.forall_mem_cons.2 ⟨subd11_0_1289, List.forall_mem_cons.2 ⟨subd11_0_1290, List.forall_mem_cons.2 ⟨subd11_0_1291, List.forall_mem_cons.2 ⟨subd11_0_1292, List.forall_mem_cons.2 ⟨subd11_0_1293, List.forall_mem_cons.2 ⟨subd11_0_1294, List.forall_mem_cons.2 ⟨subd11_0_1295, List.forall_mem_cons.2 ⟨subd11_0_1296, List.forall_mem_cons.2 ⟨subd11_0_1297, List.forall_mem_cons.2 ⟨subd11_0_1298, List.forall_mem_cons.2 ⟨subd11_0_1299, List.forall_mem_cons.2 ⟨subd11_0_1300, List.forall_mem_cons.2 ⟨subd11_0_1301, List.forall_mem_cons.2 ⟨subd11_0_1302, List.forall_mem_cons.2 ⟨subd11_0_1303, List.forall_mem_cons.2 ⟨subd11_0_1304, List.forall_mem_cons.2 ⟨subd11_0_1305, List.forall_mem_cons.2 ⟨subd11_0_1306, List.forall_mem_cons.2 ⟨subd11_0_1307, List.forall_mem_cons.2 ⟨subd11_0_1308, List.forall_mem_cons.2 ⟨subd11_0_1309, List.forall_mem_cons.2 ⟨subd11_0_1310, List.forall_mem_cons.2 ⟨subd11_0_1311, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_1312 : subd11_0 [1, -1, 3] = true := by decide +kernel
theorem subd11_0_1313 : subd11_0 [1, -1, 4] = true := by decide +kernel
theorem subd11_0_1314 : subd11_0 [1, -1, 5] = true := by decide +kernel
theorem subd11_0_1315 : subd11_0 [1, -1, 6] = true := by decide +kernel
theorem subd11_0_1316 : subd11_0 [1, -1, 7] = true := by decide +kernel
theorem subd11_0_1317 : subd11_0 [1, -1, 8] = true := by decide +kernel
theorem subd11_0_1318 : subd11_0 [1, 0, -9] = true := by decide +kernel
theorem subd11_0_1319 : subd11_0 [1, 0, -8] = true := by decide +kernel
theorem subd11_0_1320 : subd11_0 [1, 0, -7] = true := by decide +kernel
theorem subd11_0_1321 : subd11_0 [1, 0, -6] = true := by decide +kernel
theorem subd11_0_1322 : subd11_0 [1, 0, -5] = true := by decide +kernel
theorem subd11_0_1323 : subd11_0 [1, 0, -4] = true := by decide +kernel
theorem subd11_0_1324 : subd11_0 [1, 0, -3] = true := by decide +kernel
theorem subd11_0_1325 : subd11_0 [1, 0, -2] = true := by decide +kernel
theorem subd11_0_1326 : subd11_0 [1, 0, -1] = true := by decide +kernel
theorem subd11_0_1327 : subd11_0 [1, 0, 0] = true := by decide +kernel
theorem subd11_0_1328 : subd11_0 [1, 0, 1] = true := by decide +kernel
theorem subd11_0_1329 : subd11_0 [1, 0, 2] = true := by decide +kernel
theorem subd11_0_1330 : subd11_0 [1, 0, 3] = true := by decide +kernel
theorem subd11_0_1331 : subd11_0 [1, 0, 4] = true := by decide +kernel
theorem subd11_0_1332 : subd11_0 [1, 0, 5] = true := by decide +kernel
theorem subd11_0_1333 : subd11_0 [1, 0, 6] = true := by decide +kernel
theorem subd11_0_1334 : subd11_0 [1, 0, 7] = true := by decide +kernel
theorem subd11_0_1335 : subd11_0 [1, 0, 8] = true := by decide +kernel
theorem subd11_0_1336 : subd11_0 [1, 1, -9] = true := by decide +kernel
theorem subd11_0_1337 : subd11_0 [1, 1, -8] = true := by decide +kernel
theorem subd11_0_1338 : subd11_0 [1, 1, -7] = true := by decide +kernel
theorem subd11_0_1339 : subd11_0 [1, 1, -6] = true := by decide +kernel
theorem subd11_0_1340 : subd11_0 [1, 1, -5] = true := by decide +kernel
theorem subd11_0_1341 : subd11_0 [1, 1, -4] = true := by decide +kernel
theorem subd11_0_1342 : subd11_0 [1, 1, -3] = true := by decide +kernel
theorem subd11_0_1343 : subd11_0 [1, 1, -2] = true := by decide +kernel
theorem sbd11_0_41 : ∀ q ∈ blkd11_0_41, subd11_0 q = true := by
  unfold blkd11_0_41
  exact List.forall_mem_cons.2 ⟨subd11_0_1312, List.forall_mem_cons.2 ⟨subd11_0_1313, List.forall_mem_cons.2 ⟨subd11_0_1314, List.forall_mem_cons.2 ⟨subd11_0_1315, List.forall_mem_cons.2 ⟨subd11_0_1316, List.forall_mem_cons.2 ⟨subd11_0_1317, List.forall_mem_cons.2 ⟨subd11_0_1318, List.forall_mem_cons.2 ⟨subd11_0_1319, List.forall_mem_cons.2 ⟨subd11_0_1320, List.forall_mem_cons.2 ⟨subd11_0_1321, List.forall_mem_cons.2 ⟨subd11_0_1322, List.forall_mem_cons.2 ⟨subd11_0_1323, List.forall_mem_cons.2 ⟨subd11_0_1324, List.forall_mem_cons.2 ⟨subd11_0_1325, List.forall_mem_cons.2 ⟨subd11_0_1326, List.forall_mem_cons.2 ⟨subd11_0_1327, List.forall_mem_cons.2 ⟨subd11_0_1328, List.forall_mem_cons.2 ⟨subd11_0_1329, List.forall_mem_cons.2 ⟨subd11_0_1330, List.forall_mem_cons.2 ⟨subd11_0_1331, List.forall_mem_cons.2 ⟨subd11_0_1332, List.forall_mem_cons.2 ⟨subd11_0_1333, List.forall_mem_cons.2 ⟨subd11_0_1334, List.forall_mem_cons.2 ⟨subd11_0_1335, List.forall_mem_cons.2 ⟨subd11_0_1336, List.forall_mem_cons.2 ⟨subd11_0_1337, List.forall_mem_cons.2 ⟨subd11_0_1338, List.forall_mem_cons.2 ⟨subd11_0_1339, List.forall_mem_cons.2 ⟨subd11_0_1340, List.forall_mem_cons.2 ⟨subd11_0_1341, List.forall_mem_cons.2 ⟨subd11_0_1342, List.forall_mem_cons.2 ⟨subd11_0_1343, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_1344 : subd11_0 [1, 1, -1] = true := by decide +kernel
theorem subd11_0_1345 : subd11_0 [1, 1, 0] = true := by decide +kernel
theorem subd11_0_1346 : subd11_0 [1, 1, 1] = true := by decide +kernel
theorem subd11_0_1347 : subd11_0 [1, 1, 2] = true := by decide +kernel
theorem subd11_0_1348 : subd11_0 [1, 1, 3] = true := by decide +kernel
theorem subd11_0_1349 : subd11_0 [1, 1, 4] = true := by decide +kernel
theorem subd11_0_1350 : subd11_0 [1, 1, 5] = true := by decide +kernel
theorem subd11_0_1351 : subd11_0 [1, 1, 6] = true := by decide +kernel
theorem subd11_0_1352 : subd11_0 [1, 1, 7] = true := by decide +kernel
theorem subd11_0_1353 : subd11_0 [1, 1, 8] = true := by decide +kernel
theorem subd11_0_1354 : subd11_0 [1, 2, -9] = true := by decide +kernel
theorem subd11_0_1355 : subd11_0 [1, 2, -8] = true := by decide +kernel
theorem subd11_0_1356 : subd11_0 [1, 2, -7] = true := by decide +kernel
theorem subd11_0_1357 : subd11_0 [1, 2, -6] = true := by decide +kernel
theorem subd11_0_1358 : subd11_0 [1, 2, -5] = true := by decide +kernel
theorem subd11_0_1359 : subd11_0 [1, 2, -4] = true := by decide +kernel
theorem subd11_0_1360 : subd11_0 [1, 2, -3] = true := by decide +kernel
theorem subd11_0_1361 : subd11_0 [1, 2, -2] = true := by decide +kernel
theorem subd11_0_1362 : subd11_0 [1, 2, -1] = true := by decide +kernel
theorem subd11_0_1363 : subd11_0 [1, 2, 0] = true := by decide +kernel
theorem subd11_0_1364 : subd11_0 [1, 2, 1] = true := by decide +kernel
theorem subd11_0_1365 : subd11_0 [1, 2, 2] = true := by decide +kernel
theorem subd11_0_1366 : subd11_0 [1, 2, 3] = true := by decide +kernel
theorem subd11_0_1367 : subd11_0 [1, 2, 4] = true := by decide +kernel
theorem subd11_0_1368 : subd11_0 [1, 2, 5] = true := by decide +kernel
theorem subd11_0_1369 : subd11_0 [1, 2, 6] = true := by decide +kernel
theorem subd11_0_1370 : subd11_0 [1, 2, 7] = true := by decide +kernel
theorem subd11_0_1371 : subd11_0 [1, 2, 8] = true := by decide +kernel
theorem subd11_0_1372 : subd11_0 [1, 3, -9] = true := by decide +kernel
theorem subd11_0_1373 : subd11_0 [1, 3, -8] = true := by decide +kernel
theorem subd11_0_1374 : subd11_0 [1, 3, -7] = true := by decide +kernel
theorem subd11_0_1375 : subd11_0 [1, 3, -6] = true := by decide +kernel
theorem sbd11_0_42 : ∀ q ∈ blkd11_0_42, subd11_0 q = true := by
  unfold blkd11_0_42
  exact List.forall_mem_cons.2 ⟨subd11_0_1344, List.forall_mem_cons.2 ⟨subd11_0_1345, List.forall_mem_cons.2 ⟨subd11_0_1346, List.forall_mem_cons.2 ⟨subd11_0_1347, List.forall_mem_cons.2 ⟨subd11_0_1348, List.forall_mem_cons.2 ⟨subd11_0_1349, List.forall_mem_cons.2 ⟨subd11_0_1350, List.forall_mem_cons.2 ⟨subd11_0_1351, List.forall_mem_cons.2 ⟨subd11_0_1352, List.forall_mem_cons.2 ⟨subd11_0_1353, List.forall_mem_cons.2 ⟨subd11_0_1354, List.forall_mem_cons.2 ⟨subd11_0_1355, List.forall_mem_cons.2 ⟨subd11_0_1356, List.forall_mem_cons.2 ⟨subd11_0_1357, List.forall_mem_cons.2 ⟨subd11_0_1358, List.forall_mem_cons.2 ⟨subd11_0_1359, List.forall_mem_cons.2 ⟨subd11_0_1360, List.forall_mem_cons.2 ⟨subd11_0_1361, List.forall_mem_cons.2 ⟨subd11_0_1362, List.forall_mem_cons.2 ⟨subd11_0_1363, List.forall_mem_cons.2 ⟨subd11_0_1364, List.forall_mem_cons.2 ⟨subd11_0_1365, List.forall_mem_cons.2 ⟨subd11_0_1366, List.forall_mem_cons.2 ⟨subd11_0_1367, List.forall_mem_cons.2 ⟨subd11_0_1368, List.forall_mem_cons.2 ⟨subd11_0_1369, List.forall_mem_cons.2 ⟨subd11_0_1370, List.forall_mem_cons.2 ⟨subd11_0_1371, List.forall_mem_cons.2 ⟨subd11_0_1372, List.forall_mem_cons.2 ⟨subd11_0_1373, List.forall_mem_cons.2 ⟨subd11_0_1374, List.forall_mem_cons.2 ⟨subd11_0_1375, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_1376 : subd11_0 [1, 3, -5] = true := by decide +kernel
theorem subd11_0_1377 : subd11_0 [1, 3, -4] = true := by decide +kernel
theorem subd11_0_1378 : subd11_0 [1, 3, -3] = true := by decide +kernel
theorem subd11_0_1379 : subd11_0 [1, 3, -2] = true := by decide +kernel
theorem subd11_0_1380 : subd11_0 [1, 3, -1] = true := by decide +kernel
theorem subd11_0_1381 : subd11_0 [1, 3, 0] = true := by decide +kernel
theorem subd11_0_1382 : subd11_0 [1, 3, 1] = true := by decide +kernel
theorem subd11_0_1383 : subd11_0 [1, 3, 2] = true := by decide +kernel
theorem subd11_0_1384 : subd11_0 [1, 3, 3] = true := by decide +kernel
theorem subd11_0_1385 : subd11_0 [1, 3, 4] = true := by decide +kernel
theorem subd11_0_1386 : subd11_0 [1, 3, 5] = true := by decide +kernel
theorem subd11_0_1387 : subd11_0 [1, 3, 6] = true := by decide +kernel
theorem subd11_0_1388 : subd11_0 [1, 3, 7] = true := by decide +kernel
theorem subd11_0_1389 : subd11_0 [1, 3, 8] = true := by decide +kernel
theorem subd11_0_1390 : subd11_0 [1, 4, -8] = true := by decide +kernel
theorem subd11_0_1391 : subd11_0 [1, 4, -7] = true := by decide +kernel
theorem subd11_0_1392 : subd11_0 [1, 4, -6] = true := by decide +kernel
theorem subd11_0_1393 : subd11_0 [1, 4, -5] = true := by decide +kernel
theorem subd11_0_1394 : subd11_0 [1, 4, -4] = true := by decide +kernel
theorem subd11_0_1395 : subd11_0 [1, 4, -3] = true := by decide +kernel
theorem subd11_0_1396 : subd11_0 [1, 4, -2] = true := by decide +kernel
theorem subd11_0_1397 : subd11_0 [1, 4, -1] = true := by decide +kernel
theorem subd11_0_1398 : subd11_0 [1, 4, 0] = true := by decide +kernel
theorem subd11_0_1399 : subd11_0 [1, 4, 1] = true := by decide +kernel
theorem subd11_0_1400 : subd11_0 [1, 4, 2] = true := by decide +kernel
theorem subd11_0_1401 : subd11_0 [1, 4, 3] = true := by decide +kernel
theorem subd11_0_1402 : subd11_0 [1, 4, 4] = true := by decide +kernel
theorem subd11_0_1403 : subd11_0 [1, 4, 5] = true := by decide +kernel
theorem subd11_0_1404 : subd11_0 [1, 4, 6] = true := by decide +kernel
theorem subd11_0_1405 : subd11_0 [1, 4, 7] = true := by decide +kernel
theorem subd11_0_1406 : subd11_0 [1, 4, 8] = true := by decide +kernel
theorem subd11_0_1407 : subd11_0 [1, 5, -8] = true := by decide +kernel
theorem sbd11_0_43 : ∀ q ∈ blkd11_0_43, subd11_0 q = true := by
  unfold blkd11_0_43
  exact List.forall_mem_cons.2 ⟨subd11_0_1376, List.forall_mem_cons.2 ⟨subd11_0_1377, List.forall_mem_cons.2 ⟨subd11_0_1378, List.forall_mem_cons.2 ⟨subd11_0_1379, List.forall_mem_cons.2 ⟨subd11_0_1380, List.forall_mem_cons.2 ⟨subd11_0_1381, List.forall_mem_cons.2 ⟨subd11_0_1382, List.forall_mem_cons.2 ⟨subd11_0_1383, List.forall_mem_cons.2 ⟨subd11_0_1384, List.forall_mem_cons.2 ⟨subd11_0_1385, List.forall_mem_cons.2 ⟨subd11_0_1386, List.forall_mem_cons.2 ⟨subd11_0_1387, List.forall_mem_cons.2 ⟨subd11_0_1388, List.forall_mem_cons.2 ⟨subd11_0_1389, List.forall_mem_cons.2 ⟨subd11_0_1390, List.forall_mem_cons.2 ⟨subd11_0_1391, List.forall_mem_cons.2 ⟨subd11_0_1392, List.forall_mem_cons.2 ⟨subd11_0_1393, List.forall_mem_cons.2 ⟨subd11_0_1394, List.forall_mem_cons.2 ⟨subd11_0_1395, List.forall_mem_cons.2 ⟨subd11_0_1396, List.forall_mem_cons.2 ⟨subd11_0_1397, List.forall_mem_cons.2 ⟨subd11_0_1398, List.forall_mem_cons.2 ⟨subd11_0_1399, List.forall_mem_cons.2 ⟨subd11_0_1400, List.forall_mem_cons.2 ⟨subd11_0_1401, List.forall_mem_cons.2 ⟨subd11_0_1402, List.forall_mem_cons.2 ⟨subd11_0_1403, List.forall_mem_cons.2 ⟨subd11_0_1404, List.forall_mem_cons.2 ⟨subd11_0_1405, List.forall_mem_cons.2 ⟨subd11_0_1406, List.forall_mem_cons.2 ⟨subd11_0_1407, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_1408 : subd11_0 [1, 5, -7] = true := by decide +kernel
theorem subd11_0_1409 : subd11_0 [1, 5, -6] = true := by decide +kernel
theorem subd11_0_1410 : subd11_0 [1, 5, -5] = true := by decide +kernel
theorem subd11_0_1411 : subd11_0 [1, 5, -4] = true := by decide +kernel
theorem subd11_0_1412 : subd11_0 [1, 5, -3] = true := by decide +kernel
theorem subd11_0_1413 : subd11_0 [1, 5, -2] = true := by decide +kernel
theorem subd11_0_1414 : subd11_0 [1, 5, -1] = true := by decide +kernel
theorem subd11_0_1415 : subd11_0 [1, 5, 0] = true := by decide +kernel
theorem subd11_0_1416 : subd11_0 [1, 5, 1] = true := by decide +kernel
theorem subd11_0_1417 : subd11_0 [1, 5, 2] = true := by decide +kernel
theorem subd11_0_1418 : subd11_0 [1, 5, 3] = true := by decide +kernel
theorem subd11_0_1419 : subd11_0 [1, 5, 4] = true := by decide +kernel
theorem subd11_0_1420 : subd11_0 [1, 5, 5] = true := by decide +kernel
theorem subd11_0_1421 : subd11_0 [1, 5, 6] = true := by decide +kernel
theorem subd11_0_1422 : subd11_0 [1, 5, 7] = true := by decide +kernel
theorem subd11_0_1423 : subd11_0 [1, 6, -8] = true := by decide +kernel
theorem subd11_0_1424 : subd11_0 [1, 6, -7] = true := by decide +kernel
theorem subd11_0_1425 : subd11_0 [1, 6, -6] = true := by decide +kernel
theorem subd11_0_1426 : subd11_0 [1, 6, -5] = true := by decide +kernel
theorem subd11_0_1427 : subd11_0 [1, 6, -4] = true := by decide +kernel
theorem subd11_0_1428 : subd11_0 [1, 6, -3] = true := by decide +kernel
theorem subd11_0_1429 : subd11_0 [1, 6, -2] = true := by decide +kernel
theorem subd11_0_1430 : subd11_0 [1, 6, -1] = true := by decide +kernel
theorem subd11_0_1431 : subd11_0 [1, 6, 0] = true := by decide +kernel
theorem subd11_0_1432 : subd11_0 [1, 6, 1] = true := by decide +kernel
theorem subd11_0_1433 : subd11_0 [1, 6, 2] = true := by decide +kernel
theorem subd11_0_1434 : subd11_0 [1, 6, 3] = true := by decide +kernel
theorem subd11_0_1435 : subd11_0 [1, 6, 4] = true := by decide +kernel
theorem subd11_0_1436 : subd11_0 [1, 6, 5] = true := by decide +kernel
theorem subd11_0_1437 : subd11_0 [1, 6, 6] = true := by decide +kernel
theorem subd11_0_1438 : subd11_0 [1, 7, -7] = true := by decide +kernel
theorem subd11_0_1439 : subd11_0 [1, 7, -6] = true := by decide +kernel
theorem sbd11_0_44 : ∀ q ∈ blkd11_0_44, subd11_0 q = true := by
  unfold blkd11_0_44
  exact List.forall_mem_cons.2 ⟨subd11_0_1408, List.forall_mem_cons.2 ⟨subd11_0_1409, List.forall_mem_cons.2 ⟨subd11_0_1410, List.forall_mem_cons.2 ⟨subd11_0_1411, List.forall_mem_cons.2 ⟨subd11_0_1412, List.forall_mem_cons.2 ⟨subd11_0_1413, List.forall_mem_cons.2 ⟨subd11_0_1414, List.forall_mem_cons.2 ⟨subd11_0_1415, List.forall_mem_cons.2 ⟨subd11_0_1416, List.forall_mem_cons.2 ⟨subd11_0_1417, List.forall_mem_cons.2 ⟨subd11_0_1418, List.forall_mem_cons.2 ⟨subd11_0_1419, List.forall_mem_cons.2 ⟨subd11_0_1420, List.forall_mem_cons.2 ⟨subd11_0_1421, List.forall_mem_cons.2 ⟨subd11_0_1422, List.forall_mem_cons.2 ⟨subd11_0_1423, List.forall_mem_cons.2 ⟨subd11_0_1424, List.forall_mem_cons.2 ⟨subd11_0_1425, List.forall_mem_cons.2 ⟨subd11_0_1426, List.forall_mem_cons.2 ⟨subd11_0_1427, List.forall_mem_cons.2 ⟨subd11_0_1428, List.forall_mem_cons.2 ⟨subd11_0_1429, List.forall_mem_cons.2 ⟨subd11_0_1430, List.forall_mem_cons.2 ⟨subd11_0_1431, List.forall_mem_cons.2 ⟨subd11_0_1432, List.forall_mem_cons.2 ⟨subd11_0_1433, List.forall_mem_cons.2 ⟨subd11_0_1434, List.forall_mem_cons.2 ⟨subd11_0_1435, List.forall_mem_cons.2 ⟨subd11_0_1436, List.forall_mem_cons.2 ⟨subd11_0_1437, List.forall_mem_cons.2 ⟨subd11_0_1438, List.forall_mem_cons.2 ⟨subd11_0_1439, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_1440 : subd11_0 [1, 7, -5] = true := by decide +kernel
theorem subd11_0_1441 : subd11_0 [1, 7, -4] = true := by decide +kernel
theorem subd11_0_1442 : subd11_0 [1, 7, -3] = true := by decide +kernel
theorem subd11_0_1443 : subd11_0 [1, 7, -2] = true := by decide +kernel
theorem subd11_0_1444 : subd11_0 [1, 7, -1] = true := by decide +kernel
theorem subd11_0_1445 : subd11_0 [1, 7, 0] = true := by decide +kernel
theorem subd11_0_1446 : subd11_0 [1, 7, 1] = true := by decide +kernel
theorem subd11_0_1447 : subd11_0 [1, 7, 2] = true := by decide +kernel
theorem subd11_0_1448 : subd11_0 [1, 7, 3] = true := by decide +kernel
theorem subd11_0_1449 : subd11_0 [1, 7, 4] = true := by decide +kernel
theorem subd11_0_1450 : subd11_0 [1, 7, 5] = true := by decide +kernel
theorem subd11_0_1451 : subd11_0 [1, 7, 6] = true := by decide +kernel
theorem subd11_0_1452 : subd11_0 [1, 8] = true := by decide +kernel
theorem subd11_0_1453 : subd11_0 [1, 9] = true := by decide +kernel
theorem subd11_0_1454 : subd11_0 [2, -9] = true := by decide +kernel
theorem subd11_0_1455 : subd11_0 [2, -8] = true := by decide +kernel
theorem subd11_0_1456 : subd11_0 [2, -7] = true := by decide +kernel
theorem subd11_0_1457 : subd11_0 [2, -6] = true := by decide +kernel
theorem subd11_0_1458 : subd11_0 [2, -5, -6] = true := by decide +kernel
theorem subd11_0_1459 : subd11_0 [2, -5, -5] = true := by decide +kernel
theorem subd11_0_1460 : subd11_0 [2, -5, -4] = true := by decide +kernel
theorem subd11_0_1461 : subd11_0 [2, -5, -3] = true := by decide +kernel
theorem subd11_0_1462 : subd11_0 [2, -5, -2] = true := by decide +kernel
theorem subd11_0_1463 : subd11_0 [2, -5, -1] = true := by decide +kernel
theorem subd11_0_1464 : subd11_0 [2, -5, 0] = true := by decide +kernel
theorem subd11_0_1465 : subd11_0 [2, -5, 1] = true := by decide +kernel
theorem subd11_0_1466 : subd11_0 [2, -5, 2] = true := by decide +kernel
theorem subd11_0_1467 : subd11_0 [2, -5, 3] = true := by decide +kernel
theorem subd11_0_1468 : subd11_0 [2, -5, 4] = true := by decide +kernel
theorem subd11_0_1469 : subd11_0 [2, -5, 5] = true := by decide +kernel
theorem subd11_0_1470 : subd11_0 [2, -5, 6] = true := by decide +kernel
theorem subd11_0_1471 : subd11_0 [2, -5, 7] = true := by decide +kernel
theorem sbd11_0_45 : ∀ q ∈ blkd11_0_45, subd11_0 q = true := by
  unfold blkd11_0_45
  exact List.forall_mem_cons.2 ⟨subd11_0_1440, List.forall_mem_cons.2 ⟨subd11_0_1441, List.forall_mem_cons.2 ⟨subd11_0_1442, List.forall_mem_cons.2 ⟨subd11_0_1443, List.forall_mem_cons.2 ⟨subd11_0_1444, List.forall_mem_cons.2 ⟨subd11_0_1445, List.forall_mem_cons.2 ⟨subd11_0_1446, List.forall_mem_cons.2 ⟨subd11_0_1447, List.forall_mem_cons.2 ⟨subd11_0_1448, List.forall_mem_cons.2 ⟨subd11_0_1449, List.forall_mem_cons.2 ⟨subd11_0_1450, List.forall_mem_cons.2 ⟨subd11_0_1451, List.forall_mem_cons.2 ⟨subd11_0_1452, List.forall_mem_cons.2 ⟨subd11_0_1453, List.forall_mem_cons.2 ⟨subd11_0_1454, List.forall_mem_cons.2 ⟨subd11_0_1455, List.forall_mem_cons.2 ⟨subd11_0_1456, List.forall_mem_cons.2 ⟨subd11_0_1457, List.forall_mem_cons.2 ⟨subd11_0_1458, List.forall_mem_cons.2 ⟨subd11_0_1459, List.forall_mem_cons.2 ⟨subd11_0_1460, List.forall_mem_cons.2 ⟨subd11_0_1461, List.forall_mem_cons.2 ⟨subd11_0_1462, List.forall_mem_cons.2 ⟨subd11_0_1463, List.forall_mem_cons.2 ⟨subd11_0_1464, List.forall_mem_cons.2 ⟨subd11_0_1465, List.forall_mem_cons.2 ⟨subd11_0_1466, List.forall_mem_cons.2 ⟨subd11_0_1467, List.forall_mem_cons.2 ⟨subd11_0_1468, List.forall_mem_cons.2 ⟨subd11_0_1469, List.forall_mem_cons.2 ⟨subd11_0_1470, List.forall_mem_cons.2 ⟨subd11_0_1471, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_1472 : subd11_0 [2, -4, -7] = true := by decide +kernel
theorem subd11_0_1473 : subd11_0 [2, -4, -6] = true := by decide +kernel
theorem subd11_0_1474 : subd11_0 [2, -4, -5] = true := by decide +kernel
theorem subd11_0_1475 : subd11_0 [2, -4, -4] = true := by decide +kernel
theorem subd11_0_1476 : subd11_0 [2, -4, -3] = true := by decide +kernel
theorem subd11_0_1477 : subd11_0 [2, -4, -2] = true := by decide +kernel
theorem subd11_0_1478 : subd11_0 [2, -4, -1] = true := by decide +kernel
theorem subd11_0_1479 : subd11_0 [2, -4, 0] = true := by decide +kernel
theorem subd11_0_1480 : subd11_0 [2, -4, 1] = true := by decide +kernel
theorem subd11_0_1481 : subd11_0 [2, -4, 2] = true := by decide +kernel
theorem subd11_0_1482 : subd11_0 [2, -4, 3] = true := by decide +kernel
theorem subd11_0_1483 : subd11_0 [2, -4, 4] = true := by decide +kernel
theorem subd11_0_1484 : subd11_0 [2, -4, 5] = true := by decide +kernel
theorem subd11_0_1485 : subd11_0 [2, -4, 6] = true := by decide +kernel
theorem subd11_0_1486 : subd11_0 [2, -4, 7] = true := by decide +kernel
theorem subd11_0_1487 : subd11_0 [2, -3, -8] = true := by decide +kernel
theorem subd11_0_1488 : subd11_0 [2, -3, -7] = true := by decide +kernel
theorem subd11_0_1489 : subd11_0 [2, -3, -6] = true := by decide +kernel
theorem subd11_0_1490 : subd11_0 [2, -3, -5] = true := by decide +kernel
theorem subd11_0_1491 : subd11_0 [2, -3, -4] = true := by decide +kernel
theorem subd11_0_1492 : subd11_0 [2, -3, -3] = true := by decide +kernel
theorem subd11_0_1493 : subd11_0 [2, -3, -2] = true := by decide +kernel
theorem subd11_0_1494 : subd11_0 [2, -3, -1] = true := by decide +kernel
theorem subd11_0_1495 : subd11_0 [2, -3, 0] = true := by decide +kernel
theorem subd11_0_1496 : subd11_0 [2, -3, 1] = true := by decide +kernel
theorem subd11_0_1497 : subd11_0 [2, -3, 2] = true := by decide +kernel
theorem subd11_0_1498 : subd11_0 [2, -3, 3] = true := by decide +kernel
theorem subd11_0_1499 : subd11_0 [2, -3, 4] = true := by decide +kernel
theorem subd11_0_1500 : subd11_0 [2, -3, 5] = true := by decide +kernel
theorem subd11_0_1501 : subd11_0 [2, -3, 6] = true := by decide +kernel
theorem subd11_0_1502 : subd11_0 [2, -3, 7] = true := by decide +kernel
theorem subd11_0_1503 : subd11_0 [2, -3, 8] = true := by decide +kernel
theorem sbd11_0_46 : ∀ q ∈ blkd11_0_46, subd11_0 q = true := by
  unfold blkd11_0_46
  exact List.forall_mem_cons.2 ⟨subd11_0_1472, List.forall_mem_cons.2 ⟨subd11_0_1473, List.forall_mem_cons.2 ⟨subd11_0_1474, List.forall_mem_cons.2 ⟨subd11_0_1475, List.forall_mem_cons.2 ⟨subd11_0_1476, List.forall_mem_cons.2 ⟨subd11_0_1477, List.forall_mem_cons.2 ⟨subd11_0_1478, List.forall_mem_cons.2 ⟨subd11_0_1479, List.forall_mem_cons.2 ⟨subd11_0_1480, List.forall_mem_cons.2 ⟨subd11_0_1481, List.forall_mem_cons.2 ⟨subd11_0_1482, List.forall_mem_cons.2 ⟨subd11_0_1483, List.forall_mem_cons.2 ⟨subd11_0_1484, List.forall_mem_cons.2 ⟨subd11_0_1485, List.forall_mem_cons.2 ⟨subd11_0_1486, List.forall_mem_cons.2 ⟨subd11_0_1487, List.forall_mem_cons.2 ⟨subd11_0_1488, List.forall_mem_cons.2 ⟨subd11_0_1489, List.forall_mem_cons.2 ⟨subd11_0_1490, List.forall_mem_cons.2 ⟨subd11_0_1491, List.forall_mem_cons.2 ⟨subd11_0_1492, List.forall_mem_cons.2 ⟨subd11_0_1493, List.forall_mem_cons.2 ⟨subd11_0_1494, List.forall_mem_cons.2 ⟨subd11_0_1495, List.forall_mem_cons.2 ⟨subd11_0_1496, List.forall_mem_cons.2 ⟨subd11_0_1497, List.forall_mem_cons.2 ⟨subd11_0_1498, List.forall_mem_cons.2 ⟨subd11_0_1499, List.forall_mem_cons.2 ⟨subd11_0_1500, List.forall_mem_cons.2 ⟨subd11_0_1501, List.forall_mem_cons.2 ⟨subd11_0_1502, List.forall_mem_cons.2 ⟨subd11_0_1503, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_1504 : subd11_0 [2, -2, -8] = true := by decide +kernel
theorem subd11_0_1505 : subd11_0 [2, -2, -7] = true := by decide +kernel
theorem subd11_0_1506 : subd11_0 [2, -2, -6] = true := by decide +kernel
theorem subd11_0_1507 : subd11_0 [2, -2, -5] = true := by decide +kernel
theorem subd11_0_1508 : subd11_0 [2, -2, -4] = true := by decide +kernel
theorem subd11_0_1509 : subd11_0 [2, -2, -3] = true := by decide +kernel
theorem subd11_0_1510 : subd11_0 [2, -2, -2] = true := by decide +kernel
theorem subd11_0_1511 : subd11_0 [2, -2, -1] = true := by decide +kernel
theorem subd11_0_1512 : subd11_0 [2, -2, 0] = true := by decide +kernel
theorem subd11_0_1513 : subd11_0 [2, -2, 1] = true := by decide +kernel
theorem subd11_0_1514 : subd11_0 [2, -2, 2] = true := by decide +kernel
theorem subd11_0_1515 : subd11_0 [2, -2, 3] = true := by decide +kernel
theorem subd11_0_1516 : subd11_0 [2, -2, 4] = true := by decide +kernel
theorem subd11_0_1517 : subd11_0 [2, -2, 5] = true := by decide +kernel
theorem subd11_0_1518 : subd11_0 [2, -2, 6] = true := by decide +kernel
theorem subd11_0_1519 : subd11_0 [2, -2, 7] = true := by decide +kernel
theorem subd11_0_1520 : subd11_0 [2, -2, 8] = true := by decide +kernel
theorem subd11_0_1521 : subd11_0 [2, -1, -8] = true := by decide +kernel
theorem subd11_0_1522 : subd11_0 [2, -1, -7] = true := by decide +kernel
theorem subd11_0_1523 : subd11_0 [2, -1, -6] = true := by decide +kernel
theorem subd11_0_1524 : subd11_0 [2, -1, -5] = true := by decide +kernel
theorem subd11_0_1525 : subd11_0 [2, -1, -4] = true := by decide +kernel
theorem subd11_0_1526 : subd11_0 [2, -1, -3] = true := by decide +kernel
theorem subd11_0_1527 : subd11_0 [2, -1, -2] = true := by decide +kernel
theorem subd11_0_1528 : subd11_0 [2, -1, -1] = true := by decide +kernel
theorem subd11_0_1529 : subd11_0 [2, -1, 0] = true := by decide +kernel
theorem subd11_0_1530 : subd11_0 [2, -1, 1] = true := by decide +kernel
theorem subd11_0_1531 : subd11_0 [2, -1, 2] = true := by decide +kernel
theorem subd11_0_1532 : subd11_0 [2, -1, 3] = true := by decide +kernel
theorem subd11_0_1533 : subd11_0 [2, -1, 4] = true := by decide +kernel
theorem subd11_0_1534 : subd11_0 [2, -1, 5] = true := by decide +kernel
theorem subd11_0_1535 : subd11_0 [2, -1, 6] = true := by decide +kernel
theorem sbd11_0_47 : ∀ q ∈ blkd11_0_47, subd11_0 q = true := by
  unfold blkd11_0_47
  exact List.forall_mem_cons.2 ⟨subd11_0_1504, List.forall_mem_cons.2 ⟨subd11_0_1505, List.forall_mem_cons.2 ⟨subd11_0_1506, List.forall_mem_cons.2 ⟨subd11_0_1507, List.forall_mem_cons.2 ⟨subd11_0_1508, List.forall_mem_cons.2 ⟨subd11_0_1509, List.forall_mem_cons.2 ⟨subd11_0_1510, List.forall_mem_cons.2 ⟨subd11_0_1511, List.forall_mem_cons.2 ⟨subd11_0_1512, List.forall_mem_cons.2 ⟨subd11_0_1513, List.forall_mem_cons.2 ⟨subd11_0_1514, List.forall_mem_cons.2 ⟨subd11_0_1515, List.forall_mem_cons.2 ⟨subd11_0_1516, List.forall_mem_cons.2 ⟨subd11_0_1517, List.forall_mem_cons.2 ⟨subd11_0_1518, List.forall_mem_cons.2 ⟨subd11_0_1519, List.forall_mem_cons.2 ⟨subd11_0_1520, List.forall_mem_cons.2 ⟨subd11_0_1521, List.forall_mem_cons.2 ⟨subd11_0_1522, List.forall_mem_cons.2 ⟨subd11_0_1523, List.forall_mem_cons.2 ⟨subd11_0_1524, List.forall_mem_cons.2 ⟨subd11_0_1525, List.forall_mem_cons.2 ⟨subd11_0_1526, List.forall_mem_cons.2 ⟨subd11_0_1527, List.forall_mem_cons.2 ⟨subd11_0_1528, List.forall_mem_cons.2 ⟨subd11_0_1529, List.forall_mem_cons.2 ⟨subd11_0_1530, List.forall_mem_cons.2 ⟨subd11_0_1531, List.forall_mem_cons.2 ⟨subd11_0_1532, List.forall_mem_cons.2 ⟨subd11_0_1533, List.forall_mem_cons.2 ⟨subd11_0_1534, List.forall_mem_cons.2 ⟨subd11_0_1535, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_1536 : subd11_0 [2, -1, 7] = true := by decide +kernel
theorem subd11_0_1537 : subd11_0 [2, -1, 8] = true := by decide +kernel
theorem subd11_0_1538 : subd11_0 [2, 0, -8] = true := by decide +kernel
theorem subd11_0_1539 : subd11_0 [2, 0, -7] = true := by decide +kernel
theorem subd11_0_1540 : subd11_0 [2, 0, -6] = true := by decide +kernel
theorem subd11_0_1541 : subd11_0 [2, 0, -5] = true := by decide +kernel
theorem subd11_0_1542 : subd11_0 [2, 0, -4] = true := by decide +kernel
theorem subd11_0_1543 : subd11_0 [2, 0, -3] = true := by decide +kernel
theorem subd11_0_1544 : subd11_0 [2, 0, -2] = true := by decide +kernel
theorem subd11_0_1545 : subd11_0 [2, 0, -1] = true := by decide +kernel
theorem subd11_0_1546 : subd11_0 [2, 0, 0] = true := by decide +kernel
theorem subd11_0_1547 : subd11_0 [2, 0, 1] = true := by decide +kernel
theorem subd11_0_1548 : subd11_0 [2, 0, 2] = true := by decide +kernel
theorem subd11_0_1549 : subd11_0 [2, 0, 3] = true := by decide +kernel
theorem subd11_0_1550 : subd11_0 [2, 0, 4] = true := by decide +kernel
theorem subd11_0_1551 : subd11_0 [2, 0, 5] = true := by decide +kernel
theorem subd11_0_1552 : subd11_0 [2, 0, 6] = true := by decide +kernel
theorem subd11_0_1553 : subd11_0 [2, 0, 7] = true := by decide +kernel
theorem subd11_0_1554 : subd11_0 [2, 0, 8] = true := by decide +kernel
theorem subd11_0_1555 : subd11_0 [2, 1, -9] = true := by decide +kernel
theorem subd11_0_1556 : subd11_0 [2, 1, -8] = true := by decide +kernel
theorem subd11_0_1557 : subd11_0 [2, 1, -7] = true := by decide +kernel
theorem subd11_0_1558 : subd11_0 [2, 1, -6] = true := by decide +kernel
theorem subd11_0_1559 : subd11_0 [2, 1, -5] = true := by decide +kernel
theorem subd11_0_1560 : subd11_0 [2, 1, -4] = true := by decide +kernel
theorem subd11_0_1561 : subd11_0 [2, 1, -3] = true := by decide +kernel
theorem subd11_0_1562 : subd11_0 [2, 1, -2] = true := by decide +kernel
theorem subd11_0_1563 : subd11_0 [2, 1, -1] = true := by decide +kernel
theorem subd11_0_1564 : subd11_0 [2, 1, 0] = true := by decide +kernel
theorem subd11_0_1565 : subd11_0 [2, 1, 1] = true := by decide +kernel
theorem subd11_0_1566 : subd11_0 [2, 1, 2] = true := by decide +kernel
theorem subd11_0_1567 : subd11_0 [2, 1, 3] = true := by decide +kernel
theorem sbd11_0_48 : ∀ q ∈ blkd11_0_48, subd11_0 q = true := by
  unfold blkd11_0_48
  exact List.forall_mem_cons.2 ⟨subd11_0_1536, List.forall_mem_cons.2 ⟨subd11_0_1537, List.forall_mem_cons.2 ⟨subd11_0_1538, List.forall_mem_cons.2 ⟨subd11_0_1539, List.forall_mem_cons.2 ⟨subd11_0_1540, List.forall_mem_cons.2 ⟨subd11_0_1541, List.forall_mem_cons.2 ⟨subd11_0_1542, List.forall_mem_cons.2 ⟨subd11_0_1543, List.forall_mem_cons.2 ⟨subd11_0_1544, List.forall_mem_cons.2 ⟨subd11_0_1545, List.forall_mem_cons.2 ⟨subd11_0_1546, List.forall_mem_cons.2 ⟨subd11_0_1547, List.forall_mem_cons.2 ⟨subd11_0_1548, List.forall_mem_cons.2 ⟨subd11_0_1549, List.forall_mem_cons.2 ⟨subd11_0_1550, List.forall_mem_cons.2 ⟨subd11_0_1551, List.forall_mem_cons.2 ⟨subd11_0_1552, List.forall_mem_cons.2 ⟨subd11_0_1553, List.forall_mem_cons.2 ⟨subd11_0_1554, List.forall_mem_cons.2 ⟨subd11_0_1555, List.forall_mem_cons.2 ⟨subd11_0_1556, List.forall_mem_cons.2 ⟨subd11_0_1557, List.forall_mem_cons.2 ⟨subd11_0_1558, List.forall_mem_cons.2 ⟨subd11_0_1559, List.forall_mem_cons.2 ⟨subd11_0_1560, List.forall_mem_cons.2 ⟨subd11_0_1561, List.forall_mem_cons.2 ⟨subd11_0_1562, List.forall_mem_cons.2 ⟨subd11_0_1563, List.forall_mem_cons.2 ⟨subd11_0_1564, List.forall_mem_cons.2 ⟨subd11_0_1565, List.forall_mem_cons.2 ⟨subd11_0_1566, List.forall_mem_cons.2 ⟨subd11_0_1567, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C131
