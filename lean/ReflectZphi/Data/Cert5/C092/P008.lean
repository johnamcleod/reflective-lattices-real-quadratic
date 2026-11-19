import ReflectZphi.Data.Cert5.C092.Base

namespace ReflectZphi.Data.Cert5.C092
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub7_1088 : sub7 [3, 2, -7] = true := by decide +kernel
theorem sub7_1089 : sub7 [3, 2, -6] = true := by decide +kernel
theorem sub7_1090 : sub7 [3, 2, -5] = true := by decide +kernel
theorem sub7_1091 : sub7 [3, 2, -4] = true := by decide +kernel
theorem sub7_1092 : sub7 [3, 2, -3] = true := by decide +kernel
theorem sub7_1093 : sub7 [3, 2, -2] = true := by decide +kernel
theorem sub7_1094 : sub7 [3, 2, -1] = true := by decide +kernel
theorem sub7_1095 : sub7 [3, 2, 0] = true := by decide +kernel
theorem sub7_1096 : sub7 [3, 2, 1] = true := by decide +kernel
theorem sub7_1097 : sub7 [3, 2, 2] = true := by decide +kernel
theorem sub7_1098 : sub7 [3, 2, 3] = true := by decide +kernel
theorem sub7_1099 : sub7 [3, 2, 4] = true := by decide +kernel
theorem sub7_1100 : sub7 [3, 2, 5] = true := by decide +kernel
theorem sub7_1101 : sub7 [3, 2, 6] = true := by decide +kernel
theorem sub7_1102 : sub7 [3, 2, 7] = true := by decide +kernel
theorem sub7_1103 : sub7 [3, 2, 8] = true := by decide +kernel
theorem sub7_1104 : sub7 [3, 3, -7] = true := by decide +kernel
theorem sub7_1105 : sub7 [3, 3, -6] = true := by decide +kernel
theorem sub7_1106 : sub7 [3, 3, -5] = true := by decide +kernel
theorem sub7_1107 : sub7 [3, 3, -4] = true := by decide +kernel
theorem sub7_1108 : sub7 [3, 3, -3] = true := by decide +kernel
theorem sub7_1109 : sub7 [3, 3, -2] = true := by decide +kernel
theorem sub7_1110 : sub7 [3, 3, -1] = true := by decide +kernel
theorem sub7_1111 : sub7 [3, 3, 0] = true := by decide +kernel
theorem sub7_1112 : sub7 [3, 3, 1] = true := by decide +kernel
theorem sub7_1113 : sub7 [3, 3, 2] = true := by decide +kernel
theorem sub7_1114 : sub7 [3, 3, 3] = true := by decide +kernel
theorem sub7_1115 : sub7 [3, 3, 4] = true := by decide +kernel
theorem sub7_1116 : sub7 [3, 3, 5] = true := by decide +kernel
theorem sub7_1117 : sub7 [3, 3, 6] = true := by decide +kernel
theorem sub7_1118 : sub7 [3, 3, 7] = true := by decide +kernel
theorem sub7_1119 : sub7 [3, 3, 8] = true := by decide +kernel
theorem sb7_34 : ∀ q ∈ blk7_34, sub7 q = true := by
  unfold blk7_34
  exact List.forall_mem_cons.2 ⟨sub7_1088, List.forall_mem_cons.2 ⟨sub7_1089, List.forall_mem_cons.2 ⟨sub7_1090, List.forall_mem_cons.2 ⟨sub7_1091, List.forall_mem_cons.2 ⟨sub7_1092, List.forall_mem_cons.2 ⟨sub7_1093, List.forall_mem_cons.2 ⟨sub7_1094, List.forall_mem_cons.2 ⟨sub7_1095, List.forall_mem_cons.2 ⟨sub7_1096, List.forall_mem_cons.2 ⟨sub7_1097, List.forall_mem_cons.2 ⟨sub7_1098, List.forall_mem_cons.2 ⟨sub7_1099, List.forall_mem_cons.2 ⟨sub7_1100, List.forall_mem_cons.2 ⟨sub7_1101, List.forall_mem_cons.2 ⟨sub7_1102, List.forall_mem_cons.2 ⟨sub7_1103, List.forall_mem_cons.2 ⟨sub7_1104, List.forall_mem_cons.2 ⟨sub7_1105, List.forall_mem_cons.2 ⟨sub7_1106, List.forall_mem_cons.2 ⟨sub7_1107, List.forall_mem_cons.2 ⟨sub7_1108, List.forall_mem_cons.2 ⟨sub7_1109, List.forall_mem_cons.2 ⟨sub7_1110, List.forall_mem_cons.2 ⟨sub7_1111, List.forall_mem_cons.2 ⟨sub7_1112, List.forall_mem_cons.2 ⟨sub7_1113, List.forall_mem_cons.2 ⟨sub7_1114, List.forall_mem_cons.2 ⟨sub7_1115, List.forall_mem_cons.2 ⟨sub7_1116, List.forall_mem_cons.2 ⟨sub7_1117, List.forall_mem_cons.2 ⟨sub7_1118, List.forall_mem_cons.2 ⟨sub7_1119, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_1120 : sub7 [3, 4, -6] = true := by decide +kernel
theorem sub7_1121 : sub7 [3, 4, -5] = true := by decide +kernel
theorem sub7_1122 : sub7 [3, 4, -4] = true := by decide +kernel
theorem sub7_1123 : sub7 [3, 4, -3] = true := by decide +kernel
theorem sub7_1124 : sub7 [3, 4, -2] = true := by decide +kernel
theorem sub7_1125 : sub7 [3, 4, -1] = true := by decide +kernel
theorem sub7_1126 : sub7 [3, 4, 0] = true := by decide +kernel
theorem sub7_1127 : sub7 [3, 4, 1] = true := by decide +kernel
theorem sub7_1128 : sub7 [3, 4, 2] = true := by decide +kernel
theorem sub7_1129 : sub7 [3, 4, 3] = true := by decide +kernel
theorem sub7_1130 : sub7 [3, 4, 4] = true := by decide +kernel
theorem sub7_1131 : sub7 [3, 4, 5] = true := by decide +kernel
theorem sub7_1132 : sub7 [3, 4, 6] = true := by decide +kernel
theorem sub7_1133 : sub7 [3, 4, 7] = true := by decide +kernel
theorem sub7_1134 : sub7 [3, 5] = true := by decide +kernel
theorem sub7_1135 : sub7 [3, 6] = true := by decide +kernel
theorem sub7_1136 : sub7 [3, 7] = true := by decide +kernel
theorem sub7_1137 : sub7 [4, -6] = true := by decide +kernel
theorem sub7_1138 : sub7 [4, -5] = true := by decide +kernel
theorem sub7_1139 : sub7 [4, -4] = true := by decide +kernel
theorem sub7_1140 : sub7 [4, -3] = true := by decide +kernel
theorem sub7_1141 : sub7 [4, -2, -7] = true := by decide +kernel
theorem sub7_1142 : sub7 [4, -2, -6] = true := by decide +kernel
theorem sub7_1143 : sub7 [4, -2, -5] = true := by decide +kernel
theorem sub7_1144 : sub7 [4, -2, -4] = true := by decide +kernel
theorem sub7_1145 : sub7 [4, -2, -3] = true := by decide +kernel
theorem sub7_1146 : sub7 [4, -2, -2] = true := by decide +kernel
theorem sub7_1147 : sub7 [4, -2, -1] = true := by decide +kernel
theorem sub7_1148 : sub7 [4, -2, 0] = true := by decide +kernel
theorem sub7_1149 : sub7 [4, -2, 1] = true := by decide +kernel
theorem sub7_1150 : sub7 [4, -2, 2] = true := by decide +kernel
theorem sub7_1151 : sub7 [4, -2, 3] = true := by decide +kernel
theorem sb7_35 : ∀ q ∈ blk7_35, sub7 q = true := by
  unfold blk7_35
  exact List.forall_mem_cons.2 ⟨sub7_1120, List.forall_mem_cons.2 ⟨sub7_1121, List.forall_mem_cons.2 ⟨sub7_1122, List.forall_mem_cons.2 ⟨sub7_1123, List.forall_mem_cons.2 ⟨sub7_1124, List.forall_mem_cons.2 ⟨sub7_1125, List.forall_mem_cons.2 ⟨sub7_1126, List.forall_mem_cons.2 ⟨sub7_1127, List.forall_mem_cons.2 ⟨sub7_1128, List.forall_mem_cons.2 ⟨sub7_1129, List.forall_mem_cons.2 ⟨sub7_1130, List.forall_mem_cons.2 ⟨sub7_1131, List.forall_mem_cons.2 ⟨sub7_1132, List.forall_mem_cons.2 ⟨sub7_1133, List.forall_mem_cons.2 ⟨sub7_1134, List.forall_mem_cons.2 ⟨sub7_1135, List.forall_mem_cons.2 ⟨sub7_1136, List.forall_mem_cons.2 ⟨sub7_1137, List.forall_mem_cons.2 ⟨sub7_1138, List.forall_mem_cons.2 ⟨sub7_1139, List.forall_mem_cons.2 ⟨sub7_1140, List.forall_mem_cons.2 ⟨sub7_1141, List.forall_mem_cons.2 ⟨sub7_1142, List.forall_mem_cons.2 ⟨sub7_1143, List.forall_mem_cons.2 ⟨sub7_1144, List.forall_mem_cons.2 ⟨sub7_1145, List.forall_mem_cons.2 ⟨sub7_1146, List.forall_mem_cons.2 ⟨sub7_1147, List.forall_mem_cons.2 ⟨sub7_1148, List.forall_mem_cons.2 ⟨sub7_1149, List.forall_mem_cons.2 ⟨sub7_1150, List.forall_mem_cons.2 ⟨sub7_1151, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_1152 : sub7 [4, -2, 4] = true := by decide +kernel
theorem sub7_1153 : sub7 [4, -2, 5] = true := by decide +kernel
theorem sub7_1154 : sub7 [4, -2, 6] = true := by decide +kernel
theorem sub7_1155 : sub7 [4, -1, -7] = true := by decide +kernel
theorem sub7_1156 : sub7 [4, -1, -6] = true := by decide +kernel
theorem sub7_1157 : sub7 [4, -1, -5] = true := by decide +kernel
theorem sub7_1158 : sub7 [4, -1, -4] = true := by decide +kernel
theorem sub7_1159 : sub7 [4, -1, -3] = true := by decide +kernel
theorem sub7_1160 : sub7 [4, -1, -2] = true := by decide +kernel
theorem sub7_1161 : sub7 [4, -1, -1] = true := by decide +kernel
theorem sub7_1162 : sub7 [4, -1, 0] = true := by decide +kernel
theorem sub7_1163 : sub7 [4, -1, 1] = true := by decide +kernel
theorem sub7_1164 : sub7 [4, -1, 2] = true := by decide +kernel
theorem sub7_1165 : sub7 [4, -1, 3] = true := by decide +kernel
theorem sub7_1166 : sub7 [4, -1, 4] = true := by decide +kernel
theorem sub7_1167 : sub7 [4, -1, 5] = true := by decide +kernel
theorem sub7_1168 : sub7 [4, -1, 6] = true := by decide +kernel
theorem sub7_1169 : sub7 [4, -1, 7] = true := by decide +kernel
theorem sub7_1170 : sub7 [4, 0, -7] = true := by decide +kernel
theorem sub7_1171 : sub7 [4, 0, -6] = true := by decide +kernel
theorem sub7_1172 : sub7 [4, 0, -5] = true := by decide +kernel
theorem sub7_1173 : sub7 [4, 0, -4] = true := by decide +kernel
theorem sub7_1174 : sub7 [4, 0, -3] = true := by decide +kernel
theorem sub7_1175 : sub7 [4, 0, -2] = true := by decide +kernel
theorem sub7_1176 : sub7 [4, 0, -1] = true := by decide +kernel
theorem sub7_1177 : sub7 [4, 0, 0] = true := by decide +kernel
theorem sub7_1178 : sub7 [4, 0, 1] = true := by decide +kernel
theorem sub7_1179 : sub7 [4, 0, 2] = true := by decide +kernel
theorem sub7_1180 : sub7 [4, 0, 3] = true := by decide +kernel
theorem sub7_1181 : sub7 [4, 0, 4] = true := by decide +kernel
theorem sub7_1182 : sub7 [4, 0, 5] = true := by decide +kernel
theorem sub7_1183 : sub7 [4, 0, 6] = true := by decide +kernel
theorem sb7_36 : ∀ q ∈ blk7_36, sub7 q = true := by
  unfold blk7_36
  exact List.forall_mem_cons.2 ⟨sub7_1152, List.forall_mem_cons.2 ⟨sub7_1153, List.forall_mem_cons.2 ⟨sub7_1154, List.forall_mem_cons.2 ⟨sub7_1155, List.forall_mem_cons.2 ⟨sub7_1156, List.forall_mem_cons.2 ⟨sub7_1157, List.forall_mem_cons.2 ⟨sub7_1158, List.forall_mem_cons.2 ⟨sub7_1159, List.forall_mem_cons.2 ⟨sub7_1160, List.forall_mem_cons.2 ⟨sub7_1161, List.forall_mem_cons.2 ⟨sub7_1162, List.forall_mem_cons.2 ⟨sub7_1163, List.forall_mem_cons.2 ⟨sub7_1164, List.forall_mem_cons.2 ⟨sub7_1165, List.forall_mem_cons.2 ⟨sub7_1166, List.forall_mem_cons.2 ⟨sub7_1167, List.forall_mem_cons.2 ⟨sub7_1168, List.forall_mem_cons.2 ⟨sub7_1169, List.forall_mem_cons.2 ⟨sub7_1170, List.forall_mem_cons.2 ⟨sub7_1171, List.forall_mem_cons.2 ⟨sub7_1172, List.forall_mem_cons.2 ⟨sub7_1173, List.forall_mem_cons.2 ⟨sub7_1174, List.forall_mem_cons.2 ⟨sub7_1175, List.forall_mem_cons.2 ⟨sub7_1176, List.forall_mem_cons.2 ⟨sub7_1177, List.forall_mem_cons.2 ⟨sub7_1178, List.forall_mem_cons.2 ⟨sub7_1179, List.forall_mem_cons.2 ⟨sub7_1180, List.forall_mem_cons.2 ⟨sub7_1181, List.forall_mem_cons.2 ⟨sub7_1182, List.forall_mem_cons.2 ⟨sub7_1183, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_1184 : sub7 [4, 0, 7] = true := by decide +kernel
theorem sub7_1185 : sub7 [4, 1, -7] = true := by decide +kernel
theorem sub7_1186 : sub7 [4, 1, -6] = true := by decide +kernel
theorem sub7_1187 : sub7 [4, 1, -5] = true := by decide +kernel
theorem sub7_1188 : sub7 [4, 1, -4] = true := by decide +kernel
theorem sub7_1189 : sub7 [4, 1, -3] = true := by decide +kernel
theorem sub7_1190 : sub7 [4, 1, -2] = true := by decide +kernel
theorem sub7_1191 : sub7 [4, 1, -1] = true := by decide +kernel
theorem sub7_1192 : sub7 [4, 1, 0] = true := by decide +kernel
theorem sub7_1193 : sub7 [4, 1, 1] = true := by decide +kernel
theorem sub7_1194 : sub7 [4, 1, 2] = true := by decide +kernel
theorem sub7_1195 : sub7 [4, 1, 3] = true := by decide +kernel
theorem sub7_1196 : sub7 [4, 1, 4] = true := by decide +kernel
theorem sub7_1197 : sub7 [4, 1, 5] = true := by decide +kernel
theorem sub7_1198 : sub7 [4, 1, 6] = true := by decide +kernel
theorem sub7_1199 : sub7 [4, 1, 7] = true := by decide +kernel
theorem sub7_1200 : sub7 [4, 2, -7] = true := by decide +kernel
theorem sub7_1201 : sub7 [4, 2, -6] = true := by decide +kernel
theorem sub7_1202 : sub7 [4, 2, -5] = true := by decide +kernel
theorem sub7_1203 : sub7 [4, 2, -4] = true := by decide +kernel
theorem sub7_1204 : sub7 [4, 2, -3] = true := by decide +kernel
theorem sub7_1205 : sub7 [4, 2, -2] = true := by decide +kernel
theorem sub7_1206 : sub7 [4, 2, -1] = true := by decide +kernel
theorem sub7_1207 : sub7 [4, 2, 0] = true := by decide +kernel
theorem sub7_1208 : sub7 [4, 2, 1] = true := by decide +kernel
theorem sub7_1209 : sub7 [4, 2, 2] = true := by decide +kernel
theorem sub7_1210 : sub7 [4, 2, 3] = true := by decide +kernel
theorem sub7_1211 : sub7 [4, 2, 4] = true := by decide +kernel
theorem sub7_1212 : sub7 [4, 2, 5] = true := by decide +kernel
theorem sub7_1213 : sub7 [4, 2, 6] = true := by decide +kernel
theorem sub7_1214 : sub7 [4, 2, 7] = true := by decide +kernel
theorem sub7_1215 : sub7 [4, 3, -6] = true := by decide +kernel
theorem sb7_37 : ∀ q ∈ blk7_37, sub7 q = true := by
  unfold blk7_37
  exact List.forall_mem_cons.2 ⟨sub7_1184, List.forall_mem_cons.2 ⟨sub7_1185, List.forall_mem_cons.2 ⟨sub7_1186, List.forall_mem_cons.2 ⟨sub7_1187, List.forall_mem_cons.2 ⟨sub7_1188, List.forall_mem_cons.2 ⟨sub7_1189, List.forall_mem_cons.2 ⟨sub7_1190, List.forall_mem_cons.2 ⟨sub7_1191, List.forall_mem_cons.2 ⟨sub7_1192, List.forall_mem_cons.2 ⟨sub7_1193, List.forall_mem_cons.2 ⟨sub7_1194, List.forall_mem_cons.2 ⟨sub7_1195, List.forall_mem_cons.2 ⟨sub7_1196, List.forall_mem_cons.2 ⟨sub7_1197, List.forall_mem_cons.2 ⟨sub7_1198, List.forall_mem_cons.2 ⟨sub7_1199, List.forall_mem_cons.2 ⟨sub7_1200, List.forall_mem_cons.2 ⟨sub7_1201, List.forall_mem_cons.2 ⟨sub7_1202, List.forall_mem_cons.2 ⟨sub7_1203, List.forall_mem_cons.2 ⟨sub7_1204, List.forall_mem_cons.2 ⟨sub7_1205, List.forall_mem_cons.2 ⟨sub7_1206, List.forall_mem_cons.2 ⟨sub7_1207, List.forall_mem_cons.2 ⟨sub7_1208, List.forall_mem_cons.2 ⟨sub7_1209, List.forall_mem_cons.2 ⟨sub7_1210, List.forall_mem_cons.2 ⟨sub7_1211, List.forall_mem_cons.2 ⟨sub7_1212, List.forall_mem_cons.2 ⟨sub7_1213, List.forall_mem_cons.2 ⟨sub7_1214, List.forall_mem_cons.2 ⟨sub7_1215, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_1216 : sub7 [4, 3, -5] = true := by decide +kernel
theorem sub7_1217 : sub7 [4, 3, -4] = true := by decide +kernel
theorem sub7_1218 : sub7 [4, 3, -3] = true := by decide +kernel
theorem sub7_1219 : sub7 [4, 3, -2] = true := by decide +kernel
theorem sub7_1220 : sub7 [4, 3, -1] = true := by decide +kernel
theorem sub7_1221 : sub7 [4, 3, 0] = true := by decide +kernel
theorem sub7_1222 : sub7 [4, 3, 1] = true := by decide +kernel
theorem sub7_1223 : sub7 [4, 3, 2] = true := by decide +kernel
theorem sub7_1224 : sub7 [4, 3, 3] = true := by decide +kernel
theorem sub7_1225 : sub7 [4, 3, 4] = true := by decide +kernel
theorem sub7_1226 : sub7 [4, 3, 5] = true := by decide +kernel
theorem sub7_1227 : sub7 [4, 3, 6] = true := by decide +kernel
theorem sub7_1228 : sub7 [4, 3, 7] = true := by decide +kernel
theorem sub7_1229 : sub7 [4, 4] = true := by decide +kernel
theorem sub7_1230 : sub7 [4, 5] = true := by decide +kernel
theorem sub7_1231 : sub7 [4, 6] = true := by decide +kernel
theorem sub7_1232 : sub7 [4, 7] = true := by decide +kernel
theorem sub7_1233 : sub7 [5, -5] = true := by decide +kernel
theorem sub7_1234 : sub7 [5, -4] = true := by decide +kernel
theorem sub7_1235 : sub7 [5, -3] = true := by decide +kernel
theorem sub7_1236 : sub7 [5, -2] = true := by decide +kernel
theorem sub7_1237 : sub7 [5, -1] = true := by decide +kernel
theorem sub7_1238 : sub7 [5, 0] = true := by decide +kernel
theorem sub7_1239 : sub7 [5, 1, -6] = true := by decide +kernel
theorem sub7_1240 : sub7 [5, 1, -5] = true := by decide +kernel
theorem sub7_1241 : sub7 [5, 1, -4] = true := by decide +kernel
theorem sub7_1242 : sub7 [5, 1, -3] = true := by decide +kernel
theorem sub7_1243 : sub7 [5, 1, -2] = true := by decide +kernel
theorem sub7_1244 : sub7 [5, 1, -1] = true := by decide +kernel
theorem sub7_1245 : sub7 [5, 1, 0] = true := by decide +kernel
theorem sub7_1246 : sub7 [5, 1, 1] = true := by decide +kernel
theorem sub7_1247 : sub7 [5, 1, 2] = true := by decide +kernel
theorem sb7_38 : ∀ q ∈ blk7_38, sub7 q = true := by
  unfold blk7_38
  exact List.forall_mem_cons.2 ⟨sub7_1216, List.forall_mem_cons.2 ⟨sub7_1217, List.forall_mem_cons.2 ⟨sub7_1218, List.forall_mem_cons.2 ⟨sub7_1219, List.forall_mem_cons.2 ⟨sub7_1220, List.forall_mem_cons.2 ⟨sub7_1221, List.forall_mem_cons.2 ⟨sub7_1222, List.forall_mem_cons.2 ⟨sub7_1223, List.forall_mem_cons.2 ⟨sub7_1224, List.forall_mem_cons.2 ⟨sub7_1225, List.forall_mem_cons.2 ⟨sub7_1226, List.forall_mem_cons.2 ⟨sub7_1227, List.forall_mem_cons.2 ⟨sub7_1228, List.forall_mem_cons.2 ⟨sub7_1229, List.forall_mem_cons.2 ⟨sub7_1230, List.forall_mem_cons.2 ⟨sub7_1231, List.forall_mem_cons.2 ⟨sub7_1232, List.forall_mem_cons.2 ⟨sub7_1233, List.forall_mem_cons.2 ⟨sub7_1234, List.forall_mem_cons.2 ⟨sub7_1235, List.forall_mem_cons.2 ⟨sub7_1236, List.forall_mem_cons.2 ⟨sub7_1237, List.forall_mem_cons.2 ⟨sub7_1238, List.forall_mem_cons.2 ⟨sub7_1239, List.forall_mem_cons.2 ⟨sub7_1240, List.forall_mem_cons.2 ⟨sub7_1241, List.forall_mem_cons.2 ⟨sub7_1242, List.forall_mem_cons.2 ⟨sub7_1243, List.forall_mem_cons.2 ⟨sub7_1244, List.forall_mem_cons.2 ⟨sub7_1245, List.forall_mem_cons.2 ⟨sub7_1246, List.forall_mem_cons.2 ⟨sub7_1247, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_1248 : sub7 [5, 1, 3] = true := by decide +kernel
theorem sub7_1249 : sub7 [5, 1, 4] = true := by decide +kernel
theorem sub7_1250 : sub7 [5, 1, 5] = true := by decide +kernel
theorem sub7_1251 : sub7 [5, 1, 6] = true := by decide +kernel
theorem sub7_1252 : sub7 [5, 1, 7] = true := by decide +kernel
theorem sub7_1253 : sub7 [5, 2] = true := by decide +kernel
theorem sub7_1254 : sub7 [5, 3] = true := by decide +kernel
theorem sub7_1255 : sub7 [5, 4] = true := by decide +kernel
theorem sub7_1256 : sub7 [5, 5] = true := by decide +kernel
theorem sub7_1257 : sub7 [5, 6] = true := by decide +kernel
theorem sub7_1258 : sub7 [6, -4] = true := by decide +kernel
theorem sub7_1259 : sub7 [6, -3] = true := by decide +kernel
theorem sub7_1260 : sub7 [6, -2] = true := by decide +kernel
theorem sub7_1261 : sub7 [6, -1] = true := by decide +kernel
theorem sub7_1262 : sub7 [6, 0] = true := by decide +kernel
theorem sub7_1263 : sub7 [6, 1] = true := by decide +kernel
theorem sub7_1264 : sub7 [6, 2] = true := by decide +kernel
theorem sub7_1265 : sub7 [6, 3] = true := by decide +kernel
theorem sub7_1266 : sub7 [6, 4] = true := by decide +kernel
theorem sub7_1267 : sub7 [6, 5] = true := by decide +kernel
theorem sub7_1268 : sub7 [6, 6] = true := by decide +kernel
theorem sub7_1269 : sub7 [7, -3] = true := by decide +kernel
theorem sub7_1270 : sub7 [7, -2] = true := by decide +kernel
theorem sub7_1271 : sub7 [7, -1] = true := by decide +kernel
theorem sub7_1272 : sub7 [7, 0] = true := by decide +kernel
theorem sub7_1273 : sub7 [7, 1] = true := by decide +kernel
theorem sub7_1274 : sub7 [7, 2] = true := by decide +kernel
theorem sub7_1275 : sub7 [7, 3] = true := by decide +kernel
theorem sub7_1276 : sub7 [7, 4] = true := by decide +kernel
theorem sub7_1277 : sub7 [7, 5] = true := by decide +kernel
theorem sub7_1278 : sub7 [8] = true := by decide +kernel
theorem sb7_39 : ∀ q ∈ blk7_39, sub7 q = true := by
  unfold blk7_39
  exact List.forall_mem_cons.2 ⟨sub7_1248, List.forall_mem_cons.2 ⟨sub7_1249, List.forall_mem_cons.2 ⟨sub7_1250, List.forall_mem_cons.2 ⟨sub7_1251, List.forall_mem_cons.2 ⟨sub7_1252, List.forall_mem_cons.2 ⟨sub7_1253, List.forall_mem_cons.2 ⟨sub7_1254, List.forall_mem_cons.2 ⟨sub7_1255, List.forall_mem_cons.2 ⟨sub7_1256, List.forall_mem_cons.2 ⟨sub7_1257, List.forall_mem_cons.2 ⟨sub7_1258, List.forall_mem_cons.2 ⟨sub7_1259, List.forall_mem_cons.2 ⟨sub7_1260, List.forall_mem_cons.2 ⟨sub7_1261, List.forall_mem_cons.2 ⟨sub7_1262, List.forall_mem_cons.2 ⟨sub7_1263, List.forall_mem_cons.2 ⟨sub7_1264, List.forall_mem_cons.2 ⟨sub7_1265, List.forall_mem_cons.2 ⟨sub7_1266, List.forall_mem_cons.2 ⟨sub7_1267, List.forall_mem_cons.2 ⟨sub7_1268, List.forall_mem_cons.2 ⟨sub7_1269, List.forall_mem_cons.2 ⟨sub7_1270, List.forall_mem_cons.2 ⟨sub7_1271, List.forall_mem_cons.2 ⟨sub7_1272, List.forall_mem_cons.2 ⟨sub7_1273, List.forall_mem_cons.2 ⟨sub7_1274, List.forall_mem_cons.2 ⟨sub7_1275, List.forall_mem_cons.2 ⟨sub7_1276, List.forall_mem_cons.2 ⟨sub7_1277, List.forall_mem_cons.2 ⟨sub7_1278, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_0 : sub8 [-7, -2] = true := by decide +kernel
theorem sub8_1 : sub8 [-7, -1] = true := by decide +kernel
theorem sub8_2 : sub8 [-7, 0] = true := by decide +kernel
theorem sub8_3 : sub8 [-7, 1] = true := by decide +kernel
theorem sub8_4 : sub8 [-7, 2] = true := by decide +kernel
theorem sub8_5 : sub8 [-7, 3] = true := by decide +kernel
theorem sub8_6 : sub8 [-7, 4] = true := by decide +kernel
theorem sub8_7 : sub8 [-7, 5] = true := by decide +kernel
theorem sub8_8 : sub8 [-6, -4] = true := by decide +kernel
theorem sub8_9 : sub8 [-6, -3] = true := by decide +kernel
theorem sub8_10 : sub8 [-6, -2] = true := by decide +kernel
theorem sub8_11 : sub8 [-6, -1] = true := by decide +kernel
theorem sub8_12 : sub8 [-6, 0] = true := by decide +kernel
theorem sub8_13 : sub8 [-6, 1] = true := by decide +kernel
theorem sub8_14 : sub8 [-6, 2] = true := by decide +kernel
theorem sub8_15 : sub8 [-6, 3] = true := by decide +kernel
theorem sub8_16 : sub8 [-6, 4] = true := by decide +kernel
theorem sub8_17 : sub8 [-6, 5] = true := by decide +kernel
theorem sub8_18 : sub8 [-6, 6] = true := by decide +kernel
theorem sub8_19 : sub8 [-5, -5] = true := by decide +kernel
theorem sub8_20 : sub8 [-5, -4] = true := by decide +kernel
theorem sub8_21 : sub8 [-5, -3] = true := by decide +kernel
theorem sub8_22 : sub8 [-5, -2] = true := by decide +kernel
theorem sub8_23 : sub8 [-5, -1] = true := by decide +kernel
theorem sub8_24 : sub8 [-5, 0] = true := by decide +kernel
theorem sub8_25 : sub8 [-5, 1] = true := by decide +kernel
theorem sub8_26 : sub8 [-5, 2] = true := by decide +kernel
theorem sub8_27 : sub8 [-5, 3] = true := by decide +kernel
theorem sub8_28 : sub8 [-5, 4] = true := by decide +kernel
theorem sub8_29 : sub8 [-5, 5] = true := by decide +kernel
theorem sub8_30 : sub8 [-5, 6] = true := by decide +kernel
theorem sub8_31 : sub8 [-5, 7] = true := by decide +kernel
theorem sb8_0 : ∀ q ∈ blk8_0, sub8 q = true := by
  unfold blk8_0
  exact List.forall_mem_cons.2 ⟨sub8_0, List.forall_mem_cons.2 ⟨sub8_1, List.forall_mem_cons.2 ⟨sub8_2, List.forall_mem_cons.2 ⟨sub8_3, List.forall_mem_cons.2 ⟨sub8_4, List.forall_mem_cons.2 ⟨sub8_5, List.forall_mem_cons.2 ⟨sub8_6, List.forall_mem_cons.2 ⟨sub8_7, List.forall_mem_cons.2 ⟨sub8_8, List.forall_mem_cons.2 ⟨sub8_9, List.forall_mem_cons.2 ⟨sub8_10, List.forall_mem_cons.2 ⟨sub8_11, List.forall_mem_cons.2 ⟨sub8_12, List.forall_mem_cons.2 ⟨sub8_13, List.forall_mem_cons.2 ⟨sub8_14, List.forall_mem_cons.2 ⟨sub8_15, List.forall_mem_cons.2 ⟨sub8_16, List.forall_mem_cons.2 ⟨sub8_17, List.forall_mem_cons.2 ⟨sub8_18, List.forall_mem_cons.2 ⟨sub8_19, List.forall_mem_cons.2 ⟨sub8_20, List.forall_mem_cons.2 ⟨sub8_21, List.forall_mem_cons.2 ⟨sub8_22, List.forall_mem_cons.2 ⟨sub8_23, List.forall_mem_cons.2 ⟨sub8_24, List.forall_mem_cons.2 ⟨sub8_25, List.forall_mem_cons.2 ⟨sub8_26, List.forall_mem_cons.2 ⟨sub8_27, List.forall_mem_cons.2 ⟨sub8_28, List.forall_mem_cons.2 ⟨sub8_29, List.forall_mem_cons.2 ⟨sub8_30, List.forall_mem_cons.2 ⟨sub8_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C092
