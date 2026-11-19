import ReflectZphi.Data.Cert5.C080.Base

namespace ReflectZphi.Data.Cert5.C080
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub10_1120 : sub10 [2, 1, -11] = true := by decide +kernel
theorem sub10_1121 : sub10 [2, 1, -10] = true := by decide +kernel
theorem sub10_1122 : sub10 [2, 1, -9] = true := by decide +kernel
theorem sub10_1123 : sub10 [2, 1, -8] = true := by decide +kernel
theorem sub10_1124 : sub10 [2, 1, -7] = true := by decide +kernel
theorem sub10_1125 : sub10 [2, 1, -6] = true := by decide +kernel
theorem sub10_1126 : sub10 [2, 1, -5] = true := by decide +kernel
theorem sub10_1127 : sub10 [2, 1, -4] = true := by decide +kernel
theorem sub10_1128 : sub10 [2, 1, -3] = true := by decide +kernel
theorem sub10_1129 : sub10 [2, 1, -2] = true := by decide +kernel
theorem sub10_1130 : sub10 [2, 1, -1] = true := by decide +kernel
theorem sub10_1131 : sub10 [2, 1, 0] = true := by decide +kernel
theorem sub10_1132 : sub10 [2, 1, 1] = true := by decide +kernel
theorem sub10_1133 : sub10 [2, 1, 2] = true := by decide +kernel
theorem sub10_1134 : sub10 [2, 1, 3] = true := by decide +kernel
theorem sub10_1135 : sub10 [2, 1, 4] = true := by decide +kernel
theorem sub10_1136 : sub10 [2, 1, 5] = true := by decide +kernel
theorem sub10_1137 : sub10 [2, 1, 6] = true := by decide +kernel
theorem sub10_1138 : sub10 [2, 1, 7] = true := by decide +kernel
theorem sub10_1139 : sub10 [2, 1, 8] = true := by decide +kernel
theorem sub10_1140 : sub10 [2, 1, 9] = true := by decide +kernel
theorem sub10_1141 : sub10 [2, 1, 10] = true := by decide +kernel
theorem sub10_1142 : sub10 [2, 1, 11] = true := by decide +kernel
theorem sub10_1143 : sub10 [2, 2, -12] = true := by decide +kernel
theorem sub10_1144 : sub10 [2, 2, -11] = true := by decide +kernel
theorem sub10_1145 : sub10 [2, 2, -10] = true := by decide +kernel
theorem sub10_1146 : sub10 [2, 2, -9] = true := by decide +kernel
theorem sub10_1147 : sub10 [2, 2, -8] = true := by decide +kernel
theorem sub10_1148 : sub10 [2, 2, -7] = true := by decide +kernel
theorem sub10_1149 : sub10 [2, 2, -6] = true := by decide +kernel
theorem sub10_1150 : sub10 [2, 2, -5] = true := by decide +kernel
theorem sub10_1151 : sub10 [2, 2, -4] = true := by decide +kernel
theorem sb10_35 : ∀ q ∈ blk10_35, sub10 q = true := by
  unfold blk10_35
  exact List.forall_mem_cons.2 ⟨sub10_1120, List.forall_mem_cons.2 ⟨sub10_1121, List.forall_mem_cons.2 ⟨sub10_1122, List.forall_mem_cons.2 ⟨sub10_1123, List.forall_mem_cons.2 ⟨sub10_1124, List.forall_mem_cons.2 ⟨sub10_1125, List.forall_mem_cons.2 ⟨sub10_1126, List.forall_mem_cons.2 ⟨sub10_1127, List.forall_mem_cons.2 ⟨sub10_1128, List.forall_mem_cons.2 ⟨sub10_1129, List.forall_mem_cons.2 ⟨sub10_1130, List.forall_mem_cons.2 ⟨sub10_1131, List.forall_mem_cons.2 ⟨sub10_1132, List.forall_mem_cons.2 ⟨sub10_1133, List.forall_mem_cons.2 ⟨sub10_1134, List.forall_mem_cons.2 ⟨sub10_1135, List.forall_mem_cons.2 ⟨sub10_1136, List.forall_mem_cons.2 ⟨sub10_1137, List.forall_mem_cons.2 ⟨sub10_1138, List.forall_mem_cons.2 ⟨sub10_1139, List.forall_mem_cons.2 ⟨sub10_1140, List.forall_mem_cons.2 ⟨sub10_1141, List.forall_mem_cons.2 ⟨sub10_1142, List.forall_mem_cons.2 ⟨sub10_1143, List.forall_mem_cons.2 ⟨sub10_1144, List.forall_mem_cons.2 ⟨sub10_1145, List.forall_mem_cons.2 ⟨sub10_1146, List.forall_mem_cons.2 ⟨sub10_1147, List.forall_mem_cons.2 ⟨sub10_1148, List.forall_mem_cons.2 ⟨sub10_1149, List.forall_mem_cons.2 ⟨sub10_1150, List.forall_mem_cons.2 ⟨sub10_1151, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_1152 : sub10 [2, 2, -3] = true := by decide +kernel
theorem sub10_1153 : sub10 [2, 2, -2] = true := by decide +kernel
theorem sub10_1154 : sub10 [2, 2, -1] = true := by decide +kernel
theorem sub10_1155 : sub10 [2, 2, 0] = true := by decide +kernel
theorem sub10_1156 : sub10 [2, 2, 1] = true := by decide +kernel
theorem sub10_1157 : sub10 [2, 2, 2] = true := by decide +kernel
theorem sub10_1158 : sub10 [2, 2, 3] = true := by decide +kernel
theorem sub10_1159 : sub10 [2, 2, 4] = true := by decide +kernel
theorem sub10_1160 : sub10 [2, 2, 5] = true := by decide +kernel
theorem sub10_1161 : sub10 [2, 2, 6] = true := by decide +kernel
theorem sub10_1162 : sub10 [2, 2, 7] = true := by decide +kernel
theorem sub10_1163 : sub10 [2, 2, 8] = true := by decide +kernel
theorem sub10_1164 : sub10 [2, 2, 9] = true := by decide +kernel
theorem sub10_1165 : sub10 [2, 2, 10] = true := by decide +kernel
theorem sub10_1166 : sub10 [2, 3, -11] = true := by decide +kernel
theorem sub10_1167 : sub10 [2, 3, -10] = true := by decide +kernel
theorem sub10_1168 : sub10 [2, 3, -9] = true := by decide +kernel
theorem sub10_1169 : sub10 [2, 3, -8] = true := by decide +kernel
theorem sub10_1170 : sub10 [2, 3, -7] = true := by decide +kernel
theorem sub10_1171 : sub10 [2, 3, -6] = true := by decide +kernel
theorem sub10_1172 : sub10 [2, 3, -5] = true := by decide +kernel
theorem sub10_1173 : sub10 [2, 3, -4] = true := by decide +kernel
theorem sub10_1174 : sub10 [2, 3, -3] = true := by decide +kernel
theorem sub10_1175 : sub10 [2, 3, -2] = true := by decide +kernel
theorem sub10_1176 : sub10 [2, 3, -1] = true := by decide +kernel
theorem sub10_1177 : sub10 [2, 3, 0] = true := by decide +kernel
theorem sub10_1178 : sub10 [2, 3, 1] = true := by decide +kernel
theorem sub10_1179 : sub10 [2, 3, 2] = true := by decide +kernel
theorem sub10_1180 : sub10 [2, 3, 3] = true := by decide +kernel
theorem sub10_1181 : sub10 [2, 3, 4] = true := by decide +kernel
theorem sub10_1182 : sub10 [2, 3, 5] = true := by decide +kernel
theorem sub10_1183 : sub10 [2, 3, 6] = true := by decide +kernel
theorem sb10_36 : ∀ q ∈ blk10_36, sub10 q = true := by
  unfold blk10_36
  exact List.forall_mem_cons.2 ⟨sub10_1152, List.forall_mem_cons.2 ⟨sub10_1153, List.forall_mem_cons.2 ⟨sub10_1154, List.forall_mem_cons.2 ⟨sub10_1155, List.forall_mem_cons.2 ⟨sub10_1156, List.forall_mem_cons.2 ⟨sub10_1157, List.forall_mem_cons.2 ⟨sub10_1158, List.forall_mem_cons.2 ⟨sub10_1159, List.forall_mem_cons.2 ⟨sub10_1160, List.forall_mem_cons.2 ⟨sub10_1161, List.forall_mem_cons.2 ⟨sub10_1162, List.forall_mem_cons.2 ⟨sub10_1163, List.forall_mem_cons.2 ⟨sub10_1164, List.forall_mem_cons.2 ⟨sub10_1165, List.forall_mem_cons.2 ⟨sub10_1166, List.forall_mem_cons.2 ⟨sub10_1167, List.forall_mem_cons.2 ⟨sub10_1168, List.forall_mem_cons.2 ⟨sub10_1169, List.forall_mem_cons.2 ⟨sub10_1170, List.forall_mem_cons.2 ⟨sub10_1171, List.forall_mem_cons.2 ⟨sub10_1172, List.forall_mem_cons.2 ⟨sub10_1173, List.forall_mem_cons.2 ⟨sub10_1174, List.forall_mem_cons.2 ⟨sub10_1175, List.forall_mem_cons.2 ⟨sub10_1176, List.forall_mem_cons.2 ⟨sub10_1177, List.forall_mem_cons.2 ⟨sub10_1178, List.forall_mem_cons.2 ⟨sub10_1179, List.forall_mem_cons.2 ⟨sub10_1180, List.forall_mem_cons.2 ⟨sub10_1181, List.forall_mem_cons.2 ⟨sub10_1182, List.forall_mem_cons.2 ⟨sub10_1183, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_1184 : sub10 [2, 3, 7] = true := by decide +kernel
theorem sub10_1185 : sub10 [2, 3, 8] = true := by decide +kernel
theorem sub10_1186 : sub10 [2, 3, 9] = true := by decide +kernel
theorem sub10_1187 : sub10 [2, 4, -10] = true := by decide +kernel
theorem sub10_1188 : sub10 [2, 4, -9] = true := by decide +kernel
theorem sub10_1189 : sub10 [2, 4, -8] = true := by decide +kernel
theorem sub10_1190 : sub10 [2, 4, -7] = true := by decide +kernel
theorem sub10_1191 : sub10 [2, 4, -6] = true := by decide +kernel
theorem sub10_1192 : sub10 [2, 4, -5] = true := by decide +kernel
theorem sub10_1193 : sub10 [2, 4, -4] = true := by decide +kernel
theorem sub10_1194 : sub10 [2, 4, -3] = true := by decide +kernel
theorem sub10_1195 : sub10 [2, 4, -2] = true := by decide +kernel
theorem sub10_1196 : sub10 [2, 4, -1] = true := by decide +kernel
theorem sub10_1197 : sub10 [2, 4, 0] = true := by decide +kernel
theorem sub10_1198 : sub10 [2, 4, 1] = true := by decide +kernel
theorem sub10_1199 : sub10 [2, 4, 2] = true := by decide +kernel
theorem sub10_1200 : sub10 [2, 4, 3] = true := by decide +kernel
theorem sub10_1201 : sub10 [2, 4, 4] = true := by decide +kernel
theorem sub10_1202 : sub10 [2, 4, 5] = true := by decide +kernel
theorem sub10_1203 : sub10 [2, 4, 6] = true := by decide +kernel
theorem sub10_1204 : sub10 [2, 4, 7] = true := by decide +kernel
theorem sub10_1205 : sub10 [2, 5] = true := by decide +kernel
theorem sub10_1206 : sub10 [3, -5] = true := by decide +kernel
theorem sub10_1207 : sub10 [3, -4] = true := by decide +kernel
theorem sub10_1208 : sub10 [3, -3, -5] = true := by decide +kernel
theorem sub10_1209 : sub10 [3, -3, -4] = true := by decide +kernel
theorem sub10_1210 : sub10 [3, -3, -3] = true := by decide +kernel
theorem sub10_1211 : sub10 [3, -3, -2] = true := by decide +kernel
theorem sub10_1212 : sub10 [3, -3, -1] = true := by decide +kernel
theorem sub10_1213 : sub10 [3, -3, 0] = true := by decide +kernel
theorem sub10_1214 : sub10 [3, -3, 1] = true := by decide +kernel
theorem sub10_1215 : sub10 [3, -3, 2] = true := by decide +kernel
theorem sb10_37 : ∀ q ∈ blk10_37, sub10 q = true := by
  unfold blk10_37
  exact List.forall_mem_cons.2 ⟨sub10_1184, List.forall_mem_cons.2 ⟨sub10_1185, List.forall_mem_cons.2 ⟨sub10_1186, List.forall_mem_cons.2 ⟨sub10_1187, List.forall_mem_cons.2 ⟨sub10_1188, List.forall_mem_cons.2 ⟨sub10_1189, List.forall_mem_cons.2 ⟨sub10_1190, List.forall_mem_cons.2 ⟨sub10_1191, List.forall_mem_cons.2 ⟨sub10_1192, List.forall_mem_cons.2 ⟨sub10_1193, List.forall_mem_cons.2 ⟨sub10_1194, List.forall_mem_cons.2 ⟨sub10_1195, List.forall_mem_cons.2 ⟨sub10_1196, List.forall_mem_cons.2 ⟨sub10_1197, List.forall_mem_cons.2 ⟨sub10_1198, List.forall_mem_cons.2 ⟨sub10_1199, List.forall_mem_cons.2 ⟨sub10_1200, List.forall_mem_cons.2 ⟨sub10_1201, List.forall_mem_cons.2 ⟨sub10_1202, List.forall_mem_cons.2 ⟨sub10_1203, List.forall_mem_cons.2 ⟨sub10_1204, List.forall_mem_cons.2 ⟨sub10_1205, List.forall_mem_cons.2 ⟨sub10_1206, List.forall_mem_cons.2 ⟨sub10_1207, List.forall_mem_cons.2 ⟨sub10_1208, List.forall_mem_cons.2 ⟨sub10_1209, List.forall_mem_cons.2 ⟨sub10_1210, List.forall_mem_cons.2 ⟨sub10_1211, List.forall_mem_cons.2 ⟨sub10_1212, List.forall_mem_cons.2 ⟨sub10_1213, List.forall_mem_cons.2 ⟨sub10_1214, List.forall_mem_cons.2 ⟨sub10_1215, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_1216 : sub10 [3, -3, 3] = true := by decide +kernel
theorem sub10_1217 : sub10 [3, -3, 4] = true := by decide +kernel
theorem sub10_1218 : sub10 [3, -3, 5] = true := by decide +kernel
theorem sub10_1219 : sub10 [3, -3, 6] = true := by decide +kernel
theorem sub10_1220 : sub10 [3, -3, 7] = true := by decide +kernel
theorem sub10_1221 : sub10 [3, -3, 8] = true := by decide +kernel
theorem sub10_1222 : sub10 [3, -2, -7] = true := by decide +kernel
theorem sub10_1223 : sub10 [3, -2, -6] = true := by decide +kernel
theorem sub10_1224 : sub10 [3, -2, -5] = true := by decide +kernel
theorem sub10_1225 : sub10 [3, -2, -4] = true := by decide +kernel
theorem sub10_1226 : sub10 [3, -2, -3] = true := by decide +kernel
theorem sub10_1227 : sub10 [3, -2, -2] = true := by decide +kernel
theorem sub10_1228 : sub10 [3, -2, -1] = true := by decide +kernel
theorem sub10_1229 : sub10 [3, -2, 0] = true := by decide +kernel
theorem sub10_1230 : sub10 [3, -2, 1] = true := by decide +kernel
theorem sub10_1231 : sub10 [3, -2, 2] = true := by decide +kernel
theorem sub10_1232 : sub10 [3, -2, 3] = true := by decide +kernel
theorem sub10_1233 : sub10 [3, -2, 4] = true := by decide +kernel
theorem sub10_1234 : sub10 [3, -2, 5] = true := by decide +kernel
theorem sub10_1235 : sub10 [3, -2, 6] = true := by decide +kernel
theorem sub10_1236 : sub10 [3, -2, 7] = true := by decide +kernel
theorem sub10_1237 : sub10 [3, -2, 8] = true := by decide +kernel
theorem sub10_1238 : sub10 [3, -2, 9] = true := by decide +kernel
theorem sub10_1239 : sub10 [3, -1, -9] = true := by decide +kernel
theorem sub10_1240 : sub10 [3, -1, -8] = true := by decide +kernel
theorem sub10_1241 : sub10 [3, -1, -7] = true := by decide +kernel
theorem sub10_1242 : sub10 [3, -1, -6] = true := by decide +kernel
theorem sub10_1243 : sub10 [3, -1, -5] = true := by decide +kernel
theorem sub10_1244 : sub10 [3, -1, -4] = true := by decide +kernel
theorem sub10_1245 : sub10 [3, -1, -3] = true := by decide +kernel
theorem sub10_1246 : sub10 [3, -1, -2] = true := by decide +kernel
theorem sub10_1247 : sub10 [3, -1, -1] = true := by decide +kernel
theorem sb10_38 : ∀ q ∈ blk10_38, sub10 q = true := by
  unfold blk10_38
  exact List.forall_mem_cons.2 ⟨sub10_1216, List.forall_mem_cons.2 ⟨sub10_1217, List.forall_mem_cons.2 ⟨sub10_1218, List.forall_mem_cons.2 ⟨sub10_1219, List.forall_mem_cons.2 ⟨sub10_1220, List.forall_mem_cons.2 ⟨sub10_1221, List.forall_mem_cons.2 ⟨sub10_1222, List.forall_mem_cons.2 ⟨sub10_1223, List.forall_mem_cons.2 ⟨sub10_1224, List.forall_mem_cons.2 ⟨sub10_1225, List.forall_mem_cons.2 ⟨sub10_1226, List.forall_mem_cons.2 ⟨sub10_1227, List.forall_mem_cons.2 ⟨sub10_1228, List.forall_mem_cons.2 ⟨sub10_1229, List.forall_mem_cons.2 ⟨sub10_1230, List.forall_mem_cons.2 ⟨sub10_1231, List.forall_mem_cons.2 ⟨sub10_1232, List.forall_mem_cons.2 ⟨sub10_1233, List.forall_mem_cons.2 ⟨sub10_1234, List.forall_mem_cons.2 ⟨sub10_1235, List.forall_mem_cons.2 ⟨sub10_1236, List.forall_mem_cons.2 ⟨sub10_1237, List.forall_mem_cons.2 ⟨sub10_1238, List.forall_mem_cons.2 ⟨sub10_1239, List.forall_mem_cons.2 ⟨sub10_1240, List.forall_mem_cons.2 ⟨sub10_1241, List.forall_mem_cons.2 ⟨sub10_1242, List.forall_mem_cons.2 ⟨sub10_1243, List.forall_mem_cons.2 ⟨sub10_1244, List.forall_mem_cons.2 ⟨sub10_1245, List.forall_mem_cons.2 ⟨sub10_1246, List.forall_mem_cons.2 ⟨sub10_1247, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_1248 : sub10 [3, -1, 0] = true := by decide +kernel
theorem sub10_1249 : sub10 [3, -1, 1] = true := by decide +kernel
theorem sub10_1250 : sub10 [3, -1, 2] = true := by decide +kernel
theorem sub10_1251 : sub10 [3, -1, 3] = true := by decide +kernel
theorem sub10_1252 : sub10 [3, -1, 4] = true := by decide +kernel
theorem sub10_1253 : sub10 [3, -1, 5] = true := by decide +kernel
theorem sub10_1254 : sub10 [3, -1, 6] = true := by decide +kernel
theorem sub10_1255 : sub10 [3, -1, 7] = true := by decide +kernel
theorem sub10_1256 : sub10 [3, -1, 8] = true := by decide +kernel
theorem sub10_1257 : sub10 [3, -1, 9] = true := by decide +kernel
theorem sub10_1258 : sub10 [3, -1, 10] = true := by decide +kernel
theorem sub10_1259 : sub10 [3, 0, -10] = true := by decide +kernel
theorem sub10_1260 : sub10 [3, 0, -9] = true := by decide +kernel
theorem sub10_1261 : sub10 [3, 0, -8] = true := by decide +kernel
theorem sub10_1262 : sub10 [3, 0, -7] = true := by decide +kernel
theorem sub10_1263 : sub10 [3, 0, -6] = true := by decide +kernel
theorem sub10_1264 : sub10 [3, 0, -5] = true := by decide +kernel
theorem sub10_1265 : sub10 [3, 0, -4] = true := by decide +kernel
theorem sub10_1266 : sub10 [3, 0, -3] = true := by decide +kernel
theorem sub10_1267 : sub10 [3, 0, -2] = true := by decide +kernel
theorem sub10_1268 : sub10 [3, 0, -1] = true := by decide +kernel
theorem sub10_1269 : sub10 [3, 0, 0] = true := by decide +kernel
theorem sub10_1270 : sub10 [3, 0, 1] = true := by decide +kernel
theorem sub10_1271 : sub10 [3, 0, 2] = true := by decide +kernel
theorem sub10_1272 : sub10 [3, 0, 3] = true := by decide +kernel
theorem sub10_1273 : sub10 [3, 0, 4] = true := by decide +kernel
theorem sub10_1274 : sub10 [3, 0, 5] = true := by decide +kernel
theorem sub10_1275 : sub10 [3, 0, 6] = true := by decide +kernel
theorem sub10_1276 : sub10 [3, 0, 7] = true := by decide +kernel
theorem sub10_1277 : sub10 [3, 0, 8] = true := by decide +kernel
theorem sub10_1278 : sub10 [3, 0, 9] = true := by decide +kernel
theorem sub10_1279 : sub10 [3, 0, 10] = true := by decide +kernel
theorem sb10_39 : ∀ q ∈ blk10_39, sub10 q = true := by
  unfold blk10_39
  exact List.forall_mem_cons.2 ⟨sub10_1248, List.forall_mem_cons.2 ⟨sub10_1249, List.forall_mem_cons.2 ⟨sub10_1250, List.forall_mem_cons.2 ⟨sub10_1251, List.forall_mem_cons.2 ⟨sub10_1252, List.forall_mem_cons.2 ⟨sub10_1253, List.forall_mem_cons.2 ⟨sub10_1254, List.forall_mem_cons.2 ⟨sub10_1255, List.forall_mem_cons.2 ⟨sub10_1256, List.forall_mem_cons.2 ⟨sub10_1257, List.forall_mem_cons.2 ⟨sub10_1258, List.forall_mem_cons.2 ⟨sub10_1259, List.forall_mem_cons.2 ⟨sub10_1260, List.forall_mem_cons.2 ⟨sub10_1261, List.forall_mem_cons.2 ⟨sub10_1262, List.forall_mem_cons.2 ⟨sub10_1263, List.forall_mem_cons.2 ⟨sub10_1264, List.forall_mem_cons.2 ⟨sub10_1265, List.forall_mem_cons.2 ⟨sub10_1266, List.forall_mem_cons.2 ⟨sub10_1267, List.forall_mem_cons.2 ⟨sub10_1268, List.forall_mem_cons.2 ⟨sub10_1269, List.forall_mem_cons.2 ⟨sub10_1270, List.forall_mem_cons.2 ⟨sub10_1271, List.forall_mem_cons.2 ⟨sub10_1272, List.forall_mem_cons.2 ⟨sub10_1273, List.forall_mem_cons.2 ⟨sub10_1274, List.forall_mem_cons.2 ⟨sub10_1275, List.forall_mem_cons.2 ⟨sub10_1276, List.forall_mem_cons.2 ⟨sub10_1277, List.forall_mem_cons.2 ⟨sub10_1278, List.forall_mem_cons.2 ⟨sub10_1279, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_1280 : sub10 [3, 1, -10] = true := by decide +kernel
theorem sub10_1281 : sub10 [3, 1, -9] = true := by decide +kernel
theorem sub10_1282 : sub10 [3, 1, -8] = true := by decide +kernel
theorem sub10_1283 : sub10 [3, 1, -7] = true := by decide +kernel
theorem sub10_1284 : sub10 [3, 1, -6] = true := by decide +kernel
theorem sub10_1285 : sub10 [3, 1, -5] = true := by decide +kernel
theorem sub10_1286 : sub10 [3, 1, -4] = true := by decide +kernel
theorem sub10_1287 : sub10 [3, 1, -3] = true := by decide +kernel
theorem sub10_1288 : sub10 [3, 1, -2] = true := by decide +kernel
theorem sub10_1289 : sub10 [3, 1, -1] = true := by decide +kernel
theorem sub10_1290 : sub10 [3, 1, 0] = true := by decide +kernel
theorem sub10_1291 : sub10 [3, 1, 1] = true := by decide +kernel
theorem sub10_1292 : sub10 [3, 1, 2] = true := by decide +kernel
theorem sub10_1293 : sub10 [3, 1, 3] = true := by decide +kernel
theorem sub10_1294 : sub10 [3, 1, 4] = true := by decide +kernel
theorem sub10_1295 : sub10 [3, 1, 5] = true := by decide +kernel
theorem sub10_1296 : sub10 [3, 1, 6] = true := by decide +kernel
theorem sub10_1297 : sub10 [3, 1, 7] = true := by decide +kernel
theorem sub10_1298 : sub10 [3, 1, 8] = true := by decide +kernel
theorem sub10_1299 : sub10 [3, 1, 9] = true := by decide +kernel
theorem sub10_1300 : sub10 [3, 1, 10] = true := by decide +kernel
theorem sub10_1301 : sub10 [3, 2, -10] = true := by decide +kernel
theorem sub10_1302 : sub10 [3, 2, -9] = true := by decide +kernel
theorem sub10_1303 : sub10 [3, 2, -8] = true := by decide +kernel
theorem sub10_1304 : sub10 [3, 2, -7] = true := by decide +kernel
theorem sub10_1305 : sub10 [3, 2, -6] = true := by decide +kernel
theorem sub10_1306 : sub10 [3, 2, -5] = true := by decide +kernel
theorem sub10_1307 : sub10 [3, 2, -4] = true := by decide +kernel
theorem sub10_1308 : sub10 [3, 2, -3] = true := by decide +kernel
theorem sub10_1309 : sub10 [3, 2, -2] = true := by decide +kernel
theorem sub10_1310 : sub10 [3, 2, -1] = true := by decide +kernel
theorem sub10_1311 : sub10 [3, 2, 0] = true := by decide +kernel
theorem sb10_40 : ∀ q ∈ blk10_40, sub10 q = true := by
  unfold blk10_40
  exact List.forall_mem_cons.2 ⟨sub10_1280, List.forall_mem_cons.2 ⟨sub10_1281, List.forall_mem_cons.2 ⟨sub10_1282, List.forall_mem_cons.2 ⟨sub10_1283, List.forall_mem_cons.2 ⟨sub10_1284, List.forall_mem_cons.2 ⟨sub10_1285, List.forall_mem_cons.2 ⟨sub10_1286, List.forall_mem_cons.2 ⟨sub10_1287, List.forall_mem_cons.2 ⟨sub10_1288, List.forall_mem_cons.2 ⟨sub10_1289, List.forall_mem_cons.2 ⟨sub10_1290, List.forall_mem_cons.2 ⟨sub10_1291, List.forall_mem_cons.2 ⟨sub10_1292, List.forall_mem_cons.2 ⟨sub10_1293, List.forall_mem_cons.2 ⟨sub10_1294, List.forall_mem_cons.2 ⟨sub10_1295, List.forall_mem_cons.2 ⟨sub10_1296, List.forall_mem_cons.2 ⟨sub10_1297, List.forall_mem_cons.2 ⟨sub10_1298, List.forall_mem_cons.2 ⟨sub10_1299, List.forall_mem_cons.2 ⟨sub10_1300, List.forall_mem_cons.2 ⟨sub10_1301, List.forall_mem_cons.2 ⟨sub10_1302, List.forall_mem_cons.2 ⟨sub10_1303, List.forall_mem_cons.2 ⟨sub10_1304, List.forall_mem_cons.2 ⟨sub10_1305, List.forall_mem_cons.2 ⟨sub10_1306, List.forall_mem_cons.2 ⟨sub10_1307, List.forall_mem_cons.2 ⟨sub10_1308, List.forall_mem_cons.2 ⟨sub10_1309, List.forall_mem_cons.2 ⟨sub10_1310, List.forall_mem_cons.2 ⟨sub10_1311, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_1312 : sub10 [3, 2, 1] = true := by decide +kernel
theorem sub10_1313 : sub10 [3, 2, 2] = true := by decide +kernel
theorem sub10_1314 : sub10 [3, 2, 3] = true := by decide +kernel
theorem sub10_1315 : sub10 [3, 2, 4] = true := by decide +kernel
theorem sub10_1316 : sub10 [3, 2, 5] = true := by decide +kernel
theorem sub10_1317 : sub10 [3, 2, 6] = true := by decide +kernel
theorem sub10_1318 : sub10 [3, 2, 7] = true := by decide +kernel
theorem sub10_1319 : sub10 [3, 2, 8] = true := by decide +kernel
theorem sub10_1320 : sub10 [3, 2, 9] = true := by decide +kernel
theorem sub10_1321 : sub10 [3, 3, -9] = true := by decide +kernel
theorem sub10_1322 : sub10 [3, 3, -8] = true := by decide +kernel
theorem sub10_1323 : sub10 [3, 3, -7] = true := by decide +kernel
theorem sub10_1324 : sub10 [3, 3, -6] = true := by decide +kernel
theorem sub10_1325 : sub10 [3, 3, -5] = true := by decide +kernel
theorem sub10_1326 : sub10 [3, 3, -4] = true := by decide +kernel
theorem sub10_1327 : sub10 [3, 3, -3] = true := by decide +kernel
theorem sub10_1328 : sub10 [3, 3, -2] = true := by decide +kernel
theorem sub10_1329 : sub10 [3, 3, -1] = true := by decide +kernel
theorem sub10_1330 : sub10 [3, 3, 0] = true := by decide +kernel
theorem sub10_1331 : sub10 [3, 3, 1] = true := by decide +kernel
theorem sub10_1332 : sub10 [3, 3, 2] = true := by decide +kernel
theorem sub10_1333 : sub10 [3, 3, 3] = true := by decide +kernel
theorem sub10_1334 : sub10 [3, 3, 4] = true := by decide +kernel
theorem sub10_1335 : sub10 [3, 3, 5] = true := by decide +kernel
theorem sub10_1336 : sub10 [3, 3, 6] = true := by decide +kernel
theorem sub10_1337 : sub10 [3, 3, 7] = true := by decide +kernel
theorem sub10_1338 : sub10 [3, 3, 8] = true := by decide +kernel
theorem sub10_1339 : sub10 [3, 4, -8] = true := by decide +kernel
theorem sub10_1340 : sub10 [3, 4, -7] = true := by decide +kernel
theorem sub10_1341 : sub10 [3, 4, -6] = true := by decide +kernel
theorem sub10_1342 : sub10 [3, 4, -5] = true := by decide +kernel
theorem sub10_1343 : sub10 [3, 4, -4] = true := by decide +kernel
theorem sb10_41 : ∀ q ∈ blk10_41, sub10 q = true := by
  unfold blk10_41
  exact List.forall_mem_cons.2 ⟨sub10_1312, List.forall_mem_cons.2 ⟨sub10_1313, List.forall_mem_cons.2 ⟨sub10_1314, List.forall_mem_cons.2 ⟨sub10_1315, List.forall_mem_cons.2 ⟨sub10_1316, List.forall_mem_cons.2 ⟨sub10_1317, List.forall_mem_cons.2 ⟨sub10_1318, List.forall_mem_cons.2 ⟨sub10_1319, List.forall_mem_cons.2 ⟨sub10_1320, List.forall_mem_cons.2 ⟨sub10_1321, List.forall_mem_cons.2 ⟨sub10_1322, List.forall_mem_cons.2 ⟨sub10_1323, List.forall_mem_cons.2 ⟨sub10_1324, List.forall_mem_cons.2 ⟨sub10_1325, List.forall_mem_cons.2 ⟨sub10_1326, List.forall_mem_cons.2 ⟨sub10_1327, List.forall_mem_cons.2 ⟨sub10_1328, List.forall_mem_cons.2 ⟨sub10_1329, List.forall_mem_cons.2 ⟨sub10_1330, List.forall_mem_cons.2 ⟨sub10_1331, List.forall_mem_cons.2 ⟨sub10_1332, List.forall_mem_cons.2 ⟨sub10_1333, List.forall_mem_cons.2 ⟨sub10_1334, List.forall_mem_cons.2 ⟨sub10_1335, List.forall_mem_cons.2 ⟨sub10_1336, List.forall_mem_cons.2 ⟨sub10_1337, List.forall_mem_cons.2 ⟨sub10_1338, List.forall_mem_cons.2 ⟨sub10_1339, List.forall_mem_cons.2 ⟨sub10_1340, List.forall_mem_cons.2 ⟨sub10_1341, List.forall_mem_cons.2 ⟨sub10_1342, List.forall_mem_cons.2 ⟨sub10_1343, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_1344 : sub10 [3, 4, -3] = true := by decide +kernel
theorem sub10_1345 : sub10 [3, 4, -2] = true := by decide +kernel
theorem sub10_1346 : sub10 [3, 4, -1] = true := by decide +kernel
theorem sub10_1347 : sub10 [3, 4, 0] = true := by decide +kernel
theorem sub10_1348 : sub10 [3, 4, 1] = true := by decide +kernel
theorem sub10_1349 : sub10 [3, 4, 2] = true := by decide +kernel
theorem sub10_1350 : sub10 [3, 4, 3] = true := by decide +kernel
theorem sub10_1351 : sub10 [3, 4, 4] = true := by decide +kernel
theorem sub10_1352 : sub10 [3, 4, 5] = true := by decide +kernel
theorem sub10_1353 : sub10 [3, 4, 6] = true := by decide +kernel
theorem sub10_1354 : sub10 [3, 5] = true := by decide +kernel
theorem sub10_1355 : sub10 [4, -3] = true := by decide +kernel
theorem sub10_1356 : sub10 [4, -2] = true := by decide +kernel
theorem sub10_1357 : sub10 [4, -1, -6] = true := by decide +kernel
theorem sub10_1358 : sub10 [4, -1, -5] = true := by decide +kernel
theorem sub10_1359 : sub10 [4, -1, -4] = true := by decide +kernel
theorem sub10_1360 : sub10 [4, -1, -3] = true := by decide +kernel
theorem sub10_1361 : sub10 [4, -1, -2] = true := by decide +kernel
theorem sub10_1362 : sub10 [4, -1, -1] = true := by decide +kernel
theorem sub10_1363 : sub10 [4, -1, 0] = true := by decide +kernel
theorem sub10_1364 : sub10 [4, -1, 1] = true := by decide +kernel
theorem sub10_1365 : sub10 [4, -1, 2] = true := by decide +kernel
theorem sub10_1366 : sub10 [4, -1, 3] = true := by decide +kernel
theorem sub10_1367 : sub10 [4, -1, 4] = true := by decide +kernel
theorem sub10_1368 : sub10 [4, -1, 5] = true := by decide +kernel
theorem sub10_1369 : sub10 [4, -1, 6] = true := by decide +kernel
theorem sub10_1370 : sub10 [4, -1, 7] = true := by decide +kernel
theorem sub10_1371 : sub10 [4, -1, 8] = true := by decide +kernel
theorem sub10_1372 : sub10 [4, 0, -7] = true := by decide +kernel
theorem sub10_1373 : sub10 [4, 0, -6] = true := by decide +kernel
theorem sub10_1374 : sub10 [4, 0, -5] = true := by decide +kernel
theorem sub10_1375 : sub10 [4, 0, -4] = true := by decide +kernel
theorem sb10_42 : ∀ q ∈ blk10_42, sub10 q = true := by
  unfold blk10_42
  exact List.forall_mem_cons.2 ⟨sub10_1344, List.forall_mem_cons.2 ⟨sub10_1345, List.forall_mem_cons.2 ⟨sub10_1346, List.forall_mem_cons.2 ⟨sub10_1347, List.forall_mem_cons.2 ⟨sub10_1348, List.forall_mem_cons.2 ⟨sub10_1349, List.forall_mem_cons.2 ⟨sub10_1350, List.forall_mem_cons.2 ⟨sub10_1351, List.forall_mem_cons.2 ⟨sub10_1352, List.forall_mem_cons.2 ⟨sub10_1353, List.forall_mem_cons.2 ⟨sub10_1354, List.forall_mem_cons.2 ⟨sub10_1355, List.forall_mem_cons.2 ⟨sub10_1356, List.forall_mem_cons.2 ⟨sub10_1357, List.forall_mem_cons.2 ⟨sub10_1358, List.forall_mem_cons.2 ⟨sub10_1359, List.forall_mem_cons.2 ⟨sub10_1360, List.forall_mem_cons.2 ⟨sub10_1361, List.forall_mem_cons.2 ⟨sub10_1362, List.forall_mem_cons.2 ⟨sub10_1363, List.forall_mem_cons.2 ⟨sub10_1364, List.forall_mem_cons.2 ⟨sub10_1365, List.forall_mem_cons.2 ⟨sub10_1366, List.forall_mem_cons.2 ⟨sub10_1367, List.forall_mem_cons.2 ⟨sub10_1368, List.forall_mem_cons.2 ⟨sub10_1369, List.forall_mem_cons.2 ⟨sub10_1370, List.forall_mem_cons.2 ⟨sub10_1371, List.forall_mem_cons.2 ⟨sub10_1372, List.forall_mem_cons.2 ⟨sub10_1373, List.forall_mem_cons.2 ⟨sub10_1374, List.forall_mem_cons.2 ⟨sub10_1375, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_1376 : sub10 [4, 0, -3] = true := by decide +kernel
theorem sub10_1377 : sub10 [4, 0, -2] = true := by decide +kernel
theorem sub10_1378 : sub10 [4, 0, -1] = true := by decide +kernel
theorem sub10_1379 : sub10 [4, 0, 0] = true := by decide +kernel
theorem sub10_1380 : sub10 [4, 0, 1] = true := by decide +kernel
theorem sub10_1381 : sub10 [4, 0, 2] = true := by decide +kernel
theorem sub10_1382 : sub10 [4, 0, 3] = true := by decide +kernel
theorem sub10_1383 : sub10 [4, 0, 4] = true := by decide +kernel
theorem sub10_1384 : sub10 [4, 0, 5] = true := by decide +kernel
theorem sub10_1385 : sub10 [4, 0, 6] = true := by decide +kernel
theorem sub10_1386 : sub10 [4, 0, 7] = true := by decide +kernel
theorem sub10_1387 : sub10 [4, 0, 8] = true := by decide +kernel
theorem sub10_1388 : sub10 [4, 1, -8] = true := by decide +kernel
theorem sub10_1389 : sub10 [4, 1, -7] = true := by decide +kernel
theorem sub10_1390 : sub10 [4, 1, -6] = true := by decide +kernel
theorem sub10_1391 : sub10 [4, 1, -5] = true := by decide +kernel
theorem sub10_1392 : sub10 [4, 1, -4] = true := by decide +kernel
theorem sub10_1393 : sub10 [4, 1, -3] = true := by decide +kernel
theorem sub10_1394 : sub10 [4, 1, -2] = true := by decide +kernel
theorem sub10_1395 : sub10 [4, 1, -1] = true := by decide +kernel
theorem sub10_1396 : sub10 [4, 1, 0] = true := by decide +kernel
theorem sub10_1397 : sub10 [4, 1, 1] = true := by decide +kernel
theorem sub10_1398 : sub10 [4, 1, 2] = true := by decide +kernel
theorem sub10_1399 : sub10 [4, 1, 3] = true := by decide +kernel
theorem sub10_1400 : sub10 [4, 1, 4] = true := by decide +kernel
theorem sub10_1401 : sub10 [4, 1, 5] = true := by decide +kernel
theorem sub10_1402 : sub10 [4, 1, 6] = true := by decide +kernel
theorem sub10_1403 : sub10 [4, 1, 7] = true := by decide +kernel
theorem sub10_1404 : sub10 [4, 1, 8] = true := by decide +kernel
theorem sub10_1405 : sub10 [4, 2, -8] = true := by decide +kernel
theorem sub10_1406 : sub10 [4, 2, -7] = true := by decide +kernel
theorem sub10_1407 : sub10 [4, 2, -6] = true := by decide +kernel
theorem sb10_43 : ∀ q ∈ blk10_43, sub10 q = true := by
  unfold blk10_43
  exact List.forall_mem_cons.2 ⟨sub10_1376, List.forall_mem_cons.2 ⟨sub10_1377, List.forall_mem_cons.2 ⟨sub10_1378, List.forall_mem_cons.2 ⟨sub10_1379, List.forall_mem_cons.2 ⟨sub10_1380, List.forall_mem_cons.2 ⟨sub10_1381, List.forall_mem_cons.2 ⟨sub10_1382, List.forall_mem_cons.2 ⟨sub10_1383, List.forall_mem_cons.2 ⟨sub10_1384, List.forall_mem_cons.2 ⟨sub10_1385, List.forall_mem_cons.2 ⟨sub10_1386, List.forall_mem_cons.2 ⟨sub10_1387, List.forall_mem_cons.2 ⟨sub10_1388, List.forall_mem_cons.2 ⟨sub10_1389, List.forall_mem_cons.2 ⟨sub10_1390, List.forall_mem_cons.2 ⟨sub10_1391, List.forall_mem_cons.2 ⟨sub10_1392, List.forall_mem_cons.2 ⟨sub10_1393, List.forall_mem_cons.2 ⟨sub10_1394, List.forall_mem_cons.2 ⟨sub10_1395, List.forall_mem_cons.2 ⟨sub10_1396, List.forall_mem_cons.2 ⟨sub10_1397, List.forall_mem_cons.2 ⟨sub10_1398, List.forall_mem_cons.2 ⟨sub10_1399, List.forall_mem_cons.2 ⟨sub10_1400, List.forall_mem_cons.2 ⟨sub10_1401, List.forall_mem_cons.2 ⟨sub10_1402, List.forall_mem_cons.2 ⟨sub10_1403, List.forall_mem_cons.2 ⟨sub10_1404, List.forall_mem_cons.2 ⟨sub10_1405, List.forall_mem_cons.2 ⟨sub10_1406, List.forall_mem_cons.2 ⟨sub10_1407, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_1408 : sub10 [4, 2, -5] = true := by decide +kernel
theorem sub10_1409 : sub10 [4, 2, -4] = true := by decide +kernel
theorem sub10_1410 : sub10 [4, 2, -3] = true := by decide +kernel
theorem sub10_1411 : sub10 [4, 2, -2] = true := by decide +kernel
theorem sub10_1412 : sub10 [4, 2, -1] = true := by decide +kernel
theorem sub10_1413 : sub10 [4, 2, 0] = true := by decide +kernel
theorem sub10_1414 : sub10 [4, 2, 1] = true := by decide +kernel
theorem sub10_1415 : sub10 [4, 2, 2] = true := by decide +kernel
theorem sub10_1416 : sub10 [4, 2, 3] = true := by decide +kernel
theorem sub10_1417 : sub10 [4, 2, 4] = true := by decide +kernel
theorem sub10_1418 : sub10 [4, 2, 5] = true := by decide +kernel
theorem sub10_1419 : sub10 [4, 2, 6] = true := by decide +kernel
theorem sub10_1420 : sub10 [4, 2, 7] = true := by decide +kernel
theorem sub10_1421 : sub10 [4, 3, -7] = true := by decide +kernel
theorem sub10_1422 : sub10 [4, 3, -6] = true := by decide +kernel
theorem sub10_1423 : sub10 [4, 3, -5] = true := by decide +kernel
theorem sub10_1424 : sub10 [4, 3, -4] = true := by decide +kernel
theorem sub10_1425 : sub10 [4, 3, -3] = true := by decide +kernel
theorem sub10_1426 : sub10 [4, 3, -2] = true := by decide +kernel
theorem sub10_1427 : sub10 [4, 3, -1] = true := by decide +kernel
theorem sub10_1428 : sub10 [4, 3, 0] = true := by decide +kernel
theorem sub10_1429 : sub10 [4, 3, 1] = true := by decide +kernel
theorem sub10_1430 : sub10 [4, 3, 2] = true := by decide +kernel
theorem sub10_1431 : sub10 [4, 3, 3] = true := by decide +kernel
theorem sub10_1432 : sub10 [4, 3, 4] = true := by decide +kernel
theorem sub10_1433 : sub10 [4, 3, 5] = true := by decide +kernel
theorem sub10_1434 : sub10 [4, 3, 6] = true := by decide +kernel
theorem sub10_1435 : sub10 [4, 4] = true := by decide +kernel
theorem sub10_1436 : sub10 [5] = true := by decide +kernel
theorem sb10_44 : ∀ q ∈ blk10_44, sub10 q = true := by
  unfold blk10_44
  exact List.forall_mem_cons.2 ⟨sub10_1408, List.forall_mem_cons.2 ⟨sub10_1409, List.forall_mem_cons.2 ⟨sub10_1410, List.forall_mem_cons.2 ⟨sub10_1411, List.forall_mem_cons.2 ⟨sub10_1412, List.forall_mem_cons.2 ⟨sub10_1413, List.forall_mem_cons.2 ⟨sub10_1414, List.forall_mem_cons.2 ⟨sub10_1415, List.forall_mem_cons.2 ⟨sub10_1416, List.forall_mem_cons.2 ⟨sub10_1417, List.forall_mem_cons.2 ⟨sub10_1418, List.forall_mem_cons.2 ⟨sub10_1419, List.forall_mem_cons.2 ⟨sub10_1420, List.forall_mem_cons.2 ⟨sub10_1421, List.forall_mem_cons.2 ⟨sub10_1422, List.forall_mem_cons.2 ⟨sub10_1423, List.forall_mem_cons.2 ⟨sub10_1424, List.forall_mem_cons.2 ⟨sub10_1425, List.forall_mem_cons.2 ⟨sub10_1426, List.forall_mem_cons.2 ⟨sub10_1427, List.forall_mem_cons.2 ⟨sub10_1428, List.forall_mem_cons.2 ⟨sub10_1429, List.forall_mem_cons.2 ⟨sub10_1430, List.forall_mem_cons.2 ⟨sub10_1431, List.forall_mem_cons.2 ⟨sub10_1432, List.forall_mem_cons.2 ⟨sub10_1433, List.forall_mem_cons.2 ⟨sub10_1434, List.forall_mem_cons.2 ⟨sub10_1435, List.forall_mem_cons.2 ⟨sub10_1436, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C080
