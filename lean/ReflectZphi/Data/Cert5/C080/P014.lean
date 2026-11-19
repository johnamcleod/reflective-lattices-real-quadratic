import ReflectZphi.Data.Cert5.C080.Base

namespace ReflectZphi.Data.Cert5.C080
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub8_1152 : sub8 [3, 1, 5] = true := by decide +kernel
theorem sub8_1153 : sub8 [3, 1, 6] = true := by decide +kernel
theorem sub8_1154 : sub8 [3, 1, 7] = true := by decide +kernel
theorem sub8_1155 : sub8 [3, 2, -10] = true := by decide +kernel
theorem sub8_1156 : sub8 [3, 2, -9] = true := by decide +kernel
theorem sub8_1157 : sub8 [3, 2, -8] = true := by decide +kernel
theorem sub8_1158 : sub8 [3, 2, -7] = true := by decide +kernel
theorem sub8_1159 : sub8 [3, 2, -6] = true := by decide +kernel
theorem sub8_1160 : sub8 [3, 2, -5] = true := by decide +kernel
theorem sub8_1161 : sub8 [3, 2, -4] = true := by decide +kernel
theorem sub8_1162 : sub8 [3, 2, -3] = true := by decide +kernel
theorem sub8_1163 : sub8 [3, 2, -2] = true := by decide +kernel
theorem sub8_1164 : sub8 [3, 2, -1] = true := by decide +kernel
theorem sub8_1165 : sub8 [3, 2, 0] = true := by decide +kernel
theorem sub8_1166 : sub8 [3, 2, 1] = true := by decide +kernel
theorem sub8_1167 : sub8 [3, 2, 2] = true := by decide +kernel
theorem sub8_1168 : sub8 [3, 2, 3] = true := by decide +kernel
theorem sub8_1169 : sub8 [3, 2, 4] = true := by decide +kernel
theorem sub8_1170 : sub8 [3, 2, 5] = true := by decide +kernel
theorem sub8_1171 : sub8 [3, 2, 6] = true := by decide +kernel
theorem sub8_1172 : sub8 [3, 3, -9] = true := by decide +kernel
theorem sub8_1173 : sub8 [3, 3, -8] = true := by decide +kernel
theorem sub8_1174 : sub8 [3, 3, -7] = true := by decide +kernel
theorem sub8_1175 : sub8 [3, 3, -6] = true := by decide +kernel
theorem sub8_1176 : sub8 [3, 3, -5] = true := by decide +kernel
theorem sub8_1177 : sub8 [3, 3, -4] = true := by decide +kernel
theorem sub8_1178 : sub8 [3, 3, -3] = true := by decide +kernel
theorem sub8_1179 : sub8 [3, 3, -2] = true := by decide +kernel
theorem sub8_1180 : sub8 [3, 3, -1] = true := by decide +kernel
theorem sub8_1181 : sub8 [3, 3, 0] = true := by decide +kernel
theorem sub8_1182 : sub8 [3, 3, 1] = true := by decide +kernel
theorem sub8_1183 : sub8 [3, 3, 2] = true := by decide +kernel
theorem sb8_36 : ∀ q ∈ blk8_36, sub8 q = true := by
  unfold blk8_36
  exact List.forall_mem_cons.2 ⟨sub8_1152, List.forall_mem_cons.2 ⟨sub8_1153, List.forall_mem_cons.2 ⟨sub8_1154, List.forall_mem_cons.2 ⟨sub8_1155, List.forall_mem_cons.2 ⟨sub8_1156, List.forall_mem_cons.2 ⟨sub8_1157, List.forall_mem_cons.2 ⟨sub8_1158, List.forall_mem_cons.2 ⟨sub8_1159, List.forall_mem_cons.2 ⟨sub8_1160, List.forall_mem_cons.2 ⟨sub8_1161, List.forall_mem_cons.2 ⟨sub8_1162, List.forall_mem_cons.2 ⟨sub8_1163, List.forall_mem_cons.2 ⟨sub8_1164, List.forall_mem_cons.2 ⟨sub8_1165, List.forall_mem_cons.2 ⟨sub8_1166, List.forall_mem_cons.2 ⟨sub8_1167, List.forall_mem_cons.2 ⟨sub8_1168, List.forall_mem_cons.2 ⟨sub8_1169, List.forall_mem_cons.2 ⟨sub8_1170, List.forall_mem_cons.2 ⟨sub8_1171, List.forall_mem_cons.2 ⟨sub8_1172, List.forall_mem_cons.2 ⟨sub8_1173, List.forall_mem_cons.2 ⟨sub8_1174, List.forall_mem_cons.2 ⟨sub8_1175, List.forall_mem_cons.2 ⟨sub8_1176, List.forall_mem_cons.2 ⟨sub8_1177, List.forall_mem_cons.2 ⟨sub8_1178, List.forall_mem_cons.2 ⟨sub8_1179, List.forall_mem_cons.2 ⟨sub8_1180, List.forall_mem_cons.2 ⟨sub8_1181, List.forall_mem_cons.2 ⟨sub8_1182, List.forall_mem_cons.2 ⟨sub8_1183, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_1184 : sub8 [3, 3, 3] = true := by decide +kernel
theorem sub8_1185 : sub8 [3, 3, 4] = true := by decide +kernel
theorem sub8_1186 : sub8 [3, 3, 5] = true := by decide +kernel
theorem sub8_1187 : sub8 [3, 3, 6] = true := by decide +kernel
theorem sub8_1188 : sub8 [3, 4, -8] = true := by decide +kernel
theorem sub8_1189 : sub8 [3, 4, -7] = true := by decide +kernel
theorem sub8_1190 : sub8 [3, 4, -6] = true := by decide +kernel
theorem sub8_1191 : sub8 [3, 4, -5] = true := by decide +kernel
theorem sub8_1192 : sub8 [3, 4, -4] = true := by decide +kernel
theorem sub8_1193 : sub8 [3, 4, -3] = true := by decide +kernel
theorem sub8_1194 : sub8 [3, 4, -2] = true := by decide +kernel
theorem sub8_1195 : sub8 [3, 4, -1] = true := by decide +kernel
theorem sub8_1196 : sub8 [3, 4, 0] = true := by decide +kernel
theorem sub8_1197 : sub8 [3, 4, 1] = true := by decide +kernel
theorem sub8_1198 : sub8 [3, 4, 2] = true := by decide +kernel
theorem sub8_1199 : sub8 [3, 4, 3] = true := by decide +kernel
theorem sub8_1200 : sub8 [3, 4, 4] = true := by decide +kernel
theorem sub8_1201 : sub8 [3, 4, 5] = true := by decide +kernel
theorem sub8_1202 : sub8 [3, 5] = true := by decide +kernel
theorem sub8_1203 : sub8 [4, -5] = true := by decide +kernel
theorem sub8_1204 : sub8 [4, -4] = true := by decide +kernel
theorem sub8_1205 : sub8 [4, -3] = true := by decide +kernel
theorem sub8_1206 : sub8 [4, -2, -8] = true := by decide +kernel
theorem sub8_1207 : sub8 [4, -2, -7] = true := by decide +kernel
theorem sub8_1208 : sub8 [4, -2, -6] = true := by decide +kernel
theorem sub8_1209 : sub8 [4, -2, -5] = true := by decide +kernel
theorem sub8_1210 : sub8 [4, -2, -4] = true := by decide +kernel
theorem sub8_1211 : sub8 [4, -2, -3] = true := by decide +kernel
theorem sub8_1212 : sub8 [4, -2, -2] = true := by decide +kernel
theorem sub8_1213 : sub8 [4, -2, -1] = true := by decide +kernel
theorem sub8_1214 : sub8 [4, -2, 0] = true := by decide +kernel
theorem sub8_1215 : sub8 [4, -2, 1] = true := by decide +kernel
theorem sb8_37 : ∀ q ∈ blk8_37, sub8 q = true := by
  unfold blk8_37
  exact List.forall_mem_cons.2 ⟨sub8_1184, List.forall_mem_cons.2 ⟨sub8_1185, List.forall_mem_cons.2 ⟨sub8_1186, List.forall_mem_cons.2 ⟨sub8_1187, List.forall_mem_cons.2 ⟨sub8_1188, List.forall_mem_cons.2 ⟨sub8_1189, List.forall_mem_cons.2 ⟨sub8_1190, List.forall_mem_cons.2 ⟨sub8_1191, List.forall_mem_cons.2 ⟨sub8_1192, List.forall_mem_cons.2 ⟨sub8_1193, List.forall_mem_cons.2 ⟨sub8_1194, List.forall_mem_cons.2 ⟨sub8_1195, List.forall_mem_cons.2 ⟨sub8_1196, List.forall_mem_cons.2 ⟨sub8_1197, List.forall_mem_cons.2 ⟨sub8_1198, List.forall_mem_cons.2 ⟨sub8_1199, List.forall_mem_cons.2 ⟨sub8_1200, List.forall_mem_cons.2 ⟨sub8_1201, List.forall_mem_cons.2 ⟨sub8_1202, List.forall_mem_cons.2 ⟨sub8_1203, List.forall_mem_cons.2 ⟨sub8_1204, List.forall_mem_cons.2 ⟨sub8_1205, List.forall_mem_cons.2 ⟨sub8_1206, List.forall_mem_cons.2 ⟨sub8_1207, List.forall_mem_cons.2 ⟨sub8_1208, List.forall_mem_cons.2 ⟨sub8_1209, List.forall_mem_cons.2 ⟨sub8_1210, List.forall_mem_cons.2 ⟨sub8_1211, List.forall_mem_cons.2 ⟨sub8_1212, List.forall_mem_cons.2 ⟨sub8_1213, List.forall_mem_cons.2 ⟨sub8_1214, List.forall_mem_cons.2 ⟨sub8_1215, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_1216 : sub8 [4, -2, 2] = true := by decide +kernel
theorem sub8_1217 : sub8 [4, -2, 3] = true := by decide +kernel
theorem sub8_1218 : sub8 [4, -2, 4] = true := by decide +kernel
theorem sub8_1219 : sub8 [4, -1, -9] = true := by decide +kernel
theorem sub8_1220 : sub8 [4, -1, -8] = true := by decide +kernel
theorem sub8_1221 : sub8 [4, -1, -7] = true := by decide +kernel
theorem sub8_1222 : sub8 [4, -1, -6] = true := by decide +kernel
theorem sub8_1223 : sub8 [4, -1, -5] = true := by decide +kernel
theorem sub8_1224 : sub8 [4, -1, -4] = true := by decide +kernel
theorem sub8_1225 : sub8 [4, -1, -3] = true := by decide +kernel
theorem sub8_1226 : sub8 [4, -1, -2] = true := by decide +kernel
theorem sub8_1227 : sub8 [4, -1, -1] = true := by decide +kernel
theorem sub8_1228 : sub8 [4, -1, 0] = true := by decide +kernel
theorem sub8_1229 : sub8 [4, -1, 1] = true := by decide +kernel
theorem sub8_1230 : sub8 [4, -1, 2] = true := by decide +kernel
theorem sub8_1231 : sub8 [4, -1, 3] = true := by decide +kernel
theorem sub8_1232 : sub8 [4, -1, 4] = true := by decide +kernel
theorem sub8_1233 : sub8 [4, -1, 5] = true := by decide +kernel
theorem sub8_1234 : sub8 [4, 0, -10] = true := by decide +kernel
theorem sub8_1235 : sub8 [4, 0, -9] = true := by decide +kernel
theorem sub8_1236 : sub8 [4, 0, -8] = true := by decide +kernel
theorem sub8_1237 : sub8 [4, 0, -7] = true := by decide +kernel
theorem sub8_1238 : sub8 [4, 0, -6] = true := by decide +kernel
theorem sub8_1239 : sub8 [4, 0, -5] = true := by decide +kernel
theorem sub8_1240 : sub8 [4, 0, -4] = true := by decide +kernel
theorem sub8_1241 : sub8 [4, 0, -3] = true := by decide +kernel
theorem sub8_1242 : sub8 [4, 0, -2] = true := by decide +kernel
theorem sub8_1243 : sub8 [4, 0, -1] = true := by decide +kernel
theorem sub8_1244 : sub8 [4, 0, 0] = true := by decide +kernel
theorem sub8_1245 : sub8 [4, 0, 1] = true := by decide +kernel
theorem sub8_1246 : sub8 [4, 0, 2] = true := by decide +kernel
theorem sub8_1247 : sub8 [4, 0, 3] = true := by decide +kernel
theorem sb8_38 : ∀ q ∈ blk8_38, sub8 q = true := by
  unfold blk8_38
  exact List.forall_mem_cons.2 ⟨sub8_1216, List.forall_mem_cons.2 ⟨sub8_1217, List.forall_mem_cons.2 ⟨sub8_1218, List.forall_mem_cons.2 ⟨sub8_1219, List.forall_mem_cons.2 ⟨sub8_1220, List.forall_mem_cons.2 ⟨sub8_1221, List.forall_mem_cons.2 ⟨sub8_1222, List.forall_mem_cons.2 ⟨sub8_1223, List.forall_mem_cons.2 ⟨sub8_1224, List.forall_mem_cons.2 ⟨sub8_1225, List.forall_mem_cons.2 ⟨sub8_1226, List.forall_mem_cons.2 ⟨sub8_1227, List.forall_mem_cons.2 ⟨sub8_1228, List.forall_mem_cons.2 ⟨sub8_1229, List.forall_mem_cons.2 ⟨sub8_1230, List.forall_mem_cons.2 ⟨sub8_1231, List.forall_mem_cons.2 ⟨sub8_1232, List.forall_mem_cons.2 ⟨sub8_1233, List.forall_mem_cons.2 ⟨sub8_1234, List.forall_mem_cons.2 ⟨sub8_1235, List.forall_mem_cons.2 ⟨sub8_1236, List.forall_mem_cons.2 ⟨sub8_1237, List.forall_mem_cons.2 ⟨sub8_1238, List.forall_mem_cons.2 ⟨sub8_1239, List.forall_mem_cons.2 ⟨sub8_1240, List.forall_mem_cons.2 ⟨sub8_1241, List.forall_mem_cons.2 ⟨sub8_1242, List.forall_mem_cons.2 ⟨sub8_1243, List.forall_mem_cons.2 ⟨sub8_1244, List.forall_mem_cons.2 ⟨sub8_1245, List.forall_mem_cons.2 ⟨sub8_1246, List.forall_mem_cons.2 ⟨sub8_1247, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_1248 : sub8 [4, 0, 4] = true := by decide +kernel
theorem sub8_1249 : sub8 [4, 0, 5] = true := by decide +kernel
theorem sub8_1250 : sub8 [4, 1, -10] = true := by decide +kernel
theorem sub8_1251 : sub8 [4, 1, -9] = true := by decide +kernel
theorem sub8_1252 : sub8 [4, 1, -8] = true := by decide +kernel
theorem sub8_1253 : sub8 [4, 1, -7] = true := by decide +kernel
theorem sub8_1254 : sub8 [4, 1, -6] = true := by decide +kernel
theorem sub8_1255 : sub8 [4, 1, -5] = true := by decide +kernel
theorem sub8_1256 : sub8 [4, 1, -4] = true := by decide +kernel
theorem sub8_1257 : sub8 [4, 1, -3] = true := by decide +kernel
theorem sub8_1258 : sub8 [4, 1, -2] = true := by decide +kernel
theorem sub8_1259 : sub8 [4, 1, -1] = true := by decide +kernel
theorem sub8_1260 : sub8 [4, 1, 0] = true := by decide +kernel
theorem sub8_1261 : sub8 [4, 1, 1] = true := by decide +kernel
theorem sub8_1262 : sub8 [4, 1, 2] = true := by decide +kernel
theorem sub8_1263 : sub8 [4, 1, 3] = true := by decide +kernel
theorem sub8_1264 : sub8 [4, 1, 4] = true := by decide +kernel
theorem sub8_1265 : sub8 [4, 1, 5] = true := by decide +kernel
theorem sub8_1266 : sub8 [4, 1, 6] = true := by decide +kernel
theorem sub8_1267 : sub8 [4, 2, -10] = true := by decide +kernel
theorem sub8_1268 : sub8 [4, 2, -9] = true := by decide +kernel
theorem sub8_1269 : sub8 [4, 2, -8] = true := by decide +kernel
theorem sub8_1270 : sub8 [4, 2, -7] = true := by decide +kernel
theorem sub8_1271 : sub8 [4, 2, -6] = true := by decide +kernel
theorem sub8_1272 : sub8 [4, 2, -5] = true := by decide +kernel
theorem sub8_1273 : sub8 [4, 2, -4] = true := by decide +kernel
theorem sub8_1274 : sub8 [4, 2, -3] = true := by decide +kernel
theorem sub8_1275 : sub8 [4, 2, -2] = true := by decide +kernel
theorem sub8_1276 : sub8 [4, 2, -1] = true := by decide +kernel
theorem sub8_1277 : sub8 [4, 2, 0] = true := by decide +kernel
theorem sub8_1278 : sub8 [4, 2, 1] = true := by decide +kernel
theorem sub8_1279 : sub8 [4, 2, 2] = true := by decide +kernel
theorem sb8_39 : ∀ q ∈ blk8_39, sub8 q = true := by
  unfold blk8_39
  exact List.forall_mem_cons.2 ⟨sub8_1248, List.forall_mem_cons.2 ⟨sub8_1249, List.forall_mem_cons.2 ⟨sub8_1250, List.forall_mem_cons.2 ⟨sub8_1251, List.forall_mem_cons.2 ⟨sub8_1252, List.forall_mem_cons.2 ⟨sub8_1253, List.forall_mem_cons.2 ⟨sub8_1254, List.forall_mem_cons.2 ⟨sub8_1255, List.forall_mem_cons.2 ⟨sub8_1256, List.forall_mem_cons.2 ⟨sub8_1257, List.forall_mem_cons.2 ⟨sub8_1258, List.forall_mem_cons.2 ⟨sub8_1259, List.forall_mem_cons.2 ⟨sub8_1260, List.forall_mem_cons.2 ⟨sub8_1261, List.forall_mem_cons.2 ⟨sub8_1262, List.forall_mem_cons.2 ⟨sub8_1263, List.forall_mem_cons.2 ⟨sub8_1264, List.forall_mem_cons.2 ⟨sub8_1265, List.forall_mem_cons.2 ⟨sub8_1266, List.forall_mem_cons.2 ⟨sub8_1267, List.forall_mem_cons.2 ⟨sub8_1268, List.forall_mem_cons.2 ⟨sub8_1269, List.forall_mem_cons.2 ⟨sub8_1270, List.forall_mem_cons.2 ⟨sub8_1271, List.forall_mem_cons.2 ⟨sub8_1272, List.forall_mem_cons.2 ⟨sub8_1273, List.forall_mem_cons.2 ⟨sub8_1274, List.forall_mem_cons.2 ⟨sub8_1275, List.forall_mem_cons.2 ⟨sub8_1276, List.forall_mem_cons.2 ⟨sub8_1277, List.forall_mem_cons.2 ⟨sub8_1278, List.forall_mem_cons.2 ⟨sub8_1279, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_1280 : sub8 [4, 2, 3] = true := by decide +kernel
theorem sub8_1281 : sub8 [4, 2, 4] = true := by decide +kernel
theorem sub8_1282 : sub8 [4, 2, 5] = true := by decide +kernel
theorem sub8_1283 : sub8 [4, 3, -9] = true := by decide +kernel
theorem sub8_1284 : sub8 [4, 3, -8] = true := by decide +kernel
theorem sub8_1285 : sub8 [4, 3, -7] = true := by decide +kernel
theorem sub8_1286 : sub8 [4, 3, -6] = true := by decide +kernel
theorem sub8_1287 : sub8 [4, 3, -5] = true := by decide +kernel
theorem sub8_1288 : sub8 [4, 3, -4] = true := by decide +kernel
theorem sub8_1289 : sub8 [4, 3, -3] = true := by decide +kernel
theorem sub8_1290 : sub8 [4, 3, -2] = true := by decide +kernel
theorem sub8_1291 : sub8 [4, 3, -1] = true := by decide +kernel
theorem sub8_1292 : sub8 [4, 3, 0] = true := by decide +kernel
theorem sub8_1293 : sub8 [4, 3, 1] = true := by decide +kernel
theorem sub8_1294 : sub8 [4, 3, 2] = true := by decide +kernel
theorem sub8_1295 : sub8 [4, 3, 3] = true := by decide +kernel
theorem sub8_1296 : sub8 [4, 3, 4] = true := by decide +kernel
theorem sub8_1297 : sub8 [4, 3, 5] = true := by decide +kernel
theorem sub8_1298 : sub8 [4, 4] = true := by decide +kernel
theorem sub8_1299 : sub8 [4, 5] = true := by decide +kernel
theorem sub8_1300 : sub8 [5, -4] = true := by decide +kernel
theorem sub8_1301 : sub8 [5, -3] = true := by decide +kernel
theorem sub8_1302 : sub8 [5, -2] = true := by decide +kernel
theorem sub8_1303 : sub8 [5, -1] = true := by decide +kernel
theorem sub8_1304 : sub8 [5, 0, -9] = true := by decide +kernel
theorem sub8_1305 : sub8 [5, 0, -8] = true := by decide +kernel
theorem sub8_1306 : sub8 [5, 0, -7] = true := by decide +kernel
theorem sub8_1307 : sub8 [5, 0, -6] = true := by decide +kernel
theorem sub8_1308 : sub8 [5, 0, -5] = true := by decide +kernel
theorem sub8_1309 : sub8 [5, 0, -4] = true := by decide +kernel
theorem sub8_1310 : sub8 [5, 0, -3] = true := by decide +kernel
theorem sub8_1311 : sub8 [5, 0, -2] = true := by decide +kernel
theorem sb8_40 : ∀ q ∈ blk8_40, sub8 q = true := by
  unfold blk8_40
  exact List.forall_mem_cons.2 ⟨sub8_1280, List.forall_mem_cons.2 ⟨sub8_1281, List.forall_mem_cons.2 ⟨sub8_1282, List.forall_mem_cons.2 ⟨sub8_1283, List.forall_mem_cons.2 ⟨sub8_1284, List.forall_mem_cons.2 ⟨sub8_1285, List.forall_mem_cons.2 ⟨sub8_1286, List.forall_mem_cons.2 ⟨sub8_1287, List.forall_mem_cons.2 ⟨sub8_1288, List.forall_mem_cons.2 ⟨sub8_1289, List.forall_mem_cons.2 ⟨sub8_1290, List.forall_mem_cons.2 ⟨sub8_1291, List.forall_mem_cons.2 ⟨sub8_1292, List.forall_mem_cons.2 ⟨sub8_1293, List.forall_mem_cons.2 ⟨sub8_1294, List.forall_mem_cons.2 ⟨sub8_1295, List.forall_mem_cons.2 ⟨sub8_1296, List.forall_mem_cons.2 ⟨sub8_1297, List.forall_mem_cons.2 ⟨sub8_1298, List.forall_mem_cons.2 ⟨sub8_1299, List.forall_mem_cons.2 ⟨sub8_1300, List.forall_mem_cons.2 ⟨sub8_1301, List.forall_mem_cons.2 ⟨sub8_1302, List.forall_mem_cons.2 ⟨sub8_1303, List.forall_mem_cons.2 ⟨sub8_1304, List.forall_mem_cons.2 ⟨sub8_1305, List.forall_mem_cons.2 ⟨sub8_1306, List.forall_mem_cons.2 ⟨sub8_1307, List.forall_mem_cons.2 ⟨sub8_1308, List.forall_mem_cons.2 ⟨sub8_1309, List.forall_mem_cons.2 ⟨sub8_1310, List.forall_mem_cons.2 ⟨sub8_1311, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_1312 : sub8 [5, 0, -1] = true := by decide +kernel
theorem sub8_1313 : sub8 [5, 0, 0] = true := by decide +kernel
theorem sub8_1314 : sub8 [5, 0, 1] = true := by decide +kernel
theorem sub8_1315 : sub8 [5, 0, 2] = true := by decide +kernel
theorem sub8_1316 : sub8 [5, 0, 3] = true := by decide +kernel
theorem sub8_1317 : sub8 [5, 0, 4] = true := by decide +kernel
theorem sub8_1318 : sub8 [5, 1, -9] = true := by decide +kernel
theorem sub8_1319 : sub8 [5, 1, -8] = true := by decide +kernel
theorem sub8_1320 : sub8 [5, 1, -7] = true := by decide +kernel
theorem sub8_1321 : sub8 [5, 1, -6] = true := by decide +kernel
theorem sub8_1322 : sub8 [5, 1, -5] = true := by decide +kernel
theorem sub8_1323 : sub8 [5, 1, -4] = true := by decide +kernel
theorem sub8_1324 : sub8 [5, 1, -3] = true := by decide +kernel
theorem sub8_1325 : sub8 [5, 1, -2] = true := by decide +kernel
theorem sub8_1326 : sub8 [5, 1, -1] = true := by decide +kernel
theorem sub8_1327 : sub8 [5, 1, 0] = true := by decide +kernel
theorem sub8_1328 : sub8 [5, 1, 1] = true := by decide +kernel
theorem sub8_1329 : sub8 [5, 1, 2] = true := by decide +kernel
theorem sub8_1330 : sub8 [5, 1, 3] = true := by decide +kernel
theorem sub8_1331 : sub8 [5, 1, 4] = true := by decide +kernel
theorem sub8_1332 : sub8 [5, 2, -9] = true := by decide +kernel
theorem sub8_1333 : sub8 [5, 2, -8] = true := by decide +kernel
theorem sub8_1334 : sub8 [5, 2, -7] = true := by decide +kernel
theorem sub8_1335 : sub8 [5, 2, -6] = true := by decide +kernel
theorem sub8_1336 : sub8 [5, 2, -5] = true := by decide +kernel
theorem sub8_1337 : sub8 [5, 2, -4] = true := by decide +kernel
theorem sub8_1338 : sub8 [5, 2, -3] = true := by decide +kernel
theorem sub8_1339 : sub8 [5, 2, -2] = true := by decide +kernel
theorem sub8_1340 : sub8 [5, 2, -1] = true := by decide +kernel
theorem sub8_1341 : sub8 [5, 2, 0] = true := by decide +kernel
theorem sub8_1342 : sub8 [5, 2, 1] = true := by decide +kernel
theorem sub8_1343 : sub8 [5, 2, 2] = true := by decide +kernel
theorem sb8_41 : ∀ q ∈ blk8_41, sub8 q = true := by
  unfold blk8_41
  exact List.forall_mem_cons.2 ⟨sub8_1312, List.forall_mem_cons.2 ⟨sub8_1313, List.forall_mem_cons.2 ⟨sub8_1314, List.forall_mem_cons.2 ⟨sub8_1315, List.forall_mem_cons.2 ⟨sub8_1316, List.forall_mem_cons.2 ⟨sub8_1317, List.forall_mem_cons.2 ⟨sub8_1318, List.forall_mem_cons.2 ⟨sub8_1319, List.forall_mem_cons.2 ⟨sub8_1320, List.forall_mem_cons.2 ⟨sub8_1321, List.forall_mem_cons.2 ⟨sub8_1322, List.forall_mem_cons.2 ⟨sub8_1323, List.forall_mem_cons.2 ⟨sub8_1324, List.forall_mem_cons.2 ⟨sub8_1325, List.forall_mem_cons.2 ⟨sub8_1326, List.forall_mem_cons.2 ⟨sub8_1327, List.forall_mem_cons.2 ⟨sub8_1328, List.forall_mem_cons.2 ⟨sub8_1329, List.forall_mem_cons.2 ⟨sub8_1330, List.forall_mem_cons.2 ⟨sub8_1331, List.forall_mem_cons.2 ⟨sub8_1332, List.forall_mem_cons.2 ⟨sub8_1333, List.forall_mem_cons.2 ⟨sub8_1334, List.forall_mem_cons.2 ⟨sub8_1335, List.forall_mem_cons.2 ⟨sub8_1336, List.forall_mem_cons.2 ⟨sub8_1337, List.forall_mem_cons.2 ⟨sub8_1338, List.forall_mem_cons.2 ⟨sub8_1339, List.forall_mem_cons.2 ⟨sub8_1340, List.forall_mem_cons.2 ⟨sub8_1341, List.forall_mem_cons.2 ⟨sub8_1342, List.forall_mem_cons.2 ⟨sub8_1343, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_1344 : sub8 [5, 2, 3] = true := by decide +kernel
theorem sub8_1345 : sub8 [5, 2, 4] = true := by decide +kernel
theorem sub8_1346 : sub8 [5, 3] = true := by decide +kernel
theorem sub8_1347 : sub8 [5, 4] = true := by decide +kernel
theorem sub8_1348 : sub8 [5, 5] = true := by decide +kernel
theorem sub8_1349 : sub8 [6, -2] = true := by decide +kernel
theorem sub8_1350 : sub8 [6, -1] = true := by decide +kernel
theorem sub8_1351 : sub8 [6, 0] = true := by decide +kernel
theorem sub8_1352 : sub8 [6, 1] = true := by decide +kernel
theorem sub8_1353 : sub8 [6, 2] = true := by decide +kernel
theorem sub8_1354 : sub8 [6, 3] = true := by decide +kernel
theorem sb8_42 : ∀ q ∈ blk8_42, sub8 q = true := by
  unfold blk8_42
  exact List.forall_mem_cons.2 ⟨sub8_1344, List.forall_mem_cons.2 ⟨sub8_1345, List.forall_mem_cons.2 ⟨sub8_1346, List.forall_mem_cons.2 ⟨sub8_1347, List.forall_mem_cons.2 ⟨sub8_1348, List.forall_mem_cons.2 ⟨sub8_1349, List.forall_mem_cons.2 ⟨sub8_1350, List.forall_mem_cons.2 ⟨sub8_1351, List.forall_mem_cons.2 ⟨sub8_1352, List.forall_mem_cons.2 ⟨sub8_1353, List.forall_mem_cons.2 ⟨sub8_1354, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_0 : sub9 [-6, -5] = true := by decide +kernel
theorem sub9_1 : sub9 [-6, -4] = true := by decide +kernel
theorem sub9_2 : sub9 [-6, -3] = true := by decide +kernel
theorem sub9_3 : sub9 [-6, -2] = true := by decide +kernel
theorem sub9_4 : sub9 [-6, -1] = true := by decide +kernel
theorem sub9_5 : sub9 [-6, 0] = true := by decide +kernel
theorem sub9_6 : sub9 [-5, -7] = true := by decide +kernel
theorem sub9_7 : sub9 [-5, -6] = true := by decide +kernel
theorem sub9_8 : sub9 [-5, -5] = true := by decide +kernel
theorem sub9_9 : sub9 [-5, -4] = true := by decide +kernel
theorem sub9_10 : sub9 [-5, -3] = true := by decide +kernel
theorem sub9_11 : sub9 [-5, -2, -6] = true := by decide +kernel
theorem sub9_12 : sub9 [-5, -2, -5] = true := by decide +kernel
theorem sub9_13 : sub9 [-5, -2, -4] = true := by decide +kernel
theorem sub9_14 : sub9 [-5, -2, -3] = true := by decide +kernel
theorem sub9_15 : sub9 [-5, -2, -2] = true := by decide +kernel
theorem sub9_16 : sub9 [-5, -2, -1] = true := by decide +kernel
theorem sub9_17 : sub9 [-5, -2, 0] = true := by decide +kernel
theorem sub9_18 : sub9 [-5, -2, 1] = true := by decide +kernel
theorem sub9_19 : sub9 [-5, -2, 2] = true := by decide +kernel
theorem sub9_20 : sub9 [-5, -2, 3] = true := by decide +kernel
theorem sub9_21 : sub9 [-5, -2, 4] = true := by decide +kernel
theorem sub9_22 : sub9 [-5, -2, 5] = true := by decide +kernel
theorem sub9_23 : sub9 [-5, -2, 6] = true := by decide +kernel
theorem sub9_24 : sub9 [-5, -1] = true := by decide +kernel
theorem sub9_25 : sub9 [-5, 0] = true := by decide +kernel
theorem sub9_26 : sub9 [-5, 1] = true := by decide +kernel
theorem sub9_27 : sub9 [-5, 2] = true := by decide +kernel
theorem sub9_28 : sub9 [-4, -7] = true := by decide +kernel
theorem sub9_29 : sub9 [-4, -6] = true := by decide +kernel
theorem sub9_30 : sub9 [-4, -5] = true := by decide +kernel
theorem sub9_31 : sub9 [-4, -4, -6] = true := by decide +kernel
theorem sb9_0 : ∀ q ∈ blk9_0, sub9 q = true := by
  unfold blk9_0
  exact List.forall_mem_cons.2 ⟨sub9_0, List.forall_mem_cons.2 ⟨sub9_1, List.forall_mem_cons.2 ⟨sub9_2, List.forall_mem_cons.2 ⟨sub9_3, List.forall_mem_cons.2 ⟨sub9_4, List.forall_mem_cons.2 ⟨sub9_5, List.forall_mem_cons.2 ⟨sub9_6, List.forall_mem_cons.2 ⟨sub9_7, List.forall_mem_cons.2 ⟨sub9_8, List.forall_mem_cons.2 ⟨sub9_9, List.forall_mem_cons.2 ⟨sub9_10, List.forall_mem_cons.2 ⟨sub9_11, List.forall_mem_cons.2 ⟨sub9_12, List.forall_mem_cons.2 ⟨sub9_13, List.forall_mem_cons.2 ⟨sub9_14, List.forall_mem_cons.2 ⟨sub9_15, List.forall_mem_cons.2 ⟨sub9_16, List.forall_mem_cons.2 ⟨sub9_17, List.forall_mem_cons.2 ⟨sub9_18, List.forall_mem_cons.2 ⟨sub9_19, List.forall_mem_cons.2 ⟨sub9_20, List.forall_mem_cons.2 ⟨sub9_21, List.forall_mem_cons.2 ⟨sub9_22, List.forall_mem_cons.2 ⟨sub9_23, List.forall_mem_cons.2 ⟨sub9_24, List.forall_mem_cons.2 ⟨sub9_25, List.forall_mem_cons.2 ⟨sub9_26, List.forall_mem_cons.2 ⟨sub9_27, List.forall_mem_cons.2 ⟨sub9_28, List.forall_mem_cons.2 ⟨sub9_29, List.forall_mem_cons.2 ⟨sub9_30, List.forall_mem_cons.2 ⟨sub9_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_32 : sub9 [-4, -4, -5] = true := by decide +kernel
theorem sub9_33 : sub9 [-4, -4, -4] = true := by decide +kernel
theorem sub9_34 : sub9 [-4, -4, -3] = true := by decide +kernel
theorem sub9_35 : sub9 [-4, -4, -2] = true := by decide +kernel
theorem sub9_36 : sub9 [-4, -4, -1] = true := by decide +kernel
theorem sub9_37 : sub9 [-4, -4, 0] = true := by decide +kernel
theorem sub9_38 : sub9 [-4, -4, 1] = true := by decide +kernel
theorem sub9_39 : sub9 [-4, -4, 2] = true := by decide +kernel
theorem sub9_40 : sub9 [-4, -4, 3] = true := by decide +kernel
theorem sub9_41 : sub9 [-4, -4, 4] = true := by decide +kernel
theorem sub9_42 : sub9 [-4, -4, 5] = true := by decide +kernel
theorem sub9_43 : sub9 [-4, -4, 6] = true := by decide +kernel
theorem sub9_44 : sub9 [-4, -4, 7] = true := by decide +kernel
theorem sub9_45 : sub9 [-4, -4, 8] = true := by decide +kernel
theorem sub9_46 : sub9 [-4, -3, -7] = true := by decide +kernel
theorem sub9_47 : sub9 [-4, -3, -6] = true := by decide +kernel
theorem sub9_48 : sub9 [-4, -3, -5] = true := by decide +kernel
theorem sub9_49 : sub9 [-4, -3, -4] = true := by decide +kernel
theorem sub9_50 : sub9 [-4, -3, -3] = true := by decide +kernel
theorem sub9_51 : sub9 [-4, -3, -2] = true := by decide +kernel
theorem sub9_52 : sub9 [-4, -3, -1] = true := by decide +kernel
theorem sub9_53 : sub9 [-4, -3, 0] = true := by decide +kernel
theorem sub9_54 : sub9 [-4, -3, 1] = true := by decide +kernel
theorem sub9_55 : sub9 [-4, -3, 2] = true := by decide +kernel
theorem sub9_56 : sub9 [-4, -3, 3] = true := by decide +kernel
theorem sub9_57 : sub9 [-4, -3, 4] = true := by decide +kernel
theorem sub9_58 : sub9 [-4, -3, 5] = true := by decide +kernel
theorem sub9_59 : sub9 [-4, -3, 6] = true := by decide +kernel
theorem sub9_60 : sub9 [-4, -3, 7] = true := by decide +kernel
theorem sub9_61 : sub9 [-4, -3, 8] = true := by decide +kernel
theorem sub9_62 : sub9 [-4, -2, -8] = true := by decide +kernel
theorem sub9_63 : sub9 [-4, -2, -7] = true := by decide +kernel
theorem sb9_1 : ∀ q ∈ blk9_1, sub9 q = true := by
  unfold blk9_1
  exact List.forall_mem_cons.2 ⟨sub9_32, List.forall_mem_cons.2 ⟨sub9_33, List.forall_mem_cons.2 ⟨sub9_34, List.forall_mem_cons.2 ⟨sub9_35, List.forall_mem_cons.2 ⟨sub9_36, List.forall_mem_cons.2 ⟨sub9_37, List.forall_mem_cons.2 ⟨sub9_38, List.forall_mem_cons.2 ⟨sub9_39, List.forall_mem_cons.2 ⟨sub9_40, List.forall_mem_cons.2 ⟨sub9_41, List.forall_mem_cons.2 ⟨sub9_42, List.forall_mem_cons.2 ⟨sub9_43, List.forall_mem_cons.2 ⟨sub9_44, List.forall_mem_cons.2 ⟨sub9_45, List.forall_mem_cons.2 ⟨sub9_46, List.forall_mem_cons.2 ⟨sub9_47, List.forall_mem_cons.2 ⟨sub9_48, List.forall_mem_cons.2 ⟨sub9_49, List.forall_mem_cons.2 ⟨sub9_50, List.forall_mem_cons.2 ⟨sub9_51, List.forall_mem_cons.2 ⟨sub9_52, List.forall_mem_cons.2 ⟨sub9_53, List.forall_mem_cons.2 ⟨sub9_54, List.forall_mem_cons.2 ⟨sub9_55, List.forall_mem_cons.2 ⟨sub9_56, List.forall_mem_cons.2 ⟨sub9_57, List.forall_mem_cons.2 ⟨sub9_58, List.forall_mem_cons.2 ⟨sub9_59, List.forall_mem_cons.2 ⟨sub9_60, List.forall_mem_cons.2 ⟨sub9_61, List.forall_mem_cons.2 ⟨sub9_62, List.forall_mem_cons.2 ⟨sub9_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_64 : sub9 [-4, -2, -6] = true := by decide +kernel
theorem sub9_65 : sub9 [-4, -2, -5] = true := by decide +kernel
theorem sub9_66 : sub9 [-4, -2, -4] = true := by decide +kernel
theorem sub9_67 : sub9 [-4, -2, -3] = true := by decide +kernel
theorem sub9_68 : sub9 [-4, -2, -2] = true := by decide +kernel
theorem sub9_69 : sub9 [-4, -2, -1] = true := by decide +kernel
theorem sub9_70 : sub9 [-4, -2, 0] = true := by decide +kernel
theorem sub9_71 : sub9 [-4, -2, 1] = true := by decide +kernel
theorem sub9_72 : sub9 [-4, -2, 2] = true := by decide +kernel
theorem sub9_73 : sub9 [-4, -2, 3] = true := by decide +kernel
theorem sub9_74 : sub9 [-4, -2, 4] = true := by decide +kernel
theorem sub9_75 : sub9 [-4, -2, 5] = true := by decide +kernel
theorem sub9_76 : sub9 [-4, -2, 6] = true := by decide +kernel
theorem sub9_77 : sub9 [-4, -2, 7] = true := by decide +kernel
theorem sub9_78 : sub9 [-4, -2, 8] = true := by decide +kernel
theorem sub9_79 : sub9 [-4, -1, -8] = true := by decide +kernel
theorem sub9_80 : sub9 [-4, -1, -7] = true := by decide +kernel
theorem sub9_81 : sub9 [-4, -1, -6] = true := by decide +kernel
theorem sub9_82 : sub9 [-4, -1, -5] = true := by decide +kernel
theorem sub9_83 : sub9 [-4, -1, -4] = true := by decide +kernel
theorem sub9_84 : sub9 [-4, -1, -3] = true := by decide +kernel
theorem sub9_85 : sub9 [-4, -1, -2] = true := by decide +kernel
theorem sub9_86 : sub9 [-4, -1, -1] = true := by decide +kernel
theorem sub9_87 : sub9 [-4, -1, 0] = true := by decide +kernel
theorem sub9_88 : sub9 [-4, -1, 1] = true := by decide +kernel
theorem sub9_89 : sub9 [-4, -1, 2] = true := by decide +kernel
theorem sub9_90 : sub9 [-4, -1, 3] = true := by decide +kernel
theorem sub9_91 : sub9 [-4, -1, 4] = true := by decide +kernel
theorem sub9_92 : sub9 [-4, -1, 5] = true := by decide +kernel
theorem sub9_93 : sub9 [-4, -1, 6] = true := by decide +kernel
theorem sub9_94 : sub9 [-4, -1, 7] = true := by decide +kernel
theorem sub9_95 : sub9 [-4, 0, -8] = true := by decide +kernel
theorem sb9_2 : ∀ q ∈ blk9_2, sub9 q = true := by
  unfold blk9_2
  exact List.forall_mem_cons.2 ⟨sub9_64, List.forall_mem_cons.2 ⟨sub9_65, List.forall_mem_cons.2 ⟨sub9_66, List.forall_mem_cons.2 ⟨sub9_67, List.forall_mem_cons.2 ⟨sub9_68, List.forall_mem_cons.2 ⟨sub9_69, List.forall_mem_cons.2 ⟨sub9_70, List.forall_mem_cons.2 ⟨sub9_71, List.forall_mem_cons.2 ⟨sub9_72, List.forall_mem_cons.2 ⟨sub9_73, List.forall_mem_cons.2 ⟨sub9_74, List.forall_mem_cons.2 ⟨sub9_75, List.forall_mem_cons.2 ⟨sub9_76, List.forall_mem_cons.2 ⟨sub9_77, List.forall_mem_cons.2 ⟨sub9_78, List.forall_mem_cons.2 ⟨sub9_79, List.forall_mem_cons.2 ⟨sub9_80, List.forall_mem_cons.2 ⟨sub9_81, List.forall_mem_cons.2 ⟨sub9_82, List.forall_mem_cons.2 ⟨sub9_83, List.forall_mem_cons.2 ⟨sub9_84, List.forall_mem_cons.2 ⟨sub9_85, List.forall_mem_cons.2 ⟨sub9_86, List.forall_mem_cons.2 ⟨sub9_87, List.forall_mem_cons.2 ⟨sub9_88, List.forall_mem_cons.2 ⟨sub9_89, List.forall_mem_cons.2 ⟨sub9_90, List.forall_mem_cons.2 ⟨sub9_91, List.forall_mem_cons.2 ⟨sub9_92, List.forall_mem_cons.2 ⟨sub9_93, List.forall_mem_cons.2 ⟨sub9_94, List.forall_mem_cons.2 ⟨sub9_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_96 : sub9 [-4, 0, -7] = true := by decide +kernel
theorem sub9_97 : sub9 [-4, 0, -6] = true := by decide +kernel
theorem sub9_98 : sub9 [-4, 0, -5] = true := by decide +kernel
theorem sub9_99 : sub9 [-4, 0, -4] = true := by decide +kernel
theorem sub9_100 : sub9 [-4, 0, -3] = true := by decide +kernel
theorem sub9_101 : sub9 [-4, 0, -2] = true := by decide +kernel
theorem sub9_102 : sub9 [-4, 0, -1] = true := by decide +kernel
theorem sub9_103 : sub9 [-4, 0, 0] = true := by decide +kernel
theorem sub9_104 : sub9 [-4, 0, 1] = true := by decide +kernel
theorem sub9_105 : sub9 [-4, 0, 2] = true := by decide +kernel
theorem sub9_106 : sub9 [-4, 0, 3] = true := by decide +kernel
theorem sub9_107 : sub9 [-4, 0, 4] = true := by decide +kernel
theorem sub9_108 : sub9 [-4, 0, 5] = true := by decide +kernel
theorem sub9_109 : sub9 [-4, 0, 6] = true := by decide +kernel
theorem sub9_110 : sub9 [-4, 0, 7] = true := by decide +kernel
theorem sub9_111 : sub9 [-4, 1, -8] = true := by decide +kernel
theorem sub9_112 : sub9 [-4, 1, -7] = true := by decide +kernel
theorem sub9_113 : sub9 [-4, 1, -6] = true := by decide +kernel
theorem sub9_114 : sub9 [-4, 1, -5] = true := by decide +kernel
theorem sub9_115 : sub9 [-4, 1, -4] = true := by decide +kernel
theorem sub9_116 : sub9 [-4, 1, -3] = true := by decide +kernel
theorem sub9_117 : sub9 [-4, 1, -2] = true := by decide +kernel
theorem sub9_118 : sub9 [-4, 1, -1] = true := by decide +kernel
theorem sub9_119 : sub9 [-4, 1, 0] = true := by decide +kernel
theorem sub9_120 : sub9 [-4, 1, 1] = true := by decide +kernel
theorem sub9_121 : sub9 [-4, 1, 2] = true := by decide +kernel
theorem sub9_122 : sub9 [-4, 1, 3] = true := by decide +kernel
theorem sub9_123 : sub9 [-4, 1, 4] = true := by decide +kernel
theorem sub9_124 : sub9 [-4, 1, 5] = true := by decide +kernel
theorem sub9_125 : sub9 [-4, 1, 6] = true := by decide +kernel
theorem sub9_126 : sub9 [-4, 2, -8] = true := by decide +kernel
theorem sub9_127 : sub9 [-4, 2, -7] = true := by decide +kernel
theorem sb9_3 : ∀ q ∈ blk9_3, sub9 q = true := by
  unfold blk9_3
  exact List.forall_mem_cons.2 ⟨sub9_96, List.forall_mem_cons.2 ⟨sub9_97, List.forall_mem_cons.2 ⟨sub9_98, List.forall_mem_cons.2 ⟨sub9_99, List.forall_mem_cons.2 ⟨sub9_100, List.forall_mem_cons.2 ⟨sub9_101, List.forall_mem_cons.2 ⟨sub9_102, List.forall_mem_cons.2 ⟨sub9_103, List.forall_mem_cons.2 ⟨sub9_104, List.forall_mem_cons.2 ⟨sub9_105, List.forall_mem_cons.2 ⟨sub9_106, List.forall_mem_cons.2 ⟨sub9_107, List.forall_mem_cons.2 ⟨sub9_108, List.forall_mem_cons.2 ⟨sub9_109, List.forall_mem_cons.2 ⟨sub9_110, List.forall_mem_cons.2 ⟨sub9_111, List.forall_mem_cons.2 ⟨sub9_112, List.forall_mem_cons.2 ⟨sub9_113, List.forall_mem_cons.2 ⟨sub9_114, List.forall_mem_cons.2 ⟨sub9_115, List.forall_mem_cons.2 ⟨sub9_116, List.forall_mem_cons.2 ⟨sub9_117, List.forall_mem_cons.2 ⟨sub9_118, List.forall_mem_cons.2 ⟨sub9_119, List.forall_mem_cons.2 ⟨sub9_120, List.forall_mem_cons.2 ⟨sub9_121, List.forall_mem_cons.2 ⟨sub9_122, List.forall_mem_cons.2 ⟨sub9_123, List.forall_mem_cons.2 ⟨sub9_124, List.forall_mem_cons.2 ⟨sub9_125, List.forall_mem_cons.2 ⟨sub9_126, List.forall_mem_cons.2 ⟨sub9_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_128 : sub9 [-4, 2, -6] = true := by decide +kernel
theorem sub9_129 : sub9 [-4, 2, -5] = true := by decide +kernel
theorem sub9_130 : sub9 [-4, 2, -4] = true := by decide +kernel
theorem sub9_131 : sub9 [-4, 2, -3] = true := by decide +kernel
theorem sub9_132 : sub9 [-4, 2, -2] = true := by decide +kernel
theorem sub9_133 : sub9 [-4, 2, -1] = true := by decide +kernel
theorem sub9_134 : sub9 [-4, 2, 0] = true := by decide +kernel
theorem sub9_135 : sub9 [-4, 2, 1] = true := by decide +kernel
theorem sub9_136 : sub9 [-4, 2, 2] = true := by decide +kernel
theorem sub9_137 : sub9 [-4, 2, 3] = true := by decide +kernel
theorem sub9_138 : sub9 [-4, 2, 4] = true := by decide +kernel
theorem sub9_139 : sub9 [-4, 2, 5] = true := by decide +kernel
theorem sub9_140 : sub9 [-4, 3] = true := by decide +kernel
theorem sub9_141 : sub9 [-4, 4] = true := by decide +kernel
theorem sub9_142 : sub9 [-3, -8] = true := by decide +kernel
theorem sub9_143 : sub9 [-3, -7] = true := by decide +kernel
theorem sub9_144 : sub9 [-3, -6] = true := by decide +kernel
theorem sub9_145 : sub9 [-3, -5, -6] = true := by decide +kernel
theorem sub9_146 : sub9 [-3, -5, -5] = true := by decide +kernel
theorem sub9_147 : sub9 [-3, -5, -4] = true := by decide +kernel
theorem sub9_148 : sub9 [-3, -5, -3] = true := by decide +kernel
theorem sub9_149 : sub9 [-3, -5, -2] = true := by decide +kernel
theorem sub9_150 : sub9 [-3, -5, -1] = true := by decide +kernel
theorem sub9_151 : sub9 [-3, -5, 0] = true := by decide +kernel
theorem sub9_152 : sub9 [-3, -5, 1] = true := by decide +kernel
theorem sub9_153 : sub9 [-3, -5, 2] = true := by decide +kernel
theorem sub9_154 : sub9 [-3, -5, 3] = true := by decide +kernel
theorem sub9_155 : sub9 [-3, -5, 4] = true := by decide +kernel
theorem sub9_156 : sub9 [-3, -5, 5] = true := by decide +kernel
theorem sub9_157 : sub9 [-3, -5, 6] = true := by decide +kernel
theorem sub9_158 : sub9 [-3, -5, 7] = true := by decide +kernel
theorem sub9_159 : sub9 [-3, -5, 8] = true := by decide +kernel
theorem sb9_4 : ∀ q ∈ blk9_4, sub9 q = true := by
  unfold blk9_4
  exact List.forall_mem_cons.2 ⟨sub9_128, List.forall_mem_cons.2 ⟨sub9_129, List.forall_mem_cons.2 ⟨sub9_130, List.forall_mem_cons.2 ⟨sub9_131, List.forall_mem_cons.2 ⟨sub9_132, List.forall_mem_cons.2 ⟨sub9_133, List.forall_mem_cons.2 ⟨sub9_134, List.forall_mem_cons.2 ⟨sub9_135, List.forall_mem_cons.2 ⟨sub9_136, List.forall_mem_cons.2 ⟨sub9_137, List.forall_mem_cons.2 ⟨sub9_138, List.forall_mem_cons.2 ⟨sub9_139, List.forall_mem_cons.2 ⟨sub9_140, List.forall_mem_cons.2 ⟨sub9_141, List.forall_mem_cons.2 ⟨sub9_142, List.forall_mem_cons.2 ⟨sub9_143, List.forall_mem_cons.2 ⟨sub9_144, List.forall_mem_cons.2 ⟨sub9_145, List.forall_mem_cons.2 ⟨sub9_146, List.forall_mem_cons.2 ⟨sub9_147, List.forall_mem_cons.2 ⟨sub9_148, List.forall_mem_cons.2 ⟨sub9_149, List.forall_mem_cons.2 ⟨sub9_150, List.forall_mem_cons.2 ⟨sub9_151, List.forall_mem_cons.2 ⟨sub9_152, List.forall_mem_cons.2 ⟨sub9_153, List.forall_mem_cons.2 ⟨sub9_154, List.forall_mem_cons.2 ⟨sub9_155, List.forall_mem_cons.2 ⟨sub9_156, List.forall_mem_cons.2 ⟨sub9_157, List.forall_mem_cons.2 ⟨sub9_158, List.forall_mem_cons.2 ⟨sub9_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_160 : sub9 [-3, -4, -7] = true := by decide +kernel
theorem sub9_161 : sub9 [-3, -4, -6] = true := by decide +kernel
theorem sub9_162 : sub9 [-3, -4, -5] = true := by decide +kernel
theorem sub9_163 : sub9 [-3, -4, -4] = true := by decide +kernel
theorem sub9_164 : sub9 [-3, -4, -3] = true := by decide +kernel
theorem sub9_165 : sub9 [-3, -4, -2] = true := by decide +kernel
theorem sub9_166 : sub9 [-3, -4, -1] = true := by decide +kernel
theorem sub9_167 : sub9 [-3, -4, 0] = true := by decide +kernel
theorem sub9_168 : sub9 [-3, -4, 1] = true := by decide +kernel
theorem sub9_169 : sub9 [-3, -4, 2] = true := by decide +kernel
theorem sub9_170 : sub9 [-3, -4, 3] = true := by decide +kernel
theorem sub9_171 : sub9 [-3, -4, 4] = true := by decide +kernel
theorem sub9_172 : sub9 [-3, -4, 5] = true := by decide +kernel
theorem sub9_173 : sub9 [-3, -4, 6] = true := by decide +kernel
theorem sub9_174 : sub9 [-3, -4, 7] = true := by decide +kernel
theorem sub9_175 : sub9 [-3, -4, 8] = true := by decide +kernel
theorem sub9_176 : sub9 [-3, -3, -8] = true := by decide +kernel
theorem sub9_177 : sub9 [-3, -3, -7] = true := by decide +kernel
theorem sub9_178 : sub9 [-3, -3, -6] = true := by decide +kernel
theorem sub9_179 : sub9 [-3, -3, -5] = true := by decide +kernel
theorem sub9_180 : sub9 [-3, -3, -4] = true := by decide +kernel
theorem sub9_181 : sub9 [-3, -3, -3] = true := by decide +kernel
theorem sub9_182 : sub9 [-3, -3, -2] = true := by decide +kernel
theorem sub9_183 : sub9 [-3, -3, -1] = true := by decide +kernel
theorem sub9_184 : sub9 [-3, -3, 0] = true := by decide +kernel
theorem sub9_185 : sub9 [-3, -3, 1] = true := by decide +kernel
theorem sub9_186 : sub9 [-3, -3, 2] = true := by decide +kernel
theorem sub9_187 : sub9 [-3, -3, 3] = true := by decide +kernel
theorem sub9_188 : sub9 [-3, -3, 4] = true := by decide +kernel
theorem sub9_189 : sub9 [-3, -3, 5] = true := by decide +kernel
theorem sub9_190 : sub9 [-3, -3, 6] = true := by decide +kernel
theorem sub9_191 : sub9 [-3, -3, 7] = true := by decide +kernel
theorem sb9_5 : ∀ q ∈ blk9_5, sub9 q = true := by
  unfold blk9_5
  exact List.forall_mem_cons.2 ⟨sub9_160, List.forall_mem_cons.2 ⟨sub9_161, List.forall_mem_cons.2 ⟨sub9_162, List.forall_mem_cons.2 ⟨sub9_163, List.forall_mem_cons.2 ⟨sub9_164, List.forall_mem_cons.2 ⟨sub9_165, List.forall_mem_cons.2 ⟨sub9_166, List.forall_mem_cons.2 ⟨sub9_167, List.forall_mem_cons.2 ⟨sub9_168, List.forall_mem_cons.2 ⟨sub9_169, List.forall_mem_cons.2 ⟨sub9_170, List.forall_mem_cons.2 ⟨sub9_171, List.forall_mem_cons.2 ⟨sub9_172, List.forall_mem_cons.2 ⟨sub9_173, List.forall_mem_cons.2 ⟨sub9_174, List.forall_mem_cons.2 ⟨sub9_175, List.forall_mem_cons.2 ⟨sub9_176, List.forall_mem_cons.2 ⟨sub9_177, List.forall_mem_cons.2 ⟨sub9_178, List.forall_mem_cons.2 ⟨sub9_179, List.forall_mem_cons.2 ⟨sub9_180, List.forall_mem_cons.2 ⟨sub9_181, List.forall_mem_cons.2 ⟨sub9_182, List.forall_mem_cons.2 ⟨sub9_183, List.forall_mem_cons.2 ⟨sub9_184, List.forall_mem_cons.2 ⟨sub9_185, List.forall_mem_cons.2 ⟨sub9_186, List.forall_mem_cons.2 ⟨sub9_187, List.forall_mem_cons.2 ⟨sub9_188, List.forall_mem_cons.2 ⟨sub9_189, List.forall_mem_cons.2 ⟨sub9_190, List.forall_mem_cons.2 ⟨sub9_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C080
