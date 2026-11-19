import ReflectZphi.Data.Cert5.C142.Base

namespace ReflectZphi.Data.Cert5.C142

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_2_1184 : subd8_2 [3, -3] = true := by decide +kernel
theorem subd8_2_1185 : subd8_2 [3, -2, -9] = true := by decide +kernel
theorem subd8_2_1186 : subd8_2 [3, -2, -8] = true := by decide +kernel
theorem subd8_2_1187 : subd8_2 [3, -2, -7] = true := by decide +kernel
theorem subd8_2_1188 : subd8_2 [3, -2, -6] = true := by decide +kernel
theorem subd8_2_1189 : subd8_2 [3, -2, -5] = true := by decide +kernel
theorem subd8_2_1190 : subd8_2 [3, -2, -4] = true := by decide +kernel
theorem subd8_2_1191 : subd8_2 [3, -2, -3] = true := by decide +kernel
theorem subd8_2_1192 : subd8_2 [3, -2, -2] = true := by decide +kernel
theorem subd8_2_1193 : subd8_2 [3, -2, -1] = true := by decide +kernel
theorem subd8_2_1194 : subd8_2 [3, -2, 0] = true := by decide +kernel
theorem subd8_2_1195 : subd8_2 [3, -2, 1] = true := by decide +kernel
theorem subd8_2_1196 : subd8_2 [3, -2, 2] = true := by decide +kernel
theorem subd8_2_1197 : subd8_2 [3, -2, 3] = true := by decide +kernel
theorem subd8_2_1198 : subd8_2 [3, -2, 4] = true := by decide +kernel
theorem subd8_2_1199 : subd8_2 [3, -2, 5] = true := by decide +kernel
theorem subd8_2_1200 : subd8_2 [3, -2, 6] = true := by decide +kernel
theorem subd8_2_1201 : subd8_2 [3, -2, 7] = true := by decide +kernel
theorem subd8_2_1202 : subd8_2 [3, -1, -10] = true := by decide +kernel
theorem subd8_2_1203 : subd8_2 [3, -1, -9] = true := by decide +kernel
theorem subd8_2_1204 : subd8_2 [3, -1, -8] = true := by decide +kernel
theorem subd8_2_1205 : subd8_2 [3, -1, -7] = true := by decide +kernel
theorem subd8_2_1206 : subd8_2 [3, -1, -6] = true := by decide +kernel
theorem subd8_2_1207 : subd8_2 [3, -1, -5] = true := by decide +kernel
theorem subd8_2_1208 : subd8_2 [3, -1, -4] = true := by decide +kernel
theorem subd8_2_1209 : subd8_2 [3, -1, -3] = true := by decide +kernel
theorem subd8_2_1210 : subd8_2 [3, -1, -2] = true := by decide +kernel
theorem subd8_2_1211 : subd8_2 [3, -1, -1] = true := by decide +kernel
theorem subd8_2_1212 : subd8_2 [3, -1, 0] = true := by decide +kernel
theorem subd8_2_1213 : subd8_2 [3, -1, 1] = true := by decide +kernel
theorem subd8_2_1214 : subd8_2 [3, -1, 2] = true := by decide +kernel
theorem subd8_2_1215 : subd8_2 [3, -1, 3] = true := by decide +kernel
theorem sbd8_2_37 : ∀ q ∈ blkd8_2_37, subd8_2 q = true := by
  unfold blkd8_2_37
  exact List.forall_mem_cons.2 ⟨subd8_2_1184, List.forall_mem_cons.2 ⟨subd8_2_1185, List.forall_mem_cons.2 ⟨subd8_2_1186, List.forall_mem_cons.2 ⟨subd8_2_1187, List.forall_mem_cons.2 ⟨subd8_2_1188, List.forall_mem_cons.2 ⟨subd8_2_1189, List.forall_mem_cons.2 ⟨subd8_2_1190, List.forall_mem_cons.2 ⟨subd8_2_1191, List.forall_mem_cons.2 ⟨subd8_2_1192, List.forall_mem_cons.2 ⟨subd8_2_1193, List.forall_mem_cons.2 ⟨subd8_2_1194, List.forall_mem_cons.2 ⟨subd8_2_1195, List.forall_mem_cons.2 ⟨subd8_2_1196, List.forall_mem_cons.2 ⟨subd8_2_1197, List.forall_mem_cons.2 ⟨subd8_2_1198, List.forall_mem_cons.2 ⟨subd8_2_1199, List.forall_mem_cons.2 ⟨subd8_2_1200, List.forall_mem_cons.2 ⟨subd8_2_1201, List.forall_mem_cons.2 ⟨subd8_2_1202, List.forall_mem_cons.2 ⟨subd8_2_1203, List.forall_mem_cons.2 ⟨subd8_2_1204, List.forall_mem_cons.2 ⟨subd8_2_1205, List.forall_mem_cons.2 ⟨subd8_2_1206, List.forall_mem_cons.2 ⟨subd8_2_1207, List.forall_mem_cons.2 ⟨subd8_2_1208, List.forall_mem_cons.2 ⟨subd8_2_1209, List.forall_mem_cons.2 ⟨subd8_2_1210, List.forall_mem_cons.2 ⟨subd8_2_1211, List.forall_mem_cons.2 ⟨subd8_2_1212, List.forall_mem_cons.2 ⟨subd8_2_1213, List.forall_mem_cons.2 ⟨subd8_2_1214, List.forall_mem_cons.2 ⟨subd8_2_1215, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_1216 : subd8_2 [3, -1, 4] = true := by decide +kernel
theorem subd8_2_1217 : subd8_2 [3, -1, 5] = true := by decide +kernel
theorem subd8_2_1218 : subd8_2 [3, -1, 6] = true := by decide +kernel
theorem subd8_2_1219 : subd8_2 [3, -1, 7] = true := by decide +kernel
theorem subd8_2_1220 : subd8_2 [3, -1, 8] = true := by decide +kernel
theorem subd8_2_1221 : subd8_2 [3, 0, -12] = true := by decide +kernel
theorem subd8_2_1222 : subd8_2 [3, 0, -11] = true := by decide +kernel
theorem subd8_2_1223 : subd8_2 [3, 0, -10] = true := by decide +kernel
theorem subd8_2_1224 : subd8_2 [3, 0, -9] = true := by decide +kernel
theorem subd8_2_1225 : subd8_2 [3, 0, -8] = true := by decide +kernel
theorem subd8_2_1226 : subd8_2 [3, 0, -7] = true := by decide +kernel
theorem subd8_2_1227 : subd8_2 [3, 0, -6] = true := by decide +kernel
theorem subd8_2_1228 : subd8_2 [3, 0, -5] = true := by decide +kernel
theorem subd8_2_1229 : subd8_2 [3, 0, -4] = true := by decide +kernel
theorem subd8_2_1230 : subd8_2 [3, 0, -3] = true := by decide +kernel
theorem subd8_2_1231 : subd8_2 [3, 0, -2] = true := by decide +kernel
theorem subd8_2_1232 : subd8_2 [3, 0, -1] = true := by decide +kernel
theorem subd8_2_1233 : subd8_2 [3, 0, 0] = true := by decide +kernel
theorem subd8_2_1234 : subd8_2 [3, 0, 1] = true := by decide +kernel
theorem subd8_2_1235 : subd8_2 [3, 0, 2] = true := by decide +kernel
theorem subd8_2_1236 : subd8_2 [3, 0, 3] = true := by decide +kernel
theorem subd8_2_1237 : subd8_2 [3, 0, 4] = true := by decide +kernel
theorem subd8_2_1238 : subd8_2 [3, 0, 5] = true := by decide +kernel
theorem subd8_2_1239 : subd8_2 [3, 0, 6] = true := by decide +kernel
theorem subd8_2_1240 : subd8_2 [3, 0, 7] = true := by decide +kernel
theorem subd8_2_1241 : subd8_2 [3, 0, 8] = true := by decide +kernel
theorem subd8_2_1242 : subd8_2 [3, 1, -12] = true := by decide +kernel
theorem subd8_2_1243 : subd8_2 [3, 1, -11] = true := by decide +kernel
theorem subd8_2_1244 : subd8_2 [3, 1, -10] = true := by decide +kernel
theorem subd8_2_1245 : subd8_2 [3, 1, -9] = true := by decide +kernel
theorem subd8_2_1246 : subd8_2 [3, 1, -8] = true := by decide +kernel
theorem subd8_2_1247 : subd8_2 [3, 1, -7] = true := by decide +kernel
theorem sbd8_2_38 : ∀ q ∈ blkd8_2_38, subd8_2 q = true := by
  unfold blkd8_2_38
  exact List.forall_mem_cons.2 ⟨subd8_2_1216, List.forall_mem_cons.2 ⟨subd8_2_1217, List.forall_mem_cons.2 ⟨subd8_2_1218, List.forall_mem_cons.2 ⟨subd8_2_1219, List.forall_mem_cons.2 ⟨subd8_2_1220, List.forall_mem_cons.2 ⟨subd8_2_1221, List.forall_mem_cons.2 ⟨subd8_2_1222, List.forall_mem_cons.2 ⟨subd8_2_1223, List.forall_mem_cons.2 ⟨subd8_2_1224, List.forall_mem_cons.2 ⟨subd8_2_1225, List.forall_mem_cons.2 ⟨subd8_2_1226, List.forall_mem_cons.2 ⟨subd8_2_1227, List.forall_mem_cons.2 ⟨subd8_2_1228, List.forall_mem_cons.2 ⟨subd8_2_1229, List.forall_mem_cons.2 ⟨subd8_2_1230, List.forall_mem_cons.2 ⟨subd8_2_1231, List.forall_mem_cons.2 ⟨subd8_2_1232, List.forall_mem_cons.2 ⟨subd8_2_1233, List.forall_mem_cons.2 ⟨subd8_2_1234, List.forall_mem_cons.2 ⟨subd8_2_1235, List.forall_mem_cons.2 ⟨subd8_2_1236, List.forall_mem_cons.2 ⟨subd8_2_1237, List.forall_mem_cons.2 ⟨subd8_2_1238, List.forall_mem_cons.2 ⟨subd8_2_1239, List.forall_mem_cons.2 ⟨subd8_2_1240, List.forall_mem_cons.2 ⟨subd8_2_1241, List.forall_mem_cons.2 ⟨subd8_2_1242, List.forall_mem_cons.2 ⟨subd8_2_1243, List.forall_mem_cons.2 ⟨subd8_2_1244, List.forall_mem_cons.2 ⟨subd8_2_1245, List.forall_mem_cons.2 ⟨subd8_2_1246, List.forall_mem_cons.2 ⟨subd8_2_1247, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_1248 : subd8_2 [3, 1, -6] = true := by decide +kernel
theorem subd8_2_1249 : subd8_2 [3, 1, -5] = true := by decide +kernel
theorem subd8_2_1250 : subd8_2 [3, 1, -4] = true := by decide +kernel
theorem subd8_2_1251 : subd8_2 [3, 1, -3] = true := by decide +kernel
theorem subd8_2_1252 : subd8_2 [3, 1, -2] = true := by decide +kernel
theorem subd8_2_1253 : subd8_2 [3, 1, -1] = true := by decide +kernel
theorem subd8_2_1254 : subd8_2 [3, 1, 0] = true := by decide +kernel
theorem subd8_2_1255 : subd8_2 [3, 1, 1] = true := by decide +kernel
theorem subd8_2_1256 : subd8_2 [3, 1, 2] = true := by decide +kernel
theorem subd8_2_1257 : subd8_2 [3, 1, 3] = true := by decide +kernel
theorem subd8_2_1258 : subd8_2 [3, 1, 4] = true := by decide +kernel
theorem subd8_2_1259 : subd8_2 [3, 1, 5] = true := by decide +kernel
theorem subd8_2_1260 : subd8_2 [3, 1, 6] = true := by decide +kernel
theorem subd8_2_1261 : subd8_2 [3, 1, 7] = true := by decide +kernel
theorem subd8_2_1262 : subd8_2 [3, 1, 8] = true := by decide +kernel
theorem subd8_2_1263 : subd8_2 [3, 2, -12] = true := by decide +kernel
theorem subd8_2_1264 : subd8_2 [3, 2, -11] = true := by decide +kernel
theorem subd8_2_1265 : subd8_2 [3, 2, -10] = true := by decide +kernel
theorem subd8_2_1266 : subd8_2 [3, 2, -9] = true := by decide +kernel
theorem subd8_2_1267 : subd8_2 [3, 2, -8] = true := by decide +kernel
theorem subd8_2_1268 : subd8_2 [3, 2, -7] = true := by decide +kernel
theorem subd8_2_1269 : subd8_2 [3, 2, -6] = true := by decide +kernel
theorem subd8_2_1270 : subd8_2 [3, 2, -5] = true := by decide +kernel
theorem subd8_2_1271 : subd8_2 [3, 2, -4] = true := by decide +kernel
theorem subd8_2_1272 : subd8_2 [3, 2, -3] = true := by decide +kernel
theorem subd8_2_1273 : subd8_2 [3, 2, -2] = true := by decide +kernel
theorem subd8_2_1274 : subd8_2 [3, 2, -1] = true := by decide +kernel
theorem subd8_2_1275 : subd8_2 [3, 2, 0] = true := by decide +kernel
theorem subd8_2_1276 : subd8_2 [3, 2, 1] = true := by decide +kernel
theorem subd8_2_1277 : subd8_2 [3, 2, 2] = true := by decide +kernel
theorem subd8_2_1278 : subd8_2 [3, 2, 3] = true := by decide +kernel
theorem subd8_2_1279 : subd8_2 [3, 2, 4] = true := by decide +kernel
theorem sbd8_2_39 : ∀ q ∈ blkd8_2_39, subd8_2 q = true := by
  unfold blkd8_2_39
  exact List.forall_mem_cons.2 ⟨subd8_2_1248, List.forall_mem_cons.2 ⟨subd8_2_1249, List.forall_mem_cons.2 ⟨subd8_2_1250, List.forall_mem_cons.2 ⟨subd8_2_1251, List.forall_mem_cons.2 ⟨subd8_2_1252, List.forall_mem_cons.2 ⟨subd8_2_1253, List.forall_mem_cons.2 ⟨subd8_2_1254, List.forall_mem_cons.2 ⟨subd8_2_1255, List.forall_mem_cons.2 ⟨subd8_2_1256, List.forall_mem_cons.2 ⟨subd8_2_1257, List.forall_mem_cons.2 ⟨subd8_2_1258, List.forall_mem_cons.2 ⟨subd8_2_1259, List.forall_mem_cons.2 ⟨subd8_2_1260, List.forall_mem_cons.2 ⟨subd8_2_1261, List.forall_mem_cons.2 ⟨subd8_2_1262, List.forall_mem_cons.2 ⟨subd8_2_1263, List.forall_mem_cons.2 ⟨subd8_2_1264, List.forall_mem_cons.2 ⟨subd8_2_1265, List.forall_mem_cons.2 ⟨subd8_2_1266, List.forall_mem_cons.2 ⟨subd8_2_1267, List.forall_mem_cons.2 ⟨subd8_2_1268, List.forall_mem_cons.2 ⟨subd8_2_1269, List.forall_mem_cons.2 ⟨subd8_2_1270, List.forall_mem_cons.2 ⟨subd8_2_1271, List.forall_mem_cons.2 ⟨subd8_2_1272, List.forall_mem_cons.2 ⟨subd8_2_1273, List.forall_mem_cons.2 ⟨subd8_2_1274, List.forall_mem_cons.2 ⟨subd8_2_1275, List.forall_mem_cons.2 ⟨subd8_2_1276, List.forall_mem_cons.2 ⟨subd8_2_1277, List.forall_mem_cons.2 ⟨subd8_2_1278, List.forall_mem_cons.2 ⟨subd8_2_1279, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_1280 : subd8_2 [3, 2, 5] = true := by decide +kernel
theorem subd8_2_1281 : subd8_2 [3, 2, 6] = true := by decide +kernel
theorem subd8_2_1282 : subd8_2 [3, 2, 7] = true := by decide +kernel
theorem subd8_2_1283 : subd8_2 [3, 3, -12] = true := by decide +kernel
theorem subd8_2_1284 : subd8_2 [3, 3, -11] = true := by decide +kernel
theorem subd8_2_1285 : subd8_2 [3, 3, -10] = true := by decide +kernel
theorem subd8_2_1286 : subd8_2 [3, 3, -9] = true := by decide +kernel
theorem subd8_2_1287 : subd8_2 [3, 3, -8] = true := by decide +kernel
theorem subd8_2_1288 : subd8_2 [3, 3, -7] = true := by decide +kernel
theorem subd8_2_1289 : subd8_2 [3, 3, -6] = true := by decide +kernel
theorem subd8_2_1290 : subd8_2 [3, 3, -5] = true := by decide +kernel
theorem subd8_2_1291 : subd8_2 [3, 3, -4] = true := by decide +kernel
theorem subd8_2_1292 : subd8_2 [3, 3, -3] = true := by decide +kernel
theorem subd8_2_1293 : subd8_2 [3, 3, -2] = true := by decide +kernel
theorem subd8_2_1294 : subd8_2 [3, 3, -1] = true := by decide +kernel
theorem subd8_2_1295 : subd8_2 [3, 3, 0] = true := by decide +kernel
theorem subd8_2_1296 : subd8_2 [3, 3, 1] = true := by decide +kernel
theorem subd8_2_1297 : subd8_2 [3, 3, 2] = true := by decide +kernel
theorem subd8_2_1298 : subd8_2 [3, 3, 3] = true := by decide +kernel
theorem subd8_2_1299 : subd8_2 [3, 3, 4] = true := by decide +kernel
theorem subd8_2_1300 : subd8_2 [3, 3, 5] = true := by decide +kernel
theorem subd8_2_1301 : subd8_2 [3, 3, 6] = true := by decide +kernel
theorem subd8_2_1302 : subd8_2 [3, 4, -11] = true := by decide +kernel
theorem subd8_2_1303 : subd8_2 [3, 4, -10] = true := by decide +kernel
theorem subd8_2_1304 : subd8_2 [3, 4, -9] = true := by decide +kernel
theorem subd8_2_1305 : subd8_2 [3, 4, -8] = true := by decide +kernel
theorem subd8_2_1306 : subd8_2 [3, 4, -7] = true := by decide +kernel
theorem subd8_2_1307 : subd8_2 [3, 4, -6] = true := by decide +kernel
theorem subd8_2_1308 : subd8_2 [3, 4, -5] = true := by decide +kernel
theorem subd8_2_1309 : subd8_2 [3, 4, -4] = true := by decide +kernel
theorem subd8_2_1310 : subd8_2 [3, 4, -3] = true := by decide +kernel
theorem subd8_2_1311 : subd8_2 [3, 4, -2] = true := by decide +kernel
theorem sbd8_2_40 : ∀ q ∈ blkd8_2_40, subd8_2 q = true := by
  unfold blkd8_2_40
  exact List.forall_mem_cons.2 ⟨subd8_2_1280, List.forall_mem_cons.2 ⟨subd8_2_1281, List.forall_mem_cons.2 ⟨subd8_2_1282, List.forall_mem_cons.2 ⟨subd8_2_1283, List.forall_mem_cons.2 ⟨subd8_2_1284, List.forall_mem_cons.2 ⟨subd8_2_1285, List.forall_mem_cons.2 ⟨subd8_2_1286, List.forall_mem_cons.2 ⟨subd8_2_1287, List.forall_mem_cons.2 ⟨subd8_2_1288, List.forall_mem_cons.2 ⟨subd8_2_1289, List.forall_mem_cons.2 ⟨subd8_2_1290, List.forall_mem_cons.2 ⟨subd8_2_1291, List.forall_mem_cons.2 ⟨subd8_2_1292, List.forall_mem_cons.2 ⟨subd8_2_1293, List.forall_mem_cons.2 ⟨subd8_2_1294, List.forall_mem_cons.2 ⟨subd8_2_1295, List.forall_mem_cons.2 ⟨subd8_2_1296, List.forall_mem_cons.2 ⟨subd8_2_1297, List.forall_mem_cons.2 ⟨subd8_2_1298, List.forall_mem_cons.2 ⟨subd8_2_1299, List.forall_mem_cons.2 ⟨subd8_2_1300, List.forall_mem_cons.2 ⟨subd8_2_1301, List.forall_mem_cons.2 ⟨subd8_2_1302, List.forall_mem_cons.2 ⟨subd8_2_1303, List.forall_mem_cons.2 ⟨subd8_2_1304, List.forall_mem_cons.2 ⟨subd8_2_1305, List.forall_mem_cons.2 ⟨subd8_2_1306, List.forall_mem_cons.2 ⟨subd8_2_1307, List.forall_mem_cons.2 ⟨subd8_2_1308, List.forall_mem_cons.2 ⟨subd8_2_1309, List.forall_mem_cons.2 ⟨subd8_2_1310, List.forall_mem_cons.2 ⟨subd8_2_1311, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_1312 : subd8_2 [3, 4, -1] = true := by decide +kernel
theorem subd8_2_1313 : subd8_2 [3, 4, 0] = true := by decide +kernel
theorem subd8_2_1314 : subd8_2 [3, 4, 1] = true := by decide +kernel
theorem subd8_2_1315 : subd8_2 [3, 4, 2] = true := by decide +kernel
theorem subd8_2_1316 : subd8_2 [3, 4, 3] = true := by decide +kernel
theorem subd8_2_1317 : subd8_2 [3, 4, 4] = true := by decide +kernel
theorem subd8_2_1318 : subd8_2 [3, 5] = true := by decide +kernel
theorem subd8_2_1319 : subd8_2 [4, -3] = true := by decide +kernel
theorem subd8_2_1320 : subd8_2 [4, -2] = true := by decide +kernel
theorem subd8_2_1321 : subd8_2 [4, -1] = true := by decide +kernel
theorem subd8_2_1322 : subd8_2 [4, 0, -9] = true := by decide +kernel
theorem subd8_2_1323 : subd8_2 [4, 0, -8] = true := by decide +kernel
theorem subd8_2_1324 : subd8_2 [4, 0, -7] = true := by decide +kernel
theorem subd8_2_1325 : subd8_2 [4, 0, -6] = true := by decide +kernel
theorem subd8_2_1326 : subd8_2 [4, 0, -5] = true := by decide +kernel
theorem subd8_2_1327 : subd8_2 [4, 0, -4] = true := by decide +kernel
theorem subd8_2_1328 : subd8_2 [4, 0, -3] = true := by decide +kernel
theorem subd8_2_1329 : subd8_2 [4, 0, -2] = true := by decide +kernel
theorem subd8_2_1330 : subd8_2 [4, 0, -1] = true := by decide +kernel
theorem subd8_2_1331 : subd8_2 [4, 0, 0] = true := by decide +kernel
theorem subd8_2_1332 : subd8_2 [4, 0, 1] = true := by decide +kernel
theorem subd8_2_1333 : subd8_2 [4, 0, 2] = true := by decide +kernel
theorem subd8_2_1334 : subd8_2 [4, 0, 3] = true := by decide +kernel
theorem subd8_2_1335 : subd8_2 [4, 0, 4] = true := by decide +kernel
theorem subd8_2_1336 : subd8_2 [4, 0, 5] = true := by decide +kernel
theorem subd8_2_1337 : subd8_2 [4, 1, -10] = true := by decide +kernel
theorem subd8_2_1338 : subd8_2 [4, 1, -9] = true := by decide +kernel
theorem subd8_2_1339 : subd8_2 [4, 1, -8] = true := by decide +kernel
theorem subd8_2_1340 : subd8_2 [4, 1, -7] = true := by decide +kernel
theorem subd8_2_1341 : subd8_2 [4, 1, -6] = true := by decide +kernel
theorem subd8_2_1342 : subd8_2 [4, 1, -5] = true := by decide +kernel
theorem subd8_2_1343 : subd8_2 [4, 1, -4] = true := by decide +kernel
theorem sbd8_2_41 : ∀ q ∈ blkd8_2_41, subd8_2 q = true := by
  unfold blkd8_2_41
  exact List.forall_mem_cons.2 ⟨subd8_2_1312, List.forall_mem_cons.2 ⟨subd8_2_1313, List.forall_mem_cons.2 ⟨subd8_2_1314, List.forall_mem_cons.2 ⟨subd8_2_1315, List.forall_mem_cons.2 ⟨subd8_2_1316, List.forall_mem_cons.2 ⟨subd8_2_1317, List.forall_mem_cons.2 ⟨subd8_2_1318, List.forall_mem_cons.2 ⟨subd8_2_1319, List.forall_mem_cons.2 ⟨subd8_2_1320, List.forall_mem_cons.2 ⟨subd8_2_1321, List.forall_mem_cons.2 ⟨subd8_2_1322, List.forall_mem_cons.2 ⟨subd8_2_1323, List.forall_mem_cons.2 ⟨subd8_2_1324, List.forall_mem_cons.2 ⟨subd8_2_1325, List.forall_mem_cons.2 ⟨subd8_2_1326, List.forall_mem_cons.2 ⟨subd8_2_1327, List.forall_mem_cons.2 ⟨subd8_2_1328, List.forall_mem_cons.2 ⟨subd8_2_1329, List.forall_mem_cons.2 ⟨subd8_2_1330, List.forall_mem_cons.2 ⟨subd8_2_1331, List.forall_mem_cons.2 ⟨subd8_2_1332, List.forall_mem_cons.2 ⟨subd8_2_1333, List.forall_mem_cons.2 ⟨subd8_2_1334, List.forall_mem_cons.2 ⟨subd8_2_1335, List.forall_mem_cons.2 ⟨subd8_2_1336, List.forall_mem_cons.2 ⟨subd8_2_1337, List.forall_mem_cons.2 ⟨subd8_2_1338, List.forall_mem_cons.2 ⟨subd8_2_1339, List.forall_mem_cons.2 ⟨subd8_2_1340, List.forall_mem_cons.2 ⟨subd8_2_1341, List.forall_mem_cons.2 ⟨subd8_2_1342, List.forall_mem_cons.2 ⟨subd8_2_1343, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_1344 : subd8_2 [4, 1, -3] = true := by decide +kernel
theorem subd8_2_1345 : subd8_2 [4, 1, -2] = true := by decide +kernel
theorem subd8_2_1346 : subd8_2 [4, 1, -1] = true := by decide +kernel
theorem subd8_2_1347 : subd8_2 [4, 1, 0] = true := by decide +kernel
theorem subd8_2_1348 : subd8_2 [4, 1, 1] = true := by decide +kernel
theorem subd8_2_1349 : subd8_2 [4, 1, 2] = true := by decide +kernel
theorem subd8_2_1350 : subd8_2 [4, 1, 3] = true := by decide +kernel
theorem subd8_2_1351 : subd8_2 [4, 1, 4] = true := by decide +kernel
theorem subd8_2_1352 : subd8_2 [4, 1, 5] = true := by decide +kernel
theorem subd8_2_1353 : subd8_2 [4, 2, -10] = true := by decide +kernel
theorem subd8_2_1354 : subd8_2 [4, 2, -9] = true := by decide +kernel
theorem subd8_2_1355 : subd8_2 [4, 2, -8] = true := by decide +kernel
theorem subd8_2_1356 : subd8_2 [4, 2, -7] = true := by decide +kernel
theorem subd8_2_1357 : subd8_2 [4, 2, -6] = true := by decide +kernel
theorem subd8_2_1358 : subd8_2 [4, 2, -5] = true := by decide +kernel
theorem subd8_2_1359 : subd8_2 [4, 2, -4] = true := by decide +kernel
theorem subd8_2_1360 : subd8_2 [4, 2, -3] = true := by decide +kernel
theorem subd8_2_1361 : subd8_2 [4, 2, -2] = true := by decide +kernel
theorem subd8_2_1362 : subd8_2 [4, 2, -1] = true := by decide +kernel
theorem subd8_2_1363 : subd8_2 [4, 2, 0] = true := by decide +kernel
theorem subd8_2_1364 : subd8_2 [4, 2, 1] = true := by decide +kernel
theorem subd8_2_1365 : subd8_2 [4, 2, 2] = true := by decide +kernel
theorem subd8_2_1366 : subd8_2 [4, 2, 3] = true := by decide +kernel
theorem subd8_2_1367 : subd8_2 [4, 2, 4] = true := by decide +kernel
theorem subd8_2_1368 : subd8_2 [4, 2, 5] = true := by decide +kernel
theorem subd8_2_1369 : subd8_2 [4, 3, -10] = true := by decide +kernel
theorem subd8_2_1370 : subd8_2 [4, 3, -9] = true := by decide +kernel
theorem subd8_2_1371 : subd8_2 [4, 3, -8] = true := by decide +kernel
theorem subd8_2_1372 : subd8_2 [4, 3, -7] = true := by decide +kernel
theorem subd8_2_1373 : subd8_2 [4, 3, -6] = true := by decide +kernel
theorem subd8_2_1374 : subd8_2 [4, 3, -5] = true := by decide +kernel
theorem subd8_2_1375 : subd8_2 [4, 3, -4] = true := by decide +kernel
theorem sbd8_2_42 : ∀ q ∈ blkd8_2_42, subd8_2 q = true := by
  unfold blkd8_2_42
  exact List.forall_mem_cons.2 ⟨subd8_2_1344, List.forall_mem_cons.2 ⟨subd8_2_1345, List.forall_mem_cons.2 ⟨subd8_2_1346, List.forall_mem_cons.2 ⟨subd8_2_1347, List.forall_mem_cons.2 ⟨subd8_2_1348, List.forall_mem_cons.2 ⟨subd8_2_1349, List.forall_mem_cons.2 ⟨subd8_2_1350, List.forall_mem_cons.2 ⟨subd8_2_1351, List.forall_mem_cons.2 ⟨subd8_2_1352, List.forall_mem_cons.2 ⟨subd8_2_1353, List.forall_mem_cons.2 ⟨subd8_2_1354, List.forall_mem_cons.2 ⟨subd8_2_1355, List.forall_mem_cons.2 ⟨subd8_2_1356, List.forall_mem_cons.2 ⟨subd8_2_1357, List.forall_mem_cons.2 ⟨subd8_2_1358, List.forall_mem_cons.2 ⟨subd8_2_1359, List.forall_mem_cons.2 ⟨subd8_2_1360, List.forall_mem_cons.2 ⟨subd8_2_1361, List.forall_mem_cons.2 ⟨subd8_2_1362, List.forall_mem_cons.2 ⟨subd8_2_1363, List.forall_mem_cons.2 ⟨subd8_2_1364, List.forall_mem_cons.2 ⟨subd8_2_1365, List.forall_mem_cons.2 ⟨subd8_2_1366, List.forall_mem_cons.2 ⟨subd8_2_1367, List.forall_mem_cons.2 ⟨subd8_2_1368, List.forall_mem_cons.2 ⟨subd8_2_1369, List.forall_mem_cons.2 ⟨subd8_2_1370, List.forall_mem_cons.2 ⟨subd8_2_1371, List.forall_mem_cons.2 ⟨subd8_2_1372, List.forall_mem_cons.2 ⟨subd8_2_1373, List.forall_mem_cons.2 ⟨subd8_2_1374, List.forall_mem_cons.2 ⟨subd8_2_1375, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_1376 : subd8_2 [4, 3, -3] = true := by decide +kernel
theorem subd8_2_1377 : subd8_2 [4, 3, -2] = true := by decide +kernel
theorem subd8_2_1378 : subd8_2 [4, 3, -1] = true := by decide +kernel
theorem subd8_2_1379 : subd8_2 [4, 3, 0] = true := by decide +kernel
theorem subd8_2_1380 : subd8_2 [4, 3, 1] = true := by decide +kernel
theorem subd8_2_1381 : subd8_2 [4, 3, 2] = true := by decide +kernel
theorem subd8_2_1382 : subd8_2 [4, 3, 3] = true := by decide +kernel
theorem subd8_2_1383 : subd8_2 [4, 4] = true := by decide +kernel
theorem subd8_2_1384 : subd8_2 [5] = true := by decide +kernel
theorem sbd8_2_43 : ∀ q ∈ blkd8_2_43, subd8_2 q = true := by
  unfold blkd8_2_43
  exact List.forall_mem_cons.2 ⟨subd8_2_1376, List.forall_mem_cons.2 ⟨subd8_2_1377, List.forall_mem_cons.2 ⟨subd8_2_1378, List.forall_mem_cons.2 ⟨subd8_2_1379, List.forall_mem_cons.2 ⟨subd8_2_1380, List.forall_mem_cons.2 ⟨subd8_2_1381, List.forall_mem_cons.2 ⟨subd8_2_1382, List.forall_mem_cons.2 ⟨subd8_2_1383, List.forall_mem_cons.2 ⟨subd8_2_1384, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_3 : ldCheck G d8_3.U d8_3.ms ldd8_3 = true := by decide +kernel
theorem pre_okd8_3 : subPre G cell8 d8_3 = true := by decide +kernel
theorem subd8_3_0 : subd8_3 [-3] = true := by decide +kernel
theorem subd8_3_1 : subd8_3 [-2, -4] = true := by decide +kernel
theorem subd8_3_2 : subd8_3 [-2, -3] = true := by decide +kernel
theorem subd8_3_3 : subd8_3 [-2, -2] = true := by decide +kernel
theorem subd8_3_4 : subd8_3 [-2, -1] = true := by decide +kernel
theorem subd8_3_5 : subd8_3 [-2, 0] = true := by decide +kernel
theorem subd8_3_6 : subd8_3 [-2, 1] = true := by decide +kernel
theorem subd8_3_7 : subd8_3 [-2, 2] = true := by decide +kernel
theorem subd8_3_8 : subd8_3 [-2, 3] = true := by decide +kernel
theorem subd8_3_9 : subd8_3 [-1, -4] = true := by decide +kernel
theorem subd8_3_10 : subd8_3 [-1, -3] = true := by decide +kernel
theorem subd8_3_11 : subd8_3 [-1, -2] = true := by decide +kernel
theorem subd8_3_12 : subd8_3 [-1, -1] = true := by decide +kernel
theorem subd8_3_13 : subd8_3 [-1, 0] = true := by decide +kernel
theorem subd8_3_14 : subd8_3 [-1, 1] = true := by decide +kernel
theorem subd8_3_15 : subd8_3 [-1, 2] = true := by decide +kernel
theorem subd8_3_16 : subd8_3 [-1, 3] = true := by decide +kernel
theorem subd8_3_17 : subd8_3 [0, -4] = true := by decide +kernel
theorem subd8_3_18 : subd8_3 [0, -3] = true := by decide +kernel
theorem subd8_3_19 : subd8_3 [0, -2] = true := by decide +kernel
theorem subd8_3_20 : subd8_3 [0, -1] = true := by decide +kernel
theorem subd8_3_21 : subd8_3 [0, 0] = true := by decide +kernel
theorem subd8_3_22 : subd8_3 [0, 1] = true := by decide +kernel
theorem subd8_3_23 : subd8_3 [0, 2] = true := by decide +kernel
theorem subd8_3_24 : subd8_3 [0, 3] = true := by decide +kernel
theorem subd8_3_25 : subd8_3 [1, -4] = true := by decide +kernel
theorem subd8_3_26 : subd8_3 [1, -3] = true := by decide +kernel
theorem subd8_3_27 : subd8_3 [1, -2] = true := by decide +kernel
theorem subd8_3_28 : subd8_3 [1, -1] = true := by decide +kernel
theorem subd8_3_29 : subd8_3 [1, 0] = true := by decide +kernel
theorem subd8_3_30 : subd8_3 [1, 1] = true := by decide +kernel
theorem subd8_3_31 : subd8_3 [1, 2] = true := by decide +kernel
theorem sbd8_3_0 : ∀ q ∈ blkd8_3_0, subd8_3 q = true := by
  unfold blkd8_3_0
  exact List.forall_mem_cons.2 ⟨subd8_3_0, List.forall_mem_cons.2 ⟨subd8_3_1, List.forall_mem_cons.2 ⟨subd8_3_2, List.forall_mem_cons.2 ⟨subd8_3_3, List.forall_mem_cons.2 ⟨subd8_3_4, List.forall_mem_cons.2 ⟨subd8_3_5, List.forall_mem_cons.2 ⟨subd8_3_6, List.forall_mem_cons.2 ⟨subd8_3_7, List.forall_mem_cons.2 ⟨subd8_3_8, List.forall_mem_cons.2 ⟨subd8_3_9, List.forall_mem_cons.2 ⟨subd8_3_10, List.forall_mem_cons.2 ⟨subd8_3_11, List.forall_mem_cons.2 ⟨subd8_3_12, List.forall_mem_cons.2 ⟨subd8_3_13, List.forall_mem_cons.2 ⟨subd8_3_14, List.forall_mem_cons.2 ⟨subd8_3_15, List.forall_mem_cons.2 ⟨subd8_3_16, List.forall_mem_cons.2 ⟨subd8_3_17, List.forall_mem_cons.2 ⟨subd8_3_18, List.forall_mem_cons.2 ⟨subd8_3_19, List.forall_mem_cons.2 ⟨subd8_3_20, List.forall_mem_cons.2 ⟨subd8_3_21, List.forall_mem_cons.2 ⟨subd8_3_22, List.forall_mem_cons.2 ⟨subd8_3_23, List.forall_mem_cons.2 ⟨subd8_3_24, List.forall_mem_cons.2 ⟨subd8_3_25, List.forall_mem_cons.2 ⟨subd8_3_26, List.forall_mem_cons.2 ⟨subd8_3_27, List.forall_mem_cons.2 ⟨subd8_3_28, List.forall_mem_cons.2 ⟨subd8_3_29, List.forall_mem_cons.2 ⟨subd8_3_30, List.forall_mem_cons.2 ⟨subd8_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_32 : subd8_3 [1, 3] = true := by decide +kernel
theorem subd8_3_33 : subd8_3 [2, -4] = true := by decide +kernel
theorem subd8_3_34 : subd8_3 [2, -3] = true := by decide +kernel
theorem subd8_3_35 : subd8_3 [2, -2] = true := by decide +kernel
theorem subd8_3_36 : subd8_3 [2, -1] = true := by decide +kernel
theorem subd8_3_37 : subd8_3 [2, 0] = true := by decide +kernel
theorem subd8_3_38 : subd8_3 [2, 1] = true := by decide +kernel
theorem subd8_3_39 : subd8_3 [2, 2] = true := by decide +kernel
theorem subd8_3_40 : subd8_3 [2, 3] = true := by decide +kernel
theorem subd8_3_41 : subd8_3 [3] = true := by decide +kernel
theorem sbd8_3_1 : ∀ q ∈ blkd8_3_1, subd8_3 q = true := by
  unfold blkd8_3_1
  exact List.forall_mem_cons.2 ⟨subd8_3_32, List.forall_mem_cons.2 ⟨subd8_3_33, List.forall_mem_cons.2 ⟨subd8_3_34, List.forall_mem_cons.2 ⟨subd8_3_35, List.forall_mem_cons.2 ⟨subd8_3_36, List.forall_mem_cons.2 ⟨subd8_3_37, List.forall_mem_cons.2 ⟨subd8_3_38, List.forall_mem_cons.2 ⟨subd8_3_39, List.forall_mem_cons.2 ⟨subd8_3_40, List.forall_mem_cons.2 ⟨subd8_3_41, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_0 : ldCheck G d9_0.U d9_0.ms ldd9_0 = true := by decide +kernel
theorem pre_okd9_0 : subPre G cell9 d9_0 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C142
