import ReflectZphi.Data.Cert5.C096.Base

namespace ReflectZphi.Data.Cert5.C096

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_3_1216 : subd7_3 [2, 4, 1] = true := by decide +kernel
theorem subd7_3_1217 : subd7_3 [2, 4, 2] = true := by decide +kernel
theorem subd7_3_1218 : subd7_3 [2, 4, 3] = true := by decide +kernel
theorem subd7_3_1219 : subd7_3 [2, 4, 4] = true := by decide +kernel
theorem subd7_3_1220 : subd7_3 [2, 4, 5] = true := by decide +kernel
theorem subd7_3_1221 : subd7_3 [2, 4, 6] = true := by decide +kernel
theorem subd7_3_1222 : subd7_3 [2, 4, 7] = true := by decide +kernel
theorem subd7_3_1223 : subd7_3 [2, 5, -6] = true := by decide +kernel
theorem subd7_3_1224 : subd7_3 [2, 5, -5] = true := by decide +kernel
theorem subd7_3_1225 : subd7_3 [2, 5, -4] = true := by decide +kernel
theorem subd7_3_1226 : subd7_3 [2, 5, -3] = true := by decide +kernel
theorem subd7_3_1227 : subd7_3 [2, 5, -2] = true := by decide +kernel
theorem subd7_3_1228 : subd7_3 [2, 5, -1] = true := by decide +kernel
theorem subd7_3_1229 : subd7_3 [2, 5, 0] = true := by decide +kernel
theorem subd7_3_1230 : subd7_3 [2, 5, 1] = true := by decide +kernel
theorem subd7_3_1231 : subd7_3 [2, 5, 2] = true := by decide +kernel
theorem subd7_3_1232 : subd7_3 [2, 5, 3] = true := by decide +kernel
theorem subd7_3_1233 : subd7_3 [2, 5, 4] = true := by decide +kernel
theorem subd7_3_1234 : subd7_3 [2, 5, 5] = true := by decide +kernel
theorem subd7_3_1235 : subd7_3 [2, 5, 6] = true := by decide +kernel
theorem subd7_3_1236 : subd7_3 [2, 6] = true := by decide +kernel
theorem subd7_3_1237 : subd7_3 [2, 7] = true := by decide +kernel
theorem subd7_3_1238 : subd7_3 [2, 8] = true := by decide +kernel
theorem subd7_3_1239 : subd7_3 [3, -9] = true := by decide +kernel
theorem subd7_3_1240 : subd7_3 [3, -8] = true := by decide +kernel
theorem subd7_3_1241 : subd7_3 [3, -7] = true := by decide +kernel
theorem subd7_3_1242 : subd7_3 [3, -6] = true := by decide +kernel
theorem subd7_3_1243 : subd7_3 [3, -5] = true := by decide +kernel
theorem subd7_3_1244 : subd7_3 [3, -4, -5] = true := by decide +kernel
theorem subd7_3_1245 : subd7_3 [3, -4, -4] = true := by decide +kernel
theorem subd7_3_1246 : subd7_3 [3, -4, -3] = true := by decide +kernel
theorem subd7_3_1247 : subd7_3 [3, -4, -2] = true := by decide +kernel
theorem sbd7_3_38 : ∀ q ∈ blkd7_3_38, subd7_3 q = true := by
  unfold blkd7_3_38
  exact List.forall_mem_cons.2 ⟨subd7_3_1216, List.forall_mem_cons.2 ⟨subd7_3_1217, List.forall_mem_cons.2 ⟨subd7_3_1218, List.forall_mem_cons.2 ⟨subd7_3_1219, List.forall_mem_cons.2 ⟨subd7_3_1220, List.forall_mem_cons.2 ⟨subd7_3_1221, List.forall_mem_cons.2 ⟨subd7_3_1222, List.forall_mem_cons.2 ⟨subd7_3_1223, List.forall_mem_cons.2 ⟨subd7_3_1224, List.forall_mem_cons.2 ⟨subd7_3_1225, List.forall_mem_cons.2 ⟨subd7_3_1226, List.forall_mem_cons.2 ⟨subd7_3_1227, List.forall_mem_cons.2 ⟨subd7_3_1228, List.forall_mem_cons.2 ⟨subd7_3_1229, List.forall_mem_cons.2 ⟨subd7_3_1230, List.forall_mem_cons.2 ⟨subd7_3_1231, List.forall_mem_cons.2 ⟨subd7_3_1232, List.forall_mem_cons.2 ⟨subd7_3_1233, List.forall_mem_cons.2 ⟨subd7_3_1234, List.forall_mem_cons.2 ⟨subd7_3_1235, List.forall_mem_cons.2 ⟨subd7_3_1236, List.forall_mem_cons.2 ⟨subd7_3_1237, List.forall_mem_cons.2 ⟨subd7_3_1238, List.forall_mem_cons.2 ⟨subd7_3_1239, List.forall_mem_cons.2 ⟨subd7_3_1240, List.forall_mem_cons.2 ⟨subd7_3_1241, List.forall_mem_cons.2 ⟨subd7_3_1242, List.forall_mem_cons.2 ⟨subd7_3_1243, List.forall_mem_cons.2 ⟨subd7_3_1244, List.forall_mem_cons.2 ⟨subd7_3_1245, List.forall_mem_cons.2 ⟨subd7_3_1246, List.forall_mem_cons.2 ⟨subd7_3_1247, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_1248 : subd7_3 [3, -4, -1] = true := by decide +kernel
theorem subd7_3_1249 : subd7_3 [3, -4, 0] = true := by decide +kernel
theorem subd7_3_1250 : subd7_3 [3, -4, 1] = true := by decide +kernel
theorem subd7_3_1251 : subd7_3 [3, -4, 2] = true := by decide +kernel
theorem subd7_3_1252 : subd7_3 [3, -4, 3] = true := by decide +kernel
theorem subd7_3_1253 : subd7_3 [3, -4, 4] = true := by decide +kernel
theorem subd7_3_1254 : subd7_3 [3, -4, 5] = true := by decide +kernel
theorem subd7_3_1255 : subd7_3 [3, -4, 6] = true := by decide +kernel
theorem subd7_3_1256 : subd7_3 [3, -4, 7] = true := by decide +kernel
theorem subd7_3_1257 : subd7_3 [3, -4, 8] = true := by decide +kernel
theorem subd7_3_1258 : subd7_3 [3, -3, -6] = true := by decide +kernel
theorem subd7_3_1259 : subd7_3 [3, -3, -5] = true := by decide +kernel
theorem subd7_3_1260 : subd7_3 [3, -3, -4] = true := by decide +kernel
theorem subd7_3_1261 : subd7_3 [3, -3, -3] = true := by decide +kernel
theorem subd7_3_1262 : subd7_3 [3, -3, -2] = true := by decide +kernel
theorem subd7_3_1263 : subd7_3 [3, -3, -1] = true := by decide +kernel
theorem subd7_3_1264 : subd7_3 [3, -3, 0] = true := by decide +kernel
theorem subd7_3_1265 : subd7_3 [3, -3, 1] = true := by decide +kernel
theorem subd7_3_1266 : subd7_3 [3, -3, 2] = true := by decide +kernel
theorem subd7_3_1267 : subd7_3 [3, -3, 3] = true := by decide +kernel
theorem subd7_3_1268 : subd7_3 [3, -3, 4] = true := by decide +kernel
theorem subd7_3_1269 : subd7_3 [3, -3, 5] = true := by decide +kernel
theorem subd7_3_1270 : subd7_3 [3, -3, 6] = true := by decide +kernel
theorem subd7_3_1271 : subd7_3 [3, -3, 7] = true := by decide +kernel
theorem subd7_3_1272 : subd7_3 [3, -3, 8] = true := by decide +kernel
theorem subd7_3_1273 : subd7_3 [3, -2, -6] = true := by decide +kernel
theorem subd7_3_1274 : subd7_3 [3, -2, -5] = true := by decide +kernel
theorem subd7_3_1275 : subd7_3 [3, -2, -4] = true := by decide +kernel
theorem subd7_3_1276 : subd7_3 [3, -2, -3] = true := by decide +kernel
theorem subd7_3_1277 : subd7_3 [3, -2, -2] = true := by decide +kernel
theorem subd7_3_1278 : subd7_3 [3, -2, -1] = true := by decide +kernel
theorem subd7_3_1279 : subd7_3 [3, -2, 0] = true := by decide +kernel
theorem sbd7_3_39 : ∀ q ∈ blkd7_3_39, subd7_3 q = true := by
  unfold blkd7_3_39
  exact List.forall_mem_cons.2 ⟨subd7_3_1248, List.forall_mem_cons.2 ⟨subd7_3_1249, List.forall_mem_cons.2 ⟨subd7_3_1250, List.forall_mem_cons.2 ⟨subd7_3_1251, List.forall_mem_cons.2 ⟨subd7_3_1252, List.forall_mem_cons.2 ⟨subd7_3_1253, List.forall_mem_cons.2 ⟨subd7_3_1254, List.forall_mem_cons.2 ⟨subd7_3_1255, List.forall_mem_cons.2 ⟨subd7_3_1256, List.forall_mem_cons.2 ⟨subd7_3_1257, List.forall_mem_cons.2 ⟨subd7_3_1258, List.forall_mem_cons.2 ⟨subd7_3_1259, List.forall_mem_cons.2 ⟨subd7_3_1260, List.forall_mem_cons.2 ⟨subd7_3_1261, List.forall_mem_cons.2 ⟨subd7_3_1262, List.forall_mem_cons.2 ⟨subd7_3_1263, List.forall_mem_cons.2 ⟨subd7_3_1264, List.forall_mem_cons.2 ⟨subd7_3_1265, List.forall_mem_cons.2 ⟨subd7_3_1266, List.forall_mem_cons.2 ⟨subd7_3_1267, List.forall_mem_cons.2 ⟨subd7_3_1268, List.forall_mem_cons.2 ⟨subd7_3_1269, List.forall_mem_cons.2 ⟨subd7_3_1270, List.forall_mem_cons.2 ⟨subd7_3_1271, List.forall_mem_cons.2 ⟨subd7_3_1272, List.forall_mem_cons.2 ⟨subd7_3_1273, List.forall_mem_cons.2 ⟨subd7_3_1274, List.forall_mem_cons.2 ⟨subd7_3_1275, List.forall_mem_cons.2 ⟨subd7_3_1276, List.forall_mem_cons.2 ⟨subd7_3_1277, List.forall_mem_cons.2 ⟨subd7_3_1278, List.forall_mem_cons.2 ⟨subd7_3_1279, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_1280 : subd7_3 [3, -2, 1] = true := by decide +kernel
theorem subd7_3_1281 : subd7_3 [3, -2, 2] = true := by decide +kernel
theorem subd7_3_1282 : subd7_3 [3, -2, 3] = true := by decide +kernel
theorem subd7_3_1283 : subd7_3 [3, -2, 4] = true := by decide +kernel
theorem subd7_3_1284 : subd7_3 [3, -2, 5] = true := by decide +kernel
theorem subd7_3_1285 : subd7_3 [3, -2, 6] = true := by decide +kernel
theorem subd7_3_1286 : subd7_3 [3, -2, 7] = true := by decide +kernel
theorem subd7_3_1287 : subd7_3 [3, -2, 8] = true := by decide +kernel
theorem subd7_3_1288 : subd7_3 [3, -1, -6] = true := by decide +kernel
theorem subd7_3_1289 : subd7_3 [3, -1, -5] = true := by decide +kernel
theorem subd7_3_1290 : subd7_3 [3, -1, -4] = true := by decide +kernel
theorem subd7_3_1291 : subd7_3 [3, -1, -3] = true := by decide +kernel
theorem subd7_3_1292 : subd7_3 [3, -1, -2] = true := by decide +kernel
theorem subd7_3_1293 : subd7_3 [3, -1, -1] = true := by decide +kernel
theorem subd7_3_1294 : subd7_3 [3, -1, 0] = true := by decide +kernel
theorem subd7_3_1295 : subd7_3 [3, -1, 1] = true := by decide +kernel
theorem subd7_3_1296 : subd7_3 [3, -1, 2] = true := by decide +kernel
theorem subd7_3_1297 : subd7_3 [3, -1, 3] = true := by decide +kernel
theorem subd7_3_1298 : subd7_3 [3, -1, 4] = true := by decide +kernel
theorem subd7_3_1299 : subd7_3 [3, -1, 5] = true := by decide +kernel
theorem subd7_3_1300 : subd7_3 [3, -1, 6] = true := by decide +kernel
theorem subd7_3_1301 : subd7_3 [3, -1, 7] = true := by decide +kernel
theorem subd7_3_1302 : subd7_3 [3, -1, 8] = true := by decide +kernel
theorem subd7_3_1303 : subd7_3 [3, 0, -6] = true := by decide +kernel
theorem subd7_3_1304 : subd7_3 [3, 0, -5] = true := by decide +kernel
theorem subd7_3_1305 : subd7_3 [3, 0, -4] = true := by decide +kernel
theorem subd7_3_1306 : subd7_3 [3, 0, -3] = true := by decide +kernel
theorem subd7_3_1307 : subd7_3 [3, 0, -2] = true := by decide +kernel
theorem subd7_3_1308 : subd7_3 [3, 0, -1] = true := by decide +kernel
theorem subd7_3_1309 : subd7_3 [3, 0, 0] = true := by decide +kernel
theorem subd7_3_1310 : subd7_3 [3, 0, 1] = true := by decide +kernel
theorem subd7_3_1311 : subd7_3 [3, 0, 2] = true := by decide +kernel
theorem sbd7_3_40 : ∀ q ∈ blkd7_3_40, subd7_3 q = true := by
  unfold blkd7_3_40
  exact List.forall_mem_cons.2 ⟨subd7_3_1280, List.forall_mem_cons.2 ⟨subd7_3_1281, List.forall_mem_cons.2 ⟨subd7_3_1282, List.forall_mem_cons.2 ⟨subd7_3_1283, List.forall_mem_cons.2 ⟨subd7_3_1284, List.forall_mem_cons.2 ⟨subd7_3_1285, List.forall_mem_cons.2 ⟨subd7_3_1286, List.forall_mem_cons.2 ⟨subd7_3_1287, List.forall_mem_cons.2 ⟨subd7_3_1288, List.forall_mem_cons.2 ⟨subd7_3_1289, List.forall_mem_cons.2 ⟨subd7_3_1290, List.forall_mem_cons.2 ⟨subd7_3_1291, List.forall_mem_cons.2 ⟨subd7_3_1292, List.forall_mem_cons.2 ⟨subd7_3_1293, List.forall_mem_cons.2 ⟨subd7_3_1294, List.forall_mem_cons.2 ⟨subd7_3_1295, List.forall_mem_cons.2 ⟨subd7_3_1296, List.forall_mem_cons.2 ⟨subd7_3_1297, List.forall_mem_cons.2 ⟨subd7_3_1298, List.forall_mem_cons.2 ⟨subd7_3_1299, List.forall_mem_cons.2 ⟨subd7_3_1300, List.forall_mem_cons.2 ⟨subd7_3_1301, List.forall_mem_cons.2 ⟨subd7_3_1302, List.forall_mem_cons.2 ⟨subd7_3_1303, List.forall_mem_cons.2 ⟨subd7_3_1304, List.forall_mem_cons.2 ⟨subd7_3_1305, List.forall_mem_cons.2 ⟨subd7_3_1306, List.forall_mem_cons.2 ⟨subd7_3_1307, List.forall_mem_cons.2 ⟨subd7_3_1308, List.forall_mem_cons.2 ⟨subd7_3_1309, List.forall_mem_cons.2 ⟨subd7_3_1310, List.forall_mem_cons.2 ⟨subd7_3_1311, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_1312 : subd7_3 [3, 0, 3] = true := by decide +kernel
theorem subd7_3_1313 : subd7_3 [3, 0, 4] = true := by decide +kernel
theorem subd7_3_1314 : subd7_3 [3, 0, 5] = true := by decide +kernel
theorem subd7_3_1315 : subd7_3 [3, 0, 6] = true := by decide +kernel
theorem subd7_3_1316 : subd7_3 [3, 0, 7] = true := by decide +kernel
theorem subd7_3_1317 : subd7_3 [3, 0, 8] = true := by decide +kernel
theorem subd7_3_1318 : subd7_3 [3, 1, -7] = true := by decide +kernel
theorem subd7_3_1319 : subd7_3 [3, 1, -6] = true := by decide +kernel
theorem subd7_3_1320 : subd7_3 [3, 1, -5] = true := by decide +kernel
theorem subd7_3_1321 : subd7_3 [3, 1, -4] = true := by decide +kernel
theorem subd7_3_1322 : subd7_3 [3, 1, -3] = true := by decide +kernel
theorem subd7_3_1323 : subd7_3 [3, 1, -2] = true := by decide +kernel
theorem subd7_3_1324 : subd7_3 [3, 1, -1] = true := by decide +kernel
theorem subd7_3_1325 : subd7_3 [3, 1, 0] = true := by decide +kernel
theorem subd7_3_1326 : subd7_3 [3, 1, 1] = true := by decide +kernel
theorem subd7_3_1327 : subd7_3 [3, 1, 2] = true := by decide +kernel
theorem subd7_3_1328 : subd7_3 [3, 1, 3] = true := by decide +kernel
theorem subd7_3_1329 : subd7_3 [3, 1, 4] = true := by decide +kernel
theorem subd7_3_1330 : subd7_3 [3, 1, 5] = true := by decide +kernel
theorem subd7_3_1331 : subd7_3 [3, 1, 6] = true := by decide +kernel
theorem subd7_3_1332 : subd7_3 [3, 1, 7] = true := by decide +kernel
theorem subd7_3_1333 : subd7_3 [3, 1, 8] = true := by decide +kernel
theorem subd7_3_1334 : subd7_3 [3, 2, -6] = true := by decide +kernel
theorem subd7_3_1335 : subd7_3 [3, 2, -5] = true := by decide +kernel
theorem subd7_3_1336 : subd7_3 [3, 2, -4] = true := by decide +kernel
theorem subd7_3_1337 : subd7_3 [3, 2, -3] = true := by decide +kernel
theorem subd7_3_1338 : subd7_3 [3, 2, -2] = true := by decide +kernel
theorem subd7_3_1339 : subd7_3 [3, 2, -1] = true := by decide +kernel
theorem subd7_3_1340 : subd7_3 [3, 2, 0] = true := by decide +kernel
theorem subd7_3_1341 : subd7_3 [3, 2, 1] = true := by decide +kernel
theorem subd7_3_1342 : subd7_3 [3, 2, 2] = true := by decide +kernel
theorem subd7_3_1343 : subd7_3 [3, 2, 3] = true := by decide +kernel
theorem sbd7_3_41 : ∀ q ∈ blkd7_3_41, subd7_3 q = true := by
  unfold blkd7_3_41
  exact List.forall_mem_cons.2 ⟨subd7_3_1312, List.forall_mem_cons.2 ⟨subd7_3_1313, List.forall_mem_cons.2 ⟨subd7_3_1314, List.forall_mem_cons.2 ⟨subd7_3_1315, List.forall_mem_cons.2 ⟨subd7_3_1316, List.forall_mem_cons.2 ⟨subd7_3_1317, List.forall_mem_cons.2 ⟨subd7_3_1318, List.forall_mem_cons.2 ⟨subd7_3_1319, List.forall_mem_cons.2 ⟨subd7_3_1320, List.forall_mem_cons.2 ⟨subd7_3_1321, List.forall_mem_cons.2 ⟨subd7_3_1322, List.forall_mem_cons.2 ⟨subd7_3_1323, List.forall_mem_cons.2 ⟨subd7_3_1324, List.forall_mem_cons.2 ⟨subd7_3_1325, List.forall_mem_cons.2 ⟨subd7_3_1326, List.forall_mem_cons.2 ⟨subd7_3_1327, List.forall_mem_cons.2 ⟨subd7_3_1328, List.forall_mem_cons.2 ⟨subd7_3_1329, List.forall_mem_cons.2 ⟨subd7_3_1330, List.forall_mem_cons.2 ⟨subd7_3_1331, List.forall_mem_cons.2 ⟨subd7_3_1332, List.forall_mem_cons.2 ⟨subd7_3_1333, List.forall_mem_cons.2 ⟨subd7_3_1334, List.forall_mem_cons.2 ⟨subd7_3_1335, List.forall_mem_cons.2 ⟨subd7_3_1336, List.forall_mem_cons.2 ⟨subd7_3_1337, List.forall_mem_cons.2 ⟨subd7_3_1338, List.forall_mem_cons.2 ⟨subd7_3_1339, List.forall_mem_cons.2 ⟨subd7_3_1340, List.forall_mem_cons.2 ⟨subd7_3_1341, List.forall_mem_cons.2 ⟨subd7_3_1342, List.forall_mem_cons.2 ⟨subd7_3_1343, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_1344 : subd7_3 [3, 2, 4] = true := by decide +kernel
theorem subd7_3_1345 : subd7_3 [3, 2, 5] = true := by decide +kernel
theorem subd7_3_1346 : subd7_3 [3, 2, 6] = true := by decide +kernel
theorem subd7_3_1347 : subd7_3 [3, 2, 7] = true := by decide +kernel
theorem subd7_3_1348 : subd7_3 [3, 2, 8] = true := by decide +kernel
theorem subd7_3_1349 : subd7_3 [3, 3, -6] = true := by decide +kernel
theorem subd7_3_1350 : subd7_3 [3, 3, -5] = true := by decide +kernel
theorem subd7_3_1351 : subd7_3 [3, 3, -4] = true := by decide +kernel
theorem subd7_3_1352 : subd7_3 [3, 3, -3] = true := by decide +kernel
theorem subd7_3_1353 : subd7_3 [3, 3, -2] = true := by decide +kernel
theorem subd7_3_1354 : subd7_3 [3, 3, -1] = true := by decide +kernel
theorem subd7_3_1355 : subd7_3 [3, 3, 0] = true := by decide +kernel
theorem subd7_3_1356 : subd7_3 [3, 3, 1] = true := by decide +kernel
theorem subd7_3_1357 : subd7_3 [3, 3, 2] = true := by decide +kernel
theorem subd7_3_1358 : subd7_3 [3, 3, 3] = true := by decide +kernel
theorem subd7_3_1359 : subd7_3 [3, 3, 4] = true := by decide +kernel
theorem subd7_3_1360 : subd7_3 [3, 3, 5] = true := by decide +kernel
theorem subd7_3_1361 : subd7_3 [3, 3, 6] = true := by decide +kernel
theorem subd7_3_1362 : subd7_3 [3, 3, 7] = true := by decide +kernel
theorem subd7_3_1363 : subd7_3 [3, 3, 8] = true := by decide +kernel
theorem subd7_3_1364 : subd7_3 [3, 4, -6] = true := by decide +kernel
theorem subd7_3_1365 : subd7_3 [3, 4, -5] = true := by decide +kernel
theorem subd7_3_1366 : subd7_3 [3, 4, -4] = true := by decide +kernel
theorem subd7_3_1367 : subd7_3 [3, 4, -3] = true := by decide +kernel
theorem subd7_3_1368 : subd7_3 [3, 4, -2] = true := by decide +kernel
theorem subd7_3_1369 : subd7_3 [3, 4, -1] = true := by decide +kernel
theorem subd7_3_1370 : subd7_3 [3, 4, 0] = true := by decide +kernel
theorem subd7_3_1371 : subd7_3 [3, 4, 1] = true := by decide +kernel
theorem subd7_3_1372 : subd7_3 [3, 4, 2] = true := by decide +kernel
theorem subd7_3_1373 : subd7_3 [3, 4, 3] = true := by decide +kernel
theorem subd7_3_1374 : subd7_3 [3, 4, 4] = true := by decide +kernel
theorem subd7_3_1375 : subd7_3 [3, 4, 5] = true := by decide +kernel
theorem sbd7_3_42 : ∀ q ∈ blkd7_3_42, subd7_3 q = true := by
  unfold blkd7_3_42
  exact List.forall_mem_cons.2 ⟨subd7_3_1344, List.forall_mem_cons.2 ⟨subd7_3_1345, List.forall_mem_cons.2 ⟨subd7_3_1346, List.forall_mem_cons.2 ⟨subd7_3_1347, List.forall_mem_cons.2 ⟨subd7_3_1348, List.forall_mem_cons.2 ⟨subd7_3_1349, List.forall_mem_cons.2 ⟨subd7_3_1350, List.forall_mem_cons.2 ⟨subd7_3_1351, List.forall_mem_cons.2 ⟨subd7_3_1352, List.forall_mem_cons.2 ⟨subd7_3_1353, List.forall_mem_cons.2 ⟨subd7_3_1354, List.forall_mem_cons.2 ⟨subd7_3_1355, List.forall_mem_cons.2 ⟨subd7_3_1356, List.forall_mem_cons.2 ⟨subd7_3_1357, List.forall_mem_cons.2 ⟨subd7_3_1358, List.forall_mem_cons.2 ⟨subd7_3_1359, List.forall_mem_cons.2 ⟨subd7_3_1360, List.forall_mem_cons.2 ⟨subd7_3_1361, List.forall_mem_cons.2 ⟨subd7_3_1362, List.forall_mem_cons.2 ⟨subd7_3_1363, List.forall_mem_cons.2 ⟨subd7_3_1364, List.forall_mem_cons.2 ⟨subd7_3_1365, List.forall_mem_cons.2 ⟨subd7_3_1366, List.forall_mem_cons.2 ⟨subd7_3_1367, List.forall_mem_cons.2 ⟨subd7_3_1368, List.forall_mem_cons.2 ⟨subd7_3_1369, List.forall_mem_cons.2 ⟨subd7_3_1370, List.forall_mem_cons.2 ⟨subd7_3_1371, List.forall_mem_cons.2 ⟨subd7_3_1372, List.forall_mem_cons.2 ⟨subd7_3_1373, List.forall_mem_cons.2 ⟨subd7_3_1374, List.forall_mem_cons.2 ⟨subd7_3_1375, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_1376 : subd7_3 [3, 4, 6] = true := by decide +kernel
theorem subd7_3_1377 : subd7_3 [3, 4, 7] = true := by decide +kernel
theorem subd7_3_1378 : subd7_3 [3, 5] = true := by decide +kernel
theorem subd7_3_1379 : subd7_3 [3, 6] = true := by decide +kernel
theorem subd7_3_1380 : subd7_3 [3, 7] = true := by decide +kernel
theorem subd7_3_1381 : subd7_3 [3, 8] = true := by decide +kernel
theorem subd7_3_1382 : subd7_3 [4, -8] = true := by decide +kernel
theorem subd7_3_1383 : subd7_3 [4, -7] = true := by decide +kernel
theorem subd7_3_1384 : subd7_3 [4, -6] = true := by decide +kernel
theorem subd7_3_1385 : subd7_3 [4, -5] = true := by decide +kernel
theorem subd7_3_1386 : subd7_3 [4, -4] = true := by decide +kernel
theorem subd7_3_1387 : subd7_3 [4, -3, -5] = true := by decide +kernel
theorem subd7_3_1388 : subd7_3 [4, -3, -4] = true := by decide +kernel
theorem subd7_3_1389 : subd7_3 [4, -3, -3] = true := by decide +kernel
theorem subd7_3_1390 : subd7_3 [4, -3, -2] = true := by decide +kernel
theorem subd7_3_1391 : subd7_3 [4, -3, -1] = true := by decide +kernel
theorem subd7_3_1392 : subd7_3 [4, -3, 0] = true := by decide +kernel
theorem subd7_3_1393 : subd7_3 [4, -3, 1] = true := by decide +kernel
theorem subd7_3_1394 : subd7_3 [4, -3, 2] = true := by decide +kernel
theorem subd7_3_1395 : subd7_3 [4, -3, 3] = true := by decide +kernel
theorem subd7_3_1396 : subd7_3 [4, -3, 4] = true := by decide +kernel
theorem subd7_3_1397 : subd7_3 [4, -3, 5] = true := by decide +kernel
theorem subd7_3_1398 : subd7_3 [4, -3, 6] = true := by decide +kernel
theorem subd7_3_1399 : subd7_3 [4, -3, 7] = true := by decide +kernel
theorem subd7_3_1400 : subd7_3 [4, -3, 8] = true := by decide +kernel
theorem subd7_3_1401 : subd7_3 [4, -2, -5] = true := by decide +kernel
theorem subd7_3_1402 : subd7_3 [4, -2, -4] = true := by decide +kernel
theorem subd7_3_1403 : subd7_3 [4, -2, -3] = true := by decide +kernel
theorem subd7_3_1404 : subd7_3 [4, -2, -2] = true := by decide +kernel
theorem subd7_3_1405 : subd7_3 [4, -2, -1] = true := by decide +kernel
theorem subd7_3_1406 : subd7_3 [4, -2, 0] = true := by decide +kernel
theorem subd7_3_1407 : subd7_3 [4, -2, 1] = true := by decide +kernel
theorem sbd7_3_43 : ∀ q ∈ blkd7_3_43, subd7_3 q = true := by
  unfold blkd7_3_43
  exact List.forall_mem_cons.2 ⟨subd7_3_1376, List.forall_mem_cons.2 ⟨subd7_3_1377, List.forall_mem_cons.2 ⟨subd7_3_1378, List.forall_mem_cons.2 ⟨subd7_3_1379, List.forall_mem_cons.2 ⟨subd7_3_1380, List.forall_mem_cons.2 ⟨subd7_3_1381, List.forall_mem_cons.2 ⟨subd7_3_1382, List.forall_mem_cons.2 ⟨subd7_3_1383, List.forall_mem_cons.2 ⟨subd7_3_1384, List.forall_mem_cons.2 ⟨subd7_3_1385, List.forall_mem_cons.2 ⟨subd7_3_1386, List.forall_mem_cons.2 ⟨subd7_3_1387, List.forall_mem_cons.2 ⟨subd7_3_1388, List.forall_mem_cons.2 ⟨subd7_3_1389, List.forall_mem_cons.2 ⟨subd7_3_1390, List.forall_mem_cons.2 ⟨subd7_3_1391, List.forall_mem_cons.2 ⟨subd7_3_1392, List.forall_mem_cons.2 ⟨subd7_3_1393, List.forall_mem_cons.2 ⟨subd7_3_1394, List.forall_mem_cons.2 ⟨subd7_3_1395, List.forall_mem_cons.2 ⟨subd7_3_1396, List.forall_mem_cons.2 ⟨subd7_3_1397, List.forall_mem_cons.2 ⟨subd7_3_1398, List.forall_mem_cons.2 ⟨subd7_3_1399, List.forall_mem_cons.2 ⟨subd7_3_1400, List.forall_mem_cons.2 ⟨subd7_3_1401, List.forall_mem_cons.2 ⟨subd7_3_1402, List.forall_mem_cons.2 ⟨subd7_3_1403, List.forall_mem_cons.2 ⟨subd7_3_1404, List.forall_mem_cons.2 ⟨subd7_3_1405, List.forall_mem_cons.2 ⟨subd7_3_1406, List.forall_mem_cons.2 ⟨subd7_3_1407, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_1408 : subd7_3 [4, -2, 2] = true := by decide +kernel
theorem subd7_3_1409 : subd7_3 [4, -2, 3] = true := by decide +kernel
theorem subd7_3_1410 : subd7_3 [4, -2, 4] = true := by decide +kernel
theorem subd7_3_1411 : subd7_3 [4, -2, 5] = true := by decide +kernel
theorem subd7_3_1412 : subd7_3 [4, -2, 6] = true := by decide +kernel
theorem subd7_3_1413 : subd7_3 [4, -2, 7] = true := by decide +kernel
theorem subd7_3_1414 : subd7_3 [4, -2, 8] = true := by decide +kernel
theorem subd7_3_1415 : subd7_3 [4, -1, -5] = true := by decide +kernel
theorem subd7_3_1416 : subd7_3 [4, -1, -4] = true := by decide +kernel
theorem subd7_3_1417 : subd7_3 [4, -1, -3] = true := by decide +kernel
theorem subd7_3_1418 : subd7_3 [4, -1, -2] = true := by decide +kernel
theorem subd7_3_1419 : subd7_3 [4, -1, -1] = true := by decide +kernel
theorem subd7_3_1420 : subd7_3 [4, -1, 0] = true := by decide +kernel
theorem subd7_3_1421 : subd7_3 [4, -1, 1] = true := by decide +kernel
theorem subd7_3_1422 : subd7_3 [4, -1, 2] = true := by decide +kernel
theorem subd7_3_1423 : subd7_3 [4, -1, 3] = true := by decide +kernel
theorem subd7_3_1424 : subd7_3 [4, -1, 4] = true := by decide +kernel
theorem subd7_3_1425 : subd7_3 [4, -1, 5] = true := by decide +kernel
theorem subd7_3_1426 : subd7_3 [4, -1, 6] = true := by decide +kernel
theorem subd7_3_1427 : subd7_3 [4, -1, 7] = true := by decide +kernel
theorem subd7_3_1428 : subd7_3 [4, -1, 8] = true := by decide +kernel
theorem subd7_3_1429 : subd7_3 [4, 0, -5] = true := by decide +kernel
theorem subd7_3_1430 : subd7_3 [4, 0, -4] = true := by decide +kernel
theorem subd7_3_1431 : subd7_3 [4, 0, -3] = true := by decide +kernel
theorem subd7_3_1432 : subd7_3 [4, 0, -2] = true := by decide +kernel
theorem subd7_3_1433 : subd7_3 [4, 0, -1] = true := by decide +kernel
theorem subd7_3_1434 : subd7_3 [4, 0, 0] = true := by decide +kernel
theorem subd7_3_1435 : subd7_3 [4, 0, 1] = true := by decide +kernel
theorem subd7_3_1436 : subd7_3 [4, 0, 2] = true := by decide +kernel
theorem subd7_3_1437 : subd7_3 [4, 0, 3] = true := by decide +kernel
theorem subd7_3_1438 : subd7_3 [4, 0, 4] = true := by decide +kernel
theorem subd7_3_1439 : subd7_3 [4, 0, 5] = true := by decide +kernel
theorem sbd7_3_44 : ∀ q ∈ blkd7_3_44, subd7_3 q = true := by
  unfold blkd7_3_44
  exact List.forall_mem_cons.2 ⟨subd7_3_1408, List.forall_mem_cons.2 ⟨subd7_3_1409, List.forall_mem_cons.2 ⟨subd7_3_1410, List.forall_mem_cons.2 ⟨subd7_3_1411, List.forall_mem_cons.2 ⟨subd7_3_1412, List.forall_mem_cons.2 ⟨subd7_3_1413, List.forall_mem_cons.2 ⟨subd7_3_1414, List.forall_mem_cons.2 ⟨subd7_3_1415, List.forall_mem_cons.2 ⟨subd7_3_1416, List.forall_mem_cons.2 ⟨subd7_3_1417, List.forall_mem_cons.2 ⟨subd7_3_1418, List.forall_mem_cons.2 ⟨subd7_3_1419, List.forall_mem_cons.2 ⟨subd7_3_1420, List.forall_mem_cons.2 ⟨subd7_3_1421, List.forall_mem_cons.2 ⟨subd7_3_1422, List.forall_mem_cons.2 ⟨subd7_3_1423, List.forall_mem_cons.2 ⟨subd7_3_1424, List.forall_mem_cons.2 ⟨subd7_3_1425, List.forall_mem_cons.2 ⟨subd7_3_1426, List.forall_mem_cons.2 ⟨subd7_3_1427, List.forall_mem_cons.2 ⟨subd7_3_1428, List.forall_mem_cons.2 ⟨subd7_3_1429, List.forall_mem_cons.2 ⟨subd7_3_1430, List.forall_mem_cons.2 ⟨subd7_3_1431, List.forall_mem_cons.2 ⟨subd7_3_1432, List.forall_mem_cons.2 ⟨subd7_3_1433, List.forall_mem_cons.2 ⟨subd7_3_1434, List.forall_mem_cons.2 ⟨subd7_3_1435, List.forall_mem_cons.2 ⟨subd7_3_1436, List.forall_mem_cons.2 ⟨subd7_3_1437, List.forall_mem_cons.2 ⟨subd7_3_1438, List.forall_mem_cons.2 ⟨subd7_3_1439, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_1440 : subd7_3 [4, 0, 6] = true := by decide +kernel
theorem subd7_3_1441 : subd7_3 [4, 0, 7] = true := by decide +kernel
theorem subd7_3_1442 : subd7_3 [4, 0, 8] = true := by decide +kernel
theorem subd7_3_1443 : subd7_3 [4, 1, -5] = true := by decide +kernel
theorem subd7_3_1444 : subd7_3 [4, 1, -4] = true := by decide +kernel
theorem subd7_3_1445 : subd7_3 [4, 1, -3] = true := by decide +kernel
theorem subd7_3_1446 : subd7_3 [4, 1, -2] = true := by decide +kernel
theorem subd7_3_1447 : subd7_3 [4, 1, -1] = true := by decide +kernel
theorem subd7_3_1448 : subd7_3 [4, 1, 0] = true := by decide +kernel
theorem subd7_3_1449 : subd7_3 [4, 1, 1] = true := by decide +kernel
theorem subd7_3_1450 : subd7_3 [4, 1, 2] = true := by decide +kernel
theorem subd7_3_1451 : subd7_3 [4, 1, 3] = true := by decide +kernel
theorem subd7_3_1452 : subd7_3 [4, 1, 4] = true := by decide +kernel
theorem subd7_3_1453 : subd7_3 [4, 1, 5] = true := by decide +kernel
theorem subd7_3_1454 : subd7_3 [4, 1, 6] = true := by decide +kernel
theorem subd7_3_1455 : subd7_3 [4, 1, 7] = true := by decide +kernel
theorem subd7_3_1456 : subd7_3 [4, 1, 8] = true := by decide +kernel
theorem subd7_3_1457 : subd7_3 [4, 2, -5] = true := by decide +kernel
theorem subd7_3_1458 : subd7_3 [4, 2, -4] = true := by decide +kernel
theorem subd7_3_1459 : subd7_3 [4, 2, -3] = true := by decide +kernel
theorem subd7_3_1460 : subd7_3 [4, 2, -2] = true := by decide +kernel
theorem subd7_3_1461 : subd7_3 [4, 2, -1] = true := by decide +kernel
theorem subd7_3_1462 : subd7_3 [4, 2, 0] = true := by decide +kernel
theorem subd7_3_1463 : subd7_3 [4, 2, 1] = true := by decide +kernel
theorem subd7_3_1464 : subd7_3 [4, 2, 2] = true := by decide +kernel
theorem subd7_3_1465 : subd7_3 [4, 2, 3] = true := by decide +kernel
theorem subd7_3_1466 : subd7_3 [4, 2, 4] = true := by decide +kernel
theorem subd7_3_1467 : subd7_3 [4, 2, 5] = true := by decide +kernel
theorem subd7_3_1468 : subd7_3 [4, 2, 6] = true := by decide +kernel
theorem subd7_3_1469 : subd7_3 [4, 2, 7] = true := by decide +kernel
theorem subd7_3_1470 : subd7_3 [4, 2, 8] = true := by decide +kernel
theorem subd7_3_1471 : subd7_3 [4, 3, -5] = true := by decide +kernel
theorem sbd7_3_45 : ∀ q ∈ blkd7_3_45, subd7_3 q = true := by
  unfold blkd7_3_45
  exact List.forall_mem_cons.2 ⟨subd7_3_1440, List.forall_mem_cons.2 ⟨subd7_3_1441, List.forall_mem_cons.2 ⟨subd7_3_1442, List.forall_mem_cons.2 ⟨subd7_3_1443, List.forall_mem_cons.2 ⟨subd7_3_1444, List.forall_mem_cons.2 ⟨subd7_3_1445, List.forall_mem_cons.2 ⟨subd7_3_1446, List.forall_mem_cons.2 ⟨subd7_3_1447, List.forall_mem_cons.2 ⟨subd7_3_1448, List.forall_mem_cons.2 ⟨subd7_3_1449, List.forall_mem_cons.2 ⟨subd7_3_1450, List.forall_mem_cons.2 ⟨subd7_3_1451, List.forall_mem_cons.2 ⟨subd7_3_1452, List.forall_mem_cons.2 ⟨subd7_3_1453, List.forall_mem_cons.2 ⟨subd7_3_1454, List.forall_mem_cons.2 ⟨subd7_3_1455, List.forall_mem_cons.2 ⟨subd7_3_1456, List.forall_mem_cons.2 ⟨subd7_3_1457, List.forall_mem_cons.2 ⟨subd7_3_1458, List.forall_mem_cons.2 ⟨subd7_3_1459, List.forall_mem_cons.2 ⟨subd7_3_1460, List.forall_mem_cons.2 ⟨subd7_3_1461, List.forall_mem_cons.2 ⟨subd7_3_1462, List.forall_mem_cons.2 ⟨subd7_3_1463, List.forall_mem_cons.2 ⟨subd7_3_1464, List.forall_mem_cons.2 ⟨subd7_3_1465, List.forall_mem_cons.2 ⟨subd7_3_1466, List.forall_mem_cons.2 ⟨subd7_3_1467, List.forall_mem_cons.2 ⟨subd7_3_1468, List.forall_mem_cons.2 ⟨subd7_3_1469, List.forall_mem_cons.2 ⟨subd7_3_1470, List.forall_mem_cons.2 ⟨subd7_3_1471, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_1472 : subd7_3 [4, 3, -4] = true := by decide +kernel
theorem subd7_3_1473 : subd7_3 [4, 3, -3] = true := by decide +kernel
theorem subd7_3_1474 : subd7_3 [4, 3, -2] = true := by decide +kernel
theorem subd7_3_1475 : subd7_3 [4, 3, -1] = true := by decide +kernel
theorem subd7_3_1476 : subd7_3 [4, 3, 0] = true := by decide +kernel
theorem subd7_3_1477 : subd7_3 [4, 3, 1] = true := by decide +kernel
theorem subd7_3_1478 : subd7_3 [4, 3, 2] = true := by decide +kernel
theorem subd7_3_1479 : subd7_3 [4, 3, 3] = true := by decide +kernel
theorem subd7_3_1480 : subd7_3 [4, 3, 4] = true := by decide +kernel
theorem subd7_3_1481 : subd7_3 [4, 3, 5] = true := by decide +kernel
theorem subd7_3_1482 : subd7_3 [4, 3, 6] = true := by decide +kernel
theorem subd7_3_1483 : subd7_3 [4, 3, 7] = true := by decide +kernel
theorem subd7_3_1484 : subd7_3 [4, 4] = true := by decide +kernel
theorem subd7_3_1485 : subd7_3 [4, 5] = true := by decide +kernel
theorem subd7_3_1486 : subd7_3 [4, 6] = true := by decide +kernel
theorem subd7_3_1487 : subd7_3 [4, 7] = true := by decide +kernel
theorem subd7_3_1488 : subd7_3 [5, -7] = true := by decide +kernel
theorem subd7_3_1489 : subd7_3 [5, -6] = true := by decide +kernel
theorem subd7_3_1490 : subd7_3 [5, -5] = true := by decide +kernel
theorem subd7_3_1491 : subd7_3 [5, -4] = true := by decide +kernel
theorem subd7_3_1492 : subd7_3 [5, -3] = true := by decide +kernel
theorem subd7_3_1493 : subd7_3 [5, -2] = true := by decide +kernel
theorem subd7_3_1494 : subd7_3 [5, -1] = true := by decide +kernel
theorem subd7_3_1495 : subd7_3 [5, 0, -4] = true := by decide +kernel
theorem subd7_3_1496 : subd7_3 [5, 0, -3] = true := by decide +kernel
theorem subd7_3_1497 : subd7_3 [5, 0, -2] = true := by decide +kernel
theorem subd7_3_1498 : subd7_3 [5, 0, -1] = true := by decide +kernel
theorem subd7_3_1499 : subd7_3 [5, 0, 0] = true := by decide +kernel
theorem subd7_3_1500 : subd7_3 [5, 0, 1] = true := by decide +kernel
theorem subd7_3_1501 : subd7_3 [5, 0, 2] = true := by decide +kernel
theorem subd7_3_1502 : subd7_3 [5, 0, 3] = true := by decide +kernel
theorem subd7_3_1503 : subd7_3 [5, 0, 4] = true := by decide +kernel
theorem sbd7_3_46 : ∀ q ∈ blkd7_3_46, subd7_3 q = true := by
  unfold blkd7_3_46
  exact List.forall_mem_cons.2 ⟨subd7_3_1472, List.forall_mem_cons.2 ⟨subd7_3_1473, List.forall_mem_cons.2 ⟨subd7_3_1474, List.forall_mem_cons.2 ⟨subd7_3_1475, List.forall_mem_cons.2 ⟨subd7_3_1476, List.forall_mem_cons.2 ⟨subd7_3_1477, List.forall_mem_cons.2 ⟨subd7_3_1478, List.forall_mem_cons.2 ⟨subd7_3_1479, List.forall_mem_cons.2 ⟨subd7_3_1480, List.forall_mem_cons.2 ⟨subd7_3_1481, List.forall_mem_cons.2 ⟨subd7_3_1482, List.forall_mem_cons.2 ⟨subd7_3_1483, List.forall_mem_cons.2 ⟨subd7_3_1484, List.forall_mem_cons.2 ⟨subd7_3_1485, List.forall_mem_cons.2 ⟨subd7_3_1486, List.forall_mem_cons.2 ⟨subd7_3_1487, List.forall_mem_cons.2 ⟨subd7_3_1488, List.forall_mem_cons.2 ⟨subd7_3_1489, List.forall_mem_cons.2 ⟨subd7_3_1490, List.forall_mem_cons.2 ⟨subd7_3_1491, List.forall_mem_cons.2 ⟨subd7_3_1492, List.forall_mem_cons.2 ⟨subd7_3_1493, List.forall_mem_cons.2 ⟨subd7_3_1494, List.forall_mem_cons.2 ⟨subd7_3_1495, List.forall_mem_cons.2 ⟨subd7_3_1496, List.forall_mem_cons.2 ⟨subd7_3_1497, List.forall_mem_cons.2 ⟨subd7_3_1498, List.forall_mem_cons.2 ⟨subd7_3_1499, List.forall_mem_cons.2 ⟨subd7_3_1500, List.forall_mem_cons.2 ⟨subd7_3_1501, List.forall_mem_cons.2 ⟨subd7_3_1502, List.forall_mem_cons.2 ⟨subd7_3_1503, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_1504 : subd7_3 [5, 0, 5] = true := by decide +kernel
theorem subd7_3_1505 : subd7_3 [5, 0, 6] = true := by decide +kernel
theorem subd7_3_1506 : subd7_3 [5, 0, 7] = true := by decide +kernel
theorem subd7_3_1507 : subd7_3 [5, 0, 8] = true := by decide +kernel
theorem subd7_3_1508 : subd7_3 [5, 1] = true := by decide +kernel
theorem subd7_3_1509 : subd7_3 [5, 2] = true := by decide +kernel
theorem subd7_3_1510 : subd7_3 [5, 3] = true := by decide +kernel
theorem subd7_3_1511 : subd7_3 [5, 4] = true := by decide +kernel
theorem subd7_3_1512 : subd7_3 [5, 5] = true := by decide +kernel
theorem subd7_3_1513 : subd7_3 [5, 6] = true := by decide +kernel
theorem subd7_3_1514 : subd7_3 [6, -6] = true := by decide +kernel
theorem subd7_3_1515 : subd7_3 [6, -5] = true := by decide +kernel
theorem subd7_3_1516 : subd7_3 [6, -4] = true := by decide +kernel
theorem subd7_3_1517 : subd7_3 [6, -3] = true := by decide +kernel
theorem subd7_3_1518 : subd7_3 [6, -2] = true := by decide +kernel
theorem subd7_3_1519 : subd7_3 [6, -1] = true := by decide +kernel
theorem subd7_3_1520 : subd7_3 [6, 0] = true := by decide +kernel
theorem subd7_3_1521 : subd7_3 [6, 1] = true := by decide +kernel
theorem subd7_3_1522 : subd7_3 [6, 2] = true := by decide +kernel
theorem subd7_3_1523 : subd7_3 [6, 3] = true := by decide +kernel
theorem subd7_3_1524 : subd7_3 [6, 4] = true := by decide +kernel
theorem subd7_3_1525 : subd7_3 [6, 5] = true := by decide +kernel
theorem subd7_3_1526 : subd7_3 [7] = true := by decide +kernel
theorem sbd7_3_47 : ∀ q ∈ blkd7_3_47, subd7_3 q = true := by
  unfold blkd7_3_47
  exact List.forall_mem_cons.2 ⟨subd7_3_1504, List.forall_mem_cons.2 ⟨subd7_3_1505, List.forall_mem_cons.2 ⟨subd7_3_1506, List.forall_mem_cons.2 ⟨subd7_3_1507, List.forall_mem_cons.2 ⟨subd7_3_1508, List.forall_mem_cons.2 ⟨subd7_3_1509, List.forall_mem_cons.2 ⟨subd7_3_1510, List.forall_mem_cons.2 ⟨subd7_3_1511, List.forall_mem_cons.2 ⟨subd7_3_1512, List.forall_mem_cons.2 ⟨subd7_3_1513, List.forall_mem_cons.2 ⟨subd7_3_1514, List.forall_mem_cons.2 ⟨subd7_3_1515, List.forall_mem_cons.2 ⟨subd7_3_1516, List.forall_mem_cons.2 ⟨subd7_3_1517, List.forall_mem_cons.2 ⟨subd7_3_1518, List.forall_mem_cons.2 ⟨subd7_3_1519, List.forall_mem_cons.2 ⟨subd7_3_1520, List.forall_mem_cons.2 ⟨subd7_3_1521, List.forall_mem_cons.2 ⟨subd7_3_1522, List.forall_mem_cons.2 ⟨subd7_3_1523, List.forall_mem_cons.2 ⟨subd7_3_1524, List.forall_mem_cons.2 ⟨subd7_3_1525, List.forall_mem_cons.2 ⟨subd7_3_1526, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C096
