import ReflectZphi.Data.Cert5.C093.Base

namespace ReflectZphi.Data.Cert5.C093

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_0_1280 : subd7_0 [3, 2, 0] = true := by decide +kernel
theorem subd7_0_1281 : subd7_0 [3, 2, 1] = true := by decide +kernel
theorem subd7_0_1282 : subd7_0 [3, 2, 2] = true := by decide +kernel
theorem subd7_0_1283 : subd7_0 [3, 2, 3] = true := by decide +kernel
theorem subd7_0_1284 : subd7_0 [3, 2, 4] = true := by decide +kernel
theorem subd7_0_1285 : subd7_0 [3, 2, 5] = true := by decide +kernel
theorem subd7_0_1286 : subd7_0 [3, 2, 6] = true := by decide +kernel
theorem subd7_0_1287 : subd7_0 [3, 3, -9] = true := by decide +kernel
theorem subd7_0_1288 : subd7_0 [3, 3, -8] = true := by decide +kernel
theorem subd7_0_1289 : subd7_0 [3, 3, -7] = true := by decide +kernel
theorem subd7_0_1290 : subd7_0 [3, 3, -6] = true := by decide +kernel
theorem subd7_0_1291 : subd7_0 [3, 3, -5] = true := by decide +kernel
theorem subd7_0_1292 : subd7_0 [3, 3, -4] = true := by decide +kernel
theorem subd7_0_1293 : subd7_0 [3, 3, -3] = true := by decide +kernel
theorem subd7_0_1294 : subd7_0 [3, 3, -2] = true := by decide +kernel
theorem subd7_0_1295 : subd7_0 [3, 3, -1] = true := by decide +kernel
theorem subd7_0_1296 : subd7_0 [3, 3, 0] = true := by decide +kernel
theorem subd7_0_1297 : subd7_0 [3, 3, 1] = true := by decide +kernel
theorem subd7_0_1298 : subd7_0 [3, 3, 2] = true := by decide +kernel
theorem subd7_0_1299 : subd7_0 [3, 3, 3] = true := by decide +kernel
theorem subd7_0_1300 : subd7_0 [3, 3, 4] = true := by decide +kernel
theorem subd7_0_1301 : subd7_0 [3, 3, 5] = true := by decide +kernel
theorem subd7_0_1302 : subd7_0 [3, 4] = true := by decide +kernel
theorem subd7_0_1303 : subd7_0 [3, 5] = true := by decide +kernel
theorem subd7_0_1304 : subd7_0 [3, 6] = true := by decide +kernel
theorem subd7_0_1305 : subd7_0 [4, -8] = true := by decide +kernel
theorem subd7_0_1306 : subd7_0 [4, -7] = true := by decide +kernel
theorem subd7_0_1307 : subd7_0 [4, -6] = true := by decide +kernel
theorem subd7_0_1308 : subd7_0 [4, -5] = true := by decide +kernel
theorem subd7_0_1309 : subd7_0 [4, -4] = true := by decide +kernel
theorem subd7_0_1310 : subd7_0 [4, -3, -6] = true := by decide +kernel
theorem subd7_0_1311 : subd7_0 [4, -3, -5] = true := by decide +kernel
theorem sbd7_0_40 : ∀ q ∈ blkd7_0_40, subd7_0 q = true := by
  unfold blkd7_0_40
  exact List.forall_mem_cons.2 ⟨subd7_0_1280, List.forall_mem_cons.2 ⟨subd7_0_1281, List.forall_mem_cons.2 ⟨subd7_0_1282, List.forall_mem_cons.2 ⟨subd7_0_1283, List.forall_mem_cons.2 ⟨subd7_0_1284, List.forall_mem_cons.2 ⟨subd7_0_1285, List.forall_mem_cons.2 ⟨subd7_0_1286, List.forall_mem_cons.2 ⟨subd7_0_1287, List.forall_mem_cons.2 ⟨subd7_0_1288, List.forall_mem_cons.2 ⟨subd7_0_1289, List.forall_mem_cons.2 ⟨subd7_0_1290, List.forall_mem_cons.2 ⟨subd7_0_1291, List.forall_mem_cons.2 ⟨subd7_0_1292, List.forall_mem_cons.2 ⟨subd7_0_1293, List.forall_mem_cons.2 ⟨subd7_0_1294, List.forall_mem_cons.2 ⟨subd7_0_1295, List.forall_mem_cons.2 ⟨subd7_0_1296, List.forall_mem_cons.2 ⟨subd7_0_1297, List.forall_mem_cons.2 ⟨subd7_0_1298, List.forall_mem_cons.2 ⟨subd7_0_1299, List.forall_mem_cons.2 ⟨subd7_0_1300, List.forall_mem_cons.2 ⟨subd7_0_1301, List.forall_mem_cons.2 ⟨subd7_0_1302, List.forall_mem_cons.2 ⟨subd7_0_1303, List.forall_mem_cons.2 ⟨subd7_0_1304, List.forall_mem_cons.2 ⟨subd7_0_1305, List.forall_mem_cons.2 ⟨subd7_0_1306, List.forall_mem_cons.2 ⟨subd7_0_1307, List.forall_mem_cons.2 ⟨subd7_0_1308, List.forall_mem_cons.2 ⟨subd7_0_1309, List.forall_mem_cons.2 ⟨subd7_0_1310, List.forall_mem_cons.2 ⟨subd7_0_1311, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_1312 : subd7_0 [4, -3, -4] = true := by decide +kernel
theorem subd7_0_1313 : subd7_0 [4, -3, -3] = true := by decide +kernel
theorem subd7_0_1314 : subd7_0 [4, -3, -2] = true := by decide +kernel
theorem subd7_0_1315 : subd7_0 [4, -3, -1] = true := by decide +kernel
theorem subd7_0_1316 : subd7_0 [4, -3, 0] = true := by decide +kernel
theorem subd7_0_1317 : subd7_0 [4, -3, 1] = true := by decide +kernel
theorem subd7_0_1318 : subd7_0 [4, -3, 2] = true := by decide +kernel
theorem subd7_0_1319 : subd7_0 [4, -3, 3] = true := by decide +kernel
theorem subd7_0_1320 : subd7_0 [4, -3, 4] = true := by decide +kernel
theorem subd7_0_1321 : subd7_0 [4, -3, 5] = true := by decide +kernel
theorem subd7_0_1322 : subd7_0 [4, -3, 6] = true := by decide +kernel
theorem subd7_0_1323 : subd7_0 [4, -3, 7] = true := by decide +kernel
theorem subd7_0_1324 : subd7_0 [4, -3, 8] = true := by decide +kernel
theorem subd7_0_1325 : subd7_0 [4, -2, -7] = true := by decide +kernel
theorem subd7_0_1326 : subd7_0 [4, -2, -6] = true := by decide +kernel
theorem subd7_0_1327 : subd7_0 [4, -2, -5] = true := by decide +kernel
theorem subd7_0_1328 : subd7_0 [4, -2, -4] = true := by decide +kernel
theorem subd7_0_1329 : subd7_0 [4, -2, -3] = true := by decide +kernel
theorem subd7_0_1330 : subd7_0 [4, -2, -2] = true := by decide +kernel
theorem subd7_0_1331 : subd7_0 [4, -2, -1] = true := by decide +kernel
theorem subd7_0_1332 : subd7_0 [4, -2, 0] = true := by decide +kernel
theorem subd7_0_1333 : subd7_0 [4, -2, 1] = true := by decide +kernel
theorem subd7_0_1334 : subd7_0 [4, -2, 2] = true := by decide +kernel
theorem subd7_0_1335 : subd7_0 [4, -2, 3] = true := by decide +kernel
theorem subd7_0_1336 : subd7_0 [4, -2, 4] = true := by decide +kernel
theorem subd7_0_1337 : subd7_0 [4, -2, 5] = true := by decide +kernel
theorem subd7_0_1338 : subd7_0 [4, -2, 6] = true := by decide +kernel
theorem subd7_0_1339 : subd7_0 [4, -2, 7] = true := by decide +kernel
theorem subd7_0_1340 : subd7_0 [4, -2, 8] = true := by decide +kernel
theorem subd7_0_1341 : subd7_0 [4, -1, -7] = true := by decide +kernel
theorem subd7_0_1342 : subd7_0 [4, -1, -6] = true := by decide +kernel
theorem subd7_0_1343 : subd7_0 [4, -1, -5] = true := by decide +kernel
theorem sbd7_0_41 : ∀ q ∈ blkd7_0_41, subd7_0 q = true := by
  unfold blkd7_0_41
  exact List.forall_mem_cons.2 ⟨subd7_0_1312, List.forall_mem_cons.2 ⟨subd7_0_1313, List.forall_mem_cons.2 ⟨subd7_0_1314, List.forall_mem_cons.2 ⟨subd7_0_1315, List.forall_mem_cons.2 ⟨subd7_0_1316, List.forall_mem_cons.2 ⟨subd7_0_1317, List.forall_mem_cons.2 ⟨subd7_0_1318, List.forall_mem_cons.2 ⟨subd7_0_1319, List.forall_mem_cons.2 ⟨subd7_0_1320, List.forall_mem_cons.2 ⟨subd7_0_1321, List.forall_mem_cons.2 ⟨subd7_0_1322, List.forall_mem_cons.2 ⟨subd7_0_1323, List.forall_mem_cons.2 ⟨subd7_0_1324, List.forall_mem_cons.2 ⟨subd7_0_1325, List.forall_mem_cons.2 ⟨subd7_0_1326, List.forall_mem_cons.2 ⟨subd7_0_1327, List.forall_mem_cons.2 ⟨subd7_0_1328, List.forall_mem_cons.2 ⟨subd7_0_1329, List.forall_mem_cons.2 ⟨subd7_0_1330, List.forall_mem_cons.2 ⟨subd7_0_1331, List.forall_mem_cons.2 ⟨subd7_0_1332, List.forall_mem_cons.2 ⟨subd7_0_1333, List.forall_mem_cons.2 ⟨subd7_0_1334, List.forall_mem_cons.2 ⟨subd7_0_1335, List.forall_mem_cons.2 ⟨subd7_0_1336, List.forall_mem_cons.2 ⟨subd7_0_1337, List.forall_mem_cons.2 ⟨subd7_0_1338, List.forall_mem_cons.2 ⟨subd7_0_1339, List.forall_mem_cons.2 ⟨subd7_0_1340, List.forall_mem_cons.2 ⟨subd7_0_1341, List.forall_mem_cons.2 ⟨subd7_0_1342, List.forall_mem_cons.2 ⟨subd7_0_1343, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_1344 : subd7_0 [4, -1, -4] = true := by decide +kernel
theorem subd7_0_1345 : subd7_0 [4, -1, -3] = true := by decide +kernel
theorem subd7_0_1346 : subd7_0 [4, -1, -2] = true := by decide +kernel
theorem subd7_0_1347 : subd7_0 [4, -1, -1] = true := by decide +kernel
theorem subd7_0_1348 : subd7_0 [4, -1, 0] = true := by decide +kernel
theorem subd7_0_1349 : subd7_0 [4, -1, 1] = true := by decide +kernel
theorem subd7_0_1350 : subd7_0 [4, -1, 2] = true := by decide +kernel
theorem subd7_0_1351 : subd7_0 [4, -1, 3] = true := by decide +kernel
theorem subd7_0_1352 : subd7_0 [4, -1, 4] = true := by decide +kernel
theorem subd7_0_1353 : subd7_0 [4, -1, 5] = true := by decide +kernel
theorem subd7_0_1354 : subd7_0 [4, -1, 6] = true := by decide +kernel
theorem subd7_0_1355 : subd7_0 [4, -1, 7] = true := by decide +kernel
theorem subd7_0_1356 : subd7_0 [4, 0, -8] = true := by decide +kernel
theorem subd7_0_1357 : subd7_0 [4, 0, -7] = true := by decide +kernel
theorem subd7_0_1358 : subd7_0 [4, 0, -6] = true := by decide +kernel
theorem subd7_0_1359 : subd7_0 [4, 0, -5] = true := by decide +kernel
theorem subd7_0_1360 : subd7_0 [4, 0, -4] = true := by decide +kernel
theorem subd7_0_1361 : subd7_0 [4, 0, -3] = true := by decide +kernel
theorem subd7_0_1362 : subd7_0 [4, 0, -2] = true := by decide +kernel
theorem subd7_0_1363 : subd7_0 [4, 0, -1] = true := by decide +kernel
theorem subd7_0_1364 : subd7_0 [4, 0, 0] = true := by decide +kernel
theorem subd7_0_1365 : subd7_0 [4, 0, 1] = true := by decide +kernel
theorem subd7_0_1366 : subd7_0 [4, 0, 2] = true := by decide +kernel
theorem subd7_0_1367 : subd7_0 [4, 0, 3] = true := by decide +kernel
theorem subd7_0_1368 : subd7_0 [4, 0, 4] = true := by decide +kernel
theorem subd7_0_1369 : subd7_0 [4, 0, 5] = true := by decide +kernel
theorem subd7_0_1370 : subd7_0 [4, 0, 6] = true := by decide +kernel
theorem subd7_0_1371 : subd7_0 [4, 0, 7] = true := by decide +kernel
theorem subd7_0_1372 : subd7_0 [4, 1, -8] = true := by decide +kernel
theorem subd7_0_1373 : subd7_0 [4, 1, -7] = true := by decide +kernel
theorem subd7_0_1374 : subd7_0 [4, 1, -6] = true := by decide +kernel
theorem subd7_0_1375 : subd7_0 [4, 1, -5] = true := by decide +kernel
theorem sbd7_0_42 : ∀ q ∈ blkd7_0_42, subd7_0 q = true := by
  unfold blkd7_0_42
  exact List.forall_mem_cons.2 ⟨subd7_0_1344, List.forall_mem_cons.2 ⟨subd7_0_1345, List.forall_mem_cons.2 ⟨subd7_0_1346, List.forall_mem_cons.2 ⟨subd7_0_1347, List.forall_mem_cons.2 ⟨subd7_0_1348, List.forall_mem_cons.2 ⟨subd7_0_1349, List.forall_mem_cons.2 ⟨subd7_0_1350, List.forall_mem_cons.2 ⟨subd7_0_1351, List.forall_mem_cons.2 ⟨subd7_0_1352, List.forall_mem_cons.2 ⟨subd7_0_1353, List.forall_mem_cons.2 ⟨subd7_0_1354, List.forall_mem_cons.2 ⟨subd7_0_1355, List.forall_mem_cons.2 ⟨subd7_0_1356, List.forall_mem_cons.2 ⟨subd7_0_1357, List.forall_mem_cons.2 ⟨subd7_0_1358, List.forall_mem_cons.2 ⟨subd7_0_1359, List.forall_mem_cons.2 ⟨subd7_0_1360, List.forall_mem_cons.2 ⟨subd7_0_1361, List.forall_mem_cons.2 ⟨subd7_0_1362, List.forall_mem_cons.2 ⟨subd7_0_1363, List.forall_mem_cons.2 ⟨subd7_0_1364, List.forall_mem_cons.2 ⟨subd7_0_1365, List.forall_mem_cons.2 ⟨subd7_0_1366, List.forall_mem_cons.2 ⟨subd7_0_1367, List.forall_mem_cons.2 ⟨subd7_0_1368, List.forall_mem_cons.2 ⟨subd7_0_1369, List.forall_mem_cons.2 ⟨subd7_0_1370, List.forall_mem_cons.2 ⟨subd7_0_1371, List.forall_mem_cons.2 ⟨subd7_0_1372, List.forall_mem_cons.2 ⟨subd7_0_1373, List.forall_mem_cons.2 ⟨subd7_0_1374, List.forall_mem_cons.2 ⟨subd7_0_1375, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_1376 : subd7_0 [4, 1, -4] = true := by decide +kernel
theorem subd7_0_1377 : subd7_0 [4, 1, -3] = true := by decide +kernel
theorem subd7_0_1378 : subd7_0 [4, 1, -2] = true := by decide +kernel
theorem subd7_0_1379 : subd7_0 [4, 1, -1] = true := by decide +kernel
theorem subd7_0_1380 : subd7_0 [4, 1, 0] = true := by decide +kernel
theorem subd7_0_1381 : subd7_0 [4, 1, 1] = true := by decide +kernel
theorem subd7_0_1382 : subd7_0 [4, 1, 2] = true := by decide +kernel
theorem subd7_0_1383 : subd7_0 [4, 1, 3] = true := by decide +kernel
theorem subd7_0_1384 : subd7_0 [4, 1, 4] = true := by decide +kernel
theorem subd7_0_1385 : subd7_0 [4, 1, 5] = true := by decide +kernel
theorem subd7_0_1386 : subd7_0 [4, 1, 6] = true := by decide +kernel
theorem subd7_0_1387 : subd7_0 [4, 2, -8] = true := by decide +kernel
theorem subd7_0_1388 : subd7_0 [4, 2, -7] = true := by decide +kernel
theorem subd7_0_1389 : subd7_0 [4, 2, -6] = true := by decide +kernel
theorem subd7_0_1390 : subd7_0 [4, 2, -5] = true := by decide +kernel
theorem subd7_0_1391 : subd7_0 [4, 2, -4] = true := by decide +kernel
theorem subd7_0_1392 : subd7_0 [4, 2, -3] = true := by decide +kernel
theorem subd7_0_1393 : subd7_0 [4, 2, -2] = true := by decide +kernel
theorem subd7_0_1394 : subd7_0 [4, 2, -1] = true := by decide +kernel
theorem subd7_0_1395 : subd7_0 [4, 2, 0] = true := by decide +kernel
theorem subd7_0_1396 : subd7_0 [4, 2, 1] = true := by decide +kernel
theorem subd7_0_1397 : subd7_0 [4, 2, 2] = true := by decide +kernel
theorem subd7_0_1398 : subd7_0 [4, 2, 3] = true := by decide +kernel
theorem subd7_0_1399 : subd7_0 [4, 2, 4] = true := by decide +kernel
theorem subd7_0_1400 : subd7_0 [4, 2, 5] = true := by decide +kernel
theorem subd7_0_1401 : subd7_0 [4, 3] = true := by decide +kernel
theorem subd7_0_1402 : subd7_0 [4, 4] = true := by decide +kernel
theorem subd7_0_1403 : subd7_0 [4, 5] = true := by decide +kernel
theorem subd7_0_1404 : subd7_0 [5, -7] = true := by decide +kernel
theorem subd7_0_1405 : subd7_0 [5, -6] = true := by decide +kernel
theorem subd7_0_1406 : subd7_0 [5, -5] = true := by decide +kernel
theorem subd7_0_1407 : subd7_0 [5, -4] = true := by decide +kernel
theorem sbd7_0_43 : ∀ q ∈ blkd7_0_43, subd7_0 q = true := by
  unfold blkd7_0_43
  exact List.forall_mem_cons.2 ⟨subd7_0_1376, List.forall_mem_cons.2 ⟨subd7_0_1377, List.forall_mem_cons.2 ⟨subd7_0_1378, List.forall_mem_cons.2 ⟨subd7_0_1379, List.forall_mem_cons.2 ⟨subd7_0_1380, List.forall_mem_cons.2 ⟨subd7_0_1381, List.forall_mem_cons.2 ⟨subd7_0_1382, List.forall_mem_cons.2 ⟨subd7_0_1383, List.forall_mem_cons.2 ⟨subd7_0_1384, List.forall_mem_cons.2 ⟨subd7_0_1385, List.forall_mem_cons.2 ⟨subd7_0_1386, List.forall_mem_cons.2 ⟨subd7_0_1387, List.forall_mem_cons.2 ⟨subd7_0_1388, List.forall_mem_cons.2 ⟨subd7_0_1389, List.forall_mem_cons.2 ⟨subd7_0_1390, List.forall_mem_cons.2 ⟨subd7_0_1391, List.forall_mem_cons.2 ⟨subd7_0_1392, List.forall_mem_cons.2 ⟨subd7_0_1393, List.forall_mem_cons.2 ⟨subd7_0_1394, List.forall_mem_cons.2 ⟨subd7_0_1395, List.forall_mem_cons.2 ⟨subd7_0_1396, List.forall_mem_cons.2 ⟨subd7_0_1397, List.forall_mem_cons.2 ⟨subd7_0_1398, List.forall_mem_cons.2 ⟨subd7_0_1399, List.forall_mem_cons.2 ⟨subd7_0_1400, List.forall_mem_cons.2 ⟨subd7_0_1401, List.forall_mem_cons.2 ⟨subd7_0_1402, List.forall_mem_cons.2 ⟨subd7_0_1403, List.forall_mem_cons.2 ⟨subd7_0_1404, List.forall_mem_cons.2 ⟨subd7_0_1405, List.forall_mem_cons.2 ⟨subd7_0_1406, List.forall_mem_cons.2 ⟨subd7_0_1407, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_1408 : subd7_0 [5, -3] = true := by decide +kernel
theorem subd7_0_1409 : subd7_0 [5, -2] = true := by decide +kernel
theorem subd7_0_1410 : subd7_0 [5, -1] = true := by decide +kernel
theorem subd7_0_1411 : subd7_0 [5, 0] = true := by decide +kernel
theorem subd7_0_1412 : subd7_0 [5, 1] = true := by decide +kernel
theorem subd7_0_1413 : subd7_0 [5, 2] = true := by decide +kernel
theorem subd7_0_1414 : subd7_0 [5, 3] = true := by decide +kernel
theorem subd7_0_1415 : subd7_0 [5, 4] = true := by decide +kernel
theorem subd7_0_1416 : subd7_0 [6, -6] = true := by decide +kernel
theorem subd7_0_1417 : subd7_0 [6, -5] = true := by decide +kernel
theorem subd7_0_1418 : subd7_0 [6, -4] = true := by decide +kernel
theorem subd7_0_1419 : subd7_0 [6, -3] = true := by decide +kernel
theorem subd7_0_1420 : subd7_0 [6, -2] = true := by decide +kernel
theorem subd7_0_1421 : subd7_0 [6, -1] = true := by decide +kernel
theorem subd7_0_1422 : subd7_0 [6, 0] = true := by decide +kernel
theorem subd7_0_1423 : subd7_0 [6, 1] = true := by decide +kernel
theorem subd7_0_1424 : subd7_0 [6, 2] = true := by decide +kernel
theorem subd7_0_1425 : subd7_0 [6, 3] = true := by decide +kernel
theorem subd7_0_1426 : subd7_0 [7] = true := by decide +kernel
theorem sbd7_0_44 : ∀ q ∈ blkd7_0_44, subd7_0 q = true := by
  unfold blkd7_0_44
  exact List.forall_mem_cons.2 ⟨subd7_0_1408, List.forall_mem_cons.2 ⟨subd7_0_1409, List.forall_mem_cons.2 ⟨subd7_0_1410, List.forall_mem_cons.2 ⟨subd7_0_1411, List.forall_mem_cons.2 ⟨subd7_0_1412, List.forall_mem_cons.2 ⟨subd7_0_1413, List.forall_mem_cons.2 ⟨subd7_0_1414, List.forall_mem_cons.2 ⟨subd7_0_1415, List.forall_mem_cons.2 ⟨subd7_0_1416, List.forall_mem_cons.2 ⟨subd7_0_1417, List.forall_mem_cons.2 ⟨subd7_0_1418, List.forall_mem_cons.2 ⟨subd7_0_1419, List.forall_mem_cons.2 ⟨subd7_0_1420, List.forall_mem_cons.2 ⟨subd7_0_1421, List.forall_mem_cons.2 ⟨subd7_0_1422, List.forall_mem_cons.2 ⟨subd7_0_1423, List.forall_mem_cons.2 ⟨subd7_0_1424, List.forall_mem_cons.2 ⟨subd7_0_1425, List.forall_mem_cons.2 ⟨subd7_0_1426, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_1 : ldCheck G d7_1.U d7_1.ms ldd7_1 = true := by decide +kernel
theorem pre_okd7_1 : subPre G cell7 d7_1 = true := by decide +kernel
theorem subd7_1_0 : subd7_1 [-2] = true := by decide +kernel
theorem subd7_1_1 : subd7_1 [-1] = true := by decide +kernel
theorem subd7_1_2 : subd7_1 [0] = true := by decide +kernel
theorem subd7_1_3 : subd7_1 [1] = true := by decide +kernel
theorem subd7_1_4 : subd7_1 [2] = true := by decide +kernel
theorem sbd7_1_0 : ∀ q ∈ blkd7_1_0, subd7_1 q = true := by
  unfold blkd7_1_0
  exact List.forall_mem_cons.2 ⟨subd7_1_0, List.forall_mem_cons.2 ⟨subd7_1_1, List.forall_mem_cons.2 ⟨subd7_1_2, List.forall_mem_cons.2 ⟨subd7_1_3, List.forall_mem_cons.2 ⟨subd7_1_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd7_2 : ldCheck G d7_2.U d7_2.ms ldd7_2 = true := by decide +kernel
theorem pre_okd7_2 : subPre G cell7 d7_2 = true := by decide +kernel
theorem subd7_2_0 : subd7_2 [] = true := by decide +kernel
theorem sbd7_2_0 : ∀ q ∈ blkd7_2_0, subd7_2 q = true := by
  unfold blkd7_2_0
  exact List.forall_mem_cons.2 ⟨subd7_2_0, List.forall_mem_nil _⟩
theorem ld_okd7_3 : ldCheck G d7_3.U d7_3.ms ldd7_3 = true := by decide +kernel
theorem pre_okd7_3 : subPre G cell7 d7_3 = true := by decide +kernel
theorem subd7_3_0 : subd7_3 [-1] = true := by decide +kernel
theorem subd7_3_1 : subd7_3 [0] = true := by decide +kernel
theorem subd7_3_2 : subd7_3 [1] = true := by decide +kernel
theorem sbd7_3_0 : ∀ q ∈ blkd7_3_0, subd7_3 q = true := by
  unfold blkd7_3_0
  exact List.forall_mem_cons.2 ⟨subd7_3_0, List.forall_mem_cons.2 ⟨subd7_3_1, List.forall_mem_cons.2 ⟨subd7_3_2, List.forall_mem_nil _⟩⟩⟩

end ReflectZphi.Data.Cert5.C093
