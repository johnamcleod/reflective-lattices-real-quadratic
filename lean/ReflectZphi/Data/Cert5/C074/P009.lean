import ReflectZphi.Data.Cert5.C074.Base

namespace ReflectZphi.Data.Cert5.C074
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub8_1280 : sub8 [2, 3, 1] = true := by decide +kernel
theorem sub8_1281 : sub8 [2, 3, 2] = true := by decide +kernel
theorem sub8_1282 : sub8 [2, 3, 3] = true := by decide +kernel
theorem sub8_1283 : sub8 [2, 3, 4] = true := by decide +kernel
theorem sub8_1284 : sub8 [2, 3, 5] = true := by decide +kernel
theorem sub8_1285 : sub8 [2, 3, 6] = true := by decide +kernel
theorem sub8_1286 : sub8 [2, 3, 7] = true := by decide +kernel
theorem sub8_1287 : sub8 [2, 3, 8] = true := by decide +kernel
theorem sub8_1288 : sub8 [2, 3, 9] = true := by decide +kernel
theorem sub8_1289 : sub8 [2, 4, -8] = true := by decide +kernel
theorem sub8_1290 : sub8 [2, 4, -7] = true := by decide +kernel
theorem sub8_1291 : sub8 [2, 4, -6] = true := by decide +kernel
theorem sub8_1292 : sub8 [2, 4, -5] = true := by decide +kernel
theorem sub8_1293 : sub8 [2, 4, -4] = true := by decide +kernel
theorem sub8_1294 : sub8 [2, 4, -3] = true := by decide +kernel
theorem sub8_1295 : sub8 [2, 4, -2] = true := by decide +kernel
theorem sub8_1296 : sub8 [2, 4, -1] = true := by decide +kernel
theorem sub8_1297 : sub8 [2, 4, 0] = true := by decide +kernel
theorem sub8_1298 : sub8 [2, 4, 1] = true := by decide +kernel
theorem sub8_1299 : sub8 [2, 4, 2] = true := by decide +kernel
theorem sub8_1300 : sub8 [2, 4, 3] = true := by decide +kernel
theorem sub8_1301 : sub8 [2, 4, 4] = true := by decide +kernel
theorem sub8_1302 : sub8 [2, 4, 5] = true := by decide +kernel
theorem sub8_1303 : sub8 [2, 4, 6] = true := by decide +kernel
theorem sub8_1304 : sub8 [2, 4, 7] = true := by decide +kernel
theorem sub8_1305 : sub8 [2, 4, 8] = true := by decide +kernel
theorem sub8_1306 : sub8 [2, 4, 9] = true := by decide +kernel
theorem sub8_1307 : sub8 [2, 5, -7] = true := by decide +kernel
theorem sub8_1308 : sub8 [2, 5, -6] = true := by decide +kernel
theorem sub8_1309 : sub8 [2, 5, -5] = true := by decide +kernel
theorem sub8_1310 : sub8 [2, 5, -4] = true := by decide +kernel
theorem sub8_1311 : sub8 [2, 5, -3] = true := by decide +kernel
theorem sb8_40 : ∀ q ∈ blk8_40, sub8 q = true := by
  unfold blk8_40
  exact List.forall_mem_cons.2 ⟨sub8_1280, List.forall_mem_cons.2 ⟨sub8_1281, List.forall_mem_cons.2 ⟨sub8_1282, List.forall_mem_cons.2 ⟨sub8_1283, List.forall_mem_cons.2 ⟨sub8_1284, List.forall_mem_cons.2 ⟨sub8_1285, List.forall_mem_cons.2 ⟨sub8_1286, List.forall_mem_cons.2 ⟨sub8_1287, List.forall_mem_cons.2 ⟨sub8_1288, List.forall_mem_cons.2 ⟨sub8_1289, List.forall_mem_cons.2 ⟨sub8_1290, List.forall_mem_cons.2 ⟨sub8_1291, List.forall_mem_cons.2 ⟨sub8_1292, List.forall_mem_cons.2 ⟨sub8_1293, List.forall_mem_cons.2 ⟨sub8_1294, List.forall_mem_cons.2 ⟨sub8_1295, List.forall_mem_cons.2 ⟨sub8_1296, List.forall_mem_cons.2 ⟨sub8_1297, List.forall_mem_cons.2 ⟨sub8_1298, List.forall_mem_cons.2 ⟨sub8_1299, List.forall_mem_cons.2 ⟨sub8_1300, List.forall_mem_cons.2 ⟨sub8_1301, List.forall_mem_cons.2 ⟨sub8_1302, List.forall_mem_cons.2 ⟨sub8_1303, List.forall_mem_cons.2 ⟨sub8_1304, List.forall_mem_cons.2 ⟨sub8_1305, List.forall_mem_cons.2 ⟨sub8_1306, List.forall_mem_cons.2 ⟨sub8_1307, List.forall_mem_cons.2 ⟨sub8_1308, List.forall_mem_cons.2 ⟨sub8_1309, List.forall_mem_cons.2 ⟨sub8_1310, List.forall_mem_cons.2 ⟨sub8_1311, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_1312 : sub8 [2, 5, -2] = true := by decide +kernel
theorem sub8_1313 : sub8 [2, 5, -1] = true := by decide +kernel
theorem sub8_1314 : sub8 [2, 5, 0] = true := by decide +kernel
theorem sub8_1315 : sub8 [2, 5, 1] = true := by decide +kernel
theorem sub8_1316 : sub8 [2, 5, 2] = true := by decide +kernel
theorem sub8_1317 : sub8 [2, 5, 3] = true := by decide +kernel
theorem sub8_1318 : sub8 [2, 5, 4] = true := by decide +kernel
theorem sub8_1319 : sub8 [2, 5, 5] = true := by decide +kernel
theorem sub8_1320 : sub8 [2, 5, 6] = true := by decide +kernel
theorem sub8_1321 : sub8 [2, 5, 7] = true := by decide +kernel
theorem sub8_1322 : sub8 [2, 5, 8] = true := by decide +kernel
theorem sub8_1323 : sub8 [2, 6] = true := by decide +kernel
theorem sub8_1324 : sub8 [2, 7] = true := by decide +kernel
theorem sub8_1325 : sub8 [2, 8] = true := by decide +kernel
theorem sub8_1326 : sub8 [3, -6] = true := by decide +kernel
theorem sub8_1327 : sub8 [3, -5] = true := by decide +kernel
theorem sub8_1328 : sub8 [3, -4] = true := by decide +kernel
theorem sub8_1329 : sub8 [3, -3, -7] = true := by decide +kernel
theorem sub8_1330 : sub8 [3, -3, -6] = true := by decide +kernel
theorem sub8_1331 : sub8 [3, -3, -5] = true := by decide +kernel
theorem sub8_1332 : sub8 [3, -3, -4] = true := by decide +kernel
theorem sub8_1333 : sub8 [3, -3, -3] = true := by decide +kernel
theorem sub8_1334 : sub8 [3, -3, -2] = true := by decide +kernel
theorem sub8_1335 : sub8 [3, -3, -1] = true := by decide +kernel
theorem sub8_1336 : sub8 [3, -3, 0] = true := by decide +kernel
theorem sub8_1337 : sub8 [3, -3, 1] = true := by decide +kernel
theorem sub8_1338 : sub8 [3, -3, 2] = true := by decide +kernel
theorem sub8_1339 : sub8 [3, -3, 3] = true := by decide +kernel
theorem sub8_1340 : sub8 [3, -3, 4] = true := by decide +kernel
theorem sub8_1341 : sub8 [3, -3, 5] = true := by decide +kernel
theorem sub8_1342 : sub8 [3, -3, 6] = true := by decide +kernel
theorem sub8_1343 : sub8 [3, -3, 7] = true := by decide +kernel
theorem sb8_41 : ∀ q ∈ blk8_41, sub8 q = true := by
  unfold blk8_41
  exact List.forall_mem_cons.2 ⟨sub8_1312, List.forall_mem_cons.2 ⟨sub8_1313, List.forall_mem_cons.2 ⟨sub8_1314, List.forall_mem_cons.2 ⟨sub8_1315, List.forall_mem_cons.2 ⟨sub8_1316, List.forall_mem_cons.2 ⟨sub8_1317, List.forall_mem_cons.2 ⟨sub8_1318, List.forall_mem_cons.2 ⟨sub8_1319, List.forall_mem_cons.2 ⟨sub8_1320, List.forall_mem_cons.2 ⟨sub8_1321, List.forall_mem_cons.2 ⟨sub8_1322, List.forall_mem_cons.2 ⟨sub8_1323, List.forall_mem_cons.2 ⟨sub8_1324, List.forall_mem_cons.2 ⟨sub8_1325, List.forall_mem_cons.2 ⟨sub8_1326, List.forall_mem_cons.2 ⟨sub8_1327, List.forall_mem_cons.2 ⟨sub8_1328, List.forall_mem_cons.2 ⟨sub8_1329, List.forall_mem_cons.2 ⟨sub8_1330, List.forall_mem_cons.2 ⟨sub8_1331, List.forall_mem_cons.2 ⟨sub8_1332, List.forall_mem_cons.2 ⟨sub8_1333, List.forall_mem_cons.2 ⟨sub8_1334, List.forall_mem_cons.2 ⟨sub8_1335, List.forall_mem_cons.2 ⟨sub8_1336, List.forall_mem_cons.2 ⟨sub8_1337, List.forall_mem_cons.2 ⟨sub8_1338, List.forall_mem_cons.2 ⟨sub8_1339, List.forall_mem_cons.2 ⟨sub8_1340, List.forall_mem_cons.2 ⟨sub8_1341, List.forall_mem_cons.2 ⟨sub8_1342, List.forall_mem_cons.2 ⟨sub8_1343, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_1344 : sub8 [3, -2, -8] = true := by decide +kernel
theorem sub8_1345 : sub8 [3, -2, -7] = true := by decide +kernel
theorem sub8_1346 : sub8 [3, -2, -6] = true := by decide +kernel
theorem sub8_1347 : sub8 [3, -2, -5] = true := by decide +kernel
theorem sub8_1348 : sub8 [3, -2, -4] = true := by decide +kernel
theorem sub8_1349 : sub8 [3, -2, -3] = true := by decide +kernel
theorem sub8_1350 : sub8 [3, -2, -2] = true := by decide +kernel
theorem sub8_1351 : sub8 [3, -2, -1] = true := by decide +kernel
theorem sub8_1352 : sub8 [3, -2, 0] = true := by decide +kernel
theorem sub8_1353 : sub8 [3, -2, 1] = true := by decide +kernel
theorem sub8_1354 : sub8 [3, -2, 2] = true := by decide +kernel
theorem sub8_1355 : sub8 [3, -2, 3] = true := by decide +kernel
theorem sub8_1356 : sub8 [3, -2, 4] = true := by decide +kernel
theorem sub8_1357 : sub8 [3, -2, 5] = true := by decide +kernel
theorem sub8_1358 : sub8 [3, -2, 6] = true := by decide +kernel
theorem sub8_1359 : sub8 [3, -2, 7] = true := by decide +kernel
theorem sub8_1360 : sub8 [3, -2, 8] = true := by decide +kernel
theorem sub8_1361 : sub8 [3, -1, -9] = true := by decide +kernel
theorem sub8_1362 : sub8 [3, -1, -8] = true := by decide +kernel
theorem sub8_1363 : sub8 [3, -1, -7] = true := by decide +kernel
theorem sub8_1364 : sub8 [3, -1, -6] = true := by decide +kernel
theorem sub8_1365 : sub8 [3, -1, -5] = true := by decide +kernel
theorem sub8_1366 : sub8 [3, -1, -4] = true := by decide +kernel
theorem sub8_1367 : sub8 [3, -1, -3] = true := by decide +kernel
theorem sub8_1368 : sub8 [3, -1, -2] = true := by decide +kernel
theorem sub8_1369 : sub8 [3, -1, -1] = true := by decide +kernel
theorem sub8_1370 : sub8 [3, -1, 0] = true := by decide +kernel
theorem sub8_1371 : sub8 [3, -1, 1] = true := by decide +kernel
theorem sub8_1372 : sub8 [3, -1, 2] = true := by decide +kernel
theorem sub8_1373 : sub8 [3, -1, 3] = true := by decide +kernel
theorem sub8_1374 : sub8 [3, -1, 4] = true := by decide +kernel
theorem sub8_1375 : sub8 [3, -1, 5] = true := by decide +kernel
theorem sb8_42 : ∀ q ∈ blk8_42, sub8 q = true := by
  unfold blk8_42
  exact List.forall_mem_cons.2 ⟨sub8_1344, List.forall_mem_cons.2 ⟨sub8_1345, List.forall_mem_cons.2 ⟨sub8_1346, List.forall_mem_cons.2 ⟨sub8_1347, List.forall_mem_cons.2 ⟨sub8_1348, List.forall_mem_cons.2 ⟨sub8_1349, List.forall_mem_cons.2 ⟨sub8_1350, List.forall_mem_cons.2 ⟨sub8_1351, List.forall_mem_cons.2 ⟨sub8_1352, List.forall_mem_cons.2 ⟨sub8_1353, List.forall_mem_cons.2 ⟨sub8_1354, List.forall_mem_cons.2 ⟨sub8_1355, List.forall_mem_cons.2 ⟨sub8_1356, List.forall_mem_cons.2 ⟨sub8_1357, List.forall_mem_cons.2 ⟨sub8_1358, List.forall_mem_cons.2 ⟨sub8_1359, List.forall_mem_cons.2 ⟨sub8_1360, List.forall_mem_cons.2 ⟨sub8_1361, List.forall_mem_cons.2 ⟨sub8_1362, List.forall_mem_cons.2 ⟨sub8_1363, List.forall_mem_cons.2 ⟨sub8_1364, List.forall_mem_cons.2 ⟨sub8_1365, List.forall_mem_cons.2 ⟨sub8_1366, List.forall_mem_cons.2 ⟨sub8_1367, List.forall_mem_cons.2 ⟨sub8_1368, List.forall_mem_cons.2 ⟨sub8_1369, List.forall_mem_cons.2 ⟨sub8_1370, List.forall_mem_cons.2 ⟨sub8_1371, List.forall_mem_cons.2 ⟨sub8_1372, List.forall_mem_cons.2 ⟨sub8_1373, List.forall_mem_cons.2 ⟨sub8_1374, List.forall_mem_cons.2 ⟨sub8_1375, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_1376 : sub8 [3, -1, 6] = true := by decide +kernel
theorem sub8_1377 : sub8 [3, -1, 7] = true := by decide +kernel
theorem sub8_1378 : sub8 [3, -1, 8] = true := by decide +kernel
theorem sub8_1379 : sub8 [3, 0, -9] = true := by decide +kernel
theorem sub8_1380 : sub8 [3, 0, -8] = true := by decide +kernel
theorem sub8_1381 : sub8 [3, 0, -7] = true := by decide +kernel
theorem sub8_1382 : sub8 [3, 0, -6] = true := by decide +kernel
theorem sub8_1383 : sub8 [3, 0, -5] = true := by decide +kernel
theorem sub8_1384 : sub8 [3, 0, -4] = true := by decide +kernel
theorem sub8_1385 : sub8 [3, 0, -3] = true := by decide +kernel
theorem sub8_1386 : sub8 [3, 0, -2] = true := by decide +kernel
theorem sub8_1387 : sub8 [3, 0, -1] = true := by decide +kernel
theorem sub8_1388 : sub8 [3, 0, 0] = true := by decide +kernel
theorem sub8_1389 : sub8 [3, 0, 1] = true := by decide +kernel
theorem sub8_1390 : sub8 [3, 0, 2] = true := by decide +kernel
theorem sub8_1391 : sub8 [3, 0, 3] = true := by decide +kernel
theorem sub8_1392 : sub8 [3, 0, 4] = true := by decide +kernel
theorem sub8_1393 : sub8 [3, 0, 5] = true := by decide +kernel
theorem sub8_1394 : sub8 [3, 0, 6] = true := by decide +kernel
theorem sub8_1395 : sub8 [3, 0, 7] = true := by decide +kernel
theorem sub8_1396 : sub8 [3, 0, 8] = true := by decide +kernel
theorem sub8_1397 : sub8 [3, 0, 9] = true := by decide +kernel
theorem sub8_1398 : sub8 [3, 1, -9] = true := by decide +kernel
theorem sub8_1399 : sub8 [3, 1, -8] = true := by decide +kernel
theorem sub8_1400 : sub8 [3, 1, -7] = true := by decide +kernel
theorem sub8_1401 : sub8 [3, 1, -6] = true := by decide +kernel
theorem sub8_1402 : sub8 [3, 1, -5] = true := by decide +kernel
theorem sub8_1403 : sub8 [3, 1, -4] = true := by decide +kernel
theorem sub8_1404 : sub8 [3, 1, -3] = true := by decide +kernel
theorem sub8_1405 : sub8 [3, 1, -2] = true := by decide +kernel
theorem sub8_1406 : sub8 [3, 1, -1] = true := by decide +kernel
theorem sub8_1407 : sub8 [3, 1, 0] = true := by decide +kernel
theorem sb8_43 : ∀ q ∈ blk8_43, sub8 q = true := by
  unfold blk8_43
  exact List.forall_mem_cons.2 ⟨sub8_1376, List.forall_mem_cons.2 ⟨sub8_1377, List.forall_mem_cons.2 ⟨sub8_1378, List.forall_mem_cons.2 ⟨sub8_1379, List.forall_mem_cons.2 ⟨sub8_1380, List.forall_mem_cons.2 ⟨sub8_1381, List.forall_mem_cons.2 ⟨sub8_1382, List.forall_mem_cons.2 ⟨sub8_1383, List.forall_mem_cons.2 ⟨sub8_1384, List.forall_mem_cons.2 ⟨sub8_1385, List.forall_mem_cons.2 ⟨sub8_1386, List.forall_mem_cons.2 ⟨sub8_1387, List.forall_mem_cons.2 ⟨sub8_1388, List.forall_mem_cons.2 ⟨sub8_1389, List.forall_mem_cons.2 ⟨sub8_1390, List.forall_mem_cons.2 ⟨sub8_1391, List.forall_mem_cons.2 ⟨sub8_1392, List.forall_mem_cons.2 ⟨sub8_1393, List.forall_mem_cons.2 ⟨sub8_1394, List.forall_mem_cons.2 ⟨sub8_1395, List.forall_mem_cons.2 ⟨sub8_1396, List.forall_mem_cons.2 ⟨sub8_1397, List.forall_mem_cons.2 ⟨sub8_1398, List.forall_mem_cons.2 ⟨sub8_1399, List.forall_mem_cons.2 ⟨sub8_1400, List.forall_mem_cons.2 ⟨sub8_1401, List.forall_mem_cons.2 ⟨sub8_1402, List.forall_mem_cons.2 ⟨sub8_1403, List.forall_mem_cons.2 ⟨sub8_1404, List.forall_mem_cons.2 ⟨sub8_1405, List.forall_mem_cons.2 ⟨sub8_1406, List.forall_mem_cons.2 ⟨sub8_1407, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_1408 : sub8 [3, 1, 1] = true := by decide +kernel
theorem sub8_1409 : sub8 [3, 1, 2] = true := by decide +kernel
theorem sub8_1410 : sub8 [3, 1, 3] = true := by decide +kernel
theorem sub8_1411 : sub8 [3, 1, 4] = true := by decide +kernel
theorem sub8_1412 : sub8 [3, 1, 5] = true := by decide +kernel
theorem sub8_1413 : sub8 [3, 1, 6] = true := by decide +kernel
theorem sub8_1414 : sub8 [3, 1, 7] = true := by decide +kernel
theorem sub8_1415 : sub8 [3, 1, 8] = true := by decide +kernel
theorem sub8_1416 : sub8 [3, 1, 9] = true := by decide +kernel
theorem sub8_1417 : sub8 [3, 2, -9] = true := by decide +kernel
theorem sub8_1418 : sub8 [3, 2, -8] = true := by decide +kernel
theorem sub8_1419 : sub8 [3, 2, -7] = true := by decide +kernel
theorem sub8_1420 : sub8 [3, 2, -6] = true := by decide +kernel
theorem sub8_1421 : sub8 [3, 2, -5] = true := by decide +kernel
theorem sub8_1422 : sub8 [3, 2, -4] = true := by decide +kernel
theorem sub8_1423 : sub8 [3, 2, -3] = true := by decide +kernel
theorem sub8_1424 : sub8 [3, 2, -2] = true := by decide +kernel
theorem sub8_1425 : sub8 [3, 2, -1] = true := by decide +kernel
theorem sub8_1426 : sub8 [3, 2, 0] = true := by decide +kernel
theorem sub8_1427 : sub8 [3, 2, 1] = true := by decide +kernel
theorem sub8_1428 : sub8 [3, 2, 2] = true := by decide +kernel
theorem sub8_1429 : sub8 [3, 2, 3] = true := by decide +kernel
theorem sub8_1430 : sub8 [3, 2, 4] = true := by decide +kernel
theorem sub8_1431 : sub8 [3, 2, 5] = true := by decide +kernel
theorem sub8_1432 : sub8 [3, 2, 6] = true := by decide +kernel
theorem sub8_1433 : sub8 [3, 2, 7] = true := by decide +kernel
theorem sub8_1434 : sub8 [3, 2, 8] = true := by decide +kernel
theorem sub8_1435 : sub8 [3, 2, 9] = true := by decide +kernel
theorem sub8_1436 : sub8 [3, 3, -8] = true := by decide +kernel
theorem sub8_1437 : sub8 [3, 3, -7] = true := by decide +kernel
theorem sub8_1438 : sub8 [3, 3, -6] = true := by decide +kernel
theorem sub8_1439 : sub8 [3, 3, -5] = true := by decide +kernel
theorem sb8_44 : ∀ q ∈ blk8_44, sub8 q = true := by
  unfold blk8_44
  exact List.forall_mem_cons.2 ⟨sub8_1408, List.forall_mem_cons.2 ⟨sub8_1409, List.forall_mem_cons.2 ⟨sub8_1410, List.forall_mem_cons.2 ⟨sub8_1411, List.forall_mem_cons.2 ⟨sub8_1412, List.forall_mem_cons.2 ⟨sub8_1413, List.forall_mem_cons.2 ⟨sub8_1414, List.forall_mem_cons.2 ⟨sub8_1415, List.forall_mem_cons.2 ⟨sub8_1416, List.forall_mem_cons.2 ⟨sub8_1417, List.forall_mem_cons.2 ⟨sub8_1418, List.forall_mem_cons.2 ⟨sub8_1419, List.forall_mem_cons.2 ⟨sub8_1420, List.forall_mem_cons.2 ⟨sub8_1421, List.forall_mem_cons.2 ⟨sub8_1422, List.forall_mem_cons.2 ⟨sub8_1423, List.forall_mem_cons.2 ⟨sub8_1424, List.forall_mem_cons.2 ⟨sub8_1425, List.forall_mem_cons.2 ⟨sub8_1426, List.forall_mem_cons.2 ⟨sub8_1427, List.forall_mem_cons.2 ⟨sub8_1428, List.forall_mem_cons.2 ⟨sub8_1429, List.forall_mem_cons.2 ⟨sub8_1430, List.forall_mem_cons.2 ⟨sub8_1431, List.forall_mem_cons.2 ⟨sub8_1432, List.forall_mem_cons.2 ⟨sub8_1433, List.forall_mem_cons.2 ⟨sub8_1434, List.forall_mem_cons.2 ⟨sub8_1435, List.forall_mem_cons.2 ⟨sub8_1436, List.forall_mem_cons.2 ⟨sub8_1437, List.forall_mem_cons.2 ⟨sub8_1438, List.forall_mem_cons.2 ⟨sub8_1439, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_1440 : sub8 [3, 3, -4] = true := by decide +kernel
theorem sub8_1441 : sub8 [3, 3, -3] = true := by decide +kernel
theorem sub8_1442 : sub8 [3, 3, -2] = true := by decide +kernel
theorem sub8_1443 : sub8 [3, 3, -1] = true := by decide +kernel
theorem sub8_1444 : sub8 [3, 3, 0] = true := by decide +kernel
theorem sub8_1445 : sub8 [3, 3, 1] = true := by decide +kernel
theorem sub8_1446 : sub8 [3, 3, 2] = true := by decide +kernel
theorem sub8_1447 : sub8 [3, 3, 3] = true := by decide +kernel
theorem sub8_1448 : sub8 [3, 3, 4] = true := by decide +kernel
theorem sub8_1449 : sub8 [3, 3, 5] = true := by decide +kernel
theorem sub8_1450 : sub8 [3, 3, 6] = true := by decide +kernel
theorem sub8_1451 : sub8 [3, 3, 7] = true := by decide +kernel
theorem sub8_1452 : sub8 [3, 3, 8] = true := by decide +kernel
theorem sub8_1453 : sub8 [3, 3, 9] = true := by decide +kernel
theorem sub8_1454 : sub8 [3, 4, -8] = true := by decide +kernel
theorem sub8_1455 : sub8 [3, 4, -7] = true := by decide +kernel
theorem sub8_1456 : sub8 [3, 4, -6] = true := by decide +kernel
theorem sub8_1457 : sub8 [3, 4, -5] = true := by decide +kernel
theorem sub8_1458 : sub8 [3, 4, -4] = true := by decide +kernel
theorem sub8_1459 : sub8 [3, 4, -3] = true := by decide +kernel
theorem sub8_1460 : sub8 [3, 4, -2] = true := by decide +kernel
theorem sub8_1461 : sub8 [3, 4, -1] = true := by decide +kernel
theorem sub8_1462 : sub8 [3, 4, 0] = true := by decide +kernel
theorem sub8_1463 : sub8 [3, 4, 1] = true := by decide +kernel
theorem sub8_1464 : sub8 [3, 4, 2] = true := by decide +kernel
theorem sub8_1465 : sub8 [3, 4, 3] = true := by decide +kernel
theorem sub8_1466 : sub8 [3, 4, 4] = true := by decide +kernel
theorem sub8_1467 : sub8 [3, 4, 5] = true := by decide +kernel
theorem sub8_1468 : sub8 [3, 4, 6] = true := by decide +kernel
theorem sub8_1469 : sub8 [3, 4, 7] = true := by decide +kernel
theorem sub8_1470 : sub8 [3, 4, 8] = true := by decide +kernel
theorem sub8_1471 : sub8 [3, 4, 9] = true := by decide +kernel
theorem sb8_45 : ∀ q ∈ blk8_45, sub8 q = true := by
  unfold blk8_45
  exact List.forall_mem_cons.2 ⟨sub8_1440, List.forall_mem_cons.2 ⟨sub8_1441, List.forall_mem_cons.2 ⟨sub8_1442, List.forall_mem_cons.2 ⟨sub8_1443, List.forall_mem_cons.2 ⟨sub8_1444, List.forall_mem_cons.2 ⟨sub8_1445, List.forall_mem_cons.2 ⟨sub8_1446, List.forall_mem_cons.2 ⟨sub8_1447, List.forall_mem_cons.2 ⟨sub8_1448, List.forall_mem_cons.2 ⟨sub8_1449, List.forall_mem_cons.2 ⟨sub8_1450, List.forall_mem_cons.2 ⟨sub8_1451, List.forall_mem_cons.2 ⟨sub8_1452, List.forall_mem_cons.2 ⟨sub8_1453, List.forall_mem_cons.2 ⟨sub8_1454, List.forall_mem_cons.2 ⟨sub8_1455, List.forall_mem_cons.2 ⟨sub8_1456, List.forall_mem_cons.2 ⟨sub8_1457, List.forall_mem_cons.2 ⟨sub8_1458, List.forall_mem_cons.2 ⟨sub8_1459, List.forall_mem_cons.2 ⟨sub8_1460, List.forall_mem_cons.2 ⟨sub8_1461, List.forall_mem_cons.2 ⟨sub8_1462, List.forall_mem_cons.2 ⟨sub8_1463, List.forall_mem_cons.2 ⟨sub8_1464, List.forall_mem_cons.2 ⟨sub8_1465, List.forall_mem_cons.2 ⟨sub8_1466, List.forall_mem_cons.2 ⟨sub8_1467, List.forall_mem_cons.2 ⟨sub8_1468, List.forall_mem_cons.2 ⟨sub8_1469, List.forall_mem_cons.2 ⟨sub8_1470, List.forall_mem_cons.2 ⟨sub8_1471, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_1472 : sub8 [3, 5, -7] = true := by decide +kernel
theorem sub8_1473 : sub8 [3, 5, -6] = true := by decide +kernel
theorem sub8_1474 : sub8 [3, 5, -5] = true := by decide +kernel
theorem sub8_1475 : sub8 [3, 5, -4] = true := by decide +kernel
theorem sub8_1476 : sub8 [3, 5, -3] = true := by decide +kernel
theorem sub8_1477 : sub8 [3, 5, -2] = true := by decide +kernel
theorem sub8_1478 : sub8 [3, 5, -1] = true := by decide +kernel
theorem sub8_1479 : sub8 [3, 5, 0] = true := by decide +kernel
theorem sub8_1480 : sub8 [3, 5, 1] = true := by decide +kernel
theorem sub8_1481 : sub8 [3, 5, 2] = true := by decide +kernel
theorem sub8_1482 : sub8 [3, 5, 3] = true := by decide +kernel
theorem sub8_1483 : sub8 [3, 5, 4] = true := by decide +kernel
theorem sub8_1484 : sub8 [3, 5, 5] = true := by decide +kernel
theorem sub8_1485 : sub8 [3, 5, 6] = true := by decide +kernel
theorem sub8_1486 : sub8 [3, 5, 7] = true := by decide +kernel
theorem sub8_1487 : sub8 [3, 5, 8] = true := by decide +kernel
theorem sub8_1488 : sub8 [3, 6] = true := by decide +kernel
theorem sub8_1489 : sub8 [3, 7] = true := by decide +kernel
theorem sub8_1490 : sub8 [3, 8] = true := by decide +kernel
theorem sub8_1491 : sub8 [4, -5] = true := by decide +kernel
theorem sub8_1492 : sub8 [4, -4] = true := by decide +kernel
theorem sub8_1493 : sub8 [4, -3] = true := by decide +kernel
theorem sub8_1494 : sub8 [4, -2] = true := by decide +kernel
theorem sub8_1495 : sub8 [4, -1, -7] = true := by decide +kernel
theorem sub8_1496 : sub8 [4, -1, -6] = true := by decide +kernel
theorem sub8_1497 : sub8 [4, -1, -5] = true := by decide +kernel
theorem sub8_1498 : sub8 [4, -1, -4] = true := by decide +kernel
theorem sub8_1499 : sub8 [4, -1, -3] = true := by decide +kernel
theorem sub8_1500 : sub8 [4, -1, -2] = true := by decide +kernel
theorem sub8_1501 : sub8 [4, -1, -1] = true := by decide +kernel
theorem sub8_1502 : sub8 [4, -1, 0] = true := by decide +kernel
theorem sub8_1503 : sub8 [4, -1, 1] = true := by decide +kernel
theorem sb8_46 : ∀ q ∈ blk8_46, sub8 q = true := by
  unfold blk8_46
  exact List.forall_mem_cons.2 ⟨sub8_1472, List.forall_mem_cons.2 ⟨sub8_1473, List.forall_mem_cons.2 ⟨sub8_1474, List.forall_mem_cons.2 ⟨sub8_1475, List.forall_mem_cons.2 ⟨sub8_1476, List.forall_mem_cons.2 ⟨sub8_1477, List.forall_mem_cons.2 ⟨sub8_1478, List.forall_mem_cons.2 ⟨sub8_1479, List.forall_mem_cons.2 ⟨sub8_1480, List.forall_mem_cons.2 ⟨sub8_1481, List.forall_mem_cons.2 ⟨sub8_1482, List.forall_mem_cons.2 ⟨sub8_1483, List.forall_mem_cons.2 ⟨sub8_1484, List.forall_mem_cons.2 ⟨sub8_1485, List.forall_mem_cons.2 ⟨sub8_1486, List.forall_mem_cons.2 ⟨sub8_1487, List.forall_mem_cons.2 ⟨sub8_1488, List.forall_mem_cons.2 ⟨sub8_1489, List.forall_mem_cons.2 ⟨sub8_1490, List.forall_mem_cons.2 ⟨sub8_1491, List.forall_mem_cons.2 ⟨sub8_1492, List.forall_mem_cons.2 ⟨sub8_1493, List.forall_mem_cons.2 ⟨sub8_1494, List.forall_mem_cons.2 ⟨sub8_1495, List.forall_mem_cons.2 ⟨sub8_1496, List.forall_mem_cons.2 ⟨sub8_1497, List.forall_mem_cons.2 ⟨sub8_1498, List.forall_mem_cons.2 ⟨sub8_1499, List.forall_mem_cons.2 ⟨sub8_1500, List.forall_mem_cons.2 ⟨sub8_1501, List.forall_mem_cons.2 ⟨sub8_1502, List.forall_mem_cons.2 ⟨sub8_1503, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_1504 : sub8 [4, -1, 2] = true := by decide +kernel
theorem sub8_1505 : sub8 [4, -1, 3] = true := by decide +kernel
theorem sub8_1506 : sub8 [4, -1, 4] = true := by decide +kernel
theorem sub8_1507 : sub8 [4, -1, 5] = true := by decide +kernel
theorem sub8_1508 : sub8 [4, -1, 6] = true := by decide +kernel
theorem sub8_1509 : sub8 [4, -1, 7] = true := by decide +kernel
theorem sub8_1510 : sub8 [4, 0, -8] = true := by decide +kernel
theorem sub8_1511 : sub8 [4, 0, -7] = true := by decide +kernel
theorem sub8_1512 : sub8 [4, 0, -6] = true := by decide +kernel
theorem sub8_1513 : sub8 [4, 0, -5] = true := by decide +kernel
theorem sub8_1514 : sub8 [4, 0, -4] = true := by decide +kernel
theorem sub8_1515 : sub8 [4, 0, -3] = true := by decide +kernel
theorem sub8_1516 : sub8 [4, 0, -2] = true := by decide +kernel
theorem sub8_1517 : sub8 [4, 0, -1] = true := by decide +kernel
theorem sub8_1518 : sub8 [4, 0, 0] = true := by decide +kernel
theorem sub8_1519 : sub8 [4, 0, 1] = true := by decide +kernel
theorem sub8_1520 : sub8 [4, 0, 2] = true := by decide +kernel
theorem sub8_1521 : sub8 [4, 0, 3] = true := by decide +kernel
theorem sub8_1522 : sub8 [4, 0, 4] = true := by decide +kernel
theorem sub8_1523 : sub8 [4, 0, 5] = true := by decide +kernel
theorem sub8_1524 : sub8 [4, 0, 6] = true := by decide +kernel
theorem sub8_1525 : sub8 [4, 0, 7] = true := by decide +kernel
theorem sub8_1526 : sub8 [4, 0, 8] = true := by decide +kernel
theorem sub8_1527 : sub8 [4, 1, -8] = true := by decide +kernel
theorem sub8_1528 : sub8 [4, 1, -7] = true := by decide +kernel
theorem sub8_1529 : sub8 [4, 1, -6] = true := by decide +kernel
theorem sub8_1530 : sub8 [4, 1, -5] = true := by decide +kernel
theorem sub8_1531 : sub8 [4, 1, -4] = true := by decide +kernel
theorem sub8_1532 : sub8 [4, 1, -3] = true := by decide +kernel
theorem sub8_1533 : sub8 [4, 1, -2] = true := by decide +kernel
theorem sub8_1534 : sub8 [4, 1, -1] = true := by decide +kernel
theorem sub8_1535 : sub8 [4, 1, 0] = true := by decide +kernel
theorem sb8_47 : ∀ q ∈ blk8_47, sub8 q = true := by
  unfold blk8_47
  exact List.forall_mem_cons.2 ⟨sub8_1504, List.forall_mem_cons.2 ⟨sub8_1505, List.forall_mem_cons.2 ⟨sub8_1506, List.forall_mem_cons.2 ⟨sub8_1507, List.forall_mem_cons.2 ⟨sub8_1508, List.forall_mem_cons.2 ⟨sub8_1509, List.forall_mem_cons.2 ⟨sub8_1510, List.forall_mem_cons.2 ⟨sub8_1511, List.forall_mem_cons.2 ⟨sub8_1512, List.forall_mem_cons.2 ⟨sub8_1513, List.forall_mem_cons.2 ⟨sub8_1514, List.forall_mem_cons.2 ⟨sub8_1515, List.forall_mem_cons.2 ⟨sub8_1516, List.forall_mem_cons.2 ⟨sub8_1517, List.forall_mem_cons.2 ⟨sub8_1518, List.forall_mem_cons.2 ⟨sub8_1519, List.forall_mem_cons.2 ⟨sub8_1520, List.forall_mem_cons.2 ⟨sub8_1521, List.forall_mem_cons.2 ⟨sub8_1522, List.forall_mem_cons.2 ⟨sub8_1523, List.forall_mem_cons.2 ⟨sub8_1524, List.forall_mem_cons.2 ⟨sub8_1525, List.forall_mem_cons.2 ⟨sub8_1526, List.forall_mem_cons.2 ⟨sub8_1527, List.forall_mem_cons.2 ⟨sub8_1528, List.forall_mem_cons.2 ⟨sub8_1529, List.forall_mem_cons.2 ⟨sub8_1530, List.forall_mem_cons.2 ⟨sub8_1531, List.forall_mem_cons.2 ⟨sub8_1532, List.forall_mem_cons.2 ⟨sub8_1533, List.forall_mem_cons.2 ⟨sub8_1534, List.forall_mem_cons.2 ⟨sub8_1535, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_1536 : sub8 [4, 1, 1] = true := by decide +kernel
theorem sub8_1537 : sub8 [4, 1, 2] = true := by decide +kernel
theorem sub8_1538 : sub8 [4, 1, 3] = true := by decide +kernel
theorem sub8_1539 : sub8 [4, 1, 4] = true := by decide +kernel
theorem sub8_1540 : sub8 [4, 1, 5] = true := by decide +kernel
theorem sub8_1541 : sub8 [4, 1, 6] = true := by decide +kernel
theorem sub8_1542 : sub8 [4, 1, 7] = true := by decide +kernel
theorem sub8_1543 : sub8 [4, 1, 8] = true := by decide +kernel
theorem sub8_1544 : sub8 [4, 2, -8] = true := by decide +kernel
theorem sub8_1545 : sub8 [4, 2, -7] = true := by decide +kernel
theorem sub8_1546 : sub8 [4, 2, -6] = true := by decide +kernel
theorem sub8_1547 : sub8 [4, 2, -5] = true := by decide +kernel
theorem sub8_1548 : sub8 [4, 2, -4] = true := by decide +kernel
theorem sub8_1549 : sub8 [4, 2, -3] = true := by decide +kernel
theorem sub8_1550 : sub8 [4, 2, -2] = true := by decide +kernel
theorem sub8_1551 : sub8 [4, 2, -1] = true := by decide +kernel
theorem sub8_1552 : sub8 [4, 2, 0] = true := by decide +kernel
theorem sub8_1553 : sub8 [4, 2, 1] = true := by decide +kernel
theorem sub8_1554 : sub8 [4, 2, 2] = true := by decide +kernel
theorem sub8_1555 : sub8 [4, 2, 3] = true := by decide +kernel
theorem sub8_1556 : sub8 [4, 2, 4] = true := by decide +kernel
theorem sub8_1557 : sub8 [4, 2, 5] = true := by decide +kernel
theorem sub8_1558 : sub8 [4, 2, 6] = true := by decide +kernel
theorem sub8_1559 : sub8 [4, 2, 7] = true := by decide +kernel
theorem sub8_1560 : sub8 [4, 2, 8] = true := by decide +kernel
theorem sub8_1561 : sub8 [4, 3, -8] = true := by decide +kernel
theorem sub8_1562 : sub8 [4, 3, -7] = true := by decide +kernel
theorem sub8_1563 : sub8 [4, 3, -6] = true := by decide +kernel
theorem sub8_1564 : sub8 [4, 3, -5] = true := by decide +kernel
theorem sub8_1565 : sub8 [4, 3, -4] = true := by decide +kernel
theorem sub8_1566 : sub8 [4, 3, -3] = true := by decide +kernel
theorem sub8_1567 : sub8 [4, 3, -2] = true := by decide +kernel
theorem sb8_48 : ∀ q ∈ blk8_48, sub8 q = true := by
  unfold blk8_48
  exact List.forall_mem_cons.2 ⟨sub8_1536, List.forall_mem_cons.2 ⟨sub8_1537, List.forall_mem_cons.2 ⟨sub8_1538, List.forall_mem_cons.2 ⟨sub8_1539, List.forall_mem_cons.2 ⟨sub8_1540, List.forall_mem_cons.2 ⟨sub8_1541, List.forall_mem_cons.2 ⟨sub8_1542, List.forall_mem_cons.2 ⟨sub8_1543, List.forall_mem_cons.2 ⟨sub8_1544, List.forall_mem_cons.2 ⟨sub8_1545, List.forall_mem_cons.2 ⟨sub8_1546, List.forall_mem_cons.2 ⟨sub8_1547, List.forall_mem_cons.2 ⟨sub8_1548, List.forall_mem_cons.2 ⟨sub8_1549, List.forall_mem_cons.2 ⟨sub8_1550, List.forall_mem_cons.2 ⟨sub8_1551, List.forall_mem_cons.2 ⟨sub8_1552, List.forall_mem_cons.2 ⟨sub8_1553, List.forall_mem_cons.2 ⟨sub8_1554, List.forall_mem_cons.2 ⟨sub8_1555, List.forall_mem_cons.2 ⟨sub8_1556, List.forall_mem_cons.2 ⟨sub8_1557, List.forall_mem_cons.2 ⟨sub8_1558, List.forall_mem_cons.2 ⟨sub8_1559, List.forall_mem_cons.2 ⟨sub8_1560, List.forall_mem_cons.2 ⟨sub8_1561, List.forall_mem_cons.2 ⟨sub8_1562, List.forall_mem_cons.2 ⟨sub8_1563, List.forall_mem_cons.2 ⟨sub8_1564, List.forall_mem_cons.2 ⟨sub8_1565, List.forall_mem_cons.2 ⟨sub8_1566, List.forall_mem_cons.2 ⟨sub8_1567, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_1568 : sub8 [4, 3, -1] = true := by decide +kernel
theorem sub8_1569 : sub8 [4, 3, 0] = true := by decide +kernel
theorem sub8_1570 : sub8 [4, 3, 1] = true := by decide +kernel
theorem sub8_1571 : sub8 [4, 3, 2] = true := by decide +kernel
theorem sub8_1572 : sub8 [4, 3, 3] = true := by decide +kernel
theorem sub8_1573 : sub8 [4, 3, 4] = true := by decide +kernel
theorem sub8_1574 : sub8 [4, 3, 5] = true := by decide +kernel
theorem sub8_1575 : sub8 [4, 3, 6] = true := by decide +kernel
theorem sub8_1576 : sub8 [4, 3, 7] = true := by decide +kernel
theorem sub8_1577 : sub8 [4, 3, 8] = true := by decide +kernel
theorem sub8_1578 : sub8 [4, 4, -7] = true := by decide +kernel
theorem sub8_1579 : sub8 [4, 4, -6] = true := by decide +kernel
theorem sub8_1580 : sub8 [4, 4, -5] = true := by decide +kernel
theorem sub8_1581 : sub8 [4, 4, -4] = true := by decide +kernel
theorem sub8_1582 : sub8 [4, 4, -3] = true := by decide +kernel
theorem sub8_1583 : sub8 [4, 4, -2] = true := by decide +kernel
theorem sub8_1584 : sub8 [4, 4, -1] = true := by decide +kernel
theorem sub8_1585 : sub8 [4, 4, 0] = true := by decide +kernel
theorem sub8_1586 : sub8 [4, 4, 1] = true := by decide +kernel
theorem sub8_1587 : sub8 [4, 4, 2] = true := by decide +kernel
theorem sub8_1588 : sub8 [4, 4, 3] = true := by decide +kernel
theorem sub8_1589 : sub8 [4, 4, 4] = true := by decide +kernel
theorem sub8_1590 : sub8 [4, 4, 5] = true := by decide +kernel
theorem sub8_1591 : sub8 [4, 4, 6] = true := by decide +kernel
theorem sub8_1592 : sub8 [4, 4, 7] = true := by decide +kernel
theorem sub8_1593 : sub8 [4, 4, 8] = true := by decide +kernel
theorem sub8_1594 : sub8 [4, 5, -6] = true := by decide +kernel
theorem sub8_1595 : sub8 [4, 5, -5] = true := by decide +kernel
theorem sub8_1596 : sub8 [4, 5, -4] = true := by decide +kernel
theorem sub8_1597 : sub8 [4, 5, -3] = true := by decide +kernel
theorem sub8_1598 : sub8 [4, 5, -2] = true := by decide +kernel
theorem sub8_1599 : sub8 [4, 5, -1] = true := by decide +kernel
theorem sb8_49 : ∀ q ∈ blk8_49, sub8 q = true := by
  unfold blk8_49
  exact List.forall_mem_cons.2 ⟨sub8_1568, List.forall_mem_cons.2 ⟨sub8_1569, List.forall_mem_cons.2 ⟨sub8_1570, List.forall_mem_cons.2 ⟨sub8_1571, List.forall_mem_cons.2 ⟨sub8_1572, List.forall_mem_cons.2 ⟨sub8_1573, List.forall_mem_cons.2 ⟨sub8_1574, List.forall_mem_cons.2 ⟨sub8_1575, List.forall_mem_cons.2 ⟨sub8_1576, List.forall_mem_cons.2 ⟨sub8_1577, List.forall_mem_cons.2 ⟨sub8_1578, List.forall_mem_cons.2 ⟨sub8_1579, List.forall_mem_cons.2 ⟨sub8_1580, List.forall_mem_cons.2 ⟨sub8_1581, List.forall_mem_cons.2 ⟨sub8_1582, List.forall_mem_cons.2 ⟨sub8_1583, List.forall_mem_cons.2 ⟨sub8_1584, List.forall_mem_cons.2 ⟨sub8_1585, List.forall_mem_cons.2 ⟨sub8_1586, List.forall_mem_cons.2 ⟨sub8_1587, List.forall_mem_cons.2 ⟨sub8_1588, List.forall_mem_cons.2 ⟨sub8_1589, List.forall_mem_cons.2 ⟨sub8_1590, List.forall_mem_cons.2 ⟨sub8_1591, List.forall_mem_cons.2 ⟨sub8_1592, List.forall_mem_cons.2 ⟨sub8_1593, List.forall_mem_cons.2 ⟨sub8_1594, List.forall_mem_cons.2 ⟨sub8_1595, List.forall_mem_cons.2 ⟨sub8_1596, List.forall_mem_cons.2 ⟨sub8_1597, List.forall_mem_cons.2 ⟨sub8_1598, List.forall_mem_cons.2 ⟨sub8_1599, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_1600 : sub8 [4, 5, 0] = true := by decide +kernel
theorem sub8_1601 : sub8 [4, 5, 1] = true := by decide +kernel
theorem sub8_1602 : sub8 [4, 5, 2] = true := by decide +kernel
theorem sub8_1603 : sub8 [4, 5, 3] = true := by decide +kernel
theorem sub8_1604 : sub8 [4, 5, 4] = true := by decide +kernel
theorem sub8_1605 : sub8 [4, 5, 5] = true := by decide +kernel
theorem sub8_1606 : sub8 [4, 5, 6] = true := by decide +kernel
theorem sub8_1607 : sub8 [4, 5, 7] = true := by decide +kernel
theorem sub8_1608 : sub8 [4, 5, 8] = true := by decide +kernel
theorem sub8_1609 : sub8 [4, 6] = true := by decide +kernel
theorem sub8_1610 : sub8 [4, 7] = true := by decide +kernel
theorem sub8_1611 : sub8 [4, 8] = true := by decide +kernel
theorem sub8_1612 : sub8 [5, -4] = true := by decide +kernel
theorem sub8_1613 : sub8 [5, -3] = true := by decide +kernel
theorem sub8_1614 : sub8 [5, -2] = true := by decide +kernel
theorem sub8_1615 : sub8 [5, -1] = true := by decide +kernel
theorem sub8_1616 : sub8 [5, 0] = true := by decide +kernel
theorem sub8_1617 : sub8 [5, 1] = true := by decide +kernel
theorem sub8_1618 : sub8 [5, 2] = true := by decide +kernel
theorem sub8_1619 : sub8 [5, 3] = true := by decide +kernel
theorem sub8_1620 : sub8 [5, 4] = true := by decide +kernel
theorem sub8_1621 : sub8 [5, 5] = true := by decide +kernel
theorem sub8_1622 : sub8 [5, 6] = true := by decide +kernel
theorem sub8_1623 : sub8 [5, 7] = true := by decide +kernel
theorem sub8_1624 : sub8 [6, -2] = true := by decide +kernel
theorem sub8_1625 : sub8 [6, -1] = true := by decide +kernel
theorem sub8_1626 : sub8 [6, 0] = true := by decide +kernel
theorem sub8_1627 : sub8 [6, 1] = true := by decide +kernel
theorem sub8_1628 : sub8 [6, 2] = true := by decide +kernel
theorem sub8_1629 : sub8 [6, 3] = true := by decide +kernel
theorem sub8_1630 : sub8 [6, 4] = true := by decide +kernel
theorem sub8_1631 : sub8 [6, 5] = true := by decide +kernel
theorem sb8_50 : ∀ q ∈ blk8_50, sub8 q = true := by
  unfold blk8_50
  exact List.forall_mem_cons.2 ⟨sub8_1600, List.forall_mem_cons.2 ⟨sub8_1601, List.forall_mem_cons.2 ⟨sub8_1602, List.forall_mem_cons.2 ⟨sub8_1603, List.forall_mem_cons.2 ⟨sub8_1604, List.forall_mem_cons.2 ⟨sub8_1605, List.forall_mem_cons.2 ⟨sub8_1606, List.forall_mem_cons.2 ⟨sub8_1607, List.forall_mem_cons.2 ⟨sub8_1608, List.forall_mem_cons.2 ⟨sub8_1609, List.forall_mem_cons.2 ⟨sub8_1610, List.forall_mem_cons.2 ⟨sub8_1611, List.forall_mem_cons.2 ⟨sub8_1612, List.forall_mem_cons.2 ⟨sub8_1613, List.forall_mem_cons.2 ⟨sub8_1614, List.forall_mem_cons.2 ⟨sub8_1615, List.forall_mem_cons.2 ⟨sub8_1616, List.forall_mem_cons.2 ⟨sub8_1617, List.forall_mem_cons.2 ⟨sub8_1618, List.forall_mem_cons.2 ⟨sub8_1619, List.forall_mem_cons.2 ⟨sub8_1620, List.forall_mem_cons.2 ⟨sub8_1621, List.forall_mem_cons.2 ⟨sub8_1622, List.forall_mem_cons.2 ⟨sub8_1623, List.forall_mem_cons.2 ⟨sub8_1624, List.forall_mem_cons.2 ⟨sub8_1625, List.forall_mem_cons.2 ⟨sub8_1626, List.forall_mem_cons.2 ⟨sub8_1627, List.forall_mem_cons.2 ⟨sub8_1628, List.forall_mem_cons.2 ⟨sub8_1629, List.forall_mem_cons.2 ⟨sub8_1630, List.forall_mem_cons.2 ⟨sub8_1631, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_1632 : sub8 [6, 6] = true := by decide +kernel
theorem sb8_51 : ∀ q ∈ blk8_51, sub8 q = true := by
  unfold blk8_51
  exact List.forall_mem_cons.2 ⟨sub8_1632, List.forall_mem_nil _⟩
theorem sub9_0 : sub9 [-7] = true := by decide +kernel
theorem sub9_1 : sub9 [-6, -7] = true := by decide +kernel
theorem sub9_2 : sub9 [-6, -6] = true := by decide +kernel
theorem sub9_3 : sub9 [-6, -5] = true := by decide +kernel
theorem sub9_4 : sub9 [-6, -4] = true := by decide +kernel
theorem sub9_5 : sub9 [-6, -3] = true := by decide +kernel
theorem sub9_6 : sub9 [-6, -2] = true := by decide +kernel
theorem sub9_7 : sub9 [-6, -1] = true := by decide +kernel
theorem sub9_8 : sub9 [-6, 0] = true := by decide +kernel
theorem sub9_9 : sub9 [-6, 1] = true := by decide +kernel
theorem sub9_10 : sub9 [-6, 2] = true := by decide +kernel
theorem sub9_11 : sub9 [-5, -8] = true := by decide +kernel
theorem sub9_12 : sub9 [-5, -7] = true := by decide +kernel
theorem sub9_13 : sub9 [-5, -6] = true := by decide +kernel
theorem sub9_14 : sub9 [-5, -5] = true := by decide +kernel
theorem sub9_15 : sub9 [-5, -4] = true := by decide +kernel
theorem sub9_16 : sub9 [-5, -3, -10] = true := by decide +kernel
theorem sub9_17 : sub9 [-5, -3, -9] = true := by decide +kernel
theorem sub9_18 : sub9 [-5, -3, -8] = true := by decide +kernel
theorem sub9_19 : sub9 [-5, -3, -7] = true := by decide +kernel
theorem sub9_20 : sub9 [-5, -3, -6] = true := by decide +kernel
theorem sub9_21 : sub9 [-5, -3, -5] = true := by decide +kernel
theorem sub9_22 : sub9 [-5, -3, -4] = true := by decide +kernel
theorem sub9_23 : sub9 [-5, -3, -3] = true := by decide +kernel
theorem sub9_24 : sub9 [-5, -3, -2] = true := by decide +kernel
theorem sub9_25 : sub9 [-5, -3, -1] = true := by decide +kernel
theorem sub9_26 : sub9 [-5, -3, 0] = true := by decide +kernel
theorem sub9_27 : sub9 [-5, -3, 1] = true := by decide +kernel
theorem sub9_28 : sub9 [-5, -3, 2] = true := by decide +kernel
theorem sub9_29 : sub9 [-5, -3, 3] = true := by decide +kernel
theorem sub9_30 : sub9 [-5, -3, 4] = true := by decide +kernel
theorem sub9_31 : sub9 [-5, -2, -10] = true := by decide +kernel
theorem sb9_0 : ∀ q ∈ blk9_0, sub9 q = true := by
  unfold blk9_0
  exact List.forall_mem_cons.2 ⟨sub9_0, List.forall_mem_cons.2 ⟨sub9_1, List.forall_mem_cons.2 ⟨sub9_2, List.forall_mem_cons.2 ⟨sub9_3, List.forall_mem_cons.2 ⟨sub9_4, List.forall_mem_cons.2 ⟨sub9_5, List.forall_mem_cons.2 ⟨sub9_6, List.forall_mem_cons.2 ⟨sub9_7, List.forall_mem_cons.2 ⟨sub9_8, List.forall_mem_cons.2 ⟨sub9_9, List.forall_mem_cons.2 ⟨sub9_10, List.forall_mem_cons.2 ⟨sub9_11, List.forall_mem_cons.2 ⟨sub9_12, List.forall_mem_cons.2 ⟨sub9_13, List.forall_mem_cons.2 ⟨sub9_14, List.forall_mem_cons.2 ⟨sub9_15, List.forall_mem_cons.2 ⟨sub9_16, List.forall_mem_cons.2 ⟨sub9_17, List.forall_mem_cons.2 ⟨sub9_18, List.forall_mem_cons.2 ⟨sub9_19, List.forall_mem_cons.2 ⟨sub9_20, List.forall_mem_cons.2 ⟨sub9_21, List.forall_mem_cons.2 ⟨sub9_22, List.forall_mem_cons.2 ⟨sub9_23, List.forall_mem_cons.2 ⟨sub9_24, List.forall_mem_cons.2 ⟨sub9_25, List.forall_mem_cons.2 ⟨sub9_26, List.forall_mem_cons.2 ⟨sub9_27, List.forall_mem_cons.2 ⟨sub9_28, List.forall_mem_cons.2 ⟨sub9_29, List.forall_mem_cons.2 ⟨sub9_30, List.forall_mem_cons.2 ⟨sub9_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C074
