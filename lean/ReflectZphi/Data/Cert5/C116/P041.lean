import ReflectZphi.Data.Cert5.C116.Base

namespace ReflectZphi.Data.Cert5.C116

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_1_1312 : subd9_1 [-4, 6, -6] = true := by decide +kernel
theorem subd9_1_1313 : subd9_1 [-4, 6, -5] = true := by decide +kernel
theorem subd9_1_1314 : subd9_1 [-4, 6, -4] = true := by decide +kernel
theorem subd9_1_1315 : subd9_1 [-4, 6, -3] = true := by decide +kernel
theorem subd9_1_1316 : subd9_1 [-4, 6, -2] = true := by decide +kernel
theorem subd9_1_1317 : subd9_1 [-4, 6, -1] = true := by decide +kernel
theorem subd9_1_1318 : subd9_1 [-4, 6, 0] = true := by decide +kernel
theorem subd9_1_1319 : subd9_1 [-4, 6, 1] = true := by decide +kernel
theorem subd9_1_1320 : subd9_1 [-4, 6, 2] = true := by decide +kernel
theorem subd9_1_1321 : subd9_1 [-4, 6, 3] = true := by decide +kernel
theorem subd9_1_1322 : subd9_1 [-4, 6, 4] = true := by decide +kernel
theorem subd9_1_1323 : subd9_1 [-4, 6, 5] = true := by decide +kernel
theorem subd9_1_1324 : subd9_1 [-4, 6, 6] = true := by decide +kernel
theorem subd9_1_1325 : subd9_1 [-4, 6, 7] = true := by decide +kernel
theorem subd9_1_1326 : subd9_1 [-4, 6, 8] = true := by decide +kernel
theorem subd9_1_1327 : subd9_1 [-4, 6, 9] = true := by decide +kernel
theorem subd9_1_1328 : subd9_1 [-4, 6, 10] = true := by decide +kernel
theorem subd9_1_1329 : subd9_1 [-4, 7, -4] = true := by decide +kernel
theorem subd9_1_1330 : subd9_1 [-4, 7, -3] = true := by decide +kernel
theorem subd9_1_1331 : subd9_1 [-4, 7, -2] = true := by decide +kernel
theorem subd9_1_1332 : subd9_1 [-4, 7, -1] = true := by decide +kernel
theorem subd9_1_1333 : subd9_1 [-4, 7, 0] = true := by decide +kernel
theorem subd9_1_1334 : subd9_1 [-4, 7, 1] = true := by decide +kernel
theorem subd9_1_1335 : subd9_1 [-4, 7, 2] = true := by decide +kernel
theorem subd9_1_1336 : subd9_1 [-4, 7, 3] = true := by decide +kernel
theorem subd9_1_1337 : subd9_1 [-4, 7, 4] = true := by decide +kernel
theorem subd9_1_1338 : subd9_1 [-4, 7, 5] = true := by decide +kernel
theorem subd9_1_1339 : subd9_1 [-4, 7, 6] = true := by decide +kernel
theorem subd9_1_1340 : subd9_1 [-4, 7, 7] = true := by decide +kernel
theorem subd9_1_1341 : subd9_1 [-4, 7, 8] = true := by decide +kernel
theorem subd9_1_1342 : subd9_1 [-4, 7, 9] = true := by decide +kernel
theorem subd9_1_1343 : subd9_1 [-4, 8] = true := by decide +kernel
theorem sbd9_1_41 : ∀ q ∈ blkd9_1_41, subd9_1 q = true := by
  unfold blkd9_1_41
  exact List.forall_mem_cons.2 ⟨subd9_1_1312, List.forall_mem_cons.2 ⟨subd9_1_1313, List.forall_mem_cons.2 ⟨subd9_1_1314, List.forall_mem_cons.2 ⟨subd9_1_1315, List.forall_mem_cons.2 ⟨subd9_1_1316, List.forall_mem_cons.2 ⟨subd9_1_1317, List.forall_mem_cons.2 ⟨subd9_1_1318, List.forall_mem_cons.2 ⟨subd9_1_1319, List.forall_mem_cons.2 ⟨subd9_1_1320, List.forall_mem_cons.2 ⟨subd9_1_1321, List.forall_mem_cons.2 ⟨subd9_1_1322, List.forall_mem_cons.2 ⟨subd9_1_1323, List.forall_mem_cons.2 ⟨subd9_1_1324, List.forall_mem_cons.2 ⟨subd9_1_1325, List.forall_mem_cons.2 ⟨subd9_1_1326, List.forall_mem_cons.2 ⟨subd9_1_1327, List.forall_mem_cons.2 ⟨subd9_1_1328, List.forall_mem_cons.2 ⟨subd9_1_1329, List.forall_mem_cons.2 ⟨subd9_1_1330, List.forall_mem_cons.2 ⟨subd9_1_1331, List.forall_mem_cons.2 ⟨subd9_1_1332, List.forall_mem_cons.2 ⟨subd9_1_1333, List.forall_mem_cons.2 ⟨subd9_1_1334, List.forall_mem_cons.2 ⟨subd9_1_1335, List.forall_mem_cons.2 ⟨subd9_1_1336, List.forall_mem_cons.2 ⟨subd9_1_1337, List.forall_mem_cons.2 ⟨subd9_1_1338, List.forall_mem_cons.2 ⟨subd9_1_1339, List.forall_mem_cons.2 ⟨subd9_1_1340, List.forall_mem_cons.2 ⟨subd9_1_1341, List.forall_mem_cons.2 ⟨subd9_1_1342, List.forall_mem_cons.2 ⟨subd9_1_1343, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_1344 : subd9_1 [-4, 9] = true := by decide +kernel
theorem subd9_1_1345 : subd9_1 [-4, 10] = true := by decide +kernel
theorem subd9_1_1346 : subd9_1 [-3, -13] = true := by decide +kernel
theorem subd9_1_1347 : subd9_1 [-3, -12] = true := by decide +kernel
theorem subd9_1_1348 : subd9_1 [-3, -11] = true := by decide +kernel
theorem subd9_1_1349 : subd9_1 [-3, -10] = true := by decide +kernel
theorem subd9_1_1350 : subd9_1 [-3, -9, -12] = true := by decide +kernel
theorem subd9_1_1351 : subd9_1 [-3, -9, -11] = true := by decide +kernel
theorem subd9_1_1352 : subd9_1 [-3, -9, -10] = true := by decide +kernel
theorem subd9_1_1353 : subd9_1 [-3, -9, -9] = true := by decide +kernel
theorem subd9_1_1354 : subd9_1 [-3, -9, -8] = true := by decide +kernel
theorem subd9_1_1355 : subd9_1 [-3, -9, -7] = true := by decide +kernel
theorem subd9_1_1356 : subd9_1 [-3, -9, -6] = true := by decide +kernel
theorem subd9_1_1357 : subd9_1 [-3, -9, -5] = true := by decide +kernel
theorem subd9_1_1358 : subd9_1 [-3, -9, -4] = true := by decide +kernel
theorem subd9_1_1359 : subd9_1 [-3, -9, -3] = true := by decide +kernel
theorem subd9_1_1360 : subd9_1 [-3, -9, -2] = true := by decide +kernel
theorem subd9_1_1361 : subd9_1 [-3, -9, -1] = true := by decide +kernel
theorem subd9_1_1362 : subd9_1 [-3, -9, 0] = true := by decide +kernel
theorem subd9_1_1363 : subd9_1 [-3, -9, 1] = true := by decide +kernel
theorem subd9_1_1364 : subd9_1 [-3, -9, 2] = true := by decide +kernel
theorem subd9_1_1365 : subd9_1 [-3, -9, 3] = true := by decide +kernel
theorem subd9_1_1366 : subd9_1 [-3, -8, -12] = true := by decide +kernel
theorem subd9_1_1367 : subd9_1 [-3, -8, -11] = true := by decide +kernel
theorem subd9_1_1368 : subd9_1 [-3, -8, -10] = true := by decide +kernel
theorem subd9_1_1369 : subd9_1 [-3, -8, -9] = true := by decide +kernel
theorem subd9_1_1370 : subd9_1 [-3, -8, -8] = true := by decide +kernel
theorem subd9_1_1371 : subd9_1 [-3, -8, -7] = true := by decide +kernel
theorem subd9_1_1372 : subd9_1 [-3, -8, -6] = true := by decide +kernel
theorem subd9_1_1373 : subd9_1 [-3, -8, -5] = true := by decide +kernel
theorem subd9_1_1374 : subd9_1 [-3, -8, -4] = true := by decide +kernel
theorem subd9_1_1375 : subd9_1 [-3, -8, -3] = true := by decide +kernel
theorem sbd9_1_42 : ∀ q ∈ blkd9_1_42, subd9_1 q = true := by
  unfold blkd9_1_42
  exact List.forall_mem_cons.2 ⟨subd9_1_1344, List.forall_mem_cons.2 ⟨subd9_1_1345, List.forall_mem_cons.2 ⟨subd9_1_1346, List.forall_mem_cons.2 ⟨subd9_1_1347, List.forall_mem_cons.2 ⟨subd9_1_1348, List.forall_mem_cons.2 ⟨subd9_1_1349, List.forall_mem_cons.2 ⟨subd9_1_1350, List.forall_mem_cons.2 ⟨subd9_1_1351, List.forall_mem_cons.2 ⟨subd9_1_1352, List.forall_mem_cons.2 ⟨subd9_1_1353, List.forall_mem_cons.2 ⟨subd9_1_1354, List.forall_mem_cons.2 ⟨subd9_1_1355, List.forall_mem_cons.2 ⟨subd9_1_1356, List.forall_mem_cons.2 ⟨subd9_1_1357, List.forall_mem_cons.2 ⟨subd9_1_1358, List.forall_mem_cons.2 ⟨subd9_1_1359, List.forall_mem_cons.2 ⟨subd9_1_1360, List.forall_mem_cons.2 ⟨subd9_1_1361, List.forall_mem_cons.2 ⟨subd9_1_1362, List.forall_mem_cons.2 ⟨subd9_1_1363, List.forall_mem_cons.2 ⟨subd9_1_1364, List.forall_mem_cons.2 ⟨subd9_1_1365, List.forall_mem_cons.2 ⟨subd9_1_1366, List.forall_mem_cons.2 ⟨subd9_1_1367, List.forall_mem_cons.2 ⟨subd9_1_1368, List.forall_mem_cons.2 ⟨subd9_1_1369, List.forall_mem_cons.2 ⟨subd9_1_1370, List.forall_mem_cons.2 ⟨subd9_1_1371, List.forall_mem_cons.2 ⟨subd9_1_1372, List.forall_mem_cons.2 ⟨subd9_1_1373, List.forall_mem_cons.2 ⟨subd9_1_1374, List.forall_mem_cons.2 ⟨subd9_1_1375, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_1376 : subd9_1 [-3, -8, -2] = true := by decide +kernel
theorem subd9_1_1377 : subd9_1 [-3, -8, -1] = true := by decide +kernel
theorem subd9_1_1378 : subd9_1 [-3, -8, 0] = true := by decide +kernel
theorem subd9_1_1379 : subd9_1 [-3, -8, 1] = true := by decide +kernel
theorem subd9_1_1380 : subd9_1 [-3, -8, 2] = true := by decide +kernel
theorem subd9_1_1381 : subd9_1 [-3, -8, 3] = true := by decide +kernel
theorem subd9_1_1382 : subd9_1 [-3, -8, 4] = true := by decide +kernel
theorem subd9_1_1383 : subd9_1 [-3, -7, -12] = true := by decide +kernel
theorem subd9_1_1384 : subd9_1 [-3, -7, -11] = true := by decide +kernel
theorem subd9_1_1385 : subd9_1 [-3, -7, -10] = true := by decide +kernel
theorem subd9_1_1386 : subd9_1 [-3, -7, -9] = true := by decide +kernel
theorem subd9_1_1387 : subd9_1 [-3, -7, -8] = true := by decide +kernel
theorem subd9_1_1388 : subd9_1 [-3, -7, -7] = true := by decide +kernel
theorem subd9_1_1389 : subd9_1 [-3, -7, -6] = true := by decide +kernel
theorem subd9_1_1390 : subd9_1 [-3, -7, -5] = true := by decide +kernel
theorem subd9_1_1391 : subd9_1 [-3, -7, -4] = true := by decide +kernel
theorem subd9_1_1392 : subd9_1 [-3, -7, -3] = true := by decide +kernel
theorem subd9_1_1393 : subd9_1 [-3, -7, -2] = true := by decide +kernel
theorem subd9_1_1394 : subd9_1 [-3, -7, -1] = true := by decide +kernel
theorem subd9_1_1395 : subd9_1 [-3, -7, 0] = true := by decide +kernel
theorem subd9_1_1396 : subd9_1 [-3, -7, 1] = true := by decide +kernel
theorem subd9_1_1397 : subd9_1 [-3, -7, 2] = true := by decide +kernel
theorem subd9_1_1398 : subd9_1 [-3, -7, 3] = true := by decide +kernel
theorem subd9_1_1399 : subd9_1 [-3, -7, 4] = true := by decide +kernel
theorem subd9_1_1400 : subd9_1 [-3, -7, 5] = true := by decide +kernel
theorem subd9_1_1401 : subd9_1 [-3, -6, -12] = true := by decide +kernel
theorem subd9_1_1402 : subd9_1 [-3, -6, -11] = true := by decide +kernel
theorem subd9_1_1403 : subd9_1 [-3, -6, -10] = true := by decide +kernel
theorem subd9_1_1404 : subd9_1 [-3, -6, -9] = true := by decide +kernel
theorem subd9_1_1405 : subd9_1 [-3, -6, -8] = true := by decide +kernel
theorem subd9_1_1406 : subd9_1 [-3, -6, -7] = true := by decide +kernel
theorem subd9_1_1407 : subd9_1 [-3, -6, -6] = true := by decide +kernel
theorem sbd9_1_43 : ∀ q ∈ blkd9_1_43, subd9_1 q = true := by
  unfold blkd9_1_43
  exact List.forall_mem_cons.2 ⟨subd9_1_1376, List.forall_mem_cons.2 ⟨subd9_1_1377, List.forall_mem_cons.2 ⟨subd9_1_1378, List.forall_mem_cons.2 ⟨subd9_1_1379, List.forall_mem_cons.2 ⟨subd9_1_1380, List.forall_mem_cons.2 ⟨subd9_1_1381, List.forall_mem_cons.2 ⟨subd9_1_1382, List.forall_mem_cons.2 ⟨subd9_1_1383, List.forall_mem_cons.2 ⟨subd9_1_1384, List.forall_mem_cons.2 ⟨subd9_1_1385, List.forall_mem_cons.2 ⟨subd9_1_1386, List.forall_mem_cons.2 ⟨subd9_1_1387, List.forall_mem_cons.2 ⟨subd9_1_1388, List.forall_mem_cons.2 ⟨subd9_1_1389, List.forall_mem_cons.2 ⟨subd9_1_1390, List.forall_mem_cons.2 ⟨subd9_1_1391, List.forall_mem_cons.2 ⟨subd9_1_1392, List.forall_mem_cons.2 ⟨subd9_1_1393, List.forall_mem_cons.2 ⟨subd9_1_1394, List.forall_mem_cons.2 ⟨subd9_1_1395, List.forall_mem_cons.2 ⟨subd9_1_1396, List.forall_mem_cons.2 ⟨subd9_1_1397, List.forall_mem_cons.2 ⟨subd9_1_1398, List.forall_mem_cons.2 ⟨subd9_1_1399, List.forall_mem_cons.2 ⟨subd9_1_1400, List.forall_mem_cons.2 ⟨subd9_1_1401, List.forall_mem_cons.2 ⟨subd9_1_1402, List.forall_mem_cons.2 ⟨subd9_1_1403, List.forall_mem_cons.2 ⟨subd9_1_1404, List.forall_mem_cons.2 ⟨subd9_1_1405, List.forall_mem_cons.2 ⟨subd9_1_1406, List.forall_mem_cons.2 ⟨subd9_1_1407, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_1408 : subd9_1 [-3, -6, -5] = true := by decide +kernel
theorem subd9_1_1409 : subd9_1 [-3, -6, -4] = true := by decide +kernel
theorem subd9_1_1410 : subd9_1 [-3, -6, -3] = true := by decide +kernel
theorem subd9_1_1411 : subd9_1 [-3, -6, -2] = true := by decide +kernel
theorem subd9_1_1412 : subd9_1 [-3, -6, -1] = true := by decide +kernel
theorem subd9_1_1413 : subd9_1 [-3, -6, 0] = true := by decide +kernel
theorem subd9_1_1414 : subd9_1 [-3, -6, 1] = true := by decide +kernel
theorem subd9_1_1415 : subd9_1 [-3, -6, 2] = true := by decide +kernel
theorem subd9_1_1416 : subd9_1 [-3, -6, 3] = true := by decide +kernel
theorem subd9_1_1417 : subd9_1 [-3, -6, 4] = true := by decide +kernel
theorem subd9_1_1418 : subd9_1 [-3, -6, 5] = true := by decide +kernel
theorem subd9_1_1419 : subd9_1 [-3, -6, 6] = true := by decide +kernel
theorem subd9_1_1420 : subd9_1 [-3, -5, -12] = true := by decide +kernel
theorem subd9_1_1421 : subd9_1 [-3, -5, -11] = true := by decide +kernel
theorem subd9_1_1422 : subd9_1 [-3, -5, -10] = true := by decide +kernel
theorem subd9_1_1423 : subd9_1 [-3, -5, -9] = true := by decide +kernel
theorem subd9_1_1424 : subd9_1 [-3, -5, -8] = true := by decide +kernel
theorem subd9_1_1425 : subd9_1 [-3, -5, -7] = true := by decide +kernel
theorem subd9_1_1426 : subd9_1 [-3, -5, -6] = true := by decide +kernel
theorem subd9_1_1427 : subd9_1 [-3, -5, -5] = true := by decide +kernel
theorem subd9_1_1428 : subd9_1 [-3, -5, -4] = true := by decide +kernel
theorem subd9_1_1429 : subd9_1 [-3, -5, -3] = true := by decide +kernel
theorem subd9_1_1430 : subd9_1 [-3, -5, -2] = true := by decide +kernel
theorem subd9_1_1431 : subd9_1 [-3, -5, -1] = true := by decide +kernel
theorem subd9_1_1432 : subd9_1 [-3, -5, 0] = true := by decide +kernel
theorem subd9_1_1433 : subd9_1 [-3, -5, 1] = true := by decide +kernel
theorem subd9_1_1434 : subd9_1 [-3, -5, 2] = true := by decide +kernel
theorem subd9_1_1435 : subd9_1 [-3, -5, 3] = true := by decide +kernel
theorem subd9_1_1436 : subd9_1 [-3, -5, 4] = true := by decide +kernel
theorem subd9_1_1437 : subd9_1 [-3, -5, 5] = true := by decide +kernel
theorem subd9_1_1438 : subd9_1 [-3, -5, 6] = true := by decide +kernel
theorem subd9_1_1439 : subd9_1 [-3, -5, 7] = true := by decide +kernel
theorem sbd9_1_44 : ∀ q ∈ blkd9_1_44, subd9_1 q = true := by
  unfold blkd9_1_44
  exact List.forall_mem_cons.2 ⟨subd9_1_1408, List.forall_mem_cons.2 ⟨subd9_1_1409, List.forall_mem_cons.2 ⟨subd9_1_1410, List.forall_mem_cons.2 ⟨subd9_1_1411, List.forall_mem_cons.2 ⟨subd9_1_1412, List.forall_mem_cons.2 ⟨subd9_1_1413, List.forall_mem_cons.2 ⟨subd9_1_1414, List.forall_mem_cons.2 ⟨subd9_1_1415, List.forall_mem_cons.2 ⟨subd9_1_1416, List.forall_mem_cons.2 ⟨subd9_1_1417, List.forall_mem_cons.2 ⟨subd9_1_1418, List.forall_mem_cons.2 ⟨subd9_1_1419, List.forall_mem_cons.2 ⟨subd9_1_1420, List.forall_mem_cons.2 ⟨subd9_1_1421, List.forall_mem_cons.2 ⟨subd9_1_1422, List.forall_mem_cons.2 ⟨subd9_1_1423, List.forall_mem_cons.2 ⟨subd9_1_1424, List.forall_mem_cons.2 ⟨subd9_1_1425, List.forall_mem_cons.2 ⟨subd9_1_1426, List.forall_mem_cons.2 ⟨subd9_1_1427, List.forall_mem_cons.2 ⟨subd9_1_1428, List.forall_mem_cons.2 ⟨subd9_1_1429, List.forall_mem_cons.2 ⟨subd9_1_1430, List.forall_mem_cons.2 ⟨subd9_1_1431, List.forall_mem_cons.2 ⟨subd9_1_1432, List.forall_mem_cons.2 ⟨subd9_1_1433, List.forall_mem_cons.2 ⟨subd9_1_1434, List.forall_mem_cons.2 ⟨subd9_1_1435, List.forall_mem_cons.2 ⟨subd9_1_1436, List.forall_mem_cons.2 ⟨subd9_1_1437, List.forall_mem_cons.2 ⟨subd9_1_1438, List.forall_mem_cons.2 ⟨subd9_1_1439, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_1440 : subd9_1 [-3, -4, -12] = true := by decide +kernel
theorem subd9_1_1441 : subd9_1 [-3, -4, -11] = true := by decide +kernel
theorem subd9_1_1442 : subd9_1 [-3, -4, -10] = true := by decide +kernel
theorem subd9_1_1443 : subd9_1 [-3, -4, -9] = true := by decide +kernel
theorem subd9_1_1444 : subd9_1 [-3, -4, -8] = true := by decide +kernel
theorem subd9_1_1445 : subd9_1 [-3, -4, -7] = true := by decide +kernel
theorem subd9_1_1446 : subd9_1 [-3, -4, -6] = true := by decide +kernel
theorem subd9_1_1447 : subd9_1 [-3, -4, -5] = true := by decide +kernel
theorem subd9_1_1448 : subd9_1 [-3, -4, -4] = true := by decide +kernel
theorem subd9_1_1449 : subd9_1 [-3, -4, -3] = true := by decide +kernel
theorem subd9_1_1450 : subd9_1 [-3, -4, -2] = true := by decide +kernel
theorem subd9_1_1451 : subd9_1 [-3, -4, -1] = true := by decide +kernel
theorem subd9_1_1452 : subd9_1 [-3, -4, 0] = true := by decide +kernel
theorem subd9_1_1453 : subd9_1 [-3, -4, 1] = true := by decide +kernel
theorem subd9_1_1454 : subd9_1 [-3, -4, 2] = true := by decide +kernel
theorem subd9_1_1455 : subd9_1 [-3, -4, 3] = true := by decide +kernel
theorem subd9_1_1456 : subd9_1 [-3, -4, 4] = true := by decide +kernel
theorem subd9_1_1457 : subd9_1 [-3, -4, 5] = true := by decide +kernel
theorem subd9_1_1458 : subd9_1 [-3, -4, 6] = true := by decide +kernel
theorem subd9_1_1459 : subd9_1 [-3, -4, 7] = true := by decide +kernel
theorem subd9_1_1460 : subd9_1 [-3, -3, -12] = true := by decide +kernel
theorem subd9_1_1461 : subd9_1 [-3, -3, -11] = true := by decide +kernel
theorem subd9_1_1462 : subd9_1 [-3, -3, -10] = true := by decide +kernel
theorem subd9_1_1463 : subd9_1 [-3, -3, -9] = true := by decide +kernel
theorem subd9_1_1464 : subd9_1 [-3, -3, -8] = true := by decide +kernel
theorem subd9_1_1465 : subd9_1 [-3, -3, -7] = true := by decide +kernel
theorem subd9_1_1466 : subd9_1 [-3, -3, -6] = true := by decide +kernel
theorem subd9_1_1467 : subd9_1 [-3, -3, -5] = true := by decide +kernel
theorem subd9_1_1468 : subd9_1 [-3, -3, -4] = true := by decide +kernel
theorem subd9_1_1469 : subd9_1 [-3, -3, -3] = true := by decide +kernel
theorem subd9_1_1470 : subd9_1 [-3, -3, -2] = true := by decide +kernel
theorem subd9_1_1471 : subd9_1 [-3, -3, -1] = true := by decide +kernel
theorem sbd9_1_45 : ∀ q ∈ blkd9_1_45, subd9_1 q = true := by
  unfold blkd9_1_45
  exact List.forall_mem_cons.2 ⟨subd9_1_1440, List.forall_mem_cons.2 ⟨subd9_1_1441, List.forall_mem_cons.2 ⟨subd9_1_1442, List.forall_mem_cons.2 ⟨subd9_1_1443, List.forall_mem_cons.2 ⟨subd9_1_1444, List.forall_mem_cons.2 ⟨subd9_1_1445, List.forall_mem_cons.2 ⟨subd9_1_1446, List.forall_mem_cons.2 ⟨subd9_1_1447, List.forall_mem_cons.2 ⟨subd9_1_1448, List.forall_mem_cons.2 ⟨subd9_1_1449, List.forall_mem_cons.2 ⟨subd9_1_1450, List.forall_mem_cons.2 ⟨subd9_1_1451, List.forall_mem_cons.2 ⟨subd9_1_1452, List.forall_mem_cons.2 ⟨subd9_1_1453, List.forall_mem_cons.2 ⟨subd9_1_1454, List.forall_mem_cons.2 ⟨subd9_1_1455, List.forall_mem_cons.2 ⟨subd9_1_1456, List.forall_mem_cons.2 ⟨subd9_1_1457, List.forall_mem_cons.2 ⟨subd9_1_1458, List.forall_mem_cons.2 ⟨subd9_1_1459, List.forall_mem_cons.2 ⟨subd9_1_1460, List.forall_mem_cons.2 ⟨subd9_1_1461, List.forall_mem_cons.2 ⟨subd9_1_1462, List.forall_mem_cons.2 ⟨subd9_1_1463, List.forall_mem_cons.2 ⟨subd9_1_1464, List.forall_mem_cons.2 ⟨subd9_1_1465, List.forall_mem_cons.2 ⟨subd9_1_1466, List.forall_mem_cons.2 ⟨subd9_1_1467, List.forall_mem_cons.2 ⟨subd9_1_1468, List.forall_mem_cons.2 ⟨subd9_1_1469, List.forall_mem_cons.2 ⟨subd9_1_1470, List.forall_mem_cons.2 ⟨subd9_1_1471, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_1472 : subd9_1 [-3, -3, 0] = true := by decide +kernel
theorem subd9_1_1473 : subd9_1 [-3, -3, 1] = true := by decide +kernel
theorem subd9_1_1474 : subd9_1 [-3, -3, 2] = true := by decide +kernel
theorem subd9_1_1475 : subd9_1 [-3, -3, 3] = true := by decide +kernel
theorem subd9_1_1476 : subd9_1 [-3, -3, 4] = true := by decide +kernel
theorem subd9_1_1477 : subd9_1 [-3, -3, 5] = true := by decide +kernel
theorem subd9_1_1478 : subd9_1 [-3, -3, 6] = true := by decide +kernel
theorem subd9_1_1479 : subd9_1 [-3, -3, 7] = true := by decide +kernel
theorem subd9_1_1480 : subd9_1 [-3, -3, 8] = true := by decide +kernel
theorem subd9_1_1481 : subd9_1 [-3, -2, -11] = true := by decide +kernel
theorem subd9_1_1482 : subd9_1 [-3, -2, -10] = true := by decide +kernel
theorem subd9_1_1483 : subd9_1 [-3, -2, -9] = true := by decide +kernel
theorem subd9_1_1484 : subd9_1 [-3, -2, -8] = true := by decide +kernel
theorem subd9_1_1485 : subd9_1 [-3, -2, -7] = true := by decide +kernel
theorem subd9_1_1486 : subd9_1 [-3, -2, -6] = true := by decide +kernel
theorem subd9_1_1487 : subd9_1 [-3, -2, -5] = true := by decide +kernel
theorem subd9_1_1488 : subd9_1 [-3, -2, -4] = true := by decide +kernel
theorem subd9_1_1489 : subd9_1 [-3, -2, -3] = true := by decide +kernel
theorem subd9_1_1490 : subd9_1 [-3, -2, -2] = true := by decide +kernel
theorem subd9_1_1491 : subd9_1 [-3, -2, -1] = true := by decide +kernel
theorem subd9_1_1492 : subd9_1 [-3, -2, 0] = true := by decide +kernel
theorem subd9_1_1493 : subd9_1 [-3, -2, 1] = true := by decide +kernel
theorem subd9_1_1494 : subd9_1 [-3, -2, 2] = true := by decide +kernel
theorem subd9_1_1495 : subd9_1 [-3, -2, 3] = true := by decide +kernel
theorem subd9_1_1496 : subd9_1 [-3, -2, 4] = true := by decide +kernel
theorem subd9_1_1497 : subd9_1 [-3, -2, 5] = true := by decide +kernel
theorem subd9_1_1498 : subd9_1 [-3, -2, 6] = true := by decide +kernel
theorem subd9_1_1499 : subd9_1 [-3, -2, 7] = true := by decide +kernel
theorem subd9_1_1500 : subd9_1 [-3, -2, 8] = true := by decide +kernel
theorem subd9_1_1501 : subd9_1 [-3, -1, -11] = true := by decide +kernel
theorem subd9_1_1502 : subd9_1 [-3, -1, -10] = true := by decide +kernel
theorem subd9_1_1503 : subd9_1 [-3, -1, -9] = true := by decide +kernel
theorem sbd9_1_46 : ∀ q ∈ blkd9_1_46, subd9_1 q = true := by
  unfold blkd9_1_46
  exact List.forall_mem_cons.2 ⟨subd9_1_1472, List.forall_mem_cons.2 ⟨subd9_1_1473, List.forall_mem_cons.2 ⟨subd9_1_1474, List.forall_mem_cons.2 ⟨subd9_1_1475, List.forall_mem_cons.2 ⟨subd9_1_1476, List.forall_mem_cons.2 ⟨subd9_1_1477, List.forall_mem_cons.2 ⟨subd9_1_1478, List.forall_mem_cons.2 ⟨subd9_1_1479, List.forall_mem_cons.2 ⟨subd9_1_1480, List.forall_mem_cons.2 ⟨subd9_1_1481, List.forall_mem_cons.2 ⟨subd9_1_1482, List.forall_mem_cons.2 ⟨subd9_1_1483, List.forall_mem_cons.2 ⟨subd9_1_1484, List.forall_mem_cons.2 ⟨subd9_1_1485, List.forall_mem_cons.2 ⟨subd9_1_1486, List.forall_mem_cons.2 ⟨subd9_1_1487, List.forall_mem_cons.2 ⟨subd9_1_1488, List.forall_mem_cons.2 ⟨subd9_1_1489, List.forall_mem_cons.2 ⟨subd9_1_1490, List.forall_mem_cons.2 ⟨subd9_1_1491, List.forall_mem_cons.2 ⟨subd9_1_1492, List.forall_mem_cons.2 ⟨subd9_1_1493, List.forall_mem_cons.2 ⟨subd9_1_1494, List.forall_mem_cons.2 ⟨subd9_1_1495, List.forall_mem_cons.2 ⟨subd9_1_1496, List.forall_mem_cons.2 ⟨subd9_1_1497, List.forall_mem_cons.2 ⟨subd9_1_1498, List.forall_mem_cons.2 ⟨subd9_1_1499, List.forall_mem_cons.2 ⟨subd9_1_1500, List.forall_mem_cons.2 ⟨subd9_1_1501, List.forall_mem_cons.2 ⟨subd9_1_1502, List.forall_mem_cons.2 ⟨subd9_1_1503, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_1504 : subd9_1 [-3, -1, -8] = true := by decide +kernel
theorem subd9_1_1505 : subd9_1 [-3, -1, -7] = true := by decide +kernel
theorem subd9_1_1506 : subd9_1 [-3, -1, -6] = true := by decide +kernel
theorem subd9_1_1507 : subd9_1 [-3, -1, -5] = true := by decide +kernel
theorem subd9_1_1508 : subd9_1 [-3, -1, -4] = true := by decide +kernel
theorem subd9_1_1509 : subd9_1 [-3, -1, -3] = true := by decide +kernel
theorem subd9_1_1510 : subd9_1 [-3, -1, -2] = true := by decide +kernel
theorem subd9_1_1511 : subd9_1 [-3, -1, -1] = true := by decide +kernel
theorem subd9_1_1512 : subd9_1 [-3, -1, 0] = true := by decide +kernel
theorem subd9_1_1513 : subd9_1 [-3, -1, 1] = true := by decide +kernel
theorem subd9_1_1514 : subd9_1 [-3, -1, 2] = true := by decide +kernel
theorem subd9_1_1515 : subd9_1 [-3, -1, 3] = true := by decide +kernel
theorem subd9_1_1516 : subd9_1 [-3, -1, 4] = true := by decide +kernel
theorem subd9_1_1517 : subd9_1 [-3, -1, 5] = true := by decide +kernel
theorem subd9_1_1518 : subd9_1 [-3, -1, 6] = true := by decide +kernel
theorem subd9_1_1519 : subd9_1 [-3, -1, 7] = true := by decide +kernel
theorem subd9_1_1520 : subd9_1 [-3, -1, 8] = true := by decide +kernel
theorem subd9_1_1521 : subd9_1 [-3, -1, 9] = true := by decide +kernel
theorem subd9_1_1522 : subd9_1 [-3, 0, -10] = true := by decide +kernel
theorem subd9_1_1523 : subd9_1 [-3, 0, -9] = true := by decide +kernel
theorem subd9_1_1524 : subd9_1 [-3, 0, -8] = true := by decide +kernel
theorem subd9_1_1525 : subd9_1 [-3, 0, -7] = true := by decide +kernel
theorem subd9_1_1526 : subd9_1 [-3, 0, -6] = true := by decide +kernel
theorem subd9_1_1527 : subd9_1 [-3, 0, -5] = true := by decide +kernel
theorem subd9_1_1528 : subd9_1 [-3, 0, -4] = true := by decide +kernel
theorem subd9_1_1529 : subd9_1 [-3, 0, -3] = true := by decide +kernel
theorem subd9_1_1530 : subd9_1 [-3, 0, -2] = true := by decide +kernel
theorem subd9_1_1531 : subd9_1 [-3, 0, -1] = true := by decide +kernel
theorem subd9_1_1532 : subd9_1 [-3, 0, 0] = true := by decide +kernel
theorem subd9_1_1533 : subd9_1 [-3, 0, 1] = true := by decide +kernel
theorem subd9_1_1534 : subd9_1 [-3, 0, 2] = true := by decide +kernel
theorem subd9_1_1535 : subd9_1 [-3, 0, 3] = true := by decide +kernel
theorem sbd9_1_47 : ∀ q ∈ blkd9_1_47, subd9_1 q = true := by
  unfold blkd9_1_47
  exact List.forall_mem_cons.2 ⟨subd9_1_1504, List.forall_mem_cons.2 ⟨subd9_1_1505, List.forall_mem_cons.2 ⟨subd9_1_1506, List.forall_mem_cons.2 ⟨subd9_1_1507, List.forall_mem_cons.2 ⟨subd9_1_1508, List.forall_mem_cons.2 ⟨subd9_1_1509, List.forall_mem_cons.2 ⟨subd9_1_1510, List.forall_mem_cons.2 ⟨subd9_1_1511, List.forall_mem_cons.2 ⟨subd9_1_1512, List.forall_mem_cons.2 ⟨subd9_1_1513, List.forall_mem_cons.2 ⟨subd9_1_1514, List.forall_mem_cons.2 ⟨subd9_1_1515, List.forall_mem_cons.2 ⟨subd9_1_1516, List.forall_mem_cons.2 ⟨subd9_1_1517, List.forall_mem_cons.2 ⟨subd9_1_1518, List.forall_mem_cons.2 ⟨subd9_1_1519, List.forall_mem_cons.2 ⟨subd9_1_1520, List.forall_mem_cons.2 ⟨subd9_1_1521, List.forall_mem_cons.2 ⟨subd9_1_1522, List.forall_mem_cons.2 ⟨subd9_1_1523, List.forall_mem_cons.2 ⟨subd9_1_1524, List.forall_mem_cons.2 ⟨subd9_1_1525, List.forall_mem_cons.2 ⟨subd9_1_1526, List.forall_mem_cons.2 ⟨subd9_1_1527, List.forall_mem_cons.2 ⟨subd9_1_1528, List.forall_mem_cons.2 ⟨subd9_1_1529, List.forall_mem_cons.2 ⟨subd9_1_1530, List.forall_mem_cons.2 ⟨subd9_1_1531, List.forall_mem_cons.2 ⟨subd9_1_1532, List.forall_mem_cons.2 ⟨subd9_1_1533, List.forall_mem_cons.2 ⟨subd9_1_1534, List.forall_mem_cons.2 ⟨subd9_1_1535, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_1536 : subd9_1 [-3, 0, 4] = true := by decide +kernel
theorem subd9_1_1537 : subd9_1 [-3, 0, 5] = true := by decide +kernel
theorem subd9_1_1538 : subd9_1 [-3, 0, 6] = true := by decide +kernel
theorem subd9_1_1539 : subd9_1 [-3, 0, 7] = true := by decide +kernel
theorem subd9_1_1540 : subd9_1 [-3, 0, 8] = true := by decide +kernel
theorem subd9_1_1541 : subd9_1 [-3, 0, 9] = true := by decide +kernel
theorem subd9_1_1542 : subd9_1 [-3, 1, -10] = true := by decide +kernel
theorem subd9_1_1543 : subd9_1 [-3, 1, -9] = true := by decide +kernel
theorem subd9_1_1544 : subd9_1 [-3, 1, -8] = true := by decide +kernel
theorem subd9_1_1545 : subd9_1 [-3, 1, -7] = true := by decide +kernel
theorem subd9_1_1546 : subd9_1 [-3, 1, -6] = true := by decide +kernel
theorem subd9_1_1547 : subd9_1 [-3, 1, -5] = true := by decide +kernel
theorem subd9_1_1548 : subd9_1 [-3, 1, -4] = true := by decide +kernel
theorem subd9_1_1549 : subd9_1 [-3, 1, -3] = true := by decide +kernel
theorem subd9_1_1550 : subd9_1 [-3, 1, -2] = true := by decide +kernel
theorem subd9_1_1551 : subd9_1 [-3, 1, -1] = true := by decide +kernel
theorem subd9_1_1552 : subd9_1 [-3, 1, 0] = true := by decide +kernel
theorem subd9_1_1553 : subd9_1 [-3, 1, 1] = true := by decide +kernel
theorem subd9_1_1554 : subd9_1 [-3, 1, 2] = true := by decide +kernel
theorem subd9_1_1555 : subd9_1 [-3, 1, 3] = true := by decide +kernel
theorem subd9_1_1556 : subd9_1 [-3, 1, 4] = true := by decide +kernel
theorem subd9_1_1557 : subd9_1 [-3, 1, 5] = true := by decide +kernel
theorem subd9_1_1558 : subd9_1 [-3, 1, 6] = true := by decide +kernel
theorem subd9_1_1559 : subd9_1 [-3, 1, 7] = true := by decide +kernel
theorem subd9_1_1560 : subd9_1 [-3, 1, 8] = true := by decide +kernel
theorem subd9_1_1561 : subd9_1 [-3, 1, 9] = true := by decide +kernel
theorem subd9_1_1562 : subd9_1 [-3, 1, 10] = true := by decide +kernel
theorem subd9_1_1563 : subd9_1 [-3, 2, -9] = true := by decide +kernel
theorem subd9_1_1564 : subd9_1 [-3, 2, -8] = true := by decide +kernel
theorem subd9_1_1565 : subd9_1 [-3, 2, -7] = true := by decide +kernel
theorem subd9_1_1566 : subd9_1 [-3, 2, -6] = true := by decide +kernel
theorem subd9_1_1567 : subd9_1 [-3, 2, -5] = true := by decide +kernel
theorem sbd9_1_48 : ∀ q ∈ blkd9_1_48, subd9_1 q = true := by
  unfold blkd9_1_48
  exact List.forall_mem_cons.2 ⟨subd9_1_1536, List.forall_mem_cons.2 ⟨subd9_1_1537, List.forall_mem_cons.2 ⟨subd9_1_1538, List.forall_mem_cons.2 ⟨subd9_1_1539, List.forall_mem_cons.2 ⟨subd9_1_1540, List.forall_mem_cons.2 ⟨subd9_1_1541, List.forall_mem_cons.2 ⟨subd9_1_1542, List.forall_mem_cons.2 ⟨subd9_1_1543, List.forall_mem_cons.2 ⟨subd9_1_1544, List.forall_mem_cons.2 ⟨subd9_1_1545, List.forall_mem_cons.2 ⟨subd9_1_1546, List.forall_mem_cons.2 ⟨subd9_1_1547, List.forall_mem_cons.2 ⟨subd9_1_1548, List.forall_mem_cons.2 ⟨subd9_1_1549, List.forall_mem_cons.2 ⟨subd9_1_1550, List.forall_mem_cons.2 ⟨subd9_1_1551, List.forall_mem_cons.2 ⟨subd9_1_1552, List.forall_mem_cons.2 ⟨subd9_1_1553, List.forall_mem_cons.2 ⟨subd9_1_1554, List.forall_mem_cons.2 ⟨subd9_1_1555, List.forall_mem_cons.2 ⟨subd9_1_1556, List.forall_mem_cons.2 ⟨subd9_1_1557, List.forall_mem_cons.2 ⟨subd9_1_1558, List.forall_mem_cons.2 ⟨subd9_1_1559, List.forall_mem_cons.2 ⟨subd9_1_1560, List.forall_mem_cons.2 ⟨subd9_1_1561, List.forall_mem_cons.2 ⟨subd9_1_1562, List.forall_mem_cons.2 ⟨subd9_1_1563, List.forall_mem_cons.2 ⟨subd9_1_1564, List.forall_mem_cons.2 ⟨subd9_1_1565, List.forall_mem_cons.2 ⟨subd9_1_1566, List.forall_mem_cons.2 ⟨subd9_1_1567, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_1568 : subd9_1 [-3, 2, -4] = true := by decide +kernel
theorem subd9_1_1569 : subd9_1 [-3, 2, -3] = true := by decide +kernel
theorem subd9_1_1570 : subd9_1 [-3, 2, -2] = true := by decide +kernel
theorem subd9_1_1571 : subd9_1 [-3, 2, -1] = true := by decide +kernel
theorem subd9_1_1572 : subd9_1 [-3, 2, 0] = true := by decide +kernel
theorem subd9_1_1573 : subd9_1 [-3, 2, 1] = true := by decide +kernel
theorem subd9_1_1574 : subd9_1 [-3, 2, 2] = true := by decide +kernel
theorem subd9_1_1575 : subd9_1 [-3, 2, 3] = true := by decide +kernel
theorem subd9_1_1576 : subd9_1 [-3, 2, 4] = true := by decide +kernel
theorem subd9_1_1577 : subd9_1 [-3, 2, 5] = true := by decide +kernel
theorem subd9_1_1578 : subd9_1 [-3, 2, 6] = true := by decide +kernel
theorem subd9_1_1579 : subd9_1 [-3, 2, 7] = true := by decide +kernel
theorem subd9_1_1580 : subd9_1 [-3, 2, 8] = true := by decide +kernel
theorem subd9_1_1581 : subd9_1 [-3, 2, 9] = true := by decide +kernel
theorem subd9_1_1582 : subd9_1 [-3, 2, 10] = true := by decide +kernel
theorem subd9_1_1583 : subd9_1 [-3, 3, -9] = true := by decide +kernel
theorem subd9_1_1584 : subd9_1 [-3, 3, -8] = true := by decide +kernel
theorem subd9_1_1585 : subd9_1 [-3, 3, -7] = true := by decide +kernel
theorem subd9_1_1586 : subd9_1 [-3, 3, -6] = true := by decide +kernel
theorem subd9_1_1587 : subd9_1 [-3, 3, -5] = true := by decide +kernel
theorem subd9_1_1588 : subd9_1 [-3, 3, -4] = true := by decide +kernel
theorem subd9_1_1589 : subd9_1 [-3, 3, -3] = true := by decide +kernel
theorem subd9_1_1590 : subd9_1 [-3, 3, -2] = true := by decide +kernel
theorem subd9_1_1591 : subd9_1 [-3, 3, -1] = true := by decide +kernel
theorem subd9_1_1592 : subd9_1 [-3, 3, 0] = true := by decide +kernel
theorem subd9_1_1593 : subd9_1 [-3, 3, 1] = true := by decide +kernel
theorem subd9_1_1594 : subd9_1 [-3, 3, 2] = true := by decide +kernel
theorem subd9_1_1595 : subd9_1 [-3, 3, 3] = true := by decide +kernel
theorem subd9_1_1596 : subd9_1 [-3, 3, 4] = true := by decide +kernel
theorem subd9_1_1597 : subd9_1 [-3, 3, 5] = true := by decide +kernel
theorem subd9_1_1598 : subd9_1 [-3, 3, 6] = true := by decide +kernel
theorem subd9_1_1599 : subd9_1 [-3, 3, 7] = true := by decide +kernel
theorem sbd9_1_49 : ∀ q ∈ blkd9_1_49, subd9_1 q = true := by
  unfold blkd9_1_49
  exact List.forall_mem_cons.2 ⟨subd9_1_1568, List.forall_mem_cons.2 ⟨subd9_1_1569, List.forall_mem_cons.2 ⟨subd9_1_1570, List.forall_mem_cons.2 ⟨subd9_1_1571, List.forall_mem_cons.2 ⟨subd9_1_1572, List.forall_mem_cons.2 ⟨subd9_1_1573, List.forall_mem_cons.2 ⟨subd9_1_1574, List.forall_mem_cons.2 ⟨subd9_1_1575, List.forall_mem_cons.2 ⟨subd9_1_1576, List.forall_mem_cons.2 ⟨subd9_1_1577, List.forall_mem_cons.2 ⟨subd9_1_1578, List.forall_mem_cons.2 ⟨subd9_1_1579, List.forall_mem_cons.2 ⟨subd9_1_1580, List.forall_mem_cons.2 ⟨subd9_1_1581, List.forall_mem_cons.2 ⟨subd9_1_1582, List.forall_mem_cons.2 ⟨subd9_1_1583, List.forall_mem_cons.2 ⟨subd9_1_1584, List.forall_mem_cons.2 ⟨subd9_1_1585, List.forall_mem_cons.2 ⟨subd9_1_1586, List.forall_mem_cons.2 ⟨subd9_1_1587, List.forall_mem_cons.2 ⟨subd9_1_1588, List.forall_mem_cons.2 ⟨subd9_1_1589, List.forall_mem_cons.2 ⟨subd9_1_1590, List.forall_mem_cons.2 ⟨subd9_1_1591, List.forall_mem_cons.2 ⟨subd9_1_1592, List.forall_mem_cons.2 ⟨subd9_1_1593, List.forall_mem_cons.2 ⟨subd9_1_1594, List.forall_mem_cons.2 ⟨subd9_1_1595, List.forall_mem_cons.2 ⟨subd9_1_1596, List.forall_mem_cons.2 ⟨subd9_1_1597, List.forall_mem_cons.2 ⟨subd9_1_1598, List.forall_mem_cons.2 ⟨subd9_1_1599, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_1600 : subd9_1 [-3, 3, 8] = true := by decide +kernel
theorem subd9_1_1601 : subd9_1 [-3, 3, 9] = true := by decide +kernel
theorem subd9_1_1602 : subd9_1 [-3, 3, 10] = true := by decide +kernel
theorem subd9_1_1603 : subd9_1 [-3, 4, -8] = true := by decide +kernel
theorem subd9_1_1604 : subd9_1 [-3, 4, -7] = true := by decide +kernel
theorem subd9_1_1605 : subd9_1 [-3, 4, -6] = true := by decide +kernel
theorem subd9_1_1606 : subd9_1 [-3, 4, -5] = true := by decide +kernel
theorem subd9_1_1607 : subd9_1 [-3, 4, -4] = true := by decide +kernel
theorem subd9_1_1608 : subd9_1 [-3, 4, -3] = true := by decide +kernel
theorem subd9_1_1609 : subd9_1 [-3, 4, -2] = true := by decide +kernel
theorem subd9_1_1610 : subd9_1 [-3, 4, -1] = true := by decide +kernel
theorem subd9_1_1611 : subd9_1 [-3, 4, 0] = true := by decide +kernel
theorem subd9_1_1612 : subd9_1 [-3, 4, 1] = true := by decide +kernel
theorem subd9_1_1613 : subd9_1 [-3, 4, 2] = true := by decide +kernel
theorem subd9_1_1614 : subd9_1 [-3, 4, 3] = true := by decide +kernel
theorem subd9_1_1615 : subd9_1 [-3, 4, 4] = true := by decide +kernel
theorem subd9_1_1616 : subd9_1 [-3, 4, 5] = true := by decide +kernel
theorem subd9_1_1617 : subd9_1 [-3, 4, 6] = true := by decide +kernel
theorem subd9_1_1618 : subd9_1 [-3, 4, 7] = true := by decide +kernel
theorem subd9_1_1619 : subd9_1 [-3, 4, 8] = true := by decide +kernel
theorem subd9_1_1620 : subd9_1 [-3, 4, 9] = true := by decide +kernel
theorem subd9_1_1621 : subd9_1 [-3, 4, 10] = true := by decide +kernel
theorem subd9_1_1622 : subd9_1 [-3, 5, -7] = true := by decide +kernel
theorem subd9_1_1623 : subd9_1 [-3, 5, -6] = true := by decide +kernel
theorem subd9_1_1624 : subd9_1 [-3, 5, -5] = true := by decide +kernel
theorem subd9_1_1625 : subd9_1 [-3, 5, -4] = true := by decide +kernel
theorem subd9_1_1626 : subd9_1 [-3, 5, -3] = true := by decide +kernel
theorem subd9_1_1627 : subd9_1 [-3, 5, -2] = true := by decide +kernel
theorem subd9_1_1628 : subd9_1 [-3, 5, -1] = true := by decide +kernel
theorem subd9_1_1629 : subd9_1 [-3, 5, 0] = true := by decide +kernel
theorem subd9_1_1630 : subd9_1 [-3, 5, 1] = true := by decide +kernel
theorem subd9_1_1631 : subd9_1 [-3, 5, 2] = true := by decide +kernel
theorem sbd9_1_50 : ∀ q ∈ blkd9_1_50, subd9_1 q = true := by
  unfold blkd9_1_50
  exact List.forall_mem_cons.2 ⟨subd9_1_1600, List.forall_mem_cons.2 ⟨subd9_1_1601, List.forall_mem_cons.2 ⟨subd9_1_1602, List.forall_mem_cons.2 ⟨subd9_1_1603, List.forall_mem_cons.2 ⟨subd9_1_1604, List.forall_mem_cons.2 ⟨subd9_1_1605, List.forall_mem_cons.2 ⟨subd9_1_1606, List.forall_mem_cons.2 ⟨subd9_1_1607, List.forall_mem_cons.2 ⟨subd9_1_1608, List.forall_mem_cons.2 ⟨subd9_1_1609, List.forall_mem_cons.2 ⟨subd9_1_1610, List.forall_mem_cons.2 ⟨subd9_1_1611, List.forall_mem_cons.2 ⟨subd9_1_1612, List.forall_mem_cons.2 ⟨subd9_1_1613, List.forall_mem_cons.2 ⟨subd9_1_1614, List.forall_mem_cons.2 ⟨subd9_1_1615, List.forall_mem_cons.2 ⟨subd9_1_1616, List.forall_mem_cons.2 ⟨subd9_1_1617, List.forall_mem_cons.2 ⟨subd9_1_1618, List.forall_mem_cons.2 ⟨subd9_1_1619, List.forall_mem_cons.2 ⟨subd9_1_1620, List.forall_mem_cons.2 ⟨subd9_1_1621, List.forall_mem_cons.2 ⟨subd9_1_1622, List.forall_mem_cons.2 ⟨subd9_1_1623, List.forall_mem_cons.2 ⟨subd9_1_1624, List.forall_mem_cons.2 ⟨subd9_1_1625, List.forall_mem_cons.2 ⟨subd9_1_1626, List.forall_mem_cons.2 ⟨subd9_1_1627, List.forall_mem_cons.2 ⟨subd9_1_1628, List.forall_mem_cons.2 ⟨subd9_1_1629, List.forall_mem_cons.2 ⟨subd9_1_1630, List.forall_mem_cons.2 ⟨subd9_1_1631, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_1632 : subd9_1 [-3, 5, 3] = true := by decide +kernel
theorem subd9_1_1633 : subd9_1 [-3, 5, 4] = true := by decide +kernel
theorem subd9_1_1634 : subd9_1 [-3, 5, 5] = true := by decide +kernel
theorem subd9_1_1635 : subd9_1 [-3, 5, 6] = true := by decide +kernel
theorem subd9_1_1636 : subd9_1 [-3, 5, 7] = true := by decide +kernel
theorem subd9_1_1637 : subd9_1 [-3, 5, 8] = true := by decide +kernel
theorem subd9_1_1638 : subd9_1 [-3, 5, 9] = true := by decide +kernel
theorem subd9_1_1639 : subd9_1 [-3, 5, 10] = true := by decide +kernel
theorem subd9_1_1640 : subd9_1 [-3, 6, -6] = true := by decide +kernel
theorem subd9_1_1641 : subd9_1 [-3, 6, -5] = true := by decide +kernel
theorem subd9_1_1642 : subd9_1 [-3, 6, -4] = true := by decide +kernel
theorem subd9_1_1643 : subd9_1 [-3, 6, -3] = true := by decide +kernel
theorem subd9_1_1644 : subd9_1 [-3, 6, -2] = true := by decide +kernel
theorem subd9_1_1645 : subd9_1 [-3, 6, -1] = true := by decide +kernel
theorem subd9_1_1646 : subd9_1 [-3, 6, 0] = true := by decide +kernel
theorem subd9_1_1647 : subd9_1 [-3, 6, 1] = true := by decide +kernel
theorem subd9_1_1648 : subd9_1 [-3, 6, 2] = true := by decide +kernel
theorem subd9_1_1649 : subd9_1 [-3, 6, 3] = true := by decide +kernel
theorem subd9_1_1650 : subd9_1 [-3, 6, 4] = true := by decide +kernel
theorem subd9_1_1651 : subd9_1 [-3, 6, 5] = true := by decide +kernel
theorem subd9_1_1652 : subd9_1 [-3, 6, 6] = true := by decide +kernel
theorem subd9_1_1653 : subd9_1 [-3, 6, 7] = true := by decide +kernel
theorem subd9_1_1654 : subd9_1 [-3, 6, 8] = true := by decide +kernel
theorem subd9_1_1655 : subd9_1 [-3, 6, 9] = true := by decide +kernel
theorem subd9_1_1656 : subd9_1 [-3, 6, 10] = true := by decide +kernel
theorem subd9_1_1657 : subd9_1 [-3, 7, -5] = true := by decide +kernel
theorem subd9_1_1658 : subd9_1 [-3, 7, -4] = true := by decide +kernel
theorem subd9_1_1659 : subd9_1 [-3, 7, -3] = true := by decide +kernel
theorem subd9_1_1660 : subd9_1 [-3, 7, -2] = true := by decide +kernel
theorem subd9_1_1661 : subd9_1 [-3, 7, -1] = true := by decide +kernel
theorem subd9_1_1662 : subd9_1 [-3, 7, 0] = true := by decide +kernel
theorem subd9_1_1663 : subd9_1 [-3, 7, 1] = true := by decide +kernel
theorem sbd9_1_51 : ∀ q ∈ blkd9_1_51, subd9_1 q = true := by
  unfold blkd9_1_51
  exact List.forall_mem_cons.2 ⟨subd9_1_1632, List.forall_mem_cons.2 ⟨subd9_1_1633, List.forall_mem_cons.2 ⟨subd9_1_1634, List.forall_mem_cons.2 ⟨subd9_1_1635, List.forall_mem_cons.2 ⟨subd9_1_1636, List.forall_mem_cons.2 ⟨subd9_1_1637, List.forall_mem_cons.2 ⟨subd9_1_1638, List.forall_mem_cons.2 ⟨subd9_1_1639, List.forall_mem_cons.2 ⟨subd9_1_1640, List.forall_mem_cons.2 ⟨subd9_1_1641, List.forall_mem_cons.2 ⟨subd9_1_1642, List.forall_mem_cons.2 ⟨subd9_1_1643, List.forall_mem_cons.2 ⟨subd9_1_1644, List.forall_mem_cons.2 ⟨subd9_1_1645, List.forall_mem_cons.2 ⟨subd9_1_1646, List.forall_mem_cons.2 ⟨subd9_1_1647, List.forall_mem_cons.2 ⟨subd9_1_1648, List.forall_mem_cons.2 ⟨subd9_1_1649, List.forall_mem_cons.2 ⟨subd9_1_1650, List.forall_mem_cons.2 ⟨subd9_1_1651, List.forall_mem_cons.2 ⟨subd9_1_1652, List.forall_mem_cons.2 ⟨subd9_1_1653, List.forall_mem_cons.2 ⟨subd9_1_1654, List.forall_mem_cons.2 ⟨subd9_1_1655, List.forall_mem_cons.2 ⟨subd9_1_1656, List.forall_mem_cons.2 ⟨subd9_1_1657, List.forall_mem_cons.2 ⟨subd9_1_1658, List.forall_mem_cons.2 ⟨subd9_1_1659, List.forall_mem_cons.2 ⟨subd9_1_1660, List.forall_mem_cons.2 ⟨subd9_1_1661, List.forall_mem_cons.2 ⟨subd9_1_1662, List.forall_mem_cons.2 ⟨subd9_1_1663, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_1664 : subd9_1 [-3, 7, 2] = true := by decide +kernel
theorem subd9_1_1665 : subd9_1 [-3, 7, 3] = true := by decide +kernel
theorem subd9_1_1666 : subd9_1 [-3, 7, 4] = true := by decide +kernel
theorem subd9_1_1667 : subd9_1 [-3, 7, 5] = true := by decide +kernel
theorem subd9_1_1668 : subd9_1 [-3, 7, 6] = true := by decide +kernel
theorem subd9_1_1669 : subd9_1 [-3, 7, 7] = true := by decide +kernel
theorem subd9_1_1670 : subd9_1 [-3, 7, 8] = true := by decide +kernel
theorem subd9_1_1671 : subd9_1 [-3, 7, 9] = true := by decide +kernel
theorem subd9_1_1672 : subd9_1 [-3, 7, 10] = true := by decide +kernel
theorem subd9_1_1673 : subd9_1 [-3, 8] = true := by decide +kernel
theorem subd9_1_1674 : subd9_1 [-3, 9] = true := by decide +kernel
theorem subd9_1_1675 : subd9_1 [-3, 10] = true := by decide +kernel
theorem subd9_1_1676 : subd9_1 [-2, -13] = true := by decide +kernel
theorem subd9_1_1677 : subd9_1 [-2, -12] = true := by decide +kernel
theorem subd9_1_1678 : subd9_1 [-2, -11] = true := by decide +kernel
theorem subd9_1_1679 : subd9_1 [-2, -10] = true := by decide +kernel
theorem subd9_1_1680 : subd9_1 [-2, -9, -12] = true := by decide +kernel
theorem subd9_1_1681 : subd9_1 [-2, -9, -11] = true := by decide +kernel
theorem subd9_1_1682 : subd9_1 [-2, -9, -10] = true := by decide +kernel
theorem subd9_1_1683 : subd9_1 [-2, -9, -9] = true := by decide +kernel
theorem subd9_1_1684 : subd9_1 [-2, -9, -8] = true := by decide +kernel
theorem subd9_1_1685 : subd9_1 [-2, -9, -7] = true := by decide +kernel
theorem subd9_1_1686 : subd9_1 [-2, -9, -6] = true := by decide +kernel
theorem subd9_1_1687 : subd9_1 [-2, -9, -5] = true := by decide +kernel
theorem subd9_1_1688 : subd9_1 [-2, -9, -4] = true := by decide +kernel
theorem subd9_1_1689 : subd9_1 [-2, -9, -3] = true := by decide +kernel
theorem subd9_1_1690 : subd9_1 [-2, -9, -2] = true := by decide +kernel
theorem subd9_1_1691 : subd9_1 [-2, -9, -1] = true := by decide +kernel
theorem subd9_1_1692 : subd9_1 [-2, -9, 0] = true := by decide +kernel
theorem subd9_1_1693 : subd9_1 [-2, -9, 1] = true := by decide +kernel
theorem subd9_1_1694 : subd9_1 [-2, -9, 2] = true := by decide +kernel
theorem subd9_1_1695 : subd9_1 [-2, -9, 3] = true := by decide +kernel
theorem sbd9_1_52 : ∀ q ∈ blkd9_1_52, subd9_1 q = true := by
  unfold blkd9_1_52
  exact List.forall_mem_cons.2 ⟨subd9_1_1664, List.forall_mem_cons.2 ⟨subd9_1_1665, List.forall_mem_cons.2 ⟨subd9_1_1666, List.forall_mem_cons.2 ⟨subd9_1_1667, List.forall_mem_cons.2 ⟨subd9_1_1668, List.forall_mem_cons.2 ⟨subd9_1_1669, List.forall_mem_cons.2 ⟨subd9_1_1670, List.forall_mem_cons.2 ⟨subd9_1_1671, List.forall_mem_cons.2 ⟨subd9_1_1672, List.forall_mem_cons.2 ⟨subd9_1_1673, List.forall_mem_cons.2 ⟨subd9_1_1674, List.forall_mem_cons.2 ⟨subd9_1_1675, List.forall_mem_cons.2 ⟨subd9_1_1676, List.forall_mem_cons.2 ⟨subd9_1_1677, List.forall_mem_cons.2 ⟨subd9_1_1678, List.forall_mem_cons.2 ⟨subd9_1_1679, List.forall_mem_cons.2 ⟨subd9_1_1680, List.forall_mem_cons.2 ⟨subd9_1_1681, List.forall_mem_cons.2 ⟨subd9_1_1682, List.forall_mem_cons.2 ⟨subd9_1_1683, List.forall_mem_cons.2 ⟨subd9_1_1684, List.forall_mem_cons.2 ⟨subd9_1_1685, List.forall_mem_cons.2 ⟨subd9_1_1686, List.forall_mem_cons.2 ⟨subd9_1_1687, List.forall_mem_cons.2 ⟨subd9_1_1688, List.forall_mem_cons.2 ⟨subd9_1_1689, List.forall_mem_cons.2 ⟨subd9_1_1690, List.forall_mem_cons.2 ⟨subd9_1_1691, List.forall_mem_cons.2 ⟨subd9_1_1692, List.forall_mem_cons.2 ⟨subd9_1_1693, List.forall_mem_cons.2 ⟨subd9_1_1694, List.forall_mem_cons.2 ⟨subd9_1_1695, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_1696 : subd9_1 [-2, -8, -12] = true := by decide +kernel
theorem subd9_1_1697 : subd9_1 [-2, -8, -11] = true := by decide +kernel
theorem subd9_1_1698 : subd9_1 [-2, -8, -10] = true := by decide +kernel
theorem subd9_1_1699 : subd9_1 [-2, -8, -9] = true := by decide +kernel
theorem subd9_1_1700 : subd9_1 [-2, -8, -8] = true := by decide +kernel
theorem subd9_1_1701 : subd9_1 [-2, -8, -7] = true := by decide +kernel
theorem subd9_1_1702 : subd9_1 [-2, -8, -6] = true := by decide +kernel
theorem subd9_1_1703 : subd9_1 [-2, -8, -5] = true := by decide +kernel
theorem subd9_1_1704 : subd9_1 [-2, -8, -4] = true := by decide +kernel
theorem subd9_1_1705 : subd9_1 [-2, -8, -3] = true := by decide +kernel
theorem subd9_1_1706 : subd9_1 [-2, -8, -2] = true := by decide +kernel
theorem subd9_1_1707 : subd9_1 [-2, -8, -1] = true := by decide +kernel
theorem subd9_1_1708 : subd9_1 [-2, -8, 0] = true := by decide +kernel
theorem subd9_1_1709 : subd9_1 [-2, -8, 1] = true := by decide +kernel
theorem subd9_1_1710 : subd9_1 [-2, -8, 2] = true := by decide +kernel
theorem subd9_1_1711 : subd9_1 [-2, -8, 3] = true := by decide +kernel
theorem subd9_1_1712 : subd9_1 [-2, -8, 4] = true := by decide +kernel
theorem subd9_1_1713 : subd9_1 [-2, -7, -12] = true := by decide +kernel
theorem subd9_1_1714 : subd9_1 [-2, -7, -11] = true := by decide +kernel
theorem subd9_1_1715 : subd9_1 [-2, -7, -10] = true := by decide +kernel
theorem subd9_1_1716 : subd9_1 [-2, -7, -9] = true := by decide +kernel
theorem subd9_1_1717 : subd9_1 [-2, -7, -8] = true := by decide +kernel
theorem subd9_1_1718 : subd9_1 [-2, -7, -7] = true := by decide +kernel
theorem subd9_1_1719 : subd9_1 [-2, -7, -6] = true := by decide +kernel
theorem subd9_1_1720 : subd9_1 [-2, -7, -5] = true := by decide +kernel
theorem subd9_1_1721 : subd9_1 [-2, -7, -4] = true := by decide +kernel
theorem subd9_1_1722 : subd9_1 [-2, -7, -3] = true := by decide +kernel
theorem subd9_1_1723 : subd9_1 [-2, -7, -2] = true := by decide +kernel
theorem subd9_1_1724 : subd9_1 [-2, -7, -1] = true := by decide +kernel
theorem subd9_1_1725 : subd9_1 [-2, -7, 0] = true := by decide +kernel
theorem subd9_1_1726 : subd9_1 [-2, -7, 1] = true := by decide +kernel
theorem subd9_1_1727 : subd9_1 [-2, -7, 2] = true := by decide +kernel
theorem sbd9_1_53 : ∀ q ∈ blkd9_1_53, subd9_1 q = true := by
  unfold blkd9_1_53
  exact List.forall_mem_cons.2 ⟨subd9_1_1696, List.forall_mem_cons.2 ⟨subd9_1_1697, List.forall_mem_cons.2 ⟨subd9_1_1698, List.forall_mem_cons.2 ⟨subd9_1_1699, List.forall_mem_cons.2 ⟨subd9_1_1700, List.forall_mem_cons.2 ⟨subd9_1_1701, List.forall_mem_cons.2 ⟨subd9_1_1702, List.forall_mem_cons.2 ⟨subd9_1_1703, List.forall_mem_cons.2 ⟨subd9_1_1704, List.forall_mem_cons.2 ⟨subd9_1_1705, List.forall_mem_cons.2 ⟨subd9_1_1706, List.forall_mem_cons.2 ⟨subd9_1_1707, List.forall_mem_cons.2 ⟨subd9_1_1708, List.forall_mem_cons.2 ⟨subd9_1_1709, List.forall_mem_cons.2 ⟨subd9_1_1710, List.forall_mem_cons.2 ⟨subd9_1_1711, List.forall_mem_cons.2 ⟨subd9_1_1712, List.forall_mem_cons.2 ⟨subd9_1_1713, List.forall_mem_cons.2 ⟨subd9_1_1714, List.forall_mem_cons.2 ⟨subd9_1_1715, List.forall_mem_cons.2 ⟨subd9_1_1716, List.forall_mem_cons.2 ⟨subd9_1_1717, List.forall_mem_cons.2 ⟨subd9_1_1718, List.forall_mem_cons.2 ⟨subd9_1_1719, List.forall_mem_cons.2 ⟨subd9_1_1720, List.forall_mem_cons.2 ⟨subd9_1_1721, List.forall_mem_cons.2 ⟨subd9_1_1722, List.forall_mem_cons.2 ⟨subd9_1_1723, List.forall_mem_cons.2 ⟨subd9_1_1724, List.forall_mem_cons.2 ⟨subd9_1_1725, List.forall_mem_cons.2 ⟨subd9_1_1726, List.forall_mem_cons.2 ⟨subd9_1_1727, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_1728 : subd9_1 [-2, -7, 3] = true := by decide +kernel
theorem subd9_1_1729 : subd9_1 [-2, -7, 4] = true := by decide +kernel
theorem subd9_1_1730 : subd9_1 [-2, -7, 5] = true := by decide +kernel
theorem subd9_1_1731 : subd9_1 [-2, -6, -12] = true := by decide +kernel
theorem subd9_1_1732 : subd9_1 [-2, -6, -11] = true := by decide +kernel
theorem subd9_1_1733 : subd9_1 [-2, -6, -10] = true := by decide +kernel
theorem subd9_1_1734 : subd9_1 [-2, -6, -9] = true := by decide +kernel
theorem subd9_1_1735 : subd9_1 [-2, -6, -8] = true := by decide +kernel
theorem subd9_1_1736 : subd9_1 [-2, -6, -7] = true := by decide +kernel
theorem subd9_1_1737 : subd9_1 [-2, -6, -6] = true := by decide +kernel
theorem subd9_1_1738 : subd9_1 [-2, -6, -5] = true := by decide +kernel
theorem subd9_1_1739 : subd9_1 [-2, -6, -4] = true := by decide +kernel
theorem subd9_1_1740 : subd9_1 [-2, -6, -3] = true := by decide +kernel
theorem subd9_1_1741 : subd9_1 [-2, -6, -2] = true := by decide +kernel
theorem subd9_1_1742 : subd9_1 [-2, -6, -1] = true := by decide +kernel
theorem subd9_1_1743 : subd9_1 [-2, -6, 0] = true := by decide +kernel
theorem subd9_1_1744 : subd9_1 [-2, -6, 1] = true := by decide +kernel
theorem subd9_1_1745 : subd9_1 [-2, -6, 2] = true := by decide +kernel
theorem subd9_1_1746 : subd9_1 [-2, -6, 3] = true := by decide +kernel
theorem subd9_1_1747 : subd9_1 [-2, -6, 4] = true := by decide +kernel
theorem subd9_1_1748 : subd9_1 [-2, -6, 5] = true := by decide +kernel
theorem subd9_1_1749 : subd9_1 [-2, -6, 6] = true := by decide +kernel
theorem subd9_1_1750 : subd9_1 [-2, -5, -12] = true := by decide +kernel
theorem subd9_1_1751 : subd9_1 [-2, -5, -11] = true := by decide +kernel
theorem subd9_1_1752 : subd9_1 [-2, -5, -10] = true := by decide +kernel
theorem subd9_1_1753 : subd9_1 [-2, -5, -9] = true := by decide +kernel
theorem subd9_1_1754 : subd9_1 [-2, -5, -8] = true := by decide +kernel
theorem subd9_1_1755 : subd9_1 [-2, -5, -7] = true := by decide +kernel
theorem subd9_1_1756 : subd9_1 [-2, -5, -6] = true := by decide +kernel
theorem subd9_1_1757 : subd9_1 [-2, -5, -5] = true := by decide +kernel
theorem subd9_1_1758 : subd9_1 [-2, -5, -4] = true := by decide +kernel
theorem subd9_1_1759 : subd9_1 [-2, -5, -3] = true := by decide +kernel
theorem sbd9_1_54 : ∀ q ∈ blkd9_1_54, subd9_1 q = true := by
  unfold blkd9_1_54
  exact List.forall_mem_cons.2 ⟨subd9_1_1728, List.forall_mem_cons.2 ⟨subd9_1_1729, List.forall_mem_cons.2 ⟨subd9_1_1730, List.forall_mem_cons.2 ⟨subd9_1_1731, List.forall_mem_cons.2 ⟨subd9_1_1732, List.forall_mem_cons.2 ⟨subd9_1_1733, List.forall_mem_cons.2 ⟨subd9_1_1734, List.forall_mem_cons.2 ⟨subd9_1_1735, List.forall_mem_cons.2 ⟨subd9_1_1736, List.forall_mem_cons.2 ⟨subd9_1_1737, List.forall_mem_cons.2 ⟨subd9_1_1738, List.forall_mem_cons.2 ⟨subd9_1_1739, List.forall_mem_cons.2 ⟨subd9_1_1740, List.forall_mem_cons.2 ⟨subd9_1_1741, List.forall_mem_cons.2 ⟨subd9_1_1742, List.forall_mem_cons.2 ⟨subd9_1_1743, List.forall_mem_cons.2 ⟨subd9_1_1744, List.forall_mem_cons.2 ⟨subd9_1_1745, List.forall_mem_cons.2 ⟨subd9_1_1746, List.forall_mem_cons.2 ⟨subd9_1_1747, List.forall_mem_cons.2 ⟨subd9_1_1748, List.forall_mem_cons.2 ⟨subd9_1_1749, List.forall_mem_cons.2 ⟨subd9_1_1750, List.forall_mem_cons.2 ⟨subd9_1_1751, List.forall_mem_cons.2 ⟨subd9_1_1752, List.forall_mem_cons.2 ⟨subd9_1_1753, List.forall_mem_cons.2 ⟨subd9_1_1754, List.forall_mem_cons.2 ⟨subd9_1_1755, List.forall_mem_cons.2 ⟨subd9_1_1756, List.forall_mem_cons.2 ⟨subd9_1_1757, List.forall_mem_cons.2 ⟨subd9_1_1758, List.forall_mem_cons.2 ⟨subd9_1_1759, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_1760 : subd9_1 [-2, -5, -2] = true := by decide +kernel
theorem subd9_1_1761 : subd9_1 [-2, -5, -1] = true := by decide +kernel
theorem subd9_1_1762 : subd9_1 [-2, -5, 0] = true := by decide +kernel
theorem subd9_1_1763 : subd9_1 [-2, -5, 1] = true := by decide +kernel
theorem subd9_1_1764 : subd9_1 [-2, -5, 2] = true := by decide +kernel
theorem subd9_1_1765 : subd9_1 [-2, -5, 3] = true := by decide +kernel
theorem subd9_1_1766 : subd9_1 [-2, -5, 4] = true := by decide +kernel
theorem subd9_1_1767 : subd9_1 [-2, -5, 5] = true := by decide +kernel
theorem subd9_1_1768 : subd9_1 [-2, -5, 6] = true := by decide +kernel
theorem subd9_1_1769 : subd9_1 [-2, -5, 7] = true := by decide +kernel
theorem subd9_1_1770 : subd9_1 [-2, -4, -12] = true := by decide +kernel
theorem subd9_1_1771 : subd9_1 [-2, -4, -11] = true := by decide +kernel
theorem subd9_1_1772 : subd9_1 [-2, -4, -10] = true := by decide +kernel
theorem subd9_1_1773 : subd9_1 [-2, -4, -9] = true := by decide +kernel
theorem subd9_1_1774 : subd9_1 [-2, -4, -8] = true := by decide +kernel
theorem subd9_1_1775 : subd9_1 [-2, -4, -7] = true := by decide +kernel
theorem subd9_1_1776 : subd9_1 [-2, -4, -6] = true := by decide +kernel
theorem subd9_1_1777 : subd9_1 [-2, -4, -5] = true := by decide +kernel
theorem subd9_1_1778 : subd9_1 [-2, -4, -4] = true := by decide +kernel
theorem subd9_1_1779 : subd9_1 [-2, -4, -3] = true := by decide +kernel
theorem subd9_1_1780 : subd9_1 [-2, -4, -2] = true := by decide +kernel
theorem subd9_1_1781 : subd9_1 [-2, -4, -1] = true := by decide +kernel
theorem subd9_1_1782 : subd9_1 [-2, -4, 0] = true := by decide +kernel
theorem subd9_1_1783 : subd9_1 [-2, -4, 1] = true := by decide +kernel
theorem subd9_1_1784 : subd9_1 [-2, -4, 2] = true := by decide +kernel
theorem subd9_1_1785 : subd9_1 [-2, -4, 3] = true := by decide +kernel
theorem subd9_1_1786 : subd9_1 [-2, -4, 4] = true := by decide +kernel
theorem subd9_1_1787 : subd9_1 [-2, -4, 5] = true := by decide +kernel
theorem subd9_1_1788 : subd9_1 [-2, -4, 6] = true := by decide +kernel
theorem subd9_1_1789 : subd9_1 [-2, -4, 7] = true := by decide +kernel
theorem subd9_1_1790 : subd9_1 [-2, -3, -12] = true := by decide +kernel
theorem subd9_1_1791 : subd9_1 [-2, -3, -11] = true := by decide +kernel
theorem sbd9_1_55 : ∀ q ∈ blkd9_1_55, subd9_1 q = true := by
  unfold blkd9_1_55
  exact List.forall_mem_cons.2 ⟨subd9_1_1760, List.forall_mem_cons.2 ⟨subd9_1_1761, List.forall_mem_cons.2 ⟨subd9_1_1762, List.forall_mem_cons.2 ⟨subd9_1_1763, List.forall_mem_cons.2 ⟨subd9_1_1764, List.forall_mem_cons.2 ⟨subd9_1_1765, List.forall_mem_cons.2 ⟨subd9_1_1766, List.forall_mem_cons.2 ⟨subd9_1_1767, List.forall_mem_cons.2 ⟨subd9_1_1768, List.forall_mem_cons.2 ⟨subd9_1_1769, List.forall_mem_cons.2 ⟨subd9_1_1770, List.forall_mem_cons.2 ⟨subd9_1_1771, List.forall_mem_cons.2 ⟨subd9_1_1772, List.forall_mem_cons.2 ⟨subd9_1_1773, List.forall_mem_cons.2 ⟨subd9_1_1774, List.forall_mem_cons.2 ⟨subd9_1_1775, List.forall_mem_cons.2 ⟨subd9_1_1776, List.forall_mem_cons.2 ⟨subd9_1_1777, List.forall_mem_cons.2 ⟨subd9_1_1778, List.forall_mem_cons.2 ⟨subd9_1_1779, List.forall_mem_cons.2 ⟨subd9_1_1780, List.forall_mem_cons.2 ⟨subd9_1_1781, List.forall_mem_cons.2 ⟨subd9_1_1782, List.forall_mem_cons.2 ⟨subd9_1_1783, List.forall_mem_cons.2 ⟨subd9_1_1784, List.forall_mem_cons.2 ⟨subd9_1_1785, List.forall_mem_cons.2 ⟨subd9_1_1786, List.forall_mem_cons.2 ⟨subd9_1_1787, List.forall_mem_cons.2 ⟨subd9_1_1788, List.forall_mem_cons.2 ⟨subd9_1_1789, List.forall_mem_cons.2 ⟨subd9_1_1790, List.forall_mem_cons.2 ⟨subd9_1_1791, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C116
