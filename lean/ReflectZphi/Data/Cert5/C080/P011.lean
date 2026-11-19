import ReflectZphi.Data.Cert5.C080.Base

namespace ReflectZphi.Data.Cert5.C080
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub7_1344 : sub7 [3, -2, 6] = true := by decide +kernel
theorem sub7_1345 : sub7 [3, -2, 7] = true := by decide +kernel
theorem sub7_1346 : sub7 [3, -2, 8] = true := by decide +kernel
theorem sub7_1347 : sub7 [3, -2, 9] = true := by decide +kernel
theorem sub7_1348 : sub7 [3, -2, 10] = true := by decide +kernel
theorem sub7_1349 : sub7 [3, -1, -11] = true := by decide +kernel
theorem sub7_1350 : sub7 [3, -1, -10] = true := by decide +kernel
theorem sub7_1351 : sub7 [3, -1, -9] = true := by decide +kernel
theorem sub7_1352 : sub7 [3, -1, -8] = true := by decide +kernel
theorem sub7_1353 : sub7 [3, -1, -7] = true := by decide +kernel
theorem sub7_1354 : sub7 [3, -1, -6] = true := by decide +kernel
theorem sub7_1355 : sub7 [3, -1, -5] = true := by decide +kernel
theorem sub7_1356 : sub7 [3, -1, -4] = true := by decide +kernel
theorem sub7_1357 : sub7 [3, -1, -3] = true := by decide +kernel
theorem sub7_1358 : sub7 [3, -1, -2] = true := by decide +kernel
theorem sub7_1359 : sub7 [3, -1, -1] = true := by decide +kernel
theorem sub7_1360 : sub7 [3, -1, 0] = true := by decide +kernel
theorem sub7_1361 : sub7 [3, -1, 1] = true := by decide +kernel
theorem sub7_1362 : sub7 [3, -1, 2] = true := by decide +kernel
theorem sub7_1363 : sub7 [3, -1, 3] = true := by decide +kernel
theorem sub7_1364 : sub7 [3, -1, 4] = true := by decide +kernel
theorem sub7_1365 : sub7 [3, -1, 5] = true := by decide +kernel
theorem sub7_1366 : sub7 [3, -1, 6] = true := by decide +kernel
theorem sub7_1367 : sub7 [3, -1, 7] = true := by decide +kernel
theorem sub7_1368 : sub7 [3, -1, 8] = true := by decide +kernel
theorem sub7_1369 : sub7 [3, -1, 9] = true := by decide +kernel
theorem sub7_1370 : sub7 [3, -1, 10] = true := by decide +kernel
theorem sub7_1371 : sub7 [3, -1, 11] = true := by decide +kernel
theorem sub7_1372 : sub7 [3, 0, -11] = true := by decide +kernel
theorem sub7_1373 : sub7 [3, 0, -10] = true := by decide +kernel
theorem sub7_1374 : sub7 [3, 0, -9] = true := by decide +kernel
theorem sub7_1375 : sub7 [3, 0, -8] = true := by decide +kernel
theorem sb7_42 : ∀ q ∈ blk7_42, sub7 q = true := by
  unfold blk7_42
  exact List.forall_mem_cons.2 ⟨sub7_1344, List.forall_mem_cons.2 ⟨sub7_1345, List.forall_mem_cons.2 ⟨sub7_1346, List.forall_mem_cons.2 ⟨sub7_1347, List.forall_mem_cons.2 ⟨sub7_1348, List.forall_mem_cons.2 ⟨sub7_1349, List.forall_mem_cons.2 ⟨sub7_1350, List.forall_mem_cons.2 ⟨sub7_1351, List.forall_mem_cons.2 ⟨sub7_1352, List.forall_mem_cons.2 ⟨sub7_1353, List.forall_mem_cons.2 ⟨sub7_1354, List.forall_mem_cons.2 ⟨sub7_1355, List.forall_mem_cons.2 ⟨sub7_1356, List.forall_mem_cons.2 ⟨sub7_1357, List.forall_mem_cons.2 ⟨sub7_1358, List.forall_mem_cons.2 ⟨sub7_1359, List.forall_mem_cons.2 ⟨sub7_1360, List.forall_mem_cons.2 ⟨sub7_1361, List.forall_mem_cons.2 ⟨sub7_1362, List.forall_mem_cons.2 ⟨sub7_1363, List.forall_mem_cons.2 ⟨sub7_1364, List.forall_mem_cons.2 ⟨sub7_1365, List.forall_mem_cons.2 ⟨sub7_1366, List.forall_mem_cons.2 ⟨sub7_1367, List.forall_mem_cons.2 ⟨sub7_1368, List.forall_mem_cons.2 ⟨sub7_1369, List.forall_mem_cons.2 ⟨sub7_1370, List.forall_mem_cons.2 ⟨sub7_1371, List.forall_mem_cons.2 ⟨sub7_1372, List.forall_mem_cons.2 ⟨sub7_1373, List.forall_mem_cons.2 ⟨sub7_1374, List.forall_mem_cons.2 ⟨sub7_1375, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_1376 : sub7 [3, 0, -7] = true := by decide +kernel
theorem sub7_1377 : sub7 [3, 0, -6] = true := by decide +kernel
theorem sub7_1378 : sub7 [3, 0, -5] = true := by decide +kernel
theorem sub7_1379 : sub7 [3, 0, -4] = true := by decide +kernel
theorem sub7_1380 : sub7 [3, 0, -3] = true := by decide +kernel
theorem sub7_1381 : sub7 [3, 0, -2] = true := by decide +kernel
theorem sub7_1382 : sub7 [3, 0, -1] = true := by decide +kernel
theorem sub7_1383 : sub7 [3, 0, 0] = true := by decide +kernel
theorem sub7_1384 : sub7 [3, 0, 1] = true := by decide +kernel
theorem sub7_1385 : sub7 [3, 0, 2] = true := by decide +kernel
theorem sub7_1386 : sub7 [3, 0, 3] = true := by decide +kernel
theorem sub7_1387 : sub7 [3, 0, 4] = true := by decide +kernel
theorem sub7_1388 : sub7 [3, 0, 5] = true := by decide +kernel
theorem sub7_1389 : sub7 [3, 0, 6] = true := by decide +kernel
theorem sub7_1390 : sub7 [3, 0, 7] = true := by decide +kernel
theorem sub7_1391 : sub7 [3, 0, 8] = true := by decide +kernel
theorem sub7_1392 : sub7 [3, 0, 9] = true := by decide +kernel
theorem sub7_1393 : sub7 [3, 0, 10] = true := by decide +kernel
theorem sub7_1394 : sub7 [3, 0, 11] = true := by decide +kernel
theorem sub7_1395 : sub7 [3, 1, -11] = true := by decide +kernel
theorem sub7_1396 : sub7 [3, 1, -10] = true := by decide +kernel
theorem sub7_1397 : sub7 [3, 1, -9] = true := by decide +kernel
theorem sub7_1398 : sub7 [3, 1, -8] = true := by decide +kernel
theorem sub7_1399 : sub7 [3, 1, -7] = true := by decide +kernel
theorem sub7_1400 : sub7 [3, 1, -6] = true := by decide +kernel
theorem sub7_1401 : sub7 [3, 1, -5] = true := by decide +kernel
theorem sub7_1402 : sub7 [3, 1, -4] = true := by decide +kernel
theorem sub7_1403 : sub7 [3, 1, -3] = true := by decide +kernel
theorem sub7_1404 : sub7 [3, 1, -2] = true := by decide +kernel
theorem sub7_1405 : sub7 [3, 1, -1] = true := by decide +kernel
theorem sub7_1406 : sub7 [3, 1, 0] = true := by decide +kernel
theorem sub7_1407 : sub7 [3, 1, 1] = true := by decide +kernel
theorem sb7_43 : ∀ q ∈ blk7_43, sub7 q = true := by
  unfold blk7_43
  exact List.forall_mem_cons.2 ⟨sub7_1376, List.forall_mem_cons.2 ⟨sub7_1377, List.forall_mem_cons.2 ⟨sub7_1378, List.forall_mem_cons.2 ⟨sub7_1379, List.forall_mem_cons.2 ⟨sub7_1380, List.forall_mem_cons.2 ⟨sub7_1381, List.forall_mem_cons.2 ⟨sub7_1382, List.forall_mem_cons.2 ⟨sub7_1383, List.forall_mem_cons.2 ⟨sub7_1384, List.forall_mem_cons.2 ⟨sub7_1385, List.forall_mem_cons.2 ⟨sub7_1386, List.forall_mem_cons.2 ⟨sub7_1387, List.forall_mem_cons.2 ⟨sub7_1388, List.forall_mem_cons.2 ⟨sub7_1389, List.forall_mem_cons.2 ⟨sub7_1390, List.forall_mem_cons.2 ⟨sub7_1391, List.forall_mem_cons.2 ⟨sub7_1392, List.forall_mem_cons.2 ⟨sub7_1393, List.forall_mem_cons.2 ⟨sub7_1394, List.forall_mem_cons.2 ⟨sub7_1395, List.forall_mem_cons.2 ⟨sub7_1396, List.forall_mem_cons.2 ⟨sub7_1397, List.forall_mem_cons.2 ⟨sub7_1398, List.forall_mem_cons.2 ⟨sub7_1399, List.forall_mem_cons.2 ⟨sub7_1400, List.forall_mem_cons.2 ⟨sub7_1401, List.forall_mem_cons.2 ⟨sub7_1402, List.forall_mem_cons.2 ⟨sub7_1403, List.forall_mem_cons.2 ⟨sub7_1404, List.forall_mem_cons.2 ⟨sub7_1405, List.forall_mem_cons.2 ⟨sub7_1406, List.forall_mem_cons.2 ⟨sub7_1407, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_1408 : sub7 [3, 1, 2] = true := by decide +kernel
theorem sub7_1409 : sub7 [3, 1, 3] = true := by decide +kernel
theorem sub7_1410 : sub7 [3, 1, 4] = true := by decide +kernel
theorem sub7_1411 : sub7 [3, 1, 5] = true := by decide +kernel
theorem sub7_1412 : sub7 [3, 1, 6] = true := by decide +kernel
theorem sub7_1413 : sub7 [3, 1, 7] = true := by decide +kernel
theorem sub7_1414 : sub7 [3, 1, 8] = true := by decide +kernel
theorem sub7_1415 : sub7 [3, 1, 9] = true := by decide +kernel
theorem sub7_1416 : sub7 [3, 1, 10] = true := by decide +kernel
theorem sub7_1417 : sub7 [3, 2, -9] = true := by decide +kernel
theorem sub7_1418 : sub7 [3, 2, -8] = true := by decide +kernel
theorem sub7_1419 : sub7 [3, 2, -7] = true := by decide +kernel
theorem sub7_1420 : sub7 [3, 2, -6] = true := by decide +kernel
theorem sub7_1421 : sub7 [3, 2, -5] = true := by decide +kernel
theorem sub7_1422 : sub7 [3, 2, -4] = true := by decide +kernel
theorem sub7_1423 : sub7 [3, 2, -3] = true := by decide +kernel
theorem sub7_1424 : sub7 [3, 2, -2] = true := by decide +kernel
theorem sub7_1425 : sub7 [3, 2, -1] = true := by decide +kernel
theorem sub7_1426 : sub7 [3, 2, 0] = true := by decide +kernel
theorem sub7_1427 : sub7 [3, 2, 1] = true := by decide +kernel
theorem sub7_1428 : sub7 [3, 2, 2] = true := by decide +kernel
theorem sub7_1429 : sub7 [3, 2, 3] = true := by decide +kernel
theorem sub7_1430 : sub7 [3, 2, 4] = true := by decide +kernel
theorem sub7_1431 : sub7 [3, 2, 5] = true := by decide +kernel
theorem sub7_1432 : sub7 [3, 2, 6] = true := by decide +kernel
theorem sub7_1433 : sub7 [3, 2, 7] = true := by decide +kernel
theorem sub7_1434 : sub7 [3, 2, 8] = true := by decide +kernel
theorem sub7_1435 : sub7 [3, 2, 9] = true := by decide +kernel
theorem sub7_1436 : sub7 [3, 3, -7] = true := by decide +kernel
theorem sub7_1437 : sub7 [3, 3, -6] = true := by decide +kernel
theorem sub7_1438 : sub7 [3, 3, -5] = true := by decide +kernel
theorem sub7_1439 : sub7 [3, 3, -4] = true := by decide +kernel
theorem sb7_44 : ∀ q ∈ blk7_44, sub7 q = true := by
  unfold blk7_44
  exact List.forall_mem_cons.2 ⟨sub7_1408, List.forall_mem_cons.2 ⟨sub7_1409, List.forall_mem_cons.2 ⟨sub7_1410, List.forall_mem_cons.2 ⟨sub7_1411, List.forall_mem_cons.2 ⟨sub7_1412, List.forall_mem_cons.2 ⟨sub7_1413, List.forall_mem_cons.2 ⟨sub7_1414, List.forall_mem_cons.2 ⟨sub7_1415, List.forall_mem_cons.2 ⟨sub7_1416, List.forall_mem_cons.2 ⟨sub7_1417, List.forall_mem_cons.2 ⟨sub7_1418, List.forall_mem_cons.2 ⟨sub7_1419, List.forall_mem_cons.2 ⟨sub7_1420, List.forall_mem_cons.2 ⟨sub7_1421, List.forall_mem_cons.2 ⟨sub7_1422, List.forall_mem_cons.2 ⟨sub7_1423, List.forall_mem_cons.2 ⟨sub7_1424, List.forall_mem_cons.2 ⟨sub7_1425, List.forall_mem_cons.2 ⟨sub7_1426, List.forall_mem_cons.2 ⟨sub7_1427, List.forall_mem_cons.2 ⟨sub7_1428, List.forall_mem_cons.2 ⟨sub7_1429, List.forall_mem_cons.2 ⟨sub7_1430, List.forall_mem_cons.2 ⟨sub7_1431, List.forall_mem_cons.2 ⟨sub7_1432, List.forall_mem_cons.2 ⟨sub7_1433, List.forall_mem_cons.2 ⟨sub7_1434, List.forall_mem_cons.2 ⟨sub7_1435, List.forall_mem_cons.2 ⟨sub7_1436, List.forall_mem_cons.2 ⟨sub7_1437, List.forall_mem_cons.2 ⟨sub7_1438, List.forall_mem_cons.2 ⟨sub7_1439, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_1440 : sub7 [3, 3, -3] = true := by decide +kernel
theorem sub7_1441 : sub7 [3, 3, -2] = true := by decide +kernel
theorem sub7_1442 : sub7 [3, 3, -1] = true := by decide +kernel
theorem sub7_1443 : sub7 [3, 3, 0] = true := by decide +kernel
theorem sub7_1444 : sub7 [3, 3, 1] = true := by decide +kernel
theorem sub7_1445 : sub7 [3, 3, 2] = true := by decide +kernel
theorem sub7_1446 : sub7 [3, 3, 3] = true := by decide +kernel
theorem sub7_1447 : sub7 [3, 3, 4] = true := by decide +kernel
theorem sub7_1448 : sub7 [3, 3, 5] = true := by decide +kernel
theorem sub7_1449 : sub7 [3, 3, 6] = true := by decide +kernel
theorem sub7_1450 : sub7 [3, 3, 7] = true := by decide +kernel
theorem sub7_1451 : sub7 [4, -5] = true := by decide +kernel
theorem sub7_1452 : sub7 [4, -4] = true := by decide +kernel
theorem sub7_1453 : sub7 [4, -3] = true := by decide +kernel
theorem sub7_1454 : sub7 [4, -2, -8] = true := by decide +kernel
theorem sub7_1455 : sub7 [4, -2, -7] = true := by decide +kernel
theorem sub7_1456 : sub7 [4, -2, -6] = true := by decide +kernel
theorem sub7_1457 : sub7 [4, -2, -5] = true := by decide +kernel
theorem sub7_1458 : sub7 [4, -2, -4] = true := by decide +kernel
theorem sub7_1459 : sub7 [4, -2, -3] = true := by decide +kernel
theorem sub7_1460 : sub7 [4, -2, -2] = true := by decide +kernel
theorem sub7_1461 : sub7 [4, -2, -1] = true := by decide +kernel
theorem sub7_1462 : sub7 [4, -2, 0] = true := by decide +kernel
theorem sub7_1463 : sub7 [4, -2, 1] = true := by decide +kernel
theorem sub7_1464 : sub7 [4, -2, 2] = true := by decide +kernel
theorem sub7_1465 : sub7 [4, -2, 3] = true := by decide +kernel
theorem sub7_1466 : sub7 [4, -2, 4] = true := by decide +kernel
theorem sub7_1467 : sub7 [4, -2, 5] = true := by decide +kernel
theorem sub7_1468 : sub7 [4, -2, 6] = true := by decide +kernel
theorem sub7_1469 : sub7 [4, -2, 7] = true := by decide +kernel
theorem sub7_1470 : sub7 [4, -1, -9] = true := by decide +kernel
theorem sub7_1471 : sub7 [4, -1, -8] = true := by decide +kernel
theorem sb7_45 : ∀ q ∈ blk7_45, sub7 q = true := by
  unfold blk7_45
  exact List.forall_mem_cons.2 ⟨sub7_1440, List.forall_mem_cons.2 ⟨sub7_1441, List.forall_mem_cons.2 ⟨sub7_1442, List.forall_mem_cons.2 ⟨sub7_1443, List.forall_mem_cons.2 ⟨sub7_1444, List.forall_mem_cons.2 ⟨sub7_1445, List.forall_mem_cons.2 ⟨sub7_1446, List.forall_mem_cons.2 ⟨sub7_1447, List.forall_mem_cons.2 ⟨sub7_1448, List.forall_mem_cons.2 ⟨sub7_1449, List.forall_mem_cons.2 ⟨sub7_1450, List.forall_mem_cons.2 ⟨sub7_1451, List.forall_mem_cons.2 ⟨sub7_1452, List.forall_mem_cons.2 ⟨sub7_1453, List.forall_mem_cons.2 ⟨sub7_1454, List.forall_mem_cons.2 ⟨sub7_1455, List.forall_mem_cons.2 ⟨sub7_1456, List.forall_mem_cons.2 ⟨sub7_1457, List.forall_mem_cons.2 ⟨sub7_1458, List.forall_mem_cons.2 ⟨sub7_1459, List.forall_mem_cons.2 ⟨sub7_1460, List.forall_mem_cons.2 ⟨sub7_1461, List.forall_mem_cons.2 ⟨sub7_1462, List.forall_mem_cons.2 ⟨sub7_1463, List.forall_mem_cons.2 ⟨sub7_1464, List.forall_mem_cons.2 ⟨sub7_1465, List.forall_mem_cons.2 ⟨sub7_1466, List.forall_mem_cons.2 ⟨sub7_1467, List.forall_mem_cons.2 ⟨sub7_1468, List.forall_mem_cons.2 ⟨sub7_1469, List.forall_mem_cons.2 ⟨sub7_1470, List.forall_mem_cons.2 ⟨sub7_1471, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_1472 : sub7 [4, -1, -7] = true := by decide +kernel
theorem sub7_1473 : sub7 [4, -1, -6] = true := by decide +kernel
theorem sub7_1474 : sub7 [4, -1, -5] = true := by decide +kernel
theorem sub7_1475 : sub7 [4, -1, -4] = true := by decide +kernel
theorem sub7_1476 : sub7 [4, -1, -3] = true := by decide +kernel
theorem sub7_1477 : sub7 [4, -1, -2] = true := by decide +kernel
theorem sub7_1478 : sub7 [4, -1, -1] = true := by decide +kernel
theorem sub7_1479 : sub7 [4, -1, 0] = true := by decide +kernel
theorem sub7_1480 : sub7 [4, -1, 1] = true := by decide +kernel
theorem sub7_1481 : sub7 [4, -1, 2] = true := by decide +kernel
theorem sub7_1482 : sub7 [4, -1, 3] = true := by decide +kernel
theorem sub7_1483 : sub7 [4, -1, 4] = true := by decide +kernel
theorem sub7_1484 : sub7 [4, -1, 5] = true := by decide +kernel
theorem sub7_1485 : sub7 [4, -1, 6] = true := by decide +kernel
theorem sub7_1486 : sub7 [4, -1, 7] = true := by decide +kernel
theorem sub7_1487 : sub7 [4, -1, 8] = true := by decide +kernel
theorem sub7_1488 : sub7 [4, 0, -8] = true := by decide +kernel
theorem sub7_1489 : sub7 [4, 0, -7] = true := by decide +kernel
theorem sub7_1490 : sub7 [4, 0, -6] = true := by decide +kernel
theorem sub7_1491 : sub7 [4, 0, -5] = true := by decide +kernel
theorem sub7_1492 : sub7 [4, 0, -4] = true := by decide +kernel
theorem sub7_1493 : sub7 [4, 0, -3] = true := by decide +kernel
theorem sub7_1494 : sub7 [4, 0, -2] = true := by decide +kernel
theorem sub7_1495 : sub7 [4, 0, -1] = true := by decide +kernel
theorem sub7_1496 : sub7 [4, 0, 0] = true := by decide +kernel
theorem sub7_1497 : sub7 [4, 0, 1] = true := by decide +kernel
theorem sub7_1498 : sub7 [4, 0, 2] = true := by decide +kernel
theorem sub7_1499 : sub7 [4, 0, 3] = true := by decide +kernel
theorem sub7_1500 : sub7 [4, 0, 4] = true := by decide +kernel
theorem sub7_1501 : sub7 [4, 0, 5] = true := by decide +kernel
theorem sub7_1502 : sub7 [4, 0, 6] = true := by decide +kernel
theorem sub7_1503 : sub7 [4, 0, 7] = true := by decide +kernel
theorem sb7_46 : ∀ q ∈ blk7_46, sub7 q = true := by
  unfold blk7_46
  exact List.forall_mem_cons.2 ⟨sub7_1472, List.forall_mem_cons.2 ⟨sub7_1473, List.forall_mem_cons.2 ⟨sub7_1474, List.forall_mem_cons.2 ⟨sub7_1475, List.forall_mem_cons.2 ⟨sub7_1476, List.forall_mem_cons.2 ⟨sub7_1477, List.forall_mem_cons.2 ⟨sub7_1478, List.forall_mem_cons.2 ⟨sub7_1479, List.forall_mem_cons.2 ⟨sub7_1480, List.forall_mem_cons.2 ⟨sub7_1481, List.forall_mem_cons.2 ⟨sub7_1482, List.forall_mem_cons.2 ⟨sub7_1483, List.forall_mem_cons.2 ⟨sub7_1484, List.forall_mem_cons.2 ⟨sub7_1485, List.forall_mem_cons.2 ⟨sub7_1486, List.forall_mem_cons.2 ⟨sub7_1487, List.forall_mem_cons.2 ⟨sub7_1488, List.forall_mem_cons.2 ⟨sub7_1489, List.forall_mem_cons.2 ⟨sub7_1490, List.forall_mem_cons.2 ⟨sub7_1491, List.forall_mem_cons.2 ⟨sub7_1492, List.forall_mem_cons.2 ⟨sub7_1493, List.forall_mem_cons.2 ⟨sub7_1494, List.forall_mem_cons.2 ⟨sub7_1495, List.forall_mem_cons.2 ⟨sub7_1496, List.forall_mem_cons.2 ⟨sub7_1497, List.forall_mem_cons.2 ⟨sub7_1498, List.forall_mem_cons.2 ⟨sub7_1499, List.forall_mem_cons.2 ⟨sub7_1500, List.forall_mem_cons.2 ⟨sub7_1501, List.forall_mem_cons.2 ⟨sub7_1502, List.forall_mem_cons.2 ⟨sub7_1503, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_1504 : sub7 [4, 0, 8] = true := by decide +kernel
theorem sub7_1505 : sub7 [4, 1, -8] = true := by decide +kernel
theorem sub7_1506 : sub7 [4, 1, -7] = true := by decide +kernel
theorem sub7_1507 : sub7 [4, 1, -6] = true := by decide +kernel
theorem sub7_1508 : sub7 [4, 1, -5] = true := by decide +kernel
theorem sub7_1509 : sub7 [4, 1, -4] = true := by decide +kernel
theorem sub7_1510 : sub7 [4, 1, -3] = true := by decide +kernel
theorem sub7_1511 : sub7 [4, 1, -2] = true := by decide +kernel
theorem sub7_1512 : sub7 [4, 1, -1] = true := by decide +kernel
theorem sub7_1513 : sub7 [4, 1, 0] = true := by decide +kernel
theorem sub7_1514 : sub7 [4, 1, 1] = true := by decide +kernel
theorem sub7_1515 : sub7 [4, 1, 2] = true := by decide +kernel
theorem sub7_1516 : sub7 [4, 1, 3] = true := by decide +kernel
theorem sub7_1517 : sub7 [4, 1, 4] = true := by decide +kernel
theorem sub7_1518 : sub7 [4, 1, 5] = true := by decide +kernel
theorem sub7_1519 : sub7 [4, 1, 6] = true := by decide +kernel
theorem sub7_1520 : sub7 [4, 1, 7] = true := by decide +kernel
theorem sub7_1521 : sub7 [4, 2] = true := by decide +kernel
theorem sub7_1522 : sub7 [5] = true := by decide +kernel
theorem sb7_47 : ∀ q ∈ blk7_47, sub7 q = true := by
  unfold blk7_47
  exact List.forall_mem_cons.2 ⟨sub7_1504, List.forall_mem_cons.2 ⟨sub7_1505, List.forall_mem_cons.2 ⟨sub7_1506, List.forall_mem_cons.2 ⟨sub7_1507, List.forall_mem_cons.2 ⟨sub7_1508, List.forall_mem_cons.2 ⟨sub7_1509, List.forall_mem_cons.2 ⟨sub7_1510, List.forall_mem_cons.2 ⟨sub7_1511, List.forall_mem_cons.2 ⟨sub7_1512, List.forall_mem_cons.2 ⟨sub7_1513, List.forall_mem_cons.2 ⟨sub7_1514, List.forall_mem_cons.2 ⟨sub7_1515, List.forall_mem_cons.2 ⟨sub7_1516, List.forall_mem_cons.2 ⟨sub7_1517, List.forall_mem_cons.2 ⟨sub7_1518, List.forall_mem_cons.2 ⟨sub7_1519, List.forall_mem_cons.2 ⟨sub7_1520, List.forall_mem_cons.2 ⟨sub7_1521, List.forall_mem_cons.2 ⟨sub7_1522, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_0 : sub8 [-6, -4] = true := by decide +kernel
theorem sub8_1 : sub8 [-6, -3] = true := by decide +kernel
theorem sub8_2 : sub8 [-6, -2] = true := by decide +kernel
theorem sub8_3 : sub8 [-6, -1] = true := by decide +kernel
theorem sub8_4 : sub8 [-6, 0] = true := by decide +kernel
theorem sub8_5 : sub8 [-6, 1] = true := by decide +kernel
theorem sub8_6 : sub8 [-5, -6] = true := by decide +kernel
theorem sub8_7 : sub8 [-5, -5] = true := by decide +kernel
theorem sub8_8 : sub8 [-5, -4] = true := by decide +kernel
theorem sub8_9 : sub8 [-5, -3] = true := by decide +kernel
theorem sub8_10 : sub8 [-5, -2, -5] = true := by decide +kernel
theorem sub8_11 : sub8 [-5, -2, -4] = true := by decide +kernel
theorem sub8_12 : sub8 [-5, -2, -3] = true := by decide +kernel
theorem sub8_13 : sub8 [-5, -2, -2] = true := by decide +kernel
theorem sub8_14 : sub8 [-5, -2, -1] = true := by decide +kernel
theorem sub8_15 : sub8 [-5, -2, 0] = true := by decide +kernel
theorem sub8_16 : sub8 [-5, -2, 1] = true := by decide +kernel
theorem sub8_17 : sub8 [-5, -2, 2] = true := by decide +kernel
theorem sub8_18 : sub8 [-5, -2, 3] = true := by decide +kernel
theorem sub8_19 : sub8 [-5, -2, 4] = true := by decide +kernel
theorem sub8_20 : sub8 [-5, -2, 5] = true := by decide +kernel
theorem sub8_21 : sub8 [-5, -2, 6] = true := by decide +kernel
theorem sub8_22 : sub8 [-5, -2, 7] = true := by decide +kernel
theorem sub8_23 : sub8 [-5, -2, 8] = true := by decide +kernel
theorem sub8_24 : sub8 [-5, -1, -5] = true := by decide +kernel
theorem sub8_25 : sub8 [-5, -1, -4] = true := by decide +kernel
theorem sub8_26 : sub8 [-5, -1, -3] = true := by decide +kernel
theorem sub8_27 : sub8 [-5, -1, -2] = true := by decide +kernel
theorem sub8_28 : sub8 [-5, -1, -1] = true := by decide +kernel
theorem sub8_29 : sub8 [-5, -1, 0] = true := by decide +kernel
theorem sub8_30 : sub8 [-5, -1, 1] = true := by decide +kernel
theorem sub8_31 : sub8 [-5, -1, 2] = true := by decide +kernel
theorem sb8_0 : ∀ q ∈ blk8_0, sub8 q = true := by
  unfold blk8_0
  exact List.forall_mem_cons.2 ⟨sub8_0, List.forall_mem_cons.2 ⟨sub8_1, List.forall_mem_cons.2 ⟨sub8_2, List.forall_mem_cons.2 ⟨sub8_3, List.forall_mem_cons.2 ⟨sub8_4, List.forall_mem_cons.2 ⟨sub8_5, List.forall_mem_cons.2 ⟨sub8_6, List.forall_mem_cons.2 ⟨sub8_7, List.forall_mem_cons.2 ⟨sub8_8, List.forall_mem_cons.2 ⟨sub8_9, List.forall_mem_cons.2 ⟨sub8_10, List.forall_mem_cons.2 ⟨sub8_11, List.forall_mem_cons.2 ⟨sub8_12, List.forall_mem_cons.2 ⟨sub8_13, List.forall_mem_cons.2 ⟨sub8_14, List.forall_mem_cons.2 ⟨sub8_15, List.forall_mem_cons.2 ⟨sub8_16, List.forall_mem_cons.2 ⟨sub8_17, List.forall_mem_cons.2 ⟨sub8_18, List.forall_mem_cons.2 ⟨sub8_19, List.forall_mem_cons.2 ⟨sub8_20, List.forall_mem_cons.2 ⟨sub8_21, List.forall_mem_cons.2 ⟨sub8_22, List.forall_mem_cons.2 ⟨sub8_23, List.forall_mem_cons.2 ⟨sub8_24, List.forall_mem_cons.2 ⟨sub8_25, List.forall_mem_cons.2 ⟨sub8_26, List.forall_mem_cons.2 ⟨sub8_27, List.forall_mem_cons.2 ⟨sub8_28, List.forall_mem_cons.2 ⟨sub8_29, List.forall_mem_cons.2 ⟨sub8_30, List.forall_mem_cons.2 ⟨sub8_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_32 : sub8 [-5, -1, 3] = true := by decide +kernel
theorem sub8_33 : sub8 [-5, -1, 4] = true := by decide +kernel
theorem sub8_34 : sub8 [-5, -1, 5] = true := by decide +kernel
theorem sub8_35 : sub8 [-5, -1, 6] = true := by decide +kernel
theorem sub8_36 : sub8 [-5, -1, 7] = true := by decide +kernel
theorem sub8_37 : sub8 [-5, -1, 8] = true := by decide +kernel
theorem sub8_38 : sub8 [-5, 0, -5] = true := by decide +kernel
theorem sub8_39 : sub8 [-5, 0, -4] = true := by decide +kernel
theorem sub8_40 : sub8 [-5, 0, -3] = true := by decide +kernel
theorem sub8_41 : sub8 [-5, 0, -2] = true := by decide +kernel
theorem sub8_42 : sub8 [-5, 0, -1] = true := by decide +kernel
theorem sub8_43 : sub8 [-5, 0, 0] = true := by decide +kernel
theorem sub8_44 : sub8 [-5, 0, 1] = true := by decide +kernel
theorem sub8_45 : sub8 [-5, 0, 2] = true := by decide +kernel
theorem sub8_46 : sub8 [-5, 0, 3] = true := by decide +kernel
theorem sub8_47 : sub8 [-5, 0, 4] = true := by decide +kernel
theorem sub8_48 : sub8 [-5, 0, 5] = true := by decide +kernel
theorem sub8_49 : sub8 [-5, 0, 6] = true := by decide +kernel
theorem sub8_50 : sub8 [-5, 0, 7] = true := by decide +kernel
theorem sub8_51 : sub8 [-5, 0, 8] = true := by decide +kernel
theorem sub8_52 : sub8 [-5, 1] = true := by decide +kernel
theorem sub8_53 : sub8 [-5, 2] = true := by decide +kernel
theorem sub8_54 : sub8 [-5, 3] = true := by decide +kernel
theorem sub8_55 : sub8 [-4, -6] = true := by decide +kernel
theorem sub8_56 : sub8 [-4, -5] = true := by decide +kernel
theorem sub8_57 : sub8 [-4, -4] = true := by decide +kernel
theorem sub8_58 : sub8 [-4, -3, -6] = true := by decide +kernel
theorem sub8_59 : sub8 [-4, -3, -5] = true := by decide +kernel
theorem sub8_60 : sub8 [-4, -3, -4] = true := by decide +kernel
theorem sub8_61 : sub8 [-4, -3, -3] = true := by decide +kernel
theorem sub8_62 : sub8 [-4, -3, -2] = true := by decide +kernel
theorem sub8_63 : sub8 [-4, -3, -1] = true := by decide +kernel
theorem sb8_1 : ∀ q ∈ blk8_1, sub8 q = true := by
  unfold blk8_1
  exact List.forall_mem_cons.2 ⟨sub8_32, List.forall_mem_cons.2 ⟨sub8_33, List.forall_mem_cons.2 ⟨sub8_34, List.forall_mem_cons.2 ⟨sub8_35, List.forall_mem_cons.2 ⟨sub8_36, List.forall_mem_cons.2 ⟨sub8_37, List.forall_mem_cons.2 ⟨sub8_38, List.forall_mem_cons.2 ⟨sub8_39, List.forall_mem_cons.2 ⟨sub8_40, List.forall_mem_cons.2 ⟨sub8_41, List.forall_mem_cons.2 ⟨sub8_42, List.forall_mem_cons.2 ⟨sub8_43, List.forall_mem_cons.2 ⟨sub8_44, List.forall_mem_cons.2 ⟨sub8_45, List.forall_mem_cons.2 ⟨sub8_46, List.forall_mem_cons.2 ⟨sub8_47, List.forall_mem_cons.2 ⟨sub8_48, List.forall_mem_cons.2 ⟨sub8_49, List.forall_mem_cons.2 ⟨sub8_50, List.forall_mem_cons.2 ⟨sub8_51, List.forall_mem_cons.2 ⟨sub8_52, List.forall_mem_cons.2 ⟨sub8_53, List.forall_mem_cons.2 ⟨sub8_54, List.forall_mem_cons.2 ⟨sub8_55, List.forall_mem_cons.2 ⟨sub8_56, List.forall_mem_cons.2 ⟨sub8_57, List.forall_mem_cons.2 ⟨sub8_58, List.forall_mem_cons.2 ⟨sub8_59, List.forall_mem_cons.2 ⟨sub8_60, List.forall_mem_cons.2 ⟨sub8_61, List.forall_mem_cons.2 ⟨sub8_62, List.forall_mem_cons.2 ⟨sub8_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_64 : sub8 [-4, -3, 0] = true := by decide +kernel
theorem sub8_65 : sub8 [-4, -3, 1] = true := by decide +kernel
theorem sub8_66 : sub8 [-4, -3, 2] = true := by decide +kernel
theorem sub8_67 : sub8 [-4, -3, 3] = true := by decide +kernel
theorem sub8_68 : sub8 [-4, -3, 4] = true := by decide +kernel
theorem sub8_69 : sub8 [-4, -3, 5] = true := by decide +kernel
theorem sub8_70 : sub8 [-4, -3, 6] = true := by decide +kernel
theorem sub8_71 : sub8 [-4, -3, 7] = true := by decide +kernel
theorem sub8_72 : sub8 [-4, -3, 8] = true := by decide +kernel
theorem sub8_73 : sub8 [-4, -2, -6] = true := by decide +kernel
theorem sub8_74 : sub8 [-4, -2, -5] = true := by decide +kernel
theorem sub8_75 : sub8 [-4, -2, -4] = true := by decide +kernel
theorem sub8_76 : sub8 [-4, -2, -3] = true := by decide +kernel
theorem sub8_77 : sub8 [-4, -2, -2] = true := by decide +kernel
theorem sub8_78 : sub8 [-4, -2, -1] = true := by decide +kernel
theorem sub8_79 : sub8 [-4, -2, 0] = true := by decide +kernel
theorem sub8_80 : sub8 [-4, -2, 1] = true := by decide +kernel
theorem sub8_81 : sub8 [-4, -2, 2] = true := by decide +kernel
theorem sub8_82 : sub8 [-4, -2, 3] = true := by decide +kernel
theorem sub8_83 : sub8 [-4, -2, 4] = true := by decide +kernel
theorem sub8_84 : sub8 [-4, -2, 5] = true := by decide +kernel
theorem sub8_85 : sub8 [-4, -2, 6] = true := by decide +kernel
theorem sub8_86 : sub8 [-4, -2, 7] = true := by decide +kernel
theorem sub8_87 : sub8 [-4, -2, 8] = true := by decide +kernel
theorem sub8_88 : sub8 [-4, -2, 9] = true := by decide +kernel
theorem sub8_89 : sub8 [-4, -1, -7] = true := by decide +kernel
theorem sub8_90 : sub8 [-4, -1, -6] = true := by decide +kernel
theorem sub8_91 : sub8 [-4, -1, -5] = true := by decide +kernel
theorem sub8_92 : sub8 [-4, -1, -4] = true := by decide +kernel
theorem sub8_93 : sub8 [-4, -1, -3] = true := by decide +kernel
theorem sub8_94 : sub8 [-4, -1, -2] = true := by decide +kernel
theorem sub8_95 : sub8 [-4, -1, -1] = true := by decide +kernel
theorem sb8_2 : ∀ q ∈ blk8_2, sub8 q = true := by
  unfold blk8_2
  exact List.forall_mem_cons.2 ⟨sub8_64, List.forall_mem_cons.2 ⟨sub8_65, List.forall_mem_cons.2 ⟨sub8_66, List.forall_mem_cons.2 ⟨sub8_67, List.forall_mem_cons.2 ⟨sub8_68, List.forall_mem_cons.2 ⟨sub8_69, List.forall_mem_cons.2 ⟨sub8_70, List.forall_mem_cons.2 ⟨sub8_71, List.forall_mem_cons.2 ⟨sub8_72, List.forall_mem_cons.2 ⟨sub8_73, List.forall_mem_cons.2 ⟨sub8_74, List.forall_mem_cons.2 ⟨sub8_75, List.forall_mem_cons.2 ⟨sub8_76, List.forall_mem_cons.2 ⟨sub8_77, List.forall_mem_cons.2 ⟨sub8_78, List.forall_mem_cons.2 ⟨sub8_79, List.forall_mem_cons.2 ⟨sub8_80, List.forall_mem_cons.2 ⟨sub8_81, List.forall_mem_cons.2 ⟨sub8_82, List.forall_mem_cons.2 ⟨sub8_83, List.forall_mem_cons.2 ⟨sub8_84, List.forall_mem_cons.2 ⟨sub8_85, List.forall_mem_cons.2 ⟨sub8_86, List.forall_mem_cons.2 ⟨sub8_87, List.forall_mem_cons.2 ⟨sub8_88, List.forall_mem_cons.2 ⟨sub8_89, List.forall_mem_cons.2 ⟨sub8_90, List.forall_mem_cons.2 ⟨sub8_91, List.forall_mem_cons.2 ⟨sub8_92, List.forall_mem_cons.2 ⟨sub8_93, List.forall_mem_cons.2 ⟨sub8_94, List.forall_mem_cons.2 ⟨sub8_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_96 : sub8 [-4, -1, 0] = true := by decide +kernel
theorem sub8_97 : sub8 [-4, -1, 1] = true := by decide +kernel
theorem sub8_98 : sub8 [-4, -1, 2] = true := by decide +kernel
theorem sub8_99 : sub8 [-4, -1, 3] = true := by decide +kernel
theorem sub8_100 : sub8 [-4, -1, 4] = true := by decide +kernel
theorem sub8_101 : sub8 [-4, -1, 5] = true := by decide +kernel
theorem sub8_102 : sub8 [-4, -1, 6] = true := by decide +kernel
theorem sub8_103 : sub8 [-4, -1, 7] = true := by decide +kernel
theorem sub8_104 : sub8 [-4, -1, 8] = true := by decide +kernel
theorem sub8_105 : sub8 [-4, -1, 9] = true := by decide +kernel
theorem sub8_106 : sub8 [-4, 0, -6] = true := by decide +kernel
theorem sub8_107 : sub8 [-4, 0, -5] = true := by decide +kernel
theorem sub8_108 : sub8 [-4, 0, -4] = true := by decide +kernel
theorem sub8_109 : sub8 [-4, 0, -3] = true := by decide +kernel
theorem sub8_110 : sub8 [-4, 0, -2] = true := by decide +kernel
theorem sub8_111 : sub8 [-4, 0, -1] = true := by decide +kernel
theorem sub8_112 : sub8 [-4, 0, 0] = true := by decide +kernel
theorem sub8_113 : sub8 [-4, 0, 1] = true := by decide +kernel
theorem sub8_114 : sub8 [-4, 0, 2] = true := by decide +kernel
theorem sub8_115 : sub8 [-4, 0, 3] = true := by decide +kernel
theorem sub8_116 : sub8 [-4, 0, 4] = true := by decide +kernel
theorem sub8_117 : sub8 [-4, 0, 5] = true := by decide +kernel
theorem sub8_118 : sub8 [-4, 0, 6] = true := by decide +kernel
theorem sub8_119 : sub8 [-4, 0, 7] = true := by decide +kernel
theorem sub8_120 : sub8 [-4, 0, 8] = true := by decide +kernel
theorem sub8_121 : sub8 [-4, 0, 9] = true := by decide +kernel
theorem sub8_122 : sub8 [-4, 1, -6] = true := by decide +kernel
theorem sub8_123 : sub8 [-4, 1, -5] = true := by decide +kernel
theorem sub8_124 : sub8 [-4, 1, -4] = true := by decide +kernel
theorem sub8_125 : sub8 [-4, 1, -3] = true := by decide +kernel
theorem sub8_126 : sub8 [-4, 1, -2] = true := by decide +kernel
theorem sub8_127 : sub8 [-4, 1, -1] = true := by decide +kernel
theorem sb8_3 : ∀ q ∈ blk8_3, sub8 q = true := by
  unfold blk8_3
  exact List.forall_mem_cons.2 ⟨sub8_96, List.forall_mem_cons.2 ⟨sub8_97, List.forall_mem_cons.2 ⟨sub8_98, List.forall_mem_cons.2 ⟨sub8_99, List.forall_mem_cons.2 ⟨sub8_100, List.forall_mem_cons.2 ⟨sub8_101, List.forall_mem_cons.2 ⟨sub8_102, List.forall_mem_cons.2 ⟨sub8_103, List.forall_mem_cons.2 ⟨sub8_104, List.forall_mem_cons.2 ⟨sub8_105, List.forall_mem_cons.2 ⟨sub8_106, List.forall_mem_cons.2 ⟨sub8_107, List.forall_mem_cons.2 ⟨sub8_108, List.forall_mem_cons.2 ⟨sub8_109, List.forall_mem_cons.2 ⟨sub8_110, List.forall_mem_cons.2 ⟨sub8_111, List.forall_mem_cons.2 ⟨sub8_112, List.forall_mem_cons.2 ⟨sub8_113, List.forall_mem_cons.2 ⟨sub8_114, List.forall_mem_cons.2 ⟨sub8_115, List.forall_mem_cons.2 ⟨sub8_116, List.forall_mem_cons.2 ⟨sub8_117, List.forall_mem_cons.2 ⟨sub8_118, List.forall_mem_cons.2 ⟨sub8_119, List.forall_mem_cons.2 ⟨sub8_120, List.forall_mem_cons.2 ⟨sub8_121, List.forall_mem_cons.2 ⟨sub8_122, List.forall_mem_cons.2 ⟨sub8_123, List.forall_mem_cons.2 ⟨sub8_124, List.forall_mem_cons.2 ⟨sub8_125, List.forall_mem_cons.2 ⟨sub8_126, List.forall_mem_cons.2 ⟨sub8_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_128 : sub8 [-4, 1, 0] = true := by decide +kernel
theorem sub8_129 : sub8 [-4, 1, 1] = true := by decide +kernel
theorem sub8_130 : sub8 [-4, 1, 2] = true := by decide +kernel
theorem sub8_131 : sub8 [-4, 1, 3] = true := by decide +kernel
theorem sub8_132 : sub8 [-4, 1, 4] = true := by decide +kernel
theorem sub8_133 : sub8 [-4, 1, 5] = true := by decide +kernel
theorem sub8_134 : sub8 [-4, 1, 6] = true := by decide +kernel
theorem sub8_135 : sub8 [-4, 1, 7] = true := by decide +kernel
theorem sub8_136 : sub8 [-4, 1, 8] = true := by decide +kernel
theorem sub8_137 : sub8 [-4, 2, -5] = true := by decide +kernel
theorem sub8_138 : sub8 [-4, 2, -4] = true := by decide +kernel
theorem sub8_139 : sub8 [-4, 2, -3] = true := by decide +kernel
theorem sub8_140 : sub8 [-4, 2, -2] = true := by decide +kernel
theorem sub8_141 : sub8 [-4, 2, -1] = true := by decide +kernel
theorem sub8_142 : sub8 [-4, 2, 0] = true := by decide +kernel
theorem sub8_143 : sub8 [-4, 2, 1] = true := by decide +kernel
theorem sub8_144 : sub8 [-4, 2, 2] = true := by decide +kernel
theorem sub8_145 : sub8 [-4, 2, 3] = true := by decide +kernel
theorem sub8_146 : sub8 [-4, 2, 4] = true := by decide +kernel
theorem sub8_147 : sub8 [-4, 2, 5] = true := by decide +kernel
theorem sub8_148 : sub8 [-4, 2, 6] = true := by decide +kernel
theorem sub8_149 : sub8 [-4, 2, 7] = true := by decide +kernel
theorem sub8_150 : sub8 [-4, 3] = true := by decide +kernel
theorem sub8_151 : sub8 [-4, 4] = true := by decide +kernel
theorem sub8_152 : sub8 [-3, -6] = true := by decide +kernel
theorem sub8_153 : sub8 [-3, -5] = true := by decide +kernel
theorem sub8_154 : sub8 [-3, -4, -6] = true := by decide +kernel
theorem sub8_155 : sub8 [-3, -4, -5] = true := by decide +kernel
theorem sub8_156 : sub8 [-3, -4, -4] = true := by decide +kernel
theorem sub8_157 : sub8 [-3, -4, -3] = true := by decide +kernel
theorem sub8_158 : sub8 [-3, -4, -2] = true := by decide +kernel
theorem sub8_159 : sub8 [-3, -4, -1] = true := by decide +kernel
theorem sb8_4 : ∀ q ∈ blk8_4, sub8 q = true := by
  unfold blk8_4
  exact List.forall_mem_cons.2 ⟨sub8_128, List.forall_mem_cons.2 ⟨sub8_129, List.forall_mem_cons.2 ⟨sub8_130, List.forall_mem_cons.2 ⟨sub8_131, List.forall_mem_cons.2 ⟨sub8_132, List.forall_mem_cons.2 ⟨sub8_133, List.forall_mem_cons.2 ⟨sub8_134, List.forall_mem_cons.2 ⟨sub8_135, List.forall_mem_cons.2 ⟨sub8_136, List.forall_mem_cons.2 ⟨sub8_137, List.forall_mem_cons.2 ⟨sub8_138, List.forall_mem_cons.2 ⟨sub8_139, List.forall_mem_cons.2 ⟨sub8_140, List.forall_mem_cons.2 ⟨sub8_141, List.forall_mem_cons.2 ⟨sub8_142, List.forall_mem_cons.2 ⟨sub8_143, List.forall_mem_cons.2 ⟨sub8_144, List.forall_mem_cons.2 ⟨sub8_145, List.forall_mem_cons.2 ⟨sub8_146, List.forall_mem_cons.2 ⟨sub8_147, List.forall_mem_cons.2 ⟨sub8_148, List.forall_mem_cons.2 ⟨sub8_149, List.forall_mem_cons.2 ⟨sub8_150, List.forall_mem_cons.2 ⟨sub8_151, List.forall_mem_cons.2 ⟨sub8_152, List.forall_mem_cons.2 ⟨sub8_153, List.forall_mem_cons.2 ⟨sub8_154, List.forall_mem_cons.2 ⟨sub8_155, List.forall_mem_cons.2 ⟨sub8_156, List.forall_mem_cons.2 ⟨sub8_157, List.forall_mem_cons.2 ⟨sub8_158, List.forall_mem_cons.2 ⟨sub8_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_160 : sub8 [-3, -4, 0] = true := by decide +kernel
theorem sub8_161 : sub8 [-3, -4, 1] = true := by decide +kernel
theorem sub8_162 : sub8 [-3, -4, 2] = true := by decide +kernel
theorem sub8_163 : sub8 [-3, -4, 3] = true := by decide +kernel
theorem sub8_164 : sub8 [-3, -4, 4] = true := by decide +kernel
theorem sub8_165 : sub8 [-3, -4, 5] = true := by decide +kernel
theorem sub8_166 : sub8 [-3, -4, 6] = true := by decide +kernel
theorem sub8_167 : sub8 [-3, -4, 7] = true := by decide +kernel
theorem sub8_168 : sub8 [-3, -3, -7] = true := by decide +kernel
theorem sub8_169 : sub8 [-3, -3, -6] = true := by decide +kernel
theorem sub8_170 : sub8 [-3, -3, -5] = true := by decide +kernel
theorem sub8_171 : sub8 [-3, -3, -4] = true := by decide +kernel
theorem sub8_172 : sub8 [-3, -3, -3] = true := by decide +kernel
theorem sub8_173 : sub8 [-3, -3, -2] = true := by decide +kernel
theorem sub8_174 : sub8 [-3, -3, -1] = true := by decide +kernel
theorem sub8_175 : sub8 [-3, -3, 0] = true := by decide +kernel
theorem sub8_176 : sub8 [-3, -3, 1] = true := by decide +kernel
theorem sub8_177 : sub8 [-3, -3, 2] = true := by decide +kernel
theorem sub8_178 : sub8 [-3, -3, 3] = true := by decide +kernel
theorem sub8_179 : sub8 [-3, -3, 4] = true := by decide +kernel
theorem sub8_180 : sub8 [-3, -3, 5] = true := by decide +kernel
theorem sub8_181 : sub8 [-3, -3, 6] = true := by decide +kernel
theorem sub8_182 : sub8 [-3, -3, 7] = true := by decide +kernel
theorem sub8_183 : sub8 [-3, -3, 8] = true := by decide +kernel
theorem sub8_184 : sub8 [-3, -2, -7] = true := by decide +kernel
theorem sub8_185 : sub8 [-3, -2, -6] = true := by decide +kernel
theorem sub8_186 : sub8 [-3, -2, -5] = true := by decide +kernel
theorem sub8_187 : sub8 [-3, -2, -4] = true := by decide +kernel
theorem sub8_188 : sub8 [-3, -2, -3] = true := by decide +kernel
theorem sub8_189 : sub8 [-3, -2, -2] = true := by decide +kernel
theorem sub8_190 : sub8 [-3, -2, -1] = true := by decide +kernel
theorem sub8_191 : sub8 [-3, -2, 0] = true := by decide +kernel
theorem sb8_5 : ∀ q ∈ blk8_5, sub8 q = true := by
  unfold blk8_5
  exact List.forall_mem_cons.2 ⟨sub8_160, List.forall_mem_cons.2 ⟨sub8_161, List.forall_mem_cons.2 ⟨sub8_162, List.forall_mem_cons.2 ⟨sub8_163, List.forall_mem_cons.2 ⟨sub8_164, List.forall_mem_cons.2 ⟨sub8_165, List.forall_mem_cons.2 ⟨sub8_166, List.forall_mem_cons.2 ⟨sub8_167, List.forall_mem_cons.2 ⟨sub8_168, List.forall_mem_cons.2 ⟨sub8_169, List.forall_mem_cons.2 ⟨sub8_170, List.forall_mem_cons.2 ⟨sub8_171, List.forall_mem_cons.2 ⟨sub8_172, List.forall_mem_cons.2 ⟨sub8_173, List.forall_mem_cons.2 ⟨sub8_174, List.forall_mem_cons.2 ⟨sub8_175, List.forall_mem_cons.2 ⟨sub8_176, List.forall_mem_cons.2 ⟨sub8_177, List.forall_mem_cons.2 ⟨sub8_178, List.forall_mem_cons.2 ⟨sub8_179, List.forall_mem_cons.2 ⟨sub8_180, List.forall_mem_cons.2 ⟨sub8_181, List.forall_mem_cons.2 ⟨sub8_182, List.forall_mem_cons.2 ⟨sub8_183, List.forall_mem_cons.2 ⟨sub8_184, List.forall_mem_cons.2 ⟨sub8_185, List.forall_mem_cons.2 ⟨sub8_186, List.forall_mem_cons.2 ⟨sub8_187, List.forall_mem_cons.2 ⟨sub8_188, List.forall_mem_cons.2 ⟨sub8_189, List.forall_mem_cons.2 ⟨sub8_190, List.forall_mem_cons.2 ⟨sub8_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_192 : sub8 [-3, -2, 1] = true := by decide +kernel
theorem sub8_193 : sub8 [-3, -2, 2] = true := by decide +kernel
theorem sub8_194 : sub8 [-3, -2, 3] = true := by decide +kernel
theorem sub8_195 : sub8 [-3, -2, 4] = true := by decide +kernel
theorem sub8_196 : sub8 [-3, -2, 5] = true := by decide +kernel
theorem sub8_197 : sub8 [-3, -2, 6] = true := by decide +kernel
theorem sub8_198 : sub8 [-3, -2, 7] = true := by decide +kernel
theorem sub8_199 : sub8 [-3, -2, 8] = true := by decide +kernel
theorem sub8_200 : sub8 [-3, -2, 9] = true := by decide +kernel
theorem sub8_201 : sub8 [-3, -1, -8] = true := by decide +kernel
theorem sub8_202 : sub8 [-3, -1, -7] = true := by decide +kernel
theorem sub8_203 : sub8 [-3, -1, -6] = true := by decide +kernel
theorem sub8_204 : sub8 [-3, -1, -5] = true := by decide +kernel
theorem sub8_205 : sub8 [-3, -1, -4] = true := by decide +kernel
theorem sub8_206 : sub8 [-3, -1, -3] = true := by decide +kernel
theorem sub8_207 : sub8 [-3, -1, -2] = true := by decide +kernel
theorem sub8_208 : sub8 [-3, -1, -1] = true := by decide +kernel
theorem sub8_209 : sub8 [-3, -1, 0] = true := by decide +kernel
theorem sub8_210 : sub8 [-3, -1, 1] = true := by decide +kernel
theorem sub8_211 : sub8 [-3, -1, 2] = true := by decide +kernel
theorem sub8_212 : sub8 [-3, -1, 3] = true := by decide +kernel
theorem sub8_213 : sub8 [-3, -1, 4] = true := by decide +kernel
theorem sub8_214 : sub8 [-3, -1, 5] = true := by decide +kernel
theorem sub8_215 : sub8 [-3, -1, 6] = true := by decide +kernel
theorem sub8_216 : sub8 [-3, -1, 7] = true := by decide +kernel
theorem sub8_217 : sub8 [-3, -1, 8] = true := by decide +kernel
theorem sub8_218 : sub8 [-3, -1, 9] = true := by decide +kernel
theorem sub8_219 : sub8 [-3, 0, -8] = true := by decide +kernel
theorem sub8_220 : sub8 [-3, 0, -7] = true := by decide +kernel
theorem sub8_221 : sub8 [-3, 0, -6] = true := by decide +kernel
theorem sub8_222 : sub8 [-3, 0, -5] = true := by decide +kernel
theorem sub8_223 : sub8 [-3, 0, -4] = true := by decide +kernel
theorem sb8_6 : ∀ q ∈ blk8_6, sub8 q = true := by
  unfold blk8_6
  exact List.forall_mem_cons.2 ⟨sub8_192, List.forall_mem_cons.2 ⟨sub8_193, List.forall_mem_cons.2 ⟨sub8_194, List.forall_mem_cons.2 ⟨sub8_195, List.forall_mem_cons.2 ⟨sub8_196, List.forall_mem_cons.2 ⟨sub8_197, List.forall_mem_cons.2 ⟨sub8_198, List.forall_mem_cons.2 ⟨sub8_199, List.forall_mem_cons.2 ⟨sub8_200, List.forall_mem_cons.2 ⟨sub8_201, List.forall_mem_cons.2 ⟨sub8_202, List.forall_mem_cons.2 ⟨sub8_203, List.forall_mem_cons.2 ⟨sub8_204, List.forall_mem_cons.2 ⟨sub8_205, List.forall_mem_cons.2 ⟨sub8_206, List.forall_mem_cons.2 ⟨sub8_207, List.forall_mem_cons.2 ⟨sub8_208, List.forall_mem_cons.2 ⟨sub8_209, List.forall_mem_cons.2 ⟨sub8_210, List.forall_mem_cons.2 ⟨sub8_211, List.forall_mem_cons.2 ⟨sub8_212, List.forall_mem_cons.2 ⟨sub8_213, List.forall_mem_cons.2 ⟨sub8_214, List.forall_mem_cons.2 ⟨sub8_215, List.forall_mem_cons.2 ⟨sub8_216, List.forall_mem_cons.2 ⟨sub8_217, List.forall_mem_cons.2 ⟨sub8_218, List.forall_mem_cons.2 ⟨sub8_219, List.forall_mem_cons.2 ⟨sub8_220, List.forall_mem_cons.2 ⟨sub8_221, List.forall_mem_cons.2 ⟨sub8_222, List.forall_mem_cons.2 ⟨sub8_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_224 : sub8 [-3, 0, -3] = true := by decide +kernel
theorem sub8_225 : sub8 [-3, 0, -2] = true := by decide +kernel
theorem sub8_226 : sub8 [-3, 0, -1] = true := by decide +kernel
theorem sub8_227 : sub8 [-3, 0, 0] = true := by decide +kernel
theorem sub8_228 : sub8 [-3, 0, 1] = true := by decide +kernel
theorem sub8_229 : sub8 [-3, 0, 2] = true := by decide +kernel
theorem sub8_230 : sub8 [-3, 0, 3] = true := by decide +kernel
theorem sub8_231 : sub8 [-3, 0, 4] = true := by decide +kernel
theorem sub8_232 : sub8 [-3, 0, 5] = true := by decide +kernel
theorem sub8_233 : sub8 [-3, 0, 6] = true := by decide +kernel
theorem sub8_234 : sub8 [-3, 0, 7] = true := by decide +kernel
theorem sub8_235 : sub8 [-3, 0, 8] = true := by decide +kernel
theorem sub8_236 : sub8 [-3, 0, 9] = true := by decide +kernel
theorem sub8_237 : sub8 [-3, 1, -7] = true := by decide +kernel
theorem sub8_238 : sub8 [-3, 1, -6] = true := by decide +kernel
theorem sub8_239 : sub8 [-3, 1, -5] = true := by decide +kernel
theorem sub8_240 : sub8 [-3, 1, -4] = true := by decide +kernel
theorem sub8_241 : sub8 [-3, 1, -3] = true := by decide +kernel
theorem sub8_242 : sub8 [-3, 1, -2] = true := by decide +kernel
theorem sub8_243 : sub8 [-3, 1, -1] = true := by decide +kernel
theorem sub8_244 : sub8 [-3, 1, 0] = true := by decide +kernel
theorem sub8_245 : sub8 [-3, 1, 1] = true := by decide +kernel
theorem sub8_246 : sub8 [-3, 1, 2] = true := by decide +kernel
theorem sub8_247 : sub8 [-3, 1, 3] = true := by decide +kernel
theorem sub8_248 : sub8 [-3, 1, 4] = true := by decide +kernel
theorem sub8_249 : sub8 [-3, 1, 5] = true := by decide +kernel
theorem sub8_250 : sub8 [-3, 1, 6] = true := by decide +kernel
theorem sub8_251 : sub8 [-3, 1, 7] = true := by decide +kernel
theorem sub8_252 : sub8 [-3, 1, 8] = true := by decide +kernel
theorem sub8_253 : sub8 [-3, 1, 9] = true := by decide +kernel
theorem sub8_254 : sub8 [-3, 2, -7] = true := by decide +kernel
theorem sub8_255 : sub8 [-3, 2, -6] = true := by decide +kernel
theorem sb8_7 : ∀ q ∈ blk8_7, sub8 q = true := by
  unfold blk8_7
  exact List.forall_mem_cons.2 ⟨sub8_224, List.forall_mem_cons.2 ⟨sub8_225, List.forall_mem_cons.2 ⟨sub8_226, List.forall_mem_cons.2 ⟨sub8_227, List.forall_mem_cons.2 ⟨sub8_228, List.forall_mem_cons.2 ⟨sub8_229, List.forall_mem_cons.2 ⟨sub8_230, List.forall_mem_cons.2 ⟨sub8_231, List.forall_mem_cons.2 ⟨sub8_232, List.forall_mem_cons.2 ⟨sub8_233, List.forall_mem_cons.2 ⟨sub8_234, List.forall_mem_cons.2 ⟨sub8_235, List.forall_mem_cons.2 ⟨sub8_236, List.forall_mem_cons.2 ⟨sub8_237, List.forall_mem_cons.2 ⟨sub8_238, List.forall_mem_cons.2 ⟨sub8_239, List.forall_mem_cons.2 ⟨sub8_240, List.forall_mem_cons.2 ⟨sub8_241, List.forall_mem_cons.2 ⟨sub8_242, List.forall_mem_cons.2 ⟨sub8_243, List.forall_mem_cons.2 ⟨sub8_244, List.forall_mem_cons.2 ⟨sub8_245, List.forall_mem_cons.2 ⟨sub8_246, List.forall_mem_cons.2 ⟨sub8_247, List.forall_mem_cons.2 ⟨sub8_248, List.forall_mem_cons.2 ⟨sub8_249, List.forall_mem_cons.2 ⟨sub8_250, List.forall_mem_cons.2 ⟨sub8_251, List.forall_mem_cons.2 ⟨sub8_252, List.forall_mem_cons.2 ⟨sub8_253, List.forall_mem_cons.2 ⟨sub8_254, List.forall_mem_cons.2 ⟨sub8_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C080
