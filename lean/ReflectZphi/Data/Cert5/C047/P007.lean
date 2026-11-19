import ReflectZphi.Data.Cert5.C047.Base

namespace ReflectZphi.Data.Cert5.C047
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub4_1376 : sub4 [3, -1, 6] = true := by decide +kernel
theorem sub4_1377 : sub4 [3, -1, 7] = true := by decide +kernel
theorem sub4_1378 : sub4 [3, -1, 8] = true := by decide +kernel
theorem sub4_1379 : sub4 [3, -1, 9] = true := by decide +kernel
theorem sub4_1380 : sub4 [3, 0, -11] = true := by decide +kernel
theorem sub4_1381 : sub4 [3, 0, -10] = true := by decide +kernel
theorem sub4_1382 : sub4 [3, 0, -9] = true := by decide +kernel
theorem sub4_1383 : sub4 [3, 0, -8] = true := by decide +kernel
theorem sub4_1384 : sub4 [3, 0, -7] = true := by decide +kernel
theorem sub4_1385 : sub4 [3, 0, -6] = true := by decide +kernel
theorem sub4_1386 : sub4 [3, 0, -5] = true := by decide +kernel
theorem sub4_1387 : sub4 [3, 0, -4] = true := by decide +kernel
theorem sub4_1388 : sub4 [3, 0, -3] = true := by decide +kernel
theorem sub4_1389 : sub4 [3, 0, -2] = true := by decide +kernel
theorem sub4_1390 : sub4 [3, 0, -1] = true := by decide +kernel
theorem sub4_1391 : sub4 [3, 0, 0] = true := by decide +kernel
theorem sub4_1392 : sub4 [3, 0, 1] = true := by decide +kernel
theorem sub4_1393 : sub4 [3, 0, 2] = true := by decide +kernel
theorem sub4_1394 : sub4 [3, 0, 3] = true := by decide +kernel
theorem sub4_1395 : sub4 [3, 0, 4] = true := by decide +kernel
theorem sub4_1396 : sub4 [3, 0, 5] = true := by decide +kernel
theorem sub4_1397 : sub4 [3, 0, 6] = true := by decide +kernel
theorem sub4_1398 : sub4 [3, 0, 7] = true := by decide +kernel
theorem sub4_1399 : sub4 [3, 0, 8] = true := by decide +kernel
theorem sub4_1400 : sub4 [3, 1, -10] = true := by decide +kernel
theorem sub4_1401 : sub4 [3, 1, -9] = true := by decide +kernel
theorem sub4_1402 : sub4 [3, 1, -8] = true := by decide +kernel
theorem sub4_1403 : sub4 [3, 1, -7] = true := by decide +kernel
theorem sub4_1404 : sub4 [3, 1, -6] = true := by decide +kernel
theorem sub4_1405 : sub4 [3, 1, -5] = true := by decide +kernel
theorem sub4_1406 : sub4 [3, 1, -4] = true := by decide +kernel
theorem sub4_1407 : sub4 [3, 1, -3] = true := by decide +kernel
theorem sb4_43 : ∀ q ∈ blk4_43, sub4 q = true := by
  unfold blk4_43
  exact List.forall_mem_cons.2 ⟨sub4_1376, List.forall_mem_cons.2 ⟨sub4_1377, List.forall_mem_cons.2 ⟨sub4_1378, List.forall_mem_cons.2 ⟨sub4_1379, List.forall_mem_cons.2 ⟨sub4_1380, List.forall_mem_cons.2 ⟨sub4_1381, List.forall_mem_cons.2 ⟨sub4_1382, List.forall_mem_cons.2 ⟨sub4_1383, List.forall_mem_cons.2 ⟨sub4_1384, List.forall_mem_cons.2 ⟨sub4_1385, List.forall_mem_cons.2 ⟨sub4_1386, List.forall_mem_cons.2 ⟨sub4_1387, List.forall_mem_cons.2 ⟨sub4_1388, List.forall_mem_cons.2 ⟨sub4_1389, List.forall_mem_cons.2 ⟨sub4_1390, List.forall_mem_cons.2 ⟨sub4_1391, List.forall_mem_cons.2 ⟨sub4_1392, List.forall_mem_cons.2 ⟨sub4_1393, List.forall_mem_cons.2 ⟨sub4_1394, List.forall_mem_cons.2 ⟨sub4_1395, List.forall_mem_cons.2 ⟨sub4_1396, List.forall_mem_cons.2 ⟨sub4_1397, List.forall_mem_cons.2 ⟨sub4_1398, List.forall_mem_cons.2 ⟨sub4_1399, List.forall_mem_cons.2 ⟨sub4_1400, List.forall_mem_cons.2 ⟨sub4_1401, List.forall_mem_cons.2 ⟨sub4_1402, List.forall_mem_cons.2 ⟨sub4_1403, List.forall_mem_cons.2 ⟨sub4_1404, List.forall_mem_cons.2 ⟨sub4_1405, List.forall_mem_cons.2 ⟨sub4_1406, List.forall_mem_cons.2 ⟨sub4_1407, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_1408 : sub4 [3, 1, -2] = true := by decide +kernel
theorem sub4_1409 : sub4 [3, 1, -1] = true := by decide +kernel
theorem sub4_1410 : sub4 [3, 1, 0] = true := by decide +kernel
theorem sub4_1411 : sub4 [3, 1, 1] = true := by decide +kernel
theorem sub4_1412 : sub4 [3, 1, 2] = true := by decide +kernel
theorem sub4_1413 : sub4 [3, 1, 3] = true := by decide +kernel
theorem sub4_1414 : sub4 [3, 1, 4] = true := by decide +kernel
theorem sub4_1415 : sub4 [3, 1, 5] = true := by decide +kernel
theorem sub4_1416 : sub4 [3, 1, 6] = true := by decide +kernel
theorem sub4_1417 : sub4 [3, 1, 7] = true := by decide +kernel
theorem sub4_1418 : sub4 [3, 1, 8] = true := by decide +kernel
theorem sub4_1419 : sub4 [3, 2, -9] = true := by decide +kernel
theorem sub4_1420 : sub4 [3, 2, -8] = true := by decide +kernel
theorem sub4_1421 : sub4 [3, 2, -7] = true := by decide +kernel
theorem sub4_1422 : sub4 [3, 2, -6] = true := by decide +kernel
theorem sub4_1423 : sub4 [3, 2, -5] = true := by decide +kernel
theorem sub4_1424 : sub4 [3, 2, -4] = true := by decide +kernel
theorem sub4_1425 : sub4 [3, 2, -3] = true := by decide +kernel
theorem sub4_1426 : sub4 [3, 2, -2] = true := by decide +kernel
theorem sub4_1427 : sub4 [3, 2, -1] = true := by decide +kernel
theorem sub4_1428 : sub4 [3, 2, 0] = true := by decide +kernel
theorem sub4_1429 : sub4 [3, 2, 1] = true := by decide +kernel
theorem sub4_1430 : sub4 [3, 2, 2] = true := by decide +kernel
theorem sub4_1431 : sub4 [3, 2, 3] = true := by decide +kernel
theorem sub4_1432 : sub4 [3, 2, 4] = true := by decide +kernel
theorem sub4_1433 : sub4 [3, 2, 5] = true := by decide +kernel
theorem sub4_1434 : sub4 [3, 2, 6] = true := by decide +kernel
theorem sub4_1435 : sub4 [3, 3] = true := by decide +kernel
theorem sub4_1436 : sub4 [4, -6] = true := by decide +kernel
theorem sub4_1437 : sub4 [4, -5] = true := by decide +kernel
theorem sub4_1438 : sub4 [4, -4, -9] = true := by decide +kernel
theorem sub4_1439 : sub4 [4, -4, -8] = true := by decide +kernel
theorem sb4_44 : ∀ q ∈ blk4_44, sub4 q = true := by
  unfold blk4_44
  exact List.forall_mem_cons.2 ⟨sub4_1408, List.forall_mem_cons.2 ⟨sub4_1409, List.forall_mem_cons.2 ⟨sub4_1410, List.forall_mem_cons.2 ⟨sub4_1411, List.forall_mem_cons.2 ⟨sub4_1412, List.forall_mem_cons.2 ⟨sub4_1413, List.forall_mem_cons.2 ⟨sub4_1414, List.forall_mem_cons.2 ⟨sub4_1415, List.forall_mem_cons.2 ⟨sub4_1416, List.forall_mem_cons.2 ⟨sub4_1417, List.forall_mem_cons.2 ⟨sub4_1418, List.forall_mem_cons.2 ⟨sub4_1419, List.forall_mem_cons.2 ⟨sub4_1420, List.forall_mem_cons.2 ⟨sub4_1421, List.forall_mem_cons.2 ⟨sub4_1422, List.forall_mem_cons.2 ⟨sub4_1423, List.forall_mem_cons.2 ⟨sub4_1424, List.forall_mem_cons.2 ⟨sub4_1425, List.forall_mem_cons.2 ⟨sub4_1426, List.forall_mem_cons.2 ⟨sub4_1427, List.forall_mem_cons.2 ⟨sub4_1428, List.forall_mem_cons.2 ⟨sub4_1429, List.forall_mem_cons.2 ⟨sub4_1430, List.forall_mem_cons.2 ⟨sub4_1431, List.forall_mem_cons.2 ⟨sub4_1432, List.forall_mem_cons.2 ⟨sub4_1433, List.forall_mem_cons.2 ⟨sub4_1434, List.forall_mem_cons.2 ⟨sub4_1435, List.forall_mem_cons.2 ⟨sub4_1436, List.forall_mem_cons.2 ⟨sub4_1437, List.forall_mem_cons.2 ⟨sub4_1438, List.forall_mem_cons.2 ⟨sub4_1439, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_1440 : sub4 [4, -4, -7] = true := by decide +kernel
theorem sub4_1441 : sub4 [4, -4, -6] = true := by decide +kernel
theorem sub4_1442 : sub4 [4, -4, -5] = true := by decide +kernel
theorem sub4_1443 : sub4 [4, -4, -4] = true := by decide +kernel
theorem sub4_1444 : sub4 [4, -4, -3] = true := by decide +kernel
theorem sub4_1445 : sub4 [4, -4, -2] = true := by decide +kernel
theorem sub4_1446 : sub4 [4, -4, -1] = true := by decide +kernel
theorem sub4_1447 : sub4 [4, -4, 0] = true := by decide +kernel
theorem sub4_1448 : sub4 [4, -4, 1] = true := by decide +kernel
theorem sub4_1449 : sub4 [4, -4, 2] = true := by decide +kernel
theorem sub4_1450 : sub4 [4, -4, 3] = true := by decide +kernel
theorem sub4_1451 : sub4 [4, -4, 4] = true := by decide +kernel
theorem sub4_1452 : sub4 [4, -4, 5] = true := by decide +kernel
theorem sub4_1453 : sub4 [4, -3, -9] = true := by decide +kernel
theorem sub4_1454 : sub4 [4, -3, -8] = true := by decide +kernel
theorem sub4_1455 : sub4 [4, -3, -7] = true := by decide +kernel
theorem sub4_1456 : sub4 [4, -3, -6] = true := by decide +kernel
theorem sub4_1457 : sub4 [4, -3, -5] = true := by decide +kernel
theorem sub4_1458 : sub4 [4, -3, -4] = true := by decide +kernel
theorem sub4_1459 : sub4 [4, -3, -3] = true := by decide +kernel
theorem sub4_1460 : sub4 [4, -3, -2] = true := by decide +kernel
theorem sub4_1461 : sub4 [4, -3, -1] = true := by decide +kernel
theorem sub4_1462 : sub4 [4, -3, 0] = true := by decide +kernel
theorem sub4_1463 : sub4 [4, -3, 1] = true := by decide +kernel
theorem sub4_1464 : sub4 [4, -3, 2] = true := by decide +kernel
theorem sub4_1465 : sub4 [4, -3, 3] = true := by decide +kernel
theorem sub4_1466 : sub4 [4, -3, 4] = true := by decide +kernel
theorem sub4_1467 : sub4 [4, -3, 5] = true := by decide +kernel
theorem sub4_1468 : sub4 [4, -3, 6] = true := by decide +kernel
theorem sub4_1469 : sub4 [4, -2, -10] = true := by decide +kernel
theorem sub4_1470 : sub4 [4, -2, -9] = true := by decide +kernel
theorem sub4_1471 : sub4 [4, -2, -8] = true := by decide +kernel
theorem sb4_45 : ∀ q ∈ blk4_45, sub4 q = true := by
  unfold blk4_45
  exact List.forall_mem_cons.2 ⟨sub4_1440, List.forall_mem_cons.2 ⟨sub4_1441, List.forall_mem_cons.2 ⟨sub4_1442, List.forall_mem_cons.2 ⟨sub4_1443, List.forall_mem_cons.2 ⟨sub4_1444, List.forall_mem_cons.2 ⟨sub4_1445, List.forall_mem_cons.2 ⟨sub4_1446, List.forall_mem_cons.2 ⟨sub4_1447, List.forall_mem_cons.2 ⟨sub4_1448, List.forall_mem_cons.2 ⟨sub4_1449, List.forall_mem_cons.2 ⟨sub4_1450, List.forall_mem_cons.2 ⟨sub4_1451, List.forall_mem_cons.2 ⟨sub4_1452, List.forall_mem_cons.2 ⟨sub4_1453, List.forall_mem_cons.2 ⟨sub4_1454, List.forall_mem_cons.2 ⟨sub4_1455, List.forall_mem_cons.2 ⟨sub4_1456, List.forall_mem_cons.2 ⟨sub4_1457, List.forall_mem_cons.2 ⟨sub4_1458, List.forall_mem_cons.2 ⟨sub4_1459, List.forall_mem_cons.2 ⟨sub4_1460, List.forall_mem_cons.2 ⟨sub4_1461, List.forall_mem_cons.2 ⟨sub4_1462, List.forall_mem_cons.2 ⟨sub4_1463, List.forall_mem_cons.2 ⟨sub4_1464, List.forall_mem_cons.2 ⟨sub4_1465, List.forall_mem_cons.2 ⟨sub4_1466, List.forall_mem_cons.2 ⟨sub4_1467, List.forall_mem_cons.2 ⟨sub4_1468, List.forall_mem_cons.2 ⟨sub4_1469, List.forall_mem_cons.2 ⟨sub4_1470, List.forall_mem_cons.2 ⟨sub4_1471, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_1472 : sub4 [4, -2, -7] = true := by decide +kernel
theorem sub4_1473 : sub4 [4, -2, -6] = true := by decide +kernel
theorem sub4_1474 : sub4 [4, -2, -5] = true := by decide +kernel
theorem sub4_1475 : sub4 [4, -2, -4] = true := by decide +kernel
theorem sub4_1476 : sub4 [4, -2, -3] = true := by decide +kernel
theorem sub4_1477 : sub4 [4, -2, -2] = true := by decide +kernel
theorem sub4_1478 : sub4 [4, -2, -1] = true := by decide +kernel
theorem sub4_1479 : sub4 [4, -2, 0] = true := by decide +kernel
theorem sub4_1480 : sub4 [4, -2, 1] = true := by decide +kernel
theorem sub4_1481 : sub4 [4, -2, 2] = true := by decide +kernel
theorem sub4_1482 : sub4 [4, -2, 3] = true := by decide +kernel
theorem sub4_1483 : sub4 [4, -2, 4] = true := by decide +kernel
theorem sub4_1484 : sub4 [4, -2, 5] = true := by decide +kernel
theorem sub4_1485 : sub4 [4, -2, 6] = true := by decide +kernel
theorem sub4_1486 : sub4 [4, -1, -10] = true := by decide +kernel
theorem sub4_1487 : sub4 [4, -1, -9] = true := by decide +kernel
theorem sub4_1488 : sub4 [4, -1, -8] = true := by decide +kernel
theorem sub4_1489 : sub4 [4, -1, -7] = true := by decide +kernel
theorem sub4_1490 : sub4 [4, -1, -6] = true := by decide +kernel
theorem sub4_1491 : sub4 [4, -1, -5] = true := by decide +kernel
theorem sub4_1492 : sub4 [4, -1, -4] = true := by decide +kernel
theorem sub4_1493 : sub4 [4, -1, -3] = true := by decide +kernel
theorem sub4_1494 : sub4 [4, -1, -2] = true := by decide +kernel
theorem sub4_1495 : sub4 [4, -1, -1] = true := by decide +kernel
theorem sub4_1496 : sub4 [4, -1, 0] = true := by decide +kernel
theorem sub4_1497 : sub4 [4, -1, 1] = true := by decide +kernel
theorem sub4_1498 : sub4 [4, -1, 2] = true := by decide +kernel
theorem sub4_1499 : sub4 [4, -1, 3] = true := by decide +kernel
theorem sub4_1500 : sub4 [4, -1, 4] = true := by decide +kernel
theorem sub4_1501 : sub4 [4, -1, 5] = true := by decide +kernel
theorem sub4_1502 : sub4 [4, -1, 6] = true := by decide +kernel
theorem sub4_1503 : sub4 [4, 0, -9] = true := by decide +kernel
theorem sb4_46 : ∀ q ∈ blk4_46, sub4 q = true := by
  unfold blk4_46
  exact List.forall_mem_cons.2 ⟨sub4_1472, List.forall_mem_cons.2 ⟨sub4_1473, List.forall_mem_cons.2 ⟨sub4_1474, List.forall_mem_cons.2 ⟨sub4_1475, List.forall_mem_cons.2 ⟨sub4_1476, List.forall_mem_cons.2 ⟨sub4_1477, List.forall_mem_cons.2 ⟨sub4_1478, List.forall_mem_cons.2 ⟨sub4_1479, List.forall_mem_cons.2 ⟨sub4_1480, List.forall_mem_cons.2 ⟨sub4_1481, List.forall_mem_cons.2 ⟨sub4_1482, List.forall_mem_cons.2 ⟨sub4_1483, List.forall_mem_cons.2 ⟨sub4_1484, List.forall_mem_cons.2 ⟨sub4_1485, List.forall_mem_cons.2 ⟨sub4_1486, List.forall_mem_cons.2 ⟨sub4_1487, List.forall_mem_cons.2 ⟨sub4_1488, List.forall_mem_cons.2 ⟨sub4_1489, List.forall_mem_cons.2 ⟨sub4_1490, List.forall_mem_cons.2 ⟨sub4_1491, List.forall_mem_cons.2 ⟨sub4_1492, List.forall_mem_cons.2 ⟨sub4_1493, List.forall_mem_cons.2 ⟨sub4_1494, List.forall_mem_cons.2 ⟨sub4_1495, List.forall_mem_cons.2 ⟨sub4_1496, List.forall_mem_cons.2 ⟨sub4_1497, List.forall_mem_cons.2 ⟨sub4_1498, List.forall_mem_cons.2 ⟨sub4_1499, List.forall_mem_cons.2 ⟨sub4_1500, List.forall_mem_cons.2 ⟨sub4_1501, List.forall_mem_cons.2 ⟨sub4_1502, List.forall_mem_cons.2 ⟨sub4_1503, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_1504 : sub4 [4, 0, -8] = true := by decide +kernel
theorem sub4_1505 : sub4 [4, 0, -7] = true := by decide +kernel
theorem sub4_1506 : sub4 [4, 0, -6] = true := by decide +kernel
theorem sub4_1507 : sub4 [4, 0, -5] = true := by decide +kernel
theorem sub4_1508 : sub4 [4, 0, -4] = true := by decide +kernel
theorem sub4_1509 : sub4 [4, 0, -3] = true := by decide +kernel
theorem sub4_1510 : sub4 [4, 0, -2] = true := by decide +kernel
theorem sub4_1511 : sub4 [4, 0, -1] = true := by decide +kernel
theorem sub4_1512 : sub4 [4, 0, 0] = true := by decide +kernel
theorem sub4_1513 : sub4 [4, 0, 1] = true := by decide +kernel
theorem sub4_1514 : sub4 [4, 0, 2] = true := by decide +kernel
theorem sub4_1515 : sub4 [4, 0, 3] = true := by decide +kernel
theorem sub4_1516 : sub4 [4, 0, 4] = true := by decide +kernel
theorem sub4_1517 : sub4 [4, 0, 5] = true := by decide +kernel
theorem sub4_1518 : sub4 [4, 0, 6] = true := by decide +kernel
theorem sub4_1519 : sub4 [4, 1] = true := by decide +kernel
theorem sub4_1520 : sub4 [4, 2] = true := by decide +kernel
theorem sub4_1521 : sub4 [5, -5] = true := by decide +kernel
theorem sub4_1522 : sub4 [5, -4] = true := by decide +kernel
theorem sub4_1523 : sub4 [5, -3] = true := by decide +kernel
theorem sub4_1524 : sub4 [5, -2] = true := by decide +kernel
theorem sub4_1525 : sub4 [5, -1] = true := by decide +kernel
theorem sub4_1526 : sub4 [5, 0] = true := by decide +kernel
theorem sb4_47 : ∀ q ∈ blk4_47, sub4 q = true := by
  unfold blk4_47
  exact List.forall_mem_cons.2 ⟨sub4_1504, List.forall_mem_cons.2 ⟨sub4_1505, List.forall_mem_cons.2 ⟨sub4_1506, List.forall_mem_cons.2 ⟨sub4_1507, List.forall_mem_cons.2 ⟨sub4_1508, List.forall_mem_cons.2 ⟨sub4_1509, List.forall_mem_cons.2 ⟨sub4_1510, List.forall_mem_cons.2 ⟨sub4_1511, List.forall_mem_cons.2 ⟨sub4_1512, List.forall_mem_cons.2 ⟨sub4_1513, List.forall_mem_cons.2 ⟨sub4_1514, List.forall_mem_cons.2 ⟨sub4_1515, List.forall_mem_cons.2 ⟨sub4_1516, List.forall_mem_cons.2 ⟨sub4_1517, List.forall_mem_cons.2 ⟨sub4_1518, List.forall_mem_cons.2 ⟨sub4_1519, List.forall_mem_cons.2 ⟨sub4_1520, List.forall_mem_cons.2 ⟨sub4_1521, List.forall_mem_cons.2 ⟨sub4_1522, List.forall_mem_cons.2 ⟨sub4_1523, List.forall_mem_cons.2 ⟨sub4_1524, List.forall_mem_cons.2 ⟨sub4_1525, List.forall_mem_cons.2 ⟨sub4_1526, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_0 : sub5 [-7] = true := by decide +kernel
theorem sub5_1 : sub5 [-6, -4] = true := by decide +kernel
theorem sub5_2 : sub5 [-6, -3] = true := by decide +kernel
theorem sub5_3 : sub5 [-6, -2] = true := by decide +kernel
theorem sub5_4 : sub5 [-6, -1] = true := by decide +kernel
theorem sub5_5 : sub5 [-6, 0] = true := by decide +kernel
theorem sub5_6 : sub5 [-6, 1] = true := by decide +kernel
theorem sub5_7 : sub5 [-6, 2] = true := by decide +kernel
theorem sub5_8 : sub5 [-6, 3] = true := by decide +kernel
theorem sub5_9 : sub5 [-5, -5] = true := by decide +kernel
theorem sub5_10 : sub5 [-5, -4] = true := by decide +kernel
theorem sub5_11 : sub5 [-5, -3] = true := by decide +kernel
theorem sub5_12 : sub5 [-5, -2] = true := by decide +kernel
theorem sub5_13 : sub5 [-5, -1] = true := by decide +kernel
theorem sub5_14 : sub5 [-5, 0] = true := by decide +kernel
theorem sub5_15 : sub5 [-5, 1] = true := by decide +kernel
theorem sub5_16 : sub5 [-5, 2] = true := by decide +kernel
theorem sub5_17 : sub5 [-5, 3] = true := by decide +kernel
theorem sub5_18 : sub5 [-5, 4] = true := by decide +kernel
theorem sub5_19 : sub5 [-5, 5] = true := by decide +kernel
theorem sub5_20 : sub5 [-4, -6] = true := by decide +kernel
theorem sub5_21 : sub5 [-4, -5] = true := by decide +kernel
theorem sub5_22 : sub5 [-4, -4] = true := by decide +kernel
theorem sub5_23 : sub5 [-4, -3] = true := by decide +kernel
theorem sub5_24 : sub5 [-4, -2] = true := by decide +kernel
theorem sub5_25 : sub5 [-4, -1, -8] = true := by decide +kernel
theorem sub5_26 : sub5 [-4, -1, -7] = true := by decide +kernel
theorem sub5_27 : sub5 [-4, -1, -6] = true := by decide +kernel
theorem sub5_28 : sub5 [-4, -1, -5] = true := by decide +kernel
theorem sub5_29 : sub5 [-4, -1, -4] = true := by decide +kernel
theorem sub5_30 : sub5 [-4, -1, -3] = true := by decide +kernel
theorem sub5_31 : sub5 [-4, -1, -2] = true := by decide +kernel
theorem sb5_0 : ∀ q ∈ blk5_0, sub5 q = true := by
  unfold blk5_0
  exact List.forall_mem_cons.2 ⟨sub5_0, List.forall_mem_cons.2 ⟨sub5_1, List.forall_mem_cons.2 ⟨sub5_2, List.forall_mem_cons.2 ⟨sub5_3, List.forall_mem_cons.2 ⟨sub5_4, List.forall_mem_cons.2 ⟨sub5_5, List.forall_mem_cons.2 ⟨sub5_6, List.forall_mem_cons.2 ⟨sub5_7, List.forall_mem_cons.2 ⟨sub5_8, List.forall_mem_cons.2 ⟨sub5_9, List.forall_mem_cons.2 ⟨sub5_10, List.forall_mem_cons.2 ⟨sub5_11, List.forall_mem_cons.2 ⟨sub5_12, List.forall_mem_cons.2 ⟨sub5_13, List.forall_mem_cons.2 ⟨sub5_14, List.forall_mem_cons.2 ⟨sub5_15, List.forall_mem_cons.2 ⟨sub5_16, List.forall_mem_cons.2 ⟨sub5_17, List.forall_mem_cons.2 ⟨sub5_18, List.forall_mem_cons.2 ⟨sub5_19, List.forall_mem_cons.2 ⟨sub5_20, List.forall_mem_cons.2 ⟨sub5_21, List.forall_mem_cons.2 ⟨sub5_22, List.forall_mem_cons.2 ⟨sub5_23, List.forall_mem_cons.2 ⟨sub5_24, List.forall_mem_cons.2 ⟨sub5_25, List.forall_mem_cons.2 ⟨sub5_26, List.forall_mem_cons.2 ⟨sub5_27, List.forall_mem_cons.2 ⟨sub5_28, List.forall_mem_cons.2 ⟨sub5_29, List.forall_mem_cons.2 ⟨sub5_30, List.forall_mem_cons.2 ⟨sub5_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_32 : sub5 [-4, -1, -1] = true := by decide +kernel
theorem sub5_33 : sub5 [-4, -1, 0] = true := by decide +kernel
theorem sub5_34 : sub5 [-4, -1, 1] = true := by decide +kernel
theorem sub5_35 : sub5 [-4, -1, 2] = true := by decide +kernel
theorem sub5_36 : sub5 [-4, -1, 3] = true := by decide +kernel
theorem sub5_37 : sub5 [-4, -1, 4] = true := by decide +kernel
theorem sub5_38 : sub5 [-4, -1, 5] = true := by decide +kernel
theorem sub5_39 : sub5 [-4, 0, -9] = true := by decide +kernel
theorem sub5_40 : sub5 [-4, 0, -8] = true := by decide +kernel
theorem sub5_41 : sub5 [-4, 0, -7] = true := by decide +kernel
theorem sub5_42 : sub5 [-4, 0, -6] = true := by decide +kernel
theorem sub5_43 : sub5 [-4, 0, -5] = true := by decide +kernel
theorem sub5_44 : sub5 [-4, 0, -4] = true := by decide +kernel
theorem sub5_45 : sub5 [-4, 0, -3] = true := by decide +kernel
theorem sub5_46 : sub5 [-4, 0, -2] = true := by decide +kernel
theorem sub5_47 : sub5 [-4, 0, -1] = true := by decide +kernel
theorem sub5_48 : sub5 [-4, 0, 0] = true := by decide +kernel
theorem sub5_49 : sub5 [-4, 0, 1] = true := by decide +kernel
theorem sub5_50 : sub5 [-4, 0, 2] = true := by decide +kernel
theorem sub5_51 : sub5 [-4, 0, 3] = true := by decide +kernel
theorem sub5_52 : sub5 [-4, 0, 4] = true := by decide +kernel
theorem sub5_53 : sub5 [-4, 0, 5] = true := by decide +kernel
theorem sub5_54 : sub5 [-4, 1, -9] = true := by decide +kernel
theorem sub5_55 : sub5 [-4, 1, -8] = true := by decide +kernel
theorem sub5_56 : sub5 [-4, 1, -7] = true := by decide +kernel
theorem sub5_57 : sub5 [-4, 1, -6] = true := by decide +kernel
theorem sub5_58 : sub5 [-4, 1, -5] = true := by decide +kernel
theorem sub5_59 : sub5 [-4, 1, -4] = true := by decide +kernel
theorem sub5_60 : sub5 [-4, 1, -3] = true := by decide +kernel
theorem sub5_61 : sub5 [-4, 1, -2] = true := by decide +kernel
theorem sub5_62 : sub5 [-4, 1, -1] = true := by decide +kernel
theorem sub5_63 : sub5 [-4, 1, 0] = true := by decide +kernel
theorem sb5_1 : ∀ q ∈ blk5_1, sub5 q = true := by
  unfold blk5_1
  exact List.forall_mem_cons.2 ⟨sub5_32, List.forall_mem_cons.2 ⟨sub5_33, List.forall_mem_cons.2 ⟨sub5_34, List.forall_mem_cons.2 ⟨sub5_35, List.forall_mem_cons.2 ⟨sub5_36, List.forall_mem_cons.2 ⟨sub5_37, List.forall_mem_cons.2 ⟨sub5_38, List.forall_mem_cons.2 ⟨sub5_39, List.forall_mem_cons.2 ⟨sub5_40, List.forall_mem_cons.2 ⟨sub5_41, List.forall_mem_cons.2 ⟨sub5_42, List.forall_mem_cons.2 ⟨sub5_43, List.forall_mem_cons.2 ⟨sub5_44, List.forall_mem_cons.2 ⟨sub5_45, List.forall_mem_cons.2 ⟨sub5_46, List.forall_mem_cons.2 ⟨sub5_47, List.forall_mem_cons.2 ⟨sub5_48, List.forall_mem_cons.2 ⟨sub5_49, List.forall_mem_cons.2 ⟨sub5_50, List.forall_mem_cons.2 ⟨sub5_51, List.forall_mem_cons.2 ⟨sub5_52, List.forall_mem_cons.2 ⟨sub5_53, List.forall_mem_cons.2 ⟨sub5_54, List.forall_mem_cons.2 ⟨sub5_55, List.forall_mem_cons.2 ⟨sub5_56, List.forall_mem_cons.2 ⟨sub5_57, List.forall_mem_cons.2 ⟨sub5_58, List.forall_mem_cons.2 ⟨sub5_59, List.forall_mem_cons.2 ⟨sub5_60, List.forall_mem_cons.2 ⟨sub5_61, List.forall_mem_cons.2 ⟨sub5_62, List.forall_mem_cons.2 ⟨sub5_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_64 : sub5 [-4, 1, 1] = true := by decide +kernel
theorem sub5_65 : sub5 [-4, 1, 2] = true := by decide +kernel
theorem sub5_66 : sub5 [-4, 1, 3] = true := by decide +kernel
theorem sub5_67 : sub5 [-4, 1, 4] = true := by decide +kernel
theorem sub5_68 : sub5 [-4, 1, 5] = true := by decide +kernel
theorem sub5_69 : sub5 [-4, 2, -9] = true := by decide +kernel
theorem sub5_70 : sub5 [-4, 2, -8] = true := by decide +kernel
theorem sub5_71 : sub5 [-4, 2, -7] = true := by decide +kernel
theorem sub5_72 : sub5 [-4, 2, -6] = true := by decide +kernel
theorem sub5_73 : sub5 [-4, 2, -5] = true := by decide +kernel
theorem sub5_74 : sub5 [-4, 2, -4] = true := by decide +kernel
theorem sub5_75 : sub5 [-4, 2, -3] = true := by decide +kernel
theorem sub5_76 : sub5 [-4, 2, -2] = true := by decide +kernel
theorem sub5_77 : sub5 [-4, 2, -1] = true := by decide +kernel
theorem sub5_78 : sub5 [-4, 2, 0] = true := by decide +kernel
theorem sub5_79 : sub5 [-4, 2, 1] = true := by decide +kernel
theorem sub5_80 : sub5 [-4, 2, 2] = true := by decide +kernel
theorem sub5_81 : sub5 [-4, 2, 3] = true := by decide +kernel
theorem sub5_82 : sub5 [-4, 2, 4] = true := by decide +kernel
theorem sub5_83 : sub5 [-4, 3] = true := by decide +kernel
theorem sub5_84 : sub5 [-4, 4] = true := by decide +kernel
theorem sub5_85 : sub5 [-4, 5] = true := by decide +kernel
theorem sub5_86 : sub5 [-3, -6] = true := by decide +kernel
theorem sub5_87 : sub5 [-3, -5] = true := by decide +kernel
theorem sub5_88 : sub5 [-3, -4] = true := by decide +kernel
theorem sub5_89 : sub5 [-3, -3] = true := by decide +kernel
theorem sub5_90 : sub5 [-3, -2, -8] = true := by decide +kernel
theorem sub5_91 : sub5 [-3, -2, -7] = true := by decide +kernel
theorem sub5_92 : sub5 [-3, -2, -6] = true := by decide +kernel
theorem sub5_93 : sub5 [-3, -2, -5] = true := by decide +kernel
theorem sub5_94 : sub5 [-3, -2, -4] = true := by decide +kernel
theorem sub5_95 : sub5 [-3, -2, -3] = true := by decide +kernel
theorem sb5_2 : ∀ q ∈ blk5_2, sub5 q = true := by
  unfold blk5_2
  exact List.forall_mem_cons.2 ⟨sub5_64, List.forall_mem_cons.2 ⟨sub5_65, List.forall_mem_cons.2 ⟨sub5_66, List.forall_mem_cons.2 ⟨sub5_67, List.forall_mem_cons.2 ⟨sub5_68, List.forall_mem_cons.2 ⟨sub5_69, List.forall_mem_cons.2 ⟨sub5_70, List.forall_mem_cons.2 ⟨sub5_71, List.forall_mem_cons.2 ⟨sub5_72, List.forall_mem_cons.2 ⟨sub5_73, List.forall_mem_cons.2 ⟨sub5_74, List.forall_mem_cons.2 ⟨sub5_75, List.forall_mem_cons.2 ⟨sub5_76, List.forall_mem_cons.2 ⟨sub5_77, List.forall_mem_cons.2 ⟨sub5_78, List.forall_mem_cons.2 ⟨sub5_79, List.forall_mem_cons.2 ⟨sub5_80, List.forall_mem_cons.2 ⟨sub5_81, List.forall_mem_cons.2 ⟨sub5_82, List.forall_mem_cons.2 ⟨sub5_83, List.forall_mem_cons.2 ⟨sub5_84, List.forall_mem_cons.2 ⟨sub5_85, List.forall_mem_cons.2 ⟨sub5_86, List.forall_mem_cons.2 ⟨sub5_87, List.forall_mem_cons.2 ⟨sub5_88, List.forall_mem_cons.2 ⟨sub5_89, List.forall_mem_cons.2 ⟨sub5_90, List.forall_mem_cons.2 ⟨sub5_91, List.forall_mem_cons.2 ⟨sub5_92, List.forall_mem_cons.2 ⟨sub5_93, List.forall_mem_cons.2 ⟨sub5_94, List.forall_mem_cons.2 ⟨sub5_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_96 : sub5 [-3, -2, -2] = true := by decide +kernel
theorem sub5_97 : sub5 [-3, -2, -1] = true := by decide +kernel
theorem sub5_98 : sub5 [-3, -2, 0] = true := by decide +kernel
theorem sub5_99 : sub5 [-3, -2, 1] = true := by decide +kernel
theorem sub5_100 : sub5 [-3, -2, 2] = true := by decide +kernel
theorem sub5_101 : sub5 [-3, -2, 3] = true := by decide +kernel
theorem sub5_102 : sub5 [-3, -2, 4] = true := by decide +kernel
theorem sub5_103 : sub5 [-3, -2, 5] = true := by decide +kernel
theorem sub5_104 : sub5 [-3, -2, 6] = true := by decide +kernel
theorem sub5_105 : sub5 [-3, -1, -9] = true := by decide +kernel
theorem sub5_106 : sub5 [-3, -1, -8] = true := by decide +kernel
theorem sub5_107 : sub5 [-3, -1, -7] = true := by decide +kernel
theorem sub5_108 : sub5 [-3, -1, -6] = true := by decide +kernel
theorem sub5_109 : sub5 [-3, -1, -5] = true := by decide +kernel
theorem sub5_110 : sub5 [-3, -1, -4] = true := by decide +kernel
theorem sub5_111 : sub5 [-3, -1, -3] = true := by decide +kernel
theorem sub5_112 : sub5 [-3, -1, -2] = true := by decide +kernel
theorem sub5_113 : sub5 [-3, -1, -1] = true := by decide +kernel
theorem sub5_114 : sub5 [-3, -1, 0] = true := by decide +kernel
theorem sub5_115 : sub5 [-3, -1, 1] = true := by decide +kernel
theorem sub5_116 : sub5 [-3, -1, 2] = true := by decide +kernel
theorem sub5_117 : sub5 [-3, -1, 3] = true := by decide +kernel
theorem sub5_118 : sub5 [-3, -1, 4] = true := by decide +kernel
theorem sub5_119 : sub5 [-3, -1, 5] = true := by decide +kernel
theorem sub5_120 : sub5 [-3, -1, 6] = true := by decide +kernel
theorem sub5_121 : sub5 [-3, 0, -9] = true := by decide +kernel
theorem sub5_122 : sub5 [-3, 0, -8] = true := by decide +kernel
theorem sub5_123 : sub5 [-3, 0, -7] = true := by decide +kernel
theorem sub5_124 : sub5 [-3, 0, -6] = true := by decide +kernel
theorem sub5_125 : sub5 [-3, 0, -5] = true := by decide +kernel
theorem sub5_126 : sub5 [-3, 0, -4] = true := by decide +kernel
theorem sub5_127 : sub5 [-3, 0, -3] = true := by decide +kernel
theorem sb5_3 : ∀ q ∈ blk5_3, sub5 q = true := by
  unfold blk5_3
  exact List.forall_mem_cons.2 ⟨sub5_96, List.forall_mem_cons.2 ⟨sub5_97, List.forall_mem_cons.2 ⟨sub5_98, List.forall_mem_cons.2 ⟨sub5_99, List.forall_mem_cons.2 ⟨sub5_100, List.forall_mem_cons.2 ⟨sub5_101, List.forall_mem_cons.2 ⟨sub5_102, List.forall_mem_cons.2 ⟨sub5_103, List.forall_mem_cons.2 ⟨sub5_104, List.forall_mem_cons.2 ⟨sub5_105, List.forall_mem_cons.2 ⟨sub5_106, List.forall_mem_cons.2 ⟨sub5_107, List.forall_mem_cons.2 ⟨sub5_108, List.forall_mem_cons.2 ⟨sub5_109, List.forall_mem_cons.2 ⟨sub5_110, List.forall_mem_cons.2 ⟨sub5_111, List.forall_mem_cons.2 ⟨sub5_112, List.forall_mem_cons.2 ⟨sub5_113, List.forall_mem_cons.2 ⟨sub5_114, List.forall_mem_cons.2 ⟨sub5_115, List.forall_mem_cons.2 ⟨sub5_116, List.forall_mem_cons.2 ⟨sub5_117, List.forall_mem_cons.2 ⟨sub5_118, List.forall_mem_cons.2 ⟨sub5_119, List.forall_mem_cons.2 ⟨sub5_120, List.forall_mem_cons.2 ⟨sub5_121, List.forall_mem_cons.2 ⟨sub5_122, List.forall_mem_cons.2 ⟨sub5_123, List.forall_mem_cons.2 ⟨sub5_124, List.forall_mem_cons.2 ⟨sub5_125, List.forall_mem_cons.2 ⟨sub5_126, List.forall_mem_cons.2 ⟨sub5_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_128 : sub5 [-3, 0, -2] = true := by decide +kernel
theorem sub5_129 : sub5 [-3, 0, -1] = true := by decide +kernel
theorem sub5_130 : sub5 [-3, 0, 0] = true := by decide +kernel
theorem sub5_131 : sub5 [-3, 0, 1] = true := by decide +kernel
theorem sub5_132 : sub5 [-3, 0, 2] = true := by decide +kernel
theorem sub5_133 : sub5 [-3, 0, 3] = true := by decide +kernel
theorem sub5_134 : sub5 [-3, 0, 4] = true := by decide +kernel
theorem sub5_135 : sub5 [-3, 0, 5] = true := by decide +kernel
theorem sub5_136 : sub5 [-3, 0, 6] = true := by decide +kernel
theorem sub5_137 : sub5 [-3, 1, -9] = true := by decide +kernel
theorem sub5_138 : sub5 [-3, 1, -8] = true := by decide +kernel
theorem sub5_139 : sub5 [-3, 1, -7] = true := by decide +kernel
theorem sub5_140 : sub5 [-3, 1, -6] = true := by decide +kernel
theorem sub5_141 : sub5 [-3, 1, -5] = true := by decide +kernel
theorem sub5_142 : sub5 [-3, 1, -4] = true := by decide +kernel
theorem sub5_143 : sub5 [-3, 1, -3] = true := by decide +kernel
theorem sub5_144 : sub5 [-3, 1, -2] = true := by decide +kernel
theorem sub5_145 : sub5 [-3, 1, -1] = true := by decide +kernel
theorem sub5_146 : sub5 [-3, 1, 0] = true := by decide +kernel
theorem sub5_147 : sub5 [-3, 1, 1] = true := by decide +kernel
theorem sub5_148 : sub5 [-3, 1, 2] = true := by decide +kernel
theorem sub5_149 : sub5 [-3, 1, 3] = true := by decide +kernel
theorem sub5_150 : sub5 [-3, 1, 4] = true := by decide +kernel
theorem sub5_151 : sub5 [-3, 1, 5] = true := by decide +kernel
theorem sub5_152 : sub5 [-3, 1, 6] = true := by decide +kernel
theorem sub5_153 : sub5 [-3, 2, -9] = true := by decide +kernel
theorem sub5_154 : sub5 [-3, 2, -8] = true := by decide +kernel
theorem sub5_155 : sub5 [-3, 2, -7] = true := by decide +kernel
theorem sub5_156 : sub5 [-3, 2, -6] = true := by decide +kernel
theorem sub5_157 : sub5 [-3, 2, -5] = true := by decide +kernel
theorem sub5_158 : sub5 [-3, 2, -4] = true := by decide +kernel
theorem sub5_159 : sub5 [-3, 2, -3] = true := by decide +kernel
theorem sb5_4 : ∀ q ∈ blk5_4, sub5 q = true := by
  unfold blk5_4
  exact List.forall_mem_cons.2 ⟨sub5_128, List.forall_mem_cons.2 ⟨sub5_129, List.forall_mem_cons.2 ⟨sub5_130, List.forall_mem_cons.2 ⟨sub5_131, List.forall_mem_cons.2 ⟨sub5_132, List.forall_mem_cons.2 ⟨sub5_133, List.forall_mem_cons.2 ⟨sub5_134, List.forall_mem_cons.2 ⟨sub5_135, List.forall_mem_cons.2 ⟨sub5_136, List.forall_mem_cons.2 ⟨sub5_137, List.forall_mem_cons.2 ⟨sub5_138, List.forall_mem_cons.2 ⟨sub5_139, List.forall_mem_cons.2 ⟨sub5_140, List.forall_mem_cons.2 ⟨sub5_141, List.forall_mem_cons.2 ⟨sub5_142, List.forall_mem_cons.2 ⟨sub5_143, List.forall_mem_cons.2 ⟨sub5_144, List.forall_mem_cons.2 ⟨sub5_145, List.forall_mem_cons.2 ⟨sub5_146, List.forall_mem_cons.2 ⟨sub5_147, List.forall_mem_cons.2 ⟨sub5_148, List.forall_mem_cons.2 ⟨sub5_149, List.forall_mem_cons.2 ⟨sub5_150, List.forall_mem_cons.2 ⟨sub5_151, List.forall_mem_cons.2 ⟨sub5_152, List.forall_mem_cons.2 ⟨sub5_153, List.forall_mem_cons.2 ⟨sub5_154, List.forall_mem_cons.2 ⟨sub5_155, List.forall_mem_cons.2 ⟨sub5_156, List.forall_mem_cons.2 ⟨sub5_157, List.forall_mem_cons.2 ⟨sub5_158, List.forall_mem_cons.2 ⟨sub5_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_160 : sub5 [-3, 2, -2] = true := by decide +kernel
theorem sub5_161 : sub5 [-3, 2, -1] = true := by decide +kernel
theorem sub5_162 : sub5 [-3, 2, 0] = true := by decide +kernel
theorem sub5_163 : sub5 [-3, 2, 1] = true := by decide +kernel
theorem sub5_164 : sub5 [-3, 2, 2] = true := by decide +kernel
theorem sub5_165 : sub5 [-3, 2, 3] = true := by decide +kernel
theorem sub5_166 : sub5 [-3, 2, 4] = true := by decide +kernel
theorem sub5_167 : sub5 [-3, 2, 5] = true := by decide +kernel
theorem sub5_168 : sub5 [-3, 3, -9] = true := by decide +kernel
theorem sub5_169 : sub5 [-3, 3, -8] = true := by decide +kernel
theorem sub5_170 : sub5 [-3, 3, -7] = true := by decide +kernel
theorem sub5_171 : sub5 [-3, 3, -6] = true := by decide +kernel
theorem sub5_172 : sub5 [-3, 3, -5] = true := by decide +kernel
theorem sub5_173 : sub5 [-3, 3, -4] = true := by decide +kernel
theorem sub5_174 : sub5 [-3, 3, -3] = true := by decide +kernel
theorem sub5_175 : sub5 [-3, 3, -2] = true := by decide +kernel
theorem sub5_176 : sub5 [-3, 3, -1] = true := by decide +kernel
theorem sub5_177 : sub5 [-3, 3, 0] = true := by decide +kernel
theorem sub5_178 : sub5 [-3, 3, 1] = true := by decide +kernel
theorem sub5_179 : sub5 [-3, 3, 2] = true := by decide +kernel
theorem sub5_180 : sub5 [-3, 3, 3] = true := by decide +kernel
theorem sub5_181 : sub5 [-3, 3, 4] = true := by decide +kernel
theorem sub5_182 : sub5 [-3, 3, 5] = true := by decide +kernel
theorem sub5_183 : sub5 [-3, 4] = true := by decide +kernel
theorem sub5_184 : sub5 [-3, 5] = true := by decide +kernel
theorem sub5_185 : sub5 [-3, 6] = true := by decide +kernel
theorem sub5_186 : sub5 [-2, -7] = true := by decide +kernel
theorem sub5_187 : sub5 [-2, -6] = true := by decide +kernel
theorem sub5_188 : sub5 [-2, -5] = true := by decide +kernel
theorem sub5_189 : sub5 [-2, -4] = true := by decide +kernel
theorem sub5_190 : sub5 [-2, -3, -8] = true := by decide +kernel
theorem sub5_191 : sub5 [-2, -3, -7] = true := by decide +kernel
theorem sb5_5 : ∀ q ∈ blk5_5, sub5 q = true := by
  unfold blk5_5
  exact List.forall_mem_cons.2 ⟨sub5_160, List.forall_mem_cons.2 ⟨sub5_161, List.forall_mem_cons.2 ⟨sub5_162, List.forall_mem_cons.2 ⟨sub5_163, List.forall_mem_cons.2 ⟨sub5_164, List.forall_mem_cons.2 ⟨sub5_165, List.forall_mem_cons.2 ⟨sub5_166, List.forall_mem_cons.2 ⟨sub5_167, List.forall_mem_cons.2 ⟨sub5_168, List.forall_mem_cons.2 ⟨sub5_169, List.forall_mem_cons.2 ⟨sub5_170, List.forall_mem_cons.2 ⟨sub5_171, List.forall_mem_cons.2 ⟨sub5_172, List.forall_mem_cons.2 ⟨sub5_173, List.forall_mem_cons.2 ⟨sub5_174, List.forall_mem_cons.2 ⟨sub5_175, List.forall_mem_cons.2 ⟨sub5_176, List.forall_mem_cons.2 ⟨sub5_177, List.forall_mem_cons.2 ⟨sub5_178, List.forall_mem_cons.2 ⟨sub5_179, List.forall_mem_cons.2 ⟨sub5_180, List.forall_mem_cons.2 ⟨sub5_181, List.forall_mem_cons.2 ⟨sub5_182, List.forall_mem_cons.2 ⟨sub5_183, List.forall_mem_cons.2 ⟨sub5_184, List.forall_mem_cons.2 ⟨sub5_185, List.forall_mem_cons.2 ⟨sub5_186, List.forall_mem_cons.2 ⟨sub5_187, List.forall_mem_cons.2 ⟨sub5_188, List.forall_mem_cons.2 ⟨sub5_189, List.forall_mem_cons.2 ⟨sub5_190, List.forall_mem_cons.2 ⟨sub5_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_192 : sub5 [-2, -3, -6] = true := by decide +kernel
theorem sub5_193 : sub5 [-2, -3, -5] = true := by decide +kernel
theorem sub5_194 : sub5 [-2, -3, -4] = true := by decide +kernel
theorem sub5_195 : sub5 [-2, -3, -3] = true := by decide +kernel
theorem sub5_196 : sub5 [-2, -3, -2] = true := by decide +kernel
theorem sub5_197 : sub5 [-2, -3, -1] = true := by decide +kernel
theorem sub5_198 : sub5 [-2, -3, 0] = true := by decide +kernel
theorem sub5_199 : sub5 [-2, -3, 1] = true := by decide +kernel
theorem sub5_200 : sub5 [-2, -3, 2] = true := by decide +kernel
theorem sub5_201 : sub5 [-2, -3, 3] = true := by decide +kernel
theorem sub5_202 : sub5 [-2, -3, 4] = true := by decide +kernel
theorem sub5_203 : sub5 [-2, -3, 5] = true := by decide +kernel
theorem sub5_204 : sub5 [-2, -3, 6] = true := by decide +kernel
theorem sub5_205 : sub5 [-2, -3, 7] = true := by decide +kernel
theorem sub5_206 : sub5 [-2, -2, -8] = true := by decide +kernel
theorem sub5_207 : sub5 [-2, -2, -7] = true := by decide +kernel
theorem sub5_208 : sub5 [-2, -2, -6] = true := by decide +kernel
theorem sub5_209 : sub5 [-2, -2, -5] = true := by decide +kernel
theorem sub5_210 : sub5 [-2, -2, -4] = true := by decide +kernel
theorem sub5_211 : sub5 [-2, -2, -3] = true := by decide +kernel
theorem sub5_212 : sub5 [-2, -2, -2] = true := by decide +kernel
theorem sub5_213 : sub5 [-2, -2, -1] = true := by decide +kernel
theorem sub5_214 : sub5 [-2, -2, 0] = true := by decide +kernel
theorem sub5_215 : sub5 [-2, -2, 1] = true := by decide +kernel
theorem sub5_216 : sub5 [-2, -2, 2] = true := by decide +kernel
theorem sub5_217 : sub5 [-2, -2, 3] = true := by decide +kernel
theorem sub5_218 : sub5 [-2, -2, 4] = true := by decide +kernel
theorem sub5_219 : sub5 [-2, -2, 5] = true := by decide +kernel
theorem sub5_220 : sub5 [-2, -2, 6] = true := by decide +kernel
theorem sub5_221 : sub5 [-2, -2, 7] = true := by decide +kernel
theorem sub5_222 : sub5 [-2, -1, -9] = true := by decide +kernel
theorem sub5_223 : sub5 [-2, -1, -8] = true := by decide +kernel
theorem sb5_6 : ∀ q ∈ blk5_6, sub5 q = true := by
  unfold blk5_6
  exact List.forall_mem_cons.2 ⟨sub5_192, List.forall_mem_cons.2 ⟨sub5_193, List.forall_mem_cons.2 ⟨sub5_194, List.forall_mem_cons.2 ⟨sub5_195, List.forall_mem_cons.2 ⟨sub5_196, List.forall_mem_cons.2 ⟨sub5_197, List.forall_mem_cons.2 ⟨sub5_198, List.forall_mem_cons.2 ⟨sub5_199, List.forall_mem_cons.2 ⟨sub5_200, List.forall_mem_cons.2 ⟨sub5_201, List.forall_mem_cons.2 ⟨sub5_202, List.forall_mem_cons.2 ⟨sub5_203, List.forall_mem_cons.2 ⟨sub5_204, List.forall_mem_cons.2 ⟨sub5_205, List.forall_mem_cons.2 ⟨sub5_206, List.forall_mem_cons.2 ⟨sub5_207, List.forall_mem_cons.2 ⟨sub5_208, List.forall_mem_cons.2 ⟨sub5_209, List.forall_mem_cons.2 ⟨sub5_210, List.forall_mem_cons.2 ⟨sub5_211, List.forall_mem_cons.2 ⟨sub5_212, List.forall_mem_cons.2 ⟨sub5_213, List.forall_mem_cons.2 ⟨sub5_214, List.forall_mem_cons.2 ⟨sub5_215, List.forall_mem_cons.2 ⟨sub5_216, List.forall_mem_cons.2 ⟨sub5_217, List.forall_mem_cons.2 ⟨sub5_218, List.forall_mem_cons.2 ⟨sub5_219, List.forall_mem_cons.2 ⟨sub5_220, List.forall_mem_cons.2 ⟨sub5_221, List.forall_mem_cons.2 ⟨sub5_222, List.forall_mem_cons.2 ⟨sub5_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C047
