import ReflectZphi.Data.Cert5.C131.Base

namespace ReflectZphi.Data.Cert5.C131

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd10_0_1408 : subd10_0 [3, 3, 1] = true := by decide +kernel
theorem subd10_0_1409 : subd10_0 [3, 3, 2] = true := by decide +kernel
theorem subd10_0_1410 : subd10_0 [3, 3, 3] = true := by decide +kernel
theorem subd10_0_1411 : subd10_0 [3, 3, 4] = true := by decide +kernel
theorem subd10_0_1412 : subd10_0 [3, 3, 5] = true := by decide +kernel
theorem subd10_0_1413 : subd10_0 [3, 3, 6] = true := by decide +kernel
theorem subd10_0_1414 : subd10_0 [3, 3, 7] = true := by decide +kernel
theorem subd10_0_1415 : subd10_0 [3, 4, -7] = true := by decide +kernel
theorem subd10_0_1416 : subd10_0 [3, 4, -6] = true := by decide +kernel
theorem subd10_0_1417 : subd10_0 [3, 4, -5] = true := by decide +kernel
theorem subd10_0_1418 : subd10_0 [3, 4, -4] = true := by decide +kernel
theorem subd10_0_1419 : subd10_0 [3, 4, -3] = true := by decide +kernel
theorem subd10_0_1420 : subd10_0 [3, 4, -2] = true := by decide +kernel
theorem subd10_0_1421 : subd10_0 [3, 4, -1] = true := by decide +kernel
theorem subd10_0_1422 : subd10_0 [3, 4, 0] = true := by decide +kernel
theorem subd10_0_1423 : subd10_0 [3, 4, 1] = true := by decide +kernel
theorem subd10_0_1424 : subd10_0 [3, 4, 2] = true := by decide +kernel
theorem subd10_0_1425 : subd10_0 [3, 4, 3] = true := by decide +kernel
theorem subd10_0_1426 : subd10_0 [3, 4, 4] = true := by decide +kernel
theorem subd10_0_1427 : subd10_0 [3, 4, 5] = true := by decide +kernel
theorem subd10_0_1428 : subd10_0 [3, 4, 6] = true := by decide +kernel
theorem subd10_0_1429 : subd10_0 [3, 5] = true := by decide +kernel
theorem subd10_0_1430 : subd10_0 [3, 6] = true := by decide +kernel
theorem subd10_0_1431 : subd10_0 [4, -7] = true := by decide +kernel
theorem subd10_0_1432 : subd10_0 [4, -6] = true := by decide +kernel
theorem subd10_0_1433 : subd10_0 [4, -5] = true := by decide +kernel
theorem subd10_0_1434 : subd10_0 [4, -4, -5] = true := by decide +kernel
theorem subd10_0_1435 : subd10_0 [4, -4, -4] = true := by decide +kernel
theorem subd10_0_1436 : subd10_0 [4, -4, -3] = true := by decide +kernel
theorem subd10_0_1437 : subd10_0 [4, -4, -2] = true := by decide +kernel
theorem subd10_0_1438 : subd10_0 [4, -4, -1] = true := by decide +kernel
theorem subd10_0_1439 : subd10_0 [4, -4, 0] = true := by decide +kernel
theorem sbd10_0_44 : ∀ q ∈ blkd10_0_44, subd10_0 q = true := by
  unfold blkd10_0_44
  exact List.forall_mem_cons.2 ⟨subd10_0_1408, List.forall_mem_cons.2 ⟨subd10_0_1409, List.forall_mem_cons.2 ⟨subd10_0_1410, List.forall_mem_cons.2 ⟨subd10_0_1411, List.forall_mem_cons.2 ⟨subd10_0_1412, List.forall_mem_cons.2 ⟨subd10_0_1413, List.forall_mem_cons.2 ⟨subd10_0_1414, List.forall_mem_cons.2 ⟨subd10_0_1415, List.forall_mem_cons.2 ⟨subd10_0_1416, List.forall_mem_cons.2 ⟨subd10_0_1417, List.forall_mem_cons.2 ⟨subd10_0_1418, List.forall_mem_cons.2 ⟨subd10_0_1419, List.forall_mem_cons.2 ⟨subd10_0_1420, List.forall_mem_cons.2 ⟨subd10_0_1421, List.forall_mem_cons.2 ⟨subd10_0_1422, List.forall_mem_cons.2 ⟨subd10_0_1423, List.forall_mem_cons.2 ⟨subd10_0_1424, List.forall_mem_cons.2 ⟨subd10_0_1425, List.forall_mem_cons.2 ⟨subd10_0_1426, List.forall_mem_cons.2 ⟨subd10_0_1427, List.forall_mem_cons.2 ⟨subd10_0_1428, List.forall_mem_cons.2 ⟨subd10_0_1429, List.forall_mem_cons.2 ⟨subd10_0_1430, List.forall_mem_cons.2 ⟨subd10_0_1431, List.forall_mem_cons.2 ⟨subd10_0_1432, List.forall_mem_cons.2 ⟨subd10_0_1433, List.forall_mem_cons.2 ⟨subd10_0_1434, List.forall_mem_cons.2 ⟨subd10_0_1435, List.forall_mem_cons.2 ⟨subd10_0_1436, List.forall_mem_cons.2 ⟨subd10_0_1437, List.forall_mem_cons.2 ⟨subd10_0_1438, List.forall_mem_cons.2 ⟨subd10_0_1439, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_1440 : subd10_0 [4, -4, 1] = true := by decide +kernel
theorem subd10_0_1441 : subd10_0 [4, -4, 2] = true := by decide +kernel
theorem subd10_0_1442 : subd10_0 [4, -4, 3] = true := by decide +kernel
theorem subd10_0_1443 : subd10_0 [4, -4, 4] = true := by decide +kernel
theorem subd10_0_1444 : subd10_0 [4, -4, 5] = true := by decide +kernel
theorem subd10_0_1445 : subd10_0 [4, -4, 6] = true := by decide +kernel
theorem subd10_0_1446 : subd10_0 [4, -4, 7] = true := by decide +kernel
theorem subd10_0_1447 : subd10_0 [4, -3, -6] = true := by decide +kernel
theorem subd10_0_1448 : subd10_0 [4, -3, -5] = true := by decide +kernel
theorem subd10_0_1449 : subd10_0 [4, -3, -4] = true := by decide +kernel
theorem subd10_0_1450 : subd10_0 [4, -3, -3] = true := by decide +kernel
theorem subd10_0_1451 : subd10_0 [4, -3, -2] = true := by decide +kernel
theorem subd10_0_1452 : subd10_0 [4, -3, -1] = true := by decide +kernel
theorem subd10_0_1453 : subd10_0 [4, -3, 0] = true := by decide +kernel
theorem subd10_0_1454 : subd10_0 [4, -3, 1] = true := by decide +kernel
theorem subd10_0_1455 : subd10_0 [4, -3, 2] = true := by decide +kernel
theorem subd10_0_1456 : subd10_0 [4, -3, 3] = true := by decide +kernel
theorem subd10_0_1457 : subd10_0 [4, -3, 4] = true := by decide +kernel
theorem subd10_0_1458 : subd10_0 [4, -3, 5] = true := by decide +kernel
theorem subd10_0_1459 : subd10_0 [4, -3, 6] = true := by decide +kernel
theorem subd10_0_1460 : subd10_0 [4, -3, 7] = true := by decide +kernel
theorem subd10_0_1461 : subd10_0 [4, -3, 8] = true := by decide +kernel
theorem subd10_0_1462 : subd10_0 [4, -2, -6] = true := by decide +kernel
theorem subd10_0_1463 : subd10_0 [4, -2, -5] = true := by decide +kernel
theorem subd10_0_1464 : subd10_0 [4, -2, -4] = true := by decide +kernel
theorem subd10_0_1465 : subd10_0 [4, -2, -3] = true := by decide +kernel
theorem subd10_0_1466 : subd10_0 [4, -2, -2] = true := by decide +kernel
theorem subd10_0_1467 : subd10_0 [4, -2, -1] = true := by decide +kernel
theorem subd10_0_1468 : subd10_0 [4, -2, 0] = true := by decide +kernel
theorem subd10_0_1469 : subd10_0 [4, -2, 1] = true := by decide +kernel
theorem subd10_0_1470 : subd10_0 [4, -2, 2] = true := by decide +kernel
theorem subd10_0_1471 : subd10_0 [4, -2, 3] = true := by decide +kernel
theorem sbd10_0_45 : ∀ q ∈ blkd10_0_45, subd10_0 q = true := by
  unfold blkd10_0_45
  exact List.forall_mem_cons.2 ⟨subd10_0_1440, List.forall_mem_cons.2 ⟨subd10_0_1441, List.forall_mem_cons.2 ⟨subd10_0_1442, List.forall_mem_cons.2 ⟨subd10_0_1443, List.forall_mem_cons.2 ⟨subd10_0_1444, List.forall_mem_cons.2 ⟨subd10_0_1445, List.forall_mem_cons.2 ⟨subd10_0_1446, List.forall_mem_cons.2 ⟨subd10_0_1447, List.forall_mem_cons.2 ⟨subd10_0_1448, List.forall_mem_cons.2 ⟨subd10_0_1449, List.forall_mem_cons.2 ⟨subd10_0_1450, List.forall_mem_cons.2 ⟨subd10_0_1451, List.forall_mem_cons.2 ⟨subd10_0_1452, List.forall_mem_cons.2 ⟨subd10_0_1453, List.forall_mem_cons.2 ⟨subd10_0_1454, List.forall_mem_cons.2 ⟨subd10_0_1455, List.forall_mem_cons.2 ⟨subd10_0_1456, List.forall_mem_cons.2 ⟨subd10_0_1457, List.forall_mem_cons.2 ⟨subd10_0_1458, List.forall_mem_cons.2 ⟨subd10_0_1459, List.forall_mem_cons.2 ⟨subd10_0_1460, List.forall_mem_cons.2 ⟨subd10_0_1461, List.forall_mem_cons.2 ⟨subd10_0_1462, List.forall_mem_cons.2 ⟨subd10_0_1463, List.forall_mem_cons.2 ⟨subd10_0_1464, List.forall_mem_cons.2 ⟨subd10_0_1465, List.forall_mem_cons.2 ⟨subd10_0_1466, List.forall_mem_cons.2 ⟨subd10_0_1467, List.forall_mem_cons.2 ⟨subd10_0_1468, List.forall_mem_cons.2 ⟨subd10_0_1469, List.forall_mem_cons.2 ⟨subd10_0_1470, List.forall_mem_cons.2 ⟨subd10_0_1471, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_1472 : subd10_0 [4, -2, 4] = true := by decide +kernel
theorem subd10_0_1473 : subd10_0 [4, -2, 5] = true := by decide +kernel
theorem subd10_0_1474 : subd10_0 [4, -2, 6] = true := by decide +kernel
theorem subd10_0_1475 : subd10_0 [4, -2, 7] = true := by decide +kernel
theorem subd10_0_1476 : subd10_0 [4, -2, 8] = true := by decide +kernel
theorem subd10_0_1477 : subd10_0 [4, -1, -7] = true := by decide +kernel
theorem subd10_0_1478 : subd10_0 [4, -1, -6] = true := by decide +kernel
theorem subd10_0_1479 : subd10_0 [4, -1, -5] = true := by decide +kernel
theorem subd10_0_1480 : subd10_0 [4, -1, -4] = true := by decide +kernel
theorem subd10_0_1481 : subd10_0 [4, -1, -3] = true := by decide +kernel
theorem subd10_0_1482 : subd10_0 [4, -1, -2] = true := by decide +kernel
theorem subd10_0_1483 : subd10_0 [4, -1, -1] = true := by decide +kernel
theorem subd10_0_1484 : subd10_0 [4, -1, 0] = true := by decide +kernel
theorem subd10_0_1485 : subd10_0 [4, -1, 1] = true := by decide +kernel
theorem subd10_0_1486 : subd10_0 [4, -1, 2] = true := by decide +kernel
theorem subd10_0_1487 : subd10_0 [4, -1, 3] = true := by decide +kernel
theorem subd10_0_1488 : subd10_0 [4, -1, 4] = true := by decide +kernel
theorem subd10_0_1489 : subd10_0 [4, -1, 5] = true := by decide +kernel
theorem subd10_0_1490 : subd10_0 [4, -1, 6] = true := by decide +kernel
theorem subd10_0_1491 : subd10_0 [4, -1, 7] = true := by decide +kernel
theorem subd10_0_1492 : subd10_0 [4, -1, 8] = true := by decide +kernel
theorem subd10_0_1493 : subd10_0 [4, 0, -7] = true := by decide +kernel
theorem subd10_0_1494 : subd10_0 [4, 0, -6] = true := by decide +kernel
theorem subd10_0_1495 : subd10_0 [4, 0, -5] = true := by decide +kernel
theorem subd10_0_1496 : subd10_0 [4, 0, -4] = true := by decide +kernel
theorem subd10_0_1497 : subd10_0 [4, 0, -3] = true := by decide +kernel
theorem subd10_0_1498 : subd10_0 [4, 0, -2] = true := by decide +kernel
theorem subd10_0_1499 : subd10_0 [4, 0, -1] = true := by decide +kernel
theorem subd10_0_1500 : subd10_0 [4, 0, 0] = true := by decide +kernel
theorem subd10_0_1501 : subd10_0 [4, 0, 1] = true := by decide +kernel
theorem subd10_0_1502 : subd10_0 [4, 0, 2] = true := by decide +kernel
theorem subd10_0_1503 : subd10_0 [4, 0, 3] = true := by decide +kernel
theorem sbd10_0_46 : ∀ q ∈ blkd10_0_46, subd10_0 q = true := by
  unfold blkd10_0_46
  exact List.forall_mem_cons.2 ⟨subd10_0_1472, List.forall_mem_cons.2 ⟨subd10_0_1473, List.forall_mem_cons.2 ⟨subd10_0_1474, List.forall_mem_cons.2 ⟨subd10_0_1475, List.forall_mem_cons.2 ⟨subd10_0_1476, List.forall_mem_cons.2 ⟨subd10_0_1477, List.forall_mem_cons.2 ⟨subd10_0_1478, List.forall_mem_cons.2 ⟨subd10_0_1479, List.forall_mem_cons.2 ⟨subd10_0_1480, List.forall_mem_cons.2 ⟨subd10_0_1481, List.forall_mem_cons.2 ⟨subd10_0_1482, List.forall_mem_cons.2 ⟨subd10_0_1483, List.forall_mem_cons.2 ⟨subd10_0_1484, List.forall_mem_cons.2 ⟨subd10_0_1485, List.forall_mem_cons.2 ⟨subd10_0_1486, List.forall_mem_cons.2 ⟨subd10_0_1487, List.forall_mem_cons.2 ⟨subd10_0_1488, List.forall_mem_cons.2 ⟨subd10_0_1489, List.forall_mem_cons.2 ⟨subd10_0_1490, List.forall_mem_cons.2 ⟨subd10_0_1491, List.forall_mem_cons.2 ⟨subd10_0_1492, List.forall_mem_cons.2 ⟨subd10_0_1493, List.forall_mem_cons.2 ⟨subd10_0_1494, List.forall_mem_cons.2 ⟨subd10_0_1495, List.forall_mem_cons.2 ⟨subd10_0_1496, List.forall_mem_cons.2 ⟨subd10_0_1497, List.forall_mem_cons.2 ⟨subd10_0_1498, List.forall_mem_cons.2 ⟨subd10_0_1499, List.forall_mem_cons.2 ⟨subd10_0_1500, List.forall_mem_cons.2 ⟨subd10_0_1501, List.forall_mem_cons.2 ⟨subd10_0_1502, List.forall_mem_cons.2 ⟨subd10_0_1503, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_1504 : subd10_0 [4, 0, 4] = true := by decide +kernel
theorem subd10_0_1505 : subd10_0 [4, 0, 5] = true := by decide +kernel
theorem subd10_0_1506 : subd10_0 [4, 0, 6] = true := by decide +kernel
theorem subd10_0_1507 : subd10_0 [4, 0, 7] = true := by decide +kernel
theorem subd10_0_1508 : subd10_0 [4, 0, 8] = true := by decide +kernel
theorem subd10_0_1509 : subd10_0 [4, 1, -7] = true := by decide +kernel
theorem subd10_0_1510 : subd10_0 [4, 1, -6] = true := by decide +kernel
theorem subd10_0_1511 : subd10_0 [4, 1, -5] = true := by decide +kernel
theorem subd10_0_1512 : subd10_0 [4, 1, -4] = true := by decide +kernel
theorem subd10_0_1513 : subd10_0 [4, 1, -3] = true := by decide +kernel
theorem subd10_0_1514 : subd10_0 [4, 1, -2] = true := by decide +kernel
theorem subd10_0_1515 : subd10_0 [4, 1, -1] = true := by decide +kernel
theorem subd10_0_1516 : subd10_0 [4, 1, 0] = true := by decide +kernel
theorem subd10_0_1517 : subd10_0 [4, 1, 1] = true := by decide +kernel
theorem subd10_0_1518 : subd10_0 [4, 1, 2] = true := by decide +kernel
theorem subd10_0_1519 : subd10_0 [4, 1, 3] = true := by decide +kernel
theorem subd10_0_1520 : subd10_0 [4, 1, 4] = true := by decide +kernel
theorem subd10_0_1521 : subd10_0 [4, 1, 5] = true := by decide +kernel
theorem subd10_0_1522 : subd10_0 [4, 1, 6] = true := by decide +kernel
theorem subd10_0_1523 : subd10_0 [4, 1, 7] = true := by decide +kernel
theorem subd10_0_1524 : subd10_0 [4, 1, 8] = true := by decide +kernel
theorem subd10_0_1525 : subd10_0 [4, 2, -7] = true := by decide +kernel
theorem subd10_0_1526 : subd10_0 [4, 2, -6] = true := by decide +kernel
theorem subd10_0_1527 : subd10_0 [4, 2, -5] = true := by decide +kernel
theorem subd10_0_1528 : subd10_0 [4, 2, -4] = true := by decide +kernel
theorem subd10_0_1529 : subd10_0 [4, 2, -3] = true := by decide +kernel
theorem subd10_0_1530 : subd10_0 [4, 2, -2] = true := by decide +kernel
theorem subd10_0_1531 : subd10_0 [4, 2, -1] = true := by decide +kernel
theorem subd10_0_1532 : subd10_0 [4, 2, 0] = true := by decide +kernel
theorem subd10_0_1533 : subd10_0 [4, 2, 1] = true := by decide +kernel
theorem subd10_0_1534 : subd10_0 [4, 2, 2] = true := by decide +kernel
theorem subd10_0_1535 : subd10_0 [4, 2, 3] = true := by decide +kernel
theorem sbd10_0_47 : ∀ q ∈ blkd10_0_47, subd10_0 q = true := by
  unfold blkd10_0_47
  exact List.forall_mem_cons.2 ⟨subd10_0_1504, List.forall_mem_cons.2 ⟨subd10_0_1505, List.forall_mem_cons.2 ⟨subd10_0_1506, List.forall_mem_cons.2 ⟨subd10_0_1507, List.forall_mem_cons.2 ⟨subd10_0_1508, List.forall_mem_cons.2 ⟨subd10_0_1509, List.forall_mem_cons.2 ⟨subd10_0_1510, List.forall_mem_cons.2 ⟨subd10_0_1511, List.forall_mem_cons.2 ⟨subd10_0_1512, List.forall_mem_cons.2 ⟨subd10_0_1513, List.forall_mem_cons.2 ⟨subd10_0_1514, List.forall_mem_cons.2 ⟨subd10_0_1515, List.forall_mem_cons.2 ⟨subd10_0_1516, List.forall_mem_cons.2 ⟨subd10_0_1517, List.forall_mem_cons.2 ⟨subd10_0_1518, List.forall_mem_cons.2 ⟨subd10_0_1519, List.forall_mem_cons.2 ⟨subd10_0_1520, List.forall_mem_cons.2 ⟨subd10_0_1521, List.forall_mem_cons.2 ⟨subd10_0_1522, List.forall_mem_cons.2 ⟨subd10_0_1523, List.forall_mem_cons.2 ⟨subd10_0_1524, List.forall_mem_cons.2 ⟨subd10_0_1525, List.forall_mem_cons.2 ⟨subd10_0_1526, List.forall_mem_cons.2 ⟨subd10_0_1527, List.forall_mem_cons.2 ⟨subd10_0_1528, List.forall_mem_cons.2 ⟨subd10_0_1529, List.forall_mem_cons.2 ⟨subd10_0_1530, List.forall_mem_cons.2 ⟨subd10_0_1531, List.forall_mem_cons.2 ⟨subd10_0_1532, List.forall_mem_cons.2 ⟨subd10_0_1533, List.forall_mem_cons.2 ⟨subd10_0_1534, List.forall_mem_cons.2 ⟨subd10_0_1535, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_1536 : subd10_0 [4, 2, 4] = true := by decide +kernel
theorem subd10_0_1537 : subd10_0 [4, 2, 5] = true := by decide +kernel
theorem subd10_0_1538 : subd10_0 [4, 2, 6] = true := by decide +kernel
theorem subd10_0_1539 : subd10_0 [4, 2, 7] = true := by decide +kernel
theorem subd10_0_1540 : subd10_0 [4, 3, -7] = true := by decide +kernel
theorem subd10_0_1541 : subd10_0 [4, 3, -6] = true := by decide +kernel
theorem subd10_0_1542 : subd10_0 [4, 3, -5] = true := by decide +kernel
theorem subd10_0_1543 : subd10_0 [4, 3, -4] = true := by decide +kernel
theorem subd10_0_1544 : subd10_0 [4, 3, -3] = true := by decide +kernel
theorem subd10_0_1545 : subd10_0 [4, 3, -2] = true := by decide +kernel
theorem subd10_0_1546 : subd10_0 [4, 3, -1] = true := by decide +kernel
theorem subd10_0_1547 : subd10_0 [4, 3, 0] = true := by decide +kernel
theorem subd10_0_1548 : subd10_0 [4, 3, 1] = true := by decide +kernel
theorem subd10_0_1549 : subd10_0 [4, 3, 2] = true := by decide +kernel
theorem subd10_0_1550 : subd10_0 [4, 3, 3] = true := by decide +kernel
theorem subd10_0_1551 : subd10_0 [4, 3, 4] = true := by decide +kernel
theorem subd10_0_1552 : subd10_0 [4, 3, 5] = true := by decide +kernel
theorem subd10_0_1553 : subd10_0 [4, 3, 6] = true := by decide +kernel
theorem subd10_0_1554 : subd10_0 [4, 4] = true := by decide +kernel
theorem subd10_0_1555 : subd10_0 [4, 5] = true := by decide +kernel
theorem subd10_0_1556 : subd10_0 [4, 6] = true := by decide +kernel
theorem subd10_0_1557 : subd10_0 [5, -7] = true := by decide +kernel
theorem subd10_0_1558 : subd10_0 [5, -6] = true := by decide +kernel
theorem subd10_0_1559 : subd10_0 [5, -5] = true := by decide +kernel
theorem subd10_0_1560 : subd10_0 [5, -4] = true := by decide +kernel
theorem subd10_0_1561 : subd10_0 [5, -3] = true := by decide +kernel
theorem subd10_0_1562 : subd10_0 [5, -2, -5] = true := by decide +kernel
theorem subd10_0_1563 : subd10_0 [5, -2, -4] = true := by decide +kernel
theorem subd10_0_1564 : subd10_0 [5, -2, -3] = true := by decide +kernel
theorem subd10_0_1565 : subd10_0 [5, -2, -2] = true := by decide +kernel
theorem subd10_0_1566 : subd10_0 [5, -2, -1] = true := by decide +kernel
theorem subd10_0_1567 : subd10_0 [5, -2, 0] = true := by decide +kernel
theorem sbd10_0_48 : ∀ q ∈ blkd10_0_48, subd10_0 q = true := by
  unfold blkd10_0_48
  exact List.forall_mem_cons.2 ⟨subd10_0_1536, List.forall_mem_cons.2 ⟨subd10_0_1537, List.forall_mem_cons.2 ⟨subd10_0_1538, List.forall_mem_cons.2 ⟨subd10_0_1539, List.forall_mem_cons.2 ⟨subd10_0_1540, List.forall_mem_cons.2 ⟨subd10_0_1541, List.forall_mem_cons.2 ⟨subd10_0_1542, List.forall_mem_cons.2 ⟨subd10_0_1543, List.forall_mem_cons.2 ⟨subd10_0_1544, List.forall_mem_cons.2 ⟨subd10_0_1545, List.forall_mem_cons.2 ⟨subd10_0_1546, List.forall_mem_cons.2 ⟨subd10_0_1547, List.forall_mem_cons.2 ⟨subd10_0_1548, List.forall_mem_cons.2 ⟨subd10_0_1549, List.forall_mem_cons.2 ⟨subd10_0_1550, List.forall_mem_cons.2 ⟨subd10_0_1551, List.forall_mem_cons.2 ⟨subd10_0_1552, List.forall_mem_cons.2 ⟨subd10_0_1553, List.forall_mem_cons.2 ⟨subd10_0_1554, List.forall_mem_cons.2 ⟨subd10_0_1555, List.forall_mem_cons.2 ⟨subd10_0_1556, List.forall_mem_cons.2 ⟨subd10_0_1557, List.forall_mem_cons.2 ⟨subd10_0_1558, List.forall_mem_cons.2 ⟨subd10_0_1559, List.forall_mem_cons.2 ⟨subd10_0_1560, List.forall_mem_cons.2 ⟨subd10_0_1561, List.forall_mem_cons.2 ⟨subd10_0_1562, List.forall_mem_cons.2 ⟨subd10_0_1563, List.forall_mem_cons.2 ⟨subd10_0_1564, List.forall_mem_cons.2 ⟨subd10_0_1565, List.forall_mem_cons.2 ⟨subd10_0_1566, List.forall_mem_cons.2 ⟨subd10_0_1567, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_1568 : subd10_0 [5, -2, 1] = true := by decide +kernel
theorem subd10_0_1569 : subd10_0 [5, -2, 2] = true := by decide +kernel
theorem subd10_0_1570 : subd10_0 [5, -2, 3] = true := by decide +kernel
theorem subd10_0_1571 : subd10_0 [5, -2, 4] = true := by decide +kernel
theorem subd10_0_1572 : subd10_0 [5, -2, 5] = true := by decide +kernel
theorem subd10_0_1573 : subd10_0 [5, -2, 6] = true := by decide +kernel
theorem subd10_0_1574 : subd10_0 [5, -2, 7] = true := by decide +kernel
theorem subd10_0_1575 : subd10_0 [5, -1, -6] = true := by decide +kernel
theorem subd10_0_1576 : subd10_0 [5, -1, -5] = true := by decide +kernel
theorem subd10_0_1577 : subd10_0 [5, -1, -4] = true := by decide +kernel
theorem subd10_0_1578 : subd10_0 [5, -1, -3] = true := by decide +kernel
theorem subd10_0_1579 : subd10_0 [5, -1, -2] = true := by decide +kernel
theorem subd10_0_1580 : subd10_0 [5, -1, -1] = true := by decide +kernel
theorem subd10_0_1581 : subd10_0 [5, -1, 0] = true := by decide +kernel
theorem subd10_0_1582 : subd10_0 [5, -1, 1] = true := by decide +kernel
theorem subd10_0_1583 : subd10_0 [5, -1, 2] = true := by decide +kernel
theorem subd10_0_1584 : subd10_0 [5, -1, 3] = true := by decide +kernel
theorem subd10_0_1585 : subd10_0 [5, -1, 4] = true := by decide +kernel
theorem subd10_0_1586 : subd10_0 [5, -1, 5] = true := by decide +kernel
theorem subd10_0_1587 : subd10_0 [5, -1, 6] = true := by decide +kernel
theorem subd10_0_1588 : subd10_0 [5, -1, 7] = true := by decide +kernel
theorem subd10_0_1589 : subd10_0 [5, 0, -6] = true := by decide +kernel
theorem subd10_0_1590 : subd10_0 [5, 0, -5] = true := by decide +kernel
theorem subd10_0_1591 : subd10_0 [5, 0, -4] = true := by decide +kernel
theorem subd10_0_1592 : subd10_0 [5, 0, -3] = true := by decide +kernel
theorem subd10_0_1593 : subd10_0 [5, 0, -2] = true := by decide +kernel
theorem subd10_0_1594 : subd10_0 [5, 0, -1] = true := by decide +kernel
theorem subd10_0_1595 : subd10_0 [5, 0, 0] = true := by decide +kernel
theorem subd10_0_1596 : subd10_0 [5, 0, 1] = true := by decide +kernel
theorem subd10_0_1597 : subd10_0 [5, 0, 2] = true := by decide +kernel
theorem subd10_0_1598 : subd10_0 [5, 0, 3] = true := by decide +kernel
theorem subd10_0_1599 : subd10_0 [5, 0, 4] = true := by decide +kernel
theorem sbd10_0_49 : ∀ q ∈ blkd10_0_49, subd10_0 q = true := by
  unfold blkd10_0_49
  exact List.forall_mem_cons.2 ⟨subd10_0_1568, List.forall_mem_cons.2 ⟨subd10_0_1569, List.forall_mem_cons.2 ⟨subd10_0_1570, List.forall_mem_cons.2 ⟨subd10_0_1571, List.forall_mem_cons.2 ⟨subd10_0_1572, List.forall_mem_cons.2 ⟨subd10_0_1573, List.forall_mem_cons.2 ⟨subd10_0_1574, List.forall_mem_cons.2 ⟨subd10_0_1575, List.forall_mem_cons.2 ⟨subd10_0_1576, List.forall_mem_cons.2 ⟨subd10_0_1577, List.forall_mem_cons.2 ⟨subd10_0_1578, List.forall_mem_cons.2 ⟨subd10_0_1579, List.forall_mem_cons.2 ⟨subd10_0_1580, List.forall_mem_cons.2 ⟨subd10_0_1581, List.forall_mem_cons.2 ⟨subd10_0_1582, List.forall_mem_cons.2 ⟨subd10_0_1583, List.forall_mem_cons.2 ⟨subd10_0_1584, List.forall_mem_cons.2 ⟨subd10_0_1585, List.forall_mem_cons.2 ⟨subd10_0_1586, List.forall_mem_cons.2 ⟨subd10_0_1587, List.forall_mem_cons.2 ⟨subd10_0_1588, List.forall_mem_cons.2 ⟨subd10_0_1589, List.forall_mem_cons.2 ⟨subd10_0_1590, List.forall_mem_cons.2 ⟨subd10_0_1591, List.forall_mem_cons.2 ⟨subd10_0_1592, List.forall_mem_cons.2 ⟨subd10_0_1593, List.forall_mem_cons.2 ⟨subd10_0_1594, List.forall_mem_cons.2 ⟨subd10_0_1595, List.forall_mem_cons.2 ⟨subd10_0_1596, List.forall_mem_cons.2 ⟨subd10_0_1597, List.forall_mem_cons.2 ⟨subd10_0_1598, List.forall_mem_cons.2 ⟨subd10_0_1599, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_1600 : subd10_0 [5, 0, 5] = true := by decide +kernel
theorem subd10_0_1601 : subd10_0 [5, 0, 6] = true := by decide +kernel
theorem subd10_0_1602 : subd10_0 [5, 0, 7] = true := by decide +kernel
theorem subd10_0_1603 : subd10_0 [5, 1, -6] = true := by decide +kernel
theorem subd10_0_1604 : subd10_0 [5, 1, -5] = true := by decide +kernel
theorem subd10_0_1605 : subd10_0 [5, 1, -4] = true := by decide +kernel
theorem subd10_0_1606 : subd10_0 [5, 1, -3] = true := by decide +kernel
theorem subd10_0_1607 : subd10_0 [5, 1, -2] = true := by decide +kernel
theorem subd10_0_1608 : subd10_0 [5, 1, -1] = true := by decide +kernel
theorem subd10_0_1609 : subd10_0 [5, 1, 0] = true := by decide +kernel
theorem subd10_0_1610 : subd10_0 [5, 1, 1] = true := by decide +kernel
theorem subd10_0_1611 : subd10_0 [5, 1, 2] = true := by decide +kernel
theorem subd10_0_1612 : subd10_0 [5, 1, 3] = true := by decide +kernel
theorem subd10_0_1613 : subd10_0 [5, 1, 4] = true := by decide +kernel
theorem subd10_0_1614 : subd10_0 [5, 1, 5] = true := by decide +kernel
theorem subd10_0_1615 : subd10_0 [5, 1, 6] = true := by decide +kernel
theorem subd10_0_1616 : subd10_0 [5, 1, 7] = true := by decide +kernel
theorem subd10_0_1617 : subd10_0 [5, 2] = true := by decide +kernel
theorem subd10_0_1618 : subd10_0 [5, 3] = true := by decide +kernel
theorem subd10_0_1619 : subd10_0 [5, 4] = true := by decide +kernel
theorem subd10_0_1620 : subd10_0 [5, 5] = true := by decide +kernel
theorem subd10_0_1621 : subd10_0 [6, -6] = true := by decide +kernel
theorem subd10_0_1622 : subd10_0 [6, -5] = true := by decide +kernel
theorem subd10_0_1623 : subd10_0 [6, -4] = true := by decide +kernel
theorem subd10_0_1624 : subd10_0 [6, -3] = true := by decide +kernel
theorem subd10_0_1625 : subd10_0 [6, -2] = true := by decide +kernel
theorem subd10_0_1626 : subd10_0 [6, -1] = true := by decide +kernel
theorem subd10_0_1627 : subd10_0 [6, 0] = true := by decide +kernel
theorem subd10_0_1628 : subd10_0 [6, 1] = true := by decide +kernel
theorem subd10_0_1629 : subd10_0 [6, 2] = true := by decide +kernel
theorem subd10_0_1630 : subd10_0 [6, 3] = true := by decide +kernel
theorem subd10_0_1631 : subd10_0 [6, 4] = true := by decide +kernel
theorem sbd10_0_50 : ∀ q ∈ blkd10_0_50, subd10_0 q = true := by
  unfold blkd10_0_50
  exact List.forall_mem_cons.2 ⟨subd10_0_1600, List.forall_mem_cons.2 ⟨subd10_0_1601, List.forall_mem_cons.2 ⟨subd10_0_1602, List.forall_mem_cons.2 ⟨subd10_0_1603, List.forall_mem_cons.2 ⟨subd10_0_1604, List.forall_mem_cons.2 ⟨subd10_0_1605, List.forall_mem_cons.2 ⟨subd10_0_1606, List.forall_mem_cons.2 ⟨subd10_0_1607, List.forall_mem_cons.2 ⟨subd10_0_1608, List.forall_mem_cons.2 ⟨subd10_0_1609, List.forall_mem_cons.2 ⟨subd10_0_1610, List.forall_mem_cons.2 ⟨subd10_0_1611, List.forall_mem_cons.2 ⟨subd10_0_1612, List.forall_mem_cons.2 ⟨subd10_0_1613, List.forall_mem_cons.2 ⟨subd10_0_1614, List.forall_mem_cons.2 ⟨subd10_0_1615, List.forall_mem_cons.2 ⟨subd10_0_1616, List.forall_mem_cons.2 ⟨subd10_0_1617, List.forall_mem_cons.2 ⟨subd10_0_1618, List.forall_mem_cons.2 ⟨subd10_0_1619, List.forall_mem_cons.2 ⟨subd10_0_1620, List.forall_mem_cons.2 ⟨subd10_0_1621, List.forall_mem_cons.2 ⟨subd10_0_1622, List.forall_mem_cons.2 ⟨subd10_0_1623, List.forall_mem_cons.2 ⟨subd10_0_1624, List.forall_mem_cons.2 ⟨subd10_0_1625, List.forall_mem_cons.2 ⟨subd10_0_1626, List.forall_mem_cons.2 ⟨subd10_0_1627, List.forall_mem_cons.2 ⟨subd10_0_1628, List.forall_mem_cons.2 ⟨subd10_0_1629, List.forall_mem_cons.2 ⟨subd10_0_1630, List.forall_mem_cons.2 ⟨subd10_0_1631, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_1632 : subd10_0 [7, -4] = true := by decide +kernel
theorem subd10_0_1633 : subd10_0 [7, -3] = true := by decide +kernel
theorem subd10_0_1634 : subd10_0 [7, -2] = true := by decide +kernel
theorem subd10_0_1635 : subd10_0 [7, -1] = true := by decide +kernel
theorem subd10_0_1636 : subd10_0 [7, 0] = true := by decide +kernel
theorem subd10_0_1637 : subd10_0 [7, 1] = true := by decide +kernel
theorem subd10_0_1638 : subd10_0 [7, 2] = true := by decide +kernel
theorem sbd10_0_51 : ∀ q ∈ blkd10_0_51, subd10_0 q = true := by
  unfold blkd10_0_51
  exact List.forall_mem_cons.2 ⟨subd10_0_1632, List.forall_mem_cons.2 ⟨subd10_0_1633, List.forall_mem_cons.2 ⟨subd10_0_1634, List.forall_mem_cons.2 ⟨subd10_0_1635, List.forall_mem_cons.2 ⟨subd10_0_1636, List.forall_mem_cons.2 ⟨subd10_0_1637, List.forall_mem_cons.2 ⟨subd10_0_1638, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_1 : ldCheck G d10_1.U d10_1.ms ldd10_1 = true := by decide +kernel
theorem pre_okd10_1 : subPre G cell10 d10_1 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C131
