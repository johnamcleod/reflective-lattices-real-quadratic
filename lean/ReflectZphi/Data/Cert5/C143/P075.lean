import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd19_3_1440 : subd19_3 [3, 2, -8] = true := by decide +kernel
theorem subd19_3_1441 : subd19_3 [3, 2, -7] = true := by decide +kernel
theorem subd19_3_1442 : subd19_3 [3, 2, -6] = true := by decide +kernel
theorem subd19_3_1443 : subd19_3 [3, 2, -5] = true := by decide +kernel
theorem subd19_3_1444 : subd19_3 [3, 2, -4] = true := by decide +kernel
theorem subd19_3_1445 : subd19_3 [3, 2, -3] = true := by decide +kernel
theorem subd19_3_1446 : subd19_3 [3, 2, -2] = true := by decide +kernel
theorem subd19_3_1447 : subd19_3 [3, 2, -1] = true := by decide +kernel
theorem subd19_3_1448 : subd19_3 [3, 2, 0] = true := by decide +kernel
theorem subd19_3_1449 : subd19_3 [3, 2, 1] = true := by decide +kernel
theorem subd19_3_1450 : subd19_3 [3, 2, 2] = true := by decide +kernel
theorem subd19_3_1451 : subd19_3 [3, 2, 3] = true := by decide +kernel
theorem subd19_3_1452 : subd19_3 [3, 2, 4] = true := by decide +kernel
theorem subd19_3_1453 : subd19_3 [3, 2, 5] = true := by decide +kernel
theorem subd19_3_1454 : subd19_3 [3, 3, -10] = true := by decide +kernel
theorem subd19_3_1455 : subd19_3 [3, 3, -9] = true := by decide +kernel
theorem subd19_3_1456 : subd19_3 [3, 3, -8] = true := by decide +kernel
theorem subd19_3_1457 : subd19_3 [3, 3, -7] = true := by decide +kernel
theorem subd19_3_1458 : subd19_3 [3, 3, -6] = true := by decide +kernel
theorem subd19_3_1459 : subd19_3 [3, 3, -5] = true := by decide +kernel
theorem subd19_3_1460 : subd19_3 [3, 3, -4] = true := by decide +kernel
theorem subd19_3_1461 : subd19_3 [3, 3, -3] = true := by decide +kernel
theorem subd19_3_1462 : subd19_3 [3, 3, -2] = true := by decide +kernel
theorem subd19_3_1463 : subd19_3 [3, 3, -1] = true := by decide +kernel
theorem subd19_3_1464 : subd19_3 [3, 3, 0] = true := by decide +kernel
theorem subd19_3_1465 : subd19_3 [3, 3, 1] = true := by decide +kernel
theorem subd19_3_1466 : subd19_3 [3, 3, 2] = true := by decide +kernel
theorem subd19_3_1467 : subd19_3 [3, 3, 3] = true := by decide +kernel
theorem subd19_3_1468 : subd19_3 [3, 3, 4] = true := by decide +kernel
theorem subd19_3_1469 : subd19_3 [3, 3, 5] = true := by decide +kernel
theorem subd19_3_1470 : subd19_3 [3, 4, -10] = true := by decide +kernel
theorem subd19_3_1471 : subd19_3 [3, 4, -9] = true := by decide +kernel
theorem sbd19_3_45 : ∀ q ∈ blkd19_3_45, subd19_3 q = true := by
  unfold blkd19_3_45
  exact List.forall_mem_cons.2 ⟨subd19_3_1440, List.forall_mem_cons.2 ⟨subd19_3_1441, List.forall_mem_cons.2 ⟨subd19_3_1442, List.forall_mem_cons.2 ⟨subd19_3_1443, List.forall_mem_cons.2 ⟨subd19_3_1444, List.forall_mem_cons.2 ⟨subd19_3_1445, List.forall_mem_cons.2 ⟨subd19_3_1446, List.forall_mem_cons.2 ⟨subd19_3_1447, List.forall_mem_cons.2 ⟨subd19_3_1448, List.forall_mem_cons.2 ⟨subd19_3_1449, List.forall_mem_cons.2 ⟨subd19_3_1450, List.forall_mem_cons.2 ⟨subd19_3_1451, List.forall_mem_cons.2 ⟨subd19_3_1452, List.forall_mem_cons.2 ⟨subd19_3_1453, List.forall_mem_cons.2 ⟨subd19_3_1454, List.forall_mem_cons.2 ⟨subd19_3_1455, List.forall_mem_cons.2 ⟨subd19_3_1456, List.forall_mem_cons.2 ⟨subd19_3_1457, List.forall_mem_cons.2 ⟨subd19_3_1458, List.forall_mem_cons.2 ⟨subd19_3_1459, List.forall_mem_cons.2 ⟨subd19_3_1460, List.forall_mem_cons.2 ⟨subd19_3_1461, List.forall_mem_cons.2 ⟨subd19_3_1462, List.forall_mem_cons.2 ⟨subd19_3_1463, List.forall_mem_cons.2 ⟨subd19_3_1464, List.forall_mem_cons.2 ⟨subd19_3_1465, List.forall_mem_cons.2 ⟨subd19_3_1466, List.forall_mem_cons.2 ⟨subd19_3_1467, List.forall_mem_cons.2 ⟨subd19_3_1468, List.forall_mem_cons.2 ⟨subd19_3_1469, List.forall_mem_cons.2 ⟨subd19_3_1470, List.forall_mem_cons.2 ⟨subd19_3_1471, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_1472 : subd19_3 [3, 4, -8] = true := by decide +kernel
theorem subd19_3_1473 : subd19_3 [3, 4, -7] = true := by decide +kernel
theorem subd19_3_1474 : subd19_3 [3, 4, -6] = true := by decide +kernel
theorem subd19_3_1475 : subd19_3 [3, 4, -5] = true := by decide +kernel
theorem subd19_3_1476 : subd19_3 [3, 4, -4] = true := by decide +kernel
theorem subd19_3_1477 : subd19_3 [3, 4, -3] = true := by decide +kernel
theorem subd19_3_1478 : subd19_3 [3, 4, -2] = true := by decide +kernel
theorem subd19_3_1479 : subd19_3 [3, 4, -1] = true := by decide +kernel
theorem subd19_3_1480 : subd19_3 [3, 4, 0] = true := by decide +kernel
theorem subd19_3_1481 : subd19_3 [3, 4, 1] = true := by decide +kernel
theorem subd19_3_1482 : subd19_3 [3, 4, 2] = true := by decide +kernel
theorem subd19_3_1483 : subd19_3 [3, 4, 3] = true := by decide +kernel
theorem subd19_3_1484 : subd19_3 [3, 5] = true := by decide +kernel
theorem subd19_3_1485 : subd19_3 [3, 6] = true := by decide +kernel
theorem subd19_3_1486 : subd19_3 [3, 7] = true := by decide +kernel
theorem subd19_3_1487 : subd19_3 [4, -8] = true := by decide +kernel
theorem subd19_3_1488 : subd19_3 [4, -7] = true := by decide +kernel
theorem subd19_3_1489 : subd19_3 [4, -6] = true := by decide +kernel
theorem subd19_3_1490 : subd19_3 [4, -5] = true := by decide +kernel
theorem subd19_3_1491 : subd19_3 [4, -4, -7] = true := by decide +kernel
theorem subd19_3_1492 : subd19_3 [4, -4, -6] = true := by decide +kernel
theorem subd19_3_1493 : subd19_3 [4, -4, -5] = true := by decide +kernel
theorem subd19_3_1494 : subd19_3 [4, -4, -4] = true := by decide +kernel
theorem subd19_3_1495 : subd19_3 [4, -4, -3] = true := by decide +kernel
theorem subd19_3_1496 : subd19_3 [4, -4, -2] = true := by decide +kernel
theorem subd19_3_1497 : subd19_3 [4, -4, -1] = true := by decide +kernel
theorem subd19_3_1498 : subd19_3 [4, -4, 0] = true := by decide +kernel
theorem subd19_3_1499 : subd19_3 [4, -4, 1] = true := by decide +kernel
theorem subd19_3_1500 : subd19_3 [4, -4, 2] = true := by decide +kernel
theorem subd19_3_1501 : subd19_3 [4, -4, 3] = true := by decide +kernel
theorem subd19_3_1502 : subd19_3 [4, -4, 4] = true := by decide +kernel
theorem subd19_3_1503 : subd19_3 [4, -4, 5] = true := by decide +kernel
theorem sbd19_3_46 : ∀ q ∈ blkd19_3_46, subd19_3 q = true := by
  unfold blkd19_3_46
  exact List.forall_mem_cons.2 ⟨subd19_3_1472, List.forall_mem_cons.2 ⟨subd19_3_1473, List.forall_mem_cons.2 ⟨subd19_3_1474, List.forall_mem_cons.2 ⟨subd19_3_1475, List.forall_mem_cons.2 ⟨subd19_3_1476, List.forall_mem_cons.2 ⟨subd19_3_1477, List.forall_mem_cons.2 ⟨subd19_3_1478, List.forall_mem_cons.2 ⟨subd19_3_1479, List.forall_mem_cons.2 ⟨subd19_3_1480, List.forall_mem_cons.2 ⟨subd19_3_1481, List.forall_mem_cons.2 ⟨subd19_3_1482, List.forall_mem_cons.2 ⟨subd19_3_1483, List.forall_mem_cons.2 ⟨subd19_3_1484, List.forall_mem_cons.2 ⟨subd19_3_1485, List.forall_mem_cons.2 ⟨subd19_3_1486, List.forall_mem_cons.2 ⟨subd19_3_1487, List.forall_mem_cons.2 ⟨subd19_3_1488, List.forall_mem_cons.2 ⟨subd19_3_1489, List.forall_mem_cons.2 ⟨subd19_3_1490, List.forall_mem_cons.2 ⟨subd19_3_1491, List.forall_mem_cons.2 ⟨subd19_3_1492, List.forall_mem_cons.2 ⟨subd19_3_1493, List.forall_mem_cons.2 ⟨subd19_3_1494, List.forall_mem_cons.2 ⟨subd19_3_1495, List.forall_mem_cons.2 ⟨subd19_3_1496, List.forall_mem_cons.2 ⟨subd19_3_1497, List.forall_mem_cons.2 ⟨subd19_3_1498, List.forall_mem_cons.2 ⟨subd19_3_1499, List.forall_mem_cons.2 ⟨subd19_3_1500, List.forall_mem_cons.2 ⟨subd19_3_1501, List.forall_mem_cons.2 ⟨subd19_3_1502, List.forall_mem_cons.2 ⟨subd19_3_1503, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_1504 : subd19_3 [4, -4, 6] = true := by decide +kernel
theorem subd19_3_1505 : subd19_3 [4, -4, 7] = true := by decide +kernel
theorem subd19_3_1506 : subd19_3 [4, -3, -8] = true := by decide +kernel
theorem subd19_3_1507 : subd19_3 [4, -3, -7] = true := by decide +kernel
theorem subd19_3_1508 : subd19_3 [4, -3, -6] = true := by decide +kernel
theorem subd19_3_1509 : subd19_3 [4, -3, -5] = true := by decide +kernel
theorem subd19_3_1510 : subd19_3 [4, -3, -4] = true := by decide +kernel
theorem subd19_3_1511 : subd19_3 [4, -3, -3] = true := by decide +kernel
theorem subd19_3_1512 : subd19_3 [4, -3, -2] = true := by decide +kernel
theorem subd19_3_1513 : subd19_3 [4, -3, -1] = true := by decide +kernel
theorem subd19_3_1514 : subd19_3 [4, -3, 0] = true := by decide +kernel
theorem subd19_3_1515 : subd19_3 [4, -3, 1] = true := by decide +kernel
theorem subd19_3_1516 : subd19_3 [4, -3, 2] = true := by decide +kernel
theorem subd19_3_1517 : subd19_3 [4, -3, 3] = true := by decide +kernel
theorem subd19_3_1518 : subd19_3 [4, -3, 4] = true := by decide +kernel
theorem subd19_3_1519 : subd19_3 [4, -3, 5] = true := by decide +kernel
theorem subd19_3_1520 : subd19_3 [4, -3, 6] = true := by decide +kernel
theorem subd19_3_1521 : subd19_3 [4, -3, 7] = true := by decide +kernel
theorem subd19_3_1522 : subd19_3 [4, -2, -9] = true := by decide +kernel
theorem subd19_3_1523 : subd19_3 [4, -2, -8] = true := by decide +kernel
theorem subd19_3_1524 : subd19_3 [4, -2, -7] = true := by decide +kernel
theorem subd19_3_1525 : subd19_3 [4, -2, -6] = true := by decide +kernel
theorem subd19_3_1526 : subd19_3 [4, -2, -5] = true := by decide +kernel
theorem subd19_3_1527 : subd19_3 [4, -2, -4] = true := by decide +kernel
theorem subd19_3_1528 : subd19_3 [4, -2, -3] = true := by decide +kernel
theorem subd19_3_1529 : subd19_3 [4, -2, -2] = true := by decide +kernel
theorem subd19_3_1530 : subd19_3 [4, -2, -1] = true := by decide +kernel
theorem subd19_3_1531 : subd19_3 [4, -2, 0] = true := by decide +kernel
theorem subd19_3_1532 : subd19_3 [4, -2, 1] = true := by decide +kernel
theorem subd19_3_1533 : subd19_3 [4, -2, 2] = true := by decide +kernel
theorem subd19_3_1534 : subd19_3 [4, -2, 3] = true := by decide +kernel
theorem subd19_3_1535 : subd19_3 [4, -2, 4] = true := by decide +kernel
theorem sbd19_3_47 : ∀ q ∈ blkd19_3_47, subd19_3 q = true := by
  unfold blkd19_3_47
  exact List.forall_mem_cons.2 ⟨subd19_3_1504, List.forall_mem_cons.2 ⟨subd19_3_1505, List.forall_mem_cons.2 ⟨subd19_3_1506, List.forall_mem_cons.2 ⟨subd19_3_1507, List.forall_mem_cons.2 ⟨subd19_3_1508, List.forall_mem_cons.2 ⟨subd19_3_1509, List.forall_mem_cons.2 ⟨subd19_3_1510, List.forall_mem_cons.2 ⟨subd19_3_1511, List.forall_mem_cons.2 ⟨subd19_3_1512, List.forall_mem_cons.2 ⟨subd19_3_1513, List.forall_mem_cons.2 ⟨subd19_3_1514, List.forall_mem_cons.2 ⟨subd19_3_1515, List.forall_mem_cons.2 ⟨subd19_3_1516, List.forall_mem_cons.2 ⟨subd19_3_1517, List.forall_mem_cons.2 ⟨subd19_3_1518, List.forall_mem_cons.2 ⟨subd19_3_1519, List.forall_mem_cons.2 ⟨subd19_3_1520, List.forall_mem_cons.2 ⟨subd19_3_1521, List.forall_mem_cons.2 ⟨subd19_3_1522, List.forall_mem_cons.2 ⟨subd19_3_1523, List.forall_mem_cons.2 ⟨subd19_3_1524, List.forall_mem_cons.2 ⟨subd19_3_1525, List.forall_mem_cons.2 ⟨subd19_3_1526, List.forall_mem_cons.2 ⟨subd19_3_1527, List.forall_mem_cons.2 ⟨subd19_3_1528, List.forall_mem_cons.2 ⟨subd19_3_1529, List.forall_mem_cons.2 ⟨subd19_3_1530, List.forall_mem_cons.2 ⟨subd19_3_1531, List.forall_mem_cons.2 ⟨subd19_3_1532, List.forall_mem_cons.2 ⟨subd19_3_1533, List.forall_mem_cons.2 ⟨subd19_3_1534, List.forall_mem_cons.2 ⟨subd19_3_1535, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_1536 : subd19_3 [4, -2, 5] = true := by decide +kernel
theorem subd19_3_1537 : subd19_3 [4, -2, 6] = true := by decide +kernel
theorem subd19_3_1538 : subd19_3 [4, -2, 7] = true := by decide +kernel
theorem subd19_3_1539 : subd19_3 [4, -1, -9] = true := by decide +kernel
theorem subd19_3_1540 : subd19_3 [4, -1, -8] = true := by decide +kernel
theorem subd19_3_1541 : subd19_3 [4, -1, -7] = true := by decide +kernel
theorem subd19_3_1542 : subd19_3 [4, -1, -6] = true := by decide +kernel
theorem subd19_3_1543 : subd19_3 [4, -1, -5] = true := by decide +kernel
theorem subd19_3_1544 : subd19_3 [4, -1, -4] = true := by decide +kernel
theorem subd19_3_1545 : subd19_3 [4, -1, -3] = true := by decide +kernel
theorem subd19_3_1546 : subd19_3 [4, -1, -2] = true := by decide +kernel
theorem subd19_3_1547 : subd19_3 [4, -1, -1] = true := by decide +kernel
theorem subd19_3_1548 : subd19_3 [4, -1, 0] = true := by decide +kernel
theorem subd19_3_1549 : subd19_3 [4, -1, 1] = true := by decide +kernel
theorem subd19_3_1550 : subd19_3 [4, -1, 2] = true := by decide +kernel
theorem subd19_3_1551 : subd19_3 [4, -1, 3] = true := by decide +kernel
theorem subd19_3_1552 : subd19_3 [4, -1, 4] = true := by decide +kernel
theorem subd19_3_1553 : subd19_3 [4, -1, 5] = true := by decide +kernel
theorem subd19_3_1554 : subd19_3 [4, -1, 6] = true := by decide +kernel
theorem subd19_3_1555 : subd19_3 [4, 0, -10] = true := by decide +kernel
theorem subd19_3_1556 : subd19_3 [4, 0, -9] = true := by decide +kernel
theorem subd19_3_1557 : subd19_3 [4, 0, -8] = true := by decide +kernel
theorem subd19_3_1558 : subd19_3 [4, 0, -7] = true := by decide +kernel
theorem subd19_3_1559 : subd19_3 [4, 0, -6] = true := by decide +kernel
theorem subd19_3_1560 : subd19_3 [4, 0, -5] = true := by decide +kernel
theorem subd19_3_1561 : subd19_3 [4, 0, -4] = true := by decide +kernel
theorem subd19_3_1562 : subd19_3 [4, 0, -3] = true := by decide +kernel
theorem subd19_3_1563 : subd19_3 [4, 0, -2] = true := by decide +kernel
theorem subd19_3_1564 : subd19_3 [4, 0, -1] = true := by decide +kernel
theorem subd19_3_1565 : subd19_3 [4, 0, 0] = true := by decide +kernel
theorem subd19_3_1566 : subd19_3 [4, 0, 1] = true := by decide +kernel
theorem subd19_3_1567 : subd19_3 [4, 0, 2] = true := by decide +kernel
theorem sbd19_3_48 : ∀ q ∈ blkd19_3_48, subd19_3 q = true := by
  unfold blkd19_3_48
  exact List.forall_mem_cons.2 ⟨subd19_3_1536, List.forall_mem_cons.2 ⟨subd19_3_1537, List.forall_mem_cons.2 ⟨subd19_3_1538, List.forall_mem_cons.2 ⟨subd19_3_1539, List.forall_mem_cons.2 ⟨subd19_3_1540, List.forall_mem_cons.2 ⟨subd19_3_1541, List.forall_mem_cons.2 ⟨subd19_3_1542, List.forall_mem_cons.2 ⟨subd19_3_1543, List.forall_mem_cons.2 ⟨subd19_3_1544, List.forall_mem_cons.2 ⟨subd19_3_1545, List.forall_mem_cons.2 ⟨subd19_3_1546, List.forall_mem_cons.2 ⟨subd19_3_1547, List.forall_mem_cons.2 ⟨subd19_3_1548, List.forall_mem_cons.2 ⟨subd19_3_1549, List.forall_mem_cons.2 ⟨subd19_3_1550, List.forall_mem_cons.2 ⟨subd19_3_1551, List.forall_mem_cons.2 ⟨subd19_3_1552, List.forall_mem_cons.2 ⟨subd19_3_1553, List.forall_mem_cons.2 ⟨subd19_3_1554, List.forall_mem_cons.2 ⟨subd19_3_1555, List.forall_mem_cons.2 ⟨subd19_3_1556, List.forall_mem_cons.2 ⟨subd19_3_1557, List.forall_mem_cons.2 ⟨subd19_3_1558, List.forall_mem_cons.2 ⟨subd19_3_1559, List.forall_mem_cons.2 ⟨subd19_3_1560, List.forall_mem_cons.2 ⟨subd19_3_1561, List.forall_mem_cons.2 ⟨subd19_3_1562, List.forall_mem_cons.2 ⟨subd19_3_1563, List.forall_mem_cons.2 ⟨subd19_3_1564, List.forall_mem_cons.2 ⟨subd19_3_1565, List.forall_mem_cons.2 ⟨subd19_3_1566, List.forall_mem_cons.2 ⟨subd19_3_1567, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_1568 : subd19_3 [4, 0, 3] = true := by decide +kernel
theorem subd19_3_1569 : subd19_3 [4, 0, 4] = true := by decide +kernel
theorem subd19_3_1570 : subd19_3 [4, 0, 5] = true := by decide +kernel
theorem subd19_3_1571 : subd19_3 [4, 0, 6] = true := by decide +kernel
theorem subd19_3_1572 : subd19_3 [4, 1, -10] = true := by decide +kernel
theorem subd19_3_1573 : subd19_3 [4, 1, -9] = true := by decide +kernel
theorem subd19_3_1574 : subd19_3 [4, 1, -8] = true := by decide +kernel
theorem subd19_3_1575 : subd19_3 [4, 1, -7] = true := by decide +kernel
theorem subd19_3_1576 : subd19_3 [4, 1, -6] = true := by decide +kernel
theorem subd19_3_1577 : subd19_3 [4, 1, -5] = true := by decide +kernel
theorem subd19_3_1578 : subd19_3 [4, 1, -4] = true := by decide +kernel
theorem subd19_3_1579 : subd19_3 [4, 1, -3] = true := by decide +kernel
theorem subd19_3_1580 : subd19_3 [4, 1, -2] = true := by decide +kernel
theorem subd19_3_1581 : subd19_3 [4, 1, -1] = true := by decide +kernel
theorem subd19_3_1582 : subd19_3 [4, 1, 0] = true := by decide +kernel
theorem subd19_3_1583 : subd19_3 [4, 1, 1] = true := by decide +kernel
theorem subd19_3_1584 : subd19_3 [4, 1, 2] = true := by decide +kernel
theorem subd19_3_1585 : subd19_3 [4, 1, 3] = true := by decide +kernel
theorem subd19_3_1586 : subd19_3 [4, 1, 4] = true := by decide +kernel
theorem subd19_3_1587 : subd19_3 [4, 1, 5] = true := by decide +kernel
theorem subd19_3_1588 : subd19_3 [4, 2, -10] = true := by decide +kernel
theorem subd19_3_1589 : subd19_3 [4, 2, -9] = true := by decide +kernel
theorem subd19_3_1590 : subd19_3 [4, 2, -8] = true := by decide +kernel
theorem subd19_3_1591 : subd19_3 [4, 2, -7] = true := by decide +kernel
theorem subd19_3_1592 : subd19_3 [4, 2, -6] = true := by decide +kernel
theorem subd19_3_1593 : subd19_3 [4, 2, -5] = true := by decide +kernel
theorem subd19_3_1594 : subd19_3 [4, 2, -4] = true := by decide +kernel
theorem subd19_3_1595 : subd19_3 [4, 2, -3] = true := by decide +kernel
theorem subd19_3_1596 : subd19_3 [4, 2, -2] = true := by decide +kernel
theorem subd19_3_1597 : subd19_3 [4, 2, -1] = true := by decide +kernel
theorem subd19_3_1598 : subd19_3 [4, 2, 0] = true := by decide +kernel
theorem subd19_3_1599 : subd19_3 [4, 2, 1] = true := by decide +kernel
theorem sbd19_3_49 : ∀ q ∈ blkd19_3_49, subd19_3 q = true := by
  unfold blkd19_3_49
  exact List.forall_mem_cons.2 ⟨subd19_3_1568, List.forall_mem_cons.2 ⟨subd19_3_1569, List.forall_mem_cons.2 ⟨subd19_3_1570, List.forall_mem_cons.2 ⟨subd19_3_1571, List.forall_mem_cons.2 ⟨subd19_3_1572, List.forall_mem_cons.2 ⟨subd19_3_1573, List.forall_mem_cons.2 ⟨subd19_3_1574, List.forall_mem_cons.2 ⟨subd19_3_1575, List.forall_mem_cons.2 ⟨subd19_3_1576, List.forall_mem_cons.2 ⟨subd19_3_1577, List.forall_mem_cons.2 ⟨subd19_3_1578, List.forall_mem_cons.2 ⟨subd19_3_1579, List.forall_mem_cons.2 ⟨subd19_3_1580, List.forall_mem_cons.2 ⟨subd19_3_1581, List.forall_mem_cons.2 ⟨subd19_3_1582, List.forall_mem_cons.2 ⟨subd19_3_1583, List.forall_mem_cons.2 ⟨subd19_3_1584, List.forall_mem_cons.2 ⟨subd19_3_1585, List.forall_mem_cons.2 ⟨subd19_3_1586, List.forall_mem_cons.2 ⟨subd19_3_1587, List.forall_mem_cons.2 ⟨subd19_3_1588, List.forall_mem_cons.2 ⟨subd19_3_1589, List.forall_mem_cons.2 ⟨subd19_3_1590, List.forall_mem_cons.2 ⟨subd19_3_1591, List.forall_mem_cons.2 ⟨subd19_3_1592, List.forall_mem_cons.2 ⟨subd19_3_1593, List.forall_mem_cons.2 ⟨subd19_3_1594, List.forall_mem_cons.2 ⟨subd19_3_1595, List.forall_mem_cons.2 ⟨subd19_3_1596, List.forall_mem_cons.2 ⟨subd19_3_1597, List.forall_mem_cons.2 ⟨subd19_3_1598, List.forall_mem_cons.2 ⟨subd19_3_1599, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_1600 : subd19_3 [4, 2, 2] = true := by decide +kernel
theorem subd19_3_1601 : subd19_3 [4, 2, 3] = true := by decide +kernel
theorem subd19_3_1602 : subd19_3 [4, 2, 4] = true := by decide +kernel
theorem subd19_3_1603 : subd19_3 [4, 2, 5] = true := by decide +kernel
theorem subd19_3_1604 : subd19_3 [4, 3, -10] = true := by decide +kernel
theorem subd19_3_1605 : subd19_3 [4, 3, -9] = true := by decide +kernel
theorem subd19_3_1606 : subd19_3 [4, 3, -8] = true := by decide +kernel
theorem subd19_3_1607 : subd19_3 [4, 3, -7] = true := by decide +kernel
theorem subd19_3_1608 : subd19_3 [4, 3, -6] = true := by decide +kernel
theorem subd19_3_1609 : subd19_3 [4, 3, -5] = true := by decide +kernel
theorem subd19_3_1610 : subd19_3 [4, 3, -4] = true := by decide +kernel
theorem subd19_3_1611 : subd19_3 [4, 3, -3] = true := by decide +kernel
theorem subd19_3_1612 : subd19_3 [4, 3, -2] = true := by decide +kernel
theorem subd19_3_1613 : subd19_3 [4, 3, -1] = true := by decide +kernel
theorem subd19_3_1614 : subd19_3 [4, 3, 0] = true := by decide +kernel
theorem subd19_3_1615 : subd19_3 [4, 3, 1] = true := by decide +kernel
theorem subd19_3_1616 : subd19_3 [4, 3, 2] = true := by decide +kernel
theorem subd19_3_1617 : subd19_3 [4, 3, 3] = true := by decide +kernel
theorem subd19_3_1618 : subd19_3 [4, 3, 4] = true := by decide +kernel
theorem subd19_3_1619 : subd19_3 [4, 4] = true := by decide +kernel
theorem subd19_3_1620 : subd19_3 [4, 5] = true := by decide +kernel
theorem subd19_3_1621 : subd19_3 [4, 6] = true := by decide +kernel
theorem subd19_3_1622 : subd19_3 [5, -7] = true := by decide +kernel
theorem subd19_3_1623 : subd19_3 [5, -6] = true := by decide +kernel
theorem subd19_3_1624 : subd19_3 [5, -5] = true := by decide +kernel
theorem subd19_3_1625 : subd19_3 [5, -4] = true := by decide +kernel
theorem subd19_3_1626 : subd19_3 [5, -3] = true := by decide +kernel
theorem subd19_3_1627 : subd19_3 [5, -2, -8] = true := by decide +kernel
theorem subd19_3_1628 : subd19_3 [5, -2, -7] = true := by decide +kernel
theorem subd19_3_1629 : subd19_3 [5, -2, -6] = true := by decide +kernel
theorem subd19_3_1630 : subd19_3 [5, -2, -5] = true := by decide +kernel
theorem subd19_3_1631 : subd19_3 [5, -2, -4] = true := by decide +kernel
theorem sbd19_3_50 : ∀ q ∈ blkd19_3_50, subd19_3 q = true := by
  unfold blkd19_3_50
  exact List.forall_mem_cons.2 ⟨subd19_3_1600, List.forall_mem_cons.2 ⟨subd19_3_1601, List.forall_mem_cons.2 ⟨subd19_3_1602, List.forall_mem_cons.2 ⟨subd19_3_1603, List.forall_mem_cons.2 ⟨subd19_3_1604, List.forall_mem_cons.2 ⟨subd19_3_1605, List.forall_mem_cons.2 ⟨subd19_3_1606, List.forall_mem_cons.2 ⟨subd19_3_1607, List.forall_mem_cons.2 ⟨subd19_3_1608, List.forall_mem_cons.2 ⟨subd19_3_1609, List.forall_mem_cons.2 ⟨subd19_3_1610, List.forall_mem_cons.2 ⟨subd19_3_1611, List.forall_mem_cons.2 ⟨subd19_3_1612, List.forall_mem_cons.2 ⟨subd19_3_1613, List.forall_mem_cons.2 ⟨subd19_3_1614, List.forall_mem_cons.2 ⟨subd19_3_1615, List.forall_mem_cons.2 ⟨subd19_3_1616, List.forall_mem_cons.2 ⟨subd19_3_1617, List.forall_mem_cons.2 ⟨subd19_3_1618, List.forall_mem_cons.2 ⟨subd19_3_1619, List.forall_mem_cons.2 ⟨subd19_3_1620, List.forall_mem_cons.2 ⟨subd19_3_1621, List.forall_mem_cons.2 ⟨subd19_3_1622, List.forall_mem_cons.2 ⟨subd19_3_1623, List.forall_mem_cons.2 ⟨subd19_3_1624, List.forall_mem_cons.2 ⟨subd19_3_1625, List.forall_mem_cons.2 ⟨subd19_3_1626, List.forall_mem_cons.2 ⟨subd19_3_1627, List.forall_mem_cons.2 ⟨subd19_3_1628, List.forall_mem_cons.2 ⟨subd19_3_1629, List.forall_mem_cons.2 ⟨subd19_3_1630, List.forall_mem_cons.2 ⟨subd19_3_1631, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_1632 : subd19_3 [5, -2, -3] = true := by decide +kernel
theorem subd19_3_1633 : subd19_3 [5, -2, -2] = true := by decide +kernel
theorem subd19_3_1634 : subd19_3 [5, -2, -1] = true := by decide +kernel
theorem subd19_3_1635 : subd19_3 [5, -2, 0] = true := by decide +kernel
theorem subd19_3_1636 : subd19_3 [5, -2, 1] = true := by decide +kernel
theorem subd19_3_1637 : subd19_3 [5, -2, 2] = true := by decide +kernel
theorem subd19_3_1638 : subd19_3 [5, -2, 3] = true := by decide +kernel
theorem subd19_3_1639 : subd19_3 [5, -2, 4] = true := by decide +kernel
theorem subd19_3_1640 : subd19_3 [5, -2, 5] = true := by decide +kernel
theorem subd19_3_1641 : subd19_3 [5, -2, 6] = true := by decide +kernel
theorem subd19_3_1642 : subd19_3 [5, -1, -9] = true := by decide +kernel
theorem subd19_3_1643 : subd19_3 [5, -1, -8] = true := by decide +kernel
theorem subd19_3_1644 : subd19_3 [5, -1, -7] = true := by decide +kernel
theorem subd19_3_1645 : subd19_3 [5, -1, -6] = true := by decide +kernel
theorem subd19_3_1646 : subd19_3 [5, -1, -5] = true := by decide +kernel
theorem subd19_3_1647 : subd19_3 [5, -1, -4] = true := by decide +kernel
theorem subd19_3_1648 : subd19_3 [5, -1, -3] = true := by decide +kernel
theorem subd19_3_1649 : subd19_3 [5, -1, -2] = true := by decide +kernel
theorem subd19_3_1650 : subd19_3 [5, -1, -1] = true := by decide +kernel
theorem subd19_3_1651 : subd19_3 [5, -1, 0] = true := by decide +kernel
theorem subd19_3_1652 : subd19_3 [5, -1, 1] = true := by decide +kernel
theorem subd19_3_1653 : subd19_3 [5, -1, 2] = true := by decide +kernel
theorem subd19_3_1654 : subd19_3 [5, -1, 3] = true := by decide +kernel
theorem subd19_3_1655 : subd19_3 [5, -1, 4] = true := by decide +kernel
theorem subd19_3_1656 : subd19_3 [5, -1, 5] = true := by decide +kernel
theorem subd19_3_1657 : subd19_3 [5, 0, -9] = true := by decide +kernel
theorem subd19_3_1658 : subd19_3 [5, 0, -8] = true := by decide +kernel
theorem subd19_3_1659 : subd19_3 [5, 0, -7] = true := by decide +kernel
theorem subd19_3_1660 : subd19_3 [5, 0, -6] = true := by decide +kernel
theorem subd19_3_1661 : subd19_3 [5, 0, -5] = true := by decide +kernel
theorem subd19_3_1662 : subd19_3 [5, 0, -4] = true := by decide +kernel
theorem subd19_3_1663 : subd19_3 [5, 0, -3] = true := by decide +kernel
theorem sbd19_3_51 : ∀ q ∈ blkd19_3_51, subd19_3 q = true := by
  unfold blkd19_3_51
  exact List.forall_mem_cons.2 ⟨subd19_3_1632, List.forall_mem_cons.2 ⟨subd19_3_1633, List.forall_mem_cons.2 ⟨subd19_3_1634, List.forall_mem_cons.2 ⟨subd19_3_1635, List.forall_mem_cons.2 ⟨subd19_3_1636, List.forall_mem_cons.2 ⟨subd19_3_1637, List.forall_mem_cons.2 ⟨subd19_3_1638, List.forall_mem_cons.2 ⟨subd19_3_1639, List.forall_mem_cons.2 ⟨subd19_3_1640, List.forall_mem_cons.2 ⟨subd19_3_1641, List.forall_mem_cons.2 ⟨subd19_3_1642, List.forall_mem_cons.2 ⟨subd19_3_1643, List.forall_mem_cons.2 ⟨subd19_3_1644, List.forall_mem_cons.2 ⟨subd19_3_1645, List.forall_mem_cons.2 ⟨subd19_3_1646, List.forall_mem_cons.2 ⟨subd19_3_1647, List.forall_mem_cons.2 ⟨subd19_3_1648, List.forall_mem_cons.2 ⟨subd19_3_1649, List.forall_mem_cons.2 ⟨subd19_3_1650, List.forall_mem_cons.2 ⟨subd19_3_1651, List.forall_mem_cons.2 ⟨subd19_3_1652, List.forall_mem_cons.2 ⟨subd19_3_1653, List.forall_mem_cons.2 ⟨subd19_3_1654, List.forall_mem_cons.2 ⟨subd19_3_1655, List.forall_mem_cons.2 ⟨subd19_3_1656, List.forall_mem_cons.2 ⟨subd19_3_1657, List.forall_mem_cons.2 ⟨subd19_3_1658, List.forall_mem_cons.2 ⟨subd19_3_1659, List.forall_mem_cons.2 ⟨subd19_3_1660, List.forall_mem_cons.2 ⟨subd19_3_1661, List.forall_mem_cons.2 ⟨subd19_3_1662, List.forall_mem_cons.2 ⟨subd19_3_1663, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_1664 : subd19_3 [5, 0, -2] = true := by decide +kernel
theorem subd19_3_1665 : subd19_3 [5, 0, -1] = true := by decide +kernel
theorem subd19_3_1666 : subd19_3 [5, 0, 0] = true := by decide +kernel
theorem subd19_3_1667 : subd19_3 [5, 0, 1] = true := by decide +kernel
theorem subd19_3_1668 : subd19_3 [5, 0, 2] = true := by decide +kernel
theorem subd19_3_1669 : subd19_3 [5, 0, 3] = true := by decide +kernel
theorem subd19_3_1670 : subd19_3 [5, 0, 4] = true := by decide +kernel
theorem subd19_3_1671 : subd19_3 [5, 0, 5] = true := by decide +kernel
theorem subd19_3_1672 : subd19_3 [5, 1, -10] = true := by decide +kernel
theorem subd19_3_1673 : subd19_3 [5, 1, -9] = true := by decide +kernel
theorem subd19_3_1674 : subd19_3 [5, 1, -8] = true := by decide +kernel
theorem subd19_3_1675 : subd19_3 [5, 1, -7] = true := by decide +kernel
theorem subd19_3_1676 : subd19_3 [5, 1, -6] = true := by decide +kernel
theorem subd19_3_1677 : subd19_3 [5, 1, -5] = true := by decide +kernel
theorem subd19_3_1678 : subd19_3 [5, 1, -4] = true := by decide +kernel
theorem subd19_3_1679 : subd19_3 [5, 1, -3] = true := by decide +kernel
theorem subd19_3_1680 : subd19_3 [5, 1, -2] = true := by decide +kernel
theorem subd19_3_1681 : subd19_3 [5, 1, -1] = true := by decide +kernel
theorem subd19_3_1682 : subd19_3 [5, 1, 0] = true := by decide +kernel
theorem subd19_3_1683 : subd19_3 [5, 1, 1] = true := by decide +kernel
theorem subd19_3_1684 : subd19_3 [5, 1, 2] = true := by decide +kernel
theorem subd19_3_1685 : subd19_3 [5, 1, 3] = true := by decide +kernel
theorem subd19_3_1686 : subd19_3 [5, 1, 4] = true := by decide +kernel
theorem subd19_3_1687 : subd19_3 [5, 2, -10] = true := by decide +kernel
theorem subd19_3_1688 : subd19_3 [5, 2, -9] = true := by decide +kernel
theorem subd19_3_1689 : subd19_3 [5, 2, -8] = true := by decide +kernel
theorem subd19_3_1690 : subd19_3 [5, 2, -7] = true := by decide +kernel
theorem subd19_3_1691 : subd19_3 [5, 2, -6] = true := by decide +kernel
theorem subd19_3_1692 : subd19_3 [5, 2, -5] = true := by decide +kernel
theorem subd19_3_1693 : subd19_3 [5, 2, -4] = true := by decide +kernel
theorem subd19_3_1694 : subd19_3 [5, 2, -3] = true := by decide +kernel
theorem subd19_3_1695 : subd19_3 [5, 2, -2] = true := by decide +kernel
theorem sbd19_3_52 : ∀ q ∈ blkd19_3_52, subd19_3 q = true := by
  unfold blkd19_3_52
  exact List.forall_mem_cons.2 ⟨subd19_3_1664, List.forall_mem_cons.2 ⟨subd19_3_1665, List.forall_mem_cons.2 ⟨subd19_3_1666, List.forall_mem_cons.2 ⟨subd19_3_1667, List.forall_mem_cons.2 ⟨subd19_3_1668, List.forall_mem_cons.2 ⟨subd19_3_1669, List.forall_mem_cons.2 ⟨subd19_3_1670, List.forall_mem_cons.2 ⟨subd19_3_1671, List.forall_mem_cons.2 ⟨subd19_3_1672, List.forall_mem_cons.2 ⟨subd19_3_1673, List.forall_mem_cons.2 ⟨subd19_3_1674, List.forall_mem_cons.2 ⟨subd19_3_1675, List.forall_mem_cons.2 ⟨subd19_3_1676, List.forall_mem_cons.2 ⟨subd19_3_1677, List.forall_mem_cons.2 ⟨subd19_3_1678, List.forall_mem_cons.2 ⟨subd19_3_1679, List.forall_mem_cons.2 ⟨subd19_3_1680, List.forall_mem_cons.2 ⟨subd19_3_1681, List.forall_mem_cons.2 ⟨subd19_3_1682, List.forall_mem_cons.2 ⟨subd19_3_1683, List.forall_mem_cons.2 ⟨subd19_3_1684, List.forall_mem_cons.2 ⟨subd19_3_1685, List.forall_mem_cons.2 ⟨subd19_3_1686, List.forall_mem_cons.2 ⟨subd19_3_1687, List.forall_mem_cons.2 ⟨subd19_3_1688, List.forall_mem_cons.2 ⟨subd19_3_1689, List.forall_mem_cons.2 ⟨subd19_3_1690, List.forall_mem_cons.2 ⟨subd19_3_1691, List.forall_mem_cons.2 ⟨subd19_3_1692, List.forall_mem_cons.2 ⟨subd19_3_1693, List.forall_mem_cons.2 ⟨subd19_3_1694, List.forall_mem_cons.2 ⟨subd19_3_1695, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_1696 : subd19_3 [5, 2, -1] = true := by decide +kernel
theorem subd19_3_1697 : subd19_3 [5, 2, 0] = true := by decide +kernel
theorem subd19_3_1698 : subd19_3 [5, 2, 1] = true := by decide +kernel
theorem subd19_3_1699 : subd19_3 [5, 2, 2] = true := by decide +kernel
theorem subd19_3_1700 : subd19_3 [5, 2, 3] = true := by decide +kernel
theorem subd19_3_1701 : subd19_3 [5, 2, 4] = true := by decide +kernel
theorem subd19_3_1702 : subd19_3 [5, 3] = true := by decide +kernel
theorem subd19_3_1703 : subd19_3 [5, 4] = true := by decide +kernel
theorem subd19_3_1704 : subd19_3 [5, 5] = true := by decide +kernel
theorem subd19_3_1705 : subd19_3 [5, 6] = true := by decide +kernel
theorem subd19_3_1706 : subd19_3 [6, -7] = true := by decide +kernel
theorem subd19_3_1707 : subd19_3 [6, -6] = true := by decide +kernel
theorem subd19_3_1708 : subd19_3 [6, -5] = true := by decide +kernel
theorem subd19_3_1709 : subd19_3 [6, -4] = true := by decide +kernel
theorem subd19_3_1710 : subd19_3 [6, -3] = true := by decide +kernel
theorem subd19_3_1711 : subd19_3 [6, -2] = true := by decide +kernel
theorem subd19_3_1712 : subd19_3 [6, -1] = true := by decide +kernel
theorem subd19_3_1713 : subd19_3 [6, 0] = true := by decide +kernel
theorem subd19_3_1714 : subd19_3 [6, 1] = true := by decide +kernel
theorem subd19_3_1715 : subd19_3 [6, 2] = true := by decide +kernel
theorem subd19_3_1716 : subd19_3 [6, 3] = true := by decide +kernel
theorem subd19_3_1717 : subd19_3 [6, 4] = true := by decide +kernel
theorem subd19_3_1718 : subd19_3 [6, 5] = true := by decide +kernel
theorem subd19_3_1719 : subd19_3 [7, -6] = true := by decide +kernel
theorem subd19_3_1720 : subd19_3 [7, -5] = true := by decide +kernel
theorem subd19_3_1721 : subd19_3 [7, -4] = true := by decide +kernel
theorem subd19_3_1722 : subd19_3 [7, -3] = true := by decide +kernel
theorem subd19_3_1723 : subd19_3 [7, -2] = true := by decide +kernel
theorem subd19_3_1724 : subd19_3 [7, -1] = true := by decide +kernel
theorem subd19_3_1725 : subd19_3 [7, 0] = true := by decide +kernel
theorem subd19_3_1726 : subd19_3 [7, 1] = true := by decide +kernel
theorem subd19_3_1727 : subd19_3 [7, 2] = true := by decide +kernel
theorem sbd19_3_53 : ∀ q ∈ blkd19_3_53, subd19_3 q = true := by
  unfold blkd19_3_53
  exact List.forall_mem_cons.2 ⟨subd19_3_1696, List.forall_mem_cons.2 ⟨subd19_3_1697, List.forall_mem_cons.2 ⟨subd19_3_1698, List.forall_mem_cons.2 ⟨subd19_3_1699, List.forall_mem_cons.2 ⟨subd19_3_1700, List.forall_mem_cons.2 ⟨subd19_3_1701, List.forall_mem_cons.2 ⟨subd19_3_1702, List.forall_mem_cons.2 ⟨subd19_3_1703, List.forall_mem_cons.2 ⟨subd19_3_1704, List.forall_mem_cons.2 ⟨subd19_3_1705, List.forall_mem_cons.2 ⟨subd19_3_1706, List.forall_mem_cons.2 ⟨subd19_3_1707, List.forall_mem_cons.2 ⟨subd19_3_1708, List.forall_mem_cons.2 ⟨subd19_3_1709, List.forall_mem_cons.2 ⟨subd19_3_1710, List.forall_mem_cons.2 ⟨subd19_3_1711, List.forall_mem_cons.2 ⟨subd19_3_1712, List.forall_mem_cons.2 ⟨subd19_3_1713, List.forall_mem_cons.2 ⟨subd19_3_1714, List.forall_mem_cons.2 ⟨subd19_3_1715, List.forall_mem_cons.2 ⟨subd19_3_1716, List.forall_mem_cons.2 ⟨subd19_3_1717, List.forall_mem_cons.2 ⟨subd19_3_1718, List.forall_mem_cons.2 ⟨subd19_3_1719, List.forall_mem_cons.2 ⟨subd19_3_1720, List.forall_mem_cons.2 ⟨subd19_3_1721, List.forall_mem_cons.2 ⟨subd19_3_1722, List.forall_mem_cons.2 ⟨subd19_3_1723, List.forall_mem_cons.2 ⟨subd19_3_1724, List.forall_mem_cons.2 ⟨subd19_3_1725, List.forall_mem_cons.2 ⟨subd19_3_1726, List.forall_mem_cons.2 ⟨subd19_3_1727, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_3_1728 : subd19_3 [7, 3] = true := by decide +kernel
theorem subd19_3_1729 : subd19_3 [7, 4] = true := by decide +kernel
theorem subd19_3_1730 : subd19_3 [8, -4] = true := by decide +kernel
theorem subd19_3_1731 : subd19_3 [8, -3] = true := by decide +kernel
theorem subd19_3_1732 : subd19_3 [8, -2] = true := by decide +kernel
theorem subd19_3_1733 : subd19_3 [8, -1] = true := by decide +kernel
theorem subd19_3_1734 : subd19_3 [8, 0] = true := by decide +kernel
theorem subd19_3_1735 : subd19_3 [8, 1] = true := by decide +kernel
theorem subd19_3_1736 : subd19_3 [8, 2] = true := by decide +kernel
theorem sbd19_3_54 : ∀ q ∈ blkd19_3_54, subd19_3 q = true := by
  unfold blkd19_3_54
  exact List.forall_mem_cons.2 ⟨subd19_3_1728, List.forall_mem_cons.2 ⟨subd19_3_1729, List.forall_mem_cons.2 ⟨subd19_3_1730, List.forall_mem_cons.2 ⟨subd19_3_1731, List.forall_mem_cons.2 ⟨subd19_3_1732, List.forall_mem_cons.2 ⟨subd19_3_1733, List.forall_mem_cons.2 ⟨subd19_3_1734, List.forall_mem_cons.2 ⟨subd19_3_1735, List.forall_mem_cons.2 ⟨subd19_3_1736, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd20_0 : ldCheck G d20_0.U d20_0.ms ldd20_0 = true := by decide +kernel
theorem pre_okd20_0 : subPre G cell20 d20_0 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C143
