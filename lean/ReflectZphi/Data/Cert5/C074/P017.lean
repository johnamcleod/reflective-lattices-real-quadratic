import ReflectZphi.Data.Cert5.C074.Base

namespace ReflectZphi.Data.Cert5.C074
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub10_1440 : sub10 [3, -4, 1] = true := by decide +kernel
theorem sub10_1441 : sub10 [3, -4, 2] = true := by decide +kernel
theorem sub10_1442 : sub10 [3, -4, 3] = true := by decide +kernel
theorem sub10_1443 : sub10 [3, -4, 4] = true := by decide +kernel
theorem sub10_1444 : sub10 [3, -4, 5] = true := by decide +kernel
theorem sub10_1445 : sub10 [3, -4, 6] = true := by decide +kernel
theorem sub10_1446 : sub10 [3, -4, 7] = true := by decide +kernel
theorem sub10_1447 : sub10 [3, -4, 8] = true := by decide +kernel
theorem sub10_1448 : sub10 [3, -4, 9] = true := by decide +kernel
theorem sub10_1449 : sub10 [3, -3, -7] = true := by decide +kernel
theorem sub10_1450 : sub10 [3, -3, -6] = true := by decide +kernel
theorem sub10_1451 : sub10 [3, -3, -5] = true := by decide +kernel
theorem sub10_1452 : sub10 [3, -3, -4] = true := by decide +kernel
theorem sub10_1453 : sub10 [3, -3, -3] = true := by decide +kernel
theorem sub10_1454 : sub10 [3, -3, -2] = true := by decide +kernel
theorem sub10_1455 : sub10 [3, -3, -1] = true := by decide +kernel
theorem sub10_1456 : sub10 [3, -3, 0] = true := by decide +kernel
theorem sub10_1457 : sub10 [3, -3, 1] = true := by decide +kernel
theorem sub10_1458 : sub10 [3, -3, 2] = true := by decide +kernel
theorem sub10_1459 : sub10 [3, -3, 3] = true := by decide +kernel
theorem sub10_1460 : sub10 [3, -3, 4] = true := by decide +kernel
theorem sub10_1461 : sub10 [3, -3, 5] = true := by decide +kernel
theorem sub10_1462 : sub10 [3, -3, 6] = true := by decide +kernel
theorem sub10_1463 : sub10 [3, -3, 7] = true := by decide +kernel
theorem sub10_1464 : sub10 [3, -3, 8] = true := by decide +kernel
theorem sub10_1465 : sub10 [3, -3, 9] = true := by decide +kernel
theorem sub10_1466 : sub10 [3, -2, -7] = true := by decide +kernel
theorem sub10_1467 : sub10 [3, -2, -6] = true := by decide +kernel
theorem sub10_1468 : sub10 [3, -2, -5] = true := by decide +kernel
theorem sub10_1469 : sub10 [3, -2, -4] = true := by decide +kernel
theorem sub10_1470 : sub10 [3, -2, -3] = true := by decide +kernel
theorem sub10_1471 : sub10 [3, -2, -2] = true := by decide +kernel
theorem sb10_45 : ∀ q ∈ blk10_45, sub10 q = true := by
  unfold blk10_45
  exact List.forall_mem_cons.2 ⟨sub10_1440, List.forall_mem_cons.2 ⟨sub10_1441, List.forall_mem_cons.2 ⟨sub10_1442, List.forall_mem_cons.2 ⟨sub10_1443, List.forall_mem_cons.2 ⟨sub10_1444, List.forall_mem_cons.2 ⟨sub10_1445, List.forall_mem_cons.2 ⟨sub10_1446, List.forall_mem_cons.2 ⟨sub10_1447, List.forall_mem_cons.2 ⟨sub10_1448, List.forall_mem_cons.2 ⟨sub10_1449, List.forall_mem_cons.2 ⟨sub10_1450, List.forall_mem_cons.2 ⟨sub10_1451, List.forall_mem_cons.2 ⟨sub10_1452, List.forall_mem_cons.2 ⟨sub10_1453, List.forall_mem_cons.2 ⟨sub10_1454, List.forall_mem_cons.2 ⟨sub10_1455, List.forall_mem_cons.2 ⟨sub10_1456, List.forall_mem_cons.2 ⟨sub10_1457, List.forall_mem_cons.2 ⟨sub10_1458, List.forall_mem_cons.2 ⟨sub10_1459, List.forall_mem_cons.2 ⟨sub10_1460, List.forall_mem_cons.2 ⟨sub10_1461, List.forall_mem_cons.2 ⟨sub10_1462, List.forall_mem_cons.2 ⟨sub10_1463, List.forall_mem_cons.2 ⟨sub10_1464, List.forall_mem_cons.2 ⟨sub10_1465, List.forall_mem_cons.2 ⟨sub10_1466, List.forall_mem_cons.2 ⟨sub10_1467, List.forall_mem_cons.2 ⟨sub10_1468, List.forall_mem_cons.2 ⟨sub10_1469, List.forall_mem_cons.2 ⟨sub10_1470, List.forall_mem_cons.2 ⟨sub10_1471, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_1472 : sub10 [3, -2, -1] = true := by decide +kernel
theorem sub10_1473 : sub10 [3, -2, 0] = true := by decide +kernel
theorem sub10_1474 : sub10 [3, -2, 1] = true := by decide +kernel
theorem sub10_1475 : sub10 [3, -2, 2] = true := by decide +kernel
theorem sub10_1476 : sub10 [3, -2, 3] = true := by decide +kernel
theorem sub10_1477 : sub10 [3, -2, 4] = true := by decide +kernel
theorem sub10_1478 : sub10 [3, -2, 5] = true := by decide +kernel
theorem sub10_1479 : sub10 [3, -2, 6] = true := by decide +kernel
theorem sub10_1480 : sub10 [3, -2, 7] = true := by decide +kernel
theorem sub10_1481 : sub10 [3, -2, 8] = true := by decide +kernel
theorem sub10_1482 : sub10 [3, -2, 9] = true := by decide +kernel
theorem sub10_1483 : sub10 [3, -1, -7] = true := by decide +kernel
theorem sub10_1484 : sub10 [3, -1, -6] = true := by decide +kernel
theorem sub10_1485 : sub10 [3, -1, -5] = true := by decide +kernel
theorem sub10_1486 : sub10 [3, -1, -4] = true := by decide +kernel
theorem sub10_1487 : sub10 [3, -1, -3] = true := by decide +kernel
theorem sub10_1488 : sub10 [3, -1, -2] = true := by decide +kernel
theorem sub10_1489 : sub10 [3, -1, -1] = true := by decide +kernel
theorem sub10_1490 : sub10 [3, -1, 0] = true := by decide +kernel
theorem sub10_1491 : sub10 [3, -1, 1] = true := by decide +kernel
theorem sub10_1492 : sub10 [3, -1, 2] = true := by decide +kernel
theorem sub10_1493 : sub10 [3, -1, 3] = true := by decide +kernel
theorem sub10_1494 : sub10 [3, -1, 4] = true := by decide +kernel
theorem sub10_1495 : sub10 [3, -1, 5] = true := by decide +kernel
theorem sub10_1496 : sub10 [3, -1, 6] = true := by decide +kernel
theorem sub10_1497 : sub10 [3, -1, 7] = true := by decide +kernel
theorem sub10_1498 : sub10 [3, -1, 8] = true := by decide +kernel
theorem sub10_1499 : sub10 [3, -1, 9] = true := by decide +kernel
theorem sub10_1500 : sub10 [3, 0, -8] = true := by decide +kernel
theorem sub10_1501 : sub10 [3, 0, -7] = true := by decide +kernel
theorem sub10_1502 : sub10 [3, 0, -6] = true := by decide +kernel
theorem sub10_1503 : sub10 [3, 0, -5] = true := by decide +kernel
theorem sb10_46 : ∀ q ∈ blk10_46, sub10 q = true := by
  unfold blk10_46
  exact List.forall_mem_cons.2 ⟨sub10_1472, List.forall_mem_cons.2 ⟨sub10_1473, List.forall_mem_cons.2 ⟨sub10_1474, List.forall_mem_cons.2 ⟨sub10_1475, List.forall_mem_cons.2 ⟨sub10_1476, List.forall_mem_cons.2 ⟨sub10_1477, List.forall_mem_cons.2 ⟨sub10_1478, List.forall_mem_cons.2 ⟨sub10_1479, List.forall_mem_cons.2 ⟨sub10_1480, List.forall_mem_cons.2 ⟨sub10_1481, List.forall_mem_cons.2 ⟨sub10_1482, List.forall_mem_cons.2 ⟨sub10_1483, List.forall_mem_cons.2 ⟨sub10_1484, List.forall_mem_cons.2 ⟨sub10_1485, List.forall_mem_cons.2 ⟨sub10_1486, List.forall_mem_cons.2 ⟨sub10_1487, List.forall_mem_cons.2 ⟨sub10_1488, List.forall_mem_cons.2 ⟨sub10_1489, List.forall_mem_cons.2 ⟨sub10_1490, List.forall_mem_cons.2 ⟨sub10_1491, List.forall_mem_cons.2 ⟨sub10_1492, List.forall_mem_cons.2 ⟨sub10_1493, List.forall_mem_cons.2 ⟨sub10_1494, List.forall_mem_cons.2 ⟨sub10_1495, List.forall_mem_cons.2 ⟨sub10_1496, List.forall_mem_cons.2 ⟨sub10_1497, List.forall_mem_cons.2 ⟨sub10_1498, List.forall_mem_cons.2 ⟨sub10_1499, List.forall_mem_cons.2 ⟨sub10_1500, List.forall_mem_cons.2 ⟨sub10_1501, List.forall_mem_cons.2 ⟨sub10_1502, List.forall_mem_cons.2 ⟨sub10_1503, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_1504 : sub10 [3, 0, -4] = true := by decide +kernel
theorem sub10_1505 : sub10 [3, 0, -3] = true := by decide +kernel
theorem sub10_1506 : sub10 [3, 0, -2] = true := by decide +kernel
theorem sub10_1507 : sub10 [3, 0, -1] = true := by decide +kernel
theorem sub10_1508 : sub10 [3, 0, 0] = true := by decide +kernel
theorem sub10_1509 : sub10 [3, 0, 1] = true := by decide +kernel
theorem sub10_1510 : sub10 [3, 0, 2] = true := by decide +kernel
theorem sub10_1511 : sub10 [3, 0, 3] = true := by decide +kernel
theorem sub10_1512 : sub10 [3, 0, 4] = true := by decide +kernel
theorem sub10_1513 : sub10 [3, 0, 5] = true := by decide +kernel
theorem sub10_1514 : sub10 [3, 0, 6] = true := by decide +kernel
theorem sub10_1515 : sub10 [3, 0, 7] = true := by decide +kernel
theorem sub10_1516 : sub10 [3, 0, 8] = true := by decide +kernel
theorem sub10_1517 : sub10 [3, 0, 9] = true := by decide +kernel
theorem sub10_1518 : sub10 [3, 1, -8] = true := by decide +kernel
theorem sub10_1519 : sub10 [3, 1, -7] = true := by decide +kernel
theorem sub10_1520 : sub10 [3, 1, -6] = true := by decide +kernel
theorem sub10_1521 : sub10 [3, 1, -5] = true := by decide +kernel
theorem sub10_1522 : sub10 [3, 1, -4] = true := by decide +kernel
theorem sub10_1523 : sub10 [3, 1, -3] = true := by decide +kernel
theorem sub10_1524 : sub10 [3, 1, -2] = true := by decide +kernel
theorem sub10_1525 : sub10 [3, 1, -1] = true := by decide +kernel
theorem sub10_1526 : sub10 [3, 1, 0] = true := by decide +kernel
theorem sub10_1527 : sub10 [3, 1, 1] = true := by decide +kernel
theorem sub10_1528 : sub10 [3, 1, 2] = true := by decide +kernel
theorem sub10_1529 : sub10 [3, 1, 3] = true := by decide +kernel
theorem sub10_1530 : sub10 [3, 1, 4] = true := by decide +kernel
theorem sub10_1531 : sub10 [3, 1, 5] = true := by decide +kernel
theorem sub10_1532 : sub10 [3, 1, 6] = true := by decide +kernel
theorem sub10_1533 : sub10 [3, 1, 7] = true := by decide +kernel
theorem sub10_1534 : sub10 [3, 1, 8] = true := by decide +kernel
theorem sub10_1535 : sub10 [3, 2, -7] = true := by decide +kernel
theorem sb10_47 : ∀ q ∈ blk10_47, sub10 q = true := by
  unfold blk10_47
  exact List.forall_mem_cons.2 ⟨sub10_1504, List.forall_mem_cons.2 ⟨sub10_1505, List.forall_mem_cons.2 ⟨sub10_1506, List.forall_mem_cons.2 ⟨sub10_1507, List.forall_mem_cons.2 ⟨sub10_1508, List.forall_mem_cons.2 ⟨sub10_1509, List.forall_mem_cons.2 ⟨sub10_1510, List.forall_mem_cons.2 ⟨sub10_1511, List.forall_mem_cons.2 ⟨sub10_1512, List.forall_mem_cons.2 ⟨sub10_1513, List.forall_mem_cons.2 ⟨sub10_1514, List.forall_mem_cons.2 ⟨sub10_1515, List.forall_mem_cons.2 ⟨sub10_1516, List.forall_mem_cons.2 ⟨sub10_1517, List.forall_mem_cons.2 ⟨sub10_1518, List.forall_mem_cons.2 ⟨sub10_1519, List.forall_mem_cons.2 ⟨sub10_1520, List.forall_mem_cons.2 ⟨sub10_1521, List.forall_mem_cons.2 ⟨sub10_1522, List.forall_mem_cons.2 ⟨sub10_1523, List.forall_mem_cons.2 ⟨sub10_1524, List.forall_mem_cons.2 ⟨sub10_1525, List.forall_mem_cons.2 ⟨sub10_1526, List.forall_mem_cons.2 ⟨sub10_1527, List.forall_mem_cons.2 ⟨sub10_1528, List.forall_mem_cons.2 ⟨sub10_1529, List.forall_mem_cons.2 ⟨sub10_1530, List.forall_mem_cons.2 ⟨sub10_1531, List.forall_mem_cons.2 ⟨sub10_1532, List.forall_mem_cons.2 ⟨sub10_1533, List.forall_mem_cons.2 ⟨sub10_1534, List.forall_mem_cons.2 ⟨sub10_1535, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_1536 : sub10 [3, 2, -6] = true := by decide +kernel
theorem sub10_1537 : sub10 [3, 2, -5] = true := by decide +kernel
theorem sub10_1538 : sub10 [3, 2, -4] = true := by decide +kernel
theorem sub10_1539 : sub10 [3, 2, -3] = true := by decide +kernel
theorem sub10_1540 : sub10 [3, 2, -2] = true := by decide +kernel
theorem sub10_1541 : sub10 [3, 2, -1] = true := by decide +kernel
theorem sub10_1542 : sub10 [3, 2, 0] = true := by decide +kernel
theorem sub10_1543 : sub10 [3, 2, 1] = true := by decide +kernel
theorem sub10_1544 : sub10 [3, 2, 2] = true := by decide +kernel
theorem sub10_1545 : sub10 [3, 2, 3] = true := by decide +kernel
theorem sub10_1546 : sub10 [3, 2, 4] = true := by decide +kernel
theorem sub10_1547 : sub10 [3, 2, 5] = true := by decide +kernel
theorem sub10_1548 : sub10 [3, 2, 6] = true := by decide +kernel
theorem sub10_1549 : sub10 [3, 2, 7] = true := by decide +kernel
theorem sub10_1550 : sub10 [3, 3, -7] = true := by decide +kernel
theorem sub10_1551 : sub10 [3, 3, -6] = true := by decide +kernel
theorem sub10_1552 : sub10 [3, 3, -5] = true := by decide +kernel
theorem sub10_1553 : sub10 [3, 3, -4] = true := by decide +kernel
theorem sub10_1554 : sub10 [3, 3, -3] = true := by decide +kernel
theorem sub10_1555 : sub10 [3, 3, -2] = true := by decide +kernel
theorem sub10_1556 : sub10 [3, 3, -1] = true := by decide +kernel
theorem sub10_1557 : sub10 [3, 3, 0] = true := by decide +kernel
theorem sub10_1558 : sub10 [3, 3, 1] = true := by decide +kernel
theorem sub10_1559 : sub10 [3, 3, 2] = true := by decide +kernel
theorem sub10_1560 : sub10 [3, 3, 3] = true := by decide +kernel
theorem sub10_1561 : sub10 [3, 3, 4] = true := by decide +kernel
theorem sub10_1562 : sub10 [3, 3, 5] = true := by decide +kernel
theorem sub10_1563 : sub10 [3, 3, 6] = true := by decide +kernel
theorem sub10_1564 : sub10 [3, 4] = true := by decide +kernel
theorem sub10_1565 : sub10 [3, 5] = true := by decide +kernel
theorem sub10_1566 : sub10 [3, 6] = true := by decide +kernel
theorem sub10_1567 : sub10 [4, -9] = true := by decide +kernel
theorem sb10_48 : ∀ q ∈ blk10_48, sub10 q = true := by
  unfold blk10_48
  exact List.forall_mem_cons.2 ⟨sub10_1536, List.forall_mem_cons.2 ⟨sub10_1537, List.forall_mem_cons.2 ⟨sub10_1538, List.forall_mem_cons.2 ⟨sub10_1539, List.forall_mem_cons.2 ⟨sub10_1540, List.forall_mem_cons.2 ⟨sub10_1541, List.forall_mem_cons.2 ⟨sub10_1542, List.forall_mem_cons.2 ⟨sub10_1543, List.forall_mem_cons.2 ⟨sub10_1544, List.forall_mem_cons.2 ⟨sub10_1545, List.forall_mem_cons.2 ⟨sub10_1546, List.forall_mem_cons.2 ⟨sub10_1547, List.forall_mem_cons.2 ⟨sub10_1548, List.forall_mem_cons.2 ⟨sub10_1549, List.forall_mem_cons.2 ⟨sub10_1550, List.forall_mem_cons.2 ⟨sub10_1551, List.forall_mem_cons.2 ⟨sub10_1552, List.forall_mem_cons.2 ⟨sub10_1553, List.forall_mem_cons.2 ⟨sub10_1554, List.forall_mem_cons.2 ⟨sub10_1555, List.forall_mem_cons.2 ⟨sub10_1556, List.forall_mem_cons.2 ⟨sub10_1557, List.forall_mem_cons.2 ⟨sub10_1558, List.forall_mem_cons.2 ⟨sub10_1559, List.forall_mem_cons.2 ⟨sub10_1560, List.forall_mem_cons.2 ⟨sub10_1561, List.forall_mem_cons.2 ⟨sub10_1562, List.forall_mem_cons.2 ⟨sub10_1563, List.forall_mem_cons.2 ⟨sub10_1564, List.forall_mem_cons.2 ⟨sub10_1565, List.forall_mem_cons.2 ⟨sub10_1566, List.forall_mem_cons.2 ⟨sub10_1567, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_1568 : sub10 [4, -8] = true := by decide +kernel
theorem sub10_1569 : sub10 [4, -7] = true := by decide +kernel
theorem sub10_1570 : sub10 [4, -6] = true := by decide +kernel
theorem sub10_1571 : sub10 [4, -5, -5] = true := by decide +kernel
theorem sub10_1572 : sub10 [4, -5, -4] = true := by decide +kernel
theorem sub10_1573 : sub10 [4, -5, -3] = true := by decide +kernel
theorem sub10_1574 : sub10 [4, -5, -2] = true := by decide +kernel
theorem sub10_1575 : sub10 [4, -5, -1] = true := by decide +kernel
theorem sub10_1576 : sub10 [4, -5, 0] = true := by decide +kernel
theorem sub10_1577 : sub10 [4, -5, 1] = true := by decide +kernel
theorem sub10_1578 : sub10 [4, -5, 2] = true := by decide +kernel
theorem sub10_1579 : sub10 [4, -5, 3] = true := by decide +kernel
theorem sub10_1580 : sub10 [4, -5, 4] = true := by decide +kernel
theorem sub10_1581 : sub10 [4, -5, 5] = true := by decide +kernel
theorem sub10_1582 : sub10 [4, -5, 6] = true := by decide +kernel
theorem sub10_1583 : sub10 [4, -5, 7] = true := by decide +kernel
theorem sub10_1584 : sub10 [4, -5, 8] = true := by decide +kernel
theorem sub10_1585 : sub10 [4, -5, 9] = true := by decide +kernel
theorem sub10_1586 : sub10 [4, -4, -5] = true := by decide +kernel
theorem sub10_1587 : sub10 [4, -4, -4] = true := by decide +kernel
theorem sub10_1588 : sub10 [4, -4, -3] = true := by decide +kernel
theorem sub10_1589 : sub10 [4, -4, -2] = true := by decide +kernel
theorem sub10_1590 : sub10 [4, -4, -1] = true := by decide +kernel
theorem sub10_1591 : sub10 [4, -4, 0] = true := by decide +kernel
theorem sub10_1592 : sub10 [4, -4, 1] = true := by decide +kernel
theorem sub10_1593 : sub10 [4, -4, 2] = true := by decide +kernel
theorem sub10_1594 : sub10 [4, -4, 3] = true := by decide +kernel
theorem sub10_1595 : sub10 [4, -4, 4] = true := by decide +kernel
theorem sub10_1596 : sub10 [4, -4, 5] = true := by decide +kernel
theorem sub10_1597 : sub10 [4, -4, 6] = true := by decide +kernel
theorem sub10_1598 : sub10 [4, -4, 7] = true := by decide +kernel
theorem sub10_1599 : sub10 [4, -4, 8] = true := by decide +kernel
theorem sb10_49 : ∀ q ∈ blk10_49, sub10 q = true := by
  unfold blk10_49
  exact List.forall_mem_cons.2 ⟨sub10_1568, List.forall_mem_cons.2 ⟨sub10_1569, List.forall_mem_cons.2 ⟨sub10_1570, List.forall_mem_cons.2 ⟨sub10_1571, List.forall_mem_cons.2 ⟨sub10_1572, List.forall_mem_cons.2 ⟨sub10_1573, List.forall_mem_cons.2 ⟨sub10_1574, List.forall_mem_cons.2 ⟨sub10_1575, List.forall_mem_cons.2 ⟨sub10_1576, List.forall_mem_cons.2 ⟨sub10_1577, List.forall_mem_cons.2 ⟨sub10_1578, List.forall_mem_cons.2 ⟨sub10_1579, List.forall_mem_cons.2 ⟨sub10_1580, List.forall_mem_cons.2 ⟨sub10_1581, List.forall_mem_cons.2 ⟨sub10_1582, List.forall_mem_cons.2 ⟨sub10_1583, List.forall_mem_cons.2 ⟨sub10_1584, List.forall_mem_cons.2 ⟨sub10_1585, List.forall_mem_cons.2 ⟨sub10_1586, List.forall_mem_cons.2 ⟨sub10_1587, List.forall_mem_cons.2 ⟨sub10_1588, List.forall_mem_cons.2 ⟨sub10_1589, List.forall_mem_cons.2 ⟨sub10_1590, List.forall_mem_cons.2 ⟨sub10_1591, List.forall_mem_cons.2 ⟨sub10_1592, List.forall_mem_cons.2 ⟨sub10_1593, List.forall_mem_cons.2 ⟨sub10_1594, List.forall_mem_cons.2 ⟨sub10_1595, List.forall_mem_cons.2 ⟨sub10_1596, List.forall_mem_cons.2 ⟨sub10_1597, List.forall_mem_cons.2 ⟨sub10_1598, List.forall_mem_cons.2 ⟨sub10_1599, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_1600 : sub10 [4, -4, 9] = true := by decide +kernel
theorem sub10_1601 : sub10 [4, -3, -6] = true := by decide +kernel
theorem sub10_1602 : sub10 [4, -3, -5] = true := by decide +kernel
theorem sub10_1603 : sub10 [4, -3, -4] = true := by decide +kernel
theorem sub10_1604 : sub10 [4, -3, -3] = true := by decide +kernel
theorem sub10_1605 : sub10 [4, -3, -2] = true := by decide +kernel
theorem sub10_1606 : sub10 [4, -3, -1] = true := by decide +kernel
theorem sub10_1607 : sub10 [4, -3, 0] = true := by decide +kernel
theorem sub10_1608 : sub10 [4, -3, 1] = true := by decide +kernel
theorem sub10_1609 : sub10 [4, -3, 2] = true := by decide +kernel
theorem sub10_1610 : sub10 [4, -3, 3] = true := by decide +kernel
theorem sub10_1611 : sub10 [4, -3, 4] = true := by decide +kernel
theorem sub10_1612 : sub10 [4, -3, 5] = true := by decide +kernel
theorem sub10_1613 : sub10 [4, -3, 6] = true := by decide +kernel
theorem sub10_1614 : sub10 [4, -3, 7] = true := by decide +kernel
theorem sub10_1615 : sub10 [4, -3, 8] = true := by decide +kernel
theorem sub10_1616 : sub10 [4, -3, 9] = true := by decide +kernel
theorem sub10_1617 : sub10 [4, -2, -6] = true := by decide +kernel
theorem sub10_1618 : sub10 [4, -2, -5] = true := by decide +kernel
theorem sub10_1619 : sub10 [4, -2, -4] = true := by decide +kernel
theorem sub10_1620 : sub10 [4, -2, -3] = true := by decide +kernel
theorem sub10_1621 : sub10 [4, -2, -2] = true := by decide +kernel
theorem sub10_1622 : sub10 [4, -2, -1] = true := by decide +kernel
theorem sub10_1623 : sub10 [4, -2, 0] = true := by decide +kernel
theorem sub10_1624 : sub10 [4, -2, 1] = true := by decide +kernel
theorem sub10_1625 : sub10 [4, -2, 2] = true := by decide +kernel
theorem sub10_1626 : sub10 [4, -2, 3] = true := by decide +kernel
theorem sub10_1627 : sub10 [4, -2, 4] = true := by decide +kernel
theorem sub10_1628 : sub10 [4, -2, 5] = true := by decide +kernel
theorem sub10_1629 : sub10 [4, -2, 6] = true := by decide +kernel
theorem sub10_1630 : sub10 [4, -2, 7] = true := by decide +kernel
theorem sub10_1631 : sub10 [4, -2, 8] = true := by decide +kernel
theorem sb10_50 : ∀ q ∈ blk10_50, sub10 q = true := by
  unfold blk10_50
  exact List.forall_mem_cons.2 ⟨sub10_1600, List.forall_mem_cons.2 ⟨sub10_1601, List.forall_mem_cons.2 ⟨sub10_1602, List.forall_mem_cons.2 ⟨sub10_1603, List.forall_mem_cons.2 ⟨sub10_1604, List.forall_mem_cons.2 ⟨sub10_1605, List.forall_mem_cons.2 ⟨sub10_1606, List.forall_mem_cons.2 ⟨sub10_1607, List.forall_mem_cons.2 ⟨sub10_1608, List.forall_mem_cons.2 ⟨sub10_1609, List.forall_mem_cons.2 ⟨sub10_1610, List.forall_mem_cons.2 ⟨sub10_1611, List.forall_mem_cons.2 ⟨sub10_1612, List.forall_mem_cons.2 ⟨sub10_1613, List.forall_mem_cons.2 ⟨sub10_1614, List.forall_mem_cons.2 ⟨sub10_1615, List.forall_mem_cons.2 ⟨sub10_1616, List.forall_mem_cons.2 ⟨sub10_1617, List.forall_mem_cons.2 ⟨sub10_1618, List.forall_mem_cons.2 ⟨sub10_1619, List.forall_mem_cons.2 ⟨sub10_1620, List.forall_mem_cons.2 ⟨sub10_1621, List.forall_mem_cons.2 ⟨sub10_1622, List.forall_mem_cons.2 ⟨sub10_1623, List.forall_mem_cons.2 ⟨sub10_1624, List.forall_mem_cons.2 ⟨sub10_1625, List.forall_mem_cons.2 ⟨sub10_1626, List.forall_mem_cons.2 ⟨sub10_1627, List.forall_mem_cons.2 ⟨sub10_1628, List.forall_mem_cons.2 ⟨sub10_1629, List.forall_mem_cons.2 ⟨sub10_1630, List.forall_mem_cons.2 ⟨sub10_1631, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_1632 : sub10 [4, -2, 9] = true := by decide +kernel
theorem sub10_1633 : sub10 [4, -1, -6] = true := by decide +kernel
theorem sub10_1634 : sub10 [4, -1, -5] = true := by decide +kernel
theorem sub10_1635 : sub10 [4, -1, -4] = true := by decide +kernel
theorem sub10_1636 : sub10 [4, -1, -3] = true := by decide +kernel
theorem sub10_1637 : sub10 [4, -1, -2] = true := by decide +kernel
theorem sub10_1638 : sub10 [4, -1, -1] = true := by decide +kernel
theorem sub10_1639 : sub10 [4, -1, 0] = true := by decide +kernel
theorem sub10_1640 : sub10 [4, -1, 1] = true := by decide +kernel
theorem sub10_1641 : sub10 [4, -1, 2] = true := by decide +kernel
theorem sub10_1642 : sub10 [4, -1, 3] = true := by decide +kernel
theorem sub10_1643 : sub10 [4, -1, 4] = true := by decide +kernel
theorem sub10_1644 : sub10 [4, -1, 5] = true := by decide +kernel
theorem sub10_1645 : sub10 [4, -1, 6] = true := by decide +kernel
theorem sub10_1646 : sub10 [4, -1, 7] = true := by decide +kernel
theorem sub10_1647 : sub10 [4, -1, 8] = true := by decide +kernel
theorem sub10_1648 : sub10 [4, 0, -7] = true := by decide +kernel
theorem sub10_1649 : sub10 [4, 0, -6] = true := by decide +kernel
theorem sub10_1650 : sub10 [4, 0, -5] = true := by decide +kernel
theorem sub10_1651 : sub10 [4, 0, -4] = true := by decide +kernel
theorem sub10_1652 : sub10 [4, 0, -3] = true := by decide +kernel
theorem sub10_1653 : sub10 [4, 0, -2] = true := by decide +kernel
theorem sub10_1654 : sub10 [4, 0, -1] = true := by decide +kernel
theorem sub10_1655 : sub10 [4, 0, 0] = true := by decide +kernel
theorem sub10_1656 : sub10 [4, 0, 1] = true := by decide +kernel
theorem sub10_1657 : sub10 [4, 0, 2] = true := by decide +kernel
theorem sub10_1658 : sub10 [4, 0, 3] = true := by decide +kernel
theorem sub10_1659 : sub10 [4, 0, 4] = true := by decide +kernel
theorem sub10_1660 : sub10 [4, 0, 5] = true := by decide +kernel
theorem sub10_1661 : sub10 [4, 0, 6] = true := by decide +kernel
theorem sub10_1662 : sub10 [4, 0, 7] = true := by decide +kernel
theorem sub10_1663 : sub10 [4, 0, 8] = true := by decide +kernel
theorem sb10_51 : ∀ q ∈ blk10_51, sub10 q = true := by
  unfold blk10_51
  exact List.forall_mem_cons.2 ⟨sub10_1632, List.forall_mem_cons.2 ⟨sub10_1633, List.forall_mem_cons.2 ⟨sub10_1634, List.forall_mem_cons.2 ⟨sub10_1635, List.forall_mem_cons.2 ⟨sub10_1636, List.forall_mem_cons.2 ⟨sub10_1637, List.forall_mem_cons.2 ⟨sub10_1638, List.forall_mem_cons.2 ⟨sub10_1639, List.forall_mem_cons.2 ⟨sub10_1640, List.forall_mem_cons.2 ⟨sub10_1641, List.forall_mem_cons.2 ⟨sub10_1642, List.forall_mem_cons.2 ⟨sub10_1643, List.forall_mem_cons.2 ⟨sub10_1644, List.forall_mem_cons.2 ⟨sub10_1645, List.forall_mem_cons.2 ⟨sub10_1646, List.forall_mem_cons.2 ⟨sub10_1647, List.forall_mem_cons.2 ⟨sub10_1648, List.forall_mem_cons.2 ⟨sub10_1649, List.forall_mem_cons.2 ⟨sub10_1650, List.forall_mem_cons.2 ⟨sub10_1651, List.forall_mem_cons.2 ⟨sub10_1652, List.forall_mem_cons.2 ⟨sub10_1653, List.forall_mem_cons.2 ⟨sub10_1654, List.forall_mem_cons.2 ⟨sub10_1655, List.forall_mem_cons.2 ⟨sub10_1656, List.forall_mem_cons.2 ⟨sub10_1657, List.forall_mem_cons.2 ⟨sub10_1658, List.forall_mem_cons.2 ⟨sub10_1659, List.forall_mem_cons.2 ⟨sub10_1660, List.forall_mem_cons.2 ⟨sub10_1661, List.forall_mem_cons.2 ⟨sub10_1662, List.forall_mem_cons.2 ⟨sub10_1663, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_1664 : sub10 [4, 1, -6] = true := by decide +kernel
theorem sub10_1665 : sub10 [4, 1, -5] = true := by decide +kernel
theorem sub10_1666 : sub10 [4, 1, -4] = true := by decide +kernel
theorem sub10_1667 : sub10 [4, 1, -3] = true := by decide +kernel
theorem sub10_1668 : sub10 [4, 1, -2] = true := by decide +kernel
theorem sub10_1669 : sub10 [4, 1, -1] = true := by decide +kernel
theorem sub10_1670 : sub10 [4, 1, 0] = true := by decide +kernel
theorem sub10_1671 : sub10 [4, 1, 1] = true := by decide +kernel
theorem sub10_1672 : sub10 [4, 1, 2] = true := by decide +kernel
theorem sub10_1673 : sub10 [4, 1, 3] = true := by decide +kernel
theorem sub10_1674 : sub10 [4, 1, 4] = true := by decide +kernel
theorem sub10_1675 : sub10 [4, 1, 5] = true := by decide +kernel
theorem sub10_1676 : sub10 [4, 1, 6] = true := by decide +kernel
theorem sub10_1677 : sub10 [4, 1, 7] = true := by decide +kernel
theorem sub10_1678 : sub10 [4, 2, -6] = true := by decide +kernel
theorem sub10_1679 : sub10 [4, 2, -5] = true := by decide +kernel
theorem sub10_1680 : sub10 [4, 2, -4] = true := by decide +kernel
theorem sub10_1681 : sub10 [4, 2, -3] = true := by decide +kernel
theorem sub10_1682 : sub10 [4, 2, -2] = true := by decide +kernel
theorem sub10_1683 : sub10 [4, 2, -1] = true := by decide +kernel
theorem sub10_1684 : sub10 [4, 2, 0] = true := by decide +kernel
theorem sub10_1685 : sub10 [4, 2, 1] = true := by decide +kernel
theorem sub10_1686 : sub10 [4, 2, 2] = true := by decide +kernel
theorem sub10_1687 : sub10 [4, 2, 3] = true := by decide +kernel
theorem sub10_1688 : sub10 [4, 2, 4] = true := by decide +kernel
theorem sub10_1689 : sub10 [4, 2, 5] = true := by decide +kernel
theorem sub10_1690 : sub10 [4, 2, 6] = true := by decide +kernel
theorem sub10_1691 : sub10 [4, 2, 7] = true := by decide +kernel
theorem sub10_1692 : sub10 [4, 3] = true := by decide +kernel
theorem sub10_1693 : sub10 [4, 4] = true := by decide +kernel
theorem sub10_1694 : sub10 [4, 5] = true := by decide +kernel
theorem sub10_1695 : sub10 [5, -9] = true := by decide +kernel
theorem sb10_52 : ∀ q ∈ blk10_52, sub10 q = true := by
  unfold blk10_52
  exact List.forall_mem_cons.2 ⟨sub10_1664, List.forall_mem_cons.2 ⟨sub10_1665, List.forall_mem_cons.2 ⟨sub10_1666, List.forall_mem_cons.2 ⟨sub10_1667, List.forall_mem_cons.2 ⟨sub10_1668, List.forall_mem_cons.2 ⟨sub10_1669, List.forall_mem_cons.2 ⟨sub10_1670, List.forall_mem_cons.2 ⟨sub10_1671, List.forall_mem_cons.2 ⟨sub10_1672, List.forall_mem_cons.2 ⟨sub10_1673, List.forall_mem_cons.2 ⟨sub10_1674, List.forall_mem_cons.2 ⟨sub10_1675, List.forall_mem_cons.2 ⟨sub10_1676, List.forall_mem_cons.2 ⟨sub10_1677, List.forall_mem_cons.2 ⟨sub10_1678, List.forall_mem_cons.2 ⟨sub10_1679, List.forall_mem_cons.2 ⟨sub10_1680, List.forall_mem_cons.2 ⟨sub10_1681, List.forall_mem_cons.2 ⟨sub10_1682, List.forall_mem_cons.2 ⟨sub10_1683, List.forall_mem_cons.2 ⟨sub10_1684, List.forall_mem_cons.2 ⟨sub10_1685, List.forall_mem_cons.2 ⟨sub10_1686, List.forall_mem_cons.2 ⟨sub10_1687, List.forall_mem_cons.2 ⟨sub10_1688, List.forall_mem_cons.2 ⟨sub10_1689, List.forall_mem_cons.2 ⟨sub10_1690, List.forall_mem_cons.2 ⟨sub10_1691, List.forall_mem_cons.2 ⟨sub10_1692, List.forall_mem_cons.2 ⟨sub10_1693, List.forall_mem_cons.2 ⟨sub10_1694, List.forall_mem_cons.2 ⟨sub10_1695, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_1696 : sub10 [5, -8] = true := by decide +kernel
theorem sub10_1697 : sub10 [5, -7] = true := by decide +kernel
theorem sub10_1698 : sub10 [5, -6] = true := by decide +kernel
theorem sub10_1699 : sub10 [5, -5] = true := by decide +kernel
theorem sub10_1700 : sub10 [5, -4, -4] = true := by decide +kernel
theorem sub10_1701 : sub10 [5, -4, -3] = true := by decide +kernel
theorem sub10_1702 : sub10 [5, -4, -2] = true := by decide +kernel
theorem sub10_1703 : sub10 [5, -4, -1] = true := by decide +kernel
theorem sub10_1704 : sub10 [5, -4, 0] = true := by decide +kernel
theorem sub10_1705 : sub10 [5, -4, 1] = true := by decide +kernel
theorem sub10_1706 : sub10 [5, -4, 2] = true := by decide +kernel
theorem sub10_1707 : sub10 [5, -4, 3] = true := by decide +kernel
theorem sub10_1708 : sub10 [5, -4, 4] = true := by decide +kernel
theorem sub10_1709 : sub10 [5, -4, 5] = true := by decide +kernel
theorem sub10_1710 : sub10 [5, -4, 6] = true := by decide +kernel
theorem sub10_1711 : sub10 [5, -4, 7] = true := by decide +kernel
theorem sub10_1712 : sub10 [5, -4, 8] = true := by decide +kernel
theorem sub10_1713 : sub10 [5, -3, -5] = true := by decide +kernel
theorem sub10_1714 : sub10 [5, -3, -4] = true := by decide +kernel
theorem sub10_1715 : sub10 [5, -3, -3] = true := by decide +kernel
theorem sub10_1716 : sub10 [5, -3, -2] = true := by decide +kernel
theorem sub10_1717 : sub10 [5, -3, -1] = true := by decide +kernel
theorem sub10_1718 : sub10 [5, -3, 0] = true := by decide +kernel
theorem sub10_1719 : sub10 [5, -3, 1] = true := by decide +kernel
theorem sub10_1720 : sub10 [5, -3, 2] = true := by decide +kernel
theorem sub10_1721 : sub10 [5, -3, 3] = true := by decide +kernel
theorem sub10_1722 : sub10 [5, -3, 4] = true := by decide +kernel
theorem sub10_1723 : sub10 [5, -3, 5] = true := by decide +kernel
theorem sub10_1724 : sub10 [5, -3, 6] = true := by decide +kernel
theorem sub10_1725 : sub10 [5, -3, 7] = true := by decide +kernel
theorem sub10_1726 : sub10 [5, -3, 8] = true := by decide +kernel
theorem sub10_1727 : sub10 [5, -2, -5] = true := by decide +kernel
theorem sb10_53 : ∀ q ∈ blk10_53, sub10 q = true := by
  unfold blk10_53
  exact List.forall_mem_cons.2 ⟨sub10_1696, List.forall_mem_cons.2 ⟨sub10_1697, List.forall_mem_cons.2 ⟨sub10_1698, List.forall_mem_cons.2 ⟨sub10_1699, List.forall_mem_cons.2 ⟨sub10_1700, List.forall_mem_cons.2 ⟨sub10_1701, List.forall_mem_cons.2 ⟨sub10_1702, List.forall_mem_cons.2 ⟨sub10_1703, List.forall_mem_cons.2 ⟨sub10_1704, List.forall_mem_cons.2 ⟨sub10_1705, List.forall_mem_cons.2 ⟨sub10_1706, List.forall_mem_cons.2 ⟨sub10_1707, List.forall_mem_cons.2 ⟨sub10_1708, List.forall_mem_cons.2 ⟨sub10_1709, List.forall_mem_cons.2 ⟨sub10_1710, List.forall_mem_cons.2 ⟨sub10_1711, List.forall_mem_cons.2 ⟨sub10_1712, List.forall_mem_cons.2 ⟨sub10_1713, List.forall_mem_cons.2 ⟨sub10_1714, List.forall_mem_cons.2 ⟨sub10_1715, List.forall_mem_cons.2 ⟨sub10_1716, List.forall_mem_cons.2 ⟨sub10_1717, List.forall_mem_cons.2 ⟨sub10_1718, List.forall_mem_cons.2 ⟨sub10_1719, List.forall_mem_cons.2 ⟨sub10_1720, List.forall_mem_cons.2 ⟨sub10_1721, List.forall_mem_cons.2 ⟨sub10_1722, List.forall_mem_cons.2 ⟨sub10_1723, List.forall_mem_cons.2 ⟨sub10_1724, List.forall_mem_cons.2 ⟨sub10_1725, List.forall_mem_cons.2 ⟨sub10_1726, List.forall_mem_cons.2 ⟨sub10_1727, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_1728 : sub10 [5, -2, -4] = true := by decide +kernel
theorem sub10_1729 : sub10 [5, -2, -3] = true := by decide +kernel
theorem sub10_1730 : sub10 [5, -2, -2] = true := by decide +kernel
theorem sub10_1731 : sub10 [5, -2, -1] = true := by decide +kernel
theorem sub10_1732 : sub10 [5, -2, 0] = true := by decide +kernel
theorem sub10_1733 : sub10 [5, -2, 1] = true := by decide +kernel
theorem sub10_1734 : sub10 [5, -2, 2] = true := by decide +kernel
theorem sub10_1735 : sub10 [5, -2, 3] = true := by decide +kernel
theorem sub10_1736 : sub10 [5, -2, 4] = true := by decide +kernel
theorem sub10_1737 : sub10 [5, -2, 5] = true := by decide +kernel
theorem sub10_1738 : sub10 [5, -2, 6] = true := by decide +kernel
theorem sub10_1739 : sub10 [5, -2, 7] = true := by decide +kernel
theorem sub10_1740 : sub10 [5, -2, 8] = true := by decide +kernel
theorem sub10_1741 : sub10 [5, -1, -5] = true := by decide +kernel
theorem sub10_1742 : sub10 [5, -1, -4] = true := by decide +kernel
theorem sub10_1743 : sub10 [5, -1, -3] = true := by decide +kernel
theorem sub10_1744 : sub10 [5, -1, -2] = true := by decide +kernel
theorem sub10_1745 : sub10 [5, -1, -1] = true := by decide +kernel
theorem sub10_1746 : sub10 [5, -1, 0] = true := by decide +kernel
theorem sub10_1747 : sub10 [5, -1, 1] = true := by decide +kernel
theorem sub10_1748 : sub10 [5, -1, 2] = true := by decide +kernel
theorem sub10_1749 : sub10 [5, -1, 3] = true := by decide +kernel
theorem sub10_1750 : sub10 [5, -1, 4] = true := by decide +kernel
theorem sub10_1751 : sub10 [5, -1, 5] = true := by decide +kernel
theorem sub10_1752 : sub10 [5, -1, 6] = true := by decide +kernel
theorem sub10_1753 : sub10 [5, -1, 7] = true := by decide +kernel
theorem sub10_1754 : sub10 [5, -1, 8] = true := by decide +kernel
theorem sub10_1755 : sub10 [5, 0, -5] = true := by decide +kernel
theorem sub10_1756 : sub10 [5, 0, -4] = true := by decide +kernel
theorem sub10_1757 : sub10 [5, 0, -3] = true := by decide +kernel
theorem sub10_1758 : sub10 [5, 0, -2] = true := by decide +kernel
theorem sub10_1759 : sub10 [5, 0, -1] = true := by decide +kernel
theorem sb10_54 : ∀ q ∈ blk10_54, sub10 q = true := by
  unfold blk10_54
  exact List.forall_mem_cons.2 ⟨sub10_1728, List.forall_mem_cons.2 ⟨sub10_1729, List.forall_mem_cons.2 ⟨sub10_1730, List.forall_mem_cons.2 ⟨sub10_1731, List.forall_mem_cons.2 ⟨sub10_1732, List.forall_mem_cons.2 ⟨sub10_1733, List.forall_mem_cons.2 ⟨sub10_1734, List.forall_mem_cons.2 ⟨sub10_1735, List.forall_mem_cons.2 ⟨sub10_1736, List.forall_mem_cons.2 ⟨sub10_1737, List.forall_mem_cons.2 ⟨sub10_1738, List.forall_mem_cons.2 ⟨sub10_1739, List.forall_mem_cons.2 ⟨sub10_1740, List.forall_mem_cons.2 ⟨sub10_1741, List.forall_mem_cons.2 ⟨sub10_1742, List.forall_mem_cons.2 ⟨sub10_1743, List.forall_mem_cons.2 ⟨sub10_1744, List.forall_mem_cons.2 ⟨sub10_1745, List.forall_mem_cons.2 ⟨sub10_1746, List.forall_mem_cons.2 ⟨sub10_1747, List.forall_mem_cons.2 ⟨sub10_1748, List.forall_mem_cons.2 ⟨sub10_1749, List.forall_mem_cons.2 ⟨sub10_1750, List.forall_mem_cons.2 ⟨sub10_1751, List.forall_mem_cons.2 ⟨sub10_1752, List.forall_mem_cons.2 ⟨sub10_1753, List.forall_mem_cons.2 ⟨sub10_1754, List.forall_mem_cons.2 ⟨sub10_1755, List.forall_mem_cons.2 ⟨sub10_1756, List.forall_mem_cons.2 ⟨sub10_1757, List.forall_mem_cons.2 ⟨sub10_1758, List.forall_mem_cons.2 ⟨sub10_1759, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_1760 : sub10 [5, 0, 0] = true := by decide +kernel
theorem sub10_1761 : sub10 [5, 0, 1] = true := by decide +kernel
theorem sub10_1762 : sub10 [5, 0, 2] = true := by decide +kernel
theorem sub10_1763 : sub10 [5, 0, 3] = true := by decide +kernel
theorem sub10_1764 : sub10 [5, 0, 4] = true := by decide +kernel
theorem sub10_1765 : sub10 [5, 0, 5] = true := by decide +kernel
theorem sub10_1766 : sub10 [5, 0, 6] = true := by decide +kernel
theorem sub10_1767 : sub10 [5, 0, 7] = true := by decide +kernel
theorem sub10_1768 : sub10 [5, 1] = true := by decide +kernel
theorem sub10_1769 : sub10 [5, 2] = true := by decide +kernel
theorem sub10_1770 : sub10 [5, 3] = true := by decide +kernel
theorem sub10_1771 : sub10 [6, -8] = true := by decide +kernel
theorem sub10_1772 : sub10 [6, -7] = true := by decide +kernel
theorem sub10_1773 : sub10 [6, -6] = true := by decide +kernel
theorem sub10_1774 : sub10 [6, -5] = true := by decide +kernel
theorem sub10_1775 : sub10 [6, -4] = true := by decide +kernel
theorem sub10_1776 : sub10 [6, -3] = true := by decide +kernel
theorem sub10_1777 : sub10 [6, -2] = true := by decide +kernel
theorem sub10_1778 : sub10 [6, -1] = true := by decide +kernel
theorem sub10_1779 : sub10 [6, 0] = true := by decide +kernel
theorem sub10_1780 : sub10 [6, 1] = true := by decide +kernel
theorem sub10_1781 : sub10 [6, 2] = true := by decide +kernel
theorem sub10_1782 : sub10 [7] = true := by decide +kernel
theorem sb10_55 : ∀ q ∈ blk10_55, sub10 q = true := by
  unfold blk10_55
  exact List.forall_mem_cons.2 ⟨sub10_1760, List.forall_mem_cons.2 ⟨sub10_1761, List.forall_mem_cons.2 ⟨sub10_1762, List.forall_mem_cons.2 ⟨sub10_1763, List.forall_mem_cons.2 ⟨sub10_1764, List.forall_mem_cons.2 ⟨sub10_1765, List.forall_mem_cons.2 ⟨sub10_1766, List.forall_mem_cons.2 ⟨sub10_1767, List.forall_mem_cons.2 ⟨sub10_1768, List.forall_mem_cons.2 ⟨sub10_1769, List.forall_mem_cons.2 ⟨sub10_1770, List.forall_mem_cons.2 ⟨sub10_1771, List.forall_mem_cons.2 ⟨sub10_1772, List.forall_mem_cons.2 ⟨sub10_1773, List.forall_mem_cons.2 ⟨sub10_1774, List.forall_mem_cons.2 ⟨sub10_1775, List.forall_mem_cons.2 ⟨sub10_1776, List.forall_mem_cons.2 ⟨sub10_1777, List.forall_mem_cons.2 ⟨sub10_1778, List.forall_mem_cons.2 ⟨sub10_1779, List.forall_mem_cons.2 ⟨sub10_1780, List.forall_mem_cons.2 ⟨sub10_1781, List.forall_mem_cons.2 ⟨sub10_1782, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub11_0 : sub11 [-5, -4] = true := by decide +kernel
theorem sub11_1 : sub11 [-5, -3] = true := by decide +kernel
theorem sub11_2 : sub11 [-5, -2] = true := by decide +kernel
theorem sub11_3 : sub11 [-5, -1] = true := by decide +kernel
theorem sub11_4 : sub11 [-5, 0] = true := by decide +kernel
theorem sub11_5 : sub11 [-5, 1] = true := by decide +kernel
theorem sub11_6 : sub11 [-5, 2] = true := by decide +kernel
theorem sub11_7 : sub11 [-4, -5] = true := by decide +kernel
theorem sub11_8 : sub11 [-4, -4] = true := by decide +kernel
theorem sub11_9 : sub11 [-4, -3] = true := by decide +kernel
theorem sub11_10 : sub11 [-4, -2] = true := by decide +kernel
theorem sub11_11 : sub11 [-4, -1, -7] = true := by decide +kernel
theorem sub11_12 : sub11 [-4, -1, -6] = true := by decide +kernel
theorem sub11_13 : sub11 [-4, -1, -5] = true := by decide +kernel
theorem sub11_14 : sub11 [-4, -1, -4] = true := by decide +kernel
theorem sub11_15 : sub11 [-4, -1, -3] = true := by decide +kernel
theorem sub11_16 : sub11 [-4, -1, -2] = true := by decide +kernel
theorem sub11_17 : sub11 [-4, -1, -1] = true := by decide +kernel
theorem sub11_18 : sub11 [-4, -1, 0] = true := by decide +kernel
theorem sub11_19 : sub11 [-4, -1, 1] = true := by decide +kernel
theorem sub11_20 : sub11 [-4, -1, 2] = true := by decide +kernel
theorem sub11_21 : sub11 [-4, -1, 3] = true := by decide +kernel
theorem sub11_22 : sub11 [-4, -1, 4] = true := by decide +kernel
theorem sub11_23 : sub11 [-4, -1, 5] = true := by decide +kernel
theorem sub11_24 : sub11 [-4, -1, 6] = true := by decide +kernel
theorem sub11_25 : sub11 [-4, 0, -6] = true := by decide +kernel
theorem sub11_26 : sub11 [-4, 0, -5] = true := by decide +kernel
theorem sub11_27 : sub11 [-4, 0, -4] = true := by decide +kernel
theorem sub11_28 : sub11 [-4, 0, -3] = true := by decide +kernel
theorem sub11_29 : sub11 [-4, 0, -2] = true := by decide +kernel
theorem sub11_30 : sub11 [-4, 0, -1] = true := by decide +kernel
theorem sub11_31 : sub11 [-4, 0, 0] = true := by decide +kernel
theorem sb11_0 : ∀ q ∈ blk11_0, sub11 q = true := by
  unfold blk11_0
  exact List.forall_mem_cons.2 ⟨sub11_0, List.forall_mem_cons.2 ⟨sub11_1, List.forall_mem_cons.2 ⟨sub11_2, List.forall_mem_cons.2 ⟨sub11_3, List.forall_mem_cons.2 ⟨sub11_4, List.forall_mem_cons.2 ⟨sub11_5, List.forall_mem_cons.2 ⟨sub11_6, List.forall_mem_cons.2 ⟨sub11_7, List.forall_mem_cons.2 ⟨sub11_8, List.forall_mem_cons.2 ⟨sub11_9, List.forall_mem_cons.2 ⟨sub11_10, List.forall_mem_cons.2 ⟨sub11_11, List.forall_mem_cons.2 ⟨sub11_12, List.forall_mem_cons.2 ⟨sub11_13, List.forall_mem_cons.2 ⟨sub11_14, List.forall_mem_cons.2 ⟨sub11_15, List.forall_mem_cons.2 ⟨sub11_16, List.forall_mem_cons.2 ⟨sub11_17, List.forall_mem_cons.2 ⟨sub11_18, List.forall_mem_cons.2 ⟨sub11_19, List.forall_mem_cons.2 ⟨sub11_20, List.forall_mem_cons.2 ⟨sub11_21, List.forall_mem_cons.2 ⟨sub11_22, List.forall_mem_cons.2 ⟨sub11_23, List.forall_mem_cons.2 ⟨sub11_24, List.forall_mem_cons.2 ⟨sub11_25, List.forall_mem_cons.2 ⟨sub11_26, List.forall_mem_cons.2 ⟨sub11_27, List.forall_mem_cons.2 ⟨sub11_28, List.forall_mem_cons.2 ⟨sub11_29, List.forall_mem_cons.2 ⟨sub11_30, List.forall_mem_cons.2 ⟨sub11_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C074
