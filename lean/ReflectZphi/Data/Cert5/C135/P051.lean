import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_3_1504 : subd9_3 [2, 4, 5] = true := by decide +kernel
theorem subd9_3_1505 : subd9_3 [2, 4, 6] = true := by decide +kernel
theorem subd9_3_1506 : subd9_3 [2, 4, 7] = true := by decide +kernel
theorem subd9_3_1507 : subd9_3 [2, 4, 8] = true := by decide +kernel
theorem subd9_3_1508 : subd9_3 [2, 4, 9] = true := by decide +kernel
theorem subd9_3_1509 : subd9_3 [2, 5] = true := by decide +kernel
theorem subd9_3_1510 : subd9_3 [3, -6] = true := by decide +kernel
theorem subd9_3_1511 : subd9_3 [3, -5] = true := by decide +kernel
theorem subd9_3_1512 : subd9_3 [3, -4, -7] = true := by decide +kernel
theorem subd9_3_1513 : subd9_3 [3, -4, -6] = true := by decide +kernel
theorem subd9_3_1514 : subd9_3 [3, -4, -5] = true := by decide +kernel
theorem subd9_3_1515 : subd9_3 [3, -4, -4] = true := by decide +kernel
theorem subd9_3_1516 : subd9_3 [3, -4, -3] = true := by decide +kernel
theorem subd9_3_1517 : subd9_3 [3, -4, -2] = true := by decide +kernel
theorem subd9_3_1518 : subd9_3 [3, -4, -1] = true := by decide +kernel
theorem subd9_3_1519 : subd9_3 [3, -4, 0] = true := by decide +kernel
theorem subd9_3_1520 : subd9_3 [3, -4, 1] = true := by decide +kernel
theorem subd9_3_1521 : subd9_3 [3, -4, 2] = true := by decide +kernel
theorem subd9_3_1522 : subd9_3 [3, -4, 3] = true := by decide +kernel
theorem subd9_3_1523 : subd9_3 [3, -4, 4] = true := by decide +kernel
theorem subd9_3_1524 : subd9_3 [3, -4, 5] = true := by decide +kernel
theorem subd9_3_1525 : subd9_3 [3, -4, 6] = true := by decide +kernel
theorem subd9_3_1526 : subd9_3 [3, -4, 7] = true := by decide +kernel
theorem subd9_3_1527 : subd9_3 [3, -4, 8] = true := by decide +kernel
theorem subd9_3_1528 : subd9_3 [3, -3, -8] = true := by decide +kernel
theorem subd9_3_1529 : subd9_3 [3, -3, -7] = true := by decide +kernel
theorem subd9_3_1530 : subd9_3 [3, -3, -6] = true := by decide +kernel
theorem subd9_3_1531 : subd9_3 [3, -3, -5] = true := by decide +kernel
theorem subd9_3_1532 : subd9_3 [3, -3, -4] = true := by decide +kernel
theorem subd9_3_1533 : subd9_3 [3, -3, -3] = true := by decide +kernel
theorem subd9_3_1534 : subd9_3 [3, -3, -2] = true := by decide +kernel
theorem subd9_3_1535 : subd9_3 [3, -3, -1] = true := by decide +kernel
theorem sbd9_3_47 : ∀ q ∈ blkd9_3_47, subd9_3 q = true := by
  unfold blkd9_3_47
  exact List.forall_mem_cons.2 ⟨subd9_3_1504, List.forall_mem_cons.2 ⟨subd9_3_1505, List.forall_mem_cons.2 ⟨subd9_3_1506, List.forall_mem_cons.2 ⟨subd9_3_1507, List.forall_mem_cons.2 ⟨subd9_3_1508, List.forall_mem_cons.2 ⟨subd9_3_1509, List.forall_mem_cons.2 ⟨subd9_3_1510, List.forall_mem_cons.2 ⟨subd9_3_1511, List.forall_mem_cons.2 ⟨subd9_3_1512, List.forall_mem_cons.2 ⟨subd9_3_1513, List.forall_mem_cons.2 ⟨subd9_3_1514, List.forall_mem_cons.2 ⟨subd9_3_1515, List.forall_mem_cons.2 ⟨subd9_3_1516, List.forall_mem_cons.2 ⟨subd9_3_1517, List.forall_mem_cons.2 ⟨subd9_3_1518, List.forall_mem_cons.2 ⟨subd9_3_1519, List.forall_mem_cons.2 ⟨subd9_3_1520, List.forall_mem_cons.2 ⟨subd9_3_1521, List.forall_mem_cons.2 ⟨subd9_3_1522, List.forall_mem_cons.2 ⟨subd9_3_1523, List.forall_mem_cons.2 ⟨subd9_3_1524, List.forall_mem_cons.2 ⟨subd9_3_1525, List.forall_mem_cons.2 ⟨subd9_3_1526, List.forall_mem_cons.2 ⟨subd9_3_1527, List.forall_mem_cons.2 ⟨subd9_3_1528, List.forall_mem_cons.2 ⟨subd9_3_1529, List.forall_mem_cons.2 ⟨subd9_3_1530, List.forall_mem_cons.2 ⟨subd9_3_1531, List.forall_mem_cons.2 ⟨subd9_3_1532, List.forall_mem_cons.2 ⟨subd9_3_1533, List.forall_mem_cons.2 ⟨subd9_3_1534, List.forall_mem_cons.2 ⟨subd9_3_1535, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_1536 : subd9_3 [3, -3, 0] = true := by decide +kernel
theorem subd9_3_1537 : subd9_3 [3, -3, 1] = true := by decide +kernel
theorem subd9_3_1538 : subd9_3 [3, -3, 2] = true := by decide +kernel
theorem subd9_3_1539 : subd9_3 [3, -3, 3] = true := by decide +kernel
theorem subd9_3_1540 : subd9_3 [3, -3, 4] = true := by decide +kernel
theorem subd9_3_1541 : subd9_3 [3, -3, 5] = true := by decide +kernel
theorem subd9_3_1542 : subd9_3 [3, -3, 6] = true := by decide +kernel
theorem subd9_3_1543 : subd9_3 [3, -3, 7] = true := by decide +kernel
theorem subd9_3_1544 : subd9_3 [3, -3, 8] = true := by decide +kernel
theorem subd9_3_1545 : subd9_3 [3, -3, 9] = true := by decide +kernel
theorem subd9_3_1546 : subd9_3 [3, -3, 10] = true := by decide +kernel
theorem subd9_3_1547 : subd9_3 [3, -2, -9] = true := by decide +kernel
theorem subd9_3_1548 : subd9_3 [3, -2, -8] = true := by decide +kernel
theorem subd9_3_1549 : subd9_3 [3, -2, -7] = true := by decide +kernel
theorem subd9_3_1550 : subd9_3 [3, -2, -6] = true := by decide +kernel
theorem subd9_3_1551 : subd9_3 [3, -2, -5] = true := by decide +kernel
theorem subd9_3_1552 : subd9_3 [3, -2, -4] = true := by decide +kernel
theorem subd9_3_1553 : subd9_3 [3, -2, -3] = true := by decide +kernel
theorem subd9_3_1554 : subd9_3 [3, -2, -2] = true := by decide +kernel
theorem subd9_3_1555 : subd9_3 [3, -2, -1] = true := by decide +kernel
theorem subd9_3_1556 : subd9_3 [3, -2, 0] = true := by decide +kernel
theorem subd9_3_1557 : subd9_3 [3, -2, 1] = true := by decide +kernel
theorem subd9_3_1558 : subd9_3 [3, -2, 2] = true := by decide +kernel
theorem subd9_3_1559 : subd9_3 [3, -2, 3] = true := by decide +kernel
theorem subd9_3_1560 : subd9_3 [3, -2, 4] = true := by decide +kernel
theorem subd9_3_1561 : subd9_3 [3, -2, 5] = true := by decide +kernel
theorem subd9_3_1562 : subd9_3 [3, -2, 6] = true := by decide +kernel
theorem subd9_3_1563 : subd9_3 [3, -2, 7] = true := by decide +kernel
theorem subd9_3_1564 : subd9_3 [3, -2, 8] = true := by decide +kernel
theorem subd9_3_1565 : subd9_3 [3, -2, 9] = true := by decide +kernel
theorem subd9_3_1566 : subd9_3 [3, -2, 10] = true := by decide +kernel
theorem subd9_3_1567 : subd9_3 [3, -2, 11] = true := by decide +kernel
theorem sbd9_3_48 : ∀ q ∈ blkd9_3_48, subd9_3 q = true := by
  unfold blkd9_3_48
  exact List.forall_mem_cons.2 ⟨subd9_3_1536, List.forall_mem_cons.2 ⟨subd9_3_1537, List.forall_mem_cons.2 ⟨subd9_3_1538, List.forall_mem_cons.2 ⟨subd9_3_1539, List.forall_mem_cons.2 ⟨subd9_3_1540, List.forall_mem_cons.2 ⟨subd9_3_1541, List.forall_mem_cons.2 ⟨subd9_3_1542, List.forall_mem_cons.2 ⟨subd9_3_1543, List.forall_mem_cons.2 ⟨subd9_3_1544, List.forall_mem_cons.2 ⟨subd9_3_1545, List.forall_mem_cons.2 ⟨subd9_3_1546, List.forall_mem_cons.2 ⟨subd9_3_1547, List.forall_mem_cons.2 ⟨subd9_3_1548, List.forall_mem_cons.2 ⟨subd9_3_1549, List.forall_mem_cons.2 ⟨subd9_3_1550, List.forall_mem_cons.2 ⟨subd9_3_1551, List.forall_mem_cons.2 ⟨subd9_3_1552, List.forall_mem_cons.2 ⟨subd9_3_1553, List.forall_mem_cons.2 ⟨subd9_3_1554, List.forall_mem_cons.2 ⟨subd9_3_1555, List.forall_mem_cons.2 ⟨subd9_3_1556, List.forall_mem_cons.2 ⟨subd9_3_1557, List.forall_mem_cons.2 ⟨subd9_3_1558, List.forall_mem_cons.2 ⟨subd9_3_1559, List.forall_mem_cons.2 ⟨subd9_3_1560, List.forall_mem_cons.2 ⟨subd9_3_1561, List.forall_mem_cons.2 ⟨subd9_3_1562, List.forall_mem_cons.2 ⟨subd9_3_1563, List.forall_mem_cons.2 ⟨subd9_3_1564, List.forall_mem_cons.2 ⟨subd9_3_1565, List.forall_mem_cons.2 ⟨subd9_3_1566, List.forall_mem_cons.2 ⟨subd9_3_1567, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_1568 : subd9_3 [3, -1, -10] = true := by decide +kernel
theorem subd9_3_1569 : subd9_3 [3, -1, -9] = true := by decide +kernel
theorem subd9_3_1570 : subd9_3 [3, -1, -8] = true := by decide +kernel
theorem subd9_3_1571 : subd9_3 [3, -1, -7] = true := by decide +kernel
theorem subd9_3_1572 : subd9_3 [3, -1, -6] = true := by decide +kernel
theorem subd9_3_1573 : subd9_3 [3, -1, -5] = true := by decide +kernel
theorem subd9_3_1574 : subd9_3 [3, -1, -4] = true := by decide +kernel
theorem subd9_3_1575 : subd9_3 [3, -1, -3] = true := by decide +kernel
theorem subd9_3_1576 : subd9_3 [3, -1, -2] = true := by decide +kernel
theorem subd9_3_1577 : subd9_3 [3, -1, -1] = true := by decide +kernel
theorem subd9_3_1578 : subd9_3 [3, -1, 0] = true := by decide +kernel
theorem subd9_3_1579 : subd9_3 [3, -1, 1] = true := by decide +kernel
theorem subd9_3_1580 : subd9_3 [3, -1, 2] = true := by decide +kernel
theorem subd9_3_1581 : subd9_3 [3, -1, 3] = true := by decide +kernel
theorem subd9_3_1582 : subd9_3 [3, -1, 4] = true := by decide +kernel
theorem subd9_3_1583 : subd9_3 [3, -1, 5] = true := by decide +kernel
theorem subd9_3_1584 : subd9_3 [3, -1, 6] = true := by decide +kernel
theorem subd9_3_1585 : subd9_3 [3, -1, 7] = true := by decide +kernel
theorem subd9_3_1586 : subd9_3 [3, -1, 8] = true := by decide +kernel
theorem subd9_3_1587 : subd9_3 [3, -1, 9] = true := by decide +kernel
theorem subd9_3_1588 : subd9_3 [3, -1, 10] = true := by decide +kernel
theorem subd9_3_1589 : subd9_3 [3, -1, 11] = true := by decide +kernel
theorem subd9_3_1590 : subd9_3 [3, 0, -10] = true := by decide +kernel
theorem subd9_3_1591 : subd9_3 [3, 0, -9] = true := by decide +kernel
theorem subd9_3_1592 : subd9_3 [3, 0, -8] = true := by decide +kernel
theorem subd9_3_1593 : subd9_3 [3, 0, -7] = true := by decide +kernel
theorem subd9_3_1594 : subd9_3 [3, 0, -6] = true := by decide +kernel
theorem subd9_3_1595 : subd9_3 [3, 0, -5] = true := by decide +kernel
theorem subd9_3_1596 : subd9_3 [3, 0, -4] = true := by decide +kernel
theorem subd9_3_1597 : subd9_3 [3, 0, -3] = true := by decide +kernel
theorem subd9_3_1598 : subd9_3 [3, 0, -2] = true := by decide +kernel
theorem subd9_3_1599 : subd9_3 [3, 0, -1] = true := by decide +kernel
theorem sbd9_3_49 : ∀ q ∈ blkd9_3_49, subd9_3 q = true := by
  unfold blkd9_3_49
  exact List.forall_mem_cons.2 ⟨subd9_3_1568, List.forall_mem_cons.2 ⟨subd9_3_1569, List.forall_mem_cons.2 ⟨subd9_3_1570, List.forall_mem_cons.2 ⟨subd9_3_1571, List.forall_mem_cons.2 ⟨subd9_3_1572, List.forall_mem_cons.2 ⟨subd9_3_1573, List.forall_mem_cons.2 ⟨subd9_3_1574, List.forall_mem_cons.2 ⟨subd9_3_1575, List.forall_mem_cons.2 ⟨subd9_3_1576, List.forall_mem_cons.2 ⟨subd9_3_1577, List.forall_mem_cons.2 ⟨subd9_3_1578, List.forall_mem_cons.2 ⟨subd9_3_1579, List.forall_mem_cons.2 ⟨subd9_3_1580, List.forall_mem_cons.2 ⟨subd9_3_1581, List.forall_mem_cons.2 ⟨subd9_3_1582, List.forall_mem_cons.2 ⟨subd9_3_1583, List.forall_mem_cons.2 ⟨subd9_3_1584, List.forall_mem_cons.2 ⟨subd9_3_1585, List.forall_mem_cons.2 ⟨subd9_3_1586, List.forall_mem_cons.2 ⟨subd9_3_1587, List.forall_mem_cons.2 ⟨subd9_3_1588, List.forall_mem_cons.2 ⟨subd9_3_1589, List.forall_mem_cons.2 ⟨subd9_3_1590, List.forall_mem_cons.2 ⟨subd9_3_1591, List.forall_mem_cons.2 ⟨subd9_3_1592, List.forall_mem_cons.2 ⟨subd9_3_1593, List.forall_mem_cons.2 ⟨subd9_3_1594, List.forall_mem_cons.2 ⟨subd9_3_1595, List.forall_mem_cons.2 ⟨subd9_3_1596, List.forall_mem_cons.2 ⟨subd9_3_1597, List.forall_mem_cons.2 ⟨subd9_3_1598, List.forall_mem_cons.2 ⟨subd9_3_1599, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_1600 : subd9_3 [3, 0, 0] = true := by decide +kernel
theorem subd9_3_1601 : subd9_3 [3, 0, 1] = true := by decide +kernel
theorem subd9_3_1602 : subd9_3 [3, 0, 2] = true := by decide +kernel
theorem subd9_3_1603 : subd9_3 [3, 0, 3] = true := by decide +kernel
theorem subd9_3_1604 : subd9_3 [3, 0, 4] = true := by decide +kernel
theorem subd9_3_1605 : subd9_3 [3, 0, 5] = true := by decide +kernel
theorem subd9_3_1606 : subd9_3 [3, 0, 6] = true := by decide +kernel
theorem subd9_3_1607 : subd9_3 [3, 0, 7] = true := by decide +kernel
theorem subd9_3_1608 : subd9_3 [3, 0, 8] = true := by decide +kernel
theorem subd9_3_1609 : subd9_3 [3, 0, 9] = true := by decide +kernel
theorem subd9_3_1610 : subd9_3 [3, 0, 10] = true := by decide +kernel
theorem subd9_3_1611 : subd9_3 [3, 0, 11] = true := by decide +kernel
theorem subd9_3_1612 : subd9_3 [3, 0, 12] = true := by decide +kernel
theorem subd9_3_1613 : subd9_3 [3, 1, -10] = true := by decide +kernel
theorem subd9_3_1614 : subd9_3 [3, 1, -9] = true := by decide +kernel
theorem subd9_3_1615 : subd9_3 [3, 1, -8] = true := by decide +kernel
theorem subd9_3_1616 : subd9_3 [3, 1, -7] = true := by decide +kernel
theorem subd9_3_1617 : subd9_3 [3, 1, -6] = true := by decide +kernel
theorem subd9_3_1618 : subd9_3 [3, 1, -5] = true := by decide +kernel
theorem subd9_3_1619 : subd9_3 [3, 1, -4] = true := by decide +kernel
theorem subd9_3_1620 : subd9_3 [3, 1, -3] = true := by decide +kernel
theorem subd9_3_1621 : subd9_3 [3, 1, -2] = true := by decide +kernel
theorem subd9_3_1622 : subd9_3 [3, 1, -1] = true := by decide +kernel
theorem subd9_3_1623 : subd9_3 [3, 1, 0] = true := by decide +kernel
theorem subd9_3_1624 : subd9_3 [3, 1, 1] = true := by decide +kernel
theorem subd9_3_1625 : subd9_3 [3, 1, 2] = true := by decide +kernel
theorem subd9_3_1626 : subd9_3 [3, 1, 3] = true := by decide +kernel
theorem subd9_3_1627 : subd9_3 [3, 1, 4] = true := by decide +kernel
theorem subd9_3_1628 : subd9_3 [3, 1, 5] = true := by decide +kernel
theorem subd9_3_1629 : subd9_3 [3, 1, 6] = true := by decide +kernel
theorem subd9_3_1630 : subd9_3 [3, 1, 7] = true := by decide +kernel
theorem subd9_3_1631 : subd9_3 [3, 1, 8] = true := by decide +kernel
theorem sbd9_3_50 : ∀ q ∈ blkd9_3_50, subd9_3 q = true := by
  unfold blkd9_3_50
  exact List.forall_mem_cons.2 ⟨subd9_3_1600, List.forall_mem_cons.2 ⟨subd9_3_1601, List.forall_mem_cons.2 ⟨subd9_3_1602, List.forall_mem_cons.2 ⟨subd9_3_1603, List.forall_mem_cons.2 ⟨subd9_3_1604, List.forall_mem_cons.2 ⟨subd9_3_1605, List.forall_mem_cons.2 ⟨subd9_3_1606, List.forall_mem_cons.2 ⟨subd9_3_1607, List.forall_mem_cons.2 ⟨subd9_3_1608, List.forall_mem_cons.2 ⟨subd9_3_1609, List.forall_mem_cons.2 ⟨subd9_3_1610, List.forall_mem_cons.2 ⟨subd9_3_1611, List.forall_mem_cons.2 ⟨subd9_3_1612, List.forall_mem_cons.2 ⟨subd9_3_1613, List.forall_mem_cons.2 ⟨subd9_3_1614, List.forall_mem_cons.2 ⟨subd9_3_1615, List.forall_mem_cons.2 ⟨subd9_3_1616, List.forall_mem_cons.2 ⟨subd9_3_1617, List.forall_mem_cons.2 ⟨subd9_3_1618, List.forall_mem_cons.2 ⟨subd9_3_1619, List.forall_mem_cons.2 ⟨subd9_3_1620, List.forall_mem_cons.2 ⟨subd9_3_1621, List.forall_mem_cons.2 ⟨subd9_3_1622, List.forall_mem_cons.2 ⟨subd9_3_1623, List.forall_mem_cons.2 ⟨subd9_3_1624, List.forall_mem_cons.2 ⟨subd9_3_1625, List.forall_mem_cons.2 ⟨subd9_3_1626, List.forall_mem_cons.2 ⟨subd9_3_1627, List.forall_mem_cons.2 ⟨subd9_3_1628, List.forall_mem_cons.2 ⟨subd9_3_1629, List.forall_mem_cons.2 ⟨subd9_3_1630, List.forall_mem_cons.2 ⟨subd9_3_1631, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_1632 : subd9_3 [3, 1, 9] = true := by decide +kernel
theorem subd9_3_1633 : subd9_3 [3, 1, 10] = true := by decide +kernel
theorem subd9_3_1634 : subd9_3 [3, 1, 11] = true := by decide +kernel
theorem subd9_3_1635 : subd9_3 [3, 2, -9] = true := by decide +kernel
theorem subd9_3_1636 : subd9_3 [3, 2, -8] = true := by decide +kernel
theorem subd9_3_1637 : subd9_3 [3, 2, -7] = true := by decide +kernel
theorem subd9_3_1638 : subd9_3 [3, 2, -6] = true := by decide +kernel
theorem subd9_3_1639 : subd9_3 [3, 2, -5] = true := by decide +kernel
theorem subd9_3_1640 : subd9_3 [3, 2, -4] = true := by decide +kernel
theorem subd9_3_1641 : subd9_3 [3, 2, -3] = true := by decide +kernel
theorem subd9_3_1642 : subd9_3 [3, 2, -2] = true := by decide +kernel
theorem subd9_3_1643 : subd9_3 [3, 2, -1] = true := by decide +kernel
theorem subd9_3_1644 : subd9_3 [3, 2, 0] = true := by decide +kernel
theorem subd9_3_1645 : subd9_3 [3, 2, 1] = true := by decide +kernel
theorem subd9_3_1646 : subd9_3 [3, 2, 2] = true := by decide +kernel
theorem subd9_3_1647 : subd9_3 [3, 2, 3] = true := by decide +kernel
theorem subd9_3_1648 : subd9_3 [3, 2, 4] = true := by decide +kernel
theorem subd9_3_1649 : subd9_3 [3, 2, 5] = true := by decide +kernel
theorem subd9_3_1650 : subd9_3 [3, 2, 6] = true := by decide +kernel
theorem subd9_3_1651 : subd9_3 [3, 2, 7] = true := by decide +kernel
theorem subd9_3_1652 : subd9_3 [3, 2, 8] = true := by decide +kernel
theorem subd9_3_1653 : subd9_3 [3, 2, 9] = true := by decide +kernel
theorem subd9_3_1654 : subd9_3 [3, 2, 10] = true := by decide +kernel
theorem subd9_3_1655 : subd9_3 [3, 2, 11] = true := by decide +kernel
theorem subd9_3_1656 : subd9_3 [3, 3, -8] = true := by decide +kernel
theorem subd9_3_1657 : subd9_3 [3, 3, -7] = true := by decide +kernel
theorem subd9_3_1658 : subd9_3 [3, 3, -6] = true := by decide +kernel
theorem subd9_3_1659 : subd9_3 [3, 3, -5] = true := by decide +kernel
theorem subd9_3_1660 : subd9_3 [3, 3, -4] = true := by decide +kernel
theorem subd9_3_1661 : subd9_3 [3, 3, -3] = true := by decide +kernel
theorem subd9_3_1662 : subd9_3 [3, 3, -2] = true := by decide +kernel
theorem subd9_3_1663 : subd9_3 [3, 3, -1] = true := by decide +kernel
theorem sbd9_3_51 : ∀ q ∈ blkd9_3_51, subd9_3 q = true := by
  unfold blkd9_3_51
  exact List.forall_mem_cons.2 ⟨subd9_3_1632, List.forall_mem_cons.2 ⟨subd9_3_1633, List.forall_mem_cons.2 ⟨subd9_3_1634, List.forall_mem_cons.2 ⟨subd9_3_1635, List.forall_mem_cons.2 ⟨subd9_3_1636, List.forall_mem_cons.2 ⟨subd9_3_1637, List.forall_mem_cons.2 ⟨subd9_3_1638, List.forall_mem_cons.2 ⟨subd9_3_1639, List.forall_mem_cons.2 ⟨subd9_3_1640, List.forall_mem_cons.2 ⟨subd9_3_1641, List.forall_mem_cons.2 ⟨subd9_3_1642, List.forall_mem_cons.2 ⟨subd9_3_1643, List.forall_mem_cons.2 ⟨subd9_3_1644, List.forall_mem_cons.2 ⟨subd9_3_1645, List.forall_mem_cons.2 ⟨subd9_3_1646, List.forall_mem_cons.2 ⟨subd9_3_1647, List.forall_mem_cons.2 ⟨subd9_3_1648, List.forall_mem_cons.2 ⟨subd9_3_1649, List.forall_mem_cons.2 ⟨subd9_3_1650, List.forall_mem_cons.2 ⟨subd9_3_1651, List.forall_mem_cons.2 ⟨subd9_3_1652, List.forall_mem_cons.2 ⟨subd9_3_1653, List.forall_mem_cons.2 ⟨subd9_3_1654, List.forall_mem_cons.2 ⟨subd9_3_1655, List.forall_mem_cons.2 ⟨subd9_3_1656, List.forall_mem_cons.2 ⟨subd9_3_1657, List.forall_mem_cons.2 ⟨subd9_3_1658, List.forall_mem_cons.2 ⟨subd9_3_1659, List.forall_mem_cons.2 ⟨subd9_3_1660, List.forall_mem_cons.2 ⟨subd9_3_1661, List.forall_mem_cons.2 ⟨subd9_3_1662, List.forall_mem_cons.2 ⟨subd9_3_1663, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_1664 : subd9_3 [3, 3, 0] = true := by decide +kernel
theorem subd9_3_1665 : subd9_3 [3, 3, 1] = true := by decide +kernel
theorem subd9_3_1666 : subd9_3 [3, 3, 2] = true := by decide +kernel
theorem subd9_3_1667 : subd9_3 [3, 3, 3] = true := by decide +kernel
theorem subd9_3_1668 : subd9_3 [3, 3, 4] = true := by decide +kernel
theorem subd9_3_1669 : subd9_3 [3, 3, 5] = true := by decide +kernel
theorem subd9_3_1670 : subd9_3 [3, 3, 6] = true := by decide +kernel
theorem subd9_3_1671 : subd9_3 [3, 3, 7] = true := by decide +kernel
theorem subd9_3_1672 : subd9_3 [3, 3, 8] = true := by decide +kernel
theorem subd9_3_1673 : subd9_3 [3, 3, 9] = true := by decide +kernel
theorem subd9_3_1674 : subd9_3 [3, 3, 10] = true := by decide +kernel
theorem subd9_3_1675 : subd9_3 [3, 4, -7] = true := by decide +kernel
theorem subd9_3_1676 : subd9_3 [3, 4, -6] = true := by decide +kernel
theorem subd9_3_1677 : subd9_3 [3, 4, -5] = true := by decide +kernel
theorem subd9_3_1678 : subd9_3 [3, 4, -4] = true := by decide +kernel
theorem subd9_3_1679 : subd9_3 [3, 4, -3] = true := by decide +kernel
theorem subd9_3_1680 : subd9_3 [3, 4, -2] = true := by decide +kernel
theorem subd9_3_1681 : subd9_3 [3, 4, -1] = true := by decide +kernel
theorem subd9_3_1682 : subd9_3 [3, 4, 0] = true := by decide +kernel
theorem subd9_3_1683 : subd9_3 [3, 4, 1] = true := by decide +kernel
theorem subd9_3_1684 : subd9_3 [3, 4, 2] = true := by decide +kernel
theorem subd9_3_1685 : subd9_3 [3, 4, 3] = true := by decide +kernel
theorem subd9_3_1686 : subd9_3 [3, 4, 4] = true := by decide +kernel
theorem subd9_3_1687 : subd9_3 [3, 4, 5] = true := by decide +kernel
theorem subd9_3_1688 : subd9_3 [3, 4, 6] = true := by decide +kernel
theorem subd9_3_1689 : subd9_3 [3, 4, 7] = true := by decide +kernel
theorem subd9_3_1690 : subd9_3 [3, 4, 8] = true := by decide +kernel
theorem subd9_3_1691 : subd9_3 [3, 5] = true := by decide +kernel
theorem subd9_3_1692 : subd9_3 [4, -6] = true := by decide +kernel
theorem subd9_3_1693 : subd9_3 [4, -5] = true := by decide +kernel
theorem subd9_3_1694 : subd9_3 [4, -4] = true := by decide +kernel
theorem subd9_3_1695 : subd9_3 [4, -3, -7] = true := by decide +kernel
theorem sbd9_3_52 : ∀ q ∈ blkd9_3_52, subd9_3 q = true := by
  unfold blkd9_3_52
  exact List.forall_mem_cons.2 ⟨subd9_3_1664, List.forall_mem_cons.2 ⟨subd9_3_1665, List.forall_mem_cons.2 ⟨subd9_3_1666, List.forall_mem_cons.2 ⟨subd9_3_1667, List.forall_mem_cons.2 ⟨subd9_3_1668, List.forall_mem_cons.2 ⟨subd9_3_1669, List.forall_mem_cons.2 ⟨subd9_3_1670, List.forall_mem_cons.2 ⟨subd9_3_1671, List.forall_mem_cons.2 ⟨subd9_3_1672, List.forall_mem_cons.2 ⟨subd9_3_1673, List.forall_mem_cons.2 ⟨subd9_3_1674, List.forall_mem_cons.2 ⟨subd9_3_1675, List.forall_mem_cons.2 ⟨subd9_3_1676, List.forall_mem_cons.2 ⟨subd9_3_1677, List.forall_mem_cons.2 ⟨subd9_3_1678, List.forall_mem_cons.2 ⟨subd9_3_1679, List.forall_mem_cons.2 ⟨subd9_3_1680, List.forall_mem_cons.2 ⟨subd9_3_1681, List.forall_mem_cons.2 ⟨subd9_3_1682, List.forall_mem_cons.2 ⟨subd9_3_1683, List.forall_mem_cons.2 ⟨subd9_3_1684, List.forall_mem_cons.2 ⟨subd9_3_1685, List.forall_mem_cons.2 ⟨subd9_3_1686, List.forall_mem_cons.2 ⟨subd9_3_1687, List.forall_mem_cons.2 ⟨subd9_3_1688, List.forall_mem_cons.2 ⟨subd9_3_1689, List.forall_mem_cons.2 ⟨subd9_3_1690, List.forall_mem_cons.2 ⟨subd9_3_1691, List.forall_mem_cons.2 ⟨subd9_3_1692, List.forall_mem_cons.2 ⟨subd9_3_1693, List.forall_mem_cons.2 ⟨subd9_3_1694, List.forall_mem_cons.2 ⟨subd9_3_1695, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_1696 : subd9_3 [4, -3, -6] = true := by decide +kernel
theorem subd9_3_1697 : subd9_3 [4, -3, -5] = true := by decide +kernel
theorem subd9_3_1698 : subd9_3 [4, -3, -4] = true := by decide +kernel
theorem subd9_3_1699 : subd9_3 [4, -3, -3] = true := by decide +kernel
theorem subd9_3_1700 : subd9_3 [4, -3, -2] = true := by decide +kernel
theorem subd9_3_1701 : subd9_3 [4, -3, -1] = true := by decide +kernel
theorem subd9_3_1702 : subd9_3 [4, -3, 0] = true := by decide +kernel
theorem subd9_3_1703 : subd9_3 [4, -3, 1] = true := by decide +kernel
theorem subd9_3_1704 : subd9_3 [4, -3, 2] = true := by decide +kernel
theorem subd9_3_1705 : subd9_3 [4, -3, 3] = true := by decide +kernel
theorem subd9_3_1706 : subd9_3 [4, -3, 4] = true := by decide +kernel
theorem subd9_3_1707 : subd9_3 [4, -3, 5] = true := by decide +kernel
theorem subd9_3_1708 : subd9_3 [4, -3, 6] = true := by decide +kernel
theorem subd9_3_1709 : subd9_3 [4, -3, 7] = true := by decide +kernel
theorem subd9_3_1710 : subd9_3 [4, -3, 8] = true := by decide +kernel
theorem subd9_3_1711 : subd9_3 [4, -3, 9] = true := by decide +kernel
theorem subd9_3_1712 : subd9_3 [4, -2, -8] = true := by decide +kernel
theorem subd9_3_1713 : subd9_3 [4, -2, -7] = true := by decide +kernel
theorem subd9_3_1714 : subd9_3 [4, -2, -6] = true := by decide +kernel
theorem subd9_3_1715 : subd9_3 [4, -2, -5] = true := by decide +kernel
theorem subd9_3_1716 : subd9_3 [4, -2, -4] = true := by decide +kernel
theorem subd9_3_1717 : subd9_3 [4, -2, -3] = true := by decide +kernel
theorem subd9_3_1718 : subd9_3 [4, -2, -2] = true := by decide +kernel
theorem subd9_3_1719 : subd9_3 [4, -2, -1] = true := by decide +kernel
theorem subd9_3_1720 : subd9_3 [4, -2, 0] = true := by decide +kernel
theorem subd9_3_1721 : subd9_3 [4, -2, 1] = true := by decide +kernel
theorem subd9_3_1722 : subd9_3 [4, -2, 2] = true := by decide +kernel
theorem subd9_3_1723 : subd9_3 [4, -2, 3] = true := by decide +kernel
theorem subd9_3_1724 : subd9_3 [4, -2, 4] = true := by decide +kernel
theorem subd9_3_1725 : subd9_3 [4, -2, 5] = true := by decide +kernel
theorem subd9_3_1726 : subd9_3 [4, -2, 6] = true := by decide +kernel
theorem subd9_3_1727 : subd9_3 [4, -2, 7] = true := by decide +kernel
theorem sbd9_3_53 : ∀ q ∈ blkd9_3_53, subd9_3 q = true := by
  unfold blkd9_3_53
  exact List.forall_mem_cons.2 ⟨subd9_3_1696, List.forall_mem_cons.2 ⟨subd9_3_1697, List.forall_mem_cons.2 ⟨subd9_3_1698, List.forall_mem_cons.2 ⟨subd9_3_1699, List.forall_mem_cons.2 ⟨subd9_3_1700, List.forall_mem_cons.2 ⟨subd9_3_1701, List.forall_mem_cons.2 ⟨subd9_3_1702, List.forall_mem_cons.2 ⟨subd9_3_1703, List.forall_mem_cons.2 ⟨subd9_3_1704, List.forall_mem_cons.2 ⟨subd9_3_1705, List.forall_mem_cons.2 ⟨subd9_3_1706, List.forall_mem_cons.2 ⟨subd9_3_1707, List.forall_mem_cons.2 ⟨subd9_3_1708, List.forall_mem_cons.2 ⟨subd9_3_1709, List.forall_mem_cons.2 ⟨subd9_3_1710, List.forall_mem_cons.2 ⟨subd9_3_1711, List.forall_mem_cons.2 ⟨subd9_3_1712, List.forall_mem_cons.2 ⟨subd9_3_1713, List.forall_mem_cons.2 ⟨subd9_3_1714, List.forall_mem_cons.2 ⟨subd9_3_1715, List.forall_mem_cons.2 ⟨subd9_3_1716, List.forall_mem_cons.2 ⟨subd9_3_1717, List.forall_mem_cons.2 ⟨subd9_3_1718, List.forall_mem_cons.2 ⟨subd9_3_1719, List.forall_mem_cons.2 ⟨subd9_3_1720, List.forall_mem_cons.2 ⟨subd9_3_1721, List.forall_mem_cons.2 ⟨subd9_3_1722, List.forall_mem_cons.2 ⟨subd9_3_1723, List.forall_mem_cons.2 ⟨subd9_3_1724, List.forall_mem_cons.2 ⟨subd9_3_1725, List.forall_mem_cons.2 ⟨subd9_3_1726, List.forall_mem_cons.2 ⟨subd9_3_1727, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_1728 : subd9_3 [4, -2, 8] = true := by decide +kernel
theorem subd9_3_1729 : subd9_3 [4, -2, 9] = true := by decide +kernel
theorem subd9_3_1730 : subd9_3 [4, -2, 10] = true := by decide +kernel
theorem subd9_3_1731 : subd9_3 [4, -1, -8] = true := by decide +kernel
theorem subd9_3_1732 : subd9_3 [4, -1, -7] = true := by decide +kernel
theorem subd9_3_1733 : subd9_3 [4, -1, -6] = true := by decide +kernel
theorem subd9_3_1734 : subd9_3 [4, -1, -5] = true := by decide +kernel
theorem subd9_3_1735 : subd9_3 [4, -1, -4] = true := by decide +kernel
theorem subd9_3_1736 : subd9_3 [4, -1, -3] = true := by decide +kernel
theorem subd9_3_1737 : subd9_3 [4, -1, -2] = true := by decide +kernel
theorem subd9_3_1738 : subd9_3 [4, -1, -1] = true := by decide +kernel
theorem subd9_3_1739 : subd9_3 [4, -1, 0] = true := by decide +kernel
theorem subd9_3_1740 : subd9_3 [4, -1, 1] = true := by decide +kernel
theorem subd9_3_1741 : subd9_3 [4, -1, 2] = true := by decide +kernel
theorem subd9_3_1742 : subd9_3 [4, -1, 3] = true := by decide +kernel
theorem subd9_3_1743 : subd9_3 [4, -1, 4] = true := by decide +kernel
theorem subd9_3_1744 : subd9_3 [4, -1, 5] = true := by decide +kernel
theorem subd9_3_1745 : subd9_3 [4, -1, 6] = true := by decide +kernel
theorem subd9_3_1746 : subd9_3 [4, -1, 7] = true := by decide +kernel
theorem subd9_3_1747 : subd9_3 [4, -1, 8] = true := by decide +kernel
theorem subd9_3_1748 : subd9_3 [4, -1, 9] = true := by decide +kernel
theorem subd9_3_1749 : subd9_3 [4, -1, 10] = true := by decide +kernel
theorem subd9_3_1750 : subd9_3 [4, -1, 11] = true := by decide +kernel
theorem subd9_3_1751 : subd9_3 [4, 0, -8] = true := by decide +kernel
theorem subd9_3_1752 : subd9_3 [4, 0, -7] = true := by decide +kernel
theorem subd9_3_1753 : subd9_3 [4, 0, -6] = true := by decide +kernel
theorem subd9_3_1754 : subd9_3 [4, 0, -5] = true := by decide +kernel
theorem subd9_3_1755 : subd9_3 [4, 0, -4] = true := by decide +kernel
theorem subd9_3_1756 : subd9_3 [4, 0, -3] = true := by decide +kernel
theorem subd9_3_1757 : subd9_3 [4, 0, -2] = true := by decide +kernel
theorem subd9_3_1758 : subd9_3 [4, 0, -1] = true := by decide +kernel
theorem subd9_3_1759 : subd9_3 [4, 0, 0] = true := by decide +kernel
theorem sbd9_3_54 : ∀ q ∈ blkd9_3_54, subd9_3 q = true := by
  unfold blkd9_3_54
  exact List.forall_mem_cons.2 ⟨subd9_3_1728, List.forall_mem_cons.2 ⟨subd9_3_1729, List.forall_mem_cons.2 ⟨subd9_3_1730, List.forall_mem_cons.2 ⟨subd9_3_1731, List.forall_mem_cons.2 ⟨subd9_3_1732, List.forall_mem_cons.2 ⟨subd9_3_1733, List.forall_mem_cons.2 ⟨subd9_3_1734, List.forall_mem_cons.2 ⟨subd9_3_1735, List.forall_mem_cons.2 ⟨subd9_3_1736, List.forall_mem_cons.2 ⟨subd9_3_1737, List.forall_mem_cons.2 ⟨subd9_3_1738, List.forall_mem_cons.2 ⟨subd9_3_1739, List.forall_mem_cons.2 ⟨subd9_3_1740, List.forall_mem_cons.2 ⟨subd9_3_1741, List.forall_mem_cons.2 ⟨subd9_3_1742, List.forall_mem_cons.2 ⟨subd9_3_1743, List.forall_mem_cons.2 ⟨subd9_3_1744, List.forall_mem_cons.2 ⟨subd9_3_1745, List.forall_mem_cons.2 ⟨subd9_3_1746, List.forall_mem_cons.2 ⟨subd9_3_1747, List.forall_mem_cons.2 ⟨subd9_3_1748, List.forall_mem_cons.2 ⟨subd9_3_1749, List.forall_mem_cons.2 ⟨subd9_3_1750, List.forall_mem_cons.2 ⟨subd9_3_1751, List.forall_mem_cons.2 ⟨subd9_3_1752, List.forall_mem_cons.2 ⟨subd9_3_1753, List.forall_mem_cons.2 ⟨subd9_3_1754, List.forall_mem_cons.2 ⟨subd9_3_1755, List.forall_mem_cons.2 ⟨subd9_3_1756, List.forall_mem_cons.2 ⟨subd9_3_1757, List.forall_mem_cons.2 ⟨subd9_3_1758, List.forall_mem_cons.2 ⟨subd9_3_1759, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_1760 : subd9_3 [4, 0, 1] = true := by decide +kernel
theorem subd9_3_1761 : subd9_3 [4, 0, 2] = true := by decide +kernel
theorem subd9_3_1762 : subd9_3 [4, 0, 3] = true := by decide +kernel
theorem subd9_3_1763 : subd9_3 [4, 0, 4] = true := by decide +kernel
theorem subd9_3_1764 : subd9_3 [4, 0, 5] = true := by decide +kernel
theorem subd9_3_1765 : subd9_3 [4, 0, 6] = true := by decide +kernel
theorem subd9_3_1766 : subd9_3 [4, 0, 7] = true := by decide +kernel
theorem subd9_3_1767 : subd9_3 [4, 0, 8] = true := by decide +kernel
theorem subd9_3_1768 : subd9_3 [4, 0, 9] = true := by decide +kernel
theorem subd9_3_1769 : subd9_3 [4, 0, 10] = true := by decide +kernel
theorem subd9_3_1770 : subd9_3 [4, 0, 11] = true := by decide +kernel
theorem subd9_3_1771 : subd9_3 [4, 1, -8] = true := by decide +kernel
theorem subd9_3_1772 : subd9_3 [4, 1, -7] = true := by decide +kernel
theorem subd9_3_1773 : subd9_3 [4, 1, -6] = true := by decide +kernel
theorem subd9_3_1774 : subd9_3 [4, 1, -5] = true := by decide +kernel
theorem subd9_3_1775 : subd9_3 [4, 1, -4] = true := by decide +kernel
theorem subd9_3_1776 : subd9_3 [4, 1, -3] = true := by decide +kernel
theorem subd9_3_1777 : subd9_3 [4, 1, -2] = true := by decide +kernel
theorem subd9_3_1778 : subd9_3 [4, 1, -1] = true := by decide +kernel
theorem subd9_3_1779 : subd9_3 [4, 1, 0] = true := by decide +kernel
theorem subd9_3_1780 : subd9_3 [4, 1, 1] = true := by decide +kernel
theorem subd9_3_1781 : subd9_3 [4, 1, 2] = true := by decide +kernel
theorem subd9_3_1782 : subd9_3 [4, 1, 3] = true := by decide +kernel
theorem subd9_3_1783 : subd9_3 [4, 1, 4] = true := by decide +kernel
theorem subd9_3_1784 : subd9_3 [4, 1, 5] = true := by decide +kernel
theorem subd9_3_1785 : subd9_3 [4, 1, 6] = true := by decide +kernel
theorem subd9_3_1786 : subd9_3 [4, 1, 7] = true := by decide +kernel
theorem subd9_3_1787 : subd9_3 [4, 1, 8] = true := by decide +kernel
theorem subd9_3_1788 : subd9_3 [4, 1, 9] = true := by decide +kernel
theorem subd9_3_1789 : subd9_3 [4, 1, 10] = true := by decide +kernel
theorem subd9_3_1790 : subd9_3 [4, 1, 11] = true := by decide +kernel
theorem subd9_3_1791 : subd9_3 [4, 2, -7] = true := by decide +kernel
theorem sbd9_3_55 : ∀ q ∈ blkd9_3_55, subd9_3 q = true := by
  unfold blkd9_3_55
  exact List.forall_mem_cons.2 ⟨subd9_3_1760, List.forall_mem_cons.2 ⟨subd9_3_1761, List.forall_mem_cons.2 ⟨subd9_3_1762, List.forall_mem_cons.2 ⟨subd9_3_1763, List.forall_mem_cons.2 ⟨subd9_3_1764, List.forall_mem_cons.2 ⟨subd9_3_1765, List.forall_mem_cons.2 ⟨subd9_3_1766, List.forall_mem_cons.2 ⟨subd9_3_1767, List.forall_mem_cons.2 ⟨subd9_3_1768, List.forall_mem_cons.2 ⟨subd9_3_1769, List.forall_mem_cons.2 ⟨subd9_3_1770, List.forall_mem_cons.2 ⟨subd9_3_1771, List.forall_mem_cons.2 ⟨subd9_3_1772, List.forall_mem_cons.2 ⟨subd9_3_1773, List.forall_mem_cons.2 ⟨subd9_3_1774, List.forall_mem_cons.2 ⟨subd9_3_1775, List.forall_mem_cons.2 ⟨subd9_3_1776, List.forall_mem_cons.2 ⟨subd9_3_1777, List.forall_mem_cons.2 ⟨subd9_3_1778, List.forall_mem_cons.2 ⟨subd9_3_1779, List.forall_mem_cons.2 ⟨subd9_3_1780, List.forall_mem_cons.2 ⟨subd9_3_1781, List.forall_mem_cons.2 ⟨subd9_3_1782, List.forall_mem_cons.2 ⟨subd9_3_1783, List.forall_mem_cons.2 ⟨subd9_3_1784, List.forall_mem_cons.2 ⟨subd9_3_1785, List.forall_mem_cons.2 ⟨subd9_3_1786, List.forall_mem_cons.2 ⟨subd9_3_1787, List.forall_mem_cons.2 ⟨subd9_3_1788, List.forall_mem_cons.2 ⟨subd9_3_1789, List.forall_mem_cons.2 ⟨subd9_3_1790, List.forall_mem_cons.2 ⟨subd9_3_1791, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_1792 : subd9_3 [4, 2, -6] = true := by decide +kernel
theorem subd9_3_1793 : subd9_3 [4, 2, -5] = true := by decide +kernel
theorem subd9_3_1794 : subd9_3 [4, 2, -4] = true := by decide +kernel
theorem subd9_3_1795 : subd9_3 [4, 2, -3] = true := by decide +kernel
theorem subd9_3_1796 : subd9_3 [4, 2, -2] = true := by decide +kernel
theorem subd9_3_1797 : subd9_3 [4, 2, -1] = true := by decide +kernel
theorem subd9_3_1798 : subd9_3 [4, 2, 0] = true := by decide +kernel
theorem subd9_3_1799 : subd9_3 [4, 2, 1] = true := by decide +kernel
theorem subd9_3_1800 : subd9_3 [4, 2, 2] = true := by decide +kernel
theorem subd9_3_1801 : subd9_3 [4, 2, 3] = true := by decide +kernel
theorem subd9_3_1802 : subd9_3 [4, 2, 4] = true := by decide +kernel
theorem subd9_3_1803 : subd9_3 [4, 2, 5] = true := by decide +kernel
theorem subd9_3_1804 : subd9_3 [4, 2, 6] = true := by decide +kernel
theorem subd9_3_1805 : subd9_3 [4, 2, 7] = true := by decide +kernel
theorem subd9_3_1806 : subd9_3 [4, 2, 8] = true := by decide +kernel
theorem subd9_3_1807 : subd9_3 [4, 2, 9] = true := by decide +kernel
theorem subd9_3_1808 : subd9_3 [4, 2, 10] = true := by decide +kernel
theorem subd9_3_1809 : subd9_3 [4, 3, -6] = true := by decide +kernel
theorem subd9_3_1810 : subd9_3 [4, 3, -5] = true := by decide +kernel
theorem subd9_3_1811 : subd9_3 [4, 3, -4] = true := by decide +kernel
theorem subd9_3_1812 : subd9_3 [4, 3, -3] = true := by decide +kernel
theorem subd9_3_1813 : subd9_3 [4, 3, -2] = true := by decide +kernel
theorem subd9_3_1814 : subd9_3 [4, 3, -1] = true := by decide +kernel
theorem subd9_3_1815 : subd9_3 [4, 3, 0] = true := by decide +kernel
theorem subd9_3_1816 : subd9_3 [4, 3, 1] = true := by decide +kernel
theorem subd9_3_1817 : subd9_3 [4, 3, 2] = true := by decide +kernel
theorem subd9_3_1818 : subd9_3 [4, 3, 3] = true := by decide +kernel
theorem subd9_3_1819 : subd9_3 [4, 3, 4] = true := by decide +kernel
theorem subd9_3_1820 : subd9_3 [4, 3, 5] = true := by decide +kernel
theorem subd9_3_1821 : subd9_3 [4, 3, 6] = true := by decide +kernel
theorem subd9_3_1822 : subd9_3 [4, 3, 7] = true := by decide +kernel
theorem subd9_3_1823 : subd9_3 [4, 3, 8] = true := by decide +kernel
theorem sbd9_3_56 : ∀ q ∈ blkd9_3_56, subd9_3 q = true := by
  unfold blkd9_3_56
  exact List.forall_mem_cons.2 ⟨subd9_3_1792, List.forall_mem_cons.2 ⟨subd9_3_1793, List.forall_mem_cons.2 ⟨subd9_3_1794, List.forall_mem_cons.2 ⟨subd9_3_1795, List.forall_mem_cons.2 ⟨subd9_3_1796, List.forall_mem_cons.2 ⟨subd9_3_1797, List.forall_mem_cons.2 ⟨subd9_3_1798, List.forall_mem_cons.2 ⟨subd9_3_1799, List.forall_mem_cons.2 ⟨subd9_3_1800, List.forall_mem_cons.2 ⟨subd9_3_1801, List.forall_mem_cons.2 ⟨subd9_3_1802, List.forall_mem_cons.2 ⟨subd9_3_1803, List.forall_mem_cons.2 ⟨subd9_3_1804, List.forall_mem_cons.2 ⟨subd9_3_1805, List.forall_mem_cons.2 ⟨subd9_3_1806, List.forall_mem_cons.2 ⟨subd9_3_1807, List.forall_mem_cons.2 ⟨subd9_3_1808, List.forall_mem_cons.2 ⟨subd9_3_1809, List.forall_mem_cons.2 ⟨subd9_3_1810, List.forall_mem_cons.2 ⟨subd9_3_1811, List.forall_mem_cons.2 ⟨subd9_3_1812, List.forall_mem_cons.2 ⟨subd9_3_1813, List.forall_mem_cons.2 ⟨subd9_3_1814, List.forall_mem_cons.2 ⟨subd9_3_1815, List.forall_mem_cons.2 ⟨subd9_3_1816, List.forall_mem_cons.2 ⟨subd9_3_1817, List.forall_mem_cons.2 ⟨subd9_3_1818, List.forall_mem_cons.2 ⟨subd9_3_1819, List.forall_mem_cons.2 ⟨subd9_3_1820, List.forall_mem_cons.2 ⟨subd9_3_1821, List.forall_mem_cons.2 ⟨subd9_3_1822, List.forall_mem_cons.2 ⟨subd9_3_1823, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_1824 : subd9_3 [4, 3, 9] = true := by decide +kernel
theorem subd9_3_1825 : subd9_3 [4, 4] = true := by decide +kernel
theorem subd9_3_1826 : subd9_3 [5, -5] = true := by decide +kernel
theorem subd9_3_1827 : subd9_3 [5, -4] = true := by decide +kernel
theorem subd9_3_1828 : subd9_3 [5, -3] = true := by decide +kernel
theorem subd9_3_1829 : subd9_3 [5, -2, -5] = true := by decide +kernel
theorem subd9_3_1830 : subd9_3 [5, -2, -4] = true := by decide +kernel
theorem subd9_3_1831 : subd9_3 [5, -2, -3] = true := by decide +kernel
theorem subd9_3_1832 : subd9_3 [5, -2, -2] = true := by decide +kernel
theorem subd9_3_1833 : subd9_3 [5, -2, -1] = true := by decide +kernel
theorem subd9_3_1834 : subd9_3 [5, -2, 0] = true := by decide +kernel
theorem subd9_3_1835 : subd9_3 [5, -2, 1] = true := by decide +kernel
theorem subd9_3_1836 : subd9_3 [5, -2, 2] = true := by decide +kernel
theorem subd9_3_1837 : subd9_3 [5, -2, 3] = true := by decide +kernel
theorem subd9_3_1838 : subd9_3 [5, -2, 4] = true := by decide +kernel
theorem subd9_3_1839 : subd9_3 [5, -2, 5] = true := by decide +kernel
theorem subd9_3_1840 : subd9_3 [5, -2, 6] = true := by decide +kernel
theorem subd9_3_1841 : subd9_3 [5, -2, 7] = true := by decide +kernel
theorem subd9_3_1842 : subd9_3 [5, -2, 8] = true := by decide +kernel
theorem subd9_3_1843 : subd9_3 [5, -1, -6] = true := by decide +kernel
theorem subd9_3_1844 : subd9_3 [5, -1, -5] = true := by decide +kernel
theorem subd9_3_1845 : subd9_3 [5, -1, -4] = true := by decide +kernel
theorem subd9_3_1846 : subd9_3 [5, -1, -3] = true := by decide +kernel
theorem subd9_3_1847 : subd9_3 [5, -1, -2] = true := by decide +kernel
theorem subd9_3_1848 : subd9_3 [5, -1, -1] = true := by decide +kernel
theorem subd9_3_1849 : subd9_3 [5, -1, 0] = true := by decide +kernel
theorem subd9_3_1850 : subd9_3 [5, -1, 1] = true := by decide +kernel
theorem subd9_3_1851 : subd9_3 [5, -1, 2] = true := by decide +kernel
theorem subd9_3_1852 : subd9_3 [5, -1, 3] = true := by decide +kernel
theorem subd9_3_1853 : subd9_3 [5, -1, 4] = true := by decide +kernel
theorem subd9_3_1854 : subd9_3 [5, -1, 5] = true := by decide +kernel
theorem subd9_3_1855 : subd9_3 [5, -1, 6] = true := by decide +kernel
theorem sbd9_3_57 : ∀ q ∈ blkd9_3_57, subd9_3 q = true := by
  unfold blkd9_3_57
  exact List.forall_mem_cons.2 ⟨subd9_3_1824, List.forall_mem_cons.2 ⟨subd9_3_1825, List.forall_mem_cons.2 ⟨subd9_3_1826, List.forall_mem_cons.2 ⟨subd9_3_1827, List.forall_mem_cons.2 ⟨subd9_3_1828, List.forall_mem_cons.2 ⟨subd9_3_1829, List.forall_mem_cons.2 ⟨subd9_3_1830, List.forall_mem_cons.2 ⟨subd9_3_1831, List.forall_mem_cons.2 ⟨subd9_3_1832, List.forall_mem_cons.2 ⟨subd9_3_1833, List.forall_mem_cons.2 ⟨subd9_3_1834, List.forall_mem_cons.2 ⟨subd9_3_1835, List.forall_mem_cons.2 ⟨subd9_3_1836, List.forall_mem_cons.2 ⟨subd9_3_1837, List.forall_mem_cons.2 ⟨subd9_3_1838, List.forall_mem_cons.2 ⟨subd9_3_1839, List.forall_mem_cons.2 ⟨subd9_3_1840, List.forall_mem_cons.2 ⟨subd9_3_1841, List.forall_mem_cons.2 ⟨subd9_3_1842, List.forall_mem_cons.2 ⟨subd9_3_1843, List.forall_mem_cons.2 ⟨subd9_3_1844, List.forall_mem_cons.2 ⟨subd9_3_1845, List.forall_mem_cons.2 ⟨subd9_3_1846, List.forall_mem_cons.2 ⟨subd9_3_1847, List.forall_mem_cons.2 ⟨subd9_3_1848, List.forall_mem_cons.2 ⟨subd9_3_1849, List.forall_mem_cons.2 ⟨subd9_3_1850, List.forall_mem_cons.2 ⟨subd9_3_1851, List.forall_mem_cons.2 ⟨subd9_3_1852, List.forall_mem_cons.2 ⟨subd9_3_1853, List.forall_mem_cons.2 ⟨subd9_3_1854, List.forall_mem_cons.2 ⟨subd9_3_1855, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_1856 : subd9_3 [5, -1, 7] = true := by decide +kernel
theorem subd9_3_1857 : subd9_3 [5, -1, 8] = true := by decide +kernel
theorem subd9_3_1858 : subd9_3 [5, -1, 9] = true := by decide +kernel
theorem subd9_3_1859 : subd9_3 [5, 0, -6] = true := by decide +kernel
theorem subd9_3_1860 : subd9_3 [5, 0, -5] = true := by decide +kernel
theorem subd9_3_1861 : subd9_3 [5, 0, -4] = true := by decide +kernel
theorem subd9_3_1862 : subd9_3 [5, 0, -3] = true := by decide +kernel
theorem subd9_3_1863 : subd9_3 [5, 0, -2] = true := by decide +kernel
theorem subd9_3_1864 : subd9_3 [5, 0, -1] = true := by decide +kernel
theorem subd9_3_1865 : subd9_3 [5, 0, 0] = true := by decide +kernel
theorem subd9_3_1866 : subd9_3 [5, 0, 1] = true := by decide +kernel
theorem subd9_3_1867 : subd9_3 [5, 0, 2] = true := by decide +kernel
theorem subd9_3_1868 : subd9_3 [5, 0, 3] = true := by decide +kernel
theorem subd9_3_1869 : subd9_3 [5, 0, 4] = true := by decide +kernel
theorem subd9_3_1870 : subd9_3 [5, 0, 5] = true := by decide +kernel
theorem subd9_3_1871 : subd9_3 [5, 0, 6] = true := by decide +kernel
theorem subd9_3_1872 : subd9_3 [5, 0, 7] = true := by decide +kernel
theorem subd9_3_1873 : subd9_3 [5, 0, 8] = true := by decide +kernel
theorem subd9_3_1874 : subd9_3 [5, 0, 9] = true := by decide +kernel
theorem subd9_3_1875 : subd9_3 [5, 1, -6] = true := by decide +kernel
theorem subd9_3_1876 : subd9_3 [5, 1, -5] = true := by decide +kernel
theorem subd9_3_1877 : subd9_3 [5, 1, -4] = true := by decide +kernel
theorem subd9_3_1878 : subd9_3 [5, 1, -3] = true := by decide +kernel
theorem subd9_3_1879 : subd9_3 [5, 1, -2] = true := by decide +kernel
theorem subd9_3_1880 : subd9_3 [5, 1, -1] = true := by decide +kernel
theorem subd9_3_1881 : subd9_3 [5, 1, 0] = true := by decide +kernel
theorem subd9_3_1882 : subd9_3 [5, 1, 1] = true := by decide +kernel
theorem subd9_3_1883 : subd9_3 [5, 1, 2] = true := by decide +kernel
theorem subd9_3_1884 : subd9_3 [5, 1, 3] = true := by decide +kernel
theorem subd9_3_1885 : subd9_3 [5, 1, 4] = true := by decide +kernel
theorem subd9_3_1886 : subd9_3 [5, 1, 5] = true := by decide +kernel
theorem subd9_3_1887 : subd9_3 [5, 1, 6] = true := by decide +kernel
theorem sbd9_3_58 : ∀ q ∈ blkd9_3_58, subd9_3 q = true := by
  unfold blkd9_3_58
  exact List.forall_mem_cons.2 ⟨subd9_3_1856, List.forall_mem_cons.2 ⟨subd9_3_1857, List.forall_mem_cons.2 ⟨subd9_3_1858, List.forall_mem_cons.2 ⟨subd9_3_1859, List.forall_mem_cons.2 ⟨subd9_3_1860, List.forall_mem_cons.2 ⟨subd9_3_1861, List.forall_mem_cons.2 ⟨subd9_3_1862, List.forall_mem_cons.2 ⟨subd9_3_1863, List.forall_mem_cons.2 ⟨subd9_3_1864, List.forall_mem_cons.2 ⟨subd9_3_1865, List.forall_mem_cons.2 ⟨subd9_3_1866, List.forall_mem_cons.2 ⟨subd9_3_1867, List.forall_mem_cons.2 ⟨subd9_3_1868, List.forall_mem_cons.2 ⟨subd9_3_1869, List.forall_mem_cons.2 ⟨subd9_3_1870, List.forall_mem_cons.2 ⟨subd9_3_1871, List.forall_mem_cons.2 ⟨subd9_3_1872, List.forall_mem_cons.2 ⟨subd9_3_1873, List.forall_mem_cons.2 ⟨subd9_3_1874, List.forall_mem_cons.2 ⟨subd9_3_1875, List.forall_mem_cons.2 ⟨subd9_3_1876, List.forall_mem_cons.2 ⟨subd9_3_1877, List.forall_mem_cons.2 ⟨subd9_3_1878, List.forall_mem_cons.2 ⟨subd9_3_1879, List.forall_mem_cons.2 ⟨subd9_3_1880, List.forall_mem_cons.2 ⟨subd9_3_1881, List.forall_mem_cons.2 ⟨subd9_3_1882, List.forall_mem_cons.2 ⟨subd9_3_1883, List.forall_mem_cons.2 ⟨subd9_3_1884, List.forall_mem_cons.2 ⟨subd9_3_1885, List.forall_mem_cons.2 ⟨subd9_3_1886, List.forall_mem_cons.2 ⟨subd9_3_1887, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_1888 : subd9_3 [5, 1, 7] = true := by decide +kernel
theorem subd9_3_1889 : subd9_3 [5, 1, 8] = true := by decide +kernel
theorem subd9_3_1890 : subd9_3 [5, 1, 9] = true := by decide +kernel
theorem subd9_3_1891 : subd9_3 [5, 2] = true := by decide +kernel
theorem subd9_3_1892 : subd9_3 [5, 3] = true := by decide +kernel
theorem subd9_3_1893 : subd9_3 [6, -3] = true := by decide +kernel
theorem subd9_3_1894 : subd9_3 [6, -2] = true := by decide +kernel
theorem subd9_3_1895 : subd9_3 [6, -1] = true := by decide +kernel
theorem subd9_3_1896 : subd9_3 [6, 0] = true := by decide +kernel
theorem subd9_3_1897 : subd9_3 [6, 1] = true := by decide +kernel
theorem subd9_3_1898 : subd9_3 [6, 2] = true := by decide +kernel
theorem sbd9_3_59 : ∀ q ∈ blkd9_3_59, subd9_3 q = true := by
  unfold blkd9_3_59
  exact List.forall_mem_cons.2 ⟨subd9_3_1888, List.forall_mem_cons.2 ⟨subd9_3_1889, List.forall_mem_cons.2 ⟨subd9_3_1890, List.forall_mem_cons.2 ⟨subd9_3_1891, List.forall_mem_cons.2 ⟨subd9_3_1892, List.forall_mem_cons.2 ⟨subd9_3_1893, List.forall_mem_cons.2 ⟨subd9_3_1894, List.forall_mem_cons.2 ⟨subd9_3_1895, List.forall_mem_cons.2 ⟨subd9_3_1896, List.forall_mem_cons.2 ⟨subd9_3_1897, List.forall_mem_cons.2 ⟨subd9_3_1898, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_4 : ldCheck G d9_4.U d9_4.ms ldd9_4 = true := by decide +kernel
theorem pre_okd9_4 : subPre G cell9 d9_4 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C135
