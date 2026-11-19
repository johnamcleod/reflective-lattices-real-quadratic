import ReflectZphi.Data.Cert5.C131.Base

namespace ReflectZphi.Data.Cert5.C131

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd11_0_1568 : subd11_0 [2, 1, 4] = true := by decide +kernel
theorem subd11_0_1569 : subd11_0 [2, 1, 5] = true := by decide +kernel
theorem subd11_0_1570 : subd11_0 [2, 1, 6] = true := by decide +kernel
theorem subd11_0_1571 : subd11_0 [2, 1, 7] = true := by decide +kernel
theorem subd11_0_1572 : subd11_0 [2, 1, 8] = true := by decide +kernel
theorem subd11_0_1573 : subd11_0 [2, 2, -9] = true := by decide +kernel
theorem subd11_0_1574 : subd11_0 [2, 2, -8] = true := by decide +kernel
theorem subd11_0_1575 : subd11_0 [2, 2, -7] = true := by decide +kernel
theorem subd11_0_1576 : subd11_0 [2, 2, -6] = true := by decide +kernel
theorem subd11_0_1577 : subd11_0 [2, 2, -5] = true := by decide +kernel
theorem subd11_0_1578 : subd11_0 [2, 2, -4] = true := by decide +kernel
theorem subd11_0_1579 : subd11_0 [2, 2, -3] = true := by decide +kernel
theorem subd11_0_1580 : subd11_0 [2, 2, -2] = true := by decide +kernel
theorem subd11_0_1581 : subd11_0 [2, 2, -1] = true := by decide +kernel
theorem subd11_0_1582 : subd11_0 [2, 2, 0] = true := by decide +kernel
theorem subd11_0_1583 : subd11_0 [2, 2, 1] = true := by decide +kernel
theorem subd11_0_1584 : subd11_0 [2, 2, 2] = true := by decide +kernel
theorem subd11_0_1585 : subd11_0 [2, 2, 3] = true := by decide +kernel
theorem subd11_0_1586 : subd11_0 [2, 2, 4] = true := by decide +kernel
theorem subd11_0_1587 : subd11_0 [2, 2, 5] = true := by decide +kernel
theorem subd11_0_1588 : subd11_0 [2, 2, 6] = true := by decide +kernel
theorem subd11_0_1589 : subd11_0 [2, 2, 7] = true := by decide +kernel
theorem subd11_0_1590 : subd11_0 [2, 2, 8] = true := by decide +kernel
theorem subd11_0_1591 : subd11_0 [2, 3, -8] = true := by decide +kernel
theorem subd11_0_1592 : subd11_0 [2, 3, -7] = true := by decide +kernel
theorem subd11_0_1593 : subd11_0 [2, 3, -6] = true := by decide +kernel
theorem subd11_0_1594 : subd11_0 [2, 3, -5] = true := by decide +kernel
theorem subd11_0_1595 : subd11_0 [2, 3, -4] = true := by decide +kernel
theorem subd11_0_1596 : subd11_0 [2, 3, -3] = true := by decide +kernel
theorem subd11_0_1597 : subd11_0 [2, 3, -2] = true := by decide +kernel
theorem subd11_0_1598 : subd11_0 [2, 3, -1] = true := by decide +kernel
theorem subd11_0_1599 : subd11_0 [2, 3, 0] = true := by decide +kernel
theorem sbd11_0_49 : ∀ q ∈ blkd11_0_49, subd11_0 q = true := by
  unfold blkd11_0_49
  exact List.forall_mem_cons.2 ⟨subd11_0_1568, List.forall_mem_cons.2 ⟨subd11_0_1569, List.forall_mem_cons.2 ⟨subd11_0_1570, List.forall_mem_cons.2 ⟨subd11_0_1571, List.forall_mem_cons.2 ⟨subd11_0_1572, List.forall_mem_cons.2 ⟨subd11_0_1573, List.forall_mem_cons.2 ⟨subd11_0_1574, List.forall_mem_cons.2 ⟨subd11_0_1575, List.forall_mem_cons.2 ⟨subd11_0_1576, List.forall_mem_cons.2 ⟨subd11_0_1577, List.forall_mem_cons.2 ⟨subd11_0_1578, List.forall_mem_cons.2 ⟨subd11_0_1579, List.forall_mem_cons.2 ⟨subd11_0_1580, List.forall_mem_cons.2 ⟨subd11_0_1581, List.forall_mem_cons.2 ⟨subd11_0_1582, List.forall_mem_cons.2 ⟨subd11_0_1583, List.forall_mem_cons.2 ⟨subd11_0_1584, List.forall_mem_cons.2 ⟨subd11_0_1585, List.forall_mem_cons.2 ⟨subd11_0_1586, List.forall_mem_cons.2 ⟨subd11_0_1587, List.forall_mem_cons.2 ⟨subd11_0_1588, List.forall_mem_cons.2 ⟨subd11_0_1589, List.forall_mem_cons.2 ⟨subd11_0_1590, List.forall_mem_cons.2 ⟨subd11_0_1591, List.forall_mem_cons.2 ⟨subd11_0_1592, List.forall_mem_cons.2 ⟨subd11_0_1593, List.forall_mem_cons.2 ⟨subd11_0_1594, List.forall_mem_cons.2 ⟨subd11_0_1595, List.forall_mem_cons.2 ⟨subd11_0_1596, List.forall_mem_cons.2 ⟨subd11_0_1597, List.forall_mem_cons.2 ⟨subd11_0_1598, List.forall_mem_cons.2 ⟨subd11_0_1599, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_1600 : subd11_0 [2, 3, 1] = true := by decide +kernel
theorem subd11_0_1601 : subd11_0 [2, 3, 2] = true := by decide +kernel
theorem subd11_0_1602 : subd11_0 [2, 3, 3] = true := by decide +kernel
theorem subd11_0_1603 : subd11_0 [2, 3, 4] = true := by decide +kernel
theorem subd11_0_1604 : subd11_0 [2, 3, 5] = true := by decide +kernel
theorem subd11_0_1605 : subd11_0 [2, 3, 6] = true := by decide +kernel
theorem subd11_0_1606 : subd11_0 [2, 3, 7] = true := by decide +kernel
theorem subd11_0_1607 : subd11_0 [2, 3, 8] = true := by decide +kernel
theorem subd11_0_1608 : subd11_0 [2, 4, -8] = true := by decide +kernel
theorem subd11_0_1609 : subd11_0 [2, 4, -7] = true := by decide +kernel
theorem subd11_0_1610 : subd11_0 [2, 4, -6] = true := by decide +kernel
theorem subd11_0_1611 : subd11_0 [2, 4, -5] = true := by decide +kernel
theorem subd11_0_1612 : subd11_0 [2, 4, -4] = true := by decide +kernel
theorem subd11_0_1613 : subd11_0 [2, 4, -3] = true := by decide +kernel
theorem subd11_0_1614 : subd11_0 [2, 4, -2] = true := by decide +kernel
theorem subd11_0_1615 : subd11_0 [2, 4, -1] = true := by decide +kernel
theorem subd11_0_1616 : subd11_0 [2, 4, 0] = true := by decide +kernel
theorem subd11_0_1617 : subd11_0 [2, 4, 1] = true := by decide +kernel
theorem subd11_0_1618 : subd11_0 [2, 4, 2] = true := by decide +kernel
theorem subd11_0_1619 : subd11_0 [2, 4, 3] = true := by decide +kernel
theorem subd11_0_1620 : subd11_0 [2, 4, 4] = true := by decide +kernel
theorem subd11_0_1621 : subd11_0 [2, 4, 5] = true := by decide +kernel
theorem subd11_0_1622 : subd11_0 [2, 4, 6] = true := by decide +kernel
theorem subd11_0_1623 : subd11_0 [2, 4, 7] = true := by decide +kernel
theorem subd11_0_1624 : subd11_0 [2, 4, 8] = true := by decide +kernel
theorem subd11_0_1625 : subd11_0 [2, 5, -8] = true := by decide +kernel
theorem subd11_0_1626 : subd11_0 [2, 5, -7] = true := by decide +kernel
theorem subd11_0_1627 : subd11_0 [2, 5, -6] = true := by decide +kernel
theorem subd11_0_1628 : subd11_0 [2, 5, -5] = true := by decide +kernel
theorem subd11_0_1629 : subd11_0 [2, 5, -4] = true := by decide +kernel
theorem subd11_0_1630 : subd11_0 [2, 5, -3] = true := by decide +kernel
theorem subd11_0_1631 : subd11_0 [2, 5, -2] = true := by decide +kernel
theorem sbd11_0_50 : ∀ q ∈ blkd11_0_50, subd11_0 q = true := by
  unfold blkd11_0_50
  exact List.forall_mem_cons.2 ⟨subd11_0_1600, List.forall_mem_cons.2 ⟨subd11_0_1601, List.forall_mem_cons.2 ⟨subd11_0_1602, List.forall_mem_cons.2 ⟨subd11_0_1603, List.forall_mem_cons.2 ⟨subd11_0_1604, List.forall_mem_cons.2 ⟨subd11_0_1605, List.forall_mem_cons.2 ⟨subd11_0_1606, List.forall_mem_cons.2 ⟨subd11_0_1607, List.forall_mem_cons.2 ⟨subd11_0_1608, List.forall_mem_cons.2 ⟨subd11_0_1609, List.forall_mem_cons.2 ⟨subd11_0_1610, List.forall_mem_cons.2 ⟨subd11_0_1611, List.forall_mem_cons.2 ⟨subd11_0_1612, List.forall_mem_cons.2 ⟨subd11_0_1613, List.forall_mem_cons.2 ⟨subd11_0_1614, List.forall_mem_cons.2 ⟨subd11_0_1615, List.forall_mem_cons.2 ⟨subd11_0_1616, List.forall_mem_cons.2 ⟨subd11_0_1617, List.forall_mem_cons.2 ⟨subd11_0_1618, List.forall_mem_cons.2 ⟨subd11_0_1619, List.forall_mem_cons.2 ⟨subd11_0_1620, List.forall_mem_cons.2 ⟨subd11_0_1621, List.forall_mem_cons.2 ⟨subd11_0_1622, List.forall_mem_cons.2 ⟨subd11_0_1623, List.forall_mem_cons.2 ⟨subd11_0_1624, List.forall_mem_cons.2 ⟨subd11_0_1625, List.forall_mem_cons.2 ⟨subd11_0_1626, List.forall_mem_cons.2 ⟨subd11_0_1627, List.forall_mem_cons.2 ⟨subd11_0_1628, List.forall_mem_cons.2 ⟨subd11_0_1629, List.forall_mem_cons.2 ⟨subd11_0_1630, List.forall_mem_cons.2 ⟨subd11_0_1631, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_1632 : subd11_0 [2, 5, -1] = true := by decide +kernel
theorem subd11_0_1633 : subd11_0 [2, 5, 0] = true := by decide +kernel
theorem subd11_0_1634 : subd11_0 [2, 5, 1] = true := by decide +kernel
theorem subd11_0_1635 : subd11_0 [2, 5, 2] = true := by decide +kernel
theorem subd11_0_1636 : subd11_0 [2, 5, 3] = true := by decide +kernel
theorem subd11_0_1637 : subd11_0 [2, 5, 4] = true := by decide +kernel
theorem subd11_0_1638 : subd11_0 [2, 5, 5] = true := by decide +kernel
theorem subd11_0_1639 : subd11_0 [2, 5, 6] = true := by decide +kernel
theorem subd11_0_1640 : subd11_0 [2, 5, 7] = true := by decide +kernel
theorem subd11_0_1641 : subd11_0 [2, 6, -7] = true := by decide +kernel
theorem subd11_0_1642 : subd11_0 [2, 6, -6] = true := by decide +kernel
theorem subd11_0_1643 : subd11_0 [2, 6, -5] = true := by decide +kernel
theorem subd11_0_1644 : subd11_0 [2, 6, -4] = true := by decide +kernel
theorem subd11_0_1645 : subd11_0 [2, 6, -3] = true := by decide +kernel
theorem subd11_0_1646 : subd11_0 [2, 6, -2] = true := by decide +kernel
theorem subd11_0_1647 : subd11_0 [2, 6, -1] = true := by decide +kernel
theorem subd11_0_1648 : subd11_0 [2, 6, 0] = true := by decide +kernel
theorem subd11_0_1649 : subd11_0 [2, 6, 1] = true := by decide +kernel
theorem subd11_0_1650 : subd11_0 [2, 6, 2] = true := by decide +kernel
theorem subd11_0_1651 : subd11_0 [2, 6, 3] = true := by decide +kernel
theorem subd11_0_1652 : subd11_0 [2, 6, 4] = true := by decide +kernel
theorem subd11_0_1653 : subd11_0 [2, 6, 5] = true := by decide +kernel
theorem subd11_0_1654 : subd11_0 [2, 6, 6] = true := by decide +kernel
theorem subd11_0_1655 : subd11_0 [2, 6, 7] = true := by decide +kernel
theorem subd11_0_1656 : subd11_0 [2, 7, -7] = true := by decide +kernel
theorem subd11_0_1657 : subd11_0 [2, 7, -6] = true := by decide +kernel
theorem subd11_0_1658 : subd11_0 [2, 7, -5] = true := by decide +kernel
theorem subd11_0_1659 : subd11_0 [2, 7, -4] = true := by decide +kernel
theorem subd11_0_1660 : subd11_0 [2, 7, -3] = true := by decide +kernel
theorem subd11_0_1661 : subd11_0 [2, 7, -2] = true := by decide +kernel
theorem subd11_0_1662 : subd11_0 [2, 7, -1] = true := by decide +kernel
theorem subd11_0_1663 : subd11_0 [2, 7, 0] = true := by decide +kernel
theorem sbd11_0_51 : ∀ q ∈ blkd11_0_51, subd11_0 q = true := by
  unfold blkd11_0_51
  exact List.forall_mem_cons.2 ⟨subd11_0_1632, List.forall_mem_cons.2 ⟨subd11_0_1633, List.forall_mem_cons.2 ⟨subd11_0_1634, List.forall_mem_cons.2 ⟨subd11_0_1635, List.forall_mem_cons.2 ⟨subd11_0_1636, List.forall_mem_cons.2 ⟨subd11_0_1637, List.forall_mem_cons.2 ⟨subd11_0_1638, List.forall_mem_cons.2 ⟨subd11_0_1639, List.forall_mem_cons.2 ⟨subd11_0_1640, List.forall_mem_cons.2 ⟨subd11_0_1641, List.forall_mem_cons.2 ⟨subd11_0_1642, List.forall_mem_cons.2 ⟨subd11_0_1643, List.forall_mem_cons.2 ⟨subd11_0_1644, List.forall_mem_cons.2 ⟨subd11_0_1645, List.forall_mem_cons.2 ⟨subd11_0_1646, List.forall_mem_cons.2 ⟨subd11_0_1647, List.forall_mem_cons.2 ⟨subd11_0_1648, List.forall_mem_cons.2 ⟨subd11_0_1649, List.forall_mem_cons.2 ⟨subd11_0_1650, List.forall_mem_cons.2 ⟨subd11_0_1651, List.forall_mem_cons.2 ⟨subd11_0_1652, List.forall_mem_cons.2 ⟨subd11_0_1653, List.forall_mem_cons.2 ⟨subd11_0_1654, List.forall_mem_cons.2 ⟨subd11_0_1655, List.forall_mem_cons.2 ⟨subd11_0_1656, List.forall_mem_cons.2 ⟨subd11_0_1657, List.forall_mem_cons.2 ⟨subd11_0_1658, List.forall_mem_cons.2 ⟨subd11_0_1659, List.forall_mem_cons.2 ⟨subd11_0_1660, List.forall_mem_cons.2 ⟨subd11_0_1661, List.forall_mem_cons.2 ⟨subd11_0_1662, List.forall_mem_cons.2 ⟨subd11_0_1663, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_1664 : subd11_0 [2, 7, 1] = true := by decide +kernel
theorem subd11_0_1665 : subd11_0 [2, 7, 2] = true := by decide +kernel
theorem subd11_0_1666 : subd11_0 [2, 7, 3] = true := by decide +kernel
theorem subd11_0_1667 : subd11_0 [2, 7, 4] = true := by decide +kernel
theorem subd11_0_1668 : subd11_0 [2, 7, 5] = true := by decide +kernel
theorem subd11_0_1669 : subd11_0 [2, 7, 6] = true := by decide +kernel
theorem subd11_0_1670 : subd11_0 [2, 8] = true := by decide +kernel
theorem subd11_0_1671 : subd11_0 [2, 9] = true := by decide +kernel
theorem subd11_0_1672 : subd11_0 [2, 10] = true := by decide +kernel
theorem subd11_0_1673 : subd11_0 [3, -8] = true := by decide +kernel
theorem subd11_0_1674 : subd11_0 [3, -7] = true := by decide +kernel
theorem subd11_0_1675 : subd11_0 [3, -6] = true := by decide +kernel
theorem subd11_0_1676 : subd11_0 [3, -5] = true := by decide +kernel
theorem subd11_0_1677 : subd11_0 [3, -4, -6] = true := by decide +kernel
theorem subd11_0_1678 : subd11_0 [3, -4, -5] = true := by decide +kernel
theorem subd11_0_1679 : subd11_0 [3, -4, -4] = true := by decide +kernel
theorem subd11_0_1680 : subd11_0 [3, -4, -3] = true := by decide +kernel
theorem subd11_0_1681 : subd11_0 [3, -4, -2] = true := by decide +kernel
theorem subd11_0_1682 : subd11_0 [3, -4, -1] = true := by decide +kernel
theorem subd11_0_1683 : subd11_0 [3, -4, 0] = true := by decide +kernel
theorem subd11_0_1684 : subd11_0 [3, -4, 1] = true := by decide +kernel
theorem subd11_0_1685 : subd11_0 [3, -4, 2] = true := by decide +kernel
theorem subd11_0_1686 : subd11_0 [3, -4, 3] = true := by decide +kernel
theorem subd11_0_1687 : subd11_0 [3, -4, 4] = true := by decide +kernel
theorem subd11_0_1688 : subd11_0 [3, -4, 5] = true := by decide +kernel
theorem subd11_0_1689 : subd11_0 [3, -4, 6] = true := by decide +kernel
theorem subd11_0_1690 : subd11_0 [3, -4, 7] = true := by decide +kernel
theorem subd11_0_1691 : subd11_0 [3, -3, -7] = true := by decide +kernel
theorem subd11_0_1692 : subd11_0 [3, -3, -6] = true := by decide +kernel
theorem subd11_0_1693 : subd11_0 [3, -3, -5] = true := by decide +kernel
theorem subd11_0_1694 : subd11_0 [3, -3, -4] = true := by decide +kernel
theorem subd11_0_1695 : subd11_0 [3, -3, -3] = true := by decide +kernel
theorem sbd11_0_52 : ∀ q ∈ blkd11_0_52, subd11_0 q = true := by
  unfold blkd11_0_52
  exact List.forall_mem_cons.2 ⟨subd11_0_1664, List.forall_mem_cons.2 ⟨subd11_0_1665, List.forall_mem_cons.2 ⟨subd11_0_1666, List.forall_mem_cons.2 ⟨subd11_0_1667, List.forall_mem_cons.2 ⟨subd11_0_1668, List.forall_mem_cons.2 ⟨subd11_0_1669, List.forall_mem_cons.2 ⟨subd11_0_1670, List.forall_mem_cons.2 ⟨subd11_0_1671, List.forall_mem_cons.2 ⟨subd11_0_1672, List.forall_mem_cons.2 ⟨subd11_0_1673, List.forall_mem_cons.2 ⟨subd11_0_1674, List.forall_mem_cons.2 ⟨subd11_0_1675, List.forall_mem_cons.2 ⟨subd11_0_1676, List.forall_mem_cons.2 ⟨subd11_0_1677, List.forall_mem_cons.2 ⟨subd11_0_1678, List.forall_mem_cons.2 ⟨subd11_0_1679, List.forall_mem_cons.2 ⟨subd11_0_1680, List.forall_mem_cons.2 ⟨subd11_0_1681, List.forall_mem_cons.2 ⟨subd11_0_1682, List.forall_mem_cons.2 ⟨subd11_0_1683, List.forall_mem_cons.2 ⟨subd11_0_1684, List.forall_mem_cons.2 ⟨subd11_0_1685, List.forall_mem_cons.2 ⟨subd11_0_1686, List.forall_mem_cons.2 ⟨subd11_0_1687, List.forall_mem_cons.2 ⟨subd11_0_1688, List.forall_mem_cons.2 ⟨subd11_0_1689, List.forall_mem_cons.2 ⟨subd11_0_1690, List.forall_mem_cons.2 ⟨subd11_0_1691, List.forall_mem_cons.2 ⟨subd11_0_1692, List.forall_mem_cons.2 ⟨subd11_0_1693, List.forall_mem_cons.2 ⟨subd11_0_1694, List.forall_mem_cons.2 ⟨subd11_0_1695, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_1696 : subd11_0 [3, -3, -2] = true := by decide +kernel
theorem subd11_0_1697 : subd11_0 [3, -3, -1] = true := by decide +kernel
theorem subd11_0_1698 : subd11_0 [3, -3, 0] = true := by decide +kernel
theorem subd11_0_1699 : subd11_0 [3, -3, 1] = true := by decide +kernel
theorem subd11_0_1700 : subd11_0 [3, -3, 2] = true := by decide +kernel
theorem subd11_0_1701 : subd11_0 [3, -3, 3] = true := by decide +kernel
theorem subd11_0_1702 : subd11_0 [3, -3, 4] = true := by decide +kernel
theorem subd11_0_1703 : subd11_0 [3, -3, 5] = true := by decide +kernel
theorem subd11_0_1704 : subd11_0 [3, -3, 6] = true := by decide +kernel
theorem subd11_0_1705 : subd11_0 [3, -3, 7] = true := by decide +kernel
theorem subd11_0_1706 : subd11_0 [3, -3, 8] = true := by decide +kernel
theorem subd11_0_1707 : subd11_0 [3, -2, -7] = true := by decide +kernel
theorem subd11_0_1708 : subd11_0 [3, -2, -6] = true := by decide +kernel
theorem subd11_0_1709 : subd11_0 [3, -2, -5] = true := by decide +kernel
theorem subd11_0_1710 : subd11_0 [3, -2, -4] = true := by decide +kernel
theorem subd11_0_1711 : subd11_0 [3, -2, -3] = true := by decide +kernel
theorem subd11_0_1712 : subd11_0 [3, -2, -2] = true := by decide +kernel
theorem subd11_0_1713 : subd11_0 [3, -2, -1] = true := by decide +kernel
theorem subd11_0_1714 : subd11_0 [3, -2, 0] = true := by decide +kernel
theorem subd11_0_1715 : subd11_0 [3, -2, 1] = true := by decide +kernel
theorem subd11_0_1716 : subd11_0 [3, -2, 2] = true := by decide +kernel
theorem subd11_0_1717 : subd11_0 [3, -2, 3] = true := by decide +kernel
theorem subd11_0_1718 : subd11_0 [3, -2, 4] = true := by decide +kernel
theorem subd11_0_1719 : subd11_0 [3, -2, 5] = true := by decide +kernel
theorem subd11_0_1720 : subd11_0 [3, -2, 6] = true := by decide +kernel
theorem subd11_0_1721 : subd11_0 [3, -2, 7] = true := by decide +kernel
theorem subd11_0_1722 : subd11_0 [3, -2, 8] = true := by decide +kernel
theorem subd11_0_1723 : subd11_0 [3, -1, -8] = true := by decide +kernel
theorem subd11_0_1724 : subd11_0 [3, -1, -7] = true := by decide +kernel
theorem subd11_0_1725 : subd11_0 [3, -1, -6] = true := by decide +kernel
theorem subd11_0_1726 : subd11_0 [3, -1, -5] = true := by decide +kernel
theorem subd11_0_1727 : subd11_0 [3, -1, -4] = true := by decide +kernel
theorem sbd11_0_53 : ∀ q ∈ blkd11_0_53, subd11_0 q = true := by
  unfold blkd11_0_53
  exact List.forall_mem_cons.2 ⟨subd11_0_1696, List.forall_mem_cons.2 ⟨subd11_0_1697, List.forall_mem_cons.2 ⟨subd11_0_1698, List.forall_mem_cons.2 ⟨subd11_0_1699, List.forall_mem_cons.2 ⟨subd11_0_1700, List.forall_mem_cons.2 ⟨subd11_0_1701, List.forall_mem_cons.2 ⟨subd11_0_1702, List.forall_mem_cons.2 ⟨subd11_0_1703, List.forall_mem_cons.2 ⟨subd11_0_1704, List.forall_mem_cons.2 ⟨subd11_0_1705, List.forall_mem_cons.2 ⟨subd11_0_1706, List.forall_mem_cons.2 ⟨subd11_0_1707, List.forall_mem_cons.2 ⟨subd11_0_1708, List.forall_mem_cons.2 ⟨subd11_0_1709, List.forall_mem_cons.2 ⟨subd11_0_1710, List.forall_mem_cons.2 ⟨subd11_0_1711, List.forall_mem_cons.2 ⟨subd11_0_1712, List.forall_mem_cons.2 ⟨subd11_0_1713, List.forall_mem_cons.2 ⟨subd11_0_1714, List.forall_mem_cons.2 ⟨subd11_0_1715, List.forall_mem_cons.2 ⟨subd11_0_1716, List.forall_mem_cons.2 ⟨subd11_0_1717, List.forall_mem_cons.2 ⟨subd11_0_1718, List.forall_mem_cons.2 ⟨subd11_0_1719, List.forall_mem_cons.2 ⟨subd11_0_1720, List.forall_mem_cons.2 ⟨subd11_0_1721, List.forall_mem_cons.2 ⟨subd11_0_1722, List.forall_mem_cons.2 ⟨subd11_0_1723, List.forall_mem_cons.2 ⟨subd11_0_1724, List.forall_mem_cons.2 ⟨subd11_0_1725, List.forall_mem_cons.2 ⟨subd11_0_1726, List.forall_mem_cons.2 ⟨subd11_0_1727, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_1728 : subd11_0 [3, -1, -3] = true := by decide +kernel
theorem subd11_0_1729 : subd11_0 [3, -1, -2] = true := by decide +kernel
theorem subd11_0_1730 : subd11_0 [3, -1, -1] = true := by decide +kernel
theorem subd11_0_1731 : subd11_0 [3, -1, 0] = true := by decide +kernel
theorem subd11_0_1732 : subd11_0 [3, -1, 1] = true := by decide +kernel
theorem subd11_0_1733 : subd11_0 [3, -1, 2] = true := by decide +kernel
theorem subd11_0_1734 : subd11_0 [3, -1, 3] = true := by decide +kernel
theorem subd11_0_1735 : subd11_0 [3, -1, 4] = true := by decide +kernel
theorem subd11_0_1736 : subd11_0 [3, -1, 5] = true := by decide +kernel
theorem subd11_0_1737 : subd11_0 [3, -1, 6] = true := by decide +kernel
theorem subd11_0_1738 : subd11_0 [3, -1, 7] = true := by decide +kernel
theorem subd11_0_1739 : subd11_0 [3, -1, 8] = true := by decide +kernel
theorem subd11_0_1740 : subd11_0 [3, 0, -8] = true := by decide +kernel
theorem subd11_0_1741 : subd11_0 [3, 0, -7] = true := by decide +kernel
theorem subd11_0_1742 : subd11_0 [3, 0, -6] = true := by decide +kernel
theorem subd11_0_1743 : subd11_0 [3, 0, -5] = true := by decide +kernel
theorem subd11_0_1744 : subd11_0 [3, 0, -4] = true := by decide +kernel
theorem subd11_0_1745 : subd11_0 [3, 0, -3] = true := by decide +kernel
theorem subd11_0_1746 : subd11_0 [3, 0, -2] = true := by decide +kernel
theorem subd11_0_1747 : subd11_0 [3, 0, -1] = true := by decide +kernel
theorem subd11_0_1748 : subd11_0 [3, 0, 0] = true := by decide +kernel
theorem subd11_0_1749 : subd11_0 [3, 0, 1] = true := by decide +kernel
theorem subd11_0_1750 : subd11_0 [3, 0, 2] = true := by decide +kernel
theorem subd11_0_1751 : subd11_0 [3, 0, 3] = true := by decide +kernel
theorem subd11_0_1752 : subd11_0 [3, 0, 4] = true := by decide +kernel
theorem subd11_0_1753 : subd11_0 [3, 0, 5] = true := by decide +kernel
theorem subd11_0_1754 : subd11_0 [3, 0, 6] = true := by decide +kernel
theorem subd11_0_1755 : subd11_0 [3, 0, 7] = true := by decide +kernel
theorem subd11_0_1756 : subd11_0 [3, 0, 8] = true := by decide +kernel
theorem subd11_0_1757 : subd11_0 [3, 1, -8] = true := by decide +kernel
theorem subd11_0_1758 : subd11_0 [3, 1, -7] = true := by decide +kernel
theorem subd11_0_1759 : subd11_0 [3, 1, -6] = true := by decide +kernel
theorem sbd11_0_54 : ∀ q ∈ blkd11_0_54, subd11_0 q = true := by
  unfold blkd11_0_54
  exact List.forall_mem_cons.2 ⟨subd11_0_1728, List.forall_mem_cons.2 ⟨subd11_0_1729, List.forall_mem_cons.2 ⟨subd11_0_1730, List.forall_mem_cons.2 ⟨subd11_0_1731, List.forall_mem_cons.2 ⟨subd11_0_1732, List.forall_mem_cons.2 ⟨subd11_0_1733, List.forall_mem_cons.2 ⟨subd11_0_1734, List.forall_mem_cons.2 ⟨subd11_0_1735, List.forall_mem_cons.2 ⟨subd11_0_1736, List.forall_mem_cons.2 ⟨subd11_0_1737, List.forall_mem_cons.2 ⟨subd11_0_1738, List.forall_mem_cons.2 ⟨subd11_0_1739, List.forall_mem_cons.2 ⟨subd11_0_1740, List.forall_mem_cons.2 ⟨subd11_0_1741, List.forall_mem_cons.2 ⟨subd11_0_1742, List.forall_mem_cons.2 ⟨subd11_0_1743, List.forall_mem_cons.2 ⟨subd11_0_1744, List.forall_mem_cons.2 ⟨subd11_0_1745, List.forall_mem_cons.2 ⟨subd11_0_1746, List.forall_mem_cons.2 ⟨subd11_0_1747, List.forall_mem_cons.2 ⟨subd11_0_1748, List.forall_mem_cons.2 ⟨subd11_0_1749, List.forall_mem_cons.2 ⟨subd11_0_1750, List.forall_mem_cons.2 ⟨subd11_0_1751, List.forall_mem_cons.2 ⟨subd11_0_1752, List.forall_mem_cons.2 ⟨subd11_0_1753, List.forall_mem_cons.2 ⟨subd11_0_1754, List.forall_mem_cons.2 ⟨subd11_0_1755, List.forall_mem_cons.2 ⟨subd11_0_1756, List.forall_mem_cons.2 ⟨subd11_0_1757, List.forall_mem_cons.2 ⟨subd11_0_1758, List.forall_mem_cons.2 ⟨subd11_0_1759, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_1760 : subd11_0 [3, 1, -5] = true := by decide +kernel
theorem subd11_0_1761 : subd11_0 [3, 1, -4] = true := by decide +kernel
theorem subd11_0_1762 : subd11_0 [3, 1, -3] = true := by decide +kernel
theorem subd11_0_1763 : subd11_0 [3, 1, -2] = true := by decide +kernel
theorem subd11_0_1764 : subd11_0 [3, 1, -1] = true := by decide +kernel
theorem subd11_0_1765 : subd11_0 [3, 1, 0] = true := by decide +kernel
theorem subd11_0_1766 : subd11_0 [3, 1, 1] = true := by decide +kernel
theorem subd11_0_1767 : subd11_0 [3, 1, 2] = true := by decide +kernel
theorem subd11_0_1768 : subd11_0 [3, 1, 3] = true := by decide +kernel
theorem subd11_0_1769 : subd11_0 [3, 1, 4] = true := by decide +kernel
theorem subd11_0_1770 : subd11_0 [3, 1, 5] = true := by decide +kernel
theorem subd11_0_1771 : subd11_0 [3, 1, 6] = true := by decide +kernel
theorem subd11_0_1772 : subd11_0 [3, 1, 7] = true := by decide +kernel
theorem subd11_0_1773 : subd11_0 [3, 1, 8] = true := by decide +kernel
theorem subd11_0_1774 : subd11_0 [3, 2, -8] = true := by decide +kernel
theorem subd11_0_1775 : subd11_0 [3, 2, -7] = true := by decide +kernel
theorem subd11_0_1776 : subd11_0 [3, 2, -6] = true := by decide +kernel
theorem subd11_0_1777 : subd11_0 [3, 2, -5] = true := by decide +kernel
theorem subd11_0_1778 : subd11_0 [3, 2, -4] = true := by decide +kernel
theorem subd11_0_1779 : subd11_0 [3, 2, -3] = true := by decide +kernel
theorem subd11_0_1780 : subd11_0 [3, 2, -2] = true := by decide +kernel
theorem subd11_0_1781 : subd11_0 [3, 2, -1] = true := by decide +kernel
theorem subd11_0_1782 : subd11_0 [3, 2, 0] = true := by decide +kernel
theorem subd11_0_1783 : subd11_0 [3, 2, 1] = true := by decide +kernel
theorem subd11_0_1784 : subd11_0 [3, 2, 2] = true := by decide +kernel
theorem subd11_0_1785 : subd11_0 [3, 2, 3] = true := by decide +kernel
theorem subd11_0_1786 : subd11_0 [3, 2, 4] = true := by decide +kernel
theorem subd11_0_1787 : subd11_0 [3, 2, 5] = true := by decide +kernel
theorem subd11_0_1788 : subd11_0 [3, 2, 6] = true := by decide +kernel
theorem subd11_0_1789 : subd11_0 [3, 2, 7] = true := by decide +kernel
theorem subd11_0_1790 : subd11_0 [3, 2, 8] = true := by decide +kernel
theorem subd11_0_1791 : subd11_0 [3, 3, -8] = true := by decide +kernel
theorem sbd11_0_55 : ∀ q ∈ blkd11_0_55, subd11_0 q = true := by
  unfold blkd11_0_55
  exact List.forall_mem_cons.2 ⟨subd11_0_1760, List.forall_mem_cons.2 ⟨subd11_0_1761, List.forall_mem_cons.2 ⟨subd11_0_1762, List.forall_mem_cons.2 ⟨subd11_0_1763, List.forall_mem_cons.2 ⟨subd11_0_1764, List.forall_mem_cons.2 ⟨subd11_0_1765, List.forall_mem_cons.2 ⟨subd11_0_1766, List.forall_mem_cons.2 ⟨subd11_0_1767, List.forall_mem_cons.2 ⟨subd11_0_1768, List.forall_mem_cons.2 ⟨subd11_0_1769, List.forall_mem_cons.2 ⟨subd11_0_1770, List.forall_mem_cons.2 ⟨subd11_0_1771, List.forall_mem_cons.2 ⟨subd11_0_1772, List.forall_mem_cons.2 ⟨subd11_0_1773, List.forall_mem_cons.2 ⟨subd11_0_1774, List.forall_mem_cons.2 ⟨subd11_0_1775, List.forall_mem_cons.2 ⟨subd11_0_1776, List.forall_mem_cons.2 ⟨subd11_0_1777, List.forall_mem_cons.2 ⟨subd11_0_1778, List.forall_mem_cons.2 ⟨subd11_0_1779, List.forall_mem_cons.2 ⟨subd11_0_1780, List.forall_mem_cons.2 ⟨subd11_0_1781, List.forall_mem_cons.2 ⟨subd11_0_1782, List.forall_mem_cons.2 ⟨subd11_0_1783, List.forall_mem_cons.2 ⟨subd11_0_1784, List.forall_mem_cons.2 ⟨subd11_0_1785, List.forall_mem_cons.2 ⟨subd11_0_1786, List.forall_mem_cons.2 ⟨subd11_0_1787, List.forall_mem_cons.2 ⟨subd11_0_1788, List.forall_mem_cons.2 ⟨subd11_0_1789, List.forall_mem_cons.2 ⟨subd11_0_1790, List.forall_mem_cons.2 ⟨subd11_0_1791, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_1792 : subd11_0 [3, 3, -7] = true := by decide +kernel
theorem subd11_0_1793 : subd11_0 [3, 3, -6] = true := by decide +kernel
theorem subd11_0_1794 : subd11_0 [3, 3, -5] = true := by decide +kernel
theorem subd11_0_1795 : subd11_0 [3, 3, -4] = true := by decide +kernel
theorem subd11_0_1796 : subd11_0 [3, 3, -3] = true := by decide +kernel
theorem subd11_0_1797 : subd11_0 [3, 3, -2] = true := by decide +kernel
theorem subd11_0_1798 : subd11_0 [3, 3, -1] = true := by decide +kernel
theorem subd11_0_1799 : subd11_0 [3, 3, 0] = true := by decide +kernel
theorem subd11_0_1800 : subd11_0 [3, 3, 1] = true := by decide +kernel
theorem subd11_0_1801 : subd11_0 [3, 3, 2] = true := by decide +kernel
theorem subd11_0_1802 : subd11_0 [3, 3, 3] = true := by decide +kernel
theorem subd11_0_1803 : subd11_0 [3, 3, 4] = true := by decide +kernel
theorem subd11_0_1804 : subd11_0 [3, 3, 5] = true := by decide +kernel
theorem subd11_0_1805 : subd11_0 [3, 3, 6] = true := by decide +kernel
theorem subd11_0_1806 : subd11_0 [3, 3, 7] = true := by decide +kernel
theorem subd11_0_1807 : subd11_0 [3, 3, 8] = true := by decide +kernel
theorem subd11_0_1808 : subd11_0 [3, 4, -8] = true := by decide +kernel
theorem subd11_0_1809 : subd11_0 [3, 4, -7] = true := by decide +kernel
theorem subd11_0_1810 : subd11_0 [3, 4, -6] = true := by decide +kernel
theorem subd11_0_1811 : subd11_0 [3, 4, -5] = true := by decide +kernel
theorem subd11_0_1812 : subd11_0 [3, 4, -4] = true := by decide +kernel
theorem subd11_0_1813 : subd11_0 [3, 4, -3] = true := by decide +kernel
theorem subd11_0_1814 : subd11_0 [3, 4, -2] = true := by decide +kernel
theorem subd11_0_1815 : subd11_0 [3, 4, -1] = true := by decide +kernel
theorem subd11_0_1816 : subd11_0 [3, 4, 0] = true := by decide +kernel
theorem subd11_0_1817 : subd11_0 [3, 4, 1] = true := by decide +kernel
theorem subd11_0_1818 : subd11_0 [3, 4, 2] = true := by decide +kernel
theorem subd11_0_1819 : subd11_0 [3, 4, 3] = true := by decide +kernel
theorem subd11_0_1820 : subd11_0 [3, 4, 4] = true := by decide +kernel
theorem subd11_0_1821 : subd11_0 [3, 4, 5] = true := by decide +kernel
theorem subd11_0_1822 : subd11_0 [3, 4, 6] = true := by decide +kernel
theorem subd11_0_1823 : subd11_0 [3, 4, 7] = true := by decide +kernel
theorem sbd11_0_56 : ∀ q ∈ blkd11_0_56, subd11_0 q = true := by
  unfold blkd11_0_56
  exact List.forall_mem_cons.2 ⟨subd11_0_1792, List.forall_mem_cons.2 ⟨subd11_0_1793, List.forall_mem_cons.2 ⟨subd11_0_1794, List.forall_mem_cons.2 ⟨subd11_0_1795, List.forall_mem_cons.2 ⟨subd11_0_1796, List.forall_mem_cons.2 ⟨subd11_0_1797, List.forall_mem_cons.2 ⟨subd11_0_1798, List.forall_mem_cons.2 ⟨subd11_0_1799, List.forall_mem_cons.2 ⟨subd11_0_1800, List.forall_mem_cons.2 ⟨subd11_0_1801, List.forall_mem_cons.2 ⟨subd11_0_1802, List.forall_mem_cons.2 ⟨subd11_0_1803, List.forall_mem_cons.2 ⟨subd11_0_1804, List.forall_mem_cons.2 ⟨subd11_0_1805, List.forall_mem_cons.2 ⟨subd11_0_1806, List.forall_mem_cons.2 ⟨subd11_0_1807, List.forall_mem_cons.2 ⟨subd11_0_1808, List.forall_mem_cons.2 ⟨subd11_0_1809, List.forall_mem_cons.2 ⟨subd11_0_1810, List.forall_mem_cons.2 ⟨subd11_0_1811, List.forall_mem_cons.2 ⟨subd11_0_1812, List.forall_mem_cons.2 ⟨subd11_0_1813, List.forall_mem_cons.2 ⟨subd11_0_1814, List.forall_mem_cons.2 ⟨subd11_0_1815, List.forall_mem_cons.2 ⟨subd11_0_1816, List.forall_mem_cons.2 ⟨subd11_0_1817, List.forall_mem_cons.2 ⟨subd11_0_1818, List.forall_mem_cons.2 ⟨subd11_0_1819, List.forall_mem_cons.2 ⟨subd11_0_1820, List.forall_mem_cons.2 ⟨subd11_0_1821, List.forall_mem_cons.2 ⟨subd11_0_1822, List.forall_mem_cons.2 ⟨subd11_0_1823, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_1824 : subd11_0 [3, 4, 8] = true := by decide +kernel
theorem subd11_0_1825 : subd11_0 [3, 5, -7] = true := by decide +kernel
theorem subd11_0_1826 : subd11_0 [3, 5, -6] = true := by decide +kernel
theorem subd11_0_1827 : subd11_0 [3, 5, -5] = true := by decide +kernel
theorem subd11_0_1828 : subd11_0 [3, 5, -4] = true := by decide +kernel
theorem subd11_0_1829 : subd11_0 [3, 5, -3] = true := by decide +kernel
theorem subd11_0_1830 : subd11_0 [3, 5, -2] = true := by decide +kernel
theorem subd11_0_1831 : subd11_0 [3, 5, -1] = true := by decide +kernel
theorem subd11_0_1832 : subd11_0 [3, 5, 0] = true := by decide +kernel
theorem subd11_0_1833 : subd11_0 [3, 5, 1] = true := by decide +kernel
theorem subd11_0_1834 : subd11_0 [3, 5, 2] = true := by decide +kernel
theorem subd11_0_1835 : subd11_0 [3, 5, 3] = true := by decide +kernel
theorem subd11_0_1836 : subd11_0 [3, 5, 4] = true := by decide +kernel
theorem subd11_0_1837 : subd11_0 [3, 5, 5] = true := by decide +kernel
theorem subd11_0_1838 : subd11_0 [3, 5, 6] = true := by decide +kernel
theorem subd11_0_1839 : subd11_0 [3, 5, 7] = true := by decide +kernel
theorem subd11_0_1840 : subd11_0 [3, 6, -7] = true := by decide +kernel
theorem subd11_0_1841 : subd11_0 [3, 6, -6] = true := by decide +kernel
theorem subd11_0_1842 : subd11_0 [3, 6, -5] = true := by decide +kernel
theorem subd11_0_1843 : subd11_0 [3, 6, -4] = true := by decide +kernel
theorem subd11_0_1844 : subd11_0 [3, 6, -3] = true := by decide +kernel
theorem subd11_0_1845 : subd11_0 [3, 6, -2] = true := by decide +kernel
theorem subd11_0_1846 : subd11_0 [3, 6, -1] = true := by decide +kernel
theorem subd11_0_1847 : subd11_0 [3, 6, 0] = true := by decide +kernel
theorem subd11_0_1848 : subd11_0 [3, 6, 1] = true := by decide +kernel
theorem subd11_0_1849 : subd11_0 [3, 6, 2] = true := by decide +kernel
theorem subd11_0_1850 : subd11_0 [3, 6, 3] = true := by decide +kernel
theorem subd11_0_1851 : subd11_0 [3, 6, 4] = true := by decide +kernel
theorem subd11_0_1852 : subd11_0 [3, 6, 5] = true := by decide +kernel
theorem subd11_0_1853 : subd11_0 [3, 6, 6] = true := by decide +kernel
theorem subd11_0_1854 : subd11_0 [3, 6, 7] = true := by decide +kernel
theorem subd11_0_1855 : subd11_0 [3, 7, -6] = true := by decide +kernel
theorem sbd11_0_57 : ∀ q ∈ blkd11_0_57, subd11_0 q = true := by
  unfold blkd11_0_57
  exact List.forall_mem_cons.2 ⟨subd11_0_1824, List.forall_mem_cons.2 ⟨subd11_0_1825, List.forall_mem_cons.2 ⟨subd11_0_1826, List.forall_mem_cons.2 ⟨subd11_0_1827, List.forall_mem_cons.2 ⟨subd11_0_1828, List.forall_mem_cons.2 ⟨subd11_0_1829, List.forall_mem_cons.2 ⟨subd11_0_1830, List.forall_mem_cons.2 ⟨subd11_0_1831, List.forall_mem_cons.2 ⟨subd11_0_1832, List.forall_mem_cons.2 ⟨subd11_0_1833, List.forall_mem_cons.2 ⟨subd11_0_1834, List.forall_mem_cons.2 ⟨subd11_0_1835, List.forall_mem_cons.2 ⟨subd11_0_1836, List.forall_mem_cons.2 ⟨subd11_0_1837, List.forall_mem_cons.2 ⟨subd11_0_1838, List.forall_mem_cons.2 ⟨subd11_0_1839, List.forall_mem_cons.2 ⟨subd11_0_1840, List.forall_mem_cons.2 ⟨subd11_0_1841, List.forall_mem_cons.2 ⟨subd11_0_1842, List.forall_mem_cons.2 ⟨subd11_0_1843, List.forall_mem_cons.2 ⟨subd11_0_1844, List.forall_mem_cons.2 ⟨subd11_0_1845, List.forall_mem_cons.2 ⟨subd11_0_1846, List.forall_mem_cons.2 ⟨subd11_0_1847, List.forall_mem_cons.2 ⟨subd11_0_1848, List.forall_mem_cons.2 ⟨subd11_0_1849, List.forall_mem_cons.2 ⟨subd11_0_1850, List.forall_mem_cons.2 ⟨subd11_0_1851, List.forall_mem_cons.2 ⟨subd11_0_1852, List.forall_mem_cons.2 ⟨subd11_0_1853, List.forall_mem_cons.2 ⟨subd11_0_1854, List.forall_mem_cons.2 ⟨subd11_0_1855, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_1856 : subd11_0 [3, 7, -5] = true := by decide +kernel
theorem subd11_0_1857 : subd11_0 [3, 7, -4] = true := by decide +kernel
theorem subd11_0_1858 : subd11_0 [3, 7, -3] = true := by decide +kernel
theorem subd11_0_1859 : subd11_0 [3, 7, -2] = true := by decide +kernel
theorem subd11_0_1860 : subd11_0 [3, 7, -1] = true := by decide +kernel
theorem subd11_0_1861 : subd11_0 [3, 7, 0] = true := by decide +kernel
theorem subd11_0_1862 : subd11_0 [3, 7, 1] = true := by decide +kernel
theorem subd11_0_1863 : subd11_0 [3, 7, 2] = true := by decide +kernel
theorem subd11_0_1864 : subd11_0 [3, 7, 3] = true := by decide +kernel
theorem subd11_0_1865 : subd11_0 [3, 7, 4] = true := by decide +kernel
theorem subd11_0_1866 : subd11_0 [3, 7, 5] = true := by decide +kernel
theorem subd11_0_1867 : subd11_0 [3, 7, 6] = true := by decide +kernel
theorem subd11_0_1868 : subd11_0 [3, 8] = true := by decide +kernel
theorem subd11_0_1869 : subd11_0 [3, 9] = true := by decide +kernel
theorem subd11_0_1870 : subd11_0 [3, 10] = true := by decide +kernel
theorem subd11_0_1871 : subd11_0 [4, -7] = true := by decide +kernel
theorem subd11_0_1872 : subd11_0 [4, -6] = true := by decide +kernel
theorem subd11_0_1873 : subd11_0 [4, -5] = true := by decide +kernel
theorem subd11_0_1874 : subd11_0 [4, -4] = true := by decide +kernel
theorem subd11_0_1875 : subd11_0 [4, -3, -6] = true := by decide +kernel
theorem subd11_0_1876 : subd11_0 [4, -3, -5] = true := by decide +kernel
theorem subd11_0_1877 : subd11_0 [4, -3, -4] = true := by decide +kernel
theorem subd11_0_1878 : subd11_0 [4, -3, -3] = true := by decide +kernel
theorem subd11_0_1879 : subd11_0 [4, -3, -2] = true := by decide +kernel
theorem subd11_0_1880 : subd11_0 [4, -3, -1] = true := by decide +kernel
theorem subd11_0_1881 : subd11_0 [4, -3, 0] = true := by decide +kernel
theorem subd11_0_1882 : subd11_0 [4, -3, 1] = true := by decide +kernel
theorem subd11_0_1883 : subd11_0 [4, -3, 2] = true := by decide +kernel
theorem subd11_0_1884 : subd11_0 [4, -3, 3] = true := by decide +kernel
theorem subd11_0_1885 : subd11_0 [4, -3, 4] = true := by decide +kernel
theorem subd11_0_1886 : subd11_0 [4, -3, 5] = true := by decide +kernel
theorem subd11_0_1887 : subd11_0 [4, -3, 6] = true := by decide +kernel
theorem sbd11_0_58 : ∀ q ∈ blkd11_0_58, subd11_0 q = true := by
  unfold blkd11_0_58
  exact List.forall_mem_cons.2 ⟨subd11_0_1856, List.forall_mem_cons.2 ⟨subd11_0_1857, List.forall_mem_cons.2 ⟨subd11_0_1858, List.forall_mem_cons.2 ⟨subd11_0_1859, List.forall_mem_cons.2 ⟨subd11_0_1860, List.forall_mem_cons.2 ⟨subd11_0_1861, List.forall_mem_cons.2 ⟨subd11_0_1862, List.forall_mem_cons.2 ⟨subd11_0_1863, List.forall_mem_cons.2 ⟨subd11_0_1864, List.forall_mem_cons.2 ⟨subd11_0_1865, List.forall_mem_cons.2 ⟨subd11_0_1866, List.forall_mem_cons.2 ⟨subd11_0_1867, List.forall_mem_cons.2 ⟨subd11_0_1868, List.forall_mem_cons.2 ⟨subd11_0_1869, List.forall_mem_cons.2 ⟨subd11_0_1870, List.forall_mem_cons.2 ⟨subd11_0_1871, List.forall_mem_cons.2 ⟨subd11_0_1872, List.forall_mem_cons.2 ⟨subd11_0_1873, List.forall_mem_cons.2 ⟨subd11_0_1874, List.forall_mem_cons.2 ⟨subd11_0_1875, List.forall_mem_cons.2 ⟨subd11_0_1876, List.forall_mem_cons.2 ⟨subd11_0_1877, List.forall_mem_cons.2 ⟨subd11_0_1878, List.forall_mem_cons.2 ⟨subd11_0_1879, List.forall_mem_cons.2 ⟨subd11_0_1880, List.forall_mem_cons.2 ⟨subd11_0_1881, List.forall_mem_cons.2 ⟨subd11_0_1882, List.forall_mem_cons.2 ⟨subd11_0_1883, List.forall_mem_cons.2 ⟨subd11_0_1884, List.forall_mem_cons.2 ⟨subd11_0_1885, List.forall_mem_cons.2 ⟨subd11_0_1886, List.forall_mem_cons.2 ⟨subd11_0_1887, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_1888 : subd11_0 [4, -3, 7] = true := by decide +kernel
theorem subd11_0_1889 : subd11_0 [4, -2, -6] = true := by decide +kernel
theorem subd11_0_1890 : subd11_0 [4, -2, -5] = true := by decide +kernel
theorem subd11_0_1891 : subd11_0 [4, -2, -4] = true := by decide +kernel
theorem subd11_0_1892 : subd11_0 [4, -2, -3] = true := by decide +kernel
theorem subd11_0_1893 : subd11_0 [4, -2, -2] = true := by decide +kernel
theorem subd11_0_1894 : subd11_0 [4, -2, -1] = true := by decide +kernel
theorem subd11_0_1895 : subd11_0 [4, -2, 0] = true := by decide +kernel
theorem subd11_0_1896 : subd11_0 [4, -2, 1] = true := by decide +kernel
theorem subd11_0_1897 : subd11_0 [4, -2, 2] = true := by decide +kernel
theorem subd11_0_1898 : subd11_0 [4, -2, 3] = true := by decide +kernel
theorem subd11_0_1899 : subd11_0 [4, -2, 4] = true := by decide +kernel
theorem subd11_0_1900 : subd11_0 [4, -2, 5] = true := by decide +kernel
theorem subd11_0_1901 : subd11_0 [4, -2, 6] = true := by decide +kernel
theorem subd11_0_1902 : subd11_0 [4, -2, 7] = true := by decide +kernel
theorem subd11_0_1903 : subd11_0 [4, -2, 8] = true := by decide +kernel
theorem subd11_0_1904 : subd11_0 [4, -1, -7] = true := by decide +kernel
theorem subd11_0_1905 : subd11_0 [4, -1, -6] = true := by decide +kernel
theorem subd11_0_1906 : subd11_0 [4, -1, -5] = true := by decide +kernel
theorem subd11_0_1907 : subd11_0 [4, -1, -4] = true := by decide +kernel
theorem subd11_0_1908 : subd11_0 [4, -1, -3] = true := by decide +kernel
theorem subd11_0_1909 : subd11_0 [4, -1, -2] = true := by decide +kernel
theorem subd11_0_1910 : subd11_0 [4, -1, -1] = true := by decide +kernel
theorem subd11_0_1911 : subd11_0 [4, -1, 0] = true := by decide +kernel
theorem subd11_0_1912 : subd11_0 [4, -1, 1] = true := by decide +kernel
theorem subd11_0_1913 : subd11_0 [4, -1, 2] = true := by decide +kernel
theorem subd11_0_1914 : subd11_0 [4, -1, 3] = true := by decide +kernel
theorem subd11_0_1915 : subd11_0 [4, -1, 4] = true := by decide +kernel
theorem subd11_0_1916 : subd11_0 [4, -1, 5] = true := by decide +kernel
theorem subd11_0_1917 : subd11_0 [4, -1, 6] = true := by decide +kernel
theorem subd11_0_1918 : subd11_0 [4, -1, 7] = true := by decide +kernel
theorem subd11_0_1919 : subd11_0 [4, -1, 8] = true := by decide +kernel
theorem sbd11_0_59 : ∀ q ∈ blkd11_0_59, subd11_0 q = true := by
  unfold blkd11_0_59
  exact List.forall_mem_cons.2 ⟨subd11_0_1888, List.forall_mem_cons.2 ⟨subd11_0_1889, List.forall_mem_cons.2 ⟨subd11_0_1890, List.forall_mem_cons.2 ⟨subd11_0_1891, List.forall_mem_cons.2 ⟨subd11_0_1892, List.forall_mem_cons.2 ⟨subd11_0_1893, List.forall_mem_cons.2 ⟨subd11_0_1894, List.forall_mem_cons.2 ⟨subd11_0_1895, List.forall_mem_cons.2 ⟨subd11_0_1896, List.forall_mem_cons.2 ⟨subd11_0_1897, List.forall_mem_cons.2 ⟨subd11_0_1898, List.forall_mem_cons.2 ⟨subd11_0_1899, List.forall_mem_cons.2 ⟨subd11_0_1900, List.forall_mem_cons.2 ⟨subd11_0_1901, List.forall_mem_cons.2 ⟨subd11_0_1902, List.forall_mem_cons.2 ⟨subd11_0_1903, List.forall_mem_cons.2 ⟨subd11_0_1904, List.forall_mem_cons.2 ⟨subd11_0_1905, List.forall_mem_cons.2 ⟨subd11_0_1906, List.forall_mem_cons.2 ⟨subd11_0_1907, List.forall_mem_cons.2 ⟨subd11_0_1908, List.forall_mem_cons.2 ⟨subd11_0_1909, List.forall_mem_cons.2 ⟨subd11_0_1910, List.forall_mem_cons.2 ⟨subd11_0_1911, List.forall_mem_cons.2 ⟨subd11_0_1912, List.forall_mem_cons.2 ⟨subd11_0_1913, List.forall_mem_cons.2 ⟨subd11_0_1914, List.forall_mem_cons.2 ⟨subd11_0_1915, List.forall_mem_cons.2 ⟨subd11_0_1916, List.forall_mem_cons.2 ⟨subd11_0_1917, List.forall_mem_cons.2 ⟨subd11_0_1918, List.forall_mem_cons.2 ⟨subd11_0_1919, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_1920 : subd11_0 [4, 0, -7] = true := by decide +kernel
theorem subd11_0_1921 : subd11_0 [4, 0, -6] = true := by decide +kernel
theorem subd11_0_1922 : subd11_0 [4, 0, -5] = true := by decide +kernel
theorem subd11_0_1923 : subd11_0 [4, 0, -4] = true := by decide +kernel
theorem subd11_0_1924 : subd11_0 [4, 0, -3] = true := by decide +kernel
theorem subd11_0_1925 : subd11_0 [4, 0, -2] = true := by decide +kernel
theorem subd11_0_1926 : subd11_0 [4, 0, -1] = true := by decide +kernel
theorem subd11_0_1927 : subd11_0 [4, 0, 0] = true := by decide +kernel
theorem subd11_0_1928 : subd11_0 [4, 0, 1] = true := by decide +kernel
theorem subd11_0_1929 : subd11_0 [4, 0, 2] = true := by decide +kernel
theorem subd11_0_1930 : subd11_0 [4, 0, 3] = true := by decide +kernel
theorem subd11_0_1931 : subd11_0 [4, 0, 4] = true := by decide +kernel
theorem subd11_0_1932 : subd11_0 [4, 0, 5] = true := by decide +kernel
theorem subd11_0_1933 : subd11_0 [4, 0, 6] = true := by decide +kernel
theorem subd11_0_1934 : subd11_0 [4, 0, 7] = true := by decide +kernel
theorem subd11_0_1935 : subd11_0 [4, 0, 8] = true := by decide +kernel
theorem subd11_0_1936 : subd11_0 [4, 1, -7] = true := by decide +kernel
theorem subd11_0_1937 : subd11_0 [4, 1, -6] = true := by decide +kernel
theorem subd11_0_1938 : subd11_0 [4, 1, -5] = true := by decide +kernel
theorem subd11_0_1939 : subd11_0 [4, 1, -4] = true := by decide +kernel
theorem subd11_0_1940 : subd11_0 [4, 1, -3] = true := by decide +kernel
theorem subd11_0_1941 : subd11_0 [4, 1, -2] = true := by decide +kernel
theorem subd11_0_1942 : subd11_0 [4, 1, -1] = true := by decide +kernel
theorem subd11_0_1943 : subd11_0 [4, 1, 0] = true := by decide +kernel
theorem subd11_0_1944 : subd11_0 [4, 1, 1] = true := by decide +kernel
theorem subd11_0_1945 : subd11_0 [4, 1, 2] = true := by decide +kernel
theorem subd11_0_1946 : subd11_0 [4, 1, 3] = true := by decide +kernel
theorem subd11_0_1947 : subd11_0 [4, 1, 4] = true := by decide +kernel
theorem subd11_0_1948 : subd11_0 [4, 1, 5] = true := by decide +kernel
theorem subd11_0_1949 : subd11_0 [4, 1, 6] = true := by decide +kernel
theorem subd11_0_1950 : subd11_0 [4, 1, 7] = true := by decide +kernel
theorem subd11_0_1951 : subd11_0 [4, 1, 8] = true := by decide +kernel
theorem sbd11_0_60 : ∀ q ∈ blkd11_0_60, subd11_0 q = true := by
  unfold blkd11_0_60
  exact List.forall_mem_cons.2 ⟨subd11_0_1920, List.forall_mem_cons.2 ⟨subd11_0_1921, List.forall_mem_cons.2 ⟨subd11_0_1922, List.forall_mem_cons.2 ⟨subd11_0_1923, List.forall_mem_cons.2 ⟨subd11_0_1924, List.forall_mem_cons.2 ⟨subd11_0_1925, List.forall_mem_cons.2 ⟨subd11_0_1926, List.forall_mem_cons.2 ⟨subd11_0_1927, List.forall_mem_cons.2 ⟨subd11_0_1928, List.forall_mem_cons.2 ⟨subd11_0_1929, List.forall_mem_cons.2 ⟨subd11_0_1930, List.forall_mem_cons.2 ⟨subd11_0_1931, List.forall_mem_cons.2 ⟨subd11_0_1932, List.forall_mem_cons.2 ⟨subd11_0_1933, List.forall_mem_cons.2 ⟨subd11_0_1934, List.forall_mem_cons.2 ⟨subd11_0_1935, List.forall_mem_cons.2 ⟨subd11_0_1936, List.forall_mem_cons.2 ⟨subd11_0_1937, List.forall_mem_cons.2 ⟨subd11_0_1938, List.forall_mem_cons.2 ⟨subd11_0_1939, List.forall_mem_cons.2 ⟨subd11_0_1940, List.forall_mem_cons.2 ⟨subd11_0_1941, List.forall_mem_cons.2 ⟨subd11_0_1942, List.forall_mem_cons.2 ⟨subd11_0_1943, List.forall_mem_cons.2 ⟨subd11_0_1944, List.forall_mem_cons.2 ⟨subd11_0_1945, List.forall_mem_cons.2 ⟨subd11_0_1946, List.forall_mem_cons.2 ⟨subd11_0_1947, List.forall_mem_cons.2 ⟨subd11_0_1948, List.forall_mem_cons.2 ⟨subd11_0_1949, List.forall_mem_cons.2 ⟨subd11_0_1950, List.forall_mem_cons.2 ⟨subd11_0_1951, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_1952 : subd11_0 [4, 2, -7] = true := by decide +kernel
theorem subd11_0_1953 : subd11_0 [4, 2, -6] = true := by decide +kernel
theorem subd11_0_1954 : subd11_0 [4, 2, -5] = true := by decide +kernel
theorem subd11_0_1955 : subd11_0 [4, 2, -4] = true := by decide +kernel
theorem subd11_0_1956 : subd11_0 [4, 2, -3] = true := by decide +kernel
theorem subd11_0_1957 : subd11_0 [4, 2, -2] = true := by decide +kernel
theorem subd11_0_1958 : subd11_0 [4, 2, -1] = true := by decide +kernel
theorem subd11_0_1959 : subd11_0 [4, 2, 0] = true := by decide +kernel
theorem subd11_0_1960 : subd11_0 [4, 2, 1] = true := by decide +kernel
theorem subd11_0_1961 : subd11_0 [4, 2, 2] = true := by decide +kernel
theorem subd11_0_1962 : subd11_0 [4, 2, 3] = true := by decide +kernel
theorem subd11_0_1963 : subd11_0 [4, 2, 4] = true := by decide +kernel
theorem subd11_0_1964 : subd11_0 [4, 2, 5] = true := by decide +kernel
theorem subd11_0_1965 : subd11_0 [4, 2, 6] = true := by decide +kernel
theorem subd11_0_1966 : subd11_0 [4, 2, 7] = true := by decide +kernel
theorem subd11_0_1967 : subd11_0 [4, 2, 8] = true := by decide +kernel
theorem subd11_0_1968 : subd11_0 [4, 3, -7] = true := by decide +kernel
theorem subd11_0_1969 : subd11_0 [4, 3, -6] = true := by decide +kernel
theorem subd11_0_1970 : subd11_0 [4, 3, -5] = true := by decide +kernel
theorem subd11_0_1971 : subd11_0 [4, 3, -4] = true := by decide +kernel
theorem subd11_0_1972 : subd11_0 [4, 3, -3] = true := by decide +kernel
theorem subd11_0_1973 : subd11_0 [4, 3, -2] = true := by decide +kernel
theorem subd11_0_1974 : subd11_0 [4, 3, -1] = true := by decide +kernel
theorem subd11_0_1975 : subd11_0 [4, 3, 0] = true := by decide +kernel
theorem subd11_0_1976 : subd11_0 [4, 3, 1] = true := by decide +kernel
theorem subd11_0_1977 : subd11_0 [4, 3, 2] = true := by decide +kernel
theorem subd11_0_1978 : subd11_0 [4, 3, 3] = true := by decide +kernel
theorem subd11_0_1979 : subd11_0 [4, 3, 4] = true := by decide +kernel
theorem subd11_0_1980 : subd11_0 [4, 3, 5] = true := by decide +kernel
theorem subd11_0_1981 : subd11_0 [4, 3, 6] = true := by decide +kernel
theorem subd11_0_1982 : subd11_0 [4, 3, 7] = true := by decide +kernel
theorem subd11_0_1983 : subd11_0 [4, 3, 8] = true := by decide +kernel
theorem sbd11_0_61 : ∀ q ∈ blkd11_0_61, subd11_0 q = true := by
  unfold blkd11_0_61
  exact List.forall_mem_cons.2 ⟨subd11_0_1952, List.forall_mem_cons.2 ⟨subd11_0_1953, List.forall_mem_cons.2 ⟨subd11_0_1954, List.forall_mem_cons.2 ⟨subd11_0_1955, List.forall_mem_cons.2 ⟨subd11_0_1956, List.forall_mem_cons.2 ⟨subd11_0_1957, List.forall_mem_cons.2 ⟨subd11_0_1958, List.forall_mem_cons.2 ⟨subd11_0_1959, List.forall_mem_cons.2 ⟨subd11_0_1960, List.forall_mem_cons.2 ⟨subd11_0_1961, List.forall_mem_cons.2 ⟨subd11_0_1962, List.forall_mem_cons.2 ⟨subd11_0_1963, List.forall_mem_cons.2 ⟨subd11_0_1964, List.forall_mem_cons.2 ⟨subd11_0_1965, List.forall_mem_cons.2 ⟨subd11_0_1966, List.forall_mem_cons.2 ⟨subd11_0_1967, List.forall_mem_cons.2 ⟨subd11_0_1968, List.forall_mem_cons.2 ⟨subd11_0_1969, List.forall_mem_cons.2 ⟨subd11_0_1970, List.forall_mem_cons.2 ⟨subd11_0_1971, List.forall_mem_cons.2 ⟨subd11_0_1972, List.forall_mem_cons.2 ⟨subd11_0_1973, List.forall_mem_cons.2 ⟨subd11_0_1974, List.forall_mem_cons.2 ⟨subd11_0_1975, List.forall_mem_cons.2 ⟨subd11_0_1976, List.forall_mem_cons.2 ⟨subd11_0_1977, List.forall_mem_cons.2 ⟨subd11_0_1978, List.forall_mem_cons.2 ⟨subd11_0_1979, List.forall_mem_cons.2 ⟨subd11_0_1980, List.forall_mem_cons.2 ⟨subd11_0_1981, List.forall_mem_cons.2 ⟨subd11_0_1982, List.forall_mem_cons.2 ⟨subd11_0_1983, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_1984 : subd11_0 [4, 4, -7] = true := by decide +kernel
theorem subd11_0_1985 : subd11_0 [4, 4, -6] = true := by decide +kernel
theorem subd11_0_1986 : subd11_0 [4, 4, -5] = true := by decide +kernel
theorem subd11_0_1987 : subd11_0 [4, 4, -4] = true := by decide +kernel
theorem subd11_0_1988 : subd11_0 [4, 4, -3] = true := by decide +kernel
theorem subd11_0_1989 : subd11_0 [4, 4, -2] = true := by decide +kernel
theorem subd11_0_1990 : subd11_0 [4, 4, -1] = true := by decide +kernel
theorem subd11_0_1991 : subd11_0 [4, 4, 0] = true := by decide +kernel
theorem subd11_0_1992 : subd11_0 [4, 4, 1] = true := by decide +kernel
theorem subd11_0_1993 : subd11_0 [4, 4, 2] = true := by decide +kernel
theorem subd11_0_1994 : subd11_0 [4, 4, 3] = true := by decide +kernel
theorem subd11_0_1995 : subd11_0 [4, 4, 4] = true := by decide +kernel
theorem subd11_0_1996 : subd11_0 [4, 4, 5] = true := by decide +kernel
theorem subd11_0_1997 : subd11_0 [4, 4, 6] = true := by decide +kernel
theorem subd11_0_1998 : subd11_0 [4, 4, 7] = true := by decide +kernel
theorem subd11_0_1999 : subd11_0 [4, 4, 8] = true := by decide +kernel
theorem subd11_0_2000 : subd11_0 [4, 5, -7] = true := by decide +kernel
theorem subd11_0_2001 : subd11_0 [4, 5, -6] = true := by decide +kernel
theorem subd11_0_2002 : subd11_0 [4, 5, -5] = true := by decide +kernel
theorem subd11_0_2003 : subd11_0 [4, 5, -4] = true := by decide +kernel
theorem subd11_0_2004 : subd11_0 [4, 5, -3] = true := by decide +kernel
theorem subd11_0_2005 : subd11_0 [4, 5, -2] = true := by decide +kernel
theorem subd11_0_2006 : subd11_0 [4, 5, -1] = true := by decide +kernel
theorem subd11_0_2007 : subd11_0 [4, 5, 0] = true := by decide +kernel
theorem subd11_0_2008 : subd11_0 [4, 5, 1] = true := by decide +kernel
theorem subd11_0_2009 : subd11_0 [4, 5, 2] = true := by decide +kernel
theorem subd11_0_2010 : subd11_0 [4, 5, 3] = true := by decide +kernel
theorem subd11_0_2011 : subd11_0 [4, 5, 4] = true := by decide +kernel
theorem subd11_0_2012 : subd11_0 [4, 5, 5] = true := by decide +kernel
theorem subd11_0_2013 : subd11_0 [4, 5, 6] = true := by decide +kernel
theorem subd11_0_2014 : subd11_0 [4, 5, 7] = true := by decide +kernel
theorem subd11_0_2015 : subd11_0 [4, 6, -6] = true := by decide +kernel
theorem sbd11_0_62 : ∀ q ∈ blkd11_0_62, subd11_0 q = true := by
  unfold blkd11_0_62
  exact List.forall_mem_cons.2 ⟨subd11_0_1984, List.forall_mem_cons.2 ⟨subd11_0_1985, List.forall_mem_cons.2 ⟨subd11_0_1986, List.forall_mem_cons.2 ⟨subd11_0_1987, List.forall_mem_cons.2 ⟨subd11_0_1988, List.forall_mem_cons.2 ⟨subd11_0_1989, List.forall_mem_cons.2 ⟨subd11_0_1990, List.forall_mem_cons.2 ⟨subd11_0_1991, List.forall_mem_cons.2 ⟨subd11_0_1992, List.forall_mem_cons.2 ⟨subd11_0_1993, List.forall_mem_cons.2 ⟨subd11_0_1994, List.forall_mem_cons.2 ⟨subd11_0_1995, List.forall_mem_cons.2 ⟨subd11_0_1996, List.forall_mem_cons.2 ⟨subd11_0_1997, List.forall_mem_cons.2 ⟨subd11_0_1998, List.forall_mem_cons.2 ⟨subd11_0_1999, List.forall_mem_cons.2 ⟨subd11_0_2000, List.forall_mem_cons.2 ⟨subd11_0_2001, List.forall_mem_cons.2 ⟨subd11_0_2002, List.forall_mem_cons.2 ⟨subd11_0_2003, List.forall_mem_cons.2 ⟨subd11_0_2004, List.forall_mem_cons.2 ⟨subd11_0_2005, List.forall_mem_cons.2 ⟨subd11_0_2006, List.forall_mem_cons.2 ⟨subd11_0_2007, List.forall_mem_cons.2 ⟨subd11_0_2008, List.forall_mem_cons.2 ⟨subd11_0_2009, List.forall_mem_cons.2 ⟨subd11_0_2010, List.forall_mem_cons.2 ⟨subd11_0_2011, List.forall_mem_cons.2 ⟨subd11_0_2012, List.forall_mem_cons.2 ⟨subd11_0_2013, List.forall_mem_cons.2 ⟨subd11_0_2014, List.forall_mem_cons.2 ⟨subd11_0_2015, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C131
