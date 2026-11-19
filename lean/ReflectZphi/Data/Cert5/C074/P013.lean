import ReflectZphi.Data.Cert5.C074.Base

namespace ReflectZphi.Data.Cert5.C074
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub9_1600 : sub9 [3, 2, 9] = true := by decide +kernel
theorem sub9_1601 : sub9 [3, 2, 10] = true := by decide +kernel
theorem sub9_1602 : sub9 [3, 3, -7] = true := by decide +kernel
theorem sub9_1603 : sub9 [3, 3, -6] = true := by decide +kernel
theorem sub9_1604 : sub9 [3, 3, -5] = true := by decide +kernel
theorem sub9_1605 : sub9 [3, 3, -4] = true := by decide +kernel
theorem sub9_1606 : sub9 [3, 3, -3] = true := by decide +kernel
theorem sub9_1607 : sub9 [3, 3, -2] = true := by decide +kernel
theorem sub9_1608 : sub9 [3, 3, -1] = true := by decide +kernel
theorem sub9_1609 : sub9 [3, 3, 0] = true := by decide +kernel
theorem sub9_1610 : sub9 [3, 3, 1] = true := by decide +kernel
theorem sub9_1611 : sub9 [3, 3, 2] = true := by decide +kernel
theorem sub9_1612 : sub9 [3, 3, 3] = true := by decide +kernel
theorem sub9_1613 : sub9 [3, 3, 4] = true := by decide +kernel
theorem sub9_1614 : sub9 [3, 3, 5] = true := by decide +kernel
theorem sub9_1615 : sub9 [3, 3, 6] = true := by decide +kernel
theorem sub9_1616 : sub9 [3, 3, 7] = true := by decide +kernel
theorem sub9_1617 : sub9 [3, 3, 8] = true := by decide +kernel
theorem sub9_1618 : sub9 [3, 3, 9] = true := by decide +kernel
theorem sub9_1619 : sub9 [3, 3, 10] = true := by decide +kernel
theorem sub9_1620 : sub9 [3, 4, -6] = true := by decide +kernel
theorem sub9_1621 : sub9 [3, 4, -5] = true := by decide +kernel
theorem sub9_1622 : sub9 [3, 4, -4] = true := by decide +kernel
theorem sub9_1623 : sub9 [3, 4, -3] = true := by decide +kernel
theorem sub9_1624 : sub9 [3, 4, -2] = true := by decide +kernel
theorem sub9_1625 : sub9 [3, 4, -1] = true := by decide +kernel
theorem sub9_1626 : sub9 [3, 4, 0] = true := by decide +kernel
theorem sub9_1627 : sub9 [3, 4, 1] = true := by decide +kernel
theorem sub9_1628 : sub9 [3, 4, 2] = true := by decide +kernel
theorem sub9_1629 : sub9 [3, 4, 3] = true := by decide +kernel
theorem sub9_1630 : sub9 [3, 4, 4] = true := by decide +kernel
theorem sub9_1631 : sub9 [3, 4, 5] = true := by decide +kernel
theorem sb9_50 : ∀ q ∈ blk9_50, sub9 q = true := by
  unfold blk9_50
  exact List.forall_mem_cons.2 ⟨sub9_1600, List.forall_mem_cons.2 ⟨sub9_1601, List.forall_mem_cons.2 ⟨sub9_1602, List.forall_mem_cons.2 ⟨sub9_1603, List.forall_mem_cons.2 ⟨sub9_1604, List.forall_mem_cons.2 ⟨sub9_1605, List.forall_mem_cons.2 ⟨sub9_1606, List.forall_mem_cons.2 ⟨sub9_1607, List.forall_mem_cons.2 ⟨sub9_1608, List.forall_mem_cons.2 ⟨sub9_1609, List.forall_mem_cons.2 ⟨sub9_1610, List.forall_mem_cons.2 ⟨sub9_1611, List.forall_mem_cons.2 ⟨sub9_1612, List.forall_mem_cons.2 ⟨sub9_1613, List.forall_mem_cons.2 ⟨sub9_1614, List.forall_mem_cons.2 ⟨sub9_1615, List.forall_mem_cons.2 ⟨sub9_1616, List.forall_mem_cons.2 ⟨sub9_1617, List.forall_mem_cons.2 ⟨sub9_1618, List.forall_mem_cons.2 ⟨sub9_1619, List.forall_mem_cons.2 ⟨sub9_1620, List.forall_mem_cons.2 ⟨sub9_1621, List.forall_mem_cons.2 ⟨sub9_1622, List.forall_mem_cons.2 ⟨sub9_1623, List.forall_mem_cons.2 ⟨sub9_1624, List.forall_mem_cons.2 ⟨sub9_1625, List.forall_mem_cons.2 ⟨sub9_1626, List.forall_mem_cons.2 ⟨sub9_1627, List.forall_mem_cons.2 ⟨sub9_1628, List.forall_mem_cons.2 ⟨sub9_1629, List.forall_mem_cons.2 ⟨sub9_1630, List.forall_mem_cons.2 ⟨sub9_1631, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_1632 : sub9 [3, 4, 6] = true := by decide +kernel
theorem sub9_1633 : sub9 [3, 4, 7] = true := by decide +kernel
theorem sub9_1634 : sub9 [3, 4, 8] = true := by decide +kernel
theorem sub9_1635 : sub9 [3, 4, 9] = true := by decide +kernel
theorem sub9_1636 : sub9 [3, 4, 10] = true := by decide +kernel
theorem sub9_1637 : sub9 [3, 5, -5] = true := by decide +kernel
theorem sub9_1638 : sub9 [3, 5, -4] = true := by decide +kernel
theorem sub9_1639 : sub9 [3, 5, -3] = true := by decide +kernel
theorem sub9_1640 : sub9 [3, 5, -2] = true := by decide +kernel
theorem sub9_1641 : sub9 [3, 5, -1] = true := by decide +kernel
theorem sub9_1642 : sub9 [3, 5, 0] = true := by decide +kernel
theorem sub9_1643 : sub9 [3, 5, 1] = true := by decide +kernel
theorem sub9_1644 : sub9 [3, 5, 2] = true := by decide +kernel
theorem sub9_1645 : sub9 [3, 5, 3] = true := by decide +kernel
theorem sub9_1646 : sub9 [3, 5, 4] = true := by decide +kernel
theorem sub9_1647 : sub9 [3, 5, 5] = true := by decide +kernel
theorem sub9_1648 : sub9 [3, 5, 6] = true := by decide +kernel
theorem sub9_1649 : sub9 [3, 5, 7] = true := by decide +kernel
theorem sub9_1650 : sub9 [3, 5, 8] = true := by decide +kernel
theorem sub9_1651 : sub9 [3, 5, 9] = true := by decide +kernel
theorem sub9_1652 : sub9 [3, 5, 10] = true := by decide +kernel
theorem sub9_1653 : sub9 [3, 6] = true := by decide +kernel
theorem sub9_1654 : sub9 [3, 7] = true := by decide +kernel
theorem sub9_1655 : sub9 [3, 8] = true := by decide +kernel
theorem sub9_1656 : sub9 [4, -6] = true := by decide +kernel
theorem sub9_1657 : sub9 [4, -5] = true := by decide +kernel
theorem sub9_1658 : sub9 [4, -4] = true := by decide +kernel
theorem sub9_1659 : sub9 [4, -3] = true := by decide +kernel
theorem sub9_1660 : sub9 [4, -2, -8] = true := by decide +kernel
theorem sub9_1661 : sub9 [4, -2, -7] = true := by decide +kernel
theorem sub9_1662 : sub9 [4, -2, -6] = true := by decide +kernel
theorem sub9_1663 : sub9 [4, -2, -5] = true := by decide +kernel
theorem sb9_51 : ∀ q ∈ blk9_51, sub9 q = true := by
  unfold blk9_51
  exact List.forall_mem_cons.2 ⟨sub9_1632, List.forall_mem_cons.2 ⟨sub9_1633, List.forall_mem_cons.2 ⟨sub9_1634, List.forall_mem_cons.2 ⟨sub9_1635, List.forall_mem_cons.2 ⟨sub9_1636, List.forall_mem_cons.2 ⟨sub9_1637, List.forall_mem_cons.2 ⟨sub9_1638, List.forall_mem_cons.2 ⟨sub9_1639, List.forall_mem_cons.2 ⟨sub9_1640, List.forall_mem_cons.2 ⟨sub9_1641, List.forall_mem_cons.2 ⟨sub9_1642, List.forall_mem_cons.2 ⟨sub9_1643, List.forall_mem_cons.2 ⟨sub9_1644, List.forall_mem_cons.2 ⟨sub9_1645, List.forall_mem_cons.2 ⟨sub9_1646, List.forall_mem_cons.2 ⟨sub9_1647, List.forall_mem_cons.2 ⟨sub9_1648, List.forall_mem_cons.2 ⟨sub9_1649, List.forall_mem_cons.2 ⟨sub9_1650, List.forall_mem_cons.2 ⟨sub9_1651, List.forall_mem_cons.2 ⟨sub9_1652, List.forall_mem_cons.2 ⟨sub9_1653, List.forall_mem_cons.2 ⟨sub9_1654, List.forall_mem_cons.2 ⟨sub9_1655, List.forall_mem_cons.2 ⟨sub9_1656, List.forall_mem_cons.2 ⟨sub9_1657, List.forall_mem_cons.2 ⟨sub9_1658, List.forall_mem_cons.2 ⟨sub9_1659, List.forall_mem_cons.2 ⟨sub9_1660, List.forall_mem_cons.2 ⟨sub9_1661, List.forall_mem_cons.2 ⟨sub9_1662, List.forall_mem_cons.2 ⟨sub9_1663, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_1664 : sub9 [4, -2, -4] = true := by decide +kernel
theorem sub9_1665 : sub9 [4, -2, -3] = true := by decide +kernel
theorem sub9_1666 : sub9 [4, -2, -2] = true := by decide +kernel
theorem sub9_1667 : sub9 [4, -2, -1] = true := by decide +kernel
theorem sub9_1668 : sub9 [4, -2, 0] = true := by decide +kernel
theorem sub9_1669 : sub9 [4, -2, 1] = true := by decide +kernel
theorem sub9_1670 : sub9 [4, -2, 2] = true := by decide +kernel
theorem sub9_1671 : sub9 [4, -2, 3] = true := by decide +kernel
theorem sub9_1672 : sub9 [4, -2, 4] = true := by decide +kernel
theorem sub9_1673 : sub9 [4, -2, 5] = true := by decide +kernel
theorem sub9_1674 : sub9 [4, -2, 6] = true := by decide +kernel
theorem sub9_1675 : sub9 [4, -2, 7] = true := by decide +kernel
theorem sub9_1676 : sub9 [4, -1, -8] = true := by decide +kernel
theorem sub9_1677 : sub9 [4, -1, -7] = true := by decide +kernel
theorem sub9_1678 : sub9 [4, -1, -6] = true := by decide +kernel
theorem sub9_1679 : sub9 [4, -1, -5] = true := by decide +kernel
theorem sub9_1680 : sub9 [4, -1, -4] = true := by decide +kernel
theorem sub9_1681 : sub9 [4, -1, -3] = true := by decide +kernel
theorem sub9_1682 : sub9 [4, -1, -2] = true := by decide +kernel
theorem sub9_1683 : sub9 [4, -1, -1] = true := by decide +kernel
theorem sub9_1684 : sub9 [4, -1, 0] = true := by decide +kernel
theorem sub9_1685 : sub9 [4, -1, 1] = true := by decide +kernel
theorem sub9_1686 : sub9 [4, -1, 2] = true := by decide +kernel
theorem sub9_1687 : sub9 [4, -1, 3] = true := by decide +kernel
theorem sub9_1688 : sub9 [4, -1, 4] = true := by decide +kernel
theorem sub9_1689 : sub9 [4, -1, 5] = true := by decide +kernel
theorem sub9_1690 : sub9 [4, -1, 6] = true := by decide +kernel
theorem sub9_1691 : sub9 [4, -1, 7] = true := by decide +kernel
theorem sub9_1692 : sub9 [4, -1, 8] = true := by decide +kernel
theorem sub9_1693 : sub9 [4, 0, -8] = true := by decide +kernel
theorem sub9_1694 : sub9 [4, 0, -7] = true := by decide +kernel
theorem sub9_1695 : sub9 [4, 0, -6] = true := by decide +kernel
theorem sb9_52 : ∀ q ∈ blk9_52, sub9 q = true := by
  unfold blk9_52
  exact List.forall_mem_cons.2 ⟨sub9_1664, List.forall_mem_cons.2 ⟨sub9_1665, List.forall_mem_cons.2 ⟨sub9_1666, List.forall_mem_cons.2 ⟨sub9_1667, List.forall_mem_cons.2 ⟨sub9_1668, List.forall_mem_cons.2 ⟨sub9_1669, List.forall_mem_cons.2 ⟨sub9_1670, List.forall_mem_cons.2 ⟨sub9_1671, List.forall_mem_cons.2 ⟨sub9_1672, List.forall_mem_cons.2 ⟨sub9_1673, List.forall_mem_cons.2 ⟨sub9_1674, List.forall_mem_cons.2 ⟨sub9_1675, List.forall_mem_cons.2 ⟨sub9_1676, List.forall_mem_cons.2 ⟨sub9_1677, List.forall_mem_cons.2 ⟨sub9_1678, List.forall_mem_cons.2 ⟨sub9_1679, List.forall_mem_cons.2 ⟨sub9_1680, List.forall_mem_cons.2 ⟨sub9_1681, List.forall_mem_cons.2 ⟨sub9_1682, List.forall_mem_cons.2 ⟨sub9_1683, List.forall_mem_cons.2 ⟨sub9_1684, List.forall_mem_cons.2 ⟨sub9_1685, List.forall_mem_cons.2 ⟨sub9_1686, List.forall_mem_cons.2 ⟨sub9_1687, List.forall_mem_cons.2 ⟨sub9_1688, List.forall_mem_cons.2 ⟨sub9_1689, List.forall_mem_cons.2 ⟨sub9_1690, List.forall_mem_cons.2 ⟨sub9_1691, List.forall_mem_cons.2 ⟨sub9_1692, List.forall_mem_cons.2 ⟨sub9_1693, List.forall_mem_cons.2 ⟨sub9_1694, List.forall_mem_cons.2 ⟨sub9_1695, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_1696 : sub9 [4, 0, -5] = true := by decide +kernel
theorem sub9_1697 : sub9 [4, 0, -4] = true := by decide +kernel
theorem sub9_1698 : sub9 [4, 0, -3] = true := by decide +kernel
theorem sub9_1699 : sub9 [4, 0, -2] = true := by decide +kernel
theorem sub9_1700 : sub9 [4, 0, -1] = true := by decide +kernel
theorem sub9_1701 : sub9 [4, 0, 0] = true := by decide +kernel
theorem sub9_1702 : sub9 [4, 0, 1] = true := by decide +kernel
theorem sub9_1703 : sub9 [4, 0, 2] = true := by decide +kernel
theorem sub9_1704 : sub9 [4, 0, 3] = true := by decide +kernel
theorem sub9_1705 : sub9 [4, 0, 4] = true := by decide +kernel
theorem sub9_1706 : sub9 [4, 0, 5] = true := by decide +kernel
theorem sub9_1707 : sub9 [4, 0, 6] = true := by decide +kernel
theorem sub9_1708 : sub9 [4, 0, 7] = true := by decide +kernel
theorem sub9_1709 : sub9 [4, 0, 8] = true := by decide +kernel
theorem sub9_1710 : sub9 [4, 0, 9] = true := by decide +kernel
theorem sub9_1711 : sub9 [4, 1, -7] = true := by decide +kernel
theorem sub9_1712 : sub9 [4, 1, -6] = true := by decide +kernel
theorem sub9_1713 : sub9 [4, 1, -5] = true := by decide +kernel
theorem sub9_1714 : sub9 [4, 1, -4] = true := by decide +kernel
theorem sub9_1715 : sub9 [4, 1, -3] = true := by decide +kernel
theorem sub9_1716 : sub9 [4, 1, -2] = true := by decide +kernel
theorem sub9_1717 : sub9 [4, 1, -1] = true := by decide +kernel
theorem sub9_1718 : sub9 [4, 1, 0] = true := by decide +kernel
theorem sub9_1719 : sub9 [4, 1, 1] = true := by decide +kernel
theorem sub9_1720 : sub9 [4, 1, 2] = true := by decide +kernel
theorem sub9_1721 : sub9 [4, 1, 3] = true := by decide +kernel
theorem sub9_1722 : sub9 [4, 1, 4] = true := by decide +kernel
theorem sub9_1723 : sub9 [4, 1, 5] = true := by decide +kernel
theorem sub9_1724 : sub9 [4, 1, 6] = true := by decide +kernel
theorem sub9_1725 : sub9 [4, 1, 7] = true := by decide +kernel
theorem sub9_1726 : sub9 [4, 1, 8] = true := by decide +kernel
theorem sub9_1727 : sub9 [4, 1, 9] = true := by decide +kernel
theorem sb9_53 : ∀ q ∈ blk9_53, sub9 q = true := by
  unfold blk9_53
  exact List.forall_mem_cons.2 ⟨sub9_1696, List.forall_mem_cons.2 ⟨sub9_1697, List.forall_mem_cons.2 ⟨sub9_1698, List.forall_mem_cons.2 ⟨sub9_1699, List.forall_mem_cons.2 ⟨sub9_1700, List.forall_mem_cons.2 ⟨sub9_1701, List.forall_mem_cons.2 ⟨sub9_1702, List.forall_mem_cons.2 ⟨sub9_1703, List.forall_mem_cons.2 ⟨sub9_1704, List.forall_mem_cons.2 ⟨sub9_1705, List.forall_mem_cons.2 ⟨sub9_1706, List.forall_mem_cons.2 ⟨sub9_1707, List.forall_mem_cons.2 ⟨sub9_1708, List.forall_mem_cons.2 ⟨sub9_1709, List.forall_mem_cons.2 ⟨sub9_1710, List.forall_mem_cons.2 ⟨sub9_1711, List.forall_mem_cons.2 ⟨sub9_1712, List.forall_mem_cons.2 ⟨sub9_1713, List.forall_mem_cons.2 ⟨sub9_1714, List.forall_mem_cons.2 ⟨sub9_1715, List.forall_mem_cons.2 ⟨sub9_1716, List.forall_mem_cons.2 ⟨sub9_1717, List.forall_mem_cons.2 ⟨sub9_1718, List.forall_mem_cons.2 ⟨sub9_1719, List.forall_mem_cons.2 ⟨sub9_1720, List.forall_mem_cons.2 ⟨sub9_1721, List.forall_mem_cons.2 ⟨sub9_1722, List.forall_mem_cons.2 ⟨sub9_1723, List.forall_mem_cons.2 ⟨sub9_1724, List.forall_mem_cons.2 ⟨sub9_1725, List.forall_mem_cons.2 ⟨sub9_1726, List.forall_mem_cons.2 ⟨sub9_1727, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_1728 : sub9 [4, 2, -7] = true := by decide +kernel
theorem sub9_1729 : sub9 [4, 2, -6] = true := by decide +kernel
theorem sub9_1730 : sub9 [4, 2, -5] = true := by decide +kernel
theorem sub9_1731 : sub9 [4, 2, -4] = true := by decide +kernel
theorem sub9_1732 : sub9 [4, 2, -3] = true := by decide +kernel
theorem sub9_1733 : sub9 [4, 2, -2] = true := by decide +kernel
theorem sub9_1734 : sub9 [4, 2, -1] = true := by decide +kernel
theorem sub9_1735 : sub9 [4, 2, 0] = true := by decide +kernel
theorem sub9_1736 : sub9 [4, 2, 1] = true := by decide +kernel
theorem sub9_1737 : sub9 [4, 2, 2] = true := by decide +kernel
theorem sub9_1738 : sub9 [4, 2, 3] = true := by decide +kernel
theorem sub9_1739 : sub9 [4, 2, 4] = true := by decide +kernel
theorem sub9_1740 : sub9 [4, 2, 5] = true := by decide +kernel
theorem sub9_1741 : sub9 [4, 2, 6] = true := by decide +kernel
theorem sub9_1742 : sub9 [4, 2, 7] = true := by decide +kernel
theorem sub9_1743 : sub9 [4, 2, 8] = true := by decide +kernel
theorem sub9_1744 : sub9 [4, 2, 9] = true := by decide +kernel
theorem sub9_1745 : sub9 [4, 2, 10] = true := by decide +kernel
theorem sub9_1746 : sub9 [4, 3, -6] = true := by decide +kernel
theorem sub9_1747 : sub9 [4, 3, -5] = true := by decide +kernel
theorem sub9_1748 : sub9 [4, 3, -4] = true := by decide +kernel
theorem sub9_1749 : sub9 [4, 3, -3] = true := by decide +kernel
theorem sub9_1750 : sub9 [4, 3, -2] = true := by decide +kernel
theorem sub9_1751 : sub9 [4, 3, -1] = true := by decide +kernel
theorem sub9_1752 : sub9 [4, 3, 0] = true := by decide +kernel
theorem sub9_1753 : sub9 [4, 3, 1] = true := by decide +kernel
theorem sub9_1754 : sub9 [4, 3, 2] = true := by decide +kernel
theorem sub9_1755 : sub9 [4, 3, 3] = true := by decide +kernel
theorem sub9_1756 : sub9 [4, 3, 4] = true := by decide +kernel
theorem sub9_1757 : sub9 [4, 3, 5] = true := by decide +kernel
theorem sub9_1758 : sub9 [4, 3, 6] = true := by decide +kernel
theorem sub9_1759 : sub9 [4, 3, 7] = true := by decide +kernel
theorem sb9_54 : ∀ q ∈ blk9_54, sub9 q = true := by
  unfold blk9_54
  exact List.forall_mem_cons.2 ⟨sub9_1728, List.forall_mem_cons.2 ⟨sub9_1729, List.forall_mem_cons.2 ⟨sub9_1730, List.forall_mem_cons.2 ⟨sub9_1731, List.forall_mem_cons.2 ⟨sub9_1732, List.forall_mem_cons.2 ⟨sub9_1733, List.forall_mem_cons.2 ⟨sub9_1734, List.forall_mem_cons.2 ⟨sub9_1735, List.forall_mem_cons.2 ⟨sub9_1736, List.forall_mem_cons.2 ⟨sub9_1737, List.forall_mem_cons.2 ⟨sub9_1738, List.forall_mem_cons.2 ⟨sub9_1739, List.forall_mem_cons.2 ⟨sub9_1740, List.forall_mem_cons.2 ⟨sub9_1741, List.forall_mem_cons.2 ⟨sub9_1742, List.forall_mem_cons.2 ⟨sub9_1743, List.forall_mem_cons.2 ⟨sub9_1744, List.forall_mem_cons.2 ⟨sub9_1745, List.forall_mem_cons.2 ⟨sub9_1746, List.forall_mem_cons.2 ⟨sub9_1747, List.forall_mem_cons.2 ⟨sub9_1748, List.forall_mem_cons.2 ⟨sub9_1749, List.forall_mem_cons.2 ⟨sub9_1750, List.forall_mem_cons.2 ⟨sub9_1751, List.forall_mem_cons.2 ⟨sub9_1752, List.forall_mem_cons.2 ⟨sub9_1753, List.forall_mem_cons.2 ⟨sub9_1754, List.forall_mem_cons.2 ⟨sub9_1755, List.forall_mem_cons.2 ⟨sub9_1756, List.forall_mem_cons.2 ⟨sub9_1757, List.forall_mem_cons.2 ⟨sub9_1758, List.forall_mem_cons.2 ⟨sub9_1759, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_1760 : sub9 [4, 3, 8] = true := by decide +kernel
theorem sub9_1761 : sub9 [4, 3, 9] = true := by decide +kernel
theorem sub9_1762 : sub9 [4, 3, 10] = true := by decide +kernel
theorem sub9_1763 : sub9 [4, 4, -5] = true := by decide +kernel
theorem sub9_1764 : sub9 [4, 4, -4] = true := by decide +kernel
theorem sub9_1765 : sub9 [4, 4, -3] = true := by decide +kernel
theorem sub9_1766 : sub9 [4, 4, -2] = true := by decide +kernel
theorem sub9_1767 : sub9 [4, 4, -1] = true := by decide +kernel
theorem sub9_1768 : sub9 [4, 4, 0] = true := by decide +kernel
theorem sub9_1769 : sub9 [4, 4, 1] = true := by decide +kernel
theorem sub9_1770 : sub9 [4, 4, 2] = true := by decide +kernel
theorem sub9_1771 : sub9 [4, 4, 3] = true := by decide +kernel
theorem sub9_1772 : sub9 [4, 4, 4] = true := by decide +kernel
theorem sub9_1773 : sub9 [4, 4, 5] = true := by decide +kernel
theorem sub9_1774 : sub9 [4, 4, 6] = true := by decide +kernel
theorem sub9_1775 : sub9 [4, 4, 7] = true := by decide +kernel
theorem sub9_1776 : sub9 [4, 4, 8] = true := by decide +kernel
theorem sub9_1777 : sub9 [4, 4, 9] = true := by decide +kernel
theorem sub9_1778 : sub9 [4, 4, 10] = true := by decide +kernel
theorem sub9_1779 : sub9 [4, 5, -4] = true := by decide +kernel
theorem sub9_1780 : sub9 [4, 5, -3] = true := by decide +kernel
theorem sub9_1781 : sub9 [4, 5, -2] = true := by decide +kernel
theorem sub9_1782 : sub9 [4, 5, -1] = true := by decide +kernel
theorem sub9_1783 : sub9 [4, 5, 0] = true := by decide +kernel
theorem sub9_1784 : sub9 [4, 5, 1] = true := by decide +kernel
theorem sub9_1785 : sub9 [4, 5, 2] = true := by decide +kernel
theorem sub9_1786 : sub9 [4, 5, 3] = true := by decide +kernel
theorem sub9_1787 : sub9 [4, 5, 4] = true := by decide +kernel
theorem sub9_1788 : sub9 [4, 5, 5] = true := by decide +kernel
theorem sub9_1789 : sub9 [4, 5, 6] = true := by decide +kernel
theorem sub9_1790 : sub9 [4, 5, 7] = true := by decide +kernel
theorem sub9_1791 : sub9 [4, 5, 8] = true := by decide +kernel
theorem sb9_55 : ∀ q ∈ blk9_55, sub9 q = true := by
  unfold blk9_55
  exact List.forall_mem_cons.2 ⟨sub9_1760, List.forall_mem_cons.2 ⟨sub9_1761, List.forall_mem_cons.2 ⟨sub9_1762, List.forall_mem_cons.2 ⟨sub9_1763, List.forall_mem_cons.2 ⟨sub9_1764, List.forall_mem_cons.2 ⟨sub9_1765, List.forall_mem_cons.2 ⟨sub9_1766, List.forall_mem_cons.2 ⟨sub9_1767, List.forall_mem_cons.2 ⟨sub9_1768, List.forall_mem_cons.2 ⟨sub9_1769, List.forall_mem_cons.2 ⟨sub9_1770, List.forall_mem_cons.2 ⟨sub9_1771, List.forall_mem_cons.2 ⟨sub9_1772, List.forall_mem_cons.2 ⟨sub9_1773, List.forall_mem_cons.2 ⟨sub9_1774, List.forall_mem_cons.2 ⟨sub9_1775, List.forall_mem_cons.2 ⟨sub9_1776, List.forall_mem_cons.2 ⟨sub9_1777, List.forall_mem_cons.2 ⟨sub9_1778, List.forall_mem_cons.2 ⟨sub9_1779, List.forall_mem_cons.2 ⟨sub9_1780, List.forall_mem_cons.2 ⟨sub9_1781, List.forall_mem_cons.2 ⟨sub9_1782, List.forall_mem_cons.2 ⟨sub9_1783, List.forall_mem_cons.2 ⟨sub9_1784, List.forall_mem_cons.2 ⟨sub9_1785, List.forall_mem_cons.2 ⟨sub9_1786, List.forall_mem_cons.2 ⟨sub9_1787, List.forall_mem_cons.2 ⟨sub9_1788, List.forall_mem_cons.2 ⟨sub9_1789, List.forall_mem_cons.2 ⟨sub9_1790, List.forall_mem_cons.2 ⟨sub9_1791, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_1792 : sub9 [4, 5, 9] = true := by decide +kernel
theorem sub9_1793 : sub9 [4, 5, 10] = true := by decide +kernel
theorem sub9_1794 : sub9 [4, 6] = true := by decide +kernel
theorem sub9_1795 : sub9 [4, 7] = true := by decide +kernel
theorem sub9_1796 : sub9 [4, 8] = true := by decide +kernel
theorem sub9_1797 : sub9 [5, -4] = true := by decide +kernel
theorem sub9_1798 : sub9 [5, -3] = true := by decide +kernel
theorem sub9_1799 : sub9 [5, -2] = true := by decide +kernel
theorem sub9_1800 : sub9 [5, -1] = true := by decide +kernel
theorem sub9_1801 : sub9 [5, 0, -6] = true := by decide +kernel
theorem sub9_1802 : sub9 [5, 0, -5] = true := by decide +kernel
theorem sub9_1803 : sub9 [5, 0, -4] = true := by decide +kernel
theorem sub9_1804 : sub9 [5, 0, -3] = true := by decide +kernel
theorem sub9_1805 : sub9 [5, 0, -2] = true := by decide +kernel
theorem sub9_1806 : sub9 [5, 0, -1] = true := by decide +kernel
theorem sub9_1807 : sub9 [5, 0, 0] = true := by decide +kernel
theorem sub9_1808 : sub9 [5, 0, 1] = true := by decide +kernel
theorem sub9_1809 : sub9 [5, 0, 2] = true := by decide +kernel
theorem sub9_1810 : sub9 [5, 0, 3] = true := by decide +kernel
theorem sub9_1811 : sub9 [5, 0, 4] = true := by decide +kernel
theorem sub9_1812 : sub9 [5, 0, 5] = true := by decide +kernel
theorem sub9_1813 : sub9 [5, 0, 6] = true := by decide +kernel
theorem sub9_1814 : sub9 [5, 0, 7] = true := by decide +kernel
theorem sub9_1815 : sub9 [5, 0, 8] = true := by decide +kernel
theorem sub9_1816 : sub9 [5, 1, -6] = true := by decide +kernel
theorem sub9_1817 : sub9 [5, 1, -5] = true := by decide +kernel
theorem sub9_1818 : sub9 [5, 1, -4] = true := by decide +kernel
theorem sub9_1819 : sub9 [5, 1, -3] = true := by decide +kernel
theorem sub9_1820 : sub9 [5, 1, -2] = true := by decide +kernel
theorem sub9_1821 : sub9 [5, 1, -1] = true := by decide +kernel
theorem sub9_1822 : sub9 [5, 1, 0] = true := by decide +kernel
theorem sub9_1823 : sub9 [5, 1, 1] = true := by decide +kernel
theorem sb9_56 : ∀ q ∈ blk9_56, sub9 q = true := by
  unfold blk9_56
  exact List.forall_mem_cons.2 ⟨sub9_1792, List.forall_mem_cons.2 ⟨sub9_1793, List.forall_mem_cons.2 ⟨sub9_1794, List.forall_mem_cons.2 ⟨sub9_1795, List.forall_mem_cons.2 ⟨sub9_1796, List.forall_mem_cons.2 ⟨sub9_1797, List.forall_mem_cons.2 ⟨sub9_1798, List.forall_mem_cons.2 ⟨sub9_1799, List.forall_mem_cons.2 ⟨sub9_1800, List.forall_mem_cons.2 ⟨sub9_1801, List.forall_mem_cons.2 ⟨sub9_1802, List.forall_mem_cons.2 ⟨sub9_1803, List.forall_mem_cons.2 ⟨sub9_1804, List.forall_mem_cons.2 ⟨sub9_1805, List.forall_mem_cons.2 ⟨sub9_1806, List.forall_mem_cons.2 ⟨sub9_1807, List.forall_mem_cons.2 ⟨sub9_1808, List.forall_mem_cons.2 ⟨sub9_1809, List.forall_mem_cons.2 ⟨sub9_1810, List.forall_mem_cons.2 ⟨sub9_1811, List.forall_mem_cons.2 ⟨sub9_1812, List.forall_mem_cons.2 ⟨sub9_1813, List.forall_mem_cons.2 ⟨sub9_1814, List.forall_mem_cons.2 ⟨sub9_1815, List.forall_mem_cons.2 ⟨sub9_1816, List.forall_mem_cons.2 ⟨sub9_1817, List.forall_mem_cons.2 ⟨sub9_1818, List.forall_mem_cons.2 ⟨sub9_1819, List.forall_mem_cons.2 ⟨sub9_1820, List.forall_mem_cons.2 ⟨sub9_1821, List.forall_mem_cons.2 ⟨sub9_1822, List.forall_mem_cons.2 ⟨sub9_1823, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_1824 : sub9 [5, 1, 2] = true := by decide +kernel
theorem sub9_1825 : sub9 [5, 1, 3] = true := by decide +kernel
theorem sub9_1826 : sub9 [5, 1, 4] = true := by decide +kernel
theorem sub9_1827 : sub9 [5, 1, 5] = true := by decide +kernel
theorem sub9_1828 : sub9 [5, 1, 6] = true := by decide +kernel
theorem sub9_1829 : sub9 [5, 1, 7] = true := by decide +kernel
theorem sub9_1830 : sub9 [5, 1, 8] = true := by decide +kernel
theorem sub9_1831 : sub9 [5, 2, -6] = true := by decide +kernel
theorem sub9_1832 : sub9 [5, 2, -5] = true := by decide +kernel
theorem sub9_1833 : sub9 [5, 2, -4] = true := by decide +kernel
theorem sub9_1834 : sub9 [5, 2, -3] = true := by decide +kernel
theorem sub9_1835 : sub9 [5, 2, -2] = true := by decide +kernel
theorem sub9_1836 : sub9 [5, 2, -1] = true := by decide +kernel
theorem sub9_1837 : sub9 [5, 2, 0] = true := by decide +kernel
theorem sub9_1838 : sub9 [5, 2, 1] = true := by decide +kernel
theorem sub9_1839 : sub9 [5, 2, 2] = true := by decide +kernel
theorem sub9_1840 : sub9 [5, 2, 3] = true := by decide +kernel
theorem sub9_1841 : sub9 [5, 2, 4] = true := by decide +kernel
theorem sub9_1842 : sub9 [5, 2, 5] = true := by decide +kernel
theorem sub9_1843 : sub9 [5, 2, 6] = true := by decide +kernel
theorem sub9_1844 : sub9 [5, 2, 7] = true := by decide +kernel
theorem sub9_1845 : sub9 [5, 2, 8] = true := by decide +kernel
theorem sub9_1846 : sub9 [5, 2, 9] = true := by decide +kernel
theorem sub9_1847 : sub9 [5, 3, -5] = true := by decide +kernel
theorem sub9_1848 : sub9 [5, 3, -4] = true := by decide +kernel
theorem sub9_1849 : sub9 [5, 3, -3] = true := by decide +kernel
theorem sub9_1850 : sub9 [5, 3, -2] = true := by decide +kernel
theorem sub9_1851 : sub9 [5, 3, -1] = true := by decide +kernel
theorem sub9_1852 : sub9 [5, 3, 0] = true := by decide +kernel
theorem sub9_1853 : sub9 [5, 3, 1] = true := by decide +kernel
theorem sub9_1854 : sub9 [5, 3, 2] = true := by decide +kernel
theorem sub9_1855 : sub9 [5, 3, 3] = true := by decide +kernel
theorem sb9_57 : ∀ q ∈ blk9_57, sub9 q = true := by
  unfold blk9_57
  exact List.forall_mem_cons.2 ⟨sub9_1824, List.forall_mem_cons.2 ⟨sub9_1825, List.forall_mem_cons.2 ⟨sub9_1826, List.forall_mem_cons.2 ⟨sub9_1827, List.forall_mem_cons.2 ⟨sub9_1828, List.forall_mem_cons.2 ⟨sub9_1829, List.forall_mem_cons.2 ⟨sub9_1830, List.forall_mem_cons.2 ⟨sub9_1831, List.forall_mem_cons.2 ⟨sub9_1832, List.forall_mem_cons.2 ⟨sub9_1833, List.forall_mem_cons.2 ⟨sub9_1834, List.forall_mem_cons.2 ⟨sub9_1835, List.forall_mem_cons.2 ⟨sub9_1836, List.forall_mem_cons.2 ⟨sub9_1837, List.forall_mem_cons.2 ⟨sub9_1838, List.forall_mem_cons.2 ⟨sub9_1839, List.forall_mem_cons.2 ⟨sub9_1840, List.forall_mem_cons.2 ⟨sub9_1841, List.forall_mem_cons.2 ⟨sub9_1842, List.forall_mem_cons.2 ⟨sub9_1843, List.forall_mem_cons.2 ⟨sub9_1844, List.forall_mem_cons.2 ⟨sub9_1845, List.forall_mem_cons.2 ⟨sub9_1846, List.forall_mem_cons.2 ⟨sub9_1847, List.forall_mem_cons.2 ⟨sub9_1848, List.forall_mem_cons.2 ⟨sub9_1849, List.forall_mem_cons.2 ⟨sub9_1850, List.forall_mem_cons.2 ⟨sub9_1851, List.forall_mem_cons.2 ⟨sub9_1852, List.forall_mem_cons.2 ⟨sub9_1853, List.forall_mem_cons.2 ⟨sub9_1854, List.forall_mem_cons.2 ⟨sub9_1855, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_1856 : sub9 [5, 3, 4] = true := by decide +kernel
theorem sub9_1857 : sub9 [5, 3, 5] = true := by decide +kernel
theorem sub9_1858 : sub9 [5, 3, 6] = true := by decide +kernel
theorem sub9_1859 : sub9 [5, 3, 7] = true := by decide +kernel
theorem sub9_1860 : sub9 [5, 3, 8] = true := by decide +kernel
theorem sub9_1861 : sub9 [5, 3, 9] = true := by decide +kernel
theorem sub9_1862 : sub9 [5, 4] = true := by decide +kernel
theorem sub9_1863 : sub9 [5, 5] = true := by decide +kernel
theorem sub9_1864 : sub9 [5, 6] = true := by decide +kernel
theorem sub9_1865 : sub9 [5, 7] = true := by decide +kernel
theorem sub9_1866 : sub9 [6, -3] = true := by decide +kernel
theorem sub9_1867 : sub9 [6, -2] = true := by decide +kernel
theorem sub9_1868 : sub9 [6, -1] = true := by decide +kernel
theorem sub9_1869 : sub9 [6, 0] = true := by decide +kernel
theorem sub9_1870 : sub9 [6, 1] = true := by decide +kernel
theorem sub9_1871 : sub9 [6, 2] = true := by decide +kernel
theorem sub9_1872 : sub9 [6, 3] = true := by decide +kernel
theorem sub9_1873 : sub9 [6, 4] = true := by decide +kernel
theorem sub9_1874 : sub9 [6, 5] = true := by decide +kernel
theorem sub9_1875 : sub9 [6, 6] = true := by decide +kernel
theorem sub9_1876 : sub9 [7] = true := by decide +kernel
theorem sb9_58 : ∀ q ∈ blk9_58, sub9 q = true := by
  unfold blk9_58
  exact List.forall_mem_cons.2 ⟨sub9_1856, List.forall_mem_cons.2 ⟨sub9_1857, List.forall_mem_cons.2 ⟨sub9_1858, List.forall_mem_cons.2 ⟨sub9_1859, List.forall_mem_cons.2 ⟨sub9_1860, List.forall_mem_cons.2 ⟨sub9_1861, List.forall_mem_cons.2 ⟨sub9_1862, List.forall_mem_cons.2 ⟨sub9_1863, List.forall_mem_cons.2 ⟨sub9_1864, List.forall_mem_cons.2 ⟨sub9_1865, List.forall_mem_cons.2 ⟨sub9_1866, List.forall_mem_cons.2 ⟨sub9_1867, List.forall_mem_cons.2 ⟨sub9_1868, List.forall_mem_cons.2 ⟨sub9_1869, List.forall_mem_cons.2 ⟨sub9_1870, List.forall_mem_cons.2 ⟨sub9_1871, List.forall_mem_cons.2 ⟨sub9_1872, List.forall_mem_cons.2 ⟨sub9_1873, List.forall_mem_cons.2 ⟨sub9_1874, List.forall_mem_cons.2 ⟨sub9_1875, List.forall_mem_cons.2 ⟨sub9_1876, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_0 : sub10 [-7] = true := by decide +kernel
theorem sub10_1 : sub10 [-6, -3] = true := by decide +kernel
theorem sub10_2 : sub10 [-6, -2] = true := by decide +kernel
theorem sub10_3 : sub10 [-6, -1] = true := by decide +kernel
theorem sub10_4 : sub10 [-6, 0] = true := by decide +kernel
theorem sub10_5 : sub10 [-6, 1] = true := by decide +kernel
theorem sub10_6 : sub10 [-6, 2] = true := by decide +kernel
theorem sub10_7 : sub10 [-6, 3] = true := by decide +kernel
theorem sub10_8 : sub10 [-6, 4] = true := by decide +kernel
theorem sub10_9 : sub10 [-6, 5] = true := by decide +kernel
theorem sub10_10 : sub10 [-6, 6] = true := by decide +kernel
theorem sub10_11 : sub10 [-6, 7] = true := by decide +kernel
theorem sub10_12 : sub10 [-5, -4] = true := by decide +kernel
theorem sub10_13 : sub10 [-5, -3] = true := by decide +kernel
theorem sub10_14 : sub10 [-5, -2] = true := by decide +kernel
theorem sub10_15 : sub10 [-5, -1] = true := by decide +kernel
theorem sub10_16 : sub10 [-5, 0, -8] = true := by decide +kernel
theorem sub10_17 : sub10 [-5, 0, -7] = true := by decide +kernel
theorem sub10_18 : sub10 [-5, 0, -6] = true := by decide +kernel
theorem sub10_19 : sub10 [-5, 0, -5] = true := by decide +kernel
theorem sub10_20 : sub10 [-5, 0, -4] = true := by decide +kernel
theorem sub10_21 : sub10 [-5, 0, -3] = true := by decide +kernel
theorem sub10_22 : sub10 [-5, 0, -2] = true := by decide +kernel
theorem sub10_23 : sub10 [-5, 0, -1] = true := by decide +kernel
theorem sub10_24 : sub10 [-5, 0, 0] = true := by decide +kernel
theorem sub10_25 : sub10 [-5, 0, 1] = true := by decide +kernel
theorem sub10_26 : sub10 [-5, 0, 2] = true := by decide +kernel
theorem sub10_27 : sub10 [-5, 0, 3] = true := by decide +kernel
theorem sub10_28 : sub10 [-5, 0, 4] = true := by decide +kernel
theorem sub10_29 : sub10 [-5, 1, -9] = true := by decide +kernel
theorem sub10_30 : sub10 [-5, 1, -8] = true := by decide +kernel
theorem sub10_31 : sub10 [-5, 1, -7] = true := by decide +kernel
theorem sb10_0 : ∀ q ∈ blk10_0, sub10 q = true := by
  unfold blk10_0
  exact List.forall_mem_cons.2 ⟨sub10_0, List.forall_mem_cons.2 ⟨sub10_1, List.forall_mem_cons.2 ⟨sub10_2, List.forall_mem_cons.2 ⟨sub10_3, List.forall_mem_cons.2 ⟨sub10_4, List.forall_mem_cons.2 ⟨sub10_5, List.forall_mem_cons.2 ⟨sub10_6, List.forall_mem_cons.2 ⟨sub10_7, List.forall_mem_cons.2 ⟨sub10_8, List.forall_mem_cons.2 ⟨sub10_9, List.forall_mem_cons.2 ⟨sub10_10, List.forall_mem_cons.2 ⟨sub10_11, List.forall_mem_cons.2 ⟨sub10_12, List.forall_mem_cons.2 ⟨sub10_13, List.forall_mem_cons.2 ⟨sub10_14, List.forall_mem_cons.2 ⟨sub10_15, List.forall_mem_cons.2 ⟨sub10_16, List.forall_mem_cons.2 ⟨sub10_17, List.forall_mem_cons.2 ⟨sub10_18, List.forall_mem_cons.2 ⟨sub10_19, List.forall_mem_cons.2 ⟨sub10_20, List.forall_mem_cons.2 ⟨sub10_21, List.forall_mem_cons.2 ⟨sub10_22, List.forall_mem_cons.2 ⟨sub10_23, List.forall_mem_cons.2 ⟨sub10_24, List.forall_mem_cons.2 ⟨sub10_25, List.forall_mem_cons.2 ⟨sub10_26, List.forall_mem_cons.2 ⟨sub10_27, List.forall_mem_cons.2 ⟨sub10_28, List.forall_mem_cons.2 ⟨sub10_29, List.forall_mem_cons.2 ⟨sub10_30, List.forall_mem_cons.2 ⟨sub10_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_32 : sub10 [-5, 1, -6] = true := by decide +kernel
theorem sub10_33 : sub10 [-5, 1, -5] = true := by decide +kernel
theorem sub10_34 : sub10 [-5, 1, -4] = true := by decide +kernel
theorem sub10_35 : sub10 [-5, 1, -3] = true := by decide +kernel
theorem sub10_36 : sub10 [-5, 1, -2] = true := by decide +kernel
theorem sub10_37 : sub10 [-5, 1, -1] = true := by decide +kernel
theorem sub10_38 : sub10 [-5, 1, 0] = true := by decide +kernel
theorem sub10_39 : sub10 [-5, 1, 1] = true := by decide +kernel
theorem sub10_40 : sub10 [-5, 1, 2] = true := by decide +kernel
theorem sub10_41 : sub10 [-5, 1, 3] = true := by decide +kernel
theorem sub10_42 : sub10 [-5, 1, 4] = true := by decide +kernel
theorem sub10_43 : sub10 [-5, 2, -9] = true := by decide +kernel
theorem sub10_44 : sub10 [-5, 2, -8] = true := by decide +kernel
theorem sub10_45 : sub10 [-5, 2, -7] = true := by decide +kernel
theorem sub10_46 : sub10 [-5, 2, -6] = true := by decide +kernel
theorem sub10_47 : sub10 [-5, 2, -5] = true := by decide +kernel
theorem sub10_48 : sub10 [-5, 2, -4] = true := by decide +kernel
theorem sub10_49 : sub10 [-5, 2, -3] = true := by decide +kernel
theorem sub10_50 : sub10 [-5, 2, -2] = true := by decide +kernel
theorem sub10_51 : sub10 [-5, 2, -1] = true := by decide +kernel
theorem sub10_52 : sub10 [-5, 2, 0] = true := by decide +kernel
theorem sub10_53 : sub10 [-5, 2, 1] = true := by decide +kernel
theorem sub10_54 : sub10 [-5, 2, 2] = true := by decide +kernel
theorem sub10_55 : sub10 [-5, 2, 3] = true := by decide +kernel
theorem sub10_56 : sub10 [-5, 2, 4] = true := by decide +kernel
theorem sub10_57 : sub10 [-5, 3, -9] = true := by decide +kernel
theorem sub10_58 : sub10 [-5, 3, -8] = true := by decide +kernel
theorem sub10_59 : sub10 [-5, 3, -7] = true := by decide +kernel
theorem sub10_60 : sub10 [-5, 3, -6] = true := by decide +kernel
theorem sub10_61 : sub10 [-5, 3, -5] = true := by decide +kernel
theorem sub10_62 : sub10 [-5, 3, -4] = true := by decide +kernel
theorem sub10_63 : sub10 [-5, 3, -3] = true := by decide +kernel
theorem sb10_1 : ∀ q ∈ blk10_1, sub10 q = true := by
  unfold blk10_1
  exact List.forall_mem_cons.2 ⟨sub10_32, List.forall_mem_cons.2 ⟨sub10_33, List.forall_mem_cons.2 ⟨sub10_34, List.forall_mem_cons.2 ⟨sub10_35, List.forall_mem_cons.2 ⟨sub10_36, List.forall_mem_cons.2 ⟨sub10_37, List.forall_mem_cons.2 ⟨sub10_38, List.forall_mem_cons.2 ⟨sub10_39, List.forall_mem_cons.2 ⟨sub10_40, List.forall_mem_cons.2 ⟨sub10_41, List.forall_mem_cons.2 ⟨sub10_42, List.forall_mem_cons.2 ⟨sub10_43, List.forall_mem_cons.2 ⟨sub10_44, List.forall_mem_cons.2 ⟨sub10_45, List.forall_mem_cons.2 ⟨sub10_46, List.forall_mem_cons.2 ⟨sub10_47, List.forall_mem_cons.2 ⟨sub10_48, List.forall_mem_cons.2 ⟨sub10_49, List.forall_mem_cons.2 ⟨sub10_50, List.forall_mem_cons.2 ⟨sub10_51, List.forall_mem_cons.2 ⟨sub10_52, List.forall_mem_cons.2 ⟨sub10_53, List.forall_mem_cons.2 ⟨sub10_54, List.forall_mem_cons.2 ⟨sub10_55, List.forall_mem_cons.2 ⟨sub10_56, List.forall_mem_cons.2 ⟨sub10_57, List.forall_mem_cons.2 ⟨sub10_58, List.forall_mem_cons.2 ⟨sub10_59, List.forall_mem_cons.2 ⟨sub10_60, List.forall_mem_cons.2 ⟨sub10_61, List.forall_mem_cons.2 ⟨sub10_62, List.forall_mem_cons.2 ⟨sub10_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_64 : sub10 [-5, 3, -2] = true := by decide +kernel
theorem sub10_65 : sub10 [-5, 3, -1] = true := by decide +kernel
theorem sub10_66 : sub10 [-5, 3, 0] = true := by decide +kernel
theorem sub10_67 : sub10 [-5, 3, 1] = true := by decide +kernel
theorem sub10_68 : sub10 [-5, 3, 2] = true := by decide +kernel
theorem sub10_69 : sub10 [-5, 3, 3] = true := by decide +kernel
theorem sub10_70 : sub10 [-5, 3, 4] = true := by decide +kernel
theorem sub10_71 : sub10 [-5, 4, -9] = true := by decide +kernel
theorem sub10_72 : sub10 [-5, 4, -8] = true := by decide +kernel
theorem sub10_73 : sub10 [-5, 4, -7] = true := by decide +kernel
theorem sub10_74 : sub10 [-5, 4, -6] = true := by decide +kernel
theorem sub10_75 : sub10 [-5, 4, -5] = true := by decide +kernel
theorem sub10_76 : sub10 [-5, 4, -4] = true := by decide +kernel
theorem sub10_77 : sub10 [-5, 4, -3] = true := by decide +kernel
theorem sub10_78 : sub10 [-5, 4, -2] = true := by decide +kernel
theorem sub10_79 : sub10 [-5, 4, -1] = true := by decide +kernel
theorem sub10_80 : sub10 [-5, 4, 0] = true := by decide +kernel
theorem sub10_81 : sub10 [-5, 4, 1] = true := by decide +kernel
theorem sub10_82 : sub10 [-5, 4, 2] = true := by decide +kernel
theorem sub10_83 : sub10 [-5, 4, 3] = true := by decide +kernel
theorem sub10_84 : sub10 [-5, 5] = true := by decide +kernel
theorem sub10_85 : sub10 [-5, 6] = true := by decide +kernel
theorem sub10_86 : sub10 [-5, 7] = true := by decide +kernel
theorem sub10_87 : sub10 [-5, 8] = true := by decide +kernel
theorem sub10_88 : sub10 [-4, -6] = true := by decide +kernel
theorem sub10_89 : sub10 [-4, -5] = true := by decide +kernel
theorem sub10_90 : sub10 [-4, -4] = true := by decide +kernel
theorem sub10_91 : sub10 [-4, -3] = true := by decide +kernel
theorem sub10_92 : sub10 [-4, -2, -8] = true := by decide +kernel
theorem sub10_93 : sub10 [-4, -2, -7] = true := by decide +kernel
theorem sub10_94 : sub10 [-4, -2, -6] = true := by decide +kernel
theorem sub10_95 : sub10 [-4, -2, -5] = true := by decide +kernel
theorem sb10_2 : ∀ q ∈ blk10_2, sub10 q = true := by
  unfold blk10_2
  exact List.forall_mem_cons.2 ⟨sub10_64, List.forall_mem_cons.2 ⟨sub10_65, List.forall_mem_cons.2 ⟨sub10_66, List.forall_mem_cons.2 ⟨sub10_67, List.forall_mem_cons.2 ⟨sub10_68, List.forall_mem_cons.2 ⟨sub10_69, List.forall_mem_cons.2 ⟨sub10_70, List.forall_mem_cons.2 ⟨sub10_71, List.forall_mem_cons.2 ⟨sub10_72, List.forall_mem_cons.2 ⟨sub10_73, List.forall_mem_cons.2 ⟨sub10_74, List.forall_mem_cons.2 ⟨sub10_75, List.forall_mem_cons.2 ⟨sub10_76, List.forall_mem_cons.2 ⟨sub10_77, List.forall_mem_cons.2 ⟨sub10_78, List.forall_mem_cons.2 ⟨sub10_79, List.forall_mem_cons.2 ⟨sub10_80, List.forall_mem_cons.2 ⟨sub10_81, List.forall_mem_cons.2 ⟨sub10_82, List.forall_mem_cons.2 ⟨sub10_83, List.forall_mem_cons.2 ⟨sub10_84, List.forall_mem_cons.2 ⟨sub10_85, List.forall_mem_cons.2 ⟨sub10_86, List.forall_mem_cons.2 ⟨sub10_87, List.forall_mem_cons.2 ⟨sub10_88, List.forall_mem_cons.2 ⟨sub10_89, List.forall_mem_cons.2 ⟨sub10_90, List.forall_mem_cons.2 ⟨sub10_91, List.forall_mem_cons.2 ⟨sub10_92, List.forall_mem_cons.2 ⟨sub10_93, List.forall_mem_cons.2 ⟨sub10_94, List.forall_mem_cons.2 ⟨sub10_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C074
