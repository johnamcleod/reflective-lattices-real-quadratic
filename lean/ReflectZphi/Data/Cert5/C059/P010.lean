import ReflectZphi.Data.Cert5.C059.Base

namespace ReflectZphi.Data.Cert5.C059
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub5_1664 : sub5 [3, 1, -1] = true := by decide +kernel
theorem sub5_1665 : sub5 [3, 1, 0] = true := by decide +kernel
theorem sub5_1666 : sub5 [3, 1, 1] = true := by decide +kernel
theorem sub5_1667 : sub5 [3, 1, 2] = true := by decide +kernel
theorem sub5_1668 : sub5 [3, 1, 3] = true := by decide +kernel
theorem sub5_1669 : sub5 [3, 1, 4] = true := by decide +kernel
theorem sub5_1670 : sub5 [3, 1, 5] = true := by decide +kernel
theorem sub5_1671 : sub5 [3, 1, 6] = true := by decide +kernel
theorem sub5_1672 : sub5 [3, 1, 7] = true := by decide +kernel
theorem sub5_1673 : sub5 [3, 1, 8] = true := by decide +kernel
theorem sub5_1674 : sub5 [3, 1, 9] = true := by decide +kernel
theorem sub5_1675 : sub5 [3, 1, 10] = true := by decide +kernel
theorem sub5_1676 : sub5 [3, 2, -9] = true := by decide +kernel
theorem sub5_1677 : sub5 [3, 2, -8] = true := by decide +kernel
theorem sub5_1678 : sub5 [3, 2, -7] = true := by decide +kernel
theorem sub5_1679 : sub5 [3, 2, -6] = true := by decide +kernel
theorem sub5_1680 : sub5 [3, 2, -5] = true := by decide +kernel
theorem sub5_1681 : sub5 [3, 2, -4] = true := by decide +kernel
theorem sub5_1682 : sub5 [3, 2, -3] = true := by decide +kernel
theorem sub5_1683 : sub5 [3, 2, -2] = true := by decide +kernel
theorem sub5_1684 : sub5 [3, 2, -1] = true := by decide +kernel
theorem sub5_1685 : sub5 [3, 2, 0] = true := by decide +kernel
theorem sub5_1686 : sub5 [3, 2, 1] = true := by decide +kernel
theorem sub5_1687 : sub5 [3, 2, 2] = true := by decide +kernel
theorem sub5_1688 : sub5 [3, 2, 3] = true := by decide +kernel
theorem sub5_1689 : sub5 [3, 2, 4] = true := by decide +kernel
theorem sub5_1690 : sub5 [3, 2, 5] = true := by decide +kernel
theorem sub5_1691 : sub5 [3, 2, 6] = true := by decide +kernel
theorem sub5_1692 : sub5 [3, 2, 7] = true := by decide +kernel
theorem sub5_1693 : sub5 [3, 2, 8] = true := by decide +kernel
theorem sub5_1694 : sub5 [3, 2, 9] = true := by decide +kernel
theorem sub5_1695 : sub5 [3, 3, -8] = true := by decide +kernel
theorem sb5_52 : ∀ q ∈ blk5_52, sub5 q = true := by
  unfold blk5_52
  exact List.forall_mem_cons.2 ⟨sub5_1664, List.forall_mem_cons.2 ⟨sub5_1665, List.forall_mem_cons.2 ⟨sub5_1666, List.forall_mem_cons.2 ⟨sub5_1667, List.forall_mem_cons.2 ⟨sub5_1668, List.forall_mem_cons.2 ⟨sub5_1669, List.forall_mem_cons.2 ⟨sub5_1670, List.forall_mem_cons.2 ⟨sub5_1671, List.forall_mem_cons.2 ⟨sub5_1672, List.forall_mem_cons.2 ⟨sub5_1673, List.forall_mem_cons.2 ⟨sub5_1674, List.forall_mem_cons.2 ⟨sub5_1675, List.forall_mem_cons.2 ⟨sub5_1676, List.forall_mem_cons.2 ⟨sub5_1677, List.forall_mem_cons.2 ⟨sub5_1678, List.forall_mem_cons.2 ⟨sub5_1679, List.forall_mem_cons.2 ⟨sub5_1680, List.forall_mem_cons.2 ⟨sub5_1681, List.forall_mem_cons.2 ⟨sub5_1682, List.forall_mem_cons.2 ⟨sub5_1683, List.forall_mem_cons.2 ⟨sub5_1684, List.forall_mem_cons.2 ⟨sub5_1685, List.forall_mem_cons.2 ⟨sub5_1686, List.forall_mem_cons.2 ⟨sub5_1687, List.forall_mem_cons.2 ⟨sub5_1688, List.forall_mem_cons.2 ⟨sub5_1689, List.forall_mem_cons.2 ⟨sub5_1690, List.forall_mem_cons.2 ⟨sub5_1691, List.forall_mem_cons.2 ⟨sub5_1692, List.forall_mem_cons.2 ⟨sub5_1693, List.forall_mem_cons.2 ⟨sub5_1694, List.forall_mem_cons.2 ⟨sub5_1695, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_1696 : sub5 [3, 3, -7] = true := by decide +kernel
theorem sub5_1697 : sub5 [3, 3, -6] = true := by decide +kernel
theorem sub5_1698 : sub5 [3, 3, -5] = true := by decide +kernel
theorem sub5_1699 : sub5 [3, 3, -4] = true := by decide +kernel
theorem sub5_1700 : sub5 [3, 3, -3] = true := by decide +kernel
theorem sub5_1701 : sub5 [3, 3, -2] = true := by decide +kernel
theorem sub5_1702 : sub5 [3, 3, -1] = true := by decide +kernel
theorem sub5_1703 : sub5 [3, 3, 0] = true := by decide +kernel
theorem sub5_1704 : sub5 [3, 3, 1] = true := by decide +kernel
theorem sub5_1705 : sub5 [3, 3, 2] = true := by decide +kernel
theorem sub5_1706 : sub5 [3, 3, 3] = true := by decide +kernel
theorem sub5_1707 : sub5 [3, 3, 4] = true := by decide +kernel
theorem sub5_1708 : sub5 [3, 3, 5] = true := by decide +kernel
theorem sub5_1709 : sub5 [3, 3, 6] = true := by decide +kernel
theorem sub5_1710 : sub5 [3, 3, 7] = true := by decide +kernel
theorem sub5_1711 : sub5 [3, 3, 8] = true := by decide +kernel
theorem sub5_1712 : sub5 [3, 4, -7] = true := by decide +kernel
theorem sub5_1713 : sub5 [3, 4, -6] = true := by decide +kernel
theorem sub5_1714 : sub5 [3, 4, -5] = true := by decide +kernel
theorem sub5_1715 : sub5 [3, 4, -4] = true := by decide +kernel
theorem sub5_1716 : sub5 [3, 4, -3] = true := by decide +kernel
theorem sub5_1717 : sub5 [3, 4, -2] = true := by decide +kernel
theorem sub5_1718 : sub5 [3, 4, -1] = true := by decide +kernel
theorem sub5_1719 : sub5 [3, 4, 0] = true := by decide +kernel
theorem sub5_1720 : sub5 [3, 4, 1] = true := by decide +kernel
theorem sub5_1721 : sub5 [3, 4, 2] = true := by decide +kernel
theorem sub5_1722 : sub5 [3, 4, 3] = true := by decide +kernel
theorem sub5_1723 : sub5 [3, 4, 4] = true := by decide +kernel
theorem sub5_1724 : sub5 [3, 4, 5] = true := by decide +kernel
theorem sub5_1725 : sub5 [3, 4, 6] = true := by decide +kernel
theorem sub5_1726 : sub5 [3, 4, 7] = true := by decide +kernel
theorem sub5_1727 : sub5 [3, 5] = true := by decide +kernel
theorem sb5_53 : ∀ q ∈ blk5_53, sub5 q = true := by
  unfold blk5_53
  exact List.forall_mem_cons.2 ⟨sub5_1696, List.forall_mem_cons.2 ⟨sub5_1697, List.forall_mem_cons.2 ⟨sub5_1698, List.forall_mem_cons.2 ⟨sub5_1699, List.forall_mem_cons.2 ⟨sub5_1700, List.forall_mem_cons.2 ⟨sub5_1701, List.forall_mem_cons.2 ⟨sub5_1702, List.forall_mem_cons.2 ⟨sub5_1703, List.forall_mem_cons.2 ⟨sub5_1704, List.forall_mem_cons.2 ⟨sub5_1705, List.forall_mem_cons.2 ⟨sub5_1706, List.forall_mem_cons.2 ⟨sub5_1707, List.forall_mem_cons.2 ⟨sub5_1708, List.forall_mem_cons.2 ⟨sub5_1709, List.forall_mem_cons.2 ⟨sub5_1710, List.forall_mem_cons.2 ⟨sub5_1711, List.forall_mem_cons.2 ⟨sub5_1712, List.forall_mem_cons.2 ⟨sub5_1713, List.forall_mem_cons.2 ⟨sub5_1714, List.forall_mem_cons.2 ⟨sub5_1715, List.forall_mem_cons.2 ⟨sub5_1716, List.forall_mem_cons.2 ⟨sub5_1717, List.forall_mem_cons.2 ⟨sub5_1718, List.forall_mem_cons.2 ⟨sub5_1719, List.forall_mem_cons.2 ⟨sub5_1720, List.forall_mem_cons.2 ⟨sub5_1721, List.forall_mem_cons.2 ⟨sub5_1722, List.forall_mem_cons.2 ⟨sub5_1723, List.forall_mem_cons.2 ⟨sub5_1724, List.forall_mem_cons.2 ⟨sub5_1725, List.forall_mem_cons.2 ⟨sub5_1726, List.forall_mem_cons.2 ⟨sub5_1727, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_1728 : sub5 [3, 6] = true := by decide +kernel
theorem sub5_1729 : sub5 [4, -8] = true := by decide +kernel
theorem sub5_1730 : sub5 [4, -7] = true := by decide +kernel
theorem sub5_1731 : sub5 [4, -6] = true := by decide +kernel
theorem sub5_1732 : sub5 [4, -5] = true := by decide +kernel
theorem sub5_1733 : sub5 [4, -4, -6] = true := by decide +kernel
theorem sub5_1734 : sub5 [4, -4, -5] = true := by decide +kernel
theorem sub5_1735 : sub5 [4, -4, -4] = true := by decide +kernel
theorem sub5_1736 : sub5 [4, -4, -3] = true := by decide +kernel
theorem sub5_1737 : sub5 [4, -4, -2] = true := by decide +kernel
theorem sub5_1738 : sub5 [4, -4, -1] = true := by decide +kernel
theorem sub5_1739 : sub5 [4, -4, 0] = true := by decide +kernel
theorem sub5_1740 : sub5 [4, -4, 1] = true := by decide +kernel
theorem sub5_1741 : sub5 [4, -4, 2] = true := by decide +kernel
theorem sub5_1742 : sub5 [4, -4, 3] = true := by decide +kernel
theorem sub5_1743 : sub5 [4, -4, 4] = true := by decide +kernel
theorem sub5_1744 : sub5 [4, -4, 5] = true := by decide +kernel
theorem sub5_1745 : sub5 [4, -4, 6] = true := by decide +kernel
theorem sub5_1746 : sub5 [4, -4, 7] = true := by decide +kernel
theorem sub5_1747 : sub5 [4, -4, 8] = true := by decide +kernel
theorem sub5_1748 : sub5 [4, -4, 9] = true := by decide +kernel
theorem sub5_1749 : sub5 [4, -3, -6] = true := by decide +kernel
theorem sub5_1750 : sub5 [4, -3, -5] = true := by decide +kernel
theorem sub5_1751 : sub5 [4, -3, -4] = true := by decide +kernel
theorem sub5_1752 : sub5 [4, -3, -3] = true := by decide +kernel
theorem sub5_1753 : sub5 [4, -3, -2] = true := by decide +kernel
theorem sub5_1754 : sub5 [4, -3, -1] = true := by decide +kernel
theorem sub5_1755 : sub5 [4, -3, 0] = true := by decide +kernel
theorem sub5_1756 : sub5 [4, -3, 1] = true := by decide +kernel
theorem sub5_1757 : sub5 [4, -3, 2] = true := by decide +kernel
theorem sub5_1758 : sub5 [4, -3, 3] = true := by decide +kernel
theorem sub5_1759 : sub5 [4, -3, 4] = true := by decide +kernel
theorem sb5_54 : ∀ q ∈ blk5_54, sub5 q = true := by
  unfold blk5_54
  exact List.forall_mem_cons.2 ⟨sub5_1728, List.forall_mem_cons.2 ⟨sub5_1729, List.forall_mem_cons.2 ⟨sub5_1730, List.forall_mem_cons.2 ⟨sub5_1731, List.forall_mem_cons.2 ⟨sub5_1732, List.forall_mem_cons.2 ⟨sub5_1733, List.forall_mem_cons.2 ⟨sub5_1734, List.forall_mem_cons.2 ⟨sub5_1735, List.forall_mem_cons.2 ⟨sub5_1736, List.forall_mem_cons.2 ⟨sub5_1737, List.forall_mem_cons.2 ⟨sub5_1738, List.forall_mem_cons.2 ⟨sub5_1739, List.forall_mem_cons.2 ⟨sub5_1740, List.forall_mem_cons.2 ⟨sub5_1741, List.forall_mem_cons.2 ⟨sub5_1742, List.forall_mem_cons.2 ⟨sub5_1743, List.forall_mem_cons.2 ⟨sub5_1744, List.forall_mem_cons.2 ⟨sub5_1745, List.forall_mem_cons.2 ⟨sub5_1746, List.forall_mem_cons.2 ⟨sub5_1747, List.forall_mem_cons.2 ⟨sub5_1748, List.forall_mem_cons.2 ⟨sub5_1749, List.forall_mem_cons.2 ⟨sub5_1750, List.forall_mem_cons.2 ⟨sub5_1751, List.forall_mem_cons.2 ⟨sub5_1752, List.forall_mem_cons.2 ⟨sub5_1753, List.forall_mem_cons.2 ⟨sub5_1754, List.forall_mem_cons.2 ⟨sub5_1755, List.forall_mem_cons.2 ⟨sub5_1756, List.forall_mem_cons.2 ⟨sub5_1757, List.forall_mem_cons.2 ⟨sub5_1758, List.forall_mem_cons.2 ⟨sub5_1759, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_1760 : sub5 [4, -3, 5] = true := by decide +kernel
theorem sub5_1761 : sub5 [4, -3, 6] = true := by decide +kernel
theorem sub5_1762 : sub5 [4, -3, 7] = true := by decide +kernel
theorem sub5_1763 : sub5 [4, -3, 8] = true := by decide +kernel
theorem sub5_1764 : sub5 [4, -3, 9] = true := by decide +kernel
theorem sub5_1765 : sub5 [4, -3, 10] = true := by decide +kernel
theorem sub5_1766 : sub5 [4, -2, -7] = true := by decide +kernel
theorem sub5_1767 : sub5 [4, -2, -6] = true := by decide +kernel
theorem sub5_1768 : sub5 [4, -2, -5] = true := by decide +kernel
theorem sub5_1769 : sub5 [4, -2, -4] = true := by decide +kernel
theorem sub5_1770 : sub5 [4, -2, -3] = true := by decide +kernel
theorem sub5_1771 : sub5 [4, -2, -2] = true := by decide +kernel
theorem sub5_1772 : sub5 [4, -2, -1] = true := by decide +kernel
theorem sub5_1773 : sub5 [4, -2, 0] = true := by decide +kernel
theorem sub5_1774 : sub5 [4, -2, 1] = true := by decide +kernel
theorem sub5_1775 : sub5 [4, -2, 2] = true := by decide +kernel
theorem sub5_1776 : sub5 [4, -2, 3] = true := by decide +kernel
theorem sub5_1777 : sub5 [4, -2, 4] = true := by decide +kernel
theorem sub5_1778 : sub5 [4, -2, 5] = true := by decide +kernel
theorem sub5_1779 : sub5 [4, -2, 6] = true := by decide +kernel
theorem sub5_1780 : sub5 [4, -2, 7] = true := by decide +kernel
theorem sub5_1781 : sub5 [4, -2, 8] = true := by decide +kernel
theorem sub5_1782 : sub5 [4, -2, 9] = true := by decide +kernel
theorem sub5_1783 : sub5 [4, -2, 10] = true := by decide +kernel
theorem sub5_1784 : sub5 [4, -1, -7] = true := by decide +kernel
theorem sub5_1785 : sub5 [4, -1, -6] = true := by decide +kernel
theorem sub5_1786 : sub5 [4, -1, -5] = true := by decide +kernel
theorem sub5_1787 : sub5 [4, -1, -4] = true := by decide +kernel
theorem sub5_1788 : sub5 [4, -1, -3] = true := by decide +kernel
theorem sub5_1789 : sub5 [4, -1, -2] = true := by decide +kernel
theorem sub5_1790 : sub5 [4, -1, -1] = true := by decide +kernel
theorem sub5_1791 : sub5 [4, -1, 0] = true := by decide +kernel
theorem sb5_55 : ∀ q ∈ blk5_55, sub5 q = true := by
  unfold blk5_55
  exact List.forall_mem_cons.2 ⟨sub5_1760, List.forall_mem_cons.2 ⟨sub5_1761, List.forall_mem_cons.2 ⟨sub5_1762, List.forall_mem_cons.2 ⟨sub5_1763, List.forall_mem_cons.2 ⟨sub5_1764, List.forall_mem_cons.2 ⟨sub5_1765, List.forall_mem_cons.2 ⟨sub5_1766, List.forall_mem_cons.2 ⟨sub5_1767, List.forall_mem_cons.2 ⟨sub5_1768, List.forall_mem_cons.2 ⟨sub5_1769, List.forall_mem_cons.2 ⟨sub5_1770, List.forall_mem_cons.2 ⟨sub5_1771, List.forall_mem_cons.2 ⟨sub5_1772, List.forall_mem_cons.2 ⟨sub5_1773, List.forall_mem_cons.2 ⟨sub5_1774, List.forall_mem_cons.2 ⟨sub5_1775, List.forall_mem_cons.2 ⟨sub5_1776, List.forall_mem_cons.2 ⟨sub5_1777, List.forall_mem_cons.2 ⟨sub5_1778, List.forall_mem_cons.2 ⟨sub5_1779, List.forall_mem_cons.2 ⟨sub5_1780, List.forall_mem_cons.2 ⟨sub5_1781, List.forall_mem_cons.2 ⟨sub5_1782, List.forall_mem_cons.2 ⟨sub5_1783, List.forall_mem_cons.2 ⟨sub5_1784, List.forall_mem_cons.2 ⟨sub5_1785, List.forall_mem_cons.2 ⟨sub5_1786, List.forall_mem_cons.2 ⟨sub5_1787, List.forall_mem_cons.2 ⟨sub5_1788, List.forall_mem_cons.2 ⟨sub5_1789, List.forall_mem_cons.2 ⟨sub5_1790, List.forall_mem_cons.2 ⟨sub5_1791, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_1792 : sub5 [4, -1, 1] = true := by decide +kernel
theorem sub5_1793 : sub5 [4, -1, 2] = true := by decide +kernel
theorem sub5_1794 : sub5 [4, -1, 3] = true := by decide +kernel
theorem sub5_1795 : sub5 [4, -1, 4] = true := by decide +kernel
theorem sub5_1796 : sub5 [4, -1, 5] = true := by decide +kernel
theorem sub5_1797 : sub5 [4, -1, 6] = true := by decide +kernel
theorem sub5_1798 : sub5 [4, -1, 7] = true := by decide +kernel
theorem sub5_1799 : sub5 [4, -1, 8] = true := by decide +kernel
theorem sub5_1800 : sub5 [4, -1, 9] = true := by decide +kernel
theorem sub5_1801 : sub5 [4, -1, 10] = true := by decide +kernel
theorem sub5_1802 : sub5 [4, 0, -7] = true := by decide +kernel
theorem sub5_1803 : sub5 [4, 0, -6] = true := by decide +kernel
theorem sub5_1804 : sub5 [4, 0, -5] = true := by decide +kernel
theorem sub5_1805 : sub5 [4, 0, -4] = true := by decide +kernel
theorem sub5_1806 : sub5 [4, 0, -3] = true := by decide +kernel
theorem sub5_1807 : sub5 [4, 0, -2] = true := by decide +kernel
theorem sub5_1808 : sub5 [4, 0, -1] = true := by decide +kernel
theorem sub5_1809 : sub5 [4, 0, 0] = true := by decide +kernel
theorem sub5_1810 : sub5 [4, 0, 1] = true := by decide +kernel
theorem sub5_1811 : sub5 [4, 0, 2] = true := by decide +kernel
theorem sub5_1812 : sub5 [4, 0, 3] = true := by decide +kernel
theorem sub5_1813 : sub5 [4, 0, 4] = true := by decide +kernel
theorem sub5_1814 : sub5 [4, 0, 5] = true := by decide +kernel
theorem sub5_1815 : sub5 [4, 0, 6] = true := by decide +kernel
theorem sub5_1816 : sub5 [4, 0, 7] = true := by decide +kernel
theorem sub5_1817 : sub5 [4, 0, 8] = true := by decide +kernel
theorem sub5_1818 : sub5 [4, 0, 9] = true := by decide +kernel
theorem sub5_1819 : sub5 [4, 0, 10] = true := by decide +kernel
theorem sub5_1820 : sub5 [4, 1, -7] = true := by decide +kernel
theorem sub5_1821 : sub5 [4, 1, -6] = true := by decide +kernel
theorem sub5_1822 : sub5 [4, 1, -5] = true := by decide +kernel
theorem sub5_1823 : sub5 [4, 1, -4] = true := by decide +kernel
theorem sb5_56 : ∀ q ∈ blk5_56, sub5 q = true := by
  unfold blk5_56
  exact List.forall_mem_cons.2 ⟨sub5_1792, List.forall_mem_cons.2 ⟨sub5_1793, List.forall_mem_cons.2 ⟨sub5_1794, List.forall_mem_cons.2 ⟨sub5_1795, List.forall_mem_cons.2 ⟨sub5_1796, List.forall_mem_cons.2 ⟨sub5_1797, List.forall_mem_cons.2 ⟨sub5_1798, List.forall_mem_cons.2 ⟨sub5_1799, List.forall_mem_cons.2 ⟨sub5_1800, List.forall_mem_cons.2 ⟨sub5_1801, List.forall_mem_cons.2 ⟨sub5_1802, List.forall_mem_cons.2 ⟨sub5_1803, List.forall_mem_cons.2 ⟨sub5_1804, List.forall_mem_cons.2 ⟨sub5_1805, List.forall_mem_cons.2 ⟨sub5_1806, List.forall_mem_cons.2 ⟨sub5_1807, List.forall_mem_cons.2 ⟨sub5_1808, List.forall_mem_cons.2 ⟨sub5_1809, List.forall_mem_cons.2 ⟨sub5_1810, List.forall_mem_cons.2 ⟨sub5_1811, List.forall_mem_cons.2 ⟨sub5_1812, List.forall_mem_cons.2 ⟨sub5_1813, List.forall_mem_cons.2 ⟨sub5_1814, List.forall_mem_cons.2 ⟨sub5_1815, List.forall_mem_cons.2 ⟨sub5_1816, List.forall_mem_cons.2 ⟨sub5_1817, List.forall_mem_cons.2 ⟨sub5_1818, List.forall_mem_cons.2 ⟨sub5_1819, List.forall_mem_cons.2 ⟨sub5_1820, List.forall_mem_cons.2 ⟨sub5_1821, List.forall_mem_cons.2 ⟨sub5_1822, List.forall_mem_cons.2 ⟨sub5_1823, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_1824 : sub5 [4, 1, -3] = true := by decide +kernel
theorem sub5_1825 : sub5 [4, 1, -2] = true := by decide +kernel
theorem sub5_1826 : sub5 [4, 1, -1] = true := by decide +kernel
theorem sub5_1827 : sub5 [4, 1, 0] = true := by decide +kernel
theorem sub5_1828 : sub5 [4, 1, 1] = true := by decide +kernel
theorem sub5_1829 : sub5 [4, 1, 2] = true := by decide +kernel
theorem sub5_1830 : sub5 [4, 1, 3] = true := by decide +kernel
theorem sub5_1831 : sub5 [4, 1, 4] = true := by decide +kernel
theorem sub5_1832 : sub5 [4, 1, 5] = true := by decide +kernel
theorem sub5_1833 : sub5 [4, 1, 6] = true := by decide +kernel
theorem sub5_1834 : sub5 [4, 1, 7] = true := by decide +kernel
theorem sub5_1835 : sub5 [4, 1, 8] = true := by decide +kernel
theorem sub5_1836 : sub5 [4, 1, 9] = true := by decide +kernel
theorem sub5_1837 : sub5 [4, 2, -7] = true := by decide +kernel
theorem sub5_1838 : sub5 [4, 2, -6] = true := by decide +kernel
theorem sub5_1839 : sub5 [4, 2, -5] = true := by decide +kernel
theorem sub5_1840 : sub5 [4, 2, -4] = true := by decide +kernel
theorem sub5_1841 : sub5 [4, 2, -3] = true := by decide +kernel
theorem sub5_1842 : sub5 [4, 2, -2] = true := by decide +kernel
theorem sub5_1843 : sub5 [4, 2, -1] = true := by decide +kernel
theorem sub5_1844 : sub5 [4, 2, 0] = true := by decide +kernel
theorem sub5_1845 : sub5 [4, 2, 1] = true := by decide +kernel
theorem sub5_1846 : sub5 [4, 2, 2] = true := by decide +kernel
theorem sub5_1847 : sub5 [4, 2, 3] = true := by decide +kernel
theorem sub5_1848 : sub5 [4, 2, 4] = true := by decide +kernel
theorem sub5_1849 : sub5 [4, 2, 5] = true := by decide +kernel
theorem sub5_1850 : sub5 [4, 2, 6] = true := by decide +kernel
theorem sub5_1851 : sub5 [4, 2, 7] = true := by decide +kernel
theorem sub5_1852 : sub5 [4, 2, 8] = true := by decide +kernel
theorem sub5_1853 : sub5 [4, 3, -7] = true := by decide +kernel
theorem sub5_1854 : sub5 [4, 3, -6] = true := by decide +kernel
theorem sub5_1855 : sub5 [4, 3, -5] = true := by decide +kernel
theorem sb5_57 : ∀ q ∈ blk5_57, sub5 q = true := by
  unfold blk5_57
  exact List.forall_mem_cons.2 ⟨sub5_1824, List.forall_mem_cons.2 ⟨sub5_1825, List.forall_mem_cons.2 ⟨sub5_1826, List.forall_mem_cons.2 ⟨sub5_1827, List.forall_mem_cons.2 ⟨sub5_1828, List.forall_mem_cons.2 ⟨sub5_1829, List.forall_mem_cons.2 ⟨sub5_1830, List.forall_mem_cons.2 ⟨sub5_1831, List.forall_mem_cons.2 ⟨sub5_1832, List.forall_mem_cons.2 ⟨sub5_1833, List.forall_mem_cons.2 ⟨sub5_1834, List.forall_mem_cons.2 ⟨sub5_1835, List.forall_mem_cons.2 ⟨sub5_1836, List.forall_mem_cons.2 ⟨sub5_1837, List.forall_mem_cons.2 ⟨sub5_1838, List.forall_mem_cons.2 ⟨sub5_1839, List.forall_mem_cons.2 ⟨sub5_1840, List.forall_mem_cons.2 ⟨sub5_1841, List.forall_mem_cons.2 ⟨sub5_1842, List.forall_mem_cons.2 ⟨sub5_1843, List.forall_mem_cons.2 ⟨sub5_1844, List.forall_mem_cons.2 ⟨sub5_1845, List.forall_mem_cons.2 ⟨sub5_1846, List.forall_mem_cons.2 ⟨sub5_1847, List.forall_mem_cons.2 ⟨sub5_1848, List.forall_mem_cons.2 ⟨sub5_1849, List.forall_mem_cons.2 ⟨sub5_1850, List.forall_mem_cons.2 ⟨sub5_1851, List.forall_mem_cons.2 ⟨sub5_1852, List.forall_mem_cons.2 ⟨sub5_1853, List.forall_mem_cons.2 ⟨sub5_1854, List.forall_mem_cons.2 ⟨sub5_1855, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_1856 : sub5 [4, 3, -4] = true := by decide +kernel
theorem sub5_1857 : sub5 [4, 3, -3] = true := by decide +kernel
theorem sub5_1858 : sub5 [4, 3, -2] = true := by decide +kernel
theorem sub5_1859 : sub5 [4, 3, -1] = true := by decide +kernel
theorem sub5_1860 : sub5 [4, 3, 0] = true := by decide +kernel
theorem sub5_1861 : sub5 [4, 3, 1] = true := by decide +kernel
theorem sub5_1862 : sub5 [4, 3, 2] = true := by decide +kernel
theorem sub5_1863 : sub5 [4, 3, 3] = true := by decide +kernel
theorem sub5_1864 : sub5 [4, 3, 4] = true := by decide +kernel
theorem sub5_1865 : sub5 [4, 3, 5] = true := by decide +kernel
theorem sub5_1866 : sub5 [4, 3, 6] = true := by decide +kernel
theorem sub5_1867 : sub5 [4, 3, 7] = true := by decide +kernel
theorem sub5_1868 : sub5 [4, 4] = true := by decide +kernel
theorem sub5_1869 : sub5 [4, 5] = true := by decide +kernel
theorem sub5_1870 : sub5 [5, -7] = true := by decide +kernel
theorem sub5_1871 : sub5 [5, -6] = true := by decide +kernel
theorem sub5_1872 : sub5 [5, -5] = true := by decide +kernel
theorem sub5_1873 : sub5 [5, -4] = true := by decide +kernel
theorem sub5_1874 : sub5 [5, -3, -5] = true := by decide +kernel
theorem sub5_1875 : sub5 [5, -3, -4] = true := by decide +kernel
theorem sub5_1876 : sub5 [5, -3, -3] = true := by decide +kernel
theorem sub5_1877 : sub5 [5, -3, -2] = true := by decide +kernel
theorem sub5_1878 : sub5 [5, -3, -1] = true := by decide +kernel
theorem sub5_1879 : sub5 [5, -3, 0] = true := by decide +kernel
theorem sub5_1880 : sub5 [5, -3, 1] = true := by decide +kernel
theorem sub5_1881 : sub5 [5, -3, 2] = true := by decide +kernel
theorem sub5_1882 : sub5 [5, -3, 3] = true := by decide +kernel
theorem sub5_1883 : sub5 [5, -3, 4] = true := by decide +kernel
theorem sub5_1884 : sub5 [5, -3, 5] = true := by decide +kernel
theorem sub5_1885 : sub5 [5, -3, 6] = true := by decide +kernel
theorem sub5_1886 : sub5 [5, -3, 7] = true := by decide +kernel
theorem sub5_1887 : sub5 [5, -3, 8] = true := by decide +kernel
theorem sb5_58 : ∀ q ∈ blk5_58, sub5 q = true := by
  unfold blk5_58
  exact List.forall_mem_cons.2 ⟨sub5_1856, List.forall_mem_cons.2 ⟨sub5_1857, List.forall_mem_cons.2 ⟨sub5_1858, List.forall_mem_cons.2 ⟨sub5_1859, List.forall_mem_cons.2 ⟨sub5_1860, List.forall_mem_cons.2 ⟨sub5_1861, List.forall_mem_cons.2 ⟨sub5_1862, List.forall_mem_cons.2 ⟨sub5_1863, List.forall_mem_cons.2 ⟨sub5_1864, List.forall_mem_cons.2 ⟨sub5_1865, List.forall_mem_cons.2 ⟨sub5_1866, List.forall_mem_cons.2 ⟨sub5_1867, List.forall_mem_cons.2 ⟨sub5_1868, List.forall_mem_cons.2 ⟨sub5_1869, List.forall_mem_cons.2 ⟨sub5_1870, List.forall_mem_cons.2 ⟨sub5_1871, List.forall_mem_cons.2 ⟨sub5_1872, List.forall_mem_cons.2 ⟨sub5_1873, List.forall_mem_cons.2 ⟨sub5_1874, List.forall_mem_cons.2 ⟨sub5_1875, List.forall_mem_cons.2 ⟨sub5_1876, List.forall_mem_cons.2 ⟨sub5_1877, List.forall_mem_cons.2 ⟨sub5_1878, List.forall_mem_cons.2 ⟨sub5_1879, List.forall_mem_cons.2 ⟨sub5_1880, List.forall_mem_cons.2 ⟨sub5_1881, List.forall_mem_cons.2 ⟨sub5_1882, List.forall_mem_cons.2 ⟨sub5_1883, List.forall_mem_cons.2 ⟨sub5_1884, List.forall_mem_cons.2 ⟨sub5_1885, List.forall_mem_cons.2 ⟨sub5_1886, List.forall_mem_cons.2 ⟨sub5_1887, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_1888 : sub5 [5, -3, 9] = true := by decide +kernel
theorem sub5_1889 : sub5 [5, -2, -5] = true := by decide +kernel
theorem sub5_1890 : sub5 [5, -2, -4] = true := by decide +kernel
theorem sub5_1891 : sub5 [5, -2, -3] = true := by decide +kernel
theorem sub5_1892 : sub5 [5, -2, -2] = true := by decide +kernel
theorem sub5_1893 : sub5 [5, -2, -1] = true := by decide +kernel
theorem sub5_1894 : sub5 [5, -2, 0] = true := by decide +kernel
theorem sub5_1895 : sub5 [5, -2, 1] = true := by decide +kernel
theorem sub5_1896 : sub5 [5, -2, 2] = true := by decide +kernel
theorem sub5_1897 : sub5 [5, -2, 3] = true := by decide +kernel
theorem sub5_1898 : sub5 [5, -2, 4] = true := by decide +kernel
theorem sub5_1899 : sub5 [5, -2, 5] = true := by decide +kernel
theorem sub5_1900 : sub5 [5, -2, 6] = true := by decide +kernel
theorem sub5_1901 : sub5 [5, -2, 7] = true := by decide +kernel
theorem sub5_1902 : sub5 [5, -2, 8] = true := by decide +kernel
theorem sub5_1903 : sub5 [5, -2, 9] = true := by decide +kernel
theorem sub5_1904 : sub5 [5, -1, -6] = true := by decide +kernel
theorem sub5_1905 : sub5 [5, -1, -5] = true := by decide +kernel
theorem sub5_1906 : sub5 [5, -1, -4] = true := by decide +kernel
theorem sub5_1907 : sub5 [5, -1, -3] = true := by decide +kernel
theorem sub5_1908 : sub5 [5, -1, -2] = true := by decide +kernel
theorem sub5_1909 : sub5 [5, -1, -1] = true := by decide +kernel
theorem sub5_1910 : sub5 [5, -1, 0] = true := by decide +kernel
theorem sub5_1911 : sub5 [5, -1, 1] = true := by decide +kernel
theorem sub5_1912 : sub5 [5, -1, 2] = true := by decide +kernel
theorem sub5_1913 : sub5 [5, -1, 3] = true := by decide +kernel
theorem sub5_1914 : sub5 [5, -1, 4] = true := by decide +kernel
theorem sub5_1915 : sub5 [5, -1, 5] = true := by decide +kernel
theorem sub5_1916 : sub5 [5, -1, 6] = true := by decide +kernel
theorem sub5_1917 : sub5 [5, -1, 7] = true := by decide +kernel
theorem sub5_1918 : sub5 [5, -1, 8] = true := by decide +kernel
theorem sub5_1919 : sub5 [5, -1, 9] = true := by decide +kernel
theorem sb5_59 : ∀ q ∈ blk5_59, sub5 q = true := by
  unfold blk5_59
  exact List.forall_mem_cons.2 ⟨sub5_1888, List.forall_mem_cons.2 ⟨sub5_1889, List.forall_mem_cons.2 ⟨sub5_1890, List.forall_mem_cons.2 ⟨sub5_1891, List.forall_mem_cons.2 ⟨sub5_1892, List.forall_mem_cons.2 ⟨sub5_1893, List.forall_mem_cons.2 ⟨sub5_1894, List.forall_mem_cons.2 ⟨sub5_1895, List.forall_mem_cons.2 ⟨sub5_1896, List.forall_mem_cons.2 ⟨sub5_1897, List.forall_mem_cons.2 ⟨sub5_1898, List.forall_mem_cons.2 ⟨sub5_1899, List.forall_mem_cons.2 ⟨sub5_1900, List.forall_mem_cons.2 ⟨sub5_1901, List.forall_mem_cons.2 ⟨sub5_1902, List.forall_mem_cons.2 ⟨sub5_1903, List.forall_mem_cons.2 ⟨sub5_1904, List.forall_mem_cons.2 ⟨sub5_1905, List.forall_mem_cons.2 ⟨sub5_1906, List.forall_mem_cons.2 ⟨sub5_1907, List.forall_mem_cons.2 ⟨sub5_1908, List.forall_mem_cons.2 ⟨sub5_1909, List.forall_mem_cons.2 ⟨sub5_1910, List.forall_mem_cons.2 ⟨sub5_1911, List.forall_mem_cons.2 ⟨sub5_1912, List.forall_mem_cons.2 ⟨sub5_1913, List.forall_mem_cons.2 ⟨sub5_1914, List.forall_mem_cons.2 ⟨sub5_1915, List.forall_mem_cons.2 ⟨sub5_1916, List.forall_mem_cons.2 ⟨sub5_1917, List.forall_mem_cons.2 ⟨sub5_1918, List.forall_mem_cons.2 ⟨sub5_1919, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_1920 : sub5 [5, 0, -6] = true := by decide +kernel
theorem sub5_1921 : sub5 [5, 0, -5] = true := by decide +kernel
theorem sub5_1922 : sub5 [5, 0, -4] = true := by decide +kernel
theorem sub5_1923 : sub5 [5, 0, -3] = true := by decide +kernel
theorem sub5_1924 : sub5 [5, 0, -2] = true := by decide +kernel
theorem sub5_1925 : sub5 [5, 0, -1] = true := by decide +kernel
theorem sub5_1926 : sub5 [5, 0, 0] = true := by decide +kernel
theorem sub5_1927 : sub5 [5, 0, 1] = true := by decide +kernel
theorem sub5_1928 : sub5 [5, 0, 2] = true := by decide +kernel
theorem sub5_1929 : sub5 [5, 0, 3] = true := by decide +kernel
theorem sub5_1930 : sub5 [5, 0, 4] = true := by decide +kernel
theorem sub5_1931 : sub5 [5, 0, 5] = true := by decide +kernel
theorem sub5_1932 : sub5 [5, 0, 6] = true := by decide +kernel
theorem sub5_1933 : sub5 [5, 0, 7] = true := by decide +kernel
theorem sub5_1934 : sub5 [5, 0, 8] = true := by decide +kernel
theorem sub5_1935 : sub5 [5, 0, 9] = true := by decide +kernel
theorem sub5_1936 : sub5 [5, 1, -6] = true := by decide +kernel
theorem sub5_1937 : sub5 [5, 1, -5] = true := by decide +kernel
theorem sub5_1938 : sub5 [5, 1, -4] = true := by decide +kernel
theorem sub5_1939 : sub5 [5, 1, -3] = true := by decide +kernel
theorem sub5_1940 : sub5 [5, 1, -2] = true := by decide +kernel
theorem sub5_1941 : sub5 [5, 1, -1] = true := by decide +kernel
theorem sub5_1942 : sub5 [5, 1, 0] = true := by decide +kernel
theorem sub5_1943 : sub5 [5, 1, 1] = true := by decide +kernel
theorem sub5_1944 : sub5 [5, 1, 2] = true := by decide +kernel
theorem sub5_1945 : sub5 [5, 1, 3] = true := by decide +kernel
theorem sub5_1946 : sub5 [5, 1, 4] = true := by decide +kernel
theorem sub5_1947 : sub5 [5, 1, 5] = true := by decide +kernel
theorem sub5_1948 : sub5 [5, 1, 6] = true := by decide +kernel
theorem sub5_1949 : sub5 [5, 1, 7] = true := by decide +kernel
theorem sub5_1950 : sub5 [5, 1, 8] = true := by decide +kernel
theorem sub5_1951 : sub5 [5, 2] = true := by decide +kernel
theorem sb5_60 : ∀ q ∈ blk5_60, sub5 q = true := by
  unfold blk5_60
  exact List.forall_mem_cons.2 ⟨sub5_1920, List.forall_mem_cons.2 ⟨sub5_1921, List.forall_mem_cons.2 ⟨sub5_1922, List.forall_mem_cons.2 ⟨sub5_1923, List.forall_mem_cons.2 ⟨sub5_1924, List.forall_mem_cons.2 ⟨sub5_1925, List.forall_mem_cons.2 ⟨sub5_1926, List.forall_mem_cons.2 ⟨sub5_1927, List.forall_mem_cons.2 ⟨sub5_1928, List.forall_mem_cons.2 ⟨sub5_1929, List.forall_mem_cons.2 ⟨sub5_1930, List.forall_mem_cons.2 ⟨sub5_1931, List.forall_mem_cons.2 ⟨sub5_1932, List.forall_mem_cons.2 ⟨sub5_1933, List.forall_mem_cons.2 ⟨sub5_1934, List.forall_mem_cons.2 ⟨sub5_1935, List.forall_mem_cons.2 ⟨sub5_1936, List.forall_mem_cons.2 ⟨sub5_1937, List.forall_mem_cons.2 ⟨sub5_1938, List.forall_mem_cons.2 ⟨sub5_1939, List.forall_mem_cons.2 ⟨sub5_1940, List.forall_mem_cons.2 ⟨sub5_1941, List.forall_mem_cons.2 ⟨sub5_1942, List.forall_mem_cons.2 ⟨sub5_1943, List.forall_mem_cons.2 ⟨sub5_1944, List.forall_mem_cons.2 ⟨sub5_1945, List.forall_mem_cons.2 ⟨sub5_1946, List.forall_mem_cons.2 ⟨sub5_1947, List.forall_mem_cons.2 ⟨sub5_1948, List.forall_mem_cons.2 ⟨sub5_1949, List.forall_mem_cons.2 ⟨sub5_1950, List.forall_mem_cons.2 ⟨sub5_1951, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_1952 : sub5 [5, 3] = true := by decide +kernel
theorem sub5_1953 : sub5 [5, 4] = true := by decide +kernel
theorem sub5_1954 : sub5 [6, -6] = true := by decide +kernel
theorem sub5_1955 : sub5 [6, -5] = true := by decide +kernel
theorem sub5_1956 : sub5 [6, -4] = true := by decide +kernel
theorem sub5_1957 : sub5 [6, -3] = true := by decide +kernel
theorem sub5_1958 : sub5 [6, -2] = true := by decide +kernel
theorem sub5_1959 : sub5 [6, -1] = true := by decide +kernel
theorem sub5_1960 : sub5 [6, 0] = true := by decide +kernel
theorem sub5_1961 : sub5 [6, 1] = true := by decide +kernel
theorem sub5_1962 : sub5 [6, 2] = true := by decide +kernel
theorem sub5_1963 : sub5 [6, 3] = true := by decide +kernel
theorem sub5_1964 : sub5 [7] = true := by decide +kernel
theorem sb5_61 : ∀ q ∈ blk5_61, sub5 q = true := by
  unfold blk5_61
  exact List.forall_mem_cons.2 ⟨sub5_1952, List.forall_mem_cons.2 ⟨sub5_1953, List.forall_mem_cons.2 ⟨sub5_1954, List.forall_mem_cons.2 ⟨sub5_1955, List.forall_mem_cons.2 ⟨sub5_1956, List.forall_mem_cons.2 ⟨sub5_1957, List.forall_mem_cons.2 ⟨sub5_1958, List.forall_mem_cons.2 ⟨sub5_1959, List.forall_mem_cons.2 ⟨sub5_1960, List.forall_mem_cons.2 ⟨sub5_1961, List.forall_mem_cons.2 ⟨sub5_1962, List.forall_mem_cons.2 ⟨sub5_1963, List.forall_mem_cons.2 ⟨sub5_1964, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_0 : sub6 [-4, -3] = true := by decide +kernel
theorem sub6_1 : sub6 [-4, -2] = true := by decide +kernel
theorem sub6_2 : sub6 [-4, -1] = true := by decide +kernel
theorem sub6_3 : sub6 [-4, 0] = true := by decide +kernel
theorem sub6_4 : sub6 [-4, 1] = true := by decide +kernel
theorem sub6_5 : sub6 [-4, 2] = true := by decide +kernel
theorem sub6_6 : sub6 [-4, 3] = true := by decide +kernel
theorem sub6_7 : sub6 [-3, -4] = true := by decide +kernel
theorem sub6_8 : sub6 [-3, -3] = true := by decide +kernel
theorem sub6_9 : sub6 [-3, -2] = true := by decide +kernel
theorem sub6_10 : sub6 [-3, -1, -8] = true := by decide +kernel
theorem sub6_11 : sub6 [-3, -1, -7] = true := by decide +kernel
theorem sub6_12 : sub6 [-3, -1, -6] = true := by decide +kernel
theorem sub6_13 : sub6 [-3, -1, -5] = true := by decide +kernel
theorem sub6_14 : sub6 [-3, -1, -4] = true := by decide +kernel
theorem sub6_15 : sub6 [-3, -1, -3] = true := by decide +kernel
theorem sub6_16 : sub6 [-3, -1, -2] = true := by decide +kernel
theorem sub6_17 : sub6 [-3, -1, -1] = true := by decide +kernel
theorem sub6_18 : sub6 [-3, -1, 0] = true := by decide +kernel
theorem sub6_19 : sub6 [-3, -1, 1] = true := by decide +kernel
theorem sub6_20 : sub6 [-3, -1, 2] = true := by decide +kernel
theorem sub6_21 : sub6 [-3, -1, 3] = true := by decide +kernel
theorem sub6_22 : sub6 [-3, -1, 4] = true := by decide +kernel
theorem sub6_23 : sub6 [-3, -1, 5] = true := by decide +kernel
theorem sub6_24 : sub6 [-3, -1, 6] = true := by decide +kernel
theorem sub6_25 : sub6 [-3, -1, 7] = true := by decide +kernel
theorem sub6_26 : sub6 [-3, -1, 8] = true := by decide +kernel
theorem sub6_27 : sub6 [-3, 0, -9] = true := by decide +kernel
theorem sub6_28 : sub6 [-3, 0, -8] = true := by decide +kernel
theorem sub6_29 : sub6 [-3, 0, -7] = true := by decide +kernel
theorem sub6_30 : sub6 [-3, 0, -6] = true := by decide +kernel
theorem sub6_31 : sub6 [-3, 0, -5] = true := by decide +kernel
theorem sb6_0 : ∀ q ∈ blk6_0, sub6 q = true := by
  unfold blk6_0
  exact List.forall_mem_cons.2 ⟨sub6_0, List.forall_mem_cons.2 ⟨sub6_1, List.forall_mem_cons.2 ⟨sub6_2, List.forall_mem_cons.2 ⟨sub6_3, List.forall_mem_cons.2 ⟨sub6_4, List.forall_mem_cons.2 ⟨sub6_5, List.forall_mem_cons.2 ⟨sub6_6, List.forall_mem_cons.2 ⟨sub6_7, List.forall_mem_cons.2 ⟨sub6_8, List.forall_mem_cons.2 ⟨sub6_9, List.forall_mem_cons.2 ⟨sub6_10, List.forall_mem_cons.2 ⟨sub6_11, List.forall_mem_cons.2 ⟨sub6_12, List.forall_mem_cons.2 ⟨sub6_13, List.forall_mem_cons.2 ⟨sub6_14, List.forall_mem_cons.2 ⟨sub6_15, List.forall_mem_cons.2 ⟨sub6_16, List.forall_mem_cons.2 ⟨sub6_17, List.forall_mem_cons.2 ⟨sub6_18, List.forall_mem_cons.2 ⟨sub6_19, List.forall_mem_cons.2 ⟨sub6_20, List.forall_mem_cons.2 ⟨sub6_21, List.forall_mem_cons.2 ⟨sub6_22, List.forall_mem_cons.2 ⟨sub6_23, List.forall_mem_cons.2 ⟨sub6_24, List.forall_mem_cons.2 ⟨sub6_25, List.forall_mem_cons.2 ⟨sub6_26, List.forall_mem_cons.2 ⟨sub6_27, List.forall_mem_cons.2 ⟨sub6_28, List.forall_mem_cons.2 ⟨sub6_29, List.forall_mem_cons.2 ⟨sub6_30, List.forall_mem_cons.2 ⟨sub6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_32 : sub6 [-3, 0, -4] = true := by decide +kernel
theorem sub6_33 : sub6 [-3, 0, -3] = true := by decide +kernel
theorem sub6_34 : sub6 [-3, 0, -2] = true := by decide +kernel
theorem sub6_35 : sub6 [-3, 0, -1] = true := by decide +kernel
theorem sub6_36 : sub6 [-3, 0, 0] = true := by decide +kernel
theorem sub6_37 : sub6 [-3, 0, 1] = true := by decide +kernel
theorem sub6_38 : sub6 [-3, 0, 2] = true := by decide +kernel
theorem sub6_39 : sub6 [-3, 0, 3] = true := by decide +kernel
theorem sub6_40 : sub6 [-3, 0, 4] = true := by decide +kernel
theorem sub6_41 : sub6 [-3, 0, 5] = true := by decide +kernel
theorem sub6_42 : sub6 [-3, 0, 6] = true := by decide +kernel
theorem sub6_43 : sub6 [-3, 0, 7] = true := by decide +kernel
theorem sub6_44 : sub6 [-3, 0, 8] = true := by decide +kernel
theorem sub6_45 : sub6 [-3, 1, -9] = true := by decide +kernel
theorem sub6_46 : sub6 [-3, 1, -8] = true := by decide +kernel
theorem sub6_47 : sub6 [-3, 1, -7] = true := by decide +kernel
theorem sub6_48 : sub6 [-3, 1, -6] = true := by decide +kernel
theorem sub6_49 : sub6 [-3, 1, -5] = true := by decide +kernel
theorem sub6_50 : sub6 [-3, 1, -4] = true := by decide +kernel
theorem sub6_51 : sub6 [-3, 1, -3] = true := by decide +kernel
theorem sub6_52 : sub6 [-3, 1, -2] = true := by decide +kernel
theorem sub6_53 : sub6 [-3, 1, -1] = true := by decide +kernel
theorem sub6_54 : sub6 [-3, 1, 0] = true := by decide +kernel
theorem sub6_55 : sub6 [-3, 1, 1] = true := by decide +kernel
theorem sub6_56 : sub6 [-3, 1, 2] = true := by decide +kernel
theorem sub6_57 : sub6 [-3, 1, 3] = true := by decide +kernel
theorem sub6_58 : sub6 [-3, 1, 4] = true := by decide +kernel
theorem sub6_59 : sub6 [-3, 1, 5] = true := by decide +kernel
theorem sub6_60 : sub6 [-3, 1, 6] = true := by decide +kernel
theorem sub6_61 : sub6 [-3, 1, 7] = true := by decide +kernel
theorem sub6_62 : sub6 [-3, 1, 8] = true := by decide +kernel
theorem sub6_63 : sub6 [-3, 2, -8] = true := by decide +kernel
theorem sb6_1 : ∀ q ∈ blk6_1, sub6 q = true := by
  unfold blk6_1
  exact List.forall_mem_cons.2 ⟨sub6_32, List.forall_mem_cons.2 ⟨sub6_33, List.forall_mem_cons.2 ⟨sub6_34, List.forall_mem_cons.2 ⟨sub6_35, List.forall_mem_cons.2 ⟨sub6_36, List.forall_mem_cons.2 ⟨sub6_37, List.forall_mem_cons.2 ⟨sub6_38, List.forall_mem_cons.2 ⟨sub6_39, List.forall_mem_cons.2 ⟨sub6_40, List.forall_mem_cons.2 ⟨sub6_41, List.forall_mem_cons.2 ⟨sub6_42, List.forall_mem_cons.2 ⟨sub6_43, List.forall_mem_cons.2 ⟨sub6_44, List.forall_mem_cons.2 ⟨sub6_45, List.forall_mem_cons.2 ⟨sub6_46, List.forall_mem_cons.2 ⟨sub6_47, List.forall_mem_cons.2 ⟨sub6_48, List.forall_mem_cons.2 ⟨sub6_49, List.forall_mem_cons.2 ⟨sub6_50, List.forall_mem_cons.2 ⟨sub6_51, List.forall_mem_cons.2 ⟨sub6_52, List.forall_mem_cons.2 ⟨sub6_53, List.forall_mem_cons.2 ⟨sub6_54, List.forall_mem_cons.2 ⟨sub6_55, List.forall_mem_cons.2 ⟨sub6_56, List.forall_mem_cons.2 ⟨sub6_57, List.forall_mem_cons.2 ⟨sub6_58, List.forall_mem_cons.2 ⟨sub6_59, List.forall_mem_cons.2 ⟨sub6_60, List.forall_mem_cons.2 ⟨sub6_61, List.forall_mem_cons.2 ⟨sub6_62, List.forall_mem_cons.2 ⟨sub6_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_64 : sub6 [-3, 2, -7] = true := by decide +kernel
theorem sub6_65 : sub6 [-3, 2, -6] = true := by decide +kernel
theorem sub6_66 : sub6 [-3, 2, -5] = true := by decide +kernel
theorem sub6_67 : sub6 [-3, 2, -4] = true := by decide +kernel
theorem sub6_68 : sub6 [-3, 2, -3] = true := by decide +kernel
theorem sub6_69 : sub6 [-3, 2, -2] = true := by decide +kernel
theorem sub6_70 : sub6 [-3, 2, -1] = true := by decide +kernel
theorem sub6_71 : sub6 [-3, 2, 0] = true := by decide +kernel
theorem sub6_72 : sub6 [-3, 2, 1] = true := by decide +kernel
theorem sub6_73 : sub6 [-3, 2, 2] = true := by decide +kernel
theorem sub6_74 : sub6 [-3, 2, 3] = true := by decide +kernel
theorem sub6_75 : sub6 [-3, 2, 4] = true := by decide +kernel
theorem sub6_76 : sub6 [-3, 2, 5] = true := by decide +kernel
theorem sub6_77 : sub6 [-3, 2, 6] = true := by decide +kernel
theorem sub6_78 : sub6 [-3, 2, 7] = true := by decide +kernel
theorem sub6_79 : sub6 [-3, 3] = true := by decide +kernel
theorem sub6_80 : sub6 [-3, 4] = true := by decide +kernel
theorem sub6_81 : sub6 [-2, -4] = true := by decide +kernel
theorem sub6_82 : sub6 [-2, -3] = true := by decide +kernel
theorem sub6_83 : sub6 [-2, -2, -9] = true := by decide +kernel
theorem sub6_84 : sub6 [-2, -2, -8] = true := by decide +kernel
theorem sub6_85 : sub6 [-2, -2, -7] = true := by decide +kernel
theorem sub6_86 : sub6 [-2, -2, -6] = true := by decide +kernel
theorem sub6_87 : sub6 [-2, -2, -5] = true := by decide +kernel
theorem sub6_88 : sub6 [-2, -2, -4] = true := by decide +kernel
theorem sub6_89 : sub6 [-2, -2, -3] = true := by decide +kernel
theorem sub6_90 : sub6 [-2, -2, -2] = true := by decide +kernel
theorem sub6_91 : sub6 [-2, -2, -1] = true := by decide +kernel
theorem sub6_92 : sub6 [-2, -2, 0] = true := by decide +kernel
theorem sub6_93 : sub6 [-2, -2, 1] = true := by decide +kernel
theorem sub6_94 : sub6 [-2, -2, 2] = true := by decide +kernel
theorem sub6_95 : sub6 [-2, -2, 3] = true := by decide +kernel
theorem sb6_2 : ∀ q ∈ blk6_2, sub6 q = true := by
  unfold blk6_2
  exact List.forall_mem_cons.2 ⟨sub6_64, List.forall_mem_cons.2 ⟨sub6_65, List.forall_mem_cons.2 ⟨sub6_66, List.forall_mem_cons.2 ⟨sub6_67, List.forall_mem_cons.2 ⟨sub6_68, List.forall_mem_cons.2 ⟨sub6_69, List.forall_mem_cons.2 ⟨sub6_70, List.forall_mem_cons.2 ⟨sub6_71, List.forall_mem_cons.2 ⟨sub6_72, List.forall_mem_cons.2 ⟨sub6_73, List.forall_mem_cons.2 ⟨sub6_74, List.forall_mem_cons.2 ⟨sub6_75, List.forall_mem_cons.2 ⟨sub6_76, List.forall_mem_cons.2 ⟨sub6_77, List.forall_mem_cons.2 ⟨sub6_78, List.forall_mem_cons.2 ⟨sub6_79, List.forall_mem_cons.2 ⟨sub6_80, List.forall_mem_cons.2 ⟨sub6_81, List.forall_mem_cons.2 ⟨sub6_82, List.forall_mem_cons.2 ⟨sub6_83, List.forall_mem_cons.2 ⟨sub6_84, List.forall_mem_cons.2 ⟨sub6_85, List.forall_mem_cons.2 ⟨sub6_86, List.forall_mem_cons.2 ⟨sub6_87, List.forall_mem_cons.2 ⟨sub6_88, List.forall_mem_cons.2 ⟨sub6_89, List.forall_mem_cons.2 ⟨sub6_90, List.forall_mem_cons.2 ⟨sub6_91, List.forall_mem_cons.2 ⟨sub6_92, List.forall_mem_cons.2 ⟨sub6_93, List.forall_mem_cons.2 ⟨sub6_94, List.forall_mem_cons.2 ⟨sub6_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C059
