import ReflectZphi.Data.Cert5.C079.Base

namespace ReflectZphi.Data.Cert5.C079
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub5_1792 : sub5 [4, 1, 1] = true := by decide +kernel
theorem sub5_1793 : sub5 [4, 1, 2] = true := by decide +kernel
theorem sub5_1794 : sub5 [4, 1, 3] = true := by decide +kernel
theorem sub5_1795 : sub5 [4, 1, 4] = true := by decide +kernel
theorem sub5_1796 : sub5 [4, 1, 5] = true := by decide +kernel
theorem sub5_1797 : sub5 [4, 1, 6] = true := by decide +kernel
theorem sub5_1798 : sub5 [4, 1, 7] = true := by decide +kernel
theorem sub5_1799 : sub5 [4, 2, -11] = true := by decide +kernel
theorem sub5_1800 : sub5 [4, 2, -10] = true := by decide +kernel
theorem sub5_1801 : sub5 [4, 2, -9] = true := by decide +kernel
theorem sub5_1802 : sub5 [4, 2, -8] = true := by decide +kernel
theorem sub5_1803 : sub5 [4, 2, -7] = true := by decide +kernel
theorem sub5_1804 : sub5 [4, 2, -6] = true := by decide +kernel
theorem sub5_1805 : sub5 [4, 2, -5] = true := by decide +kernel
theorem sub5_1806 : sub5 [4, 2, -4] = true := by decide +kernel
theorem sub5_1807 : sub5 [4, 2, -3] = true := by decide +kernel
theorem sub5_1808 : sub5 [4, 2, -2] = true := by decide +kernel
theorem sub5_1809 : sub5 [4, 2, -1] = true := by decide +kernel
theorem sub5_1810 : sub5 [4, 2, 0] = true := by decide +kernel
theorem sub5_1811 : sub5 [4, 2, 1] = true := by decide +kernel
theorem sub5_1812 : sub5 [4, 2, 2] = true := by decide +kernel
theorem sub5_1813 : sub5 [4, 2, 3] = true := by decide +kernel
theorem sub5_1814 : sub5 [4, 2, 4] = true := by decide +kernel
theorem sub5_1815 : sub5 [4, 2, 5] = true := by decide +kernel
theorem sub5_1816 : sub5 [4, 2, 6] = true := by decide +kernel
theorem sub5_1817 : sub5 [4, 2, 7] = true := by decide +kernel
theorem sub5_1818 : sub5 [4, 3, -9] = true := by decide +kernel
theorem sub5_1819 : sub5 [4, 3, -8] = true := by decide +kernel
theorem sub5_1820 : sub5 [4, 3, -7] = true := by decide +kernel
theorem sub5_1821 : sub5 [4, 3, -6] = true := by decide +kernel
theorem sub5_1822 : sub5 [4, 3, -5] = true := by decide +kernel
theorem sub5_1823 : sub5 [4, 3, -4] = true := by decide +kernel
theorem sb5_56 : ∀ q ∈ blk5_56, sub5 q = true := by
  unfold blk5_56
  exact List.forall_mem_cons.2 ⟨sub5_1792, List.forall_mem_cons.2 ⟨sub5_1793, List.forall_mem_cons.2 ⟨sub5_1794, List.forall_mem_cons.2 ⟨sub5_1795, List.forall_mem_cons.2 ⟨sub5_1796, List.forall_mem_cons.2 ⟨sub5_1797, List.forall_mem_cons.2 ⟨sub5_1798, List.forall_mem_cons.2 ⟨sub5_1799, List.forall_mem_cons.2 ⟨sub5_1800, List.forall_mem_cons.2 ⟨sub5_1801, List.forall_mem_cons.2 ⟨sub5_1802, List.forall_mem_cons.2 ⟨sub5_1803, List.forall_mem_cons.2 ⟨sub5_1804, List.forall_mem_cons.2 ⟨sub5_1805, List.forall_mem_cons.2 ⟨sub5_1806, List.forall_mem_cons.2 ⟨sub5_1807, List.forall_mem_cons.2 ⟨sub5_1808, List.forall_mem_cons.2 ⟨sub5_1809, List.forall_mem_cons.2 ⟨sub5_1810, List.forall_mem_cons.2 ⟨sub5_1811, List.forall_mem_cons.2 ⟨sub5_1812, List.forall_mem_cons.2 ⟨sub5_1813, List.forall_mem_cons.2 ⟨sub5_1814, List.forall_mem_cons.2 ⟨sub5_1815, List.forall_mem_cons.2 ⟨sub5_1816, List.forall_mem_cons.2 ⟨sub5_1817, List.forall_mem_cons.2 ⟨sub5_1818, List.forall_mem_cons.2 ⟨sub5_1819, List.forall_mem_cons.2 ⟨sub5_1820, List.forall_mem_cons.2 ⟨sub5_1821, List.forall_mem_cons.2 ⟨sub5_1822, List.forall_mem_cons.2 ⟨sub5_1823, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_1824 : sub5 [4, 3, -3] = true := by decide +kernel
theorem sub5_1825 : sub5 [4, 3, -2] = true := by decide +kernel
theorem sub5_1826 : sub5 [4, 3, -1] = true := by decide +kernel
theorem sub5_1827 : sub5 [4, 3, 0] = true := by decide +kernel
theorem sub5_1828 : sub5 [4, 3, 1] = true := by decide +kernel
theorem sub5_1829 : sub5 [4, 3, 2] = true := by decide +kernel
theorem sub5_1830 : sub5 [4, 3, 3] = true := by decide +kernel
theorem sub5_1831 : sub5 [4, 3, 4] = true := by decide +kernel
theorem sub5_1832 : sub5 [4, 3, 5] = true := by decide +kernel
theorem sub5_1833 : sub5 [4, 3, 6] = true := by decide +kernel
theorem sub5_1834 : sub5 [4, 4] = true := by decide +kernel
theorem sub5_1835 : sub5 [5, -3] = true := by decide +kernel
theorem sub5_1836 : sub5 [5, -2] = true := by decide +kernel
theorem sub5_1837 : sub5 [5, -1, -9] = true := by decide +kernel
theorem sub5_1838 : sub5 [5, -1, -8] = true := by decide +kernel
theorem sub5_1839 : sub5 [5, -1, -7] = true := by decide +kernel
theorem sub5_1840 : sub5 [5, -1, -6] = true := by decide +kernel
theorem sub5_1841 : sub5 [5, -1, -5] = true := by decide +kernel
theorem sub5_1842 : sub5 [5, -1, -4] = true := by decide +kernel
theorem sub5_1843 : sub5 [5, -1, -3] = true := by decide +kernel
theorem sub5_1844 : sub5 [5, -1, -2] = true := by decide +kernel
theorem sub5_1845 : sub5 [5, -1, -1] = true := by decide +kernel
theorem sub5_1846 : sub5 [5, -1, 0] = true := by decide +kernel
theorem sub5_1847 : sub5 [5, -1, 1] = true := by decide +kernel
theorem sub5_1848 : sub5 [5, -1, 2] = true := by decide +kernel
theorem sub5_1849 : sub5 [5, -1, 3] = true := by decide +kernel
theorem sub5_1850 : sub5 [5, -1, 4] = true := by decide +kernel
theorem sub5_1851 : sub5 [5, 0, -9] = true := by decide +kernel
theorem sub5_1852 : sub5 [5, 0, -8] = true := by decide +kernel
theorem sub5_1853 : sub5 [5, 0, -7] = true := by decide +kernel
theorem sub5_1854 : sub5 [5, 0, -6] = true := by decide +kernel
theorem sub5_1855 : sub5 [5, 0, -5] = true := by decide +kernel
theorem sb5_57 : ∀ q ∈ blk5_57, sub5 q = true := by
  unfold blk5_57
  exact List.forall_mem_cons.2 ⟨sub5_1824, List.forall_mem_cons.2 ⟨sub5_1825, List.forall_mem_cons.2 ⟨sub5_1826, List.forall_mem_cons.2 ⟨sub5_1827, List.forall_mem_cons.2 ⟨sub5_1828, List.forall_mem_cons.2 ⟨sub5_1829, List.forall_mem_cons.2 ⟨sub5_1830, List.forall_mem_cons.2 ⟨sub5_1831, List.forall_mem_cons.2 ⟨sub5_1832, List.forall_mem_cons.2 ⟨sub5_1833, List.forall_mem_cons.2 ⟨sub5_1834, List.forall_mem_cons.2 ⟨sub5_1835, List.forall_mem_cons.2 ⟨sub5_1836, List.forall_mem_cons.2 ⟨sub5_1837, List.forall_mem_cons.2 ⟨sub5_1838, List.forall_mem_cons.2 ⟨sub5_1839, List.forall_mem_cons.2 ⟨sub5_1840, List.forall_mem_cons.2 ⟨sub5_1841, List.forall_mem_cons.2 ⟨sub5_1842, List.forall_mem_cons.2 ⟨sub5_1843, List.forall_mem_cons.2 ⟨sub5_1844, List.forall_mem_cons.2 ⟨sub5_1845, List.forall_mem_cons.2 ⟨sub5_1846, List.forall_mem_cons.2 ⟨sub5_1847, List.forall_mem_cons.2 ⟨sub5_1848, List.forall_mem_cons.2 ⟨sub5_1849, List.forall_mem_cons.2 ⟨sub5_1850, List.forall_mem_cons.2 ⟨sub5_1851, List.forall_mem_cons.2 ⟨sub5_1852, List.forall_mem_cons.2 ⟨sub5_1853, List.forall_mem_cons.2 ⟨sub5_1854, List.forall_mem_cons.2 ⟨sub5_1855, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_1856 : sub5 [5, 0, -4] = true := by decide +kernel
theorem sub5_1857 : sub5 [5, 0, -3] = true := by decide +kernel
theorem sub5_1858 : sub5 [5, 0, -2] = true := by decide +kernel
theorem sub5_1859 : sub5 [5, 0, -1] = true := by decide +kernel
theorem sub5_1860 : sub5 [5, 0, 0] = true := by decide +kernel
theorem sub5_1861 : sub5 [5, 0, 1] = true := by decide +kernel
theorem sub5_1862 : sub5 [5, 0, 2] = true := by decide +kernel
theorem sub5_1863 : sub5 [5, 0, 3] = true := by decide +kernel
theorem sub5_1864 : sub5 [5, 0, 4] = true := by decide +kernel
theorem sub5_1865 : sub5 [5, 1, -9] = true := by decide +kernel
theorem sub5_1866 : sub5 [5, 1, -8] = true := by decide +kernel
theorem sub5_1867 : sub5 [5, 1, -7] = true := by decide +kernel
theorem sub5_1868 : sub5 [5, 1, -6] = true := by decide +kernel
theorem sub5_1869 : sub5 [5, 1, -5] = true := by decide +kernel
theorem sub5_1870 : sub5 [5, 1, -4] = true := by decide +kernel
theorem sub5_1871 : sub5 [5, 1, -3] = true := by decide +kernel
theorem sub5_1872 : sub5 [5, 1, -2] = true := by decide +kernel
theorem sub5_1873 : sub5 [5, 1, -1] = true := by decide +kernel
theorem sub5_1874 : sub5 [5, 1, 0] = true := by decide +kernel
theorem sub5_1875 : sub5 [5, 1, 1] = true := by decide +kernel
theorem sub5_1876 : sub5 [5, 1, 2] = true := by decide +kernel
theorem sub5_1877 : sub5 [5, 1, 3] = true := by decide +kernel
theorem sub5_1878 : sub5 [5, 1, 4] = true := by decide +kernel
theorem sub5_1879 : sub5 [5, 2] = true := by decide +kernel
theorem sub5_1880 : sub5 [5, 3] = true := by decide +kernel
theorem sb5_58 : ∀ q ∈ blk5_58, sub5 q = true := by
  unfold blk5_58
  exact List.forall_mem_cons.2 ⟨sub5_1856, List.forall_mem_cons.2 ⟨sub5_1857, List.forall_mem_cons.2 ⟨sub5_1858, List.forall_mem_cons.2 ⟨sub5_1859, List.forall_mem_cons.2 ⟨sub5_1860, List.forall_mem_cons.2 ⟨sub5_1861, List.forall_mem_cons.2 ⟨sub5_1862, List.forall_mem_cons.2 ⟨sub5_1863, List.forall_mem_cons.2 ⟨sub5_1864, List.forall_mem_cons.2 ⟨sub5_1865, List.forall_mem_cons.2 ⟨sub5_1866, List.forall_mem_cons.2 ⟨sub5_1867, List.forall_mem_cons.2 ⟨sub5_1868, List.forall_mem_cons.2 ⟨sub5_1869, List.forall_mem_cons.2 ⟨sub5_1870, List.forall_mem_cons.2 ⟨sub5_1871, List.forall_mem_cons.2 ⟨sub5_1872, List.forall_mem_cons.2 ⟨sub5_1873, List.forall_mem_cons.2 ⟨sub5_1874, List.forall_mem_cons.2 ⟨sub5_1875, List.forall_mem_cons.2 ⟨sub5_1876, List.forall_mem_cons.2 ⟨sub5_1877, List.forall_mem_cons.2 ⟨sub5_1878, List.forall_mem_cons.2 ⟨sub5_1879, List.forall_mem_cons.2 ⟨sub5_1880, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_0 : sub6 [-7, 0] = true := by decide +kernel
theorem sub6_1 : sub6 [-7, 1] = true := by decide +kernel
theorem sub6_2 : sub6 [-7, 2] = true := by decide +kernel
theorem sub6_3 : sub6 [-7, 3] = true := by decide +kernel
theorem sub6_4 : sub6 [-7, 4] = true := by decide +kernel
theorem sub6_5 : sub6 [-7, 5] = true := by decide +kernel
theorem sub6_6 : sub6 [-7, 6] = true := by decide +kernel
theorem sub6_7 : sub6 [-6, -2] = true := by decide +kernel
theorem sub6_8 : sub6 [-6, -1] = true := by decide +kernel
theorem sub6_9 : sub6 [-6, 0] = true := by decide +kernel
theorem sub6_10 : sub6 [-6, 1] = true := by decide +kernel
theorem sub6_11 : sub6 [-6, 2] = true := by decide +kernel
theorem sub6_12 : sub6 [-6, 3, -9] = true := by decide +kernel
theorem sub6_13 : sub6 [-6, 3, -8] = true := by decide +kernel
theorem sub6_14 : sub6 [-6, 3, -7] = true := by decide +kernel
theorem sub6_15 : sub6 [-6, 3, -6] = true := by decide +kernel
theorem sub6_16 : sub6 [-6, 3, -5] = true := by decide +kernel
theorem sub6_17 : sub6 [-6, 3, -4] = true := by decide +kernel
theorem sub6_18 : sub6 [-6, 3, -3] = true := by decide +kernel
theorem sub6_19 : sub6 [-6, 3, -2] = true := by decide +kernel
theorem sub6_20 : sub6 [-6, 3, -1] = true := by decide +kernel
theorem sub6_21 : sub6 [-6, 3, 0] = true := by decide +kernel
theorem sub6_22 : sub6 [-6, 3, 1] = true := by decide +kernel
theorem sub6_23 : sub6 [-6, 3, 2] = true := by decide +kernel
theorem sub6_24 : sub6 [-6, 3, 3] = true := by decide +kernel
theorem sub6_25 : sub6 [-6, 4] = true := by decide +kernel
theorem sub6_26 : sub6 [-6, 5] = true := by decide +kernel
theorem sub6_27 : sub6 [-6, 6] = true := by decide +kernel
theorem sub6_28 : sub6 [-6, 7] = true := by decide +kernel
theorem sub6_29 : sub6 [-5, -4] = true := by decide +kernel
theorem sub6_30 : sub6 [-5, -3] = true := by decide +kernel
theorem sub6_31 : sub6 [-5, -2] = true := by decide +kernel
theorem sb6_0 : ∀ q ∈ blk6_0, sub6 q = true := by
  unfold blk6_0
  exact List.forall_mem_cons.2 ⟨sub6_0, List.forall_mem_cons.2 ⟨sub6_1, List.forall_mem_cons.2 ⟨sub6_2, List.forall_mem_cons.2 ⟨sub6_3, List.forall_mem_cons.2 ⟨sub6_4, List.forall_mem_cons.2 ⟨sub6_5, List.forall_mem_cons.2 ⟨sub6_6, List.forall_mem_cons.2 ⟨sub6_7, List.forall_mem_cons.2 ⟨sub6_8, List.forall_mem_cons.2 ⟨sub6_9, List.forall_mem_cons.2 ⟨sub6_10, List.forall_mem_cons.2 ⟨sub6_11, List.forall_mem_cons.2 ⟨sub6_12, List.forall_mem_cons.2 ⟨sub6_13, List.forall_mem_cons.2 ⟨sub6_14, List.forall_mem_cons.2 ⟨sub6_15, List.forall_mem_cons.2 ⟨sub6_16, List.forall_mem_cons.2 ⟨sub6_17, List.forall_mem_cons.2 ⟨sub6_18, List.forall_mem_cons.2 ⟨sub6_19, List.forall_mem_cons.2 ⟨sub6_20, List.forall_mem_cons.2 ⟨sub6_21, List.forall_mem_cons.2 ⟨sub6_22, List.forall_mem_cons.2 ⟨sub6_23, List.forall_mem_cons.2 ⟨sub6_24, List.forall_mem_cons.2 ⟨sub6_25, List.forall_mem_cons.2 ⟨sub6_26, List.forall_mem_cons.2 ⟨sub6_27, List.forall_mem_cons.2 ⟨sub6_28, List.forall_mem_cons.2 ⟨sub6_29, List.forall_mem_cons.2 ⟨sub6_30, List.forall_mem_cons.2 ⟨sub6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_32 : sub6 [-5, -1, -7] = true := by decide +kernel
theorem sub6_33 : sub6 [-5, -1, -6] = true := by decide +kernel
theorem sub6_34 : sub6 [-5, -1, -5] = true := by decide +kernel
theorem sub6_35 : sub6 [-5, -1, -4] = true := by decide +kernel
theorem sub6_36 : sub6 [-5, -1, -3] = true := by decide +kernel
theorem sub6_37 : sub6 [-5, -1, -2] = true := by decide +kernel
theorem sub6_38 : sub6 [-5, -1, -1] = true := by decide +kernel
theorem sub6_39 : sub6 [-5, -1, 0] = true := by decide +kernel
theorem sub6_40 : sub6 [-5, -1, 1] = true := by decide +kernel
theorem sub6_41 : sub6 [-5, -1, 2] = true := by decide +kernel
theorem sub6_42 : sub6 [-5, -1, 3] = true := by decide +kernel
theorem sub6_43 : sub6 [-5, -1, 4] = true := by decide +kernel
theorem sub6_44 : sub6 [-5, -1, 5] = true := by decide +kernel
theorem sub6_45 : sub6 [-5, -1, 6] = true := by decide +kernel
theorem sub6_46 : sub6 [-5, 0, -8] = true := by decide +kernel
theorem sub6_47 : sub6 [-5, 0, -7] = true := by decide +kernel
theorem sub6_48 : sub6 [-5, 0, -6] = true := by decide +kernel
theorem sub6_49 : sub6 [-5, 0, -5] = true := by decide +kernel
theorem sub6_50 : sub6 [-5, 0, -4] = true := by decide +kernel
theorem sub6_51 : sub6 [-5, 0, -3] = true := by decide +kernel
theorem sub6_52 : sub6 [-5, 0, -2] = true := by decide +kernel
theorem sub6_53 : sub6 [-5, 0, -1] = true := by decide +kernel
theorem sub6_54 : sub6 [-5, 0, 0] = true := by decide +kernel
theorem sub6_55 : sub6 [-5, 0, 1] = true := by decide +kernel
theorem sub6_56 : sub6 [-5, 0, 2] = true := by decide +kernel
theorem sub6_57 : sub6 [-5, 0, 3] = true := by decide +kernel
theorem sub6_58 : sub6 [-5, 0, 4] = true := by decide +kernel
theorem sub6_59 : sub6 [-5, 0, 5] = true := by decide +kernel
theorem sub6_60 : sub6 [-5, 0, 6] = true := by decide +kernel
theorem sub6_61 : sub6 [-5, 1, -9] = true := by decide +kernel
theorem sub6_62 : sub6 [-5, 1, -8] = true := by decide +kernel
theorem sub6_63 : sub6 [-5, 1, -7] = true := by decide +kernel
theorem sb6_1 : ∀ q ∈ blk6_1, sub6 q = true := by
  unfold blk6_1
  exact List.forall_mem_cons.2 ⟨sub6_32, List.forall_mem_cons.2 ⟨sub6_33, List.forall_mem_cons.2 ⟨sub6_34, List.forall_mem_cons.2 ⟨sub6_35, List.forall_mem_cons.2 ⟨sub6_36, List.forall_mem_cons.2 ⟨sub6_37, List.forall_mem_cons.2 ⟨sub6_38, List.forall_mem_cons.2 ⟨sub6_39, List.forall_mem_cons.2 ⟨sub6_40, List.forall_mem_cons.2 ⟨sub6_41, List.forall_mem_cons.2 ⟨sub6_42, List.forall_mem_cons.2 ⟨sub6_43, List.forall_mem_cons.2 ⟨sub6_44, List.forall_mem_cons.2 ⟨sub6_45, List.forall_mem_cons.2 ⟨sub6_46, List.forall_mem_cons.2 ⟨sub6_47, List.forall_mem_cons.2 ⟨sub6_48, List.forall_mem_cons.2 ⟨sub6_49, List.forall_mem_cons.2 ⟨sub6_50, List.forall_mem_cons.2 ⟨sub6_51, List.forall_mem_cons.2 ⟨sub6_52, List.forall_mem_cons.2 ⟨sub6_53, List.forall_mem_cons.2 ⟨sub6_54, List.forall_mem_cons.2 ⟨sub6_55, List.forall_mem_cons.2 ⟨sub6_56, List.forall_mem_cons.2 ⟨sub6_57, List.forall_mem_cons.2 ⟨sub6_58, List.forall_mem_cons.2 ⟨sub6_59, List.forall_mem_cons.2 ⟨sub6_60, List.forall_mem_cons.2 ⟨sub6_61, List.forall_mem_cons.2 ⟨sub6_62, List.forall_mem_cons.2 ⟨sub6_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_64 : sub6 [-5, 1, -6] = true := by decide +kernel
theorem sub6_65 : sub6 [-5, 1, -5] = true := by decide +kernel
theorem sub6_66 : sub6 [-5, 1, -4] = true := by decide +kernel
theorem sub6_67 : sub6 [-5, 1, -3] = true := by decide +kernel
theorem sub6_68 : sub6 [-5, 1, -2] = true := by decide +kernel
theorem sub6_69 : sub6 [-5, 1, -1] = true := by decide +kernel
theorem sub6_70 : sub6 [-5, 1, 0] = true := by decide +kernel
theorem sub6_71 : sub6 [-5, 1, 1] = true := by decide +kernel
theorem sub6_72 : sub6 [-5, 1, 2] = true := by decide +kernel
theorem sub6_73 : sub6 [-5, 1, 3] = true := by decide +kernel
theorem sub6_74 : sub6 [-5, 1, 4] = true := by decide +kernel
theorem sub6_75 : sub6 [-5, 1, 5] = true := by decide +kernel
theorem sub6_76 : sub6 [-5, 1, 6] = true := by decide +kernel
theorem sub6_77 : sub6 [-5, 2, -10] = true := by decide +kernel
theorem sub6_78 : sub6 [-5, 2, -9] = true := by decide +kernel
theorem sub6_79 : sub6 [-5, 2, -8] = true := by decide +kernel
theorem sub6_80 : sub6 [-5, 2, -7] = true := by decide +kernel
theorem sub6_81 : sub6 [-5, 2, -6] = true := by decide +kernel
theorem sub6_82 : sub6 [-5, 2, -5] = true := by decide +kernel
theorem sub6_83 : sub6 [-5, 2, -4] = true := by decide +kernel
theorem sub6_84 : sub6 [-5, 2, -3] = true := by decide +kernel
theorem sub6_85 : sub6 [-5, 2, -2] = true := by decide +kernel
theorem sub6_86 : sub6 [-5, 2, -1] = true := by decide +kernel
theorem sub6_87 : sub6 [-5, 2, 0] = true := by decide +kernel
theorem sub6_88 : sub6 [-5, 2, 1] = true := by decide +kernel
theorem sub6_89 : sub6 [-5, 2, 2] = true := by decide +kernel
theorem sub6_90 : sub6 [-5, 2, 3] = true := by decide +kernel
theorem sub6_91 : sub6 [-5, 2, 4] = true := by decide +kernel
theorem sub6_92 : sub6 [-5, 2, 5] = true := by decide +kernel
theorem sub6_93 : sub6 [-5, 2, 6] = true := by decide +kernel
theorem sub6_94 : sub6 [-5, 3, -10] = true := by decide +kernel
theorem sub6_95 : sub6 [-5, 3, -9] = true := by decide +kernel
theorem sb6_2 : ∀ q ∈ blk6_2, sub6 q = true := by
  unfold blk6_2
  exact List.forall_mem_cons.2 ⟨sub6_64, List.forall_mem_cons.2 ⟨sub6_65, List.forall_mem_cons.2 ⟨sub6_66, List.forall_mem_cons.2 ⟨sub6_67, List.forall_mem_cons.2 ⟨sub6_68, List.forall_mem_cons.2 ⟨sub6_69, List.forall_mem_cons.2 ⟨sub6_70, List.forall_mem_cons.2 ⟨sub6_71, List.forall_mem_cons.2 ⟨sub6_72, List.forall_mem_cons.2 ⟨sub6_73, List.forall_mem_cons.2 ⟨sub6_74, List.forall_mem_cons.2 ⟨sub6_75, List.forall_mem_cons.2 ⟨sub6_76, List.forall_mem_cons.2 ⟨sub6_77, List.forall_mem_cons.2 ⟨sub6_78, List.forall_mem_cons.2 ⟨sub6_79, List.forall_mem_cons.2 ⟨sub6_80, List.forall_mem_cons.2 ⟨sub6_81, List.forall_mem_cons.2 ⟨sub6_82, List.forall_mem_cons.2 ⟨sub6_83, List.forall_mem_cons.2 ⟨sub6_84, List.forall_mem_cons.2 ⟨sub6_85, List.forall_mem_cons.2 ⟨sub6_86, List.forall_mem_cons.2 ⟨sub6_87, List.forall_mem_cons.2 ⟨sub6_88, List.forall_mem_cons.2 ⟨sub6_89, List.forall_mem_cons.2 ⟨sub6_90, List.forall_mem_cons.2 ⟨sub6_91, List.forall_mem_cons.2 ⟨sub6_92, List.forall_mem_cons.2 ⟨sub6_93, List.forall_mem_cons.2 ⟨sub6_94, List.forall_mem_cons.2 ⟨sub6_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_96 : sub6 [-5, 3, -8] = true := by decide +kernel
theorem sub6_97 : sub6 [-5, 3, -7] = true := by decide +kernel
theorem sub6_98 : sub6 [-5, 3, -6] = true := by decide +kernel
theorem sub6_99 : sub6 [-5, 3, -5] = true := by decide +kernel
theorem sub6_100 : sub6 [-5, 3, -4] = true := by decide +kernel
theorem sub6_101 : sub6 [-5, 3, -3] = true := by decide +kernel
theorem sub6_102 : sub6 [-5, 3, -2] = true := by decide +kernel
theorem sub6_103 : sub6 [-5, 3, -1] = true := by decide +kernel
theorem sub6_104 : sub6 [-5, 3, 0] = true := by decide +kernel
theorem sub6_105 : sub6 [-5, 3, 1] = true := by decide +kernel
theorem sub6_106 : sub6 [-5, 3, 2] = true := by decide +kernel
theorem sub6_107 : sub6 [-5, 3, 3] = true := by decide +kernel
theorem sub6_108 : sub6 [-5, 3, 4] = true := by decide +kernel
theorem sub6_109 : sub6 [-5, 3, 5] = true := by decide +kernel
theorem sub6_110 : sub6 [-5, 4, -11] = true := by decide +kernel
theorem sub6_111 : sub6 [-5, 4, -10] = true := by decide +kernel
theorem sub6_112 : sub6 [-5, 4, -9] = true := by decide +kernel
theorem sub6_113 : sub6 [-5, 4, -8] = true := by decide +kernel
theorem sub6_114 : sub6 [-5, 4, -7] = true := by decide +kernel
theorem sub6_115 : sub6 [-5, 4, -6] = true := by decide +kernel
theorem sub6_116 : sub6 [-5, 4, -5] = true := by decide +kernel
theorem sub6_117 : sub6 [-5, 4, -4] = true := by decide +kernel
theorem sub6_118 : sub6 [-5, 4, -3] = true := by decide +kernel
theorem sub6_119 : sub6 [-5, 4, -2] = true := by decide +kernel
theorem sub6_120 : sub6 [-5, 4, -1] = true := by decide +kernel
theorem sub6_121 : sub6 [-5, 4, 0] = true := by decide +kernel
theorem sub6_122 : sub6 [-5, 4, 1] = true := by decide +kernel
theorem sub6_123 : sub6 [-5, 4, 2] = true := by decide +kernel
theorem sub6_124 : sub6 [-5, 4, 3] = true := by decide +kernel
theorem sub6_125 : sub6 [-5, 4, 4] = true := by decide +kernel
theorem sub6_126 : sub6 [-5, 5, -11] = true := by decide +kernel
theorem sub6_127 : sub6 [-5, 5, -10] = true := by decide +kernel
theorem sb6_3 : ∀ q ∈ blk6_3, sub6 q = true := by
  unfold blk6_3
  exact List.forall_mem_cons.2 ⟨sub6_96, List.forall_mem_cons.2 ⟨sub6_97, List.forall_mem_cons.2 ⟨sub6_98, List.forall_mem_cons.2 ⟨sub6_99, List.forall_mem_cons.2 ⟨sub6_100, List.forall_mem_cons.2 ⟨sub6_101, List.forall_mem_cons.2 ⟨sub6_102, List.forall_mem_cons.2 ⟨sub6_103, List.forall_mem_cons.2 ⟨sub6_104, List.forall_mem_cons.2 ⟨sub6_105, List.forall_mem_cons.2 ⟨sub6_106, List.forall_mem_cons.2 ⟨sub6_107, List.forall_mem_cons.2 ⟨sub6_108, List.forall_mem_cons.2 ⟨sub6_109, List.forall_mem_cons.2 ⟨sub6_110, List.forall_mem_cons.2 ⟨sub6_111, List.forall_mem_cons.2 ⟨sub6_112, List.forall_mem_cons.2 ⟨sub6_113, List.forall_mem_cons.2 ⟨sub6_114, List.forall_mem_cons.2 ⟨sub6_115, List.forall_mem_cons.2 ⟨sub6_116, List.forall_mem_cons.2 ⟨sub6_117, List.forall_mem_cons.2 ⟨sub6_118, List.forall_mem_cons.2 ⟨sub6_119, List.forall_mem_cons.2 ⟨sub6_120, List.forall_mem_cons.2 ⟨sub6_121, List.forall_mem_cons.2 ⟨sub6_122, List.forall_mem_cons.2 ⟨sub6_123, List.forall_mem_cons.2 ⟨sub6_124, List.forall_mem_cons.2 ⟨sub6_125, List.forall_mem_cons.2 ⟨sub6_126, List.forall_mem_cons.2 ⟨sub6_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_128 : sub6 [-5, 5, -9] = true := by decide +kernel
theorem sub6_129 : sub6 [-5, 5, -8] = true := by decide +kernel
theorem sub6_130 : sub6 [-5, 5, -7] = true := by decide +kernel
theorem sub6_131 : sub6 [-5, 5, -6] = true := by decide +kernel
theorem sub6_132 : sub6 [-5, 5, -5] = true := by decide +kernel
theorem sub6_133 : sub6 [-5, 5, -4] = true := by decide +kernel
theorem sub6_134 : sub6 [-5, 5, -3] = true := by decide +kernel
theorem sub6_135 : sub6 [-5, 5, -2] = true := by decide +kernel
theorem sub6_136 : sub6 [-5, 5, -1] = true := by decide +kernel
theorem sub6_137 : sub6 [-5, 5, 0] = true := by decide +kernel
theorem sub6_138 : sub6 [-5, 5, 1] = true := by decide +kernel
theorem sub6_139 : sub6 [-5, 5, 2] = true := by decide +kernel
theorem sub6_140 : sub6 [-5, 5, 3] = true := by decide +kernel
theorem sub6_141 : sub6 [-5, 5, 4] = true := by decide +kernel
theorem sub6_142 : sub6 [-5, 6, -10] = true := by decide +kernel
theorem sub6_143 : sub6 [-5, 6, -9] = true := by decide +kernel
theorem sub6_144 : sub6 [-5, 6, -8] = true := by decide +kernel
theorem sub6_145 : sub6 [-5, 6, -7] = true := by decide +kernel
theorem sub6_146 : sub6 [-5, 6, -6] = true := by decide +kernel
theorem sub6_147 : sub6 [-5, 6, -5] = true := by decide +kernel
theorem sub6_148 : sub6 [-5, 6, -4] = true := by decide +kernel
theorem sub6_149 : sub6 [-5, 6, -3] = true := by decide +kernel
theorem sub6_150 : sub6 [-5, 6, -2] = true := by decide +kernel
theorem sub6_151 : sub6 [-5, 6, -1] = true := by decide +kernel
theorem sub6_152 : sub6 [-5, 6, 0] = true := by decide +kernel
theorem sub6_153 : sub6 [-5, 6, 1] = true := by decide +kernel
theorem sub6_154 : sub6 [-5, 6, 2] = true := by decide +kernel
theorem sub6_155 : sub6 [-5, 7] = true := by decide +kernel
theorem sub6_156 : sub6 [-5, 8] = true := by decide +kernel
theorem sub6_157 : sub6 [-4, -6] = true := by decide +kernel
theorem sub6_158 : sub6 [-4, -5] = true := by decide +kernel
theorem sub6_159 : sub6 [-4, -4] = true := by decide +kernel
theorem sb6_4 : ∀ q ∈ blk6_4, sub6 q = true := by
  unfold blk6_4
  exact List.forall_mem_cons.2 ⟨sub6_128, List.forall_mem_cons.2 ⟨sub6_129, List.forall_mem_cons.2 ⟨sub6_130, List.forall_mem_cons.2 ⟨sub6_131, List.forall_mem_cons.2 ⟨sub6_132, List.forall_mem_cons.2 ⟨sub6_133, List.forall_mem_cons.2 ⟨sub6_134, List.forall_mem_cons.2 ⟨sub6_135, List.forall_mem_cons.2 ⟨sub6_136, List.forall_mem_cons.2 ⟨sub6_137, List.forall_mem_cons.2 ⟨sub6_138, List.forall_mem_cons.2 ⟨sub6_139, List.forall_mem_cons.2 ⟨sub6_140, List.forall_mem_cons.2 ⟨sub6_141, List.forall_mem_cons.2 ⟨sub6_142, List.forall_mem_cons.2 ⟨sub6_143, List.forall_mem_cons.2 ⟨sub6_144, List.forall_mem_cons.2 ⟨sub6_145, List.forall_mem_cons.2 ⟨sub6_146, List.forall_mem_cons.2 ⟨sub6_147, List.forall_mem_cons.2 ⟨sub6_148, List.forall_mem_cons.2 ⟨sub6_149, List.forall_mem_cons.2 ⟨sub6_150, List.forall_mem_cons.2 ⟨sub6_151, List.forall_mem_cons.2 ⟨sub6_152, List.forall_mem_cons.2 ⟨sub6_153, List.forall_mem_cons.2 ⟨sub6_154, List.forall_mem_cons.2 ⟨sub6_155, List.forall_mem_cons.2 ⟨sub6_156, List.forall_mem_cons.2 ⟨sub6_157, List.forall_mem_cons.2 ⟨sub6_158, List.forall_mem_cons.2 ⟨sub6_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_160 : sub6 [-4, -3, -6] = true := by decide +kernel
theorem sub6_161 : sub6 [-4, -3, -5] = true := by decide +kernel
theorem sub6_162 : sub6 [-4, -3, -4] = true := by decide +kernel
theorem sub6_163 : sub6 [-4, -3, -3] = true := by decide +kernel
theorem sub6_164 : sub6 [-4, -3, -2] = true := by decide +kernel
theorem sub6_165 : sub6 [-4, -3, -1] = true := by decide +kernel
theorem sub6_166 : sub6 [-4, -3, 0] = true := by decide +kernel
theorem sub6_167 : sub6 [-4, -3, 1] = true := by decide +kernel
theorem sub6_168 : sub6 [-4, -3, 2] = true := by decide +kernel
theorem sub6_169 : sub6 [-4, -3, 3] = true := by decide +kernel
theorem sub6_170 : sub6 [-4, -3, 4] = true := by decide +kernel
theorem sub6_171 : sub6 [-4, -3, 5] = true := by decide +kernel
theorem sub6_172 : sub6 [-4, -3, 6] = true := by decide +kernel
theorem sub6_173 : sub6 [-4, -2, -8] = true := by decide +kernel
theorem sub6_174 : sub6 [-4, -2, -7] = true := by decide +kernel
theorem sub6_175 : sub6 [-4, -2, -6] = true := by decide +kernel
theorem sub6_176 : sub6 [-4, -2, -5] = true := by decide +kernel
theorem sub6_177 : sub6 [-4, -2, -4] = true := by decide +kernel
theorem sub6_178 : sub6 [-4, -2, -3] = true := by decide +kernel
theorem sub6_179 : sub6 [-4, -2, -2] = true := by decide +kernel
theorem sub6_180 : sub6 [-4, -2, -1] = true := by decide +kernel
theorem sub6_181 : sub6 [-4, -2, 0] = true := by decide +kernel
theorem sub6_182 : sub6 [-4, -2, 1] = true := by decide +kernel
theorem sub6_183 : sub6 [-4, -2, 2] = true := by decide +kernel
theorem sub6_184 : sub6 [-4, -2, 3] = true := by decide +kernel
theorem sub6_185 : sub6 [-4, -2, 4] = true := by decide +kernel
theorem sub6_186 : sub6 [-4, -2, 5] = true := by decide +kernel
theorem sub6_187 : sub6 [-4, -2, 6] = true := by decide +kernel
theorem sub6_188 : sub6 [-4, -2, 7] = true := by decide +kernel
theorem sub6_189 : sub6 [-4, -1, -9] = true := by decide +kernel
theorem sub6_190 : sub6 [-4, -1, -8] = true := by decide +kernel
theorem sub6_191 : sub6 [-4, -1, -7] = true := by decide +kernel
theorem sb6_5 : ∀ q ∈ blk6_5, sub6 q = true := by
  unfold blk6_5
  exact List.forall_mem_cons.2 ⟨sub6_160, List.forall_mem_cons.2 ⟨sub6_161, List.forall_mem_cons.2 ⟨sub6_162, List.forall_mem_cons.2 ⟨sub6_163, List.forall_mem_cons.2 ⟨sub6_164, List.forall_mem_cons.2 ⟨sub6_165, List.forall_mem_cons.2 ⟨sub6_166, List.forall_mem_cons.2 ⟨sub6_167, List.forall_mem_cons.2 ⟨sub6_168, List.forall_mem_cons.2 ⟨sub6_169, List.forall_mem_cons.2 ⟨sub6_170, List.forall_mem_cons.2 ⟨sub6_171, List.forall_mem_cons.2 ⟨sub6_172, List.forall_mem_cons.2 ⟨sub6_173, List.forall_mem_cons.2 ⟨sub6_174, List.forall_mem_cons.2 ⟨sub6_175, List.forall_mem_cons.2 ⟨sub6_176, List.forall_mem_cons.2 ⟨sub6_177, List.forall_mem_cons.2 ⟨sub6_178, List.forall_mem_cons.2 ⟨sub6_179, List.forall_mem_cons.2 ⟨sub6_180, List.forall_mem_cons.2 ⟨sub6_181, List.forall_mem_cons.2 ⟨sub6_182, List.forall_mem_cons.2 ⟨sub6_183, List.forall_mem_cons.2 ⟨sub6_184, List.forall_mem_cons.2 ⟨sub6_185, List.forall_mem_cons.2 ⟨sub6_186, List.forall_mem_cons.2 ⟨sub6_187, List.forall_mem_cons.2 ⟨sub6_188, List.forall_mem_cons.2 ⟨sub6_189, List.forall_mem_cons.2 ⟨sub6_190, List.forall_mem_cons.2 ⟨sub6_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_192 : sub6 [-4, -1, -6] = true := by decide +kernel
theorem sub6_193 : sub6 [-4, -1, -5] = true := by decide +kernel
theorem sub6_194 : sub6 [-4, -1, -4] = true := by decide +kernel
theorem sub6_195 : sub6 [-4, -1, -3] = true := by decide +kernel
theorem sub6_196 : sub6 [-4, -1, -2] = true := by decide +kernel
theorem sub6_197 : sub6 [-4, -1, -1] = true := by decide +kernel
theorem sub6_198 : sub6 [-4, -1, 0] = true := by decide +kernel
theorem sub6_199 : sub6 [-4, -1, 1] = true := by decide +kernel
theorem sub6_200 : sub6 [-4, -1, 2] = true := by decide +kernel
theorem sub6_201 : sub6 [-4, -1, 3] = true := by decide +kernel
theorem sub6_202 : sub6 [-4, -1, 4] = true := by decide +kernel
theorem sub6_203 : sub6 [-4, -1, 5] = true := by decide +kernel
theorem sub6_204 : sub6 [-4, -1, 6] = true := by decide +kernel
theorem sub6_205 : sub6 [-4, -1, 7] = true := by decide +kernel
theorem sub6_206 : sub6 [-4, 0, -10] = true := by decide +kernel
theorem sub6_207 : sub6 [-4, 0, -9] = true := by decide +kernel
theorem sub6_208 : sub6 [-4, 0, -8] = true := by decide +kernel
theorem sub6_209 : sub6 [-4, 0, -7] = true := by decide +kernel
theorem sub6_210 : sub6 [-4, 0, -6] = true := by decide +kernel
theorem sub6_211 : sub6 [-4, 0, -5] = true := by decide +kernel
theorem sub6_212 : sub6 [-4, 0, -4] = true := by decide +kernel
theorem sub6_213 : sub6 [-4, 0, -3] = true := by decide +kernel
theorem sub6_214 : sub6 [-4, 0, -2] = true := by decide +kernel
theorem sub6_215 : sub6 [-4, 0, -1] = true := by decide +kernel
theorem sub6_216 : sub6 [-4, 0, 0] = true := by decide +kernel
theorem sub6_217 : sub6 [-4, 0, 1] = true := by decide +kernel
theorem sub6_218 : sub6 [-4, 0, 2] = true := by decide +kernel
theorem sub6_219 : sub6 [-4, 0, 3] = true := by decide +kernel
theorem sub6_220 : sub6 [-4, 0, 4] = true := by decide +kernel
theorem sub6_221 : sub6 [-4, 0, 5] = true := by decide +kernel
theorem sub6_222 : sub6 [-4, 0, 6] = true := by decide +kernel
theorem sub6_223 : sub6 [-4, 0, 7] = true := by decide +kernel
theorem sb6_6 : ∀ q ∈ blk6_6, sub6 q = true := by
  unfold blk6_6
  exact List.forall_mem_cons.2 ⟨sub6_192, List.forall_mem_cons.2 ⟨sub6_193, List.forall_mem_cons.2 ⟨sub6_194, List.forall_mem_cons.2 ⟨sub6_195, List.forall_mem_cons.2 ⟨sub6_196, List.forall_mem_cons.2 ⟨sub6_197, List.forall_mem_cons.2 ⟨sub6_198, List.forall_mem_cons.2 ⟨sub6_199, List.forall_mem_cons.2 ⟨sub6_200, List.forall_mem_cons.2 ⟨sub6_201, List.forall_mem_cons.2 ⟨sub6_202, List.forall_mem_cons.2 ⟨sub6_203, List.forall_mem_cons.2 ⟨sub6_204, List.forall_mem_cons.2 ⟨sub6_205, List.forall_mem_cons.2 ⟨sub6_206, List.forall_mem_cons.2 ⟨sub6_207, List.forall_mem_cons.2 ⟨sub6_208, List.forall_mem_cons.2 ⟨sub6_209, List.forall_mem_cons.2 ⟨sub6_210, List.forall_mem_cons.2 ⟨sub6_211, List.forall_mem_cons.2 ⟨sub6_212, List.forall_mem_cons.2 ⟨sub6_213, List.forall_mem_cons.2 ⟨sub6_214, List.forall_mem_cons.2 ⟨sub6_215, List.forall_mem_cons.2 ⟨sub6_216, List.forall_mem_cons.2 ⟨sub6_217, List.forall_mem_cons.2 ⟨sub6_218, List.forall_mem_cons.2 ⟨sub6_219, List.forall_mem_cons.2 ⟨sub6_220, List.forall_mem_cons.2 ⟨sub6_221, List.forall_mem_cons.2 ⟨sub6_222, List.forall_mem_cons.2 ⟨sub6_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_224 : sub6 [-4, 1, -10] = true := by decide +kernel
theorem sub6_225 : sub6 [-4, 1, -9] = true := by decide +kernel
theorem sub6_226 : sub6 [-4, 1, -8] = true := by decide +kernel
theorem sub6_227 : sub6 [-4, 1, -7] = true := by decide +kernel
theorem sub6_228 : sub6 [-4, 1, -6] = true := by decide +kernel
theorem sub6_229 : sub6 [-4, 1, -5] = true := by decide +kernel
theorem sub6_230 : sub6 [-4, 1, -4] = true := by decide +kernel
theorem sub6_231 : sub6 [-4, 1, -3] = true := by decide +kernel
theorem sub6_232 : sub6 [-4, 1, -2] = true := by decide +kernel
theorem sub6_233 : sub6 [-4, 1, -1] = true := by decide +kernel
theorem sub6_234 : sub6 [-4, 1, 0] = true := by decide +kernel
theorem sub6_235 : sub6 [-4, 1, 1] = true := by decide +kernel
theorem sub6_236 : sub6 [-4, 1, 2] = true := by decide +kernel
theorem sub6_237 : sub6 [-4, 1, 3] = true := by decide +kernel
theorem sub6_238 : sub6 [-4, 1, 4] = true := by decide +kernel
theorem sub6_239 : sub6 [-4, 1, 5] = true := by decide +kernel
theorem sub6_240 : sub6 [-4, 1, 6] = true := by decide +kernel
theorem sub6_241 : sub6 [-4, 1, 7] = true := by decide +kernel
theorem sub6_242 : sub6 [-4, 2, -11] = true := by decide +kernel
theorem sub6_243 : sub6 [-4, 2, -10] = true := by decide +kernel
theorem sub6_244 : sub6 [-4, 2, -9] = true := by decide +kernel
theorem sub6_245 : sub6 [-4, 2, -8] = true := by decide +kernel
theorem sub6_246 : sub6 [-4, 2, -7] = true := by decide +kernel
theorem sub6_247 : sub6 [-4, 2, -6] = true := by decide +kernel
theorem sub6_248 : sub6 [-4, 2, -5] = true := by decide +kernel
theorem sub6_249 : sub6 [-4, 2, -4] = true := by decide +kernel
theorem sub6_250 : sub6 [-4, 2, -3] = true := by decide +kernel
theorem sub6_251 : sub6 [-4, 2, -2] = true := by decide +kernel
theorem sub6_252 : sub6 [-4, 2, -1] = true := by decide +kernel
theorem sub6_253 : sub6 [-4, 2, 0] = true := by decide +kernel
theorem sub6_254 : sub6 [-4, 2, 1] = true := by decide +kernel
theorem sub6_255 : sub6 [-4, 2, 2] = true := by decide +kernel
theorem sb6_7 : ∀ q ∈ blk6_7, sub6 q = true := by
  unfold blk6_7
  exact List.forall_mem_cons.2 ⟨sub6_224, List.forall_mem_cons.2 ⟨sub6_225, List.forall_mem_cons.2 ⟨sub6_226, List.forall_mem_cons.2 ⟨sub6_227, List.forall_mem_cons.2 ⟨sub6_228, List.forall_mem_cons.2 ⟨sub6_229, List.forall_mem_cons.2 ⟨sub6_230, List.forall_mem_cons.2 ⟨sub6_231, List.forall_mem_cons.2 ⟨sub6_232, List.forall_mem_cons.2 ⟨sub6_233, List.forall_mem_cons.2 ⟨sub6_234, List.forall_mem_cons.2 ⟨sub6_235, List.forall_mem_cons.2 ⟨sub6_236, List.forall_mem_cons.2 ⟨sub6_237, List.forall_mem_cons.2 ⟨sub6_238, List.forall_mem_cons.2 ⟨sub6_239, List.forall_mem_cons.2 ⟨sub6_240, List.forall_mem_cons.2 ⟨sub6_241, List.forall_mem_cons.2 ⟨sub6_242, List.forall_mem_cons.2 ⟨sub6_243, List.forall_mem_cons.2 ⟨sub6_244, List.forall_mem_cons.2 ⟨sub6_245, List.forall_mem_cons.2 ⟨sub6_246, List.forall_mem_cons.2 ⟨sub6_247, List.forall_mem_cons.2 ⟨sub6_248, List.forall_mem_cons.2 ⟨sub6_249, List.forall_mem_cons.2 ⟨sub6_250, List.forall_mem_cons.2 ⟨sub6_251, List.forall_mem_cons.2 ⟨sub6_252, List.forall_mem_cons.2 ⟨sub6_253, List.forall_mem_cons.2 ⟨sub6_254, List.forall_mem_cons.2 ⟨sub6_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_256 : sub6 [-4, 2, 3] = true := by decide +kernel
theorem sub6_257 : sub6 [-4, 2, 4] = true := by decide +kernel
theorem sub6_258 : sub6 [-4, 2, 5] = true := by decide +kernel
theorem sub6_259 : sub6 [-4, 2, 6] = true := by decide +kernel
theorem sub6_260 : sub6 [-4, 2, 7] = true := by decide +kernel
theorem sub6_261 : sub6 [-4, 3, -11] = true := by decide +kernel
theorem sub6_262 : sub6 [-4, 3, -10] = true := by decide +kernel
theorem sub6_263 : sub6 [-4, 3, -9] = true := by decide +kernel
theorem sub6_264 : sub6 [-4, 3, -8] = true := by decide +kernel
theorem sub6_265 : sub6 [-4, 3, -7] = true := by decide +kernel
theorem sub6_266 : sub6 [-4, 3, -6] = true := by decide +kernel
theorem sub6_267 : sub6 [-4, 3, -5] = true := by decide +kernel
theorem sub6_268 : sub6 [-4, 3, -4] = true := by decide +kernel
theorem sub6_269 : sub6 [-4, 3, -3] = true := by decide +kernel
theorem sub6_270 : sub6 [-4, 3, -2] = true := by decide +kernel
theorem sub6_271 : sub6 [-4, 3, -1] = true := by decide +kernel
theorem sub6_272 : sub6 [-4, 3, 0] = true := by decide +kernel
theorem sub6_273 : sub6 [-4, 3, 1] = true := by decide +kernel
theorem sub6_274 : sub6 [-4, 3, 2] = true := by decide +kernel
theorem sub6_275 : sub6 [-4, 3, 3] = true := by decide +kernel
theorem sub6_276 : sub6 [-4, 3, 4] = true := by decide +kernel
theorem sub6_277 : sub6 [-4, 3, 5] = true := by decide +kernel
theorem sub6_278 : sub6 [-4, 3, 6] = true := by decide +kernel
theorem sub6_279 : sub6 [-4, 4, -11] = true := by decide +kernel
theorem sub6_280 : sub6 [-4, 4, -10] = true := by decide +kernel
theorem sub6_281 : sub6 [-4, 4, -9] = true := by decide +kernel
theorem sub6_282 : sub6 [-4, 4, -8] = true := by decide +kernel
theorem sub6_283 : sub6 [-4, 4, -7] = true := by decide +kernel
theorem sub6_284 : sub6 [-4, 4, -6] = true := by decide +kernel
theorem sub6_285 : sub6 [-4, 4, -5] = true := by decide +kernel
theorem sub6_286 : sub6 [-4, 4, -4] = true := by decide +kernel
theorem sub6_287 : sub6 [-4, 4, -3] = true := by decide +kernel
theorem sb6_8 : ∀ q ∈ blk6_8, sub6 q = true := by
  unfold blk6_8
  exact List.forall_mem_cons.2 ⟨sub6_256, List.forall_mem_cons.2 ⟨sub6_257, List.forall_mem_cons.2 ⟨sub6_258, List.forall_mem_cons.2 ⟨sub6_259, List.forall_mem_cons.2 ⟨sub6_260, List.forall_mem_cons.2 ⟨sub6_261, List.forall_mem_cons.2 ⟨sub6_262, List.forall_mem_cons.2 ⟨sub6_263, List.forall_mem_cons.2 ⟨sub6_264, List.forall_mem_cons.2 ⟨sub6_265, List.forall_mem_cons.2 ⟨sub6_266, List.forall_mem_cons.2 ⟨sub6_267, List.forall_mem_cons.2 ⟨sub6_268, List.forall_mem_cons.2 ⟨sub6_269, List.forall_mem_cons.2 ⟨sub6_270, List.forall_mem_cons.2 ⟨sub6_271, List.forall_mem_cons.2 ⟨sub6_272, List.forall_mem_cons.2 ⟨sub6_273, List.forall_mem_cons.2 ⟨sub6_274, List.forall_mem_cons.2 ⟨sub6_275, List.forall_mem_cons.2 ⟨sub6_276, List.forall_mem_cons.2 ⟨sub6_277, List.forall_mem_cons.2 ⟨sub6_278, List.forall_mem_cons.2 ⟨sub6_279, List.forall_mem_cons.2 ⟨sub6_280, List.forall_mem_cons.2 ⟨sub6_281, List.forall_mem_cons.2 ⟨sub6_282, List.forall_mem_cons.2 ⟨sub6_283, List.forall_mem_cons.2 ⟨sub6_284, List.forall_mem_cons.2 ⟨sub6_285, List.forall_mem_cons.2 ⟨sub6_286, List.forall_mem_cons.2 ⟨sub6_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_288 : sub6 [-4, 4, -2] = true := by decide +kernel
theorem sub6_289 : sub6 [-4, 4, -1] = true := by decide +kernel
theorem sub6_290 : sub6 [-4, 4, 0] = true := by decide +kernel
theorem sub6_291 : sub6 [-4, 4, 1] = true := by decide +kernel
theorem sub6_292 : sub6 [-4, 4, 2] = true := by decide +kernel
theorem sub6_293 : sub6 [-4, 4, 3] = true := by decide +kernel
theorem sub6_294 : sub6 [-4, 4, 4] = true := by decide +kernel
theorem sub6_295 : sub6 [-4, 4, 5] = true := by decide +kernel
theorem sub6_296 : sub6 [-4, 4, 6] = true := by decide +kernel
theorem sub6_297 : sub6 [-4, 5, -11] = true := by decide +kernel
theorem sub6_298 : sub6 [-4, 5, -10] = true := by decide +kernel
theorem sub6_299 : sub6 [-4, 5, -9] = true := by decide +kernel
theorem sub6_300 : sub6 [-4, 5, -8] = true := by decide +kernel
theorem sub6_301 : sub6 [-4, 5, -7] = true := by decide +kernel
theorem sub6_302 : sub6 [-4, 5, -6] = true := by decide +kernel
theorem sub6_303 : sub6 [-4, 5, -5] = true := by decide +kernel
theorem sub6_304 : sub6 [-4, 5, -4] = true := by decide +kernel
theorem sub6_305 : sub6 [-4, 5, -3] = true := by decide +kernel
theorem sub6_306 : sub6 [-4, 5, -2] = true := by decide +kernel
theorem sub6_307 : sub6 [-4, 5, -1] = true := by decide +kernel
theorem sub6_308 : sub6 [-4, 5, 0] = true := by decide +kernel
theorem sub6_309 : sub6 [-4, 5, 1] = true := by decide +kernel
theorem sub6_310 : sub6 [-4, 5, 2] = true := by decide +kernel
theorem sub6_311 : sub6 [-4, 5, 3] = true := by decide +kernel
theorem sub6_312 : sub6 [-4, 5, 4] = true := by decide +kernel
theorem sub6_313 : sub6 [-4, 5, 5] = true := by decide +kernel
theorem sub6_314 : sub6 [-4, 6, -11] = true := by decide +kernel
theorem sub6_315 : sub6 [-4, 6, -10] = true := by decide +kernel
theorem sub6_316 : sub6 [-4, 6, -9] = true := by decide +kernel
theorem sub6_317 : sub6 [-4, 6, -8] = true := by decide +kernel
theorem sub6_318 : sub6 [-4, 6, -7] = true := by decide +kernel
theorem sub6_319 : sub6 [-4, 6, -6] = true := by decide +kernel
theorem sb6_9 : ∀ q ∈ blk6_9, sub6 q = true := by
  unfold blk6_9
  exact List.forall_mem_cons.2 ⟨sub6_288, List.forall_mem_cons.2 ⟨sub6_289, List.forall_mem_cons.2 ⟨sub6_290, List.forall_mem_cons.2 ⟨sub6_291, List.forall_mem_cons.2 ⟨sub6_292, List.forall_mem_cons.2 ⟨sub6_293, List.forall_mem_cons.2 ⟨sub6_294, List.forall_mem_cons.2 ⟨sub6_295, List.forall_mem_cons.2 ⟨sub6_296, List.forall_mem_cons.2 ⟨sub6_297, List.forall_mem_cons.2 ⟨sub6_298, List.forall_mem_cons.2 ⟨sub6_299, List.forall_mem_cons.2 ⟨sub6_300, List.forall_mem_cons.2 ⟨sub6_301, List.forall_mem_cons.2 ⟨sub6_302, List.forall_mem_cons.2 ⟨sub6_303, List.forall_mem_cons.2 ⟨sub6_304, List.forall_mem_cons.2 ⟨sub6_305, List.forall_mem_cons.2 ⟨sub6_306, List.forall_mem_cons.2 ⟨sub6_307, List.forall_mem_cons.2 ⟨sub6_308, List.forall_mem_cons.2 ⟨sub6_309, List.forall_mem_cons.2 ⟨sub6_310, List.forall_mem_cons.2 ⟨sub6_311, List.forall_mem_cons.2 ⟨sub6_312, List.forall_mem_cons.2 ⟨sub6_313, List.forall_mem_cons.2 ⟨sub6_314, List.forall_mem_cons.2 ⟨sub6_315, List.forall_mem_cons.2 ⟨sub6_316, List.forall_mem_cons.2 ⟨sub6_317, List.forall_mem_cons.2 ⟨sub6_318, List.forall_mem_cons.2 ⟨sub6_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C079
