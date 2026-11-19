import ReflectZphi.Data.Cert5.C079.Base

namespace ReflectZphi.Data.Cert5.C079
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub4_1792 : sub4 [4, -1, -7] = true := by decide +kernel
theorem sub4_1793 : sub4 [4, -1, -6] = true := by decide +kernel
theorem sub4_1794 : sub4 [4, -1, -5] = true := by decide +kernel
theorem sub4_1795 : sub4 [4, -1, -4] = true := by decide +kernel
theorem sub4_1796 : sub4 [4, -1, -3] = true := by decide +kernel
theorem sub4_1797 : sub4 [4, -1, -2] = true := by decide +kernel
theorem sub4_1798 : sub4 [4, -1, -1] = true := by decide +kernel
theorem sub4_1799 : sub4 [4, -1, 0] = true := by decide +kernel
theorem sub4_1800 : sub4 [4, -1, 1] = true := by decide +kernel
theorem sub4_1801 : sub4 [4, -1, 2] = true := by decide +kernel
theorem sub4_1802 : sub4 [4, -1, 3] = true := by decide +kernel
theorem sub4_1803 : sub4 [4, -1, 4] = true := by decide +kernel
theorem sub4_1804 : sub4 [4, -1, 5] = true := by decide +kernel
theorem sub4_1805 : sub4 [4, -1, 6] = true := by decide +kernel
theorem sub4_1806 : sub4 [4, -1, 7] = true := by decide +kernel
theorem sub4_1807 : sub4 [4, -1, 8] = true := by decide +kernel
theorem sub4_1808 : sub4 [4, -1, 9] = true := by decide +kernel
theorem sub4_1809 : sub4 [4, -1, 10] = true := by decide +kernel
theorem sub4_1810 : sub4 [4, 0, -7] = true := by decide +kernel
theorem sub4_1811 : sub4 [4, 0, -6] = true := by decide +kernel
theorem sub4_1812 : sub4 [4, 0, -5] = true := by decide +kernel
theorem sub4_1813 : sub4 [4, 0, -4] = true := by decide +kernel
theorem sub4_1814 : sub4 [4, 0, -3] = true := by decide +kernel
theorem sub4_1815 : sub4 [4, 0, -2] = true := by decide +kernel
theorem sub4_1816 : sub4 [4, 0, -1] = true := by decide +kernel
theorem sub4_1817 : sub4 [4, 0, 0] = true := by decide +kernel
theorem sub4_1818 : sub4 [4, 0, 1] = true := by decide +kernel
theorem sub4_1819 : sub4 [4, 0, 2] = true := by decide +kernel
theorem sub4_1820 : sub4 [4, 0, 3] = true := by decide +kernel
theorem sub4_1821 : sub4 [4, 0, 4] = true := by decide +kernel
theorem sub4_1822 : sub4 [4, 0, 5] = true := by decide +kernel
theorem sub4_1823 : sub4 [4, 0, 6] = true := by decide +kernel
theorem sb4_56 : ∀ q ∈ blk4_56, sub4 q = true := by
  unfold blk4_56
  exact List.forall_mem_cons.2 ⟨sub4_1792, List.forall_mem_cons.2 ⟨sub4_1793, List.forall_mem_cons.2 ⟨sub4_1794, List.forall_mem_cons.2 ⟨sub4_1795, List.forall_mem_cons.2 ⟨sub4_1796, List.forall_mem_cons.2 ⟨sub4_1797, List.forall_mem_cons.2 ⟨sub4_1798, List.forall_mem_cons.2 ⟨sub4_1799, List.forall_mem_cons.2 ⟨sub4_1800, List.forall_mem_cons.2 ⟨sub4_1801, List.forall_mem_cons.2 ⟨sub4_1802, List.forall_mem_cons.2 ⟨sub4_1803, List.forall_mem_cons.2 ⟨sub4_1804, List.forall_mem_cons.2 ⟨sub4_1805, List.forall_mem_cons.2 ⟨sub4_1806, List.forall_mem_cons.2 ⟨sub4_1807, List.forall_mem_cons.2 ⟨sub4_1808, List.forall_mem_cons.2 ⟨sub4_1809, List.forall_mem_cons.2 ⟨sub4_1810, List.forall_mem_cons.2 ⟨sub4_1811, List.forall_mem_cons.2 ⟨sub4_1812, List.forall_mem_cons.2 ⟨sub4_1813, List.forall_mem_cons.2 ⟨sub4_1814, List.forall_mem_cons.2 ⟨sub4_1815, List.forall_mem_cons.2 ⟨sub4_1816, List.forall_mem_cons.2 ⟨sub4_1817, List.forall_mem_cons.2 ⟨sub4_1818, List.forall_mem_cons.2 ⟨sub4_1819, List.forall_mem_cons.2 ⟨sub4_1820, List.forall_mem_cons.2 ⟨sub4_1821, List.forall_mem_cons.2 ⟨sub4_1822, List.forall_mem_cons.2 ⟨sub4_1823, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_1824 : sub4 [4, 0, 7] = true := by decide +kernel
theorem sub4_1825 : sub4 [4, 0, 8] = true := by decide +kernel
theorem sub4_1826 : sub4 [4, 0, 9] = true := by decide +kernel
theorem sub4_1827 : sub4 [4, 0, 10] = true := by decide +kernel
theorem sub4_1828 : sub4 [4, 1, -7] = true := by decide +kernel
theorem sub4_1829 : sub4 [4, 1, -6] = true := by decide +kernel
theorem sub4_1830 : sub4 [4, 1, -5] = true := by decide +kernel
theorem sub4_1831 : sub4 [4, 1, -4] = true := by decide +kernel
theorem sub4_1832 : sub4 [4, 1, -3] = true := by decide +kernel
theorem sub4_1833 : sub4 [4, 1, -2] = true := by decide +kernel
theorem sub4_1834 : sub4 [4, 1, -1] = true := by decide +kernel
theorem sub4_1835 : sub4 [4, 1, 0] = true := by decide +kernel
theorem sub4_1836 : sub4 [4, 1, 1] = true := by decide +kernel
theorem sub4_1837 : sub4 [4, 1, 2] = true := by decide +kernel
theorem sub4_1838 : sub4 [4, 1, 3] = true := by decide +kernel
theorem sub4_1839 : sub4 [4, 1, 4] = true := by decide +kernel
theorem sub4_1840 : sub4 [4, 1, 5] = true := by decide +kernel
theorem sub4_1841 : sub4 [4, 1, 6] = true := by decide +kernel
theorem sub4_1842 : sub4 [4, 1, 7] = true := by decide +kernel
theorem sub4_1843 : sub4 [4, 1, 8] = true := by decide +kernel
theorem sub4_1844 : sub4 [4, 1, 9] = true := by decide +kernel
theorem sub4_1845 : sub4 [4, 2, -6] = true := by decide +kernel
theorem sub4_1846 : sub4 [4, 2, -5] = true := by decide +kernel
theorem sub4_1847 : sub4 [4, 2, -4] = true := by decide +kernel
theorem sub4_1848 : sub4 [4, 2, -3] = true := by decide +kernel
theorem sub4_1849 : sub4 [4, 2, -2] = true := by decide +kernel
theorem sub4_1850 : sub4 [4, 2, -1] = true := by decide +kernel
theorem sub4_1851 : sub4 [4, 2, 0] = true := by decide +kernel
theorem sub4_1852 : sub4 [4, 2, 1] = true := by decide +kernel
theorem sub4_1853 : sub4 [4, 2, 2] = true := by decide +kernel
theorem sub4_1854 : sub4 [4, 2, 3] = true := by decide +kernel
theorem sub4_1855 : sub4 [4, 2, 4] = true := by decide +kernel
theorem sb4_57 : ∀ q ∈ blk4_57, sub4 q = true := by
  unfold blk4_57
  exact List.forall_mem_cons.2 ⟨sub4_1824, List.forall_mem_cons.2 ⟨sub4_1825, List.forall_mem_cons.2 ⟨sub4_1826, List.forall_mem_cons.2 ⟨sub4_1827, List.forall_mem_cons.2 ⟨sub4_1828, List.forall_mem_cons.2 ⟨sub4_1829, List.forall_mem_cons.2 ⟨sub4_1830, List.forall_mem_cons.2 ⟨sub4_1831, List.forall_mem_cons.2 ⟨sub4_1832, List.forall_mem_cons.2 ⟨sub4_1833, List.forall_mem_cons.2 ⟨sub4_1834, List.forall_mem_cons.2 ⟨sub4_1835, List.forall_mem_cons.2 ⟨sub4_1836, List.forall_mem_cons.2 ⟨sub4_1837, List.forall_mem_cons.2 ⟨sub4_1838, List.forall_mem_cons.2 ⟨sub4_1839, List.forall_mem_cons.2 ⟨sub4_1840, List.forall_mem_cons.2 ⟨sub4_1841, List.forall_mem_cons.2 ⟨sub4_1842, List.forall_mem_cons.2 ⟨sub4_1843, List.forall_mem_cons.2 ⟨sub4_1844, List.forall_mem_cons.2 ⟨sub4_1845, List.forall_mem_cons.2 ⟨sub4_1846, List.forall_mem_cons.2 ⟨sub4_1847, List.forall_mem_cons.2 ⟨sub4_1848, List.forall_mem_cons.2 ⟨sub4_1849, List.forall_mem_cons.2 ⟨sub4_1850, List.forall_mem_cons.2 ⟨sub4_1851, List.forall_mem_cons.2 ⟨sub4_1852, List.forall_mem_cons.2 ⟨sub4_1853, List.forall_mem_cons.2 ⟨sub4_1854, List.forall_mem_cons.2 ⟨sub4_1855, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_1856 : sub4 [4, 2, 5] = true := by decide +kernel
theorem sub4_1857 : sub4 [4, 2, 6] = true := by decide +kernel
theorem sub4_1858 : sub4 [4, 2, 7] = true := by decide +kernel
theorem sub4_1859 : sub4 [4, 2, 8] = true := by decide +kernel
theorem sub4_1860 : sub4 [4, 2, 9] = true := by decide +kernel
theorem sub4_1861 : sub4 [4, 3, -5] = true := by decide +kernel
theorem sub4_1862 : sub4 [4, 3, -4] = true := by decide +kernel
theorem sub4_1863 : sub4 [4, 3, -3] = true := by decide +kernel
theorem sub4_1864 : sub4 [4, 3, -2] = true := by decide +kernel
theorem sub4_1865 : sub4 [4, 3, -1] = true := by decide +kernel
theorem sub4_1866 : sub4 [4, 3, 0] = true := by decide +kernel
theorem sub4_1867 : sub4 [4, 3, 1] = true := by decide +kernel
theorem sub4_1868 : sub4 [4, 3, 2] = true := by decide +kernel
theorem sub4_1869 : sub4 [4, 3, 3] = true := by decide +kernel
theorem sub4_1870 : sub4 [4, 3, 4] = true := by decide +kernel
theorem sub4_1871 : sub4 [4, 3, 5] = true := by decide +kernel
theorem sub4_1872 : sub4 [4, 3, 6] = true := by decide +kernel
theorem sub4_1873 : sub4 [4, 3, 7] = true := by decide +kernel
theorem sub4_1874 : sub4 [4, 3, 8] = true := by decide +kernel
theorem sub4_1875 : sub4 [4, 4] = true := by decide +kernel
theorem sub4_1876 : sub4 [5, -6] = true := by decide +kernel
theorem sub4_1877 : sub4 [5, -5] = true := by decide +kernel
theorem sub4_1878 : sub4 [5, -4] = true := by decide +kernel
theorem sub4_1879 : sub4 [5, -3, -5] = true := by decide +kernel
theorem sub4_1880 : sub4 [5, -3, -4] = true := by decide +kernel
theorem sub4_1881 : sub4 [5, -3, -3] = true := by decide +kernel
theorem sub4_1882 : sub4 [5, -3, -2] = true := by decide +kernel
theorem sub4_1883 : sub4 [5, -3, -1] = true := by decide +kernel
theorem sub4_1884 : sub4 [5, -3, 0] = true := by decide +kernel
theorem sub4_1885 : sub4 [5, -3, 1] = true := by decide +kernel
theorem sub4_1886 : sub4 [5, -3, 2] = true := by decide +kernel
theorem sub4_1887 : sub4 [5, -3, 3] = true := by decide +kernel
theorem sb4_58 : ∀ q ∈ blk4_58, sub4 q = true := by
  unfold blk4_58
  exact List.forall_mem_cons.2 ⟨sub4_1856, List.forall_mem_cons.2 ⟨sub4_1857, List.forall_mem_cons.2 ⟨sub4_1858, List.forall_mem_cons.2 ⟨sub4_1859, List.forall_mem_cons.2 ⟨sub4_1860, List.forall_mem_cons.2 ⟨sub4_1861, List.forall_mem_cons.2 ⟨sub4_1862, List.forall_mem_cons.2 ⟨sub4_1863, List.forall_mem_cons.2 ⟨sub4_1864, List.forall_mem_cons.2 ⟨sub4_1865, List.forall_mem_cons.2 ⟨sub4_1866, List.forall_mem_cons.2 ⟨sub4_1867, List.forall_mem_cons.2 ⟨sub4_1868, List.forall_mem_cons.2 ⟨sub4_1869, List.forall_mem_cons.2 ⟨sub4_1870, List.forall_mem_cons.2 ⟨sub4_1871, List.forall_mem_cons.2 ⟨sub4_1872, List.forall_mem_cons.2 ⟨sub4_1873, List.forall_mem_cons.2 ⟨sub4_1874, List.forall_mem_cons.2 ⟨sub4_1875, List.forall_mem_cons.2 ⟨sub4_1876, List.forall_mem_cons.2 ⟨sub4_1877, List.forall_mem_cons.2 ⟨sub4_1878, List.forall_mem_cons.2 ⟨sub4_1879, List.forall_mem_cons.2 ⟨sub4_1880, List.forall_mem_cons.2 ⟨sub4_1881, List.forall_mem_cons.2 ⟨sub4_1882, List.forall_mem_cons.2 ⟨sub4_1883, List.forall_mem_cons.2 ⟨sub4_1884, List.forall_mem_cons.2 ⟨sub4_1885, List.forall_mem_cons.2 ⟨sub4_1886, List.forall_mem_cons.2 ⟨sub4_1887, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_1888 : sub4 [5, -3, 4] = true := by decide +kernel
theorem sub4_1889 : sub4 [5, -3, 5] = true := by decide +kernel
theorem sub4_1890 : sub4 [5, -3, 6] = true := by decide +kernel
theorem sub4_1891 : sub4 [5, -3, 7] = true := by decide +kernel
theorem sub4_1892 : sub4 [5, -3, 8] = true := by decide +kernel
theorem sub4_1893 : sub4 [5, -2, -6] = true := by decide +kernel
theorem sub4_1894 : sub4 [5, -2, -5] = true := by decide +kernel
theorem sub4_1895 : sub4 [5, -2, -4] = true := by decide +kernel
theorem sub4_1896 : sub4 [5, -2, -3] = true := by decide +kernel
theorem sub4_1897 : sub4 [5, -2, -2] = true := by decide +kernel
theorem sub4_1898 : sub4 [5, -2, -1] = true := by decide +kernel
theorem sub4_1899 : sub4 [5, -2, 0] = true := by decide +kernel
theorem sub4_1900 : sub4 [5, -2, 1] = true := by decide +kernel
theorem sub4_1901 : sub4 [5, -2, 2] = true := by decide +kernel
theorem sub4_1902 : sub4 [5, -2, 3] = true := by decide +kernel
theorem sub4_1903 : sub4 [5, -2, 4] = true := by decide +kernel
theorem sub4_1904 : sub4 [5, -2, 5] = true := by decide +kernel
theorem sub4_1905 : sub4 [5, -2, 6] = true := by decide +kernel
theorem sub4_1906 : sub4 [5, -2, 7] = true := by decide +kernel
theorem sub4_1907 : sub4 [5, -2, 8] = true := by decide +kernel
theorem sub4_1908 : sub4 [5, -1, -6] = true := by decide +kernel
theorem sub4_1909 : sub4 [5, -1, -5] = true := by decide +kernel
theorem sub4_1910 : sub4 [5, -1, -4] = true := by decide +kernel
theorem sub4_1911 : sub4 [5, -1, -3] = true := by decide +kernel
theorem sub4_1912 : sub4 [5, -1, -2] = true := by decide +kernel
theorem sub4_1913 : sub4 [5, -1, -1] = true := by decide +kernel
theorem sub4_1914 : sub4 [5, -1, 0] = true := by decide +kernel
theorem sub4_1915 : sub4 [5, -1, 1] = true := by decide +kernel
theorem sub4_1916 : sub4 [5, -1, 2] = true := by decide +kernel
theorem sub4_1917 : sub4 [5, -1, 3] = true := by decide +kernel
theorem sub4_1918 : sub4 [5, -1, 4] = true := by decide +kernel
theorem sub4_1919 : sub4 [5, -1, 5] = true := by decide +kernel
theorem sb4_59 : ∀ q ∈ blk4_59, sub4 q = true := by
  unfold blk4_59
  exact List.forall_mem_cons.2 ⟨sub4_1888, List.forall_mem_cons.2 ⟨sub4_1889, List.forall_mem_cons.2 ⟨sub4_1890, List.forall_mem_cons.2 ⟨sub4_1891, List.forall_mem_cons.2 ⟨sub4_1892, List.forall_mem_cons.2 ⟨sub4_1893, List.forall_mem_cons.2 ⟨sub4_1894, List.forall_mem_cons.2 ⟨sub4_1895, List.forall_mem_cons.2 ⟨sub4_1896, List.forall_mem_cons.2 ⟨sub4_1897, List.forall_mem_cons.2 ⟨sub4_1898, List.forall_mem_cons.2 ⟨sub4_1899, List.forall_mem_cons.2 ⟨sub4_1900, List.forall_mem_cons.2 ⟨sub4_1901, List.forall_mem_cons.2 ⟨sub4_1902, List.forall_mem_cons.2 ⟨sub4_1903, List.forall_mem_cons.2 ⟨sub4_1904, List.forall_mem_cons.2 ⟨sub4_1905, List.forall_mem_cons.2 ⟨sub4_1906, List.forall_mem_cons.2 ⟨sub4_1907, List.forall_mem_cons.2 ⟨sub4_1908, List.forall_mem_cons.2 ⟨sub4_1909, List.forall_mem_cons.2 ⟨sub4_1910, List.forall_mem_cons.2 ⟨sub4_1911, List.forall_mem_cons.2 ⟨sub4_1912, List.forall_mem_cons.2 ⟨sub4_1913, List.forall_mem_cons.2 ⟨sub4_1914, List.forall_mem_cons.2 ⟨sub4_1915, List.forall_mem_cons.2 ⟨sub4_1916, List.forall_mem_cons.2 ⟨sub4_1917, List.forall_mem_cons.2 ⟨sub4_1918, List.forall_mem_cons.2 ⟨sub4_1919, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_1920 : sub4 [5, -1, 6] = true := by decide +kernel
theorem sub4_1921 : sub4 [5, -1, 7] = true := by decide +kernel
theorem sub4_1922 : sub4 [5, -1, 8] = true := by decide +kernel
theorem sub4_1923 : sub4 [5, -1, 9] = true := by decide +kernel
theorem sub4_1924 : sub4 [5, 0, -5] = true := by decide +kernel
theorem sub4_1925 : sub4 [5, 0, -4] = true := by decide +kernel
theorem sub4_1926 : sub4 [5, 0, -3] = true := by decide +kernel
theorem sub4_1927 : sub4 [5, 0, -2] = true := by decide +kernel
theorem sub4_1928 : sub4 [5, 0, -1] = true := by decide +kernel
theorem sub4_1929 : sub4 [5, 0, 0] = true := by decide +kernel
theorem sub4_1930 : sub4 [5, 0, 1] = true := by decide +kernel
theorem sub4_1931 : sub4 [5, 0, 2] = true := by decide +kernel
theorem sub4_1932 : sub4 [5, 0, 3] = true := by decide +kernel
theorem sub4_1933 : sub4 [5, 0, 4] = true := by decide +kernel
theorem sub4_1934 : sub4 [5, 0, 5] = true := by decide +kernel
theorem sub4_1935 : sub4 [5, 0, 6] = true := by decide +kernel
theorem sub4_1936 : sub4 [5, 0, 7] = true := by decide +kernel
theorem sub4_1937 : sub4 [5, 0, 8] = true := by decide +kernel
theorem sub4_1938 : sub4 [5, 1, -5] = true := by decide +kernel
theorem sub4_1939 : sub4 [5, 1, -4] = true := by decide +kernel
theorem sub4_1940 : sub4 [5, 1, -3] = true := by decide +kernel
theorem sub4_1941 : sub4 [5, 1, -2] = true := by decide +kernel
theorem sub4_1942 : sub4 [5, 1, -1] = true := by decide +kernel
theorem sub4_1943 : sub4 [5, 1, 0] = true := by decide +kernel
theorem sub4_1944 : sub4 [5, 1, 1] = true := by decide +kernel
theorem sub4_1945 : sub4 [5, 1, 2] = true := by decide +kernel
theorem sub4_1946 : sub4 [5, 1, 3] = true := by decide +kernel
theorem sub4_1947 : sub4 [5, 1, 4] = true := by decide +kernel
theorem sub4_1948 : sub4 [5, 1, 5] = true := by decide +kernel
theorem sub4_1949 : sub4 [5, 1, 6] = true := by decide +kernel
theorem sub4_1950 : sub4 [5, 1, 7] = true := by decide +kernel
theorem sub4_1951 : sub4 [5, 1, 8] = true := by decide +kernel
theorem sb4_60 : ∀ q ∈ blk4_60, sub4 q = true := by
  unfold blk4_60
  exact List.forall_mem_cons.2 ⟨sub4_1920, List.forall_mem_cons.2 ⟨sub4_1921, List.forall_mem_cons.2 ⟨sub4_1922, List.forall_mem_cons.2 ⟨sub4_1923, List.forall_mem_cons.2 ⟨sub4_1924, List.forall_mem_cons.2 ⟨sub4_1925, List.forall_mem_cons.2 ⟨sub4_1926, List.forall_mem_cons.2 ⟨sub4_1927, List.forall_mem_cons.2 ⟨sub4_1928, List.forall_mem_cons.2 ⟨sub4_1929, List.forall_mem_cons.2 ⟨sub4_1930, List.forall_mem_cons.2 ⟨sub4_1931, List.forall_mem_cons.2 ⟨sub4_1932, List.forall_mem_cons.2 ⟨sub4_1933, List.forall_mem_cons.2 ⟨sub4_1934, List.forall_mem_cons.2 ⟨sub4_1935, List.forall_mem_cons.2 ⟨sub4_1936, List.forall_mem_cons.2 ⟨sub4_1937, List.forall_mem_cons.2 ⟨sub4_1938, List.forall_mem_cons.2 ⟨sub4_1939, List.forall_mem_cons.2 ⟨sub4_1940, List.forall_mem_cons.2 ⟨sub4_1941, List.forall_mem_cons.2 ⟨sub4_1942, List.forall_mem_cons.2 ⟨sub4_1943, List.forall_mem_cons.2 ⟨sub4_1944, List.forall_mem_cons.2 ⟨sub4_1945, List.forall_mem_cons.2 ⟨sub4_1946, List.forall_mem_cons.2 ⟨sub4_1947, List.forall_mem_cons.2 ⟨sub4_1948, List.forall_mem_cons.2 ⟨sub4_1949, List.forall_mem_cons.2 ⟨sub4_1950, List.forall_mem_cons.2 ⟨sub4_1951, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_1952 : sub4 [5, 2] = true := by decide +kernel
theorem sub4_1953 : sub4 [5, 3] = true := by decide +kernel
theorem sub4_1954 : sub4 [6, -5] = true := by decide +kernel
theorem sub4_1955 : sub4 [6, -4] = true := by decide +kernel
theorem sub4_1956 : sub4 [6, -3] = true := by decide +kernel
theorem sub4_1957 : sub4 [6, -2] = true := by decide +kernel
theorem sub4_1958 : sub4 [6, -1] = true := by decide +kernel
theorem sub4_1959 : sub4 [6, 0] = true := by decide +kernel
theorem sub4_1960 : sub4 [6, 1] = true := by decide +kernel
theorem sb4_61 : ∀ q ∈ blk4_61, sub4 q = true := by
  unfold blk4_61
  exact List.forall_mem_cons.2 ⟨sub4_1952, List.forall_mem_cons.2 ⟨sub4_1953, List.forall_mem_cons.2 ⟨sub4_1954, List.forall_mem_cons.2 ⟨sub4_1955, List.forall_mem_cons.2 ⟨sub4_1956, List.forall_mem_cons.2 ⟨sub4_1957, List.forall_mem_cons.2 ⟨sub4_1958, List.forall_mem_cons.2 ⟨sub4_1959, List.forall_mem_cons.2 ⟨sub4_1960, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_0 : sub5 [-5, -4] = true := by decide +kernel
theorem sub5_1 : sub5 [-5, -3] = true := by decide +kernel
theorem sub5_2 : sub5 [-5, -2] = true := by decide +kernel
theorem sub5_3 : sub5 [-5, -1, -5] = true := by decide +kernel
theorem sub5_4 : sub5 [-5, -1, -4] = true := by decide +kernel
theorem sub5_5 : sub5 [-5, -1, -3] = true := by decide +kernel
theorem sub5_6 : sub5 [-5, -1, -2] = true := by decide +kernel
theorem sub5_7 : sub5 [-5, -1, -1] = true := by decide +kernel
theorem sub5_8 : sub5 [-5, -1, 0] = true := by decide +kernel
theorem sub5_9 : sub5 [-5, -1, 1] = true := by decide +kernel
theorem sub5_10 : sub5 [-5, -1, 2] = true := by decide +kernel
theorem sub5_11 : sub5 [-5, -1, 3] = true := by decide +kernel
theorem sub5_12 : sub5 [-5, -1, 4] = true := by decide +kernel
theorem sub5_13 : sub5 [-5, -1, 5] = true := by decide +kernel
theorem sub5_14 : sub5 [-5, -1, 6] = true := by decide +kernel
theorem sub5_15 : sub5 [-5, -1, 7] = true := by decide +kernel
theorem sub5_16 : sub5 [-5, -1, 8] = true := by decide +kernel
theorem sub5_17 : sub5 [-5, 0, -5] = true := by decide +kernel
theorem sub5_18 : sub5 [-5, 0, -4] = true := by decide +kernel
theorem sub5_19 : sub5 [-5, 0, -3] = true := by decide +kernel
theorem sub5_20 : sub5 [-5, 0, -2] = true := by decide +kernel
theorem sub5_21 : sub5 [-5, 0, -1] = true := by decide +kernel
theorem sub5_22 : sub5 [-5, 0, 0] = true := by decide +kernel
theorem sub5_23 : sub5 [-5, 0, 1] = true := by decide +kernel
theorem sub5_24 : sub5 [-5, 0, 2] = true := by decide +kernel
theorem sub5_25 : sub5 [-5, 0, 3] = true := by decide +kernel
theorem sub5_26 : sub5 [-5, 0, 4] = true := by decide +kernel
theorem sub5_27 : sub5 [-5, 0, 5] = true := by decide +kernel
theorem sub5_28 : sub5 [-5, 0, 6] = true := by decide +kernel
theorem sub5_29 : sub5 [-5, 0, 7] = true := by decide +kernel
theorem sub5_30 : sub5 [-5, 0, 8] = true := by decide +kernel
theorem sub5_31 : sub5 [-5, 1, -5] = true := by decide +kernel
theorem sb5_0 : ∀ q ∈ blk5_0, sub5 q = true := by
  unfold blk5_0
  exact List.forall_mem_cons.2 ⟨sub5_0, List.forall_mem_cons.2 ⟨sub5_1, List.forall_mem_cons.2 ⟨sub5_2, List.forall_mem_cons.2 ⟨sub5_3, List.forall_mem_cons.2 ⟨sub5_4, List.forall_mem_cons.2 ⟨sub5_5, List.forall_mem_cons.2 ⟨sub5_6, List.forall_mem_cons.2 ⟨sub5_7, List.forall_mem_cons.2 ⟨sub5_8, List.forall_mem_cons.2 ⟨sub5_9, List.forall_mem_cons.2 ⟨sub5_10, List.forall_mem_cons.2 ⟨sub5_11, List.forall_mem_cons.2 ⟨sub5_12, List.forall_mem_cons.2 ⟨sub5_13, List.forall_mem_cons.2 ⟨sub5_14, List.forall_mem_cons.2 ⟨sub5_15, List.forall_mem_cons.2 ⟨sub5_16, List.forall_mem_cons.2 ⟨sub5_17, List.forall_mem_cons.2 ⟨sub5_18, List.forall_mem_cons.2 ⟨sub5_19, List.forall_mem_cons.2 ⟨sub5_20, List.forall_mem_cons.2 ⟨sub5_21, List.forall_mem_cons.2 ⟨sub5_22, List.forall_mem_cons.2 ⟨sub5_23, List.forall_mem_cons.2 ⟨sub5_24, List.forall_mem_cons.2 ⟨sub5_25, List.forall_mem_cons.2 ⟨sub5_26, List.forall_mem_cons.2 ⟨sub5_27, List.forall_mem_cons.2 ⟨sub5_28, List.forall_mem_cons.2 ⟨sub5_29, List.forall_mem_cons.2 ⟨sub5_30, List.forall_mem_cons.2 ⟨sub5_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_32 : sub5 [-5, 1, -4] = true := by decide +kernel
theorem sub5_33 : sub5 [-5, 1, -3] = true := by decide +kernel
theorem sub5_34 : sub5 [-5, 1, -2] = true := by decide +kernel
theorem sub5_35 : sub5 [-5, 1, -1] = true := by decide +kernel
theorem sub5_36 : sub5 [-5, 1, 0] = true := by decide +kernel
theorem sub5_37 : sub5 [-5, 1, 1] = true := by decide +kernel
theorem sub5_38 : sub5 [-5, 1, 2] = true := by decide +kernel
theorem sub5_39 : sub5 [-5, 1, 3] = true := by decide +kernel
theorem sub5_40 : sub5 [-5, 1, 4] = true := by decide +kernel
theorem sub5_41 : sub5 [-5, 1, 5] = true := by decide +kernel
theorem sub5_42 : sub5 [-5, 1, 6] = true := by decide +kernel
theorem sub5_43 : sub5 [-5, 1, 7] = true := by decide +kernel
theorem sub5_44 : sub5 [-5, 1, 8] = true := by decide +kernel
theorem sub5_45 : sub5 [-5, 2] = true := by decide +kernel
theorem sub5_46 : sub5 [-4, -5] = true := by decide +kernel
theorem sub5_47 : sub5 [-4, -4] = true := by decide +kernel
theorem sub5_48 : sub5 [-4, -3, -7] = true := by decide +kernel
theorem sub5_49 : sub5 [-4, -3, -6] = true := by decide +kernel
theorem sub5_50 : sub5 [-4, -3, -5] = true := by decide +kernel
theorem sub5_51 : sub5 [-4, -3, -4] = true := by decide +kernel
theorem sub5_52 : sub5 [-4, -3, -3] = true := by decide +kernel
theorem sub5_53 : sub5 [-4, -3, -2] = true := by decide +kernel
theorem sub5_54 : sub5 [-4, -3, -1] = true := by decide +kernel
theorem sub5_55 : sub5 [-4, -3, 0] = true := by decide +kernel
theorem sub5_56 : sub5 [-4, -3, 1] = true := by decide +kernel
theorem sub5_57 : sub5 [-4, -3, 2] = true := by decide +kernel
theorem sub5_58 : sub5 [-4, -3, 3] = true := by decide +kernel
theorem sub5_59 : sub5 [-4, -3, 4] = true := by decide +kernel
theorem sub5_60 : sub5 [-4, -3, 5] = true := by decide +kernel
theorem sub5_61 : sub5 [-4, -3, 6] = true := by decide +kernel
theorem sub5_62 : sub5 [-4, -3, 7] = true := by decide +kernel
theorem sub5_63 : sub5 [-4, -3, 8] = true := by decide +kernel
theorem sb5_1 : ∀ q ∈ blk5_1, sub5 q = true := by
  unfold blk5_1
  exact List.forall_mem_cons.2 ⟨sub5_32, List.forall_mem_cons.2 ⟨sub5_33, List.forall_mem_cons.2 ⟨sub5_34, List.forall_mem_cons.2 ⟨sub5_35, List.forall_mem_cons.2 ⟨sub5_36, List.forall_mem_cons.2 ⟨sub5_37, List.forall_mem_cons.2 ⟨sub5_38, List.forall_mem_cons.2 ⟨sub5_39, List.forall_mem_cons.2 ⟨sub5_40, List.forall_mem_cons.2 ⟨sub5_41, List.forall_mem_cons.2 ⟨sub5_42, List.forall_mem_cons.2 ⟨sub5_43, List.forall_mem_cons.2 ⟨sub5_44, List.forall_mem_cons.2 ⟨sub5_45, List.forall_mem_cons.2 ⟨sub5_46, List.forall_mem_cons.2 ⟨sub5_47, List.forall_mem_cons.2 ⟨sub5_48, List.forall_mem_cons.2 ⟨sub5_49, List.forall_mem_cons.2 ⟨sub5_50, List.forall_mem_cons.2 ⟨sub5_51, List.forall_mem_cons.2 ⟨sub5_52, List.forall_mem_cons.2 ⟨sub5_53, List.forall_mem_cons.2 ⟨sub5_54, List.forall_mem_cons.2 ⟨sub5_55, List.forall_mem_cons.2 ⟨sub5_56, List.forall_mem_cons.2 ⟨sub5_57, List.forall_mem_cons.2 ⟨sub5_58, List.forall_mem_cons.2 ⟨sub5_59, List.forall_mem_cons.2 ⟨sub5_60, List.forall_mem_cons.2 ⟨sub5_61, List.forall_mem_cons.2 ⟨sub5_62, List.forall_mem_cons.2 ⟨sub5_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_64 : sub5 [-4, -2, -8] = true := by decide +kernel
theorem sub5_65 : sub5 [-4, -2, -7] = true := by decide +kernel
theorem sub5_66 : sub5 [-4, -2, -6] = true := by decide +kernel
theorem sub5_67 : sub5 [-4, -2, -5] = true := by decide +kernel
theorem sub5_68 : sub5 [-4, -2, -4] = true := by decide +kernel
theorem sub5_69 : sub5 [-4, -2, -3] = true := by decide +kernel
theorem sub5_70 : sub5 [-4, -2, -2] = true := by decide +kernel
theorem sub5_71 : sub5 [-4, -2, -1] = true := by decide +kernel
theorem sub5_72 : sub5 [-4, -2, 0] = true := by decide +kernel
theorem sub5_73 : sub5 [-4, -2, 1] = true := by decide +kernel
theorem sub5_74 : sub5 [-4, -2, 2] = true := by decide +kernel
theorem sub5_75 : sub5 [-4, -2, 3] = true := by decide +kernel
theorem sub5_76 : sub5 [-4, -2, 4] = true := by decide +kernel
theorem sub5_77 : sub5 [-4, -2, 5] = true := by decide +kernel
theorem sub5_78 : sub5 [-4, -2, 6] = true := by decide +kernel
theorem sub5_79 : sub5 [-4, -2, 7] = true := by decide +kernel
theorem sub5_80 : sub5 [-4, -2, 8] = true := by decide +kernel
theorem sub5_81 : sub5 [-4, -2, 9] = true := by decide +kernel
theorem sub5_82 : sub5 [-4, -2, 10] = true := by decide +kernel
theorem sub5_83 : sub5 [-4, -1, -8] = true := by decide +kernel
theorem sub5_84 : sub5 [-4, -1, -7] = true := by decide +kernel
theorem sub5_85 : sub5 [-4, -1, -6] = true := by decide +kernel
theorem sub5_86 : sub5 [-4, -1, -5] = true := by decide +kernel
theorem sub5_87 : sub5 [-4, -1, -4] = true := by decide +kernel
theorem sub5_88 : sub5 [-4, -1, -3] = true := by decide +kernel
theorem sub5_89 : sub5 [-4, -1, -2] = true := by decide +kernel
theorem sub5_90 : sub5 [-4, -1, -1] = true := by decide +kernel
theorem sub5_91 : sub5 [-4, -1, 0] = true := by decide +kernel
theorem sub5_92 : sub5 [-4, -1, 1] = true := by decide +kernel
theorem sub5_93 : sub5 [-4, -1, 2] = true := by decide +kernel
theorem sub5_94 : sub5 [-4, -1, 3] = true := by decide +kernel
theorem sub5_95 : sub5 [-4, -1, 4] = true := by decide +kernel
theorem sb5_2 : ∀ q ∈ blk5_2, sub5 q = true := by
  unfold blk5_2
  exact List.forall_mem_cons.2 ⟨sub5_64, List.forall_mem_cons.2 ⟨sub5_65, List.forall_mem_cons.2 ⟨sub5_66, List.forall_mem_cons.2 ⟨sub5_67, List.forall_mem_cons.2 ⟨sub5_68, List.forall_mem_cons.2 ⟨sub5_69, List.forall_mem_cons.2 ⟨sub5_70, List.forall_mem_cons.2 ⟨sub5_71, List.forall_mem_cons.2 ⟨sub5_72, List.forall_mem_cons.2 ⟨sub5_73, List.forall_mem_cons.2 ⟨sub5_74, List.forall_mem_cons.2 ⟨sub5_75, List.forall_mem_cons.2 ⟨sub5_76, List.forall_mem_cons.2 ⟨sub5_77, List.forall_mem_cons.2 ⟨sub5_78, List.forall_mem_cons.2 ⟨sub5_79, List.forall_mem_cons.2 ⟨sub5_80, List.forall_mem_cons.2 ⟨sub5_81, List.forall_mem_cons.2 ⟨sub5_82, List.forall_mem_cons.2 ⟨sub5_83, List.forall_mem_cons.2 ⟨sub5_84, List.forall_mem_cons.2 ⟨sub5_85, List.forall_mem_cons.2 ⟨sub5_86, List.forall_mem_cons.2 ⟨sub5_87, List.forall_mem_cons.2 ⟨sub5_88, List.forall_mem_cons.2 ⟨sub5_89, List.forall_mem_cons.2 ⟨sub5_90, List.forall_mem_cons.2 ⟨sub5_91, List.forall_mem_cons.2 ⟨sub5_92, List.forall_mem_cons.2 ⟨sub5_93, List.forall_mem_cons.2 ⟨sub5_94, List.forall_mem_cons.2 ⟨sub5_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_96 : sub5 [-4, -1, 5] = true := by decide +kernel
theorem sub5_97 : sub5 [-4, -1, 6] = true := by decide +kernel
theorem sub5_98 : sub5 [-4, -1, 7] = true := by decide +kernel
theorem sub5_99 : sub5 [-4, -1, 8] = true := by decide +kernel
theorem sub5_100 : sub5 [-4, -1, 9] = true := by decide +kernel
theorem sub5_101 : sub5 [-4, -1, 10] = true := by decide +kernel
theorem sub5_102 : sub5 [-4, 0, -8] = true := by decide +kernel
theorem sub5_103 : sub5 [-4, 0, -7] = true := by decide +kernel
theorem sub5_104 : sub5 [-4, 0, -6] = true := by decide +kernel
theorem sub5_105 : sub5 [-4, 0, -5] = true := by decide +kernel
theorem sub5_106 : sub5 [-4, 0, -4] = true := by decide +kernel
theorem sub5_107 : sub5 [-4, 0, -3] = true := by decide +kernel
theorem sub5_108 : sub5 [-4, 0, -2] = true := by decide +kernel
theorem sub5_109 : sub5 [-4, 0, -1] = true := by decide +kernel
theorem sub5_110 : sub5 [-4, 0, 0] = true := by decide +kernel
theorem sub5_111 : sub5 [-4, 0, 1] = true := by decide +kernel
theorem sub5_112 : sub5 [-4, 0, 2] = true := by decide +kernel
theorem sub5_113 : sub5 [-4, 0, 3] = true := by decide +kernel
theorem sub5_114 : sub5 [-4, 0, 4] = true := by decide +kernel
theorem sub5_115 : sub5 [-4, 0, 5] = true := by decide +kernel
theorem sub5_116 : sub5 [-4, 0, 6] = true := by decide +kernel
theorem sub5_117 : sub5 [-4, 0, 7] = true := by decide +kernel
theorem sub5_118 : sub5 [-4, 0, 8] = true := by decide +kernel
theorem sub5_119 : sub5 [-4, 0, 9] = true := by decide +kernel
theorem sub5_120 : sub5 [-4, 0, 10] = true := by decide +kernel
theorem sub5_121 : sub5 [-4, 0, 11] = true := by decide +kernel
theorem sub5_122 : sub5 [-4, 1, -8] = true := by decide +kernel
theorem sub5_123 : sub5 [-4, 1, -7] = true := by decide +kernel
theorem sub5_124 : sub5 [-4, 1, -6] = true := by decide +kernel
theorem sub5_125 : sub5 [-4, 1, -5] = true := by decide +kernel
theorem sub5_126 : sub5 [-4, 1, -4] = true := by decide +kernel
theorem sub5_127 : sub5 [-4, 1, -3] = true := by decide +kernel
theorem sb5_3 : ∀ q ∈ blk5_3, sub5 q = true := by
  unfold blk5_3
  exact List.forall_mem_cons.2 ⟨sub5_96, List.forall_mem_cons.2 ⟨sub5_97, List.forall_mem_cons.2 ⟨sub5_98, List.forall_mem_cons.2 ⟨sub5_99, List.forall_mem_cons.2 ⟨sub5_100, List.forall_mem_cons.2 ⟨sub5_101, List.forall_mem_cons.2 ⟨sub5_102, List.forall_mem_cons.2 ⟨sub5_103, List.forall_mem_cons.2 ⟨sub5_104, List.forall_mem_cons.2 ⟨sub5_105, List.forall_mem_cons.2 ⟨sub5_106, List.forall_mem_cons.2 ⟨sub5_107, List.forall_mem_cons.2 ⟨sub5_108, List.forall_mem_cons.2 ⟨sub5_109, List.forall_mem_cons.2 ⟨sub5_110, List.forall_mem_cons.2 ⟨sub5_111, List.forall_mem_cons.2 ⟨sub5_112, List.forall_mem_cons.2 ⟨sub5_113, List.forall_mem_cons.2 ⟨sub5_114, List.forall_mem_cons.2 ⟨sub5_115, List.forall_mem_cons.2 ⟨sub5_116, List.forall_mem_cons.2 ⟨sub5_117, List.forall_mem_cons.2 ⟨sub5_118, List.forall_mem_cons.2 ⟨sub5_119, List.forall_mem_cons.2 ⟨sub5_120, List.forall_mem_cons.2 ⟨sub5_121, List.forall_mem_cons.2 ⟨sub5_122, List.forall_mem_cons.2 ⟨sub5_123, List.forall_mem_cons.2 ⟨sub5_124, List.forall_mem_cons.2 ⟨sub5_125, List.forall_mem_cons.2 ⟨sub5_126, List.forall_mem_cons.2 ⟨sub5_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_128 : sub5 [-4, 1, -2] = true := by decide +kernel
theorem sub5_129 : sub5 [-4, 1, -1] = true := by decide +kernel
theorem sub5_130 : sub5 [-4, 1, 0] = true := by decide +kernel
theorem sub5_131 : sub5 [-4, 1, 1] = true := by decide +kernel
theorem sub5_132 : sub5 [-4, 1, 2] = true := by decide +kernel
theorem sub5_133 : sub5 [-4, 1, 3] = true := by decide +kernel
theorem sub5_134 : sub5 [-4, 1, 4] = true := by decide +kernel
theorem sub5_135 : sub5 [-4, 1, 5] = true := by decide +kernel
theorem sub5_136 : sub5 [-4, 1, 6] = true := by decide +kernel
theorem sub5_137 : sub5 [-4, 1, 7] = true := by decide +kernel
theorem sub5_138 : sub5 [-4, 1, 8] = true := by decide +kernel
theorem sub5_139 : sub5 [-4, 1, 9] = true := by decide +kernel
theorem sub5_140 : sub5 [-4, 1, 10] = true := by decide +kernel
theorem sub5_141 : sub5 [-4, 2, -7] = true := by decide +kernel
theorem sub5_142 : sub5 [-4, 2, -6] = true := by decide +kernel
theorem sub5_143 : sub5 [-4, 2, -5] = true := by decide +kernel
theorem sub5_144 : sub5 [-4, 2, -4] = true := by decide +kernel
theorem sub5_145 : sub5 [-4, 2, -3] = true := by decide +kernel
theorem sub5_146 : sub5 [-4, 2, -2] = true := by decide +kernel
theorem sub5_147 : sub5 [-4, 2, -1] = true := by decide +kernel
theorem sub5_148 : sub5 [-4, 2, 0] = true := by decide +kernel
theorem sub5_149 : sub5 [-4, 2, 1] = true := by decide +kernel
theorem sub5_150 : sub5 [-4, 2, 2] = true := by decide +kernel
theorem sub5_151 : sub5 [-4, 2, 3] = true := by decide +kernel
theorem sub5_152 : sub5 [-4, 2, 4] = true := by decide +kernel
theorem sub5_153 : sub5 [-4, 2, 5] = true := by decide +kernel
theorem sub5_154 : sub5 [-4, 2, 6] = true := by decide +kernel
theorem sub5_155 : sub5 [-4, 2, 7] = true := by decide +kernel
theorem sub5_156 : sub5 [-4, 2, 8] = true := by decide +kernel
theorem sub5_157 : sub5 [-4, 2, 9] = true := by decide +kernel
theorem sub5_158 : sub5 [-4, 2, 10] = true := by decide +kernel
theorem sub5_159 : sub5 [-4, 3, -5] = true := by decide +kernel
theorem sb5_4 : ∀ q ∈ blk5_4, sub5 q = true := by
  unfold blk5_4
  exact List.forall_mem_cons.2 ⟨sub5_128, List.forall_mem_cons.2 ⟨sub5_129, List.forall_mem_cons.2 ⟨sub5_130, List.forall_mem_cons.2 ⟨sub5_131, List.forall_mem_cons.2 ⟨sub5_132, List.forall_mem_cons.2 ⟨sub5_133, List.forall_mem_cons.2 ⟨sub5_134, List.forall_mem_cons.2 ⟨sub5_135, List.forall_mem_cons.2 ⟨sub5_136, List.forall_mem_cons.2 ⟨sub5_137, List.forall_mem_cons.2 ⟨sub5_138, List.forall_mem_cons.2 ⟨sub5_139, List.forall_mem_cons.2 ⟨sub5_140, List.forall_mem_cons.2 ⟨sub5_141, List.forall_mem_cons.2 ⟨sub5_142, List.forall_mem_cons.2 ⟨sub5_143, List.forall_mem_cons.2 ⟨sub5_144, List.forall_mem_cons.2 ⟨sub5_145, List.forall_mem_cons.2 ⟨sub5_146, List.forall_mem_cons.2 ⟨sub5_147, List.forall_mem_cons.2 ⟨sub5_148, List.forall_mem_cons.2 ⟨sub5_149, List.forall_mem_cons.2 ⟨sub5_150, List.forall_mem_cons.2 ⟨sub5_151, List.forall_mem_cons.2 ⟨sub5_152, List.forall_mem_cons.2 ⟨sub5_153, List.forall_mem_cons.2 ⟨sub5_154, List.forall_mem_cons.2 ⟨sub5_155, List.forall_mem_cons.2 ⟨sub5_156, List.forall_mem_cons.2 ⟨sub5_157, List.forall_mem_cons.2 ⟨sub5_158, List.forall_mem_cons.2 ⟨sub5_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_160 : sub5 [-4, 3, -4] = true := by decide +kernel
theorem sub5_161 : sub5 [-4, 3, -3] = true := by decide +kernel
theorem sub5_162 : sub5 [-4, 3, -2] = true := by decide +kernel
theorem sub5_163 : sub5 [-4, 3, -1] = true := by decide +kernel
theorem sub5_164 : sub5 [-4, 3, 0] = true := by decide +kernel
theorem sub5_165 : sub5 [-4, 3, 1] = true := by decide +kernel
theorem sub5_166 : sub5 [-4, 3, 2] = true := by decide +kernel
theorem sub5_167 : sub5 [-4, 3, 3] = true := by decide +kernel
theorem sub5_168 : sub5 [-4, 3, 4] = true := by decide +kernel
theorem sub5_169 : sub5 [-4, 3, 5] = true := by decide +kernel
theorem sub5_170 : sub5 [-4, 3, 6] = true := by decide +kernel
theorem sub5_171 : sub5 [-4, 3, 7] = true := by decide +kernel
theorem sub5_172 : sub5 [-4, 3, 8] = true := by decide +kernel
theorem sub5_173 : sub5 [-4, 4] = true := by decide +kernel
theorem sub5_174 : sub5 [-3, -6] = true := by decide +kernel
theorem sub5_175 : sub5 [-3, -5] = true := by decide +kernel
theorem sub5_176 : sub5 [-3, -4, -7] = true := by decide +kernel
theorem sub5_177 : sub5 [-3, -4, -6] = true := by decide +kernel
theorem sub5_178 : sub5 [-3, -4, -5] = true := by decide +kernel
theorem sub5_179 : sub5 [-3, -4, -4] = true := by decide +kernel
theorem sub5_180 : sub5 [-3, -4, -3] = true := by decide +kernel
theorem sub5_181 : sub5 [-3, -4, -2] = true := by decide +kernel
theorem sub5_182 : sub5 [-3, -4, -1] = true := by decide +kernel
theorem sub5_183 : sub5 [-3, -4, 0] = true := by decide +kernel
theorem sub5_184 : sub5 [-3, -4, 1] = true := by decide +kernel
theorem sub5_185 : sub5 [-3, -4, 2] = true := by decide +kernel
theorem sub5_186 : sub5 [-3, -4, 3] = true := by decide +kernel
theorem sub5_187 : sub5 [-3, -4, 4] = true := by decide +kernel
theorem sub5_188 : sub5 [-3, -4, 5] = true := by decide +kernel
theorem sub5_189 : sub5 [-3, -4, 6] = true := by decide +kernel
theorem sub5_190 : sub5 [-3, -4, 7] = true := by decide +kernel
theorem sub5_191 : sub5 [-3, -4, 8] = true := by decide +kernel
theorem sb5_5 : ∀ q ∈ blk5_5, sub5 q = true := by
  unfold blk5_5
  exact List.forall_mem_cons.2 ⟨sub5_160, List.forall_mem_cons.2 ⟨sub5_161, List.forall_mem_cons.2 ⟨sub5_162, List.forall_mem_cons.2 ⟨sub5_163, List.forall_mem_cons.2 ⟨sub5_164, List.forall_mem_cons.2 ⟨sub5_165, List.forall_mem_cons.2 ⟨sub5_166, List.forall_mem_cons.2 ⟨sub5_167, List.forall_mem_cons.2 ⟨sub5_168, List.forall_mem_cons.2 ⟨sub5_169, List.forall_mem_cons.2 ⟨sub5_170, List.forall_mem_cons.2 ⟨sub5_171, List.forall_mem_cons.2 ⟨sub5_172, List.forall_mem_cons.2 ⟨sub5_173, List.forall_mem_cons.2 ⟨sub5_174, List.forall_mem_cons.2 ⟨sub5_175, List.forall_mem_cons.2 ⟨sub5_176, List.forall_mem_cons.2 ⟨sub5_177, List.forall_mem_cons.2 ⟨sub5_178, List.forall_mem_cons.2 ⟨sub5_179, List.forall_mem_cons.2 ⟨sub5_180, List.forall_mem_cons.2 ⟨sub5_181, List.forall_mem_cons.2 ⟨sub5_182, List.forall_mem_cons.2 ⟨sub5_183, List.forall_mem_cons.2 ⟨sub5_184, List.forall_mem_cons.2 ⟨sub5_185, List.forall_mem_cons.2 ⟨sub5_186, List.forall_mem_cons.2 ⟨sub5_187, List.forall_mem_cons.2 ⟨sub5_188, List.forall_mem_cons.2 ⟨sub5_189, List.forall_mem_cons.2 ⟨sub5_190, List.forall_mem_cons.2 ⟨sub5_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_192 : sub5 [-3, -3, -9] = true := by decide +kernel
theorem sub5_193 : sub5 [-3, -3, -8] = true := by decide +kernel
theorem sub5_194 : sub5 [-3, -3, -7] = true := by decide +kernel
theorem sub5_195 : sub5 [-3, -3, -6] = true := by decide +kernel
theorem sub5_196 : sub5 [-3, -3, -5] = true := by decide +kernel
theorem sub5_197 : sub5 [-3, -3, -4] = true := by decide +kernel
theorem sub5_198 : sub5 [-3, -3, -3] = true := by decide +kernel
theorem sub5_199 : sub5 [-3, -3, -2] = true := by decide +kernel
theorem sub5_200 : sub5 [-3, -3, -1] = true := by decide +kernel
theorem sub5_201 : sub5 [-3, -3, 0] = true := by decide +kernel
theorem sub5_202 : sub5 [-3, -3, 1] = true := by decide +kernel
theorem sub5_203 : sub5 [-3, -3, 2] = true := by decide +kernel
theorem sub5_204 : sub5 [-3, -3, 3] = true := by decide +kernel
theorem sub5_205 : sub5 [-3, -3, 4] = true := by decide +kernel
theorem sub5_206 : sub5 [-3, -3, 5] = true := by decide +kernel
theorem sub5_207 : sub5 [-3, -3, 6] = true := by decide +kernel
theorem sub5_208 : sub5 [-3, -3, 7] = true := by decide +kernel
theorem sub5_209 : sub5 [-3, -3, 8] = true := by decide +kernel
theorem sub5_210 : sub5 [-3, -3, 9] = true := by decide +kernel
theorem sub5_211 : sub5 [-3, -3, 10] = true := by decide +kernel
theorem sub5_212 : sub5 [-3, -2, -10] = true := by decide +kernel
theorem sub5_213 : sub5 [-3, -2, -9] = true := by decide +kernel
theorem sub5_214 : sub5 [-3, -2, -8] = true := by decide +kernel
theorem sub5_215 : sub5 [-3, -2, -7] = true := by decide +kernel
theorem sub5_216 : sub5 [-3, -2, -6] = true := by decide +kernel
theorem sub5_217 : sub5 [-3, -2, -5] = true := by decide +kernel
theorem sub5_218 : sub5 [-3, -2, -4] = true := by decide +kernel
theorem sub5_219 : sub5 [-3, -2, -3] = true := by decide +kernel
theorem sub5_220 : sub5 [-3, -2, -2] = true := by decide +kernel
theorem sub5_221 : sub5 [-3, -2, -1] = true := by decide +kernel
theorem sub5_222 : sub5 [-3, -2, 0] = true := by decide +kernel
theorem sub5_223 : sub5 [-3, -2, 1] = true := by decide +kernel
theorem sb5_6 : ∀ q ∈ blk5_6, sub5 q = true := by
  unfold blk5_6
  exact List.forall_mem_cons.2 ⟨sub5_192, List.forall_mem_cons.2 ⟨sub5_193, List.forall_mem_cons.2 ⟨sub5_194, List.forall_mem_cons.2 ⟨sub5_195, List.forall_mem_cons.2 ⟨sub5_196, List.forall_mem_cons.2 ⟨sub5_197, List.forall_mem_cons.2 ⟨sub5_198, List.forall_mem_cons.2 ⟨sub5_199, List.forall_mem_cons.2 ⟨sub5_200, List.forall_mem_cons.2 ⟨sub5_201, List.forall_mem_cons.2 ⟨sub5_202, List.forall_mem_cons.2 ⟨sub5_203, List.forall_mem_cons.2 ⟨sub5_204, List.forall_mem_cons.2 ⟨sub5_205, List.forall_mem_cons.2 ⟨sub5_206, List.forall_mem_cons.2 ⟨sub5_207, List.forall_mem_cons.2 ⟨sub5_208, List.forall_mem_cons.2 ⟨sub5_209, List.forall_mem_cons.2 ⟨sub5_210, List.forall_mem_cons.2 ⟨sub5_211, List.forall_mem_cons.2 ⟨sub5_212, List.forall_mem_cons.2 ⟨sub5_213, List.forall_mem_cons.2 ⟨sub5_214, List.forall_mem_cons.2 ⟨sub5_215, List.forall_mem_cons.2 ⟨sub5_216, List.forall_mem_cons.2 ⟨sub5_217, List.forall_mem_cons.2 ⟨sub5_218, List.forall_mem_cons.2 ⟨sub5_219, List.forall_mem_cons.2 ⟨sub5_220, List.forall_mem_cons.2 ⟨sub5_221, List.forall_mem_cons.2 ⟨sub5_222, List.forall_mem_cons.2 ⟨sub5_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_224 : sub5 [-3, -2, 2] = true := by decide +kernel
theorem sub5_225 : sub5 [-3, -2, 3] = true := by decide +kernel
theorem sub5_226 : sub5 [-3, -2, 4] = true := by decide +kernel
theorem sub5_227 : sub5 [-3, -2, 5] = true := by decide +kernel
theorem sub5_228 : sub5 [-3, -2, 6] = true := by decide +kernel
theorem sub5_229 : sub5 [-3, -2, 7] = true := by decide +kernel
theorem sub5_230 : sub5 [-3, -2, 8] = true := by decide +kernel
theorem sub5_231 : sub5 [-3, -2, 9] = true := by decide +kernel
theorem sub5_232 : sub5 [-3, -2, 10] = true := by decide +kernel
theorem sub5_233 : sub5 [-3, -2, 11] = true := by decide +kernel
theorem sub5_234 : sub5 [-3, -1, -10] = true := by decide +kernel
theorem sub5_235 : sub5 [-3, -1, -9] = true := by decide +kernel
theorem sub5_236 : sub5 [-3, -1, -8] = true := by decide +kernel
theorem sub5_237 : sub5 [-3, -1, -7] = true := by decide +kernel
theorem sub5_238 : sub5 [-3, -1, -6] = true := by decide +kernel
theorem sub5_239 : sub5 [-3, -1, -5] = true := by decide +kernel
theorem sub5_240 : sub5 [-3, -1, -4] = true := by decide +kernel
theorem sub5_241 : sub5 [-3, -1, -3] = true := by decide +kernel
theorem sub5_242 : sub5 [-3, -1, -2] = true := by decide +kernel
theorem sub5_243 : sub5 [-3, -1, -1] = true := by decide +kernel
theorem sub5_244 : sub5 [-3, -1, 0] = true := by decide +kernel
theorem sub5_245 : sub5 [-3, -1, 1] = true := by decide +kernel
theorem sub5_246 : sub5 [-3, -1, 2] = true := by decide +kernel
theorem sub5_247 : sub5 [-3, -1, 3] = true := by decide +kernel
theorem sub5_248 : sub5 [-3, -1, 4] = true := by decide +kernel
theorem sub5_249 : sub5 [-3, -1, 5] = true := by decide +kernel
theorem sub5_250 : sub5 [-3, -1, 6] = true := by decide +kernel
theorem sub5_251 : sub5 [-3, -1, 7] = true := by decide +kernel
theorem sub5_252 : sub5 [-3, -1, 8] = true := by decide +kernel
theorem sub5_253 : sub5 [-3, -1, 9] = true := by decide +kernel
theorem sub5_254 : sub5 [-3, -1, 10] = true := by decide +kernel
theorem sub5_255 : sub5 [-3, -1, 11] = true := by decide +kernel
theorem sb5_7 : ∀ q ∈ blk5_7, sub5 q = true := by
  unfold blk5_7
  exact List.forall_mem_cons.2 ⟨sub5_224, List.forall_mem_cons.2 ⟨sub5_225, List.forall_mem_cons.2 ⟨sub5_226, List.forall_mem_cons.2 ⟨sub5_227, List.forall_mem_cons.2 ⟨sub5_228, List.forall_mem_cons.2 ⟨sub5_229, List.forall_mem_cons.2 ⟨sub5_230, List.forall_mem_cons.2 ⟨sub5_231, List.forall_mem_cons.2 ⟨sub5_232, List.forall_mem_cons.2 ⟨sub5_233, List.forall_mem_cons.2 ⟨sub5_234, List.forall_mem_cons.2 ⟨sub5_235, List.forall_mem_cons.2 ⟨sub5_236, List.forall_mem_cons.2 ⟨sub5_237, List.forall_mem_cons.2 ⟨sub5_238, List.forall_mem_cons.2 ⟨sub5_239, List.forall_mem_cons.2 ⟨sub5_240, List.forall_mem_cons.2 ⟨sub5_241, List.forall_mem_cons.2 ⟨sub5_242, List.forall_mem_cons.2 ⟨sub5_243, List.forall_mem_cons.2 ⟨sub5_244, List.forall_mem_cons.2 ⟨sub5_245, List.forall_mem_cons.2 ⟨sub5_246, List.forall_mem_cons.2 ⟨sub5_247, List.forall_mem_cons.2 ⟨sub5_248, List.forall_mem_cons.2 ⟨sub5_249, List.forall_mem_cons.2 ⟨sub5_250, List.forall_mem_cons.2 ⟨sub5_251, List.forall_mem_cons.2 ⟨sub5_252, List.forall_mem_cons.2 ⟨sub5_253, List.forall_mem_cons.2 ⟨sub5_254, List.forall_mem_cons.2 ⟨sub5_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C079
