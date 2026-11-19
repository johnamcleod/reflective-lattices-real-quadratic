import ReflectZphi.Data.Cert5.C049.Base

namespace ReflectZphi.Data.Cert5.C049
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub7_1984 : sub7 [4, 4, 0] = true := by decide +kernel
theorem sub7_1985 : sub7 [4, 4, 1] = true := by decide +kernel
theorem sub7_1986 : sub7 [4, 4, 2] = true := by decide +kernel
theorem sub7_1987 : sub7 [4, 4, 3] = true := by decide +kernel
theorem sub7_1988 : sub7 [4, 4, 4] = true := by decide +kernel
theorem sub7_1989 : sub7 [4, 4, 5] = true := by decide +kernel
theorem sub7_1990 : sub7 [4, 4, 6] = true := by decide +kernel
theorem sub7_1991 : sub7 [4, 5, -8] = true := by decide +kernel
theorem sub7_1992 : sub7 [4, 5, -7] = true := by decide +kernel
theorem sub7_1993 : sub7 [4, 5, -6] = true := by decide +kernel
theorem sub7_1994 : sub7 [4, 5, -5] = true := by decide +kernel
theorem sub7_1995 : sub7 [4, 5, -4] = true := by decide +kernel
theorem sub7_1996 : sub7 [4, 5, -3] = true := by decide +kernel
theorem sub7_1997 : sub7 [4, 5, -2] = true := by decide +kernel
theorem sub7_1998 : sub7 [4, 5, -1] = true := by decide +kernel
theorem sub7_1999 : sub7 [4, 5, 0] = true := by decide +kernel
theorem sub7_2000 : sub7 [4, 5, 1] = true := by decide +kernel
theorem sub7_2001 : sub7 [4, 5, 2] = true := by decide +kernel
theorem sub7_2002 : sub7 [4, 5, 3] = true := by decide +kernel
theorem sub7_2003 : sub7 [4, 5, 4] = true := by decide +kernel
theorem sub7_2004 : sub7 [4, 5, 5] = true := by decide +kernel
theorem sub7_2005 : sub7 [4, 6] = true := by decide +kernel
theorem sub7_2006 : sub7 [4, 7] = true := by decide +kernel
theorem sub7_2007 : sub7 [5, -6] = true := by decide +kernel
theorem sub7_2008 : sub7 [5, -5] = true := by decide +kernel
theorem sub7_2009 : sub7 [5, -4] = true := by decide +kernel
theorem sub7_2010 : sub7 [5, -3, -10] = true := by decide +kernel
theorem sub7_2011 : sub7 [5, -3, -9] = true := by decide +kernel
theorem sub7_2012 : sub7 [5, -3, -8] = true := by decide +kernel
theorem sub7_2013 : sub7 [5, -3, -7] = true := by decide +kernel
theorem sub7_2014 : sub7 [5, -3, -6] = true := by decide +kernel
theorem sub7_2015 : sub7 [5, -3, -5] = true := by decide +kernel
theorem sb7_62 : ∀ q ∈ blk7_62, sub7 q = true := by
  unfold blk7_62
  exact List.forall_mem_cons.2 ⟨sub7_1984, List.forall_mem_cons.2 ⟨sub7_1985, List.forall_mem_cons.2 ⟨sub7_1986, List.forall_mem_cons.2 ⟨sub7_1987, List.forall_mem_cons.2 ⟨sub7_1988, List.forall_mem_cons.2 ⟨sub7_1989, List.forall_mem_cons.2 ⟨sub7_1990, List.forall_mem_cons.2 ⟨sub7_1991, List.forall_mem_cons.2 ⟨sub7_1992, List.forall_mem_cons.2 ⟨sub7_1993, List.forall_mem_cons.2 ⟨sub7_1994, List.forall_mem_cons.2 ⟨sub7_1995, List.forall_mem_cons.2 ⟨sub7_1996, List.forall_mem_cons.2 ⟨sub7_1997, List.forall_mem_cons.2 ⟨sub7_1998, List.forall_mem_cons.2 ⟨sub7_1999, List.forall_mem_cons.2 ⟨sub7_2000, List.forall_mem_cons.2 ⟨sub7_2001, List.forall_mem_cons.2 ⟨sub7_2002, List.forall_mem_cons.2 ⟨sub7_2003, List.forall_mem_cons.2 ⟨sub7_2004, List.forall_mem_cons.2 ⟨sub7_2005, List.forall_mem_cons.2 ⟨sub7_2006, List.forall_mem_cons.2 ⟨sub7_2007, List.forall_mem_cons.2 ⟨sub7_2008, List.forall_mem_cons.2 ⟨sub7_2009, List.forall_mem_cons.2 ⟨sub7_2010, List.forall_mem_cons.2 ⟨sub7_2011, List.forall_mem_cons.2 ⟨sub7_2012, List.forall_mem_cons.2 ⟨sub7_2013, List.forall_mem_cons.2 ⟨sub7_2014, List.forall_mem_cons.2 ⟨sub7_2015, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_2016 : sub7 [5, -3, -4] = true := by decide +kernel
theorem sub7_2017 : sub7 [5, -3, -3] = true := by decide +kernel
theorem sub7_2018 : sub7 [5, -3, -2] = true := by decide +kernel
theorem sub7_2019 : sub7 [5, -3, -1] = true := by decide +kernel
theorem sub7_2020 : sub7 [5, -3, 0] = true := by decide +kernel
theorem sub7_2021 : sub7 [5, -3, 1] = true := by decide +kernel
theorem sub7_2022 : sub7 [5, -3, 2] = true := by decide +kernel
theorem sub7_2023 : sub7 [5, -3, 3] = true := by decide +kernel
theorem sub7_2024 : sub7 [5, -3, 4] = true := by decide +kernel
theorem sub7_2025 : sub7 [5, -2, -10] = true := by decide +kernel
theorem sub7_2026 : sub7 [5, -2, -9] = true := by decide +kernel
theorem sub7_2027 : sub7 [5, -2, -8] = true := by decide +kernel
theorem sub7_2028 : sub7 [5, -2, -7] = true := by decide +kernel
theorem sub7_2029 : sub7 [5, -2, -6] = true := by decide +kernel
theorem sub7_2030 : sub7 [5, -2, -5] = true := by decide +kernel
theorem sub7_2031 : sub7 [5, -2, -4] = true := by decide +kernel
theorem sub7_2032 : sub7 [5, -2, -3] = true := by decide +kernel
theorem sub7_2033 : sub7 [5, -2, -2] = true := by decide +kernel
theorem sub7_2034 : sub7 [5, -2, -1] = true := by decide +kernel
theorem sub7_2035 : sub7 [5, -2, 0] = true := by decide +kernel
theorem sub7_2036 : sub7 [5, -2, 1] = true := by decide +kernel
theorem sub7_2037 : sub7 [5, -2, 2] = true := by decide +kernel
theorem sub7_2038 : sub7 [5, -2, 3] = true := by decide +kernel
theorem sub7_2039 : sub7 [5, -2, 4] = true := by decide +kernel
theorem sub7_2040 : sub7 [5, -2, 5] = true := by decide +kernel
theorem sub7_2041 : sub7 [5, -1, -10] = true := by decide +kernel
theorem sub7_2042 : sub7 [5, -1, -9] = true := by decide +kernel
theorem sub7_2043 : sub7 [5, -1, -8] = true := by decide +kernel
theorem sub7_2044 : sub7 [5, -1, -7] = true := by decide +kernel
theorem sub7_2045 : sub7 [5, -1, -6] = true := by decide +kernel
theorem sub7_2046 : sub7 [5, -1, -5] = true := by decide +kernel
theorem sub7_2047 : sub7 [5, -1, -4] = true := by decide +kernel
theorem sb7_63 : ∀ q ∈ blk7_63, sub7 q = true := by
  unfold blk7_63
  exact List.forall_mem_cons.2 ⟨sub7_2016, List.forall_mem_cons.2 ⟨sub7_2017, List.forall_mem_cons.2 ⟨sub7_2018, List.forall_mem_cons.2 ⟨sub7_2019, List.forall_mem_cons.2 ⟨sub7_2020, List.forall_mem_cons.2 ⟨sub7_2021, List.forall_mem_cons.2 ⟨sub7_2022, List.forall_mem_cons.2 ⟨sub7_2023, List.forall_mem_cons.2 ⟨sub7_2024, List.forall_mem_cons.2 ⟨sub7_2025, List.forall_mem_cons.2 ⟨sub7_2026, List.forall_mem_cons.2 ⟨sub7_2027, List.forall_mem_cons.2 ⟨sub7_2028, List.forall_mem_cons.2 ⟨sub7_2029, List.forall_mem_cons.2 ⟨sub7_2030, List.forall_mem_cons.2 ⟨sub7_2031, List.forall_mem_cons.2 ⟨sub7_2032, List.forall_mem_cons.2 ⟨sub7_2033, List.forall_mem_cons.2 ⟨sub7_2034, List.forall_mem_cons.2 ⟨sub7_2035, List.forall_mem_cons.2 ⟨sub7_2036, List.forall_mem_cons.2 ⟨sub7_2037, List.forall_mem_cons.2 ⟨sub7_2038, List.forall_mem_cons.2 ⟨sub7_2039, List.forall_mem_cons.2 ⟨sub7_2040, List.forall_mem_cons.2 ⟨sub7_2041, List.forall_mem_cons.2 ⟨sub7_2042, List.forall_mem_cons.2 ⟨sub7_2043, List.forall_mem_cons.2 ⟨sub7_2044, List.forall_mem_cons.2 ⟨sub7_2045, List.forall_mem_cons.2 ⟨sub7_2046, List.forall_mem_cons.2 ⟨sub7_2047, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_2048 : sub7 [5, -1, -3] = true := by decide +kernel
theorem sub7_2049 : sub7 [5, -1, -2] = true := by decide +kernel
theorem sub7_2050 : sub7 [5, -1, -1] = true := by decide +kernel
theorem sub7_2051 : sub7 [5, -1, 0] = true := by decide +kernel
theorem sub7_2052 : sub7 [5, -1, 1] = true := by decide +kernel
theorem sub7_2053 : sub7 [5, -1, 2] = true := by decide +kernel
theorem sub7_2054 : sub7 [5, -1, 3] = true := by decide +kernel
theorem sub7_2055 : sub7 [5, -1, 4] = true := by decide +kernel
theorem sub7_2056 : sub7 [5, -1, 5] = true := by decide +kernel
theorem sub7_2057 : sub7 [5, 0, -11] = true := by decide +kernel
theorem sub7_2058 : sub7 [5, 0, -10] = true := by decide +kernel
theorem sub7_2059 : sub7 [5, 0, -9] = true := by decide +kernel
theorem sub7_2060 : sub7 [5, 0, -8] = true := by decide +kernel
theorem sub7_2061 : sub7 [5, 0, -7] = true := by decide +kernel
theorem sub7_2062 : sub7 [5, 0, -6] = true := by decide +kernel
theorem sub7_2063 : sub7 [5, 0, -5] = true := by decide +kernel
theorem sub7_2064 : sub7 [5, 0, -4] = true := by decide +kernel
theorem sub7_2065 : sub7 [5, 0, -3] = true := by decide +kernel
theorem sub7_2066 : sub7 [5, 0, -2] = true := by decide +kernel
theorem sub7_2067 : sub7 [5, 0, -1] = true := by decide +kernel
theorem sub7_2068 : sub7 [5, 0, 0] = true := by decide +kernel
theorem sub7_2069 : sub7 [5, 0, 1] = true := by decide +kernel
theorem sub7_2070 : sub7 [5, 0, 2] = true := by decide +kernel
theorem sub7_2071 : sub7 [5, 0, 3] = true := by decide +kernel
theorem sub7_2072 : sub7 [5, 0, 4] = true := by decide +kernel
theorem sub7_2073 : sub7 [5, 0, 5] = true := by decide +kernel
theorem sub7_2074 : sub7 [5, 0, 6] = true := by decide +kernel
theorem sub7_2075 : sub7 [5, 1, -10] = true := by decide +kernel
theorem sub7_2076 : sub7 [5, 1, -9] = true := by decide +kernel
theorem sub7_2077 : sub7 [5, 1, -8] = true := by decide +kernel
theorem sub7_2078 : sub7 [5, 1, -7] = true := by decide +kernel
theorem sub7_2079 : sub7 [5, 1, -6] = true := by decide +kernel
theorem sb7_64 : ∀ q ∈ blk7_64, sub7 q = true := by
  unfold blk7_64
  exact List.forall_mem_cons.2 ⟨sub7_2048, List.forall_mem_cons.2 ⟨sub7_2049, List.forall_mem_cons.2 ⟨sub7_2050, List.forall_mem_cons.2 ⟨sub7_2051, List.forall_mem_cons.2 ⟨sub7_2052, List.forall_mem_cons.2 ⟨sub7_2053, List.forall_mem_cons.2 ⟨sub7_2054, List.forall_mem_cons.2 ⟨sub7_2055, List.forall_mem_cons.2 ⟨sub7_2056, List.forall_mem_cons.2 ⟨sub7_2057, List.forall_mem_cons.2 ⟨sub7_2058, List.forall_mem_cons.2 ⟨sub7_2059, List.forall_mem_cons.2 ⟨sub7_2060, List.forall_mem_cons.2 ⟨sub7_2061, List.forall_mem_cons.2 ⟨sub7_2062, List.forall_mem_cons.2 ⟨sub7_2063, List.forall_mem_cons.2 ⟨sub7_2064, List.forall_mem_cons.2 ⟨sub7_2065, List.forall_mem_cons.2 ⟨sub7_2066, List.forall_mem_cons.2 ⟨sub7_2067, List.forall_mem_cons.2 ⟨sub7_2068, List.forall_mem_cons.2 ⟨sub7_2069, List.forall_mem_cons.2 ⟨sub7_2070, List.forall_mem_cons.2 ⟨sub7_2071, List.forall_mem_cons.2 ⟨sub7_2072, List.forall_mem_cons.2 ⟨sub7_2073, List.forall_mem_cons.2 ⟨sub7_2074, List.forall_mem_cons.2 ⟨sub7_2075, List.forall_mem_cons.2 ⟨sub7_2076, List.forall_mem_cons.2 ⟨sub7_2077, List.forall_mem_cons.2 ⟨sub7_2078, List.forall_mem_cons.2 ⟨sub7_2079, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_2080 : sub7 [5, 1, -5] = true := by decide +kernel
theorem sub7_2081 : sub7 [5, 1, -4] = true := by decide +kernel
theorem sub7_2082 : sub7 [5, 1, -3] = true := by decide +kernel
theorem sub7_2083 : sub7 [5, 1, -2] = true := by decide +kernel
theorem sub7_2084 : sub7 [5, 1, -1] = true := by decide +kernel
theorem sub7_2085 : sub7 [5, 1, 0] = true := by decide +kernel
theorem sub7_2086 : sub7 [5, 1, 1] = true := by decide +kernel
theorem sub7_2087 : sub7 [5, 1, 2] = true := by decide +kernel
theorem sub7_2088 : sub7 [5, 1, 3] = true := by decide +kernel
theorem sub7_2089 : sub7 [5, 1, 4] = true := by decide +kernel
theorem sub7_2090 : sub7 [5, 1, 5] = true := by decide +kernel
theorem sub7_2091 : sub7 [5, 1, 6] = true := by decide +kernel
theorem sub7_2092 : sub7 [5, 2, -10] = true := by decide +kernel
theorem sub7_2093 : sub7 [5, 2, -9] = true := by decide +kernel
theorem sub7_2094 : sub7 [5, 2, -8] = true := by decide +kernel
theorem sub7_2095 : sub7 [5, 2, -7] = true := by decide +kernel
theorem sub7_2096 : sub7 [5, 2, -6] = true := by decide +kernel
theorem sub7_2097 : sub7 [5, 2, -5] = true := by decide +kernel
theorem sub7_2098 : sub7 [5, 2, -4] = true := by decide +kernel
theorem sub7_2099 : sub7 [5, 2, -3] = true := by decide +kernel
theorem sub7_2100 : sub7 [5, 2, -2] = true := by decide +kernel
theorem sub7_2101 : sub7 [5, 2, -1] = true := by decide +kernel
theorem sub7_2102 : sub7 [5, 2, 0] = true := by decide +kernel
theorem sub7_2103 : sub7 [5, 2, 1] = true := by decide +kernel
theorem sub7_2104 : sub7 [5, 2, 2] = true := by decide +kernel
theorem sub7_2105 : sub7 [5, 2, 3] = true := by decide +kernel
theorem sub7_2106 : sub7 [5, 2, 4] = true := by decide +kernel
theorem sub7_2107 : sub7 [5, 2, 5] = true := by decide +kernel
theorem sub7_2108 : sub7 [5, 2, 6] = true := by decide +kernel
theorem sub7_2109 : sub7 [5, 3, -10] = true := by decide +kernel
theorem sub7_2110 : sub7 [5, 3, -9] = true := by decide +kernel
theorem sub7_2111 : sub7 [5, 3, -8] = true := by decide +kernel
theorem sb7_65 : ∀ q ∈ blk7_65, sub7 q = true := by
  unfold blk7_65
  exact List.forall_mem_cons.2 ⟨sub7_2080, List.forall_mem_cons.2 ⟨sub7_2081, List.forall_mem_cons.2 ⟨sub7_2082, List.forall_mem_cons.2 ⟨sub7_2083, List.forall_mem_cons.2 ⟨sub7_2084, List.forall_mem_cons.2 ⟨sub7_2085, List.forall_mem_cons.2 ⟨sub7_2086, List.forall_mem_cons.2 ⟨sub7_2087, List.forall_mem_cons.2 ⟨sub7_2088, List.forall_mem_cons.2 ⟨sub7_2089, List.forall_mem_cons.2 ⟨sub7_2090, List.forall_mem_cons.2 ⟨sub7_2091, List.forall_mem_cons.2 ⟨sub7_2092, List.forall_mem_cons.2 ⟨sub7_2093, List.forall_mem_cons.2 ⟨sub7_2094, List.forall_mem_cons.2 ⟨sub7_2095, List.forall_mem_cons.2 ⟨sub7_2096, List.forall_mem_cons.2 ⟨sub7_2097, List.forall_mem_cons.2 ⟨sub7_2098, List.forall_mem_cons.2 ⟨sub7_2099, List.forall_mem_cons.2 ⟨sub7_2100, List.forall_mem_cons.2 ⟨sub7_2101, List.forall_mem_cons.2 ⟨sub7_2102, List.forall_mem_cons.2 ⟨sub7_2103, List.forall_mem_cons.2 ⟨sub7_2104, List.forall_mem_cons.2 ⟨sub7_2105, List.forall_mem_cons.2 ⟨sub7_2106, List.forall_mem_cons.2 ⟨sub7_2107, List.forall_mem_cons.2 ⟨sub7_2108, List.forall_mem_cons.2 ⟨sub7_2109, List.forall_mem_cons.2 ⟨sub7_2110, List.forall_mem_cons.2 ⟨sub7_2111, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_2112 : sub7 [5, 3, -7] = true := by decide +kernel
theorem sub7_2113 : sub7 [5, 3, -6] = true := by decide +kernel
theorem sub7_2114 : sub7 [5, 3, -5] = true := by decide +kernel
theorem sub7_2115 : sub7 [5, 3, -4] = true := by decide +kernel
theorem sub7_2116 : sub7 [5, 3, -3] = true := by decide +kernel
theorem sub7_2117 : sub7 [5, 3, -2] = true := by decide +kernel
theorem sub7_2118 : sub7 [5, 3, -1] = true := by decide +kernel
theorem sub7_2119 : sub7 [5, 3, 0] = true := by decide +kernel
theorem sub7_2120 : sub7 [5, 3, 1] = true := by decide +kernel
theorem sub7_2121 : sub7 [5, 3, 2] = true := by decide +kernel
theorem sub7_2122 : sub7 [5, 3, 3] = true := by decide +kernel
theorem sub7_2123 : sub7 [5, 3, 4] = true := by decide +kernel
theorem sub7_2124 : sub7 [5, 3, 5] = true := by decide +kernel
theorem sub7_2125 : sub7 [5, 4, -9] = true := by decide +kernel
theorem sub7_2126 : sub7 [5, 4, -8] = true := by decide +kernel
theorem sub7_2127 : sub7 [5, 4, -7] = true := by decide +kernel
theorem sub7_2128 : sub7 [5, 4, -6] = true := by decide +kernel
theorem sub7_2129 : sub7 [5, 4, -5] = true := by decide +kernel
theorem sub7_2130 : sub7 [5, 4, -4] = true := by decide +kernel
theorem sub7_2131 : sub7 [5, 4, -3] = true := by decide +kernel
theorem sub7_2132 : sub7 [5, 4, -2] = true := by decide +kernel
theorem sub7_2133 : sub7 [5, 4, -1] = true := by decide +kernel
theorem sub7_2134 : sub7 [5, 4, 0] = true := by decide +kernel
theorem sub7_2135 : sub7 [5, 4, 1] = true := by decide +kernel
theorem sub7_2136 : sub7 [5, 4, 2] = true := by decide +kernel
theorem sub7_2137 : sub7 [5, 4, 3] = true := by decide +kernel
theorem sub7_2138 : sub7 [5, 4, 4] = true := by decide +kernel
theorem sub7_2139 : sub7 [5, 4, 5] = true := by decide +kernel
theorem sub7_2140 : sub7 [5, 5] = true := by decide +kernel
theorem sub7_2141 : sub7 [5, 6] = true := by decide +kernel
theorem sub7_2142 : sub7 [5, 7] = true := by decide +kernel
theorem sub7_2143 : sub7 [6, -5] = true := by decide +kernel
theorem sb7_66 : ∀ q ∈ blk7_66, sub7 q = true := by
  unfold blk7_66
  exact List.forall_mem_cons.2 ⟨sub7_2112, List.forall_mem_cons.2 ⟨sub7_2113, List.forall_mem_cons.2 ⟨sub7_2114, List.forall_mem_cons.2 ⟨sub7_2115, List.forall_mem_cons.2 ⟨sub7_2116, List.forall_mem_cons.2 ⟨sub7_2117, List.forall_mem_cons.2 ⟨sub7_2118, List.forall_mem_cons.2 ⟨sub7_2119, List.forall_mem_cons.2 ⟨sub7_2120, List.forall_mem_cons.2 ⟨sub7_2121, List.forall_mem_cons.2 ⟨sub7_2122, List.forall_mem_cons.2 ⟨sub7_2123, List.forall_mem_cons.2 ⟨sub7_2124, List.forall_mem_cons.2 ⟨sub7_2125, List.forall_mem_cons.2 ⟨sub7_2126, List.forall_mem_cons.2 ⟨sub7_2127, List.forall_mem_cons.2 ⟨sub7_2128, List.forall_mem_cons.2 ⟨sub7_2129, List.forall_mem_cons.2 ⟨sub7_2130, List.forall_mem_cons.2 ⟨sub7_2131, List.forall_mem_cons.2 ⟨sub7_2132, List.forall_mem_cons.2 ⟨sub7_2133, List.forall_mem_cons.2 ⟨sub7_2134, List.forall_mem_cons.2 ⟨sub7_2135, List.forall_mem_cons.2 ⟨sub7_2136, List.forall_mem_cons.2 ⟨sub7_2137, List.forall_mem_cons.2 ⟨sub7_2138, List.forall_mem_cons.2 ⟨sub7_2139, List.forall_mem_cons.2 ⟨sub7_2140, List.forall_mem_cons.2 ⟨sub7_2141, List.forall_mem_cons.2 ⟨sub7_2142, List.forall_mem_cons.2 ⟨sub7_2143, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_2144 : sub7 [6, -4] = true := by decide +kernel
theorem sub7_2145 : sub7 [6, -3] = true := by decide +kernel
theorem sub7_2146 : sub7 [6, -2] = true := by decide +kernel
theorem sub7_2147 : sub7 [6, -1, -10] = true := by decide +kernel
theorem sub7_2148 : sub7 [6, -1, -9] = true := by decide +kernel
theorem sub7_2149 : sub7 [6, -1, -8] = true := by decide +kernel
theorem sub7_2150 : sub7 [6, -1, -7] = true := by decide +kernel
theorem sub7_2151 : sub7 [6, -1, -6] = true := by decide +kernel
theorem sub7_2152 : sub7 [6, -1, -5] = true := by decide +kernel
theorem sub7_2153 : sub7 [6, -1, -4] = true := by decide +kernel
theorem sub7_2154 : sub7 [6, -1, -3] = true := by decide +kernel
theorem sub7_2155 : sub7 [6, -1, -2] = true := by decide +kernel
theorem sub7_2156 : sub7 [6, -1, -1] = true := by decide +kernel
theorem sub7_2157 : sub7 [6, -1, 0] = true := by decide +kernel
theorem sub7_2158 : sub7 [6, -1, 1] = true := by decide +kernel
theorem sub7_2159 : sub7 [6, -1, 2] = true := by decide +kernel
theorem sub7_2160 : sub7 [6, -1, 3] = true := by decide +kernel
theorem sub7_2161 : sub7 [6, -1, 4] = true := by decide +kernel
theorem sub7_2162 : sub7 [6, 0, -10] = true := by decide +kernel
theorem sub7_2163 : sub7 [6, 0, -9] = true := by decide +kernel
theorem sub7_2164 : sub7 [6, 0, -8] = true := by decide +kernel
theorem sub7_2165 : sub7 [6, 0, -7] = true := by decide +kernel
theorem sub7_2166 : sub7 [6, 0, -6] = true := by decide +kernel
theorem sub7_2167 : sub7 [6, 0, -5] = true := by decide +kernel
theorem sub7_2168 : sub7 [6, 0, -4] = true := by decide +kernel
theorem sub7_2169 : sub7 [6, 0, -3] = true := by decide +kernel
theorem sub7_2170 : sub7 [6, 0, -2] = true := by decide +kernel
theorem sub7_2171 : sub7 [6, 0, -1] = true := by decide +kernel
theorem sub7_2172 : sub7 [6, 0, 0] = true := by decide +kernel
theorem sub7_2173 : sub7 [6, 0, 1] = true := by decide +kernel
theorem sub7_2174 : sub7 [6, 0, 2] = true := by decide +kernel
theorem sub7_2175 : sub7 [6, 0, 3] = true := by decide +kernel
theorem sb7_67 : ∀ q ∈ blk7_67, sub7 q = true := by
  unfold blk7_67
  exact List.forall_mem_cons.2 ⟨sub7_2144, List.forall_mem_cons.2 ⟨sub7_2145, List.forall_mem_cons.2 ⟨sub7_2146, List.forall_mem_cons.2 ⟨sub7_2147, List.forall_mem_cons.2 ⟨sub7_2148, List.forall_mem_cons.2 ⟨sub7_2149, List.forall_mem_cons.2 ⟨sub7_2150, List.forall_mem_cons.2 ⟨sub7_2151, List.forall_mem_cons.2 ⟨sub7_2152, List.forall_mem_cons.2 ⟨sub7_2153, List.forall_mem_cons.2 ⟨sub7_2154, List.forall_mem_cons.2 ⟨sub7_2155, List.forall_mem_cons.2 ⟨sub7_2156, List.forall_mem_cons.2 ⟨sub7_2157, List.forall_mem_cons.2 ⟨sub7_2158, List.forall_mem_cons.2 ⟨sub7_2159, List.forall_mem_cons.2 ⟨sub7_2160, List.forall_mem_cons.2 ⟨sub7_2161, List.forall_mem_cons.2 ⟨sub7_2162, List.forall_mem_cons.2 ⟨sub7_2163, List.forall_mem_cons.2 ⟨sub7_2164, List.forall_mem_cons.2 ⟨sub7_2165, List.forall_mem_cons.2 ⟨sub7_2166, List.forall_mem_cons.2 ⟨sub7_2167, List.forall_mem_cons.2 ⟨sub7_2168, List.forall_mem_cons.2 ⟨sub7_2169, List.forall_mem_cons.2 ⟨sub7_2170, List.forall_mem_cons.2 ⟨sub7_2171, List.forall_mem_cons.2 ⟨sub7_2172, List.forall_mem_cons.2 ⟨sub7_2173, List.forall_mem_cons.2 ⟨sub7_2174, List.forall_mem_cons.2 ⟨sub7_2175, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_2176 : sub7 [6, 0, 4] = true := by decide +kernel
theorem sub7_2177 : sub7 [6, 1, -10] = true := by decide +kernel
theorem sub7_2178 : sub7 [6, 1, -9] = true := by decide +kernel
theorem sub7_2179 : sub7 [6, 1, -8] = true := by decide +kernel
theorem sub7_2180 : sub7 [6, 1, -7] = true := by decide +kernel
theorem sub7_2181 : sub7 [6, 1, -6] = true := by decide +kernel
theorem sub7_2182 : sub7 [6, 1, -5] = true := by decide +kernel
theorem sub7_2183 : sub7 [6, 1, -4] = true := by decide +kernel
theorem sub7_2184 : sub7 [6, 1, -3] = true := by decide +kernel
theorem sub7_2185 : sub7 [6, 1, -2] = true := by decide +kernel
theorem sub7_2186 : sub7 [6, 1, -1] = true := by decide +kernel
theorem sub7_2187 : sub7 [6, 1, 0] = true := by decide +kernel
theorem sub7_2188 : sub7 [6, 1, 1] = true := by decide +kernel
theorem sub7_2189 : sub7 [6, 1, 2] = true := by decide +kernel
theorem sub7_2190 : sub7 [6, 1, 3] = true := by decide +kernel
theorem sub7_2191 : sub7 [6, 1, 4] = true := by decide +kernel
theorem sub7_2192 : sub7 [6, 2, -10] = true := by decide +kernel
theorem sub7_2193 : sub7 [6, 2, -9] = true := by decide +kernel
theorem sub7_2194 : sub7 [6, 2, -8] = true := by decide +kernel
theorem sub7_2195 : sub7 [6, 2, -7] = true := by decide +kernel
theorem sub7_2196 : sub7 [6, 2, -6] = true := by decide +kernel
theorem sub7_2197 : sub7 [6, 2, -5] = true := by decide +kernel
theorem sub7_2198 : sub7 [6, 2, -4] = true := by decide +kernel
theorem sub7_2199 : sub7 [6, 2, -3] = true := by decide +kernel
theorem sub7_2200 : sub7 [6, 2, -2] = true := by decide +kernel
theorem sub7_2201 : sub7 [6, 2, -1] = true := by decide +kernel
theorem sub7_2202 : sub7 [6, 2, 0] = true := by decide +kernel
theorem sub7_2203 : sub7 [6, 2, 1] = true := by decide +kernel
theorem sub7_2204 : sub7 [6, 2, 2] = true := by decide +kernel
theorem sub7_2205 : sub7 [6, 2, 3] = true := by decide +kernel
theorem sub7_2206 : sub7 [6, 2, 4] = true := by decide +kernel
theorem sub7_2207 : sub7 [6, 3] = true := by decide +kernel
theorem sb7_68 : ∀ q ∈ blk7_68, sub7 q = true := by
  unfold blk7_68
  exact List.forall_mem_cons.2 ⟨sub7_2176, List.forall_mem_cons.2 ⟨sub7_2177, List.forall_mem_cons.2 ⟨sub7_2178, List.forall_mem_cons.2 ⟨sub7_2179, List.forall_mem_cons.2 ⟨sub7_2180, List.forall_mem_cons.2 ⟨sub7_2181, List.forall_mem_cons.2 ⟨sub7_2182, List.forall_mem_cons.2 ⟨sub7_2183, List.forall_mem_cons.2 ⟨sub7_2184, List.forall_mem_cons.2 ⟨sub7_2185, List.forall_mem_cons.2 ⟨sub7_2186, List.forall_mem_cons.2 ⟨sub7_2187, List.forall_mem_cons.2 ⟨sub7_2188, List.forall_mem_cons.2 ⟨sub7_2189, List.forall_mem_cons.2 ⟨sub7_2190, List.forall_mem_cons.2 ⟨sub7_2191, List.forall_mem_cons.2 ⟨sub7_2192, List.forall_mem_cons.2 ⟨sub7_2193, List.forall_mem_cons.2 ⟨sub7_2194, List.forall_mem_cons.2 ⟨sub7_2195, List.forall_mem_cons.2 ⟨sub7_2196, List.forall_mem_cons.2 ⟨sub7_2197, List.forall_mem_cons.2 ⟨sub7_2198, List.forall_mem_cons.2 ⟨sub7_2199, List.forall_mem_cons.2 ⟨sub7_2200, List.forall_mem_cons.2 ⟨sub7_2201, List.forall_mem_cons.2 ⟨sub7_2202, List.forall_mem_cons.2 ⟨sub7_2203, List.forall_mem_cons.2 ⟨sub7_2204, List.forall_mem_cons.2 ⟨sub7_2205, List.forall_mem_cons.2 ⟨sub7_2206, List.forall_mem_cons.2 ⟨sub7_2207, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_2208 : sub7 [6, 4] = true := by decide +kernel
theorem sub7_2209 : sub7 [6, 5] = true := by decide +kernel
theorem sub7_2210 : sub7 [6, 6] = true := by decide +kernel
theorem sub7_2211 : sub7 [7, -4] = true := by decide +kernel
theorem sub7_2212 : sub7 [7, -3] = true := by decide +kernel
theorem sub7_2213 : sub7 [7, -2] = true := by decide +kernel
theorem sub7_2214 : sub7 [7, -1] = true := by decide +kernel
theorem sub7_2215 : sub7 [7, 0] = true := by decide +kernel
theorem sub7_2216 : sub7 [7, 1] = true := by decide +kernel
theorem sub7_2217 : sub7 [7, 2] = true := by decide +kernel
theorem sub7_2218 : sub7 [7, 3] = true := by decide +kernel
theorem sub7_2219 : sub7 [7, 4] = true := by decide +kernel
theorem sub7_2220 : sub7 [7, 5] = true := by decide +kernel
theorem sub7_2221 : sub7 [8, -2] = true := by decide +kernel
theorem sub7_2222 : sub7 [8, -1] = true := by decide +kernel
theorem sub7_2223 : sub7 [8, 0] = true := by decide +kernel
theorem sub7_2224 : sub7 [8, 1] = true := by decide +kernel
theorem sub7_2225 : sub7 [8, 2] = true := by decide +kernel
theorem sub7_2226 : sub7 [8, 3] = true := by decide +kernel
theorem sb7_69 : ∀ q ∈ blk7_69, sub7 q = true := by
  unfold blk7_69
  exact List.forall_mem_cons.2 ⟨sub7_2208, List.forall_mem_cons.2 ⟨sub7_2209, List.forall_mem_cons.2 ⟨sub7_2210, List.forall_mem_cons.2 ⟨sub7_2211, List.forall_mem_cons.2 ⟨sub7_2212, List.forall_mem_cons.2 ⟨sub7_2213, List.forall_mem_cons.2 ⟨sub7_2214, List.forall_mem_cons.2 ⟨sub7_2215, List.forall_mem_cons.2 ⟨sub7_2216, List.forall_mem_cons.2 ⟨sub7_2217, List.forall_mem_cons.2 ⟨sub7_2218, List.forall_mem_cons.2 ⟨sub7_2219, List.forall_mem_cons.2 ⟨sub7_2220, List.forall_mem_cons.2 ⟨sub7_2221, List.forall_mem_cons.2 ⟨sub7_2222, List.forall_mem_cons.2 ⟨sub7_2223, List.forall_mem_cons.2 ⟨sub7_2224, List.forall_mem_cons.2 ⟨sub7_2225, List.forall_mem_cons.2 ⟨sub7_2226, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C049
