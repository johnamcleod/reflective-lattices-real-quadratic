import ReflectZphi.Data.Cert5.C131.Base

namespace ReflectZphi.Data.Cert5.C131

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd11_0_2016 : subd11_0 [4, 6, -5] = true := by decide +kernel
theorem subd11_0_2017 : subd11_0 [4, 6, -4] = true := by decide +kernel
theorem subd11_0_2018 : subd11_0 [4, 6, -3] = true := by decide +kernel
theorem subd11_0_2019 : subd11_0 [4, 6, -2] = true := by decide +kernel
theorem subd11_0_2020 : subd11_0 [4, 6, -1] = true := by decide +kernel
theorem subd11_0_2021 : subd11_0 [4, 6, 0] = true := by decide +kernel
theorem subd11_0_2022 : subd11_0 [4, 6, 1] = true := by decide +kernel
theorem subd11_0_2023 : subd11_0 [4, 6, 2] = true := by decide +kernel
theorem subd11_0_2024 : subd11_0 [4, 6, 3] = true := by decide +kernel
theorem subd11_0_2025 : subd11_0 [4, 6, 4] = true := by decide +kernel
theorem subd11_0_2026 : subd11_0 [4, 6, 5] = true := by decide +kernel
theorem subd11_0_2027 : subd11_0 [4, 6, 6] = true := by decide +kernel
theorem subd11_0_2028 : subd11_0 [4, 6, 7] = true := by decide +kernel
theorem subd11_0_2029 : subd11_0 [4, 7] = true := by decide +kernel
theorem subd11_0_2030 : subd11_0 [4, 8] = true := by decide +kernel
theorem subd11_0_2031 : subd11_0 [4, 9] = true := by decide +kernel
theorem subd11_0_2032 : subd11_0 [4, 10] = true := by decide +kernel
theorem subd11_0_2033 : subd11_0 [5, -6] = true := by decide +kernel
theorem subd11_0_2034 : subd11_0 [5, -5] = true := by decide +kernel
theorem subd11_0_2035 : subd11_0 [5, -4] = true := by decide +kernel
theorem subd11_0_2036 : subd11_0 [5, -3] = true := by decide +kernel
theorem subd11_0_2037 : subd11_0 [5, -2] = true := by decide +kernel
theorem subd11_0_2038 : subd11_0 [5, -1, -6] = true := by decide +kernel
theorem subd11_0_2039 : subd11_0 [5, -1, -5] = true := by decide +kernel
theorem subd11_0_2040 : subd11_0 [5, -1, -4] = true := by decide +kernel
theorem subd11_0_2041 : subd11_0 [5, -1, -3] = true := by decide +kernel
theorem subd11_0_2042 : subd11_0 [5, -1, -2] = true := by decide +kernel
theorem subd11_0_2043 : subd11_0 [5, -1, -1] = true := by decide +kernel
theorem subd11_0_2044 : subd11_0 [5, -1, 0] = true := by decide +kernel
theorem subd11_0_2045 : subd11_0 [5, -1, 1] = true := by decide +kernel
theorem subd11_0_2046 : subd11_0 [5, -1, 2] = true := by decide +kernel
theorem subd11_0_2047 : subd11_0 [5, -1, 3] = true := by decide +kernel
theorem sbd11_0_63 : ∀ q ∈ blkd11_0_63, subd11_0 q = true := by
  unfold blkd11_0_63
  exact List.forall_mem_cons.2 ⟨subd11_0_2016, List.forall_mem_cons.2 ⟨subd11_0_2017, List.forall_mem_cons.2 ⟨subd11_0_2018, List.forall_mem_cons.2 ⟨subd11_0_2019, List.forall_mem_cons.2 ⟨subd11_0_2020, List.forall_mem_cons.2 ⟨subd11_0_2021, List.forall_mem_cons.2 ⟨subd11_0_2022, List.forall_mem_cons.2 ⟨subd11_0_2023, List.forall_mem_cons.2 ⟨subd11_0_2024, List.forall_mem_cons.2 ⟨subd11_0_2025, List.forall_mem_cons.2 ⟨subd11_0_2026, List.forall_mem_cons.2 ⟨subd11_0_2027, List.forall_mem_cons.2 ⟨subd11_0_2028, List.forall_mem_cons.2 ⟨subd11_0_2029, List.forall_mem_cons.2 ⟨subd11_0_2030, List.forall_mem_cons.2 ⟨subd11_0_2031, List.forall_mem_cons.2 ⟨subd11_0_2032, List.forall_mem_cons.2 ⟨subd11_0_2033, List.forall_mem_cons.2 ⟨subd11_0_2034, List.forall_mem_cons.2 ⟨subd11_0_2035, List.forall_mem_cons.2 ⟨subd11_0_2036, List.forall_mem_cons.2 ⟨subd11_0_2037, List.forall_mem_cons.2 ⟨subd11_0_2038, List.forall_mem_cons.2 ⟨subd11_0_2039, List.forall_mem_cons.2 ⟨subd11_0_2040, List.forall_mem_cons.2 ⟨subd11_0_2041, List.forall_mem_cons.2 ⟨subd11_0_2042, List.forall_mem_cons.2 ⟨subd11_0_2043, List.forall_mem_cons.2 ⟨subd11_0_2044, List.forall_mem_cons.2 ⟨subd11_0_2045, List.forall_mem_cons.2 ⟨subd11_0_2046, List.forall_mem_cons.2 ⟨subd11_0_2047, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_2048 : subd11_0 [5, -1, 4] = true := by decide +kernel
theorem subd11_0_2049 : subd11_0 [5, -1, 5] = true := by decide +kernel
theorem subd11_0_2050 : subd11_0 [5, -1, 6] = true := by decide +kernel
theorem subd11_0_2051 : subd11_0 [5, -1, 7] = true := by decide +kernel
theorem subd11_0_2052 : subd11_0 [5, 0, -6] = true := by decide +kernel
theorem subd11_0_2053 : subd11_0 [5, 0, -5] = true := by decide +kernel
theorem subd11_0_2054 : subd11_0 [5, 0, -4] = true := by decide +kernel
theorem subd11_0_2055 : subd11_0 [5, 0, -3] = true := by decide +kernel
theorem subd11_0_2056 : subd11_0 [5, 0, -2] = true := by decide +kernel
theorem subd11_0_2057 : subd11_0 [5, 0, -1] = true := by decide +kernel
theorem subd11_0_2058 : subd11_0 [5, 0, 0] = true := by decide +kernel
theorem subd11_0_2059 : subd11_0 [5, 0, 1] = true := by decide +kernel
theorem subd11_0_2060 : subd11_0 [5, 0, 2] = true := by decide +kernel
theorem subd11_0_2061 : subd11_0 [5, 0, 3] = true := by decide +kernel
theorem subd11_0_2062 : subd11_0 [5, 0, 4] = true := by decide +kernel
theorem subd11_0_2063 : subd11_0 [5, 0, 5] = true := by decide +kernel
theorem subd11_0_2064 : subd11_0 [5, 0, 6] = true := by decide +kernel
theorem subd11_0_2065 : subd11_0 [5, 0, 7] = true := by decide +kernel
theorem subd11_0_2066 : subd11_0 [5, 0, 8] = true := by decide +kernel
theorem subd11_0_2067 : subd11_0 [5, 1, -6] = true := by decide +kernel
theorem subd11_0_2068 : subd11_0 [5, 1, -5] = true := by decide +kernel
theorem subd11_0_2069 : subd11_0 [5, 1, -4] = true := by decide +kernel
theorem subd11_0_2070 : subd11_0 [5, 1, -3] = true := by decide +kernel
theorem subd11_0_2071 : subd11_0 [5, 1, -2] = true := by decide +kernel
theorem subd11_0_2072 : subd11_0 [5, 1, -1] = true := by decide +kernel
theorem subd11_0_2073 : subd11_0 [5, 1, 0] = true := by decide +kernel
theorem subd11_0_2074 : subd11_0 [5, 1, 1] = true := by decide +kernel
theorem subd11_0_2075 : subd11_0 [5, 1, 2] = true := by decide +kernel
theorem subd11_0_2076 : subd11_0 [5, 1, 3] = true := by decide +kernel
theorem subd11_0_2077 : subd11_0 [5, 1, 4] = true := by decide +kernel
theorem subd11_0_2078 : subd11_0 [5, 1, 5] = true := by decide +kernel
theorem subd11_0_2079 : subd11_0 [5, 1, 6] = true := by decide +kernel
theorem sbd11_0_64 : ∀ q ∈ blkd11_0_64, subd11_0 q = true := by
  unfold blkd11_0_64
  exact List.forall_mem_cons.2 ⟨subd11_0_2048, List.forall_mem_cons.2 ⟨subd11_0_2049, List.forall_mem_cons.2 ⟨subd11_0_2050, List.forall_mem_cons.2 ⟨subd11_0_2051, List.forall_mem_cons.2 ⟨subd11_0_2052, List.forall_mem_cons.2 ⟨subd11_0_2053, List.forall_mem_cons.2 ⟨subd11_0_2054, List.forall_mem_cons.2 ⟨subd11_0_2055, List.forall_mem_cons.2 ⟨subd11_0_2056, List.forall_mem_cons.2 ⟨subd11_0_2057, List.forall_mem_cons.2 ⟨subd11_0_2058, List.forall_mem_cons.2 ⟨subd11_0_2059, List.forall_mem_cons.2 ⟨subd11_0_2060, List.forall_mem_cons.2 ⟨subd11_0_2061, List.forall_mem_cons.2 ⟨subd11_0_2062, List.forall_mem_cons.2 ⟨subd11_0_2063, List.forall_mem_cons.2 ⟨subd11_0_2064, List.forall_mem_cons.2 ⟨subd11_0_2065, List.forall_mem_cons.2 ⟨subd11_0_2066, List.forall_mem_cons.2 ⟨subd11_0_2067, List.forall_mem_cons.2 ⟨subd11_0_2068, List.forall_mem_cons.2 ⟨subd11_0_2069, List.forall_mem_cons.2 ⟨subd11_0_2070, List.forall_mem_cons.2 ⟨subd11_0_2071, List.forall_mem_cons.2 ⟨subd11_0_2072, List.forall_mem_cons.2 ⟨subd11_0_2073, List.forall_mem_cons.2 ⟨subd11_0_2074, List.forall_mem_cons.2 ⟨subd11_0_2075, List.forall_mem_cons.2 ⟨subd11_0_2076, List.forall_mem_cons.2 ⟨subd11_0_2077, List.forall_mem_cons.2 ⟨subd11_0_2078, List.forall_mem_cons.2 ⟨subd11_0_2079, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_2080 : subd11_0 [5, 1, 7] = true := by decide +kernel
theorem subd11_0_2081 : subd11_0 [5, 1, 8] = true := by decide +kernel
theorem subd11_0_2082 : subd11_0 [5, 2, -6] = true := by decide +kernel
theorem subd11_0_2083 : subd11_0 [5, 2, -5] = true := by decide +kernel
theorem subd11_0_2084 : subd11_0 [5, 2, -4] = true := by decide +kernel
theorem subd11_0_2085 : subd11_0 [5, 2, -3] = true := by decide +kernel
theorem subd11_0_2086 : subd11_0 [5, 2, -2] = true := by decide +kernel
theorem subd11_0_2087 : subd11_0 [5, 2, -1] = true := by decide +kernel
theorem subd11_0_2088 : subd11_0 [5, 2, 0] = true := by decide +kernel
theorem subd11_0_2089 : subd11_0 [5, 2, 1] = true := by decide +kernel
theorem subd11_0_2090 : subd11_0 [5, 2, 2] = true := by decide +kernel
theorem subd11_0_2091 : subd11_0 [5, 2, 3] = true := by decide +kernel
theorem subd11_0_2092 : subd11_0 [5, 2, 4] = true := by decide +kernel
theorem subd11_0_2093 : subd11_0 [5, 2, 5] = true := by decide +kernel
theorem subd11_0_2094 : subd11_0 [5, 2, 6] = true := by decide +kernel
theorem subd11_0_2095 : subd11_0 [5, 2, 7] = true := by decide +kernel
theorem subd11_0_2096 : subd11_0 [5, 2, 8] = true := by decide +kernel
theorem subd11_0_2097 : subd11_0 [5, 3, -6] = true := by decide +kernel
theorem subd11_0_2098 : subd11_0 [5, 3, -5] = true := by decide +kernel
theorem subd11_0_2099 : subd11_0 [5, 3, -4] = true := by decide +kernel
theorem subd11_0_2100 : subd11_0 [5, 3, -3] = true := by decide +kernel
theorem subd11_0_2101 : subd11_0 [5, 3, -2] = true := by decide +kernel
theorem subd11_0_2102 : subd11_0 [5, 3, -1] = true := by decide +kernel
theorem subd11_0_2103 : subd11_0 [5, 3, 0] = true := by decide +kernel
theorem subd11_0_2104 : subd11_0 [5, 3, 1] = true := by decide +kernel
theorem subd11_0_2105 : subd11_0 [5, 3, 2] = true := by decide +kernel
theorem subd11_0_2106 : subd11_0 [5, 3, 3] = true := by decide +kernel
theorem subd11_0_2107 : subd11_0 [5, 3, 4] = true := by decide +kernel
theorem subd11_0_2108 : subd11_0 [5, 3, 5] = true := by decide +kernel
theorem subd11_0_2109 : subd11_0 [5, 3, 6] = true := by decide +kernel
theorem subd11_0_2110 : subd11_0 [5, 3, 7] = true := by decide +kernel
theorem subd11_0_2111 : subd11_0 [5, 3, 8] = true := by decide +kernel
theorem sbd11_0_65 : ∀ q ∈ blkd11_0_65, subd11_0 q = true := by
  unfold blkd11_0_65
  exact List.forall_mem_cons.2 ⟨subd11_0_2080, List.forall_mem_cons.2 ⟨subd11_0_2081, List.forall_mem_cons.2 ⟨subd11_0_2082, List.forall_mem_cons.2 ⟨subd11_0_2083, List.forall_mem_cons.2 ⟨subd11_0_2084, List.forall_mem_cons.2 ⟨subd11_0_2085, List.forall_mem_cons.2 ⟨subd11_0_2086, List.forall_mem_cons.2 ⟨subd11_0_2087, List.forall_mem_cons.2 ⟨subd11_0_2088, List.forall_mem_cons.2 ⟨subd11_0_2089, List.forall_mem_cons.2 ⟨subd11_0_2090, List.forall_mem_cons.2 ⟨subd11_0_2091, List.forall_mem_cons.2 ⟨subd11_0_2092, List.forall_mem_cons.2 ⟨subd11_0_2093, List.forall_mem_cons.2 ⟨subd11_0_2094, List.forall_mem_cons.2 ⟨subd11_0_2095, List.forall_mem_cons.2 ⟨subd11_0_2096, List.forall_mem_cons.2 ⟨subd11_0_2097, List.forall_mem_cons.2 ⟨subd11_0_2098, List.forall_mem_cons.2 ⟨subd11_0_2099, List.forall_mem_cons.2 ⟨subd11_0_2100, List.forall_mem_cons.2 ⟨subd11_0_2101, List.forall_mem_cons.2 ⟨subd11_0_2102, List.forall_mem_cons.2 ⟨subd11_0_2103, List.forall_mem_cons.2 ⟨subd11_0_2104, List.forall_mem_cons.2 ⟨subd11_0_2105, List.forall_mem_cons.2 ⟨subd11_0_2106, List.forall_mem_cons.2 ⟨subd11_0_2107, List.forall_mem_cons.2 ⟨subd11_0_2108, List.forall_mem_cons.2 ⟨subd11_0_2109, List.forall_mem_cons.2 ⟨subd11_0_2110, List.forall_mem_cons.2 ⟨subd11_0_2111, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_2112 : subd11_0 [5, 4, -6] = true := by decide +kernel
theorem subd11_0_2113 : subd11_0 [5, 4, -5] = true := by decide +kernel
theorem subd11_0_2114 : subd11_0 [5, 4, -4] = true := by decide +kernel
theorem subd11_0_2115 : subd11_0 [5, 4, -3] = true := by decide +kernel
theorem subd11_0_2116 : subd11_0 [5, 4, -2] = true := by decide +kernel
theorem subd11_0_2117 : subd11_0 [5, 4, -1] = true := by decide +kernel
theorem subd11_0_2118 : subd11_0 [5, 4, 0] = true := by decide +kernel
theorem subd11_0_2119 : subd11_0 [5, 4, 1] = true := by decide +kernel
theorem subd11_0_2120 : subd11_0 [5, 4, 2] = true := by decide +kernel
theorem subd11_0_2121 : subd11_0 [5, 4, 3] = true := by decide +kernel
theorem subd11_0_2122 : subd11_0 [5, 4, 4] = true := by decide +kernel
theorem subd11_0_2123 : subd11_0 [5, 4, 5] = true := by decide +kernel
theorem subd11_0_2124 : subd11_0 [5, 4, 6] = true := by decide +kernel
theorem subd11_0_2125 : subd11_0 [5, 4, 7] = true := by decide +kernel
theorem subd11_0_2126 : subd11_0 [5, 5, -6] = true := by decide +kernel
theorem subd11_0_2127 : subd11_0 [5, 5, -5] = true := by decide +kernel
theorem subd11_0_2128 : subd11_0 [5, 5, -4] = true := by decide +kernel
theorem subd11_0_2129 : subd11_0 [5, 5, -3] = true := by decide +kernel
theorem subd11_0_2130 : subd11_0 [5, 5, -2] = true := by decide +kernel
theorem subd11_0_2131 : subd11_0 [5, 5, -1] = true := by decide +kernel
theorem subd11_0_2132 : subd11_0 [5, 5, 0] = true := by decide +kernel
theorem subd11_0_2133 : subd11_0 [5, 5, 1] = true := by decide +kernel
theorem subd11_0_2134 : subd11_0 [5, 5, 2] = true := by decide +kernel
theorem subd11_0_2135 : subd11_0 [5, 5, 3] = true := by decide +kernel
theorem subd11_0_2136 : subd11_0 [5, 5, 4] = true := by decide +kernel
theorem subd11_0_2137 : subd11_0 [5, 5, 5] = true := by decide +kernel
theorem subd11_0_2138 : subd11_0 [5, 5, 6] = true := by decide +kernel
theorem subd11_0_2139 : subd11_0 [5, 5, 7] = true := by decide +kernel
theorem subd11_0_2140 : subd11_0 [5, 6, -6] = true := by decide +kernel
theorem subd11_0_2141 : subd11_0 [5, 6, -5] = true := by decide +kernel
theorem subd11_0_2142 : subd11_0 [5, 6, -4] = true := by decide +kernel
theorem subd11_0_2143 : subd11_0 [5, 6, -3] = true := by decide +kernel
theorem sbd11_0_66 : ∀ q ∈ blkd11_0_66, subd11_0 q = true := by
  unfold blkd11_0_66
  exact List.forall_mem_cons.2 ⟨subd11_0_2112, List.forall_mem_cons.2 ⟨subd11_0_2113, List.forall_mem_cons.2 ⟨subd11_0_2114, List.forall_mem_cons.2 ⟨subd11_0_2115, List.forall_mem_cons.2 ⟨subd11_0_2116, List.forall_mem_cons.2 ⟨subd11_0_2117, List.forall_mem_cons.2 ⟨subd11_0_2118, List.forall_mem_cons.2 ⟨subd11_0_2119, List.forall_mem_cons.2 ⟨subd11_0_2120, List.forall_mem_cons.2 ⟨subd11_0_2121, List.forall_mem_cons.2 ⟨subd11_0_2122, List.forall_mem_cons.2 ⟨subd11_0_2123, List.forall_mem_cons.2 ⟨subd11_0_2124, List.forall_mem_cons.2 ⟨subd11_0_2125, List.forall_mem_cons.2 ⟨subd11_0_2126, List.forall_mem_cons.2 ⟨subd11_0_2127, List.forall_mem_cons.2 ⟨subd11_0_2128, List.forall_mem_cons.2 ⟨subd11_0_2129, List.forall_mem_cons.2 ⟨subd11_0_2130, List.forall_mem_cons.2 ⟨subd11_0_2131, List.forall_mem_cons.2 ⟨subd11_0_2132, List.forall_mem_cons.2 ⟨subd11_0_2133, List.forall_mem_cons.2 ⟨subd11_0_2134, List.forall_mem_cons.2 ⟨subd11_0_2135, List.forall_mem_cons.2 ⟨subd11_0_2136, List.forall_mem_cons.2 ⟨subd11_0_2137, List.forall_mem_cons.2 ⟨subd11_0_2138, List.forall_mem_cons.2 ⟨subd11_0_2139, List.forall_mem_cons.2 ⟨subd11_0_2140, List.forall_mem_cons.2 ⟨subd11_0_2141, List.forall_mem_cons.2 ⟨subd11_0_2142, List.forall_mem_cons.2 ⟨subd11_0_2143, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_2144 : subd11_0 [5, 6, -2] = true := by decide +kernel
theorem subd11_0_2145 : subd11_0 [5, 6, -1] = true := by decide +kernel
theorem subd11_0_2146 : subd11_0 [5, 6, 0] = true := by decide +kernel
theorem subd11_0_2147 : subd11_0 [5, 6, 1] = true := by decide +kernel
theorem subd11_0_2148 : subd11_0 [5, 6, 2] = true := by decide +kernel
theorem subd11_0_2149 : subd11_0 [5, 6, 3] = true := by decide +kernel
theorem subd11_0_2150 : subd11_0 [5, 6, 4] = true := by decide +kernel
theorem subd11_0_2151 : subd11_0 [5, 6, 5] = true := by decide +kernel
theorem subd11_0_2152 : subd11_0 [5, 6, 6] = true := by decide +kernel
theorem subd11_0_2153 : subd11_0 [5, 6, 7] = true := by decide +kernel
theorem subd11_0_2154 : subd11_0 [5, 7] = true := by decide +kernel
theorem subd11_0_2155 : subd11_0 [5, 8] = true := by decide +kernel
theorem subd11_0_2156 : subd11_0 [5, 9] = true := by decide +kernel
theorem subd11_0_2157 : subd11_0 [6, -5] = true := by decide +kernel
theorem subd11_0_2158 : subd11_0 [6, -4] = true := by decide +kernel
theorem subd11_0_2159 : subd11_0 [6, -3] = true := by decide +kernel
theorem subd11_0_2160 : subd11_0 [6, -2] = true := by decide +kernel
theorem subd11_0_2161 : subd11_0 [6, -1] = true := by decide +kernel
theorem subd11_0_2162 : subd11_0 [6, 0] = true := by decide +kernel
theorem subd11_0_2163 : subd11_0 [6, 1] = true := by decide +kernel
theorem subd11_0_2164 : subd11_0 [6, 2] = true := by decide +kernel
theorem subd11_0_2165 : subd11_0 [6, 3, -5] = true := by decide +kernel
theorem subd11_0_2166 : subd11_0 [6, 3, -4] = true := by decide +kernel
theorem subd11_0_2167 : subd11_0 [6, 3, -3] = true := by decide +kernel
theorem subd11_0_2168 : subd11_0 [6, 3, -2] = true := by decide +kernel
theorem subd11_0_2169 : subd11_0 [6, 3, -1] = true := by decide +kernel
theorem subd11_0_2170 : subd11_0 [6, 3, 0] = true := by decide +kernel
theorem subd11_0_2171 : subd11_0 [6, 3, 1] = true := by decide +kernel
theorem subd11_0_2172 : subd11_0 [6, 3, 2] = true := by decide +kernel
theorem subd11_0_2173 : subd11_0 [6, 3, 3] = true := by decide +kernel
theorem subd11_0_2174 : subd11_0 [6, 3, 4] = true := by decide +kernel
theorem subd11_0_2175 : subd11_0 [6, 3, 5] = true := by decide +kernel
theorem sbd11_0_67 : ∀ q ∈ blkd11_0_67, subd11_0 q = true := by
  unfold blkd11_0_67
  exact List.forall_mem_cons.2 ⟨subd11_0_2144, List.forall_mem_cons.2 ⟨subd11_0_2145, List.forall_mem_cons.2 ⟨subd11_0_2146, List.forall_mem_cons.2 ⟨subd11_0_2147, List.forall_mem_cons.2 ⟨subd11_0_2148, List.forall_mem_cons.2 ⟨subd11_0_2149, List.forall_mem_cons.2 ⟨subd11_0_2150, List.forall_mem_cons.2 ⟨subd11_0_2151, List.forall_mem_cons.2 ⟨subd11_0_2152, List.forall_mem_cons.2 ⟨subd11_0_2153, List.forall_mem_cons.2 ⟨subd11_0_2154, List.forall_mem_cons.2 ⟨subd11_0_2155, List.forall_mem_cons.2 ⟨subd11_0_2156, List.forall_mem_cons.2 ⟨subd11_0_2157, List.forall_mem_cons.2 ⟨subd11_0_2158, List.forall_mem_cons.2 ⟨subd11_0_2159, List.forall_mem_cons.2 ⟨subd11_0_2160, List.forall_mem_cons.2 ⟨subd11_0_2161, List.forall_mem_cons.2 ⟨subd11_0_2162, List.forall_mem_cons.2 ⟨subd11_0_2163, List.forall_mem_cons.2 ⟨subd11_0_2164, List.forall_mem_cons.2 ⟨subd11_0_2165, List.forall_mem_cons.2 ⟨subd11_0_2166, List.forall_mem_cons.2 ⟨subd11_0_2167, List.forall_mem_cons.2 ⟨subd11_0_2168, List.forall_mem_cons.2 ⟨subd11_0_2169, List.forall_mem_cons.2 ⟨subd11_0_2170, List.forall_mem_cons.2 ⟨subd11_0_2171, List.forall_mem_cons.2 ⟨subd11_0_2172, List.forall_mem_cons.2 ⟨subd11_0_2173, List.forall_mem_cons.2 ⟨subd11_0_2174, List.forall_mem_cons.2 ⟨subd11_0_2175, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_2176 : subd11_0 [6, 3, 6] = true := by decide +kernel
theorem subd11_0_2177 : subd11_0 [6, 3, 7] = true := by decide +kernel
theorem subd11_0_2178 : subd11_0 [6, 4] = true := by decide +kernel
theorem subd11_0_2179 : subd11_0 [6, 5] = true := by decide +kernel
theorem subd11_0_2180 : subd11_0 [6, 6] = true := by decide +kernel
theorem subd11_0_2181 : subd11_0 [6, 7] = true := by decide +kernel
theorem subd11_0_2182 : subd11_0 [6, 8] = true := by decide +kernel
theorem subd11_0_2183 : subd11_0 [6, 9] = true := by decide +kernel
theorem subd11_0_2184 : subd11_0 [7, -3] = true := by decide +kernel
theorem subd11_0_2185 : subd11_0 [7, -2] = true := by decide +kernel
theorem subd11_0_2186 : subd11_0 [7, -1] = true := by decide +kernel
theorem subd11_0_2187 : subd11_0 [7, 0] = true := by decide +kernel
theorem subd11_0_2188 : subd11_0 [7, 1] = true := by decide +kernel
theorem subd11_0_2189 : subd11_0 [7, 2] = true := by decide +kernel
theorem subd11_0_2190 : subd11_0 [7, 3] = true := by decide +kernel
theorem subd11_0_2191 : subd11_0 [7, 4] = true := by decide +kernel
theorem subd11_0_2192 : subd11_0 [7, 5] = true := by decide +kernel
theorem subd11_0_2193 : subd11_0 [7, 6] = true := by decide +kernel
theorem subd11_0_2194 : subd11_0 [7, 7] = true := by decide +kernel
theorem subd11_0_2195 : subd11_0 [7, 8] = true := by decide +kernel
theorem subd11_0_2196 : subd11_0 [8, 0] = true := by decide +kernel
theorem subd11_0_2197 : subd11_0 [8, 1] = true := by decide +kernel
theorem subd11_0_2198 : subd11_0 [8, 2] = true := by decide +kernel
theorem subd11_0_2199 : subd11_0 [8, 3] = true := by decide +kernel
theorem subd11_0_2200 : subd11_0 [8, 4] = true := by decide +kernel
theorem subd11_0_2201 : subd11_0 [8, 5] = true := by decide +kernel
theorem subd11_0_2202 : subd11_0 [8, 6] = true := by decide +kernel
theorem sbd11_0_68 : ∀ q ∈ blkd11_0_68, subd11_0 q = true := by
  unfold blkd11_0_68
  exact List.forall_mem_cons.2 ⟨subd11_0_2176, List.forall_mem_cons.2 ⟨subd11_0_2177, List.forall_mem_cons.2 ⟨subd11_0_2178, List.forall_mem_cons.2 ⟨subd11_0_2179, List.forall_mem_cons.2 ⟨subd11_0_2180, List.forall_mem_cons.2 ⟨subd11_0_2181, List.forall_mem_cons.2 ⟨subd11_0_2182, List.forall_mem_cons.2 ⟨subd11_0_2183, List.forall_mem_cons.2 ⟨subd11_0_2184, List.forall_mem_cons.2 ⟨subd11_0_2185, List.forall_mem_cons.2 ⟨subd11_0_2186, List.forall_mem_cons.2 ⟨subd11_0_2187, List.forall_mem_cons.2 ⟨subd11_0_2188, List.forall_mem_cons.2 ⟨subd11_0_2189, List.forall_mem_cons.2 ⟨subd11_0_2190, List.forall_mem_cons.2 ⟨subd11_0_2191, List.forall_mem_cons.2 ⟨subd11_0_2192, List.forall_mem_cons.2 ⟨subd11_0_2193, List.forall_mem_cons.2 ⟨subd11_0_2194, List.forall_mem_cons.2 ⟨subd11_0_2195, List.forall_mem_cons.2 ⟨subd11_0_2196, List.forall_mem_cons.2 ⟨subd11_0_2197, List.forall_mem_cons.2 ⟨subd11_0_2198, List.forall_mem_cons.2 ⟨subd11_0_2199, List.forall_mem_cons.2 ⟨subd11_0_2200, List.forall_mem_cons.2 ⟨subd11_0_2201, List.forall_mem_cons.2 ⟨subd11_0_2202, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_1 : ldCheck G d11_1.U d11_1.ms ldd11_1 = true := by decide +kernel
theorem pre_okd11_1 : subPre G cell11 d11_1 = true := by decide +kernel
theorem subd11_1_0 : subd11_1 [-4, -2] = true := by decide +kernel
theorem subd11_1_1 : subd11_1 [-4, -1] = true := by decide +kernel
theorem subd11_1_2 : subd11_1 [-4, 0] = true := by decide +kernel
theorem subd11_1_3 : subd11_1 [-4, 1] = true := by decide +kernel
theorem subd11_1_4 : subd11_1 [-4, 2] = true := by decide +kernel
theorem subd11_1_5 : subd11_1 [-3, -3] = true := by decide +kernel
theorem subd11_1_6 : subd11_1 [-3, -2] = true := by decide +kernel
theorem subd11_1_7 : subd11_1 [-3, -1] = true := by decide +kernel
theorem subd11_1_8 : subd11_1 [-3, 0, -7] = true := by decide +kernel
theorem subd11_1_9 : subd11_1 [-3, 0, -6] = true := by decide +kernel
theorem subd11_1_10 : subd11_1 [-3, 0, -5] = true := by decide +kernel
theorem subd11_1_11 : subd11_1 [-3, 0, -4] = true := by decide +kernel
theorem subd11_1_12 : subd11_1 [-3, 0, -3] = true := by decide +kernel
theorem subd11_1_13 : subd11_1 [-3, 0, -2] = true := by decide +kernel
theorem subd11_1_14 : subd11_1 [-3, 0, -1] = true := by decide +kernel
theorem subd11_1_15 : subd11_1 [-3, 0, 0] = true := by decide +kernel
theorem subd11_1_16 : subd11_1 [-3, 0, 1] = true := by decide +kernel
theorem subd11_1_17 : subd11_1 [-3, 0, 2] = true := by decide +kernel
theorem subd11_1_18 : subd11_1 [-3, 0, 3] = true := by decide +kernel
theorem subd11_1_19 : subd11_1 [-3, 0, 4] = true := by decide +kernel
theorem subd11_1_20 : subd11_1 [-3, 0, 5] = true := by decide +kernel
theorem subd11_1_21 : subd11_1 [-3, 0, 6] = true := by decide +kernel
theorem subd11_1_22 : subd11_1 [-3, 0, 7] = true := by decide +kernel
theorem subd11_1_23 : subd11_1 [-3, 1, -6] = true := by decide +kernel
theorem subd11_1_24 : subd11_1 [-3, 1, -5] = true := by decide +kernel
theorem subd11_1_25 : subd11_1 [-3, 1, -4] = true := by decide +kernel
theorem subd11_1_26 : subd11_1 [-3, 1, -3] = true := by decide +kernel
theorem subd11_1_27 : subd11_1 [-3, 1, -2] = true := by decide +kernel
theorem subd11_1_28 : subd11_1 [-3, 1, -1] = true := by decide +kernel
theorem subd11_1_29 : subd11_1 [-3, 1, 0] = true := by decide +kernel
theorem subd11_1_30 : subd11_1 [-3, 1, 1] = true := by decide +kernel
theorem subd11_1_31 : subd11_1 [-3, 1, 2] = true := by decide +kernel
theorem sbd11_1_0 : ∀ q ∈ blkd11_1_0, subd11_1 q = true := by
  unfold blkd11_1_0
  exact List.forall_mem_cons.2 ⟨subd11_1_0, List.forall_mem_cons.2 ⟨subd11_1_1, List.forall_mem_cons.2 ⟨subd11_1_2, List.forall_mem_cons.2 ⟨subd11_1_3, List.forall_mem_cons.2 ⟨subd11_1_4, List.forall_mem_cons.2 ⟨subd11_1_5, List.forall_mem_cons.2 ⟨subd11_1_6, List.forall_mem_cons.2 ⟨subd11_1_7, List.forall_mem_cons.2 ⟨subd11_1_8, List.forall_mem_cons.2 ⟨subd11_1_9, List.forall_mem_cons.2 ⟨subd11_1_10, List.forall_mem_cons.2 ⟨subd11_1_11, List.forall_mem_cons.2 ⟨subd11_1_12, List.forall_mem_cons.2 ⟨subd11_1_13, List.forall_mem_cons.2 ⟨subd11_1_14, List.forall_mem_cons.2 ⟨subd11_1_15, List.forall_mem_cons.2 ⟨subd11_1_16, List.forall_mem_cons.2 ⟨subd11_1_17, List.forall_mem_cons.2 ⟨subd11_1_18, List.forall_mem_cons.2 ⟨subd11_1_19, List.forall_mem_cons.2 ⟨subd11_1_20, List.forall_mem_cons.2 ⟨subd11_1_21, List.forall_mem_cons.2 ⟨subd11_1_22, List.forall_mem_cons.2 ⟨subd11_1_23, List.forall_mem_cons.2 ⟨subd11_1_24, List.forall_mem_cons.2 ⟨subd11_1_25, List.forall_mem_cons.2 ⟨subd11_1_26, List.forall_mem_cons.2 ⟨subd11_1_27, List.forall_mem_cons.2 ⟨subd11_1_28, List.forall_mem_cons.2 ⟨subd11_1_29, List.forall_mem_cons.2 ⟨subd11_1_30, List.forall_mem_cons.2 ⟨subd11_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_32 : subd11_1 [-3, 1, 3] = true := by decide +kernel
theorem subd11_1_33 : subd11_1 [-3, 1, 4] = true := by decide +kernel
theorem subd11_1_34 : subd11_1 [-3, 1, 5] = true := by decide +kernel
theorem subd11_1_35 : subd11_1 [-3, 1, 6] = true := by decide +kernel
theorem subd11_1_36 : subd11_1 [-3, 1, 7] = true := by decide +kernel
theorem subd11_1_37 : subd11_1 [-3, 2, -6] = true := by decide +kernel
theorem subd11_1_38 : subd11_1 [-3, 2, -5] = true := by decide +kernel
theorem subd11_1_39 : subd11_1 [-3, 2, -4] = true := by decide +kernel
theorem subd11_1_40 : subd11_1 [-3, 2, -3] = true := by decide +kernel
theorem subd11_1_41 : subd11_1 [-3, 2, -2] = true := by decide +kernel
theorem subd11_1_42 : subd11_1 [-3, 2, -1] = true := by decide +kernel
theorem subd11_1_43 : subd11_1 [-3, 2, 0] = true := by decide +kernel
theorem subd11_1_44 : subd11_1 [-3, 2, 1] = true := by decide +kernel
theorem subd11_1_45 : subd11_1 [-3, 2, 2] = true := by decide +kernel
theorem subd11_1_46 : subd11_1 [-3, 2, 3] = true := by decide +kernel
theorem subd11_1_47 : subd11_1 [-3, 2, 4] = true := by decide +kernel
theorem subd11_1_48 : subd11_1 [-3, 2, 5] = true := by decide +kernel
theorem subd11_1_49 : subd11_1 [-3, 2, 6] = true := by decide +kernel
theorem subd11_1_50 : subd11_1 [-3, 2, 7] = true := by decide +kernel
theorem subd11_1_51 : subd11_1 [-3, 3] = true := by decide +kernel
theorem subd11_1_52 : subd11_1 [-3, 4] = true := by decide +kernel
theorem subd11_1_53 : subd11_1 [-2, -4] = true := by decide +kernel
theorem subd11_1_54 : subd11_1 [-2, -3] = true := by decide +kernel
theorem subd11_1_55 : subd11_1 [-2, -2, -7] = true := by decide +kernel
theorem subd11_1_56 : subd11_1 [-2, -2, -6] = true := by decide +kernel
theorem subd11_1_57 : subd11_1 [-2, -2, -5] = true := by decide +kernel
theorem subd11_1_58 : subd11_1 [-2, -2, -4] = true := by decide +kernel
theorem subd11_1_59 : subd11_1 [-2, -2, -3] = true := by decide +kernel
theorem subd11_1_60 : subd11_1 [-2, -2, -2] = true := by decide +kernel
theorem subd11_1_61 : subd11_1 [-2, -2, -1] = true := by decide +kernel
theorem subd11_1_62 : subd11_1 [-2, -2, 0] = true := by decide +kernel
theorem subd11_1_63 : subd11_1 [-2, -2, 1] = true := by decide +kernel
theorem sbd11_1_1 : ∀ q ∈ blkd11_1_1, subd11_1 q = true := by
  unfold blkd11_1_1
  exact List.forall_mem_cons.2 ⟨subd11_1_32, List.forall_mem_cons.2 ⟨subd11_1_33, List.forall_mem_cons.2 ⟨subd11_1_34, List.forall_mem_cons.2 ⟨subd11_1_35, List.forall_mem_cons.2 ⟨subd11_1_36, List.forall_mem_cons.2 ⟨subd11_1_37, List.forall_mem_cons.2 ⟨subd11_1_38, List.forall_mem_cons.2 ⟨subd11_1_39, List.forall_mem_cons.2 ⟨subd11_1_40, List.forall_mem_cons.2 ⟨subd11_1_41, List.forall_mem_cons.2 ⟨subd11_1_42, List.forall_mem_cons.2 ⟨subd11_1_43, List.forall_mem_cons.2 ⟨subd11_1_44, List.forall_mem_cons.2 ⟨subd11_1_45, List.forall_mem_cons.2 ⟨subd11_1_46, List.forall_mem_cons.2 ⟨subd11_1_47, List.forall_mem_cons.2 ⟨subd11_1_48, List.forall_mem_cons.2 ⟨subd11_1_49, List.forall_mem_cons.2 ⟨subd11_1_50, List.forall_mem_cons.2 ⟨subd11_1_51, List.forall_mem_cons.2 ⟨subd11_1_52, List.forall_mem_cons.2 ⟨subd11_1_53, List.forall_mem_cons.2 ⟨subd11_1_54, List.forall_mem_cons.2 ⟨subd11_1_55, List.forall_mem_cons.2 ⟨subd11_1_56, List.forall_mem_cons.2 ⟨subd11_1_57, List.forall_mem_cons.2 ⟨subd11_1_58, List.forall_mem_cons.2 ⟨subd11_1_59, List.forall_mem_cons.2 ⟨subd11_1_60, List.forall_mem_cons.2 ⟨subd11_1_61, List.forall_mem_cons.2 ⟨subd11_1_62, List.forall_mem_cons.2 ⟨subd11_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_64 : subd11_1 [-2, -2, 2] = true := by decide +kernel
theorem subd11_1_65 : subd11_1 [-2, -2, 3] = true := by decide +kernel
theorem subd11_1_66 : subd11_1 [-2, -2, 4] = true := by decide +kernel
theorem subd11_1_67 : subd11_1 [-2, -2, 5] = true := by decide +kernel
theorem subd11_1_68 : subd11_1 [-2, -2, 6] = true := by decide +kernel
theorem subd11_1_69 : subd11_1 [-2, -1, -8] = true := by decide +kernel
theorem subd11_1_70 : subd11_1 [-2, -1, -7] = true := by decide +kernel
theorem subd11_1_71 : subd11_1 [-2, -1, -6] = true := by decide +kernel
theorem subd11_1_72 : subd11_1 [-2, -1, -5] = true := by decide +kernel
theorem subd11_1_73 : subd11_1 [-2, -1, -4] = true := by decide +kernel
theorem subd11_1_74 : subd11_1 [-2, -1, -3] = true := by decide +kernel
theorem subd11_1_75 : subd11_1 [-2, -1, -2] = true := by decide +kernel
theorem subd11_1_76 : subd11_1 [-2, -1, -1] = true := by decide +kernel
theorem subd11_1_77 : subd11_1 [-2, -1, 0] = true := by decide +kernel
theorem subd11_1_78 : subd11_1 [-2, -1, 1] = true := by decide +kernel
theorem subd11_1_79 : subd11_1 [-2, -1, 2] = true := by decide +kernel
theorem subd11_1_80 : subd11_1 [-2, -1, 3] = true := by decide +kernel
theorem subd11_1_81 : subd11_1 [-2, -1, 4] = true := by decide +kernel
theorem subd11_1_82 : subd11_1 [-2, -1, 5] = true := by decide +kernel
theorem subd11_1_83 : subd11_1 [-2, -1, 6] = true := by decide +kernel
theorem subd11_1_84 : subd11_1 [-2, -1, 7] = true := by decide +kernel
theorem subd11_1_85 : subd11_1 [-2, 0, -8] = true := by decide +kernel
theorem subd11_1_86 : subd11_1 [-2, 0, -7] = true := by decide +kernel
theorem subd11_1_87 : subd11_1 [-2, 0, -6] = true := by decide +kernel
theorem subd11_1_88 : subd11_1 [-2, 0, -5] = true := by decide +kernel
theorem subd11_1_89 : subd11_1 [-2, 0, -4] = true := by decide +kernel
theorem subd11_1_90 : subd11_1 [-2, 0, -3] = true := by decide +kernel
theorem subd11_1_91 : subd11_1 [-2, 0, -2] = true := by decide +kernel
theorem subd11_1_92 : subd11_1 [-2, 0, -1] = true := by decide +kernel
theorem subd11_1_93 : subd11_1 [-2, 0, 0] = true := by decide +kernel
theorem subd11_1_94 : subd11_1 [-2, 0, 1] = true := by decide +kernel
theorem subd11_1_95 : subd11_1 [-2, 0, 2] = true := by decide +kernel
theorem sbd11_1_2 : ∀ q ∈ blkd11_1_2, subd11_1 q = true := by
  unfold blkd11_1_2
  exact List.forall_mem_cons.2 ⟨subd11_1_64, List.forall_mem_cons.2 ⟨subd11_1_65, List.forall_mem_cons.2 ⟨subd11_1_66, List.forall_mem_cons.2 ⟨subd11_1_67, List.forall_mem_cons.2 ⟨subd11_1_68, List.forall_mem_cons.2 ⟨subd11_1_69, List.forall_mem_cons.2 ⟨subd11_1_70, List.forall_mem_cons.2 ⟨subd11_1_71, List.forall_mem_cons.2 ⟨subd11_1_72, List.forall_mem_cons.2 ⟨subd11_1_73, List.forall_mem_cons.2 ⟨subd11_1_74, List.forall_mem_cons.2 ⟨subd11_1_75, List.forall_mem_cons.2 ⟨subd11_1_76, List.forall_mem_cons.2 ⟨subd11_1_77, List.forall_mem_cons.2 ⟨subd11_1_78, List.forall_mem_cons.2 ⟨subd11_1_79, List.forall_mem_cons.2 ⟨subd11_1_80, List.forall_mem_cons.2 ⟨subd11_1_81, List.forall_mem_cons.2 ⟨subd11_1_82, List.forall_mem_cons.2 ⟨subd11_1_83, List.forall_mem_cons.2 ⟨subd11_1_84, List.forall_mem_cons.2 ⟨subd11_1_85, List.forall_mem_cons.2 ⟨subd11_1_86, List.forall_mem_cons.2 ⟨subd11_1_87, List.forall_mem_cons.2 ⟨subd11_1_88, List.forall_mem_cons.2 ⟨subd11_1_89, List.forall_mem_cons.2 ⟨subd11_1_90, List.forall_mem_cons.2 ⟨subd11_1_91, List.forall_mem_cons.2 ⟨subd11_1_92, List.forall_mem_cons.2 ⟨subd11_1_93, List.forall_mem_cons.2 ⟨subd11_1_94, List.forall_mem_cons.2 ⟨subd11_1_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C131
