import ReflectZphi.Data.Cert5.C079.Base

namespace ReflectZphi.Data.Cert5.C079
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub6_2112 : sub6 [4, -4, 0] = true := by decide +kernel
theorem sub6_2113 : sub6 [4, -4, 1] = true := by decide +kernel
theorem sub6_2114 : sub6 [4, -4, 2] = true := by decide +kernel
theorem sub6_2115 : sub6 [4, -4, 3] = true := by decide +kernel
theorem sub6_2116 : sub6 [4, -4, 4] = true := by decide +kernel
theorem sub6_2117 : sub6 [4, -4, 5] = true := by decide +kernel
theorem sub6_2118 : sub6 [4, -4, 6] = true := by decide +kernel
theorem sub6_2119 : sub6 [4, -4, 7] = true := by decide +kernel
theorem sub6_2120 : sub6 [4, -4, 8] = true := by decide +kernel
theorem sub6_2121 : sub6 [4, -4, 9] = true := by decide +kernel
theorem sub6_2122 : sub6 [4, -4, 10] = true := by decide +kernel
theorem sub6_2123 : sub6 [4, -3, -7] = true := by decide +kernel
theorem sub6_2124 : sub6 [4, -3, -6] = true := by decide +kernel
theorem sub6_2125 : sub6 [4, -3, -5] = true := by decide +kernel
theorem sub6_2126 : sub6 [4, -3, -4] = true := by decide +kernel
theorem sub6_2127 : sub6 [4, -3, -3] = true := by decide +kernel
theorem sub6_2128 : sub6 [4, -3, -2] = true := by decide +kernel
theorem sub6_2129 : sub6 [4, -3, -1] = true := by decide +kernel
theorem sub6_2130 : sub6 [4, -3, 0] = true := by decide +kernel
theorem sub6_2131 : sub6 [4, -3, 1] = true := by decide +kernel
theorem sub6_2132 : sub6 [4, -3, 2] = true := by decide +kernel
theorem sub6_2133 : sub6 [4, -3, 3] = true := by decide +kernel
theorem sub6_2134 : sub6 [4, -3, 4] = true := by decide +kernel
theorem sub6_2135 : sub6 [4, -3, 5] = true := by decide +kernel
theorem sub6_2136 : sub6 [4, -3, 6] = true := by decide +kernel
theorem sub6_2137 : sub6 [4, -3, 7] = true := by decide +kernel
theorem sub6_2138 : sub6 [4, -3, 8] = true := by decide +kernel
theorem sub6_2139 : sub6 [4, -3, 9] = true := by decide +kernel
theorem sub6_2140 : sub6 [4, -3, 10] = true := by decide +kernel
theorem sub6_2141 : sub6 [4, -2, -8] = true := by decide +kernel
theorem sub6_2142 : sub6 [4, -2, -7] = true := by decide +kernel
theorem sub6_2143 : sub6 [4, -2, -6] = true := by decide +kernel
theorem sb6_66 : ∀ q ∈ blk6_66, sub6 q = true := by
  unfold blk6_66
  exact List.forall_mem_cons.2 ⟨sub6_2112, List.forall_mem_cons.2 ⟨sub6_2113, List.forall_mem_cons.2 ⟨sub6_2114, List.forall_mem_cons.2 ⟨sub6_2115, List.forall_mem_cons.2 ⟨sub6_2116, List.forall_mem_cons.2 ⟨sub6_2117, List.forall_mem_cons.2 ⟨sub6_2118, List.forall_mem_cons.2 ⟨sub6_2119, List.forall_mem_cons.2 ⟨sub6_2120, List.forall_mem_cons.2 ⟨sub6_2121, List.forall_mem_cons.2 ⟨sub6_2122, List.forall_mem_cons.2 ⟨sub6_2123, List.forall_mem_cons.2 ⟨sub6_2124, List.forall_mem_cons.2 ⟨sub6_2125, List.forall_mem_cons.2 ⟨sub6_2126, List.forall_mem_cons.2 ⟨sub6_2127, List.forall_mem_cons.2 ⟨sub6_2128, List.forall_mem_cons.2 ⟨sub6_2129, List.forall_mem_cons.2 ⟨sub6_2130, List.forall_mem_cons.2 ⟨sub6_2131, List.forall_mem_cons.2 ⟨sub6_2132, List.forall_mem_cons.2 ⟨sub6_2133, List.forall_mem_cons.2 ⟨sub6_2134, List.forall_mem_cons.2 ⟨sub6_2135, List.forall_mem_cons.2 ⟨sub6_2136, List.forall_mem_cons.2 ⟨sub6_2137, List.forall_mem_cons.2 ⟨sub6_2138, List.forall_mem_cons.2 ⟨sub6_2139, List.forall_mem_cons.2 ⟨sub6_2140, List.forall_mem_cons.2 ⟨sub6_2141, List.forall_mem_cons.2 ⟨sub6_2142, List.forall_mem_cons.2 ⟨sub6_2143, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_2144 : sub6 [4, -2, -5] = true := by decide +kernel
theorem sub6_2145 : sub6 [4, -2, -4] = true := by decide +kernel
theorem sub6_2146 : sub6 [4, -2, -3] = true := by decide +kernel
theorem sub6_2147 : sub6 [4, -2, -2] = true := by decide +kernel
theorem sub6_2148 : sub6 [4, -2, -1] = true := by decide +kernel
theorem sub6_2149 : sub6 [4, -2, 0] = true := by decide +kernel
theorem sub6_2150 : sub6 [4, -2, 1] = true := by decide +kernel
theorem sub6_2151 : sub6 [4, -2, 2] = true := by decide +kernel
theorem sub6_2152 : sub6 [4, -2, 3] = true := by decide +kernel
theorem sub6_2153 : sub6 [4, -2, 4] = true := by decide +kernel
theorem sub6_2154 : sub6 [4, -2, 5] = true := by decide +kernel
theorem sub6_2155 : sub6 [4, -2, 6] = true := by decide +kernel
theorem sub6_2156 : sub6 [4, -2, 7] = true := by decide +kernel
theorem sub6_2157 : sub6 [4, -2, 8] = true := by decide +kernel
theorem sub6_2158 : sub6 [4, -2, 9] = true := by decide +kernel
theorem sub6_2159 : sub6 [4, -2, 10] = true := by decide +kernel
theorem sub6_2160 : sub6 [4, -1, -8] = true := by decide +kernel
theorem sub6_2161 : sub6 [4, -1, -7] = true := by decide +kernel
theorem sub6_2162 : sub6 [4, -1, -6] = true := by decide +kernel
theorem sub6_2163 : sub6 [4, -1, -5] = true := by decide +kernel
theorem sub6_2164 : sub6 [4, -1, -4] = true := by decide +kernel
theorem sub6_2165 : sub6 [4, -1, -3] = true := by decide +kernel
theorem sub6_2166 : sub6 [4, -1, -2] = true := by decide +kernel
theorem sub6_2167 : sub6 [4, -1, -1] = true := by decide +kernel
theorem sub6_2168 : sub6 [4, -1, 0] = true := by decide +kernel
theorem sub6_2169 : sub6 [4, -1, 1] = true := by decide +kernel
theorem sub6_2170 : sub6 [4, -1, 2] = true := by decide +kernel
theorem sub6_2171 : sub6 [4, -1, 3] = true := by decide +kernel
theorem sub6_2172 : sub6 [4, -1, 4] = true := by decide +kernel
theorem sub6_2173 : sub6 [4, -1, 5] = true := by decide +kernel
theorem sub6_2174 : sub6 [4, -1, 6] = true := by decide +kernel
theorem sub6_2175 : sub6 [4, -1, 7] = true := by decide +kernel
theorem sb6_67 : ∀ q ∈ blk6_67, sub6 q = true := by
  unfold blk6_67
  exact List.forall_mem_cons.2 ⟨sub6_2144, List.forall_mem_cons.2 ⟨sub6_2145, List.forall_mem_cons.2 ⟨sub6_2146, List.forall_mem_cons.2 ⟨sub6_2147, List.forall_mem_cons.2 ⟨sub6_2148, List.forall_mem_cons.2 ⟨sub6_2149, List.forall_mem_cons.2 ⟨sub6_2150, List.forall_mem_cons.2 ⟨sub6_2151, List.forall_mem_cons.2 ⟨sub6_2152, List.forall_mem_cons.2 ⟨sub6_2153, List.forall_mem_cons.2 ⟨sub6_2154, List.forall_mem_cons.2 ⟨sub6_2155, List.forall_mem_cons.2 ⟨sub6_2156, List.forall_mem_cons.2 ⟨sub6_2157, List.forall_mem_cons.2 ⟨sub6_2158, List.forall_mem_cons.2 ⟨sub6_2159, List.forall_mem_cons.2 ⟨sub6_2160, List.forall_mem_cons.2 ⟨sub6_2161, List.forall_mem_cons.2 ⟨sub6_2162, List.forall_mem_cons.2 ⟨sub6_2163, List.forall_mem_cons.2 ⟨sub6_2164, List.forall_mem_cons.2 ⟨sub6_2165, List.forall_mem_cons.2 ⟨sub6_2166, List.forall_mem_cons.2 ⟨sub6_2167, List.forall_mem_cons.2 ⟨sub6_2168, List.forall_mem_cons.2 ⟨sub6_2169, List.forall_mem_cons.2 ⟨sub6_2170, List.forall_mem_cons.2 ⟨sub6_2171, List.forall_mem_cons.2 ⟨sub6_2172, List.forall_mem_cons.2 ⟨sub6_2173, List.forall_mem_cons.2 ⟨sub6_2174, List.forall_mem_cons.2 ⟨sub6_2175, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_2176 : sub6 [4, -1, 8] = true := by decide +kernel
theorem sub6_2177 : sub6 [4, -1, 9] = true := by decide +kernel
theorem sub6_2178 : sub6 [4, 0, -8] = true := by decide +kernel
theorem sub6_2179 : sub6 [4, 0, -7] = true := by decide +kernel
theorem sub6_2180 : sub6 [4, 0, -6] = true := by decide +kernel
theorem sub6_2181 : sub6 [4, 0, -5] = true := by decide +kernel
theorem sub6_2182 : sub6 [4, 0, -4] = true := by decide +kernel
theorem sub6_2183 : sub6 [4, 0, -3] = true := by decide +kernel
theorem sub6_2184 : sub6 [4, 0, -2] = true := by decide +kernel
theorem sub6_2185 : sub6 [4, 0, -1] = true := by decide +kernel
theorem sub6_2186 : sub6 [4, 0, 0] = true := by decide +kernel
theorem sub6_2187 : sub6 [4, 0, 1] = true := by decide +kernel
theorem sub6_2188 : sub6 [4, 0, 2] = true := by decide +kernel
theorem sub6_2189 : sub6 [4, 0, 3] = true := by decide +kernel
theorem sub6_2190 : sub6 [4, 0, 4] = true := by decide +kernel
theorem sub6_2191 : sub6 [4, 0, 5] = true := by decide +kernel
theorem sub6_2192 : sub6 [4, 0, 6] = true := by decide +kernel
theorem sub6_2193 : sub6 [4, 0, 7] = true := by decide +kernel
theorem sub6_2194 : sub6 [4, 0, 8] = true := by decide +kernel
theorem sub6_2195 : sub6 [4, 0, 9] = true := by decide +kernel
theorem sub6_2196 : sub6 [4, 1, -8] = true := by decide +kernel
theorem sub6_2197 : sub6 [4, 1, -7] = true := by decide +kernel
theorem sub6_2198 : sub6 [4, 1, -6] = true := by decide +kernel
theorem sub6_2199 : sub6 [4, 1, -5] = true := by decide +kernel
theorem sub6_2200 : sub6 [4, 1, -4] = true := by decide +kernel
theorem sub6_2201 : sub6 [4, 1, -3] = true := by decide +kernel
theorem sub6_2202 : sub6 [4, 1, -2] = true := by decide +kernel
theorem sub6_2203 : sub6 [4, 1, -1] = true := by decide +kernel
theorem sub6_2204 : sub6 [4, 1, 0] = true := by decide +kernel
theorem sub6_2205 : sub6 [4, 1, 1] = true := by decide +kernel
theorem sub6_2206 : sub6 [4, 1, 2] = true := by decide +kernel
theorem sub6_2207 : sub6 [4, 1, 3] = true := by decide +kernel
theorem sb6_68 : ∀ q ∈ blk6_68, sub6 q = true := by
  unfold blk6_68
  exact List.forall_mem_cons.2 ⟨sub6_2176, List.forall_mem_cons.2 ⟨sub6_2177, List.forall_mem_cons.2 ⟨sub6_2178, List.forall_mem_cons.2 ⟨sub6_2179, List.forall_mem_cons.2 ⟨sub6_2180, List.forall_mem_cons.2 ⟨sub6_2181, List.forall_mem_cons.2 ⟨sub6_2182, List.forall_mem_cons.2 ⟨sub6_2183, List.forall_mem_cons.2 ⟨sub6_2184, List.forall_mem_cons.2 ⟨sub6_2185, List.forall_mem_cons.2 ⟨sub6_2186, List.forall_mem_cons.2 ⟨sub6_2187, List.forall_mem_cons.2 ⟨sub6_2188, List.forall_mem_cons.2 ⟨sub6_2189, List.forall_mem_cons.2 ⟨sub6_2190, List.forall_mem_cons.2 ⟨sub6_2191, List.forall_mem_cons.2 ⟨sub6_2192, List.forall_mem_cons.2 ⟨sub6_2193, List.forall_mem_cons.2 ⟨sub6_2194, List.forall_mem_cons.2 ⟨sub6_2195, List.forall_mem_cons.2 ⟨sub6_2196, List.forall_mem_cons.2 ⟨sub6_2197, List.forall_mem_cons.2 ⟨sub6_2198, List.forall_mem_cons.2 ⟨sub6_2199, List.forall_mem_cons.2 ⟨sub6_2200, List.forall_mem_cons.2 ⟨sub6_2201, List.forall_mem_cons.2 ⟨sub6_2202, List.forall_mem_cons.2 ⟨sub6_2203, List.forall_mem_cons.2 ⟨sub6_2204, List.forall_mem_cons.2 ⟨sub6_2205, List.forall_mem_cons.2 ⟨sub6_2206, List.forall_mem_cons.2 ⟨sub6_2207, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_2208 : sub6 [4, 1, 4] = true := by decide +kernel
theorem sub6_2209 : sub6 [4, 1, 5] = true := by decide +kernel
theorem sub6_2210 : sub6 [4, 1, 6] = true := by decide +kernel
theorem sub6_2211 : sub6 [4, 1, 7] = true := by decide +kernel
theorem sub6_2212 : sub6 [4, 1, 8] = true := by decide +kernel
theorem sub6_2213 : sub6 [4, 2, -8] = true := by decide +kernel
theorem sub6_2214 : sub6 [4, 2, -7] = true := by decide +kernel
theorem sub6_2215 : sub6 [4, 2, -6] = true := by decide +kernel
theorem sub6_2216 : sub6 [4, 2, -5] = true := by decide +kernel
theorem sub6_2217 : sub6 [4, 2, -4] = true := by decide +kernel
theorem sub6_2218 : sub6 [4, 2, -3] = true := by decide +kernel
theorem sub6_2219 : sub6 [4, 2, -2] = true := by decide +kernel
theorem sub6_2220 : sub6 [4, 2, -1] = true := by decide +kernel
theorem sub6_2221 : sub6 [4, 2, 0] = true := by decide +kernel
theorem sub6_2222 : sub6 [4, 2, 1] = true := by decide +kernel
theorem sub6_2223 : sub6 [4, 2, 2] = true := by decide +kernel
theorem sub6_2224 : sub6 [4, 2, 3] = true := by decide +kernel
theorem sub6_2225 : sub6 [4, 2, 4] = true := by decide +kernel
theorem sub6_2226 : sub6 [4, 2, 5] = true := by decide +kernel
theorem sub6_2227 : sub6 [4, 2, 6] = true := by decide +kernel
theorem sub6_2228 : sub6 [4, 2, 7] = true := by decide +kernel
theorem sub6_2229 : sub6 [4, 3, -7] = true := by decide +kernel
theorem sub6_2230 : sub6 [4, 3, -6] = true := by decide +kernel
theorem sub6_2231 : sub6 [4, 3, -5] = true := by decide +kernel
theorem sub6_2232 : sub6 [4, 3, -4] = true := by decide +kernel
theorem sub6_2233 : sub6 [4, 3, -3] = true := by decide +kernel
theorem sub6_2234 : sub6 [4, 3, -2] = true := by decide +kernel
theorem sub6_2235 : sub6 [4, 3, -1] = true := by decide +kernel
theorem sub6_2236 : sub6 [4, 3, 0] = true := by decide +kernel
theorem sub6_2237 : sub6 [4, 3, 1] = true := by decide +kernel
theorem sub6_2238 : sub6 [4, 3, 2] = true := by decide +kernel
theorem sub6_2239 : sub6 [4, 3, 3] = true := by decide +kernel
theorem sb6_69 : ∀ q ∈ blk6_69, sub6 q = true := by
  unfold blk6_69
  exact List.forall_mem_cons.2 ⟨sub6_2208, List.forall_mem_cons.2 ⟨sub6_2209, List.forall_mem_cons.2 ⟨sub6_2210, List.forall_mem_cons.2 ⟨sub6_2211, List.forall_mem_cons.2 ⟨sub6_2212, List.forall_mem_cons.2 ⟨sub6_2213, List.forall_mem_cons.2 ⟨sub6_2214, List.forall_mem_cons.2 ⟨sub6_2215, List.forall_mem_cons.2 ⟨sub6_2216, List.forall_mem_cons.2 ⟨sub6_2217, List.forall_mem_cons.2 ⟨sub6_2218, List.forall_mem_cons.2 ⟨sub6_2219, List.forall_mem_cons.2 ⟨sub6_2220, List.forall_mem_cons.2 ⟨sub6_2221, List.forall_mem_cons.2 ⟨sub6_2222, List.forall_mem_cons.2 ⟨sub6_2223, List.forall_mem_cons.2 ⟨sub6_2224, List.forall_mem_cons.2 ⟨sub6_2225, List.forall_mem_cons.2 ⟨sub6_2226, List.forall_mem_cons.2 ⟨sub6_2227, List.forall_mem_cons.2 ⟨sub6_2228, List.forall_mem_cons.2 ⟨sub6_2229, List.forall_mem_cons.2 ⟨sub6_2230, List.forall_mem_cons.2 ⟨sub6_2231, List.forall_mem_cons.2 ⟨sub6_2232, List.forall_mem_cons.2 ⟨sub6_2233, List.forall_mem_cons.2 ⟨sub6_2234, List.forall_mem_cons.2 ⟨sub6_2235, List.forall_mem_cons.2 ⟨sub6_2236, List.forall_mem_cons.2 ⟨sub6_2237, List.forall_mem_cons.2 ⟨sub6_2238, List.forall_mem_cons.2 ⟨sub6_2239, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_2240 : sub6 [4, 3, 4] = true := by decide +kernel
theorem sub6_2241 : sub6 [4, 3, 5] = true := by decide +kernel
theorem sub6_2242 : sub6 [4, 4] = true := by decide +kernel
theorem sub6_2243 : sub6 [4, 5] = true := by decide +kernel
theorem sub6_2244 : sub6 [5, -9] = true := by decide +kernel
theorem sub6_2245 : sub6 [5, -8] = true := by decide +kernel
theorem sub6_2246 : sub6 [5, -7] = true := by decide +kernel
theorem sub6_2247 : sub6 [5, -6, -3] = true := by decide +kernel
theorem sub6_2248 : sub6 [5, -6, -2] = true := by decide +kernel
theorem sub6_2249 : sub6 [5, -6, -1] = true := by decide +kernel
theorem sub6_2250 : sub6 [5, -6, 0] = true := by decide +kernel
theorem sub6_2251 : sub6 [5, -6, 1] = true := by decide +kernel
theorem sub6_2252 : sub6 [5, -6, 2] = true := by decide +kernel
theorem sub6_2253 : sub6 [5, -6, 3] = true := by decide +kernel
theorem sub6_2254 : sub6 [5, -6, 4] = true := by decide +kernel
theorem sub6_2255 : sub6 [5, -6, 5] = true := by decide +kernel
theorem sub6_2256 : sub6 [5, -6, 6] = true := by decide +kernel
theorem sub6_2257 : sub6 [5, -6, 7] = true := by decide +kernel
theorem sub6_2258 : sub6 [5, -6, 8] = true := by decide +kernel
theorem sub6_2259 : sub6 [5, -6, 9] = true := by decide +kernel
theorem sub6_2260 : sub6 [5, -5, -5] = true := by decide +kernel
theorem sub6_2261 : sub6 [5, -5, -4] = true := by decide +kernel
theorem sub6_2262 : sub6 [5, -5, -3] = true := by decide +kernel
theorem sub6_2263 : sub6 [5, -5, -2] = true := by decide +kernel
theorem sub6_2264 : sub6 [5, -5, -1] = true := by decide +kernel
theorem sub6_2265 : sub6 [5, -5, 0] = true := by decide +kernel
theorem sub6_2266 : sub6 [5, -5, 1] = true := by decide +kernel
theorem sub6_2267 : sub6 [5, -5, 2] = true := by decide +kernel
theorem sub6_2268 : sub6 [5, -5, 3] = true := by decide +kernel
theorem sub6_2269 : sub6 [5, -5, 4] = true := by decide +kernel
theorem sub6_2270 : sub6 [5, -5, 5] = true := by decide +kernel
theorem sub6_2271 : sub6 [5, -5, 6] = true := by decide +kernel
theorem sb6_70 : ∀ q ∈ blk6_70, sub6 q = true := by
  unfold blk6_70
  exact List.forall_mem_cons.2 ⟨sub6_2240, List.forall_mem_cons.2 ⟨sub6_2241, List.forall_mem_cons.2 ⟨sub6_2242, List.forall_mem_cons.2 ⟨sub6_2243, List.forall_mem_cons.2 ⟨sub6_2244, List.forall_mem_cons.2 ⟨sub6_2245, List.forall_mem_cons.2 ⟨sub6_2246, List.forall_mem_cons.2 ⟨sub6_2247, List.forall_mem_cons.2 ⟨sub6_2248, List.forall_mem_cons.2 ⟨sub6_2249, List.forall_mem_cons.2 ⟨sub6_2250, List.forall_mem_cons.2 ⟨sub6_2251, List.forall_mem_cons.2 ⟨sub6_2252, List.forall_mem_cons.2 ⟨sub6_2253, List.forall_mem_cons.2 ⟨sub6_2254, List.forall_mem_cons.2 ⟨sub6_2255, List.forall_mem_cons.2 ⟨sub6_2256, List.forall_mem_cons.2 ⟨sub6_2257, List.forall_mem_cons.2 ⟨sub6_2258, List.forall_mem_cons.2 ⟨sub6_2259, List.forall_mem_cons.2 ⟨sub6_2260, List.forall_mem_cons.2 ⟨sub6_2261, List.forall_mem_cons.2 ⟨sub6_2262, List.forall_mem_cons.2 ⟨sub6_2263, List.forall_mem_cons.2 ⟨sub6_2264, List.forall_mem_cons.2 ⟨sub6_2265, List.forall_mem_cons.2 ⟨sub6_2266, List.forall_mem_cons.2 ⟨sub6_2267, List.forall_mem_cons.2 ⟨sub6_2268, List.forall_mem_cons.2 ⟨sub6_2269, List.forall_mem_cons.2 ⟨sub6_2270, List.forall_mem_cons.2 ⟨sub6_2271, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_2272 : sub6 [5, -5, 7] = true := by decide +kernel
theorem sub6_2273 : sub6 [5, -5, 8] = true := by decide +kernel
theorem sub6_2274 : sub6 [5, -5, 9] = true := by decide +kernel
theorem sub6_2275 : sub6 [5, -5, 10] = true := by decide +kernel
theorem sub6_2276 : sub6 [5, -4, -5] = true := by decide +kernel
theorem sub6_2277 : sub6 [5, -4, -4] = true := by decide +kernel
theorem sub6_2278 : sub6 [5, -4, -3] = true := by decide +kernel
theorem sub6_2279 : sub6 [5, -4, -2] = true := by decide +kernel
theorem sub6_2280 : sub6 [5, -4, -1] = true := by decide +kernel
theorem sub6_2281 : sub6 [5, -4, 0] = true := by decide +kernel
theorem sub6_2282 : sub6 [5, -4, 1] = true := by decide +kernel
theorem sub6_2283 : sub6 [5, -4, 2] = true := by decide +kernel
theorem sub6_2284 : sub6 [5, -4, 3] = true := by decide +kernel
theorem sub6_2285 : sub6 [5, -4, 4] = true := by decide +kernel
theorem sub6_2286 : sub6 [5, -4, 5] = true := by decide +kernel
theorem sub6_2287 : sub6 [5, -4, 6] = true := by decide +kernel
theorem sub6_2288 : sub6 [5, -4, 7] = true := by decide +kernel
theorem sub6_2289 : sub6 [5, -4, 8] = true := by decide +kernel
theorem sub6_2290 : sub6 [5, -4, 9] = true := by decide +kernel
theorem sub6_2291 : sub6 [5, -4, 10] = true := by decide +kernel
theorem sub6_2292 : sub6 [5, -3, -6] = true := by decide +kernel
theorem sub6_2293 : sub6 [5, -3, -5] = true := by decide +kernel
theorem sub6_2294 : sub6 [5, -3, -4] = true := by decide +kernel
theorem sub6_2295 : sub6 [5, -3, -3] = true := by decide +kernel
theorem sub6_2296 : sub6 [5, -3, -2] = true := by decide +kernel
theorem sub6_2297 : sub6 [5, -3, -1] = true := by decide +kernel
theorem sub6_2298 : sub6 [5, -3, 0] = true := by decide +kernel
theorem sub6_2299 : sub6 [5, -3, 1] = true := by decide +kernel
theorem sub6_2300 : sub6 [5, -3, 2] = true := by decide +kernel
theorem sub6_2301 : sub6 [5, -3, 3] = true := by decide +kernel
theorem sub6_2302 : sub6 [5, -3, 4] = true := by decide +kernel
theorem sub6_2303 : sub6 [5, -3, 5] = true := by decide +kernel
theorem sb6_71 : ∀ q ∈ blk6_71, sub6 q = true := by
  unfold blk6_71
  exact List.forall_mem_cons.2 ⟨sub6_2272, List.forall_mem_cons.2 ⟨sub6_2273, List.forall_mem_cons.2 ⟨sub6_2274, List.forall_mem_cons.2 ⟨sub6_2275, List.forall_mem_cons.2 ⟨sub6_2276, List.forall_mem_cons.2 ⟨sub6_2277, List.forall_mem_cons.2 ⟨sub6_2278, List.forall_mem_cons.2 ⟨sub6_2279, List.forall_mem_cons.2 ⟨sub6_2280, List.forall_mem_cons.2 ⟨sub6_2281, List.forall_mem_cons.2 ⟨sub6_2282, List.forall_mem_cons.2 ⟨sub6_2283, List.forall_mem_cons.2 ⟨sub6_2284, List.forall_mem_cons.2 ⟨sub6_2285, List.forall_mem_cons.2 ⟨sub6_2286, List.forall_mem_cons.2 ⟨sub6_2287, List.forall_mem_cons.2 ⟨sub6_2288, List.forall_mem_cons.2 ⟨sub6_2289, List.forall_mem_cons.2 ⟨sub6_2290, List.forall_mem_cons.2 ⟨sub6_2291, List.forall_mem_cons.2 ⟨sub6_2292, List.forall_mem_cons.2 ⟨sub6_2293, List.forall_mem_cons.2 ⟨sub6_2294, List.forall_mem_cons.2 ⟨sub6_2295, List.forall_mem_cons.2 ⟨sub6_2296, List.forall_mem_cons.2 ⟨sub6_2297, List.forall_mem_cons.2 ⟨sub6_2298, List.forall_mem_cons.2 ⟨sub6_2299, List.forall_mem_cons.2 ⟨sub6_2300, List.forall_mem_cons.2 ⟨sub6_2301, List.forall_mem_cons.2 ⟨sub6_2302, List.forall_mem_cons.2 ⟨sub6_2303, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_2304 : sub6 [5, -3, 6] = true := by decide +kernel
theorem sub6_2305 : sub6 [5, -3, 7] = true := by decide +kernel
theorem sub6_2306 : sub6 [5, -3, 8] = true := by decide +kernel
theorem sub6_2307 : sub6 [5, -3, 9] = true := by decide +kernel
theorem sub6_2308 : sub6 [5, -2, -7] = true := by decide +kernel
theorem sub6_2309 : sub6 [5, -2, -6] = true := by decide +kernel
theorem sub6_2310 : sub6 [5, -2, -5] = true := by decide +kernel
theorem sub6_2311 : sub6 [5, -2, -4] = true := by decide +kernel
theorem sub6_2312 : sub6 [5, -2, -3] = true := by decide +kernel
theorem sub6_2313 : sub6 [5, -2, -2] = true := by decide +kernel
theorem sub6_2314 : sub6 [5, -2, -1] = true := by decide +kernel
theorem sub6_2315 : sub6 [5, -2, 0] = true := by decide +kernel
theorem sub6_2316 : sub6 [5, -2, 1] = true := by decide +kernel
theorem sub6_2317 : sub6 [5, -2, 2] = true := by decide +kernel
theorem sub6_2318 : sub6 [5, -2, 3] = true := by decide +kernel
theorem sub6_2319 : sub6 [5, -2, 4] = true := by decide +kernel
theorem sub6_2320 : sub6 [5, -2, 5] = true := by decide +kernel
theorem sub6_2321 : sub6 [5, -2, 6] = true := by decide +kernel
theorem sub6_2322 : sub6 [5, -2, 7] = true := by decide +kernel
theorem sub6_2323 : sub6 [5, -2, 8] = true := by decide +kernel
theorem sub6_2324 : sub6 [5, -2, 9] = true := by decide +kernel
theorem sub6_2325 : sub6 [5, -1, -7] = true := by decide +kernel
theorem sub6_2326 : sub6 [5, -1, -6] = true := by decide +kernel
theorem sub6_2327 : sub6 [5, -1, -5] = true := by decide +kernel
theorem sub6_2328 : sub6 [5, -1, -4] = true := by decide +kernel
theorem sub6_2329 : sub6 [5, -1, -3] = true := by decide +kernel
theorem sub6_2330 : sub6 [5, -1, -2] = true := by decide +kernel
theorem sub6_2331 : sub6 [5, -1, -1] = true := by decide +kernel
theorem sub6_2332 : sub6 [5, -1, 0] = true := by decide +kernel
theorem sub6_2333 : sub6 [5, -1, 1] = true := by decide +kernel
theorem sub6_2334 : sub6 [5, -1, 2] = true := by decide +kernel
theorem sub6_2335 : sub6 [5, -1, 3] = true := by decide +kernel
theorem sb6_72 : ∀ q ∈ blk6_72, sub6 q = true := by
  unfold blk6_72
  exact List.forall_mem_cons.2 ⟨sub6_2304, List.forall_mem_cons.2 ⟨sub6_2305, List.forall_mem_cons.2 ⟨sub6_2306, List.forall_mem_cons.2 ⟨sub6_2307, List.forall_mem_cons.2 ⟨sub6_2308, List.forall_mem_cons.2 ⟨sub6_2309, List.forall_mem_cons.2 ⟨sub6_2310, List.forall_mem_cons.2 ⟨sub6_2311, List.forall_mem_cons.2 ⟨sub6_2312, List.forall_mem_cons.2 ⟨sub6_2313, List.forall_mem_cons.2 ⟨sub6_2314, List.forall_mem_cons.2 ⟨sub6_2315, List.forall_mem_cons.2 ⟨sub6_2316, List.forall_mem_cons.2 ⟨sub6_2317, List.forall_mem_cons.2 ⟨sub6_2318, List.forall_mem_cons.2 ⟨sub6_2319, List.forall_mem_cons.2 ⟨sub6_2320, List.forall_mem_cons.2 ⟨sub6_2321, List.forall_mem_cons.2 ⟨sub6_2322, List.forall_mem_cons.2 ⟨sub6_2323, List.forall_mem_cons.2 ⟨sub6_2324, List.forall_mem_cons.2 ⟨sub6_2325, List.forall_mem_cons.2 ⟨sub6_2326, List.forall_mem_cons.2 ⟨sub6_2327, List.forall_mem_cons.2 ⟨sub6_2328, List.forall_mem_cons.2 ⟨sub6_2329, List.forall_mem_cons.2 ⟨sub6_2330, List.forall_mem_cons.2 ⟨sub6_2331, List.forall_mem_cons.2 ⟨sub6_2332, List.forall_mem_cons.2 ⟨sub6_2333, List.forall_mem_cons.2 ⟨sub6_2334, List.forall_mem_cons.2 ⟨sub6_2335, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_2336 : sub6 [5, -1, 4] = true := by decide +kernel
theorem sub6_2337 : sub6 [5, -1, 5] = true := by decide +kernel
theorem sub6_2338 : sub6 [5, -1, 6] = true := by decide +kernel
theorem sub6_2339 : sub6 [5, -1, 7] = true := by decide +kernel
theorem sub6_2340 : sub6 [5, -1, 8] = true := by decide +kernel
theorem sub6_2341 : sub6 [5, 0, -7] = true := by decide +kernel
theorem sub6_2342 : sub6 [5, 0, -6] = true := by decide +kernel
theorem sub6_2343 : sub6 [5, 0, -5] = true := by decide +kernel
theorem sub6_2344 : sub6 [5, 0, -4] = true := by decide +kernel
theorem sub6_2345 : sub6 [5, 0, -3] = true := by decide +kernel
theorem sub6_2346 : sub6 [5, 0, -2] = true := by decide +kernel
theorem sub6_2347 : sub6 [5, 0, -1] = true := by decide +kernel
theorem sub6_2348 : sub6 [5, 0, 0] = true := by decide +kernel
theorem sub6_2349 : sub6 [5, 0, 1] = true := by decide +kernel
theorem sub6_2350 : sub6 [5, 0, 2] = true := by decide +kernel
theorem sub6_2351 : sub6 [5, 0, 3] = true := by decide +kernel
theorem sub6_2352 : sub6 [5, 0, 4] = true := by decide +kernel
theorem sub6_2353 : sub6 [5, 0, 5] = true := by decide +kernel
theorem sub6_2354 : sub6 [5, 0, 6] = true := by decide +kernel
theorem sub6_2355 : sub6 [5, 0, 7] = true := by decide +kernel
theorem sub6_2356 : sub6 [5, 1, -7] = true := by decide +kernel
theorem sub6_2357 : sub6 [5, 1, -6] = true := by decide +kernel
theorem sub6_2358 : sub6 [5, 1, -5] = true := by decide +kernel
theorem sub6_2359 : sub6 [5, 1, -4] = true := by decide +kernel
theorem sub6_2360 : sub6 [5, 1, -3] = true := by decide +kernel
theorem sub6_2361 : sub6 [5, 1, -2] = true := by decide +kernel
theorem sub6_2362 : sub6 [5, 1, -1] = true := by decide +kernel
theorem sub6_2363 : sub6 [5, 1, 0] = true := by decide +kernel
theorem sub6_2364 : sub6 [5, 1, 1] = true := by decide +kernel
theorem sub6_2365 : sub6 [5, 1, 2] = true := by decide +kernel
theorem sub6_2366 : sub6 [5, 1, 3] = true := by decide +kernel
theorem sub6_2367 : sub6 [5, 1, 4] = true := by decide +kernel
theorem sb6_73 : ∀ q ∈ blk6_73, sub6 q = true := by
  unfold blk6_73
  exact List.forall_mem_cons.2 ⟨sub6_2336, List.forall_mem_cons.2 ⟨sub6_2337, List.forall_mem_cons.2 ⟨sub6_2338, List.forall_mem_cons.2 ⟨sub6_2339, List.forall_mem_cons.2 ⟨sub6_2340, List.forall_mem_cons.2 ⟨sub6_2341, List.forall_mem_cons.2 ⟨sub6_2342, List.forall_mem_cons.2 ⟨sub6_2343, List.forall_mem_cons.2 ⟨sub6_2344, List.forall_mem_cons.2 ⟨sub6_2345, List.forall_mem_cons.2 ⟨sub6_2346, List.forall_mem_cons.2 ⟨sub6_2347, List.forall_mem_cons.2 ⟨sub6_2348, List.forall_mem_cons.2 ⟨sub6_2349, List.forall_mem_cons.2 ⟨sub6_2350, List.forall_mem_cons.2 ⟨sub6_2351, List.forall_mem_cons.2 ⟨sub6_2352, List.forall_mem_cons.2 ⟨sub6_2353, List.forall_mem_cons.2 ⟨sub6_2354, List.forall_mem_cons.2 ⟨sub6_2355, List.forall_mem_cons.2 ⟨sub6_2356, List.forall_mem_cons.2 ⟨sub6_2357, List.forall_mem_cons.2 ⟨sub6_2358, List.forall_mem_cons.2 ⟨sub6_2359, List.forall_mem_cons.2 ⟨sub6_2360, List.forall_mem_cons.2 ⟨sub6_2361, List.forall_mem_cons.2 ⟨sub6_2362, List.forall_mem_cons.2 ⟨sub6_2363, List.forall_mem_cons.2 ⟨sub6_2364, List.forall_mem_cons.2 ⟨sub6_2365, List.forall_mem_cons.2 ⟨sub6_2366, List.forall_mem_cons.2 ⟨sub6_2367, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_2368 : sub6 [5, 1, 5] = true := by decide +kernel
theorem sub6_2369 : sub6 [5, 1, 6] = true := by decide +kernel
theorem sub6_2370 : sub6 [5, 2] = true := by decide +kernel
theorem sub6_2371 : sub6 [5, 3] = true := by decide +kernel
theorem sub6_2372 : sub6 [6, -8] = true := by decide +kernel
theorem sub6_2373 : sub6 [6, -7] = true := by decide +kernel
theorem sub6_2374 : sub6 [6, -6] = true := by decide +kernel
theorem sub6_2375 : sub6 [6, -5] = true := by decide +kernel
theorem sub6_2376 : sub6 [6, -4] = true := by decide +kernel
theorem sub6_2377 : sub6 [6, -3, -4] = true := by decide +kernel
theorem sub6_2378 : sub6 [6, -3, -3] = true := by decide +kernel
theorem sub6_2379 : sub6 [6, -3, -2] = true := by decide +kernel
theorem sub6_2380 : sub6 [6, -3, -1] = true := by decide +kernel
theorem sub6_2381 : sub6 [6, -3, 0] = true := by decide +kernel
theorem sub6_2382 : sub6 [6, -3, 1] = true := by decide +kernel
theorem sub6_2383 : sub6 [6, -3, 2] = true := by decide +kernel
theorem sub6_2384 : sub6 [6, -3, 3] = true := by decide +kernel
theorem sub6_2385 : sub6 [6, -3, 4] = true := by decide +kernel
theorem sub6_2386 : sub6 [6, -3, 5] = true := by decide +kernel
theorem sub6_2387 : sub6 [6, -3, 6] = true := by decide +kernel
theorem sub6_2388 : sub6 [6, -3, 7] = true := by decide +kernel
theorem sub6_2389 : sub6 [6, -3, 8] = true := by decide +kernel
theorem sub6_2390 : sub6 [6, -2] = true := by decide +kernel
theorem sub6_2391 : sub6 [6, -1] = true := by decide +kernel
theorem sub6_2392 : sub6 [6, 0] = true := by decide +kernel
theorem sub6_2393 : sub6 [6, 1] = true := by decide +kernel
theorem sub6_2394 : sub6 [7, -7] = true := by decide +kernel
theorem sub6_2395 : sub6 [7, -6] = true := by decide +kernel
theorem sub6_2396 : sub6 [7, -5] = true := by decide +kernel
theorem sub6_2397 : sub6 [7, -4] = true := by decide +kernel
theorem sub6_2398 : sub6 [7, -3] = true := by decide +kernel
theorem sub6_2399 : sub6 [7, -2] = true := by decide +kernel
theorem sb6_74 : ∀ q ∈ blk6_74, sub6 q = true := by
  unfold blk6_74
  exact List.forall_mem_cons.2 ⟨sub6_2368, List.forall_mem_cons.2 ⟨sub6_2369, List.forall_mem_cons.2 ⟨sub6_2370, List.forall_mem_cons.2 ⟨sub6_2371, List.forall_mem_cons.2 ⟨sub6_2372, List.forall_mem_cons.2 ⟨sub6_2373, List.forall_mem_cons.2 ⟨sub6_2374, List.forall_mem_cons.2 ⟨sub6_2375, List.forall_mem_cons.2 ⟨sub6_2376, List.forall_mem_cons.2 ⟨sub6_2377, List.forall_mem_cons.2 ⟨sub6_2378, List.forall_mem_cons.2 ⟨sub6_2379, List.forall_mem_cons.2 ⟨sub6_2380, List.forall_mem_cons.2 ⟨sub6_2381, List.forall_mem_cons.2 ⟨sub6_2382, List.forall_mem_cons.2 ⟨sub6_2383, List.forall_mem_cons.2 ⟨sub6_2384, List.forall_mem_cons.2 ⟨sub6_2385, List.forall_mem_cons.2 ⟨sub6_2386, List.forall_mem_cons.2 ⟨sub6_2387, List.forall_mem_cons.2 ⟨sub6_2388, List.forall_mem_cons.2 ⟨sub6_2389, List.forall_mem_cons.2 ⟨sub6_2390, List.forall_mem_cons.2 ⟨sub6_2391, List.forall_mem_cons.2 ⟨sub6_2392, List.forall_mem_cons.2 ⟨sub6_2393, List.forall_mem_cons.2 ⟨sub6_2394, List.forall_mem_cons.2 ⟨sub6_2395, List.forall_mem_cons.2 ⟨sub6_2396, List.forall_mem_cons.2 ⟨sub6_2397, List.forall_mem_cons.2 ⟨sub6_2398, List.forall_mem_cons.2 ⟨sub6_2399, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_2400 : sub6 [7, -1] = true := by decide +kernel
theorem sb6_75 : ∀ q ∈ blk6_75, sub6 q = true := by
  unfold blk6_75
  exact List.forall_mem_cons.2 ⟨sub6_2400, List.forall_mem_nil _⟩
theorem sub7_0 : sub7 [-6, -2] = true := by decide +kernel
theorem sub7_1 : sub7 [-6, -1] = true := by decide +kernel
theorem sub7_2 : sub7 [-6, 0] = true := by decide +kernel
theorem sub7_3 : sub7 [-6, 1] = true := by decide +kernel
theorem sub7_4 : sub7 [-6, 2] = true := by decide +kernel
theorem sub7_5 : sub7 [-6, 3] = true := by decide +kernel
theorem sub7_6 : sub7 [-6, 4] = true := by decide +kernel
theorem sub7_7 : sub7 [-5, -4] = true := by decide +kernel
theorem sub7_8 : sub7 [-5, -3] = true := by decide +kernel
theorem sub7_9 : sub7 [-5, -2] = true := by decide +kernel
theorem sub7_10 : sub7 [-5, -1] = true := by decide +kernel
theorem sub7_11 : sub7 [-5, 0] = true := by decide +kernel
theorem sub7_12 : sub7 [-5, 1] = true := by decide +kernel
theorem sub7_13 : sub7 [-5, 2] = true := by decide +kernel
theorem sub7_14 : sub7 [-5, 3] = true := by decide +kernel
theorem sub7_15 : sub7 [-5, 4] = true := by decide +kernel
theorem sub7_16 : sub7 [-5, 5] = true := by decide +kernel
theorem sub7_17 : sub7 [-5, 6] = true := by decide +kernel
theorem sub7_18 : sub7 [-4, -6] = true := by decide +kernel
theorem sub7_19 : sub7 [-4, -5] = true := by decide +kernel
theorem sub7_20 : sub7 [-4, -4] = true := by decide +kernel
theorem sub7_21 : sub7 [-4, -3] = true := by decide +kernel
theorem sub7_22 : sub7 [-4, -2] = true := by decide +kernel
theorem sub7_23 : sub7 [-4, -1] = true := by decide +kernel
theorem sub7_24 : sub7 [-4, 0] = true := by decide +kernel
theorem sub7_25 : sub7 [-4, 1] = true := by decide +kernel
theorem sub7_26 : sub7 [-4, 2] = true := by decide +kernel
theorem sub7_27 : sub7 [-4, 3] = true := by decide +kernel
theorem sub7_28 : sub7 [-4, 4] = true := by decide +kernel
theorem sub7_29 : sub7 [-4, 5] = true := by decide +kernel
theorem sub7_30 : sub7 [-4, 6] = true := by decide +kernel
theorem sub7_31 : sub7 [-4, 7] = true := by decide +kernel
theorem sb7_0 : ∀ q ∈ blk7_0, sub7 q = true := by
  unfold blk7_0
  exact List.forall_mem_cons.2 ⟨sub7_0, List.forall_mem_cons.2 ⟨sub7_1, List.forall_mem_cons.2 ⟨sub7_2, List.forall_mem_cons.2 ⟨sub7_3, List.forall_mem_cons.2 ⟨sub7_4, List.forall_mem_cons.2 ⟨sub7_5, List.forall_mem_cons.2 ⟨sub7_6, List.forall_mem_cons.2 ⟨sub7_7, List.forall_mem_cons.2 ⟨sub7_8, List.forall_mem_cons.2 ⟨sub7_9, List.forall_mem_cons.2 ⟨sub7_10, List.forall_mem_cons.2 ⟨sub7_11, List.forall_mem_cons.2 ⟨sub7_12, List.forall_mem_cons.2 ⟨sub7_13, List.forall_mem_cons.2 ⟨sub7_14, List.forall_mem_cons.2 ⟨sub7_15, List.forall_mem_cons.2 ⟨sub7_16, List.forall_mem_cons.2 ⟨sub7_17, List.forall_mem_cons.2 ⟨sub7_18, List.forall_mem_cons.2 ⟨sub7_19, List.forall_mem_cons.2 ⟨sub7_20, List.forall_mem_cons.2 ⟨sub7_21, List.forall_mem_cons.2 ⟨sub7_22, List.forall_mem_cons.2 ⟨sub7_23, List.forall_mem_cons.2 ⟨sub7_24, List.forall_mem_cons.2 ⟨sub7_25, List.forall_mem_cons.2 ⟨sub7_26, List.forall_mem_cons.2 ⟨sub7_27, List.forall_mem_cons.2 ⟨sub7_28, List.forall_mem_cons.2 ⟨sub7_29, List.forall_mem_cons.2 ⟨sub7_30, List.forall_mem_cons.2 ⟨sub7_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C079
