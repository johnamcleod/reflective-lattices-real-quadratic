import ReflectZphi.Data.Cert5.C083.Base

namespace ReflectZphi.Data.Cert5.C083
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub5_2272 : sub5 [4, 6] = true := by decide +kernel
theorem sub5_2273 : sub5 [4, 7] = true := by decide +kernel
theorem sub5_2274 : sub5 [5, -7] = true := by decide +kernel
theorem sub5_2275 : sub5 [5, -6] = true := by decide +kernel
theorem sub5_2276 : sub5 [5, -5] = true := by decide +kernel
theorem sub5_2277 : sub5 [5, -4] = true := by decide +kernel
theorem sub5_2278 : sub5 [5, -3, -8] = true := by decide +kernel
theorem sub5_2279 : sub5 [5, -3, -7] = true := by decide +kernel
theorem sub5_2280 : sub5 [5, -3, -6] = true := by decide +kernel
theorem sub5_2281 : sub5 [5, -3, -5] = true := by decide +kernel
theorem sub5_2282 : sub5 [5, -3, -4] = true := by decide +kernel
theorem sub5_2283 : sub5 [5, -3, -3] = true := by decide +kernel
theorem sub5_2284 : sub5 [5, -3, -2] = true := by decide +kernel
theorem sub5_2285 : sub5 [5, -3, -1] = true := by decide +kernel
theorem sub5_2286 : sub5 [5, -3, 0] = true := by decide +kernel
theorem sub5_2287 : sub5 [5, -3, 1] = true := by decide +kernel
theorem sub5_2288 : sub5 [5, -3, 2] = true := by decide +kernel
theorem sub5_2289 : sub5 [5, -3, 3] = true := by decide +kernel
theorem sub5_2290 : sub5 [5, -3, 4] = true := by decide +kernel
theorem sub5_2291 : sub5 [5, -3, 5] = true := by decide +kernel
theorem sub5_2292 : sub5 [5, -3, 6] = true := by decide +kernel
theorem sub5_2293 : sub5 [5, -2, -9] = true := by decide +kernel
theorem sub5_2294 : sub5 [5, -2, -8] = true := by decide +kernel
theorem sub5_2295 : sub5 [5, -2, -7] = true := by decide +kernel
theorem sub5_2296 : sub5 [5, -2, -6] = true := by decide +kernel
theorem sub5_2297 : sub5 [5, -2, -5] = true := by decide +kernel
theorem sub5_2298 : sub5 [5, -2, -4] = true := by decide +kernel
theorem sub5_2299 : sub5 [5, -2, -3] = true := by decide +kernel
theorem sub5_2300 : sub5 [5, -2, -2] = true := by decide +kernel
theorem sub5_2301 : sub5 [5, -2, -1] = true := by decide +kernel
theorem sub5_2302 : sub5 [5, -2, 0] = true := by decide +kernel
theorem sub5_2303 : sub5 [5, -2, 1] = true := by decide +kernel
theorem sb5_71 : ∀ q ∈ blk5_71, sub5 q = true := by
  unfold blk5_71
  exact List.forall_mem_cons.2 ⟨sub5_2272, List.forall_mem_cons.2 ⟨sub5_2273, List.forall_mem_cons.2 ⟨sub5_2274, List.forall_mem_cons.2 ⟨sub5_2275, List.forall_mem_cons.2 ⟨sub5_2276, List.forall_mem_cons.2 ⟨sub5_2277, List.forall_mem_cons.2 ⟨sub5_2278, List.forall_mem_cons.2 ⟨sub5_2279, List.forall_mem_cons.2 ⟨sub5_2280, List.forall_mem_cons.2 ⟨sub5_2281, List.forall_mem_cons.2 ⟨sub5_2282, List.forall_mem_cons.2 ⟨sub5_2283, List.forall_mem_cons.2 ⟨sub5_2284, List.forall_mem_cons.2 ⟨sub5_2285, List.forall_mem_cons.2 ⟨sub5_2286, List.forall_mem_cons.2 ⟨sub5_2287, List.forall_mem_cons.2 ⟨sub5_2288, List.forall_mem_cons.2 ⟨sub5_2289, List.forall_mem_cons.2 ⟨sub5_2290, List.forall_mem_cons.2 ⟨sub5_2291, List.forall_mem_cons.2 ⟨sub5_2292, List.forall_mem_cons.2 ⟨sub5_2293, List.forall_mem_cons.2 ⟨sub5_2294, List.forall_mem_cons.2 ⟨sub5_2295, List.forall_mem_cons.2 ⟨sub5_2296, List.forall_mem_cons.2 ⟨sub5_2297, List.forall_mem_cons.2 ⟨sub5_2298, List.forall_mem_cons.2 ⟨sub5_2299, List.forall_mem_cons.2 ⟨sub5_2300, List.forall_mem_cons.2 ⟨sub5_2301, List.forall_mem_cons.2 ⟨sub5_2302, List.forall_mem_cons.2 ⟨sub5_2303, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_2304 : sub5 [5, -2, 2] = true := by decide +kernel
theorem sub5_2305 : sub5 [5, -2, 3] = true := by decide +kernel
theorem sub5_2306 : sub5 [5, -2, 4] = true := by decide +kernel
theorem sub5_2307 : sub5 [5, -2, 5] = true := by decide +kernel
theorem sub5_2308 : sub5 [5, -2, 6] = true := by decide +kernel
theorem sub5_2309 : sub5 [5, -1, -10] = true := by decide +kernel
theorem sub5_2310 : sub5 [5, -1, -9] = true := by decide +kernel
theorem sub5_2311 : sub5 [5, -1, -8] = true := by decide +kernel
theorem sub5_2312 : sub5 [5, -1, -7] = true := by decide +kernel
theorem sub5_2313 : sub5 [5, -1, -6] = true := by decide +kernel
theorem sub5_2314 : sub5 [5, -1, -5] = true := by decide +kernel
theorem sub5_2315 : sub5 [5, -1, -4] = true := by decide +kernel
theorem sub5_2316 : sub5 [5, -1, -3] = true := by decide +kernel
theorem sub5_2317 : sub5 [5, -1, -2] = true := by decide +kernel
theorem sub5_2318 : sub5 [5, -1, -1] = true := by decide +kernel
theorem sub5_2319 : sub5 [5, -1, 0] = true := by decide +kernel
theorem sub5_2320 : sub5 [5, -1, 1] = true := by decide +kernel
theorem sub5_2321 : sub5 [5, -1, 2] = true := by decide +kernel
theorem sub5_2322 : sub5 [5, -1, 3] = true := by decide +kernel
theorem sub5_2323 : sub5 [5, -1, 4] = true := by decide +kernel
theorem sub5_2324 : sub5 [5, -1, 5] = true := by decide +kernel
theorem sub5_2325 : sub5 [5, -1, 6] = true := by decide +kernel
theorem sub5_2326 : sub5 [5, 0, -11] = true := by decide +kernel
theorem sub5_2327 : sub5 [5, 0, -10] = true := by decide +kernel
theorem sub5_2328 : sub5 [5, 0, -9] = true := by decide +kernel
theorem sub5_2329 : sub5 [5, 0, -8] = true := by decide +kernel
theorem sub5_2330 : sub5 [5, 0, -7] = true := by decide +kernel
theorem sub5_2331 : sub5 [5, 0, -6] = true := by decide +kernel
theorem sub5_2332 : sub5 [5, 0, -5] = true := by decide +kernel
theorem sub5_2333 : sub5 [5, 0, -4] = true := by decide +kernel
theorem sub5_2334 : sub5 [5, 0, -3] = true := by decide +kernel
theorem sub5_2335 : sub5 [5, 0, -2] = true := by decide +kernel
theorem sb5_72 : ∀ q ∈ blk5_72, sub5 q = true := by
  unfold blk5_72
  exact List.forall_mem_cons.2 ⟨sub5_2304, List.forall_mem_cons.2 ⟨sub5_2305, List.forall_mem_cons.2 ⟨sub5_2306, List.forall_mem_cons.2 ⟨sub5_2307, List.forall_mem_cons.2 ⟨sub5_2308, List.forall_mem_cons.2 ⟨sub5_2309, List.forall_mem_cons.2 ⟨sub5_2310, List.forall_mem_cons.2 ⟨sub5_2311, List.forall_mem_cons.2 ⟨sub5_2312, List.forall_mem_cons.2 ⟨sub5_2313, List.forall_mem_cons.2 ⟨sub5_2314, List.forall_mem_cons.2 ⟨sub5_2315, List.forall_mem_cons.2 ⟨sub5_2316, List.forall_mem_cons.2 ⟨sub5_2317, List.forall_mem_cons.2 ⟨sub5_2318, List.forall_mem_cons.2 ⟨sub5_2319, List.forall_mem_cons.2 ⟨sub5_2320, List.forall_mem_cons.2 ⟨sub5_2321, List.forall_mem_cons.2 ⟨sub5_2322, List.forall_mem_cons.2 ⟨sub5_2323, List.forall_mem_cons.2 ⟨sub5_2324, List.forall_mem_cons.2 ⟨sub5_2325, List.forall_mem_cons.2 ⟨sub5_2326, List.forall_mem_cons.2 ⟨sub5_2327, List.forall_mem_cons.2 ⟨sub5_2328, List.forall_mem_cons.2 ⟨sub5_2329, List.forall_mem_cons.2 ⟨sub5_2330, List.forall_mem_cons.2 ⟨sub5_2331, List.forall_mem_cons.2 ⟨sub5_2332, List.forall_mem_cons.2 ⟨sub5_2333, List.forall_mem_cons.2 ⟨sub5_2334, List.forall_mem_cons.2 ⟨sub5_2335, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_2336 : sub5 [5, 0, -1] = true := by decide +kernel
theorem sub5_2337 : sub5 [5, 0, 0] = true := by decide +kernel
theorem sub5_2338 : sub5 [5, 0, 1] = true := by decide +kernel
theorem sub5_2339 : sub5 [5, 0, 2] = true := by decide +kernel
theorem sub5_2340 : sub5 [5, 0, 3] = true := by decide +kernel
theorem sub5_2341 : sub5 [5, 0, 4] = true := by decide +kernel
theorem sub5_2342 : sub5 [5, 0, 5] = true := by decide +kernel
theorem sub5_2343 : sub5 [5, 0, 6] = true := by decide +kernel
theorem sub5_2344 : sub5 [5, 1, -11] = true := by decide +kernel
theorem sub5_2345 : sub5 [5, 1, -10] = true := by decide +kernel
theorem sub5_2346 : sub5 [5, 1, -9] = true := by decide +kernel
theorem sub5_2347 : sub5 [5, 1, -8] = true := by decide +kernel
theorem sub5_2348 : sub5 [5, 1, -7] = true := by decide +kernel
theorem sub5_2349 : sub5 [5, 1, -6] = true := by decide +kernel
theorem sub5_2350 : sub5 [5, 1, -5] = true := by decide +kernel
theorem sub5_2351 : sub5 [5, 1, -4] = true := by decide +kernel
theorem sub5_2352 : sub5 [5, 1, -3] = true := by decide +kernel
theorem sub5_2353 : sub5 [5, 1, -2] = true := by decide +kernel
theorem sub5_2354 : sub5 [5, 1, -1] = true := by decide +kernel
theorem sub5_2355 : sub5 [5, 1, 0] = true := by decide +kernel
theorem sub5_2356 : sub5 [5, 1, 1] = true := by decide +kernel
theorem sub5_2357 : sub5 [5, 1, 2] = true := by decide +kernel
theorem sub5_2358 : sub5 [5, 1, 3] = true := by decide +kernel
theorem sub5_2359 : sub5 [5, 1, 4] = true := by decide +kernel
theorem sub5_2360 : sub5 [5, 1, 5] = true := by decide +kernel
theorem sub5_2361 : sub5 [5, 1, 6] = true := by decide +kernel
theorem sub5_2362 : sub5 [5, 2, -11] = true := by decide +kernel
theorem sub5_2363 : sub5 [5, 2, -10] = true := by decide +kernel
theorem sub5_2364 : sub5 [5, 2, -9] = true := by decide +kernel
theorem sub5_2365 : sub5 [5, 2, -8] = true := by decide +kernel
theorem sub5_2366 : sub5 [5, 2, -7] = true := by decide +kernel
theorem sub5_2367 : sub5 [5, 2, -6] = true := by decide +kernel
theorem sb5_73 : ∀ q ∈ blk5_73, sub5 q = true := by
  unfold blk5_73
  exact List.forall_mem_cons.2 ⟨sub5_2336, List.forall_mem_cons.2 ⟨sub5_2337, List.forall_mem_cons.2 ⟨sub5_2338, List.forall_mem_cons.2 ⟨sub5_2339, List.forall_mem_cons.2 ⟨sub5_2340, List.forall_mem_cons.2 ⟨sub5_2341, List.forall_mem_cons.2 ⟨sub5_2342, List.forall_mem_cons.2 ⟨sub5_2343, List.forall_mem_cons.2 ⟨sub5_2344, List.forall_mem_cons.2 ⟨sub5_2345, List.forall_mem_cons.2 ⟨sub5_2346, List.forall_mem_cons.2 ⟨sub5_2347, List.forall_mem_cons.2 ⟨sub5_2348, List.forall_mem_cons.2 ⟨sub5_2349, List.forall_mem_cons.2 ⟨sub5_2350, List.forall_mem_cons.2 ⟨sub5_2351, List.forall_mem_cons.2 ⟨sub5_2352, List.forall_mem_cons.2 ⟨sub5_2353, List.forall_mem_cons.2 ⟨sub5_2354, List.forall_mem_cons.2 ⟨sub5_2355, List.forall_mem_cons.2 ⟨sub5_2356, List.forall_mem_cons.2 ⟨sub5_2357, List.forall_mem_cons.2 ⟨sub5_2358, List.forall_mem_cons.2 ⟨sub5_2359, List.forall_mem_cons.2 ⟨sub5_2360, List.forall_mem_cons.2 ⟨sub5_2361, List.forall_mem_cons.2 ⟨sub5_2362, List.forall_mem_cons.2 ⟨sub5_2363, List.forall_mem_cons.2 ⟨sub5_2364, List.forall_mem_cons.2 ⟨sub5_2365, List.forall_mem_cons.2 ⟨sub5_2366, List.forall_mem_cons.2 ⟨sub5_2367, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_2368 : sub5 [5, 2, -5] = true := by decide +kernel
theorem sub5_2369 : sub5 [5, 2, -4] = true := by decide +kernel
theorem sub5_2370 : sub5 [5, 2, -3] = true := by decide +kernel
theorem sub5_2371 : sub5 [5, 2, -2] = true := by decide +kernel
theorem sub5_2372 : sub5 [5, 2, -1] = true := by decide +kernel
theorem sub5_2373 : sub5 [5, 2, 0] = true := by decide +kernel
theorem sub5_2374 : sub5 [5, 2, 1] = true := by decide +kernel
theorem sub5_2375 : sub5 [5, 2, 2] = true := by decide +kernel
theorem sub5_2376 : sub5 [5, 2, 3] = true := by decide +kernel
theorem sub5_2377 : sub5 [5, 2, 4] = true := by decide +kernel
theorem sub5_2378 : sub5 [5, 2, 5] = true := by decide +kernel
theorem sub5_2379 : sub5 [5, 3, -11] = true := by decide +kernel
theorem sub5_2380 : sub5 [5, 3, -10] = true := by decide +kernel
theorem sub5_2381 : sub5 [5, 3, -9] = true := by decide +kernel
theorem sub5_2382 : sub5 [5, 3, -8] = true := by decide +kernel
theorem sub5_2383 : sub5 [5, 3, -7] = true := by decide +kernel
theorem sub5_2384 : sub5 [5, 3, -6] = true := by decide +kernel
theorem sub5_2385 : sub5 [5, 3, -5] = true := by decide +kernel
theorem sub5_2386 : sub5 [5, 3, -4] = true := by decide +kernel
theorem sub5_2387 : sub5 [5, 3, -3] = true := by decide +kernel
theorem sub5_2388 : sub5 [5, 3, -2] = true := by decide +kernel
theorem sub5_2389 : sub5 [5, 3, -1] = true := by decide +kernel
theorem sub5_2390 : sub5 [5, 3, 0] = true := by decide +kernel
theorem sub5_2391 : sub5 [5, 3, 1] = true := by decide +kernel
theorem sub5_2392 : sub5 [5, 3, 2] = true := by decide +kernel
theorem sub5_2393 : sub5 [5, 3, 3] = true := by decide +kernel
theorem sub5_2394 : sub5 [5, 3, 4] = true := by decide +kernel
theorem sub5_2395 : sub5 [5, 4, -11] = true := by decide +kernel
theorem sub5_2396 : sub5 [5, 4, -10] = true := by decide +kernel
theorem sub5_2397 : sub5 [5, 4, -9] = true := by decide +kernel
theorem sub5_2398 : sub5 [5, 4, -8] = true := by decide +kernel
theorem sub5_2399 : sub5 [5, 4, -7] = true := by decide +kernel
theorem sb5_74 : ∀ q ∈ blk5_74, sub5 q = true := by
  unfold blk5_74
  exact List.forall_mem_cons.2 ⟨sub5_2368, List.forall_mem_cons.2 ⟨sub5_2369, List.forall_mem_cons.2 ⟨sub5_2370, List.forall_mem_cons.2 ⟨sub5_2371, List.forall_mem_cons.2 ⟨sub5_2372, List.forall_mem_cons.2 ⟨sub5_2373, List.forall_mem_cons.2 ⟨sub5_2374, List.forall_mem_cons.2 ⟨sub5_2375, List.forall_mem_cons.2 ⟨sub5_2376, List.forall_mem_cons.2 ⟨sub5_2377, List.forall_mem_cons.2 ⟨sub5_2378, List.forall_mem_cons.2 ⟨sub5_2379, List.forall_mem_cons.2 ⟨sub5_2380, List.forall_mem_cons.2 ⟨sub5_2381, List.forall_mem_cons.2 ⟨sub5_2382, List.forall_mem_cons.2 ⟨sub5_2383, List.forall_mem_cons.2 ⟨sub5_2384, List.forall_mem_cons.2 ⟨sub5_2385, List.forall_mem_cons.2 ⟨sub5_2386, List.forall_mem_cons.2 ⟨sub5_2387, List.forall_mem_cons.2 ⟨sub5_2388, List.forall_mem_cons.2 ⟨sub5_2389, List.forall_mem_cons.2 ⟨sub5_2390, List.forall_mem_cons.2 ⟨sub5_2391, List.forall_mem_cons.2 ⟨sub5_2392, List.forall_mem_cons.2 ⟨sub5_2393, List.forall_mem_cons.2 ⟨sub5_2394, List.forall_mem_cons.2 ⟨sub5_2395, List.forall_mem_cons.2 ⟨sub5_2396, List.forall_mem_cons.2 ⟨sub5_2397, List.forall_mem_cons.2 ⟨sub5_2398, List.forall_mem_cons.2 ⟨sub5_2399, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_2400 : sub5 [5, 4, -6] = true := by decide +kernel
theorem sub5_2401 : sub5 [5, 4, -5] = true := by decide +kernel
theorem sub5_2402 : sub5 [5, 4, -4] = true := by decide +kernel
theorem sub5_2403 : sub5 [5, 4, -3] = true := by decide +kernel
theorem sub5_2404 : sub5 [5, 4, -2] = true := by decide +kernel
theorem sub5_2405 : sub5 [5, 4, -1] = true := by decide +kernel
theorem sub5_2406 : sub5 [5, 4, 0] = true := by decide +kernel
theorem sub5_2407 : sub5 [5, 4, 1] = true := by decide +kernel
theorem sub5_2408 : sub5 [5, 4, 2] = true := by decide +kernel
theorem sub5_2409 : sub5 [5, 4, 3] = true := by decide +kernel
theorem sub5_2410 : sub5 [5, 5] = true := by decide +kernel
theorem sub5_2411 : sub5 [5, 6] = true := by decide +kernel
theorem sub5_2412 : sub5 [6, -6] = true := by decide +kernel
theorem sub5_2413 : sub5 [6, -5] = true := by decide +kernel
theorem sub5_2414 : sub5 [6, -4] = true := by decide +kernel
theorem sub5_2415 : sub5 [6, -3] = true := by decide +kernel
theorem sub5_2416 : sub5 [6, -2] = true := by decide +kernel
theorem sub5_2417 : sub5 [6, -1, -9] = true := by decide +kernel
theorem sub5_2418 : sub5 [6, -1, -8] = true := by decide +kernel
theorem sub5_2419 : sub5 [6, -1, -7] = true := by decide +kernel
theorem sub5_2420 : sub5 [6, -1, -6] = true := by decide +kernel
theorem sub5_2421 : sub5 [6, -1, -5] = true := by decide +kernel
theorem sub5_2422 : sub5 [6, -1, -4] = true := by decide +kernel
theorem sub5_2423 : sub5 [6, -1, -3] = true := by decide +kernel
theorem sub5_2424 : sub5 [6, -1, -2] = true := by decide +kernel
theorem sub5_2425 : sub5 [6, -1, -1] = true := by decide +kernel
theorem sub5_2426 : sub5 [6, -1, 0] = true := by decide +kernel
theorem sub5_2427 : sub5 [6, -1, 1] = true := by decide +kernel
theorem sub5_2428 : sub5 [6, -1, 2] = true := by decide +kernel
theorem sub5_2429 : sub5 [6, -1, 3] = true := by decide +kernel
theorem sub5_2430 : sub5 [6, -1, 4] = true := by decide +kernel
theorem sub5_2431 : sub5 [6, -1, 5] = true := by decide +kernel
theorem sb5_75 : ∀ q ∈ blk5_75, sub5 q = true := by
  unfold blk5_75
  exact List.forall_mem_cons.2 ⟨sub5_2400, List.forall_mem_cons.2 ⟨sub5_2401, List.forall_mem_cons.2 ⟨sub5_2402, List.forall_mem_cons.2 ⟨sub5_2403, List.forall_mem_cons.2 ⟨sub5_2404, List.forall_mem_cons.2 ⟨sub5_2405, List.forall_mem_cons.2 ⟨sub5_2406, List.forall_mem_cons.2 ⟨sub5_2407, List.forall_mem_cons.2 ⟨sub5_2408, List.forall_mem_cons.2 ⟨sub5_2409, List.forall_mem_cons.2 ⟨sub5_2410, List.forall_mem_cons.2 ⟨sub5_2411, List.forall_mem_cons.2 ⟨sub5_2412, List.forall_mem_cons.2 ⟨sub5_2413, List.forall_mem_cons.2 ⟨sub5_2414, List.forall_mem_cons.2 ⟨sub5_2415, List.forall_mem_cons.2 ⟨sub5_2416, List.forall_mem_cons.2 ⟨sub5_2417, List.forall_mem_cons.2 ⟨sub5_2418, List.forall_mem_cons.2 ⟨sub5_2419, List.forall_mem_cons.2 ⟨sub5_2420, List.forall_mem_cons.2 ⟨sub5_2421, List.forall_mem_cons.2 ⟨sub5_2422, List.forall_mem_cons.2 ⟨sub5_2423, List.forall_mem_cons.2 ⟨sub5_2424, List.forall_mem_cons.2 ⟨sub5_2425, List.forall_mem_cons.2 ⟨sub5_2426, List.forall_mem_cons.2 ⟨sub5_2427, List.forall_mem_cons.2 ⟨sub5_2428, List.forall_mem_cons.2 ⟨sub5_2429, List.forall_mem_cons.2 ⟨sub5_2430, List.forall_mem_cons.2 ⟨sub5_2431, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_2432 : sub5 [6, 0, -10] = true := by decide +kernel
theorem sub5_2433 : sub5 [6, 0, -9] = true := by decide +kernel
theorem sub5_2434 : sub5 [6, 0, -8] = true := by decide +kernel
theorem sub5_2435 : sub5 [6, 0, -7] = true := by decide +kernel
theorem sub5_2436 : sub5 [6, 0, -6] = true := by decide +kernel
theorem sub5_2437 : sub5 [6, 0, -5] = true := by decide +kernel
theorem sub5_2438 : sub5 [6, 0, -4] = true := by decide +kernel
theorem sub5_2439 : sub5 [6, 0, -3] = true := by decide +kernel
theorem sub5_2440 : sub5 [6, 0, -2] = true := by decide +kernel
theorem sub5_2441 : sub5 [6, 0, -1] = true := by decide +kernel
theorem sub5_2442 : sub5 [6, 0, 0] = true := by decide +kernel
theorem sub5_2443 : sub5 [6, 0, 1] = true := by decide +kernel
theorem sub5_2444 : sub5 [6, 0, 2] = true := by decide +kernel
theorem sub5_2445 : sub5 [6, 0, 3] = true := by decide +kernel
theorem sub5_2446 : sub5 [6, 0, 4] = true := by decide +kernel
theorem sub5_2447 : sub5 [6, 0, 5] = true := by decide +kernel
theorem sub5_2448 : sub5 [6, 1, -10] = true := by decide +kernel
theorem sub5_2449 : sub5 [6, 1, -9] = true := by decide +kernel
theorem sub5_2450 : sub5 [6, 1, -8] = true := by decide +kernel
theorem sub5_2451 : sub5 [6, 1, -7] = true := by decide +kernel
theorem sub5_2452 : sub5 [6, 1, -6] = true := by decide +kernel
theorem sub5_2453 : sub5 [6, 1, -5] = true := by decide +kernel
theorem sub5_2454 : sub5 [6, 1, -4] = true := by decide +kernel
theorem sub5_2455 : sub5 [6, 1, -3] = true := by decide +kernel
theorem sub5_2456 : sub5 [6, 1, -2] = true := by decide +kernel
theorem sub5_2457 : sub5 [6, 1, -1] = true := by decide +kernel
theorem sub5_2458 : sub5 [6, 1, 0] = true := by decide +kernel
theorem sub5_2459 : sub5 [6, 1, 1] = true := by decide +kernel
theorem sub5_2460 : sub5 [6, 1, 2] = true := by decide +kernel
theorem sub5_2461 : sub5 [6, 1, 3] = true := by decide +kernel
theorem sub5_2462 : sub5 [6, 1, 4] = true := by decide +kernel
theorem sub5_2463 : sub5 [6, 2, -10] = true := by decide +kernel
theorem sb5_76 : ∀ q ∈ blk5_76, sub5 q = true := by
  unfold blk5_76
  exact List.forall_mem_cons.2 ⟨sub5_2432, List.forall_mem_cons.2 ⟨sub5_2433, List.forall_mem_cons.2 ⟨sub5_2434, List.forall_mem_cons.2 ⟨sub5_2435, List.forall_mem_cons.2 ⟨sub5_2436, List.forall_mem_cons.2 ⟨sub5_2437, List.forall_mem_cons.2 ⟨sub5_2438, List.forall_mem_cons.2 ⟨sub5_2439, List.forall_mem_cons.2 ⟨sub5_2440, List.forall_mem_cons.2 ⟨sub5_2441, List.forall_mem_cons.2 ⟨sub5_2442, List.forall_mem_cons.2 ⟨sub5_2443, List.forall_mem_cons.2 ⟨sub5_2444, List.forall_mem_cons.2 ⟨sub5_2445, List.forall_mem_cons.2 ⟨sub5_2446, List.forall_mem_cons.2 ⟨sub5_2447, List.forall_mem_cons.2 ⟨sub5_2448, List.forall_mem_cons.2 ⟨sub5_2449, List.forall_mem_cons.2 ⟨sub5_2450, List.forall_mem_cons.2 ⟨sub5_2451, List.forall_mem_cons.2 ⟨sub5_2452, List.forall_mem_cons.2 ⟨sub5_2453, List.forall_mem_cons.2 ⟨sub5_2454, List.forall_mem_cons.2 ⟨sub5_2455, List.forall_mem_cons.2 ⟨sub5_2456, List.forall_mem_cons.2 ⟨sub5_2457, List.forall_mem_cons.2 ⟨sub5_2458, List.forall_mem_cons.2 ⟨sub5_2459, List.forall_mem_cons.2 ⟨sub5_2460, List.forall_mem_cons.2 ⟨sub5_2461, List.forall_mem_cons.2 ⟨sub5_2462, List.forall_mem_cons.2 ⟨sub5_2463, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_2464 : sub5 [6, 2, -9] = true := by decide +kernel
theorem sub5_2465 : sub5 [6, 2, -8] = true := by decide +kernel
theorem sub5_2466 : sub5 [6, 2, -7] = true := by decide +kernel
theorem sub5_2467 : sub5 [6, 2, -6] = true := by decide +kernel
theorem sub5_2468 : sub5 [6, 2, -5] = true := by decide +kernel
theorem sub5_2469 : sub5 [6, 2, -4] = true := by decide +kernel
theorem sub5_2470 : sub5 [6, 2, -3] = true := by decide +kernel
theorem sub5_2471 : sub5 [6, 2, -2] = true := by decide +kernel
theorem sub5_2472 : sub5 [6, 2, -1] = true := by decide +kernel
theorem sub5_2473 : sub5 [6, 2, 0] = true := by decide +kernel
theorem sub5_2474 : sub5 [6, 2, 1] = true := by decide +kernel
theorem sub5_2475 : sub5 [6, 2, 2] = true := by decide +kernel
theorem sub5_2476 : sub5 [6, 2, 3] = true := by decide +kernel
theorem sub5_2477 : sub5 [6, 3] = true := by decide +kernel
theorem sub5_2478 : sub5 [6, 4] = true := by decide +kernel
theorem sub5_2479 : sub5 [6, 5] = true := by decide +kernel
theorem sub5_2480 : sub5 [7, -4] = true := by decide +kernel
theorem sub5_2481 : sub5 [7, -3] = true := by decide +kernel
theorem sub5_2482 : sub5 [7, -2] = true := by decide +kernel
theorem sub5_2483 : sub5 [7, -1] = true := by decide +kernel
theorem sub5_2484 : sub5 [7, 0] = true := by decide +kernel
theorem sub5_2485 : sub5 [7, 1] = true := by decide +kernel
theorem sub5_2486 : sub5 [7, 2] = true := by decide +kernel
theorem sub5_2487 : sub5 [7, 3] = true := by decide +kernel
theorem sub5_2488 : sub5 [7, 4] = true := by decide +kernel
theorem sb5_77 : ∀ q ∈ blk5_77, sub5 q = true := by
  unfold blk5_77
  exact List.forall_mem_cons.2 ⟨sub5_2464, List.forall_mem_cons.2 ⟨sub5_2465, List.forall_mem_cons.2 ⟨sub5_2466, List.forall_mem_cons.2 ⟨sub5_2467, List.forall_mem_cons.2 ⟨sub5_2468, List.forall_mem_cons.2 ⟨sub5_2469, List.forall_mem_cons.2 ⟨sub5_2470, List.forall_mem_cons.2 ⟨sub5_2471, List.forall_mem_cons.2 ⟨sub5_2472, List.forall_mem_cons.2 ⟨sub5_2473, List.forall_mem_cons.2 ⟨sub5_2474, List.forall_mem_cons.2 ⟨sub5_2475, List.forall_mem_cons.2 ⟨sub5_2476, List.forall_mem_cons.2 ⟨sub5_2477, List.forall_mem_cons.2 ⟨sub5_2478, List.forall_mem_cons.2 ⟨sub5_2479, List.forall_mem_cons.2 ⟨sub5_2480, List.forall_mem_cons.2 ⟨sub5_2481, List.forall_mem_cons.2 ⟨sub5_2482, List.forall_mem_cons.2 ⟨sub5_2483, List.forall_mem_cons.2 ⟨sub5_2484, List.forall_mem_cons.2 ⟨sub5_2485, List.forall_mem_cons.2 ⟨sub5_2486, List.forall_mem_cons.2 ⟨sub5_2487, List.forall_mem_cons.2 ⟨sub5_2488, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_0 : sub6 [-7, -2] = true := by decide +kernel
theorem sub6_1 : sub6 [-7, -1] = true := by decide +kernel
theorem sub6_2 : sub6 [-7, 0] = true := by decide +kernel
theorem sub6_3 : sub6 [-7, 1] = true := by decide +kernel
theorem sub6_4 : sub6 [-7, 2] = true := by decide +kernel
theorem sub6_5 : sub6 [-7, 3] = true := by decide +kernel
theorem sub6_6 : sub6 [-7, 4] = true := by decide +kernel
theorem sub6_7 : sub6 [-6, -3] = true := by decide +kernel
theorem sub6_8 : sub6 [-6, -2] = true := by decide +kernel
theorem sub6_9 : sub6 [-6, -1] = true := by decide +kernel
theorem sub6_10 : sub6 [-6, 0] = true := by decide +kernel
theorem sub6_11 : sub6 [-6, 1] = true := by decide +kernel
theorem sub6_12 : sub6 [-6, 2] = true := by decide +kernel
theorem sub6_13 : sub6 [-6, 3] = true := by decide +kernel
theorem sub6_14 : sub6 [-6, 4] = true := by decide +kernel
theorem sub6_15 : sub6 [-6, 5] = true := by decide +kernel
theorem sub6_16 : sub6 [-5, -4] = true := by decide +kernel
theorem sub6_17 : sub6 [-5, -3] = true := by decide +kernel
theorem sub6_18 : sub6 [-5, -2] = true := by decide +kernel
theorem sub6_19 : sub6 [-5, -1] = true := by decide +kernel
theorem sub6_20 : sub6 [-5, 0] = true := by decide +kernel
theorem sub6_21 : sub6 [-5, 1] = true := by decide +kernel
theorem sub6_22 : sub6 [-5, 2] = true := by decide +kernel
theorem sub6_23 : sub6 [-5, 3] = true := by decide +kernel
theorem sub6_24 : sub6 [-5, 4] = true := by decide +kernel
theorem sub6_25 : sub6 [-5, 5] = true := by decide +kernel
theorem sub6_26 : sub6 [-5, 6] = true := by decide +kernel
theorem sub6_27 : sub6 [-4, -5] = true := by decide +kernel
theorem sub6_28 : sub6 [-4, -4] = true := by decide +kernel
theorem sub6_29 : sub6 [-4, -3] = true := by decide +kernel
theorem sub6_30 : sub6 [-4, -2] = true := by decide +kernel
theorem sub6_31 : sub6 [-4, -1] = true := by decide +kernel
theorem sb6_0 : ∀ q ∈ blk6_0, sub6 q = true := by
  unfold blk6_0
  exact List.forall_mem_cons.2 ⟨sub6_0, List.forall_mem_cons.2 ⟨sub6_1, List.forall_mem_cons.2 ⟨sub6_2, List.forall_mem_cons.2 ⟨sub6_3, List.forall_mem_cons.2 ⟨sub6_4, List.forall_mem_cons.2 ⟨sub6_5, List.forall_mem_cons.2 ⟨sub6_6, List.forall_mem_cons.2 ⟨sub6_7, List.forall_mem_cons.2 ⟨sub6_8, List.forall_mem_cons.2 ⟨sub6_9, List.forall_mem_cons.2 ⟨sub6_10, List.forall_mem_cons.2 ⟨sub6_11, List.forall_mem_cons.2 ⟨sub6_12, List.forall_mem_cons.2 ⟨sub6_13, List.forall_mem_cons.2 ⟨sub6_14, List.forall_mem_cons.2 ⟨sub6_15, List.forall_mem_cons.2 ⟨sub6_16, List.forall_mem_cons.2 ⟨sub6_17, List.forall_mem_cons.2 ⟨sub6_18, List.forall_mem_cons.2 ⟨sub6_19, List.forall_mem_cons.2 ⟨sub6_20, List.forall_mem_cons.2 ⟨sub6_21, List.forall_mem_cons.2 ⟨sub6_22, List.forall_mem_cons.2 ⟨sub6_23, List.forall_mem_cons.2 ⟨sub6_24, List.forall_mem_cons.2 ⟨sub6_25, List.forall_mem_cons.2 ⟨sub6_26, List.forall_mem_cons.2 ⟨sub6_27, List.forall_mem_cons.2 ⟨sub6_28, List.forall_mem_cons.2 ⟨sub6_29, List.forall_mem_cons.2 ⟨sub6_30, List.forall_mem_cons.2 ⟨sub6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_32 : sub6 [-4, 0] = true := by decide +kernel
theorem sub6_33 : sub6 [-4, 1] = true := by decide +kernel
theorem sub6_34 : sub6 [-4, 2] = true := by decide +kernel
theorem sub6_35 : sub6 [-4, 3] = true := by decide +kernel
theorem sub6_36 : sub6 [-4, 4] = true := by decide +kernel
theorem sub6_37 : sub6 [-4, 5] = true := by decide +kernel
theorem sub6_38 : sub6 [-4, 6] = true := by decide +kernel
theorem sub6_39 : sub6 [-3, -6] = true := by decide +kernel
theorem sub6_40 : sub6 [-3, -5] = true := by decide +kernel
theorem sub6_41 : sub6 [-3, -4] = true := by decide +kernel
theorem sub6_42 : sub6 [-3, -3] = true := by decide +kernel
theorem sub6_43 : sub6 [-3, -2] = true := by decide +kernel
theorem sub6_44 : sub6 [-3, -1, -6] = true := by decide +kernel
theorem sub6_45 : sub6 [-3, -1, -5] = true := by decide +kernel
theorem sub6_46 : sub6 [-3, -1, -4] = true := by decide +kernel
theorem sub6_47 : sub6 [-3, -1, -3] = true := by decide +kernel
theorem sub6_48 : sub6 [-3, -1, -2] = true := by decide +kernel
theorem sub6_49 : sub6 [-3, -1, -1] = true := by decide +kernel
theorem sub6_50 : sub6 [-3, -1, 0] = true := by decide +kernel
theorem sub6_51 : sub6 [-3, -1, 1] = true := by decide +kernel
theorem sub6_52 : sub6 [-3, -1, 2] = true := by decide +kernel
theorem sub6_53 : sub6 [-3, -1, 3] = true := by decide +kernel
theorem sub6_54 : sub6 [-3, -1, 4] = true := by decide +kernel
theorem sub6_55 : sub6 [-3, -1, 5] = true := by decide +kernel
theorem sub6_56 : sub6 [-3, -1, 6] = true := by decide +kernel
theorem sub6_57 : sub6 [-3, -1, 7] = true := by decide +kernel
theorem sub6_58 : sub6 [-3, 0, -6] = true := by decide +kernel
theorem sub6_59 : sub6 [-3, 0, -5] = true := by decide +kernel
theorem sub6_60 : sub6 [-3, 0, -4] = true := by decide +kernel
theorem sub6_61 : sub6 [-3, 0, -3] = true := by decide +kernel
theorem sub6_62 : sub6 [-3, 0, -2] = true := by decide +kernel
theorem sub6_63 : sub6 [-3, 0, -1] = true := by decide +kernel
theorem sb6_1 : ∀ q ∈ blk6_1, sub6 q = true := by
  unfold blk6_1
  exact List.forall_mem_cons.2 ⟨sub6_32, List.forall_mem_cons.2 ⟨sub6_33, List.forall_mem_cons.2 ⟨sub6_34, List.forall_mem_cons.2 ⟨sub6_35, List.forall_mem_cons.2 ⟨sub6_36, List.forall_mem_cons.2 ⟨sub6_37, List.forall_mem_cons.2 ⟨sub6_38, List.forall_mem_cons.2 ⟨sub6_39, List.forall_mem_cons.2 ⟨sub6_40, List.forall_mem_cons.2 ⟨sub6_41, List.forall_mem_cons.2 ⟨sub6_42, List.forall_mem_cons.2 ⟨sub6_43, List.forall_mem_cons.2 ⟨sub6_44, List.forall_mem_cons.2 ⟨sub6_45, List.forall_mem_cons.2 ⟨sub6_46, List.forall_mem_cons.2 ⟨sub6_47, List.forall_mem_cons.2 ⟨sub6_48, List.forall_mem_cons.2 ⟨sub6_49, List.forall_mem_cons.2 ⟨sub6_50, List.forall_mem_cons.2 ⟨sub6_51, List.forall_mem_cons.2 ⟨sub6_52, List.forall_mem_cons.2 ⟨sub6_53, List.forall_mem_cons.2 ⟨sub6_54, List.forall_mem_cons.2 ⟨sub6_55, List.forall_mem_cons.2 ⟨sub6_56, List.forall_mem_cons.2 ⟨sub6_57, List.forall_mem_cons.2 ⟨sub6_58, List.forall_mem_cons.2 ⟨sub6_59, List.forall_mem_cons.2 ⟨sub6_60, List.forall_mem_cons.2 ⟨sub6_61, List.forall_mem_cons.2 ⟨sub6_62, List.forall_mem_cons.2 ⟨sub6_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_64 : sub6 [-3, 0, 0] = true := by decide +kernel
theorem sub6_65 : sub6 [-3, 0, 1] = true := by decide +kernel
theorem sub6_66 : sub6 [-3, 0, 2] = true := by decide +kernel
theorem sub6_67 : sub6 [-3, 0, 3] = true := by decide +kernel
theorem sub6_68 : sub6 [-3, 0, 4] = true := by decide +kernel
theorem sub6_69 : sub6 [-3, 0, 5] = true := by decide +kernel
theorem sub6_70 : sub6 [-3, 0, 6] = true := by decide +kernel
theorem sub6_71 : sub6 [-3, 0, 7] = true := by decide +kernel
theorem sub6_72 : sub6 [-3, 1, -6] = true := by decide +kernel
theorem sub6_73 : sub6 [-3, 1, -5] = true := by decide +kernel
theorem sub6_74 : sub6 [-3, 1, -4] = true := by decide +kernel
theorem sub6_75 : sub6 [-3, 1, -3] = true := by decide +kernel
theorem sub6_76 : sub6 [-3, 1, -2] = true := by decide +kernel
theorem sub6_77 : sub6 [-3, 1, -1] = true := by decide +kernel
theorem sub6_78 : sub6 [-3, 1, 0] = true := by decide +kernel
theorem sub6_79 : sub6 [-3, 1, 1] = true := by decide +kernel
theorem sub6_80 : sub6 [-3, 1, 2] = true := by decide +kernel
theorem sub6_81 : sub6 [-3, 1, 3] = true := by decide +kernel
theorem sub6_82 : sub6 [-3, 1, 4] = true := by decide +kernel
theorem sub6_83 : sub6 [-3, 1, 5] = true := by decide +kernel
theorem sub6_84 : sub6 [-3, 1, 6] = true := by decide +kernel
theorem sub6_85 : sub6 [-3, 1, 7] = true := by decide +kernel
theorem sub6_86 : sub6 [-3, 2, -5] = true := by decide +kernel
theorem sub6_87 : sub6 [-3, 2, -4] = true := by decide +kernel
theorem sub6_88 : sub6 [-3, 2, -3] = true := by decide +kernel
theorem sub6_89 : sub6 [-3, 2, -2] = true := by decide +kernel
theorem sub6_90 : sub6 [-3, 2, -1] = true := by decide +kernel
theorem sub6_91 : sub6 [-3, 2, 0] = true := by decide +kernel
theorem sub6_92 : sub6 [-3, 2, 1] = true := by decide +kernel
theorem sub6_93 : sub6 [-3, 2, 2] = true := by decide +kernel
theorem sub6_94 : sub6 [-3, 2, 3] = true := by decide +kernel
theorem sub6_95 : sub6 [-3, 2, 4] = true := by decide +kernel
theorem sb6_2 : ∀ q ∈ blk6_2, sub6 q = true := by
  unfold blk6_2
  exact List.forall_mem_cons.2 ⟨sub6_64, List.forall_mem_cons.2 ⟨sub6_65, List.forall_mem_cons.2 ⟨sub6_66, List.forall_mem_cons.2 ⟨sub6_67, List.forall_mem_cons.2 ⟨sub6_68, List.forall_mem_cons.2 ⟨sub6_69, List.forall_mem_cons.2 ⟨sub6_70, List.forall_mem_cons.2 ⟨sub6_71, List.forall_mem_cons.2 ⟨sub6_72, List.forall_mem_cons.2 ⟨sub6_73, List.forall_mem_cons.2 ⟨sub6_74, List.forall_mem_cons.2 ⟨sub6_75, List.forall_mem_cons.2 ⟨sub6_76, List.forall_mem_cons.2 ⟨sub6_77, List.forall_mem_cons.2 ⟨sub6_78, List.forall_mem_cons.2 ⟨sub6_79, List.forall_mem_cons.2 ⟨sub6_80, List.forall_mem_cons.2 ⟨sub6_81, List.forall_mem_cons.2 ⟨sub6_82, List.forall_mem_cons.2 ⟨sub6_83, List.forall_mem_cons.2 ⟨sub6_84, List.forall_mem_cons.2 ⟨sub6_85, List.forall_mem_cons.2 ⟨sub6_86, List.forall_mem_cons.2 ⟨sub6_87, List.forall_mem_cons.2 ⟨sub6_88, List.forall_mem_cons.2 ⟨sub6_89, List.forall_mem_cons.2 ⟨sub6_90, List.forall_mem_cons.2 ⟨sub6_91, List.forall_mem_cons.2 ⟨sub6_92, List.forall_mem_cons.2 ⟨sub6_93, List.forall_mem_cons.2 ⟨sub6_94, List.forall_mem_cons.2 ⟨sub6_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C083
