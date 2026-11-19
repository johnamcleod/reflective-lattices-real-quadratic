import ReflectZphi.Data.Cert5.C116.Base

namespace ReflectZphi.Data.Cert5.C116

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_1_2304 : subd9_1 [-1, 4, 4] = true := by decide +kernel
theorem subd9_1_2305 : subd9_1 [-1, 4, 5] = true := by decide +kernel
theorem subd9_1_2306 : subd9_1 [-1, 4, 6] = true := by decide +kernel
theorem subd9_1_2307 : subd9_1 [-1, 4, 7] = true := by decide +kernel
theorem subd9_1_2308 : subd9_1 [-1, 4, 8] = true := by decide +kernel
theorem subd9_1_2309 : subd9_1 [-1, 4, 9] = true := by decide +kernel
theorem subd9_1_2310 : subd9_1 [-1, 4, 10] = true := by decide +kernel
theorem subd9_1_2311 : subd9_1 [-1, 4, 11] = true := by decide +kernel
theorem subd9_1_2312 : subd9_1 [-1, 5, -8] = true := by decide +kernel
theorem subd9_1_2313 : subd9_1 [-1, 5, -7] = true := by decide +kernel
theorem subd9_1_2314 : subd9_1 [-1, 5, -6] = true := by decide +kernel
theorem subd9_1_2315 : subd9_1 [-1, 5, -5] = true := by decide +kernel
theorem subd9_1_2316 : subd9_1 [-1, 5, -4] = true := by decide +kernel
theorem subd9_1_2317 : subd9_1 [-1, 5, -3] = true := by decide +kernel
theorem subd9_1_2318 : subd9_1 [-1, 5, -2] = true := by decide +kernel
theorem subd9_1_2319 : subd9_1 [-1, 5, -1] = true := by decide +kernel
theorem subd9_1_2320 : subd9_1 [-1, 5, 0] = true := by decide +kernel
theorem subd9_1_2321 : subd9_1 [-1, 5, 1] = true := by decide +kernel
theorem subd9_1_2322 : subd9_1 [-1, 5, 2] = true := by decide +kernel
theorem subd9_1_2323 : subd9_1 [-1, 5, 3] = true := by decide +kernel
theorem subd9_1_2324 : subd9_1 [-1, 5, 4] = true := by decide +kernel
theorem subd9_1_2325 : subd9_1 [-1, 5, 5] = true := by decide +kernel
theorem subd9_1_2326 : subd9_1 [-1, 5, 6] = true := by decide +kernel
theorem subd9_1_2327 : subd9_1 [-1, 5, 7] = true := by decide +kernel
theorem subd9_1_2328 : subd9_1 [-1, 5, 8] = true := by decide +kernel
theorem subd9_1_2329 : subd9_1 [-1, 5, 9] = true := by decide +kernel
theorem subd9_1_2330 : subd9_1 [-1, 5, 10] = true := by decide +kernel
theorem subd9_1_2331 : subd9_1 [-1, 5, 11] = true := by decide +kernel
theorem subd9_1_2332 : subd9_1 [-1, 6, -7] = true := by decide +kernel
theorem subd9_1_2333 : subd9_1 [-1, 6, -6] = true := by decide +kernel
theorem subd9_1_2334 : subd9_1 [-1, 6, -5] = true := by decide +kernel
theorem subd9_1_2335 : subd9_1 [-1, 6, -4] = true := by decide +kernel
theorem sbd9_1_72 : ∀ q ∈ blkd9_1_72, subd9_1 q = true := by
  unfold blkd9_1_72
  exact List.forall_mem_cons.2 ⟨subd9_1_2304, List.forall_mem_cons.2 ⟨subd9_1_2305, List.forall_mem_cons.2 ⟨subd9_1_2306, List.forall_mem_cons.2 ⟨subd9_1_2307, List.forall_mem_cons.2 ⟨subd9_1_2308, List.forall_mem_cons.2 ⟨subd9_1_2309, List.forall_mem_cons.2 ⟨subd9_1_2310, List.forall_mem_cons.2 ⟨subd9_1_2311, List.forall_mem_cons.2 ⟨subd9_1_2312, List.forall_mem_cons.2 ⟨subd9_1_2313, List.forall_mem_cons.2 ⟨subd9_1_2314, List.forall_mem_cons.2 ⟨subd9_1_2315, List.forall_mem_cons.2 ⟨subd9_1_2316, List.forall_mem_cons.2 ⟨subd9_1_2317, List.forall_mem_cons.2 ⟨subd9_1_2318, List.forall_mem_cons.2 ⟨subd9_1_2319, List.forall_mem_cons.2 ⟨subd9_1_2320, List.forall_mem_cons.2 ⟨subd9_1_2321, List.forall_mem_cons.2 ⟨subd9_1_2322, List.forall_mem_cons.2 ⟨subd9_1_2323, List.forall_mem_cons.2 ⟨subd9_1_2324, List.forall_mem_cons.2 ⟨subd9_1_2325, List.forall_mem_cons.2 ⟨subd9_1_2326, List.forall_mem_cons.2 ⟨subd9_1_2327, List.forall_mem_cons.2 ⟨subd9_1_2328, List.forall_mem_cons.2 ⟨subd9_1_2329, List.forall_mem_cons.2 ⟨subd9_1_2330, List.forall_mem_cons.2 ⟨subd9_1_2331, List.forall_mem_cons.2 ⟨subd9_1_2332, List.forall_mem_cons.2 ⟨subd9_1_2333, List.forall_mem_cons.2 ⟨subd9_1_2334, List.forall_mem_cons.2 ⟨subd9_1_2335, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_2336 : subd9_1 [-1, 6, -3] = true := by decide +kernel
theorem subd9_1_2337 : subd9_1 [-1, 6, -2] = true := by decide +kernel
theorem subd9_1_2338 : subd9_1 [-1, 6, -1] = true := by decide +kernel
theorem subd9_1_2339 : subd9_1 [-1, 6, 0] = true := by decide +kernel
theorem subd9_1_2340 : subd9_1 [-1, 6, 1] = true := by decide +kernel
theorem subd9_1_2341 : subd9_1 [-1, 6, 2] = true := by decide +kernel
theorem subd9_1_2342 : subd9_1 [-1, 6, 3] = true := by decide +kernel
theorem subd9_1_2343 : subd9_1 [-1, 6, 4] = true := by decide +kernel
theorem subd9_1_2344 : subd9_1 [-1, 6, 5] = true := by decide +kernel
theorem subd9_1_2345 : subd9_1 [-1, 6, 6] = true := by decide +kernel
theorem subd9_1_2346 : subd9_1 [-1, 6, 7] = true := by decide +kernel
theorem subd9_1_2347 : subd9_1 [-1, 6, 8] = true := by decide +kernel
theorem subd9_1_2348 : subd9_1 [-1, 6, 9] = true := by decide +kernel
theorem subd9_1_2349 : subd9_1 [-1, 6, 10] = true := by decide +kernel
theorem subd9_1_2350 : subd9_1 [-1, 6, 11] = true := by decide +kernel
theorem subd9_1_2351 : subd9_1 [-1, 7, -6] = true := by decide +kernel
theorem subd9_1_2352 : subd9_1 [-1, 7, -5] = true := by decide +kernel
theorem subd9_1_2353 : subd9_1 [-1, 7, -4] = true := by decide +kernel
theorem subd9_1_2354 : subd9_1 [-1, 7, -3] = true := by decide +kernel
theorem subd9_1_2355 : subd9_1 [-1, 7, -2] = true := by decide +kernel
theorem subd9_1_2356 : subd9_1 [-1, 7, -1] = true := by decide +kernel
theorem subd9_1_2357 : subd9_1 [-1, 7, 0] = true := by decide +kernel
theorem subd9_1_2358 : subd9_1 [-1, 7, 1] = true := by decide +kernel
theorem subd9_1_2359 : subd9_1 [-1, 7, 2] = true := by decide +kernel
theorem subd9_1_2360 : subd9_1 [-1, 7, 3] = true := by decide +kernel
theorem subd9_1_2361 : subd9_1 [-1, 7, 4] = true := by decide +kernel
theorem subd9_1_2362 : subd9_1 [-1, 7, 5] = true := by decide +kernel
theorem subd9_1_2363 : subd9_1 [-1, 7, 6] = true := by decide +kernel
theorem subd9_1_2364 : subd9_1 [-1, 7, 7] = true := by decide +kernel
theorem subd9_1_2365 : subd9_1 [-1, 7, 8] = true := by decide +kernel
theorem subd9_1_2366 : subd9_1 [-1, 7, 9] = true := by decide +kernel
theorem subd9_1_2367 : subd9_1 [-1, 7, 10] = true := by decide +kernel
theorem sbd9_1_73 : ∀ q ∈ blkd9_1_73, subd9_1 q = true := by
  unfold blkd9_1_73
  exact List.forall_mem_cons.2 ⟨subd9_1_2336, List.forall_mem_cons.2 ⟨subd9_1_2337, List.forall_mem_cons.2 ⟨subd9_1_2338, List.forall_mem_cons.2 ⟨subd9_1_2339, List.forall_mem_cons.2 ⟨subd9_1_2340, List.forall_mem_cons.2 ⟨subd9_1_2341, List.forall_mem_cons.2 ⟨subd9_1_2342, List.forall_mem_cons.2 ⟨subd9_1_2343, List.forall_mem_cons.2 ⟨subd9_1_2344, List.forall_mem_cons.2 ⟨subd9_1_2345, List.forall_mem_cons.2 ⟨subd9_1_2346, List.forall_mem_cons.2 ⟨subd9_1_2347, List.forall_mem_cons.2 ⟨subd9_1_2348, List.forall_mem_cons.2 ⟨subd9_1_2349, List.forall_mem_cons.2 ⟨subd9_1_2350, List.forall_mem_cons.2 ⟨subd9_1_2351, List.forall_mem_cons.2 ⟨subd9_1_2352, List.forall_mem_cons.2 ⟨subd9_1_2353, List.forall_mem_cons.2 ⟨subd9_1_2354, List.forall_mem_cons.2 ⟨subd9_1_2355, List.forall_mem_cons.2 ⟨subd9_1_2356, List.forall_mem_cons.2 ⟨subd9_1_2357, List.forall_mem_cons.2 ⟨subd9_1_2358, List.forall_mem_cons.2 ⟨subd9_1_2359, List.forall_mem_cons.2 ⟨subd9_1_2360, List.forall_mem_cons.2 ⟨subd9_1_2361, List.forall_mem_cons.2 ⟨subd9_1_2362, List.forall_mem_cons.2 ⟨subd9_1_2363, List.forall_mem_cons.2 ⟨subd9_1_2364, List.forall_mem_cons.2 ⟨subd9_1_2365, List.forall_mem_cons.2 ⟨subd9_1_2366, List.forall_mem_cons.2 ⟨subd9_1_2367, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_2368 : subd9_1 [-1, 7, 11] = true := by decide +kernel
theorem subd9_1_2369 : subd9_1 [-1, 8, -5] = true := by decide +kernel
theorem subd9_1_2370 : subd9_1 [-1, 8, -4] = true := by decide +kernel
theorem subd9_1_2371 : subd9_1 [-1, 8, -3] = true := by decide +kernel
theorem subd9_1_2372 : subd9_1 [-1, 8, -2] = true := by decide +kernel
theorem subd9_1_2373 : subd9_1 [-1, 8, -1] = true := by decide +kernel
theorem subd9_1_2374 : subd9_1 [-1, 8, 0] = true := by decide +kernel
theorem subd9_1_2375 : subd9_1 [-1, 8, 1] = true := by decide +kernel
theorem subd9_1_2376 : subd9_1 [-1, 8, 2] = true := by decide +kernel
theorem subd9_1_2377 : subd9_1 [-1, 8, 3] = true := by decide +kernel
theorem subd9_1_2378 : subd9_1 [-1, 8, 4] = true := by decide +kernel
theorem subd9_1_2379 : subd9_1 [-1, 8, 5] = true := by decide +kernel
theorem subd9_1_2380 : subd9_1 [-1, 8, 6] = true := by decide +kernel
theorem subd9_1_2381 : subd9_1 [-1, 8, 7] = true := by decide +kernel
theorem subd9_1_2382 : subd9_1 [-1, 8, 8] = true := by decide +kernel
theorem subd9_1_2383 : subd9_1 [-1, 8, 9] = true := by decide +kernel
theorem subd9_1_2384 : subd9_1 [-1, 8, 10] = true := by decide +kernel
theorem subd9_1_2385 : subd9_1 [-1, 9] = true := by decide +kernel
theorem subd9_1_2386 : subd9_1 [-1, 10] = true := by decide +kernel
theorem subd9_1_2387 : subd9_1 [-1, 11] = true := by decide +kernel
theorem subd9_1_2388 : subd9_1 [0, -13] = true := by decide +kernel
theorem subd9_1_2389 : subd9_1 [0, -12] = true := by decide +kernel
theorem subd9_1_2390 : subd9_1 [0, -11] = true := by decide +kernel
theorem subd9_1_2391 : subd9_1 [0, -10] = true := by decide +kernel
theorem subd9_1_2392 : subd9_1 [0, -9, -11] = true := by decide +kernel
theorem subd9_1_2393 : subd9_1 [0, -9, -10] = true := by decide +kernel
theorem subd9_1_2394 : subd9_1 [0, -9, -9] = true := by decide +kernel
theorem subd9_1_2395 : subd9_1 [0, -9, -8] = true := by decide +kernel
theorem subd9_1_2396 : subd9_1 [0, -9, -7] = true := by decide +kernel
theorem subd9_1_2397 : subd9_1 [0, -9, -6] = true := by decide +kernel
theorem subd9_1_2398 : subd9_1 [0, -9, -5] = true := by decide +kernel
theorem subd9_1_2399 : subd9_1 [0, -9, -4] = true := by decide +kernel
theorem sbd9_1_74 : ∀ q ∈ blkd9_1_74, subd9_1 q = true := by
  unfold blkd9_1_74
  exact List.forall_mem_cons.2 ⟨subd9_1_2368, List.forall_mem_cons.2 ⟨subd9_1_2369, List.forall_mem_cons.2 ⟨subd9_1_2370, List.forall_mem_cons.2 ⟨subd9_1_2371, List.forall_mem_cons.2 ⟨subd9_1_2372, List.forall_mem_cons.2 ⟨subd9_1_2373, List.forall_mem_cons.2 ⟨subd9_1_2374, List.forall_mem_cons.2 ⟨subd9_1_2375, List.forall_mem_cons.2 ⟨subd9_1_2376, List.forall_mem_cons.2 ⟨subd9_1_2377, List.forall_mem_cons.2 ⟨subd9_1_2378, List.forall_mem_cons.2 ⟨subd9_1_2379, List.forall_mem_cons.2 ⟨subd9_1_2380, List.forall_mem_cons.2 ⟨subd9_1_2381, List.forall_mem_cons.2 ⟨subd9_1_2382, List.forall_mem_cons.2 ⟨subd9_1_2383, List.forall_mem_cons.2 ⟨subd9_1_2384, List.forall_mem_cons.2 ⟨subd9_1_2385, List.forall_mem_cons.2 ⟨subd9_1_2386, List.forall_mem_cons.2 ⟨subd9_1_2387, List.forall_mem_cons.2 ⟨subd9_1_2388, List.forall_mem_cons.2 ⟨subd9_1_2389, List.forall_mem_cons.2 ⟨subd9_1_2390, List.forall_mem_cons.2 ⟨subd9_1_2391, List.forall_mem_cons.2 ⟨subd9_1_2392, List.forall_mem_cons.2 ⟨subd9_1_2393, List.forall_mem_cons.2 ⟨subd9_1_2394, List.forall_mem_cons.2 ⟨subd9_1_2395, List.forall_mem_cons.2 ⟨subd9_1_2396, List.forall_mem_cons.2 ⟨subd9_1_2397, List.forall_mem_cons.2 ⟨subd9_1_2398, List.forall_mem_cons.2 ⟨subd9_1_2399, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_2400 : subd9_1 [0, -9, -3] = true := by decide +kernel
theorem subd9_1_2401 : subd9_1 [0, -9, -2] = true := by decide +kernel
theorem subd9_1_2402 : subd9_1 [0, -9, -1] = true := by decide +kernel
theorem subd9_1_2403 : subd9_1 [0, -9, 0] = true := by decide +kernel
theorem subd9_1_2404 : subd9_1 [0, -9, 1] = true := by decide +kernel
theorem subd9_1_2405 : subd9_1 [0, -9, 2] = true := by decide +kernel
theorem subd9_1_2406 : subd9_1 [0, -9, 3] = true := by decide +kernel
theorem subd9_1_2407 : subd9_1 [0, -8, -12] = true := by decide +kernel
theorem subd9_1_2408 : subd9_1 [0, -8, -11] = true := by decide +kernel
theorem subd9_1_2409 : subd9_1 [0, -8, -10] = true := by decide +kernel
theorem subd9_1_2410 : subd9_1 [0, -8, -9] = true := by decide +kernel
theorem subd9_1_2411 : subd9_1 [0, -8, -8] = true := by decide +kernel
theorem subd9_1_2412 : subd9_1 [0, -8, -7] = true := by decide +kernel
theorem subd9_1_2413 : subd9_1 [0, -8, -6] = true := by decide +kernel
theorem subd9_1_2414 : subd9_1 [0, -8, -5] = true := by decide +kernel
theorem subd9_1_2415 : subd9_1 [0, -8, -4] = true := by decide +kernel
theorem subd9_1_2416 : subd9_1 [0, -8, -3] = true := by decide +kernel
theorem subd9_1_2417 : subd9_1 [0, -8, -2] = true := by decide +kernel
theorem subd9_1_2418 : subd9_1 [0, -8, -1] = true := by decide +kernel
theorem subd9_1_2419 : subd9_1 [0, -8, 0] = true := by decide +kernel
theorem subd9_1_2420 : subd9_1 [0, -8, 1] = true := by decide +kernel
theorem subd9_1_2421 : subd9_1 [0, -8, 2] = true := by decide +kernel
theorem subd9_1_2422 : subd9_1 [0, -8, 3] = true := by decide +kernel
theorem subd9_1_2423 : subd9_1 [0, -8, 4] = true := by decide +kernel
theorem subd9_1_2424 : subd9_1 [0, -7, -12] = true := by decide +kernel
theorem subd9_1_2425 : subd9_1 [0, -7, -11] = true := by decide +kernel
theorem subd9_1_2426 : subd9_1 [0, -7, -10] = true := by decide +kernel
theorem subd9_1_2427 : subd9_1 [0, -7, -9] = true := by decide +kernel
theorem subd9_1_2428 : subd9_1 [0, -7, -8] = true := by decide +kernel
theorem subd9_1_2429 : subd9_1 [0, -7, -7] = true := by decide +kernel
theorem subd9_1_2430 : subd9_1 [0, -7, -6] = true := by decide +kernel
theorem subd9_1_2431 : subd9_1 [0, -7, -5] = true := by decide +kernel
theorem sbd9_1_75 : ∀ q ∈ blkd9_1_75, subd9_1 q = true := by
  unfold blkd9_1_75
  exact List.forall_mem_cons.2 ⟨subd9_1_2400, List.forall_mem_cons.2 ⟨subd9_1_2401, List.forall_mem_cons.2 ⟨subd9_1_2402, List.forall_mem_cons.2 ⟨subd9_1_2403, List.forall_mem_cons.2 ⟨subd9_1_2404, List.forall_mem_cons.2 ⟨subd9_1_2405, List.forall_mem_cons.2 ⟨subd9_1_2406, List.forall_mem_cons.2 ⟨subd9_1_2407, List.forall_mem_cons.2 ⟨subd9_1_2408, List.forall_mem_cons.2 ⟨subd9_1_2409, List.forall_mem_cons.2 ⟨subd9_1_2410, List.forall_mem_cons.2 ⟨subd9_1_2411, List.forall_mem_cons.2 ⟨subd9_1_2412, List.forall_mem_cons.2 ⟨subd9_1_2413, List.forall_mem_cons.2 ⟨subd9_1_2414, List.forall_mem_cons.2 ⟨subd9_1_2415, List.forall_mem_cons.2 ⟨subd9_1_2416, List.forall_mem_cons.2 ⟨subd9_1_2417, List.forall_mem_cons.2 ⟨subd9_1_2418, List.forall_mem_cons.2 ⟨subd9_1_2419, List.forall_mem_cons.2 ⟨subd9_1_2420, List.forall_mem_cons.2 ⟨subd9_1_2421, List.forall_mem_cons.2 ⟨subd9_1_2422, List.forall_mem_cons.2 ⟨subd9_1_2423, List.forall_mem_cons.2 ⟨subd9_1_2424, List.forall_mem_cons.2 ⟨subd9_1_2425, List.forall_mem_cons.2 ⟨subd9_1_2426, List.forall_mem_cons.2 ⟨subd9_1_2427, List.forall_mem_cons.2 ⟨subd9_1_2428, List.forall_mem_cons.2 ⟨subd9_1_2429, List.forall_mem_cons.2 ⟨subd9_1_2430, List.forall_mem_cons.2 ⟨subd9_1_2431, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_2432 : subd9_1 [0, -7, -4] = true := by decide +kernel
theorem subd9_1_2433 : subd9_1 [0, -7, -3] = true := by decide +kernel
theorem subd9_1_2434 : subd9_1 [0, -7, -2] = true := by decide +kernel
theorem subd9_1_2435 : subd9_1 [0, -7, -1] = true := by decide +kernel
theorem subd9_1_2436 : subd9_1 [0, -7, 0] = true := by decide +kernel
theorem subd9_1_2437 : subd9_1 [0, -7, 1] = true := by decide +kernel
theorem subd9_1_2438 : subd9_1 [0, -7, 2] = true := by decide +kernel
theorem subd9_1_2439 : subd9_1 [0, -7, 3] = true := by decide +kernel
theorem subd9_1_2440 : subd9_1 [0, -7, 4] = true := by decide +kernel
theorem subd9_1_2441 : subd9_1 [0, -7, 5] = true := by decide +kernel
theorem subd9_1_2442 : subd9_1 [0, -6, -12] = true := by decide +kernel
theorem subd9_1_2443 : subd9_1 [0, -6, -11] = true := by decide +kernel
theorem subd9_1_2444 : subd9_1 [0, -6, -10] = true := by decide +kernel
theorem subd9_1_2445 : subd9_1 [0, -6, -9] = true := by decide +kernel
theorem subd9_1_2446 : subd9_1 [0, -6, -8] = true := by decide +kernel
theorem subd9_1_2447 : subd9_1 [0, -6, -7] = true := by decide +kernel
theorem subd9_1_2448 : subd9_1 [0, -6, -6] = true := by decide +kernel
theorem subd9_1_2449 : subd9_1 [0, -6, -5] = true := by decide +kernel
theorem subd9_1_2450 : subd9_1 [0, -6, -4] = true := by decide +kernel
theorem subd9_1_2451 : subd9_1 [0, -6, -3] = true := by decide +kernel
theorem subd9_1_2452 : subd9_1 [0, -6, -2] = true := by decide +kernel
theorem subd9_1_2453 : subd9_1 [0, -6, -1] = true := by decide +kernel
theorem subd9_1_2454 : subd9_1 [0, -6, 0] = true := by decide +kernel
theorem subd9_1_2455 : subd9_1 [0, -6, 1] = true := by decide +kernel
theorem subd9_1_2456 : subd9_1 [0, -6, 2] = true := by decide +kernel
theorem subd9_1_2457 : subd9_1 [0, -6, 3] = true := by decide +kernel
theorem subd9_1_2458 : subd9_1 [0, -6, 4] = true := by decide +kernel
theorem subd9_1_2459 : subd9_1 [0, -6, 5] = true := by decide +kernel
theorem subd9_1_2460 : subd9_1 [0, -6, 6] = true := by decide +kernel
theorem subd9_1_2461 : subd9_1 [0, -5, -12] = true := by decide +kernel
theorem subd9_1_2462 : subd9_1 [0, -5, -11] = true := by decide +kernel
theorem subd9_1_2463 : subd9_1 [0, -5, -10] = true := by decide +kernel
theorem sbd9_1_76 : ∀ q ∈ blkd9_1_76, subd9_1 q = true := by
  unfold blkd9_1_76
  exact List.forall_mem_cons.2 ⟨subd9_1_2432, List.forall_mem_cons.2 ⟨subd9_1_2433, List.forall_mem_cons.2 ⟨subd9_1_2434, List.forall_mem_cons.2 ⟨subd9_1_2435, List.forall_mem_cons.2 ⟨subd9_1_2436, List.forall_mem_cons.2 ⟨subd9_1_2437, List.forall_mem_cons.2 ⟨subd9_1_2438, List.forall_mem_cons.2 ⟨subd9_1_2439, List.forall_mem_cons.2 ⟨subd9_1_2440, List.forall_mem_cons.2 ⟨subd9_1_2441, List.forall_mem_cons.2 ⟨subd9_1_2442, List.forall_mem_cons.2 ⟨subd9_1_2443, List.forall_mem_cons.2 ⟨subd9_1_2444, List.forall_mem_cons.2 ⟨subd9_1_2445, List.forall_mem_cons.2 ⟨subd9_1_2446, List.forall_mem_cons.2 ⟨subd9_1_2447, List.forall_mem_cons.2 ⟨subd9_1_2448, List.forall_mem_cons.2 ⟨subd9_1_2449, List.forall_mem_cons.2 ⟨subd9_1_2450, List.forall_mem_cons.2 ⟨subd9_1_2451, List.forall_mem_cons.2 ⟨subd9_1_2452, List.forall_mem_cons.2 ⟨subd9_1_2453, List.forall_mem_cons.2 ⟨subd9_1_2454, List.forall_mem_cons.2 ⟨subd9_1_2455, List.forall_mem_cons.2 ⟨subd9_1_2456, List.forall_mem_cons.2 ⟨subd9_1_2457, List.forall_mem_cons.2 ⟨subd9_1_2458, List.forall_mem_cons.2 ⟨subd9_1_2459, List.forall_mem_cons.2 ⟨subd9_1_2460, List.forall_mem_cons.2 ⟨subd9_1_2461, List.forall_mem_cons.2 ⟨subd9_1_2462, List.forall_mem_cons.2 ⟨subd9_1_2463, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_2464 : subd9_1 [0, -5, -9] = true := by decide +kernel
theorem subd9_1_2465 : subd9_1 [0, -5, -8] = true := by decide +kernel
theorem subd9_1_2466 : subd9_1 [0, -5, -7] = true := by decide +kernel
theorem subd9_1_2467 : subd9_1 [0, -5, -6] = true := by decide +kernel
theorem subd9_1_2468 : subd9_1 [0, -5, -5] = true := by decide +kernel
theorem subd9_1_2469 : subd9_1 [0, -5, -4] = true := by decide +kernel
theorem subd9_1_2470 : subd9_1 [0, -5, -3] = true := by decide +kernel
theorem subd9_1_2471 : subd9_1 [0, -5, -2] = true := by decide +kernel
theorem subd9_1_2472 : subd9_1 [0, -5, -1] = true := by decide +kernel
theorem subd9_1_2473 : subd9_1 [0, -5, 0] = true := by decide +kernel
theorem subd9_1_2474 : subd9_1 [0, -5, 1] = true := by decide +kernel
theorem subd9_1_2475 : subd9_1 [0, -5, 2] = true := by decide +kernel
theorem subd9_1_2476 : subd9_1 [0, -5, 3] = true := by decide +kernel
theorem subd9_1_2477 : subd9_1 [0, -5, 4] = true := by decide +kernel
theorem subd9_1_2478 : subd9_1 [0, -5, 5] = true := by decide +kernel
theorem subd9_1_2479 : subd9_1 [0, -5, 6] = true := by decide +kernel
theorem subd9_1_2480 : subd9_1 [0, -5, 7] = true := by decide +kernel
theorem subd9_1_2481 : subd9_1 [0, -4, -12] = true := by decide +kernel
theorem subd9_1_2482 : subd9_1 [0, -4, -11] = true := by decide +kernel
theorem subd9_1_2483 : subd9_1 [0, -4, -10] = true := by decide +kernel
theorem subd9_1_2484 : subd9_1 [0, -4, -9] = true := by decide +kernel
theorem subd9_1_2485 : subd9_1 [0, -4, -8] = true := by decide +kernel
theorem subd9_1_2486 : subd9_1 [0, -4, -7] = true := by decide +kernel
theorem subd9_1_2487 : subd9_1 [0, -4, -6] = true := by decide +kernel
theorem subd9_1_2488 : subd9_1 [0, -4, -5] = true := by decide +kernel
theorem subd9_1_2489 : subd9_1 [0, -4, -4] = true := by decide +kernel
theorem subd9_1_2490 : subd9_1 [0, -4, -3] = true := by decide +kernel
theorem subd9_1_2491 : subd9_1 [0, -4, -2] = true := by decide +kernel
theorem subd9_1_2492 : subd9_1 [0, -4, -1] = true := by decide +kernel
theorem subd9_1_2493 : subd9_1 [0, -4, 0] = true := by decide +kernel
theorem subd9_1_2494 : subd9_1 [0, -4, 1] = true := by decide +kernel
theorem subd9_1_2495 : subd9_1 [0, -4, 2] = true := by decide +kernel
theorem sbd9_1_77 : ∀ q ∈ blkd9_1_77, subd9_1 q = true := by
  unfold blkd9_1_77
  exact List.forall_mem_cons.2 ⟨subd9_1_2464, List.forall_mem_cons.2 ⟨subd9_1_2465, List.forall_mem_cons.2 ⟨subd9_1_2466, List.forall_mem_cons.2 ⟨subd9_1_2467, List.forall_mem_cons.2 ⟨subd9_1_2468, List.forall_mem_cons.2 ⟨subd9_1_2469, List.forall_mem_cons.2 ⟨subd9_1_2470, List.forall_mem_cons.2 ⟨subd9_1_2471, List.forall_mem_cons.2 ⟨subd9_1_2472, List.forall_mem_cons.2 ⟨subd9_1_2473, List.forall_mem_cons.2 ⟨subd9_1_2474, List.forall_mem_cons.2 ⟨subd9_1_2475, List.forall_mem_cons.2 ⟨subd9_1_2476, List.forall_mem_cons.2 ⟨subd9_1_2477, List.forall_mem_cons.2 ⟨subd9_1_2478, List.forall_mem_cons.2 ⟨subd9_1_2479, List.forall_mem_cons.2 ⟨subd9_1_2480, List.forall_mem_cons.2 ⟨subd9_1_2481, List.forall_mem_cons.2 ⟨subd9_1_2482, List.forall_mem_cons.2 ⟨subd9_1_2483, List.forall_mem_cons.2 ⟨subd9_1_2484, List.forall_mem_cons.2 ⟨subd9_1_2485, List.forall_mem_cons.2 ⟨subd9_1_2486, List.forall_mem_cons.2 ⟨subd9_1_2487, List.forall_mem_cons.2 ⟨subd9_1_2488, List.forall_mem_cons.2 ⟨subd9_1_2489, List.forall_mem_cons.2 ⟨subd9_1_2490, List.forall_mem_cons.2 ⟨subd9_1_2491, List.forall_mem_cons.2 ⟨subd9_1_2492, List.forall_mem_cons.2 ⟨subd9_1_2493, List.forall_mem_cons.2 ⟨subd9_1_2494, List.forall_mem_cons.2 ⟨subd9_1_2495, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_2496 : subd9_1 [0, -4, 3] = true := by decide +kernel
theorem subd9_1_2497 : subd9_1 [0, -4, 4] = true := by decide +kernel
theorem subd9_1_2498 : subd9_1 [0, -4, 5] = true := by decide +kernel
theorem subd9_1_2499 : subd9_1 [0, -4, 6] = true := by decide +kernel
theorem subd9_1_2500 : subd9_1 [0, -4, 7] = true := by decide +kernel
theorem subd9_1_2501 : subd9_1 [0, -3, -12] = true := by decide +kernel
theorem subd9_1_2502 : subd9_1 [0, -3, -11] = true := by decide +kernel
theorem subd9_1_2503 : subd9_1 [0, -3, -10] = true := by decide +kernel
theorem subd9_1_2504 : subd9_1 [0, -3, -9] = true := by decide +kernel
theorem subd9_1_2505 : subd9_1 [0, -3, -8] = true := by decide +kernel
theorem subd9_1_2506 : subd9_1 [0, -3, -7] = true := by decide +kernel
theorem subd9_1_2507 : subd9_1 [0, -3, -6] = true := by decide +kernel
theorem subd9_1_2508 : subd9_1 [0, -3, -5] = true := by decide +kernel
theorem subd9_1_2509 : subd9_1 [0, -3, -4] = true := by decide +kernel
theorem subd9_1_2510 : subd9_1 [0, -3, -3] = true := by decide +kernel
theorem subd9_1_2511 : subd9_1 [0, -3, -2] = true := by decide +kernel
theorem subd9_1_2512 : subd9_1 [0, -3, -1] = true := by decide +kernel
theorem subd9_1_2513 : subd9_1 [0, -3, 0] = true := by decide +kernel
theorem subd9_1_2514 : subd9_1 [0, -3, 1] = true := by decide +kernel
theorem subd9_1_2515 : subd9_1 [0, -3, 2] = true := by decide +kernel
theorem subd9_1_2516 : subd9_1 [0, -3, 3] = true := by decide +kernel
theorem subd9_1_2517 : subd9_1 [0, -3, 4] = true := by decide +kernel
theorem subd9_1_2518 : subd9_1 [0, -3, 5] = true := by decide +kernel
theorem subd9_1_2519 : subd9_1 [0, -3, 6] = true := by decide +kernel
theorem subd9_1_2520 : subd9_1 [0, -3, 7] = true := by decide +kernel
theorem subd9_1_2521 : subd9_1 [0, -3, 8] = true := by decide +kernel
theorem subd9_1_2522 : subd9_1 [0, -2, -11] = true := by decide +kernel
theorem subd9_1_2523 : subd9_1 [0, -2, -10] = true := by decide +kernel
theorem subd9_1_2524 : subd9_1 [0, -2, -9] = true := by decide +kernel
theorem subd9_1_2525 : subd9_1 [0, -2, -8] = true := by decide +kernel
theorem subd9_1_2526 : subd9_1 [0, -2, -7] = true := by decide +kernel
theorem subd9_1_2527 : subd9_1 [0, -2, -6] = true := by decide +kernel
theorem sbd9_1_78 : ∀ q ∈ blkd9_1_78, subd9_1 q = true := by
  unfold blkd9_1_78
  exact List.forall_mem_cons.2 ⟨subd9_1_2496, List.forall_mem_cons.2 ⟨subd9_1_2497, List.forall_mem_cons.2 ⟨subd9_1_2498, List.forall_mem_cons.2 ⟨subd9_1_2499, List.forall_mem_cons.2 ⟨subd9_1_2500, List.forall_mem_cons.2 ⟨subd9_1_2501, List.forall_mem_cons.2 ⟨subd9_1_2502, List.forall_mem_cons.2 ⟨subd9_1_2503, List.forall_mem_cons.2 ⟨subd9_1_2504, List.forall_mem_cons.2 ⟨subd9_1_2505, List.forall_mem_cons.2 ⟨subd9_1_2506, List.forall_mem_cons.2 ⟨subd9_1_2507, List.forall_mem_cons.2 ⟨subd9_1_2508, List.forall_mem_cons.2 ⟨subd9_1_2509, List.forall_mem_cons.2 ⟨subd9_1_2510, List.forall_mem_cons.2 ⟨subd9_1_2511, List.forall_mem_cons.2 ⟨subd9_1_2512, List.forall_mem_cons.2 ⟨subd9_1_2513, List.forall_mem_cons.2 ⟨subd9_1_2514, List.forall_mem_cons.2 ⟨subd9_1_2515, List.forall_mem_cons.2 ⟨subd9_1_2516, List.forall_mem_cons.2 ⟨subd9_1_2517, List.forall_mem_cons.2 ⟨subd9_1_2518, List.forall_mem_cons.2 ⟨subd9_1_2519, List.forall_mem_cons.2 ⟨subd9_1_2520, List.forall_mem_cons.2 ⟨subd9_1_2521, List.forall_mem_cons.2 ⟨subd9_1_2522, List.forall_mem_cons.2 ⟨subd9_1_2523, List.forall_mem_cons.2 ⟨subd9_1_2524, List.forall_mem_cons.2 ⟨subd9_1_2525, List.forall_mem_cons.2 ⟨subd9_1_2526, List.forall_mem_cons.2 ⟨subd9_1_2527, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_2528 : subd9_1 [0, -2, -5] = true := by decide +kernel
theorem subd9_1_2529 : subd9_1 [0, -2, -4] = true := by decide +kernel
theorem subd9_1_2530 : subd9_1 [0, -2, -3] = true := by decide +kernel
theorem subd9_1_2531 : subd9_1 [0, -2, -2] = true := by decide +kernel
theorem subd9_1_2532 : subd9_1 [0, -2, -1] = true := by decide +kernel
theorem subd9_1_2533 : subd9_1 [0, -2, 0] = true := by decide +kernel
theorem subd9_1_2534 : subd9_1 [0, -2, 1] = true := by decide +kernel
theorem subd9_1_2535 : subd9_1 [0, -2, 2] = true := by decide +kernel
theorem subd9_1_2536 : subd9_1 [0, -2, 3] = true := by decide +kernel
theorem subd9_1_2537 : subd9_1 [0, -2, 4] = true := by decide +kernel
theorem subd9_1_2538 : subd9_1 [0, -2, 5] = true := by decide +kernel
theorem subd9_1_2539 : subd9_1 [0, -2, 6] = true := by decide +kernel
theorem subd9_1_2540 : subd9_1 [0, -2, 7] = true := by decide +kernel
theorem subd9_1_2541 : subd9_1 [0, -2, 8] = true := by decide +kernel
theorem subd9_1_2542 : subd9_1 [0, -2, 9] = true := by decide +kernel
theorem subd9_1_2543 : subd9_1 [0, -1, -11] = true := by decide +kernel
theorem subd9_1_2544 : subd9_1 [0, -1, -10] = true := by decide +kernel
theorem subd9_1_2545 : subd9_1 [0, -1, -9] = true := by decide +kernel
theorem subd9_1_2546 : subd9_1 [0, -1, -8] = true := by decide +kernel
theorem subd9_1_2547 : subd9_1 [0, -1, -7] = true := by decide +kernel
theorem subd9_1_2548 : subd9_1 [0, -1, -6] = true := by decide +kernel
theorem subd9_1_2549 : subd9_1 [0, -1, -5] = true := by decide +kernel
theorem subd9_1_2550 : subd9_1 [0, -1, -4] = true := by decide +kernel
theorem subd9_1_2551 : subd9_1 [0, -1, -3] = true := by decide +kernel
theorem subd9_1_2552 : subd9_1 [0, -1, -2] = true := by decide +kernel
theorem subd9_1_2553 : subd9_1 [0, -1, -1] = true := by decide +kernel
theorem subd9_1_2554 : subd9_1 [0, -1, 0] = true := by decide +kernel
theorem subd9_1_2555 : subd9_1 [0, -1, 1] = true := by decide +kernel
theorem subd9_1_2556 : subd9_1 [0, -1, 2] = true := by decide +kernel
theorem subd9_1_2557 : subd9_1 [0, -1, 3] = true := by decide +kernel
theorem subd9_1_2558 : subd9_1 [0, -1, 4] = true := by decide +kernel
theorem subd9_1_2559 : subd9_1 [0, -1, 5] = true := by decide +kernel
theorem sbd9_1_79 : ∀ q ∈ blkd9_1_79, subd9_1 q = true := by
  unfold blkd9_1_79
  exact List.forall_mem_cons.2 ⟨subd9_1_2528, List.forall_mem_cons.2 ⟨subd9_1_2529, List.forall_mem_cons.2 ⟨subd9_1_2530, List.forall_mem_cons.2 ⟨subd9_1_2531, List.forall_mem_cons.2 ⟨subd9_1_2532, List.forall_mem_cons.2 ⟨subd9_1_2533, List.forall_mem_cons.2 ⟨subd9_1_2534, List.forall_mem_cons.2 ⟨subd9_1_2535, List.forall_mem_cons.2 ⟨subd9_1_2536, List.forall_mem_cons.2 ⟨subd9_1_2537, List.forall_mem_cons.2 ⟨subd9_1_2538, List.forall_mem_cons.2 ⟨subd9_1_2539, List.forall_mem_cons.2 ⟨subd9_1_2540, List.forall_mem_cons.2 ⟨subd9_1_2541, List.forall_mem_cons.2 ⟨subd9_1_2542, List.forall_mem_cons.2 ⟨subd9_1_2543, List.forall_mem_cons.2 ⟨subd9_1_2544, List.forall_mem_cons.2 ⟨subd9_1_2545, List.forall_mem_cons.2 ⟨subd9_1_2546, List.forall_mem_cons.2 ⟨subd9_1_2547, List.forall_mem_cons.2 ⟨subd9_1_2548, List.forall_mem_cons.2 ⟨subd9_1_2549, List.forall_mem_cons.2 ⟨subd9_1_2550, List.forall_mem_cons.2 ⟨subd9_1_2551, List.forall_mem_cons.2 ⟨subd9_1_2552, List.forall_mem_cons.2 ⟨subd9_1_2553, List.forall_mem_cons.2 ⟨subd9_1_2554, List.forall_mem_cons.2 ⟨subd9_1_2555, List.forall_mem_cons.2 ⟨subd9_1_2556, List.forall_mem_cons.2 ⟨subd9_1_2557, List.forall_mem_cons.2 ⟨subd9_1_2558, List.forall_mem_cons.2 ⟨subd9_1_2559, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_2560 : subd9_1 [0, -1, 6] = true := by decide +kernel
theorem subd9_1_2561 : subd9_1 [0, -1, 7] = true := by decide +kernel
theorem subd9_1_2562 : subd9_1 [0, -1, 8] = true := by decide +kernel
theorem subd9_1_2563 : subd9_1 [0, -1, 9] = true := by decide +kernel
theorem subd9_1_2564 : subd9_1 [0, 0, -11] = true := by decide +kernel
theorem subd9_1_2565 : subd9_1 [0, 0, -10] = true := by decide +kernel
theorem subd9_1_2566 : subd9_1 [0, 0, -9] = true := by decide +kernel
theorem subd9_1_2567 : subd9_1 [0, 0, -8] = true := by decide +kernel
theorem subd9_1_2568 : subd9_1 [0, 0, -7] = true := by decide +kernel
theorem subd9_1_2569 : subd9_1 [0, 0, -6] = true := by decide +kernel
theorem subd9_1_2570 : subd9_1 [0, 0, -5] = true := by decide +kernel
theorem subd9_1_2571 : subd9_1 [0, 0, -4] = true := by decide +kernel
theorem subd9_1_2572 : subd9_1 [0, 0, -3] = true := by decide +kernel
theorem subd9_1_2573 : subd9_1 [0, 0, -2] = true := by decide +kernel
theorem subd9_1_2574 : subd9_1 [0, 0, -1] = true := by decide +kernel
theorem subd9_1_2575 : subd9_1 [0, 0, 0] = true := by decide +kernel
theorem subd9_1_2576 : subd9_1 [0, 0, 1] = true := by decide +kernel
theorem subd9_1_2577 : subd9_1 [0, 0, 2] = true := by decide +kernel
theorem subd9_1_2578 : subd9_1 [0, 0, 3] = true := by decide +kernel
theorem subd9_1_2579 : subd9_1 [0, 0, 4] = true := by decide +kernel
theorem subd9_1_2580 : subd9_1 [0, 0, 5] = true := by decide +kernel
theorem subd9_1_2581 : subd9_1 [0, 0, 6] = true := by decide +kernel
theorem subd9_1_2582 : subd9_1 [0, 0, 7] = true := by decide +kernel
theorem subd9_1_2583 : subd9_1 [0, 0, 8] = true := by decide +kernel
theorem subd9_1_2584 : subd9_1 [0, 0, 9] = true := by decide +kernel
theorem subd9_1_2585 : subd9_1 [0, 0, 10] = true := by decide +kernel
theorem subd9_1_2586 : subd9_1 [0, 1, -10] = true := by decide +kernel
theorem subd9_1_2587 : subd9_1 [0, 1, -9] = true := by decide +kernel
theorem subd9_1_2588 : subd9_1 [0, 1, -8] = true := by decide +kernel
theorem subd9_1_2589 : subd9_1 [0, 1, -7] = true := by decide +kernel
theorem subd9_1_2590 : subd9_1 [0, 1, -6] = true := by decide +kernel
theorem subd9_1_2591 : subd9_1 [0, 1, -5] = true := by decide +kernel
theorem sbd9_1_80 : ∀ q ∈ blkd9_1_80, subd9_1 q = true := by
  unfold blkd9_1_80
  exact List.forall_mem_cons.2 ⟨subd9_1_2560, List.forall_mem_cons.2 ⟨subd9_1_2561, List.forall_mem_cons.2 ⟨subd9_1_2562, List.forall_mem_cons.2 ⟨subd9_1_2563, List.forall_mem_cons.2 ⟨subd9_1_2564, List.forall_mem_cons.2 ⟨subd9_1_2565, List.forall_mem_cons.2 ⟨subd9_1_2566, List.forall_mem_cons.2 ⟨subd9_1_2567, List.forall_mem_cons.2 ⟨subd9_1_2568, List.forall_mem_cons.2 ⟨subd9_1_2569, List.forall_mem_cons.2 ⟨subd9_1_2570, List.forall_mem_cons.2 ⟨subd9_1_2571, List.forall_mem_cons.2 ⟨subd9_1_2572, List.forall_mem_cons.2 ⟨subd9_1_2573, List.forall_mem_cons.2 ⟨subd9_1_2574, List.forall_mem_cons.2 ⟨subd9_1_2575, List.forall_mem_cons.2 ⟨subd9_1_2576, List.forall_mem_cons.2 ⟨subd9_1_2577, List.forall_mem_cons.2 ⟨subd9_1_2578, List.forall_mem_cons.2 ⟨subd9_1_2579, List.forall_mem_cons.2 ⟨subd9_1_2580, List.forall_mem_cons.2 ⟨subd9_1_2581, List.forall_mem_cons.2 ⟨subd9_1_2582, List.forall_mem_cons.2 ⟨subd9_1_2583, List.forall_mem_cons.2 ⟨subd9_1_2584, List.forall_mem_cons.2 ⟨subd9_1_2585, List.forall_mem_cons.2 ⟨subd9_1_2586, List.forall_mem_cons.2 ⟨subd9_1_2587, List.forall_mem_cons.2 ⟨subd9_1_2588, List.forall_mem_cons.2 ⟨subd9_1_2589, List.forall_mem_cons.2 ⟨subd9_1_2590, List.forall_mem_cons.2 ⟨subd9_1_2591, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_2592 : subd9_1 [0, 1, -4] = true := by decide +kernel
theorem subd9_1_2593 : subd9_1 [0, 1, -3] = true := by decide +kernel
theorem subd9_1_2594 : subd9_1 [0, 1, -2] = true := by decide +kernel
theorem subd9_1_2595 : subd9_1 [0, 1, -1] = true := by decide +kernel
theorem subd9_1_2596 : subd9_1 [0, 1, 0] = true := by decide +kernel
theorem subd9_1_2597 : subd9_1 [0, 1, 1] = true := by decide +kernel
theorem subd9_1_2598 : subd9_1 [0, 1, 2] = true := by decide +kernel
theorem subd9_1_2599 : subd9_1 [0, 1, 3] = true := by decide +kernel
theorem subd9_1_2600 : subd9_1 [0, 1, 4] = true := by decide +kernel
theorem subd9_1_2601 : subd9_1 [0, 1, 5] = true := by decide +kernel
theorem subd9_1_2602 : subd9_1 [0, 1, 6] = true := by decide +kernel
theorem subd9_1_2603 : subd9_1 [0, 1, 7] = true := by decide +kernel
theorem subd9_1_2604 : subd9_1 [0, 1, 8] = true := by decide +kernel
theorem subd9_1_2605 : subd9_1 [0, 1, 9] = true := by decide +kernel
theorem subd9_1_2606 : subd9_1 [0, 1, 10] = true := by decide +kernel
theorem subd9_1_2607 : subd9_1 [0, 2, -10] = true := by decide +kernel
theorem subd9_1_2608 : subd9_1 [0, 2, -9] = true := by decide +kernel
theorem subd9_1_2609 : subd9_1 [0, 2, -8] = true := by decide +kernel
theorem subd9_1_2610 : subd9_1 [0, 2, -7] = true := by decide +kernel
theorem subd9_1_2611 : subd9_1 [0, 2, -6] = true := by decide +kernel
theorem subd9_1_2612 : subd9_1 [0, 2, -5] = true := by decide +kernel
theorem subd9_1_2613 : subd9_1 [0, 2, -4] = true := by decide +kernel
theorem subd9_1_2614 : subd9_1 [0, 2, -3] = true := by decide +kernel
theorem subd9_1_2615 : subd9_1 [0, 2, -2] = true := by decide +kernel
theorem subd9_1_2616 : subd9_1 [0, 2, -1] = true := by decide +kernel
theorem subd9_1_2617 : subd9_1 [0, 2, 0] = true := by decide +kernel
theorem subd9_1_2618 : subd9_1 [0, 2, 1] = true := by decide +kernel
theorem subd9_1_2619 : subd9_1 [0, 2, 2] = true := by decide +kernel
theorem subd9_1_2620 : subd9_1 [0, 2, 3] = true := by decide +kernel
theorem subd9_1_2621 : subd9_1 [0, 2, 4] = true := by decide +kernel
theorem subd9_1_2622 : subd9_1 [0, 2, 5] = true := by decide +kernel
theorem subd9_1_2623 : subd9_1 [0, 2, 6] = true := by decide +kernel
theorem sbd9_1_81 : ∀ q ∈ blkd9_1_81, subd9_1 q = true := by
  unfold blkd9_1_81
  exact List.forall_mem_cons.2 ⟨subd9_1_2592, List.forall_mem_cons.2 ⟨subd9_1_2593, List.forall_mem_cons.2 ⟨subd9_1_2594, List.forall_mem_cons.2 ⟨subd9_1_2595, List.forall_mem_cons.2 ⟨subd9_1_2596, List.forall_mem_cons.2 ⟨subd9_1_2597, List.forall_mem_cons.2 ⟨subd9_1_2598, List.forall_mem_cons.2 ⟨subd9_1_2599, List.forall_mem_cons.2 ⟨subd9_1_2600, List.forall_mem_cons.2 ⟨subd9_1_2601, List.forall_mem_cons.2 ⟨subd9_1_2602, List.forall_mem_cons.2 ⟨subd9_1_2603, List.forall_mem_cons.2 ⟨subd9_1_2604, List.forall_mem_cons.2 ⟨subd9_1_2605, List.forall_mem_cons.2 ⟨subd9_1_2606, List.forall_mem_cons.2 ⟨subd9_1_2607, List.forall_mem_cons.2 ⟨subd9_1_2608, List.forall_mem_cons.2 ⟨subd9_1_2609, List.forall_mem_cons.2 ⟨subd9_1_2610, List.forall_mem_cons.2 ⟨subd9_1_2611, List.forall_mem_cons.2 ⟨subd9_1_2612, List.forall_mem_cons.2 ⟨subd9_1_2613, List.forall_mem_cons.2 ⟨subd9_1_2614, List.forall_mem_cons.2 ⟨subd9_1_2615, List.forall_mem_cons.2 ⟨subd9_1_2616, List.forall_mem_cons.2 ⟨subd9_1_2617, List.forall_mem_cons.2 ⟨subd9_1_2618, List.forall_mem_cons.2 ⟨subd9_1_2619, List.forall_mem_cons.2 ⟨subd9_1_2620, List.forall_mem_cons.2 ⟨subd9_1_2621, List.forall_mem_cons.2 ⟨subd9_1_2622, List.forall_mem_cons.2 ⟨subd9_1_2623, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_2624 : subd9_1 [0, 2, 7] = true := by decide +kernel
theorem subd9_1_2625 : subd9_1 [0, 2, 8] = true := by decide +kernel
theorem subd9_1_2626 : subd9_1 [0, 2, 9] = true := by decide +kernel
theorem subd9_1_2627 : subd9_1 [0, 2, 10] = true := by decide +kernel
theorem subd9_1_2628 : subd9_1 [0, 3, -9] = true := by decide +kernel
theorem subd9_1_2629 : subd9_1 [0, 3, -8] = true := by decide +kernel
theorem subd9_1_2630 : subd9_1 [0, 3, -7] = true := by decide +kernel
theorem subd9_1_2631 : subd9_1 [0, 3, -6] = true := by decide +kernel
theorem subd9_1_2632 : subd9_1 [0, 3, -5] = true := by decide +kernel
theorem subd9_1_2633 : subd9_1 [0, 3, -4] = true := by decide +kernel
theorem subd9_1_2634 : subd9_1 [0, 3, -3] = true := by decide +kernel
theorem subd9_1_2635 : subd9_1 [0, 3, -2] = true := by decide +kernel
theorem subd9_1_2636 : subd9_1 [0, 3, -1] = true := by decide +kernel
theorem subd9_1_2637 : subd9_1 [0, 3, 0] = true := by decide +kernel
theorem subd9_1_2638 : subd9_1 [0, 3, 1] = true := by decide +kernel
theorem subd9_1_2639 : subd9_1 [0, 3, 2] = true := by decide +kernel
theorem subd9_1_2640 : subd9_1 [0, 3, 3] = true := by decide +kernel
theorem subd9_1_2641 : subd9_1 [0, 3, 4] = true := by decide +kernel
theorem subd9_1_2642 : subd9_1 [0, 3, 5] = true := by decide +kernel
theorem subd9_1_2643 : subd9_1 [0, 3, 6] = true := by decide +kernel
theorem subd9_1_2644 : subd9_1 [0, 3, 7] = true := by decide +kernel
theorem subd9_1_2645 : subd9_1 [0, 3, 8] = true := by decide +kernel
theorem subd9_1_2646 : subd9_1 [0, 3, 9] = true := by decide +kernel
theorem subd9_1_2647 : subd9_1 [0, 3, 10] = true := by decide +kernel
theorem subd9_1_2648 : subd9_1 [0, 3, 11] = true := by decide +kernel
theorem subd9_1_2649 : subd9_1 [0, 4, -8] = true := by decide +kernel
theorem subd9_1_2650 : subd9_1 [0, 4, -7] = true := by decide +kernel
theorem subd9_1_2651 : subd9_1 [0, 4, -6] = true := by decide +kernel
theorem subd9_1_2652 : subd9_1 [0, 4, -5] = true := by decide +kernel
theorem subd9_1_2653 : subd9_1 [0, 4, -4] = true := by decide +kernel
theorem subd9_1_2654 : subd9_1 [0, 4, -3] = true := by decide +kernel
theorem subd9_1_2655 : subd9_1 [0, 4, -2] = true := by decide +kernel
theorem sbd9_1_82 : ∀ q ∈ blkd9_1_82, subd9_1 q = true := by
  unfold blkd9_1_82
  exact List.forall_mem_cons.2 ⟨subd9_1_2624, List.forall_mem_cons.2 ⟨subd9_1_2625, List.forall_mem_cons.2 ⟨subd9_1_2626, List.forall_mem_cons.2 ⟨subd9_1_2627, List.forall_mem_cons.2 ⟨subd9_1_2628, List.forall_mem_cons.2 ⟨subd9_1_2629, List.forall_mem_cons.2 ⟨subd9_1_2630, List.forall_mem_cons.2 ⟨subd9_1_2631, List.forall_mem_cons.2 ⟨subd9_1_2632, List.forall_mem_cons.2 ⟨subd9_1_2633, List.forall_mem_cons.2 ⟨subd9_1_2634, List.forall_mem_cons.2 ⟨subd9_1_2635, List.forall_mem_cons.2 ⟨subd9_1_2636, List.forall_mem_cons.2 ⟨subd9_1_2637, List.forall_mem_cons.2 ⟨subd9_1_2638, List.forall_mem_cons.2 ⟨subd9_1_2639, List.forall_mem_cons.2 ⟨subd9_1_2640, List.forall_mem_cons.2 ⟨subd9_1_2641, List.forall_mem_cons.2 ⟨subd9_1_2642, List.forall_mem_cons.2 ⟨subd9_1_2643, List.forall_mem_cons.2 ⟨subd9_1_2644, List.forall_mem_cons.2 ⟨subd9_1_2645, List.forall_mem_cons.2 ⟨subd9_1_2646, List.forall_mem_cons.2 ⟨subd9_1_2647, List.forall_mem_cons.2 ⟨subd9_1_2648, List.forall_mem_cons.2 ⟨subd9_1_2649, List.forall_mem_cons.2 ⟨subd9_1_2650, List.forall_mem_cons.2 ⟨subd9_1_2651, List.forall_mem_cons.2 ⟨subd9_1_2652, List.forall_mem_cons.2 ⟨subd9_1_2653, List.forall_mem_cons.2 ⟨subd9_1_2654, List.forall_mem_cons.2 ⟨subd9_1_2655, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_2656 : subd9_1 [0, 4, -1] = true := by decide +kernel
theorem subd9_1_2657 : subd9_1 [0, 4, 0] = true := by decide +kernel
theorem subd9_1_2658 : subd9_1 [0, 4, 1] = true := by decide +kernel
theorem subd9_1_2659 : subd9_1 [0, 4, 2] = true := by decide +kernel
theorem subd9_1_2660 : subd9_1 [0, 4, 3] = true := by decide +kernel
theorem subd9_1_2661 : subd9_1 [0, 4, 4] = true := by decide +kernel
theorem subd9_1_2662 : subd9_1 [0, 4, 5] = true := by decide +kernel
theorem subd9_1_2663 : subd9_1 [0, 4, 6] = true := by decide +kernel
theorem subd9_1_2664 : subd9_1 [0, 4, 7] = true := by decide +kernel
theorem subd9_1_2665 : subd9_1 [0, 4, 8] = true := by decide +kernel
theorem subd9_1_2666 : subd9_1 [0, 4, 9] = true := by decide +kernel
theorem subd9_1_2667 : subd9_1 [0, 4, 10] = true := by decide +kernel
theorem subd9_1_2668 : subd9_1 [0, 4, 11] = true := by decide +kernel
theorem subd9_1_2669 : subd9_1 [0, 5, -8] = true := by decide +kernel
theorem subd9_1_2670 : subd9_1 [0, 5, -7] = true := by decide +kernel
theorem subd9_1_2671 : subd9_1 [0, 5, -6] = true := by decide +kernel
theorem subd9_1_2672 : subd9_1 [0, 5, -5] = true := by decide +kernel
theorem subd9_1_2673 : subd9_1 [0, 5, -4] = true := by decide +kernel
theorem subd9_1_2674 : subd9_1 [0, 5, -3] = true := by decide +kernel
theorem subd9_1_2675 : subd9_1 [0, 5, -2] = true := by decide +kernel
theorem subd9_1_2676 : subd9_1 [0, 5, -1] = true := by decide +kernel
theorem subd9_1_2677 : subd9_1 [0, 5, 0] = true := by decide +kernel
theorem subd9_1_2678 : subd9_1 [0, 5, 1] = true := by decide +kernel
theorem subd9_1_2679 : subd9_1 [0, 5, 2] = true := by decide +kernel
theorem subd9_1_2680 : subd9_1 [0, 5, 3] = true := by decide +kernel
theorem subd9_1_2681 : subd9_1 [0, 5, 4] = true := by decide +kernel
theorem subd9_1_2682 : subd9_1 [0, 5, 5] = true := by decide +kernel
theorem subd9_1_2683 : subd9_1 [0, 5, 6] = true := by decide +kernel
theorem subd9_1_2684 : subd9_1 [0, 5, 7] = true := by decide +kernel
theorem subd9_1_2685 : subd9_1 [0, 5, 8] = true := by decide +kernel
theorem subd9_1_2686 : subd9_1 [0, 5, 9] = true := by decide +kernel
theorem subd9_1_2687 : subd9_1 [0, 5, 10] = true := by decide +kernel
theorem sbd9_1_83 : ∀ q ∈ blkd9_1_83, subd9_1 q = true := by
  unfold blkd9_1_83
  exact List.forall_mem_cons.2 ⟨subd9_1_2656, List.forall_mem_cons.2 ⟨subd9_1_2657, List.forall_mem_cons.2 ⟨subd9_1_2658, List.forall_mem_cons.2 ⟨subd9_1_2659, List.forall_mem_cons.2 ⟨subd9_1_2660, List.forall_mem_cons.2 ⟨subd9_1_2661, List.forall_mem_cons.2 ⟨subd9_1_2662, List.forall_mem_cons.2 ⟨subd9_1_2663, List.forall_mem_cons.2 ⟨subd9_1_2664, List.forall_mem_cons.2 ⟨subd9_1_2665, List.forall_mem_cons.2 ⟨subd9_1_2666, List.forall_mem_cons.2 ⟨subd9_1_2667, List.forall_mem_cons.2 ⟨subd9_1_2668, List.forall_mem_cons.2 ⟨subd9_1_2669, List.forall_mem_cons.2 ⟨subd9_1_2670, List.forall_mem_cons.2 ⟨subd9_1_2671, List.forall_mem_cons.2 ⟨subd9_1_2672, List.forall_mem_cons.2 ⟨subd9_1_2673, List.forall_mem_cons.2 ⟨subd9_1_2674, List.forall_mem_cons.2 ⟨subd9_1_2675, List.forall_mem_cons.2 ⟨subd9_1_2676, List.forall_mem_cons.2 ⟨subd9_1_2677, List.forall_mem_cons.2 ⟨subd9_1_2678, List.forall_mem_cons.2 ⟨subd9_1_2679, List.forall_mem_cons.2 ⟨subd9_1_2680, List.forall_mem_cons.2 ⟨subd9_1_2681, List.forall_mem_cons.2 ⟨subd9_1_2682, List.forall_mem_cons.2 ⟨subd9_1_2683, List.forall_mem_cons.2 ⟨subd9_1_2684, List.forall_mem_cons.2 ⟨subd9_1_2685, List.forall_mem_cons.2 ⟨subd9_1_2686, List.forall_mem_cons.2 ⟨subd9_1_2687, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_2688 : subd9_1 [0, 5, 11] = true := by decide +kernel
theorem subd9_1_2689 : subd9_1 [0, 6, -7] = true := by decide +kernel
theorem subd9_1_2690 : subd9_1 [0, 6, -6] = true := by decide +kernel
theorem subd9_1_2691 : subd9_1 [0, 6, -5] = true := by decide +kernel
theorem subd9_1_2692 : subd9_1 [0, 6, -4] = true := by decide +kernel
theorem subd9_1_2693 : subd9_1 [0, 6, -3] = true := by decide +kernel
theorem subd9_1_2694 : subd9_1 [0, 6, -2] = true := by decide +kernel
theorem subd9_1_2695 : subd9_1 [0, 6, -1] = true := by decide +kernel
theorem subd9_1_2696 : subd9_1 [0, 6, 0] = true := by decide +kernel
theorem subd9_1_2697 : subd9_1 [0, 6, 1] = true := by decide +kernel
theorem subd9_1_2698 : subd9_1 [0, 6, 2] = true := by decide +kernel
theorem subd9_1_2699 : subd9_1 [0, 6, 3] = true := by decide +kernel
theorem subd9_1_2700 : subd9_1 [0, 6, 4] = true := by decide +kernel
theorem subd9_1_2701 : subd9_1 [0, 6, 5] = true := by decide +kernel
theorem subd9_1_2702 : subd9_1 [0, 6, 6] = true := by decide +kernel
theorem subd9_1_2703 : subd9_1 [0, 6, 7] = true := by decide +kernel
theorem subd9_1_2704 : subd9_1 [0, 6, 8] = true := by decide +kernel
theorem subd9_1_2705 : subd9_1 [0, 6, 9] = true := by decide +kernel
theorem subd9_1_2706 : subd9_1 [0, 6, 10] = true := by decide +kernel
theorem subd9_1_2707 : subd9_1 [0, 6, 11] = true := by decide +kernel
theorem subd9_1_2708 : subd9_1 [0, 7, -6] = true := by decide +kernel
theorem subd9_1_2709 : subd9_1 [0, 7, -5] = true := by decide +kernel
theorem subd9_1_2710 : subd9_1 [0, 7, -4] = true := by decide +kernel
theorem subd9_1_2711 : subd9_1 [0, 7, -3] = true := by decide +kernel
theorem subd9_1_2712 : subd9_1 [0, 7, -2] = true := by decide +kernel
theorem subd9_1_2713 : subd9_1 [0, 7, -1] = true := by decide +kernel
theorem subd9_1_2714 : subd9_1 [0, 7, 0] = true := by decide +kernel
theorem subd9_1_2715 : subd9_1 [0, 7, 1] = true := by decide +kernel
theorem subd9_1_2716 : subd9_1 [0, 7, 2] = true := by decide +kernel
theorem subd9_1_2717 : subd9_1 [0, 7, 3] = true := by decide +kernel
theorem subd9_1_2718 : subd9_1 [0, 7, 4] = true := by decide +kernel
theorem subd9_1_2719 : subd9_1 [0, 7, 5] = true := by decide +kernel
theorem sbd9_1_84 : ∀ q ∈ blkd9_1_84, subd9_1 q = true := by
  unfold blkd9_1_84
  exact List.forall_mem_cons.2 ⟨subd9_1_2688, List.forall_mem_cons.2 ⟨subd9_1_2689, List.forall_mem_cons.2 ⟨subd9_1_2690, List.forall_mem_cons.2 ⟨subd9_1_2691, List.forall_mem_cons.2 ⟨subd9_1_2692, List.forall_mem_cons.2 ⟨subd9_1_2693, List.forall_mem_cons.2 ⟨subd9_1_2694, List.forall_mem_cons.2 ⟨subd9_1_2695, List.forall_mem_cons.2 ⟨subd9_1_2696, List.forall_mem_cons.2 ⟨subd9_1_2697, List.forall_mem_cons.2 ⟨subd9_1_2698, List.forall_mem_cons.2 ⟨subd9_1_2699, List.forall_mem_cons.2 ⟨subd9_1_2700, List.forall_mem_cons.2 ⟨subd9_1_2701, List.forall_mem_cons.2 ⟨subd9_1_2702, List.forall_mem_cons.2 ⟨subd9_1_2703, List.forall_mem_cons.2 ⟨subd9_1_2704, List.forall_mem_cons.2 ⟨subd9_1_2705, List.forall_mem_cons.2 ⟨subd9_1_2706, List.forall_mem_cons.2 ⟨subd9_1_2707, List.forall_mem_cons.2 ⟨subd9_1_2708, List.forall_mem_cons.2 ⟨subd9_1_2709, List.forall_mem_cons.2 ⟨subd9_1_2710, List.forall_mem_cons.2 ⟨subd9_1_2711, List.forall_mem_cons.2 ⟨subd9_1_2712, List.forall_mem_cons.2 ⟨subd9_1_2713, List.forall_mem_cons.2 ⟨subd9_1_2714, List.forall_mem_cons.2 ⟨subd9_1_2715, List.forall_mem_cons.2 ⟨subd9_1_2716, List.forall_mem_cons.2 ⟨subd9_1_2717, List.forall_mem_cons.2 ⟨subd9_1_2718, List.forall_mem_cons.2 ⟨subd9_1_2719, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_2720 : subd9_1 [0, 7, 6] = true := by decide +kernel
theorem subd9_1_2721 : subd9_1 [0, 7, 7] = true := by decide +kernel
theorem subd9_1_2722 : subd9_1 [0, 7, 8] = true := by decide +kernel
theorem subd9_1_2723 : subd9_1 [0, 7, 9] = true := by decide +kernel
theorem subd9_1_2724 : subd9_1 [0, 7, 10] = true := by decide +kernel
theorem subd9_1_2725 : subd9_1 [0, 7, 11] = true := by decide +kernel
theorem subd9_1_2726 : subd9_1 [0, 8, -5] = true := by decide +kernel
theorem subd9_1_2727 : subd9_1 [0, 8, -4] = true := by decide +kernel
theorem subd9_1_2728 : subd9_1 [0, 8, -3] = true := by decide +kernel
theorem subd9_1_2729 : subd9_1 [0, 8, -2] = true := by decide +kernel
theorem subd9_1_2730 : subd9_1 [0, 8, -1] = true := by decide +kernel
theorem subd9_1_2731 : subd9_1 [0, 8, 0] = true := by decide +kernel
theorem subd9_1_2732 : subd9_1 [0, 8, 1] = true := by decide +kernel
theorem subd9_1_2733 : subd9_1 [0, 8, 2] = true := by decide +kernel
theorem subd9_1_2734 : subd9_1 [0, 8, 3] = true := by decide +kernel
theorem subd9_1_2735 : subd9_1 [0, 8, 4] = true := by decide +kernel
theorem subd9_1_2736 : subd9_1 [0, 8, 5] = true := by decide +kernel
theorem subd9_1_2737 : subd9_1 [0, 8, 6] = true := by decide +kernel
theorem subd9_1_2738 : subd9_1 [0, 8, 7] = true := by decide +kernel
theorem subd9_1_2739 : subd9_1 [0, 8, 8] = true := by decide +kernel
theorem subd9_1_2740 : subd9_1 [0, 8, 9] = true := by decide +kernel
theorem subd9_1_2741 : subd9_1 [0, 8, 10] = true := by decide +kernel
theorem subd9_1_2742 : subd9_1 [0, 8, 11] = true := by decide +kernel
theorem subd9_1_2743 : subd9_1 [0, 9, -4] = true := by decide +kernel
theorem subd9_1_2744 : subd9_1 [0, 9, -3] = true := by decide +kernel
theorem subd9_1_2745 : subd9_1 [0, 9, -2] = true := by decide +kernel
theorem subd9_1_2746 : subd9_1 [0, 9, -1] = true := by decide +kernel
theorem subd9_1_2747 : subd9_1 [0, 9, 0] = true := by decide +kernel
theorem subd9_1_2748 : subd9_1 [0, 9, 1] = true := by decide +kernel
theorem subd9_1_2749 : subd9_1 [0, 9, 2] = true := by decide +kernel
theorem subd9_1_2750 : subd9_1 [0, 9, 3] = true := by decide +kernel
theorem subd9_1_2751 : subd9_1 [0, 9, 4] = true := by decide +kernel
theorem sbd9_1_85 : ∀ q ∈ blkd9_1_85, subd9_1 q = true := by
  unfold blkd9_1_85
  exact List.forall_mem_cons.2 ⟨subd9_1_2720, List.forall_mem_cons.2 ⟨subd9_1_2721, List.forall_mem_cons.2 ⟨subd9_1_2722, List.forall_mem_cons.2 ⟨subd9_1_2723, List.forall_mem_cons.2 ⟨subd9_1_2724, List.forall_mem_cons.2 ⟨subd9_1_2725, List.forall_mem_cons.2 ⟨subd9_1_2726, List.forall_mem_cons.2 ⟨subd9_1_2727, List.forall_mem_cons.2 ⟨subd9_1_2728, List.forall_mem_cons.2 ⟨subd9_1_2729, List.forall_mem_cons.2 ⟨subd9_1_2730, List.forall_mem_cons.2 ⟨subd9_1_2731, List.forall_mem_cons.2 ⟨subd9_1_2732, List.forall_mem_cons.2 ⟨subd9_1_2733, List.forall_mem_cons.2 ⟨subd9_1_2734, List.forall_mem_cons.2 ⟨subd9_1_2735, List.forall_mem_cons.2 ⟨subd9_1_2736, List.forall_mem_cons.2 ⟨subd9_1_2737, List.forall_mem_cons.2 ⟨subd9_1_2738, List.forall_mem_cons.2 ⟨subd9_1_2739, List.forall_mem_cons.2 ⟨subd9_1_2740, List.forall_mem_cons.2 ⟨subd9_1_2741, List.forall_mem_cons.2 ⟨subd9_1_2742, List.forall_mem_cons.2 ⟨subd9_1_2743, List.forall_mem_cons.2 ⟨subd9_1_2744, List.forall_mem_cons.2 ⟨subd9_1_2745, List.forall_mem_cons.2 ⟨subd9_1_2746, List.forall_mem_cons.2 ⟨subd9_1_2747, List.forall_mem_cons.2 ⟨subd9_1_2748, List.forall_mem_cons.2 ⟨subd9_1_2749, List.forall_mem_cons.2 ⟨subd9_1_2750, List.forall_mem_cons.2 ⟨subd9_1_2751, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_2752 : subd9_1 [0, 9, 5] = true := by decide +kernel
theorem subd9_1_2753 : subd9_1 [0, 9, 6] = true := by decide +kernel
theorem subd9_1_2754 : subd9_1 [0, 9, 7] = true := by decide +kernel
theorem subd9_1_2755 : subd9_1 [0, 9, 8] = true := by decide +kernel
theorem subd9_1_2756 : subd9_1 [0, 9, 9] = true := by decide +kernel
theorem subd9_1_2757 : subd9_1 [0, 9, 10] = true := by decide +kernel
theorem subd9_1_2758 : subd9_1 [0, 10] = true := by decide +kernel
theorem subd9_1_2759 : subd9_1 [0, 11] = true := by decide +kernel
theorem subd9_1_2760 : subd9_1 [0, 12] = true := by decide +kernel
theorem subd9_1_2761 : subd9_1 [1, -12] = true := by decide +kernel
theorem subd9_1_2762 : subd9_1 [1, -11] = true := by decide +kernel
theorem subd9_1_2763 : subd9_1 [1, -10] = true := by decide +kernel
theorem subd9_1_2764 : subd9_1 [1, -9] = true := by decide +kernel
theorem subd9_1_2765 : subd9_1 [1, -8, -11] = true := by decide +kernel
theorem subd9_1_2766 : subd9_1 [1, -8, -10] = true := by decide +kernel
theorem subd9_1_2767 : subd9_1 [1, -8, -9] = true := by decide +kernel
theorem subd9_1_2768 : subd9_1 [1, -8, -8] = true := by decide +kernel
theorem subd9_1_2769 : subd9_1 [1, -8, -7] = true := by decide +kernel
theorem subd9_1_2770 : subd9_1 [1, -8, -6] = true := by decide +kernel
theorem subd9_1_2771 : subd9_1 [1, -8, -5] = true := by decide +kernel
theorem subd9_1_2772 : subd9_1 [1, -8, -4] = true := by decide +kernel
theorem subd9_1_2773 : subd9_1 [1, -8, -3] = true := by decide +kernel
theorem subd9_1_2774 : subd9_1 [1, -8, -2] = true := by decide +kernel
theorem subd9_1_2775 : subd9_1 [1, -8, -1] = true := by decide +kernel
theorem subd9_1_2776 : subd9_1 [1, -8, 0] = true := by decide +kernel
theorem subd9_1_2777 : subd9_1 [1, -8, 1] = true := by decide +kernel
theorem subd9_1_2778 : subd9_1 [1, -8, 2] = true := by decide +kernel
theorem subd9_1_2779 : subd9_1 [1, -8, 3] = true := by decide +kernel
theorem subd9_1_2780 : subd9_1 [1, -8, 4] = true := by decide +kernel
theorem subd9_1_2781 : subd9_1 [1, -7, -12] = true := by decide +kernel
theorem subd9_1_2782 : subd9_1 [1, -7, -11] = true := by decide +kernel
theorem subd9_1_2783 : subd9_1 [1, -7, -10] = true := by decide +kernel
theorem sbd9_1_86 : ∀ q ∈ blkd9_1_86, subd9_1 q = true := by
  unfold blkd9_1_86
  exact List.forall_mem_cons.2 ⟨subd9_1_2752, List.forall_mem_cons.2 ⟨subd9_1_2753, List.forall_mem_cons.2 ⟨subd9_1_2754, List.forall_mem_cons.2 ⟨subd9_1_2755, List.forall_mem_cons.2 ⟨subd9_1_2756, List.forall_mem_cons.2 ⟨subd9_1_2757, List.forall_mem_cons.2 ⟨subd9_1_2758, List.forall_mem_cons.2 ⟨subd9_1_2759, List.forall_mem_cons.2 ⟨subd9_1_2760, List.forall_mem_cons.2 ⟨subd9_1_2761, List.forall_mem_cons.2 ⟨subd9_1_2762, List.forall_mem_cons.2 ⟨subd9_1_2763, List.forall_mem_cons.2 ⟨subd9_1_2764, List.forall_mem_cons.2 ⟨subd9_1_2765, List.forall_mem_cons.2 ⟨subd9_1_2766, List.forall_mem_cons.2 ⟨subd9_1_2767, List.forall_mem_cons.2 ⟨subd9_1_2768, List.forall_mem_cons.2 ⟨subd9_1_2769, List.forall_mem_cons.2 ⟨subd9_1_2770, List.forall_mem_cons.2 ⟨subd9_1_2771, List.forall_mem_cons.2 ⟨subd9_1_2772, List.forall_mem_cons.2 ⟨subd9_1_2773, List.forall_mem_cons.2 ⟨subd9_1_2774, List.forall_mem_cons.2 ⟨subd9_1_2775, List.forall_mem_cons.2 ⟨subd9_1_2776, List.forall_mem_cons.2 ⟨subd9_1_2777, List.forall_mem_cons.2 ⟨subd9_1_2778, List.forall_mem_cons.2 ⟨subd9_1_2779, List.forall_mem_cons.2 ⟨subd9_1_2780, List.forall_mem_cons.2 ⟨subd9_1_2781, List.forall_mem_cons.2 ⟨subd9_1_2782, List.forall_mem_cons.2 ⟨subd9_1_2783, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C116
