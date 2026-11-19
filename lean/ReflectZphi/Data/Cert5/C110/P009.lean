import ReflectZphi.Data.Cert5.C110.Base

namespace ReflectZphi.Data.Cert5.C110

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_2_288 : subd6_2 [1, 0, -3] = true := by decide +kernel
theorem subd6_2_289 : subd6_2 [1, 0, -2] = true := by decide +kernel
theorem subd6_2_290 : subd6_2 [1, 0, -1] = true := by decide +kernel
theorem subd6_2_291 : subd6_2 [1, 0, 0] = true := by decide +kernel
theorem subd6_2_292 : subd6_2 [1, 0, 1] = true := by decide +kernel
theorem subd6_2_293 : subd6_2 [1, 0, 2] = true := by decide +kernel
theorem subd6_2_294 : subd6_2 [1, 0, 3] = true := by decide +kernel
theorem subd6_2_295 : subd6_2 [1, 0, 4] = true := by decide +kernel
theorem subd6_2_296 : subd6_2 [1, 0, 5] = true := by decide +kernel
theorem subd6_2_297 : subd6_2 [1, 0, 6] = true := by decide +kernel
theorem subd6_2_298 : subd6_2 [1, 0, 7] = true := by decide +kernel
theorem subd6_2_299 : subd6_2 [1, 0, 8] = true := by decide +kernel
theorem subd6_2_300 : subd6_2 [1, 1, -8] = true := by decide +kernel
theorem subd6_2_301 : subd6_2 [1, 1, -7] = true := by decide +kernel
theorem subd6_2_302 : subd6_2 [1, 1, -6] = true := by decide +kernel
theorem subd6_2_303 : subd6_2 [1, 1, -5] = true := by decide +kernel
theorem subd6_2_304 : subd6_2 [1, 1, -4] = true := by decide +kernel
theorem subd6_2_305 : subd6_2 [1, 1, -3] = true := by decide +kernel
theorem subd6_2_306 : subd6_2 [1, 1, -2] = true := by decide +kernel
theorem subd6_2_307 : subd6_2 [1, 1, -1] = true := by decide +kernel
theorem subd6_2_308 : subd6_2 [1, 1, 0] = true := by decide +kernel
theorem subd6_2_309 : subd6_2 [1, 1, 1] = true := by decide +kernel
theorem subd6_2_310 : subd6_2 [1, 1, 2] = true := by decide +kernel
theorem subd6_2_311 : subd6_2 [1, 1, 3] = true := by decide +kernel
theorem subd6_2_312 : subd6_2 [1, 1, 4] = true := by decide +kernel
theorem subd6_2_313 : subd6_2 [1, 1, 5] = true := by decide +kernel
theorem subd6_2_314 : subd6_2 [1, 1, 6] = true := by decide +kernel
theorem subd6_2_315 : subd6_2 [1, 1, 7] = true := by decide +kernel
theorem subd6_2_316 : subd6_2 [1, 1, 8] = true := by decide +kernel
theorem subd6_2_317 : subd6_2 [1, 2, -7] = true := by decide +kernel
theorem subd6_2_318 : subd6_2 [1, 2, -6] = true := by decide +kernel
theorem subd6_2_319 : subd6_2 [1, 2, -5] = true := by decide +kernel
theorem sbd6_2_9 : ∀ q ∈ blkd6_2_9, subd6_2 q = true := by
  unfold blkd6_2_9
  exact List.forall_mem_cons.2 ⟨subd6_2_288, List.forall_mem_cons.2 ⟨subd6_2_289, List.forall_mem_cons.2 ⟨subd6_2_290, List.forall_mem_cons.2 ⟨subd6_2_291, List.forall_mem_cons.2 ⟨subd6_2_292, List.forall_mem_cons.2 ⟨subd6_2_293, List.forall_mem_cons.2 ⟨subd6_2_294, List.forall_mem_cons.2 ⟨subd6_2_295, List.forall_mem_cons.2 ⟨subd6_2_296, List.forall_mem_cons.2 ⟨subd6_2_297, List.forall_mem_cons.2 ⟨subd6_2_298, List.forall_mem_cons.2 ⟨subd6_2_299, List.forall_mem_cons.2 ⟨subd6_2_300, List.forall_mem_cons.2 ⟨subd6_2_301, List.forall_mem_cons.2 ⟨subd6_2_302, List.forall_mem_cons.2 ⟨subd6_2_303, List.forall_mem_cons.2 ⟨subd6_2_304, List.forall_mem_cons.2 ⟨subd6_2_305, List.forall_mem_cons.2 ⟨subd6_2_306, List.forall_mem_cons.2 ⟨subd6_2_307, List.forall_mem_cons.2 ⟨subd6_2_308, List.forall_mem_cons.2 ⟨subd6_2_309, List.forall_mem_cons.2 ⟨subd6_2_310, List.forall_mem_cons.2 ⟨subd6_2_311, List.forall_mem_cons.2 ⟨subd6_2_312, List.forall_mem_cons.2 ⟨subd6_2_313, List.forall_mem_cons.2 ⟨subd6_2_314, List.forall_mem_cons.2 ⟨subd6_2_315, List.forall_mem_cons.2 ⟨subd6_2_316, List.forall_mem_cons.2 ⟨subd6_2_317, List.forall_mem_cons.2 ⟨subd6_2_318, List.forall_mem_cons.2 ⟨subd6_2_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_2_320 : subd6_2 [1, 2, -4] = true := by decide +kernel
theorem subd6_2_321 : subd6_2 [1, 2, -3] = true := by decide +kernel
theorem subd6_2_322 : subd6_2 [1, 2, -2] = true := by decide +kernel
theorem subd6_2_323 : subd6_2 [1, 2, -1] = true := by decide +kernel
theorem subd6_2_324 : subd6_2 [1, 2, 0] = true := by decide +kernel
theorem subd6_2_325 : subd6_2 [1, 2, 1] = true := by decide +kernel
theorem subd6_2_326 : subd6_2 [1, 2, 2] = true := by decide +kernel
theorem subd6_2_327 : subd6_2 [1, 2, 3] = true := by decide +kernel
theorem subd6_2_328 : subd6_2 [1, 2, 4] = true := by decide +kernel
theorem subd6_2_329 : subd6_2 [1, 2, 5] = true := by decide +kernel
theorem subd6_2_330 : subd6_2 [1, 2, 6] = true := by decide +kernel
theorem subd6_2_331 : subd6_2 [1, 2, 7] = true := by decide +kernel
theorem subd6_2_332 : subd6_2 [1, 3] = true := by decide +kernel
theorem subd6_2_333 : subd6_2 [2, -4] = true := by decide +kernel
theorem subd6_2_334 : subd6_2 [2, -3] = true := by decide +kernel
theorem subd6_2_335 : subd6_2 [2, -2, -7] = true := by decide +kernel
theorem subd6_2_336 : subd6_2 [2, -2, -6] = true := by decide +kernel
theorem subd6_2_337 : subd6_2 [2, -2, -5] = true := by decide +kernel
theorem subd6_2_338 : subd6_2 [2, -2, -4] = true := by decide +kernel
theorem subd6_2_339 : subd6_2 [2, -2, -3] = true := by decide +kernel
theorem subd6_2_340 : subd6_2 [2, -2, -2] = true := by decide +kernel
theorem subd6_2_341 : subd6_2 [2, -2, -1] = true := by decide +kernel
theorem subd6_2_342 : subd6_2 [2, -2, 0] = true := by decide +kernel
theorem subd6_2_343 : subd6_2 [2, -2, 1] = true := by decide +kernel
theorem subd6_2_344 : subd6_2 [2, -2, 2] = true := by decide +kernel
theorem subd6_2_345 : subd6_2 [2, -2, 3] = true := by decide +kernel
theorem subd6_2_346 : subd6_2 [2, -2, 4] = true := by decide +kernel
theorem subd6_2_347 : subd6_2 [2, -2, 5] = true := by decide +kernel
theorem subd6_2_348 : subd6_2 [2, -2, 6] = true := by decide +kernel
theorem subd6_2_349 : subd6_2 [2, -1, -8] = true := by decide +kernel
theorem subd6_2_350 : subd6_2 [2, -1, -7] = true := by decide +kernel
theorem subd6_2_351 : subd6_2 [2, -1, -6] = true := by decide +kernel
theorem sbd6_2_10 : ∀ q ∈ blkd6_2_10, subd6_2 q = true := by
  unfold blkd6_2_10
  exact List.forall_mem_cons.2 ⟨subd6_2_320, List.forall_mem_cons.2 ⟨subd6_2_321, List.forall_mem_cons.2 ⟨subd6_2_322, List.forall_mem_cons.2 ⟨subd6_2_323, List.forall_mem_cons.2 ⟨subd6_2_324, List.forall_mem_cons.2 ⟨subd6_2_325, List.forall_mem_cons.2 ⟨subd6_2_326, List.forall_mem_cons.2 ⟨subd6_2_327, List.forall_mem_cons.2 ⟨subd6_2_328, List.forall_mem_cons.2 ⟨subd6_2_329, List.forall_mem_cons.2 ⟨subd6_2_330, List.forall_mem_cons.2 ⟨subd6_2_331, List.forall_mem_cons.2 ⟨subd6_2_332, List.forall_mem_cons.2 ⟨subd6_2_333, List.forall_mem_cons.2 ⟨subd6_2_334, List.forall_mem_cons.2 ⟨subd6_2_335, List.forall_mem_cons.2 ⟨subd6_2_336, List.forall_mem_cons.2 ⟨subd6_2_337, List.forall_mem_cons.2 ⟨subd6_2_338, List.forall_mem_cons.2 ⟨subd6_2_339, List.forall_mem_cons.2 ⟨subd6_2_340, List.forall_mem_cons.2 ⟨subd6_2_341, List.forall_mem_cons.2 ⟨subd6_2_342, List.forall_mem_cons.2 ⟨subd6_2_343, List.forall_mem_cons.2 ⟨subd6_2_344, List.forall_mem_cons.2 ⟨subd6_2_345, List.forall_mem_cons.2 ⟨subd6_2_346, List.forall_mem_cons.2 ⟨subd6_2_347, List.forall_mem_cons.2 ⟨subd6_2_348, List.forall_mem_cons.2 ⟨subd6_2_349, List.forall_mem_cons.2 ⟨subd6_2_350, List.forall_mem_cons.2 ⟨subd6_2_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_2_352 : subd6_2 [2, -1, -5] = true := by decide +kernel
theorem subd6_2_353 : subd6_2 [2, -1, -4] = true := by decide +kernel
theorem subd6_2_354 : subd6_2 [2, -1, -3] = true := by decide +kernel
theorem subd6_2_355 : subd6_2 [2, -1, -2] = true := by decide +kernel
theorem subd6_2_356 : subd6_2 [2, -1, -1] = true := by decide +kernel
theorem subd6_2_357 : subd6_2 [2, -1, 0] = true := by decide +kernel
theorem subd6_2_358 : subd6_2 [2, -1, 1] = true := by decide +kernel
theorem subd6_2_359 : subd6_2 [2, -1, 2] = true := by decide +kernel
theorem subd6_2_360 : subd6_2 [2, -1, 3] = true := by decide +kernel
theorem subd6_2_361 : subd6_2 [2, -1, 4] = true := by decide +kernel
theorem subd6_2_362 : subd6_2 [2, -1, 5] = true := by decide +kernel
theorem subd6_2_363 : subd6_2 [2, -1, 6] = true := by decide +kernel
theorem subd6_2_364 : subd6_2 [2, -1, 7] = true := by decide +kernel
theorem subd6_2_365 : subd6_2 [2, 0, -8] = true := by decide +kernel
theorem subd6_2_366 : subd6_2 [2, 0, -7] = true := by decide +kernel
theorem subd6_2_367 : subd6_2 [2, 0, -6] = true := by decide +kernel
theorem subd6_2_368 : subd6_2 [2, 0, -5] = true := by decide +kernel
theorem subd6_2_369 : subd6_2 [2, 0, -4] = true := by decide +kernel
theorem subd6_2_370 : subd6_2 [2, 0, -3] = true := by decide +kernel
theorem subd6_2_371 : subd6_2 [2, 0, -2] = true := by decide +kernel
theorem subd6_2_372 : subd6_2 [2, 0, -1] = true := by decide +kernel
theorem subd6_2_373 : subd6_2 [2, 0, 0] = true := by decide +kernel
theorem subd6_2_374 : subd6_2 [2, 0, 1] = true := by decide +kernel
theorem subd6_2_375 : subd6_2 [2, 0, 2] = true := by decide +kernel
theorem subd6_2_376 : subd6_2 [2, 0, 3] = true := by decide +kernel
theorem subd6_2_377 : subd6_2 [2, 0, 4] = true := by decide +kernel
theorem subd6_2_378 : subd6_2 [2, 0, 5] = true := by decide +kernel
theorem subd6_2_379 : subd6_2 [2, 0, 6] = true := by decide +kernel
theorem subd6_2_380 : subd6_2 [2, 0, 7] = true := by decide +kernel
theorem subd6_2_381 : subd6_2 [2, 0, 8] = true := by decide +kernel
theorem subd6_2_382 : subd6_2 [2, 1, -7] = true := by decide +kernel
theorem subd6_2_383 : subd6_2 [2, 1, -6] = true := by decide +kernel
theorem sbd6_2_11 : ∀ q ∈ blkd6_2_11, subd6_2 q = true := by
  unfold blkd6_2_11
  exact List.forall_mem_cons.2 ⟨subd6_2_352, List.forall_mem_cons.2 ⟨subd6_2_353, List.forall_mem_cons.2 ⟨subd6_2_354, List.forall_mem_cons.2 ⟨subd6_2_355, List.forall_mem_cons.2 ⟨subd6_2_356, List.forall_mem_cons.2 ⟨subd6_2_357, List.forall_mem_cons.2 ⟨subd6_2_358, List.forall_mem_cons.2 ⟨subd6_2_359, List.forall_mem_cons.2 ⟨subd6_2_360, List.forall_mem_cons.2 ⟨subd6_2_361, List.forall_mem_cons.2 ⟨subd6_2_362, List.forall_mem_cons.2 ⟨subd6_2_363, List.forall_mem_cons.2 ⟨subd6_2_364, List.forall_mem_cons.2 ⟨subd6_2_365, List.forall_mem_cons.2 ⟨subd6_2_366, List.forall_mem_cons.2 ⟨subd6_2_367, List.forall_mem_cons.2 ⟨subd6_2_368, List.forall_mem_cons.2 ⟨subd6_2_369, List.forall_mem_cons.2 ⟨subd6_2_370, List.forall_mem_cons.2 ⟨subd6_2_371, List.forall_mem_cons.2 ⟨subd6_2_372, List.forall_mem_cons.2 ⟨subd6_2_373, List.forall_mem_cons.2 ⟨subd6_2_374, List.forall_mem_cons.2 ⟨subd6_2_375, List.forall_mem_cons.2 ⟨subd6_2_376, List.forall_mem_cons.2 ⟨subd6_2_377, List.forall_mem_cons.2 ⟨subd6_2_378, List.forall_mem_cons.2 ⟨subd6_2_379, List.forall_mem_cons.2 ⟨subd6_2_380, List.forall_mem_cons.2 ⟨subd6_2_381, List.forall_mem_cons.2 ⟨subd6_2_382, List.forall_mem_cons.2 ⟨subd6_2_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_2_384 : subd6_2 [2, 1, -5] = true := by decide +kernel
theorem subd6_2_385 : subd6_2 [2, 1, -4] = true := by decide +kernel
theorem subd6_2_386 : subd6_2 [2, 1, -3] = true := by decide +kernel
theorem subd6_2_387 : subd6_2 [2, 1, -2] = true := by decide +kernel
theorem subd6_2_388 : subd6_2 [2, 1, -1] = true := by decide +kernel
theorem subd6_2_389 : subd6_2 [2, 1, 0] = true := by decide +kernel
theorem subd6_2_390 : subd6_2 [2, 1, 1] = true := by decide +kernel
theorem subd6_2_391 : subd6_2 [2, 1, 2] = true := by decide +kernel
theorem subd6_2_392 : subd6_2 [2, 1, 3] = true := by decide +kernel
theorem subd6_2_393 : subd6_2 [2, 1, 4] = true := by decide +kernel
theorem subd6_2_394 : subd6_2 [2, 1, 5] = true := by decide +kernel
theorem subd6_2_395 : subd6_2 [2, 1, 6] = true := by decide +kernel
theorem subd6_2_396 : subd6_2 [2, 1, 7] = true := by decide +kernel
theorem subd6_2_397 : subd6_2 [2, 2] = true := by decide +kernel
theorem subd6_2_398 : subd6_2 [3, -3] = true := by decide +kernel
theorem subd6_2_399 : subd6_2 [3, -2] = true := by decide +kernel
theorem subd6_2_400 : subd6_2 [3, -1] = true := by decide +kernel
theorem subd6_2_401 : subd6_2 [3, 0] = true := by decide +kernel
theorem subd6_2_402 : subd6_2 [3, 1] = true := by decide +kernel
theorem sbd6_2_12 : ∀ q ∈ blkd6_2_12, subd6_2 q = true := by
  unfold blkd6_2_12
  exact List.forall_mem_cons.2 ⟨subd6_2_384, List.forall_mem_cons.2 ⟨subd6_2_385, List.forall_mem_cons.2 ⟨subd6_2_386, List.forall_mem_cons.2 ⟨subd6_2_387, List.forall_mem_cons.2 ⟨subd6_2_388, List.forall_mem_cons.2 ⟨subd6_2_389, List.forall_mem_cons.2 ⟨subd6_2_390, List.forall_mem_cons.2 ⟨subd6_2_391, List.forall_mem_cons.2 ⟨subd6_2_392, List.forall_mem_cons.2 ⟨subd6_2_393, List.forall_mem_cons.2 ⟨subd6_2_394, List.forall_mem_cons.2 ⟨subd6_2_395, List.forall_mem_cons.2 ⟨subd6_2_396, List.forall_mem_cons.2 ⟨subd6_2_397, List.forall_mem_cons.2 ⟨subd6_2_398, List.forall_mem_cons.2 ⟨subd6_2_399, List.forall_mem_cons.2 ⟨subd6_2_400, List.forall_mem_cons.2 ⟨subd6_2_401, List.forall_mem_cons.2 ⟨subd6_2_402, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_3 : ldCheck G d6_3.U d6_3.ms ldd6_3 = true := by decide +kernel
theorem pre_okd6_3 : subPre G cell6 d6_3 = true := by decide +kernel
theorem subd6_3_0 : subd6_3 [-4] = true := by decide +kernel
theorem subd6_3_1 : subd6_3 [-3, -6] = true := by decide +kernel
theorem subd6_3_2 : subd6_3 [-3, -5] = true := by decide +kernel
theorem subd6_3_3 : subd6_3 [-3, -4] = true := by decide +kernel
theorem subd6_3_4 : subd6_3 [-3, -3] = true := by decide +kernel
theorem subd6_3_5 : subd6_3 [-3, -2] = true := by decide +kernel
theorem subd6_3_6 : subd6_3 [-3, -1] = true := by decide +kernel
theorem subd6_3_7 : subd6_3 [-3, 0] = true := by decide +kernel
theorem subd6_3_8 : subd6_3 [-3, 1] = true := by decide +kernel
theorem subd6_3_9 : subd6_3 [-3, 2] = true := by decide +kernel
theorem subd6_3_10 : subd6_3 [-2, -6] = true := by decide +kernel
theorem subd6_3_11 : subd6_3 [-2, -5] = true := by decide +kernel
theorem subd6_3_12 : subd6_3 [-2, -4] = true := by decide +kernel
theorem subd6_3_13 : subd6_3 [-2, -3] = true := by decide +kernel
theorem subd6_3_14 : subd6_3 [-2, -2] = true := by decide +kernel
theorem subd6_3_15 : subd6_3 [-2, -1] = true := by decide +kernel
theorem subd6_3_16 : subd6_3 [-2, 0] = true := by decide +kernel
theorem subd6_3_17 : subd6_3 [-2, 1] = true := by decide +kernel
theorem subd6_3_18 : subd6_3 [-2, 2] = true := by decide +kernel
theorem subd6_3_19 : subd6_3 [-2, 3] = true := by decide +kernel
theorem subd6_3_20 : subd6_3 [-2, 4] = true := by decide +kernel
theorem subd6_3_21 : subd6_3 [-1, -6] = true := by decide +kernel
theorem subd6_3_22 : subd6_3 [-1, -5] = true := by decide +kernel
theorem subd6_3_23 : subd6_3 [-1, -4] = true := by decide +kernel
theorem subd6_3_24 : subd6_3 [-1, -3] = true := by decide +kernel
theorem subd6_3_25 : subd6_3 [-1, -2] = true := by decide +kernel
theorem subd6_3_26 : subd6_3 [-1, -1] = true := by decide +kernel
theorem subd6_3_27 : subd6_3 [-1, 0] = true := by decide +kernel
theorem subd6_3_28 : subd6_3 [-1, 1] = true := by decide +kernel
theorem subd6_3_29 : subd6_3 [-1, 2] = true := by decide +kernel
theorem subd6_3_30 : subd6_3 [-1, 3] = true := by decide +kernel
theorem subd6_3_31 : subd6_3 [-1, 4] = true := by decide +kernel
theorem sbd6_3_0 : ∀ q ∈ blkd6_3_0, subd6_3 q = true := by
  unfold blkd6_3_0
  exact List.forall_mem_cons.2 ⟨subd6_3_0, List.forall_mem_cons.2 ⟨subd6_3_1, List.forall_mem_cons.2 ⟨subd6_3_2, List.forall_mem_cons.2 ⟨subd6_3_3, List.forall_mem_cons.2 ⟨subd6_3_4, List.forall_mem_cons.2 ⟨subd6_3_5, List.forall_mem_cons.2 ⟨subd6_3_6, List.forall_mem_cons.2 ⟨subd6_3_7, List.forall_mem_cons.2 ⟨subd6_3_8, List.forall_mem_cons.2 ⟨subd6_3_9, List.forall_mem_cons.2 ⟨subd6_3_10, List.forall_mem_cons.2 ⟨subd6_3_11, List.forall_mem_cons.2 ⟨subd6_3_12, List.forall_mem_cons.2 ⟨subd6_3_13, List.forall_mem_cons.2 ⟨subd6_3_14, List.forall_mem_cons.2 ⟨subd6_3_15, List.forall_mem_cons.2 ⟨subd6_3_16, List.forall_mem_cons.2 ⟨subd6_3_17, List.forall_mem_cons.2 ⟨subd6_3_18, List.forall_mem_cons.2 ⟨subd6_3_19, List.forall_mem_cons.2 ⟨subd6_3_20, List.forall_mem_cons.2 ⟨subd6_3_21, List.forall_mem_cons.2 ⟨subd6_3_22, List.forall_mem_cons.2 ⟨subd6_3_23, List.forall_mem_cons.2 ⟨subd6_3_24, List.forall_mem_cons.2 ⟨subd6_3_25, List.forall_mem_cons.2 ⟨subd6_3_26, List.forall_mem_cons.2 ⟨subd6_3_27, List.forall_mem_cons.2 ⟨subd6_3_28, List.forall_mem_cons.2 ⟨subd6_3_29, List.forall_mem_cons.2 ⟨subd6_3_30, List.forall_mem_cons.2 ⟨subd6_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_3_32 : subd6_3 [0, -6] = true := by decide +kernel
theorem subd6_3_33 : subd6_3 [0, -5] = true := by decide +kernel
theorem subd6_3_34 : subd6_3 [0, -4] = true := by decide +kernel
theorem subd6_3_35 : subd6_3 [0, -3] = true := by decide +kernel
theorem subd6_3_36 : subd6_3 [0, -2] = true := by decide +kernel
theorem subd6_3_37 : subd6_3 [0, -1] = true := by decide +kernel
theorem subd6_3_38 : subd6_3 [0, 0] = true := by decide +kernel
theorem subd6_3_39 : subd6_3 [0, 1] = true := by decide +kernel
theorem subd6_3_40 : subd6_3 [0, 2] = true := by decide +kernel
theorem subd6_3_41 : subd6_3 [0, 3] = true := by decide +kernel
theorem subd6_3_42 : subd6_3 [0, 4] = true := by decide +kernel
theorem subd6_3_43 : subd6_3 [0, 5] = true := by decide +kernel
theorem subd6_3_44 : subd6_3 [1, -5] = true := by decide +kernel
theorem subd6_3_45 : subd6_3 [1, -4] = true := by decide +kernel
theorem subd6_3_46 : subd6_3 [1, -3] = true := by decide +kernel
theorem subd6_3_47 : subd6_3 [1, -2] = true := by decide +kernel
theorem subd6_3_48 : subd6_3 [1, -1] = true := by decide +kernel
theorem subd6_3_49 : subd6_3 [1, 0] = true := by decide +kernel
theorem subd6_3_50 : subd6_3 [1, 1] = true := by decide +kernel
theorem subd6_3_51 : subd6_3 [1, 2] = true := by decide +kernel
theorem subd6_3_52 : subd6_3 [1, 3] = true := by decide +kernel
theorem subd6_3_53 : subd6_3 [1, 4] = true := by decide +kernel
theorem subd6_3_54 : subd6_3 [1, 5] = true := by decide +kernel
theorem subd6_3_55 : subd6_3 [2, -5] = true := by decide +kernel
theorem subd6_3_56 : subd6_3 [2, -4] = true := by decide +kernel
theorem subd6_3_57 : subd6_3 [2, -3] = true := by decide +kernel
theorem subd6_3_58 : subd6_3 [2, -2] = true := by decide +kernel
theorem subd6_3_59 : subd6_3 [2, -1] = true := by decide +kernel
theorem subd6_3_60 : subd6_3 [2, 0] = true := by decide +kernel
theorem subd6_3_61 : subd6_3 [2, 1] = true := by decide +kernel
theorem subd6_3_62 : subd6_3 [2, 2] = true := by decide +kernel
theorem subd6_3_63 : subd6_3 [2, 3] = true := by decide +kernel
theorem sbd6_3_1 : ∀ q ∈ blkd6_3_1, subd6_3 q = true := by
  unfold blkd6_3_1
  exact List.forall_mem_cons.2 ⟨subd6_3_32, List.forall_mem_cons.2 ⟨subd6_3_33, List.forall_mem_cons.2 ⟨subd6_3_34, List.forall_mem_cons.2 ⟨subd6_3_35, List.forall_mem_cons.2 ⟨subd6_3_36, List.forall_mem_cons.2 ⟨subd6_3_37, List.forall_mem_cons.2 ⟨subd6_3_38, List.forall_mem_cons.2 ⟨subd6_3_39, List.forall_mem_cons.2 ⟨subd6_3_40, List.forall_mem_cons.2 ⟨subd6_3_41, List.forall_mem_cons.2 ⟨subd6_3_42, List.forall_mem_cons.2 ⟨subd6_3_43, List.forall_mem_cons.2 ⟨subd6_3_44, List.forall_mem_cons.2 ⟨subd6_3_45, List.forall_mem_cons.2 ⟨subd6_3_46, List.forall_mem_cons.2 ⟨subd6_3_47, List.forall_mem_cons.2 ⟨subd6_3_48, List.forall_mem_cons.2 ⟨subd6_3_49, List.forall_mem_cons.2 ⟨subd6_3_50, List.forall_mem_cons.2 ⟨subd6_3_51, List.forall_mem_cons.2 ⟨subd6_3_52, List.forall_mem_cons.2 ⟨subd6_3_53, List.forall_mem_cons.2 ⟨subd6_3_54, List.forall_mem_cons.2 ⟨subd6_3_55, List.forall_mem_cons.2 ⟨subd6_3_56, List.forall_mem_cons.2 ⟨subd6_3_57, List.forall_mem_cons.2 ⟨subd6_3_58, List.forall_mem_cons.2 ⟨subd6_3_59, List.forall_mem_cons.2 ⟨subd6_3_60, List.forall_mem_cons.2 ⟨subd6_3_61, List.forall_mem_cons.2 ⟨subd6_3_62, List.forall_mem_cons.2 ⟨subd6_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_3_64 : subd6_3 [2, 4] = true := by decide +kernel
theorem subd6_3_65 : subd6_3 [2, 5] = true := by decide +kernel
theorem subd6_3_66 : subd6_3 [3, -3] = true := by decide +kernel
theorem subd6_3_67 : subd6_3 [3, -2] = true := by decide +kernel
theorem subd6_3_68 : subd6_3 [3, -1] = true := by decide +kernel
theorem subd6_3_69 : subd6_3 [3, 0] = true := by decide +kernel
theorem subd6_3_70 : subd6_3 [3, 1] = true := by decide +kernel
theorem subd6_3_71 : subd6_3 [3, 2] = true := by decide +kernel
theorem subd6_3_72 : subd6_3 [3, 3] = true := by decide +kernel
theorem subd6_3_73 : subd6_3 [3, 4] = true := by decide +kernel
theorem subd6_3_74 : subd6_3 [3, 5] = true := by decide +kernel
theorem subd6_3_75 : subd6_3 [4] = true := by decide +kernel
theorem sbd6_3_2 : ∀ q ∈ blkd6_3_2, subd6_3 q = true := by
  unfold blkd6_3_2
  exact List.forall_mem_cons.2 ⟨subd6_3_64, List.forall_mem_cons.2 ⟨subd6_3_65, List.forall_mem_cons.2 ⟨subd6_3_66, List.forall_mem_cons.2 ⟨subd6_3_67, List.forall_mem_cons.2 ⟨subd6_3_68, List.forall_mem_cons.2 ⟨subd6_3_69, List.forall_mem_cons.2 ⟨subd6_3_70, List.forall_mem_cons.2 ⟨subd6_3_71, List.forall_mem_cons.2 ⟨subd6_3_72, List.forall_mem_cons.2 ⟨subd6_3_73, List.forall_mem_cons.2 ⟨subd6_3_74, List.forall_mem_cons.2 ⟨subd6_3_75, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_4 : ldCheck G d6_4.U d6_4.ms ldd6_4 = true := by decide +kernel
theorem pre_okd6_4 : subPre G cell6 d6_4 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C110
