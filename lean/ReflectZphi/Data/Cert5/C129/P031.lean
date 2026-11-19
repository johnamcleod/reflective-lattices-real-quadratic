import ReflectZphi.Data.Cert5.C129.Base

namespace ReflectZphi.Data.Cert5.C129

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_2_288 : subd9_2 [1, 0, -1] = true := by decide +kernel
theorem subd9_2_289 : subd9_2 [1, 0, 0] = true := by decide +kernel
theorem subd9_2_290 : subd9_2 [1, 0, 1] = true := by decide +kernel
theorem subd9_2_291 : subd9_2 [1, 0, 2] = true := by decide +kernel
theorem subd9_2_292 : subd9_2 [1, 0, 3] = true := by decide +kernel
theorem subd9_2_293 : subd9_2 [1, 0, 4] = true := by decide +kernel
theorem subd9_2_294 : subd9_2 [1, 0, 5] = true := by decide +kernel
theorem subd9_2_295 : subd9_2 [1, 0, 6] = true := by decide +kernel
theorem subd9_2_296 : subd9_2 [1, 0, 7] = true := by decide +kernel
theorem subd9_2_297 : subd9_2 [1, 1, -8] = true := by decide +kernel
theorem subd9_2_298 : subd9_2 [1, 1, -7] = true := by decide +kernel
theorem subd9_2_299 : subd9_2 [1, 1, -6] = true := by decide +kernel
theorem subd9_2_300 : subd9_2 [1, 1, -5] = true := by decide +kernel
theorem subd9_2_301 : subd9_2 [1, 1, -4] = true := by decide +kernel
theorem subd9_2_302 : subd9_2 [1, 1, -3] = true := by decide +kernel
theorem subd9_2_303 : subd9_2 [1, 1, -2] = true := by decide +kernel
theorem subd9_2_304 : subd9_2 [1, 1, -1] = true := by decide +kernel
theorem subd9_2_305 : subd9_2 [1, 1, 0] = true := by decide +kernel
theorem subd9_2_306 : subd9_2 [1, 1, 1] = true := by decide +kernel
theorem subd9_2_307 : subd9_2 [1, 1, 2] = true := by decide +kernel
theorem subd9_2_308 : subd9_2 [1, 1, 3] = true := by decide +kernel
theorem subd9_2_309 : subd9_2 [1, 1, 4] = true := by decide +kernel
theorem subd9_2_310 : subd9_2 [1, 1, 5] = true := by decide +kernel
theorem subd9_2_311 : subd9_2 [1, 1, 6] = true := by decide +kernel
theorem subd9_2_312 : subd9_2 [1, 1, 7] = true := by decide +kernel
theorem subd9_2_313 : subd9_2 [1, 2, -7] = true := by decide +kernel
theorem subd9_2_314 : subd9_2 [1, 2, -6] = true := by decide +kernel
theorem subd9_2_315 : subd9_2 [1, 2, -5] = true := by decide +kernel
theorem subd9_2_316 : subd9_2 [1, 2, -4] = true := by decide +kernel
theorem subd9_2_317 : subd9_2 [1, 2, -3] = true := by decide +kernel
theorem subd9_2_318 : subd9_2 [1, 2, -2] = true := by decide +kernel
theorem subd9_2_319 : subd9_2 [1, 2, -1] = true := by decide +kernel
theorem sbd9_2_9 : ∀ q ∈ blkd9_2_9, subd9_2 q = true := by
  unfold blkd9_2_9
  exact List.forall_mem_cons.2 ⟨subd9_2_288, List.forall_mem_cons.2 ⟨subd9_2_289, List.forall_mem_cons.2 ⟨subd9_2_290, List.forall_mem_cons.2 ⟨subd9_2_291, List.forall_mem_cons.2 ⟨subd9_2_292, List.forall_mem_cons.2 ⟨subd9_2_293, List.forall_mem_cons.2 ⟨subd9_2_294, List.forall_mem_cons.2 ⟨subd9_2_295, List.forall_mem_cons.2 ⟨subd9_2_296, List.forall_mem_cons.2 ⟨subd9_2_297, List.forall_mem_cons.2 ⟨subd9_2_298, List.forall_mem_cons.2 ⟨subd9_2_299, List.forall_mem_cons.2 ⟨subd9_2_300, List.forall_mem_cons.2 ⟨subd9_2_301, List.forall_mem_cons.2 ⟨subd9_2_302, List.forall_mem_cons.2 ⟨subd9_2_303, List.forall_mem_cons.2 ⟨subd9_2_304, List.forall_mem_cons.2 ⟨subd9_2_305, List.forall_mem_cons.2 ⟨subd9_2_306, List.forall_mem_cons.2 ⟨subd9_2_307, List.forall_mem_cons.2 ⟨subd9_2_308, List.forall_mem_cons.2 ⟨subd9_2_309, List.forall_mem_cons.2 ⟨subd9_2_310, List.forall_mem_cons.2 ⟨subd9_2_311, List.forall_mem_cons.2 ⟨subd9_2_312, List.forall_mem_cons.2 ⟨subd9_2_313, List.forall_mem_cons.2 ⟨subd9_2_314, List.forall_mem_cons.2 ⟨subd9_2_315, List.forall_mem_cons.2 ⟨subd9_2_316, List.forall_mem_cons.2 ⟨subd9_2_317, List.forall_mem_cons.2 ⟨subd9_2_318, List.forall_mem_cons.2 ⟨subd9_2_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_320 : subd9_2 [1, 2, 0] = true := by decide +kernel
theorem subd9_2_321 : subd9_2 [1, 2, 1] = true := by decide +kernel
theorem subd9_2_322 : subd9_2 [1, 2, 2] = true := by decide +kernel
theorem subd9_2_323 : subd9_2 [1, 2, 3] = true := by decide +kernel
theorem subd9_2_324 : subd9_2 [1, 2, 4] = true := by decide +kernel
theorem subd9_2_325 : subd9_2 [1, 2, 5] = true := by decide +kernel
theorem subd9_2_326 : subd9_2 [1, 2, 6] = true := by decide +kernel
theorem subd9_2_327 : subd9_2 [1, 2, 7] = true := by decide +kernel
theorem subd9_2_328 : subd9_2 [1, 3] = true := by decide +kernel
theorem subd9_2_329 : subd9_2 [1, 4] = true := by decide +kernel
theorem subd9_2_330 : subd9_2 [2, -5] = true := by decide +kernel
theorem subd9_2_331 : subd9_2 [2, -4] = true := by decide +kernel
theorem subd9_2_332 : subd9_2 [2, -3] = true := by decide +kernel
theorem subd9_2_333 : subd9_2 [2, -2, -8] = true := by decide +kernel
theorem subd9_2_334 : subd9_2 [2, -2, -7] = true := by decide +kernel
theorem subd9_2_335 : subd9_2 [2, -2, -6] = true := by decide +kernel
theorem subd9_2_336 : subd9_2 [2, -2, -5] = true := by decide +kernel
theorem subd9_2_337 : subd9_2 [2, -2, -4] = true := by decide +kernel
theorem subd9_2_338 : subd9_2 [2, -2, -3] = true := by decide +kernel
theorem subd9_2_339 : subd9_2 [2, -2, -2] = true := by decide +kernel
theorem subd9_2_340 : subd9_2 [2, -2, -1] = true := by decide +kernel
theorem subd9_2_341 : subd9_2 [2, -2, 0] = true := by decide +kernel
theorem subd9_2_342 : subd9_2 [2, -2, 1] = true := by decide +kernel
theorem subd9_2_343 : subd9_2 [2, -2, 2] = true := by decide +kernel
theorem subd9_2_344 : subd9_2 [2, -2, 3] = true := by decide +kernel
theorem subd9_2_345 : subd9_2 [2, -2, 4] = true := by decide +kernel
theorem subd9_2_346 : subd9_2 [2, -2, 5] = true := by decide +kernel
theorem subd9_2_347 : subd9_2 [2, -2, 6] = true := by decide +kernel
theorem subd9_2_348 : subd9_2 [2, -1, -8] = true := by decide +kernel
theorem subd9_2_349 : subd9_2 [2, -1, -7] = true := by decide +kernel
theorem subd9_2_350 : subd9_2 [2, -1, -6] = true := by decide +kernel
theorem subd9_2_351 : subd9_2 [2, -1, -5] = true := by decide +kernel
theorem sbd9_2_10 : ∀ q ∈ blkd9_2_10, subd9_2 q = true := by
  unfold blkd9_2_10
  exact List.forall_mem_cons.2 ⟨subd9_2_320, List.forall_mem_cons.2 ⟨subd9_2_321, List.forall_mem_cons.2 ⟨subd9_2_322, List.forall_mem_cons.2 ⟨subd9_2_323, List.forall_mem_cons.2 ⟨subd9_2_324, List.forall_mem_cons.2 ⟨subd9_2_325, List.forall_mem_cons.2 ⟨subd9_2_326, List.forall_mem_cons.2 ⟨subd9_2_327, List.forall_mem_cons.2 ⟨subd9_2_328, List.forall_mem_cons.2 ⟨subd9_2_329, List.forall_mem_cons.2 ⟨subd9_2_330, List.forall_mem_cons.2 ⟨subd9_2_331, List.forall_mem_cons.2 ⟨subd9_2_332, List.forall_mem_cons.2 ⟨subd9_2_333, List.forall_mem_cons.2 ⟨subd9_2_334, List.forall_mem_cons.2 ⟨subd9_2_335, List.forall_mem_cons.2 ⟨subd9_2_336, List.forall_mem_cons.2 ⟨subd9_2_337, List.forall_mem_cons.2 ⟨subd9_2_338, List.forall_mem_cons.2 ⟨subd9_2_339, List.forall_mem_cons.2 ⟨subd9_2_340, List.forall_mem_cons.2 ⟨subd9_2_341, List.forall_mem_cons.2 ⟨subd9_2_342, List.forall_mem_cons.2 ⟨subd9_2_343, List.forall_mem_cons.2 ⟨subd9_2_344, List.forall_mem_cons.2 ⟨subd9_2_345, List.forall_mem_cons.2 ⟨subd9_2_346, List.forall_mem_cons.2 ⟨subd9_2_347, List.forall_mem_cons.2 ⟨subd9_2_348, List.forall_mem_cons.2 ⟨subd9_2_349, List.forall_mem_cons.2 ⟨subd9_2_350, List.forall_mem_cons.2 ⟨subd9_2_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_352 : subd9_2 [2, -1, -4] = true := by decide +kernel
theorem subd9_2_353 : subd9_2 [2, -1, -3] = true := by decide +kernel
theorem subd9_2_354 : subd9_2 [2, -1, -2] = true := by decide +kernel
theorem subd9_2_355 : subd9_2 [2, -1, -1] = true := by decide +kernel
theorem subd9_2_356 : subd9_2 [2, -1, 0] = true := by decide +kernel
theorem subd9_2_357 : subd9_2 [2, -1, 1] = true := by decide +kernel
theorem subd9_2_358 : subd9_2 [2, -1, 2] = true := by decide +kernel
theorem subd9_2_359 : subd9_2 [2, -1, 3] = true := by decide +kernel
theorem subd9_2_360 : subd9_2 [2, -1, 4] = true := by decide +kernel
theorem subd9_2_361 : subd9_2 [2, -1, 5] = true := by decide +kernel
theorem subd9_2_362 : subd9_2 [2, -1, 6] = true := by decide +kernel
theorem subd9_2_363 : subd9_2 [2, 0, -8] = true := by decide +kernel
theorem subd9_2_364 : subd9_2 [2, 0, -7] = true := by decide +kernel
theorem subd9_2_365 : subd9_2 [2, 0, -6] = true := by decide +kernel
theorem subd9_2_366 : subd9_2 [2, 0, -5] = true := by decide +kernel
theorem subd9_2_367 : subd9_2 [2, 0, -4] = true := by decide +kernel
theorem subd9_2_368 : subd9_2 [2, 0, -3] = true := by decide +kernel
theorem subd9_2_369 : subd9_2 [2, 0, -2] = true := by decide +kernel
theorem subd9_2_370 : subd9_2 [2, 0, -1] = true := by decide +kernel
theorem subd9_2_371 : subd9_2 [2, 0, 0] = true := by decide +kernel
theorem subd9_2_372 : subd9_2 [2, 0, 1] = true := by decide +kernel
theorem subd9_2_373 : subd9_2 [2, 0, 2] = true := by decide +kernel
theorem subd9_2_374 : subd9_2 [2, 0, 3] = true := by decide +kernel
theorem subd9_2_375 : subd9_2 [2, 0, 4] = true := by decide +kernel
theorem subd9_2_376 : subd9_2 [2, 0, 5] = true := by decide +kernel
theorem subd9_2_377 : subd9_2 [2, 0, 6] = true := by decide +kernel
theorem subd9_2_378 : subd9_2 [2, 0, 7] = true := by decide +kernel
theorem subd9_2_379 : subd9_2 [2, 1, -7] = true := by decide +kernel
theorem subd9_2_380 : subd9_2 [2, 1, -6] = true := by decide +kernel
theorem subd9_2_381 : subd9_2 [2, 1, -5] = true := by decide +kernel
theorem subd9_2_382 : subd9_2 [2, 1, -4] = true := by decide +kernel
theorem subd9_2_383 : subd9_2 [2, 1, -3] = true := by decide +kernel
theorem sbd9_2_11 : ∀ q ∈ blkd9_2_11, subd9_2 q = true := by
  unfold blkd9_2_11
  exact List.forall_mem_cons.2 ⟨subd9_2_352, List.forall_mem_cons.2 ⟨subd9_2_353, List.forall_mem_cons.2 ⟨subd9_2_354, List.forall_mem_cons.2 ⟨subd9_2_355, List.forall_mem_cons.2 ⟨subd9_2_356, List.forall_mem_cons.2 ⟨subd9_2_357, List.forall_mem_cons.2 ⟨subd9_2_358, List.forall_mem_cons.2 ⟨subd9_2_359, List.forall_mem_cons.2 ⟨subd9_2_360, List.forall_mem_cons.2 ⟨subd9_2_361, List.forall_mem_cons.2 ⟨subd9_2_362, List.forall_mem_cons.2 ⟨subd9_2_363, List.forall_mem_cons.2 ⟨subd9_2_364, List.forall_mem_cons.2 ⟨subd9_2_365, List.forall_mem_cons.2 ⟨subd9_2_366, List.forall_mem_cons.2 ⟨subd9_2_367, List.forall_mem_cons.2 ⟨subd9_2_368, List.forall_mem_cons.2 ⟨subd9_2_369, List.forall_mem_cons.2 ⟨subd9_2_370, List.forall_mem_cons.2 ⟨subd9_2_371, List.forall_mem_cons.2 ⟨subd9_2_372, List.forall_mem_cons.2 ⟨subd9_2_373, List.forall_mem_cons.2 ⟨subd9_2_374, List.forall_mem_cons.2 ⟨subd9_2_375, List.forall_mem_cons.2 ⟨subd9_2_376, List.forall_mem_cons.2 ⟨subd9_2_377, List.forall_mem_cons.2 ⟨subd9_2_378, List.forall_mem_cons.2 ⟨subd9_2_379, List.forall_mem_cons.2 ⟨subd9_2_380, List.forall_mem_cons.2 ⟨subd9_2_381, List.forall_mem_cons.2 ⟨subd9_2_382, List.forall_mem_cons.2 ⟨subd9_2_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_384 : subd9_2 [2, 1, -2] = true := by decide +kernel
theorem subd9_2_385 : subd9_2 [2, 1, -1] = true := by decide +kernel
theorem subd9_2_386 : subd9_2 [2, 1, 0] = true := by decide +kernel
theorem subd9_2_387 : subd9_2 [2, 1, 1] = true := by decide +kernel
theorem subd9_2_388 : subd9_2 [2, 1, 2] = true := by decide +kernel
theorem subd9_2_389 : subd9_2 [2, 1, 3] = true := by decide +kernel
theorem subd9_2_390 : subd9_2 [2, 1, 4] = true := by decide +kernel
theorem subd9_2_391 : subd9_2 [2, 1, 5] = true := by decide +kernel
theorem subd9_2_392 : subd9_2 [2, 1, 6] = true := by decide +kernel
theorem subd9_2_393 : subd9_2 [2, 2] = true := by decide +kernel
theorem subd9_2_394 : subd9_2 [2, 3] = true := by decide +kernel
theorem subd9_2_395 : subd9_2 [3, -5] = true := by decide +kernel
theorem subd9_2_396 : subd9_2 [3, -4] = true := by decide +kernel
theorem subd9_2_397 : subd9_2 [3, -3] = true := by decide +kernel
theorem subd9_2_398 : subd9_2 [3, -2] = true := by decide +kernel
theorem subd9_2_399 : subd9_2 [3, -1] = true := by decide +kernel
theorem subd9_2_400 : subd9_2 [3, 0] = true := by decide +kernel
theorem subd9_2_401 : subd9_2 [3, 1] = true := by decide +kernel
theorem subd9_2_402 : subd9_2 [3, 2] = true := by decide +kernel
theorem subd9_2_403 : subd9_2 [3, 3] = true := by decide +kernel
theorem subd9_2_404 : subd9_2 [4, -4] = true := by decide +kernel
theorem subd9_2_405 : subd9_2 [4, -3] = true := by decide +kernel
theorem subd9_2_406 : subd9_2 [4, -2] = true := by decide +kernel
theorem subd9_2_407 : subd9_2 [4, -1] = true := by decide +kernel
theorem subd9_2_408 : subd9_2 [4, 0] = true := by decide +kernel
theorem subd9_2_409 : subd9_2 [4, 1] = true := by decide +kernel
theorem subd9_2_410 : subd9_2 [4, 2] = true := by decide +kernel
theorem sbd9_2_12 : ∀ q ∈ blkd9_2_12, subd9_2 q = true := by
  unfold blkd9_2_12
  exact List.forall_mem_cons.2 ⟨subd9_2_384, List.forall_mem_cons.2 ⟨subd9_2_385, List.forall_mem_cons.2 ⟨subd9_2_386, List.forall_mem_cons.2 ⟨subd9_2_387, List.forall_mem_cons.2 ⟨subd9_2_388, List.forall_mem_cons.2 ⟨subd9_2_389, List.forall_mem_cons.2 ⟨subd9_2_390, List.forall_mem_cons.2 ⟨subd9_2_391, List.forall_mem_cons.2 ⟨subd9_2_392, List.forall_mem_cons.2 ⟨subd9_2_393, List.forall_mem_cons.2 ⟨subd9_2_394, List.forall_mem_cons.2 ⟨subd9_2_395, List.forall_mem_cons.2 ⟨subd9_2_396, List.forall_mem_cons.2 ⟨subd9_2_397, List.forall_mem_cons.2 ⟨subd9_2_398, List.forall_mem_cons.2 ⟨subd9_2_399, List.forall_mem_cons.2 ⟨subd9_2_400, List.forall_mem_cons.2 ⟨subd9_2_401, List.forall_mem_cons.2 ⟨subd9_2_402, List.forall_mem_cons.2 ⟨subd9_2_403, List.forall_mem_cons.2 ⟨subd9_2_404, List.forall_mem_cons.2 ⟨subd9_2_405, List.forall_mem_cons.2 ⟨subd9_2_406, List.forall_mem_cons.2 ⟨subd9_2_407, List.forall_mem_cons.2 ⟨subd9_2_408, List.forall_mem_cons.2 ⟨subd9_2_409, List.forall_mem_cons.2 ⟨subd9_2_410, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_3 : ldCheck G d9_3.U d9_3.ms ldd9_3 = true := by decide +kernel
theorem pre_okd9_3 : subPre G cell9 d9_3 = true := by decide +kernel
theorem subd9_3_0 : subd9_3 [-4, -2] = true := by decide +kernel
theorem subd9_3_1 : subd9_3 [-4, -1] = true := by decide +kernel
theorem subd9_3_2 : subd9_3 [-4, 0] = true := by decide +kernel
theorem subd9_3_3 : subd9_3 [-4, 1] = true := by decide +kernel
theorem subd9_3_4 : subd9_3 [-4, 2] = true := by decide +kernel
theorem subd9_3_5 : subd9_3 [-4, 3] = true := by decide +kernel
theorem subd9_3_6 : subd9_3 [-4, 4] = true := by decide +kernel
theorem subd9_3_7 : subd9_3 [-4, 5] = true := by decide +kernel
theorem subd9_3_8 : subd9_3 [-3, -3] = true := by decide +kernel
theorem subd9_3_9 : subd9_3 [-3, -2] = true := by decide +kernel
theorem subd9_3_10 : subd9_3 [-3, -1] = true := by decide +kernel
theorem subd9_3_11 : subd9_3 [-3, 0] = true := by decide +kernel
theorem subd9_3_12 : subd9_3 [-3, 1] = true := by decide +kernel
theorem subd9_3_13 : subd9_3 [-3, 2] = true := by decide +kernel
theorem subd9_3_14 : subd9_3 [-3, 3] = true := by decide +kernel
theorem subd9_3_15 : subd9_3 [-3, 4] = true := by decide +kernel
theorem subd9_3_16 : subd9_3 [-3, 5] = true := by decide +kernel
theorem subd9_3_17 : subd9_3 [-2, -5] = true := by decide +kernel
theorem subd9_3_18 : subd9_3 [-2, -4] = true := by decide +kernel
theorem subd9_3_19 : subd9_3 [-2, -3] = true := by decide +kernel
theorem subd9_3_20 : subd9_3 [-2, -2] = true := by decide +kernel
theorem subd9_3_21 : subd9_3 [-2, -1, -7] = true := by decide +kernel
theorem subd9_3_22 : subd9_3 [-2, -1, -6] = true := by decide +kernel
theorem subd9_3_23 : subd9_3 [-2, -1, -5] = true := by decide +kernel
theorem subd9_3_24 : subd9_3 [-2, -1, -4] = true := by decide +kernel
theorem subd9_3_25 : subd9_3 [-2, -1, -3] = true := by decide +kernel
theorem subd9_3_26 : subd9_3 [-2, -1, -2] = true := by decide +kernel
theorem subd9_3_27 : subd9_3 [-2, -1, -1] = true := by decide +kernel
theorem subd9_3_28 : subd9_3 [-2, -1, 0] = true := by decide +kernel
theorem subd9_3_29 : subd9_3 [-2, -1, 1] = true := by decide +kernel
theorem subd9_3_30 : subd9_3 [-2, -1, 2] = true := by decide +kernel
theorem subd9_3_31 : subd9_3 [-2, -1, 3] = true := by decide +kernel
theorem sbd9_3_0 : ∀ q ∈ blkd9_3_0, subd9_3 q = true := by
  unfold blkd9_3_0
  exact List.forall_mem_cons.2 ⟨subd9_3_0, List.forall_mem_cons.2 ⟨subd9_3_1, List.forall_mem_cons.2 ⟨subd9_3_2, List.forall_mem_cons.2 ⟨subd9_3_3, List.forall_mem_cons.2 ⟨subd9_3_4, List.forall_mem_cons.2 ⟨subd9_3_5, List.forall_mem_cons.2 ⟨subd9_3_6, List.forall_mem_cons.2 ⟨subd9_3_7, List.forall_mem_cons.2 ⟨subd9_3_8, List.forall_mem_cons.2 ⟨subd9_3_9, List.forall_mem_cons.2 ⟨subd9_3_10, List.forall_mem_cons.2 ⟨subd9_3_11, List.forall_mem_cons.2 ⟨subd9_3_12, List.forall_mem_cons.2 ⟨subd9_3_13, List.forall_mem_cons.2 ⟨subd9_3_14, List.forall_mem_cons.2 ⟨subd9_3_15, List.forall_mem_cons.2 ⟨subd9_3_16, List.forall_mem_cons.2 ⟨subd9_3_17, List.forall_mem_cons.2 ⟨subd9_3_18, List.forall_mem_cons.2 ⟨subd9_3_19, List.forall_mem_cons.2 ⟨subd9_3_20, List.forall_mem_cons.2 ⟨subd9_3_21, List.forall_mem_cons.2 ⟨subd9_3_22, List.forall_mem_cons.2 ⟨subd9_3_23, List.forall_mem_cons.2 ⟨subd9_3_24, List.forall_mem_cons.2 ⟨subd9_3_25, List.forall_mem_cons.2 ⟨subd9_3_26, List.forall_mem_cons.2 ⟨subd9_3_27, List.forall_mem_cons.2 ⟨subd9_3_28, List.forall_mem_cons.2 ⟨subd9_3_29, List.forall_mem_cons.2 ⟨subd9_3_30, List.forall_mem_cons.2 ⟨subd9_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_32 : subd9_3 [-2, -1, 4] = true := by decide +kernel
theorem subd9_3_33 : subd9_3 [-2, -1, 5] = true := by decide +kernel
theorem subd9_3_34 : subd9_3 [-2, -1, 6] = true := by decide +kernel
theorem subd9_3_35 : subd9_3 [-2, -1, 7] = true := by decide +kernel
theorem subd9_3_36 : subd9_3 [-2, 0, -7] = true := by decide +kernel
theorem subd9_3_37 : subd9_3 [-2, 0, -6] = true := by decide +kernel
theorem subd9_3_38 : subd9_3 [-2, 0, -5] = true := by decide +kernel
theorem subd9_3_39 : subd9_3 [-2, 0, -4] = true := by decide +kernel
theorem subd9_3_40 : subd9_3 [-2, 0, -3] = true := by decide +kernel
theorem subd9_3_41 : subd9_3 [-2, 0, -2] = true := by decide +kernel
theorem subd9_3_42 : subd9_3 [-2, 0, -1] = true := by decide +kernel
theorem subd9_3_43 : subd9_3 [-2, 0, 0] = true := by decide +kernel
theorem subd9_3_44 : subd9_3 [-2, 0, 1] = true := by decide +kernel
theorem subd9_3_45 : subd9_3 [-2, 0, 2] = true := by decide +kernel
theorem subd9_3_46 : subd9_3 [-2, 0, 3] = true := by decide +kernel
theorem subd9_3_47 : subd9_3 [-2, 0, 4] = true := by decide +kernel
theorem subd9_3_48 : subd9_3 [-2, 0, 5] = true := by decide +kernel
theorem subd9_3_49 : subd9_3 [-2, 0, 6] = true := by decide +kernel
theorem subd9_3_50 : subd9_3 [-2, 0, 7] = true := by decide +kernel
theorem subd9_3_51 : subd9_3 [-2, 1, -7] = true := by decide +kernel
theorem subd9_3_52 : subd9_3 [-2, 1, -6] = true := by decide +kernel
theorem subd9_3_53 : subd9_3 [-2, 1, -5] = true := by decide +kernel
theorem subd9_3_54 : subd9_3 [-2, 1, -4] = true := by decide +kernel
theorem subd9_3_55 : subd9_3 [-2, 1, -3] = true := by decide +kernel
theorem subd9_3_56 : subd9_3 [-2, 1, -2] = true := by decide +kernel
theorem subd9_3_57 : subd9_3 [-2, 1, -1] = true := by decide +kernel
theorem subd9_3_58 : subd9_3 [-2, 1, 0] = true := by decide +kernel
theorem subd9_3_59 : subd9_3 [-2, 1, 1] = true := by decide +kernel
theorem subd9_3_60 : subd9_3 [-2, 1, 2] = true := by decide +kernel
theorem subd9_3_61 : subd9_3 [-2, 1, 3] = true := by decide +kernel
theorem subd9_3_62 : subd9_3 [-2, 1, 4] = true := by decide +kernel
theorem subd9_3_63 : subd9_3 [-2, 1, 5] = true := by decide +kernel
theorem sbd9_3_1 : ∀ q ∈ blkd9_3_1, subd9_3 q = true := by
  unfold blkd9_3_1
  exact List.forall_mem_cons.2 ⟨subd9_3_32, List.forall_mem_cons.2 ⟨subd9_3_33, List.forall_mem_cons.2 ⟨subd9_3_34, List.forall_mem_cons.2 ⟨subd9_3_35, List.forall_mem_cons.2 ⟨subd9_3_36, List.forall_mem_cons.2 ⟨subd9_3_37, List.forall_mem_cons.2 ⟨subd9_3_38, List.forall_mem_cons.2 ⟨subd9_3_39, List.forall_mem_cons.2 ⟨subd9_3_40, List.forall_mem_cons.2 ⟨subd9_3_41, List.forall_mem_cons.2 ⟨subd9_3_42, List.forall_mem_cons.2 ⟨subd9_3_43, List.forall_mem_cons.2 ⟨subd9_3_44, List.forall_mem_cons.2 ⟨subd9_3_45, List.forall_mem_cons.2 ⟨subd9_3_46, List.forall_mem_cons.2 ⟨subd9_3_47, List.forall_mem_cons.2 ⟨subd9_3_48, List.forall_mem_cons.2 ⟨subd9_3_49, List.forall_mem_cons.2 ⟨subd9_3_50, List.forall_mem_cons.2 ⟨subd9_3_51, List.forall_mem_cons.2 ⟨subd9_3_52, List.forall_mem_cons.2 ⟨subd9_3_53, List.forall_mem_cons.2 ⟨subd9_3_54, List.forall_mem_cons.2 ⟨subd9_3_55, List.forall_mem_cons.2 ⟨subd9_3_56, List.forall_mem_cons.2 ⟨subd9_3_57, List.forall_mem_cons.2 ⟨subd9_3_58, List.forall_mem_cons.2 ⟨subd9_3_59, List.forall_mem_cons.2 ⟨subd9_3_60, List.forall_mem_cons.2 ⟨subd9_3_61, List.forall_mem_cons.2 ⟨subd9_3_62, List.forall_mem_cons.2 ⟨subd9_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_64 : subd9_3 [-2, 1, 6] = true := by decide +kernel
theorem subd9_3_65 : subd9_3 [-2, 1, 7] = true := by decide +kernel
theorem subd9_3_66 : subd9_3 [-2, 2, -7] = true := by decide +kernel
theorem subd9_3_67 : subd9_3 [-2, 2, -6] = true := by decide +kernel
theorem subd9_3_68 : subd9_3 [-2, 2, -5] = true := by decide +kernel
theorem subd9_3_69 : subd9_3 [-2, 2, -4] = true := by decide +kernel
theorem subd9_3_70 : subd9_3 [-2, 2, -3] = true := by decide +kernel
theorem subd9_3_71 : subd9_3 [-2, 2, -2] = true := by decide +kernel
theorem subd9_3_72 : subd9_3 [-2, 2, -1] = true := by decide +kernel
theorem subd9_3_73 : subd9_3 [-2, 2, 0] = true := by decide +kernel
theorem subd9_3_74 : subd9_3 [-2, 2, 1] = true := by decide +kernel
theorem subd9_3_75 : subd9_3 [-2, 2, 2] = true := by decide +kernel
theorem subd9_3_76 : subd9_3 [-2, 2, 3] = true := by decide +kernel
theorem subd9_3_77 : subd9_3 [-2, 2, 4] = true := by decide +kernel
theorem subd9_3_78 : subd9_3 [-2, 2, 5] = true := by decide +kernel
theorem subd9_3_79 : subd9_3 [-2, 2, 6] = true := by decide +kernel
theorem subd9_3_80 : subd9_3 [-2, 2, 7] = true := by decide +kernel
theorem subd9_3_81 : subd9_3 [-2, 3, -6] = true := by decide +kernel
theorem subd9_3_82 : subd9_3 [-2, 3, -5] = true := by decide +kernel
theorem subd9_3_83 : subd9_3 [-2, 3, -4] = true := by decide +kernel
theorem subd9_3_84 : subd9_3 [-2, 3, -3] = true := by decide +kernel
theorem subd9_3_85 : subd9_3 [-2, 3, -2] = true := by decide +kernel
theorem subd9_3_86 : subd9_3 [-2, 3, -1] = true := by decide +kernel
theorem subd9_3_87 : subd9_3 [-2, 3, 0] = true := by decide +kernel
theorem subd9_3_88 : subd9_3 [-2, 3, 1] = true := by decide +kernel
theorem subd9_3_89 : subd9_3 [-2, 3, 2] = true := by decide +kernel
theorem subd9_3_90 : subd9_3 [-2, 3, 3] = true := by decide +kernel
theorem subd9_3_91 : subd9_3 [-2, 3, 4] = true := by decide +kernel
theorem subd9_3_92 : subd9_3 [-2, 3, 5] = true := by decide +kernel
theorem subd9_3_93 : subd9_3 [-2, 3, 6] = true := by decide +kernel
theorem subd9_3_94 : subd9_3 [-2, 3, 7] = true := by decide +kernel
theorem subd9_3_95 : subd9_3 [-2, 4] = true := by decide +kernel
theorem sbd9_3_2 : ∀ q ∈ blkd9_3_2, subd9_3 q = true := by
  unfold blkd9_3_2
  exact List.forall_mem_cons.2 ⟨subd9_3_64, List.forall_mem_cons.2 ⟨subd9_3_65, List.forall_mem_cons.2 ⟨subd9_3_66, List.forall_mem_cons.2 ⟨subd9_3_67, List.forall_mem_cons.2 ⟨subd9_3_68, List.forall_mem_cons.2 ⟨subd9_3_69, List.forall_mem_cons.2 ⟨subd9_3_70, List.forall_mem_cons.2 ⟨subd9_3_71, List.forall_mem_cons.2 ⟨subd9_3_72, List.forall_mem_cons.2 ⟨subd9_3_73, List.forall_mem_cons.2 ⟨subd9_3_74, List.forall_mem_cons.2 ⟨subd9_3_75, List.forall_mem_cons.2 ⟨subd9_3_76, List.forall_mem_cons.2 ⟨subd9_3_77, List.forall_mem_cons.2 ⟨subd9_3_78, List.forall_mem_cons.2 ⟨subd9_3_79, List.forall_mem_cons.2 ⟨subd9_3_80, List.forall_mem_cons.2 ⟨subd9_3_81, List.forall_mem_cons.2 ⟨subd9_3_82, List.forall_mem_cons.2 ⟨subd9_3_83, List.forall_mem_cons.2 ⟨subd9_3_84, List.forall_mem_cons.2 ⟨subd9_3_85, List.forall_mem_cons.2 ⟨subd9_3_86, List.forall_mem_cons.2 ⟨subd9_3_87, List.forall_mem_cons.2 ⟨subd9_3_88, List.forall_mem_cons.2 ⟨subd9_3_89, List.forall_mem_cons.2 ⟨subd9_3_90, List.forall_mem_cons.2 ⟨subd9_3_91, List.forall_mem_cons.2 ⟨subd9_3_92, List.forall_mem_cons.2 ⟨subd9_3_93, List.forall_mem_cons.2 ⟨subd9_3_94, List.forall_mem_cons.2 ⟨subd9_3_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_96 : subd9_3 [-2, 5] = true := by decide +kernel
theorem subd9_3_97 : subd9_3 [-1, -5] = true := by decide +kernel
theorem subd9_3_98 : subd9_3 [-1, -4] = true := by decide +kernel
theorem subd9_3_99 : subd9_3 [-1, -3] = true := by decide +kernel
theorem subd9_3_100 : subd9_3 [-1, -2, -7] = true := by decide +kernel
theorem subd9_3_101 : subd9_3 [-1, -2, -6] = true := by decide +kernel
theorem subd9_3_102 : subd9_3 [-1, -2, -5] = true := by decide +kernel
theorem subd9_3_103 : subd9_3 [-1, -2, -4] = true := by decide +kernel
theorem subd9_3_104 : subd9_3 [-1, -2, -3] = true := by decide +kernel
theorem subd9_3_105 : subd9_3 [-1, -2, -2] = true := by decide +kernel
theorem subd9_3_106 : subd9_3 [-1, -2, -1] = true := by decide +kernel
theorem subd9_3_107 : subd9_3 [-1, -2, 0] = true := by decide +kernel
theorem subd9_3_108 : subd9_3 [-1, -2, 1] = true := by decide +kernel
theorem subd9_3_109 : subd9_3 [-1, -2, 2] = true := by decide +kernel
theorem subd9_3_110 : subd9_3 [-1, -2, 3] = true := by decide +kernel
theorem subd9_3_111 : subd9_3 [-1, -2, 4] = true := by decide +kernel
theorem subd9_3_112 : subd9_3 [-1, -2, 5] = true := by decide +kernel
theorem subd9_3_113 : subd9_3 [-1, -2, 6] = true := by decide +kernel
theorem subd9_3_114 : subd9_3 [-1, -1, -8] = true := by decide +kernel
theorem subd9_3_115 : subd9_3 [-1, -1, -7] = true := by decide +kernel
theorem subd9_3_116 : subd9_3 [-1, -1, -6] = true := by decide +kernel
theorem subd9_3_117 : subd9_3 [-1, -1, -5] = true := by decide +kernel
theorem subd9_3_118 : subd9_3 [-1, -1, -4] = true := by decide +kernel
theorem subd9_3_119 : subd9_3 [-1, -1, -3] = true := by decide +kernel
theorem subd9_3_120 : subd9_3 [-1, -1, -2] = true := by decide +kernel
theorem subd9_3_121 : subd9_3 [-1, -1, -1] = true := by decide +kernel
theorem subd9_3_122 : subd9_3 [-1, -1, 0] = true := by decide +kernel
theorem subd9_3_123 : subd9_3 [-1, -1, 1] = true := by decide +kernel
theorem subd9_3_124 : subd9_3 [-1, -1, 2] = true := by decide +kernel
theorem subd9_3_125 : subd9_3 [-1, -1, 3] = true := by decide +kernel
theorem subd9_3_126 : subd9_3 [-1, -1, 4] = true := by decide +kernel
theorem subd9_3_127 : subd9_3 [-1, -1, 5] = true := by decide +kernel
theorem sbd9_3_3 : ∀ q ∈ blkd9_3_3, subd9_3 q = true := by
  unfold blkd9_3_3
  exact List.forall_mem_cons.2 ⟨subd9_3_96, List.forall_mem_cons.2 ⟨subd9_3_97, List.forall_mem_cons.2 ⟨subd9_3_98, List.forall_mem_cons.2 ⟨subd9_3_99, List.forall_mem_cons.2 ⟨subd9_3_100, List.forall_mem_cons.2 ⟨subd9_3_101, List.forall_mem_cons.2 ⟨subd9_3_102, List.forall_mem_cons.2 ⟨subd9_3_103, List.forall_mem_cons.2 ⟨subd9_3_104, List.forall_mem_cons.2 ⟨subd9_3_105, List.forall_mem_cons.2 ⟨subd9_3_106, List.forall_mem_cons.2 ⟨subd9_3_107, List.forall_mem_cons.2 ⟨subd9_3_108, List.forall_mem_cons.2 ⟨subd9_3_109, List.forall_mem_cons.2 ⟨subd9_3_110, List.forall_mem_cons.2 ⟨subd9_3_111, List.forall_mem_cons.2 ⟨subd9_3_112, List.forall_mem_cons.2 ⟨subd9_3_113, List.forall_mem_cons.2 ⟨subd9_3_114, List.forall_mem_cons.2 ⟨subd9_3_115, List.forall_mem_cons.2 ⟨subd9_3_116, List.forall_mem_cons.2 ⟨subd9_3_117, List.forall_mem_cons.2 ⟨subd9_3_118, List.forall_mem_cons.2 ⟨subd9_3_119, List.forall_mem_cons.2 ⟨subd9_3_120, List.forall_mem_cons.2 ⟨subd9_3_121, List.forall_mem_cons.2 ⟨subd9_3_122, List.forall_mem_cons.2 ⟨subd9_3_123, List.forall_mem_cons.2 ⟨subd9_3_124, List.forall_mem_cons.2 ⟨subd9_3_125, List.forall_mem_cons.2 ⟨subd9_3_126, List.forall_mem_cons.2 ⟨subd9_3_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_128 : subd9_3 [-1, -1, 6] = true := by decide +kernel
theorem subd9_3_129 : subd9_3 [-1, -1, 7] = true := by decide +kernel
theorem subd9_3_130 : subd9_3 [-1, 0, -8] = true := by decide +kernel
theorem subd9_3_131 : subd9_3 [-1, 0, -7] = true := by decide +kernel
theorem subd9_3_132 : subd9_3 [-1, 0, -6] = true := by decide +kernel
theorem subd9_3_133 : subd9_3 [-1, 0, -5] = true := by decide +kernel
theorem subd9_3_134 : subd9_3 [-1, 0, -4] = true := by decide +kernel
theorem subd9_3_135 : subd9_3 [-1, 0, -3] = true := by decide +kernel
theorem subd9_3_136 : subd9_3 [-1, 0, -2] = true := by decide +kernel
theorem subd9_3_137 : subd9_3 [-1, 0, -1] = true := by decide +kernel
theorem subd9_3_138 : subd9_3 [-1, 0, 0] = true := by decide +kernel
theorem subd9_3_139 : subd9_3 [-1, 0, 1] = true := by decide +kernel
theorem subd9_3_140 : subd9_3 [-1, 0, 2] = true := by decide +kernel
theorem subd9_3_141 : subd9_3 [-1, 0, 3] = true := by decide +kernel
theorem subd9_3_142 : subd9_3 [-1, 0, 4] = true := by decide +kernel
theorem subd9_3_143 : subd9_3 [-1, 0, 5] = true := by decide +kernel
theorem subd9_3_144 : subd9_3 [-1, 0, 6] = true := by decide +kernel
theorem subd9_3_145 : subd9_3 [-1, 0, 7] = true := by decide +kernel
theorem subd9_3_146 : subd9_3 [-1, 1, -8] = true := by decide +kernel
theorem subd9_3_147 : subd9_3 [-1, 1, -7] = true := by decide +kernel
theorem subd9_3_148 : subd9_3 [-1, 1, -6] = true := by decide +kernel
theorem subd9_3_149 : subd9_3 [-1, 1, -5] = true := by decide +kernel
theorem subd9_3_150 : subd9_3 [-1, 1, -4] = true := by decide +kernel
theorem subd9_3_151 : subd9_3 [-1, 1, -3] = true := by decide +kernel
theorem subd9_3_152 : subd9_3 [-1, 1, -2] = true := by decide +kernel
theorem subd9_3_153 : subd9_3 [-1, 1, -1] = true := by decide +kernel
theorem subd9_3_154 : subd9_3 [-1, 1, 0] = true := by decide +kernel
theorem subd9_3_155 : subd9_3 [-1, 1, 1] = true := by decide +kernel
theorem subd9_3_156 : subd9_3 [-1, 1, 2] = true := by decide +kernel
theorem subd9_3_157 : subd9_3 [-1, 1, 3] = true := by decide +kernel
theorem subd9_3_158 : subd9_3 [-1, 1, 4] = true := by decide +kernel
theorem subd9_3_159 : subd9_3 [-1, 1, 5] = true := by decide +kernel
theorem sbd9_3_4 : ∀ q ∈ blkd9_3_4, subd9_3 q = true := by
  unfold blkd9_3_4
  exact List.forall_mem_cons.2 ⟨subd9_3_128, List.forall_mem_cons.2 ⟨subd9_3_129, List.forall_mem_cons.2 ⟨subd9_3_130, List.forall_mem_cons.2 ⟨subd9_3_131, List.forall_mem_cons.2 ⟨subd9_3_132, List.forall_mem_cons.2 ⟨subd9_3_133, List.forall_mem_cons.2 ⟨subd9_3_134, List.forall_mem_cons.2 ⟨subd9_3_135, List.forall_mem_cons.2 ⟨subd9_3_136, List.forall_mem_cons.2 ⟨subd9_3_137, List.forall_mem_cons.2 ⟨subd9_3_138, List.forall_mem_cons.2 ⟨subd9_3_139, List.forall_mem_cons.2 ⟨subd9_3_140, List.forall_mem_cons.2 ⟨subd9_3_141, List.forall_mem_cons.2 ⟨subd9_3_142, List.forall_mem_cons.2 ⟨subd9_3_143, List.forall_mem_cons.2 ⟨subd9_3_144, List.forall_mem_cons.2 ⟨subd9_3_145, List.forall_mem_cons.2 ⟨subd9_3_146, List.forall_mem_cons.2 ⟨subd9_3_147, List.forall_mem_cons.2 ⟨subd9_3_148, List.forall_mem_cons.2 ⟨subd9_3_149, List.forall_mem_cons.2 ⟨subd9_3_150, List.forall_mem_cons.2 ⟨subd9_3_151, List.forall_mem_cons.2 ⟨subd9_3_152, List.forall_mem_cons.2 ⟨subd9_3_153, List.forall_mem_cons.2 ⟨subd9_3_154, List.forall_mem_cons.2 ⟨subd9_3_155, List.forall_mem_cons.2 ⟨subd9_3_156, List.forall_mem_cons.2 ⟨subd9_3_157, List.forall_mem_cons.2 ⟨subd9_3_158, List.forall_mem_cons.2 ⟨subd9_3_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_160 : subd9_3 [-1, 1, 6] = true := by decide +kernel
theorem subd9_3_161 : subd9_3 [-1, 1, 7] = true := by decide +kernel
theorem subd9_3_162 : subd9_3 [-1, 1, 8] = true := by decide +kernel
theorem subd9_3_163 : subd9_3 [-1, 2, -7] = true := by decide +kernel
theorem subd9_3_164 : subd9_3 [-1, 2, -6] = true := by decide +kernel
theorem subd9_3_165 : subd9_3 [-1, 2, -5] = true := by decide +kernel
theorem subd9_3_166 : subd9_3 [-1, 2, -4] = true := by decide +kernel
theorem subd9_3_167 : subd9_3 [-1, 2, -3] = true := by decide +kernel
theorem subd9_3_168 : subd9_3 [-1, 2, -2] = true := by decide +kernel
theorem subd9_3_169 : subd9_3 [-1, 2, -1] = true := by decide +kernel
theorem subd9_3_170 : subd9_3 [-1, 2, 0] = true := by decide +kernel
theorem subd9_3_171 : subd9_3 [-1, 2, 1] = true := by decide +kernel
theorem subd9_3_172 : subd9_3 [-1, 2, 2] = true := by decide +kernel
theorem subd9_3_173 : subd9_3 [-1, 2, 3] = true := by decide +kernel
theorem subd9_3_174 : subd9_3 [-1, 2, 4] = true := by decide +kernel
theorem subd9_3_175 : subd9_3 [-1, 2, 5] = true := by decide +kernel
theorem subd9_3_176 : subd9_3 [-1, 2, 6] = true := by decide +kernel
theorem subd9_3_177 : subd9_3 [-1, 2, 7] = true := by decide +kernel
theorem subd9_3_178 : subd9_3 [-1, 3, -7] = true := by decide +kernel
theorem subd9_3_179 : subd9_3 [-1, 3, -6] = true := by decide +kernel
theorem subd9_3_180 : subd9_3 [-1, 3, -5] = true := by decide +kernel
theorem subd9_3_181 : subd9_3 [-1, 3, -4] = true := by decide +kernel
theorem subd9_3_182 : subd9_3 [-1, 3, -3] = true := by decide +kernel
theorem subd9_3_183 : subd9_3 [-1, 3, -2] = true := by decide +kernel
theorem subd9_3_184 : subd9_3 [-1, 3, -1] = true := by decide +kernel
theorem subd9_3_185 : subd9_3 [-1, 3, 0] = true := by decide +kernel
theorem subd9_3_186 : subd9_3 [-1, 3, 1] = true := by decide +kernel
theorem subd9_3_187 : subd9_3 [-1, 3, 2] = true := by decide +kernel
theorem subd9_3_188 : subd9_3 [-1, 3, 3] = true := by decide +kernel
theorem subd9_3_189 : subd9_3 [-1, 3, 4] = true := by decide +kernel
theorem subd9_3_190 : subd9_3 [-1, 3, 5] = true := by decide +kernel
theorem subd9_3_191 : subd9_3 [-1, 3, 6] = true := by decide +kernel
theorem sbd9_3_5 : ∀ q ∈ blkd9_3_5, subd9_3 q = true := by
  unfold blkd9_3_5
  exact List.forall_mem_cons.2 ⟨subd9_3_160, List.forall_mem_cons.2 ⟨subd9_3_161, List.forall_mem_cons.2 ⟨subd9_3_162, List.forall_mem_cons.2 ⟨subd9_3_163, List.forall_mem_cons.2 ⟨subd9_3_164, List.forall_mem_cons.2 ⟨subd9_3_165, List.forall_mem_cons.2 ⟨subd9_3_166, List.forall_mem_cons.2 ⟨subd9_3_167, List.forall_mem_cons.2 ⟨subd9_3_168, List.forall_mem_cons.2 ⟨subd9_3_169, List.forall_mem_cons.2 ⟨subd9_3_170, List.forall_mem_cons.2 ⟨subd9_3_171, List.forall_mem_cons.2 ⟨subd9_3_172, List.forall_mem_cons.2 ⟨subd9_3_173, List.forall_mem_cons.2 ⟨subd9_3_174, List.forall_mem_cons.2 ⟨subd9_3_175, List.forall_mem_cons.2 ⟨subd9_3_176, List.forall_mem_cons.2 ⟨subd9_3_177, List.forall_mem_cons.2 ⟨subd9_3_178, List.forall_mem_cons.2 ⟨subd9_3_179, List.forall_mem_cons.2 ⟨subd9_3_180, List.forall_mem_cons.2 ⟨subd9_3_181, List.forall_mem_cons.2 ⟨subd9_3_182, List.forall_mem_cons.2 ⟨subd9_3_183, List.forall_mem_cons.2 ⟨subd9_3_184, List.forall_mem_cons.2 ⟨subd9_3_185, List.forall_mem_cons.2 ⟨subd9_3_186, List.forall_mem_cons.2 ⟨subd9_3_187, List.forall_mem_cons.2 ⟨subd9_3_188, List.forall_mem_cons.2 ⟨subd9_3_189, List.forall_mem_cons.2 ⟨subd9_3_190, List.forall_mem_cons.2 ⟨subd9_3_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C129
