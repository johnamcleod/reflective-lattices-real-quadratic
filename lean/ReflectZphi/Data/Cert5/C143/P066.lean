import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd19_1_288 : subd19_1 [-3, 3, 6] = true := by decide +kernel
theorem subd19_1_289 : subd19_1 [-3, 3, 7] = true := by decide +kernel
theorem subd19_1_290 : subd19_1 [-3, 3, 8] = true := by decide +kernel
theorem subd19_1_291 : subd19_1 [-3, 3, 9] = true := by decide +kernel
theorem subd19_1_292 : subd19_1 [-3, 4, -4] = true := by decide +kernel
theorem subd19_1_293 : subd19_1 [-3, 4, -3] = true := by decide +kernel
theorem subd19_1_294 : subd19_1 [-3, 4, -2] = true := by decide +kernel
theorem subd19_1_295 : subd19_1 [-3, 4, -1] = true := by decide +kernel
theorem subd19_1_296 : subd19_1 [-3, 4, 0] = true := by decide +kernel
theorem subd19_1_297 : subd19_1 [-3, 4, 1] = true := by decide +kernel
theorem subd19_1_298 : subd19_1 [-3, 4, 2] = true := by decide +kernel
theorem subd19_1_299 : subd19_1 [-3, 4, 3] = true := by decide +kernel
theorem subd19_1_300 : subd19_1 [-3, 4, 4] = true := by decide +kernel
theorem subd19_1_301 : subd19_1 [-3, 4, 5] = true := by decide +kernel
theorem subd19_1_302 : subd19_1 [-3, 4, 6] = true := by decide +kernel
theorem subd19_1_303 : subd19_1 [-3, 4, 7] = true := by decide +kernel
theorem subd19_1_304 : subd19_1 [-3, 4, 8] = true := by decide +kernel
theorem subd19_1_305 : subd19_1 [-3, 4, 9] = true := by decide +kernel
theorem subd19_1_306 : subd19_1 [-3, 5] = true := by decide +kernel
theorem subd19_1_307 : subd19_1 [-3, 6] = true := by decide +kernel
theorem subd19_1_308 : subd19_1 [-3, 7] = true := by decide +kernel
theorem subd19_1_309 : subd19_1 [-3, 8] = true := by decide +kernel
theorem subd19_1_310 : subd19_1 [-2, -10] = true := by decide +kernel
theorem subd19_1_311 : subd19_1 [-2, -9] = true := by decide +kernel
theorem subd19_1_312 : subd19_1 [-2, -8] = true := by decide +kernel
theorem subd19_1_313 : subd19_1 [-2, -7] = true := by decide +kernel
theorem subd19_1_314 : subd19_1 [-2, -6] = true := by decide +kernel
theorem subd19_1_315 : subd19_1 [-2, -5] = true := by decide +kernel
theorem subd19_1_316 : subd19_1 [-2, -4, -8] = true := by decide +kernel
theorem subd19_1_317 : subd19_1 [-2, -4, -7] = true := by decide +kernel
theorem subd19_1_318 : subd19_1 [-2, -4, -6] = true := by decide +kernel
theorem subd19_1_319 : subd19_1 [-2, -4, -5] = true := by decide +kernel
theorem sbd19_1_9 : ∀ q ∈ blkd19_1_9, subd19_1 q = true := by
  unfold blkd19_1_9
  exact List.forall_mem_cons.2 ⟨subd19_1_288, List.forall_mem_cons.2 ⟨subd19_1_289, List.forall_mem_cons.2 ⟨subd19_1_290, List.forall_mem_cons.2 ⟨subd19_1_291, List.forall_mem_cons.2 ⟨subd19_1_292, List.forall_mem_cons.2 ⟨subd19_1_293, List.forall_mem_cons.2 ⟨subd19_1_294, List.forall_mem_cons.2 ⟨subd19_1_295, List.forall_mem_cons.2 ⟨subd19_1_296, List.forall_mem_cons.2 ⟨subd19_1_297, List.forall_mem_cons.2 ⟨subd19_1_298, List.forall_mem_cons.2 ⟨subd19_1_299, List.forall_mem_cons.2 ⟨subd19_1_300, List.forall_mem_cons.2 ⟨subd19_1_301, List.forall_mem_cons.2 ⟨subd19_1_302, List.forall_mem_cons.2 ⟨subd19_1_303, List.forall_mem_cons.2 ⟨subd19_1_304, List.forall_mem_cons.2 ⟨subd19_1_305, List.forall_mem_cons.2 ⟨subd19_1_306, List.forall_mem_cons.2 ⟨subd19_1_307, List.forall_mem_cons.2 ⟨subd19_1_308, List.forall_mem_cons.2 ⟨subd19_1_309, List.forall_mem_cons.2 ⟨subd19_1_310, List.forall_mem_cons.2 ⟨subd19_1_311, List.forall_mem_cons.2 ⟨subd19_1_312, List.forall_mem_cons.2 ⟨subd19_1_313, List.forall_mem_cons.2 ⟨subd19_1_314, List.forall_mem_cons.2 ⟨subd19_1_315, List.forall_mem_cons.2 ⟨subd19_1_316, List.forall_mem_cons.2 ⟨subd19_1_317, List.forall_mem_cons.2 ⟨subd19_1_318, List.forall_mem_cons.2 ⟨subd19_1_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_1_320 : subd19_1 [-2, -4, -4] = true := by decide +kernel
theorem subd19_1_321 : subd19_1 [-2, -4, -3] = true := by decide +kernel
theorem subd19_1_322 : subd19_1 [-2, -4, -2] = true := by decide +kernel
theorem subd19_1_323 : subd19_1 [-2, -4, -1] = true := by decide +kernel
theorem subd19_1_324 : subd19_1 [-2, -4, 0] = true := by decide +kernel
theorem subd19_1_325 : subd19_1 [-2, -4, 1] = true := by decide +kernel
theorem subd19_1_326 : subd19_1 [-2, -4, 2] = true := by decide +kernel
theorem subd19_1_327 : subd19_1 [-2, -4, 3] = true := by decide +kernel
theorem subd19_1_328 : subd19_1 [-2, -4, 4] = true := by decide +kernel
theorem subd19_1_329 : subd19_1 [-2, -4, 5] = true := by decide +kernel
theorem subd19_1_330 : subd19_1 [-2, -4, 6] = true := by decide +kernel
theorem subd19_1_331 : subd19_1 [-2, -3, -8] = true := by decide +kernel
theorem subd19_1_332 : subd19_1 [-2, -3, -7] = true := by decide +kernel
theorem subd19_1_333 : subd19_1 [-2, -3, -6] = true := by decide +kernel
theorem subd19_1_334 : subd19_1 [-2, -3, -5] = true := by decide +kernel
theorem subd19_1_335 : subd19_1 [-2, -3, -4] = true := by decide +kernel
theorem subd19_1_336 : subd19_1 [-2, -3, -3] = true := by decide +kernel
theorem subd19_1_337 : subd19_1 [-2, -3, -2] = true := by decide +kernel
theorem subd19_1_338 : subd19_1 [-2, -3, -1] = true := by decide +kernel
theorem subd19_1_339 : subd19_1 [-2, -3, 0] = true := by decide +kernel
theorem subd19_1_340 : subd19_1 [-2, -3, 1] = true := by decide +kernel
theorem subd19_1_341 : subd19_1 [-2, -3, 2] = true := by decide +kernel
theorem subd19_1_342 : subd19_1 [-2, -3, 3] = true := by decide +kernel
theorem subd19_1_343 : subd19_1 [-2, -3, 4] = true := by decide +kernel
theorem subd19_1_344 : subd19_1 [-2, -3, 5] = true := by decide +kernel
theorem subd19_1_345 : subd19_1 [-2, -3, 6] = true := by decide +kernel
theorem subd19_1_346 : subd19_1 [-2, -2, -7] = true := by decide +kernel
theorem subd19_1_347 : subd19_1 [-2, -2, -6] = true := by decide +kernel
theorem subd19_1_348 : subd19_1 [-2, -2, -5] = true := by decide +kernel
theorem subd19_1_349 : subd19_1 [-2, -2, -4] = true := by decide +kernel
theorem subd19_1_350 : subd19_1 [-2, -2, -3] = true := by decide +kernel
theorem subd19_1_351 : subd19_1 [-2, -2, -2] = true := by decide +kernel
theorem sbd19_1_10 : ∀ q ∈ blkd19_1_10, subd19_1 q = true := by
  unfold blkd19_1_10
  exact List.forall_mem_cons.2 ⟨subd19_1_320, List.forall_mem_cons.2 ⟨subd19_1_321, List.forall_mem_cons.2 ⟨subd19_1_322, List.forall_mem_cons.2 ⟨subd19_1_323, List.forall_mem_cons.2 ⟨subd19_1_324, List.forall_mem_cons.2 ⟨subd19_1_325, List.forall_mem_cons.2 ⟨subd19_1_326, List.forall_mem_cons.2 ⟨subd19_1_327, List.forall_mem_cons.2 ⟨subd19_1_328, List.forall_mem_cons.2 ⟨subd19_1_329, List.forall_mem_cons.2 ⟨subd19_1_330, List.forall_mem_cons.2 ⟨subd19_1_331, List.forall_mem_cons.2 ⟨subd19_1_332, List.forall_mem_cons.2 ⟨subd19_1_333, List.forall_mem_cons.2 ⟨subd19_1_334, List.forall_mem_cons.2 ⟨subd19_1_335, List.forall_mem_cons.2 ⟨subd19_1_336, List.forall_mem_cons.2 ⟨subd19_1_337, List.forall_mem_cons.2 ⟨subd19_1_338, List.forall_mem_cons.2 ⟨subd19_1_339, List.forall_mem_cons.2 ⟨subd19_1_340, List.forall_mem_cons.2 ⟨subd19_1_341, List.forall_mem_cons.2 ⟨subd19_1_342, List.forall_mem_cons.2 ⟨subd19_1_343, List.forall_mem_cons.2 ⟨subd19_1_344, List.forall_mem_cons.2 ⟨subd19_1_345, List.forall_mem_cons.2 ⟨subd19_1_346, List.forall_mem_cons.2 ⟨subd19_1_347, List.forall_mem_cons.2 ⟨subd19_1_348, List.forall_mem_cons.2 ⟨subd19_1_349, List.forall_mem_cons.2 ⟨subd19_1_350, List.forall_mem_cons.2 ⟨subd19_1_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_1_352 : subd19_1 [-2, -2, -1] = true := by decide +kernel
theorem subd19_1_353 : subd19_1 [-2, -2, 0] = true := by decide +kernel
theorem subd19_1_354 : subd19_1 [-2, -2, 1] = true := by decide +kernel
theorem subd19_1_355 : subd19_1 [-2, -2, 2] = true := by decide +kernel
theorem subd19_1_356 : subd19_1 [-2, -2, 3] = true := by decide +kernel
theorem subd19_1_357 : subd19_1 [-2, -2, 4] = true := by decide +kernel
theorem subd19_1_358 : subd19_1 [-2, -2, 5] = true := by decide +kernel
theorem subd19_1_359 : subd19_1 [-2, -2, 6] = true := by decide +kernel
theorem subd19_1_360 : subd19_1 [-2, -2, 7] = true := by decide +kernel
theorem subd19_1_361 : subd19_1 [-2, -1, -7] = true := by decide +kernel
theorem subd19_1_362 : subd19_1 [-2, -1, -6] = true := by decide +kernel
theorem subd19_1_363 : subd19_1 [-2, -1, -5] = true := by decide +kernel
theorem subd19_1_364 : subd19_1 [-2, -1, -4] = true := by decide +kernel
theorem subd19_1_365 : subd19_1 [-2, -1, -3] = true := by decide +kernel
theorem subd19_1_366 : subd19_1 [-2, -1, -2] = true := by decide +kernel
theorem subd19_1_367 : subd19_1 [-2, -1, -1] = true := by decide +kernel
theorem subd19_1_368 : subd19_1 [-2, -1, 0] = true := by decide +kernel
theorem subd19_1_369 : subd19_1 [-2, -1, 1] = true := by decide +kernel
theorem subd19_1_370 : subd19_1 [-2, -1, 2] = true := by decide +kernel
theorem subd19_1_371 : subd19_1 [-2, -1, 3] = true := by decide +kernel
theorem subd19_1_372 : subd19_1 [-2, -1, 4] = true := by decide +kernel
theorem subd19_1_373 : subd19_1 [-2, -1, 5] = true := by decide +kernel
theorem subd19_1_374 : subd19_1 [-2, -1, 6] = true := by decide +kernel
theorem subd19_1_375 : subd19_1 [-2, -1, 7] = true := by decide +kernel
theorem subd19_1_376 : subd19_1 [-2, 0, -7] = true := by decide +kernel
theorem subd19_1_377 : subd19_1 [-2, 0, -6] = true := by decide +kernel
theorem subd19_1_378 : subd19_1 [-2, 0, -5] = true := by decide +kernel
theorem subd19_1_379 : subd19_1 [-2, 0, -4] = true := by decide +kernel
theorem subd19_1_380 : subd19_1 [-2, 0, -3] = true := by decide +kernel
theorem subd19_1_381 : subd19_1 [-2, 0, -2] = true := by decide +kernel
theorem subd19_1_382 : subd19_1 [-2, 0, -1] = true := by decide +kernel
theorem subd19_1_383 : subd19_1 [-2, 0, 0] = true := by decide +kernel
theorem sbd19_1_11 : ∀ q ∈ blkd19_1_11, subd19_1 q = true := by
  unfold blkd19_1_11
  exact List.forall_mem_cons.2 ⟨subd19_1_352, List.forall_mem_cons.2 ⟨subd19_1_353, List.forall_mem_cons.2 ⟨subd19_1_354, List.forall_mem_cons.2 ⟨subd19_1_355, List.forall_mem_cons.2 ⟨subd19_1_356, List.forall_mem_cons.2 ⟨subd19_1_357, List.forall_mem_cons.2 ⟨subd19_1_358, List.forall_mem_cons.2 ⟨subd19_1_359, List.forall_mem_cons.2 ⟨subd19_1_360, List.forall_mem_cons.2 ⟨subd19_1_361, List.forall_mem_cons.2 ⟨subd19_1_362, List.forall_mem_cons.2 ⟨subd19_1_363, List.forall_mem_cons.2 ⟨subd19_1_364, List.forall_mem_cons.2 ⟨subd19_1_365, List.forall_mem_cons.2 ⟨subd19_1_366, List.forall_mem_cons.2 ⟨subd19_1_367, List.forall_mem_cons.2 ⟨subd19_1_368, List.forall_mem_cons.2 ⟨subd19_1_369, List.forall_mem_cons.2 ⟨subd19_1_370, List.forall_mem_cons.2 ⟨subd19_1_371, List.forall_mem_cons.2 ⟨subd19_1_372, List.forall_mem_cons.2 ⟨subd19_1_373, List.forall_mem_cons.2 ⟨subd19_1_374, List.forall_mem_cons.2 ⟨subd19_1_375, List.forall_mem_cons.2 ⟨subd19_1_376, List.forall_mem_cons.2 ⟨subd19_1_377, List.forall_mem_cons.2 ⟨subd19_1_378, List.forall_mem_cons.2 ⟨subd19_1_379, List.forall_mem_cons.2 ⟨subd19_1_380, List.forall_mem_cons.2 ⟨subd19_1_381, List.forall_mem_cons.2 ⟨subd19_1_382, List.forall_mem_cons.2 ⟨subd19_1_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_1_384 : subd19_1 [-2, 0, 1] = true := by decide +kernel
theorem subd19_1_385 : subd19_1 [-2, 0, 2] = true := by decide +kernel
theorem subd19_1_386 : subd19_1 [-2, 0, 3] = true := by decide +kernel
theorem subd19_1_387 : subd19_1 [-2, 0, 4] = true := by decide +kernel
theorem subd19_1_388 : subd19_1 [-2, 0, 5] = true := by decide +kernel
theorem subd19_1_389 : subd19_1 [-2, 0, 6] = true := by decide +kernel
theorem subd19_1_390 : subd19_1 [-2, 0, 7] = true := by decide +kernel
theorem subd19_1_391 : subd19_1 [-2, 0, 8] = true := by decide +kernel
theorem subd19_1_392 : subd19_1 [-2, 1, -7] = true := by decide +kernel
theorem subd19_1_393 : subd19_1 [-2, 1, -6] = true := by decide +kernel
theorem subd19_1_394 : subd19_1 [-2, 1, -5] = true := by decide +kernel
theorem subd19_1_395 : subd19_1 [-2, 1, -4] = true := by decide +kernel
theorem subd19_1_396 : subd19_1 [-2, 1, -3] = true := by decide +kernel
theorem subd19_1_397 : subd19_1 [-2, 1, -2] = true := by decide +kernel
theorem subd19_1_398 : subd19_1 [-2, 1, -1] = true := by decide +kernel
theorem subd19_1_399 : subd19_1 [-2, 1, 0] = true := by decide +kernel
theorem subd19_1_400 : subd19_1 [-2, 1, 1] = true := by decide +kernel
theorem subd19_1_401 : subd19_1 [-2, 1, 2] = true := by decide +kernel
theorem subd19_1_402 : subd19_1 [-2, 1, 3] = true := by decide +kernel
theorem subd19_1_403 : subd19_1 [-2, 1, 4] = true := by decide +kernel
theorem subd19_1_404 : subd19_1 [-2, 1, 5] = true := by decide +kernel
theorem subd19_1_405 : subd19_1 [-2, 1, 6] = true := by decide +kernel
theorem subd19_1_406 : subd19_1 [-2, 1, 7] = true := by decide +kernel
theorem subd19_1_407 : subd19_1 [-2, 1, 8] = true := by decide +kernel
theorem subd19_1_408 : subd19_1 [-2, 2, -6] = true := by decide +kernel
theorem subd19_1_409 : subd19_1 [-2, 2, -5] = true := by decide +kernel
theorem subd19_1_410 : subd19_1 [-2, 2, -4] = true := by decide +kernel
theorem subd19_1_411 : subd19_1 [-2, 2, -3] = true := by decide +kernel
theorem subd19_1_412 : subd19_1 [-2, 2, -2] = true := by decide +kernel
theorem subd19_1_413 : subd19_1 [-2, 2, -1] = true := by decide +kernel
theorem subd19_1_414 : subd19_1 [-2, 2, 0] = true := by decide +kernel
theorem subd19_1_415 : subd19_1 [-2, 2, 1] = true := by decide +kernel
theorem sbd19_1_12 : ∀ q ∈ blkd19_1_12, subd19_1 q = true := by
  unfold blkd19_1_12
  exact List.forall_mem_cons.2 ⟨subd19_1_384, List.forall_mem_cons.2 ⟨subd19_1_385, List.forall_mem_cons.2 ⟨subd19_1_386, List.forall_mem_cons.2 ⟨subd19_1_387, List.forall_mem_cons.2 ⟨subd19_1_388, List.forall_mem_cons.2 ⟨subd19_1_389, List.forall_mem_cons.2 ⟨subd19_1_390, List.forall_mem_cons.2 ⟨subd19_1_391, List.forall_mem_cons.2 ⟨subd19_1_392, List.forall_mem_cons.2 ⟨subd19_1_393, List.forall_mem_cons.2 ⟨subd19_1_394, List.forall_mem_cons.2 ⟨subd19_1_395, List.forall_mem_cons.2 ⟨subd19_1_396, List.forall_mem_cons.2 ⟨subd19_1_397, List.forall_mem_cons.2 ⟨subd19_1_398, List.forall_mem_cons.2 ⟨subd19_1_399, List.forall_mem_cons.2 ⟨subd19_1_400, List.forall_mem_cons.2 ⟨subd19_1_401, List.forall_mem_cons.2 ⟨subd19_1_402, List.forall_mem_cons.2 ⟨subd19_1_403, List.forall_mem_cons.2 ⟨subd19_1_404, List.forall_mem_cons.2 ⟨subd19_1_405, List.forall_mem_cons.2 ⟨subd19_1_406, List.forall_mem_cons.2 ⟨subd19_1_407, List.forall_mem_cons.2 ⟨subd19_1_408, List.forall_mem_cons.2 ⟨subd19_1_409, List.forall_mem_cons.2 ⟨subd19_1_410, List.forall_mem_cons.2 ⟨subd19_1_411, List.forall_mem_cons.2 ⟨subd19_1_412, List.forall_mem_cons.2 ⟨subd19_1_413, List.forall_mem_cons.2 ⟨subd19_1_414, List.forall_mem_cons.2 ⟨subd19_1_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_1_416 : subd19_1 [-2, 2, 2] = true := by decide +kernel
theorem subd19_1_417 : subd19_1 [-2, 2, 3] = true := by decide +kernel
theorem subd19_1_418 : subd19_1 [-2, 2, 4] = true := by decide +kernel
theorem subd19_1_419 : subd19_1 [-2, 2, 5] = true := by decide +kernel
theorem subd19_1_420 : subd19_1 [-2, 2, 6] = true := by decide +kernel
theorem subd19_1_421 : subd19_1 [-2, 2, 7] = true := by decide +kernel
theorem subd19_1_422 : subd19_1 [-2, 2, 8] = true := by decide +kernel
theorem subd19_1_423 : subd19_1 [-2, 3, -6] = true := by decide +kernel
theorem subd19_1_424 : subd19_1 [-2, 3, -5] = true := by decide +kernel
theorem subd19_1_425 : subd19_1 [-2, 3, -4] = true := by decide +kernel
theorem subd19_1_426 : subd19_1 [-2, 3, -3] = true := by decide +kernel
theorem subd19_1_427 : subd19_1 [-2, 3, -2] = true := by decide +kernel
theorem subd19_1_428 : subd19_1 [-2, 3, -1] = true := by decide +kernel
theorem subd19_1_429 : subd19_1 [-2, 3, 0] = true := by decide +kernel
theorem subd19_1_430 : subd19_1 [-2, 3, 1] = true := by decide +kernel
theorem subd19_1_431 : subd19_1 [-2, 3, 2] = true := by decide +kernel
theorem subd19_1_432 : subd19_1 [-2, 3, 3] = true := by decide +kernel
theorem subd19_1_433 : subd19_1 [-2, 3, 4] = true := by decide +kernel
theorem subd19_1_434 : subd19_1 [-2, 3, 5] = true := by decide +kernel
theorem subd19_1_435 : subd19_1 [-2, 3, 6] = true := by decide +kernel
theorem subd19_1_436 : subd19_1 [-2, 3, 7] = true := by decide +kernel
theorem subd19_1_437 : subd19_1 [-2, 3, 8] = true := by decide +kernel
theorem subd19_1_438 : subd19_1 [-2, 4, -5] = true := by decide +kernel
theorem subd19_1_439 : subd19_1 [-2, 4, -4] = true := by decide +kernel
theorem subd19_1_440 : subd19_1 [-2, 4, -3] = true := by decide +kernel
theorem subd19_1_441 : subd19_1 [-2, 4, -2] = true := by decide +kernel
theorem subd19_1_442 : subd19_1 [-2, 4, -1] = true := by decide +kernel
theorem subd19_1_443 : subd19_1 [-2, 4, 0] = true := by decide +kernel
theorem subd19_1_444 : subd19_1 [-2, 4, 1] = true := by decide +kernel
theorem subd19_1_445 : subd19_1 [-2, 4, 2] = true := by decide +kernel
theorem subd19_1_446 : subd19_1 [-2, 4, 3] = true := by decide +kernel
theorem subd19_1_447 : subd19_1 [-2, 4, 4] = true := by decide +kernel
theorem sbd19_1_13 : ∀ q ∈ blkd19_1_13, subd19_1 q = true := by
  unfold blkd19_1_13
  exact List.forall_mem_cons.2 ⟨subd19_1_416, List.forall_mem_cons.2 ⟨subd19_1_417, List.forall_mem_cons.2 ⟨subd19_1_418, List.forall_mem_cons.2 ⟨subd19_1_419, List.forall_mem_cons.2 ⟨subd19_1_420, List.forall_mem_cons.2 ⟨subd19_1_421, List.forall_mem_cons.2 ⟨subd19_1_422, List.forall_mem_cons.2 ⟨subd19_1_423, List.forall_mem_cons.2 ⟨subd19_1_424, List.forall_mem_cons.2 ⟨subd19_1_425, List.forall_mem_cons.2 ⟨subd19_1_426, List.forall_mem_cons.2 ⟨subd19_1_427, List.forall_mem_cons.2 ⟨subd19_1_428, List.forall_mem_cons.2 ⟨subd19_1_429, List.forall_mem_cons.2 ⟨subd19_1_430, List.forall_mem_cons.2 ⟨subd19_1_431, List.forall_mem_cons.2 ⟨subd19_1_432, List.forall_mem_cons.2 ⟨subd19_1_433, List.forall_mem_cons.2 ⟨subd19_1_434, List.forall_mem_cons.2 ⟨subd19_1_435, List.forall_mem_cons.2 ⟨subd19_1_436, List.forall_mem_cons.2 ⟨subd19_1_437, List.forall_mem_cons.2 ⟨subd19_1_438, List.forall_mem_cons.2 ⟨subd19_1_439, List.forall_mem_cons.2 ⟨subd19_1_440, List.forall_mem_cons.2 ⟨subd19_1_441, List.forall_mem_cons.2 ⟨subd19_1_442, List.forall_mem_cons.2 ⟨subd19_1_443, List.forall_mem_cons.2 ⟨subd19_1_444, List.forall_mem_cons.2 ⟨subd19_1_445, List.forall_mem_cons.2 ⟨subd19_1_446, List.forall_mem_cons.2 ⟨subd19_1_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_1_448 : subd19_1 [-2, 4, 5] = true := by decide +kernel
theorem subd19_1_449 : subd19_1 [-2, 4, 6] = true := by decide +kernel
theorem subd19_1_450 : subd19_1 [-2, 4, 7] = true := by decide +kernel
theorem subd19_1_451 : subd19_1 [-2, 4, 8] = true := by decide +kernel
theorem subd19_1_452 : subd19_1 [-2, 5] = true := by decide +kernel
theorem subd19_1_453 : subd19_1 [-2, 6] = true := by decide +kernel
theorem subd19_1_454 : subd19_1 [-2, 7] = true := by decide +kernel
theorem subd19_1_455 : subd19_1 [-2, 8] = true := by decide +kernel
theorem subd19_1_456 : subd19_1 [-2, 9] = true := by decide +kernel
theorem subd19_1_457 : subd19_1 [-1, -10] = true := by decide +kernel
theorem subd19_1_458 : subd19_1 [-1, -9] = true := by decide +kernel
theorem subd19_1_459 : subd19_1 [-1, -8] = true := by decide +kernel
theorem subd19_1_460 : subd19_1 [-1, -7] = true := by decide +kernel
theorem subd19_1_461 : subd19_1 [-1, -6] = true := by decide +kernel
theorem subd19_1_462 : subd19_1 [-1, -5] = true := by decide +kernel
theorem subd19_1_463 : subd19_1 [-1, -4, -8] = true := by decide +kernel
theorem subd19_1_464 : subd19_1 [-1, -4, -7] = true := by decide +kernel
theorem subd19_1_465 : subd19_1 [-1, -4, -6] = true := by decide +kernel
theorem subd19_1_466 : subd19_1 [-1, -4, -5] = true := by decide +kernel
theorem subd19_1_467 : subd19_1 [-1, -4, -4] = true := by decide +kernel
theorem subd19_1_468 : subd19_1 [-1, -4, -3] = true := by decide +kernel
theorem subd19_1_469 : subd19_1 [-1, -4, -2] = true := by decide +kernel
theorem subd19_1_470 : subd19_1 [-1, -4, -1] = true := by decide +kernel
theorem subd19_1_471 : subd19_1 [-1, -4, 0] = true := by decide +kernel
theorem subd19_1_472 : subd19_1 [-1, -4, 1] = true := by decide +kernel
theorem subd19_1_473 : subd19_1 [-1, -4, 2] = true := by decide +kernel
theorem subd19_1_474 : subd19_1 [-1, -4, 3] = true := by decide +kernel
theorem subd19_1_475 : subd19_1 [-1, -4, 4] = true := by decide +kernel
theorem subd19_1_476 : subd19_1 [-1, -4, 5] = true := by decide +kernel
theorem subd19_1_477 : subd19_1 [-1, -3, -8] = true := by decide +kernel
theorem subd19_1_478 : subd19_1 [-1, -3, -7] = true := by decide +kernel
theorem subd19_1_479 : subd19_1 [-1, -3, -6] = true := by decide +kernel
theorem sbd19_1_14 : ∀ q ∈ blkd19_1_14, subd19_1 q = true := by
  unfold blkd19_1_14
  exact List.forall_mem_cons.2 ⟨subd19_1_448, List.forall_mem_cons.2 ⟨subd19_1_449, List.forall_mem_cons.2 ⟨subd19_1_450, List.forall_mem_cons.2 ⟨subd19_1_451, List.forall_mem_cons.2 ⟨subd19_1_452, List.forall_mem_cons.2 ⟨subd19_1_453, List.forall_mem_cons.2 ⟨subd19_1_454, List.forall_mem_cons.2 ⟨subd19_1_455, List.forall_mem_cons.2 ⟨subd19_1_456, List.forall_mem_cons.2 ⟨subd19_1_457, List.forall_mem_cons.2 ⟨subd19_1_458, List.forall_mem_cons.2 ⟨subd19_1_459, List.forall_mem_cons.2 ⟨subd19_1_460, List.forall_mem_cons.2 ⟨subd19_1_461, List.forall_mem_cons.2 ⟨subd19_1_462, List.forall_mem_cons.2 ⟨subd19_1_463, List.forall_mem_cons.2 ⟨subd19_1_464, List.forall_mem_cons.2 ⟨subd19_1_465, List.forall_mem_cons.2 ⟨subd19_1_466, List.forall_mem_cons.2 ⟨subd19_1_467, List.forall_mem_cons.2 ⟨subd19_1_468, List.forall_mem_cons.2 ⟨subd19_1_469, List.forall_mem_cons.2 ⟨subd19_1_470, List.forall_mem_cons.2 ⟨subd19_1_471, List.forall_mem_cons.2 ⟨subd19_1_472, List.forall_mem_cons.2 ⟨subd19_1_473, List.forall_mem_cons.2 ⟨subd19_1_474, List.forall_mem_cons.2 ⟨subd19_1_475, List.forall_mem_cons.2 ⟨subd19_1_476, List.forall_mem_cons.2 ⟨subd19_1_477, List.forall_mem_cons.2 ⟨subd19_1_478, List.forall_mem_cons.2 ⟨subd19_1_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_1_480 : subd19_1 [-1, -3, -5] = true := by decide +kernel
theorem subd19_1_481 : subd19_1 [-1, -3, -4] = true := by decide +kernel
theorem subd19_1_482 : subd19_1 [-1, -3, -3] = true := by decide +kernel
theorem subd19_1_483 : subd19_1 [-1, -3, -2] = true := by decide +kernel
theorem subd19_1_484 : subd19_1 [-1, -3, -1] = true := by decide +kernel
theorem subd19_1_485 : subd19_1 [-1, -3, 0] = true := by decide +kernel
theorem subd19_1_486 : subd19_1 [-1, -3, 1] = true := by decide +kernel
theorem subd19_1_487 : subd19_1 [-1, -3, 2] = true := by decide +kernel
theorem subd19_1_488 : subd19_1 [-1, -3, 3] = true := by decide +kernel
theorem subd19_1_489 : subd19_1 [-1, -3, 4] = true := by decide +kernel
theorem subd19_1_490 : subd19_1 [-1, -3, 5] = true := by decide +kernel
theorem subd19_1_491 : subd19_1 [-1, -3, 6] = true := by decide +kernel
theorem subd19_1_492 : subd19_1 [-1, -2, -8] = true := by decide +kernel
theorem subd19_1_493 : subd19_1 [-1, -2, -7] = true := by decide +kernel
theorem subd19_1_494 : subd19_1 [-1, -2, -6] = true := by decide +kernel
theorem subd19_1_495 : subd19_1 [-1, -2, -5] = true := by decide +kernel
theorem subd19_1_496 : subd19_1 [-1, -2, -4] = true := by decide +kernel
theorem subd19_1_497 : subd19_1 [-1, -2, -3] = true := by decide +kernel
theorem subd19_1_498 : subd19_1 [-1, -2, -2] = true := by decide +kernel
theorem subd19_1_499 : subd19_1 [-1, -2, -1] = true := by decide +kernel
theorem subd19_1_500 : subd19_1 [-1, -2, 0] = true := by decide +kernel
theorem subd19_1_501 : subd19_1 [-1, -2, 1] = true := by decide +kernel
theorem subd19_1_502 : subd19_1 [-1, -2, 2] = true := by decide +kernel
theorem subd19_1_503 : subd19_1 [-1, -2, 3] = true := by decide +kernel
theorem subd19_1_504 : subd19_1 [-1, -2, 4] = true := by decide +kernel
theorem subd19_1_505 : subd19_1 [-1, -2, 5] = true := by decide +kernel
theorem subd19_1_506 : subd19_1 [-1, -2, 6] = true := by decide +kernel
theorem subd19_1_507 : subd19_1 [-1, -2, 7] = true := by decide +kernel
theorem subd19_1_508 : subd19_1 [-1, -1, -8] = true := by decide +kernel
theorem subd19_1_509 : subd19_1 [-1, -1, -7] = true := by decide +kernel
theorem subd19_1_510 : subd19_1 [-1, -1, -6] = true := by decide +kernel
theorem subd19_1_511 : subd19_1 [-1, -1, -5] = true := by decide +kernel
theorem sbd19_1_15 : ∀ q ∈ blkd19_1_15, subd19_1 q = true := by
  unfold blkd19_1_15
  exact List.forall_mem_cons.2 ⟨subd19_1_480, List.forall_mem_cons.2 ⟨subd19_1_481, List.forall_mem_cons.2 ⟨subd19_1_482, List.forall_mem_cons.2 ⟨subd19_1_483, List.forall_mem_cons.2 ⟨subd19_1_484, List.forall_mem_cons.2 ⟨subd19_1_485, List.forall_mem_cons.2 ⟨subd19_1_486, List.forall_mem_cons.2 ⟨subd19_1_487, List.forall_mem_cons.2 ⟨subd19_1_488, List.forall_mem_cons.2 ⟨subd19_1_489, List.forall_mem_cons.2 ⟨subd19_1_490, List.forall_mem_cons.2 ⟨subd19_1_491, List.forall_mem_cons.2 ⟨subd19_1_492, List.forall_mem_cons.2 ⟨subd19_1_493, List.forall_mem_cons.2 ⟨subd19_1_494, List.forall_mem_cons.2 ⟨subd19_1_495, List.forall_mem_cons.2 ⟨subd19_1_496, List.forall_mem_cons.2 ⟨subd19_1_497, List.forall_mem_cons.2 ⟨subd19_1_498, List.forall_mem_cons.2 ⟨subd19_1_499, List.forall_mem_cons.2 ⟨subd19_1_500, List.forall_mem_cons.2 ⟨subd19_1_501, List.forall_mem_cons.2 ⟨subd19_1_502, List.forall_mem_cons.2 ⟨subd19_1_503, List.forall_mem_cons.2 ⟨subd19_1_504, List.forall_mem_cons.2 ⟨subd19_1_505, List.forall_mem_cons.2 ⟨subd19_1_506, List.forall_mem_cons.2 ⟨subd19_1_507, List.forall_mem_cons.2 ⟨subd19_1_508, List.forall_mem_cons.2 ⟨subd19_1_509, List.forall_mem_cons.2 ⟨subd19_1_510, List.forall_mem_cons.2 ⟨subd19_1_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_1_512 : subd19_1 [-1, -1, -4] = true := by decide +kernel
theorem subd19_1_513 : subd19_1 [-1, -1, -3] = true := by decide +kernel
theorem subd19_1_514 : subd19_1 [-1, -1, -2] = true := by decide +kernel
theorem subd19_1_515 : subd19_1 [-1, -1, -1] = true := by decide +kernel
theorem subd19_1_516 : subd19_1 [-1, -1, 0] = true := by decide +kernel
theorem subd19_1_517 : subd19_1 [-1, -1, 1] = true := by decide +kernel
theorem subd19_1_518 : subd19_1 [-1, -1, 2] = true := by decide +kernel
theorem subd19_1_519 : subd19_1 [-1, -1, 3] = true := by decide +kernel
theorem subd19_1_520 : subd19_1 [-1, -1, 4] = true := by decide +kernel
theorem subd19_1_521 : subd19_1 [-1, -1, 5] = true := by decide +kernel
theorem subd19_1_522 : subd19_1 [-1, -1, 6] = true := by decide +kernel
theorem subd19_1_523 : subd19_1 [-1, -1, 7] = true := by decide +kernel
theorem subd19_1_524 : subd19_1 [-1, 0, -8] = true := by decide +kernel
theorem subd19_1_525 : subd19_1 [-1, 0, -7] = true := by decide +kernel
theorem subd19_1_526 : subd19_1 [-1, 0, -6] = true := by decide +kernel
theorem subd19_1_527 : subd19_1 [-1, 0, -5] = true := by decide +kernel
theorem subd19_1_528 : subd19_1 [-1, 0, -4] = true := by decide +kernel
theorem subd19_1_529 : subd19_1 [-1, 0, -3] = true := by decide +kernel
theorem subd19_1_530 : subd19_1 [-1, 0, -2] = true := by decide +kernel
theorem subd19_1_531 : subd19_1 [-1, 0, -1] = true := by decide +kernel
theorem subd19_1_532 : subd19_1 [-1, 0, 0] = true := by decide +kernel
theorem subd19_1_533 : subd19_1 [-1, 0, 1] = true := by decide +kernel
theorem subd19_1_534 : subd19_1 [-1, 0, 2] = true := by decide +kernel
theorem subd19_1_535 : subd19_1 [-1, 0, 3] = true := by decide +kernel
theorem subd19_1_536 : subd19_1 [-1, 0, 4] = true := by decide +kernel
theorem subd19_1_537 : subd19_1 [-1, 0, 5] = true := by decide +kernel
theorem subd19_1_538 : subd19_1 [-1, 0, 6] = true := by decide +kernel
theorem subd19_1_539 : subd19_1 [-1, 0, 7] = true := by decide +kernel
theorem subd19_1_540 : subd19_1 [-1, 0, 8] = true := by decide +kernel
theorem subd19_1_541 : subd19_1 [-1, 1, -7] = true := by decide +kernel
theorem subd19_1_542 : subd19_1 [-1, 1, -6] = true := by decide +kernel
theorem subd19_1_543 : subd19_1 [-1, 1, -5] = true := by decide +kernel
theorem sbd19_1_16 : ∀ q ∈ blkd19_1_16, subd19_1 q = true := by
  unfold blkd19_1_16
  exact List.forall_mem_cons.2 ⟨subd19_1_512, List.forall_mem_cons.2 ⟨subd19_1_513, List.forall_mem_cons.2 ⟨subd19_1_514, List.forall_mem_cons.2 ⟨subd19_1_515, List.forall_mem_cons.2 ⟨subd19_1_516, List.forall_mem_cons.2 ⟨subd19_1_517, List.forall_mem_cons.2 ⟨subd19_1_518, List.forall_mem_cons.2 ⟨subd19_1_519, List.forall_mem_cons.2 ⟨subd19_1_520, List.forall_mem_cons.2 ⟨subd19_1_521, List.forall_mem_cons.2 ⟨subd19_1_522, List.forall_mem_cons.2 ⟨subd19_1_523, List.forall_mem_cons.2 ⟨subd19_1_524, List.forall_mem_cons.2 ⟨subd19_1_525, List.forall_mem_cons.2 ⟨subd19_1_526, List.forall_mem_cons.2 ⟨subd19_1_527, List.forall_mem_cons.2 ⟨subd19_1_528, List.forall_mem_cons.2 ⟨subd19_1_529, List.forall_mem_cons.2 ⟨subd19_1_530, List.forall_mem_cons.2 ⟨subd19_1_531, List.forall_mem_cons.2 ⟨subd19_1_532, List.forall_mem_cons.2 ⟨subd19_1_533, List.forall_mem_cons.2 ⟨subd19_1_534, List.forall_mem_cons.2 ⟨subd19_1_535, List.forall_mem_cons.2 ⟨subd19_1_536, List.forall_mem_cons.2 ⟨subd19_1_537, List.forall_mem_cons.2 ⟨subd19_1_538, List.forall_mem_cons.2 ⟨subd19_1_539, List.forall_mem_cons.2 ⟨subd19_1_540, List.forall_mem_cons.2 ⟨subd19_1_541, List.forall_mem_cons.2 ⟨subd19_1_542, List.forall_mem_cons.2 ⟨subd19_1_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_1_544 : subd19_1 [-1, 1, -4] = true := by decide +kernel
theorem subd19_1_545 : subd19_1 [-1, 1, -3] = true := by decide +kernel
theorem subd19_1_546 : subd19_1 [-1, 1, -2] = true := by decide +kernel
theorem subd19_1_547 : subd19_1 [-1, 1, -1] = true := by decide +kernel
theorem subd19_1_548 : subd19_1 [-1, 1, 0] = true := by decide +kernel
theorem subd19_1_549 : subd19_1 [-1, 1, 1] = true := by decide +kernel
theorem subd19_1_550 : subd19_1 [-1, 1, 2] = true := by decide +kernel
theorem subd19_1_551 : subd19_1 [-1, 1, 3] = true := by decide +kernel
theorem subd19_1_552 : subd19_1 [-1, 1, 4] = true := by decide +kernel
theorem subd19_1_553 : subd19_1 [-1, 1, 5] = true := by decide +kernel
theorem subd19_1_554 : subd19_1 [-1, 1, 6] = true := by decide +kernel
theorem subd19_1_555 : subd19_1 [-1, 1, 7] = true := by decide +kernel
theorem subd19_1_556 : subd19_1 [-1, 1, 8] = true := by decide +kernel
theorem subd19_1_557 : subd19_1 [-1, 2, -7] = true := by decide +kernel
theorem subd19_1_558 : subd19_1 [-1, 2, -6] = true := by decide +kernel
theorem subd19_1_559 : subd19_1 [-1, 2, -5] = true := by decide +kernel
theorem subd19_1_560 : subd19_1 [-1, 2, -4] = true := by decide +kernel
theorem subd19_1_561 : subd19_1 [-1, 2, -3] = true := by decide +kernel
theorem subd19_1_562 : subd19_1 [-1, 2, -2] = true := by decide +kernel
theorem subd19_1_563 : subd19_1 [-1, 2, -1] = true := by decide +kernel
theorem subd19_1_564 : subd19_1 [-1, 2, 0] = true := by decide +kernel
theorem subd19_1_565 : subd19_1 [-1, 2, 1] = true := by decide +kernel
theorem subd19_1_566 : subd19_1 [-1, 2, 2] = true := by decide +kernel
theorem subd19_1_567 : subd19_1 [-1, 2, 3] = true := by decide +kernel
theorem subd19_1_568 : subd19_1 [-1, 2, 4] = true := by decide +kernel
theorem subd19_1_569 : subd19_1 [-1, 2, 5] = true := by decide +kernel
theorem subd19_1_570 : subd19_1 [-1, 2, 6] = true := by decide +kernel
theorem subd19_1_571 : subd19_1 [-1, 2, 7] = true := by decide +kernel
theorem subd19_1_572 : subd19_1 [-1, 2, 8] = true := by decide +kernel
theorem subd19_1_573 : subd19_1 [-1, 3, -6] = true := by decide +kernel
theorem subd19_1_574 : subd19_1 [-1, 3, -5] = true := by decide +kernel
theorem subd19_1_575 : subd19_1 [-1, 3, -4] = true := by decide +kernel
theorem sbd19_1_17 : ∀ q ∈ blkd19_1_17, subd19_1 q = true := by
  unfold blkd19_1_17
  exact List.forall_mem_cons.2 ⟨subd19_1_544, List.forall_mem_cons.2 ⟨subd19_1_545, List.forall_mem_cons.2 ⟨subd19_1_546, List.forall_mem_cons.2 ⟨subd19_1_547, List.forall_mem_cons.2 ⟨subd19_1_548, List.forall_mem_cons.2 ⟨subd19_1_549, List.forall_mem_cons.2 ⟨subd19_1_550, List.forall_mem_cons.2 ⟨subd19_1_551, List.forall_mem_cons.2 ⟨subd19_1_552, List.forall_mem_cons.2 ⟨subd19_1_553, List.forall_mem_cons.2 ⟨subd19_1_554, List.forall_mem_cons.2 ⟨subd19_1_555, List.forall_mem_cons.2 ⟨subd19_1_556, List.forall_mem_cons.2 ⟨subd19_1_557, List.forall_mem_cons.2 ⟨subd19_1_558, List.forall_mem_cons.2 ⟨subd19_1_559, List.forall_mem_cons.2 ⟨subd19_1_560, List.forall_mem_cons.2 ⟨subd19_1_561, List.forall_mem_cons.2 ⟨subd19_1_562, List.forall_mem_cons.2 ⟨subd19_1_563, List.forall_mem_cons.2 ⟨subd19_1_564, List.forall_mem_cons.2 ⟨subd19_1_565, List.forall_mem_cons.2 ⟨subd19_1_566, List.forall_mem_cons.2 ⟨subd19_1_567, List.forall_mem_cons.2 ⟨subd19_1_568, List.forall_mem_cons.2 ⟨subd19_1_569, List.forall_mem_cons.2 ⟨subd19_1_570, List.forall_mem_cons.2 ⟨subd19_1_571, List.forall_mem_cons.2 ⟨subd19_1_572, List.forall_mem_cons.2 ⟨subd19_1_573, List.forall_mem_cons.2 ⟨subd19_1_574, List.forall_mem_cons.2 ⟨subd19_1_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_1_576 : subd19_1 [-1, 3, -3] = true := by decide +kernel
theorem subd19_1_577 : subd19_1 [-1, 3, -2] = true := by decide +kernel
theorem subd19_1_578 : subd19_1 [-1, 3, -1] = true := by decide +kernel
theorem subd19_1_579 : subd19_1 [-1, 3, 0] = true := by decide +kernel
theorem subd19_1_580 : subd19_1 [-1, 3, 1] = true := by decide +kernel
theorem subd19_1_581 : subd19_1 [-1, 3, 2] = true := by decide +kernel
theorem subd19_1_582 : subd19_1 [-1, 3, 3] = true := by decide +kernel
theorem subd19_1_583 : subd19_1 [-1, 3, 4] = true := by decide +kernel
theorem subd19_1_584 : subd19_1 [-1, 3, 5] = true := by decide +kernel
theorem subd19_1_585 : subd19_1 [-1, 3, 6] = true := by decide +kernel
theorem subd19_1_586 : subd19_1 [-1, 3, 7] = true := by decide +kernel
theorem subd19_1_587 : subd19_1 [-1, 3, 8] = true := by decide +kernel
theorem subd19_1_588 : subd19_1 [-1, 4, -6] = true := by decide +kernel
theorem subd19_1_589 : subd19_1 [-1, 4, -5] = true := by decide +kernel
theorem subd19_1_590 : subd19_1 [-1, 4, -4] = true := by decide +kernel
theorem subd19_1_591 : subd19_1 [-1, 4, -3] = true := by decide +kernel
theorem subd19_1_592 : subd19_1 [-1, 4, -2] = true := by decide +kernel
theorem subd19_1_593 : subd19_1 [-1, 4, -1] = true := by decide +kernel
theorem subd19_1_594 : subd19_1 [-1, 4, 0] = true := by decide +kernel
theorem subd19_1_595 : subd19_1 [-1, 4, 1] = true := by decide +kernel
theorem subd19_1_596 : subd19_1 [-1, 4, 2] = true := by decide +kernel
theorem subd19_1_597 : subd19_1 [-1, 4, 3] = true := by decide +kernel
theorem subd19_1_598 : subd19_1 [-1, 4, 4] = true := by decide +kernel
theorem subd19_1_599 : subd19_1 [-1, 4, 5] = true := by decide +kernel
theorem subd19_1_600 : subd19_1 [-1, 4, 6] = true := by decide +kernel
theorem subd19_1_601 : subd19_1 [-1, 4, 7] = true := by decide +kernel
theorem subd19_1_602 : subd19_1 [-1, 4, 8] = true := by decide +kernel
theorem subd19_1_603 : subd19_1 [-1, 5, -5] = true := by decide +kernel
theorem subd19_1_604 : subd19_1 [-1, 5, -4] = true := by decide +kernel
theorem subd19_1_605 : subd19_1 [-1, 5, -3] = true := by decide +kernel
theorem subd19_1_606 : subd19_1 [-1, 5, -2] = true := by decide +kernel
theorem subd19_1_607 : subd19_1 [-1, 5, -1] = true := by decide +kernel
theorem sbd19_1_18 : ∀ q ∈ blkd19_1_18, subd19_1 q = true := by
  unfold blkd19_1_18
  exact List.forall_mem_cons.2 ⟨subd19_1_576, List.forall_mem_cons.2 ⟨subd19_1_577, List.forall_mem_cons.2 ⟨subd19_1_578, List.forall_mem_cons.2 ⟨subd19_1_579, List.forall_mem_cons.2 ⟨subd19_1_580, List.forall_mem_cons.2 ⟨subd19_1_581, List.forall_mem_cons.2 ⟨subd19_1_582, List.forall_mem_cons.2 ⟨subd19_1_583, List.forall_mem_cons.2 ⟨subd19_1_584, List.forall_mem_cons.2 ⟨subd19_1_585, List.forall_mem_cons.2 ⟨subd19_1_586, List.forall_mem_cons.2 ⟨subd19_1_587, List.forall_mem_cons.2 ⟨subd19_1_588, List.forall_mem_cons.2 ⟨subd19_1_589, List.forall_mem_cons.2 ⟨subd19_1_590, List.forall_mem_cons.2 ⟨subd19_1_591, List.forall_mem_cons.2 ⟨subd19_1_592, List.forall_mem_cons.2 ⟨subd19_1_593, List.forall_mem_cons.2 ⟨subd19_1_594, List.forall_mem_cons.2 ⟨subd19_1_595, List.forall_mem_cons.2 ⟨subd19_1_596, List.forall_mem_cons.2 ⟨subd19_1_597, List.forall_mem_cons.2 ⟨subd19_1_598, List.forall_mem_cons.2 ⟨subd19_1_599, List.forall_mem_cons.2 ⟨subd19_1_600, List.forall_mem_cons.2 ⟨subd19_1_601, List.forall_mem_cons.2 ⟨subd19_1_602, List.forall_mem_cons.2 ⟨subd19_1_603, List.forall_mem_cons.2 ⟨subd19_1_604, List.forall_mem_cons.2 ⟨subd19_1_605, List.forall_mem_cons.2 ⟨subd19_1_606, List.forall_mem_cons.2 ⟨subd19_1_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_1_608 : subd19_1 [-1, 5, 0] = true := by decide +kernel
theorem subd19_1_609 : subd19_1 [-1, 5, 1] = true := by decide +kernel
theorem subd19_1_610 : subd19_1 [-1, 5, 2] = true := by decide +kernel
theorem subd19_1_611 : subd19_1 [-1, 5, 3] = true := by decide +kernel
theorem subd19_1_612 : subd19_1 [-1, 5, 4] = true := by decide +kernel
theorem subd19_1_613 : subd19_1 [-1, 5, 5] = true := by decide +kernel
theorem subd19_1_614 : subd19_1 [-1, 5, 6] = true := by decide +kernel
theorem subd19_1_615 : subd19_1 [-1, 5, 7] = true := by decide +kernel
theorem subd19_1_616 : subd19_1 [-1, 5, 8] = true := by decide +kernel
theorem subd19_1_617 : subd19_1 [-1, 6] = true := by decide +kernel
theorem subd19_1_618 : subd19_1 [-1, 7] = true := by decide +kernel
theorem subd19_1_619 : subd19_1 [-1, 8] = true := by decide +kernel
theorem subd19_1_620 : subd19_1 [-1, 9] = true := by decide +kernel
theorem subd19_1_621 : subd19_1 [0, -10] = true := by decide +kernel
theorem subd19_1_622 : subd19_1 [0, -9] = true := by decide +kernel
theorem subd19_1_623 : subd19_1 [0, -8] = true := by decide +kernel
theorem subd19_1_624 : subd19_1 [0, -7] = true := by decide +kernel
theorem subd19_1_625 : subd19_1 [0, -6] = true := by decide +kernel
theorem subd19_1_626 : subd19_1 [0, -5] = true := by decide +kernel
theorem subd19_1_627 : subd19_1 [0, -4, -9] = true := by decide +kernel
theorem subd19_1_628 : subd19_1 [0, -4, -8] = true := by decide +kernel
theorem subd19_1_629 : subd19_1 [0, -4, -7] = true := by decide +kernel
theorem subd19_1_630 : subd19_1 [0, -4, -6] = true := by decide +kernel
theorem subd19_1_631 : subd19_1 [0, -4, -5] = true := by decide +kernel
theorem subd19_1_632 : subd19_1 [0, -4, -4] = true := by decide +kernel
theorem subd19_1_633 : subd19_1 [0, -4, -3] = true := by decide +kernel
theorem subd19_1_634 : subd19_1 [0, -4, -2] = true := by decide +kernel
theorem subd19_1_635 : subd19_1 [0, -4, -1] = true := by decide +kernel
theorem subd19_1_636 : subd19_1 [0, -4, 0] = true := by decide +kernel
theorem subd19_1_637 : subd19_1 [0, -4, 1] = true := by decide +kernel
theorem subd19_1_638 : subd19_1 [0, -4, 2] = true := by decide +kernel
theorem subd19_1_639 : subd19_1 [0, -4, 3] = true := by decide +kernel
theorem sbd19_1_19 : ∀ q ∈ blkd19_1_19, subd19_1 q = true := by
  unfold blkd19_1_19
  exact List.forall_mem_cons.2 ⟨subd19_1_608, List.forall_mem_cons.2 ⟨subd19_1_609, List.forall_mem_cons.2 ⟨subd19_1_610, List.forall_mem_cons.2 ⟨subd19_1_611, List.forall_mem_cons.2 ⟨subd19_1_612, List.forall_mem_cons.2 ⟨subd19_1_613, List.forall_mem_cons.2 ⟨subd19_1_614, List.forall_mem_cons.2 ⟨subd19_1_615, List.forall_mem_cons.2 ⟨subd19_1_616, List.forall_mem_cons.2 ⟨subd19_1_617, List.forall_mem_cons.2 ⟨subd19_1_618, List.forall_mem_cons.2 ⟨subd19_1_619, List.forall_mem_cons.2 ⟨subd19_1_620, List.forall_mem_cons.2 ⟨subd19_1_621, List.forall_mem_cons.2 ⟨subd19_1_622, List.forall_mem_cons.2 ⟨subd19_1_623, List.forall_mem_cons.2 ⟨subd19_1_624, List.forall_mem_cons.2 ⟨subd19_1_625, List.forall_mem_cons.2 ⟨subd19_1_626, List.forall_mem_cons.2 ⟨subd19_1_627, List.forall_mem_cons.2 ⟨subd19_1_628, List.forall_mem_cons.2 ⟨subd19_1_629, List.forall_mem_cons.2 ⟨subd19_1_630, List.forall_mem_cons.2 ⟨subd19_1_631, List.forall_mem_cons.2 ⟨subd19_1_632, List.forall_mem_cons.2 ⟨subd19_1_633, List.forall_mem_cons.2 ⟨subd19_1_634, List.forall_mem_cons.2 ⟨subd19_1_635, List.forall_mem_cons.2 ⟨subd19_1_636, List.forall_mem_cons.2 ⟨subd19_1_637, List.forall_mem_cons.2 ⟨subd19_1_638, List.forall_mem_cons.2 ⟨subd19_1_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_1_640 : subd19_1 [0, -4, 4] = true := by decide +kernel
theorem subd19_1_641 : subd19_1 [0, -4, 5] = true := by decide +kernel
theorem subd19_1_642 : subd19_1 [0, -3, -9] = true := by decide +kernel
theorem subd19_1_643 : subd19_1 [0, -3, -8] = true := by decide +kernel
theorem subd19_1_644 : subd19_1 [0, -3, -7] = true := by decide +kernel
theorem subd19_1_645 : subd19_1 [0, -3, -6] = true := by decide +kernel
theorem subd19_1_646 : subd19_1 [0, -3, -5] = true := by decide +kernel
theorem subd19_1_647 : subd19_1 [0, -3, -4] = true := by decide +kernel
theorem subd19_1_648 : subd19_1 [0, -3, -3] = true := by decide +kernel
theorem subd19_1_649 : subd19_1 [0, -3, -2] = true := by decide +kernel
theorem subd19_1_650 : subd19_1 [0, -3, -1] = true := by decide +kernel
theorem subd19_1_651 : subd19_1 [0, -3, 0] = true := by decide +kernel
theorem subd19_1_652 : subd19_1 [0, -3, 1] = true := by decide +kernel
theorem subd19_1_653 : subd19_1 [0, -3, 2] = true := by decide +kernel
theorem subd19_1_654 : subd19_1 [0, -3, 3] = true := by decide +kernel
theorem subd19_1_655 : subd19_1 [0, -3, 4] = true := by decide +kernel
theorem subd19_1_656 : subd19_1 [0, -3, 5] = true := by decide +kernel
theorem subd19_1_657 : subd19_1 [0, -3, 6] = true := by decide +kernel
theorem subd19_1_658 : subd19_1 [0, -2, -9] = true := by decide +kernel
theorem subd19_1_659 : subd19_1 [0, -2, -8] = true := by decide +kernel
theorem subd19_1_660 : subd19_1 [0, -2, -7] = true := by decide +kernel
theorem subd19_1_661 : subd19_1 [0, -2, -6] = true := by decide +kernel
theorem subd19_1_662 : subd19_1 [0, -2, -5] = true := by decide +kernel
theorem subd19_1_663 : subd19_1 [0, -2, -4] = true := by decide +kernel
theorem subd19_1_664 : subd19_1 [0, -2, -3] = true := by decide +kernel
theorem subd19_1_665 : subd19_1 [0, -2, -2] = true := by decide +kernel
theorem subd19_1_666 : subd19_1 [0, -2, -1] = true := by decide +kernel
theorem subd19_1_667 : subd19_1 [0, -2, 0] = true := by decide +kernel
theorem subd19_1_668 : subd19_1 [0, -2, 1] = true := by decide +kernel
theorem subd19_1_669 : subd19_1 [0, -2, 2] = true := by decide +kernel
theorem subd19_1_670 : subd19_1 [0, -2, 3] = true := by decide +kernel
theorem subd19_1_671 : subd19_1 [0, -2, 4] = true := by decide +kernel
theorem sbd19_1_20 : ∀ q ∈ blkd19_1_20, subd19_1 q = true := by
  unfold blkd19_1_20
  exact List.forall_mem_cons.2 ⟨subd19_1_640, List.forall_mem_cons.2 ⟨subd19_1_641, List.forall_mem_cons.2 ⟨subd19_1_642, List.forall_mem_cons.2 ⟨subd19_1_643, List.forall_mem_cons.2 ⟨subd19_1_644, List.forall_mem_cons.2 ⟨subd19_1_645, List.forall_mem_cons.2 ⟨subd19_1_646, List.forall_mem_cons.2 ⟨subd19_1_647, List.forall_mem_cons.2 ⟨subd19_1_648, List.forall_mem_cons.2 ⟨subd19_1_649, List.forall_mem_cons.2 ⟨subd19_1_650, List.forall_mem_cons.2 ⟨subd19_1_651, List.forall_mem_cons.2 ⟨subd19_1_652, List.forall_mem_cons.2 ⟨subd19_1_653, List.forall_mem_cons.2 ⟨subd19_1_654, List.forall_mem_cons.2 ⟨subd19_1_655, List.forall_mem_cons.2 ⟨subd19_1_656, List.forall_mem_cons.2 ⟨subd19_1_657, List.forall_mem_cons.2 ⟨subd19_1_658, List.forall_mem_cons.2 ⟨subd19_1_659, List.forall_mem_cons.2 ⟨subd19_1_660, List.forall_mem_cons.2 ⟨subd19_1_661, List.forall_mem_cons.2 ⟨subd19_1_662, List.forall_mem_cons.2 ⟨subd19_1_663, List.forall_mem_cons.2 ⟨subd19_1_664, List.forall_mem_cons.2 ⟨subd19_1_665, List.forall_mem_cons.2 ⟨subd19_1_666, List.forall_mem_cons.2 ⟨subd19_1_667, List.forall_mem_cons.2 ⟨subd19_1_668, List.forall_mem_cons.2 ⟨subd19_1_669, List.forall_mem_cons.2 ⟨subd19_1_670, List.forall_mem_cons.2 ⟨subd19_1_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_1_672 : subd19_1 [0, -2, 5] = true := by decide +kernel
theorem subd19_1_673 : subd19_1 [0, -2, 6] = true := by decide +kernel
theorem subd19_1_674 : subd19_1 [0, -1, -8] = true := by decide +kernel
theorem subd19_1_675 : subd19_1 [0, -1, -7] = true := by decide +kernel
theorem subd19_1_676 : subd19_1 [0, -1, -6] = true := by decide +kernel
theorem subd19_1_677 : subd19_1 [0, -1, -5] = true := by decide +kernel
theorem subd19_1_678 : subd19_1 [0, -1, -4] = true := by decide +kernel
theorem subd19_1_679 : subd19_1 [0, -1, -3] = true := by decide +kernel
theorem subd19_1_680 : subd19_1 [0, -1, -2] = true := by decide +kernel
theorem subd19_1_681 : subd19_1 [0, -1, -1] = true := by decide +kernel
theorem subd19_1_682 : subd19_1 [0, -1, 0] = true := by decide +kernel
theorem subd19_1_683 : subd19_1 [0, -1, 1] = true := by decide +kernel
theorem subd19_1_684 : subd19_1 [0, -1, 2] = true := by decide +kernel
theorem subd19_1_685 : subd19_1 [0, -1, 3] = true := by decide +kernel
theorem subd19_1_686 : subd19_1 [0, -1, 4] = true := by decide +kernel
theorem subd19_1_687 : subd19_1 [0, -1, 5] = true := by decide +kernel
theorem subd19_1_688 : subd19_1 [0, -1, 6] = true := by decide +kernel
theorem subd19_1_689 : subd19_1 [0, -1, 7] = true := by decide +kernel
theorem subd19_1_690 : subd19_1 [0, 0, -8] = true := by decide +kernel
theorem subd19_1_691 : subd19_1 [0, 0, -7] = true := by decide +kernel
theorem subd19_1_692 : subd19_1 [0, 0, -6] = true := by decide +kernel
theorem subd19_1_693 : subd19_1 [0, 0, -5] = true := by decide +kernel
theorem subd19_1_694 : subd19_1 [0, 0, -4] = true := by decide +kernel
theorem subd19_1_695 : subd19_1 [0, 0, -3] = true := by decide +kernel
theorem subd19_1_696 : subd19_1 [0, 0, -2] = true := by decide +kernel
theorem subd19_1_697 : subd19_1 [0, 0, -1] = true := by decide +kernel
theorem subd19_1_698 : subd19_1 [0, 0, 0] = true := by decide +kernel
theorem subd19_1_699 : subd19_1 [0, 0, 1] = true := by decide +kernel
theorem subd19_1_700 : subd19_1 [0, 0, 2] = true := by decide +kernel
theorem subd19_1_701 : subd19_1 [0, 0, 3] = true := by decide +kernel
theorem subd19_1_702 : subd19_1 [0, 0, 4] = true := by decide +kernel
theorem subd19_1_703 : subd19_1 [0, 0, 5] = true := by decide +kernel
theorem sbd19_1_21 : ∀ q ∈ blkd19_1_21, subd19_1 q = true := by
  unfold blkd19_1_21
  exact List.forall_mem_cons.2 ⟨subd19_1_672, List.forall_mem_cons.2 ⟨subd19_1_673, List.forall_mem_cons.2 ⟨subd19_1_674, List.forall_mem_cons.2 ⟨subd19_1_675, List.forall_mem_cons.2 ⟨subd19_1_676, List.forall_mem_cons.2 ⟨subd19_1_677, List.forall_mem_cons.2 ⟨subd19_1_678, List.forall_mem_cons.2 ⟨subd19_1_679, List.forall_mem_cons.2 ⟨subd19_1_680, List.forall_mem_cons.2 ⟨subd19_1_681, List.forall_mem_cons.2 ⟨subd19_1_682, List.forall_mem_cons.2 ⟨subd19_1_683, List.forall_mem_cons.2 ⟨subd19_1_684, List.forall_mem_cons.2 ⟨subd19_1_685, List.forall_mem_cons.2 ⟨subd19_1_686, List.forall_mem_cons.2 ⟨subd19_1_687, List.forall_mem_cons.2 ⟨subd19_1_688, List.forall_mem_cons.2 ⟨subd19_1_689, List.forall_mem_cons.2 ⟨subd19_1_690, List.forall_mem_cons.2 ⟨subd19_1_691, List.forall_mem_cons.2 ⟨subd19_1_692, List.forall_mem_cons.2 ⟨subd19_1_693, List.forall_mem_cons.2 ⟨subd19_1_694, List.forall_mem_cons.2 ⟨subd19_1_695, List.forall_mem_cons.2 ⟨subd19_1_696, List.forall_mem_cons.2 ⟨subd19_1_697, List.forall_mem_cons.2 ⟨subd19_1_698, List.forall_mem_cons.2 ⟨subd19_1_699, List.forall_mem_cons.2 ⟨subd19_1_700, List.forall_mem_cons.2 ⟨subd19_1_701, List.forall_mem_cons.2 ⟨subd19_1_702, List.forall_mem_cons.2 ⟨subd19_1_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_1_704 : subd19_1 [0, 0, 6] = true := by decide +kernel
theorem subd19_1_705 : subd19_1 [0, 0, 7] = true := by decide +kernel
theorem subd19_1_706 : subd19_1 [0, 1, -8] = true := by decide +kernel
theorem subd19_1_707 : subd19_1 [0, 1, -7] = true := by decide +kernel
theorem subd19_1_708 : subd19_1 [0, 1, -6] = true := by decide +kernel
theorem subd19_1_709 : subd19_1 [0, 1, -5] = true := by decide +kernel
theorem subd19_1_710 : subd19_1 [0, 1, -4] = true := by decide +kernel
theorem subd19_1_711 : subd19_1 [0, 1, -3] = true := by decide +kernel
theorem subd19_1_712 : subd19_1 [0, 1, -2] = true := by decide +kernel
theorem subd19_1_713 : subd19_1 [0, 1, -1] = true := by decide +kernel
theorem subd19_1_714 : subd19_1 [0, 1, 0] = true := by decide +kernel
theorem subd19_1_715 : subd19_1 [0, 1, 1] = true := by decide +kernel
theorem subd19_1_716 : subd19_1 [0, 1, 2] = true := by decide +kernel
theorem subd19_1_717 : subd19_1 [0, 1, 3] = true := by decide +kernel
theorem subd19_1_718 : subd19_1 [0, 1, 4] = true := by decide +kernel
theorem subd19_1_719 : subd19_1 [0, 1, 5] = true := by decide +kernel
theorem subd19_1_720 : subd19_1 [0, 1, 6] = true := by decide +kernel
theorem subd19_1_721 : subd19_1 [0, 1, 7] = true := by decide +kernel
theorem subd19_1_722 : subd19_1 [0, 2, -7] = true := by decide +kernel
theorem subd19_1_723 : subd19_1 [0, 2, -6] = true := by decide +kernel
theorem subd19_1_724 : subd19_1 [0, 2, -5] = true := by decide +kernel
theorem subd19_1_725 : subd19_1 [0, 2, -4] = true := by decide +kernel
theorem subd19_1_726 : subd19_1 [0, 2, -3] = true := by decide +kernel
theorem subd19_1_727 : subd19_1 [0, 2, -2] = true := by decide +kernel
theorem subd19_1_728 : subd19_1 [0, 2, -1] = true := by decide +kernel
theorem subd19_1_729 : subd19_1 [0, 2, 0] = true := by decide +kernel
theorem subd19_1_730 : subd19_1 [0, 2, 1] = true := by decide +kernel
theorem subd19_1_731 : subd19_1 [0, 2, 2] = true := by decide +kernel
theorem subd19_1_732 : subd19_1 [0, 2, 3] = true := by decide +kernel
theorem subd19_1_733 : subd19_1 [0, 2, 4] = true := by decide +kernel
theorem subd19_1_734 : subd19_1 [0, 2, 5] = true := by decide +kernel
theorem subd19_1_735 : subd19_1 [0, 2, 6] = true := by decide +kernel
theorem sbd19_1_22 : ∀ q ∈ blkd19_1_22, subd19_1 q = true := by
  unfold blkd19_1_22
  exact List.forall_mem_cons.2 ⟨subd19_1_704, List.forall_mem_cons.2 ⟨subd19_1_705, List.forall_mem_cons.2 ⟨subd19_1_706, List.forall_mem_cons.2 ⟨subd19_1_707, List.forall_mem_cons.2 ⟨subd19_1_708, List.forall_mem_cons.2 ⟨subd19_1_709, List.forall_mem_cons.2 ⟨subd19_1_710, List.forall_mem_cons.2 ⟨subd19_1_711, List.forall_mem_cons.2 ⟨subd19_1_712, List.forall_mem_cons.2 ⟨subd19_1_713, List.forall_mem_cons.2 ⟨subd19_1_714, List.forall_mem_cons.2 ⟨subd19_1_715, List.forall_mem_cons.2 ⟨subd19_1_716, List.forall_mem_cons.2 ⟨subd19_1_717, List.forall_mem_cons.2 ⟨subd19_1_718, List.forall_mem_cons.2 ⟨subd19_1_719, List.forall_mem_cons.2 ⟨subd19_1_720, List.forall_mem_cons.2 ⟨subd19_1_721, List.forall_mem_cons.2 ⟨subd19_1_722, List.forall_mem_cons.2 ⟨subd19_1_723, List.forall_mem_cons.2 ⟨subd19_1_724, List.forall_mem_cons.2 ⟨subd19_1_725, List.forall_mem_cons.2 ⟨subd19_1_726, List.forall_mem_cons.2 ⟨subd19_1_727, List.forall_mem_cons.2 ⟨subd19_1_728, List.forall_mem_cons.2 ⟨subd19_1_729, List.forall_mem_cons.2 ⟨subd19_1_730, List.forall_mem_cons.2 ⟨subd19_1_731, List.forall_mem_cons.2 ⟨subd19_1_732, List.forall_mem_cons.2 ⟨subd19_1_733, List.forall_mem_cons.2 ⟨subd19_1_734, List.forall_mem_cons.2 ⟨subd19_1_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
