import ReflectZphi.Data.Cert5.C111.Base

namespace ReflectZphi.Data.Cert5.C111

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_3_288 : subd8_3 [0, 2, 0] = true := by decide +kernel
theorem subd8_3_289 : subd8_3 [0, 2, 1] = true := by decide +kernel
theorem subd8_3_290 : subd8_3 [0, 2, 2] = true := by decide +kernel
theorem subd8_3_291 : subd8_3 [0, 2, 3] = true := by decide +kernel
theorem subd8_3_292 : subd8_3 [0, 2, 4] = true := by decide +kernel
theorem subd8_3_293 : subd8_3 [0, 2, 5] = true := by decide +kernel
theorem subd8_3_294 : subd8_3 [0, 2, 6] = true := by decide +kernel
theorem subd8_3_295 : subd8_3 [0, 2, 7] = true := by decide +kernel
theorem subd8_3_296 : subd8_3 [0, 3, -7] = true := by decide +kernel
theorem subd8_3_297 : subd8_3 [0, 3, -6] = true := by decide +kernel
theorem subd8_3_298 : subd8_3 [0, 3, -5] = true := by decide +kernel
theorem subd8_3_299 : subd8_3 [0, 3, -4] = true := by decide +kernel
theorem subd8_3_300 : subd8_3 [0, 3, -3] = true := by decide +kernel
theorem subd8_3_301 : subd8_3 [0, 3, -2] = true := by decide +kernel
theorem subd8_3_302 : subd8_3 [0, 3, -1] = true := by decide +kernel
theorem subd8_3_303 : subd8_3 [0, 3, 0] = true := by decide +kernel
theorem subd8_3_304 : subd8_3 [0, 3, 1] = true := by decide +kernel
theorem subd8_3_305 : subd8_3 [0, 3, 2] = true := by decide +kernel
theorem subd8_3_306 : subd8_3 [0, 3, 3] = true := by decide +kernel
theorem subd8_3_307 : subd8_3 [0, 3, 4] = true := by decide +kernel
theorem subd8_3_308 : subd8_3 [0, 3, 5] = true := by decide +kernel
theorem subd8_3_309 : subd8_3 [0, 3, 6] = true := by decide +kernel
theorem subd8_3_310 : subd8_3 [0, 4] = true := by decide +kernel
theorem subd8_3_311 : subd8_3 [1, -6] = true := by decide +kernel
theorem subd8_3_312 : subd8_3 [1, -5] = true := by decide +kernel
theorem subd8_3_313 : subd8_3 [1, -4] = true := by decide +kernel
theorem subd8_3_314 : subd8_3 [1, -3, -8] = true := by decide +kernel
theorem subd8_3_315 : subd8_3 [1, -3, -7] = true := by decide +kernel
theorem subd8_3_316 : subd8_3 [1, -3, -6] = true := by decide +kernel
theorem subd8_3_317 : subd8_3 [1, -3, -5] = true := by decide +kernel
theorem subd8_3_318 : subd8_3 [1, -3, -4] = true := by decide +kernel
theorem subd8_3_319 : subd8_3 [1, -3, -3] = true := by decide +kernel
theorem sbd8_3_9 : ∀ q ∈ blkd8_3_9, subd8_3 q = true := by
  unfold blkd8_3_9
  exact List.forall_mem_cons.2 ⟨subd8_3_288, List.forall_mem_cons.2 ⟨subd8_3_289, List.forall_mem_cons.2 ⟨subd8_3_290, List.forall_mem_cons.2 ⟨subd8_3_291, List.forall_mem_cons.2 ⟨subd8_3_292, List.forall_mem_cons.2 ⟨subd8_3_293, List.forall_mem_cons.2 ⟨subd8_3_294, List.forall_mem_cons.2 ⟨subd8_3_295, List.forall_mem_cons.2 ⟨subd8_3_296, List.forall_mem_cons.2 ⟨subd8_3_297, List.forall_mem_cons.2 ⟨subd8_3_298, List.forall_mem_cons.2 ⟨subd8_3_299, List.forall_mem_cons.2 ⟨subd8_3_300, List.forall_mem_cons.2 ⟨subd8_3_301, List.forall_mem_cons.2 ⟨subd8_3_302, List.forall_mem_cons.2 ⟨subd8_3_303, List.forall_mem_cons.2 ⟨subd8_3_304, List.forall_mem_cons.2 ⟨subd8_3_305, List.forall_mem_cons.2 ⟨subd8_3_306, List.forall_mem_cons.2 ⟨subd8_3_307, List.forall_mem_cons.2 ⟨subd8_3_308, List.forall_mem_cons.2 ⟨subd8_3_309, List.forall_mem_cons.2 ⟨subd8_3_310, List.forall_mem_cons.2 ⟨subd8_3_311, List.forall_mem_cons.2 ⟨subd8_3_312, List.forall_mem_cons.2 ⟨subd8_3_313, List.forall_mem_cons.2 ⟨subd8_3_314, List.forall_mem_cons.2 ⟨subd8_3_315, List.forall_mem_cons.2 ⟨subd8_3_316, List.forall_mem_cons.2 ⟨subd8_3_317, List.forall_mem_cons.2 ⟨subd8_3_318, List.forall_mem_cons.2 ⟨subd8_3_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_320 : subd8_3 [1, -3, -2] = true := by decide +kernel
theorem subd8_3_321 : subd8_3 [1, -3, -1] = true := by decide +kernel
theorem subd8_3_322 : subd8_3 [1, -3, 0] = true := by decide +kernel
theorem subd8_3_323 : subd8_3 [1, -3, 1] = true := by decide +kernel
theorem subd8_3_324 : subd8_3 [1, -3, 2] = true := by decide +kernel
theorem subd8_3_325 : subd8_3 [1, -3, 3] = true := by decide +kernel
theorem subd8_3_326 : subd8_3 [1, -3, 4] = true := by decide +kernel
theorem subd8_3_327 : subd8_3 [1, -3, 5] = true := by decide +kernel
theorem subd8_3_328 : subd8_3 [1, -3, 6] = true := by decide +kernel
theorem subd8_3_329 : subd8_3 [1, -2, -9] = true := by decide +kernel
theorem subd8_3_330 : subd8_3 [1, -2, -8] = true := by decide +kernel
theorem subd8_3_331 : subd8_3 [1, -2, -7] = true := by decide +kernel
theorem subd8_3_332 : subd8_3 [1, -2, -6] = true := by decide +kernel
theorem subd8_3_333 : subd8_3 [1, -2, -5] = true := by decide +kernel
theorem subd8_3_334 : subd8_3 [1, -2, -4] = true := by decide +kernel
theorem subd8_3_335 : subd8_3 [1, -2, -3] = true := by decide +kernel
theorem subd8_3_336 : subd8_3 [1, -2, -2] = true := by decide +kernel
theorem subd8_3_337 : subd8_3 [1, -2, -1] = true := by decide +kernel
theorem subd8_3_338 : subd8_3 [1, -2, 0] = true := by decide +kernel
theorem subd8_3_339 : subd8_3 [1, -2, 1] = true := by decide +kernel
theorem subd8_3_340 : subd8_3 [1, -2, 2] = true := by decide +kernel
theorem subd8_3_341 : subd8_3 [1, -2, 3] = true := by decide +kernel
theorem subd8_3_342 : subd8_3 [1, -2, 4] = true := by decide +kernel
theorem subd8_3_343 : subd8_3 [1, -2, 5] = true := by decide +kernel
theorem subd8_3_344 : subd8_3 [1, -2, 6] = true := by decide +kernel
theorem subd8_3_345 : subd8_3 [1, -2, 7] = true := by decide +kernel
theorem subd8_3_346 : subd8_3 [1, -1, -9] = true := by decide +kernel
theorem subd8_3_347 : subd8_3 [1, -1, -8] = true := by decide +kernel
theorem subd8_3_348 : subd8_3 [1, -1, -7] = true := by decide +kernel
theorem subd8_3_349 : subd8_3 [1, -1, -6] = true := by decide +kernel
theorem subd8_3_350 : subd8_3 [1, -1, -5] = true := by decide +kernel
theorem subd8_3_351 : subd8_3 [1, -1, -4] = true := by decide +kernel
theorem sbd8_3_10 : ∀ q ∈ blkd8_3_10, subd8_3 q = true := by
  unfold blkd8_3_10
  exact List.forall_mem_cons.2 ⟨subd8_3_320, List.forall_mem_cons.2 ⟨subd8_3_321, List.forall_mem_cons.2 ⟨subd8_3_322, List.forall_mem_cons.2 ⟨subd8_3_323, List.forall_mem_cons.2 ⟨subd8_3_324, List.forall_mem_cons.2 ⟨subd8_3_325, List.forall_mem_cons.2 ⟨subd8_3_326, List.forall_mem_cons.2 ⟨subd8_3_327, List.forall_mem_cons.2 ⟨subd8_3_328, List.forall_mem_cons.2 ⟨subd8_3_329, List.forall_mem_cons.2 ⟨subd8_3_330, List.forall_mem_cons.2 ⟨subd8_3_331, List.forall_mem_cons.2 ⟨subd8_3_332, List.forall_mem_cons.2 ⟨subd8_3_333, List.forall_mem_cons.2 ⟨subd8_3_334, List.forall_mem_cons.2 ⟨subd8_3_335, List.forall_mem_cons.2 ⟨subd8_3_336, List.forall_mem_cons.2 ⟨subd8_3_337, List.forall_mem_cons.2 ⟨subd8_3_338, List.forall_mem_cons.2 ⟨subd8_3_339, List.forall_mem_cons.2 ⟨subd8_3_340, List.forall_mem_cons.2 ⟨subd8_3_341, List.forall_mem_cons.2 ⟨subd8_3_342, List.forall_mem_cons.2 ⟨subd8_3_343, List.forall_mem_cons.2 ⟨subd8_3_344, List.forall_mem_cons.2 ⟨subd8_3_345, List.forall_mem_cons.2 ⟨subd8_3_346, List.forall_mem_cons.2 ⟨subd8_3_347, List.forall_mem_cons.2 ⟨subd8_3_348, List.forall_mem_cons.2 ⟨subd8_3_349, List.forall_mem_cons.2 ⟨subd8_3_350, List.forall_mem_cons.2 ⟨subd8_3_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_352 : subd8_3 [1, -1, -3] = true := by decide +kernel
theorem subd8_3_353 : subd8_3 [1, -1, -2] = true := by decide +kernel
theorem subd8_3_354 : subd8_3 [1, -1, -1] = true := by decide +kernel
theorem subd8_3_355 : subd8_3 [1, -1, 0] = true := by decide +kernel
theorem subd8_3_356 : subd8_3 [1, -1, 1] = true := by decide +kernel
theorem subd8_3_357 : subd8_3 [1, -1, 2] = true := by decide +kernel
theorem subd8_3_358 : subd8_3 [1, -1, 3] = true := by decide +kernel
theorem subd8_3_359 : subd8_3 [1, -1, 4] = true := by decide +kernel
theorem subd8_3_360 : subd8_3 [1, -1, 5] = true := by decide +kernel
theorem subd8_3_361 : subd8_3 [1, -1, 6] = true := by decide +kernel
theorem subd8_3_362 : subd8_3 [1, -1, 7] = true := by decide +kernel
theorem subd8_3_363 : subd8_3 [1, 0, -9] = true := by decide +kernel
theorem subd8_3_364 : subd8_3 [1, 0, -8] = true := by decide +kernel
theorem subd8_3_365 : subd8_3 [1, 0, -7] = true := by decide +kernel
theorem subd8_3_366 : subd8_3 [1, 0, -6] = true := by decide +kernel
theorem subd8_3_367 : subd8_3 [1, 0, -5] = true := by decide +kernel
theorem subd8_3_368 : subd8_3 [1, 0, -4] = true := by decide +kernel
theorem subd8_3_369 : subd8_3 [1, 0, -3] = true := by decide +kernel
theorem subd8_3_370 : subd8_3 [1, 0, -2] = true := by decide +kernel
theorem subd8_3_371 : subd8_3 [1, 0, -1] = true := by decide +kernel
theorem subd8_3_372 : subd8_3 [1, 0, 0] = true := by decide +kernel
theorem subd8_3_373 : subd8_3 [1, 0, 1] = true := by decide +kernel
theorem subd8_3_374 : subd8_3 [1, 0, 2] = true := by decide +kernel
theorem subd8_3_375 : subd8_3 [1, 0, 3] = true := by decide +kernel
theorem subd8_3_376 : subd8_3 [1, 0, 4] = true := by decide +kernel
theorem subd8_3_377 : subd8_3 [1, 0, 5] = true := by decide +kernel
theorem subd8_3_378 : subd8_3 [1, 0, 6] = true := by decide +kernel
theorem subd8_3_379 : subd8_3 [1, 0, 7] = true := by decide +kernel
theorem subd8_3_380 : subd8_3 [1, 1, -9] = true := by decide +kernel
theorem subd8_3_381 : subd8_3 [1, 1, -8] = true := by decide +kernel
theorem subd8_3_382 : subd8_3 [1, 1, -7] = true := by decide +kernel
theorem subd8_3_383 : subd8_3 [1, 1, -6] = true := by decide +kernel
theorem sbd8_3_11 : ∀ q ∈ blkd8_3_11, subd8_3 q = true := by
  unfold blkd8_3_11
  exact List.forall_mem_cons.2 ⟨subd8_3_352, List.forall_mem_cons.2 ⟨subd8_3_353, List.forall_mem_cons.2 ⟨subd8_3_354, List.forall_mem_cons.2 ⟨subd8_3_355, List.forall_mem_cons.2 ⟨subd8_3_356, List.forall_mem_cons.2 ⟨subd8_3_357, List.forall_mem_cons.2 ⟨subd8_3_358, List.forall_mem_cons.2 ⟨subd8_3_359, List.forall_mem_cons.2 ⟨subd8_3_360, List.forall_mem_cons.2 ⟨subd8_3_361, List.forall_mem_cons.2 ⟨subd8_3_362, List.forall_mem_cons.2 ⟨subd8_3_363, List.forall_mem_cons.2 ⟨subd8_3_364, List.forall_mem_cons.2 ⟨subd8_3_365, List.forall_mem_cons.2 ⟨subd8_3_366, List.forall_mem_cons.2 ⟨subd8_3_367, List.forall_mem_cons.2 ⟨subd8_3_368, List.forall_mem_cons.2 ⟨subd8_3_369, List.forall_mem_cons.2 ⟨subd8_3_370, List.forall_mem_cons.2 ⟨subd8_3_371, List.forall_mem_cons.2 ⟨subd8_3_372, List.forall_mem_cons.2 ⟨subd8_3_373, List.forall_mem_cons.2 ⟨subd8_3_374, List.forall_mem_cons.2 ⟨subd8_3_375, List.forall_mem_cons.2 ⟨subd8_3_376, List.forall_mem_cons.2 ⟨subd8_3_377, List.forall_mem_cons.2 ⟨subd8_3_378, List.forall_mem_cons.2 ⟨subd8_3_379, List.forall_mem_cons.2 ⟨subd8_3_380, List.forall_mem_cons.2 ⟨subd8_3_381, List.forall_mem_cons.2 ⟨subd8_3_382, List.forall_mem_cons.2 ⟨subd8_3_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_384 : subd8_3 [1, 1, -5] = true := by decide +kernel
theorem subd8_3_385 : subd8_3 [1, 1, -4] = true := by decide +kernel
theorem subd8_3_386 : subd8_3 [1, 1, -3] = true := by decide +kernel
theorem subd8_3_387 : subd8_3 [1, 1, -2] = true := by decide +kernel
theorem subd8_3_388 : subd8_3 [1, 1, -1] = true := by decide +kernel
theorem subd8_3_389 : subd8_3 [1, 1, 0] = true := by decide +kernel
theorem subd8_3_390 : subd8_3 [1, 1, 1] = true := by decide +kernel
theorem subd8_3_391 : subd8_3 [1, 1, 2] = true := by decide +kernel
theorem subd8_3_392 : subd8_3 [1, 1, 3] = true := by decide +kernel
theorem subd8_3_393 : subd8_3 [1, 1, 4] = true := by decide +kernel
theorem subd8_3_394 : subd8_3 [1, 1, 5] = true := by decide +kernel
theorem subd8_3_395 : subd8_3 [1, 1, 6] = true := by decide +kernel
theorem subd8_3_396 : subd8_3 [1, 1, 7] = true := by decide +kernel
theorem subd8_3_397 : subd8_3 [1, 2, -8] = true := by decide +kernel
theorem subd8_3_398 : subd8_3 [1, 2, -7] = true := by decide +kernel
theorem subd8_3_399 : subd8_3 [1, 2, -6] = true := by decide +kernel
theorem subd8_3_400 : subd8_3 [1, 2, -5] = true := by decide +kernel
theorem subd8_3_401 : subd8_3 [1, 2, -4] = true := by decide +kernel
theorem subd8_3_402 : subd8_3 [1, 2, -3] = true := by decide +kernel
theorem subd8_3_403 : subd8_3 [1, 2, -2] = true := by decide +kernel
theorem subd8_3_404 : subd8_3 [1, 2, -1] = true := by decide +kernel
theorem subd8_3_405 : subd8_3 [1, 2, 0] = true := by decide +kernel
theorem subd8_3_406 : subd8_3 [1, 2, 1] = true := by decide +kernel
theorem subd8_3_407 : subd8_3 [1, 2, 2] = true := by decide +kernel
theorem subd8_3_408 : subd8_3 [1, 2, 3] = true := by decide +kernel
theorem subd8_3_409 : subd8_3 [1, 2, 4] = true := by decide +kernel
theorem subd8_3_410 : subd8_3 [1, 2, 5] = true := by decide +kernel
theorem subd8_3_411 : subd8_3 [1, 2, 6] = true := by decide +kernel
theorem subd8_3_412 : subd8_3 [1, 3] = true := by decide +kernel
theorem subd8_3_413 : subd8_3 [1, 4] = true := by decide +kernel
theorem subd8_3_414 : subd8_3 [2, -6] = true := by decide +kernel
theorem subd8_3_415 : subd8_3 [2, -5] = true := by decide +kernel
theorem sbd8_3_12 : ∀ q ∈ blkd8_3_12, subd8_3 q = true := by
  unfold blkd8_3_12
  exact List.forall_mem_cons.2 ⟨subd8_3_384, List.forall_mem_cons.2 ⟨subd8_3_385, List.forall_mem_cons.2 ⟨subd8_3_386, List.forall_mem_cons.2 ⟨subd8_3_387, List.forall_mem_cons.2 ⟨subd8_3_388, List.forall_mem_cons.2 ⟨subd8_3_389, List.forall_mem_cons.2 ⟨subd8_3_390, List.forall_mem_cons.2 ⟨subd8_3_391, List.forall_mem_cons.2 ⟨subd8_3_392, List.forall_mem_cons.2 ⟨subd8_3_393, List.forall_mem_cons.2 ⟨subd8_3_394, List.forall_mem_cons.2 ⟨subd8_3_395, List.forall_mem_cons.2 ⟨subd8_3_396, List.forall_mem_cons.2 ⟨subd8_3_397, List.forall_mem_cons.2 ⟨subd8_3_398, List.forall_mem_cons.2 ⟨subd8_3_399, List.forall_mem_cons.2 ⟨subd8_3_400, List.forall_mem_cons.2 ⟨subd8_3_401, List.forall_mem_cons.2 ⟨subd8_3_402, List.forall_mem_cons.2 ⟨subd8_3_403, List.forall_mem_cons.2 ⟨subd8_3_404, List.forall_mem_cons.2 ⟨subd8_3_405, List.forall_mem_cons.2 ⟨subd8_3_406, List.forall_mem_cons.2 ⟨subd8_3_407, List.forall_mem_cons.2 ⟨subd8_3_408, List.forall_mem_cons.2 ⟨subd8_3_409, List.forall_mem_cons.2 ⟨subd8_3_410, List.forall_mem_cons.2 ⟨subd8_3_411, List.forall_mem_cons.2 ⟨subd8_3_412, List.forall_mem_cons.2 ⟨subd8_3_413, List.forall_mem_cons.2 ⟨subd8_3_414, List.forall_mem_cons.2 ⟨subd8_3_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_416 : subd8_3 [2, -4] = true := by decide +kernel
theorem subd8_3_417 : subd8_3 [2, -3, -8] = true := by decide +kernel
theorem subd8_3_418 : subd8_3 [2, -3, -7] = true := by decide +kernel
theorem subd8_3_419 : subd8_3 [2, -3, -6] = true := by decide +kernel
theorem subd8_3_420 : subd8_3 [2, -3, -5] = true := by decide +kernel
theorem subd8_3_421 : subd8_3 [2, -3, -4] = true := by decide +kernel
theorem subd8_3_422 : subd8_3 [2, -3, -3] = true := by decide +kernel
theorem subd8_3_423 : subd8_3 [2, -3, -2] = true := by decide +kernel
theorem subd8_3_424 : subd8_3 [2, -3, -1] = true := by decide +kernel
theorem subd8_3_425 : subd8_3 [2, -3, 0] = true := by decide +kernel
theorem subd8_3_426 : subd8_3 [2, -3, 1] = true := by decide +kernel
theorem subd8_3_427 : subd8_3 [2, -3, 2] = true := by decide +kernel
theorem subd8_3_428 : subd8_3 [2, -3, 3] = true := by decide +kernel
theorem subd8_3_429 : subd8_3 [2, -3, 4] = true := by decide +kernel
theorem subd8_3_430 : subd8_3 [2, -3, 5] = true := by decide +kernel
theorem subd8_3_431 : subd8_3 [2, -2, -9] = true := by decide +kernel
theorem subd8_3_432 : subd8_3 [2, -2, -8] = true := by decide +kernel
theorem subd8_3_433 : subd8_3 [2, -2, -7] = true := by decide +kernel
theorem subd8_3_434 : subd8_3 [2, -2, -6] = true := by decide +kernel
theorem subd8_3_435 : subd8_3 [2, -2, -5] = true := by decide +kernel
theorem subd8_3_436 : subd8_3 [2, -2, -4] = true := by decide +kernel
theorem subd8_3_437 : subd8_3 [2, -2, -3] = true := by decide +kernel
theorem subd8_3_438 : subd8_3 [2, -2, -2] = true := by decide +kernel
theorem subd8_3_439 : subd8_3 [2, -2, -1] = true := by decide +kernel
theorem subd8_3_440 : subd8_3 [2, -2, 0] = true := by decide +kernel
theorem subd8_3_441 : subd8_3 [2, -2, 1] = true := by decide +kernel
theorem subd8_3_442 : subd8_3 [2, -2, 2] = true := by decide +kernel
theorem subd8_3_443 : subd8_3 [2, -2, 3] = true := by decide +kernel
theorem subd8_3_444 : subd8_3 [2, -2, 4] = true := by decide +kernel
theorem subd8_3_445 : subd8_3 [2, -2, 5] = true := by decide +kernel
theorem subd8_3_446 : subd8_3 [2, -2, 6] = true := by decide +kernel
theorem subd8_3_447 : subd8_3 [2, -1, -9] = true := by decide +kernel
theorem sbd8_3_13 : ∀ q ∈ blkd8_3_13, subd8_3 q = true := by
  unfold blkd8_3_13
  exact List.forall_mem_cons.2 ⟨subd8_3_416, List.forall_mem_cons.2 ⟨subd8_3_417, List.forall_mem_cons.2 ⟨subd8_3_418, List.forall_mem_cons.2 ⟨subd8_3_419, List.forall_mem_cons.2 ⟨subd8_3_420, List.forall_mem_cons.2 ⟨subd8_3_421, List.forall_mem_cons.2 ⟨subd8_3_422, List.forall_mem_cons.2 ⟨subd8_3_423, List.forall_mem_cons.2 ⟨subd8_3_424, List.forall_mem_cons.2 ⟨subd8_3_425, List.forall_mem_cons.2 ⟨subd8_3_426, List.forall_mem_cons.2 ⟨subd8_3_427, List.forall_mem_cons.2 ⟨subd8_3_428, List.forall_mem_cons.2 ⟨subd8_3_429, List.forall_mem_cons.2 ⟨subd8_3_430, List.forall_mem_cons.2 ⟨subd8_3_431, List.forall_mem_cons.2 ⟨subd8_3_432, List.forall_mem_cons.2 ⟨subd8_3_433, List.forall_mem_cons.2 ⟨subd8_3_434, List.forall_mem_cons.2 ⟨subd8_3_435, List.forall_mem_cons.2 ⟨subd8_3_436, List.forall_mem_cons.2 ⟨subd8_3_437, List.forall_mem_cons.2 ⟨subd8_3_438, List.forall_mem_cons.2 ⟨subd8_3_439, List.forall_mem_cons.2 ⟨subd8_3_440, List.forall_mem_cons.2 ⟨subd8_3_441, List.forall_mem_cons.2 ⟨subd8_3_442, List.forall_mem_cons.2 ⟨subd8_3_443, List.forall_mem_cons.2 ⟨subd8_3_444, List.forall_mem_cons.2 ⟨subd8_3_445, List.forall_mem_cons.2 ⟨subd8_3_446, List.forall_mem_cons.2 ⟨subd8_3_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_448 : subd8_3 [2, -1, -8] = true := by decide +kernel
theorem subd8_3_449 : subd8_3 [2, -1, -7] = true := by decide +kernel
theorem subd8_3_450 : subd8_3 [2, -1, -6] = true := by decide +kernel
theorem subd8_3_451 : subd8_3 [2, -1, -5] = true := by decide +kernel
theorem subd8_3_452 : subd8_3 [2, -1, -4] = true := by decide +kernel
theorem subd8_3_453 : subd8_3 [2, -1, -3] = true := by decide +kernel
theorem subd8_3_454 : subd8_3 [2, -1, -2] = true := by decide +kernel
theorem subd8_3_455 : subd8_3 [2, -1, -1] = true := by decide +kernel
theorem subd8_3_456 : subd8_3 [2, -1, 0] = true := by decide +kernel
theorem subd8_3_457 : subd8_3 [2, -1, 1] = true := by decide +kernel
theorem subd8_3_458 : subd8_3 [2, -1, 2] = true := by decide +kernel
theorem subd8_3_459 : subd8_3 [2, -1, 3] = true := by decide +kernel
theorem subd8_3_460 : subd8_3 [2, -1, 4] = true := by decide +kernel
theorem subd8_3_461 : subd8_3 [2, -1, 5] = true := by decide +kernel
theorem subd8_3_462 : subd8_3 [2, -1, 6] = true := by decide +kernel
theorem subd8_3_463 : subd8_3 [2, 0, -8] = true := by decide +kernel
theorem subd8_3_464 : subd8_3 [2, 0, -7] = true := by decide +kernel
theorem subd8_3_465 : subd8_3 [2, 0, -6] = true := by decide +kernel
theorem subd8_3_466 : subd8_3 [2, 0, -5] = true := by decide +kernel
theorem subd8_3_467 : subd8_3 [2, 0, -4] = true := by decide +kernel
theorem subd8_3_468 : subd8_3 [2, 0, -3] = true := by decide +kernel
theorem subd8_3_469 : subd8_3 [2, 0, -2] = true := by decide +kernel
theorem subd8_3_470 : subd8_3 [2, 0, -1] = true := by decide +kernel
theorem subd8_3_471 : subd8_3 [2, 0, 0] = true := by decide +kernel
theorem subd8_3_472 : subd8_3 [2, 0, 1] = true := by decide +kernel
theorem subd8_3_473 : subd8_3 [2, 0, 2] = true := by decide +kernel
theorem subd8_3_474 : subd8_3 [2, 0, 3] = true := by decide +kernel
theorem subd8_3_475 : subd8_3 [2, 0, 4] = true := by decide +kernel
theorem subd8_3_476 : subd8_3 [2, 0, 5] = true := by decide +kernel
theorem subd8_3_477 : subd8_3 [2, 0, 6] = true := by decide +kernel
theorem subd8_3_478 : subd8_3 [2, 1, -8] = true := by decide +kernel
theorem subd8_3_479 : subd8_3 [2, 1, -7] = true := by decide +kernel
theorem sbd8_3_14 : ∀ q ∈ blkd8_3_14, subd8_3 q = true := by
  unfold blkd8_3_14
  exact List.forall_mem_cons.2 ⟨subd8_3_448, List.forall_mem_cons.2 ⟨subd8_3_449, List.forall_mem_cons.2 ⟨subd8_3_450, List.forall_mem_cons.2 ⟨subd8_3_451, List.forall_mem_cons.2 ⟨subd8_3_452, List.forall_mem_cons.2 ⟨subd8_3_453, List.forall_mem_cons.2 ⟨subd8_3_454, List.forall_mem_cons.2 ⟨subd8_3_455, List.forall_mem_cons.2 ⟨subd8_3_456, List.forall_mem_cons.2 ⟨subd8_3_457, List.forall_mem_cons.2 ⟨subd8_3_458, List.forall_mem_cons.2 ⟨subd8_3_459, List.forall_mem_cons.2 ⟨subd8_3_460, List.forall_mem_cons.2 ⟨subd8_3_461, List.forall_mem_cons.2 ⟨subd8_3_462, List.forall_mem_cons.2 ⟨subd8_3_463, List.forall_mem_cons.2 ⟨subd8_3_464, List.forall_mem_cons.2 ⟨subd8_3_465, List.forall_mem_cons.2 ⟨subd8_3_466, List.forall_mem_cons.2 ⟨subd8_3_467, List.forall_mem_cons.2 ⟨subd8_3_468, List.forall_mem_cons.2 ⟨subd8_3_469, List.forall_mem_cons.2 ⟨subd8_3_470, List.forall_mem_cons.2 ⟨subd8_3_471, List.forall_mem_cons.2 ⟨subd8_3_472, List.forall_mem_cons.2 ⟨subd8_3_473, List.forall_mem_cons.2 ⟨subd8_3_474, List.forall_mem_cons.2 ⟨subd8_3_475, List.forall_mem_cons.2 ⟨subd8_3_476, List.forall_mem_cons.2 ⟨subd8_3_477, List.forall_mem_cons.2 ⟨subd8_3_478, List.forall_mem_cons.2 ⟨subd8_3_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_480 : subd8_3 [2, 1, -6] = true := by decide +kernel
theorem subd8_3_481 : subd8_3 [2, 1, -5] = true := by decide +kernel
theorem subd8_3_482 : subd8_3 [2, 1, -4] = true := by decide +kernel
theorem subd8_3_483 : subd8_3 [2, 1, -3] = true := by decide +kernel
theorem subd8_3_484 : subd8_3 [2, 1, -2] = true := by decide +kernel
theorem subd8_3_485 : subd8_3 [2, 1, -1] = true := by decide +kernel
theorem subd8_3_486 : subd8_3 [2, 1, 0] = true := by decide +kernel
theorem subd8_3_487 : subd8_3 [2, 1, 1] = true := by decide +kernel
theorem subd8_3_488 : subd8_3 [2, 1, 2] = true := by decide +kernel
theorem subd8_3_489 : subd8_3 [2, 1, 3] = true := by decide +kernel
theorem subd8_3_490 : subd8_3 [2, 1, 4] = true := by decide +kernel
theorem subd8_3_491 : subd8_3 [2, 1, 5] = true := by decide +kernel
theorem subd8_3_492 : subd8_3 [2, 1, 6] = true := by decide +kernel
theorem subd8_3_493 : subd8_3 [2, 2] = true := by decide +kernel
theorem subd8_3_494 : subd8_3 [2, 3] = true := by decide +kernel
theorem subd8_3_495 : subd8_3 [3, -6] = true := by decide +kernel
theorem subd8_3_496 : subd8_3 [3, -5] = true := by decide +kernel
theorem subd8_3_497 : subd8_3 [3, -4] = true := by decide +kernel
theorem subd8_3_498 : subd8_3 [3, -3] = true := by decide +kernel
theorem subd8_3_499 : subd8_3 [3, -2] = true := by decide +kernel
theorem subd8_3_500 : subd8_3 [3, -1] = true := by decide +kernel
theorem subd8_3_501 : subd8_3 [3, 0] = true := by decide +kernel
theorem subd8_3_502 : subd8_3 [3, 1] = true := by decide +kernel
theorem subd8_3_503 : subd8_3 [3, 2] = true := by decide +kernel
theorem subd8_3_504 : subd8_3 [4] = true := by decide +kernel
theorem sbd8_3_15 : ∀ q ∈ blkd8_3_15, subd8_3 q = true := by
  unfold blkd8_3_15
  exact List.forall_mem_cons.2 ⟨subd8_3_480, List.forall_mem_cons.2 ⟨subd8_3_481, List.forall_mem_cons.2 ⟨subd8_3_482, List.forall_mem_cons.2 ⟨subd8_3_483, List.forall_mem_cons.2 ⟨subd8_3_484, List.forall_mem_cons.2 ⟨subd8_3_485, List.forall_mem_cons.2 ⟨subd8_3_486, List.forall_mem_cons.2 ⟨subd8_3_487, List.forall_mem_cons.2 ⟨subd8_3_488, List.forall_mem_cons.2 ⟨subd8_3_489, List.forall_mem_cons.2 ⟨subd8_3_490, List.forall_mem_cons.2 ⟨subd8_3_491, List.forall_mem_cons.2 ⟨subd8_3_492, List.forall_mem_cons.2 ⟨subd8_3_493, List.forall_mem_cons.2 ⟨subd8_3_494, List.forall_mem_cons.2 ⟨subd8_3_495, List.forall_mem_cons.2 ⟨subd8_3_496, List.forall_mem_cons.2 ⟨subd8_3_497, List.forall_mem_cons.2 ⟨subd8_3_498, List.forall_mem_cons.2 ⟨subd8_3_499, List.forall_mem_cons.2 ⟨subd8_3_500, List.forall_mem_cons.2 ⟨subd8_3_501, List.forall_mem_cons.2 ⟨subd8_3_502, List.forall_mem_cons.2 ⟨subd8_3_503, List.forall_mem_cons.2 ⟨subd8_3_504, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_0 : ldCheck G d9_0.U d9_0.ms ldd9_0 = true := by decide +kernel
theorem pre_okd9_0 : subPre G cell9 d9_0 = true := by decide +kernel
theorem subd9_0_0 : subd9_0 [-1] = true := by decide +kernel
theorem subd9_0_1 : subd9_0 [0] = true := by decide +kernel
theorem subd9_0_2 : subd9_0 [1] = true := by decide +kernel
theorem sbd9_0_0 : ∀ q ∈ blkd9_0_0, subd9_0 q = true := by
  unfold blkd9_0_0
  exact List.forall_mem_cons.2 ⟨subd9_0_0, List.forall_mem_cons.2 ⟨subd9_0_1, List.forall_mem_cons.2 ⟨subd9_0_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd9_1 : ldCheck G d9_1.U d9_1.ms ldd9_1 = true := by decide +kernel
theorem pre_okd9_1 : subPre G cell9 d9_1 = true := by decide +kernel
theorem subd9_1_0 : subd9_1 [-2] = true := by decide +kernel
theorem subd9_1_1 : subd9_1 [-1, -3] = true := by decide +kernel
theorem subd9_1_2 : subd9_1 [-1, -2] = true := by decide +kernel
theorem subd9_1_3 : subd9_1 [-1, -1] = true := by decide +kernel
theorem subd9_1_4 : subd9_1 [-1, 0] = true := by decide +kernel
theorem subd9_1_5 : subd9_1 [-1, 1] = true := by decide +kernel
theorem subd9_1_6 : subd9_1 [-1, 2] = true := by decide +kernel
theorem subd9_1_7 : subd9_1 [0, -3] = true := by decide +kernel
theorem subd9_1_8 : subd9_1 [0, -2] = true := by decide +kernel
theorem subd9_1_9 : subd9_1 [0, -1] = true := by decide +kernel
theorem subd9_1_10 : subd9_1 [0, 0] = true := by decide +kernel
theorem subd9_1_11 : subd9_1 [0, 1] = true := by decide +kernel
theorem subd9_1_12 : subd9_1 [0, 2] = true := by decide +kernel
theorem subd9_1_13 : subd9_1 [1, -3] = true := by decide +kernel
theorem subd9_1_14 : subd9_1 [1, -2] = true := by decide +kernel
theorem subd9_1_15 : subd9_1 [1, -1] = true := by decide +kernel
theorem subd9_1_16 : subd9_1 [1, 0] = true := by decide +kernel
theorem subd9_1_17 : subd9_1 [1, 1] = true := by decide +kernel
theorem subd9_1_18 : subd9_1 [1, 2] = true := by decide +kernel
theorem subd9_1_19 : subd9_1 [2] = true := by decide +kernel
theorem sbd9_1_0 : ∀ q ∈ blkd9_1_0, subd9_1 q = true := by
  unfold blkd9_1_0
  exact List.forall_mem_cons.2 ⟨subd9_1_0, List.forall_mem_cons.2 ⟨subd9_1_1, List.forall_mem_cons.2 ⟨subd9_1_2, List.forall_mem_cons.2 ⟨subd9_1_3, List.forall_mem_cons.2 ⟨subd9_1_4, List.forall_mem_cons.2 ⟨subd9_1_5, List.forall_mem_cons.2 ⟨subd9_1_6, List.forall_mem_cons.2 ⟨subd9_1_7, List.forall_mem_cons.2 ⟨subd9_1_8, List.forall_mem_cons.2 ⟨subd9_1_9, List.forall_mem_cons.2 ⟨subd9_1_10, List.forall_mem_cons.2 ⟨subd9_1_11, List.forall_mem_cons.2 ⟨subd9_1_12, List.forall_mem_cons.2 ⟨subd9_1_13, List.forall_mem_cons.2 ⟨subd9_1_14, List.forall_mem_cons.2 ⟨subd9_1_15, List.forall_mem_cons.2 ⟨subd9_1_16, List.forall_mem_cons.2 ⟨subd9_1_17, List.forall_mem_cons.2 ⟨subd9_1_18, List.forall_mem_cons.2 ⟨subd9_1_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_2 : ldCheck G d9_2.U d9_2.ms ldd9_2 = true := by decide +kernel
theorem pre_okd9_2 : subPre G cell9 d9_2 = true := by decide +kernel
theorem subd9_2_0 : subd9_2 [-1, -2] = true := by decide +kernel
theorem subd9_2_1 : subd9_2 [-1, -1, -8] = true := by decide +kernel
theorem subd9_2_2 : subd9_2 [-1, -1, -7] = true := by decide +kernel
theorem subd9_2_3 : subd9_2 [-1, -1, -6] = true := by decide +kernel
theorem subd9_2_4 : subd9_2 [-1, -1, -5] = true := by decide +kernel
theorem subd9_2_5 : subd9_2 [-1, -1, -4] = true := by decide +kernel
theorem subd9_2_6 : subd9_2 [-1, -1, -3] = true := by decide +kernel
theorem subd9_2_7 : subd9_2 [-1, -1, -2] = true := by decide +kernel
theorem subd9_2_8 : subd9_2 [-1, -1, -1] = true := by decide +kernel
theorem subd9_2_9 : subd9_2 [-1, -1, 0] = true := by decide +kernel
theorem subd9_2_10 : subd9_2 [-1, -1, 1] = true := by decide +kernel
theorem subd9_2_11 : subd9_2 [-1, -1, 2] = true := by decide +kernel
theorem subd9_2_12 : subd9_2 [-1, -1, 3] = true := by decide +kernel
theorem subd9_2_13 : subd9_2 [-1, -1, 4] = true := by decide +kernel
theorem subd9_2_14 : subd9_2 [-1, -1, 5] = true := by decide +kernel
theorem subd9_2_15 : subd9_2 [-1, -1, 6] = true := by decide +kernel
theorem subd9_2_16 : subd9_2 [-1, -1, 7] = true := by decide +kernel
theorem subd9_2_17 : subd9_2 [-1, 0, -10] = true := by decide +kernel
theorem subd9_2_18 : subd9_2 [-1, 0, -9] = true := by decide +kernel
theorem subd9_2_19 : subd9_2 [-1, 0, -8] = true := by decide +kernel
theorem subd9_2_20 : subd9_2 [-1, 0, -7] = true := by decide +kernel
theorem subd9_2_21 : subd9_2 [-1, 0, -6] = true := by decide +kernel
theorem subd9_2_22 : subd9_2 [-1, 0, -5] = true := by decide +kernel
theorem subd9_2_23 : subd9_2 [-1, 0, -4] = true := by decide +kernel
theorem subd9_2_24 : subd9_2 [-1, 0, -3] = true := by decide +kernel
theorem subd9_2_25 : subd9_2 [-1, 0, -2] = true := by decide +kernel
theorem subd9_2_26 : subd9_2 [-1, 0, -1] = true := by decide +kernel
theorem subd9_2_27 : subd9_2 [-1, 0, 0] = true := by decide +kernel
theorem subd9_2_28 : subd9_2 [-1, 0, 1] = true := by decide +kernel
theorem subd9_2_29 : subd9_2 [-1, 0, 2] = true := by decide +kernel
theorem subd9_2_30 : subd9_2 [-1, 0, 3] = true := by decide +kernel
theorem subd9_2_31 : subd9_2 [-1, 0, 4] = true := by decide +kernel
theorem sbd9_2_0 : ∀ q ∈ blkd9_2_0, subd9_2 q = true := by
  unfold blkd9_2_0
  exact List.forall_mem_cons.2 ⟨subd9_2_0, List.forall_mem_cons.2 ⟨subd9_2_1, List.forall_mem_cons.2 ⟨subd9_2_2, List.forall_mem_cons.2 ⟨subd9_2_3, List.forall_mem_cons.2 ⟨subd9_2_4, List.forall_mem_cons.2 ⟨subd9_2_5, List.forall_mem_cons.2 ⟨subd9_2_6, List.forall_mem_cons.2 ⟨subd9_2_7, List.forall_mem_cons.2 ⟨subd9_2_8, List.forall_mem_cons.2 ⟨subd9_2_9, List.forall_mem_cons.2 ⟨subd9_2_10, List.forall_mem_cons.2 ⟨subd9_2_11, List.forall_mem_cons.2 ⟨subd9_2_12, List.forall_mem_cons.2 ⟨subd9_2_13, List.forall_mem_cons.2 ⟨subd9_2_14, List.forall_mem_cons.2 ⟨subd9_2_15, List.forall_mem_cons.2 ⟨subd9_2_16, List.forall_mem_cons.2 ⟨subd9_2_17, List.forall_mem_cons.2 ⟨subd9_2_18, List.forall_mem_cons.2 ⟨subd9_2_19, List.forall_mem_cons.2 ⟨subd9_2_20, List.forall_mem_cons.2 ⟨subd9_2_21, List.forall_mem_cons.2 ⟨subd9_2_22, List.forall_mem_cons.2 ⟨subd9_2_23, List.forall_mem_cons.2 ⟨subd9_2_24, List.forall_mem_cons.2 ⟨subd9_2_25, List.forall_mem_cons.2 ⟨subd9_2_26, List.forall_mem_cons.2 ⟨subd9_2_27, List.forall_mem_cons.2 ⟨subd9_2_28, List.forall_mem_cons.2 ⟨subd9_2_29, List.forall_mem_cons.2 ⟨subd9_2_30, List.forall_mem_cons.2 ⟨subd9_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C111
