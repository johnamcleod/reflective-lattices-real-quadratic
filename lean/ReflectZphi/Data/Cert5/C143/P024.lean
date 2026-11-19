import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd14_1_320 : subd14_1 [0, -3, -1] = true := by decide +kernel
theorem subd14_1_321 : subd14_1 [0, -3, 0] = true := by decide +kernel
theorem subd14_1_322 : subd14_1 [0, -3, 1] = true := by decide +kernel
theorem subd14_1_323 : subd14_1 [0, -3, 2] = true := by decide +kernel
theorem subd14_1_324 : subd14_1 [0, -3, 3] = true := by decide +kernel
theorem subd14_1_325 : subd14_1 [0, -3, 4] = true := by decide +kernel
theorem subd14_1_326 : subd14_1 [0, -2, -8] = true := by decide +kernel
theorem subd14_1_327 : subd14_1 [0, -2, -7] = true := by decide +kernel
theorem subd14_1_328 : subd14_1 [0, -2, -6] = true := by decide +kernel
theorem subd14_1_329 : subd14_1 [0, -2, -5] = true := by decide +kernel
theorem subd14_1_330 : subd14_1 [0, -2, -4] = true := by decide +kernel
theorem subd14_1_331 : subd14_1 [0, -2, -3] = true := by decide +kernel
theorem subd14_1_332 : subd14_1 [0, -2, -2] = true := by decide +kernel
theorem subd14_1_333 : subd14_1 [0, -2, -1] = true := by decide +kernel
theorem subd14_1_334 : subd14_1 [0, -2, 0] = true := by decide +kernel
theorem subd14_1_335 : subd14_1 [0, -2, 1] = true := by decide +kernel
theorem subd14_1_336 : subd14_1 [0, -2, 2] = true := by decide +kernel
theorem subd14_1_337 : subd14_1 [0, -2, 3] = true := by decide +kernel
theorem subd14_1_338 : subd14_1 [0, -2, 4] = true := by decide +kernel
theorem subd14_1_339 : subd14_1 [0, -2, 5] = true := by decide +kernel
theorem subd14_1_340 : subd14_1 [0, -1, -8] = true := by decide +kernel
theorem subd14_1_341 : subd14_1 [0, -1, -7] = true := by decide +kernel
theorem subd14_1_342 : subd14_1 [0, -1, -6] = true := by decide +kernel
theorem subd14_1_343 : subd14_1 [0, -1, -5] = true := by decide +kernel
theorem subd14_1_344 : subd14_1 [0, -1, -4] = true := by decide +kernel
theorem subd14_1_345 : subd14_1 [0, -1, -3] = true := by decide +kernel
theorem subd14_1_346 : subd14_1 [0, -1, -2] = true := by decide +kernel
theorem subd14_1_347 : subd14_1 [0, -1, -1] = true := by decide +kernel
theorem subd14_1_348 : subd14_1 [0, -1, 0] = true := by decide +kernel
theorem subd14_1_349 : subd14_1 [0, -1, 1] = true := by decide +kernel
theorem subd14_1_350 : subd14_1 [0, -1, 2] = true := by decide +kernel
theorem subd14_1_351 : subd14_1 [0, -1, 3] = true := by decide +kernel
theorem sbd14_1_10 : ∀ q ∈ blkd14_1_10, subd14_1 q = true := by
  unfold blkd14_1_10
  exact List.forall_mem_cons.2 ⟨subd14_1_320, List.forall_mem_cons.2 ⟨subd14_1_321, List.forall_mem_cons.2 ⟨subd14_1_322, List.forall_mem_cons.2 ⟨subd14_1_323, List.forall_mem_cons.2 ⟨subd14_1_324, List.forall_mem_cons.2 ⟨subd14_1_325, List.forall_mem_cons.2 ⟨subd14_1_326, List.forall_mem_cons.2 ⟨subd14_1_327, List.forall_mem_cons.2 ⟨subd14_1_328, List.forall_mem_cons.2 ⟨subd14_1_329, List.forall_mem_cons.2 ⟨subd14_1_330, List.forall_mem_cons.2 ⟨subd14_1_331, List.forall_mem_cons.2 ⟨subd14_1_332, List.forall_mem_cons.2 ⟨subd14_1_333, List.forall_mem_cons.2 ⟨subd14_1_334, List.forall_mem_cons.2 ⟨subd14_1_335, List.forall_mem_cons.2 ⟨subd14_1_336, List.forall_mem_cons.2 ⟨subd14_1_337, List.forall_mem_cons.2 ⟨subd14_1_338, List.forall_mem_cons.2 ⟨subd14_1_339, List.forall_mem_cons.2 ⟨subd14_1_340, List.forall_mem_cons.2 ⟨subd14_1_341, List.forall_mem_cons.2 ⟨subd14_1_342, List.forall_mem_cons.2 ⟨subd14_1_343, List.forall_mem_cons.2 ⟨subd14_1_344, List.forall_mem_cons.2 ⟨subd14_1_345, List.forall_mem_cons.2 ⟨subd14_1_346, List.forall_mem_cons.2 ⟨subd14_1_347, List.forall_mem_cons.2 ⟨subd14_1_348, List.forall_mem_cons.2 ⟨subd14_1_349, List.forall_mem_cons.2 ⟨subd14_1_350, List.forall_mem_cons.2 ⟨subd14_1_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_1_352 : subd14_1 [0, -1, 4] = true := by decide +kernel
theorem subd14_1_353 : subd14_1 [0, -1, 5] = true := by decide +kernel
theorem subd14_1_354 : subd14_1 [0, -1, 6] = true := by decide +kernel
theorem subd14_1_355 : subd14_1 [0, 0, -7] = true := by decide +kernel
theorem subd14_1_356 : subd14_1 [0, 0, -6] = true := by decide +kernel
theorem subd14_1_357 : subd14_1 [0, 0, -5] = true := by decide +kernel
theorem subd14_1_358 : subd14_1 [0, 0, -4] = true := by decide +kernel
theorem subd14_1_359 : subd14_1 [0, 0, -3] = true := by decide +kernel
theorem subd14_1_360 : subd14_1 [0, 0, -2] = true := by decide +kernel
theorem subd14_1_361 : subd14_1 [0, 0, -1] = true := by decide +kernel
theorem subd14_1_362 : subd14_1 [0, 0, 0] = true := by decide +kernel
theorem subd14_1_363 : subd14_1 [0, 0, 1] = true := by decide +kernel
theorem subd14_1_364 : subd14_1 [0, 0, 2] = true := by decide +kernel
theorem subd14_1_365 : subd14_1 [0, 0, 3] = true := by decide +kernel
theorem subd14_1_366 : subd14_1 [0, 0, 4] = true := by decide +kernel
theorem subd14_1_367 : subd14_1 [0, 0, 5] = true := by decide +kernel
theorem subd14_1_368 : subd14_1 [0, 0, 6] = true := by decide +kernel
theorem subd14_1_369 : subd14_1 [0, 1, -7] = true := by decide +kernel
theorem subd14_1_370 : subd14_1 [0, 1, -6] = true := by decide +kernel
theorem subd14_1_371 : subd14_1 [0, 1, -5] = true := by decide +kernel
theorem subd14_1_372 : subd14_1 [0, 1, -4] = true := by decide +kernel
theorem subd14_1_373 : subd14_1 [0, 1, -3] = true := by decide +kernel
theorem subd14_1_374 : subd14_1 [0, 1, -2] = true := by decide +kernel
theorem subd14_1_375 : subd14_1 [0, 1, -1] = true := by decide +kernel
theorem subd14_1_376 : subd14_1 [0, 1, 0] = true := by decide +kernel
theorem subd14_1_377 : subd14_1 [0, 1, 1] = true := by decide +kernel
theorem subd14_1_378 : subd14_1 [0, 1, 2] = true := by decide +kernel
theorem subd14_1_379 : subd14_1 [0, 1, 3] = true := by decide +kernel
theorem subd14_1_380 : subd14_1 [0, 1, 4] = true := by decide +kernel
theorem subd14_1_381 : subd14_1 [0, 1, 5] = true := by decide +kernel
theorem subd14_1_382 : subd14_1 [0, 1, 6] = true := by decide +kernel
theorem subd14_1_383 : subd14_1 [0, 1, 7] = true := by decide +kernel
theorem sbd14_1_11 : ∀ q ∈ blkd14_1_11, subd14_1 q = true := by
  unfold blkd14_1_11
  exact List.forall_mem_cons.2 ⟨subd14_1_352, List.forall_mem_cons.2 ⟨subd14_1_353, List.forall_mem_cons.2 ⟨subd14_1_354, List.forall_mem_cons.2 ⟨subd14_1_355, List.forall_mem_cons.2 ⟨subd14_1_356, List.forall_mem_cons.2 ⟨subd14_1_357, List.forall_mem_cons.2 ⟨subd14_1_358, List.forall_mem_cons.2 ⟨subd14_1_359, List.forall_mem_cons.2 ⟨subd14_1_360, List.forall_mem_cons.2 ⟨subd14_1_361, List.forall_mem_cons.2 ⟨subd14_1_362, List.forall_mem_cons.2 ⟨subd14_1_363, List.forall_mem_cons.2 ⟨subd14_1_364, List.forall_mem_cons.2 ⟨subd14_1_365, List.forall_mem_cons.2 ⟨subd14_1_366, List.forall_mem_cons.2 ⟨subd14_1_367, List.forall_mem_cons.2 ⟨subd14_1_368, List.forall_mem_cons.2 ⟨subd14_1_369, List.forall_mem_cons.2 ⟨subd14_1_370, List.forall_mem_cons.2 ⟨subd14_1_371, List.forall_mem_cons.2 ⟨subd14_1_372, List.forall_mem_cons.2 ⟨subd14_1_373, List.forall_mem_cons.2 ⟨subd14_1_374, List.forall_mem_cons.2 ⟨subd14_1_375, List.forall_mem_cons.2 ⟨subd14_1_376, List.forall_mem_cons.2 ⟨subd14_1_377, List.forall_mem_cons.2 ⟨subd14_1_378, List.forall_mem_cons.2 ⟨subd14_1_379, List.forall_mem_cons.2 ⟨subd14_1_380, List.forall_mem_cons.2 ⟨subd14_1_381, List.forall_mem_cons.2 ⟨subd14_1_382, List.forall_mem_cons.2 ⟨subd14_1_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_1_384 : subd14_1 [0, 2, -6] = true := by decide +kernel
theorem subd14_1_385 : subd14_1 [0, 2, -5] = true := by decide +kernel
theorem subd14_1_386 : subd14_1 [0, 2, -4] = true := by decide +kernel
theorem subd14_1_387 : subd14_1 [0, 2, -3] = true := by decide +kernel
theorem subd14_1_388 : subd14_1 [0, 2, -2] = true := by decide +kernel
theorem subd14_1_389 : subd14_1 [0, 2, -1] = true := by decide +kernel
theorem subd14_1_390 : subd14_1 [0, 2, 0] = true := by decide +kernel
theorem subd14_1_391 : subd14_1 [0, 2, 1] = true := by decide +kernel
theorem subd14_1_392 : subd14_1 [0, 2, 2] = true := by decide +kernel
theorem subd14_1_393 : subd14_1 [0, 2, 3] = true := by decide +kernel
theorem subd14_1_394 : subd14_1 [0, 2, 4] = true := by decide +kernel
theorem subd14_1_395 : subd14_1 [0, 2, 5] = true := by decide +kernel
theorem subd14_1_396 : subd14_1 [0, 2, 6] = true := by decide +kernel
theorem subd14_1_397 : subd14_1 [0, 2, 7] = true := by decide +kernel
theorem subd14_1_398 : subd14_1 [0, 3, -5] = true := by decide +kernel
theorem subd14_1_399 : subd14_1 [0, 3, -4] = true := by decide +kernel
theorem subd14_1_400 : subd14_1 [0, 3, -3] = true := by decide +kernel
theorem subd14_1_401 : subd14_1 [0, 3, -2] = true := by decide +kernel
theorem subd14_1_402 : subd14_1 [0, 3, -1] = true := by decide +kernel
theorem subd14_1_403 : subd14_1 [0, 3, 0] = true := by decide +kernel
theorem subd14_1_404 : subd14_1 [0, 3, 1] = true := by decide +kernel
theorem subd14_1_405 : subd14_1 [0, 3, 2] = true := by decide +kernel
theorem subd14_1_406 : subd14_1 [0, 3, 3] = true := by decide +kernel
theorem subd14_1_407 : subd14_1 [0, 3, 4] = true := by decide +kernel
theorem subd14_1_408 : subd14_1 [0, 3, 5] = true := by decide +kernel
theorem subd14_1_409 : subd14_1 [0, 3, 6] = true := by decide +kernel
theorem subd14_1_410 : subd14_1 [0, 3, 7] = true := by decide +kernel
theorem subd14_1_411 : subd14_1 [0, 4] = true := by decide +kernel
theorem subd14_1_412 : subd14_1 [0, 5] = true := by decide +kernel
theorem subd14_1_413 : subd14_1 [0, 6] = true := by decide +kernel
theorem subd14_1_414 : subd14_1 [0, 7] = true := by decide +kernel
theorem subd14_1_415 : subd14_1 [0, 8] = true := by decide +kernel
theorem sbd14_1_12 : ∀ q ∈ blkd14_1_12, subd14_1 q = true := by
  unfold blkd14_1_12
  exact List.forall_mem_cons.2 ⟨subd14_1_384, List.forall_mem_cons.2 ⟨subd14_1_385, List.forall_mem_cons.2 ⟨subd14_1_386, List.forall_mem_cons.2 ⟨subd14_1_387, List.forall_mem_cons.2 ⟨subd14_1_388, List.forall_mem_cons.2 ⟨subd14_1_389, List.forall_mem_cons.2 ⟨subd14_1_390, List.forall_mem_cons.2 ⟨subd14_1_391, List.forall_mem_cons.2 ⟨subd14_1_392, List.forall_mem_cons.2 ⟨subd14_1_393, List.forall_mem_cons.2 ⟨subd14_1_394, List.forall_mem_cons.2 ⟨subd14_1_395, List.forall_mem_cons.2 ⟨subd14_1_396, List.forall_mem_cons.2 ⟨subd14_1_397, List.forall_mem_cons.2 ⟨subd14_1_398, List.forall_mem_cons.2 ⟨subd14_1_399, List.forall_mem_cons.2 ⟨subd14_1_400, List.forall_mem_cons.2 ⟨subd14_1_401, List.forall_mem_cons.2 ⟨subd14_1_402, List.forall_mem_cons.2 ⟨subd14_1_403, List.forall_mem_cons.2 ⟨subd14_1_404, List.forall_mem_cons.2 ⟨subd14_1_405, List.forall_mem_cons.2 ⟨subd14_1_406, List.forall_mem_cons.2 ⟨subd14_1_407, List.forall_mem_cons.2 ⟨subd14_1_408, List.forall_mem_cons.2 ⟨subd14_1_409, List.forall_mem_cons.2 ⟨subd14_1_410, List.forall_mem_cons.2 ⟨subd14_1_411, List.forall_mem_cons.2 ⟨subd14_1_412, List.forall_mem_cons.2 ⟨subd14_1_413, List.forall_mem_cons.2 ⟨subd14_1_414, List.forall_mem_cons.2 ⟨subd14_1_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_1_416 : subd14_1 [1, -8] = true := by decide +kernel
theorem subd14_1_417 : subd14_1 [1, -7] = true := by decide +kernel
theorem subd14_1_418 : subd14_1 [1, -6] = true := by decide +kernel
theorem subd14_1_419 : subd14_1 [1, -5] = true := by decide +kernel
theorem subd14_1_420 : subd14_1 [1, -4] = true := by decide +kernel
theorem subd14_1_421 : subd14_1 [1, -3, -9] = true := by decide +kernel
theorem subd14_1_422 : subd14_1 [1, -3, -8] = true := by decide +kernel
theorem subd14_1_423 : subd14_1 [1, -3, -7] = true := by decide +kernel
theorem subd14_1_424 : subd14_1 [1, -3, -6] = true := by decide +kernel
theorem subd14_1_425 : subd14_1 [1, -3, -5] = true := by decide +kernel
theorem subd14_1_426 : subd14_1 [1, -3, -4] = true := by decide +kernel
theorem subd14_1_427 : subd14_1 [1, -3, -3] = true := by decide +kernel
theorem subd14_1_428 : subd14_1 [1, -3, -2] = true := by decide +kernel
theorem subd14_1_429 : subd14_1 [1, -3, -1] = true := by decide +kernel
theorem subd14_1_430 : subd14_1 [1, -3, 0] = true := by decide +kernel
theorem subd14_1_431 : subd14_1 [1, -3, 1] = true := by decide +kernel
theorem subd14_1_432 : subd14_1 [1, -3, 2] = true := by decide +kernel
theorem subd14_1_433 : subd14_1 [1, -3, 3] = true := by decide +kernel
theorem subd14_1_434 : subd14_1 [1, -3, 4] = true := by decide +kernel
theorem subd14_1_435 : subd14_1 [1, -2, -8] = true := by decide +kernel
theorem subd14_1_436 : subd14_1 [1, -2, -7] = true := by decide +kernel
theorem subd14_1_437 : subd14_1 [1, -2, -6] = true := by decide +kernel
theorem subd14_1_438 : subd14_1 [1, -2, -5] = true := by decide +kernel
theorem subd14_1_439 : subd14_1 [1, -2, -4] = true := by decide +kernel
theorem subd14_1_440 : subd14_1 [1, -2, -3] = true := by decide +kernel
theorem subd14_1_441 : subd14_1 [1, -2, -2] = true := by decide +kernel
theorem subd14_1_442 : subd14_1 [1, -2, -1] = true := by decide +kernel
theorem subd14_1_443 : subd14_1 [1, -2, 0] = true := by decide +kernel
theorem subd14_1_444 : subd14_1 [1, -2, 1] = true := by decide +kernel
theorem subd14_1_445 : subd14_1 [1, -2, 2] = true := by decide +kernel
theorem subd14_1_446 : subd14_1 [1, -2, 3] = true := by decide +kernel
theorem subd14_1_447 : subd14_1 [1, -2, 4] = true := by decide +kernel
theorem sbd14_1_13 : ∀ q ∈ blkd14_1_13, subd14_1 q = true := by
  unfold blkd14_1_13
  exact List.forall_mem_cons.2 ⟨subd14_1_416, List.forall_mem_cons.2 ⟨subd14_1_417, List.forall_mem_cons.2 ⟨subd14_1_418, List.forall_mem_cons.2 ⟨subd14_1_419, List.forall_mem_cons.2 ⟨subd14_1_420, List.forall_mem_cons.2 ⟨subd14_1_421, List.forall_mem_cons.2 ⟨subd14_1_422, List.forall_mem_cons.2 ⟨subd14_1_423, List.forall_mem_cons.2 ⟨subd14_1_424, List.forall_mem_cons.2 ⟨subd14_1_425, List.forall_mem_cons.2 ⟨subd14_1_426, List.forall_mem_cons.2 ⟨subd14_1_427, List.forall_mem_cons.2 ⟨subd14_1_428, List.forall_mem_cons.2 ⟨subd14_1_429, List.forall_mem_cons.2 ⟨subd14_1_430, List.forall_mem_cons.2 ⟨subd14_1_431, List.forall_mem_cons.2 ⟨subd14_1_432, List.forall_mem_cons.2 ⟨subd14_1_433, List.forall_mem_cons.2 ⟨subd14_1_434, List.forall_mem_cons.2 ⟨subd14_1_435, List.forall_mem_cons.2 ⟨subd14_1_436, List.forall_mem_cons.2 ⟨subd14_1_437, List.forall_mem_cons.2 ⟨subd14_1_438, List.forall_mem_cons.2 ⟨subd14_1_439, List.forall_mem_cons.2 ⟨subd14_1_440, List.forall_mem_cons.2 ⟨subd14_1_441, List.forall_mem_cons.2 ⟨subd14_1_442, List.forall_mem_cons.2 ⟨subd14_1_443, List.forall_mem_cons.2 ⟨subd14_1_444, List.forall_mem_cons.2 ⟨subd14_1_445, List.forall_mem_cons.2 ⟨subd14_1_446, List.forall_mem_cons.2 ⟨subd14_1_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_1_448 : subd14_1 [1, -2, 5] = true := by decide +kernel
theorem subd14_1_449 : subd14_1 [1, -1, -8] = true := by decide +kernel
theorem subd14_1_450 : subd14_1 [1, -1, -7] = true := by decide +kernel
theorem subd14_1_451 : subd14_1 [1, -1, -6] = true := by decide +kernel
theorem subd14_1_452 : subd14_1 [1, -1, -5] = true := by decide +kernel
theorem subd14_1_453 : subd14_1 [1, -1, -4] = true := by decide +kernel
theorem subd14_1_454 : subd14_1 [1, -1, -3] = true := by decide +kernel
theorem subd14_1_455 : subd14_1 [1, -1, -2] = true := by decide +kernel
theorem subd14_1_456 : subd14_1 [1, -1, -1] = true := by decide +kernel
theorem subd14_1_457 : subd14_1 [1, -1, 0] = true := by decide +kernel
theorem subd14_1_458 : subd14_1 [1, -1, 1] = true := by decide +kernel
theorem subd14_1_459 : subd14_1 [1, -1, 2] = true := by decide +kernel
theorem subd14_1_460 : subd14_1 [1, -1, 3] = true := by decide +kernel
theorem subd14_1_461 : subd14_1 [1, -1, 4] = true := by decide +kernel
theorem subd14_1_462 : subd14_1 [1, -1, 5] = true := by decide +kernel
theorem subd14_1_463 : subd14_1 [1, 0, -8] = true := by decide +kernel
theorem subd14_1_464 : subd14_1 [1, 0, -7] = true := by decide +kernel
theorem subd14_1_465 : subd14_1 [1, 0, -6] = true := by decide +kernel
theorem subd14_1_466 : subd14_1 [1, 0, -5] = true := by decide +kernel
theorem subd14_1_467 : subd14_1 [1, 0, -4] = true := by decide +kernel
theorem subd14_1_468 : subd14_1 [1, 0, -3] = true := by decide +kernel
theorem subd14_1_469 : subd14_1 [1, 0, -2] = true := by decide +kernel
theorem subd14_1_470 : subd14_1 [1, 0, -1] = true := by decide +kernel
theorem subd14_1_471 : subd14_1 [1, 0, 0] = true := by decide +kernel
theorem subd14_1_472 : subd14_1 [1, 0, 1] = true := by decide +kernel
theorem subd14_1_473 : subd14_1 [1, 0, 2] = true := by decide +kernel
theorem subd14_1_474 : subd14_1 [1, 0, 3] = true := by decide +kernel
theorem subd14_1_475 : subd14_1 [1, 0, 4] = true := by decide +kernel
theorem subd14_1_476 : subd14_1 [1, 0, 5] = true := by decide +kernel
theorem subd14_1_477 : subd14_1 [1, 0, 6] = true := by decide +kernel
theorem subd14_1_478 : subd14_1 [1, 1, -7] = true := by decide +kernel
theorem subd14_1_479 : subd14_1 [1, 1, -6] = true := by decide +kernel
theorem sbd14_1_14 : ∀ q ∈ blkd14_1_14, subd14_1 q = true := by
  unfold blkd14_1_14
  exact List.forall_mem_cons.2 ⟨subd14_1_448, List.forall_mem_cons.2 ⟨subd14_1_449, List.forall_mem_cons.2 ⟨subd14_1_450, List.forall_mem_cons.2 ⟨subd14_1_451, List.forall_mem_cons.2 ⟨subd14_1_452, List.forall_mem_cons.2 ⟨subd14_1_453, List.forall_mem_cons.2 ⟨subd14_1_454, List.forall_mem_cons.2 ⟨subd14_1_455, List.forall_mem_cons.2 ⟨subd14_1_456, List.forall_mem_cons.2 ⟨subd14_1_457, List.forall_mem_cons.2 ⟨subd14_1_458, List.forall_mem_cons.2 ⟨subd14_1_459, List.forall_mem_cons.2 ⟨subd14_1_460, List.forall_mem_cons.2 ⟨subd14_1_461, List.forall_mem_cons.2 ⟨subd14_1_462, List.forall_mem_cons.2 ⟨subd14_1_463, List.forall_mem_cons.2 ⟨subd14_1_464, List.forall_mem_cons.2 ⟨subd14_1_465, List.forall_mem_cons.2 ⟨subd14_1_466, List.forall_mem_cons.2 ⟨subd14_1_467, List.forall_mem_cons.2 ⟨subd14_1_468, List.forall_mem_cons.2 ⟨subd14_1_469, List.forall_mem_cons.2 ⟨subd14_1_470, List.forall_mem_cons.2 ⟨subd14_1_471, List.forall_mem_cons.2 ⟨subd14_1_472, List.forall_mem_cons.2 ⟨subd14_1_473, List.forall_mem_cons.2 ⟨subd14_1_474, List.forall_mem_cons.2 ⟨subd14_1_475, List.forall_mem_cons.2 ⟨subd14_1_476, List.forall_mem_cons.2 ⟨subd14_1_477, List.forall_mem_cons.2 ⟨subd14_1_478, List.forall_mem_cons.2 ⟨subd14_1_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_1_480 : subd14_1 [1, 1, -5] = true := by decide +kernel
theorem subd14_1_481 : subd14_1 [1, 1, -4] = true := by decide +kernel
theorem subd14_1_482 : subd14_1 [1, 1, -3] = true := by decide +kernel
theorem subd14_1_483 : subd14_1 [1, 1, -2] = true := by decide +kernel
theorem subd14_1_484 : subd14_1 [1, 1, -1] = true := by decide +kernel
theorem subd14_1_485 : subd14_1 [1, 1, 0] = true := by decide +kernel
theorem subd14_1_486 : subd14_1 [1, 1, 1] = true := by decide +kernel
theorem subd14_1_487 : subd14_1 [1, 1, 2] = true := by decide +kernel
theorem subd14_1_488 : subd14_1 [1, 1, 3] = true := by decide +kernel
theorem subd14_1_489 : subd14_1 [1, 1, 4] = true := by decide +kernel
theorem subd14_1_490 : subd14_1 [1, 1, 5] = true := by decide +kernel
theorem subd14_1_491 : subd14_1 [1, 1, 6] = true := by decide +kernel
theorem subd14_1_492 : subd14_1 [1, 2, -6] = true := by decide +kernel
theorem subd14_1_493 : subd14_1 [1, 2, -5] = true := by decide +kernel
theorem subd14_1_494 : subd14_1 [1, 2, -4] = true := by decide +kernel
theorem subd14_1_495 : subd14_1 [1, 2, -3] = true := by decide +kernel
theorem subd14_1_496 : subd14_1 [1, 2, -2] = true := by decide +kernel
theorem subd14_1_497 : subd14_1 [1, 2, -1] = true := by decide +kernel
theorem subd14_1_498 : subd14_1 [1, 2, 0] = true := by decide +kernel
theorem subd14_1_499 : subd14_1 [1, 2, 1] = true := by decide +kernel
theorem subd14_1_500 : subd14_1 [1, 2, 2] = true := by decide +kernel
theorem subd14_1_501 : subd14_1 [1, 2, 3] = true := by decide +kernel
theorem subd14_1_502 : subd14_1 [1, 2, 4] = true := by decide +kernel
theorem subd14_1_503 : subd14_1 [1, 2, 5] = true := by decide +kernel
theorem subd14_1_504 : subd14_1 [1, 2, 6] = true := by decide +kernel
theorem subd14_1_505 : subd14_1 [1, 2, 7] = true := by decide +kernel
theorem subd14_1_506 : subd14_1 [1, 3, -6] = true := by decide +kernel
theorem subd14_1_507 : subd14_1 [1, 3, -5] = true := by decide +kernel
theorem subd14_1_508 : subd14_1 [1, 3, -4] = true := by decide +kernel
theorem subd14_1_509 : subd14_1 [1, 3, -3] = true := by decide +kernel
theorem subd14_1_510 : subd14_1 [1, 3, -2] = true := by decide +kernel
theorem subd14_1_511 : subd14_1 [1, 3, -1] = true := by decide +kernel
theorem sbd14_1_15 : ∀ q ∈ blkd14_1_15, subd14_1 q = true := by
  unfold blkd14_1_15
  exact List.forall_mem_cons.2 ⟨subd14_1_480, List.forall_mem_cons.2 ⟨subd14_1_481, List.forall_mem_cons.2 ⟨subd14_1_482, List.forall_mem_cons.2 ⟨subd14_1_483, List.forall_mem_cons.2 ⟨subd14_1_484, List.forall_mem_cons.2 ⟨subd14_1_485, List.forall_mem_cons.2 ⟨subd14_1_486, List.forall_mem_cons.2 ⟨subd14_1_487, List.forall_mem_cons.2 ⟨subd14_1_488, List.forall_mem_cons.2 ⟨subd14_1_489, List.forall_mem_cons.2 ⟨subd14_1_490, List.forall_mem_cons.2 ⟨subd14_1_491, List.forall_mem_cons.2 ⟨subd14_1_492, List.forall_mem_cons.2 ⟨subd14_1_493, List.forall_mem_cons.2 ⟨subd14_1_494, List.forall_mem_cons.2 ⟨subd14_1_495, List.forall_mem_cons.2 ⟨subd14_1_496, List.forall_mem_cons.2 ⟨subd14_1_497, List.forall_mem_cons.2 ⟨subd14_1_498, List.forall_mem_cons.2 ⟨subd14_1_499, List.forall_mem_cons.2 ⟨subd14_1_500, List.forall_mem_cons.2 ⟨subd14_1_501, List.forall_mem_cons.2 ⟨subd14_1_502, List.forall_mem_cons.2 ⟨subd14_1_503, List.forall_mem_cons.2 ⟨subd14_1_504, List.forall_mem_cons.2 ⟨subd14_1_505, List.forall_mem_cons.2 ⟨subd14_1_506, List.forall_mem_cons.2 ⟨subd14_1_507, List.forall_mem_cons.2 ⟨subd14_1_508, List.forall_mem_cons.2 ⟨subd14_1_509, List.forall_mem_cons.2 ⟨subd14_1_510, List.forall_mem_cons.2 ⟨subd14_1_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_1_512 : subd14_1 [1, 3, 0] = true := by decide +kernel
theorem subd14_1_513 : subd14_1 [1, 3, 1] = true := by decide +kernel
theorem subd14_1_514 : subd14_1 [1, 3, 2] = true := by decide +kernel
theorem subd14_1_515 : subd14_1 [1, 3, 3] = true := by decide +kernel
theorem subd14_1_516 : subd14_1 [1, 3, 4] = true := by decide +kernel
theorem subd14_1_517 : subd14_1 [1, 3, 5] = true := by decide +kernel
theorem subd14_1_518 : subd14_1 [1, 3, 6] = true := by decide +kernel
theorem subd14_1_519 : subd14_1 [1, 3, 7] = true := by decide +kernel
theorem subd14_1_520 : subd14_1 [1, 4] = true := by decide +kernel
theorem subd14_1_521 : subd14_1 [1, 5] = true := by decide +kernel
theorem subd14_1_522 : subd14_1 [1, 6] = true := by decide +kernel
theorem subd14_1_523 : subd14_1 [1, 7] = true := by decide +kernel
theorem subd14_1_524 : subd14_1 [1, 8] = true := by decide +kernel
theorem subd14_1_525 : subd14_1 [2, -8] = true := by decide +kernel
theorem subd14_1_526 : subd14_1 [2, -7] = true := by decide +kernel
theorem subd14_1_527 : subd14_1 [2, -6] = true := by decide +kernel
theorem subd14_1_528 : subd14_1 [2, -5] = true := by decide +kernel
theorem subd14_1_529 : subd14_1 [2, -4] = true := by decide +kernel
theorem subd14_1_530 : subd14_1 [2, -3] = true := by decide +kernel
theorem subd14_1_531 : subd14_1 [2, -2, -9] = true := by decide +kernel
theorem subd14_1_532 : subd14_1 [2, -2, -8] = true := by decide +kernel
theorem subd14_1_533 : subd14_1 [2, -2, -7] = true := by decide +kernel
theorem subd14_1_534 : subd14_1 [2, -2, -6] = true := by decide +kernel
theorem subd14_1_535 : subd14_1 [2, -2, -5] = true := by decide +kernel
theorem subd14_1_536 : subd14_1 [2, -2, -4] = true := by decide +kernel
theorem subd14_1_537 : subd14_1 [2, -2, -3] = true := by decide +kernel
theorem subd14_1_538 : subd14_1 [2, -2, -2] = true := by decide +kernel
theorem subd14_1_539 : subd14_1 [2, -2, -1] = true := by decide +kernel
theorem subd14_1_540 : subd14_1 [2, -2, 0] = true := by decide +kernel
theorem subd14_1_541 : subd14_1 [2, -2, 1] = true := by decide +kernel
theorem subd14_1_542 : subd14_1 [2, -2, 2] = true := by decide +kernel
theorem subd14_1_543 : subd14_1 [2, -2, 3] = true := by decide +kernel
theorem sbd14_1_16 : ∀ q ∈ blkd14_1_16, subd14_1 q = true := by
  unfold blkd14_1_16
  exact List.forall_mem_cons.2 ⟨subd14_1_512, List.forall_mem_cons.2 ⟨subd14_1_513, List.forall_mem_cons.2 ⟨subd14_1_514, List.forall_mem_cons.2 ⟨subd14_1_515, List.forall_mem_cons.2 ⟨subd14_1_516, List.forall_mem_cons.2 ⟨subd14_1_517, List.forall_mem_cons.2 ⟨subd14_1_518, List.forall_mem_cons.2 ⟨subd14_1_519, List.forall_mem_cons.2 ⟨subd14_1_520, List.forall_mem_cons.2 ⟨subd14_1_521, List.forall_mem_cons.2 ⟨subd14_1_522, List.forall_mem_cons.2 ⟨subd14_1_523, List.forall_mem_cons.2 ⟨subd14_1_524, List.forall_mem_cons.2 ⟨subd14_1_525, List.forall_mem_cons.2 ⟨subd14_1_526, List.forall_mem_cons.2 ⟨subd14_1_527, List.forall_mem_cons.2 ⟨subd14_1_528, List.forall_mem_cons.2 ⟨subd14_1_529, List.forall_mem_cons.2 ⟨subd14_1_530, List.forall_mem_cons.2 ⟨subd14_1_531, List.forall_mem_cons.2 ⟨subd14_1_532, List.forall_mem_cons.2 ⟨subd14_1_533, List.forall_mem_cons.2 ⟨subd14_1_534, List.forall_mem_cons.2 ⟨subd14_1_535, List.forall_mem_cons.2 ⟨subd14_1_536, List.forall_mem_cons.2 ⟨subd14_1_537, List.forall_mem_cons.2 ⟨subd14_1_538, List.forall_mem_cons.2 ⟨subd14_1_539, List.forall_mem_cons.2 ⟨subd14_1_540, List.forall_mem_cons.2 ⟨subd14_1_541, List.forall_mem_cons.2 ⟨subd14_1_542, List.forall_mem_cons.2 ⟨subd14_1_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_1_544 : subd14_1 [2, -2, 4] = true := by decide +kernel
theorem subd14_1_545 : subd14_1 [2, -1, -8] = true := by decide +kernel
theorem subd14_1_546 : subd14_1 [2, -1, -7] = true := by decide +kernel
theorem subd14_1_547 : subd14_1 [2, -1, -6] = true := by decide +kernel
theorem subd14_1_548 : subd14_1 [2, -1, -5] = true := by decide +kernel
theorem subd14_1_549 : subd14_1 [2, -1, -4] = true := by decide +kernel
theorem subd14_1_550 : subd14_1 [2, -1, -3] = true := by decide +kernel
theorem subd14_1_551 : subd14_1 [2, -1, -2] = true := by decide +kernel
theorem subd14_1_552 : subd14_1 [2, -1, -1] = true := by decide +kernel
theorem subd14_1_553 : subd14_1 [2, -1, 0] = true := by decide +kernel
theorem subd14_1_554 : subd14_1 [2, -1, 1] = true := by decide +kernel
theorem subd14_1_555 : subd14_1 [2, -1, 2] = true := by decide +kernel
theorem subd14_1_556 : subd14_1 [2, -1, 3] = true := by decide +kernel
theorem subd14_1_557 : subd14_1 [2, -1, 4] = true := by decide +kernel
theorem subd14_1_558 : subd14_1 [2, -1, 5] = true := by decide +kernel
theorem subd14_1_559 : subd14_1 [2, 0, -8] = true := by decide +kernel
theorem subd14_1_560 : subd14_1 [2, 0, -7] = true := by decide +kernel
theorem subd14_1_561 : subd14_1 [2, 0, -6] = true := by decide +kernel
theorem subd14_1_562 : subd14_1 [2, 0, -5] = true := by decide +kernel
theorem subd14_1_563 : subd14_1 [2, 0, -4] = true := by decide +kernel
theorem subd14_1_564 : subd14_1 [2, 0, -3] = true := by decide +kernel
theorem subd14_1_565 : subd14_1 [2, 0, -2] = true := by decide +kernel
theorem subd14_1_566 : subd14_1 [2, 0, -1] = true := by decide +kernel
theorem subd14_1_567 : subd14_1 [2, 0, 0] = true := by decide +kernel
theorem subd14_1_568 : subd14_1 [2, 0, 1] = true := by decide +kernel
theorem subd14_1_569 : subd14_1 [2, 0, 2] = true := by decide +kernel
theorem subd14_1_570 : subd14_1 [2, 0, 3] = true := by decide +kernel
theorem subd14_1_571 : subd14_1 [2, 0, 4] = true := by decide +kernel
theorem subd14_1_572 : subd14_1 [2, 0, 5] = true := by decide +kernel
theorem subd14_1_573 : subd14_1 [2, 1, -7] = true := by decide +kernel
theorem subd14_1_574 : subd14_1 [2, 1, -6] = true := by decide +kernel
theorem subd14_1_575 : subd14_1 [2, 1, -5] = true := by decide +kernel
theorem sbd14_1_17 : ∀ q ∈ blkd14_1_17, subd14_1 q = true := by
  unfold blkd14_1_17
  exact List.forall_mem_cons.2 ⟨subd14_1_544, List.forall_mem_cons.2 ⟨subd14_1_545, List.forall_mem_cons.2 ⟨subd14_1_546, List.forall_mem_cons.2 ⟨subd14_1_547, List.forall_mem_cons.2 ⟨subd14_1_548, List.forall_mem_cons.2 ⟨subd14_1_549, List.forall_mem_cons.2 ⟨subd14_1_550, List.forall_mem_cons.2 ⟨subd14_1_551, List.forall_mem_cons.2 ⟨subd14_1_552, List.forall_mem_cons.2 ⟨subd14_1_553, List.forall_mem_cons.2 ⟨subd14_1_554, List.forall_mem_cons.2 ⟨subd14_1_555, List.forall_mem_cons.2 ⟨subd14_1_556, List.forall_mem_cons.2 ⟨subd14_1_557, List.forall_mem_cons.2 ⟨subd14_1_558, List.forall_mem_cons.2 ⟨subd14_1_559, List.forall_mem_cons.2 ⟨subd14_1_560, List.forall_mem_cons.2 ⟨subd14_1_561, List.forall_mem_cons.2 ⟨subd14_1_562, List.forall_mem_cons.2 ⟨subd14_1_563, List.forall_mem_cons.2 ⟨subd14_1_564, List.forall_mem_cons.2 ⟨subd14_1_565, List.forall_mem_cons.2 ⟨subd14_1_566, List.forall_mem_cons.2 ⟨subd14_1_567, List.forall_mem_cons.2 ⟨subd14_1_568, List.forall_mem_cons.2 ⟨subd14_1_569, List.forall_mem_cons.2 ⟨subd14_1_570, List.forall_mem_cons.2 ⟨subd14_1_571, List.forall_mem_cons.2 ⟨subd14_1_572, List.forall_mem_cons.2 ⟨subd14_1_573, List.forall_mem_cons.2 ⟨subd14_1_574, List.forall_mem_cons.2 ⟨subd14_1_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_1_576 : subd14_1 [2, 1, -4] = true := by decide +kernel
theorem subd14_1_577 : subd14_1 [2, 1, -3] = true := by decide +kernel
theorem subd14_1_578 : subd14_1 [2, 1, -2] = true := by decide +kernel
theorem subd14_1_579 : subd14_1 [2, 1, -1] = true := by decide +kernel
theorem subd14_1_580 : subd14_1 [2, 1, 0] = true := by decide +kernel
theorem subd14_1_581 : subd14_1 [2, 1, 1] = true := by decide +kernel
theorem subd14_1_582 : subd14_1 [2, 1, 2] = true := by decide +kernel
theorem subd14_1_583 : subd14_1 [2, 1, 3] = true := by decide +kernel
theorem subd14_1_584 : subd14_1 [2, 1, 4] = true := by decide +kernel
theorem subd14_1_585 : subd14_1 [2, 1, 5] = true := by decide +kernel
theorem subd14_1_586 : subd14_1 [2, 1, 6] = true := by decide +kernel
theorem subd14_1_587 : subd14_1 [2, 2, -7] = true := by decide +kernel
theorem subd14_1_588 : subd14_1 [2, 2, -6] = true := by decide +kernel
theorem subd14_1_589 : subd14_1 [2, 2, -5] = true := by decide +kernel
theorem subd14_1_590 : subd14_1 [2, 2, -4] = true := by decide +kernel
theorem subd14_1_591 : subd14_1 [2, 2, -3] = true := by decide +kernel
theorem subd14_1_592 : subd14_1 [2, 2, -2] = true := by decide +kernel
theorem subd14_1_593 : subd14_1 [2, 2, -1] = true := by decide +kernel
theorem subd14_1_594 : subd14_1 [2, 2, 0] = true := by decide +kernel
theorem subd14_1_595 : subd14_1 [2, 2, 1] = true := by decide +kernel
theorem subd14_1_596 : subd14_1 [2, 2, 2] = true := by decide +kernel
theorem subd14_1_597 : subd14_1 [2, 2, 3] = true := by decide +kernel
theorem subd14_1_598 : subd14_1 [2, 2, 4] = true := by decide +kernel
theorem subd14_1_599 : subd14_1 [2, 2, 5] = true := by decide +kernel
theorem subd14_1_600 : subd14_1 [2, 2, 6] = true := by decide +kernel
theorem subd14_1_601 : subd14_1 [2, 3] = true := by decide +kernel
theorem subd14_1_602 : subd14_1 [2, 4] = true := by decide +kernel
theorem subd14_1_603 : subd14_1 [2, 5] = true := by decide +kernel
theorem subd14_1_604 : subd14_1 [2, 6] = true := by decide +kernel
theorem subd14_1_605 : subd14_1 [2, 7] = true := by decide +kernel
theorem subd14_1_606 : subd14_1 [3, -8] = true := by decide +kernel
theorem subd14_1_607 : subd14_1 [3, -7] = true := by decide +kernel
theorem sbd14_1_18 : ∀ q ∈ blkd14_1_18, subd14_1 q = true := by
  unfold blkd14_1_18
  exact List.forall_mem_cons.2 ⟨subd14_1_576, List.forall_mem_cons.2 ⟨subd14_1_577, List.forall_mem_cons.2 ⟨subd14_1_578, List.forall_mem_cons.2 ⟨subd14_1_579, List.forall_mem_cons.2 ⟨subd14_1_580, List.forall_mem_cons.2 ⟨subd14_1_581, List.forall_mem_cons.2 ⟨subd14_1_582, List.forall_mem_cons.2 ⟨subd14_1_583, List.forall_mem_cons.2 ⟨subd14_1_584, List.forall_mem_cons.2 ⟨subd14_1_585, List.forall_mem_cons.2 ⟨subd14_1_586, List.forall_mem_cons.2 ⟨subd14_1_587, List.forall_mem_cons.2 ⟨subd14_1_588, List.forall_mem_cons.2 ⟨subd14_1_589, List.forall_mem_cons.2 ⟨subd14_1_590, List.forall_mem_cons.2 ⟨subd14_1_591, List.forall_mem_cons.2 ⟨subd14_1_592, List.forall_mem_cons.2 ⟨subd14_1_593, List.forall_mem_cons.2 ⟨subd14_1_594, List.forall_mem_cons.2 ⟨subd14_1_595, List.forall_mem_cons.2 ⟨subd14_1_596, List.forall_mem_cons.2 ⟨subd14_1_597, List.forall_mem_cons.2 ⟨subd14_1_598, List.forall_mem_cons.2 ⟨subd14_1_599, List.forall_mem_cons.2 ⟨subd14_1_600, List.forall_mem_cons.2 ⟨subd14_1_601, List.forall_mem_cons.2 ⟨subd14_1_602, List.forall_mem_cons.2 ⟨subd14_1_603, List.forall_mem_cons.2 ⟨subd14_1_604, List.forall_mem_cons.2 ⟨subd14_1_605, List.forall_mem_cons.2 ⟨subd14_1_606, List.forall_mem_cons.2 ⟨subd14_1_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_1_608 : subd14_1 [3, -6] = true := by decide +kernel
theorem subd14_1_609 : subd14_1 [3, -5] = true := by decide +kernel
theorem subd14_1_610 : subd14_1 [3, -4] = true := by decide +kernel
theorem subd14_1_611 : subd14_1 [3, -3] = true := by decide +kernel
theorem subd14_1_612 : subd14_1 [3, -2] = true := by decide +kernel
theorem subd14_1_613 : subd14_1 [3, -1, -8] = true := by decide +kernel
theorem subd14_1_614 : subd14_1 [3, -1, -7] = true := by decide +kernel
theorem subd14_1_615 : subd14_1 [3, -1, -6] = true := by decide +kernel
theorem subd14_1_616 : subd14_1 [3, -1, -5] = true := by decide +kernel
theorem subd14_1_617 : subd14_1 [3, -1, -4] = true := by decide +kernel
theorem subd14_1_618 : subd14_1 [3, -1, -3] = true := by decide +kernel
theorem subd14_1_619 : subd14_1 [3, -1, -2] = true := by decide +kernel
theorem subd14_1_620 : subd14_1 [3, -1, -1] = true := by decide +kernel
theorem subd14_1_621 : subd14_1 [3, -1, 0] = true := by decide +kernel
theorem subd14_1_622 : subd14_1 [3, -1, 1] = true := by decide +kernel
theorem subd14_1_623 : subd14_1 [3, -1, 2] = true := by decide +kernel
theorem subd14_1_624 : subd14_1 [3, -1, 3] = true := by decide +kernel
theorem subd14_1_625 : subd14_1 [3, -1, 4] = true := by decide +kernel
theorem subd14_1_626 : subd14_1 [3, 0, -8] = true := by decide +kernel
theorem subd14_1_627 : subd14_1 [3, 0, -7] = true := by decide +kernel
theorem subd14_1_628 : subd14_1 [3, 0, -6] = true := by decide +kernel
theorem subd14_1_629 : subd14_1 [3, 0, -5] = true := by decide +kernel
theorem subd14_1_630 : subd14_1 [3, 0, -4] = true := by decide +kernel
theorem subd14_1_631 : subd14_1 [3, 0, -3] = true := by decide +kernel
theorem subd14_1_632 : subd14_1 [3, 0, -2] = true := by decide +kernel
theorem subd14_1_633 : subd14_1 [3, 0, -1] = true := by decide +kernel
theorem subd14_1_634 : subd14_1 [3, 0, 0] = true := by decide +kernel
theorem subd14_1_635 : subd14_1 [3, 0, 1] = true := by decide +kernel
theorem subd14_1_636 : subd14_1 [3, 0, 2] = true := by decide +kernel
theorem subd14_1_637 : subd14_1 [3, 0, 3] = true := by decide +kernel
theorem subd14_1_638 : subd14_1 [3, 0, 4] = true := by decide +kernel
theorem subd14_1_639 : subd14_1 [3, 0, 5] = true := by decide +kernel
theorem sbd14_1_19 : ∀ q ∈ blkd14_1_19, subd14_1 q = true := by
  unfold blkd14_1_19
  exact List.forall_mem_cons.2 ⟨subd14_1_608, List.forall_mem_cons.2 ⟨subd14_1_609, List.forall_mem_cons.2 ⟨subd14_1_610, List.forall_mem_cons.2 ⟨subd14_1_611, List.forall_mem_cons.2 ⟨subd14_1_612, List.forall_mem_cons.2 ⟨subd14_1_613, List.forall_mem_cons.2 ⟨subd14_1_614, List.forall_mem_cons.2 ⟨subd14_1_615, List.forall_mem_cons.2 ⟨subd14_1_616, List.forall_mem_cons.2 ⟨subd14_1_617, List.forall_mem_cons.2 ⟨subd14_1_618, List.forall_mem_cons.2 ⟨subd14_1_619, List.forall_mem_cons.2 ⟨subd14_1_620, List.forall_mem_cons.2 ⟨subd14_1_621, List.forall_mem_cons.2 ⟨subd14_1_622, List.forall_mem_cons.2 ⟨subd14_1_623, List.forall_mem_cons.2 ⟨subd14_1_624, List.forall_mem_cons.2 ⟨subd14_1_625, List.forall_mem_cons.2 ⟨subd14_1_626, List.forall_mem_cons.2 ⟨subd14_1_627, List.forall_mem_cons.2 ⟨subd14_1_628, List.forall_mem_cons.2 ⟨subd14_1_629, List.forall_mem_cons.2 ⟨subd14_1_630, List.forall_mem_cons.2 ⟨subd14_1_631, List.forall_mem_cons.2 ⟨subd14_1_632, List.forall_mem_cons.2 ⟨subd14_1_633, List.forall_mem_cons.2 ⟨subd14_1_634, List.forall_mem_cons.2 ⟨subd14_1_635, List.forall_mem_cons.2 ⟨subd14_1_636, List.forall_mem_cons.2 ⟨subd14_1_637, List.forall_mem_cons.2 ⟨subd14_1_638, List.forall_mem_cons.2 ⟨subd14_1_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_1_640 : subd14_1 [3, 1, -7] = true := by decide +kernel
theorem subd14_1_641 : subd14_1 [3, 1, -6] = true := by decide +kernel
theorem subd14_1_642 : subd14_1 [3, 1, -5] = true := by decide +kernel
theorem subd14_1_643 : subd14_1 [3, 1, -4] = true := by decide +kernel
theorem subd14_1_644 : subd14_1 [3, 1, -3] = true := by decide +kernel
theorem subd14_1_645 : subd14_1 [3, 1, -2] = true := by decide +kernel
theorem subd14_1_646 : subd14_1 [3, 1, -1] = true := by decide +kernel
theorem subd14_1_647 : subd14_1 [3, 1, 0] = true := by decide +kernel
theorem subd14_1_648 : subd14_1 [3, 1, 1] = true := by decide +kernel
theorem subd14_1_649 : subd14_1 [3, 1, 2] = true := by decide +kernel
theorem subd14_1_650 : subd14_1 [3, 1, 3] = true := by decide +kernel
theorem subd14_1_651 : subd14_1 [3, 1, 4] = true := by decide +kernel
theorem subd14_1_652 : subd14_1 [3, 1, 5] = true := by decide +kernel
theorem subd14_1_653 : subd14_1 [3, 2, -7] = true := by decide +kernel
theorem subd14_1_654 : subd14_1 [3, 2, -6] = true := by decide +kernel
theorem subd14_1_655 : subd14_1 [3, 2, -5] = true := by decide +kernel
theorem subd14_1_656 : subd14_1 [3, 2, -4] = true := by decide +kernel
theorem subd14_1_657 : subd14_1 [3, 2, -3] = true := by decide +kernel
theorem subd14_1_658 : subd14_1 [3, 2, -2] = true := by decide +kernel
theorem subd14_1_659 : subd14_1 [3, 2, -1] = true := by decide +kernel
theorem subd14_1_660 : subd14_1 [3, 2, 0] = true := by decide +kernel
theorem subd14_1_661 : subd14_1 [3, 2, 1] = true := by decide +kernel
theorem subd14_1_662 : subd14_1 [3, 2, 2] = true := by decide +kernel
theorem subd14_1_663 : subd14_1 [3, 2, 3] = true := by decide +kernel
theorem subd14_1_664 : subd14_1 [3, 2, 4] = true := by decide +kernel
theorem subd14_1_665 : subd14_1 [3, 2, 5] = true := by decide +kernel
theorem subd14_1_666 : subd14_1 [3, 2, 6] = true := by decide +kernel
theorem subd14_1_667 : subd14_1 [3, 3] = true := by decide +kernel
theorem subd14_1_668 : subd14_1 [3, 4] = true := by decide +kernel
theorem subd14_1_669 : subd14_1 [3, 5] = true := by decide +kernel
theorem subd14_1_670 : subd14_1 [3, 6] = true := by decide +kernel
theorem subd14_1_671 : subd14_1 [3, 7] = true := by decide +kernel
theorem sbd14_1_20 : ∀ q ∈ blkd14_1_20, subd14_1 q = true := by
  unfold blkd14_1_20
  exact List.forall_mem_cons.2 ⟨subd14_1_640, List.forall_mem_cons.2 ⟨subd14_1_641, List.forall_mem_cons.2 ⟨subd14_1_642, List.forall_mem_cons.2 ⟨subd14_1_643, List.forall_mem_cons.2 ⟨subd14_1_644, List.forall_mem_cons.2 ⟨subd14_1_645, List.forall_mem_cons.2 ⟨subd14_1_646, List.forall_mem_cons.2 ⟨subd14_1_647, List.forall_mem_cons.2 ⟨subd14_1_648, List.forall_mem_cons.2 ⟨subd14_1_649, List.forall_mem_cons.2 ⟨subd14_1_650, List.forall_mem_cons.2 ⟨subd14_1_651, List.forall_mem_cons.2 ⟨subd14_1_652, List.forall_mem_cons.2 ⟨subd14_1_653, List.forall_mem_cons.2 ⟨subd14_1_654, List.forall_mem_cons.2 ⟨subd14_1_655, List.forall_mem_cons.2 ⟨subd14_1_656, List.forall_mem_cons.2 ⟨subd14_1_657, List.forall_mem_cons.2 ⟨subd14_1_658, List.forall_mem_cons.2 ⟨subd14_1_659, List.forall_mem_cons.2 ⟨subd14_1_660, List.forall_mem_cons.2 ⟨subd14_1_661, List.forall_mem_cons.2 ⟨subd14_1_662, List.forall_mem_cons.2 ⟨subd14_1_663, List.forall_mem_cons.2 ⟨subd14_1_664, List.forall_mem_cons.2 ⟨subd14_1_665, List.forall_mem_cons.2 ⟨subd14_1_666, List.forall_mem_cons.2 ⟨subd14_1_667, List.forall_mem_cons.2 ⟨subd14_1_668, List.forall_mem_cons.2 ⟨subd14_1_669, List.forall_mem_cons.2 ⟨subd14_1_670, List.forall_mem_cons.2 ⟨subd14_1_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
