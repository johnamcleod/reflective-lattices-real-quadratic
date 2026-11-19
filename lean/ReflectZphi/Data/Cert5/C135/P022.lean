import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_2_320 : subd7_2 [0, 0, -4] = true := by decide +kernel
theorem subd7_2_321 : subd7_2 [0, 0, -3] = true := by decide +kernel
theorem subd7_2_322 : subd7_2 [0, 0, -2] = true := by decide +kernel
theorem subd7_2_323 : subd7_2 [0, 0, -1] = true := by decide +kernel
theorem subd7_2_324 : subd7_2 [0, 0, 0] = true := by decide +kernel
theorem subd7_2_325 : subd7_2 [0, 0, 1] = true := by decide +kernel
theorem subd7_2_326 : subd7_2 [0, 0, 2] = true := by decide +kernel
theorem subd7_2_327 : subd7_2 [0, 0, 3] = true := by decide +kernel
theorem subd7_2_328 : subd7_2 [0, 0, 4] = true := by decide +kernel
theorem subd7_2_329 : subd7_2 [0, 0, 5] = true := by decide +kernel
theorem subd7_2_330 : subd7_2 [0, 0, 6] = true := by decide +kernel
theorem subd7_2_331 : subd7_2 [0, 0, 7] = true := by decide +kernel
theorem subd7_2_332 : subd7_2 [0, 0, 8] = true := by decide +kernel
theorem subd7_2_333 : subd7_2 [0, 0, 9] = true := by decide +kernel
theorem subd7_2_334 : subd7_2 [0, 0, 10] = true := by decide +kernel
theorem subd7_2_335 : subd7_2 [0, 0, 11] = true := by decide +kernel
theorem subd7_2_336 : subd7_2 [0, 0, 12] = true := by decide +kernel
theorem subd7_2_337 : subd7_2 [0, 0, 13] = true := by decide +kernel
theorem subd7_2_338 : subd7_2 [0, 1, -13] = true := by decide +kernel
theorem subd7_2_339 : subd7_2 [0, 1, -12] = true := by decide +kernel
theorem subd7_2_340 : subd7_2 [0, 1, -11] = true := by decide +kernel
theorem subd7_2_341 : subd7_2 [0, 1, -10] = true := by decide +kernel
theorem subd7_2_342 : subd7_2 [0, 1, -9] = true := by decide +kernel
theorem subd7_2_343 : subd7_2 [0, 1, -8] = true := by decide +kernel
theorem subd7_2_344 : subd7_2 [0, 1, -7] = true := by decide +kernel
theorem subd7_2_345 : subd7_2 [0, 1, -6] = true := by decide +kernel
theorem subd7_2_346 : subd7_2 [0, 1, -5] = true := by decide +kernel
theorem subd7_2_347 : subd7_2 [0, 1, -4] = true := by decide +kernel
theorem subd7_2_348 : subd7_2 [0, 1, -3] = true := by decide +kernel
theorem subd7_2_349 : subd7_2 [0, 1, -2] = true := by decide +kernel
theorem subd7_2_350 : subd7_2 [0, 1, -1] = true := by decide +kernel
theorem subd7_2_351 : subd7_2 [0, 1, 0] = true := by decide +kernel
theorem sbd7_2_10 : ∀ q ∈ blkd7_2_10, subd7_2 q = true := by
  unfold blkd7_2_10
  exact List.forall_mem_cons.2 ⟨subd7_2_320, List.forall_mem_cons.2 ⟨subd7_2_321, List.forall_mem_cons.2 ⟨subd7_2_322, List.forall_mem_cons.2 ⟨subd7_2_323, List.forall_mem_cons.2 ⟨subd7_2_324, List.forall_mem_cons.2 ⟨subd7_2_325, List.forall_mem_cons.2 ⟨subd7_2_326, List.forall_mem_cons.2 ⟨subd7_2_327, List.forall_mem_cons.2 ⟨subd7_2_328, List.forall_mem_cons.2 ⟨subd7_2_329, List.forall_mem_cons.2 ⟨subd7_2_330, List.forall_mem_cons.2 ⟨subd7_2_331, List.forall_mem_cons.2 ⟨subd7_2_332, List.forall_mem_cons.2 ⟨subd7_2_333, List.forall_mem_cons.2 ⟨subd7_2_334, List.forall_mem_cons.2 ⟨subd7_2_335, List.forall_mem_cons.2 ⟨subd7_2_336, List.forall_mem_cons.2 ⟨subd7_2_337, List.forall_mem_cons.2 ⟨subd7_2_338, List.forall_mem_cons.2 ⟨subd7_2_339, List.forall_mem_cons.2 ⟨subd7_2_340, List.forall_mem_cons.2 ⟨subd7_2_341, List.forall_mem_cons.2 ⟨subd7_2_342, List.forall_mem_cons.2 ⟨subd7_2_343, List.forall_mem_cons.2 ⟨subd7_2_344, List.forall_mem_cons.2 ⟨subd7_2_345, List.forall_mem_cons.2 ⟨subd7_2_346, List.forall_mem_cons.2 ⟨subd7_2_347, List.forall_mem_cons.2 ⟨subd7_2_348, List.forall_mem_cons.2 ⟨subd7_2_349, List.forall_mem_cons.2 ⟨subd7_2_350, List.forall_mem_cons.2 ⟨subd7_2_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_352 : subd7_2 [0, 1, 1] = true := by decide +kernel
theorem subd7_2_353 : subd7_2 [0, 1, 2] = true := by decide +kernel
theorem subd7_2_354 : subd7_2 [0, 1, 3] = true := by decide +kernel
theorem subd7_2_355 : subd7_2 [0, 1, 4] = true := by decide +kernel
theorem subd7_2_356 : subd7_2 [0, 1, 5] = true := by decide +kernel
theorem subd7_2_357 : subd7_2 [0, 1, 6] = true := by decide +kernel
theorem subd7_2_358 : subd7_2 [0, 1, 7] = true := by decide +kernel
theorem subd7_2_359 : subd7_2 [0, 1, 8] = true := by decide +kernel
theorem subd7_2_360 : subd7_2 [0, 1, 9] = true := by decide +kernel
theorem subd7_2_361 : subd7_2 [0, 1, 10] = true := by decide +kernel
theorem subd7_2_362 : subd7_2 [0, 1, 11] = true := by decide +kernel
theorem subd7_2_363 : subd7_2 [0, 1, 12] = true := by decide +kernel
theorem subd7_2_364 : subd7_2 [0, 1, 13] = true := by decide +kernel
theorem subd7_2_365 : subd7_2 [0, 2, -11] = true := by decide +kernel
theorem subd7_2_366 : subd7_2 [0, 2, -10] = true := by decide +kernel
theorem subd7_2_367 : subd7_2 [0, 2, -9] = true := by decide +kernel
theorem subd7_2_368 : subd7_2 [0, 2, -8] = true := by decide +kernel
theorem subd7_2_369 : subd7_2 [0, 2, -7] = true := by decide +kernel
theorem subd7_2_370 : subd7_2 [0, 2, -6] = true := by decide +kernel
theorem subd7_2_371 : subd7_2 [0, 2, -5] = true := by decide +kernel
theorem subd7_2_372 : subd7_2 [0, 2, -4] = true := by decide +kernel
theorem subd7_2_373 : subd7_2 [0, 2, -3] = true := by decide +kernel
theorem subd7_2_374 : subd7_2 [0, 2, -2] = true := by decide +kernel
theorem subd7_2_375 : subd7_2 [0, 2, -1] = true := by decide +kernel
theorem subd7_2_376 : subd7_2 [0, 2, 0] = true := by decide +kernel
theorem subd7_2_377 : subd7_2 [0, 2, 1] = true := by decide +kernel
theorem subd7_2_378 : subd7_2 [0, 2, 2] = true := by decide +kernel
theorem subd7_2_379 : subd7_2 [0, 2, 3] = true := by decide +kernel
theorem subd7_2_380 : subd7_2 [0, 2, 4] = true := by decide +kernel
theorem subd7_2_381 : subd7_2 [0, 2, 5] = true := by decide +kernel
theorem subd7_2_382 : subd7_2 [0, 2, 6] = true := by decide +kernel
theorem subd7_2_383 : subd7_2 [0, 2, 7] = true := by decide +kernel
theorem sbd7_2_11 : ∀ q ∈ blkd7_2_11, subd7_2 q = true := by
  unfold blkd7_2_11
  exact List.forall_mem_cons.2 ⟨subd7_2_352, List.forall_mem_cons.2 ⟨subd7_2_353, List.forall_mem_cons.2 ⟨subd7_2_354, List.forall_mem_cons.2 ⟨subd7_2_355, List.forall_mem_cons.2 ⟨subd7_2_356, List.forall_mem_cons.2 ⟨subd7_2_357, List.forall_mem_cons.2 ⟨subd7_2_358, List.forall_mem_cons.2 ⟨subd7_2_359, List.forall_mem_cons.2 ⟨subd7_2_360, List.forall_mem_cons.2 ⟨subd7_2_361, List.forall_mem_cons.2 ⟨subd7_2_362, List.forall_mem_cons.2 ⟨subd7_2_363, List.forall_mem_cons.2 ⟨subd7_2_364, List.forall_mem_cons.2 ⟨subd7_2_365, List.forall_mem_cons.2 ⟨subd7_2_366, List.forall_mem_cons.2 ⟨subd7_2_367, List.forall_mem_cons.2 ⟨subd7_2_368, List.forall_mem_cons.2 ⟨subd7_2_369, List.forall_mem_cons.2 ⟨subd7_2_370, List.forall_mem_cons.2 ⟨subd7_2_371, List.forall_mem_cons.2 ⟨subd7_2_372, List.forall_mem_cons.2 ⟨subd7_2_373, List.forall_mem_cons.2 ⟨subd7_2_374, List.forall_mem_cons.2 ⟨subd7_2_375, List.forall_mem_cons.2 ⟨subd7_2_376, List.forall_mem_cons.2 ⟨subd7_2_377, List.forall_mem_cons.2 ⟨subd7_2_378, List.forall_mem_cons.2 ⟨subd7_2_379, List.forall_mem_cons.2 ⟨subd7_2_380, List.forall_mem_cons.2 ⟨subd7_2_381, List.forall_mem_cons.2 ⟨subd7_2_382, List.forall_mem_cons.2 ⟨subd7_2_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_384 : subd7_2 [0, 2, 8] = true := by decide +kernel
theorem subd7_2_385 : subd7_2 [0, 2, 9] = true := by decide +kernel
theorem subd7_2_386 : subd7_2 [0, 2, 10] = true := by decide +kernel
theorem subd7_2_387 : subd7_2 [0, 2, 11] = true := by decide +kernel
theorem subd7_2_388 : subd7_2 [0, 3, -8] = true := by decide +kernel
theorem subd7_2_389 : subd7_2 [0, 3, -7] = true := by decide +kernel
theorem subd7_2_390 : subd7_2 [0, 3, -6] = true := by decide +kernel
theorem subd7_2_391 : subd7_2 [0, 3, -5] = true := by decide +kernel
theorem subd7_2_392 : subd7_2 [0, 3, -4] = true := by decide +kernel
theorem subd7_2_393 : subd7_2 [0, 3, -3] = true := by decide +kernel
theorem subd7_2_394 : subd7_2 [0, 3, -2] = true := by decide +kernel
theorem subd7_2_395 : subd7_2 [0, 3, -1] = true := by decide +kernel
theorem subd7_2_396 : subd7_2 [0, 3, 0] = true := by decide +kernel
theorem subd7_2_397 : subd7_2 [0, 3, 1] = true := by decide +kernel
theorem subd7_2_398 : subd7_2 [0, 3, 2] = true := by decide +kernel
theorem subd7_2_399 : subd7_2 [0, 3, 3] = true := by decide +kernel
theorem subd7_2_400 : subd7_2 [0, 3, 4] = true := by decide +kernel
theorem subd7_2_401 : subd7_2 [0, 3, 5] = true := by decide +kernel
theorem subd7_2_402 : subd7_2 [0, 3, 6] = true := by decide +kernel
theorem subd7_2_403 : subd7_2 [0, 3, 7] = true := by decide +kernel
theorem subd7_2_404 : subd7_2 [0, 3, 8] = true := by decide +kernel
theorem subd7_2_405 : subd7_2 [1, -3] = true := by decide +kernel
theorem subd7_2_406 : subd7_2 [1, -2, -10] = true := by decide +kernel
theorem subd7_2_407 : subd7_2 [1, -2, -9] = true := by decide +kernel
theorem subd7_2_408 : subd7_2 [1, -2, -8] = true := by decide +kernel
theorem subd7_2_409 : subd7_2 [1, -2, -7] = true := by decide +kernel
theorem subd7_2_410 : subd7_2 [1, -2, -6] = true := by decide +kernel
theorem subd7_2_411 : subd7_2 [1, -2, -5] = true := by decide +kernel
theorem subd7_2_412 : subd7_2 [1, -2, -4] = true := by decide +kernel
theorem subd7_2_413 : subd7_2 [1, -2, -3] = true := by decide +kernel
theorem subd7_2_414 : subd7_2 [1, -2, -2] = true := by decide +kernel
theorem subd7_2_415 : subd7_2 [1, -2, -1] = true := by decide +kernel
theorem sbd7_2_12 : ∀ q ∈ blkd7_2_12, subd7_2 q = true := by
  unfold blkd7_2_12
  exact List.forall_mem_cons.2 ⟨subd7_2_384, List.forall_mem_cons.2 ⟨subd7_2_385, List.forall_mem_cons.2 ⟨subd7_2_386, List.forall_mem_cons.2 ⟨subd7_2_387, List.forall_mem_cons.2 ⟨subd7_2_388, List.forall_mem_cons.2 ⟨subd7_2_389, List.forall_mem_cons.2 ⟨subd7_2_390, List.forall_mem_cons.2 ⟨subd7_2_391, List.forall_mem_cons.2 ⟨subd7_2_392, List.forall_mem_cons.2 ⟨subd7_2_393, List.forall_mem_cons.2 ⟨subd7_2_394, List.forall_mem_cons.2 ⟨subd7_2_395, List.forall_mem_cons.2 ⟨subd7_2_396, List.forall_mem_cons.2 ⟨subd7_2_397, List.forall_mem_cons.2 ⟨subd7_2_398, List.forall_mem_cons.2 ⟨subd7_2_399, List.forall_mem_cons.2 ⟨subd7_2_400, List.forall_mem_cons.2 ⟨subd7_2_401, List.forall_mem_cons.2 ⟨subd7_2_402, List.forall_mem_cons.2 ⟨subd7_2_403, List.forall_mem_cons.2 ⟨subd7_2_404, List.forall_mem_cons.2 ⟨subd7_2_405, List.forall_mem_cons.2 ⟨subd7_2_406, List.forall_mem_cons.2 ⟨subd7_2_407, List.forall_mem_cons.2 ⟨subd7_2_408, List.forall_mem_cons.2 ⟨subd7_2_409, List.forall_mem_cons.2 ⟨subd7_2_410, List.forall_mem_cons.2 ⟨subd7_2_411, List.forall_mem_cons.2 ⟨subd7_2_412, List.forall_mem_cons.2 ⟨subd7_2_413, List.forall_mem_cons.2 ⟨subd7_2_414, List.forall_mem_cons.2 ⟨subd7_2_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_416 : subd7_2 [1, -2, 0] = true := by decide +kernel
theorem subd7_2_417 : subd7_2 [1, -2, 1] = true := by decide +kernel
theorem subd7_2_418 : subd7_2 [1, -2, 2] = true := by decide +kernel
theorem subd7_2_419 : subd7_2 [1, -2, 3] = true := by decide +kernel
theorem subd7_2_420 : subd7_2 [1, -2, 4] = true := by decide +kernel
theorem subd7_2_421 : subd7_2 [1, -2, 5] = true := by decide +kernel
theorem subd7_2_422 : subd7_2 [1, -2, 6] = true := by decide +kernel
theorem subd7_2_423 : subd7_2 [1, -2, 7] = true := by decide +kernel
theorem subd7_2_424 : subd7_2 [1, -2, 8] = true := by decide +kernel
theorem subd7_2_425 : subd7_2 [1, -1, -12] = true := by decide +kernel
theorem subd7_2_426 : subd7_2 [1, -1, -11] = true := by decide +kernel
theorem subd7_2_427 : subd7_2 [1, -1, -10] = true := by decide +kernel
theorem subd7_2_428 : subd7_2 [1, -1, -9] = true := by decide +kernel
theorem subd7_2_429 : subd7_2 [1, -1, -8] = true := by decide +kernel
theorem subd7_2_430 : subd7_2 [1, -1, -7] = true := by decide +kernel
theorem subd7_2_431 : subd7_2 [1, -1, -6] = true := by decide +kernel
theorem subd7_2_432 : subd7_2 [1, -1, -5] = true := by decide +kernel
theorem subd7_2_433 : subd7_2 [1, -1, -4] = true := by decide +kernel
theorem subd7_2_434 : subd7_2 [1, -1, -3] = true := by decide +kernel
theorem subd7_2_435 : subd7_2 [1, -1, -2] = true := by decide +kernel
theorem subd7_2_436 : subd7_2 [1, -1, -1] = true := by decide +kernel
theorem subd7_2_437 : subd7_2 [1, -1, 0] = true := by decide +kernel
theorem subd7_2_438 : subd7_2 [1, -1, 1] = true := by decide +kernel
theorem subd7_2_439 : subd7_2 [1, -1, 2] = true := by decide +kernel
theorem subd7_2_440 : subd7_2 [1, -1, 3] = true := by decide +kernel
theorem subd7_2_441 : subd7_2 [1, -1, 4] = true := by decide +kernel
theorem subd7_2_442 : subd7_2 [1, -1, 5] = true := by decide +kernel
theorem subd7_2_443 : subd7_2 [1, -1, 6] = true := by decide +kernel
theorem subd7_2_444 : subd7_2 [1, -1, 7] = true := by decide +kernel
theorem subd7_2_445 : subd7_2 [1, -1, 8] = true := by decide +kernel
theorem subd7_2_446 : subd7_2 [1, -1, 9] = true := by decide +kernel
theorem subd7_2_447 : subd7_2 [1, -1, 10] = true := by decide +kernel
theorem sbd7_2_13 : ∀ q ∈ blkd7_2_13, subd7_2 q = true := by
  unfold blkd7_2_13
  exact List.forall_mem_cons.2 ⟨subd7_2_416, List.forall_mem_cons.2 ⟨subd7_2_417, List.forall_mem_cons.2 ⟨subd7_2_418, List.forall_mem_cons.2 ⟨subd7_2_419, List.forall_mem_cons.2 ⟨subd7_2_420, List.forall_mem_cons.2 ⟨subd7_2_421, List.forall_mem_cons.2 ⟨subd7_2_422, List.forall_mem_cons.2 ⟨subd7_2_423, List.forall_mem_cons.2 ⟨subd7_2_424, List.forall_mem_cons.2 ⟨subd7_2_425, List.forall_mem_cons.2 ⟨subd7_2_426, List.forall_mem_cons.2 ⟨subd7_2_427, List.forall_mem_cons.2 ⟨subd7_2_428, List.forall_mem_cons.2 ⟨subd7_2_429, List.forall_mem_cons.2 ⟨subd7_2_430, List.forall_mem_cons.2 ⟨subd7_2_431, List.forall_mem_cons.2 ⟨subd7_2_432, List.forall_mem_cons.2 ⟨subd7_2_433, List.forall_mem_cons.2 ⟨subd7_2_434, List.forall_mem_cons.2 ⟨subd7_2_435, List.forall_mem_cons.2 ⟨subd7_2_436, List.forall_mem_cons.2 ⟨subd7_2_437, List.forall_mem_cons.2 ⟨subd7_2_438, List.forall_mem_cons.2 ⟨subd7_2_439, List.forall_mem_cons.2 ⟨subd7_2_440, List.forall_mem_cons.2 ⟨subd7_2_441, List.forall_mem_cons.2 ⟨subd7_2_442, List.forall_mem_cons.2 ⟨subd7_2_443, List.forall_mem_cons.2 ⟨subd7_2_444, List.forall_mem_cons.2 ⟨subd7_2_445, List.forall_mem_cons.2 ⟨subd7_2_446, List.forall_mem_cons.2 ⟨subd7_2_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_448 : subd7_2 [1, -1, 11] = true := by decide +kernel
theorem subd7_2_449 : subd7_2 [1, 0, -13] = true := by decide +kernel
theorem subd7_2_450 : subd7_2 [1, 0, -12] = true := by decide +kernel
theorem subd7_2_451 : subd7_2 [1, 0, -11] = true := by decide +kernel
theorem subd7_2_452 : subd7_2 [1, 0, -10] = true := by decide +kernel
theorem subd7_2_453 : subd7_2 [1, 0, -9] = true := by decide +kernel
theorem subd7_2_454 : subd7_2 [1, 0, -8] = true := by decide +kernel
theorem subd7_2_455 : subd7_2 [1, 0, -7] = true := by decide +kernel
theorem subd7_2_456 : subd7_2 [1, 0, -6] = true := by decide +kernel
theorem subd7_2_457 : subd7_2 [1, 0, -5] = true := by decide +kernel
theorem subd7_2_458 : subd7_2 [1, 0, -4] = true := by decide +kernel
theorem subd7_2_459 : subd7_2 [1, 0, -3] = true := by decide +kernel
theorem subd7_2_460 : subd7_2 [1, 0, -2] = true := by decide +kernel
theorem subd7_2_461 : subd7_2 [1, 0, -1] = true := by decide +kernel
theorem subd7_2_462 : subd7_2 [1, 0, 0] = true := by decide +kernel
theorem subd7_2_463 : subd7_2 [1, 0, 1] = true := by decide +kernel
theorem subd7_2_464 : subd7_2 [1, 0, 2] = true := by decide +kernel
theorem subd7_2_465 : subd7_2 [1, 0, 3] = true := by decide +kernel
theorem subd7_2_466 : subd7_2 [1, 0, 4] = true := by decide +kernel
theorem subd7_2_467 : subd7_2 [1, 0, 5] = true := by decide +kernel
theorem subd7_2_468 : subd7_2 [1, 0, 6] = true := by decide +kernel
theorem subd7_2_469 : subd7_2 [1, 0, 7] = true := by decide +kernel
theorem subd7_2_470 : subd7_2 [1, 0, 8] = true := by decide +kernel
theorem subd7_2_471 : subd7_2 [1, 0, 9] = true := by decide +kernel
theorem subd7_2_472 : subd7_2 [1, 0, 10] = true := by decide +kernel
theorem subd7_2_473 : subd7_2 [1, 0, 11] = true := by decide +kernel
theorem subd7_2_474 : subd7_2 [1, 0, 12] = true := by decide +kernel
theorem subd7_2_475 : subd7_2 [1, 0, 13] = true := by decide +kernel
theorem subd7_2_476 : subd7_2 [1, 1, -13] = true := by decide +kernel
theorem subd7_2_477 : subd7_2 [1, 1, -12] = true := by decide +kernel
theorem subd7_2_478 : subd7_2 [1, 1, -11] = true := by decide +kernel
theorem subd7_2_479 : subd7_2 [1, 1, -10] = true := by decide +kernel
theorem sbd7_2_14 : ∀ q ∈ blkd7_2_14, subd7_2 q = true := by
  unfold blkd7_2_14
  exact List.forall_mem_cons.2 ⟨subd7_2_448, List.forall_mem_cons.2 ⟨subd7_2_449, List.forall_mem_cons.2 ⟨subd7_2_450, List.forall_mem_cons.2 ⟨subd7_2_451, List.forall_mem_cons.2 ⟨subd7_2_452, List.forall_mem_cons.2 ⟨subd7_2_453, List.forall_mem_cons.2 ⟨subd7_2_454, List.forall_mem_cons.2 ⟨subd7_2_455, List.forall_mem_cons.2 ⟨subd7_2_456, List.forall_mem_cons.2 ⟨subd7_2_457, List.forall_mem_cons.2 ⟨subd7_2_458, List.forall_mem_cons.2 ⟨subd7_2_459, List.forall_mem_cons.2 ⟨subd7_2_460, List.forall_mem_cons.2 ⟨subd7_2_461, List.forall_mem_cons.2 ⟨subd7_2_462, List.forall_mem_cons.2 ⟨subd7_2_463, List.forall_mem_cons.2 ⟨subd7_2_464, List.forall_mem_cons.2 ⟨subd7_2_465, List.forall_mem_cons.2 ⟨subd7_2_466, List.forall_mem_cons.2 ⟨subd7_2_467, List.forall_mem_cons.2 ⟨subd7_2_468, List.forall_mem_cons.2 ⟨subd7_2_469, List.forall_mem_cons.2 ⟨subd7_2_470, List.forall_mem_cons.2 ⟨subd7_2_471, List.forall_mem_cons.2 ⟨subd7_2_472, List.forall_mem_cons.2 ⟨subd7_2_473, List.forall_mem_cons.2 ⟨subd7_2_474, List.forall_mem_cons.2 ⟨subd7_2_475, List.forall_mem_cons.2 ⟨subd7_2_476, List.forall_mem_cons.2 ⟨subd7_2_477, List.forall_mem_cons.2 ⟨subd7_2_478, List.forall_mem_cons.2 ⟨subd7_2_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_480 : subd7_2 [1, 1, -9] = true := by decide +kernel
theorem subd7_2_481 : subd7_2 [1, 1, -8] = true := by decide +kernel
theorem subd7_2_482 : subd7_2 [1, 1, -7] = true := by decide +kernel
theorem subd7_2_483 : subd7_2 [1, 1, -6] = true := by decide +kernel
theorem subd7_2_484 : subd7_2 [1, 1, -5] = true := by decide +kernel
theorem subd7_2_485 : subd7_2 [1, 1, -4] = true := by decide +kernel
theorem subd7_2_486 : subd7_2 [1, 1, -3] = true := by decide +kernel
theorem subd7_2_487 : subd7_2 [1, 1, -2] = true := by decide +kernel
theorem subd7_2_488 : subd7_2 [1, 1, -1] = true := by decide +kernel
theorem subd7_2_489 : subd7_2 [1, 1, 0] = true := by decide +kernel
theorem subd7_2_490 : subd7_2 [1, 1, 1] = true := by decide +kernel
theorem subd7_2_491 : subd7_2 [1, 1, 2] = true := by decide +kernel
theorem subd7_2_492 : subd7_2 [1, 1, 3] = true := by decide +kernel
theorem subd7_2_493 : subd7_2 [1, 1, 4] = true := by decide +kernel
theorem subd7_2_494 : subd7_2 [1, 1, 5] = true := by decide +kernel
theorem subd7_2_495 : subd7_2 [1, 1, 6] = true := by decide +kernel
theorem subd7_2_496 : subd7_2 [1, 1, 7] = true := by decide +kernel
theorem subd7_2_497 : subd7_2 [1, 1, 8] = true := by decide +kernel
theorem subd7_2_498 : subd7_2 [1, 1, 9] = true := by decide +kernel
theorem subd7_2_499 : subd7_2 [1, 1, 10] = true := by decide +kernel
theorem subd7_2_500 : subd7_2 [1, 1, 11] = true := by decide +kernel
theorem subd7_2_501 : subd7_2 [1, 1, 12] = true := by decide +kernel
theorem subd7_2_502 : subd7_2 [1, 1, 13] = true := by decide +kernel
theorem subd7_2_503 : subd7_2 [1, 2, -11] = true := by decide +kernel
theorem subd7_2_504 : subd7_2 [1, 2, -10] = true := by decide +kernel
theorem subd7_2_505 : subd7_2 [1, 2, -9] = true := by decide +kernel
theorem subd7_2_506 : subd7_2 [1, 2, -8] = true := by decide +kernel
theorem subd7_2_507 : subd7_2 [1, 2, -7] = true := by decide +kernel
theorem subd7_2_508 : subd7_2 [1, 2, -6] = true := by decide +kernel
theorem subd7_2_509 : subd7_2 [1, 2, -5] = true := by decide +kernel
theorem subd7_2_510 : subd7_2 [1, 2, -4] = true := by decide +kernel
theorem subd7_2_511 : subd7_2 [1, 2, -3] = true := by decide +kernel
theorem sbd7_2_15 : ∀ q ∈ blkd7_2_15, subd7_2 q = true := by
  unfold blkd7_2_15
  exact List.forall_mem_cons.2 ⟨subd7_2_480, List.forall_mem_cons.2 ⟨subd7_2_481, List.forall_mem_cons.2 ⟨subd7_2_482, List.forall_mem_cons.2 ⟨subd7_2_483, List.forall_mem_cons.2 ⟨subd7_2_484, List.forall_mem_cons.2 ⟨subd7_2_485, List.forall_mem_cons.2 ⟨subd7_2_486, List.forall_mem_cons.2 ⟨subd7_2_487, List.forall_mem_cons.2 ⟨subd7_2_488, List.forall_mem_cons.2 ⟨subd7_2_489, List.forall_mem_cons.2 ⟨subd7_2_490, List.forall_mem_cons.2 ⟨subd7_2_491, List.forall_mem_cons.2 ⟨subd7_2_492, List.forall_mem_cons.2 ⟨subd7_2_493, List.forall_mem_cons.2 ⟨subd7_2_494, List.forall_mem_cons.2 ⟨subd7_2_495, List.forall_mem_cons.2 ⟨subd7_2_496, List.forall_mem_cons.2 ⟨subd7_2_497, List.forall_mem_cons.2 ⟨subd7_2_498, List.forall_mem_cons.2 ⟨subd7_2_499, List.forall_mem_cons.2 ⟨subd7_2_500, List.forall_mem_cons.2 ⟨subd7_2_501, List.forall_mem_cons.2 ⟨subd7_2_502, List.forall_mem_cons.2 ⟨subd7_2_503, List.forall_mem_cons.2 ⟨subd7_2_504, List.forall_mem_cons.2 ⟨subd7_2_505, List.forall_mem_cons.2 ⟨subd7_2_506, List.forall_mem_cons.2 ⟨subd7_2_507, List.forall_mem_cons.2 ⟨subd7_2_508, List.forall_mem_cons.2 ⟨subd7_2_509, List.forall_mem_cons.2 ⟨subd7_2_510, List.forall_mem_cons.2 ⟨subd7_2_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_512 : subd7_2 [1, 2, -2] = true := by decide +kernel
theorem subd7_2_513 : subd7_2 [1, 2, -1] = true := by decide +kernel
theorem subd7_2_514 : subd7_2 [1, 2, 0] = true := by decide +kernel
theorem subd7_2_515 : subd7_2 [1, 2, 1] = true := by decide +kernel
theorem subd7_2_516 : subd7_2 [1, 2, 2] = true := by decide +kernel
theorem subd7_2_517 : subd7_2 [1, 2, 3] = true := by decide +kernel
theorem subd7_2_518 : subd7_2 [1, 2, 4] = true := by decide +kernel
theorem subd7_2_519 : subd7_2 [1, 2, 5] = true := by decide +kernel
theorem subd7_2_520 : subd7_2 [1, 2, 6] = true := by decide +kernel
theorem subd7_2_521 : subd7_2 [1, 2, 7] = true := by decide +kernel
theorem subd7_2_522 : subd7_2 [1, 2, 8] = true := by decide +kernel
theorem subd7_2_523 : subd7_2 [1, 2, 9] = true := by decide +kernel
theorem subd7_2_524 : subd7_2 [1, 2, 10] = true := by decide +kernel
theorem subd7_2_525 : subd7_2 [1, 2, 11] = true := by decide +kernel
theorem subd7_2_526 : subd7_2 [1, 2, 12] = true := by decide +kernel
theorem subd7_2_527 : subd7_2 [1, 3, -8] = true := by decide +kernel
theorem subd7_2_528 : subd7_2 [1, 3, -7] = true := by decide +kernel
theorem subd7_2_529 : subd7_2 [1, 3, -6] = true := by decide +kernel
theorem subd7_2_530 : subd7_2 [1, 3, -5] = true := by decide +kernel
theorem subd7_2_531 : subd7_2 [1, 3, -4] = true := by decide +kernel
theorem subd7_2_532 : subd7_2 [1, 3, -3] = true := by decide +kernel
theorem subd7_2_533 : subd7_2 [1, 3, -2] = true := by decide +kernel
theorem subd7_2_534 : subd7_2 [1, 3, -1] = true := by decide +kernel
theorem subd7_2_535 : subd7_2 [1, 3, 0] = true := by decide +kernel
theorem subd7_2_536 : subd7_2 [1, 3, 1] = true := by decide +kernel
theorem subd7_2_537 : subd7_2 [1, 3, 2] = true := by decide +kernel
theorem subd7_2_538 : subd7_2 [1, 3, 3] = true := by decide +kernel
theorem subd7_2_539 : subd7_2 [1, 3, 4] = true := by decide +kernel
theorem subd7_2_540 : subd7_2 [1, 3, 5] = true := by decide +kernel
theorem subd7_2_541 : subd7_2 [1, 3, 6] = true := by decide +kernel
theorem subd7_2_542 : subd7_2 [1, 3, 7] = true := by decide +kernel
theorem subd7_2_543 : subd7_2 [1, 3, 8] = true := by decide +kernel
theorem sbd7_2_16 : ∀ q ∈ blkd7_2_16, subd7_2 q = true := by
  unfold blkd7_2_16
  exact List.forall_mem_cons.2 ⟨subd7_2_512, List.forall_mem_cons.2 ⟨subd7_2_513, List.forall_mem_cons.2 ⟨subd7_2_514, List.forall_mem_cons.2 ⟨subd7_2_515, List.forall_mem_cons.2 ⟨subd7_2_516, List.forall_mem_cons.2 ⟨subd7_2_517, List.forall_mem_cons.2 ⟨subd7_2_518, List.forall_mem_cons.2 ⟨subd7_2_519, List.forall_mem_cons.2 ⟨subd7_2_520, List.forall_mem_cons.2 ⟨subd7_2_521, List.forall_mem_cons.2 ⟨subd7_2_522, List.forall_mem_cons.2 ⟨subd7_2_523, List.forall_mem_cons.2 ⟨subd7_2_524, List.forall_mem_cons.2 ⟨subd7_2_525, List.forall_mem_cons.2 ⟨subd7_2_526, List.forall_mem_cons.2 ⟨subd7_2_527, List.forall_mem_cons.2 ⟨subd7_2_528, List.forall_mem_cons.2 ⟨subd7_2_529, List.forall_mem_cons.2 ⟨subd7_2_530, List.forall_mem_cons.2 ⟨subd7_2_531, List.forall_mem_cons.2 ⟨subd7_2_532, List.forall_mem_cons.2 ⟨subd7_2_533, List.forall_mem_cons.2 ⟨subd7_2_534, List.forall_mem_cons.2 ⟨subd7_2_535, List.forall_mem_cons.2 ⟨subd7_2_536, List.forall_mem_cons.2 ⟨subd7_2_537, List.forall_mem_cons.2 ⟨subd7_2_538, List.forall_mem_cons.2 ⟨subd7_2_539, List.forall_mem_cons.2 ⟨subd7_2_540, List.forall_mem_cons.2 ⟨subd7_2_541, List.forall_mem_cons.2 ⟨subd7_2_542, List.forall_mem_cons.2 ⟨subd7_2_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_544 : subd7_2 [1, 3, 9] = true := by decide +kernel
theorem subd7_2_545 : subd7_2 [2, -2] = true := by decide +kernel
theorem subd7_2_546 : subd7_2 [2, -1, -8] = true := by decide +kernel
theorem subd7_2_547 : subd7_2 [2, -1, -7] = true := by decide +kernel
theorem subd7_2_548 : subd7_2 [2, -1, -6] = true := by decide +kernel
theorem subd7_2_549 : subd7_2 [2, -1, -5] = true := by decide +kernel
theorem subd7_2_550 : subd7_2 [2, -1, -4] = true := by decide +kernel
theorem subd7_2_551 : subd7_2 [2, -1, -3] = true := by decide +kernel
theorem subd7_2_552 : subd7_2 [2, -1, -2] = true := by decide +kernel
theorem subd7_2_553 : subd7_2 [2, -1, -1] = true := by decide +kernel
theorem subd7_2_554 : subd7_2 [2, -1, 0] = true := by decide +kernel
theorem subd7_2_555 : subd7_2 [2, -1, 1] = true := by decide +kernel
theorem subd7_2_556 : subd7_2 [2, -1, 2] = true := by decide +kernel
theorem subd7_2_557 : subd7_2 [2, -1, 3] = true := by decide +kernel
theorem subd7_2_558 : subd7_2 [2, -1, 4] = true := by decide +kernel
theorem subd7_2_559 : subd7_2 [2, -1, 5] = true := by decide +kernel
theorem subd7_2_560 : subd7_2 [2, -1, 6] = true := by decide +kernel
theorem subd7_2_561 : subd7_2 [2, -1, 7] = true := by decide +kernel
theorem subd7_2_562 : subd7_2 [2, -1, 8] = true := by decide +kernel
theorem subd7_2_563 : subd7_2 [2, 0, -10] = true := by decide +kernel
theorem subd7_2_564 : subd7_2 [2, 0, -9] = true := by decide +kernel
theorem subd7_2_565 : subd7_2 [2, 0, -8] = true := by decide +kernel
theorem subd7_2_566 : subd7_2 [2, 0, -7] = true := by decide +kernel
theorem subd7_2_567 : subd7_2 [2, 0, -6] = true := by decide +kernel
theorem subd7_2_568 : subd7_2 [2, 0, -5] = true := by decide +kernel
theorem subd7_2_569 : subd7_2 [2, 0, -4] = true := by decide +kernel
theorem subd7_2_570 : subd7_2 [2, 0, -3] = true := by decide +kernel
theorem subd7_2_571 : subd7_2 [2, 0, -2] = true := by decide +kernel
theorem subd7_2_572 : subd7_2 [2, 0, -1] = true := by decide +kernel
theorem subd7_2_573 : subd7_2 [2, 0, 0] = true := by decide +kernel
theorem subd7_2_574 : subd7_2 [2, 0, 1] = true := by decide +kernel
theorem subd7_2_575 : subd7_2 [2, 0, 2] = true := by decide +kernel
theorem sbd7_2_17 : ∀ q ∈ blkd7_2_17, subd7_2 q = true := by
  unfold blkd7_2_17
  exact List.forall_mem_cons.2 ⟨subd7_2_544, List.forall_mem_cons.2 ⟨subd7_2_545, List.forall_mem_cons.2 ⟨subd7_2_546, List.forall_mem_cons.2 ⟨subd7_2_547, List.forall_mem_cons.2 ⟨subd7_2_548, List.forall_mem_cons.2 ⟨subd7_2_549, List.forall_mem_cons.2 ⟨subd7_2_550, List.forall_mem_cons.2 ⟨subd7_2_551, List.forall_mem_cons.2 ⟨subd7_2_552, List.forall_mem_cons.2 ⟨subd7_2_553, List.forall_mem_cons.2 ⟨subd7_2_554, List.forall_mem_cons.2 ⟨subd7_2_555, List.forall_mem_cons.2 ⟨subd7_2_556, List.forall_mem_cons.2 ⟨subd7_2_557, List.forall_mem_cons.2 ⟨subd7_2_558, List.forall_mem_cons.2 ⟨subd7_2_559, List.forall_mem_cons.2 ⟨subd7_2_560, List.forall_mem_cons.2 ⟨subd7_2_561, List.forall_mem_cons.2 ⟨subd7_2_562, List.forall_mem_cons.2 ⟨subd7_2_563, List.forall_mem_cons.2 ⟨subd7_2_564, List.forall_mem_cons.2 ⟨subd7_2_565, List.forall_mem_cons.2 ⟨subd7_2_566, List.forall_mem_cons.2 ⟨subd7_2_567, List.forall_mem_cons.2 ⟨subd7_2_568, List.forall_mem_cons.2 ⟨subd7_2_569, List.forall_mem_cons.2 ⟨subd7_2_570, List.forall_mem_cons.2 ⟨subd7_2_571, List.forall_mem_cons.2 ⟨subd7_2_572, List.forall_mem_cons.2 ⟨subd7_2_573, List.forall_mem_cons.2 ⟨subd7_2_574, List.forall_mem_cons.2 ⟨subd7_2_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_576 : subd7_2 [2, 0, 3] = true := by decide +kernel
theorem subd7_2_577 : subd7_2 [2, 0, 4] = true := by decide +kernel
theorem subd7_2_578 : subd7_2 [2, 0, 5] = true := by decide +kernel
theorem subd7_2_579 : subd7_2 [2, 0, 6] = true := by decide +kernel
theorem subd7_2_580 : subd7_2 [2, 0, 7] = true := by decide +kernel
theorem subd7_2_581 : subd7_2 [2, 0, 8] = true := by decide +kernel
theorem subd7_2_582 : subd7_2 [2, 0, 9] = true := by decide +kernel
theorem subd7_2_583 : subd7_2 [2, 0, 10] = true := by decide +kernel
theorem subd7_2_584 : subd7_2 [2, 1, -10] = true := by decide +kernel
theorem subd7_2_585 : subd7_2 [2, 1, -9] = true := by decide +kernel
theorem subd7_2_586 : subd7_2 [2, 1, -8] = true := by decide +kernel
theorem subd7_2_587 : subd7_2 [2, 1, -7] = true := by decide +kernel
theorem subd7_2_588 : subd7_2 [2, 1, -6] = true := by decide +kernel
theorem subd7_2_589 : subd7_2 [2, 1, -5] = true := by decide +kernel
theorem subd7_2_590 : subd7_2 [2, 1, -4] = true := by decide +kernel
theorem subd7_2_591 : subd7_2 [2, 1, -3] = true := by decide +kernel
theorem subd7_2_592 : subd7_2 [2, 1, -2] = true := by decide +kernel
theorem subd7_2_593 : subd7_2 [2, 1, -1] = true := by decide +kernel
theorem subd7_2_594 : subd7_2 [2, 1, 0] = true := by decide +kernel
theorem subd7_2_595 : subd7_2 [2, 1, 1] = true := by decide +kernel
theorem subd7_2_596 : subd7_2 [2, 1, 2] = true := by decide +kernel
theorem subd7_2_597 : subd7_2 [2, 1, 3] = true := by decide +kernel
theorem subd7_2_598 : subd7_2 [2, 1, 4] = true := by decide +kernel
theorem subd7_2_599 : subd7_2 [2, 1, 5] = true := by decide +kernel
theorem subd7_2_600 : subd7_2 [2, 1, 6] = true := by decide +kernel
theorem subd7_2_601 : subd7_2 [2, 1, 7] = true := by decide +kernel
theorem subd7_2_602 : subd7_2 [2, 1, 8] = true := by decide +kernel
theorem subd7_2_603 : subd7_2 [2, 1, 9] = true := by decide +kernel
theorem subd7_2_604 : subd7_2 [2, 1, 10] = true := by decide +kernel
theorem subd7_2_605 : subd7_2 [2, 1, 11] = true := by decide +kernel
theorem subd7_2_606 : subd7_2 [2, 2, -9] = true := by decide +kernel
theorem subd7_2_607 : subd7_2 [2, 2, -8] = true := by decide +kernel
theorem sbd7_2_18 : ∀ q ∈ blkd7_2_18, subd7_2 q = true := by
  unfold blkd7_2_18
  exact List.forall_mem_cons.2 ⟨subd7_2_576, List.forall_mem_cons.2 ⟨subd7_2_577, List.forall_mem_cons.2 ⟨subd7_2_578, List.forall_mem_cons.2 ⟨subd7_2_579, List.forall_mem_cons.2 ⟨subd7_2_580, List.forall_mem_cons.2 ⟨subd7_2_581, List.forall_mem_cons.2 ⟨subd7_2_582, List.forall_mem_cons.2 ⟨subd7_2_583, List.forall_mem_cons.2 ⟨subd7_2_584, List.forall_mem_cons.2 ⟨subd7_2_585, List.forall_mem_cons.2 ⟨subd7_2_586, List.forall_mem_cons.2 ⟨subd7_2_587, List.forall_mem_cons.2 ⟨subd7_2_588, List.forall_mem_cons.2 ⟨subd7_2_589, List.forall_mem_cons.2 ⟨subd7_2_590, List.forall_mem_cons.2 ⟨subd7_2_591, List.forall_mem_cons.2 ⟨subd7_2_592, List.forall_mem_cons.2 ⟨subd7_2_593, List.forall_mem_cons.2 ⟨subd7_2_594, List.forall_mem_cons.2 ⟨subd7_2_595, List.forall_mem_cons.2 ⟨subd7_2_596, List.forall_mem_cons.2 ⟨subd7_2_597, List.forall_mem_cons.2 ⟨subd7_2_598, List.forall_mem_cons.2 ⟨subd7_2_599, List.forall_mem_cons.2 ⟨subd7_2_600, List.forall_mem_cons.2 ⟨subd7_2_601, List.forall_mem_cons.2 ⟨subd7_2_602, List.forall_mem_cons.2 ⟨subd7_2_603, List.forall_mem_cons.2 ⟨subd7_2_604, List.forall_mem_cons.2 ⟨subd7_2_605, List.forall_mem_cons.2 ⟨subd7_2_606, List.forall_mem_cons.2 ⟨subd7_2_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_608 : subd7_2 [2, 2, -7] = true := by decide +kernel
theorem subd7_2_609 : subd7_2 [2, 2, -6] = true := by decide +kernel
theorem subd7_2_610 : subd7_2 [2, 2, -5] = true := by decide +kernel
theorem subd7_2_611 : subd7_2 [2, 2, -4] = true := by decide +kernel
theorem subd7_2_612 : subd7_2 [2, 2, -3] = true := by decide +kernel
theorem subd7_2_613 : subd7_2 [2, 2, -2] = true := by decide +kernel
theorem subd7_2_614 : subd7_2 [2, 2, -1] = true := by decide +kernel
theorem subd7_2_615 : subd7_2 [2, 2, 0] = true := by decide +kernel
theorem subd7_2_616 : subd7_2 [2, 2, 1] = true := by decide +kernel
theorem subd7_2_617 : subd7_2 [2, 2, 2] = true := by decide +kernel
theorem subd7_2_618 : subd7_2 [2, 2, 3] = true := by decide +kernel
theorem subd7_2_619 : subd7_2 [2, 2, 4] = true := by decide +kernel
theorem subd7_2_620 : subd7_2 [2, 2, 5] = true := by decide +kernel
theorem subd7_2_621 : subd7_2 [2, 2, 6] = true := by decide +kernel
theorem subd7_2_622 : subd7_2 [2, 2, 7] = true := by decide +kernel
theorem subd7_2_623 : subd7_2 [2, 2, 8] = true := by decide +kernel
theorem subd7_2_624 : subd7_2 [2, 2, 9] = true := by decide +kernel
theorem subd7_2_625 : subd7_2 [2, 2, 10] = true := by decide +kernel
theorem subd7_2_626 : subd7_2 [2, 2, 11] = true := by decide +kernel
theorem subd7_2_627 : subd7_2 [2, 3, -7] = true := by decide +kernel
theorem subd7_2_628 : subd7_2 [2, 3, -6] = true := by decide +kernel
theorem subd7_2_629 : subd7_2 [2, 3, -5] = true := by decide +kernel
theorem subd7_2_630 : subd7_2 [2, 3, -4] = true := by decide +kernel
theorem subd7_2_631 : subd7_2 [2, 3, -3] = true := by decide +kernel
theorem subd7_2_632 : subd7_2 [2, 3, -2] = true := by decide +kernel
theorem subd7_2_633 : subd7_2 [2, 3, -1] = true := by decide +kernel
theorem subd7_2_634 : subd7_2 [2, 3, 0] = true := by decide +kernel
theorem subd7_2_635 : subd7_2 [2, 3, 1] = true := by decide +kernel
theorem subd7_2_636 : subd7_2 [2, 3, 2] = true := by decide +kernel
theorem subd7_2_637 : subd7_2 [2, 3, 3] = true := by decide +kernel
theorem subd7_2_638 : subd7_2 [2, 3, 4] = true := by decide +kernel
theorem subd7_2_639 : subd7_2 [2, 3, 5] = true := by decide +kernel
theorem sbd7_2_19 : ∀ q ∈ blkd7_2_19, subd7_2 q = true := by
  unfold blkd7_2_19
  exact List.forall_mem_cons.2 ⟨subd7_2_608, List.forall_mem_cons.2 ⟨subd7_2_609, List.forall_mem_cons.2 ⟨subd7_2_610, List.forall_mem_cons.2 ⟨subd7_2_611, List.forall_mem_cons.2 ⟨subd7_2_612, List.forall_mem_cons.2 ⟨subd7_2_613, List.forall_mem_cons.2 ⟨subd7_2_614, List.forall_mem_cons.2 ⟨subd7_2_615, List.forall_mem_cons.2 ⟨subd7_2_616, List.forall_mem_cons.2 ⟨subd7_2_617, List.forall_mem_cons.2 ⟨subd7_2_618, List.forall_mem_cons.2 ⟨subd7_2_619, List.forall_mem_cons.2 ⟨subd7_2_620, List.forall_mem_cons.2 ⟨subd7_2_621, List.forall_mem_cons.2 ⟨subd7_2_622, List.forall_mem_cons.2 ⟨subd7_2_623, List.forall_mem_cons.2 ⟨subd7_2_624, List.forall_mem_cons.2 ⟨subd7_2_625, List.forall_mem_cons.2 ⟨subd7_2_626, List.forall_mem_cons.2 ⟨subd7_2_627, List.forall_mem_cons.2 ⟨subd7_2_628, List.forall_mem_cons.2 ⟨subd7_2_629, List.forall_mem_cons.2 ⟨subd7_2_630, List.forall_mem_cons.2 ⟨subd7_2_631, List.forall_mem_cons.2 ⟨subd7_2_632, List.forall_mem_cons.2 ⟨subd7_2_633, List.forall_mem_cons.2 ⟨subd7_2_634, List.forall_mem_cons.2 ⟨subd7_2_635, List.forall_mem_cons.2 ⟨subd7_2_636, List.forall_mem_cons.2 ⟨subd7_2_637, List.forall_mem_cons.2 ⟨subd7_2_638, List.forall_mem_cons.2 ⟨subd7_2_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_640 : subd7_2 [2, 3, 6] = true := by decide +kernel
theorem subd7_2_641 : subd7_2 [2, 3, 7] = true := by decide +kernel
theorem subd7_2_642 : subd7_2 [2, 3, 8] = true := by decide +kernel
theorem subd7_2_643 : subd7_2 [2, 3, 9] = true := by decide +kernel
theorem subd7_2_644 : subd7_2 [3, 0] = true := by decide +kernel
theorem subd7_2_645 : subd7_2 [3, 1] = true := by decide +kernel
theorem subd7_2_646 : subd7_2 [3, 2] = true := by decide +kernel
theorem sbd7_2_20 : ∀ q ∈ blkd7_2_20, subd7_2 q = true := by
  unfold blkd7_2_20
  exact List.forall_mem_cons.2 ⟨subd7_2_640, List.forall_mem_cons.2 ⟨subd7_2_641, List.forall_mem_cons.2 ⟨subd7_2_642, List.forall_mem_cons.2 ⟨subd7_2_643, List.forall_mem_cons.2 ⟨subd7_2_644, List.forall_mem_cons.2 ⟨subd7_2_645, List.forall_mem_cons.2 ⟨subd7_2_646, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_3 : ldCheck G d7_3.U d7_3.ms ldd7_3 = true := by decide +kernel
theorem pre_okd7_3 : subPre G cell7 d7_3 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C135
