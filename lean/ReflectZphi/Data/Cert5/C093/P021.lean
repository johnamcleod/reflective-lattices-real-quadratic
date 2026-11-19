import ReflectZphi.Data.Cert5.C093.Base

namespace ReflectZphi.Data.Cert5.C093

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd10_0_352 : subd10_0 [0, 2, -2] = true := by decide +kernel
theorem subd10_0_353 : subd10_0 [0, 2, -1] = true := by decide +kernel
theorem subd10_0_354 : subd10_0 [0, 2, 0] = true := by decide +kernel
theorem subd10_0_355 : subd10_0 [0, 2, 1] = true := by decide +kernel
theorem subd10_0_356 : subd10_0 [0, 2, 2] = true := by decide +kernel
theorem subd10_0_357 : subd10_0 [0, 2, 3] = true := by decide +kernel
theorem subd10_0_358 : subd10_0 [0, 2, 4] = true := by decide +kernel
theorem subd10_0_359 : subd10_0 [0, 2, 5] = true := by decide +kernel
theorem subd10_0_360 : subd10_0 [0, 2, 6] = true := by decide +kernel
theorem subd10_0_361 : subd10_0 [0, 2, 7] = true := by decide +kernel
theorem subd10_0_362 : subd10_0 [0, 2, 8] = true := by decide +kernel
theorem subd10_0_363 : subd10_0 [0, 3, -9] = true := by decide +kernel
theorem subd10_0_364 : subd10_0 [0, 3, -8] = true := by decide +kernel
theorem subd10_0_365 : subd10_0 [0, 3, -7] = true := by decide +kernel
theorem subd10_0_366 : subd10_0 [0, 3, -6] = true := by decide +kernel
theorem subd10_0_367 : subd10_0 [0, 3, -5] = true := by decide +kernel
theorem subd10_0_368 : subd10_0 [0, 3, -4] = true := by decide +kernel
theorem subd10_0_369 : subd10_0 [0, 3, -3] = true := by decide +kernel
theorem subd10_0_370 : subd10_0 [0, 3, -2] = true := by decide +kernel
theorem subd10_0_371 : subd10_0 [0, 3, -1] = true := by decide +kernel
theorem subd10_0_372 : subd10_0 [0, 3, 0] = true := by decide +kernel
theorem subd10_0_373 : subd10_0 [0, 3, 1] = true := by decide +kernel
theorem subd10_0_374 : subd10_0 [0, 3, 2] = true := by decide +kernel
theorem subd10_0_375 : subd10_0 [0, 3, 3] = true := by decide +kernel
theorem subd10_0_376 : subd10_0 [0, 3, 4] = true := by decide +kernel
theorem subd10_0_377 : subd10_0 [0, 3, 5] = true := by decide +kernel
theorem subd10_0_378 : subd10_0 [0, 3, 6] = true := by decide +kernel
theorem subd10_0_379 : subd10_0 [0, 4] = true := by decide +kernel
theorem subd10_0_380 : subd10_0 [1, -5] = true := by decide +kernel
theorem subd10_0_381 : subd10_0 [1, -4] = true := by decide +kernel
theorem subd10_0_382 : subd10_0 [1, -3, -8] = true := by decide +kernel
theorem subd10_0_383 : subd10_0 [1, -3, -7] = true := by decide +kernel
theorem sbd10_0_11 : ∀ q ∈ blkd10_0_11, subd10_0 q = true := by
  unfold blkd10_0_11
  exact List.forall_mem_cons.2 ⟨subd10_0_352, List.forall_mem_cons.2 ⟨subd10_0_353, List.forall_mem_cons.2 ⟨subd10_0_354, List.forall_mem_cons.2 ⟨subd10_0_355, List.forall_mem_cons.2 ⟨subd10_0_356, List.forall_mem_cons.2 ⟨subd10_0_357, List.forall_mem_cons.2 ⟨subd10_0_358, List.forall_mem_cons.2 ⟨subd10_0_359, List.forall_mem_cons.2 ⟨subd10_0_360, List.forall_mem_cons.2 ⟨subd10_0_361, List.forall_mem_cons.2 ⟨subd10_0_362, List.forall_mem_cons.2 ⟨subd10_0_363, List.forall_mem_cons.2 ⟨subd10_0_364, List.forall_mem_cons.2 ⟨subd10_0_365, List.forall_mem_cons.2 ⟨subd10_0_366, List.forall_mem_cons.2 ⟨subd10_0_367, List.forall_mem_cons.2 ⟨subd10_0_368, List.forall_mem_cons.2 ⟨subd10_0_369, List.forall_mem_cons.2 ⟨subd10_0_370, List.forall_mem_cons.2 ⟨subd10_0_371, List.forall_mem_cons.2 ⟨subd10_0_372, List.forall_mem_cons.2 ⟨subd10_0_373, List.forall_mem_cons.2 ⟨subd10_0_374, List.forall_mem_cons.2 ⟨subd10_0_375, List.forall_mem_cons.2 ⟨subd10_0_376, List.forall_mem_cons.2 ⟨subd10_0_377, List.forall_mem_cons.2 ⟨subd10_0_378, List.forall_mem_cons.2 ⟨subd10_0_379, List.forall_mem_cons.2 ⟨subd10_0_380, List.forall_mem_cons.2 ⟨subd10_0_381, List.forall_mem_cons.2 ⟨subd10_0_382, List.forall_mem_cons.2 ⟨subd10_0_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_384 : subd10_0 [1, -3, -6] = true := by decide +kernel
theorem subd10_0_385 : subd10_0 [1, -3, -5] = true := by decide +kernel
theorem subd10_0_386 : subd10_0 [1, -3, -4] = true := by decide +kernel
theorem subd10_0_387 : subd10_0 [1, -3, -3] = true := by decide +kernel
theorem subd10_0_388 : subd10_0 [1, -3, -2] = true := by decide +kernel
theorem subd10_0_389 : subd10_0 [1, -3, -1] = true := by decide +kernel
theorem subd10_0_390 : subd10_0 [1, -3, 0] = true := by decide +kernel
theorem subd10_0_391 : subd10_0 [1, -3, 1] = true := by decide +kernel
theorem subd10_0_392 : subd10_0 [1, -3, 2] = true := by decide +kernel
theorem subd10_0_393 : subd10_0 [1, -3, 3] = true := by decide +kernel
theorem subd10_0_394 : subd10_0 [1, -3, 4] = true := by decide +kernel
theorem subd10_0_395 : subd10_0 [1, -3, 5] = true := by decide +kernel
theorem subd10_0_396 : subd10_0 [1, -3, 6] = true := by decide +kernel
theorem subd10_0_397 : subd10_0 [1, -3, 7] = true := by decide +kernel
theorem subd10_0_398 : subd10_0 [1, -3, 8] = true := by decide +kernel
theorem subd10_0_399 : subd10_0 [1, -2, -9] = true := by decide +kernel
theorem subd10_0_400 : subd10_0 [1, -2, -8] = true := by decide +kernel
theorem subd10_0_401 : subd10_0 [1, -2, -7] = true := by decide +kernel
theorem subd10_0_402 : subd10_0 [1, -2, -6] = true := by decide +kernel
theorem subd10_0_403 : subd10_0 [1, -2, -5] = true := by decide +kernel
theorem subd10_0_404 : subd10_0 [1, -2, -4] = true := by decide +kernel
theorem subd10_0_405 : subd10_0 [1, -2, -3] = true := by decide +kernel
theorem subd10_0_406 : subd10_0 [1, -2, -2] = true := by decide +kernel
theorem subd10_0_407 : subd10_0 [1, -2, -1] = true := by decide +kernel
theorem subd10_0_408 : subd10_0 [1, -2, 0] = true := by decide +kernel
theorem subd10_0_409 : subd10_0 [1, -2, 1] = true := by decide +kernel
theorem subd10_0_410 : subd10_0 [1, -2, 2] = true := by decide +kernel
theorem subd10_0_411 : subd10_0 [1, -2, 3] = true := by decide +kernel
theorem subd10_0_412 : subd10_0 [1, -2, 4] = true := by decide +kernel
theorem subd10_0_413 : subd10_0 [1, -2, 5] = true := by decide +kernel
theorem subd10_0_414 : subd10_0 [1, -2, 6] = true := by decide +kernel
theorem subd10_0_415 : subd10_0 [1, -2, 7] = true := by decide +kernel
theorem sbd10_0_12 : ∀ q ∈ blkd10_0_12, subd10_0 q = true := by
  unfold blkd10_0_12
  exact List.forall_mem_cons.2 ⟨subd10_0_384, List.forall_mem_cons.2 ⟨subd10_0_385, List.forall_mem_cons.2 ⟨subd10_0_386, List.forall_mem_cons.2 ⟨subd10_0_387, List.forall_mem_cons.2 ⟨subd10_0_388, List.forall_mem_cons.2 ⟨subd10_0_389, List.forall_mem_cons.2 ⟨subd10_0_390, List.forall_mem_cons.2 ⟨subd10_0_391, List.forall_mem_cons.2 ⟨subd10_0_392, List.forall_mem_cons.2 ⟨subd10_0_393, List.forall_mem_cons.2 ⟨subd10_0_394, List.forall_mem_cons.2 ⟨subd10_0_395, List.forall_mem_cons.2 ⟨subd10_0_396, List.forall_mem_cons.2 ⟨subd10_0_397, List.forall_mem_cons.2 ⟨subd10_0_398, List.forall_mem_cons.2 ⟨subd10_0_399, List.forall_mem_cons.2 ⟨subd10_0_400, List.forall_mem_cons.2 ⟨subd10_0_401, List.forall_mem_cons.2 ⟨subd10_0_402, List.forall_mem_cons.2 ⟨subd10_0_403, List.forall_mem_cons.2 ⟨subd10_0_404, List.forall_mem_cons.2 ⟨subd10_0_405, List.forall_mem_cons.2 ⟨subd10_0_406, List.forall_mem_cons.2 ⟨subd10_0_407, List.forall_mem_cons.2 ⟨subd10_0_408, List.forall_mem_cons.2 ⟨subd10_0_409, List.forall_mem_cons.2 ⟨subd10_0_410, List.forall_mem_cons.2 ⟨subd10_0_411, List.forall_mem_cons.2 ⟨subd10_0_412, List.forall_mem_cons.2 ⟨subd10_0_413, List.forall_mem_cons.2 ⟨subd10_0_414, List.forall_mem_cons.2 ⟨subd10_0_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_416 : subd10_0 [1, -2, 8] = true := by decide +kernel
theorem subd10_0_417 : subd10_0 [1, -2, 9] = true := by decide +kernel
theorem subd10_0_418 : subd10_0 [1, -1, -10] = true := by decide +kernel
theorem subd10_0_419 : subd10_0 [1, -1, -9] = true := by decide +kernel
theorem subd10_0_420 : subd10_0 [1, -1, -8] = true := by decide +kernel
theorem subd10_0_421 : subd10_0 [1, -1, -7] = true := by decide +kernel
theorem subd10_0_422 : subd10_0 [1, -1, -6] = true := by decide +kernel
theorem subd10_0_423 : subd10_0 [1, -1, -5] = true := by decide +kernel
theorem subd10_0_424 : subd10_0 [1, -1, -4] = true := by decide +kernel
theorem subd10_0_425 : subd10_0 [1, -1, -3] = true := by decide +kernel
theorem subd10_0_426 : subd10_0 [1, -1, -2] = true := by decide +kernel
theorem subd10_0_427 : subd10_0 [1, -1, -1] = true := by decide +kernel
theorem subd10_0_428 : subd10_0 [1, -1, 0] = true := by decide +kernel
theorem subd10_0_429 : subd10_0 [1, -1, 1] = true := by decide +kernel
theorem subd10_0_430 : subd10_0 [1, -1, 2] = true := by decide +kernel
theorem subd10_0_431 : subd10_0 [1, -1, 3] = true := by decide +kernel
theorem subd10_0_432 : subd10_0 [1, -1, 4] = true := by decide +kernel
theorem subd10_0_433 : subd10_0 [1, -1, 5] = true := by decide +kernel
theorem subd10_0_434 : subd10_0 [1, -1, 6] = true := by decide +kernel
theorem subd10_0_435 : subd10_0 [1, -1, 7] = true := by decide +kernel
theorem subd10_0_436 : subd10_0 [1, -1, 8] = true := by decide +kernel
theorem subd10_0_437 : subd10_0 [1, -1, 9] = true := by decide +kernel
theorem subd10_0_438 : subd10_0 [1, -1, 10] = true := by decide +kernel
theorem subd10_0_439 : subd10_0 [1, 0, -10] = true := by decide +kernel
theorem subd10_0_440 : subd10_0 [1, 0, -9] = true := by decide +kernel
theorem subd10_0_441 : subd10_0 [1, 0, -8] = true := by decide +kernel
theorem subd10_0_442 : subd10_0 [1, 0, -7] = true := by decide +kernel
theorem subd10_0_443 : subd10_0 [1, 0, -6] = true := by decide +kernel
theorem subd10_0_444 : subd10_0 [1, 0, -5] = true := by decide +kernel
theorem subd10_0_445 : subd10_0 [1, 0, -4] = true := by decide +kernel
theorem subd10_0_446 : subd10_0 [1, 0, -3] = true := by decide +kernel
theorem subd10_0_447 : subd10_0 [1, 0, -2] = true := by decide +kernel
theorem sbd10_0_13 : ∀ q ∈ blkd10_0_13, subd10_0 q = true := by
  unfold blkd10_0_13
  exact List.forall_mem_cons.2 ⟨subd10_0_416, List.forall_mem_cons.2 ⟨subd10_0_417, List.forall_mem_cons.2 ⟨subd10_0_418, List.forall_mem_cons.2 ⟨subd10_0_419, List.forall_mem_cons.2 ⟨subd10_0_420, List.forall_mem_cons.2 ⟨subd10_0_421, List.forall_mem_cons.2 ⟨subd10_0_422, List.forall_mem_cons.2 ⟨subd10_0_423, List.forall_mem_cons.2 ⟨subd10_0_424, List.forall_mem_cons.2 ⟨subd10_0_425, List.forall_mem_cons.2 ⟨subd10_0_426, List.forall_mem_cons.2 ⟨subd10_0_427, List.forall_mem_cons.2 ⟨subd10_0_428, List.forall_mem_cons.2 ⟨subd10_0_429, List.forall_mem_cons.2 ⟨subd10_0_430, List.forall_mem_cons.2 ⟨subd10_0_431, List.forall_mem_cons.2 ⟨subd10_0_432, List.forall_mem_cons.2 ⟨subd10_0_433, List.forall_mem_cons.2 ⟨subd10_0_434, List.forall_mem_cons.2 ⟨subd10_0_435, List.forall_mem_cons.2 ⟨subd10_0_436, List.forall_mem_cons.2 ⟨subd10_0_437, List.forall_mem_cons.2 ⟨subd10_0_438, List.forall_mem_cons.2 ⟨subd10_0_439, List.forall_mem_cons.2 ⟨subd10_0_440, List.forall_mem_cons.2 ⟨subd10_0_441, List.forall_mem_cons.2 ⟨subd10_0_442, List.forall_mem_cons.2 ⟨subd10_0_443, List.forall_mem_cons.2 ⟨subd10_0_444, List.forall_mem_cons.2 ⟨subd10_0_445, List.forall_mem_cons.2 ⟨subd10_0_446, List.forall_mem_cons.2 ⟨subd10_0_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_448 : subd10_0 [1, 0, -1] = true := by decide +kernel
theorem subd10_0_449 : subd10_0 [1, 0, 0] = true := by decide +kernel
theorem subd10_0_450 : subd10_0 [1, 0, 1] = true := by decide +kernel
theorem subd10_0_451 : subd10_0 [1, 0, 2] = true := by decide +kernel
theorem subd10_0_452 : subd10_0 [1, 0, 3] = true := by decide +kernel
theorem subd10_0_453 : subd10_0 [1, 0, 4] = true := by decide +kernel
theorem subd10_0_454 : subd10_0 [1, 0, 5] = true := by decide +kernel
theorem subd10_0_455 : subd10_0 [1, 0, 6] = true := by decide +kernel
theorem subd10_0_456 : subd10_0 [1, 0, 7] = true := by decide +kernel
theorem subd10_0_457 : subd10_0 [1, 0, 8] = true := by decide +kernel
theorem subd10_0_458 : subd10_0 [1, 0, 9] = true := by decide +kernel
theorem subd10_0_459 : subd10_0 [1, 1, -10] = true := by decide +kernel
theorem subd10_0_460 : subd10_0 [1, 1, -9] = true := by decide +kernel
theorem subd10_0_461 : subd10_0 [1, 1, -8] = true := by decide +kernel
theorem subd10_0_462 : subd10_0 [1, 1, -7] = true := by decide +kernel
theorem subd10_0_463 : subd10_0 [1, 1, -6] = true := by decide +kernel
theorem subd10_0_464 : subd10_0 [1, 1, -5] = true := by decide +kernel
theorem subd10_0_465 : subd10_0 [1, 1, -4] = true := by decide +kernel
theorem subd10_0_466 : subd10_0 [1, 1, -3] = true := by decide +kernel
theorem subd10_0_467 : subd10_0 [1, 1, -2] = true := by decide +kernel
theorem subd10_0_468 : subd10_0 [1, 1, -1] = true := by decide +kernel
theorem subd10_0_469 : subd10_0 [1, 1, 0] = true := by decide +kernel
theorem subd10_0_470 : subd10_0 [1, 1, 1] = true := by decide +kernel
theorem subd10_0_471 : subd10_0 [1, 1, 2] = true := by decide +kernel
theorem subd10_0_472 : subd10_0 [1, 1, 3] = true := by decide +kernel
theorem subd10_0_473 : subd10_0 [1, 1, 4] = true := by decide +kernel
theorem subd10_0_474 : subd10_0 [1, 1, 5] = true := by decide +kernel
theorem subd10_0_475 : subd10_0 [1, 1, 6] = true := by decide +kernel
theorem subd10_0_476 : subd10_0 [1, 1, 7] = true := by decide +kernel
theorem subd10_0_477 : subd10_0 [1, 1, 8] = true := by decide +kernel
theorem subd10_0_478 : subd10_0 [1, 1, 9] = true := by decide +kernel
theorem subd10_0_479 : subd10_0 [1, 2, -9] = true := by decide +kernel
theorem sbd10_0_14 : ∀ q ∈ blkd10_0_14, subd10_0 q = true := by
  unfold blkd10_0_14
  exact List.forall_mem_cons.2 ⟨subd10_0_448, List.forall_mem_cons.2 ⟨subd10_0_449, List.forall_mem_cons.2 ⟨subd10_0_450, List.forall_mem_cons.2 ⟨subd10_0_451, List.forall_mem_cons.2 ⟨subd10_0_452, List.forall_mem_cons.2 ⟨subd10_0_453, List.forall_mem_cons.2 ⟨subd10_0_454, List.forall_mem_cons.2 ⟨subd10_0_455, List.forall_mem_cons.2 ⟨subd10_0_456, List.forall_mem_cons.2 ⟨subd10_0_457, List.forall_mem_cons.2 ⟨subd10_0_458, List.forall_mem_cons.2 ⟨subd10_0_459, List.forall_mem_cons.2 ⟨subd10_0_460, List.forall_mem_cons.2 ⟨subd10_0_461, List.forall_mem_cons.2 ⟨subd10_0_462, List.forall_mem_cons.2 ⟨subd10_0_463, List.forall_mem_cons.2 ⟨subd10_0_464, List.forall_mem_cons.2 ⟨subd10_0_465, List.forall_mem_cons.2 ⟨subd10_0_466, List.forall_mem_cons.2 ⟨subd10_0_467, List.forall_mem_cons.2 ⟨subd10_0_468, List.forall_mem_cons.2 ⟨subd10_0_469, List.forall_mem_cons.2 ⟨subd10_0_470, List.forall_mem_cons.2 ⟨subd10_0_471, List.forall_mem_cons.2 ⟨subd10_0_472, List.forall_mem_cons.2 ⟨subd10_0_473, List.forall_mem_cons.2 ⟨subd10_0_474, List.forall_mem_cons.2 ⟨subd10_0_475, List.forall_mem_cons.2 ⟨subd10_0_476, List.forall_mem_cons.2 ⟨subd10_0_477, List.forall_mem_cons.2 ⟨subd10_0_478, List.forall_mem_cons.2 ⟨subd10_0_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_480 : subd10_0 [1, 2, -8] = true := by decide +kernel
theorem subd10_0_481 : subd10_0 [1, 2, -7] = true := by decide +kernel
theorem subd10_0_482 : subd10_0 [1, 2, -6] = true := by decide +kernel
theorem subd10_0_483 : subd10_0 [1, 2, -5] = true := by decide +kernel
theorem subd10_0_484 : subd10_0 [1, 2, -4] = true := by decide +kernel
theorem subd10_0_485 : subd10_0 [1, 2, -3] = true := by decide +kernel
theorem subd10_0_486 : subd10_0 [1, 2, -2] = true := by decide +kernel
theorem subd10_0_487 : subd10_0 [1, 2, -1] = true := by decide +kernel
theorem subd10_0_488 : subd10_0 [1, 2, 0] = true := by decide +kernel
theorem subd10_0_489 : subd10_0 [1, 2, 1] = true := by decide +kernel
theorem subd10_0_490 : subd10_0 [1, 2, 2] = true := by decide +kernel
theorem subd10_0_491 : subd10_0 [1, 2, 3] = true := by decide +kernel
theorem subd10_0_492 : subd10_0 [1, 2, 4] = true := by decide +kernel
theorem subd10_0_493 : subd10_0 [1, 2, 5] = true := by decide +kernel
theorem subd10_0_494 : subd10_0 [1, 2, 6] = true := by decide +kernel
theorem subd10_0_495 : subd10_0 [1, 2, 7] = true := by decide +kernel
theorem subd10_0_496 : subd10_0 [1, 3] = true := by decide +kernel
theorem subd10_0_497 : subd10_0 [2, -5] = true := by decide +kernel
theorem subd10_0_498 : subd10_0 [2, -4] = true := by decide +kernel
theorem subd10_0_499 : subd10_0 [2, -3, -7] = true := by decide +kernel
theorem subd10_0_500 : subd10_0 [2, -3, -6] = true := by decide +kernel
theorem subd10_0_501 : subd10_0 [2, -3, -5] = true := by decide +kernel
theorem subd10_0_502 : subd10_0 [2, -3, -4] = true := by decide +kernel
theorem subd10_0_503 : subd10_0 [2, -3, -3] = true := by decide +kernel
theorem subd10_0_504 : subd10_0 [2, -3, -2] = true := by decide +kernel
theorem subd10_0_505 : subd10_0 [2, -3, -1] = true := by decide +kernel
theorem subd10_0_506 : subd10_0 [2, -3, 0] = true := by decide +kernel
theorem subd10_0_507 : subd10_0 [2, -3, 1] = true := by decide +kernel
theorem subd10_0_508 : subd10_0 [2, -3, 2] = true := by decide +kernel
theorem subd10_0_509 : subd10_0 [2, -3, 3] = true := by decide +kernel
theorem subd10_0_510 : subd10_0 [2, -3, 4] = true := by decide +kernel
theorem subd10_0_511 : subd10_0 [2, -3, 5] = true := by decide +kernel
theorem sbd10_0_15 : ∀ q ∈ blkd10_0_15, subd10_0 q = true := by
  unfold blkd10_0_15
  exact List.forall_mem_cons.2 ⟨subd10_0_480, List.forall_mem_cons.2 ⟨subd10_0_481, List.forall_mem_cons.2 ⟨subd10_0_482, List.forall_mem_cons.2 ⟨subd10_0_483, List.forall_mem_cons.2 ⟨subd10_0_484, List.forall_mem_cons.2 ⟨subd10_0_485, List.forall_mem_cons.2 ⟨subd10_0_486, List.forall_mem_cons.2 ⟨subd10_0_487, List.forall_mem_cons.2 ⟨subd10_0_488, List.forall_mem_cons.2 ⟨subd10_0_489, List.forall_mem_cons.2 ⟨subd10_0_490, List.forall_mem_cons.2 ⟨subd10_0_491, List.forall_mem_cons.2 ⟨subd10_0_492, List.forall_mem_cons.2 ⟨subd10_0_493, List.forall_mem_cons.2 ⟨subd10_0_494, List.forall_mem_cons.2 ⟨subd10_0_495, List.forall_mem_cons.2 ⟨subd10_0_496, List.forall_mem_cons.2 ⟨subd10_0_497, List.forall_mem_cons.2 ⟨subd10_0_498, List.forall_mem_cons.2 ⟨subd10_0_499, List.forall_mem_cons.2 ⟨subd10_0_500, List.forall_mem_cons.2 ⟨subd10_0_501, List.forall_mem_cons.2 ⟨subd10_0_502, List.forall_mem_cons.2 ⟨subd10_0_503, List.forall_mem_cons.2 ⟨subd10_0_504, List.forall_mem_cons.2 ⟨subd10_0_505, List.forall_mem_cons.2 ⟨subd10_0_506, List.forall_mem_cons.2 ⟨subd10_0_507, List.forall_mem_cons.2 ⟨subd10_0_508, List.forall_mem_cons.2 ⟨subd10_0_509, List.forall_mem_cons.2 ⟨subd10_0_510, List.forall_mem_cons.2 ⟨subd10_0_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_512 : subd10_0 [2, -3, 6] = true := by decide +kernel
theorem subd10_0_513 : subd10_0 [2, -3, 7] = true := by decide +kernel
theorem subd10_0_514 : subd10_0 [2, -3, 8] = true := by decide +kernel
theorem subd10_0_515 : subd10_0 [2, -2, -8] = true := by decide +kernel
theorem subd10_0_516 : subd10_0 [2, -2, -7] = true := by decide +kernel
theorem subd10_0_517 : subd10_0 [2, -2, -6] = true := by decide +kernel
theorem subd10_0_518 : subd10_0 [2, -2, -5] = true := by decide +kernel
theorem subd10_0_519 : subd10_0 [2, -2, -4] = true := by decide +kernel
theorem subd10_0_520 : subd10_0 [2, -2, -3] = true := by decide +kernel
theorem subd10_0_521 : subd10_0 [2, -2, -2] = true := by decide +kernel
theorem subd10_0_522 : subd10_0 [2, -2, -1] = true := by decide +kernel
theorem subd10_0_523 : subd10_0 [2, -2, 0] = true := by decide +kernel
theorem subd10_0_524 : subd10_0 [2, -2, 1] = true := by decide +kernel
theorem subd10_0_525 : subd10_0 [2, -2, 2] = true := by decide +kernel
theorem subd10_0_526 : subd10_0 [2, -2, 3] = true := by decide +kernel
theorem subd10_0_527 : subd10_0 [2, -2, 4] = true := by decide +kernel
theorem subd10_0_528 : subd10_0 [2, -2, 5] = true := by decide +kernel
theorem subd10_0_529 : subd10_0 [2, -2, 6] = true := by decide +kernel
theorem subd10_0_530 : subd10_0 [2, -2, 7] = true := by decide +kernel
theorem subd10_0_531 : subd10_0 [2, -2, 8] = true := by decide +kernel
theorem subd10_0_532 : subd10_0 [2, -2, 9] = true := by decide +kernel
theorem subd10_0_533 : subd10_0 [2, -1, -9] = true := by decide +kernel
theorem subd10_0_534 : subd10_0 [2, -1, -8] = true := by decide +kernel
theorem subd10_0_535 : subd10_0 [2, -1, -7] = true := by decide +kernel
theorem subd10_0_536 : subd10_0 [2, -1, -6] = true := by decide +kernel
theorem subd10_0_537 : subd10_0 [2, -1, -5] = true := by decide +kernel
theorem subd10_0_538 : subd10_0 [2, -1, -4] = true := by decide +kernel
theorem subd10_0_539 : subd10_0 [2, -1, -3] = true := by decide +kernel
theorem subd10_0_540 : subd10_0 [2, -1, -2] = true := by decide +kernel
theorem subd10_0_541 : subd10_0 [2, -1, -1] = true := by decide +kernel
theorem subd10_0_542 : subd10_0 [2, -1, 0] = true := by decide +kernel
theorem subd10_0_543 : subd10_0 [2, -1, 1] = true := by decide +kernel
theorem sbd10_0_16 : ∀ q ∈ blkd10_0_16, subd10_0 q = true := by
  unfold blkd10_0_16
  exact List.forall_mem_cons.2 ⟨subd10_0_512, List.forall_mem_cons.2 ⟨subd10_0_513, List.forall_mem_cons.2 ⟨subd10_0_514, List.forall_mem_cons.2 ⟨subd10_0_515, List.forall_mem_cons.2 ⟨subd10_0_516, List.forall_mem_cons.2 ⟨subd10_0_517, List.forall_mem_cons.2 ⟨subd10_0_518, List.forall_mem_cons.2 ⟨subd10_0_519, List.forall_mem_cons.2 ⟨subd10_0_520, List.forall_mem_cons.2 ⟨subd10_0_521, List.forall_mem_cons.2 ⟨subd10_0_522, List.forall_mem_cons.2 ⟨subd10_0_523, List.forall_mem_cons.2 ⟨subd10_0_524, List.forall_mem_cons.2 ⟨subd10_0_525, List.forall_mem_cons.2 ⟨subd10_0_526, List.forall_mem_cons.2 ⟨subd10_0_527, List.forall_mem_cons.2 ⟨subd10_0_528, List.forall_mem_cons.2 ⟨subd10_0_529, List.forall_mem_cons.2 ⟨subd10_0_530, List.forall_mem_cons.2 ⟨subd10_0_531, List.forall_mem_cons.2 ⟨subd10_0_532, List.forall_mem_cons.2 ⟨subd10_0_533, List.forall_mem_cons.2 ⟨subd10_0_534, List.forall_mem_cons.2 ⟨subd10_0_535, List.forall_mem_cons.2 ⟨subd10_0_536, List.forall_mem_cons.2 ⟨subd10_0_537, List.forall_mem_cons.2 ⟨subd10_0_538, List.forall_mem_cons.2 ⟨subd10_0_539, List.forall_mem_cons.2 ⟨subd10_0_540, List.forall_mem_cons.2 ⟨subd10_0_541, List.forall_mem_cons.2 ⟨subd10_0_542, List.forall_mem_cons.2 ⟨subd10_0_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_544 : subd10_0 [2, -1, 2] = true := by decide +kernel
theorem subd10_0_545 : subd10_0 [2, -1, 3] = true := by decide +kernel
theorem subd10_0_546 : subd10_0 [2, -1, 4] = true := by decide +kernel
theorem subd10_0_547 : subd10_0 [2, -1, 5] = true := by decide +kernel
theorem subd10_0_548 : subd10_0 [2, -1, 6] = true := by decide +kernel
theorem subd10_0_549 : subd10_0 [2, -1, 7] = true := by decide +kernel
theorem subd10_0_550 : subd10_0 [2, -1, 8] = true := by decide +kernel
theorem subd10_0_551 : subd10_0 [2, -1, 9] = true := by decide +kernel
theorem subd10_0_552 : subd10_0 [2, 0, -9] = true := by decide +kernel
theorem subd10_0_553 : subd10_0 [2, 0, -8] = true := by decide +kernel
theorem subd10_0_554 : subd10_0 [2, 0, -7] = true := by decide +kernel
theorem subd10_0_555 : subd10_0 [2, 0, -6] = true := by decide +kernel
theorem subd10_0_556 : subd10_0 [2, 0, -5] = true := by decide +kernel
theorem subd10_0_557 : subd10_0 [2, 0, -4] = true := by decide +kernel
theorem subd10_0_558 : subd10_0 [2, 0, -3] = true := by decide +kernel
theorem subd10_0_559 : subd10_0 [2, 0, -2] = true := by decide +kernel
theorem subd10_0_560 : subd10_0 [2, 0, -1] = true := by decide +kernel
theorem subd10_0_561 : subd10_0 [2, 0, 0] = true := by decide +kernel
theorem subd10_0_562 : subd10_0 [2, 0, 1] = true := by decide +kernel
theorem subd10_0_563 : subd10_0 [2, 0, 2] = true := by decide +kernel
theorem subd10_0_564 : subd10_0 [2, 0, 3] = true := by decide +kernel
theorem subd10_0_565 : subd10_0 [2, 0, 4] = true := by decide +kernel
theorem subd10_0_566 : subd10_0 [2, 0, 5] = true := by decide +kernel
theorem subd10_0_567 : subd10_0 [2, 0, 6] = true := by decide +kernel
theorem subd10_0_568 : subd10_0 [2, 0, 7] = true := by decide +kernel
theorem subd10_0_569 : subd10_0 [2, 0, 8] = true := by decide +kernel
theorem subd10_0_570 : subd10_0 [2, 1, -8] = true := by decide +kernel
theorem subd10_0_571 : subd10_0 [2, 1, -7] = true := by decide +kernel
theorem subd10_0_572 : subd10_0 [2, 1, -6] = true := by decide +kernel
theorem subd10_0_573 : subd10_0 [2, 1, -5] = true := by decide +kernel
theorem subd10_0_574 : subd10_0 [2, 1, -4] = true := by decide +kernel
theorem subd10_0_575 : subd10_0 [2, 1, -3] = true := by decide +kernel
theorem sbd10_0_17 : ∀ q ∈ blkd10_0_17, subd10_0 q = true := by
  unfold blkd10_0_17
  exact List.forall_mem_cons.2 ⟨subd10_0_544, List.forall_mem_cons.2 ⟨subd10_0_545, List.forall_mem_cons.2 ⟨subd10_0_546, List.forall_mem_cons.2 ⟨subd10_0_547, List.forall_mem_cons.2 ⟨subd10_0_548, List.forall_mem_cons.2 ⟨subd10_0_549, List.forall_mem_cons.2 ⟨subd10_0_550, List.forall_mem_cons.2 ⟨subd10_0_551, List.forall_mem_cons.2 ⟨subd10_0_552, List.forall_mem_cons.2 ⟨subd10_0_553, List.forall_mem_cons.2 ⟨subd10_0_554, List.forall_mem_cons.2 ⟨subd10_0_555, List.forall_mem_cons.2 ⟨subd10_0_556, List.forall_mem_cons.2 ⟨subd10_0_557, List.forall_mem_cons.2 ⟨subd10_0_558, List.forall_mem_cons.2 ⟨subd10_0_559, List.forall_mem_cons.2 ⟨subd10_0_560, List.forall_mem_cons.2 ⟨subd10_0_561, List.forall_mem_cons.2 ⟨subd10_0_562, List.forall_mem_cons.2 ⟨subd10_0_563, List.forall_mem_cons.2 ⟨subd10_0_564, List.forall_mem_cons.2 ⟨subd10_0_565, List.forall_mem_cons.2 ⟨subd10_0_566, List.forall_mem_cons.2 ⟨subd10_0_567, List.forall_mem_cons.2 ⟨subd10_0_568, List.forall_mem_cons.2 ⟨subd10_0_569, List.forall_mem_cons.2 ⟨subd10_0_570, List.forall_mem_cons.2 ⟨subd10_0_571, List.forall_mem_cons.2 ⟨subd10_0_572, List.forall_mem_cons.2 ⟨subd10_0_573, List.forall_mem_cons.2 ⟨subd10_0_574, List.forall_mem_cons.2 ⟨subd10_0_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_576 : subd10_0 [2, 1, -2] = true := by decide +kernel
theorem subd10_0_577 : subd10_0 [2, 1, -1] = true := by decide +kernel
theorem subd10_0_578 : subd10_0 [2, 1, 0] = true := by decide +kernel
theorem subd10_0_579 : subd10_0 [2, 1, 1] = true := by decide +kernel
theorem subd10_0_580 : subd10_0 [2, 1, 2] = true := by decide +kernel
theorem subd10_0_581 : subd10_0 [2, 1, 3] = true := by decide +kernel
theorem subd10_0_582 : subd10_0 [2, 1, 4] = true := by decide +kernel
theorem subd10_0_583 : subd10_0 [2, 1, 5] = true := by decide +kernel
theorem subd10_0_584 : subd10_0 [2, 1, 6] = true := by decide +kernel
theorem subd10_0_585 : subd10_0 [2, 1, 7] = true := by decide +kernel
theorem subd10_0_586 : subd10_0 [2, 2] = true := by decide +kernel
theorem subd10_0_587 : subd10_0 [2, 3] = true := by decide +kernel
theorem subd10_0_588 : subd10_0 [3, -5] = true := by decide +kernel
theorem subd10_0_589 : subd10_0 [3, -4] = true := by decide +kernel
theorem subd10_0_590 : subd10_0 [3, -3] = true := by decide +kernel
theorem subd10_0_591 : subd10_0 [3, -2, -6] = true := by decide +kernel
theorem subd10_0_592 : subd10_0 [3, -2, -5] = true := by decide +kernel
theorem subd10_0_593 : subd10_0 [3, -2, -4] = true := by decide +kernel
theorem subd10_0_594 : subd10_0 [3, -2, -3] = true := by decide +kernel
theorem subd10_0_595 : subd10_0 [3, -2, -2] = true := by decide +kernel
theorem subd10_0_596 : subd10_0 [3, -2, -1] = true := by decide +kernel
theorem subd10_0_597 : subd10_0 [3, -2, 0] = true := by decide +kernel
theorem subd10_0_598 : subd10_0 [3, -2, 1] = true := by decide +kernel
theorem subd10_0_599 : subd10_0 [3, -2, 2] = true := by decide +kernel
theorem subd10_0_600 : subd10_0 [3, -2, 3] = true := by decide +kernel
theorem subd10_0_601 : subd10_0 [3, -2, 4] = true := by decide +kernel
theorem subd10_0_602 : subd10_0 [3, -2, 5] = true := by decide +kernel
theorem subd10_0_603 : subd10_0 [3, -2, 6] = true := by decide +kernel
theorem subd10_0_604 : subd10_0 [3, -2, 7] = true := by decide +kernel
theorem subd10_0_605 : subd10_0 [3, -1, -7] = true := by decide +kernel
theorem subd10_0_606 : subd10_0 [3, -1, -6] = true := by decide +kernel
theorem subd10_0_607 : subd10_0 [3, -1, -5] = true := by decide +kernel
theorem sbd10_0_18 : ∀ q ∈ blkd10_0_18, subd10_0 q = true := by
  unfold blkd10_0_18
  exact List.forall_mem_cons.2 ⟨subd10_0_576, List.forall_mem_cons.2 ⟨subd10_0_577, List.forall_mem_cons.2 ⟨subd10_0_578, List.forall_mem_cons.2 ⟨subd10_0_579, List.forall_mem_cons.2 ⟨subd10_0_580, List.forall_mem_cons.2 ⟨subd10_0_581, List.forall_mem_cons.2 ⟨subd10_0_582, List.forall_mem_cons.2 ⟨subd10_0_583, List.forall_mem_cons.2 ⟨subd10_0_584, List.forall_mem_cons.2 ⟨subd10_0_585, List.forall_mem_cons.2 ⟨subd10_0_586, List.forall_mem_cons.2 ⟨subd10_0_587, List.forall_mem_cons.2 ⟨subd10_0_588, List.forall_mem_cons.2 ⟨subd10_0_589, List.forall_mem_cons.2 ⟨subd10_0_590, List.forall_mem_cons.2 ⟨subd10_0_591, List.forall_mem_cons.2 ⟨subd10_0_592, List.forall_mem_cons.2 ⟨subd10_0_593, List.forall_mem_cons.2 ⟨subd10_0_594, List.forall_mem_cons.2 ⟨subd10_0_595, List.forall_mem_cons.2 ⟨subd10_0_596, List.forall_mem_cons.2 ⟨subd10_0_597, List.forall_mem_cons.2 ⟨subd10_0_598, List.forall_mem_cons.2 ⟨subd10_0_599, List.forall_mem_cons.2 ⟨subd10_0_600, List.forall_mem_cons.2 ⟨subd10_0_601, List.forall_mem_cons.2 ⟨subd10_0_602, List.forall_mem_cons.2 ⟨subd10_0_603, List.forall_mem_cons.2 ⟨subd10_0_604, List.forall_mem_cons.2 ⟨subd10_0_605, List.forall_mem_cons.2 ⟨subd10_0_606, List.forall_mem_cons.2 ⟨subd10_0_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_608 : subd10_0 [3, -1, -4] = true := by decide +kernel
theorem subd10_0_609 : subd10_0 [3, -1, -3] = true := by decide +kernel
theorem subd10_0_610 : subd10_0 [3, -1, -2] = true := by decide +kernel
theorem subd10_0_611 : subd10_0 [3, -1, -1] = true := by decide +kernel
theorem subd10_0_612 : subd10_0 [3, -1, 0] = true := by decide +kernel
theorem subd10_0_613 : subd10_0 [3, -1, 1] = true := by decide +kernel
theorem subd10_0_614 : subd10_0 [3, -1, 2] = true := by decide +kernel
theorem subd10_0_615 : subd10_0 [3, -1, 3] = true := by decide +kernel
theorem subd10_0_616 : subd10_0 [3, -1, 4] = true := by decide +kernel
theorem subd10_0_617 : subd10_0 [3, -1, 5] = true := by decide +kernel
theorem subd10_0_618 : subd10_0 [3, -1, 6] = true := by decide +kernel
theorem subd10_0_619 : subd10_0 [3, -1, 7] = true := by decide +kernel
theorem subd10_0_620 : subd10_0 [3, 0] = true := by decide +kernel
theorem subd10_0_621 : subd10_0 [3, 1] = true := by decide +kernel
theorem subd10_0_622 : subd10_0 [4] = true := by decide +kernel
theorem sbd10_0_19 : ∀ q ∈ blkd10_0_19, subd10_0 q = true := by
  unfold blkd10_0_19
  exact List.forall_mem_cons.2 ⟨subd10_0_608, List.forall_mem_cons.2 ⟨subd10_0_609, List.forall_mem_cons.2 ⟨subd10_0_610, List.forall_mem_cons.2 ⟨subd10_0_611, List.forall_mem_cons.2 ⟨subd10_0_612, List.forall_mem_cons.2 ⟨subd10_0_613, List.forall_mem_cons.2 ⟨subd10_0_614, List.forall_mem_cons.2 ⟨subd10_0_615, List.forall_mem_cons.2 ⟨subd10_0_616, List.forall_mem_cons.2 ⟨subd10_0_617, List.forall_mem_cons.2 ⟨subd10_0_618, List.forall_mem_cons.2 ⟨subd10_0_619, List.forall_mem_cons.2 ⟨subd10_0_620, List.forall_mem_cons.2 ⟨subd10_0_621, List.forall_mem_cons.2 ⟨subd10_0_622, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_1 : ldCheck G d10_1.U d10_1.ms ldd10_1 = true := by decide +kernel
theorem pre_okd10_1 : subPre G cell10 d10_1 = true := by decide +kernel
theorem subd10_1_0 : subd10_1 [-2] = true := by decide +kernel
theorem subd10_1_1 : subd10_1 [-1] = true := by decide +kernel
theorem subd10_1_2 : subd10_1 [0] = true := by decide +kernel
theorem subd10_1_3 : subd10_1 [1] = true := by decide +kernel
theorem subd10_1_4 : subd10_1 [2] = true := by decide +kernel
theorem sbd10_1_0 : ∀ q ∈ blkd10_1_0, subd10_1 q = true := by
  unfold blkd10_1_0
  exact List.forall_mem_cons.2 ⟨subd10_1_0, List.forall_mem_cons.2 ⟨subd10_1_1, List.forall_mem_cons.2 ⟨subd10_1_2, List.forall_mem_cons.2 ⟨subd10_1_3, List.forall_mem_cons.2 ⟨subd10_1_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd10_2 : ldCheck G d10_2.U d10_2.ms ldd10_2 = true := by decide +kernel
theorem pre_okd10_2 : subPre G cell10 d10_2 = true := by decide +kernel
theorem subd10_2_0 : subd10_2 [-2] = true := by decide +kernel
theorem subd10_2_1 : subd10_2 [-1] = true := by decide +kernel
theorem subd10_2_2 : subd10_2 [0, -3] = true := by decide +kernel
theorem subd10_2_3 : subd10_2 [0, -2] = true := by decide +kernel
theorem subd10_2_4 : subd10_2 [0, -1] = true := by decide +kernel
theorem subd10_2_5 : subd10_2 [0, 0] = true := by decide +kernel
theorem subd10_2_6 : subd10_2 [0, 1] = true := by decide +kernel
theorem subd10_2_7 : subd10_2 [0, 2] = true := by decide +kernel
theorem subd10_2_8 : subd10_2 [1] = true := by decide +kernel
theorem subd10_2_9 : subd10_2 [2] = true := by decide +kernel
theorem sbd10_2_0 : ∀ q ∈ blkd10_2_0, subd10_2 q = true := by
  unfold blkd10_2_0
  exact List.forall_mem_cons.2 ⟨subd10_2_0, List.forall_mem_cons.2 ⟨subd10_2_1, List.forall_mem_cons.2 ⟨subd10_2_2, List.forall_mem_cons.2 ⟨subd10_2_3, List.forall_mem_cons.2 ⟨subd10_2_4, List.forall_mem_cons.2 ⟨subd10_2_5, List.forall_mem_cons.2 ⟨subd10_2_6, List.forall_mem_cons.2 ⟨subd10_2_7, List.forall_mem_cons.2 ⟨subd10_2_8, List.forall_mem_cons.2 ⟨subd10_2_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C093
