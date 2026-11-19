import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd17_0_352 : subd17_0 [0, 1, -2] = true := by decide +kernel
theorem subd17_0_353 : subd17_0 [0, 1, -1] = true := by decide +kernel
theorem subd17_0_354 : subd17_0 [0, 1, 0] = true := by decide +kernel
theorem subd17_0_355 : subd17_0 [0, 1, 1] = true := by decide +kernel
theorem subd17_0_356 : subd17_0 [0, 1, 2] = true := by decide +kernel
theorem subd17_0_357 : subd17_0 [0, 1, 3] = true := by decide +kernel
theorem subd17_0_358 : subd17_0 [0, 1, 4] = true := by decide +kernel
theorem subd17_0_359 : subd17_0 [0, 1, 5] = true := by decide +kernel
theorem subd17_0_360 : subd17_0 [0, 1, 6] = true := by decide +kernel
theorem subd17_0_361 : subd17_0 [0, 1, 7] = true := by decide +kernel
theorem subd17_0_362 : subd17_0 [0, 1, 8] = true := by decide +kernel
theorem subd17_0_363 : subd17_0 [0, 1, 9] = true := by decide +kernel
theorem subd17_0_364 : subd17_0 [0, 1, 10] = true := by decide +kernel
theorem subd17_0_365 : subd17_0 [0, 1, 11] = true := by decide +kernel
theorem subd17_0_366 : subd17_0 [0, 1, 12] = true := by decide +kernel
theorem subd17_0_367 : subd17_0 [0, 1, 13] = true := by decide +kernel
theorem subd17_0_368 : subd17_0 [0, 1, 14] = true := by decide +kernel
theorem subd17_0_369 : subd17_0 [0, 2, -12] = true := by decide +kernel
theorem subd17_0_370 : subd17_0 [0, 2, -11] = true := by decide +kernel
theorem subd17_0_371 : subd17_0 [0, 2, -10] = true := by decide +kernel
theorem subd17_0_372 : subd17_0 [0, 2, -9] = true := by decide +kernel
theorem subd17_0_373 : subd17_0 [0, 2, -8] = true := by decide +kernel
theorem subd17_0_374 : subd17_0 [0, 2, -7] = true := by decide +kernel
theorem subd17_0_375 : subd17_0 [0, 2, -6] = true := by decide +kernel
theorem subd17_0_376 : subd17_0 [0, 2, -5] = true := by decide +kernel
theorem subd17_0_377 : subd17_0 [0, 2, -4] = true := by decide +kernel
theorem subd17_0_378 : subd17_0 [0, 2, -3] = true := by decide +kernel
theorem subd17_0_379 : subd17_0 [0, 2, -2] = true := by decide +kernel
theorem subd17_0_380 : subd17_0 [0, 2, -1] = true := by decide +kernel
theorem subd17_0_381 : subd17_0 [0, 2, 0] = true := by decide +kernel
theorem subd17_0_382 : subd17_0 [0, 2, 1] = true := by decide +kernel
theorem subd17_0_383 : subd17_0 [0, 2, 2] = true := by decide +kernel
theorem sbd17_0_11 : ∀ q ∈ blkd17_0_11, subd17_0 q = true := by
  unfold blkd17_0_11
  exact List.forall_mem_cons.2 ⟨subd17_0_352, List.forall_mem_cons.2 ⟨subd17_0_353, List.forall_mem_cons.2 ⟨subd17_0_354, List.forall_mem_cons.2 ⟨subd17_0_355, List.forall_mem_cons.2 ⟨subd17_0_356, List.forall_mem_cons.2 ⟨subd17_0_357, List.forall_mem_cons.2 ⟨subd17_0_358, List.forall_mem_cons.2 ⟨subd17_0_359, List.forall_mem_cons.2 ⟨subd17_0_360, List.forall_mem_cons.2 ⟨subd17_0_361, List.forall_mem_cons.2 ⟨subd17_0_362, List.forall_mem_cons.2 ⟨subd17_0_363, List.forall_mem_cons.2 ⟨subd17_0_364, List.forall_mem_cons.2 ⟨subd17_0_365, List.forall_mem_cons.2 ⟨subd17_0_366, List.forall_mem_cons.2 ⟨subd17_0_367, List.forall_mem_cons.2 ⟨subd17_0_368, List.forall_mem_cons.2 ⟨subd17_0_369, List.forall_mem_cons.2 ⟨subd17_0_370, List.forall_mem_cons.2 ⟨subd17_0_371, List.forall_mem_cons.2 ⟨subd17_0_372, List.forall_mem_cons.2 ⟨subd17_0_373, List.forall_mem_cons.2 ⟨subd17_0_374, List.forall_mem_cons.2 ⟨subd17_0_375, List.forall_mem_cons.2 ⟨subd17_0_376, List.forall_mem_cons.2 ⟨subd17_0_377, List.forall_mem_cons.2 ⟨subd17_0_378, List.forall_mem_cons.2 ⟨subd17_0_379, List.forall_mem_cons.2 ⟨subd17_0_380, List.forall_mem_cons.2 ⟨subd17_0_381, List.forall_mem_cons.2 ⟨subd17_0_382, List.forall_mem_cons.2 ⟨subd17_0_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_0_384 : subd17_0 [0, 2, 3] = true := by decide +kernel
theorem subd17_0_385 : subd17_0 [0, 2, 4] = true := by decide +kernel
theorem subd17_0_386 : subd17_0 [0, 2, 5] = true := by decide +kernel
theorem subd17_0_387 : subd17_0 [0, 2, 6] = true := by decide +kernel
theorem subd17_0_388 : subd17_0 [0, 2, 7] = true := by decide +kernel
theorem subd17_0_389 : subd17_0 [0, 2, 8] = true := by decide +kernel
theorem subd17_0_390 : subd17_0 [0, 2, 9] = true := by decide +kernel
theorem subd17_0_391 : subd17_0 [0, 2, 10] = true := by decide +kernel
theorem subd17_0_392 : subd17_0 [0, 2, 11] = true := by decide +kernel
theorem subd17_0_393 : subd17_0 [0, 2, 12] = true := by decide +kernel
theorem subd17_0_394 : subd17_0 [0, 3, -8] = true := by decide +kernel
theorem subd17_0_395 : subd17_0 [0, 3, -7] = true := by decide +kernel
theorem subd17_0_396 : subd17_0 [0, 3, -6] = true := by decide +kernel
theorem subd17_0_397 : subd17_0 [0, 3, -5] = true := by decide +kernel
theorem subd17_0_398 : subd17_0 [0, 3, -4] = true := by decide +kernel
theorem subd17_0_399 : subd17_0 [0, 3, -3] = true := by decide +kernel
theorem subd17_0_400 : subd17_0 [0, 3, -2] = true := by decide +kernel
theorem subd17_0_401 : subd17_0 [0, 3, -1] = true := by decide +kernel
theorem subd17_0_402 : subd17_0 [0, 3, 0] = true := by decide +kernel
theorem subd17_0_403 : subd17_0 [0, 3, 1] = true := by decide +kernel
theorem subd17_0_404 : subd17_0 [0, 3, 2] = true := by decide +kernel
theorem subd17_0_405 : subd17_0 [0, 3, 3] = true := by decide +kernel
theorem subd17_0_406 : subd17_0 [0, 3, 4] = true := by decide +kernel
theorem subd17_0_407 : subd17_0 [0, 3, 5] = true := by decide +kernel
theorem subd17_0_408 : subd17_0 [0, 3, 6] = true := by decide +kernel
theorem subd17_0_409 : subd17_0 [0, 3, 7] = true := by decide +kernel
theorem subd17_0_410 : subd17_0 [1, -3] = true := by decide +kernel
theorem subd17_0_411 : subd17_0 [1, -2, -10] = true := by decide +kernel
theorem subd17_0_412 : subd17_0 [1, -2, -9] = true := by decide +kernel
theorem subd17_0_413 : subd17_0 [1, -2, -8] = true := by decide +kernel
theorem subd17_0_414 : subd17_0 [1, -2, -7] = true := by decide +kernel
theorem subd17_0_415 : subd17_0 [1, -2, -6] = true := by decide +kernel
theorem sbd17_0_12 : ∀ q ∈ blkd17_0_12, subd17_0 q = true := by
  unfold blkd17_0_12
  exact List.forall_mem_cons.2 ⟨subd17_0_384, List.forall_mem_cons.2 ⟨subd17_0_385, List.forall_mem_cons.2 ⟨subd17_0_386, List.forall_mem_cons.2 ⟨subd17_0_387, List.forall_mem_cons.2 ⟨subd17_0_388, List.forall_mem_cons.2 ⟨subd17_0_389, List.forall_mem_cons.2 ⟨subd17_0_390, List.forall_mem_cons.2 ⟨subd17_0_391, List.forall_mem_cons.2 ⟨subd17_0_392, List.forall_mem_cons.2 ⟨subd17_0_393, List.forall_mem_cons.2 ⟨subd17_0_394, List.forall_mem_cons.2 ⟨subd17_0_395, List.forall_mem_cons.2 ⟨subd17_0_396, List.forall_mem_cons.2 ⟨subd17_0_397, List.forall_mem_cons.2 ⟨subd17_0_398, List.forall_mem_cons.2 ⟨subd17_0_399, List.forall_mem_cons.2 ⟨subd17_0_400, List.forall_mem_cons.2 ⟨subd17_0_401, List.forall_mem_cons.2 ⟨subd17_0_402, List.forall_mem_cons.2 ⟨subd17_0_403, List.forall_mem_cons.2 ⟨subd17_0_404, List.forall_mem_cons.2 ⟨subd17_0_405, List.forall_mem_cons.2 ⟨subd17_0_406, List.forall_mem_cons.2 ⟨subd17_0_407, List.forall_mem_cons.2 ⟨subd17_0_408, List.forall_mem_cons.2 ⟨subd17_0_409, List.forall_mem_cons.2 ⟨subd17_0_410, List.forall_mem_cons.2 ⟨subd17_0_411, List.forall_mem_cons.2 ⟨subd17_0_412, List.forall_mem_cons.2 ⟨subd17_0_413, List.forall_mem_cons.2 ⟨subd17_0_414, List.forall_mem_cons.2 ⟨subd17_0_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_0_416 : subd17_0 [1, -2, -5] = true := by decide +kernel
theorem subd17_0_417 : subd17_0 [1, -2, -4] = true := by decide +kernel
theorem subd17_0_418 : subd17_0 [1, -2, -3] = true := by decide +kernel
theorem subd17_0_419 : subd17_0 [1, -2, -2] = true := by decide +kernel
theorem subd17_0_420 : subd17_0 [1, -2, -1] = true := by decide +kernel
theorem subd17_0_421 : subd17_0 [1, -2, 0] = true := by decide +kernel
theorem subd17_0_422 : subd17_0 [1, -2, 1] = true := by decide +kernel
theorem subd17_0_423 : subd17_0 [1, -2, 2] = true := by decide +kernel
theorem subd17_0_424 : subd17_0 [1, -2, 3] = true := by decide +kernel
theorem subd17_0_425 : subd17_0 [1, -2, 4] = true := by decide +kernel
theorem subd17_0_426 : subd17_0 [1, -2, 5] = true := by decide +kernel
theorem subd17_0_427 : subd17_0 [1, -2, 6] = true := by decide +kernel
theorem subd17_0_428 : subd17_0 [1, -2, 7] = true := by decide +kernel
theorem subd17_0_429 : subd17_0 [1, -2, 8] = true := by decide +kernel
theorem subd17_0_430 : subd17_0 [1, -2, 9] = true := by decide +kernel
theorem subd17_0_431 : subd17_0 [1, -1, -13] = true := by decide +kernel
theorem subd17_0_432 : subd17_0 [1, -1, -12] = true := by decide +kernel
theorem subd17_0_433 : subd17_0 [1, -1, -11] = true := by decide +kernel
theorem subd17_0_434 : subd17_0 [1, -1, -10] = true := by decide +kernel
theorem subd17_0_435 : subd17_0 [1, -1, -9] = true := by decide +kernel
theorem subd17_0_436 : subd17_0 [1, -1, -8] = true := by decide +kernel
theorem subd17_0_437 : subd17_0 [1, -1, -7] = true := by decide +kernel
theorem subd17_0_438 : subd17_0 [1, -1, -6] = true := by decide +kernel
theorem subd17_0_439 : subd17_0 [1, -1, -5] = true := by decide +kernel
theorem subd17_0_440 : subd17_0 [1, -1, -4] = true := by decide +kernel
theorem subd17_0_441 : subd17_0 [1, -1, -3] = true := by decide +kernel
theorem subd17_0_442 : subd17_0 [1, -1, -2] = true := by decide +kernel
theorem subd17_0_443 : subd17_0 [1, -1, -1] = true := by decide +kernel
theorem subd17_0_444 : subd17_0 [1, -1, 0] = true := by decide +kernel
theorem subd17_0_445 : subd17_0 [1, -1, 1] = true := by decide +kernel
theorem subd17_0_446 : subd17_0 [1, -1, 2] = true := by decide +kernel
theorem subd17_0_447 : subd17_0 [1, -1, 3] = true := by decide +kernel
theorem sbd17_0_13 : ∀ q ∈ blkd17_0_13, subd17_0 q = true := by
  unfold blkd17_0_13
  exact List.forall_mem_cons.2 ⟨subd17_0_416, List.forall_mem_cons.2 ⟨subd17_0_417, List.forall_mem_cons.2 ⟨subd17_0_418, List.forall_mem_cons.2 ⟨subd17_0_419, List.forall_mem_cons.2 ⟨subd17_0_420, List.forall_mem_cons.2 ⟨subd17_0_421, List.forall_mem_cons.2 ⟨subd17_0_422, List.forall_mem_cons.2 ⟨subd17_0_423, List.forall_mem_cons.2 ⟨subd17_0_424, List.forall_mem_cons.2 ⟨subd17_0_425, List.forall_mem_cons.2 ⟨subd17_0_426, List.forall_mem_cons.2 ⟨subd17_0_427, List.forall_mem_cons.2 ⟨subd17_0_428, List.forall_mem_cons.2 ⟨subd17_0_429, List.forall_mem_cons.2 ⟨subd17_0_430, List.forall_mem_cons.2 ⟨subd17_0_431, List.forall_mem_cons.2 ⟨subd17_0_432, List.forall_mem_cons.2 ⟨subd17_0_433, List.forall_mem_cons.2 ⟨subd17_0_434, List.forall_mem_cons.2 ⟨subd17_0_435, List.forall_mem_cons.2 ⟨subd17_0_436, List.forall_mem_cons.2 ⟨subd17_0_437, List.forall_mem_cons.2 ⟨subd17_0_438, List.forall_mem_cons.2 ⟨subd17_0_439, List.forall_mem_cons.2 ⟨subd17_0_440, List.forall_mem_cons.2 ⟨subd17_0_441, List.forall_mem_cons.2 ⟨subd17_0_442, List.forall_mem_cons.2 ⟨subd17_0_443, List.forall_mem_cons.2 ⟨subd17_0_444, List.forall_mem_cons.2 ⟨subd17_0_445, List.forall_mem_cons.2 ⟨subd17_0_446, List.forall_mem_cons.2 ⟨subd17_0_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_0_448 : subd17_0 [1, -1, 4] = true := by decide +kernel
theorem subd17_0_449 : subd17_0 [1, -1, 5] = true := by decide +kernel
theorem subd17_0_450 : subd17_0 [1, -1, 6] = true := by decide +kernel
theorem subd17_0_451 : subd17_0 [1, -1, 7] = true := by decide +kernel
theorem subd17_0_452 : subd17_0 [1, -1, 8] = true := by decide +kernel
theorem subd17_0_453 : subd17_0 [1, -1, 9] = true := by decide +kernel
theorem subd17_0_454 : subd17_0 [1, -1, 10] = true := by decide +kernel
theorem subd17_0_455 : subd17_0 [1, -1, 11] = true := by decide +kernel
theorem subd17_0_456 : subd17_0 [1, -1, 12] = true := by decide +kernel
theorem subd17_0_457 : subd17_0 [1, -1, 13] = true := by decide +kernel
theorem subd17_0_458 : subd17_0 [1, 0, -14] = true := by decide +kernel
theorem subd17_0_459 : subd17_0 [1, 0, -13] = true := by decide +kernel
theorem subd17_0_460 : subd17_0 [1, 0, -12] = true := by decide +kernel
theorem subd17_0_461 : subd17_0 [1, 0, -11] = true := by decide +kernel
theorem subd17_0_462 : subd17_0 [1, 0, -10] = true := by decide +kernel
theorem subd17_0_463 : subd17_0 [1, 0, -9] = true := by decide +kernel
theorem subd17_0_464 : subd17_0 [1, 0, -8] = true := by decide +kernel
theorem subd17_0_465 : subd17_0 [1, 0, -7] = true := by decide +kernel
theorem subd17_0_466 : subd17_0 [1, 0, -6] = true := by decide +kernel
theorem subd17_0_467 : subd17_0 [1, 0, -5] = true := by decide +kernel
theorem subd17_0_468 : subd17_0 [1, 0, -4] = true := by decide +kernel
theorem subd17_0_469 : subd17_0 [1, 0, -3] = true := by decide +kernel
theorem subd17_0_470 : subd17_0 [1, 0, -2] = true := by decide +kernel
theorem subd17_0_471 : subd17_0 [1, 0, -1] = true := by decide +kernel
theorem subd17_0_472 : subd17_0 [1, 0, 0] = true := by decide +kernel
theorem subd17_0_473 : subd17_0 [1, 0, 1] = true := by decide +kernel
theorem subd17_0_474 : subd17_0 [1, 0, 2] = true := by decide +kernel
theorem subd17_0_475 : subd17_0 [1, 0, 3] = true := by decide +kernel
theorem subd17_0_476 : subd17_0 [1, 0, 4] = true := by decide +kernel
theorem subd17_0_477 : subd17_0 [1, 0, 5] = true := by decide +kernel
theorem subd17_0_478 : subd17_0 [1, 0, 6] = true := by decide +kernel
theorem subd17_0_479 : subd17_0 [1, 0, 7] = true := by decide +kernel
theorem sbd17_0_14 : ∀ q ∈ blkd17_0_14, subd17_0 q = true := by
  unfold blkd17_0_14
  exact List.forall_mem_cons.2 ⟨subd17_0_448, List.forall_mem_cons.2 ⟨subd17_0_449, List.forall_mem_cons.2 ⟨subd17_0_450, List.forall_mem_cons.2 ⟨subd17_0_451, List.forall_mem_cons.2 ⟨subd17_0_452, List.forall_mem_cons.2 ⟨subd17_0_453, List.forall_mem_cons.2 ⟨subd17_0_454, List.forall_mem_cons.2 ⟨subd17_0_455, List.forall_mem_cons.2 ⟨subd17_0_456, List.forall_mem_cons.2 ⟨subd17_0_457, List.forall_mem_cons.2 ⟨subd17_0_458, List.forall_mem_cons.2 ⟨subd17_0_459, List.forall_mem_cons.2 ⟨subd17_0_460, List.forall_mem_cons.2 ⟨subd17_0_461, List.forall_mem_cons.2 ⟨subd17_0_462, List.forall_mem_cons.2 ⟨subd17_0_463, List.forall_mem_cons.2 ⟨subd17_0_464, List.forall_mem_cons.2 ⟨subd17_0_465, List.forall_mem_cons.2 ⟨subd17_0_466, List.forall_mem_cons.2 ⟨subd17_0_467, List.forall_mem_cons.2 ⟨subd17_0_468, List.forall_mem_cons.2 ⟨subd17_0_469, List.forall_mem_cons.2 ⟨subd17_0_470, List.forall_mem_cons.2 ⟨subd17_0_471, List.forall_mem_cons.2 ⟨subd17_0_472, List.forall_mem_cons.2 ⟨subd17_0_473, List.forall_mem_cons.2 ⟨subd17_0_474, List.forall_mem_cons.2 ⟨subd17_0_475, List.forall_mem_cons.2 ⟨subd17_0_476, List.forall_mem_cons.2 ⟨subd17_0_477, List.forall_mem_cons.2 ⟨subd17_0_478, List.forall_mem_cons.2 ⟨subd17_0_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_0_480 : subd17_0 [1, 0, 8] = true := by decide +kernel
theorem subd17_0_481 : subd17_0 [1, 0, 9] = true := by decide +kernel
theorem subd17_0_482 : subd17_0 [1, 0, 10] = true := by decide +kernel
theorem subd17_0_483 : subd17_0 [1, 0, 11] = true := by decide +kernel
theorem subd17_0_484 : subd17_0 [1, 0, 12] = true := by decide +kernel
theorem subd17_0_485 : subd17_0 [1, 0, 13] = true := by decide +kernel
theorem subd17_0_486 : subd17_0 [1, 0, 14] = true := by decide +kernel
theorem subd17_0_487 : subd17_0 [1, 1, -14] = true := by decide +kernel
theorem subd17_0_488 : subd17_0 [1, 1, -13] = true := by decide +kernel
theorem subd17_0_489 : subd17_0 [1, 1, -12] = true := by decide +kernel
theorem subd17_0_490 : subd17_0 [1, 1, -11] = true := by decide +kernel
theorem subd17_0_491 : subd17_0 [1, 1, -10] = true := by decide +kernel
theorem subd17_0_492 : subd17_0 [1, 1, -9] = true := by decide +kernel
theorem subd17_0_493 : subd17_0 [1, 1, -8] = true := by decide +kernel
theorem subd17_0_494 : subd17_0 [1, 1, -7] = true := by decide +kernel
theorem subd17_0_495 : subd17_0 [1, 1, -6] = true := by decide +kernel
theorem subd17_0_496 : subd17_0 [1, 1, -5] = true := by decide +kernel
theorem subd17_0_497 : subd17_0 [1, 1, -4] = true := by decide +kernel
theorem subd17_0_498 : subd17_0 [1, 1, -3] = true := by decide +kernel
theorem subd17_0_499 : subd17_0 [1, 1, -2] = true := by decide +kernel
theorem subd17_0_500 : subd17_0 [1, 1, -1] = true := by decide +kernel
theorem subd17_0_501 : subd17_0 [1, 1, 0] = true := by decide +kernel
theorem subd17_0_502 : subd17_0 [1, 1, 1] = true := by decide +kernel
theorem subd17_0_503 : subd17_0 [1, 1, 2] = true := by decide +kernel
theorem subd17_0_504 : subd17_0 [1, 1, 3] = true := by decide +kernel
theorem subd17_0_505 : subd17_0 [1, 1, 4] = true := by decide +kernel
theorem subd17_0_506 : subd17_0 [1, 1, 5] = true := by decide +kernel
theorem subd17_0_507 : subd17_0 [1, 1, 6] = true := by decide +kernel
theorem subd17_0_508 : subd17_0 [1, 1, 7] = true := by decide +kernel
theorem subd17_0_509 : subd17_0 [1, 1, 8] = true := by decide +kernel
theorem subd17_0_510 : subd17_0 [1, 1, 9] = true := by decide +kernel
theorem subd17_0_511 : subd17_0 [1, 1, 10] = true := by decide +kernel
theorem sbd17_0_15 : ∀ q ∈ blkd17_0_15, subd17_0 q = true := by
  unfold blkd17_0_15
  exact List.forall_mem_cons.2 ⟨subd17_0_480, List.forall_mem_cons.2 ⟨subd17_0_481, List.forall_mem_cons.2 ⟨subd17_0_482, List.forall_mem_cons.2 ⟨subd17_0_483, List.forall_mem_cons.2 ⟨subd17_0_484, List.forall_mem_cons.2 ⟨subd17_0_485, List.forall_mem_cons.2 ⟨subd17_0_486, List.forall_mem_cons.2 ⟨subd17_0_487, List.forall_mem_cons.2 ⟨subd17_0_488, List.forall_mem_cons.2 ⟨subd17_0_489, List.forall_mem_cons.2 ⟨subd17_0_490, List.forall_mem_cons.2 ⟨subd17_0_491, List.forall_mem_cons.2 ⟨subd17_0_492, List.forall_mem_cons.2 ⟨subd17_0_493, List.forall_mem_cons.2 ⟨subd17_0_494, List.forall_mem_cons.2 ⟨subd17_0_495, List.forall_mem_cons.2 ⟨subd17_0_496, List.forall_mem_cons.2 ⟨subd17_0_497, List.forall_mem_cons.2 ⟨subd17_0_498, List.forall_mem_cons.2 ⟨subd17_0_499, List.forall_mem_cons.2 ⟨subd17_0_500, List.forall_mem_cons.2 ⟨subd17_0_501, List.forall_mem_cons.2 ⟨subd17_0_502, List.forall_mem_cons.2 ⟨subd17_0_503, List.forall_mem_cons.2 ⟨subd17_0_504, List.forall_mem_cons.2 ⟨subd17_0_505, List.forall_mem_cons.2 ⟨subd17_0_506, List.forall_mem_cons.2 ⟨subd17_0_507, List.forall_mem_cons.2 ⟨subd17_0_508, List.forall_mem_cons.2 ⟨subd17_0_509, List.forall_mem_cons.2 ⟨subd17_0_510, List.forall_mem_cons.2 ⟨subd17_0_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_0_512 : subd17_0 [1, 1, 11] = true := by decide +kernel
theorem subd17_0_513 : subd17_0 [1, 1, 12] = true := by decide +kernel
theorem subd17_0_514 : subd17_0 [1, 1, 13] = true := by decide +kernel
theorem subd17_0_515 : subd17_0 [1, 1, 14] = true := by decide +kernel
theorem subd17_0_516 : subd17_0 [1, 2, -12] = true := by decide +kernel
theorem subd17_0_517 : subd17_0 [1, 2, -11] = true := by decide +kernel
theorem subd17_0_518 : subd17_0 [1, 2, -10] = true := by decide +kernel
theorem subd17_0_519 : subd17_0 [1, 2, -9] = true := by decide +kernel
theorem subd17_0_520 : subd17_0 [1, 2, -8] = true := by decide +kernel
theorem subd17_0_521 : subd17_0 [1, 2, -7] = true := by decide +kernel
theorem subd17_0_522 : subd17_0 [1, 2, -6] = true := by decide +kernel
theorem subd17_0_523 : subd17_0 [1, 2, -5] = true := by decide +kernel
theorem subd17_0_524 : subd17_0 [1, 2, -4] = true := by decide +kernel
theorem subd17_0_525 : subd17_0 [1, 2, -3] = true := by decide +kernel
theorem subd17_0_526 : subd17_0 [1, 2, -2] = true := by decide +kernel
theorem subd17_0_527 : subd17_0 [1, 2, -1] = true := by decide +kernel
theorem subd17_0_528 : subd17_0 [1, 2, 0] = true := by decide +kernel
theorem subd17_0_529 : subd17_0 [1, 2, 1] = true := by decide +kernel
theorem subd17_0_530 : subd17_0 [1, 2, 2] = true := by decide +kernel
theorem subd17_0_531 : subd17_0 [1, 2, 3] = true := by decide +kernel
theorem subd17_0_532 : subd17_0 [1, 2, 4] = true := by decide +kernel
theorem subd17_0_533 : subd17_0 [1, 2, 5] = true := by decide +kernel
theorem subd17_0_534 : subd17_0 [1, 2, 6] = true := by decide +kernel
theorem subd17_0_535 : subd17_0 [1, 2, 7] = true := by decide +kernel
theorem subd17_0_536 : subd17_0 [1, 2, 8] = true := by decide +kernel
theorem subd17_0_537 : subd17_0 [1, 2, 9] = true := by decide +kernel
theorem subd17_0_538 : subd17_0 [1, 2, 10] = true := by decide +kernel
theorem subd17_0_539 : subd17_0 [1, 2, 11] = true := by decide +kernel
theorem subd17_0_540 : subd17_0 [1, 2, 12] = true := by decide +kernel
theorem subd17_0_541 : subd17_0 [1, 3, -8] = true := by decide +kernel
theorem subd17_0_542 : subd17_0 [1, 3, -7] = true := by decide +kernel
theorem subd17_0_543 : subd17_0 [1, 3, -6] = true := by decide +kernel
theorem sbd17_0_16 : ∀ q ∈ blkd17_0_16, subd17_0 q = true := by
  unfold blkd17_0_16
  exact List.forall_mem_cons.2 ⟨subd17_0_512, List.forall_mem_cons.2 ⟨subd17_0_513, List.forall_mem_cons.2 ⟨subd17_0_514, List.forall_mem_cons.2 ⟨subd17_0_515, List.forall_mem_cons.2 ⟨subd17_0_516, List.forall_mem_cons.2 ⟨subd17_0_517, List.forall_mem_cons.2 ⟨subd17_0_518, List.forall_mem_cons.2 ⟨subd17_0_519, List.forall_mem_cons.2 ⟨subd17_0_520, List.forall_mem_cons.2 ⟨subd17_0_521, List.forall_mem_cons.2 ⟨subd17_0_522, List.forall_mem_cons.2 ⟨subd17_0_523, List.forall_mem_cons.2 ⟨subd17_0_524, List.forall_mem_cons.2 ⟨subd17_0_525, List.forall_mem_cons.2 ⟨subd17_0_526, List.forall_mem_cons.2 ⟨subd17_0_527, List.forall_mem_cons.2 ⟨subd17_0_528, List.forall_mem_cons.2 ⟨subd17_0_529, List.forall_mem_cons.2 ⟨subd17_0_530, List.forall_mem_cons.2 ⟨subd17_0_531, List.forall_mem_cons.2 ⟨subd17_0_532, List.forall_mem_cons.2 ⟨subd17_0_533, List.forall_mem_cons.2 ⟨subd17_0_534, List.forall_mem_cons.2 ⟨subd17_0_535, List.forall_mem_cons.2 ⟨subd17_0_536, List.forall_mem_cons.2 ⟨subd17_0_537, List.forall_mem_cons.2 ⟨subd17_0_538, List.forall_mem_cons.2 ⟨subd17_0_539, List.forall_mem_cons.2 ⟨subd17_0_540, List.forall_mem_cons.2 ⟨subd17_0_541, List.forall_mem_cons.2 ⟨subd17_0_542, List.forall_mem_cons.2 ⟨subd17_0_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_0_544 : subd17_0 [1, 3, -5] = true := by decide +kernel
theorem subd17_0_545 : subd17_0 [1, 3, -4] = true := by decide +kernel
theorem subd17_0_546 : subd17_0 [1, 3, -3] = true := by decide +kernel
theorem subd17_0_547 : subd17_0 [1, 3, -2] = true := by decide +kernel
theorem subd17_0_548 : subd17_0 [1, 3, -1] = true := by decide +kernel
theorem subd17_0_549 : subd17_0 [1, 3, 0] = true := by decide +kernel
theorem subd17_0_550 : subd17_0 [1, 3, 1] = true := by decide +kernel
theorem subd17_0_551 : subd17_0 [1, 3, 2] = true := by decide +kernel
theorem subd17_0_552 : subd17_0 [1, 3, 3] = true := by decide +kernel
theorem subd17_0_553 : subd17_0 [1, 3, 4] = true := by decide +kernel
theorem subd17_0_554 : subd17_0 [1, 3, 5] = true := by decide +kernel
theorem subd17_0_555 : subd17_0 [1, 3, 6] = true := by decide +kernel
theorem subd17_0_556 : subd17_0 [1, 3, 7] = true := by decide +kernel
theorem subd17_0_557 : subd17_0 [1, 3, 8] = true := by decide +kernel
theorem subd17_0_558 : subd17_0 [2, -2] = true := by decide +kernel
theorem subd17_0_559 : subd17_0 [2, -1, -8] = true := by decide +kernel
theorem subd17_0_560 : subd17_0 [2, -1, -7] = true := by decide +kernel
theorem subd17_0_561 : subd17_0 [2, -1, -6] = true := by decide +kernel
theorem subd17_0_562 : subd17_0 [2, -1, -5] = true := by decide +kernel
theorem subd17_0_563 : subd17_0 [2, -1, -4] = true := by decide +kernel
theorem subd17_0_564 : subd17_0 [2, -1, -3] = true := by decide +kernel
theorem subd17_0_565 : subd17_0 [2, -1, -2] = true := by decide +kernel
theorem subd17_0_566 : subd17_0 [2, -1, -1] = true := by decide +kernel
theorem subd17_0_567 : subd17_0 [2, -1, 0] = true := by decide +kernel
theorem subd17_0_568 : subd17_0 [2, -1, 1] = true := by decide +kernel
theorem subd17_0_569 : subd17_0 [2, -1, 2] = true := by decide +kernel
theorem subd17_0_570 : subd17_0 [2, -1, 3] = true := by decide +kernel
theorem subd17_0_571 : subd17_0 [2, -1, 4] = true := by decide +kernel
theorem subd17_0_572 : subd17_0 [2, -1, 5] = true := by decide +kernel
theorem subd17_0_573 : subd17_0 [2, -1, 6] = true := by decide +kernel
theorem subd17_0_574 : subd17_0 [2, -1, 7] = true := by decide +kernel
theorem subd17_0_575 : subd17_0 [2, -1, 8] = true := by decide +kernel
theorem sbd17_0_17 : ∀ q ∈ blkd17_0_17, subd17_0 q = true := by
  unfold blkd17_0_17
  exact List.forall_mem_cons.2 ⟨subd17_0_544, List.forall_mem_cons.2 ⟨subd17_0_545, List.forall_mem_cons.2 ⟨subd17_0_546, List.forall_mem_cons.2 ⟨subd17_0_547, List.forall_mem_cons.2 ⟨subd17_0_548, List.forall_mem_cons.2 ⟨subd17_0_549, List.forall_mem_cons.2 ⟨subd17_0_550, List.forall_mem_cons.2 ⟨subd17_0_551, List.forall_mem_cons.2 ⟨subd17_0_552, List.forall_mem_cons.2 ⟨subd17_0_553, List.forall_mem_cons.2 ⟨subd17_0_554, List.forall_mem_cons.2 ⟨subd17_0_555, List.forall_mem_cons.2 ⟨subd17_0_556, List.forall_mem_cons.2 ⟨subd17_0_557, List.forall_mem_cons.2 ⟨subd17_0_558, List.forall_mem_cons.2 ⟨subd17_0_559, List.forall_mem_cons.2 ⟨subd17_0_560, List.forall_mem_cons.2 ⟨subd17_0_561, List.forall_mem_cons.2 ⟨subd17_0_562, List.forall_mem_cons.2 ⟨subd17_0_563, List.forall_mem_cons.2 ⟨subd17_0_564, List.forall_mem_cons.2 ⟨subd17_0_565, List.forall_mem_cons.2 ⟨subd17_0_566, List.forall_mem_cons.2 ⟨subd17_0_567, List.forall_mem_cons.2 ⟨subd17_0_568, List.forall_mem_cons.2 ⟨subd17_0_569, List.forall_mem_cons.2 ⟨subd17_0_570, List.forall_mem_cons.2 ⟨subd17_0_571, List.forall_mem_cons.2 ⟨subd17_0_572, List.forall_mem_cons.2 ⟨subd17_0_573, List.forall_mem_cons.2 ⟨subd17_0_574, List.forall_mem_cons.2 ⟨subd17_0_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_0_576 : subd17_0 [2, -1, 9] = true := by decide +kernel
theorem subd17_0_577 : subd17_0 [2, 0, -11] = true := by decide +kernel
theorem subd17_0_578 : subd17_0 [2, 0, -10] = true := by decide +kernel
theorem subd17_0_579 : subd17_0 [2, 0, -9] = true := by decide +kernel
theorem subd17_0_580 : subd17_0 [2, 0, -8] = true := by decide +kernel
theorem subd17_0_581 : subd17_0 [2, 0, -7] = true := by decide +kernel
theorem subd17_0_582 : subd17_0 [2, 0, -6] = true := by decide +kernel
theorem subd17_0_583 : subd17_0 [2, 0, -5] = true := by decide +kernel
theorem subd17_0_584 : subd17_0 [2, 0, -4] = true := by decide +kernel
theorem subd17_0_585 : subd17_0 [2, 0, -3] = true := by decide +kernel
theorem subd17_0_586 : subd17_0 [2, 0, -2] = true := by decide +kernel
theorem subd17_0_587 : subd17_0 [2, 0, -1] = true := by decide +kernel
theorem subd17_0_588 : subd17_0 [2, 0, 0] = true := by decide +kernel
theorem subd17_0_589 : subd17_0 [2, 0, 1] = true := by decide +kernel
theorem subd17_0_590 : subd17_0 [2, 0, 2] = true := by decide +kernel
theorem subd17_0_591 : subd17_0 [2, 0, 3] = true := by decide +kernel
theorem subd17_0_592 : subd17_0 [2, 0, 4] = true := by decide +kernel
theorem subd17_0_593 : subd17_0 [2, 0, 5] = true := by decide +kernel
theorem subd17_0_594 : subd17_0 [2, 0, 6] = true := by decide +kernel
theorem subd17_0_595 : subd17_0 [2, 0, 7] = true := by decide +kernel
theorem subd17_0_596 : subd17_0 [2, 0, 8] = true := by decide +kernel
theorem subd17_0_597 : subd17_0 [2, 0, 9] = true := by decide +kernel
theorem subd17_0_598 : subd17_0 [2, 0, 10] = true := by decide +kernel
theorem subd17_0_599 : subd17_0 [2, 0, 11] = true := by decide +kernel
theorem subd17_0_600 : subd17_0 [2, 1, -11] = true := by decide +kernel
theorem subd17_0_601 : subd17_0 [2, 1, -10] = true := by decide +kernel
theorem subd17_0_602 : subd17_0 [2, 1, -9] = true := by decide +kernel
theorem subd17_0_603 : subd17_0 [2, 1, -8] = true := by decide +kernel
theorem subd17_0_604 : subd17_0 [2, 1, -7] = true := by decide +kernel
theorem subd17_0_605 : subd17_0 [2, 1, -6] = true := by decide +kernel
theorem subd17_0_606 : subd17_0 [2, 1, -5] = true := by decide +kernel
theorem subd17_0_607 : subd17_0 [2, 1, -4] = true := by decide +kernel
theorem sbd17_0_18 : ∀ q ∈ blkd17_0_18, subd17_0 q = true := by
  unfold blkd17_0_18
  exact List.forall_mem_cons.2 ⟨subd17_0_576, List.forall_mem_cons.2 ⟨subd17_0_577, List.forall_mem_cons.2 ⟨subd17_0_578, List.forall_mem_cons.2 ⟨subd17_0_579, List.forall_mem_cons.2 ⟨subd17_0_580, List.forall_mem_cons.2 ⟨subd17_0_581, List.forall_mem_cons.2 ⟨subd17_0_582, List.forall_mem_cons.2 ⟨subd17_0_583, List.forall_mem_cons.2 ⟨subd17_0_584, List.forall_mem_cons.2 ⟨subd17_0_585, List.forall_mem_cons.2 ⟨subd17_0_586, List.forall_mem_cons.2 ⟨subd17_0_587, List.forall_mem_cons.2 ⟨subd17_0_588, List.forall_mem_cons.2 ⟨subd17_0_589, List.forall_mem_cons.2 ⟨subd17_0_590, List.forall_mem_cons.2 ⟨subd17_0_591, List.forall_mem_cons.2 ⟨subd17_0_592, List.forall_mem_cons.2 ⟨subd17_0_593, List.forall_mem_cons.2 ⟨subd17_0_594, List.forall_mem_cons.2 ⟨subd17_0_595, List.forall_mem_cons.2 ⟨subd17_0_596, List.forall_mem_cons.2 ⟨subd17_0_597, List.forall_mem_cons.2 ⟨subd17_0_598, List.forall_mem_cons.2 ⟨subd17_0_599, List.forall_mem_cons.2 ⟨subd17_0_600, List.forall_mem_cons.2 ⟨subd17_0_601, List.forall_mem_cons.2 ⟨subd17_0_602, List.forall_mem_cons.2 ⟨subd17_0_603, List.forall_mem_cons.2 ⟨subd17_0_604, List.forall_mem_cons.2 ⟨subd17_0_605, List.forall_mem_cons.2 ⟨subd17_0_606, List.forall_mem_cons.2 ⟨subd17_0_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_0_608 : subd17_0 [2, 1, -3] = true := by decide +kernel
theorem subd17_0_609 : subd17_0 [2, 1, -2] = true := by decide +kernel
theorem subd17_0_610 : subd17_0 [2, 1, -1] = true := by decide +kernel
theorem subd17_0_611 : subd17_0 [2, 1, 0] = true := by decide +kernel
theorem subd17_0_612 : subd17_0 [2, 1, 1] = true := by decide +kernel
theorem subd17_0_613 : subd17_0 [2, 1, 2] = true := by decide +kernel
theorem subd17_0_614 : subd17_0 [2, 1, 3] = true := by decide +kernel
theorem subd17_0_615 : subd17_0 [2, 1, 4] = true := by decide +kernel
theorem subd17_0_616 : subd17_0 [2, 1, 5] = true := by decide +kernel
theorem subd17_0_617 : subd17_0 [2, 1, 6] = true := by decide +kernel
theorem subd17_0_618 : subd17_0 [2, 1, 7] = true := by decide +kernel
theorem subd17_0_619 : subd17_0 [2, 1, 8] = true := by decide +kernel
theorem subd17_0_620 : subd17_0 [2, 1, 9] = true := by decide +kernel
theorem subd17_0_621 : subd17_0 [2, 1, 10] = true := by decide +kernel
theorem subd17_0_622 : subd17_0 [2, 1, 11] = true := by decide +kernel
theorem subd17_0_623 : subd17_0 [2, 1, 12] = true := by decide +kernel
theorem subd17_0_624 : subd17_0 [2, 2, -10] = true := by decide +kernel
theorem subd17_0_625 : subd17_0 [2, 2, -9] = true := by decide +kernel
theorem subd17_0_626 : subd17_0 [2, 2, -8] = true := by decide +kernel
theorem subd17_0_627 : subd17_0 [2, 2, -7] = true := by decide +kernel
theorem subd17_0_628 : subd17_0 [2, 2, -6] = true := by decide +kernel
theorem subd17_0_629 : subd17_0 [2, 2, -5] = true := by decide +kernel
theorem subd17_0_630 : subd17_0 [2, 2, -4] = true := by decide +kernel
theorem subd17_0_631 : subd17_0 [2, 2, -3] = true := by decide +kernel
theorem subd17_0_632 : subd17_0 [2, 2, -2] = true := by decide +kernel
theorem subd17_0_633 : subd17_0 [2, 2, -1] = true := by decide +kernel
theorem subd17_0_634 : subd17_0 [2, 2, 0] = true := by decide +kernel
theorem subd17_0_635 : subd17_0 [2, 2, 1] = true := by decide +kernel
theorem subd17_0_636 : subd17_0 [2, 2, 2] = true := by decide +kernel
theorem subd17_0_637 : subd17_0 [2, 2, 3] = true := by decide +kernel
theorem subd17_0_638 : subd17_0 [2, 2, 4] = true := by decide +kernel
theorem subd17_0_639 : subd17_0 [2, 2, 5] = true := by decide +kernel
theorem sbd17_0_19 : ∀ q ∈ blkd17_0_19, subd17_0 q = true := by
  unfold blkd17_0_19
  exact List.forall_mem_cons.2 ⟨subd17_0_608, List.forall_mem_cons.2 ⟨subd17_0_609, List.forall_mem_cons.2 ⟨subd17_0_610, List.forall_mem_cons.2 ⟨subd17_0_611, List.forall_mem_cons.2 ⟨subd17_0_612, List.forall_mem_cons.2 ⟨subd17_0_613, List.forall_mem_cons.2 ⟨subd17_0_614, List.forall_mem_cons.2 ⟨subd17_0_615, List.forall_mem_cons.2 ⟨subd17_0_616, List.forall_mem_cons.2 ⟨subd17_0_617, List.forall_mem_cons.2 ⟨subd17_0_618, List.forall_mem_cons.2 ⟨subd17_0_619, List.forall_mem_cons.2 ⟨subd17_0_620, List.forall_mem_cons.2 ⟨subd17_0_621, List.forall_mem_cons.2 ⟨subd17_0_622, List.forall_mem_cons.2 ⟨subd17_0_623, List.forall_mem_cons.2 ⟨subd17_0_624, List.forall_mem_cons.2 ⟨subd17_0_625, List.forall_mem_cons.2 ⟨subd17_0_626, List.forall_mem_cons.2 ⟨subd17_0_627, List.forall_mem_cons.2 ⟨subd17_0_628, List.forall_mem_cons.2 ⟨subd17_0_629, List.forall_mem_cons.2 ⟨subd17_0_630, List.forall_mem_cons.2 ⟨subd17_0_631, List.forall_mem_cons.2 ⟨subd17_0_632, List.forall_mem_cons.2 ⟨subd17_0_633, List.forall_mem_cons.2 ⟨subd17_0_634, List.forall_mem_cons.2 ⟨subd17_0_635, List.forall_mem_cons.2 ⟨subd17_0_636, List.forall_mem_cons.2 ⟨subd17_0_637, List.forall_mem_cons.2 ⟨subd17_0_638, List.forall_mem_cons.2 ⟨subd17_0_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_0_640 : subd17_0 [2, 2, 6] = true := by decide +kernel
theorem subd17_0_641 : subd17_0 [2, 2, 7] = true := by decide +kernel
theorem subd17_0_642 : subd17_0 [2, 2, 8] = true := by decide +kernel
theorem subd17_0_643 : subd17_0 [2, 2, 9] = true := by decide +kernel
theorem subd17_0_644 : subd17_0 [2, 2, 10] = true := by decide +kernel
theorem subd17_0_645 : subd17_0 [2, 3] = true := by decide +kernel
theorem subd17_0_646 : subd17_0 [3] = true := by decide +kernel
theorem sbd17_0_20 : ∀ q ∈ blkd17_0_20, subd17_0 q = true := by
  unfold blkd17_0_20
  exact List.forall_mem_cons.2 ⟨subd17_0_640, List.forall_mem_cons.2 ⟨subd17_0_641, List.forall_mem_cons.2 ⟨subd17_0_642, List.forall_mem_cons.2 ⟨subd17_0_643, List.forall_mem_cons.2 ⟨subd17_0_644, List.forall_mem_cons.2 ⟨subd17_0_645, List.forall_mem_cons.2 ⟨subd17_0_646, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd17_1 : ldCheck G d17_1.U d17_1.ms ldd17_1 = true := by decide +kernel
theorem pre_okd17_1 : subPre G cell17 d17_1 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C143
