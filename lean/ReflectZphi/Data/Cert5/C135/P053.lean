import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_4_352 : subd9_4 [0, -3, -2] = true := by decide +kernel
theorem subd9_4_353 : subd9_4 [0, -3, -1] = true := by decide +kernel
theorem subd9_4_354 : subd9_4 [0, -3, 0] = true := by decide +kernel
theorem subd9_4_355 : subd9_4 [0, -3, 1] = true := by decide +kernel
theorem subd9_4_356 : subd9_4 [0, -3, 2] = true := by decide +kernel
theorem subd9_4_357 : subd9_4 [0, -3, 3] = true := by decide +kernel
theorem subd9_4_358 : subd9_4 [0, -3, 4] = true := by decide +kernel
theorem subd9_4_359 : subd9_4 [0, -3, 5] = true := by decide +kernel
theorem subd9_4_360 : subd9_4 [0, -3, 6] = true := by decide +kernel
theorem subd9_4_361 : subd9_4 [0, -2, -8] = true := by decide +kernel
theorem subd9_4_362 : subd9_4 [0, -2, -7] = true := by decide +kernel
theorem subd9_4_363 : subd9_4 [0, -2, -6] = true := by decide +kernel
theorem subd9_4_364 : subd9_4 [0, -2, -5] = true := by decide +kernel
theorem subd9_4_365 : subd9_4 [0, -2, -4] = true := by decide +kernel
theorem subd9_4_366 : subd9_4 [0, -2, -3] = true := by decide +kernel
theorem subd9_4_367 : subd9_4 [0, -2, -2] = true := by decide +kernel
theorem subd9_4_368 : subd9_4 [0, -2, -1] = true := by decide +kernel
theorem subd9_4_369 : subd9_4 [0, -2, 0] = true := by decide +kernel
theorem subd9_4_370 : subd9_4 [0, -2, 1] = true := by decide +kernel
theorem subd9_4_371 : subd9_4 [0, -2, 2] = true := by decide +kernel
theorem subd9_4_372 : subd9_4 [0, -2, 3] = true := by decide +kernel
theorem subd9_4_373 : subd9_4 [0, -2, 4] = true := by decide +kernel
theorem subd9_4_374 : subd9_4 [0, -2, 5] = true := by decide +kernel
theorem subd9_4_375 : subd9_4 [0, -2, 6] = true := by decide +kernel
theorem subd9_4_376 : subd9_4 [0, -2, 7] = true := by decide +kernel
theorem subd9_4_377 : subd9_4 [0, -1, -9] = true := by decide +kernel
theorem subd9_4_378 : subd9_4 [0, -1, -8] = true := by decide +kernel
theorem subd9_4_379 : subd9_4 [0, -1, -7] = true := by decide +kernel
theorem subd9_4_380 : subd9_4 [0, -1, -6] = true := by decide +kernel
theorem subd9_4_381 : subd9_4 [0, -1, -5] = true := by decide +kernel
theorem subd9_4_382 : subd9_4 [0, -1, -4] = true := by decide +kernel
theorem subd9_4_383 : subd9_4 [0, -1, -3] = true := by decide +kernel
theorem sbd9_4_11 : ∀ q ∈ blkd9_4_11, subd9_4 q = true := by
  unfold blkd9_4_11
  exact List.forall_mem_cons.2 ⟨subd9_4_352, List.forall_mem_cons.2 ⟨subd9_4_353, List.forall_mem_cons.2 ⟨subd9_4_354, List.forall_mem_cons.2 ⟨subd9_4_355, List.forall_mem_cons.2 ⟨subd9_4_356, List.forall_mem_cons.2 ⟨subd9_4_357, List.forall_mem_cons.2 ⟨subd9_4_358, List.forall_mem_cons.2 ⟨subd9_4_359, List.forall_mem_cons.2 ⟨subd9_4_360, List.forall_mem_cons.2 ⟨subd9_4_361, List.forall_mem_cons.2 ⟨subd9_4_362, List.forall_mem_cons.2 ⟨subd9_4_363, List.forall_mem_cons.2 ⟨subd9_4_364, List.forall_mem_cons.2 ⟨subd9_4_365, List.forall_mem_cons.2 ⟨subd9_4_366, List.forall_mem_cons.2 ⟨subd9_4_367, List.forall_mem_cons.2 ⟨subd9_4_368, List.forall_mem_cons.2 ⟨subd9_4_369, List.forall_mem_cons.2 ⟨subd9_4_370, List.forall_mem_cons.2 ⟨subd9_4_371, List.forall_mem_cons.2 ⟨subd9_4_372, List.forall_mem_cons.2 ⟨subd9_4_373, List.forall_mem_cons.2 ⟨subd9_4_374, List.forall_mem_cons.2 ⟨subd9_4_375, List.forall_mem_cons.2 ⟨subd9_4_376, List.forall_mem_cons.2 ⟨subd9_4_377, List.forall_mem_cons.2 ⟨subd9_4_378, List.forall_mem_cons.2 ⟨subd9_4_379, List.forall_mem_cons.2 ⟨subd9_4_380, List.forall_mem_cons.2 ⟨subd9_4_381, List.forall_mem_cons.2 ⟨subd9_4_382, List.forall_mem_cons.2 ⟨subd9_4_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_4_384 : subd9_4 [0, -1, -2] = true := by decide +kernel
theorem subd9_4_385 : subd9_4 [0, -1, -1] = true := by decide +kernel
theorem subd9_4_386 : subd9_4 [0, -1, 0] = true := by decide +kernel
theorem subd9_4_387 : subd9_4 [0, -1, 1] = true := by decide +kernel
theorem subd9_4_388 : subd9_4 [0, -1, 2] = true := by decide +kernel
theorem subd9_4_389 : subd9_4 [0, -1, 3] = true := by decide +kernel
theorem subd9_4_390 : subd9_4 [0, -1, 4] = true := by decide +kernel
theorem subd9_4_391 : subd9_4 [0, -1, 5] = true := by decide +kernel
theorem subd9_4_392 : subd9_4 [0, -1, 6] = true := by decide +kernel
theorem subd9_4_393 : subd9_4 [0, -1, 7] = true := by decide +kernel
theorem subd9_4_394 : subd9_4 [0, 0, -9] = true := by decide +kernel
theorem subd9_4_395 : subd9_4 [0, 0, -8] = true := by decide +kernel
theorem subd9_4_396 : subd9_4 [0, 0, -7] = true := by decide +kernel
theorem subd9_4_397 : subd9_4 [0, 0, -6] = true := by decide +kernel
theorem subd9_4_398 : subd9_4 [0, 0, -5] = true := by decide +kernel
theorem subd9_4_399 : subd9_4 [0, 0, -4] = true := by decide +kernel
theorem subd9_4_400 : subd9_4 [0, 0, -3] = true := by decide +kernel
theorem subd9_4_401 : subd9_4 [0, 0, -2] = true := by decide +kernel
theorem subd9_4_402 : subd9_4 [0, 0, -1] = true := by decide +kernel
theorem subd9_4_403 : subd9_4 [0, 0, 0] = true := by decide +kernel
theorem subd9_4_404 : subd9_4 [0, 0, 1] = true := by decide +kernel
theorem subd9_4_405 : subd9_4 [0, 0, 2] = true := by decide +kernel
theorem subd9_4_406 : subd9_4 [0, 0, 3] = true := by decide +kernel
theorem subd9_4_407 : subd9_4 [0, 0, 4] = true := by decide +kernel
theorem subd9_4_408 : subd9_4 [0, 0, 5] = true := by decide +kernel
theorem subd9_4_409 : subd9_4 [0, 0, 6] = true := by decide +kernel
theorem subd9_4_410 : subd9_4 [0, 0, 7] = true := by decide +kernel
theorem subd9_4_411 : subd9_4 [0, 0, 8] = true := by decide +kernel
theorem subd9_4_412 : subd9_4 [0, 1, -8] = true := by decide +kernel
theorem subd9_4_413 : subd9_4 [0, 1, -7] = true := by decide +kernel
theorem subd9_4_414 : subd9_4 [0, 1, -6] = true := by decide +kernel
theorem subd9_4_415 : subd9_4 [0, 1, -5] = true := by decide +kernel
theorem sbd9_4_12 : ∀ q ∈ blkd9_4_12, subd9_4 q = true := by
  unfold blkd9_4_12
  exact List.forall_mem_cons.2 ⟨subd9_4_384, List.forall_mem_cons.2 ⟨subd9_4_385, List.forall_mem_cons.2 ⟨subd9_4_386, List.forall_mem_cons.2 ⟨subd9_4_387, List.forall_mem_cons.2 ⟨subd9_4_388, List.forall_mem_cons.2 ⟨subd9_4_389, List.forall_mem_cons.2 ⟨subd9_4_390, List.forall_mem_cons.2 ⟨subd9_4_391, List.forall_mem_cons.2 ⟨subd9_4_392, List.forall_mem_cons.2 ⟨subd9_4_393, List.forall_mem_cons.2 ⟨subd9_4_394, List.forall_mem_cons.2 ⟨subd9_4_395, List.forall_mem_cons.2 ⟨subd9_4_396, List.forall_mem_cons.2 ⟨subd9_4_397, List.forall_mem_cons.2 ⟨subd9_4_398, List.forall_mem_cons.2 ⟨subd9_4_399, List.forall_mem_cons.2 ⟨subd9_4_400, List.forall_mem_cons.2 ⟨subd9_4_401, List.forall_mem_cons.2 ⟨subd9_4_402, List.forall_mem_cons.2 ⟨subd9_4_403, List.forall_mem_cons.2 ⟨subd9_4_404, List.forall_mem_cons.2 ⟨subd9_4_405, List.forall_mem_cons.2 ⟨subd9_4_406, List.forall_mem_cons.2 ⟨subd9_4_407, List.forall_mem_cons.2 ⟨subd9_4_408, List.forall_mem_cons.2 ⟨subd9_4_409, List.forall_mem_cons.2 ⟨subd9_4_410, List.forall_mem_cons.2 ⟨subd9_4_411, List.forall_mem_cons.2 ⟨subd9_4_412, List.forall_mem_cons.2 ⟨subd9_4_413, List.forall_mem_cons.2 ⟨subd9_4_414, List.forall_mem_cons.2 ⟨subd9_4_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_4_416 : subd9_4 [0, 1, -4] = true := by decide +kernel
theorem subd9_4_417 : subd9_4 [0, 1, -3] = true := by decide +kernel
theorem subd9_4_418 : subd9_4 [0, 1, -2] = true := by decide +kernel
theorem subd9_4_419 : subd9_4 [0, 1, -1] = true := by decide +kernel
theorem subd9_4_420 : subd9_4 [0, 1, 0] = true := by decide +kernel
theorem subd9_4_421 : subd9_4 [0, 1, 1] = true := by decide +kernel
theorem subd9_4_422 : subd9_4 [0, 1, 2] = true := by decide +kernel
theorem subd9_4_423 : subd9_4 [0, 1, 3] = true := by decide +kernel
theorem subd9_4_424 : subd9_4 [0, 1, 4] = true := by decide +kernel
theorem subd9_4_425 : subd9_4 [0, 1, 5] = true := by decide +kernel
theorem subd9_4_426 : subd9_4 [0, 1, 6] = true := by decide +kernel
theorem subd9_4_427 : subd9_4 [0, 1, 7] = true := by decide +kernel
theorem subd9_4_428 : subd9_4 [0, 1, 8] = true := by decide +kernel
theorem subd9_4_429 : subd9_4 [0, 2, -8] = true := by decide +kernel
theorem subd9_4_430 : subd9_4 [0, 2, -7] = true := by decide +kernel
theorem subd9_4_431 : subd9_4 [0, 2, -6] = true := by decide +kernel
theorem subd9_4_432 : subd9_4 [0, 2, -5] = true := by decide +kernel
theorem subd9_4_433 : subd9_4 [0, 2, -4] = true := by decide +kernel
theorem subd9_4_434 : subd9_4 [0, 2, -3] = true := by decide +kernel
theorem subd9_4_435 : subd9_4 [0, 2, -2] = true := by decide +kernel
theorem subd9_4_436 : subd9_4 [0, 2, -1] = true := by decide +kernel
theorem subd9_4_437 : subd9_4 [0, 2, 0] = true := by decide +kernel
theorem subd9_4_438 : subd9_4 [0, 2, 1] = true := by decide +kernel
theorem subd9_4_439 : subd9_4 [0, 2, 2] = true := by decide +kernel
theorem subd9_4_440 : subd9_4 [0, 2, 3] = true := by decide +kernel
theorem subd9_4_441 : subd9_4 [0, 2, 4] = true := by decide +kernel
theorem subd9_4_442 : subd9_4 [0, 2, 5] = true := by decide +kernel
theorem subd9_4_443 : subd9_4 [0, 2, 6] = true := by decide +kernel
theorem subd9_4_444 : subd9_4 [0, 2, 7] = true := by decide +kernel
theorem subd9_4_445 : subd9_4 [0, 3, -7] = true := by decide +kernel
theorem subd9_4_446 : subd9_4 [0, 3, -6] = true := by decide +kernel
theorem subd9_4_447 : subd9_4 [0, 3, -5] = true := by decide +kernel
theorem sbd9_4_13 : ∀ q ∈ blkd9_4_13, subd9_4 q = true := by
  unfold blkd9_4_13
  exact List.forall_mem_cons.2 ⟨subd9_4_416, List.forall_mem_cons.2 ⟨subd9_4_417, List.forall_mem_cons.2 ⟨subd9_4_418, List.forall_mem_cons.2 ⟨subd9_4_419, List.forall_mem_cons.2 ⟨subd9_4_420, List.forall_mem_cons.2 ⟨subd9_4_421, List.forall_mem_cons.2 ⟨subd9_4_422, List.forall_mem_cons.2 ⟨subd9_4_423, List.forall_mem_cons.2 ⟨subd9_4_424, List.forall_mem_cons.2 ⟨subd9_4_425, List.forall_mem_cons.2 ⟨subd9_4_426, List.forall_mem_cons.2 ⟨subd9_4_427, List.forall_mem_cons.2 ⟨subd9_4_428, List.forall_mem_cons.2 ⟨subd9_4_429, List.forall_mem_cons.2 ⟨subd9_4_430, List.forall_mem_cons.2 ⟨subd9_4_431, List.forall_mem_cons.2 ⟨subd9_4_432, List.forall_mem_cons.2 ⟨subd9_4_433, List.forall_mem_cons.2 ⟨subd9_4_434, List.forall_mem_cons.2 ⟨subd9_4_435, List.forall_mem_cons.2 ⟨subd9_4_436, List.forall_mem_cons.2 ⟨subd9_4_437, List.forall_mem_cons.2 ⟨subd9_4_438, List.forall_mem_cons.2 ⟨subd9_4_439, List.forall_mem_cons.2 ⟨subd9_4_440, List.forall_mem_cons.2 ⟨subd9_4_441, List.forall_mem_cons.2 ⟨subd9_4_442, List.forall_mem_cons.2 ⟨subd9_4_443, List.forall_mem_cons.2 ⟨subd9_4_444, List.forall_mem_cons.2 ⟨subd9_4_445, List.forall_mem_cons.2 ⟨subd9_4_446, List.forall_mem_cons.2 ⟨subd9_4_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_4_448 : subd9_4 [0, 3, -4] = true := by decide +kernel
theorem subd9_4_449 : subd9_4 [0, 3, -3] = true := by decide +kernel
theorem subd9_4_450 : subd9_4 [0, 3, -2] = true := by decide +kernel
theorem subd9_4_451 : subd9_4 [0, 3, -1] = true := by decide +kernel
theorem subd9_4_452 : subd9_4 [0, 3, 0] = true := by decide +kernel
theorem subd9_4_453 : subd9_4 [0, 3, 1] = true := by decide +kernel
theorem subd9_4_454 : subd9_4 [0, 3, 2] = true := by decide +kernel
theorem subd9_4_455 : subd9_4 [0, 3, 3] = true := by decide +kernel
theorem subd9_4_456 : subd9_4 [0, 3, 4] = true := by decide +kernel
theorem subd9_4_457 : subd9_4 [0, 3, 5] = true := by decide +kernel
theorem subd9_4_458 : subd9_4 [0, 3, 6] = true := by decide +kernel
theorem subd9_4_459 : subd9_4 [0, 3, 7] = true := by decide +kernel
theorem subd9_4_460 : subd9_4 [0, 4] = true := by decide +kernel
theorem subd9_4_461 : subd9_4 [0, 5] = true := by decide +kernel
theorem subd9_4_462 : subd9_4 [0, 6] = true := by decide +kernel
theorem subd9_4_463 : subd9_4 [1, -7] = true := by decide +kernel
theorem subd9_4_464 : subd9_4 [1, -6] = true := by decide +kernel
theorem subd9_4_465 : subd9_4 [1, -5] = true := by decide +kernel
theorem subd9_4_466 : subd9_4 [1, -4] = true := by decide +kernel
theorem subd9_4_467 : subd9_4 [1, -3, -7] = true := by decide +kernel
theorem subd9_4_468 : subd9_4 [1, -3, -6] = true := by decide +kernel
theorem subd9_4_469 : subd9_4 [1, -3, -5] = true := by decide +kernel
theorem subd9_4_470 : subd9_4 [1, -3, -4] = true := by decide +kernel
theorem subd9_4_471 : subd9_4 [1, -3, -3] = true := by decide +kernel
theorem subd9_4_472 : subd9_4 [1, -3, -2] = true := by decide +kernel
theorem subd9_4_473 : subd9_4 [1, -3, -1] = true := by decide +kernel
theorem subd9_4_474 : subd9_4 [1, -3, 0] = true := by decide +kernel
theorem subd9_4_475 : subd9_4 [1, -3, 1] = true := by decide +kernel
theorem subd9_4_476 : subd9_4 [1, -3, 2] = true := by decide +kernel
theorem subd9_4_477 : subd9_4 [1, -3, 3] = true := by decide +kernel
theorem subd9_4_478 : subd9_4 [1, -3, 4] = true := by decide +kernel
theorem subd9_4_479 : subd9_4 [1, -3, 5] = true := by decide +kernel
theorem sbd9_4_14 : ∀ q ∈ blkd9_4_14, subd9_4 q = true := by
  unfold blkd9_4_14
  exact List.forall_mem_cons.2 ⟨subd9_4_448, List.forall_mem_cons.2 ⟨subd9_4_449, List.forall_mem_cons.2 ⟨subd9_4_450, List.forall_mem_cons.2 ⟨subd9_4_451, List.forall_mem_cons.2 ⟨subd9_4_452, List.forall_mem_cons.2 ⟨subd9_4_453, List.forall_mem_cons.2 ⟨subd9_4_454, List.forall_mem_cons.2 ⟨subd9_4_455, List.forall_mem_cons.2 ⟨subd9_4_456, List.forall_mem_cons.2 ⟨subd9_4_457, List.forall_mem_cons.2 ⟨subd9_4_458, List.forall_mem_cons.2 ⟨subd9_4_459, List.forall_mem_cons.2 ⟨subd9_4_460, List.forall_mem_cons.2 ⟨subd9_4_461, List.forall_mem_cons.2 ⟨subd9_4_462, List.forall_mem_cons.2 ⟨subd9_4_463, List.forall_mem_cons.2 ⟨subd9_4_464, List.forall_mem_cons.2 ⟨subd9_4_465, List.forall_mem_cons.2 ⟨subd9_4_466, List.forall_mem_cons.2 ⟨subd9_4_467, List.forall_mem_cons.2 ⟨subd9_4_468, List.forall_mem_cons.2 ⟨subd9_4_469, List.forall_mem_cons.2 ⟨subd9_4_470, List.forall_mem_cons.2 ⟨subd9_4_471, List.forall_mem_cons.2 ⟨subd9_4_472, List.forall_mem_cons.2 ⟨subd9_4_473, List.forall_mem_cons.2 ⟨subd9_4_474, List.forall_mem_cons.2 ⟨subd9_4_475, List.forall_mem_cons.2 ⟨subd9_4_476, List.forall_mem_cons.2 ⟨subd9_4_477, List.forall_mem_cons.2 ⟨subd9_4_478, List.forall_mem_cons.2 ⟨subd9_4_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_4_480 : subd9_4 [1, -3, 6] = true := by decide +kernel
theorem subd9_4_481 : subd9_4 [1, -3, 7] = true := by decide +kernel
theorem subd9_4_482 : subd9_4 [1, -2, -8] = true := by decide +kernel
theorem subd9_4_483 : subd9_4 [1, -2, -7] = true := by decide +kernel
theorem subd9_4_484 : subd9_4 [1, -2, -6] = true := by decide +kernel
theorem subd9_4_485 : subd9_4 [1, -2, -5] = true := by decide +kernel
theorem subd9_4_486 : subd9_4 [1, -2, -4] = true := by decide +kernel
theorem subd9_4_487 : subd9_4 [1, -2, -3] = true := by decide +kernel
theorem subd9_4_488 : subd9_4 [1, -2, -2] = true := by decide +kernel
theorem subd9_4_489 : subd9_4 [1, -2, -1] = true := by decide +kernel
theorem subd9_4_490 : subd9_4 [1, -2, 0] = true := by decide +kernel
theorem subd9_4_491 : subd9_4 [1, -2, 1] = true := by decide +kernel
theorem subd9_4_492 : subd9_4 [1, -2, 2] = true := by decide +kernel
theorem subd9_4_493 : subd9_4 [1, -2, 3] = true := by decide +kernel
theorem subd9_4_494 : subd9_4 [1, -2, 4] = true := by decide +kernel
theorem subd9_4_495 : subd9_4 [1, -2, 5] = true := by decide +kernel
theorem subd9_4_496 : subd9_4 [1, -2, 6] = true := by decide +kernel
theorem subd9_4_497 : subd9_4 [1, -2, 7] = true := by decide +kernel
theorem subd9_4_498 : subd9_4 [1, -1, -8] = true := by decide +kernel
theorem subd9_4_499 : subd9_4 [1, -1, -7] = true := by decide +kernel
theorem subd9_4_500 : subd9_4 [1, -1, -6] = true := by decide +kernel
theorem subd9_4_501 : subd9_4 [1, -1, -5] = true := by decide +kernel
theorem subd9_4_502 : subd9_4 [1, -1, -4] = true := by decide +kernel
theorem subd9_4_503 : subd9_4 [1, -1, -3] = true := by decide +kernel
theorem subd9_4_504 : subd9_4 [1, -1, -2] = true := by decide +kernel
theorem subd9_4_505 : subd9_4 [1, -1, -1] = true := by decide +kernel
theorem subd9_4_506 : subd9_4 [1, -1, 0] = true := by decide +kernel
theorem subd9_4_507 : subd9_4 [1, -1, 1] = true := by decide +kernel
theorem subd9_4_508 : subd9_4 [1, -1, 2] = true := by decide +kernel
theorem subd9_4_509 : subd9_4 [1, -1, 3] = true := by decide +kernel
theorem subd9_4_510 : subd9_4 [1, -1, 4] = true := by decide +kernel
theorem subd9_4_511 : subd9_4 [1, -1, 5] = true := by decide +kernel
theorem sbd9_4_15 : ∀ q ∈ blkd9_4_15, subd9_4 q = true := by
  unfold blkd9_4_15
  exact List.forall_mem_cons.2 ⟨subd9_4_480, List.forall_mem_cons.2 ⟨subd9_4_481, List.forall_mem_cons.2 ⟨subd9_4_482, List.forall_mem_cons.2 ⟨subd9_4_483, List.forall_mem_cons.2 ⟨subd9_4_484, List.forall_mem_cons.2 ⟨subd9_4_485, List.forall_mem_cons.2 ⟨subd9_4_486, List.forall_mem_cons.2 ⟨subd9_4_487, List.forall_mem_cons.2 ⟨subd9_4_488, List.forall_mem_cons.2 ⟨subd9_4_489, List.forall_mem_cons.2 ⟨subd9_4_490, List.forall_mem_cons.2 ⟨subd9_4_491, List.forall_mem_cons.2 ⟨subd9_4_492, List.forall_mem_cons.2 ⟨subd9_4_493, List.forall_mem_cons.2 ⟨subd9_4_494, List.forall_mem_cons.2 ⟨subd9_4_495, List.forall_mem_cons.2 ⟨subd9_4_496, List.forall_mem_cons.2 ⟨subd9_4_497, List.forall_mem_cons.2 ⟨subd9_4_498, List.forall_mem_cons.2 ⟨subd9_4_499, List.forall_mem_cons.2 ⟨subd9_4_500, List.forall_mem_cons.2 ⟨subd9_4_501, List.forall_mem_cons.2 ⟨subd9_4_502, List.forall_mem_cons.2 ⟨subd9_4_503, List.forall_mem_cons.2 ⟨subd9_4_504, List.forall_mem_cons.2 ⟨subd9_4_505, List.forall_mem_cons.2 ⟨subd9_4_506, List.forall_mem_cons.2 ⟨subd9_4_507, List.forall_mem_cons.2 ⟨subd9_4_508, List.forall_mem_cons.2 ⟨subd9_4_509, List.forall_mem_cons.2 ⟨subd9_4_510, List.forall_mem_cons.2 ⟨subd9_4_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_4_512 : subd9_4 [1, -1, 6] = true := by decide +kernel
theorem subd9_4_513 : subd9_4 [1, -1, 7] = true := by decide +kernel
theorem subd9_4_514 : subd9_4 [1, -1, 8] = true := by decide +kernel
theorem subd9_4_515 : subd9_4 [1, 0, -8] = true := by decide +kernel
theorem subd9_4_516 : subd9_4 [1, 0, -7] = true := by decide +kernel
theorem subd9_4_517 : subd9_4 [1, 0, -6] = true := by decide +kernel
theorem subd9_4_518 : subd9_4 [1, 0, -5] = true := by decide +kernel
theorem subd9_4_519 : subd9_4 [1, 0, -4] = true := by decide +kernel
theorem subd9_4_520 : subd9_4 [1, 0, -3] = true := by decide +kernel
theorem subd9_4_521 : subd9_4 [1, 0, -2] = true := by decide +kernel
theorem subd9_4_522 : subd9_4 [1, 0, -1] = true := by decide +kernel
theorem subd9_4_523 : subd9_4 [1, 0, 0] = true := by decide +kernel
theorem subd9_4_524 : subd9_4 [1, 0, 1] = true := by decide +kernel
theorem subd9_4_525 : subd9_4 [1, 0, 2] = true := by decide +kernel
theorem subd9_4_526 : subd9_4 [1, 0, 3] = true := by decide +kernel
theorem subd9_4_527 : subd9_4 [1, 0, 4] = true := by decide +kernel
theorem subd9_4_528 : subd9_4 [1, 0, 5] = true := by decide +kernel
theorem subd9_4_529 : subd9_4 [1, 0, 6] = true := by decide +kernel
theorem subd9_4_530 : subd9_4 [1, 0, 7] = true := by decide +kernel
theorem subd9_4_531 : subd9_4 [1, 0, 8] = true := by decide +kernel
theorem subd9_4_532 : subd9_4 [1, 1, -8] = true := by decide +kernel
theorem subd9_4_533 : subd9_4 [1, 1, -7] = true := by decide +kernel
theorem subd9_4_534 : subd9_4 [1, 1, -6] = true := by decide +kernel
theorem subd9_4_535 : subd9_4 [1, 1, -5] = true := by decide +kernel
theorem subd9_4_536 : subd9_4 [1, 1, -4] = true := by decide +kernel
theorem subd9_4_537 : subd9_4 [1, 1, -3] = true := by decide +kernel
theorem subd9_4_538 : subd9_4 [1, 1, -2] = true := by decide +kernel
theorem subd9_4_539 : subd9_4 [1, 1, -1] = true := by decide +kernel
theorem subd9_4_540 : subd9_4 [1, 1, 0] = true := by decide +kernel
theorem subd9_4_541 : subd9_4 [1, 1, 1] = true := by decide +kernel
theorem subd9_4_542 : subd9_4 [1, 1, 2] = true := by decide +kernel
theorem subd9_4_543 : subd9_4 [1, 1, 3] = true := by decide +kernel
theorem sbd9_4_16 : ∀ q ∈ blkd9_4_16, subd9_4 q = true := by
  unfold blkd9_4_16
  exact List.forall_mem_cons.2 ⟨subd9_4_512, List.forall_mem_cons.2 ⟨subd9_4_513, List.forall_mem_cons.2 ⟨subd9_4_514, List.forall_mem_cons.2 ⟨subd9_4_515, List.forall_mem_cons.2 ⟨subd9_4_516, List.forall_mem_cons.2 ⟨subd9_4_517, List.forall_mem_cons.2 ⟨subd9_4_518, List.forall_mem_cons.2 ⟨subd9_4_519, List.forall_mem_cons.2 ⟨subd9_4_520, List.forall_mem_cons.2 ⟨subd9_4_521, List.forall_mem_cons.2 ⟨subd9_4_522, List.forall_mem_cons.2 ⟨subd9_4_523, List.forall_mem_cons.2 ⟨subd9_4_524, List.forall_mem_cons.2 ⟨subd9_4_525, List.forall_mem_cons.2 ⟨subd9_4_526, List.forall_mem_cons.2 ⟨subd9_4_527, List.forall_mem_cons.2 ⟨subd9_4_528, List.forall_mem_cons.2 ⟨subd9_4_529, List.forall_mem_cons.2 ⟨subd9_4_530, List.forall_mem_cons.2 ⟨subd9_4_531, List.forall_mem_cons.2 ⟨subd9_4_532, List.forall_mem_cons.2 ⟨subd9_4_533, List.forall_mem_cons.2 ⟨subd9_4_534, List.forall_mem_cons.2 ⟨subd9_4_535, List.forall_mem_cons.2 ⟨subd9_4_536, List.forall_mem_cons.2 ⟨subd9_4_537, List.forall_mem_cons.2 ⟨subd9_4_538, List.forall_mem_cons.2 ⟨subd9_4_539, List.forall_mem_cons.2 ⟨subd9_4_540, List.forall_mem_cons.2 ⟨subd9_4_541, List.forall_mem_cons.2 ⟨subd9_4_542, List.forall_mem_cons.2 ⟨subd9_4_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_4_544 : subd9_4 [1, 1, 4] = true := by decide +kernel
theorem subd9_4_545 : subd9_4 [1, 1, 5] = true := by decide +kernel
theorem subd9_4_546 : subd9_4 [1, 1, 6] = true := by decide +kernel
theorem subd9_4_547 : subd9_4 [1, 1, 7] = true := by decide +kernel
theorem subd9_4_548 : subd9_4 [1, 1, 8] = true := by decide +kernel
theorem subd9_4_549 : subd9_4 [1, 2, -8] = true := by decide +kernel
theorem subd9_4_550 : subd9_4 [1, 2, -7] = true := by decide +kernel
theorem subd9_4_551 : subd9_4 [1, 2, -6] = true := by decide +kernel
theorem subd9_4_552 : subd9_4 [1, 2, -5] = true := by decide +kernel
theorem subd9_4_553 : subd9_4 [1, 2, -4] = true := by decide +kernel
theorem subd9_4_554 : subd9_4 [1, 2, -3] = true := by decide +kernel
theorem subd9_4_555 : subd9_4 [1, 2, -2] = true := by decide +kernel
theorem subd9_4_556 : subd9_4 [1, 2, -1] = true := by decide +kernel
theorem subd9_4_557 : subd9_4 [1, 2, 0] = true := by decide +kernel
theorem subd9_4_558 : subd9_4 [1, 2, 1] = true := by decide +kernel
theorem subd9_4_559 : subd9_4 [1, 2, 2] = true := by decide +kernel
theorem subd9_4_560 : subd9_4 [1, 2, 3] = true := by decide +kernel
theorem subd9_4_561 : subd9_4 [1, 2, 4] = true := by decide +kernel
theorem subd9_4_562 : subd9_4 [1, 2, 5] = true := by decide +kernel
theorem subd9_4_563 : subd9_4 [1, 2, 6] = true := by decide +kernel
theorem subd9_4_564 : subd9_4 [1, 2, 7] = true := by decide +kernel
theorem subd9_4_565 : subd9_4 [1, 2, 8] = true := by decide +kernel
theorem subd9_4_566 : subd9_4 [1, 3, -7] = true := by decide +kernel
theorem subd9_4_567 : subd9_4 [1, 3, -6] = true := by decide +kernel
theorem subd9_4_568 : subd9_4 [1, 3, -5] = true := by decide +kernel
theorem subd9_4_569 : subd9_4 [1, 3, -4] = true := by decide +kernel
theorem subd9_4_570 : subd9_4 [1, 3, -3] = true := by decide +kernel
theorem subd9_4_571 : subd9_4 [1, 3, -2] = true := by decide +kernel
theorem subd9_4_572 : subd9_4 [1, 3, -1] = true := by decide +kernel
theorem subd9_4_573 : subd9_4 [1, 3, 0] = true := by decide +kernel
theorem subd9_4_574 : subd9_4 [1, 3, 1] = true := by decide +kernel
theorem subd9_4_575 : subd9_4 [1, 3, 2] = true := by decide +kernel
theorem sbd9_4_17 : ∀ q ∈ blkd9_4_17, subd9_4 q = true := by
  unfold blkd9_4_17
  exact List.forall_mem_cons.2 ⟨subd9_4_544, List.forall_mem_cons.2 ⟨subd9_4_545, List.forall_mem_cons.2 ⟨subd9_4_546, List.forall_mem_cons.2 ⟨subd9_4_547, List.forall_mem_cons.2 ⟨subd9_4_548, List.forall_mem_cons.2 ⟨subd9_4_549, List.forall_mem_cons.2 ⟨subd9_4_550, List.forall_mem_cons.2 ⟨subd9_4_551, List.forall_mem_cons.2 ⟨subd9_4_552, List.forall_mem_cons.2 ⟨subd9_4_553, List.forall_mem_cons.2 ⟨subd9_4_554, List.forall_mem_cons.2 ⟨subd9_4_555, List.forall_mem_cons.2 ⟨subd9_4_556, List.forall_mem_cons.2 ⟨subd9_4_557, List.forall_mem_cons.2 ⟨subd9_4_558, List.forall_mem_cons.2 ⟨subd9_4_559, List.forall_mem_cons.2 ⟨subd9_4_560, List.forall_mem_cons.2 ⟨subd9_4_561, List.forall_mem_cons.2 ⟨subd9_4_562, List.forall_mem_cons.2 ⟨subd9_4_563, List.forall_mem_cons.2 ⟨subd9_4_564, List.forall_mem_cons.2 ⟨subd9_4_565, List.forall_mem_cons.2 ⟨subd9_4_566, List.forall_mem_cons.2 ⟨subd9_4_567, List.forall_mem_cons.2 ⟨subd9_4_568, List.forall_mem_cons.2 ⟨subd9_4_569, List.forall_mem_cons.2 ⟨subd9_4_570, List.forall_mem_cons.2 ⟨subd9_4_571, List.forall_mem_cons.2 ⟨subd9_4_572, List.forall_mem_cons.2 ⟨subd9_4_573, List.forall_mem_cons.2 ⟨subd9_4_574, List.forall_mem_cons.2 ⟨subd9_4_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_4_576 : subd9_4 [1, 3, 3] = true := by decide +kernel
theorem subd9_4_577 : subd9_4 [1, 3, 4] = true := by decide +kernel
theorem subd9_4_578 : subd9_4 [1, 3, 5] = true := by decide +kernel
theorem subd9_4_579 : subd9_4 [1, 3, 6] = true := by decide +kernel
theorem subd9_4_580 : subd9_4 [1, 3, 7] = true := by decide +kernel
theorem subd9_4_581 : subd9_4 [1, 4] = true := by decide +kernel
theorem subd9_4_582 : subd9_4 [1, 5] = true := by decide +kernel
theorem subd9_4_583 : subd9_4 [1, 6] = true := by decide +kernel
theorem subd9_4_584 : subd9_4 [2, -7] = true := by decide +kernel
theorem subd9_4_585 : subd9_4 [2, -6] = true := by decide +kernel
theorem subd9_4_586 : subd9_4 [2, -5] = true := by decide +kernel
theorem subd9_4_587 : subd9_4 [2, -4] = true := by decide +kernel
theorem subd9_4_588 : subd9_4 [2, -3, -7] = true := by decide +kernel
theorem subd9_4_589 : subd9_4 [2, -3, -6] = true := by decide +kernel
theorem subd9_4_590 : subd9_4 [2, -3, -5] = true := by decide +kernel
theorem subd9_4_591 : subd9_4 [2, -3, -4] = true := by decide +kernel
theorem subd9_4_592 : subd9_4 [2, -3, -3] = true := by decide +kernel
theorem subd9_4_593 : subd9_4 [2, -3, -2] = true := by decide +kernel
theorem subd9_4_594 : subd9_4 [2, -3, -1] = true := by decide +kernel
theorem subd9_4_595 : subd9_4 [2, -3, 0] = true := by decide +kernel
theorem subd9_4_596 : subd9_4 [2, -3, 1] = true := by decide +kernel
theorem subd9_4_597 : subd9_4 [2, -3, 2] = true := by decide +kernel
theorem subd9_4_598 : subd9_4 [2, -3, 3] = true := by decide +kernel
theorem subd9_4_599 : subd9_4 [2, -3, 4] = true := by decide +kernel
theorem subd9_4_600 : subd9_4 [2, -3, 5] = true := by decide +kernel
theorem subd9_4_601 : subd9_4 [2, -3, 6] = true := by decide +kernel
theorem subd9_4_602 : subd9_4 [2, -3, 7] = true := by decide +kernel
theorem subd9_4_603 : subd9_4 [2, -2, -7] = true := by decide +kernel
theorem subd9_4_604 : subd9_4 [2, -2, -6] = true := by decide +kernel
theorem subd9_4_605 : subd9_4 [2, -2, -5] = true := by decide +kernel
theorem subd9_4_606 : subd9_4 [2, -2, -4] = true := by decide +kernel
theorem subd9_4_607 : subd9_4 [2, -2, -3] = true := by decide +kernel
theorem sbd9_4_18 : ∀ q ∈ blkd9_4_18, subd9_4 q = true := by
  unfold blkd9_4_18
  exact List.forall_mem_cons.2 ⟨subd9_4_576, List.forall_mem_cons.2 ⟨subd9_4_577, List.forall_mem_cons.2 ⟨subd9_4_578, List.forall_mem_cons.2 ⟨subd9_4_579, List.forall_mem_cons.2 ⟨subd9_4_580, List.forall_mem_cons.2 ⟨subd9_4_581, List.forall_mem_cons.2 ⟨subd9_4_582, List.forall_mem_cons.2 ⟨subd9_4_583, List.forall_mem_cons.2 ⟨subd9_4_584, List.forall_mem_cons.2 ⟨subd9_4_585, List.forall_mem_cons.2 ⟨subd9_4_586, List.forall_mem_cons.2 ⟨subd9_4_587, List.forall_mem_cons.2 ⟨subd9_4_588, List.forall_mem_cons.2 ⟨subd9_4_589, List.forall_mem_cons.2 ⟨subd9_4_590, List.forall_mem_cons.2 ⟨subd9_4_591, List.forall_mem_cons.2 ⟨subd9_4_592, List.forall_mem_cons.2 ⟨subd9_4_593, List.forall_mem_cons.2 ⟨subd9_4_594, List.forall_mem_cons.2 ⟨subd9_4_595, List.forall_mem_cons.2 ⟨subd9_4_596, List.forall_mem_cons.2 ⟨subd9_4_597, List.forall_mem_cons.2 ⟨subd9_4_598, List.forall_mem_cons.2 ⟨subd9_4_599, List.forall_mem_cons.2 ⟨subd9_4_600, List.forall_mem_cons.2 ⟨subd9_4_601, List.forall_mem_cons.2 ⟨subd9_4_602, List.forall_mem_cons.2 ⟨subd9_4_603, List.forall_mem_cons.2 ⟨subd9_4_604, List.forall_mem_cons.2 ⟨subd9_4_605, List.forall_mem_cons.2 ⟨subd9_4_606, List.forall_mem_cons.2 ⟨subd9_4_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_4_608 : subd9_4 [2, -2, -2] = true := by decide +kernel
theorem subd9_4_609 : subd9_4 [2, -2, -1] = true := by decide +kernel
theorem subd9_4_610 : subd9_4 [2, -2, 0] = true := by decide +kernel
theorem subd9_4_611 : subd9_4 [2, -2, 1] = true := by decide +kernel
theorem subd9_4_612 : subd9_4 [2, -2, 2] = true := by decide +kernel
theorem subd9_4_613 : subd9_4 [2, -2, 3] = true := by decide +kernel
theorem subd9_4_614 : subd9_4 [2, -2, 4] = true := by decide +kernel
theorem subd9_4_615 : subd9_4 [2, -2, 5] = true := by decide +kernel
theorem subd9_4_616 : subd9_4 [2, -2, 6] = true := by decide +kernel
theorem subd9_4_617 : subd9_4 [2, -2, 7] = true := by decide +kernel
theorem subd9_4_618 : subd9_4 [2, -1, -7] = true := by decide +kernel
theorem subd9_4_619 : subd9_4 [2, -1, -6] = true := by decide +kernel
theorem subd9_4_620 : subd9_4 [2, -1, -5] = true := by decide +kernel
theorem subd9_4_621 : subd9_4 [2, -1, -4] = true := by decide +kernel
theorem subd9_4_622 : subd9_4 [2, -1, -3] = true := by decide +kernel
theorem subd9_4_623 : subd9_4 [2, -1, -2] = true := by decide +kernel
theorem subd9_4_624 : subd9_4 [2, -1, -1] = true := by decide +kernel
theorem subd9_4_625 : subd9_4 [2, -1, 0] = true := by decide +kernel
theorem subd9_4_626 : subd9_4 [2, -1, 1] = true := by decide +kernel
theorem subd9_4_627 : subd9_4 [2, -1, 2] = true := by decide +kernel
theorem subd9_4_628 : subd9_4 [2, -1, 3] = true := by decide +kernel
theorem subd9_4_629 : subd9_4 [2, -1, 4] = true := by decide +kernel
theorem subd9_4_630 : subd9_4 [2, -1, 5] = true := by decide +kernel
theorem subd9_4_631 : subd9_4 [2, -1, 6] = true := by decide +kernel
theorem subd9_4_632 : subd9_4 [2, -1, 7] = true := by decide +kernel
theorem subd9_4_633 : subd9_4 [2, -1, 8] = true := by decide +kernel
theorem subd9_4_634 : subd9_4 [2, 0, -7] = true := by decide +kernel
theorem subd9_4_635 : subd9_4 [2, 0, -6] = true := by decide +kernel
theorem subd9_4_636 : subd9_4 [2, 0, -5] = true := by decide +kernel
theorem subd9_4_637 : subd9_4 [2, 0, -4] = true := by decide +kernel
theorem subd9_4_638 : subd9_4 [2, 0, -3] = true := by decide +kernel
theorem subd9_4_639 : subd9_4 [2, 0, -2] = true := by decide +kernel
theorem sbd9_4_19 : ∀ q ∈ blkd9_4_19, subd9_4 q = true := by
  unfold blkd9_4_19
  exact List.forall_mem_cons.2 ⟨subd9_4_608, List.forall_mem_cons.2 ⟨subd9_4_609, List.forall_mem_cons.2 ⟨subd9_4_610, List.forall_mem_cons.2 ⟨subd9_4_611, List.forall_mem_cons.2 ⟨subd9_4_612, List.forall_mem_cons.2 ⟨subd9_4_613, List.forall_mem_cons.2 ⟨subd9_4_614, List.forall_mem_cons.2 ⟨subd9_4_615, List.forall_mem_cons.2 ⟨subd9_4_616, List.forall_mem_cons.2 ⟨subd9_4_617, List.forall_mem_cons.2 ⟨subd9_4_618, List.forall_mem_cons.2 ⟨subd9_4_619, List.forall_mem_cons.2 ⟨subd9_4_620, List.forall_mem_cons.2 ⟨subd9_4_621, List.forall_mem_cons.2 ⟨subd9_4_622, List.forall_mem_cons.2 ⟨subd9_4_623, List.forall_mem_cons.2 ⟨subd9_4_624, List.forall_mem_cons.2 ⟨subd9_4_625, List.forall_mem_cons.2 ⟨subd9_4_626, List.forall_mem_cons.2 ⟨subd9_4_627, List.forall_mem_cons.2 ⟨subd9_4_628, List.forall_mem_cons.2 ⟨subd9_4_629, List.forall_mem_cons.2 ⟨subd9_4_630, List.forall_mem_cons.2 ⟨subd9_4_631, List.forall_mem_cons.2 ⟨subd9_4_632, List.forall_mem_cons.2 ⟨subd9_4_633, List.forall_mem_cons.2 ⟨subd9_4_634, List.forall_mem_cons.2 ⟨subd9_4_635, List.forall_mem_cons.2 ⟨subd9_4_636, List.forall_mem_cons.2 ⟨subd9_4_637, List.forall_mem_cons.2 ⟨subd9_4_638, List.forall_mem_cons.2 ⟨subd9_4_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_4_640 : subd9_4 [2, 0, -1] = true := by decide +kernel
theorem subd9_4_641 : subd9_4 [2, 0, 0] = true := by decide +kernel
theorem subd9_4_642 : subd9_4 [2, 0, 1] = true := by decide +kernel
theorem subd9_4_643 : subd9_4 [2, 0, 2] = true := by decide +kernel
theorem subd9_4_644 : subd9_4 [2, 0, 3] = true := by decide +kernel
theorem subd9_4_645 : subd9_4 [2, 0, 4] = true := by decide +kernel
theorem subd9_4_646 : subd9_4 [2, 0, 5] = true := by decide +kernel
theorem subd9_4_647 : subd9_4 [2, 0, 6] = true := by decide +kernel
theorem subd9_4_648 : subd9_4 [2, 0, 7] = true := by decide +kernel
theorem subd9_4_649 : subd9_4 [2, 0, 8] = true := by decide +kernel
theorem subd9_4_650 : subd9_4 [2, 1, -7] = true := by decide +kernel
theorem subd9_4_651 : subd9_4 [2, 1, -6] = true := by decide +kernel
theorem subd9_4_652 : subd9_4 [2, 1, -5] = true := by decide +kernel
theorem subd9_4_653 : subd9_4 [2, 1, -4] = true := by decide +kernel
theorem subd9_4_654 : subd9_4 [2, 1, -3] = true := by decide +kernel
theorem subd9_4_655 : subd9_4 [2, 1, -2] = true := by decide +kernel
theorem subd9_4_656 : subd9_4 [2, 1, -1] = true := by decide +kernel
theorem subd9_4_657 : subd9_4 [2, 1, 0] = true := by decide +kernel
theorem subd9_4_658 : subd9_4 [2, 1, 1] = true := by decide +kernel
theorem subd9_4_659 : subd9_4 [2, 1, 2] = true := by decide +kernel
theorem subd9_4_660 : subd9_4 [2, 1, 3] = true := by decide +kernel
theorem subd9_4_661 : subd9_4 [2, 1, 4] = true := by decide +kernel
theorem subd9_4_662 : subd9_4 [2, 1, 5] = true := by decide +kernel
theorem subd9_4_663 : subd9_4 [2, 1, 6] = true := by decide +kernel
theorem subd9_4_664 : subd9_4 [2, 1, 7] = true := by decide +kernel
theorem subd9_4_665 : subd9_4 [2, 1, 8] = true := by decide +kernel
theorem subd9_4_666 : subd9_4 [2, 2, -7] = true := by decide +kernel
theorem subd9_4_667 : subd9_4 [2, 2, -6] = true := by decide +kernel
theorem subd9_4_668 : subd9_4 [2, 2, -5] = true := by decide +kernel
theorem subd9_4_669 : subd9_4 [2, 2, -4] = true := by decide +kernel
theorem subd9_4_670 : subd9_4 [2, 2, -3] = true := by decide +kernel
theorem subd9_4_671 : subd9_4 [2, 2, -2] = true := by decide +kernel
theorem sbd9_4_20 : ∀ q ∈ blkd9_4_20, subd9_4 q = true := by
  unfold blkd9_4_20
  exact List.forall_mem_cons.2 ⟨subd9_4_640, List.forall_mem_cons.2 ⟨subd9_4_641, List.forall_mem_cons.2 ⟨subd9_4_642, List.forall_mem_cons.2 ⟨subd9_4_643, List.forall_mem_cons.2 ⟨subd9_4_644, List.forall_mem_cons.2 ⟨subd9_4_645, List.forall_mem_cons.2 ⟨subd9_4_646, List.forall_mem_cons.2 ⟨subd9_4_647, List.forall_mem_cons.2 ⟨subd9_4_648, List.forall_mem_cons.2 ⟨subd9_4_649, List.forall_mem_cons.2 ⟨subd9_4_650, List.forall_mem_cons.2 ⟨subd9_4_651, List.forall_mem_cons.2 ⟨subd9_4_652, List.forall_mem_cons.2 ⟨subd9_4_653, List.forall_mem_cons.2 ⟨subd9_4_654, List.forall_mem_cons.2 ⟨subd9_4_655, List.forall_mem_cons.2 ⟨subd9_4_656, List.forall_mem_cons.2 ⟨subd9_4_657, List.forall_mem_cons.2 ⟨subd9_4_658, List.forall_mem_cons.2 ⟨subd9_4_659, List.forall_mem_cons.2 ⟨subd9_4_660, List.forall_mem_cons.2 ⟨subd9_4_661, List.forall_mem_cons.2 ⟨subd9_4_662, List.forall_mem_cons.2 ⟨subd9_4_663, List.forall_mem_cons.2 ⟨subd9_4_664, List.forall_mem_cons.2 ⟨subd9_4_665, List.forall_mem_cons.2 ⟨subd9_4_666, List.forall_mem_cons.2 ⟨subd9_4_667, List.forall_mem_cons.2 ⟨subd9_4_668, List.forall_mem_cons.2 ⟨subd9_4_669, List.forall_mem_cons.2 ⟨subd9_4_670, List.forall_mem_cons.2 ⟨subd9_4_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_4_672 : subd9_4 [2, 2, -1] = true := by decide +kernel
theorem subd9_4_673 : subd9_4 [2, 2, 0] = true := by decide +kernel
theorem subd9_4_674 : subd9_4 [2, 2, 1] = true := by decide +kernel
theorem subd9_4_675 : subd9_4 [2, 2, 2] = true := by decide +kernel
theorem subd9_4_676 : subd9_4 [2, 2, 3] = true := by decide +kernel
theorem subd9_4_677 : subd9_4 [2, 2, 4] = true := by decide +kernel
theorem subd9_4_678 : subd9_4 [2, 2, 5] = true := by decide +kernel
theorem subd9_4_679 : subd9_4 [2, 2, 6] = true := by decide +kernel
theorem subd9_4_680 : subd9_4 [2, 2, 7] = true := by decide +kernel
theorem subd9_4_681 : subd9_4 [2, 2, 8] = true := by decide +kernel
theorem subd9_4_682 : subd9_4 [2, 3] = true := by decide +kernel
theorem subd9_4_683 : subd9_4 [2, 4] = true := by decide +kernel
theorem subd9_4_684 : subd9_4 [2, 5] = true := by decide +kernel
theorem subd9_4_685 : subd9_4 [2, 6] = true := by decide +kernel
theorem subd9_4_686 : subd9_4 [3, -6] = true := by decide +kernel
theorem subd9_4_687 : subd9_4 [3, -5] = true := by decide +kernel
theorem subd9_4_688 : subd9_4 [3, -4] = true := by decide +kernel
theorem subd9_4_689 : subd9_4 [3, -3] = true := by decide +kernel
theorem subd9_4_690 : subd9_4 [3, -2] = true := by decide +kernel
theorem subd9_4_691 : subd9_4 [3, -1, -7] = true := by decide +kernel
theorem subd9_4_692 : subd9_4 [3, -1, -6] = true := by decide +kernel
theorem subd9_4_693 : subd9_4 [3, -1, -5] = true := by decide +kernel
theorem subd9_4_694 : subd9_4 [3, -1, -4] = true := by decide +kernel
theorem subd9_4_695 : subd9_4 [3, -1, -3] = true := by decide +kernel
theorem subd9_4_696 : subd9_4 [3, -1, -2] = true := by decide +kernel
theorem subd9_4_697 : subd9_4 [3, -1, -1] = true := by decide +kernel
theorem subd9_4_698 : subd9_4 [3, -1, 0] = true := by decide +kernel
theorem subd9_4_699 : subd9_4 [3, -1, 1] = true := by decide +kernel
theorem subd9_4_700 : subd9_4 [3, -1, 2] = true := by decide +kernel
theorem subd9_4_701 : subd9_4 [3, -1, 3] = true := by decide +kernel
theorem subd9_4_702 : subd9_4 [3, -1, 4] = true := by decide +kernel
theorem subd9_4_703 : subd9_4 [3, -1, 5] = true := by decide +kernel
theorem sbd9_4_21 : ∀ q ∈ blkd9_4_21, subd9_4 q = true := by
  unfold blkd9_4_21
  exact List.forall_mem_cons.2 ⟨subd9_4_672, List.forall_mem_cons.2 ⟨subd9_4_673, List.forall_mem_cons.2 ⟨subd9_4_674, List.forall_mem_cons.2 ⟨subd9_4_675, List.forall_mem_cons.2 ⟨subd9_4_676, List.forall_mem_cons.2 ⟨subd9_4_677, List.forall_mem_cons.2 ⟨subd9_4_678, List.forall_mem_cons.2 ⟨subd9_4_679, List.forall_mem_cons.2 ⟨subd9_4_680, List.forall_mem_cons.2 ⟨subd9_4_681, List.forall_mem_cons.2 ⟨subd9_4_682, List.forall_mem_cons.2 ⟨subd9_4_683, List.forall_mem_cons.2 ⟨subd9_4_684, List.forall_mem_cons.2 ⟨subd9_4_685, List.forall_mem_cons.2 ⟨subd9_4_686, List.forall_mem_cons.2 ⟨subd9_4_687, List.forall_mem_cons.2 ⟨subd9_4_688, List.forall_mem_cons.2 ⟨subd9_4_689, List.forall_mem_cons.2 ⟨subd9_4_690, List.forall_mem_cons.2 ⟨subd9_4_691, List.forall_mem_cons.2 ⟨subd9_4_692, List.forall_mem_cons.2 ⟨subd9_4_693, List.forall_mem_cons.2 ⟨subd9_4_694, List.forall_mem_cons.2 ⟨subd9_4_695, List.forall_mem_cons.2 ⟨subd9_4_696, List.forall_mem_cons.2 ⟨subd9_4_697, List.forall_mem_cons.2 ⟨subd9_4_698, List.forall_mem_cons.2 ⟨subd9_4_699, List.forall_mem_cons.2 ⟨subd9_4_700, List.forall_mem_cons.2 ⟨subd9_4_701, List.forall_mem_cons.2 ⟨subd9_4_702, List.forall_mem_cons.2 ⟨subd9_4_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_4_704 : subd9_4 [3, -1, 6] = true := by decide +kernel
theorem subd9_4_705 : subd9_4 [3, -1, 7] = true := by decide +kernel
theorem subd9_4_706 : subd9_4 [3, -1, 8] = true := by decide +kernel
theorem subd9_4_707 : subd9_4 [3, 0, -7] = true := by decide +kernel
theorem subd9_4_708 : subd9_4 [3, 0, -6] = true := by decide +kernel
theorem subd9_4_709 : subd9_4 [3, 0, -5] = true := by decide +kernel
theorem subd9_4_710 : subd9_4 [3, 0, -4] = true := by decide +kernel
theorem subd9_4_711 : subd9_4 [3, 0, -3] = true := by decide +kernel
theorem subd9_4_712 : subd9_4 [3, 0, -2] = true := by decide +kernel
theorem subd9_4_713 : subd9_4 [3, 0, -1] = true := by decide +kernel
theorem subd9_4_714 : subd9_4 [3, 0, 0] = true := by decide +kernel
theorem subd9_4_715 : subd9_4 [3, 0, 1] = true := by decide +kernel
theorem subd9_4_716 : subd9_4 [3, 0, 2] = true := by decide +kernel
theorem subd9_4_717 : subd9_4 [3, 0, 3] = true := by decide +kernel
theorem subd9_4_718 : subd9_4 [3, 0, 4] = true := by decide +kernel
theorem subd9_4_719 : subd9_4 [3, 0, 5] = true := by decide +kernel
theorem subd9_4_720 : subd9_4 [3, 0, 6] = true := by decide +kernel
theorem subd9_4_721 : subd9_4 [3, 0, 7] = true := by decide +kernel
theorem subd9_4_722 : subd9_4 [3, 0, 8] = true := by decide +kernel
theorem subd9_4_723 : subd9_4 [3, 1, -7] = true := by decide +kernel
theorem subd9_4_724 : subd9_4 [3, 1, -6] = true := by decide +kernel
theorem subd9_4_725 : subd9_4 [3, 1, -5] = true := by decide +kernel
theorem subd9_4_726 : subd9_4 [3, 1, -4] = true := by decide +kernel
theorem subd9_4_727 : subd9_4 [3, 1, -3] = true := by decide +kernel
theorem subd9_4_728 : subd9_4 [3, 1, -2] = true := by decide +kernel
theorem subd9_4_729 : subd9_4 [3, 1, -1] = true := by decide +kernel
theorem subd9_4_730 : subd9_4 [3, 1, 0] = true := by decide +kernel
theorem subd9_4_731 : subd9_4 [3, 1, 1] = true := by decide +kernel
theorem subd9_4_732 : subd9_4 [3, 1, 2] = true := by decide +kernel
theorem subd9_4_733 : subd9_4 [3, 1, 3] = true := by decide +kernel
theorem subd9_4_734 : subd9_4 [3, 1, 4] = true := by decide +kernel
theorem subd9_4_735 : subd9_4 [3, 1, 5] = true := by decide +kernel
theorem sbd9_4_22 : ∀ q ∈ blkd9_4_22, subd9_4 q = true := by
  unfold blkd9_4_22
  exact List.forall_mem_cons.2 ⟨subd9_4_704, List.forall_mem_cons.2 ⟨subd9_4_705, List.forall_mem_cons.2 ⟨subd9_4_706, List.forall_mem_cons.2 ⟨subd9_4_707, List.forall_mem_cons.2 ⟨subd9_4_708, List.forall_mem_cons.2 ⟨subd9_4_709, List.forall_mem_cons.2 ⟨subd9_4_710, List.forall_mem_cons.2 ⟨subd9_4_711, List.forall_mem_cons.2 ⟨subd9_4_712, List.forall_mem_cons.2 ⟨subd9_4_713, List.forall_mem_cons.2 ⟨subd9_4_714, List.forall_mem_cons.2 ⟨subd9_4_715, List.forall_mem_cons.2 ⟨subd9_4_716, List.forall_mem_cons.2 ⟨subd9_4_717, List.forall_mem_cons.2 ⟨subd9_4_718, List.forall_mem_cons.2 ⟨subd9_4_719, List.forall_mem_cons.2 ⟨subd9_4_720, List.forall_mem_cons.2 ⟨subd9_4_721, List.forall_mem_cons.2 ⟨subd9_4_722, List.forall_mem_cons.2 ⟨subd9_4_723, List.forall_mem_cons.2 ⟨subd9_4_724, List.forall_mem_cons.2 ⟨subd9_4_725, List.forall_mem_cons.2 ⟨subd9_4_726, List.forall_mem_cons.2 ⟨subd9_4_727, List.forall_mem_cons.2 ⟨subd9_4_728, List.forall_mem_cons.2 ⟨subd9_4_729, List.forall_mem_cons.2 ⟨subd9_4_730, List.forall_mem_cons.2 ⟨subd9_4_731, List.forall_mem_cons.2 ⟨subd9_4_732, List.forall_mem_cons.2 ⟨subd9_4_733, List.forall_mem_cons.2 ⟨subd9_4_734, List.forall_mem_cons.2 ⟨subd9_4_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_4_736 : subd9_4 [3, 1, 6] = true := by decide +kernel
theorem subd9_4_737 : subd9_4 [3, 1, 7] = true := by decide +kernel
theorem subd9_4_738 : subd9_4 [3, 1, 8] = true := by decide +kernel
theorem subd9_4_739 : subd9_4 [3, 2, -6] = true := by decide +kernel
theorem subd9_4_740 : subd9_4 [3, 2, -5] = true := by decide +kernel
theorem subd9_4_741 : subd9_4 [3, 2, -4] = true := by decide +kernel
theorem subd9_4_742 : subd9_4 [3, 2, -3] = true := by decide +kernel
theorem subd9_4_743 : subd9_4 [3, 2, -2] = true := by decide +kernel
theorem subd9_4_744 : subd9_4 [3, 2, -1] = true := by decide +kernel
theorem subd9_4_745 : subd9_4 [3, 2, 0] = true := by decide +kernel
theorem subd9_4_746 : subd9_4 [3, 2, 1] = true := by decide +kernel
theorem subd9_4_747 : subd9_4 [3, 2, 2] = true := by decide +kernel
theorem subd9_4_748 : subd9_4 [3, 2, 3] = true := by decide +kernel
theorem subd9_4_749 : subd9_4 [3, 2, 4] = true := by decide +kernel
theorem subd9_4_750 : subd9_4 [3, 2, 5] = true := by decide +kernel
theorem subd9_4_751 : subd9_4 [3, 2, 6] = true := by decide +kernel
theorem subd9_4_752 : subd9_4 [3, 2, 7] = true := by decide +kernel
theorem subd9_4_753 : subd9_4 [3, 2, 8] = true := by decide +kernel
theorem subd9_4_754 : subd9_4 [3, 3] = true := by decide +kernel
theorem subd9_4_755 : subd9_4 [3, 4] = true := by decide +kernel
theorem subd9_4_756 : subd9_4 [3, 5] = true := by decide +kernel
theorem subd9_4_757 : subd9_4 [3, 6] = true := by decide +kernel
theorem subd9_4_758 : subd9_4 [4, -6] = true := by decide +kernel
theorem subd9_4_759 : subd9_4 [4, -5] = true := by decide +kernel
theorem subd9_4_760 : subd9_4 [4, -4] = true := by decide +kernel
theorem subd9_4_761 : subd9_4 [4, -3] = true := by decide +kernel
theorem subd9_4_762 : subd9_4 [4, -2] = true := by decide +kernel
theorem subd9_4_763 : subd9_4 [4, -1] = true := by decide +kernel
theorem subd9_4_764 : subd9_4 [4, 0, -6] = true := by decide +kernel
theorem subd9_4_765 : subd9_4 [4, 0, -5] = true := by decide +kernel
theorem subd9_4_766 : subd9_4 [4, 0, -4] = true := by decide +kernel
theorem subd9_4_767 : subd9_4 [4, 0, -3] = true := by decide +kernel
theorem sbd9_4_23 : ∀ q ∈ blkd9_4_23, subd9_4 q = true := by
  unfold blkd9_4_23
  exact List.forall_mem_cons.2 ⟨subd9_4_736, List.forall_mem_cons.2 ⟨subd9_4_737, List.forall_mem_cons.2 ⟨subd9_4_738, List.forall_mem_cons.2 ⟨subd9_4_739, List.forall_mem_cons.2 ⟨subd9_4_740, List.forall_mem_cons.2 ⟨subd9_4_741, List.forall_mem_cons.2 ⟨subd9_4_742, List.forall_mem_cons.2 ⟨subd9_4_743, List.forall_mem_cons.2 ⟨subd9_4_744, List.forall_mem_cons.2 ⟨subd9_4_745, List.forall_mem_cons.2 ⟨subd9_4_746, List.forall_mem_cons.2 ⟨subd9_4_747, List.forall_mem_cons.2 ⟨subd9_4_748, List.forall_mem_cons.2 ⟨subd9_4_749, List.forall_mem_cons.2 ⟨subd9_4_750, List.forall_mem_cons.2 ⟨subd9_4_751, List.forall_mem_cons.2 ⟨subd9_4_752, List.forall_mem_cons.2 ⟨subd9_4_753, List.forall_mem_cons.2 ⟨subd9_4_754, List.forall_mem_cons.2 ⟨subd9_4_755, List.forall_mem_cons.2 ⟨subd9_4_756, List.forall_mem_cons.2 ⟨subd9_4_757, List.forall_mem_cons.2 ⟨subd9_4_758, List.forall_mem_cons.2 ⟨subd9_4_759, List.forall_mem_cons.2 ⟨subd9_4_760, List.forall_mem_cons.2 ⟨subd9_4_761, List.forall_mem_cons.2 ⟨subd9_4_762, List.forall_mem_cons.2 ⟨subd9_4_763, List.forall_mem_cons.2 ⟨subd9_4_764, List.forall_mem_cons.2 ⟨subd9_4_765, List.forall_mem_cons.2 ⟨subd9_4_766, List.forall_mem_cons.2 ⟨subd9_4_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C135
