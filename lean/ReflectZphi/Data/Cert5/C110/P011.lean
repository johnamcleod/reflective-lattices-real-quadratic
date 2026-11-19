import ReflectZphi.Data.Cert5.C110.Base

namespace ReflectZphi.Data.Cert5.C110

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_4_352 : subd6_4 [0, 1, 4] = true := by decide +kernel
theorem subd6_4_353 : subd6_4 [0, 1, 5] = true := by decide +kernel
theorem subd6_4_354 : subd6_4 [0, 1, 6] = true := by decide +kernel
theorem subd6_4_355 : subd6_4 [0, 2, -8] = true := by decide +kernel
theorem subd6_4_356 : subd6_4 [0, 2, -7] = true := by decide +kernel
theorem subd6_4_357 : subd6_4 [0, 2, -6] = true := by decide +kernel
theorem subd6_4_358 : subd6_4 [0, 2, -5] = true := by decide +kernel
theorem subd6_4_359 : subd6_4 [0, 2, -4] = true := by decide +kernel
theorem subd6_4_360 : subd6_4 [0, 2, -3] = true := by decide +kernel
theorem subd6_4_361 : subd6_4 [0, 2, -2] = true := by decide +kernel
theorem subd6_4_362 : subd6_4 [0, 2, -1] = true := by decide +kernel
theorem subd6_4_363 : subd6_4 [0, 2, 0] = true := by decide +kernel
theorem subd6_4_364 : subd6_4 [0, 2, 1] = true := by decide +kernel
theorem subd6_4_365 : subd6_4 [0, 2, 2] = true := by decide +kernel
theorem subd6_4_366 : subd6_4 [0, 2, 3] = true := by decide +kernel
theorem subd6_4_367 : subd6_4 [0, 2, 4] = true := by decide +kernel
theorem subd6_4_368 : subd6_4 [0, 2, 5] = true := by decide +kernel
theorem subd6_4_369 : subd6_4 [0, 2, 6] = true := by decide +kernel
theorem subd6_4_370 : subd6_4 [0, 3, -8] = true := by decide +kernel
theorem subd6_4_371 : subd6_4 [0, 3, -7] = true := by decide +kernel
theorem subd6_4_372 : subd6_4 [0, 3, -6] = true := by decide +kernel
theorem subd6_4_373 : subd6_4 [0, 3, -5] = true := by decide +kernel
theorem subd6_4_374 : subd6_4 [0, 3, -4] = true := by decide +kernel
theorem subd6_4_375 : subd6_4 [0, 3, -3] = true := by decide +kernel
theorem subd6_4_376 : subd6_4 [0, 3, -2] = true := by decide +kernel
theorem subd6_4_377 : subd6_4 [0, 3, -1] = true := by decide +kernel
theorem subd6_4_378 : subd6_4 [0, 3, 0] = true := by decide +kernel
theorem subd6_4_379 : subd6_4 [0, 3, 1] = true := by decide +kernel
theorem subd6_4_380 : subd6_4 [0, 3, 2] = true := by decide +kernel
theorem subd6_4_381 : subd6_4 [0, 3, 3] = true := by decide +kernel
theorem subd6_4_382 : subd6_4 [0, 3, 4] = true := by decide +kernel
theorem subd6_4_383 : subd6_4 [0, 3, 5] = true := by decide +kernel
theorem sbd6_4_11 : ∀ q ∈ blkd6_4_11, subd6_4 q = true := by
  unfold blkd6_4_11
  exact List.forall_mem_cons.2 ⟨subd6_4_352, List.forall_mem_cons.2 ⟨subd6_4_353, List.forall_mem_cons.2 ⟨subd6_4_354, List.forall_mem_cons.2 ⟨subd6_4_355, List.forall_mem_cons.2 ⟨subd6_4_356, List.forall_mem_cons.2 ⟨subd6_4_357, List.forall_mem_cons.2 ⟨subd6_4_358, List.forall_mem_cons.2 ⟨subd6_4_359, List.forall_mem_cons.2 ⟨subd6_4_360, List.forall_mem_cons.2 ⟨subd6_4_361, List.forall_mem_cons.2 ⟨subd6_4_362, List.forall_mem_cons.2 ⟨subd6_4_363, List.forall_mem_cons.2 ⟨subd6_4_364, List.forall_mem_cons.2 ⟨subd6_4_365, List.forall_mem_cons.2 ⟨subd6_4_366, List.forall_mem_cons.2 ⟨subd6_4_367, List.forall_mem_cons.2 ⟨subd6_4_368, List.forall_mem_cons.2 ⟨subd6_4_369, List.forall_mem_cons.2 ⟨subd6_4_370, List.forall_mem_cons.2 ⟨subd6_4_371, List.forall_mem_cons.2 ⟨subd6_4_372, List.forall_mem_cons.2 ⟨subd6_4_373, List.forall_mem_cons.2 ⟨subd6_4_374, List.forall_mem_cons.2 ⟨subd6_4_375, List.forall_mem_cons.2 ⟨subd6_4_376, List.forall_mem_cons.2 ⟨subd6_4_377, List.forall_mem_cons.2 ⟨subd6_4_378, List.forall_mem_cons.2 ⟨subd6_4_379, List.forall_mem_cons.2 ⟨subd6_4_380, List.forall_mem_cons.2 ⟨subd6_4_381, List.forall_mem_cons.2 ⟨subd6_4_382, List.forall_mem_cons.2 ⟨subd6_4_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_4_384 : subd6_4 [0, 4] = true := by decide +kernel
theorem subd6_4_385 : subd6_4 [0, 5] = true := by decide +kernel
theorem subd6_4_386 : subd6_4 [0, 6] = true := by decide +kernel
theorem subd6_4_387 : subd6_4 [1, -7] = true := by decide +kernel
theorem subd6_4_388 : subd6_4 [1, -6] = true := by decide +kernel
theorem subd6_4_389 : subd6_4 [1, -5] = true := by decide +kernel
theorem subd6_4_390 : subd6_4 [1, -4] = true := by decide +kernel
theorem subd6_4_391 : subd6_4 [1, -3, -6] = true := by decide +kernel
theorem subd6_4_392 : subd6_4 [1, -3, -5] = true := by decide +kernel
theorem subd6_4_393 : subd6_4 [1, -3, -4] = true := by decide +kernel
theorem subd6_4_394 : subd6_4 [1, -3, -3] = true := by decide +kernel
theorem subd6_4_395 : subd6_4 [1, -3, -2] = true := by decide +kernel
theorem subd6_4_396 : subd6_4 [1, -3, -1] = true := by decide +kernel
theorem subd6_4_397 : subd6_4 [1, -3, 0] = true := by decide +kernel
theorem subd6_4_398 : subd6_4 [1, -3, 1] = true := by decide +kernel
theorem subd6_4_399 : subd6_4 [1, -3, 2] = true := by decide +kernel
theorem subd6_4_400 : subd6_4 [1, -3, 3] = true := by decide +kernel
theorem subd6_4_401 : subd6_4 [1, -3, 4] = true := by decide +kernel
theorem subd6_4_402 : subd6_4 [1, -3, 5] = true := by decide +kernel
theorem subd6_4_403 : subd6_4 [1, -3, 6] = true := by decide +kernel
theorem subd6_4_404 : subd6_4 [1, -3, 7] = true := by decide +kernel
theorem subd6_4_405 : subd6_4 [1, -2, -7] = true := by decide +kernel
theorem subd6_4_406 : subd6_4 [1, -2, -6] = true := by decide +kernel
theorem subd6_4_407 : subd6_4 [1, -2, -5] = true := by decide +kernel
theorem subd6_4_408 : subd6_4 [1, -2, -4] = true := by decide +kernel
theorem subd6_4_409 : subd6_4 [1, -2, -3] = true := by decide +kernel
theorem subd6_4_410 : subd6_4 [1, -2, -2] = true := by decide +kernel
theorem subd6_4_411 : subd6_4 [1, -2, -1] = true := by decide +kernel
theorem subd6_4_412 : subd6_4 [1, -2, 0] = true := by decide +kernel
theorem subd6_4_413 : subd6_4 [1, -2, 1] = true := by decide +kernel
theorem subd6_4_414 : subd6_4 [1, -2, 2] = true := by decide +kernel
theorem subd6_4_415 : subd6_4 [1, -2, 3] = true := by decide +kernel
theorem sbd6_4_12 : ∀ q ∈ blkd6_4_12, subd6_4 q = true := by
  unfold blkd6_4_12
  exact List.forall_mem_cons.2 ⟨subd6_4_384, List.forall_mem_cons.2 ⟨subd6_4_385, List.forall_mem_cons.2 ⟨subd6_4_386, List.forall_mem_cons.2 ⟨subd6_4_387, List.forall_mem_cons.2 ⟨subd6_4_388, List.forall_mem_cons.2 ⟨subd6_4_389, List.forall_mem_cons.2 ⟨subd6_4_390, List.forall_mem_cons.2 ⟨subd6_4_391, List.forall_mem_cons.2 ⟨subd6_4_392, List.forall_mem_cons.2 ⟨subd6_4_393, List.forall_mem_cons.2 ⟨subd6_4_394, List.forall_mem_cons.2 ⟨subd6_4_395, List.forall_mem_cons.2 ⟨subd6_4_396, List.forall_mem_cons.2 ⟨subd6_4_397, List.forall_mem_cons.2 ⟨subd6_4_398, List.forall_mem_cons.2 ⟨subd6_4_399, List.forall_mem_cons.2 ⟨subd6_4_400, List.forall_mem_cons.2 ⟨subd6_4_401, List.forall_mem_cons.2 ⟨subd6_4_402, List.forall_mem_cons.2 ⟨subd6_4_403, List.forall_mem_cons.2 ⟨subd6_4_404, List.forall_mem_cons.2 ⟨subd6_4_405, List.forall_mem_cons.2 ⟨subd6_4_406, List.forall_mem_cons.2 ⟨subd6_4_407, List.forall_mem_cons.2 ⟨subd6_4_408, List.forall_mem_cons.2 ⟨subd6_4_409, List.forall_mem_cons.2 ⟨subd6_4_410, List.forall_mem_cons.2 ⟨subd6_4_411, List.forall_mem_cons.2 ⟨subd6_4_412, List.forall_mem_cons.2 ⟨subd6_4_413, List.forall_mem_cons.2 ⟨subd6_4_414, List.forall_mem_cons.2 ⟨subd6_4_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_4_416 : subd6_4 [1, -2, 4] = true := by decide +kernel
theorem subd6_4_417 : subd6_4 [1, -2, 5] = true := by decide +kernel
theorem subd6_4_418 : subd6_4 [1, -2, 6] = true := by decide +kernel
theorem subd6_4_419 : subd6_4 [1, -2, 7] = true := by decide +kernel
theorem subd6_4_420 : subd6_4 [1, -1, -7] = true := by decide +kernel
theorem subd6_4_421 : subd6_4 [1, -1, -6] = true := by decide +kernel
theorem subd6_4_422 : subd6_4 [1, -1, -5] = true := by decide +kernel
theorem subd6_4_423 : subd6_4 [1, -1, -4] = true := by decide +kernel
theorem subd6_4_424 : subd6_4 [1, -1, -3] = true := by decide +kernel
theorem subd6_4_425 : subd6_4 [1, -1, -2] = true := by decide +kernel
theorem subd6_4_426 : subd6_4 [1, -1, -1] = true := by decide +kernel
theorem subd6_4_427 : subd6_4 [1, -1, 0] = true := by decide +kernel
theorem subd6_4_428 : subd6_4 [1, -1, 1] = true := by decide +kernel
theorem subd6_4_429 : subd6_4 [1, -1, 2] = true := by decide +kernel
theorem subd6_4_430 : subd6_4 [1, -1, 3] = true := by decide +kernel
theorem subd6_4_431 : subd6_4 [1, -1, 4] = true := by decide +kernel
theorem subd6_4_432 : subd6_4 [1, -1, 5] = true := by decide +kernel
theorem subd6_4_433 : subd6_4 [1, -1, 6] = true := by decide +kernel
theorem subd6_4_434 : subd6_4 [1, -1, 7] = true := by decide +kernel
theorem subd6_4_435 : subd6_4 [1, 0, -8] = true := by decide +kernel
theorem subd6_4_436 : subd6_4 [1, 0, -7] = true := by decide +kernel
theorem subd6_4_437 : subd6_4 [1, 0, -6] = true := by decide +kernel
theorem subd6_4_438 : subd6_4 [1, 0, -5] = true := by decide +kernel
theorem subd6_4_439 : subd6_4 [1, 0, -4] = true := by decide +kernel
theorem subd6_4_440 : subd6_4 [1, 0, -3] = true := by decide +kernel
theorem subd6_4_441 : subd6_4 [1, 0, -2] = true := by decide +kernel
theorem subd6_4_442 : subd6_4 [1, 0, -1] = true := by decide +kernel
theorem subd6_4_443 : subd6_4 [1, 0, 0] = true := by decide +kernel
theorem subd6_4_444 : subd6_4 [1, 0, 1] = true := by decide +kernel
theorem subd6_4_445 : subd6_4 [1, 0, 2] = true := by decide +kernel
theorem subd6_4_446 : subd6_4 [1, 0, 3] = true := by decide +kernel
theorem subd6_4_447 : subd6_4 [1, 0, 4] = true := by decide +kernel
theorem sbd6_4_13 : ∀ q ∈ blkd6_4_13, subd6_4 q = true := by
  unfold blkd6_4_13
  exact List.forall_mem_cons.2 ⟨subd6_4_416, List.forall_mem_cons.2 ⟨subd6_4_417, List.forall_mem_cons.2 ⟨subd6_4_418, List.forall_mem_cons.2 ⟨subd6_4_419, List.forall_mem_cons.2 ⟨subd6_4_420, List.forall_mem_cons.2 ⟨subd6_4_421, List.forall_mem_cons.2 ⟨subd6_4_422, List.forall_mem_cons.2 ⟨subd6_4_423, List.forall_mem_cons.2 ⟨subd6_4_424, List.forall_mem_cons.2 ⟨subd6_4_425, List.forall_mem_cons.2 ⟨subd6_4_426, List.forall_mem_cons.2 ⟨subd6_4_427, List.forall_mem_cons.2 ⟨subd6_4_428, List.forall_mem_cons.2 ⟨subd6_4_429, List.forall_mem_cons.2 ⟨subd6_4_430, List.forall_mem_cons.2 ⟨subd6_4_431, List.forall_mem_cons.2 ⟨subd6_4_432, List.forall_mem_cons.2 ⟨subd6_4_433, List.forall_mem_cons.2 ⟨subd6_4_434, List.forall_mem_cons.2 ⟨subd6_4_435, List.forall_mem_cons.2 ⟨subd6_4_436, List.forall_mem_cons.2 ⟨subd6_4_437, List.forall_mem_cons.2 ⟨subd6_4_438, List.forall_mem_cons.2 ⟨subd6_4_439, List.forall_mem_cons.2 ⟨subd6_4_440, List.forall_mem_cons.2 ⟨subd6_4_441, List.forall_mem_cons.2 ⟨subd6_4_442, List.forall_mem_cons.2 ⟨subd6_4_443, List.forall_mem_cons.2 ⟨subd6_4_444, List.forall_mem_cons.2 ⟨subd6_4_445, List.forall_mem_cons.2 ⟨subd6_4_446, List.forall_mem_cons.2 ⟨subd6_4_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_4_448 : subd6_4 [1, 0, 5] = true := by decide +kernel
theorem subd6_4_449 : subd6_4 [1, 0, 6] = true := by decide +kernel
theorem subd6_4_450 : subd6_4 [1, 0, 7] = true := by decide +kernel
theorem subd6_4_451 : subd6_4 [1, 1, -8] = true := by decide +kernel
theorem subd6_4_452 : subd6_4 [1, 1, -7] = true := by decide +kernel
theorem subd6_4_453 : subd6_4 [1, 1, -6] = true := by decide +kernel
theorem subd6_4_454 : subd6_4 [1, 1, -5] = true := by decide +kernel
theorem subd6_4_455 : subd6_4 [1, 1, -4] = true := by decide +kernel
theorem subd6_4_456 : subd6_4 [1, 1, -3] = true := by decide +kernel
theorem subd6_4_457 : subd6_4 [1, 1, -2] = true := by decide +kernel
theorem subd6_4_458 : subd6_4 [1, 1, -1] = true := by decide +kernel
theorem subd6_4_459 : subd6_4 [1, 1, 0] = true := by decide +kernel
theorem subd6_4_460 : subd6_4 [1, 1, 1] = true := by decide +kernel
theorem subd6_4_461 : subd6_4 [1, 1, 2] = true := by decide +kernel
theorem subd6_4_462 : subd6_4 [1, 1, 3] = true := by decide +kernel
theorem subd6_4_463 : subd6_4 [1, 1, 4] = true := by decide +kernel
theorem subd6_4_464 : subd6_4 [1, 1, 5] = true := by decide +kernel
theorem subd6_4_465 : subd6_4 [1, 1, 6] = true := by decide +kernel
theorem subd6_4_466 : subd6_4 [1, 2, -8] = true := by decide +kernel
theorem subd6_4_467 : subd6_4 [1, 2, -7] = true := by decide +kernel
theorem subd6_4_468 : subd6_4 [1, 2, -6] = true := by decide +kernel
theorem subd6_4_469 : subd6_4 [1, 2, -5] = true := by decide +kernel
theorem subd6_4_470 : subd6_4 [1, 2, -4] = true := by decide +kernel
theorem subd6_4_471 : subd6_4 [1, 2, -3] = true := by decide +kernel
theorem subd6_4_472 : subd6_4 [1, 2, -2] = true := by decide +kernel
theorem subd6_4_473 : subd6_4 [1, 2, -1] = true := by decide +kernel
theorem subd6_4_474 : subd6_4 [1, 2, 0] = true := by decide +kernel
theorem subd6_4_475 : subd6_4 [1, 2, 1] = true := by decide +kernel
theorem subd6_4_476 : subd6_4 [1, 2, 2] = true := by decide +kernel
theorem subd6_4_477 : subd6_4 [1, 2, 3] = true := by decide +kernel
theorem subd6_4_478 : subd6_4 [1, 2, 4] = true := by decide +kernel
theorem subd6_4_479 : subd6_4 [1, 2, 5] = true := by decide +kernel
theorem sbd6_4_14 : ∀ q ∈ blkd6_4_14, subd6_4 q = true := by
  unfold blkd6_4_14
  exact List.forall_mem_cons.2 ⟨subd6_4_448, List.forall_mem_cons.2 ⟨subd6_4_449, List.forall_mem_cons.2 ⟨subd6_4_450, List.forall_mem_cons.2 ⟨subd6_4_451, List.forall_mem_cons.2 ⟨subd6_4_452, List.forall_mem_cons.2 ⟨subd6_4_453, List.forall_mem_cons.2 ⟨subd6_4_454, List.forall_mem_cons.2 ⟨subd6_4_455, List.forall_mem_cons.2 ⟨subd6_4_456, List.forall_mem_cons.2 ⟨subd6_4_457, List.forall_mem_cons.2 ⟨subd6_4_458, List.forall_mem_cons.2 ⟨subd6_4_459, List.forall_mem_cons.2 ⟨subd6_4_460, List.forall_mem_cons.2 ⟨subd6_4_461, List.forall_mem_cons.2 ⟨subd6_4_462, List.forall_mem_cons.2 ⟨subd6_4_463, List.forall_mem_cons.2 ⟨subd6_4_464, List.forall_mem_cons.2 ⟨subd6_4_465, List.forall_mem_cons.2 ⟨subd6_4_466, List.forall_mem_cons.2 ⟨subd6_4_467, List.forall_mem_cons.2 ⟨subd6_4_468, List.forall_mem_cons.2 ⟨subd6_4_469, List.forall_mem_cons.2 ⟨subd6_4_470, List.forall_mem_cons.2 ⟨subd6_4_471, List.forall_mem_cons.2 ⟨subd6_4_472, List.forall_mem_cons.2 ⟨subd6_4_473, List.forall_mem_cons.2 ⟨subd6_4_474, List.forall_mem_cons.2 ⟨subd6_4_475, List.forall_mem_cons.2 ⟨subd6_4_476, List.forall_mem_cons.2 ⟨subd6_4_477, List.forall_mem_cons.2 ⟨subd6_4_478, List.forall_mem_cons.2 ⟨subd6_4_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_4_480 : subd6_4 [1, 2, 6] = true := by decide +kernel
theorem subd6_4_481 : subd6_4 [1, 3, -8] = true := by decide +kernel
theorem subd6_4_482 : subd6_4 [1, 3, -7] = true := by decide +kernel
theorem subd6_4_483 : subd6_4 [1, 3, -6] = true := by decide +kernel
theorem subd6_4_484 : subd6_4 [1, 3, -5] = true := by decide +kernel
theorem subd6_4_485 : subd6_4 [1, 3, -4] = true := by decide +kernel
theorem subd6_4_486 : subd6_4 [1, 3, -3] = true := by decide +kernel
theorem subd6_4_487 : subd6_4 [1, 3, -2] = true := by decide +kernel
theorem subd6_4_488 : subd6_4 [1, 3, -1] = true := by decide +kernel
theorem subd6_4_489 : subd6_4 [1, 3, 0] = true := by decide +kernel
theorem subd6_4_490 : subd6_4 [1, 3, 1] = true := by decide +kernel
theorem subd6_4_491 : subd6_4 [1, 3, 2] = true := by decide +kernel
theorem subd6_4_492 : subd6_4 [1, 3, 3] = true := by decide +kernel
theorem subd6_4_493 : subd6_4 [1, 3, 4] = true := by decide +kernel
theorem subd6_4_494 : subd6_4 [1, 3, 5] = true := by decide +kernel
theorem subd6_4_495 : subd6_4 [1, 4] = true := by decide +kernel
theorem subd6_4_496 : subd6_4 [1, 5] = true := by decide +kernel
theorem subd6_4_497 : subd6_4 [1, 6] = true := by decide +kernel
theorem subd6_4_498 : subd6_4 [2, -7] = true := by decide +kernel
theorem subd6_4_499 : subd6_4 [2, -6] = true := by decide +kernel
theorem subd6_4_500 : subd6_4 [2, -5] = true := by decide +kernel
theorem subd6_4_501 : subd6_4 [2, -4] = true := by decide +kernel
theorem subd6_4_502 : subd6_4 [2, -3] = true := by decide +kernel
theorem subd6_4_503 : subd6_4 [2, -2, -6] = true := by decide +kernel
theorem subd6_4_504 : subd6_4 [2, -2, -5] = true := by decide +kernel
theorem subd6_4_505 : subd6_4 [2, -2, -4] = true := by decide +kernel
theorem subd6_4_506 : subd6_4 [2, -2, -3] = true := by decide +kernel
theorem subd6_4_507 : subd6_4 [2, -2, -2] = true := by decide +kernel
theorem subd6_4_508 : subd6_4 [2, -2, -1] = true := by decide +kernel
theorem subd6_4_509 : subd6_4 [2, -2, 0] = true := by decide +kernel
theorem subd6_4_510 : subd6_4 [2, -2, 1] = true := by decide +kernel
theorem subd6_4_511 : subd6_4 [2, -2, 2] = true := by decide +kernel
theorem sbd6_4_15 : ∀ q ∈ blkd6_4_15, subd6_4 q = true := by
  unfold blkd6_4_15
  exact List.forall_mem_cons.2 ⟨subd6_4_480, List.forall_mem_cons.2 ⟨subd6_4_481, List.forall_mem_cons.2 ⟨subd6_4_482, List.forall_mem_cons.2 ⟨subd6_4_483, List.forall_mem_cons.2 ⟨subd6_4_484, List.forall_mem_cons.2 ⟨subd6_4_485, List.forall_mem_cons.2 ⟨subd6_4_486, List.forall_mem_cons.2 ⟨subd6_4_487, List.forall_mem_cons.2 ⟨subd6_4_488, List.forall_mem_cons.2 ⟨subd6_4_489, List.forall_mem_cons.2 ⟨subd6_4_490, List.forall_mem_cons.2 ⟨subd6_4_491, List.forall_mem_cons.2 ⟨subd6_4_492, List.forall_mem_cons.2 ⟨subd6_4_493, List.forall_mem_cons.2 ⟨subd6_4_494, List.forall_mem_cons.2 ⟨subd6_4_495, List.forall_mem_cons.2 ⟨subd6_4_496, List.forall_mem_cons.2 ⟨subd6_4_497, List.forall_mem_cons.2 ⟨subd6_4_498, List.forall_mem_cons.2 ⟨subd6_4_499, List.forall_mem_cons.2 ⟨subd6_4_500, List.forall_mem_cons.2 ⟨subd6_4_501, List.forall_mem_cons.2 ⟨subd6_4_502, List.forall_mem_cons.2 ⟨subd6_4_503, List.forall_mem_cons.2 ⟨subd6_4_504, List.forall_mem_cons.2 ⟨subd6_4_505, List.forall_mem_cons.2 ⟨subd6_4_506, List.forall_mem_cons.2 ⟨subd6_4_507, List.forall_mem_cons.2 ⟨subd6_4_508, List.forall_mem_cons.2 ⟨subd6_4_509, List.forall_mem_cons.2 ⟨subd6_4_510, List.forall_mem_cons.2 ⟨subd6_4_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_4_512 : subd6_4 [2, -2, 3] = true := by decide +kernel
theorem subd6_4_513 : subd6_4 [2, -2, 4] = true := by decide +kernel
theorem subd6_4_514 : subd6_4 [2, -2, 5] = true := by decide +kernel
theorem subd6_4_515 : subd6_4 [2, -2, 6] = true := by decide +kernel
theorem subd6_4_516 : subd6_4 [2, -2, 7] = true := by decide +kernel
theorem subd6_4_517 : subd6_4 [2, -1, -7] = true := by decide +kernel
theorem subd6_4_518 : subd6_4 [2, -1, -6] = true := by decide +kernel
theorem subd6_4_519 : subd6_4 [2, -1, -5] = true := by decide +kernel
theorem subd6_4_520 : subd6_4 [2, -1, -4] = true := by decide +kernel
theorem subd6_4_521 : subd6_4 [2, -1, -3] = true := by decide +kernel
theorem subd6_4_522 : subd6_4 [2, -1, -2] = true := by decide +kernel
theorem subd6_4_523 : subd6_4 [2, -1, -1] = true := by decide +kernel
theorem subd6_4_524 : subd6_4 [2, -1, 0] = true := by decide +kernel
theorem subd6_4_525 : subd6_4 [2, -1, 1] = true := by decide +kernel
theorem subd6_4_526 : subd6_4 [2, -1, 2] = true := by decide +kernel
theorem subd6_4_527 : subd6_4 [2, -1, 3] = true := by decide +kernel
theorem subd6_4_528 : subd6_4 [2, -1, 4] = true := by decide +kernel
theorem subd6_4_529 : subd6_4 [2, -1, 5] = true := by decide +kernel
theorem subd6_4_530 : subd6_4 [2, -1, 6] = true := by decide +kernel
theorem subd6_4_531 : subd6_4 [2, -1, 7] = true := by decide +kernel
theorem subd6_4_532 : subd6_4 [2, 0, -7] = true := by decide +kernel
theorem subd6_4_533 : subd6_4 [2, 0, -6] = true := by decide +kernel
theorem subd6_4_534 : subd6_4 [2, 0, -5] = true := by decide +kernel
theorem subd6_4_535 : subd6_4 [2, 0, -4] = true := by decide +kernel
theorem subd6_4_536 : subd6_4 [2, 0, -3] = true := by decide +kernel
theorem subd6_4_537 : subd6_4 [2, 0, -2] = true := by decide +kernel
theorem subd6_4_538 : subd6_4 [2, 0, -1] = true := by decide +kernel
theorem subd6_4_539 : subd6_4 [2, 0, 0] = true := by decide +kernel
theorem subd6_4_540 : subd6_4 [2, 0, 1] = true := by decide +kernel
theorem subd6_4_541 : subd6_4 [2, 0, 2] = true := by decide +kernel
theorem subd6_4_542 : subd6_4 [2, 0, 3] = true := by decide +kernel
theorem subd6_4_543 : subd6_4 [2, 0, 4] = true := by decide +kernel
theorem sbd6_4_16 : ∀ q ∈ blkd6_4_16, subd6_4 q = true := by
  unfold blkd6_4_16
  exact List.forall_mem_cons.2 ⟨subd6_4_512, List.forall_mem_cons.2 ⟨subd6_4_513, List.forall_mem_cons.2 ⟨subd6_4_514, List.forall_mem_cons.2 ⟨subd6_4_515, List.forall_mem_cons.2 ⟨subd6_4_516, List.forall_mem_cons.2 ⟨subd6_4_517, List.forall_mem_cons.2 ⟨subd6_4_518, List.forall_mem_cons.2 ⟨subd6_4_519, List.forall_mem_cons.2 ⟨subd6_4_520, List.forall_mem_cons.2 ⟨subd6_4_521, List.forall_mem_cons.2 ⟨subd6_4_522, List.forall_mem_cons.2 ⟨subd6_4_523, List.forall_mem_cons.2 ⟨subd6_4_524, List.forall_mem_cons.2 ⟨subd6_4_525, List.forall_mem_cons.2 ⟨subd6_4_526, List.forall_mem_cons.2 ⟨subd6_4_527, List.forall_mem_cons.2 ⟨subd6_4_528, List.forall_mem_cons.2 ⟨subd6_4_529, List.forall_mem_cons.2 ⟨subd6_4_530, List.forall_mem_cons.2 ⟨subd6_4_531, List.forall_mem_cons.2 ⟨subd6_4_532, List.forall_mem_cons.2 ⟨subd6_4_533, List.forall_mem_cons.2 ⟨subd6_4_534, List.forall_mem_cons.2 ⟨subd6_4_535, List.forall_mem_cons.2 ⟨subd6_4_536, List.forall_mem_cons.2 ⟨subd6_4_537, List.forall_mem_cons.2 ⟨subd6_4_538, List.forall_mem_cons.2 ⟨subd6_4_539, List.forall_mem_cons.2 ⟨subd6_4_540, List.forall_mem_cons.2 ⟨subd6_4_541, List.forall_mem_cons.2 ⟨subd6_4_542, List.forall_mem_cons.2 ⟨subd6_4_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_4_544 : subd6_4 [2, 0, 5] = true := by decide +kernel
theorem subd6_4_545 : subd6_4 [2, 0, 6] = true := by decide +kernel
theorem subd6_4_546 : subd6_4 [2, 0, 7] = true := by decide +kernel
theorem subd6_4_547 : subd6_4 [2, 1, -8] = true := by decide +kernel
theorem subd6_4_548 : subd6_4 [2, 1, -7] = true := by decide +kernel
theorem subd6_4_549 : subd6_4 [2, 1, -6] = true := by decide +kernel
theorem subd6_4_550 : subd6_4 [2, 1, -5] = true := by decide +kernel
theorem subd6_4_551 : subd6_4 [2, 1, -4] = true := by decide +kernel
theorem subd6_4_552 : subd6_4 [2, 1, -3] = true := by decide +kernel
theorem subd6_4_553 : subd6_4 [2, 1, -2] = true := by decide +kernel
theorem subd6_4_554 : subd6_4 [2, 1, -1] = true := by decide +kernel
theorem subd6_4_555 : subd6_4 [2, 1, 0] = true := by decide +kernel
theorem subd6_4_556 : subd6_4 [2, 1, 1] = true := by decide +kernel
theorem subd6_4_557 : subd6_4 [2, 1, 2] = true := by decide +kernel
theorem subd6_4_558 : subd6_4 [2, 1, 3] = true := by decide +kernel
theorem subd6_4_559 : subd6_4 [2, 1, 4] = true := by decide +kernel
theorem subd6_4_560 : subd6_4 [2, 1, 5] = true := by decide +kernel
theorem subd6_4_561 : subd6_4 [2, 1, 6] = true := by decide +kernel
theorem subd6_4_562 : subd6_4 [2, 2, -8] = true := by decide +kernel
theorem subd6_4_563 : subd6_4 [2, 2, -7] = true := by decide +kernel
theorem subd6_4_564 : subd6_4 [2, 2, -6] = true := by decide +kernel
theorem subd6_4_565 : subd6_4 [2, 2, -5] = true := by decide +kernel
theorem subd6_4_566 : subd6_4 [2, 2, -4] = true := by decide +kernel
theorem subd6_4_567 : subd6_4 [2, 2, -3] = true := by decide +kernel
theorem subd6_4_568 : subd6_4 [2, 2, -2] = true := by decide +kernel
theorem subd6_4_569 : subd6_4 [2, 2, -1] = true := by decide +kernel
theorem subd6_4_570 : subd6_4 [2, 2, 0] = true := by decide +kernel
theorem subd6_4_571 : subd6_4 [2, 2, 1] = true := by decide +kernel
theorem subd6_4_572 : subd6_4 [2, 2, 2] = true := by decide +kernel
theorem subd6_4_573 : subd6_4 [2, 2, 3] = true := by decide +kernel
theorem subd6_4_574 : subd6_4 [2, 2, 4] = true := by decide +kernel
theorem subd6_4_575 : subd6_4 [2, 2, 5] = true := by decide +kernel
theorem sbd6_4_17 : ∀ q ∈ blkd6_4_17, subd6_4 q = true := by
  unfold blkd6_4_17
  exact List.forall_mem_cons.2 ⟨subd6_4_544, List.forall_mem_cons.2 ⟨subd6_4_545, List.forall_mem_cons.2 ⟨subd6_4_546, List.forall_mem_cons.2 ⟨subd6_4_547, List.forall_mem_cons.2 ⟨subd6_4_548, List.forall_mem_cons.2 ⟨subd6_4_549, List.forall_mem_cons.2 ⟨subd6_4_550, List.forall_mem_cons.2 ⟨subd6_4_551, List.forall_mem_cons.2 ⟨subd6_4_552, List.forall_mem_cons.2 ⟨subd6_4_553, List.forall_mem_cons.2 ⟨subd6_4_554, List.forall_mem_cons.2 ⟨subd6_4_555, List.forall_mem_cons.2 ⟨subd6_4_556, List.forall_mem_cons.2 ⟨subd6_4_557, List.forall_mem_cons.2 ⟨subd6_4_558, List.forall_mem_cons.2 ⟨subd6_4_559, List.forall_mem_cons.2 ⟨subd6_4_560, List.forall_mem_cons.2 ⟨subd6_4_561, List.forall_mem_cons.2 ⟨subd6_4_562, List.forall_mem_cons.2 ⟨subd6_4_563, List.forall_mem_cons.2 ⟨subd6_4_564, List.forall_mem_cons.2 ⟨subd6_4_565, List.forall_mem_cons.2 ⟨subd6_4_566, List.forall_mem_cons.2 ⟨subd6_4_567, List.forall_mem_cons.2 ⟨subd6_4_568, List.forall_mem_cons.2 ⟨subd6_4_569, List.forall_mem_cons.2 ⟨subd6_4_570, List.forall_mem_cons.2 ⟨subd6_4_571, List.forall_mem_cons.2 ⟨subd6_4_572, List.forall_mem_cons.2 ⟨subd6_4_573, List.forall_mem_cons.2 ⟨subd6_4_574, List.forall_mem_cons.2 ⟨subd6_4_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_4_576 : subd6_4 [2, 3] = true := by decide +kernel
theorem subd6_4_577 : subd6_4 [2, 4] = true := by decide +kernel
theorem subd6_4_578 : subd6_4 [2, 5] = true := by decide +kernel
theorem subd6_4_579 : subd6_4 [2, 6] = true := by decide +kernel
theorem subd6_4_580 : subd6_4 [3, -6] = true := by decide +kernel
theorem subd6_4_581 : subd6_4 [3, -5] = true := by decide +kernel
theorem subd6_4_582 : subd6_4 [3, -4] = true := by decide +kernel
theorem subd6_4_583 : subd6_4 [3, -3] = true := by decide +kernel
theorem subd6_4_584 : subd6_4 [3, -2, -6] = true := by decide +kernel
theorem subd6_4_585 : subd6_4 [3, -2, -5] = true := by decide +kernel
theorem subd6_4_586 : subd6_4 [3, -2, -4] = true := by decide +kernel
theorem subd6_4_587 : subd6_4 [3, -2, -3] = true := by decide +kernel
theorem subd6_4_588 : subd6_4 [3, -2, -2] = true := by decide +kernel
theorem subd6_4_589 : subd6_4 [3, -2, -1] = true := by decide +kernel
theorem subd6_4_590 : subd6_4 [3, -2, 0] = true := by decide +kernel
theorem subd6_4_591 : subd6_4 [3, -2, 1] = true := by decide +kernel
theorem subd6_4_592 : subd6_4 [3, -2, 2] = true := by decide +kernel
theorem subd6_4_593 : subd6_4 [3, -2, 3] = true := by decide +kernel
theorem subd6_4_594 : subd6_4 [3, -2, 4] = true := by decide +kernel
theorem subd6_4_595 : subd6_4 [3, -2, 5] = true := by decide +kernel
theorem subd6_4_596 : subd6_4 [3, -2, 6] = true := by decide +kernel
theorem subd6_4_597 : subd6_4 [3, -2, 7] = true := by decide +kernel
theorem subd6_4_598 : subd6_4 [3, -1, -6] = true := by decide +kernel
theorem subd6_4_599 : subd6_4 [3, -1, -5] = true := by decide +kernel
theorem subd6_4_600 : subd6_4 [3, -1, -4] = true := by decide +kernel
theorem subd6_4_601 : subd6_4 [3, -1, -3] = true := by decide +kernel
theorem subd6_4_602 : subd6_4 [3, -1, -2] = true := by decide +kernel
theorem subd6_4_603 : subd6_4 [3, -1, -1] = true := by decide +kernel
theorem subd6_4_604 : subd6_4 [3, -1, 0] = true := by decide +kernel
theorem subd6_4_605 : subd6_4 [3, -1, 1] = true := by decide +kernel
theorem subd6_4_606 : subd6_4 [3, -1, 2] = true := by decide +kernel
theorem subd6_4_607 : subd6_4 [3, -1, 3] = true := by decide +kernel
theorem sbd6_4_18 : ∀ q ∈ blkd6_4_18, subd6_4 q = true := by
  unfold blkd6_4_18
  exact List.forall_mem_cons.2 ⟨subd6_4_576, List.forall_mem_cons.2 ⟨subd6_4_577, List.forall_mem_cons.2 ⟨subd6_4_578, List.forall_mem_cons.2 ⟨subd6_4_579, List.forall_mem_cons.2 ⟨subd6_4_580, List.forall_mem_cons.2 ⟨subd6_4_581, List.forall_mem_cons.2 ⟨subd6_4_582, List.forall_mem_cons.2 ⟨subd6_4_583, List.forall_mem_cons.2 ⟨subd6_4_584, List.forall_mem_cons.2 ⟨subd6_4_585, List.forall_mem_cons.2 ⟨subd6_4_586, List.forall_mem_cons.2 ⟨subd6_4_587, List.forall_mem_cons.2 ⟨subd6_4_588, List.forall_mem_cons.2 ⟨subd6_4_589, List.forall_mem_cons.2 ⟨subd6_4_590, List.forall_mem_cons.2 ⟨subd6_4_591, List.forall_mem_cons.2 ⟨subd6_4_592, List.forall_mem_cons.2 ⟨subd6_4_593, List.forall_mem_cons.2 ⟨subd6_4_594, List.forall_mem_cons.2 ⟨subd6_4_595, List.forall_mem_cons.2 ⟨subd6_4_596, List.forall_mem_cons.2 ⟨subd6_4_597, List.forall_mem_cons.2 ⟨subd6_4_598, List.forall_mem_cons.2 ⟨subd6_4_599, List.forall_mem_cons.2 ⟨subd6_4_600, List.forall_mem_cons.2 ⟨subd6_4_601, List.forall_mem_cons.2 ⟨subd6_4_602, List.forall_mem_cons.2 ⟨subd6_4_603, List.forall_mem_cons.2 ⟨subd6_4_604, List.forall_mem_cons.2 ⟨subd6_4_605, List.forall_mem_cons.2 ⟨subd6_4_606, List.forall_mem_cons.2 ⟨subd6_4_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_4_608 : subd6_4 [3, -1, 4] = true := by decide +kernel
theorem subd6_4_609 : subd6_4 [3, -1, 5] = true := by decide +kernel
theorem subd6_4_610 : subd6_4 [3, -1, 6] = true := by decide +kernel
theorem subd6_4_611 : subd6_4 [3, 0, -7] = true := by decide +kernel
theorem subd6_4_612 : subd6_4 [3, 0, -6] = true := by decide +kernel
theorem subd6_4_613 : subd6_4 [3, 0, -5] = true := by decide +kernel
theorem subd6_4_614 : subd6_4 [3, 0, -4] = true := by decide +kernel
theorem subd6_4_615 : subd6_4 [3, 0, -3] = true := by decide +kernel
theorem subd6_4_616 : subd6_4 [3, 0, -2] = true := by decide +kernel
theorem subd6_4_617 : subd6_4 [3, 0, -1] = true := by decide +kernel
theorem subd6_4_618 : subd6_4 [3, 0, 0] = true := by decide +kernel
theorem subd6_4_619 : subd6_4 [3, 0, 1] = true := by decide +kernel
theorem subd6_4_620 : subd6_4 [3, 0, 2] = true := by decide +kernel
theorem subd6_4_621 : subd6_4 [3, 0, 3] = true := by decide +kernel
theorem subd6_4_622 : subd6_4 [3, 0, 4] = true := by decide +kernel
theorem subd6_4_623 : subd6_4 [3, 0, 5] = true := by decide +kernel
theorem subd6_4_624 : subd6_4 [3, 0, 6] = true := by decide +kernel
theorem subd6_4_625 : subd6_4 [3, 1, -7] = true := by decide +kernel
theorem subd6_4_626 : subd6_4 [3, 1, -6] = true := by decide +kernel
theorem subd6_4_627 : subd6_4 [3, 1, -5] = true := by decide +kernel
theorem subd6_4_628 : subd6_4 [3, 1, -4] = true := by decide +kernel
theorem subd6_4_629 : subd6_4 [3, 1, -3] = true := by decide +kernel
theorem subd6_4_630 : subd6_4 [3, 1, -2] = true := by decide +kernel
theorem subd6_4_631 : subd6_4 [3, 1, -1] = true := by decide +kernel
theorem subd6_4_632 : subd6_4 [3, 1, 0] = true := by decide +kernel
theorem subd6_4_633 : subd6_4 [3, 1, 1] = true := by decide +kernel
theorem subd6_4_634 : subd6_4 [3, 1, 2] = true := by decide +kernel
theorem subd6_4_635 : subd6_4 [3, 1, 3] = true := by decide +kernel
theorem subd6_4_636 : subd6_4 [3, 1, 4] = true := by decide +kernel
theorem subd6_4_637 : subd6_4 [3, 1, 5] = true := by decide +kernel
theorem subd6_4_638 : subd6_4 [3, 2] = true := by decide +kernel
theorem subd6_4_639 : subd6_4 [3, 3] = true := by decide +kernel
theorem sbd6_4_19 : ∀ q ∈ blkd6_4_19, subd6_4 q = true := by
  unfold blkd6_4_19
  exact List.forall_mem_cons.2 ⟨subd6_4_608, List.forall_mem_cons.2 ⟨subd6_4_609, List.forall_mem_cons.2 ⟨subd6_4_610, List.forall_mem_cons.2 ⟨subd6_4_611, List.forall_mem_cons.2 ⟨subd6_4_612, List.forall_mem_cons.2 ⟨subd6_4_613, List.forall_mem_cons.2 ⟨subd6_4_614, List.forall_mem_cons.2 ⟨subd6_4_615, List.forall_mem_cons.2 ⟨subd6_4_616, List.forall_mem_cons.2 ⟨subd6_4_617, List.forall_mem_cons.2 ⟨subd6_4_618, List.forall_mem_cons.2 ⟨subd6_4_619, List.forall_mem_cons.2 ⟨subd6_4_620, List.forall_mem_cons.2 ⟨subd6_4_621, List.forall_mem_cons.2 ⟨subd6_4_622, List.forall_mem_cons.2 ⟨subd6_4_623, List.forall_mem_cons.2 ⟨subd6_4_624, List.forall_mem_cons.2 ⟨subd6_4_625, List.forall_mem_cons.2 ⟨subd6_4_626, List.forall_mem_cons.2 ⟨subd6_4_627, List.forall_mem_cons.2 ⟨subd6_4_628, List.forall_mem_cons.2 ⟨subd6_4_629, List.forall_mem_cons.2 ⟨subd6_4_630, List.forall_mem_cons.2 ⟨subd6_4_631, List.forall_mem_cons.2 ⟨subd6_4_632, List.forall_mem_cons.2 ⟨subd6_4_633, List.forall_mem_cons.2 ⟨subd6_4_634, List.forall_mem_cons.2 ⟨subd6_4_635, List.forall_mem_cons.2 ⟨subd6_4_636, List.forall_mem_cons.2 ⟨subd6_4_637, List.forall_mem_cons.2 ⟨subd6_4_638, List.forall_mem_cons.2 ⟨subd6_4_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_4_640 : subd6_4 [3, 4] = true := by decide +kernel
theorem subd6_4_641 : subd6_4 [3, 5] = true := by decide +kernel
theorem subd6_4_642 : subd6_4 [4, -6] = true := by decide +kernel
theorem subd6_4_643 : subd6_4 [4, -5] = true := by decide +kernel
theorem subd6_4_644 : subd6_4 [4, -4] = true := by decide +kernel
theorem subd6_4_645 : subd6_4 [4, -3] = true := by decide +kernel
theorem subd6_4_646 : subd6_4 [4, -2] = true := by decide +kernel
theorem subd6_4_647 : subd6_4 [4, -1] = true := by decide +kernel
theorem subd6_4_648 : subd6_4 [4, 0] = true := by decide +kernel
theorem subd6_4_649 : subd6_4 [4, 1] = true := by decide +kernel
theorem subd6_4_650 : subd6_4 [4, 2] = true := by decide +kernel
theorem subd6_4_651 : subd6_4 [4, 3] = true := by decide +kernel
theorem subd6_4_652 : subd6_4 [4, 4] = true := by decide +kernel
theorem subd6_4_653 : subd6_4 [5, -5] = true := by decide +kernel
theorem subd6_4_654 : subd6_4 [5, -4] = true := by decide +kernel
theorem subd6_4_655 : subd6_4 [5, -3] = true := by decide +kernel
theorem subd6_4_656 : subd6_4 [5, -2] = true := by decide +kernel
theorem subd6_4_657 : subd6_4 [5, -1] = true := by decide +kernel
theorem subd6_4_658 : subd6_4 [5, 0] = true := by decide +kernel
theorem subd6_4_659 : subd6_4 [5, 1] = true := by decide +kernel
theorem subd6_4_660 : subd6_4 [5, 2] = true := by decide +kernel
theorem subd6_4_661 : subd6_4 [5, 3] = true := by decide +kernel
theorem subd6_4_662 : subd6_4 [6] = true := by decide +kernel
theorem sbd6_4_20 : ∀ q ∈ blkd6_4_20, subd6_4 q = true := by
  unfold blkd6_4_20
  exact List.forall_mem_cons.2 ⟨subd6_4_640, List.forall_mem_cons.2 ⟨subd6_4_641, List.forall_mem_cons.2 ⟨subd6_4_642, List.forall_mem_cons.2 ⟨subd6_4_643, List.forall_mem_cons.2 ⟨subd6_4_644, List.forall_mem_cons.2 ⟨subd6_4_645, List.forall_mem_cons.2 ⟨subd6_4_646, List.forall_mem_cons.2 ⟨subd6_4_647, List.forall_mem_cons.2 ⟨subd6_4_648, List.forall_mem_cons.2 ⟨subd6_4_649, List.forall_mem_cons.2 ⟨subd6_4_650, List.forall_mem_cons.2 ⟨subd6_4_651, List.forall_mem_cons.2 ⟨subd6_4_652, List.forall_mem_cons.2 ⟨subd6_4_653, List.forall_mem_cons.2 ⟨subd6_4_654, List.forall_mem_cons.2 ⟨subd6_4_655, List.forall_mem_cons.2 ⟨subd6_4_656, List.forall_mem_cons.2 ⟨subd6_4_657, List.forall_mem_cons.2 ⟨subd6_4_658, List.forall_mem_cons.2 ⟨subd6_4_659, List.forall_mem_cons.2 ⟨subd6_4_660, List.forall_mem_cons.2 ⟨subd6_4_661, List.forall_mem_cons.2 ⟨subd6_4_662, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_0 : ldCheck G d7_0.U d7_0.ms ldd7_0 = true := by decide +kernel
theorem pre_okd7_0 : subPre G cell7 d7_0 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C110
