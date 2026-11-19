import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_3_352 : subd6_3 [-1, 0, -3] = true := by decide +kernel
theorem subd6_3_353 : subd6_3 [-1, 0, -2] = true := by decide +kernel
theorem subd6_3_354 : subd6_3 [-1, 0, -1] = true := by decide +kernel
theorem subd6_3_355 : subd6_3 [-1, 0, 0] = true := by decide +kernel
theorem subd6_3_356 : subd6_3 [-1, 0, 1] = true := by decide +kernel
theorem subd6_3_357 : subd6_3 [-1, 0, 2] = true := by decide +kernel
theorem subd6_3_358 : subd6_3 [-1, 0, 3] = true := by decide +kernel
theorem subd6_3_359 : subd6_3 [-1, 0, 4] = true := by decide +kernel
theorem subd6_3_360 : subd6_3 [-1, 0, 5] = true := by decide +kernel
theorem subd6_3_361 : subd6_3 [-1, 0, 6] = true := by decide +kernel
theorem subd6_3_362 : subd6_3 [-1, 0, 7] = true := by decide +kernel
theorem subd6_3_363 : subd6_3 [-1, 0, 8] = true := by decide +kernel
theorem subd6_3_364 : subd6_3 [-1, 1, -10] = true := by decide +kernel
theorem subd6_3_365 : subd6_3 [-1, 1, -9] = true := by decide +kernel
theorem subd6_3_366 : subd6_3 [-1, 1, -8] = true := by decide +kernel
theorem subd6_3_367 : subd6_3 [-1, 1, -7] = true := by decide +kernel
theorem subd6_3_368 : subd6_3 [-1, 1, -6] = true := by decide +kernel
theorem subd6_3_369 : subd6_3 [-1, 1, -5] = true := by decide +kernel
theorem subd6_3_370 : subd6_3 [-1, 1, -4] = true := by decide +kernel
theorem subd6_3_371 : subd6_3 [-1, 1, -3] = true := by decide +kernel
theorem subd6_3_372 : subd6_3 [-1, 1, -2] = true := by decide +kernel
theorem subd6_3_373 : subd6_3 [-1, 1, -1] = true := by decide +kernel
theorem subd6_3_374 : subd6_3 [-1, 1, 0] = true := by decide +kernel
theorem subd6_3_375 : subd6_3 [-1, 1, 1] = true := by decide +kernel
theorem subd6_3_376 : subd6_3 [-1, 1, 2] = true := by decide +kernel
theorem subd6_3_377 : subd6_3 [-1, 1, 3] = true := by decide +kernel
theorem subd6_3_378 : subd6_3 [-1, 1, 4] = true := by decide +kernel
theorem subd6_3_379 : subd6_3 [-1, 1, 5] = true := by decide +kernel
theorem subd6_3_380 : subd6_3 [-1, 1, 6] = true := by decide +kernel
theorem subd6_3_381 : subd6_3 [-1, 1, 7] = true := by decide +kernel
theorem subd6_3_382 : subd6_3 [-1, 1, 8] = true := by decide +kernel
theorem subd6_3_383 : subd6_3 [-1, 2, -10] = true := by decide +kernel
theorem sbd6_3_11 : ∀ q ∈ blkd6_3_11, subd6_3 q = true := by
  unfold blkd6_3_11
  exact List.forall_mem_cons.2 ⟨subd6_3_352, List.forall_mem_cons.2 ⟨subd6_3_353, List.forall_mem_cons.2 ⟨subd6_3_354, List.forall_mem_cons.2 ⟨subd6_3_355, List.forall_mem_cons.2 ⟨subd6_3_356, List.forall_mem_cons.2 ⟨subd6_3_357, List.forall_mem_cons.2 ⟨subd6_3_358, List.forall_mem_cons.2 ⟨subd6_3_359, List.forall_mem_cons.2 ⟨subd6_3_360, List.forall_mem_cons.2 ⟨subd6_3_361, List.forall_mem_cons.2 ⟨subd6_3_362, List.forall_mem_cons.2 ⟨subd6_3_363, List.forall_mem_cons.2 ⟨subd6_3_364, List.forall_mem_cons.2 ⟨subd6_3_365, List.forall_mem_cons.2 ⟨subd6_3_366, List.forall_mem_cons.2 ⟨subd6_3_367, List.forall_mem_cons.2 ⟨subd6_3_368, List.forall_mem_cons.2 ⟨subd6_3_369, List.forall_mem_cons.2 ⟨subd6_3_370, List.forall_mem_cons.2 ⟨subd6_3_371, List.forall_mem_cons.2 ⟨subd6_3_372, List.forall_mem_cons.2 ⟨subd6_3_373, List.forall_mem_cons.2 ⟨subd6_3_374, List.forall_mem_cons.2 ⟨subd6_3_375, List.forall_mem_cons.2 ⟨subd6_3_376, List.forall_mem_cons.2 ⟨subd6_3_377, List.forall_mem_cons.2 ⟨subd6_3_378, List.forall_mem_cons.2 ⟨subd6_3_379, List.forall_mem_cons.2 ⟨subd6_3_380, List.forall_mem_cons.2 ⟨subd6_3_381, List.forall_mem_cons.2 ⟨subd6_3_382, List.forall_mem_cons.2 ⟨subd6_3_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_3_384 : subd6_3 [-1, 2, -9] = true := by decide +kernel
theorem subd6_3_385 : subd6_3 [-1, 2, -8] = true := by decide +kernel
theorem subd6_3_386 : subd6_3 [-1, 2, -7] = true := by decide +kernel
theorem subd6_3_387 : subd6_3 [-1, 2, -6] = true := by decide +kernel
theorem subd6_3_388 : subd6_3 [-1, 2, -5] = true := by decide +kernel
theorem subd6_3_389 : subd6_3 [-1, 2, -4] = true := by decide +kernel
theorem subd6_3_390 : subd6_3 [-1, 2, -3] = true := by decide +kernel
theorem subd6_3_391 : subd6_3 [-1, 2, -2] = true := by decide +kernel
theorem subd6_3_392 : subd6_3 [-1, 2, -1] = true := by decide +kernel
theorem subd6_3_393 : subd6_3 [-1, 2, 0] = true := by decide +kernel
theorem subd6_3_394 : subd6_3 [-1, 2, 1] = true := by decide +kernel
theorem subd6_3_395 : subd6_3 [-1, 2, 2] = true := by decide +kernel
theorem subd6_3_396 : subd6_3 [-1, 2, 3] = true := by decide +kernel
theorem subd6_3_397 : subd6_3 [-1, 2, 4] = true := by decide +kernel
theorem subd6_3_398 : subd6_3 [-1, 2, 5] = true := by decide +kernel
theorem subd6_3_399 : subd6_3 [-1, 2, 6] = true := by decide +kernel
theorem subd6_3_400 : subd6_3 [-1, 2, 7] = true := by decide +kernel
theorem subd6_3_401 : subd6_3 [-1, 3, -9] = true := by decide +kernel
theorem subd6_3_402 : subd6_3 [-1, 3, -8] = true := by decide +kernel
theorem subd6_3_403 : subd6_3 [-1, 3, -7] = true := by decide +kernel
theorem subd6_3_404 : subd6_3 [-1, 3, -6] = true := by decide +kernel
theorem subd6_3_405 : subd6_3 [-1, 3, -5] = true := by decide +kernel
theorem subd6_3_406 : subd6_3 [-1, 3, -4] = true := by decide +kernel
theorem subd6_3_407 : subd6_3 [-1, 3, -3] = true := by decide +kernel
theorem subd6_3_408 : subd6_3 [-1, 3, -2] = true := by decide +kernel
theorem subd6_3_409 : subd6_3 [-1, 3, -1] = true := by decide +kernel
theorem subd6_3_410 : subd6_3 [-1, 3, 0] = true := by decide +kernel
theorem subd6_3_411 : subd6_3 [-1, 3, 1] = true := by decide +kernel
theorem subd6_3_412 : subd6_3 [-1, 3, 2] = true := by decide +kernel
theorem subd6_3_413 : subd6_3 [-1, 3, 3] = true := by decide +kernel
theorem subd6_3_414 : subd6_3 [-1, 3, 4] = true := by decide +kernel
theorem subd6_3_415 : subd6_3 [-1, 3, 5] = true := by decide +kernel
theorem sbd6_3_12 : ∀ q ∈ blkd6_3_12, subd6_3 q = true := by
  unfold blkd6_3_12
  exact List.forall_mem_cons.2 ⟨subd6_3_384, List.forall_mem_cons.2 ⟨subd6_3_385, List.forall_mem_cons.2 ⟨subd6_3_386, List.forall_mem_cons.2 ⟨subd6_3_387, List.forall_mem_cons.2 ⟨subd6_3_388, List.forall_mem_cons.2 ⟨subd6_3_389, List.forall_mem_cons.2 ⟨subd6_3_390, List.forall_mem_cons.2 ⟨subd6_3_391, List.forall_mem_cons.2 ⟨subd6_3_392, List.forall_mem_cons.2 ⟨subd6_3_393, List.forall_mem_cons.2 ⟨subd6_3_394, List.forall_mem_cons.2 ⟨subd6_3_395, List.forall_mem_cons.2 ⟨subd6_3_396, List.forall_mem_cons.2 ⟨subd6_3_397, List.forall_mem_cons.2 ⟨subd6_3_398, List.forall_mem_cons.2 ⟨subd6_3_399, List.forall_mem_cons.2 ⟨subd6_3_400, List.forall_mem_cons.2 ⟨subd6_3_401, List.forall_mem_cons.2 ⟨subd6_3_402, List.forall_mem_cons.2 ⟨subd6_3_403, List.forall_mem_cons.2 ⟨subd6_3_404, List.forall_mem_cons.2 ⟨subd6_3_405, List.forall_mem_cons.2 ⟨subd6_3_406, List.forall_mem_cons.2 ⟨subd6_3_407, List.forall_mem_cons.2 ⟨subd6_3_408, List.forall_mem_cons.2 ⟨subd6_3_409, List.forall_mem_cons.2 ⟨subd6_3_410, List.forall_mem_cons.2 ⟨subd6_3_411, List.forall_mem_cons.2 ⟨subd6_3_412, List.forall_mem_cons.2 ⟨subd6_3_413, List.forall_mem_cons.2 ⟨subd6_3_414, List.forall_mem_cons.2 ⟨subd6_3_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_3_416 : subd6_3 [-1, 3, 6] = true := by decide +kernel
theorem subd6_3_417 : subd6_3 [-1, 4, -8] = true := by decide +kernel
theorem subd6_3_418 : subd6_3 [-1, 4, -7] = true := by decide +kernel
theorem subd6_3_419 : subd6_3 [-1, 4, -6] = true := by decide +kernel
theorem subd6_3_420 : subd6_3 [-1, 4, -5] = true := by decide +kernel
theorem subd6_3_421 : subd6_3 [-1, 4, -4] = true := by decide +kernel
theorem subd6_3_422 : subd6_3 [-1, 4, -3] = true := by decide +kernel
theorem subd6_3_423 : subd6_3 [-1, 4, -2] = true := by decide +kernel
theorem subd6_3_424 : subd6_3 [-1, 4, -1] = true := by decide +kernel
theorem subd6_3_425 : subd6_3 [-1, 4, 0] = true := by decide +kernel
theorem subd6_3_426 : subd6_3 [-1, 4, 1] = true := by decide +kernel
theorem subd6_3_427 : subd6_3 [-1, 4, 2] = true := by decide +kernel
theorem subd6_3_428 : subd6_3 [-1, 4, 3] = true := by decide +kernel
theorem subd6_3_429 : subd6_3 [-1, 4, 4] = true := by decide +kernel
theorem subd6_3_430 : subd6_3 [-1, 5] = true := by decide +kernel
theorem subd6_3_431 : subd6_3 [0, -7] = true := by decide +kernel
theorem subd6_3_432 : subd6_3 [0, -6] = true := by decide +kernel
theorem subd6_3_433 : subd6_3 [0, -5] = true := by decide +kernel
theorem subd6_3_434 : subd6_3 [0, -4, -6] = true := by decide +kernel
theorem subd6_3_435 : subd6_3 [0, -4, -5] = true := by decide +kernel
theorem subd6_3_436 : subd6_3 [0, -4, -4] = true := by decide +kernel
theorem subd6_3_437 : subd6_3 [0, -4, -3] = true := by decide +kernel
theorem subd6_3_438 : subd6_3 [0, -4, -2] = true := by decide +kernel
theorem subd6_3_439 : subd6_3 [0, -4, -1] = true := by decide +kernel
theorem subd6_3_440 : subd6_3 [0, -4, 0] = true := by decide +kernel
theorem subd6_3_441 : subd6_3 [0, -4, 1] = true := by decide +kernel
theorem subd6_3_442 : subd6_3 [0, -4, 2] = true := by decide +kernel
theorem subd6_3_443 : subd6_3 [0, -4, 3] = true := by decide +kernel
theorem subd6_3_444 : subd6_3 [0, -4, 4] = true := by decide +kernel
theorem subd6_3_445 : subd6_3 [0, -4, 5] = true := by decide +kernel
theorem subd6_3_446 : subd6_3 [0, -4, 6] = true := by decide +kernel
theorem subd6_3_447 : subd6_3 [0, -4, 7] = true := by decide +kernel
theorem sbd6_3_13 : ∀ q ∈ blkd6_3_13, subd6_3 q = true := by
  unfold blkd6_3_13
  exact List.forall_mem_cons.2 ⟨subd6_3_416, List.forall_mem_cons.2 ⟨subd6_3_417, List.forall_mem_cons.2 ⟨subd6_3_418, List.forall_mem_cons.2 ⟨subd6_3_419, List.forall_mem_cons.2 ⟨subd6_3_420, List.forall_mem_cons.2 ⟨subd6_3_421, List.forall_mem_cons.2 ⟨subd6_3_422, List.forall_mem_cons.2 ⟨subd6_3_423, List.forall_mem_cons.2 ⟨subd6_3_424, List.forall_mem_cons.2 ⟨subd6_3_425, List.forall_mem_cons.2 ⟨subd6_3_426, List.forall_mem_cons.2 ⟨subd6_3_427, List.forall_mem_cons.2 ⟨subd6_3_428, List.forall_mem_cons.2 ⟨subd6_3_429, List.forall_mem_cons.2 ⟨subd6_3_430, List.forall_mem_cons.2 ⟨subd6_3_431, List.forall_mem_cons.2 ⟨subd6_3_432, List.forall_mem_cons.2 ⟨subd6_3_433, List.forall_mem_cons.2 ⟨subd6_3_434, List.forall_mem_cons.2 ⟨subd6_3_435, List.forall_mem_cons.2 ⟨subd6_3_436, List.forall_mem_cons.2 ⟨subd6_3_437, List.forall_mem_cons.2 ⟨subd6_3_438, List.forall_mem_cons.2 ⟨subd6_3_439, List.forall_mem_cons.2 ⟨subd6_3_440, List.forall_mem_cons.2 ⟨subd6_3_441, List.forall_mem_cons.2 ⟨subd6_3_442, List.forall_mem_cons.2 ⟨subd6_3_443, List.forall_mem_cons.2 ⟨subd6_3_444, List.forall_mem_cons.2 ⟨subd6_3_445, List.forall_mem_cons.2 ⟨subd6_3_446, List.forall_mem_cons.2 ⟨subd6_3_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_3_448 : subd6_3 [0, -4, 8] = true := by decide +kernel
theorem subd6_3_449 : subd6_3 [0, -3, -7] = true := by decide +kernel
theorem subd6_3_450 : subd6_3 [0, -3, -6] = true := by decide +kernel
theorem subd6_3_451 : subd6_3 [0, -3, -5] = true := by decide +kernel
theorem subd6_3_452 : subd6_3 [0, -3, -4] = true := by decide +kernel
theorem subd6_3_453 : subd6_3 [0, -3, -3] = true := by decide +kernel
theorem subd6_3_454 : subd6_3 [0, -3, -2] = true := by decide +kernel
theorem subd6_3_455 : subd6_3 [0, -3, -1] = true := by decide +kernel
theorem subd6_3_456 : subd6_3 [0, -3, 0] = true := by decide +kernel
theorem subd6_3_457 : subd6_3 [0, -3, 1] = true := by decide +kernel
theorem subd6_3_458 : subd6_3 [0, -3, 2] = true := by decide +kernel
theorem subd6_3_459 : subd6_3 [0, -3, 3] = true := by decide +kernel
theorem subd6_3_460 : subd6_3 [0, -3, 4] = true := by decide +kernel
theorem subd6_3_461 : subd6_3 [0, -3, 5] = true := by decide +kernel
theorem subd6_3_462 : subd6_3 [0, -3, 6] = true := by decide +kernel
theorem subd6_3_463 : subd6_3 [0, -3, 7] = true := by decide +kernel
theorem subd6_3_464 : subd6_3 [0, -3, 8] = true := by decide +kernel
theorem subd6_3_465 : subd6_3 [0, -2, -8] = true := by decide +kernel
theorem subd6_3_466 : subd6_3 [0, -2, -7] = true := by decide +kernel
theorem subd6_3_467 : subd6_3 [0, -2, -6] = true := by decide +kernel
theorem subd6_3_468 : subd6_3 [0, -2, -5] = true := by decide +kernel
theorem subd6_3_469 : subd6_3 [0, -2, -4] = true := by decide +kernel
theorem subd6_3_470 : subd6_3 [0, -2, -3] = true := by decide +kernel
theorem subd6_3_471 : subd6_3 [0, -2, -2] = true := by decide +kernel
theorem subd6_3_472 : subd6_3 [0, -2, -1] = true := by decide +kernel
theorem subd6_3_473 : subd6_3 [0, -2, 0] = true := by decide +kernel
theorem subd6_3_474 : subd6_3 [0, -2, 1] = true := by decide +kernel
theorem subd6_3_475 : subd6_3 [0, -2, 2] = true := by decide +kernel
theorem subd6_3_476 : subd6_3 [0, -2, 3] = true := by decide +kernel
theorem subd6_3_477 : subd6_3 [0, -2, 4] = true := by decide +kernel
theorem subd6_3_478 : subd6_3 [0, -2, 5] = true := by decide +kernel
theorem subd6_3_479 : subd6_3 [0, -2, 6] = true := by decide +kernel
theorem sbd6_3_14 : ∀ q ∈ blkd6_3_14, subd6_3 q = true := by
  unfold blkd6_3_14
  exact List.forall_mem_cons.2 ⟨subd6_3_448, List.forall_mem_cons.2 ⟨subd6_3_449, List.forall_mem_cons.2 ⟨subd6_3_450, List.forall_mem_cons.2 ⟨subd6_3_451, List.forall_mem_cons.2 ⟨subd6_3_452, List.forall_mem_cons.2 ⟨subd6_3_453, List.forall_mem_cons.2 ⟨subd6_3_454, List.forall_mem_cons.2 ⟨subd6_3_455, List.forall_mem_cons.2 ⟨subd6_3_456, List.forall_mem_cons.2 ⟨subd6_3_457, List.forall_mem_cons.2 ⟨subd6_3_458, List.forall_mem_cons.2 ⟨subd6_3_459, List.forall_mem_cons.2 ⟨subd6_3_460, List.forall_mem_cons.2 ⟨subd6_3_461, List.forall_mem_cons.2 ⟨subd6_3_462, List.forall_mem_cons.2 ⟨subd6_3_463, List.forall_mem_cons.2 ⟨subd6_3_464, List.forall_mem_cons.2 ⟨subd6_3_465, List.forall_mem_cons.2 ⟨subd6_3_466, List.forall_mem_cons.2 ⟨subd6_3_467, List.forall_mem_cons.2 ⟨subd6_3_468, List.forall_mem_cons.2 ⟨subd6_3_469, List.forall_mem_cons.2 ⟨subd6_3_470, List.forall_mem_cons.2 ⟨subd6_3_471, List.forall_mem_cons.2 ⟨subd6_3_472, List.forall_mem_cons.2 ⟨subd6_3_473, List.forall_mem_cons.2 ⟨subd6_3_474, List.forall_mem_cons.2 ⟨subd6_3_475, List.forall_mem_cons.2 ⟨subd6_3_476, List.forall_mem_cons.2 ⟨subd6_3_477, List.forall_mem_cons.2 ⟨subd6_3_478, List.forall_mem_cons.2 ⟨subd6_3_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_3_480 : subd6_3 [0, -2, 7] = true := by decide +kernel
theorem subd6_3_481 : subd6_3 [0, -2, 8] = true := by decide +kernel
theorem subd6_3_482 : subd6_3 [0, -2, 9] = true := by decide +kernel
theorem subd6_3_483 : subd6_3 [0, -1, -9] = true := by decide +kernel
theorem subd6_3_484 : subd6_3 [0, -1, -8] = true := by decide +kernel
theorem subd6_3_485 : subd6_3 [0, -1, -7] = true := by decide +kernel
theorem subd6_3_486 : subd6_3 [0, -1, -6] = true := by decide +kernel
theorem subd6_3_487 : subd6_3 [0, -1, -5] = true := by decide +kernel
theorem subd6_3_488 : subd6_3 [0, -1, -4] = true := by decide +kernel
theorem subd6_3_489 : subd6_3 [0, -1, -3] = true := by decide +kernel
theorem subd6_3_490 : subd6_3 [0, -1, -2] = true := by decide +kernel
theorem subd6_3_491 : subd6_3 [0, -1, -1] = true := by decide +kernel
theorem subd6_3_492 : subd6_3 [0, -1, 0] = true := by decide +kernel
theorem subd6_3_493 : subd6_3 [0, -1, 1] = true := by decide +kernel
theorem subd6_3_494 : subd6_3 [0, -1, 2] = true := by decide +kernel
theorem subd6_3_495 : subd6_3 [0, -1, 3] = true := by decide +kernel
theorem subd6_3_496 : subd6_3 [0, -1, 4] = true := by decide +kernel
theorem subd6_3_497 : subd6_3 [0, -1, 5] = true := by decide +kernel
theorem subd6_3_498 : subd6_3 [0, -1, 6] = true := by decide +kernel
theorem subd6_3_499 : subd6_3 [0, -1, 7] = true := by decide +kernel
theorem subd6_3_500 : subd6_3 [0, -1, 8] = true := by decide +kernel
theorem subd6_3_501 : subd6_3 [0, -1, 9] = true := by decide +kernel
theorem subd6_3_502 : subd6_3 [0, 0, -10] = true := by decide +kernel
theorem subd6_3_503 : subd6_3 [0, 0, -9] = true := by decide +kernel
theorem subd6_3_504 : subd6_3 [0, 0, -8] = true := by decide +kernel
theorem subd6_3_505 : subd6_3 [0, 0, -7] = true := by decide +kernel
theorem subd6_3_506 : subd6_3 [0, 0, -6] = true := by decide +kernel
theorem subd6_3_507 : subd6_3 [0, 0, -5] = true := by decide +kernel
theorem subd6_3_508 : subd6_3 [0, 0, -4] = true := by decide +kernel
theorem subd6_3_509 : subd6_3 [0, 0, -3] = true := by decide +kernel
theorem subd6_3_510 : subd6_3 [0, 0, -2] = true := by decide +kernel
theorem subd6_3_511 : subd6_3 [0, 0, -1] = true := by decide +kernel
theorem sbd6_3_15 : ∀ q ∈ blkd6_3_15, subd6_3 q = true := by
  unfold blkd6_3_15
  exact List.forall_mem_cons.2 ⟨subd6_3_480, List.forall_mem_cons.2 ⟨subd6_3_481, List.forall_mem_cons.2 ⟨subd6_3_482, List.forall_mem_cons.2 ⟨subd6_3_483, List.forall_mem_cons.2 ⟨subd6_3_484, List.forall_mem_cons.2 ⟨subd6_3_485, List.forall_mem_cons.2 ⟨subd6_3_486, List.forall_mem_cons.2 ⟨subd6_3_487, List.forall_mem_cons.2 ⟨subd6_3_488, List.forall_mem_cons.2 ⟨subd6_3_489, List.forall_mem_cons.2 ⟨subd6_3_490, List.forall_mem_cons.2 ⟨subd6_3_491, List.forall_mem_cons.2 ⟨subd6_3_492, List.forall_mem_cons.2 ⟨subd6_3_493, List.forall_mem_cons.2 ⟨subd6_3_494, List.forall_mem_cons.2 ⟨subd6_3_495, List.forall_mem_cons.2 ⟨subd6_3_496, List.forall_mem_cons.2 ⟨subd6_3_497, List.forall_mem_cons.2 ⟨subd6_3_498, List.forall_mem_cons.2 ⟨subd6_3_499, List.forall_mem_cons.2 ⟨subd6_3_500, List.forall_mem_cons.2 ⟨subd6_3_501, List.forall_mem_cons.2 ⟨subd6_3_502, List.forall_mem_cons.2 ⟨subd6_3_503, List.forall_mem_cons.2 ⟨subd6_3_504, List.forall_mem_cons.2 ⟨subd6_3_505, List.forall_mem_cons.2 ⟨subd6_3_506, List.forall_mem_cons.2 ⟨subd6_3_507, List.forall_mem_cons.2 ⟨subd6_3_508, List.forall_mem_cons.2 ⟨subd6_3_509, List.forall_mem_cons.2 ⟨subd6_3_510, List.forall_mem_cons.2 ⟨subd6_3_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_3_512 : subd6_3 [0, 0, 0] = true := by decide +kernel
theorem subd6_3_513 : subd6_3 [0, 0, 1] = true := by decide +kernel
theorem subd6_3_514 : subd6_3 [0, 0, 2] = true := by decide +kernel
theorem subd6_3_515 : subd6_3 [0, 0, 3] = true := by decide +kernel
theorem subd6_3_516 : subd6_3 [0, 0, 4] = true := by decide +kernel
theorem subd6_3_517 : subd6_3 [0, 0, 5] = true := by decide +kernel
theorem subd6_3_518 : subd6_3 [0, 0, 6] = true := by decide +kernel
theorem subd6_3_519 : subd6_3 [0, 0, 7] = true := by decide +kernel
theorem subd6_3_520 : subd6_3 [0, 0, 8] = true := by decide +kernel
theorem subd6_3_521 : subd6_3 [0, 0, 9] = true := by decide +kernel
theorem subd6_3_522 : subd6_3 [0, 1, -10] = true := by decide +kernel
theorem subd6_3_523 : subd6_3 [0, 1, -9] = true := by decide +kernel
theorem subd6_3_524 : subd6_3 [0, 1, -8] = true := by decide +kernel
theorem subd6_3_525 : subd6_3 [0, 1, -7] = true := by decide +kernel
theorem subd6_3_526 : subd6_3 [0, 1, -6] = true := by decide +kernel
theorem subd6_3_527 : subd6_3 [0, 1, -5] = true := by decide +kernel
theorem subd6_3_528 : subd6_3 [0, 1, -4] = true := by decide +kernel
theorem subd6_3_529 : subd6_3 [0, 1, -3] = true := by decide +kernel
theorem subd6_3_530 : subd6_3 [0, 1, -2] = true := by decide +kernel
theorem subd6_3_531 : subd6_3 [0, 1, -1] = true := by decide +kernel
theorem subd6_3_532 : subd6_3 [0, 1, 0] = true := by decide +kernel
theorem subd6_3_533 : subd6_3 [0, 1, 1] = true := by decide +kernel
theorem subd6_3_534 : subd6_3 [0, 1, 2] = true := by decide +kernel
theorem subd6_3_535 : subd6_3 [0, 1, 3] = true := by decide +kernel
theorem subd6_3_536 : subd6_3 [0, 1, 4] = true := by decide +kernel
theorem subd6_3_537 : subd6_3 [0, 1, 5] = true := by decide +kernel
theorem subd6_3_538 : subd6_3 [0, 1, 6] = true := by decide +kernel
theorem subd6_3_539 : subd6_3 [0, 1, 7] = true := by decide +kernel
theorem subd6_3_540 : subd6_3 [0, 1, 8] = true := by decide +kernel
theorem subd6_3_541 : subd6_3 [0, 2, -10] = true := by decide +kernel
theorem subd6_3_542 : subd6_3 [0, 2, -9] = true := by decide +kernel
theorem subd6_3_543 : subd6_3 [0, 2, -8] = true := by decide +kernel
theorem sbd6_3_16 : ∀ q ∈ blkd6_3_16, subd6_3 q = true := by
  unfold blkd6_3_16
  exact List.forall_mem_cons.2 ⟨subd6_3_512, List.forall_mem_cons.2 ⟨subd6_3_513, List.forall_mem_cons.2 ⟨subd6_3_514, List.forall_mem_cons.2 ⟨subd6_3_515, List.forall_mem_cons.2 ⟨subd6_3_516, List.forall_mem_cons.2 ⟨subd6_3_517, List.forall_mem_cons.2 ⟨subd6_3_518, List.forall_mem_cons.2 ⟨subd6_3_519, List.forall_mem_cons.2 ⟨subd6_3_520, List.forall_mem_cons.2 ⟨subd6_3_521, List.forall_mem_cons.2 ⟨subd6_3_522, List.forall_mem_cons.2 ⟨subd6_3_523, List.forall_mem_cons.2 ⟨subd6_3_524, List.forall_mem_cons.2 ⟨subd6_3_525, List.forall_mem_cons.2 ⟨subd6_3_526, List.forall_mem_cons.2 ⟨subd6_3_527, List.forall_mem_cons.2 ⟨subd6_3_528, List.forall_mem_cons.2 ⟨subd6_3_529, List.forall_mem_cons.2 ⟨subd6_3_530, List.forall_mem_cons.2 ⟨subd6_3_531, List.forall_mem_cons.2 ⟨subd6_3_532, List.forall_mem_cons.2 ⟨subd6_3_533, List.forall_mem_cons.2 ⟨subd6_3_534, List.forall_mem_cons.2 ⟨subd6_3_535, List.forall_mem_cons.2 ⟨subd6_3_536, List.forall_mem_cons.2 ⟨subd6_3_537, List.forall_mem_cons.2 ⟨subd6_3_538, List.forall_mem_cons.2 ⟨subd6_3_539, List.forall_mem_cons.2 ⟨subd6_3_540, List.forall_mem_cons.2 ⟨subd6_3_541, List.forall_mem_cons.2 ⟨subd6_3_542, List.forall_mem_cons.2 ⟨subd6_3_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_3_544 : subd6_3 [0, 2, -7] = true := by decide +kernel
theorem subd6_3_545 : subd6_3 [0, 2, -6] = true := by decide +kernel
theorem subd6_3_546 : subd6_3 [0, 2, -5] = true := by decide +kernel
theorem subd6_3_547 : subd6_3 [0, 2, -4] = true := by decide +kernel
theorem subd6_3_548 : subd6_3 [0, 2, -3] = true := by decide +kernel
theorem subd6_3_549 : subd6_3 [0, 2, -2] = true := by decide +kernel
theorem subd6_3_550 : subd6_3 [0, 2, -1] = true := by decide +kernel
theorem subd6_3_551 : subd6_3 [0, 2, 0] = true := by decide +kernel
theorem subd6_3_552 : subd6_3 [0, 2, 1] = true := by decide +kernel
theorem subd6_3_553 : subd6_3 [0, 2, 2] = true := by decide +kernel
theorem subd6_3_554 : subd6_3 [0, 2, 3] = true := by decide +kernel
theorem subd6_3_555 : subd6_3 [0, 2, 4] = true := by decide +kernel
theorem subd6_3_556 : subd6_3 [0, 2, 5] = true := by decide +kernel
theorem subd6_3_557 : subd6_3 [0, 2, 6] = true := by decide +kernel
theorem subd6_3_558 : subd6_3 [0, 2, 7] = true := by decide +kernel
theorem subd6_3_559 : subd6_3 [0, 3, -9] = true := by decide +kernel
theorem subd6_3_560 : subd6_3 [0, 3, -8] = true := by decide +kernel
theorem subd6_3_561 : subd6_3 [0, 3, -7] = true := by decide +kernel
theorem subd6_3_562 : subd6_3 [0, 3, -6] = true := by decide +kernel
theorem subd6_3_563 : subd6_3 [0, 3, -5] = true := by decide +kernel
theorem subd6_3_564 : subd6_3 [0, 3, -4] = true := by decide +kernel
theorem subd6_3_565 : subd6_3 [0, 3, -3] = true := by decide +kernel
theorem subd6_3_566 : subd6_3 [0, 3, -2] = true := by decide +kernel
theorem subd6_3_567 : subd6_3 [0, 3, -1] = true := by decide +kernel
theorem subd6_3_568 : subd6_3 [0, 3, 0] = true := by decide +kernel
theorem subd6_3_569 : subd6_3 [0, 3, 1] = true := by decide +kernel
theorem subd6_3_570 : subd6_3 [0, 3, 2] = true := by decide +kernel
theorem subd6_3_571 : subd6_3 [0, 3, 3] = true := by decide +kernel
theorem subd6_3_572 : subd6_3 [0, 3, 4] = true := by decide +kernel
theorem subd6_3_573 : subd6_3 [0, 3, 5] = true := by decide +kernel
theorem subd6_3_574 : subd6_3 [0, 3, 6] = true := by decide +kernel
theorem subd6_3_575 : subd6_3 [0, 4, -9] = true := by decide +kernel
theorem sbd6_3_17 : ∀ q ∈ blkd6_3_17, subd6_3 q = true := by
  unfold blkd6_3_17
  exact List.forall_mem_cons.2 ⟨subd6_3_544, List.forall_mem_cons.2 ⟨subd6_3_545, List.forall_mem_cons.2 ⟨subd6_3_546, List.forall_mem_cons.2 ⟨subd6_3_547, List.forall_mem_cons.2 ⟨subd6_3_548, List.forall_mem_cons.2 ⟨subd6_3_549, List.forall_mem_cons.2 ⟨subd6_3_550, List.forall_mem_cons.2 ⟨subd6_3_551, List.forall_mem_cons.2 ⟨subd6_3_552, List.forall_mem_cons.2 ⟨subd6_3_553, List.forall_mem_cons.2 ⟨subd6_3_554, List.forall_mem_cons.2 ⟨subd6_3_555, List.forall_mem_cons.2 ⟨subd6_3_556, List.forall_mem_cons.2 ⟨subd6_3_557, List.forall_mem_cons.2 ⟨subd6_3_558, List.forall_mem_cons.2 ⟨subd6_3_559, List.forall_mem_cons.2 ⟨subd6_3_560, List.forall_mem_cons.2 ⟨subd6_3_561, List.forall_mem_cons.2 ⟨subd6_3_562, List.forall_mem_cons.2 ⟨subd6_3_563, List.forall_mem_cons.2 ⟨subd6_3_564, List.forall_mem_cons.2 ⟨subd6_3_565, List.forall_mem_cons.2 ⟨subd6_3_566, List.forall_mem_cons.2 ⟨subd6_3_567, List.forall_mem_cons.2 ⟨subd6_3_568, List.forall_mem_cons.2 ⟨subd6_3_569, List.forall_mem_cons.2 ⟨subd6_3_570, List.forall_mem_cons.2 ⟨subd6_3_571, List.forall_mem_cons.2 ⟨subd6_3_572, List.forall_mem_cons.2 ⟨subd6_3_573, List.forall_mem_cons.2 ⟨subd6_3_574, List.forall_mem_cons.2 ⟨subd6_3_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_3_576 : subd6_3 [0, 4, -8] = true := by decide +kernel
theorem subd6_3_577 : subd6_3 [0, 4, -7] = true := by decide +kernel
theorem subd6_3_578 : subd6_3 [0, 4, -6] = true := by decide +kernel
theorem subd6_3_579 : subd6_3 [0, 4, -5] = true := by decide +kernel
theorem subd6_3_580 : subd6_3 [0, 4, -4] = true := by decide +kernel
theorem subd6_3_581 : subd6_3 [0, 4, -3] = true := by decide +kernel
theorem subd6_3_582 : subd6_3 [0, 4, -2] = true := by decide +kernel
theorem subd6_3_583 : subd6_3 [0, 4, -1] = true := by decide +kernel
theorem subd6_3_584 : subd6_3 [0, 4, 0] = true := by decide +kernel
theorem subd6_3_585 : subd6_3 [0, 4, 1] = true := by decide +kernel
theorem subd6_3_586 : subd6_3 [0, 4, 2] = true := by decide +kernel
theorem subd6_3_587 : subd6_3 [0, 4, 3] = true := by decide +kernel
theorem subd6_3_588 : subd6_3 [0, 4, 4] = true := by decide +kernel
theorem subd6_3_589 : subd6_3 [0, 4, 5] = true := by decide +kernel
theorem subd6_3_590 : subd6_3 [0, 5] = true := by decide +kernel
theorem subd6_3_591 : subd6_3 [0, 6] = true := by decide +kernel
theorem subd6_3_592 : subd6_3 [1, -6] = true := by decide +kernel
theorem subd6_3_593 : subd6_3 [1, -5] = true := by decide +kernel
theorem subd6_3_594 : subd6_3 [1, -4, -5] = true := by decide +kernel
theorem subd6_3_595 : subd6_3 [1, -4, -4] = true := by decide +kernel
theorem subd6_3_596 : subd6_3 [1, -4, -3] = true := by decide +kernel
theorem subd6_3_597 : subd6_3 [1, -4, -2] = true := by decide +kernel
theorem subd6_3_598 : subd6_3 [1, -4, -1] = true := by decide +kernel
theorem subd6_3_599 : subd6_3 [1, -4, 0] = true := by decide +kernel
theorem subd6_3_600 : subd6_3 [1, -4, 1] = true := by decide +kernel
theorem subd6_3_601 : subd6_3 [1, -4, 2] = true := by decide +kernel
theorem subd6_3_602 : subd6_3 [1, -4, 3] = true := by decide +kernel
theorem subd6_3_603 : subd6_3 [1, -4, 4] = true := by decide +kernel
theorem subd6_3_604 : subd6_3 [1, -4, 5] = true := by decide +kernel
theorem subd6_3_605 : subd6_3 [1, -4, 6] = true := by decide +kernel
theorem subd6_3_606 : subd6_3 [1, -4, 7] = true := by decide +kernel
theorem subd6_3_607 : subd6_3 [1, -3, -7] = true := by decide +kernel
theorem sbd6_3_18 : ∀ q ∈ blkd6_3_18, subd6_3 q = true := by
  unfold blkd6_3_18
  exact List.forall_mem_cons.2 ⟨subd6_3_576, List.forall_mem_cons.2 ⟨subd6_3_577, List.forall_mem_cons.2 ⟨subd6_3_578, List.forall_mem_cons.2 ⟨subd6_3_579, List.forall_mem_cons.2 ⟨subd6_3_580, List.forall_mem_cons.2 ⟨subd6_3_581, List.forall_mem_cons.2 ⟨subd6_3_582, List.forall_mem_cons.2 ⟨subd6_3_583, List.forall_mem_cons.2 ⟨subd6_3_584, List.forall_mem_cons.2 ⟨subd6_3_585, List.forall_mem_cons.2 ⟨subd6_3_586, List.forall_mem_cons.2 ⟨subd6_3_587, List.forall_mem_cons.2 ⟨subd6_3_588, List.forall_mem_cons.2 ⟨subd6_3_589, List.forall_mem_cons.2 ⟨subd6_3_590, List.forall_mem_cons.2 ⟨subd6_3_591, List.forall_mem_cons.2 ⟨subd6_3_592, List.forall_mem_cons.2 ⟨subd6_3_593, List.forall_mem_cons.2 ⟨subd6_3_594, List.forall_mem_cons.2 ⟨subd6_3_595, List.forall_mem_cons.2 ⟨subd6_3_596, List.forall_mem_cons.2 ⟨subd6_3_597, List.forall_mem_cons.2 ⟨subd6_3_598, List.forall_mem_cons.2 ⟨subd6_3_599, List.forall_mem_cons.2 ⟨subd6_3_600, List.forall_mem_cons.2 ⟨subd6_3_601, List.forall_mem_cons.2 ⟨subd6_3_602, List.forall_mem_cons.2 ⟨subd6_3_603, List.forall_mem_cons.2 ⟨subd6_3_604, List.forall_mem_cons.2 ⟨subd6_3_605, List.forall_mem_cons.2 ⟨subd6_3_606, List.forall_mem_cons.2 ⟨subd6_3_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_3_608 : subd6_3 [1, -3, -6] = true := by decide +kernel
theorem subd6_3_609 : subd6_3 [1, -3, -5] = true := by decide +kernel
theorem subd6_3_610 : subd6_3 [1, -3, -4] = true := by decide +kernel
theorem subd6_3_611 : subd6_3 [1, -3, -3] = true := by decide +kernel
theorem subd6_3_612 : subd6_3 [1, -3, -2] = true := by decide +kernel
theorem subd6_3_613 : subd6_3 [1, -3, -1] = true := by decide +kernel
theorem subd6_3_614 : subd6_3 [1, -3, 0] = true := by decide +kernel
theorem subd6_3_615 : subd6_3 [1, -3, 1] = true := by decide +kernel
theorem subd6_3_616 : subd6_3 [1, -3, 2] = true := by decide +kernel
theorem subd6_3_617 : subd6_3 [1, -3, 3] = true := by decide +kernel
theorem subd6_3_618 : subd6_3 [1, -3, 4] = true := by decide +kernel
theorem subd6_3_619 : subd6_3 [1, -3, 5] = true := by decide +kernel
theorem subd6_3_620 : subd6_3 [1, -3, 6] = true := by decide +kernel
theorem subd6_3_621 : subd6_3 [1, -3, 7] = true := by decide +kernel
theorem subd6_3_622 : subd6_3 [1, -3, 8] = true := by decide +kernel
theorem subd6_3_623 : subd6_3 [1, -2, -8] = true := by decide +kernel
theorem subd6_3_624 : subd6_3 [1, -2, -7] = true := by decide +kernel
theorem subd6_3_625 : subd6_3 [1, -2, -6] = true := by decide +kernel
theorem subd6_3_626 : subd6_3 [1, -2, -5] = true := by decide +kernel
theorem subd6_3_627 : subd6_3 [1, -2, -4] = true := by decide +kernel
theorem subd6_3_628 : subd6_3 [1, -2, -3] = true := by decide +kernel
theorem subd6_3_629 : subd6_3 [1, -2, -2] = true := by decide +kernel
theorem subd6_3_630 : subd6_3 [1, -2, -1] = true := by decide +kernel
theorem subd6_3_631 : subd6_3 [1, -2, 0] = true := by decide +kernel
theorem subd6_3_632 : subd6_3 [1, -2, 1] = true := by decide +kernel
theorem subd6_3_633 : subd6_3 [1, -2, 2] = true := by decide +kernel
theorem subd6_3_634 : subd6_3 [1, -2, 3] = true := by decide +kernel
theorem subd6_3_635 : subd6_3 [1, -2, 4] = true := by decide +kernel
theorem subd6_3_636 : subd6_3 [1, -2, 5] = true := by decide +kernel
theorem subd6_3_637 : subd6_3 [1, -2, 6] = true := by decide +kernel
theorem subd6_3_638 : subd6_3 [1, -2, 7] = true := by decide +kernel
theorem subd6_3_639 : subd6_3 [1, -2, 8] = true := by decide +kernel
theorem sbd6_3_19 : ∀ q ∈ blkd6_3_19, subd6_3 q = true := by
  unfold blkd6_3_19
  exact List.forall_mem_cons.2 ⟨subd6_3_608, List.forall_mem_cons.2 ⟨subd6_3_609, List.forall_mem_cons.2 ⟨subd6_3_610, List.forall_mem_cons.2 ⟨subd6_3_611, List.forall_mem_cons.2 ⟨subd6_3_612, List.forall_mem_cons.2 ⟨subd6_3_613, List.forall_mem_cons.2 ⟨subd6_3_614, List.forall_mem_cons.2 ⟨subd6_3_615, List.forall_mem_cons.2 ⟨subd6_3_616, List.forall_mem_cons.2 ⟨subd6_3_617, List.forall_mem_cons.2 ⟨subd6_3_618, List.forall_mem_cons.2 ⟨subd6_3_619, List.forall_mem_cons.2 ⟨subd6_3_620, List.forall_mem_cons.2 ⟨subd6_3_621, List.forall_mem_cons.2 ⟨subd6_3_622, List.forall_mem_cons.2 ⟨subd6_3_623, List.forall_mem_cons.2 ⟨subd6_3_624, List.forall_mem_cons.2 ⟨subd6_3_625, List.forall_mem_cons.2 ⟨subd6_3_626, List.forall_mem_cons.2 ⟨subd6_3_627, List.forall_mem_cons.2 ⟨subd6_3_628, List.forall_mem_cons.2 ⟨subd6_3_629, List.forall_mem_cons.2 ⟨subd6_3_630, List.forall_mem_cons.2 ⟨subd6_3_631, List.forall_mem_cons.2 ⟨subd6_3_632, List.forall_mem_cons.2 ⟨subd6_3_633, List.forall_mem_cons.2 ⟨subd6_3_634, List.forall_mem_cons.2 ⟨subd6_3_635, List.forall_mem_cons.2 ⟨subd6_3_636, List.forall_mem_cons.2 ⟨subd6_3_637, List.forall_mem_cons.2 ⟨subd6_3_638, List.forall_mem_cons.2 ⟨subd6_3_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_3_640 : subd6_3 [1, -2, 9] = true := by decide +kernel
theorem subd6_3_641 : subd6_3 [1, -1, -9] = true := by decide +kernel
theorem subd6_3_642 : subd6_3 [1, -1, -8] = true := by decide +kernel
theorem subd6_3_643 : subd6_3 [1, -1, -7] = true := by decide +kernel
theorem subd6_3_644 : subd6_3 [1, -1, -6] = true := by decide +kernel
theorem subd6_3_645 : subd6_3 [1, -1, -5] = true := by decide +kernel
theorem subd6_3_646 : subd6_3 [1, -1, -4] = true := by decide +kernel
theorem subd6_3_647 : subd6_3 [1, -1, -3] = true := by decide +kernel
theorem subd6_3_648 : subd6_3 [1, -1, -2] = true := by decide +kernel
theorem subd6_3_649 : subd6_3 [1, -1, -1] = true := by decide +kernel
theorem subd6_3_650 : subd6_3 [1, -1, 0] = true := by decide +kernel
theorem subd6_3_651 : subd6_3 [1, -1, 1] = true := by decide +kernel
theorem subd6_3_652 : subd6_3 [1, -1, 2] = true := by decide +kernel
theorem subd6_3_653 : subd6_3 [1, -1, 3] = true := by decide +kernel
theorem subd6_3_654 : subd6_3 [1, -1, 4] = true := by decide +kernel
theorem subd6_3_655 : subd6_3 [1, -1, 5] = true := by decide +kernel
theorem subd6_3_656 : subd6_3 [1, -1, 6] = true := by decide +kernel
theorem subd6_3_657 : subd6_3 [1, -1, 7] = true := by decide +kernel
theorem subd6_3_658 : subd6_3 [1, -1, 8] = true := by decide +kernel
theorem subd6_3_659 : subd6_3 [1, -1, 9] = true := by decide +kernel
theorem subd6_3_660 : subd6_3 [1, 0, -9] = true := by decide +kernel
theorem subd6_3_661 : subd6_3 [1, 0, -8] = true := by decide +kernel
theorem subd6_3_662 : subd6_3 [1, 0, -7] = true := by decide +kernel
theorem subd6_3_663 : subd6_3 [1, 0, -6] = true := by decide +kernel
theorem subd6_3_664 : subd6_3 [1, 0, -5] = true := by decide +kernel
theorem subd6_3_665 : subd6_3 [1, 0, -4] = true := by decide +kernel
theorem subd6_3_666 : subd6_3 [1, 0, -3] = true := by decide +kernel
theorem subd6_3_667 : subd6_3 [1, 0, -2] = true := by decide +kernel
theorem subd6_3_668 : subd6_3 [1, 0, -1] = true := by decide +kernel
theorem subd6_3_669 : subd6_3 [1, 0, 0] = true := by decide +kernel
theorem subd6_3_670 : subd6_3 [1, 0, 1] = true := by decide +kernel
theorem subd6_3_671 : subd6_3 [1, 0, 2] = true := by decide +kernel
theorem sbd6_3_20 : ∀ q ∈ blkd6_3_20, subd6_3 q = true := by
  unfold blkd6_3_20
  exact List.forall_mem_cons.2 ⟨subd6_3_640, List.forall_mem_cons.2 ⟨subd6_3_641, List.forall_mem_cons.2 ⟨subd6_3_642, List.forall_mem_cons.2 ⟨subd6_3_643, List.forall_mem_cons.2 ⟨subd6_3_644, List.forall_mem_cons.2 ⟨subd6_3_645, List.forall_mem_cons.2 ⟨subd6_3_646, List.forall_mem_cons.2 ⟨subd6_3_647, List.forall_mem_cons.2 ⟨subd6_3_648, List.forall_mem_cons.2 ⟨subd6_3_649, List.forall_mem_cons.2 ⟨subd6_3_650, List.forall_mem_cons.2 ⟨subd6_3_651, List.forall_mem_cons.2 ⟨subd6_3_652, List.forall_mem_cons.2 ⟨subd6_3_653, List.forall_mem_cons.2 ⟨subd6_3_654, List.forall_mem_cons.2 ⟨subd6_3_655, List.forall_mem_cons.2 ⟨subd6_3_656, List.forall_mem_cons.2 ⟨subd6_3_657, List.forall_mem_cons.2 ⟨subd6_3_658, List.forall_mem_cons.2 ⟨subd6_3_659, List.forall_mem_cons.2 ⟨subd6_3_660, List.forall_mem_cons.2 ⟨subd6_3_661, List.forall_mem_cons.2 ⟨subd6_3_662, List.forall_mem_cons.2 ⟨subd6_3_663, List.forall_mem_cons.2 ⟨subd6_3_664, List.forall_mem_cons.2 ⟨subd6_3_665, List.forall_mem_cons.2 ⟨subd6_3_666, List.forall_mem_cons.2 ⟨subd6_3_667, List.forall_mem_cons.2 ⟨subd6_3_668, List.forall_mem_cons.2 ⟨subd6_3_669, List.forall_mem_cons.2 ⟨subd6_3_670, List.forall_mem_cons.2 ⟨subd6_3_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_3_672 : subd6_3 [1, 0, 3] = true := by decide +kernel
theorem subd6_3_673 : subd6_3 [1, 0, 4] = true := by decide +kernel
theorem subd6_3_674 : subd6_3 [1, 0, 5] = true := by decide +kernel
theorem subd6_3_675 : subd6_3 [1, 0, 6] = true := by decide +kernel
theorem subd6_3_676 : subd6_3 [1, 0, 7] = true := by decide +kernel
theorem subd6_3_677 : subd6_3 [1, 0, 8] = true := by decide +kernel
theorem subd6_3_678 : subd6_3 [1, 0, 9] = true := by decide +kernel
theorem subd6_3_679 : subd6_3 [1, 1, -9] = true := by decide +kernel
theorem subd6_3_680 : subd6_3 [1, 1, -8] = true := by decide +kernel
theorem subd6_3_681 : subd6_3 [1, 1, -7] = true := by decide +kernel
theorem subd6_3_682 : subd6_3 [1, 1, -6] = true := by decide +kernel
theorem subd6_3_683 : subd6_3 [1, 1, -5] = true := by decide +kernel
theorem subd6_3_684 : subd6_3 [1, 1, -4] = true := by decide +kernel
theorem subd6_3_685 : subd6_3 [1, 1, -3] = true := by decide +kernel
theorem subd6_3_686 : subd6_3 [1, 1, -2] = true := by decide +kernel
theorem subd6_3_687 : subd6_3 [1, 1, -1] = true := by decide +kernel
theorem subd6_3_688 : subd6_3 [1, 1, 0] = true := by decide +kernel
theorem subd6_3_689 : subd6_3 [1, 1, 1] = true := by decide +kernel
theorem subd6_3_690 : subd6_3 [1, 1, 2] = true := by decide +kernel
theorem subd6_3_691 : subd6_3 [1, 1, 3] = true := by decide +kernel
theorem subd6_3_692 : subd6_3 [1, 1, 4] = true := by decide +kernel
theorem subd6_3_693 : subd6_3 [1, 1, 5] = true := by decide +kernel
theorem subd6_3_694 : subd6_3 [1, 1, 6] = true := by decide +kernel
theorem subd6_3_695 : subd6_3 [1, 1, 7] = true := by decide +kernel
theorem subd6_3_696 : subd6_3 [1, 1, 8] = true := by decide +kernel
theorem subd6_3_697 : subd6_3 [1, 2, -9] = true := by decide +kernel
theorem subd6_3_698 : subd6_3 [1, 2, -8] = true := by decide +kernel
theorem subd6_3_699 : subd6_3 [1, 2, -7] = true := by decide +kernel
theorem subd6_3_700 : subd6_3 [1, 2, -6] = true := by decide +kernel
theorem subd6_3_701 : subd6_3 [1, 2, -5] = true := by decide +kernel
theorem subd6_3_702 : subd6_3 [1, 2, -4] = true := by decide +kernel
theorem subd6_3_703 : subd6_3 [1, 2, -3] = true := by decide +kernel
theorem sbd6_3_21 : ∀ q ∈ blkd6_3_21, subd6_3 q = true := by
  unfold blkd6_3_21
  exact List.forall_mem_cons.2 ⟨subd6_3_672, List.forall_mem_cons.2 ⟨subd6_3_673, List.forall_mem_cons.2 ⟨subd6_3_674, List.forall_mem_cons.2 ⟨subd6_3_675, List.forall_mem_cons.2 ⟨subd6_3_676, List.forall_mem_cons.2 ⟨subd6_3_677, List.forall_mem_cons.2 ⟨subd6_3_678, List.forall_mem_cons.2 ⟨subd6_3_679, List.forall_mem_cons.2 ⟨subd6_3_680, List.forall_mem_cons.2 ⟨subd6_3_681, List.forall_mem_cons.2 ⟨subd6_3_682, List.forall_mem_cons.2 ⟨subd6_3_683, List.forall_mem_cons.2 ⟨subd6_3_684, List.forall_mem_cons.2 ⟨subd6_3_685, List.forall_mem_cons.2 ⟨subd6_3_686, List.forall_mem_cons.2 ⟨subd6_3_687, List.forall_mem_cons.2 ⟨subd6_3_688, List.forall_mem_cons.2 ⟨subd6_3_689, List.forall_mem_cons.2 ⟨subd6_3_690, List.forall_mem_cons.2 ⟨subd6_3_691, List.forall_mem_cons.2 ⟨subd6_3_692, List.forall_mem_cons.2 ⟨subd6_3_693, List.forall_mem_cons.2 ⟨subd6_3_694, List.forall_mem_cons.2 ⟨subd6_3_695, List.forall_mem_cons.2 ⟨subd6_3_696, List.forall_mem_cons.2 ⟨subd6_3_697, List.forall_mem_cons.2 ⟨subd6_3_698, List.forall_mem_cons.2 ⟨subd6_3_699, List.forall_mem_cons.2 ⟨subd6_3_700, List.forall_mem_cons.2 ⟨subd6_3_701, List.forall_mem_cons.2 ⟨subd6_3_702, List.forall_mem_cons.2 ⟨subd6_3_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_3_704 : subd6_3 [1, 2, -2] = true := by decide +kernel
theorem subd6_3_705 : subd6_3 [1, 2, -1] = true := by decide +kernel
theorem subd6_3_706 : subd6_3 [1, 2, 0] = true := by decide +kernel
theorem subd6_3_707 : subd6_3 [1, 2, 1] = true := by decide +kernel
theorem subd6_3_708 : subd6_3 [1, 2, 2] = true := by decide +kernel
theorem subd6_3_709 : subd6_3 [1, 2, 3] = true := by decide +kernel
theorem subd6_3_710 : subd6_3 [1, 2, 4] = true := by decide +kernel
theorem subd6_3_711 : subd6_3 [1, 2, 5] = true := by decide +kernel
theorem subd6_3_712 : subd6_3 [1, 2, 6] = true := by decide +kernel
theorem subd6_3_713 : subd6_3 [1, 2, 7] = true := by decide +kernel
theorem subd6_3_714 : subd6_3 [1, 3, -9] = true := by decide +kernel
theorem subd6_3_715 : subd6_3 [1, 3, -8] = true := by decide +kernel
theorem subd6_3_716 : subd6_3 [1, 3, -7] = true := by decide +kernel
theorem subd6_3_717 : subd6_3 [1, 3, -6] = true := by decide +kernel
theorem subd6_3_718 : subd6_3 [1, 3, -5] = true := by decide +kernel
theorem subd6_3_719 : subd6_3 [1, 3, -4] = true := by decide +kernel
theorem subd6_3_720 : subd6_3 [1, 3, -3] = true := by decide +kernel
theorem subd6_3_721 : subd6_3 [1, 3, -2] = true := by decide +kernel
theorem subd6_3_722 : subd6_3 [1, 3, -1] = true := by decide +kernel
theorem subd6_3_723 : subd6_3 [1, 3, 0] = true := by decide +kernel
theorem subd6_3_724 : subd6_3 [1, 3, 1] = true := by decide +kernel
theorem subd6_3_725 : subd6_3 [1, 3, 2] = true := by decide +kernel
theorem subd6_3_726 : subd6_3 [1, 3, 3] = true := by decide +kernel
theorem subd6_3_727 : subd6_3 [1, 3, 4] = true := by decide +kernel
theorem subd6_3_728 : subd6_3 [1, 3, 5] = true := by decide +kernel
theorem subd6_3_729 : subd6_3 [1, 3, 6] = true := by decide +kernel
theorem subd6_3_730 : subd6_3 [1, 4, -9] = true := by decide +kernel
theorem subd6_3_731 : subd6_3 [1, 4, -8] = true := by decide +kernel
theorem subd6_3_732 : subd6_3 [1, 4, -7] = true := by decide +kernel
theorem subd6_3_733 : subd6_3 [1, 4, -6] = true := by decide +kernel
theorem subd6_3_734 : subd6_3 [1, 4, -5] = true := by decide +kernel
theorem subd6_3_735 : subd6_3 [1, 4, -4] = true := by decide +kernel
theorem sbd6_3_22 : ∀ q ∈ blkd6_3_22, subd6_3 q = true := by
  unfold blkd6_3_22
  exact List.forall_mem_cons.2 ⟨subd6_3_704, List.forall_mem_cons.2 ⟨subd6_3_705, List.forall_mem_cons.2 ⟨subd6_3_706, List.forall_mem_cons.2 ⟨subd6_3_707, List.forall_mem_cons.2 ⟨subd6_3_708, List.forall_mem_cons.2 ⟨subd6_3_709, List.forall_mem_cons.2 ⟨subd6_3_710, List.forall_mem_cons.2 ⟨subd6_3_711, List.forall_mem_cons.2 ⟨subd6_3_712, List.forall_mem_cons.2 ⟨subd6_3_713, List.forall_mem_cons.2 ⟨subd6_3_714, List.forall_mem_cons.2 ⟨subd6_3_715, List.forall_mem_cons.2 ⟨subd6_3_716, List.forall_mem_cons.2 ⟨subd6_3_717, List.forall_mem_cons.2 ⟨subd6_3_718, List.forall_mem_cons.2 ⟨subd6_3_719, List.forall_mem_cons.2 ⟨subd6_3_720, List.forall_mem_cons.2 ⟨subd6_3_721, List.forall_mem_cons.2 ⟨subd6_3_722, List.forall_mem_cons.2 ⟨subd6_3_723, List.forall_mem_cons.2 ⟨subd6_3_724, List.forall_mem_cons.2 ⟨subd6_3_725, List.forall_mem_cons.2 ⟨subd6_3_726, List.forall_mem_cons.2 ⟨subd6_3_727, List.forall_mem_cons.2 ⟨subd6_3_728, List.forall_mem_cons.2 ⟨subd6_3_729, List.forall_mem_cons.2 ⟨subd6_3_730, List.forall_mem_cons.2 ⟨subd6_3_731, List.forall_mem_cons.2 ⟨subd6_3_732, List.forall_mem_cons.2 ⟨subd6_3_733, List.forall_mem_cons.2 ⟨subd6_3_734, List.forall_mem_cons.2 ⟨subd6_3_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_3_736 : subd6_3 [1, 4, -3] = true := by decide +kernel
theorem subd6_3_737 : subd6_3 [1, 4, -2] = true := by decide +kernel
theorem subd6_3_738 : subd6_3 [1, 4, -1] = true := by decide +kernel
theorem subd6_3_739 : subd6_3 [1, 4, 0] = true := by decide +kernel
theorem subd6_3_740 : subd6_3 [1, 4, 1] = true := by decide +kernel
theorem subd6_3_741 : subd6_3 [1, 4, 2] = true := by decide +kernel
theorem subd6_3_742 : subd6_3 [1, 4, 3] = true := by decide +kernel
theorem subd6_3_743 : subd6_3 [1, 4, 4] = true := by decide +kernel
theorem subd6_3_744 : subd6_3 [1, 4, 5] = true := by decide +kernel
theorem subd6_3_745 : subd6_3 [1, 5] = true := by decide +kernel
theorem subd6_3_746 : subd6_3 [1, 6] = true := by decide +kernel
theorem subd6_3_747 : subd6_3 [2, -6] = true := by decide +kernel
theorem subd6_3_748 : subd6_3 [2, -5] = true := by decide +kernel
theorem subd6_3_749 : subd6_3 [2, -4] = true := by decide +kernel
theorem subd6_3_750 : subd6_3 [2, -3, -6] = true := by decide +kernel
theorem subd6_3_751 : subd6_3 [2, -3, -5] = true := by decide +kernel
theorem subd6_3_752 : subd6_3 [2, -3, -4] = true := by decide +kernel
theorem subd6_3_753 : subd6_3 [2, -3, -3] = true := by decide +kernel
theorem subd6_3_754 : subd6_3 [2, -3, -2] = true := by decide +kernel
theorem subd6_3_755 : subd6_3 [2, -3, -1] = true := by decide +kernel
theorem subd6_3_756 : subd6_3 [2, -3, 0] = true := by decide +kernel
theorem subd6_3_757 : subd6_3 [2, -3, 1] = true := by decide +kernel
theorem subd6_3_758 : subd6_3 [2, -3, 2] = true := by decide +kernel
theorem subd6_3_759 : subd6_3 [2, -3, 3] = true := by decide +kernel
theorem subd6_3_760 : subd6_3 [2, -3, 4] = true := by decide +kernel
theorem subd6_3_761 : subd6_3 [2, -3, 5] = true := by decide +kernel
theorem subd6_3_762 : subd6_3 [2, -3, 6] = true := by decide +kernel
theorem subd6_3_763 : subd6_3 [2, -3, 7] = true := by decide +kernel
theorem subd6_3_764 : subd6_3 [2, -3, 8] = true := by decide +kernel
theorem subd6_3_765 : subd6_3 [2, -2, -7] = true := by decide +kernel
theorem subd6_3_766 : subd6_3 [2, -2, -6] = true := by decide +kernel
theorem subd6_3_767 : subd6_3 [2, -2, -5] = true := by decide +kernel
theorem sbd6_3_23 : ∀ q ∈ blkd6_3_23, subd6_3 q = true := by
  unfold blkd6_3_23
  exact List.forall_mem_cons.2 ⟨subd6_3_736, List.forall_mem_cons.2 ⟨subd6_3_737, List.forall_mem_cons.2 ⟨subd6_3_738, List.forall_mem_cons.2 ⟨subd6_3_739, List.forall_mem_cons.2 ⟨subd6_3_740, List.forall_mem_cons.2 ⟨subd6_3_741, List.forall_mem_cons.2 ⟨subd6_3_742, List.forall_mem_cons.2 ⟨subd6_3_743, List.forall_mem_cons.2 ⟨subd6_3_744, List.forall_mem_cons.2 ⟨subd6_3_745, List.forall_mem_cons.2 ⟨subd6_3_746, List.forall_mem_cons.2 ⟨subd6_3_747, List.forall_mem_cons.2 ⟨subd6_3_748, List.forall_mem_cons.2 ⟨subd6_3_749, List.forall_mem_cons.2 ⟨subd6_3_750, List.forall_mem_cons.2 ⟨subd6_3_751, List.forall_mem_cons.2 ⟨subd6_3_752, List.forall_mem_cons.2 ⟨subd6_3_753, List.forall_mem_cons.2 ⟨subd6_3_754, List.forall_mem_cons.2 ⟨subd6_3_755, List.forall_mem_cons.2 ⟨subd6_3_756, List.forall_mem_cons.2 ⟨subd6_3_757, List.forall_mem_cons.2 ⟨subd6_3_758, List.forall_mem_cons.2 ⟨subd6_3_759, List.forall_mem_cons.2 ⟨subd6_3_760, List.forall_mem_cons.2 ⟨subd6_3_761, List.forall_mem_cons.2 ⟨subd6_3_762, List.forall_mem_cons.2 ⟨subd6_3_763, List.forall_mem_cons.2 ⟨subd6_3_764, List.forall_mem_cons.2 ⟨subd6_3_765, List.forall_mem_cons.2 ⟨subd6_3_766, List.forall_mem_cons.2 ⟨subd6_3_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_3_768 : subd6_3 [2, -2, -4] = true := by decide +kernel
theorem subd6_3_769 : subd6_3 [2, -2, -3] = true := by decide +kernel
theorem subd6_3_770 : subd6_3 [2, -2, -2] = true := by decide +kernel
theorem subd6_3_771 : subd6_3 [2, -2, -1] = true := by decide +kernel
theorem subd6_3_772 : subd6_3 [2, -2, 0] = true := by decide +kernel
theorem subd6_3_773 : subd6_3 [2, -2, 1] = true := by decide +kernel
theorem subd6_3_774 : subd6_3 [2, -2, 2] = true := by decide +kernel
theorem subd6_3_775 : subd6_3 [2, -2, 3] = true := by decide +kernel
theorem subd6_3_776 : subd6_3 [2, -2, 4] = true := by decide +kernel
theorem subd6_3_777 : subd6_3 [2, -2, 5] = true := by decide +kernel
theorem subd6_3_778 : subd6_3 [2, -2, 6] = true := by decide +kernel
theorem subd6_3_779 : subd6_3 [2, -2, 7] = true := by decide +kernel
theorem subd6_3_780 : subd6_3 [2, -2, 8] = true := by decide +kernel
theorem subd6_3_781 : subd6_3 [2, -1, -8] = true := by decide +kernel
theorem subd6_3_782 : subd6_3 [2, -1, -7] = true := by decide +kernel
theorem subd6_3_783 : subd6_3 [2, -1, -6] = true := by decide +kernel
theorem subd6_3_784 : subd6_3 [2, -1, -5] = true := by decide +kernel
theorem subd6_3_785 : subd6_3 [2, -1, -4] = true := by decide +kernel
theorem subd6_3_786 : subd6_3 [2, -1, -3] = true := by decide +kernel
theorem subd6_3_787 : subd6_3 [2, -1, -2] = true := by decide +kernel
theorem subd6_3_788 : subd6_3 [2, -1, -1] = true := by decide +kernel
theorem subd6_3_789 : subd6_3 [2, -1, 0] = true := by decide +kernel
theorem subd6_3_790 : subd6_3 [2, -1, 1] = true := by decide +kernel
theorem subd6_3_791 : subd6_3 [2, -1, 2] = true := by decide +kernel
theorem subd6_3_792 : subd6_3 [2, -1, 3] = true := by decide +kernel
theorem subd6_3_793 : subd6_3 [2, -1, 4] = true := by decide +kernel
theorem subd6_3_794 : subd6_3 [2, -1, 5] = true := by decide +kernel
theorem subd6_3_795 : subd6_3 [2, -1, 6] = true := by decide +kernel
theorem subd6_3_796 : subd6_3 [2, -1, 7] = true := by decide +kernel
theorem subd6_3_797 : subd6_3 [2, -1, 8] = true := by decide +kernel
theorem subd6_3_798 : subd6_3 [2, 0, -9] = true := by decide +kernel
theorem subd6_3_799 : subd6_3 [2, 0, -8] = true := by decide +kernel
theorem sbd6_3_24 : ∀ q ∈ blkd6_3_24, subd6_3 q = true := by
  unfold blkd6_3_24
  exact List.forall_mem_cons.2 ⟨subd6_3_768, List.forall_mem_cons.2 ⟨subd6_3_769, List.forall_mem_cons.2 ⟨subd6_3_770, List.forall_mem_cons.2 ⟨subd6_3_771, List.forall_mem_cons.2 ⟨subd6_3_772, List.forall_mem_cons.2 ⟨subd6_3_773, List.forall_mem_cons.2 ⟨subd6_3_774, List.forall_mem_cons.2 ⟨subd6_3_775, List.forall_mem_cons.2 ⟨subd6_3_776, List.forall_mem_cons.2 ⟨subd6_3_777, List.forall_mem_cons.2 ⟨subd6_3_778, List.forall_mem_cons.2 ⟨subd6_3_779, List.forall_mem_cons.2 ⟨subd6_3_780, List.forall_mem_cons.2 ⟨subd6_3_781, List.forall_mem_cons.2 ⟨subd6_3_782, List.forall_mem_cons.2 ⟨subd6_3_783, List.forall_mem_cons.2 ⟨subd6_3_784, List.forall_mem_cons.2 ⟨subd6_3_785, List.forall_mem_cons.2 ⟨subd6_3_786, List.forall_mem_cons.2 ⟨subd6_3_787, List.forall_mem_cons.2 ⟨subd6_3_788, List.forall_mem_cons.2 ⟨subd6_3_789, List.forall_mem_cons.2 ⟨subd6_3_790, List.forall_mem_cons.2 ⟨subd6_3_791, List.forall_mem_cons.2 ⟨subd6_3_792, List.forall_mem_cons.2 ⟨subd6_3_793, List.forall_mem_cons.2 ⟨subd6_3_794, List.forall_mem_cons.2 ⟨subd6_3_795, List.forall_mem_cons.2 ⟨subd6_3_796, List.forall_mem_cons.2 ⟨subd6_3_797, List.forall_mem_cons.2 ⟨subd6_3_798, List.forall_mem_cons.2 ⟨subd6_3_799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_3_800 : subd6_3 [2, 0, -7] = true := by decide +kernel
theorem subd6_3_801 : subd6_3 [2, 0, -6] = true := by decide +kernel
theorem subd6_3_802 : subd6_3 [2, 0, -5] = true := by decide +kernel
theorem subd6_3_803 : subd6_3 [2, 0, -4] = true := by decide +kernel
theorem subd6_3_804 : subd6_3 [2, 0, -3] = true := by decide +kernel
theorem subd6_3_805 : subd6_3 [2, 0, -2] = true := by decide +kernel
theorem subd6_3_806 : subd6_3 [2, 0, -1] = true := by decide +kernel
theorem subd6_3_807 : subd6_3 [2, 0, 0] = true := by decide +kernel
theorem subd6_3_808 : subd6_3 [2, 0, 1] = true := by decide +kernel
theorem subd6_3_809 : subd6_3 [2, 0, 2] = true := by decide +kernel
theorem subd6_3_810 : subd6_3 [2, 0, 3] = true := by decide +kernel
theorem subd6_3_811 : subd6_3 [2, 0, 4] = true := by decide +kernel
theorem subd6_3_812 : subd6_3 [2, 0, 5] = true := by decide +kernel
theorem subd6_3_813 : subd6_3 [2, 0, 6] = true := by decide +kernel
theorem subd6_3_814 : subd6_3 [2, 0, 7] = true := by decide +kernel
theorem subd6_3_815 : subd6_3 [2, 0, 8] = true := by decide +kernel
theorem subd6_3_816 : subd6_3 [2, 1, -9] = true := by decide +kernel
theorem subd6_3_817 : subd6_3 [2, 1, -8] = true := by decide +kernel
theorem subd6_3_818 : subd6_3 [2, 1, -7] = true := by decide +kernel
theorem subd6_3_819 : subd6_3 [2, 1, -6] = true := by decide +kernel
theorem subd6_3_820 : subd6_3 [2, 1, -5] = true := by decide +kernel
theorem subd6_3_821 : subd6_3 [2, 1, -4] = true := by decide +kernel
theorem subd6_3_822 : subd6_3 [2, 1, -3] = true := by decide +kernel
theorem subd6_3_823 : subd6_3 [2, 1, -2] = true := by decide +kernel
theorem subd6_3_824 : subd6_3 [2, 1, -1] = true := by decide +kernel
theorem subd6_3_825 : subd6_3 [2, 1, 0] = true := by decide +kernel
theorem subd6_3_826 : subd6_3 [2, 1, 1] = true := by decide +kernel
theorem subd6_3_827 : subd6_3 [2, 1, 2] = true := by decide +kernel
theorem subd6_3_828 : subd6_3 [2, 1, 3] = true := by decide +kernel
theorem subd6_3_829 : subd6_3 [2, 1, 4] = true := by decide +kernel
theorem subd6_3_830 : subd6_3 [2, 1, 5] = true := by decide +kernel
theorem subd6_3_831 : subd6_3 [2, 1, 6] = true := by decide +kernel
theorem sbd6_3_25 : ∀ q ∈ blkd6_3_25, subd6_3 q = true := by
  unfold blkd6_3_25
  exact List.forall_mem_cons.2 ⟨subd6_3_800, List.forall_mem_cons.2 ⟨subd6_3_801, List.forall_mem_cons.2 ⟨subd6_3_802, List.forall_mem_cons.2 ⟨subd6_3_803, List.forall_mem_cons.2 ⟨subd6_3_804, List.forall_mem_cons.2 ⟨subd6_3_805, List.forall_mem_cons.2 ⟨subd6_3_806, List.forall_mem_cons.2 ⟨subd6_3_807, List.forall_mem_cons.2 ⟨subd6_3_808, List.forall_mem_cons.2 ⟨subd6_3_809, List.forall_mem_cons.2 ⟨subd6_3_810, List.forall_mem_cons.2 ⟨subd6_3_811, List.forall_mem_cons.2 ⟨subd6_3_812, List.forall_mem_cons.2 ⟨subd6_3_813, List.forall_mem_cons.2 ⟨subd6_3_814, List.forall_mem_cons.2 ⟨subd6_3_815, List.forall_mem_cons.2 ⟨subd6_3_816, List.forall_mem_cons.2 ⟨subd6_3_817, List.forall_mem_cons.2 ⟨subd6_3_818, List.forall_mem_cons.2 ⟨subd6_3_819, List.forall_mem_cons.2 ⟨subd6_3_820, List.forall_mem_cons.2 ⟨subd6_3_821, List.forall_mem_cons.2 ⟨subd6_3_822, List.forall_mem_cons.2 ⟨subd6_3_823, List.forall_mem_cons.2 ⟨subd6_3_824, List.forall_mem_cons.2 ⟨subd6_3_825, List.forall_mem_cons.2 ⟨subd6_3_826, List.forall_mem_cons.2 ⟨subd6_3_827, List.forall_mem_cons.2 ⟨subd6_3_828, List.forall_mem_cons.2 ⟨subd6_3_829, List.forall_mem_cons.2 ⟨subd6_3_830, List.forall_mem_cons.2 ⟨subd6_3_831, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C135
