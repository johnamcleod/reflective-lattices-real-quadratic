import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd13_3_384 : subd13_3 [1, 0, -9] = true := by decide +kernel
theorem subd13_3_385 : subd13_3 [1, 0, -8] = true := by decide +kernel
theorem subd13_3_386 : subd13_3 [1, 0, -7] = true := by decide +kernel
theorem subd13_3_387 : subd13_3 [1, 0, -6] = true := by decide +kernel
theorem subd13_3_388 : subd13_3 [1, 0, -5] = true := by decide +kernel
theorem subd13_3_389 : subd13_3 [1, 0, -4] = true := by decide +kernel
theorem subd13_3_390 : subd13_3 [1, 0, -3] = true := by decide +kernel
theorem subd13_3_391 : subd13_3 [1, 0, -2] = true := by decide +kernel
theorem subd13_3_392 : subd13_3 [1, 0, -1] = true := by decide +kernel
theorem subd13_3_393 : subd13_3 [1, 0, 0] = true := by decide +kernel
theorem subd13_3_394 : subd13_3 [1, 0, 1] = true := by decide +kernel
theorem subd13_3_395 : subd13_3 [1, 0, 2] = true := by decide +kernel
theorem subd13_3_396 : subd13_3 [1, 0, 3] = true := by decide +kernel
theorem subd13_3_397 : subd13_3 [1, 0, 4] = true := by decide +kernel
theorem subd13_3_398 : subd13_3 [1, 0, 5] = true := by decide +kernel
theorem subd13_3_399 : subd13_3 [1, 0, 6] = true := by decide +kernel
theorem subd13_3_400 : subd13_3 [1, 0, 7] = true := by decide +kernel
theorem subd13_3_401 : subd13_3 [1, 0, 8] = true := by decide +kernel
theorem subd13_3_402 : subd13_3 [1, 0, 9] = true := by decide +kernel
theorem subd13_3_403 : subd13_3 [1, 0, 10] = true := by decide +kernel
theorem subd13_3_404 : subd13_3 [1, 0, 11] = true := by decide +kernel
theorem subd13_3_405 : subd13_3 [1, 0, 12] = true := by decide +kernel
theorem subd13_3_406 : subd13_3 [1, 1, -13] = true := by decide +kernel
theorem subd13_3_407 : subd13_3 [1, 1, -12] = true := by decide +kernel
theorem subd13_3_408 : subd13_3 [1, 1, -11] = true := by decide +kernel
theorem subd13_3_409 : subd13_3 [1, 1, -10] = true := by decide +kernel
theorem subd13_3_410 : subd13_3 [1, 1, -9] = true := by decide +kernel
theorem subd13_3_411 : subd13_3 [1, 1, -8] = true := by decide +kernel
theorem subd13_3_412 : subd13_3 [1, 1, -7] = true := by decide +kernel
theorem subd13_3_413 : subd13_3 [1, 1, -6] = true := by decide +kernel
theorem subd13_3_414 : subd13_3 [1, 1, -5] = true := by decide +kernel
theorem subd13_3_415 : subd13_3 [1, 1, -4] = true := by decide +kernel
theorem sbd13_3_12 : ∀ q ∈ blkd13_3_12, subd13_3 q = true := by
  unfold blkd13_3_12
  exact List.forall_mem_cons.2 ⟨subd13_3_384, List.forall_mem_cons.2 ⟨subd13_3_385, List.forall_mem_cons.2 ⟨subd13_3_386, List.forall_mem_cons.2 ⟨subd13_3_387, List.forall_mem_cons.2 ⟨subd13_3_388, List.forall_mem_cons.2 ⟨subd13_3_389, List.forall_mem_cons.2 ⟨subd13_3_390, List.forall_mem_cons.2 ⟨subd13_3_391, List.forall_mem_cons.2 ⟨subd13_3_392, List.forall_mem_cons.2 ⟨subd13_3_393, List.forall_mem_cons.2 ⟨subd13_3_394, List.forall_mem_cons.2 ⟨subd13_3_395, List.forall_mem_cons.2 ⟨subd13_3_396, List.forall_mem_cons.2 ⟨subd13_3_397, List.forall_mem_cons.2 ⟨subd13_3_398, List.forall_mem_cons.2 ⟨subd13_3_399, List.forall_mem_cons.2 ⟨subd13_3_400, List.forall_mem_cons.2 ⟨subd13_3_401, List.forall_mem_cons.2 ⟨subd13_3_402, List.forall_mem_cons.2 ⟨subd13_3_403, List.forall_mem_cons.2 ⟨subd13_3_404, List.forall_mem_cons.2 ⟨subd13_3_405, List.forall_mem_cons.2 ⟨subd13_3_406, List.forall_mem_cons.2 ⟨subd13_3_407, List.forall_mem_cons.2 ⟨subd13_3_408, List.forall_mem_cons.2 ⟨subd13_3_409, List.forall_mem_cons.2 ⟨subd13_3_410, List.forall_mem_cons.2 ⟨subd13_3_411, List.forall_mem_cons.2 ⟨subd13_3_412, List.forall_mem_cons.2 ⟨subd13_3_413, List.forall_mem_cons.2 ⟨subd13_3_414, List.forall_mem_cons.2 ⟨subd13_3_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_3_416 : subd13_3 [1, 1, -3] = true := by decide +kernel
theorem subd13_3_417 : subd13_3 [1, 1, -2] = true := by decide +kernel
theorem subd13_3_418 : subd13_3 [1, 1, -1] = true := by decide +kernel
theorem subd13_3_419 : subd13_3 [1, 1, 0] = true := by decide +kernel
theorem subd13_3_420 : subd13_3 [1, 1, 1] = true := by decide +kernel
theorem subd13_3_421 : subd13_3 [1, 1, 2] = true := by decide +kernel
theorem subd13_3_422 : subd13_3 [1, 1, 3] = true := by decide +kernel
theorem subd13_3_423 : subd13_3 [1, 1, 4] = true := by decide +kernel
theorem subd13_3_424 : subd13_3 [1, 1, 5] = true := by decide +kernel
theorem subd13_3_425 : subd13_3 [1, 1, 6] = true := by decide +kernel
theorem subd13_3_426 : subd13_3 [1, 1, 7] = true := by decide +kernel
theorem subd13_3_427 : subd13_3 [1, 1, 8] = true := by decide +kernel
theorem subd13_3_428 : subd13_3 [1, 1, 9] = true := by decide +kernel
theorem subd13_3_429 : subd13_3 [1, 1, 10] = true := by decide +kernel
theorem subd13_3_430 : subd13_3 [1, 1, 11] = true := by decide +kernel
theorem subd13_3_431 : subd13_3 [1, 2, -10] = true := by decide +kernel
theorem subd13_3_432 : subd13_3 [1, 2, -9] = true := by decide +kernel
theorem subd13_3_433 : subd13_3 [1, 2, -8] = true := by decide +kernel
theorem subd13_3_434 : subd13_3 [1, 2, -7] = true := by decide +kernel
theorem subd13_3_435 : subd13_3 [1, 2, -6] = true := by decide +kernel
theorem subd13_3_436 : subd13_3 [1, 2, -5] = true := by decide +kernel
theorem subd13_3_437 : subd13_3 [1, 2, -4] = true := by decide +kernel
theorem subd13_3_438 : subd13_3 [1, 2, -3] = true := by decide +kernel
theorem subd13_3_439 : subd13_3 [1, 2, -2] = true := by decide +kernel
theorem subd13_3_440 : subd13_3 [1, 2, -1] = true := by decide +kernel
theorem subd13_3_441 : subd13_3 [1, 2, 0] = true := by decide +kernel
theorem subd13_3_442 : subd13_3 [1, 2, 1] = true := by decide +kernel
theorem subd13_3_443 : subd13_3 [1, 2, 2] = true := by decide +kernel
theorem subd13_3_444 : subd13_3 [1, 2, 3] = true := by decide +kernel
theorem subd13_3_445 : subd13_3 [1, 2, 4] = true := by decide +kernel
theorem subd13_3_446 : subd13_3 [1, 2, 5] = true := by decide +kernel
theorem subd13_3_447 : subd13_3 [1, 2, 6] = true := by decide +kernel
theorem sbd13_3_13 : ∀ q ∈ blkd13_3_13, subd13_3 q = true := by
  unfold blkd13_3_13
  exact List.forall_mem_cons.2 ⟨subd13_3_416, List.forall_mem_cons.2 ⟨subd13_3_417, List.forall_mem_cons.2 ⟨subd13_3_418, List.forall_mem_cons.2 ⟨subd13_3_419, List.forall_mem_cons.2 ⟨subd13_3_420, List.forall_mem_cons.2 ⟨subd13_3_421, List.forall_mem_cons.2 ⟨subd13_3_422, List.forall_mem_cons.2 ⟨subd13_3_423, List.forall_mem_cons.2 ⟨subd13_3_424, List.forall_mem_cons.2 ⟨subd13_3_425, List.forall_mem_cons.2 ⟨subd13_3_426, List.forall_mem_cons.2 ⟨subd13_3_427, List.forall_mem_cons.2 ⟨subd13_3_428, List.forall_mem_cons.2 ⟨subd13_3_429, List.forall_mem_cons.2 ⟨subd13_3_430, List.forall_mem_cons.2 ⟨subd13_3_431, List.forall_mem_cons.2 ⟨subd13_3_432, List.forall_mem_cons.2 ⟨subd13_3_433, List.forall_mem_cons.2 ⟨subd13_3_434, List.forall_mem_cons.2 ⟨subd13_3_435, List.forall_mem_cons.2 ⟨subd13_3_436, List.forall_mem_cons.2 ⟨subd13_3_437, List.forall_mem_cons.2 ⟨subd13_3_438, List.forall_mem_cons.2 ⟨subd13_3_439, List.forall_mem_cons.2 ⟨subd13_3_440, List.forall_mem_cons.2 ⟨subd13_3_441, List.forall_mem_cons.2 ⟨subd13_3_442, List.forall_mem_cons.2 ⟨subd13_3_443, List.forall_mem_cons.2 ⟨subd13_3_444, List.forall_mem_cons.2 ⟨subd13_3_445, List.forall_mem_cons.2 ⟨subd13_3_446, List.forall_mem_cons.2 ⟨subd13_3_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_3_448 : subd13_3 [1, 2, 7] = true := by decide +kernel
theorem subd13_3_449 : subd13_3 [1, 2, 8] = true := by decide +kernel
theorem subd13_3_450 : subd13_3 [1, 2, 9] = true := by decide +kernel
theorem subd13_3_451 : subd13_3 [2, -3] = true := by decide +kernel
theorem subd13_3_452 : subd13_3 [2, -2, -8] = true := by decide +kernel
theorem subd13_3_453 : subd13_3 [2, -2, -7] = true := by decide +kernel
theorem subd13_3_454 : subd13_3 [2, -2, -6] = true := by decide +kernel
theorem subd13_3_455 : subd13_3 [2, -2, -5] = true := by decide +kernel
theorem subd13_3_456 : subd13_3 [2, -2, -4] = true := by decide +kernel
theorem subd13_3_457 : subd13_3 [2, -2, -3] = true := by decide +kernel
theorem subd13_3_458 : subd13_3 [2, -2, -2] = true := by decide +kernel
theorem subd13_3_459 : subd13_3 [2, -2, -1] = true := by decide +kernel
theorem subd13_3_460 : subd13_3 [2, -2, 0] = true := by decide +kernel
theorem subd13_3_461 : subd13_3 [2, -2, 1] = true := by decide +kernel
theorem subd13_3_462 : subd13_3 [2, -2, 2] = true := by decide +kernel
theorem subd13_3_463 : subd13_3 [2, -2, 3] = true := by decide +kernel
theorem subd13_3_464 : subd13_3 [2, -2, 4] = true := by decide +kernel
theorem subd13_3_465 : subd13_3 [2, -2, 5] = true := by decide +kernel
theorem subd13_3_466 : subd13_3 [2, -2, 6] = true := by decide +kernel
theorem subd13_3_467 : subd13_3 [2, -1, -11] = true := by decide +kernel
theorem subd13_3_468 : subd13_3 [2, -1, -10] = true := by decide +kernel
theorem subd13_3_469 : subd13_3 [2, -1, -9] = true := by decide +kernel
theorem subd13_3_470 : subd13_3 [2, -1, -8] = true := by decide +kernel
theorem subd13_3_471 : subd13_3 [2, -1, -7] = true := by decide +kernel
theorem subd13_3_472 : subd13_3 [2, -1, -6] = true := by decide +kernel
theorem subd13_3_473 : subd13_3 [2, -1, -5] = true := by decide +kernel
theorem subd13_3_474 : subd13_3 [2, -1, -4] = true := by decide +kernel
theorem subd13_3_475 : subd13_3 [2, -1, -3] = true := by decide +kernel
theorem subd13_3_476 : subd13_3 [2, -1, -2] = true := by decide +kernel
theorem subd13_3_477 : subd13_3 [2, -1, -1] = true := by decide +kernel
theorem subd13_3_478 : subd13_3 [2, -1, 0] = true := by decide +kernel
theorem subd13_3_479 : subd13_3 [2, -1, 1] = true := by decide +kernel
theorem sbd13_3_14 : ∀ q ∈ blkd13_3_14, subd13_3 q = true := by
  unfold blkd13_3_14
  exact List.forall_mem_cons.2 ⟨subd13_3_448, List.forall_mem_cons.2 ⟨subd13_3_449, List.forall_mem_cons.2 ⟨subd13_3_450, List.forall_mem_cons.2 ⟨subd13_3_451, List.forall_mem_cons.2 ⟨subd13_3_452, List.forall_mem_cons.2 ⟨subd13_3_453, List.forall_mem_cons.2 ⟨subd13_3_454, List.forall_mem_cons.2 ⟨subd13_3_455, List.forall_mem_cons.2 ⟨subd13_3_456, List.forall_mem_cons.2 ⟨subd13_3_457, List.forall_mem_cons.2 ⟨subd13_3_458, List.forall_mem_cons.2 ⟨subd13_3_459, List.forall_mem_cons.2 ⟨subd13_3_460, List.forall_mem_cons.2 ⟨subd13_3_461, List.forall_mem_cons.2 ⟨subd13_3_462, List.forall_mem_cons.2 ⟨subd13_3_463, List.forall_mem_cons.2 ⟨subd13_3_464, List.forall_mem_cons.2 ⟨subd13_3_465, List.forall_mem_cons.2 ⟨subd13_3_466, List.forall_mem_cons.2 ⟨subd13_3_467, List.forall_mem_cons.2 ⟨subd13_3_468, List.forall_mem_cons.2 ⟨subd13_3_469, List.forall_mem_cons.2 ⟨subd13_3_470, List.forall_mem_cons.2 ⟨subd13_3_471, List.forall_mem_cons.2 ⟨subd13_3_472, List.forall_mem_cons.2 ⟨subd13_3_473, List.forall_mem_cons.2 ⟨subd13_3_474, List.forall_mem_cons.2 ⟨subd13_3_475, List.forall_mem_cons.2 ⟨subd13_3_476, List.forall_mem_cons.2 ⟨subd13_3_477, List.forall_mem_cons.2 ⟨subd13_3_478, List.forall_mem_cons.2 ⟨subd13_3_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_3_480 : subd13_3 [2, -1, 2] = true := by decide +kernel
theorem subd13_3_481 : subd13_3 [2, -1, 3] = true := by decide +kernel
theorem subd13_3_482 : subd13_3 [2, -1, 4] = true := by decide +kernel
theorem subd13_3_483 : subd13_3 [2, -1, 5] = true := by decide +kernel
theorem subd13_3_484 : subd13_3 [2, -1, 6] = true := by decide +kernel
theorem subd13_3_485 : subd13_3 [2, -1, 7] = true := by decide +kernel
theorem subd13_3_486 : subd13_3 [2, -1, 8] = true := by decide +kernel
theorem subd13_3_487 : subd13_3 [2, -1, 9] = true := by decide +kernel
theorem subd13_3_488 : subd13_3 [2, 0, -12] = true := by decide +kernel
theorem subd13_3_489 : subd13_3 [2, 0, -11] = true := by decide +kernel
theorem subd13_3_490 : subd13_3 [2, 0, -10] = true := by decide +kernel
theorem subd13_3_491 : subd13_3 [2, 0, -9] = true := by decide +kernel
theorem subd13_3_492 : subd13_3 [2, 0, -8] = true := by decide +kernel
theorem subd13_3_493 : subd13_3 [2, 0, -7] = true := by decide +kernel
theorem subd13_3_494 : subd13_3 [2, 0, -6] = true := by decide +kernel
theorem subd13_3_495 : subd13_3 [2, 0, -5] = true := by decide +kernel
theorem subd13_3_496 : subd13_3 [2, 0, -4] = true := by decide +kernel
theorem subd13_3_497 : subd13_3 [2, 0, -3] = true := by decide +kernel
theorem subd13_3_498 : subd13_3 [2, 0, -2] = true := by decide +kernel
theorem subd13_3_499 : subd13_3 [2, 0, -1] = true := by decide +kernel
theorem subd13_3_500 : subd13_3 [2, 0, 0] = true := by decide +kernel
theorem subd13_3_501 : subd13_3 [2, 0, 1] = true := by decide +kernel
theorem subd13_3_502 : subd13_3 [2, 0, 2] = true := by decide +kernel
theorem subd13_3_503 : subd13_3 [2, 0, 3] = true := by decide +kernel
theorem subd13_3_504 : subd13_3 [2, 0, 4] = true := by decide +kernel
theorem subd13_3_505 : subd13_3 [2, 0, 5] = true := by decide +kernel
theorem subd13_3_506 : subd13_3 [2, 0, 6] = true := by decide +kernel
theorem subd13_3_507 : subd13_3 [2, 0, 7] = true := by decide +kernel
theorem subd13_3_508 : subd13_3 [2, 0, 8] = true := by decide +kernel
theorem subd13_3_509 : subd13_3 [2, 0, 9] = true := by decide +kernel
theorem subd13_3_510 : subd13_3 [2, 0, 10] = true := by decide +kernel
theorem subd13_3_511 : subd13_3 [2, 1, -10] = true := by decide +kernel
theorem sbd13_3_15 : ∀ q ∈ blkd13_3_15, subd13_3 q = true := by
  unfold blkd13_3_15
  exact List.forall_mem_cons.2 ⟨subd13_3_480, List.forall_mem_cons.2 ⟨subd13_3_481, List.forall_mem_cons.2 ⟨subd13_3_482, List.forall_mem_cons.2 ⟨subd13_3_483, List.forall_mem_cons.2 ⟨subd13_3_484, List.forall_mem_cons.2 ⟨subd13_3_485, List.forall_mem_cons.2 ⟨subd13_3_486, List.forall_mem_cons.2 ⟨subd13_3_487, List.forall_mem_cons.2 ⟨subd13_3_488, List.forall_mem_cons.2 ⟨subd13_3_489, List.forall_mem_cons.2 ⟨subd13_3_490, List.forall_mem_cons.2 ⟨subd13_3_491, List.forall_mem_cons.2 ⟨subd13_3_492, List.forall_mem_cons.2 ⟨subd13_3_493, List.forall_mem_cons.2 ⟨subd13_3_494, List.forall_mem_cons.2 ⟨subd13_3_495, List.forall_mem_cons.2 ⟨subd13_3_496, List.forall_mem_cons.2 ⟨subd13_3_497, List.forall_mem_cons.2 ⟨subd13_3_498, List.forall_mem_cons.2 ⟨subd13_3_499, List.forall_mem_cons.2 ⟨subd13_3_500, List.forall_mem_cons.2 ⟨subd13_3_501, List.forall_mem_cons.2 ⟨subd13_3_502, List.forall_mem_cons.2 ⟨subd13_3_503, List.forall_mem_cons.2 ⟨subd13_3_504, List.forall_mem_cons.2 ⟨subd13_3_505, List.forall_mem_cons.2 ⟨subd13_3_506, List.forall_mem_cons.2 ⟨subd13_3_507, List.forall_mem_cons.2 ⟨subd13_3_508, List.forall_mem_cons.2 ⟨subd13_3_509, List.forall_mem_cons.2 ⟨subd13_3_510, List.forall_mem_cons.2 ⟨subd13_3_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_3_512 : subd13_3 [2, 1, -9] = true := by decide +kernel
theorem subd13_3_513 : subd13_3 [2, 1, -8] = true := by decide +kernel
theorem subd13_3_514 : subd13_3 [2, 1, -7] = true := by decide +kernel
theorem subd13_3_515 : subd13_3 [2, 1, -6] = true := by decide +kernel
theorem subd13_3_516 : subd13_3 [2, 1, -5] = true := by decide +kernel
theorem subd13_3_517 : subd13_3 [2, 1, -4] = true := by decide +kernel
theorem subd13_3_518 : subd13_3 [2, 1, -3] = true := by decide +kernel
theorem subd13_3_519 : subd13_3 [2, 1, -2] = true := by decide +kernel
theorem subd13_3_520 : subd13_3 [2, 1, -1] = true := by decide +kernel
theorem subd13_3_521 : subd13_3 [2, 1, 0] = true := by decide +kernel
theorem subd13_3_522 : subd13_3 [2, 1, 1] = true := by decide +kernel
theorem subd13_3_523 : subd13_3 [2, 1, 2] = true := by decide +kernel
theorem subd13_3_524 : subd13_3 [2, 1, 3] = true := by decide +kernel
theorem subd13_3_525 : subd13_3 [2, 1, 4] = true := by decide +kernel
theorem subd13_3_526 : subd13_3 [2, 1, 5] = true := by decide +kernel
theorem subd13_3_527 : subd13_3 [2, 1, 6] = true := by decide +kernel
theorem subd13_3_528 : subd13_3 [2, 1, 7] = true := by decide +kernel
theorem subd13_3_529 : subd13_3 [2, 1, 8] = true := by decide +kernel
theorem subd13_3_530 : subd13_3 [2, 1, 9] = true := by decide +kernel
theorem subd13_3_531 : subd13_3 [2, 2] = true := by decide +kernel
theorem subd13_3_532 : subd13_3 [3] = true := by decide +kernel
theorem sbd13_3_16 : ∀ q ∈ blkd13_3_16, subd13_3 q = true := by
  unfold blkd13_3_16
  exact List.forall_mem_cons.2 ⟨subd13_3_512, List.forall_mem_cons.2 ⟨subd13_3_513, List.forall_mem_cons.2 ⟨subd13_3_514, List.forall_mem_cons.2 ⟨subd13_3_515, List.forall_mem_cons.2 ⟨subd13_3_516, List.forall_mem_cons.2 ⟨subd13_3_517, List.forall_mem_cons.2 ⟨subd13_3_518, List.forall_mem_cons.2 ⟨subd13_3_519, List.forall_mem_cons.2 ⟨subd13_3_520, List.forall_mem_cons.2 ⟨subd13_3_521, List.forall_mem_cons.2 ⟨subd13_3_522, List.forall_mem_cons.2 ⟨subd13_3_523, List.forall_mem_cons.2 ⟨subd13_3_524, List.forall_mem_cons.2 ⟨subd13_3_525, List.forall_mem_cons.2 ⟨subd13_3_526, List.forall_mem_cons.2 ⟨subd13_3_527, List.forall_mem_cons.2 ⟨subd13_3_528, List.forall_mem_cons.2 ⟨subd13_3_529, List.forall_mem_cons.2 ⟨subd13_3_530, List.forall_mem_cons.2 ⟨subd13_3_531, List.forall_mem_cons.2 ⟨subd13_3_532, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd14_0 : ldCheck G d14_0.U d14_0.ms ldd14_0 = true := by decide +kernel
theorem pre_okd14_0 : subPre G cell14 d14_0 = true := by decide +kernel
theorem subd14_0_0 : subd14_0 [-6] = true := by decide +kernel
theorem subd14_0_1 : subd14_0 [-5, -5] = true := by decide +kernel
theorem subd14_0_2 : subd14_0 [-5, -4] = true := by decide +kernel
theorem subd14_0_3 : subd14_0 [-5, -3] = true := by decide +kernel
theorem subd14_0_4 : subd14_0 [-5, -2] = true := by decide +kernel
theorem subd14_0_5 : subd14_0 [-5, -1] = true := by decide +kernel
theorem subd14_0_6 : subd14_0 [-5, 0] = true := by decide +kernel
theorem subd14_0_7 : subd14_0 [-5, 1] = true := by decide +kernel
theorem subd14_0_8 : subd14_0 [-5, 2] = true := by decide +kernel
theorem subd14_0_9 : subd14_0 [-5, 3] = true := by decide +kernel
theorem subd14_0_10 : subd14_0 [-5, 4] = true := by decide +kernel
theorem subd14_0_11 : subd14_0 [-4, -6] = true := by decide +kernel
theorem subd14_0_12 : subd14_0 [-4, -5] = true := by decide +kernel
theorem subd14_0_13 : subd14_0 [-4, -4] = true := by decide +kernel
theorem subd14_0_14 : subd14_0 [-4, -3] = true := by decide +kernel
theorem subd14_0_15 : subd14_0 [-4, -2] = true := by decide +kernel
theorem subd14_0_16 : subd14_0 [-4, -1] = true := by decide +kernel
theorem subd14_0_17 : subd14_0 [-4, 0] = true := by decide +kernel
theorem subd14_0_18 : subd14_0 [-4, 1] = true := by decide +kernel
theorem subd14_0_19 : subd14_0 [-4, 2] = true := by decide +kernel
theorem subd14_0_20 : subd14_0 [-4, 3] = true := by decide +kernel
theorem subd14_0_21 : subd14_0 [-4, 4] = true := by decide +kernel
theorem subd14_0_22 : subd14_0 [-4, 5] = true := by decide +kernel
theorem subd14_0_23 : subd14_0 [-3, -6] = true := by decide +kernel
theorem subd14_0_24 : subd14_0 [-3, -5] = true := by decide +kernel
theorem subd14_0_25 : subd14_0 [-3, -4] = true := by decide +kernel
theorem subd14_0_26 : subd14_0 [-3, -3] = true := by decide +kernel
theorem subd14_0_27 : subd14_0 [-3, -2] = true := by decide +kernel
theorem subd14_0_28 : subd14_0 [-3, -1, -6] = true := by decide +kernel
theorem subd14_0_29 : subd14_0 [-3, -1, -5] = true := by decide +kernel
theorem subd14_0_30 : subd14_0 [-3, -1, -4] = true := by decide +kernel
theorem subd14_0_31 : subd14_0 [-3, -1, -3] = true := by decide +kernel
theorem sbd14_0_0 : ∀ q ∈ blkd14_0_0, subd14_0 q = true := by
  unfold blkd14_0_0
  exact List.forall_mem_cons.2 ⟨subd14_0_0, List.forall_mem_cons.2 ⟨subd14_0_1, List.forall_mem_cons.2 ⟨subd14_0_2, List.forall_mem_cons.2 ⟨subd14_0_3, List.forall_mem_cons.2 ⟨subd14_0_4, List.forall_mem_cons.2 ⟨subd14_0_5, List.forall_mem_cons.2 ⟨subd14_0_6, List.forall_mem_cons.2 ⟨subd14_0_7, List.forall_mem_cons.2 ⟨subd14_0_8, List.forall_mem_cons.2 ⟨subd14_0_9, List.forall_mem_cons.2 ⟨subd14_0_10, List.forall_mem_cons.2 ⟨subd14_0_11, List.forall_mem_cons.2 ⟨subd14_0_12, List.forall_mem_cons.2 ⟨subd14_0_13, List.forall_mem_cons.2 ⟨subd14_0_14, List.forall_mem_cons.2 ⟨subd14_0_15, List.forall_mem_cons.2 ⟨subd14_0_16, List.forall_mem_cons.2 ⟨subd14_0_17, List.forall_mem_cons.2 ⟨subd14_0_18, List.forall_mem_cons.2 ⟨subd14_0_19, List.forall_mem_cons.2 ⟨subd14_0_20, List.forall_mem_cons.2 ⟨subd14_0_21, List.forall_mem_cons.2 ⟨subd14_0_22, List.forall_mem_cons.2 ⟨subd14_0_23, List.forall_mem_cons.2 ⟨subd14_0_24, List.forall_mem_cons.2 ⟨subd14_0_25, List.forall_mem_cons.2 ⟨subd14_0_26, List.forall_mem_cons.2 ⟨subd14_0_27, List.forall_mem_cons.2 ⟨subd14_0_28, List.forall_mem_cons.2 ⟨subd14_0_29, List.forall_mem_cons.2 ⟨subd14_0_30, List.forall_mem_cons.2 ⟨subd14_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_0_32 : subd14_0 [-3, -1, -2] = true := by decide +kernel
theorem subd14_0_33 : subd14_0 [-3, -1, -1] = true := by decide +kernel
theorem subd14_0_34 : subd14_0 [-3, -1, 0] = true := by decide +kernel
theorem subd14_0_35 : subd14_0 [-3, -1, 1] = true := by decide +kernel
theorem subd14_0_36 : subd14_0 [-3, -1, 2] = true := by decide +kernel
theorem subd14_0_37 : subd14_0 [-3, -1, 3] = true := by decide +kernel
theorem subd14_0_38 : subd14_0 [-3, -1, 4] = true := by decide +kernel
theorem subd14_0_39 : subd14_0 [-3, -1, 5] = true := by decide +kernel
theorem subd14_0_40 : subd14_0 [-3, -1, 6] = true := by decide +kernel
theorem subd14_0_41 : subd14_0 [-3, -1, 7] = true := by decide +kernel
theorem subd14_0_42 : subd14_0 [-3, 0, -6] = true := by decide +kernel
theorem subd14_0_43 : subd14_0 [-3, 0, -5] = true := by decide +kernel
theorem subd14_0_44 : subd14_0 [-3, 0, -4] = true := by decide +kernel
theorem subd14_0_45 : subd14_0 [-3, 0, -3] = true := by decide +kernel
theorem subd14_0_46 : subd14_0 [-3, 0, -2] = true := by decide +kernel
theorem subd14_0_47 : subd14_0 [-3, 0, -1] = true := by decide +kernel
theorem subd14_0_48 : subd14_0 [-3, 0, 0] = true := by decide +kernel
theorem subd14_0_49 : subd14_0 [-3, 0, 1] = true := by decide +kernel
theorem subd14_0_50 : subd14_0 [-3, 0, 2] = true := by decide +kernel
theorem subd14_0_51 : subd14_0 [-3, 0, 3] = true := by decide +kernel
theorem subd14_0_52 : subd14_0 [-3, 0, 4] = true := by decide +kernel
theorem subd14_0_53 : subd14_0 [-3, 0, 5] = true := by decide +kernel
theorem subd14_0_54 : subd14_0 [-3, 0, 6] = true := by decide +kernel
theorem subd14_0_55 : subd14_0 [-3, 0, 7] = true := by decide +kernel
theorem subd14_0_56 : subd14_0 [-3, 1, -6] = true := by decide +kernel
theorem subd14_0_57 : subd14_0 [-3, 1, -5] = true := by decide +kernel
theorem subd14_0_58 : subd14_0 [-3, 1, -4] = true := by decide +kernel
theorem subd14_0_59 : subd14_0 [-3, 1, -3] = true := by decide +kernel
theorem subd14_0_60 : subd14_0 [-3, 1, -2] = true := by decide +kernel
theorem subd14_0_61 : subd14_0 [-3, 1, -1] = true := by decide +kernel
theorem subd14_0_62 : subd14_0 [-3, 1, 0] = true := by decide +kernel
theorem subd14_0_63 : subd14_0 [-3, 1, 1] = true := by decide +kernel
theorem sbd14_0_1 : ∀ q ∈ blkd14_0_1, subd14_0 q = true := by
  unfold blkd14_0_1
  exact List.forall_mem_cons.2 ⟨subd14_0_32, List.forall_mem_cons.2 ⟨subd14_0_33, List.forall_mem_cons.2 ⟨subd14_0_34, List.forall_mem_cons.2 ⟨subd14_0_35, List.forall_mem_cons.2 ⟨subd14_0_36, List.forall_mem_cons.2 ⟨subd14_0_37, List.forall_mem_cons.2 ⟨subd14_0_38, List.forall_mem_cons.2 ⟨subd14_0_39, List.forall_mem_cons.2 ⟨subd14_0_40, List.forall_mem_cons.2 ⟨subd14_0_41, List.forall_mem_cons.2 ⟨subd14_0_42, List.forall_mem_cons.2 ⟨subd14_0_43, List.forall_mem_cons.2 ⟨subd14_0_44, List.forall_mem_cons.2 ⟨subd14_0_45, List.forall_mem_cons.2 ⟨subd14_0_46, List.forall_mem_cons.2 ⟨subd14_0_47, List.forall_mem_cons.2 ⟨subd14_0_48, List.forall_mem_cons.2 ⟨subd14_0_49, List.forall_mem_cons.2 ⟨subd14_0_50, List.forall_mem_cons.2 ⟨subd14_0_51, List.forall_mem_cons.2 ⟨subd14_0_52, List.forall_mem_cons.2 ⟨subd14_0_53, List.forall_mem_cons.2 ⟨subd14_0_54, List.forall_mem_cons.2 ⟨subd14_0_55, List.forall_mem_cons.2 ⟨subd14_0_56, List.forall_mem_cons.2 ⟨subd14_0_57, List.forall_mem_cons.2 ⟨subd14_0_58, List.forall_mem_cons.2 ⟨subd14_0_59, List.forall_mem_cons.2 ⟨subd14_0_60, List.forall_mem_cons.2 ⟨subd14_0_61, List.forall_mem_cons.2 ⟨subd14_0_62, List.forall_mem_cons.2 ⟨subd14_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_0_64 : subd14_0 [-3, 1, 2] = true := by decide +kernel
theorem subd14_0_65 : subd14_0 [-3, 1, 3] = true := by decide +kernel
theorem subd14_0_66 : subd14_0 [-3, 1, 4] = true := by decide +kernel
theorem subd14_0_67 : subd14_0 [-3, 1, 5] = true := by decide +kernel
theorem subd14_0_68 : subd14_0 [-3, 1, 6] = true := by decide +kernel
theorem subd14_0_69 : subd14_0 [-3, 1, 7] = true := by decide +kernel
theorem subd14_0_70 : subd14_0 [-3, 2] = true := by decide +kernel
theorem subd14_0_71 : subd14_0 [-3, 3] = true := by decide +kernel
theorem subd14_0_72 : subd14_0 [-3, 4] = true := by decide +kernel
theorem subd14_0_73 : subd14_0 [-3, 5] = true := by decide +kernel
theorem subd14_0_74 : subd14_0 [-2, -7] = true := by decide +kernel
theorem subd14_0_75 : subd14_0 [-2, -6] = true := by decide +kernel
theorem subd14_0_76 : subd14_0 [-2, -5] = true := by decide +kernel
theorem subd14_0_77 : subd14_0 [-2, -4] = true := by decide +kernel
theorem subd14_0_78 : subd14_0 [-2, -3] = true := by decide +kernel
theorem subd14_0_79 : subd14_0 [-2, -2, -6] = true := by decide +kernel
theorem subd14_0_80 : subd14_0 [-2, -2, -5] = true := by decide +kernel
theorem subd14_0_81 : subd14_0 [-2, -2, -4] = true := by decide +kernel
theorem subd14_0_82 : subd14_0 [-2, -2, -3] = true := by decide +kernel
theorem subd14_0_83 : subd14_0 [-2, -2, -2] = true := by decide +kernel
theorem subd14_0_84 : subd14_0 [-2, -2, -1] = true := by decide +kernel
theorem subd14_0_85 : subd14_0 [-2, -2, 0] = true := by decide +kernel
theorem subd14_0_86 : subd14_0 [-2, -2, 1] = true := by decide +kernel
theorem subd14_0_87 : subd14_0 [-2, -2, 2] = true := by decide +kernel
theorem subd14_0_88 : subd14_0 [-2, -2, 3] = true := by decide +kernel
theorem subd14_0_89 : subd14_0 [-2, -2, 4] = true := by decide +kernel
theorem subd14_0_90 : subd14_0 [-2, -2, 5] = true := by decide +kernel
theorem subd14_0_91 : subd14_0 [-2, -2, 6] = true := by decide +kernel
theorem subd14_0_92 : subd14_0 [-2, -2, 7] = true := by decide +kernel
theorem subd14_0_93 : subd14_0 [-2, -1, -7] = true := by decide +kernel
theorem subd14_0_94 : subd14_0 [-2, -1, -6] = true := by decide +kernel
theorem subd14_0_95 : subd14_0 [-2, -1, -5] = true := by decide +kernel
theorem sbd14_0_2 : ∀ q ∈ blkd14_0_2, subd14_0 q = true := by
  unfold blkd14_0_2
  exact List.forall_mem_cons.2 ⟨subd14_0_64, List.forall_mem_cons.2 ⟨subd14_0_65, List.forall_mem_cons.2 ⟨subd14_0_66, List.forall_mem_cons.2 ⟨subd14_0_67, List.forall_mem_cons.2 ⟨subd14_0_68, List.forall_mem_cons.2 ⟨subd14_0_69, List.forall_mem_cons.2 ⟨subd14_0_70, List.forall_mem_cons.2 ⟨subd14_0_71, List.forall_mem_cons.2 ⟨subd14_0_72, List.forall_mem_cons.2 ⟨subd14_0_73, List.forall_mem_cons.2 ⟨subd14_0_74, List.forall_mem_cons.2 ⟨subd14_0_75, List.forall_mem_cons.2 ⟨subd14_0_76, List.forall_mem_cons.2 ⟨subd14_0_77, List.forall_mem_cons.2 ⟨subd14_0_78, List.forall_mem_cons.2 ⟨subd14_0_79, List.forall_mem_cons.2 ⟨subd14_0_80, List.forall_mem_cons.2 ⟨subd14_0_81, List.forall_mem_cons.2 ⟨subd14_0_82, List.forall_mem_cons.2 ⟨subd14_0_83, List.forall_mem_cons.2 ⟨subd14_0_84, List.forall_mem_cons.2 ⟨subd14_0_85, List.forall_mem_cons.2 ⟨subd14_0_86, List.forall_mem_cons.2 ⟨subd14_0_87, List.forall_mem_cons.2 ⟨subd14_0_88, List.forall_mem_cons.2 ⟨subd14_0_89, List.forall_mem_cons.2 ⟨subd14_0_90, List.forall_mem_cons.2 ⟨subd14_0_91, List.forall_mem_cons.2 ⟨subd14_0_92, List.forall_mem_cons.2 ⟨subd14_0_93, List.forall_mem_cons.2 ⟨subd14_0_94, List.forall_mem_cons.2 ⟨subd14_0_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_0_96 : subd14_0 [-2, -1, -4] = true := by decide +kernel
theorem subd14_0_97 : subd14_0 [-2, -1, -3] = true := by decide +kernel
theorem subd14_0_98 : subd14_0 [-2, -1, -2] = true := by decide +kernel
theorem subd14_0_99 : subd14_0 [-2, -1, -1] = true := by decide +kernel
theorem subd14_0_100 : subd14_0 [-2, -1, 0] = true := by decide +kernel
theorem subd14_0_101 : subd14_0 [-2, -1, 1] = true := by decide +kernel
theorem subd14_0_102 : subd14_0 [-2, -1, 2] = true := by decide +kernel
theorem subd14_0_103 : subd14_0 [-2, -1, 3] = true := by decide +kernel
theorem subd14_0_104 : subd14_0 [-2, -1, 4] = true := by decide +kernel
theorem subd14_0_105 : subd14_0 [-2, -1, 5] = true := by decide +kernel
theorem subd14_0_106 : subd14_0 [-2, -1, 6] = true := by decide +kernel
theorem subd14_0_107 : subd14_0 [-2, -1, 7] = true := by decide +kernel
theorem subd14_0_108 : subd14_0 [-2, 0, -7] = true := by decide +kernel
theorem subd14_0_109 : subd14_0 [-2, 0, -6] = true := by decide +kernel
theorem subd14_0_110 : subd14_0 [-2, 0, -5] = true := by decide +kernel
theorem subd14_0_111 : subd14_0 [-2, 0, -4] = true := by decide +kernel
theorem subd14_0_112 : subd14_0 [-2, 0, -3] = true := by decide +kernel
theorem subd14_0_113 : subd14_0 [-2, 0, -2] = true := by decide +kernel
theorem subd14_0_114 : subd14_0 [-2, 0, -1] = true := by decide +kernel
theorem subd14_0_115 : subd14_0 [-2, 0, 0] = true := by decide +kernel
theorem subd14_0_116 : subd14_0 [-2, 0, 1] = true := by decide +kernel
theorem subd14_0_117 : subd14_0 [-2, 0, 2] = true := by decide +kernel
theorem subd14_0_118 : subd14_0 [-2, 0, 3] = true := by decide +kernel
theorem subd14_0_119 : subd14_0 [-2, 0, 4] = true := by decide +kernel
theorem subd14_0_120 : subd14_0 [-2, 0, 5] = true := by decide +kernel
theorem subd14_0_121 : subd14_0 [-2, 0, 6] = true := by decide +kernel
theorem subd14_0_122 : subd14_0 [-2, 0, 7] = true := by decide +kernel
theorem subd14_0_123 : subd14_0 [-2, 1, -7] = true := by decide +kernel
theorem subd14_0_124 : subd14_0 [-2, 1, -6] = true := by decide +kernel
theorem subd14_0_125 : subd14_0 [-2, 1, -5] = true := by decide +kernel
theorem subd14_0_126 : subd14_0 [-2, 1, -4] = true := by decide +kernel
theorem subd14_0_127 : subd14_0 [-2, 1, -3] = true := by decide +kernel
theorem sbd14_0_3 : ∀ q ∈ blkd14_0_3, subd14_0 q = true := by
  unfold blkd14_0_3
  exact List.forall_mem_cons.2 ⟨subd14_0_96, List.forall_mem_cons.2 ⟨subd14_0_97, List.forall_mem_cons.2 ⟨subd14_0_98, List.forall_mem_cons.2 ⟨subd14_0_99, List.forall_mem_cons.2 ⟨subd14_0_100, List.forall_mem_cons.2 ⟨subd14_0_101, List.forall_mem_cons.2 ⟨subd14_0_102, List.forall_mem_cons.2 ⟨subd14_0_103, List.forall_mem_cons.2 ⟨subd14_0_104, List.forall_mem_cons.2 ⟨subd14_0_105, List.forall_mem_cons.2 ⟨subd14_0_106, List.forall_mem_cons.2 ⟨subd14_0_107, List.forall_mem_cons.2 ⟨subd14_0_108, List.forall_mem_cons.2 ⟨subd14_0_109, List.forall_mem_cons.2 ⟨subd14_0_110, List.forall_mem_cons.2 ⟨subd14_0_111, List.forall_mem_cons.2 ⟨subd14_0_112, List.forall_mem_cons.2 ⟨subd14_0_113, List.forall_mem_cons.2 ⟨subd14_0_114, List.forall_mem_cons.2 ⟨subd14_0_115, List.forall_mem_cons.2 ⟨subd14_0_116, List.forall_mem_cons.2 ⟨subd14_0_117, List.forall_mem_cons.2 ⟨subd14_0_118, List.forall_mem_cons.2 ⟨subd14_0_119, List.forall_mem_cons.2 ⟨subd14_0_120, List.forall_mem_cons.2 ⟨subd14_0_121, List.forall_mem_cons.2 ⟨subd14_0_122, List.forall_mem_cons.2 ⟨subd14_0_123, List.forall_mem_cons.2 ⟨subd14_0_124, List.forall_mem_cons.2 ⟨subd14_0_125, List.forall_mem_cons.2 ⟨subd14_0_126, List.forall_mem_cons.2 ⟨subd14_0_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
