import ReflectZphi.Data.Cert5.C093.Base

namespace ReflectZphi.Data.Cert5.C093

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_0_416 : subd9_0 [1, 0, -1] = true := by decide +kernel
theorem subd9_0_417 : subd9_0 [1, 0, 0] = true := by decide +kernel
theorem subd9_0_418 : subd9_0 [1, 0, 1] = true := by decide +kernel
theorem subd9_0_419 : subd9_0 [1, 0, 2] = true := by decide +kernel
theorem subd9_0_420 : subd9_0 [1, 0, 3] = true := by decide +kernel
theorem subd9_0_421 : subd9_0 [1, 0, 4] = true := by decide +kernel
theorem subd9_0_422 : subd9_0 [1, 0, 5] = true := by decide +kernel
theorem subd9_0_423 : subd9_0 [1, 0, 6] = true := by decide +kernel
theorem subd9_0_424 : subd9_0 [1, 0, 7] = true := by decide +kernel
theorem subd9_0_425 : subd9_0 [1, 0, 8] = true := by decide +kernel
theorem subd9_0_426 : subd9_0 [1, 1, -9] = true := by decide +kernel
theorem subd9_0_427 : subd9_0 [1, 1, -8] = true := by decide +kernel
theorem subd9_0_428 : subd9_0 [1, 1, -7] = true := by decide +kernel
theorem subd9_0_429 : subd9_0 [1, 1, -6] = true := by decide +kernel
theorem subd9_0_430 : subd9_0 [1, 1, -5] = true := by decide +kernel
theorem subd9_0_431 : subd9_0 [1, 1, -4] = true := by decide +kernel
theorem subd9_0_432 : subd9_0 [1, 1, -3] = true := by decide +kernel
theorem subd9_0_433 : subd9_0 [1, 1, -2] = true := by decide +kernel
theorem subd9_0_434 : subd9_0 [1, 1, -1] = true := by decide +kernel
theorem subd9_0_435 : subd9_0 [1, 1, 0] = true := by decide +kernel
theorem subd9_0_436 : subd9_0 [1, 1, 1] = true := by decide +kernel
theorem subd9_0_437 : subd9_0 [1, 1, 2] = true := by decide +kernel
theorem subd9_0_438 : subd9_0 [1, 1, 3] = true := by decide +kernel
theorem subd9_0_439 : subd9_0 [1, 1, 4] = true := by decide +kernel
theorem subd9_0_440 : subd9_0 [1, 1, 5] = true := by decide +kernel
theorem subd9_0_441 : subd9_0 [1, 1, 6] = true := by decide +kernel
theorem subd9_0_442 : subd9_0 [1, 1, 7] = true := by decide +kernel
theorem subd9_0_443 : subd9_0 [1, 1, 8] = true := by decide +kernel
theorem subd9_0_444 : subd9_0 [1, 2, -8] = true := by decide +kernel
theorem subd9_0_445 : subd9_0 [1, 2, -7] = true := by decide +kernel
theorem subd9_0_446 : subd9_0 [1, 2, -6] = true := by decide +kernel
theorem subd9_0_447 : subd9_0 [1, 2, -5] = true := by decide +kernel
theorem sbd9_0_13 : ∀ q ∈ blkd9_0_13, subd9_0 q = true := by
  unfold blkd9_0_13
  exact List.forall_mem_cons.2 ⟨subd9_0_416, List.forall_mem_cons.2 ⟨subd9_0_417, List.forall_mem_cons.2 ⟨subd9_0_418, List.forall_mem_cons.2 ⟨subd9_0_419, List.forall_mem_cons.2 ⟨subd9_0_420, List.forall_mem_cons.2 ⟨subd9_0_421, List.forall_mem_cons.2 ⟨subd9_0_422, List.forall_mem_cons.2 ⟨subd9_0_423, List.forall_mem_cons.2 ⟨subd9_0_424, List.forall_mem_cons.2 ⟨subd9_0_425, List.forall_mem_cons.2 ⟨subd9_0_426, List.forall_mem_cons.2 ⟨subd9_0_427, List.forall_mem_cons.2 ⟨subd9_0_428, List.forall_mem_cons.2 ⟨subd9_0_429, List.forall_mem_cons.2 ⟨subd9_0_430, List.forall_mem_cons.2 ⟨subd9_0_431, List.forall_mem_cons.2 ⟨subd9_0_432, List.forall_mem_cons.2 ⟨subd9_0_433, List.forall_mem_cons.2 ⟨subd9_0_434, List.forall_mem_cons.2 ⟨subd9_0_435, List.forall_mem_cons.2 ⟨subd9_0_436, List.forall_mem_cons.2 ⟨subd9_0_437, List.forall_mem_cons.2 ⟨subd9_0_438, List.forall_mem_cons.2 ⟨subd9_0_439, List.forall_mem_cons.2 ⟨subd9_0_440, List.forall_mem_cons.2 ⟨subd9_0_441, List.forall_mem_cons.2 ⟨subd9_0_442, List.forall_mem_cons.2 ⟨subd9_0_443, List.forall_mem_cons.2 ⟨subd9_0_444, List.forall_mem_cons.2 ⟨subd9_0_445, List.forall_mem_cons.2 ⟨subd9_0_446, List.forall_mem_cons.2 ⟨subd9_0_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_448 : subd9_0 [1, 2, -4] = true := by decide +kernel
theorem subd9_0_449 : subd9_0 [1, 2, -3] = true := by decide +kernel
theorem subd9_0_450 : subd9_0 [1, 2, -2] = true := by decide +kernel
theorem subd9_0_451 : subd9_0 [1, 2, -1] = true := by decide +kernel
theorem subd9_0_452 : subd9_0 [1, 2, 0] = true := by decide +kernel
theorem subd9_0_453 : subd9_0 [1, 2, 1] = true := by decide +kernel
theorem subd9_0_454 : subd9_0 [1, 2, 2] = true := by decide +kernel
theorem subd9_0_455 : subd9_0 [1, 2, 3] = true := by decide +kernel
theorem subd9_0_456 : subd9_0 [1, 2, 4] = true := by decide +kernel
theorem subd9_0_457 : subd9_0 [1, 2, 5] = true := by decide +kernel
theorem subd9_0_458 : subd9_0 [1, 2, 6] = true := by decide +kernel
theorem subd9_0_459 : subd9_0 [1, 2, 7] = true := by decide +kernel
theorem subd9_0_460 : subd9_0 [1, 3] = true := by decide +kernel
theorem subd9_0_461 : subd9_0 [1, 4] = true := by decide +kernel
theorem subd9_0_462 : subd9_0 [2, -5] = true := by decide +kernel
theorem subd9_0_463 : subd9_0 [2, -4] = true := by decide +kernel
theorem subd9_0_464 : subd9_0 [2, -3, -7] = true := by decide +kernel
theorem subd9_0_465 : subd9_0 [2, -3, -6] = true := by decide +kernel
theorem subd9_0_466 : subd9_0 [2, -3, -5] = true := by decide +kernel
theorem subd9_0_467 : subd9_0 [2, -3, -4] = true := by decide +kernel
theorem subd9_0_468 : subd9_0 [2, -3, -3] = true := by decide +kernel
theorem subd9_0_469 : subd9_0 [2, -3, -2] = true := by decide +kernel
theorem subd9_0_470 : subd9_0 [2, -3, -1] = true := by decide +kernel
theorem subd9_0_471 : subd9_0 [2, -3, 0] = true := by decide +kernel
theorem subd9_0_472 : subd9_0 [2, -3, 1] = true := by decide +kernel
theorem subd9_0_473 : subd9_0 [2, -3, 2] = true := by decide +kernel
theorem subd9_0_474 : subd9_0 [2, -3, 3] = true := by decide +kernel
theorem subd9_0_475 : subd9_0 [2, -3, 4] = true := by decide +kernel
theorem subd9_0_476 : subd9_0 [2, -3, 5] = true := by decide +kernel
theorem subd9_0_477 : subd9_0 [2, -3, 6] = true := by decide +kernel
theorem subd9_0_478 : subd9_0 [2, -2, -8] = true := by decide +kernel
theorem subd9_0_479 : subd9_0 [2, -2, -7] = true := by decide +kernel
theorem sbd9_0_14 : ∀ q ∈ blkd9_0_14, subd9_0 q = true := by
  unfold blkd9_0_14
  exact List.forall_mem_cons.2 ⟨subd9_0_448, List.forall_mem_cons.2 ⟨subd9_0_449, List.forall_mem_cons.2 ⟨subd9_0_450, List.forall_mem_cons.2 ⟨subd9_0_451, List.forall_mem_cons.2 ⟨subd9_0_452, List.forall_mem_cons.2 ⟨subd9_0_453, List.forall_mem_cons.2 ⟨subd9_0_454, List.forall_mem_cons.2 ⟨subd9_0_455, List.forall_mem_cons.2 ⟨subd9_0_456, List.forall_mem_cons.2 ⟨subd9_0_457, List.forall_mem_cons.2 ⟨subd9_0_458, List.forall_mem_cons.2 ⟨subd9_0_459, List.forall_mem_cons.2 ⟨subd9_0_460, List.forall_mem_cons.2 ⟨subd9_0_461, List.forall_mem_cons.2 ⟨subd9_0_462, List.forall_mem_cons.2 ⟨subd9_0_463, List.forall_mem_cons.2 ⟨subd9_0_464, List.forall_mem_cons.2 ⟨subd9_0_465, List.forall_mem_cons.2 ⟨subd9_0_466, List.forall_mem_cons.2 ⟨subd9_0_467, List.forall_mem_cons.2 ⟨subd9_0_468, List.forall_mem_cons.2 ⟨subd9_0_469, List.forall_mem_cons.2 ⟨subd9_0_470, List.forall_mem_cons.2 ⟨subd9_0_471, List.forall_mem_cons.2 ⟨subd9_0_472, List.forall_mem_cons.2 ⟨subd9_0_473, List.forall_mem_cons.2 ⟨subd9_0_474, List.forall_mem_cons.2 ⟨subd9_0_475, List.forall_mem_cons.2 ⟨subd9_0_476, List.forall_mem_cons.2 ⟨subd9_0_477, List.forall_mem_cons.2 ⟨subd9_0_478, List.forall_mem_cons.2 ⟨subd9_0_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_480 : subd9_0 [2, -2, -6] = true := by decide +kernel
theorem subd9_0_481 : subd9_0 [2, -2, -5] = true := by decide +kernel
theorem subd9_0_482 : subd9_0 [2, -2, -4] = true := by decide +kernel
theorem subd9_0_483 : subd9_0 [2, -2, -3] = true := by decide +kernel
theorem subd9_0_484 : subd9_0 [2, -2, -2] = true := by decide +kernel
theorem subd9_0_485 : subd9_0 [2, -2, -1] = true := by decide +kernel
theorem subd9_0_486 : subd9_0 [2, -2, 0] = true := by decide +kernel
theorem subd9_0_487 : subd9_0 [2, -2, 1] = true := by decide +kernel
theorem subd9_0_488 : subd9_0 [2, -2, 2] = true := by decide +kernel
theorem subd9_0_489 : subd9_0 [2, -2, 3] = true := by decide +kernel
theorem subd9_0_490 : subd9_0 [2, -2, 4] = true := by decide +kernel
theorem subd9_0_491 : subd9_0 [2, -2, 5] = true := by decide +kernel
theorem subd9_0_492 : subd9_0 [2, -2, 6] = true := by decide +kernel
theorem subd9_0_493 : subd9_0 [2, -2, 7] = true := by decide +kernel
theorem subd9_0_494 : subd9_0 [2, -1, -8] = true := by decide +kernel
theorem subd9_0_495 : subd9_0 [2, -1, -7] = true := by decide +kernel
theorem subd9_0_496 : subd9_0 [2, -1, -6] = true := by decide +kernel
theorem subd9_0_497 : subd9_0 [2, -1, -5] = true := by decide +kernel
theorem subd9_0_498 : subd9_0 [2, -1, -4] = true := by decide +kernel
theorem subd9_0_499 : subd9_0 [2, -1, -3] = true := by decide +kernel
theorem subd9_0_500 : subd9_0 [2, -1, -2] = true := by decide +kernel
theorem subd9_0_501 : subd9_0 [2, -1, -1] = true := by decide +kernel
theorem subd9_0_502 : subd9_0 [2, -1, 0] = true := by decide +kernel
theorem subd9_0_503 : subd9_0 [2, -1, 1] = true := by decide +kernel
theorem subd9_0_504 : subd9_0 [2, -1, 2] = true := by decide +kernel
theorem subd9_0_505 : subd9_0 [2, -1, 3] = true := by decide +kernel
theorem subd9_0_506 : subd9_0 [2, -1, 4] = true := by decide +kernel
theorem subd9_0_507 : subd9_0 [2, -1, 5] = true := by decide +kernel
theorem subd9_0_508 : subd9_0 [2, -1, 6] = true := by decide +kernel
theorem subd9_0_509 : subd9_0 [2, -1, 7] = true := by decide +kernel
theorem subd9_0_510 : subd9_0 [2, -1, 8] = true := by decide +kernel
theorem subd9_0_511 : subd9_0 [2, 0, -8] = true := by decide +kernel
theorem sbd9_0_15 : ∀ q ∈ blkd9_0_15, subd9_0 q = true := by
  unfold blkd9_0_15
  exact List.forall_mem_cons.2 ⟨subd9_0_480, List.forall_mem_cons.2 ⟨subd9_0_481, List.forall_mem_cons.2 ⟨subd9_0_482, List.forall_mem_cons.2 ⟨subd9_0_483, List.forall_mem_cons.2 ⟨subd9_0_484, List.forall_mem_cons.2 ⟨subd9_0_485, List.forall_mem_cons.2 ⟨subd9_0_486, List.forall_mem_cons.2 ⟨subd9_0_487, List.forall_mem_cons.2 ⟨subd9_0_488, List.forall_mem_cons.2 ⟨subd9_0_489, List.forall_mem_cons.2 ⟨subd9_0_490, List.forall_mem_cons.2 ⟨subd9_0_491, List.forall_mem_cons.2 ⟨subd9_0_492, List.forall_mem_cons.2 ⟨subd9_0_493, List.forall_mem_cons.2 ⟨subd9_0_494, List.forall_mem_cons.2 ⟨subd9_0_495, List.forall_mem_cons.2 ⟨subd9_0_496, List.forall_mem_cons.2 ⟨subd9_0_497, List.forall_mem_cons.2 ⟨subd9_0_498, List.forall_mem_cons.2 ⟨subd9_0_499, List.forall_mem_cons.2 ⟨subd9_0_500, List.forall_mem_cons.2 ⟨subd9_0_501, List.forall_mem_cons.2 ⟨subd9_0_502, List.forall_mem_cons.2 ⟨subd9_0_503, List.forall_mem_cons.2 ⟨subd9_0_504, List.forall_mem_cons.2 ⟨subd9_0_505, List.forall_mem_cons.2 ⟨subd9_0_506, List.forall_mem_cons.2 ⟨subd9_0_507, List.forall_mem_cons.2 ⟨subd9_0_508, List.forall_mem_cons.2 ⟨subd9_0_509, List.forall_mem_cons.2 ⟨subd9_0_510, List.forall_mem_cons.2 ⟨subd9_0_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_512 : subd9_0 [2, 0, -7] = true := by decide +kernel
theorem subd9_0_513 : subd9_0 [2, 0, -6] = true := by decide +kernel
theorem subd9_0_514 : subd9_0 [2, 0, -5] = true := by decide +kernel
theorem subd9_0_515 : subd9_0 [2, 0, -4] = true := by decide +kernel
theorem subd9_0_516 : subd9_0 [2, 0, -3] = true := by decide +kernel
theorem subd9_0_517 : subd9_0 [2, 0, -2] = true := by decide +kernel
theorem subd9_0_518 : subd9_0 [2, 0, -1] = true := by decide +kernel
theorem subd9_0_519 : subd9_0 [2, 0, 0] = true := by decide +kernel
theorem subd9_0_520 : subd9_0 [2, 0, 1] = true := by decide +kernel
theorem subd9_0_521 : subd9_0 [2, 0, 2] = true := by decide +kernel
theorem subd9_0_522 : subd9_0 [2, 0, 3] = true := by decide +kernel
theorem subd9_0_523 : subd9_0 [2, 0, 4] = true := by decide +kernel
theorem subd9_0_524 : subd9_0 [2, 0, 5] = true := by decide +kernel
theorem subd9_0_525 : subd9_0 [2, 0, 6] = true := by decide +kernel
theorem subd9_0_526 : subd9_0 [2, 0, 7] = true := by decide +kernel
theorem subd9_0_527 : subd9_0 [2, 0, 8] = true := by decide +kernel
theorem subd9_0_528 : subd9_0 [2, 1, -8] = true := by decide +kernel
theorem subd9_0_529 : subd9_0 [2, 1, -7] = true := by decide +kernel
theorem subd9_0_530 : subd9_0 [2, 1, -6] = true := by decide +kernel
theorem subd9_0_531 : subd9_0 [2, 1, -5] = true := by decide +kernel
theorem subd9_0_532 : subd9_0 [2, 1, -4] = true := by decide +kernel
theorem subd9_0_533 : subd9_0 [2, 1, -3] = true := by decide +kernel
theorem subd9_0_534 : subd9_0 [2, 1, -2] = true := by decide +kernel
theorem subd9_0_535 : subd9_0 [2, 1, -1] = true := by decide +kernel
theorem subd9_0_536 : subd9_0 [2, 1, 0] = true := by decide +kernel
theorem subd9_0_537 : subd9_0 [2, 1, 1] = true := by decide +kernel
theorem subd9_0_538 : subd9_0 [2, 1, 2] = true := by decide +kernel
theorem subd9_0_539 : subd9_0 [2, 1, 3] = true := by decide +kernel
theorem subd9_0_540 : subd9_0 [2, 1, 4] = true := by decide +kernel
theorem subd9_0_541 : subd9_0 [2, 1, 5] = true := by decide +kernel
theorem subd9_0_542 : subd9_0 [2, 1, 6] = true := by decide +kernel
theorem subd9_0_543 : subd9_0 [2, 1, 7] = true := by decide +kernel
theorem sbd9_0_16 : ∀ q ∈ blkd9_0_16, subd9_0 q = true := by
  unfold blkd9_0_16
  exact List.forall_mem_cons.2 ⟨subd9_0_512, List.forall_mem_cons.2 ⟨subd9_0_513, List.forall_mem_cons.2 ⟨subd9_0_514, List.forall_mem_cons.2 ⟨subd9_0_515, List.forall_mem_cons.2 ⟨subd9_0_516, List.forall_mem_cons.2 ⟨subd9_0_517, List.forall_mem_cons.2 ⟨subd9_0_518, List.forall_mem_cons.2 ⟨subd9_0_519, List.forall_mem_cons.2 ⟨subd9_0_520, List.forall_mem_cons.2 ⟨subd9_0_521, List.forall_mem_cons.2 ⟨subd9_0_522, List.forall_mem_cons.2 ⟨subd9_0_523, List.forall_mem_cons.2 ⟨subd9_0_524, List.forall_mem_cons.2 ⟨subd9_0_525, List.forall_mem_cons.2 ⟨subd9_0_526, List.forall_mem_cons.2 ⟨subd9_0_527, List.forall_mem_cons.2 ⟨subd9_0_528, List.forall_mem_cons.2 ⟨subd9_0_529, List.forall_mem_cons.2 ⟨subd9_0_530, List.forall_mem_cons.2 ⟨subd9_0_531, List.forall_mem_cons.2 ⟨subd9_0_532, List.forall_mem_cons.2 ⟨subd9_0_533, List.forall_mem_cons.2 ⟨subd9_0_534, List.forall_mem_cons.2 ⟨subd9_0_535, List.forall_mem_cons.2 ⟨subd9_0_536, List.forall_mem_cons.2 ⟨subd9_0_537, List.forall_mem_cons.2 ⟨subd9_0_538, List.forall_mem_cons.2 ⟨subd9_0_539, List.forall_mem_cons.2 ⟨subd9_0_540, List.forall_mem_cons.2 ⟨subd9_0_541, List.forall_mem_cons.2 ⟨subd9_0_542, List.forall_mem_cons.2 ⟨subd9_0_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_544 : subd9_0 [2, 2, -7] = true := by decide +kernel
theorem subd9_0_545 : subd9_0 [2, 2, -6] = true := by decide +kernel
theorem subd9_0_546 : subd9_0 [2, 2, -5] = true := by decide +kernel
theorem subd9_0_547 : subd9_0 [2, 2, -4] = true := by decide +kernel
theorem subd9_0_548 : subd9_0 [2, 2, -3] = true := by decide +kernel
theorem subd9_0_549 : subd9_0 [2, 2, -2] = true := by decide +kernel
theorem subd9_0_550 : subd9_0 [2, 2, -1] = true := by decide +kernel
theorem subd9_0_551 : subd9_0 [2, 2, 0] = true := by decide +kernel
theorem subd9_0_552 : subd9_0 [2, 2, 1] = true := by decide +kernel
theorem subd9_0_553 : subd9_0 [2, 2, 2] = true := by decide +kernel
theorem subd9_0_554 : subd9_0 [2, 2, 3] = true := by decide +kernel
theorem subd9_0_555 : subd9_0 [2, 2, 4] = true := by decide +kernel
theorem subd9_0_556 : subd9_0 [2, 2, 5] = true := by decide +kernel
theorem subd9_0_557 : subd9_0 [2, 2, 6] = true := by decide +kernel
theorem subd9_0_558 : subd9_0 [2, 3] = true := by decide +kernel
theorem subd9_0_559 : subd9_0 [3, -5] = true := by decide +kernel
theorem subd9_0_560 : subd9_0 [3, -4] = true := by decide +kernel
theorem subd9_0_561 : subd9_0 [3, -3] = true := by decide +kernel
theorem subd9_0_562 : subd9_0 [3, -2] = true := by decide +kernel
theorem subd9_0_563 : subd9_0 [3, -1, -7] = true := by decide +kernel
theorem subd9_0_564 : subd9_0 [3, -1, -6] = true := by decide +kernel
theorem subd9_0_565 : subd9_0 [3, -1, -5] = true := by decide +kernel
theorem subd9_0_566 : subd9_0 [3, -1, -4] = true := by decide +kernel
theorem subd9_0_567 : subd9_0 [3, -1, -3] = true := by decide +kernel
theorem subd9_0_568 : subd9_0 [3, -1, -2] = true := by decide +kernel
theorem subd9_0_569 : subd9_0 [3, -1, -1] = true := by decide +kernel
theorem subd9_0_570 : subd9_0 [3, -1, 0] = true := by decide +kernel
theorem subd9_0_571 : subd9_0 [3, -1, 1] = true := by decide +kernel
theorem subd9_0_572 : subd9_0 [3, -1, 2] = true := by decide +kernel
theorem subd9_0_573 : subd9_0 [3, -1, 3] = true := by decide +kernel
theorem subd9_0_574 : subd9_0 [3, -1, 4] = true := by decide +kernel
theorem subd9_0_575 : subd9_0 [3, -1, 5] = true := by decide +kernel
theorem sbd9_0_17 : ∀ q ∈ blkd9_0_17, subd9_0 q = true := by
  unfold blkd9_0_17
  exact List.forall_mem_cons.2 ⟨subd9_0_544, List.forall_mem_cons.2 ⟨subd9_0_545, List.forall_mem_cons.2 ⟨subd9_0_546, List.forall_mem_cons.2 ⟨subd9_0_547, List.forall_mem_cons.2 ⟨subd9_0_548, List.forall_mem_cons.2 ⟨subd9_0_549, List.forall_mem_cons.2 ⟨subd9_0_550, List.forall_mem_cons.2 ⟨subd9_0_551, List.forall_mem_cons.2 ⟨subd9_0_552, List.forall_mem_cons.2 ⟨subd9_0_553, List.forall_mem_cons.2 ⟨subd9_0_554, List.forall_mem_cons.2 ⟨subd9_0_555, List.forall_mem_cons.2 ⟨subd9_0_556, List.forall_mem_cons.2 ⟨subd9_0_557, List.forall_mem_cons.2 ⟨subd9_0_558, List.forall_mem_cons.2 ⟨subd9_0_559, List.forall_mem_cons.2 ⟨subd9_0_560, List.forall_mem_cons.2 ⟨subd9_0_561, List.forall_mem_cons.2 ⟨subd9_0_562, List.forall_mem_cons.2 ⟨subd9_0_563, List.forall_mem_cons.2 ⟨subd9_0_564, List.forall_mem_cons.2 ⟨subd9_0_565, List.forall_mem_cons.2 ⟨subd9_0_566, List.forall_mem_cons.2 ⟨subd9_0_567, List.forall_mem_cons.2 ⟨subd9_0_568, List.forall_mem_cons.2 ⟨subd9_0_569, List.forall_mem_cons.2 ⟨subd9_0_570, List.forall_mem_cons.2 ⟨subd9_0_571, List.forall_mem_cons.2 ⟨subd9_0_572, List.forall_mem_cons.2 ⟨subd9_0_573, List.forall_mem_cons.2 ⟨subd9_0_574, List.forall_mem_cons.2 ⟨subd9_0_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_576 : subd9_0 [3, -1, 6] = true := by decide +kernel
theorem subd9_0_577 : subd9_0 [3, 0] = true := by decide +kernel
theorem subd9_0_578 : subd9_0 [3, 1] = true := by decide +kernel
theorem subd9_0_579 : subd9_0 [3, 2] = true := by decide +kernel
theorem subd9_0_580 : subd9_0 [4] = true := by decide +kernel
theorem sbd9_0_18 : ∀ q ∈ blkd9_0_18, subd9_0 q = true := by
  unfold blkd9_0_18
  exact List.forall_mem_cons.2 ⟨subd9_0_576, List.forall_mem_cons.2 ⟨subd9_0_577, List.forall_mem_cons.2 ⟨subd9_0_578, List.forall_mem_cons.2 ⟨subd9_0_579, List.forall_mem_cons.2 ⟨subd9_0_580, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd9_1 : ldCheck G d9_1.U d9_1.ms ldd9_1 = true := by decide +kernel
theorem pre_okd9_1 : subPre G cell9 d9_1 = true := by decide +kernel
theorem subd9_1_0 : subd9_1 [] = true := by decide +kernel
theorem sbd9_1_0 : ∀ q ∈ blkd9_1_0, subd9_1 q = true := by
  unfold blkd9_1_0
  exact List.forall_mem_cons.2 ⟨subd9_1_0, List.forall_mem_nil _⟩
theorem ld_okd9_2 : ldCheck G d9_2.U d9_2.ms ldd9_2 = true := by decide +kernel
theorem pre_okd9_2 : subPre G cell9 d9_2 = true := by decide +kernel
theorem subd9_2_0 : subd9_2 [-2] = true := by decide +kernel
theorem subd9_2_1 : subd9_2 [-1] = true := by decide +kernel
theorem subd9_2_2 : subd9_2 [0] = true := by decide +kernel
theorem subd9_2_3 : subd9_2 [1] = true := by decide +kernel
theorem subd9_2_4 : subd9_2 [2] = true := by decide +kernel
theorem sbd9_2_0 : ∀ q ∈ blkd9_2_0, subd9_2 q = true := by
  unfold blkd9_2_0
  exact List.forall_mem_cons.2 ⟨subd9_2_0, List.forall_mem_cons.2 ⟨subd9_2_1, List.forall_mem_cons.2 ⟨subd9_2_2, List.forall_mem_cons.2 ⟨subd9_2_3, List.forall_mem_cons.2 ⟨subd9_2_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd9_3 : ldCheck G d9_3.U d9_3.ms ldd9_3 = true := by decide +kernel
theorem pre_okd9_3 : subPre G cell9 d9_3 = true := by decide +kernel
theorem subd9_3_0 : subd9_3 [-1] = true := by decide +kernel
theorem subd9_3_1 : subd9_3 [0] = true := by decide +kernel
theorem subd9_3_2 : subd9_3 [1] = true := by decide +kernel
theorem sbd9_3_0 : ∀ q ∈ blkd9_3_0, subd9_3 q = true := by
  unfold blkd9_3_0
  exact List.forall_mem_cons.2 ⟨subd9_3_0, List.forall_mem_cons.2 ⟨subd9_3_1, List.forall_mem_cons.2 ⟨subd9_3_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd9_4 : ldCheck G d9_4.U d9_4.ms ldd9_4 = true := by decide +kernel
theorem pre_okd9_4 : subPre G cell9 d9_4 = true := by decide +kernel
theorem subd9_4_0 : subd9_4 [-1] = true := by decide +kernel
theorem subd9_4_1 : subd9_4 [0] = true := by decide +kernel
theorem subd9_4_2 : subd9_4 [1] = true := by decide +kernel
theorem sbd9_4_0 : ∀ q ∈ blkd9_4_0, subd9_4 q = true := by
  unfold blkd9_4_0
  exact List.forall_mem_cons.2 ⟨subd9_4_0, List.forall_mem_cons.2 ⟨subd9_4_1, List.forall_mem_cons.2 ⟨subd9_4_2, List.forall_mem_nil _⟩⟩⟩

end ReflectZphi.Data.Cert5.C093
