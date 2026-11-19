import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd17_2_416 : subd17_2 [0, 0, -6] = true := by decide +kernel
theorem subd17_2_417 : subd17_2 [0, 0, -5] = true := by decide +kernel
theorem subd17_2_418 : subd17_2 [0, 0, -4] = true := by decide +kernel
theorem subd17_2_419 : subd17_2 [0, 0, -3] = true := by decide +kernel
theorem subd17_2_420 : subd17_2 [0, 0, -2] = true := by decide +kernel
theorem subd17_2_421 : subd17_2 [0, 0, -1] = true := by decide +kernel
theorem subd17_2_422 : subd17_2 [0, 0, 0] = true := by decide +kernel
theorem subd17_2_423 : subd17_2 [0, 0, 1] = true := by decide +kernel
theorem subd17_2_424 : subd17_2 [0, 0, 2] = true := by decide +kernel
theorem subd17_2_425 : subd17_2 [0, 0, 3] = true := by decide +kernel
theorem subd17_2_426 : subd17_2 [0, 0, 4] = true := by decide +kernel
theorem subd17_2_427 : subd17_2 [0, 0, 5] = true := by decide +kernel
theorem subd17_2_428 : subd17_2 [0, 0, 6] = true := by decide +kernel
theorem subd17_2_429 : subd17_2 [0, 0, 7] = true := by decide +kernel
theorem subd17_2_430 : subd17_2 [0, 0, 8] = true := by decide +kernel
theorem subd17_2_431 : subd17_2 [0, 1, -9] = true := by decide +kernel
theorem subd17_2_432 : subd17_2 [0, 1, -8] = true := by decide +kernel
theorem subd17_2_433 : subd17_2 [0, 1, -7] = true := by decide +kernel
theorem subd17_2_434 : subd17_2 [0, 1, -6] = true := by decide +kernel
theorem subd17_2_435 : subd17_2 [0, 1, -5] = true := by decide +kernel
theorem subd17_2_436 : subd17_2 [0, 1, -4] = true := by decide +kernel
theorem subd17_2_437 : subd17_2 [0, 1, -3] = true := by decide +kernel
theorem subd17_2_438 : subd17_2 [0, 1, -2] = true := by decide +kernel
theorem subd17_2_439 : subd17_2 [0, 1, -1] = true := by decide +kernel
theorem subd17_2_440 : subd17_2 [0, 1, 0] = true := by decide +kernel
theorem subd17_2_441 : subd17_2 [0, 1, 1] = true := by decide +kernel
theorem subd17_2_442 : subd17_2 [0, 1, 2] = true := by decide +kernel
theorem subd17_2_443 : subd17_2 [0, 1, 3] = true := by decide +kernel
theorem subd17_2_444 : subd17_2 [0, 1, 4] = true := by decide +kernel
theorem subd17_2_445 : subd17_2 [0, 1, 5] = true := by decide +kernel
theorem subd17_2_446 : subd17_2 [0, 1, 6] = true := by decide +kernel
theorem subd17_2_447 : subd17_2 [0, 1, 7] = true := by decide +kernel
theorem sbd17_2_13 : ∀ q ∈ blkd17_2_13, subd17_2 q = true := by
  unfold blkd17_2_13
  exact List.forall_mem_cons.2 ⟨subd17_2_416, List.forall_mem_cons.2 ⟨subd17_2_417, List.forall_mem_cons.2 ⟨subd17_2_418, List.forall_mem_cons.2 ⟨subd17_2_419, List.forall_mem_cons.2 ⟨subd17_2_420, List.forall_mem_cons.2 ⟨subd17_2_421, List.forall_mem_cons.2 ⟨subd17_2_422, List.forall_mem_cons.2 ⟨subd17_2_423, List.forall_mem_cons.2 ⟨subd17_2_424, List.forall_mem_cons.2 ⟨subd17_2_425, List.forall_mem_cons.2 ⟨subd17_2_426, List.forall_mem_cons.2 ⟨subd17_2_427, List.forall_mem_cons.2 ⟨subd17_2_428, List.forall_mem_cons.2 ⟨subd17_2_429, List.forall_mem_cons.2 ⟨subd17_2_430, List.forall_mem_cons.2 ⟨subd17_2_431, List.forall_mem_cons.2 ⟨subd17_2_432, List.forall_mem_cons.2 ⟨subd17_2_433, List.forall_mem_cons.2 ⟨subd17_2_434, List.forall_mem_cons.2 ⟨subd17_2_435, List.forall_mem_cons.2 ⟨subd17_2_436, List.forall_mem_cons.2 ⟨subd17_2_437, List.forall_mem_cons.2 ⟨subd17_2_438, List.forall_mem_cons.2 ⟨subd17_2_439, List.forall_mem_cons.2 ⟨subd17_2_440, List.forall_mem_cons.2 ⟨subd17_2_441, List.forall_mem_cons.2 ⟨subd17_2_442, List.forall_mem_cons.2 ⟨subd17_2_443, List.forall_mem_cons.2 ⟨subd17_2_444, List.forall_mem_cons.2 ⟨subd17_2_445, List.forall_mem_cons.2 ⟨subd17_2_446, List.forall_mem_cons.2 ⟨subd17_2_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_2_448 : subd17_2 [0, 1, 8] = true := by decide +kernel
theorem subd17_2_449 : subd17_2 [0, 2, -8] = true := by decide +kernel
theorem subd17_2_450 : subd17_2 [0, 2, -7] = true := by decide +kernel
theorem subd17_2_451 : subd17_2 [0, 2, -6] = true := by decide +kernel
theorem subd17_2_452 : subd17_2 [0, 2, -5] = true := by decide +kernel
theorem subd17_2_453 : subd17_2 [0, 2, -4] = true := by decide +kernel
theorem subd17_2_454 : subd17_2 [0, 2, -3] = true := by decide +kernel
theorem subd17_2_455 : subd17_2 [0, 2, -2] = true := by decide +kernel
theorem subd17_2_456 : subd17_2 [0, 2, -1] = true := by decide +kernel
theorem subd17_2_457 : subd17_2 [0, 2, 0] = true := by decide +kernel
theorem subd17_2_458 : subd17_2 [0, 2, 1] = true := by decide +kernel
theorem subd17_2_459 : subd17_2 [0, 2, 2] = true := by decide +kernel
theorem subd17_2_460 : subd17_2 [0, 2, 3] = true := by decide +kernel
theorem subd17_2_461 : subd17_2 [0, 2, 4] = true := by decide +kernel
theorem subd17_2_462 : subd17_2 [0, 2, 5] = true := by decide +kernel
theorem subd17_2_463 : subd17_2 [0, 2, 6] = true := by decide +kernel
theorem subd17_2_464 : subd17_2 [0, 2, 7] = true := by decide +kernel
theorem subd17_2_465 : subd17_2 [0, 2, 8] = true := by decide +kernel
theorem subd17_2_466 : subd17_2 [0, 3, -7] = true := by decide +kernel
theorem subd17_2_467 : subd17_2 [0, 3, -6] = true := by decide +kernel
theorem subd17_2_468 : subd17_2 [0, 3, -5] = true := by decide +kernel
theorem subd17_2_469 : subd17_2 [0, 3, -4] = true := by decide +kernel
theorem subd17_2_470 : subd17_2 [0, 3, -3] = true := by decide +kernel
theorem subd17_2_471 : subd17_2 [0, 3, -2] = true := by decide +kernel
theorem subd17_2_472 : subd17_2 [0, 3, -1] = true := by decide +kernel
theorem subd17_2_473 : subd17_2 [0, 3, 0] = true := by decide +kernel
theorem subd17_2_474 : subd17_2 [0, 3, 1] = true := by decide +kernel
theorem subd17_2_475 : subd17_2 [0, 3, 2] = true := by decide +kernel
theorem subd17_2_476 : subd17_2 [0, 3, 3] = true := by decide +kernel
theorem subd17_2_477 : subd17_2 [0, 3, 4] = true := by decide +kernel
theorem subd17_2_478 : subd17_2 [0, 3, 5] = true := by decide +kernel
theorem subd17_2_479 : subd17_2 [0, 3, 6] = true := by decide +kernel
theorem sbd17_2_14 : ∀ q ∈ blkd17_2_14, subd17_2 q = true := by
  unfold blkd17_2_14
  exact List.forall_mem_cons.2 ⟨subd17_2_448, List.forall_mem_cons.2 ⟨subd17_2_449, List.forall_mem_cons.2 ⟨subd17_2_450, List.forall_mem_cons.2 ⟨subd17_2_451, List.forall_mem_cons.2 ⟨subd17_2_452, List.forall_mem_cons.2 ⟨subd17_2_453, List.forall_mem_cons.2 ⟨subd17_2_454, List.forall_mem_cons.2 ⟨subd17_2_455, List.forall_mem_cons.2 ⟨subd17_2_456, List.forall_mem_cons.2 ⟨subd17_2_457, List.forall_mem_cons.2 ⟨subd17_2_458, List.forall_mem_cons.2 ⟨subd17_2_459, List.forall_mem_cons.2 ⟨subd17_2_460, List.forall_mem_cons.2 ⟨subd17_2_461, List.forall_mem_cons.2 ⟨subd17_2_462, List.forall_mem_cons.2 ⟨subd17_2_463, List.forall_mem_cons.2 ⟨subd17_2_464, List.forall_mem_cons.2 ⟨subd17_2_465, List.forall_mem_cons.2 ⟨subd17_2_466, List.forall_mem_cons.2 ⟨subd17_2_467, List.forall_mem_cons.2 ⟨subd17_2_468, List.forall_mem_cons.2 ⟨subd17_2_469, List.forall_mem_cons.2 ⟨subd17_2_470, List.forall_mem_cons.2 ⟨subd17_2_471, List.forall_mem_cons.2 ⟨subd17_2_472, List.forall_mem_cons.2 ⟨subd17_2_473, List.forall_mem_cons.2 ⟨subd17_2_474, List.forall_mem_cons.2 ⟨subd17_2_475, List.forall_mem_cons.2 ⟨subd17_2_476, List.forall_mem_cons.2 ⟨subd17_2_477, List.forall_mem_cons.2 ⟨subd17_2_478, List.forall_mem_cons.2 ⟨subd17_2_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_2_480 : subd17_2 [0, 3, 7] = true := by decide +kernel
theorem subd17_2_481 : subd17_2 [0, 3, 8] = true := by decide +kernel
theorem subd17_2_482 : subd17_2 [0, 4, -5] = true := by decide +kernel
theorem subd17_2_483 : subd17_2 [0, 4, -4] = true := by decide +kernel
theorem subd17_2_484 : subd17_2 [0, 4, -3] = true := by decide +kernel
theorem subd17_2_485 : subd17_2 [0, 4, -2] = true := by decide +kernel
theorem subd17_2_486 : subd17_2 [0, 4, -1] = true := by decide +kernel
theorem subd17_2_487 : subd17_2 [0, 4, 0] = true := by decide +kernel
theorem subd17_2_488 : subd17_2 [0, 4, 1] = true := by decide +kernel
theorem subd17_2_489 : subd17_2 [0, 4, 2] = true := by decide +kernel
theorem subd17_2_490 : subd17_2 [0, 4, 3] = true := by decide +kernel
theorem subd17_2_491 : subd17_2 [0, 4, 4] = true := by decide +kernel
theorem subd17_2_492 : subd17_2 [0, 4, 5] = true := by decide +kernel
theorem subd17_2_493 : subd17_2 [0, 4, 6] = true := by decide +kernel
theorem subd17_2_494 : subd17_2 [0, 4, 7] = true := by decide +kernel
theorem subd17_2_495 : subd17_2 [0, 5] = true := by decide +kernel
theorem subd17_2_496 : subd17_2 [0, 6] = true := by decide +kernel
theorem subd17_2_497 : subd17_2 [1, -6] = true := by decide +kernel
theorem subd17_2_498 : subd17_2 [1, -5] = true := by decide +kernel
theorem subd17_2_499 : subd17_2 [1, -4] = true := by decide +kernel
theorem subd17_2_500 : subd17_2 [1, -3, -8] = true := by decide +kernel
theorem subd17_2_501 : subd17_2 [1, -3, -7] = true := by decide +kernel
theorem subd17_2_502 : subd17_2 [1, -3, -6] = true := by decide +kernel
theorem subd17_2_503 : subd17_2 [1, -3, -5] = true := by decide +kernel
theorem subd17_2_504 : subd17_2 [1, -3, -4] = true := by decide +kernel
theorem subd17_2_505 : subd17_2 [1, -3, -3] = true := by decide +kernel
theorem subd17_2_506 : subd17_2 [1, -3, -2] = true := by decide +kernel
theorem subd17_2_507 : subd17_2 [1, -3, -1] = true := by decide +kernel
theorem subd17_2_508 : subd17_2 [1, -3, 0] = true := by decide +kernel
theorem subd17_2_509 : subd17_2 [1, -3, 1] = true := by decide +kernel
theorem subd17_2_510 : subd17_2 [1, -3, 2] = true := by decide +kernel
theorem subd17_2_511 : subd17_2 [1, -3, 3] = true := by decide +kernel
theorem sbd17_2_15 : ∀ q ∈ blkd17_2_15, subd17_2 q = true := by
  unfold blkd17_2_15
  exact List.forall_mem_cons.2 ⟨subd17_2_480, List.forall_mem_cons.2 ⟨subd17_2_481, List.forall_mem_cons.2 ⟨subd17_2_482, List.forall_mem_cons.2 ⟨subd17_2_483, List.forall_mem_cons.2 ⟨subd17_2_484, List.forall_mem_cons.2 ⟨subd17_2_485, List.forall_mem_cons.2 ⟨subd17_2_486, List.forall_mem_cons.2 ⟨subd17_2_487, List.forall_mem_cons.2 ⟨subd17_2_488, List.forall_mem_cons.2 ⟨subd17_2_489, List.forall_mem_cons.2 ⟨subd17_2_490, List.forall_mem_cons.2 ⟨subd17_2_491, List.forall_mem_cons.2 ⟨subd17_2_492, List.forall_mem_cons.2 ⟨subd17_2_493, List.forall_mem_cons.2 ⟨subd17_2_494, List.forall_mem_cons.2 ⟨subd17_2_495, List.forall_mem_cons.2 ⟨subd17_2_496, List.forall_mem_cons.2 ⟨subd17_2_497, List.forall_mem_cons.2 ⟨subd17_2_498, List.forall_mem_cons.2 ⟨subd17_2_499, List.forall_mem_cons.2 ⟨subd17_2_500, List.forall_mem_cons.2 ⟨subd17_2_501, List.forall_mem_cons.2 ⟨subd17_2_502, List.forall_mem_cons.2 ⟨subd17_2_503, List.forall_mem_cons.2 ⟨subd17_2_504, List.forall_mem_cons.2 ⟨subd17_2_505, List.forall_mem_cons.2 ⟨subd17_2_506, List.forall_mem_cons.2 ⟨subd17_2_507, List.forall_mem_cons.2 ⟨subd17_2_508, List.forall_mem_cons.2 ⟨subd17_2_509, List.forall_mem_cons.2 ⟨subd17_2_510, List.forall_mem_cons.2 ⟨subd17_2_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_2_512 : subd17_2 [1, -3, 4] = true := by decide +kernel
theorem subd17_2_513 : subd17_2 [1, -3, 5] = true := by decide +kernel
theorem subd17_2_514 : subd17_2 [1, -2, -9] = true := by decide +kernel
theorem subd17_2_515 : subd17_2 [1, -2, -8] = true := by decide +kernel
theorem subd17_2_516 : subd17_2 [1, -2, -7] = true := by decide +kernel
theorem subd17_2_517 : subd17_2 [1, -2, -6] = true := by decide +kernel
theorem subd17_2_518 : subd17_2 [1, -2, -5] = true := by decide +kernel
theorem subd17_2_519 : subd17_2 [1, -2, -4] = true := by decide +kernel
theorem subd17_2_520 : subd17_2 [1, -2, -3] = true := by decide +kernel
theorem subd17_2_521 : subd17_2 [1, -2, -2] = true := by decide +kernel
theorem subd17_2_522 : subd17_2 [1, -2, -1] = true := by decide +kernel
theorem subd17_2_523 : subd17_2 [1, -2, 0] = true := by decide +kernel
theorem subd17_2_524 : subd17_2 [1, -2, 1] = true := by decide +kernel
theorem subd17_2_525 : subd17_2 [1, -2, 2] = true := by decide +kernel
theorem subd17_2_526 : subd17_2 [1, -2, 3] = true := by decide +kernel
theorem subd17_2_527 : subd17_2 [1, -2, 4] = true := by decide +kernel
theorem subd17_2_528 : subd17_2 [1, -2, 5] = true := by decide +kernel
theorem subd17_2_529 : subd17_2 [1, -2, 6] = true := by decide +kernel
theorem subd17_2_530 : subd17_2 [1, -2, 7] = true := by decide +kernel
theorem subd17_2_531 : subd17_2 [1, -1, -9] = true := by decide +kernel
theorem subd17_2_532 : subd17_2 [1, -1, -8] = true := by decide +kernel
theorem subd17_2_533 : subd17_2 [1, -1, -7] = true := by decide +kernel
theorem subd17_2_534 : subd17_2 [1, -1, -6] = true := by decide +kernel
theorem subd17_2_535 : subd17_2 [1, -1, -5] = true := by decide +kernel
theorem subd17_2_536 : subd17_2 [1, -1, -4] = true := by decide +kernel
theorem subd17_2_537 : subd17_2 [1, -1, -3] = true := by decide +kernel
theorem subd17_2_538 : subd17_2 [1, -1, -2] = true := by decide +kernel
theorem subd17_2_539 : subd17_2 [1, -1, -1] = true := by decide +kernel
theorem subd17_2_540 : subd17_2 [1, -1, 0] = true := by decide +kernel
theorem subd17_2_541 : subd17_2 [1, -1, 1] = true := by decide +kernel
theorem subd17_2_542 : subd17_2 [1, -1, 2] = true := by decide +kernel
theorem subd17_2_543 : subd17_2 [1, -1, 3] = true := by decide +kernel
theorem sbd17_2_16 : ∀ q ∈ blkd17_2_16, subd17_2 q = true := by
  unfold blkd17_2_16
  exact List.forall_mem_cons.2 ⟨subd17_2_512, List.forall_mem_cons.2 ⟨subd17_2_513, List.forall_mem_cons.2 ⟨subd17_2_514, List.forall_mem_cons.2 ⟨subd17_2_515, List.forall_mem_cons.2 ⟨subd17_2_516, List.forall_mem_cons.2 ⟨subd17_2_517, List.forall_mem_cons.2 ⟨subd17_2_518, List.forall_mem_cons.2 ⟨subd17_2_519, List.forall_mem_cons.2 ⟨subd17_2_520, List.forall_mem_cons.2 ⟨subd17_2_521, List.forall_mem_cons.2 ⟨subd17_2_522, List.forall_mem_cons.2 ⟨subd17_2_523, List.forall_mem_cons.2 ⟨subd17_2_524, List.forall_mem_cons.2 ⟨subd17_2_525, List.forall_mem_cons.2 ⟨subd17_2_526, List.forall_mem_cons.2 ⟨subd17_2_527, List.forall_mem_cons.2 ⟨subd17_2_528, List.forall_mem_cons.2 ⟨subd17_2_529, List.forall_mem_cons.2 ⟨subd17_2_530, List.forall_mem_cons.2 ⟨subd17_2_531, List.forall_mem_cons.2 ⟨subd17_2_532, List.forall_mem_cons.2 ⟨subd17_2_533, List.forall_mem_cons.2 ⟨subd17_2_534, List.forall_mem_cons.2 ⟨subd17_2_535, List.forall_mem_cons.2 ⟨subd17_2_536, List.forall_mem_cons.2 ⟨subd17_2_537, List.forall_mem_cons.2 ⟨subd17_2_538, List.forall_mem_cons.2 ⟨subd17_2_539, List.forall_mem_cons.2 ⟨subd17_2_540, List.forall_mem_cons.2 ⟨subd17_2_541, List.forall_mem_cons.2 ⟨subd17_2_542, List.forall_mem_cons.2 ⟨subd17_2_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_2_544 : subd17_2 [1, -1, 4] = true := by decide +kernel
theorem subd17_2_545 : subd17_2 [1, -1, 5] = true := by decide +kernel
theorem subd17_2_546 : subd17_2 [1, -1, 6] = true := by decide +kernel
theorem subd17_2_547 : subd17_2 [1, -1, 7] = true := by decide +kernel
theorem subd17_2_548 : subd17_2 [1, 0, -9] = true := by decide +kernel
theorem subd17_2_549 : subd17_2 [1, 0, -8] = true := by decide +kernel
theorem subd17_2_550 : subd17_2 [1, 0, -7] = true := by decide +kernel
theorem subd17_2_551 : subd17_2 [1, 0, -6] = true := by decide +kernel
theorem subd17_2_552 : subd17_2 [1, 0, -5] = true := by decide +kernel
theorem subd17_2_553 : subd17_2 [1, 0, -4] = true := by decide +kernel
theorem subd17_2_554 : subd17_2 [1, 0, -3] = true := by decide +kernel
theorem subd17_2_555 : subd17_2 [1, 0, -2] = true := by decide +kernel
theorem subd17_2_556 : subd17_2 [1, 0, -1] = true := by decide +kernel
theorem subd17_2_557 : subd17_2 [1, 0, 0] = true := by decide +kernel
theorem subd17_2_558 : subd17_2 [1, 0, 1] = true := by decide +kernel
theorem subd17_2_559 : subd17_2 [1, 0, 2] = true := by decide +kernel
theorem subd17_2_560 : subd17_2 [1, 0, 3] = true := by decide +kernel
theorem subd17_2_561 : subd17_2 [1, 0, 4] = true := by decide +kernel
theorem subd17_2_562 : subd17_2 [1, 0, 5] = true := by decide +kernel
theorem subd17_2_563 : subd17_2 [1, 0, 6] = true := by decide +kernel
theorem subd17_2_564 : subd17_2 [1, 0, 7] = true := by decide +kernel
theorem subd17_2_565 : subd17_2 [1, 0, 8] = true := by decide +kernel
theorem subd17_2_566 : subd17_2 [1, 1, -8] = true := by decide +kernel
theorem subd17_2_567 : subd17_2 [1, 1, -7] = true := by decide +kernel
theorem subd17_2_568 : subd17_2 [1, 1, -6] = true := by decide +kernel
theorem subd17_2_569 : subd17_2 [1, 1, -5] = true := by decide +kernel
theorem subd17_2_570 : subd17_2 [1, 1, -4] = true := by decide +kernel
theorem subd17_2_571 : subd17_2 [1, 1, -3] = true := by decide +kernel
theorem subd17_2_572 : subd17_2 [1, 1, -2] = true := by decide +kernel
theorem subd17_2_573 : subd17_2 [1, 1, -1] = true := by decide +kernel
theorem subd17_2_574 : subd17_2 [1, 1, 0] = true := by decide +kernel
theorem subd17_2_575 : subd17_2 [1, 1, 1] = true := by decide +kernel
theorem sbd17_2_17 : ∀ q ∈ blkd17_2_17, subd17_2 q = true := by
  unfold blkd17_2_17
  exact List.forall_mem_cons.2 ⟨subd17_2_544, List.forall_mem_cons.2 ⟨subd17_2_545, List.forall_mem_cons.2 ⟨subd17_2_546, List.forall_mem_cons.2 ⟨subd17_2_547, List.forall_mem_cons.2 ⟨subd17_2_548, List.forall_mem_cons.2 ⟨subd17_2_549, List.forall_mem_cons.2 ⟨subd17_2_550, List.forall_mem_cons.2 ⟨subd17_2_551, List.forall_mem_cons.2 ⟨subd17_2_552, List.forall_mem_cons.2 ⟨subd17_2_553, List.forall_mem_cons.2 ⟨subd17_2_554, List.forall_mem_cons.2 ⟨subd17_2_555, List.forall_mem_cons.2 ⟨subd17_2_556, List.forall_mem_cons.2 ⟨subd17_2_557, List.forall_mem_cons.2 ⟨subd17_2_558, List.forall_mem_cons.2 ⟨subd17_2_559, List.forall_mem_cons.2 ⟨subd17_2_560, List.forall_mem_cons.2 ⟨subd17_2_561, List.forall_mem_cons.2 ⟨subd17_2_562, List.forall_mem_cons.2 ⟨subd17_2_563, List.forall_mem_cons.2 ⟨subd17_2_564, List.forall_mem_cons.2 ⟨subd17_2_565, List.forall_mem_cons.2 ⟨subd17_2_566, List.forall_mem_cons.2 ⟨subd17_2_567, List.forall_mem_cons.2 ⟨subd17_2_568, List.forall_mem_cons.2 ⟨subd17_2_569, List.forall_mem_cons.2 ⟨subd17_2_570, List.forall_mem_cons.2 ⟨subd17_2_571, List.forall_mem_cons.2 ⟨subd17_2_572, List.forall_mem_cons.2 ⟨subd17_2_573, List.forall_mem_cons.2 ⟨subd17_2_574, List.forall_mem_cons.2 ⟨subd17_2_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_2_576 : subd17_2 [1, 1, 2] = true := by decide +kernel
theorem subd17_2_577 : subd17_2 [1, 1, 3] = true := by decide +kernel
theorem subd17_2_578 : subd17_2 [1, 1, 4] = true := by decide +kernel
theorem subd17_2_579 : subd17_2 [1, 1, 5] = true := by decide +kernel
theorem subd17_2_580 : subd17_2 [1, 1, 6] = true := by decide +kernel
theorem subd17_2_581 : subd17_2 [1, 1, 7] = true := by decide +kernel
theorem subd17_2_582 : subd17_2 [1, 1, 8] = true := by decide +kernel
theorem subd17_2_583 : subd17_2 [1, 2, -8] = true := by decide +kernel
theorem subd17_2_584 : subd17_2 [1, 2, -7] = true := by decide +kernel
theorem subd17_2_585 : subd17_2 [1, 2, -6] = true := by decide +kernel
theorem subd17_2_586 : subd17_2 [1, 2, -5] = true := by decide +kernel
theorem subd17_2_587 : subd17_2 [1, 2, -4] = true := by decide +kernel
theorem subd17_2_588 : subd17_2 [1, 2, -3] = true := by decide +kernel
theorem subd17_2_589 : subd17_2 [1, 2, -2] = true := by decide +kernel
theorem subd17_2_590 : subd17_2 [1, 2, -1] = true := by decide +kernel
theorem subd17_2_591 : subd17_2 [1, 2, 0] = true := by decide +kernel
theorem subd17_2_592 : subd17_2 [1, 2, 1] = true := by decide +kernel
theorem subd17_2_593 : subd17_2 [1, 2, 2] = true := by decide +kernel
theorem subd17_2_594 : subd17_2 [1, 2, 3] = true := by decide +kernel
theorem subd17_2_595 : subd17_2 [1, 2, 4] = true := by decide +kernel
theorem subd17_2_596 : subd17_2 [1, 2, 5] = true := by decide +kernel
theorem subd17_2_597 : subd17_2 [1, 2, 6] = true := by decide +kernel
theorem subd17_2_598 : subd17_2 [1, 2, 7] = true := by decide +kernel
theorem subd17_2_599 : subd17_2 [1, 2, 8] = true := by decide +kernel
theorem subd17_2_600 : subd17_2 [1, 3, -7] = true := by decide +kernel
theorem subd17_2_601 : subd17_2 [1, 3, -6] = true := by decide +kernel
theorem subd17_2_602 : subd17_2 [1, 3, -5] = true := by decide +kernel
theorem subd17_2_603 : subd17_2 [1, 3, -4] = true := by decide +kernel
theorem subd17_2_604 : subd17_2 [1, 3, -3] = true := by decide +kernel
theorem subd17_2_605 : subd17_2 [1, 3, -2] = true := by decide +kernel
theorem subd17_2_606 : subd17_2 [1, 3, -1] = true := by decide +kernel
theorem subd17_2_607 : subd17_2 [1, 3, 0] = true := by decide +kernel
theorem sbd17_2_18 : ∀ q ∈ blkd17_2_18, subd17_2 q = true := by
  unfold blkd17_2_18
  exact List.forall_mem_cons.2 ⟨subd17_2_576, List.forall_mem_cons.2 ⟨subd17_2_577, List.forall_mem_cons.2 ⟨subd17_2_578, List.forall_mem_cons.2 ⟨subd17_2_579, List.forall_mem_cons.2 ⟨subd17_2_580, List.forall_mem_cons.2 ⟨subd17_2_581, List.forall_mem_cons.2 ⟨subd17_2_582, List.forall_mem_cons.2 ⟨subd17_2_583, List.forall_mem_cons.2 ⟨subd17_2_584, List.forall_mem_cons.2 ⟨subd17_2_585, List.forall_mem_cons.2 ⟨subd17_2_586, List.forall_mem_cons.2 ⟨subd17_2_587, List.forall_mem_cons.2 ⟨subd17_2_588, List.forall_mem_cons.2 ⟨subd17_2_589, List.forall_mem_cons.2 ⟨subd17_2_590, List.forall_mem_cons.2 ⟨subd17_2_591, List.forall_mem_cons.2 ⟨subd17_2_592, List.forall_mem_cons.2 ⟨subd17_2_593, List.forall_mem_cons.2 ⟨subd17_2_594, List.forall_mem_cons.2 ⟨subd17_2_595, List.forall_mem_cons.2 ⟨subd17_2_596, List.forall_mem_cons.2 ⟨subd17_2_597, List.forall_mem_cons.2 ⟨subd17_2_598, List.forall_mem_cons.2 ⟨subd17_2_599, List.forall_mem_cons.2 ⟨subd17_2_600, List.forall_mem_cons.2 ⟨subd17_2_601, List.forall_mem_cons.2 ⟨subd17_2_602, List.forall_mem_cons.2 ⟨subd17_2_603, List.forall_mem_cons.2 ⟨subd17_2_604, List.forall_mem_cons.2 ⟨subd17_2_605, List.forall_mem_cons.2 ⟨subd17_2_606, List.forall_mem_cons.2 ⟨subd17_2_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_2_608 : subd17_2 [1, 3, 1] = true := by decide +kernel
theorem subd17_2_609 : subd17_2 [1, 3, 2] = true := by decide +kernel
theorem subd17_2_610 : subd17_2 [1, 3, 3] = true := by decide +kernel
theorem subd17_2_611 : subd17_2 [1, 3, 4] = true := by decide +kernel
theorem subd17_2_612 : subd17_2 [1, 3, 5] = true := by decide +kernel
theorem subd17_2_613 : subd17_2 [1, 3, 6] = true := by decide +kernel
theorem subd17_2_614 : subd17_2 [1, 3, 7] = true := by decide +kernel
theorem subd17_2_615 : subd17_2 [1, 3, 8] = true := by decide +kernel
theorem subd17_2_616 : subd17_2 [1, 4, -6] = true := by decide +kernel
theorem subd17_2_617 : subd17_2 [1, 4, -5] = true := by decide +kernel
theorem subd17_2_618 : subd17_2 [1, 4, -4] = true := by decide +kernel
theorem subd17_2_619 : subd17_2 [1, 4, -3] = true := by decide +kernel
theorem subd17_2_620 : subd17_2 [1, 4, -2] = true := by decide +kernel
theorem subd17_2_621 : subd17_2 [1, 4, -1] = true := by decide +kernel
theorem subd17_2_622 : subd17_2 [1, 4, 0] = true := by decide +kernel
theorem subd17_2_623 : subd17_2 [1, 4, 1] = true := by decide +kernel
theorem subd17_2_624 : subd17_2 [1, 4, 2] = true := by decide +kernel
theorem subd17_2_625 : subd17_2 [1, 4, 3] = true := by decide +kernel
theorem subd17_2_626 : subd17_2 [1, 4, 4] = true := by decide +kernel
theorem subd17_2_627 : subd17_2 [1, 4, 5] = true := by decide +kernel
theorem subd17_2_628 : subd17_2 [1, 4, 6] = true := by decide +kernel
theorem subd17_2_629 : subd17_2 [1, 4, 7] = true := by decide +kernel
theorem subd17_2_630 : subd17_2 [1, 4, 8] = true := by decide +kernel
theorem subd17_2_631 : subd17_2 [1, 5] = true := by decide +kernel
theorem subd17_2_632 : subd17_2 [1, 6] = true := by decide +kernel
theorem subd17_2_633 : subd17_2 [2, -5] = true := by decide +kernel
theorem subd17_2_634 : subd17_2 [2, -4] = true := by decide +kernel
theorem subd17_2_635 : subd17_2 [2, -3] = true := by decide +kernel
theorem subd17_2_636 : subd17_2 [2, -2, -8] = true := by decide +kernel
theorem subd17_2_637 : subd17_2 [2, -2, -7] = true := by decide +kernel
theorem subd17_2_638 : subd17_2 [2, -2, -6] = true := by decide +kernel
theorem subd17_2_639 : subd17_2 [2, -2, -5] = true := by decide +kernel
theorem sbd17_2_19 : ∀ q ∈ blkd17_2_19, subd17_2 q = true := by
  unfold blkd17_2_19
  exact List.forall_mem_cons.2 ⟨subd17_2_608, List.forall_mem_cons.2 ⟨subd17_2_609, List.forall_mem_cons.2 ⟨subd17_2_610, List.forall_mem_cons.2 ⟨subd17_2_611, List.forall_mem_cons.2 ⟨subd17_2_612, List.forall_mem_cons.2 ⟨subd17_2_613, List.forall_mem_cons.2 ⟨subd17_2_614, List.forall_mem_cons.2 ⟨subd17_2_615, List.forall_mem_cons.2 ⟨subd17_2_616, List.forall_mem_cons.2 ⟨subd17_2_617, List.forall_mem_cons.2 ⟨subd17_2_618, List.forall_mem_cons.2 ⟨subd17_2_619, List.forall_mem_cons.2 ⟨subd17_2_620, List.forall_mem_cons.2 ⟨subd17_2_621, List.forall_mem_cons.2 ⟨subd17_2_622, List.forall_mem_cons.2 ⟨subd17_2_623, List.forall_mem_cons.2 ⟨subd17_2_624, List.forall_mem_cons.2 ⟨subd17_2_625, List.forall_mem_cons.2 ⟨subd17_2_626, List.forall_mem_cons.2 ⟨subd17_2_627, List.forall_mem_cons.2 ⟨subd17_2_628, List.forall_mem_cons.2 ⟨subd17_2_629, List.forall_mem_cons.2 ⟨subd17_2_630, List.forall_mem_cons.2 ⟨subd17_2_631, List.forall_mem_cons.2 ⟨subd17_2_632, List.forall_mem_cons.2 ⟨subd17_2_633, List.forall_mem_cons.2 ⟨subd17_2_634, List.forall_mem_cons.2 ⟨subd17_2_635, List.forall_mem_cons.2 ⟨subd17_2_636, List.forall_mem_cons.2 ⟨subd17_2_637, List.forall_mem_cons.2 ⟨subd17_2_638, List.forall_mem_cons.2 ⟨subd17_2_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_2_640 : subd17_2 [2, -2, -4] = true := by decide +kernel
theorem subd17_2_641 : subd17_2 [2, -2, -3] = true := by decide +kernel
theorem subd17_2_642 : subd17_2 [2, -2, -2] = true := by decide +kernel
theorem subd17_2_643 : subd17_2 [2, -2, -1] = true := by decide +kernel
theorem subd17_2_644 : subd17_2 [2, -2, 0] = true := by decide +kernel
theorem subd17_2_645 : subd17_2 [2, -2, 1] = true := by decide +kernel
theorem subd17_2_646 : subd17_2 [2, -2, 2] = true := by decide +kernel
theorem subd17_2_647 : subd17_2 [2, -2, 3] = true := by decide +kernel
theorem subd17_2_648 : subd17_2 [2, -2, 4] = true := by decide +kernel
theorem subd17_2_649 : subd17_2 [2, -2, 5] = true := by decide +kernel
theorem subd17_2_650 : subd17_2 [2, -2, 6] = true := by decide +kernel
theorem subd17_2_651 : subd17_2 [2, -1, -8] = true := by decide +kernel
theorem subd17_2_652 : subd17_2 [2, -1, -7] = true := by decide +kernel
theorem subd17_2_653 : subd17_2 [2, -1, -6] = true := by decide +kernel
theorem subd17_2_654 : subd17_2 [2, -1, -5] = true := by decide +kernel
theorem subd17_2_655 : subd17_2 [2, -1, -4] = true := by decide +kernel
theorem subd17_2_656 : subd17_2 [2, -1, -3] = true := by decide +kernel
theorem subd17_2_657 : subd17_2 [2, -1, -2] = true := by decide +kernel
theorem subd17_2_658 : subd17_2 [2, -1, -1] = true := by decide +kernel
theorem subd17_2_659 : subd17_2 [2, -1, 0] = true := by decide +kernel
theorem subd17_2_660 : subd17_2 [2, -1, 1] = true := by decide +kernel
theorem subd17_2_661 : subd17_2 [2, -1, 2] = true := by decide +kernel
theorem subd17_2_662 : subd17_2 [2, -1, 3] = true := by decide +kernel
theorem subd17_2_663 : subd17_2 [2, -1, 4] = true := by decide +kernel
theorem subd17_2_664 : subd17_2 [2, -1, 5] = true := by decide +kernel
theorem subd17_2_665 : subd17_2 [2, -1, 6] = true := by decide +kernel
theorem subd17_2_666 : subd17_2 [2, -1, 7] = true := by decide +kernel
theorem subd17_2_667 : subd17_2 [2, 0, -8] = true := by decide +kernel
theorem subd17_2_668 : subd17_2 [2, 0, -7] = true := by decide +kernel
theorem subd17_2_669 : subd17_2 [2, 0, -6] = true := by decide +kernel
theorem subd17_2_670 : subd17_2 [2, 0, -5] = true := by decide +kernel
theorem subd17_2_671 : subd17_2 [2, 0, -4] = true := by decide +kernel
theorem sbd17_2_20 : ∀ q ∈ blkd17_2_20, subd17_2 q = true := by
  unfold blkd17_2_20
  exact List.forall_mem_cons.2 ⟨subd17_2_640, List.forall_mem_cons.2 ⟨subd17_2_641, List.forall_mem_cons.2 ⟨subd17_2_642, List.forall_mem_cons.2 ⟨subd17_2_643, List.forall_mem_cons.2 ⟨subd17_2_644, List.forall_mem_cons.2 ⟨subd17_2_645, List.forall_mem_cons.2 ⟨subd17_2_646, List.forall_mem_cons.2 ⟨subd17_2_647, List.forall_mem_cons.2 ⟨subd17_2_648, List.forall_mem_cons.2 ⟨subd17_2_649, List.forall_mem_cons.2 ⟨subd17_2_650, List.forall_mem_cons.2 ⟨subd17_2_651, List.forall_mem_cons.2 ⟨subd17_2_652, List.forall_mem_cons.2 ⟨subd17_2_653, List.forall_mem_cons.2 ⟨subd17_2_654, List.forall_mem_cons.2 ⟨subd17_2_655, List.forall_mem_cons.2 ⟨subd17_2_656, List.forall_mem_cons.2 ⟨subd17_2_657, List.forall_mem_cons.2 ⟨subd17_2_658, List.forall_mem_cons.2 ⟨subd17_2_659, List.forall_mem_cons.2 ⟨subd17_2_660, List.forall_mem_cons.2 ⟨subd17_2_661, List.forall_mem_cons.2 ⟨subd17_2_662, List.forall_mem_cons.2 ⟨subd17_2_663, List.forall_mem_cons.2 ⟨subd17_2_664, List.forall_mem_cons.2 ⟨subd17_2_665, List.forall_mem_cons.2 ⟨subd17_2_666, List.forall_mem_cons.2 ⟨subd17_2_667, List.forall_mem_cons.2 ⟨subd17_2_668, List.forall_mem_cons.2 ⟨subd17_2_669, List.forall_mem_cons.2 ⟨subd17_2_670, List.forall_mem_cons.2 ⟨subd17_2_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_2_672 : subd17_2 [2, 0, -3] = true := by decide +kernel
theorem subd17_2_673 : subd17_2 [2, 0, -2] = true := by decide +kernel
theorem subd17_2_674 : subd17_2 [2, 0, -1] = true := by decide +kernel
theorem subd17_2_675 : subd17_2 [2, 0, 0] = true := by decide +kernel
theorem subd17_2_676 : subd17_2 [2, 0, 1] = true := by decide +kernel
theorem subd17_2_677 : subd17_2 [2, 0, 2] = true := by decide +kernel
theorem subd17_2_678 : subd17_2 [2, 0, 3] = true := by decide +kernel
theorem subd17_2_679 : subd17_2 [2, 0, 4] = true := by decide +kernel
theorem subd17_2_680 : subd17_2 [2, 0, 5] = true := by decide +kernel
theorem subd17_2_681 : subd17_2 [2, 0, 6] = true := by decide +kernel
theorem subd17_2_682 : subd17_2 [2, 0, 7] = true := by decide +kernel
theorem subd17_2_683 : subd17_2 [2, 0, 8] = true := by decide +kernel
theorem subd17_2_684 : subd17_2 [2, 1, -8] = true := by decide +kernel
theorem subd17_2_685 : subd17_2 [2, 1, -7] = true := by decide +kernel
theorem subd17_2_686 : subd17_2 [2, 1, -6] = true := by decide +kernel
theorem subd17_2_687 : subd17_2 [2, 1, -5] = true := by decide +kernel
theorem subd17_2_688 : subd17_2 [2, 1, -4] = true := by decide +kernel
theorem subd17_2_689 : subd17_2 [2, 1, -3] = true := by decide +kernel
theorem subd17_2_690 : subd17_2 [2, 1, -2] = true := by decide +kernel
theorem subd17_2_691 : subd17_2 [2, 1, -1] = true := by decide +kernel
theorem subd17_2_692 : subd17_2 [2, 1, 0] = true := by decide +kernel
theorem subd17_2_693 : subd17_2 [2, 1, 1] = true := by decide +kernel
theorem subd17_2_694 : subd17_2 [2, 1, 2] = true := by decide +kernel
theorem subd17_2_695 : subd17_2 [2, 1, 3] = true := by decide +kernel
theorem subd17_2_696 : subd17_2 [2, 1, 4] = true := by decide +kernel
theorem subd17_2_697 : subd17_2 [2, 1, 5] = true := by decide +kernel
theorem subd17_2_698 : subd17_2 [2, 1, 6] = true := by decide +kernel
theorem subd17_2_699 : subd17_2 [2, 1, 7] = true := by decide +kernel
theorem subd17_2_700 : subd17_2 [2, 1, 8] = true := by decide +kernel
theorem subd17_2_701 : subd17_2 [2, 2, -7] = true := by decide +kernel
theorem subd17_2_702 : subd17_2 [2, 2, -6] = true := by decide +kernel
theorem subd17_2_703 : subd17_2 [2, 2, -5] = true := by decide +kernel
theorem sbd17_2_21 : ∀ q ∈ blkd17_2_21, subd17_2 q = true := by
  unfold blkd17_2_21
  exact List.forall_mem_cons.2 ⟨subd17_2_672, List.forall_mem_cons.2 ⟨subd17_2_673, List.forall_mem_cons.2 ⟨subd17_2_674, List.forall_mem_cons.2 ⟨subd17_2_675, List.forall_mem_cons.2 ⟨subd17_2_676, List.forall_mem_cons.2 ⟨subd17_2_677, List.forall_mem_cons.2 ⟨subd17_2_678, List.forall_mem_cons.2 ⟨subd17_2_679, List.forall_mem_cons.2 ⟨subd17_2_680, List.forall_mem_cons.2 ⟨subd17_2_681, List.forall_mem_cons.2 ⟨subd17_2_682, List.forall_mem_cons.2 ⟨subd17_2_683, List.forall_mem_cons.2 ⟨subd17_2_684, List.forall_mem_cons.2 ⟨subd17_2_685, List.forall_mem_cons.2 ⟨subd17_2_686, List.forall_mem_cons.2 ⟨subd17_2_687, List.forall_mem_cons.2 ⟨subd17_2_688, List.forall_mem_cons.2 ⟨subd17_2_689, List.forall_mem_cons.2 ⟨subd17_2_690, List.forall_mem_cons.2 ⟨subd17_2_691, List.forall_mem_cons.2 ⟨subd17_2_692, List.forall_mem_cons.2 ⟨subd17_2_693, List.forall_mem_cons.2 ⟨subd17_2_694, List.forall_mem_cons.2 ⟨subd17_2_695, List.forall_mem_cons.2 ⟨subd17_2_696, List.forall_mem_cons.2 ⟨subd17_2_697, List.forall_mem_cons.2 ⟨subd17_2_698, List.forall_mem_cons.2 ⟨subd17_2_699, List.forall_mem_cons.2 ⟨subd17_2_700, List.forall_mem_cons.2 ⟨subd17_2_701, List.forall_mem_cons.2 ⟨subd17_2_702, List.forall_mem_cons.2 ⟨subd17_2_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_2_704 : subd17_2 [2, 2, -4] = true := by decide +kernel
theorem subd17_2_705 : subd17_2 [2, 2, -3] = true := by decide +kernel
theorem subd17_2_706 : subd17_2 [2, 2, -2] = true := by decide +kernel
theorem subd17_2_707 : subd17_2 [2, 2, -1] = true := by decide +kernel
theorem subd17_2_708 : subd17_2 [2, 2, 0] = true := by decide +kernel
theorem subd17_2_709 : subd17_2 [2, 2, 1] = true := by decide +kernel
theorem subd17_2_710 : subd17_2 [2, 2, 2] = true := by decide +kernel
theorem subd17_2_711 : subd17_2 [2, 2, 3] = true := by decide +kernel
theorem subd17_2_712 : subd17_2 [2, 2, 4] = true := by decide +kernel
theorem subd17_2_713 : subd17_2 [2, 2, 5] = true := by decide +kernel
theorem subd17_2_714 : subd17_2 [2, 2, 6] = true := by decide +kernel
theorem subd17_2_715 : subd17_2 [2, 2, 7] = true := by decide +kernel
theorem subd17_2_716 : subd17_2 [2, 2, 8] = true := by decide +kernel
theorem subd17_2_717 : subd17_2 [2, 3, -6] = true := by decide +kernel
theorem subd17_2_718 : subd17_2 [2, 3, -5] = true := by decide +kernel
theorem subd17_2_719 : subd17_2 [2, 3, -4] = true := by decide +kernel
theorem subd17_2_720 : subd17_2 [2, 3, -3] = true := by decide +kernel
theorem subd17_2_721 : subd17_2 [2, 3, -2] = true := by decide +kernel
theorem subd17_2_722 : subd17_2 [2, 3, -1] = true := by decide +kernel
theorem subd17_2_723 : subd17_2 [2, 3, 0] = true := by decide +kernel
theorem subd17_2_724 : subd17_2 [2, 3, 1] = true := by decide +kernel
theorem subd17_2_725 : subd17_2 [2, 3, 2] = true := by decide +kernel
theorem subd17_2_726 : subd17_2 [2, 3, 3] = true := by decide +kernel
theorem subd17_2_727 : subd17_2 [2, 3, 4] = true := by decide +kernel
theorem subd17_2_728 : subd17_2 [2, 3, 5] = true := by decide +kernel
theorem subd17_2_729 : subd17_2 [2, 3, 6] = true := by decide +kernel
theorem subd17_2_730 : subd17_2 [2, 3, 7] = true := by decide +kernel
theorem subd17_2_731 : subd17_2 [2, 3, 8] = true := by decide +kernel
theorem subd17_2_732 : subd17_2 [2, 4, -5] = true := by decide +kernel
theorem subd17_2_733 : subd17_2 [2, 4, -4] = true := by decide +kernel
theorem subd17_2_734 : subd17_2 [2, 4, -3] = true := by decide +kernel
theorem subd17_2_735 : subd17_2 [2, 4, -2] = true := by decide +kernel
theorem sbd17_2_22 : ∀ q ∈ blkd17_2_22, subd17_2 q = true := by
  unfold blkd17_2_22
  exact List.forall_mem_cons.2 ⟨subd17_2_704, List.forall_mem_cons.2 ⟨subd17_2_705, List.forall_mem_cons.2 ⟨subd17_2_706, List.forall_mem_cons.2 ⟨subd17_2_707, List.forall_mem_cons.2 ⟨subd17_2_708, List.forall_mem_cons.2 ⟨subd17_2_709, List.forall_mem_cons.2 ⟨subd17_2_710, List.forall_mem_cons.2 ⟨subd17_2_711, List.forall_mem_cons.2 ⟨subd17_2_712, List.forall_mem_cons.2 ⟨subd17_2_713, List.forall_mem_cons.2 ⟨subd17_2_714, List.forall_mem_cons.2 ⟨subd17_2_715, List.forall_mem_cons.2 ⟨subd17_2_716, List.forall_mem_cons.2 ⟨subd17_2_717, List.forall_mem_cons.2 ⟨subd17_2_718, List.forall_mem_cons.2 ⟨subd17_2_719, List.forall_mem_cons.2 ⟨subd17_2_720, List.forall_mem_cons.2 ⟨subd17_2_721, List.forall_mem_cons.2 ⟨subd17_2_722, List.forall_mem_cons.2 ⟨subd17_2_723, List.forall_mem_cons.2 ⟨subd17_2_724, List.forall_mem_cons.2 ⟨subd17_2_725, List.forall_mem_cons.2 ⟨subd17_2_726, List.forall_mem_cons.2 ⟨subd17_2_727, List.forall_mem_cons.2 ⟨subd17_2_728, List.forall_mem_cons.2 ⟨subd17_2_729, List.forall_mem_cons.2 ⟨subd17_2_730, List.forall_mem_cons.2 ⟨subd17_2_731, List.forall_mem_cons.2 ⟨subd17_2_732, List.forall_mem_cons.2 ⟨subd17_2_733, List.forall_mem_cons.2 ⟨subd17_2_734, List.forall_mem_cons.2 ⟨subd17_2_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_2_736 : subd17_2 [2, 4, -1] = true := by decide +kernel
theorem subd17_2_737 : subd17_2 [2, 4, 0] = true := by decide +kernel
theorem subd17_2_738 : subd17_2 [2, 4, 1] = true := by decide +kernel
theorem subd17_2_739 : subd17_2 [2, 4, 2] = true := by decide +kernel
theorem subd17_2_740 : subd17_2 [2, 4, 3] = true := by decide +kernel
theorem subd17_2_741 : subd17_2 [2, 4, 4] = true := by decide +kernel
theorem subd17_2_742 : subd17_2 [2, 4, 5] = true := by decide +kernel
theorem subd17_2_743 : subd17_2 [2, 4, 6] = true := by decide +kernel
theorem subd17_2_744 : subd17_2 [2, 4, 7] = true := by decide +kernel
theorem subd17_2_745 : subd17_2 [2, 4, 8] = true := by decide +kernel
theorem subd17_2_746 : subd17_2 [2, 5] = true := by decide +kernel
theorem subd17_2_747 : subd17_2 [2, 6] = true := by decide +kernel
theorem subd17_2_748 : subd17_2 [3, -4] = true := by decide +kernel
theorem subd17_2_749 : subd17_2 [3, -3] = true := by decide +kernel
theorem subd17_2_750 : subd17_2 [3, -2] = true := by decide +kernel
theorem subd17_2_751 : subd17_2 [3, -1, -7] = true := by decide +kernel
theorem subd17_2_752 : subd17_2 [3, -1, -6] = true := by decide +kernel
theorem subd17_2_753 : subd17_2 [3, -1, -5] = true := by decide +kernel
theorem subd17_2_754 : subd17_2 [3, -1, -4] = true := by decide +kernel
theorem subd17_2_755 : subd17_2 [3, -1, -3] = true := by decide +kernel
theorem subd17_2_756 : subd17_2 [3, -1, -2] = true := by decide +kernel
theorem subd17_2_757 : subd17_2 [3, -1, -1] = true := by decide +kernel
theorem subd17_2_758 : subd17_2 [3, -1, 0] = true := by decide +kernel
theorem subd17_2_759 : subd17_2 [3, -1, 1] = true := by decide +kernel
theorem subd17_2_760 : subd17_2 [3, -1, 2] = true := by decide +kernel
theorem subd17_2_761 : subd17_2 [3, -1, 3] = true := by decide +kernel
theorem subd17_2_762 : subd17_2 [3, -1, 4] = true := by decide +kernel
theorem subd17_2_763 : subd17_2 [3, -1, 5] = true := by decide +kernel
theorem subd17_2_764 : subd17_2 [3, -1, 6] = true := by decide +kernel
theorem subd17_2_765 : subd17_2 [3, 0, -7] = true := by decide +kernel
theorem subd17_2_766 : subd17_2 [3, 0, -6] = true := by decide +kernel
theorem subd17_2_767 : subd17_2 [3, 0, -5] = true := by decide +kernel
theorem sbd17_2_23 : ∀ q ∈ blkd17_2_23, subd17_2 q = true := by
  unfold blkd17_2_23
  exact List.forall_mem_cons.2 ⟨subd17_2_736, List.forall_mem_cons.2 ⟨subd17_2_737, List.forall_mem_cons.2 ⟨subd17_2_738, List.forall_mem_cons.2 ⟨subd17_2_739, List.forall_mem_cons.2 ⟨subd17_2_740, List.forall_mem_cons.2 ⟨subd17_2_741, List.forall_mem_cons.2 ⟨subd17_2_742, List.forall_mem_cons.2 ⟨subd17_2_743, List.forall_mem_cons.2 ⟨subd17_2_744, List.forall_mem_cons.2 ⟨subd17_2_745, List.forall_mem_cons.2 ⟨subd17_2_746, List.forall_mem_cons.2 ⟨subd17_2_747, List.forall_mem_cons.2 ⟨subd17_2_748, List.forall_mem_cons.2 ⟨subd17_2_749, List.forall_mem_cons.2 ⟨subd17_2_750, List.forall_mem_cons.2 ⟨subd17_2_751, List.forall_mem_cons.2 ⟨subd17_2_752, List.forall_mem_cons.2 ⟨subd17_2_753, List.forall_mem_cons.2 ⟨subd17_2_754, List.forall_mem_cons.2 ⟨subd17_2_755, List.forall_mem_cons.2 ⟨subd17_2_756, List.forall_mem_cons.2 ⟨subd17_2_757, List.forall_mem_cons.2 ⟨subd17_2_758, List.forall_mem_cons.2 ⟨subd17_2_759, List.forall_mem_cons.2 ⟨subd17_2_760, List.forall_mem_cons.2 ⟨subd17_2_761, List.forall_mem_cons.2 ⟨subd17_2_762, List.forall_mem_cons.2 ⟨subd17_2_763, List.forall_mem_cons.2 ⟨subd17_2_764, List.forall_mem_cons.2 ⟨subd17_2_765, List.forall_mem_cons.2 ⟨subd17_2_766, List.forall_mem_cons.2 ⟨subd17_2_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_2_768 : subd17_2 [3, 0, -4] = true := by decide +kernel
theorem subd17_2_769 : subd17_2 [3, 0, -3] = true := by decide +kernel
theorem subd17_2_770 : subd17_2 [3, 0, -2] = true := by decide +kernel
theorem subd17_2_771 : subd17_2 [3, 0, -1] = true := by decide +kernel
theorem subd17_2_772 : subd17_2 [3, 0, 0] = true := by decide +kernel
theorem subd17_2_773 : subd17_2 [3, 0, 1] = true := by decide +kernel
theorem subd17_2_774 : subd17_2 [3, 0, 2] = true := by decide +kernel
theorem subd17_2_775 : subd17_2 [3, 0, 3] = true := by decide +kernel
theorem subd17_2_776 : subd17_2 [3, 0, 4] = true := by decide +kernel
theorem subd17_2_777 : subd17_2 [3, 0, 5] = true := by decide +kernel
theorem subd17_2_778 : subd17_2 [3, 0, 6] = true := by decide +kernel
theorem subd17_2_779 : subd17_2 [3, 0, 7] = true := by decide +kernel
theorem subd17_2_780 : subd17_2 [3, 1, -7] = true := by decide +kernel
theorem subd17_2_781 : subd17_2 [3, 1, -6] = true := by decide +kernel
theorem subd17_2_782 : subd17_2 [3, 1, -5] = true := by decide +kernel
theorem subd17_2_783 : subd17_2 [3, 1, -4] = true := by decide +kernel
theorem subd17_2_784 : subd17_2 [3, 1, -3] = true := by decide +kernel
theorem subd17_2_785 : subd17_2 [3, 1, -2] = true := by decide +kernel
theorem subd17_2_786 : subd17_2 [3, 1, -1] = true := by decide +kernel
theorem subd17_2_787 : subd17_2 [3, 1, 0] = true := by decide +kernel
theorem subd17_2_788 : subd17_2 [3, 1, 1] = true := by decide +kernel
theorem subd17_2_789 : subd17_2 [3, 1, 2] = true := by decide +kernel
theorem subd17_2_790 : subd17_2 [3, 1, 3] = true := by decide +kernel
theorem subd17_2_791 : subd17_2 [3, 1, 4] = true := by decide +kernel
theorem subd17_2_792 : subd17_2 [3, 1, 5] = true := by decide +kernel
theorem subd17_2_793 : subd17_2 [3, 1, 6] = true := by decide +kernel
theorem subd17_2_794 : subd17_2 [3, 1, 7] = true := by decide +kernel
theorem subd17_2_795 : subd17_2 [3, 2, -6] = true := by decide +kernel
theorem subd17_2_796 : subd17_2 [3, 2, -5] = true := by decide +kernel
theorem subd17_2_797 : subd17_2 [3, 2, -4] = true := by decide +kernel
theorem subd17_2_798 : subd17_2 [3, 2, -3] = true := by decide +kernel
theorem subd17_2_799 : subd17_2 [3, 2, -2] = true := by decide +kernel
theorem sbd17_2_24 : ∀ q ∈ blkd17_2_24, subd17_2 q = true := by
  unfold blkd17_2_24
  exact List.forall_mem_cons.2 ⟨subd17_2_768, List.forall_mem_cons.2 ⟨subd17_2_769, List.forall_mem_cons.2 ⟨subd17_2_770, List.forall_mem_cons.2 ⟨subd17_2_771, List.forall_mem_cons.2 ⟨subd17_2_772, List.forall_mem_cons.2 ⟨subd17_2_773, List.forall_mem_cons.2 ⟨subd17_2_774, List.forall_mem_cons.2 ⟨subd17_2_775, List.forall_mem_cons.2 ⟨subd17_2_776, List.forall_mem_cons.2 ⟨subd17_2_777, List.forall_mem_cons.2 ⟨subd17_2_778, List.forall_mem_cons.2 ⟨subd17_2_779, List.forall_mem_cons.2 ⟨subd17_2_780, List.forall_mem_cons.2 ⟨subd17_2_781, List.forall_mem_cons.2 ⟨subd17_2_782, List.forall_mem_cons.2 ⟨subd17_2_783, List.forall_mem_cons.2 ⟨subd17_2_784, List.forall_mem_cons.2 ⟨subd17_2_785, List.forall_mem_cons.2 ⟨subd17_2_786, List.forall_mem_cons.2 ⟨subd17_2_787, List.forall_mem_cons.2 ⟨subd17_2_788, List.forall_mem_cons.2 ⟨subd17_2_789, List.forall_mem_cons.2 ⟨subd17_2_790, List.forall_mem_cons.2 ⟨subd17_2_791, List.forall_mem_cons.2 ⟨subd17_2_792, List.forall_mem_cons.2 ⟨subd17_2_793, List.forall_mem_cons.2 ⟨subd17_2_794, List.forall_mem_cons.2 ⟨subd17_2_795, List.forall_mem_cons.2 ⟨subd17_2_796, List.forall_mem_cons.2 ⟨subd17_2_797, List.forall_mem_cons.2 ⟨subd17_2_798, List.forall_mem_cons.2 ⟨subd17_2_799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_2_800 : subd17_2 [3, 2, -1] = true := by decide +kernel
theorem subd17_2_801 : subd17_2 [3, 2, 0] = true := by decide +kernel
theorem subd17_2_802 : subd17_2 [3, 2, 1] = true := by decide +kernel
theorem subd17_2_803 : subd17_2 [3, 2, 2] = true := by decide +kernel
theorem subd17_2_804 : subd17_2 [3, 2, 3] = true := by decide +kernel
theorem subd17_2_805 : subd17_2 [3, 2, 4] = true := by decide +kernel
theorem subd17_2_806 : subd17_2 [3, 2, 5] = true := by decide +kernel
theorem subd17_2_807 : subd17_2 [3, 2, 6] = true := by decide +kernel
theorem subd17_2_808 : subd17_2 [3, 2, 7] = true := by decide +kernel
theorem subd17_2_809 : subd17_2 [3, 2, 8] = true := by decide +kernel
theorem subd17_2_810 : subd17_2 [3, 3, -6] = true := by decide +kernel
theorem subd17_2_811 : subd17_2 [3, 3, -5] = true := by decide +kernel
theorem subd17_2_812 : subd17_2 [3, 3, -4] = true := by decide +kernel
theorem subd17_2_813 : subd17_2 [3, 3, -3] = true := by decide +kernel
theorem subd17_2_814 : subd17_2 [3, 3, -2] = true := by decide +kernel
theorem subd17_2_815 : subd17_2 [3, 3, -1] = true := by decide +kernel
theorem subd17_2_816 : subd17_2 [3, 3, 0] = true := by decide +kernel
theorem subd17_2_817 : subd17_2 [3, 3, 1] = true := by decide +kernel
theorem subd17_2_818 : subd17_2 [3, 3, 2] = true := by decide +kernel
theorem subd17_2_819 : subd17_2 [3, 3, 3] = true := by decide +kernel
theorem subd17_2_820 : subd17_2 [3, 3, 4] = true := by decide +kernel
theorem subd17_2_821 : subd17_2 [3, 3, 5] = true := by decide +kernel
theorem subd17_2_822 : subd17_2 [3, 3, 6] = true := by decide +kernel
theorem subd17_2_823 : subd17_2 [3, 3, 7] = true := by decide +kernel
theorem subd17_2_824 : subd17_2 [3, 3, 8] = true := by decide +kernel
theorem subd17_2_825 : subd17_2 [3, 4] = true := by decide +kernel
theorem subd17_2_826 : subd17_2 [3, 5] = true := by decide +kernel
theorem subd17_2_827 : subd17_2 [3, 6] = true := by decide +kernel
theorem subd17_2_828 : subd17_2 [4, -3] = true := by decide +kernel
theorem subd17_2_829 : subd17_2 [4, -2] = true := by decide +kernel
theorem subd17_2_830 : subd17_2 [4, -1] = true := by decide +kernel
theorem subd17_2_831 : subd17_2 [4, 0] = true := by decide +kernel
theorem sbd17_2_25 : ∀ q ∈ blkd17_2_25, subd17_2 q = true := by
  unfold blkd17_2_25
  exact List.forall_mem_cons.2 ⟨subd17_2_800, List.forall_mem_cons.2 ⟨subd17_2_801, List.forall_mem_cons.2 ⟨subd17_2_802, List.forall_mem_cons.2 ⟨subd17_2_803, List.forall_mem_cons.2 ⟨subd17_2_804, List.forall_mem_cons.2 ⟨subd17_2_805, List.forall_mem_cons.2 ⟨subd17_2_806, List.forall_mem_cons.2 ⟨subd17_2_807, List.forall_mem_cons.2 ⟨subd17_2_808, List.forall_mem_cons.2 ⟨subd17_2_809, List.forall_mem_cons.2 ⟨subd17_2_810, List.forall_mem_cons.2 ⟨subd17_2_811, List.forall_mem_cons.2 ⟨subd17_2_812, List.forall_mem_cons.2 ⟨subd17_2_813, List.forall_mem_cons.2 ⟨subd17_2_814, List.forall_mem_cons.2 ⟨subd17_2_815, List.forall_mem_cons.2 ⟨subd17_2_816, List.forall_mem_cons.2 ⟨subd17_2_817, List.forall_mem_cons.2 ⟨subd17_2_818, List.forall_mem_cons.2 ⟨subd17_2_819, List.forall_mem_cons.2 ⟨subd17_2_820, List.forall_mem_cons.2 ⟨subd17_2_821, List.forall_mem_cons.2 ⟨subd17_2_822, List.forall_mem_cons.2 ⟨subd17_2_823, List.forall_mem_cons.2 ⟨subd17_2_824, List.forall_mem_cons.2 ⟨subd17_2_825, List.forall_mem_cons.2 ⟨subd17_2_826, List.forall_mem_cons.2 ⟨subd17_2_827, List.forall_mem_cons.2 ⟨subd17_2_828, List.forall_mem_cons.2 ⟨subd17_2_829, List.forall_mem_cons.2 ⟨subd17_2_830, List.forall_mem_cons.2 ⟨subd17_2_831, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_2_832 : subd17_2 [4, 1] = true := by decide +kernel
theorem subd17_2_833 : subd17_2 [4, 2] = true := by decide +kernel
theorem subd17_2_834 : subd17_2 [4, 3] = true := by decide +kernel
theorem subd17_2_835 : subd17_2 [4, 4] = true := by decide +kernel
theorem subd17_2_836 : subd17_2 [4, 5] = true := by decide +kernel
theorem subd17_2_837 : subd17_2 [5, -1] = true := by decide +kernel
theorem subd17_2_838 : subd17_2 [5, 0] = true := by decide +kernel
theorem subd17_2_839 : subd17_2 [5, 1] = true := by decide +kernel
theorem subd17_2_840 : subd17_2 [5, 2] = true := by decide +kernel
theorem subd17_2_841 : subd17_2 [5, 3] = true := by decide +kernel
theorem subd17_2_842 : subd17_2 [5, 4] = true := by decide +kernel
theorem sbd17_2_26 : ∀ q ∈ blkd17_2_26, subd17_2 q = true := by
  unfold blkd17_2_26
  exact List.forall_mem_cons.2 ⟨subd17_2_832, List.forall_mem_cons.2 ⟨subd17_2_833, List.forall_mem_cons.2 ⟨subd17_2_834, List.forall_mem_cons.2 ⟨subd17_2_835, List.forall_mem_cons.2 ⟨subd17_2_836, List.forall_mem_cons.2 ⟨subd17_2_837, List.forall_mem_cons.2 ⟨subd17_2_838, List.forall_mem_cons.2 ⟨subd17_2_839, List.forall_mem_cons.2 ⟨subd17_2_840, List.forall_mem_cons.2 ⟨subd17_2_841, List.forall_mem_cons.2 ⟨subd17_2_842, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
