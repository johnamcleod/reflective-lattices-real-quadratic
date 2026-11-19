import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd10_2_448 : subd10_2 [1, -3, 3] = true := by decide +kernel
theorem subd10_2_449 : subd10_2 [1, -3, 4] = true := by decide +kernel
theorem subd10_2_450 : subd10_2 [1, -3, 5] = true := by decide +kernel
theorem subd10_2_451 : subd10_2 [1, -3, 6] = true := by decide +kernel
theorem subd10_2_452 : subd10_2 [1, -3, 7] = true := by decide +kernel
theorem subd10_2_453 : subd10_2 [1, -3, 8] = true := by decide +kernel
theorem subd10_2_454 : subd10_2 [1, -2, -13] = true := by decide +kernel
theorem subd10_2_455 : subd10_2 [1, -2, -12] = true := by decide +kernel
theorem subd10_2_456 : subd10_2 [1, -2, -11] = true := by decide +kernel
theorem subd10_2_457 : subd10_2 [1, -2, -10] = true := by decide +kernel
theorem subd10_2_458 : subd10_2 [1, -2, -9] = true := by decide +kernel
theorem subd10_2_459 : subd10_2 [1, -2, -8] = true := by decide +kernel
theorem subd10_2_460 : subd10_2 [1, -2, -7] = true := by decide +kernel
theorem subd10_2_461 : subd10_2 [1, -2, -6] = true := by decide +kernel
theorem subd10_2_462 : subd10_2 [1, -2, -5] = true := by decide +kernel
theorem subd10_2_463 : subd10_2 [1, -2, -4] = true := by decide +kernel
theorem subd10_2_464 : subd10_2 [1, -2, -3] = true := by decide +kernel
theorem subd10_2_465 : subd10_2 [1, -2, -2] = true := by decide +kernel
theorem subd10_2_466 : subd10_2 [1, -2, -1] = true := by decide +kernel
theorem subd10_2_467 : subd10_2 [1, -2, 0] = true := by decide +kernel
theorem subd10_2_468 : subd10_2 [1, -2, 1] = true := by decide +kernel
theorem subd10_2_469 : subd10_2 [1, -2, 2] = true := by decide +kernel
theorem subd10_2_470 : subd10_2 [1, -2, 3] = true := by decide +kernel
theorem subd10_2_471 : subd10_2 [1, -2, 4] = true := by decide +kernel
theorem subd10_2_472 : subd10_2 [1, -2, 5] = true := by decide +kernel
theorem subd10_2_473 : subd10_2 [1, -2, 6] = true := by decide +kernel
theorem subd10_2_474 : subd10_2 [1, -2, 7] = true := by decide +kernel
theorem subd10_2_475 : subd10_2 [1, -2, 8] = true := by decide +kernel
theorem subd10_2_476 : subd10_2 [1, -2, 9] = true := by decide +kernel
theorem subd10_2_477 : subd10_2 [1, -2, 10] = true := by decide +kernel
theorem subd10_2_478 : subd10_2 [1, -2, 11] = true := by decide +kernel
theorem subd10_2_479 : subd10_2 [1, -2, 12] = true := by decide +kernel
theorem sbd10_2_14 : ∀ q ∈ blkd10_2_14, subd10_2 q = true := by
  unfold blkd10_2_14
  exact List.forall_mem_cons.2 ⟨subd10_2_448, List.forall_mem_cons.2 ⟨subd10_2_449, List.forall_mem_cons.2 ⟨subd10_2_450, List.forall_mem_cons.2 ⟨subd10_2_451, List.forall_mem_cons.2 ⟨subd10_2_452, List.forall_mem_cons.2 ⟨subd10_2_453, List.forall_mem_cons.2 ⟨subd10_2_454, List.forall_mem_cons.2 ⟨subd10_2_455, List.forall_mem_cons.2 ⟨subd10_2_456, List.forall_mem_cons.2 ⟨subd10_2_457, List.forall_mem_cons.2 ⟨subd10_2_458, List.forall_mem_cons.2 ⟨subd10_2_459, List.forall_mem_cons.2 ⟨subd10_2_460, List.forall_mem_cons.2 ⟨subd10_2_461, List.forall_mem_cons.2 ⟨subd10_2_462, List.forall_mem_cons.2 ⟨subd10_2_463, List.forall_mem_cons.2 ⟨subd10_2_464, List.forall_mem_cons.2 ⟨subd10_2_465, List.forall_mem_cons.2 ⟨subd10_2_466, List.forall_mem_cons.2 ⟨subd10_2_467, List.forall_mem_cons.2 ⟨subd10_2_468, List.forall_mem_cons.2 ⟨subd10_2_469, List.forall_mem_cons.2 ⟨subd10_2_470, List.forall_mem_cons.2 ⟨subd10_2_471, List.forall_mem_cons.2 ⟨subd10_2_472, List.forall_mem_cons.2 ⟨subd10_2_473, List.forall_mem_cons.2 ⟨subd10_2_474, List.forall_mem_cons.2 ⟨subd10_2_475, List.forall_mem_cons.2 ⟨subd10_2_476, List.forall_mem_cons.2 ⟨subd10_2_477, List.forall_mem_cons.2 ⟨subd10_2_478, List.forall_mem_cons.2 ⟨subd10_2_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_2_480 : subd10_2 [1, -1, -15] = true := by decide +kernel
theorem subd10_2_481 : subd10_2 [1, -1, -14] = true := by decide +kernel
theorem subd10_2_482 : subd10_2 [1, -1, -13] = true := by decide +kernel
theorem subd10_2_483 : subd10_2 [1, -1, -12] = true := by decide +kernel
theorem subd10_2_484 : subd10_2 [1, -1, -11] = true := by decide +kernel
theorem subd10_2_485 : subd10_2 [1, -1, -10] = true := by decide +kernel
theorem subd10_2_486 : subd10_2 [1, -1, -9] = true := by decide +kernel
theorem subd10_2_487 : subd10_2 [1, -1, -8] = true := by decide +kernel
theorem subd10_2_488 : subd10_2 [1, -1, -7] = true := by decide +kernel
theorem subd10_2_489 : subd10_2 [1, -1, -6] = true := by decide +kernel
theorem subd10_2_490 : subd10_2 [1, -1, -5] = true := by decide +kernel
theorem subd10_2_491 : subd10_2 [1, -1, -4] = true := by decide +kernel
theorem subd10_2_492 : subd10_2 [1, -1, -3] = true := by decide +kernel
theorem subd10_2_493 : subd10_2 [1, -1, -2] = true := by decide +kernel
theorem subd10_2_494 : subd10_2 [1, -1, -1] = true := by decide +kernel
theorem subd10_2_495 : subd10_2 [1, -1, 0] = true := by decide +kernel
theorem subd10_2_496 : subd10_2 [1, -1, 1] = true := by decide +kernel
theorem subd10_2_497 : subd10_2 [1, -1, 2] = true := by decide +kernel
theorem subd10_2_498 : subd10_2 [1, -1, 3] = true := by decide +kernel
theorem subd10_2_499 : subd10_2 [1, -1, 4] = true := by decide +kernel
theorem subd10_2_500 : subd10_2 [1, -1, 5] = true := by decide +kernel
theorem subd10_2_501 : subd10_2 [1, -1, 6] = true := by decide +kernel
theorem subd10_2_502 : subd10_2 [1, -1, 7] = true := by decide +kernel
theorem subd10_2_503 : subd10_2 [1, -1, 8] = true := by decide +kernel
theorem subd10_2_504 : subd10_2 [1, -1, 9] = true := by decide +kernel
theorem subd10_2_505 : subd10_2 [1, -1, 10] = true := by decide +kernel
theorem subd10_2_506 : subd10_2 [1, -1, 11] = true := by decide +kernel
theorem subd10_2_507 : subd10_2 [1, -1, 12] = true := by decide +kernel
theorem subd10_2_508 : subd10_2 [1, -1, 13] = true := by decide +kernel
theorem subd10_2_509 : subd10_2 [1, 0, -15] = true := by decide +kernel
theorem subd10_2_510 : subd10_2 [1, 0, -14] = true := by decide +kernel
theorem subd10_2_511 : subd10_2 [1, 0, -13] = true := by decide +kernel
theorem sbd10_2_15 : ∀ q ∈ blkd10_2_15, subd10_2 q = true := by
  unfold blkd10_2_15
  exact List.forall_mem_cons.2 ⟨subd10_2_480, List.forall_mem_cons.2 ⟨subd10_2_481, List.forall_mem_cons.2 ⟨subd10_2_482, List.forall_mem_cons.2 ⟨subd10_2_483, List.forall_mem_cons.2 ⟨subd10_2_484, List.forall_mem_cons.2 ⟨subd10_2_485, List.forall_mem_cons.2 ⟨subd10_2_486, List.forall_mem_cons.2 ⟨subd10_2_487, List.forall_mem_cons.2 ⟨subd10_2_488, List.forall_mem_cons.2 ⟨subd10_2_489, List.forall_mem_cons.2 ⟨subd10_2_490, List.forall_mem_cons.2 ⟨subd10_2_491, List.forall_mem_cons.2 ⟨subd10_2_492, List.forall_mem_cons.2 ⟨subd10_2_493, List.forall_mem_cons.2 ⟨subd10_2_494, List.forall_mem_cons.2 ⟨subd10_2_495, List.forall_mem_cons.2 ⟨subd10_2_496, List.forall_mem_cons.2 ⟨subd10_2_497, List.forall_mem_cons.2 ⟨subd10_2_498, List.forall_mem_cons.2 ⟨subd10_2_499, List.forall_mem_cons.2 ⟨subd10_2_500, List.forall_mem_cons.2 ⟨subd10_2_501, List.forall_mem_cons.2 ⟨subd10_2_502, List.forall_mem_cons.2 ⟨subd10_2_503, List.forall_mem_cons.2 ⟨subd10_2_504, List.forall_mem_cons.2 ⟨subd10_2_505, List.forall_mem_cons.2 ⟨subd10_2_506, List.forall_mem_cons.2 ⟨subd10_2_507, List.forall_mem_cons.2 ⟨subd10_2_508, List.forall_mem_cons.2 ⟨subd10_2_509, List.forall_mem_cons.2 ⟨subd10_2_510, List.forall_mem_cons.2 ⟨subd10_2_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_2_512 : subd10_2 [1, 0, -12] = true := by decide +kernel
theorem subd10_2_513 : subd10_2 [1, 0, -11] = true := by decide +kernel
theorem subd10_2_514 : subd10_2 [1, 0, -10] = true := by decide +kernel
theorem subd10_2_515 : subd10_2 [1, 0, -9] = true := by decide +kernel
theorem subd10_2_516 : subd10_2 [1, 0, -8] = true := by decide +kernel
theorem subd10_2_517 : subd10_2 [1, 0, -7] = true := by decide +kernel
theorem subd10_2_518 : subd10_2 [1, 0, -6] = true := by decide +kernel
theorem subd10_2_519 : subd10_2 [1, 0, -5] = true := by decide +kernel
theorem subd10_2_520 : subd10_2 [1, 0, -4] = true := by decide +kernel
theorem subd10_2_521 : subd10_2 [1, 0, -3] = true := by decide +kernel
theorem subd10_2_522 : subd10_2 [1, 0, -2] = true := by decide +kernel
theorem subd10_2_523 : subd10_2 [1, 0, -1] = true := by decide +kernel
theorem subd10_2_524 : subd10_2 [1, 0, 0] = true := by decide +kernel
theorem subd10_2_525 : subd10_2 [1, 0, 1] = true := by decide +kernel
theorem subd10_2_526 : subd10_2 [1, 0, 2] = true := by decide +kernel
theorem subd10_2_527 : subd10_2 [1, 0, 3] = true := by decide +kernel
theorem subd10_2_528 : subd10_2 [1, 0, 4] = true := by decide +kernel
theorem subd10_2_529 : subd10_2 [1, 0, 5] = true := by decide +kernel
theorem subd10_2_530 : subd10_2 [1, 0, 6] = true := by decide +kernel
theorem subd10_2_531 : subd10_2 [1, 0, 7] = true := by decide +kernel
theorem subd10_2_532 : subd10_2 [1, 0, 8] = true := by decide +kernel
theorem subd10_2_533 : subd10_2 [1, 0, 9] = true := by decide +kernel
theorem subd10_2_534 : subd10_2 [1, 0, 10] = true := by decide +kernel
theorem subd10_2_535 : subd10_2 [1, 0, 11] = true := by decide +kernel
theorem subd10_2_536 : subd10_2 [1, 0, 12] = true := by decide +kernel
theorem subd10_2_537 : subd10_2 [1, 0, 13] = true := by decide +kernel
theorem subd10_2_538 : subd10_2 [1, 1, -14] = true := by decide +kernel
theorem subd10_2_539 : subd10_2 [1, 1, -13] = true := by decide +kernel
theorem subd10_2_540 : subd10_2 [1, 1, -12] = true := by decide +kernel
theorem subd10_2_541 : subd10_2 [1, 1, -11] = true := by decide +kernel
theorem subd10_2_542 : subd10_2 [1, 1, -10] = true := by decide +kernel
theorem subd10_2_543 : subd10_2 [1, 1, -9] = true := by decide +kernel
theorem sbd10_2_16 : ∀ q ∈ blkd10_2_16, subd10_2 q = true := by
  unfold blkd10_2_16
  exact List.forall_mem_cons.2 ⟨subd10_2_512, List.forall_mem_cons.2 ⟨subd10_2_513, List.forall_mem_cons.2 ⟨subd10_2_514, List.forall_mem_cons.2 ⟨subd10_2_515, List.forall_mem_cons.2 ⟨subd10_2_516, List.forall_mem_cons.2 ⟨subd10_2_517, List.forall_mem_cons.2 ⟨subd10_2_518, List.forall_mem_cons.2 ⟨subd10_2_519, List.forall_mem_cons.2 ⟨subd10_2_520, List.forall_mem_cons.2 ⟨subd10_2_521, List.forall_mem_cons.2 ⟨subd10_2_522, List.forall_mem_cons.2 ⟨subd10_2_523, List.forall_mem_cons.2 ⟨subd10_2_524, List.forall_mem_cons.2 ⟨subd10_2_525, List.forall_mem_cons.2 ⟨subd10_2_526, List.forall_mem_cons.2 ⟨subd10_2_527, List.forall_mem_cons.2 ⟨subd10_2_528, List.forall_mem_cons.2 ⟨subd10_2_529, List.forall_mem_cons.2 ⟨subd10_2_530, List.forall_mem_cons.2 ⟨subd10_2_531, List.forall_mem_cons.2 ⟨subd10_2_532, List.forall_mem_cons.2 ⟨subd10_2_533, List.forall_mem_cons.2 ⟨subd10_2_534, List.forall_mem_cons.2 ⟨subd10_2_535, List.forall_mem_cons.2 ⟨subd10_2_536, List.forall_mem_cons.2 ⟨subd10_2_537, List.forall_mem_cons.2 ⟨subd10_2_538, List.forall_mem_cons.2 ⟨subd10_2_539, List.forall_mem_cons.2 ⟨subd10_2_540, List.forall_mem_cons.2 ⟨subd10_2_541, List.forall_mem_cons.2 ⟨subd10_2_542, List.forall_mem_cons.2 ⟨subd10_2_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_2_544 : subd10_2 [1, 1, -8] = true := by decide +kernel
theorem subd10_2_545 : subd10_2 [1, 1, -7] = true := by decide +kernel
theorem subd10_2_546 : subd10_2 [1, 1, -6] = true := by decide +kernel
theorem subd10_2_547 : subd10_2 [1, 1, -5] = true := by decide +kernel
theorem subd10_2_548 : subd10_2 [1, 1, -4] = true := by decide +kernel
theorem subd10_2_549 : subd10_2 [1, 1, -3] = true := by decide +kernel
theorem subd10_2_550 : subd10_2 [1, 1, -2] = true := by decide +kernel
theorem subd10_2_551 : subd10_2 [1, 1, -1] = true := by decide +kernel
theorem subd10_2_552 : subd10_2 [1, 1, 0] = true := by decide +kernel
theorem subd10_2_553 : subd10_2 [1, 1, 1] = true := by decide +kernel
theorem subd10_2_554 : subd10_2 [1, 1, 2] = true := by decide +kernel
theorem subd10_2_555 : subd10_2 [1, 1, 3] = true := by decide +kernel
theorem subd10_2_556 : subd10_2 [1, 1, 4] = true := by decide +kernel
theorem subd10_2_557 : subd10_2 [1, 1, 5] = true := by decide +kernel
theorem subd10_2_558 : subd10_2 [1, 1, 6] = true := by decide +kernel
theorem subd10_2_559 : subd10_2 [1, 1, 7] = true := by decide +kernel
theorem subd10_2_560 : subd10_2 [1, 1, 8] = true := by decide +kernel
theorem subd10_2_561 : subd10_2 [1, 1, 9] = true := by decide +kernel
theorem subd10_2_562 : subd10_2 [1, 1, 10] = true := by decide +kernel
theorem subd10_2_563 : subd10_2 [1, 1, 11] = true := by decide +kernel
theorem subd10_2_564 : subd10_2 [1, 1, 12] = true := by decide +kernel
theorem subd10_2_565 : subd10_2 [1, 2, -11] = true := by decide +kernel
theorem subd10_2_566 : subd10_2 [1, 2, -10] = true := by decide +kernel
theorem subd10_2_567 : subd10_2 [1, 2, -9] = true := by decide +kernel
theorem subd10_2_568 : subd10_2 [1, 2, -8] = true := by decide +kernel
theorem subd10_2_569 : subd10_2 [1, 2, -7] = true := by decide +kernel
theorem subd10_2_570 : subd10_2 [1, 2, -6] = true := by decide +kernel
theorem subd10_2_571 : subd10_2 [1, 2, -5] = true := by decide +kernel
theorem subd10_2_572 : subd10_2 [1, 2, -4] = true := by decide +kernel
theorem subd10_2_573 : subd10_2 [1, 2, -3] = true := by decide +kernel
theorem subd10_2_574 : subd10_2 [1, 2, -2] = true := by decide +kernel
theorem subd10_2_575 : subd10_2 [1, 2, -1] = true := by decide +kernel
theorem sbd10_2_17 : ∀ q ∈ blkd10_2_17, subd10_2 q = true := by
  unfold blkd10_2_17
  exact List.forall_mem_cons.2 ⟨subd10_2_544, List.forall_mem_cons.2 ⟨subd10_2_545, List.forall_mem_cons.2 ⟨subd10_2_546, List.forall_mem_cons.2 ⟨subd10_2_547, List.forall_mem_cons.2 ⟨subd10_2_548, List.forall_mem_cons.2 ⟨subd10_2_549, List.forall_mem_cons.2 ⟨subd10_2_550, List.forall_mem_cons.2 ⟨subd10_2_551, List.forall_mem_cons.2 ⟨subd10_2_552, List.forall_mem_cons.2 ⟨subd10_2_553, List.forall_mem_cons.2 ⟨subd10_2_554, List.forall_mem_cons.2 ⟨subd10_2_555, List.forall_mem_cons.2 ⟨subd10_2_556, List.forall_mem_cons.2 ⟨subd10_2_557, List.forall_mem_cons.2 ⟨subd10_2_558, List.forall_mem_cons.2 ⟨subd10_2_559, List.forall_mem_cons.2 ⟨subd10_2_560, List.forall_mem_cons.2 ⟨subd10_2_561, List.forall_mem_cons.2 ⟨subd10_2_562, List.forall_mem_cons.2 ⟨subd10_2_563, List.forall_mem_cons.2 ⟨subd10_2_564, List.forall_mem_cons.2 ⟨subd10_2_565, List.forall_mem_cons.2 ⟨subd10_2_566, List.forall_mem_cons.2 ⟨subd10_2_567, List.forall_mem_cons.2 ⟨subd10_2_568, List.forall_mem_cons.2 ⟨subd10_2_569, List.forall_mem_cons.2 ⟨subd10_2_570, List.forall_mem_cons.2 ⟨subd10_2_571, List.forall_mem_cons.2 ⟨subd10_2_572, List.forall_mem_cons.2 ⟨subd10_2_573, List.forall_mem_cons.2 ⟨subd10_2_574, List.forall_mem_cons.2 ⟨subd10_2_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_2_576 : subd10_2 [1, 2, 0] = true := by decide +kernel
theorem subd10_2_577 : subd10_2 [1, 2, 1] = true := by decide +kernel
theorem subd10_2_578 : subd10_2 [1, 2, 2] = true := by decide +kernel
theorem subd10_2_579 : subd10_2 [1, 2, 3] = true := by decide +kernel
theorem subd10_2_580 : subd10_2 [1, 2, 4] = true := by decide +kernel
theorem subd10_2_581 : subd10_2 [1, 2, 5] = true := by decide +kernel
theorem subd10_2_582 : subd10_2 [1, 2, 6] = true := by decide +kernel
theorem subd10_2_583 : subd10_2 [1, 2, 7] = true := by decide +kernel
theorem subd10_2_584 : subd10_2 [1, 2, 8] = true := by decide +kernel
theorem subd10_2_585 : subd10_2 [1, 2, 9] = true := by decide +kernel
theorem subd10_2_586 : subd10_2 [2, -4] = true := by decide +kernel
theorem subd10_2_587 : subd10_2 [2, -3, -8] = true := by decide +kernel
theorem subd10_2_588 : subd10_2 [2, -3, -7] = true := by decide +kernel
theorem subd10_2_589 : subd10_2 [2, -3, -6] = true := by decide +kernel
theorem subd10_2_590 : subd10_2 [2, -3, -5] = true := by decide +kernel
theorem subd10_2_591 : subd10_2 [2, -3, -4] = true := by decide +kernel
theorem subd10_2_592 : subd10_2 [2, -3, -3] = true := by decide +kernel
theorem subd10_2_593 : subd10_2 [2, -3, -2] = true := by decide +kernel
theorem subd10_2_594 : subd10_2 [2, -3, -1] = true := by decide +kernel
theorem subd10_2_595 : subd10_2 [2, -3, 0] = true := by decide +kernel
theorem subd10_2_596 : subd10_2 [2, -3, 1] = true := by decide +kernel
theorem subd10_2_597 : subd10_2 [2, -3, 2] = true := by decide +kernel
theorem subd10_2_598 : subd10_2 [2, -3, 3] = true := by decide +kernel
theorem subd10_2_599 : subd10_2 [2, -3, 4] = true := by decide +kernel
theorem subd10_2_600 : subd10_2 [2, -3, 5] = true := by decide +kernel
theorem subd10_2_601 : subd10_2 [2, -3, 6] = true := by decide +kernel
theorem subd10_2_602 : subd10_2 [2, -2, -12] = true := by decide +kernel
theorem subd10_2_603 : subd10_2 [2, -2, -11] = true := by decide +kernel
theorem subd10_2_604 : subd10_2 [2, -2, -10] = true := by decide +kernel
theorem subd10_2_605 : subd10_2 [2, -2, -9] = true := by decide +kernel
theorem subd10_2_606 : subd10_2 [2, -2, -8] = true := by decide +kernel
theorem subd10_2_607 : subd10_2 [2, -2, -7] = true := by decide +kernel
theorem sbd10_2_18 : ∀ q ∈ blkd10_2_18, subd10_2 q = true := by
  unfold blkd10_2_18
  exact List.forall_mem_cons.2 ⟨subd10_2_576, List.forall_mem_cons.2 ⟨subd10_2_577, List.forall_mem_cons.2 ⟨subd10_2_578, List.forall_mem_cons.2 ⟨subd10_2_579, List.forall_mem_cons.2 ⟨subd10_2_580, List.forall_mem_cons.2 ⟨subd10_2_581, List.forall_mem_cons.2 ⟨subd10_2_582, List.forall_mem_cons.2 ⟨subd10_2_583, List.forall_mem_cons.2 ⟨subd10_2_584, List.forall_mem_cons.2 ⟨subd10_2_585, List.forall_mem_cons.2 ⟨subd10_2_586, List.forall_mem_cons.2 ⟨subd10_2_587, List.forall_mem_cons.2 ⟨subd10_2_588, List.forall_mem_cons.2 ⟨subd10_2_589, List.forall_mem_cons.2 ⟨subd10_2_590, List.forall_mem_cons.2 ⟨subd10_2_591, List.forall_mem_cons.2 ⟨subd10_2_592, List.forall_mem_cons.2 ⟨subd10_2_593, List.forall_mem_cons.2 ⟨subd10_2_594, List.forall_mem_cons.2 ⟨subd10_2_595, List.forall_mem_cons.2 ⟨subd10_2_596, List.forall_mem_cons.2 ⟨subd10_2_597, List.forall_mem_cons.2 ⟨subd10_2_598, List.forall_mem_cons.2 ⟨subd10_2_599, List.forall_mem_cons.2 ⟨subd10_2_600, List.forall_mem_cons.2 ⟨subd10_2_601, List.forall_mem_cons.2 ⟨subd10_2_602, List.forall_mem_cons.2 ⟨subd10_2_603, List.forall_mem_cons.2 ⟨subd10_2_604, List.forall_mem_cons.2 ⟨subd10_2_605, List.forall_mem_cons.2 ⟨subd10_2_606, List.forall_mem_cons.2 ⟨subd10_2_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_2_608 : subd10_2 [2, -2, -6] = true := by decide +kernel
theorem subd10_2_609 : subd10_2 [2, -2, -5] = true := by decide +kernel
theorem subd10_2_610 : subd10_2 [2, -2, -4] = true := by decide +kernel
theorem subd10_2_611 : subd10_2 [2, -2, -3] = true := by decide +kernel
theorem subd10_2_612 : subd10_2 [2, -2, -2] = true := by decide +kernel
theorem subd10_2_613 : subd10_2 [2, -2, -1] = true := by decide +kernel
theorem subd10_2_614 : subd10_2 [2, -2, 0] = true := by decide +kernel
theorem subd10_2_615 : subd10_2 [2, -2, 1] = true := by decide +kernel
theorem subd10_2_616 : subd10_2 [2, -2, 2] = true := by decide +kernel
theorem subd10_2_617 : subd10_2 [2, -2, 3] = true := by decide +kernel
theorem subd10_2_618 : subd10_2 [2, -2, 4] = true := by decide +kernel
theorem subd10_2_619 : subd10_2 [2, -2, 5] = true := by decide +kernel
theorem subd10_2_620 : subd10_2 [2, -2, 6] = true := by decide +kernel
theorem subd10_2_621 : subd10_2 [2, -2, 7] = true := by decide +kernel
theorem subd10_2_622 : subd10_2 [2, -2, 8] = true := by decide +kernel
theorem subd10_2_623 : subd10_2 [2, -2, 9] = true := by decide +kernel
theorem subd10_2_624 : subd10_2 [2, -1, -13] = true := by decide +kernel
theorem subd10_2_625 : subd10_2 [2, -1, -12] = true := by decide +kernel
theorem subd10_2_626 : subd10_2 [2, -1, -11] = true := by decide +kernel
theorem subd10_2_627 : subd10_2 [2, -1, -10] = true := by decide +kernel
theorem subd10_2_628 : subd10_2 [2, -1, -9] = true := by decide +kernel
theorem subd10_2_629 : subd10_2 [2, -1, -8] = true := by decide +kernel
theorem subd10_2_630 : subd10_2 [2, -1, -7] = true := by decide +kernel
theorem subd10_2_631 : subd10_2 [2, -1, -6] = true := by decide +kernel
theorem subd10_2_632 : subd10_2 [2, -1, -5] = true := by decide +kernel
theorem subd10_2_633 : subd10_2 [2, -1, -4] = true := by decide +kernel
theorem subd10_2_634 : subd10_2 [2, -1, -3] = true := by decide +kernel
theorem subd10_2_635 : subd10_2 [2, -1, -2] = true := by decide +kernel
theorem subd10_2_636 : subd10_2 [2, -1, -1] = true := by decide +kernel
theorem subd10_2_637 : subd10_2 [2, -1, 0] = true := by decide +kernel
theorem subd10_2_638 : subd10_2 [2, -1, 1] = true := by decide +kernel
theorem subd10_2_639 : subd10_2 [2, -1, 2] = true := by decide +kernel
theorem sbd10_2_19 : ∀ q ∈ blkd10_2_19, subd10_2 q = true := by
  unfold blkd10_2_19
  exact List.forall_mem_cons.2 ⟨subd10_2_608, List.forall_mem_cons.2 ⟨subd10_2_609, List.forall_mem_cons.2 ⟨subd10_2_610, List.forall_mem_cons.2 ⟨subd10_2_611, List.forall_mem_cons.2 ⟨subd10_2_612, List.forall_mem_cons.2 ⟨subd10_2_613, List.forall_mem_cons.2 ⟨subd10_2_614, List.forall_mem_cons.2 ⟨subd10_2_615, List.forall_mem_cons.2 ⟨subd10_2_616, List.forall_mem_cons.2 ⟨subd10_2_617, List.forall_mem_cons.2 ⟨subd10_2_618, List.forall_mem_cons.2 ⟨subd10_2_619, List.forall_mem_cons.2 ⟨subd10_2_620, List.forall_mem_cons.2 ⟨subd10_2_621, List.forall_mem_cons.2 ⟨subd10_2_622, List.forall_mem_cons.2 ⟨subd10_2_623, List.forall_mem_cons.2 ⟨subd10_2_624, List.forall_mem_cons.2 ⟨subd10_2_625, List.forall_mem_cons.2 ⟨subd10_2_626, List.forall_mem_cons.2 ⟨subd10_2_627, List.forall_mem_cons.2 ⟨subd10_2_628, List.forall_mem_cons.2 ⟨subd10_2_629, List.forall_mem_cons.2 ⟨subd10_2_630, List.forall_mem_cons.2 ⟨subd10_2_631, List.forall_mem_cons.2 ⟨subd10_2_632, List.forall_mem_cons.2 ⟨subd10_2_633, List.forall_mem_cons.2 ⟨subd10_2_634, List.forall_mem_cons.2 ⟨subd10_2_635, List.forall_mem_cons.2 ⟨subd10_2_636, List.forall_mem_cons.2 ⟨subd10_2_637, List.forall_mem_cons.2 ⟨subd10_2_638, List.forall_mem_cons.2 ⟨subd10_2_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_2_640 : subd10_2 [2, -1, 3] = true := by decide +kernel
theorem subd10_2_641 : subd10_2 [2, -1, 4] = true := by decide +kernel
theorem subd10_2_642 : subd10_2 [2, -1, 5] = true := by decide +kernel
theorem subd10_2_643 : subd10_2 [2, -1, 6] = true := by decide +kernel
theorem subd10_2_644 : subd10_2 [2, -1, 7] = true := by decide +kernel
theorem subd10_2_645 : subd10_2 [2, -1, 8] = true := by decide +kernel
theorem subd10_2_646 : subd10_2 [2, -1, 9] = true := by decide +kernel
theorem subd10_2_647 : subd10_2 [2, -1, 10] = true := by decide +kernel
theorem subd10_2_648 : subd10_2 [2, 0, -13] = true := by decide +kernel
theorem subd10_2_649 : subd10_2 [2, 0, -12] = true := by decide +kernel
theorem subd10_2_650 : subd10_2 [2, 0, -11] = true := by decide +kernel
theorem subd10_2_651 : subd10_2 [2, 0, -10] = true := by decide +kernel
theorem subd10_2_652 : subd10_2 [2, 0, -9] = true := by decide +kernel
theorem subd10_2_653 : subd10_2 [2, 0, -8] = true := by decide +kernel
theorem subd10_2_654 : subd10_2 [2, 0, -7] = true := by decide +kernel
theorem subd10_2_655 : subd10_2 [2, 0, -6] = true := by decide +kernel
theorem subd10_2_656 : subd10_2 [2, 0, -5] = true := by decide +kernel
theorem subd10_2_657 : subd10_2 [2, 0, -4] = true := by decide +kernel
theorem subd10_2_658 : subd10_2 [2, 0, -3] = true := by decide +kernel
theorem subd10_2_659 : subd10_2 [2, 0, -2] = true := by decide +kernel
theorem subd10_2_660 : subd10_2 [2, 0, -1] = true := by decide +kernel
theorem subd10_2_661 : subd10_2 [2, 0, 0] = true := by decide +kernel
theorem subd10_2_662 : subd10_2 [2, 0, 1] = true := by decide +kernel
theorem subd10_2_663 : subd10_2 [2, 0, 2] = true := by decide +kernel
theorem subd10_2_664 : subd10_2 [2, 0, 3] = true := by decide +kernel
theorem subd10_2_665 : subd10_2 [2, 0, 4] = true := by decide +kernel
theorem subd10_2_666 : subd10_2 [2, 0, 5] = true := by decide +kernel
theorem subd10_2_667 : subd10_2 [2, 0, 6] = true := by decide +kernel
theorem subd10_2_668 : subd10_2 [2, 0, 7] = true := by decide +kernel
theorem subd10_2_669 : subd10_2 [2, 0, 8] = true := by decide +kernel
theorem subd10_2_670 : subd10_2 [2, 0, 9] = true := by decide +kernel
theorem subd10_2_671 : subd10_2 [2, 0, 10] = true := by decide +kernel
theorem sbd10_2_20 : ∀ q ∈ blkd10_2_20, subd10_2 q = true := by
  unfold blkd10_2_20
  exact List.forall_mem_cons.2 ⟨subd10_2_640, List.forall_mem_cons.2 ⟨subd10_2_641, List.forall_mem_cons.2 ⟨subd10_2_642, List.forall_mem_cons.2 ⟨subd10_2_643, List.forall_mem_cons.2 ⟨subd10_2_644, List.forall_mem_cons.2 ⟨subd10_2_645, List.forall_mem_cons.2 ⟨subd10_2_646, List.forall_mem_cons.2 ⟨subd10_2_647, List.forall_mem_cons.2 ⟨subd10_2_648, List.forall_mem_cons.2 ⟨subd10_2_649, List.forall_mem_cons.2 ⟨subd10_2_650, List.forall_mem_cons.2 ⟨subd10_2_651, List.forall_mem_cons.2 ⟨subd10_2_652, List.forall_mem_cons.2 ⟨subd10_2_653, List.forall_mem_cons.2 ⟨subd10_2_654, List.forall_mem_cons.2 ⟨subd10_2_655, List.forall_mem_cons.2 ⟨subd10_2_656, List.forall_mem_cons.2 ⟨subd10_2_657, List.forall_mem_cons.2 ⟨subd10_2_658, List.forall_mem_cons.2 ⟨subd10_2_659, List.forall_mem_cons.2 ⟨subd10_2_660, List.forall_mem_cons.2 ⟨subd10_2_661, List.forall_mem_cons.2 ⟨subd10_2_662, List.forall_mem_cons.2 ⟨subd10_2_663, List.forall_mem_cons.2 ⟨subd10_2_664, List.forall_mem_cons.2 ⟨subd10_2_665, List.forall_mem_cons.2 ⟨subd10_2_666, List.forall_mem_cons.2 ⟨subd10_2_667, List.forall_mem_cons.2 ⟨subd10_2_668, List.forall_mem_cons.2 ⟨subd10_2_669, List.forall_mem_cons.2 ⟨subd10_2_670, List.forall_mem_cons.2 ⟨subd10_2_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_2_672 : subd10_2 [2, 1, -10] = true := by decide +kernel
theorem subd10_2_673 : subd10_2 [2, 1, -9] = true := by decide +kernel
theorem subd10_2_674 : subd10_2 [2, 1, -8] = true := by decide +kernel
theorem subd10_2_675 : subd10_2 [2, 1, -7] = true := by decide +kernel
theorem subd10_2_676 : subd10_2 [2, 1, -6] = true := by decide +kernel
theorem subd10_2_677 : subd10_2 [2, 1, -5] = true := by decide +kernel
theorem subd10_2_678 : subd10_2 [2, 1, -4] = true := by decide +kernel
theorem subd10_2_679 : subd10_2 [2, 1, -3] = true := by decide +kernel
theorem subd10_2_680 : subd10_2 [2, 1, -2] = true := by decide +kernel
theorem subd10_2_681 : subd10_2 [2, 1, -1] = true := by decide +kernel
theorem subd10_2_682 : subd10_2 [2, 1, 0] = true := by decide +kernel
theorem subd10_2_683 : subd10_2 [2, 1, 1] = true := by decide +kernel
theorem subd10_2_684 : subd10_2 [2, 1, 2] = true := by decide +kernel
theorem subd10_2_685 : subd10_2 [2, 1, 3] = true := by decide +kernel
theorem subd10_2_686 : subd10_2 [2, 1, 4] = true := by decide +kernel
theorem subd10_2_687 : subd10_2 [2, 1, 5] = true := by decide +kernel
theorem subd10_2_688 : subd10_2 [2, 1, 6] = true := by decide +kernel
theorem subd10_2_689 : subd10_2 [2, 1, 7] = true := by decide +kernel
theorem subd10_2_690 : subd10_2 [3] = true := by decide +kernel
theorem sbd10_2_21 : ∀ q ∈ blkd10_2_21, subd10_2 q = true := by
  unfold blkd10_2_21
  exact List.forall_mem_cons.2 ⟨subd10_2_672, List.forall_mem_cons.2 ⟨subd10_2_673, List.forall_mem_cons.2 ⟨subd10_2_674, List.forall_mem_cons.2 ⟨subd10_2_675, List.forall_mem_cons.2 ⟨subd10_2_676, List.forall_mem_cons.2 ⟨subd10_2_677, List.forall_mem_cons.2 ⟨subd10_2_678, List.forall_mem_cons.2 ⟨subd10_2_679, List.forall_mem_cons.2 ⟨subd10_2_680, List.forall_mem_cons.2 ⟨subd10_2_681, List.forall_mem_cons.2 ⟨subd10_2_682, List.forall_mem_cons.2 ⟨subd10_2_683, List.forall_mem_cons.2 ⟨subd10_2_684, List.forall_mem_cons.2 ⟨subd10_2_685, List.forall_mem_cons.2 ⟨subd10_2_686, List.forall_mem_cons.2 ⟨subd10_2_687, List.forall_mem_cons.2 ⟨subd10_2_688, List.forall_mem_cons.2 ⟨subd10_2_689, List.forall_mem_cons.2 ⟨subd10_2_690, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_3 : ldCheck G d10_3.U d10_3.ms ldd10_3 = true := by decide +kernel
theorem pre_okd10_3 : subPre G cell10 d10_3 = true := by decide +kernel
theorem subd10_3_0 : subd10_3 [-6, -3] = true := by decide +kernel
theorem subd10_3_1 : subd10_3 [-6, -2] = true := by decide +kernel
theorem subd10_3_2 : subd10_3 [-6, -1] = true := by decide +kernel
theorem subd10_3_3 : subd10_3 [-6, 0] = true := by decide +kernel
theorem subd10_3_4 : subd10_3 [-6, 1] = true := by decide +kernel
theorem subd10_3_5 : subd10_3 [-6, 2] = true := by decide +kernel
theorem subd10_3_6 : subd10_3 [-6, 3] = true := by decide +kernel
theorem subd10_3_7 : subd10_3 [-5, -4] = true := by decide +kernel
theorem subd10_3_8 : subd10_3 [-5, -3] = true := by decide +kernel
theorem subd10_3_9 : subd10_3 [-5, -2] = true := by decide +kernel
theorem subd10_3_10 : subd10_3 [-5, -1] = true := by decide +kernel
theorem subd10_3_11 : subd10_3 [-5, 0] = true := by decide +kernel
theorem subd10_3_12 : subd10_3 [-5, 1] = true := by decide +kernel
theorem subd10_3_13 : subd10_3 [-5, 2] = true := by decide +kernel
theorem subd10_3_14 : subd10_3 [-5, 3] = true := by decide +kernel
theorem subd10_3_15 : subd10_3 [-5, 4] = true := by decide +kernel
theorem subd10_3_16 : subd10_3 [-4, -5] = true := by decide +kernel
theorem subd10_3_17 : subd10_3 [-4, -4] = true := by decide +kernel
theorem subd10_3_18 : subd10_3 [-4, -3] = true := by decide +kernel
theorem subd10_3_19 : subd10_3 [-4, -2, -7] = true := by decide +kernel
theorem subd10_3_20 : subd10_3 [-4, -2, -6] = true := by decide +kernel
theorem subd10_3_21 : subd10_3 [-4, -2, -5] = true := by decide +kernel
theorem subd10_3_22 : subd10_3 [-4, -2, -4] = true := by decide +kernel
theorem subd10_3_23 : subd10_3 [-4, -2, -3] = true := by decide +kernel
theorem subd10_3_24 : subd10_3 [-4, -2, -2] = true := by decide +kernel
theorem subd10_3_25 : subd10_3 [-4, -2, -1] = true := by decide +kernel
theorem subd10_3_26 : subd10_3 [-4, -2, 0] = true := by decide +kernel
theorem subd10_3_27 : subd10_3 [-4, -2, 1] = true := by decide +kernel
theorem subd10_3_28 : subd10_3 [-4, -2, 2] = true := by decide +kernel
theorem subd10_3_29 : subd10_3 [-4, -2, 3] = true := by decide +kernel
theorem subd10_3_30 : subd10_3 [-4, -2, 4] = true := by decide +kernel
theorem subd10_3_31 : subd10_3 [-4, -2, 5] = true := by decide +kernel
theorem sbd10_3_0 : ∀ q ∈ blkd10_3_0, subd10_3 q = true := by
  unfold blkd10_3_0
  exact List.forall_mem_cons.2 ⟨subd10_3_0, List.forall_mem_cons.2 ⟨subd10_3_1, List.forall_mem_cons.2 ⟨subd10_3_2, List.forall_mem_cons.2 ⟨subd10_3_3, List.forall_mem_cons.2 ⟨subd10_3_4, List.forall_mem_cons.2 ⟨subd10_3_5, List.forall_mem_cons.2 ⟨subd10_3_6, List.forall_mem_cons.2 ⟨subd10_3_7, List.forall_mem_cons.2 ⟨subd10_3_8, List.forall_mem_cons.2 ⟨subd10_3_9, List.forall_mem_cons.2 ⟨subd10_3_10, List.forall_mem_cons.2 ⟨subd10_3_11, List.forall_mem_cons.2 ⟨subd10_3_12, List.forall_mem_cons.2 ⟨subd10_3_13, List.forall_mem_cons.2 ⟨subd10_3_14, List.forall_mem_cons.2 ⟨subd10_3_15, List.forall_mem_cons.2 ⟨subd10_3_16, List.forall_mem_cons.2 ⟨subd10_3_17, List.forall_mem_cons.2 ⟨subd10_3_18, List.forall_mem_cons.2 ⟨subd10_3_19, List.forall_mem_cons.2 ⟨subd10_3_20, List.forall_mem_cons.2 ⟨subd10_3_21, List.forall_mem_cons.2 ⟨subd10_3_22, List.forall_mem_cons.2 ⟨subd10_3_23, List.forall_mem_cons.2 ⟨subd10_3_24, List.forall_mem_cons.2 ⟨subd10_3_25, List.forall_mem_cons.2 ⟨subd10_3_26, List.forall_mem_cons.2 ⟨subd10_3_27, List.forall_mem_cons.2 ⟨subd10_3_28, List.forall_mem_cons.2 ⟨subd10_3_29, List.forall_mem_cons.2 ⟨subd10_3_30, List.forall_mem_cons.2 ⟨subd10_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C135
