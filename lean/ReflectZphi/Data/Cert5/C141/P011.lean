import ReflectZphi.Data.Cert5.C141.Base

namespace ReflectZphi.Data.Cert5.C141

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_2_448 : subd7_2 [1, -2, -1] = true := by decide +kernel
theorem subd7_2_449 : subd7_2 [1, -2, 0] = true := by decide +kernel
theorem subd7_2_450 : subd7_2 [1, -2, 1] = true := by decide +kernel
theorem subd7_2_451 : subd7_2 [1, -2, 2] = true := by decide +kernel
theorem subd7_2_452 : subd7_2 [1, -2, 3] = true := by decide +kernel
theorem subd7_2_453 : subd7_2 [1, -2, 4] = true := by decide +kernel
theorem subd7_2_454 : subd7_2 [1, -2, 5] = true := by decide +kernel
theorem subd7_2_455 : subd7_2 [1, -2, 6] = true := by decide +kernel
theorem subd7_2_456 : subd7_2 [1, -2, 7] = true := by decide +kernel
theorem subd7_2_457 : subd7_2 [1, -2, 8] = true := by decide +kernel
theorem subd7_2_458 : subd7_2 [1, -1, -8] = true := by decide +kernel
theorem subd7_2_459 : subd7_2 [1, -1, -7] = true := by decide +kernel
theorem subd7_2_460 : subd7_2 [1, -1, -6] = true := by decide +kernel
theorem subd7_2_461 : subd7_2 [1, -1, -5] = true := by decide +kernel
theorem subd7_2_462 : subd7_2 [1, -1, -4] = true := by decide +kernel
theorem subd7_2_463 : subd7_2 [1, -1, -3] = true := by decide +kernel
theorem subd7_2_464 : subd7_2 [1, -1, -2] = true := by decide +kernel
theorem subd7_2_465 : subd7_2 [1, -1, -1] = true := by decide +kernel
theorem subd7_2_466 : subd7_2 [1, -1, 0] = true := by decide +kernel
theorem subd7_2_467 : subd7_2 [1, -1, 1] = true := by decide +kernel
theorem subd7_2_468 : subd7_2 [1, -1, 2] = true := by decide +kernel
theorem subd7_2_469 : subd7_2 [1, -1, 3] = true := by decide +kernel
theorem subd7_2_470 : subd7_2 [1, -1, 4] = true := by decide +kernel
theorem subd7_2_471 : subd7_2 [1, -1, 5] = true := by decide +kernel
theorem subd7_2_472 : subd7_2 [1, -1, 6] = true := by decide +kernel
theorem subd7_2_473 : subd7_2 [1, -1, 7] = true := by decide +kernel
theorem subd7_2_474 : subd7_2 [1, -1, 8] = true := by decide +kernel
theorem subd7_2_475 : subd7_2 [1, 0, -9] = true := by decide +kernel
theorem subd7_2_476 : subd7_2 [1, 0, -8] = true := by decide +kernel
theorem subd7_2_477 : subd7_2 [1, 0, -7] = true := by decide +kernel
theorem subd7_2_478 : subd7_2 [1, 0, -6] = true := by decide +kernel
theorem subd7_2_479 : subd7_2 [1, 0, -5] = true := by decide +kernel
theorem sbd7_2_14 : ∀ q ∈ blkd7_2_14, subd7_2 q = true := by
  unfold blkd7_2_14
  exact List.forall_mem_cons.2 ⟨subd7_2_448, List.forall_mem_cons.2 ⟨subd7_2_449, List.forall_mem_cons.2 ⟨subd7_2_450, List.forall_mem_cons.2 ⟨subd7_2_451, List.forall_mem_cons.2 ⟨subd7_2_452, List.forall_mem_cons.2 ⟨subd7_2_453, List.forall_mem_cons.2 ⟨subd7_2_454, List.forall_mem_cons.2 ⟨subd7_2_455, List.forall_mem_cons.2 ⟨subd7_2_456, List.forall_mem_cons.2 ⟨subd7_2_457, List.forall_mem_cons.2 ⟨subd7_2_458, List.forall_mem_cons.2 ⟨subd7_2_459, List.forall_mem_cons.2 ⟨subd7_2_460, List.forall_mem_cons.2 ⟨subd7_2_461, List.forall_mem_cons.2 ⟨subd7_2_462, List.forall_mem_cons.2 ⟨subd7_2_463, List.forall_mem_cons.2 ⟨subd7_2_464, List.forall_mem_cons.2 ⟨subd7_2_465, List.forall_mem_cons.2 ⟨subd7_2_466, List.forall_mem_cons.2 ⟨subd7_2_467, List.forall_mem_cons.2 ⟨subd7_2_468, List.forall_mem_cons.2 ⟨subd7_2_469, List.forall_mem_cons.2 ⟨subd7_2_470, List.forall_mem_cons.2 ⟨subd7_2_471, List.forall_mem_cons.2 ⟨subd7_2_472, List.forall_mem_cons.2 ⟨subd7_2_473, List.forall_mem_cons.2 ⟨subd7_2_474, List.forall_mem_cons.2 ⟨subd7_2_475, List.forall_mem_cons.2 ⟨subd7_2_476, List.forall_mem_cons.2 ⟨subd7_2_477, List.forall_mem_cons.2 ⟨subd7_2_478, List.forall_mem_cons.2 ⟨subd7_2_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_480 : subd7_2 [1, 0, -4] = true := by decide +kernel
theorem subd7_2_481 : subd7_2 [1, 0, -3] = true := by decide +kernel
theorem subd7_2_482 : subd7_2 [1, 0, -2] = true := by decide +kernel
theorem subd7_2_483 : subd7_2 [1, 0, -1] = true := by decide +kernel
theorem subd7_2_484 : subd7_2 [1, 0, 0] = true := by decide +kernel
theorem subd7_2_485 : subd7_2 [1, 0, 1] = true := by decide +kernel
theorem subd7_2_486 : subd7_2 [1, 0, 2] = true := by decide +kernel
theorem subd7_2_487 : subd7_2 [1, 0, 3] = true := by decide +kernel
theorem subd7_2_488 : subd7_2 [1, 0, 4] = true := by decide +kernel
theorem subd7_2_489 : subd7_2 [1, 0, 5] = true := by decide +kernel
theorem subd7_2_490 : subd7_2 [1, 0, 6] = true := by decide +kernel
theorem subd7_2_491 : subd7_2 [1, 0, 7] = true := by decide +kernel
theorem subd7_2_492 : subd7_2 [1, 0, 8] = true := by decide +kernel
theorem subd7_2_493 : subd7_2 [1, 0, 9] = true := by decide +kernel
theorem subd7_2_494 : subd7_2 [1, 1, -9] = true := by decide +kernel
theorem subd7_2_495 : subd7_2 [1, 1, -8] = true := by decide +kernel
theorem subd7_2_496 : subd7_2 [1, 1, -7] = true := by decide +kernel
theorem subd7_2_497 : subd7_2 [1, 1, -6] = true := by decide +kernel
theorem subd7_2_498 : subd7_2 [1, 1, -5] = true := by decide +kernel
theorem subd7_2_499 : subd7_2 [1, 1, -4] = true := by decide +kernel
theorem subd7_2_500 : subd7_2 [1, 1, -3] = true := by decide +kernel
theorem subd7_2_501 : subd7_2 [1, 1, -2] = true := by decide +kernel
theorem subd7_2_502 : subd7_2 [1, 1, -1] = true := by decide +kernel
theorem subd7_2_503 : subd7_2 [1, 1, 0] = true := by decide +kernel
theorem subd7_2_504 : subd7_2 [1, 1, 1] = true := by decide +kernel
theorem subd7_2_505 : subd7_2 [1, 1, 2] = true := by decide +kernel
theorem subd7_2_506 : subd7_2 [1, 1, 3] = true := by decide +kernel
theorem subd7_2_507 : subd7_2 [1, 1, 4] = true := by decide +kernel
theorem subd7_2_508 : subd7_2 [1, 1, 5] = true := by decide +kernel
theorem subd7_2_509 : subd7_2 [1, 1, 6] = true := by decide +kernel
theorem subd7_2_510 : subd7_2 [1, 1, 7] = true := by decide +kernel
theorem subd7_2_511 : subd7_2 [1, 1, 8] = true := by decide +kernel
theorem sbd7_2_15 : ∀ q ∈ blkd7_2_15, subd7_2 q = true := by
  unfold blkd7_2_15
  exact List.forall_mem_cons.2 ⟨subd7_2_480, List.forall_mem_cons.2 ⟨subd7_2_481, List.forall_mem_cons.2 ⟨subd7_2_482, List.forall_mem_cons.2 ⟨subd7_2_483, List.forall_mem_cons.2 ⟨subd7_2_484, List.forall_mem_cons.2 ⟨subd7_2_485, List.forall_mem_cons.2 ⟨subd7_2_486, List.forall_mem_cons.2 ⟨subd7_2_487, List.forall_mem_cons.2 ⟨subd7_2_488, List.forall_mem_cons.2 ⟨subd7_2_489, List.forall_mem_cons.2 ⟨subd7_2_490, List.forall_mem_cons.2 ⟨subd7_2_491, List.forall_mem_cons.2 ⟨subd7_2_492, List.forall_mem_cons.2 ⟨subd7_2_493, List.forall_mem_cons.2 ⟨subd7_2_494, List.forall_mem_cons.2 ⟨subd7_2_495, List.forall_mem_cons.2 ⟨subd7_2_496, List.forall_mem_cons.2 ⟨subd7_2_497, List.forall_mem_cons.2 ⟨subd7_2_498, List.forall_mem_cons.2 ⟨subd7_2_499, List.forall_mem_cons.2 ⟨subd7_2_500, List.forall_mem_cons.2 ⟨subd7_2_501, List.forall_mem_cons.2 ⟨subd7_2_502, List.forall_mem_cons.2 ⟨subd7_2_503, List.forall_mem_cons.2 ⟨subd7_2_504, List.forall_mem_cons.2 ⟨subd7_2_505, List.forall_mem_cons.2 ⟨subd7_2_506, List.forall_mem_cons.2 ⟨subd7_2_507, List.forall_mem_cons.2 ⟨subd7_2_508, List.forall_mem_cons.2 ⟨subd7_2_509, List.forall_mem_cons.2 ⟨subd7_2_510, List.forall_mem_cons.2 ⟨subd7_2_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_512 : subd7_2 [1, 2, -8] = true := by decide +kernel
theorem subd7_2_513 : subd7_2 [1, 2, -7] = true := by decide +kernel
theorem subd7_2_514 : subd7_2 [1, 2, -6] = true := by decide +kernel
theorem subd7_2_515 : subd7_2 [1, 2, -5] = true := by decide +kernel
theorem subd7_2_516 : subd7_2 [1, 2, -4] = true := by decide +kernel
theorem subd7_2_517 : subd7_2 [1, 2, -3] = true := by decide +kernel
theorem subd7_2_518 : subd7_2 [1, 2, -2] = true := by decide +kernel
theorem subd7_2_519 : subd7_2 [1, 2, -1] = true := by decide +kernel
theorem subd7_2_520 : subd7_2 [1, 2, 0] = true := by decide +kernel
theorem subd7_2_521 : subd7_2 [1, 2, 1] = true := by decide +kernel
theorem subd7_2_522 : subd7_2 [1, 2, 2] = true := by decide +kernel
theorem subd7_2_523 : subd7_2 [1, 2, 3] = true := by decide +kernel
theorem subd7_2_524 : subd7_2 [1, 2, 4] = true := by decide +kernel
theorem subd7_2_525 : subd7_2 [1, 2, 5] = true := by decide +kernel
theorem subd7_2_526 : subd7_2 [1, 2, 6] = true := by decide +kernel
theorem subd7_2_527 : subd7_2 [1, 2, 7] = true := by decide +kernel
theorem subd7_2_528 : subd7_2 [1, 2, 8] = true := by decide +kernel
theorem subd7_2_529 : subd7_2 [1, 3, -7] = true := by decide +kernel
theorem subd7_2_530 : subd7_2 [1, 3, -6] = true := by decide +kernel
theorem subd7_2_531 : subd7_2 [1, 3, -5] = true := by decide +kernel
theorem subd7_2_532 : subd7_2 [1, 3, -4] = true := by decide +kernel
theorem subd7_2_533 : subd7_2 [1, 3, -3] = true := by decide +kernel
theorem subd7_2_534 : subd7_2 [1, 3, -2] = true := by decide +kernel
theorem subd7_2_535 : subd7_2 [1, 3, -1] = true := by decide +kernel
theorem subd7_2_536 : subd7_2 [1, 3, 0] = true := by decide +kernel
theorem subd7_2_537 : subd7_2 [1, 3, 1] = true := by decide +kernel
theorem subd7_2_538 : subd7_2 [1, 3, 2] = true := by decide +kernel
theorem subd7_2_539 : subd7_2 [1, 3, 3] = true := by decide +kernel
theorem subd7_2_540 : subd7_2 [1, 3, 4] = true := by decide +kernel
theorem subd7_2_541 : subd7_2 [1, 3, 5] = true := by decide +kernel
theorem subd7_2_542 : subd7_2 [1, 3, 6] = true := by decide +kernel
theorem subd7_2_543 : subd7_2 [1, 3, 7] = true := by decide +kernel
theorem sbd7_2_16 : ∀ q ∈ blkd7_2_16, subd7_2 q = true := by
  unfold blkd7_2_16
  exact List.forall_mem_cons.2 ⟨subd7_2_512, List.forall_mem_cons.2 ⟨subd7_2_513, List.forall_mem_cons.2 ⟨subd7_2_514, List.forall_mem_cons.2 ⟨subd7_2_515, List.forall_mem_cons.2 ⟨subd7_2_516, List.forall_mem_cons.2 ⟨subd7_2_517, List.forall_mem_cons.2 ⟨subd7_2_518, List.forall_mem_cons.2 ⟨subd7_2_519, List.forall_mem_cons.2 ⟨subd7_2_520, List.forall_mem_cons.2 ⟨subd7_2_521, List.forall_mem_cons.2 ⟨subd7_2_522, List.forall_mem_cons.2 ⟨subd7_2_523, List.forall_mem_cons.2 ⟨subd7_2_524, List.forall_mem_cons.2 ⟨subd7_2_525, List.forall_mem_cons.2 ⟨subd7_2_526, List.forall_mem_cons.2 ⟨subd7_2_527, List.forall_mem_cons.2 ⟨subd7_2_528, List.forall_mem_cons.2 ⟨subd7_2_529, List.forall_mem_cons.2 ⟨subd7_2_530, List.forall_mem_cons.2 ⟨subd7_2_531, List.forall_mem_cons.2 ⟨subd7_2_532, List.forall_mem_cons.2 ⟨subd7_2_533, List.forall_mem_cons.2 ⟨subd7_2_534, List.forall_mem_cons.2 ⟨subd7_2_535, List.forall_mem_cons.2 ⟨subd7_2_536, List.forall_mem_cons.2 ⟨subd7_2_537, List.forall_mem_cons.2 ⟨subd7_2_538, List.forall_mem_cons.2 ⟨subd7_2_539, List.forall_mem_cons.2 ⟨subd7_2_540, List.forall_mem_cons.2 ⟨subd7_2_541, List.forall_mem_cons.2 ⟨subd7_2_542, List.forall_mem_cons.2 ⟨subd7_2_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_544 : subd7_2 [1, 4] = true := by decide +kernel
theorem subd7_2_545 : subd7_2 [1, 5] = true := by decide +kernel
theorem subd7_2_546 : subd7_2 [2, -5] = true := by decide +kernel
theorem subd7_2_547 : subd7_2 [2, -4] = true := by decide +kernel
theorem subd7_2_548 : subd7_2 [2, -3] = true := by decide +kernel
theorem subd7_2_549 : subd7_2 [2, -2, -7] = true := by decide +kernel
theorem subd7_2_550 : subd7_2 [2, -2, -6] = true := by decide +kernel
theorem subd7_2_551 : subd7_2 [2, -2, -5] = true := by decide +kernel
theorem subd7_2_552 : subd7_2 [2, -2, -4] = true := by decide +kernel
theorem subd7_2_553 : subd7_2 [2, -2, -3] = true := by decide +kernel
theorem subd7_2_554 : subd7_2 [2, -2, -2] = true := by decide +kernel
theorem subd7_2_555 : subd7_2 [2, -2, -1] = true := by decide +kernel
theorem subd7_2_556 : subd7_2 [2, -2, 0] = true := by decide +kernel
theorem subd7_2_557 : subd7_2 [2, -2, 1] = true := by decide +kernel
theorem subd7_2_558 : subd7_2 [2, -2, 2] = true := by decide +kernel
theorem subd7_2_559 : subd7_2 [2, -2, 3] = true := by decide +kernel
theorem subd7_2_560 : subd7_2 [2, -2, 4] = true := by decide +kernel
theorem subd7_2_561 : subd7_2 [2, -2, 5] = true := by decide +kernel
theorem subd7_2_562 : subd7_2 [2, -2, 6] = true := by decide +kernel
theorem subd7_2_563 : subd7_2 [2, -2, 7] = true := by decide +kernel
theorem subd7_2_564 : subd7_2 [2, -2, 8] = true := by decide +kernel
theorem subd7_2_565 : subd7_2 [2, -1, -7] = true := by decide +kernel
theorem subd7_2_566 : subd7_2 [2, -1, -6] = true := by decide +kernel
theorem subd7_2_567 : subd7_2 [2, -1, -5] = true := by decide +kernel
theorem subd7_2_568 : subd7_2 [2, -1, -4] = true := by decide +kernel
theorem subd7_2_569 : subd7_2 [2, -1, -3] = true := by decide +kernel
theorem subd7_2_570 : subd7_2 [2, -1, -2] = true := by decide +kernel
theorem subd7_2_571 : subd7_2 [2, -1, -1] = true := by decide +kernel
theorem subd7_2_572 : subd7_2 [2, -1, 0] = true := by decide +kernel
theorem subd7_2_573 : subd7_2 [2, -1, 1] = true := by decide +kernel
theorem subd7_2_574 : subd7_2 [2, -1, 2] = true := by decide +kernel
theorem subd7_2_575 : subd7_2 [2, -1, 3] = true := by decide +kernel
theorem sbd7_2_17 : ∀ q ∈ blkd7_2_17, subd7_2 q = true := by
  unfold blkd7_2_17
  exact List.forall_mem_cons.2 ⟨subd7_2_544, List.forall_mem_cons.2 ⟨subd7_2_545, List.forall_mem_cons.2 ⟨subd7_2_546, List.forall_mem_cons.2 ⟨subd7_2_547, List.forall_mem_cons.2 ⟨subd7_2_548, List.forall_mem_cons.2 ⟨subd7_2_549, List.forall_mem_cons.2 ⟨subd7_2_550, List.forall_mem_cons.2 ⟨subd7_2_551, List.forall_mem_cons.2 ⟨subd7_2_552, List.forall_mem_cons.2 ⟨subd7_2_553, List.forall_mem_cons.2 ⟨subd7_2_554, List.forall_mem_cons.2 ⟨subd7_2_555, List.forall_mem_cons.2 ⟨subd7_2_556, List.forall_mem_cons.2 ⟨subd7_2_557, List.forall_mem_cons.2 ⟨subd7_2_558, List.forall_mem_cons.2 ⟨subd7_2_559, List.forall_mem_cons.2 ⟨subd7_2_560, List.forall_mem_cons.2 ⟨subd7_2_561, List.forall_mem_cons.2 ⟨subd7_2_562, List.forall_mem_cons.2 ⟨subd7_2_563, List.forall_mem_cons.2 ⟨subd7_2_564, List.forall_mem_cons.2 ⟨subd7_2_565, List.forall_mem_cons.2 ⟨subd7_2_566, List.forall_mem_cons.2 ⟨subd7_2_567, List.forall_mem_cons.2 ⟨subd7_2_568, List.forall_mem_cons.2 ⟨subd7_2_569, List.forall_mem_cons.2 ⟨subd7_2_570, List.forall_mem_cons.2 ⟨subd7_2_571, List.forall_mem_cons.2 ⟨subd7_2_572, List.forall_mem_cons.2 ⟨subd7_2_573, List.forall_mem_cons.2 ⟨subd7_2_574, List.forall_mem_cons.2 ⟨subd7_2_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_576 : subd7_2 [2, -1, 4] = true := by decide +kernel
theorem subd7_2_577 : subd7_2 [2, -1, 5] = true := by decide +kernel
theorem subd7_2_578 : subd7_2 [2, -1, 6] = true := by decide +kernel
theorem subd7_2_579 : subd7_2 [2, -1, 7] = true := by decide +kernel
theorem subd7_2_580 : subd7_2 [2, -1, 8] = true := by decide +kernel
theorem subd7_2_581 : subd7_2 [2, 0, -8] = true := by decide +kernel
theorem subd7_2_582 : subd7_2 [2, 0, -7] = true := by decide +kernel
theorem subd7_2_583 : subd7_2 [2, 0, -6] = true := by decide +kernel
theorem subd7_2_584 : subd7_2 [2, 0, -5] = true := by decide +kernel
theorem subd7_2_585 : subd7_2 [2, 0, -4] = true := by decide +kernel
theorem subd7_2_586 : subd7_2 [2, 0, -3] = true := by decide +kernel
theorem subd7_2_587 : subd7_2 [2, 0, -2] = true := by decide +kernel
theorem subd7_2_588 : subd7_2 [2, 0, -1] = true := by decide +kernel
theorem subd7_2_589 : subd7_2 [2, 0, 0] = true := by decide +kernel
theorem subd7_2_590 : subd7_2 [2, 0, 1] = true := by decide +kernel
theorem subd7_2_591 : subd7_2 [2, 0, 2] = true := by decide +kernel
theorem subd7_2_592 : subd7_2 [2, 0, 3] = true := by decide +kernel
theorem subd7_2_593 : subd7_2 [2, 0, 4] = true := by decide +kernel
theorem subd7_2_594 : subd7_2 [2, 0, 5] = true := by decide +kernel
theorem subd7_2_595 : subd7_2 [2, 0, 6] = true := by decide +kernel
theorem subd7_2_596 : subd7_2 [2, 0, 7] = true := by decide +kernel
theorem subd7_2_597 : subd7_2 [2, 0, 8] = true := by decide +kernel
theorem subd7_2_598 : subd7_2 [2, 1, -8] = true := by decide +kernel
theorem subd7_2_599 : subd7_2 [2, 1, -7] = true := by decide +kernel
theorem subd7_2_600 : subd7_2 [2, 1, -6] = true := by decide +kernel
theorem subd7_2_601 : subd7_2 [2, 1, -5] = true := by decide +kernel
theorem subd7_2_602 : subd7_2 [2, 1, -4] = true := by decide +kernel
theorem subd7_2_603 : subd7_2 [2, 1, -3] = true := by decide +kernel
theorem subd7_2_604 : subd7_2 [2, 1, -2] = true := by decide +kernel
theorem subd7_2_605 : subd7_2 [2, 1, -1] = true := by decide +kernel
theorem subd7_2_606 : subd7_2 [2, 1, 0] = true := by decide +kernel
theorem subd7_2_607 : subd7_2 [2, 1, 1] = true := by decide +kernel
theorem sbd7_2_18 : ∀ q ∈ blkd7_2_18, subd7_2 q = true := by
  unfold blkd7_2_18
  exact List.forall_mem_cons.2 ⟨subd7_2_576, List.forall_mem_cons.2 ⟨subd7_2_577, List.forall_mem_cons.2 ⟨subd7_2_578, List.forall_mem_cons.2 ⟨subd7_2_579, List.forall_mem_cons.2 ⟨subd7_2_580, List.forall_mem_cons.2 ⟨subd7_2_581, List.forall_mem_cons.2 ⟨subd7_2_582, List.forall_mem_cons.2 ⟨subd7_2_583, List.forall_mem_cons.2 ⟨subd7_2_584, List.forall_mem_cons.2 ⟨subd7_2_585, List.forall_mem_cons.2 ⟨subd7_2_586, List.forall_mem_cons.2 ⟨subd7_2_587, List.forall_mem_cons.2 ⟨subd7_2_588, List.forall_mem_cons.2 ⟨subd7_2_589, List.forall_mem_cons.2 ⟨subd7_2_590, List.forall_mem_cons.2 ⟨subd7_2_591, List.forall_mem_cons.2 ⟨subd7_2_592, List.forall_mem_cons.2 ⟨subd7_2_593, List.forall_mem_cons.2 ⟨subd7_2_594, List.forall_mem_cons.2 ⟨subd7_2_595, List.forall_mem_cons.2 ⟨subd7_2_596, List.forall_mem_cons.2 ⟨subd7_2_597, List.forall_mem_cons.2 ⟨subd7_2_598, List.forall_mem_cons.2 ⟨subd7_2_599, List.forall_mem_cons.2 ⟨subd7_2_600, List.forall_mem_cons.2 ⟨subd7_2_601, List.forall_mem_cons.2 ⟨subd7_2_602, List.forall_mem_cons.2 ⟨subd7_2_603, List.forall_mem_cons.2 ⟨subd7_2_604, List.forall_mem_cons.2 ⟨subd7_2_605, List.forall_mem_cons.2 ⟨subd7_2_606, List.forall_mem_cons.2 ⟨subd7_2_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_608 : subd7_2 [2, 1, 2] = true := by decide +kernel
theorem subd7_2_609 : subd7_2 [2, 1, 3] = true := by decide +kernel
theorem subd7_2_610 : subd7_2 [2, 1, 4] = true := by decide +kernel
theorem subd7_2_611 : subd7_2 [2, 1, 5] = true := by decide +kernel
theorem subd7_2_612 : subd7_2 [2, 1, 6] = true := by decide +kernel
theorem subd7_2_613 : subd7_2 [2, 1, 7] = true := by decide +kernel
theorem subd7_2_614 : subd7_2 [2, 1, 8] = true := by decide +kernel
theorem subd7_2_615 : subd7_2 [2, 2, -7] = true := by decide +kernel
theorem subd7_2_616 : subd7_2 [2, 2, -6] = true := by decide +kernel
theorem subd7_2_617 : subd7_2 [2, 2, -5] = true := by decide +kernel
theorem subd7_2_618 : subd7_2 [2, 2, -4] = true := by decide +kernel
theorem subd7_2_619 : subd7_2 [2, 2, -3] = true := by decide +kernel
theorem subd7_2_620 : subd7_2 [2, 2, -2] = true := by decide +kernel
theorem subd7_2_621 : subd7_2 [2, 2, -1] = true := by decide +kernel
theorem subd7_2_622 : subd7_2 [2, 2, 0] = true := by decide +kernel
theorem subd7_2_623 : subd7_2 [2, 2, 1] = true := by decide +kernel
theorem subd7_2_624 : subd7_2 [2, 2, 2] = true := by decide +kernel
theorem subd7_2_625 : subd7_2 [2, 2, 3] = true := by decide +kernel
theorem subd7_2_626 : subd7_2 [2, 2, 4] = true := by decide +kernel
theorem subd7_2_627 : subd7_2 [2, 2, 5] = true := by decide +kernel
theorem subd7_2_628 : subd7_2 [2, 2, 6] = true := by decide +kernel
theorem subd7_2_629 : subd7_2 [2, 2, 7] = true := by decide +kernel
theorem subd7_2_630 : subd7_2 [2, 2, 8] = true := by decide +kernel
theorem subd7_2_631 : subd7_2 [2, 3, -7] = true := by decide +kernel
theorem subd7_2_632 : subd7_2 [2, 3, -6] = true := by decide +kernel
theorem subd7_2_633 : subd7_2 [2, 3, -5] = true := by decide +kernel
theorem subd7_2_634 : subd7_2 [2, 3, -4] = true := by decide +kernel
theorem subd7_2_635 : subd7_2 [2, 3, -3] = true := by decide +kernel
theorem subd7_2_636 : subd7_2 [2, 3, -2] = true := by decide +kernel
theorem subd7_2_637 : subd7_2 [2, 3, -1] = true := by decide +kernel
theorem subd7_2_638 : subd7_2 [2, 3, 0] = true := by decide +kernel
theorem subd7_2_639 : subd7_2 [2, 3, 1] = true := by decide +kernel
theorem sbd7_2_19 : ∀ q ∈ blkd7_2_19, subd7_2 q = true := by
  unfold blkd7_2_19
  exact List.forall_mem_cons.2 ⟨subd7_2_608, List.forall_mem_cons.2 ⟨subd7_2_609, List.forall_mem_cons.2 ⟨subd7_2_610, List.forall_mem_cons.2 ⟨subd7_2_611, List.forall_mem_cons.2 ⟨subd7_2_612, List.forall_mem_cons.2 ⟨subd7_2_613, List.forall_mem_cons.2 ⟨subd7_2_614, List.forall_mem_cons.2 ⟨subd7_2_615, List.forall_mem_cons.2 ⟨subd7_2_616, List.forall_mem_cons.2 ⟨subd7_2_617, List.forall_mem_cons.2 ⟨subd7_2_618, List.forall_mem_cons.2 ⟨subd7_2_619, List.forall_mem_cons.2 ⟨subd7_2_620, List.forall_mem_cons.2 ⟨subd7_2_621, List.forall_mem_cons.2 ⟨subd7_2_622, List.forall_mem_cons.2 ⟨subd7_2_623, List.forall_mem_cons.2 ⟨subd7_2_624, List.forall_mem_cons.2 ⟨subd7_2_625, List.forall_mem_cons.2 ⟨subd7_2_626, List.forall_mem_cons.2 ⟨subd7_2_627, List.forall_mem_cons.2 ⟨subd7_2_628, List.forall_mem_cons.2 ⟨subd7_2_629, List.forall_mem_cons.2 ⟨subd7_2_630, List.forall_mem_cons.2 ⟨subd7_2_631, List.forall_mem_cons.2 ⟨subd7_2_632, List.forall_mem_cons.2 ⟨subd7_2_633, List.forall_mem_cons.2 ⟨subd7_2_634, List.forall_mem_cons.2 ⟨subd7_2_635, List.forall_mem_cons.2 ⟨subd7_2_636, List.forall_mem_cons.2 ⟨subd7_2_637, List.forall_mem_cons.2 ⟨subd7_2_638, List.forall_mem_cons.2 ⟨subd7_2_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_640 : subd7_2 [2, 3, 2] = true := by decide +kernel
theorem subd7_2_641 : subd7_2 [2, 3, 3] = true := by decide +kernel
theorem subd7_2_642 : subd7_2 [2, 3, 4] = true := by decide +kernel
theorem subd7_2_643 : subd7_2 [2, 3, 5] = true := by decide +kernel
theorem subd7_2_644 : subd7_2 [2, 3, 6] = true := by decide +kernel
theorem subd7_2_645 : subd7_2 [2, 3, 7] = true := by decide +kernel
theorem subd7_2_646 : subd7_2 [2, 4] = true := by decide +kernel
theorem subd7_2_647 : subd7_2 [2, 5] = true := by decide +kernel
theorem subd7_2_648 : subd7_2 [3, -4] = true := by decide +kernel
theorem subd7_2_649 : subd7_2 [3, -3] = true := by decide +kernel
theorem subd7_2_650 : subd7_2 [3, -2] = true := by decide +kernel
theorem subd7_2_651 : subd7_2 [3, -1, -6] = true := by decide +kernel
theorem subd7_2_652 : subd7_2 [3, -1, -5] = true := by decide +kernel
theorem subd7_2_653 : subd7_2 [3, -1, -4] = true := by decide +kernel
theorem subd7_2_654 : subd7_2 [3, -1, -3] = true := by decide +kernel
theorem subd7_2_655 : subd7_2 [3, -1, -2] = true := by decide +kernel
theorem subd7_2_656 : subd7_2 [3, -1, -1] = true := by decide +kernel
theorem subd7_2_657 : subd7_2 [3, -1, 0] = true := by decide +kernel
theorem subd7_2_658 : subd7_2 [3, -1, 1] = true := by decide +kernel
theorem subd7_2_659 : subd7_2 [3, -1, 2] = true := by decide +kernel
theorem subd7_2_660 : subd7_2 [3, -1, 3] = true := by decide +kernel
theorem subd7_2_661 : subd7_2 [3, -1, 4] = true := by decide +kernel
theorem subd7_2_662 : subd7_2 [3, -1, 5] = true := by decide +kernel
theorem subd7_2_663 : subd7_2 [3, -1, 6] = true := by decide +kernel
theorem subd7_2_664 : subd7_2 [3, -1, 7] = true := by decide +kernel
theorem subd7_2_665 : subd7_2 [3, 0, -6] = true := by decide +kernel
theorem subd7_2_666 : subd7_2 [3, 0, -5] = true := by decide +kernel
theorem subd7_2_667 : subd7_2 [3, 0, -4] = true := by decide +kernel
theorem subd7_2_668 : subd7_2 [3, 0, -3] = true := by decide +kernel
theorem subd7_2_669 : subd7_2 [3, 0, -2] = true := by decide +kernel
theorem subd7_2_670 : subd7_2 [3, 0, -1] = true := by decide +kernel
theorem subd7_2_671 : subd7_2 [3, 0, 0] = true := by decide +kernel
theorem sbd7_2_20 : ∀ q ∈ blkd7_2_20, subd7_2 q = true := by
  unfold blkd7_2_20
  exact List.forall_mem_cons.2 ⟨subd7_2_640, List.forall_mem_cons.2 ⟨subd7_2_641, List.forall_mem_cons.2 ⟨subd7_2_642, List.forall_mem_cons.2 ⟨subd7_2_643, List.forall_mem_cons.2 ⟨subd7_2_644, List.forall_mem_cons.2 ⟨subd7_2_645, List.forall_mem_cons.2 ⟨subd7_2_646, List.forall_mem_cons.2 ⟨subd7_2_647, List.forall_mem_cons.2 ⟨subd7_2_648, List.forall_mem_cons.2 ⟨subd7_2_649, List.forall_mem_cons.2 ⟨subd7_2_650, List.forall_mem_cons.2 ⟨subd7_2_651, List.forall_mem_cons.2 ⟨subd7_2_652, List.forall_mem_cons.2 ⟨subd7_2_653, List.forall_mem_cons.2 ⟨subd7_2_654, List.forall_mem_cons.2 ⟨subd7_2_655, List.forall_mem_cons.2 ⟨subd7_2_656, List.forall_mem_cons.2 ⟨subd7_2_657, List.forall_mem_cons.2 ⟨subd7_2_658, List.forall_mem_cons.2 ⟨subd7_2_659, List.forall_mem_cons.2 ⟨subd7_2_660, List.forall_mem_cons.2 ⟨subd7_2_661, List.forall_mem_cons.2 ⟨subd7_2_662, List.forall_mem_cons.2 ⟨subd7_2_663, List.forall_mem_cons.2 ⟨subd7_2_664, List.forall_mem_cons.2 ⟨subd7_2_665, List.forall_mem_cons.2 ⟨subd7_2_666, List.forall_mem_cons.2 ⟨subd7_2_667, List.forall_mem_cons.2 ⟨subd7_2_668, List.forall_mem_cons.2 ⟨subd7_2_669, List.forall_mem_cons.2 ⟨subd7_2_670, List.forall_mem_cons.2 ⟨subd7_2_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_672 : subd7_2 [3, 0, 1] = true := by decide +kernel
theorem subd7_2_673 : subd7_2 [3, 0, 2] = true := by decide +kernel
theorem subd7_2_674 : subd7_2 [3, 0, 3] = true := by decide +kernel
theorem subd7_2_675 : subd7_2 [3, 0, 4] = true := by decide +kernel
theorem subd7_2_676 : subd7_2 [3, 0, 5] = true := by decide +kernel
theorem subd7_2_677 : subd7_2 [3, 0, 6] = true := by decide +kernel
theorem subd7_2_678 : subd7_2 [3, 0, 7] = true := by decide +kernel
theorem subd7_2_679 : subd7_2 [3, 0, 8] = true := by decide +kernel
theorem subd7_2_680 : subd7_2 [3, 1, -6] = true := by decide +kernel
theorem subd7_2_681 : subd7_2 [3, 1, -5] = true := by decide +kernel
theorem subd7_2_682 : subd7_2 [3, 1, -4] = true := by decide +kernel
theorem subd7_2_683 : subd7_2 [3, 1, -3] = true := by decide +kernel
theorem subd7_2_684 : subd7_2 [3, 1, -2] = true := by decide +kernel
theorem subd7_2_685 : subd7_2 [3, 1, -1] = true := by decide +kernel
theorem subd7_2_686 : subd7_2 [3, 1, 0] = true := by decide +kernel
theorem subd7_2_687 : subd7_2 [3, 1, 1] = true := by decide +kernel
theorem subd7_2_688 : subd7_2 [3, 1, 2] = true := by decide +kernel
theorem subd7_2_689 : subd7_2 [3, 1, 3] = true := by decide +kernel
theorem subd7_2_690 : subd7_2 [3, 1, 4] = true := by decide +kernel
theorem subd7_2_691 : subd7_2 [3, 1, 5] = true := by decide +kernel
theorem subd7_2_692 : subd7_2 [3, 1, 6] = true := by decide +kernel
theorem subd7_2_693 : subd7_2 [3, 1, 7] = true := by decide +kernel
theorem subd7_2_694 : subd7_2 [3, 1, 8] = true := by decide +kernel
theorem subd7_2_695 : subd7_2 [3, 2, -6] = true := by decide +kernel
theorem subd7_2_696 : subd7_2 [3, 2, -5] = true := by decide +kernel
theorem subd7_2_697 : subd7_2 [3, 2, -4] = true := by decide +kernel
theorem subd7_2_698 : subd7_2 [3, 2, -3] = true := by decide +kernel
theorem subd7_2_699 : subd7_2 [3, 2, -2] = true := by decide +kernel
theorem subd7_2_700 : subd7_2 [3, 2, -1] = true := by decide +kernel
theorem subd7_2_701 : subd7_2 [3, 2, 0] = true := by decide +kernel
theorem subd7_2_702 : subd7_2 [3, 2, 1] = true := by decide +kernel
theorem subd7_2_703 : subd7_2 [3, 2, 2] = true := by decide +kernel
theorem sbd7_2_21 : ∀ q ∈ blkd7_2_21, subd7_2 q = true := by
  unfold blkd7_2_21
  exact List.forall_mem_cons.2 ⟨subd7_2_672, List.forall_mem_cons.2 ⟨subd7_2_673, List.forall_mem_cons.2 ⟨subd7_2_674, List.forall_mem_cons.2 ⟨subd7_2_675, List.forall_mem_cons.2 ⟨subd7_2_676, List.forall_mem_cons.2 ⟨subd7_2_677, List.forall_mem_cons.2 ⟨subd7_2_678, List.forall_mem_cons.2 ⟨subd7_2_679, List.forall_mem_cons.2 ⟨subd7_2_680, List.forall_mem_cons.2 ⟨subd7_2_681, List.forall_mem_cons.2 ⟨subd7_2_682, List.forall_mem_cons.2 ⟨subd7_2_683, List.forall_mem_cons.2 ⟨subd7_2_684, List.forall_mem_cons.2 ⟨subd7_2_685, List.forall_mem_cons.2 ⟨subd7_2_686, List.forall_mem_cons.2 ⟨subd7_2_687, List.forall_mem_cons.2 ⟨subd7_2_688, List.forall_mem_cons.2 ⟨subd7_2_689, List.forall_mem_cons.2 ⟨subd7_2_690, List.forall_mem_cons.2 ⟨subd7_2_691, List.forall_mem_cons.2 ⟨subd7_2_692, List.forall_mem_cons.2 ⟨subd7_2_693, List.forall_mem_cons.2 ⟨subd7_2_694, List.forall_mem_cons.2 ⟨subd7_2_695, List.forall_mem_cons.2 ⟨subd7_2_696, List.forall_mem_cons.2 ⟨subd7_2_697, List.forall_mem_cons.2 ⟨subd7_2_698, List.forall_mem_cons.2 ⟨subd7_2_699, List.forall_mem_cons.2 ⟨subd7_2_700, List.forall_mem_cons.2 ⟨subd7_2_701, List.forall_mem_cons.2 ⟨subd7_2_702, List.forall_mem_cons.2 ⟨subd7_2_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_704 : subd7_2 [3, 2, 3] = true := by decide +kernel
theorem subd7_2_705 : subd7_2 [3, 2, 4] = true := by decide +kernel
theorem subd7_2_706 : subd7_2 [3, 2, 5] = true := by decide +kernel
theorem subd7_2_707 : subd7_2 [3, 2, 6] = true := by decide +kernel
theorem subd7_2_708 : subd7_2 [3, 2, 7] = true := by decide +kernel
theorem subd7_2_709 : subd7_2 [3, 3] = true := by decide +kernel
theorem subd7_2_710 : subd7_2 [3, 4] = true := by decide +kernel
theorem subd7_2_711 : subd7_2 [4, -3] = true := by decide +kernel
theorem subd7_2_712 : subd7_2 [4, -2] = true := by decide +kernel
theorem subd7_2_713 : subd7_2 [4, -1] = true := by decide +kernel
theorem subd7_2_714 : subd7_2 [4, 0] = true := by decide +kernel
theorem subd7_2_715 : subd7_2 [4, 1] = true := by decide +kernel
theorem subd7_2_716 : subd7_2 [4, 2] = true := by decide +kernel
theorem subd7_2_717 : subd7_2 [4, 3] = true := by decide +kernel
theorem subd7_2_718 : subd7_2 [5] = true := by decide +kernel
theorem sbd7_2_22 : ∀ q ∈ blkd7_2_22, subd7_2 q = true := by
  unfold blkd7_2_22
  exact List.forall_mem_cons.2 ⟨subd7_2_704, List.forall_mem_cons.2 ⟨subd7_2_705, List.forall_mem_cons.2 ⟨subd7_2_706, List.forall_mem_cons.2 ⟨subd7_2_707, List.forall_mem_cons.2 ⟨subd7_2_708, List.forall_mem_cons.2 ⟨subd7_2_709, List.forall_mem_cons.2 ⟨subd7_2_710, List.forall_mem_cons.2 ⟨subd7_2_711, List.forall_mem_cons.2 ⟨subd7_2_712, List.forall_mem_cons.2 ⟨subd7_2_713, List.forall_mem_cons.2 ⟨subd7_2_714, List.forall_mem_cons.2 ⟨subd7_2_715, List.forall_mem_cons.2 ⟨subd7_2_716, List.forall_mem_cons.2 ⟨subd7_2_717, List.forall_mem_cons.2 ⟨subd7_2_718, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_3 : ldCheck G d7_3.U d7_3.ms ldd7_3 = true := by decide +kernel
theorem pre_okd7_3 : subPre G cell7 d7_3 = true := by decide +kernel
theorem subd7_3_0 : subd7_3 [-2] = true := by decide +kernel
theorem subd7_3_1 : subd7_3 [-1, -3] = true := by decide +kernel
theorem subd7_3_2 : subd7_3 [-1, -2] = true := by decide +kernel
theorem subd7_3_3 : subd7_3 [-1, -1, -8] = true := by decide +kernel
theorem subd7_3_4 : subd7_3 [-1, -1, -7] = true := by decide +kernel
theorem subd7_3_5 : subd7_3 [-1, -1, -6] = true := by decide +kernel
theorem subd7_3_6 : subd7_3 [-1, -1, -5] = true := by decide +kernel
theorem subd7_3_7 : subd7_3 [-1, -1, -4] = true := by decide +kernel
theorem subd7_3_8 : subd7_3 [-1, -1, -3] = true := by decide +kernel
theorem subd7_3_9 : subd7_3 [-1, -1, -2] = true := by decide +kernel
theorem subd7_3_10 : subd7_3 [-1, -1, -1] = true := by decide +kernel
theorem subd7_3_11 : subd7_3 [-1, -1, 0] = true := by decide +kernel
theorem subd7_3_12 : subd7_3 [-1, -1, 1] = true := by decide +kernel
theorem subd7_3_13 : subd7_3 [-1, -1, 2] = true := by decide +kernel
theorem subd7_3_14 : subd7_3 [-1, -1, 3] = true := by decide +kernel
theorem subd7_3_15 : subd7_3 [-1, -1, 4] = true := by decide +kernel
theorem subd7_3_16 : subd7_3 [-1, -1, 5] = true := by decide +kernel
theorem subd7_3_17 : subd7_3 [-1, -1, 6] = true := by decide +kernel
theorem subd7_3_18 : subd7_3 [-1, -1, 7] = true := by decide +kernel
theorem subd7_3_19 : subd7_3 [-1, 0, -8] = true := by decide +kernel
theorem subd7_3_20 : subd7_3 [-1, 0, -7] = true := by decide +kernel
theorem subd7_3_21 : subd7_3 [-1, 0, -6] = true := by decide +kernel
theorem subd7_3_22 : subd7_3 [-1, 0, -5] = true := by decide +kernel
theorem subd7_3_23 : subd7_3 [-1, 0, -4] = true := by decide +kernel
theorem subd7_3_24 : subd7_3 [-1, 0, -3] = true := by decide +kernel
theorem subd7_3_25 : subd7_3 [-1, 0, -2] = true := by decide +kernel
theorem subd7_3_26 : subd7_3 [-1, 0, -1] = true := by decide +kernel
theorem subd7_3_27 : subd7_3 [-1, 0, 0] = true := by decide +kernel
theorem subd7_3_28 : subd7_3 [-1, 0, 1] = true := by decide +kernel
theorem subd7_3_29 : subd7_3 [-1, 0, 2] = true := by decide +kernel
theorem subd7_3_30 : subd7_3 [-1, 0, 3] = true := by decide +kernel
theorem subd7_3_31 : subd7_3 [-1, 0, 4] = true := by decide +kernel
theorem sbd7_3_0 : ∀ q ∈ blkd7_3_0, subd7_3 q = true := by
  unfold blkd7_3_0
  exact List.forall_mem_cons.2 ⟨subd7_3_0, List.forall_mem_cons.2 ⟨subd7_3_1, List.forall_mem_cons.2 ⟨subd7_3_2, List.forall_mem_cons.2 ⟨subd7_3_3, List.forall_mem_cons.2 ⟨subd7_3_4, List.forall_mem_cons.2 ⟨subd7_3_5, List.forall_mem_cons.2 ⟨subd7_3_6, List.forall_mem_cons.2 ⟨subd7_3_7, List.forall_mem_cons.2 ⟨subd7_3_8, List.forall_mem_cons.2 ⟨subd7_3_9, List.forall_mem_cons.2 ⟨subd7_3_10, List.forall_mem_cons.2 ⟨subd7_3_11, List.forall_mem_cons.2 ⟨subd7_3_12, List.forall_mem_cons.2 ⟨subd7_3_13, List.forall_mem_cons.2 ⟨subd7_3_14, List.forall_mem_cons.2 ⟨subd7_3_15, List.forall_mem_cons.2 ⟨subd7_3_16, List.forall_mem_cons.2 ⟨subd7_3_17, List.forall_mem_cons.2 ⟨subd7_3_18, List.forall_mem_cons.2 ⟨subd7_3_19, List.forall_mem_cons.2 ⟨subd7_3_20, List.forall_mem_cons.2 ⟨subd7_3_21, List.forall_mem_cons.2 ⟨subd7_3_22, List.forall_mem_cons.2 ⟨subd7_3_23, List.forall_mem_cons.2 ⟨subd7_3_24, List.forall_mem_cons.2 ⟨subd7_3_25, List.forall_mem_cons.2 ⟨subd7_3_26, List.forall_mem_cons.2 ⟨subd7_3_27, List.forall_mem_cons.2 ⟨subd7_3_28, List.forall_mem_cons.2 ⟨subd7_3_29, List.forall_mem_cons.2 ⟨subd7_3_30, List.forall_mem_cons.2 ⟨subd7_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_32 : subd7_3 [-1, 0, 5] = true := by decide +kernel
theorem subd7_3_33 : subd7_3 [-1, 0, 6] = true := by decide +kernel
theorem subd7_3_34 : subd7_3 [-1, 0, 7] = true := by decide +kernel
theorem subd7_3_35 : subd7_3 [-1, 1] = true := by decide +kernel
theorem subd7_3_36 : subd7_3 [0, -3] = true := by decide +kernel
theorem subd7_3_37 : subd7_3 [0, -2] = true := by decide +kernel
theorem subd7_3_38 : subd7_3 [0, -1, -8] = true := by decide +kernel
theorem subd7_3_39 : subd7_3 [0, -1, -7] = true := by decide +kernel
theorem subd7_3_40 : subd7_3 [0, -1, -6] = true := by decide +kernel
theorem subd7_3_41 : subd7_3 [0, -1, -5] = true := by decide +kernel
theorem subd7_3_42 : subd7_3 [0, -1, -4] = true := by decide +kernel
theorem subd7_3_43 : subd7_3 [0, -1, -3] = true := by decide +kernel
theorem subd7_3_44 : subd7_3 [0, -1, -2] = true := by decide +kernel
theorem subd7_3_45 : subd7_3 [0, -1, -1] = true := by decide +kernel
theorem subd7_3_46 : subd7_3 [0, -1, 0] = true := by decide +kernel
theorem subd7_3_47 : subd7_3 [0, -1, 1] = true := by decide +kernel
theorem subd7_3_48 : subd7_3 [0, -1, 2] = true := by decide +kernel
theorem subd7_3_49 : subd7_3 [0, -1, 3] = true := by decide +kernel
theorem subd7_3_50 : subd7_3 [0, -1, 4] = true := by decide +kernel
theorem subd7_3_51 : subd7_3 [0, -1, 5] = true := by decide +kernel
theorem subd7_3_52 : subd7_3 [0, -1, 6] = true := by decide +kernel
theorem subd7_3_53 : subd7_3 [0, -1, 7] = true := by decide +kernel
theorem subd7_3_54 : subd7_3 [0, 0, -9] = true := by decide +kernel
theorem subd7_3_55 : subd7_3 [0, 0, -8] = true := by decide +kernel
theorem subd7_3_56 : subd7_3 [0, 0, -7] = true := by decide +kernel
theorem subd7_3_57 : subd7_3 [0, 0, -6] = true := by decide +kernel
theorem subd7_3_58 : subd7_3 [0, 0, -5] = true := by decide +kernel
theorem subd7_3_59 : subd7_3 [0, 0, -4] = true := by decide +kernel
theorem subd7_3_60 : subd7_3 [0, 0, -3] = true := by decide +kernel
theorem subd7_3_61 : subd7_3 [0, 0, -2] = true := by decide +kernel
theorem subd7_3_62 : subd7_3 [0, 0, -1] = true := by decide +kernel
theorem subd7_3_63 : subd7_3 [0, 0, 0] = true := by decide +kernel
theorem sbd7_3_1 : ∀ q ∈ blkd7_3_1, subd7_3 q = true := by
  unfold blkd7_3_1
  exact List.forall_mem_cons.2 ⟨subd7_3_32, List.forall_mem_cons.2 ⟨subd7_3_33, List.forall_mem_cons.2 ⟨subd7_3_34, List.forall_mem_cons.2 ⟨subd7_3_35, List.forall_mem_cons.2 ⟨subd7_3_36, List.forall_mem_cons.2 ⟨subd7_3_37, List.forall_mem_cons.2 ⟨subd7_3_38, List.forall_mem_cons.2 ⟨subd7_3_39, List.forall_mem_cons.2 ⟨subd7_3_40, List.forall_mem_cons.2 ⟨subd7_3_41, List.forall_mem_cons.2 ⟨subd7_3_42, List.forall_mem_cons.2 ⟨subd7_3_43, List.forall_mem_cons.2 ⟨subd7_3_44, List.forall_mem_cons.2 ⟨subd7_3_45, List.forall_mem_cons.2 ⟨subd7_3_46, List.forall_mem_cons.2 ⟨subd7_3_47, List.forall_mem_cons.2 ⟨subd7_3_48, List.forall_mem_cons.2 ⟨subd7_3_49, List.forall_mem_cons.2 ⟨subd7_3_50, List.forall_mem_cons.2 ⟨subd7_3_51, List.forall_mem_cons.2 ⟨subd7_3_52, List.forall_mem_cons.2 ⟨subd7_3_53, List.forall_mem_cons.2 ⟨subd7_3_54, List.forall_mem_cons.2 ⟨subd7_3_55, List.forall_mem_cons.2 ⟨subd7_3_56, List.forall_mem_cons.2 ⟨subd7_3_57, List.forall_mem_cons.2 ⟨subd7_3_58, List.forall_mem_cons.2 ⟨subd7_3_59, List.forall_mem_cons.2 ⟨subd7_3_60, List.forall_mem_cons.2 ⟨subd7_3_61, List.forall_mem_cons.2 ⟨subd7_3_62, List.forall_mem_cons.2 ⟨subd7_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_64 : subd7_3 [0, 0, 1] = true := by decide +kernel
theorem subd7_3_65 : subd7_3 [0, 0, 2] = true := by decide +kernel
theorem subd7_3_66 : subd7_3 [0, 0, 3] = true := by decide +kernel
theorem subd7_3_67 : subd7_3 [0, 0, 4] = true := by decide +kernel
theorem subd7_3_68 : subd7_3 [0, 0, 5] = true := by decide +kernel
theorem subd7_3_69 : subd7_3 [0, 0, 6] = true := by decide +kernel
theorem subd7_3_70 : subd7_3 [0, 0, 7] = true := by decide +kernel
theorem subd7_3_71 : subd7_3 [0, 0, 8] = true := by decide +kernel
theorem subd7_3_72 : subd7_3 [0, 1, -8] = true := by decide +kernel
theorem subd7_3_73 : subd7_3 [0, 1, -7] = true := by decide +kernel
theorem subd7_3_74 : subd7_3 [0, 1, -6] = true := by decide +kernel
theorem subd7_3_75 : subd7_3 [0, 1, -5] = true := by decide +kernel
theorem subd7_3_76 : subd7_3 [0, 1, -4] = true := by decide +kernel
theorem subd7_3_77 : subd7_3 [0, 1, -3] = true := by decide +kernel
theorem subd7_3_78 : subd7_3 [0, 1, -2] = true := by decide +kernel
theorem subd7_3_79 : subd7_3 [0, 1, -1] = true := by decide +kernel
theorem subd7_3_80 : subd7_3 [0, 1, 0] = true := by decide +kernel
theorem subd7_3_81 : subd7_3 [0, 1, 1] = true := by decide +kernel
theorem subd7_3_82 : subd7_3 [0, 1, 2] = true := by decide +kernel
theorem subd7_3_83 : subd7_3 [0, 1, 3] = true := by decide +kernel
theorem subd7_3_84 : subd7_3 [0, 1, 4] = true := by decide +kernel
theorem subd7_3_85 : subd7_3 [0, 1, 5] = true := by decide +kernel
theorem subd7_3_86 : subd7_3 [0, 1, 6] = true := by decide +kernel
theorem subd7_3_87 : subd7_3 [0, 1, 7] = true := by decide +kernel
theorem subd7_3_88 : subd7_3 [0, 2] = true := by decide +kernel
theorem subd7_3_89 : subd7_3 [1, -2] = true := by decide +kernel
theorem subd7_3_90 : subd7_3 [1, -1] = true := by decide +kernel
theorem subd7_3_91 : subd7_3 [1, 0, -8] = true := by decide +kernel
theorem subd7_3_92 : subd7_3 [1, 0, -7] = true := by decide +kernel
theorem subd7_3_93 : subd7_3 [1, 0, -6] = true := by decide +kernel
theorem subd7_3_94 : subd7_3 [1, 0, -5] = true := by decide +kernel
theorem subd7_3_95 : subd7_3 [1, 0, -4] = true := by decide +kernel
theorem sbd7_3_2 : ∀ q ∈ blkd7_3_2, subd7_3 q = true := by
  unfold blkd7_3_2
  exact List.forall_mem_cons.2 ⟨subd7_3_64, List.forall_mem_cons.2 ⟨subd7_3_65, List.forall_mem_cons.2 ⟨subd7_3_66, List.forall_mem_cons.2 ⟨subd7_3_67, List.forall_mem_cons.2 ⟨subd7_3_68, List.forall_mem_cons.2 ⟨subd7_3_69, List.forall_mem_cons.2 ⟨subd7_3_70, List.forall_mem_cons.2 ⟨subd7_3_71, List.forall_mem_cons.2 ⟨subd7_3_72, List.forall_mem_cons.2 ⟨subd7_3_73, List.forall_mem_cons.2 ⟨subd7_3_74, List.forall_mem_cons.2 ⟨subd7_3_75, List.forall_mem_cons.2 ⟨subd7_3_76, List.forall_mem_cons.2 ⟨subd7_3_77, List.forall_mem_cons.2 ⟨subd7_3_78, List.forall_mem_cons.2 ⟨subd7_3_79, List.forall_mem_cons.2 ⟨subd7_3_80, List.forall_mem_cons.2 ⟨subd7_3_81, List.forall_mem_cons.2 ⟨subd7_3_82, List.forall_mem_cons.2 ⟨subd7_3_83, List.forall_mem_cons.2 ⟨subd7_3_84, List.forall_mem_cons.2 ⟨subd7_3_85, List.forall_mem_cons.2 ⟨subd7_3_86, List.forall_mem_cons.2 ⟨subd7_3_87, List.forall_mem_cons.2 ⟨subd7_3_88, List.forall_mem_cons.2 ⟨subd7_3_89, List.forall_mem_cons.2 ⟨subd7_3_90, List.forall_mem_cons.2 ⟨subd7_3_91, List.forall_mem_cons.2 ⟨subd7_3_92, List.forall_mem_cons.2 ⟨subd7_3_93, List.forall_mem_cons.2 ⟨subd7_3_94, List.forall_mem_cons.2 ⟨subd7_3_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_96 : subd7_3 [1, 0, -3] = true := by decide +kernel
theorem subd7_3_97 : subd7_3 [1, 0, -2] = true := by decide +kernel
theorem subd7_3_98 : subd7_3 [1, 0, -1] = true := by decide +kernel
theorem subd7_3_99 : subd7_3 [1, 0, 0] = true := by decide +kernel
theorem subd7_3_100 : subd7_3 [1, 0, 1] = true := by decide +kernel
theorem subd7_3_101 : subd7_3 [1, 0, 2] = true := by decide +kernel
theorem subd7_3_102 : subd7_3 [1, 0, 3] = true := by decide +kernel
theorem subd7_3_103 : subd7_3 [1, 0, 4] = true := by decide +kernel
theorem subd7_3_104 : subd7_3 [1, 0, 5] = true := by decide +kernel
theorem subd7_3_105 : subd7_3 [1, 0, 6] = true := by decide +kernel
theorem subd7_3_106 : subd7_3 [1, 0, 7] = true := by decide +kernel
theorem subd7_3_107 : subd7_3 [1, 1, -8] = true := by decide +kernel
theorem subd7_3_108 : subd7_3 [1, 1, -7] = true := by decide +kernel
theorem subd7_3_109 : subd7_3 [1, 1, -6] = true := by decide +kernel
theorem subd7_3_110 : subd7_3 [1, 1, -5] = true := by decide +kernel
theorem subd7_3_111 : subd7_3 [1, 1, -4] = true := by decide +kernel
theorem subd7_3_112 : subd7_3 [1, 1, -3] = true := by decide +kernel
theorem subd7_3_113 : subd7_3 [1, 1, -2] = true := by decide +kernel
theorem subd7_3_114 : subd7_3 [1, 1, -1] = true := by decide +kernel
theorem subd7_3_115 : subd7_3 [1, 1, 0] = true := by decide +kernel
theorem subd7_3_116 : subd7_3 [1, 1, 1] = true := by decide +kernel
theorem subd7_3_117 : subd7_3 [1, 1, 2] = true := by decide +kernel
theorem subd7_3_118 : subd7_3 [1, 1, 3] = true := by decide +kernel
theorem subd7_3_119 : subd7_3 [1, 1, 4] = true := by decide +kernel
theorem subd7_3_120 : subd7_3 [1, 1, 5] = true := by decide +kernel
theorem subd7_3_121 : subd7_3 [1, 1, 6] = true := by decide +kernel
theorem subd7_3_122 : subd7_3 [1, 1, 7] = true := by decide +kernel
theorem subd7_3_123 : subd7_3 [1, 2] = true := by decide +kernel
theorem subd7_3_124 : subd7_3 [2] = true := by decide +kernel
theorem sbd7_3_3 : ∀ q ∈ blkd7_3_3, subd7_3 q = true := by
  unfold blkd7_3_3
  exact List.forall_mem_cons.2 ⟨subd7_3_96, List.forall_mem_cons.2 ⟨subd7_3_97, List.forall_mem_cons.2 ⟨subd7_3_98, List.forall_mem_cons.2 ⟨subd7_3_99, List.forall_mem_cons.2 ⟨subd7_3_100, List.forall_mem_cons.2 ⟨subd7_3_101, List.forall_mem_cons.2 ⟨subd7_3_102, List.forall_mem_cons.2 ⟨subd7_3_103, List.forall_mem_cons.2 ⟨subd7_3_104, List.forall_mem_cons.2 ⟨subd7_3_105, List.forall_mem_cons.2 ⟨subd7_3_106, List.forall_mem_cons.2 ⟨subd7_3_107, List.forall_mem_cons.2 ⟨subd7_3_108, List.forall_mem_cons.2 ⟨subd7_3_109, List.forall_mem_cons.2 ⟨subd7_3_110, List.forall_mem_cons.2 ⟨subd7_3_111, List.forall_mem_cons.2 ⟨subd7_3_112, List.forall_mem_cons.2 ⟨subd7_3_113, List.forall_mem_cons.2 ⟨subd7_3_114, List.forall_mem_cons.2 ⟨subd7_3_115, List.forall_mem_cons.2 ⟨subd7_3_116, List.forall_mem_cons.2 ⟨subd7_3_117, List.forall_mem_cons.2 ⟨subd7_3_118, List.forall_mem_cons.2 ⟨subd7_3_119, List.forall_mem_cons.2 ⟨subd7_3_120, List.forall_mem_cons.2 ⟨subd7_3_121, List.forall_mem_cons.2 ⟨subd7_3_122, List.forall_mem_cons.2 ⟨subd7_3_123, List.forall_mem_cons.2 ⟨subd7_3_124, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C141
