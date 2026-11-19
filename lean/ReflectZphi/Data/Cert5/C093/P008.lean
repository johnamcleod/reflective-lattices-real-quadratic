import ReflectZphi.Data.Cert5.C093.Base

namespace ReflectZphi.Data.Cert5.C093

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_0_480 : subd6_0 [-2, 4, 1] = true := by decide +kernel
theorem subd6_0_481 : subd6_0 [-2, 4, 2] = true := by decide +kernel
theorem subd6_0_482 : subd6_0 [-2, 4, 3] = true := by decide +kernel
theorem subd6_0_483 : subd6_0 [-2, 4, 4] = true := by decide +kernel
theorem subd6_0_484 : subd6_0 [-2, 4, 5] = true := by decide +kernel
theorem subd6_0_485 : subd6_0 [-2, 4, 6] = true := by decide +kernel
theorem subd6_0_486 : subd6_0 [-2, 5, -8] = true := by decide +kernel
theorem subd6_0_487 : subd6_0 [-2, 5, -7] = true := by decide +kernel
theorem subd6_0_488 : subd6_0 [-2, 5, -6] = true := by decide +kernel
theorem subd6_0_489 : subd6_0 [-2, 5, -5] = true := by decide +kernel
theorem subd6_0_490 : subd6_0 [-2, 5, -4] = true := by decide +kernel
theorem subd6_0_491 : subd6_0 [-2, 5, -3] = true := by decide +kernel
theorem subd6_0_492 : subd6_0 [-2, 5, -2] = true := by decide +kernel
theorem subd6_0_493 : subd6_0 [-2, 5, -1] = true := by decide +kernel
theorem subd6_0_494 : subd6_0 [-2, 5, 0] = true := by decide +kernel
theorem subd6_0_495 : subd6_0 [-2, 5, 1] = true := by decide +kernel
theorem subd6_0_496 : subd6_0 [-2, 5, 2] = true := by decide +kernel
theorem subd6_0_497 : subd6_0 [-2, 5, 3] = true := by decide +kernel
theorem subd6_0_498 : subd6_0 [-2, 5, 4] = true := by decide +kernel
theorem subd6_0_499 : subd6_0 [-2, 5, 5] = true := by decide +kernel
theorem subd6_0_500 : subd6_0 [-2, 5, 6] = true := by decide +kernel
theorem subd6_0_501 : subd6_0 [-2, 6] = true := by decide +kernel
theorem subd6_0_502 : subd6_0 [-2, 7] = true := by decide +kernel
theorem subd6_0_503 : subd6_0 [-2, 8] = true := by decide +kernel
theorem subd6_0_504 : subd6_0 [-1, -8] = true := by decide +kernel
theorem subd6_0_505 : subd6_0 [-1, -7] = true := by decide +kernel
theorem subd6_0_506 : subd6_0 [-1, -6] = true := by decide +kernel
theorem subd6_0_507 : subd6_0 [-1, -5, -6] = true := by decide +kernel
theorem subd6_0_508 : subd6_0 [-1, -5, -5] = true := by decide +kernel
theorem subd6_0_509 : subd6_0 [-1, -5, -4] = true := by decide +kernel
theorem subd6_0_510 : subd6_0 [-1, -5, -3] = true := by decide +kernel
theorem subd6_0_511 : subd6_0 [-1, -5, -2] = true := by decide +kernel
theorem sbd6_0_15 : ∀ q ∈ blkd6_0_15, subd6_0 q = true := by
  unfold blkd6_0_15
  exact List.forall_mem_cons.2 ⟨subd6_0_480, List.forall_mem_cons.2 ⟨subd6_0_481, List.forall_mem_cons.2 ⟨subd6_0_482, List.forall_mem_cons.2 ⟨subd6_0_483, List.forall_mem_cons.2 ⟨subd6_0_484, List.forall_mem_cons.2 ⟨subd6_0_485, List.forall_mem_cons.2 ⟨subd6_0_486, List.forall_mem_cons.2 ⟨subd6_0_487, List.forall_mem_cons.2 ⟨subd6_0_488, List.forall_mem_cons.2 ⟨subd6_0_489, List.forall_mem_cons.2 ⟨subd6_0_490, List.forall_mem_cons.2 ⟨subd6_0_491, List.forall_mem_cons.2 ⟨subd6_0_492, List.forall_mem_cons.2 ⟨subd6_0_493, List.forall_mem_cons.2 ⟨subd6_0_494, List.forall_mem_cons.2 ⟨subd6_0_495, List.forall_mem_cons.2 ⟨subd6_0_496, List.forall_mem_cons.2 ⟨subd6_0_497, List.forall_mem_cons.2 ⟨subd6_0_498, List.forall_mem_cons.2 ⟨subd6_0_499, List.forall_mem_cons.2 ⟨subd6_0_500, List.forall_mem_cons.2 ⟨subd6_0_501, List.forall_mem_cons.2 ⟨subd6_0_502, List.forall_mem_cons.2 ⟨subd6_0_503, List.forall_mem_cons.2 ⟨subd6_0_504, List.forall_mem_cons.2 ⟨subd6_0_505, List.forall_mem_cons.2 ⟨subd6_0_506, List.forall_mem_cons.2 ⟨subd6_0_507, List.forall_mem_cons.2 ⟨subd6_0_508, List.forall_mem_cons.2 ⟨subd6_0_509, List.forall_mem_cons.2 ⟨subd6_0_510, List.forall_mem_cons.2 ⟨subd6_0_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_512 : subd6_0 [-1, -5, -1] = true := by decide +kernel
theorem subd6_0_513 : subd6_0 [-1, -5, 0] = true := by decide +kernel
theorem subd6_0_514 : subd6_0 [-1, -5, 1] = true := by decide +kernel
theorem subd6_0_515 : subd6_0 [-1, -5, 2] = true := by decide +kernel
theorem subd6_0_516 : subd6_0 [-1, -5, 3] = true := by decide +kernel
theorem subd6_0_517 : subd6_0 [-1, -5, 4] = true := by decide +kernel
theorem subd6_0_518 : subd6_0 [-1, -5, 5] = true := by decide +kernel
theorem subd6_0_519 : subd6_0 [-1, -5, 6] = true := by decide +kernel
theorem subd6_0_520 : subd6_0 [-1, -5, 7] = true := by decide +kernel
theorem subd6_0_521 : subd6_0 [-1, -4, -7] = true := by decide +kernel
theorem subd6_0_522 : subd6_0 [-1, -4, -6] = true := by decide +kernel
theorem subd6_0_523 : subd6_0 [-1, -4, -5] = true := by decide +kernel
theorem subd6_0_524 : subd6_0 [-1, -4, -4] = true := by decide +kernel
theorem subd6_0_525 : subd6_0 [-1, -4, -3] = true := by decide +kernel
theorem subd6_0_526 : subd6_0 [-1, -4, -2] = true := by decide +kernel
theorem subd6_0_527 : subd6_0 [-1, -4, -1] = true := by decide +kernel
theorem subd6_0_528 : subd6_0 [-1, -4, 0] = true := by decide +kernel
theorem subd6_0_529 : subd6_0 [-1, -4, 1] = true := by decide +kernel
theorem subd6_0_530 : subd6_0 [-1, -4, 2] = true := by decide +kernel
theorem subd6_0_531 : subd6_0 [-1, -4, 3] = true := by decide +kernel
theorem subd6_0_532 : subd6_0 [-1, -4, 4] = true := by decide +kernel
theorem subd6_0_533 : subd6_0 [-1, -4, 5] = true := by decide +kernel
theorem subd6_0_534 : subd6_0 [-1, -4, 6] = true := by decide +kernel
theorem subd6_0_535 : subd6_0 [-1, -4, 7] = true := by decide +kernel
theorem subd6_0_536 : subd6_0 [-1, -3, -8] = true := by decide +kernel
theorem subd6_0_537 : subd6_0 [-1, -3, -7] = true := by decide +kernel
theorem subd6_0_538 : subd6_0 [-1, -3, -6] = true := by decide +kernel
theorem subd6_0_539 : subd6_0 [-1, -3, -5] = true := by decide +kernel
theorem subd6_0_540 : subd6_0 [-1, -3, -4] = true := by decide +kernel
theorem subd6_0_541 : subd6_0 [-1, -3, -3] = true := by decide +kernel
theorem subd6_0_542 : subd6_0 [-1, -3, -2] = true := by decide +kernel
theorem subd6_0_543 : subd6_0 [-1, -3, -1] = true := by decide +kernel
theorem sbd6_0_16 : ∀ q ∈ blkd6_0_16, subd6_0 q = true := by
  unfold blkd6_0_16
  exact List.forall_mem_cons.2 ⟨subd6_0_512, List.forall_mem_cons.2 ⟨subd6_0_513, List.forall_mem_cons.2 ⟨subd6_0_514, List.forall_mem_cons.2 ⟨subd6_0_515, List.forall_mem_cons.2 ⟨subd6_0_516, List.forall_mem_cons.2 ⟨subd6_0_517, List.forall_mem_cons.2 ⟨subd6_0_518, List.forall_mem_cons.2 ⟨subd6_0_519, List.forall_mem_cons.2 ⟨subd6_0_520, List.forall_mem_cons.2 ⟨subd6_0_521, List.forall_mem_cons.2 ⟨subd6_0_522, List.forall_mem_cons.2 ⟨subd6_0_523, List.forall_mem_cons.2 ⟨subd6_0_524, List.forall_mem_cons.2 ⟨subd6_0_525, List.forall_mem_cons.2 ⟨subd6_0_526, List.forall_mem_cons.2 ⟨subd6_0_527, List.forall_mem_cons.2 ⟨subd6_0_528, List.forall_mem_cons.2 ⟨subd6_0_529, List.forall_mem_cons.2 ⟨subd6_0_530, List.forall_mem_cons.2 ⟨subd6_0_531, List.forall_mem_cons.2 ⟨subd6_0_532, List.forall_mem_cons.2 ⟨subd6_0_533, List.forall_mem_cons.2 ⟨subd6_0_534, List.forall_mem_cons.2 ⟨subd6_0_535, List.forall_mem_cons.2 ⟨subd6_0_536, List.forall_mem_cons.2 ⟨subd6_0_537, List.forall_mem_cons.2 ⟨subd6_0_538, List.forall_mem_cons.2 ⟨subd6_0_539, List.forall_mem_cons.2 ⟨subd6_0_540, List.forall_mem_cons.2 ⟨subd6_0_541, List.forall_mem_cons.2 ⟨subd6_0_542, List.forall_mem_cons.2 ⟨subd6_0_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_544 : subd6_0 [-1, -3, 0] = true := by decide +kernel
theorem subd6_0_545 : subd6_0 [-1, -3, 1] = true := by decide +kernel
theorem subd6_0_546 : subd6_0 [-1, -3, 2] = true := by decide +kernel
theorem subd6_0_547 : subd6_0 [-1, -3, 3] = true := by decide +kernel
theorem subd6_0_548 : subd6_0 [-1, -3, 4] = true := by decide +kernel
theorem subd6_0_549 : subd6_0 [-1, -3, 5] = true := by decide +kernel
theorem subd6_0_550 : subd6_0 [-1, -3, 6] = true := by decide +kernel
theorem subd6_0_551 : subd6_0 [-1, -3, 7] = true := by decide +kernel
theorem subd6_0_552 : subd6_0 [-1, -3, 8] = true := by decide +kernel
theorem subd6_0_553 : subd6_0 [-1, -2, -8] = true := by decide +kernel
theorem subd6_0_554 : subd6_0 [-1, -2, -7] = true := by decide +kernel
theorem subd6_0_555 : subd6_0 [-1, -2, -6] = true := by decide +kernel
theorem subd6_0_556 : subd6_0 [-1, -2, -5] = true := by decide +kernel
theorem subd6_0_557 : subd6_0 [-1, -2, -4] = true := by decide +kernel
theorem subd6_0_558 : subd6_0 [-1, -2, -3] = true := by decide +kernel
theorem subd6_0_559 : subd6_0 [-1, -2, -2] = true := by decide +kernel
theorem subd6_0_560 : subd6_0 [-1, -2, -1] = true := by decide +kernel
theorem subd6_0_561 : subd6_0 [-1, -2, 0] = true := by decide +kernel
theorem subd6_0_562 : subd6_0 [-1, -2, 1] = true := by decide +kernel
theorem subd6_0_563 : subd6_0 [-1, -2, 2] = true := by decide +kernel
theorem subd6_0_564 : subd6_0 [-1, -2, 3] = true := by decide +kernel
theorem subd6_0_565 : subd6_0 [-1, -2, 4] = true := by decide +kernel
theorem subd6_0_566 : subd6_0 [-1, -2, 5] = true := by decide +kernel
theorem subd6_0_567 : subd6_0 [-1, -2, 6] = true := by decide +kernel
theorem subd6_0_568 : subd6_0 [-1, -2, 7] = true := by decide +kernel
theorem subd6_0_569 : subd6_0 [-1, -2, 8] = true := by decide +kernel
theorem subd6_0_570 : subd6_0 [-1, -1, -9] = true := by decide +kernel
theorem subd6_0_571 : subd6_0 [-1, -1, -8] = true := by decide +kernel
theorem subd6_0_572 : subd6_0 [-1, -1, -7] = true := by decide +kernel
theorem subd6_0_573 : subd6_0 [-1, -1, -6] = true := by decide +kernel
theorem subd6_0_574 : subd6_0 [-1, -1, -5] = true := by decide +kernel
theorem subd6_0_575 : subd6_0 [-1, -1, -4] = true := by decide +kernel
theorem sbd6_0_17 : ∀ q ∈ blkd6_0_17, subd6_0 q = true := by
  unfold blkd6_0_17
  exact List.forall_mem_cons.2 ⟨subd6_0_544, List.forall_mem_cons.2 ⟨subd6_0_545, List.forall_mem_cons.2 ⟨subd6_0_546, List.forall_mem_cons.2 ⟨subd6_0_547, List.forall_mem_cons.2 ⟨subd6_0_548, List.forall_mem_cons.2 ⟨subd6_0_549, List.forall_mem_cons.2 ⟨subd6_0_550, List.forall_mem_cons.2 ⟨subd6_0_551, List.forall_mem_cons.2 ⟨subd6_0_552, List.forall_mem_cons.2 ⟨subd6_0_553, List.forall_mem_cons.2 ⟨subd6_0_554, List.forall_mem_cons.2 ⟨subd6_0_555, List.forall_mem_cons.2 ⟨subd6_0_556, List.forall_mem_cons.2 ⟨subd6_0_557, List.forall_mem_cons.2 ⟨subd6_0_558, List.forall_mem_cons.2 ⟨subd6_0_559, List.forall_mem_cons.2 ⟨subd6_0_560, List.forall_mem_cons.2 ⟨subd6_0_561, List.forall_mem_cons.2 ⟨subd6_0_562, List.forall_mem_cons.2 ⟨subd6_0_563, List.forall_mem_cons.2 ⟨subd6_0_564, List.forall_mem_cons.2 ⟨subd6_0_565, List.forall_mem_cons.2 ⟨subd6_0_566, List.forall_mem_cons.2 ⟨subd6_0_567, List.forall_mem_cons.2 ⟨subd6_0_568, List.forall_mem_cons.2 ⟨subd6_0_569, List.forall_mem_cons.2 ⟨subd6_0_570, List.forall_mem_cons.2 ⟨subd6_0_571, List.forall_mem_cons.2 ⟨subd6_0_572, List.forall_mem_cons.2 ⟨subd6_0_573, List.forall_mem_cons.2 ⟨subd6_0_574, List.forall_mem_cons.2 ⟨subd6_0_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_576 : subd6_0 [-1, -1, -3] = true := by decide +kernel
theorem subd6_0_577 : subd6_0 [-1, -1, -2] = true := by decide +kernel
theorem subd6_0_578 : subd6_0 [-1, -1, -1] = true := by decide +kernel
theorem subd6_0_579 : subd6_0 [-1, -1, 0] = true := by decide +kernel
theorem subd6_0_580 : subd6_0 [-1, -1, 1] = true := by decide +kernel
theorem subd6_0_581 : subd6_0 [-1, -1, 2] = true := by decide +kernel
theorem subd6_0_582 : subd6_0 [-1, -1, 3] = true := by decide +kernel
theorem subd6_0_583 : subd6_0 [-1, -1, 4] = true := by decide +kernel
theorem subd6_0_584 : subd6_0 [-1, -1, 5] = true := by decide +kernel
theorem subd6_0_585 : subd6_0 [-1, -1, 6] = true := by decide +kernel
theorem subd6_0_586 : subd6_0 [-1, -1, 7] = true := by decide +kernel
theorem subd6_0_587 : subd6_0 [-1, -1, 8] = true := by decide +kernel
theorem subd6_0_588 : subd6_0 [-1, 0, -9] = true := by decide +kernel
theorem subd6_0_589 : subd6_0 [-1, 0, -8] = true := by decide +kernel
theorem subd6_0_590 : subd6_0 [-1, 0, -7] = true := by decide +kernel
theorem subd6_0_591 : subd6_0 [-1, 0, -6] = true := by decide +kernel
theorem subd6_0_592 : subd6_0 [-1, 0, -5] = true := by decide +kernel
theorem subd6_0_593 : subd6_0 [-1, 0, -4] = true := by decide +kernel
theorem subd6_0_594 : subd6_0 [-1, 0, -3] = true := by decide +kernel
theorem subd6_0_595 : subd6_0 [-1, 0, -2] = true := by decide +kernel
theorem subd6_0_596 : subd6_0 [-1, 0, -1] = true := by decide +kernel
theorem subd6_0_597 : subd6_0 [-1, 0, 0] = true := by decide +kernel
theorem subd6_0_598 : subd6_0 [-1, 0, 1] = true := by decide +kernel
theorem subd6_0_599 : subd6_0 [-1, 0, 2] = true := by decide +kernel
theorem subd6_0_600 : subd6_0 [-1, 0, 3] = true := by decide +kernel
theorem subd6_0_601 : subd6_0 [-1, 0, 4] = true := by decide +kernel
theorem subd6_0_602 : subd6_0 [-1, 0, 5] = true := by decide +kernel
theorem subd6_0_603 : subd6_0 [-1, 0, 6] = true := by decide +kernel
theorem subd6_0_604 : subd6_0 [-1, 0, 7] = true := by decide +kernel
theorem subd6_0_605 : subd6_0 [-1, 0, 8] = true := by decide +kernel
theorem subd6_0_606 : subd6_0 [-1, 1, -9] = true := by decide +kernel
theorem subd6_0_607 : subd6_0 [-1, 1, -8] = true := by decide +kernel
theorem sbd6_0_18 : ∀ q ∈ blkd6_0_18, subd6_0 q = true := by
  unfold blkd6_0_18
  exact List.forall_mem_cons.2 ⟨subd6_0_576, List.forall_mem_cons.2 ⟨subd6_0_577, List.forall_mem_cons.2 ⟨subd6_0_578, List.forall_mem_cons.2 ⟨subd6_0_579, List.forall_mem_cons.2 ⟨subd6_0_580, List.forall_mem_cons.2 ⟨subd6_0_581, List.forall_mem_cons.2 ⟨subd6_0_582, List.forall_mem_cons.2 ⟨subd6_0_583, List.forall_mem_cons.2 ⟨subd6_0_584, List.forall_mem_cons.2 ⟨subd6_0_585, List.forall_mem_cons.2 ⟨subd6_0_586, List.forall_mem_cons.2 ⟨subd6_0_587, List.forall_mem_cons.2 ⟨subd6_0_588, List.forall_mem_cons.2 ⟨subd6_0_589, List.forall_mem_cons.2 ⟨subd6_0_590, List.forall_mem_cons.2 ⟨subd6_0_591, List.forall_mem_cons.2 ⟨subd6_0_592, List.forall_mem_cons.2 ⟨subd6_0_593, List.forall_mem_cons.2 ⟨subd6_0_594, List.forall_mem_cons.2 ⟨subd6_0_595, List.forall_mem_cons.2 ⟨subd6_0_596, List.forall_mem_cons.2 ⟨subd6_0_597, List.forall_mem_cons.2 ⟨subd6_0_598, List.forall_mem_cons.2 ⟨subd6_0_599, List.forall_mem_cons.2 ⟨subd6_0_600, List.forall_mem_cons.2 ⟨subd6_0_601, List.forall_mem_cons.2 ⟨subd6_0_602, List.forall_mem_cons.2 ⟨subd6_0_603, List.forall_mem_cons.2 ⟨subd6_0_604, List.forall_mem_cons.2 ⟨subd6_0_605, List.forall_mem_cons.2 ⟨subd6_0_606, List.forall_mem_cons.2 ⟨subd6_0_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_608 : subd6_0 [-1, 1, -7] = true := by decide +kernel
theorem subd6_0_609 : subd6_0 [-1, 1, -6] = true := by decide +kernel
theorem subd6_0_610 : subd6_0 [-1, 1, -5] = true := by decide +kernel
theorem subd6_0_611 : subd6_0 [-1, 1, -4] = true := by decide +kernel
theorem subd6_0_612 : subd6_0 [-1, 1, -3] = true := by decide +kernel
theorem subd6_0_613 : subd6_0 [-1, 1, -2] = true := by decide +kernel
theorem subd6_0_614 : subd6_0 [-1, 1, -1] = true := by decide +kernel
theorem subd6_0_615 : subd6_0 [-1, 1, 0] = true := by decide +kernel
theorem subd6_0_616 : subd6_0 [-1, 1, 1] = true := by decide +kernel
theorem subd6_0_617 : subd6_0 [-1, 1, 2] = true := by decide +kernel
theorem subd6_0_618 : subd6_0 [-1, 1, 3] = true := by decide +kernel
theorem subd6_0_619 : subd6_0 [-1, 1, 4] = true := by decide +kernel
theorem subd6_0_620 : subd6_0 [-1, 1, 5] = true := by decide +kernel
theorem subd6_0_621 : subd6_0 [-1, 1, 6] = true := by decide +kernel
theorem subd6_0_622 : subd6_0 [-1, 1, 7] = true := by decide +kernel
theorem subd6_0_623 : subd6_0 [-1, 1, 8] = true := by decide +kernel
theorem subd6_0_624 : subd6_0 [-1, 2, -9] = true := by decide +kernel
theorem subd6_0_625 : subd6_0 [-1, 2, -8] = true := by decide +kernel
theorem subd6_0_626 : subd6_0 [-1, 2, -7] = true := by decide +kernel
theorem subd6_0_627 : subd6_0 [-1, 2, -6] = true := by decide +kernel
theorem subd6_0_628 : subd6_0 [-1, 2, -5] = true := by decide +kernel
theorem subd6_0_629 : subd6_0 [-1, 2, -4] = true := by decide +kernel
theorem subd6_0_630 : subd6_0 [-1, 2, -3] = true := by decide +kernel
theorem subd6_0_631 : subd6_0 [-1, 2, -2] = true := by decide +kernel
theorem subd6_0_632 : subd6_0 [-1, 2, -1] = true := by decide +kernel
theorem subd6_0_633 : subd6_0 [-1, 2, 0] = true := by decide +kernel
theorem subd6_0_634 : subd6_0 [-1, 2, 1] = true := by decide +kernel
theorem subd6_0_635 : subd6_0 [-1, 2, 2] = true := by decide +kernel
theorem subd6_0_636 : subd6_0 [-1, 2, 3] = true := by decide +kernel
theorem subd6_0_637 : subd6_0 [-1, 2, 4] = true := by decide +kernel
theorem subd6_0_638 : subd6_0 [-1, 2, 5] = true := by decide +kernel
theorem subd6_0_639 : subd6_0 [-1, 2, 6] = true := by decide +kernel
theorem sbd6_0_19 : ∀ q ∈ blkd6_0_19, subd6_0 q = true := by
  unfold blkd6_0_19
  exact List.forall_mem_cons.2 ⟨subd6_0_608, List.forall_mem_cons.2 ⟨subd6_0_609, List.forall_mem_cons.2 ⟨subd6_0_610, List.forall_mem_cons.2 ⟨subd6_0_611, List.forall_mem_cons.2 ⟨subd6_0_612, List.forall_mem_cons.2 ⟨subd6_0_613, List.forall_mem_cons.2 ⟨subd6_0_614, List.forall_mem_cons.2 ⟨subd6_0_615, List.forall_mem_cons.2 ⟨subd6_0_616, List.forall_mem_cons.2 ⟨subd6_0_617, List.forall_mem_cons.2 ⟨subd6_0_618, List.forall_mem_cons.2 ⟨subd6_0_619, List.forall_mem_cons.2 ⟨subd6_0_620, List.forall_mem_cons.2 ⟨subd6_0_621, List.forall_mem_cons.2 ⟨subd6_0_622, List.forall_mem_cons.2 ⟨subd6_0_623, List.forall_mem_cons.2 ⟨subd6_0_624, List.forall_mem_cons.2 ⟨subd6_0_625, List.forall_mem_cons.2 ⟨subd6_0_626, List.forall_mem_cons.2 ⟨subd6_0_627, List.forall_mem_cons.2 ⟨subd6_0_628, List.forall_mem_cons.2 ⟨subd6_0_629, List.forall_mem_cons.2 ⟨subd6_0_630, List.forall_mem_cons.2 ⟨subd6_0_631, List.forall_mem_cons.2 ⟨subd6_0_632, List.forall_mem_cons.2 ⟨subd6_0_633, List.forall_mem_cons.2 ⟨subd6_0_634, List.forall_mem_cons.2 ⟨subd6_0_635, List.forall_mem_cons.2 ⟨subd6_0_636, List.forall_mem_cons.2 ⟨subd6_0_637, List.forall_mem_cons.2 ⟨subd6_0_638, List.forall_mem_cons.2 ⟨subd6_0_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_640 : subd6_0 [-1, 2, 7] = true := by decide +kernel
theorem subd6_0_641 : subd6_0 [-1, 2, 8] = true := by decide +kernel
theorem subd6_0_642 : subd6_0 [-1, 3, -9] = true := by decide +kernel
theorem subd6_0_643 : subd6_0 [-1, 3, -8] = true := by decide +kernel
theorem subd6_0_644 : subd6_0 [-1, 3, -7] = true := by decide +kernel
theorem subd6_0_645 : subd6_0 [-1, 3, -6] = true := by decide +kernel
theorem subd6_0_646 : subd6_0 [-1, 3, -5] = true := by decide +kernel
theorem subd6_0_647 : subd6_0 [-1, 3, -4] = true := by decide +kernel
theorem subd6_0_648 : subd6_0 [-1, 3, -3] = true := by decide +kernel
theorem subd6_0_649 : subd6_0 [-1, 3, -2] = true := by decide +kernel
theorem subd6_0_650 : subd6_0 [-1, 3, -1] = true := by decide +kernel
theorem subd6_0_651 : subd6_0 [-1, 3, 0] = true := by decide +kernel
theorem subd6_0_652 : subd6_0 [-1, 3, 1] = true := by decide +kernel
theorem subd6_0_653 : subd6_0 [-1, 3, 2] = true := by decide +kernel
theorem subd6_0_654 : subd6_0 [-1, 3, 3] = true := by decide +kernel
theorem subd6_0_655 : subd6_0 [-1, 3, 4] = true := by decide +kernel
theorem subd6_0_656 : subd6_0 [-1, 3, 5] = true := by decide +kernel
theorem subd6_0_657 : subd6_0 [-1, 3, 6] = true := by decide +kernel
theorem subd6_0_658 : subd6_0 [-1, 3, 7] = true := by decide +kernel
theorem subd6_0_659 : subd6_0 [-1, 4, -8] = true := by decide +kernel
theorem subd6_0_660 : subd6_0 [-1, 4, -7] = true := by decide +kernel
theorem subd6_0_661 : subd6_0 [-1, 4, -6] = true := by decide +kernel
theorem subd6_0_662 : subd6_0 [-1, 4, -5] = true := by decide +kernel
theorem subd6_0_663 : subd6_0 [-1, 4, -4] = true := by decide +kernel
theorem subd6_0_664 : subd6_0 [-1, 4, -3] = true := by decide +kernel
theorem subd6_0_665 : subd6_0 [-1, 4, -2] = true := by decide +kernel
theorem subd6_0_666 : subd6_0 [-1, 4, -1] = true := by decide +kernel
theorem subd6_0_667 : subd6_0 [-1, 4, 0] = true := by decide +kernel
theorem subd6_0_668 : subd6_0 [-1, 4, 1] = true := by decide +kernel
theorem subd6_0_669 : subd6_0 [-1, 4, 2] = true := by decide +kernel
theorem subd6_0_670 : subd6_0 [-1, 4, 3] = true := by decide +kernel
theorem subd6_0_671 : subd6_0 [-1, 4, 4] = true := by decide +kernel
theorem sbd6_0_20 : ∀ q ∈ blkd6_0_20, subd6_0 q = true := by
  unfold blkd6_0_20
  exact List.forall_mem_cons.2 ⟨subd6_0_640, List.forall_mem_cons.2 ⟨subd6_0_641, List.forall_mem_cons.2 ⟨subd6_0_642, List.forall_mem_cons.2 ⟨subd6_0_643, List.forall_mem_cons.2 ⟨subd6_0_644, List.forall_mem_cons.2 ⟨subd6_0_645, List.forall_mem_cons.2 ⟨subd6_0_646, List.forall_mem_cons.2 ⟨subd6_0_647, List.forall_mem_cons.2 ⟨subd6_0_648, List.forall_mem_cons.2 ⟨subd6_0_649, List.forall_mem_cons.2 ⟨subd6_0_650, List.forall_mem_cons.2 ⟨subd6_0_651, List.forall_mem_cons.2 ⟨subd6_0_652, List.forall_mem_cons.2 ⟨subd6_0_653, List.forall_mem_cons.2 ⟨subd6_0_654, List.forall_mem_cons.2 ⟨subd6_0_655, List.forall_mem_cons.2 ⟨subd6_0_656, List.forall_mem_cons.2 ⟨subd6_0_657, List.forall_mem_cons.2 ⟨subd6_0_658, List.forall_mem_cons.2 ⟨subd6_0_659, List.forall_mem_cons.2 ⟨subd6_0_660, List.forall_mem_cons.2 ⟨subd6_0_661, List.forall_mem_cons.2 ⟨subd6_0_662, List.forall_mem_cons.2 ⟨subd6_0_663, List.forall_mem_cons.2 ⟨subd6_0_664, List.forall_mem_cons.2 ⟨subd6_0_665, List.forall_mem_cons.2 ⟨subd6_0_666, List.forall_mem_cons.2 ⟨subd6_0_667, List.forall_mem_cons.2 ⟨subd6_0_668, List.forall_mem_cons.2 ⟨subd6_0_669, List.forall_mem_cons.2 ⟨subd6_0_670, List.forall_mem_cons.2 ⟨subd6_0_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_672 : subd6_0 [-1, 4, 5] = true := by decide +kernel
theorem subd6_0_673 : subd6_0 [-1, 4, 6] = true := by decide +kernel
theorem subd6_0_674 : subd6_0 [-1, 5, -8] = true := by decide +kernel
theorem subd6_0_675 : subd6_0 [-1, 5, -7] = true := by decide +kernel
theorem subd6_0_676 : subd6_0 [-1, 5, -6] = true := by decide +kernel
theorem subd6_0_677 : subd6_0 [-1, 5, -5] = true := by decide +kernel
theorem subd6_0_678 : subd6_0 [-1, 5, -4] = true := by decide +kernel
theorem subd6_0_679 : subd6_0 [-1, 5, -3] = true := by decide +kernel
theorem subd6_0_680 : subd6_0 [-1, 5, -2] = true := by decide +kernel
theorem subd6_0_681 : subd6_0 [-1, 5, -1] = true := by decide +kernel
theorem subd6_0_682 : subd6_0 [-1, 5, 0] = true := by decide +kernel
theorem subd6_0_683 : subd6_0 [-1, 5, 1] = true := by decide +kernel
theorem subd6_0_684 : subd6_0 [-1, 5, 2] = true := by decide +kernel
theorem subd6_0_685 : subd6_0 [-1, 5, 3] = true := by decide +kernel
theorem subd6_0_686 : subd6_0 [-1, 5, 4] = true := by decide +kernel
theorem subd6_0_687 : subd6_0 [-1, 5, 5] = true := by decide +kernel
theorem subd6_0_688 : subd6_0 [-1, 5, 6] = true := by decide +kernel
theorem subd6_0_689 : subd6_0 [-1, 6] = true := by decide +kernel
theorem subd6_0_690 : subd6_0 [-1, 7] = true := by decide +kernel
theorem subd6_0_691 : subd6_0 [-1, 8] = true := by decide +kernel
theorem subd6_0_692 : subd6_0 [0, -9] = true := by decide +kernel
theorem subd6_0_693 : subd6_0 [0, -8] = true := by decide +kernel
theorem subd6_0_694 : subd6_0 [0, -7] = true := by decide +kernel
theorem subd6_0_695 : subd6_0 [0, -6] = true := by decide +kernel
theorem subd6_0_696 : subd6_0 [0, -5, -7] = true := by decide +kernel
theorem subd6_0_697 : subd6_0 [0, -5, -6] = true := by decide +kernel
theorem subd6_0_698 : subd6_0 [0, -5, -5] = true := by decide +kernel
theorem subd6_0_699 : subd6_0 [0, -5, -4] = true := by decide +kernel
theorem subd6_0_700 : subd6_0 [0, -5, -3] = true := by decide +kernel
theorem subd6_0_701 : subd6_0 [0, -5, -2] = true := by decide +kernel
theorem subd6_0_702 : subd6_0 [0, -5, -1] = true := by decide +kernel
theorem subd6_0_703 : subd6_0 [0, -5, 0] = true := by decide +kernel
theorem sbd6_0_21 : ∀ q ∈ blkd6_0_21, subd6_0 q = true := by
  unfold blkd6_0_21
  exact List.forall_mem_cons.2 ⟨subd6_0_672, List.forall_mem_cons.2 ⟨subd6_0_673, List.forall_mem_cons.2 ⟨subd6_0_674, List.forall_mem_cons.2 ⟨subd6_0_675, List.forall_mem_cons.2 ⟨subd6_0_676, List.forall_mem_cons.2 ⟨subd6_0_677, List.forall_mem_cons.2 ⟨subd6_0_678, List.forall_mem_cons.2 ⟨subd6_0_679, List.forall_mem_cons.2 ⟨subd6_0_680, List.forall_mem_cons.2 ⟨subd6_0_681, List.forall_mem_cons.2 ⟨subd6_0_682, List.forall_mem_cons.2 ⟨subd6_0_683, List.forall_mem_cons.2 ⟨subd6_0_684, List.forall_mem_cons.2 ⟨subd6_0_685, List.forall_mem_cons.2 ⟨subd6_0_686, List.forall_mem_cons.2 ⟨subd6_0_687, List.forall_mem_cons.2 ⟨subd6_0_688, List.forall_mem_cons.2 ⟨subd6_0_689, List.forall_mem_cons.2 ⟨subd6_0_690, List.forall_mem_cons.2 ⟨subd6_0_691, List.forall_mem_cons.2 ⟨subd6_0_692, List.forall_mem_cons.2 ⟨subd6_0_693, List.forall_mem_cons.2 ⟨subd6_0_694, List.forall_mem_cons.2 ⟨subd6_0_695, List.forall_mem_cons.2 ⟨subd6_0_696, List.forall_mem_cons.2 ⟨subd6_0_697, List.forall_mem_cons.2 ⟨subd6_0_698, List.forall_mem_cons.2 ⟨subd6_0_699, List.forall_mem_cons.2 ⟨subd6_0_700, List.forall_mem_cons.2 ⟨subd6_0_701, List.forall_mem_cons.2 ⟨subd6_0_702, List.forall_mem_cons.2 ⟨subd6_0_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_704 : subd6_0 [0, -5, 1] = true := by decide +kernel
theorem subd6_0_705 : subd6_0 [0, -5, 2] = true := by decide +kernel
theorem subd6_0_706 : subd6_0 [0, -5, 3] = true := by decide +kernel
theorem subd6_0_707 : subd6_0 [0, -5, 4] = true := by decide +kernel
theorem subd6_0_708 : subd6_0 [0, -5, 5] = true := by decide +kernel
theorem subd6_0_709 : subd6_0 [0, -5, 6] = true := by decide +kernel
theorem subd6_0_710 : subd6_0 [0, -5, 7] = true := by decide +kernel
theorem subd6_0_711 : subd6_0 [0, -4, -7] = true := by decide +kernel
theorem subd6_0_712 : subd6_0 [0, -4, -6] = true := by decide +kernel
theorem subd6_0_713 : subd6_0 [0, -4, -5] = true := by decide +kernel
theorem subd6_0_714 : subd6_0 [0, -4, -4] = true := by decide +kernel
theorem subd6_0_715 : subd6_0 [0, -4, -3] = true := by decide +kernel
theorem subd6_0_716 : subd6_0 [0, -4, -2] = true := by decide +kernel
theorem subd6_0_717 : subd6_0 [0, -4, -1] = true := by decide +kernel
theorem subd6_0_718 : subd6_0 [0, -4, 0] = true := by decide +kernel
theorem subd6_0_719 : subd6_0 [0, -4, 1] = true := by decide +kernel
theorem subd6_0_720 : subd6_0 [0, -4, 2] = true := by decide +kernel
theorem subd6_0_721 : subd6_0 [0, -4, 3] = true := by decide +kernel
theorem subd6_0_722 : subd6_0 [0, -4, 4] = true := by decide +kernel
theorem subd6_0_723 : subd6_0 [0, -4, 5] = true := by decide +kernel
theorem subd6_0_724 : subd6_0 [0, -4, 6] = true := by decide +kernel
theorem subd6_0_725 : subd6_0 [0, -4, 7] = true := by decide +kernel
theorem subd6_0_726 : subd6_0 [0, -3, -8] = true := by decide +kernel
theorem subd6_0_727 : subd6_0 [0, -3, -7] = true := by decide +kernel
theorem subd6_0_728 : subd6_0 [0, -3, -6] = true := by decide +kernel
theorem subd6_0_729 : subd6_0 [0, -3, -5] = true := by decide +kernel
theorem subd6_0_730 : subd6_0 [0, -3, -4] = true := by decide +kernel
theorem subd6_0_731 : subd6_0 [0, -3, -3] = true := by decide +kernel
theorem subd6_0_732 : subd6_0 [0, -3, -2] = true := by decide +kernel
theorem subd6_0_733 : subd6_0 [0, -3, -1] = true := by decide +kernel
theorem subd6_0_734 : subd6_0 [0, -3, 0] = true := by decide +kernel
theorem subd6_0_735 : subd6_0 [0, -3, 1] = true := by decide +kernel
theorem sbd6_0_22 : ∀ q ∈ blkd6_0_22, subd6_0 q = true := by
  unfold blkd6_0_22
  exact List.forall_mem_cons.2 ⟨subd6_0_704, List.forall_mem_cons.2 ⟨subd6_0_705, List.forall_mem_cons.2 ⟨subd6_0_706, List.forall_mem_cons.2 ⟨subd6_0_707, List.forall_mem_cons.2 ⟨subd6_0_708, List.forall_mem_cons.2 ⟨subd6_0_709, List.forall_mem_cons.2 ⟨subd6_0_710, List.forall_mem_cons.2 ⟨subd6_0_711, List.forall_mem_cons.2 ⟨subd6_0_712, List.forall_mem_cons.2 ⟨subd6_0_713, List.forall_mem_cons.2 ⟨subd6_0_714, List.forall_mem_cons.2 ⟨subd6_0_715, List.forall_mem_cons.2 ⟨subd6_0_716, List.forall_mem_cons.2 ⟨subd6_0_717, List.forall_mem_cons.2 ⟨subd6_0_718, List.forall_mem_cons.2 ⟨subd6_0_719, List.forall_mem_cons.2 ⟨subd6_0_720, List.forall_mem_cons.2 ⟨subd6_0_721, List.forall_mem_cons.2 ⟨subd6_0_722, List.forall_mem_cons.2 ⟨subd6_0_723, List.forall_mem_cons.2 ⟨subd6_0_724, List.forall_mem_cons.2 ⟨subd6_0_725, List.forall_mem_cons.2 ⟨subd6_0_726, List.forall_mem_cons.2 ⟨subd6_0_727, List.forall_mem_cons.2 ⟨subd6_0_728, List.forall_mem_cons.2 ⟨subd6_0_729, List.forall_mem_cons.2 ⟨subd6_0_730, List.forall_mem_cons.2 ⟨subd6_0_731, List.forall_mem_cons.2 ⟨subd6_0_732, List.forall_mem_cons.2 ⟨subd6_0_733, List.forall_mem_cons.2 ⟨subd6_0_734, List.forall_mem_cons.2 ⟨subd6_0_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_736 : subd6_0 [0, -3, 2] = true := by decide +kernel
theorem subd6_0_737 : subd6_0 [0, -3, 3] = true := by decide +kernel
theorem subd6_0_738 : subd6_0 [0, -3, 4] = true := by decide +kernel
theorem subd6_0_739 : subd6_0 [0, -3, 5] = true := by decide +kernel
theorem subd6_0_740 : subd6_0 [0, -3, 6] = true := by decide +kernel
theorem subd6_0_741 : subd6_0 [0, -3, 7] = true := by decide +kernel
theorem subd6_0_742 : subd6_0 [0, -3, 8] = true := by decide +kernel
theorem subd6_0_743 : subd6_0 [0, -2, -9] = true := by decide +kernel
theorem subd6_0_744 : subd6_0 [0, -2, -8] = true := by decide +kernel
theorem subd6_0_745 : subd6_0 [0, -2, -7] = true := by decide +kernel
theorem subd6_0_746 : subd6_0 [0, -2, -6] = true := by decide +kernel
theorem subd6_0_747 : subd6_0 [0, -2, -5] = true := by decide +kernel
theorem subd6_0_748 : subd6_0 [0, -2, -4] = true := by decide +kernel
theorem subd6_0_749 : subd6_0 [0, -2, -3] = true := by decide +kernel
theorem subd6_0_750 : subd6_0 [0, -2, -2] = true := by decide +kernel
theorem subd6_0_751 : subd6_0 [0, -2, -1] = true := by decide +kernel
theorem subd6_0_752 : subd6_0 [0, -2, 0] = true := by decide +kernel
theorem subd6_0_753 : subd6_0 [0, -2, 1] = true := by decide +kernel
theorem subd6_0_754 : subd6_0 [0, -2, 2] = true := by decide +kernel
theorem subd6_0_755 : subd6_0 [0, -2, 3] = true := by decide +kernel
theorem subd6_0_756 : subd6_0 [0, -2, 4] = true := by decide +kernel
theorem subd6_0_757 : subd6_0 [0, -2, 5] = true := by decide +kernel
theorem subd6_0_758 : subd6_0 [0, -2, 6] = true := by decide +kernel
theorem subd6_0_759 : subd6_0 [0, -2, 7] = true := by decide +kernel
theorem subd6_0_760 : subd6_0 [0, -2, 8] = true := by decide +kernel
theorem subd6_0_761 : subd6_0 [0, -1, -9] = true := by decide +kernel
theorem subd6_0_762 : subd6_0 [0, -1, -8] = true := by decide +kernel
theorem subd6_0_763 : subd6_0 [0, -1, -7] = true := by decide +kernel
theorem subd6_0_764 : subd6_0 [0, -1, -6] = true := by decide +kernel
theorem subd6_0_765 : subd6_0 [0, -1, -5] = true := by decide +kernel
theorem subd6_0_766 : subd6_0 [0, -1, -4] = true := by decide +kernel
theorem subd6_0_767 : subd6_0 [0, -1, -3] = true := by decide +kernel
theorem sbd6_0_23 : ∀ q ∈ blkd6_0_23, subd6_0 q = true := by
  unfold blkd6_0_23
  exact List.forall_mem_cons.2 ⟨subd6_0_736, List.forall_mem_cons.2 ⟨subd6_0_737, List.forall_mem_cons.2 ⟨subd6_0_738, List.forall_mem_cons.2 ⟨subd6_0_739, List.forall_mem_cons.2 ⟨subd6_0_740, List.forall_mem_cons.2 ⟨subd6_0_741, List.forall_mem_cons.2 ⟨subd6_0_742, List.forall_mem_cons.2 ⟨subd6_0_743, List.forall_mem_cons.2 ⟨subd6_0_744, List.forall_mem_cons.2 ⟨subd6_0_745, List.forall_mem_cons.2 ⟨subd6_0_746, List.forall_mem_cons.2 ⟨subd6_0_747, List.forall_mem_cons.2 ⟨subd6_0_748, List.forall_mem_cons.2 ⟨subd6_0_749, List.forall_mem_cons.2 ⟨subd6_0_750, List.forall_mem_cons.2 ⟨subd6_0_751, List.forall_mem_cons.2 ⟨subd6_0_752, List.forall_mem_cons.2 ⟨subd6_0_753, List.forall_mem_cons.2 ⟨subd6_0_754, List.forall_mem_cons.2 ⟨subd6_0_755, List.forall_mem_cons.2 ⟨subd6_0_756, List.forall_mem_cons.2 ⟨subd6_0_757, List.forall_mem_cons.2 ⟨subd6_0_758, List.forall_mem_cons.2 ⟨subd6_0_759, List.forall_mem_cons.2 ⟨subd6_0_760, List.forall_mem_cons.2 ⟨subd6_0_761, List.forall_mem_cons.2 ⟨subd6_0_762, List.forall_mem_cons.2 ⟨subd6_0_763, List.forall_mem_cons.2 ⟨subd6_0_764, List.forall_mem_cons.2 ⟨subd6_0_765, List.forall_mem_cons.2 ⟨subd6_0_766, List.forall_mem_cons.2 ⟨subd6_0_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_768 : subd6_0 [0, -1, -2] = true := by decide +kernel
theorem subd6_0_769 : subd6_0 [0, -1, -1] = true := by decide +kernel
theorem subd6_0_770 : subd6_0 [0, -1, 0] = true := by decide +kernel
theorem subd6_0_771 : subd6_0 [0, -1, 1] = true := by decide +kernel
theorem subd6_0_772 : subd6_0 [0, -1, 2] = true := by decide +kernel
theorem subd6_0_773 : subd6_0 [0, -1, 3] = true := by decide +kernel
theorem subd6_0_774 : subd6_0 [0, -1, 4] = true := by decide +kernel
theorem subd6_0_775 : subd6_0 [0, -1, 5] = true := by decide +kernel
theorem subd6_0_776 : subd6_0 [0, -1, 6] = true := by decide +kernel
theorem subd6_0_777 : subd6_0 [0, -1, 7] = true := by decide +kernel
theorem subd6_0_778 : subd6_0 [0, -1, 8] = true := by decide +kernel
theorem subd6_0_779 : subd6_0 [0, 0, -9] = true := by decide +kernel
theorem subd6_0_780 : subd6_0 [0, 0, -8] = true := by decide +kernel
theorem subd6_0_781 : subd6_0 [0, 0, -7] = true := by decide +kernel
theorem subd6_0_782 : subd6_0 [0, 0, -6] = true := by decide +kernel
theorem subd6_0_783 : subd6_0 [0, 0, -5] = true := by decide +kernel
theorem subd6_0_784 : subd6_0 [0, 0, -4] = true := by decide +kernel
theorem subd6_0_785 : subd6_0 [0, 0, -3] = true := by decide +kernel
theorem subd6_0_786 : subd6_0 [0, 0, -2] = true := by decide +kernel
theorem subd6_0_787 : subd6_0 [0, 0, -1] = true := by decide +kernel
theorem subd6_0_788 : subd6_0 [0, 0, 0] = true := by decide +kernel
theorem subd6_0_789 : subd6_0 [0, 0, 1] = true := by decide +kernel
theorem subd6_0_790 : subd6_0 [0, 0, 2] = true := by decide +kernel
theorem subd6_0_791 : subd6_0 [0, 0, 3] = true := by decide +kernel
theorem subd6_0_792 : subd6_0 [0, 0, 4] = true := by decide +kernel
theorem subd6_0_793 : subd6_0 [0, 0, 5] = true := by decide +kernel
theorem subd6_0_794 : subd6_0 [0, 0, 6] = true := by decide +kernel
theorem subd6_0_795 : subd6_0 [0, 0, 7] = true := by decide +kernel
theorem subd6_0_796 : subd6_0 [0, 0, 8] = true := by decide +kernel
theorem subd6_0_797 : subd6_0 [0, 1, -9] = true := by decide +kernel
theorem subd6_0_798 : subd6_0 [0, 1, -8] = true := by decide +kernel
theorem subd6_0_799 : subd6_0 [0, 1, -7] = true := by decide +kernel
theorem sbd6_0_24 : ∀ q ∈ blkd6_0_24, subd6_0 q = true := by
  unfold blkd6_0_24
  exact List.forall_mem_cons.2 ⟨subd6_0_768, List.forall_mem_cons.2 ⟨subd6_0_769, List.forall_mem_cons.2 ⟨subd6_0_770, List.forall_mem_cons.2 ⟨subd6_0_771, List.forall_mem_cons.2 ⟨subd6_0_772, List.forall_mem_cons.2 ⟨subd6_0_773, List.forall_mem_cons.2 ⟨subd6_0_774, List.forall_mem_cons.2 ⟨subd6_0_775, List.forall_mem_cons.2 ⟨subd6_0_776, List.forall_mem_cons.2 ⟨subd6_0_777, List.forall_mem_cons.2 ⟨subd6_0_778, List.forall_mem_cons.2 ⟨subd6_0_779, List.forall_mem_cons.2 ⟨subd6_0_780, List.forall_mem_cons.2 ⟨subd6_0_781, List.forall_mem_cons.2 ⟨subd6_0_782, List.forall_mem_cons.2 ⟨subd6_0_783, List.forall_mem_cons.2 ⟨subd6_0_784, List.forall_mem_cons.2 ⟨subd6_0_785, List.forall_mem_cons.2 ⟨subd6_0_786, List.forall_mem_cons.2 ⟨subd6_0_787, List.forall_mem_cons.2 ⟨subd6_0_788, List.forall_mem_cons.2 ⟨subd6_0_789, List.forall_mem_cons.2 ⟨subd6_0_790, List.forall_mem_cons.2 ⟨subd6_0_791, List.forall_mem_cons.2 ⟨subd6_0_792, List.forall_mem_cons.2 ⟨subd6_0_793, List.forall_mem_cons.2 ⟨subd6_0_794, List.forall_mem_cons.2 ⟨subd6_0_795, List.forall_mem_cons.2 ⟨subd6_0_796, List.forall_mem_cons.2 ⟨subd6_0_797, List.forall_mem_cons.2 ⟨subd6_0_798, List.forall_mem_cons.2 ⟨subd6_0_799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_800 : subd6_0 [0, 1, -6] = true := by decide +kernel
theorem subd6_0_801 : subd6_0 [0, 1, -5] = true := by decide +kernel
theorem subd6_0_802 : subd6_0 [0, 1, -4] = true := by decide +kernel
theorem subd6_0_803 : subd6_0 [0, 1, -3] = true := by decide +kernel
theorem subd6_0_804 : subd6_0 [0, 1, -2] = true := by decide +kernel
theorem subd6_0_805 : subd6_0 [0, 1, -1] = true := by decide +kernel
theorem subd6_0_806 : subd6_0 [0, 1, 0] = true := by decide +kernel
theorem subd6_0_807 : subd6_0 [0, 1, 1] = true := by decide +kernel
theorem subd6_0_808 : subd6_0 [0, 1, 2] = true := by decide +kernel
theorem subd6_0_809 : subd6_0 [0, 1, 3] = true := by decide +kernel
theorem subd6_0_810 : subd6_0 [0, 1, 4] = true := by decide +kernel
theorem subd6_0_811 : subd6_0 [0, 1, 5] = true := by decide +kernel
theorem subd6_0_812 : subd6_0 [0, 1, 6] = true := by decide +kernel
theorem subd6_0_813 : subd6_0 [0, 1, 7] = true := by decide +kernel
theorem subd6_0_814 : subd6_0 [0, 1, 8] = true := by decide +kernel
theorem subd6_0_815 : subd6_0 [0, 2, -9] = true := by decide +kernel
theorem subd6_0_816 : subd6_0 [0, 2, -8] = true := by decide +kernel
theorem subd6_0_817 : subd6_0 [0, 2, -7] = true := by decide +kernel
theorem subd6_0_818 : subd6_0 [0, 2, -6] = true := by decide +kernel
theorem subd6_0_819 : subd6_0 [0, 2, -5] = true := by decide +kernel
theorem subd6_0_820 : subd6_0 [0, 2, -4] = true := by decide +kernel
theorem subd6_0_821 : subd6_0 [0, 2, -3] = true := by decide +kernel
theorem subd6_0_822 : subd6_0 [0, 2, -2] = true := by decide +kernel
theorem subd6_0_823 : subd6_0 [0, 2, -1] = true := by decide +kernel
theorem subd6_0_824 : subd6_0 [0, 2, 0] = true := by decide +kernel
theorem subd6_0_825 : subd6_0 [0, 2, 1] = true := by decide +kernel
theorem subd6_0_826 : subd6_0 [0, 2, 2] = true := by decide +kernel
theorem subd6_0_827 : subd6_0 [0, 2, 3] = true := by decide +kernel
theorem subd6_0_828 : subd6_0 [0, 2, 4] = true := by decide +kernel
theorem subd6_0_829 : subd6_0 [0, 2, 5] = true := by decide +kernel
theorem subd6_0_830 : subd6_0 [0, 2, 6] = true := by decide +kernel
theorem subd6_0_831 : subd6_0 [0, 2, 7] = true := by decide +kernel
theorem sbd6_0_25 : ∀ q ∈ blkd6_0_25, subd6_0 q = true := by
  unfold blkd6_0_25
  exact List.forall_mem_cons.2 ⟨subd6_0_800, List.forall_mem_cons.2 ⟨subd6_0_801, List.forall_mem_cons.2 ⟨subd6_0_802, List.forall_mem_cons.2 ⟨subd6_0_803, List.forall_mem_cons.2 ⟨subd6_0_804, List.forall_mem_cons.2 ⟨subd6_0_805, List.forall_mem_cons.2 ⟨subd6_0_806, List.forall_mem_cons.2 ⟨subd6_0_807, List.forall_mem_cons.2 ⟨subd6_0_808, List.forall_mem_cons.2 ⟨subd6_0_809, List.forall_mem_cons.2 ⟨subd6_0_810, List.forall_mem_cons.2 ⟨subd6_0_811, List.forall_mem_cons.2 ⟨subd6_0_812, List.forall_mem_cons.2 ⟨subd6_0_813, List.forall_mem_cons.2 ⟨subd6_0_814, List.forall_mem_cons.2 ⟨subd6_0_815, List.forall_mem_cons.2 ⟨subd6_0_816, List.forall_mem_cons.2 ⟨subd6_0_817, List.forall_mem_cons.2 ⟨subd6_0_818, List.forall_mem_cons.2 ⟨subd6_0_819, List.forall_mem_cons.2 ⟨subd6_0_820, List.forall_mem_cons.2 ⟨subd6_0_821, List.forall_mem_cons.2 ⟨subd6_0_822, List.forall_mem_cons.2 ⟨subd6_0_823, List.forall_mem_cons.2 ⟨subd6_0_824, List.forall_mem_cons.2 ⟨subd6_0_825, List.forall_mem_cons.2 ⟨subd6_0_826, List.forall_mem_cons.2 ⟨subd6_0_827, List.forall_mem_cons.2 ⟨subd6_0_828, List.forall_mem_cons.2 ⟨subd6_0_829, List.forall_mem_cons.2 ⟨subd6_0_830, List.forall_mem_cons.2 ⟨subd6_0_831, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_832 : subd6_0 [0, 2, 8] = true := by decide +kernel
theorem subd6_0_833 : subd6_0 [0, 3, -9] = true := by decide +kernel
theorem subd6_0_834 : subd6_0 [0, 3, -8] = true := by decide +kernel
theorem subd6_0_835 : subd6_0 [0, 3, -7] = true := by decide +kernel
theorem subd6_0_836 : subd6_0 [0, 3, -6] = true := by decide +kernel
theorem subd6_0_837 : subd6_0 [0, 3, -5] = true := by decide +kernel
theorem subd6_0_838 : subd6_0 [0, 3, -4] = true := by decide +kernel
theorem subd6_0_839 : subd6_0 [0, 3, -3] = true := by decide +kernel
theorem subd6_0_840 : subd6_0 [0, 3, -2] = true := by decide +kernel
theorem subd6_0_841 : subd6_0 [0, 3, -1] = true := by decide +kernel
theorem subd6_0_842 : subd6_0 [0, 3, 0] = true := by decide +kernel
theorem subd6_0_843 : subd6_0 [0, 3, 1] = true := by decide +kernel
theorem subd6_0_844 : subd6_0 [0, 3, 2] = true := by decide +kernel
theorem subd6_0_845 : subd6_0 [0, 3, 3] = true := by decide +kernel
theorem subd6_0_846 : subd6_0 [0, 3, 4] = true := by decide +kernel
theorem subd6_0_847 : subd6_0 [0, 3, 5] = true := by decide +kernel
theorem subd6_0_848 : subd6_0 [0, 3, 6] = true := by decide +kernel
theorem subd6_0_849 : subd6_0 [0, 3, 7] = true := by decide +kernel
theorem subd6_0_850 : subd6_0 [0, 4, -8] = true := by decide +kernel
theorem subd6_0_851 : subd6_0 [0, 4, -7] = true := by decide +kernel
theorem subd6_0_852 : subd6_0 [0, 4, -6] = true := by decide +kernel
theorem subd6_0_853 : subd6_0 [0, 4, -5] = true := by decide +kernel
theorem subd6_0_854 : subd6_0 [0, 4, -4] = true := by decide +kernel
theorem subd6_0_855 : subd6_0 [0, 4, -3] = true := by decide +kernel
theorem subd6_0_856 : subd6_0 [0, 4, -2] = true := by decide +kernel
theorem subd6_0_857 : subd6_0 [0, 4, -1] = true := by decide +kernel
theorem subd6_0_858 : subd6_0 [0, 4, 0] = true := by decide +kernel
theorem subd6_0_859 : subd6_0 [0, 4, 1] = true := by decide +kernel
theorem subd6_0_860 : subd6_0 [0, 4, 2] = true := by decide +kernel
theorem subd6_0_861 : subd6_0 [0, 4, 3] = true := by decide +kernel
theorem subd6_0_862 : subd6_0 [0, 4, 4] = true := by decide +kernel
theorem subd6_0_863 : subd6_0 [0, 4, 5] = true := by decide +kernel
theorem sbd6_0_26 : ∀ q ∈ blkd6_0_26, subd6_0 q = true := by
  unfold blkd6_0_26
  exact List.forall_mem_cons.2 ⟨subd6_0_832, List.forall_mem_cons.2 ⟨subd6_0_833, List.forall_mem_cons.2 ⟨subd6_0_834, List.forall_mem_cons.2 ⟨subd6_0_835, List.forall_mem_cons.2 ⟨subd6_0_836, List.forall_mem_cons.2 ⟨subd6_0_837, List.forall_mem_cons.2 ⟨subd6_0_838, List.forall_mem_cons.2 ⟨subd6_0_839, List.forall_mem_cons.2 ⟨subd6_0_840, List.forall_mem_cons.2 ⟨subd6_0_841, List.forall_mem_cons.2 ⟨subd6_0_842, List.forall_mem_cons.2 ⟨subd6_0_843, List.forall_mem_cons.2 ⟨subd6_0_844, List.forall_mem_cons.2 ⟨subd6_0_845, List.forall_mem_cons.2 ⟨subd6_0_846, List.forall_mem_cons.2 ⟨subd6_0_847, List.forall_mem_cons.2 ⟨subd6_0_848, List.forall_mem_cons.2 ⟨subd6_0_849, List.forall_mem_cons.2 ⟨subd6_0_850, List.forall_mem_cons.2 ⟨subd6_0_851, List.forall_mem_cons.2 ⟨subd6_0_852, List.forall_mem_cons.2 ⟨subd6_0_853, List.forall_mem_cons.2 ⟨subd6_0_854, List.forall_mem_cons.2 ⟨subd6_0_855, List.forall_mem_cons.2 ⟨subd6_0_856, List.forall_mem_cons.2 ⟨subd6_0_857, List.forall_mem_cons.2 ⟨subd6_0_858, List.forall_mem_cons.2 ⟨subd6_0_859, List.forall_mem_cons.2 ⟨subd6_0_860, List.forall_mem_cons.2 ⟨subd6_0_861, List.forall_mem_cons.2 ⟨subd6_0_862, List.forall_mem_cons.2 ⟨subd6_0_863, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_864 : subd6_0 [0, 4, 6] = true := by decide +kernel
theorem subd6_0_865 : subd6_0 [0, 5, -8] = true := by decide +kernel
theorem subd6_0_866 : subd6_0 [0, 5, -7] = true := by decide +kernel
theorem subd6_0_867 : subd6_0 [0, 5, -6] = true := by decide +kernel
theorem subd6_0_868 : subd6_0 [0, 5, -5] = true := by decide +kernel
theorem subd6_0_869 : subd6_0 [0, 5, -4] = true := by decide +kernel
theorem subd6_0_870 : subd6_0 [0, 5, -3] = true := by decide +kernel
theorem subd6_0_871 : subd6_0 [0, 5, -2] = true := by decide +kernel
theorem subd6_0_872 : subd6_0 [0, 5, -1] = true := by decide +kernel
theorem subd6_0_873 : subd6_0 [0, 5, 0] = true := by decide +kernel
theorem subd6_0_874 : subd6_0 [0, 5, 1] = true := by decide +kernel
theorem subd6_0_875 : subd6_0 [0, 5, 2] = true := by decide +kernel
theorem subd6_0_876 : subd6_0 [0, 5, 3] = true := by decide +kernel
theorem subd6_0_877 : subd6_0 [0, 5, 4] = true := by decide +kernel
theorem subd6_0_878 : subd6_0 [0, 5, 5] = true := by decide +kernel
theorem subd6_0_879 : subd6_0 [0, 5, 6] = true := by decide +kernel
theorem subd6_0_880 : subd6_0 [0, 6] = true := by decide +kernel
theorem subd6_0_881 : subd6_0 [0, 7] = true := by decide +kernel
theorem subd6_0_882 : subd6_0 [0, 8] = true := by decide +kernel
theorem subd6_0_883 : subd6_0 [1, -9] = true := by decide +kernel
theorem subd6_0_884 : subd6_0 [1, -8] = true := by decide +kernel
theorem subd6_0_885 : subd6_0 [1, -7] = true := by decide +kernel
theorem subd6_0_886 : subd6_0 [1, -6] = true := by decide +kernel
theorem subd6_0_887 : subd6_0 [1, -5, -7] = true := by decide +kernel
theorem subd6_0_888 : subd6_0 [1, -5, -6] = true := by decide +kernel
theorem subd6_0_889 : subd6_0 [1, -5, -5] = true := by decide +kernel
theorem subd6_0_890 : subd6_0 [1, -5, -4] = true := by decide +kernel
theorem subd6_0_891 : subd6_0 [1, -5, -3] = true := by decide +kernel
theorem subd6_0_892 : subd6_0 [1, -5, -2] = true := by decide +kernel
theorem subd6_0_893 : subd6_0 [1, -5, -1] = true := by decide +kernel
theorem subd6_0_894 : subd6_0 [1, -5, 0] = true := by decide +kernel
theorem subd6_0_895 : subd6_0 [1, -5, 1] = true := by decide +kernel
theorem sbd6_0_27 : ∀ q ∈ blkd6_0_27, subd6_0 q = true := by
  unfold blkd6_0_27
  exact List.forall_mem_cons.2 ⟨subd6_0_864, List.forall_mem_cons.2 ⟨subd6_0_865, List.forall_mem_cons.2 ⟨subd6_0_866, List.forall_mem_cons.2 ⟨subd6_0_867, List.forall_mem_cons.2 ⟨subd6_0_868, List.forall_mem_cons.2 ⟨subd6_0_869, List.forall_mem_cons.2 ⟨subd6_0_870, List.forall_mem_cons.2 ⟨subd6_0_871, List.forall_mem_cons.2 ⟨subd6_0_872, List.forall_mem_cons.2 ⟨subd6_0_873, List.forall_mem_cons.2 ⟨subd6_0_874, List.forall_mem_cons.2 ⟨subd6_0_875, List.forall_mem_cons.2 ⟨subd6_0_876, List.forall_mem_cons.2 ⟨subd6_0_877, List.forall_mem_cons.2 ⟨subd6_0_878, List.forall_mem_cons.2 ⟨subd6_0_879, List.forall_mem_cons.2 ⟨subd6_0_880, List.forall_mem_cons.2 ⟨subd6_0_881, List.forall_mem_cons.2 ⟨subd6_0_882, List.forall_mem_cons.2 ⟨subd6_0_883, List.forall_mem_cons.2 ⟨subd6_0_884, List.forall_mem_cons.2 ⟨subd6_0_885, List.forall_mem_cons.2 ⟨subd6_0_886, List.forall_mem_cons.2 ⟨subd6_0_887, List.forall_mem_cons.2 ⟨subd6_0_888, List.forall_mem_cons.2 ⟨subd6_0_889, List.forall_mem_cons.2 ⟨subd6_0_890, List.forall_mem_cons.2 ⟨subd6_0_891, List.forall_mem_cons.2 ⟨subd6_0_892, List.forall_mem_cons.2 ⟨subd6_0_893, List.forall_mem_cons.2 ⟨subd6_0_894, List.forall_mem_cons.2 ⟨subd6_0_895, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_896 : subd6_0 [1, -5, 2] = true := by decide +kernel
theorem subd6_0_897 : subd6_0 [1, -5, 3] = true := by decide +kernel
theorem subd6_0_898 : subd6_0 [1, -5, 4] = true := by decide +kernel
theorem subd6_0_899 : subd6_0 [1, -5, 5] = true := by decide +kernel
theorem subd6_0_900 : subd6_0 [1, -5, 6] = true := by decide +kernel
theorem subd6_0_901 : subd6_0 [1, -5, 7] = true := by decide +kernel
theorem subd6_0_902 : subd6_0 [1, -4, -7] = true := by decide +kernel
theorem subd6_0_903 : subd6_0 [1, -4, -6] = true := by decide +kernel
theorem subd6_0_904 : subd6_0 [1, -4, -5] = true := by decide +kernel
theorem subd6_0_905 : subd6_0 [1, -4, -4] = true := by decide +kernel
theorem subd6_0_906 : subd6_0 [1, -4, -3] = true := by decide +kernel
theorem subd6_0_907 : subd6_0 [1, -4, -2] = true := by decide +kernel
theorem subd6_0_908 : subd6_0 [1, -4, -1] = true := by decide +kernel
theorem subd6_0_909 : subd6_0 [1, -4, 0] = true := by decide +kernel
theorem subd6_0_910 : subd6_0 [1, -4, 1] = true := by decide +kernel
theorem subd6_0_911 : subd6_0 [1, -4, 2] = true := by decide +kernel
theorem subd6_0_912 : subd6_0 [1, -4, 3] = true := by decide +kernel
theorem subd6_0_913 : subd6_0 [1, -4, 4] = true := by decide +kernel
theorem subd6_0_914 : subd6_0 [1, -4, 5] = true := by decide +kernel
theorem subd6_0_915 : subd6_0 [1, -4, 6] = true := by decide +kernel
theorem subd6_0_916 : subd6_0 [1, -4, 7] = true := by decide +kernel
theorem subd6_0_917 : subd6_0 [1, -3, -8] = true := by decide +kernel
theorem subd6_0_918 : subd6_0 [1, -3, -7] = true := by decide +kernel
theorem subd6_0_919 : subd6_0 [1, -3, -6] = true := by decide +kernel
theorem subd6_0_920 : subd6_0 [1, -3, -5] = true := by decide +kernel
theorem subd6_0_921 : subd6_0 [1, -3, -4] = true := by decide +kernel
theorem subd6_0_922 : subd6_0 [1, -3, -3] = true := by decide +kernel
theorem subd6_0_923 : subd6_0 [1, -3, -2] = true := by decide +kernel
theorem subd6_0_924 : subd6_0 [1, -3, -1] = true := by decide +kernel
theorem subd6_0_925 : subd6_0 [1, -3, 0] = true := by decide +kernel
theorem subd6_0_926 : subd6_0 [1, -3, 1] = true := by decide +kernel
theorem subd6_0_927 : subd6_0 [1, -3, 2] = true := by decide +kernel
theorem sbd6_0_28 : ∀ q ∈ blkd6_0_28, subd6_0 q = true := by
  unfold blkd6_0_28
  exact List.forall_mem_cons.2 ⟨subd6_0_896, List.forall_mem_cons.2 ⟨subd6_0_897, List.forall_mem_cons.2 ⟨subd6_0_898, List.forall_mem_cons.2 ⟨subd6_0_899, List.forall_mem_cons.2 ⟨subd6_0_900, List.forall_mem_cons.2 ⟨subd6_0_901, List.forall_mem_cons.2 ⟨subd6_0_902, List.forall_mem_cons.2 ⟨subd6_0_903, List.forall_mem_cons.2 ⟨subd6_0_904, List.forall_mem_cons.2 ⟨subd6_0_905, List.forall_mem_cons.2 ⟨subd6_0_906, List.forall_mem_cons.2 ⟨subd6_0_907, List.forall_mem_cons.2 ⟨subd6_0_908, List.forall_mem_cons.2 ⟨subd6_0_909, List.forall_mem_cons.2 ⟨subd6_0_910, List.forall_mem_cons.2 ⟨subd6_0_911, List.forall_mem_cons.2 ⟨subd6_0_912, List.forall_mem_cons.2 ⟨subd6_0_913, List.forall_mem_cons.2 ⟨subd6_0_914, List.forall_mem_cons.2 ⟨subd6_0_915, List.forall_mem_cons.2 ⟨subd6_0_916, List.forall_mem_cons.2 ⟨subd6_0_917, List.forall_mem_cons.2 ⟨subd6_0_918, List.forall_mem_cons.2 ⟨subd6_0_919, List.forall_mem_cons.2 ⟨subd6_0_920, List.forall_mem_cons.2 ⟨subd6_0_921, List.forall_mem_cons.2 ⟨subd6_0_922, List.forall_mem_cons.2 ⟨subd6_0_923, List.forall_mem_cons.2 ⟨subd6_0_924, List.forall_mem_cons.2 ⟨subd6_0_925, List.forall_mem_cons.2 ⟨subd6_0_926, List.forall_mem_cons.2 ⟨subd6_0_927, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_928 : subd6_0 [1, -3, 3] = true := by decide +kernel
theorem subd6_0_929 : subd6_0 [1, -3, 4] = true := by decide +kernel
theorem subd6_0_930 : subd6_0 [1, -3, 5] = true := by decide +kernel
theorem subd6_0_931 : subd6_0 [1, -3, 6] = true := by decide +kernel
theorem subd6_0_932 : subd6_0 [1, -3, 7] = true := by decide +kernel
theorem subd6_0_933 : subd6_0 [1, -3, 8] = true := by decide +kernel
theorem subd6_0_934 : subd6_0 [1, -2, -9] = true := by decide +kernel
theorem subd6_0_935 : subd6_0 [1, -2, -8] = true := by decide +kernel
theorem subd6_0_936 : subd6_0 [1, -2, -7] = true := by decide +kernel
theorem subd6_0_937 : subd6_0 [1, -2, -6] = true := by decide +kernel
theorem subd6_0_938 : subd6_0 [1, -2, -5] = true := by decide +kernel
theorem subd6_0_939 : subd6_0 [1, -2, -4] = true := by decide +kernel
theorem subd6_0_940 : subd6_0 [1, -2, -3] = true := by decide +kernel
theorem subd6_0_941 : subd6_0 [1, -2, -2] = true := by decide +kernel
theorem subd6_0_942 : subd6_0 [1, -2, -1] = true := by decide +kernel
theorem subd6_0_943 : subd6_0 [1, -2, 0] = true := by decide +kernel
theorem subd6_0_944 : subd6_0 [1, -2, 1] = true := by decide +kernel
theorem subd6_0_945 : subd6_0 [1, -2, 2] = true := by decide +kernel
theorem subd6_0_946 : subd6_0 [1, -2, 3] = true := by decide +kernel
theorem subd6_0_947 : subd6_0 [1, -2, 4] = true := by decide +kernel
theorem subd6_0_948 : subd6_0 [1, -2, 5] = true := by decide +kernel
theorem subd6_0_949 : subd6_0 [1, -2, 6] = true := by decide +kernel
theorem subd6_0_950 : subd6_0 [1, -2, 7] = true := by decide +kernel
theorem subd6_0_951 : subd6_0 [1, -2, 8] = true := by decide +kernel
theorem subd6_0_952 : subd6_0 [1, -1, -9] = true := by decide +kernel
theorem subd6_0_953 : subd6_0 [1, -1, -8] = true := by decide +kernel
theorem subd6_0_954 : subd6_0 [1, -1, -7] = true := by decide +kernel
theorem subd6_0_955 : subd6_0 [1, -1, -6] = true := by decide +kernel
theorem subd6_0_956 : subd6_0 [1, -1, -5] = true := by decide +kernel
theorem subd6_0_957 : subd6_0 [1, -1, -4] = true := by decide +kernel
theorem subd6_0_958 : subd6_0 [1, -1, -3] = true := by decide +kernel
theorem subd6_0_959 : subd6_0 [1, -1, -2] = true := by decide +kernel
theorem sbd6_0_29 : ∀ q ∈ blkd6_0_29, subd6_0 q = true := by
  unfold blkd6_0_29
  exact List.forall_mem_cons.2 ⟨subd6_0_928, List.forall_mem_cons.2 ⟨subd6_0_929, List.forall_mem_cons.2 ⟨subd6_0_930, List.forall_mem_cons.2 ⟨subd6_0_931, List.forall_mem_cons.2 ⟨subd6_0_932, List.forall_mem_cons.2 ⟨subd6_0_933, List.forall_mem_cons.2 ⟨subd6_0_934, List.forall_mem_cons.2 ⟨subd6_0_935, List.forall_mem_cons.2 ⟨subd6_0_936, List.forall_mem_cons.2 ⟨subd6_0_937, List.forall_mem_cons.2 ⟨subd6_0_938, List.forall_mem_cons.2 ⟨subd6_0_939, List.forall_mem_cons.2 ⟨subd6_0_940, List.forall_mem_cons.2 ⟨subd6_0_941, List.forall_mem_cons.2 ⟨subd6_0_942, List.forall_mem_cons.2 ⟨subd6_0_943, List.forall_mem_cons.2 ⟨subd6_0_944, List.forall_mem_cons.2 ⟨subd6_0_945, List.forall_mem_cons.2 ⟨subd6_0_946, List.forall_mem_cons.2 ⟨subd6_0_947, List.forall_mem_cons.2 ⟨subd6_0_948, List.forall_mem_cons.2 ⟨subd6_0_949, List.forall_mem_cons.2 ⟨subd6_0_950, List.forall_mem_cons.2 ⟨subd6_0_951, List.forall_mem_cons.2 ⟨subd6_0_952, List.forall_mem_cons.2 ⟨subd6_0_953, List.forall_mem_cons.2 ⟨subd6_0_954, List.forall_mem_cons.2 ⟨subd6_0_955, List.forall_mem_cons.2 ⟨subd6_0_956, List.forall_mem_cons.2 ⟨subd6_0_957, List.forall_mem_cons.2 ⟨subd6_0_958, List.forall_mem_cons.2 ⟨subd6_0_959, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C093
