import ReflectZphi.Data.Cert5.C055.Base

namespace ReflectZphi.Data.Cert5.C055
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub4_480 : sub4 [1, -3, -6] = true := by decide +kernel
theorem sub4_481 : sub4 [1, -3, -5] = true := by decide +kernel
theorem sub4_482 : sub4 [1, -3, -4] = true := by decide +kernel
theorem sub4_483 : sub4 [1, -3, -3] = true := by decide +kernel
theorem sub4_484 : sub4 [1, -3, -2] = true := by decide +kernel
theorem sub4_485 : sub4 [1, -3, -1] = true := by decide +kernel
theorem sub4_486 : sub4 [1, -3, 0] = true := by decide +kernel
theorem sub4_487 : sub4 [1, -3, 1] = true := by decide +kernel
theorem sub4_488 : sub4 [1, -3, 2] = true := by decide +kernel
theorem sub4_489 : sub4 [1, -3, 3] = true := by decide +kernel
theorem sub4_490 : sub4 [1, -3, 4] = true := by decide +kernel
theorem sub4_491 : sub4 [1, -3, 5] = true := by decide +kernel
theorem sub4_492 : sub4 [1, -3, 6] = true := by decide +kernel
theorem sub4_493 : sub4 [1, -3, 7] = true := by decide +kernel
theorem sub4_494 : sub4 [1, -2, -12] = true := by decide +kernel
theorem sub4_495 : sub4 [1, -2, -11] = true := by decide +kernel
theorem sub4_496 : sub4 [1, -2, -10] = true := by decide +kernel
theorem sub4_497 : sub4 [1, -2, -9] = true := by decide +kernel
theorem sub4_498 : sub4 [1, -2, -8] = true := by decide +kernel
theorem sub4_499 : sub4 [1, -2, -7] = true := by decide +kernel
theorem sub4_500 : sub4 [1, -2, -6] = true := by decide +kernel
theorem sub4_501 : sub4 [1, -2, -5] = true := by decide +kernel
theorem sub4_502 : sub4 [1, -2, -4] = true := by decide +kernel
theorem sub4_503 : sub4 [1, -2, -3] = true := by decide +kernel
theorem sub4_504 : sub4 [1, -2, -2] = true := by decide +kernel
theorem sub4_505 : sub4 [1, -2, -1] = true := by decide +kernel
theorem sub4_506 : sub4 [1, -2, 0] = true := by decide +kernel
theorem sub4_507 : sub4 [1, -2, 1] = true := by decide +kernel
theorem sub4_508 : sub4 [1, -2, 2] = true := by decide +kernel
theorem sub4_509 : sub4 [1, -2, 3] = true := by decide +kernel
theorem sub4_510 : sub4 [1, -2, 4] = true := by decide +kernel
theorem sub4_511 : sub4 [1, -2, 5] = true := by decide +kernel
theorem sb4_15 : ∀ q ∈ blk4_15, sub4 q = true := by
  unfold blk4_15
  exact List.forall_mem_cons.2 ⟨sub4_480, List.forall_mem_cons.2 ⟨sub4_481, List.forall_mem_cons.2 ⟨sub4_482, List.forall_mem_cons.2 ⟨sub4_483, List.forall_mem_cons.2 ⟨sub4_484, List.forall_mem_cons.2 ⟨sub4_485, List.forall_mem_cons.2 ⟨sub4_486, List.forall_mem_cons.2 ⟨sub4_487, List.forall_mem_cons.2 ⟨sub4_488, List.forall_mem_cons.2 ⟨sub4_489, List.forall_mem_cons.2 ⟨sub4_490, List.forall_mem_cons.2 ⟨sub4_491, List.forall_mem_cons.2 ⟨sub4_492, List.forall_mem_cons.2 ⟨sub4_493, List.forall_mem_cons.2 ⟨sub4_494, List.forall_mem_cons.2 ⟨sub4_495, List.forall_mem_cons.2 ⟨sub4_496, List.forall_mem_cons.2 ⟨sub4_497, List.forall_mem_cons.2 ⟨sub4_498, List.forall_mem_cons.2 ⟨sub4_499, List.forall_mem_cons.2 ⟨sub4_500, List.forall_mem_cons.2 ⟨sub4_501, List.forall_mem_cons.2 ⟨sub4_502, List.forall_mem_cons.2 ⟨sub4_503, List.forall_mem_cons.2 ⟨sub4_504, List.forall_mem_cons.2 ⟨sub4_505, List.forall_mem_cons.2 ⟨sub4_506, List.forall_mem_cons.2 ⟨sub4_507, List.forall_mem_cons.2 ⟨sub4_508, List.forall_mem_cons.2 ⟨sub4_509, List.forall_mem_cons.2 ⟨sub4_510, List.forall_mem_cons.2 ⟨sub4_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_512 : sub4 [1, -2, 6] = true := by decide +kernel
theorem sub4_513 : sub4 [1, -2, 7] = true := by decide +kernel
theorem sub4_514 : sub4 [1, -2, 8] = true := by decide +kernel
theorem sub4_515 : sub4 [1, -2, 9] = true := by decide +kernel
theorem sub4_516 : sub4 [1, -1, -12] = true := by decide +kernel
theorem sub4_517 : sub4 [1, -1, -11] = true := by decide +kernel
theorem sub4_518 : sub4 [1, -1, -10] = true := by decide +kernel
theorem sub4_519 : sub4 [1, -1, -9] = true := by decide +kernel
theorem sub4_520 : sub4 [1, -1, -8] = true := by decide +kernel
theorem sub4_521 : sub4 [1, -1, -7] = true := by decide +kernel
theorem sub4_522 : sub4 [1, -1, -6] = true := by decide +kernel
theorem sub4_523 : sub4 [1, -1, -5] = true := by decide +kernel
theorem sub4_524 : sub4 [1, -1, -4] = true := by decide +kernel
theorem sub4_525 : sub4 [1, -1, -3] = true := by decide +kernel
theorem sub4_526 : sub4 [1, -1, -2] = true := by decide +kernel
theorem sub4_527 : sub4 [1, -1, -1] = true := by decide +kernel
theorem sub4_528 : sub4 [1, -1, 0] = true := by decide +kernel
theorem sub4_529 : sub4 [1, -1, 1] = true := by decide +kernel
theorem sub4_530 : sub4 [1, -1, 2] = true := by decide +kernel
theorem sub4_531 : sub4 [1, -1, 3] = true := by decide +kernel
theorem sub4_532 : sub4 [1, -1, 4] = true := by decide +kernel
theorem sub4_533 : sub4 [1, -1, 5] = true := by decide +kernel
theorem sub4_534 : sub4 [1, -1, 6] = true := by decide +kernel
theorem sub4_535 : sub4 [1, -1, 7] = true := by decide +kernel
theorem sub4_536 : sub4 [1, -1, 8] = true := by decide +kernel
theorem sub4_537 : sub4 [1, -1, 9] = true := by decide +kernel
theorem sub4_538 : sub4 [1, -1, 10] = true := by decide +kernel
theorem sub4_539 : sub4 [1, 0, -12] = true := by decide +kernel
theorem sub4_540 : sub4 [1, 0, -11] = true := by decide +kernel
theorem sub4_541 : sub4 [1, 0, -10] = true := by decide +kernel
theorem sub4_542 : sub4 [1, 0, -9] = true := by decide +kernel
theorem sub4_543 : sub4 [1, 0, -8] = true := by decide +kernel
theorem sb4_16 : ∀ q ∈ blk4_16, sub4 q = true := by
  unfold blk4_16
  exact List.forall_mem_cons.2 ⟨sub4_512, List.forall_mem_cons.2 ⟨sub4_513, List.forall_mem_cons.2 ⟨sub4_514, List.forall_mem_cons.2 ⟨sub4_515, List.forall_mem_cons.2 ⟨sub4_516, List.forall_mem_cons.2 ⟨sub4_517, List.forall_mem_cons.2 ⟨sub4_518, List.forall_mem_cons.2 ⟨sub4_519, List.forall_mem_cons.2 ⟨sub4_520, List.forall_mem_cons.2 ⟨sub4_521, List.forall_mem_cons.2 ⟨sub4_522, List.forall_mem_cons.2 ⟨sub4_523, List.forall_mem_cons.2 ⟨sub4_524, List.forall_mem_cons.2 ⟨sub4_525, List.forall_mem_cons.2 ⟨sub4_526, List.forall_mem_cons.2 ⟨sub4_527, List.forall_mem_cons.2 ⟨sub4_528, List.forall_mem_cons.2 ⟨sub4_529, List.forall_mem_cons.2 ⟨sub4_530, List.forall_mem_cons.2 ⟨sub4_531, List.forall_mem_cons.2 ⟨sub4_532, List.forall_mem_cons.2 ⟨sub4_533, List.forall_mem_cons.2 ⟨sub4_534, List.forall_mem_cons.2 ⟨sub4_535, List.forall_mem_cons.2 ⟨sub4_536, List.forall_mem_cons.2 ⟨sub4_537, List.forall_mem_cons.2 ⟨sub4_538, List.forall_mem_cons.2 ⟨sub4_539, List.forall_mem_cons.2 ⟨sub4_540, List.forall_mem_cons.2 ⟨sub4_541, List.forall_mem_cons.2 ⟨sub4_542, List.forall_mem_cons.2 ⟨sub4_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_544 : sub4 [1, 0, -7] = true := by decide +kernel
theorem sub4_545 : sub4 [1, 0, -6] = true := by decide +kernel
theorem sub4_546 : sub4 [1, 0, -5] = true := by decide +kernel
theorem sub4_547 : sub4 [1, 0, -4] = true := by decide +kernel
theorem sub4_548 : sub4 [1, 0, -3] = true := by decide +kernel
theorem sub4_549 : sub4 [1, 0, -2] = true := by decide +kernel
theorem sub4_550 : sub4 [1, 0, -1] = true := by decide +kernel
theorem sub4_551 : sub4 [1, 0, 0] = true := by decide +kernel
theorem sub4_552 : sub4 [1, 0, 1] = true := by decide +kernel
theorem sub4_553 : sub4 [1, 0, 2] = true := by decide +kernel
theorem sub4_554 : sub4 [1, 0, 3] = true := by decide +kernel
theorem sub4_555 : sub4 [1, 0, 4] = true := by decide +kernel
theorem sub4_556 : sub4 [1, 0, 5] = true := by decide +kernel
theorem sub4_557 : sub4 [1, 0, 6] = true := by decide +kernel
theorem sub4_558 : sub4 [1, 0, 7] = true := by decide +kernel
theorem sub4_559 : sub4 [1, 0, 8] = true := by decide +kernel
theorem sub4_560 : sub4 [1, 0, 9] = true := by decide +kernel
theorem sub4_561 : sub4 [1, 0, 10] = true := by decide +kernel
theorem sub4_562 : sub4 [1, 0, 11] = true := by decide +kernel
theorem sub4_563 : sub4 [1, 1, -12] = true := by decide +kernel
theorem sub4_564 : sub4 [1, 1, -11] = true := by decide +kernel
theorem sub4_565 : sub4 [1, 1, -10] = true := by decide +kernel
theorem sub4_566 : sub4 [1, 1, -9] = true := by decide +kernel
theorem sub4_567 : sub4 [1, 1, -8] = true := by decide +kernel
theorem sub4_568 : sub4 [1, 1, -7] = true := by decide +kernel
theorem sub4_569 : sub4 [1, 1, -6] = true := by decide +kernel
theorem sub4_570 : sub4 [1, 1, -5] = true := by decide +kernel
theorem sub4_571 : sub4 [1, 1, -4] = true := by decide +kernel
theorem sub4_572 : sub4 [1, 1, -3] = true := by decide +kernel
theorem sub4_573 : sub4 [1, 1, -2] = true := by decide +kernel
theorem sub4_574 : sub4 [1, 1, -1] = true := by decide +kernel
theorem sub4_575 : sub4 [1, 1, 0] = true := by decide +kernel
theorem sb4_17 : ∀ q ∈ blk4_17, sub4 q = true := by
  unfold blk4_17
  exact List.forall_mem_cons.2 ⟨sub4_544, List.forall_mem_cons.2 ⟨sub4_545, List.forall_mem_cons.2 ⟨sub4_546, List.forall_mem_cons.2 ⟨sub4_547, List.forall_mem_cons.2 ⟨sub4_548, List.forall_mem_cons.2 ⟨sub4_549, List.forall_mem_cons.2 ⟨sub4_550, List.forall_mem_cons.2 ⟨sub4_551, List.forall_mem_cons.2 ⟨sub4_552, List.forall_mem_cons.2 ⟨sub4_553, List.forall_mem_cons.2 ⟨sub4_554, List.forall_mem_cons.2 ⟨sub4_555, List.forall_mem_cons.2 ⟨sub4_556, List.forall_mem_cons.2 ⟨sub4_557, List.forall_mem_cons.2 ⟨sub4_558, List.forall_mem_cons.2 ⟨sub4_559, List.forall_mem_cons.2 ⟨sub4_560, List.forall_mem_cons.2 ⟨sub4_561, List.forall_mem_cons.2 ⟨sub4_562, List.forall_mem_cons.2 ⟨sub4_563, List.forall_mem_cons.2 ⟨sub4_564, List.forall_mem_cons.2 ⟨sub4_565, List.forall_mem_cons.2 ⟨sub4_566, List.forall_mem_cons.2 ⟨sub4_567, List.forall_mem_cons.2 ⟨sub4_568, List.forall_mem_cons.2 ⟨sub4_569, List.forall_mem_cons.2 ⟨sub4_570, List.forall_mem_cons.2 ⟨sub4_571, List.forall_mem_cons.2 ⟨sub4_572, List.forall_mem_cons.2 ⟨sub4_573, List.forall_mem_cons.2 ⟨sub4_574, List.forall_mem_cons.2 ⟨sub4_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_576 : sub4 [1, 1, 1] = true := by decide +kernel
theorem sub4_577 : sub4 [1, 1, 2] = true := by decide +kernel
theorem sub4_578 : sub4 [1, 1, 3] = true := by decide +kernel
theorem sub4_579 : sub4 [1, 1, 4] = true := by decide +kernel
theorem sub4_580 : sub4 [1, 1, 5] = true := by decide +kernel
theorem sub4_581 : sub4 [1, 1, 6] = true := by decide +kernel
theorem sub4_582 : sub4 [1, 1, 7] = true := by decide +kernel
theorem sub4_583 : sub4 [1, 1, 8] = true := by decide +kernel
theorem sub4_584 : sub4 [1, 1, 9] = true := by decide +kernel
theorem sub4_585 : sub4 [1, 1, 10] = true := by decide +kernel
theorem sub4_586 : sub4 [1, 2, -10] = true := by decide +kernel
theorem sub4_587 : sub4 [1, 2, -9] = true := by decide +kernel
theorem sub4_588 : sub4 [1, 2, -8] = true := by decide +kernel
theorem sub4_589 : sub4 [1, 2, -7] = true := by decide +kernel
theorem sub4_590 : sub4 [1, 2, -6] = true := by decide +kernel
theorem sub4_591 : sub4 [1, 2, -5] = true := by decide +kernel
theorem sub4_592 : sub4 [1, 2, -4] = true := by decide +kernel
theorem sub4_593 : sub4 [1, 2, -3] = true := by decide +kernel
theorem sub4_594 : sub4 [1, 2, -2] = true := by decide +kernel
theorem sub4_595 : sub4 [1, 2, -1] = true := by decide +kernel
theorem sub4_596 : sub4 [1, 2, 0] = true := by decide +kernel
theorem sub4_597 : sub4 [1, 2, 1] = true := by decide +kernel
theorem sub4_598 : sub4 [1, 2, 2] = true := by decide +kernel
theorem sub4_599 : sub4 [1, 2, 3] = true := by decide +kernel
theorem sub4_600 : sub4 [1, 2, 4] = true := by decide +kernel
theorem sub4_601 : sub4 [1, 2, 5] = true := by decide +kernel
theorem sub4_602 : sub4 [1, 2, 6] = true := by decide +kernel
theorem sub4_603 : sub4 [1, 2, 7] = true := by decide +kernel
theorem sub4_604 : sub4 [1, 2, 8] = true := by decide +kernel
theorem sub4_605 : sub4 [1, 2, 9] = true := by decide +kernel
theorem sub4_606 : sub4 [1, 3, -7] = true := by decide +kernel
theorem sub4_607 : sub4 [1, 3, -6] = true := by decide +kernel
theorem sb4_18 : ∀ q ∈ blk4_18, sub4 q = true := by
  unfold blk4_18
  exact List.forall_mem_cons.2 ⟨sub4_576, List.forall_mem_cons.2 ⟨sub4_577, List.forall_mem_cons.2 ⟨sub4_578, List.forall_mem_cons.2 ⟨sub4_579, List.forall_mem_cons.2 ⟨sub4_580, List.forall_mem_cons.2 ⟨sub4_581, List.forall_mem_cons.2 ⟨sub4_582, List.forall_mem_cons.2 ⟨sub4_583, List.forall_mem_cons.2 ⟨sub4_584, List.forall_mem_cons.2 ⟨sub4_585, List.forall_mem_cons.2 ⟨sub4_586, List.forall_mem_cons.2 ⟨sub4_587, List.forall_mem_cons.2 ⟨sub4_588, List.forall_mem_cons.2 ⟨sub4_589, List.forall_mem_cons.2 ⟨sub4_590, List.forall_mem_cons.2 ⟨sub4_591, List.forall_mem_cons.2 ⟨sub4_592, List.forall_mem_cons.2 ⟨sub4_593, List.forall_mem_cons.2 ⟨sub4_594, List.forall_mem_cons.2 ⟨sub4_595, List.forall_mem_cons.2 ⟨sub4_596, List.forall_mem_cons.2 ⟨sub4_597, List.forall_mem_cons.2 ⟨sub4_598, List.forall_mem_cons.2 ⟨sub4_599, List.forall_mem_cons.2 ⟨sub4_600, List.forall_mem_cons.2 ⟨sub4_601, List.forall_mem_cons.2 ⟨sub4_602, List.forall_mem_cons.2 ⟨sub4_603, List.forall_mem_cons.2 ⟨sub4_604, List.forall_mem_cons.2 ⟨sub4_605, List.forall_mem_cons.2 ⟨sub4_606, List.forall_mem_cons.2 ⟨sub4_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_608 : sub4 [1, 3, -5] = true := by decide +kernel
theorem sub4_609 : sub4 [1, 3, -4] = true := by decide +kernel
theorem sub4_610 : sub4 [1, 3, -3] = true := by decide +kernel
theorem sub4_611 : sub4 [1, 3, -2] = true := by decide +kernel
theorem sub4_612 : sub4 [1, 3, -1] = true := by decide +kernel
theorem sub4_613 : sub4 [1, 3, 0] = true := by decide +kernel
theorem sub4_614 : sub4 [1, 3, 1] = true := by decide +kernel
theorem sub4_615 : sub4 [1, 3, 2] = true := by decide +kernel
theorem sub4_616 : sub4 [1, 3, 3] = true := by decide +kernel
theorem sub4_617 : sub4 [1, 3, 4] = true := by decide +kernel
theorem sub4_618 : sub4 [1, 3, 5] = true := by decide +kernel
theorem sub4_619 : sub4 [1, 3, 6] = true := by decide +kernel
theorem sub4_620 : sub4 [1, 3, 7] = true := by decide +kernel
theorem sub4_621 : sub4 [2, -4] = true := by decide +kernel
theorem sub4_622 : sub4 [2, -3, -9] = true := by decide +kernel
theorem sub4_623 : sub4 [2, -3, -8] = true := by decide +kernel
theorem sub4_624 : sub4 [2, -3, -7] = true := by decide +kernel
theorem sub4_625 : sub4 [2, -3, -6] = true := by decide +kernel
theorem sub4_626 : sub4 [2, -3, -5] = true := by decide +kernel
theorem sub4_627 : sub4 [2, -3, -4] = true := by decide +kernel
theorem sub4_628 : sub4 [2, -3, -3] = true := by decide +kernel
theorem sub4_629 : sub4 [2, -3, -2] = true := by decide +kernel
theorem sub4_630 : sub4 [2, -3, -1] = true := by decide +kernel
theorem sub4_631 : sub4 [2, -3, 0] = true := by decide +kernel
theorem sub4_632 : sub4 [2, -3, 1] = true := by decide +kernel
theorem sub4_633 : sub4 [2, -3, 2] = true := by decide +kernel
theorem sub4_634 : sub4 [2, -3, 3] = true := by decide +kernel
theorem sub4_635 : sub4 [2, -3, 4] = true := by decide +kernel
theorem sub4_636 : sub4 [2, -3, 5] = true := by decide +kernel
theorem sub4_637 : sub4 [2, -2, -11] = true := by decide +kernel
theorem sub4_638 : sub4 [2, -2, -10] = true := by decide +kernel
theorem sub4_639 : sub4 [2, -2, -9] = true := by decide +kernel
theorem sb4_19 : ∀ q ∈ blk4_19, sub4 q = true := by
  unfold blk4_19
  exact List.forall_mem_cons.2 ⟨sub4_608, List.forall_mem_cons.2 ⟨sub4_609, List.forall_mem_cons.2 ⟨sub4_610, List.forall_mem_cons.2 ⟨sub4_611, List.forall_mem_cons.2 ⟨sub4_612, List.forall_mem_cons.2 ⟨sub4_613, List.forall_mem_cons.2 ⟨sub4_614, List.forall_mem_cons.2 ⟨sub4_615, List.forall_mem_cons.2 ⟨sub4_616, List.forall_mem_cons.2 ⟨sub4_617, List.forall_mem_cons.2 ⟨sub4_618, List.forall_mem_cons.2 ⟨sub4_619, List.forall_mem_cons.2 ⟨sub4_620, List.forall_mem_cons.2 ⟨sub4_621, List.forall_mem_cons.2 ⟨sub4_622, List.forall_mem_cons.2 ⟨sub4_623, List.forall_mem_cons.2 ⟨sub4_624, List.forall_mem_cons.2 ⟨sub4_625, List.forall_mem_cons.2 ⟨sub4_626, List.forall_mem_cons.2 ⟨sub4_627, List.forall_mem_cons.2 ⟨sub4_628, List.forall_mem_cons.2 ⟨sub4_629, List.forall_mem_cons.2 ⟨sub4_630, List.forall_mem_cons.2 ⟨sub4_631, List.forall_mem_cons.2 ⟨sub4_632, List.forall_mem_cons.2 ⟨sub4_633, List.forall_mem_cons.2 ⟨sub4_634, List.forall_mem_cons.2 ⟨sub4_635, List.forall_mem_cons.2 ⟨sub4_636, List.forall_mem_cons.2 ⟨sub4_637, List.forall_mem_cons.2 ⟨sub4_638, List.forall_mem_cons.2 ⟨sub4_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_640 : sub4 [2, -2, -8] = true := by decide +kernel
theorem sub4_641 : sub4 [2, -2, -7] = true := by decide +kernel
theorem sub4_642 : sub4 [2, -2, -6] = true := by decide +kernel
theorem sub4_643 : sub4 [2, -2, -5] = true := by decide +kernel
theorem sub4_644 : sub4 [2, -2, -4] = true := by decide +kernel
theorem sub4_645 : sub4 [2, -2, -3] = true := by decide +kernel
theorem sub4_646 : sub4 [2, -2, -2] = true := by decide +kernel
theorem sub4_647 : sub4 [2, -2, -1] = true := by decide +kernel
theorem sub4_648 : sub4 [2, -2, 0] = true := by decide +kernel
theorem sub4_649 : sub4 [2, -2, 1] = true := by decide +kernel
theorem sub4_650 : sub4 [2, -2, 2] = true := by decide +kernel
theorem sub4_651 : sub4 [2, -2, 3] = true := by decide +kernel
theorem sub4_652 : sub4 [2, -2, 4] = true := by decide +kernel
theorem sub4_653 : sub4 [2, -2, 5] = true := by decide +kernel
theorem sub4_654 : sub4 [2, -2, 6] = true := by decide +kernel
theorem sub4_655 : sub4 [2, -2, 7] = true := by decide +kernel
theorem sub4_656 : sub4 [2, -1, -11] = true := by decide +kernel
theorem sub4_657 : sub4 [2, -1, -10] = true := by decide +kernel
theorem sub4_658 : sub4 [2, -1, -9] = true := by decide +kernel
theorem sub4_659 : sub4 [2, -1, -8] = true := by decide +kernel
theorem sub4_660 : sub4 [2, -1, -7] = true := by decide +kernel
theorem sub4_661 : sub4 [2, -1, -6] = true := by decide +kernel
theorem sub4_662 : sub4 [2, -1, -5] = true := by decide +kernel
theorem sub4_663 : sub4 [2, -1, -4] = true := by decide +kernel
theorem sub4_664 : sub4 [2, -1, -3] = true := by decide +kernel
theorem sub4_665 : sub4 [2, -1, -2] = true := by decide +kernel
theorem sub4_666 : sub4 [2, -1, -1] = true := by decide +kernel
theorem sub4_667 : sub4 [2, -1, 0] = true := by decide +kernel
theorem sub4_668 : sub4 [2, -1, 1] = true := by decide +kernel
theorem sub4_669 : sub4 [2, -1, 2] = true := by decide +kernel
theorem sub4_670 : sub4 [2, -1, 3] = true := by decide +kernel
theorem sub4_671 : sub4 [2, -1, 4] = true := by decide +kernel
theorem sb4_20 : ∀ q ∈ blk4_20, sub4 q = true := by
  unfold blk4_20
  exact List.forall_mem_cons.2 ⟨sub4_640, List.forall_mem_cons.2 ⟨sub4_641, List.forall_mem_cons.2 ⟨sub4_642, List.forall_mem_cons.2 ⟨sub4_643, List.forall_mem_cons.2 ⟨sub4_644, List.forall_mem_cons.2 ⟨sub4_645, List.forall_mem_cons.2 ⟨sub4_646, List.forall_mem_cons.2 ⟨sub4_647, List.forall_mem_cons.2 ⟨sub4_648, List.forall_mem_cons.2 ⟨sub4_649, List.forall_mem_cons.2 ⟨sub4_650, List.forall_mem_cons.2 ⟨sub4_651, List.forall_mem_cons.2 ⟨sub4_652, List.forall_mem_cons.2 ⟨sub4_653, List.forall_mem_cons.2 ⟨sub4_654, List.forall_mem_cons.2 ⟨sub4_655, List.forall_mem_cons.2 ⟨sub4_656, List.forall_mem_cons.2 ⟨sub4_657, List.forall_mem_cons.2 ⟨sub4_658, List.forall_mem_cons.2 ⟨sub4_659, List.forall_mem_cons.2 ⟨sub4_660, List.forall_mem_cons.2 ⟨sub4_661, List.forall_mem_cons.2 ⟨sub4_662, List.forall_mem_cons.2 ⟨sub4_663, List.forall_mem_cons.2 ⟨sub4_664, List.forall_mem_cons.2 ⟨sub4_665, List.forall_mem_cons.2 ⟨sub4_666, List.forall_mem_cons.2 ⟨sub4_667, List.forall_mem_cons.2 ⟨sub4_668, List.forall_mem_cons.2 ⟨sub4_669, List.forall_mem_cons.2 ⟨sub4_670, List.forall_mem_cons.2 ⟨sub4_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_672 : sub4 [2, -1, 5] = true := by decide +kernel
theorem sub4_673 : sub4 [2, -1, 6] = true := by decide +kernel
theorem sub4_674 : sub4 [2, -1, 7] = true := by decide +kernel
theorem sub4_675 : sub4 [2, -1, 8] = true := by decide +kernel
theorem sub4_676 : sub4 [2, -1, 9] = true := by decide +kernel
theorem sub4_677 : sub4 [2, 0, -11] = true := by decide +kernel
theorem sub4_678 : sub4 [2, 0, -10] = true := by decide +kernel
theorem sub4_679 : sub4 [2, 0, -9] = true := by decide +kernel
theorem sub4_680 : sub4 [2, 0, -8] = true := by decide +kernel
theorem sub4_681 : sub4 [2, 0, -7] = true := by decide +kernel
theorem sub4_682 : sub4 [2, 0, -6] = true := by decide +kernel
theorem sub4_683 : sub4 [2, 0, -5] = true := by decide +kernel
theorem sub4_684 : sub4 [2, 0, -4] = true := by decide +kernel
theorem sub4_685 : sub4 [2, 0, -3] = true := by decide +kernel
theorem sub4_686 : sub4 [2, 0, -2] = true := by decide +kernel
theorem sub4_687 : sub4 [2, 0, -1] = true := by decide +kernel
theorem sub4_688 : sub4 [2, 0, 0] = true := by decide +kernel
theorem sub4_689 : sub4 [2, 0, 1] = true := by decide +kernel
theorem sub4_690 : sub4 [2, 0, 2] = true := by decide +kernel
theorem sub4_691 : sub4 [2, 0, 3] = true := by decide +kernel
theorem sub4_692 : sub4 [2, 0, 4] = true := by decide +kernel
theorem sub4_693 : sub4 [2, 0, 5] = true := by decide +kernel
theorem sub4_694 : sub4 [2, 0, 6] = true := by decide +kernel
theorem sub4_695 : sub4 [2, 0, 7] = true := by decide +kernel
theorem sub4_696 : sub4 [2, 0, 8] = true := by decide +kernel
theorem sub4_697 : sub4 [2, 0, 9] = true := by decide +kernel
theorem sub4_698 : sub4 [2, 1, -10] = true := by decide +kernel
theorem sub4_699 : sub4 [2, 1, -9] = true := by decide +kernel
theorem sub4_700 : sub4 [2, 1, -8] = true := by decide +kernel
theorem sub4_701 : sub4 [2, 1, -7] = true := by decide +kernel
theorem sub4_702 : sub4 [2, 1, -6] = true := by decide +kernel
theorem sub4_703 : sub4 [2, 1, -5] = true := by decide +kernel
theorem sb4_21 : ∀ q ∈ blk4_21, sub4 q = true := by
  unfold blk4_21
  exact List.forall_mem_cons.2 ⟨sub4_672, List.forall_mem_cons.2 ⟨sub4_673, List.forall_mem_cons.2 ⟨sub4_674, List.forall_mem_cons.2 ⟨sub4_675, List.forall_mem_cons.2 ⟨sub4_676, List.forall_mem_cons.2 ⟨sub4_677, List.forall_mem_cons.2 ⟨sub4_678, List.forall_mem_cons.2 ⟨sub4_679, List.forall_mem_cons.2 ⟨sub4_680, List.forall_mem_cons.2 ⟨sub4_681, List.forall_mem_cons.2 ⟨sub4_682, List.forall_mem_cons.2 ⟨sub4_683, List.forall_mem_cons.2 ⟨sub4_684, List.forall_mem_cons.2 ⟨sub4_685, List.forall_mem_cons.2 ⟨sub4_686, List.forall_mem_cons.2 ⟨sub4_687, List.forall_mem_cons.2 ⟨sub4_688, List.forall_mem_cons.2 ⟨sub4_689, List.forall_mem_cons.2 ⟨sub4_690, List.forall_mem_cons.2 ⟨sub4_691, List.forall_mem_cons.2 ⟨sub4_692, List.forall_mem_cons.2 ⟨sub4_693, List.forall_mem_cons.2 ⟨sub4_694, List.forall_mem_cons.2 ⟨sub4_695, List.forall_mem_cons.2 ⟨sub4_696, List.forall_mem_cons.2 ⟨sub4_697, List.forall_mem_cons.2 ⟨sub4_698, List.forall_mem_cons.2 ⟨sub4_699, List.forall_mem_cons.2 ⟨sub4_700, List.forall_mem_cons.2 ⟨sub4_701, List.forall_mem_cons.2 ⟨sub4_702, List.forall_mem_cons.2 ⟨sub4_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_704 : sub4 [2, 1, -4] = true := by decide +kernel
theorem sub4_705 : sub4 [2, 1, -3] = true := by decide +kernel
theorem sub4_706 : sub4 [2, 1, -2] = true := by decide +kernel
theorem sub4_707 : sub4 [2, 1, -1] = true := by decide +kernel
theorem sub4_708 : sub4 [2, 1, 0] = true := by decide +kernel
theorem sub4_709 : sub4 [2, 1, 1] = true := by decide +kernel
theorem sub4_710 : sub4 [2, 1, 2] = true := by decide +kernel
theorem sub4_711 : sub4 [2, 1, 3] = true := by decide +kernel
theorem sub4_712 : sub4 [2, 1, 4] = true := by decide +kernel
theorem sub4_713 : sub4 [2, 1, 5] = true := by decide +kernel
theorem sub4_714 : sub4 [2, 1, 6] = true := by decide +kernel
theorem sub4_715 : sub4 [2, 1, 7] = true := by decide +kernel
theorem sub4_716 : sub4 [2, 1, 8] = true := by decide +kernel
theorem sub4_717 : sub4 [2, 2, -9] = true := by decide +kernel
theorem sub4_718 : sub4 [2, 2, -8] = true := by decide +kernel
theorem sub4_719 : sub4 [2, 2, -7] = true := by decide +kernel
theorem sub4_720 : sub4 [2, 2, -6] = true := by decide +kernel
theorem sub4_721 : sub4 [2, 2, -5] = true := by decide +kernel
theorem sub4_722 : sub4 [2, 2, -4] = true := by decide +kernel
theorem sub4_723 : sub4 [2, 2, -3] = true := by decide +kernel
theorem sub4_724 : sub4 [2, 2, -2] = true := by decide +kernel
theorem sub4_725 : sub4 [2, 2, -1] = true := by decide +kernel
theorem sub4_726 : sub4 [2, 2, 0] = true := by decide +kernel
theorem sub4_727 : sub4 [2, 2, 1] = true := by decide +kernel
theorem sub4_728 : sub4 [2, 2, 2] = true := by decide +kernel
theorem sub4_729 : sub4 [2, 2, 3] = true := by decide +kernel
theorem sub4_730 : sub4 [2, 2, 4] = true := by decide +kernel
theorem sub4_731 : sub4 [2, 2, 5] = true := by decide +kernel
theorem sub4_732 : sub4 [2, 2, 6] = true := by decide +kernel
theorem sub4_733 : sub4 [2, 2, 7] = true := by decide +kernel
theorem sub4_734 : sub4 [2, 3] = true := by decide +kernel
theorem sub4_735 : sub4 [3, -4] = true := by decide +kernel
theorem sb4_22 : ∀ q ∈ blk4_22, sub4 q = true := by
  unfold blk4_22
  exact List.forall_mem_cons.2 ⟨sub4_704, List.forall_mem_cons.2 ⟨sub4_705, List.forall_mem_cons.2 ⟨sub4_706, List.forall_mem_cons.2 ⟨sub4_707, List.forall_mem_cons.2 ⟨sub4_708, List.forall_mem_cons.2 ⟨sub4_709, List.forall_mem_cons.2 ⟨sub4_710, List.forall_mem_cons.2 ⟨sub4_711, List.forall_mem_cons.2 ⟨sub4_712, List.forall_mem_cons.2 ⟨sub4_713, List.forall_mem_cons.2 ⟨sub4_714, List.forall_mem_cons.2 ⟨sub4_715, List.forall_mem_cons.2 ⟨sub4_716, List.forall_mem_cons.2 ⟨sub4_717, List.forall_mem_cons.2 ⟨sub4_718, List.forall_mem_cons.2 ⟨sub4_719, List.forall_mem_cons.2 ⟨sub4_720, List.forall_mem_cons.2 ⟨sub4_721, List.forall_mem_cons.2 ⟨sub4_722, List.forall_mem_cons.2 ⟨sub4_723, List.forall_mem_cons.2 ⟨sub4_724, List.forall_mem_cons.2 ⟨sub4_725, List.forall_mem_cons.2 ⟨sub4_726, List.forall_mem_cons.2 ⟨sub4_727, List.forall_mem_cons.2 ⟨sub4_728, List.forall_mem_cons.2 ⟨sub4_729, List.forall_mem_cons.2 ⟨sub4_730, List.forall_mem_cons.2 ⟨sub4_731, List.forall_mem_cons.2 ⟨sub4_732, List.forall_mem_cons.2 ⟨sub4_733, List.forall_mem_cons.2 ⟨sub4_734, List.forall_mem_cons.2 ⟨sub4_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_736 : sub4 [3, -3] = true := by decide +kernel
theorem sub4_737 : sub4 [3, -2, -8] = true := by decide +kernel
theorem sub4_738 : sub4 [3, -2, -7] = true := by decide +kernel
theorem sub4_739 : sub4 [3, -2, -6] = true := by decide +kernel
theorem sub4_740 : sub4 [3, -2, -5] = true := by decide +kernel
theorem sub4_741 : sub4 [3, -2, -4] = true := by decide +kernel
theorem sub4_742 : sub4 [3, -2, -3] = true := by decide +kernel
theorem sub4_743 : sub4 [3, -2, -2] = true := by decide +kernel
theorem sub4_744 : sub4 [3, -2, -1] = true := by decide +kernel
theorem sub4_745 : sub4 [3, -2, 0] = true := by decide +kernel
theorem sub4_746 : sub4 [3, -2, 1] = true := by decide +kernel
theorem sub4_747 : sub4 [3, -2, 2] = true := by decide +kernel
theorem sub4_748 : sub4 [3, -2, 3] = true := by decide +kernel
theorem sub4_749 : sub4 [3, -2, 4] = true := by decide +kernel
theorem sub4_750 : sub4 [3, -1, -9] = true := by decide +kernel
theorem sub4_751 : sub4 [3, -1, -8] = true := by decide +kernel
theorem sub4_752 : sub4 [3, -1, -7] = true := by decide +kernel
theorem sub4_753 : sub4 [3, -1, -6] = true := by decide +kernel
theorem sub4_754 : sub4 [3, -1, -5] = true := by decide +kernel
theorem sub4_755 : sub4 [3, -1, -4] = true := by decide +kernel
theorem sub4_756 : sub4 [3, -1, -3] = true := by decide +kernel
theorem sub4_757 : sub4 [3, -1, -2] = true := by decide +kernel
theorem sub4_758 : sub4 [3, -1, -1] = true := by decide +kernel
theorem sub4_759 : sub4 [3, -1, 0] = true := by decide +kernel
theorem sub4_760 : sub4 [3, -1, 1] = true := by decide +kernel
theorem sub4_761 : sub4 [3, -1, 2] = true := by decide +kernel
theorem sub4_762 : sub4 [3, -1, 3] = true := by decide +kernel
theorem sub4_763 : sub4 [3, -1, 4] = true := by decide +kernel
theorem sub4_764 : sub4 [3, -1, 5] = true := by decide +kernel
theorem sub4_765 : sub4 [3, -1, 6] = true := by decide +kernel
theorem sub4_766 : sub4 [3, 0, -9] = true := by decide +kernel
theorem sub4_767 : sub4 [3, 0, -8] = true := by decide +kernel
theorem sb4_23 : ∀ q ∈ blk4_23, sub4 q = true := by
  unfold blk4_23
  exact List.forall_mem_cons.2 ⟨sub4_736, List.forall_mem_cons.2 ⟨sub4_737, List.forall_mem_cons.2 ⟨sub4_738, List.forall_mem_cons.2 ⟨sub4_739, List.forall_mem_cons.2 ⟨sub4_740, List.forall_mem_cons.2 ⟨sub4_741, List.forall_mem_cons.2 ⟨sub4_742, List.forall_mem_cons.2 ⟨sub4_743, List.forall_mem_cons.2 ⟨sub4_744, List.forall_mem_cons.2 ⟨sub4_745, List.forall_mem_cons.2 ⟨sub4_746, List.forall_mem_cons.2 ⟨sub4_747, List.forall_mem_cons.2 ⟨sub4_748, List.forall_mem_cons.2 ⟨sub4_749, List.forall_mem_cons.2 ⟨sub4_750, List.forall_mem_cons.2 ⟨sub4_751, List.forall_mem_cons.2 ⟨sub4_752, List.forall_mem_cons.2 ⟨sub4_753, List.forall_mem_cons.2 ⟨sub4_754, List.forall_mem_cons.2 ⟨sub4_755, List.forall_mem_cons.2 ⟨sub4_756, List.forall_mem_cons.2 ⟨sub4_757, List.forall_mem_cons.2 ⟨sub4_758, List.forall_mem_cons.2 ⟨sub4_759, List.forall_mem_cons.2 ⟨sub4_760, List.forall_mem_cons.2 ⟨sub4_761, List.forall_mem_cons.2 ⟨sub4_762, List.forall_mem_cons.2 ⟨sub4_763, List.forall_mem_cons.2 ⟨sub4_764, List.forall_mem_cons.2 ⟨sub4_765, List.forall_mem_cons.2 ⟨sub4_766, List.forall_mem_cons.2 ⟨sub4_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_768 : sub4 [3, 0, -7] = true := by decide +kernel
theorem sub4_769 : sub4 [3, 0, -6] = true := by decide +kernel
theorem sub4_770 : sub4 [3, 0, -5] = true := by decide +kernel
theorem sub4_771 : sub4 [3, 0, -4] = true := by decide +kernel
theorem sub4_772 : sub4 [3, 0, -3] = true := by decide +kernel
theorem sub4_773 : sub4 [3, 0, -2] = true := by decide +kernel
theorem sub4_774 : sub4 [3, 0, -1] = true := by decide +kernel
theorem sub4_775 : sub4 [3, 0, 0] = true := by decide +kernel
theorem sub4_776 : sub4 [3, 0, 1] = true := by decide +kernel
theorem sub4_777 : sub4 [3, 0, 2] = true := by decide +kernel
theorem sub4_778 : sub4 [3, 0, 3] = true := by decide +kernel
theorem sub4_779 : sub4 [3, 0, 4] = true := by decide +kernel
theorem sub4_780 : sub4 [3, 0, 5] = true := by decide +kernel
theorem sub4_781 : sub4 [3, 0, 6] = true := by decide +kernel
theorem sub4_782 : sub4 [3, 1, -8] = true := by decide +kernel
theorem sub4_783 : sub4 [3, 1, -7] = true := by decide +kernel
theorem sub4_784 : sub4 [3, 1, -6] = true := by decide +kernel
theorem sub4_785 : sub4 [3, 1, -5] = true := by decide +kernel
theorem sub4_786 : sub4 [3, 1, -4] = true := by decide +kernel
theorem sub4_787 : sub4 [3, 1, -3] = true := by decide +kernel
theorem sub4_788 : sub4 [3, 1, -2] = true := by decide +kernel
theorem sub4_789 : sub4 [3, 1, -1] = true := by decide +kernel
theorem sub4_790 : sub4 [3, 1, 0] = true := by decide +kernel
theorem sub4_791 : sub4 [3, 1, 1] = true := by decide +kernel
theorem sub4_792 : sub4 [3, 1, 2] = true := by decide +kernel
theorem sub4_793 : sub4 [3, 1, 3] = true := by decide +kernel
theorem sub4_794 : sub4 [3, 1, 4] = true := by decide +kernel
theorem sub4_795 : sub4 [3, 1, 5] = true := by decide +kernel
theorem sub4_796 : sub4 [3, 2] = true := by decide +kernel
theorem sb4_24 : ∀ q ∈ blk4_24, sub4 q = true := by
  unfold blk4_24
  exact List.forall_mem_cons.2 ⟨sub4_768, List.forall_mem_cons.2 ⟨sub4_769, List.forall_mem_cons.2 ⟨sub4_770, List.forall_mem_cons.2 ⟨sub4_771, List.forall_mem_cons.2 ⟨sub4_772, List.forall_mem_cons.2 ⟨sub4_773, List.forall_mem_cons.2 ⟨sub4_774, List.forall_mem_cons.2 ⟨sub4_775, List.forall_mem_cons.2 ⟨sub4_776, List.forall_mem_cons.2 ⟨sub4_777, List.forall_mem_cons.2 ⟨sub4_778, List.forall_mem_cons.2 ⟨sub4_779, List.forall_mem_cons.2 ⟨sub4_780, List.forall_mem_cons.2 ⟨sub4_781, List.forall_mem_cons.2 ⟨sub4_782, List.forall_mem_cons.2 ⟨sub4_783, List.forall_mem_cons.2 ⟨sub4_784, List.forall_mem_cons.2 ⟨sub4_785, List.forall_mem_cons.2 ⟨sub4_786, List.forall_mem_cons.2 ⟨sub4_787, List.forall_mem_cons.2 ⟨sub4_788, List.forall_mem_cons.2 ⟨sub4_789, List.forall_mem_cons.2 ⟨sub4_790, List.forall_mem_cons.2 ⟨sub4_791, List.forall_mem_cons.2 ⟨sub4_792, List.forall_mem_cons.2 ⟨sub4_793, List.forall_mem_cons.2 ⟨sub4_794, List.forall_mem_cons.2 ⟨sub4_795, List.forall_mem_cons.2 ⟨sub4_796, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_0 : sub5 [-6] = true := by decide +kernel
theorem sub5_1 : sub5 [-5, -3] = true := by decide +kernel
theorem sub5_2 : sub5 [-5, -2] = true := by decide +kernel
theorem sub5_3 : sub5 [-5, -1] = true := by decide +kernel
theorem sub5_4 : sub5 [-5, 0] = true := by decide +kernel
theorem sub5_5 : sub5 [-5, 1] = true := by decide +kernel
theorem sub5_6 : sub5 [-5, 2] = true := by decide +kernel
theorem sub5_7 : sub5 [-5, 3] = true := by decide +kernel
theorem sub5_8 : sub5 [-5, 4] = true := by decide +kernel
theorem sub5_9 : sub5 [-4, -4] = true := by decide +kernel
theorem sub5_10 : sub5 [-4, -3] = true := by decide +kernel
theorem sub5_11 : sub5 [-4, -2] = true := by decide +kernel
theorem sub5_12 : sub5 [-4, -1] = true := by decide +kernel
theorem sub5_13 : sub5 [-4, 0] = true := by decide +kernel
theorem sub5_14 : sub5 [-4, 1] = true := by decide +kernel
theorem sub5_15 : sub5 [-4, 2] = true := by decide +kernel
theorem sub5_16 : sub5 [-4, 3] = true := by decide +kernel
theorem sub5_17 : sub5 [-4, 4] = true := by decide +kernel
theorem sub5_18 : sub5 [-4, 5] = true := by decide +kernel
theorem sub5_19 : sub5 [-3, -5] = true := by decide +kernel
theorem sub5_20 : sub5 [-3, -4] = true := by decide +kernel
theorem sub5_21 : sub5 [-3, -3] = true := by decide +kernel
theorem sub5_22 : sub5 [-3, -2] = true := by decide +kernel
theorem sub5_23 : sub5 [-3, -1, -9] = true := by decide +kernel
theorem sub5_24 : sub5 [-3, -1, -8] = true := by decide +kernel
theorem sub5_25 : sub5 [-3, -1, -7] = true := by decide +kernel
theorem sub5_26 : sub5 [-3, -1, -6] = true := by decide +kernel
theorem sub5_27 : sub5 [-3, -1, -5] = true := by decide +kernel
theorem sub5_28 : sub5 [-3, -1, -4] = true := by decide +kernel
theorem sub5_29 : sub5 [-3, -1, -3] = true := by decide +kernel
theorem sub5_30 : sub5 [-3, -1, -2] = true := by decide +kernel
theorem sub5_31 : sub5 [-3, -1, -1] = true := by decide +kernel
theorem sb5_0 : ∀ q ∈ blk5_0, sub5 q = true := by
  unfold blk5_0
  exact List.forall_mem_cons.2 ⟨sub5_0, List.forall_mem_cons.2 ⟨sub5_1, List.forall_mem_cons.2 ⟨sub5_2, List.forall_mem_cons.2 ⟨sub5_3, List.forall_mem_cons.2 ⟨sub5_4, List.forall_mem_cons.2 ⟨sub5_5, List.forall_mem_cons.2 ⟨sub5_6, List.forall_mem_cons.2 ⟨sub5_7, List.forall_mem_cons.2 ⟨sub5_8, List.forall_mem_cons.2 ⟨sub5_9, List.forall_mem_cons.2 ⟨sub5_10, List.forall_mem_cons.2 ⟨sub5_11, List.forall_mem_cons.2 ⟨sub5_12, List.forall_mem_cons.2 ⟨sub5_13, List.forall_mem_cons.2 ⟨sub5_14, List.forall_mem_cons.2 ⟨sub5_15, List.forall_mem_cons.2 ⟨sub5_16, List.forall_mem_cons.2 ⟨sub5_17, List.forall_mem_cons.2 ⟨sub5_18, List.forall_mem_cons.2 ⟨sub5_19, List.forall_mem_cons.2 ⟨sub5_20, List.forall_mem_cons.2 ⟨sub5_21, List.forall_mem_cons.2 ⟨sub5_22, List.forall_mem_cons.2 ⟨sub5_23, List.forall_mem_cons.2 ⟨sub5_24, List.forall_mem_cons.2 ⟨sub5_25, List.forall_mem_cons.2 ⟨sub5_26, List.forall_mem_cons.2 ⟨sub5_27, List.forall_mem_cons.2 ⟨sub5_28, List.forall_mem_cons.2 ⟨sub5_29, List.forall_mem_cons.2 ⟨sub5_30, List.forall_mem_cons.2 ⟨sub5_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_32 : sub5 [-3, -1, 0] = true := by decide +kernel
theorem sub5_33 : sub5 [-3, -1, 1] = true := by decide +kernel
theorem sub5_34 : sub5 [-3, -1, 2] = true := by decide +kernel
theorem sub5_35 : sub5 [-3, -1, 3] = true := by decide +kernel
theorem sub5_36 : sub5 [-3, -1, 4] = true := by decide +kernel
theorem sub5_37 : sub5 [-3, -1, 5] = true := by decide +kernel
theorem sub5_38 : sub5 [-3, 0, -9] = true := by decide +kernel
theorem sub5_39 : sub5 [-3, 0, -8] = true := by decide +kernel
theorem sub5_40 : sub5 [-3, 0, -7] = true := by decide +kernel
theorem sub5_41 : sub5 [-3, 0, -6] = true := by decide +kernel
theorem sub5_42 : sub5 [-3, 0, -5] = true := by decide +kernel
theorem sub5_43 : sub5 [-3, 0, -4] = true := by decide +kernel
theorem sub5_44 : sub5 [-3, 0, -3] = true := by decide +kernel
theorem sub5_45 : sub5 [-3, 0, -2] = true := by decide +kernel
theorem sub5_46 : sub5 [-3, 0, -1] = true := by decide +kernel
theorem sub5_47 : sub5 [-3, 0, 0] = true := by decide +kernel
theorem sub5_48 : sub5 [-3, 0, 1] = true := by decide +kernel
theorem sub5_49 : sub5 [-3, 0, 2] = true := by decide +kernel
theorem sub5_50 : sub5 [-3, 0, 3] = true := by decide +kernel
theorem sub5_51 : sub5 [-3, 0, 4] = true := by decide +kernel
theorem sub5_52 : sub5 [-3, 0, 5] = true := by decide +kernel
theorem sub5_53 : sub5 [-3, 1, -8] = true := by decide +kernel
theorem sub5_54 : sub5 [-3, 1, -7] = true := by decide +kernel
theorem sub5_55 : sub5 [-3, 1, -6] = true := by decide +kernel
theorem sub5_56 : sub5 [-3, 1, -5] = true := by decide +kernel
theorem sub5_57 : sub5 [-3, 1, -4] = true := by decide +kernel
theorem sub5_58 : sub5 [-3, 1, -3] = true := by decide +kernel
theorem sub5_59 : sub5 [-3, 1, -2] = true := by decide +kernel
theorem sub5_60 : sub5 [-3, 1, -1] = true := by decide +kernel
theorem sub5_61 : sub5 [-3, 1, 0] = true := by decide +kernel
theorem sub5_62 : sub5 [-3, 1, 1] = true := by decide +kernel
theorem sub5_63 : sub5 [-3, 1, 2] = true := by decide +kernel
theorem sb5_1 : ∀ q ∈ blk5_1, sub5 q = true := by
  unfold blk5_1
  exact List.forall_mem_cons.2 ⟨sub5_32, List.forall_mem_cons.2 ⟨sub5_33, List.forall_mem_cons.2 ⟨sub5_34, List.forall_mem_cons.2 ⟨sub5_35, List.forall_mem_cons.2 ⟨sub5_36, List.forall_mem_cons.2 ⟨sub5_37, List.forall_mem_cons.2 ⟨sub5_38, List.forall_mem_cons.2 ⟨sub5_39, List.forall_mem_cons.2 ⟨sub5_40, List.forall_mem_cons.2 ⟨sub5_41, List.forall_mem_cons.2 ⟨sub5_42, List.forall_mem_cons.2 ⟨sub5_43, List.forall_mem_cons.2 ⟨sub5_44, List.forall_mem_cons.2 ⟨sub5_45, List.forall_mem_cons.2 ⟨sub5_46, List.forall_mem_cons.2 ⟨sub5_47, List.forall_mem_cons.2 ⟨sub5_48, List.forall_mem_cons.2 ⟨sub5_49, List.forall_mem_cons.2 ⟨sub5_50, List.forall_mem_cons.2 ⟨sub5_51, List.forall_mem_cons.2 ⟨sub5_52, List.forall_mem_cons.2 ⟨sub5_53, List.forall_mem_cons.2 ⟨sub5_54, List.forall_mem_cons.2 ⟨sub5_55, List.forall_mem_cons.2 ⟨sub5_56, List.forall_mem_cons.2 ⟨sub5_57, List.forall_mem_cons.2 ⟨sub5_58, List.forall_mem_cons.2 ⟨sub5_59, List.forall_mem_cons.2 ⟨sub5_60, List.forall_mem_cons.2 ⟨sub5_61, List.forall_mem_cons.2 ⟨sub5_62, List.forall_mem_cons.2 ⟨sub5_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C055
