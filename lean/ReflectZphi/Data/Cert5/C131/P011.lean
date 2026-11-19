import ReflectZphi.Data.Cert5.C131.Base

namespace ReflectZphi.Data.Cert5.C131

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd10_0_512 : subd10_0 [-2, 4, 4] = true := by decide +kernel
theorem subd10_0_513 : subd10_0 [-2, 4, 5] = true := by decide +kernel
theorem subd10_0_514 : subd10_0 [-2, 4, 6] = true := by decide +kernel
theorem subd10_0_515 : subd10_0 [-2, 5, -9] = true := by decide +kernel
theorem subd10_0_516 : subd10_0 [-2, 5, -8] = true := by decide +kernel
theorem subd10_0_517 : subd10_0 [-2, 5, -7] = true := by decide +kernel
theorem subd10_0_518 : subd10_0 [-2, 5, -6] = true := by decide +kernel
theorem subd10_0_519 : subd10_0 [-2, 5, -5] = true := by decide +kernel
theorem subd10_0_520 : subd10_0 [-2, 5, -4] = true := by decide +kernel
theorem subd10_0_521 : subd10_0 [-2, 5, -3] = true := by decide +kernel
theorem subd10_0_522 : subd10_0 [-2, 5, -2] = true := by decide +kernel
theorem subd10_0_523 : subd10_0 [-2, 5, -1] = true := by decide +kernel
theorem subd10_0_524 : subd10_0 [-2, 5, 0] = true := by decide +kernel
theorem subd10_0_525 : subd10_0 [-2, 5, 1] = true := by decide +kernel
theorem subd10_0_526 : subd10_0 [-2, 5, 2] = true := by decide +kernel
theorem subd10_0_527 : subd10_0 [-2, 5, 3] = true := by decide +kernel
theorem subd10_0_528 : subd10_0 [-2, 5, 4] = true := by decide +kernel
theorem subd10_0_529 : subd10_0 [-2, 5, 5] = true := by decide +kernel
theorem subd10_0_530 : subd10_0 [-2, 6] = true := by decide +kernel
theorem subd10_0_531 : subd10_0 [-2, 7] = true := by decide +kernel
theorem subd10_0_532 : subd10_0 [-1, -8] = true := by decide +kernel
theorem subd10_0_533 : subd10_0 [-1, -7] = true := by decide +kernel
theorem subd10_0_534 : subd10_0 [-1, -6] = true := by decide +kernel
theorem subd10_0_535 : subd10_0 [-1, -5, -6] = true := by decide +kernel
theorem subd10_0_536 : subd10_0 [-1, -5, -5] = true := by decide +kernel
theorem subd10_0_537 : subd10_0 [-1, -5, -4] = true := by decide +kernel
theorem subd10_0_538 : subd10_0 [-1, -5, -3] = true := by decide +kernel
theorem subd10_0_539 : subd10_0 [-1, -5, -2] = true := by decide +kernel
theorem subd10_0_540 : subd10_0 [-1, -5, -1] = true := by decide +kernel
theorem subd10_0_541 : subd10_0 [-1, -5, 0] = true := by decide +kernel
theorem subd10_0_542 : subd10_0 [-1, -5, 1] = true := by decide +kernel
theorem subd10_0_543 : subd10_0 [-1, -5, 2] = true := by decide +kernel
theorem sbd10_0_16 : ∀ q ∈ blkd10_0_16, subd10_0 q = true := by
  unfold blkd10_0_16
  exact List.forall_mem_cons.2 ⟨subd10_0_512, List.forall_mem_cons.2 ⟨subd10_0_513, List.forall_mem_cons.2 ⟨subd10_0_514, List.forall_mem_cons.2 ⟨subd10_0_515, List.forall_mem_cons.2 ⟨subd10_0_516, List.forall_mem_cons.2 ⟨subd10_0_517, List.forall_mem_cons.2 ⟨subd10_0_518, List.forall_mem_cons.2 ⟨subd10_0_519, List.forall_mem_cons.2 ⟨subd10_0_520, List.forall_mem_cons.2 ⟨subd10_0_521, List.forall_mem_cons.2 ⟨subd10_0_522, List.forall_mem_cons.2 ⟨subd10_0_523, List.forall_mem_cons.2 ⟨subd10_0_524, List.forall_mem_cons.2 ⟨subd10_0_525, List.forall_mem_cons.2 ⟨subd10_0_526, List.forall_mem_cons.2 ⟨subd10_0_527, List.forall_mem_cons.2 ⟨subd10_0_528, List.forall_mem_cons.2 ⟨subd10_0_529, List.forall_mem_cons.2 ⟨subd10_0_530, List.forall_mem_cons.2 ⟨subd10_0_531, List.forall_mem_cons.2 ⟨subd10_0_532, List.forall_mem_cons.2 ⟨subd10_0_533, List.forall_mem_cons.2 ⟨subd10_0_534, List.forall_mem_cons.2 ⟨subd10_0_535, List.forall_mem_cons.2 ⟨subd10_0_536, List.forall_mem_cons.2 ⟨subd10_0_537, List.forall_mem_cons.2 ⟨subd10_0_538, List.forall_mem_cons.2 ⟨subd10_0_539, List.forall_mem_cons.2 ⟨subd10_0_540, List.forall_mem_cons.2 ⟨subd10_0_541, List.forall_mem_cons.2 ⟨subd10_0_542, List.forall_mem_cons.2 ⟨subd10_0_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_544 : subd10_0 [-1, -5, 3] = true := by decide +kernel
theorem subd10_0_545 : subd10_0 [-1, -5, 4] = true := by decide +kernel
theorem subd10_0_546 : subd10_0 [-1, -5, 5] = true := by decide +kernel
theorem subd10_0_547 : subd10_0 [-1, -5, 6] = true := by decide +kernel
theorem subd10_0_548 : subd10_0 [-1, -5, 7] = true := by decide +kernel
theorem subd10_0_549 : subd10_0 [-1, -4, -7] = true := by decide +kernel
theorem subd10_0_550 : subd10_0 [-1, -4, -6] = true := by decide +kernel
theorem subd10_0_551 : subd10_0 [-1, -4, -5] = true := by decide +kernel
theorem subd10_0_552 : subd10_0 [-1, -4, -4] = true := by decide +kernel
theorem subd10_0_553 : subd10_0 [-1, -4, -3] = true := by decide +kernel
theorem subd10_0_554 : subd10_0 [-1, -4, -2] = true := by decide +kernel
theorem subd10_0_555 : subd10_0 [-1, -4, -1] = true := by decide +kernel
theorem subd10_0_556 : subd10_0 [-1, -4, 0] = true := by decide +kernel
theorem subd10_0_557 : subd10_0 [-1, -4, 1] = true := by decide +kernel
theorem subd10_0_558 : subd10_0 [-1, -4, 2] = true := by decide +kernel
theorem subd10_0_559 : subd10_0 [-1, -4, 3] = true := by decide +kernel
theorem subd10_0_560 : subd10_0 [-1, -4, 4] = true := by decide +kernel
theorem subd10_0_561 : subd10_0 [-1, -4, 5] = true := by decide +kernel
theorem subd10_0_562 : subd10_0 [-1, -4, 6] = true := by decide +kernel
theorem subd10_0_563 : subd10_0 [-1, -4, 7] = true := by decide +kernel
theorem subd10_0_564 : subd10_0 [-1, -4, 8] = true := by decide +kernel
theorem subd10_0_565 : subd10_0 [-1, -3, -8] = true := by decide +kernel
theorem subd10_0_566 : subd10_0 [-1, -3, -7] = true := by decide +kernel
theorem subd10_0_567 : subd10_0 [-1, -3, -6] = true := by decide +kernel
theorem subd10_0_568 : subd10_0 [-1, -3, -5] = true := by decide +kernel
theorem subd10_0_569 : subd10_0 [-1, -3, -4] = true := by decide +kernel
theorem subd10_0_570 : subd10_0 [-1, -3, -3] = true := by decide +kernel
theorem subd10_0_571 : subd10_0 [-1, -3, -2] = true := by decide +kernel
theorem subd10_0_572 : subd10_0 [-1, -3, -1] = true := by decide +kernel
theorem subd10_0_573 : subd10_0 [-1, -3, 0] = true := by decide +kernel
theorem subd10_0_574 : subd10_0 [-1, -3, 1] = true := by decide +kernel
theorem subd10_0_575 : subd10_0 [-1, -3, 2] = true := by decide +kernel
theorem sbd10_0_17 : ∀ q ∈ blkd10_0_17, subd10_0 q = true := by
  unfold blkd10_0_17
  exact List.forall_mem_cons.2 ⟨subd10_0_544, List.forall_mem_cons.2 ⟨subd10_0_545, List.forall_mem_cons.2 ⟨subd10_0_546, List.forall_mem_cons.2 ⟨subd10_0_547, List.forall_mem_cons.2 ⟨subd10_0_548, List.forall_mem_cons.2 ⟨subd10_0_549, List.forall_mem_cons.2 ⟨subd10_0_550, List.forall_mem_cons.2 ⟨subd10_0_551, List.forall_mem_cons.2 ⟨subd10_0_552, List.forall_mem_cons.2 ⟨subd10_0_553, List.forall_mem_cons.2 ⟨subd10_0_554, List.forall_mem_cons.2 ⟨subd10_0_555, List.forall_mem_cons.2 ⟨subd10_0_556, List.forall_mem_cons.2 ⟨subd10_0_557, List.forall_mem_cons.2 ⟨subd10_0_558, List.forall_mem_cons.2 ⟨subd10_0_559, List.forall_mem_cons.2 ⟨subd10_0_560, List.forall_mem_cons.2 ⟨subd10_0_561, List.forall_mem_cons.2 ⟨subd10_0_562, List.forall_mem_cons.2 ⟨subd10_0_563, List.forall_mem_cons.2 ⟨subd10_0_564, List.forall_mem_cons.2 ⟨subd10_0_565, List.forall_mem_cons.2 ⟨subd10_0_566, List.forall_mem_cons.2 ⟨subd10_0_567, List.forall_mem_cons.2 ⟨subd10_0_568, List.forall_mem_cons.2 ⟨subd10_0_569, List.forall_mem_cons.2 ⟨subd10_0_570, List.forall_mem_cons.2 ⟨subd10_0_571, List.forall_mem_cons.2 ⟨subd10_0_572, List.forall_mem_cons.2 ⟨subd10_0_573, List.forall_mem_cons.2 ⟨subd10_0_574, List.forall_mem_cons.2 ⟨subd10_0_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_576 : subd10_0 [-1, -3, 3] = true := by decide +kernel
theorem subd10_0_577 : subd10_0 [-1, -3, 4] = true := by decide +kernel
theorem subd10_0_578 : subd10_0 [-1, -3, 5] = true := by decide +kernel
theorem subd10_0_579 : subd10_0 [-1, -3, 6] = true := by decide +kernel
theorem subd10_0_580 : subd10_0 [-1, -3, 7] = true := by decide +kernel
theorem subd10_0_581 : subd10_0 [-1, -3, 8] = true := by decide +kernel
theorem subd10_0_582 : subd10_0 [-1, -2, -9] = true := by decide +kernel
theorem subd10_0_583 : subd10_0 [-1, -2, -8] = true := by decide +kernel
theorem subd10_0_584 : subd10_0 [-1, -2, -7] = true := by decide +kernel
theorem subd10_0_585 : subd10_0 [-1, -2, -6] = true := by decide +kernel
theorem subd10_0_586 : subd10_0 [-1, -2, -5] = true := by decide +kernel
theorem subd10_0_587 : subd10_0 [-1, -2, -4] = true := by decide +kernel
theorem subd10_0_588 : subd10_0 [-1, -2, -3] = true := by decide +kernel
theorem subd10_0_589 : subd10_0 [-1, -2, -2] = true := by decide +kernel
theorem subd10_0_590 : subd10_0 [-1, -2, -1] = true := by decide +kernel
theorem subd10_0_591 : subd10_0 [-1, -2, 0] = true := by decide +kernel
theorem subd10_0_592 : subd10_0 [-1, -2, 1] = true := by decide +kernel
theorem subd10_0_593 : subd10_0 [-1, -2, 2] = true := by decide +kernel
theorem subd10_0_594 : subd10_0 [-1, -2, 3] = true := by decide +kernel
theorem subd10_0_595 : subd10_0 [-1, -2, 4] = true := by decide +kernel
theorem subd10_0_596 : subd10_0 [-1, -2, 5] = true := by decide +kernel
theorem subd10_0_597 : subd10_0 [-1, -2, 6] = true := by decide +kernel
theorem subd10_0_598 : subd10_0 [-1, -2, 7] = true := by decide +kernel
theorem subd10_0_599 : subd10_0 [-1, -2, 8] = true := by decide +kernel
theorem subd10_0_600 : subd10_0 [-1, -1, -9] = true := by decide +kernel
theorem subd10_0_601 : subd10_0 [-1, -1, -8] = true := by decide +kernel
theorem subd10_0_602 : subd10_0 [-1, -1, -7] = true := by decide +kernel
theorem subd10_0_603 : subd10_0 [-1, -1, -6] = true := by decide +kernel
theorem subd10_0_604 : subd10_0 [-1, -1, -5] = true := by decide +kernel
theorem subd10_0_605 : subd10_0 [-1, -1, -4] = true := by decide +kernel
theorem subd10_0_606 : subd10_0 [-1, -1, -3] = true := by decide +kernel
theorem subd10_0_607 : subd10_0 [-1, -1, -2] = true := by decide +kernel
theorem sbd10_0_18 : ∀ q ∈ blkd10_0_18, subd10_0 q = true := by
  unfold blkd10_0_18
  exact List.forall_mem_cons.2 ⟨subd10_0_576, List.forall_mem_cons.2 ⟨subd10_0_577, List.forall_mem_cons.2 ⟨subd10_0_578, List.forall_mem_cons.2 ⟨subd10_0_579, List.forall_mem_cons.2 ⟨subd10_0_580, List.forall_mem_cons.2 ⟨subd10_0_581, List.forall_mem_cons.2 ⟨subd10_0_582, List.forall_mem_cons.2 ⟨subd10_0_583, List.forall_mem_cons.2 ⟨subd10_0_584, List.forall_mem_cons.2 ⟨subd10_0_585, List.forall_mem_cons.2 ⟨subd10_0_586, List.forall_mem_cons.2 ⟨subd10_0_587, List.forall_mem_cons.2 ⟨subd10_0_588, List.forall_mem_cons.2 ⟨subd10_0_589, List.forall_mem_cons.2 ⟨subd10_0_590, List.forall_mem_cons.2 ⟨subd10_0_591, List.forall_mem_cons.2 ⟨subd10_0_592, List.forall_mem_cons.2 ⟨subd10_0_593, List.forall_mem_cons.2 ⟨subd10_0_594, List.forall_mem_cons.2 ⟨subd10_0_595, List.forall_mem_cons.2 ⟨subd10_0_596, List.forall_mem_cons.2 ⟨subd10_0_597, List.forall_mem_cons.2 ⟨subd10_0_598, List.forall_mem_cons.2 ⟨subd10_0_599, List.forall_mem_cons.2 ⟨subd10_0_600, List.forall_mem_cons.2 ⟨subd10_0_601, List.forall_mem_cons.2 ⟨subd10_0_602, List.forall_mem_cons.2 ⟨subd10_0_603, List.forall_mem_cons.2 ⟨subd10_0_604, List.forall_mem_cons.2 ⟨subd10_0_605, List.forall_mem_cons.2 ⟨subd10_0_606, List.forall_mem_cons.2 ⟨subd10_0_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_608 : subd10_0 [-1, -1, -1] = true := by decide +kernel
theorem subd10_0_609 : subd10_0 [-1, -1, 0] = true := by decide +kernel
theorem subd10_0_610 : subd10_0 [-1, -1, 1] = true := by decide +kernel
theorem subd10_0_611 : subd10_0 [-1, -1, 2] = true := by decide +kernel
theorem subd10_0_612 : subd10_0 [-1, -1, 3] = true := by decide +kernel
theorem subd10_0_613 : subd10_0 [-1, -1, 4] = true := by decide +kernel
theorem subd10_0_614 : subd10_0 [-1, -1, 5] = true := by decide +kernel
theorem subd10_0_615 : subd10_0 [-1, -1, 6] = true := by decide +kernel
theorem subd10_0_616 : subd10_0 [-1, -1, 7] = true := by decide +kernel
theorem subd10_0_617 : subd10_0 [-1, -1, 8] = true := by decide +kernel
theorem subd10_0_618 : subd10_0 [-1, 0, -10] = true := by decide +kernel
theorem subd10_0_619 : subd10_0 [-1, 0, -9] = true := by decide +kernel
theorem subd10_0_620 : subd10_0 [-1, 0, -8] = true := by decide +kernel
theorem subd10_0_621 : subd10_0 [-1, 0, -7] = true := by decide +kernel
theorem subd10_0_622 : subd10_0 [-1, 0, -6] = true := by decide +kernel
theorem subd10_0_623 : subd10_0 [-1, 0, -5] = true := by decide +kernel
theorem subd10_0_624 : subd10_0 [-1, 0, -4] = true := by decide +kernel
theorem subd10_0_625 : subd10_0 [-1, 0, -3] = true := by decide +kernel
theorem subd10_0_626 : subd10_0 [-1, 0, -2] = true := by decide +kernel
theorem subd10_0_627 : subd10_0 [-1, 0, -1] = true := by decide +kernel
theorem subd10_0_628 : subd10_0 [-1, 0, 0] = true := by decide +kernel
theorem subd10_0_629 : subd10_0 [-1, 0, 1] = true := by decide +kernel
theorem subd10_0_630 : subd10_0 [-1, 0, 2] = true := by decide +kernel
theorem subd10_0_631 : subd10_0 [-1, 0, 3] = true := by decide +kernel
theorem subd10_0_632 : subd10_0 [-1, 0, 4] = true := by decide +kernel
theorem subd10_0_633 : subd10_0 [-1, 0, 5] = true := by decide +kernel
theorem subd10_0_634 : subd10_0 [-1, 0, 6] = true := by decide +kernel
theorem subd10_0_635 : subd10_0 [-1, 0, 7] = true := by decide +kernel
theorem subd10_0_636 : subd10_0 [-1, 0, 8] = true := by decide +kernel
theorem subd10_0_637 : subd10_0 [-1, 1, -10] = true := by decide +kernel
theorem subd10_0_638 : subd10_0 [-1, 1, -9] = true := by decide +kernel
theorem subd10_0_639 : subd10_0 [-1, 1, -8] = true := by decide +kernel
theorem sbd10_0_19 : ∀ q ∈ blkd10_0_19, subd10_0 q = true := by
  unfold blkd10_0_19
  exact List.forall_mem_cons.2 ⟨subd10_0_608, List.forall_mem_cons.2 ⟨subd10_0_609, List.forall_mem_cons.2 ⟨subd10_0_610, List.forall_mem_cons.2 ⟨subd10_0_611, List.forall_mem_cons.2 ⟨subd10_0_612, List.forall_mem_cons.2 ⟨subd10_0_613, List.forall_mem_cons.2 ⟨subd10_0_614, List.forall_mem_cons.2 ⟨subd10_0_615, List.forall_mem_cons.2 ⟨subd10_0_616, List.forall_mem_cons.2 ⟨subd10_0_617, List.forall_mem_cons.2 ⟨subd10_0_618, List.forall_mem_cons.2 ⟨subd10_0_619, List.forall_mem_cons.2 ⟨subd10_0_620, List.forall_mem_cons.2 ⟨subd10_0_621, List.forall_mem_cons.2 ⟨subd10_0_622, List.forall_mem_cons.2 ⟨subd10_0_623, List.forall_mem_cons.2 ⟨subd10_0_624, List.forall_mem_cons.2 ⟨subd10_0_625, List.forall_mem_cons.2 ⟨subd10_0_626, List.forall_mem_cons.2 ⟨subd10_0_627, List.forall_mem_cons.2 ⟨subd10_0_628, List.forall_mem_cons.2 ⟨subd10_0_629, List.forall_mem_cons.2 ⟨subd10_0_630, List.forall_mem_cons.2 ⟨subd10_0_631, List.forall_mem_cons.2 ⟨subd10_0_632, List.forall_mem_cons.2 ⟨subd10_0_633, List.forall_mem_cons.2 ⟨subd10_0_634, List.forall_mem_cons.2 ⟨subd10_0_635, List.forall_mem_cons.2 ⟨subd10_0_636, List.forall_mem_cons.2 ⟨subd10_0_637, List.forall_mem_cons.2 ⟨subd10_0_638, List.forall_mem_cons.2 ⟨subd10_0_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_640 : subd10_0 [-1, 1, -7] = true := by decide +kernel
theorem subd10_0_641 : subd10_0 [-1, 1, -6] = true := by decide +kernel
theorem subd10_0_642 : subd10_0 [-1, 1, -5] = true := by decide +kernel
theorem subd10_0_643 : subd10_0 [-1, 1, -4] = true := by decide +kernel
theorem subd10_0_644 : subd10_0 [-1, 1, -3] = true := by decide +kernel
theorem subd10_0_645 : subd10_0 [-1, 1, -2] = true := by decide +kernel
theorem subd10_0_646 : subd10_0 [-1, 1, -1] = true := by decide +kernel
theorem subd10_0_647 : subd10_0 [-1, 1, 0] = true := by decide +kernel
theorem subd10_0_648 : subd10_0 [-1, 1, 1] = true := by decide +kernel
theorem subd10_0_649 : subd10_0 [-1, 1, 2] = true := by decide +kernel
theorem subd10_0_650 : subd10_0 [-1, 1, 3] = true := by decide +kernel
theorem subd10_0_651 : subd10_0 [-1, 1, 4] = true := by decide +kernel
theorem subd10_0_652 : subd10_0 [-1, 1, 5] = true := by decide +kernel
theorem subd10_0_653 : subd10_0 [-1, 1, 6] = true := by decide +kernel
theorem subd10_0_654 : subd10_0 [-1, 1, 7] = true := by decide +kernel
theorem subd10_0_655 : subd10_0 [-1, 1, 8] = true := by decide +kernel
theorem subd10_0_656 : subd10_0 [-1, 2, -10] = true := by decide +kernel
theorem subd10_0_657 : subd10_0 [-1, 2, -9] = true := by decide +kernel
theorem subd10_0_658 : subd10_0 [-1, 2, -8] = true := by decide +kernel
theorem subd10_0_659 : subd10_0 [-1, 2, -7] = true := by decide +kernel
theorem subd10_0_660 : subd10_0 [-1, 2, -6] = true := by decide +kernel
theorem subd10_0_661 : subd10_0 [-1, 2, -5] = true := by decide +kernel
theorem subd10_0_662 : subd10_0 [-1, 2, -4] = true := by decide +kernel
theorem subd10_0_663 : subd10_0 [-1, 2, -3] = true := by decide +kernel
theorem subd10_0_664 : subd10_0 [-1, 2, -2] = true := by decide +kernel
theorem subd10_0_665 : subd10_0 [-1, 2, -1] = true := by decide +kernel
theorem subd10_0_666 : subd10_0 [-1, 2, 0] = true := by decide +kernel
theorem subd10_0_667 : subd10_0 [-1, 2, 1] = true := by decide +kernel
theorem subd10_0_668 : subd10_0 [-1, 2, 2] = true := by decide +kernel
theorem subd10_0_669 : subd10_0 [-1, 2, 3] = true := by decide +kernel
theorem subd10_0_670 : subd10_0 [-1, 2, 4] = true := by decide +kernel
theorem subd10_0_671 : subd10_0 [-1, 2, 5] = true := by decide +kernel
theorem sbd10_0_20 : ∀ q ∈ blkd10_0_20, subd10_0 q = true := by
  unfold blkd10_0_20
  exact List.forall_mem_cons.2 ⟨subd10_0_640, List.forall_mem_cons.2 ⟨subd10_0_641, List.forall_mem_cons.2 ⟨subd10_0_642, List.forall_mem_cons.2 ⟨subd10_0_643, List.forall_mem_cons.2 ⟨subd10_0_644, List.forall_mem_cons.2 ⟨subd10_0_645, List.forall_mem_cons.2 ⟨subd10_0_646, List.forall_mem_cons.2 ⟨subd10_0_647, List.forall_mem_cons.2 ⟨subd10_0_648, List.forall_mem_cons.2 ⟨subd10_0_649, List.forall_mem_cons.2 ⟨subd10_0_650, List.forall_mem_cons.2 ⟨subd10_0_651, List.forall_mem_cons.2 ⟨subd10_0_652, List.forall_mem_cons.2 ⟨subd10_0_653, List.forall_mem_cons.2 ⟨subd10_0_654, List.forall_mem_cons.2 ⟨subd10_0_655, List.forall_mem_cons.2 ⟨subd10_0_656, List.forall_mem_cons.2 ⟨subd10_0_657, List.forall_mem_cons.2 ⟨subd10_0_658, List.forall_mem_cons.2 ⟨subd10_0_659, List.forall_mem_cons.2 ⟨subd10_0_660, List.forall_mem_cons.2 ⟨subd10_0_661, List.forall_mem_cons.2 ⟨subd10_0_662, List.forall_mem_cons.2 ⟨subd10_0_663, List.forall_mem_cons.2 ⟨subd10_0_664, List.forall_mem_cons.2 ⟨subd10_0_665, List.forall_mem_cons.2 ⟨subd10_0_666, List.forall_mem_cons.2 ⟨subd10_0_667, List.forall_mem_cons.2 ⟨subd10_0_668, List.forall_mem_cons.2 ⟨subd10_0_669, List.forall_mem_cons.2 ⟨subd10_0_670, List.forall_mem_cons.2 ⟨subd10_0_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_672 : subd10_0 [-1, 2, 6] = true := by decide +kernel
theorem subd10_0_673 : subd10_0 [-1, 2, 7] = true := by decide +kernel
theorem subd10_0_674 : subd10_0 [-1, 3, -9] = true := by decide +kernel
theorem subd10_0_675 : subd10_0 [-1, 3, -8] = true := by decide +kernel
theorem subd10_0_676 : subd10_0 [-1, 3, -7] = true := by decide +kernel
theorem subd10_0_677 : subd10_0 [-1, 3, -6] = true := by decide +kernel
theorem subd10_0_678 : subd10_0 [-1, 3, -5] = true := by decide +kernel
theorem subd10_0_679 : subd10_0 [-1, 3, -4] = true := by decide +kernel
theorem subd10_0_680 : subd10_0 [-1, 3, -3] = true := by decide +kernel
theorem subd10_0_681 : subd10_0 [-1, 3, -2] = true := by decide +kernel
theorem subd10_0_682 : subd10_0 [-1, 3, -1] = true := by decide +kernel
theorem subd10_0_683 : subd10_0 [-1, 3, 0] = true := by decide +kernel
theorem subd10_0_684 : subd10_0 [-1, 3, 1] = true := by decide +kernel
theorem subd10_0_685 : subd10_0 [-1, 3, 2] = true := by decide +kernel
theorem subd10_0_686 : subd10_0 [-1, 3, 3] = true := by decide +kernel
theorem subd10_0_687 : subd10_0 [-1, 3, 4] = true := by decide +kernel
theorem subd10_0_688 : subd10_0 [-1, 3, 5] = true := by decide +kernel
theorem subd10_0_689 : subd10_0 [-1, 3, 6] = true := by decide +kernel
theorem subd10_0_690 : subd10_0 [-1, 3, 7] = true := by decide +kernel
theorem subd10_0_691 : subd10_0 [-1, 4, -9] = true := by decide +kernel
theorem subd10_0_692 : subd10_0 [-1, 4, -8] = true := by decide +kernel
theorem subd10_0_693 : subd10_0 [-1, 4, -7] = true := by decide +kernel
theorem subd10_0_694 : subd10_0 [-1, 4, -6] = true := by decide +kernel
theorem subd10_0_695 : subd10_0 [-1, 4, -5] = true := by decide +kernel
theorem subd10_0_696 : subd10_0 [-1, 4, -4] = true := by decide +kernel
theorem subd10_0_697 : subd10_0 [-1, 4, -3] = true := by decide +kernel
theorem subd10_0_698 : subd10_0 [-1, 4, -2] = true := by decide +kernel
theorem subd10_0_699 : subd10_0 [-1, 4, -1] = true := by decide +kernel
theorem subd10_0_700 : subd10_0 [-1, 4, 0] = true := by decide +kernel
theorem subd10_0_701 : subd10_0 [-1, 4, 1] = true := by decide +kernel
theorem subd10_0_702 : subd10_0 [-1, 4, 2] = true := by decide +kernel
theorem subd10_0_703 : subd10_0 [-1, 4, 3] = true := by decide +kernel
theorem sbd10_0_21 : ∀ q ∈ blkd10_0_21, subd10_0 q = true := by
  unfold blkd10_0_21
  exact List.forall_mem_cons.2 ⟨subd10_0_672, List.forall_mem_cons.2 ⟨subd10_0_673, List.forall_mem_cons.2 ⟨subd10_0_674, List.forall_mem_cons.2 ⟨subd10_0_675, List.forall_mem_cons.2 ⟨subd10_0_676, List.forall_mem_cons.2 ⟨subd10_0_677, List.forall_mem_cons.2 ⟨subd10_0_678, List.forall_mem_cons.2 ⟨subd10_0_679, List.forall_mem_cons.2 ⟨subd10_0_680, List.forall_mem_cons.2 ⟨subd10_0_681, List.forall_mem_cons.2 ⟨subd10_0_682, List.forall_mem_cons.2 ⟨subd10_0_683, List.forall_mem_cons.2 ⟨subd10_0_684, List.forall_mem_cons.2 ⟨subd10_0_685, List.forall_mem_cons.2 ⟨subd10_0_686, List.forall_mem_cons.2 ⟨subd10_0_687, List.forall_mem_cons.2 ⟨subd10_0_688, List.forall_mem_cons.2 ⟨subd10_0_689, List.forall_mem_cons.2 ⟨subd10_0_690, List.forall_mem_cons.2 ⟨subd10_0_691, List.forall_mem_cons.2 ⟨subd10_0_692, List.forall_mem_cons.2 ⟨subd10_0_693, List.forall_mem_cons.2 ⟨subd10_0_694, List.forall_mem_cons.2 ⟨subd10_0_695, List.forall_mem_cons.2 ⟨subd10_0_696, List.forall_mem_cons.2 ⟨subd10_0_697, List.forall_mem_cons.2 ⟨subd10_0_698, List.forall_mem_cons.2 ⟨subd10_0_699, List.forall_mem_cons.2 ⟨subd10_0_700, List.forall_mem_cons.2 ⟨subd10_0_701, List.forall_mem_cons.2 ⟨subd10_0_702, List.forall_mem_cons.2 ⟨subd10_0_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_704 : subd10_0 [-1, 4, 4] = true := by decide +kernel
theorem subd10_0_705 : subd10_0 [-1, 4, 5] = true := by decide +kernel
theorem subd10_0_706 : subd10_0 [-1, 4, 6] = true := by decide +kernel
theorem subd10_0_707 : subd10_0 [-1, 5, -9] = true := by decide +kernel
theorem subd10_0_708 : subd10_0 [-1, 5, -8] = true := by decide +kernel
theorem subd10_0_709 : subd10_0 [-1, 5, -7] = true := by decide +kernel
theorem subd10_0_710 : subd10_0 [-1, 5, -6] = true := by decide +kernel
theorem subd10_0_711 : subd10_0 [-1, 5, -5] = true := by decide +kernel
theorem subd10_0_712 : subd10_0 [-1, 5, -4] = true := by decide +kernel
theorem subd10_0_713 : subd10_0 [-1, 5, -3] = true := by decide +kernel
theorem subd10_0_714 : subd10_0 [-1, 5, -2] = true := by decide +kernel
theorem subd10_0_715 : subd10_0 [-1, 5, -1] = true := by decide +kernel
theorem subd10_0_716 : subd10_0 [-1, 5, 0] = true := by decide +kernel
theorem subd10_0_717 : subd10_0 [-1, 5, 1] = true := by decide +kernel
theorem subd10_0_718 : subd10_0 [-1, 5, 2] = true := by decide +kernel
theorem subd10_0_719 : subd10_0 [-1, 5, 3] = true := by decide +kernel
theorem subd10_0_720 : subd10_0 [-1, 5, 4] = true := by decide +kernel
theorem subd10_0_721 : subd10_0 [-1, 5, 5] = true := by decide +kernel
theorem subd10_0_722 : subd10_0 [-1, 6] = true := by decide +kernel
theorem subd10_0_723 : subd10_0 [-1, 7] = true := by decide +kernel
theorem subd10_0_724 : subd10_0 [0, -8] = true := by decide +kernel
theorem subd10_0_725 : subd10_0 [0, -7] = true := by decide +kernel
theorem subd10_0_726 : subd10_0 [0, -6] = true := by decide +kernel
theorem subd10_0_727 : subd10_0 [0, -5, -6] = true := by decide +kernel
theorem subd10_0_728 : subd10_0 [0, -5, -5] = true := by decide +kernel
theorem subd10_0_729 : subd10_0 [0, -5, -4] = true := by decide +kernel
theorem subd10_0_730 : subd10_0 [0, -5, -3] = true := by decide +kernel
theorem subd10_0_731 : subd10_0 [0, -5, -2] = true := by decide +kernel
theorem subd10_0_732 : subd10_0 [0, -5, -1] = true := by decide +kernel
theorem subd10_0_733 : subd10_0 [0, -5, 0] = true := by decide +kernel
theorem subd10_0_734 : subd10_0 [0, -5, 1] = true := by decide +kernel
theorem subd10_0_735 : subd10_0 [0, -5, 2] = true := by decide +kernel
theorem sbd10_0_22 : ∀ q ∈ blkd10_0_22, subd10_0 q = true := by
  unfold blkd10_0_22
  exact List.forall_mem_cons.2 ⟨subd10_0_704, List.forall_mem_cons.2 ⟨subd10_0_705, List.forall_mem_cons.2 ⟨subd10_0_706, List.forall_mem_cons.2 ⟨subd10_0_707, List.forall_mem_cons.2 ⟨subd10_0_708, List.forall_mem_cons.2 ⟨subd10_0_709, List.forall_mem_cons.2 ⟨subd10_0_710, List.forall_mem_cons.2 ⟨subd10_0_711, List.forall_mem_cons.2 ⟨subd10_0_712, List.forall_mem_cons.2 ⟨subd10_0_713, List.forall_mem_cons.2 ⟨subd10_0_714, List.forall_mem_cons.2 ⟨subd10_0_715, List.forall_mem_cons.2 ⟨subd10_0_716, List.forall_mem_cons.2 ⟨subd10_0_717, List.forall_mem_cons.2 ⟨subd10_0_718, List.forall_mem_cons.2 ⟨subd10_0_719, List.forall_mem_cons.2 ⟨subd10_0_720, List.forall_mem_cons.2 ⟨subd10_0_721, List.forall_mem_cons.2 ⟨subd10_0_722, List.forall_mem_cons.2 ⟨subd10_0_723, List.forall_mem_cons.2 ⟨subd10_0_724, List.forall_mem_cons.2 ⟨subd10_0_725, List.forall_mem_cons.2 ⟨subd10_0_726, List.forall_mem_cons.2 ⟨subd10_0_727, List.forall_mem_cons.2 ⟨subd10_0_728, List.forall_mem_cons.2 ⟨subd10_0_729, List.forall_mem_cons.2 ⟨subd10_0_730, List.forall_mem_cons.2 ⟨subd10_0_731, List.forall_mem_cons.2 ⟨subd10_0_732, List.forall_mem_cons.2 ⟨subd10_0_733, List.forall_mem_cons.2 ⟨subd10_0_734, List.forall_mem_cons.2 ⟨subd10_0_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_736 : subd10_0 [0, -5, 3] = true := by decide +kernel
theorem subd10_0_737 : subd10_0 [0, -5, 4] = true := by decide +kernel
theorem subd10_0_738 : subd10_0 [0, -5, 5] = true := by decide +kernel
theorem subd10_0_739 : subd10_0 [0, -5, 6] = true := by decide +kernel
theorem subd10_0_740 : subd10_0 [0, -5, 7] = true := by decide +kernel
theorem subd10_0_741 : subd10_0 [0, -4, -7] = true := by decide +kernel
theorem subd10_0_742 : subd10_0 [0, -4, -6] = true := by decide +kernel
theorem subd10_0_743 : subd10_0 [0, -4, -5] = true := by decide +kernel
theorem subd10_0_744 : subd10_0 [0, -4, -4] = true := by decide +kernel
theorem subd10_0_745 : subd10_0 [0, -4, -3] = true := by decide +kernel
theorem subd10_0_746 : subd10_0 [0, -4, -2] = true := by decide +kernel
theorem subd10_0_747 : subd10_0 [0, -4, -1] = true := by decide +kernel
theorem subd10_0_748 : subd10_0 [0, -4, 0] = true := by decide +kernel
theorem subd10_0_749 : subd10_0 [0, -4, 1] = true := by decide +kernel
theorem subd10_0_750 : subd10_0 [0, -4, 2] = true := by decide +kernel
theorem subd10_0_751 : subd10_0 [0, -4, 3] = true := by decide +kernel
theorem subd10_0_752 : subd10_0 [0, -4, 4] = true := by decide +kernel
theorem subd10_0_753 : subd10_0 [0, -4, 5] = true := by decide +kernel
theorem subd10_0_754 : subd10_0 [0, -4, 6] = true := by decide +kernel
theorem subd10_0_755 : subd10_0 [0, -4, 7] = true := by decide +kernel
theorem subd10_0_756 : subd10_0 [0, -4, 8] = true := by decide +kernel
theorem subd10_0_757 : subd10_0 [0, -3, -8] = true := by decide +kernel
theorem subd10_0_758 : subd10_0 [0, -3, -7] = true := by decide +kernel
theorem subd10_0_759 : subd10_0 [0, -3, -6] = true := by decide +kernel
theorem subd10_0_760 : subd10_0 [0, -3, -5] = true := by decide +kernel
theorem subd10_0_761 : subd10_0 [0, -3, -4] = true := by decide +kernel
theorem subd10_0_762 : subd10_0 [0, -3, -3] = true := by decide +kernel
theorem subd10_0_763 : subd10_0 [0, -3, -2] = true := by decide +kernel
theorem subd10_0_764 : subd10_0 [0, -3, -1] = true := by decide +kernel
theorem subd10_0_765 : subd10_0 [0, -3, 0] = true := by decide +kernel
theorem subd10_0_766 : subd10_0 [0, -3, 1] = true := by decide +kernel
theorem subd10_0_767 : subd10_0 [0, -3, 2] = true := by decide +kernel
theorem sbd10_0_23 : ∀ q ∈ blkd10_0_23, subd10_0 q = true := by
  unfold blkd10_0_23
  exact List.forall_mem_cons.2 ⟨subd10_0_736, List.forall_mem_cons.2 ⟨subd10_0_737, List.forall_mem_cons.2 ⟨subd10_0_738, List.forall_mem_cons.2 ⟨subd10_0_739, List.forall_mem_cons.2 ⟨subd10_0_740, List.forall_mem_cons.2 ⟨subd10_0_741, List.forall_mem_cons.2 ⟨subd10_0_742, List.forall_mem_cons.2 ⟨subd10_0_743, List.forall_mem_cons.2 ⟨subd10_0_744, List.forall_mem_cons.2 ⟨subd10_0_745, List.forall_mem_cons.2 ⟨subd10_0_746, List.forall_mem_cons.2 ⟨subd10_0_747, List.forall_mem_cons.2 ⟨subd10_0_748, List.forall_mem_cons.2 ⟨subd10_0_749, List.forall_mem_cons.2 ⟨subd10_0_750, List.forall_mem_cons.2 ⟨subd10_0_751, List.forall_mem_cons.2 ⟨subd10_0_752, List.forall_mem_cons.2 ⟨subd10_0_753, List.forall_mem_cons.2 ⟨subd10_0_754, List.forall_mem_cons.2 ⟨subd10_0_755, List.forall_mem_cons.2 ⟨subd10_0_756, List.forall_mem_cons.2 ⟨subd10_0_757, List.forall_mem_cons.2 ⟨subd10_0_758, List.forall_mem_cons.2 ⟨subd10_0_759, List.forall_mem_cons.2 ⟨subd10_0_760, List.forall_mem_cons.2 ⟨subd10_0_761, List.forall_mem_cons.2 ⟨subd10_0_762, List.forall_mem_cons.2 ⟨subd10_0_763, List.forall_mem_cons.2 ⟨subd10_0_764, List.forall_mem_cons.2 ⟨subd10_0_765, List.forall_mem_cons.2 ⟨subd10_0_766, List.forall_mem_cons.2 ⟨subd10_0_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_768 : subd10_0 [0, -3, 3] = true := by decide +kernel
theorem subd10_0_769 : subd10_0 [0, -3, 4] = true := by decide +kernel
theorem subd10_0_770 : subd10_0 [0, -3, 5] = true := by decide +kernel
theorem subd10_0_771 : subd10_0 [0, -3, 6] = true := by decide +kernel
theorem subd10_0_772 : subd10_0 [0, -3, 7] = true := by decide +kernel
theorem subd10_0_773 : subd10_0 [0, -3, 8] = true := by decide +kernel
theorem subd10_0_774 : subd10_0 [0, -2, -9] = true := by decide +kernel
theorem subd10_0_775 : subd10_0 [0, -2, -8] = true := by decide +kernel
theorem subd10_0_776 : subd10_0 [0, -2, -7] = true := by decide +kernel
theorem subd10_0_777 : subd10_0 [0, -2, -6] = true := by decide +kernel
theorem subd10_0_778 : subd10_0 [0, -2, -5] = true := by decide +kernel
theorem subd10_0_779 : subd10_0 [0, -2, -4] = true := by decide +kernel
theorem subd10_0_780 : subd10_0 [0, -2, -3] = true := by decide +kernel
theorem subd10_0_781 : subd10_0 [0, -2, -2] = true := by decide +kernel
theorem subd10_0_782 : subd10_0 [0, -2, -1] = true := by decide +kernel
theorem subd10_0_783 : subd10_0 [0, -2, 0] = true := by decide +kernel
theorem subd10_0_784 : subd10_0 [0, -2, 1] = true := by decide +kernel
theorem subd10_0_785 : subd10_0 [0, -2, 2] = true := by decide +kernel
theorem subd10_0_786 : subd10_0 [0, -2, 3] = true := by decide +kernel
theorem subd10_0_787 : subd10_0 [0, -2, 4] = true := by decide +kernel
theorem subd10_0_788 : subd10_0 [0, -2, 5] = true := by decide +kernel
theorem subd10_0_789 : subd10_0 [0, -2, 6] = true := by decide +kernel
theorem subd10_0_790 : subd10_0 [0, -2, 7] = true := by decide +kernel
theorem subd10_0_791 : subd10_0 [0, -2, 8] = true := by decide +kernel
theorem subd10_0_792 : subd10_0 [0, -1, -9] = true := by decide +kernel
theorem subd10_0_793 : subd10_0 [0, -1, -8] = true := by decide +kernel
theorem subd10_0_794 : subd10_0 [0, -1, -7] = true := by decide +kernel
theorem subd10_0_795 : subd10_0 [0, -1, -6] = true := by decide +kernel
theorem subd10_0_796 : subd10_0 [0, -1, -5] = true := by decide +kernel
theorem subd10_0_797 : subd10_0 [0, -1, -4] = true := by decide +kernel
theorem subd10_0_798 : subd10_0 [0, -1, -3] = true := by decide +kernel
theorem subd10_0_799 : subd10_0 [0, -1, -2] = true := by decide +kernel
theorem sbd10_0_24 : ∀ q ∈ blkd10_0_24, subd10_0 q = true := by
  unfold blkd10_0_24
  exact List.forall_mem_cons.2 ⟨subd10_0_768, List.forall_mem_cons.2 ⟨subd10_0_769, List.forall_mem_cons.2 ⟨subd10_0_770, List.forall_mem_cons.2 ⟨subd10_0_771, List.forall_mem_cons.2 ⟨subd10_0_772, List.forall_mem_cons.2 ⟨subd10_0_773, List.forall_mem_cons.2 ⟨subd10_0_774, List.forall_mem_cons.2 ⟨subd10_0_775, List.forall_mem_cons.2 ⟨subd10_0_776, List.forall_mem_cons.2 ⟨subd10_0_777, List.forall_mem_cons.2 ⟨subd10_0_778, List.forall_mem_cons.2 ⟨subd10_0_779, List.forall_mem_cons.2 ⟨subd10_0_780, List.forall_mem_cons.2 ⟨subd10_0_781, List.forall_mem_cons.2 ⟨subd10_0_782, List.forall_mem_cons.2 ⟨subd10_0_783, List.forall_mem_cons.2 ⟨subd10_0_784, List.forall_mem_cons.2 ⟨subd10_0_785, List.forall_mem_cons.2 ⟨subd10_0_786, List.forall_mem_cons.2 ⟨subd10_0_787, List.forall_mem_cons.2 ⟨subd10_0_788, List.forall_mem_cons.2 ⟨subd10_0_789, List.forall_mem_cons.2 ⟨subd10_0_790, List.forall_mem_cons.2 ⟨subd10_0_791, List.forall_mem_cons.2 ⟨subd10_0_792, List.forall_mem_cons.2 ⟨subd10_0_793, List.forall_mem_cons.2 ⟨subd10_0_794, List.forall_mem_cons.2 ⟨subd10_0_795, List.forall_mem_cons.2 ⟨subd10_0_796, List.forall_mem_cons.2 ⟨subd10_0_797, List.forall_mem_cons.2 ⟨subd10_0_798, List.forall_mem_cons.2 ⟨subd10_0_799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_800 : subd10_0 [0, -1, -1] = true := by decide +kernel
theorem subd10_0_801 : subd10_0 [0, -1, 0] = true := by decide +kernel
theorem subd10_0_802 : subd10_0 [0, -1, 1] = true := by decide +kernel
theorem subd10_0_803 : subd10_0 [0, -1, 2] = true := by decide +kernel
theorem subd10_0_804 : subd10_0 [0, -1, 3] = true := by decide +kernel
theorem subd10_0_805 : subd10_0 [0, -1, 4] = true := by decide +kernel
theorem subd10_0_806 : subd10_0 [0, -1, 5] = true := by decide +kernel
theorem subd10_0_807 : subd10_0 [0, -1, 6] = true := by decide +kernel
theorem subd10_0_808 : subd10_0 [0, -1, 7] = true := by decide +kernel
theorem subd10_0_809 : subd10_0 [0, -1, 8] = true := by decide +kernel
theorem subd10_0_810 : subd10_0 [0, -1, 9] = true := by decide +kernel
theorem subd10_0_811 : subd10_0 [0, 0, -9] = true := by decide +kernel
theorem subd10_0_812 : subd10_0 [0, 0, -8] = true := by decide +kernel
theorem subd10_0_813 : subd10_0 [0, 0, -7] = true := by decide +kernel
theorem subd10_0_814 : subd10_0 [0, 0, -6] = true := by decide +kernel
theorem subd10_0_815 : subd10_0 [0, 0, -5] = true := by decide +kernel
theorem subd10_0_816 : subd10_0 [0, 0, -4] = true := by decide +kernel
theorem subd10_0_817 : subd10_0 [0, 0, -3] = true := by decide +kernel
theorem subd10_0_818 : subd10_0 [0, 0, -2] = true := by decide +kernel
theorem subd10_0_819 : subd10_0 [0, 0, -1] = true := by decide +kernel
theorem subd10_0_820 : subd10_0 [0, 0, 0] = true := by decide +kernel
theorem subd10_0_821 : subd10_0 [0, 0, 1] = true := by decide +kernel
theorem subd10_0_822 : subd10_0 [0, 0, 2] = true := by decide +kernel
theorem subd10_0_823 : subd10_0 [0, 0, 3] = true := by decide +kernel
theorem subd10_0_824 : subd10_0 [0, 0, 4] = true := by decide +kernel
theorem subd10_0_825 : subd10_0 [0, 0, 5] = true := by decide +kernel
theorem subd10_0_826 : subd10_0 [0, 0, 6] = true := by decide +kernel
theorem subd10_0_827 : subd10_0 [0, 0, 7] = true := by decide +kernel
theorem subd10_0_828 : subd10_0 [0, 0, 8] = true := by decide +kernel
theorem subd10_0_829 : subd10_0 [0, 1, -10] = true := by decide +kernel
theorem subd10_0_830 : subd10_0 [0, 1, -9] = true := by decide +kernel
theorem subd10_0_831 : subd10_0 [0, 1, -8] = true := by decide +kernel
theorem sbd10_0_25 : ∀ q ∈ blkd10_0_25, subd10_0 q = true := by
  unfold blkd10_0_25
  exact List.forall_mem_cons.2 ⟨subd10_0_800, List.forall_mem_cons.2 ⟨subd10_0_801, List.forall_mem_cons.2 ⟨subd10_0_802, List.forall_mem_cons.2 ⟨subd10_0_803, List.forall_mem_cons.2 ⟨subd10_0_804, List.forall_mem_cons.2 ⟨subd10_0_805, List.forall_mem_cons.2 ⟨subd10_0_806, List.forall_mem_cons.2 ⟨subd10_0_807, List.forall_mem_cons.2 ⟨subd10_0_808, List.forall_mem_cons.2 ⟨subd10_0_809, List.forall_mem_cons.2 ⟨subd10_0_810, List.forall_mem_cons.2 ⟨subd10_0_811, List.forall_mem_cons.2 ⟨subd10_0_812, List.forall_mem_cons.2 ⟨subd10_0_813, List.forall_mem_cons.2 ⟨subd10_0_814, List.forall_mem_cons.2 ⟨subd10_0_815, List.forall_mem_cons.2 ⟨subd10_0_816, List.forall_mem_cons.2 ⟨subd10_0_817, List.forall_mem_cons.2 ⟨subd10_0_818, List.forall_mem_cons.2 ⟨subd10_0_819, List.forall_mem_cons.2 ⟨subd10_0_820, List.forall_mem_cons.2 ⟨subd10_0_821, List.forall_mem_cons.2 ⟨subd10_0_822, List.forall_mem_cons.2 ⟨subd10_0_823, List.forall_mem_cons.2 ⟨subd10_0_824, List.forall_mem_cons.2 ⟨subd10_0_825, List.forall_mem_cons.2 ⟨subd10_0_826, List.forall_mem_cons.2 ⟨subd10_0_827, List.forall_mem_cons.2 ⟨subd10_0_828, List.forall_mem_cons.2 ⟨subd10_0_829, List.forall_mem_cons.2 ⟨subd10_0_830, List.forall_mem_cons.2 ⟨subd10_0_831, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_832 : subd10_0 [0, 1, -7] = true := by decide +kernel
theorem subd10_0_833 : subd10_0 [0, 1, -6] = true := by decide +kernel
theorem subd10_0_834 : subd10_0 [0, 1, -5] = true := by decide +kernel
theorem subd10_0_835 : subd10_0 [0, 1, -4] = true := by decide +kernel
theorem subd10_0_836 : subd10_0 [0, 1, -3] = true := by decide +kernel
theorem subd10_0_837 : subd10_0 [0, 1, -2] = true := by decide +kernel
theorem subd10_0_838 : subd10_0 [0, 1, -1] = true := by decide +kernel
theorem subd10_0_839 : subd10_0 [0, 1, 0] = true := by decide +kernel
theorem subd10_0_840 : subd10_0 [0, 1, 1] = true := by decide +kernel
theorem subd10_0_841 : subd10_0 [0, 1, 2] = true := by decide +kernel
theorem subd10_0_842 : subd10_0 [0, 1, 3] = true := by decide +kernel
theorem subd10_0_843 : subd10_0 [0, 1, 4] = true := by decide +kernel
theorem subd10_0_844 : subd10_0 [0, 1, 5] = true := by decide +kernel
theorem subd10_0_845 : subd10_0 [0, 1, 6] = true := by decide +kernel
theorem subd10_0_846 : subd10_0 [0, 1, 7] = true := by decide +kernel
theorem subd10_0_847 : subd10_0 [0, 1, 8] = true := by decide +kernel
theorem subd10_0_848 : subd10_0 [0, 2, -9] = true := by decide +kernel
theorem subd10_0_849 : subd10_0 [0, 2, -8] = true := by decide +kernel
theorem subd10_0_850 : subd10_0 [0, 2, -7] = true := by decide +kernel
theorem subd10_0_851 : subd10_0 [0, 2, -6] = true := by decide +kernel
theorem subd10_0_852 : subd10_0 [0, 2, -5] = true := by decide +kernel
theorem subd10_0_853 : subd10_0 [0, 2, -4] = true := by decide +kernel
theorem subd10_0_854 : subd10_0 [0, 2, -3] = true := by decide +kernel
theorem subd10_0_855 : subd10_0 [0, 2, -2] = true := by decide +kernel
theorem subd10_0_856 : subd10_0 [0, 2, -1] = true := by decide +kernel
theorem subd10_0_857 : subd10_0 [0, 2, 0] = true := by decide +kernel
theorem subd10_0_858 : subd10_0 [0, 2, 1] = true := by decide +kernel
theorem subd10_0_859 : subd10_0 [0, 2, 2] = true := by decide +kernel
theorem subd10_0_860 : subd10_0 [0, 2, 3] = true := by decide +kernel
theorem subd10_0_861 : subd10_0 [0, 2, 4] = true := by decide +kernel
theorem subd10_0_862 : subd10_0 [0, 2, 5] = true := by decide +kernel
theorem subd10_0_863 : subd10_0 [0, 2, 6] = true := by decide +kernel
theorem sbd10_0_26 : ∀ q ∈ blkd10_0_26, subd10_0 q = true := by
  unfold blkd10_0_26
  exact List.forall_mem_cons.2 ⟨subd10_0_832, List.forall_mem_cons.2 ⟨subd10_0_833, List.forall_mem_cons.2 ⟨subd10_0_834, List.forall_mem_cons.2 ⟨subd10_0_835, List.forall_mem_cons.2 ⟨subd10_0_836, List.forall_mem_cons.2 ⟨subd10_0_837, List.forall_mem_cons.2 ⟨subd10_0_838, List.forall_mem_cons.2 ⟨subd10_0_839, List.forall_mem_cons.2 ⟨subd10_0_840, List.forall_mem_cons.2 ⟨subd10_0_841, List.forall_mem_cons.2 ⟨subd10_0_842, List.forall_mem_cons.2 ⟨subd10_0_843, List.forall_mem_cons.2 ⟨subd10_0_844, List.forall_mem_cons.2 ⟨subd10_0_845, List.forall_mem_cons.2 ⟨subd10_0_846, List.forall_mem_cons.2 ⟨subd10_0_847, List.forall_mem_cons.2 ⟨subd10_0_848, List.forall_mem_cons.2 ⟨subd10_0_849, List.forall_mem_cons.2 ⟨subd10_0_850, List.forall_mem_cons.2 ⟨subd10_0_851, List.forall_mem_cons.2 ⟨subd10_0_852, List.forall_mem_cons.2 ⟨subd10_0_853, List.forall_mem_cons.2 ⟨subd10_0_854, List.forall_mem_cons.2 ⟨subd10_0_855, List.forall_mem_cons.2 ⟨subd10_0_856, List.forall_mem_cons.2 ⟨subd10_0_857, List.forall_mem_cons.2 ⟨subd10_0_858, List.forall_mem_cons.2 ⟨subd10_0_859, List.forall_mem_cons.2 ⟨subd10_0_860, List.forall_mem_cons.2 ⟨subd10_0_861, List.forall_mem_cons.2 ⟨subd10_0_862, List.forall_mem_cons.2 ⟨subd10_0_863, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_864 : subd10_0 [0, 2, 7] = true := by decide +kernel
theorem subd10_0_865 : subd10_0 [0, 2, 8] = true := by decide +kernel
theorem subd10_0_866 : subd10_0 [0, 3, -9] = true := by decide +kernel
theorem subd10_0_867 : subd10_0 [0, 3, -8] = true := by decide +kernel
theorem subd10_0_868 : subd10_0 [0, 3, -7] = true := by decide +kernel
theorem subd10_0_869 : subd10_0 [0, 3, -6] = true := by decide +kernel
theorem subd10_0_870 : subd10_0 [0, 3, -5] = true := by decide +kernel
theorem subd10_0_871 : subd10_0 [0, 3, -4] = true := by decide +kernel
theorem subd10_0_872 : subd10_0 [0, 3, -3] = true := by decide +kernel
theorem subd10_0_873 : subd10_0 [0, 3, -2] = true := by decide +kernel
theorem subd10_0_874 : subd10_0 [0, 3, -1] = true := by decide +kernel
theorem subd10_0_875 : subd10_0 [0, 3, 0] = true := by decide +kernel
theorem subd10_0_876 : subd10_0 [0, 3, 1] = true := by decide +kernel
theorem subd10_0_877 : subd10_0 [0, 3, 2] = true := by decide +kernel
theorem subd10_0_878 : subd10_0 [0, 3, 3] = true := by decide +kernel
theorem subd10_0_879 : subd10_0 [0, 3, 4] = true := by decide +kernel
theorem subd10_0_880 : subd10_0 [0, 3, 5] = true := by decide +kernel
theorem subd10_0_881 : subd10_0 [0, 3, 6] = true := by decide +kernel
theorem subd10_0_882 : subd10_0 [0, 3, 7] = true := by decide +kernel
theorem subd10_0_883 : subd10_0 [0, 4, -9] = true := by decide +kernel
theorem subd10_0_884 : subd10_0 [0, 4, -8] = true := by decide +kernel
theorem subd10_0_885 : subd10_0 [0, 4, -7] = true := by decide +kernel
theorem subd10_0_886 : subd10_0 [0, 4, -6] = true := by decide +kernel
theorem subd10_0_887 : subd10_0 [0, 4, -5] = true := by decide +kernel
theorem subd10_0_888 : subd10_0 [0, 4, -4] = true := by decide +kernel
theorem subd10_0_889 : subd10_0 [0, 4, -3] = true := by decide +kernel
theorem subd10_0_890 : subd10_0 [0, 4, -2] = true := by decide +kernel
theorem subd10_0_891 : subd10_0 [0, 4, -1] = true := by decide +kernel
theorem subd10_0_892 : subd10_0 [0, 4, 0] = true := by decide +kernel
theorem subd10_0_893 : subd10_0 [0, 4, 1] = true := by decide +kernel
theorem subd10_0_894 : subd10_0 [0, 4, 2] = true := by decide +kernel
theorem subd10_0_895 : subd10_0 [0, 4, 3] = true := by decide +kernel
theorem sbd10_0_27 : ∀ q ∈ blkd10_0_27, subd10_0 q = true := by
  unfold blkd10_0_27
  exact List.forall_mem_cons.2 ⟨subd10_0_864, List.forall_mem_cons.2 ⟨subd10_0_865, List.forall_mem_cons.2 ⟨subd10_0_866, List.forall_mem_cons.2 ⟨subd10_0_867, List.forall_mem_cons.2 ⟨subd10_0_868, List.forall_mem_cons.2 ⟨subd10_0_869, List.forall_mem_cons.2 ⟨subd10_0_870, List.forall_mem_cons.2 ⟨subd10_0_871, List.forall_mem_cons.2 ⟨subd10_0_872, List.forall_mem_cons.2 ⟨subd10_0_873, List.forall_mem_cons.2 ⟨subd10_0_874, List.forall_mem_cons.2 ⟨subd10_0_875, List.forall_mem_cons.2 ⟨subd10_0_876, List.forall_mem_cons.2 ⟨subd10_0_877, List.forall_mem_cons.2 ⟨subd10_0_878, List.forall_mem_cons.2 ⟨subd10_0_879, List.forall_mem_cons.2 ⟨subd10_0_880, List.forall_mem_cons.2 ⟨subd10_0_881, List.forall_mem_cons.2 ⟨subd10_0_882, List.forall_mem_cons.2 ⟨subd10_0_883, List.forall_mem_cons.2 ⟨subd10_0_884, List.forall_mem_cons.2 ⟨subd10_0_885, List.forall_mem_cons.2 ⟨subd10_0_886, List.forall_mem_cons.2 ⟨subd10_0_887, List.forall_mem_cons.2 ⟨subd10_0_888, List.forall_mem_cons.2 ⟨subd10_0_889, List.forall_mem_cons.2 ⟨subd10_0_890, List.forall_mem_cons.2 ⟨subd10_0_891, List.forall_mem_cons.2 ⟨subd10_0_892, List.forall_mem_cons.2 ⟨subd10_0_893, List.forall_mem_cons.2 ⟨subd10_0_894, List.forall_mem_cons.2 ⟨subd10_0_895, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_896 : subd10_0 [0, 4, 4] = true := by decide +kernel
theorem subd10_0_897 : subd10_0 [0, 4, 5] = true := by decide +kernel
theorem subd10_0_898 : subd10_0 [0, 4, 6] = true := by decide +kernel
theorem subd10_0_899 : subd10_0 [0, 5, -8] = true := by decide +kernel
theorem subd10_0_900 : subd10_0 [0, 5, -7] = true := by decide +kernel
theorem subd10_0_901 : subd10_0 [0, 5, -6] = true := by decide +kernel
theorem subd10_0_902 : subd10_0 [0, 5, -5] = true := by decide +kernel
theorem subd10_0_903 : subd10_0 [0, 5, -4] = true := by decide +kernel
theorem subd10_0_904 : subd10_0 [0, 5, -3] = true := by decide +kernel
theorem subd10_0_905 : subd10_0 [0, 5, -2] = true := by decide +kernel
theorem subd10_0_906 : subd10_0 [0, 5, -1] = true := by decide +kernel
theorem subd10_0_907 : subd10_0 [0, 5, 0] = true := by decide +kernel
theorem subd10_0_908 : subd10_0 [0, 5, 1] = true := by decide +kernel
theorem subd10_0_909 : subd10_0 [0, 5, 2] = true := by decide +kernel
theorem subd10_0_910 : subd10_0 [0, 5, 3] = true := by decide +kernel
theorem subd10_0_911 : subd10_0 [0, 5, 4] = true := by decide +kernel
theorem subd10_0_912 : subd10_0 [0, 5, 5] = true := by decide +kernel
theorem subd10_0_913 : subd10_0 [0, 6] = true := by decide +kernel
theorem subd10_0_914 : subd10_0 [0, 7] = true := by decide +kernel
theorem subd10_0_915 : subd10_0 [1, -8] = true := by decide +kernel
theorem subd10_0_916 : subd10_0 [1, -7] = true := by decide +kernel
theorem subd10_0_917 : subd10_0 [1, -6] = true := by decide +kernel
theorem subd10_0_918 : subd10_0 [1, -5, -6] = true := by decide +kernel
theorem subd10_0_919 : subd10_0 [1, -5, -5] = true := by decide +kernel
theorem subd10_0_920 : subd10_0 [1, -5, -4] = true := by decide +kernel
theorem subd10_0_921 : subd10_0 [1, -5, -3] = true := by decide +kernel
theorem subd10_0_922 : subd10_0 [1, -5, -2] = true := by decide +kernel
theorem subd10_0_923 : subd10_0 [1, -5, -1] = true := by decide +kernel
theorem subd10_0_924 : subd10_0 [1, -5, 0] = true := by decide +kernel
theorem subd10_0_925 : subd10_0 [1, -5, 1] = true := by decide +kernel
theorem subd10_0_926 : subd10_0 [1, -5, 2] = true := by decide +kernel
theorem subd10_0_927 : subd10_0 [1, -5, 3] = true := by decide +kernel
theorem sbd10_0_28 : ∀ q ∈ blkd10_0_28, subd10_0 q = true := by
  unfold blkd10_0_28
  exact List.forall_mem_cons.2 ⟨subd10_0_896, List.forall_mem_cons.2 ⟨subd10_0_897, List.forall_mem_cons.2 ⟨subd10_0_898, List.forall_mem_cons.2 ⟨subd10_0_899, List.forall_mem_cons.2 ⟨subd10_0_900, List.forall_mem_cons.2 ⟨subd10_0_901, List.forall_mem_cons.2 ⟨subd10_0_902, List.forall_mem_cons.2 ⟨subd10_0_903, List.forall_mem_cons.2 ⟨subd10_0_904, List.forall_mem_cons.2 ⟨subd10_0_905, List.forall_mem_cons.2 ⟨subd10_0_906, List.forall_mem_cons.2 ⟨subd10_0_907, List.forall_mem_cons.2 ⟨subd10_0_908, List.forall_mem_cons.2 ⟨subd10_0_909, List.forall_mem_cons.2 ⟨subd10_0_910, List.forall_mem_cons.2 ⟨subd10_0_911, List.forall_mem_cons.2 ⟨subd10_0_912, List.forall_mem_cons.2 ⟨subd10_0_913, List.forall_mem_cons.2 ⟨subd10_0_914, List.forall_mem_cons.2 ⟨subd10_0_915, List.forall_mem_cons.2 ⟨subd10_0_916, List.forall_mem_cons.2 ⟨subd10_0_917, List.forall_mem_cons.2 ⟨subd10_0_918, List.forall_mem_cons.2 ⟨subd10_0_919, List.forall_mem_cons.2 ⟨subd10_0_920, List.forall_mem_cons.2 ⟨subd10_0_921, List.forall_mem_cons.2 ⟨subd10_0_922, List.forall_mem_cons.2 ⟨subd10_0_923, List.forall_mem_cons.2 ⟨subd10_0_924, List.forall_mem_cons.2 ⟨subd10_0_925, List.forall_mem_cons.2 ⟨subd10_0_926, List.forall_mem_cons.2 ⟨subd10_0_927, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_928 : subd10_0 [1, -5, 4] = true := by decide +kernel
theorem subd10_0_929 : subd10_0 [1, -5, 5] = true := by decide +kernel
theorem subd10_0_930 : subd10_0 [1, -5, 6] = true := by decide +kernel
theorem subd10_0_931 : subd10_0 [1, -5, 7] = true := by decide +kernel
theorem subd10_0_932 : subd10_0 [1, -5, 8] = true := by decide +kernel
theorem subd10_0_933 : subd10_0 [1, -4, -7] = true := by decide +kernel
theorem subd10_0_934 : subd10_0 [1, -4, -6] = true := by decide +kernel
theorem subd10_0_935 : subd10_0 [1, -4, -5] = true := by decide +kernel
theorem subd10_0_936 : subd10_0 [1, -4, -4] = true := by decide +kernel
theorem subd10_0_937 : subd10_0 [1, -4, -3] = true := by decide +kernel
theorem subd10_0_938 : subd10_0 [1, -4, -2] = true := by decide +kernel
theorem subd10_0_939 : subd10_0 [1, -4, -1] = true := by decide +kernel
theorem subd10_0_940 : subd10_0 [1, -4, 0] = true := by decide +kernel
theorem subd10_0_941 : subd10_0 [1, -4, 1] = true := by decide +kernel
theorem subd10_0_942 : subd10_0 [1, -4, 2] = true := by decide +kernel
theorem subd10_0_943 : subd10_0 [1, -4, 3] = true := by decide +kernel
theorem subd10_0_944 : subd10_0 [1, -4, 4] = true := by decide +kernel
theorem subd10_0_945 : subd10_0 [1, -4, 5] = true := by decide +kernel
theorem subd10_0_946 : subd10_0 [1, -4, 6] = true := by decide +kernel
theorem subd10_0_947 : subd10_0 [1, -4, 7] = true := by decide +kernel
theorem subd10_0_948 : subd10_0 [1, -4, 8] = true := by decide +kernel
theorem subd10_0_949 : subd10_0 [1, -3, -8] = true := by decide +kernel
theorem subd10_0_950 : subd10_0 [1, -3, -7] = true := by decide +kernel
theorem subd10_0_951 : subd10_0 [1, -3, -6] = true := by decide +kernel
theorem subd10_0_952 : subd10_0 [1, -3, -5] = true := by decide +kernel
theorem subd10_0_953 : subd10_0 [1, -3, -4] = true := by decide +kernel
theorem subd10_0_954 : subd10_0 [1, -3, -3] = true := by decide +kernel
theorem subd10_0_955 : subd10_0 [1, -3, -2] = true := by decide +kernel
theorem subd10_0_956 : subd10_0 [1, -3, -1] = true := by decide +kernel
theorem subd10_0_957 : subd10_0 [1, -3, 0] = true := by decide +kernel
theorem subd10_0_958 : subd10_0 [1, -3, 1] = true := by decide +kernel
theorem subd10_0_959 : subd10_0 [1, -3, 2] = true := by decide +kernel
theorem sbd10_0_29 : ∀ q ∈ blkd10_0_29, subd10_0 q = true := by
  unfold blkd10_0_29
  exact List.forall_mem_cons.2 ⟨subd10_0_928, List.forall_mem_cons.2 ⟨subd10_0_929, List.forall_mem_cons.2 ⟨subd10_0_930, List.forall_mem_cons.2 ⟨subd10_0_931, List.forall_mem_cons.2 ⟨subd10_0_932, List.forall_mem_cons.2 ⟨subd10_0_933, List.forall_mem_cons.2 ⟨subd10_0_934, List.forall_mem_cons.2 ⟨subd10_0_935, List.forall_mem_cons.2 ⟨subd10_0_936, List.forall_mem_cons.2 ⟨subd10_0_937, List.forall_mem_cons.2 ⟨subd10_0_938, List.forall_mem_cons.2 ⟨subd10_0_939, List.forall_mem_cons.2 ⟨subd10_0_940, List.forall_mem_cons.2 ⟨subd10_0_941, List.forall_mem_cons.2 ⟨subd10_0_942, List.forall_mem_cons.2 ⟨subd10_0_943, List.forall_mem_cons.2 ⟨subd10_0_944, List.forall_mem_cons.2 ⟨subd10_0_945, List.forall_mem_cons.2 ⟨subd10_0_946, List.forall_mem_cons.2 ⟨subd10_0_947, List.forall_mem_cons.2 ⟨subd10_0_948, List.forall_mem_cons.2 ⟨subd10_0_949, List.forall_mem_cons.2 ⟨subd10_0_950, List.forall_mem_cons.2 ⟨subd10_0_951, List.forall_mem_cons.2 ⟨subd10_0_952, List.forall_mem_cons.2 ⟨subd10_0_953, List.forall_mem_cons.2 ⟨subd10_0_954, List.forall_mem_cons.2 ⟨subd10_0_955, List.forall_mem_cons.2 ⟨subd10_0_956, List.forall_mem_cons.2 ⟨subd10_0_957, List.forall_mem_cons.2 ⟨subd10_0_958, List.forall_mem_cons.2 ⟨subd10_0_959, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C131
