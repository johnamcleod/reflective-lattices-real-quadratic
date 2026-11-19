import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd10_1_512 : subd10_1 [1, 0, 3] = true := by decide +kernel
theorem subd10_1_513 : subd10_1 [1, 0, 4] = true := by decide +kernel
theorem subd10_1_514 : subd10_1 [1, 0, 5] = true := by decide +kernel
theorem subd10_1_515 : subd10_1 [1, 0, 6] = true := by decide +kernel
theorem subd10_1_516 : subd10_1 [1, 0, 7] = true := by decide +kernel
theorem subd10_1_517 : subd10_1 [1, 1, -9] = true := by decide +kernel
theorem subd10_1_518 : subd10_1 [1, 1, -8] = true := by decide +kernel
theorem subd10_1_519 : subd10_1 [1, 1, -7] = true := by decide +kernel
theorem subd10_1_520 : subd10_1 [1, 1, -6] = true := by decide +kernel
theorem subd10_1_521 : subd10_1 [1, 1, -5] = true := by decide +kernel
theorem subd10_1_522 : subd10_1 [1, 1, -4] = true := by decide +kernel
theorem subd10_1_523 : subd10_1 [1, 1, -3] = true := by decide +kernel
theorem subd10_1_524 : subd10_1 [1, 1, -2] = true := by decide +kernel
theorem subd10_1_525 : subd10_1 [1, 1, -1] = true := by decide +kernel
theorem subd10_1_526 : subd10_1 [1, 1, 0] = true := by decide +kernel
theorem subd10_1_527 : subd10_1 [1, 1, 1] = true := by decide +kernel
theorem subd10_1_528 : subd10_1 [1, 1, 2] = true := by decide +kernel
theorem subd10_1_529 : subd10_1 [1, 1, 3] = true := by decide +kernel
theorem subd10_1_530 : subd10_1 [1, 1, 4] = true := by decide +kernel
theorem subd10_1_531 : subd10_1 [1, 1, 5] = true := by decide +kernel
theorem subd10_1_532 : subd10_1 [1, 1, 6] = true := by decide +kernel
theorem subd10_1_533 : subd10_1 [1, 1, 7] = true := by decide +kernel
theorem subd10_1_534 : subd10_1 [1, 2, -9] = true := by decide +kernel
theorem subd10_1_535 : subd10_1 [1, 2, -8] = true := by decide +kernel
theorem subd10_1_536 : subd10_1 [1, 2, -7] = true := by decide +kernel
theorem subd10_1_537 : subd10_1 [1, 2, -6] = true := by decide +kernel
theorem subd10_1_538 : subd10_1 [1, 2, -5] = true := by decide +kernel
theorem subd10_1_539 : subd10_1 [1, 2, -4] = true := by decide +kernel
theorem subd10_1_540 : subd10_1 [1, 2, -3] = true := by decide +kernel
theorem subd10_1_541 : subd10_1 [1, 2, -2] = true := by decide +kernel
theorem subd10_1_542 : subd10_1 [1, 2, -1] = true := by decide +kernel
theorem subd10_1_543 : subd10_1 [1, 2, 0] = true := by decide +kernel
theorem sbd10_1_16 : ∀ q ∈ blkd10_1_16, subd10_1 q = true := by
  unfold blkd10_1_16
  exact List.forall_mem_cons.2 ⟨subd10_1_512, List.forall_mem_cons.2 ⟨subd10_1_513, List.forall_mem_cons.2 ⟨subd10_1_514, List.forall_mem_cons.2 ⟨subd10_1_515, List.forall_mem_cons.2 ⟨subd10_1_516, List.forall_mem_cons.2 ⟨subd10_1_517, List.forall_mem_cons.2 ⟨subd10_1_518, List.forall_mem_cons.2 ⟨subd10_1_519, List.forall_mem_cons.2 ⟨subd10_1_520, List.forall_mem_cons.2 ⟨subd10_1_521, List.forall_mem_cons.2 ⟨subd10_1_522, List.forall_mem_cons.2 ⟨subd10_1_523, List.forall_mem_cons.2 ⟨subd10_1_524, List.forall_mem_cons.2 ⟨subd10_1_525, List.forall_mem_cons.2 ⟨subd10_1_526, List.forall_mem_cons.2 ⟨subd10_1_527, List.forall_mem_cons.2 ⟨subd10_1_528, List.forall_mem_cons.2 ⟨subd10_1_529, List.forall_mem_cons.2 ⟨subd10_1_530, List.forall_mem_cons.2 ⟨subd10_1_531, List.forall_mem_cons.2 ⟨subd10_1_532, List.forall_mem_cons.2 ⟨subd10_1_533, List.forall_mem_cons.2 ⟨subd10_1_534, List.forall_mem_cons.2 ⟨subd10_1_535, List.forall_mem_cons.2 ⟨subd10_1_536, List.forall_mem_cons.2 ⟨subd10_1_537, List.forall_mem_cons.2 ⟨subd10_1_538, List.forall_mem_cons.2 ⟨subd10_1_539, List.forall_mem_cons.2 ⟨subd10_1_540, List.forall_mem_cons.2 ⟨subd10_1_541, List.forall_mem_cons.2 ⟨subd10_1_542, List.forall_mem_cons.2 ⟨subd10_1_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_544 : subd10_1 [1, 2, 1] = true := by decide +kernel
theorem subd10_1_545 : subd10_1 [1, 2, 2] = true := by decide +kernel
theorem subd10_1_546 : subd10_1 [1, 2, 3] = true := by decide +kernel
theorem subd10_1_547 : subd10_1 [1, 2, 4] = true := by decide +kernel
theorem subd10_1_548 : subd10_1 [1, 2, 5] = true := by decide +kernel
theorem subd10_1_549 : subd10_1 [1, 2, 6] = true := by decide +kernel
theorem subd10_1_550 : subd10_1 [1, 3, -8] = true := by decide +kernel
theorem subd10_1_551 : subd10_1 [1, 3, -7] = true := by decide +kernel
theorem subd10_1_552 : subd10_1 [1, 3, -6] = true := by decide +kernel
theorem subd10_1_553 : subd10_1 [1, 3, -5] = true := by decide +kernel
theorem subd10_1_554 : subd10_1 [1, 3, -4] = true := by decide +kernel
theorem subd10_1_555 : subd10_1 [1, 3, -3] = true := by decide +kernel
theorem subd10_1_556 : subd10_1 [1, 3, -2] = true := by decide +kernel
theorem subd10_1_557 : subd10_1 [1, 3, -1] = true := by decide +kernel
theorem subd10_1_558 : subd10_1 [1, 3, 0] = true := by decide +kernel
theorem subd10_1_559 : subd10_1 [1, 3, 1] = true := by decide +kernel
theorem subd10_1_560 : subd10_1 [1, 3, 2] = true := by decide +kernel
theorem subd10_1_561 : subd10_1 [1, 3, 3] = true := by decide +kernel
theorem subd10_1_562 : subd10_1 [1, 3, 4] = true := by decide +kernel
theorem subd10_1_563 : subd10_1 [1, 3, 5] = true := by decide +kernel
theorem subd10_1_564 : subd10_1 [1, 4] = true := by decide +kernel
theorem subd10_1_565 : subd10_1 [1, 5] = true := by decide +kernel
theorem subd10_1_566 : subd10_1 [2, -7] = true := by decide +kernel
theorem subd10_1_567 : subd10_1 [2, -6] = true := by decide +kernel
theorem subd10_1_568 : subd10_1 [2, -5] = true := by decide +kernel
theorem subd10_1_569 : subd10_1 [2, -4, -6] = true := by decide +kernel
theorem subd10_1_570 : subd10_1 [2, -4, -5] = true := by decide +kernel
theorem subd10_1_571 : subd10_1 [2, -4, -4] = true := by decide +kernel
theorem subd10_1_572 : subd10_1 [2, -4, -3] = true := by decide +kernel
theorem subd10_1_573 : subd10_1 [2, -4, -2] = true := by decide +kernel
theorem subd10_1_574 : subd10_1 [2, -4, -1] = true := by decide +kernel
theorem subd10_1_575 : subd10_1 [2, -4, 0] = true := by decide +kernel
theorem sbd10_1_17 : ∀ q ∈ blkd10_1_17, subd10_1 q = true := by
  unfold blkd10_1_17
  exact List.forall_mem_cons.2 ⟨subd10_1_544, List.forall_mem_cons.2 ⟨subd10_1_545, List.forall_mem_cons.2 ⟨subd10_1_546, List.forall_mem_cons.2 ⟨subd10_1_547, List.forall_mem_cons.2 ⟨subd10_1_548, List.forall_mem_cons.2 ⟨subd10_1_549, List.forall_mem_cons.2 ⟨subd10_1_550, List.forall_mem_cons.2 ⟨subd10_1_551, List.forall_mem_cons.2 ⟨subd10_1_552, List.forall_mem_cons.2 ⟨subd10_1_553, List.forall_mem_cons.2 ⟨subd10_1_554, List.forall_mem_cons.2 ⟨subd10_1_555, List.forall_mem_cons.2 ⟨subd10_1_556, List.forall_mem_cons.2 ⟨subd10_1_557, List.forall_mem_cons.2 ⟨subd10_1_558, List.forall_mem_cons.2 ⟨subd10_1_559, List.forall_mem_cons.2 ⟨subd10_1_560, List.forall_mem_cons.2 ⟨subd10_1_561, List.forall_mem_cons.2 ⟨subd10_1_562, List.forall_mem_cons.2 ⟨subd10_1_563, List.forall_mem_cons.2 ⟨subd10_1_564, List.forall_mem_cons.2 ⟨subd10_1_565, List.forall_mem_cons.2 ⟨subd10_1_566, List.forall_mem_cons.2 ⟨subd10_1_567, List.forall_mem_cons.2 ⟨subd10_1_568, List.forall_mem_cons.2 ⟨subd10_1_569, List.forall_mem_cons.2 ⟨subd10_1_570, List.forall_mem_cons.2 ⟨subd10_1_571, List.forall_mem_cons.2 ⟨subd10_1_572, List.forall_mem_cons.2 ⟨subd10_1_573, List.forall_mem_cons.2 ⟨subd10_1_574, List.forall_mem_cons.2 ⟨subd10_1_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_576 : subd10_1 [2, -4, 1] = true := by decide +kernel
theorem subd10_1_577 : subd10_1 [2, -4, 2] = true := by decide +kernel
theorem subd10_1_578 : subd10_1 [2, -4, 3] = true := by decide +kernel
theorem subd10_1_579 : subd10_1 [2, -4, 4] = true := by decide +kernel
theorem subd10_1_580 : subd10_1 [2, -4, 5] = true := by decide +kernel
theorem subd10_1_581 : subd10_1 [2, -4, 6] = true := by decide +kernel
theorem subd10_1_582 : subd10_1 [2, -3, -7] = true := by decide +kernel
theorem subd10_1_583 : subd10_1 [2, -3, -6] = true := by decide +kernel
theorem subd10_1_584 : subd10_1 [2, -3, -5] = true := by decide +kernel
theorem subd10_1_585 : subd10_1 [2, -3, -4] = true := by decide +kernel
theorem subd10_1_586 : subd10_1 [2, -3, -3] = true := by decide +kernel
theorem subd10_1_587 : subd10_1 [2, -3, -2] = true := by decide +kernel
theorem subd10_1_588 : subd10_1 [2, -3, -1] = true := by decide +kernel
theorem subd10_1_589 : subd10_1 [2, -3, 0] = true := by decide +kernel
theorem subd10_1_590 : subd10_1 [2, -3, 1] = true := by decide +kernel
theorem subd10_1_591 : subd10_1 [2, -3, 2] = true := by decide +kernel
theorem subd10_1_592 : subd10_1 [2, -3, 3] = true := by decide +kernel
theorem subd10_1_593 : subd10_1 [2, -3, 4] = true := by decide +kernel
theorem subd10_1_594 : subd10_1 [2, -3, 5] = true := by decide +kernel
theorem subd10_1_595 : subd10_1 [2, -3, 6] = true := by decide +kernel
theorem subd10_1_596 : subd10_1 [2, -2, -8] = true := by decide +kernel
theorem subd10_1_597 : subd10_1 [2, -2, -7] = true := by decide +kernel
theorem subd10_1_598 : subd10_1 [2, -2, -6] = true := by decide +kernel
theorem subd10_1_599 : subd10_1 [2, -2, -5] = true := by decide +kernel
theorem subd10_1_600 : subd10_1 [2, -2, -4] = true := by decide +kernel
theorem subd10_1_601 : subd10_1 [2, -2, -3] = true := by decide +kernel
theorem subd10_1_602 : subd10_1 [2, -2, -2] = true := by decide +kernel
theorem subd10_1_603 : subd10_1 [2, -2, -1] = true := by decide +kernel
theorem subd10_1_604 : subd10_1 [2, -2, 0] = true := by decide +kernel
theorem subd10_1_605 : subd10_1 [2, -2, 1] = true := by decide +kernel
theorem subd10_1_606 : subd10_1 [2, -2, 2] = true := by decide +kernel
theorem subd10_1_607 : subd10_1 [2, -2, 3] = true := by decide +kernel
theorem sbd10_1_18 : ∀ q ∈ blkd10_1_18, subd10_1 q = true := by
  unfold blkd10_1_18
  exact List.forall_mem_cons.2 ⟨subd10_1_576, List.forall_mem_cons.2 ⟨subd10_1_577, List.forall_mem_cons.2 ⟨subd10_1_578, List.forall_mem_cons.2 ⟨subd10_1_579, List.forall_mem_cons.2 ⟨subd10_1_580, List.forall_mem_cons.2 ⟨subd10_1_581, List.forall_mem_cons.2 ⟨subd10_1_582, List.forall_mem_cons.2 ⟨subd10_1_583, List.forall_mem_cons.2 ⟨subd10_1_584, List.forall_mem_cons.2 ⟨subd10_1_585, List.forall_mem_cons.2 ⟨subd10_1_586, List.forall_mem_cons.2 ⟨subd10_1_587, List.forall_mem_cons.2 ⟨subd10_1_588, List.forall_mem_cons.2 ⟨subd10_1_589, List.forall_mem_cons.2 ⟨subd10_1_590, List.forall_mem_cons.2 ⟨subd10_1_591, List.forall_mem_cons.2 ⟨subd10_1_592, List.forall_mem_cons.2 ⟨subd10_1_593, List.forall_mem_cons.2 ⟨subd10_1_594, List.forall_mem_cons.2 ⟨subd10_1_595, List.forall_mem_cons.2 ⟨subd10_1_596, List.forall_mem_cons.2 ⟨subd10_1_597, List.forall_mem_cons.2 ⟨subd10_1_598, List.forall_mem_cons.2 ⟨subd10_1_599, List.forall_mem_cons.2 ⟨subd10_1_600, List.forall_mem_cons.2 ⟨subd10_1_601, List.forall_mem_cons.2 ⟨subd10_1_602, List.forall_mem_cons.2 ⟨subd10_1_603, List.forall_mem_cons.2 ⟨subd10_1_604, List.forall_mem_cons.2 ⟨subd10_1_605, List.forall_mem_cons.2 ⟨subd10_1_606, List.forall_mem_cons.2 ⟨subd10_1_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_608 : subd10_1 [2, -2, 4] = true := by decide +kernel
theorem subd10_1_609 : subd10_1 [2, -2, 5] = true := by decide +kernel
theorem subd10_1_610 : subd10_1 [2, -2, 6] = true := by decide +kernel
theorem subd10_1_611 : subd10_1 [2, -2, 7] = true := by decide +kernel
theorem subd10_1_612 : subd10_1 [2, -1, -9] = true := by decide +kernel
theorem subd10_1_613 : subd10_1 [2, -1, -8] = true := by decide +kernel
theorem subd10_1_614 : subd10_1 [2, -1, -7] = true := by decide +kernel
theorem subd10_1_615 : subd10_1 [2, -1, -6] = true := by decide +kernel
theorem subd10_1_616 : subd10_1 [2, -1, -5] = true := by decide +kernel
theorem subd10_1_617 : subd10_1 [2, -1, -4] = true := by decide +kernel
theorem subd10_1_618 : subd10_1 [2, -1, -3] = true := by decide +kernel
theorem subd10_1_619 : subd10_1 [2, -1, -2] = true := by decide +kernel
theorem subd10_1_620 : subd10_1 [2, -1, -1] = true := by decide +kernel
theorem subd10_1_621 : subd10_1 [2, -1, 0] = true := by decide +kernel
theorem subd10_1_622 : subd10_1 [2, -1, 1] = true := by decide +kernel
theorem subd10_1_623 : subd10_1 [2, -1, 2] = true := by decide +kernel
theorem subd10_1_624 : subd10_1 [2, -1, 3] = true := by decide +kernel
theorem subd10_1_625 : subd10_1 [2, -1, 4] = true := by decide +kernel
theorem subd10_1_626 : subd10_1 [2, -1, 5] = true := by decide +kernel
theorem subd10_1_627 : subd10_1 [2, -1, 6] = true := by decide +kernel
theorem subd10_1_628 : subd10_1 [2, -1, 7] = true := by decide +kernel
theorem subd10_1_629 : subd10_1 [2, 0, -9] = true := by decide +kernel
theorem subd10_1_630 : subd10_1 [2, 0, -8] = true := by decide +kernel
theorem subd10_1_631 : subd10_1 [2, 0, -7] = true := by decide +kernel
theorem subd10_1_632 : subd10_1 [2, 0, -6] = true := by decide +kernel
theorem subd10_1_633 : subd10_1 [2, 0, -5] = true := by decide +kernel
theorem subd10_1_634 : subd10_1 [2, 0, -4] = true := by decide +kernel
theorem subd10_1_635 : subd10_1 [2, 0, -3] = true := by decide +kernel
theorem subd10_1_636 : subd10_1 [2, 0, -2] = true := by decide +kernel
theorem subd10_1_637 : subd10_1 [2, 0, -1] = true := by decide +kernel
theorem subd10_1_638 : subd10_1 [2, 0, 0] = true := by decide +kernel
theorem subd10_1_639 : subd10_1 [2, 0, 1] = true := by decide +kernel
theorem sbd10_1_19 : ∀ q ∈ blkd10_1_19, subd10_1 q = true := by
  unfold blkd10_1_19
  exact List.forall_mem_cons.2 ⟨subd10_1_608, List.forall_mem_cons.2 ⟨subd10_1_609, List.forall_mem_cons.2 ⟨subd10_1_610, List.forall_mem_cons.2 ⟨subd10_1_611, List.forall_mem_cons.2 ⟨subd10_1_612, List.forall_mem_cons.2 ⟨subd10_1_613, List.forall_mem_cons.2 ⟨subd10_1_614, List.forall_mem_cons.2 ⟨subd10_1_615, List.forall_mem_cons.2 ⟨subd10_1_616, List.forall_mem_cons.2 ⟨subd10_1_617, List.forall_mem_cons.2 ⟨subd10_1_618, List.forall_mem_cons.2 ⟨subd10_1_619, List.forall_mem_cons.2 ⟨subd10_1_620, List.forall_mem_cons.2 ⟨subd10_1_621, List.forall_mem_cons.2 ⟨subd10_1_622, List.forall_mem_cons.2 ⟨subd10_1_623, List.forall_mem_cons.2 ⟨subd10_1_624, List.forall_mem_cons.2 ⟨subd10_1_625, List.forall_mem_cons.2 ⟨subd10_1_626, List.forall_mem_cons.2 ⟨subd10_1_627, List.forall_mem_cons.2 ⟨subd10_1_628, List.forall_mem_cons.2 ⟨subd10_1_629, List.forall_mem_cons.2 ⟨subd10_1_630, List.forall_mem_cons.2 ⟨subd10_1_631, List.forall_mem_cons.2 ⟨subd10_1_632, List.forall_mem_cons.2 ⟨subd10_1_633, List.forall_mem_cons.2 ⟨subd10_1_634, List.forall_mem_cons.2 ⟨subd10_1_635, List.forall_mem_cons.2 ⟨subd10_1_636, List.forall_mem_cons.2 ⟨subd10_1_637, List.forall_mem_cons.2 ⟨subd10_1_638, List.forall_mem_cons.2 ⟨subd10_1_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_640 : subd10_1 [2, 0, 2] = true := by decide +kernel
theorem subd10_1_641 : subd10_1 [2, 0, 3] = true := by decide +kernel
theorem subd10_1_642 : subd10_1 [2, 0, 4] = true := by decide +kernel
theorem subd10_1_643 : subd10_1 [2, 0, 5] = true := by decide +kernel
theorem subd10_1_644 : subd10_1 [2, 0, 6] = true := by decide +kernel
theorem subd10_1_645 : subd10_1 [2, 1, -9] = true := by decide +kernel
theorem subd10_1_646 : subd10_1 [2, 1, -8] = true := by decide +kernel
theorem subd10_1_647 : subd10_1 [2, 1, -7] = true := by decide +kernel
theorem subd10_1_648 : subd10_1 [2, 1, -6] = true := by decide +kernel
theorem subd10_1_649 : subd10_1 [2, 1, -5] = true := by decide +kernel
theorem subd10_1_650 : subd10_1 [2, 1, -4] = true := by decide +kernel
theorem subd10_1_651 : subd10_1 [2, 1, -3] = true := by decide +kernel
theorem subd10_1_652 : subd10_1 [2, 1, -2] = true := by decide +kernel
theorem subd10_1_653 : subd10_1 [2, 1, -1] = true := by decide +kernel
theorem subd10_1_654 : subd10_1 [2, 1, 0] = true := by decide +kernel
theorem subd10_1_655 : subd10_1 [2, 1, 1] = true := by decide +kernel
theorem subd10_1_656 : subd10_1 [2, 1, 2] = true := by decide +kernel
theorem subd10_1_657 : subd10_1 [2, 1, 3] = true := by decide +kernel
theorem subd10_1_658 : subd10_1 [2, 1, 4] = true := by decide +kernel
theorem subd10_1_659 : subd10_1 [2, 1, 5] = true := by decide +kernel
theorem subd10_1_660 : subd10_1 [2, 1, 6] = true := by decide +kernel
theorem subd10_1_661 : subd10_1 [2, 2, -8] = true := by decide +kernel
theorem subd10_1_662 : subd10_1 [2, 2, -7] = true := by decide +kernel
theorem subd10_1_663 : subd10_1 [2, 2, -6] = true := by decide +kernel
theorem subd10_1_664 : subd10_1 [2, 2, -5] = true := by decide +kernel
theorem subd10_1_665 : subd10_1 [2, 2, -4] = true := by decide +kernel
theorem subd10_1_666 : subd10_1 [2, 2, -3] = true := by decide +kernel
theorem subd10_1_667 : subd10_1 [2, 2, -2] = true := by decide +kernel
theorem subd10_1_668 : subd10_1 [2, 2, -1] = true := by decide +kernel
theorem subd10_1_669 : subd10_1 [2, 2, 0] = true := by decide +kernel
theorem subd10_1_670 : subd10_1 [2, 2, 1] = true := by decide +kernel
theorem subd10_1_671 : subd10_1 [2, 2, 2] = true := by decide +kernel
theorem sbd10_1_20 : ∀ q ∈ blkd10_1_20, subd10_1 q = true := by
  unfold blkd10_1_20
  exact List.forall_mem_cons.2 ⟨subd10_1_640, List.forall_mem_cons.2 ⟨subd10_1_641, List.forall_mem_cons.2 ⟨subd10_1_642, List.forall_mem_cons.2 ⟨subd10_1_643, List.forall_mem_cons.2 ⟨subd10_1_644, List.forall_mem_cons.2 ⟨subd10_1_645, List.forall_mem_cons.2 ⟨subd10_1_646, List.forall_mem_cons.2 ⟨subd10_1_647, List.forall_mem_cons.2 ⟨subd10_1_648, List.forall_mem_cons.2 ⟨subd10_1_649, List.forall_mem_cons.2 ⟨subd10_1_650, List.forall_mem_cons.2 ⟨subd10_1_651, List.forall_mem_cons.2 ⟨subd10_1_652, List.forall_mem_cons.2 ⟨subd10_1_653, List.forall_mem_cons.2 ⟨subd10_1_654, List.forall_mem_cons.2 ⟨subd10_1_655, List.forall_mem_cons.2 ⟨subd10_1_656, List.forall_mem_cons.2 ⟨subd10_1_657, List.forall_mem_cons.2 ⟨subd10_1_658, List.forall_mem_cons.2 ⟨subd10_1_659, List.forall_mem_cons.2 ⟨subd10_1_660, List.forall_mem_cons.2 ⟨subd10_1_661, List.forall_mem_cons.2 ⟨subd10_1_662, List.forall_mem_cons.2 ⟨subd10_1_663, List.forall_mem_cons.2 ⟨subd10_1_664, List.forall_mem_cons.2 ⟨subd10_1_665, List.forall_mem_cons.2 ⟨subd10_1_666, List.forall_mem_cons.2 ⟨subd10_1_667, List.forall_mem_cons.2 ⟨subd10_1_668, List.forall_mem_cons.2 ⟨subd10_1_669, List.forall_mem_cons.2 ⟨subd10_1_670, List.forall_mem_cons.2 ⟨subd10_1_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_672 : subd10_1 [2, 2, 3] = true := by decide +kernel
theorem subd10_1_673 : subd10_1 [2, 2, 4] = true := by decide +kernel
theorem subd10_1_674 : subd10_1 [2, 2, 5] = true := by decide +kernel
theorem subd10_1_675 : subd10_1 [2, 3] = true := by decide +kernel
theorem subd10_1_676 : subd10_1 [2, 4] = true := by decide +kernel
theorem subd10_1_677 : subd10_1 [3, -6] = true := by decide +kernel
theorem subd10_1_678 : subd10_1 [3, -5] = true := by decide +kernel
theorem subd10_1_679 : subd10_1 [3, -4] = true := by decide +kernel
theorem subd10_1_680 : subd10_1 [3, -3, -7] = true := by decide +kernel
theorem subd10_1_681 : subd10_1 [3, -3, -6] = true := by decide +kernel
theorem subd10_1_682 : subd10_1 [3, -3, -5] = true := by decide +kernel
theorem subd10_1_683 : subd10_1 [3, -3, -4] = true := by decide +kernel
theorem subd10_1_684 : subd10_1 [3, -3, -3] = true := by decide +kernel
theorem subd10_1_685 : subd10_1 [3, -3, -2] = true := by decide +kernel
theorem subd10_1_686 : subd10_1 [3, -3, -1] = true := by decide +kernel
theorem subd10_1_687 : subd10_1 [3, -3, 0] = true := by decide +kernel
theorem subd10_1_688 : subd10_1 [3, -3, 1] = true := by decide +kernel
theorem subd10_1_689 : subd10_1 [3, -3, 2] = true := by decide +kernel
theorem subd10_1_690 : subd10_1 [3, -3, 3] = true := by decide +kernel
theorem subd10_1_691 : subd10_1 [3, -3, 4] = true := by decide +kernel
theorem subd10_1_692 : subd10_1 [3, -3, 5] = true := by decide +kernel
theorem subd10_1_693 : subd10_1 [3, -2, -8] = true := by decide +kernel
theorem subd10_1_694 : subd10_1 [3, -2, -7] = true := by decide +kernel
theorem subd10_1_695 : subd10_1 [3, -2, -6] = true := by decide +kernel
theorem subd10_1_696 : subd10_1 [3, -2, -5] = true := by decide +kernel
theorem subd10_1_697 : subd10_1 [3, -2, -4] = true := by decide +kernel
theorem subd10_1_698 : subd10_1 [3, -2, -3] = true := by decide +kernel
theorem subd10_1_699 : subd10_1 [3, -2, -2] = true := by decide +kernel
theorem subd10_1_700 : subd10_1 [3, -2, -1] = true := by decide +kernel
theorem subd10_1_701 : subd10_1 [3, -2, 0] = true := by decide +kernel
theorem subd10_1_702 : subd10_1 [3, -2, 1] = true := by decide +kernel
theorem subd10_1_703 : subd10_1 [3, -2, 2] = true := by decide +kernel
theorem sbd10_1_21 : ∀ q ∈ blkd10_1_21, subd10_1 q = true := by
  unfold blkd10_1_21
  exact List.forall_mem_cons.2 ⟨subd10_1_672, List.forall_mem_cons.2 ⟨subd10_1_673, List.forall_mem_cons.2 ⟨subd10_1_674, List.forall_mem_cons.2 ⟨subd10_1_675, List.forall_mem_cons.2 ⟨subd10_1_676, List.forall_mem_cons.2 ⟨subd10_1_677, List.forall_mem_cons.2 ⟨subd10_1_678, List.forall_mem_cons.2 ⟨subd10_1_679, List.forall_mem_cons.2 ⟨subd10_1_680, List.forall_mem_cons.2 ⟨subd10_1_681, List.forall_mem_cons.2 ⟨subd10_1_682, List.forall_mem_cons.2 ⟨subd10_1_683, List.forall_mem_cons.2 ⟨subd10_1_684, List.forall_mem_cons.2 ⟨subd10_1_685, List.forall_mem_cons.2 ⟨subd10_1_686, List.forall_mem_cons.2 ⟨subd10_1_687, List.forall_mem_cons.2 ⟨subd10_1_688, List.forall_mem_cons.2 ⟨subd10_1_689, List.forall_mem_cons.2 ⟨subd10_1_690, List.forall_mem_cons.2 ⟨subd10_1_691, List.forall_mem_cons.2 ⟨subd10_1_692, List.forall_mem_cons.2 ⟨subd10_1_693, List.forall_mem_cons.2 ⟨subd10_1_694, List.forall_mem_cons.2 ⟨subd10_1_695, List.forall_mem_cons.2 ⟨subd10_1_696, List.forall_mem_cons.2 ⟨subd10_1_697, List.forall_mem_cons.2 ⟨subd10_1_698, List.forall_mem_cons.2 ⟨subd10_1_699, List.forall_mem_cons.2 ⟨subd10_1_700, List.forall_mem_cons.2 ⟨subd10_1_701, List.forall_mem_cons.2 ⟨subd10_1_702, List.forall_mem_cons.2 ⟨subd10_1_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_704 : subd10_1 [3, -2, 3] = true := by decide +kernel
theorem subd10_1_705 : subd10_1 [3, -2, 4] = true := by decide +kernel
theorem subd10_1_706 : subd10_1 [3, -2, 5] = true := by decide +kernel
theorem subd10_1_707 : subd10_1 [3, -2, 6] = true := by decide +kernel
theorem subd10_1_708 : subd10_1 [3, -1, -8] = true := by decide +kernel
theorem subd10_1_709 : subd10_1 [3, -1, -7] = true := by decide +kernel
theorem subd10_1_710 : subd10_1 [3, -1, -6] = true := by decide +kernel
theorem subd10_1_711 : subd10_1 [3, -1, -5] = true := by decide +kernel
theorem subd10_1_712 : subd10_1 [3, -1, -4] = true := by decide +kernel
theorem subd10_1_713 : subd10_1 [3, -1, -3] = true := by decide +kernel
theorem subd10_1_714 : subd10_1 [3, -1, -2] = true := by decide +kernel
theorem subd10_1_715 : subd10_1 [3, -1, -1] = true := by decide +kernel
theorem subd10_1_716 : subd10_1 [3, -1, 0] = true := by decide +kernel
theorem subd10_1_717 : subd10_1 [3, -1, 1] = true := by decide +kernel
theorem subd10_1_718 : subd10_1 [3, -1, 2] = true := by decide +kernel
theorem subd10_1_719 : subd10_1 [3, -1, 3] = true := by decide +kernel
theorem subd10_1_720 : subd10_1 [3, -1, 4] = true := by decide +kernel
theorem subd10_1_721 : subd10_1 [3, -1, 5] = true := by decide +kernel
theorem subd10_1_722 : subd10_1 [3, 0, -8] = true := by decide +kernel
theorem subd10_1_723 : subd10_1 [3, 0, -7] = true := by decide +kernel
theorem subd10_1_724 : subd10_1 [3, 0, -6] = true := by decide +kernel
theorem subd10_1_725 : subd10_1 [3, 0, -5] = true := by decide +kernel
theorem subd10_1_726 : subd10_1 [3, 0, -4] = true := by decide +kernel
theorem subd10_1_727 : subd10_1 [3, 0, -3] = true := by decide +kernel
theorem subd10_1_728 : subd10_1 [3, 0, -2] = true := by decide +kernel
theorem subd10_1_729 : subd10_1 [3, 0, -1] = true := by decide +kernel
theorem subd10_1_730 : subd10_1 [3, 0, 0] = true := by decide +kernel
theorem subd10_1_731 : subd10_1 [3, 0, 1] = true := by decide +kernel
theorem subd10_1_732 : subd10_1 [3, 0, 2] = true := by decide +kernel
theorem subd10_1_733 : subd10_1 [3, 0, 3] = true := by decide +kernel
theorem subd10_1_734 : subd10_1 [3, 0, 4] = true := by decide +kernel
theorem subd10_1_735 : subd10_1 [3, 0, 5] = true := by decide +kernel
theorem sbd10_1_22 : ∀ q ∈ blkd10_1_22, subd10_1 q = true := by
  unfold blkd10_1_22
  exact List.forall_mem_cons.2 ⟨subd10_1_704, List.forall_mem_cons.2 ⟨subd10_1_705, List.forall_mem_cons.2 ⟨subd10_1_706, List.forall_mem_cons.2 ⟨subd10_1_707, List.forall_mem_cons.2 ⟨subd10_1_708, List.forall_mem_cons.2 ⟨subd10_1_709, List.forall_mem_cons.2 ⟨subd10_1_710, List.forall_mem_cons.2 ⟨subd10_1_711, List.forall_mem_cons.2 ⟨subd10_1_712, List.forall_mem_cons.2 ⟨subd10_1_713, List.forall_mem_cons.2 ⟨subd10_1_714, List.forall_mem_cons.2 ⟨subd10_1_715, List.forall_mem_cons.2 ⟨subd10_1_716, List.forall_mem_cons.2 ⟨subd10_1_717, List.forall_mem_cons.2 ⟨subd10_1_718, List.forall_mem_cons.2 ⟨subd10_1_719, List.forall_mem_cons.2 ⟨subd10_1_720, List.forall_mem_cons.2 ⟨subd10_1_721, List.forall_mem_cons.2 ⟨subd10_1_722, List.forall_mem_cons.2 ⟨subd10_1_723, List.forall_mem_cons.2 ⟨subd10_1_724, List.forall_mem_cons.2 ⟨subd10_1_725, List.forall_mem_cons.2 ⟨subd10_1_726, List.forall_mem_cons.2 ⟨subd10_1_727, List.forall_mem_cons.2 ⟨subd10_1_728, List.forall_mem_cons.2 ⟨subd10_1_729, List.forall_mem_cons.2 ⟨subd10_1_730, List.forall_mem_cons.2 ⟨subd10_1_731, List.forall_mem_cons.2 ⟨subd10_1_732, List.forall_mem_cons.2 ⟨subd10_1_733, List.forall_mem_cons.2 ⟨subd10_1_734, List.forall_mem_cons.2 ⟨subd10_1_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_736 : subd10_1 [3, 1] = true := by decide +kernel
theorem subd10_1_737 : subd10_1 [3, 2] = true := by decide +kernel
theorem subd10_1_738 : subd10_1 [3, 3] = true := by decide +kernel
theorem subd10_1_739 : subd10_1 [4, -6] = true := by decide +kernel
theorem subd10_1_740 : subd10_1 [4, -5] = true := by decide +kernel
theorem subd10_1_741 : subd10_1 [4, -4] = true := by decide +kernel
theorem subd10_1_742 : subd10_1 [4, -3] = true := by decide +kernel
theorem subd10_1_743 : subd10_1 [4, -2] = true := by decide +kernel
theorem subd10_1_744 : subd10_1 [4, -1] = true := by decide +kernel
theorem subd10_1_745 : subd10_1 [4, 0] = true := by decide +kernel
theorem subd10_1_746 : subd10_1 [4, 1] = true := by decide +kernel
theorem subd10_1_747 : subd10_1 [4, 2] = true := by decide +kernel
theorem subd10_1_748 : subd10_1 [5] = true := by decide +kernel
theorem sbd10_1_23 : ∀ q ∈ blkd10_1_23, subd10_1 q = true := by
  unfold blkd10_1_23
  exact List.forall_mem_cons.2 ⟨subd10_1_736, List.forall_mem_cons.2 ⟨subd10_1_737, List.forall_mem_cons.2 ⟨subd10_1_738, List.forall_mem_cons.2 ⟨subd10_1_739, List.forall_mem_cons.2 ⟨subd10_1_740, List.forall_mem_cons.2 ⟨subd10_1_741, List.forall_mem_cons.2 ⟨subd10_1_742, List.forall_mem_cons.2 ⟨subd10_1_743, List.forall_mem_cons.2 ⟨subd10_1_744, List.forall_mem_cons.2 ⟨subd10_1_745, List.forall_mem_cons.2 ⟨subd10_1_746, List.forall_mem_cons.2 ⟨subd10_1_747, List.forall_mem_cons.2 ⟨subd10_1_748, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_2 : ldCheck G d10_2.U d10_2.ms ldd10_2 = true := by decide +kernel
theorem pre_okd10_2 : subPre G cell10 d10_2 = true := by decide +kernel
theorem subd10_2_0 : subd10_2 [-3] = true := by decide +kernel
theorem subd10_2_1 : subd10_2 [-2, -2] = true := by decide +kernel
theorem subd10_2_2 : subd10_2 [-2, -1, -8] = true := by decide +kernel
theorem subd10_2_3 : subd10_2 [-2, -1, -7] = true := by decide +kernel
theorem subd10_2_4 : subd10_2 [-2, -1, -6] = true := by decide +kernel
theorem subd10_2_5 : subd10_2 [-2, -1, -5] = true := by decide +kernel
theorem subd10_2_6 : subd10_2 [-2, -1, -4] = true := by decide +kernel
theorem subd10_2_7 : subd10_2 [-2, -1, -3] = true := by decide +kernel
theorem subd10_2_8 : subd10_2 [-2, -1, -2] = true := by decide +kernel
theorem subd10_2_9 : subd10_2 [-2, -1, -1] = true := by decide +kernel
theorem subd10_2_10 : subd10_2 [-2, -1, 0] = true := by decide +kernel
theorem subd10_2_11 : subd10_2 [-2, -1, 1] = true := by decide +kernel
theorem subd10_2_12 : subd10_2 [-2, -1, 2] = true := by decide +kernel
theorem subd10_2_13 : subd10_2 [-2, -1, 3] = true := by decide +kernel
theorem subd10_2_14 : subd10_2 [-2, -1, 4] = true := by decide +kernel
theorem subd10_2_15 : subd10_2 [-2, -1, 5] = true := by decide +kernel
theorem subd10_2_16 : subd10_2 [-2, -1, 6] = true := by decide +kernel
theorem subd10_2_17 : subd10_2 [-2, -1, 7] = true := by decide +kernel
theorem subd10_2_18 : subd10_2 [-2, -1, 8] = true := by decide +kernel
theorem subd10_2_19 : subd10_2 [-2, -1, 9] = true := by decide +kernel
theorem subd10_2_20 : subd10_2 [-2, 0, -11] = true := by decide +kernel
theorem subd10_2_21 : subd10_2 [-2, 0, -10] = true := by decide +kernel
theorem subd10_2_22 : subd10_2 [-2, 0, -9] = true := by decide +kernel
theorem subd10_2_23 : subd10_2 [-2, 0, -8] = true := by decide +kernel
theorem subd10_2_24 : subd10_2 [-2, 0, -7] = true := by decide +kernel
theorem subd10_2_25 : subd10_2 [-2, 0, -6] = true := by decide +kernel
theorem subd10_2_26 : subd10_2 [-2, 0, -5] = true := by decide +kernel
theorem subd10_2_27 : subd10_2 [-2, 0, -4] = true := by decide +kernel
theorem subd10_2_28 : subd10_2 [-2, 0, -3] = true := by decide +kernel
theorem subd10_2_29 : subd10_2 [-2, 0, -2] = true := by decide +kernel
theorem subd10_2_30 : subd10_2 [-2, 0, -1] = true := by decide +kernel
theorem subd10_2_31 : subd10_2 [-2, 0, 0] = true := by decide +kernel
theorem sbd10_2_0 : ∀ q ∈ blkd10_2_0, subd10_2 q = true := by
  unfold blkd10_2_0
  exact List.forall_mem_cons.2 ⟨subd10_2_0, List.forall_mem_cons.2 ⟨subd10_2_1, List.forall_mem_cons.2 ⟨subd10_2_2, List.forall_mem_cons.2 ⟨subd10_2_3, List.forall_mem_cons.2 ⟨subd10_2_4, List.forall_mem_cons.2 ⟨subd10_2_5, List.forall_mem_cons.2 ⟨subd10_2_6, List.forall_mem_cons.2 ⟨subd10_2_7, List.forall_mem_cons.2 ⟨subd10_2_8, List.forall_mem_cons.2 ⟨subd10_2_9, List.forall_mem_cons.2 ⟨subd10_2_10, List.forall_mem_cons.2 ⟨subd10_2_11, List.forall_mem_cons.2 ⟨subd10_2_12, List.forall_mem_cons.2 ⟨subd10_2_13, List.forall_mem_cons.2 ⟨subd10_2_14, List.forall_mem_cons.2 ⟨subd10_2_15, List.forall_mem_cons.2 ⟨subd10_2_16, List.forall_mem_cons.2 ⟨subd10_2_17, List.forall_mem_cons.2 ⟨subd10_2_18, List.forall_mem_cons.2 ⟨subd10_2_19, List.forall_mem_cons.2 ⟨subd10_2_20, List.forall_mem_cons.2 ⟨subd10_2_21, List.forall_mem_cons.2 ⟨subd10_2_22, List.forall_mem_cons.2 ⟨subd10_2_23, List.forall_mem_cons.2 ⟨subd10_2_24, List.forall_mem_cons.2 ⟨subd10_2_25, List.forall_mem_cons.2 ⟨subd10_2_26, List.forall_mem_cons.2 ⟨subd10_2_27, List.forall_mem_cons.2 ⟨subd10_2_28, List.forall_mem_cons.2 ⟨subd10_2_29, List.forall_mem_cons.2 ⟨subd10_2_30, List.forall_mem_cons.2 ⟨subd10_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_2_32 : subd10_2 [-2, 0, 1] = true := by decide +kernel
theorem subd10_2_33 : subd10_2 [-2, 0, 2] = true := by decide +kernel
theorem subd10_2_34 : subd10_2 [-2, 0, 3] = true := by decide +kernel
theorem subd10_2_35 : subd10_2 [-2, 0, 4] = true := by decide +kernel
theorem subd10_2_36 : subd10_2 [-2, 0, 5] = true := by decide +kernel
theorem subd10_2_37 : subd10_2 [-2, 0, 6] = true := by decide +kernel
theorem subd10_2_38 : subd10_2 [-2, 0, 7] = true := by decide +kernel
theorem subd10_2_39 : subd10_2 [-2, 0, 8] = true := by decide +kernel
theorem subd10_2_40 : subd10_2 [-2, 0, 9] = true := by decide +kernel
theorem subd10_2_41 : subd10_2 [-2, 0, 10] = true := by decide +kernel
theorem subd10_2_42 : subd10_2 [-2, 0, 11] = true := by decide +kernel
theorem subd10_2_43 : subd10_2 [-2, 0, 12] = true := by decide +kernel
theorem subd10_2_44 : subd10_2 [-2, 1, -11] = true := by decide +kernel
theorem subd10_2_45 : subd10_2 [-2, 1, -10] = true := by decide +kernel
theorem subd10_2_46 : subd10_2 [-2, 1, -9] = true := by decide +kernel
theorem subd10_2_47 : subd10_2 [-2, 1, -8] = true := by decide +kernel
theorem subd10_2_48 : subd10_2 [-2, 1, -7] = true := by decide +kernel
theorem subd10_2_49 : subd10_2 [-2, 1, -6] = true := by decide +kernel
theorem subd10_2_50 : subd10_2 [-2, 1, -5] = true := by decide +kernel
theorem subd10_2_51 : subd10_2 [-2, 1, -4] = true := by decide +kernel
theorem subd10_2_52 : subd10_2 [-2, 1, -3] = true := by decide +kernel
theorem subd10_2_53 : subd10_2 [-2, 1, -2] = true := by decide +kernel
theorem subd10_2_54 : subd10_2 [-2, 1, -1] = true := by decide +kernel
theorem subd10_2_55 : subd10_2 [-2, 1, 0] = true := by decide +kernel
theorem subd10_2_56 : subd10_2 [-2, 1, 1] = true := by decide +kernel
theorem subd10_2_57 : subd10_2 [-2, 1, 2] = true := by decide +kernel
theorem subd10_2_58 : subd10_2 [-2, 1, 3] = true := by decide +kernel
theorem subd10_2_59 : subd10_2 [-2, 1, 4] = true := by decide +kernel
theorem subd10_2_60 : subd10_2 [-2, 1, 5] = true := by decide +kernel
theorem subd10_2_61 : subd10_2 [-2, 1, 6] = true := by decide +kernel
theorem subd10_2_62 : subd10_2 [-2, 1, 7] = true := by decide +kernel
theorem subd10_2_63 : subd10_2 [-2, 1, 8] = true := by decide +kernel
theorem sbd10_2_1 : ∀ q ∈ blkd10_2_1, subd10_2 q = true := by
  unfold blkd10_2_1
  exact List.forall_mem_cons.2 ⟨subd10_2_32, List.forall_mem_cons.2 ⟨subd10_2_33, List.forall_mem_cons.2 ⟨subd10_2_34, List.forall_mem_cons.2 ⟨subd10_2_35, List.forall_mem_cons.2 ⟨subd10_2_36, List.forall_mem_cons.2 ⟨subd10_2_37, List.forall_mem_cons.2 ⟨subd10_2_38, List.forall_mem_cons.2 ⟨subd10_2_39, List.forall_mem_cons.2 ⟨subd10_2_40, List.forall_mem_cons.2 ⟨subd10_2_41, List.forall_mem_cons.2 ⟨subd10_2_42, List.forall_mem_cons.2 ⟨subd10_2_43, List.forall_mem_cons.2 ⟨subd10_2_44, List.forall_mem_cons.2 ⟨subd10_2_45, List.forall_mem_cons.2 ⟨subd10_2_46, List.forall_mem_cons.2 ⟨subd10_2_47, List.forall_mem_cons.2 ⟨subd10_2_48, List.forall_mem_cons.2 ⟨subd10_2_49, List.forall_mem_cons.2 ⟨subd10_2_50, List.forall_mem_cons.2 ⟨subd10_2_51, List.forall_mem_cons.2 ⟨subd10_2_52, List.forall_mem_cons.2 ⟨subd10_2_53, List.forall_mem_cons.2 ⟨subd10_2_54, List.forall_mem_cons.2 ⟨subd10_2_55, List.forall_mem_cons.2 ⟨subd10_2_56, List.forall_mem_cons.2 ⟨subd10_2_57, List.forall_mem_cons.2 ⟨subd10_2_58, List.forall_mem_cons.2 ⟨subd10_2_59, List.forall_mem_cons.2 ⟨subd10_2_60, List.forall_mem_cons.2 ⟨subd10_2_61, List.forall_mem_cons.2 ⟨subd10_2_62, List.forall_mem_cons.2 ⟨subd10_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_2_64 : subd10_2 [-2, 1, 9] = true := by decide +kernel
theorem subd10_2_65 : subd10_2 [-2, 1, 10] = true := by decide +kernel
theorem subd10_2_66 : subd10_2 [-2, 1, 11] = true := by decide +kernel
theorem subd10_2_67 : subd10_2 [-2, 1, 12] = true := by decide +kernel
theorem subd10_2_68 : subd10_2 [-2, 2, -10] = true := by decide +kernel
theorem subd10_2_69 : subd10_2 [-2, 2, -9] = true := by decide +kernel
theorem subd10_2_70 : subd10_2 [-2, 2, -8] = true := by decide +kernel
theorem subd10_2_71 : subd10_2 [-2, 2, -7] = true := by decide +kernel
theorem subd10_2_72 : subd10_2 [-2, 2, -6] = true := by decide +kernel
theorem subd10_2_73 : subd10_2 [-2, 2, -5] = true := by decide +kernel
theorem subd10_2_74 : subd10_2 [-2, 2, -4] = true := by decide +kernel
theorem subd10_2_75 : subd10_2 [-2, 2, -3] = true := by decide +kernel
theorem subd10_2_76 : subd10_2 [-2, 2, -2] = true := by decide +kernel
theorem subd10_2_77 : subd10_2 [-2, 2, -1] = true := by decide +kernel
theorem subd10_2_78 : subd10_2 [-2, 2, 0] = true := by decide +kernel
theorem subd10_2_79 : subd10_2 [-2, 2, 1] = true := by decide +kernel
theorem subd10_2_80 : subd10_2 [-2, 2, 2] = true := by decide +kernel
theorem subd10_2_81 : subd10_2 [-2, 2, 3] = true := by decide +kernel
theorem subd10_2_82 : subd10_2 [-2, 2, 4] = true := by decide +kernel
theorem subd10_2_83 : subd10_2 [-2, 2, 5] = true := by decide +kernel
theorem subd10_2_84 : subd10_2 [-2, 2, 6] = true := by decide +kernel
theorem subd10_2_85 : subd10_2 [-2, 2, 7] = true := by decide +kernel
theorem subd10_2_86 : subd10_2 [-2, 2, 8] = true := by decide +kernel
theorem subd10_2_87 : subd10_2 [-2, 2, 9] = true := by decide +kernel
theorem subd10_2_88 : subd10_2 [-2, 2, 10] = true := by decide +kernel
theorem subd10_2_89 : subd10_2 [-2, 2, 11] = true := by decide +kernel
theorem subd10_2_90 : subd10_2 [-2, 3, -7] = true := by decide +kernel
theorem subd10_2_91 : subd10_2 [-2, 3, -6] = true := by decide +kernel
theorem subd10_2_92 : subd10_2 [-2, 3, -5] = true := by decide +kernel
theorem subd10_2_93 : subd10_2 [-2, 3, -4] = true := by decide +kernel
theorem subd10_2_94 : subd10_2 [-2, 3, -3] = true := by decide +kernel
theorem subd10_2_95 : subd10_2 [-2, 3, -2] = true := by decide +kernel
theorem sbd10_2_2 : ∀ q ∈ blkd10_2_2, subd10_2 q = true := by
  unfold blkd10_2_2
  exact List.forall_mem_cons.2 ⟨subd10_2_64, List.forall_mem_cons.2 ⟨subd10_2_65, List.forall_mem_cons.2 ⟨subd10_2_66, List.forall_mem_cons.2 ⟨subd10_2_67, List.forall_mem_cons.2 ⟨subd10_2_68, List.forall_mem_cons.2 ⟨subd10_2_69, List.forall_mem_cons.2 ⟨subd10_2_70, List.forall_mem_cons.2 ⟨subd10_2_71, List.forall_mem_cons.2 ⟨subd10_2_72, List.forall_mem_cons.2 ⟨subd10_2_73, List.forall_mem_cons.2 ⟨subd10_2_74, List.forall_mem_cons.2 ⟨subd10_2_75, List.forall_mem_cons.2 ⟨subd10_2_76, List.forall_mem_cons.2 ⟨subd10_2_77, List.forall_mem_cons.2 ⟨subd10_2_78, List.forall_mem_cons.2 ⟨subd10_2_79, List.forall_mem_cons.2 ⟨subd10_2_80, List.forall_mem_cons.2 ⟨subd10_2_81, List.forall_mem_cons.2 ⟨subd10_2_82, List.forall_mem_cons.2 ⟨subd10_2_83, List.forall_mem_cons.2 ⟨subd10_2_84, List.forall_mem_cons.2 ⟨subd10_2_85, List.forall_mem_cons.2 ⟨subd10_2_86, List.forall_mem_cons.2 ⟨subd10_2_87, List.forall_mem_cons.2 ⟨subd10_2_88, List.forall_mem_cons.2 ⟨subd10_2_89, List.forall_mem_cons.2 ⟨subd10_2_90, List.forall_mem_cons.2 ⟨subd10_2_91, List.forall_mem_cons.2 ⟨subd10_2_92, List.forall_mem_cons.2 ⟨subd10_2_93, List.forall_mem_cons.2 ⟨subd10_2_94, List.forall_mem_cons.2 ⟨subd10_2_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_2_96 : subd10_2 [-2, 3, -1] = true := by decide +kernel
theorem subd10_2_97 : subd10_2 [-2, 3, 0] = true := by decide +kernel
theorem subd10_2_98 : subd10_2 [-2, 3, 1] = true := by decide +kernel
theorem subd10_2_99 : subd10_2 [-2, 3, 2] = true := by decide +kernel
theorem subd10_2_100 : subd10_2 [-2, 3, 3] = true := by decide +kernel
theorem subd10_2_101 : subd10_2 [-2, 3, 4] = true := by decide +kernel
theorem subd10_2_102 : subd10_2 [-2, 3, 5] = true := by decide +kernel
theorem subd10_2_103 : subd10_2 [-2, 3, 6] = true := by decide +kernel
theorem subd10_2_104 : subd10_2 [-2, 3, 7] = true := by decide +kernel
theorem subd10_2_105 : subd10_2 [-1, -3] = true := by decide +kernel
theorem subd10_2_106 : subd10_2 [-1, -2, -10] = true := by decide +kernel
theorem subd10_2_107 : subd10_2 [-1, -2, -9] = true := by decide +kernel
theorem subd10_2_108 : subd10_2 [-1, -2, -8] = true := by decide +kernel
theorem subd10_2_109 : subd10_2 [-1, -2, -7] = true := by decide +kernel
theorem subd10_2_110 : subd10_2 [-1, -2, -6] = true := by decide +kernel
theorem subd10_2_111 : subd10_2 [-1, -2, -5] = true := by decide +kernel
theorem subd10_2_112 : subd10_2 [-1, -2, -4] = true := by decide +kernel
theorem subd10_2_113 : subd10_2 [-1, -2, -3] = true := by decide +kernel
theorem subd10_2_114 : subd10_2 [-1, -2, -2] = true := by decide +kernel
theorem subd10_2_115 : subd10_2 [-1, -2, -1] = true := by decide +kernel
theorem subd10_2_116 : subd10_2 [-1, -2, 0] = true := by decide +kernel
theorem subd10_2_117 : subd10_2 [-1, -2, 1] = true := by decide +kernel
theorem subd10_2_118 : subd10_2 [-1, -2, 2] = true := by decide +kernel
theorem subd10_2_119 : subd10_2 [-1, -2, 3] = true := by decide +kernel
theorem subd10_2_120 : subd10_2 [-1, -2, 4] = true := by decide +kernel
theorem subd10_2_121 : subd10_2 [-1, -2, 5] = true := by decide +kernel
theorem subd10_2_122 : subd10_2 [-1, -2, 6] = true := by decide +kernel
theorem subd10_2_123 : subd10_2 [-1, -2, 7] = true := by decide +kernel
theorem subd10_2_124 : subd10_2 [-1, -2, 8] = true := by decide +kernel
theorem subd10_2_125 : subd10_2 [-1, -2, 9] = true := by decide +kernel
theorem subd10_2_126 : subd10_2 [-1, -2, 10] = true := by decide +kernel
theorem subd10_2_127 : subd10_2 [-1, -1, -13] = true := by decide +kernel
theorem sbd10_2_3 : ∀ q ∈ blkd10_2_3, subd10_2 q = true := by
  unfold blkd10_2_3
  exact List.forall_mem_cons.2 ⟨subd10_2_96, List.forall_mem_cons.2 ⟨subd10_2_97, List.forall_mem_cons.2 ⟨subd10_2_98, List.forall_mem_cons.2 ⟨subd10_2_99, List.forall_mem_cons.2 ⟨subd10_2_100, List.forall_mem_cons.2 ⟨subd10_2_101, List.forall_mem_cons.2 ⟨subd10_2_102, List.forall_mem_cons.2 ⟨subd10_2_103, List.forall_mem_cons.2 ⟨subd10_2_104, List.forall_mem_cons.2 ⟨subd10_2_105, List.forall_mem_cons.2 ⟨subd10_2_106, List.forall_mem_cons.2 ⟨subd10_2_107, List.forall_mem_cons.2 ⟨subd10_2_108, List.forall_mem_cons.2 ⟨subd10_2_109, List.forall_mem_cons.2 ⟨subd10_2_110, List.forall_mem_cons.2 ⟨subd10_2_111, List.forall_mem_cons.2 ⟨subd10_2_112, List.forall_mem_cons.2 ⟨subd10_2_113, List.forall_mem_cons.2 ⟨subd10_2_114, List.forall_mem_cons.2 ⟨subd10_2_115, List.forall_mem_cons.2 ⟨subd10_2_116, List.forall_mem_cons.2 ⟨subd10_2_117, List.forall_mem_cons.2 ⟨subd10_2_118, List.forall_mem_cons.2 ⟨subd10_2_119, List.forall_mem_cons.2 ⟨subd10_2_120, List.forall_mem_cons.2 ⟨subd10_2_121, List.forall_mem_cons.2 ⟨subd10_2_122, List.forall_mem_cons.2 ⟨subd10_2_123, List.forall_mem_cons.2 ⟨subd10_2_124, List.forall_mem_cons.2 ⟨subd10_2_125, List.forall_mem_cons.2 ⟨subd10_2_126, List.forall_mem_cons.2 ⟨subd10_2_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C135
