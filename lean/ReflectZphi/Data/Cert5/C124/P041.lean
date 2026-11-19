import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_14_512 : subd7_14 [1, -2, 10] = true := by decide +kernel
theorem subd7_14_513 : subd7_14 [1, -1, -10] = true := by decide +kernel
theorem subd7_14_514 : subd7_14 [1, -1, -9] = true := by decide +kernel
theorem subd7_14_515 : subd7_14 [1, -1, -8] = true := by decide +kernel
theorem subd7_14_516 : subd7_14 [1, -1, -7] = true := by decide +kernel
theorem subd7_14_517 : subd7_14 [1, -1, -6] = true := by decide +kernel
theorem subd7_14_518 : subd7_14 [1, -1, -5] = true := by decide +kernel
theorem subd7_14_519 : subd7_14 [1, -1, -4] = true := by decide +kernel
theorem subd7_14_520 : subd7_14 [1, -1, -3] = true := by decide +kernel
theorem subd7_14_521 : subd7_14 [1, -1, -2] = true := by decide +kernel
theorem subd7_14_522 : subd7_14 [1, -1, -1] = true := by decide +kernel
theorem subd7_14_523 : subd7_14 [1, -1, 0] = true := by decide +kernel
theorem subd7_14_524 : subd7_14 [1, -1, 1] = true := by decide +kernel
theorem subd7_14_525 : subd7_14 [1, -1, 2] = true := by decide +kernel
theorem subd7_14_526 : subd7_14 [1, -1, 3] = true := by decide +kernel
theorem subd7_14_527 : subd7_14 [1, -1, 4] = true := by decide +kernel
theorem subd7_14_528 : subd7_14 [1, -1, 5] = true := by decide +kernel
theorem subd7_14_529 : subd7_14 [1, -1, 6] = true := by decide +kernel
theorem subd7_14_530 : subd7_14 [1, -1, 7] = true := by decide +kernel
theorem subd7_14_531 : subd7_14 [1, -1, 8] = true := by decide +kernel
theorem subd7_14_532 : subd7_14 [1, -1, 9] = true := by decide +kernel
theorem subd7_14_533 : subd7_14 [1, -1, 10] = true := by decide +kernel
theorem subd7_14_534 : subd7_14 [1, 0, -11] = true := by decide +kernel
theorem subd7_14_535 : subd7_14 [1, 0, -10] = true := by decide +kernel
theorem subd7_14_536 : subd7_14 [1, 0, -9] = true := by decide +kernel
theorem subd7_14_537 : subd7_14 [1, 0, -8] = true := by decide +kernel
theorem subd7_14_538 : subd7_14 [1, 0, -7] = true := by decide +kernel
theorem subd7_14_539 : subd7_14 [1, 0, -6] = true := by decide +kernel
theorem subd7_14_540 : subd7_14 [1, 0, -5] = true := by decide +kernel
theorem subd7_14_541 : subd7_14 [1, 0, -4] = true := by decide +kernel
theorem subd7_14_542 : subd7_14 [1, 0, -3] = true := by decide +kernel
theorem subd7_14_543 : subd7_14 [1, 0, -2] = true := by decide +kernel
theorem sbd7_14_16 : ∀ q ∈ blkd7_14_16, subd7_14 q = true := by
  unfold blkd7_14_16
  exact List.forall_mem_cons.2 ⟨subd7_14_512, List.forall_mem_cons.2 ⟨subd7_14_513, List.forall_mem_cons.2 ⟨subd7_14_514, List.forall_mem_cons.2 ⟨subd7_14_515, List.forall_mem_cons.2 ⟨subd7_14_516, List.forall_mem_cons.2 ⟨subd7_14_517, List.forall_mem_cons.2 ⟨subd7_14_518, List.forall_mem_cons.2 ⟨subd7_14_519, List.forall_mem_cons.2 ⟨subd7_14_520, List.forall_mem_cons.2 ⟨subd7_14_521, List.forall_mem_cons.2 ⟨subd7_14_522, List.forall_mem_cons.2 ⟨subd7_14_523, List.forall_mem_cons.2 ⟨subd7_14_524, List.forall_mem_cons.2 ⟨subd7_14_525, List.forall_mem_cons.2 ⟨subd7_14_526, List.forall_mem_cons.2 ⟨subd7_14_527, List.forall_mem_cons.2 ⟨subd7_14_528, List.forall_mem_cons.2 ⟨subd7_14_529, List.forall_mem_cons.2 ⟨subd7_14_530, List.forall_mem_cons.2 ⟨subd7_14_531, List.forall_mem_cons.2 ⟨subd7_14_532, List.forall_mem_cons.2 ⟨subd7_14_533, List.forall_mem_cons.2 ⟨subd7_14_534, List.forall_mem_cons.2 ⟨subd7_14_535, List.forall_mem_cons.2 ⟨subd7_14_536, List.forall_mem_cons.2 ⟨subd7_14_537, List.forall_mem_cons.2 ⟨subd7_14_538, List.forall_mem_cons.2 ⟨subd7_14_539, List.forall_mem_cons.2 ⟨subd7_14_540, List.forall_mem_cons.2 ⟨subd7_14_541, List.forall_mem_cons.2 ⟨subd7_14_542, List.forall_mem_cons.2 ⟨subd7_14_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_14_544 : subd7_14 [1, 0, -1] = true := by decide +kernel
theorem subd7_14_545 : subd7_14 [1, 0, 0] = true := by decide +kernel
theorem subd7_14_546 : subd7_14 [1, 0, 1] = true := by decide +kernel
theorem subd7_14_547 : subd7_14 [1, 0, 2] = true := by decide +kernel
theorem subd7_14_548 : subd7_14 [1, 0, 3] = true := by decide +kernel
theorem subd7_14_549 : subd7_14 [1, 0, 4] = true := by decide +kernel
theorem subd7_14_550 : subd7_14 [1, 0, 5] = true := by decide +kernel
theorem subd7_14_551 : subd7_14 [1, 0, 6] = true := by decide +kernel
theorem subd7_14_552 : subd7_14 [1, 0, 7] = true := by decide +kernel
theorem subd7_14_553 : subd7_14 [1, 0, 8] = true := by decide +kernel
theorem subd7_14_554 : subd7_14 [1, 0, 9] = true := by decide +kernel
theorem subd7_14_555 : subd7_14 [1, 0, 10] = true := by decide +kernel
theorem subd7_14_556 : subd7_14 [1, 1, -11] = true := by decide +kernel
theorem subd7_14_557 : subd7_14 [1, 1, -10] = true := by decide +kernel
theorem subd7_14_558 : subd7_14 [1, 1, -9] = true := by decide +kernel
theorem subd7_14_559 : subd7_14 [1, 1, -8] = true := by decide +kernel
theorem subd7_14_560 : subd7_14 [1, 1, -7] = true := by decide +kernel
theorem subd7_14_561 : subd7_14 [1, 1, -6] = true := by decide +kernel
theorem subd7_14_562 : subd7_14 [1, 1, -5] = true := by decide +kernel
theorem subd7_14_563 : subd7_14 [1, 1, -4] = true := by decide +kernel
theorem subd7_14_564 : subd7_14 [1, 1, -3] = true := by decide +kernel
theorem subd7_14_565 : subd7_14 [1, 1, -2] = true := by decide +kernel
theorem subd7_14_566 : subd7_14 [1, 1, -1] = true := by decide +kernel
theorem subd7_14_567 : subd7_14 [1, 1, 0] = true := by decide +kernel
theorem subd7_14_568 : subd7_14 [1, 1, 1] = true := by decide +kernel
theorem subd7_14_569 : subd7_14 [1, 1, 2] = true := by decide +kernel
theorem subd7_14_570 : subd7_14 [1, 1, 3] = true := by decide +kernel
theorem subd7_14_571 : subd7_14 [1, 1, 4] = true := by decide +kernel
theorem subd7_14_572 : subd7_14 [1, 1, 5] = true := by decide +kernel
theorem subd7_14_573 : subd7_14 [1, 1, 6] = true := by decide +kernel
theorem subd7_14_574 : subd7_14 [1, 1, 7] = true := by decide +kernel
theorem subd7_14_575 : subd7_14 [1, 1, 8] = true := by decide +kernel
theorem sbd7_14_17 : ∀ q ∈ blkd7_14_17, subd7_14 q = true := by
  unfold blkd7_14_17
  exact List.forall_mem_cons.2 ⟨subd7_14_544, List.forall_mem_cons.2 ⟨subd7_14_545, List.forall_mem_cons.2 ⟨subd7_14_546, List.forall_mem_cons.2 ⟨subd7_14_547, List.forall_mem_cons.2 ⟨subd7_14_548, List.forall_mem_cons.2 ⟨subd7_14_549, List.forall_mem_cons.2 ⟨subd7_14_550, List.forall_mem_cons.2 ⟨subd7_14_551, List.forall_mem_cons.2 ⟨subd7_14_552, List.forall_mem_cons.2 ⟨subd7_14_553, List.forall_mem_cons.2 ⟨subd7_14_554, List.forall_mem_cons.2 ⟨subd7_14_555, List.forall_mem_cons.2 ⟨subd7_14_556, List.forall_mem_cons.2 ⟨subd7_14_557, List.forall_mem_cons.2 ⟨subd7_14_558, List.forall_mem_cons.2 ⟨subd7_14_559, List.forall_mem_cons.2 ⟨subd7_14_560, List.forall_mem_cons.2 ⟨subd7_14_561, List.forall_mem_cons.2 ⟨subd7_14_562, List.forall_mem_cons.2 ⟨subd7_14_563, List.forall_mem_cons.2 ⟨subd7_14_564, List.forall_mem_cons.2 ⟨subd7_14_565, List.forall_mem_cons.2 ⟨subd7_14_566, List.forall_mem_cons.2 ⟨subd7_14_567, List.forall_mem_cons.2 ⟨subd7_14_568, List.forall_mem_cons.2 ⟨subd7_14_569, List.forall_mem_cons.2 ⟨subd7_14_570, List.forall_mem_cons.2 ⟨subd7_14_571, List.forall_mem_cons.2 ⟨subd7_14_572, List.forall_mem_cons.2 ⟨subd7_14_573, List.forall_mem_cons.2 ⟨subd7_14_574, List.forall_mem_cons.2 ⟨subd7_14_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_14_576 : subd7_14 [1, 1, 9] = true := by decide +kernel
theorem subd7_14_577 : subd7_14 [1, 1, 10] = true := by decide +kernel
theorem subd7_14_578 : subd7_14 [1, 2, -10] = true := by decide +kernel
theorem subd7_14_579 : subd7_14 [1, 2, -9] = true := by decide +kernel
theorem subd7_14_580 : subd7_14 [1, 2, -8] = true := by decide +kernel
theorem subd7_14_581 : subd7_14 [1, 2, -7] = true := by decide +kernel
theorem subd7_14_582 : subd7_14 [1, 2, -6] = true := by decide +kernel
theorem subd7_14_583 : subd7_14 [1, 2, -5] = true := by decide +kernel
theorem subd7_14_584 : subd7_14 [1, 2, -4] = true := by decide +kernel
theorem subd7_14_585 : subd7_14 [1, 2, -3] = true := by decide +kernel
theorem subd7_14_586 : subd7_14 [1, 2, -2] = true := by decide +kernel
theorem subd7_14_587 : subd7_14 [1, 2, -1] = true := by decide +kernel
theorem subd7_14_588 : subd7_14 [1, 2, 0] = true := by decide +kernel
theorem subd7_14_589 : subd7_14 [1, 2, 1] = true := by decide +kernel
theorem subd7_14_590 : subd7_14 [1, 2, 2] = true := by decide +kernel
theorem subd7_14_591 : subd7_14 [1, 2, 3] = true := by decide +kernel
theorem subd7_14_592 : subd7_14 [1, 2, 4] = true := by decide +kernel
theorem subd7_14_593 : subd7_14 [1, 2, 5] = true := by decide +kernel
theorem subd7_14_594 : subd7_14 [1, 2, 6] = true := by decide +kernel
theorem subd7_14_595 : subd7_14 [1, 2, 7] = true := by decide +kernel
theorem subd7_14_596 : subd7_14 [1, 2, 8] = true := by decide +kernel
theorem subd7_14_597 : subd7_14 [1, 2, 9] = true := by decide +kernel
theorem subd7_14_598 : subd7_14 [1, 3, -9] = true := by decide +kernel
theorem subd7_14_599 : subd7_14 [1, 3, -8] = true := by decide +kernel
theorem subd7_14_600 : subd7_14 [1, 3, -7] = true := by decide +kernel
theorem subd7_14_601 : subd7_14 [1, 3, -6] = true := by decide +kernel
theorem subd7_14_602 : subd7_14 [1, 3, -5] = true := by decide +kernel
theorem subd7_14_603 : subd7_14 [1, 3, -4] = true := by decide +kernel
theorem subd7_14_604 : subd7_14 [1, 3, -3] = true := by decide +kernel
theorem subd7_14_605 : subd7_14 [1, 3, -2] = true := by decide +kernel
theorem subd7_14_606 : subd7_14 [1, 3, -1] = true := by decide +kernel
theorem subd7_14_607 : subd7_14 [1, 3, 0] = true := by decide +kernel
theorem sbd7_14_18 : ∀ q ∈ blkd7_14_18, subd7_14 q = true := by
  unfold blkd7_14_18
  exact List.forall_mem_cons.2 ⟨subd7_14_576, List.forall_mem_cons.2 ⟨subd7_14_577, List.forall_mem_cons.2 ⟨subd7_14_578, List.forall_mem_cons.2 ⟨subd7_14_579, List.forall_mem_cons.2 ⟨subd7_14_580, List.forall_mem_cons.2 ⟨subd7_14_581, List.forall_mem_cons.2 ⟨subd7_14_582, List.forall_mem_cons.2 ⟨subd7_14_583, List.forall_mem_cons.2 ⟨subd7_14_584, List.forall_mem_cons.2 ⟨subd7_14_585, List.forall_mem_cons.2 ⟨subd7_14_586, List.forall_mem_cons.2 ⟨subd7_14_587, List.forall_mem_cons.2 ⟨subd7_14_588, List.forall_mem_cons.2 ⟨subd7_14_589, List.forall_mem_cons.2 ⟨subd7_14_590, List.forall_mem_cons.2 ⟨subd7_14_591, List.forall_mem_cons.2 ⟨subd7_14_592, List.forall_mem_cons.2 ⟨subd7_14_593, List.forall_mem_cons.2 ⟨subd7_14_594, List.forall_mem_cons.2 ⟨subd7_14_595, List.forall_mem_cons.2 ⟨subd7_14_596, List.forall_mem_cons.2 ⟨subd7_14_597, List.forall_mem_cons.2 ⟨subd7_14_598, List.forall_mem_cons.2 ⟨subd7_14_599, List.forall_mem_cons.2 ⟨subd7_14_600, List.forall_mem_cons.2 ⟨subd7_14_601, List.forall_mem_cons.2 ⟨subd7_14_602, List.forall_mem_cons.2 ⟨subd7_14_603, List.forall_mem_cons.2 ⟨subd7_14_604, List.forall_mem_cons.2 ⟨subd7_14_605, List.forall_mem_cons.2 ⟨subd7_14_606, List.forall_mem_cons.2 ⟨subd7_14_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_14_608 : subd7_14 [1, 3, 1] = true := by decide +kernel
theorem subd7_14_609 : subd7_14 [1, 3, 2] = true := by decide +kernel
theorem subd7_14_610 : subd7_14 [1, 3, 3] = true := by decide +kernel
theorem subd7_14_611 : subd7_14 [1, 3, 4] = true := by decide +kernel
theorem subd7_14_612 : subd7_14 [1, 3, 5] = true := by decide +kernel
theorem subd7_14_613 : subd7_14 [1, 3, 6] = true := by decide +kernel
theorem subd7_14_614 : subd7_14 [1, 3, 7] = true := by decide +kernel
theorem subd7_14_615 : subd7_14 [1, 4] = true := by decide +kernel
theorem subd7_14_616 : subd7_14 [2, -4] = true := by decide +kernel
theorem subd7_14_617 : subd7_14 [2, -3] = true := by decide +kernel
theorem subd7_14_618 : subd7_14 [2, -2, -8] = true := by decide +kernel
theorem subd7_14_619 : subd7_14 [2, -2, -7] = true := by decide +kernel
theorem subd7_14_620 : subd7_14 [2, -2, -6] = true := by decide +kernel
theorem subd7_14_621 : subd7_14 [2, -2, -5] = true := by decide +kernel
theorem subd7_14_622 : subd7_14 [2, -2, -4] = true := by decide +kernel
theorem subd7_14_623 : subd7_14 [2, -2, -3] = true := by decide +kernel
theorem subd7_14_624 : subd7_14 [2, -2, -2] = true := by decide +kernel
theorem subd7_14_625 : subd7_14 [2, -2, -1] = true := by decide +kernel
theorem subd7_14_626 : subd7_14 [2, -2, 0] = true := by decide +kernel
theorem subd7_14_627 : subd7_14 [2, -2, 1] = true := by decide +kernel
theorem subd7_14_628 : subd7_14 [2, -2, 2] = true := by decide +kernel
theorem subd7_14_629 : subd7_14 [2, -2, 3] = true := by decide +kernel
theorem subd7_14_630 : subd7_14 [2, -2, 4] = true := by decide +kernel
theorem subd7_14_631 : subd7_14 [2, -2, 5] = true := by decide +kernel
theorem subd7_14_632 : subd7_14 [2, -2, 6] = true := by decide +kernel
theorem subd7_14_633 : subd7_14 [2, -2, 7] = true := by decide +kernel
theorem subd7_14_634 : subd7_14 [2, -2, 8] = true := by decide +kernel
theorem subd7_14_635 : subd7_14 [2, -2, 9] = true := by decide +kernel
theorem subd7_14_636 : subd7_14 [2, -1, -9] = true := by decide +kernel
theorem subd7_14_637 : subd7_14 [2, -1, -8] = true := by decide +kernel
theorem subd7_14_638 : subd7_14 [2, -1, -7] = true := by decide +kernel
theorem subd7_14_639 : subd7_14 [2, -1, -6] = true := by decide +kernel
theorem sbd7_14_19 : ∀ q ∈ blkd7_14_19, subd7_14 q = true := by
  unfold blkd7_14_19
  exact List.forall_mem_cons.2 ⟨subd7_14_608, List.forall_mem_cons.2 ⟨subd7_14_609, List.forall_mem_cons.2 ⟨subd7_14_610, List.forall_mem_cons.2 ⟨subd7_14_611, List.forall_mem_cons.2 ⟨subd7_14_612, List.forall_mem_cons.2 ⟨subd7_14_613, List.forall_mem_cons.2 ⟨subd7_14_614, List.forall_mem_cons.2 ⟨subd7_14_615, List.forall_mem_cons.2 ⟨subd7_14_616, List.forall_mem_cons.2 ⟨subd7_14_617, List.forall_mem_cons.2 ⟨subd7_14_618, List.forall_mem_cons.2 ⟨subd7_14_619, List.forall_mem_cons.2 ⟨subd7_14_620, List.forall_mem_cons.2 ⟨subd7_14_621, List.forall_mem_cons.2 ⟨subd7_14_622, List.forall_mem_cons.2 ⟨subd7_14_623, List.forall_mem_cons.2 ⟨subd7_14_624, List.forall_mem_cons.2 ⟨subd7_14_625, List.forall_mem_cons.2 ⟨subd7_14_626, List.forall_mem_cons.2 ⟨subd7_14_627, List.forall_mem_cons.2 ⟨subd7_14_628, List.forall_mem_cons.2 ⟨subd7_14_629, List.forall_mem_cons.2 ⟨subd7_14_630, List.forall_mem_cons.2 ⟨subd7_14_631, List.forall_mem_cons.2 ⟨subd7_14_632, List.forall_mem_cons.2 ⟨subd7_14_633, List.forall_mem_cons.2 ⟨subd7_14_634, List.forall_mem_cons.2 ⟨subd7_14_635, List.forall_mem_cons.2 ⟨subd7_14_636, List.forall_mem_cons.2 ⟨subd7_14_637, List.forall_mem_cons.2 ⟨subd7_14_638, List.forall_mem_cons.2 ⟨subd7_14_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_14_640 : subd7_14 [2, -1, -5] = true := by decide +kernel
theorem subd7_14_641 : subd7_14 [2, -1, -4] = true := by decide +kernel
theorem subd7_14_642 : subd7_14 [2, -1, -3] = true := by decide +kernel
theorem subd7_14_643 : subd7_14 [2, -1, -2] = true := by decide +kernel
theorem subd7_14_644 : subd7_14 [2, -1, -1] = true := by decide +kernel
theorem subd7_14_645 : subd7_14 [2, -1, 0] = true := by decide +kernel
theorem subd7_14_646 : subd7_14 [2, -1, 1] = true := by decide +kernel
theorem subd7_14_647 : subd7_14 [2, -1, 2] = true := by decide +kernel
theorem subd7_14_648 : subd7_14 [2, -1, 3] = true := by decide +kernel
theorem subd7_14_649 : subd7_14 [2, -1, 4] = true := by decide +kernel
theorem subd7_14_650 : subd7_14 [2, -1, 5] = true := by decide +kernel
theorem subd7_14_651 : subd7_14 [2, -1, 6] = true := by decide +kernel
theorem subd7_14_652 : subd7_14 [2, -1, 7] = true := by decide +kernel
theorem subd7_14_653 : subd7_14 [2, -1, 8] = true := by decide +kernel
theorem subd7_14_654 : subd7_14 [2, -1, 9] = true := by decide +kernel
theorem subd7_14_655 : subd7_14 [2, -1, 10] = true := by decide +kernel
theorem subd7_14_656 : subd7_14 [2, 0, -10] = true := by decide +kernel
theorem subd7_14_657 : subd7_14 [2, 0, -9] = true := by decide +kernel
theorem subd7_14_658 : subd7_14 [2, 0, -8] = true := by decide +kernel
theorem subd7_14_659 : subd7_14 [2, 0, -7] = true := by decide +kernel
theorem subd7_14_660 : subd7_14 [2, 0, -6] = true := by decide +kernel
theorem subd7_14_661 : subd7_14 [2, 0, -5] = true := by decide +kernel
theorem subd7_14_662 : subd7_14 [2, 0, -4] = true := by decide +kernel
theorem subd7_14_663 : subd7_14 [2, 0, -3] = true := by decide +kernel
theorem subd7_14_664 : subd7_14 [2, 0, -2] = true := by decide +kernel
theorem subd7_14_665 : subd7_14 [2, 0, -1] = true := by decide +kernel
theorem subd7_14_666 : subd7_14 [2, 0, 0] = true := by decide +kernel
theorem subd7_14_667 : subd7_14 [2, 0, 1] = true := by decide +kernel
theorem subd7_14_668 : subd7_14 [2, 0, 2] = true := by decide +kernel
theorem subd7_14_669 : subd7_14 [2, 0, 3] = true := by decide +kernel
theorem subd7_14_670 : subd7_14 [2, 0, 4] = true := by decide +kernel
theorem subd7_14_671 : subd7_14 [2, 0, 5] = true := by decide +kernel
theorem sbd7_14_20 : ∀ q ∈ blkd7_14_20, subd7_14 q = true := by
  unfold blkd7_14_20
  exact List.forall_mem_cons.2 ⟨subd7_14_640, List.forall_mem_cons.2 ⟨subd7_14_641, List.forall_mem_cons.2 ⟨subd7_14_642, List.forall_mem_cons.2 ⟨subd7_14_643, List.forall_mem_cons.2 ⟨subd7_14_644, List.forall_mem_cons.2 ⟨subd7_14_645, List.forall_mem_cons.2 ⟨subd7_14_646, List.forall_mem_cons.2 ⟨subd7_14_647, List.forall_mem_cons.2 ⟨subd7_14_648, List.forall_mem_cons.2 ⟨subd7_14_649, List.forall_mem_cons.2 ⟨subd7_14_650, List.forall_mem_cons.2 ⟨subd7_14_651, List.forall_mem_cons.2 ⟨subd7_14_652, List.forall_mem_cons.2 ⟨subd7_14_653, List.forall_mem_cons.2 ⟨subd7_14_654, List.forall_mem_cons.2 ⟨subd7_14_655, List.forall_mem_cons.2 ⟨subd7_14_656, List.forall_mem_cons.2 ⟨subd7_14_657, List.forall_mem_cons.2 ⟨subd7_14_658, List.forall_mem_cons.2 ⟨subd7_14_659, List.forall_mem_cons.2 ⟨subd7_14_660, List.forall_mem_cons.2 ⟨subd7_14_661, List.forall_mem_cons.2 ⟨subd7_14_662, List.forall_mem_cons.2 ⟨subd7_14_663, List.forall_mem_cons.2 ⟨subd7_14_664, List.forall_mem_cons.2 ⟨subd7_14_665, List.forall_mem_cons.2 ⟨subd7_14_666, List.forall_mem_cons.2 ⟨subd7_14_667, List.forall_mem_cons.2 ⟨subd7_14_668, List.forall_mem_cons.2 ⟨subd7_14_669, List.forall_mem_cons.2 ⟨subd7_14_670, List.forall_mem_cons.2 ⟨subd7_14_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_14_672 : subd7_14 [2, 0, 6] = true := by decide +kernel
theorem subd7_14_673 : subd7_14 [2, 0, 7] = true := by decide +kernel
theorem subd7_14_674 : subd7_14 [2, 0, 8] = true := by decide +kernel
theorem subd7_14_675 : subd7_14 [2, 0, 9] = true := by decide +kernel
theorem subd7_14_676 : subd7_14 [2, 0, 10] = true := by decide +kernel
theorem subd7_14_677 : subd7_14 [2, 1, -10] = true := by decide +kernel
theorem subd7_14_678 : subd7_14 [2, 1, -9] = true := by decide +kernel
theorem subd7_14_679 : subd7_14 [2, 1, -8] = true := by decide +kernel
theorem subd7_14_680 : subd7_14 [2, 1, -7] = true := by decide +kernel
theorem subd7_14_681 : subd7_14 [2, 1, -6] = true := by decide +kernel
theorem subd7_14_682 : subd7_14 [2, 1, -5] = true := by decide +kernel
theorem subd7_14_683 : subd7_14 [2, 1, -4] = true := by decide +kernel
theorem subd7_14_684 : subd7_14 [2, 1, -3] = true := by decide +kernel
theorem subd7_14_685 : subd7_14 [2, 1, -2] = true := by decide +kernel
theorem subd7_14_686 : subd7_14 [2, 1, -1] = true := by decide +kernel
theorem subd7_14_687 : subd7_14 [2, 1, 0] = true := by decide +kernel
theorem subd7_14_688 : subd7_14 [2, 1, 1] = true := by decide +kernel
theorem subd7_14_689 : subd7_14 [2, 1, 2] = true := by decide +kernel
theorem subd7_14_690 : subd7_14 [2, 1, 3] = true := by decide +kernel
theorem subd7_14_691 : subd7_14 [2, 1, 4] = true := by decide +kernel
theorem subd7_14_692 : subd7_14 [2, 1, 5] = true := by decide +kernel
theorem subd7_14_693 : subd7_14 [2, 1, 6] = true := by decide +kernel
theorem subd7_14_694 : subd7_14 [2, 1, 7] = true := by decide +kernel
theorem subd7_14_695 : subd7_14 [2, 1, 8] = true := by decide +kernel
theorem subd7_14_696 : subd7_14 [2, 1, 9] = true := by decide +kernel
theorem subd7_14_697 : subd7_14 [2, 2, -9] = true := by decide +kernel
theorem subd7_14_698 : subd7_14 [2, 2, -8] = true := by decide +kernel
theorem subd7_14_699 : subd7_14 [2, 2, -7] = true := by decide +kernel
theorem subd7_14_700 : subd7_14 [2, 2, -6] = true := by decide +kernel
theorem subd7_14_701 : subd7_14 [2, 2, -5] = true := by decide +kernel
theorem subd7_14_702 : subd7_14 [2, 2, -4] = true := by decide +kernel
theorem subd7_14_703 : subd7_14 [2, 2, -3] = true := by decide +kernel
theorem sbd7_14_21 : ∀ q ∈ blkd7_14_21, subd7_14 q = true := by
  unfold blkd7_14_21
  exact List.forall_mem_cons.2 ⟨subd7_14_672, List.forall_mem_cons.2 ⟨subd7_14_673, List.forall_mem_cons.2 ⟨subd7_14_674, List.forall_mem_cons.2 ⟨subd7_14_675, List.forall_mem_cons.2 ⟨subd7_14_676, List.forall_mem_cons.2 ⟨subd7_14_677, List.forall_mem_cons.2 ⟨subd7_14_678, List.forall_mem_cons.2 ⟨subd7_14_679, List.forall_mem_cons.2 ⟨subd7_14_680, List.forall_mem_cons.2 ⟨subd7_14_681, List.forall_mem_cons.2 ⟨subd7_14_682, List.forall_mem_cons.2 ⟨subd7_14_683, List.forall_mem_cons.2 ⟨subd7_14_684, List.forall_mem_cons.2 ⟨subd7_14_685, List.forall_mem_cons.2 ⟨subd7_14_686, List.forall_mem_cons.2 ⟨subd7_14_687, List.forall_mem_cons.2 ⟨subd7_14_688, List.forall_mem_cons.2 ⟨subd7_14_689, List.forall_mem_cons.2 ⟨subd7_14_690, List.forall_mem_cons.2 ⟨subd7_14_691, List.forall_mem_cons.2 ⟨subd7_14_692, List.forall_mem_cons.2 ⟨subd7_14_693, List.forall_mem_cons.2 ⟨subd7_14_694, List.forall_mem_cons.2 ⟨subd7_14_695, List.forall_mem_cons.2 ⟨subd7_14_696, List.forall_mem_cons.2 ⟨subd7_14_697, List.forall_mem_cons.2 ⟨subd7_14_698, List.forall_mem_cons.2 ⟨subd7_14_699, List.forall_mem_cons.2 ⟨subd7_14_700, List.forall_mem_cons.2 ⟨subd7_14_701, List.forall_mem_cons.2 ⟨subd7_14_702, List.forall_mem_cons.2 ⟨subd7_14_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_14_704 : subd7_14 [2, 2, -2] = true := by decide +kernel
theorem subd7_14_705 : subd7_14 [2, 2, -1] = true := by decide +kernel
theorem subd7_14_706 : subd7_14 [2, 2, 0] = true := by decide +kernel
theorem subd7_14_707 : subd7_14 [2, 2, 1] = true := by decide +kernel
theorem subd7_14_708 : subd7_14 [2, 2, 2] = true := by decide +kernel
theorem subd7_14_709 : subd7_14 [2, 2, 3] = true := by decide +kernel
theorem subd7_14_710 : subd7_14 [2, 2, 4] = true := by decide +kernel
theorem subd7_14_711 : subd7_14 [2, 2, 5] = true := by decide +kernel
theorem subd7_14_712 : subd7_14 [2, 2, 6] = true := by decide +kernel
theorem subd7_14_713 : subd7_14 [2, 2, 7] = true := by decide +kernel
theorem subd7_14_714 : subd7_14 [2, 2, 8] = true := by decide +kernel
theorem subd7_14_715 : subd7_14 [2, 3, -8] = true := by decide +kernel
theorem subd7_14_716 : subd7_14 [2, 3, -7] = true := by decide +kernel
theorem subd7_14_717 : subd7_14 [2, 3, -6] = true := by decide +kernel
theorem subd7_14_718 : subd7_14 [2, 3, -5] = true := by decide +kernel
theorem subd7_14_719 : subd7_14 [2, 3, -4] = true := by decide +kernel
theorem subd7_14_720 : subd7_14 [2, 3, -3] = true := by decide +kernel
theorem subd7_14_721 : subd7_14 [2, 3, -2] = true := by decide +kernel
theorem subd7_14_722 : subd7_14 [2, 3, -1] = true := by decide +kernel
theorem subd7_14_723 : subd7_14 [2, 3, 0] = true := by decide +kernel
theorem subd7_14_724 : subd7_14 [2, 3, 1] = true := by decide +kernel
theorem subd7_14_725 : subd7_14 [2, 3, 2] = true := by decide +kernel
theorem subd7_14_726 : subd7_14 [2, 3, 3] = true := by decide +kernel
theorem subd7_14_727 : subd7_14 [2, 3, 4] = true := by decide +kernel
theorem subd7_14_728 : subd7_14 [2, 3, 5] = true := by decide +kernel
theorem subd7_14_729 : subd7_14 [2, 3, 6] = true := by decide +kernel
theorem subd7_14_730 : subd7_14 [2, 4] = true := by decide +kernel
theorem subd7_14_731 : subd7_14 [3, -4] = true := by decide +kernel
theorem subd7_14_732 : subd7_14 [3, -3] = true := by decide +kernel
theorem subd7_14_733 : subd7_14 [3, -2] = true := by decide +kernel
theorem subd7_14_734 : subd7_14 [3, -1, -7] = true := by decide +kernel
theorem subd7_14_735 : subd7_14 [3, -1, -6] = true := by decide +kernel
theorem sbd7_14_22 : ∀ q ∈ blkd7_14_22, subd7_14 q = true := by
  unfold blkd7_14_22
  exact List.forall_mem_cons.2 ⟨subd7_14_704, List.forall_mem_cons.2 ⟨subd7_14_705, List.forall_mem_cons.2 ⟨subd7_14_706, List.forall_mem_cons.2 ⟨subd7_14_707, List.forall_mem_cons.2 ⟨subd7_14_708, List.forall_mem_cons.2 ⟨subd7_14_709, List.forall_mem_cons.2 ⟨subd7_14_710, List.forall_mem_cons.2 ⟨subd7_14_711, List.forall_mem_cons.2 ⟨subd7_14_712, List.forall_mem_cons.2 ⟨subd7_14_713, List.forall_mem_cons.2 ⟨subd7_14_714, List.forall_mem_cons.2 ⟨subd7_14_715, List.forall_mem_cons.2 ⟨subd7_14_716, List.forall_mem_cons.2 ⟨subd7_14_717, List.forall_mem_cons.2 ⟨subd7_14_718, List.forall_mem_cons.2 ⟨subd7_14_719, List.forall_mem_cons.2 ⟨subd7_14_720, List.forall_mem_cons.2 ⟨subd7_14_721, List.forall_mem_cons.2 ⟨subd7_14_722, List.forall_mem_cons.2 ⟨subd7_14_723, List.forall_mem_cons.2 ⟨subd7_14_724, List.forall_mem_cons.2 ⟨subd7_14_725, List.forall_mem_cons.2 ⟨subd7_14_726, List.forall_mem_cons.2 ⟨subd7_14_727, List.forall_mem_cons.2 ⟨subd7_14_728, List.forall_mem_cons.2 ⟨subd7_14_729, List.forall_mem_cons.2 ⟨subd7_14_730, List.forall_mem_cons.2 ⟨subd7_14_731, List.forall_mem_cons.2 ⟨subd7_14_732, List.forall_mem_cons.2 ⟨subd7_14_733, List.forall_mem_cons.2 ⟨subd7_14_734, List.forall_mem_cons.2 ⟨subd7_14_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_14_736 : subd7_14 [3, -1, -5] = true := by decide +kernel
theorem subd7_14_737 : subd7_14 [3, -1, -4] = true := by decide +kernel
theorem subd7_14_738 : subd7_14 [3, -1, -3] = true := by decide +kernel
theorem subd7_14_739 : subd7_14 [3, -1, -2] = true := by decide +kernel
theorem subd7_14_740 : subd7_14 [3, -1, -1] = true := by decide +kernel
theorem subd7_14_741 : subd7_14 [3, -1, 0] = true := by decide +kernel
theorem subd7_14_742 : subd7_14 [3, -1, 1] = true := by decide +kernel
theorem subd7_14_743 : subd7_14 [3, -1, 2] = true := by decide +kernel
theorem subd7_14_744 : subd7_14 [3, -1, 3] = true := by decide +kernel
theorem subd7_14_745 : subd7_14 [3, -1, 4] = true := by decide +kernel
theorem subd7_14_746 : subd7_14 [3, -1, 5] = true := by decide +kernel
theorem subd7_14_747 : subd7_14 [3, -1, 6] = true := by decide +kernel
theorem subd7_14_748 : subd7_14 [3, -1, 7] = true := by decide +kernel
theorem subd7_14_749 : subd7_14 [3, -1, 8] = true := by decide +kernel
theorem subd7_14_750 : subd7_14 [3, 0, -8] = true := by decide +kernel
theorem subd7_14_751 : subd7_14 [3, 0, -7] = true := by decide +kernel
theorem subd7_14_752 : subd7_14 [3, 0, -6] = true := by decide +kernel
theorem subd7_14_753 : subd7_14 [3, 0, -5] = true := by decide +kernel
theorem subd7_14_754 : subd7_14 [3, 0, -4] = true := by decide +kernel
theorem subd7_14_755 : subd7_14 [3, 0, -3] = true := by decide +kernel
theorem subd7_14_756 : subd7_14 [3, 0, -2] = true := by decide +kernel
theorem subd7_14_757 : subd7_14 [3, 0, -1] = true := by decide +kernel
theorem subd7_14_758 : subd7_14 [3, 0, 0] = true := by decide +kernel
theorem subd7_14_759 : subd7_14 [3, 0, 1] = true := by decide +kernel
theorem subd7_14_760 : subd7_14 [3, 0, 2] = true := by decide +kernel
theorem subd7_14_761 : subd7_14 [3, 0, 3] = true := by decide +kernel
theorem subd7_14_762 : subd7_14 [3, 0, 4] = true := by decide +kernel
theorem subd7_14_763 : subd7_14 [3, 0, 5] = true := by decide +kernel
theorem subd7_14_764 : subd7_14 [3, 0, 6] = true := by decide +kernel
theorem subd7_14_765 : subd7_14 [3, 0, 7] = true := by decide +kernel
theorem subd7_14_766 : subd7_14 [3, 0, 8] = true := by decide +kernel
theorem subd7_14_767 : subd7_14 [3, 1, -8] = true := by decide +kernel
theorem sbd7_14_23 : ∀ q ∈ blkd7_14_23, subd7_14 q = true := by
  unfold blkd7_14_23
  exact List.forall_mem_cons.2 ⟨subd7_14_736, List.forall_mem_cons.2 ⟨subd7_14_737, List.forall_mem_cons.2 ⟨subd7_14_738, List.forall_mem_cons.2 ⟨subd7_14_739, List.forall_mem_cons.2 ⟨subd7_14_740, List.forall_mem_cons.2 ⟨subd7_14_741, List.forall_mem_cons.2 ⟨subd7_14_742, List.forall_mem_cons.2 ⟨subd7_14_743, List.forall_mem_cons.2 ⟨subd7_14_744, List.forall_mem_cons.2 ⟨subd7_14_745, List.forall_mem_cons.2 ⟨subd7_14_746, List.forall_mem_cons.2 ⟨subd7_14_747, List.forall_mem_cons.2 ⟨subd7_14_748, List.forall_mem_cons.2 ⟨subd7_14_749, List.forall_mem_cons.2 ⟨subd7_14_750, List.forall_mem_cons.2 ⟨subd7_14_751, List.forall_mem_cons.2 ⟨subd7_14_752, List.forall_mem_cons.2 ⟨subd7_14_753, List.forall_mem_cons.2 ⟨subd7_14_754, List.forall_mem_cons.2 ⟨subd7_14_755, List.forall_mem_cons.2 ⟨subd7_14_756, List.forall_mem_cons.2 ⟨subd7_14_757, List.forall_mem_cons.2 ⟨subd7_14_758, List.forall_mem_cons.2 ⟨subd7_14_759, List.forall_mem_cons.2 ⟨subd7_14_760, List.forall_mem_cons.2 ⟨subd7_14_761, List.forall_mem_cons.2 ⟨subd7_14_762, List.forall_mem_cons.2 ⟨subd7_14_763, List.forall_mem_cons.2 ⟨subd7_14_764, List.forall_mem_cons.2 ⟨subd7_14_765, List.forall_mem_cons.2 ⟨subd7_14_766, List.forall_mem_cons.2 ⟨subd7_14_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_14_768 : subd7_14 [3, 1, -7] = true := by decide +kernel
theorem subd7_14_769 : subd7_14 [3, 1, -6] = true := by decide +kernel
theorem subd7_14_770 : subd7_14 [3, 1, -5] = true := by decide +kernel
theorem subd7_14_771 : subd7_14 [3, 1, -4] = true := by decide +kernel
theorem subd7_14_772 : subd7_14 [3, 1, -3] = true := by decide +kernel
theorem subd7_14_773 : subd7_14 [3, 1, -2] = true := by decide +kernel
theorem subd7_14_774 : subd7_14 [3, 1, -1] = true := by decide +kernel
theorem subd7_14_775 : subd7_14 [3, 1, 0] = true := by decide +kernel
theorem subd7_14_776 : subd7_14 [3, 1, 1] = true := by decide +kernel
theorem subd7_14_777 : subd7_14 [3, 1, 2] = true := by decide +kernel
theorem subd7_14_778 : subd7_14 [3, 1, 3] = true := by decide +kernel
theorem subd7_14_779 : subd7_14 [3, 1, 4] = true := by decide +kernel
theorem subd7_14_780 : subd7_14 [3, 1, 5] = true := by decide +kernel
theorem subd7_14_781 : subd7_14 [3, 1, 6] = true := by decide +kernel
theorem subd7_14_782 : subd7_14 [3, 1, 7] = true := by decide +kernel
theorem subd7_14_783 : subd7_14 [3, 1, 8] = true := by decide +kernel
theorem subd7_14_784 : subd7_14 [3, 2, -7] = true := by decide +kernel
theorem subd7_14_785 : subd7_14 [3, 2, -6] = true := by decide +kernel
theorem subd7_14_786 : subd7_14 [3, 2, -5] = true := by decide +kernel
theorem subd7_14_787 : subd7_14 [3, 2, -4] = true := by decide +kernel
theorem subd7_14_788 : subd7_14 [3, 2, -3] = true := by decide +kernel
theorem subd7_14_789 : subd7_14 [3, 2, -2] = true := by decide +kernel
theorem subd7_14_790 : subd7_14 [3, 2, -1] = true := by decide +kernel
theorem subd7_14_791 : subd7_14 [3, 2, 0] = true := by decide +kernel
theorem subd7_14_792 : subd7_14 [3, 2, 1] = true := by decide +kernel
theorem subd7_14_793 : subd7_14 [3, 2, 2] = true := by decide +kernel
theorem subd7_14_794 : subd7_14 [3, 2, 3] = true := by decide +kernel
theorem subd7_14_795 : subd7_14 [3, 2, 4] = true := by decide +kernel
theorem subd7_14_796 : subd7_14 [3, 2, 5] = true := by decide +kernel
theorem subd7_14_797 : subd7_14 [3, 2, 6] = true := by decide +kernel
theorem subd7_14_798 : subd7_14 [3, 2, 7] = true := by decide +kernel
theorem subd7_14_799 : subd7_14 [3, 3] = true := by decide +kernel
theorem sbd7_14_24 : ∀ q ∈ blkd7_14_24, subd7_14 q = true := by
  unfold blkd7_14_24
  exact List.forall_mem_cons.2 ⟨subd7_14_768, List.forall_mem_cons.2 ⟨subd7_14_769, List.forall_mem_cons.2 ⟨subd7_14_770, List.forall_mem_cons.2 ⟨subd7_14_771, List.forall_mem_cons.2 ⟨subd7_14_772, List.forall_mem_cons.2 ⟨subd7_14_773, List.forall_mem_cons.2 ⟨subd7_14_774, List.forall_mem_cons.2 ⟨subd7_14_775, List.forall_mem_cons.2 ⟨subd7_14_776, List.forall_mem_cons.2 ⟨subd7_14_777, List.forall_mem_cons.2 ⟨subd7_14_778, List.forall_mem_cons.2 ⟨subd7_14_779, List.forall_mem_cons.2 ⟨subd7_14_780, List.forall_mem_cons.2 ⟨subd7_14_781, List.forall_mem_cons.2 ⟨subd7_14_782, List.forall_mem_cons.2 ⟨subd7_14_783, List.forall_mem_cons.2 ⟨subd7_14_784, List.forall_mem_cons.2 ⟨subd7_14_785, List.forall_mem_cons.2 ⟨subd7_14_786, List.forall_mem_cons.2 ⟨subd7_14_787, List.forall_mem_cons.2 ⟨subd7_14_788, List.forall_mem_cons.2 ⟨subd7_14_789, List.forall_mem_cons.2 ⟨subd7_14_790, List.forall_mem_cons.2 ⟨subd7_14_791, List.forall_mem_cons.2 ⟨subd7_14_792, List.forall_mem_cons.2 ⟨subd7_14_793, List.forall_mem_cons.2 ⟨subd7_14_794, List.forall_mem_cons.2 ⟨subd7_14_795, List.forall_mem_cons.2 ⟨subd7_14_796, List.forall_mem_cons.2 ⟨subd7_14_797, List.forall_mem_cons.2 ⟨subd7_14_798, List.forall_mem_cons.2 ⟨subd7_14_799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_14_800 : subd7_14 [4, -2] = true := by decide +kernel
theorem subd7_14_801 : subd7_14 [4, -1] = true := by decide +kernel
theorem subd7_14_802 : subd7_14 [4, 0] = true := by decide +kernel
theorem subd7_14_803 : subd7_14 [4, 1] = true := by decide +kernel
theorem subd7_14_804 : subd7_14 [4, 2] = true := by decide +kernel
theorem sbd7_14_25 : ∀ q ∈ blkd7_14_25, subd7_14 q = true := by
  unfold blkd7_14_25
  exact List.forall_mem_cons.2 ⟨subd7_14_800, List.forall_mem_cons.2 ⟨subd7_14_801, List.forall_mem_cons.2 ⟨subd7_14_802, List.forall_mem_cons.2 ⟨subd7_14_803, List.forall_mem_cons.2 ⟨subd7_14_804, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd8_0 : ldCheck G d8_0.U d8_0.ms ldd8_0 = true := by decide +kernel
theorem pre_okd8_0 : subPre G cell8 d8_0 = true := by decide +kernel
theorem subd8_0_0 : subd8_0 [-3] = true := by decide +kernel
theorem subd8_0_1 : subd8_0 [-2] = true := by decide +kernel
theorem subd8_0_2 : subd8_0 [-1] = true := by decide +kernel
theorem subd8_0_3 : subd8_0 [0, -4] = true := by decide +kernel
theorem subd8_0_4 : subd8_0 [0, -3] = true := by decide +kernel
theorem subd8_0_5 : subd8_0 [0, -2] = true := by decide +kernel
theorem subd8_0_6 : subd8_0 [0, -1] = true := by decide +kernel
theorem subd8_0_7 : subd8_0 [0, 0] = true := by decide +kernel
theorem subd8_0_8 : subd8_0 [0, 1] = true := by decide +kernel
theorem subd8_0_9 : subd8_0 [0, 2] = true := by decide +kernel
theorem subd8_0_10 : subd8_0 [0, 3] = true := by decide +kernel
theorem subd8_0_11 : subd8_0 [1] = true := by decide +kernel
theorem subd8_0_12 : subd8_0 [2] = true := by decide +kernel
theorem subd8_0_13 : subd8_0 [3] = true := by decide +kernel
theorem sbd8_0_0 : ∀ q ∈ blkd8_0_0, subd8_0 q = true := by
  unfold blkd8_0_0
  exact List.forall_mem_cons.2 ⟨subd8_0_0, List.forall_mem_cons.2 ⟨subd8_0_1, List.forall_mem_cons.2 ⟨subd8_0_2, List.forall_mem_cons.2 ⟨subd8_0_3, List.forall_mem_cons.2 ⟨subd8_0_4, List.forall_mem_cons.2 ⟨subd8_0_5, List.forall_mem_cons.2 ⟨subd8_0_6, List.forall_mem_cons.2 ⟨subd8_0_7, List.forall_mem_cons.2 ⟨subd8_0_8, List.forall_mem_cons.2 ⟨subd8_0_9, List.forall_mem_cons.2 ⟨subd8_0_10, List.forall_mem_cons.2 ⟨subd8_0_11, List.forall_mem_cons.2 ⟨subd8_0_12, List.forall_mem_cons.2 ⟨subd8_0_13, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_1 : ldCheck G d8_1.U d8_1.ms ldd8_1 = true := by decide +kernel
theorem pre_okd8_1 : subPre G cell8 d8_1 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C124
