import ReflectZphi.Data.Cert5.C142.Base

namespace ReflectZphi.Data.Cert5.C142

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_2_544 : subd9_2 [0, 3, 2] = true := by decide +kernel
theorem subd9_2_545 : subd9_2 [0, 3, 3] = true := by decide +kernel
theorem subd9_2_546 : subd9_2 [0, 3, 4] = true := by decide +kernel
theorem subd9_2_547 : subd9_2 [0, 3, 5] = true := by decide +kernel
theorem subd9_2_548 : subd9_2 [0, 3, 6] = true := by decide +kernel
theorem subd9_2_549 : subd9_2 [0, 3, 7] = true := by decide +kernel
theorem subd9_2_550 : subd9_2 [0, 3, 8] = true := by decide +kernel
theorem subd9_2_551 : subd9_2 [0, 4, -8] = true := by decide +kernel
theorem subd9_2_552 : subd9_2 [0, 4, -7] = true := by decide +kernel
theorem subd9_2_553 : subd9_2 [0, 4, -6] = true := by decide +kernel
theorem subd9_2_554 : subd9_2 [0, 4, -5] = true := by decide +kernel
theorem subd9_2_555 : subd9_2 [0, 4, -4] = true := by decide +kernel
theorem subd9_2_556 : subd9_2 [0, 4, -3] = true := by decide +kernel
theorem subd9_2_557 : subd9_2 [0, 4, -2] = true := by decide +kernel
theorem subd9_2_558 : subd9_2 [0, 4, -1] = true := by decide +kernel
theorem subd9_2_559 : subd9_2 [0, 4, 0] = true := by decide +kernel
theorem subd9_2_560 : subd9_2 [0, 4, 1] = true := by decide +kernel
theorem subd9_2_561 : subd9_2 [0, 4, 2] = true := by decide +kernel
theorem subd9_2_562 : subd9_2 [0, 4, 3] = true := by decide +kernel
theorem subd9_2_563 : subd9_2 [0, 4, 4] = true := by decide +kernel
theorem subd9_2_564 : subd9_2 [0, 4, 5] = true := by decide +kernel
theorem subd9_2_565 : subd9_2 [0, 4, 6] = true := by decide +kernel
theorem subd9_2_566 : subd9_2 [0, 5] = true := by decide +kernel
theorem subd9_2_567 : subd9_2 [1, -5] = true := by decide +kernel
theorem subd9_2_568 : subd9_2 [1, -4] = true := by decide +kernel
theorem subd9_2_569 : subd9_2 [1, -3, -8] = true := by decide +kernel
theorem subd9_2_570 : subd9_2 [1, -3, -7] = true := by decide +kernel
theorem subd9_2_571 : subd9_2 [1, -3, -6] = true := by decide +kernel
theorem subd9_2_572 : subd9_2 [1, -3, -5] = true := by decide +kernel
theorem subd9_2_573 : subd9_2 [1, -3, -4] = true := by decide +kernel
theorem subd9_2_574 : subd9_2 [1, -3, -3] = true := by decide +kernel
theorem subd9_2_575 : subd9_2 [1, -3, -2] = true := by decide +kernel
theorem sbd9_2_17 : ∀ q ∈ blkd9_2_17, subd9_2 q = true := by
  unfold blkd9_2_17
  exact List.forall_mem_cons.2 ⟨subd9_2_544, List.forall_mem_cons.2 ⟨subd9_2_545, List.forall_mem_cons.2 ⟨subd9_2_546, List.forall_mem_cons.2 ⟨subd9_2_547, List.forall_mem_cons.2 ⟨subd9_2_548, List.forall_mem_cons.2 ⟨subd9_2_549, List.forall_mem_cons.2 ⟨subd9_2_550, List.forall_mem_cons.2 ⟨subd9_2_551, List.forall_mem_cons.2 ⟨subd9_2_552, List.forall_mem_cons.2 ⟨subd9_2_553, List.forall_mem_cons.2 ⟨subd9_2_554, List.forall_mem_cons.2 ⟨subd9_2_555, List.forall_mem_cons.2 ⟨subd9_2_556, List.forall_mem_cons.2 ⟨subd9_2_557, List.forall_mem_cons.2 ⟨subd9_2_558, List.forall_mem_cons.2 ⟨subd9_2_559, List.forall_mem_cons.2 ⟨subd9_2_560, List.forall_mem_cons.2 ⟨subd9_2_561, List.forall_mem_cons.2 ⟨subd9_2_562, List.forall_mem_cons.2 ⟨subd9_2_563, List.forall_mem_cons.2 ⟨subd9_2_564, List.forall_mem_cons.2 ⟨subd9_2_565, List.forall_mem_cons.2 ⟨subd9_2_566, List.forall_mem_cons.2 ⟨subd9_2_567, List.forall_mem_cons.2 ⟨subd9_2_568, List.forall_mem_cons.2 ⟨subd9_2_569, List.forall_mem_cons.2 ⟨subd9_2_570, List.forall_mem_cons.2 ⟨subd9_2_571, List.forall_mem_cons.2 ⟨subd9_2_572, List.forall_mem_cons.2 ⟨subd9_2_573, List.forall_mem_cons.2 ⟨subd9_2_574, List.forall_mem_cons.2 ⟨subd9_2_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_576 : subd9_2 [1, -3, -1] = true := by decide +kernel
theorem subd9_2_577 : subd9_2 [1, -3, 0] = true := by decide +kernel
theorem subd9_2_578 : subd9_2 [1, -3, 1] = true := by decide +kernel
theorem subd9_2_579 : subd9_2 [1, -3, 2] = true := by decide +kernel
theorem subd9_2_580 : subd9_2 [1, -3, 3] = true := by decide +kernel
theorem subd9_2_581 : subd9_2 [1, -3, 4] = true := by decide +kernel
theorem subd9_2_582 : subd9_2 [1, -3, 5] = true := by decide +kernel
theorem subd9_2_583 : subd9_2 [1, -3, 6] = true := by decide +kernel
theorem subd9_2_584 : subd9_2 [1, -3, 7] = true := by decide +kernel
theorem subd9_2_585 : subd9_2 [1, -2, -10] = true := by decide +kernel
theorem subd9_2_586 : subd9_2 [1, -2, -9] = true := by decide +kernel
theorem subd9_2_587 : subd9_2 [1, -2, -8] = true := by decide +kernel
theorem subd9_2_588 : subd9_2 [1, -2, -7] = true := by decide +kernel
theorem subd9_2_589 : subd9_2 [1, -2, -6] = true := by decide +kernel
theorem subd9_2_590 : subd9_2 [1, -2, -5] = true := by decide +kernel
theorem subd9_2_591 : subd9_2 [1, -2, -4] = true := by decide +kernel
theorem subd9_2_592 : subd9_2 [1, -2, -3] = true := by decide +kernel
theorem subd9_2_593 : subd9_2 [1, -2, -2] = true := by decide +kernel
theorem subd9_2_594 : subd9_2 [1, -2, -1] = true := by decide +kernel
theorem subd9_2_595 : subd9_2 [1, -2, 0] = true := by decide +kernel
theorem subd9_2_596 : subd9_2 [1, -2, 1] = true := by decide +kernel
theorem subd9_2_597 : subd9_2 [1, -2, 2] = true := by decide +kernel
theorem subd9_2_598 : subd9_2 [1, -2, 3] = true := by decide +kernel
theorem subd9_2_599 : subd9_2 [1, -2, 4] = true := by decide +kernel
theorem subd9_2_600 : subd9_2 [1, -2, 5] = true := by decide +kernel
theorem subd9_2_601 : subd9_2 [1, -2, 6] = true := by decide +kernel
theorem subd9_2_602 : subd9_2 [1, -2, 7] = true := by decide +kernel
theorem subd9_2_603 : subd9_2 [1, -2, 8] = true := by decide +kernel
theorem subd9_2_604 : subd9_2 [1, -2, 9] = true := by decide +kernel
theorem subd9_2_605 : subd9_2 [1, -1, -11] = true := by decide +kernel
theorem subd9_2_606 : subd9_2 [1, -1, -10] = true := by decide +kernel
theorem subd9_2_607 : subd9_2 [1, -1, -9] = true := by decide +kernel
theorem sbd9_2_18 : ∀ q ∈ blkd9_2_18, subd9_2 q = true := by
  unfold blkd9_2_18
  exact List.forall_mem_cons.2 ⟨subd9_2_576, List.forall_mem_cons.2 ⟨subd9_2_577, List.forall_mem_cons.2 ⟨subd9_2_578, List.forall_mem_cons.2 ⟨subd9_2_579, List.forall_mem_cons.2 ⟨subd9_2_580, List.forall_mem_cons.2 ⟨subd9_2_581, List.forall_mem_cons.2 ⟨subd9_2_582, List.forall_mem_cons.2 ⟨subd9_2_583, List.forall_mem_cons.2 ⟨subd9_2_584, List.forall_mem_cons.2 ⟨subd9_2_585, List.forall_mem_cons.2 ⟨subd9_2_586, List.forall_mem_cons.2 ⟨subd9_2_587, List.forall_mem_cons.2 ⟨subd9_2_588, List.forall_mem_cons.2 ⟨subd9_2_589, List.forall_mem_cons.2 ⟨subd9_2_590, List.forall_mem_cons.2 ⟨subd9_2_591, List.forall_mem_cons.2 ⟨subd9_2_592, List.forall_mem_cons.2 ⟨subd9_2_593, List.forall_mem_cons.2 ⟨subd9_2_594, List.forall_mem_cons.2 ⟨subd9_2_595, List.forall_mem_cons.2 ⟨subd9_2_596, List.forall_mem_cons.2 ⟨subd9_2_597, List.forall_mem_cons.2 ⟨subd9_2_598, List.forall_mem_cons.2 ⟨subd9_2_599, List.forall_mem_cons.2 ⟨subd9_2_600, List.forall_mem_cons.2 ⟨subd9_2_601, List.forall_mem_cons.2 ⟨subd9_2_602, List.forall_mem_cons.2 ⟨subd9_2_603, List.forall_mem_cons.2 ⟨subd9_2_604, List.forall_mem_cons.2 ⟨subd9_2_605, List.forall_mem_cons.2 ⟨subd9_2_606, List.forall_mem_cons.2 ⟨subd9_2_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_608 : subd9_2 [1, -1, -8] = true := by decide +kernel
theorem subd9_2_609 : subd9_2 [1, -1, -7] = true := by decide +kernel
theorem subd9_2_610 : subd9_2 [1, -1, -6] = true := by decide +kernel
theorem subd9_2_611 : subd9_2 [1, -1, -5] = true := by decide +kernel
theorem subd9_2_612 : subd9_2 [1, -1, -4] = true := by decide +kernel
theorem subd9_2_613 : subd9_2 [1, -1, -3] = true := by decide +kernel
theorem subd9_2_614 : subd9_2 [1, -1, -2] = true := by decide +kernel
theorem subd9_2_615 : subd9_2 [1, -1, -1] = true := by decide +kernel
theorem subd9_2_616 : subd9_2 [1, -1, 0] = true := by decide +kernel
theorem subd9_2_617 : subd9_2 [1, -1, 1] = true := by decide +kernel
theorem subd9_2_618 : subd9_2 [1, -1, 2] = true := by decide +kernel
theorem subd9_2_619 : subd9_2 [1, -1, 3] = true := by decide +kernel
theorem subd9_2_620 : subd9_2 [1, -1, 4] = true := by decide +kernel
theorem subd9_2_621 : subd9_2 [1, -1, 5] = true := by decide +kernel
theorem subd9_2_622 : subd9_2 [1, -1, 6] = true := by decide +kernel
theorem subd9_2_623 : subd9_2 [1, -1, 7] = true := by decide +kernel
theorem subd9_2_624 : subd9_2 [1, -1, 8] = true := by decide +kernel
theorem subd9_2_625 : subd9_2 [1, -1, 9] = true := by decide +kernel
theorem subd9_2_626 : subd9_2 [1, 0, -11] = true := by decide +kernel
theorem subd9_2_627 : subd9_2 [1, 0, -10] = true := by decide +kernel
theorem subd9_2_628 : subd9_2 [1, 0, -9] = true := by decide +kernel
theorem subd9_2_629 : subd9_2 [1, 0, -8] = true := by decide +kernel
theorem subd9_2_630 : subd9_2 [1, 0, -7] = true := by decide +kernel
theorem subd9_2_631 : subd9_2 [1, 0, -6] = true := by decide +kernel
theorem subd9_2_632 : subd9_2 [1, 0, -5] = true := by decide +kernel
theorem subd9_2_633 : subd9_2 [1, 0, -4] = true := by decide +kernel
theorem subd9_2_634 : subd9_2 [1, 0, -3] = true := by decide +kernel
theorem subd9_2_635 : subd9_2 [1, 0, -2] = true := by decide +kernel
theorem subd9_2_636 : subd9_2 [1, 0, -1] = true := by decide +kernel
theorem subd9_2_637 : subd9_2 [1, 0, 0] = true := by decide +kernel
theorem subd9_2_638 : subd9_2 [1, 0, 1] = true := by decide +kernel
theorem subd9_2_639 : subd9_2 [1, 0, 2] = true := by decide +kernel
theorem sbd9_2_19 : ∀ q ∈ blkd9_2_19, subd9_2 q = true := by
  unfold blkd9_2_19
  exact List.forall_mem_cons.2 ⟨subd9_2_608, List.forall_mem_cons.2 ⟨subd9_2_609, List.forall_mem_cons.2 ⟨subd9_2_610, List.forall_mem_cons.2 ⟨subd9_2_611, List.forall_mem_cons.2 ⟨subd9_2_612, List.forall_mem_cons.2 ⟨subd9_2_613, List.forall_mem_cons.2 ⟨subd9_2_614, List.forall_mem_cons.2 ⟨subd9_2_615, List.forall_mem_cons.2 ⟨subd9_2_616, List.forall_mem_cons.2 ⟨subd9_2_617, List.forall_mem_cons.2 ⟨subd9_2_618, List.forall_mem_cons.2 ⟨subd9_2_619, List.forall_mem_cons.2 ⟨subd9_2_620, List.forall_mem_cons.2 ⟨subd9_2_621, List.forall_mem_cons.2 ⟨subd9_2_622, List.forall_mem_cons.2 ⟨subd9_2_623, List.forall_mem_cons.2 ⟨subd9_2_624, List.forall_mem_cons.2 ⟨subd9_2_625, List.forall_mem_cons.2 ⟨subd9_2_626, List.forall_mem_cons.2 ⟨subd9_2_627, List.forall_mem_cons.2 ⟨subd9_2_628, List.forall_mem_cons.2 ⟨subd9_2_629, List.forall_mem_cons.2 ⟨subd9_2_630, List.forall_mem_cons.2 ⟨subd9_2_631, List.forall_mem_cons.2 ⟨subd9_2_632, List.forall_mem_cons.2 ⟨subd9_2_633, List.forall_mem_cons.2 ⟨subd9_2_634, List.forall_mem_cons.2 ⟨subd9_2_635, List.forall_mem_cons.2 ⟨subd9_2_636, List.forall_mem_cons.2 ⟨subd9_2_637, List.forall_mem_cons.2 ⟨subd9_2_638, List.forall_mem_cons.2 ⟨subd9_2_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_640 : subd9_2 [1, 0, 3] = true := by decide +kernel
theorem subd9_2_641 : subd9_2 [1, 0, 4] = true := by decide +kernel
theorem subd9_2_642 : subd9_2 [1, 0, 5] = true := by decide +kernel
theorem subd9_2_643 : subd9_2 [1, 0, 6] = true := by decide +kernel
theorem subd9_2_644 : subd9_2 [1, 0, 7] = true := by decide +kernel
theorem subd9_2_645 : subd9_2 [1, 0, 8] = true := by decide +kernel
theorem subd9_2_646 : subd9_2 [1, 0, 9] = true := by decide +kernel
theorem subd9_2_647 : subd9_2 [1, 0, 10] = true := by decide +kernel
theorem subd9_2_648 : subd9_2 [1, 1, -11] = true := by decide +kernel
theorem subd9_2_649 : subd9_2 [1, 1, -10] = true := by decide +kernel
theorem subd9_2_650 : subd9_2 [1, 1, -9] = true := by decide +kernel
theorem subd9_2_651 : subd9_2 [1, 1, -8] = true := by decide +kernel
theorem subd9_2_652 : subd9_2 [1, 1, -7] = true := by decide +kernel
theorem subd9_2_653 : subd9_2 [1, 1, -6] = true := by decide +kernel
theorem subd9_2_654 : subd9_2 [1, 1, -5] = true := by decide +kernel
theorem subd9_2_655 : subd9_2 [1, 1, -4] = true := by decide +kernel
theorem subd9_2_656 : subd9_2 [1, 1, -3] = true := by decide +kernel
theorem subd9_2_657 : subd9_2 [1, 1, -2] = true := by decide +kernel
theorem subd9_2_658 : subd9_2 [1, 1, -1] = true := by decide +kernel
theorem subd9_2_659 : subd9_2 [1, 1, 0] = true := by decide +kernel
theorem subd9_2_660 : subd9_2 [1, 1, 1] = true := by decide +kernel
theorem subd9_2_661 : subd9_2 [1, 1, 2] = true := by decide +kernel
theorem subd9_2_662 : subd9_2 [1, 1, 3] = true := by decide +kernel
theorem subd9_2_663 : subd9_2 [1, 1, 4] = true := by decide +kernel
theorem subd9_2_664 : subd9_2 [1, 1, 5] = true := by decide +kernel
theorem subd9_2_665 : subd9_2 [1, 1, 6] = true := by decide +kernel
theorem subd9_2_666 : subd9_2 [1, 1, 7] = true := by decide +kernel
theorem subd9_2_667 : subd9_2 [1, 1, 8] = true := by decide +kernel
theorem subd9_2_668 : subd9_2 [1, 1, 9] = true := by decide +kernel
theorem subd9_2_669 : subd9_2 [1, 1, 10] = true := by decide +kernel
theorem subd9_2_670 : subd9_2 [1, 2, -11] = true := by decide +kernel
theorem subd9_2_671 : subd9_2 [1, 2, -10] = true := by decide +kernel
theorem sbd9_2_20 : ∀ q ∈ blkd9_2_20, subd9_2 q = true := by
  unfold blkd9_2_20
  exact List.forall_mem_cons.2 ⟨subd9_2_640, List.forall_mem_cons.2 ⟨subd9_2_641, List.forall_mem_cons.2 ⟨subd9_2_642, List.forall_mem_cons.2 ⟨subd9_2_643, List.forall_mem_cons.2 ⟨subd9_2_644, List.forall_mem_cons.2 ⟨subd9_2_645, List.forall_mem_cons.2 ⟨subd9_2_646, List.forall_mem_cons.2 ⟨subd9_2_647, List.forall_mem_cons.2 ⟨subd9_2_648, List.forall_mem_cons.2 ⟨subd9_2_649, List.forall_mem_cons.2 ⟨subd9_2_650, List.forall_mem_cons.2 ⟨subd9_2_651, List.forall_mem_cons.2 ⟨subd9_2_652, List.forall_mem_cons.2 ⟨subd9_2_653, List.forall_mem_cons.2 ⟨subd9_2_654, List.forall_mem_cons.2 ⟨subd9_2_655, List.forall_mem_cons.2 ⟨subd9_2_656, List.forall_mem_cons.2 ⟨subd9_2_657, List.forall_mem_cons.2 ⟨subd9_2_658, List.forall_mem_cons.2 ⟨subd9_2_659, List.forall_mem_cons.2 ⟨subd9_2_660, List.forall_mem_cons.2 ⟨subd9_2_661, List.forall_mem_cons.2 ⟨subd9_2_662, List.forall_mem_cons.2 ⟨subd9_2_663, List.forall_mem_cons.2 ⟨subd9_2_664, List.forall_mem_cons.2 ⟨subd9_2_665, List.forall_mem_cons.2 ⟨subd9_2_666, List.forall_mem_cons.2 ⟨subd9_2_667, List.forall_mem_cons.2 ⟨subd9_2_668, List.forall_mem_cons.2 ⟨subd9_2_669, List.forall_mem_cons.2 ⟨subd9_2_670, List.forall_mem_cons.2 ⟨subd9_2_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_672 : subd9_2 [1, 2, -9] = true := by decide +kernel
theorem subd9_2_673 : subd9_2 [1, 2, -8] = true := by decide +kernel
theorem subd9_2_674 : subd9_2 [1, 2, -7] = true := by decide +kernel
theorem subd9_2_675 : subd9_2 [1, 2, -6] = true := by decide +kernel
theorem subd9_2_676 : subd9_2 [1, 2, -5] = true := by decide +kernel
theorem subd9_2_677 : subd9_2 [1, 2, -4] = true := by decide +kernel
theorem subd9_2_678 : subd9_2 [1, 2, -3] = true := by decide +kernel
theorem subd9_2_679 : subd9_2 [1, 2, -2] = true := by decide +kernel
theorem subd9_2_680 : subd9_2 [1, 2, -1] = true := by decide +kernel
theorem subd9_2_681 : subd9_2 [1, 2, 0] = true := by decide +kernel
theorem subd9_2_682 : subd9_2 [1, 2, 1] = true := by decide +kernel
theorem subd9_2_683 : subd9_2 [1, 2, 2] = true := by decide +kernel
theorem subd9_2_684 : subd9_2 [1, 2, 3] = true := by decide +kernel
theorem subd9_2_685 : subd9_2 [1, 2, 4] = true := by decide +kernel
theorem subd9_2_686 : subd9_2 [1, 2, 5] = true := by decide +kernel
theorem subd9_2_687 : subd9_2 [1, 2, 6] = true := by decide +kernel
theorem subd9_2_688 : subd9_2 [1, 2, 7] = true := by decide +kernel
theorem subd9_2_689 : subd9_2 [1, 2, 8] = true := by decide +kernel
theorem subd9_2_690 : subd9_2 [1, 2, 9] = true := by decide +kernel
theorem subd9_2_691 : subd9_2 [1, 3, -10] = true := by decide +kernel
theorem subd9_2_692 : subd9_2 [1, 3, -9] = true := by decide +kernel
theorem subd9_2_693 : subd9_2 [1, 3, -8] = true := by decide +kernel
theorem subd9_2_694 : subd9_2 [1, 3, -7] = true := by decide +kernel
theorem subd9_2_695 : subd9_2 [1, 3, -6] = true := by decide +kernel
theorem subd9_2_696 : subd9_2 [1, 3, -5] = true := by decide +kernel
theorem subd9_2_697 : subd9_2 [1, 3, -4] = true := by decide +kernel
theorem subd9_2_698 : subd9_2 [1, 3, -3] = true := by decide +kernel
theorem subd9_2_699 : subd9_2 [1, 3, -2] = true := by decide +kernel
theorem subd9_2_700 : subd9_2 [1, 3, -1] = true := by decide +kernel
theorem subd9_2_701 : subd9_2 [1, 3, 0] = true := by decide +kernel
theorem subd9_2_702 : subd9_2 [1, 3, 1] = true := by decide +kernel
theorem subd9_2_703 : subd9_2 [1, 3, 2] = true := by decide +kernel
theorem sbd9_2_21 : ∀ q ∈ blkd9_2_21, subd9_2 q = true := by
  unfold blkd9_2_21
  exact List.forall_mem_cons.2 ⟨subd9_2_672, List.forall_mem_cons.2 ⟨subd9_2_673, List.forall_mem_cons.2 ⟨subd9_2_674, List.forall_mem_cons.2 ⟨subd9_2_675, List.forall_mem_cons.2 ⟨subd9_2_676, List.forall_mem_cons.2 ⟨subd9_2_677, List.forall_mem_cons.2 ⟨subd9_2_678, List.forall_mem_cons.2 ⟨subd9_2_679, List.forall_mem_cons.2 ⟨subd9_2_680, List.forall_mem_cons.2 ⟨subd9_2_681, List.forall_mem_cons.2 ⟨subd9_2_682, List.forall_mem_cons.2 ⟨subd9_2_683, List.forall_mem_cons.2 ⟨subd9_2_684, List.forall_mem_cons.2 ⟨subd9_2_685, List.forall_mem_cons.2 ⟨subd9_2_686, List.forall_mem_cons.2 ⟨subd9_2_687, List.forall_mem_cons.2 ⟨subd9_2_688, List.forall_mem_cons.2 ⟨subd9_2_689, List.forall_mem_cons.2 ⟨subd9_2_690, List.forall_mem_cons.2 ⟨subd9_2_691, List.forall_mem_cons.2 ⟨subd9_2_692, List.forall_mem_cons.2 ⟨subd9_2_693, List.forall_mem_cons.2 ⟨subd9_2_694, List.forall_mem_cons.2 ⟨subd9_2_695, List.forall_mem_cons.2 ⟨subd9_2_696, List.forall_mem_cons.2 ⟨subd9_2_697, List.forall_mem_cons.2 ⟨subd9_2_698, List.forall_mem_cons.2 ⟨subd9_2_699, List.forall_mem_cons.2 ⟨subd9_2_700, List.forall_mem_cons.2 ⟨subd9_2_701, List.forall_mem_cons.2 ⟨subd9_2_702, List.forall_mem_cons.2 ⟨subd9_2_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_704 : subd9_2 [1, 3, 3] = true := by decide +kernel
theorem subd9_2_705 : subd9_2 [1, 3, 4] = true := by decide +kernel
theorem subd9_2_706 : subd9_2 [1, 3, 5] = true := by decide +kernel
theorem subd9_2_707 : subd9_2 [1, 3, 6] = true := by decide +kernel
theorem subd9_2_708 : subd9_2 [1, 3, 7] = true := by decide +kernel
theorem subd9_2_709 : subd9_2 [1, 3, 8] = true := by decide +kernel
theorem subd9_2_710 : subd9_2 [1, 4, -9] = true := by decide +kernel
theorem subd9_2_711 : subd9_2 [1, 4, -8] = true := by decide +kernel
theorem subd9_2_712 : subd9_2 [1, 4, -7] = true := by decide +kernel
theorem subd9_2_713 : subd9_2 [1, 4, -6] = true := by decide +kernel
theorem subd9_2_714 : subd9_2 [1, 4, -5] = true := by decide +kernel
theorem subd9_2_715 : subd9_2 [1, 4, -4] = true := by decide +kernel
theorem subd9_2_716 : subd9_2 [1, 4, -3] = true := by decide +kernel
theorem subd9_2_717 : subd9_2 [1, 4, -2] = true := by decide +kernel
theorem subd9_2_718 : subd9_2 [1, 4, -1] = true := by decide +kernel
theorem subd9_2_719 : subd9_2 [1, 4, 0] = true := by decide +kernel
theorem subd9_2_720 : subd9_2 [1, 4, 1] = true := by decide +kernel
theorem subd9_2_721 : subd9_2 [1, 4, 2] = true := by decide +kernel
theorem subd9_2_722 : subd9_2 [1, 4, 3] = true := by decide +kernel
theorem subd9_2_723 : subd9_2 [1, 4, 4] = true := by decide +kernel
theorem subd9_2_724 : subd9_2 [1, 4, 5] = true := by decide +kernel
theorem subd9_2_725 : subd9_2 [1, 4, 6] = true := by decide +kernel
theorem subd9_2_726 : subd9_2 [1, 5] = true := by decide +kernel
theorem subd9_2_727 : subd9_2 [2, -4] = true := by decide +kernel
theorem subd9_2_728 : subd9_2 [2, -3] = true := by decide +kernel
theorem subd9_2_729 : subd9_2 [2, -2, -9] = true := by decide +kernel
theorem subd9_2_730 : subd9_2 [2, -2, -8] = true := by decide +kernel
theorem subd9_2_731 : subd9_2 [2, -2, -7] = true := by decide +kernel
theorem subd9_2_732 : subd9_2 [2, -2, -6] = true := by decide +kernel
theorem subd9_2_733 : subd9_2 [2, -2, -5] = true := by decide +kernel
theorem subd9_2_734 : subd9_2 [2, -2, -4] = true := by decide +kernel
theorem subd9_2_735 : subd9_2 [2, -2, -3] = true := by decide +kernel
theorem sbd9_2_22 : ∀ q ∈ blkd9_2_22, subd9_2 q = true := by
  unfold blkd9_2_22
  exact List.forall_mem_cons.2 ⟨subd9_2_704, List.forall_mem_cons.2 ⟨subd9_2_705, List.forall_mem_cons.2 ⟨subd9_2_706, List.forall_mem_cons.2 ⟨subd9_2_707, List.forall_mem_cons.2 ⟨subd9_2_708, List.forall_mem_cons.2 ⟨subd9_2_709, List.forall_mem_cons.2 ⟨subd9_2_710, List.forall_mem_cons.2 ⟨subd9_2_711, List.forall_mem_cons.2 ⟨subd9_2_712, List.forall_mem_cons.2 ⟨subd9_2_713, List.forall_mem_cons.2 ⟨subd9_2_714, List.forall_mem_cons.2 ⟨subd9_2_715, List.forall_mem_cons.2 ⟨subd9_2_716, List.forall_mem_cons.2 ⟨subd9_2_717, List.forall_mem_cons.2 ⟨subd9_2_718, List.forall_mem_cons.2 ⟨subd9_2_719, List.forall_mem_cons.2 ⟨subd9_2_720, List.forall_mem_cons.2 ⟨subd9_2_721, List.forall_mem_cons.2 ⟨subd9_2_722, List.forall_mem_cons.2 ⟨subd9_2_723, List.forall_mem_cons.2 ⟨subd9_2_724, List.forall_mem_cons.2 ⟨subd9_2_725, List.forall_mem_cons.2 ⟨subd9_2_726, List.forall_mem_cons.2 ⟨subd9_2_727, List.forall_mem_cons.2 ⟨subd9_2_728, List.forall_mem_cons.2 ⟨subd9_2_729, List.forall_mem_cons.2 ⟨subd9_2_730, List.forall_mem_cons.2 ⟨subd9_2_731, List.forall_mem_cons.2 ⟨subd9_2_732, List.forall_mem_cons.2 ⟨subd9_2_733, List.forall_mem_cons.2 ⟨subd9_2_734, List.forall_mem_cons.2 ⟨subd9_2_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_736 : subd9_2 [2, -2, -2] = true := by decide +kernel
theorem subd9_2_737 : subd9_2 [2, -2, -1] = true := by decide +kernel
theorem subd9_2_738 : subd9_2 [2, -2, 0] = true := by decide +kernel
theorem subd9_2_739 : subd9_2 [2, -2, 1] = true := by decide +kernel
theorem subd9_2_740 : subd9_2 [2, -2, 2] = true := by decide +kernel
theorem subd9_2_741 : subd9_2 [2, -2, 3] = true := by decide +kernel
theorem subd9_2_742 : subd9_2 [2, -2, 4] = true := by decide +kernel
theorem subd9_2_743 : subd9_2 [2, -2, 5] = true := by decide +kernel
theorem subd9_2_744 : subd9_2 [2, -2, 6] = true := by decide +kernel
theorem subd9_2_745 : subd9_2 [2, -2, 7] = true := by decide +kernel
theorem subd9_2_746 : subd9_2 [2, -1, -10] = true := by decide +kernel
theorem subd9_2_747 : subd9_2 [2, -1, -9] = true := by decide +kernel
theorem subd9_2_748 : subd9_2 [2, -1, -8] = true := by decide +kernel
theorem subd9_2_749 : subd9_2 [2, -1, -7] = true := by decide +kernel
theorem subd9_2_750 : subd9_2 [2, -1, -6] = true := by decide +kernel
theorem subd9_2_751 : subd9_2 [2, -1, -5] = true := by decide +kernel
theorem subd9_2_752 : subd9_2 [2, -1, -4] = true := by decide +kernel
theorem subd9_2_753 : subd9_2 [2, -1, -3] = true := by decide +kernel
theorem subd9_2_754 : subd9_2 [2, -1, -2] = true := by decide +kernel
theorem subd9_2_755 : subd9_2 [2, -1, -1] = true := by decide +kernel
theorem subd9_2_756 : subd9_2 [2, -1, 0] = true := by decide +kernel
theorem subd9_2_757 : subd9_2 [2, -1, 1] = true := by decide +kernel
theorem subd9_2_758 : subd9_2 [2, -1, 2] = true := by decide +kernel
theorem subd9_2_759 : subd9_2 [2, -1, 3] = true := by decide +kernel
theorem subd9_2_760 : subd9_2 [2, -1, 4] = true := by decide +kernel
theorem subd9_2_761 : subd9_2 [2, -1, 5] = true := by decide +kernel
theorem subd9_2_762 : subd9_2 [2, -1, 6] = true := by decide +kernel
theorem subd9_2_763 : subd9_2 [2, -1, 7] = true := by decide +kernel
theorem subd9_2_764 : subd9_2 [2, -1, 8] = true := by decide +kernel
theorem subd9_2_765 : subd9_2 [2, 0, -11] = true := by decide +kernel
theorem subd9_2_766 : subd9_2 [2, 0, -10] = true := by decide +kernel
theorem subd9_2_767 : subd9_2 [2, 0, -9] = true := by decide +kernel
theorem sbd9_2_23 : ∀ q ∈ blkd9_2_23, subd9_2 q = true := by
  unfold blkd9_2_23
  exact List.forall_mem_cons.2 ⟨subd9_2_736, List.forall_mem_cons.2 ⟨subd9_2_737, List.forall_mem_cons.2 ⟨subd9_2_738, List.forall_mem_cons.2 ⟨subd9_2_739, List.forall_mem_cons.2 ⟨subd9_2_740, List.forall_mem_cons.2 ⟨subd9_2_741, List.forall_mem_cons.2 ⟨subd9_2_742, List.forall_mem_cons.2 ⟨subd9_2_743, List.forall_mem_cons.2 ⟨subd9_2_744, List.forall_mem_cons.2 ⟨subd9_2_745, List.forall_mem_cons.2 ⟨subd9_2_746, List.forall_mem_cons.2 ⟨subd9_2_747, List.forall_mem_cons.2 ⟨subd9_2_748, List.forall_mem_cons.2 ⟨subd9_2_749, List.forall_mem_cons.2 ⟨subd9_2_750, List.forall_mem_cons.2 ⟨subd9_2_751, List.forall_mem_cons.2 ⟨subd9_2_752, List.forall_mem_cons.2 ⟨subd9_2_753, List.forall_mem_cons.2 ⟨subd9_2_754, List.forall_mem_cons.2 ⟨subd9_2_755, List.forall_mem_cons.2 ⟨subd9_2_756, List.forall_mem_cons.2 ⟨subd9_2_757, List.forall_mem_cons.2 ⟨subd9_2_758, List.forall_mem_cons.2 ⟨subd9_2_759, List.forall_mem_cons.2 ⟨subd9_2_760, List.forall_mem_cons.2 ⟨subd9_2_761, List.forall_mem_cons.2 ⟨subd9_2_762, List.forall_mem_cons.2 ⟨subd9_2_763, List.forall_mem_cons.2 ⟨subd9_2_764, List.forall_mem_cons.2 ⟨subd9_2_765, List.forall_mem_cons.2 ⟨subd9_2_766, List.forall_mem_cons.2 ⟨subd9_2_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_768 : subd9_2 [2, 0, -8] = true := by decide +kernel
theorem subd9_2_769 : subd9_2 [2, 0, -7] = true := by decide +kernel
theorem subd9_2_770 : subd9_2 [2, 0, -6] = true := by decide +kernel
theorem subd9_2_771 : subd9_2 [2, 0, -5] = true := by decide +kernel
theorem subd9_2_772 : subd9_2 [2, 0, -4] = true := by decide +kernel
theorem subd9_2_773 : subd9_2 [2, 0, -3] = true := by decide +kernel
theorem subd9_2_774 : subd9_2 [2, 0, -2] = true := by decide +kernel
theorem subd9_2_775 : subd9_2 [2, 0, -1] = true := by decide +kernel
theorem subd9_2_776 : subd9_2 [2, 0, 0] = true := by decide +kernel
theorem subd9_2_777 : subd9_2 [2, 0, 1] = true := by decide +kernel
theorem subd9_2_778 : subd9_2 [2, 0, 2] = true := by decide +kernel
theorem subd9_2_779 : subd9_2 [2, 0, 3] = true := by decide +kernel
theorem subd9_2_780 : subd9_2 [2, 0, 4] = true := by decide +kernel
theorem subd9_2_781 : subd9_2 [2, 0, 5] = true := by decide +kernel
theorem subd9_2_782 : subd9_2 [2, 0, 6] = true := by decide +kernel
theorem subd9_2_783 : subd9_2 [2, 0, 7] = true := by decide +kernel
theorem subd9_2_784 : subd9_2 [2, 0, 8] = true := by decide +kernel
theorem subd9_2_785 : subd9_2 [2, 1, -11] = true := by decide +kernel
theorem subd9_2_786 : subd9_2 [2, 1, -10] = true := by decide +kernel
theorem subd9_2_787 : subd9_2 [2, 1, -9] = true := by decide +kernel
theorem subd9_2_788 : subd9_2 [2, 1, -8] = true := by decide +kernel
theorem subd9_2_789 : subd9_2 [2, 1, -7] = true := by decide +kernel
theorem subd9_2_790 : subd9_2 [2, 1, -6] = true := by decide +kernel
theorem subd9_2_791 : subd9_2 [2, 1, -5] = true := by decide +kernel
theorem subd9_2_792 : subd9_2 [2, 1, -4] = true := by decide +kernel
theorem subd9_2_793 : subd9_2 [2, 1, -3] = true := by decide +kernel
theorem subd9_2_794 : subd9_2 [2, 1, -2] = true := by decide +kernel
theorem subd9_2_795 : subd9_2 [2, 1, -1] = true := by decide +kernel
theorem subd9_2_796 : subd9_2 [2, 1, 0] = true := by decide +kernel
theorem subd9_2_797 : subd9_2 [2, 1, 1] = true := by decide +kernel
theorem subd9_2_798 : subd9_2 [2, 1, 2] = true := by decide +kernel
theorem subd9_2_799 : subd9_2 [2, 1, 3] = true := by decide +kernel
theorem sbd9_2_24 : ∀ q ∈ blkd9_2_24, subd9_2 q = true := by
  unfold blkd9_2_24
  exact List.forall_mem_cons.2 ⟨subd9_2_768, List.forall_mem_cons.2 ⟨subd9_2_769, List.forall_mem_cons.2 ⟨subd9_2_770, List.forall_mem_cons.2 ⟨subd9_2_771, List.forall_mem_cons.2 ⟨subd9_2_772, List.forall_mem_cons.2 ⟨subd9_2_773, List.forall_mem_cons.2 ⟨subd9_2_774, List.forall_mem_cons.2 ⟨subd9_2_775, List.forall_mem_cons.2 ⟨subd9_2_776, List.forall_mem_cons.2 ⟨subd9_2_777, List.forall_mem_cons.2 ⟨subd9_2_778, List.forall_mem_cons.2 ⟨subd9_2_779, List.forall_mem_cons.2 ⟨subd9_2_780, List.forall_mem_cons.2 ⟨subd9_2_781, List.forall_mem_cons.2 ⟨subd9_2_782, List.forall_mem_cons.2 ⟨subd9_2_783, List.forall_mem_cons.2 ⟨subd9_2_784, List.forall_mem_cons.2 ⟨subd9_2_785, List.forall_mem_cons.2 ⟨subd9_2_786, List.forall_mem_cons.2 ⟨subd9_2_787, List.forall_mem_cons.2 ⟨subd9_2_788, List.forall_mem_cons.2 ⟨subd9_2_789, List.forall_mem_cons.2 ⟨subd9_2_790, List.forall_mem_cons.2 ⟨subd9_2_791, List.forall_mem_cons.2 ⟨subd9_2_792, List.forall_mem_cons.2 ⟨subd9_2_793, List.forall_mem_cons.2 ⟨subd9_2_794, List.forall_mem_cons.2 ⟨subd9_2_795, List.forall_mem_cons.2 ⟨subd9_2_796, List.forall_mem_cons.2 ⟨subd9_2_797, List.forall_mem_cons.2 ⟨subd9_2_798, List.forall_mem_cons.2 ⟨subd9_2_799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_800 : subd9_2 [2, 1, 4] = true := by decide +kernel
theorem subd9_2_801 : subd9_2 [2, 1, 5] = true := by decide +kernel
theorem subd9_2_802 : subd9_2 [2, 1, 6] = true := by decide +kernel
theorem subd9_2_803 : subd9_2 [2, 1, 7] = true := by decide +kernel
theorem subd9_2_804 : subd9_2 [2, 1, 8] = true := by decide +kernel
theorem subd9_2_805 : subd9_2 [2, 1, 9] = true := by decide +kernel
theorem subd9_2_806 : subd9_2 [2, 2, -11] = true := by decide +kernel
theorem subd9_2_807 : subd9_2 [2, 2, -10] = true := by decide +kernel
theorem subd9_2_808 : subd9_2 [2, 2, -9] = true := by decide +kernel
theorem subd9_2_809 : subd9_2 [2, 2, -8] = true := by decide +kernel
theorem subd9_2_810 : subd9_2 [2, 2, -7] = true := by decide +kernel
theorem subd9_2_811 : subd9_2 [2, 2, -6] = true := by decide +kernel
theorem subd9_2_812 : subd9_2 [2, 2, -5] = true := by decide +kernel
theorem subd9_2_813 : subd9_2 [2, 2, -4] = true := by decide +kernel
theorem subd9_2_814 : subd9_2 [2, 2, -3] = true := by decide +kernel
theorem subd9_2_815 : subd9_2 [2, 2, -2] = true := by decide +kernel
theorem subd9_2_816 : subd9_2 [2, 2, -1] = true := by decide +kernel
theorem subd9_2_817 : subd9_2 [2, 2, 0] = true := by decide +kernel
theorem subd9_2_818 : subd9_2 [2, 2, 1] = true := by decide +kernel
theorem subd9_2_819 : subd9_2 [2, 2, 2] = true := by decide +kernel
theorem subd9_2_820 : subd9_2 [2, 2, 3] = true := by decide +kernel
theorem subd9_2_821 : subd9_2 [2, 2, 4] = true := by decide +kernel
theorem subd9_2_822 : subd9_2 [2, 2, 5] = true := by decide +kernel
theorem subd9_2_823 : subd9_2 [2, 2, 6] = true := by decide +kernel
theorem subd9_2_824 : subd9_2 [2, 2, 7] = true := by decide +kernel
theorem subd9_2_825 : subd9_2 [2, 2, 8] = true := by decide +kernel
theorem subd9_2_826 : subd9_2 [2, 3, -10] = true := by decide +kernel
theorem subd9_2_827 : subd9_2 [2, 3, -9] = true := by decide +kernel
theorem subd9_2_828 : subd9_2 [2, 3, -8] = true := by decide +kernel
theorem subd9_2_829 : subd9_2 [2, 3, -7] = true := by decide +kernel
theorem subd9_2_830 : subd9_2 [2, 3, -6] = true := by decide +kernel
theorem subd9_2_831 : subd9_2 [2, 3, -5] = true := by decide +kernel
theorem sbd9_2_25 : ∀ q ∈ blkd9_2_25, subd9_2 q = true := by
  unfold blkd9_2_25
  exact List.forall_mem_cons.2 ⟨subd9_2_800, List.forall_mem_cons.2 ⟨subd9_2_801, List.forall_mem_cons.2 ⟨subd9_2_802, List.forall_mem_cons.2 ⟨subd9_2_803, List.forall_mem_cons.2 ⟨subd9_2_804, List.forall_mem_cons.2 ⟨subd9_2_805, List.forall_mem_cons.2 ⟨subd9_2_806, List.forall_mem_cons.2 ⟨subd9_2_807, List.forall_mem_cons.2 ⟨subd9_2_808, List.forall_mem_cons.2 ⟨subd9_2_809, List.forall_mem_cons.2 ⟨subd9_2_810, List.forall_mem_cons.2 ⟨subd9_2_811, List.forall_mem_cons.2 ⟨subd9_2_812, List.forall_mem_cons.2 ⟨subd9_2_813, List.forall_mem_cons.2 ⟨subd9_2_814, List.forall_mem_cons.2 ⟨subd9_2_815, List.forall_mem_cons.2 ⟨subd9_2_816, List.forall_mem_cons.2 ⟨subd9_2_817, List.forall_mem_cons.2 ⟨subd9_2_818, List.forall_mem_cons.2 ⟨subd9_2_819, List.forall_mem_cons.2 ⟨subd9_2_820, List.forall_mem_cons.2 ⟨subd9_2_821, List.forall_mem_cons.2 ⟨subd9_2_822, List.forall_mem_cons.2 ⟨subd9_2_823, List.forall_mem_cons.2 ⟨subd9_2_824, List.forall_mem_cons.2 ⟨subd9_2_825, List.forall_mem_cons.2 ⟨subd9_2_826, List.forall_mem_cons.2 ⟨subd9_2_827, List.forall_mem_cons.2 ⟨subd9_2_828, List.forall_mem_cons.2 ⟨subd9_2_829, List.forall_mem_cons.2 ⟨subd9_2_830, List.forall_mem_cons.2 ⟨subd9_2_831, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_832 : subd9_2 [2, 3, -4] = true := by decide +kernel
theorem subd9_2_833 : subd9_2 [2, 3, -3] = true := by decide +kernel
theorem subd9_2_834 : subd9_2 [2, 3, -2] = true := by decide +kernel
theorem subd9_2_835 : subd9_2 [2, 3, -1] = true := by decide +kernel
theorem subd9_2_836 : subd9_2 [2, 3, 0] = true := by decide +kernel
theorem subd9_2_837 : subd9_2 [2, 3, 1] = true := by decide +kernel
theorem subd9_2_838 : subd9_2 [2, 3, 2] = true := by decide +kernel
theorem subd9_2_839 : subd9_2 [2, 3, 3] = true := by decide +kernel
theorem subd9_2_840 : subd9_2 [2, 3, 4] = true := by decide +kernel
theorem subd9_2_841 : subd9_2 [2, 3, 5] = true := by decide +kernel
theorem subd9_2_842 : subd9_2 [2, 3, 6] = true := by decide +kernel
theorem subd9_2_843 : subd9_2 [2, 3, 7] = true := by decide +kernel
theorem subd9_2_844 : subd9_2 [2, 4, -9] = true := by decide +kernel
theorem subd9_2_845 : subd9_2 [2, 4, -8] = true := by decide +kernel
theorem subd9_2_846 : subd9_2 [2, 4, -7] = true := by decide +kernel
theorem subd9_2_847 : subd9_2 [2, 4, -6] = true := by decide +kernel
theorem subd9_2_848 : subd9_2 [2, 4, -5] = true := by decide +kernel
theorem subd9_2_849 : subd9_2 [2, 4, -4] = true := by decide +kernel
theorem subd9_2_850 : subd9_2 [2, 4, -3] = true := by decide +kernel
theorem subd9_2_851 : subd9_2 [2, 4, -2] = true := by decide +kernel
theorem subd9_2_852 : subd9_2 [2, 4, -1] = true := by decide +kernel
theorem subd9_2_853 : subd9_2 [2, 4, 0] = true := by decide +kernel
theorem subd9_2_854 : subd9_2 [2, 4, 1] = true := by decide +kernel
theorem subd9_2_855 : subd9_2 [2, 4, 2] = true := by decide +kernel
theorem subd9_2_856 : subd9_2 [2, 4, 3] = true := by decide +kernel
theorem subd9_2_857 : subd9_2 [2, 4, 4] = true := by decide +kernel
theorem subd9_2_858 : subd9_2 [2, 4, 5] = true := by decide +kernel
theorem subd9_2_859 : subd9_2 [2, 4, 6] = true := by decide +kernel
theorem subd9_2_860 : subd9_2 [2, 5] = true := by decide +kernel
theorem subd9_2_861 : subd9_2 [3, -3] = true := by decide +kernel
theorem subd9_2_862 : subd9_2 [3, -2] = true := by decide +kernel
theorem subd9_2_863 : subd9_2 [3, -1, -8] = true := by decide +kernel
theorem sbd9_2_26 : ∀ q ∈ blkd9_2_26, subd9_2 q = true := by
  unfold blkd9_2_26
  exact List.forall_mem_cons.2 ⟨subd9_2_832, List.forall_mem_cons.2 ⟨subd9_2_833, List.forall_mem_cons.2 ⟨subd9_2_834, List.forall_mem_cons.2 ⟨subd9_2_835, List.forall_mem_cons.2 ⟨subd9_2_836, List.forall_mem_cons.2 ⟨subd9_2_837, List.forall_mem_cons.2 ⟨subd9_2_838, List.forall_mem_cons.2 ⟨subd9_2_839, List.forall_mem_cons.2 ⟨subd9_2_840, List.forall_mem_cons.2 ⟨subd9_2_841, List.forall_mem_cons.2 ⟨subd9_2_842, List.forall_mem_cons.2 ⟨subd9_2_843, List.forall_mem_cons.2 ⟨subd9_2_844, List.forall_mem_cons.2 ⟨subd9_2_845, List.forall_mem_cons.2 ⟨subd9_2_846, List.forall_mem_cons.2 ⟨subd9_2_847, List.forall_mem_cons.2 ⟨subd9_2_848, List.forall_mem_cons.2 ⟨subd9_2_849, List.forall_mem_cons.2 ⟨subd9_2_850, List.forall_mem_cons.2 ⟨subd9_2_851, List.forall_mem_cons.2 ⟨subd9_2_852, List.forall_mem_cons.2 ⟨subd9_2_853, List.forall_mem_cons.2 ⟨subd9_2_854, List.forall_mem_cons.2 ⟨subd9_2_855, List.forall_mem_cons.2 ⟨subd9_2_856, List.forall_mem_cons.2 ⟨subd9_2_857, List.forall_mem_cons.2 ⟨subd9_2_858, List.forall_mem_cons.2 ⟨subd9_2_859, List.forall_mem_cons.2 ⟨subd9_2_860, List.forall_mem_cons.2 ⟨subd9_2_861, List.forall_mem_cons.2 ⟨subd9_2_862, List.forall_mem_cons.2 ⟨subd9_2_863, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_864 : subd9_2 [3, -1, -7] = true := by decide +kernel
theorem subd9_2_865 : subd9_2 [3, -1, -6] = true := by decide +kernel
theorem subd9_2_866 : subd9_2 [3, -1, -5] = true := by decide +kernel
theorem subd9_2_867 : subd9_2 [3, -1, -4] = true := by decide +kernel
theorem subd9_2_868 : subd9_2 [3, -1, -3] = true := by decide +kernel
theorem subd9_2_869 : subd9_2 [3, -1, -2] = true := by decide +kernel
theorem subd9_2_870 : subd9_2 [3, -1, -1] = true := by decide +kernel
theorem subd9_2_871 : subd9_2 [3, -1, 0] = true := by decide +kernel
theorem subd9_2_872 : subd9_2 [3, -1, 1] = true := by decide +kernel
theorem subd9_2_873 : subd9_2 [3, -1, 2] = true := by decide +kernel
theorem subd9_2_874 : subd9_2 [3, -1, 3] = true := by decide +kernel
theorem subd9_2_875 : subd9_2 [3, -1, 4] = true := by decide +kernel
theorem subd9_2_876 : subd9_2 [3, -1, 5] = true := by decide +kernel
theorem subd9_2_877 : subd9_2 [3, -1, 6] = true := by decide +kernel
theorem subd9_2_878 : subd9_2 [3, 0, -9] = true := by decide +kernel
theorem subd9_2_879 : subd9_2 [3, 0, -8] = true := by decide +kernel
theorem subd9_2_880 : subd9_2 [3, 0, -7] = true := by decide +kernel
theorem subd9_2_881 : subd9_2 [3, 0, -6] = true := by decide +kernel
theorem subd9_2_882 : subd9_2 [3, 0, -5] = true := by decide +kernel
theorem subd9_2_883 : subd9_2 [3, 0, -4] = true := by decide +kernel
theorem subd9_2_884 : subd9_2 [3, 0, -3] = true := by decide +kernel
theorem subd9_2_885 : subd9_2 [3, 0, -2] = true := by decide +kernel
theorem subd9_2_886 : subd9_2 [3, 0, -1] = true := by decide +kernel
theorem subd9_2_887 : subd9_2 [3, 0, 0] = true := by decide +kernel
theorem subd9_2_888 : subd9_2 [3, 0, 1] = true := by decide +kernel
theorem subd9_2_889 : subd9_2 [3, 0, 2] = true := by decide +kernel
theorem subd9_2_890 : subd9_2 [3, 0, 3] = true := by decide +kernel
theorem subd9_2_891 : subd9_2 [3, 0, 4] = true := by decide +kernel
theorem subd9_2_892 : subd9_2 [3, 0, 5] = true := by decide +kernel
theorem subd9_2_893 : subd9_2 [3, 0, 6] = true := by decide +kernel
theorem subd9_2_894 : subd9_2 [3, 1, -10] = true := by decide +kernel
theorem subd9_2_895 : subd9_2 [3, 1, -9] = true := by decide +kernel
theorem sbd9_2_27 : ∀ q ∈ blkd9_2_27, subd9_2 q = true := by
  unfold blkd9_2_27
  exact List.forall_mem_cons.2 ⟨subd9_2_864, List.forall_mem_cons.2 ⟨subd9_2_865, List.forall_mem_cons.2 ⟨subd9_2_866, List.forall_mem_cons.2 ⟨subd9_2_867, List.forall_mem_cons.2 ⟨subd9_2_868, List.forall_mem_cons.2 ⟨subd9_2_869, List.forall_mem_cons.2 ⟨subd9_2_870, List.forall_mem_cons.2 ⟨subd9_2_871, List.forall_mem_cons.2 ⟨subd9_2_872, List.forall_mem_cons.2 ⟨subd9_2_873, List.forall_mem_cons.2 ⟨subd9_2_874, List.forall_mem_cons.2 ⟨subd9_2_875, List.forall_mem_cons.2 ⟨subd9_2_876, List.forall_mem_cons.2 ⟨subd9_2_877, List.forall_mem_cons.2 ⟨subd9_2_878, List.forall_mem_cons.2 ⟨subd9_2_879, List.forall_mem_cons.2 ⟨subd9_2_880, List.forall_mem_cons.2 ⟨subd9_2_881, List.forall_mem_cons.2 ⟨subd9_2_882, List.forall_mem_cons.2 ⟨subd9_2_883, List.forall_mem_cons.2 ⟨subd9_2_884, List.forall_mem_cons.2 ⟨subd9_2_885, List.forall_mem_cons.2 ⟨subd9_2_886, List.forall_mem_cons.2 ⟨subd9_2_887, List.forall_mem_cons.2 ⟨subd9_2_888, List.forall_mem_cons.2 ⟨subd9_2_889, List.forall_mem_cons.2 ⟨subd9_2_890, List.forall_mem_cons.2 ⟨subd9_2_891, List.forall_mem_cons.2 ⟨subd9_2_892, List.forall_mem_cons.2 ⟨subd9_2_893, List.forall_mem_cons.2 ⟨subd9_2_894, List.forall_mem_cons.2 ⟨subd9_2_895, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_896 : subd9_2 [3, 1, -8] = true := by decide +kernel
theorem subd9_2_897 : subd9_2 [3, 1, -7] = true := by decide +kernel
theorem subd9_2_898 : subd9_2 [3, 1, -6] = true := by decide +kernel
theorem subd9_2_899 : subd9_2 [3, 1, -5] = true := by decide +kernel
theorem subd9_2_900 : subd9_2 [3, 1, -4] = true := by decide +kernel
theorem subd9_2_901 : subd9_2 [3, 1, -3] = true := by decide +kernel
theorem subd9_2_902 : subd9_2 [3, 1, -2] = true := by decide +kernel
theorem subd9_2_903 : subd9_2 [3, 1, -1] = true := by decide +kernel
theorem subd9_2_904 : subd9_2 [3, 1, 0] = true := by decide +kernel
theorem subd9_2_905 : subd9_2 [3, 1, 1] = true := by decide +kernel
theorem subd9_2_906 : subd9_2 [3, 1, 2] = true := by decide +kernel
theorem subd9_2_907 : subd9_2 [3, 1, 3] = true := by decide +kernel
theorem subd9_2_908 : subd9_2 [3, 1, 4] = true := by decide +kernel
theorem subd9_2_909 : subd9_2 [3, 1, 5] = true := by decide +kernel
theorem subd9_2_910 : subd9_2 [3, 1, 6] = true := by decide +kernel
theorem subd9_2_911 : subd9_2 [3, 1, 7] = true := by decide +kernel
theorem subd9_2_912 : subd9_2 [3, 2, -10] = true := by decide +kernel
theorem subd9_2_913 : subd9_2 [3, 2, -9] = true := by decide +kernel
theorem subd9_2_914 : subd9_2 [3, 2, -8] = true := by decide +kernel
theorem subd9_2_915 : subd9_2 [3, 2, -7] = true := by decide +kernel
theorem subd9_2_916 : subd9_2 [3, 2, -6] = true := by decide +kernel
theorem subd9_2_917 : subd9_2 [3, 2, -5] = true := by decide +kernel
theorem subd9_2_918 : subd9_2 [3, 2, -4] = true := by decide +kernel
theorem subd9_2_919 : subd9_2 [3, 2, -3] = true := by decide +kernel
theorem subd9_2_920 : subd9_2 [3, 2, -2] = true := by decide +kernel
theorem subd9_2_921 : subd9_2 [3, 2, -1] = true := by decide +kernel
theorem subd9_2_922 : subd9_2 [3, 2, 0] = true := by decide +kernel
theorem subd9_2_923 : subd9_2 [3, 2, 1] = true := by decide +kernel
theorem subd9_2_924 : subd9_2 [3, 2, 2] = true := by decide +kernel
theorem subd9_2_925 : subd9_2 [3, 2, 3] = true := by decide +kernel
theorem subd9_2_926 : subd9_2 [3, 2, 4] = true := by decide +kernel
theorem subd9_2_927 : subd9_2 [3, 2, 5] = true := by decide +kernel
theorem sbd9_2_28 : ∀ q ∈ blkd9_2_28, subd9_2 q = true := by
  unfold blkd9_2_28
  exact List.forall_mem_cons.2 ⟨subd9_2_896, List.forall_mem_cons.2 ⟨subd9_2_897, List.forall_mem_cons.2 ⟨subd9_2_898, List.forall_mem_cons.2 ⟨subd9_2_899, List.forall_mem_cons.2 ⟨subd9_2_900, List.forall_mem_cons.2 ⟨subd9_2_901, List.forall_mem_cons.2 ⟨subd9_2_902, List.forall_mem_cons.2 ⟨subd9_2_903, List.forall_mem_cons.2 ⟨subd9_2_904, List.forall_mem_cons.2 ⟨subd9_2_905, List.forall_mem_cons.2 ⟨subd9_2_906, List.forall_mem_cons.2 ⟨subd9_2_907, List.forall_mem_cons.2 ⟨subd9_2_908, List.forall_mem_cons.2 ⟨subd9_2_909, List.forall_mem_cons.2 ⟨subd9_2_910, List.forall_mem_cons.2 ⟨subd9_2_911, List.forall_mem_cons.2 ⟨subd9_2_912, List.forall_mem_cons.2 ⟨subd9_2_913, List.forall_mem_cons.2 ⟨subd9_2_914, List.forall_mem_cons.2 ⟨subd9_2_915, List.forall_mem_cons.2 ⟨subd9_2_916, List.forall_mem_cons.2 ⟨subd9_2_917, List.forall_mem_cons.2 ⟨subd9_2_918, List.forall_mem_cons.2 ⟨subd9_2_919, List.forall_mem_cons.2 ⟨subd9_2_920, List.forall_mem_cons.2 ⟨subd9_2_921, List.forall_mem_cons.2 ⟨subd9_2_922, List.forall_mem_cons.2 ⟨subd9_2_923, List.forall_mem_cons.2 ⟨subd9_2_924, List.forall_mem_cons.2 ⟨subd9_2_925, List.forall_mem_cons.2 ⟨subd9_2_926, List.forall_mem_cons.2 ⟨subd9_2_927, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_928 : subd9_2 [3, 2, 6] = true := by decide +kernel
theorem subd9_2_929 : subd9_2 [3, 2, 7] = true := by decide +kernel
theorem subd9_2_930 : subd9_2 [3, 3, -9] = true := by decide +kernel
theorem subd9_2_931 : subd9_2 [3, 3, -8] = true := by decide +kernel
theorem subd9_2_932 : subd9_2 [3, 3, -7] = true := by decide +kernel
theorem subd9_2_933 : subd9_2 [3, 3, -6] = true := by decide +kernel
theorem subd9_2_934 : subd9_2 [3, 3, -5] = true := by decide +kernel
theorem subd9_2_935 : subd9_2 [3, 3, -4] = true := by decide +kernel
theorem subd9_2_936 : subd9_2 [3, 3, -3] = true := by decide +kernel
theorem subd9_2_937 : subd9_2 [3, 3, -2] = true := by decide +kernel
theorem subd9_2_938 : subd9_2 [3, 3, -1] = true := by decide +kernel
theorem subd9_2_939 : subd9_2 [3, 3, 0] = true := by decide +kernel
theorem subd9_2_940 : subd9_2 [3, 3, 1] = true := by decide +kernel
theorem subd9_2_941 : subd9_2 [3, 3, 2] = true := by decide +kernel
theorem subd9_2_942 : subd9_2 [3, 3, 3] = true := by decide +kernel
theorem subd9_2_943 : subd9_2 [3, 3, 4] = true := by decide +kernel
theorem subd9_2_944 : subd9_2 [3, 3, 5] = true := by decide +kernel
theorem subd9_2_945 : subd9_2 [3, 3, 6] = true := by decide +kernel
theorem subd9_2_946 : subd9_2 [3, 4] = true := by decide +kernel
theorem subd9_2_947 : subd9_2 [3, 5] = true := by decide +kernel
theorem subd9_2_948 : subd9_2 [4, -2] = true := by decide +kernel
theorem subd9_2_949 : subd9_2 [4, -1] = true := by decide +kernel
theorem subd9_2_950 : subd9_2 [4, 0] = true := by decide +kernel
theorem subd9_2_951 : subd9_2 [4, 1] = true := by decide +kernel
theorem subd9_2_952 : subd9_2 [4, 2] = true := by decide +kernel
theorem subd9_2_953 : subd9_2 [4, 3] = true := by decide +kernel
theorem subd9_2_954 : subd9_2 [4, 4] = true := by decide +kernel
theorem sbd9_2_29 : ∀ q ∈ blkd9_2_29, subd9_2 q = true := by
  unfold blkd9_2_29
  exact List.forall_mem_cons.2 ⟨subd9_2_928, List.forall_mem_cons.2 ⟨subd9_2_929, List.forall_mem_cons.2 ⟨subd9_2_930, List.forall_mem_cons.2 ⟨subd9_2_931, List.forall_mem_cons.2 ⟨subd9_2_932, List.forall_mem_cons.2 ⟨subd9_2_933, List.forall_mem_cons.2 ⟨subd9_2_934, List.forall_mem_cons.2 ⟨subd9_2_935, List.forall_mem_cons.2 ⟨subd9_2_936, List.forall_mem_cons.2 ⟨subd9_2_937, List.forall_mem_cons.2 ⟨subd9_2_938, List.forall_mem_cons.2 ⟨subd9_2_939, List.forall_mem_cons.2 ⟨subd9_2_940, List.forall_mem_cons.2 ⟨subd9_2_941, List.forall_mem_cons.2 ⟨subd9_2_942, List.forall_mem_cons.2 ⟨subd9_2_943, List.forall_mem_cons.2 ⟨subd9_2_944, List.forall_mem_cons.2 ⟨subd9_2_945, List.forall_mem_cons.2 ⟨subd9_2_946, List.forall_mem_cons.2 ⟨subd9_2_947, List.forall_mem_cons.2 ⟨subd9_2_948, List.forall_mem_cons.2 ⟨subd9_2_949, List.forall_mem_cons.2 ⟨subd9_2_950, List.forall_mem_cons.2 ⟨subd9_2_951, List.forall_mem_cons.2 ⟨subd9_2_952, List.forall_mem_cons.2 ⟨subd9_2_953, List.forall_mem_cons.2 ⟨subd9_2_954, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C142
