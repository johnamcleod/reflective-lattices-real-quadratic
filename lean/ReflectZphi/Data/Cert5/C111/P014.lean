import ReflectZphi.Data.Cert5.C111.Base

namespace ReflectZphi.Data.Cert5.C111

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_3_576 : subd7_3 [1, 1, -8] = true := by decide +kernel
theorem subd7_3_577 : subd7_3 [1, 1, -7] = true := by decide +kernel
theorem subd7_3_578 : subd7_3 [1, 1, -6] = true := by decide +kernel
theorem subd7_3_579 : subd7_3 [1, 1, -5] = true := by decide +kernel
theorem subd7_3_580 : subd7_3 [1, 1, -4] = true := by decide +kernel
theorem subd7_3_581 : subd7_3 [1, 1, -3] = true := by decide +kernel
theorem subd7_3_582 : subd7_3 [1, 1, -2] = true := by decide +kernel
theorem subd7_3_583 : subd7_3 [1, 1, -1] = true := by decide +kernel
theorem subd7_3_584 : subd7_3 [1, 1, 0] = true := by decide +kernel
theorem subd7_3_585 : subd7_3 [1, 1, 1] = true := by decide +kernel
theorem subd7_3_586 : subd7_3 [1, 1, 2] = true := by decide +kernel
theorem subd7_3_587 : subd7_3 [1, 1, 3] = true := by decide +kernel
theorem subd7_3_588 : subd7_3 [1, 1, 4] = true := by decide +kernel
theorem subd7_3_589 : subd7_3 [1, 1, 5] = true := by decide +kernel
theorem subd7_3_590 : subd7_3 [1, 1, 6] = true := by decide +kernel
theorem subd7_3_591 : subd7_3 [1, 1, 7] = true := by decide +kernel
theorem subd7_3_592 : subd7_3 [1, 1, 8] = true := by decide +kernel
theorem subd7_3_593 : subd7_3 [1, 1, 9] = true := by decide +kernel
theorem subd7_3_594 : subd7_3 [1, 1, 10] = true := by decide +kernel
theorem subd7_3_595 : subd7_3 [1, 1, 11] = true := by decide +kernel
theorem subd7_3_596 : subd7_3 [1, 2, -10] = true := by decide +kernel
theorem subd7_3_597 : subd7_3 [1, 2, -9] = true := by decide +kernel
theorem subd7_3_598 : subd7_3 [1, 2, -8] = true := by decide +kernel
theorem subd7_3_599 : subd7_3 [1, 2, -7] = true := by decide +kernel
theorem subd7_3_600 : subd7_3 [1, 2, -6] = true := by decide +kernel
theorem subd7_3_601 : subd7_3 [1, 2, -5] = true := by decide +kernel
theorem subd7_3_602 : subd7_3 [1, 2, -4] = true := by decide +kernel
theorem subd7_3_603 : subd7_3 [1, 2, -3] = true := by decide +kernel
theorem subd7_3_604 : subd7_3 [1, 2, -2] = true := by decide +kernel
theorem subd7_3_605 : subd7_3 [1, 2, -1] = true := by decide +kernel
theorem subd7_3_606 : subd7_3 [1, 2, 0] = true := by decide +kernel
theorem subd7_3_607 : subd7_3 [1, 2, 1] = true := by decide +kernel
theorem sbd7_3_18 : ∀ q ∈ blkd7_3_18, subd7_3 q = true := by
  unfold blkd7_3_18
  exact List.forall_mem_cons.2 ⟨subd7_3_576, List.forall_mem_cons.2 ⟨subd7_3_577, List.forall_mem_cons.2 ⟨subd7_3_578, List.forall_mem_cons.2 ⟨subd7_3_579, List.forall_mem_cons.2 ⟨subd7_3_580, List.forall_mem_cons.2 ⟨subd7_3_581, List.forall_mem_cons.2 ⟨subd7_3_582, List.forall_mem_cons.2 ⟨subd7_3_583, List.forall_mem_cons.2 ⟨subd7_3_584, List.forall_mem_cons.2 ⟨subd7_3_585, List.forall_mem_cons.2 ⟨subd7_3_586, List.forall_mem_cons.2 ⟨subd7_3_587, List.forall_mem_cons.2 ⟨subd7_3_588, List.forall_mem_cons.2 ⟨subd7_3_589, List.forall_mem_cons.2 ⟨subd7_3_590, List.forall_mem_cons.2 ⟨subd7_3_591, List.forall_mem_cons.2 ⟨subd7_3_592, List.forall_mem_cons.2 ⟨subd7_3_593, List.forall_mem_cons.2 ⟨subd7_3_594, List.forall_mem_cons.2 ⟨subd7_3_595, List.forall_mem_cons.2 ⟨subd7_3_596, List.forall_mem_cons.2 ⟨subd7_3_597, List.forall_mem_cons.2 ⟨subd7_3_598, List.forall_mem_cons.2 ⟨subd7_3_599, List.forall_mem_cons.2 ⟨subd7_3_600, List.forall_mem_cons.2 ⟨subd7_3_601, List.forall_mem_cons.2 ⟨subd7_3_602, List.forall_mem_cons.2 ⟨subd7_3_603, List.forall_mem_cons.2 ⟨subd7_3_604, List.forall_mem_cons.2 ⟨subd7_3_605, List.forall_mem_cons.2 ⟨subd7_3_606, List.forall_mem_cons.2 ⟨subd7_3_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_608 : subd7_3 [1, 2, 2] = true := by decide +kernel
theorem subd7_3_609 : subd7_3 [1, 2, 3] = true := by decide +kernel
theorem subd7_3_610 : subd7_3 [1, 2, 4] = true := by decide +kernel
theorem subd7_3_611 : subd7_3 [1, 2, 5] = true := by decide +kernel
theorem subd7_3_612 : subd7_3 [1, 2, 6] = true := by decide +kernel
theorem subd7_3_613 : subd7_3 [1, 2, 7] = true := by decide +kernel
theorem subd7_3_614 : subd7_3 [1, 2, 8] = true := by decide +kernel
theorem subd7_3_615 : subd7_3 [1, 2, 9] = true := by decide +kernel
theorem subd7_3_616 : subd7_3 [1, 3, -7] = true := by decide +kernel
theorem subd7_3_617 : subd7_3 [1, 3, -6] = true := by decide +kernel
theorem subd7_3_618 : subd7_3 [1, 3, -5] = true := by decide +kernel
theorem subd7_3_619 : subd7_3 [1, 3, -4] = true := by decide +kernel
theorem subd7_3_620 : subd7_3 [1, 3, -3] = true := by decide +kernel
theorem subd7_3_621 : subd7_3 [1, 3, -2] = true := by decide +kernel
theorem subd7_3_622 : subd7_3 [1, 3, -1] = true := by decide +kernel
theorem subd7_3_623 : subd7_3 [1, 3, 0] = true := by decide +kernel
theorem subd7_3_624 : subd7_3 [1, 3, 1] = true := by decide +kernel
theorem subd7_3_625 : subd7_3 [1, 3, 2] = true := by decide +kernel
theorem subd7_3_626 : subd7_3 [1, 3, 3] = true := by decide +kernel
theorem subd7_3_627 : subd7_3 [1, 3, 4] = true := by decide +kernel
theorem subd7_3_628 : subd7_3 [1, 3, 5] = true := by decide +kernel
theorem subd7_3_629 : subd7_3 [2, -4] = true := by decide +kernel
theorem subd7_3_630 : subd7_3 [2, -3, -6] = true := by decide +kernel
theorem subd7_3_631 : subd7_3 [2, -3, -5] = true := by decide +kernel
theorem subd7_3_632 : subd7_3 [2, -3, -4] = true := by decide +kernel
theorem subd7_3_633 : subd7_3 [2, -3, -3] = true := by decide +kernel
theorem subd7_3_634 : subd7_3 [2, -3, -2] = true := by decide +kernel
theorem subd7_3_635 : subd7_3 [2, -3, -1] = true := by decide +kernel
theorem subd7_3_636 : subd7_3 [2, -3, 0] = true := by decide +kernel
theorem subd7_3_637 : subd7_3 [2, -3, 1] = true := by decide +kernel
theorem subd7_3_638 : subd7_3 [2, -3, 2] = true := by decide +kernel
theorem subd7_3_639 : subd7_3 [2, -3, 3] = true := by decide +kernel
theorem sbd7_3_19 : ∀ q ∈ blkd7_3_19, subd7_3 q = true := by
  unfold blkd7_3_19
  exact List.forall_mem_cons.2 ⟨subd7_3_608, List.forall_mem_cons.2 ⟨subd7_3_609, List.forall_mem_cons.2 ⟨subd7_3_610, List.forall_mem_cons.2 ⟨subd7_3_611, List.forall_mem_cons.2 ⟨subd7_3_612, List.forall_mem_cons.2 ⟨subd7_3_613, List.forall_mem_cons.2 ⟨subd7_3_614, List.forall_mem_cons.2 ⟨subd7_3_615, List.forall_mem_cons.2 ⟨subd7_3_616, List.forall_mem_cons.2 ⟨subd7_3_617, List.forall_mem_cons.2 ⟨subd7_3_618, List.forall_mem_cons.2 ⟨subd7_3_619, List.forall_mem_cons.2 ⟨subd7_3_620, List.forall_mem_cons.2 ⟨subd7_3_621, List.forall_mem_cons.2 ⟨subd7_3_622, List.forall_mem_cons.2 ⟨subd7_3_623, List.forall_mem_cons.2 ⟨subd7_3_624, List.forall_mem_cons.2 ⟨subd7_3_625, List.forall_mem_cons.2 ⟨subd7_3_626, List.forall_mem_cons.2 ⟨subd7_3_627, List.forall_mem_cons.2 ⟨subd7_3_628, List.forall_mem_cons.2 ⟨subd7_3_629, List.forall_mem_cons.2 ⟨subd7_3_630, List.forall_mem_cons.2 ⟨subd7_3_631, List.forall_mem_cons.2 ⟨subd7_3_632, List.forall_mem_cons.2 ⟨subd7_3_633, List.forall_mem_cons.2 ⟨subd7_3_634, List.forall_mem_cons.2 ⟨subd7_3_635, List.forall_mem_cons.2 ⟨subd7_3_636, List.forall_mem_cons.2 ⟨subd7_3_637, List.forall_mem_cons.2 ⟨subd7_3_638, List.forall_mem_cons.2 ⟨subd7_3_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_640 : subd7_3 [2, -3, 4] = true := by decide +kernel
theorem subd7_3_641 : subd7_3 [2, -3, 5] = true := by decide +kernel
theorem subd7_3_642 : subd7_3 [2, -3, 6] = true := by decide +kernel
theorem subd7_3_643 : subd7_3 [2, -3, 7] = true := by decide +kernel
theorem subd7_3_644 : subd7_3 [2, -3, 8] = true := by decide +kernel
theorem subd7_3_645 : subd7_3 [2, -2, -8] = true := by decide +kernel
theorem subd7_3_646 : subd7_3 [2, -2, -7] = true := by decide +kernel
theorem subd7_3_647 : subd7_3 [2, -2, -6] = true := by decide +kernel
theorem subd7_3_648 : subd7_3 [2, -2, -5] = true := by decide +kernel
theorem subd7_3_649 : subd7_3 [2, -2, -4] = true := by decide +kernel
theorem subd7_3_650 : subd7_3 [2, -2, -3] = true := by decide +kernel
theorem subd7_3_651 : subd7_3 [2, -2, -2] = true := by decide +kernel
theorem subd7_3_652 : subd7_3 [2, -2, -1] = true := by decide +kernel
theorem subd7_3_653 : subd7_3 [2, -2, 0] = true := by decide +kernel
theorem subd7_3_654 : subd7_3 [2, -2, 1] = true := by decide +kernel
theorem subd7_3_655 : subd7_3 [2, -2, 2] = true := by decide +kernel
theorem subd7_3_656 : subd7_3 [2, -2, 3] = true := by decide +kernel
theorem subd7_3_657 : subd7_3 [2, -2, 4] = true := by decide +kernel
theorem subd7_3_658 : subd7_3 [2, -2, 5] = true := by decide +kernel
theorem subd7_3_659 : subd7_3 [2, -2, 6] = true := by decide +kernel
theorem subd7_3_660 : subd7_3 [2, -2, 7] = true := by decide +kernel
theorem subd7_3_661 : subd7_3 [2, -2, 8] = true := by decide +kernel
theorem subd7_3_662 : subd7_3 [2, -2, 9] = true := by decide +kernel
theorem subd7_3_663 : subd7_3 [2, -2, 10] = true := by decide +kernel
theorem subd7_3_664 : subd7_3 [2, -1, -10] = true := by decide +kernel
theorem subd7_3_665 : subd7_3 [2, -1, -9] = true := by decide +kernel
theorem subd7_3_666 : subd7_3 [2, -1, -8] = true := by decide +kernel
theorem subd7_3_667 : subd7_3 [2, -1, -7] = true := by decide +kernel
theorem subd7_3_668 : subd7_3 [2, -1, -6] = true := by decide +kernel
theorem subd7_3_669 : subd7_3 [2, -1, -5] = true := by decide +kernel
theorem subd7_3_670 : subd7_3 [2, -1, -4] = true := by decide +kernel
theorem subd7_3_671 : subd7_3 [2, -1, -3] = true := by decide +kernel
theorem sbd7_3_20 : ∀ q ∈ blkd7_3_20, subd7_3 q = true := by
  unfold blkd7_3_20
  exact List.forall_mem_cons.2 ⟨subd7_3_640, List.forall_mem_cons.2 ⟨subd7_3_641, List.forall_mem_cons.2 ⟨subd7_3_642, List.forall_mem_cons.2 ⟨subd7_3_643, List.forall_mem_cons.2 ⟨subd7_3_644, List.forall_mem_cons.2 ⟨subd7_3_645, List.forall_mem_cons.2 ⟨subd7_3_646, List.forall_mem_cons.2 ⟨subd7_3_647, List.forall_mem_cons.2 ⟨subd7_3_648, List.forall_mem_cons.2 ⟨subd7_3_649, List.forall_mem_cons.2 ⟨subd7_3_650, List.forall_mem_cons.2 ⟨subd7_3_651, List.forall_mem_cons.2 ⟨subd7_3_652, List.forall_mem_cons.2 ⟨subd7_3_653, List.forall_mem_cons.2 ⟨subd7_3_654, List.forall_mem_cons.2 ⟨subd7_3_655, List.forall_mem_cons.2 ⟨subd7_3_656, List.forall_mem_cons.2 ⟨subd7_3_657, List.forall_mem_cons.2 ⟨subd7_3_658, List.forall_mem_cons.2 ⟨subd7_3_659, List.forall_mem_cons.2 ⟨subd7_3_660, List.forall_mem_cons.2 ⟨subd7_3_661, List.forall_mem_cons.2 ⟨subd7_3_662, List.forall_mem_cons.2 ⟨subd7_3_663, List.forall_mem_cons.2 ⟨subd7_3_664, List.forall_mem_cons.2 ⟨subd7_3_665, List.forall_mem_cons.2 ⟨subd7_3_666, List.forall_mem_cons.2 ⟨subd7_3_667, List.forall_mem_cons.2 ⟨subd7_3_668, List.forall_mem_cons.2 ⟨subd7_3_669, List.forall_mem_cons.2 ⟨subd7_3_670, List.forall_mem_cons.2 ⟨subd7_3_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_672 : subd7_3 [2, -1, -2] = true := by decide +kernel
theorem subd7_3_673 : subd7_3 [2, -1, -1] = true := by decide +kernel
theorem subd7_3_674 : subd7_3 [2, -1, 0] = true := by decide +kernel
theorem subd7_3_675 : subd7_3 [2, -1, 1] = true := by decide +kernel
theorem subd7_3_676 : subd7_3 [2, -1, 2] = true := by decide +kernel
theorem subd7_3_677 : subd7_3 [2, -1, 3] = true := by decide +kernel
theorem subd7_3_678 : subd7_3 [2, -1, 4] = true := by decide +kernel
theorem subd7_3_679 : subd7_3 [2, -1, 5] = true := by decide +kernel
theorem subd7_3_680 : subd7_3 [2, -1, 6] = true := by decide +kernel
theorem subd7_3_681 : subd7_3 [2, -1, 7] = true := by decide +kernel
theorem subd7_3_682 : subd7_3 [2, -1, 8] = true := by decide +kernel
theorem subd7_3_683 : subd7_3 [2, -1, 9] = true := by decide +kernel
theorem subd7_3_684 : subd7_3 [2, -1, 10] = true := by decide +kernel
theorem subd7_3_685 : subd7_3 [2, -1, 11] = true := by decide +kernel
theorem subd7_3_686 : subd7_3 [2, 0, -10] = true := by decide +kernel
theorem subd7_3_687 : subd7_3 [2, 0, -9] = true := by decide +kernel
theorem subd7_3_688 : subd7_3 [2, 0, -8] = true := by decide +kernel
theorem subd7_3_689 : subd7_3 [2, 0, -7] = true := by decide +kernel
theorem subd7_3_690 : subd7_3 [2, 0, -6] = true := by decide +kernel
theorem subd7_3_691 : subd7_3 [2, 0, -5] = true := by decide +kernel
theorem subd7_3_692 : subd7_3 [2, 0, -4] = true := by decide +kernel
theorem subd7_3_693 : subd7_3 [2, 0, -3] = true := by decide +kernel
theorem subd7_3_694 : subd7_3 [2, 0, -2] = true := by decide +kernel
theorem subd7_3_695 : subd7_3 [2, 0, -1] = true := by decide +kernel
theorem subd7_3_696 : subd7_3 [2, 0, 0] = true := by decide +kernel
theorem subd7_3_697 : subd7_3 [2, 0, 1] = true := by decide +kernel
theorem subd7_3_698 : subd7_3 [2, 0, 2] = true := by decide +kernel
theorem subd7_3_699 : subd7_3 [2, 0, 3] = true := by decide +kernel
theorem subd7_3_700 : subd7_3 [2, 0, 4] = true := by decide +kernel
theorem subd7_3_701 : subd7_3 [2, 0, 5] = true := by decide +kernel
theorem subd7_3_702 : subd7_3 [2, 0, 6] = true := by decide +kernel
theorem subd7_3_703 : subd7_3 [2, 0, 7] = true := by decide +kernel
theorem sbd7_3_21 : ∀ q ∈ blkd7_3_21, subd7_3 q = true := by
  unfold blkd7_3_21
  exact List.forall_mem_cons.2 ⟨subd7_3_672, List.forall_mem_cons.2 ⟨subd7_3_673, List.forall_mem_cons.2 ⟨subd7_3_674, List.forall_mem_cons.2 ⟨subd7_3_675, List.forall_mem_cons.2 ⟨subd7_3_676, List.forall_mem_cons.2 ⟨subd7_3_677, List.forall_mem_cons.2 ⟨subd7_3_678, List.forall_mem_cons.2 ⟨subd7_3_679, List.forall_mem_cons.2 ⟨subd7_3_680, List.forall_mem_cons.2 ⟨subd7_3_681, List.forall_mem_cons.2 ⟨subd7_3_682, List.forall_mem_cons.2 ⟨subd7_3_683, List.forall_mem_cons.2 ⟨subd7_3_684, List.forall_mem_cons.2 ⟨subd7_3_685, List.forall_mem_cons.2 ⟨subd7_3_686, List.forall_mem_cons.2 ⟨subd7_3_687, List.forall_mem_cons.2 ⟨subd7_3_688, List.forall_mem_cons.2 ⟨subd7_3_689, List.forall_mem_cons.2 ⟨subd7_3_690, List.forall_mem_cons.2 ⟨subd7_3_691, List.forall_mem_cons.2 ⟨subd7_3_692, List.forall_mem_cons.2 ⟨subd7_3_693, List.forall_mem_cons.2 ⟨subd7_3_694, List.forall_mem_cons.2 ⟨subd7_3_695, List.forall_mem_cons.2 ⟨subd7_3_696, List.forall_mem_cons.2 ⟨subd7_3_697, List.forall_mem_cons.2 ⟨subd7_3_698, List.forall_mem_cons.2 ⟨subd7_3_699, List.forall_mem_cons.2 ⟨subd7_3_700, List.forall_mem_cons.2 ⟨subd7_3_701, List.forall_mem_cons.2 ⟨subd7_3_702, List.forall_mem_cons.2 ⟨subd7_3_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_704 : subd7_3 [2, 0, 8] = true := by decide +kernel
theorem subd7_3_705 : subd7_3 [2, 0, 9] = true := by decide +kernel
theorem subd7_3_706 : subd7_3 [2, 0, 10] = true := by decide +kernel
theorem subd7_3_707 : subd7_3 [2, 0, 11] = true := by decide +kernel
theorem subd7_3_708 : subd7_3 [2, 1, -10] = true := by decide +kernel
theorem subd7_3_709 : subd7_3 [2, 1, -9] = true := by decide +kernel
theorem subd7_3_710 : subd7_3 [2, 1, -8] = true := by decide +kernel
theorem subd7_3_711 : subd7_3 [2, 1, -7] = true := by decide +kernel
theorem subd7_3_712 : subd7_3 [2, 1, -6] = true := by decide +kernel
theorem subd7_3_713 : subd7_3 [2, 1, -5] = true := by decide +kernel
theorem subd7_3_714 : subd7_3 [2, 1, -4] = true := by decide +kernel
theorem subd7_3_715 : subd7_3 [2, 1, -3] = true := by decide +kernel
theorem subd7_3_716 : subd7_3 [2, 1, -2] = true := by decide +kernel
theorem subd7_3_717 : subd7_3 [2, 1, -1] = true := by decide +kernel
theorem subd7_3_718 : subd7_3 [2, 1, 0] = true := by decide +kernel
theorem subd7_3_719 : subd7_3 [2, 1, 1] = true := by decide +kernel
theorem subd7_3_720 : subd7_3 [2, 1, 2] = true := by decide +kernel
theorem subd7_3_721 : subd7_3 [2, 1, 3] = true := by decide +kernel
theorem subd7_3_722 : subd7_3 [2, 1, 4] = true := by decide +kernel
theorem subd7_3_723 : subd7_3 [2, 1, 5] = true := by decide +kernel
theorem subd7_3_724 : subd7_3 [2, 1, 6] = true := by decide +kernel
theorem subd7_3_725 : subd7_3 [2, 1, 7] = true := by decide +kernel
theorem subd7_3_726 : subd7_3 [2, 1, 8] = true := by decide +kernel
theorem subd7_3_727 : subd7_3 [2, 1, 9] = true := by decide +kernel
theorem subd7_3_728 : subd7_3 [2, 1, 10] = true := by decide +kernel
theorem subd7_3_729 : subd7_3 [2, 2, -8] = true := by decide +kernel
theorem subd7_3_730 : subd7_3 [2, 2, -7] = true := by decide +kernel
theorem subd7_3_731 : subd7_3 [2, 2, -6] = true := by decide +kernel
theorem subd7_3_732 : subd7_3 [2, 2, -5] = true := by decide +kernel
theorem subd7_3_733 : subd7_3 [2, 2, -4] = true := by decide +kernel
theorem subd7_3_734 : subd7_3 [2, 2, -3] = true := by decide +kernel
theorem subd7_3_735 : subd7_3 [2, 2, -2] = true := by decide +kernel
theorem sbd7_3_22 : ∀ q ∈ blkd7_3_22, subd7_3 q = true := by
  unfold blkd7_3_22
  exact List.forall_mem_cons.2 ⟨subd7_3_704, List.forall_mem_cons.2 ⟨subd7_3_705, List.forall_mem_cons.2 ⟨subd7_3_706, List.forall_mem_cons.2 ⟨subd7_3_707, List.forall_mem_cons.2 ⟨subd7_3_708, List.forall_mem_cons.2 ⟨subd7_3_709, List.forall_mem_cons.2 ⟨subd7_3_710, List.forall_mem_cons.2 ⟨subd7_3_711, List.forall_mem_cons.2 ⟨subd7_3_712, List.forall_mem_cons.2 ⟨subd7_3_713, List.forall_mem_cons.2 ⟨subd7_3_714, List.forall_mem_cons.2 ⟨subd7_3_715, List.forall_mem_cons.2 ⟨subd7_3_716, List.forall_mem_cons.2 ⟨subd7_3_717, List.forall_mem_cons.2 ⟨subd7_3_718, List.forall_mem_cons.2 ⟨subd7_3_719, List.forall_mem_cons.2 ⟨subd7_3_720, List.forall_mem_cons.2 ⟨subd7_3_721, List.forall_mem_cons.2 ⟨subd7_3_722, List.forall_mem_cons.2 ⟨subd7_3_723, List.forall_mem_cons.2 ⟨subd7_3_724, List.forall_mem_cons.2 ⟨subd7_3_725, List.forall_mem_cons.2 ⟨subd7_3_726, List.forall_mem_cons.2 ⟨subd7_3_727, List.forall_mem_cons.2 ⟨subd7_3_728, List.forall_mem_cons.2 ⟨subd7_3_729, List.forall_mem_cons.2 ⟨subd7_3_730, List.forall_mem_cons.2 ⟨subd7_3_731, List.forall_mem_cons.2 ⟨subd7_3_732, List.forall_mem_cons.2 ⟨subd7_3_733, List.forall_mem_cons.2 ⟨subd7_3_734, List.forall_mem_cons.2 ⟨subd7_3_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_736 : subd7_3 [2, 2, -1] = true := by decide +kernel
theorem subd7_3_737 : subd7_3 [2, 2, 0] = true := by decide +kernel
theorem subd7_3_738 : subd7_3 [2, 2, 1] = true := by decide +kernel
theorem subd7_3_739 : subd7_3 [2, 2, 2] = true := by decide +kernel
theorem subd7_3_740 : subd7_3 [2, 2, 3] = true := by decide +kernel
theorem subd7_3_741 : subd7_3 [2, 2, 4] = true := by decide +kernel
theorem subd7_3_742 : subd7_3 [2, 2, 5] = true := by decide +kernel
theorem subd7_3_743 : subd7_3 [2, 2, 6] = true := by decide +kernel
theorem subd7_3_744 : subd7_3 [2, 2, 7] = true := by decide +kernel
theorem subd7_3_745 : subd7_3 [2, 2, 8] = true := by decide +kernel
theorem subd7_3_746 : subd7_3 [2, 3] = true := by decide +kernel
theorem subd7_3_747 : subd7_3 [3, -4] = true := by decide +kernel
theorem subd7_3_748 : subd7_3 [3, -3] = true := by decide +kernel
theorem subd7_3_749 : subd7_3 [3, -2, -6] = true := by decide +kernel
theorem subd7_3_750 : subd7_3 [3, -2, -5] = true := by decide +kernel
theorem subd7_3_751 : subd7_3 [3, -2, -4] = true := by decide +kernel
theorem subd7_3_752 : subd7_3 [3, -2, -3] = true := by decide +kernel
theorem subd7_3_753 : subd7_3 [3, -2, -2] = true := by decide +kernel
theorem subd7_3_754 : subd7_3 [3, -2, -1] = true := by decide +kernel
theorem subd7_3_755 : subd7_3 [3, -2, 0] = true := by decide +kernel
theorem subd7_3_756 : subd7_3 [3, -2, 1] = true := by decide +kernel
theorem subd7_3_757 : subd7_3 [3, -2, 2] = true := by decide +kernel
theorem subd7_3_758 : subd7_3 [3, -2, 3] = true := by decide +kernel
theorem subd7_3_759 : subd7_3 [3, -2, 4] = true := by decide +kernel
theorem subd7_3_760 : subd7_3 [3, -2, 5] = true := by decide +kernel
theorem subd7_3_761 : subd7_3 [3, -2, 6] = true := by decide +kernel
theorem subd7_3_762 : subd7_3 [3, -2, 7] = true := by decide +kernel
theorem subd7_3_763 : subd7_3 [3, -2, 8] = true := by decide +kernel
theorem subd7_3_764 : subd7_3 [3, -2, 9] = true := by decide +kernel
theorem subd7_3_765 : subd7_3 [3, -1, -8] = true := by decide +kernel
theorem subd7_3_766 : subd7_3 [3, -1, -7] = true := by decide +kernel
theorem subd7_3_767 : subd7_3 [3, -1, -6] = true := by decide +kernel
theorem sbd7_3_23 : ∀ q ∈ blkd7_3_23, subd7_3 q = true := by
  unfold blkd7_3_23
  exact List.forall_mem_cons.2 ⟨subd7_3_736, List.forall_mem_cons.2 ⟨subd7_3_737, List.forall_mem_cons.2 ⟨subd7_3_738, List.forall_mem_cons.2 ⟨subd7_3_739, List.forall_mem_cons.2 ⟨subd7_3_740, List.forall_mem_cons.2 ⟨subd7_3_741, List.forall_mem_cons.2 ⟨subd7_3_742, List.forall_mem_cons.2 ⟨subd7_3_743, List.forall_mem_cons.2 ⟨subd7_3_744, List.forall_mem_cons.2 ⟨subd7_3_745, List.forall_mem_cons.2 ⟨subd7_3_746, List.forall_mem_cons.2 ⟨subd7_3_747, List.forall_mem_cons.2 ⟨subd7_3_748, List.forall_mem_cons.2 ⟨subd7_3_749, List.forall_mem_cons.2 ⟨subd7_3_750, List.forall_mem_cons.2 ⟨subd7_3_751, List.forall_mem_cons.2 ⟨subd7_3_752, List.forall_mem_cons.2 ⟨subd7_3_753, List.forall_mem_cons.2 ⟨subd7_3_754, List.forall_mem_cons.2 ⟨subd7_3_755, List.forall_mem_cons.2 ⟨subd7_3_756, List.forall_mem_cons.2 ⟨subd7_3_757, List.forall_mem_cons.2 ⟨subd7_3_758, List.forall_mem_cons.2 ⟨subd7_3_759, List.forall_mem_cons.2 ⟨subd7_3_760, List.forall_mem_cons.2 ⟨subd7_3_761, List.forall_mem_cons.2 ⟨subd7_3_762, List.forall_mem_cons.2 ⟨subd7_3_763, List.forall_mem_cons.2 ⟨subd7_3_764, List.forall_mem_cons.2 ⟨subd7_3_765, List.forall_mem_cons.2 ⟨subd7_3_766, List.forall_mem_cons.2 ⟨subd7_3_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_768 : subd7_3 [3, -1, -5] = true := by decide +kernel
theorem subd7_3_769 : subd7_3 [3, -1, -4] = true := by decide +kernel
theorem subd7_3_770 : subd7_3 [3, -1, -3] = true := by decide +kernel
theorem subd7_3_771 : subd7_3 [3, -1, -2] = true := by decide +kernel
theorem subd7_3_772 : subd7_3 [3, -1, -1] = true := by decide +kernel
theorem subd7_3_773 : subd7_3 [3, -1, 0] = true := by decide +kernel
theorem subd7_3_774 : subd7_3 [3, -1, 1] = true := by decide +kernel
theorem subd7_3_775 : subd7_3 [3, -1, 2] = true := by decide +kernel
theorem subd7_3_776 : subd7_3 [3, -1, 3] = true := by decide +kernel
theorem subd7_3_777 : subd7_3 [3, -1, 4] = true := by decide +kernel
theorem subd7_3_778 : subd7_3 [3, -1, 5] = true := by decide +kernel
theorem subd7_3_779 : subd7_3 [3, -1, 6] = true := by decide +kernel
theorem subd7_3_780 : subd7_3 [3, -1, 7] = true := by decide +kernel
theorem subd7_3_781 : subd7_3 [3, -1, 8] = true := by decide +kernel
theorem subd7_3_782 : subd7_3 [3, -1, 9] = true := by decide +kernel
theorem subd7_3_783 : subd7_3 [3, -1, 10] = true := by decide +kernel
theorem subd7_3_784 : subd7_3 [3, 0, -8] = true := by decide +kernel
theorem subd7_3_785 : subd7_3 [3, 0, -7] = true := by decide +kernel
theorem subd7_3_786 : subd7_3 [3, 0, -6] = true := by decide +kernel
theorem subd7_3_787 : subd7_3 [3, 0, -5] = true := by decide +kernel
theorem subd7_3_788 : subd7_3 [3, 0, -4] = true := by decide +kernel
theorem subd7_3_789 : subd7_3 [3, 0, -3] = true := by decide +kernel
theorem subd7_3_790 : subd7_3 [3, 0, -2] = true := by decide +kernel
theorem subd7_3_791 : subd7_3 [3, 0, -1] = true := by decide +kernel
theorem subd7_3_792 : subd7_3 [3, 0, 0] = true := by decide +kernel
theorem subd7_3_793 : subd7_3 [3, 0, 1] = true := by decide +kernel
theorem subd7_3_794 : subd7_3 [3, 0, 2] = true := by decide +kernel
theorem subd7_3_795 : subd7_3 [3, 0, 3] = true := by decide +kernel
theorem subd7_3_796 : subd7_3 [3, 0, 4] = true := by decide +kernel
theorem subd7_3_797 : subd7_3 [3, 0, 5] = true := by decide +kernel
theorem subd7_3_798 : subd7_3 [3, 0, 6] = true := by decide +kernel
theorem subd7_3_799 : subd7_3 [3, 0, 7] = true := by decide +kernel
theorem sbd7_3_24 : ∀ q ∈ blkd7_3_24, subd7_3 q = true := by
  unfold blkd7_3_24
  exact List.forall_mem_cons.2 ⟨subd7_3_768, List.forall_mem_cons.2 ⟨subd7_3_769, List.forall_mem_cons.2 ⟨subd7_3_770, List.forall_mem_cons.2 ⟨subd7_3_771, List.forall_mem_cons.2 ⟨subd7_3_772, List.forall_mem_cons.2 ⟨subd7_3_773, List.forall_mem_cons.2 ⟨subd7_3_774, List.forall_mem_cons.2 ⟨subd7_3_775, List.forall_mem_cons.2 ⟨subd7_3_776, List.forall_mem_cons.2 ⟨subd7_3_777, List.forall_mem_cons.2 ⟨subd7_3_778, List.forall_mem_cons.2 ⟨subd7_3_779, List.forall_mem_cons.2 ⟨subd7_3_780, List.forall_mem_cons.2 ⟨subd7_3_781, List.forall_mem_cons.2 ⟨subd7_3_782, List.forall_mem_cons.2 ⟨subd7_3_783, List.forall_mem_cons.2 ⟨subd7_3_784, List.forall_mem_cons.2 ⟨subd7_3_785, List.forall_mem_cons.2 ⟨subd7_3_786, List.forall_mem_cons.2 ⟨subd7_3_787, List.forall_mem_cons.2 ⟨subd7_3_788, List.forall_mem_cons.2 ⟨subd7_3_789, List.forall_mem_cons.2 ⟨subd7_3_790, List.forall_mem_cons.2 ⟨subd7_3_791, List.forall_mem_cons.2 ⟨subd7_3_792, List.forall_mem_cons.2 ⟨subd7_3_793, List.forall_mem_cons.2 ⟨subd7_3_794, List.forall_mem_cons.2 ⟨subd7_3_795, List.forall_mem_cons.2 ⟨subd7_3_796, List.forall_mem_cons.2 ⟨subd7_3_797, List.forall_mem_cons.2 ⟨subd7_3_798, List.forall_mem_cons.2 ⟨subd7_3_799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_800 : subd7_3 [3, 0, 8] = true := by decide +kernel
theorem subd7_3_801 : subd7_3 [3, 0, 9] = true := by decide +kernel
theorem subd7_3_802 : subd7_3 [3, 1, -7] = true := by decide +kernel
theorem subd7_3_803 : subd7_3 [3, 1, -6] = true := by decide +kernel
theorem subd7_3_804 : subd7_3 [3, 1, -5] = true := by decide +kernel
theorem subd7_3_805 : subd7_3 [3, 1, -4] = true := by decide +kernel
theorem subd7_3_806 : subd7_3 [3, 1, -3] = true := by decide +kernel
theorem subd7_3_807 : subd7_3 [3, 1, -2] = true := by decide +kernel
theorem subd7_3_808 : subd7_3 [3, 1, -1] = true := by decide +kernel
theorem subd7_3_809 : subd7_3 [3, 1, 0] = true := by decide +kernel
theorem subd7_3_810 : subd7_3 [3, 1, 1] = true := by decide +kernel
theorem subd7_3_811 : subd7_3 [3, 1, 2] = true := by decide +kernel
theorem subd7_3_812 : subd7_3 [3, 1, 3] = true := by decide +kernel
theorem subd7_3_813 : subd7_3 [3, 1, 4] = true := by decide +kernel
theorem subd7_3_814 : subd7_3 [3, 1, 5] = true := by decide +kernel
theorem subd7_3_815 : subd7_3 [3, 1, 6] = true := by decide +kernel
theorem subd7_3_816 : subd7_3 [3, 1, 7] = true := by decide +kernel
theorem subd7_3_817 : subd7_3 [3, 1, 8] = true := by decide +kernel
theorem subd7_3_818 : subd7_3 [3, 2] = true := by decide +kernel
theorem subd7_3_819 : subd7_3 [4, -3] = true := by decide +kernel
theorem subd7_3_820 : subd7_3 [4, -2] = true := by decide +kernel
theorem subd7_3_821 : subd7_3 [4, -1] = true := by decide +kernel
theorem subd7_3_822 : subd7_3 [4, 0] = true := by decide +kernel
theorem sbd7_3_25 : ∀ q ∈ blkd7_3_25, subd7_3 q = true := by
  unfold blkd7_3_25
  exact List.forall_mem_cons.2 ⟨subd7_3_800, List.forall_mem_cons.2 ⟨subd7_3_801, List.forall_mem_cons.2 ⟨subd7_3_802, List.forall_mem_cons.2 ⟨subd7_3_803, List.forall_mem_cons.2 ⟨subd7_3_804, List.forall_mem_cons.2 ⟨subd7_3_805, List.forall_mem_cons.2 ⟨subd7_3_806, List.forall_mem_cons.2 ⟨subd7_3_807, List.forall_mem_cons.2 ⟨subd7_3_808, List.forall_mem_cons.2 ⟨subd7_3_809, List.forall_mem_cons.2 ⟨subd7_3_810, List.forall_mem_cons.2 ⟨subd7_3_811, List.forall_mem_cons.2 ⟨subd7_3_812, List.forall_mem_cons.2 ⟨subd7_3_813, List.forall_mem_cons.2 ⟨subd7_3_814, List.forall_mem_cons.2 ⟨subd7_3_815, List.forall_mem_cons.2 ⟨subd7_3_816, List.forall_mem_cons.2 ⟨subd7_3_817, List.forall_mem_cons.2 ⟨subd7_3_818, List.forall_mem_cons.2 ⟨subd7_3_819, List.forall_mem_cons.2 ⟨subd7_3_820, List.forall_mem_cons.2 ⟨subd7_3_821, List.forall_mem_cons.2 ⟨subd7_3_822, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_0 : ldCheck G d8_0.U d8_0.ms ldd8_0 = true := by decide +kernel
theorem pre_okd8_0 : subPre G cell8 d8_0 = true := by decide +kernel
theorem subd8_0_0 : subd8_0 [-2] = true := by decide +kernel
theorem subd8_0_1 : subd8_0 [-1] = true := by decide +kernel
theorem subd8_0_2 : subd8_0 [0, -3] = true := by decide +kernel
theorem subd8_0_3 : subd8_0 [0, -2] = true := by decide +kernel
theorem subd8_0_4 : subd8_0 [0, -1] = true := by decide +kernel
theorem subd8_0_5 : subd8_0 [0, 0] = true := by decide +kernel
theorem subd8_0_6 : subd8_0 [0, 1] = true := by decide +kernel
theorem subd8_0_7 : subd8_0 [0, 2] = true := by decide +kernel
theorem subd8_0_8 : subd8_0 [1] = true := by decide +kernel
theorem subd8_0_9 : subd8_0 [2] = true := by decide +kernel
theorem sbd8_0_0 : ∀ q ∈ blkd8_0_0, subd8_0 q = true := by
  unfold blkd8_0_0
  exact List.forall_mem_cons.2 ⟨subd8_0_0, List.forall_mem_cons.2 ⟨subd8_0_1, List.forall_mem_cons.2 ⟨subd8_0_2, List.forall_mem_cons.2 ⟨subd8_0_3, List.forall_mem_cons.2 ⟨subd8_0_4, List.forall_mem_cons.2 ⟨subd8_0_5, List.forall_mem_cons.2 ⟨subd8_0_6, List.forall_mem_cons.2 ⟨subd8_0_7, List.forall_mem_cons.2 ⟨subd8_0_8, List.forall_mem_cons.2 ⟨subd8_0_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_1 : ldCheck G d8_1.U d8_1.ms ldd8_1 = true := by decide +kernel
theorem pre_okd8_1 : subPre G cell8 d8_1 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C111
