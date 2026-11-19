import ReflectZphi.Data.Cert5.C116.Base

namespace ReflectZphi.Data.Cert5.C116

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd10_1_608 : subd10_1 [0, -5, -6] = true := by decide +kernel
theorem subd10_1_609 : subd10_1 [0, -5, -5] = true := by decide +kernel
theorem subd10_1_610 : subd10_1 [0, -5, -4] = true := by decide +kernel
theorem subd10_1_611 : subd10_1 [0, -5, -3] = true := by decide +kernel
theorem subd10_1_612 : subd10_1 [0, -5, -2] = true := by decide +kernel
theorem subd10_1_613 : subd10_1 [0, -5, -1] = true := by decide +kernel
theorem subd10_1_614 : subd10_1 [0, -5, 0] = true := by decide +kernel
theorem subd10_1_615 : subd10_1 [0, -5, 1] = true := by decide +kernel
theorem subd10_1_616 : subd10_1 [0, -5, 2] = true := by decide +kernel
theorem subd10_1_617 : subd10_1 [0, -5, 3] = true := by decide +kernel
theorem subd10_1_618 : subd10_1 [0, -5, 4] = true := by decide +kernel
theorem subd10_1_619 : subd10_1 [0, -5, 5] = true := by decide +kernel
theorem subd10_1_620 : subd10_1 [0, -5, 6] = true := by decide +kernel
theorem subd10_1_621 : subd10_1 [0, -5, 7] = true := by decide +kernel
theorem subd10_1_622 : subd10_1 [0, -4, -7] = true := by decide +kernel
theorem subd10_1_623 : subd10_1 [0, -4, -6] = true := by decide +kernel
theorem subd10_1_624 : subd10_1 [0, -4, -5] = true := by decide +kernel
theorem subd10_1_625 : subd10_1 [0, -4, -4] = true := by decide +kernel
theorem subd10_1_626 : subd10_1 [0, -4, -3] = true := by decide +kernel
theorem subd10_1_627 : subd10_1 [0, -4, -2] = true := by decide +kernel
theorem subd10_1_628 : subd10_1 [0, -4, -1] = true := by decide +kernel
theorem subd10_1_629 : subd10_1 [0, -4, 0] = true := by decide +kernel
theorem subd10_1_630 : subd10_1 [0, -4, 1] = true := by decide +kernel
theorem subd10_1_631 : subd10_1 [0, -4, 2] = true := by decide +kernel
theorem subd10_1_632 : subd10_1 [0, -4, 3] = true := by decide +kernel
theorem subd10_1_633 : subd10_1 [0, -4, 4] = true := by decide +kernel
theorem subd10_1_634 : subd10_1 [0, -4, 5] = true := by decide +kernel
theorem subd10_1_635 : subd10_1 [0, -4, 6] = true := by decide +kernel
theorem subd10_1_636 : subd10_1 [0, -4, 7] = true := by decide +kernel
theorem subd10_1_637 : subd10_1 [0, -3, -8] = true := by decide +kernel
theorem subd10_1_638 : subd10_1 [0, -3, -7] = true := by decide +kernel
theorem subd10_1_639 : subd10_1 [0, -3, -6] = true := by decide +kernel
theorem sbd10_1_19 : ∀ q ∈ blkd10_1_19, subd10_1 q = true := by
  unfold blkd10_1_19
  exact List.forall_mem_cons.2 ⟨subd10_1_608, List.forall_mem_cons.2 ⟨subd10_1_609, List.forall_mem_cons.2 ⟨subd10_1_610, List.forall_mem_cons.2 ⟨subd10_1_611, List.forall_mem_cons.2 ⟨subd10_1_612, List.forall_mem_cons.2 ⟨subd10_1_613, List.forall_mem_cons.2 ⟨subd10_1_614, List.forall_mem_cons.2 ⟨subd10_1_615, List.forall_mem_cons.2 ⟨subd10_1_616, List.forall_mem_cons.2 ⟨subd10_1_617, List.forall_mem_cons.2 ⟨subd10_1_618, List.forall_mem_cons.2 ⟨subd10_1_619, List.forall_mem_cons.2 ⟨subd10_1_620, List.forall_mem_cons.2 ⟨subd10_1_621, List.forall_mem_cons.2 ⟨subd10_1_622, List.forall_mem_cons.2 ⟨subd10_1_623, List.forall_mem_cons.2 ⟨subd10_1_624, List.forall_mem_cons.2 ⟨subd10_1_625, List.forall_mem_cons.2 ⟨subd10_1_626, List.forall_mem_cons.2 ⟨subd10_1_627, List.forall_mem_cons.2 ⟨subd10_1_628, List.forall_mem_cons.2 ⟨subd10_1_629, List.forall_mem_cons.2 ⟨subd10_1_630, List.forall_mem_cons.2 ⟨subd10_1_631, List.forall_mem_cons.2 ⟨subd10_1_632, List.forall_mem_cons.2 ⟨subd10_1_633, List.forall_mem_cons.2 ⟨subd10_1_634, List.forall_mem_cons.2 ⟨subd10_1_635, List.forall_mem_cons.2 ⟨subd10_1_636, List.forall_mem_cons.2 ⟨subd10_1_637, List.forall_mem_cons.2 ⟨subd10_1_638, List.forall_mem_cons.2 ⟨subd10_1_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_640 : subd10_1 [0, -3, -5] = true := by decide +kernel
theorem subd10_1_641 : subd10_1 [0, -3, -4] = true := by decide +kernel
theorem subd10_1_642 : subd10_1 [0, -3, -3] = true := by decide +kernel
theorem subd10_1_643 : subd10_1 [0, -3, -2] = true := by decide +kernel
theorem subd10_1_644 : subd10_1 [0, -3, -1] = true := by decide +kernel
theorem subd10_1_645 : subd10_1 [0, -3, 0] = true := by decide +kernel
theorem subd10_1_646 : subd10_1 [0, -3, 1] = true := by decide +kernel
theorem subd10_1_647 : subd10_1 [0, -3, 2] = true := by decide +kernel
theorem subd10_1_648 : subd10_1 [0, -3, 3] = true := by decide +kernel
theorem subd10_1_649 : subd10_1 [0, -3, 4] = true := by decide +kernel
theorem subd10_1_650 : subd10_1 [0, -3, 5] = true := by decide +kernel
theorem subd10_1_651 : subd10_1 [0, -3, 6] = true := by decide +kernel
theorem subd10_1_652 : subd10_1 [0, -3, 7] = true := by decide +kernel
theorem subd10_1_653 : subd10_1 [0, -3, 8] = true := by decide +kernel
theorem subd10_1_654 : subd10_1 [0, -2, -8] = true := by decide +kernel
theorem subd10_1_655 : subd10_1 [0, -2, -7] = true := by decide +kernel
theorem subd10_1_656 : subd10_1 [0, -2, -6] = true := by decide +kernel
theorem subd10_1_657 : subd10_1 [0, -2, -5] = true := by decide +kernel
theorem subd10_1_658 : subd10_1 [0, -2, -4] = true := by decide +kernel
theorem subd10_1_659 : subd10_1 [0, -2, -3] = true := by decide +kernel
theorem subd10_1_660 : subd10_1 [0, -2, -2] = true := by decide +kernel
theorem subd10_1_661 : subd10_1 [0, -2, -1] = true := by decide +kernel
theorem subd10_1_662 : subd10_1 [0, -2, 0] = true := by decide +kernel
theorem subd10_1_663 : subd10_1 [0, -2, 1] = true := by decide +kernel
theorem subd10_1_664 : subd10_1 [0, -2, 2] = true := by decide +kernel
theorem subd10_1_665 : subd10_1 [0, -2, 3] = true := by decide +kernel
theorem subd10_1_666 : subd10_1 [0, -2, 4] = true := by decide +kernel
theorem subd10_1_667 : subd10_1 [0, -2, 5] = true := by decide +kernel
theorem subd10_1_668 : subd10_1 [0, -2, 6] = true := by decide +kernel
theorem subd10_1_669 : subd10_1 [0, -2, 7] = true := by decide +kernel
theorem subd10_1_670 : subd10_1 [0, -2, 8] = true := by decide +kernel
theorem subd10_1_671 : subd10_1 [0, -1, -8] = true := by decide +kernel
theorem sbd10_1_20 : ∀ q ∈ blkd10_1_20, subd10_1 q = true := by
  unfold blkd10_1_20
  exact List.forall_mem_cons.2 ⟨subd10_1_640, List.forall_mem_cons.2 ⟨subd10_1_641, List.forall_mem_cons.2 ⟨subd10_1_642, List.forall_mem_cons.2 ⟨subd10_1_643, List.forall_mem_cons.2 ⟨subd10_1_644, List.forall_mem_cons.2 ⟨subd10_1_645, List.forall_mem_cons.2 ⟨subd10_1_646, List.forall_mem_cons.2 ⟨subd10_1_647, List.forall_mem_cons.2 ⟨subd10_1_648, List.forall_mem_cons.2 ⟨subd10_1_649, List.forall_mem_cons.2 ⟨subd10_1_650, List.forall_mem_cons.2 ⟨subd10_1_651, List.forall_mem_cons.2 ⟨subd10_1_652, List.forall_mem_cons.2 ⟨subd10_1_653, List.forall_mem_cons.2 ⟨subd10_1_654, List.forall_mem_cons.2 ⟨subd10_1_655, List.forall_mem_cons.2 ⟨subd10_1_656, List.forall_mem_cons.2 ⟨subd10_1_657, List.forall_mem_cons.2 ⟨subd10_1_658, List.forall_mem_cons.2 ⟨subd10_1_659, List.forall_mem_cons.2 ⟨subd10_1_660, List.forall_mem_cons.2 ⟨subd10_1_661, List.forall_mem_cons.2 ⟨subd10_1_662, List.forall_mem_cons.2 ⟨subd10_1_663, List.forall_mem_cons.2 ⟨subd10_1_664, List.forall_mem_cons.2 ⟨subd10_1_665, List.forall_mem_cons.2 ⟨subd10_1_666, List.forall_mem_cons.2 ⟨subd10_1_667, List.forall_mem_cons.2 ⟨subd10_1_668, List.forall_mem_cons.2 ⟨subd10_1_669, List.forall_mem_cons.2 ⟨subd10_1_670, List.forall_mem_cons.2 ⟨subd10_1_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_672 : subd10_1 [0, -1, -7] = true := by decide +kernel
theorem subd10_1_673 : subd10_1 [0, -1, -6] = true := by decide +kernel
theorem subd10_1_674 : subd10_1 [0, -1, -5] = true := by decide +kernel
theorem subd10_1_675 : subd10_1 [0, -1, -4] = true := by decide +kernel
theorem subd10_1_676 : subd10_1 [0, -1, -3] = true := by decide +kernel
theorem subd10_1_677 : subd10_1 [0, -1, -2] = true := by decide +kernel
theorem subd10_1_678 : subd10_1 [0, -1, -1] = true := by decide +kernel
theorem subd10_1_679 : subd10_1 [0, -1, 0] = true := by decide +kernel
theorem subd10_1_680 : subd10_1 [0, -1, 1] = true := by decide +kernel
theorem subd10_1_681 : subd10_1 [0, -1, 2] = true := by decide +kernel
theorem subd10_1_682 : subd10_1 [0, -1, 3] = true := by decide +kernel
theorem subd10_1_683 : subd10_1 [0, -1, 4] = true := by decide +kernel
theorem subd10_1_684 : subd10_1 [0, -1, 5] = true := by decide +kernel
theorem subd10_1_685 : subd10_1 [0, -1, 6] = true := by decide +kernel
theorem subd10_1_686 : subd10_1 [0, -1, 7] = true := by decide +kernel
theorem subd10_1_687 : subd10_1 [0, -1, 8] = true := by decide +kernel
theorem subd10_1_688 : subd10_1 [0, 0, -9] = true := by decide +kernel
theorem subd10_1_689 : subd10_1 [0, 0, -8] = true := by decide +kernel
theorem subd10_1_690 : subd10_1 [0, 0, -7] = true := by decide +kernel
theorem subd10_1_691 : subd10_1 [0, 0, -6] = true := by decide +kernel
theorem subd10_1_692 : subd10_1 [0, 0, -5] = true := by decide +kernel
theorem subd10_1_693 : subd10_1 [0, 0, -4] = true := by decide +kernel
theorem subd10_1_694 : subd10_1 [0, 0, -3] = true := by decide +kernel
theorem subd10_1_695 : subd10_1 [0, 0, -2] = true := by decide +kernel
theorem subd10_1_696 : subd10_1 [0, 0, -1] = true := by decide +kernel
theorem subd10_1_697 : subd10_1 [0, 0, 0] = true := by decide +kernel
theorem subd10_1_698 : subd10_1 [0, 0, 1] = true := by decide +kernel
theorem subd10_1_699 : subd10_1 [0, 0, 2] = true := by decide +kernel
theorem subd10_1_700 : subd10_1 [0, 0, 3] = true := by decide +kernel
theorem subd10_1_701 : subd10_1 [0, 0, 4] = true := by decide +kernel
theorem subd10_1_702 : subd10_1 [0, 0, 5] = true := by decide +kernel
theorem subd10_1_703 : subd10_1 [0, 0, 6] = true := by decide +kernel
theorem sbd10_1_21 : ∀ q ∈ blkd10_1_21, subd10_1 q = true := by
  unfold blkd10_1_21
  exact List.forall_mem_cons.2 ⟨subd10_1_672, List.forall_mem_cons.2 ⟨subd10_1_673, List.forall_mem_cons.2 ⟨subd10_1_674, List.forall_mem_cons.2 ⟨subd10_1_675, List.forall_mem_cons.2 ⟨subd10_1_676, List.forall_mem_cons.2 ⟨subd10_1_677, List.forall_mem_cons.2 ⟨subd10_1_678, List.forall_mem_cons.2 ⟨subd10_1_679, List.forall_mem_cons.2 ⟨subd10_1_680, List.forall_mem_cons.2 ⟨subd10_1_681, List.forall_mem_cons.2 ⟨subd10_1_682, List.forall_mem_cons.2 ⟨subd10_1_683, List.forall_mem_cons.2 ⟨subd10_1_684, List.forall_mem_cons.2 ⟨subd10_1_685, List.forall_mem_cons.2 ⟨subd10_1_686, List.forall_mem_cons.2 ⟨subd10_1_687, List.forall_mem_cons.2 ⟨subd10_1_688, List.forall_mem_cons.2 ⟨subd10_1_689, List.forall_mem_cons.2 ⟨subd10_1_690, List.forall_mem_cons.2 ⟨subd10_1_691, List.forall_mem_cons.2 ⟨subd10_1_692, List.forall_mem_cons.2 ⟨subd10_1_693, List.forall_mem_cons.2 ⟨subd10_1_694, List.forall_mem_cons.2 ⟨subd10_1_695, List.forall_mem_cons.2 ⟨subd10_1_696, List.forall_mem_cons.2 ⟨subd10_1_697, List.forall_mem_cons.2 ⟨subd10_1_698, List.forall_mem_cons.2 ⟨subd10_1_699, List.forall_mem_cons.2 ⟨subd10_1_700, List.forall_mem_cons.2 ⟨subd10_1_701, List.forall_mem_cons.2 ⟨subd10_1_702, List.forall_mem_cons.2 ⟨subd10_1_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_704 : subd10_1 [0, 0, 7] = true := by decide +kernel
theorem subd10_1_705 : subd10_1 [0, 0, 8] = true := by decide +kernel
theorem subd10_1_706 : subd10_1 [0, 1, -9] = true := by decide +kernel
theorem subd10_1_707 : subd10_1 [0, 1, -8] = true := by decide +kernel
theorem subd10_1_708 : subd10_1 [0, 1, -7] = true := by decide +kernel
theorem subd10_1_709 : subd10_1 [0, 1, -6] = true := by decide +kernel
theorem subd10_1_710 : subd10_1 [0, 1, -5] = true := by decide +kernel
theorem subd10_1_711 : subd10_1 [0, 1, -4] = true := by decide +kernel
theorem subd10_1_712 : subd10_1 [0, 1, -3] = true := by decide +kernel
theorem subd10_1_713 : subd10_1 [0, 1, -2] = true := by decide +kernel
theorem subd10_1_714 : subd10_1 [0, 1, -1] = true := by decide +kernel
theorem subd10_1_715 : subd10_1 [0, 1, 0] = true := by decide +kernel
theorem subd10_1_716 : subd10_1 [0, 1, 1] = true := by decide +kernel
theorem subd10_1_717 : subd10_1 [0, 1, 2] = true := by decide +kernel
theorem subd10_1_718 : subd10_1 [0, 1, 3] = true := by decide +kernel
theorem subd10_1_719 : subd10_1 [0, 1, 4] = true := by decide +kernel
theorem subd10_1_720 : subd10_1 [0, 1, 5] = true := by decide +kernel
theorem subd10_1_721 : subd10_1 [0, 1, 6] = true := by decide +kernel
theorem subd10_1_722 : subd10_1 [0, 1, 7] = true := by decide +kernel
theorem subd10_1_723 : subd10_1 [0, 2, -9] = true := by decide +kernel
theorem subd10_1_724 : subd10_1 [0, 2, -8] = true := by decide +kernel
theorem subd10_1_725 : subd10_1 [0, 2, -7] = true := by decide +kernel
theorem subd10_1_726 : subd10_1 [0, 2, -6] = true := by decide +kernel
theorem subd10_1_727 : subd10_1 [0, 2, -5] = true := by decide +kernel
theorem subd10_1_728 : subd10_1 [0, 2, -4] = true := by decide +kernel
theorem subd10_1_729 : subd10_1 [0, 2, -3] = true := by decide +kernel
theorem subd10_1_730 : subd10_1 [0, 2, -2] = true := by decide +kernel
theorem subd10_1_731 : subd10_1 [0, 2, -1] = true := by decide +kernel
theorem subd10_1_732 : subd10_1 [0, 2, 0] = true := by decide +kernel
theorem subd10_1_733 : subd10_1 [0, 2, 1] = true := by decide +kernel
theorem subd10_1_734 : subd10_1 [0, 2, 2] = true := by decide +kernel
theorem subd10_1_735 : subd10_1 [0, 2, 3] = true := by decide +kernel
theorem sbd10_1_22 : ∀ q ∈ blkd10_1_22, subd10_1 q = true := by
  unfold blkd10_1_22
  exact List.forall_mem_cons.2 ⟨subd10_1_704, List.forall_mem_cons.2 ⟨subd10_1_705, List.forall_mem_cons.2 ⟨subd10_1_706, List.forall_mem_cons.2 ⟨subd10_1_707, List.forall_mem_cons.2 ⟨subd10_1_708, List.forall_mem_cons.2 ⟨subd10_1_709, List.forall_mem_cons.2 ⟨subd10_1_710, List.forall_mem_cons.2 ⟨subd10_1_711, List.forall_mem_cons.2 ⟨subd10_1_712, List.forall_mem_cons.2 ⟨subd10_1_713, List.forall_mem_cons.2 ⟨subd10_1_714, List.forall_mem_cons.2 ⟨subd10_1_715, List.forall_mem_cons.2 ⟨subd10_1_716, List.forall_mem_cons.2 ⟨subd10_1_717, List.forall_mem_cons.2 ⟨subd10_1_718, List.forall_mem_cons.2 ⟨subd10_1_719, List.forall_mem_cons.2 ⟨subd10_1_720, List.forall_mem_cons.2 ⟨subd10_1_721, List.forall_mem_cons.2 ⟨subd10_1_722, List.forall_mem_cons.2 ⟨subd10_1_723, List.forall_mem_cons.2 ⟨subd10_1_724, List.forall_mem_cons.2 ⟨subd10_1_725, List.forall_mem_cons.2 ⟨subd10_1_726, List.forall_mem_cons.2 ⟨subd10_1_727, List.forall_mem_cons.2 ⟨subd10_1_728, List.forall_mem_cons.2 ⟨subd10_1_729, List.forall_mem_cons.2 ⟨subd10_1_730, List.forall_mem_cons.2 ⟨subd10_1_731, List.forall_mem_cons.2 ⟨subd10_1_732, List.forall_mem_cons.2 ⟨subd10_1_733, List.forall_mem_cons.2 ⟨subd10_1_734, List.forall_mem_cons.2 ⟨subd10_1_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_736 : subd10_1 [0, 2, 4] = true := by decide +kernel
theorem subd10_1_737 : subd10_1 [0, 2, 5] = true := by decide +kernel
theorem subd10_1_738 : subd10_1 [0, 2, 6] = true := by decide +kernel
theorem subd10_1_739 : subd10_1 [0, 2, 7] = true := by decide +kernel
theorem subd10_1_740 : subd10_1 [0, 3, -9] = true := by decide +kernel
theorem subd10_1_741 : subd10_1 [0, 3, -8] = true := by decide +kernel
theorem subd10_1_742 : subd10_1 [0, 3, -7] = true := by decide +kernel
theorem subd10_1_743 : subd10_1 [0, 3, -6] = true := by decide +kernel
theorem subd10_1_744 : subd10_1 [0, 3, -5] = true := by decide +kernel
theorem subd10_1_745 : subd10_1 [0, 3, -4] = true := by decide +kernel
theorem subd10_1_746 : subd10_1 [0, 3, -3] = true := by decide +kernel
theorem subd10_1_747 : subd10_1 [0, 3, -2] = true := by decide +kernel
theorem subd10_1_748 : subd10_1 [0, 3, -1] = true := by decide +kernel
theorem subd10_1_749 : subd10_1 [0, 3, 0] = true := by decide +kernel
theorem subd10_1_750 : subd10_1 [0, 3, 1] = true := by decide +kernel
theorem subd10_1_751 : subd10_1 [0, 3, 2] = true := by decide +kernel
theorem subd10_1_752 : subd10_1 [0, 3, 3] = true := by decide +kernel
theorem subd10_1_753 : subd10_1 [0, 3, 4] = true := by decide +kernel
theorem subd10_1_754 : subd10_1 [0, 3, 5] = true := by decide +kernel
theorem subd10_1_755 : subd10_1 [0, 3, 6] = true := by decide +kernel
theorem subd10_1_756 : subd10_1 [0, 3, 7] = true := by decide +kernel
theorem subd10_1_757 : subd10_1 [0, 4, -8] = true := by decide +kernel
theorem subd10_1_758 : subd10_1 [0, 4, -7] = true := by decide +kernel
theorem subd10_1_759 : subd10_1 [0, 4, -6] = true := by decide +kernel
theorem subd10_1_760 : subd10_1 [0, 4, -5] = true := by decide +kernel
theorem subd10_1_761 : subd10_1 [0, 4, -4] = true := by decide +kernel
theorem subd10_1_762 : subd10_1 [0, 4, -3] = true := by decide +kernel
theorem subd10_1_763 : subd10_1 [0, 4, -2] = true := by decide +kernel
theorem subd10_1_764 : subd10_1 [0, 4, -1] = true := by decide +kernel
theorem subd10_1_765 : subd10_1 [0, 4, 0] = true := by decide +kernel
theorem subd10_1_766 : subd10_1 [0, 4, 1] = true := by decide +kernel
theorem subd10_1_767 : subd10_1 [0, 4, 2] = true := by decide +kernel
theorem sbd10_1_23 : ∀ q ∈ blkd10_1_23, subd10_1 q = true := by
  unfold blkd10_1_23
  exact List.forall_mem_cons.2 ⟨subd10_1_736, List.forall_mem_cons.2 ⟨subd10_1_737, List.forall_mem_cons.2 ⟨subd10_1_738, List.forall_mem_cons.2 ⟨subd10_1_739, List.forall_mem_cons.2 ⟨subd10_1_740, List.forall_mem_cons.2 ⟨subd10_1_741, List.forall_mem_cons.2 ⟨subd10_1_742, List.forall_mem_cons.2 ⟨subd10_1_743, List.forall_mem_cons.2 ⟨subd10_1_744, List.forall_mem_cons.2 ⟨subd10_1_745, List.forall_mem_cons.2 ⟨subd10_1_746, List.forall_mem_cons.2 ⟨subd10_1_747, List.forall_mem_cons.2 ⟨subd10_1_748, List.forall_mem_cons.2 ⟨subd10_1_749, List.forall_mem_cons.2 ⟨subd10_1_750, List.forall_mem_cons.2 ⟨subd10_1_751, List.forall_mem_cons.2 ⟨subd10_1_752, List.forall_mem_cons.2 ⟨subd10_1_753, List.forall_mem_cons.2 ⟨subd10_1_754, List.forall_mem_cons.2 ⟨subd10_1_755, List.forall_mem_cons.2 ⟨subd10_1_756, List.forall_mem_cons.2 ⟨subd10_1_757, List.forall_mem_cons.2 ⟨subd10_1_758, List.forall_mem_cons.2 ⟨subd10_1_759, List.forall_mem_cons.2 ⟨subd10_1_760, List.forall_mem_cons.2 ⟨subd10_1_761, List.forall_mem_cons.2 ⟨subd10_1_762, List.forall_mem_cons.2 ⟨subd10_1_763, List.forall_mem_cons.2 ⟨subd10_1_764, List.forall_mem_cons.2 ⟨subd10_1_765, List.forall_mem_cons.2 ⟨subd10_1_766, List.forall_mem_cons.2 ⟨subd10_1_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_768 : subd10_1 [0, 4, 3] = true := by decide +kernel
theorem subd10_1_769 : subd10_1 [0, 4, 4] = true := by decide +kernel
theorem subd10_1_770 : subd10_1 [0, 4, 5] = true := by decide +kernel
theorem subd10_1_771 : subd10_1 [0, 4, 6] = true := by decide +kernel
theorem subd10_1_772 : subd10_1 [0, 5, -8] = true := by decide +kernel
theorem subd10_1_773 : subd10_1 [0, 5, -7] = true := by decide +kernel
theorem subd10_1_774 : subd10_1 [0, 5, -6] = true := by decide +kernel
theorem subd10_1_775 : subd10_1 [0, 5, -5] = true := by decide +kernel
theorem subd10_1_776 : subd10_1 [0, 5, -4] = true := by decide +kernel
theorem subd10_1_777 : subd10_1 [0, 5, -3] = true := by decide +kernel
theorem subd10_1_778 : subd10_1 [0, 5, -2] = true := by decide +kernel
theorem subd10_1_779 : subd10_1 [0, 5, -1] = true := by decide +kernel
theorem subd10_1_780 : subd10_1 [0, 5, 0] = true := by decide +kernel
theorem subd10_1_781 : subd10_1 [0, 5, 1] = true := by decide +kernel
theorem subd10_1_782 : subd10_1 [0, 5, 2] = true := by decide +kernel
theorem subd10_1_783 : subd10_1 [0, 5, 3] = true := by decide +kernel
theorem subd10_1_784 : subd10_1 [0, 5, 4] = true := by decide +kernel
theorem subd10_1_785 : subd10_1 [0, 5, 5] = true := by decide +kernel
theorem subd10_1_786 : subd10_1 [0, 6] = true := by decide +kernel
theorem subd10_1_787 : subd10_1 [0, 7] = true := by decide +kernel
theorem subd10_1_788 : subd10_1 [0, 8] = true := by decide +kernel
theorem subd10_1_789 : subd10_1 [1, -9] = true := by decide +kernel
theorem subd10_1_790 : subd10_1 [1, -8] = true := by decide +kernel
theorem subd10_1_791 : subd10_1 [1, -7] = true := by decide +kernel
theorem subd10_1_792 : subd10_1 [1, -6] = true := by decide +kernel
theorem subd10_1_793 : subd10_1 [1, -5, -7] = true := by decide +kernel
theorem subd10_1_794 : subd10_1 [1, -5, -6] = true := by decide +kernel
theorem subd10_1_795 : subd10_1 [1, -5, -5] = true := by decide +kernel
theorem subd10_1_796 : subd10_1 [1, -5, -4] = true := by decide +kernel
theorem subd10_1_797 : subd10_1 [1, -5, -3] = true := by decide +kernel
theorem subd10_1_798 : subd10_1 [1, -5, -2] = true := by decide +kernel
theorem subd10_1_799 : subd10_1 [1, -5, -1] = true := by decide +kernel
theorem sbd10_1_24 : ∀ q ∈ blkd10_1_24, subd10_1 q = true := by
  unfold blkd10_1_24
  exact List.forall_mem_cons.2 ⟨subd10_1_768, List.forall_mem_cons.2 ⟨subd10_1_769, List.forall_mem_cons.2 ⟨subd10_1_770, List.forall_mem_cons.2 ⟨subd10_1_771, List.forall_mem_cons.2 ⟨subd10_1_772, List.forall_mem_cons.2 ⟨subd10_1_773, List.forall_mem_cons.2 ⟨subd10_1_774, List.forall_mem_cons.2 ⟨subd10_1_775, List.forall_mem_cons.2 ⟨subd10_1_776, List.forall_mem_cons.2 ⟨subd10_1_777, List.forall_mem_cons.2 ⟨subd10_1_778, List.forall_mem_cons.2 ⟨subd10_1_779, List.forall_mem_cons.2 ⟨subd10_1_780, List.forall_mem_cons.2 ⟨subd10_1_781, List.forall_mem_cons.2 ⟨subd10_1_782, List.forall_mem_cons.2 ⟨subd10_1_783, List.forall_mem_cons.2 ⟨subd10_1_784, List.forall_mem_cons.2 ⟨subd10_1_785, List.forall_mem_cons.2 ⟨subd10_1_786, List.forall_mem_cons.2 ⟨subd10_1_787, List.forall_mem_cons.2 ⟨subd10_1_788, List.forall_mem_cons.2 ⟨subd10_1_789, List.forall_mem_cons.2 ⟨subd10_1_790, List.forall_mem_cons.2 ⟨subd10_1_791, List.forall_mem_cons.2 ⟨subd10_1_792, List.forall_mem_cons.2 ⟨subd10_1_793, List.forall_mem_cons.2 ⟨subd10_1_794, List.forall_mem_cons.2 ⟨subd10_1_795, List.forall_mem_cons.2 ⟨subd10_1_796, List.forall_mem_cons.2 ⟨subd10_1_797, List.forall_mem_cons.2 ⟨subd10_1_798, List.forall_mem_cons.2 ⟨subd10_1_799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_800 : subd10_1 [1, -5, 0] = true := by decide +kernel
theorem subd10_1_801 : subd10_1 [1, -5, 1] = true := by decide +kernel
theorem subd10_1_802 : subd10_1 [1, -5, 2] = true := by decide +kernel
theorem subd10_1_803 : subd10_1 [1, -5, 3] = true := by decide +kernel
theorem subd10_1_804 : subd10_1 [1, -5, 4] = true := by decide +kernel
theorem subd10_1_805 : subd10_1 [1, -5, 5] = true := by decide +kernel
theorem subd10_1_806 : subd10_1 [1, -5, 6] = true := by decide +kernel
theorem subd10_1_807 : subd10_1 [1, -5, 7] = true := by decide +kernel
theorem subd10_1_808 : subd10_1 [1, -4, -7] = true := by decide +kernel
theorem subd10_1_809 : subd10_1 [1, -4, -6] = true := by decide +kernel
theorem subd10_1_810 : subd10_1 [1, -4, -5] = true := by decide +kernel
theorem subd10_1_811 : subd10_1 [1, -4, -4] = true := by decide +kernel
theorem subd10_1_812 : subd10_1 [1, -4, -3] = true := by decide +kernel
theorem subd10_1_813 : subd10_1 [1, -4, -2] = true := by decide +kernel
theorem subd10_1_814 : subd10_1 [1, -4, -1] = true := by decide +kernel
theorem subd10_1_815 : subd10_1 [1, -4, 0] = true := by decide +kernel
theorem subd10_1_816 : subd10_1 [1, -4, 1] = true := by decide +kernel
theorem subd10_1_817 : subd10_1 [1, -4, 2] = true := by decide +kernel
theorem subd10_1_818 : subd10_1 [1, -4, 3] = true := by decide +kernel
theorem subd10_1_819 : subd10_1 [1, -4, 4] = true := by decide +kernel
theorem subd10_1_820 : subd10_1 [1, -4, 5] = true := by decide +kernel
theorem subd10_1_821 : subd10_1 [1, -4, 6] = true := by decide +kernel
theorem subd10_1_822 : subd10_1 [1, -4, 7] = true := by decide +kernel
theorem subd10_1_823 : subd10_1 [1, -3, -8] = true := by decide +kernel
theorem subd10_1_824 : subd10_1 [1, -3, -7] = true := by decide +kernel
theorem subd10_1_825 : subd10_1 [1, -3, -6] = true := by decide +kernel
theorem subd10_1_826 : subd10_1 [1, -3, -5] = true := by decide +kernel
theorem subd10_1_827 : subd10_1 [1, -3, -4] = true := by decide +kernel
theorem subd10_1_828 : subd10_1 [1, -3, -3] = true := by decide +kernel
theorem subd10_1_829 : subd10_1 [1, -3, -2] = true := by decide +kernel
theorem subd10_1_830 : subd10_1 [1, -3, -1] = true := by decide +kernel
theorem subd10_1_831 : subd10_1 [1, -3, 0] = true := by decide +kernel
theorem sbd10_1_25 : ∀ q ∈ blkd10_1_25, subd10_1 q = true := by
  unfold blkd10_1_25
  exact List.forall_mem_cons.2 ⟨subd10_1_800, List.forall_mem_cons.2 ⟨subd10_1_801, List.forall_mem_cons.2 ⟨subd10_1_802, List.forall_mem_cons.2 ⟨subd10_1_803, List.forall_mem_cons.2 ⟨subd10_1_804, List.forall_mem_cons.2 ⟨subd10_1_805, List.forall_mem_cons.2 ⟨subd10_1_806, List.forall_mem_cons.2 ⟨subd10_1_807, List.forall_mem_cons.2 ⟨subd10_1_808, List.forall_mem_cons.2 ⟨subd10_1_809, List.forall_mem_cons.2 ⟨subd10_1_810, List.forall_mem_cons.2 ⟨subd10_1_811, List.forall_mem_cons.2 ⟨subd10_1_812, List.forall_mem_cons.2 ⟨subd10_1_813, List.forall_mem_cons.2 ⟨subd10_1_814, List.forall_mem_cons.2 ⟨subd10_1_815, List.forall_mem_cons.2 ⟨subd10_1_816, List.forall_mem_cons.2 ⟨subd10_1_817, List.forall_mem_cons.2 ⟨subd10_1_818, List.forall_mem_cons.2 ⟨subd10_1_819, List.forall_mem_cons.2 ⟨subd10_1_820, List.forall_mem_cons.2 ⟨subd10_1_821, List.forall_mem_cons.2 ⟨subd10_1_822, List.forall_mem_cons.2 ⟨subd10_1_823, List.forall_mem_cons.2 ⟨subd10_1_824, List.forall_mem_cons.2 ⟨subd10_1_825, List.forall_mem_cons.2 ⟨subd10_1_826, List.forall_mem_cons.2 ⟨subd10_1_827, List.forall_mem_cons.2 ⟨subd10_1_828, List.forall_mem_cons.2 ⟨subd10_1_829, List.forall_mem_cons.2 ⟨subd10_1_830, List.forall_mem_cons.2 ⟨subd10_1_831, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_832 : subd10_1 [1, -3, 1] = true := by decide +kernel
theorem subd10_1_833 : subd10_1 [1, -3, 2] = true := by decide +kernel
theorem subd10_1_834 : subd10_1 [1, -3, 3] = true := by decide +kernel
theorem subd10_1_835 : subd10_1 [1, -3, 4] = true := by decide +kernel
theorem subd10_1_836 : subd10_1 [1, -3, 5] = true := by decide +kernel
theorem subd10_1_837 : subd10_1 [1, -3, 6] = true := by decide +kernel
theorem subd10_1_838 : subd10_1 [1, -3, 7] = true := by decide +kernel
theorem subd10_1_839 : subd10_1 [1, -2, -8] = true := by decide +kernel
theorem subd10_1_840 : subd10_1 [1, -2, -7] = true := by decide +kernel
theorem subd10_1_841 : subd10_1 [1, -2, -6] = true := by decide +kernel
theorem subd10_1_842 : subd10_1 [1, -2, -5] = true := by decide +kernel
theorem subd10_1_843 : subd10_1 [1, -2, -4] = true := by decide +kernel
theorem subd10_1_844 : subd10_1 [1, -2, -3] = true := by decide +kernel
theorem subd10_1_845 : subd10_1 [1, -2, -2] = true := by decide +kernel
theorem subd10_1_846 : subd10_1 [1, -2, -1] = true := by decide +kernel
theorem subd10_1_847 : subd10_1 [1, -2, 0] = true := by decide +kernel
theorem subd10_1_848 : subd10_1 [1, -2, 1] = true := by decide +kernel
theorem subd10_1_849 : subd10_1 [1, -2, 2] = true := by decide +kernel
theorem subd10_1_850 : subd10_1 [1, -2, 3] = true := by decide +kernel
theorem subd10_1_851 : subd10_1 [1, -2, 4] = true := by decide +kernel
theorem subd10_1_852 : subd10_1 [1, -2, 5] = true := by decide +kernel
theorem subd10_1_853 : subd10_1 [1, -2, 6] = true := by decide +kernel
theorem subd10_1_854 : subd10_1 [1, -2, 7] = true := by decide +kernel
theorem subd10_1_855 : subd10_1 [1, -2, 8] = true := by decide +kernel
theorem subd10_1_856 : subd10_1 [1, -1, -8] = true := by decide +kernel
theorem subd10_1_857 : subd10_1 [1, -1, -7] = true := by decide +kernel
theorem subd10_1_858 : subd10_1 [1, -1, -6] = true := by decide +kernel
theorem subd10_1_859 : subd10_1 [1, -1, -5] = true := by decide +kernel
theorem subd10_1_860 : subd10_1 [1, -1, -4] = true := by decide +kernel
theorem subd10_1_861 : subd10_1 [1, -1, -3] = true := by decide +kernel
theorem subd10_1_862 : subd10_1 [1, -1, -2] = true := by decide +kernel
theorem subd10_1_863 : subd10_1 [1, -1, -1] = true := by decide +kernel
theorem sbd10_1_26 : ∀ q ∈ blkd10_1_26, subd10_1 q = true := by
  unfold blkd10_1_26
  exact List.forall_mem_cons.2 ⟨subd10_1_832, List.forall_mem_cons.2 ⟨subd10_1_833, List.forall_mem_cons.2 ⟨subd10_1_834, List.forall_mem_cons.2 ⟨subd10_1_835, List.forall_mem_cons.2 ⟨subd10_1_836, List.forall_mem_cons.2 ⟨subd10_1_837, List.forall_mem_cons.2 ⟨subd10_1_838, List.forall_mem_cons.2 ⟨subd10_1_839, List.forall_mem_cons.2 ⟨subd10_1_840, List.forall_mem_cons.2 ⟨subd10_1_841, List.forall_mem_cons.2 ⟨subd10_1_842, List.forall_mem_cons.2 ⟨subd10_1_843, List.forall_mem_cons.2 ⟨subd10_1_844, List.forall_mem_cons.2 ⟨subd10_1_845, List.forall_mem_cons.2 ⟨subd10_1_846, List.forall_mem_cons.2 ⟨subd10_1_847, List.forall_mem_cons.2 ⟨subd10_1_848, List.forall_mem_cons.2 ⟨subd10_1_849, List.forall_mem_cons.2 ⟨subd10_1_850, List.forall_mem_cons.2 ⟨subd10_1_851, List.forall_mem_cons.2 ⟨subd10_1_852, List.forall_mem_cons.2 ⟨subd10_1_853, List.forall_mem_cons.2 ⟨subd10_1_854, List.forall_mem_cons.2 ⟨subd10_1_855, List.forall_mem_cons.2 ⟨subd10_1_856, List.forall_mem_cons.2 ⟨subd10_1_857, List.forall_mem_cons.2 ⟨subd10_1_858, List.forall_mem_cons.2 ⟨subd10_1_859, List.forall_mem_cons.2 ⟨subd10_1_860, List.forall_mem_cons.2 ⟨subd10_1_861, List.forall_mem_cons.2 ⟨subd10_1_862, List.forall_mem_cons.2 ⟨subd10_1_863, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_864 : subd10_1 [1, -1, 0] = true := by decide +kernel
theorem subd10_1_865 : subd10_1 [1, -1, 1] = true := by decide +kernel
theorem subd10_1_866 : subd10_1 [1, -1, 2] = true := by decide +kernel
theorem subd10_1_867 : subd10_1 [1, -1, 3] = true := by decide +kernel
theorem subd10_1_868 : subd10_1 [1, -1, 4] = true := by decide +kernel
theorem subd10_1_869 : subd10_1 [1, -1, 5] = true := by decide +kernel
theorem subd10_1_870 : subd10_1 [1, -1, 6] = true := by decide +kernel
theorem subd10_1_871 : subd10_1 [1, -1, 7] = true := by decide +kernel
theorem subd10_1_872 : subd10_1 [1, 0, -9] = true := by decide +kernel
theorem subd10_1_873 : subd10_1 [1, 0, -8] = true := by decide +kernel
theorem subd10_1_874 : subd10_1 [1, 0, -7] = true := by decide +kernel
theorem subd10_1_875 : subd10_1 [1, 0, -6] = true := by decide +kernel
theorem subd10_1_876 : subd10_1 [1, 0, -5] = true := by decide +kernel
theorem subd10_1_877 : subd10_1 [1, 0, -4] = true := by decide +kernel
theorem subd10_1_878 : subd10_1 [1, 0, -3] = true := by decide +kernel
theorem subd10_1_879 : subd10_1 [1, 0, -2] = true := by decide +kernel
theorem subd10_1_880 : subd10_1 [1, 0, -1] = true := by decide +kernel
theorem subd10_1_881 : subd10_1 [1, 0, 0] = true := by decide +kernel
theorem subd10_1_882 : subd10_1 [1, 0, 1] = true := by decide +kernel
theorem subd10_1_883 : subd10_1 [1, 0, 2] = true := by decide +kernel
theorem subd10_1_884 : subd10_1 [1, 0, 3] = true := by decide +kernel
theorem subd10_1_885 : subd10_1 [1, 0, 4] = true := by decide +kernel
theorem subd10_1_886 : subd10_1 [1, 0, 5] = true := by decide +kernel
theorem subd10_1_887 : subd10_1 [1, 0, 6] = true := by decide +kernel
theorem subd10_1_888 : subd10_1 [1, 0, 7] = true := by decide +kernel
theorem subd10_1_889 : subd10_1 [1, 1, -9] = true := by decide +kernel
theorem subd10_1_890 : subd10_1 [1, 1, -8] = true := by decide +kernel
theorem subd10_1_891 : subd10_1 [1, 1, -7] = true := by decide +kernel
theorem subd10_1_892 : subd10_1 [1, 1, -6] = true := by decide +kernel
theorem subd10_1_893 : subd10_1 [1, 1, -5] = true := by decide +kernel
theorem subd10_1_894 : subd10_1 [1, 1, -4] = true := by decide +kernel
theorem subd10_1_895 : subd10_1 [1, 1, -3] = true := by decide +kernel
theorem sbd10_1_27 : ∀ q ∈ blkd10_1_27, subd10_1 q = true := by
  unfold blkd10_1_27
  exact List.forall_mem_cons.2 ⟨subd10_1_864, List.forall_mem_cons.2 ⟨subd10_1_865, List.forall_mem_cons.2 ⟨subd10_1_866, List.forall_mem_cons.2 ⟨subd10_1_867, List.forall_mem_cons.2 ⟨subd10_1_868, List.forall_mem_cons.2 ⟨subd10_1_869, List.forall_mem_cons.2 ⟨subd10_1_870, List.forall_mem_cons.2 ⟨subd10_1_871, List.forall_mem_cons.2 ⟨subd10_1_872, List.forall_mem_cons.2 ⟨subd10_1_873, List.forall_mem_cons.2 ⟨subd10_1_874, List.forall_mem_cons.2 ⟨subd10_1_875, List.forall_mem_cons.2 ⟨subd10_1_876, List.forall_mem_cons.2 ⟨subd10_1_877, List.forall_mem_cons.2 ⟨subd10_1_878, List.forall_mem_cons.2 ⟨subd10_1_879, List.forall_mem_cons.2 ⟨subd10_1_880, List.forall_mem_cons.2 ⟨subd10_1_881, List.forall_mem_cons.2 ⟨subd10_1_882, List.forall_mem_cons.2 ⟨subd10_1_883, List.forall_mem_cons.2 ⟨subd10_1_884, List.forall_mem_cons.2 ⟨subd10_1_885, List.forall_mem_cons.2 ⟨subd10_1_886, List.forall_mem_cons.2 ⟨subd10_1_887, List.forall_mem_cons.2 ⟨subd10_1_888, List.forall_mem_cons.2 ⟨subd10_1_889, List.forall_mem_cons.2 ⟨subd10_1_890, List.forall_mem_cons.2 ⟨subd10_1_891, List.forall_mem_cons.2 ⟨subd10_1_892, List.forall_mem_cons.2 ⟨subd10_1_893, List.forall_mem_cons.2 ⟨subd10_1_894, List.forall_mem_cons.2 ⟨subd10_1_895, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_896 : subd10_1 [1, 1, -2] = true := by decide +kernel
theorem subd10_1_897 : subd10_1 [1, 1, -1] = true := by decide +kernel
theorem subd10_1_898 : subd10_1 [1, 1, 0] = true := by decide +kernel
theorem subd10_1_899 : subd10_1 [1, 1, 1] = true := by decide +kernel
theorem subd10_1_900 : subd10_1 [1, 1, 2] = true := by decide +kernel
theorem subd10_1_901 : subd10_1 [1, 1, 3] = true := by decide +kernel
theorem subd10_1_902 : subd10_1 [1, 1, 4] = true := by decide +kernel
theorem subd10_1_903 : subd10_1 [1, 1, 5] = true := by decide +kernel
theorem subd10_1_904 : subd10_1 [1, 1, 6] = true := by decide +kernel
theorem subd10_1_905 : subd10_1 [1, 1, 7] = true := by decide +kernel
theorem subd10_1_906 : subd10_1 [1, 2, -9] = true := by decide +kernel
theorem subd10_1_907 : subd10_1 [1, 2, -8] = true := by decide +kernel
theorem subd10_1_908 : subd10_1 [1, 2, -7] = true := by decide +kernel
theorem subd10_1_909 : subd10_1 [1, 2, -6] = true := by decide +kernel
theorem subd10_1_910 : subd10_1 [1, 2, -5] = true := by decide +kernel
theorem subd10_1_911 : subd10_1 [1, 2, -4] = true := by decide +kernel
theorem subd10_1_912 : subd10_1 [1, 2, -3] = true := by decide +kernel
theorem subd10_1_913 : subd10_1 [1, 2, -2] = true := by decide +kernel
theorem subd10_1_914 : subd10_1 [1, 2, -1] = true := by decide +kernel
theorem subd10_1_915 : subd10_1 [1, 2, 0] = true := by decide +kernel
theorem subd10_1_916 : subd10_1 [1, 2, 1] = true := by decide +kernel
theorem subd10_1_917 : subd10_1 [1, 2, 2] = true := by decide +kernel
theorem subd10_1_918 : subd10_1 [1, 2, 3] = true := by decide +kernel
theorem subd10_1_919 : subd10_1 [1, 2, 4] = true := by decide +kernel
theorem subd10_1_920 : subd10_1 [1, 2, 5] = true := by decide +kernel
theorem subd10_1_921 : subd10_1 [1, 2, 6] = true := by decide +kernel
theorem subd10_1_922 : subd10_1 [1, 2, 7] = true := by decide +kernel
theorem subd10_1_923 : subd10_1 [1, 3, -8] = true := by decide +kernel
theorem subd10_1_924 : subd10_1 [1, 3, -7] = true := by decide +kernel
theorem subd10_1_925 : subd10_1 [1, 3, -6] = true := by decide +kernel
theorem subd10_1_926 : subd10_1 [1, 3, -5] = true := by decide +kernel
theorem subd10_1_927 : subd10_1 [1, 3, -4] = true := by decide +kernel
theorem sbd10_1_28 : ∀ q ∈ blkd10_1_28, subd10_1 q = true := by
  unfold blkd10_1_28
  exact List.forall_mem_cons.2 ⟨subd10_1_896, List.forall_mem_cons.2 ⟨subd10_1_897, List.forall_mem_cons.2 ⟨subd10_1_898, List.forall_mem_cons.2 ⟨subd10_1_899, List.forall_mem_cons.2 ⟨subd10_1_900, List.forall_mem_cons.2 ⟨subd10_1_901, List.forall_mem_cons.2 ⟨subd10_1_902, List.forall_mem_cons.2 ⟨subd10_1_903, List.forall_mem_cons.2 ⟨subd10_1_904, List.forall_mem_cons.2 ⟨subd10_1_905, List.forall_mem_cons.2 ⟨subd10_1_906, List.forall_mem_cons.2 ⟨subd10_1_907, List.forall_mem_cons.2 ⟨subd10_1_908, List.forall_mem_cons.2 ⟨subd10_1_909, List.forall_mem_cons.2 ⟨subd10_1_910, List.forall_mem_cons.2 ⟨subd10_1_911, List.forall_mem_cons.2 ⟨subd10_1_912, List.forall_mem_cons.2 ⟨subd10_1_913, List.forall_mem_cons.2 ⟨subd10_1_914, List.forall_mem_cons.2 ⟨subd10_1_915, List.forall_mem_cons.2 ⟨subd10_1_916, List.forall_mem_cons.2 ⟨subd10_1_917, List.forall_mem_cons.2 ⟨subd10_1_918, List.forall_mem_cons.2 ⟨subd10_1_919, List.forall_mem_cons.2 ⟨subd10_1_920, List.forall_mem_cons.2 ⟨subd10_1_921, List.forall_mem_cons.2 ⟨subd10_1_922, List.forall_mem_cons.2 ⟨subd10_1_923, List.forall_mem_cons.2 ⟨subd10_1_924, List.forall_mem_cons.2 ⟨subd10_1_925, List.forall_mem_cons.2 ⟨subd10_1_926, List.forall_mem_cons.2 ⟨subd10_1_927, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_928 : subd10_1 [1, 3, -3] = true := by decide +kernel
theorem subd10_1_929 : subd10_1 [1, 3, -2] = true := by decide +kernel
theorem subd10_1_930 : subd10_1 [1, 3, -1] = true := by decide +kernel
theorem subd10_1_931 : subd10_1 [1, 3, 0] = true := by decide +kernel
theorem subd10_1_932 : subd10_1 [1, 3, 1] = true := by decide +kernel
theorem subd10_1_933 : subd10_1 [1, 3, 2] = true := by decide +kernel
theorem subd10_1_934 : subd10_1 [1, 3, 3] = true := by decide +kernel
theorem subd10_1_935 : subd10_1 [1, 3, 4] = true := by decide +kernel
theorem subd10_1_936 : subd10_1 [1, 3, 5] = true := by decide +kernel
theorem subd10_1_937 : subd10_1 [1, 3, 6] = true := by decide +kernel
theorem subd10_1_938 : subd10_1 [1, 4, -8] = true := by decide +kernel
theorem subd10_1_939 : subd10_1 [1, 4, -7] = true := by decide +kernel
theorem subd10_1_940 : subd10_1 [1, 4, -6] = true := by decide +kernel
theorem subd10_1_941 : subd10_1 [1, 4, -5] = true := by decide +kernel
theorem subd10_1_942 : subd10_1 [1, 4, -4] = true := by decide +kernel
theorem subd10_1_943 : subd10_1 [1, 4, -3] = true := by decide +kernel
theorem subd10_1_944 : subd10_1 [1, 4, -2] = true := by decide +kernel
theorem subd10_1_945 : subd10_1 [1, 4, -1] = true := by decide +kernel
theorem subd10_1_946 : subd10_1 [1, 4, 0] = true := by decide +kernel
theorem subd10_1_947 : subd10_1 [1, 4, 1] = true := by decide +kernel
theorem subd10_1_948 : subd10_1 [1, 4, 2] = true := by decide +kernel
theorem subd10_1_949 : subd10_1 [1, 4, 3] = true := by decide +kernel
theorem subd10_1_950 : subd10_1 [1, 4, 4] = true := by decide +kernel
theorem subd10_1_951 : subd10_1 [1, 4, 5] = true := by decide +kernel
theorem subd10_1_952 : subd10_1 [1, 5] = true := by decide +kernel
theorem subd10_1_953 : subd10_1 [1, 6] = true := by decide +kernel
theorem subd10_1_954 : subd10_1 [1, 7] = true := by decide +kernel
theorem subd10_1_955 : subd10_1 [1, 8] = true := by decide +kernel
theorem subd10_1_956 : subd10_1 [2, -10] = true := by decide +kernel
theorem subd10_1_957 : subd10_1 [2, -9] = true := by decide +kernel
theorem subd10_1_958 : subd10_1 [2, -8] = true := by decide +kernel
theorem subd10_1_959 : subd10_1 [2, -7] = true := by decide +kernel
theorem sbd10_1_29 : ∀ q ∈ blkd10_1_29, subd10_1 q = true := by
  unfold blkd10_1_29
  exact List.forall_mem_cons.2 ⟨subd10_1_928, List.forall_mem_cons.2 ⟨subd10_1_929, List.forall_mem_cons.2 ⟨subd10_1_930, List.forall_mem_cons.2 ⟨subd10_1_931, List.forall_mem_cons.2 ⟨subd10_1_932, List.forall_mem_cons.2 ⟨subd10_1_933, List.forall_mem_cons.2 ⟨subd10_1_934, List.forall_mem_cons.2 ⟨subd10_1_935, List.forall_mem_cons.2 ⟨subd10_1_936, List.forall_mem_cons.2 ⟨subd10_1_937, List.forall_mem_cons.2 ⟨subd10_1_938, List.forall_mem_cons.2 ⟨subd10_1_939, List.forall_mem_cons.2 ⟨subd10_1_940, List.forall_mem_cons.2 ⟨subd10_1_941, List.forall_mem_cons.2 ⟨subd10_1_942, List.forall_mem_cons.2 ⟨subd10_1_943, List.forall_mem_cons.2 ⟨subd10_1_944, List.forall_mem_cons.2 ⟨subd10_1_945, List.forall_mem_cons.2 ⟨subd10_1_946, List.forall_mem_cons.2 ⟨subd10_1_947, List.forall_mem_cons.2 ⟨subd10_1_948, List.forall_mem_cons.2 ⟨subd10_1_949, List.forall_mem_cons.2 ⟨subd10_1_950, List.forall_mem_cons.2 ⟨subd10_1_951, List.forall_mem_cons.2 ⟨subd10_1_952, List.forall_mem_cons.2 ⟨subd10_1_953, List.forall_mem_cons.2 ⟨subd10_1_954, List.forall_mem_cons.2 ⟨subd10_1_955, List.forall_mem_cons.2 ⟨subd10_1_956, List.forall_mem_cons.2 ⟨subd10_1_957, List.forall_mem_cons.2 ⟨subd10_1_958, List.forall_mem_cons.2 ⟨subd10_1_959, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_960 : subd10_1 [2, -6] = true := by decide +kernel
theorem subd10_1_961 : subd10_1 [2, -5, -7] = true := by decide +kernel
theorem subd10_1_962 : subd10_1 [2, -5, -6] = true := by decide +kernel
theorem subd10_1_963 : subd10_1 [2, -5, -5] = true := by decide +kernel
theorem subd10_1_964 : subd10_1 [2, -5, -4] = true := by decide +kernel
theorem subd10_1_965 : subd10_1 [2, -5, -3] = true := by decide +kernel
theorem subd10_1_966 : subd10_1 [2, -5, -2] = true := by decide +kernel
theorem subd10_1_967 : subd10_1 [2, -5, -1] = true := by decide +kernel
theorem subd10_1_968 : subd10_1 [2, -5, 0] = true := by decide +kernel
theorem subd10_1_969 : subd10_1 [2, -5, 1] = true := by decide +kernel
theorem subd10_1_970 : subd10_1 [2, -5, 2] = true := by decide +kernel
theorem subd10_1_971 : subd10_1 [2, -5, 3] = true := by decide +kernel
theorem subd10_1_972 : subd10_1 [2, -5, 4] = true := by decide +kernel
theorem subd10_1_973 : subd10_1 [2, -5, 5] = true := by decide +kernel
theorem subd10_1_974 : subd10_1 [2, -5, 6] = true := by decide +kernel
theorem subd10_1_975 : subd10_1 [2, -5, 7] = true := by decide +kernel
theorem subd10_1_976 : subd10_1 [2, -4, -7] = true := by decide +kernel
theorem subd10_1_977 : subd10_1 [2, -4, -6] = true := by decide +kernel
theorem subd10_1_978 : subd10_1 [2, -4, -5] = true := by decide +kernel
theorem subd10_1_979 : subd10_1 [2, -4, -4] = true := by decide +kernel
theorem subd10_1_980 : subd10_1 [2, -4, -3] = true := by decide +kernel
theorem subd10_1_981 : subd10_1 [2, -4, -2] = true := by decide +kernel
theorem subd10_1_982 : subd10_1 [2, -4, -1] = true := by decide +kernel
theorem subd10_1_983 : subd10_1 [2, -4, 0] = true := by decide +kernel
theorem subd10_1_984 : subd10_1 [2, -4, 1] = true := by decide +kernel
theorem subd10_1_985 : subd10_1 [2, -4, 2] = true := by decide +kernel
theorem subd10_1_986 : subd10_1 [2, -4, 3] = true := by decide +kernel
theorem subd10_1_987 : subd10_1 [2, -4, 4] = true := by decide +kernel
theorem subd10_1_988 : subd10_1 [2, -4, 5] = true := by decide +kernel
theorem subd10_1_989 : subd10_1 [2, -4, 6] = true := by decide +kernel
theorem subd10_1_990 : subd10_1 [2, -4, 7] = true := by decide +kernel
theorem subd10_1_991 : subd10_1 [2, -3, -8] = true := by decide +kernel
theorem sbd10_1_30 : ∀ q ∈ blkd10_1_30, subd10_1 q = true := by
  unfold blkd10_1_30
  exact List.forall_mem_cons.2 ⟨subd10_1_960, List.forall_mem_cons.2 ⟨subd10_1_961, List.forall_mem_cons.2 ⟨subd10_1_962, List.forall_mem_cons.2 ⟨subd10_1_963, List.forall_mem_cons.2 ⟨subd10_1_964, List.forall_mem_cons.2 ⟨subd10_1_965, List.forall_mem_cons.2 ⟨subd10_1_966, List.forall_mem_cons.2 ⟨subd10_1_967, List.forall_mem_cons.2 ⟨subd10_1_968, List.forall_mem_cons.2 ⟨subd10_1_969, List.forall_mem_cons.2 ⟨subd10_1_970, List.forall_mem_cons.2 ⟨subd10_1_971, List.forall_mem_cons.2 ⟨subd10_1_972, List.forall_mem_cons.2 ⟨subd10_1_973, List.forall_mem_cons.2 ⟨subd10_1_974, List.forall_mem_cons.2 ⟨subd10_1_975, List.forall_mem_cons.2 ⟨subd10_1_976, List.forall_mem_cons.2 ⟨subd10_1_977, List.forall_mem_cons.2 ⟨subd10_1_978, List.forall_mem_cons.2 ⟨subd10_1_979, List.forall_mem_cons.2 ⟨subd10_1_980, List.forall_mem_cons.2 ⟨subd10_1_981, List.forall_mem_cons.2 ⟨subd10_1_982, List.forall_mem_cons.2 ⟨subd10_1_983, List.forall_mem_cons.2 ⟨subd10_1_984, List.forall_mem_cons.2 ⟨subd10_1_985, List.forall_mem_cons.2 ⟨subd10_1_986, List.forall_mem_cons.2 ⟨subd10_1_987, List.forall_mem_cons.2 ⟨subd10_1_988, List.forall_mem_cons.2 ⟨subd10_1_989, List.forall_mem_cons.2 ⟨subd10_1_990, List.forall_mem_cons.2 ⟨subd10_1_991, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_992 : subd10_1 [2, -3, -7] = true := by decide +kernel
theorem subd10_1_993 : subd10_1 [2, -3, -6] = true := by decide +kernel
theorem subd10_1_994 : subd10_1 [2, -3, -5] = true := by decide +kernel
theorem subd10_1_995 : subd10_1 [2, -3, -4] = true := by decide +kernel
theorem subd10_1_996 : subd10_1 [2, -3, -3] = true := by decide +kernel
theorem subd10_1_997 : subd10_1 [2, -3, -2] = true := by decide +kernel
theorem subd10_1_998 : subd10_1 [2, -3, -1] = true := by decide +kernel
theorem subd10_1_999 : subd10_1 [2, -3, 0] = true := by decide +kernel
theorem subd10_1_1000 : subd10_1 [2, -3, 1] = true := by decide +kernel
theorem subd10_1_1001 : subd10_1 [2, -3, 2] = true := by decide +kernel
theorem subd10_1_1002 : subd10_1 [2, -3, 3] = true := by decide +kernel
theorem subd10_1_1003 : subd10_1 [2, -3, 4] = true := by decide +kernel
theorem subd10_1_1004 : subd10_1 [2, -3, 5] = true := by decide +kernel
theorem subd10_1_1005 : subd10_1 [2, -3, 6] = true := by decide +kernel
theorem subd10_1_1006 : subd10_1 [2, -3, 7] = true := by decide +kernel
theorem subd10_1_1007 : subd10_1 [2, -2, -8] = true := by decide +kernel
theorem subd10_1_1008 : subd10_1 [2, -2, -7] = true := by decide +kernel
theorem subd10_1_1009 : subd10_1 [2, -2, -6] = true := by decide +kernel
theorem subd10_1_1010 : subd10_1 [2, -2, -5] = true := by decide +kernel
theorem subd10_1_1011 : subd10_1 [2, -2, -4] = true := by decide +kernel
theorem subd10_1_1012 : subd10_1 [2, -2, -3] = true := by decide +kernel
theorem subd10_1_1013 : subd10_1 [2, -2, -2] = true := by decide +kernel
theorem subd10_1_1014 : subd10_1 [2, -2, -1] = true := by decide +kernel
theorem subd10_1_1015 : subd10_1 [2, -2, 0] = true := by decide +kernel
theorem subd10_1_1016 : subd10_1 [2, -2, 1] = true := by decide +kernel
theorem subd10_1_1017 : subd10_1 [2, -2, 2] = true := by decide +kernel
theorem subd10_1_1018 : subd10_1 [2, -2, 3] = true := by decide +kernel
theorem subd10_1_1019 : subd10_1 [2, -2, 4] = true := by decide +kernel
theorem subd10_1_1020 : subd10_1 [2, -2, 5] = true := by decide +kernel
theorem subd10_1_1021 : subd10_1 [2, -2, 6] = true := by decide +kernel
theorem subd10_1_1022 : subd10_1 [2, -2, 7] = true := by decide +kernel
theorem subd10_1_1023 : subd10_1 [2, -1, -8] = true := by decide +kernel
theorem sbd10_1_31 : ∀ q ∈ blkd10_1_31, subd10_1 q = true := by
  unfold blkd10_1_31
  exact List.forall_mem_cons.2 ⟨subd10_1_992, List.forall_mem_cons.2 ⟨subd10_1_993, List.forall_mem_cons.2 ⟨subd10_1_994, List.forall_mem_cons.2 ⟨subd10_1_995, List.forall_mem_cons.2 ⟨subd10_1_996, List.forall_mem_cons.2 ⟨subd10_1_997, List.forall_mem_cons.2 ⟨subd10_1_998, List.forall_mem_cons.2 ⟨subd10_1_999, List.forall_mem_cons.2 ⟨subd10_1_1000, List.forall_mem_cons.2 ⟨subd10_1_1001, List.forall_mem_cons.2 ⟨subd10_1_1002, List.forall_mem_cons.2 ⟨subd10_1_1003, List.forall_mem_cons.2 ⟨subd10_1_1004, List.forall_mem_cons.2 ⟨subd10_1_1005, List.forall_mem_cons.2 ⟨subd10_1_1006, List.forall_mem_cons.2 ⟨subd10_1_1007, List.forall_mem_cons.2 ⟨subd10_1_1008, List.forall_mem_cons.2 ⟨subd10_1_1009, List.forall_mem_cons.2 ⟨subd10_1_1010, List.forall_mem_cons.2 ⟨subd10_1_1011, List.forall_mem_cons.2 ⟨subd10_1_1012, List.forall_mem_cons.2 ⟨subd10_1_1013, List.forall_mem_cons.2 ⟨subd10_1_1014, List.forall_mem_cons.2 ⟨subd10_1_1015, List.forall_mem_cons.2 ⟨subd10_1_1016, List.forall_mem_cons.2 ⟨subd10_1_1017, List.forall_mem_cons.2 ⟨subd10_1_1018, List.forall_mem_cons.2 ⟨subd10_1_1019, List.forall_mem_cons.2 ⟨subd10_1_1020, List.forall_mem_cons.2 ⟨subd10_1_1021, List.forall_mem_cons.2 ⟨subd10_1_1022, List.forall_mem_cons.2 ⟨subd10_1_1023, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_1024 : subd10_1 [2, -1, -7] = true := by decide +kernel
theorem subd10_1_1025 : subd10_1 [2, -1, -6] = true := by decide +kernel
theorem subd10_1_1026 : subd10_1 [2, -1, -5] = true := by decide +kernel
theorem subd10_1_1027 : subd10_1 [2, -1, -4] = true := by decide +kernel
theorem subd10_1_1028 : subd10_1 [2, -1, -3] = true := by decide +kernel
theorem subd10_1_1029 : subd10_1 [2, -1, -2] = true := by decide +kernel
theorem subd10_1_1030 : subd10_1 [2, -1, -1] = true := by decide +kernel
theorem subd10_1_1031 : subd10_1 [2, -1, 0] = true := by decide +kernel
theorem subd10_1_1032 : subd10_1 [2, -1, 1] = true := by decide +kernel
theorem subd10_1_1033 : subd10_1 [2, -1, 2] = true := by decide +kernel
theorem subd10_1_1034 : subd10_1 [2, -1, 3] = true := by decide +kernel
theorem subd10_1_1035 : subd10_1 [2, -1, 4] = true := by decide +kernel
theorem subd10_1_1036 : subd10_1 [2, -1, 5] = true := by decide +kernel
theorem subd10_1_1037 : subd10_1 [2, -1, 6] = true := by decide +kernel
theorem subd10_1_1038 : subd10_1 [2, -1, 7] = true := by decide +kernel
theorem subd10_1_1039 : subd10_1 [2, 0, -9] = true := by decide +kernel
theorem subd10_1_1040 : subd10_1 [2, 0, -8] = true := by decide +kernel
theorem subd10_1_1041 : subd10_1 [2, 0, -7] = true := by decide +kernel
theorem subd10_1_1042 : subd10_1 [2, 0, -6] = true := by decide +kernel
theorem subd10_1_1043 : subd10_1 [2, 0, -5] = true := by decide +kernel
theorem subd10_1_1044 : subd10_1 [2, 0, -4] = true := by decide +kernel
theorem subd10_1_1045 : subd10_1 [2, 0, -3] = true := by decide +kernel
theorem subd10_1_1046 : subd10_1 [2, 0, -2] = true := by decide +kernel
theorem subd10_1_1047 : subd10_1 [2, 0, -1] = true := by decide +kernel
theorem subd10_1_1048 : subd10_1 [2, 0, 0] = true := by decide +kernel
theorem subd10_1_1049 : subd10_1 [2, 0, 1] = true := by decide +kernel
theorem subd10_1_1050 : subd10_1 [2, 0, 2] = true := by decide +kernel
theorem subd10_1_1051 : subd10_1 [2, 0, 3] = true := by decide +kernel
theorem subd10_1_1052 : subd10_1 [2, 0, 4] = true := by decide +kernel
theorem subd10_1_1053 : subd10_1 [2, 0, 5] = true := by decide +kernel
theorem subd10_1_1054 : subd10_1 [2, 0, 6] = true := by decide +kernel
theorem subd10_1_1055 : subd10_1 [2, 0, 7] = true := by decide +kernel
theorem sbd10_1_32 : ∀ q ∈ blkd10_1_32, subd10_1 q = true := by
  unfold blkd10_1_32
  exact List.forall_mem_cons.2 ⟨subd10_1_1024, List.forall_mem_cons.2 ⟨subd10_1_1025, List.forall_mem_cons.2 ⟨subd10_1_1026, List.forall_mem_cons.2 ⟨subd10_1_1027, List.forall_mem_cons.2 ⟨subd10_1_1028, List.forall_mem_cons.2 ⟨subd10_1_1029, List.forall_mem_cons.2 ⟨subd10_1_1030, List.forall_mem_cons.2 ⟨subd10_1_1031, List.forall_mem_cons.2 ⟨subd10_1_1032, List.forall_mem_cons.2 ⟨subd10_1_1033, List.forall_mem_cons.2 ⟨subd10_1_1034, List.forall_mem_cons.2 ⟨subd10_1_1035, List.forall_mem_cons.2 ⟨subd10_1_1036, List.forall_mem_cons.2 ⟨subd10_1_1037, List.forall_mem_cons.2 ⟨subd10_1_1038, List.forall_mem_cons.2 ⟨subd10_1_1039, List.forall_mem_cons.2 ⟨subd10_1_1040, List.forall_mem_cons.2 ⟨subd10_1_1041, List.forall_mem_cons.2 ⟨subd10_1_1042, List.forall_mem_cons.2 ⟨subd10_1_1043, List.forall_mem_cons.2 ⟨subd10_1_1044, List.forall_mem_cons.2 ⟨subd10_1_1045, List.forall_mem_cons.2 ⟨subd10_1_1046, List.forall_mem_cons.2 ⟨subd10_1_1047, List.forall_mem_cons.2 ⟨subd10_1_1048, List.forall_mem_cons.2 ⟨subd10_1_1049, List.forall_mem_cons.2 ⟨subd10_1_1050, List.forall_mem_cons.2 ⟨subd10_1_1051, List.forall_mem_cons.2 ⟨subd10_1_1052, List.forall_mem_cons.2 ⟨subd10_1_1053, List.forall_mem_cons.2 ⟨subd10_1_1054, List.forall_mem_cons.2 ⟨subd10_1_1055, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_1056 : subd10_1 [2, 1, -9] = true := by decide +kernel
theorem subd10_1_1057 : subd10_1 [2, 1, -8] = true := by decide +kernel
theorem subd10_1_1058 : subd10_1 [2, 1, -7] = true := by decide +kernel
theorem subd10_1_1059 : subd10_1 [2, 1, -6] = true := by decide +kernel
theorem subd10_1_1060 : subd10_1 [2, 1, -5] = true := by decide +kernel
theorem subd10_1_1061 : subd10_1 [2, 1, -4] = true := by decide +kernel
theorem subd10_1_1062 : subd10_1 [2, 1, -3] = true := by decide +kernel
theorem subd10_1_1063 : subd10_1 [2, 1, -2] = true := by decide +kernel
theorem subd10_1_1064 : subd10_1 [2, 1, -1] = true := by decide +kernel
theorem subd10_1_1065 : subd10_1 [2, 1, 0] = true := by decide +kernel
theorem subd10_1_1066 : subd10_1 [2, 1, 1] = true := by decide +kernel
theorem subd10_1_1067 : subd10_1 [2, 1, 2] = true := by decide +kernel
theorem subd10_1_1068 : subd10_1 [2, 1, 3] = true := by decide +kernel
theorem subd10_1_1069 : subd10_1 [2, 1, 4] = true := by decide +kernel
theorem subd10_1_1070 : subd10_1 [2, 1, 5] = true := by decide +kernel
theorem subd10_1_1071 : subd10_1 [2, 1, 6] = true := by decide +kernel
theorem subd10_1_1072 : subd10_1 [2, 1, 7] = true := by decide +kernel
theorem subd10_1_1073 : subd10_1 [2, 2, -8] = true := by decide +kernel
theorem subd10_1_1074 : subd10_1 [2, 2, -7] = true := by decide +kernel
theorem subd10_1_1075 : subd10_1 [2, 2, -6] = true := by decide +kernel
theorem subd10_1_1076 : subd10_1 [2, 2, -5] = true := by decide +kernel
theorem subd10_1_1077 : subd10_1 [2, 2, -4] = true := by decide +kernel
theorem subd10_1_1078 : subd10_1 [2, 2, -3] = true := by decide +kernel
theorem subd10_1_1079 : subd10_1 [2, 2, -2] = true := by decide +kernel
theorem subd10_1_1080 : subd10_1 [2, 2, -1] = true := by decide +kernel
theorem subd10_1_1081 : subd10_1 [2, 2, 0] = true := by decide +kernel
theorem subd10_1_1082 : subd10_1 [2, 2, 1] = true := by decide +kernel
theorem subd10_1_1083 : subd10_1 [2, 2, 2] = true := by decide +kernel
theorem subd10_1_1084 : subd10_1 [2, 2, 3] = true := by decide +kernel
theorem subd10_1_1085 : subd10_1 [2, 2, 4] = true := by decide +kernel
theorem subd10_1_1086 : subd10_1 [2, 2, 5] = true := by decide +kernel
theorem subd10_1_1087 : subd10_1 [2, 2, 6] = true := by decide +kernel
theorem sbd10_1_33 : ∀ q ∈ blkd10_1_33, subd10_1 q = true := by
  unfold blkd10_1_33
  exact List.forall_mem_cons.2 ⟨subd10_1_1056, List.forall_mem_cons.2 ⟨subd10_1_1057, List.forall_mem_cons.2 ⟨subd10_1_1058, List.forall_mem_cons.2 ⟨subd10_1_1059, List.forall_mem_cons.2 ⟨subd10_1_1060, List.forall_mem_cons.2 ⟨subd10_1_1061, List.forall_mem_cons.2 ⟨subd10_1_1062, List.forall_mem_cons.2 ⟨subd10_1_1063, List.forall_mem_cons.2 ⟨subd10_1_1064, List.forall_mem_cons.2 ⟨subd10_1_1065, List.forall_mem_cons.2 ⟨subd10_1_1066, List.forall_mem_cons.2 ⟨subd10_1_1067, List.forall_mem_cons.2 ⟨subd10_1_1068, List.forall_mem_cons.2 ⟨subd10_1_1069, List.forall_mem_cons.2 ⟨subd10_1_1070, List.forall_mem_cons.2 ⟨subd10_1_1071, List.forall_mem_cons.2 ⟨subd10_1_1072, List.forall_mem_cons.2 ⟨subd10_1_1073, List.forall_mem_cons.2 ⟨subd10_1_1074, List.forall_mem_cons.2 ⟨subd10_1_1075, List.forall_mem_cons.2 ⟨subd10_1_1076, List.forall_mem_cons.2 ⟨subd10_1_1077, List.forall_mem_cons.2 ⟨subd10_1_1078, List.forall_mem_cons.2 ⟨subd10_1_1079, List.forall_mem_cons.2 ⟨subd10_1_1080, List.forall_mem_cons.2 ⟨subd10_1_1081, List.forall_mem_cons.2 ⟨subd10_1_1082, List.forall_mem_cons.2 ⟨subd10_1_1083, List.forall_mem_cons.2 ⟨subd10_1_1084, List.forall_mem_cons.2 ⟨subd10_1_1085, List.forall_mem_cons.2 ⟨subd10_1_1086, List.forall_mem_cons.2 ⟨subd10_1_1087, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C116
