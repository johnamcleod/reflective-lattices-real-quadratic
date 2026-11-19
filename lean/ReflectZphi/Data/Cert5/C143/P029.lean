import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd14_3_640 : subd14_3 [1, -4, 0] = true := by decide +kernel
theorem subd14_3_641 : subd14_3 [1, -4, 1] = true := by decide +kernel
theorem subd14_3_642 : subd14_3 [1, -4, 2] = true := by decide +kernel
theorem subd14_3_643 : subd14_3 [1, -4, 3] = true := by decide +kernel
theorem subd14_3_644 : subd14_3 [1, -4, 4] = true := by decide +kernel
theorem subd14_3_645 : subd14_3 [1, -4, 5] = true := by decide +kernel
theorem subd14_3_646 : subd14_3 [1, -4, 6] = true := by decide +kernel
theorem subd14_3_647 : subd14_3 [1, -4, 7] = true := by decide +kernel
theorem subd14_3_648 : subd14_3 [1, -4, 8] = true := by decide +kernel
theorem subd14_3_649 : subd14_3 [1, -3, -8] = true := by decide +kernel
theorem subd14_3_650 : subd14_3 [1, -3, -7] = true := by decide +kernel
theorem subd14_3_651 : subd14_3 [1, -3, -6] = true := by decide +kernel
theorem subd14_3_652 : subd14_3 [1, -3, -5] = true := by decide +kernel
theorem subd14_3_653 : subd14_3 [1, -3, -4] = true := by decide +kernel
theorem subd14_3_654 : subd14_3 [1, -3, -3] = true := by decide +kernel
theorem subd14_3_655 : subd14_3 [1, -3, -2] = true := by decide +kernel
theorem subd14_3_656 : subd14_3 [1, -3, -1] = true := by decide +kernel
theorem subd14_3_657 : subd14_3 [1, -3, 0] = true := by decide +kernel
theorem subd14_3_658 : subd14_3 [1, -3, 1] = true := by decide +kernel
theorem subd14_3_659 : subd14_3 [1, -3, 2] = true := by decide +kernel
theorem subd14_3_660 : subd14_3 [1, -3, 3] = true := by decide +kernel
theorem subd14_3_661 : subd14_3 [1, -3, 4] = true := by decide +kernel
theorem subd14_3_662 : subd14_3 [1, -3, 5] = true := by decide +kernel
theorem subd14_3_663 : subd14_3 [1, -3, 6] = true := by decide +kernel
theorem subd14_3_664 : subd14_3 [1, -3, 7] = true := by decide +kernel
theorem subd14_3_665 : subd14_3 [1, -3, 8] = true := by decide +kernel
theorem subd14_3_666 : subd14_3 [1, -3, 9] = true := by decide +kernel
theorem subd14_3_667 : subd14_3 [1, -2, -9] = true := by decide +kernel
theorem subd14_3_668 : subd14_3 [1, -2, -8] = true := by decide +kernel
theorem subd14_3_669 : subd14_3 [1, -2, -7] = true := by decide +kernel
theorem subd14_3_670 : subd14_3 [1, -2, -6] = true := by decide +kernel
theorem subd14_3_671 : subd14_3 [1, -2, -5] = true := by decide +kernel
theorem sbd14_3_20 : ∀ q ∈ blkd14_3_20, subd14_3 q = true := by
  unfold blkd14_3_20
  exact List.forall_mem_cons.2 ⟨subd14_3_640, List.forall_mem_cons.2 ⟨subd14_3_641, List.forall_mem_cons.2 ⟨subd14_3_642, List.forall_mem_cons.2 ⟨subd14_3_643, List.forall_mem_cons.2 ⟨subd14_3_644, List.forall_mem_cons.2 ⟨subd14_3_645, List.forall_mem_cons.2 ⟨subd14_3_646, List.forall_mem_cons.2 ⟨subd14_3_647, List.forall_mem_cons.2 ⟨subd14_3_648, List.forall_mem_cons.2 ⟨subd14_3_649, List.forall_mem_cons.2 ⟨subd14_3_650, List.forall_mem_cons.2 ⟨subd14_3_651, List.forall_mem_cons.2 ⟨subd14_3_652, List.forall_mem_cons.2 ⟨subd14_3_653, List.forall_mem_cons.2 ⟨subd14_3_654, List.forall_mem_cons.2 ⟨subd14_3_655, List.forall_mem_cons.2 ⟨subd14_3_656, List.forall_mem_cons.2 ⟨subd14_3_657, List.forall_mem_cons.2 ⟨subd14_3_658, List.forall_mem_cons.2 ⟨subd14_3_659, List.forall_mem_cons.2 ⟨subd14_3_660, List.forall_mem_cons.2 ⟨subd14_3_661, List.forall_mem_cons.2 ⟨subd14_3_662, List.forall_mem_cons.2 ⟨subd14_3_663, List.forall_mem_cons.2 ⟨subd14_3_664, List.forall_mem_cons.2 ⟨subd14_3_665, List.forall_mem_cons.2 ⟨subd14_3_666, List.forall_mem_cons.2 ⟨subd14_3_667, List.forall_mem_cons.2 ⟨subd14_3_668, List.forall_mem_cons.2 ⟨subd14_3_669, List.forall_mem_cons.2 ⟨subd14_3_670, List.forall_mem_cons.2 ⟨subd14_3_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_3_672 : subd14_3 [1, -2, -4] = true := by decide +kernel
theorem subd14_3_673 : subd14_3 [1, -2, -3] = true := by decide +kernel
theorem subd14_3_674 : subd14_3 [1, -2, -2] = true := by decide +kernel
theorem subd14_3_675 : subd14_3 [1, -2, -1] = true := by decide +kernel
theorem subd14_3_676 : subd14_3 [1, -2, 0] = true := by decide +kernel
theorem subd14_3_677 : subd14_3 [1, -2, 1] = true := by decide +kernel
theorem subd14_3_678 : subd14_3 [1, -2, 2] = true := by decide +kernel
theorem subd14_3_679 : subd14_3 [1, -2, 3] = true := by decide +kernel
theorem subd14_3_680 : subd14_3 [1, -2, 4] = true := by decide +kernel
theorem subd14_3_681 : subd14_3 [1, -2, 5] = true := by decide +kernel
theorem subd14_3_682 : subd14_3 [1, -2, 6] = true := by decide +kernel
theorem subd14_3_683 : subd14_3 [1, -2, 7] = true := by decide +kernel
theorem subd14_3_684 : subd14_3 [1, -2, 8] = true := by decide +kernel
theorem subd14_3_685 : subd14_3 [1, -2, 9] = true := by decide +kernel
theorem subd14_3_686 : subd14_3 [1, -2, 10] = true := by decide +kernel
theorem subd14_3_687 : subd14_3 [1, -1, -10] = true := by decide +kernel
theorem subd14_3_688 : subd14_3 [1, -1, -9] = true := by decide +kernel
theorem subd14_3_689 : subd14_3 [1, -1, -8] = true := by decide +kernel
theorem subd14_3_690 : subd14_3 [1, -1, -7] = true := by decide +kernel
theorem subd14_3_691 : subd14_3 [1, -1, -6] = true := by decide +kernel
theorem subd14_3_692 : subd14_3 [1, -1, -5] = true := by decide +kernel
theorem subd14_3_693 : subd14_3 [1, -1, -4] = true := by decide +kernel
theorem subd14_3_694 : subd14_3 [1, -1, -3] = true := by decide +kernel
theorem subd14_3_695 : subd14_3 [1, -1, -2] = true := by decide +kernel
theorem subd14_3_696 : subd14_3 [1, -1, -1] = true := by decide +kernel
theorem subd14_3_697 : subd14_3 [1, -1, 0] = true := by decide +kernel
theorem subd14_3_698 : subd14_3 [1, -1, 1] = true := by decide +kernel
theorem subd14_3_699 : subd14_3 [1, -1, 2] = true := by decide +kernel
theorem subd14_3_700 : subd14_3 [1, -1, 3] = true := by decide +kernel
theorem subd14_3_701 : subd14_3 [1, -1, 4] = true := by decide +kernel
theorem subd14_3_702 : subd14_3 [1, -1, 5] = true := by decide +kernel
theorem subd14_3_703 : subd14_3 [1, -1, 6] = true := by decide +kernel
theorem sbd14_3_21 : ∀ q ∈ blkd14_3_21, subd14_3 q = true := by
  unfold blkd14_3_21
  exact List.forall_mem_cons.2 ⟨subd14_3_672, List.forall_mem_cons.2 ⟨subd14_3_673, List.forall_mem_cons.2 ⟨subd14_3_674, List.forall_mem_cons.2 ⟨subd14_3_675, List.forall_mem_cons.2 ⟨subd14_3_676, List.forall_mem_cons.2 ⟨subd14_3_677, List.forall_mem_cons.2 ⟨subd14_3_678, List.forall_mem_cons.2 ⟨subd14_3_679, List.forall_mem_cons.2 ⟨subd14_3_680, List.forall_mem_cons.2 ⟨subd14_3_681, List.forall_mem_cons.2 ⟨subd14_3_682, List.forall_mem_cons.2 ⟨subd14_3_683, List.forall_mem_cons.2 ⟨subd14_3_684, List.forall_mem_cons.2 ⟨subd14_3_685, List.forall_mem_cons.2 ⟨subd14_3_686, List.forall_mem_cons.2 ⟨subd14_3_687, List.forall_mem_cons.2 ⟨subd14_3_688, List.forall_mem_cons.2 ⟨subd14_3_689, List.forall_mem_cons.2 ⟨subd14_3_690, List.forall_mem_cons.2 ⟨subd14_3_691, List.forall_mem_cons.2 ⟨subd14_3_692, List.forall_mem_cons.2 ⟨subd14_3_693, List.forall_mem_cons.2 ⟨subd14_3_694, List.forall_mem_cons.2 ⟨subd14_3_695, List.forall_mem_cons.2 ⟨subd14_3_696, List.forall_mem_cons.2 ⟨subd14_3_697, List.forall_mem_cons.2 ⟨subd14_3_698, List.forall_mem_cons.2 ⟨subd14_3_699, List.forall_mem_cons.2 ⟨subd14_3_700, List.forall_mem_cons.2 ⟨subd14_3_701, List.forall_mem_cons.2 ⟨subd14_3_702, List.forall_mem_cons.2 ⟨subd14_3_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_3_704 : subd14_3 [1, -1, 7] = true := by decide +kernel
theorem subd14_3_705 : subd14_3 [1, -1, 8] = true := by decide +kernel
theorem subd14_3_706 : subd14_3 [1, -1, 9] = true := by decide +kernel
theorem subd14_3_707 : subd14_3 [1, -1, 10] = true := by decide +kernel
theorem subd14_3_708 : subd14_3 [1, 0, -11] = true := by decide +kernel
theorem subd14_3_709 : subd14_3 [1, 0, -10] = true := by decide +kernel
theorem subd14_3_710 : subd14_3 [1, 0, -9] = true := by decide +kernel
theorem subd14_3_711 : subd14_3 [1, 0, -8] = true := by decide +kernel
theorem subd14_3_712 : subd14_3 [1, 0, -7] = true := by decide +kernel
theorem subd14_3_713 : subd14_3 [1, 0, -6] = true := by decide +kernel
theorem subd14_3_714 : subd14_3 [1, 0, -5] = true := by decide +kernel
theorem subd14_3_715 : subd14_3 [1, 0, -4] = true := by decide +kernel
theorem subd14_3_716 : subd14_3 [1, 0, -3] = true := by decide +kernel
theorem subd14_3_717 : subd14_3 [1, 0, -2] = true := by decide +kernel
theorem subd14_3_718 : subd14_3 [1, 0, -1] = true := by decide +kernel
theorem subd14_3_719 : subd14_3 [1, 0, 0] = true := by decide +kernel
theorem subd14_3_720 : subd14_3 [1, 0, 1] = true := by decide +kernel
theorem subd14_3_721 : subd14_3 [1, 0, 2] = true := by decide +kernel
theorem subd14_3_722 : subd14_3 [1, 0, 3] = true := by decide +kernel
theorem subd14_3_723 : subd14_3 [1, 0, 4] = true := by decide +kernel
theorem subd14_3_724 : subd14_3 [1, 0, 5] = true := by decide +kernel
theorem subd14_3_725 : subd14_3 [1, 0, 6] = true := by decide +kernel
theorem subd14_3_726 : subd14_3 [1, 0, 7] = true := by decide +kernel
theorem subd14_3_727 : subd14_3 [1, 0, 8] = true := by decide +kernel
theorem subd14_3_728 : subd14_3 [1, 0, 9] = true := by decide +kernel
theorem subd14_3_729 : subd14_3 [1, 0, 10] = true := by decide +kernel
theorem subd14_3_730 : subd14_3 [1, 1, -11] = true := by decide +kernel
theorem subd14_3_731 : subd14_3 [1, 1, -10] = true := by decide +kernel
theorem subd14_3_732 : subd14_3 [1, 1, -9] = true := by decide +kernel
theorem subd14_3_733 : subd14_3 [1, 1, -8] = true := by decide +kernel
theorem subd14_3_734 : subd14_3 [1, 1, -7] = true := by decide +kernel
theorem subd14_3_735 : subd14_3 [1, 1, -6] = true := by decide +kernel
theorem sbd14_3_22 : ∀ q ∈ blkd14_3_22, subd14_3 q = true := by
  unfold blkd14_3_22
  exact List.forall_mem_cons.2 ⟨subd14_3_704, List.forall_mem_cons.2 ⟨subd14_3_705, List.forall_mem_cons.2 ⟨subd14_3_706, List.forall_mem_cons.2 ⟨subd14_3_707, List.forall_mem_cons.2 ⟨subd14_3_708, List.forall_mem_cons.2 ⟨subd14_3_709, List.forall_mem_cons.2 ⟨subd14_3_710, List.forall_mem_cons.2 ⟨subd14_3_711, List.forall_mem_cons.2 ⟨subd14_3_712, List.forall_mem_cons.2 ⟨subd14_3_713, List.forall_mem_cons.2 ⟨subd14_3_714, List.forall_mem_cons.2 ⟨subd14_3_715, List.forall_mem_cons.2 ⟨subd14_3_716, List.forall_mem_cons.2 ⟨subd14_3_717, List.forall_mem_cons.2 ⟨subd14_3_718, List.forall_mem_cons.2 ⟨subd14_3_719, List.forall_mem_cons.2 ⟨subd14_3_720, List.forall_mem_cons.2 ⟨subd14_3_721, List.forall_mem_cons.2 ⟨subd14_3_722, List.forall_mem_cons.2 ⟨subd14_3_723, List.forall_mem_cons.2 ⟨subd14_3_724, List.forall_mem_cons.2 ⟨subd14_3_725, List.forall_mem_cons.2 ⟨subd14_3_726, List.forall_mem_cons.2 ⟨subd14_3_727, List.forall_mem_cons.2 ⟨subd14_3_728, List.forall_mem_cons.2 ⟨subd14_3_729, List.forall_mem_cons.2 ⟨subd14_3_730, List.forall_mem_cons.2 ⟨subd14_3_731, List.forall_mem_cons.2 ⟨subd14_3_732, List.forall_mem_cons.2 ⟨subd14_3_733, List.forall_mem_cons.2 ⟨subd14_3_734, List.forall_mem_cons.2 ⟨subd14_3_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_3_736 : subd14_3 [1, 1, -5] = true := by decide +kernel
theorem subd14_3_737 : subd14_3 [1, 1, -4] = true := by decide +kernel
theorem subd14_3_738 : subd14_3 [1, 1, -3] = true := by decide +kernel
theorem subd14_3_739 : subd14_3 [1, 1, -2] = true := by decide +kernel
theorem subd14_3_740 : subd14_3 [1, 1, -1] = true := by decide +kernel
theorem subd14_3_741 : subd14_3 [1, 1, 0] = true := by decide +kernel
theorem subd14_3_742 : subd14_3 [1, 1, 1] = true := by decide +kernel
theorem subd14_3_743 : subd14_3 [1, 1, 2] = true := by decide +kernel
theorem subd14_3_744 : subd14_3 [1, 1, 3] = true := by decide +kernel
theorem subd14_3_745 : subd14_3 [1, 1, 4] = true := by decide +kernel
theorem subd14_3_746 : subd14_3 [1, 1, 5] = true := by decide +kernel
theorem subd14_3_747 : subd14_3 [1, 1, 6] = true := by decide +kernel
theorem subd14_3_748 : subd14_3 [1, 1, 7] = true := by decide +kernel
theorem subd14_3_749 : subd14_3 [1, 1, 8] = true := by decide +kernel
theorem subd14_3_750 : subd14_3 [1, 1, 9] = true := by decide +kernel
theorem subd14_3_751 : subd14_3 [1, 2, -11] = true := by decide +kernel
theorem subd14_3_752 : subd14_3 [1, 2, -10] = true := by decide +kernel
theorem subd14_3_753 : subd14_3 [1, 2, -9] = true := by decide +kernel
theorem subd14_3_754 : subd14_3 [1, 2, -8] = true := by decide +kernel
theorem subd14_3_755 : subd14_3 [1, 2, -7] = true := by decide +kernel
theorem subd14_3_756 : subd14_3 [1, 2, -6] = true := by decide +kernel
theorem subd14_3_757 : subd14_3 [1, 2, -5] = true := by decide +kernel
theorem subd14_3_758 : subd14_3 [1, 2, -4] = true := by decide +kernel
theorem subd14_3_759 : subd14_3 [1, 2, -3] = true := by decide +kernel
theorem subd14_3_760 : subd14_3 [1, 2, -2] = true := by decide +kernel
theorem subd14_3_761 : subd14_3 [1, 2, -1] = true := by decide +kernel
theorem subd14_3_762 : subd14_3 [1, 2, 0] = true := by decide +kernel
theorem subd14_3_763 : subd14_3 [1, 2, 1] = true := by decide +kernel
theorem subd14_3_764 : subd14_3 [1, 2, 2] = true := by decide +kernel
theorem subd14_3_765 : subd14_3 [1, 2, 3] = true := by decide +kernel
theorem subd14_3_766 : subd14_3 [1, 2, 4] = true := by decide +kernel
theorem subd14_3_767 : subd14_3 [1, 2, 5] = true := by decide +kernel
theorem sbd14_3_23 : ∀ q ∈ blkd14_3_23, subd14_3 q = true := by
  unfold blkd14_3_23
  exact List.forall_mem_cons.2 ⟨subd14_3_736, List.forall_mem_cons.2 ⟨subd14_3_737, List.forall_mem_cons.2 ⟨subd14_3_738, List.forall_mem_cons.2 ⟨subd14_3_739, List.forall_mem_cons.2 ⟨subd14_3_740, List.forall_mem_cons.2 ⟨subd14_3_741, List.forall_mem_cons.2 ⟨subd14_3_742, List.forall_mem_cons.2 ⟨subd14_3_743, List.forall_mem_cons.2 ⟨subd14_3_744, List.forall_mem_cons.2 ⟨subd14_3_745, List.forall_mem_cons.2 ⟨subd14_3_746, List.forall_mem_cons.2 ⟨subd14_3_747, List.forall_mem_cons.2 ⟨subd14_3_748, List.forall_mem_cons.2 ⟨subd14_3_749, List.forall_mem_cons.2 ⟨subd14_3_750, List.forall_mem_cons.2 ⟨subd14_3_751, List.forall_mem_cons.2 ⟨subd14_3_752, List.forall_mem_cons.2 ⟨subd14_3_753, List.forall_mem_cons.2 ⟨subd14_3_754, List.forall_mem_cons.2 ⟨subd14_3_755, List.forall_mem_cons.2 ⟨subd14_3_756, List.forall_mem_cons.2 ⟨subd14_3_757, List.forall_mem_cons.2 ⟨subd14_3_758, List.forall_mem_cons.2 ⟨subd14_3_759, List.forall_mem_cons.2 ⟨subd14_3_760, List.forall_mem_cons.2 ⟨subd14_3_761, List.forall_mem_cons.2 ⟨subd14_3_762, List.forall_mem_cons.2 ⟨subd14_3_763, List.forall_mem_cons.2 ⟨subd14_3_764, List.forall_mem_cons.2 ⟨subd14_3_765, List.forall_mem_cons.2 ⟨subd14_3_766, List.forall_mem_cons.2 ⟨subd14_3_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_3_768 : subd14_3 [1, 2, 6] = true := by decide +kernel
theorem subd14_3_769 : subd14_3 [1, 2, 7] = true := by decide +kernel
theorem subd14_3_770 : subd14_3 [1, 2, 8] = true := by decide +kernel
theorem subd14_3_771 : subd14_3 [1, 3, -10] = true := by decide +kernel
theorem subd14_3_772 : subd14_3 [1, 3, -9] = true := by decide +kernel
theorem subd14_3_773 : subd14_3 [1, 3, -8] = true := by decide +kernel
theorem subd14_3_774 : subd14_3 [1, 3, -7] = true := by decide +kernel
theorem subd14_3_775 : subd14_3 [1, 3, -6] = true := by decide +kernel
theorem subd14_3_776 : subd14_3 [1, 3, -5] = true := by decide +kernel
theorem subd14_3_777 : subd14_3 [1, 3, -4] = true := by decide +kernel
theorem subd14_3_778 : subd14_3 [1, 3, -3] = true := by decide +kernel
theorem subd14_3_779 : subd14_3 [1, 3, -2] = true := by decide +kernel
theorem subd14_3_780 : subd14_3 [1, 3, -1] = true := by decide +kernel
theorem subd14_3_781 : subd14_3 [1, 3, 0] = true := by decide +kernel
theorem subd14_3_782 : subd14_3 [1, 3, 1] = true := by decide +kernel
theorem subd14_3_783 : subd14_3 [1, 3, 2] = true := by decide +kernel
theorem subd14_3_784 : subd14_3 [1, 3, 3] = true := by decide +kernel
theorem subd14_3_785 : subd14_3 [1, 3, 4] = true := by decide +kernel
theorem subd14_3_786 : subd14_3 [1, 3, 5] = true := by decide +kernel
theorem subd14_3_787 : subd14_3 [1, 3, 6] = true := by decide +kernel
theorem subd14_3_788 : subd14_3 [1, 4, -9] = true := by decide +kernel
theorem subd14_3_789 : subd14_3 [1, 4, -8] = true := by decide +kernel
theorem subd14_3_790 : subd14_3 [1, 4, -7] = true := by decide +kernel
theorem subd14_3_791 : subd14_3 [1, 4, -6] = true := by decide +kernel
theorem subd14_3_792 : subd14_3 [1, 4, -5] = true := by decide +kernel
theorem subd14_3_793 : subd14_3 [1, 4, -4] = true := by decide +kernel
theorem subd14_3_794 : subd14_3 [1, 4, -3] = true := by decide +kernel
theorem subd14_3_795 : subd14_3 [1, 4, -2] = true := by decide +kernel
theorem subd14_3_796 : subd14_3 [1, 4, -1] = true := by decide +kernel
theorem subd14_3_797 : subd14_3 [1, 4, 0] = true := by decide +kernel
theorem subd14_3_798 : subd14_3 [1, 4, 1] = true := by decide +kernel
theorem subd14_3_799 : subd14_3 [1, 4, 2] = true := by decide +kernel
theorem sbd14_3_24 : ∀ q ∈ blkd14_3_24, subd14_3 q = true := by
  unfold blkd14_3_24
  exact List.forall_mem_cons.2 ⟨subd14_3_768, List.forall_mem_cons.2 ⟨subd14_3_769, List.forall_mem_cons.2 ⟨subd14_3_770, List.forall_mem_cons.2 ⟨subd14_3_771, List.forall_mem_cons.2 ⟨subd14_3_772, List.forall_mem_cons.2 ⟨subd14_3_773, List.forall_mem_cons.2 ⟨subd14_3_774, List.forall_mem_cons.2 ⟨subd14_3_775, List.forall_mem_cons.2 ⟨subd14_3_776, List.forall_mem_cons.2 ⟨subd14_3_777, List.forall_mem_cons.2 ⟨subd14_3_778, List.forall_mem_cons.2 ⟨subd14_3_779, List.forall_mem_cons.2 ⟨subd14_3_780, List.forall_mem_cons.2 ⟨subd14_3_781, List.forall_mem_cons.2 ⟨subd14_3_782, List.forall_mem_cons.2 ⟨subd14_3_783, List.forall_mem_cons.2 ⟨subd14_3_784, List.forall_mem_cons.2 ⟨subd14_3_785, List.forall_mem_cons.2 ⟨subd14_3_786, List.forall_mem_cons.2 ⟨subd14_3_787, List.forall_mem_cons.2 ⟨subd14_3_788, List.forall_mem_cons.2 ⟨subd14_3_789, List.forall_mem_cons.2 ⟨subd14_3_790, List.forall_mem_cons.2 ⟨subd14_3_791, List.forall_mem_cons.2 ⟨subd14_3_792, List.forall_mem_cons.2 ⟨subd14_3_793, List.forall_mem_cons.2 ⟨subd14_3_794, List.forall_mem_cons.2 ⟨subd14_3_795, List.forall_mem_cons.2 ⟨subd14_3_796, List.forall_mem_cons.2 ⟨subd14_3_797, List.forall_mem_cons.2 ⟨subd14_3_798, List.forall_mem_cons.2 ⟨subd14_3_799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_3_800 : subd14_3 [1, 4, 3] = true := by decide +kernel
theorem subd14_3_801 : subd14_3 [1, 4, 4] = true := by decide +kernel
theorem subd14_3_802 : subd14_3 [1, 5] = true := by decide +kernel
theorem subd14_3_803 : subd14_3 [2, -6] = true := by decide +kernel
theorem subd14_3_804 : subd14_3 [2, -5] = true := by decide +kernel
theorem subd14_3_805 : subd14_3 [2, -4] = true := by decide +kernel
theorem subd14_3_806 : subd14_3 [2, -3, -7] = true := by decide +kernel
theorem subd14_3_807 : subd14_3 [2, -3, -6] = true := by decide +kernel
theorem subd14_3_808 : subd14_3 [2, -3, -5] = true := by decide +kernel
theorem subd14_3_809 : subd14_3 [2, -3, -4] = true := by decide +kernel
theorem subd14_3_810 : subd14_3 [2, -3, -3] = true := by decide +kernel
theorem subd14_3_811 : subd14_3 [2, -3, -2] = true := by decide +kernel
theorem subd14_3_812 : subd14_3 [2, -3, -1] = true := by decide +kernel
theorem subd14_3_813 : subd14_3 [2, -3, 0] = true := by decide +kernel
theorem subd14_3_814 : subd14_3 [2, -3, 1] = true := by decide +kernel
theorem subd14_3_815 : subd14_3 [2, -3, 2] = true := by decide +kernel
theorem subd14_3_816 : subd14_3 [2, -3, 3] = true := by decide +kernel
theorem subd14_3_817 : subd14_3 [2, -3, 4] = true := by decide +kernel
theorem subd14_3_818 : subd14_3 [2, -3, 5] = true := by decide +kernel
theorem subd14_3_819 : subd14_3 [2, -3, 6] = true := by decide +kernel
theorem subd14_3_820 : subd14_3 [2, -3, 7] = true := by decide +kernel
theorem subd14_3_821 : subd14_3 [2, -3, 8] = true := by decide +kernel
theorem subd14_3_822 : subd14_3 [2, -2, -9] = true := by decide +kernel
theorem subd14_3_823 : subd14_3 [2, -2, -8] = true := by decide +kernel
theorem subd14_3_824 : subd14_3 [2, -2, -7] = true := by decide +kernel
theorem subd14_3_825 : subd14_3 [2, -2, -6] = true := by decide +kernel
theorem subd14_3_826 : subd14_3 [2, -2, -5] = true := by decide +kernel
theorem subd14_3_827 : subd14_3 [2, -2, -4] = true := by decide +kernel
theorem subd14_3_828 : subd14_3 [2, -2, -3] = true := by decide +kernel
theorem subd14_3_829 : subd14_3 [2, -2, -2] = true := by decide +kernel
theorem subd14_3_830 : subd14_3 [2, -2, -1] = true := by decide +kernel
theorem subd14_3_831 : subd14_3 [2, -2, 0] = true := by decide +kernel
theorem sbd14_3_25 : ∀ q ∈ blkd14_3_25, subd14_3 q = true := by
  unfold blkd14_3_25
  exact List.forall_mem_cons.2 ⟨subd14_3_800, List.forall_mem_cons.2 ⟨subd14_3_801, List.forall_mem_cons.2 ⟨subd14_3_802, List.forall_mem_cons.2 ⟨subd14_3_803, List.forall_mem_cons.2 ⟨subd14_3_804, List.forall_mem_cons.2 ⟨subd14_3_805, List.forall_mem_cons.2 ⟨subd14_3_806, List.forall_mem_cons.2 ⟨subd14_3_807, List.forall_mem_cons.2 ⟨subd14_3_808, List.forall_mem_cons.2 ⟨subd14_3_809, List.forall_mem_cons.2 ⟨subd14_3_810, List.forall_mem_cons.2 ⟨subd14_3_811, List.forall_mem_cons.2 ⟨subd14_3_812, List.forall_mem_cons.2 ⟨subd14_3_813, List.forall_mem_cons.2 ⟨subd14_3_814, List.forall_mem_cons.2 ⟨subd14_3_815, List.forall_mem_cons.2 ⟨subd14_3_816, List.forall_mem_cons.2 ⟨subd14_3_817, List.forall_mem_cons.2 ⟨subd14_3_818, List.forall_mem_cons.2 ⟨subd14_3_819, List.forall_mem_cons.2 ⟨subd14_3_820, List.forall_mem_cons.2 ⟨subd14_3_821, List.forall_mem_cons.2 ⟨subd14_3_822, List.forall_mem_cons.2 ⟨subd14_3_823, List.forall_mem_cons.2 ⟨subd14_3_824, List.forall_mem_cons.2 ⟨subd14_3_825, List.forall_mem_cons.2 ⟨subd14_3_826, List.forall_mem_cons.2 ⟨subd14_3_827, List.forall_mem_cons.2 ⟨subd14_3_828, List.forall_mem_cons.2 ⟨subd14_3_829, List.forall_mem_cons.2 ⟨subd14_3_830, List.forall_mem_cons.2 ⟨subd14_3_831, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_3_832 : subd14_3 [2, -2, 1] = true := by decide +kernel
theorem subd14_3_833 : subd14_3 [2, -2, 2] = true := by decide +kernel
theorem subd14_3_834 : subd14_3 [2, -2, 3] = true := by decide +kernel
theorem subd14_3_835 : subd14_3 [2, -2, 4] = true := by decide +kernel
theorem subd14_3_836 : subd14_3 [2, -2, 5] = true := by decide +kernel
theorem subd14_3_837 : subd14_3 [2, -2, 6] = true := by decide +kernel
theorem subd14_3_838 : subd14_3 [2, -2, 7] = true := by decide +kernel
theorem subd14_3_839 : subd14_3 [2, -2, 8] = true := by decide +kernel
theorem subd14_3_840 : subd14_3 [2, -2, 9] = true := by decide +kernel
theorem subd14_3_841 : subd14_3 [2, -1, -10] = true := by decide +kernel
theorem subd14_3_842 : subd14_3 [2, -1, -9] = true := by decide +kernel
theorem subd14_3_843 : subd14_3 [2, -1, -8] = true := by decide +kernel
theorem subd14_3_844 : subd14_3 [2, -1, -7] = true := by decide +kernel
theorem subd14_3_845 : subd14_3 [2, -1, -6] = true := by decide +kernel
theorem subd14_3_846 : subd14_3 [2, -1, -5] = true := by decide +kernel
theorem subd14_3_847 : subd14_3 [2, -1, -4] = true := by decide +kernel
theorem subd14_3_848 : subd14_3 [2, -1, -3] = true := by decide +kernel
theorem subd14_3_849 : subd14_3 [2, -1, -2] = true := by decide +kernel
theorem subd14_3_850 : subd14_3 [2, -1, -1] = true := by decide +kernel
theorem subd14_3_851 : subd14_3 [2, -1, 0] = true := by decide +kernel
theorem subd14_3_852 : subd14_3 [2, -1, 1] = true := by decide +kernel
theorem subd14_3_853 : subd14_3 [2, -1, 2] = true := by decide +kernel
theorem subd14_3_854 : subd14_3 [2, -1, 3] = true := by decide +kernel
theorem subd14_3_855 : subd14_3 [2, -1, 4] = true := by decide +kernel
theorem subd14_3_856 : subd14_3 [2, -1, 5] = true := by decide +kernel
theorem subd14_3_857 : subd14_3 [2, -1, 6] = true := by decide +kernel
theorem subd14_3_858 : subd14_3 [2, -1, 7] = true := by decide +kernel
theorem subd14_3_859 : subd14_3 [2, -1, 8] = true := by decide +kernel
theorem subd14_3_860 : subd14_3 [2, -1, 9] = true := by decide +kernel
theorem subd14_3_861 : subd14_3 [2, 0, -10] = true := by decide +kernel
theorem subd14_3_862 : subd14_3 [2, 0, -9] = true := by decide +kernel
theorem subd14_3_863 : subd14_3 [2, 0, -8] = true := by decide +kernel
theorem sbd14_3_26 : ∀ q ∈ blkd14_3_26, subd14_3 q = true := by
  unfold blkd14_3_26
  exact List.forall_mem_cons.2 ⟨subd14_3_832, List.forall_mem_cons.2 ⟨subd14_3_833, List.forall_mem_cons.2 ⟨subd14_3_834, List.forall_mem_cons.2 ⟨subd14_3_835, List.forall_mem_cons.2 ⟨subd14_3_836, List.forall_mem_cons.2 ⟨subd14_3_837, List.forall_mem_cons.2 ⟨subd14_3_838, List.forall_mem_cons.2 ⟨subd14_3_839, List.forall_mem_cons.2 ⟨subd14_3_840, List.forall_mem_cons.2 ⟨subd14_3_841, List.forall_mem_cons.2 ⟨subd14_3_842, List.forall_mem_cons.2 ⟨subd14_3_843, List.forall_mem_cons.2 ⟨subd14_3_844, List.forall_mem_cons.2 ⟨subd14_3_845, List.forall_mem_cons.2 ⟨subd14_3_846, List.forall_mem_cons.2 ⟨subd14_3_847, List.forall_mem_cons.2 ⟨subd14_3_848, List.forall_mem_cons.2 ⟨subd14_3_849, List.forall_mem_cons.2 ⟨subd14_3_850, List.forall_mem_cons.2 ⟨subd14_3_851, List.forall_mem_cons.2 ⟨subd14_3_852, List.forall_mem_cons.2 ⟨subd14_3_853, List.forall_mem_cons.2 ⟨subd14_3_854, List.forall_mem_cons.2 ⟨subd14_3_855, List.forall_mem_cons.2 ⟨subd14_3_856, List.forall_mem_cons.2 ⟨subd14_3_857, List.forall_mem_cons.2 ⟨subd14_3_858, List.forall_mem_cons.2 ⟨subd14_3_859, List.forall_mem_cons.2 ⟨subd14_3_860, List.forall_mem_cons.2 ⟨subd14_3_861, List.forall_mem_cons.2 ⟨subd14_3_862, List.forall_mem_cons.2 ⟨subd14_3_863, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_3_864 : subd14_3 [2, 0, -7] = true := by decide +kernel
theorem subd14_3_865 : subd14_3 [2, 0, -6] = true := by decide +kernel
theorem subd14_3_866 : subd14_3 [2, 0, -5] = true := by decide +kernel
theorem subd14_3_867 : subd14_3 [2, 0, -4] = true := by decide +kernel
theorem subd14_3_868 : subd14_3 [2, 0, -3] = true := by decide +kernel
theorem subd14_3_869 : subd14_3 [2, 0, -2] = true := by decide +kernel
theorem subd14_3_870 : subd14_3 [2, 0, -1] = true := by decide +kernel
theorem subd14_3_871 : subd14_3 [2, 0, 0] = true := by decide +kernel
theorem subd14_3_872 : subd14_3 [2, 0, 1] = true := by decide +kernel
theorem subd14_3_873 : subd14_3 [2, 0, 2] = true := by decide +kernel
theorem subd14_3_874 : subd14_3 [2, 0, 3] = true := by decide +kernel
theorem subd14_3_875 : subd14_3 [2, 0, 4] = true := by decide +kernel
theorem subd14_3_876 : subd14_3 [2, 0, 5] = true := by decide +kernel
theorem subd14_3_877 : subd14_3 [2, 0, 6] = true := by decide +kernel
theorem subd14_3_878 : subd14_3 [2, 0, 7] = true := by decide +kernel
theorem subd14_3_879 : subd14_3 [2, 0, 8] = true := by decide +kernel
theorem subd14_3_880 : subd14_3 [2, 0, 9] = true := by decide +kernel
theorem subd14_3_881 : subd14_3 [2, 1, -10] = true := by decide +kernel
theorem subd14_3_882 : subd14_3 [2, 1, -9] = true := by decide +kernel
theorem subd14_3_883 : subd14_3 [2, 1, -8] = true := by decide +kernel
theorem subd14_3_884 : subd14_3 [2, 1, -7] = true := by decide +kernel
theorem subd14_3_885 : subd14_3 [2, 1, -6] = true := by decide +kernel
theorem subd14_3_886 : subd14_3 [2, 1, -5] = true := by decide +kernel
theorem subd14_3_887 : subd14_3 [2, 1, -4] = true := by decide +kernel
theorem subd14_3_888 : subd14_3 [2, 1, -3] = true := by decide +kernel
theorem subd14_3_889 : subd14_3 [2, 1, -2] = true := by decide +kernel
theorem subd14_3_890 : subd14_3 [2, 1, -1] = true := by decide +kernel
theorem subd14_3_891 : subd14_3 [2, 1, 0] = true := by decide +kernel
theorem subd14_3_892 : subd14_3 [2, 1, 1] = true := by decide +kernel
theorem subd14_3_893 : subd14_3 [2, 1, 2] = true := by decide +kernel
theorem subd14_3_894 : subd14_3 [2, 1, 3] = true := by decide +kernel
theorem subd14_3_895 : subd14_3 [2, 1, 4] = true := by decide +kernel
theorem sbd14_3_27 : ∀ q ∈ blkd14_3_27, subd14_3 q = true := by
  unfold blkd14_3_27
  exact List.forall_mem_cons.2 ⟨subd14_3_864, List.forall_mem_cons.2 ⟨subd14_3_865, List.forall_mem_cons.2 ⟨subd14_3_866, List.forall_mem_cons.2 ⟨subd14_3_867, List.forall_mem_cons.2 ⟨subd14_3_868, List.forall_mem_cons.2 ⟨subd14_3_869, List.forall_mem_cons.2 ⟨subd14_3_870, List.forall_mem_cons.2 ⟨subd14_3_871, List.forall_mem_cons.2 ⟨subd14_3_872, List.forall_mem_cons.2 ⟨subd14_3_873, List.forall_mem_cons.2 ⟨subd14_3_874, List.forall_mem_cons.2 ⟨subd14_3_875, List.forall_mem_cons.2 ⟨subd14_3_876, List.forall_mem_cons.2 ⟨subd14_3_877, List.forall_mem_cons.2 ⟨subd14_3_878, List.forall_mem_cons.2 ⟨subd14_3_879, List.forall_mem_cons.2 ⟨subd14_3_880, List.forall_mem_cons.2 ⟨subd14_3_881, List.forall_mem_cons.2 ⟨subd14_3_882, List.forall_mem_cons.2 ⟨subd14_3_883, List.forall_mem_cons.2 ⟨subd14_3_884, List.forall_mem_cons.2 ⟨subd14_3_885, List.forall_mem_cons.2 ⟨subd14_3_886, List.forall_mem_cons.2 ⟨subd14_3_887, List.forall_mem_cons.2 ⟨subd14_3_888, List.forall_mem_cons.2 ⟨subd14_3_889, List.forall_mem_cons.2 ⟨subd14_3_890, List.forall_mem_cons.2 ⟨subd14_3_891, List.forall_mem_cons.2 ⟨subd14_3_892, List.forall_mem_cons.2 ⟨subd14_3_893, List.forall_mem_cons.2 ⟨subd14_3_894, List.forall_mem_cons.2 ⟨subd14_3_895, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_3_896 : subd14_3 [2, 1, 5] = true := by decide +kernel
theorem subd14_3_897 : subd14_3 [2, 1, 6] = true := by decide +kernel
theorem subd14_3_898 : subd14_3 [2, 1, 7] = true := by decide +kernel
theorem subd14_3_899 : subd14_3 [2, 1, 8] = true := by decide +kernel
theorem subd14_3_900 : subd14_3 [2, 2, -10] = true := by decide +kernel
theorem subd14_3_901 : subd14_3 [2, 2, -9] = true := by decide +kernel
theorem subd14_3_902 : subd14_3 [2, 2, -8] = true := by decide +kernel
theorem subd14_3_903 : subd14_3 [2, 2, -7] = true := by decide +kernel
theorem subd14_3_904 : subd14_3 [2, 2, -6] = true := by decide +kernel
theorem subd14_3_905 : subd14_3 [2, 2, -5] = true := by decide +kernel
theorem subd14_3_906 : subd14_3 [2, 2, -4] = true := by decide +kernel
theorem subd14_3_907 : subd14_3 [2, 2, -3] = true := by decide +kernel
theorem subd14_3_908 : subd14_3 [2, 2, -2] = true := by decide +kernel
theorem subd14_3_909 : subd14_3 [2, 2, -1] = true := by decide +kernel
theorem subd14_3_910 : subd14_3 [2, 2, 0] = true := by decide +kernel
theorem subd14_3_911 : subd14_3 [2, 2, 1] = true := by decide +kernel
theorem subd14_3_912 : subd14_3 [2, 2, 2] = true := by decide +kernel
theorem subd14_3_913 : subd14_3 [2, 2, 3] = true := by decide +kernel
theorem subd14_3_914 : subd14_3 [2, 2, 4] = true := by decide +kernel
theorem subd14_3_915 : subd14_3 [2, 2, 5] = true := by decide +kernel
theorem subd14_3_916 : subd14_3 [2, 2, 6] = true := by decide +kernel
theorem subd14_3_917 : subd14_3 [2, 2, 7] = true := by decide +kernel
theorem subd14_3_918 : subd14_3 [2, 3, -9] = true := by decide +kernel
theorem subd14_3_919 : subd14_3 [2, 3, -8] = true := by decide +kernel
theorem subd14_3_920 : subd14_3 [2, 3, -7] = true := by decide +kernel
theorem subd14_3_921 : subd14_3 [2, 3, -6] = true := by decide +kernel
theorem subd14_3_922 : subd14_3 [2, 3, -5] = true := by decide +kernel
theorem subd14_3_923 : subd14_3 [2, 3, -4] = true := by decide +kernel
theorem subd14_3_924 : subd14_3 [2, 3, -3] = true := by decide +kernel
theorem subd14_3_925 : subd14_3 [2, 3, -2] = true := by decide +kernel
theorem subd14_3_926 : subd14_3 [2, 3, -1] = true := by decide +kernel
theorem subd14_3_927 : subd14_3 [2, 3, 0] = true := by decide +kernel
theorem sbd14_3_28 : ∀ q ∈ blkd14_3_28, subd14_3 q = true := by
  unfold blkd14_3_28
  exact List.forall_mem_cons.2 ⟨subd14_3_896, List.forall_mem_cons.2 ⟨subd14_3_897, List.forall_mem_cons.2 ⟨subd14_3_898, List.forall_mem_cons.2 ⟨subd14_3_899, List.forall_mem_cons.2 ⟨subd14_3_900, List.forall_mem_cons.2 ⟨subd14_3_901, List.forall_mem_cons.2 ⟨subd14_3_902, List.forall_mem_cons.2 ⟨subd14_3_903, List.forall_mem_cons.2 ⟨subd14_3_904, List.forall_mem_cons.2 ⟨subd14_3_905, List.forall_mem_cons.2 ⟨subd14_3_906, List.forall_mem_cons.2 ⟨subd14_3_907, List.forall_mem_cons.2 ⟨subd14_3_908, List.forall_mem_cons.2 ⟨subd14_3_909, List.forall_mem_cons.2 ⟨subd14_3_910, List.forall_mem_cons.2 ⟨subd14_3_911, List.forall_mem_cons.2 ⟨subd14_3_912, List.forall_mem_cons.2 ⟨subd14_3_913, List.forall_mem_cons.2 ⟨subd14_3_914, List.forall_mem_cons.2 ⟨subd14_3_915, List.forall_mem_cons.2 ⟨subd14_3_916, List.forall_mem_cons.2 ⟨subd14_3_917, List.forall_mem_cons.2 ⟨subd14_3_918, List.forall_mem_cons.2 ⟨subd14_3_919, List.forall_mem_cons.2 ⟨subd14_3_920, List.forall_mem_cons.2 ⟨subd14_3_921, List.forall_mem_cons.2 ⟨subd14_3_922, List.forall_mem_cons.2 ⟨subd14_3_923, List.forall_mem_cons.2 ⟨subd14_3_924, List.forall_mem_cons.2 ⟨subd14_3_925, List.forall_mem_cons.2 ⟨subd14_3_926, List.forall_mem_cons.2 ⟨subd14_3_927, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_3_928 : subd14_3 [2, 3, 1] = true := by decide +kernel
theorem subd14_3_929 : subd14_3 [2, 3, 2] = true := by decide +kernel
theorem subd14_3_930 : subd14_3 [2, 3, 3] = true := by decide +kernel
theorem subd14_3_931 : subd14_3 [2, 3, 4] = true := by decide +kernel
theorem subd14_3_932 : subd14_3 [2, 3, 5] = true := by decide +kernel
theorem subd14_3_933 : subd14_3 [2, 3, 6] = true := by decide +kernel
theorem subd14_3_934 : subd14_3 [2, 4] = true := by decide +kernel
theorem subd14_3_935 : subd14_3 [3, -5] = true := by decide +kernel
theorem subd14_3_936 : subd14_3 [3, -4] = true := by decide +kernel
theorem subd14_3_937 : subd14_3 [3, -3, -6] = true := by decide +kernel
theorem subd14_3_938 : subd14_3 [3, -3, -5] = true := by decide +kernel
theorem subd14_3_939 : subd14_3 [3, -3, -4] = true := by decide +kernel
theorem subd14_3_940 : subd14_3 [3, -3, -3] = true := by decide +kernel
theorem subd14_3_941 : subd14_3 [3, -3, -2] = true := by decide +kernel
theorem subd14_3_942 : subd14_3 [3, -3, -1] = true := by decide +kernel
theorem subd14_3_943 : subd14_3 [3, -3, 0] = true := by decide +kernel
theorem subd14_3_944 : subd14_3 [3, -3, 1] = true := by decide +kernel
theorem subd14_3_945 : subd14_3 [3, -3, 2] = true := by decide +kernel
theorem subd14_3_946 : subd14_3 [3, -3, 3] = true := by decide +kernel
theorem subd14_3_947 : subd14_3 [3, -3, 4] = true := by decide +kernel
theorem subd14_3_948 : subd14_3 [3, -3, 5] = true := by decide +kernel
theorem subd14_3_949 : subd14_3 [3, -3, 6] = true := by decide +kernel
theorem subd14_3_950 : subd14_3 [3, -3, 7] = true := by decide +kernel
theorem subd14_3_951 : subd14_3 [3, -2, -8] = true := by decide +kernel
theorem subd14_3_952 : subd14_3 [3, -2, -7] = true := by decide +kernel
theorem subd14_3_953 : subd14_3 [3, -2, -6] = true := by decide +kernel
theorem subd14_3_954 : subd14_3 [3, -2, -5] = true := by decide +kernel
theorem subd14_3_955 : subd14_3 [3, -2, -4] = true := by decide +kernel
theorem subd14_3_956 : subd14_3 [3, -2, -3] = true := by decide +kernel
theorem subd14_3_957 : subd14_3 [3, -2, -2] = true := by decide +kernel
theorem subd14_3_958 : subd14_3 [3, -2, -1] = true := by decide +kernel
theorem subd14_3_959 : subd14_3 [3, -2, 0] = true := by decide +kernel
theorem sbd14_3_29 : ∀ q ∈ blkd14_3_29, subd14_3 q = true := by
  unfold blkd14_3_29
  exact List.forall_mem_cons.2 ⟨subd14_3_928, List.forall_mem_cons.2 ⟨subd14_3_929, List.forall_mem_cons.2 ⟨subd14_3_930, List.forall_mem_cons.2 ⟨subd14_3_931, List.forall_mem_cons.2 ⟨subd14_3_932, List.forall_mem_cons.2 ⟨subd14_3_933, List.forall_mem_cons.2 ⟨subd14_3_934, List.forall_mem_cons.2 ⟨subd14_3_935, List.forall_mem_cons.2 ⟨subd14_3_936, List.forall_mem_cons.2 ⟨subd14_3_937, List.forall_mem_cons.2 ⟨subd14_3_938, List.forall_mem_cons.2 ⟨subd14_3_939, List.forall_mem_cons.2 ⟨subd14_3_940, List.forall_mem_cons.2 ⟨subd14_3_941, List.forall_mem_cons.2 ⟨subd14_3_942, List.forall_mem_cons.2 ⟨subd14_3_943, List.forall_mem_cons.2 ⟨subd14_3_944, List.forall_mem_cons.2 ⟨subd14_3_945, List.forall_mem_cons.2 ⟨subd14_3_946, List.forall_mem_cons.2 ⟨subd14_3_947, List.forall_mem_cons.2 ⟨subd14_3_948, List.forall_mem_cons.2 ⟨subd14_3_949, List.forall_mem_cons.2 ⟨subd14_3_950, List.forall_mem_cons.2 ⟨subd14_3_951, List.forall_mem_cons.2 ⟨subd14_3_952, List.forall_mem_cons.2 ⟨subd14_3_953, List.forall_mem_cons.2 ⟨subd14_3_954, List.forall_mem_cons.2 ⟨subd14_3_955, List.forall_mem_cons.2 ⟨subd14_3_956, List.forall_mem_cons.2 ⟨subd14_3_957, List.forall_mem_cons.2 ⟨subd14_3_958, List.forall_mem_cons.2 ⟨subd14_3_959, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_3_960 : subd14_3 [3, -2, 1] = true := by decide +kernel
theorem subd14_3_961 : subd14_3 [3, -2, 2] = true := by decide +kernel
theorem subd14_3_962 : subd14_3 [3, -2, 3] = true := by decide +kernel
theorem subd14_3_963 : subd14_3 [3, -2, 4] = true := by decide +kernel
theorem subd14_3_964 : subd14_3 [3, -2, 5] = true := by decide +kernel
theorem subd14_3_965 : subd14_3 [3, -2, 6] = true := by decide +kernel
theorem subd14_3_966 : subd14_3 [3, -2, 7] = true := by decide +kernel
theorem subd14_3_967 : subd14_3 [3, -2, 8] = true := by decide +kernel
theorem subd14_3_968 : subd14_3 [3, -1, -9] = true := by decide +kernel
theorem subd14_3_969 : subd14_3 [3, -1, -8] = true := by decide +kernel
theorem subd14_3_970 : subd14_3 [3, -1, -7] = true := by decide +kernel
theorem subd14_3_971 : subd14_3 [3, -1, -6] = true := by decide +kernel
theorem subd14_3_972 : subd14_3 [3, -1, -5] = true := by decide +kernel
theorem subd14_3_973 : subd14_3 [3, -1, -4] = true := by decide +kernel
theorem subd14_3_974 : subd14_3 [3, -1, -3] = true := by decide +kernel
theorem subd14_3_975 : subd14_3 [3, -1, -2] = true := by decide +kernel
theorem subd14_3_976 : subd14_3 [3, -1, -1] = true := by decide +kernel
theorem subd14_3_977 : subd14_3 [3, -1, 0] = true := by decide +kernel
theorem subd14_3_978 : subd14_3 [3, -1, 1] = true := by decide +kernel
theorem subd14_3_979 : subd14_3 [3, -1, 2] = true := by decide +kernel
theorem subd14_3_980 : subd14_3 [3, -1, 3] = true := by decide +kernel
theorem subd14_3_981 : subd14_3 [3, -1, 4] = true := by decide +kernel
theorem subd14_3_982 : subd14_3 [3, -1, 5] = true := by decide +kernel
theorem subd14_3_983 : subd14_3 [3, -1, 6] = true := by decide +kernel
theorem subd14_3_984 : subd14_3 [3, -1, 7] = true := by decide +kernel
theorem subd14_3_985 : subd14_3 [3, -1, 8] = true := by decide +kernel
theorem subd14_3_986 : subd14_3 [3, 0, -9] = true := by decide +kernel
theorem subd14_3_987 : subd14_3 [3, 0, -8] = true := by decide +kernel
theorem subd14_3_988 : subd14_3 [3, 0, -7] = true := by decide +kernel
theorem subd14_3_989 : subd14_3 [3, 0, -6] = true := by decide +kernel
theorem subd14_3_990 : subd14_3 [3, 0, -5] = true := by decide +kernel
theorem subd14_3_991 : subd14_3 [3, 0, -4] = true := by decide +kernel
theorem sbd14_3_30 : ∀ q ∈ blkd14_3_30, subd14_3 q = true := by
  unfold blkd14_3_30
  exact List.forall_mem_cons.2 ⟨subd14_3_960, List.forall_mem_cons.2 ⟨subd14_3_961, List.forall_mem_cons.2 ⟨subd14_3_962, List.forall_mem_cons.2 ⟨subd14_3_963, List.forall_mem_cons.2 ⟨subd14_3_964, List.forall_mem_cons.2 ⟨subd14_3_965, List.forall_mem_cons.2 ⟨subd14_3_966, List.forall_mem_cons.2 ⟨subd14_3_967, List.forall_mem_cons.2 ⟨subd14_3_968, List.forall_mem_cons.2 ⟨subd14_3_969, List.forall_mem_cons.2 ⟨subd14_3_970, List.forall_mem_cons.2 ⟨subd14_3_971, List.forall_mem_cons.2 ⟨subd14_3_972, List.forall_mem_cons.2 ⟨subd14_3_973, List.forall_mem_cons.2 ⟨subd14_3_974, List.forall_mem_cons.2 ⟨subd14_3_975, List.forall_mem_cons.2 ⟨subd14_3_976, List.forall_mem_cons.2 ⟨subd14_3_977, List.forall_mem_cons.2 ⟨subd14_3_978, List.forall_mem_cons.2 ⟨subd14_3_979, List.forall_mem_cons.2 ⟨subd14_3_980, List.forall_mem_cons.2 ⟨subd14_3_981, List.forall_mem_cons.2 ⟨subd14_3_982, List.forall_mem_cons.2 ⟨subd14_3_983, List.forall_mem_cons.2 ⟨subd14_3_984, List.forall_mem_cons.2 ⟨subd14_3_985, List.forall_mem_cons.2 ⟨subd14_3_986, List.forall_mem_cons.2 ⟨subd14_3_987, List.forall_mem_cons.2 ⟨subd14_3_988, List.forall_mem_cons.2 ⟨subd14_3_989, List.forall_mem_cons.2 ⟨subd14_3_990, List.forall_mem_cons.2 ⟨subd14_3_991, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_3_992 : subd14_3 [3, 0, -3] = true := by decide +kernel
theorem subd14_3_993 : subd14_3 [3, 0, -2] = true := by decide +kernel
theorem subd14_3_994 : subd14_3 [3, 0, -1] = true := by decide +kernel
theorem subd14_3_995 : subd14_3 [3, 0, 0] = true := by decide +kernel
theorem subd14_3_996 : subd14_3 [3, 0, 1] = true := by decide +kernel
theorem subd14_3_997 : subd14_3 [3, 0, 2] = true := by decide +kernel
theorem subd14_3_998 : subd14_3 [3, 0, 3] = true := by decide +kernel
theorem subd14_3_999 : subd14_3 [3, 0, 4] = true := by decide +kernel
theorem subd14_3_1000 : subd14_3 [3, 0, 5] = true := by decide +kernel
theorem subd14_3_1001 : subd14_3 [3, 0, 6] = true := by decide +kernel
theorem subd14_3_1002 : subd14_3 [3, 0, 7] = true := by decide +kernel
theorem subd14_3_1003 : subd14_3 [3, 0, 8] = true := by decide +kernel
theorem subd14_3_1004 : subd14_3 [3, 1, -9] = true := by decide +kernel
theorem subd14_3_1005 : subd14_3 [3, 1, -8] = true := by decide +kernel
theorem subd14_3_1006 : subd14_3 [3, 1, -7] = true := by decide +kernel
theorem subd14_3_1007 : subd14_3 [3, 1, -6] = true := by decide +kernel
theorem subd14_3_1008 : subd14_3 [3, 1, -5] = true := by decide +kernel
theorem subd14_3_1009 : subd14_3 [3, 1, -4] = true := by decide +kernel
theorem subd14_3_1010 : subd14_3 [3, 1, -3] = true := by decide +kernel
theorem subd14_3_1011 : subd14_3 [3, 1, -2] = true := by decide +kernel
theorem subd14_3_1012 : subd14_3 [3, 1, -1] = true := by decide +kernel
theorem subd14_3_1013 : subd14_3 [3, 1, 0] = true := by decide +kernel
theorem subd14_3_1014 : subd14_3 [3, 1, 1] = true := by decide +kernel
theorem subd14_3_1015 : subd14_3 [3, 1, 2] = true := by decide +kernel
theorem subd14_3_1016 : subd14_3 [3, 1, 3] = true := by decide +kernel
theorem subd14_3_1017 : subd14_3 [3, 1, 4] = true := by decide +kernel
theorem subd14_3_1018 : subd14_3 [3, 1, 5] = true := by decide +kernel
theorem subd14_3_1019 : subd14_3 [3, 1, 6] = true := by decide +kernel
theorem subd14_3_1020 : subd14_3 [3, 1, 7] = true := by decide +kernel
theorem subd14_3_1021 : subd14_3 [3, 2, -9] = true := by decide +kernel
theorem subd14_3_1022 : subd14_3 [3, 2, -8] = true := by decide +kernel
theorem subd14_3_1023 : subd14_3 [3, 2, -7] = true := by decide +kernel
theorem sbd14_3_31 : ∀ q ∈ blkd14_3_31, subd14_3 q = true := by
  unfold blkd14_3_31
  exact List.forall_mem_cons.2 ⟨subd14_3_992, List.forall_mem_cons.2 ⟨subd14_3_993, List.forall_mem_cons.2 ⟨subd14_3_994, List.forall_mem_cons.2 ⟨subd14_3_995, List.forall_mem_cons.2 ⟨subd14_3_996, List.forall_mem_cons.2 ⟨subd14_3_997, List.forall_mem_cons.2 ⟨subd14_3_998, List.forall_mem_cons.2 ⟨subd14_3_999, List.forall_mem_cons.2 ⟨subd14_3_1000, List.forall_mem_cons.2 ⟨subd14_3_1001, List.forall_mem_cons.2 ⟨subd14_3_1002, List.forall_mem_cons.2 ⟨subd14_3_1003, List.forall_mem_cons.2 ⟨subd14_3_1004, List.forall_mem_cons.2 ⟨subd14_3_1005, List.forall_mem_cons.2 ⟨subd14_3_1006, List.forall_mem_cons.2 ⟨subd14_3_1007, List.forall_mem_cons.2 ⟨subd14_3_1008, List.forall_mem_cons.2 ⟨subd14_3_1009, List.forall_mem_cons.2 ⟨subd14_3_1010, List.forall_mem_cons.2 ⟨subd14_3_1011, List.forall_mem_cons.2 ⟨subd14_3_1012, List.forall_mem_cons.2 ⟨subd14_3_1013, List.forall_mem_cons.2 ⟨subd14_3_1014, List.forall_mem_cons.2 ⟨subd14_3_1015, List.forall_mem_cons.2 ⟨subd14_3_1016, List.forall_mem_cons.2 ⟨subd14_3_1017, List.forall_mem_cons.2 ⟨subd14_3_1018, List.forall_mem_cons.2 ⟨subd14_3_1019, List.forall_mem_cons.2 ⟨subd14_3_1020, List.forall_mem_cons.2 ⟨subd14_3_1021, List.forall_mem_cons.2 ⟨subd14_3_1022, List.forall_mem_cons.2 ⟨subd14_3_1023, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_3_1024 : subd14_3 [3, 2, -6] = true := by decide +kernel
theorem subd14_3_1025 : subd14_3 [3, 2, -5] = true := by decide +kernel
theorem subd14_3_1026 : subd14_3 [3, 2, -4] = true := by decide +kernel
theorem subd14_3_1027 : subd14_3 [3, 2, -3] = true := by decide +kernel
theorem subd14_3_1028 : subd14_3 [3, 2, -2] = true := by decide +kernel
theorem subd14_3_1029 : subd14_3 [3, 2, -1] = true := by decide +kernel
theorem subd14_3_1030 : subd14_3 [3, 2, 0] = true := by decide +kernel
theorem subd14_3_1031 : subd14_3 [3, 2, 1] = true := by decide +kernel
theorem subd14_3_1032 : subd14_3 [3, 2, 2] = true := by decide +kernel
theorem subd14_3_1033 : subd14_3 [3, 2, 3] = true := by decide +kernel
theorem subd14_3_1034 : subd14_3 [3, 2, 4] = true := by decide +kernel
theorem subd14_3_1035 : subd14_3 [3, 2, 5] = true := by decide +kernel
theorem subd14_3_1036 : subd14_3 [3, 2, 6] = true := by decide +kernel
theorem subd14_3_1037 : subd14_3 [3, 3] = true := by decide +kernel
theorem subd14_3_1038 : subd14_3 [3, 4] = true := by decide +kernel
theorem subd14_3_1039 : subd14_3 [4, -4] = true := by decide +kernel
theorem subd14_3_1040 : subd14_3 [4, -3] = true := by decide +kernel
theorem subd14_3_1041 : subd14_3 [4, -2] = true := by decide +kernel
theorem subd14_3_1042 : subd14_3 [4, -1, -7] = true := by decide +kernel
theorem subd14_3_1043 : subd14_3 [4, -1, -6] = true := by decide +kernel
theorem subd14_3_1044 : subd14_3 [4, -1, -5] = true := by decide +kernel
theorem subd14_3_1045 : subd14_3 [4, -1, -4] = true := by decide +kernel
theorem subd14_3_1046 : subd14_3 [4, -1, -3] = true := by decide +kernel
theorem subd14_3_1047 : subd14_3 [4, -1, -2] = true := by decide +kernel
theorem subd14_3_1048 : subd14_3 [4, -1, -1] = true := by decide +kernel
theorem subd14_3_1049 : subd14_3 [4, -1, 0] = true := by decide +kernel
theorem subd14_3_1050 : subd14_3 [4, -1, 1] = true := by decide +kernel
theorem subd14_3_1051 : subd14_3 [4, -1, 2] = true := by decide +kernel
theorem subd14_3_1052 : subd14_3 [4, -1, 3] = true := by decide +kernel
theorem subd14_3_1053 : subd14_3 [4, -1, 4] = true := by decide +kernel
theorem subd14_3_1054 : subd14_3 [4, -1, 5] = true := by decide +kernel
theorem subd14_3_1055 : subd14_3 [4, -1, 6] = true := by decide +kernel
theorem sbd14_3_32 : ∀ q ∈ blkd14_3_32, subd14_3 q = true := by
  unfold blkd14_3_32
  exact List.forall_mem_cons.2 ⟨subd14_3_1024, List.forall_mem_cons.2 ⟨subd14_3_1025, List.forall_mem_cons.2 ⟨subd14_3_1026, List.forall_mem_cons.2 ⟨subd14_3_1027, List.forall_mem_cons.2 ⟨subd14_3_1028, List.forall_mem_cons.2 ⟨subd14_3_1029, List.forall_mem_cons.2 ⟨subd14_3_1030, List.forall_mem_cons.2 ⟨subd14_3_1031, List.forall_mem_cons.2 ⟨subd14_3_1032, List.forall_mem_cons.2 ⟨subd14_3_1033, List.forall_mem_cons.2 ⟨subd14_3_1034, List.forall_mem_cons.2 ⟨subd14_3_1035, List.forall_mem_cons.2 ⟨subd14_3_1036, List.forall_mem_cons.2 ⟨subd14_3_1037, List.forall_mem_cons.2 ⟨subd14_3_1038, List.forall_mem_cons.2 ⟨subd14_3_1039, List.forall_mem_cons.2 ⟨subd14_3_1040, List.forall_mem_cons.2 ⟨subd14_3_1041, List.forall_mem_cons.2 ⟨subd14_3_1042, List.forall_mem_cons.2 ⟨subd14_3_1043, List.forall_mem_cons.2 ⟨subd14_3_1044, List.forall_mem_cons.2 ⟨subd14_3_1045, List.forall_mem_cons.2 ⟨subd14_3_1046, List.forall_mem_cons.2 ⟨subd14_3_1047, List.forall_mem_cons.2 ⟨subd14_3_1048, List.forall_mem_cons.2 ⟨subd14_3_1049, List.forall_mem_cons.2 ⟨subd14_3_1050, List.forall_mem_cons.2 ⟨subd14_3_1051, List.forall_mem_cons.2 ⟨subd14_3_1052, List.forall_mem_cons.2 ⟨subd14_3_1053, List.forall_mem_cons.2 ⟨subd14_3_1054, List.forall_mem_cons.2 ⟨subd14_3_1055, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_3_1056 : subd14_3 [4, -1, 7] = true := by decide +kernel
theorem subd14_3_1057 : subd14_3 [4, 0, -8] = true := by decide +kernel
theorem subd14_3_1058 : subd14_3 [4, 0, -7] = true := by decide +kernel
theorem subd14_3_1059 : subd14_3 [4, 0, -6] = true := by decide +kernel
theorem subd14_3_1060 : subd14_3 [4, 0, -5] = true := by decide +kernel
theorem subd14_3_1061 : subd14_3 [4, 0, -4] = true := by decide +kernel
theorem subd14_3_1062 : subd14_3 [4, 0, -3] = true := by decide +kernel
theorem subd14_3_1063 : subd14_3 [4, 0, -2] = true := by decide +kernel
theorem subd14_3_1064 : subd14_3 [4, 0, -1] = true := by decide +kernel
theorem subd14_3_1065 : subd14_3 [4, 0, 0] = true := by decide +kernel
theorem subd14_3_1066 : subd14_3 [4, 0, 1] = true := by decide +kernel
theorem subd14_3_1067 : subd14_3 [4, 0, 2] = true := by decide +kernel
theorem subd14_3_1068 : subd14_3 [4, 0, 3] = true := by decide +kernel
theorem subd14_3_1069 : subd14_3 [4, 0, 4] = true := by decide +kernel
theorem subd14_3_1070 : subd14_3 [4, 0, 5] = true := by decide +kernel
theorem subd14_3_1071 : subd14_3 [4, 0, 6] = true := by decide +kernel
theorem subd14_3_1072 : subd14_3 [4, 1, -8] = true := by decide +kernel
theorem subd14_3_1073 : subd14_3 [4, 1, -7] = true := by decide +kernel
theorem subd14_3_1074 : subd14_3 [4, 1, -6] = true := by decide +kernel
theorem subd14_3_1075 : subd14_3 [4, 1, -5] = true := by decide +kernel
theorem subd14_3_1076 : subd14_3 [4, 1, -4] = true := by decide +kernel
theorem subd14_3_1077 : subd14_3 [4, 1, -3] = true := by decide +kernel
theorem subd14_3_1078 : subd14_3 [4, 1, -2] = true := by decide +kernel
theorem subd14_3_1079 : subd14_3 [4, 1, -1] = true := by decide +kernel
theorem subd14_3_1080 : subd14_3 [4, 1, 0] = true := by decide +kernel
theorem subd14_3_1081 : subd14_3 [4, 1, 1] = true := by decide +kernel
theorem subd14_3_1082 : subd14_3 [4, 1, 2] = true := by decide +kernel
theorem subd14_3_1083 : subd14_3 [4, 1, 3] = true := by decide +kernel
theorem subd14_3_1084 : subd14_3 [4, 1, 4] = true := by decide +kernel
theorem subd14_3_1085 : subd14_3 [4, 1, 5] = true := by decide +kernel
theorem subd14_3_1086 : subd14_3 [4, 2] = true := by decide +kernel
theorem subd14_3_1087 : subd14_3 [4, 3] = true := by decide +kernel
theorem sbd14_3_33 : ∀ q ∈ blkd14_3_33, subd14_3 q = true := by
  unfold blkd14_3_33
  exact List.forall_mem_cons.2 ⟨subd14_3_1056, List.forall_mem_cons.2 ⟨subd14_3_1057, List.forall_mem_cons.2 ⟨subd14_3_1058, List.forall_mem_cons.2 ⟨subd14_3_1059, List.forall_mem_cons.2 ⟨subd14_3_1060, List.forall_mem_cons.2 ⟨subd14_3_1061, List.forall_mem_cons.2 ⟨subd14_3_1062, List.forall_mem_cons.2 ⟨subd14_3_1063, List.forall_mem_cons.2 ⟨subd14_3_1064, List.forall_mem_cons.2 ⟨subd14_3_1065, List.forall_mem_cons.2 ⟨subd14_3_1066, List.forall_mem_cons.2 ⟨subd14_3_1067, List.forall_mem_cons.2 ⟨subd14_3_1068, List.forall_mem_cons.2 ⟨subd14_3_1069, List.forall_mem_cons.2 ⟨subd14_3_1070, List.forall_mem_cons.2 ⟨subd14_3_1071, List.forall_mem_cons.2 ⟨subd14_3_1072, List.forall_mem_cons.2 ⟨subd14_3_1073, List.forall_mem_cons.2 ⟨subd14_3_1074, List.forall_mem_cons.2 ⟨subd14_3_1075, List.forall_mem_cons.2 ⟨subd14_3_1076, List.forall_mem_cons.2 ⟨subd14_3_1077, List.forall_mem_cons.2 ⟨subd14_3_1078, List.forall_mem_cons.2 ⟨subd14_3_1079, List.forall_mem_cons.2 ⟨subd14_3_1080, List.forall_mem_cons.2 ⟨subd14_3_1081, List.forall_mem_cons.2 ⟨subd14_3_1082, List.forall_mem_cons.2 ⟨subd14_3_1083, List.forall_mem_cons.2 ⟨subd14_3_1084, List.forall_mem_cons.2 ⟨subd14_3_1085, List.forall_mem_cons.2 ⟨subd14_3_1086, List.forall_mem_cons.2 ⟨subd14_3_1087, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
