import ReflectZphi.Data.Cert5.C121.Base

namespace ReflectZphi.Data.Cert5.C121

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd5_2_672 : subd5_2 [0, 1, -6] = true := by decide +kernel
theorem subd5_2_673 : subd5_2 [0, 1, -5] = true := by decide +kernel
theorem subd5_2_674 : subd5_2 [0, 1, -4] = true := by decide +kernel
theorem subd5_2_675 : subd5_2 [0, 1, -3] = true := by decide +kernel
theorem subd5_2_676 : subd5_2 [0, 1, -2] = true := by decide +kernel
theorem subd5_2_677 : subd5_2 [0, 1, -1] = true := by decide +kernel
theorem subd5_2_678 : subd5_2 [0, 1, 0] = true := by decide +kernel
theorem subd5_2_679 : subd5_2 [0, 1, 1] = true := by decide +kernel
theorem subd5_2_680 : subd5_2 [0, 1, 2] = true := by decide +kernel
theorem subd5_2_681 : subd5_2 [0, 1, 3] = true := by decide +kernel
theorem subd5_2_682 : subd5_2 [0, 1, 4] = true := by decide +kernel
theorem subd5_2_683 : subd5_2 [0, 1, 5] = true := by decide +kernel
theorem subd5_2_684 : subd5_2 [0, 1, 6] = true := by decide +kernel
theorem subd5_2_685 : subd5_2 [0, 1, 7] = true := by decide +kernel
theorem subd5_2_686 : subd5_2 [0, 1, 8] = true := by decide +kernel
theorem subd5_2_687 : subd5_2 [0, 2, -10] = true := by decide +kernel
theorem subd5_2_688 : subd5_2 [0, 2, -9] = true := by decide +kernel
theorem subd5_2_689 : subd5_2 [0, 2, -8] = true := by decide +kernel
theorem subd5_2_690 : subd5_2 [0, 2, -7] = true := by decide +kernel
theorem subd5_2_691 : subd5_2 [0, 2, -6] = true := by decide +kernel
theorem subd5_2_692 : subd5_2 [0, 2, -5] = true := by decide +kernel
theorem subd5_2_693 : subd5_2 [0, 2, -4] = true := by decide +kernel
theorem subd5_2_694 : subd5_2 [0, 2, -3] = true := by decide +kernel
theorem subd5_2_695 : subd5_2 [0, 2, -2] = true := by decide +kernel
theorem subd5_2_696 : subd5_2 [0, 2, -1] = true := by decide +kernel
theorem subd5_2_697 : subd5_2 [0, 2, 0] = true := by decide +kernel
theorem subd5_2_698 : subd5_2 [0, 2, 1] = true := by decide +kernel
theorem subd5_2_699 : subd5_2 [0, 2, 2] = true := by decide +kernel
theorem subd5_2_700 : subd5_2 [0, 2, 3] = true := by decide +kernel
theorem subd5_2_701 : subd5_2 [0, 2, 4] = true := by decide +kernel
theorem subd5_2_702 : subd5_2 [0, 2, 5] = true := by decide +kernel
theorem subd5_2_703 : subd5_2 [0, 2, 6] = true := by decide +kernel
theorem sbd5_2_21 : ∀ q ∈ blkd5_2_21, subd5_2 q = true := by
  unfold blkd5_2_21
  exact List.forall_mem_cons.2 ⟨subd5_2_672, List.forall_mem_cons.2 ⟨subd5_2_673, List.forall_mem_cons.2 ⟨subd5_2_674, List.forall_mem_cons.2 ⟨subd5_2_675, List.forall_mem_cons.2 ⟨subd5_2_676, List.forall_mem_cons.2 ⟨subd5_2_677, List.forall_mem_cons.2 ⟨subd5_2_678, List.forall_mem_cons.2 ⟨subd5_2_679, List.forall_mem_cons.2 ⟨subd5_2_680, List.forall_mem_cons.2 ⟨subd5_2_681, List.forall_mem_cons.2 ⟨subd5_2_682, List.forall_mem_cons.2 ⟨subd5_2_683, List.forall_mem_cons.2 ⟨subd5_2_684, List.forall_mem_cons.2 ⟨subd5_2_685, List.forall_mem_cons.2 ⟨subd5_2_686, List.forall_mem_cons.2 ⟨subd5_2_687, List.forall_mem_cons.2 ⟨subd5_2_688, List.forall_mem_cons.2 ⟨subd5_2_689, List.forall_mem_cons.2 ⟨subd5_2_690, List.forall_mem_cons.2 ⟨subd5_2_691, List.forall_mem_cons.2 ⟨subd5_2_692, List.forall_mem_cons.2 ⟨subd5_2_693, List.forall_mem_cons.2 ⟨subd5_2_694, List.forall_mem_cons.2 ⟨subd5_2_695, List.forall_mem_cons.2 ⟨subd5_2_696, List.forall_mem_cons.2 ⟨subd5_2_697, List.forall_mem_cons.2 ⟨subd5_2_698, List.forall_mem_cons.2 ⟨subd5_2_699, List.forall_mem_cons.2 ⟨subd5_2_700, List.forall_mem_cons.2 ⟨subd5_2_701, List.forall_mem_cons.2 ⟨subd5_2_702, List.forall_mem_cons.2 ⟨subd5_2_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_704 : subd5_2 [0, 2, 7] = true := by decide +kernel
theorem subd5_2_705 : subd5_2 [0, 3, -9] = true := by decide +kernel
theorem subd5_2_706 : subd5_2 [0, 3, -8] = true := by decide +kernel
theorem subd5_2_707 : subd5_2 [0, 3, -7] = true := by decide +kernel
theorem subd5_2_708 : subd5_2 [0, 3, -6] = true := by decide +kernel
theorem subd5_2_709 : subd5_2 [0, 3, -5] = true := by decide +kernel
theorem subd5_2_710 : subd5_2 [0, 3, -4] = true := by decide +kernel
theorem subd5_2_711 : subd5_2 [0, 3, -3] = true := by decide +kernel
theorem subd5_2_712 : subd5_2 [0, 3, -2] = true := by decide +kernel
theorem subd5_2_713 : subd5_2 [0, 3, -1] = true := by decide +kernel
theorem subd5_2_714 : subd5_2 [0, 3, 0] = true := by decide +kernel
theorem subd5_2_715 : subd5_2 [0, 3, 1] = true := by decide +kernel
theorem subd5_2_716 : subd5_2 [0, 3, 2] = true := by decide +kernel
theorem subd5_2_717 : subd5_2 [0, 3, 3] = true := by decide +kernel
theorem subd5_2_718 : subd5_2 [0, 3, 4] = true := by decide +kernel
theorem subd5_2_719 : subd5_2 [0, 3, 5] = true := by decide +kernel
theorem subd5_2_720 : subd5_2 [0, 3, 6] = true := by decide +kernel
theorem subd5_2_721 : subd5_2 [0, 3, 7] = true := by decide +kernel
theorem subd5_2_722 : subd5_2 [0, 4, -9] = true := by decide +kernel
theorem subd5_2_723 : subd5_2 [0, 4, -8] = true := by decide +kernel
theorem subd5_2_724 : subd5_2 [0, 4, -7] = true := by decide +kernel
theorem subd5_2_725 : subd5_2 [0, 4, -6] = true := by decide +kernel
theorem subd5_2_726 : subd5_2 [0, 4, -5] = true := by decide +kernel
theorem subd5_2_727 : subd5_2 [0, 4, -4] = true := by decide +kernel
theorem subd5_2_728 : subd5_2 [0, 4, -3] = true := by decide +kernel
theorem subd5_2_729 : subd5_2 [0, 4, -2] = true := by decide +kernel
theorem subd5_2_730 : subd5_2 [0, 4, -1] = true := by decide +kernel
theorem subd5_2_731 : subd5_2 [0, 4, 0] = true := by decide +kernel
theorem subd5_2_732 : subd5_2 [0, 4, 1] = true := by decide +kernel
theorem subd5_2_733 : subd5_2 [0, 4, 2] = true := by decide +kernel
theorem subd5_2_734 : subd5_2 [0, 4, 3] = true := by decide +kernel
theorem subd5_2_735 : subd5_2 [0, 4, 4] = true := by decide +kernel
theorem sbd5_2_22 : ∀ q ∈ blkd5_2_22, subd5_2 q = true := by
  unfold blkd5_2_22
  exact List.forall_mem_cons.2 ⟨subd5_2_704, List.forall_mem_cons.2 ⟨subd5_2_705, List.forall_mem_cons.2 ⟨subd5_2_706, List.forall_mem_cons.2 ⟨subd5_2_707, List.forall_mem_cons.2 ⟨subd5_2_708, List.forall_mem_cons.2 ⟨subd5_2_709, List.forall_mem_cons.2 ⟨subd5_2_710, List.forall_mem_cons.2 ⟨subd5_2_711, List.forall_mem_cons.2 ⟨subd5_2_712, List.forall_mem_cons.2 ⟨subd5_2_713, List.forall_mem_cons.2 ⟨subd5_2_714, List.forall_mem_cons.2 ⟨subd5_2_715, List.forall_mem_cons.2 ⟨subd5_2_716, List.forall_mem_cons.2 ⟨subd5_2_717, List.forall_mem_cons.2 ⟨subd5_2_718, List.forall_mem_cons.2 ⟨subd5_2_719, List.forall_mem_cons.2 ⟨subd5_2_720, List.forall_mem_cons.2 ⟨subd5_2_721, List.forall_mem_cons.2 ⟨subd5_2_722, List.forall_mem_cons.2 ⟨subd5_2_723, List.forall_mem_cons.2 ⟨subd5_2_724, List.forall_mem_cons.2 ⟨subd5_2_725, List.forall_mem_cons.2 ⟨subd5_2_726, List.forall_mem_cons.2 ⟨subd5_2_727, List.forall_mem_cons.2 ⟨subd5_2_728, List.forall_mem_cons.2 ⟨subd5_2_729, List.forall_mem_cons.2 ⟨subd5_2_730, List.forall_mem_cons.2 ⟨subd5_2_731, List.forall_mem_cons.2 ⟨subd5_2_732, List.forall_mem_cons.2 ⟨subd5_2_733, List.forall_mem_cons.2 ⟨subd5_2_734, List.forall_mem_cons.2 ⟨subd5_2_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_736 : subd5_2 [0, 4, 5] = true := by decide +kernel
theorem subd5_2_737 : subd5_2 [0, 4, 6] = true := by decide +kernel
theorem subd5_2_738 : subd5_2 [0, 5, -8] = true := by decide +kernel
theorem subd5_2_739 : subd5_2 [0, 5, -7] = true := by decide +kernel
theorem subd5_2_740 : subd5_2 [0, 5, -6] = true := by decide +kernel
theorem subd5_2_741 : subd5_2 [0, 5, -5] = true := by decide +kernel
theorem subd5_2_742 : subd5_2 [0, 5, -4] = true := by decide +kernel
theorem subd5_2_743 : subd5_2 [0, 5, -3] = true := by decide +kernel
theorem subd5_2_744 : subd5_2 [0, 5, -2] = true := by decide +kernel
theorem subd5_2_745 : subd5_2 [0, 5, -1] = true := by decide +kernel
theorem subd5_2_746 : subd5_2 [0, 5, 0] = true := by decide +kernel
theorem subd5_2_747 : subd5_2 [0, 5, 1] = true := by decide +kernel
theorem subd5_2_748 : subd5_2 [0, 5, 2] = true := by decide +kernel
theorem subd5_2_749 : subd5_2 [0, 5, 3] = true := by decide +kernel
theorem subd5_2_750 : subd5_2 [0, 5, 4] = true := by decide +kernel
theorem subd5_2_751 : subd5_2 [0, 5, 5] = true := by decide +kernel
theorem subd5_2_752 : subd5_2 [0, 6] = true := by decide +kernel
theorem subd5_2_753 : subd5_2 [0, 7] = true := by decide +kernel
theorem subd5_2_754 : subd5_2 [1, -7] = true := by decide +kernel
theorem subd5_2_755 : subd5_2 [1, -6] = true := by decide +kernel
theorem subd5_2_756 : subd5_2 [1, -5] = true := by decide +kernel
theorem subd5_2_757 : subd5_2 [1, -4, -6] = true := by decide +kernel
theorem subd5_2_758 : subd5_2 [1, -4, -5] = true := by decide +kernel
theorem subd5_2_759 : subd5_2 [1, -4, -4] = true := by decide +kernel
theorem subd5_2_760 : subd5_2 [1, -4, -3] = true := by decide +kernel
theorem subd5_2_761 : subd5_2 [1, -4, -2] = true := by decide +kernel
theorem subd5_2_762 : subd5_2 [1, -4, -1] = true := by decide +kernel
theorem subd5_2_763 : subd5_2 [1, -4, 0] = true := by decide +kernel
theorem subd5_2_764 : subd5_2 [1, -4, 1] = true := by decide +kernel
theorem subd5_2_765 : subd5_2 [1, -4, 2] = true := by decide +kernel
theorem subd5_2_766 : subd5_2 [1, -4, 3] = true := by decide +kernel
theorem subd5_2_767 : subd5_2 [1, -4, 4] = true := by decide +kernel
theorem sbd5_2_23 : ∀ q ∈ blkd5_2_23, subd5_2 q = true := by
  unfold blkd5_2_23
  exact List.forall_mem_cons.2 ⟨subd5_2_736, List.forall_mem_cons.2 ⟨subd5_2_737, List.forall_mem_cons.2 ⟨subd5_2_738, List.forall_mem_cons.2 ⟨subd5_2_739, List.forall_mem_cons.2 ⟨subd5_2_740, List.forall_mem_cons.2 ⟨subd5_2_741, List.forall_mem_cons.2 ⟨subd5_2_742, List.forall_mem_cons.2 ⟨subd5_2_743, List.forall_mem_cons.2 ⟨subd5_2_744, List.forall_mem_cons.2 ⟨subd5_2_745, List.forall_mem_cons.2 ⟨subd5_2_746, List.forall_mem_cons.2 ⟨subd5_2_747, List.forall_mem_cons.2 ⟨subd5_2_748, List.forall_mem_cons.2 ⟨subd5_2_749, List.forall_mem_cons.2 ⟨subd5_2_750, List.forall_mem_cons.2 ⟨subd5_2_751, List.forall_mem_cons.2 ⟨subd5_2_752, List.forall_mem_cons.2 ⟨subd5_2_753, List.forall_mem_cons.2 ⟨subd5_2_754, List.forall_mem_cons.2 ⟨subd5_2_755, List.forall_mem_cons.2 ⟨subd5_2_756, List.forall_mem_cons.2 ⟨subd5_2_757, List.forall_mem_cons.2 ⟨subd5_2_758, List.forall_mem_cons.2 ⟨subd5_2_759, List.forall_mem_cons.2 ⟨subd5_2_760, List.forall_mem_cons.2 ⟨subd5_2_761, List.forall_mem_cons.2 ⟨subd5_2_762, List.forall_mem_cons.2 ⟨subd5_2_763, List.forall_mem_cons.2 ⟨subd5_2_764, List.forall_mem_cons.2 ⟨subd5_2_765, List.forall_mem_cons.2 ⟨subd5_2_766, List.forall_mem_cons.2 ⟨subd5_2_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_768 : subd5_2 [1, -4, 5] = true := by decide +kernel
theorem subd5_2_769 : subd5_2 [1, -4, 6] = true := by decide +kernel
theorem subd5_2_770 : subd5_2 [1, -4, 7] = true := by decide +kernel
theorem subd5_2_771 : subd5_2 [1, -4, 8] = true := by decide +kernel
theorem subd5_2_772 : subd5_2 [1, -3, -7] = true := by decide +kernel
theorem subd5_2_773 : subd5_2 [1, -3, -6] = true := by decide +kernel
theorem subd5_2_774 : subd5_2 [1, -3, -5] = true := by decide +kernel
theorem subd5_2_775 : subd5_2 [1, -3, -4] = true := by decide +kernel
theorem subd5_2_776 : subd5_2 [1, -3, -3] = true := by decide +kernel
theorem subd5_2_777 : subd5_2 [1, -3, -2] = true := by decide +kernel
theorem subd5_2_778 : subd5_2 [1, -3, -1] = true := by decide +kernel
theorem subd5_2_779 : subd5_2 [1, -3, 0] = true := by decide +kernel
theorem subd5_2_780 : subd5_2 [1, -3, 1] = true := by decide +kernel
theorem subd5_2_781 : subd5_2 [1, -3, 2] = true := by decide +kernel
theorem subd5_2_782 : subd5_2 [1, -3, 3] = true := by decide +kernel
theorem subd5_2_783 : subd5_2 [1, -3, 4] = true := by decide +kernel
theorem subd5_2_784 : subd5_2 [1, -3, 5] = true := by decide +kernel
theorem subd5_2_785 : subd5_2 [1, -3, 6] = true := by decide +kernel
theorem subd5_2_786 : subd5_2 [1, -3, 7] = true := by decide +kernel
theorem subd5_2_787 : subd5_2 [1, -3, 8] = true := by decide +kernel
theorem subd5_2_788 : subd5_2 [1, -2, -8] = true := by decide +kernel
theorem subd5_2_789 : subd5_2 [1, -2, -7] = true := by decide +kernel
theorem subd5_2_790 : subd5_2 [1, -2, -6] = true := by decide +kernel
theorem subd5_2_791 : subd5_2 [1, -2, -5] = true := by decide +kernel
theorem subd5_2_792 : subd5_2 [1, -2, -4] = true := by decide +kernel
theorem subd5_2_793 : subd5_2 [1, -2, -3] = true := by decide +kernel
theorem subd5_2_794 : subd5_2 [1, -2, -2] = true := by decide +kernel
theorem subd5_2_795 : subd5_2 [1, -2, -1] = true := by decide +kernel
theorem subd5_2_796 : subd5_2 [1, -2, 0] = true := by decide +kernel
theorem subd5_2_797 : subd5_2 [1, -2, 1] = true := by decide +kernel
theorem subd5_2_798 : subd5_2 [1, -2, 2] = true := by decide +kernel
theorem subd5_2_799 : subd5_2 [1, -2, 3] = true := by decide +kernel
theorem sbd5_2_24 : ∀ q ∈ blkd5_2_24, subd5_2 q = true := by
  unfold blkd5_2_24
  exact List.forall_mem_cons.2 ⟨subd5_2_768, List.forall_mem_cons.2 ⟨subd5_2_769, List.forall_mem_cons.2 ⟨subd5_2_770, List.forall_mem_cons.2 ⟨subd5_2_771, List.forall_mem_cons.2 ⟨subd5_2_772, List.forall_mem_cons.2 ⟨subd5_2_773, List.forall_mem_cons.2 ⟨subd5_2_774, List.forall_mem_cons.2 ⟨subd5_2_775, List.forall_mem_cons.2 ⟨subd5_2_776, List.forall_mem_cons.2 ⟨subd5_2_777, List.forall_mem_cons.2 ⟨subd5_2_778, List.forall_mem_cons.2 ⟨subd5_2_779, List.forall_mem_cons.2 ⟨subd5_2_780, List.forall_mem_cons.2 ⟨subd5_2_781, List.forall_mem_cons.2 ⟨subd5_2_782, List.forall_mem_cons.2 ⟨subd5_2_783, List.forall_mem_cons.2 ⟨subd5_2_784, List.forall_mem_cons.2 ⟨subd5_2_785, List.forall_mem_cons.2 ⟨subd5_2_786, List.forall_mem_cons.2 ⟨subd5_2_787, List.forall_mem_cons.2 ⟨subd5_2_788, List.forall_mem_cons.2 ⟨subd5_2_789, List.forall_mem_cons.2 ⟨subd5_2_790, List.forall_mem_cons.2 ⟨subd5_2_791, List.forall_mem_cons.2 ⟨subd5_2_792, List.forall_mem_cons.2 ⟨subd5_2_793, List.forall_mem_cons.2 ⟨subd5_2_794, List.forall_mem_cons.2 ⟨subd5_2_795, List.forall_mem_cons.2 ⟨subd5_2_796, List.forall_mem_cons.2 ⟨subd5_2_797, List.forall_mem_cons.2 ⟨subd5_2_798, List.forall_mem_cons.2 ⟨subd5_2_799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_800 : subd5_2 [1, -2, 4] = true := by decide +kernel
theorem subd5_2_801 : subd5_2 [1, -2, 5] = true := by decide +kernel
theorem subd5_2_802 : subd5_2 [1, -2, 6] = true := by decide +kernel
theorem subd5_2_803 : subd5_2 [1, -2, 7] = true := by decide +kernel
theorem subd5_2_804 : subd5_2 [1, -2, 8] = true := by decide +kernel
theorem subd5_2_805 : subd5_2 [1, -2, 9] = true := by decide +kernel
theorem subd5_2_806 : subd5_2 [1, -1, -8] = true := by decide +kernel
theorem subd5_2_807 : subd5_2 [1, -1, -7] = true := by decide +kernel
theorem subd5_2_808 : subd5_2 [1, -1, -6] = true := by decide +kernel
theorem subd5_2_809 : subd5_2 [1, -1, -5] = true := by decide +kernel
theorem subd5_2_810 : subd5_2 [1, -1, -4] = true := by decide +kernel
theorem subd5_2_811 : subd5_2 [1, -1, -3] = true := by decide +kernel
theorem subd5_2_812 : subd5_2 [1, -1, -2] = true := by decide +kernel
theorem subd5_2_813 : subd5_2 [1, -1, -1] = true := by decide +kernel
theorem subd5_2_814 : subd5_2 [1, -1, 0] = true := by decide +kernel
theorem subd5_2_815 : subd5_2 [1, -1, 1] = true := by decide +kernel
theorem subd5_2_816 : subd5_2 [1, -1, 2] = true := by decide +kernel
theorem subd5_2_817 : subd5_2 [1, -1, 3] = true := by decide +kernel
theorem subd5_2_818 : subd5_2 [1, -1, 4] = true := by decide +kernel
theorem subd5_2_819 : subd5_2 [1, -1, 5] = true := by decide +kernel
theorem subd5_2_820 : subd5_2 [1, -1, 6] = true := by decide +kernel
theorem subd5_2_821 : subd5_2 [1, -1, 7] = true := by decide +kernel
theorem subd5_2_822 : subd5_2 [1, -1, 8] = true := by decide +kernel
theorem subd5_2_823 : subd5_2 [1, -1, 9] = true := by decide +kernel
theorem subd5_2_824 : subd5_2 [1, 0, -9] = true := by decide +kernel
theorem subd5_2_825 : subd5_2 [1, 0, -8] = true := by decide +kernel
theorem subd5_2_826 : subd5_2 [1, 0, -7] = true := by decide +kernel
theorem subd5_2_827 : subd5_2 [1, 0, -6] = true := by decide +kernel
theorem subd5_2_828 : subd5_2 [1, 0, -5] = true := by decide +kernel
theorem subd5_2_829 : subd5_2 [1, 0, -4] = true := by decide +kernel
theorem subd5_2_830 : subd5_2 [1, 0, -3] = true := by decide +kernel
theorem subd5_2_831 : subd5_2 [1, 0, -2] = true := by decide +kernel
theorem sbd5_2_25 : ∀ q ∈ blkd5_2_25, subd5_2 q = true := by
  unfold blkd5_2_25
  exact List.forall_mem_cons.2 ⟨subd5_2_800, List.forall_mem_cons.2 ⟨subd5_2_801, List.forall_mem_cons.2 ⟨subd5_2_802, List.forall_mem_cons.2 ⟨subd5_2_803, List.forall_mem_cons.2 ⟨subd5_2_804, List.forall_mem_cons.2 ⟨subd5_2_805, List.forall_mem_cons.2 ⟨subd5_2_806, List.forall_mem_cons.2 ⟨subd5_2_807, List.forall_mem_cons.2 ⟨subd5_2_808, List.forall_mem_cons.2 ⟨subd5_2_809, List.forall_mem_cons.2 ⟨subd5_2_810, List.forall_mem_cons.2 ⟨subd5_2_811, List.forall_mem_cons.2 ⟨subd5_2_812, List.forall_mem_cons.2 ⟨subd5_2_813, List.forall_mem_cons.2 ⟨subd5_2_814, List.forall_mem_cons.2 ⟨subd5_2_815, List.forall_mem_cons.2 ⟨subd5_2_816, List.forall_mem_cons.2 ⟨subd5_2_817, List.forall_mem_cons.2 ⟨subd5_2_818, List.forall_mem_cons.2 ⟨subd5_2_819, List.forall_mem_cons.2 ⟨subd5_2_820, List.forall_mem_cons.2 ⟨subd5_2_821, List.forall_mem_cons.2 ⟨subd5_2_822, List.forall_mem_cons.2 ⟨subd5_2_823, List.forall_mem_cons.2 ⟨subd5_2_824, List.forall_mem_cons.2 ⟨subd5_2_825, List.forall_mem_cons.2 ⟨subd5_2_826, List.forall_mem_cons.2 ⟨subd5_2_827, List.forall_mem_cons.2 ⟨subd5_2_828, List.forall_mem_cons.2 ⟨subd5_2_829, List.forall_mem_cons.2 ⟨subd5_2_830, List.forall_mem_cons.2 ⟨subd5_2_831, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_832 : subd5_2 [1, 0, -1] = true := by decide +kernel
theorem subd5_2_833 : subd5_2 [1, 0, 0] = true := by decide +kernel
theorem subd5_2_834 : subd5_2 [1, 0, 1] = true := by decide +kernel
theorem subd5_2_835 : subd5_2 [1, 0, 2] = true := by decide +kernel
theorem subd5_2_836 : subd5_2 [1, 0, 3] = true := by decide +kernel
theorem subd5_2_837 : subd5_2 [1, 0, 4] = true := by decide +kernel
theorem subd5_2_838 : subd5_2 [1, 0, 5] = true := by decide +kernel
theorem subd5_2_839 : subd5_2 [1, 0, 6] = true := by decide +kernel
theorem subd5_2_840 : subd5_2 [1, 0, 7] = true := by decide +kernel
theorem subd5_2_841 : subd5_2 [1, 0, 8] = true := by decide +kernel
theorem subd5_2_842 : subd5_2 [1, 1, -9] = true := by decide +kernel
theorem subd5_2_843 : subd5_2 [1, 1, -8] = true := by decide +kernel
theorem subd5_2_844 : subd5_2 [1, 1, -7] = true := by decide +kernel
theorem subd5_2_845 : subd5_2 [1, 1, -6] = true := by decide +kernel
theorem subd5_2_846 : subd5_2 [1, 1, -5] = true := by decide +kernel
theorem subd5_2_847 : subd5_2 [1, 1, -4] = true := by decide +kernel
theorem subd5_2_848 : subd5_2 [1, 1, -3] = true := by decide +kernel
theorem subd5_2_849 : subd5_2 [1, 1, -2] = true := by decide +kernel
theorem subd5_2_850 : subd5_2 [1, 1, -1] = true := by decide +kernel
theorem subd5_2_851 : subd5_2 [1, 1, 0] = true := by decide +kernel
theorem subd5_2_852 : subd5_2 [1, 1, 1] = true := by decide +kernel
theorem subd5_2_853 : subd5_2 [1, 1, 2] = true := by decide +kernel
theorem subd5_2_854 : subd5_2 [1, 1, 3] = true := by decide +kernel
theorem subd5_2_855 : subd5_2 [1, 1, 4] = true := by decide +kernel
theorem subd5_2_856 : subd5_2 [1, 1, 5] = true := by decide +kernel
theorem subd5_2_857 : subd5_2 [1, 1, 6] = true := by decide +kernel
theorem subd5_2_858 : subd5_2 [1, 1, 7] = true := by decide +kernel
theorem subd5_2_859 : subd5_2 [1, 1, 8] = true := by decide +kernel
theorem subd5_2_860 : subd5_2 [1, 2, -9] = true := by decide +kernel
theorem subd5_2_861 : subd5_2 [1, 2, -8] = true := by decide +kernel
theorem subd5_2_862 : subd5_2 [1, 2, -7] = true := by decide +kernel
theorem subd5_2_863 : subd5_2 [1, 2, -6] = true := by decide +kernel
theorem sbd5_2_26 : ∀ q ∈ blkd5_2_26, subd5_2 q = true := by
  unfold blkd5_2_26
  exact List.forall_mem_cons.2 ⟨subd5_2_832, List.forall_mem_cons.2 ⟨subd5_2_833, List.forall_mem_cons.2 ⟨subd5_2_834, List.forall_mem_cons.2 ⟨subd5_2_835, List.forall_mem_cons.2 ⟨subd5_2_836, List.forall_mem_cons.2 ⟨subd5_2_837, List.forall_mem_cons.2 ⟨subd5_2_838, List.forall_mem_cons.2 ⟨subd5_2_839, List.forall_mem_cons.2 ⟨subd5_2_840, List.forall_mem_cons.2 ⟨subd5_2_841, List.forall_mem_cons.2 ⟨subd5_2_842, List.forall_mem_cons.2 ⟨subd5_2_843, List.forall_mem_cons.2 ⟨subd5_2_844, List.forall_mem_cons.2 ⟨subd5_2_845, List.forall_mem_cons.2 ⟨subd5_2_846, List.forall_mem_cons.2 ⟨subd5_2_847, List.forall_mem_cons.2 ⟨subd5_2_848, List.forall_mem_cons.2 ⟨subd5_2_849, List.forall_mem_cons.2 ⟨subd5_2_850, List.forall_mem_cons.2 ⟨subd5_2_851, List.forall_mem_cons.2 ⟨subd5_2_852, List.forall_mem_cons.2 ⟨subd5_2_853, List.forall_mem_cons.2 ⟨subd5_2_854, List.forall_mem_cons.2 ⟨subd5_2_855, List.forall_mem_cons.2 ⟨subd5_2_856, List.forall_mem_cons.2 ⟨subd5_2_857, List.forall_mem_cons.2 ⟨subd5_2_858, List.forall_mem_cons.2 ⟨subd5_2_859, List.forall_mem_cons.2 ⟨subd5_2_860, List.forall_mem_cons.2 ⟨subd5_2_861, List.forall_mem_cons.2 ⟨subd5_2_862, List.forall_mem_cons.2 ⟨subd5_2_863, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_864 : subd5_2 [1, 2, -5] = true := by decide +kernel
theorem subd5_2_865 : subd5_2 [1, 2, -4] = true := by decide +kernel
theorem subd5_2_866 : subd5_2 [1, 2, -3] = true := by decide +kernel
theorem subd5_2_867 : subd5_2 [1, 2, -2] = true := by decide +kernel
theorem subd5_2_868 : subd5_2 [1, 2, -1] = true := by decide +kernel
theorem subd5_2_869 : subd5_2 [1, 2, 0] = true := by decide +kernel
theorem subd5_2_870 : subd5_2 [1, 2, 1] = true := by decide +kernel
theorem subd5_2_871 : subd5_2 [1, 2, 2] = true := by decide +kernel
theorem subd5_2_872 : subd5_2 [1, 2, 3] = true := by decide +kernel
theorem subd5_2_873 : subd5_2 [1, 2, 4] = true := by decide +kernel
theorem subd5_2_874 : subd5_2 [1, 2, 5] = true := by decide +kernel
theorem subd5_2_875 : subd5_2 [1, 2, 6] = true := by decide +kernel
theorem subd5_2_876 : subd5_2 [1, 2, 7] = true := by decide +kernel
theorem subd5_2_877 : subd5_2 [1, 2, 8] = true := by decide +kernel
theorem subd5_2_878 : subd5_2 [1, 3, -9] = true := by decide +kernel
theorem subd5_2_879 : subd5_2 [1, 3, -8] = true := by decide +kernel
theorem subd5_2_880 : subd5_2 [1, 3, -7] = true := by decide +kernel
theorem subd5_2_881 : subd5_2 [1, 3, -6] = true := by decide +kernel
theorem subd5_2_882 : subd5_2 [1, 3, -5] = true := by decide +kernel
theorem subd5_2_883 : subd5_2 [1, 3, -4] = true := by decide +kernel
theorem subd5_2_884 : subd5_2 [1, 3, -3] = true := by decide +kernel
theorem subd5_2_885 : subd5_2 [1, 3, -2] = true := by decide +kernel
theorem subd5_2_886 : subd5_2 [1, 3, -1] = true := by decide +kernel
theorem subd5_2_887 : subd5_2 [1, 3, 0] = true := by decide +kernel
theorem subd5_2_888 : subd5_2 [1, 3, 1] = true := by decide +kernel
theorem subd5_2_889 : subd5_2 [1, 3, 2] = true := by decide +kernel
theorem subd5_2_890 : subd5_2 [1, 3, 3] = true := by decide +kernel
theorem subd5_2_891 : subd5_2 [1, 3, 4] = true := by decide +kernel
theorem subd5_2_892 : subd5_2 [1, 3, 5] = true := by decide +kernel
theorem subd5_2_893 : subd5_2 [1, 3, 6] = true := by decide +kernel
theorem subd5_2_894 : subd5_2 [1, 3, 7] = true := by decide +kernel
theorem subd5_2_895 : subd5_2 [1, 4, -9] = true := by decide +kernel
theorem sbd5_2_27 : ∀ q ∈ blkd5_2_27, subd5_2 q = true := by
  unfold blkd5_2_27
  exact List.forall_mem_cons.2 ⟨subd5_2_864, List.forall_mem_cons.2 ⟨subd5_2_865, List.forall_mem_cons.2 ⟨subd5_2_866, List.forall_mem_cons.2 ⟨subd5_2_867, List.forall_mem_cons.2 ⟨subd5_2_868, List.forall_mem_cons.2 ⟨subd5_2_869, List.forall_mem_cons.2 ⟨subd5_2_870, List.forall_mem_cons.2 ⟨subd5_2_871, List.forall_mem_cons.2 ⟨subd5_2_872, List.forall_mem_cons.2 ⟨subd5_2_873, List.forall_mem_cons.2 ⟨subd5_2_874, List.forall_mem_cons.2 ⟨subd5_2_875, List.forall_mem_cons.2 ⟨subd5_2_876, List.forall_mem_cons.2 ⟨subd5_2_877, List.forall_mem_cons.2 ⟨subd5_2_878, List.forall_mem_cons.2 ⟨subd5_2_879, List.forall_mem_cons.2 ⟨subd5_2_880, List.forall_mem_cons.2 ⟨subd5_2_881, List.forall_mem_cons.2 ⟨subd5_2_882, List.forall_mem_cons.2 ⟨subd5_2_883, List.forall_mem_cons.2 ⟨subd5_2_884, List.forall_mem_cons.2 ⟨subd5_2_885, List.forall_mem_cons.2 ⟨subd5_2_886, List.forall_mem_cons.2 ⟨subd5_2_887, List.forall_mem_cons.2 ⟨subd5_2_888, List.forall_mem_cons.2 ⟨subd5_2_889, List.forall_mem_cons.2 ⟨subd5_2_890, List.forall_mem_cons.2 ⟨subd5_2_891, List.forall_mem_cons.2 ⟨subd5_2_892, List.forall_mem_cons.2 ⟨subd5_2_893, List.forall_mem_cons.2 ⟨subd5_2_894, List.forall_mem_cons.2 ⟨subd5_2_895, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_896 : subd5_2 [1, 4, -8] = true := by decide +kernel
theorem subd5_2_897 : subd5_2 [1, 4, -7] = true := by decide +kernel
theorem subd5_2_898 : subd5_2 [1, 4, -6] = true := by decide +kernel
theorem subd5_2_899 : subd5_2 [1, 4, -5] = true := by decide +kernel
theorem subd5_2_900 : subd5_2 [1, 4, -4] = true := by decide +kernel
theorem subd5_2_901 : subd5_2 [1, 4, -3] = true := by decide +kernel
theorem subd5_2_902 : subd5_2 [1, 4, -2] = true := by decide +kernel
theorem subd5_2_903 : subd5_2 [1, 4, -1] = true := by decide +kernel
theorem subd5_2_904 : subd5_2 [1, 4, 0] = true := by decide +kernel
theorem subd5_2_905 : subd5_2 [1, 4, 1] = true := by decide +kernel
theorem subd5_2_906 : subd5_2 [1, 4, 2] = true := by decide +kernel
theorem subd5_2_907 : subd5_2 [1, 4, 3] = true := by decide +kernel
theorem subd5_2_908 : subd5_2 [1, 4, 4] = true := by decide +kernel
theorem subd5_2_909 : subd5_2 [1, 4, 5] = true := by decide +kernel
theorem subd5_2_910 : subd5_2 [1, 4, 6] = true := by decide +kernel
theorem subd5_2_911 : subd5_2 [1, 5, -8] = true := by decide +kernel
theorem subd5_2_912 : subd5_2 [1, 5, -7] = true := by decide +kernel
theorem subd5_2_913 : subd5_2 [1, 5, -6] = true := by decide +kernel
theorem subd5_2_914 : subd5_2 [1, 5, -5] = true := by decide +kernel
theorem subd5_2_915 : subd5_2 [1, 5, -4] = true := by decide +kernel
theorem subd5_2_916 : subd5_2 [1, 5, -3] = true := by decide +kernel
theorem subd5_2_917 : subd5_2 [1, 5, -2] = true := by decide +kernel
theorem subd5_2_918 : subd5_2 [1, 5, -1] = true := by decide +kernel
theorem subd5_2_919 : subd5_2 [1, 5, 0] = true := by decide +kernel
theorem subd5_2_920 : subd5_2 [1, 5, 1] = true := by decide +kernel
theorem subd5_2_921 : subd5_2 [1, 5, 2] = true := by decide +kernel
theorem subd5_2_922 : subd5_2 [1, 5, 3] = true := by decide +kernel
theorem subd5_2_923 : subd5_2 [1, 5, 4] = true := by decide +kernel
theorem subd5_2_924 : subd5_2 [1, 5, 5] = true := by decide +kernel
theorem subd5_2_925 : subd5_2 [1, 6] = true := by decide +kernel
theorem subd5_2_926 : subd5_2 [1, 7] = true := by decide +kernel
theorem subd5_2_927 : subd5_2 [2, -7] = true := by decide +kernel
theorem sbd5_2_28 : ∀ q ∈ blkd5_2_28, subd5_2 q = true := by
  unfold blkd5_2_28
  exact List.forall_mem_cons.2 ⟨subd5_2_896, List.forall_mem_cons.2 ⟨subd5_2_897, List.forall_mem_cons.2 ⟨subd5_2_898, List.forall_mem_cons.2 ⟨subd5_2_899, List.forall_mem_cons.2 ⟨subd5_2_900, List.forall_mem_cons.2 ⟨subd5_2_901, List.forall_mem_cons.2 ⟨subd5_2_902, List.forall_mem_cons.2 ⟨subd5_2_903, List.forall_mem_cons.2 ⟨subd5_2_904, List.forall_mem_cons.2 ⟨subd5_2_905, List.forall_mem_cons.2 ⟨subd5_2_906, List.forall_mem_cons.2 ⟨subd5_2_907, List.forall_mem_cons.2 ⟨subd5_2_908, List.forall_mem_cons.2 ⟨subd5_2_909, List.forall_mem_cons.2 ⟨subd5_2_910, List.forall_mem_cons.2 ⟨subd5_2_911, List.forall_mem_cons.2 ⟨subd5_2_912, List.forall_mem_cons.2 ⟨subd5_2_913, List.forall_mem_cons.2 ⟨subd5_2_914, List.forall_mem_cons.2 ⟨subd5_2_915, List.forall_mem_cons.2 ⟨subd5_2_916, List.forall_mem_cons.2 ⟨subd5_2_917, List.forall_mem_cons.2 ⟨subd5_2_918, List.forall_mem_cons.2 ⟨subd5_2_919, List.forall_mem_cons.2 ⟨subd5_2_920, List.forall_mem_cons.2 ⟨subd5_2_921, List.forall_mem_cons.2 ⟨subd5_2_922, List.forall_mem_cons.2 ⟨subd5_2_923, List.forall_mem_cons.2 ⟨subd5_2_924, List.forall_mem_cons.2 ⟨subd5_2_925, List.forall_mem_cons.2 ⟨subd5_2_926, List.forall_mem_cons.2 ⟨subd5_2_927, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_928 : subd5_2 [2, -6] = true := by decide +kernel
theorem subd5_2_929 : subd5_2 [2, -5] = true := by decide +kernel
theorem subd5_2_930 : subd5_2 [2, -4] = true := by decide +kernel
theorem subd5_2_931 : subd5_2 [2, -3, -6] = true := by decide +kernel
theorem subd5_2_932 : subd5_2 [2, -3, -5] = true := by decide +kernel
theorem subd5_2_933 : subd5_2 [2, -3, -4] = true := by decide +kernel
theorem subd5_2_934 : subd5_2 [2, -3, -3] = true := by decide +kernel
theorem subd5_2_935 : subd5_2 [2, -3, -2] = true := by decide +kernel
theorem subd5_2_936 : subd5_2 [2, -3, -1] = true := by decide +kernel
theorem subd5_2_937 : subd5_2 [2, -3, 0] = true := by decide +kernel
theorem subd5_2_938 : subd5_2 [2, -3, 1] = true := by decide +kernel
theorem subd5_2_939 : subd5_2 [2, -3, 2] = true := by decide +kernel
theorem subd5_2_940 : subd5_2 [2, -3, 3] = true := by decide +kernel
theorem subd5_2_941 : subd5_2 [2, -3, 4] = true := by decide +kernel
theorem subd5_2_942 : subd5_2 [2, -3, 5] = true := by decide +kernel
theorem subd5_2_943 : subd5_2 [2, -3, 6] = true := by decide +kernel
theorem subd5_2_944 : subd5_2 [2, -3, 7] = true := by decide +kernel
theorem subd5_2_945 : subd5_2 [2, -3, 8] = true := by decide +kernel
theorem subd5_2_946 : subd5_2 [2, -2, -7] = true := by decide +kernel
theorem subd5_2_947 : subd5_2 [2, -2, -6] = true := by decide +kernel
theorem subd5_2_948 : subd5_2 [2, -2, -5] = true := by decide +kernel
theorem subd5_2_949 : subd5_2 [2, -2, -4] = true := by decide +kernel
theorem subd5_2_950 : subd5_2 [2, -2, -3] = true := by decide +kernel
theorem subd5_2_951 : subd5_2 [2, -2, -2] = true := by decide +kernel
theorem subd5_2_952 : subd5_2 [2, -2, -1] = true := by decide +kernel
theorem subd5_2_953 : subd5_2 [2, -2, 0] = true := by decide +kernel
theorem subd5_2_954 : subd5_2 [2, -2, 1] = true := by decide +kernel
theorem subd5_2_955 : subd5_2 [2, -2, 2] = true := by decide +kernel
theorem subd5_2_956 : subd5_2 [2, -2, 3] = true := by decide +kernel
theorem subd5_2_957 : subd5_2 [2, -2, 4] = true := by decide +kernel
theorem subd5_2_958 : subd5_2 [2, -2, 5] = true := by decide +kernel
theorem subd5_2_959 : subd5_2 [2, -2, 6] = true := by decide +kernel
theorem sbd5_2_29 : ∀ q ∈ blkd5_2_29, subd5_2 q = true := by
  unfold blkd5_2_29
  exact List.forall_mem_cons.2 ⟨subd5_2_928, List.forall_mem_cons.2 ⟨subd5_2_929, List.forall_mem_cons.2 ⟨subd5_2_930, List.forall_mem_cons.2 ⟨subd5_2_931, List.forall_mem_cons.2 ⟨subd5_2_932, List.forall_mem_cons.2 ⟨subd5_2_933, List.forall_mem_cons.2 ⟨subd5_2_934, List.forall_mem_cons.2 ⟨subd5_2_935, List.forall_mem_cons.2 ⟨subd5_2_936, List.forall_mem_cons.2 ⟨subd5_2_937, List.forall_mem_cons.2 ⟨subd5_2_938, List.forall_mem_cons.2 ⟨subd5_2_939, List.forall_mem_cons.2 ⟨subd5_2_940, List.forall_mem_cons.2 ⟨subd5_2_941, List.forall_mem_cons.2 ⟨subd5_2_942, List.forall_mem_cons.2 ⟨subd5_2_943, List.forall_mem_cons.2 ⟨subd5_2_944, List.forall_mem_cons.2 ⟨subd5_2_945, List.forall_mem_cons.2 ⟨subd5_2_946, List.forall_mem_cons.2 ⟨subd5_2_947, List.forall_mem_cons.2 ⟨subd5_2_948, List.forall_mem_cons.2 ⟨subd5_2_949, List.forall_mem_cons.2 ⟨subd5_2_950, List.forall_mem_cons.2 ⟨subd5_2_951, List.forall_mem_cons.2 ⟨subd5_2_952, List.forall_mem_cons.2 ⟨subd5_2_953, List.forall_mem_cons.2 ⟨subd5_2_954, List.forall_mem_cons.2 ⟨subd5_2_955, List.forall_mem_cons.2 ⟨subd5_2_956, List.forall_mem_cons.2 ⟨subd5_2_957, List.forall_mem_cons.2 ⟨subd5_2_958, List.forall_mem_cons.2 ⟨subd5_2_959, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_960 : subd5_2 [2, -2, 7] = true := by decide +kernel
theorem subd5_2_961 : subd5_2 [2, -2, 8] = true := by decide +kernel
theorem subd5_2_962 : subd5_2 [2, -1, -8] = true := by decide +kernel
theorem subd5_2_963 : subd5_2 [2, -1, -7] = true := by decide +kernel
theorem subd5_2_964 : subd5_2 [2, -1, -6] = true := by decide +kernel
theorem subd5_2_965 : subd5_2 [2, -1, -5] = true := by decide +kernel
theorem subd5_2_966 : subd5_2 [2, -1, -4] = true := by decide +kernel
theorem subd5_2_967 : subd5_2 [2, -1, -3] = true := by decide +kernel
theorem subd5_2_968 : subd5_2 [2, -1, -2] = true := by decide +kernel
theorem subd5_2_969 : subd5_2 [2, -1, -1] = true := by decide +kernel
theorem subd5_2_970 : subd5_2 [2, -1, 0] = true := by decide +kernel
theorem subd5_2_971 : subd5_2 [2, -1, 1] = true := by decide +kernel
theorem subd5_2_972 : subd5_2 [2, -1, 2] = true := by decide +kernel
theorem subd5_2_973 : subd5_2 [2, -1, 3] = true := by decide +kernel
theorem subd5_2_974 : subd5_2 [2, -1, 4] = true := by decide +kernel
theorem subd5_2_975 : subd5_2 [2, -1, 5] = true := by decide +kernel
theorem subd5_2_976 : subd5_2 [2, -1, 6] = true := by decide +kernel
theorem subd5_2_977 : subd5_2 [2, -1, 7] = true := by decide +kernel
theorem subd5_2_978 : subd5_2 [2, -1, 8] = true := by decide +kernel
theorem subd5_2_979 : subd5_2 [2, -1, 9] = true := by decide +kernel
theorem subd5_2_980 : subd5_2 [2, 0, -8] = true := by decide +kernel
theorem subd5_2_981 : subd5_2 [2, 0, -7] = true := by decide +kernel
theorem subd5_2_982 : subd5_2 [2, 0, -6] = true := by decide +kernel
theorem subd5_2_983 : subd5_2 [2, 0, -5] = true := by decide +kernel
theorem subd5_2_984 : subd5_2 [2, 0, -4] = true := by decide +kernel
theorem subd5_2_985 : subd5_2 [2, 0, -3] = true := by decide +kernel
theorem subd5_2_986 : subd5_2 [2, 0, -2] = true := by decide +kernel
theorem subd5_2_987 : subd5_2 [2, 0, -1] = true := by decide +kernel
theorem subd5_2_988 : subd5_2 [2, 0, 0] = true := by decide +kernel
theorem subd5_2_989 : subd5_2 [2, 0, 1] = true := by decide +kernel
theorem subd5_2_990 : subd5_2 [2, 0, 2] = true := by decide +kernel
theorem subd5_2_991 : subd5_2 [2, 0, 3] = true := by decide +kernel
theorem sbd5_2_30 : ∀ q ∈ blkd5_2_30, subd5_2 q = true := by
  unfold blkd5_2_30
  exact List.forall_mem_cons.2 ⟨subd5_2_960, List.forall_mem_cons.2 ⟨subd5_2_961, List.forall_mem_cons.2 ⟨subd5_2_962, List.forall_mem_cons.2 ⟨subd5_2_963, List.forall_mem_cons.2 ⟨subd5_2_964, List.forall_mem_cons.2 ⟨subd5_2_965, List.forall_mem_cons.2 ⟨subd5_2_966, List.forall_mem_cons.2 ⟨subd5_2_967, List.forall_mem_cons.2 ⟨subd5_2_968, List.forall_mem_cons.2 ⟨subd5_2_969, List.forall_mem_cons.2 ⟨subd5_2_970, List.forall_mem_cons.2 ⟨subd5_2_971, List.forall_mem_cons.2 ⟨subd5_2_972, List.forall_mem_cons.2 ⟨subd5_2_973, List.forall_mem_cons.2 ⟨subd5_2_974, List.forall_mem_cons.2 ⟨subd5_2_975, List.forall_mem_cons.2 ⟨subd5_2_976, List.forall_mem_cons.2 ⟨subd5_2_977, List.forall_mem_cons.2 ⟨subd5_2_978, List.forall_mem_cons.2 ⟨subd5_2_979, List.forall_mem_cons.2 ⟨subd5_2_980, List.forall_mem_cons.2 ⟨subd5_2_981, List.forall_mem_cons.2 ⟨subd5_2_982, List.forall_mem_cons.2 ⟨subd5_2_983, List.forall_mem_cons.2 ⟨subd5_2_984, List.forall_mem_cons.2 ⟨subd5_2_985, List.forall_mem_cons.2 ⟨subd5_2_986, List.forall_mem_cons.2 ⟨subd5_2_987, List.forall_mem_cons.2 ⟨subd5_2_988, List.forall_mem_cons.2 ⟨subd5_2_989, List.forall_mem_cons.2 ⟨subd5_2_990, List.forall_mem_cons.2 ⟨subd5_2_991, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_992 : subd5_2 [2, 0, 4] = true := by decide +kernel
theorem subd5_2_993 : subd5_2 [2, 0, 5] = true := by decide +kernel
theorem subd5_2_994 : subd5_2 [2, 0, 6] = true := by decide +kernel
theorem subd5_2_995 : subd5_2 [2, 0, 7] = true := by decide +kernel
theorem subd5_2_996 : subd5_2 [2, 0, 8] = true := by decide +kernel
theorem subd5_2_997 : subd5_2 [2, 1, -8] = true := by decide +kernel
theorem subd5_2_998 : subd5_2 [2, 1, -7] = true := by decide +kernel
theorem subd5_2_999 : subd5_2 [2, 1, -6] = true := by decide +kernel
theorem subd5_2_1000 : subd5_2 [2, 1, -5] = true := by decide +kernel
theorem subd5_2_1001 : subd5_2 [2, 1, -4] = true := by decide +kernel
theorem subd5_2_1002 : subd5_2 [2, 1, -3] = true := by decide +kernel
theorem subd5_2_1003 : subd5_2 [2, 1, -2] = true := by decide +kernel
theorem subd5_2_1004 : subd5_2 [2, 1, -1] = true := by decide +kernel
theorem subd5_2_1005 : subd5_2 [2, 1, 0] = true := by decide +kernel
theorem subd5_2_1006 : subd5_2 [2, 1, 1] = true := by decide +kernel
theorem subd5_2_1007 : subd5_2 [2, 1, 2] = true := by decide +kernel
theorem subd5_2_1008 : subd5_2 [2, 1, 3] = true := by decide +kernel
theorem subd5_2_1009 : subd5_2 [2, 1, 4] = true := by decide +kernel
theorem subd5_2_1010 : subd5_2 [2, 1, 5] = true := by decide +kernel
theorem subd5_2_1011 : subd5_2 [2, 1, 6] = true := by decide +kernel
theorem subd5_2_1012 : subd5_2 [2, 1, 7] = true := by decide +kernel
theorem subd5_2_1013 : subd5_2 [2, 1, 8] = true := by decide +kernel
theorem subd5_2_1014 : subd5_2 [2, 2, -9] = true := by decide +kernel
theorem subd5_2_1015 : subd5_2 [2, 2, -8] = true := by decide +kernel
theorem subd5_2_1016 : subd5_2 [2, 2, -7] = true := by decide +kernel
theorem subd5_2_1017 : subd5_2 [2, 2, -6] = true := by decide +kernel
theorem subd5_2_1018 : subd5_2 [2, 2, -5] = true := by decide +kernel
theorem subd5_2_1019 : subd5_2 [2, 2, -4] = true := by decide +kernel
theorem subd5_2_1020 : subd5_2 [2, 2, -3] = true := by decide +kernel
theorem subd5_2_1021 : subd5_2 [2, 2, -2] = true := by decide +kernel
theorem subd5_2_1022 : subd5_2 [2, 2, -1] = true := by decide +kernel
theorem subd5_2_1023 : subd5_2 [2, 2, 0] = true := by decide +kernel
theorem sbd5_2_31 : ∀ q ∈ blkd5_2_31, subd5_2 q = true := by
  unfold blkd5_2_31
  exact List.forall_mem_cons.2 ⟨subd5_2_992, List.forall_mem_cons.2 ⟨subd5_2_993, List.forall_mem_cons.2 ⟨subd5_2_994, List.forall_mem_cons.2 ⟨subd5_2_995, List.forall_mem_cons.2 ⟨subd5_2_996, List.forall_mem_cons.2 ⟨subd5_2_997, List.forall_mem_cons.2 ⟨subd5_2_998, List.forall_mem_cons.2 ⟨subd5_2_999, List.forall_mem_cons.2 ⟨subd5_2_1000, List.forall_mem_cons.2 ⟨subd5_2_1001, List.forall_mem_cons.2 ⟨subd5_2_1002, List.forall_mem_cons.2 ⟨subd5_2_1003, List.forall_mem_cons.2 ⟨subd5_2_1004, List.forall_mem_cons.2 ⟨subd5_2_1005, List.forall_mem_cons.2 ⟨subd5_2_1006, List.forall_mem_cons.2 ⟨subd5_2_1007, List.forall_mem_cons.2 ⟨subd5_2_1008, List.forall_mem_cons.2 ⟨subd5_2_1009, List.forall_mem_cons.2 ⟨subd5_2_1010, List.forall_mem_cons.2 ⟨subd5_2_1011, List.forall_mem_cons.2 ⟨subd5_2_1012, List.forall_mem_cons.2 ⟨subd5_2_1013, List.forall_mem_cons.2 ⟨subd5_2_1014, List.forall_mem_cons.2 ⟨subd5_2_1015, List.forall_mem_cons.2 ⟨subd5_2_1016, List.forall_mem_cons.2 ⟨subd5_2_1017, List.forall_mem_cons.2 ⟨subd5_2_1018, List.forall_mem_cons.2 ⟨subd5_2_1019, List.forall_mem_cons.2 ⟨subd5_2_1020, List.forall_mem_cons.2 ⟨subd5_2_1021, List.forall_mem_cons.2 ⟨subd5_2_1022, List.forall_mem_cons.2 ⟨subd5_2_1023, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_1024 : subd5_2 [2, 2, 1] = true := by decide +kernel
theorem subd5_2_1025 : subd5_2 [2, 2, 2] = true := by decide +kernel
theorem subd5_2_1026 : subd5_2 [2, 2, 3] = true := by decide +kernel
theorem subd5_2_1027 : subd5_2 [2, 2, 4] = true := by decide +kernel
theorem subd5_2_1028 : subd5_2 [2, 2, 5] = true := by decide +kernel
theorem subd5_2_1029 : subd5_2 [2, 2, 6] = true := by decide +kernel
theorem subd5_2_1030 : subd5_2 [2, 2, 7] = true := by decide +kernel
theorem subd5_2_1031 : subd5_2 [2, 2, 8] = true := by decide +kernel
theorem subd5_2_1032 : subd5_2 [2, 3, -9] = true := by decide +kernel
theorem subd5_2_1033 : subd5_2 [2, 3, -8] = true := by decide +kernel
theorem subd5_2_1034 : subd5_2 [2, 3, -7] = true := by decide +kernel
theorem subd5_2_1035 : subd5_2 [2, 3, -6] = true := by decide +kernel
theorem subd5_2_1036 : subd5_2 [2, 3, -5] = true := by decide +kernel
theorem subd5_2_1037 : subd5_2 [2, 3, -4] = true := by decide +kernel
theorem subd5_2_1038 : subd5_2 [2, 3, -3] = true := by decide +kernel
theorem subd5_2_1039 : subd5_2 [2, 3, -2] = true := by decide +kernel
theorem subd5_2_1040 : subd5_2 [2, 3, -1] = true := by decide +kernel
theorem subd5_2_1041 : subd5_2 [2, 3, 0] = true := by decide +kernel
theorem subd5_2_1042 : subd5_2 [2, 3, 1] = true := by decide +kernel
theorem subd5_2_1043 : subd5_2 [2, 3, 2] = true := by decide +kernel
theorem subd5_2_1044 : subd5_2 [2, 3, 3] = true := by decide +kernel
theorem subd5_2_1045 : subd5_2 [2, 3, 4] = true := by decide +kernel
theorem subd5_2_1046 : subd5_2 [2, 3, 5] = true := by decide +kernel
theorem subd5_2_1047 : subd5_2 [2, 3, 6] = true := by decide +kernel
theorem subd5_2_1048 : subd5_2 [2, 3, 7] = true := by decide +kernel
theorem subd5_2_1049 : subd5_2 [2, 4, -9] = true := by decide +kernel
theorem subd5_2_1050 : subd5_2 [2, 4, -8] = true := by decide +kernel
theorem subd5_2_1051 : subd5_2 [2, 4, -7] = true := by decide +kernel
theorem subd5_2_1052 : subd5_2 [2, 4, -6] = true := by decide +kernel
theorem subd5_2_1053 : subd5_2 [2, 4, -5] = true := by decide +kernel
theorem subd5_2_1054 : subd5_2 [2, 4, -4] = true := by decide +kernel
theorem subd5_2_1055 : subd5_2 [2, 4, -3] = true := by decide +kernel
theorem sbd5_2_32 : ∀ q ∈ blkd5_2_32, subd5_2 q = true := by
  unfold blkd5_2_32
  exact List.forall_mem_cons.2 ⟨subd5_2_1024, List.forall_mem_cons.2 ⟨subd5_2_1025, List.forall_mem_cons.2 ⟨subd5_2_1026, List.forall_mem_cons.2 ⟨subd5_2_1027, List.forall_mem_cons.2 ⟨subd5_2_1028, List.forall_mem_cons.2 ⟨subd5_2_1029, List.forall_mem_cons.2 ⟨subd5_2_1030, List.forall_mem_cons.2 ⟨subd5_2_1031, List.forall_mem_cons.2 ⟨subd5_2_1032, List.forall_mem_cons.2 ⟨subd5_2_1033, List.forall_mem_cons.2 ⟨subd5_2_1034, List.forall_mem_cons.2 ⟨subd5_2_1035, List.forall_mem_cons.2 ⟨subd5_2_1036, List.forall_mem_cons.2 ⟨subd5_2_1037, List.forall_mem_cons.2 ⟨subd5_2_1038, List.forall_mem_cons.2 ⟨subd5_2_1039, List.forall_mem_cons.2 ⟨subd5_2_1040, List.forall_mem_cons.2 ⟨subd5_2_1041, List.forall_mem_cons.2 ⟨subd5_2_1042, List.forall_mem_cons.2 ⟨subd5_2_1043, List.forall_mem_cons.2 ⟨subd5_2_1044, List.forall_mem_cons.2 ⟨subd5_2_1045, List.forall_mem_cons.2 ⟨subd5_2_1046, List.forall_mem_cons.2 ⟨subd5_2_1047, List.forall_mem_cons.2 ⟨subd5_2_1048, List.forall_mem_cons.2 ⟨subd5_2_1049, List.forall_mem_cons.2 ⟨subd5_2_1050, List.forall_mem_cons.2 ⟨subd5_2_1051, List.forall_mem_cons.2 ⟨subd5_2_1052, List.forall_mem_cons.2 ⟨subd5_2_1053, List.forall_mem_cons.2 ⟨subd5_2_1054, List.forall_mem_cons.2 ⟨subd5_2_1055, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_1056 : subd5_2 [2, 4, -2] = true := by decide +kernel
theorem subd5_2_1057 : subd5_2 [2, 4, -1] = true := by decide +kernel
theorem subd5_2_1058 : subd5_2 [2, 4, 0] = true := by decide +kernel
theorem subd5_2_1059 : subd5_2 [2, 4, 1] = true := by decide +kernel
theorem subd5_2_1060 : subd5_2 [2, 4, 2] = true := by decide +kernel
theorem subd5_2_1061 : subd5_2 [2, 4, 3] = true := by decide +kernel
theorem subd5_2_1062 : subd5_2 [2, 4, 4] = true := by decide +kernel
theorem subd5_2_1063 : subd5_2 [2, 4, 5] = true := by decide +kernel
theorem subd5_2_1064 : subd5_2 [2, 4, 6] = true := by decide +kernel
theorem subd5_2_1065 : subd5_2 [2, 4, 7] = true := by decide +kernel
theorem subd5_2_1066 : subd5_2 [2, 5, -8] = true := by decide +kernel
theorem subd5_2_1067 : subd5_2 [2, 5, -7] = true := by decide +kernel
theorem subd5_2_1068 : subd5_2 [2, 5, -6] = true := by decide +kernel
theorem subd5_2_1069 : subd5_2 [2, 5, -5] = true := by decide +kernel
theorem subd5_2_1070 : subd5_2 [2, 5, -4] = true := by decide +kernel
theorem subd5_2_1071 : subd5_2 [2, 5, -3] = true := by decide +kernel
theorem subd5_2_1072 : subd5_2 [2, 5, -2] = true := by decide +kernel
theorem subd5_2_1073 : subd5_2 [2, 5, -1] = true := by decide +kernel
theorem subd5_2_1074 : subd5_2 [2, 5, 0] = true := by decide +kernel
theorem subd5_2_1075 : subd5_2 [2, 5, 1] = true := by decide +kernel
theorem subd5_2_1076 : subd5_2 [2, 5, 2] = true := by decide +kernel
theorem subd5_2_1077 : subd5_2 [2, 5, 3] = true := by decide +kernel
theorem subd5_2_1078 : subd5_2 [2, 5, 4] = true := by decide +kernel
theorem subd5_2_1079 : subd5_2 [2, 5, 5] = true := by decide +kernel
theorem subd5_2_1080 : subd5_2 [2, 5, 6] = true := by decide +kernel
theorem subd5_2_1081 : subd5_2 [2, 6] = true := by decide +kernel
theorem subd5_2_1082 : subd5_2 [2, 7] = true := by decide +kernel
theorem subd5_2_1083 : subd5_2 [2, 8] = true := by decide +kernel
theorem subd5_2_1084 : subd5_2 [3, -6] = true := by decide +kernel
theorem subd5_2_1085 : subd5_2 [3, -5] = true := by decide +kernel
theorem subd5_2_1086 : subd5_2 [3, -4] = true := by decide +kernel
theorem subd5_2_1087 : subd5_2 [3, -3] = true := by decide +kernel
theorem sbd5_2_33 : ∀ q ∈ blkd5_2_33, subd5_2 q = true := by
  unfold blkd5_2_33
  exact List.forall_mem_cons.2 ⟨subd5_2_1056, List.forall_mem_cons.2 ⟨subd5_2_1057, List.forall_mem_cons.2 ⟨subd5_2_1058, List.forall_mem_cons.2 ⟨subd5_2_1059, List.forall_mem_cons.2 ⟨subd5_2_1060, List.forall_mem_cons.2 ⟨subd5_2_1061, List.forall_mem_cons.2 ⟨subd5_2_1062, List.forall_mem_cons.2 ⟨subd5_2_1063, List.forall_mem_cons.2 ⟨subd5_2_1064, List.forall_mem_cons.2 ⟨subd5_2_1065, List.forall_mem_cons.2 ⟨subd5_2_1066, List.forall_mem_cons.2 ⟨subd5_2_1067, List.forall_mem_cons.2 ⟨subd5_2_1068, List.forall_mem_cons.2 ⟨subd5_2_1069, List.forall_mem_cons.2 ⟨subd5_2_1070, List.forall_mem_cons.2 ⟨subd5_2_1071, List.forall_mem_cons.2 ⟨subd5_2_1072, List.forall_mem_cons.2 ⟨subd5_2_1073, List.forall_mem_cons.2 ⟨subd5_2_1074, List.forall_mem_cons.2 ⟨subd5_2_1075, List.forall_mem_cons.2 ⟨subd5_2_1076, List.forall_mem_cons.2 ⟨subd5_2_1077, List.forall_mem_cons.2 ⟨subd5_2_1078, List.forall_mem_cons.2 ⟨subd5_2_1079, List.forall_mem_cons.2 ⟨subd5_2_1080, List.forall_mem_cons.2 ⟨subd5_2_1081, List.forall_mem_cons.2 ⟨subd5_2_1082, List.forall_mem_cons.2 ⟨subd5_2_1083, List.forall_mem_cons.2 ⟨subd5_2_1084, List.forall_mem_cons.2 ⟨subd5_2_1085, List.forall_mem_cons.2 ⟨subd5_2_1086, List.forall_mem_cons.2 ⟨subd5_2_1087, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_1088 : subd5_2 [3, -2, -6] = true := by decide +kernel
theorem subd5_2_1089 : subd5_2 [3, -2, -5] = true := by decide +kernel
theorem subd5_2_1090 : subd5_2 [3, -2, -4] = true := by decide +kernel
theorem subd5_2_1091 : subd5_2 [3, -2, -3] = true := by decide +kernel
theorem subd5_2_1092 : subd5_2 [3, -2, -2] = true := by decide +kernel
theorem subd5_2_1093 : subd5_2 [3, -2, -1] = true := by decide +kernel
theorem subd5_2_1094 : subd5_2 [3, -2, 0] = true := by decide +kernel
theorem subd5_2_1095 : subd5_2 [3, -2, 1] = true := by decide +kernel
theorem subd5_2_1096 : subd5_2 [3, -2, 2] = true := by decide +kernel
theorem subd5_2_1097 : subd5_2 [3, -2, 3] = true := by decide +kernel
theorem subd5_2_1098 : subd5_2 [3, -2, 4] = true := by decide +kernel
theorem subd5_2_1099 : subd5_2 [3, -2, 5] = true := by decide +kernel
theorem subd5_2_1100 : subd5_2 [3, -2, 6] = true := by decide +kernel
theorem subd5_2_1101 : subd5_2 [3, -2, 7] = true := by decide +kernel
theorem subd5_2_1102 : subd5_2 [3, -2, 8] = true := by decide +kernel
theorem subd5_2_1103 : subd5_2 [3, -1, -6] = true := by decide +kernel
theorem subd5_2_1104 : subd5_2 [3, -1, -5] = true := by decide +kernel
theorem subd5_2_1105 : subd5_2 [3, -1, -4] = true := by decide +kernel
theorem subd5_2_1106 : subd5_2 [3, -1, -3] = true := by decide +kernel
theorem subd5_2_1107 : subd5_2 [3, -1, -2] = true := by decide +kernel
theorem subd5_2_1108 : subd5_2 [3, -1, -1] = true := by decide +kernel
theorem subd5_2_1109 : subd5_2 [3, -1, 0] = true := by decide +kernel
theorem subd5_2_1110 : subd5_2 [3, -1, 1] = true := by decide +kernel
theorem subd5_2_1111 : subd5_2 [3, -1, 2] = true := by decide +kernel
theorem subd5_2_1112 : subd5_2 [3, -1, 3] = true := by decide +kernel
theorem subd5_2_1113 : subd5_2 [3, -1, 4] = true := by decide +kernel
theorem subd5_2_1114 : subd5_2 [3, -1, 5] = true := by decide +kernel
theorem subd5_2_1115 : subd5_2 [3, -1, 6] = true := by decide +kernel
theorem subd5_2_1116 : subd5_2 [3, -1, 7] = true := by decide +kernel
theorem subd5_2_1117 : subd5_2 [3, -1, 8] = true := by decide +kernel
theorem subd5_2_1118 : subd5_2 [3, 0, -7] = true := by decide +kernel
theorem subd5_2_1119 : subd5_2 [3, 0, -6] = true := by decide +kernel
theorem sbd5_2_34 : ∀ q ∈ blkd5_2_34, subd5_2 q = true := by
  unfold blkd5_2_34
  exact List.forall_mem_cons.2 ⟨subd5_2_1088, List.forall_mem_cons.2 ⟨subd5_2_1089, List.forall_mem_cons.2 ⟨subd5_2_1090, List.forall_mem_cons.2 ⟨subd5_2_1091, List.forall_mem_cons.2 ⟨subd5_2_1092, List.forall_mem_cons.2 ⟨subd5_2_1093, List.forall_mem_cons.2 ⟨subd5_2_1094, List.forall_mem_cons.2 ⟨subd5_2_1095, List.forall_mem_cons.2 ⟨subd5_2_1096, List.forall_mem_cons.2 ⟨subd5_2_1097, List.forall_mem_cons.2 ⟨subd5_2_1098, List.forall_mem_cons.2 ⟨subd5_2_1099, List.forall_mem_cons.2 ⟨subd5_2_1100, List.forall_mem_cons.2 ⟨subd5_2_1101, List.forall_mem_cons.2 ⟨subd5_2_1102, List.forall_mem_cons.2 ⟨subd5_2_1103, List.forall_mem_cons.2 ⟨subd5_2_1104, List.forall_mem_cons.2 ⟨subd5_2_1105, List.forall_mem_cons.2 ⟨subd5_2_1106, List.forall_mem_cons.2 ⟨subd5_2_1107, List.forall_mem_cons.2 ⟨subd5_2_1108, List.forall_mem_cons.2 ⟨subd5_2_1109, List.forall_mem_cons.2 ⟨subd5_2_1110, List.forall_mem_cons.2 ⟨subd5_2_1111, List.forall_mem_cons.2 ⟨subd5_2_1112, List.forall_mem_cons.2 ⟨subd5_2_1113, List.forall_mem_cons.2 ⟨subd5_2_1114, List.forall_mem_cons.2 ⟨subd5_2_1115, List.forall_mem_cons.2 ⟨subd5_2_1116, List.forall_mem_cons.2 ⟨subd5_2_1117, List.forall_mem_cons.2 ⟨subd5_2_1118, List.forall_mem_cons.2 ⟨subd5_2_1119, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_1120 : subd5_2 [3, 0, -5] = true := by decide +kernel
theorem subd5_2_1121 : subd5_2 [3, 0, -4] = true := by decide +kernel
theorem subd5_2_1122 : subd5_2 [3, 0, -3] = true := by decide +kernel
theorem subd5_2_1123 : subd5_2 [3, 0, -2] = true := by decide +kernel
theorem subd5_2_1124 : subd5_2 [3, 0, -1] = true := by decide +kernel
theorem subd5_2_1125 : subd5_2 [3, 0, 0] = true := by decide +kernel
theorem subd5_2_1126 : subd5_2 [3, 0, 1] = true := by decide +kernel
theorem subd5_2_1127 : subd5_2 [3, 0, 2] = true := by decide +kernel
theorem subd5_2_1128 : subd5_2 [3, 0, 3] = true := by decide +kernel
theorem subd5_2_1129 : subd5_2 [3, 0, 4] = true := by decide +kernel
theorem subd5_2_1130 : subd5_2 [3, 0, 5] = true := by decide +kernel
theorem subd5_2_1131 : subd5_2 [3, 0, 6] = true := by decide +kernel
theorem subd5_2_1132 : subd5_2 [3, 0, 7] = true := by decide +kernel
theorem subd5_2_1133 : subd5_2 [3, 0, 8] = true := by decide +kernel
theorem subd5_2_1134 : subd5_2 [3, 1, -8] = true := by decide +kernel
theorem subd5_2_1135 : subd5_2 [3, 1, -7] = true := by decide +kernel
theorem subd5_2_1136 : subd5_2 [3, 1, -6] = true := by decide +kernel
theorem subd5_2_1137 : subd5_2 [3, 1, -5] = true := by decide +kernel
theorem subd5_2_1138 : subd5_2 [3, 1, -4] = true := by decide +kernel
theorem subd5_2_1139 : subd5_2 [3, 1, -3] = true := by decide +kernel
theorem subd5_2_1140 : subd5_2 [3, 1, -2] = true := by decide +kernel
theorem subd5_2_1141 : subd5_2 [3, 1, -1] = true := by decide +kernel
theorem subd5_2_1142 : subd5_2 [3, 1, 0] = true := by decide +kernel
theorem subd5_2_1143 : subd5_2 [3, 1, 1] = true := by decide +kernel
theorem subd5_2_1144 : subd5_2 [3, 1, 2] = true := by decide +kernel
theorem subd5_2_1145 : subd5_2 [3, 1, 3] = true := by decide +kernel
theorem subd5_2_1146 : subd5_2 [3, 1, 4] = true := by decide +kernel
theorem subd5_2_1147 : subd5_2 [3, 1, 5] = true := by decide +kernel
theorem subd5_2_1148 : subd5_2 [3, 1, 6] = true := by decide +kernel
theorem subd5_2_1149 : subd5_2 [3, 1, 7] = true := by decide +kernel
theorem subd5_2_1150 : subd5_2 [3, 1, 8] = true := by decide +kernel
theorem subd5_2_1151 : subd5_2 [3, 2, -8] = true := by decide +kernel
theorem sbd5_2_35 : ∀ q ∈ blkd5_2_35, subd5_2 q = true := by
  unfold blkd5_2_35
  exact List.forall_mem_cons.2 ⟨subd5_2_1120, List.forall_mem_cons.2 ⟨subd5_2_1121, List.forall_mem_cons.2 ⟨subd5_2_1122, List.forall_mem_cons.2 ⟨subd5_2_1123, List.forall_mem_cons.2 ⟨subd5_2_1124, List.forall_mem_cons.2 ⟨subd5_2_1125, List.forall_mem_cons.2 ⟨subd5_2_1126, List.forall_mem_cons.2 ⟨subd5_2_1127, List.forall_mem_cons.2 ⟨subd5_2_1128, List.forall_mem_cons.2 ⟨subd5_2_1129, List.forall_mem_cons.2 ⟨subd5_2_1130, List.forall_mem_cons.2 ⟨subd5_2_1131, List.forall_mem_cons.2 ⟨subd5_2_1132, List.forall_mem_cons.2 ⟨subd5_2_1133, List.forall_mem_cons.2 ⟨subd5_2_1134, List.forall_mem_cons.2 ⟨subd5_2_1135, List.forall_mem_cons.2 ⟨subd5_2_1136, List.forall_mem_cons.2 ⟨subd5_2_1137, List.forall_mem_cons.2 ⟨subd5_2_1138, List.forall_mem_cons.2 ⟨subd5_2_1139, List.forall_mem_cons.2 ⟨subd5_2_1140, List.forall_mem_cons.2 ⟨subd5_2_1141, List.forall_mem_cons.2 ⟨subd5_2_1142, List.forall_mem_cons.2 ⟨subd5_2_1143, List.forall_mem_cons.2 ⟨subd5_2_1144, List.forall_mem_cons.2 ⟨subd5_2_1145, List.forall_mem_cons.2 ⟨subd5_2_1146, List.forall_mem_cons.2 ⟨subd5_2_1147, List.forall_mem_cons.2 ⟨subd5_2_1148, List.forall_mem_cons.2 ⟨subd5_2_1149, List.forall_mem_cons.2 ⟨subd5_2_1150, List.forall_mem_cons.2 ⟨subd5_2_1151, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C121
