import ReflectZphi.Data.Cert5.C096.Base

namespace ReflectZphi.Data.Cert5.C096

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_2_672 : subd9_2 [1, 0, 16] = true := by decide +kernel
theorem subd9_2_673 : subd9_2 [1, 1, -16] = true := by decide +kernel
theorem subd9_2_674 : subd9_2 [1, 1, -15] = true := by decide +kernel
theorem subd9_2_675 : subd9_2 [1, 1, -14] = true := by decide +kernel
theorem subd9_2_676 : subd9_2 [1, 1, -13] = true := by decide +kernel
theorem subd9_2_677 : subd9_2 [1, 1, -12] = true := by decide +kernel
theorem subd9_2_678 : subd9_2 [1, 1, -11] = true := by decide +kernel
theorem subd9_2_679 : subd9_2 [1, 1, -10] = true := by decide +kernel
theorem subd9_2_680 : subd9_2 [1, 1, -9] = true := by decide +kernel
theorem subd9_2_681 : subd9_2 [1, 1, -8] = true := by decide +kernel
theorem subd9_2_682 : subd9_2 [1, 1, -7] = true := by decide +kernel
theorem subd9_2_683 : subd9_2 [1, 1, -6] = true := by decide +kernel
theorem subd9_2_684 : subd9_2 [1, 1, -5] = true := by decide +kernel
theorem subd9_2_685 : subd9_2 [1, 1, -4] = true := by decide +kernel
theorem subd9_2_686 : subd9_2 [1, 1, -3] = true := by decide +kernel
theorem subd9_2_687 : subd9_2 [1, 1, -2] = true := by decide +kernel
theorem subd9_2_688 : subd9_2 [1, 1, -1] = true := by decide +kernel
theorem subd9_2_689 : subd9_2 [1, 1, 0] = true := by decide +kernel
theorem subd9_2_690 : subd9_2 [1, 1, 1] = true := by decide +kernel
theorem subd9_2_691 : subd9_2 [1, 1, 2] = true := by decide +kernel
theorem subd9_2_692 : subd9_2 [1, 1, 3] = true := by decide +kernel
theorem subd9_2_693 : subd9_2 [1, 1, 4] = true := by decide +kernel
theorem subd9_2_694 : subd9_2 [1, 1, 5] = true := by decide +kernel
theorem subd9_2_695 : subd9_2 [1, 1, 6] = true := by decide +kernel
theorem subd9_2_696 : subd9_2 [1, 1, 7] = true := by decide +kernel
theorem subd9_2_697 : subd9_2 [1, 1, 8] = true := by decide +kernel
theorem subd9_2_698 : subd9_2 [1, 1, 9] = true := by decide +kernel
theorem subd9_2_699 : subd9_2 [1, 1, 10] = true := by decide +kernel
theorem subd9_2_700 : subd9_2 [1, 1, 11] = true := by decide +kernel
theorem subd9_2_701 : subd9_2 [1, 1, 12] = true := by decide +kernel
theorem subd9_2_702 : subd9_2 [1, 1, 13] = true := by decide +kernel
theorem subd9_2_703 : subd9_2 [1, 1, 14] = true := by decide +kernel
theorem sbd9_2_21 : ∀ q ∈ blkd9_2_21, subd9_2 q = true := by
  unfold blkd9_2_21
  exact List.forall_mem_cons.2 ⟨subd9_2_672, List.forall_mem_cons.2 ⟨subd9_2_673, List.forall_mem_cons.2 ⟨subd9_2_674, List.forall_mem_cons.2 ⟨subd9_2_675, List.forall_mem_cons.2 ⟨subd9_2_676, List.forall_mem_cons.2 ⟨subd9_2_677, List.forall_mem_cons.2 ⟨subd9_2_678, List.forall_mem_cons.2 ⟨subd9_2_679, List.forall_mem_cons.2 ⟨subd9_2_680, List.forall_mem_cons.2 ⟨subd9_2_681, List.forall_mem_cons.2 ⟨subd9_2_682, List.forall_mem_cons.2 ⟨subd9_2_683, List.forall_mem_cons.2 ⟨subd9_2_684, List.forall_mem_cons.2 ⟨subd9_2_685, List.forall_mem_cons.2 ⟨subd9_2_686, List.forall_mem_cons.2 ⟨subd9_2_687, List.forall_mem_cons.2 ⟨subd9_2_688, List.forall_mem_cons.2 ⟨subd9_2_689, List.forall_mem_cons.2 ⟨subd9_2_690, List.forall_mem_cons.2 ⟨subd9_2_691, List.forall_mem_cons.2 ⟨subd9_2_692, List.forall_mem_cons.2 ⟨subd9_2_693, List.forall_mem_cons.2 ⟨subd9_2_694, List.forall_mem_cons.2 ⟨subd9_2_695, List.forall_mem_cons.2 ⟨subd9_2_696, List.forall_mem_cons.2 ⟨subd9_2_697, List.forall_mem_cons.2 ⟨subd9_2_698, List.forall_mem_cons.2 ⟨subd9_2_699, List.forall_mem_cons.2 ⟨subd9_2_700, List.forall_mem_cons.2 ⟨subd9_2_701, List.forall_mem_cons.2 ⟨subd9_2_702, List.forall_mem_cons.2 ⟨subd9_2_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_704 : subd9_2 [1, 1, 15] = true := by decide +kernel
theorem subd9_2_705 : subd9_2 [1, 1, 16] = true := by decide +kernel
theorem subd9_2_706 : subd9_2 [1, 2, -13] = true := by decide +kernel
theorem subd9_2_707 : subd9_2 [1, 2, -12] = true := by decide +kernel
theorem subd9_2_708 : subd9_2 [1, 2, -11] = true := by decide +kernel
theorem subd9_2_709 : subd9_2 [1, 2, -10] = true := by decide +kernel
theorem subd9_2_710 : subd9_2 [1, 2, -9] = true := by decide +kernel
theorem subd9_2_711 : subd9_2 [1, 2, -8] = true := by decide +kernel
theorem subd9_2_712 : subd9_2 [1, 2, -7] = true := by decide +kernel
theorem subd9_2_713 : subd9_2 [1, 2, -6] = true := by decide +kernel
theorem subd9_2_714 : subd9_2 [1, 2, -5] = true := by decide +kernel
theorem subd9_2_715 : subd9_2 [1, 2, -4] = true := by decide +kernel
theorem subd9_2_716 : subd9_2 [1, 2, -3] = true := by decide +kernel
theorem subd9_2_717 : subd9_2 [1, 2, -2] = true := by decide +kernel
theorem subd9_2_718 : subd9_2 [1, 2, -1] = true := by decide +kernel
theorem subd9_2_719 : subd9_2 [1, 2, 0] = true := by decide +kernel
theorem subd9_2_720 : subd9_2 [1, 2, 1] = true := by decide +kernel
theorem subd9_2_721 : subd9_2 [1, 2, 2] = true := by decide +kernel
theorem subd9_2_722 : subd9_2 [1, 2, 3] = true := by decide +kernel
theorem subd9_2_723 : subd9_2 [1, 2, 4] = true := by decide +kernel
theorem subd9_2_724 : subd9_2 [1, 2, 5] = true := by decide +kernel
theorem subd9_2_725 : subd9_2 [1, 2, 6] = true := by decide +kernel
theorem subd9_2_726 : subd9_2 [1, 2, 7] = true := by decide +kernel
theorem subd9_2_727 : subd9_2 [1, 2, 8] = true := by decide +kernel
theorem subd9_2_728 : subd9_2 [1, 2, 9] = true := by decide +kernel
theorem subd9_2_729 : subd9_2 [1, 2, 10] = true := by decide +kernel
theorem subd9_2_730 : subd9_2 [1, 2, 11] = true := by decide +kernel
theorem subd9_2_731 : subd9_2 [1, 2, 12] = true := by decide +kernel
theorem subd9_2_732 : subd9_2 [1, 2, 13] = true := by decide +kernel
theorem subd9_2_733 : subd9_2 [1, 2, 14] = true := by decide +kernel
theorem subd9_2_734 : subd9_2 [1, 3, -7] = true := by decide +kernel
theorem subd9_2_735 : subd9_2 [1, 3, -6] = true := by decide +kernel
theorem sbd9_2_22 : ∀ q ∈ blkd9_2_22, subd9_2 q = true := by
  unfold blkd9_2_22
  exact List.forall_mem_cons.2 ⟨subd9_2_704, List.forall_mem_cons.2 ⟨subd9_2_705, List.forall_mem_cons.2 ⟨subd9_2_706, List.forall_mem_cons.2 ⟨subd9_2_707, List.forall_mem_cons.2 ⟨subd9_2_708, List.forall_mem_cons.2 ⟨subd9_2_709, List.forall_mem_cons.2 ⟨subd9_2_710, List.forall_mem_cons.2 ⟨subd9_2_711, List.forall_mem_cons.2 ⟨subd9_2_712, List.forall_mem_cons.2 ⟨subd9_2_713, List.forall_mem_cons.2 ⟨subd9_2_714, List.forall_mem_cons.2 ⟨subd9_2_715, List.forall_mem_cons.2 ⟨subd9_2_716, List.forall_mem_cons.2 ⟨subd9_2_717, List.forall_mem_cons.2 ⟨subd9_2_718, List.forall_mem_cons.2 ⟨subd9_2_719, List.forall_mem_cons.2 ⟨subd9_2_720, List.forall_mem_cons.2 ⟨subd9_2_721, List.forall_mem_cons.2 ⟨subd9_2_722, List.forall_mem_cons.2 ⟨subd9_2_723, List.forall_mem_cons.2 ⟨subd9_2_724, List.forall_mem_cons.2 ⟨subd9_2_725, List.forall_mem_cons.2 ⟨subd9_2_726, List.forall_mem_cons.2 ⟨subd9_2_727, List.forall_mem_cons.2 ⟨subd9_2_728, List.forall_mem_cons.2 ⟨subd9_2_729, List.forall_mem_cons.2 ⟨subd9_2_730, List.forall_mem_cons.2 ⟨subd9_2_731, List.forall_mem_cons.2 ⟨subd9_2_732, List.forall_mem_cons.2 ⟨subd9_2_733, List.forall_mem_cons.2 ⟨subd9_2_734, List.forall_mem_cons.2 ⟨subd9_2_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_736 : subd9_2 [1, 3, -5] = true := by decide +kernel
theorem subd9_2_737 : subd9_2 [1, 3, -4] = true := by decide +kernel
theorem subd9_2_738 : subd9_2 [1, 3, -3] = true := by decide +kernel
theorem subd9_2_739 : subd9_2 [1, 3, -2] = true := by decide +kernel
theorem subd9_2_740 : subd9_2 [1, 3, -1] = true := by decide +kernel
theorem subd9_2_741 : subd9_2 [1, 3, 0] = true := by decide +kernel
theorem subd9_2_742 : subd9_2 [1, 3, 1] = true := by decide +kernel
theorem subd9_2_743 : subd9_2 [1, 3, 2] = true := by decide +kernel
theorem subd9_2_744 : subd9_2 [1, 3, 3] = true := by decide +kernel
theorem subd9_2_745 : subd9_2 [1, 3, 4] = true := by decide +kernel
theorem subd9_2_746 : subd9_2 [1, 3, 5] = true := by decide +kernel
theorem subd9_2_747 : subd9_2 [1, 3, 6] = true := by decide +kernel
theorem subd9_2_748 : subd9_2 [1, 3, 7] = true := by decide +kernel
theorem subd9_2_749 : subd9_2 [1, 3, 8] = true := by decide +kernel
theorem subd9_2_750 : subd9_2 [2, -3] = true := by decide +kernel
theorem subd9_2_751 : subd9_2 [2, -2, -11] = true := by decide +kernel
theorem subd9_2_752 : subd9_2 [2, -2, -10] = true := by decide +kernel
theorem subd9_2_753 : subd9_2 [2, -2, -9] = true := by decide +kernel
theorem subd9_2_754 : subd9_2 [2, -2, -8] = true := by decide +kernel
theorem subd9_2_755 : subd9_2 [2, -2, -7] = true := by decide +kernel
theorem subd9_2_756 : subd9_2 [2, -2, -6] = true := by decide +kernel
theorem subd9_2_757 : subd9_2 [2, -2, -5] = true := by decide +kernel
theorem subd9_2_758 : subd9_2 [2, -2, -4] = true := by decide +kernel
theorem subd9_2_759 : subd9_2 [2, -2, -3] = true := by decide +kernel
theorem subd9_2_760 : subd9_2 [2, -2, -2] = true := by decide +kernel
theorem subd9_2_761 : subd9_2 [2, -2, -1] = true := by decide +kernel
theorem subd9_2_762 : subd9_2 [2, -2, 0] = true := by decide +kernel
theorem subd9_2_763 : subd9_2 [2, -2, 1] = true := by decide +kernel
theorem subd9_2_764 : subd9_2 [2, -2, 2] = true := by decide +kernel
theorem subd9_2_765 : subd9_2 [2, -2, 3] = true := by decide +kernel
theorem subd9_2_766 : subd9_2 [2, -2, 4] = true := by decide +kernel
theorem subd9_2_767 : subd9_2 [2, -2, 5] = true := by decide +kernel
theorem sbd9_2_23 : ∀ q ∈ blkd9_2_23, subd9_2 q = true := by
  unfold blkd9_2_23
  exact List.forall_mem_cons.2 ⟨subd9_2_736, List.forall_mem_cons.2 ⟨subd9_2_737, List.forall_mem_cons.2 ⟨subd9_2_738, List.forall_mem_cons.2 ⟨subd9_2_739, List.forall_mem_cons.2 ⟨subd9_2_740, List.forall_mem_cons.2 ⟨subd9_2_741, List.forall_mem_cons.2 ⟨subd9_2_742, List.forall_mem_cons.2 ⟨subd9_2_743, List.forall_mem_cons.2 ⟨subd9_2_744, List.forall_mem_cons.2 ⟨subd9_2_745, List.forall_mem_cons.2 ⟨subd9_2_746, List.forall_mem_cons.2 ⟨subd9_2_747, List.forall_mem_cons.2 ⟨subd9_2_748, List.forall_mem_cons.2 ⟨subd9_2_749, List.forall_mem_cons.2 ⟨subd9_2_750, List.forall_mem_cons.2 ⟨subd9_2_751, List.forall_mem_cons.2 ⟨subd9_2_752, List.forall_mem_cons.2 ⟨subd9_2_753, List.forall_mem_cons.2 ⟨subd9_2_754, List.forall_mem_cons.2 ⟨subd9_2_755, List.forall_mem_cons.2 ⟨subd9_2_756, List.forall_mem_cons.2 ⟨subd9_2_757, List.forall_mem_cons.2 ⟨subd9_2_758, List.forall_mem_cons.2 ⟨subd9_2_759, List.forall_mem_cons.2 ⟨subd9_2_760, List.forall_mem_cons.2 ⟨subd9_2_761, List.forall_mem_cons.2 ⟨subd9_2_762, List.forall_mem_cons.2 ⟨subd9_2_763, List.forall_mem_cons.2 ⟨subd9_2_764, List.forall_mem_cons.2 ⟨subd9_2_765, List.forall_mem_cons.2 ⟨subd9_2_766, List.forall_mem_cons.2 ⟨subd9_2_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_768 : subd9_2 [2, -2, 6] = true := by decide +kernel
theorem subd9_2_769 : subd9_2 [2, -2, 7] = true := by decide +kernel
theorem subd9_2_770 : subd9_2 [2, -2, 8] = true := by decide +kernel
theorem subd9_2_771 : subd9_2 [2, -2, 9] = true := by decide +kernel
theorem subd9_2_772 : subd9_2 [2, -1, -14] = true := by decide +kernel
theorem subd9_2_773 : subd9_2 [2, -1, -13] = true := by decide +kernel
theorem subd9_2_774 : subd9_2 [2, -1, -12] = true := by decide +kernel
theorem subd9_2_775 : subd9_2 [2, -1, -11] = true := by decide +kernel
theorem subd9_2_776 : subd9_2 [2, -1, -10] = true := by decide +kernel
theorem subd9_2_777 : subd9_2 [2, -1, -9] = true := by decide +kernel
theorem subd9_2_778 : subd9_2 [2, -1, -8] = true := by decide +kernel
theorem subd9_2_779 : subd9_2 [2, -1, -7] = true := by decide +kernel
theorem subd9_2_780 : subd9_2 [2, -1, -6] = true := by decide +kernel
theorem subd9_2_781 : subd9_2 [2, -1, -5] = true := by decide +kernel
theorem subd9_2_782 : subd9_2 [2, -1, -4] = true := by decide +kernel
theorem subd9_2_783 : subd9_2 [2, -1, -3] = true := by decide +kernel
theorem subd9_2_784 : subd9_2 [2, -1, -2] = true := by decide +kernel
theorem subd9_2_785 : subd9_2 [2, -1, -1] = true := by decide +kernel
theorem subd9_2_786 : subd9_2 [2, -1, 0] = true := by decide +kernel
theorem subd9_2_787 : subd9_2 [2, -1, 1] = true := by decide +kernel
theorem subd9_2_788 : subd9_2 [2, -1, 2] = true := by decide +kernel
theorem subd9_2_789 : subd9_2 [2, -1, 3] = true := by decide +kernel
theorem subd9_2_790 : subd9_2 [2, -1, 4] = true := by decide +kernel
theorem subd9_2_791 : subd9_2 [2, -1, 5] = true := by decide +kernel
theorem subd9_2_792 : subd9_2 [2, -1, 6] = true := by decide +kernel
theorem subd9_2_793 : subd9_2 [2, -1, 7] = true := by decide +kernel
theorem subd9_2_794 : subd9_2 [2, -1, 8] = true := by decide +kernel
theorem subd9_2_795 : subd9_2 [2, -1, 9] = true := by decide +kernel
theorem subd9_2_796 : subd9_2 [2, -1, 10] = true := by decide +kernel
theorem subd9_2_797 : subd9_2 [2, -1, 11] = true := by decide +kernel
theorem subd9_2_798 : subd9_2 [2, -1, 12] = true := by decide +kernel
theorem subd9_2_799 : subd9_2 [2, 0, -14] = true := by decide +kernel
theorem sbd9_2_24 : ∀ q ∈ blkd9_2_24, subd9_2 q = true := by
  unfold blkd9_2_24
  exact List.forall_mem_cons.2 ⟨subd9_2_768, List.forall_mem_cons.2 ⟨subd9_2_769, List.forall_mem_cons.2 ⟨subd9_2_770, List.forall_mem_cons.2 ⟨subd9_2_771, List.forall_mem_cons.2 ⟨subd9_2_772, List.forall_mem_cons.2 ⟨subd9_2_773, List.forall_mem_cons.2 ⟨subd9_2_774, List.forall_mem_cons.2 ⟨subd9_2_775, List.forall_mem_cons.2 ⟨subd9_2_776, List.forall_mem_cons.2 ⟨subd9_2_777, List.forall_mem_cons.2 ⟨subd9_2_778, List.forall_mem_cons.2 ⟨subd9_2_779, List.forall_mem_cons.2 ⟨subd9_2_780, List.forall_mem_cons.2 ⟨subd9_2_781, List.forall_mem_cons.2 ⟨subd9_2_782, List.forall_mem_cons.2 ⟨subd9_2_783, List.forall_mem_cons.2 ⟨subd9_2_784, List.forall_mem_cons.2 ⟨subd9_2_785, List.forall_mem_cons.2 ⟨subd9_2_786, List.forall_mem_cons.2 ⟨subd9_2_787, List.forall_mem_cons.2 ⟨subd9_2_788, List.forall_mem_cons.2 ⟨subd9_2_789, List.forall_mem_cons.2 ⟨subd9_2_790, List.forall_mem_cons.2 ⟨subd9_2_791, List.forall_mem_cons.2 ⟨subd9_2_792, List.forall_mem_cons.2 ⟨subd9_2_793, List.forall_mem_cons.2 ⟨subd9_2_794, List.forall_mem_cons.2 ⟨subd9_2_795, List.forall_mem_cons.2 ⟨subd9_2_796, List.forall_mem_cons.2 ⟨subd9_2_797, List.forall_mem_cons.2 ⟨subd9_2_798, List.forall_mem_cons.2 ⟨subd9_2_799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_800 : subd9_2 [2, 0, -13] = true := by decide +kernel
theorem subd9_2_801 : subd9_2 [2, 0, -12] = true := by decide +kernel
theorem subd9_2_802 : subd9_2 [2, 0, -11] = true := by decide +kernel
theorem subd9_2_803 : subd9_2 [2, 0, -10] = true := by decide +kernel
theorem subd9_2_804 : subd9_2 [2, 0, -9] = true := by decide +kernel
theorem subd9_2_805 : subd9_2 [2, 0, -8] = true := by decide +kernel
theorem subd9_2_806 : subd9_2 [2, 0, -7] = true := by decide +kernel
theorem subd9_2_807 : subd9_2 [2, 0, -6] = true := by decide +kernel
theorem subd9_2_808 : subd9_2 [2, 0, -5] = true := by decide +kernel
theorem subd9_2_809 : subd9_2 [2, 0, -4] = true := by decide +kernel
theorem subd9_2_810 : subd9_2 [2, 0, -3] = true := by decide +kernel
theorem subd9_2_811 : subd9_2 [2, 0, -2] = true := by decide +kernel
theorem subd9_2_812 : subd9_2 [2, 0, -1] = true := by decide +kernel
theorem subd9_2_813 : subd9_2 [2, 0, 0] = true := by decide +kernel
theorem subd9_2_814 : subd9_2 [2, 0, 1] = true := by decide +kernel
theorem subd9_2_815 : subd9_2 [2, 0, 2] = true := by decide +kernel
theorem subd9_2_816 : subd9_2 [2, 0, 3] = true := by decide +kernel
theorem subd9_2_817 : subd9_2 [2, 0, 4] = true := by decide +kernel
theorem subd9_2_818 : subd9_2 [2, 0, 5] = true := by decide +kernel
theorem subd9_2_819 : subd9_2 [2, 0, 6] = true := by decide +kernel
theorem subd9_2_820 : subd9_2 [2, 0, 7] = true := by decide +kernel
theorem subd9_2_821 : subd9_2 [2, 0, 8] = true := by decide +kernel
theorem subd9_2_822 : subd9_2 [2, 0, 9] = true := by decide +kernel
theorem subd9_2_823 : subd9_2 [2, 0, 10] = true := by decide +kernel
theorem subd9_2_824 : subd9_2 [2, 0, 11] = true := by decide +kernel
theorem subd9_2_825 : subd9_2 [2, 0, 12] = true := by decide +kernel
theorem subd9_2_826 : subd9_2 [2, 0, 13] = true := by decide +kernel
theorem subd9_2_827 : subd9_2 [2, 0, 14] = true := by decide +kernel
theorem subd9_2_828 : subd9_2 [2, 1, -13] = true := by decide +kernel
theorem subd9_2_829 : subd9_2 [2, 1, -12] = true := by decide +kernel
theorem subd9_2_830 : subd9_2 [2, 1, -11] = true := by decide +kernel
theorem subd9_2_831 : subd9_2 [2, 1, -10] = true := by decide +kernel
theorem sbd9_2_25 : ∀ q ∈ blkd9_2_25, subd9_2 q = true := by
  unfold blkd9_2_25
  exact List.forall_mem_cons.2 ⟨subd9_2_800, List.forall_mem_cons.2 ⟨subd9_2_801, List.forall_mem_cons.2 ⟨subd9_2_802, List.forall_mem_cons.2 ⟨subd9_2_803, List.forall_mem_cons.2 ⟨subd9_2_804, List.forall_mem_cons.2 ⟨subd9_2_805, List.forall_mem_cons.2 ⟨subd9_2_806, List.forall_mem_cons.2 ⟨subd9_2_807, List.forall_mem_cons.2 ⟨subd9_2_808, List.forall_mem_cons.2 ⟨subd9_2_809, List.forall_mem_cons.2 ⟨subd9_2_810, List.forall_mem_cons.2 ⟨subd9_2_811, List.forall_mem_cons.2 ⟨subd9_2_812, List.forall_mem_cons.2 ⟨subd9_2_813, List.forall_mem_cons.2 ⟨subd9_2_814, List.forall_mem_cons.2 ⟨subd9_2_815, List.forall_mem_cons.2 ⟨subd9_2_816, List.forall_mem_cons.2 ⟨subd9_2_817, List.forall_mem_cons.2 ⟨subd9_2_818, List.forall_mem_cons.2 ⟨subd9_2_819, List.forall_mem_cons.2 ⟨subd9_2_820, List.forall_mem_cons.2 ⟨subd9_2_821, List.forall_mem_cons.2 ⟨subd9_2_822, List.forall_mem_cons.2 ⟨subd9_2_823, List.forall_mem_cons.2 ⟨subd9_2_824, List.forall_mem_cons.2 ⟨subd9_2_825, List.forall_mem_cons.2 ⟨subd9_2_826, List.forall_mem_cons.2 ⟨subd9_2_827, List.forall_mem_cons.2 ⟨subd9_2_828, List.forall_mem_cons.2 ⟨subd9_2_829, List.forall_mem_cons.2 ⟨subd9_2_830, List.forall_mem_cons.2 ⟨subd9_2_831, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_832 : subd9_2 [2, 1, -9] = true := by decide +kernel
theorem subd9_2_833 : subd9_2 [2, 1, -8] = true := by decide +kernel
theorem subd9_2_834 : subd9_2 [2, 1, -7] = true := by decide +kernel
theorem subd9_2_835 : subd9_2 [2, 1, -6] = true := by decide +kernel
theorem subd9_2_836 : subd9_2 [2, 1, -5] = true := by decide +kernel
theorem subd9_2_837 : subd9_2 [2, 1, -4] = true := by decide +kernel
theorem subd9_2_838 : subd9_2 [2, 1, -3] = true := by decide +kernel
theorem subd9_2_839 : subd9_2 [2, 1, -2] = true := by decide +kernel
theorem subd9_2_840 : subd9_2 [2, 1, -1] = true := by decide +kernel
theorem subd9_2_841 : subd9_2 [2, 1, 0] = true := by decide +kernel
theorem subd9_2_842 : subd9_2 [2, 1, 1] = true := by decide +kernel
theorem subd9_2_843 : subd9_2 [2, 1, 2] = true := by decide +kernel
theorem subd9_2_844 : subd9_2 [2, 1, 3] = true := by decide +kernel
theorem subd9_2_845 : subd9_2 [2, 1, 4] = true := by decide +kernel
theorem subd9_2_846 : subd9_2 [2, 1, 5] = true := by decide +kernel
theorem subd9_2_847 : subd9_2 [2, 1, 6] = true := by decide +kernel
theorem subd9_2_848 : subd9_2 [2, 1, 7] = true := by decide +kernel
theorem subd9_2_849 : subd9_2 [2, 1, 8] = true := by decide +kernel
theorem subd9_2_850 : subd9_2 [2, 1, 9] = true := by decide +kernel
theorem subd9_2_851 : subd9_2 [2, 1, 10] = true := by decide +kernel
theorem subd9_2_852 : subd9_2 [2, 1, 11] = true := by decide +kernel
theorem subd9_2_853 : subd9_2 [2, 1, 12] = true := by decide +kernel
theorem subd9_2_854 : subd9_2 [2, 1, 13] = true := by decide +kernel
theorem subd9_2_855 : subd9_2 [2, 2, -9] = true := by decide +kernel
theorem subd9_2_856 : subd9_2 [2, 2, -8] = true := by decide +kernel
theorem subd9_2_857 : subd9_2 [2, 2, -7] = true := by decide +kernel
theorem subd9_2_858 : subd9_2 [2, 2, -6] = true := by decide +kernel
theorem subd9_2_859 : subd9_2 [2, 2, -5] = true := by decide +kernel
theorem subd9_2_860 : subd9_2 [2, 2, -4] = true := by decide +kernel
theorem subd9_2_861 : subd9_2 [2, 2, -3] = true := by decide +kernel
theorem subd9_2_862 : subd9_2 [2, 2, -2] = true := by decide +kernel
theorem subd9_2_863 : subd9_2 [2, 2, -1] = true := by decide +kernel
theorem sbd9_2_26 : ∀ q ∈ blkd9_2_26, subd9_2 q = true := by
  unfold blkd9_2_26
  exact List.forall_mem_cons.2 ⟨subd9_2_832, List.forall_mem_cons.2 ⟨subd9_2_833, List.forall_mem_cons.2 ⟨subd9_2_834, List.forall_mem_cons.2 ⟨subd9_2_835, List.forall_mem_cons.2 ⟨subd9_2_836, List.forall_mem_cons.2 ⟨subd9_2_837, List.forall_mem_cons.2 ⟨subd9_2_838, List.forall_mem_cons.2 ⟨subd9_2_839, List.forall_mem_cons.2 ⟨subd9_2_840, List.forall_mem_cons.2 ⟨subd9_2_841, List.forall_mem_cons.2 ⟨subd9_2_842, List.forall_mem_cons.2 ⟨subd9_2_843, List.forall_mem_cons.2 ⟨subd9_2_844, List.forall_mem_cons.2 ⟨subd9_2_845, List.forall_mem_cons.2 ⟨subd9_2_846, List.forall_mem_cons.2 ⟨subd9_2_847, List.forall_mem_cons.2 ⟨subd9_2_848, List.forall_mem_cons.2 ⟨subd9_2_849, List.forall_mem_cons.2 ⟨subd9_2_850, List.forall_mem_cons.2 ⟨subd9_2_851, List.forall_mem_cons.2 ⟨subd9_2_852, List.forall_mem_cons.2 ⟨subd9_2_853, List.forall_mem_cons.2 ⟨subd9_2_854, List.forall_mem_cons.2 ⟨subd9_2_855, List.forall_mem_cons.2 ⟨subd9_2_856, List.forall_mem_cons.2 ⟨subd9_2_857, List.forall_mem_cons.2 ⟨subd9_2_858, List.forall_mem_cons.2 ⟨subd9_2_859, List.forall_mem_cons.2 ⟨subd9_2_860, List.forall_mem_cons.2 ⟨subd9_2_861, List.forall_mem_cons.2 ⟨subd9_2_862, List.forall_mem_cons.2 ⟨subd9_2_863, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_864 : subd9_2 [2, 2, 0] = true := by decide +kernel
theorem subd9_2_865 : subd9_2 [2, 2, 1] = true := by decide +kernel
theorem subd9_2_866 : subd9_2 [2, 2, 2] = true := by decide +kernel
theorem subd9_2_867 : subd9_2 [2, 2, 3] = true := by decide +kernel
theorem subd9_2_868 : subd9_2 [2, 2, 4] = true := by decide +kernel
theorem subd9_2_869 : subd9_2 [2, 2, 5] = true := by decide +kernel
theorem subd9_2_870 : subd9_2 [2, 2, 6] = true := by decide +kernel
theorem subd9_2_871 : subd9_2 [2, 2, 7] = true := by decide +kernel
theorem subd9_2_872 : subd9_2 [2, 2, 8] = true := by decide +kernel
theorem subd9_2_873 : subd9_2 [2, 2, 9] = true := by decide +kernel
theorem subd9_2_874 : subd9_2 [2, 2, 10] = true := by decide +kernel
theorem subd9_2_875 : subd9_2 [2, 2, 11] = true := by decide +kernel
theorem subd9_2_876 : subd9_2 [3, -2] = true := by decide +kernel
theorem subd9_2_877 : subd9_2 [3, -1, -8] = true := by decide +kernel
theorem subd9_2_878 : subd9_2 [3, -1, -7] = true := by decide +kernel
theorem subd9_2_879 : subd9_2 [3, -1, -6] = true := by decide +kernel
theorem subd9_2_880 : subd9_2 [3, -1, -5] = true := by decide +kernel
theorem subd9_2_881 : subd9_2 [3, -1, -4] = true := by decide +kernel
theorem subd9_2_882 : subd9_2 [3, -1, -3] = true := by decide +kernel
theorem subd9_2_883 : subd9_2 [3, -1, -2] = true := by decide +kernel
theorem subd9_2_884 : subd9_2 [3, -1, -1] = true := by decide +kernel
theorem subd9_2_885 : subd9_2 [3, -1, 0] = true := by decide +kernel
theorem subd9_2_886 : subd9_2 [3, -1, 1] = true := by decide +kernel
theorem subd9_2_887 : subd9_2 [3, -1, 2] = true := by decide +kernel
theorem subd9_2_888 : subd9_2 [3, -1, 3] = true := by decide +kernel
theorem subd9_2_889 : subd9_2 [3, -1, 4] = true := by decide +kernel
theorem subd9_2_890 : subd9_2 [3, -1, 5] = true := by decide +kernel
theorem subd9_2_891 : subd9_2 [3, -1, 6] = true := by decide +kernel
theorem subd9_2_892 : subd9_2 [3, -1, 7] = true := by decide +kernel
theorem subd9_2_893 : subd9_2 [3, 0, -9] = true := by decide +kernel
theorem subd9_2_894 : subd9_2 [3, 0, -8] = true := by decide +kernel
theorem subd9_2_895 : subd9_2 [3, 0, -7] = true := by decide +kernel
theorem sbd9_2_27 : ∀ q ∈ blkd9_2_27, subd9_2 q = true := by
  unfold blkd9_2_27
  exact List.forall_mem_cons.2 ⟨subd9_2_864, List.forall_mem_cons.2 ⟨subd9_2_865, List.forall_mem_cons.2 ⟨subd9_2_866, List.forall_mem_cons.2 ⟨subd9_2_867, List.forall_mem_cons.2 ⟨subd9_2_868, List.forall_mem_cons.2 ⟨subd9_2_869, List.forall_mem_cons.2 ⟨subd9_2_870, List.forall_mem_cons.2 ⟨subd9_2_871, List.forall_mem_cons.2 ⟨subd9_2_872, List.forall_mem_cons.2 ⟨subd9_2_873, List.forall_mem_cons.2 ⟨subd9_2_874, List.forall_mem_cons.2 ⟨subd9_2_875, List.forall_mem_cons.2 ⟨subd9_2_876, List.forall_mem_cons.2 ⟨subd9_2_877, List.forall_mem_cons.2 ⟨subd9_2_878, List.forall_mem_cons.2 ⟨subd9_2_879, List.forall_mem_cons.2 ⟨subd9_2_880, List.forall_mem_cons.2 ⟨subd9_2_881, List.forall_mem_cons.2 ⟨subd9_2_882, List.forall_mem_cons.2 ⟨subd9_2_883, List.forall_mem_cons.2 ⟨subd9_2_884, List.forall_mem_cons.2 ⟨subd9_2_885, List.forall_mem_cons.2 ⟨subd9_2_886, List.forall_mem_cons.2 ⟨subd9_2_887, List.forall_mem_cons.2 ⟨subd9_2_888, List.forall_mem_cons.2 ⟨subd9_2_889, List.forall_mem_cons.2 ⟨subd9_2_890, List.forall_mem_cons.2 ⟨subd9_2_891, List.forall_mem_cons.2 ⟨subd9_2_892, List.forall_mem_cons.2 ⟨subd9_2_893, List.forall_mem_cons.2 ⟨subd9_2_894, List.forall_mem_cons.2 ⟨subd9_2_895, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_896 : subd9_2 [3, 0, -6] = true := by decide +kernel
theorem subd9_2_897 : subd9_2 [3, 0, -5] = true := by decide +kernel
theorem subd9_2_898 : subd9_2 [3, 0, -4] = true := by decide +kernel
theorem subd9_2_899 : subd9_2 [3, 0, -3] = true := by decide +kernel
theorem subd9_2_900 : subd9_2 [3, 0, -2] = true := by decide +kernel
theorem subd9_2_901 : subd9_2 [3, 0, -1] = true := by decide +kernel
theorem subd9_2_902 : subd9_2 [3, 0, 0] = true := by decide +kernel
theorem subd9_2_903 : subd9_2 [3, 0, 1] = true := by decide +kernel
theorem subd9_2_904 : subd9_2 [3, 0, 2] = true := by decide +kernel
theorem subd9_2_905 : subd9_2 [3, 0, 3] = true := by decide +kernel
theorem subd9_2_906 : subd9_2 [3, 0, 4] = true := by decide +kernel
theorem subd9_2_907 : subd9_2 [3, 0, 5] = true := by decide +kernel
theorem subd9_2_908 : subd9_2 [3, 0, 6] = true := by decide +kernel
theorem subd9_2_909 : subd9_2 [3, 0, 7] = true := by decide +kernel
theorem subd9_2_910 : subd9_2 [3, 0, 8] = true := by decide +kernel
theorem subd9_2_911 : subd9_2 [3, 0, 9] = true := by decide +kernel
theorem subd9_2_912 : subd9_2 [3, 1, -7] = true := by decide +kernel
theorem subd9_2_913 : subd9_2 [3, 1, -6] = true := by decide +kernel
theorem subd9_2_914 : subd9_2 [3, 1, -5] = true := by decide +kernel
theorem subd9_2_915 : subd9_2 [3, 1, -4] = true := by decide +kernel
theorem subd9_2_916 : subd9_2 [3, 1, -3] = true := by decide +kernel
theorem subd9_2_917 : subd9_2 [3, 1, -2] = true := by decide +kernel
theorem subd9_2_918 : subd9_2 [3, 1, -1] = true := by decide +kernel
theorem subd9_2_919 : subd9_2 [3, 1, 0] = true := by decide +kernel
theorem subd9_2_920 : subd9_2 [3, 1, 1] = true := by decide +kernel
theorem subd9_2_921 : subd9_2 [3, 1, 2] = true := by decide +kernel
theorem subd9_2_922 : subd9_2 [3, 1, 3] = true := by decide +kernel
theorem subd9_2_923 : subd9_2 [3, 1, 4] = true := by decide +kernel
theorem subd9_2_924 : subd9_2 [3, 1, 5] = true := by decide +kernel
theorem subd9_2_925 : subd9_2 [3, 1, 6] = true := by decide +kernel
theorem subd9_2_926 : subd9_2 [3, 1, 7] = true := by decide +kernel
theorem sbd9_2_28 : ∀ q ∈ blkd9_2_28, subd9_2 q = true := by
  unfold blkd9_2_28
  exact List.forall_mem_cons.2 ⟨subd9_2_896, List.forall_mem_cons.2 ⟨subd9_2_897, List.forall_mem_cons.2 ⟨subd9_2_898, List.forall_mem_cons.2 ⟨subd9_2_899, List.forall_mem_cons.2 ⟨subd9_2_900, List.forall_mem_cons.2 ⟨subd9_2_901, List.forall_mem_cons.2 ⟨subd9_2_902, List.forall_mem_cons.2 ⟨subd9_2_903, List.forall_mem_cons.2 ⟨subd9_2_904, List.forall_mem_cons.2 ⟨subd9_2_905, List.forall_mem_cons.2 ⟨subd9_2_906, List.forall_mem_cons.2 ⟨subd9_2_907, List.forall_mem_cons.2 ⟨subd9_2_908, List.forall_mem_cons.2 ⟨subd9_2_909, List.forall_mem_cons.2 ⟨subd9_2_910, List.forall_mem_cons.2 ⟨subd9_2_911, List.forall_mem_cons.2 ⟨subd9_2_912, List.forall_mem_cons.2 ⟨subd9_2_913, List.forall_mem_cons.2 ⟨subd9_2_914, List.forall_mem_cons.2 ⟨subd9_2_915, List.forall_mem_cons.2 ⟨subd9_2_916, List.forall_mem_cons.2 ⟨subd9_2_917, List.forall_mem_cons.2 ⟨subd9_2_918, List.forall_mem_cons.2 ⟨subd9_2_919, List.forall_mem_cons.2 ⟨subd9_2_920, List.forall_mem_cons.2 ⟨subd9_2_921, List.forall_mem_cons.2 ⟨subd9_2_922, List.forall_mem_cons.2 ⟨subd9_2_923, List.forall_mem_cons.2 ⟨subd9_2_924, List.forall_mem_cons.2 ⟨subd9_2_925, List.forall_mem_cons.2 ⟨subd9_2_926, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_3 : ldCheck G d9_3.U d9_3.ms ldd9_3 = true := by decide +kernel
theorem pre_okd9_3 : subPre G cell9 d9_3 = true := by decide +kernel
theorem subd9_3_0 : subd9_3 [-6] = true := by decide +kernel
theorem subd9_3_1 : subd9_3 [-5, -4] = true := by decide +kernel
theorem subd9_3_2 : subd9_3 [-5, -3] = true := by decide +kernel
theorem subd9_3_3 : subd9_3 [-5, -2] = true := by decide +kernel
theorem subd9_3_4 : subd9_3 [-5, -1] = true := by decide +kernel
theorem subd9_3_5 : subd9_3 [-5, 0] = true := by decide +kernel
theorem subd9_3_6 : subd9_3 [-5, 1] = true := by decide +kernel
theorem subd9_3_7 : subd9_3 [-5, 2] = true := by decide +kernel
theorem subd9_3_8 : subd9_3 [-5, 3] = true := by decide +kernel
theorem subd9_3_9 : subd9_3 [-4, -5] = true := by decide +kernel
theorem subd9_3_10 : subd9_3 [-4, -4] = true := by decide +kernel
theorem subd9_3_11 : subd9_3 [-4, -3] = true := by decide +kernel
theorem subd9_3_12 : subd9_3 [-4, -2, -8] = true := by decide +kernel
theorem subd9_3_13 : subd9_3 [-4, -2, -7] = true := by decide +kernel
theorem subd9_3_14 : subd9_3 [-4, -2, -6] = true := by decide +kernel
theorem subd9_3_15 : subd9_3 [-4, -2, -5] = true := by decide +kernel
theorem subd9_3_16 : subd9_3 [-4, -2, -4] = true := by decide +kernel
theorem subd9_3_17 : subd9_3 [-4, -2, -3] = true := by decide +kernel
theorem subd9_3_18 : subd9_3 [-4, -2, -2] = true := by decide +kernel
theorem subd9_3_19 : subd9_3 [-4, -2, -1] = true := by decide +kernel
theorem subd9_3_20 : subd9_3 [-4, -2, 0] = true := by decide +kernel
theorem subd9_3_21 : subd9_3 [-4, -2, 1] = true := by decide +kernel
theorem subd9_3_22 : subd9_3 [-4, -2, 2] = true := by decide +kernel
theorem subd9_3_23 : subd9_3 [-4, -2, 3] = true := by decide +kernel
theorem subd9_3_24 : subd9_3 [-4, -2, 4] = true := by decide +kernel
theorem subd9_3_25 : subd9_3 [-4, -2, 5] = true := by decide +kernel
theorem subd9_3_26 : subd9_3 [-4, -2, 6] = true := by decide +kernel
theorem subd9_3_27 : subd9_3 [-4, -1, -8] = true := by decide +kernel
theorem subd9_3_28 : subd9_3 [-4, -1, -7] = true := by decide +kernel
theorem subd9_3_29 : subd9_3 [-4, -1, -6] = true := by decide +kernel
theorem subd9_3_30 : subd9_3 [-4, -1, -5] = true := by decide +kernel
theorem subd9_3_31 : subd9_3 [-4, -1, -4] = true := by decide +kernel
theorem sbd9_3_0 : ∀ q ∈ blkd9_3_0, subd9_3 q = true := by
  unfold blkd9_3_0
  exact List.forall_mem_cons.2 ⟨subd9_3_0, List.forall_mem_cons.2 ⟨subd9_3_1, List.forall_mem_cons.2 ⟨subd9_3_2, List.forall_mem_cons.2 ⟨subd9_3_3, List.forall_mem_cons.2 ⟨subd9_3_4, List.forall_mem_cons.2 ⟨subd9_3_5, List.forall_mem_cons.2 ⟨subd9_3_6, List.forall_mem_cons.2 ⟨subd9_3_7, List.forall_mem_cons.2 ⟨subd9_3_8, List.forall_mem_cons.2 ⟨subd9_3_9, List.forall_mem_cons.2 ⟨subd9_3_10, List.forall_mem_cons.2 ⟨subd9_3_11, List.forall_mem_cons.2 ⟨subd9_3_12, List.forall_mem_cons.2 ⟨subd9_3_13, List.forall_mem_cons.2 ⟨subd9_3_14, List.forall_mem_cons.2 ⟨subd9_3_15, List.forall_mem_cons.2 ⟨subd9_3_16, List.forall_mem_cons.2 ⟨subd9_3_17, List.forall_mem_cons.2 ⟨subd9_3_18, List.forall_mem_cons.2 ⟨subd9_3_19, List.forall_mem_cons.2 ⟨subd9_3_20, List.forall_mem_cons.2 ⟨subd9_3_21, List.forall_mem_cons.2 ⟨subd9_3_22, List.forall_mem_cons.2 ⟨subd9_3_23, List.forall_mem_cons.2 ⟨subd9_3_24, List.forall_mem_cons.2 ⟨subd9_3_25, List.forall_mem_cons.2 ⟨subd9_3_26, List.forall_mem_cons.2 ⟨subd9_3_27, List.forall_mem_cons.2 ⟨subd9_3_28, List.forall_mem_cons.2 ⟨subd9_3_29, List.forall_mem_cons.2 ⟨subd9_3_30, List.forall_mem_cons.2 ⟨subd9_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_32 : subd9_3 [-4, -1, -3] = true := by decide +kernel
theorem subd9_3_33 : subd9_3 [-4, -1, -2] = true := by decide +kernel
theorem subd9_3_34 : subd9_3 [-4, -1, -1] = true := by decide +kernel
theorem subd9_3_35 : subd9_3 [-4, -1, 0] = true := by decide +kernel
theorem subd9_3_36 : subd9_3 [-4, -1, 1] = true := by decide +kernel
theorem subd9_3_37 : subd9_3 [-4, -1, 2] = true := by decide +kernel
theorem subd9_3_38 : subd9_3 [-4, -1, 3] = true := by decide +kernel
theorem subd9_3_39 : subd9_3 [-4, -1, 4] = true := by decide +kernel
theorem subd9_3_40 : subd9_3 [-4, -1, 5] = true := by decide +kernel
theorem subd9_3_41 : subd9_3 [-4, -1, 6] = true := by decide +kernel
theorem subd9_3_42 : subd9_3 [-4, 0, -9] = true := by decide +kernel
theorem subd9_3_43 : subd9_3 [-4, 0, -8] = true := by decide +kernel
theorem subd9_3_44 : subd9_3 [-4, 0, -7] = true := by decide +kernel
theorem subd9_3_45 : subd9_3 [-4, 0, -6] = true := by decide +kernel
theorem subd9_3_46 : subd9_3 [-4, 0, -5] = true := by decide +kernel
theorem subd9_3_47 : subd9_3 [-4, 0, -4] = true := by decide +kernel
theorem subd9_3_48 : subd9_3 [-4, 0, -3] = true := by decide +kernel
theorem subd9_3_49 : subd9_3 [-4, 0, -2] = true := by decide +kernel
theorem subd9_3_50 : subd9_3 [-4, 0, -1] = true := by decide +kernel
theorem subd9_3_51 : subd9_3 [-4, 0, 0] = true := by decide +kernel
theorem subd9_3_52 : subd9_3 [-4, 0, 1] = true := by decide +kernel
theorem subd9_3_53 : subd9_3 [-4, 0, 2] = true := by decide +kernel
theorem subd9_3_54 : subd9_3 [-4, 0, 3] = true := by decide +kernel
theorem subd9_3_55 : subd9_3 [-4, 0, 4] = true := by decide +kernel
theorem subd9_3_56 : subd9_3 [-4, 0, 5] = true := by decide +kernel
theorem subd9_3_57 : subd9_3 [-4, 0, 6] = true := by decide +kernel
theorem subd9_3_58 : subd9_3 [-4, 1, -8] = true := by decide +kernel
theorem subd9_3_59 : subd9_3 [-4, 1, -7] = true := by decide +kernel
theorem subd9_3_60 : subd9_3 [-4, 1, -6] = true := by decide +kernel
theorem subd9_3_61 : subd9_3 [-4, 1, -5] = true := by decide +kernel
theorem subd9_3_62 : subd9_3 [-4, 1, -4] = true := by decide +kernel
theorem subd9_3_63 : subd9_3 [-4, 1, -3] = true := by decide +kernel
theorem sbd9_3_1 : ∀ q ∈ blkd9_3_1, subd9_3 q = true := by
  unfold blkd9_3_1
  exact List.forall_mem_cons.2 ⟨subd9_3_32, List.forall_mem_cons.2 ⟨subd9_3_33, List.forall_mem_cons.2 ⟨subd9_3_34, List.forall_mem_cons.2 ⟨subd9_3_35, List.forall_mem_cons.2 ⟨subd9_3_36, List.forall_mem_cons.2 ⟨subd9_3_37, List.forall_mem_cons.2 ⟨subd9_3_38, List.forall_mem_cons.2 ⟨subd9_3_39, List.forall_mem_cons.2 ⟨subd9_3_40, List.forall_mem_cons.2 ⟨subd9_3_41, List.forall_mem_cons.2 ⟨subd9_3_42, List.forall_mem_cons.2 ⟨subd9_3_43, List.forall_mem_cons.2 ⟨subd9_3_44, List.forall_mem_cons.2 ⟨subd9_3_45, List.forall_mem_cons.2 ⟨subd9_3_46, List.forall_mem_cons.2 ⟨subd9_3_47, List.forall_mem_cons.2 ⟨subd9_3_48, List.forall_mem_cons.2 ⟨subd9_3_49, List.forall_mem_cons.2 ⟨subd9_3_50, List.forall_mem_cons.2 ⟨subd9_3_51, List.forall_mem_cons.2 ⟨subd9_3_52, List.forall_mem_cons.2 ⟨subd9_3_53, List.forall_mem_cons.2 ⟨subd9_3_54, List.forall_mem_cons.2 ⟨subd9_3_55, List.forall_mem_cons.2 ⟨subd9_3_56, List.forall_mem_cons.2 ⟨subd9_3_57, List.forall_mem_cons.2 ⟨subd9_3_58, List.forall_mem_cons.2 ⟨subd9_3_59, List.forall_mem_cons.2 ⟨subd9_3_60, List.forall_mem_cons.2 ⟨subd9_3_61, List.forall_mem_cons.2 ⟨subd9_3_62, List.forall_mem_cons.2 ⟨subd9_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C096
