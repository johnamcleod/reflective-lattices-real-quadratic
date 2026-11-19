import ReflectZphi.Data.Cert5.C142.Base

namespace ReflectZphi.Data.Cert5.C142

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd14_2_672 : subd14_2 [1, 3, 1] = true := by decide +kernel
theorem subd14_2_673 : subd14_2 [1, 3, 2] = true := by decide +kernel
theorem subd14_2_674 : subd14_2 [1, 3, 3] = true := by decide +kernel
theorem subd14_2_675 : subd14_2 [1, 3, 4] = true := by decide +kernel
theorem subd14_2_676 : subd14_2 [1, 3, 5] = true := by decide +kernel
theorem subd14_2_677 : subd14_2 [1, 3, 6] = true := by decide +kernel
theorem subd14_2_678 : subd14_2 [1, 3, 7] = true := by decide +kernel
theorem subd14_2_679 : subd14_2 [1, 4] = true := by decide +kernel
theorem subd14_2_680 : subd14_2 [1, 5] = true := by decide +kernel
theorem subd14_2_681 : subd14_2 [2, -7] = true := by decide +kernel
theorem subd14_2_682 : subd14_2 [2, -6] = true := by decide +kernel
theorem subd14_2_683 : subd14_2 [2, -5] = true := by decide +kernel
theorem subd14_2_684 : subd14_2 [2, -4, -7] = true := by decide +kernel
theorem subd14_2_685 : subd14_2 [2, -4, -6] = true := by decide +kernel
theorem subd14_2_686 : subd14_2 [2, -4, -5] = true := by decide +kernel
theorem subd14_2_687 : subd14_2 [2, -4, -4] = true := by decide +kernel
theorem subd14_2_688 : subd14_2 [2, -4, -3] = true := by decide +kernel
theorem subd14_2_689 : subd14_2 [2, -4, -2] = true := by decide +kernel
theorem subd14_2_690 : subd14_2 [2, -4, -1] = true := by decide +kernel
theorem subd14_2_691 : subd14_2 [2, -4, 0] = true := by decide +kernel
theorem subd14_2_692 : subd14_2 [2, -4, 1] = true := by decide +kernel
theorem subd14_2_693 : subd14_2 [2, -4, 2] = true := by decide +kernel
theorem subd14_2_694 : subd14_2 [2, -4, 3] = true := by decide +kernel
theorem subd14_2_695 : subd14_2 [2, -4, 4] = true := by decide +kernel
theorem subd14_2_696 : subd14_2 [2, -4, 5] = true := by decide +kernel
theorem subd14_2_697 : subd14_2 [2, -4, 6] = true := by decide +kernel
theorem subd14_2_698 : subd14_2 [2, -4, 7] = true := by decide +kernel
theorem subd14_2_699 : subd14_2 [2, -3, -8] = true := by decide +kernel
theorem subd14_2_700 : subd14_2 [2, -3, -7] = true := by decide +kernel
theorem subd14_2_701 : subd14_2 [2, -3, -6] = true := by decide +kernel
theorem subd14_2_702 : subd14_2 [2, -3, -5] = true := by decide +kernel
theorem subd14_2_703 : subd14_2 [2, -3, -4] = true := by decide +kernel
theorem sbd14_2_21 : ∀ q ∈ blkd14_2_21, subd14_2 q = true := by
  unfold blkd14_2_21
  exact List.forall_mem_cons.2 ⟨subd14_2_672, List.forall_mem_cons.2 ⟨subd14_2_673, List.forall_mem_cons.2 ⟨subd14_2_674, List.forall_mem_cons.2 ⟨subd14_2_675, List.forall_mem_cons.2 ⟨subd14_2_676, List.forall_mem_cons.2 ⟨subd14_2_677, List.forall_mem_cons.2 ⟨subd14_2_678, List.forall_mem_cons.2 ⟨subd14_2_679, List.forall_mem_cons.2 ⟨subd14_2_680, List.forall_mem_cons.2 ⟨subd14_2_681, List.forall_mem_cons.2 ⟨subd14_2_682, List.forall_mem_cons.2 ⟨subd14_2_683, List.forall_mem_cons.2 ⟨subd14_2_684, List.forall_mem_cons.2 ⟨subd14_2_685, List.forall_mem_cons.2 ⟨subd14_2_686, List.forall_mem_cons.2 ⟨subd14_2_687, List.forall_mem_cons.2 ⟨subd14_2_688, List.forall_mem_cons.2 ⟨subd14_2_689, List.forall_mem_cons.2 ⟨subd14_2_690, List.forall_mem_cons.2 ⟨subd14_2_691, List.forall_mem_cons.2 ⟨subd14_2_692, List.forall_mem_cons.2 ⟨subd14_2_693, List.forall_mem_cons.2 ⟨subd14_2_694, List.forall_mem_cons.2 ⟨subd14_2_695, List.forall_mem_cons.2 ⟨subd14_2_696, List.forall_mem_cons.2 ⟨subd14_2_697, List.forall_mem_cons.2 ⟨subd14_2_698, List.forall_mem_cons.2 ⟨subd14_2_699, List.forall_mem_cons.2 ⟨subd14_2_700, List.forall_mem_cons.2 ⟨subd14_2_701, List.forall_mem_cons.2 ⟨subd14_2_702, List.forall_mem_cons.2 ⟨subd14_2_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_2_704 : subd14_2 [2, -3, -3] = true := by decide +kernel
theorem subd14_2_705 : subd14_2 [2, -3, -2] = true := by decide +kernel
theorem subd14_2_706 : subd14_2 [2, -3, -1] = true := by decide +kernel
theorem subd14_2_707 : subd14_2 [2, -3, 0] = true := by decide +kernel
theorem subd14_2_708 : subd14_2 [2, -3, 1] = true := by decide +kernel
theorem subd14_2_709 : subd14_2 [2, -3, 2] = true := by decide +kernel
theorem subd14_2_710 : subd14_2 [2, -3, 3] = true := by decide +kernel
theorem subd14_2_711 : subd14_2 [2, -3, 4] = true := by decide +kernel
theorem subd14_2_712 : subd14_2 [2, -3, 5] = true := by decide +kernel
theorem subd14_2_713 : subd14_2 [2, -3, 6] = true := by decide +kernel
theorem subd14_2_714 : subd14_2 [2, -3, 7] = true := by decide +kernel
theorem subd14_2_715 : subd14_2 [2, -2, -8] = true := by decide +kernel
theorem subd14_2_716 : subd14_2 [2, -2, -7] = true := by decide +kernel
theorem subd14_2_717 : subd14_2 [2, -2, -6] = true := by decide +kernel
theorem subd14_2_718 : subd14_2 [2, -2, -5] = true := by decide +kernel
theorem subd14_2_719 : subd14_2 [2, -2, -4] = true := by decide +kernel
theorem subd14_2_720 : subd14_2 [2, -2, -3] = true := by decide +kernel
theorem subd14_2_721 : subd14_2 [2, -2, -2] = true := by decide +kernel
theorem subd14_2_722 : subd14_2 [2, -2, -1] = true := by decide +kernel
theorem subd14_2_723 : subd14_2 [2, -2, 0] = true := by decide +kernel
theorem subd14_2_724 : subd14_2 [2, -2, 1] = true := by decide +kernel
theorem subd14_2_725 : subd14_2 [2, -2, 2] = true := by decide +kernel
theorem subd14_2_726 : subd14_2 [2, -2, 3] = true := by decide +kernel
theorem subd14_2_727 : subd14_2 [2, -2, 4] = true := by decide +kernel
theorem subd14_2_728 : subd14_2 [2, -2, 5] = true := by decide +kernel
theorem subd14_2_729 : subd14_2 [2, -2, 6] = true := by decide +kernel
theorem subd14_2_730 : subd14_2 [2, -2, 7] = true := by decide +kernel
theorem subd14_2_731 : subd14_2 [2, -2, 8] = true := by decide +kernel
theorem subd14_2_732 : subd14_2 [2, -1, -8] = true := by decide +kernel
theorem subd14_2_733 : subd14_2 [2, -1, -7] = true := by decide +kernel
theorem subd14_2_734 : subd14_2 [2, -1, -6] = true := by decide +kernel
theorem subd14_2_735 : subd14_2 [2, -1, -5] = true := by decide +kernel
theorem sbd14_2_22 : ∀ q ∈ blkd14_2_22, subd14_2 q = true := by
  unfold blkd14_2_22
  exact List.forall_mem_cons.2 ⟨subd14_2_704, List.forall_mem_cons.2 ⟨subd14_2_705, List.forall_mem_cons.2 ⟨subd14_2_706, List.forall_mem_cons.2 ⟨subd14_2_707, List.forall_mem_cons.2 ⟨subd14_2_708, List.forall_mem_cons.2 ⟨subd14_2_709, List.forall_mem_cons.2 ⟨subd14_2_710, List.forall_mem_cons.2 ⟨subd14_2_711, List.forall_mem_cons.2 ⟨subd14_2_712, List.forall_mem_cons.2 ⟨subd14_2_713, List.forall_mem_cons.2 ⟨subd14_2_714, List.forall_mem_cons.2 ⟨subd14_2_715, List.forall_mem_cons.2 ⟨subd14_2_716, List.forall_mem_cons.2 ⟨subd14_2_717, List.forall_mem_cons.2 ⟨subd14_2_718, List.forall_mem_cons.2 ⟨subd14_2_719, List.forall_mem_cons.2 ⟨subd14_2_720, List.forall_mem_cons.2 ⟨subd14_2_721, List.forall_mem_cons.2 ⟨subd14_2_722, List.forall_mem_cons.2 ⟨subd14_2_723, List.forall_mem_cons.2 ⟨subd14_2_724, List.forall_mem_cons.2 ⟨subd14_2_725, List.forall_mem_cons.2 ⟨subd14_2_726, List.forall_mem_cons.2 ⟨subd14_2_727, List.forall_mem_cons.2 ⟨subd14_2_728, List.forall_mem_cons.2 ⟨subd14_2_729, List.forall_mem_cons.2 ⟨subd14_2_730, List.forall_mem_cons.2 ⟨subd14_2_731, List.forall_mem_cons.2 ⟨subd14_2_732, List.forall_mem_cons.2 ⟨subd14_2_733, List.forall_mem_cons.2 ⟨subd14_2_734, List.forall_mem_cons.2 ⟨subd14_2_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_2_736 : subd14_2 [2, -1, -4] = true := by decide +kernel
theorem subd14_2_737 : subd14_2 [2, -1, -3] = true := by decide +kernel
theorem subd14_2_738 : subd14_2 [2, -1, -2] = true := by decide +kernel
theorem subd14_2_739 : subd14_2 [2, -1, -1] = true := by decide +kernel
theorem subd14_2_740 : subd14_2 [2, -1, 0] = true := by decide +kernel
theorem subd14_2_741 : subd14_2 [2, -1, 1] = true := by decide +kernel
theorem subd14_2_742 : subd14_2 [2, -1, 2] = true := by decide +kernel
theorem subd14_2_743 : subd14_2 [2, -1, 3] = true := by decide +kernel
theorem subd14_2_744 : subd14_2 [2, -1, 4] = true := by decide +kernel
theorem subd14_2_745 : subd14_2 [2, -1, 5] = true := by decide +kernel
theorem subd14_2_746 : subd14_2 [2, -1, 6] = true := by decide +kernel
theorem subd14_2_747 : subd14_2 [2, -1, 7] = true := by decide +kernel
theorem subd14_2_748 : subd14_2 [2, -1, 8] = true := by decide +kernel
theorem subd14_2_749 : subd14_2 [2, 0, -8] = true := by decide +kernel
theorem subd14_2_750 : subd14_2 [2, 0, -7] = true := by decide +kernel
theorem subd14_2_751 : subd14_2 [2, 0, -6] = true := by decide +kernel
theorem subd14_2_752 : subd14_2 [2, 0, -5] = true := by decide +kernel
theorem subd14_2_753 : subd14_2 [2, 0, -4] = true := by decide +kernel
theorem subd14_2_754 : subd14_2 [2, 0, -3] = true := by decide +kernel
theorem subd14_2_755 : subd14_2 [2, 0, -2] = true := by decide +kernel
theorem subd14_2_756 : subd14_2 [2, 0, -1] = true := by decide +kernel
theorem subd14_2_757 : subd14_2 [2, 0, 0] = true := by decide +kernel
theorem subd14_2_758 : subd14_2 [2, 0, 1] = true := by decide +kernel
theorem subd14_2_759 : subd14_2 [2, 0, 2] = true := by decide +kernel
theorem subd14_2_760 : subd14_2 [2, 0, 3] = true := by decide +kernel
theorem subd14_2_761 : subd14_2 [2, 0, 4] = true := by decide +kernel
theorem subd14_2_762 : subd14_2 [2, 0, 5] = true := by decide +kernel
theorem subd14_2_763 : subd14_2 [2, 0, 6] = true := by decide +kernel
theorem subd14_2_764 : subd14_2 [2, 0, 7] = true := by decide +kernel
theorem subd14_2_765 : subd14_2 [2, 0, 8] = true := by decide +kernel
theorem subd14_2_766 : subd14_2 [2, 1, -8] = true := by decide +kernel
theorem subd14_2_767 : subd14_2 [2, 1, -7] = true := by decide +kernel
theorem sbd14_2_23 : ∀ q ∈ blkd14_2_23, subd14_2 q = true := by
  unfold blkd14_2_23
  exact List.forall_mem_cons.2 ⟨subd14_2_736, List.forall_mem_cons.2 ⟨subd14_2_737, List.forall_mem_cons.2 ⟨subd14_2_738, List.forall_mem_cons.2 ⟨subd14_2_739, List.forall_mem_cons.2 ⟨subd14_2_740, List.forall_mem_cons.2 ⟨subd14_2_741, List.forall_mem_cons.2 ⟨subd14_2_742, List.forall_mem_cons.2 ⟨subd14_2_743, List.forall_mem_cons.2 ⟨subd14_2_744, List.forall_mem_cons.2 ⟨subd14_2_745, List.forall_mem_cons.2 ⟨subd14_2_746, List.forall_mem_cons.2 ⟨subd14_2_747, List.forall_mem_cons.2 ⟨subd14_2_748, List.forall_mem_cons.2 ⟨subd14_2_749, List.forall_mem_cons.2 ⟨subd14_2_750, List.forall_mem_cons.2 ⟨subd14_2_751, List.forall_mem_cons.2 ⟨subd14_2_752, List.forall_mem_cons.2 ⟨subd14_2_753, List.forall_mem_cons.2 ⟨subd14_2_754, List.forall_mem_cons.2 ⟨subd14_2_755, List.forall_mem_cons.2 ⟨subd14_2_756, List.forall_mem_cons.2 ⟨subd14_2_757, List.forall_mem_cons.2 ⟨subd14_2_758, List.forall_mem_cons.2 ⟨subd14_2_759, List.forall_mem_cons.2 ⟨subd14_2_760, List.forall_mem_cons.2 ⟨subd14_2_761, List.forall_mem_cons.2 ⟨subd14_2_762, List.forall_mem_cons.2 ⟨subd14_2_763, List.forall_mem_cons.2 ⟨subd14_2_764, List.forall_mem_cons.2 ⟨subd14_2_765, List.forall_mem_cons.2 ⟨subd14_2_766, List.forall_mem_cons.2 ⟨subd14_2_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_2_768 : subd14_2 [2, 1, -6] = true := by decide +kernel
theorem subd14_2_769 : subd14_2 [2, 1, -5] = true := by decide +kernel
theorem subd14_2_770 : subd14_2 [2, 1, -4] = true := by decide +kernel
theorem subd14_2_771 : subd14_2 [2, 1, -3] = true := by decide +kernel
theorem subd14_2_772 : subd14_2 [2, 1, -2] = true := by decide +kernel
theorem subd14_2_773 : subd14_2 [2, 1, -1] = true := by decide +kernel
theorem subd14_2_774 : subd14_2 [2, 1, 0] = true := by decide +kernel
theorem subd14_2_775 : subd14_2 [2, 1, 1] = true := by decide +kernel
theorem subd14_2_776 : subd14_2 [2, 1, 2] = true := by decide +kernel
theorem subd14_2_777 : subd14_2 [2, 1, 3] = true := by decide +kernel
theorem subd14_2_778 : subd14_2 [2, 1, 4] = true := by decide +kernel
theorem subd14_2_779 : subd14_2 [2, 1, 5] = true := by decide +kernel
theorem subd14_2_780 : subd14_2 [2, 1, 6] = true := by decide +kernel
theorem subd14_2_781 : subd14_2 [2, 1, 7] = true := by decide +kernel
theorem subd14_2_782 : subd14_2 [2, 1, 8] = true := by decide +kernel
theorem subd14_2_783 : subd14_2 [2, 2, -7] = true := by decide +kernel
theorem subd14_2_784 : subd14_2 [2, 2, -6] = true := by decide +kernel
theorem subd14_2_785 : subd14_2 [2, 2, -5] = true := by decide +kernel
theorem subd14_2_786 : subd14_2 [2, 2, -4] = true := by decide +kernel
theorem subd14_2_787 : subd14_2 [2, 2, -3] = true := by decide +kernel
theorem subd14_2_788 : subd14_2 [2, 2, -2] = true := by decide +kernel
theorem subd14_2_789 : subd14_2 [2, 2, -1] = true := by decide +kernel
theorem subd14_2_790 : subd14_2 [2, 2, 0] = true := by decide +kernel
theorem subd14_2_791 : subd14_2 [2, 2, 1] = true := by decide +kernel
theorem subd14_2_792 : subd14_2 [2, 2, 2] = true := by decide +kernel
theorem subd14_2_793 : subd14_2 [2, 2, 3] = true := by decide +kernel
theorem subd14_2_794 : subd14_2 [2, 2, 4] = true := by decide +kernel
theorem subd14_2_795 : subd14_2 [2, 2, 5] = true := by decide +kernel
theorem subd14_2_796 : subd14_2 [2, 2, 6] = true := by decide +kernel
theorem subd14_2_797 : subd14_2 [2, 2, 7] = true := by decide +kernel
theorem subd14_2_798 : subd14_2 [2, 2, 8] = true := by decide +kernel
theorem subd14_2_799 : subd14_2 [2, 3, -6] = true := by decide +kernel
theorem sbd14_2_24 : ∀ q ∈ blkd14_2_24, subd14_2 q = true := by
  unfold blkd14_2_24
  exact List.forall_mem_cons.2 ⟨subd14_2_768, List.forall_mem_cons.2 ⟨subd14_2_769, List.forall_mem_cons.2 ⟨subd14_2_770, List.forall_mem_cons.2 ⟨subd14_2_771, List.forall_mem_cons.2 ⟨subd14_2_772, List.forall_mem_cons.2 ⟨subd14_2_773, List.forall_mem_cons.2 ⟨subd14_2_774, List.forall_mem_cons.2 ⟨subd14_2_775, List.forall_mem_cons.2 ⟨subd14_2_776, List.forall_mem_cons.2 ⟨subd14_2_777, List.forall_mem_cons.2 ⟨subd14_2_778, List.forall_mem_cons.2 ⟨subd14_2_779, List.forall_mem_cons.2 ⟨subd14_2_780, List.forall_mem_cons.2 ⟨subd14_2_781, List.forall_mem_cons.2 ⟨subd14_2_782, List.forall_mem_cons.2 ⟨subd14_2_783, List.forall_mem_cons.2 ⟨subd14_2_784, List.forall_mem_cons.2 ⟨subd14_2_785, List.forall_mem_cons.2 ⟨subd14_2_786, List.forall_mem_cons.2 ⟨subd14_2_787, List.forall_mem_cons.2 ⟨subd14_2_788, List.forall_mem_cons.2 ⟨subd14_2_789, List.forall_mem_cons.2 ⟨subd14_2_790, List.forall_mem_cons.2 ⟨subd14_2_791, List.forall_mem_cons.2 ⟨subd14_2_792, List.forall_mem_cons.2 ⟨subd14_2_793, List.forall_mem_cons.2 ⟨subd14_2_794, List.forall_mem_cons.2 ⟨subd14_2_795, List.forall_mem_cons.2 ⟨subd14_2_796, List.forall_mem_cons.2 ⟨subd14_2_797, List.forall_mem_cons.2 ⟨subd14_2_798, List.forall_mem_cons.2 ⟨subd14_2_799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_2_800 : subd14_2 [2, 3, -5] = true := by decide +kernel
theorem subd14_2_801 : subd14_2 [2, 3, -4] = true := by decide +kernel
theorem subd14_2_802 : subd14_2 [2, 3, -3] = true := by decide +kernel
theorem subd14_2_803 : subd14_2 [2, 3, -2] = true := by decide +kernel
theorem subd14_2_804 : subd14_2 [2, 3, -1] = true := by decide +kernel
theorem subd14_2_805 : subd14_2 [2, 3, 0] = true := by decide +kernel
theorem subd14_2_806 : subd14_2 [2, 3, 1] = true := by decide +kernel
theorem subd14_2_807 : subd14_2 [2, 3, 2] = true := by decide +kernel
theorem subd14_2_808 : subd14_2 [2, 3, 3] = true := by decide +kernel
theorem subd14_2_809 : subd14_2 [2, 3, 4] = true := by decide +kernel
theorem subd14_2_810 : subd14_2 [2, 3, 5] = true := by decide +kernel
theorem subd14_2_811 : subd14_2 [2, 3, 6] = true := by decide +kernel
theorem subd14_2_812 : subd14_2 [2, 3, 7] = true := by decide +kernel
theorem subd14_2_813 : subd14_2 [2, 4] = true := by decide +kernel
theorem subd14_2_814 : subd14_2 [2, 5] = true := by decide +kernel
theorem subd14_2_815 : subd14_2 [3, -7] = true := by decide +kernel
theorem subd14_2_816 : subd14_2 [3, -6] = true := by decide +kernel
theorem subd14_2_817 : subd14_2 [3, -5] = true := by decide +kernel
theorem subd14_2_818 : subd14_2 [3, -4] = true := by decide +kernel
theorem subd14_2_819 : subd14_2 [3, -3, -7] = true := by decide +kernel
theorem subd14_2_820 : subd14_2 [3, -3, -6] = true := by decide +kernel
theorem subd14_2_821 : subd14_2 [3, -3, -5] = true := by decide +kernel
theorem subd14_2_822 : subd14_2 [3, -3, -4] = true := by decide +kernel
theorem subd14_2_823 : subd14_2 [3, -3, -3] = true := by decide +kernel
theorem subd14_2_824 : subd14_2 [3, -3, -2] = true := by decide +kernel
theorem subd14_2_825 : subd14_2 [3, -3, -1] = true := by decide +kernel
theorem subd14_2_826 : subd14_2 [3, -3, 0] = true := by decide +kernel
theorem subd14_2_827 : subd14_2 [3, -3, 1] = true := by decide +kernel
theorem subd14_2_828 : subd14_2 [3, -3, 2] = true := by decide +kernel
theorem subd14_2_829 : subd14_2 [3, -3, 3] = true := by decide +kernel
theorem subd14_2_830 : subd14_2 [3, -3, 4] = true := by decide +kernel
theorem subd14_2_831 : subd14_2 [3, -3, 5] = true := by decide +kernel
theorem sbd14_2_25 : ∀ q ∈ blkd14_2_25, subd14_2 q = true := by
  unfold blkd14_2_25
  exact List.forall_mem_cons.2 ⟨subd14_2_800, List.forall_mem_cons.2 ⟨subd14_2_801, List.forall_mem_cons.2 ⟨subd14_2_802, List.forall_mem_cons.2 ⟨subd14_2_803, List.forall_mem_cons.2 ⟨subd14_2_804, List.forall_mem_cons.2 ⟨subd14_2_805, List.forall_mem_cons.2 ⟨subd14_2_806, List.forall_mem_cons.2 ⟨subd14_2_807, List.forall_mem_cons.2 ⟨subd14_2_808, List.forall_mem_cons.2 ⟨subd14_2_809, List.forall_mem_cons.2 ⟨subd14_2_810, List.forall_mem_cons.2 ⟨subd14_2_811, List.forall_mem_cons.2 ⟨subd14_2_812, List.forall_mem_cons.2 ⟨subd14_2_813, List.forall_mem_cons.2 ⟨subd14_2_814, List.forall_mem_cons.2 ⟨subd14_2_815, List.forall_mem_cons.2 ⟨subd14_2_816, List.forall_mem_cons.2 ⟨subd14_2_817, List.forall_mem_cons.2 ⟨subd14_2_818, List.forall_mem_cons.2 ⟨subd14_2_819, List.forall_mem_cons.2 ⟨subd14_2_820, List.forall_mem_cons.2 ⟨subd14_2_821, List.forall_mem_cons.2 ⟨subd14_2_822, List.forall_mem_cons.2 ⟨subd14_2_823, List.forall_mem_cons.2 ⟨subd14_2_824, List.forall_mem_cons.2 ⟨subd14_2_825, List.forall_mem_cons.2 ⟨subd14_2_826, List.forall_mem_cons.2 ⟨subd14_2_827, List.forall_mem_cons.2 ⟨subd14_2_828, List.forall_mem_cons.2 ⟨subd14_2_829, List.forall_mem_cons.2 ⟨subd14_2_830, List.forall_mem_cons.2 ⟨subd14_2_831, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_2_832 : subd14_2 [3, -3, 6] = true := by decide +kernel
theorem subd14_2_833 : subd14_2 [3, -3, 7] = true := by decide +kernel
theorem subd14_2_834 : subd14_2 [3, -2, -7] = true := by decide +kernel
theorem subd14_2_835 : subd14_2 [3, -2, -6] = true := by decide +kernel
theorem subd14_2_836 : subd14_2 [3, -2, -5] = true := by decide +kernel
theorem subd14_2_837 : subd14_2 [3, -2, -4] = true := by decide +kernel
theorem subd14_2_838 : subd14_2 [3, -2, -3] = true := by decide +kernel
theorem subd14_2_839 : subd14_2 [3, -2, -2] = true := by decide +kernel
theorem subd14_2_840 : subd14_2 [3, -2, -1] = true := by decide +kernel
theorem subd14_2_841 : subd14_2 [3, -2, 0] = true := by decide +kernel
theorem subd14_2_842 : subd14_2 [3, -2, 1] = true := by decide +kernel
theorem subd14_2_843 : subd14_2 [3, -2, 2] = true := by decide +kernel
theorem subd14_2_844 : subd14_2 [3, -2, 3] = true := by decide +kernel
theorem subd14_2_845 : subd14_2 [3, -2, 4] = true := by decide +kernel
theorem subd14_2_846 : subd14_2 [3, -2, 5] = true := by decide +kernel
theorem subd14_2_847 : subd14_2 [3, -2, 6] = true := by decide +kernel
theorem subd14_2_848 : subd14_2 [3, -2, 7] = true := by decide +kernel
theorem subd14_2_849 : subd14_2 [3, -2, 8] = true := by decide +kernel
theorem subd14_2_850 : subd14_2 [3, -1, -7] = true := by decide +kernel
theorem subd14_2_851 : subd14_2 [3, -1, -6] = true := by decide +kernel
theorem subd14_2_852 : subd14_2 [3, -1, -5] = true := by decide +kernel
theorem subd14_2_853 : subd14_2 [3, -1, -4] = true := by decide +kernel
theorem subd14_2_854 : subd14_2 [3, -1, -3] = true := by decide +kernel
theorem subd14_2_855 : subd14_2 [3, -1, -2] = true := by decide +kernel
theorem subd14_2_856 : subd14_2 [3, -1, -1] = true := by decide +kernel
theorem subd14_2_857 : subd14_2 [3, -1, 0] = true := by decide +kernel
theorem subd14_2_858 : subd14_2 [3, -1, 1] = true := by decide +kernel
theorem subd14_2_859 : subd14_2 [3, -1, 2] = true := by decide +kernel
theorem subd14_2_860 : subd14_2 [3, -1, 3] = true := by decide +kernel
theorem subd14_2_861 : subd14_2 [3, -1, 4] = true := by decide +kernel
theorem subd14_2_862 : subd14_2 [3, -1, 5] = true := by decide +kernel
theorem subd14_2_863 : subd14_2 [3, -1, 6] = true := by decide +kernel
theorem sbd14_2_26 : ∀ q ∈ blkd14_2_26, subd14_2 q = true := by
  unfold blkd14_2_26
  exact List.forall_mem_cons.2 ⟨subd14_2_832, List.forall_mem_cons.2 ⟨subd14_2_833, List.forall_mem_cons.2 ⟨subd14_2_834, List.forall_mem_cons.2 ⟨subd14_2_835, List.forall_mem_cons.2 ⟨subd14_2_836, List.forall_mem_cons.2 ⟨subd14_2_837, List.forall_mem_cons.2 ⟨subd14_2_838, List.forall_mem_cons.2 ⟨subd14_2_839, List.forall_mem_cons.2 ⟨subd14_2_840, List.forall_mem_cons.2 ⟨subd14_2_841, List.forall_mem_cons.2 ⟨subd14_2_842, List.forall_mem_cons.2 ⟨subd14_2_843, List.forall_mem_cons.2 ⟨subd14_2_844, List.forall_mem_cons.2 ⟨subd14_2_845, List.forall_mem_cons.2 ⟨subd14_2_846, List.forall_mem_cons.2 ⟨subd14_2_847, List.forall_mem_cons.2 ⟨subd14_2_848, List.forall_mem_cons.2 ⟨subd14_2_849, List.forall_mem_cons.2 ⟨subd14_2_850, List.forall_mem_cons.2 ⟨subd14_2_851, List.forall_mem_cons.2 ⟨subd14_2_852, List.forall_mem_cons.2 ⟨subd14_2_853, List.forall_mem_cons.2 ⟨subd14_2_854, List.forall_mem_cons.2 ⟨subd14_2_855, List.forall_mem_cons.2 ⟨subd14_2_856, List.forall_mem_cons.2 ⟨subd14_2_857, List.forall_mem_cons.2 ⟨subd14_2_858, List.forall_mem_cons.2 ⟨subd14_2_859, List.forall_mem_cons.2 ⟨subd14_2_860, List.forall_mem_cons.2 ⟨subd14_2_861, List.forall_mem_cons.2 ⟨subd14_2_862, List.forall_mem_cons.2 ⟨subd14_2_863, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_2_864 : subd14_2 [3, -1, 7] = true := by decide +kernel
theorem subd14_2_865 : subd14_2 [3, -1, 8] = true := by decide +kernel
theorem subd14_2_866 : subd14_2 [3, 0, -7] = true := by decide +kernel
theorem subd14_2_867 : subd14_2 [3, 0, -6] = true := by decide +kernel
theorem subd14_2_868 : subd14_2 [3, 0, -5] = true := by decide +kernel
theorem subd14_2_869 : subd14_2 [3, 0, -4] = true := by decide +kernel
theorem subd14_2_870 : subd14_2 [3, 0, -3] = true := by decide +kernel
theorem subd14_2_871 : subd14_2 [3, 0, -2] = true := by decide +kernel
theorem subd14_2_872 : subd14_2 [3, 0, -1] = true := by decide +kernel
theorem subd14_2_873 : subd14_2 [3, 0, 0] = true := by decide +kernel
theorem subd14_2_874 : subd14_2 [3, 0, 1] = true := by decide +kernel
theorem subd14_2_875 : subd14_2 [3, 0, 2] = true := by decide +kernel
theorem subd14_2_876 : subd14_2 [3, 0, 3] = true := by decide +kernel
theorem subd14_2_877 : subd14_2 [3, 0, 4] = true := by decide +kernel
theorem subd14_2_878 : subd14_2 [3, 0, 5] = true := by decide +kernel
theorem subd14_2_879 : subd14_2 [3, 0, 6] = true := by decide +kernel
theorem subd14_2_880 : subd14_2 [3, 0, 7] = true := by decide +kernel
theorem subd14_2_881 : subd14_2 [3, 0, 8] = true := by decide +kernel
theorem subd14_2_882 : subd14_2 [3, 1, -7] = true := by decide +kernel
theorem subd14_2_883 : subd14_2 [3, 1, -6] = true := by decide +kernel
theorem subd14_2_884 : subd14_2 [3, 1, -5] = true := by decide +kernel
theorem subd14_2_885 : subd14_2 [3, 1, -4] = true := by decide +kernel
theorem subd14_2_886 : subd14_2 [3, 1, -3] = true := by decide +kernel
theorem subd14_2_887 : subd14_2 [3, 1, -2] = true := by decide +kernel
theorem subd14_2_888 : subd14_2 [3, 1, -1] = true := by decide +kernel
theorem subd14_2_889 : subd14_2 [3, 1, 0] = true := by decide +kernel
theorem subd14_2_890 : subd14_2 [3, 1, 1] = true := by decide +kernel
theorem subd14_2_891 : subd14_2 [3, 1, 2] = true := by decide +kernel
theorem subd14_2_892 : subd14_2 [3, 1, 3] = true := by decide +kernel
theorem subd14_2_893 : subd14_2 [3, 1, 4] = true := by decide +kernel
theorem subd14_2_894 : subd14_2 [3, 1, 5] = true := by decide +kernel
theorem subd14_2_895 : subd14_2 [3, 1, 6] = true := by decide +kernel
theorem sbd14_2_27 : ∀ q ∈ blkd14_2_27, subd14_2 q = true := by
  unfold blkd14_2_27
  exact List.forall_mem_cons.2 ⟨subd14_2_864, List.forall_mem_cons.2 ⟨subd14_2_865, List.forall_mem_cons.2 ⟨subd14_2_866, List.forall_mem_cons.2 ⟨subd14_2_867, List.forall_mem_cons.2 ⟨subd14_2_868, List.forall_mem_cons.2 ⟨subd14_2_869, List.forall_mem_cons.2 ⟨subd14_2_870, List.forall_mem_cons.2 ⟨subd14_2_871, List.forall_mem_cons.2 ⟨subd14_2_872, List.forall_mem_cons.2 ⟨subd14_2_873, List.forall_mem_cons.2 ⟨subd14_2_874, List.forall_mem_cons.2 ⟨subd14_2_875, List.forall_mem_cons.2 ⟨subd14_2_876, List.forall_mem_cons.2 ⟨subd14_2_877, List.forall_mem_cons.2 ⟨subd14_2_878, List.forall_mem_cons.2 ⟨subd14_2_879, List.forall_mem_cons.2 ⟨subd14_2_880, List.forall_mem_cons.2 ⟨subd14_2_881, List.forall_mem_cons.2 ⟨subd14_2_882, List.forall_mem_cons.2 ⟨subd14_2_883, List.forall_mem_cons.2 ⟨subd14_2_884, List.forall_mem_cons.2 ⟨subd14_2_885, List.forall_mem_cons.2 ⟨subd14_2_886, List.forall_mem_cons.2 ⟨subd14_2_887, List.forall_mem_cons.2 ⟨subd14_2_888, List.forall_mem_cons.2 ⟨subd14_2_889, List.forall_mem_cons.2 ⟨subd14_2_890, List.forall_mem_cons.2 ⟨subd14_2_891, List.forall_mem_cons.2 ⟨subd14_2_892, List.forall_mem_cons.2 ⟨subd14_2_893, List.forall_mem_cons.2 ⟨subd14_2_894, List.forall_mem_cons.2 ⟨subd14_2_895, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_2_896 : subd14_2 [3, 1, 7] = true := by decide +kernel
theorem subd14_2_897 : subd14_2 [3, 2] = true := by decide +kernel
theorem subd14_2_898 : subd14_2 [3, 3] = true := by decide +kernel
theorem subd14_2_899 : subd14_2 [3, 4] = true := by decide +kernel
theorem subd14_2_900 : subd14_2 [4, -6] = true := by decide +kernel
theorem subd14_2_901 : subd14_2 [4, -5] = true := by decide +kernel
theorem subd14_2_902 : subd14_2 [4, -4] = true := by decide +kernel
theorem subd14_2_903 : subd14_2 [4, -3] = true := by decide +kernel
theorem subd14_2_904 : subd14_2 [4, -2] = true := by decide +kernel
theorem subd14_2_905 : subd14_2 [4, -1] = true := by decide +kernel
theorem subd14_2_906 : subd14_2 [4, 0] = true := by decide +kernel
theorem subd14_2_907 : subd14_2 [4, 1] = true := by decide +kernel
theorem subd14_2_908 : subd14_2 [4, 2] = true := by decide +kernel
theorem subd14_2_909 : subd14_2 [5, -5] = true := by decide +kernel
theorem subd14_2_910 : subd14_2 [5, -4] = true := by decide +kernel
theorem subd14_2_911 : subd14_2 [5, -3] = true := by decide +kernel
theorem subd14_2_912 : subd14_2 [5, -2] = true := by decide +kernel
theorem subd14_2_913 : subd14_2 [5, -1] = true := by decide +kernel
theorem subd14_2_914 : subd14_2 [5, 0] = true := by decide +kernel
theorem sbd14_2_28 : ∀ q ∈ blkd14_2_28, subd14_2 q = true := by
  unfold blkd14_2_28
  exact List.forall_mem_cons.2 ⟨subd14_2_896, List.forall_mem_cons.2 ⟨subd14_2_897, List.forall_mem_cons.2 ⟨subd14_2_898, List.forall_mem_cons.2 ⟨subd14_2_899, List.forall_mem_cons.2 ⟨subd14_2_900, List.forall_mem_cons.2 ⟨subd14_2_901, List.forall_mem_cons.2 ⟨subd14_2_902, List.forall_mem_cons.2 ⟨subd14_2_903, List.forall_mem_cons.2 ⟨subd14_2_904, List.forall_mem_cons.2 ⟨subd14_2_905, List.forall_mem_cons.2 ⟨subd14_2_906, List.forall_mem_cons.2 ⟨subd14_2_907, List.forall_mem_cons.2 ⟨subd14_2_908, List.forall_mem_cons.2 ⟨subd14_2_909, List.forall_mem_cons.2 ⟨subd14_2_910, List.forall_mem_cons.2 ⟨subd14_2_911, List.forall_mem_cons.2 ⟨subd14_2_912, List.forall_mem_cons.2 ⟨subd14_2_913, List.forall_mem_cons.2 ⟨subd14_2_914, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd14_3 : ldCheck G d14_3.U d14_3.ms ldd14_3 = true := by decide +kernel
theorem pre_okd14_3 : subPre G cell14 d14_3 = true := by decide +kernel
theorem subd14_3_0 : subd14_3 [-2] = true := by decide +kernel
theorem subd14_3_1 : subd14_3 [-1, -4] = true := by decide +kernel
theorem subd14_3_2 : subd14_3 [-1, -3] = true := by decide +kernel
theorem subd14_3_3 : subd14_3 [-1, -2] = true := by decide +kernel
theorem subd14_3_4 : subd14_3 [-1, -1] = true := by decide +kernel
theorem subd14_3_5 : subd14_3 [-1, 0] = true := by decide +kernel
theorem subd14_3_6 : subd14_3 [-1, 1] = true := by decide +kernel
theorem subd14_3_7 : subd14_3 [-1, 2] = true := by decide +kernel
theorem subd14_3_8 : subd14_3 [0, -3] = true := by decide +kernel
theorem subd14_3_9 : subd14_3 [0, -2] = true := by decide +kernel
theorem subd14_3_10 : subd14_3 [0, -1] = true := by decide +kernel
theorem subd14_3_11 : subd14_3 [0, 0] = true := by decide +kernel
theorem subd14_3_12 : subd14_3 [0, 1] = true := by decide +kernel
theorem subd14_3_13 : subd14_3 [0, 2] = true := by decide +kernel
theorem subd14_3_14 : subd14_3 [1, -3] = true := by decide +kernel
theorem subd14_3_15 : subd14_3 [1, -2] = true := by decide +kernel
theorem subd14_3_16 : subd14_3 [1, -1] = true := by decide +kernel
theorem subd14_3_17 : subd14_3 [1, 0] = true := by decide +kernel
theorem subd14_3_18 : subd14_3 [1, 1] = true := by decide +kernel
theorem subd14_3_19 : subd14_3 [1, 2] = true := by decide +kernel
theorem subd14_3_20 : subd14_3 [1, 3] = true := by decide +kernel
theorem subd14_3_21 : subd14_3 [2] = true := by decide +kernel
theorem sbd14_3_0 : ∀ q ∈ blkd14_3_0, subd14_3 q = true := by
  unfold blkd14_3_0
  exact List.forall_mem_cons.2 ⟨subd14_3_0, List.forall_mem_cons.2 ⟨subd14_3_1, List.forall_mem_cons.2 ⟨subd14_3_2, List.forall_mem_cons.2 ⟨subd14_3_3, List.forall_mem_cons.2 ⟨subd14_3_4, List.forall_mem_cons.2 ⟨subd14_3_5, List.forall_mem_cons.2 ⟨subd14_3_6, List.forall_mem_cons.2 ⟨subd14_3_7, List.forall_mem_cons.2 ⟨subd14_3_8, List.forall_mem_cons.2 ⟨subd14_3_9, List.forall_mem_cons.2 ⟨subd14_3_10, List.forall_mem_cons.2 ⟨subd14_3_11, List.forall_mem_cons.2 ⟨subd14_3_12, List.forall_mem_cons.2 ⟨subd14_3_13, List.forall_mem_cons.2 ⟨subd14_3_14, List.forall_mem_cons.2 ⟨subd14_3_15, List.forall_mem_cons.2 ⟨subd14_3_16, List.forall_mem_cons.2 ⟨subd14_3_17, List.forall_mem_cons.2 ⟨subd14_3_18, List.forall_mem_cons.2 ⟨subd14_3_19, List.forall_mem_cons.2 ⟨subd14_3_20, List.forall_mem_cons.2 ⟨subd14_3_21, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd15_0 : ldCheck G d15_0.U d15_0.ms ldd15_0 = true := by decide +kernel
theorem pre_okd15_0 : subPre G cell15 d15_0 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C142
