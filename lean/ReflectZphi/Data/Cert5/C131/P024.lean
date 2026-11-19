import ReflectZphi.Data.Cert5.C131.Base

namespace ReflectZphi.Data.Cert5.C131

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd12_0_672 : subd12_0 [0, -1, 2] = true := by decide +kernel
theorem subd12_0_673 : subd12_0 [0, -1, 3] = true := by decide +kernel
theorem subd12_0_674 : subd12_0 [0, -1, 4] = true := by decide +kernel
theorem subd12_0_675 : subd12_0 [0, -1, 5] = true := by decide +kernel
theorem subd12_0_676 : subd12_0 [0, -1, 6] = true := by decide +kernel
theorem subd12_0_677 : subd12_0 [0, -1, 7] = true := by decide +kernel
theorem subd12_0_678 : subd12_0 [0, 0, -9] = true := by decide +kernel
theorem subd12_0_679 : subd12_0 [0, 0, -8] = true := by decide +kernel
theorem subd12_0_680 : subd12_0 [0, 0, -7] = true := by decide +kernel
theorem subd12_0_681 : subd12_0 [0, 0, -6] = true := by decide +kernel
theorem subd12_0_682 : subd12_0 [0, 0, -5] = true := by decide +kernel
theorem subd12_0_683 : subd12_0 [0, 0, -4] = true := by decide +kernel
theorem subd12_0_684 : subd12_0 [0, 0, -3] = true := by decide +kernel
theorem subd12_0_685 : subd12_0 [0, 0, -2] = true := by decide +kernel
theorem subd12_0_686 : subd12_0 [0, 0, -1] = true := by decide +kernel
theorem subd12_0_687 : subd12_0 [0, 0, 0] = true := by decide +kernel
theorem subd12_0_688 : subd12_0 [0, 0, 1] = true := by decide +kernel
theorem subd12_0_689 : subd12_0 [0, 0, 2] = true := by decide +kernel
theorem subd12_0_690 : subd12_0 [0, 0, 3] = true := by decide +kernel
theorem subd12_0_691 : subd12_0 [0, 0, 4] = true := by decide +kernel
theorem subd12_0_692 : subd12_0 [0, 0, 5] = true := by decide +kernel
theorem subd12_0_693 : subd12_0 [0, 0, 6] = true := by decide +kernel
theorem subd12_0_694 : subd12_0 [0, 0, 7] = true := by decide +kernel
theorem subd12_0_695 : subd12_0 [0, 0, 8] = true := by decide +kernel
theorem subd12_0_696 : subd12_0 [0, 1, -8] = true := by decide +kernel
theorem subd12_0_697 : subd12_0 [0, 1, -7] = true := by decide +kernel
theorem subd12_0_698 : subd12_0 [0, 1, -6] = true := by decide +kernel
theorem subd12_0_699 : subd12_0 [0, 1, -5] = true := by decide +kernel
theorem subd12_0_700 : subd12_0 [0, 1, -4] = true := by decide +kernel
theorem subd12_0_701 : subd12_0 [0, 1, -3] = true := by decide +kernel
theorem subd12_0_702 : subd12_0 [0, 1, -2] = true := by decide +kernel
theorem subd12_0_703 : subd12_0 [0, 1, -1] = true := by decide +kernel
theorem sbd12_0_21 : ∀ q ∈ blkd12_0_21, subd12_0 q = true := by
  unfold blkd12_0_21
  exact List.forall_mem_cons.2 ⟨subd12_0_672, List.forall_mem_cons.2 ⟨subd12_0_673, List.forall_mem_cons.2 ⟨subd12_0_674, List.forall_mem_cons.2 ⟨subd12_0_675, List.forall_mem_cons.2 ⟨subd12_0_676, List.forall_mem_cons.2 ⟨subd12_0_677, List.forall_mem_cons.2 ⟨subd12_0_678, List.forall_mem_cons.2 ⟨subd12_0_679, List.forall_mem_cons.2 ⟨subd12_0_680, List.forall_mem_cons.2 ⟨subd12_0_681, List.forall_mem_cons.2 ⟨subd12_0_682, List.forall_mem_cons.2 ⟨subd12_0_683, List.forall_mem_cons.2 ⟨subd12_0_684, List.forall_mem_cons.2 ⟨subd12_0_685, List.forall_mem_cons.2 ⟨subd12_0_686, List.forall_mem_cons.2 ⟨subd12_0_687, List.forall_mem_cons.2 ⟨subd12_0_688, List.forall_mem_cons.2 ⟨subd12_0_689, List.forall_mem_cons.2 ⟨subd12_0_690, List.forall_mem_cons.2 ⟨subd12_0_691, List.forall_mem_cons.2 ⟨subd12_0_692, List.forall_mem_cons.2 ⟨subd12_0_693, List.forall_mem_cons.2 ⟨subd12_0_694, List.forall_mem_cons.2 ⟨subd12_0_695, List.forall_mem_cons.2 ⟨subd12_0_696, List.forall_mem_cons.2 ⟨subd12_0_697, List.forall_mem_cons.2 ⟨subd12_0_698, List.forall_mem_cons.2 ⟨subd12_0_699, List.forall_mem_cons.2 ⟨subd12_0_700, List.forall_mem_cons.2 ⟨subd12_0_701, List.forall_mem_cons.2 ⟨subd12_0_702, List.forall_mem_cons.2 ⟨subd12_0_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_704 : subd12_0 [0, 1, 0] = true := by decide +kernel
theorem subd12_0_705 : subd12_0 [0, 1, 1] = true := by decide +kernel
theorem subd12_0_706 : subd12_0 [0, 1, 2] = true := by decide +kernel
theorem subd12_0_707 : subd12_0 [0, 1, 3] = true := by decide +kernel
theorem subd12_0_708 : subd12_0 [0, 1, 4] = true := by decide +kernel
theorem subd12_0_709 : subd12_0 [0, 1, 5] = true := by decide +kernel
theorem subd12_0_710 : subd12_0 [0, 1, 6] = true := by decide +kernel
theorem subd12_0_711 : subd12_0 [0, 1, 7] = true := by decide +kernel
theorem subd12_0_712 : subd12_0 [0, 1, 8] = true := by decide +kernel
theorem subd12_0_713 : subd12_0 [0, 2, -7] = true := by decide +kernel
theorem subd12_0_714 : subd12_0 [0, 2, -6] = true := by decide +kernel
theorem subd12_0_715 : subd12_0 [0, 2, -5] = true := by decide +kernel
theorem subd12_0_716 : subd12_0 [0, 2, -4] = true := by decide +kernel
theorem subd12_0_717 : subd12_0 [0, 2, -3] = true := by decide +kernel
theorem subd12_0_718 : subd12_0 [0, 2, -2] = true := by decide +kernel
theorem subd12_0_719 : subd12_0 [0, 2, -1] = true := by decide +kernel
theorem subd12_0_720 : subd12_0 [0, 2, 0] = true := by decide +kernel
theorem subd12_0_721 : subd12_0 [0, 2, 1] = true := by decide +kernel
theorem subd12_0_722 : subd12_0 [0, 2, 2] = true := by decide +kernel
theorem subd12_0_723 : subd12_0 [0, 2, 3] = true := by decide +kernel
theorem subd12_0_724 : subd12_0 [0, 2, 4] = true := by decide +kernel
theorem subd12_0_725 : subd12_0 [0, 2, 5] = true := by decide +kernel
theorem subd12_0_726 : subd12_0 [0, 2, 6] = true := by decide +kernel
theorem subd12_0_727 : subd12_0 [0, 2, 7] = true := by decide +kernel
theorem subd12_0_728 : subd12_0 [0, 2, 8] = true := by decide +kernel
theorem subd12_0_729 : subd12_0 [0, 3, -7] = true := by decide +kernel
theorem subd12_0_730 : subd12_0 [0, 3, -6] = true := by decide +kernel
theorem subd12_0_731 : subd12_0 [0, 3, -5] = true := by decide +kernel
theorem subd12_0_732 : subd12_0 [0, 3, -4] = true := by decide +kernel
theorem subd12_0_733 : subd12_0 [0, 3, -3] = true := by decide +kernel
theorem subd12_0_734 : subd12_0 [0, 3, -2] = true := by decide +kernel
theorem subd12_0_735 : subd12_0 [0, 3, -1] = true := by decide +kernel
theorem sbd12_0_22 : ∀ q ∈ blkd12_0_22, subd12_0 q = true := by
  unfold blkd12_0_22
  exact List.forall_mem_cons.2 ⟨subd12_0_704, List.forall_mem_cons.2 ⟨subd12_0_705, List.forall_mem_cons.2 ⟨subd12_0_706, List.forall_mem_cons.2 ⟨subd12_0_707, List.forall_mem_cons.2 ⟨subd12_0_708, List.forall_mem_cons.2 ⟨subd12_0_709, List.forall_mem_cons.2 ⟨subd12_0_710, List.forall_mem_cons.2 ⟨subd12_0_711, List.forall_mem_cons.2 ⟨subd12_0_712, List.forall_mem_cons.2 ⟨subd12_0_713, List.forall_mem_cons.2 ⟨subd12_0_714, List.forall_mem_cons.2 ⟨subd12_0_715, List.forall_mem_cons.2 ⟨subd12_0_716, List.forall_mem_cons.2 ⟨subd12_0_717, List.forall_mem_cons.2 ⟨subd12_0_718, List.forall_mem_cons.2 ⟨subd12_0_719, List.forall_mem_cons.2 ⟨subd12_0_720, List.forall_mem_cons.2 ⟨subd12_0_721, List.forall_mem_cons.2 ⟨subd12_0_722, List.forall_mem_cons.2 ⟨subd12_0_723, List.forall_mem_cons.2 ⟨subd12_0_724, List.forall_mem_cons.2 ⟨subd12_0_725, List.forall_mem_cons.2 ⟨subd12_0_726, List.forall_mem_cons.2 ⟨subd12_0_727, List.forall_mem_cons.2 ⟨subd12_0_728, List.forall_mem_cons.2 ⟨subd12_0_729, List.forall_mem_cons.2 ⟨subd12_0_730, List.forall_mem_cons.2 ⟨subd12_0_731, List.forall_mem_cons.2 ⟨subd12_0_732, List.forall_mem_cons.2 ⟨subd12_0_733, List.forall_mem_cons.2 ⟨subd12_0_734, List.forall_mem_cons.2 ⟨subd12_0_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_736 : subd12_0 [0, 3, 0] = true := by decide +kernel
theorem subd12_0_737 : subd12_0 [0, 3, 1] = true := by decide +kernel
theorem subd12_0_738 : subd12_0 [0, 3, 2] = true := by decide +kernel
theorem subd12_0_739 : subd12_0 [0, 3, 3] = true := by decide +kernel
theorem subd12_0_740 : subd12_0 [0, 3, 4] = true := by decide +kernel
theorem subd12_0_741 : subd12_0 [0, 3, 5] = true := by decide +kernel
theorem subd12_0_742 : subd12_0 [0, 3, 6] = true := by decide +kernel
theorem subd12_0_743 : subd12_0 [0, 3, 7] = true := by decide +kernel
theorem subd12_0_744 : subd12_0 [0, 3, 8] = true := by decide +kernel
theorem subd12_0_745 : subd12_0 [0, 4, -6] = true := by decide +kernel
theorem subd12_0_746 : subd12_0 [0, 4, -5] = true := by decide +kernel
theorem subd12_0_747 : subd12_0 [0, 4, -4] = true := by decide +kernel
theorem subd12_0_748 : subd12_0 [0, 4, -3] = true := by decide +kernel
theorem subd12_0_749 : subd12_0 [0, 4, -2] = true := by decide +kernel
theorem subd12_0_750 : subd12_0 [0, 4, -1] = true := by decide +kernel
theorem subd12_0_751 : subd12_0 [0, 4, 0] = true := by decide +kernel
theorem subd12_0_752 : subd12_0 [0, 4, 1] = true := by decide +kernel
theorem subd12_0_753 : subd12_0 [0, 4, 2] = true := by decide +kernel
theorem subd12_0_754 : subd12_0 [0, 4, 3] = true := by decide +kernel
theorem subd12_0_755 : subd12_0 [0, 4, 4] = true := by decide +kernel
theorem subd12_0_756 : subd12_0 [0, 4, 5] = true := by decide +kernel
theorem subd12_0_757 : subd12_0 [0, 4, 6] = true := by decide +kernel
theorem subd12_0_758 : subd12_0 [0, 4, 7] = true := by decide +kernel
theorem subd12_0_759 : subd12_0 [0, 4, 8] = true := by decide +kernel
theorem subd12_0_760 : subd12_0 [0, 5, -5] = true := by decide +kernel
theorem subd12_0_761 : subd12_0 [0, 5, -4] = true := by decide +kernel
theorem subd12_0_762 : subd12_0 [0, 5, -3] = true := by decide +kernel
theorem subd12_0_763 : subd12_0 [0, 5, -2] = true := by decide +kernel
theorem subd12_0_764 : subd12_0 [0, 5, -1] = true := by decide +kernel
theorem subd12_0_765 : subd12_0 [0, 5, 0] = true := by decide +kernel
theorem subd12_0_766 : subd12_0 [0, 5, 1] = true := by decide +kernel
theorem subd12_0_767 : subd12_0 [0, 5, 2] = true := by decide +kernel
theorem sbd12_0_23 : ∀ q ∈ blkd12_0_23, subd12_0 q = true := by
  unfold blkd12_0_23
  exact List.forall_mem_cons.2 ⟨subd12_0_736, List.forall_mem_cons.2 ⟨subd12_0_737, List.forall_mem_cons.2 ⟨subd12_0_738, List.forall_mem_cons.2 ⟨subd12_0_739, List.forall_mem_cons.2 ⟨subd12_0_740, List.forall_mem_cons.2 ⟨subd12_0_741, List.forall_mem_cons.2 ⟨subd12_0_742, List.forall_mem_cons.2 ⟨subd12_0_743, List.forall_mem_cons.2 ⟨subd12_0_744, List.forall_mem_cons.2 ⟨subd12_0_745, List.forall_mem_cons.2 ⟨subd12_0_746, List.forall_mem_cons.2 ⟨subd12_0_747, List.forall_mem_cons.2 ⟨subd12_0_748, List.forall_mem_cons.2 ⟨subd12_0_749, List.forall_mem_cons.2 ⟨subd12_0_750, List.forall_mem_cons.2 ⟨subd12_0_751, List.forall_mem_cons.2 ⟨subd12_0_752, List.forall_mem_cons.2 ⟨subd12_0_753, List.forall_mem_cons.2 ⟨subd12_0_754, List.forall_mem_cons.2 ⟨subd12_0_755, List.forall_mem_cons.2 ⟨subd12_0_756, List.forall_mem_cons.2 ⟨subd12_0_757, List.forall_mem_cons.2 ⟨subd12_0_758, List.forall_mem_cons.2 ⟨subd12_0_759, List.forall_mem_cons.2 ⟨subd12_0_760, List.forall_mem_cons.2 ⟨subd12_0_761, List.forall_mem_cons.2 ⟨subd12_0_762, List.forall_mem_cons.2 ⟨subd12_0_763, List.forall_mem_cons.2 ⟨subd12_0_764, List.forall_mem_cons.2 ⟨subd12_0_765, List.forall_mem_cons.2 ⟨subd12_0_766, List.forall_mem_cons.2 ⟨subd12_0_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_768 : subd12_0 [0, 5, 3] = true := by decide +kernel
theorem subd12_0_769 : subd12_0 [0, 5, 4] = true := by decide +kernel
theorem subd12_0_770 : subd12_0 [0, 5, 5] = true := by decide +kernel
theorem subd12_0_771 : subd12_0 [0, 5, 6] = true := by decide +kernel
theorem subd12_0_772 : subd12_0 [0, 5, 7] = true := by decide +kernel
theorem subd12_0_773 : subd12_0 [0, 5, 8] = true := by decide +kernel
theorem subd12_0_774 : subd12_0 [0, 6] = true := by decide +kernel
theorem subd12_0_775 : subd12_0 [0, 7] = true := by decide +kernel
theorem subd12_0_776 : subd12_0 [0, 8] = true := by decide +kernel
theorem subd12_0_777 : subd12_0 [1, -9] = true := by decide +kernel
theorem subd12_0_778 : subd12_0 [1, -8] = true := by decide +kernel
theorem subd12_0_779 : subd12_0 [1, -7] = true := by decide +kernel
theorem subd12_0_780 : subd12_0 [1, -6] = true := by decide +kernel
theorem subd12_0_781 : subd12_0 [1, -5, -9] = true := by decide +kernel
theorem subd12_0_782 : subd12_0 [1, -5, -8] = true := by decide +kernel
theorem subd12_0_783 : subd12_0 [1, -5, -7] = true := by decide +kernel
theorem subd12_0_784 : subd12_0 [1, -5, -6] = true := by decide +kernel
theorem subd12_0_785 : subd12_0 [1, -5, -5] = true := by decide +kernel
theorem subd12_0_786 : subd12_0 [1, -5, -4] = true := by decide +kernel
theorem subd12_0_787 : subd12_0 [1, -5, -3] = true := by decide +kernel
theorem subd12_0_788 : subd12_0 [1, -5, -2] = true := by decide +kernel
theorem subd12_0_789 : subd12_0 [1, -5, -1] = true := by decide +kernel
theorem subd12_0_790 : subd12_0 [1, -5, 0] = true := by decide +kernel
theorem subd12_0_791 : subd12_0 [1, -5, 1] = true := by decide +kernel
theorem subd12_0_792 : subd12_0 [1, -5, 2] = true := by decide +kernel
theorem subd12_0_793 : subd12_0 [1, -5, 3] = true := by decide +kernel
theorem subd12_0_794 : subd12_0 [1, -5, 4] = true := by decide +kernel
theorem subd12_0_795 : subd12_0 [1, -4, -9] = true := by decide +kernel
theorem subd12_0_796 : subd12_0 [1, -4, -8] = true := by decide +kernel
theorem subd12_0_797 : subd12_0 [1, -4, -7] = true := by decide +kernel
theorem subd12_0_798 : subd12_0 [1, -4, -6] = true := by decide +kernel
theorem subd12_0_799 : subd12_0 [1, -4, -5] = true := by decide +kernel
theorem sbd12_0_24 : ∀ q ∈ blkd12_0_24, subd12_0 q = true := by
  unfold blkd12_0_24
  exact List.forall_mem_cons.2 ⟨subd12_0_768, List.forall_mem_cons.2 ⟨subd12_0_769, List.forall_mem_cons.2 ⟨subd12_0_770, List.forall_mem_cons.2 ⟨subd12_0_771, List.forall_mem_cons.2 ⟨subd12_0_772, List.forall_mem_cons.2 ⟨subd12_0_773, List.forall_mem_cons.2 ⟨subd12_0_774, List.forall_mem_cons.2 ⟨subd12_0_775, List.forall_mem_cons.2 ⟨subd12_0_776, List.forall_mem_cons.2 ⟨subd12_0_777, List.forall_mem_cons.2 ⟨subd12_0_778, List.forall_mem_cons.2 ⟨subd12_0_779, List.forall_mem_cons.2 ⟨subd12_0_780, List.forall_mem_cons.2 ⟨subd12_0_781, List.forall_mem_cons.2 ⟨subd12_0_782, List.forall_mem_cons.2 ⟨subd12_0_783, List.forall_mem_cons.2 ⟨subd12_0_784, List.forall_mem_cons.2 ⟨subd12_0_785, List.forall_mem_cons.2 ⟨subd12_0_786, List.forall_mem_cons.2 ⟨subd12_0_787, List.forall_mem_cons.2 ⟨subd12_0_788, List.forall_mem_cons.2 ⟨subd12_0_789, List.forall_mem_cons.2 ⟨subd12_0_790, List.forall_mem_cons.2 ⟨subd12_0_791, List.forall_mem_cons.2 ⟨subd12_0_792, List.forall_mem_cons.2 ⟨subd12_0_793, List.forall_mem_cons.2 ⟨subd12_0_794, List.forall_mem_cons.2 ⟨subd12_0_795, List.forall_mem_cons.2 ⟨subd12_0_796, List.forall_mem_cons.2 ⟨subd12_0_797, List.forall_mem_cons.2 ⟨subd12_0_798, List.forall_mem_cons.2 ⟨subd12_0_799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_800 : subd12_0 [1, -4, -4] = true := by decide +kernel
theorem subd12_0_801 : subd12_0 [1, -4, -3] = true := by decide +kernel
theorem subd12_0_802 : subd12_0 [1, -4, -2] = true := by decide +kernel
theorem subd12_0_803 : subd12_0 [1, -4, -1] = true := by decide +kernel
theorem subd12_0_804 : subd12_0 [1, -4, 0] = true := by decide +kernel
theorem subd12_0_805 : subd12_0 [1, -4, 1] = true := by decide +kernel
theorem subd12_0_806 : subd12_0 [1, -4, 2] = true := by decide +kernel
theorem subd12_0_807 : subd12_0 [1, -4, 3] = true := by decide +kernel
theorem subd12_0_808 : subd12_0 [1, -4, 4] = true := by decide +kernel
theorem subd12_0_809 : subd12_0 [1, -4, 5] = true := by decide +kernel
theorem subd12_0_810 : subd12_0 [1, -3, -9] = true := by decide +kernel
theorem subd12_0_811 : subd12_0 [1, -3, -8] = true := by decide +kernel
theorem subd12_0_812 : subd12_0 [1, -3, -7] = true := by decide +kernel
theorem subd12_0_813 : subd12_0 [1, -3, -6] = true := by decide +kernel
theorem subd12_0_814 : subd12_0 [1, -3, -5] = true := by decide +kernel
theorem subd12_0_815 : subd12_0 [1, -3, -4] = true := by decide +kernel
theorem subd12_0_816 : subd12_0 [1, -3, -3] = true := by decide +kernel
theorem subd12_0_817 : subd12_0 [1, -3, -2] = true := by decide +kernel
theorem subd12_0_818 : subd12_0 [1, -3, -1] = true := by decide +kernel
theorem subd12_0_819 : subd12_0 [1, -3, 0] = true := by decide +kernel
theorem subd12_0_820 : subd12_0 [1, -3, 1] = true := by decide +kernel
theorem subd12_0_821 : subd12_0 [1, -3, 2] = true := by decide +kernel
theorem subd12_0_822 : subd12_0 [1, -3, 3] = true := by decide +kernel
theorem subd12_0_823 : subd12_0 [1, -3, 4] = true := by decide +kernel
theorem subd12_0_824 : subd12_0 [1, -3, 5] = true := by decide +kernel
theorem subd12_0_825 : subd12_0 [1, -3, 6] = true := by decide +kernel
theorem subd12_0_826 : subd12_0 [1, -2, -9] = true := by decide +kernel
theorem subd12_0_827 : subd12_0 [1, -2, -8] = true := by decide +kernel
theorem subd12_0_828 : subd12_0 [1, -2, -7] = true := by decide +kernel
theorem subd12_0_829 : subd12_0 [1, -2, -6] = true := by decide +kernel
theorem subd12_0_830 : subd12_0 [1, -2, -5] = true := by decide +kernel
theorem subd12_0_831 : subd12_0 [1, -2, -4] = true := by decide +kernel
theorem sbd12_0_25 : ∀ q ∈ blkd12_0_25, subd12_0 q = true := by
  unfold blkd12_0_25
  exact List.forall_mem_cons.2 ⟨subd12_0_800, List.forall_mem_cons.2 ⟨subd12_0_801, List.forall_mem_cons.2 ⟨subd12_0_802, List.forall_mem_cons.2 ⟨subd12_0_803, List.forall_mem_cons.2 ⟨subd12_0_804, List.forall_mem_cons.2 ⟨subd12_0_805, List.forall_mem_cons.2 ⟨subd12_0_806, List.forall_mem_cons.2 ⟨subd12_0_807, List.forall_mem_cons.2 ⟨subd12_0_808, List.forall_mem_cons.2 ⟨subd12_0_809, List.forall_mem_cons.2 ⟨subd12_0_810, List.forall_mem_cons.2 ⟨subd12_0_811, List.forall_mem_cons.2 ⟨subd12_0_812, List.forall_mem_cons.2 ⟨subd12_0_813, List.forall_mem_cons.2 ⟨subd12_0_814, List.forall_mem_cons.2 ⟨subd12_0_815, List.forall_mem_cons.2 ⟨subd12_0_816, List.forall_mem_cons.2 ⟨subd12_0_817, List.forall_mem_cons.2 ⟨subd12_0_818, List.forall_mem_cons.2 ⟨subd12_0_819, List.forall_mem_cons.2 ⟨subd12_0_820, List.forall_mem_cons.2 ⟨subd12_0_821, List.forall_mem_cons.2 ⟨subd12_0_822, List.forall_mem_cons.2 ⟨subd12_0_823, List.forall_mem_cons.2 ⟨subd12_0_824, List.forall_mem_cons.2 ⟨subd12_0_825, List.forall_mem_cons.2 ⟨subd12_0_826, List.forall_mem_cons.2 ⟨subd12_0_827, List.forall_mem_cons.2 ⟨subd12_0_828, List.forall_mem_cons.2 ⟨subd12_0_829, List.forall_mem_cons.2 ⟨subd12_0_830, List.forall_mem_cons.2 ⟨subd12_0_831, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_832 : subd12_0 [1, -2, -3] = true := by decide +kernel
theorem subd12_0_833 : subd12_0 [1, -2, -2] = true := by decide +kernel
theorem subd12_0_834 : subd12_0 [1, -2, -1] = true := by decide +kernel
theorem subd12_0_835 : subd12_0 [1, -2, 0] = true := by decide +kernel
theorem subd12_0_836 : subd12_0 [1, -2, 1] = true := by decide +kernel
theorem subd12_0_837 : subd12_0 [1, -2, 2] = true := by decide +kernel
theorem subd12_0_838 : subd12_0 [1, -2, 3] = true := by decide +kernel
theorem subd12_0_839 : subd12_0 [1, -2, 4] = true := by decide +kernel
theorem subd12_0_840 : subd12_0 [1, -2, 5] = true := by decide +kernel
theorem subd12_0_841 : subd12_0 [1, -2, 6] = true := by decide +kernel
theorem subd12_0_842 : subd12_0 [1, -2, 7] = true := by decide +kernel
theorem subd12_0_843 : subd12_0 [1, -1, -9] = true := by decide +kernel
theorem subd12_0_844 : subd12_0 [1, -1, -8] = true := by decide +kernel
theorem subd12_0_845 : subd12_0 [1, -1, -7] = true := by decide +kernel
theorem subd12_0_846 : subd12_0 [1, -1, -6] = true := by decide +kernel
theorem subd12_0_847 : subd12_0 [1, -1, -5] = true := by decide +kernel
theorem subd12_0_848 : subd12_0 [1, -1, -4] = true := by decide +kernel
theorem subd12_0_849 : subd12_0 [1, -1, -3] = true := by decide +kernel
theorem subd12_0_850 : subd12_0 [1, -1, -2] = true := by decide +kernel
theorem subd12_0_851 : subd12_0 [1, -1, -1] = true := by decide +kernel
theorem subd12_0_852 : subd12_0 [1, -1, 0] = true := by decide +kernel
theorem subd12_0_853 : subd12_0 [1, -1, 1] = true := by decide +kernel
theorem subd12_0_854 : subd12_0 [1, -1, 2] = true := by decide +kernel
theorem subd12_0_855 : subd12_0 [1, -1, 3] = true := by decide +kernel
theorem subd12_0_856 : subd12_0 [1, -1, 4] = true := by decide +kernel
theorem subd12_0_857 : subd12_0 [1, -1, 5] = true := by decide +kernel
theorem subd12_0_858 : subd12_0 [1, -1, 6] = true := by decide +kernel
theorem subd12_0_859 : subd12_0 [1, -1, 7] = true := by decide +kernel
theorem subd12_0_860 : subd12_0 [1, 0, -8] = true := by decide +kernel
theorem subd12_0_861 : subd12_0 [1, 0, -7] = true := by decide +kernel
theorem subd12_0_862 : subd12_0 [1, 0, -6] = true := by decide +kernel
theorem subd12_0_863 : subd12_0 [1, 0, -5] = true := by decide +kernel
theorem sbd12_0_26 : ∀ q ∈ blkd12_0_26, subd12_0 q = true := by
  unfold blkd12_0_26
  exact List.forall_mem_cons.2 ⟨subd12_0_832, List.forall_mem_cons.2 ⟨subd12_0_833, List.forall_mem_cons.2 ⟨subd12_0_834, List.forall_mem_cons.2 ⟨subd12_0_835, List.forall_mem_cons.2 ⟨subd12_0_836, List.forall_mem_cons.2 ⟨subd12_0_837, List.forall_mem_cons.2 ⟨subd12_0_838, List.forall_mem_cons.2 ⟨subd12_0_839, List.forall_mem_cons.2 ⟨subd12_0_840, List.forall_mem_cons.2 ⟨subd12_0_841, List.forall_mem_cons.2 ⟨subd12_0_842, List.forall_mem_cons.2 ⟨subd12_0_843, List.forall_mem_cons.2 ⟨subd12_0_844, List.forall_mem_cons.2 ⟨subd12_0_845, List.forall_mem_cons.2 ⟨subd12_0_846, List.forall_mem_cons.2 ⟨subd12_0_847, List.forall_mem_cons.2 ⟨subd12_0_848, List.forall_mem_cons.2 ⟨subd12_0_849, List.forall_mem_cons.2 ⟨subd12_0_850, List.forall_mem_cons.2 ⟨subd12_0_851, List.forall_mem_cons.2 ⟨subd12_0_852, List.forall_mem_cons.2 ⟨subd12_0_853, List.forall_mem_cons.2 ⟨subd12_0_854, List.forall_mem_cons.2 ⟨subd12_0_855, List.forall_mem_cons.2 ⟨subd12_0_856, List.forall_mem_cons.2 ⟨subd12_0_857, List.forall_mem_cons.2 ⟨subd12_0_858, List.forall_mem_cons.2 ⟨subd12_0_859, List.forall_mem_cons.2 ⟨subd12_0_860, List.forall_mem_cons.2 ⟨subd12_0_861, List.forall_mem_cons.2 ⟨subd12_0_862, List.forall_mem_cons.2 ⟨subd12_0_863, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_864 : subd12_0 [1, 0, -4] = true := by decide +kernel
theorem subd12_0_865 : subd12_0 [1, 0, -3] = true := by decide +kernel
theorem subd12_0_866 : subd12_0 [1, 0, -2] = true := by decide +kernel
theorem subd12_0_867 : subd12_0 [1, 0, -1] = true := by decide +kernel
theorem subd12_0_868 : subd12_0 [1, 0, 0] = true := by decide +kernel
theorem subd12_0_869 : subd12_0 [1, 0, 1] = true := by decide +kernel
theorem subd12_0_870 : subd12_0 [1, 0, 2] = true := by decide +kernel
theorem subd12_0_871 : subd12_0 [1, 0, 3] = true := by decide +kernel
theorem subd12_0_872 : subd12_0 [1, 0, 4] = true := by decide +kernel
theorem subd12_0_873 : subd12_0 [1, 0, 5] = true := by decide +kernel
theorem subd12_0_874 : subd12_0 [1, 0, 6] = true := by decide +kernel
theorem subd12_0_875 : subd12_0 [1, 0, 7] = true := by decide +kernel
theorem subd12_0_876 : subd12_0 [1, 0, 8] = true := by decide +kernel
theorem subd12_0_877 : subd12_0 [1, 1, -8] = true := by decide +kernel
theorem subd12_0_878 : subd12_0 [1, 1, -7] = true := by decide +kernel
theorem subd12_0_879 : subd12_0 [1, 1, -6] = true := by decide +kernel
theorem subd12_0_880 : subd12_0 [1, 1, -5] = true := by decide +kernel
theorem subd12_0_881 : subd12_0 [1, 1, -4] = true := by decide +kernel
theorem subd12_0_882 : subd12_0 [1, 1, -3] = true := by decide +kernel
theorem subd12_0_883 : subd12_0 [1, 1, -2] = true := by decide +kernel
theorem subd12_0_884 : subd12_0 [1, 1, -1] = true := by decide +kernel
theorem subd12_0_885 : subd12_0 [1, 1, 0] = true := by decide +kernel
theorem subd12_0_886 : subd12_0 [1, 1, 1] = true := by decide +kernel
theorem subd12_0_887 : subd12_0 [1, 1, 2] = true := by decide +kernel
theorem subd12_0_888 : subd12_0 [1, 1, 3] = true := by decide +kernel
theorem subd12_0_889 : subd12_0 [1, 1, 4] = true := by decide +kernel
theorem subd12_0_890 : subd12_0 [1, 1, 5] = true := by decide +kernel
theorem subd12_0_891 : subd12_0 [1, 1, 6] = true := by decide +kernel
theorem subd12_0_892 : subd12_0 [1, 1, 7] = true := by decide +kernel
theorem subd12_0_893 : subd12_0 [1, 1, 8] = true := by decide +kernel
theorem subd12_0_894 : subd12_0 [1, 2, -7] = true := by decide +kernel
theorem subd12_0_895 : subd12_0 [1, 2, -6] = true := by decide +kernel
theorem sbd12_0_27 : ∀ q ∈ blkd12_0_27, subd12_0 q = true := by
  unfold blkd12_0_27
  exact List.forall_mem_cons.2 ⟨subd12_0_864, List.forall_mem_cons.2 ⟨subd12_0_865, List.forall_mem_cons.2 ⟨subd12_0_866, List.forall_mem_cons.2 ⟨subd12_0_867, List.forall_mem_cons.2 ⟨subd12_0_868, List.forall_mem_cons.2 ⟨subd12_0_869, List.forall_mem_cons.2 ⟨subd12_0_870, List.forall_mem_cons.2 ⟨subd12_0_871, List.forall_mem_cons.2 ⟨subd12_0_872, List.forall_mem_cons.2 ⟨subd12_0_873, List.forall_mem_cons.2 ⟨subd12_0_874, List.forall_mem_cons.2 ⟨subd12_0_875, List.forall_mem_cons.2 ⟨subd12_0_876, List.forall_mem_cons.2 ⟨subd12_0_877, List.forall_mem_cons.2 ⟨subd12_0_878, List.forall_mem_cons.2 ⟨subd12_0_879, List.forall_mem_cons.2 ⟨subd12_0_880, List.forall_mem_cons.2 ⟨subd12_0_881, List.forall_mem_cons.2 ⟨subd12_0_882, List.forall_mem_cons.2 ⟨subd12_0_883, List.forall_mem_cons.2 ⟨subd12_0_884, List.forall_mem_cons.2 ⟨subd12_0_885, List.forall_mem_cons.2 ⟨subd12_0_886, List.forall_mem_cons.2 ⟨subd12_0_887, List.forall_mem_cons.2 ⟨subd12_0_888, List.forall_mem_cons.2 ⟨subd12_0_889, List.forall_mem_cons.2 ⟨subd12_0_890, List.forall_mem_cons.2 ⟨subd12_0_891, List.forall_mem_cons.2 ⟨subd12_0_892, List.forall_mem_cons.2 ⟨subd12_0_893, List.forall_mem_cons.2 ⟨subd12_0_894, List.forall_mem_cons.2 ⟨subd12_0_895, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_896 : subd12_0 [1, 2, -5] = true := by decide +kernel
theorem subd12_0_897 : subd12_0 [1, 2, -4] = true := by decide +kernel
theorem subd12_0_898 : subd12_0 [1, 2, -3] = true := by decide +kernel
theorem subd12_0_899 : subd12_0 [1, 2, -2] = true := by decide +kernel
theorem subd12_0_900 : subd12_0 [1, 2, -1] = true := by decide +kernel
theorem subd12_0_901 : subd12_0 [1, 2, 0] = true := by decide +kernel
theorem subd12_0_902 : subd12_0 [1, 2, 1] = true := by decide +kernel
theorem subd12_0_903 : subd12_0 [1, 2, 2] = true := by decide +kernel
theorem subd12_0_904 : subd12_0 [1, 2, 3] = true := by decide +kernel
theorem subd12_0_905 : subd12_0 [1, 2, 4] = true := by decide +kernel
theorem subd12_0_906 : subd12_0 [1, 2, 5] = true := by decide +kernel
theorem subd12_0_907 : subd12_0 [1, 2, 6] = true := by decide +kernel
theorem subd12_0_908 : subd12_0 [1, 2, 7] = true := by decide +kernel
theorem subd12_0_909 : subd12_0 [1, 2, 8] = true := by decide +kernel
theorem subd12_0_910 : subd12_0 [1, 3, -7] = true := by decide +kernel
theorem subd12_0_911 : subd12_0 [1, 3, -6] = true := by decide +kernel
theorem subd12_0_912 : subd12_0 [1, 3, -5] = true := by decide +kernel
theorem subd12_0_913 : subd12_0 [1, 3, -4] = true := by decide +kernel
theorem subd12_0_914 : subd12_0 [1, 3, -3] = true := by decide +kernel
theorem subd12_0_915 : subd12_0 [1, 3, -2] = true := by decide +kernel
theorem subd12_0_916 : subd12_0 [1, 3, -1] = true := by decide +kernel
theorem subd12_0_917 : subd12_0 [1, 3, 0] = true := by decide +kernel
theorem subd12_0_918 : subd12_0 [1, 3, 1] = true := by decide +kernel
theorem subd12_0_919 : subd12_0 [1, 3, 2] = true := by decide +kernel
theorem subd12_0_920 : subd12_0 [1, 3, 3] = true := by decide +kernel
theorem subd12_0_921 : subd12_0 [1, 3, 4] = true := by decide +kernel
theorem subd12_0_922 : subd12_0 [1, 3, 5] = true := by decide +kernel
theorem subd12_0_923 : subd12_0 [1, 3, 6] = true := by decide +kernel
theorem subd12_0_924 : subd12_0 [1, 3, 7] = true := by decide +kernel
theorem subd12_0_925 : subd12_0 [1, 3, 8] = true := by decide +kernel
theorem subd12_0_926 : subd12_0 [1, 4, -6] = true := by decide +kernel
theorem subd12_0_927 : subd12_0 [1, 4, -5] = true := by decide +kernel
theorem sbd12_0_28 : ∀ q ∈ blkd12_0_28, subd12_0 q = true := by
  unfold blkd12_0_28
  exact List.forall_mem_cons.2 ⟨subd12_0_896, List.forall_mem_cons.2 ⟨subd12_0_897, List.forall_mem_cons.2 ⟨subd12_0_898, List.forall_mem_cons.2 ⟨subd12_0_899, List.forall_mem_cons.2 ⟨subd12_0_900, List.forall_mem_cons.2 ⟨subd12_0_901, List.forall_mem_cons.2 ⟨subd12_0_902, List.forall_mem_cons.2 ⟨subd12_0_903, List.forall_mem_cons.2 ⟨subd12_0_904, List.forall_mem_cons.2 ⟨subd12_0_905, List.forall_mem_cons.2 ⟨subd12_0_906, List.forall_mem_cons.2 ⟨subd12_0_907, List.forall_mem_cons.2 ⟨subd12_0_908, List.forall_mem_cons.2 ⟨subd12_0_909, List.forall_mem_cons.2 ⟨subd12_0_910, List.forall_mem_cons.2 ⟨subd12_0_911, List.forall_mem_cons.2 ⟨subd12_0_912, List.forall_mem_cons.2 ⟨subd12_0_913, List.forall_mem_cons.2 ⟨subd12_0_914, List.forall_mem_cons.2 ⟨subd12_0_915, List.forall_mem_cons.2 ⟨subd12_0_916, List.forall_mem_cons.2 ⟨subd12_0_917, List.forall_mem_cons.2 ⟨subd12_0_918, List.forall_mem_cons.2 ⟨subd12_0_919, List.forall_mem_cons.2 ⟨subd12_0_920, List.forall_mem_cons.2 ⟨subd12_0_921, List.forall_mem_cons.2 ⟨subd12_0_922, List.forall_mem_cons.2 ⟨subd12_0_923, List.forall_mem_cons.2 ⟨subd12_0_924, List.forall_mem_cons.2 ⟨subd12_0_925, List.forall_mem_cons.2 ⟨subd12_0_926, List.forall_mem_cons.2 ⟨subd12_0_927, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_928 : subd12_0 [1, 4, -4] = true := by decide +kernel
theorem subd12_0_929 : subd12_0 [1, 4, -3] = true := by decide +kernel
theorem subd12_0_930 : subd12_0 [1, 4, -2] = true := by decide +kernel
theorem subd12_0_931 : subd12_0 [1, 4, -1] = true := by decide +kernel
theorem subd12_0_932 : subd12_0 [1, 4, 0] = true := by decide +kernel
theorem subd12_0_933 : subd12_0 [1, 4, 1] = true := by decide +kernel
theorem subd12_0_934 : subd12_0 [1, 4, 2] = true := by decide +kernel
theorem subd12_0_935 : subd12_0 [1, 4, 3] = true := by decide +kernel
theorem subd12_0_936 : subd12_0 [1, 4, 4] = true := by decide +kernel
theorem subd12_0_937 : subd12_0 [1, 4, 5] = true := by decide +kernel
theorem subd12_0_938 : subd12_0 [1, 4, 6] = true := by decide +kernel
theorem subd12_0_939 : subd12_0 [1, 4, 7] = true := by decide +kernel
theorem subd12_0_940 : subd12_0 [1, 4, 8] = true := by decide +kernel
theorem subd12_0_941 : subd12_0 [1, 5] = true := by decide +kernel
theorem subd12_0_942 : subd12_0 [1, 6] = true := by decide +kernel
theorem subd12_0_943 : subd12_0 [1, 7] = true := by decide +kernel
theorem subd12_0_944 : subd12_0 [1, 8] = true := by decide +kernel
theorem subd12_0_945 : subd12_0 [2, -9] = true := by decide +kernel
theorem subd12_0_946 : subd12_0 [2, -8] = true := by decide +kernel
theorem subd12_0_947 : subd12_0 [2, -7] = true := by decide +kernel
theorem subd12_0_948 : subd12_0 [2, -6] = true := by decide +kernel
theorem subd12_0_949 : subd12_0 [2, -5, -9] = true := by decide +kernel
theorem subd12_0_950 : subd12_0 [2, -5, -8] = true := by decide +kernel
theorem subd12_0_951 : subd12_0 [2, -5, -7] = true := by decide +kernel
theorem subd12_0_952 : subd12_0 [2, -5, -6] = true := by decide +kernel
theorem subd12_0_953 : subd12_0 [2, -5, -5] = true := by decide +kernel
theorem subd12_0_954 : subd12_0 [2, -5, -4] = true := by decide +kernel
theorem subd12_0_955 : subd12_0 [2, -5, -3] = true := by decide +kernel
theorem subd12_0_956 : subd12_0 [2, -5, -2] = true := by decide +kernel
theorem subd12_0_957 : subd12_0 [2, -5, -1] = true := by decide +kernel
theorem subd12_0_958 : subd12_0 [2, -5, 0] = true := by decide +kernel
theorem subd12_0_959 : subd12_0 [2, -5, 1] = true := by decide +kernel
theorem sbd12_0_29 : ∀ q ∈ blkd12_0_29, subd12_0 q = true := by
  unfold blkd12_0_29
  exact List.forall_mem_cons.2 ⟨subd12_0_928, List.forall_mem_cons.2 ⟨subd12_0_929, List.forall_mem_cons.2 ⟨subd12_0_930, List.forall_mem_cons.2 ⟨subd12_0_931, List.forall_mem_cons.2 ⟨subd12_0_932, List.forall_mem_cons.2 ⟨subd12_0_933, List.forall_mem_cons.2 ⟨subd12_0_934, List.forall_mem_cons.2 ⟨subd12_0_935, List.forall_mem_cons.2 ⟨subd12_0_936, List.forall_mem_cons.2 ⟨subd12_0_937, List.forall_mem_cons.2 ⟨subd12_0_938, List.forall_mem_cons.2 ⟨subd12_0_939, List.forall_mem_cons.2 ⟨subd12_0_940, List.forall_mem_cons.2 ⟨subd12_0_941, List.forall_mem_cons.2 ⟨subd12_0_942, List.forall_mem_cons.2 ⟨subd12_0_943, List.forall_mem_cons.2 ⟨subd12_0_944, List.forall_mem_cons.2 ⟨subd12_0_945, List.forall_mem_cons.2 ⟨subd12_0_946, List.forall_mem_cons.2 ⟨subd12_0_947, List.forall_mem_cons.2 ⟨subd12_0_948, List.forall_mem_cons.2 ⟨subd12_0_949, List.forall_mem_cons.2 ⟨subd12_0_950, List.forall_mem_cons.2 ⟨subd12_0_951, List.forall_mem_cons.2 ⟨subd12_0_952, List.forall_mem_cons.2 ⟨subd12_0_953, List.forall_mem_cons.2 ⟨subd12_0_954, List.forall_mem_cons.2 ⟨subd12_0_955, List.forall_mem_cons.2 ⟨subd12_0_956, List.forall_mem_cons.2 ⟨subd12_0_957, List.forall_mem_cons.2 ⟨subd12_0_958, List.forall_mem_cons.2 ⟨subd12_0_959, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_960 : subd12_0 [2, -5, 2] = true := by decide +kernel
theorem subd12_0_961 : subd12_0 [2, -5, 3] = true := by decide +kernel
theorem subd12_0_962 : subd12_0 [2, -5, 4] = true := by decide +kernel
theorem subd12_0_963 : subd12_0 [2, -4, -9] = true := by decide +kernel
theorem subd12_0_964 : subd12_0 [2, -4, -8] = true := by decide +kernel
theorem subd12_0_965 : subd12_0 [2, -4, -7] = true := by decide +kernel
theorem subd12_0_966 : subd12_0 [2, -4, -6] = true := by decide +kernel
theorem subd12_0_967 : subd12_0 [2, -4, -5] = true := by decide +kernel
theorem subd12_0_968 : subd12_0 [2, -4, -4] = true := by decide +kernel
theorem subd12_0_969 : subd12_0 [2, -4, -3] = true := by decide +kernel
theorem subd12_0_970 : subd12_0 [2, -4, -2] = true := by decide +kernel
theorem subd12_0_971 : subd12_0 [2, -4, -1] = true := by decide +kernel
theorem subd12_0_972 : subd12_0 [2, -4, 0] = true := by decide +kernel
theorem subd12_0_973 : subd12_0 [2, -4, 1] = true := by decide +kernel
theorem subd12_0_974 : subd12_0 [2, -4, 2] = true := by decide +kernel
theorem subd12_0_975 : subd12_0 [2, -4, 3] = true := by decide +kernel
theorem subd12_0_976 : subd12_0 [2, -4, 4] = true := by decide +kernel
theorem subd12_0_977 : subd12_0 [2, -4, 5] = true := by decide +kernel
theorem subd12_0_978 : subd12_0 [2, -3, -9] = true := by decide +kernel
theorem subd12_0_979 : subd12_0 [2, -3, -8] = true := by decide +kernel
theorem subd12_0_980 : subd12_0 [2, -3, -7] = true := by decide +kernel
theorem subd12_0_981 : subd12_0 [2, -3, -6] = true := by decide +kernel
theorem subd12_0_982 : subd12_0 [2, -3, -5] = true := by decide +kernel
theorem subd12_0_983 : subd12_0 [2, -3, -4] = true := by decide +kernel
theorem subd12_0_984 : subd12_0 [2, -3, -3] = true := by decide +kernel
theorem subd12_0_985 : subd12_0 [2, -3, -2] = true := by decide +kernel
theorem subd12_0_986 : subd12_0 [2, -3, -1] = true := by decide +kernel
theorem subd12_0_987 : subd12_0 [2, -3, 0] = true := by decide +kernel
theorem subd12_0_988 : subd12_0 [2, -3, 1] = true := by decide +kernel
theorem subd12_0_989 : subd12_0 [2, -3, 2] = true := by decide +kernel
theorem subd12_0_990 : subd12_0 [2, -3, 3] = true := by decide +kernel
theorem subd12_0_991 : subd12_0 [2, -3, 4] = true := by decide +kernel
theorem sbd12_0_30 : ∀ q ∈ blkd12_0_30, subd12_0 q = true := by
  unfold blkd12_0_30
  exact List.forall_mem_cons.2 ⟨subd12_0_960, List.forall_mem_cons.2 ⟨subd12_0_961, List.forall_mem_cons.2 ⟨subd12_0_962, List.forall_mem_cons.2 ⟨subd12_0_963, List.forall_mem_cons.2 ⟨subd12_0_964, List.forall_mem_cons.2 ⟨subd12_0_965, List.forall_mem_cons.2 ⟨subd12_0_966, List.forall_mem_cons.2 ⟨subd12_0_967, List.forall_mem_cons.2 ⟨subd12_0_968, List.forall_mem_cons.2 ⟨subd12_0_969, List.forall_mem_cons.2 ⟨subd12_0_970, List.forall_mem_cons.2 ⟨subd12_0_971, List.forall_mem_cons.2 ⟨subd12_0_972, List.forall_mem_cons.2 ⟨subd12_0_973, List.forall_mem_cons.2 ⟨subd12_0_974, List.forall_mem_cons.2 ⟨subd12_0_975, List.forall_mem_cons.2 ⟨subd12_0_976, List.forall_mem_cons.2 ⟨subd12_0_977, List.forall_mem_cons.2 ⟨subd12_0_978, List.forall_mem_cons.2 ⟨subd12_0_979, List.forall_mem_cons.2 ⟨subd12_0_980, List.forall_mem_cons.2 ⟨subd12_0_981, List.forall_mem_cons.2 ⟨subd12_0_982, List.forall_mem_cons.2 ⟨subd12_0_983, List.forall_mem_cons.2 ⟨subd12_0_984, List.forall_mem_cons.2 ⟨subd12_0_985, List.forall_mem_cons.2 ⟨subd12_0_986, List.forall_mem_cons.2 ⟨subd12_0_987, List.forall_mem_cons.2 ⟨subd12_0_988, List.forall_mem_cons.2 ⟨subd12_0_989, List.forall_mem_cons.2 ⟨subd12_0_990, List.forall_mem_cons.2 ⟨subd12_0_991, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_992 : subd12_0 [2, -3, 5] = true := by decide +kernel
theorem subd12_0_993 : subd12_0 [2, -3, 6] = true := by decide +kernel
theorem subd12_0_994 : subd12_0 [2, -2, -9] = true := by decide +kernel
theorem subd12_0_995 : subd12_0 [2, -2, -8] = true := by decide +kernel
theorem subd12_0_996 : subd12_0 [2, -2, -7] = true := by decide +kernel
theorem subd12_0_997 : subd12_0 [2, -2, -6] = true := by decide +kernel
theorem subd12_0_998 : subd12_0 [2, -2, -5] = true := by decide +kernel
theorem subd12_0_999 : subd12_0 [2, -2, -4] = true := by decide +kernel
theorem subd12_0_1000 : subd12_0 [2, -2, -3] = true := by decide +kernel
theorem subd12_0_1001 : subd12_0 [2, -2, -2] = true := by decide +kernel
theorem subd12_0_1002 : subd12_0 [2, -2, -1] = true := by decide +kernel
theorem subd12_0_1003 : subd12_0 [2, -2, 0] = true := by decide +kernel
theorem subd12_0_1004 : subd12_0 [2, -2, 1] = true := by decide +kernel
theorem subd12_0_1005 : subd12_0 [2, -2, 2] = true := by decide +kernel
theorem subd12_0_1006 : subd12_0 [2, -2, 3] = true := by decide +kernel
theorem subd12_0_1007 : subd12_0 [2, -2, 4] = true := by decide +kernel
theorem subd12_0_1008 : subd12_0 [2, -2, 5] = true := by decide +kernel
theorem subd12_0_1009 : subd12_0 [2, -2, 6] = true := by decide +kernel
theorem subd12_0_1010 : subd12_0 [2, -1, -9] = true := by decide +kernel
theorem subd12_0_1011 : subd12_0 [2, -1, -8] = true := by decide +kernel
theorem subd12_0_1012 : subd12_0 [2, -1, -7] = true := by decide +kernel
theorem subd12_0_1013 : subd12_0 [2, -1, -6] = true := by decide +kernel
theorem subd12_0_1014 : subd12_0 [2, -1, -5] = true := by decide +kernel
theorem subd12_0_1015 : subd12_0 [2, -1, -4] = true := by decide +kernel
theorem subd12_0_1016 : subd12_0 [2, -1, -3] = true := by decide +kernel
theorem subd12_0_1017 : subd12_0 [2, -1, -2] = true := by decide +kernel
theorem subd12_0_1018 : subd12_0 [2, -1, -1] = true := by decide +kernel
theorem subd12_0_1019 : subd12_0 [2, -1, 0] = true := by decide +kernel
theorem subd12_0_1020 : subd12_0 [2, -1, 1] = true := by decide +kernel
theorem subd12_0_1021 : subd12_0 [2, -1, 2] = true := by decide +kernel
theorem subd12_0_1022 : subd12_0 [2, -1, 3] = true := by decide +kernel
theorem subd12_0_1023 : subd12_0 [2, -1, 4] = true := by decide +kernel
theorem sbd12_0_31 : ∀ q ∈ blkd12_0_31, subd12_0 q = true := by
  unfold blkd12_0_31
  exact List.forall_mem_cons.2 ⟨subd12_0_992, List.forall_mem_cons.2 ⟨subd12_0_993, List.forall_mem_cons.2 ⟨subd12_0_994, List.forall_mem_cons.2 ⟨subd12_0_995, List.forall_mem_cons.2 ⟨subd12_0_996, List.forall_mem_cons.2 ⟨subd12_0_997, List.forall_mem_cons.2 ⟨subd12_0_998, List.forall_mem_cons.2 ⟨subd12_0_999, List.forall_mem_cons.2 ⟨subd12_0_1000, List.forall_mem_cons.2 ⟨subd12_0_1001, List.forall_mem_cons.2 ⟨subd12_0_1002, List.forall_mem_cons.2 ⟨subd12_0_1003, List.forall_mem_cons.2 ⟨subd12_0_1004, List.forall_mem_cons.2 ⟨subd12_0_1005, List.forall_mem_cons.2 ⟨subd12_0_1006, List.forall_mem_cons.2 ⟨subd12_0_1007, List.forall_mem_cons.2 ⟨subd12_0_1008, List.forall_mem_cons.2 ⟨subd12_0_1009, List.forall_mem_cons.2 ⟨subd12_0_1010, List.forall_mem_cons.2 ⟨subd12_0_1011, List.forall_mem_cons.2 ⟨subd12_0_1012, List.forall_mem_cons.2 ⟨subd12_0_1013, List.forall_mem_cons.2 ⟨subd12_0_1014, List.forall_mem_cons.2 ⟨subd12_0_1015, List.forall_mem_cons.2 ⟨subd12_0_1016, List.forall_mem_cons.2 ⟨subd12_0_1017, List.forall_mem_cons.2 ⟨subd12_0_1018, List.forall_mem_cons.2 ⟨subd12_0_1019, List.forall_mem_cons.2 ⟨subd12_0_1020, List.forall_mem_cons.2 ⟨subd12_0_1021, List.forall_mem_cons.2 ⟨subd12_0_1022, List.forall_mem_cons.2 ⟨subd12_0_1023, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_1024 : subd12_0 [2, -1, 5] = true := by decide +kernel
theorem subd12_0_1025 : subd12_0 [2, -1, 6] = true := by decide +kernel
theorem subd12_0_1026 : subd12_0 [2, -1, 7] = true := by decide +kernel
theorem subd12_0_1027 : subd12_0 [2, 0, -8] = true := by decide +kernel
theorem subd12_0_1028 : subd12_0 [2, 0, -7] = true := by decide +kernel
theorem subd12_0_1029 : subd12_0 [2, 0, -6] = true := by decide +kernel
theorem subd12_0_1030 : subd12_0 [2, 0, -5] = true := by decide +kernel
theorem subd12_0_1031 : subd12_0 [2, 0, -4] = true := by decide +kernel
theorem subd12_0_1032 : subd12_0 [2, 0, -3] = true := by decide +kernel
theorem subd12_0_1033 : subd12_0 [2, 0, -2] = true := by decide +kernel
theorem subd12_0_1034 : subd12_0 [2, 0, -1] = true := by decide +kernel
theorem subd12_0_1035 : subd12_0 [2, 0, 0] = true := by decide +kernel
theorem subd12_0_1036 : subd12_0 [2, 0, 1] = true := by decide +kernel
theorem subd12_0_1037 : subd12_0 [2, 0, 2] = true := by decide +kernel
theorem subd12_0_1038 : subd12_0 [2, 0, 3] = true := by decide +kernel
theorem subd12_0_1039 : subd12_0 [2, 0, 4] = true := by decide +kernel
theorem subd12_0_1040 : subd12_0 [2, 0, 5] = true := by decide +kernel
theorem subd12_0_1041 : subd12_0 [2, 0, 6] = true := by decide +kernel
theorem subd12_0_1042 : subd12_0 [2, 0, 7] = true := by decide +kernel
theorem subd12_0_1043 : subd12_0 [2, 1, -8] = true := by decide +kernel
theorem subd12_0_1044 : subd12_0 [2, 1, -7] = true := by decide +kernel
theorem subd12_0_1045 : subd12_0 [2, 1, -6] = true := by decide +kernel
theorem subd12_0_1046 : subd12_0 [2, 1, -5] = true := by decide +kernel
theorem subd12_0_1047 : subd12_0 [2, 1, -4] = true := by decide +kernel
theorem subd12_0_1048 : subd12_0 [2, 1, -3] = true := by decide +kernel
theorem subd12_0_1049 : subd12_0 [2, 1, -2] = true := by decide +kernel
theorem subd12_0_1050 : subd12_0 [2, 1, -1] = true := by decide +kernel
theorem subd12_0_1051 : subd12_0 [2, 1, 0] = true := by decide +kernel
theorem subd12_0_1052 : subd12_0 [2, 1, 1] = true := by decide +kernel
theorem subd12_0_1053 : subd12_0 [2, 1, 2] = true := by decide +kernel
theorem subd12_0_1054 : subd12_0 [2, 1, 3] = true := by decide +kernel
theorem subd12_0_1055 : subd12_0 [2, 1, 4] = true := by decide +kernel
theorem sbd12_0_32 : ∀ q ∈ blkd12_0_32, subd12_0 q = true := by
  unfold blkd12_0_32
  exact List.forall_mem_cons.2 ⟨subd12_0_1024, List.forall_mem_cons.2 ⟨subd12_0_1025, List.forall_mem_cons.2 ⟨subd12_0_1026, List.forall_mem_cons.2 ⟨subd12_0_1027, List.forall_mem_cons.2 ⟨subd12_0_1028, List.forall_mem_cons.2 ⟨subd12_0_1029, List.forall_mem_cons.2 ⟨subd12_0_1030, List.forall_mem_cons.2 ⟨subd12_0_1031, List.forall_mem_cons.2 ⟨subd12_0_1032, List.forall_mem_cons.2 ⟨subd12_0_1033, List.forall_mem_cons.2 ⟨subd12_0_1034, List.forall_mem_cons.2 ⟨subd12_0_1035, List.forall_mem_cons.2 ⟨subd12_0_1036, List.forall_mem_cons.2 ⟨subd12_0_1037, List.forall_mem_cons.2 ⟨subd12_0_1038, List.forall_mem_cons.2 ⟨subd12_0_1039, List.forall_mem_cons.2 ⟨subd12_0_1040, List.forall_mem_cons.2 ⟨subd12_0_1041, List.forall_mem_cons.2 ⟨subd12_0_1042, List.forall_mem_cons.2 ⟨subd12_0_1043, List.forall_mem_cons.2 ⟨subd12_0_1044, List.forall_mem_cons.2 ⟨subd12_0_1045, List.forall_mem_cons.2 ⟨subd12_0_1046, List.forall_mem_cons.2 ⟨subd12_0_1047, List.forall_mem_cons.2 ⟨subd12_0_1048, List.forall_mem_cons.2 ⟨subd12_0_1049, List.forall_mem_cons.2 ⟨subd12_0_1050, List.forall_mem_cons.2 ⟨subd12_0_1051, List.forall_mem_cons.2 ⟨subd12_0_1052, List.forall_mem_cons.2 ⟨subd12_0_1053, List.forall_mem_cons.2 ⟨subd12_0_1054, List.forall_mem_cons.2 ⟨subd12_0_1055, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_1056 : subd12_0 [2, 1, 5] = true := by decide +kernel
theorem subd12_0_1057 : subd12_0 [2, 1, 6] = true := by decide +kernel
theorem subd12_0_1058 : subd12_0 [2, 1, 7] = true := by decide +kernel
theorem subd12_0_1059 : subd12_0 [2, 1, 8] = true := by decide +kernel
theorem subd12_0_1060 : subd12_0 [2, 2, -7] = true := by decide +kernel
theorem subd12_0_1061 : subd12_0 [2, 2, -6] = true := by decide +kernel
theorem subd12_0_1062 : subd12_0 [2, 2, -5] = true := by decide +kernel
theorem subd12_0_1063 : subd12_0 [2, 2, -4] = true := by decide +kernel
theorem subd12_0_1064 : subd12_0 [2, 2, -3] = true := by decide +kernel
theorem subd12_0_1065 : subd12_0 [2, 2, -2] = true := by decide +kernel
theorem subd12_0_1066 : subd12_0 [2, 2, -1] = true := by decide +kernel
theorem subd12_0_1067 : subd12_0 [2, 2, 0] = true := by decide +kernel
theorem subd12_0_1068 : subd12_0 [2, 2, 1] = true := by decide +kernel
theorem subd12_0_1069 : subd12_0 [2, 2, 2] = true := by decide +kernel
theorem subd12_0_1070 : subd12_0 [2, 2, 3] = true := by decide +kernel
theorem subd12_0_1071 : subd12_0 [2, 2, 4] = true := by decide +kernel
theorem subd12_0_1072 : subd12_0 [2, 2, 5] = true := by decide +kernel
theorem subd12_0_1073 : subd12_0 [2, 2, 6] = true := by decide +kernel
theorem subd12_0_1074 : subd12_0 [2, 2, 7] = true := by decide +kernel
theorem subd12_0_1075 : subd12_0 [2, 2, 8] = true := by decide +kernel
theorem subd12_0_1076 : subd12_0 [2, 3, -6] = true := by decide +kernel
theorem subd12_0_1077 : subd12_0 [2, 3, -5] = true := by decide +kernel
theorem subd12_0_1078 : subd12_0 [2, 3, -4] = true := by decide +kernel
theorem subd12_0_1079 : subd12_0 [2, 3, -3] = true := by decide +kernel
theorem subd12_0_1080 : subd12_0 [2, 3, -2] = true := by decide +kernel
theorem subd12_0_1081 : subd12_0 [2, 3, -1] = true := by decide +kernel
theorem subd12_0_1082 : subd12_0 [2, 3, 0] = true := by decide +kernel
theorem subd12_0_1083 : subd12_0 [2, 3, 1] = true := by decide +kernel
theorem subd12_0_1084 : subd12_0 [2, 3, 2] = true := by decide +kernel
theorem subd12_0_1085 : subd12_0 [2, 3, 3] = true := by decide +kernel
theorem subd12_0_1086 : subd12_0 [2, 3, 4] = true := by decide +kernel
theorem subd12_0_1087 : subd12_0 [2, 3, 5] = true := by decide +kernel
theorem sbd12_0_33 : ∀ q ∈ blkd12_0_33, subd12_0 q = true := by
  unfold blkd12_0_33
  exact List.forall_mem_cons.2 ⟨subd12_0_1056, List.forall_mem_cons.2 ⟨subd12_0_1057, List.forall_mem_cons.2 ⟨subd12_0_1058, List.forall_mem_cons.2 ⟨subd12_0_1059, List.forall_mem_cons.2 ⟨subd12_0_1060, List.forall_mem_cons.2 ⟨subd12_0_1061, List.forall_mem_cons.2 ⟨subd12_0_1062, List.forall_mem_cons.2 ⟨subd12_0_1063, List.forall_mem_cons.2 ⟨subd12_0_1064, List.forall_mem_cons.2 ⟨subd12_0_1065, List.forall_mem_cons.2 ⟨subd12_0_1066, List.forall_mem_cons.2 ⟨subd12_0_1067, List.forall_mem_cons.2 ⟨subd12_0_1068, List.forall_mem_cons.2 ⟨subd12_0_1069, List.forall_mem_cons.2 ⟨subd12_0_1070, List.forall_mem_cons.2 ⟨subd12_0_1071, List.forall_mem_cons.2 ⟨subd12_0_1072, List.forall_mem_cons.2 ⟨subd12_0_1073, List.forall_mem_cons.2 ⟨subd12_0_1074, List.forall_mem_cons.2 ⟨subd12_0_1075, List.forall_mem_cons.2 ⟨subd12_0_1076, List.forall_mem_cons.2 ⟨subd12_0_1077, List.forall_mem_cons.2 ⟨subd12_0_1078, List.forall_mem_cons.2 ⟨subd12_0_1079, List.forall_mem_cons.2 ⟨subd12_0_1080, List.forall_mem_cons.2 ⟨subd12_0_1081, List.forall_mem_cons.2 ⟨subd12_0_1082, List.forall_mem_cons.2 ⟨subd12_0_1083, List.forall_mem_cons.2 ⟨subd12_0_1084, List.forall_mem_cons.2 ⟨subd12_0_1085, List.forall_mem_cons.2 ⟨subd12_0_1086, List.forall_mem_cons.2 ⟨subd12_0_1087, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_1088 : subd12_0 [2, 3, 6] = true := by decide +kernel
theorem subd12_0_1089 : subd12_0 [2, 3, 7] = true := by decide +kernel
theorem subd12_0_1090 : subd12_0 [2, 3, 8] = true := by decide +kernel
theorem subd12_0_1091 : subd12_0 [2, 4, -5] = true := by decide +kernel
theorem subd12_0_1092 : subd12_0 [2, 4, -4] = true := by decide +kernel
theorem subd12_0_1093 : subd12_0 [2, 4, -3] = true := by decide +kernel
theorem subd12_0_1094 : subd12_0 [2, 4, -2] = true := by decide +kernel
theorem subd12_0_1095 : subd12_0 [2, 4, -1] = true := by decide +kernel
theorem subd12_0_1096 : subd12_0 [2, 4, 0] = true := by decide +kernel
theorem subd12_0_1097 : subd12_0 [2, 4, 1] = true := by decide +kernel
theorem subd12_0_1098 : subd12_0 [2, 4, 2] = true := by decide +kernel
theorem subd12_0_1099 : subd12_0 [2, 4, 3] = true := by decide +kernel
theorem subd12_0_1100 : subd12_0 [2, 4, 4] = true := by decide +kernel
theorem subd12_0_1101 : subd12_0 [2, 4, 5] = true := by decide +kernel
theorem subd12_0_1102 : subd12_0 [2, 4, 6] = true := by decide +kernel
theorem subd12_0_1103 : subd12_0 [2, 4, 7] = true := by decide +kernel
theorem subd12_0_1104 : subd12_0 [2, 4, 8] = true := by decide +kernel
theorem subd12_0_1105 : subd12_0 [2, 5] = true := by decide +kernel
theorem subd12_0_1106 : subd12_0 [2, 6] = true := by decide +kernel
theorem subd12_0_1107 : subd12_0 [2, 7] = true := by decide +kernel
theorem subd12_0_1108 : subd12_0 [3, -9] = true := by decide +kernel
theorem subd12_0_1109 : subd12_0 [3, -8] = true := by decide +kernel
theorem subd12_0_1110 : subd12_0 [3, -7] = true := by decide +kernel
theorem subd12_0_1111 : subd12_0 [3, -6] = true := by decide +kernel
theorem subd12_0_1112 : subd12_0 [3, -5] = true := by decide +kernel
theorem subd12_0_1113 : subd12_0 [3, -4, -9] = true := by decide +kernel
theorem subd12_0_1114 : subd12_0 [3, -4, -8] = true := by decide +kernel
theorem subd12_0_1115 : subd12_0 [3, -4, -7] = true := by decide +kernel
theorem subd12_0_1116 : subd12_0 [3, -4, -6] = true := by decide +kernel
theorem subd12_0_1117 : subd12_0 [3, -4, -5] = true := by decide +kernel
theorem subd12_0_1118 : subd12_0 [3, -4, -4] = true := by decide +kernel
theorem subd12_0_1119 : subd12_0 [3, -4, -3] = true := by decide +kernel
theorem sbd12_0_34 : ∀ q ∈ blkd12_0_34, subd12_0 q = true := by
  unfold blkd12_0_34
  exact List.forall_mem_cons.2 ⟨subd12_0_1088, List.forall_mem_cons.2 ⟨subd12_0_1089, List.forall_mem_cons.2 ⟨subd12_0_1090, List.forall_mem_cons.2 ⟨subd12_0_1091, List.forall_mem_cons.2 ⟨subd12_0_1092, List.forall_mem_cons.2 ⟨subd12_0_1093, List.forall_mem_cons.2 ⟨subd12_0_1094, List.forall_mem_cons.2 ⟨subd12_0_1095, List.forall_mem_cons.2 ⟨subd12_0_1096, List.forall_mem_cons.2 ⟨subd12_0_1097, List.forall_mem_cons.2 ⟨subd12_0_1098, List.forall_mem_cons.2 ⟨subd12_0_1099, List.forall_mem_cons.2 ⟨subd12_0_1100, List.forall_mem_cons.2 ⟨subd12_0_1101, List.forall_mem_cons.2 ⟨subd12_0_1102, List.forall_mem_cons.2 ⟨subd12_0_1103, List.forall_mem_cons.2 ⟨subd12_0_1104, List.forall_mem_cons.2 ⟨subd12_0_1105, List.forall_mem_cons.2 ⟨subd12_0_1106, List.forall_mem_cons.2 ⟨subd12_0_1107, List.forall_mem_cons.2 ⟨subd12_0_1108, List.forall_mem_cons.2 ⟨subd12_0_1109, List.forall_mem_cons.2 ⟨subd12_0_1110, List.forall_mem_cons.2 ⟨subd12_0_1111, List.forall_mem_cons.2 ⟨subd12_0_1112, List.forall_mem_cons.2 ⟨subd12_0_1113, List.forall_mem_cons.2 ⟨subd12_0_1114, List.forall_mem_cons.2 ⟨subd12_0_1115, List.forall_mem_cons.2 ⟨subd12_0_1116, List.forall_mem_cons.2 ⟨subd12_0_1117, List.forall_mem_cons.2 ⟨subd12_0_1118, List.forall_mem_cons.2 ⟨subd12_0_1119, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_1120 : subd12_0 [3, -4, -2] = true := by decide +kernel
theorem subd12_0_1121 : subd12_0 [3, -4, -1] = true := by decide +kernel
theorem subd12_0_1122 : subd12_0 [3, -4, 0] = true := by decide +kernel
theorem subd12_0_1123 : subd12_0 [3, -4, 1] = true := by decide +kernel
theorem subd12_0_1124 : subd12_0 [3, -4, 2] = true := by decide +kernel
theorem subd12_0_1125 : subd12_0 [3, -4, 3] = true := by decide +kernel
theorem subd12_0_1126 : subd12_0 [3, -4, 4] = true := by decide +kernel
theorem subd12_0_1127 : subd12_0 [3, -4, 5] = true := by decide +kernel
theorem subd12_0_1128 : subd12_0 [3, -3, -9] = true := by decide +kernel
theorem subd12_0_1129 : subd12_0 [3, -3, -8] = true := by decide +kernel
theorem subd12_0_1130 : subd12_0 [3, -3, -7] = true := by decide +kernel
theorem subd12_0_1131 : subd12_0 [3, -3, -6] = true := by decide +kernel
theorem subd12_0_1132 : subd12_0 [3, -3, -5] = true := by decide +kernel
theorem subd12_0_1133 : subd12_0 [3, -3, -4] = true := by decide +kernel
theorem subd12_0_1134 : subd12_0 [3, -3, -3] = true := by decide +kernel
theorem subd12_0_1135 : subd12_0 [3, -3, -2] = true := by decide +kernel
theorem subd12_0_1136 : subd12_0 [3, -3, -1] = true := by decide +kernel
theorem subd12_0_1137 : subd12_0 [3, -3, 0] = true := by decide +kernel
theorem subd12_0_1138 : subd12_0 [3, -3, 1] = true := by decide +kernel
theorem subd12_0_1139 : subd12_0 [3, -3, 2] = true := by decide +kernel
theorem subd12_0_1140 : subd12_0 [3, -3, 3] = true := by decide +kernel
theorem subd12_0_1141 : subd12_0 [3, -3, 4] = true := by decide +kernel
theorem subd12_0_1142 : subd12_0 [3, -3, 5] = true := by decide +kernel
theorem subd12_0_1143 : subd12_0 [3, -2, -9] = true := by decide +kernel
theorem subd12_0_1144 : subd12_0 [3, -2, -8] = true := by decide +kernel
theorem subd12_0_1145 : subd12_0 [3, -2, -7] = true := by decide +kernel
theorem subd12_0_1146 : subd12_0 [3, -2, -6] = true := by decide +kernel
theorem subd12_0_1147 : subd12_0 [3, -2, -5] = true := by decide +kernel
theorem subd12_0_1148 : subd12_0 [3, -2, -4] = true := by decide +kernel
theorem subd12_0_1149 : subd12_0 [3, -2, -3] = true := by decide +kernel
theorem subd12_0_1150 : subd12_0 [3, -2, -2] = true := by decide +kernel
theorem subd12_0_1151 : subd12_0 [3, -2, -1] = true := by decide +kernel
theorem sbd12_0_35 : ∀ q ∈ blkd12_0_35, subd12_0 q = true := by
  unfold blkd12_0_35
  exact List.forall_mem_cons.2 ⟨subd12_0_1120, List.forall_mem_cons.2 ⟨subd12_0_1121, List.forall_mem_cons.2 ⟨subd12_0_1122, List.forall_mem_cons.2 ⟨subd12_0_1123, List.forall_mem_cons.2 ⟨subd12_0_1124, List.forall_mem_cons.2 ⟨subd12_0_1125, List.forall_mem_cons.2 ⟨subd12_0_1126, List.forall_mem_cons.2 ⟨subd12_0_1127, List.forall_mem_cons.2 ⟨subd12_0_1128, List.forall_mem_cons.2 ⟨subd12_0_1129, List.forall_mem_cons.2 ⟨subd12_0_1130, List.forall_mem_cons.2 ⟨subd12_0_1131, List.forall_mem_cons.2 ⟨subd12_0_1132, List.forall_mem_cons.2 ⟨subd12_0_1133, List.forall_mem_cons.2 ⟨subd12_0_1134, List.forall_mem_cons.2 ⟨subd12_0_1135, List.forall_mem_cons.2 ⟨subd12_0_1136, List.forall_mem_cons.2 ⟨subd12_0_1137, List.forall_mem_cons.2 ⟨subd12_0_1138, List.forall_mem_cons.2 ⟨subd12_0_1139, List.forall_mem_cons.2 ⟨subd12_0_1140, List.forall_mem_cons.2 ⟨subd12_0_1141, List.forall_mem_cons.2 ⟨subd12_0_1142, List.forall_mem_cons.2 ⟨subd12_0_1143, List.forall_mem_cons.2 ⟨subd12_0_1144, List.forall_mem_cons.2 ⟨subd12_0_1145, List.forall_mem_cons.2 ⟨subd12_0_1146, List.forall_mem_cons.2 ⟨subd12_0_1147, List.forall_mem_cons.2 ⟨subd12_0_1148, List.forall_mem_cons.2 ⟨subd12_0_1149, List.forall_mem_cons.2 ⟨subd12_0_1150, List.forall_mem_cons.2 ⟨subd12_0_1151, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C131
