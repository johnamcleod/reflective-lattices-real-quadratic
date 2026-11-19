import ReflectZphi.Data.Cert5.C105.Base

namespace ReflectZphi.Data.Cert5.C105
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub9_672 : sub9 [1, 3, 6] = true := by decide +kernel
theorem sub9_673 : sub9 [1, 3, 7] = true := by decide +kernel
theorem sub9_674 : sub9 [1, 3, 8] = true := by decide +kernel
theorem sub9_675 : sub9 [1, 4] = true := by decide +kernel
theorem sub9_676 : sub9 [1, 5] = true := by decide +kernel
theorem sub9_677 : sub9 [2, -6] = true := by decide +kernel
theorem sub9_678 : sub9 [2, -5] = true := by decide +kernel
theorem sub9_679 : sub9 [2, -4] = true := by decide +kernel
theorem sub9_680 : sub9 [2, -3, -8] = true := by decide +kernel
theorem sub9_681 : sub9 [2, -3, -7] = true := by decide +kernel
theorem sub9_682 : sub9 [2, -3, -6] = true := by decide +kernel
theorem sub9_683 : sub9 [2, -3, -5] = true := by decide +kernel
theorem sub9_684 : sub9 [2, -3, -4] = true := by decide +kernel
theorem sub9_685 : sub9 [2, -3, -3] = true := by decide +kernel
theorem sub9_686 : sub9 [2, -3, -2] = true := by decide +kernel
theorem sub9_687 : sub9 [2, -3, -1] = true := by decide +kernel
theorem sub9_688 : sub9 [2, -3, 0] = true := by decide +kernel
theorem sub9_689 : sub9 [2, -3, 1] = true := by decide +kernel
theorem sub9_690 : sub9 [2, -3, 2] = true := by decide +kernel
theorem sub9_691 : sub9 [2, -3, 3] = true := by decide +kernel
theorem sub9_692 : sub9 [2, -3, 4] = true := by decide +kernel
theorem sub9_693 : sub9 [2, -3, 5] = true := by decide +kernel
theorem sub9_694 : sub9 [2, -3, 6] = true := by decide +kernel
theorem sub9_695 : sub9 [2, -2, -9] = true := by decide +kernel
theorem sub9_696 : sub9 [2, -2, -8] = true := by decide +kernel
theorem sub9_697 : sub9 [2, -2, -7] = true := by decide +kernel
theorem sub9_698 : sub9 [2, -2, -6] = true := by decide +kernel
theorem sub9_699 : sub9 [2, -2, -5] = true := by decide +kernel
theorem sub9_700 : sub9 [2, -2, -4] = true := by decide +kernel
theorem sub9_701 : sub9 [2, -2, -3] = true := by decide +kernel
theorem sub9_702 : sub9 [2, -2, -2] = true := by decide +kernel
theorem sub9_703 : sub9 [2, -2, -1] = true := by decide +kernel
theorem sb9_21 : ∀ q ∈ blk9_21, sub9 q = true := by
  unfold blk9_21
  exact List.forall_mem_cons.2 ⟨sub9_672, List.forall_mem_cons.2 ⟨sub9_673, List.forall_mem_cons.2 ⟨sub9_674, List.forall_mem_cons.2 ⟨sub9_675, List.forall_mem_cons.2 ⟨sub9_676, List.forall_mem_cons.2 ⟨sub9_677, List.forall_mem_cons.2 ⟨sub9_678, List.forall_mem_cons.2 ⟨sub9_679, List.forall_mem_cons.2 ⟨sub9_680, List.forall_mem_cons.2 ⟨sub9_681, List.forall_mem_cons.2 ⟨sub9_682, List.forall_mem_cons.2 ⟨sub9_683, List.forall_mem_cons.2 ⟨sub9_684, List.forall_mem_cons.2 ⟨sub9_685, List.forall_mem_cons.2 ⟨sub9_686, List.forall_mem_cons.2 ⟨sub9_687, List.forall_mem_cons.2 ⟨sub9_688, List.forall_mem_cons.2 ⟨sub9_689, List.forall_mem_cons.2 ⟨sub9_690, List.forall_mem_cons.2 ⟨sub9_691, List.forall_mem_cons.2 ⟨sub9_692, List.forall_mem_cons.2 ⟨sub9_693, List.forall_mem_cons.2 ⟨sub9_694, List.forall_mem_cons.2 ⟨sub9_695, List.forall_mem_cons.2 ⟨sub9_696, List.forall_mem_cons.2 ⟨sub9_697, List.forall_mem_cons.2 ⟨sub9_698, List.forall_mem_cons.2 ⟨sub9_699, List.forall_mem_cons.2 ⟨sub9_700, List.forall_mem_cons.2 ⟨sub9_701, List.forall_mem_cons.2 ⟨sub9_702, List.forall_mem_cons.2 ⟨sub9_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_704 : sub9 [2, -2, 0] = true := by decide +kernel
theorem sub9_705 : sub9 [2, -2, 1] = true := by decide +kernel
theorem sub9_706 : sub9 [2, -2, 2] = true := by decide +kernel
theorem sub9_707 : sub9 [2, -2, 3] = true := by decide +kernel
theorem sub9_708 : sub9 [2, -2, 4] = true := by decide +kernel
theorem sub9_709 : sub9 [2, -2, 5] = true := by decide +kernel
theorem sub9_710 : sub9 [2, -2, 6] = true := by decide +kernel
theorem sub9_711 : sub9 [2, -2, 7] = true := by decide +kernel
theorem sub9_712 : sub9 [2, -1, -10] = true := by decide +kernel
theorem sub9_713 : sub9 [2, -1, -9] = true := by decide +kernel
theorem sub9_714 : sub9 [2, -1, -8] = true := by decide +kernel
theorem sub9_715 : sub9 [2, -1, -7] = true := by decide +kernel
theorem sub9_716 : sub9 [2, -1, -6] = true := by decide +kernel
theorem sub9_717 : sub9 [2, -1, -5] = true := by decide +kernel
theorem sub9_718 : sub9 [2, -1, -4] = true := by decide +kernel
theorem sub9_719 : sub9 [2, -1, -3] = true := by decide +kernel
theorem sub9_720 : sub9 [2, -1, -2] = true := by decide +kernel
theorem sub9_721 : sub9 [2, -1, -1] = true := by decide +kernel
theorem sub9_722 : sub9 [2, -1, 0] = true := by decide +kernel
theorem sub9_723 : sub9 [2, -1, 1] = true := by decide +kernel
theorem sub9_724 : sub9 [2, -1, 2] = true := by decide +kernel
theorem sub9_725 : sub9 [2, -1, 3] = true := by decide +kernel
theorem sub9_726 : sub9 [2, -1, 4] = true := by decide +kernel
theorem sub9_727 : sub9 [2, -1, 5] = true := by decide +kernel
theorem sub9_728 : sub9 [2, -1, 6] = true := by decide +kernel
theorem sub9_729 : sub9 [2, -1, 7] = true := by decide +kernel
theorem sub9_730 : sub9 [2, -1, 8] = true := by decide +kernel
theorem sub9_731 : sub9 [2, 0, -10] = true := by decide +kernel
theorem sub9_732 : sub9 [2, 0, -9] = true := by decide +kernel
theorem sub9_733 : sub9 [2, 0, -8] = true := by decide +kernel
theorem sub9_734 : sub9 [2, 0, -7] = true := by decide +kernel
theorem sub9_735 : sub9 [2, 0, -6] = true := by decide +kernel
theorem sb9_22 : ∀ q ∈ blk9_22, sub9 q = true := by
  unfold blk9_22
  exact List.forall_mem_cons.2 ⟨sub9_704, List.forall_mem_cons.2 ⟨sub9_705, List.forall_mem_cons.2 ⟨sub9_706, List.forall_mem_cons.2 ⟨sub9_707, List.forall_mem_cons.2 ⟨sub9_708, List.forall_mem_cons.2 ⟨sub9_709, List.forall_mem_cons.2 ⟨sub9_710, List.forall_mem_cons.2 ⟨sub9_711, List.forall_mem_cons.2 ⟨sub9_712, List.forall_mem_cons.2 ⟨sub9_713, List.forall_mem_cons.2 ⟨sub9_714, List.forall_mem_cons.2 ⟨sub9_715, List.forall_mem_cons.2 ⟨sub9_716, List.forall_mem_cons.2 ⟨sub9_717, List.forall_mem_cons.2 ⟨sub9_718, List.forall_mem_cons.2 ⟨sub9_719, List.forall_mem_cons.2 ⟨sub9_720, List.forall_mem_cons.2 ⟨sub9_721, List.forall_mem_cons.2 ⟨sub9_722, List.forall_mem_cons.2 ⟨sub9_723, List.forall_mem_cons.2 ⟨sub9_724, List.forall_mem_cons.2 ⟨sub9_725, List.forall_mem_cons.2 ⟨sub9_726, List.forall_mem_cons.2 ⟨sub9_727, List.forall_mem_cons.2 ⟨sub9_728, List.forall_mem_cons.2 ⟨sub9_729, List.forall_mem_cons.2 ⟨sub9_730, List.forall_mem_cons.2 ⟨sub9_731, List.forall_mem_cons.2 ⟨sub9_732, List.forall_mem_cons.2 ⟨sub9_733, List.forall_mem_cons.2 ⟨sub9_734, List.forall_mem_cons.2 ⟨sub9_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_736 : sub9 [2, 0, -5] = true := by decide +kernel
theorem sub9_737 : sub9 [2, 0, -4] = true := by decide +kernel
theorem sub9_738 : sub9 [2, 0, -3] = true := by decide +kernel
theorem sub9_739 : sub9 [2, 0, -2] = true := by decide +kernel
theorem sub9_740 : sub9 [2, 0, -1] = true := by decide +kernel
theorem sub9_741 : sub9 [2, 0, 0] = true := by decide +kernel
theorem sub9_742 : sub9 [2, 0, 1] = true := by decide +kernel
theorem sub9_743 : sub9 [2, 0, 2] = true := by decide +kernel
theorem sub9_744 : sub9 [2, 0, 3] = true := by decide +kernel
theorem sub9_745 : sub9 [2, 0, 4] = true := by decide +kernel
theorem sub9_746 : sub9 [2, 0, 5] = true := by decide +kernel
theorem sub9_747 : sub9 [2, 0, 6] = true := by decide +kernel
theorem sub9_748 : sub9 [2, 0, 7] = true := by decide +kernel
theorem sub9_749 : sub9 [2, 0, 8] = true := by decide +kernel
theorem sub9_750 : sub9 [2, 1, -9] = true := by decide +kernel
theorem sub9_751 : sub9 [2, 1, -8] = true := by decide +kernel
theorem sub9_752 : sub9 [2, 1, -7] = true := by decide +kernel
theorem sub9_753 : sub9 [2, 1, -6] = true := by decide +kernel
theorem sub9_754 : sub9 [2, 1, -5] = true := by decide +kernel
theorem sub9_755 : sub9 [2, 1, -4] = true := by decide +kernel
theorem sub9_756 : sub9 [2, 1, -3] = true := by decide +kernel
theorem sub9_757 : sub9 [2, 1, -2] = true := by decide +kernel
theorem sub9_758 : sub9 [2, 1, -1] = true := by decide +kernel
theorem sub9_759 : sub9 [2, 1, 0] = true := by decide +kernel
theorem sub9_760 : sub9 [2, 1, 1] = true := by decide +kernel
theorem sub9_761 : sub9 [2, 1, 2] = true := by decide +kernel
theorem sub9_762 : sub9 [2, 1, 3] = true := by decide +kernel
theorem sub9_763 : sub9 [2, 1, 4] = true := by decide +kernel
theorem sub9_764 : sub9 [2, 1, 5] = true := by decide +kernel
theorem sub9_765 : sub9 [2, 1, 6] = true := by decide +kernel
theorem sub9_766 : sub9 [2, 1, 7] = true := by decide +kernel
theorem sub9_767 : sub9 [2, 1, 8] = true := by decide +kernel
theorem sb9_23 : ∀ q ∈ blk9_23, sub9 q = true := by
  unfold blk9_23
  exact List.forall_mem_cons.2 ⟨sub9_736, List.forall_mem_cons.2 ⟨sub9_737, List.forall_mem_cons.2 ⟨sub9_738, List.forall_mem_cons.2 ⟨sub9_739, List.forall_mem_cons.2 ⟨sub9_740, List.forall_mem_cons.2 ⟨sub9_741, List.forall_mem_cons.2 ⟨sub9_742, List.forall_mem_cons.2 ⟨sub9_743, List.forall_mem_cons.2 ⟨sub9_744, List.forall_mem_cons.2 ⟨sub9_745, List.forall_mem_cons.2 ⟨sub9_746, List.forall_mem_cons.2 ⟨sub9_747, List.forall_mem_cons.2 ⟨sub9_748, List.forall_mem_cons.2 ⟨sub9_749, List.forall_mem_cons.2 ⟨sub9_750, List.forall_mem_cons.2 ⟨sub9_751, List.forall_mem_cons.2 ⟨sub9_752, List.forall_mem_cons.2 ⟨sub9_753, List.forall_mem_cons.2 ⟨sub9_754, List.forall_mem_cons.2 ⟨sub9_755, List.forall_mem_cons.2 ⟨sub9_756, List.forall_mem_cons.2 ⟨sub9_757, List.forall_mem_cons.2 ⟨sub9_758, List.forall_mem_cons.2 ⟨sub9_759, List.forall_mem_cons.2 ⟨sub9_760, List.forall_mem_cons.2 ⟨sub9_761, List.forall_mem_cons.2 ⟨sub9_762, List.forall_mem_cons.2 ⟨sub9_763, List.forall_mem_cons.2 ⟨sub9_764, List.forall_mem_cons.2 ⟨sub9_765, List.forall_mem_cons.2 ⟨sub9_766, List.forall_mem_cons.2 ⟨sub9_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_768 : sub9 [2, 2, -9] = true := by decide +kernel
theorem sub9_769 : sub9 [2, 2, -8] = true := by decide +kernel
theorem sub9_770 : sub9 [2, 2, -7] = true := by decide +kernel
theorem sub9_771 : sub9 [2, 2, -6] = true := by decide +kernel
theorem sub9_772 : sub9 [2, 2, -5] = true := by decide +kernel
theorem sub9_773 : sub9 [2, 2, -4] = true := by decide +kernel
theorem sub9_774 : sub9 [2, 2, -3] = true := by decide +kernel
theorem sub9_775 : sub9 [2, 2, -2] = true := by decide +kernel
theorem sub9_776 : sub9 [2, 2, -1] = true := by decide +kernel
theorem sub9_777 : sub9 [2, 2, 0] = true := by decide +kernel
theorem sub9_778 : sub9 [2, 2, 1] = true := by decide +kernel
theorem sub9_779 : sub9 [2, 2, 2] = true := by decide +kernel
theorem sub9_780 : sub9 [2, 2, 3] = true := by decide +kernel
theorem sub9_781 : sub9 [2, 2, 4] = true := by decide +kernel
theorem sub9_782 : sub9 [2, 2, 5] = true := by decide +kernel
theorem sub9_783 : sub9 [2, 2, 6] = true := by decide +kernel
theorem sub9_784 : sub9 [2, 2, 7] = true := by decide +kernel
theorem sub9_785 : sub9 [2, 2, 8] = true := by decide +kernel
theorem sub9_786 : sub9 [2, 3, -8] = true := by decide +kernel
theorem sub9_787 : sub9 [2, 3, -7] = true := by decide +kernel
theorem sub9_788 : sub9 [2, 3, -6] = true := by decide +kernel
theorem sub9_789 : sub9 [2, 3, -5] = true := by decide +kernel
theorem sub9_790 : sub9 [2, 3, -4] = true := by decide +kernel
theorem sub9_791 : sub9 [2, 3, -3] = true := by decide +kernel
theorem sub9_792 : sub9 [2, 3, -2] = true := by decide +kernel
theorem sub9_793 : sub9 [2, 3, -1] = true := by decide +kernel
theorem sub9_794 : sub9 [2, 3, 0] = true := by decide +kernel
theorem sub9_795 : sub9 [2, 3, 1] = true := by decide +kernel
theorem sub9_796 : sub9 [2, 3, 2] = true := by decide +kernel
theorem sub9_797 : sub9 [2, 3, 3] = true := by decide +kernel
theorem sub9_798 : sub9 [2, 3, 4] = true := by decide +kernel
theorem sub9_799 : sub9 [2, 3, 5] = true := by decide +kernel
theorem sb9_24 : ∀ q ∈ blk9_24, sub9 q = true := by
  unfold blk9_24
  exact List.forall_mem_cons.2 ⟨sub9_768, List.forall_mem_cons.2 ⟨sub9_769, List.forall_mem_cons.2 ⟨sub9_770, List.forall_mem_cons.2 ⟨sub9_771, List.forall_mem_cons.2 ⟨sub9_772, List.forall_mem_cons.2 ⟨sub9_773, List.forall_mem_cons.2 ⟨sub9_774, List.forall_mem_cons.2 ⟨sub9_775, List.forall_mem_cons.2 ⟨sub9_776, List.forall_mem_cons.2 ⟨sub9_777, List.forall_mem_cons.2 ⟨sub9_778, List.forall_mem_cons.2 ⟨sub9_779, List.forall_mem_cons.2 ⟨sub9_780, List.forall_mem_cons.2 ⟨sub9_781, List.forall_mem_cons.2 ⟨sub9_782, List.forall_mem_cons.2 ⟨sub9_783, List.forall_mem_cons.2 ⟨sub9_784, List.forall_mem_cons.2 ⟨sub9_785, List.forall_mem_cons.2 ⟨sub9_786, List.forall_mem_cons.2 ⟨sub9_787, List.forall_mem_cons.2 ⟨sub9_788, List.forall_mem_cons.2 ⟨sub9_789, List.forall_mem_cons.2 ⟨sub9_790, List.forall_mem_cons.2 ⟨sub9_791, List.forall_mem_cons.2 ⟨sub9_792, List.forall_mem_cons.2 ⟨sub9_793, List.forall_mem_cons.2 ⟨sub9_794, List.forall_mem_cons.2 ⟨sub9_795, List.forall_mem_cons.2 ⟨sub9_796, List.forall_mem_cons.2 ⟨sub9_797, List.forall_mem_cons.2 ⟨sub9_798, List.forall_mem_cons.2 ⟨sub9_799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_800 : sub9 [2, 3, 6] = true := by decide +kernel
theorem sub9_801 : sub9 [2, 3, 7] = true := by decide +kernel
theorem sub9_802 : sub9 [2, 4] = true := by decide +kernel
theorem sub9_803 : sub9 [2, 5] = true := by decide +kernel
theorem sub9_804 : sub9 [3, -5] = true := by decide +kernel
theorem sub9_805 : sub9 [3, -4] = true := by decide +kernel
theorem sub9_806 : sub9 [3, -3] = true := by decide +kernel
theorem sub9_807 : sub9 [3, -2, -8] = true := by decide +kernel
theorem sub9_808 : sub9 [3, -2, -7] = true := by decide +kernel
theorem sub9_809 : sub9 [3, -2, -6] = true := by decide +kernel
theorem sub9_810 : sub9 [3, -2, -5] = true := by decide +kernel
theorem sub9_811 : sub9 [3, -2, -4] = true := by decide +kernel
theorem sub9_812 : sub9 [3, -2, -3] = true := by decide +kernel
theorem sub9_813 : sub9 [3, -2, -2] = true := by decide +kernel
theorem sub9_814 : sub9 [3, -2, -1] = true := by decide +kernel
theorem sub9_815 : sub9 [3, -2, 0] = true := by decide +kernel
theorem sub9_816 : sub9 [3, -2, 1] = true := by decide +kernel
theorem sub9_817 : sub9 [3, -2, 2] = true := by decide +kernel
theorem sub9_818 : sub9 [3, -2, 3] = true := by decide +kernel
theorem sub9_819 : sub9 [3, -2, 4] = true := by decide +kernel
theorem sub9_820 : sub9 [3, -2, 5] = true := by decide +kernel
theorem sub9_821 : sub9 [3, -2, 6] = true := by decide +kernel
theorem sub9_822 : sub9 [3, -1, -9] = true := by decide +kernel
theorem sub9_823 : sub9 [3, -1, -8] = true := by decide +kernel
theorem sub9_824 : sub9 [3, -1, -7] = true := by decide +kernel
theorem sub9_825 : sub9 [3, -1, -6] = true := by decide +kernel
theorem sub9_826 : sub9 [3, -1, -5] = true := by decide +kernel
theorem sub9_827 : sub9 [3, -1, -4] = true := by decide +kernel
theorem sub9_828 : sub9 [3, -1, -3] = true := by decide +kernel
theorem sub9_829 : sub9 [3, -1, -2] = true := by decide +kernel
theorem sub9_830 : sub9 [3, -1, -1] = true := by decide +kernel
theorem sub9_831 : sub9 [3, -1, 0] = true := by decide +kernel
theorem sb9_25 : ∀ q ∈ blk9_25, sub9 q = true := by
  unfold blk9_25
  exact List.forall_mem_cons.2 ⟨sub9_800, List.forall_mem_cons.2 ⟨sub9_801, List.forall_mem_cons.2 ⟨sub9_802, List.forall_mem_cons.2 ⟨sub9_803, List.forall_mem_cons.2 ⟨sub9_804, List.forall_mem_cons.2 ⟨sub9_805, List.forall_mem_cons.2 ⟨sub9_806, List.forall_mem_cons.2 ⟨sub9_807, List.forall_mem_cons.2 ⟨sub9_808, List.forall_mem_cons.2 ⟨sub9_809, List.forall_mem_cons.2 ⟨sub9_810, List.forall_mem_cons.2 ⟨sub9_811, List.forall_mem_cons.2 ⟨sub9_812, List.forall_mem_cons.2 ⟨sub9_813, List.forall_mem_cons.2 ⟨sub9_814, List.forall_mem_cons.2 ⟨sub9_815, List.forall_mem_cons.2 ⟨sub9_816, List.forall_mem_cons.2 ⟨sub9_817, List.forall_mem_cons.2 ⟨sub9_818, List.forall_mem_cons.2 ⟨sub9_819, List.forall_mem_cons.2 ⟨sub9_820, List.forall_mem_cons.2 ⟨sub9_821, List.forall_mem_cons.2 ⟨sub9_822, List.forall_mem_cons.2 ⟨sub9_823, List.forall_mem_cons.2 ⟨sub9_824, List.forall_mem_cons.2 ⟨sub9_825, List.forall_mem_cons.2 ⟨sub9_826, List.forall_mem_cons.2 ⟨sub9_827, List.forall_mem_cons.2 ⟨sub9_828, List.forall_mem_cons.2 ⟨sub9_829, List.forall_mem_cons.2 ⟨sub9_830, List.forall_mem_cons.2 ⟨sub9_831, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_832 : sub9 [3, -1, 1] = true := by decide +kernel
theorem sub9_833 : sub9 [3, -1, 2] = true := by decide +kernel
theorem sub9_834 : sub9 [3, -1, 3] = true := by decide +kernel
theorem sub9_835 : sub9 [3, -1, 4] = true := by decide +kernel
theorem sub9_836 : sub9 [3, -1, 5] = true := by decide +kernel
theorem sub9_837 : sub9 [3, -1, 6] = true := by decide +kernel
theorem sub9_838 : sub9 [3, -1, 7] = true := by decide +kernel
theorem sub9_839 : sub9 [3, 0, -9] = true := by decide +kernel
theorem sub9_840 : sub9 [3, 0, -8] = true := by decide +kernel
theorem sub9_841 : sub9 [3, 0, -7] = true := by decide +kernel
theorem sub9_842 : sub9 [3, 0, -6] = true := by decide +kernel
theorem sub9_843 : sub9 [3, 0, -5] = true := by decide +kernel
theorem sub9_844 : sub9 [3, 0, -4] = true := by decide +kernel
theorem sub9_845 : sub9 [3, 0, -3] = true := by decide +kernel
theorem sub9_846 : sub9 [3, 0, -2] = true := by decide +kernel
theorem sub9_847 : sub9 [3, 0, -1] = true := by decide +kernel
theorem sub9_848 : sub9 [3, 0, 0] = true := by decide +kernel
theorem sub9_849 : sub9 [3, 0, 1] = true := by decide +kernel
theorem sub9_850 : sub9 [3, 0, 2] = true := by decide +kernel
theorem sub9_851 : sub9 [3, 0, 3] = true := by decide +kernel
theorem sub9_852 : sub9 [3, 0, 4] = true := by decide +kernel
theorem sub9_853 : sub9 [3, 0, 5] = true := by decide +kernel
theorem sub9_854 : sub9 [3, 0, 6] = true := by decide +kernel
theorem sub9_855 : sub9 [3, 0, 7] = true := by decide +kernel
theorem sub9_856 : sub9 [3, 1, -8] = true := by decide +kernel
theorem sub9_857 : sub9 [3, 1, -7] = true := by decide +kernel
theorem sub9_858 : sub9 [3, 1, -6] = true := by decide +kernel
theorem sub9_859 : sub9 [3, 1, -5] = true := by decide +kernel
theorem sub9_860 : sub9 [3, 1, -4] = true := by decide +kernel
theorem sub9_861 : sub9 [3, 1, -3] = true := by decide +kernel
theorem sub9_862 : sub9 [3, 1, -2] = true := by decide +kernel
theorem sub9_863 : sub9 [3, 1, -1] = true := by decide +kernel
theorem sb9_26 : ∀ q ∈ blk9_26, sub9 q = true := by
  unfold blk9_26
  exact List.forall_mem_cons.2 ⟨sub9_832, List.forall_mem_cons.2 ⟨sub9_833, List.forall_mem_cons.2 ⟨sub9_834, List.forall_mem_cons.2 ⟨sub9_835, List.forall_mem_cons.2 ⟨sub9_836, List.forall_mem_cons.2 ⟨sub9_837, List.forall_mem_cons.2 ⟨sub9_838, List.forall_mem_cons.2 ⟨sub9_839, List.forall_mem_cons.2 ⟨sub9_840, List.forall_mem_cons.2 ⟨sub9_841, List.forall_mem_cons.2 ⟨sub9_842, List.forall_mem_cons.2 ⟨sub9_843, List.forall_mem_cons.2 ⟨sub9_844, List.forall_mem_cons.2 ⟨sub9_845, List.forall_mem_cons.2 ⟨sub9_846, List.forall_mem_cons.2 ⟨sub9_847, List.forall_mem_cons.2 ⟨sub9_848, List.forall_mem_cons.2 ⟨sub9_849, List.forall_mem_cons.2 ⟨sub9_850, List.forall_mem_cons.2 ⟨sub9_851, List.forall_mem_cons.2 ⟨sub9_852, List.forall_mem_cons.2 ⟨sub9_853, List.forall_mem_cons.2 ⟨sub9_854, List.forall_mem_cons.2 ⟨sub9_855, List.forall_mem_cons.2 ⟨sub9_856, List.forall_mem_cons.2 ⟨sub9_857, List.forall_mem_cons.2 ⟨sub9_858, List.forall_mem_cons.2 ⟨sub9_859, List.forall_mem_cons.2 ⟨sub9_860, List.forall_mem_cons.2 ⟨sub9_861, List.forall_mem_cons.2 ⟨sub9_862, List.forall_mem_cons.2 ⟨sub9_863, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_864 : sub9 [3, 1, 0] = true := by decide +kernel
theorem sub9_865 : sub9 [3, 1, 1] = true := by decide +kernel
theorem sub9_866 : sub9 [3, 1, 2] = true := by decide +kernel
theorem sub9_867 : sub9 [3, 1, 3] = true := by decide +kernel
theorem sub9_868 : sub9 [3, 1, 4] = true := by decide +kernel
theorem sub9_869 : sub9 [3, 1, 5] = true := by decide +kernel
theorem sub9_870 : sub9 [3, 1, 6] = true := by decide +kernel
theorem sub9_871 : sub9 [3, 1, 7] = true := by decide +kernel
theorem sub9_872 : sub9 [3, 2, -8] = true := by decide +kernel
theorem sub9_873 : sub9 [3, 2, -7] = true := by decide +kernel
theorem sub9_874 : sub9 [3, 2, -6] = true := by decide +kernel
theorem sub9_875 : sub9 [3, 2, -5] = true := by decide +kernel
theorem sub9_876 : sub9 [3, 2, -4] = true := by decide +kernel
theorem sub9_877 : sub9 [3, 2, -3] = true := by decide +kernel
theorem sub9_878 : sub9 [3, 2, -2] = true := by decide +kernel
theorem sub9_879 : sub9 [3, 2, -1] = true := by decide +kernel
theorem sub9_880 : sub9 [3, 2, 0] = true := by decide +kernel
theorem sub9_881 : sub9 [3, 2, 1] = true := by decide +kernel
theorem sub9_882 : sub9 [3, 2, 2] = true := by decide +kernel
theorem sub9_883 : sub9 [3, 2, 3] = true := by decide +kernel
theorem sub9_884 : sub9 [3, 2, 4] = true := by decide +kernel
theorem sub9_885 : sub9 [3, 2, 5] = true := by decide +kernel
theorem sub9_886 : sub9 [3, 2, 6] = true := by decide +kernel
theorem sub9_887 : sub9 [3, 2, 7] = true := by decide +kernel
theorem sub9_888 : sub9 [3, 3] = true := by decide +kernel
theorem sub9_889 : sub9 [3, 4] = true := by decide +kernel
theorem sub9_890 : sub9 [4, -4] = true := by decide +kernel
theorem sub9_891 : sub9 [4, -3] = true := by decide +kernel
theorem sub9_892 : sub9 [4, -2] = true := by decide +kernel
theorem sub9_893 : sub9 [4, -1] = true := by decide +kernel
theorem sub9_894 : sub9 [4, 0, -7] = true := by decide +kernel
theorem sub9_895 : sub9 [4, 0, -6] = true := by decide +kernel
theorem sb9_27 : ∀ q ∈ blk9_27, sub9 q = true := by
  unfold blk9_27
  exact List.forall_mem_cons.2 ⟨sub9_864, List.forall_mem_cons.2 ⟨sub9_865, List.forall_mem_cons.2 ⟨sub9_866, List.forall_mem_cons.2 ⟨sub9_867, List.forall_mem_cons.2 ⟨sub9_868, List.forall_mem_cons.2 ⟨sub9_869, List.forall_mem_cons.2 ⟨sub9_870, List.forall_mem_cons.2 ⟨sub9_871, List.forall_mem_cons.2 ⟨sub9_872, List.forall_mem_cons.2 ⟨sub9_873, List.forall_mem_cons.2 ⟨sub9_874, List.forall_mem_cons.2 ⟨sub9_875, List.forall_mem_cons.2 ⟨sub9_876, List.forall_mem_cons.2 ⟨sub9_877, List.forall_mem_cons.2 ⟨sub9_878, List.forall_mem_cons.2 ⟨sub9_879, List.forall_mem_cons.2 ⟨sub9_880, List.forall_mem_cons.2 ⟨sub9_881, List.forall_mem_cons.2 ⟨sub9_882, List.forall_mem_cons.2 ⟨sub9_883, List.forall_mem_cons.2 ⟨sub9_884, List.forall_mem_cons.2 ⟨sub9_885, List.forall_mem_cons.2 ⟨sub9_886, List.forall_mem_cons.2 ⟨sub9_887, List.forall_mem_cons.2 ⟨sub9_888, List.forall_mem_cons.2 ⟨sub9_889, List.forall_mem_cons.2 ⟨sub9_890, List.forall_mem_cons.2 ⟨sub9_891, List.forall_mem_cons.2 ⟨sub9_892, List.forall_mem_cons.2 ⟨sub9_893, List.forall_mem_cons.2 ⟨sub9_894, List.forall_mem_cons.2 ⟨sub9_895, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_896 : sub9 [4, 0, -5] = true := by decide +kernel
theorem sub9_897 : sub9 [4, 0, -4] = true := by decide +kernel
theorem sub9_898 : sub9 [4, 0, -3] = true := by decide +kernel
theorem sub9_899 : sub9 [4, 0, -2] = true := by decide +kernel
theorem sub9_900 : sub9 [4, 0, -1] = true := by decide +kernel
theorem sub9_901 : sub9 [4, 0, 0] = true := by decide +kernel
theorem sub9_902 : sub9 [4, 0, 1] = true := by decide +kernel
theorem sub9_903 : sub9 [4, 0, 2] = true := by decide +kernel
theorem sub9_904 : sub9 [4, 0, 3] = true := by decide +kernel
theorem sub9_905 : sub9 [4, 0, 4] = true := by decide +kernel
theorem sub9_906 : sub9 [4, 0, 5] = true := by decide +kernel
theorem sub9_907 : sub9 [4, 0, 6] = true := by decide +kernel
theorem sub9_908 : sub9 [4, 1] = true := by decide +kernel
theorem sub9_909 : sub9 [4, 2] = true := by decide +kernel
theorem sub9_910 : sub9 [4, 3] = true := by decide +kernel
theorem sub9_911 : sub9 [5, -3] = true := by decide +kernel
theorem sub9_912 : sub9 [5, -2] = true := by decide +kernel
theorem sub9_913 : sub9 [5, -1] = true := by decide +kernel
theorem sub9_914 : sub9 [5, 0] = true := by decide +kernel
theorem sub9_915 : sub9 [5, 1] = true := by decide +kernel
theorem sub9_916 : sub9 [5, 2] = true := by decide +kernel
theorem sb9_28 : ∀ q ∈ blk9_28, sub9 q = true := by
  unfold blk9_28
  exact List.forall_mem_cons.2 ⟨sub9_896, List.forall_mem_cons.2 ⟨sub9_897, List.forall_mem_cons.2 ⟨sub9_898, List.forall_mem_cons.2 ⟨sub9_899, List.forall_mem_cons.2 ⟨sub9_900, List.forall_mem_cons.2 ⟨sub9_901, List.forall_mem_cons.2 ⟨sub9_902, List.forall_mem_cons.2 ⟨sub9_903, List.forall_mem_cons.2 ⟨sub9_904, List.forall_mem_cons.2 ⟨sub9_905, List.forall_mem_cons.2 ⟨sub9_906, List.forall_mem_cons.2 ⟨sub9_907, List.forall_mem_cons.2 ⟨sub9_908, List.forall_mem_cons.2 ⟨sub9_909, List.forall_mem_cons.2 ⟨sub9_910, List.forall_mem_cons.2 ⟨sub9_911, List.forall_mem_cons.2 ⟨sub9_912, List.forall_mem_cons.2 ⟨sub9_913, List.forall_mem_cons.2 ⟨sub9_914, List.forall_mem_cons.2 ⟨sub9_915, List.forall_mem_cons.2 ⟨sub9_916, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_0 : sub10 [-6] = true := by decide +kernel
theorem sub10_1 : sub10 [-5, -5] = true := by decide +kernel
theorem sub10_2 : sub10 [-5, -4] = true := by decide +kernel
theorem sub10_3 : sub10 [-5, -3] = true := by decide +kernel
theorem sub10_4 : sub10 [-5, -2] = true := by decide +kernel
theorem sub10_5 : sub10 [-5, -1] = true := by decide +kernel
theorem sub10_6 : sub10 [-5, 0] = true := by decide +kernel
theorem sub10_7 : sub10 [-5, 1] = true := by decide +kernel
theorem sub10_8 : sub10 [-5, 2] = true := by decide +kernel
theorem sub10_9 : sub10 [-4, -6] = true := by decide +kernel
theorem sub10_10 : sub10 [-4, -5] = true := by decide +kernel
theorem sub10_11 : sub10 [-4, -4] = true := by decide +kernel
theorem sub10_12 : sub10 [-4, -3] = true := by decide +kernel
theorem sub10_13 : sub10 [-4, -2] = true := by decide +kernel
theorem sub10_14 : sub10 [-4, -1] = true := by decide +kernel
theorem sub10_15 : sub10 [-4, 0] = true := by decide +kernel
theorem sub10_16 : sub10 [-4, 1] = true := by decide +kernel
theorem sub10_17 : sub10 [-4, 2] = true := by decide +kernel
theorem sub10_18 : sub10 [-4, 3] = true := by decide +kernel
theorem sub10_19 : sub10 [-3, -6] = true := by decide +kernel
theorem sub10_20 : sub10 [-3, -5] = true := by decide +kernel
theorem sub10_21 : sub10 [-3, -4] = true := by decide +kernel
theorem sub10_22 : sub10 [-3, -3] = true := by decide +kernel
theorem sub10_23 : sub10 [-3, -2, -7] = true := by decide +kernel
theorem sub10_24 : sub10 [-3, -2, -6] = true := by decide +kernel
theorem sub10_25 : sub10 [-3, -2, -5] = true := by decide +kernel
theorem sub10_26 : sub10 [-3, -2, -4] = true := by decide +kernel
theorem sub10_27 : sub10 [-3, -2, -3] = true := by decide +kernel
theorem sub10_28 : sub10 [-3, -2, -2] = true := by decide +kernel
theorem sub10_29 : sub10 [-3, -2, -1] = true := by decide +kernel
theorem sub10_30 : sub10 [-3, -2, 0] = true := by decide +kernel
theorem sub10_31 : sub10 [-3, -2, 1] = true := by decide +kernel
theorem sb10_0 : ∀ q ∈ blk10_0, sub10 q = true := by
  unfold blk10_0
  exact List.forall_mem_cons.2 ⟨sub10_0, List.forall_mem_cons.2 ⟨sub10_1, List.forall_mem_cons.2 ⟨sub10_2, List.forall_mem_cons.2 ⟨sub10_3, List.forall_mem_cons.2 ⟨sub10_4, List.forall_mem_cons.2 ⟨sub10_5, List.forall_mem_cons.2 ⟨sub10_6, List.forall_mem_cons.2 ⟨sub10_7, List.forall_mem_cons.2 ⟨sub10_8, List.forall_mem_cons.2 ⟨sub10_9, List.forall_mem_cons.2 ⟨sub10_10, List.forall_mem_cons.2 ⟨sub10_11, List.forall_mem_cons.2 ⟨sub10_12, List.forall_mem_cons.2 ⟨sub10_13, List.forall_mem_cons.2 ⟨sub10_14, List.forall_mem_cons.2 ⟨sub10_15, List.forall_mem_cons.2 ⟨sub10_16, List.forall_mem_cons.2 ⟨sub10_17, List.forall_mem_cons.2 ⟨sub10_18, List.forall_mem_cons.2 ⟨sub10_19, List.forall_mem_cons.2 ⟨sub10_20, List.forall_mem_cons.2 ⟨sub10_21, List.forall_mem_cons.2 ⟨sub10_22, List.forall_mem_cons.2 ⟨sub10_23, List.forall_mem_cons.2 ⟨sub10_24, List.forall_mem_cons.2 ⟨sub10_25, List.forall_mem_cons.2 ⟨sub10_26, List.forall_mem_cons.2 ⟨sub10_27, List.forall_mem_cons.2 ⟨sub10_28, List.forall_mem_cons.2 ⟨sub10_29, List.forall_mem_cons.2 ⟨sub10_30, List.forall_mem_cons.2 ⟨sub10_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_32 : sub10 [-3, -2, 2] = true := by decide +kernel
theorem sub10_33 : sub10 [-3, -2, 3] = true := by decide +kernel
theorem sub10_34 : sub10 [-3, -2, 4] = true := by decide +kernel
theorem sub10_35 : sub10 [-3, -2, 5] = true := by decide +kernel
theorem sub10_36 : sub10 [-3, -2, 6] = true := by decide +kernel
theorem sub10_37 : sub10 [-3, -1, -7] = true := by decide +kernel
theorem sub10_38 : sub10 [-3, -1, -6] = true := by decide +kernel
theorem sub10_39 : sub10 [-3, -1, -5] = true := by decide +kernel
theorem sub10_40 : sub10 [-3, -1, -4] = true := by decide +kernel
theorem sub10_41 : sub10 [-3, -1, -3] = true := by decide +kernel
theorem sub10_42 : sub10 [-3, -1, -2] = true := by decide +kernel
theorem sub10_43 : sub10 [-3, -1, -1] = true := by decide +kernel
theorem sub10_44 : sub10 [-3, -1, 0] = true := by decide +kernel
theorem sub10_45 : sub10 [-3, -1, 1] = true := by decide +kernel
theorem sub10_46 : sub10 [-3, -1, 2] = true := by decide +kernel
theorem sub10_47 : sub10 [-3, -1, 3] = true := by decide +kernel
theorem sub10_48 : sub10 [-3, -1, 4] = true := by decide +kernel
theorem sub10_49 : sub10 [-3, -1, 5] = true := by decide +kernel
theorem sub10_50 : sub10 [-3, -1, 6] = true := by decide +kernel
theorem sub10_51 : sub10 [-3, 0, -7] = true := by decide +kernel
theorem sub10_52 : sub10 [-3, 0, -6] = true := by decide +kernel
theorem sub10_53 : sub10 [-3, 0, -5] = true := by decide +kernel
theorem sub10_54 : sub10 [-3, 0, -4] = true := by decide +kernel
theorem sub10_55 : sub10 [-3, 0, -3] = true := by decide +kernel
theorem sub10_56 : sub10 [-3, 0, -2] = true := by decide +kernel
theorem sub10_57 : sub10 [-3, 0, -1] = true := by decide +kernel
theorem sub10_58 : sub10 [-3, 0, 0] = true := by decide +kernel
theorem sub10_59 : sub10 [-3, 0, 1] = true := by decide +kernel
theorem sub10_60 : sub10 [-3, 0, 2] = true := by decide +kernel
theorem sub10_61 : sub10 [-3, 0, 3] = true := by decide +kernel
theorem sub10_62 : sub10 [-3, 0, 4] = true := by decide +kernel
theorem sub10_63 : sub10 [-3, 0, 5] = true := by decide +kernel
theorem sb10_1 : ∀ q ∈ blk10_1, sub10 q = true := by
  unfold blk10_1
  exact List.forall_mem_cons.2 ⟨sub10_32, List.forall_mem_cons.2 ⟨sub10_33, List.forall_mem_cons.2 ⟨sub10_34, List.forall_mem_cons.2 ⟨sub10_35, List.forall_mem_cons.2 ⟨sub10_36, List.forall_mem_cons.2 ⟨sub10_37, List.forall_mem_cons.2 ⟨sub10_38, List.forall_mem_cons.2 ⟨sub10_39, List.forall_mem_cons.2 ⟨sub10_40, List.forall_mem_cons.2 ⟨sub10_41, List.forall_mem_cons.2 ⟨sub10_42, List.forall_mem_cons.2 ⟨sub10_43, List.forall_mem_cons.2 ⟨sub10_44, List.forall_mem_cons.2 ⟨sub10_45, List.forall_mem_cons.2 ⟨sub10_46, List.forall_mem_cons.2 ⟨sub10_47, List.forall_mem_cons.2 ⟨sub10_48, List.forall_mem_cons.2 ⟨sub10_49, List.forall_mem_cons.2 ⟨sub10_50, List.forall_mem_cons.2 ⟨sub10_51, List.forall_mem_cons.2 ⟨sub10_52, List.forall_mem_cons.2 ⟨sub10_53, List.forall_mem_cons.2 ⟨sub10_54, List.forall_mem_cons.2 ⟨sub10_55, List.forall_mem_cons.2 ⟨sub10_56, List.forall_mem_cons.2 ⟨sub10_57, List.forall_mem_cons.2 ⟨sub10_58, List.forall_mem_cons.2 ⟨sub10_59, List.forall_mem_cons.2 ⟨sub10_60, List.forall_mem_cons.2 ⟨sub10_61, List.forall_mem_cons.2 ⟨sub10_62, List.forall_mem_cons.2 ⟨sub10_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_64 : sub10 [-3, 0, 6] = true := by decide +kernel
theorem sub10_65 : sub10 [-3, 1, -6] = true := by decide +kernel
theorem sub10_66 : sub10 [-3, 1, -5] = true := by decide +kernel
theorem sub10_67 : sub10 [-3, 1, -4] = true := by decide +kernel
theorem sub10_68 : sub10 [-3, 1, -3] = true := by decide +kernel
theorem sub10_69 : sub10 [-3, 1, -2] = true := by decide +kernel
theorem sub10_70 : sub10 [-3, 1, -1] = true := by decide +kernel
theorem sub10_71 : sub10 [-3, 1, 0] = true := by decide +kernel
theorem sub10_72 : sub10 [-3, 1, 1] = true := by decide +kernel
theorem sub10_73 : sub10 [-3, 1, 2] = true := by decide +kernel
theorem sub10_74 : sub10 [-3, 1, 3] = true := by decide +kernel
theorem sub10_75 : sub10 [-3, 1, 4] = true := by decide +kernel
theorem sub10_76 : sub10 [-3, 1, 5] = true := by decide +kernel
theorem sub10_77 : sub10 [-3, 1, 6] = true := by decide +kernel
theorem sub10_78 : sub10 [-3, 2] = true := by decide +kernel
theorem sub10_79 : sub10 [-3, 3] = true := by decide +kernel
theorem sub10_80 : sub10 [-3, 4] = true := by decide +kernel
theorem sub10_81 : sub10 [-2, -6] = true := by decide +kernel
theorem sub10_82 : sub10 [-2, -5] = true := by decide +kernel
theorem sub10_83 : sub10 [-2, -4] = true := by decide +kernel
theorem sub10_84 : sub10 [-2, -3] = true := by decide +kernel
theorem sub10_85 : sub10 [-2, -2, -7] = true := by decide +kernel
theorem sub10_86 : sub10 [-2, -2, -6] = true := by decide +kernel
theorem sub10_87 : sub10 [-2, -2, -5] = true := by decide +kernel
theorem sub10_88 : sub10 [-2, -2, -4] = true := by decide +kernel
theorem sub10_89 : sub10 [-2, -2, -3] = true := by decide +kernel
theorem sub10_90 : sub10 [-2, -2, -2] = true := by decide +kernel
theorem sub10_91 : sub10 [-2, -2, -1] = true := by decide +kernel
theorem sub10_92 : sub10 [-2, -2, 0] = true := by decide +kernel
theorem sub10_93 : sub10 [-2, -2, 1] = true := by decide +kernel
theorem sub10_94 : sub10 [-2, -2, 2] = true := by decide +kernel
theorem sub10_95 : sub10 [-2, -2, 3] = true := by decide +kernel
theorem sb10_2 : ∀ q ∈ blk10_2, sub10 q = true := by
  unfold blk10_2
  exact List.forall_mem_cons.2 ⟨sub10_64, List.forall_mem_cons.2 ⟨sub10_65, List.forall_mem_cons.2 ⟨sub10_66, List.forall_mem_cons.2 ⟨sub10_67, List.forall_mem_cons.2 ⟨sub10_68, List.forall_mem_cons.2 ⟨sub10_69, List.forall_mem_cons.2 ⟨sub10_70, List.forall_mem_cons.2 ⟨sub10_71, List.forall_mem_cons.2 ⟨sub10_72, List.forall_mem_cons.2 ⟨sub10_73, List.forall_mem_cons.2 ⟨sub10_74, List.forall_mem_cons.2 ⟨sub10_75, List.forall_mem_cons.2 ⟨sub10_76, List.forall_mem_cons.2 ⟨sub10_77, List.forall_mem_cons.2 ⟨sub10_78, List.forall_mem_cons.2 ⟨sub10_79, List.forall_mem_cons.2 ⟨sub10_80, List.forall_mem_cons.2 ⟨sub10_81, List.forall_mem_cons.2 ⟨sub10_82, List.forall_mem_cons.2 ⟨sub10_83, List.forall_mem_cons.2 ⟨sub10_84, List.forall_mem_cons.2 ⟨sub10_85, List.forall_mem_cons.2 ⟨sub10_86, List.forall_mem_cons.2 ⟨sub10_87, List.forall_mem_cons.2 ⟨sub10_88, List.forall_mem_cons.2 ⟨sub10_89, List.forall_mem_cons.2 ⟨sub10_90, List.forall_mem_cons.2 ⟨sub10_91, List.forall_mem_cons.2 ⟨sub10_92, List.forall_mem_cons.2 ⟨sub10_93, List.forall_mem_cons.2 ⟨sub10_94, List.forall_mem_cons.2 ⟨sub10_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C105
