import ReflectZphi.Data.Cert5.C044.Base

namespace ReflectZphi.Data.Cert5.C044
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub5_672 : sub5 [2, -3, -1] = true := by decide +kernel
theorem sub5_673 : sub5 [2, -3, 0] = true := by decide +kernel
theorem sub5_674 : sub5 [2, -3, 1] = true := by decide +kernel
theorem sub5_675 : sub5 [2, -3, 2] = true := by decide +kernel
theorem sub5_676 : sub5 [2, -3, 3] = true := by decide +kernel
theorem sub5_677 : sub5 [2, -3, 4] = true := by decide +kernel
theorem sub5_678 : sub5 [2, -3, 5] = true := by decide +kernel
theorem sub5_679 : sub5 [2, -3, 6] = true := by decide +kernel
theorem sub5_680 : sub5 [2, -3, 7] = true := by decide +kernel
theorem sub5_681 : sub5 [2, -2, -7] = true := by decide +kernel
theorem sub5_682 : sub5 [2, -2, -6] = true := by decide +kernel
theorem sub5_683 : sub5 [2, -2, -5] = true := by decide +kernel
theorem sub5_684 : sub5 [2, -2, -4] = true := by decide +kernel
theorem sub5_685 : sub5 [2, -2, -3] = true := by decide +kernel
theorem sub5_686 : sub5 [2, -2, -2] = true := by decide +kernel
theorem sub5_687 : sub5 [2, -2, -1] = true := by decide +kernel
theorem sub5_688 : sub5 [2, -2, 0] = true := by decide +kernel
theorem sub5_689 : sub5 [2, -2, 1] = true := by decide +kernel
theorem sub5_690 : sub5 [2, -2, 2] = true := by decide +kernel
theorem sub5_691 : sub5 [2, -2, 3] = true := by decide +kernel
theorem sub5_692 : sub5 [2, -2, 4] = true := by decide +kernel
theorem sub5_693 : sub5 [2, -2, 5] = true := by decide +kernel
theorem sub5_694 : sub5 [2, -2, 6] = true := by decide +kernel
theorem sub5_695 : sub5 [2, -2, 7] = true := by decide +kernel
theorem sub5_696 : sub5 [2, -1, -7] = true := by decide +kernel
theorem sub5_697 : sub5 [2, -1, -6] = true := by decide +kernel
theorem sub5_698 : sub5 [2, -1, -5] = true := by decide +kernel
theorem sub5_699 : sub5 [2, -1, -4] = true := by decide +kernel
theorem sub5_700 : sub5 [2, -1, -3] = true := by decide +kernel
theorem sub5_701 : sub5 [2, -1, -2] = true := by decide +kernel
theorem sub5_702 : sub5 [2, -1, -1] = true := by decide +kernel
theorem sub5_703 : sub5 [2, -1, 0] = true := by decide +kernel
theorem sb5_21 : ∀ q ∈ blk5_21, sub5 q = true := by
  unfold blk5_21
  exact List.forall_mem_cons.2 ⟨sub5_672, List.forall_mem_cons.2 ⟨sub5_673, List.forall_mem_cons.2 ⟨sub5_674, List.forall_mem_cons.2 ⟨sub5_675, List.forall_mem_cons.2 ⟨sub5_676, List.forall_mem_cons.2 ⟨sub5_677, List.forall_mem_cons.2 ⟨sub5_678, List.forall_mem_cons.2 ⟨sub5_679, List.forall_mem_cons.2 ⟨sub5_680, List.forall_mem_cons.2 ⟨sub5_681, List.forall_mem_cons.2 ⟨sub5_682, List.forall_mem_cons.2 ⟨sub5_683, List.forall_mem_cons.2 ⟨sub5_684, List.forall_mem_cons.2 ⟨sub5_685, List.forall_mem_cons.2 ⟨sub5_686, List.forall_mem_cons.2 ⟨sub5_687, List.forall_mem_cons.2 ⟨sub5_688, List.forall_mem_cons.2 ⟨sub5_689, List.forall_mem_cons.2 ⟨sub5_690, List.forall_mem_cons.2 ⟨sub5_691, List.forall_mem_cons.2 ⟨sub5_692, List.forall_mem_cons.2 ⟨sub5_693, List.forall_mem_cons.2 ⟨sub5_694, List.forall_mem_cons.2 ⟨sub5_695, List.forall_mem_cons.2 ⟨sub5_696, List.forall_mem_cons.2 ⟨sub5_697, List.forall_mem_cons.2 ⟨sub5_698, List.forall_mem_cons.2 ⟨sub5_699, List.forall_mem_cons.2 ⟨sub5_700, List.forall_mem_cons.2 ⟨sub5_701, List.forall_mem_cons.2 ⟨sub5_702, List.forall_mem_cons.2 ⟨sub5_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_704 : sub5 [2, -1, 1] = true := by decide +kernel
theorem sub5_705 : sub5 [2, -1, 2] = true := by decide +kernel
theorem sub5_706 : sub5 [2, -1, 3] = true := by decide +kernel
theorem sub5_707 : sub5 [2, -1, 4] = true := by decide +kernel
theorem sub5_708 : sub5 [2, -1, 5] = true := by decide +kernel
theorem sub5_709 : sub5 [2, -1, 6] = true := by decide +kernel
theorem sub5_710 : sub5 [2, -1, 7] = true := by decide +kernel
theorem sub5_711 : sub5 [2, 0, -8] = true := by decide +kernel
theorem sub5_712 : sub5 [2, 0, -7] = true := by decide +kernel
theorem sub5_713 : sub5 [2, 0, -6] = true := by decide +kernel
theorem sub5_714 : sub5 [2, 0, -5] = true := by decide +kernel
theorem sub5_715 : sub5 [2, 0, -4] = true := by decide +kernel
theorem sub5_716 : sub5 [2, 0, -3] = true := by decide +kernel
theorem sub5_717 : sub5 [2, 0, -2] = true := by decide +kernel
theorem sub5_718 : sub5 [2, 0, -1] = true := by decide +kernel
theorem sub5_719 : sub5 [2, 0, 0] = true := by decide +kernel
theorem sub5_720 : sub5 [2, 0, 1] = true := by decide +kernel
theorem sub5_721 : sub5 [2, 0, 2] = true := by decide +kernel
theorem sub5_722 : sub5 [2, 0, 3] = true := by decide +kernel
theorem sub5_723 : sub5 [2, 0, 4] = true := by decide +kernel
theorem sub5_724 : sub5 [2, 0, 5] = true := by decide +kernel
theorem sub5_725 : sub5 [2, 0, 6] = true := by decide +kernel
theorem sub5_726 : sub5 [2, 1, -8] = true := by decide +kernel
theorem sub5_727 : sub5 [2, 1, -7] = true := by decide +kernel
theorem sub5_728 : sub5 [2, 1, -6] = true := by decide +kernel
theorem sub5_729 : sub5 [2, 1, -5] = true := by decide +kernel
theorem sub5_730 : sub5 [2, 1, -4] = true := by decide +kernel
theorem sub5_731 : sub5 [2, 1, -3] = true := by decide +kernel
theorem sub5_732 : sub5 [2, 1, -2] = true := by decide +kernel
theorem sub5_733 : sub5 [2, 1, -1] = true := by decide +kernel
theorem sub5_734 : sub5 [2, 1, 0] = true := by decide +kernel
theorem sub5_735 : sub5 [2, 1, 1] = true := by decide +kernel
theorem sb5_22 : ∀ q ∈ blk5_22, sub5 q = true := by
  unfold blk5_22
  exact List.forall_mem_cons.2 ⟨sub5_704, List.forall_mem_cons.2 ⟨sub5_705, List.forall_mem_cons.2 ⟨sub5_706, List.forall_mem_cons.2 ⟨sub5_707, List.forall_mem_cons.2 ⟨sub5_708, List.forall_mem_cons.2 ⟨sub5_709, List.forall_mem_cons.2 ⟨sub5_710, List.forall_mem_cons.2 ⟨sub5_711, List.forall_mem_cons.2 ⟨sub5_712, List.forall_mem_cons.2 ⟨sub5_713, List.forall_mem_cons.2 ⟨sub5_714, List.forall_mem_cons.2 ⟨sub5_715, List.forall_mem_cons.2 ⟨sub5_716, List.forall_mem_cons.2 ⟨sub5_717, List.forall_mem_cons.2 ⟨sub5_718, List.forall_mem_cons.2 ⟨sub5_719, List.forall_mem_cons.2 ⟨sub5_720, List.forall_mem_cons.2 ⟨sub5_721, List.forall_mem_cons.2 ⟨sub5_722, List.forall_mem_cons.2 ⟨sub5_723, List.forall_mem_cons.2 ⟨sub5_724, List.forall_mem_cons.2 ⟨sub5_725, List.forall_mem_cons.2 ⟨sub5_726, List.forall_mem_cons.2 ⟨sub5_727, List.forall_mem_cons.2 ⟨sub5_728, List.forall_mem_cons.2 ⟨sub5_729, List.forall_mem_cons.2 ⟨sub5_730, List.forall_mem_cons.2 ⟨sub5_731, List.forall_mem_cons.2 ⟨sub5_732, List.forall_mem_cons.2 ⟨sub5_733, List.forall_mem_cons.2 ⟨sub5_734, List.forall_mem_cons.2 ⟨sub5_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_736 : sub5 [2, 1, 2] = true := by decide +kernel
theorem sub5_737 : sub5 [2, 1, 3] = true := by decide +kernel
theorem sub5_738 : sub5 [2, 1, 4] = true := by decide +kernel
theorem sub5_739 : sub5 [2, 1, 5] = true := by decide +kernel
theorem sub5_740 : sub5 [2, 1, 6] = true := by decide +kernel
theorem sub5_741 : sub5 [2, 2, -8] = true := by decide +kernel
theorem sub5_742 : sub5 [2, 2, -7] = true := by decide +kernel
theorem sub5_743 : sub5 [2, 2, -6] = true := by decide +kernel
theorem sub5_744 : sub5 [2, 2, -5] = true := by decide +kernel
theorem sub5_745 : sub5 [2, 2, -4] = true := by decide +kernel
theorem sub5_746 : sub5 [2, 2, -3] = true := by decide +kernel
theorem sub5_747 : sub5 [2, 2, -2] = true := by decide +kernel
theorem sub5_748 : sub5 [2, 2, -1] = true := by decide +kernel
theorem sub5_749 : sub5 [2, 2, 0] = true := by decide +kernel
theorem sub5_750 : sub5 [2, 2, 1] = true := by decide +kernel
theorem sub5_751 : sub5 [2, 2, 2] = true := by decide +kernel
theorem sub5_752 : sub5 [2, 2, 3] = true := by decide +kernel
theorem sub5_753 : sub5 [2, 2, 4] = true := by decide +kernel
theorem sub5_754 : sub5 [2, 2, 5] = true := by decide +kernel
theorem sub5_755 : sub5 [2, 3, -8] = true := by decide +kernel
theorem sub5_756 : sub5 [2, 3, -7] = true := by decide +kernel
theorem sub5_757 : sub5 [2, 3, -6] = true := by decide +kernel
theorem sub5_758 : sub5 [2, 3, -5] = true := by decide +kernel
theorem sub5_759 : sub5 [2, 3, -4] = true := by decide +kernel
theorem sub5_760 : sub5 [2, 3, -3] = true := by decide +kernel
theorem sub5_761 : sub5 [2, 3, -2] = true := by decide +kernel
theorem sub5_762 : sub5 [2, 3, -1] = true := by decide +kernel
theorem sub5_763 : sub5 [2, 3, 0] = true := by decide +kernel
theorem sub5_764 : sub5 [2, 3, 1] = true := by decide +kernel
theorem sub5_765 : sub5 [2, 3, 2] = true := by decide +kernel
theorem sub5_766 : sub5 [2, 3, 3] = true := by decide +kernel
theorem sub5_767 : sub5 [2, 3, 4] = true := by decide +kernel
theorem sb5_23 : ∀ q ∈ blk5_23, sub5 q = true := by
  unfold blk5_23
  exact List.forall_mem_cons.2 ⟨sub5_736, List.forall_mem_cons.2 ⟨sub5_737, List.forall_mem_cons.2 ⟨sub5_738, List.forall_mem_cons.2 ⟨sub5_739, List.forall_mem_cons.2 ⟨sub5_740, List.forall_mem_cons.2 ⟨sub5_741, List.forall_mem_cons.2 ⟨sub5_742, List.forall_mem_cons.2 ⟨sub5_743, List.forall_mem_cons.2 ⟨sub5_744, List.forall_mem_cons.2 ⟨sub5_745, List.forall_mem_cons.2 ⟨sub5_746, List.forall_mem_cons.2 ⟨sub5_747, List.forall_mem_cons.2 ⟨sub5_748, List.forall_mem_cons.2 ⟨sub5_749, List.forall_mem_cons.2 ⟨sub5_750, List.forall_mem_cons.2 ⟨sub5_751, List.forall_mem_cons.2 ⟨sub5_752, List.forall_mem_cons.2 ⟨sub5_753, List.forall_mem_cons.2 ⟨sub5_754, List.forall_mem_cons.2 ⟨sub5_755, List.forall_mem_cons.2 ⟨sub5_756, List.forall_mem_cons.2 ⟨sub5_757, List.forall_mem_cons.2 ⟨sub5_758, List.forall_mem_cons.2 ⟨sub5_759, List.forall_mem_cons.2 ⟨sub5_760, List.forall_mem_cons.2 ⟨sub5_761, List.forall_mem_cons.2 ⟨sub5_762, List.forall_mem_cons.2 ⟨sub5_763, List.forall_mem_cons.2 ⟨sub5_764, List.forall_mem_cons.2 ⟨sub5_765, List.forall_mem_cons.2 ⟨sub5_766, List.forall_mem_cons.2 ⟨sub5_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_768 : sub5 [2, 4] = true := by decide +kernel
theorem sub5_769 : sub5 [2, 5] = true := by decide +kernel
theorem sub5_770 : sub5 [2, 6] = true := by decide +kernel
theorem sub5_771 : sub5 [2, 7] = true := by decide +kernel
theorem sub5_772 : sub5 [3, -9] = true := by decide +kernel
theorem sub5_773 : sub5 [3, -8] = true := by decide +kernel
theorem sub5_774 : sub5 [3, -7] = true := by decide +kernel
theorem sub5_775 : sub5 [3, -6] = true := by decide +kernel
theorem sub5_776 : sub5 [3, -5] = true := by decide +kernel
theorem sub5_777 : sub5 [3, -4] = true := by decide +kernel
theorem sub5_778 : sub5 [3, -3, -6] = true := by decide +kernel
theorem sub5_779 : sub5 [3, -3, -5] = true := by decide +kernel
theorem sub5_780 : sub5 [3, -3, -4] = true := by decide +kernel
theorem sub5_781 : sub5 [3, -3, -3] = true := by decide +kernel
theorem sub5_782 : sub5 [3, -3, -2] = true := by decide +kernel
theorem sub5_783 : sub5 [3, -3, -1] = true := by decide +kernel
theorem sub5_784 : sub5 [3, -3, 0] = true := by decide +kernel
theorem sub5_785 : sub5 [3, -3, 1] = true := by decide +kernel
theorem sub5_786 : sub5 [3, -3, 2] = true := by decide +kernel
theorem sub5_787 : sub5 [3, -3, 3] = true := by decide +kernel
theorem sub5_788 : sub5 [3, -3, 4] = true := by decide +kernel
theorem sub5_789 : sub5 [3, -3, 5] = true := by decide +kernel
theorem sub5_790 : sub5 [3, -3, 6] = true := by decide +kernel
theorem sub5_791 : sub5 [3, -3, 7] = true := by decide +kernel
theorem sub5_792 : sub5 [3, -2, -6] = true := by decide +kernel
theorem sub5_793 : sub5 [3, -2, -5] = true := by decide +kernel
theorem sub5_794 : sub5 [3, -2, -4] = true := by decide +kernel
theorem sub5_795 : sub5 [3, -2, -3] = true := by decide +kernel
theorem sub5_796 : sub5 [3, -2, -2] = true := by decide +kernel
theorem sub5_797 : sub5 [3, -2, -1] = true := by decide +kernel
theorem sub5_798 : sub5 [3, -2, 0] = true := by decide +kernel
theorem sub5_799 : sub5 [3, -2, 1] = true := by decide +kernel
theorem sb5_24 : ∀ q ∈ blk5_24, sub5 q = true := by
  unfold blk5_24
  exact List.forall_mem_cons.2 ⟨sub5_768, List.forall_mem_cons.2 ⟨sub5_769, List.forall_mem_cons.2 ⟨sub5_770, List.forall_mem_cons.2 ⟨sub5_771, List.forall_mem_cons.2 ⟨sub5_772, List.forall_mem_cons.2 ⟨sub5_773, List.forall_mem_cons.2 ⟨sub5_774, List.forall_mem_cons.2 ⟨sub5_775, List.forall_mem_cons.2 ⟨sub5_776, List.forall_mem_cons.2 ⟨sub5_777, List.forall_mem_cons.2 ⟨sub5_778, List.forall_mem_cons.2 ⟨sub5_779, List.forall_mem_cons.2 ⟨sub5_780, List.forall_mem_cons.2 ⟨sub5_781, List.forall_mem_cons.2 ⟨sub5_782, List.forall_mem_cons.2 ⟨sub5_783, List.forall_mem_cons.2 ⟨sub5_784, List.forall_mem_cons.2 ⟨sub5_785, List.forall_mem_cons.2 ⟨sub5_786, List.forall_mem_cons.2 ⟨sub5_787, List.forall_mem_cons.2 ⟨sub5_788, List.forall_mem_cons.2 ⟨sub5_789, List.forall_mem_cons.2 ⟨sub5_790, List.forall_mem_cons.2 ⟨sub5_791, List.forall_mem_cons.2 ⟨sub5_792, List.forall_mem_cons.2 ⟨sub5_793, List.forall_mem_cons.2 ⟨sub5_794, List.forall_mem_cons.2 ⟨sub5_795, List.forall_mem_cons.2 ⟨sub5_796, List.forall_mem_cons.2 ⟨sub5_797, List.forall_mem_cons.2 ⟨sub5_798, List.forall_mem_cons.2 ⟨sub5_799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_800 : sub5 [3, -2, 2] = true := by decide +kernel
theorem sub5_801 : sub5 [3, -2, 3] = true := by decide +kernel
theorem sub5_802 : sub5 [3, -2, 4] = true := by decide +kernel
theorem sub5_803 : sub5 [3, -2, 5] = true := by decide +kernel
theorem sub5_804 : sub5 [3, -2, 6] = true := by decide +kernel
theorem sub5_805 : sub5 [3, -2, 7] = true := by decide +kernel
theorem sub5_806 : sub5 [3, -1, -7] = true := by decide +kernel
theorem sub5_807 : sub5 [3, -1, -6] = true := by decide +kernel
theorem sub5_808 : sub5 [3, -1, -5] = true := by decide +kernel
theorem sub5_809 : sub5 [3, -1, -4] = true := by decide +kernel
theorem sub5_810 : sub5 [3, -1, -3] = true := by decide +kernel
theorem sub5_811 : sub5 [3, -1, -2] = true := by decide +kernel
theorem sub5_812 : sub5 [3, -1, -1] = true := by decide +kernel
theorem sub5_813 : sub5 [3, -1, 0] = true := by decide +kernel
theorem sub5_814 : sub5 [3, -1, 1] = true := by decide +kernel
theorem sub5_815 : sub5 [3, -1, 2] = true := by decide +kernel
theorem sub5_816 : sub5 [3, -1, 3] = true := by decide +kernel
theorem sub5_817 : sub5 [3, -1, 4] = true := by decide +kernel
theorem sub5_818 : sub5 [3, -1, 5] = true := by decide +kernel
theorem sub5_819 : sub5 [3, -1, 6] = true := by decide +kernel
theorem sub5_820 : sub5 [3, 0, -7] = true := by decide +kernel
theorem sub5_821 : sub5 [3, 0, -6] = true := by decide +kernel
theorem sub5_822 : sub5 [3, 0, -5] = true := by decide +kernel
theorem sub5_823 : sub5 [3, 0, -4] = true := by decide +kernel
theorem sub5_824 : sub5 [3, 0, -3] = true := by decide +kernel
theorem sub5_825 : sub5 [3, 0, -2] = true := by decide +kernel
theorem sub5_826 : sub5 [3, 0, -1] = true := by decide +kernel
theorem sub5_827 : sub5 [3, 0, 0] = true := by decide +kernel
theorem sub5_828 : sub5 [3, 0, 1] = true := by decide +kernel
theorem sub5_829 : sub5 [3, 0, 2] = true := by decide +kernel
theorem sub5_830 : sub5 [3, 0, 3] = true := by decide +kernel
theorem sub5_831 : sub5 [3, 0, 4] = true := by decide +kernel
theorem sb5_25 : ∀ q ∈ blk5_25, sub5 q = true := by
  unfold blk5_25
  exact List.forall_mem_cons.2 ⟨sub5_800, List.forall_mem_cons.2 ⟨sub5_801, List.forall_mem_cons.2 ⟨sub5_802, List.forall_mem_cons.2 ⟨sub5_803, List.forall_mem_cons.2 ⟨sub5_804, List.forall_mem_cons.2 ⟨sub5_805, List.forall_mem_cons.2 ⟨sub5_806, List.forall_mem_cons.2 ⟨sub5_807, List.forall_mem_cons.2 ⟨sub5_808, List.forall_mem_cons.2 ⟨sub5_809, List.forall_mem_cons.2 ⟨sub5_810, List.forall_mem_cons.2 ⟨sub5_811, List.forall_mem_cons.2 ⟨sub5_812, List.forall_mem_cons.2 ⟨sub5_813, List.forall_mem_cons.2 ⟨sub5_814, List.forall_mem_cons.2 ⟨sub5_815, List.forall_mem_cons.2 ⟨sub5_816, List.forall_mem_cons.2 ⟨sub5_817, List.forall_mem_cons.2 ⟨sub5_818, List.forall_mem_cons.2 ⟨sub5_819, List.forall_mem_cons.2 ⟨sub5_820, List.forall_mem_cons.2 ⟨sub5_821, List.forall_mem_cons.2 ⟨sub5_822, List.forall_mem_cons.2 ⟨sub5_823, List.forall_mem_cons.2 ⟨sub5_824, List.forall_mem_cons.2 ⟨sub5_825, List.forall_mem_cons.2 ⟨sub5_826, List.forall_mem_cons.2 ⟨sub5_827, List.forall_mem_cons.2 ⟨sub5_828, List.forall_mem_cons.2 ⟨sub5_829, List.forall_mem_cons.2 ⟨sub5_830, List.forall_mem_cons.2 ⟨sub5_831, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_832 : sub5 [3, 0, 5] = true := by decide +kernel
theorem sub5_833 : sub5 [3, 0, 6] = true := by decide +kernel
theorem sub5_834 : sub5 [3, 1, -8] = true := by decide +kernel
theorem sub5_835 : sub5 [3, 1, -7] = true := by decide +kernel
theorem sub5_836 : sub5 [3, 1, -6] = true := by decide +kernel
theorem sub5_837 : sub5 [3, 1, -5] = true := by decide +kernel
theorem sub5_838 : sub5 [3, 1, -4] = true := by decide +kernel
theorem sub5_839 : sub5 [3, 1, -3] = true := by decide +kernel
theorem sub5_840 : sub5 [3, 1, -2] = true := by decide +kernel
theorem sub5_841 : sub5 [3, 1, -1] = true := by decide +kernel
theorem sub5_842 : sub5 [3, 1, 0] = true := by decide +kernel
theorem sub5_843 : sub5 [3, 1, 1] = true := by decide +kernel
theorem sub5_844 : sub5 [3, 1, 2] = true := by decide +kernel
theorem sub5_845 : sub5 [3, 1, 3] = true := by decide +kernel
theorem sub5_846 : sub5 [3, 1, 4] = true := by decide +kernel
theorem sub5_847 : sub5 [3, 1, 5] = true := by decide +kernel
theorem sub5_848 : sub5 [3, 2] = true := by decide +kernel
theorem sub5_849 : sub5 [3, 3] = true := by decide +kernel
theorem sub5_850 : sub5 [3, 4] = true := by decide +kernel
theorem sub5_851 : sub5 [3, 5] = true := by decide +kernel
theorem sub5_852 : sub5 [3, 6] = true := by decide +kernel
theorem sub5_853 : sub5 [4, -9] = true := by decide +kernel
theorem sub5_854 : sub5 [4, -8] = true := by decide +kernel
theorem sub5_855 : sub5 [4, -7] = true := by decide +kernel
theorem sub5_856 : sub5 [4, -6] = true := by decide +kernel
theorem sub5_857 : sub5 [4, -5] = true := by decide +kernel
theorem sub5_858 : sub5 [4, -4] = true := by decide +kernel
theorem sub5_859 : sub5 [4, -3] = true := by decide +kernel
theorem sub5_860 : sub5 [4, -2] = true := by decide +kernel
theorem sub5_861 : sub5 [4, -1] = true := by decide +kernel
theorem sub5_862 : sub5 [4, 0] = true := by decide +kernel
theorem sub5_863 : sub5 [4, 1] = true := by decide +kernel
theorem sb5_26 : ∀ q ∈ blk5_26, sub5 q = true := by
  unfold blk5_26
  exact List.forall_mem_cons.2 ⟨sub5_832, List.forall_mem_cons.2 ⟨sub5_833, List.forall_mem_cons.2 ⟨sub5_834, List.forall_mem_cons.2 ⟨sub5_835, List.forall_mem_cons.2 ⟨sub5_836, List.forall_mem_cons.2 ⟨sub5_837, List.forall_mem_cons.2 ⟨sub5_838, List.forall_mem_cons.2 ⟨sub5_839, List.forall_mem_cons.2 ⟨sub5_840, List.forall_mem_cons.2 ⟨sub5_841, List.forall_mem_cons.2 ⟨sub5_842, List.forall_mem_cons.2 ⟨sub5_843, List.forall_mem_cons.2 ⟨sub5_844, List.forall_mem_cons.2 ⟨sub5_845, List.forall_mem_cons.2 ⟨sub5_846, List.forall_mem_cons.2 ⟨sub5_847, List.forall_mem_cons.2 ⟨sub5_848, List.forall_mem_cons.2 ⟨sub5_849, List.forall_mem_cons.2 ⟨sub5_850, List.forall_mem_cons.2 ⟨sub5_851, List.forall_mem_cons.2 ⟨sub5_852, List.forall_mem_cons.2 ⟨sub5_853, List.forall_mem_cons.2 ⟨sub5_854, List.forall_mem_cons.2 ⟨sub5_855, List.forall_mem_cons.2 ⟨sub5_856, List.forall_mem_cons.2 ⟨sub5_857, List.forall_mem_cons.2 ⟨sub5_858, List.forall_mem_cons.2 ⟨sub5_859, List.forall_mem_cons.2 ⟨sub5_860, List.forall_mem_cons.2 ⟨sub5_861, List.forall_mem_cons.2 ⟨sub5_862, List.forall_mem_cons.2 ⟨sub5_863, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_864 : sub5 [4, 2] = true := by decide +kernel
theorem sub5_865 : sub5 [4, 3] = true := by decide +kernel
theorem sub5_866 : sub5 [4, 4] = true := by decide +kernel
theorem sub5_867 : sub5 [4, 5] = true := by decide +kernel
theorem sub5_868 : sub5 [5, -9] = true := by decide +kernel
theorem sub5_869 : sub5 [5, -8] = true := by decide +kernel
theorem sub5_870 : sub5 [5, -7] = true := by decide +kernel
theorem sub5_871 : sub5 [5, -6] = true := by decide +kernel
theorem sub5_872 : sub5 [5, -5] = true := by decide +kernel
theorem sub5_873 : sub5 [5, -4] = true := by decide +kernel
theorem sub5_874 : sub5 [5, -3] = true := by decide +kernel
theorem sub5_875 : sub5 [5, -2] = true := by decide +kernel
theorem sub5_876 : sub5 [5, -1] = true := by decide +kernel
theorem sub5_877 : sub5 [5, 0] = true := by decide +kernel
theorem sub5_878 : sub5 [5, 1] = true := by decide +kernel
theorem sub5_879 : sub5 [5, 2] = true := by decide +kernel
theorem sub5_880 : sub5 [5, 3] = true := by decide +kernel
theorem sub5_881 : sub5 [5, 4] = true := by decide +kernel
theorem sub5_882 : sub5 [6, -8] = true := by decide +kernel
theorem sub5_883 : sub5 [6, -7] = true := by decide +kernel
theorem sub5_884 : sub5 [6, -6] = true := by decide +kernel
theorem sub5_885 : sub5 [6, -5] = true := by decide +kernel
theorem sub5_886 : sub5 [6, -4] = true := by decide +kernel
theorem sub5_887 : sub5 [6, -3] = true := by decide +kernel
theorem sub5_888 : sub5 [6, -2] = true := by decide +kernel
theorem sub5_889 : sub5 [6, -1] = true := by decide +kernel
theorem sub5_890 : sub5 [6, 0] = true := by decide +kernel
theorem sub5_891 : sub5 [6, 1] = true := by decide +kernel
theorem sub5_892 : sub5 [6, 2] = true := by decide +kernel
theorem sub5_893 : sub5 [6, 3] = true := by decide +kernel
theorem sub5_894 : sub5 [7, -6] = true := by decide +kernel
theorem sub5_895 : sub5 [7, -5] = true := by decide +kernel
theorem sb5_27 : ∀ q ∈ blk5_27, sub5 q = true := by
  unfold blk5_27
  exact List.forall_mem_cons.2 ⟨sub5_864, List.forall_mem_cons.2 ⟨sub5_865, List.forall_mem_cons.2 ⟨sub5_866, List.forall_mem_cons.2 ⟨sub5_867, List.forall_mem_cons.2 ⟨sub5_868, List.forall_mem_cons.2 ⟨sub5_869, List.forall_mem_cons.2 ⟨sub5_870, List.forall_mem_cons.2 ⟨sub5_871, List.forall_mem_cons.2 ⟨sub5_872, List.forall_mem_cons.2 ⟨sub5_873, List.forall_mem_cons.2 ⟨sub5_874, List.forall_mem_cons.2 ⟨sub5_875, List.forall_mem_cons.2 ⟨sub5_876, List.forall_mem_cons.2 ⟨sub5_877, List.forall_mem_cons.2 ⟨sub5_878, List.forall_mem_cons.2 ⟨sub5_879, List.forall_mem_cons.2 ⟨sub5_880, List.forall_mem_cons.2 ⟨sub5_881, List.forall_mem_cons.2 ⟨sub5_882, List.forall_mem_cons.2 ⟨sub5_883, List.forall_mem_cons.2 ⟨sub5_884, List.forall_mem_cons.2 ⟨sub5_885, List.forall_mem_cons.2 ⟨sub5_886, List.forall_mem_cons.2 ⟨sub5_887, List.forall_mem_cons.2 ⟨sub5_888, List.forall_mem_cons.2 ⟨sub5_889, List.forall_mem_cons.2 ⟨sub5_890, List.forall_mem_cons.2 ⟨sub5_891, List.forall_mem_cons.2 ⟨sub5_892, List.forall_mem_cons.2 ⟨sub5_893, List.forall_mem_cons.2 ⟨sub5_894, List.forall_mem_cons.2 ⟨sub5_895, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_896 : sub5 [7, -4] = true := by decide +kernel
theorem sub5_897 : sub5 [7, -3] = true := by decide +kernel
theorem sub5_898 : sub5 [7, -2] = true := by decide +kernel
theorem sub5_899 : sub5 [7, -1] = true := by decide +kernel
theorem sub5_900 : sub5 [7, 0] = true := by decide +kernel
theorem sb5_28 : ∀ q ∈ blk5_28, sub5 q = true := by
  unfold blk5_28
  exact List.forall_mem_cons.2 ⟨sub5_896, List.forall_mem_cons.2 ⟨sub5_897, List.forall_mem_cons.2 ⟨sub5_898, List.forall_mem_cons.2 ⟨sub5_899, List.forall_mem_cons.2 ⟨sub5_900, List.forall_mem_nil _⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C044
