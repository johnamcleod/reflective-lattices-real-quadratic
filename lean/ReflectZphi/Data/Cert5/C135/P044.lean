import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_1_736 : subd9_1 [1, 3, -8] = true := by decide +kernel
theorem subd9_1_737 : subd9_1 [1, 3, -7] = true := by decide +kernel
theorem subd9_1_738 : subd9_1 [1, 3, -6] = true := by decide +kernel
theorem subd9_1_739 : subd9_1 [1, 3, -5] = true := by decide +kernel
theorem subd9_1_740 : subd9_1 [1, 3, -4] = true := by decide +kernel
theorem subd9_1_741 : subd9_1 [1, 3, -3] = true := by decide +kernel
theorem subd9_1_742 : subd9_1 [1, 3, -2] = true := by decide +kernel
theorem subd9_1_743 : subd9_1 [1, 3, -1] = true := by decide +kernel
theorem subd9_1_744 : subd9_1 [1, 3, 0] = true := by decide +kernel
theorem subd9_1_745 : subd9_1 [1, 3, 1] = true := by decide +kernel
theorem subd9_1_746 : subd9_1 [1, 3, 2] = true := by decide +kernel
theorem subd9_1_747 : subd9_1 [1, 3, 3] = true := by decide +kernel
theorem subd9_1_748 : subd9_1 [1, 3, 4] = true := by decide +kernel
theorem subd9_1_749 : subd9_1 [1, 3, 5] = true := by decide +kernel
theorem subd9_1_750 : subd9_1 [1, 3, 6] = true := by decide +kernel
theorem subd9_1_751 : subd9_1 [1, 4, -9] = true := by decide +kernel
theorem subd9_1_752 : subd9_1 [1, 4, -8] = true := by decide +kernel
theorem subd9_1_753 : subd9_1 [1, 4, -7] = true := by decide +kernel
theorem subd9_1_754 : subd9_1 [1, 4, -6] = true := by decide +kernel
theorem subd9_1_755 : subd9_1 [1, 4, -5] = true := by decide +kernel
theorem subd9_1_756 : subd9_1 [1, 4, -4] = true := by decide +kernel
theorem subd9_1_757 : subd9_1 [1, 4, -3] = true := by decide +kernel
theorem subd9_1_758 : subd9_1 [1, 4, -2] = true := by decide +kernel
theorem subd9_1_759 : subd9_1 [1, 4, -1] = true := by decide +kernel
theorem subd9_1_760 : subd9_1 [1, 4, 0] = true := by decide +kernel
theorem subd9_1_761 : subd9_1 [1, 4, 1] = true := by decide +kernel
theorem subd9_1_762 : subd9_1 [1, 4, 2] = true := by decide +kernel
theorem subd9_1_763 : subd9_1 [1, 4, 3] = true := by decide +kernel
theorem subd9_1_764 : subd9_1 [1, 4, 4] = true := by decide +kernel
theorem subd9_1_765 : subd9_1 [1, 4, 5] = true := by decide +kernel
theorem subd9_1_766 : subd9_1 [1, 5] = true := by decide +kernel
theorem subd9_1_767 : subd9_1 [1, 6] = true := by decide +kernel
theorem sbd9_1_23 : ∀ q ∈ blkd9_1_23, subd9_1 q = true := by
  unfold blkd9_1_23
  exact List.forall_mem_cons.2 ⟨subd9_1_736, List.forall_mem_cons.2 ⟨subd9_1_737, List.forall_mem_cons.2 ⟨subd9_1_738, List.forall_mem_cons.2 ⟨subd9_1_739, List.forall_mem_cons.2 ⟨subd9_1_740, List.forall_mem_cons.2 ⟨subd9_1_741, List.forall_mem_cons.2 ⟨subd9_1_742, List.forall_mem_cons.2 ⟨subd9_1_743, List.forall_mem_cons.2 ⟨subd9_1_744, List.forall_mem_cons.2 ⟨subd9_1_745, List.forall_mem_cons.2 ⟨subd9_1_746, List.forall_mem_cons.2 ⟨subd9_1_747, List.forall_mem_cons.2 ⟨subd9_1_748, List.forall_mem_cons.2 ⟨subd9_1_749, List.forall_mem_cons.2 ⟨subd9_1_750, List.forall_mem_cons.2 ⟨subd9_1_751, List.forall_mem_cons.2 ⟨subd9_1_752, List.forall_mem_cons.2 ⟨subd9_1_753, List.forall_mem_cons.2 ⟨subd9_1_754, List.forall_mem_cons.2 ⟨subd9_1_755, List.forall_mem_cons.2 ⟨subd9_1_756, List.forall_mem_cons.2 ⟨subd9_1_757, List.forall_mem_cons.2 ⟨subd9_1_758, List.forall_mem_cons.2 ⟨subd9_1_759, List.forall_mem_cons.2 ⟨subd9_1_760, List.forall_mem_cons.2 ⟨subd9_1_761, List.forall_mem_cons.2 ⟨subd9_1_762, List.forall_mem_cons.2 ⟨subd9_1_763, List.forall_mem_cons.2 ⟨subd9_1_764, List.forall_mem_cons.2 ⟨subd9_1_765, List.forall_mem_cons.2 ⟨subd9_1_766, List.forall_mem_cons.2 ⟨subd9_1_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_768 : subd9_1 [2, -6] = true := by decide +kernel
theorem subd9_1_769 : subd9_1 [2, -5] = true := by decide +kernel
theorem subd9_1_770 : subd9_1 [2, -4] = true := by decide +kernel
theorem subd9_1_771 : subd9_1 [2, -3, -7] = true := by decide +kernel
theorem subd9_1_772 : subd9_1 [2, -3, -6] = true := by decide +kernel
theorem subd9_1_773 : subd9_1 [2, -3, -5] = true := by decide +kernel
theorem subd9_1_774 : subd9_1 [2, -3, -4] = true := by decide +kernel
theorem subd9_1_775 : subd9_1 [2, -3, -3] = true := by decide +kernel
theorem subd9_1_776 : subd9_1 [2, -3, -2] = true := by decide +kernel
theorem subd9_1_777 : subd9_1 [2, -3, -1] = true := by decide +kernel
theorem subd9_1_778 : subd9_1 [2, -3, 0] = true := by decide +kernel
theorem subd9_1_779 : subd9_1 [2, -3, 1] = true := by decide +kernel
theorem subd9_1_780 : subd9_1 [2, -3, 2] = true := by decide +kernel
theorem subd9_1_781 : subd9_1 [2, -3, 3] = true := by decide +kernel
theorem subd9_1_782 : subd9_1 [2, -3, 4] = true := by decide +kernel
theorem subd9_1_783 : subd9_1 [2, -3, 5] = true := by decide +kernel
theorem subd9_1_784 : subd9_1 [2, -3, 6] = true := by decide +kernel
theorem subd9_1_785 : subd9_1 [2, -3, 7] = true := by decide +kernel
theorem subd9_1_786 : subd9_1 [2, -2, -8] = true := by decide +kernel
theorem subd9_1_787 : subd9_1 [2, -2, -7] = true := by decide +kernel
theorem subd9_1_788 : subd9_1 [2, -2, -6] = true := by decide +kernel
theorem subd9_1_789 : subd9_1 [2, -2, -5] = true := by decide +kernel
theorem subd9_1_790 : subd9_1 [2, -2, -4] = true := by decide +kernel
theorem subd9_1_791 : subd9_1 [2, -2, -3] = true := by decide +kernel
theorem subd9_1_792 : subd9_1 [2, -2, -2] = true := by decide +kernel
theorem subd9_1_793 : subd9_1 [2, -2, -1] = true := by decide +kernel
theorem subd9_1_794 : subd9_1 [2, -2, 0] = true := by decide +kernel
theorem subd9_1_795 : subd9_1 [2, -2, 1] = true := by decide +kernel
theorem subd9_1_796 : subd9_1 [2, -2, 2] = true := by decide +kernel
theorem subd9_1_797 : subd9_1 [2, -2, 3] = true := by decide +kernel
theorem subd9_1_798 : subd9_1 [2, -2, 4] = true := by decide +kernel
theorem subd9_1_799 : subd9_1 [2, -2, 5] = true := by decide +kernel
theorem sbd9_1_24 : ∀ q ∈ blkd9_1_24, subd9_1 q = true := by
  unfold blkd9_1_24
  exact List.forall_mem_cons.2 ⟨subd9_1_768, List.forall_mem_cons.2 ⟨subd9_1_769, List.forall_mem_cons.2 ⟨subd9_1_770, List.forall_mem_cons.2 ⟨subd9_1_771, List.forall_mem_cons.2 ⟨subd9_1_772, List.forall_mem_cons.2 ⟨subd9_1_773, List.forall_mem_cons.2 ⟨subd9_1_774, List.forall_mem_cons.2 ⟨subd9_1_775, List.forall_mem_cons.2 ⟨subd9_1_776, List.forall_mem_cons.2 ⟨subd9_1_777, List.forall_mem_cons.2 ⟨subd9_1_778, List.forall_mem_cons.2 ⟨subd9_1_779, List.forall_mem_cons.2 ⟨subd9_1_780, List.forall_mem_cons.2 ⟨subd9_1_781, List.forall_mem_cons.2 ⟨subd9_1_782, List.forall_mem_cons.2 ⟨subd9_1_783, List.forall_mem_cons.2 ⟨subd9_1_784, List.forall_mem_cons.2 ⟨subd9_1_785, List.forall_mem_cons.2 ⟨subd9_1_786, List.forall_mem_cons.2 ⟨subd9_1_787, List.forall_mem_cons.2 ⟨subd9_1_788, List.forall_mem_cons.2 ⟨subd9_1_789, List.forall_mem_cons.2 ⟨subd9_1_790, List.forall_mem_cons.2 ⟨subd9_1_791, List.forall_mem_cons.2 ⟨subd9_1_792, List.forall_mem_cons.2 ⟨subd9_1_793, List.forall_mem_cons.2 ⟨subd9_1_794, List.forall_mem_cons.2 ⟨subd9_1_795, List.forall_mem_cons.2 ⟨subd9_1_796, List.forall_mem_cons.2 ⟨subd9_1_797, List.forall_mem_cons.2 ⟨subd9_1_798, List.forall_mem_cons.2 ⟨subd9_1_799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_800 : subd9_1 [2, -2, 6] = true := by decide +kernel
theorem subd9_1_801 : subd9_1 [2, -2, 7] = true := by decide +kernel
theorem subd9_1_802 : subd9_1 [2, -2, 8] = true := by decide +kernel
theorem subd9_1_803 : subd9_1 [2, -1, -8] = true := by decide +kernel
theorem subd9_1_804 : subd9_1 [2, -1, -7] = true := by decide +kernel
theorem subd9_1_805 : subd9_1 [2, -1, -6] = true := by decide +kernel
theorem subd9_1_806 : subd9_1 [2, -1, -5] = true := by decide +kernel
theorem subd9_1_807 : subd9_1 [2, -1, -4] = true := by decide +kernel
theorem subd9_1_808 : subd9_1 [2, -1, -3] = true := by decide +kernel
theorem subd9_1_809 : subd9_1 [2, -1, -2] = true := by decide +kernel
theorem subd9_1_810 : subd9_1 [2, -1, -1] = true := by decide +kernel
theorem subd9_1_811 : subd9_1 [2, -1, 0] = true := by decide +kernel
theorem subd9_1_812 : subd9_1 [2, -1, 1] = true := by decide +kernel
theorem subd9_1_813 : subd9_1 [2, -1, 2] = true := by decide +kernel
theorem subd9_1_814 : subd9_1 [2, -1, 3] = true := by decide +kernel
theorem subd9_1_815 : subd9_1 [2, -1, 4] = true := by decide +kernel
theorem subd9_1_816 : subd9_1 [2, -1, 5] = true := by decide +kernel
theorem subd9_1_817 : subd9_1 [2, -1, 6] = true := by decide +kernel
theorem subd9_1_818 : subd9_1 [2, -1, 7] = true := by decide +kernel
theorem subd9_1_819 : subd9_1 [2, -1, 8] = true := by decide +kernel
theorem subd9_1_820 : subd9_1 [2, 0, -9] = true := by decide +kernel
theorem subd9_1_821 : subd9_1 [2, 0, -8] = true := by decide +kernel
theorem subd9_1_822 : subd9_1 [2, 0, -7] = true := by decide +kernel
theorem subd9_1_823 : subd9_1 [2, 0, -6] = true := by decide +kernel
theorem subd9_1_824 : subd9_1 [2, 0, -5] = true := by decide +kernel
theorem subd9_1_825 : subd9_1 [2, 0, -4] = true := by decide +kernel
theorem subd9_1_826 : subd9_1 [2, 0, -3] = true := by decide +kernel
theorem subd9_1_827 : subd9_1 [2, 0, -2] = true := by decide +kernel
theorem subd9_1_828 : subd9_1 [2, 0, -1] = true := by decide +kernel
theorem subd9_1_829 : subd9_1 [2, 0, 0] = true := by decide +kernel
theorem subd9_1_830 : subd9_1 [2, 0, 1] = true := by decide +kernel
theorem subd9_1_831 : subd9_1 [2, 0, 2] = true := by decide +kernel
theorem sbd9_1_25 : ∀ q ∈ blkd9_1_25, subd9_1 q = true := by
  unfold blkd9_1_25
  exact List.forall_mem_cons.2 ⟨subd9_1_800, List.forall_mem_cons.2 ⟨subd9_1_801, List.forall_mem_cons.2 ⟨subd9_1_802, List.forall_mem_cons.2 ⟨subd9_1_803, List.forall_mem_cons.2 ⟨subd9_1_804, List.forall_mem_cons.2 ⟨subd9_1_805, List.forall_mem_cons.2 ⟨subd9_1_806, List.forall_mem_cons.2 ⟨subd9_1_807, List.forall_mem_cons.2 ⟨subd9_1_808, List.forall_mem_cons.2 ⟨subd9_1_809, List.forall_mem_cons.2 ⟨subd9_1_810, List.forall_mem_cons.2 ⟨subd9_1_811, List.forall_mem_cons.2 ⟨subd9_1_812, List.forall_mem_cons.2 ⟨subd9_1_813, List.forall_mem_cons.2 ⟨subd9_1_814, List.forall_mem_cons.2 ⟨subd9_1_815, List.forall_mem_cons.2 ⟨subd9_1_816, List.forall_mem_cons.2 ⟨subd9_1_817, List.forall_mem_cons.2 ⟨subd9_1_818, List.forall_mem_cons.2 ⟨subd9_1_819, List.forall_mem_cons.2 ⟨subd9_1_820, List.forall_mem_cons.2 ⟨subd9_1_821, List.forall_mem_cons.2 ⟨subd9_1_822, List.forall_mem_cons.2 ⟨subd9_1_823, List.forall_mem_cons.2 ⟨subd9_1_824, List.forall_mem_cons.2 ⟨subd9_1_825, List.forall_mem_cons.2 ⟨subd9_1_826, List.forall_mem_cons.2 ⟨subd9_1_827, List.forall_mem_cons.2 ⟨subd9_1_828, List.forall_mem_cons.2 ⟨subd9_1_829, List.forall_mem_cons.2 ⟨subd9_1_830, List.forall_mem_cons.2 ⟨subd9_1_831, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_832 : subd9_1 [2, 0, 3] = true := by decide +kernel
theorem subd9_1_833 : subd9_1 [2, 0, 4] = true := by decide +kernel
theorem subd9_1_834 : subd9_1 [2, 0, 5] = true := by decide +kernel
theorem subd9_1_835 : subd9_1 [2, 0, 6] = true := by decide +kernel
theorem subd9_1_836 : subd9_1 [2, 0, 7] = true := by decide +kernel
theorem subd9_1_837 : subd9_1 [2, 0, 8] = true := by decide +kernel
theorem subd9_1_838 : subd9_1 [2, 1, -9] = true := by decide +kernel
theorem subd9_1_839 : subd9_1 [2, 1, -8] = true := by decide +kernel
theorem subd9_1_840 : subd9_1 [2, 1, -7] = true := by decide +kernel
theorem subd9_1_841 : subd9_1 [2, 1, -6] = true := by decide +kernel
theorem subd9_1_842 : subd9_1 [2, 1, -5] = true := by decide +kernel
theorem subd9_1_843 : subd9_1 [2, 1, -4] = true := by decide +kernel
theorem subd9_1_844 : subd9_1 [2, 1, -3] = true := by decide +kernel
theorem subd9_1_845 : subd9_1 [2, 1, -2] = true := by decide +kernel
theorem subd9_1_846 : subd9_1 [2, 1, -1] = true := by decide +kernel
theorem subd9_1_847 : subd9_1 [2, 1, 0] = true := by decide +kernel
theorem subd9_1_848 : subd9_1 [2, 1, 1] = true := by decide +kernel
theorem subd9_1_849 : subd9_1 [2, 1, 2] = true := by decide +kernel
theorem subd9_1_850 : subd9_1 [2, 1, 3] = true := by decide +kernel
theorem subd9_1_851 : subd9_1 [2, 1, 4] = true := by decide +kernel
theorem subd9_1_852 : subd9_1 [2, 1, 5] = true := by decide +kernel
theorem subd9_1_853 : subd9_1 [2, 1, 6] = true := by decide +kernel
theorem subd9_1_854 : subd9_1 [2, 1, 7] = true := by decide +kernel
theorem subd9_1_855 : subd9_1 [2, 2, -9] = true := by decide +kernel
theorem subd9_1_856 : subd9_1 [2, 2, -8] = true := by decide +kernel
theorem subd9_1_857 : subd9_1 [2, 2, -7] = true := by decide +kernel
theorem subd9_1_858 : subd9_1 [2, 2, -6] = true := by decide +kernel
theorem subd9_1_859 : subd9_1 [2, 2, -5] = true := by decide +kernel
theorem subd9_1_860 : subd9_1 [2, 2, -4] = true := by decide +kernel
theorem subd9_1_861 : subd9_1 [2, 2, -3] = true := by decide +kernel
theorem subd9_1_862 : subd9_1 [2, 2, -2] = true := by decide +kernel
theorem subd9_1_863 : subd9_1 [2, 2, -1] = true := by decide +kernel
theorem sbd9_1_26 : ∀ q ∈ blkd9_1_26, subd9_1 q = true := by
  unfold blkd9_1_26
  exact List.forall_mem_cons.2 ⟨subd9_1_832, List.forall_mem_cons.2 ⟨subd9_1_833, List.forall_mem_cons.2 ⟨subd9_1_834, List.forall_mem_cons.2 ⟨subd9_1_835, List.forall_mem_cons.2 ⟨subd9_1_836, List.forall_mem_cons.2 ⟨subd9_1_837, List.forall_mem_cons.2 ⟨subd9_1_838, List.forall_mem_cons.2 ⟨subd9_1_839, List.forall_mem_cons.2 ⟨subd9_1_840, List.forall_mem_cons.2 ⟨subd9_1_841, List.forall_mem_cons.2 ⟨subd9_1_842, List.forall_mem_cons.2 ⟨subd9_1_843, List.forall_mem_cons.2 ⟨subd9_1_844, List.forall_mem_cons.2 ⟨subd9_1_845, List.forall_mem_cons.2 ⟨subd9_1_846, List.forall_mem_cons.2 ⟨subd9_1_847, List.forall_mem_cons.2 ⟨subd9_1_848, List.forall_mem_cons.2 ⟨subd9_1_849, List.forall_mem_cons.2 ⟨subd9_1_850, List.forall_mem_cons.2 ⟨subd9_1_851, List.forall_mem_cons.2 ⟨subd9_1_852, List.forall_mem_cons.2 ⟨subd9_1_853, List.forall_mem_cons.2 ⟨subd9_1_854, List.forall_mem_cons.2 ⟨subd9_1_855, List.forall_mem_cons.2 ⟨subd9_1_856, List.forall_mem_cons.2 ⟨subd9_1_857, List.forall_mem_cons.2 ⟨subd9_1_858, List.forall_mem_cons.2 ⟨subd9_1_859, List.forall_mem_cons.2 ⟨subd9_1_860, List.forall_mem_cons.2 ⟨subd9_1_861, List.forall_mem_cons.2 ⟨subd9_1_862, List.forall_mem_cons.2 ⟨subd9_1_863, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_864 : subd9_1 [2, 2, 0] = true := by decide +kernel
theorem subd9_1_865 : subd9_1 [2, 2, 1] = true := by decide +kernel
theorem subd9_1_866 : subd9_1 [2, 2, 2] = true := by decide +kernel
theorem subd9_1_867 : subd9_1 [2, 2, 3] = true := by decide +kernel
theorem subd9_1_868 : subd9_1 [2, 2, 4] = true := by decide +kernel
theorem subd9_1_869 : subd9_1 [2, 2, 5] = true := by decide +kernel
theorem subd9_1_870 : subd9_1 [2, 2, 6] = true := by decide +kernel
theorem subd9_1_871 : subd9_1 [2, 2, 7] = true := by decide +kernel
theorem subd9_1_872 : subd9_1 [2, 3, -9] = true := by decide +kernel
theorem subd9_1_873 : subd9_1 [2, 3, -8] = true := by decide +kernel
theorem subd9_1_874 : subd9_1 [2, 3, -7] = true := by decide +kernel
theorem subd9_1_875 : subd9_1 [2, 3, -6] = true := by decide +kernel
theorem subd9_1_876 : subd9_1 [2, 3, -5] = true := by decide +kernel
theorem subd9_1_877 : subd9_1 [2, 3, -4] = true := by decide +kernel
theorem subd9_1_878 : subd9_1 [2, 3, -3] = true := by decide +kernel
theorem subd9_1_879 : subd9_1 [2, 3, -2] = true := by decide +kernel
theorem subd9_1_880 : subd9_1 [2, 3, -1] = true := by decide +kernel
theorem subd9_1_881 : subd9_1 [2, 3, 0] = true := by decide +kernel
theorem subd9_1_882 : subd9_1 [2, 3, 1] = true := by decide +kernel
theorem subd9_1_883 : subd9_1 [2, 3, 2] = true := by decide +kernel
theorem subd9_1_884 : subd9_1 [2, 3, 3] = true := by decide +kernel
theorem subd9_1_885 : subd9_1 [2, 3, 4] = true := by decide +kernel
theorem subd9_1_886 : subd9_1 [2, 3, 5] = true := by decide +kernel
theorem subd9_1_887 : subd9_1 [2, 3, 6] = true := by decide +kernel
theorem subd9_1_888 : subd9_1 [2, 4, -8] = true := by decide +kernel
theorem subd9_1_889 : subd9_1 [2, 4, -7] = true := by decide +kernel
theorem subd9_1_890 : subd9_1 [2, 4, -6] = true := by decide +kernel
theorem subd9_1_891 : subd9_1 [2, 4, -5] = true := by decide +kernel
theorem subd9_1_892 : subd9_1 [2, 4, -4] = true := by decide +kernel
theorem subd9_1_893 : subd9_1 [2, 4, -3] = true := by decide +kernel
theorem subd9_1_894 : subd9_1 [2, 4, -2] = true := by decide +kernel
theorem subd9_1_895 : subd9_1 [2, 4, -1] = true := by decide +kernel
theorem sbd9_1_27 : ∀ q ∈ blkd9_1_27, subd9_1 q = true := by
  unfold blkd9_1_27
  exact List.forall_mem_cons.2 ⟨subd9_1_864, List.forall_mem_cons.2 ⟨subd9_1_865, List.forall_mem_cons.2 ⟨subd9_1_866, List.forall_mem_cons.2 ⟨subd9_1_867, List.forall_mem_cons.2 ⟨subd9_1_868, List.forall_mem_cons.2 ⟨subd9_1_869, List.forall_mem_cons.2 ⟨subd9_1_870, List.forall_mem_cons.2 ⟨subd9_1_871, List.forall_mem_cons.2 ⟨subd9_1_872, List.forall_mem_cons.2 ⟨subd9_1_873, List.forall_mem_cons.2 ⟨subd9_1_874, List.forall_mem_cons.2 ⟨subd9_1_875, List.forall_mem_cons.2 ⟨subd9_1_876, List.forall_mem_cons.2 ⟨subd9_1_877, List.forall_mem_cons.2 ⟨subd9_1_878, List.forall_mem_cons.2 ⟨subd9_1_879, List.forall_mem_cons.2 ⟨subd9_1_880, List.forall_mem_cons.2 ⟨subd9_1_881, List.forall_mem_cons.2 ⟨subd9_1_882, List.forall_mem_cons.2 ⟨subd9_1_883, List.forall_mem_cons.2 ⟨subd9_1_884, List.forall_mem_cons.2 ⟨subd9_1_885, List.forall_mem_cons.2 ⟨subd9_1_886, List.forall_mem_cons.2 ⟨subd9_1_887, List.forall_mem_cons.2 ⟨subd9_1_888, List.forall_mem_cons.2 ⟨subd9_1_889, List.forall_mem_cons.2 ⟨subd9_1_890, List.forall_mem_cons.2 ⟨subd9_1_891, List.forall_mem_cons.2 ⟨subd9_1_892, List.forall_mem_cons.2 ⟨subd9_1_893, List.forall_mem_cons.2 ⟨subd9_1_894, List.forall_mem_cons.2 ⟨subd9_1_895, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_896 : subd9_1 [2, 4, 0] = true := by decide +kernel
theorem subd9_1_897 : subd9_1 [2, 4, 1] = true := by decide +kernel
theorem subd9_1_898 : subd9_1 [2, 4, 2] = true := by decide +kernel
theorem subd9_1_899 : subd9_1 [2, 4, 3] = true := by decide +kernel
theorem subd9_1_900 : subd9_1 [2, 4, 4] = true := by decide +kernel
theorem subd9_1_901 : subd9_1 [2, 4, 5] = true := by decide +kernel
theorem subd9_1_902 : subd9_1 [2, 5] = true := by decide +kernel
theorem subd9_1_903 : subd9_1 [2, 6] = true := by decide +kernel
theorem subd9_1_904 : subd9_1 [3, -6] = true := by decide +kernel
theorem subd9_1_905 : subd9_1 [3, -5] = true := by decide +kernel
theorem subd9_1_906 : subd9_1 [3, -4] = true := by decide +kernel
theorem subd9_1_907 : subd9_1 [3, -3] = true := by decide +kernel
theorem subd9_1_908 : subd9_1 [3, -2, -7] = true := by decide +kernel
theorem subd9_1_909 : subd9_1 [3, -2, -6] = true := by decide +kernel
theorem subd9_1_910 : subd9_1 [3, -2, -5] = true := by decide +kernel
theorem subd9_1_911 : subd9_1 [3, -2, -4] = true := by decide +kernel
theorem subd9_1_912 : subd9_1 [3, -2, -3] = true := by decide +kernel
theorem subd9_1_913 : subd9_1 [3, -2, -2] = true := by decide +kernel
theorem subd9_1_914 : subd9_1 [3, -2, -1] = true := by decide +kernel
theorem subd9_1_915 : subd9_1 [3, -2, 0] = true := by decide +kernel
theorem subd9_1_916 : subd9_1 [3, -2, 1] = true := by decide +kernel
theorem subd9_1_917 : subd9_1 [3, -2, 2] = true := by decide +kernel
theorem subd9_1_918 : subd9_1 [3, -2, 3] = true := by decide +kernel
theorem subd9_1_919 : subd9_1 [3, -2, 4] = true := by decide +kernel
theorem subd9_1_920 : subd9_1 [3, -2, 5] = true := by decide +kernel
theorem subd9_1_921 : subd9_1 [3, -2, 6] = true := by decide +kernel
theorem subd9_1_922 : subd9_1 [3, -2, 7] = true := by decide +kernel
theorem subd9_1_923 : subd9_1 [3, -1, -8] = true := by decide +kernel
theorem subd9_1_924 : subd9_1 [3, -1, -7] = true := by decide +kernel
theorem subd9_1_925 : subd9_1 [3, -1, -6] = true := by decide +kernel
theorem subd9_1_926 : subd9_1 [3, -1, -5] = true := by decide +kernel
theorem subd9_1_927 : subd9_1 [3, -1, -4] = true := by decide +kernel
theorem sbd9_1_28 : ∀ q ∈ blkd9_1_28, subd9_1 q = true := by
  unfold blkd9_1_28
  exact List.forall_mem_cons.2 ⟨subd9_1_896, List.forall_mem_cons.2 ⟨subd9_1_897, List.forall_mem_cons.2 ⟨subd9_1_898, List.forall_mem_cons.2 ⟨subd9_1_899, List.forall_mem_cons.2 ⟨subd9_1_900, List.forall_mem_cons.2 ⟨subd9_1_901, List.forall_mem_cons.2 ⟨subd9_1_902, List.forall_mem_cons.2 ⟨subd9_1_903, List.forall_mem_cons.2 ⟨subd9_1_904, List.forall_mem_cons.2 ⟨subd9_1_905, List.forall_mem_cons.2 ⟨subd9_1_906, List.forall_mem_cons.2 ⟨subd9_1_907, List.forall_mem_cons.2 ⟨subd9_1_908, List.forall_mem_cons.2 ⟨subd9_1_909, List.forall_mem_cons.2 ⟨subd9_1_910, List.forall_mem_cons.2 ⟨subd9_1_911, List.forall_mem_cons.2 ⟨subd9_1_912, List.forall_mem_cons.2 ⟨subd9_1_913, List.forall_mem_cons.2 ⟨subd9_1_914, List.forall_mem_cons.2 ⟨subd9_1_915, List.forall_mem_cons.2 ⟨subd9_1_916, List.forall_mem_cons.2 ⟨subd9_1_917, List.forall_mem_cons.2 ⟨subd9_1_918, List.forall_mem_cons.2 ⟨subd9_1_919, List.forall_mem_cons.2 ⟨subd9_1_920, List.forall_mem_cons.2 ⟨subd9_1_921, List.forall_mem_cons.2 ⟨subd9_1_922, List.forall_mem_cons.2 ⟨subd9_1_923, List.forall_mem_cons.2 ⟨subd9_1_924, List.forall_mem_cons.2 ⟨subd9_1_925, List.forall_mem_cons.2 ⟨subd9_1_926, List.forall_mem_cons.2 ⟨subd9_1_927, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_928 : subd9_1 [3, -1, -3] = true := by decide +kernel
theorem subd9_1_929 : subd9_1 [3, -1, -2] = true := by decide +kernel
theorem subd9_1_930 : subd9_1 [3, -1, -1] = true := by decide +kernel
theorem subd9_1_931 : subd9_1 [3, -1, 0] = true := by decide +kernel
theorem subd9_1_932 : subd9_1 [3, -1, 1] = true := by decide +kernel
theorem subd9_1_933 : subd9_1 [3, -1, 2] = true := by decide +kernel
theorem subd9_1_934 : subd9_1 [3, -1, 3] = true := by decide +kernel
theorem subd9_1_935 : subd9_1 [3, -1, 4] = true := by decide +kernel
theorem subd9_1_936 : subd9_1 [3, -1, 5] = true := by decide +kernel
theorem subd9_1_937 : subd9_1 [3, -1, 6] = true := by decide +kernel
theorem subd9_1_938 : subd9_1 [3, -1, 7] = true := by decide +kernel
theorem subd9_1_939 : subd9_1 [3, 0, -8] = true := by decide +kernel
theorem subd9_1_940 : subd9_1 [3, 0, -7] = true := by decide +kernel
theorem subd9_1_941 : subd9_1 [3, 0, -6] = true := by decide +kernel
theorem subd9_1_942 : subd9_1 [3, 0, -5] = true := by decide +kernel
theorem subd9_1_943 : subd9_1 [3, 0, -4] = true := by decide +kernel
theorem subd9_1_944 : subd9_1 [3, 0, -3] = true := by decide +kernel
theorem subd9_1_945 : subd9_1 [3, 0, -2] = true := by decide +kernel
theorem subd9_1_946 : subd9_1 [3, 0, -1] = true := by decide +kernel
theorem subd9_1_947 : subd9_1 [3, 0, 0] = true := by decide +kernel
theorem subd9_1_948 : subd9_1 [3, 0, 1] = true := by decide +kernel
theorem subd9_1_949 : subd9_1 [3, 0, 2] = true := by decide +kernel
theorem subd9_1_950 : subd9_1 [3, 0, 3] = true := by decide +kernel
theorem subd9_1_951 : subd9_1 [3, 0, 4] = true := by decide +kernel
theorem subd9_1_952 : subd9_1 [3, 0, 5] = true := by decide +kernel
theorem subd9_1_953 : subd9_1 [3, 0, 6] = true := by decide +kernel
theorem subd9_1_954 : subd9_1 [3, 0, 7] = true := by decide +kernel
theorem subd9_1_955 : subd9_1 [3, 1, -8] = true := by decide +kernel
theorem subd9_1_956 : subd9_1 [3, 1, -7] = true := by decide +kernel
theorem subd9_1_957 : subd9_1 [3, 1, -6] = true := by decide +kernel
theorem subd9_1_958 : subd9_1 [3, 1, -5] = true := by decide +kernel
theorem subd9_1_959 : subd9_1 [3, 1, -4] = true := by decide +kernel
theorem sbd9_1_29 : ∀ q ∈ blkd9_1_29, subd9_1 q = true := by
  unfold blkd9_1_29
  exact List.forall_mem_cons.2 ⟨subd9_1_928, List.forall_mem_cons.2 ⟨subd9_1_929, List.forall_mem_cons.2 ⟨subd9_1_930, List.forall_mem_cons.2 ⟨subd9_1_931, List.forall_mem_cons.2 ⟨subd9_1_932, List.forall_mem_cons.2 ⟨subd9_1_933, List.forall_mem_cons.2 ⟨subd9_1_934, List.forall_mem_cons.2 ⟨subd9_1_935, List.forall_mem_cons.2 ⟨subd9_1_936, List.forall_mem_cons.2 ⟨subd9_1_937, List.forall_mem_cons.2 ⟨subd9_1_938, List.forall_mem_cons.2 ⟨subd9_1_939, List.forall_mem_cons.2 ⟨subd9_1_940, List.forall_mem_cons.2 ⟨subd9_1_941, List.forall_mem_cons.2 ⟨subd9_1_942, List.forall_mem_cons.2 ⟨subd9_1_943, List.forall_mem_cons.2 ⟨subd9_1_944, List.forall_mem_cons.2 ⟨subd9_1_945, List.forall_mem_cons.2 ⟨subd9_1_946, List.forall_mem_cons.2 ⟨subd9_1_947, List.forall_mem_cons.2 ⟨subd9_1_948, List.forall_mem_cons.2 ⟨subd9_1_949, List.forall_mem_cons.2 ⟨subd9_1_950, List.forall_mem_cons.2 ⟨subd9_1_951, List.forall_mem_cons.2 ⟨subd9_1_952, List.forall_mem_cons.2 ⟨subd9_1_953, List.forall_mem_cons.2 ⟨subd9_1_954, List.forall_mem_cons.2 ⟨subd9_1_955, List.forall_mem_cons.2 ⟨subd9_1_956, List.forall_mem_cons.2 ⟨subd9_1_957, List.forall_mem_cons.2 ⟨subd9_1_958, List.forall_mem_cons.2 ⟨subd9_1_959, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_960 : subd9_1 [3, 1, -3] = true := by decide +kernel
theorem subd9_1_961 : subd9_1 [3, 1, -2] = true := by decide +kernel
theorem subd9_1_962 : subd9_1 [3, 1, -1] = true := by decide +kernel
theorem subd9_1_963 : subd9_1 [3, 1, 0] = true := by decide +kernel
theorem subd9_1_964 : subd9_1 [3, 1, 1] = true := by decide +kernel
theorem subd9_1_965 : subd9_1 [3, 1, 2] = true := by decide +kernel
theorem subd9_1_966 : subd9_1 [3, 1, 3] = true := by decide +kernel
theorem subd9_1_967 : subd9_1 [3, 1, 4] = true := by decide +kernel
theorem subd9_1_968 : subd9_1 [3, 1, 5] = true := by decide +kernel
theorem subd9_1_969 : subd9_1 [3, 1, 6] = true := by decide +kernel
theorem subd9_1_970 : subd9_1 [3, 1, 7] = true := by decide +kernel
theorem subd9_1_971 : subd9_1 [3, 2, -8] = true := by decide +kernel
theorem subd9_1_972 : subd9_1 [3, 2, -7] = true := by decide +kernel
theorem subd9_1_973 : subd9_1 [3, 2, -6] = true := by decide +kernel
theorem subd9_1_974 : subd9_1 [3, 2, -5] = true := by decide +kernel
theorem subd9_1_975 : subd9_1 [3, 2, -4] = true := by decide +kernel
theorem subd9_1_976 : subd9_1 [3, 2, -3] = true := by decide +kernel
theorem subd9_1_977 : subd9_1 [3, 2, -2] = true := by decide +kernel
theorem subd9_1_978 : subd9_1 [3, 2, -1] = true := by decide +kernel
theorem subd9_1_979 : subd9_1 [3, 2, 0] = true := by decide +kernel
theorem subd9_1_980 : subd9_1 [3, 2, 1] = true := by decide +kernel
theorem subd9_1_981 : subd9_1 [3, 2, 2] = true := by decide +kernel
theorem subd9_1_982 : subd9_1 [3, 2, 3] = true := by decide +kernel
theorem subd9_1_983 : subd9_1 [3, 2, 4] = true := by decide +kernel
theorem subd9_1_984 : subd9_1 [3, 2, 5] = true := by decide +kernel
theorem subd9_1_985 : subd9_1 [3, 2, 6] = true := by decide +kernel
theorem subd9_1_986 : subd9_1 [3, 3, -8] = true := by decide +kernel
theorem subd9_1_987 : subd9_1 [3, 3, -7] = true := by decide +kernel
theorem subd9_1_988 : subd9_1 [3, 3, -6] = true := by decide +kernel
theorem subd9_1_989 : subd9_1 [3, 3, -5] = true := by decide +kernel
theorem subd9_1_990 : subd9_1 [3, 3, -4] = true := by decide +kernel
theorem subd9_1_991 : subd9_1 [3, 3, -3] = true := by decide +kernel
theorem sbd9_1_30 : ∀ q ∈ blkd9_1_30, subd9_1 q = true := by
  unfold blkd9_1_30
  exact List.forall_mem_cons.2 ⟨subd9_1_960, List.forall_mem_cons.2 ⟨subd9_1_961, List.forall_mem_cons.2 ⟨subd9_1_962, List.forall_mem_cons.2 ⟨subd9_1_963, List.forall_mem_cons.2 ⟨subd9_1_964, List.forall_mem_cons.2 ⟨subd9_1_965, List.forall_mem_cons.2 ⟨subd9_1_966, List.forall_mem_cons.2 ⟨subd9_1_967, List.forall_mem_cons.2 ⟨subd9_1_968, List.forall_mem_cons.2 ⟨subd9_1_969, List.forall_mem_cons.2 ⟨subd9_1_970, List.forall_mem_cons.2 ⟨subd9_1_971, List.forall_mem_cons.2 ⟨subd9_1_972, List.forall_mem_cons.2 ⟨subd9_1_973, List.forall_mem_cons.2 ⟨subd9_1_974, List.forall_mem_cons.2 ⟨subd9_1_975, List.forall_mem_cons.2 ⟨subd9_1_976, List.forall_mem_cons.2 ⟨subd9_1_977, List.forall_mem_cons.2 ⟨subd9_1_978, List.forall_mem_cons.2 ⟨subd9_1_979, List.forall_mem_cons.2 ⟨subd9_1_980, List.forall_mem_cons.2 ⟨subd9_1_981, List.forall_mem_cons.2 ⟨subd9_1_982, List.forall_mem_cons.2 ⟨subd9_1_983, List.forall_mem_cons.2 ⟨subd9_1_984, List.forall_mem_cons.2 ⟨subd9_1_985, List.forall_mem_cons.2 ⟨subd9_1_986, List.forall_mem_cons.2 ⟨subd9_1_987, List.forall_mem_cons.2 ⟨subd9_1_988, List.forall_mem_cons.2 ⟨subd9_1_989, List.forall_mem_cons.2 ⟨subd9_1_990, List.forall_mem_cons.2 ⟨subd9_1_991, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_992 : subd9_1 [3, 3, -2] = true := by decide +kernel
theorem subd9_1_993 : subd9_1 [3, 3, -1] = true := by decide +kernel
theorem subd9_1_994 : subd9_1 [3, 3, 0] = true := by decide +kernel
theorem subd9_1_995 : subd9_1 [3, 3, 1] = true := by decide +kernel
theorem subd9_1_996 : subd9_1 [3, 3, 2] = true := by decide +kernel
theorem subd9_1_997 : subd9_1 [3, 3, 3] = true := by decide +kernel
theorem subd9_1_998 : subd9_1 [3, 3, 4] = true := by decide +kernel
theorem subd9_1_999 : subd9_1 [3, 3, 5] = true := by decide +kernel
theorem subd9_1_1000 : subd9_1 [3, 4] = true := by decide +kernel
theorem subd9_1_1001 : subd9_1 [3, 5] = true := by decide +kernel
theorem subd9_1_1002 : subd9_1 [4, -5] = true := by decide +kernel
theorem subd9_1_1003 : subd9_1 [4, -4] = true := by decide +kernel
theorem subd9_1_1004 : subd9_1 [4, -3] = true := by decide +kernel
theorem subd9_1_1005 : subd9_1 [4, -2] = true := by decide +kernel
theorem subd9_1_1006 : subd9_1 [4, -1, -6] = true := by decide +kernel
theorem subd9_1_1007 : subd9_1 [4, -1, -5] = true := by decide +kernel
theorem subd9_1_1008 : subd9_1 [4, -1, -4] = true := by decide +kernel
theorem subd9_1_1009 : subd9_1 [4, -1, -3] = true := by decide +kernel
theorem subd9_1_1010 : subd9_1 [4, -1, -2] = true := by decide +kernel
theorem subd9_1_1011 : subd9_1 [4, -1, -1] = true := by decide +kernel
theorem subd9_1_1012 : subd9_1 [4, -1, 0] = true := by decide +kernel
theorem subd9_1_1013 : subd9_1 [4, -1, 1] = true := by decide +kernel
theorem subd9_1_1014 : subd9_1 [4, -1, 2] = true := by decide +kernel
theorem subd9_1_1015 : subd9_1 [4, -1, 3] = true := by decide +kernel
theorem subd9_1_1016 : subd9_1 [4, -1, 4] = true := by decide +kernel
theorem subd9_1_1017 : subd9_1 [4, -1, 5] = true := by decide +kernel
theorem subd9_1_1018 : subd9_1 [4, -1, 6] = true := by decide +kernel
theorem subd9_1_1019 : subd9_1 [4, 0, -7] = true := by decide +kernel
theorem subd9_1_1020 : subd9_1 [4, 0, -6] = true := by decide +kernel
theorem subd9_1_1021 : subd9_1 [4, 0, -5] = true := by decide +kernel
theorem subd9_1_1022 : subd9_1 [4, 0, -4] = true := by decide +kernel
theorem subd9_1_1023 : subd9_1 [4, 0, -3] = true := by decide +kernel
theorem sbd9_1_31 : ∀ q ∈ blkd9_1_31, subd9_1 q = true := by
  unfold blkd9_1_31
  exact List.forall_mem_cons.2 ⟨subd9_1_992, List.forall_mem_cons.2 ⟨subd9_1_993, List.forall_mem_cons.2 ⟨subd9_1_994, List.forall_mem_cons.2 ⟨subd9_1_995, List.forall_mem_cons.2 ⟨subd9_1_996, List.forall_mem_cons.2 ⟨subd9_1_997, List.forall_mem_cons.2 ⟨subd9_1_998, List.forall_mem_cons.2 ⟨subd9_1_999, List.forall_mem_cons.2 ⟨subd9_1_1000, List.forall_mem_cons.2 ⟨subd9_1_1001, List.forall_mem_cons.2 ⟨subd9_1_1002, List.forall_mem_cons.2 ⟨subd9_1_1003, List.forall_mem_cons.2 ⟨subd9_1_1004, List.forall_mem_cons.2 ⟨subd9_1_1005, List.forall_mem_cons.2 ⟨subd9_1_1006, List.forall_mem_cons.2 ⟨subd9_1_1007, List.forall_mem_cons.2 ⟨subd9_1_1008, List.forall_mem_cons.2 ⟨subd9_1_1009, List.forall_mem_cons.2 ⟨subd9_1_1010, List.forall_mem_cons.2 ⟨subd9_1_1011, List.forall_mem_cons.2 ⟨subd9_1_1012, List.forall_mem_cons.2 ⟨subd9_1_1013, List.forall_mem_cons.2 ⟨subd9_1_1014, List.forall_mem_cons.2 ⟨subd9_1_1015, List.forall_mem_cons.2 ⟨subd9_1_1016, List.forall_mem_cons.2 ⟨subd9_1_1017, List.forall_mem_cons.2 ⟨subd9_1_1018, List.forall_mem_cons.2 ⟨subd9_1_1019, List.forall_mem_cons.2 ⟨subd9_1_1020, List.forall_mem_cons.2 ⟨subd9_1_1021, List.forall_mem_cons.2 ⟨subd9_1_1022, List.forall_mem_cons.2 ⟨subd9_1_1023, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_1024 : subd9_1 [4, 0, -2] = true := by decide +kernel
theorem subd9_1_1025 : subd9_1 [4, 0, -1] = true := by decide +kernel
theorem subd9_1_1026 : subd9_1 [4, 0, 0] = true := by decide +kernel
theorem subd9_1_1027 : subd9_1 [4, 0, 1] = true := by decide +kernel
theorem subd9_1_1028 : subd9_1 [4, 0, 2] = true := by decide +kernel
theorem subd9_1_1029 : subd9_1 [4, 0, 3] = true := by decide +kernel
theorem subd9_1_1030 : subd9_1 [4, 0, 4] = true := by decide +kernel
theorem subd9_1_1031 : subd9_1 [4, 0, 5] = true := by decide +kernel
theorem subd9_1_1032 : subd9_1 [4, 0, 6] = true := by decide +kernel
theorem subd9_1_1033 : subd9_1 [4, 1, -7] = true := by decide +kernel
theorem subd9_1_1034 : subd9_1 [4, 1, -6] = true := by decide +kernel
theorem subd9_1_1035 : subd9_1 [4, 1, -5] = true := by decide +kernel
theorem subd9_1_1036 : subd9_1 [4, 1, -4] = true := by decide +kernel
theorem subd9_1_1037 : subd9_1 [4, 1, -3] = true := by decide +kernel
theorem subd9_1_1038 : subd9_1 [4, 1, -2] = true := by decide +kernel
theorem subd9_1_1039 : subd9_1 [4, 1, -1] = true := by decide +kernel
theorem subd9_1_1040 : subd9_1 [4, 1, 0] = true := by decide +kernel
theorem subd9_1_1041 : subd9_1 [4, 1, 1] = true := by decide +kernel
theorem subd9_1_1042 : subd9_1 [4, 1, 2] = true := by decide +kernel
theorem subd9_1_1043 : subd9_1 [4, 1, 3] = true := by decide +kernel
theorem subd9_1_1044 : subd9_1 [4, 1, 4] = true := by decide +kernel
theorem subd9_1_1045 : subd9_1 [4, 1, 5] = true := by decide +kernel
theorem subd9_1_1046 : subd9_1 [4, 1, 6] = true := by decide +kernel
theorem subd9_1_1047 : subd9_1 [4, 2, -8] = true := by decide +kernel
theorem subd9_1_1048 : subd9_1 [4, 2, -7] = true := by decide +kernel
theorem subd9_1_1049 : subd9_1 [4, 2, -6] = true := by decide +kernel
theorem subd9_1_1050 : subd9_1 [4, 2, -5] = true := by decide +kernel
theorem subd9_1_1051 : subd9_1 [4, 2, -4] = true := by decide +kernel
theorem subd9_1_1052 : subd9_1 [4, 2, -3] = true := by decide +kernel
theorem subd9_1_1053 : subd9_1 [4, 2, -2] = true := by decide +kernel
theorem subd9_1_1054 : subd9_1 [4, 2, -1] = true := by decide +kernel
theorem subd9_1_1055 : subd9_1 [4, 2, 0] = true := by decide +kernel
theorem sbd9_1_32 : ∀ q ∈ blkd9_1_32, subd9_1 q = true := by
  unfold blkd9_1_32
  exact List.forall_mem_cons.2 ⟨subd9_1_1024, List.forall_mem_cons.2 ⟨subd9_1_1025, List.forall_mem_cons.2 ⟨subd9_1_1026, List.forall_mem_cons.2 ⟨subd9_1_1027, List.forall_mem_cons.2 ⟨subd9_1_1028, List.forall_mem_cons.2 ⟨subd9_1_1029, List.forall_mem_cons.2 ⟨subd9_1_1030, List.forall_mem_cons.2 ⟨subd9_1_1031, List.forall_mem_cons.2 ⟨subd9_1_1032, List.forall_mem_cons.2 ⟨subd9_1_1033, List.forall_mem_cons.2 ⟨subd9_1_1034, List.forall_mem_cons.2 ⟨subd9_1_1035, List.forall_mem_cons.2 ⟨subd9_1_1036, List.forall_mem_cons.2 ⟨subd9_1_1037, List.forall_mem_cons.2 ⟨subd9_1_1038, List.forall_mem_cons.2 ⟨subd9_1_1039, List.forall_mem_cons.2 ⟨subd9_1_1040, List.forall_mem_cons.2 ⟨subd9_1_1041, List.forall_mem_cons.2 ⟨subd9_1_1042, List.forall_mem_cons.2 ⟨subd9_1_1043, List.forall_mem_cons.2 ⟨subd9_1_1044, List.forall_mem_cons.2 ⟨subd9_1_1045, List.forall_mem_cons.2 ⟨subd9_1_1046, List.forall_mem_cons.2 ⟨subd9_1_1047, List.forall_mem_cons.2 ⟨subd9_1_1048, List.forall_mem_cons.2 ⟨subd9_1_1049, List.forall_mem_cons.2 ⟨subd9_1_1050, List.forall_mem_cons.2 ⟨subd9_1_1051, List.forall_mem_cons.2 ⟨subd9_1_1052, List.forall_mem_cons.2 ⟨subd9_1_1053, List.forall_mem_cons.2 ⟨subd9_1_1054, List.forall_mem_cons.2 ⟨subd9_1_1055, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_1056 : subd9_1 [4, 2, 1] = true := by decide +kernel
theorem subd9_1_1057 : subd9_1 [4, 2, 2] = true := by decide +kernel
theorem subd9_1_1058 : subd9_1 [4, 2, 3] = true := by decide +kernel
theorem subd9_1_1059 : subd9_1 [4, 2, 4] = true := by decide +kernel
theorem subd9_1_1060 : subd9_1 [4, 2, 5] = true := by decide +kernel
theorem subd9_1_1061 : subd9_1 [4, 3] = true := by decide +kernel
theorem subd9_1_1062 : subd9_1 [4, 4] = true := by decide +kernel
theorem subd9_1_1063 : subd9_1 [4, 5] = true := by decide +kernel
theorem subd9_1_1064 : subd9_1 [5, -3] = true := by decide +kernel
theorem subd9_1_1065 : subd9_1 [5, -2] = true := by decide +kernel
theorem subd9_1_1066 : subd9_1 [5, -1] = true := by decide +kernel
theorem subd9_1_1067 : subd9_1 [5, 0] = true := by decide +kernel
theorem subd9_1_1068 : subd9_1 [5, 1] = true := by decide +kernel
theorem subd9_1_1069 : subd9_1 [5, 2] = true := by decide +kernel
theorem subd9_1_1070 : subd9_1 [5, 3] = true := by decide +kernel
theorem subd9_1_1071 : subd9_1 [5, 4] = true := by decide +kernel
theorem subd9_1_1072 : subd9_1 [6] = true := by decide +kernel
theorem sbd9_1_33 : ∀ q ∈ blkd9_1_33, subd9_1 q = true := by
  unfold blkd9_1_33
  exact List.forall_mem_cons.2 ⟨subd9_1_1056, List.forall_mem_cons.2 ⟨subd9_1_1057, List.forall_mem_cons.2 ⟨subd9_1_1058, List.forall_mem_cons.2 ⟨subd9_1_1059, List.forall_mem_cons.2 ⟨subd9_1_1060, List.forall_mem_cons.2 ⟨subd9_1_1061, List.forall_mem_cons.2 ⟨subd9_1_1062, List.forall_mem_cons.2 ⟨subd9_1_1063, List.forall_mem_cons.2 ⟨subd9_1_1064, List.forall_mem_cons.2 ⟨subd9_1_1065, List.forall_mem_cons.2 ⟨subd9_1_1066, List.forall_mem_cons.2 ⟨subd9_1_1067, List.forall_mem_cons.2 ⟨subd9_1_1068, List.forall_mem_cons.2 ⟨subd9_1_1069, List.forall_mem_cons.2 ⟨subd9_1_1070, List.forall_mem_cons.2 ⟨subd9_1_1071, List.forall_mem_cons.2 ⟨subd9_1_1072, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_2 : ldCheck G d9_2.U d9_2.ms ldd9_2 = true := by decide +kernel
theorem pre_okd9_2 : subPre G cell9 d9_2 = true := by decide +kernel
theorem subd9_2_0 : subd9_2 [-3, -1] = true := by decide +kernel
theorem subd9_2_1 : subd9_2 [-3, 0, -9] = true := by decide +kernel
theorem subd9_2_2 : subd9_2 [-3, 0, -8] = true := by decide +kernel
theorem subd9_2_3 : subd9_2 [-3, 0, -7] = true := by decide +kernel
theorem subd9_2_4 : subd9_2 [-3, 0, -6] = true := by decide +kernel
theorem subd9_2_5 : subd9_2 [-3, 0, -5] = true := by decide +kernel
theorem subd9_2_6 : subd9_2 [-3, 0, -4] = true := by decide +kernel
theorem subd9_2_7 : subd9_2 [-3, 0, -3] = true := by decide +kernel
theorem subd9_2_8 : subd9_2 [-3, 0, -2] = true := by decide +kernel
theorem subd9_2_9 : subd9_2 [-3, 0, -1] = true := by decide +kernel
theorem subd9_2_10 : subd9_2 [-3, 0, 0] = true := by decide +kernel
theorem subd9_2_11 : subd9_2 [-3, 0, 1] = true := by decide +kernel
theorem subd9_2_12 : subd9_2 [-3, 0, 2] = true := by decide +kernel
theorem subd9_2_13 : subd9_2 [-3, 0, 3] = true := by decide +kernel
theorem subd9_2_14 : subd9_2 [-3, 0, 4] = true := by decide +kernel
theorem subd9_2_15 : subd9_2 [-3, 0, 5] = true := by decide +kernel
theorem subd9_2_16 : subd9_2 [-3, 0, 6] = true := by decide +kernel
theorem subd9_2_17 : subd9_2 [-3, 0, 7] = true := by decide +kernel
theorem subd9_2_18 : subd9_2 [-3, 0, 8] = true := by decide +kernel
theorem subd9_2_19 : subd9_2 [-3, 0, 9] = true := by decide +kernel
theorem subd9_2_20 : subd9_2 [-3, 0, 10] = true := by decide +kernel
theorem subd9_2_21 : subd9_2 [-3, 1, -10] = true := by decide +kernel
theorem subd9_2_22 : subd9_2 [-3, 1, -9] = true := by decide +kernel
theorem subd9_2_23 : subd9_2 [-3, 1, -8] = true := by decide +kernel
theorem subd9_2_24 : subd9_2 [-3, 1, -7] = true := by decide +kernel
theorem subd9_2_25 : subd9_2 [-3, 1, -6] = true := by decide +kernel
theorem subd9_2_26 : subd9_2 [-3, 1, -5] = true := by decide +kernel
theorem subd9_2_27 : subd9_2 [-3, 1, -4] = true := by decide +kernel
theorem subd9_2_28 : subd9_2 [-3, 1, -3] = true := by decide +kernel
theorem subd9_2_29 : subd9_2 [-3, 1, -2] = true := by decide +kernel
theorem subd9_2_30 : subd9_2 [-3, 1, -1] = true := by decide +kernel
theorem subd9_2_31 : subd9_2 [-3, 1, 0] = true := by decide +kernel
theorem sbd9_2_0 : ∀ q ∈ blkd9_2_0, subd9_2 q = true := by
  unfold blkd9_2_0
  exact List.forall_mem_cons.2 ⟨subd9_2_0, List.forall_mem_cons.2 ⟨subd9_2_1, List.forall_mem_cons.2 ⟨subd9_2_2, List.forall_mem_cons.2 ⟨subd9_2_3, List.forall_mem_cons.2 ⟨subd9_2_4, List.forall_mem_cons.2 ⟨subd9_2_5, List.forall_mem_cons.2 ⟨subd9_2_6, List.forall_mem_cons.2 ⟨subd9_2_7, List.forall_mem_cons.2 ⟨subd9_2_8, List.forall_mem_cons.2 ⟨subd9_2_9, List.forall_mem_cons.2 ⟨subd9_2_10, List.forall_mem_cons.2 ⟨subd9_2_11, List.forall_mem_cons.2 ⟨subd9_2_12, List.forall_mem_cons.2 ⟨subd9_2_13, List.forall_mem_cons.2 ⟨subd9_2_14, List.forall_mem_cons.2 ⟨subd9_2_15, List.forall_mem_cons.2 ⟨subd9_2_16, List.forall_mem_cons.2 ⟨subd9_2_17, List.forall_mem_cons.2 ⟨subd9_2_18, List.forall_mem_cons.2 ⟨subd9_2_19, List.forall_mem_cons.2 ⟨subd9_2_20, List.forall_mem_cons.2 ⟨subd9_2_21, List.forall_mem_cons.2 ⟨subd9_2_22, List.forall_mem_cons.2 ⟨subd9_2_23, List.forall_mem_cons.2 ⟨subd9_2_24, List.forall_mem_cons.2 ⟨subd9_2_25, List.forall_mem_cons.2 ⟨subd9_2_26, List.forall_mem_cons.2 ⟨subd9_2_27, List.forall_mem_cons.2 ⟨subd9_2_28, List.forall_mem_cons.2 ⟨subd9_2_29, List.forall_mem_cons.2 ⟨subd9_2_30, List.forall_mem_cons.2 ⟨subd9_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C135
