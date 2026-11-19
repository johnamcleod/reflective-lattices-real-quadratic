import ReflectZphi.Data.Cert5.C047.Base

namespace ReflectZphi.Data.Cert5.C047
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub5_736 : sub5 [1, 3, -8] = true := by decide +kernel
theorem sub5_737 : sub5 [1, 3, -7] = true := by decide +kernel
theorem sub5_738 : sub5 [1, 3, -6] = true := by decide +kernel
theorem sub5_739 : sub5 [1, 3, -5] = true := by decide +kernel
theorem sub5_740 : sub5 [1, 3, -4] = true := by decide +kernel
theorem sub5_741 : sub5 [1, 3, -3] = true := by decide +kernel
theorem sub5_742 : sub5 [1, 3, -2] = true := by decide +kernel
theorem sub5_743 : sub5 [1, 3, -1] = true := by decide +kernel
theorem sub5_744 : sub5 [1, 3, 0] = true := by decide +kernel
theorem sub5_745 : sub5 [1, 3, 1] = true := by decide +kernel
theorem sub5_746 : sub5 [1, 3, 2] = true := by decide +kernel
theorem sub5_747 : sub5 [1, 3, 3] = true := by decide +kernel
theorem sub5_748 : sub5 [1, 3, 4] = true := by decide +kernel
theorem sub5_749 : sub5 [1, 3, 5] = true := by decide +kernel
theorem sub5_750 : sub5 [1, 3, 6] = true := by decide +kernel
theorem sub5_751 : sub5 [1, 3, 7] = true := by decide +kernel
theorem sub5_752 : sub5 [1, 4, -8] = true := by decide +kernel
theorem sub5_753 : sub5 [1, 4, -7] = true := by decide +kernel
theorem sub5_754 : sub5 [1, 4, -6] = true := by decide +kernel
theorem sub5_755 : sub5 [1, 4, -5] = true := by decide +kernel
theorem sub5_756 : sub5 [1, 4, -4] = true := by decide +kernel
theorem sub5_757 : sub5 [1, 4, -3] = true := by decide +kernel
theorem sub5_758 : sub5 [1, 4, -2] = true := by decide +kernel
theorem sub5_759 : sub5 [1, 4, -1] = true := by decide +kernel
theorem sub5_760 : sub5 [1, 4, 0] = true := by decide +kernel
theorem sub5_761 : sub5 [1, 4, 1] = true := by decide +kernel
theorem sub5_762 : sub5 [1, 4, 2] = true := by decide +kernel
theorem sub5_763 : sub5 [1, 4, 3] = true := by decide +kernel
theorem sub5_764 : sub5 [1, 4, 4] = true := by decide +kernel
theorem sub5_765 : sub5 [1, 4, 5] = true := by decide +kernel
theorem sub5_766 : sub5 [1, 4, 6] = true := by decide +kernel
theorem sub5_767 : sub5 [1, 5] = true := by decide +kernel
theorem sb5_23 : ∀ q ∈ blk5_23, sub5 q = true := by
  unfold blk5_23
  exact List.forall_mem_cons.2 ⟨sub5_736, List.forall_mem_cons.2 ⟨sub5_737, List.forall_mem_cons.2 ⟨sub5_738, List.forall_mem_cons.2 ⟨sub5_739, List.forall_mem_cons.2 ⟨sub5_740, List.forall_mem_cons.2 ⟨sub5_741, List.forall_mem_cons.2 ⟨sub5_742, List.forall_mem_cons.2 ⟨sub5_743, List.forall_mem_cons.2 ⟨sub5_744, List.forall_mem_cons.2 ⟨sub5_745, List.forall_mem_cons.2 ⟨sub5_746, List.forall_mem_cons.2 ⟨sub5_747, List.forall_mem_cons.2 ⟨sub5_748, List.forall_mem_cons.2 ⟨sub5_749, List.forall_mem_cons.2 ⟨sub5_750, List.forall_mem_cons.2 ⟨sub5_751, List.forall_mem_cons.2 ⟨sub5_752, List.forall_mem_cons.2 ⟨sub5_753, List.forall_mem_cons.2 ⟨sub5_754, List.forall_mem_cons.2 ⟨sub5_755, List.forall_mem_cons.2 ⟨sub5_756, List.forall_mem_cons.2 ⟨sub5_757, List.forall_mem_cons.2 ⟨sub5_758, List.forall_mem_cons.2 ⟨sub5_759, List.forall_mem_cons.2 ⟨sub5_760, List.forall_mem_cons.2 ⟨sub5_761, List.forall_mem_cons.2 ⟨sub5_762, List.forall_mem_cons.2 ⟨sub5_763, List.forall_mem_cons.2 ⟨sub5_764, List.forall_mem_cons.2 ⟨sub5_765, List.forall_mem_cons.2 ⟨sub5_766, List.forall_mem_cons.2 ⟨sub5_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_768 : sub5 [1, 6] = true := by decide +kernel
theorem sub5_769 : sub5 [2, -7] = true := by decide +kernel
theorem sub5_770 : sub5 [2, -6] = true := by decide +kernel
theorem sub5_771 : sub5 [2, -5] = true := by decide +kernel
theorem sub5_772 : sub5 [2, -4] = true := by decide +kernel
theorem sub5_773 : sub5 [2, -3, -6] = true := by decide +kernel
theorem sub5_774 : sub5 [2, -3, -5] = true := by decide +kernel
theorem sub5_775 : sub5 [2, -3, -4] = true := by decide +kernel
theorem sub5_776 : sub5 [2, -3, -3] = true := by decide +kernel
theorem sub5_777 : sub5 [2, -3, -2] = true := by decide +kernel
theorem sub5_778 : sub5 [2, -3, -1] = true := by decide +kernel
theorem sub5_779 : sub5 [2, -3, 0] = true := by decide +kernel
theorem sub5_780 : sub5 [2, -3, 1] = true := by decide +kernel
theorem sub5_781 : sub5 [2, -3, 2] = true := by decide +kernel
theorem sub5_782 : sub5 [2, -3, 3] = true := by decide +kernel
theorem sub5_783 : sub5 [2, -3, 4] = true := by decide +kernel
theorem sub5_784 : sub5 [2, -3, 5] = true := by decide +kernel
theorem sub5_785 : sub5 [2, -3, 6] = true := by decide +kernel
theorem sub5_786 : sub5 [2, -3, 7] = true := by decide +kernel
theorem sub5_787 : sub5 [2, -3, 8] = true := by decide +kernel
theorem sub5_788 : sub5 [2, -2, -7] = true := by decide +kernel
theorem sub5_789 : sub5 [2, -2, -6] = true := by decide +kernel
theorem sub5_790 : sub5 [2, -2, -5] = true := by decide +kernel
theorem sub5_791 : sub5 [2, -2, -4] = true := by decide +kernel
theorem sub5_792 : sub5 [2, -2, -3] = true := by decide +kernel
theorem sub5_793 : sub5 [2, -2, -2] = true := by decide +kernel
theorem sub5_794 : sub5 [2, -2, -1] = true := by decide +kernel
theorem sub5_795 : sub5 [2, -2, 0] = true := by decide +kernel
theorem sub5_796 : sub5 [2, -2, 1] = true := by decide +kernel
theorem sub5_797 : sub5 [2, -2, 2] = true := by decide +kernel
theorem sub5_798 : sub5 [2, -2, 3] = true := by decide +kernel
theorem sub5_799 : sub5 [2, -2, 4] = true := by decide +kernel
theorem sb5_24 : ∀ q ∈ blk5_24, sub5 q = true := by
  unfold blk5_24
  exact List.forall_mem_cons.2 ⟨sub5_768, List.forall_mem_cons.2 ⟨sub5_769, List.forall_mem_cons.2 ⟨sub5_770, List.forall_mem_cons.2 ⟨sub5_771, List.forall_mem_cons.2 ⟨sub5_772, List.forall_mem_cons.2 ⟨sub5_773, List.forall_mem_cons.2 ⟨sub5_774, List.forall_mem_cons.2 ⟨sub5_775, List.forall_mem_cons.2 ⟨sub5_776, List.forall_mem_cons.2 ⟨sub5_777, List.forall_mem_cons.2 ⟨sub5_778, List.forall_mem_cons.2 ⟨sub5_779, List.forall_mem_cons.2 ⟨sub5_780, List.forall_mem_cons.2 ⟨sub5_781, List.forall_mem_cons.2 ⟨sub5_782, List.forall_mem_cons.2 ⟨sub5_783, List.forall_mem_cons.2 ⟨sub5_784, List.forall_mem_cons.2 ⟨sub5_785, List.forall_mem_cons.2 ⟨sub5_786, List.forall_mem_cons.2 ⟨sub5_787, List.forall_mem_cons.2 ⟨sub5_788, List.forall_mem_cons.2 ⟨sub5_789, List.forall_mem_cons.2 ⟨sub5_790, List.forall_mem_cons.2 ⟨sub5_791, List.forall_mem_cons.2 ⟨sub5_792, List.forall_mem_cons.2 ⟨sub5_793, List.forall_mem_cons.2 ⟨sub5_794, List.forall_mem_cons.2 ⟨sub5_795, List.forall_mem_cons.2 ⟨sub5_796, List.forall_mem_cons.2 ⟨sub5_797, List.forall_mem_cons.2 ⟨sub5_798, List.forall_mem_cons.2 ⟨sub5_799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_800 : sub5 [2, -2, 5] = true := by decide +kernel
theorem sub5_801 : sub5 [2, -2, 6] = true := by decide +kernel
theorem sub5_802 : sub5 [2, -2, 7] = true := by decide +kernel
theorem sub5_803 : sub5 [2, -2, 8] = true := by decide +kernel
theorem sub5_804 : sub5 [2, -1, -8] = true := by decide +kernel
theorem sub5_805 : sub5 [2, -1, -7] = true := by decide +kernel
theorem sub5_806 : sub5 [2, -1, -6] = true := by decide +kernel
theorem sub5_807 : sub5 [2, -1, -5] = true := by decide +kernel
theorem sub5_808 : sub5 [2, -1, -4] = true := by decide +kernel
theorem sub5_809 : sub5 [2, -1, -3] = true := by decide +kernel
theorem sub5_810 : sub5 [2, -1, -2] = true := by decide +kernel
theorem sub5_811 : sub5 [2, -1, -1] = true := by decide +kernel
theorem sub5_812 : sub5 [2, -1, 0] = true := by decide +kernel
theorem sub5_813 : sub5 [2, -1, 1] = true := by decide +kernel
theorem sub5_814 : sub5 [2, -1, 2] = true := by decide +kernel
theorem sub5_815 : sub5 [2, -1, 3] = true := by decide +kernel
theorem sub5_816 : sub5 [2, -1, 4] = true := by decide +kernel
theorem sub5_817 : sub5 [2, -1, 5] = true := by decide +kernel
theorem sub5_818 : sub5 [2, -1, 6] = true := by decide +kernel
theorem sub5_819 : sub5 [2, -1, 7] = true := by decide +kernel
theorem sub5_820 : sub5 [2, -1, 8] = true := by decide +kernel
theorem sub5_821 : sub5 [2, -1, 9] = true := by decide +kernel
theorem sub5_822 : sub5 [2, 0, -8] = true := by decide +kernel
theorem sub5_823 : sub5 [2, 0, -7] = true := by decide +kernel
theorem sub5_824 : sub5 [2, 0, -6] = true := by decide +kernel
theorem sub5_825 : sub5 [2, 0, -5] = true := by decide +kernel
theorem sub5_826 : sub5 [2, 0, -4] = true := by decide +kernel
theorem sub5_827 : sub5 [2, 0, -3] = true := by decide +kernel
theorem sub5_828 : sub5 [2, 0, -2] = true := by decide +kernel
theorem sub5_829 : sub5 [2, 0, -1] = true := by decide +kernel
theorem sub5_830 : sub5 [2, 0, 0] = true := by decide +kernel
theorem sub5_831 : sub5 [2, 0, 1] = true := by decide +kernel
theorem sb5_25 : ∀ q ∈ blk5_25, sub5 q = true := by
  unfold blk5_25
  exact List.forall_mem_cons.2 ⟨sub5_800, List.forall_mem_cons.2 ⟨sub5_801, List.forall_mem_cons.2 ⟨sub5_802, List.forall_mem_cons.2 ⟨sub5_803, List.forall_mem_cons.2 ⟨sub5_804, List.forall_mem_cons.2 ⟨sub5_805, List.forall_mem_cons.2 ⟨sub5_806, List.forall_mem_cons.2 ⟨sub5_807, List.forall_mem_cons.2 ⟨sub5_808, List.forall_mem_cons.2 ⟨sub5_809, List.forall_mem_cons.2 ⟨sub5_810, List.forall_mem_cons.2 ⟨sub5_811, List.forall_mem_cons.2 ⟨sub5_812, List.forall_mem_cons.2 ⟨sub5_813, List.forall_mem_cons.2 ⟨sub5_814, List.forall_mem_cons.2 ⟨sub5_815, List.forall_mem_cons.2 ⟨sub5_816, List.forall_mem_cons.2 ⟨sub5_817, List.forall_mem_cons.2 ⟨sub5_818, List.forall_mem_cons.2 ⟨sub5_819, List.forall_mem_cons.2 ⟨sub5_820, List.forall_mem_cons.2 ⟨sub5_821, List.forall_mem_cons.2 ⟨sub5_822, List.forall_mem_cons.2 ⟨sub5_823, List.forall_mem_cons.2 ⟨sub5_824, List.forall_mem_cons.2 ⟨sub5_825, List.forall_mem_cons.2 ⟨sub5_826, List.forall_mem_cons.2 ⟨sub5_827, List.forall_mem_cons.2 ⟨sub5_828, List.forall_mem_cons.2 ⟨sub5_829, List.forall_mem_cons.2 ⟨sub5_830, List.forall_mem_cons.2 ⟨sub5_831, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_832 : sub5 [2, 0, 2] = true := by decide +kernel
theorem sub5_833 : sub5 [2, 0, 3] = true := by decide +kernel
theorem sub5_834 : sub5 [2, 0, 4] = true := by decide +kernel
theorem sub5_835 : sub5 [2, 0, 5] = true := by decide +kernel
theorem sub5_836 : sub5 [2, 0, 6] = true := by decide +kernel
theorem sub5_837 : sub5 [2, 0, 7] = true := by decide +kernel
theorem sub5_838 : sub5 [2, 0, 8] = true := by decide +kernel
theorem sub5_839 : sub5 [2, 1, -8] = true := by decide +kernel
theorem sub5_840 : sub5 [2, 1, -7] = true := by decide +kernel
theorem sub5_841 : sub5 [2, 1, -6] = true := by decide +kernel
theorem sub5_842 : sub5 [2, 1, -5] = true := by decide +kernel
theorem sub5_843 : sub5 [2, 1, -4] = true := by decide +kernel
theorem sub5_844 : sub5 [2, 1, -3] = true := by decide +kernel
theorem sub5_845 : sub5 [2, 1, -2] = true := by decide +kernel
theorem sub5_846 : sub5 [2, 1, -1] = true := by decide +kernel
theorem sub5_847 : sub5 [2, 1, 0] = true := by decide +kernel
theorem sub5_848 : sub5 [2, 1, 1] = true := by decide +kernel
theorem sub5_849 : sub5 [2, 1, 2] = true := by decide +kernel
theorem sub5_850 : sub5 [2, 1, 3] = true := by decide +kernel
theorem sub5_851 : sub5 [2, 1, 4] = true := by decide +kernel
theorem sub5_852 : sub5 [2, 1, 5] = true := by decide +kernel
theorem sub5_853 : sub5 [2, 1, 6] = true := by decide +kernel
theorem sub5_854 : sub5 [2, 1, 7] = true := by decide +kernel
theorem sub5_855 : sub5 [2, 1, 8] = true := by decide +kernel
theorem sub5_856 : sub5 [2, 2, -8] = true := by decide +kernel
theorem sub5_857 : sub5 [2, 2, -7] = true := by decide +kernel
theorem sub5_858 : sub5 [2, 2, -6] = true := by decide +kernel
theorem sub5_859 : sub5 [2, 2, -5] = true := by decide +kernel
theorem sub5_860 : sub5 [2, 2, -4] = true := by decide +kernel
theorem sub5_861 : sub5 [2, 2, -3] = true := by decide +kernel
theorem sub5_862 : sub5 [2, 2, -2] = true := by decide +kernel
theorem sub5_863 : sub5 [2, 2, -1] = true := by decide +kernel
theorem sb5_26 : ∀ q ∈ blk5_26, sub5 q = true := by
  unfold blk5_26
  exact List.forall_mem_cons.2 ⟨sub5_832, List.forall_mem_cons.2 ⟨sub5_833, List.forall_mem_cons.2 ⟨sub5_834, List.forall_mem_cons.2 ⟨sub5_835, List.forall_mem_cons.2 ⟨sub5_836, List.forall_mem_cons.2 ⟨sub5_837, List.forall_mem_cons.2 ⟨sub5_838, List.forall_mem_cons.2 ⟨sub5_839, List.forall_mem_cons.2 ⟨sub5_840, List.forall_mem_cons.2 ⟨sub5_841, List.forall_mem_cons.2 ⟨sub5_842, List.forall_mem_cons.2 ⟨sub5_843, List.forall_mem_cons.2 ⟨sub5_844, List.forall_mem_cons.2 ⟨sub5_845, List.forall_mem_cons.2 ⟨sub5_846, List.forall_mem_cons.2 ⟨sub5_847, List.forall_mem_cons.2 ⟨sub5_848, List.forall_mem_cons.2 ⟨sub5_849, List.forall_mem_cons.2 ⟨sub5_850, List.forall_mem_cons.2 ⟨sub5_851, List.forall_mem_cons.2 ⟨sub5_852, List.forall_mem_cons.2 ⟨sub5_853, List.forall_mem_cons.2 ⟨sub5_854, List.forall_mem_cons.2 ⟨sub5_855, List.forall_mem_cons.2 ⟨sub5_856, List.forall_mem_cons.2 ⟨sub5_857, List.forall_mem_cons.2 ⟨sub5_858, List.forall_mem_cons.2 ⟨sub5_859, List.forall_mem_cons.2 ⟨sub5_860, List.forall_mem_cons.2 ⟨sub5_861, List.forall_mem_cons.2 ⟨sub5_862, List.forall_mem_cons.2 ⟨sub5_863, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_864 : sub5 [2, 2, 0] = true := by decide +kernel
theorem sub5_865 : sub5 [2, 2, 1] = true := by decide +kernel
theorem sub5_866 : sub5 [2, 2, 2] = true := by decide +kernel
theorem sub5_867 : sub5 [2, 2, 3] = true := by decide +kernel
theorem sub5_868 : sub5 [2, 2, 4] = true := by decide +kernel
theorem sub5_869 : sub5 [2, 2, 5] = true := by decide +kernel
theorem sub5_870 : sub5 [2, 2, 6] = true := by decide +kernel
theorem sub5_871 : sub5 [2, 2, 7] = true := by decide +kernel
theorem sub5_872 : sub5 [2, 3, -8] = true := by decide +kernel
theorem sub5_873 : sub5 [2, 3, -7] = true := by decide +kernel
theorem sub5_874 : sub5 [2, 3, -6] = true := by decide +kernel
theorem sub5_875 : sub5 [2, 3, -5] = true := by decide +kernel
theorem sub5_876 : sub5 [2, 3, -4] = true := by decide +kernel
theorem sub5_877 : sub5 [2, 3, -3] = true := by decide +kernel
theorem sub5_878 : sub5 [2, 3, -2] = true := by decide +kernel
theorem sub5_879 : sub5 [2, 3, -1] = true := by decide +kernel
theorem sub5_880 : sub5 [2, 3, 0] = true := by decide +kernel
theorem sub5_881 : sub5 [2, 3, 1] = true := by decide +kernel
theorem sub5_882 : sub5 [2, 3, 2] = true := by decide +kernel
theorem sub5_883 : sub5 [2, 3, 3] = true := by decide +kernel
theorem sub5_884 : sub5 [2, 3, 4] = true := by decide +kernel
theorem sub5_885 : sub5 [2, 3, 5] = true := by decide +kernel
theorem sub5_886 : sub5 [2, 3, 6] = true := by decide +kernel
theorem sub5_887 : sub5 [2, 3, 7] = true := by decide +kernel
theorem sub5_888 : sub5 [2, 4] = true := by decide +kernel
theorem sub5_889 : sub5 [2, 5] = true := by decide +kernel
theorem sub5_890 : sub5 [2, 6] = true := by decide +kernel
theorem sub5_891 : sub5 [3, -7] = true := by decide +kernel
theorem sub5_892 : sub5 [3, -6] = true := by decide +kernel
theorem sub5_893 : sub5 [3, -5] = true := by decide +kernel
theorem sub5_894 : sub5 [3, -4] = true := by decide +kernel
theorem sub5_895 : sub5 [3, -3, -6] = true := by decide +kernel
theorem sb5_27 : ∀ q ∈ blk5_27, sub5 q = true := by
  unfold blk5_27
  exact List.forall_mem_cons.2 ⟨sub5_864, List.forall_mem_cons.2 ⟨sub5_865, List.forall_mem_cons.2 ⟨sub5_866, List.forall_mem_cons.2 ⟨sub5_867, List.forall_mem_cons.2 ⟨sub5_868, List.forall_mem_cons.2 ⟨sub5_869, List.forall_mem_cons.2 ⟨sub5_870, List.forall_mem_cons.2 ⟨sub5_871, List.forall_mem_cons.2 ⟨sub5_872, List.forall_mem_cons.2 ⟨sub5_873, List.forall_mem_cons.2 ⟨sub5_874, List.forall_mem_cons.2 ⟨sub5_875, List.forall_mem_cons.2 ⟨sub5_876, List.forall_mem_cons.2 ⟨sub5_877, List.forall_mem_cons.2 ⟨sub5_878, List.forall_mem_cons.2 ⟨sub5_879, List.forall_mem_cons.2 ⟨sub5_880, List.forall_mem_cons.2 ⟨sub5_881, List.forall_mem_cons.2 ⟨sub5_882, List.forall_mem_cons.2 ⟨sub5_883, List.forall_mem_cons.2 ⟨sub5_884, List.forall_mem_cons.2 ⟨sub5_885, List.forall_mem_cons.2 ⟨sub5_886, List.forall_mem_cons.2 ⟨sub5_887, List.forall_mem_cons.2 ⟨sub5_888, List.forall_mem_cons.2 ⟨sub5_889, List.forall_mem_cons.2 ⟨sub5_890, List.forall_mem_cons.2 ⟨sub5_891, List.forall_mem_cons.2 ⟨sub5_892, List.forall_mem_cons.2 ⟨sub5_893, List.forall_mem_cons.2 ⟨sub5_894, List.forall_mem_cons.2 ⟨sub5_895, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_896 : sub5 [3, -3, -5] = true := by decide +kernel
theorem sub5_897 : sub5 [3, -3, -4] = true := by decide +kernel
theorem sub5_898 : sub5 [3, -3, -3] = true := by decide +kernel
theorem sub5_899 : sub5 [3, -3, -2] = true := by decide +kernel
theorem sub5_900 : sub5 [3, -3, -1] = true := by decide +kernel
theorem sub5_901 : sub5 [3, -3, 0] = true := by decide +kernel
theorem sub5_902 : sub5 [3, -3, 1] = true := by decide +kernel
theorem sub5_903 : sub5 [3, -3, 2] = true := by decide +kernel
theorem sub5_904 : sub5 [3, -3, 3] = true := by decide +kernel
theorem sub5_905 : sub5 [3, -3, 4] = true := by decide +kernel
theorem sub5_906 : sub5 [3, -3, 5] = true := by decide +kernel
theorem sub5_907 : sub5 [3, -3, 6] = true := by decide +kernel
theorem sub5_908 : sub5 [3, -3, 7] = true := by decide +kernel
theorem sub5_909 : sub5 [3, -3, 8] = true := by decide +kernel
theorem sub5_910 : sub5 [3, -2, -6] = true := by decide +kernel
theorem sub5_911 : sub5 [3, -2, -5] = true := by decide +kernel
theorem sub5_912 : sub5 [3, -2, -4] = true := by decide +kernel
theorem sub5_913 : sub5 [3, -2, -3] = true := by decide +kernel
theorem sub5_914 : sub5 [3, -2, -2] = true := by decide +kernel
theorem sub5_915 : sub5 [3, -2, -1] = true := by decide +kernel
theorem sub5_916 : sub5 [3, -2, 0] = true := by decide +kernel
theorem sub5_917 : sub5 [3, -2, 1] = true := by decide +kernel
theorem sub5_918 : sub5 [3, -2, 2] = true := by decide +kernel
theorem sub5_919 : sub5 [3, -2, 3] = true := by decide +kernel
theorem sub5_920 : sub5 [3, -2, 4] = true := by decide +kernel
theorem sub5_921 : sub5 [3, -2, 5] = true := by decide +kernel
theorem sub5_922 : sub5 [3, -2, 6] = true := by decide +kernel
theorem sub5_923 : sub5 [3, -2, 7] = true := by decide +kernel
theorem sub5_924 : sub5 [3, -2, 8] = true := by decide +kernel
theorem sub5_925 : sub5 [3, -1, -7] = true := by decide +kernel
theorem sub5_926 : sub5 [3, -1, -6] = true := by decide +kernel
theorem sub5_927 : sub5 [3, -1, -5] = true := by decide +kernel
theorem sb5_28 : ∀ q ∈ blk5_28, sub5 q = true := by
  unfold blk5_28
  exact List.forall_mem_cons.2 ⟨sub5_896, List.forall_mem_cons.2 ⟨sub5_897, List.forall_mem_cons.2 ⟨sub5_898, List.forall_mem_cons.2 ⟨sub5_899, List.forall_mem_cons.2 ⟨sub5_900, List.forall_mem_cons.2 ⟨sub5_901, List.forall_mem_cons.2 ⟨sub5_902, List.forall_mem_cons.2 ⟨sub5_903, List.forall_mem_cons.2 ⟨sub5_904, List.forall_mem_cons.2 ⟨sub5_905, List.forall_mem_cons.2 ⟨sub5_906, List.forall_mem_cons.2 ⟨sub5_907, List.forall_mem_cons.2 ⟨sub5_908, List.forall_mem_cons.2 ⟨sub5_909, List.forall_mem_cons.2 ⟨sub5_910, List.forall_mem_cons.2 ⟨sub5_911, List.forall_mem_cons.2 ⟨sub5_912, List.forall_mem_cons.2 ⟨sub5_913, List.forall_mem_cons.2 ⟨sub5_914, List.forall_mem_cons.2 ⟨sub5_915, List.forall_mem_cons.2 ⟨sub5_916, List.forall_mem_cons.2 ⟨sub5_917, List.forall_mem_cons.2 ⟨sub5_918, List.forall_mem_cons.2 ⟨sub5_919, List.forall_mem_cons.2 ⟨sub5_920, List.forall_mem_cons.2 ⟨sub5_921, List.forall_mem_cons.2 ⟨sub5_922, List.forall_mem_cons.2 ⟨sub5_923, List.forall_mem_cons.2 ⟨sub5_924, List.forall_mem_cons.2 ⟨sub5_925, List.forall_mem_cons.2 ⟨sub5_926, List.forall_mem_cons.2 ⟨sub5_927, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_928 : sub5 [3, -1, -4] = true := by decide +kernel
theorem sub5_929 : sub5 [3, -1, -3] = true := by decide +kernel
theorem sub5_930 : sub5 [3, -1, -2] = true := by decide +kernel
theorem sub5_931 : sub5 [3, -1, -1] = true := by decide +kernel
theorem sub5_932 : sub5 [3, -1, 0] = true := by decide +kernel
theorem sub5_933 : sub5 [3, -1, 1] = true := by decide +kernel
theorem sub5_934 : sub5 [3, -1, 2] = true := by decide +kernel
theorem sub5_935 : sub5 [3, -1, 3] = true := by decide +kernel
theorem sub5_936 : sub5 [3, -1, 4] = true := by decide +kernel
theorem sub5_937 : sub5 [3, -1, 5] = true := by decide +kernel
theorem sub5_938 : sub5 [3, -1, 6] = true := by decide +kernel
theorem sub5_939 : sub5 [3, -1, 7] = true := by decide +kernel
theorem sub5_940 : sub5 [3, -1, 8] = true := by decide +kernel
theorem sub5_941 : sub5 [3, 0, -7] = true := by decide +kernel
theorem sub5_942 : sub5 [3, 0, -6] = true := by decide +kernel
theorem sub5_943 : sub5 [3, 0, -5] = true := by decide +kernel
theorem sub5_944 : sub5 [3, 0, -4] = true := by decide +kernel
theorem sub5_945 : sub5 [3, 0, -3] = true := by decide +kernel
theorem sub5_946 : sub5 [3, 0, -2] = true := by decide +kernel
theorem sub5_947 : sub5 [3, 0, -1] = true := by decide +kernel
theorem sub5_948 : sub5 [3, 0, 0] = true := by decide +kernel
theorem sub5_949 : sub5 [3, 0, 1] = true := by decide +kernel
theorem sub5_950 : sub5 [3, 0, 2] = true := by decide +kernel
theorem sub5_951 : sub5 [3, 0, 3] = true := by decide +kernel
theorem sub5_952 : sub5 [3, 0, 4] = true := by decide +kernel
theorem sub5_953 : sub5 [3, 0, 5] = true := by decide +kernel
theorem sub5_954 : sub5 [3, 0, 6] = true := by decide +kernel
theorem sub5_955 : sub5 [3, 0, 7] = true := by decide +kernel
theorem sub5_956 : sub5 [3, 0, 8] = true := by decide +kernel
theorem sub5_957 : sub5 [3, 1, -7] = true := by decide +kernel
theorem sub5_958 : sub5 [3, 1, -6] = true := by decide +kernel
theorem sub5_959 : sub5 [3, 1, -5] = true := by decide +kernel
theorem sb5_29 : ∀ q ∈ blk5_29, sub5 q = true := by
  unfold blk5_29
  exact List.forall_mem_cons.2 ⟨sub5_928, List.forall_mem_cons.2 ⟨sub5_929, List.forall_mem_cons.2 ⟨sub5_930, List.forall_mem_cons.2 ⟨sub5_931, List.forall_mem_cons.2 ⟨sub5_932, List.forall_mem_cons.2 ⟨sub5_933, List.forall_mem_cons.2 ⟨sub5_934, List.forall_mem_cons.2 ⟨sub5_935, List.forall_mem_cons.2 ⟨sub5_936, List.forall_mem_cons.2 ⟨sub5_937, List.forall_mem_cons.2 ⟨sub5_938, List.forall_mem_cons.2 ⟨sub5_939, List.forall_mem_cons.2 ⟨sub5_940, List.forall_mem_cons.2 ⟨sub5_941, List.forall_mem_cons.2 ⟨sub5_942, List.forall_mem_cons.2 ⟨sub5_943, List.forall_mem_cons.2 ⟨sub5_944, List.forall_mem_cons.2 ⟨sub5_945, List.forall_mem_cons.2 ⟨sub5_946, List.forall_mem_cons.2 ⟨sub5_947, List.forall_mem_cons.2 ⟨sub5_948, List.forall_mem_cons.2 ⟨sub5_949, List.forall_mem_cons.2 ⟨sub5_950, List.forall_mem_cons.2 ⟨sub5_951, List.forall_mem_cons.2 ⟨sub5_952, List.forall_mem_cons.2 ⟨sub5_953, List.forall_mem_cons.2 ⟨sub5_954, List.forall_mem_cons.2 ⟨sub5_955, List.forall_mem_cons.2 ⟨sub5_956, List.forall_mem_cons.2 ⟨sub5_957, List.forall_mem_cons.2 ⟨sub5_958, List.forall_mem_cons.2 ⟨sub5_959, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_960 : sub5 [3, 1, -4] = true := by decide +kernel
theorem sub5_961 : sub5 [3, 1, -3] = true := by decide +kernel
theorem sub5_962 : sub5 [3, 1, -2] = true := by decide +kernel
theorem sub5_963 : sub5 [3, 1, -1] = true := by decide +kernel
theorem sub5_964 : sub5 [3, 1, 0] = true := by decide +kernel
theorem sub5_965 : sub5 [3, 1, 1] = true := by decide +kernel
theorem sub5_966 : sub5 [3, 1, 2] = true := by decide +kernel
theorem sub5_967 : sub5 [3, 1, 3] = true := by decide +kernel
theorem sub5_968 : sub5 [3, 1, 4] = true := by decide +kernel
theorem sub5_969 : sub5 [3, 1, 5] = true := by decide +kernel
theorem sub5_970 : sub5 [3, 1, 6] = true := by decide +kernel
theorem sub5_971 : sub5 [3, 1, 7] = true := by decide +kernel
theorem sub5_972 : sub5 [3, 1, 8] = true := by decide +kernel
theorem sub5_973 : sub5 [3, 2, -7] = true := by decide +kernel
theorem sub5_974 : sub5 [3, 2, -6] = true := by decide +kernel
theorem sub5_975 : sub5 [3, 2, -5] = true := by decide +kernel
theorem sub5_976 : sub5 [3, 2, -4] = true := by decide +kernel
theorem sub5_977 : sub5 [3, 2, -3] = true := by decide +kernel
theorem sub5_978 : sub5 [3, 2, -2] = true := by decide +kernel
theorem sub5_979 : sub5 [3, 2, -1] = true := by decide +kernel
theorem sub5_980 : sub5 [3, 2, 0] = true := by decide +kernel
theorem sub5_981 : sub5 [3, 2, 1] = true := by decide +kernel
theorem sub5_982 : sub5 [3, 2, 2] = true := by decide +kernel
theorem sub5_983 : sub5 [3, 2, 3] = true := by decide +kernel
theorem sub5_984 : sub5 [3, 2, 4] = true := by decide +kernel
theorem sub5_985 : sub5 [3, 2, 5] = true := by decide +kernel
theorem sub5_986 : sub5 [3, 2, 6] = true := by decide +kernel
theorem sub5_987 : sub5 [3, 2, 7] = true := by decide +kernel
theorem sub5_988 : sub5 [3, 3] = true := by decide +kernel
theorem sub5_989 : sub5 [3, 4] = true := by decide +kernel
theorem sub5_990 : sub5 [3, 5] = true := by decide +kernel
theorem sub5_991 : sub5 [4, -6] = true := by decide +kernel
theorem sb5_30 : ∀ q ∈ blk5_30, sub5 q = true := by
  unfold blk5_30
  exact List.forall_mem_cons.2 ⟨sub5_960, List.forall_mem_cons.2 ⟨sub5_961, List.forall_mem_cons.2 ⟨sub5_962, List.forall_mem_cons.2 ⟨sub5_963, List.forall_mem_cons.2 ⟨sub5_964, List.forall_mem_cons.2 ⟨sub5_965, List.forall_mem_cons.2 ⟨sub5_966, List.forall_mem_cons.2 ⟨sub5_967, List.forall_mem_cons.2 ⟨sub5_968, List.forall_mem_cons.2 ⟨sub5_969, List.forall_mem_cons.2 ⟨sub5_970, List.forall_mem_cons.2 ⟨sub5_971, List.forall_mem_cons.2 ⟨sub5_972, List.forall_mem_cons.2 ⟨sub5_973, List.forall_mem_cons.2 ⟨sub5_974, List.forall_mem_cons.2 ⟨sub5_975, List.forall_mem_cons.2 ⟨sub5_976, List.forall_mem_cons.2 ⟨sub5_977, List.forall_mem_cons.2 ⟨sub5_978, List.forall_mem_cons.2 ⟨sub5_979, List.forall_mem_cons.2 ⟨sub5_980, List.forall_mem_cons.2 ⟨sub5_981, List.forall_mem_cons.2 ⟨sub5_982, List.forall_mem_cons.2 ⟨sub5_983, List.forall_mem_cons.2 ⟨sub5_984, List.forall_mem_cons.2 ⟨sub5_985, List.forall_mem_cons.2 ⟨sub5_986, List.forall_mem_cons.2 ⟨sub5_987, List.forall_mem_cons.2 ⟨sub5_988, List.forall_mem_cons.2 ⟨sub5_989, List.forall_mem_cons.2 ⟨sub5_990, List.forall_mem_cons.2 ⟨sub5_991, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_992 : sub5 [4, -5] = true := by decide +kernel
theorem sub5_993 : sub5 [4, -4] = true := by decide +kernel
theorem sub5_994 : sub5 [4, -3] = true := by decide +kernel
theorem sub5_995 : sub5 [4, -2, -5] = true := by decide +kernel
theorem sub5_996 : sub5 [4, -2, -4] = true := by decide +kernel
theorem sub5_997 : sub5 [4, -2, -3] = true := by decide +kernel
theorem sub5_998 : sub5 [4, -2, -2] = true := by decide +kernel
theorem sub5_999 : sub5 [4, -2, -1] = true := by decide +kernel
theorem sub5_1000 : sub5 [4, -2, 0] = true := by decide +kernel
theorem sub5_1001 : sub5 [4, -2, 1] = true := by decide +kernel
theorem sub5_1002 : sub5 [4, -2, 2] = true := by decide +kernel
theorem sub5_1003 : sub5 [4, -2, 3] = true := by decide +kernel
theorem sub5_1004 : sub5 [4, -2, 4] = true := by decide +kernel
theorem sub5_1005 : sub5 [4, -2, 5] = true := by decide +kernel
theorem sub5_1006 : sub5 [4, -2, 6] = true := by decide +kernel
theorem sub5_1007 : sub5 [4, -2, 7] = true := by decide +kernel
theorem sub5_1008 : sub5 [4, -2, 8] = true := by decide +kernel
theorem sub5_1009 : sub5 [4, -1, -6] = true := by decide +kernel
theorem sub5_1010 : sub5 [4, -1, -5] = true := by decide +kernel
theorem sub5_1011 : sub5 [4, -1, -4] = true := by decide +kernel
theorem sub5_1012 : sub5 [4, -1, -3] = true := by decide +kernel
theorem sub5_1013 : sub5 [4, -1, -2] = true := by decide +kernel
theorem sub5_1014 : sub5 [4, -1, -1] = true := by decide +kernel
theorem sub5_1015 : sub5 [4, -1, 0] = true := by decide +kernel
theorem sub5_1016 : sub5 [4, -1, 1] = true := by decide +kernel
theorem sub5_1017 : sub5 [4, -1, 2] = true := by decide +kernel
theorem sub5_1018 : sub5 [4, -1, 3] = true := by decide +kernel
theorem sub5_1019 : sub5 [4, -1, 4] = true := by decide +kernel
theorem sub5_1020 : sub5 [4, -1, 5] = true := by decide +kernel
theorem sub5_1021 : sub5 [4, -1, 6] = true := by decide +kernel
theorem sub5_1022 : sub5 [4, -1, 7] = true := by decide +kernel
theorem sub5_1023 : sub5 [4, -1, 8] = true := by decide +kernel
theorem sb5_31 : ∀ q ∈ blk5_31, sub5 q = true := by
  unfold blk5_31
  exact List.forall_mem_cons.2 ⟨sub5_992, List.forall_mem_cons.2 ⟨sub5_993, List.forall_mem_cons.2 ⟨sub5_994, List.forall_mem_cons.2 ⟨sub5_995, List.forall_mem_cons.2 ⟨sub5_996, List.forall_mem_cons.2 ⟨sub5_997, List.forall_mem_cons.2 ⟨sub5_998, List.forall_mem_cons.2 ⟨sub5_999, List.forall_mem_cons.2 ⟨sub5_1000, List.forall_mem_cons.2 ⟨sub5_1001, List.forall_mem_cons.2 ⟨sub5_1002, List.forall_mem_cons.2 ⟨sub5_1003, List.forall_mem_cons.2 ⟨sub5_1004, List.forall_mem_cons.2 ⟨sub5_1005, List.forall_mem_cons.2 ⟨sub5_1006, List.forall_mem_cons.2 ⟨sub5_1007, List.forall_mem_cons.2 ⟨sub5_1008, List.forall_mem_cons.2 ⟨sub5_1009, List.forall_mem_cons.2 ⟨sub5_1010, List.forall_mem_cons.2 ⟨sub5_1011, List.forall_mem_cons.2 ⟨sub5_1012, List.forall_mem_cons.2 ⟨sub5_1013, List.forall_mem_cons.2 ⟨sub5_1014, List.forall_mem_cons.2 ⟨sub5_1015, List.forall_mem_cons.2 ⟨sub5_1016, List.forall_mem_cons.2 ⟨sub5_1017, List.forall_mem_cons.2 ⟨sub5_1018, List.forall_mem_cons.2 ⟨sub5_1019, List.forall_mem_cons.2 ⟨sub5_1020, List.forall_mem_cons.2 ⟨sub5_1021, List.forall_mem_cons.2 ⟨sub5_1022, List.forall_mem_cons.2 ⟨sub5_1023, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_1024 : sub5 [4, 0, -6] = true := by decide +kernel
theorem sub5_1025 : sub5 [4, 0, -5] = true := by decide +kernel
theorem sub5_1026 : sub5 [4, 0, -4] = true := by decide +kernel
theorem sub5_1027 : sub5 [4, 0, -3] = true := by decide +kernel
theorem sub5_1028 : sub5 [4, 0, -2] = true := by decide +kernel
theorem sub5_1029 : sub5 [4, 0, -1] = true := by decide +kernel
theorem sub5_1030 : sub5 [4, 0, 0] = true := by decide +kernel
theorem sub5_1031 : sub5 [4, 0, 1] = true := by decide +kernel
theorem sub5_1032 : sub5 [4, 0, 2] = true := by decide +kernel
theorem sub5_1033 : sub5 [4, 0, 3] = true := by decide +kernel
theorem sub5_1034 : sub5 [4, 0, 4] = true := by decide +kernel
theorem sub5_1035 : sub5 [4, 0, 5] = true := by decide +kernel
theorem sub5_1036 : sub5 [4, 0, 6] = true := by decide +kernel
theorem sub5_1037 : sub5 [4, 0, 7] = true := by decide +kernel
theorem sub5_1038 : sub5 [4, 0, 8] = true := by decide +kernel
theorem sub5_1039 : sub5 [4, 1, -6] = true := by decide +kernel
theorem sub5_1040 : sub5 [4, 1, -5] = true := by decide +kernel
theorem sub5_1041 : sub5 [4, 1, -4] = true := by decide +kernel
theorem sub5_1042 : sub5 [4, 1, -3] = true := by decide +kernel
theorem sub5_1043 : sub5 [4, 1, -2] = true := by decide +kernel
theorem sub5_1044 : sub5 [4, 1, -1] = true := by decide +kernel
theorem sub5_1045 : sub5 [4, 1, 0] = true := by decide +kernel
theorem sub5_1046 : sub5 [4, 1, 1] = true := by decide +kernel
theorem sub5_1047 : sub5 [4, 1, 2] = true := by decide +kernel
theorem sub5_1048 : sub5 [4, 1, 3] = true := by decide +kernel
theorem sub5_1049 : sub5 [4, 1, 4] = true := by decide +kernel
theorem sub5_1050 : sub5 [4, 1, 5] = true := by decide +kernel
theorem sub5_1051 : sub5 [4, 1, 6] = true := by decide +kernel
theorem sub5_1052 : sub5 [4, 1, 7] = true := by decide +kernel
theorem sub5_1053 : sub5 [4, 2] = true := by decide +kernel
theorem sub5_1054 : sub5 [4, 3] = true := by decide +kernel
theorem sub5_1055 : sub5 [4, 4] = true := by decide +kernel
theorem sb5_32 : ∀ q ∈ blk5_32, sub5 q = true := by
  unfold blk5_32
  exact List.forall_mem_cons.2 ⟨sub5_1024, List.forall_mem_cons.2 ⟨sub5_1025, List.forall_mem_cons.2 ⟨sub5_1026, List.forall_mem_cons.2 ⟨sub5_1027, List.forall_mem_cons.2 ⟨sub5_1028, List.forall_mem_cons.2 ⟨sub5_1029, List.forall_mem_cons.2 ⟨sub5_1030, List.forall_mem_cons.2 ⟨sub5_1031, List.forall_mem_cons.2 ⟨sub5_1032, List.forall_mem_cons.2 ⟨sub5_1033, List.forall_mem_cons.2 ⟨sub5_1034, List.forall_mem_cons.2 ⟨sub5_1035, List.forall_mem_cons.2 ⟨sub5_1036, List.forall_mem_cons.2 ⟨sub5_1037, List.forall_mem_cons.2 ⟨sub5_1038, List.forall_mem_cons.2 ⟨sub5_1039, List.forall_mem_cons.2 ⟨sub5_1040, List.forall_mem_cons.2 ⟨sub5_1041, List.forall_mem_cons.2 ⟨sub5_1042, List.forall_mem_cons.2 ⟨sub5_1043, List.forall_mem_cons.2 ⟨sub5_1044, List.forall_mem_cons.2 ⟨sub5_1045, List.forall_mem_cons.2 ⟨sub5_1046, List.forall_mem_cons.2 ⟨sub5_1047, List.forall_mem_cons.2 ⟨sub5_1048, List.forall_mem_cons.2 ⟨sub5_1049, List.forall_mem_cons.2 ⟨sub5_1050, List.forall_mem_cons.2 ⟨sub5_1051, List.forall_mem_cons.2 ⟨sub5_1052, List.forall_mem_cons.2 ⟨sub5_1053, List.forall_mem_cons.2 ⟨sub5_1054, List.forall_mem_cons.2 ⟨sub5_1055, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_1056 : sub5 [4, 5] = true := by decide +kernel
theorem sub5_1057 : sub5 [5, -6] = true := by decide +kernel
theorem sub5_1058 : sub5 [5, -5] = true := by decide +kernel
theorem sub5_1059 : sub5 [5, -4] = true := by decide +kernel
theorem sub5_1060 : sub5 [5, -3] = true := by decide +kernel
theorem sub5_1061 : sub5 [5, -2] = true := by decide +kernel
theorem sub5_1062 : sub5 [5, -1] = true := by decide +kernel
theorem sub5_1063 : sub5 [5, 0] = true := by decide +kernel
theorem sub5_1064 : sub5 [5, 1] = true := by decide +kernel
theorem sub5_1065 : sub5 [5, 2] = true := by decide +kernel
theorem sub5_1066 : sub5 [5, 3] = true := by decide +kernel
theorem sub5_1067 : sub5 [5, 4] = true := by decide +kernel
theorem sub5_1068 : sub5 [6, -4] = true := by decide +kernel
theorem sub5_1069 : sub5 [6, -3] = true := by decide +kernel
theorem sub5_1070 : sub5 [6, -2] = true := by decide +kernel
theorem sub5_1071 : sub5 [6, -1] = true := by decide +kernel
theorem sub5_1072 : sub5 [6, 0] = true := by decide +kernel
theorem sub5_1073 : sub5 [6, 1] = true := by decide +kernel
theorem sub5_1074 : sub5 [6, 2] = true := by decide +kernel
theorem sub5_1075 : sub5 [6, 3] = true := by decide +kernel
theorem sub5_1076 : sub5 [7] = true := by decide +kernel
theorem sb5_33 : ∀ q ∈ blk5_33, sub5 q = true := by
  unfold blk5_33
  exact List.forall_mem_cons.2 ⟨sub5_1056, List.forall_mem_cons.2 ⟨sub5_1057, List.forall_mem_cons.2 ⟨sub5_1058, List.forall_mem_cons.2 ⟨sub5_1059, List.forall_mem_cons.2 ⟨sub5_1060, List.forall_mem_cons.2 ⟨sub5_1061, List.forall_mem_cons.2 ⟨sub5_1062, List.forall_mem_cons.2 ⟨sub5_1063, List.forall_mem_cons.2 ⟨sub5_1064, List.forall_mem_cons.2 ⟨sub5_1065, List.forall_mem_cons.2 ⟨sub5_1066, List.forall_mem_cons.2 ⟨sub5_1067, List.forall_mem_cons.2 ⟨sub5_1068, List.forall_mem_cons.2 ⟨sub5_1069, List.forall_mem_cons.2 ⟨sub5_1070, List.forall_mem_cons.2 ⟨sub5_1071, List.forall_mem_cons.2 ⟨sub5_1072, List.forall_mem_cons.2 ⟨sub5_1073, List.forall_mem_cons.2 ⟨sub5_1074, List.forall_mem_cons.2 ⟨sub5_1075, List.forall_mem_cons.2 ⟨sub5_1076, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C047
