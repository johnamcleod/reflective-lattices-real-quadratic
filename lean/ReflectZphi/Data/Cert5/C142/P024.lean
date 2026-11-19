import ReflectZphi.Data.Cert5.C142.Base

namespace ReflectZphi.Data.Cert5.C142

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd13_2_768 : subd13_2 [2, -1, 0] = true := by decide +kernel
theorem subd13_2_769 : subd13_2 [2, -1, 1] = true := by decide +kernel
theorem subd13_2_770 : subd13_2 [2, -1, 2] = true := by decide +kernel
theorem subd13_2_771 : subd13_2 [2, -1, 3] = true := by decide +kernel
theorem subd13_2_772 : subd13_2 [2, -1, 4] = true := by decide +kernel
theorem subd13_2_773 : subd13_2 [2, -1, 5] = true := by decide +kernel
theorem subd13_2_774 : subd13_2 [2, -1, 6] = true := by decide +kernel
theorem subd13_2_775 : subd13_2 [2, -1, 7] = true := by decide +kernel
theorem subd13_2_776 : subd13_2 [2, -1, 8] = true := by decide +kernel
theorem subd13_2_777 : subd13_2 [2, -1, 9] = true := by decide +kernel
theorem subd13_2_778 : subd13_2 [2, -1, 10] = true := by decide +kernel
theorem subd13_2_779 : subd13_2 [2, 0, -11] = true := by decide +kernel
theorem subd13_2_780 : subd13_2 [2, 0, -10] = true := by decide +kernel
theorem subd13_2_781 : subd13_2 [2, 0, -9] = true := by decide +kernel
theorem subd13_2_782 : subd13_2 [2, 0, -8] = true := by decide +kernel
theorem subd13_2_783 : subd13_2 [2, 0, -7] = true := by decide +kernel
theorem subd13_2_784 : subd13_2 [2, 0, -6] = true := by decide +kernel
theorem subd13_2_785 : subd13_2 [2, 0, -5] = true := by decide +kernel
theorem subd13_2_786 : subd13_2 [2, 0, -4] = true := by decide +kernel
theorem subd13_2_787 : subd13_2 [2, 0, -3] = true := by decide +kernel
theorem subd13_2_788 : subd13_2 [2, 0, -2] = true := by decide +kernel
theorem subd13_2_789 : subd13_2 [2, 0, -1] = true := by decide +kernel
theorem subd13_2_790 : subd13_2 [2, 0, 0] = true := by decide +kernel
theorem subd13_2_791 : subd13_2 [2, 0, 1] = true := by decide +kernel
theorem subd13_2_792 : subd13_2 [2, 0, 2] = true := by decide +kernel
theorem subd13_2_793 : subd13_2 [2, 0, 3] = true := by decide +kernel
theorem subd13_2_794 : subd13_2 [2, 0, 4] = true := by decide +kernel
theorem subd13_2_795 : subd13_2 [2, 0, 5] = true := by decide +kernel
theorem subd13_2_796 : subd13_2 [2, 0, 6] = true := by decide +kernel
theorem subd13_2_797 : subd13_2 [2, 0, 7] = true := by decide +kernel
theorem subd13_2_798 : subd13_2 [2, 0, 8] = true := by decide +kernel
theorem subd13_2_799 : subd13_2 [2, 0, 9] = true := by decide +kernel
theorem sbd13_2_24 : ∀ q ∈ blkd13_2_24, subd13_2 q = true := by
  unfold blkd13_2_24
  exact List.forall_mem_cons.2 ⟨subd13_2_768, List.forall_mem_cons.2 ⟨subd13_2_769, List.forall_mem_cons.2 ⟨subd13_2_770, List.forall_mem_cons.2 ⟨subd13_2_771, List.forall_mem_cons.2 ⟨subd13_2_772, List.forall_mem_cons.2 ⟨subd13_2_773, List.forall_mem_cons.2 ⟨subd13_2_774, List.forall_mem_cons.2 ⟨subd13_2_775, List.forall_mem_cons.2 ⟨subd13_2_776, List.forall_mem_cons.2 ⟨subd13_2_777, List.forall_mem_cons.2 ⟨subd13_2_778, List.forall_mem_cons.2 ⟨subd13_2_779, List.forall_mem_cons.2 ⟨subd13_2_780, List.forall_mem_cons.2 ⟨subd13_2_781, List.forall_mem_cons.2 ⟨subd13_2_782, List.forall_mem_cons.2 ⟨subd13_2_783, List.forall_mem_cons.2 ⟨subd13_2_784, List.forall_mem_cons.2 ⟨subd13_2_785, List.forall_mem_cons.2 ⟨subd13_2_786, List.forall_mem_cons.2 ⟨subd13_2_787, List.forall_mem_cons.2 ⟨subd13_2_788, List.forall_mem_cons.2 ⟨subd13_2_789, List.forall_mem_cons.2 ⟨subd13_2_790, List.forall_mem_cons.2 ⟨subd13_2_791, List.forall_mem_cons.2 ⟨subd13_2_792, List.forall_mem_cons.2 ⟨subd13_2_793, List.forall_mem_cons.2 ⟨subd13_2_794, List.forall_mem_cons.2 ⟨subd13_2_795, List.forall_mem_cons.2 ⟨subd13_2_796, List.forall_mem_cons.2 ⟨subd13_2_797, List.forall_mem_cons.2 ⟨subd13_2_798, List.forall_mem_cons.2 ⟨subd13_2_799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_2_800 : subd13_2 [2, 0, 10] = true := by decide +kernel
theorem subd13_2_801 : subd13_2 [2, 1, -11] = true := by decide +kernel
theorem subd13_2_802 : subd13_2 [2, 1, -10] = true := by decide +kernel
theorem subd13_2_803 : subd13_2 [2, 1, -9] = true := by decide +kernel
theorem subd13_2_804 : subd13_2 [2, 1, -8] = true := by decide +kernel
theorem subd13_2_805 : subd13_2 [2, 1, -7] = true := by decide +kernel
theorem subd13_2_806 : subd13_2 [2, 1, -6] = true := by decide +kernel
theorem subd13_2_807 : subd13_2 [2, 1, -5] = true := by decide +kernel
theorem subd13_2_808 : subd13_2 [2, 1, -4] = true := by decide +kernel
theorem subd13_2_809 : subd13_2 [2, 1, -3] = true := by decide +kernel
theorem subd13_2_810 : subd13_2 [2, 1, -2] = true := by decide +kernel
theorem subd13_2_811 : subd13_2 [2, 1, -1] = true := by decide +kernel
theorem subd13_2_812 : subd13_2 [2, 1, 0] = true := by decide +kernel
theorem subd13_2_813 : subd13_2 [2, 1, 1] = true := by decide +kernel
theorem subd13_2_814 : subd13_2 [2, 1, 2] = true := by decide +kernel
theorem subd13_2_815 : subd13_2 [2, 1, 3] = true := by decide +kernel
theorem subd13_2_816 : subd13_2 [2, 1, 4] = true := by decide +kernel
theorem subd13_2_817 : subd13_2 [2, 1, 5] = true := by decide +kernel
theorem subd13_2_818 : subd13_2 [2, 1, 6] = true := by decide +kernel
theorem subd13_2_819 : subd13_2 [2, 1, 7] = true := by decide +kernel
theorem subd13_2_820 : subd13_2 [2, 1, 8] = true := by decide +kernel
theorem subd13_2_821 : subd13_2 [2, 1, 9] = true := by decide +kernel
theorem subd13_2_822 : subd13_2 [2, 2, -11] = true := by decide +kernel
theorem subd13_2_823 : subd13_2 [2, 2, -10] = true := by decide +kernel
theorem subd13_2_824 : subd13_2 [2, 2, -9] = true := by decide +kernel
theorem subd13_2_825 : subd13_2 [2, 2, -8] = true := by decide +kernel
theorem subd13_2_826 : subd13_2 [2, 2, -7] = true := by decide +kernel
theorem subd13_2_827 : subd13_2 [2, 2, -6] = true := by decide +kernel
theorem subd13_2_828 : subd13_2 [2, 2, -5] = true := by decide +kernel
theorem subd13_2_829 : subd13_2 [2, 2, -4] = true := by decide +kernel
theorem subd13_2_830 : subd13_2 [2, 2, -3] = true := by decide +kernel
theorem subd13_2_831 : subd13_2 [2, 2, -2] = true := by decide +kernel
theorem sbd13_2_25 : ∀ q ∈ blkd13_2_25, subd13_2 q = true := by
  unfold blkd13_2_25
  exact List.forall_mem_cons.2 ⟨subd13_2_800, List.forall_mem_cons.2 ⟨subd13_2_801, List.forall_mem_cons.2 ⟨subd13_2_802, List.forall_mem_cons.2 ⟨subd13_2_803, List.forall_mem_cons.2 ⟨subd13_2_804, List.forall_mem_cons.2 ⟨subd13_2_805, List.forall_mem_cons.2 ⟨subd13_2_806, List.forall_mem_cons.2 ⟨subd13_2_807, List.forall_mem_cons.2 ⟨subd13_2_808, List.forall_mem_cons.2 ⟨subd13_2_809, List.forall_mem_cons.2 ⟨subd13_2_810, List.forall_mem_cons.2 ⟨subd13_2_811, List.forall_mem_cons.2 ⟨subd13_2_812, List.forall_mem_cons.2 ⟨subd13_2_813, List.forall_mem_cons.2 ⟨subd13_2_814, List.forall_mem_cons.2 ⟨subd13_2_815, List.forall_mem_cons.2 ⟨subd13_2_816, List.forall_mem_cons.2 ⟨subd13_2_817, List.forall_mem_cons.2 ⟨subd13_2_818, List.forall_mem_cons.2 ⟨subd13_2_819, List.forall_mem_cons.2 ⟨subd13_2_820, List.forall_mem_cons.2 ⟨subd13_2_821, List.forall_mem_cons.2 ⟨subd13_2_822, List.forall_mem_cons.2 ⟨subd13_2_823, List.forall_mem_cons.2 ⟨subd13_2_824, List.forall_mem_cons.2 ⟨subd13_2_825, List.forall_mem_cons.2 ⟨subd13_2_826, List.forall_mem_cons.2 ⟨subd13_2_827, List.forall_mem_cons.2 ⟨subd13_2_828, List.forall_mem_cons.2 ⟨subd13_2_829, List.forall_mem_cons.2 ⟨subd13_2_830, List.forall_mem_cons.2 ⟨subd13_2_831, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_2_832 : subd13_2 [2, 2, -1] = true := by decide +kernel
theorem subd13_2_833 : subd13_2 [2, 2, 0] = true := by decide +kernel
theorem subd13_2_834 : subd13_2 [2, 2, 1] = true := by decide +kernel
theorem subd13_2_835 : subd13_2 [2, 2, 2] = true := by decide +kernel
theorem subd13_2_836 : subd13_2 [2, 2, 3] = true := by decide +kernel
theorem subd13_2_837 : subd13_2 [2, 2, 4] = true := by decide +kernel
theorem subd13_2_838 : subd13_2 [2, 2, 5] = true := by decide +kernel
theorem subd13_2_839 : subd13_2 [2, 2, 6] = true := by decide +kernel
theorem subd13_2_840 : subd13_2 [2, 2, 7] = true := by decide +kernel
theorem subd13_2_841 : subd13_2 [2, 2, 8] = true := by decide +kernel
theorem subd13_2_842 : subd13_2 [2, 3, -10] = true := by decide +kernel
theorem subd13_2_843 : subd13_2 [2, 3, -9] = true := by decide +kernel
theorem subd13_2_844 : subd13_2 [2, 3, -8] = true := by decide +kernel
theorem subd13_2_845 : subd13_2 [2, 3, -7] = true := by decide +kernel
theorem subd13_2_846 : subd13_2 [2, 3, -6] = true := by decide +kernel
theorem subd13_2_847 : subd13_2 [2, 3, -5] = true := by decide +kernel
theorem subd13_2_848 : subd13_2 [2, 3, -4] = true := by decide +kernel
theorem subd13_2_849 : subd13_2 [2, 3, -3] = true := by decide +kernel
theorem subd13_2_850 : subd13_2 [2, 3, -2] = true := by decide +kernel
theorem subd13_2_851 : subd13_2 [2, 3, -1] = true := by decide +kernel
theorem subd13_2_852 : subd13_2 [2, 3, 0] = true := by decide +kernel
theorem subd13_2_853 : subd13_2 [2, 3, 1] = true := by decide +kernel
theorem subd13_2_854 : subd13_2 [2, 3, 2] = true := by decide +kernel
theorem subd13_2_855 : subd13_2 [2, 3, 3] = true := by decide +kernel
theorem subd13_2_856 : subd13_2 [2, 3, 4] = true := by decide +kernel
theorem subd13_2_857 : subd13_2 [2, 3, 5] = true := by decide +kernel
theorem subd13_2_858 : subd13_2 [2, 3, 6] = true := by decide +kernel
theorem subd13_2_859 : subd13_2 [2, 4] = true := by decide +kernel
theorem subd13_2_860 : subd13_2 [3, -4] = true := by decide +kernel
theorem subd13_2_861 : subd13_2 [3, -3] = true := by decide +kernel
theorem subd13_2_862 : subd13_2 [3, -2, -8] = true := by decide +kernel
theorem subd13_2_863 : subd13_2 [3, -2, -7] = true := by decide +kernel
theorem sbd13_2_26 : ∀ q ∈ blkd13_2_26, subd13_2 q = true := by
  unfold blkd13_2_26
  exact List.forall_mem_cons.2 ⟨subd13_2_832, List.forall_mem_cons.2 ⟨subd13_2_833, List.forall_mem_cons.2 ⟨subd13_2_834, List.forall_mem_cons.2 ⟨subd13_2_835, List.forall_mem_cons.2 ⟨subd13_2_836, List.forall_mem_cons.2 ⟨subd13_2_837, List.forall_mem_cons.2 ⟨subd13_2_838, List.forall_mem_cons.2 ⟨subd13_2_839, List.forall_mem_cons.2 ⟨subd13_2_840, List.forall_mem_cons.2 ⟨subd13_2_841, List.forall_mem_cons.2 ⟨subd13_2_842, List.forall_mem_cons.2 ⟨subd13_2_843, List.forall_mem_cons.2 ⟨subd13_2_844, List.forall_mem_cons.2 ⟨subd13_2_845, List.forall_mem_cons.2 ⟨subd13_2_846, List.forall_mem_cons.2 ⟨subd13_2_847, List.forall_mem_cons.2 ⟨subd13_2_848, List.forall_mem_cons.2 ⟨subd13_2_849, List.forall_mem_cons.2 ⟨subd13_2_850, List.forall_mem_cons.2 ⟨subd13_2_851, List.forall_mem_cons.2 ⟨subd13_2_852, List.forall_mem_cons.2 ⟨subd13_2_853, List.forall_mem_cons.2 ⟨subd13_2_854, List.forall_mem_cons.2 ⟨subd13_2_855, List.forall_mem_cons.2 ⟨subd13_2_856, List.forall_mem_cons.2 ⟨subd13_2_857, List.forall_mem_cons.2 ⟨subd13_2_858, List.forall_mem_cons.2 ⟨subd13_2_859, List.forall_mem_cons.2 ⟨subd13_2_860, List.forall_mem_cons.2 ⟨subd13_2_861, List.forall_mem_cons.2 ⟨subd13_2_862, List.forall_mem_cons.2 ⟨subd13_2_863, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_2_864 : subd13_2 [3, -2, -6] = true := by decide +kernel
theorem subd13_2_865 : subd13_2 [3, -2, -5] = true := by decide +kernel
theorem subd13_2_866 : subd13_2 [3, -2, -4] = true := by decide +kernel
theorem subd13_2_867 : subd13_2 [3, -2, -3] = true := by decide +kernel
theorem subd13_2_868 : subd13_2 [3, -2, -2] = true := by decide +kernel
theorem subd13_2_869 : subd13_2 [3, -2, -1] = true := by decide +kernel
theorem subd13_2_870 : subd13_2 [3, -2, 0] = true := by decide +kernel
theorem subd13_2_871 : subd13_2 [3, -2, 1] = true := by decide +kernel
theorem subd13_2_872 : subd13_2 [3, -2, 2] = true := by decide +kernel
theorem subd13_2_873 : subd13_2 [3, -2, 3] = true := by decide +kernel
theorem subd13_2_874 : subd13_2 [3, -2, 4] = true := by decide +kernel
theorem subd13_2_875 : subd13_2 [3, -2, 5] = true := by decide +kernel
theorem subd13_2_876 : subd13_2 [3, -2, 6] = true := by decide +kernel
theorem subd13_2_877 : subd13_2 [3, -2, 7] = true := by decide +kernel
theorem subd13_2_878 : subd13_2 [3, -2, 8] = true := by decide +kernel
theorem subd13_2_879 : subd13_2 [3, -1, -9] = true := by decide +kernel
theorem subd13_2_880 : subd13_2 [3, -1, -8] = true := by decide +kernel
theorem subd13_2_881 : subd13_2 [3, -1, -7] = true := by decide +kernel
theorem subd13_2_882 : subd13_2 [3, -1, -6] = true := by decide +kernel
theorem subd13_2_883 : subd13_2 [3, -1, -5] = true := by decide +kernel
theorem subd13_2_884 : subd13_2 [3, -1, -4] = true := by decide +kernel
theorem subd13_2_885 : subd13_2 [3, -1, -3] = true := by decide +kernel
theorem subd13_2_886 : subd13_2 [3, -1, -2] = true := by decide +kernel
theorem subd13_2_887 : subd13_2 [3, -1, -1] = true := by decide +kernel
theorem subd13_2_888 : subd13_2 [3, -1, 0] = true := by decide +kernel
theorem subd13_2_889 : subd13_2 [3, -1, 1] = true := by decide +kernel
theorem subd13_2_890 : subd13_2 [3, -1, 2] = true := by decide +kernel
theorem subd13_2_891 : subd13_2 [3, -1, 3] = true := by decide +kernel
theorem subd13_2_892 : subd13_2 [3, -1, 4] = true := by decide +kernel
theorem subd13_2_893 : subd13_2 [3, -1, 5] = true := by decide +kernel
theorem subd13_2_894 : subd13_2 [3, -1, 6] = true := by decide +kernel
theorem subd13_2_895 : subd13_2 [3, -1, 7] = true := by decide +kernel
theorem sbd13_2_27 : ∀ q ∈ blkd13_2_27, subd13_2 q = true := by
  unfold blkd13_2_27
  exact List.forall_mem_cons.2 ⟨subd13_2_864, List.forall_mem_cons.2 ⟨subd13_2_865, List.forall_mem_cons.2 ⟨subd13_2_866, List.forall_mem_cons.2 ⟨subd13_2_867, List.forall_mem_cons.2 ⟨subd13_2_868, List.forall_mem_cons.2 ⟨subd13_2_869, List.forall_mem_cons.2 ⟨subd13_2_870, List.forall_mem_cons.2 ⟨subd13_2_871, List.forall_mem_cons.2 ⟨subd13_2_872, List.forall_mem_cons.2 ⟨subd13_2_873, List.forall_mem_cons.2 ⟨subd13_2_874, List.forall_mem_cons.2 ⟨subd13_2_875, List.forall_mem_cons.2 ⟨subd13_2_876, List.forall_mem_cons.2 ⟨subd13_2_877, List.forall_mem_cons.2 ⟨subd13_2_878, List.forall_mem_cons.2 ⟨subd13_2_879, List.forall_mem_cons.2 ⟨subd13_2_880, List.forall_mem_cons.2 ⟨subd13_2_881, List.forall_mem_cons.2 ⟨subd13_2_882, List.forall_mem_cons.2 ⟨subd13_2_883, List.forall_mem_cons.2 ⟨subd13_2_884, List.forall_mem_cons.2 ⟨subd13_2_885, List.forall_mem_cons.2 ⟨subd13_2_886, List.forall_mem_cons.2 ⟨subd13_2_887, List.forall_mem_cons.2 ⟨subd13_2_888, List.forall_mem_cons.2 ⟨subd13_2_889, List.forall_mem_cons.2 ⟨subd13_2_890, List.forall_mem_cons.2 ⟨subd13_2_891, List.forall_mem_cons.2 ⟨subd13_2_892, List.forall_mem_cons.2 ⟨subd13_2_893, List.forall_mem_cons.2 ⟨subd13_2_894, List.forall_mem_cons.2 ⟨subd13_2_895, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_2_896 : subd13_2 [3, -1, 8] = true := by decide +kernel
theorem subd13_2_897 : subd13_2 [3, -1, 9] = true := by decide +kernel
theorem subd13_2_898 : subd13_2 [3, 0, -10] = true := by decide +kernel
theorem subd13_2_899 : subd13_2 [3, 0, -9] = true := by decide +kernel
theorem subd13_2_900 : subd13_2 [3, 0, -8] = true := by decide +kernel
theorem subd13_2_901 : subd13_2 [3, 0, -7] = true := by decide +kernel
theorem subd13_2_902 : subd13_2 [3, 0, -6] = true := by decide +kernel
theorem subd13_2_903 : subd13_2 [3, 0, -5] = true := by decide +kernel
theorem subd13_2_904 : subd13_2 [3, 0, -4] = true := by decide +kernel
theorem subd13_2_905 : subd13_2 [3, 0, -3] = true := by decide +kernel
theorem subd13_2_906 : subd13_2 [3, 0, -2] = true := by decide +kernel
theorem subd13_2_907 : subd13_2 [3, 0, -1] = true := by decide +kernel
theorem subd13_2_908 : subd13_2 [3, 0, 0] = true := by decide +kernel
theorem subd13_2_909 : subd13_2 [3, 0, 1] = true := by decide +kernel
theorem subd13_2_910 : subd13_2 [3, 0, 2] = true := by decide +kernel
theorem subd13_2_911 : subd13_2 [3, 0, 3] = true := by decide +kernel
theorem subd13_2_912 : subd13_2 [3, 0, 4] = true := by decide +kernel
theorem subd13_2_913 : subd13_2 [3, 0, 5] = true := by decide +kernel
theorem subd13_2_914 : subd13_2 [3, 0, 6] = true := by decide +kernel
theorem subd13_2_915 : subd13_2 [3, 0, 7] = true := by decide +kernel
theorem subd13_2_916 : subd13_2 [3, 0, 8] = true := by decide +kernel
theorem subd13_2_917 : subd13_2 [3, 0, 9] = true := by decide +kernel
theorem subd13_2_918 : subd13_2 [3, 1, -10] = true := by decide +kernel
theorem subd13_2_919 : subd13_2 [3, 1, -9] = true := by decide +kernel
theorem subd13_2_920 : subd13_2 [3, 1, -8] = true := by decide +kernel
theorem subd13_2_921 : subd13_2 [3, 1, -7] = true := by decide +kernel
theorem subd13_2_922 : subd13_2 [3, 1, -6] = true := by decide +kernel
theorem subd13_2_923 : subd13_2 [3, 1, -5] = true := by decide +kernel
theorem subd13_2_924 : subd13_2 [3, 1, -4] = true := by decide +kernel
theorem subd13_2_925 : subd13_2 [3, 1, -3] = true := by decide +kernel
theorem subd13_2_926 : subd13_2 [3, 1, -2] = true := by decide +kernel
theorem subd13_2_927 : subd13_2 [3, 1, -1] = true := by decide +kernel
theorem sbd13_2_28 : ∀ q ∈ blkd13_2_28, subd13_2 q = true := by
  unfold blkd13_2_28
  exact List.forall_mem_cons.2 ⟨subd13_2_896, List.forall_mem_cons.2 ⟨subd13_2_897, List.forall_mem_cons.2 ⟨subd13_2_898, List.forall_mem_cons.2 ⟨subd13_2_899, List.forall_mem_cons.2 ⟨subd13_2_900, List.forall_mem_cons.2 ⟨subd13_2_901, List.forall_mem_cons.2 ⟨subd13_2_902, List.forall_mem_cons.2 ⟨subd13_2_903, List.forall_mem_cons.2 ⟨subd13_2_904, List.forall_mem_cons.2 ⟨subd13_2_905, List.forall_mem_cons.2 ⟨subd13_2_906, List.forall_mem_cons.2 ⟨subd13_2_907, List.forall_mem_cons.2 ⟨subd13_2_908, List.forall_mem_cons.2 ⟨subd13_2_909, List.forall_mem_cons.2 ⟨subd13_2_910, List.forall_mem_cons.2 ⟨subd13_2_911, List.forall_mem_cons.2 ⟨subd13_2_912, List.forall_mem_cons.2 ⟨subd13_2_913, List.forall_mem_cons.2 ⟨subd13_2_914, List.forall_mem_cons.2 ⟨subd13_2_915, List.forall_mem_cons.2 ⟨subd13_2_916, List.forall_mem_cons.2 ⟨subd13_2_917, List.forall_mem_cons.2 ⟨subd13_2_918, List.forall_mem_cons.2 ⟨subd13_2_919, List.forall_mem_cons.2 ⟨subd13_2_920, List.forall_mem_cons.2 ⟨subd13_2_921, List.forall_mem_cons.2 ⟨subd13_2_922, List.forall_mem_cons.2 ⟨subd13_2_923, List.forall_mem_cons.2 ⟨subd13_2_924, List.forall_mem_cons.2 ⟨subd13_2_925, List.forall_mem_cons.2 ⟨subd13_2_926, List.forall_mem_cons.2 ⟨subd13_2_927, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_2_928 : subd13_2 [3, 1, 0] = true := by decide +kernel
theorem subd13_2_929 : subd13_2 [3, 1, 1] = true := by decide +kernel
theorem subd13_2_930 : subd13_2 [3, 1, 2] = true := by decide +kernel
theorem subd13_2_931 : subd13_2 [3, 1, 3] = true := by decide +kernel
theorem subd13_2_932 : subd13_2 [3, 1, 4] = true := by decide +kernel
theorem subd13_2_933 : subd13_2 [3, 1, 5] = true := by decide +kernel
theorem subd13_2_934 : subd13_2 [3, 1, 6] = true := by decide +kernel
theorem subd13_2_935 : subd13_2 [3, 1, 7] = true := by decide +kernel
theorem subd13_2_936 : subd13_2 [3, 1, 8] = true := by decide +kernel
theorem subd13_2_937 : subd13_2 [3, 2, -9] = true := by decide +kernel
theorem subd13_2_938 : subd13_2 [3, 2, -8] = true := by decide +kernel
theorem subd13_2_939 : subd13_2 [3, 2, -7] = true := by decide +kernel
theorem subd13_2_940 : subd13_2 [3, 2, -6] = true := by decide +kernel
theorem subd13_2_941 : subd13_2 [3, 2, -5] = true := by decide +kernel
theorem subd13_2_942 : subd13_2 [3, 2, -4] = true := by decide +kernel
theorem subd13_2_943 : subd13_2 [3, 2, -3] = true := by decide +kernel
theorem subd13_2_944 : subd13_2 [3, 2, -2] = true := by decide +kernel
theorem subd13_2_945 : subd13_2 [3, 2, -1] = true := by decide +kernel
theorem subd13_2_946 : subd13_2 [3, 2, 0] = true := by decide +kernel
theorem subd13_2_947 : subd13_2 [3, 2, 1] = true := by decide +kernel
theorem subd13_2_948 : subd13_2 [3, 2, 2] = true := by decide +kernel
theorem subd13_2_949 : subd13_2 [3, 2, 3] = true := by decide +kernel
theorem subd13_2_950 : subd13_2 [3, 2, 4] = true := by decide +kernel
theorem subd13_2_951 : subd13_2 [3, 2, 5] = true := by decide +kernel
theorem subd13_2_952 : subd13_2 [3, 2, 6] = true := by decide +kernel
theorem subd13_2_953 : subd13_2 [3, 3] = true := by decide +kernel
theorem subd13_2_954 : subd13_2 [4, -3] = true := by decide +kernel
theorem subd13_2_955 : subd13_2 [4, -2] = true := by decide +kernel
theorem subd13_2_956 : subd13_2 [4, -1] = true := by decide +kernel
theorem subd13_2_957 : subd13_2 [4, 0, -7] = true := by decide +kernel
theorem subd13_2_958 : subd13_2 [4, 0, -6] = true := by decide +kernel
theorem subd13_2_959 : subd13_2 [4, 0, -5] = true := by decide +kernel
theorem sbd13_2_29 : ∀ q ∈ blkd13_2_29, subd13_2 q = true := by
  unfold blkd13_2_29
  exact List.forall_mem_cons.2 ⟨subd13_2_928, List.forall_mem_cons.2 ⟨subd13_2_929, List.forall_mem_cons.2 ⟨subd13_2_930, List.forall_mem_cons.2 ⟨subd13_2_931, List.forall_mem_cons.2 ⟨subd13_2_932, List.forall_mem_cons.2 ⟨subd13_2_933, List.forall_mem_cons.2 ⟨subd13_2_934, List.forall_mem_cons.2 ⟨subd13_2_935, List.forall_mem_cons.2 ⟨subd13_2_936, List.forall_mem_cons.2 ⟨subd13_2_937, List.forall_mem_cons.2 ⟨subd13_2_938, List.forall_mem_cons.2 ⟨subd13_2_939, List.forall_mem_cons.2 ⟨subd13_2_940, List.forall_mem_cons.2 ⟨subd13_2_941, List.forall_mem_cons.2 ⟨subd13_2_942, List.forall_mem_cons.2 ⟨subd13_2_943, List.forall_mem_cons.2 ⟨subd13_2_944, List.forall_mem_cons.2 ⟨subd13_2_945, List.forall_mem_cons.2 ⟨subd13_2_946, List.forall_mem_cons.2 ⟨subd13_2_947, List.forall_mem_cons.2 ⟨subd13_2_948, List.forall_mem_cons.2 ⟨subd13_2_949, List.forall_mem_cons.2 ⟨subd13_2_950, List.forall_mem_cons.2 ⟨subd13_2_951, List.forall_mem_cons.2 ⟨subd13_2_952, List.forall_mem_cons.2 ⟨subd13_2_953, List.forall_mem_cons.2 ⟨subd13_2_954, List.forall_mem_cons.2 ⟨subd13_2_955, List.forall_mem_cons.2 ⟨subd13_2_956, List.forall_mem_cons.2 ⟨subd13_2_957, List.forall_mem_cons.2 ⟨subd13_2_958, List.forall_mem_cons.2 ⟨subd13_2_959, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_2_960 : subd13_2 [4, 0, -4] = true := by decide +kernel
theorem subd13_2_961 : subd13_2 [4, 0, -3] = true := by decide +kernel
theorem subd13_2_962 : subd13_2 [4, 0, -2] = true := by decide +kernel
theorem subd13_2_963 : subd13_2 [4, 0, -1] = true := by decide +kernel
theorem subd13_2_964 : subd13_2 [4, 0, 0] = true := by decide +kernel
theorem subd13_2_965 : subd13_2 [4, 0, 1] = true := by decide +kernel
theorem subd13_2_966 : subd13_2 [4, 0, 2] = true := by decide +kernel
theorem subd13_2_967 : subd13_2 [4, 0, 3] = true := by decide +kernel
theorem subd13_2_968 : subd13_2 [4, 0, 4] = true := by decide +kernel
theorem subd13_2_969 : subd13_2 [4, 0, 5] = true := by decide +kernel
theorem subd13_2_970 : subd13_2 [4, 0, 6] = true := by decide +kernel
theorem subd13_2_971 : subd13_2 [4, 1] = true := by decide +kernel
theorem subd13_2_972 : subd13_2 [4, 2] = true := by decide +kernel
theorem sbd13_2_30 : ∀ q ∈ blkd13_2_30, subd13_2 q = true := by
  unfold blkd13_2_30
  exact List.forall_mem_cons.2 ⟨subd13_2_960, List.forall_mem_cons.2 ⟨subd13_2_961, List.forall_mem_cons.2 ⟨subd13_2_962, List.forall_mem_cons.2 ⟨subd13_2_963, List.forall_mem_cons.2 ⟨subd13_2_964, List.forall_mem_cons.2 ⟨subd13_2_965, List.forall_mem_cons.2 ⟨subd13_2_966, List.forall_mem_cons.2 ⟨subd13_2_967, List.forall_mem_cons.2 ⟨subd13_2_968, List.forall_mem_cons.2 ⟨subd13_2_969, List.forall_mem_cons.2 ⟨subd13_2_970, List.forall_mem_cons.2 ⟨subd13_2_971, List.forall_mem_cons.2 ⟨subd13_2_972, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd13_3 : ldCheck G d13_3.U d13_3.ms ldd13_3 = true := by decide +kernel
theorem pre_okd13_3 : subPre G cell13 d13_3 = true := by decide +kernel
theorem subd13_3_0 : subd13_3 [-2] = true := by decide +kernel
theorem subd13_3_1 : subd13_3 [-1, -3] = true := by decide +kernel
theorem subd13_3_2 : subd13_3 [-1, -2] = true := by decide +kernel
theorem subd13_3_3 : subd13_3 [-1, -1] = true := by decide +kernel
theorem subd13_3_4 : subd13_3 [-1, 0] = true := by decide +kernel
theorem subd13_3_5 : subd13_3 [-1, 1] = true := by decide +kernel
theorem subd13_3_6 : subd13_3 [-1, 2] = true := by decide +kernel
theorem subd13_3_7 : subd13_3 [0, -3] = true := by decide +kernel
theorem subd13_3_8 : subd13_3 [0, -2] = true := by decide +kernel
theorem subd13_3_9 : subd13_3 [0, -1] = true := by decide +kernel
theorem subd13_3_10 : subd13_3 [0, 0] = true := by decide +kernel
theorem subd13_3_11 : subd13_3 [0, 1] = true := by decide +kernel
theorem subd13_3_12 : subd13_3 [0, 2] = true := by decide +kernel
theorem subd13_3_13 : subd13_3 [1, -3] = true := by decide +kernel
theorem subd13_3_14 : subd13_3 [1, -2] = true := by decide +kernel
theorem subd13_3_15 : subd13_3 [1, -1] = true := by decide +kernel
theorem subd13_3_16 : subd13_3 [1, 0] = true := by decide +kernel
theorem subd13_3_17 : subd13_3 [1, 1] = true := by decide +kernel
theorem subd13_3_18 : subd13_3 [1, 2] = true := by decide +kernel
theorem subd13_3_19 : subd13_3 [2] = true := by decide +kernel
theorem sbd13_3_0 : ∀ q ∈ blkd13_3_0, subd13_3 q = true := by
  unfold blkd13_3_0
  exact List.forall_mem_cons.2 ⟨subd13_3_0, List.forall_mem_cons.2 ⟨subd13_3_1, List.forall_mem_cons.2 ⟨subd13_3_2, List.forall_mem_cons.2 ⟨subd13_3_3, List.forall_mem_cons.2 ⟨subd13_3_4, List.forall_mem_cons.2 ⟨subd13_3_5, List.forall_mem_cons.2 ⟨subd13_3_6, List.forall_mem_cons.2 ⟨subd13_3_7, List.forall_mem_cons.2 ⟨subd13_3_8, List.forall_mem_cons.2 ⟨subd13_3_9, List.forall_mem_cons.2 ⟨subd13_3_10, List.forall_mem_cons.2 ⟨subd13_3_11, List.forall_mem_cons.2 ⟨subd13_3_12, List.forall_mem_cons.2 ⟨subd13_3_13, List.forall_mem_cons.2 ⟨subd13_3_14, List.forall_mem_cons.2 ⟨subd13_3_15, List.forall_mem_cons.2 ⟨subd13_3_16, List.forall_mem_cons.2 ⟨subd13_3_17, List.forall_mem_cons.2 ⟨subd13_3_18, List.forall_mem_cons.2 ⟨subd13_3_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd14_0 : ldCheck G d14_0.U d14_0.ms ldd14_0 = true := by decide +kernel
theorem pre_okd14_0 : subPre G cell14 d14_0 = true := by decide +kernel
theorem subd14_0_0 : subd14_0 [-4] = true := by decide +kernel
theorem subd14_0_1 : subd14_0 [-3] = true := by decide +kernel
theorem subd14_0_2 : subd14_0 [-2, -4] = true := by decide +kernel
theorem subd14_0_3 : subd14_0 [-2, -3] = true := by decide +kernel
theorem subd14_0_4 : subd14_0 [-2, -2] = true := by decide +kernel
theorem subd14_0_5 : subd14_0 [-2, -1] = true := by decide +kernel
theorem subd14_0_6 : subd14_0 [-2, 0] = true := by decide +kernel
theorem subd14_0_7 : subd14_0 [-2, 1] = true := by decide +kernel
theorem subd14_0_8 : subd14_0 [-2, 2] = true := by decide +kernel
theorem subd14_0_9 : subd14_0 [-2, 3] = true := by decide +kernel
theorem subd14_0_10 : subd14_0 [-1, -5] = true := by decide +kernel
theorem subd14_0_11 : subd14_0 [-1, -4] = true := by decide +kernel
theorem subd14_0_12 : subd14_0 [-1, -3] = true := by decide +kernel
theorem subd14_0_13 : subd14_0 [-1, -2] = true := by decide +kernel
theorem subd14_0_14 : subd14_0 [-1, -1] = true := by decide +kernel
theorem subd14_0_15 : subd14_0 [-1, 0] = true := by decide +kernel
theorem subd14_0_16 : subd14_0 [-1, 1] = true := by decide +kernel
theorem subd14_0_17 : subd14_0 [-1, 2] = true := by decide +kernel
theorem subd14_0_18 : subd14_0 [-1, 3] = true := by decide +kernel
theorem subd14_0_19 : subd14_0 [-1, 4] = true := by decide +kernel
theorem subd14_0_20 : subd14_0 [0, -5] = true := by decide +kernel
theorem subd14_0_21 : subd14_0 [0, -4] = true := by decide +kernel
theorem subd14_0_22 : subd14_0 [0, -3] = true := by decide +kernel
theorem subd14_0_23 : subd14_0 [0, -2] = true := by decide +kernel
theorem subd14_0_24 : subd14_0 [0, -1] = true := by decide +kernel
theorem subd14_0_25 : subd14_0 [0, 0] = true := by decide +kernel
theorem subd14_0_26 : subd14_0 [0, 1] = true := by decide +kernel
theorem subd14_0_27 : subd14_0 [0, 2] = true := by decide +kernel
theorem subd14_0_28 : subd14_0 [0, 3] = true := by decide +kernel
theorem subd14_0_29 : subd14_0 [0, 4] = true := by decide +kernel
theorem subd14_0_30 : subd14_0 [1, -5] = true := by decide +kernel
theorem subd14_0_31 : subd14_0 [1, -4] = true := by decide +kernel
theorem sbd14_0_0 : ∀ q ∈ blkd14_0_0, subd14_0 q = true := by
  unfold blkd14_0_0
  exact List.forall_mem_cons.2 ⟨subd14_0_0, List.forall_mem_cons.2 ⟨subd14_0_1, List.forall_mem_cons.2 ⟨subd14_0_2, List.forall_mem_cons.2 ⟨subd14_0_3, List.forall_mem_cons.2 ⟨subd14_0_4, List.forall_mem_cons.2 ⟨subd14_0_5, List.forall_mem_cons.2 ⟨subd14_0_6, List.forall_mem_cons.2 ⟨subd14_0_7, List.forall_mem_cons.2 ⟨subd14_0_8, List.forall_mem_cons.2 ⟨subd14_0_9, List.forall_mem_cons.2 ⟨subd14_0_10, List.forall_mem_cons.2 ⟨subd14_0_11, List.forall_mem_cons.2 ⟨subd14_0_12, List.forall_mem_cons.2 ⟨subd14_0_13, List.forall_mem_cons.2 ⟨subd14_0_14, List.forall_mem_cons.2 ⟨subd14_0_15, List.forall_mem_cons.2 ⟨subd14_0_16, List.forall_mem_cons.2 ⟨subd14_0_17, List.forall_mem_cons.2 ⟨subd14_0_18, List.forall_mem_cons.2 ⟨subd14_0_19, List.forall_mem_cons.2 ⟨subd14_0_20, List.forall_mem_cons.2 ⟨subd14_0_21, List.forall_mem_cons.2 ⟨subd14_0_22, List.forall_mem_cons.2 ⟨subd14_0_23, List.forall_mem_cons.2 ⟨subd14_0_24, List.forall_mem_cons.2 ⟨subd14_0_25, List.forall_mem_cons.2 ⟨subd14_0_26, List.forall_mem_cons.2 ⟨subd14_0_27, List.forall_mem_cons.2 ⟨subd14_0_28, List.forall_mem_cons.2 ⟨subd14_0_29, List.forall_mem_cons.2 ⟨subd14_0_30, List.forall_mem_cons.2 ⟨subd14_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C142
