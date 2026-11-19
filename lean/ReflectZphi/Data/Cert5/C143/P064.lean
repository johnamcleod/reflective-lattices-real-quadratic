import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd19_0_768 : subd19_0 [1, 1, 6] = true := by decide +kernel
theorem subd19_0_769 : subd19_0 [1, 1, 7] = true := by decide +kernel
theorem subd19_0_770 : subd19_0 [1, 1, 8] = true := by decide +kernel
theorem subd19_0_771 : subd19_0 [1, 1, 9] = true := by decide +kernel
theorem subd19_0_772 : subd19_0 [1, 1, 10] = true := by decide +kernel
theorem subd19_0_773 : subd19_0 [1, 1, 11] = true := by decide +kernel
theorem subd19_0_774 : subd19_0 [1, 2, -12] = true := by decide +kernel
theorem subd19_0_775 : subd19_0 [1, 2, -11] = true := by decide +kernel
theorem subd19_0_776 : subd19_0 [1, 2, -10] = true := by decide +kernel
theorem subd19_0_777 : subd19_0 [1, 2, -9] = true := by decide +kernel
theorem subd19_0_778 : subd19_0 [1, 2, -8] = true := by decide +kernel
theorem subd19_0_779 : subd19_0 [1, 2, -7] = true := by decide +kernel
theorem subd19_0_780 : subd19_0 [1, 2, -6] = true := by decide +kernel
theorem subd19_0_781 : subd19_0 [1, 2, -5] = true := by decide +kernel
theorem subd19_0_782 : subd19_0 [1, 2, -4] = true := by decide +kernel
theorem subd19_0_783 : subd19_0 [1, 2, -3] = true := by decide +kernel
theorem subd19_0_784 : subd19_0 [1, 2, -2] = true := by decide +kernel
theorem subd19_0_785 : subd19_0 [1, 2, -1] = true := by decide +kernel
theorem subd19_0_786 : subd19_0 [1, 2, 0] = true := by decide +kernel
theorem subd19_0_787 : subd19_0 [1, 2, 1] = true := by decide +kernel
theorem subd19_0_788 : subd19_0 [1, 2, 2] = true := by decide +kernel
theorem subd19_0_789 : subd19_0 [1, 2, 3] = true := by decide +kernel
theorem subd19_0_790 : subd19_0 [1, 2, 4] = true := by decide +kernel
theorem subd19_0_791 : subd19_0 [1, 2, 5] = true := by decide +kernel
theorem subd19_0_792 : subd19_0 [1, 2, 6] = true := by decide +kernel
theorem subd19_0_793 : subd19_0 [1, 2, 7] = true := by decide +kernel
theorem subd19_0_794 : subd19_0 [1, 2, 8] = true := by decide +kernel
theorem subd19_0_795 : subd19_0 [1, 2, 9] = true := by decide +kernel
theorem subd19_0_796 : subd19_0 [1, 2, 10] = true := by decide +kernel
theorem subd19_0_797 : subd19_0 [1, 3, -10] = true := by decide +kernel
theorem subd19_0_798 : subd19_0 [1, 3, -9] = true := by decide +kernel
theorem subd19_0_799 : subd19_0 [1, 3, -8] = true := by decide +kernel
theorem sbd19_0_24 : ∀ q ∈ blkd19_0_24, subd19_0 q = true := by
  unfold blkd19_0_24
  exact List.forall_mem_cons.2 ⟨subd19_0_768, List.forall_mem_cons.2 ⟨subd19_0_769, List.forall_mem_cons.2 ⟨subd19_0_770, List.forall_mem_cons.2 ⟨subd19_0_771, List.forall_mem_cons.2 ⟨subd19_0_772, List.forall_mem_cons.2 ⟨subd19_0_773, List.forall_mem_cons.2 ⟨subd19_0_774, List.forall_mem_cons.2 ⟨subd19_0_775, List.forall_mem_cons.2 ⟨subd19_0_776, List.forall_mem_cons.2 ⟨subd19_0_777, List.forall_mem_cons.2 ⟨subd19_0_778, List.forall_mem_cons.2 ⟨subd19_0_779, List.forall_mem_cons.2 ⟨subd19_0_780, List.forall_mem_cons.2 ⟨subd19_0_781, List.forall_mem_cons.2 ⟨subd19_0_782, List.forall_mem_cons.2 ⟨subd19_0_783, List.forall_mem_cons.2 ⟨subd19_0_784, List.forall_mem_cons.2 ⟨subd19_0_785, List.forall_mem_cons.2 ⟨subd19_0_786, List.forall_mem_cons.2 ⟨subd19_0_787, List.forall_mem_cons.2 ⟨subd19_0_788, List.forall_mem_cons.2 ⟨subd19_0_789, List.forall_mem_cons.2 ⟨subd19_0_790, List.forall_mem_cons.2 ⟨subd19_0_791, List.forall_mem_cons.2 ⟨subd19_0_792, List.forall_mem_cons.2 ⟨subd19_0_793, List.forall_mem_cons.2 ⟨subd19_0_794, List.forall_mem_cons.2 ⟨subd19_0_795, List.forall_mem_cons.2 ⟨subd19_0_796, List.forall_mem_cons.2 ⟨subd19_0_797, List.forall_mem_cons.2 ⟨subd19_0_798, List.forall_mem_cons.2 ⟨subd19_0_799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_0_800 : subd19_0 [1, 3, -7] = true := by decide +kernel
theorem subd19_0_801 : subd19_0 [1, 3, -6] = true := by decide +kernel
theorem subd19_0_802 : subd19_0 [1, 3, -5] = true := by decide +kernel
theorem subd19_0_803 : subd19_0 [1, 3, -4] = true := by decide +kernel
theorem subd19_0_804 : subd19_0 [1, 3, -3] = true := by decide +kernel
theorem subd19_0_805 : subd19_0 [1, 3, -2] = true := by decide +kernel
theorem subd19_0_806 : subd19_0 [1, 3, -1] = true := by decide +kernel
theorem subd19_0_807 : subd19_0 [1, 3, 0] = true := by decide +kernel
theorem subd19_0_808 : subd19_0 [1, 3, 1] = true := by decide +kernel
theorem subd19_0_809 : subd19_0 [1, 3, 2] = true := by decide +kernel
theorem subd19_0_810 : subd19_0 [1, 3, 3] = true := by decide +kernel
theorem subd19_0_811 : subd19_0 [1, 3, 4] = true := by decide +kernel
theorem subd19_0_812 : subd19_0 [1, 3, 5] = true := by decide +kernel
theorem subd19_0_813 : subd19_0 [1, 3, 6] = true := by decide +kernel
theorem subd19_0_814 : subd19_0 [1, 3, 7] = true := by decide +kernel
theorem subd19_0_815 : subd19_0 [1, 4] = true := by decide +kernel
theorem subd19_0_816 : subd19_0 [2, -5] = true := by decide +kernel
theorem subd19_0_817 : subd19_0 [2, -4, -7] = true := by decide +kernel
theorem subd19_0_818 : subd19_0 [2, -4, -6] = true := by decide +kernel
theorem subd19_0_819 : subd19_0 [2, -4, -5] = true := by decide +kernel
theorem subd19_0_820 : subd19_0 [2, -4, -4] = true := by decide +kernel
theorem subd19_0_821 : subd19_0 [2, -4, -3] = true := by decide +kernel
theorem subd19_0_822 : subd19_0 [2, -4, -2] = true := by decide +kernel
theorem subd19_0_823 : subd19_0 [2, -4, -1] = true := by decide +kernel
theorem subd19_0_824 : subd19_0 [2, -4, 0] = true := by decide +kernel
theorem subd19_0_825 : subd19_0 [2, -4, 1] = true := by decide +kernel
theorem subd19_0_826 : subd19_0 [2, -4, 2] = true := by decide +kernel
theorem subd19_0_827 : subd19_0 [2, -4, 3] = true := by decide +kernel
theorem subd19_0_828 : subd19_0 [2, -4, 4] = true := by decide +kernel
theorem subd19_0_829 : subd19_0 [2, -4, 5] = true := by decide +kernel
theorem subd19_0_830 : subd19_0 [2, -4, 6] = true := by decide +kernel
theorem subd19_0_831 : subd19_0 [2, -4, 7] = true := by decide +kernel
theorem sbd19_0_25 : ∀ q ∈ blkd19_0_25, subd19_0 q = true := by
  unfold blkd19_0_25
  exact List.forall_mem_cons.2 ⟨subd19_0_800, List.forall_mem_cons.2 ⟨subd19_0_801, List.forall_mem_cons.2 ⟨subd19_0_802, List.forall_mem_cons.2 ⟨subd19_0_803, List.forall_mem_cons.2 ⟨subd19_0_804, List.forall_mem_cons.2 ⟨subd19_0_805, List.forall_mem_cons.2 ⟨subd19_0_806, List.forall_mem_cons.2 ⟨subd19_0_807, List.forall_mem_cons.2 ⟨subd19_0_808, List.forall_mem_cons.2 ⟨subd19_0_809, List.forall_mem_cons.2 ⟨subd19_0_810, List.forall_mem_cons.2 ⟨subd19_0_811, List.forall_mem_cons.2 ⟨subd19_0_812, List.forall_mem_cons.2 ⟨subd19_0_813, List.forall_mem_cons.2 ⟨subd19_0_814, List.forall_mem_cons.2 ⟨subd19_0_815, List.forall_mem_cons.2 ⟨subd19_0_816, List.forall_mem_cons.2 ⟨subd19_0_817, List.forall_mem_cons.2 ⟨subd19_0_818, List.forall_mem_cons.2 ⟨subd19_0_819, List.forall_mem_cons.2 ⟨subd19_0_820, List.forall_mem_cons.2 ⟨subd19_0_821, List.forall_mem_cons.2 ⟨subd19_0_822, List.forall_mem_cons.2 ⟨subd19_0_823, List.forall_mem_cons.2 ⟨subd19_0_824, List.forall_mem_cons.2 ⟨subd19_0_825, List.forall_mem_cons.2 ⟨subd19_0_826, List.forall_mem_cons.2 ⟨subd19_0_827, List.forall_mem_cons.2 ⟨subd19_0_828, List.forall_mem_cons.2 ⟨subd19_0_829, List.forall_mem_cons.2 ⟨subd19_0_830, List.forall_mem_cons.2 ⟨subd19_0_831, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_0_832 : subd19_0 [2, -4, 8] = true := by decide +kernel
theorem subd19_0_833 : subd19_0 [2, -3, -9] = true := by decide +kernel
theorem subd19_0_834 : subd19_0 [2, -3, -8] = true := by decide +kernel
theorem subd19_0_835 : subd19_0 [2, -3, -7] = true := by decide +kernel
theorem subd19_0_836 : subd19_0 [2, -3, -6] = true := by decide +kernel
theorem subd19_0_837 : subd19_0 [2, -3, -5] = true := by decide +kernel
theorem subd19_0_838 : subd19_0 [2, -3, -4] = true := by decide +kernel
theorem subd19_0_839 : subd19_0 [2, -3, -3] = true := by decide +kernel
theorem subd19_0_840 : subd19_0 [2, -3, -2] = true := by decide +kernel
theorem subd19_0_841 : subd19_0 [2, -3, -1] = true := by decide +kernel
theorem subd19_0_842 : subd19_0 [2, -3, 0] = true := by decide +kernel
theorem subd19_0_843 : subd19_0 [2, -3, 1] = true := by decide +kernel
theorem subd19_0_844 : subd19_0 [2, -3, 2] = true := by decide +kernel
theorem subd19_0_845 : subd19_0 [2, -3, 3] = true := by decide +kernel
theorem subd19_0_846 : subd19_0 [2, -3, 4] = true := by decide +kernel
theorem subd19_0_847 : subd19_0 [2, -3, 5] = true := by decide +kernel
theorem subd19_0_848 : subd19_0 [2, -3, 6] = true := by decide +kernel
theorem subd19_0_849 : subd19_0 [2, -3, 7] = true := by decide +kernel
theorem subd19_0_850 : subd19_0 [2, -3, 8] = true := by decide +kernel
theorem subd19_0_851 : subd19_0 [2, -3, 9] = true := by decide +kernel
theorem subd19_0_852 : subd19_0 [2, -3, 10] = true := by decide +kernel
theorem subd19_0_853 : subd19_0 [2, -2, -11] = true := by decide +kernel
theorem subd19_0_854 : subd19_0 [2, -2, -10] = true := by decide +kernel
theorem subd19_0_855 : subd19_0 [2, -2, -9] = true := by decide +kernel
theorem subd19_0_856 : subd19_0 [2, -2, -8] = true := by decide +kernel
theorem subd19_0_857 : subd19_0 [2, -2, -7] = true := by decide +kernel
theorem subd19_0_858 : subd19_0 [2, -2, -6] = true := by decide +kernel
theorem subd19_0_859 : subd19_0 [2, -2, -5] = true := by decide +kernel
theorem subd19_0_860 : subd19_0 [2, -2, -4] = true := by decide +kernel
theorem subd19_0_861 : subd19_0 [2, -2, -3] = true := by decide +kernel
theorem subd19_0_862 : subd19_0 [2, -2, -2] = true := by decide +kernel
theorem subd19_0_863 : subd19_0 [2, -2, -1] = true := by decide +kernel
theorem sbd19_0_26 : ∀ q ∈ blkd19_0_26, subd19_0 q = true := by
  unfold blkd19_0_26
  exact List.forall_mem_cons.2 ⟨subd19_0_832, List.forall_mem_cons.2 ⟨subd19_0_833, List.forall_mem_cons.2 ⟨subd19_0_834, List.forall_mem_cons.2 ⟨subd19_0_835, List.forall_mem_cons.2 ⟨subd19_0_836, List.forall_mem_cons.2 ⟨subd19_0_837, List.forall_mem_cons.2 ⟨subd19_0_838, List.forall_mem_cons.2 ⟨subd19_0_839, List.forall_mem_cons.2 ⟨subd19_0_840, List.forall_mem_cons.2 ⟨subd19_0_841, List.forall_mem_cons.2 ⟨subd19_0_842, List.forall_mem_cons.2 ⟨subd19_0_843, List.forall_mem_cons.2 ⟨subd19_0_844, List.forall_mem_cons.2 ⟨subd19_0_845, List.forall_mem_cons.2 ⟨subd19_0_846, List.forall_mem_cons.2 ⟨subd19_0_847, List.forall_mem_cons.2 ⟨subd19_0_848, List.forall_mem_cons.2 ⟨subd19_0_849, List.forall_mem_cons.2 ⟨subd19_0_850, List.forall_mem_cons.2 ⟨subd19_0_851, List.forall_mem_cons.2 ⟨subd19_0_852, List.forall_mem_cons.2 ⟨subd19_0_853, List.forall_mem_cons.2 ⟨subd19_0_854, List.forall_mem_cons.2 ⟨subd19_0_855, List.forall_mem_cons.2 ⟨subd19_0_856, List.forall_mem_cons.2 ⟨subd19_0_857, List.forall_mem_cons.2 ⟨subd19_0_858, List.forall_mem_cons.2 ⟨subd19_0_859, List.forall_mem_cons.2 ⟨subd19_0_860, List.forall_mem_cons.2 ⟨subd19_0_861, List.forall_mem_cons.2 ⟨subd19_0_862, List.forall_mem_cons.2 ⟨subd19_0_863, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_0_864 : subd19_0 [2, -2, 0] = true := by decide +kernel
theorem subd19_0_865 : subd19_0 [2, -2, 1] = true := by decide +kernel
theorem subd19_0_866 : subd19_0 [2, -2, 2] = true := by decide +kernel
theorem subd19_0_867 : subd19_0 [2, -2, 3] = true := by decide +kernel
theorem subd19_0_868 : subd19_0 [2, -2, 4] = true := by decide +kernel
theorem subd19_0_869 : subd19_0 [2, -2, 5] = true := by decide +kernel
theorem subd19_0_870 : subd19_0 [2, -2, 6] = true := by decide +kernel
theorem subd19_0_871 : subd19_0 [2, -2, 7] = true := by decide +kernel
theorem subd19_0_872 : subd19_0 [2, -2, 8] = true := by decide +kernel
theorem subd19_0_873 : subd19_0 [2, -2, 9] = true := by decide +kernel
theorem subd19_0_874 : subd19_0 [2, -2, 10] = true := by decide +kernel
theorem subd19_0_875 : subd19_0 [2, -2, 11] = true := by decide +kernel
theorem subd19_0_876 : subd19_0 [2, -1, -12] = true := by decide +kernel
theorem subd19_0_877 : subd19_0 [2, -1, -11] = true := by decide +kernel
theorem subd19_0_878 : subd19_0 [2, -1, -10] = true := by decide +kernel
theorem subd19_0_879 : subd19_0 [2, -1, -9] = true := by decide +kernel
theorem subd19_0_880 : subd19_0 [2, -1, -8] = true := by decide +kernel
theorem subd19_0_881 : subd19_0 [2, -1, -7] = true := by decide +kernel
theorem subd19_0_882 : subd19_0 [2, -1, -6] = true := by decide +kernel
theorem subd19_0_883 : subd19_0 [2, -1, -5] = true := by decide +kernel
theorem subd19_0_884 : subd19_0 [2, -1, -4] = true := by decide +kernel
theorem subd19_0_885 : subd19_0 [2, -1, -3] = true := by decide +kernel
theorem subd19_0_886 : subd19_0 [2, -1, -2] = true := by decide +kernel
theorem subd19_0_887 : subd19_0 [2, -1, -1] = true := by decide +kernel
theorem subd19_0_888 : subd19_0 [2, -1, 0] = true := by decide +kernel
theorem subd19_0_889 : subd19_0 [2, -1, 1] = true := by decide +kernel
theorem subd19_0_890 : subd19_0 [2, -1, 2] = true := by decide +kernel
theorem subd19_0_891 : subd19_0 [2, -1, 3] = true := by decide +kernel
theorem subd19_0_892 : subd19_0 [2, -1, 4] = true := by decide +kernel
theorem subd19_0_893 : subd19_0 [2, -1, 5] = true := by decide +kernel
theorem subd19_0_894 : subd19_0 [2, -1, 6] = true := by decide +kernel
theorem subd19_0_895 : subd19_0 [2, -1, 7] = true := by decide +kernel
theorem sbd19_0_27 : ∀ q ∈ blkd19_0_27, subd19_0 q = true := by
  unfold blkd19_0_27
  exact List.forall_mem_cons.2 ⟨subd19_0_864, List.forall_mem_cons.2 ⟨subd19_0_865, List.forall_mem_cons.2 ⟨subd19_0_866, List.forall_mem_cons.2 ⟨subd19_0_867, List.forall_mem_cons.2 ⟨subd19_0_868, List.forall_mem_cons.2 ⟨subd19_0_869, List.forall_mem_cons.2 ⟨subd19_0_870, List.forall_mem_cons.2 ⟨subd19_0_871, List.forall_mem_cons.2 ⟨subd19_0_872, List.forall_mem_cons.2 ⟨subd19_0_873, List.forall_mem_cons.2 ⟨subd19_0_874, List.forall_mem_cons.2 ⟨subd19_0_875, List.forall_mem_cons.2 ⟨subd19_0_876, List.forall_mem_cons.2 ⟨subd19_0_877, List.forall_mem_cons.2 ⟨subd19_0_878, List.forall_mem_cons.2 ⟨subd19_0_879, List.forall_mem_cons.2 ⟨subd19_0_880, List.forall_mem_cons.2 ⟨subd19_0_881, List.forall_mem_cons.2 ⟨subd19_0_882, List.forall_mem_cons.2 ⟨subd19_0_883, List.forall_mem_cons.2 ⟨subd19_0_884, List.forall_mem_cons.2 ⟨subd19_0_885, List.forall_mem_cons.2 ⟨subd19_0_886, List.forall_mem_cons.2 ⟨subd19_0_887, List.forall_mem_cons.2 ⟨subd19_0_888, List.forall_mem_cons.2 ⟨subd19_0_889, List.forall_mem_cons.2 ⟨subd19_0_890, List.forall_mem_cons.2 ⟨subd19_0_891, List.forall_mem_cons.2 ⟨subd19_0_892, List.forall_mem_cons.2 ⟨subd19_0_893, List.forall_mem_cons.2 ⟨subd19_0_894, List.forall_mem_cons.2 ⟨subd19_0_895, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_0_896 : subd19_0 [2, -1, 8] = true := by decide +kernel
theorem subd19_0_897 : subd19_0 [2, -1, 9] = true := by decide +kernel
theorem subd19_0_898 : subd19_0 [2, -1, 10] = true := by decide +kernel
theorem subd19_0_899 : subd19_0 [2, -1, 11] = true := by decide +kernel
theorem subd19_0_900 : subd19_0 [2, 0, -12] = true := by decide +kernel
theorem subd19_0_901 : subd19_0 [2, 0, -11] = true := by decide +kernel
theorem subd19_0_902 : subd19_0 [2, 0, -10] = true := by decide +kernel
theorem subd19_0_903 : subd19_0 [2, 0, -9] = true := by decide +kernel
theorem subd19_0_904 : subd19_0 [2, 0, -8] = true := by decide +kernel
theorem subd19_0_905 : subd19_0 [2, 0, -7] = true := by decide +kernel
theorem subd19_0_906 : subd19_0 [2, 0, -6] = true := by decide +kernel
theorem subd19_0_907 : subd19_0 [2, 0, -5] = true := by decide +kernel
theorem subd19_0_908 : subd19_0 [2, 0, -4] = true := by decide +kernel
theorem subd19_0_909 : subd19_0 [2, 0, -3] = true := by decide +kernel
theorem subd19_0_910 : subd19_0 [2, 0, -2] = true := by decide +kernel
theorem subd19_0_911 : subd19_0 [2, 0, -1] = true := by decide +kernel
theorem subd19_0_912 : subd19_0 [2, 0, 0] = true := by decide +kernel
theorem subd19_0_913 : subd19_0 [2, 0, 1] = true := by decide +kernel
theorem subd19_0_914 : subd19_0 [2, 0, 2] = true := by decide +kernel
theorem subd19_0_915 : subd19_0 [2, 0, 3] = true := by decide +kernel
theorem subd19_0_916 : subd19_0 [2, 0, 4] = true := by decide +kernel
theorem subd19_0_917 : subd19_0 [2, 0, 5] = true := by decide +kernel
theorem subd19_0_918 : subd19_0 [2, 0, 6] = true := by decide +kernel
theorem subd19_0_919 : subd19_0 [2, 0, 7] = true := by decide +kernel
theorem subd19_0_920 : subd19_0 [2, 0, 8] = true := by decide +kernel
theorem subd19_0_921 : subd19_0 [2, 0, 9] = true := by decide +kernel
theorem subd19_0_922 : subd19_0 [2, 0, 10] = true := by decide +kernel
theorem subd19_0_923 : subd19_0 [2, 0, 11] = true := by decide +kernel
theorem subd19_0_924 : subd19_0 [2, 1, -11] = true := by decide +kernel
theorem subd19_0_925 : subd19_0 [2, 1, -10] = true := by decide +kernel
theorem subd19_0_926 : subd19_0 [2, 1, -9] = true := by decide +kernel
theorem subd19_0_927 : subd19_0 [2, 1, -8] = true := by decide +kernel
theorem sbd19_0_28 : ∀ q ∈ blkd19_0_28, subd19_0 q = true := by
  unfold blkd19_0_28
  exact List.forall_mem_cons.2 ⟨subd19_0_896, List.forall_mem_cons.2 ⟨subd19_0_897, List.forall_mem_cons.2 ⟨subd19_0_898, List.forall_mem_cons.2 ⟨subd19_0_899, List.forall_mem_cons.2 ⟨subd19_0_900, List.forall_mem_cons.2 ⟨subd19_0_901, List.forall_mem_cons.2 ⟨subd19_0_902, List.forall_mem_cons.2 ⟨subd19_0_903, List.forall_mem_cons.2 ⟨subd19_0_904, List.forall_mem_cons.2 ⟨subd19_0_905, List.forall_mem_cons.2 ⟨subd19_0_906, List.forall_mem_cons.2 ⟨subd19_0_907, List.forall_mem_cons.2 ⟨subd19_0_908, List.forall_mem_cons.2 ⟨subd19_0_909, List.forall_mem_cons.2 ⟨subd19_0_910, List.forall_mem_cons.2 ⟨subd19_0_911, List.forall_mem_cons.2 ⟨subd19_0_912, List.forall_mem_cons.2 ⟨subd19_0_913, List.forall_mem_cons.2 ⟨subd19_0_914, List.forall_mem_cons.2 ⟨subd19_0_915, List.forall_mem_cons.2 ⟨subd19_0_916, List.forall_mem_cons.2 ⟨subd19_0_917, List.forall_mem_cons.2 ⟨subd19_0_918, List.forall_mem_cons.2 ⟨subd19_0_919, List.forall_mem_cons.2 ⟨subd19_0_920, List.forall_mem_cons.2 ⟨subd19_0_921, List.forall_mem_cons.2 ⟨subd19_0_922, List.forall_mem_cons.2 ⟨subd19_0_923, List.forall_mem_cons.2 ⟨subd19_0_924, List.forall_mem_cons.2 ⟨subd19_0_925, List.forall_mem_cons.2 ⟨subd19_0_926, List.forall_mem_cons.2 ⟨subd19_0_927, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_0_928 : subd19_0 [2, 1, -7] = true := by decide +kernel
theorem subd19_0_929 : subd19_0 [2, 1, -6] = true := by decide +kernel
theorem subd19_0_930 : subd19_0 [2, 1, -5] = true := by decide +kernel
theorem subd19_0_931 : subd19_0 [2, 1, -4] = true := by decide +kernel
theorem subd19_0_932 : subd19_0 [2, 1, -3] = true := by decide +kernel
theorem subd19_0_933 : subd19_0 [2, 1, -2] = true := by decide +kernel
theorem subd19_0_934 : subd19_0 [2, 1, -1] = true := by decide +kernel
theorem subd19_0_935 : subd19_0 [2, 1, 0] = true := by decide +kernel
theorem subd19_0_936 : subd19_0 [2, 1, 1] = true := by decide +kernel
theorem subd19_0_937 : subd19_0 [2, 1, 2] = true := by decide +kernel
theorem subd19_0_938 : subd19_0 [2, 1, 3] = true := by decide +kernel
theorem subd19_0_939 : subd19_0 [2, 1, 4] = true := by decide +kernel
theorem subd19_0_940 : subd19_0 [2, 1, 5] = true := by decide +kernel
theorem subd19_0_941 : subd19_0 [2, 1, 6] = true := by decide +kernel
theorem subd19_0_942 : subd19_0 [2, 1, 7] = true := by decide +kernel
theorem subd19_0_943 : subd19_0 [2, 1, 8] = true := by decide +kernel
theorem subd19_0_944 : subd19_0 [2, 1, 9] = true := by decide +kernel
theorem subd19_0_945 : subd19_0 [2, 1, 10] = true := by decide +kernel
theorem subd19_0_946 : subd19_0 [2, 2, -10] = true := by decide +kernel
theorem subd19_0_947 : subd19_0 [2, 2, -9] = true := by decide +kernel
theorem subd19_0_948 : subd19_0 [2, 2, -8] = true := by decide +kernel
theorem subd19_0_949 : subd19_0 [2, 2, -7] = true := by decide +kernel
theorem subd19_0_950 : subd19_0 [2, 2, -6] = true := by decide +kernel
theorem subd19_0_951 : subd19_0 [2, 2, -5] = true := by decide +kernel
theorem subd19_0_952 : subd19_0 [2, 2, -4] = true := by decide +kernel
theorem subd19_0_953 : subd19_0 [2, 2, -3] = true := by decide +kernel
theorem subd19_0_954 : subd19_0 [2, 2, -2] = true := by decide +kernel
theorem subd19_0_955 : subd19_0 [2, 2, -1] = true := by decide +kernel
theorem subd19_0_956 : subd19_0 [2, 2, 0] = true := by decide +kernel
theorem subd19_0_957 : subd19_0 [2, 2, 1] = true := by decide +kernel
theorem subd19_0_958 : subd19_0 [2, 2, 2] = true := by decide +kernel
theorem subd19_0_959 : subd19_0 [2, 2, 3] = true := by decide +kernel
theorem sbd19_0_29 : ∀ q ∈ blkd19_0_29, subd19_0 q = true := by
  unfold blkd19_0_29
  exact List.forall_mem_cons.2 ⟨subd19_0_928, List.forall_mem_cons.2 ⟨subd19_0_929, List.forall_mem_cons.2 ⟨subd19_0_930, List.forall_mem_cons.2 ⟨subd19_0_931, List.forall_mem_cons.2 ⟨subd19_0_932, List.forall_mem_cons.2 ⟨subd19_0_933, List.forall_mem_cons.2 ⟨subd19_0_934, List.forall_mem_cons.2 ⟨subd19_0_935, List.forall_mem_cons.2 ⟨subd19_0_936, List.forall_mem_cons.2 ⟨subd19_0_937, List.forall_mem_cons.2 ⟨subd19_0_938, List.forall_mem_cons.2 ⟨subd19_0_939, List.forall_mem_cons.2 ⟨subd19_0_940, List.forall_mem_cons.2 ⟨subd19_0_941, List.forall_mem_cons.2 ⟨subd19_0_942, List.forall_mem_cons.2 ⟨subd19_0_943, List.forall_mem_cons.2 ⟨subd19_0_944, List.forall_mem_cons.2 ⟨subd19_0_945, List.forall_mem_cons.2 ⟨subd19_0_946, List.forall_mem_cons.2 ⟨subd19_0_947, List.forall_mem_cons.2 ⟨subd19_0_948, List.forall_mem_cons.2 ⟨subd19_0_949, List.forall_mem_cons.2 ⟨subd19_0_950, List.forall_mem_cons.2 ⟨subd19_0_951, List.forall_mem_cons.2 ⟨subd19_0_952, List.forall_mem_cons.2 ⟨subd19_0_953, List.forall_mem_cons.2 ⟨subd19_0_954, List.forall_mem_cons.2 ⟨subd19_0_955, List.forall_mem_cons.2 ⟨subd19_0_956, List.forall_mem_cons.2 ⟨subd19_0_957, List.forall_mem_cons.2 ⟨subd19_0_958, List.forall_mem_cons.2 ⟨subd19_0_959, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_0_960 : subd19_0 [2, 2, 4] = true := by decide +kernel
theorem subd19_0_961 : subd19_0 [2, 2, 5] = true := by decide +kernel
theorem subd19_0_962 : subd19_0 [2, 2, 6] = true := by decide +kernel
theorem subd19_0_963 : subd19_0 [2, 2, 7] = true := by decide +kernel
theorem subd19_0_964 : subd19_0 [2, 2, 8] = true := by decide +kernel
theorem subd19_0_965 : subd19_0 [2, 3] = true := by decide +kernel
theorem subd19_0_966 : subd19_0 [3, -5] = true := by decide +kernel
theorem subd19_0_967 : subd19_0 [3, -4] = true := by decide +kernel
theorem subd19_0_968 : subd19_0 [3, -3, -7] = true := by decide +kernel
theorem subd19_0_969 : subd19_0 [3, -3, -6] = true := by decide +kernel
theorem subd19_0_970 : subd19_0 [3, -3, -5] = true := by decide +kernel
theorem subd19_0_971 : subd19_0 [3, -3, -4] = true := by decide +kernel
theorem subd19_0_972 : subd19_0 [3, -3, -3] = true := by decide +kernel
theorem subd19_0_973 : subd19_0 [3, -3, -2] = true := by decide +kernel
theorem subd19_0_974 : subd19_0 [3, -3, -1] = true := by decide +kernel
theorem subd19_0_975 : subd19_0 [3, -3, 0] = true := by decide +kernel
theorem subd19_0_976 : subd19_0 [3, -3, 1] = true := by decide +kernel
theorem subd19_0_977 : subd19_0 [3, -3, 2] = true := by decide +kernel
theorem subd19_0_978 : subd19_0 [3, -3, 3] = true := by decide +kernel
theorem subd19_0_979 : subd19_0 [3, -3, 4] = true := by decide +kernel
theorem subd19_0_980 : subd19_0 [3, -3, 5] = true := by decide +kernel
theorem subd19_0_981 : subd19_0 [3, -3, 6] = true := by decide +kernel
theorem subd19_0_982 : subd19_0 [3, -3, 7] = true := by decide +kernel
theorem subd19_0_983 : subd19_0 [3, -3, 8] = true := by decide +kernel
theorem subd19_0_984 : subd19_0 [3, -2, -9] = true := by decide +kernel
theorem subd19_0_985 : subd19_0 [3, -2, -8] = true := by decide +kernel
theorem subd19_0_986 : subd19_0 [3, -2, -7] = true := by decide +kernel
theorem subd19_0_987 : subd19_0 [3, -2, -6] = true := by decide +kernel
theorem subd19_0_988 : subd19_0 [3, -2, -5] = true := by decide +kernel
theorem subd19_0_989 : subd19_0 [3, -2, -4] = true := by decide +kernel
theorem subd19_0_990 : subd19_0 [3, -2, -3] = true := by decide +kernel
theorem subd19_0_991 : subd19_0 [3, -2, -2] = true := by decide +kernel
theorem sbd19_0_30 : ∀ q ∈ blkd19_0_30, subd19_0 q = true := by
  unfold blkd19_0_30
  exact List.forall_mem_cons.2 ⟨subd19_0_960, List.forall_mem_cons.2 ⟨subd19_0_961, List.forall_mem_cons.2 ⟨subd19_0_962, List.forall_mem_cons.2 ⟨subd19_0_963, List.forall_mem_cons.2 ⟨subd19_0_964, List.forall_mem_cons.2 ⟨subd19_0_965, List.forall_mem_cons.2 ⟨subd19_0_966, List.forall_mem_cons.2 ⟨subd19_0_967, List.forall_mem_cons.2 ⟨subd19_0_968, List.forall_mem_cons.2 ⟨subd19_0_969, List.forall_mem_cons.2 ⟨subd19_0_970, List.forall_mem_cons.2 ⟨subd19_0_971, List.forall_mem_cons.2 ⟨subd19_0_972, List.forall_mem_cons.2 ⟨subd19_0_973, List.forall_mem_cons.2 ⟨subd19_0_974, List.forall_mem_cons.2 ⟨subd19_0_975, List.forall_mem_cons.2 ⟨subd19_0_976, List.forall_mem_cons.2 ⟨subd19_0_977, List.forall_mem_cons.2 ⟨subd19_0_978, List.forall_mem_cons.2 ⟨subd19_0_979, List.forall_mem_cons.2 ⟨subd19_0_980, List.forall_mem_cons.2 ⟨subd19_0_981, List.forall_mem_cons.2 ⟨subd19_0_982, List.forall_mem_cons.2 ⟨subd19_0_983, List.forall_mem_cons.2 ⟨subd19_0_984, List.forall_mem_cons.2 ⟨subd19_0_985, List.forall_mem_cons.2 ⟨subd19_0_986, List.forall_mem_cons.2 ⟨subd19_0_987, List.forall_mem_cons.2 ⟨subd19_0_988, List.forall_mem_cons.2 ⟨subd19_0_989, List.forall_mem_cons.2 ⟨subd19_0_990, List.forall_mem_cons.2 ⟨subd19_0_991, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_0_992 : subd19_0 [3, -2, -1] = true := by decide +kernel
theorem subd19_0_993 : subd19_0 [3, -2, 0] = true := by decide +kernel
theorem subd19_0_994 : subd19_0 [3, -2, 1] = true := by decide +kernel
theorem subd19_0_995 : subd19_0 [3, -2, 2] = true := by decide +kernel
theorem subd19_0_996 : subd19_0 [3, -2, 3] = true := by decide +kernel
theorem subd19_0_997 : subd19_0 [3, -2, 4] = true := by decide +kernel
theorem subd19_0_998 : subd19_0 [3, -2, 5] = true := by decide +kernel
theorem subd19_0_999 : subd19_0 [3, -2, 6] = true := by decide +kernel
theorem subd19_0_1000 : subd19_0 [3, -2, 7] = true := by decide +kernel
theorem subd19_0_1001 : subd19_0 [3, -2, 8] = true := by decide +kernel
theorem subd19_0_1002 : subd19_0 [3, -2, 9] = true := by decide +kernel
theorem subd19_0_1003 : subd19_0 [3, -1, -10] = true := by decide +kernel
theorem subd19_0_1004 : subd19_0 [3, -1, -9] = true := by decide +kernel
theorem subd19_0_1005 : subd19_0 [3, -1, -8] = true := by decide +kernel
theorem subd19_0_1006 : subd19_0 [3, -1, -7] = true := by decide +kernel
theorem subd19_0_1007 : subd19_0 [3, -1, -6] = true := by decide +kernel
theorem subd19_0_1008 : subd19_0 [3, -1, -5] = true := by decide +kernel
theorem subd19_0_1009 : subd19_0 [3, -1, -4] = true := by decide +kernel
theorem subd19_0_1010 : subd19_0 [3, -1, -3] = true := by decide +kernel
theorem subd19_0_1011 : subd19_0 [3, -1, -2] = true := by decide +kernel
theorem subd19_0_1012 : subd19_0 [3, -1, -1] = true := by decide +kernel
theorem subd19_0_1013 : subd19_0 [3, -1, 0] = true := by decide +kernel
theorem subd19_0_1014 : subd19_0 [3, -1, 1] = true := by decide +kernel
theorem subd19_0_1015 : subd19_0 [3, -1, 2] = true := by decide +kernel
theorem subd19_0_1016 : subd19_0 [3, -1, 3] = true := by decide +kernel
theorem subd19_0_1017 : subd19_0 [3, -1, 4] = true := by decide +kernel
theorem subd19_0_1018 : subd19_0 [3, -1, 5] = true := by decide +kernel
theorem subd19_0_1019 : subd19_0 [3, -1, 6] = true := by decide +kernel
theorem subd19_0_1020 : subd19_0 [3, -1, 7] = true := by decide +kernel
theorem subd19_0_1021 : subd19_0 [3, -1, 8] = true := by decide +kernel
theorem subd19_0_1022 : subd19_0 [3, -1, 9] = true := by decide +kernel
theorem subd19_0_1023 : subd19_0 [3, 0, -10] = true := by decide +kernel
theorem sbd19_0_31 : ∀ q ∈ blkd19_0_31, subd19_0 q = true := by
  unfold blkd19_0_31
  exact List.forall_mem_cons.2 ⟨subd19_0_992, List.forall_mem_cons.2 ⟨subd19_0_993, List.forall_mem_cons.2 ⟨subd19_0_994, List.forall_mem_cons.2 ⟨subd19_0_995, List.forall_mem_cons.2 ⟨subd19_0_996, List.forall_mem_cons.2 ⟨subd19_0_997, List.forall_mem_cons.2 ⟨subd19_0_998, List.forall_mem_cons.2 ⟨subd19_0_999, List.forall_mem_cons.2 ⟨subd19_0_1000, List.forall_mem_cons.2 ⟨subd19_0_1001, List.forall_mem_cons.2 ⟨subd19_0_1002, List.forall_mem_cons.2 ⟨subd19_0_1003, List.forall_mem_cons.2 ⟨subd19_0_1004, List.forall_mem_cons.2 ⟨subd19_0_1005, List.forall_mem_cons.2 ⟨subd19_0_1006, List.forall_mem_cons.2 ⟨subd19_0_1007, List.forall_mem_cons.2 ⟨subd19_0_1008, List.forall_mem_cons.2 ⟨subd19_0_1009, List.forall_mem_cons.2 ⟨subd19_0_1010, List.forall_mem_cons.2 ⟨subd19_0_1011, List.forall_mem_cons.2 ⟨subd19_0_1012, List.forall_mem_cons.2 ⟨subd19_0_1013, List.forall_mem_cons.2 ⟨subd19_0_1014, List.forall_mem_cons.2 ⟨subd19_0_1015, List.forall_mem_cons.2 ⟨subd19_0_1016, List.forall_mem_cons.2 ⟨subd19_0_1017, List.forall_mem_cons.2 ⟨subd19_0_1018, List.forall_mem_cons.2 ⟨subd19_0_1019, List.forall_mem_cons.2 ⟨subd19_0_1020, List.forall_mem_cons.2 ⟨subd19_0_1021, List.forall_mem_cons.2 ⟨subd19_0_1022, List.forall_mem_cons.2 ⟨subd19_0_1023, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_0_1024 : subd19_0 [3, 0, -9] = true := by decide +kernel
theorem subd19_0_1025 : subd19_0 [3, 0, -8] = true := by decide +kernel
theorem subd19_0_1026 : subd19_0 [3, 0, -7] = true := by decide +kernel
theorem subd19_0_1027 : subd19_0 [3, 0, -6] = true := by decide +kernel
theorem subd19_0_1028 : subd19_0 [3, 0, -5] = true := by decide +kernel
theorem subd19_0_1029 : subd19_0 [3, 0, -4] = true := by decide +kernel
theorem subd19_0_1030 : subd19_0 [3, 0, -3] = true := by decide +kernel
theorem subd19_0_1031 : subd19_0 [3, 0, -2] = true := by decide +kernel
theorem subd19_0_1032 : subd19_0 [3, 0, -1] = true := by decide +kernel
theorem subd19_0_1033 : subd19_0 [3, 0, 0] = true := by decide +kernel
theorem subd19_0_1034 : subd19_0 [3, 0, 1] = true := by decide +kernel
theorem subd19_0_1035 : subd19_0 [3, 0, 2] = true := by decide +kernel
theorem subd19_0_1036 : subd19_0 [3, 0, 3] = true := by decide +kernel
theorem subd19_0_1037 : subd19_0 [3, 0, 4] = true := by decide +kernel
theorem subd19_0_1038 : subd19_0 [3, 0, 5] = true := by decide +kernel
theorem subd19_0_1039 : subd19_0 [3, 0, 6] = true := by decide +kernel
theorem subd19_0_1040 : subd19_0 [3, 0, 7] = true := by decide +kernel
theorem subd19_0_1041 : subd19_0 [3, 0, 8] = true := by decide +kernel
theorem subd19_0_1042 : subd19_0 [3, 1, -9] = true := by decide +kernel
theorem subd19_0_1043 : subd19_0 [3, 1, -8] = true := by decide +kernel
theorem subd19_0_1044 : subd19_0 [3, 1, -7] = true := by decide +kernel
theorem subd19_0_1045 : subd19_0 [3, 1, -6] = true := by decide +kernel
theorem subd19_0_1046 : subd19_0 [3, 1, -5] = true := by decide +kernel
theorem subd19_0_1047 : subd19_0 [3, 1, -4] = true := by decide +kernel
theorem subd19_0_1048 : subd19_0 [3, 1, -3] = true := by decide +kernel
theorem subd19_0_1049 : subd19_0 [3, 1, -2] = true := by decide +kernel
theorem subd19_0_1050 : subd19_0 [3, 1, -1] = true := by decide +kernel
theorem subd19_0_1051 : subd19_0 [3, 1, 0] = true := by decide +kernel
theorem subd19_0_1052 : subd19_0 [3, 1, 1] = true := by decide +kernel
theorem subd19_0_1053 : subd19_0 [3, 1, 2] = true := by decide +kernel
theorem subd19_0_1054 : subd19_0 [3, 1, 3] = true := by decide +kernel
theorem subd19_0_1055 : subd19_0 [3, 1, 4] = true := by decide +kernel
theorem sbd19_0_32 : ∀ q ∈ blkd19_0_32, subd19_0 q = true := by
  unfold blkd19_0_32
  exact List.forall_mem_cons.2 ⟨subd19_0_1024, List.forall_mem_cons.2 ⟨subd19_0_1025, List.forall_mem_cons.2 ⟨subd19_0_1026, List.forall_mem_cons.2 ⟨subd19_0_1027, List.forall_mem_cons.2 ⟨subd19_0_1028, List.forall_mem_cons.2 ⟨subd19_0_1029, List.forall_mem_cons.2 ⟨subd19_0_1030, List.forall_mem_cons.2 ⟨subd19_0_1031, List.forall_mem_cons.2 ⟨subd19_0_1032, List.forall_mem_cons.2 ⟨subd19_0_1033, List.forall_mem_cons.2 ⟨subd19_0_1034, List.forall_mem_cons.2 ⟨subd19_0_1035, List.forall_mem_cons.2 ⟨subd19_0_1036, List.forall_mem_cons.2 ⟨subd19_0_1037, List.forall_mem_cons.2 ⟨subd19_0_1038, List.forall_mem_cons.2 ⟨subd19_0_1039, List.forall_mem_cons.2 ⟨subd19_0_1040, List.forall_mem_cons.2 ⟨subd19_0_1041, List.forall_mem_cons.2 ⟨subd19_0_1042, List.forall_mem_cons.2 ⟨subd19_0_1043, List.forall_mem_cons.2 ⟨subd19_0_1044, List.forall_mem_cons.2 ⟨subd19_0_1045, List.forall_mem_cons.2 ⟨subd19_0_1046, List.forall_mem_cons.2 ⟨subd19_0_1047, List.forall_mem_cons.2 ⟨subd19_0_1048, List.forall_mem_cons.2 ⟨subd19_0_1049, List.forall_mem_cons.2 ⟨subd19_0_1050, List.forall_mem_cons.2 ⟨subd19_0_1051, List.forall_mem_cons.2 ⟨subd19_0_1052, List.forall_mem_cons.2 ⟨subd19_0_1053, List.forall_mem_cons.2 ⟨subd19_0_1054, List.forall_mem_cons.2 ⟨subd19_0_1055, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_0_1056 : subd19_0 [3, 1, 5] = true := by decide +kernel
theorem subd19_0_1057 : subd19_0 [3, 1, 6] = true := by decide +kernel
theorem subd19_0_1058 : subd19_0 [3, 1, 7] = true := by decide +kernel
theorem subd19_0_1059 : subd19_0 [3, 2] = true := by decide +kernel
theorem subd19_0_1060 : subd19_0 [4, -4] = true := by decide +kernel
theorem subd19_0_1061 : subd19_0 [4, -3] = true := by decide +kernel
theorem subd19_0_1062 : subd19_0 [4, -2] = true := by decide +kernel
theorem subd19_0_1063 : subd19_0 [4, -1] = true := by decide +kernel
theorem subd19_0_1064 : subd19_0 [4, 0] = true := by decide +kernel
theorem sbd19_0_33 : ∀ q ∈ blkd19_0_33, subd19_0 q = true := by
  unfold blkd19_0_33
  exact List.forall_mem_cons.2 ⟨subd19_0_1056, List.forall_mem_cons.2 ⟨subd19_0_1057, List.forall_mem_cons.2 ⟨subd19_0_1058, List.forall_mem_cons.2 ⟨subd19_0_1059, List.forall_mem_cons.2 ⟨subd19_0_1060, List.forall_mem_cons.2 ⟨subd19_0_1061, List.forall_mem_cons.2 ⟨subd19_0_1062, List.forall_mem_cons.2 ⟨subd19_0_1063, List.forall_mem_cons.2 ⟨subd19_0_1064, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd19_1 : ldCheck G d19_1.U d19_1.ms ldd19_1 = true := by decide +kernel
theorem pre_okd19_1 : subPre G cell19 d19_1 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C143
