import ReflectZphi.Data.Cert5.C093.Base

namespace ReflectZphi.Data.Cert5.C093

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_0_800 : subd7_0 [0, 5, -1] = true := by decide +kernel
theorem subd7_0_801 : subd7_0 [0, 5, 0] = true := by decide +kernel
theorem subd7_0_802 : subd7_0 [0, 5, 1] = true := by decide +kernel
theorem subd7_0_803 : subd7_0 [0, 5, 2] = true := by decide +kernel
theorem subd7_0_804 : subd7_0 [0, 5, 3] = true := by decide +kernel
theorem subd7_0_805 : subd7_0 [0, 5, 4] = true := by decide +kernel
theorem subd7_0_806 : subd7_0 [0, 6] = true := by decide +kernel
theorem subd7_0_807 : subd7_0 [0, 7] = true := by decide +kernel
theorem subd7_0_808 : subd7_0 [1, -9] = true := by decide +kernel
theorem subd7_0_809 : subd7_0 [1, -8] = true := by decide +kernel
theorem subd7_0_810 : subd7_0 [1, -7] = true := by decide +kernel
theorem subd7_0_811 : subd7_0 [1, -6] = true := by decide +kernel
theorem subd7_0_812 : subd7_0 [1, -5, -5] = true := by decide +kernel
theorem subd7_0_813 : subd7_0 [1, -5, -4] = true := by decide +kernel
theorem subd7_0_814 : subd7_0 [1, -5, -3] = true := by decide +kernel
theorem subd7_0_815 : subd7_0 [1, -5, -2] = true := by decide +kernel
theorem subd7_0_816 : subd7_0 [1, -5, -1] = true := by decide +kernel
theorem subd7_0_817 : subd7_0 [1, -5, 0] = true := by decide +kernel
theorem subd7_0_818 : subd7_0 [1, -5, 1] = true := by decide +kernel
theorem subd7_0_819 : subd7_0 [1, -5, 2] = true := by decide +kernel
theorem subd7_0_820 : subd7_0 [1, -5, 3] = true := by decide +kernel
theorem subd7_0_821 : subd7_0 [1, -5, 4] = true := by decide +kernel
theorem subd7_0_822 : subd7_0 [1, -5, 5] = true := by decide +kernel
theorem subd7_0_823 : subd7_0 [1, -5, 6] = true := by decide +kernel
theorem subd7_0_824 : subd7_0 [1, -5, 7] = true := by decide +kernel
theorem subd7_0_825 : subd7_0 [1, -5, 8] = true := by decide +kernel
theorem subd7_0_826 : subd7_0 [1, -4, -6] = true := by decide +kernel
theorem subd7_0_827 : subd7_0 [1, -4, -5] = true := by decide +kernel
theorem subd7_0_828 : subd7_0 [1, -4, -4] = true := by decide +kernel
theorem subd7_0_829 : subd7_0 [1, -4, -3] = true := by decide +kernel
theorem subd7_0_830 : subd7_0 [1, -4, -2] = true := by decide +kernel
theorem subd7_0_831 : subd7_0 [1, -4, -1] = true := by decide +kernel
theorem sbd7_0_25 : ∀ q ∈ blkd7_0_25, subd7_0 q = true := by
  unfold blkd7_0_25
  exact List.forall_mem_cons.2 ⟨subd7_0_800, List.forall_mem_cons.2 ⟨subd7_0_801, List.forall_mem_cons.2 ⟨subd7_0_802, List.forall_mem_cons.2 ⟨subd7_0_803, List.forall_mem_cons.2 ⟨subd7_0_804, List.forall_mem_cons.2 ⟨subd7_0_805, List.forall_mem_cons.2 ⟨subd7_0_806, List.forall_mem_cons.2 ⟨subd7_0_807, List.forall_mem_cons.2 ⟨subd7_0_808, List.forall_mem_cons.2 ⟨subd7_0_809, List.forall_mem_cons.2 ⟨subd7_0_810, List.forall_mem_cons.2 ⟨subd7_0_811, List.forall_mem_cons.2 ⟨subd7_0_812, List.forall_mem_cons.2 ⟨subd7_0_813, List.forall_mem_cons.2 ⟨subd7_0_814, List.forall_mem_cons.2 ⟨subd7_0_815, List.forall_mem_cons.2 ⟨subd7_0_816, List.forall_mem_cons.2 ⟨subd7_0_817, List.forall_mem_cons.2 ⟨subd7_0_818, List.forall_mem_cons.2 ⟨subd7_0_819, List.forall_mem_cons.2 ⟨subd7_0_820, List.forall_mem_cons.2 ⟨subd7_0_821, List.forall_mem_cons.2 ⟨subd7_0_822, List.forall_mem_cons.2 ⟨subd7_0_823, List.forall_mem_cons.2 ⟨subd7_0_824, List.forall_mem_cons.2 ⟨subd7_0_825, List.forall_mem_cons.2 ⟨subd7_0_826, List.forall_mem_cons.2 ⟨subd7_0_827, List.forall_mem_cons.2 ⟨subd7_0_828, List.forall_mem_cons.2 ⟨subd7_0_829, List.forall_mem_cons.2 ⟨subd7_0_830, List.forall_mem_cons.2 ⟨subd7_0_831, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_832 : subd7_0 [1, -4, 0] = true := by decide +kernel
theorem subd7_0_833 : subd7_0 [1, -4, 1] = true := by decide +kernel
theorem subd7_0_834 : subd7_0 [1, -4, 2] = true := by decide +kernel
theorem subd7_0_835 : subd7_0 [1, -4, 3] = true := by decide +kernel
theorem subd7_0_836 : subd7_0 [1, -4, 4] = true := by decide +kernel
theorem subd7_0_837 : subd7_0 [1, -4, 5] = true := by decide +kernel
theorem subd7_0_838 : subd7_0 [1, -4, 6] = true := by decide +kernel
theorem subd7_0_839 : subd7_0 [1, -4, 7] = true := by decide +kernel
theorem subd7_0_840 : subd7_0 [1, -4, 8] = true := by decide +kernel
theorem subd7_0_841 : subd7_0 [1, -4, 9] = true := by decide +kernel
theorem subd7_0_842 : subd7_0 [1, -3, -7] = true := by decide +kernel
theorem subd7_0_843 : subd7_0 [1, -3, -6] = true := by decide +kernel
theorem subd7_0_844 : subd7_0 [1, -3, -5] = true := by decide +kernel
theorem subd7_0_845 : subd7_0 [1, -3, -4] = true := by decide +kernel
theorem subd7_0_846 : subd7_0 [1, -3, -3] = true := by decide +kernel
theorem subd7_0_847 : subd7_0 [1, -3, -2] = true := by decide +kernel
theorem subd7_0_848 : subd7_0 [1, -3, -1] = true := by decide +kernel
theorem subd7_0_849 : subd7_0 [1, -3, 0] = true := by decide +kernel
theorem subd7_0_850 : subd7_0 [1, -3, 1] = true := by decide +kernel
theorem subd7_0_851 : subd7_0 [1, -3, 2] = true := by decide +kernel
theorem subd7_0_852 : subd7_0 [1, -3, 3] = true := by decide +kernel
theorem subd7_0_853 : subd7_0 [1, -3, 4] = true := by decide +kernel
theorem subd7_0_854 : subd7_0 [1, -3, 5] = true := by decide +kernel
theorem subd7_0_855 : subd7_0 [1, -3, 6] = true := by decide +kernel
theorem subd7_0_856 : subd7_0 [1, -3, 7] = true := by decide +kernel
theorem subd7_0_857 : subd7_0 [1, -3, 8] = true := by decide +kernel
theorem subd7_0_858 : subd7_0 [1, -3, 9] = true := by decide +kernel
theorem subd7_0_859 : subd7_0 [1, -2, -8] = true := by decide +kernel
theorem subd7_0_860 : subd7_0 [1, -2, -7] = true := by decide +kernel
theorem subd7_0_861 : subd7_0 [1, -2, -6] = true := by decide +kernel
theorem subd7_0_862 : subd7_0 [1, -2, -5] = true := by decide +kernel
theorem subd7_0_863 : subd7_0 [1, -2, -4] = true := by decide +kernel
theorem sbd7_0_26 : ∀ q ∈ blkd7_0_26, subd7_0 q = true := by
  unfold blkd7_0_26
  exact List.forall_mem_cons.2 ⟨subd7_0_832, List.forall_mem_cons.2 ⟨subd7_0_833, List.forall_mem_cons.2 ⟨subd7_0_834, List.forall_mem_cons.2 ⟨subd7_0_835, List.forall_mem_cons.2 ⟨subd7_0_836, List.forall_mem_cons.2 ⟨subd7_0_837, List.forall_mem_cons.2 ⟨subd7_0_838, List.forall_mem_cons.2 ⟨subd7_0_839, List.forall_mem_cons.2 ⟨subd7_0_840, List.forall_mem_cons.2 ⟨subd7_0_841, List.forall_mem_cons.2 ⟨subd7_0_842, List.forall_mem_cons.2 ⟨subd7_0_843, List.forall_mem_cons.2 ⟨subd7_0_844, List.forall_mem_cons.2 ⟨subd7_0_845, List.forall_mem_cons.2 ⟨subd7_0_846, List.forall_mem_cons.2 ⟨subd7_0_847, List.forall_mem_cons.2 ⟨subd7_0_848, List.forall_mem_cons.2 ⟨subd7_0_849, List.forall_mem_cons.2 ⟨subd7_0_850, List.forall_mem_cons.2 ⟨subd7_0_851, List.forall_mem_cons.2 ⟨subd7_0_852, List.forall_mem_cons.2 ⟨subd7_0_853, List.forall_mem_cons.2 ⟨subd7_0_854, List.forall_mem_cons.2 ⟨subd7_0_855, List.forall_mem_cons.2 ⟨subd7_0_856, List.forall_mem_cons.2 ⟨subd7_0_857, List.forall_mem_cons.2 ⟨subd7_0_858, List.forall_mem_cons.2 ⟨subd7_0_859, List.forall_mem_cons.2 ⟨subd7_0_860, List.forall_mem_cons.2 ⟨subd7_0_861, List.forall_mem_cons.2 ⟨subd7_0_862, List.forall_mem_cons.2 ⟨subd7_0_863, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_864 : subd7_0 [1, -2, -3] = true := by decide +kernel
theorem subd7_0_865 : subd7_0 [1, -2, -2] = true := by decide +kernel
theorem subd7_0_866 : subd7_0 [1, -2, -1] = true := by decide +kernel
theorem subd7_0_867 : subd7_0 [1, -2, 0] = true := by decide +kernel
theorem subd7_0_868 : subd7_0 [1, -2, 1] = true := by decide +kernel
theorem subd7_0_869 : subd7_0 [1, -2, 2] = true := by decide +kernel
theorem subd7_0_870 : subd7_0 [1, -2, 3] = true := by decide +kernel
theorem subd7_0_871 : subd7_0 [1, -2, 4] = true := by decide +kernel
theorem subd7_0_872 : subd7_0 [1, -2, 5] = true := by decide +kernel
theorem subd7_0_873 : subd7_0 [1, -2, 6] = true := by decide +kernel
theorem subd7_0_874 : subd7_0 [1, -2, 7] = true := by decide +kernel
theorem subd7_0_875 : subd7_0 [1, -2, 8] = true := by decide +kernel
theorem subd7_0_876 : subd7_0 [1, -2, 9] = true := by decide +kernel
theorem subd7_0_877 : subd7_0 [1, -1, -9] = true := by decide +kernel
theorem subd7_0_878 : subd7_0 [1, -1, -8] = true := by decide +kernel
theorem subd7_0_879 : subd7_0 [1, -1, -7] = true := by decide +kernel
theorem subd7_0_880 : subd7_0 [1, -1, -6] = true := by decide +kernel
theorem subd7_0_881 : subd7_0 [1, -1, -5] = true := by decide +kernel
theorem subd7_0_882 : subd7_0 [1, -1, -4] = true := by decide +kernel
theorem subd7_0_883 : subd7_0 [1, -1, -3] = true := by decide +kernel
theorem subd7_0_884 : subd7_0 [1, -1, -2] = true := by decide +kernel
theorem subd7_0_885 : subd7_0 [1, -1, -1] = true := by decide +kernel
theorem subd7_0_886 : subd7_0 [1, -1, 0] = true := by decide +kernel
theorem subd7_0_887 : subd7_0 [1, -1, 1] = true := by decide +kernel
theorem subd7_0_888 : subd7_0 [1, -1, 2] = true := by decide +kernel
theorem subd7_0_889 : subd7_0 [1, -1, 3] = true := by decide +kernel
theorem subd7_0_890 : subd7_0 [1, -1, 4] = true := by decide +kernel
theorem subd7_0_891 : subd7_0 [1, -1, 5] = true := by decide +kernel
theorem subd7_0_892 : subd7_0 [1, -1, 6] = true := by decide +kernel
theorem subd7_0_893 : subd7_0 [1, -1, 7] = true := by decide +kernel
theorem subd7_0_894 : subd7_0 [1, -1, 8] = true := by decide +kernel
theorem subd7_0_895 : subd7_0 [1, 0, -9] = true := by decide +kernel
theorem sbd7_0_27 : ∀ q ∈ blkd7_0_27, subd7_0 q = true := by
  unfold blkd7_0_27
  exact List.forall_mem_cons.2 ⟨subd7_0_864, List.forall_mem_cons.2 ⟨subd7_0_865, List.forall_mem_cons.2 ⟨subd7_0_866, List.forall_mem_cons.2 ⟨subd7_0_867, List.forall_mem_cons.2 ⟨subd7_0_868, List.forall_mem_cons.2 ⟨subd7_0_869, List.forall_mem_cons.2 ⟨subd7_0_870, List.forall_mem_cons.2 ⟨subd7_0_871, List.forall_mem_cons.2 ⟨subd7_0_872, List.forall_mem_cons.2 ⟨subd7_0_873, List.forall_mem_cons.2 ⟨subd7_0_874, List.forall_mem_cons.2 ⟨subd7_0_875, List.forall_mem_cons.2 ⟨subd7_0_876, List.forall_mem_cons.2 ⟨subd7_0_877, List.forall_mem_cons.2 ⟨subd7_0_878, List.forall_mem_cons.2 ⟨subd7_0_879, List.forall_mem_cons.2 ⟨subd7_0_880, List.forall_mem_cons.2 ⟨subd7_0_881, List.forall_mem_cons.2 ⟨subd7_0_882, List.forall_mem_cons.2 ⟨subd7_0_883, List.forall_mem_cons.2 ⟨subd7_0_884, List.forall_mem_cons.2 ⟨subd7_0_885, List.forall_mem_cons.2 ⟨subd7_0_886, List.forall_mem_cons.2 ⟨subd7_0_887, List.forall_mem_cons.2 ⟨subd7_0_888, List.forall_mem_cons.2 ⟨subd7_0_889, List.forall_mem_cons.2 ⟨subd7_0_890, List.forall_mem_cons.2 ⟨subd7_0_891, List.forall_mem_cons.2 ⟨subd7_0_892, List.forall_mem_cons.2 ⟨subd7_0_893, List.forall_mem_cons.2 ⟨subd7_0_894, List.forall_mem_cons.2 ⟨subd7_0_895, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_896 : subd7_0 [1, 0, -8] = true := by decide +kernel
theorem subd7_0_897 : subd7_0 [1, 0, -7] = true := by decide +kernel
theorem subd7_0_898 : subd7_0 [1, 0, -6] = true := by decide +kernel
theorem subd7_0_899 : subd7_0 [1, 0, -5] = true := by decide +kernel
theorem subd7_0_900 : subd7_0 [1, 0, -4] = true := by decide +kernel
theorem subd7_0_901 : subd7_0 [1, 0, -3] = true := by decide +kernel
theorem subd7_0_902 : subd7_0 [1, 0, -2] = true := by decide +kernel
theorem subd7_0_903 : subd7_0 [1, 0, -1] = true := by decide +kernel
theorem subd7_0_904 : subd7_0 [1, 0, 0] = true := by decide +kernel
theorem subd7_0_905 : subd7_0 [1, 0, 1] = true := by decide +kernel
theorem subd7_0_906 : subd7_0 [1, 0, 2] = true := by decide +kernel
theorem subd7_0_907 : subd7_0 [1, 0, 3] = true := by decide +kernel
theorem subd7_0_908 : subd7_0 [1, 0, 4] = true := by decide +kernel
theorem subd7_0_909 : subd7_0 [1, 0, 5] = true := by decide +kernel
theorem subd7_0_910 : subd7_0 [1, 0, 6] = true := by decide +kernel
theorem subd7_0_911 : subd7_0 [1, 0, 7] = true := by decide +kernel
theorem subd7_0_912 : subd7_0 [1, 0, 8] = true := by decide +kernel
theorem subd7_0_913 : subd7_0 [1, 1, -9] = true := by decide +kernel
theorem subd7_0_914 : subd7_0 [1, 1, -8] = true := by decide +kernel
theorem subd7_0_915 : subd7_0 [1, 1, -7] = true := by decide +kernel
theorem subd7_0_916 : subd7_0 [1, 1, -6] = true := by decide +kernel
theorem subd7_0_917 : subd7_0 [1, 1, -5] = true := by decide +kernel
theorem subd7_0_918 : subd7_0 [1, 1, -4] = true := by decide +kernel
theorem subd7_0_919 : subd7_0 [1, 1, -3] = true := by decide +kernel
theorem subd7_0_920 : subd7_0 [1, 1, -2] = true := by decide +kernel
theorem subd7_0_921 : subd7_0 [1, 1, -1] = true := by decide +kernel
theorem subd7_0_922 : subd7_0 [1, 1, 0] = true := by decide +kernel
theorem subd7_0_923 : subd7_0 [1, 1, 1] = true := by decide +kernel
theorem subd7_0_924 : subd7_0 [1, 1, 2] = true := by decide +kernel
theorem subd7_0_925 : subd7_0 [1, 1, 3] = true := by decide +kernel
theorem subd7_0_926 : subd7_0 [1, 1, 4] = true := by decide +kernel
theorem subd7_0_927 : subd7_0 [1, 1, 5] = true := by decide +kernel
theorem sbd7_0_28 : ∀ q ∈ blkd7_0_28, subd7_0 q = true := by
  unfold blkd7_0_28
  exact List.forall_mem_cons.2 ⟨subd7_0_896, List.forall_mem_cons.2 ⟨subd7_0_897, List.forall_mem_cons.2 ⟨subd7_0_898, List.forall_mem_cons.2 ⟨subd7_0_899, List.forall_mem_cons.2 ⟨subd7_0_900, List.forall_mem_cons.2 ⟨subd7_0_901, List.forall_mem_cons.2 ⟨subd7_0_902, List.forall_mem_cons.2 ⟨subd7_0_903, List.forall_mem_cons.2 ⟨subd7_0_904, List.forall_mem_cons.2 ⟨subd7_0_905, List.forall_mem_cons.2 ⟨subd7_0_906, List.forall_mem_cons.2 ⟨subd7_0_907, List.forall_mem_cons.2 ⟨subd7_0_908, List.forall_mem_cons.2 ⟨subd7_0_909, List.forall_mem_cons.2 ⟨subd7_0_910, List.forall_mem_cons.2 ⟨subd7_0_911, List.forall_mem_cons.2 ⟨subd7_0_912, List.forall_mem_cons.2 ⟨subd7_0_913, List.forall_mem_cons.2 ⟨subd7_0_914, List.forall_mem_cons.2 ⟨subd7_0_915, List.forall_mem_cons.2 ⟨subd7_0_916, List.forall_mem_cons.2 ⟨subd7_0_917, List.forall_mem_cons.2 ⟨subd7_0_918, List.forall_mem_cons.2 ⟨subd7_0_919, List.forall_mem_cons.2 ⟨subd7_0_920, List.forall_mem_cons.2 ⟨subd7_0_921, List.forall_mem_cons.2 ⟨subd7_0_922, List.forall_mem_cons.2 ⟨subd7_0_923, List.forall_mem_cons.2 ⟨subd7_0_924, List.forall_mem_cons.2 ⟨subd7_0_925, List.forall_mem_cons.2 ⟨subd7_0_926, List.forall_mem_cons.2 ⟨subd7_0_927, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_928 : subd7_0 [1, 1, 6] = true := by decide +kernel
theorem subd7_0_929 : subd7_0 [1, 1, 7] = true := by decide +kernel
theorem subd7_0_930 : subd7_0 [1, 1, 8] = true := by decide +kernel
theorem subd7_0_931 : subd7_0 [1, 2, -10] = true := by decide +kernel
theorem subd7_0_932 : subd7_0 [1, 2, -9] = true := by decide +kernel
theorem subd7_0_933 : subd7_0 [1, 2, -8] = true := by decide +kernel
theorem subd7_0_934 : subd7_0 [1, 2, -7] = true := by decide +kernel
theorem subd7_0_935 : subd7_0 [1, 2, -6] = true := by decide +kernel
theorem subd7_0_936 : subd7_0 [1, 2, -5] = true := by decide +kernel
theorem subd7_0_937 : subd7_0 [1, 2, -4] = true := by decide +kernel
theorem subd7_0_938 : subd7_0 [1, 2, -3] = true := by decide +kernel
theorem subd7_0_939 : subd7_0 [1, 2, -2] = true := by decide +kernel
theorem subd7_0_940 : subd7_0 [1, 2, -1] = true := by decide +kernel
theorem subd7_0_941 : subd7_0 [1, 2, 0] = true := by decide +kernel
theorem subd7_0_942 : subd7_0 [1, 2, 1] = true := by decide +kernel
theorem subd7_0_943 : subd7_0 [1, 2, 2] = true := by decide +kernel
theorem subd7_0_944 : subd7_0 [1, 2, 3] = true := by decide +kernel
theorem subd7_0_945 : subd7_0 [1, 2, 4] = true := by decide +kernel
theorem subd7_0_946 : subd7_0 [1, 2, 5] = true := by decide +kernel
theorem subd7_0_947 : subd7_0 [1, 2, 6] = true := by decide +kernel
theorem subd7_0_948 : subd7_0 [1, 2, 7] = true := by decide +kernel
theorem subd7_0_949 : subd7_0 [1, 3, -10] = true := by decide +kernel
theorem subd7_0_950 : subd7_0 [1, 3, -9] = true := by decide +kernel
theorem subd7_0_951 : subd7_0 [1, 3, -8] = true := by decide +kernel
theorem subd7_0_952 : subd7_0 [1, 3, -7] = true := by decide +kernel
theorem subd7_0_953 : subd7_0 [1, 3, -6] = true := by decide +kernel
theorem subd7_0_954 : subd7_0 [1, 3, -5] = true := by decide +kernel
theorem subd7_0_955 : subd7_0 [1, 3, -4] = true := by decide +kernel
theorem subd7_0_956 : subd7_0 [1, 3, -3] = true := by decide +kernel
theorem subd7_0_957 : subd7_0 [1, 3, -2] = true := by decide +kernel
theorem subd7_0_958 : subd7_0 [1, 3, -1] = true := by decide +kernel
theorem subd7_0_959 : subd7_0 [1, 3, 0] = true := by decide +kernel
theorem sbd7_0_29 : ∀ q ∈ blkd7_0_29, subd7_0 q = true := by
  unfold blkd7_0_29
  exact List.forall_mem_cons.2 ⟨subd7_0_928, List.forall_mem_cons.2 ⟨subd7_0_929, List.forall_mem_cons.2 ⟨subd7_0_930, List.forall_mem_cons.2 ⟨subd7_0_931, List.forall_mem_cons.2 ⟨subd7_0_932, List.forall_mem_cons.2 ⟨subd7_0_933, List.forall_mem_cons.2 ⟨subd7_0_934, List.forall_mem_cons.2 ⟨subd7_0_935, List.forall_mem_cons.2 ⟨subd7_0_936, List.forall_mem_cons.2 ⟨subd7_0_937, List.forall_mem_cons.2 ⟨subd7_0_938, List.forall_mem_cons.2 ⟨subd7_0_939, List.forall_mem_cons.2 ⟨subd7_0_940, List.forall_mem_cons.2 ⟨subd7_0_941, List.forall_mem_cons.2 ⟨subd7_0_942, List.forall_mem_cons.2 ⟨subd7_0_943, List.forall_mem_cons.2 ⟨subd7_0_944, List.forall_mem_cons.2 ⟨subd7_0_945, List.forall_mem_cons.2 ⟨subd7_0_946, List.forall_mem_cons.2 ⟨subd7_0_947, List.forall_mem_cons.2 ⟨subd7_0_948, List.forall_mem_cons.2 ⟨subd7_0_949, List.forall_mem_cons.2 ⟨subd7_0_950, List.forall_mem_cons.2 ⟨subd7_0_951, List.forall_mem_cons.2 ⟨subd7_0_952, List.forall_mem_cons.2 ⟨subd7_0_953, List.forall_mem_cons.2 ⟨subd7_0_954, List.forall_mem_cons.2 ⟨subd7_0_955, List.forall_mem_cons.2 ⟨subd7_0_956, List.forall_mem_cons.2 ⟨subd7_0_957, List.forall_mem_cons.2 ⟨subd7_0_958, List.forall_mem_cons.2 ⟨subd7_0_959, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_960 : subd7_0 [1, 3, 1] = true := by decide +kernel
theorem subd7_0_961 : subd7_0 [1, 3, 2] = true := by decide +kernel
theorem subd7_0_962 : subd7_0 [1, 3, 3] = true := by decide +kernel
theorem subd7_0_963 : subd7_0 [1, 3, 4] = true := by decide +kernel
theorem subd7_0_964 : subd7_0 [1, 3, 5] = true := by decide +kernel
theorem subd7_0_965 : subd7_0 [1, 3, 6] = true := by decide +kernel
theorem subd7_0_966 : subd7_0 [1, 4, -10] = true := by decide +kernel
theorem subd7_0_967 : subd7_0 [1, 4, -9] = true := by decide +kernel
theorem subd7_0_968 : subd7_0 [1, 4, -8] = true := by decide +kernel
theorem subd7_0_969 : subd7_0 [1, 4, -7] = true := by decide +kernel
theorem subd7_0_970 : subd7_0 [1, 4, -6] = true := by decide +kernel
theorem subd7_0_971 : subd7_0 [1, 4, -5] = true := by decide +kernel
theorem subd7_0_972 : subd7_0 [1, 4, -4] = true := by decide +kernel
theorem subd7_0_973 : subd7_0 [1, 4, -3] = true := by decide +kernel
theorem subd7_0_974 : subd7_0 [1, 4, -2] = true := by decide +kernel
theorem subd7_0_975 : subd7_0 [1, 4, -1] = true := by decide +kernel
theorem subd7_0_976 : subd7_0 [1, 4, 0] = true := by decide +kernel
theorem subd7_0_977 : subd7_0 [1, 4, 1] = true := by decide +kernel
theorem subd7_0_978 : subd7_0 [1, 4, 2] = true := by decide +kernel
theorem subd7_0_979 : subd7_0 [1, 4, 3] = true := by decide +kernel
theorem subd7_0_980 : subd7_0 [1, 4, 4] = true := by decide +kernel
theorem subd7_0_981 : subd7_0 [1, 4, 5] = true := by decide +kernel
theorem subd7_0_982 : subd7_0 [1, 5, -9] = true := by decide +kernel
theorem subd7_0_983 : subd7_0 [1, 5, -8] = true := by decide +kernel
theorem subd7_0_984 : subd7_0 [1, 5, -7] = true := by decide +kernel
theorem subd7_0_985 : subd7_0 [1, 5, -6] = true := by decide +kernel
theorem subd7_0_986 : subd7_0 [1, 5, -5] = true := by decide +kernel
theorem subd7_0_987 : subd7_0 [1, 5, -4] = true := by decide +kernel
theorem subd7_0_988 : subd7_0 [1, 5, -3] = true := by decide +kernel
theorem subd7_0_989 : subd7_0 [1, 5, -2] = true := by decide +kernel
theorem subd7_0_990 : subd7_0 [1, 5, -1] = true := by decide +kernel
theorem subd7_0_991 : subd7_0 [1, 5, 0] = true := by decide +kernel
theorem sbd7_0_30 : ∀ q ∈ blkd7_0_30, subd7_0 q = true := by
  unfold blkd7_0_30
  exact List.forall_mem_cons.2 ⟨subd7_0_960, List.forall_mem_cons.2 ⟨subd7_0_961, List.forall_mem_cons.2 ⟨subd7_0_962, List.forall_mem_cons.2 ⟨subd7_0_963, List.forall_mem_cons.2 ⟨subd7_0_964, List.forall_mem_cons.2 ⟨subd7_0_965, List.forall_mem_cons.2 ⟨subd7_0_966, List.forall_mem_cons.2 ⟨subd7_0_967, List.forall_mem_cons.2 ⟨subd7_0_968, List.forall_mem_cons.2 ⟨subd7_0_969, List.forall_mem_cons.2 ⟨subd7_0_970, List.forall_mem_cons.2 ⟨subd7_0_971, List.forall_mem_cons.2 ⟨subd7_0_972, List.forall_mem_cons.2 ⟨subd7_0_973, List.forall_mem_cons.2 ⟨subd7_0_974, List.forall_mem_cons.2 ⟨subd7_0_975, List.forall_mem_cons.2 ⟨subd7_0_976, List.forall_mem_cons.2 ⟨subd7_0_977, List.forall_mem_cons.2 ⟨subd7_0_978, List.forall_mem_cons.2 ⟨subd7_0_979, List.forall_mem_cons.2 ⟨subd7_0_980, List.forall_mem_cons.2 ⟨subd7_0_981, List.forall_mem_cons.2 ⟨subd7_0_982, List.forall_mem_cons.2 ⟨subd7_0_983, List.forall_mem_cons.2 ⟨subd7_0_984, List.forall_mem_cons.2 ⟨subd7_0_985, List.forall_mem_cons.2 ⟨subd7_0_986, List.forall_mem_cons.2 ⟨subd7_0_987, List.forall_mem_cons.2 ⟨subd7_0_988, List.forall_mem_cons.2 ⟨subd7_0_989, List.forall_mem_cons.2 ⟨subd7_0_990, List.forall_mem_cons.2 ⟨subd7_0_991, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_992 : subd7_0 [1, 5, 1] = true := by decide +kernel
theorem subd7_0_993 : subd7_0 [1, 5, 2] = true := by decide +kernel
theorem subd7_0_994 : subd7_0 [1, 5, 3] = true := by decide +kernel
theorem subd7_0_995 : subd7_0 [1, 5, 4] = true := by decide +kernel
theorem subd7_0_996 : subd7_0 [1, 6] = true := by decide +kernel
theorem subd7_0_997 : subd7_0 [1, 7] = true := by decide +kernel
theorem subd7_0_998 : subd7_0 [2, -9] = true := by decide +kernel
theorem subd7_0_999 : subd7_0 [2, -8] = true := by decide +kernel
theorem subd7_0_1000 : subd7_0 [2, -7] = true := by decide +kernel
theorem subd7_0_1001 : subd7_0 [2, -6] = true := by decide +kernel
theorem subd7_0_1002 : subd7_0 [2, -5, -5] = true := by decide +kernel
theorem subd7_0_1003 : subd7_0 [2, -5, -4] = true := by decide +kernel
theorem subd7_0_1004 : subd7_0 [2, -5, -3] = true := by decide +kernel
theorem subd7_0_1005 : subd7_0 [2, -5, -2] = true := by decide +kernel
theorem subd7_0_1006 : subd7_0 [2, -5, -1] = true := by decide +kernel
theorem subd7_0_1007 : subd7_0 [2, -5, 0] = true := by decide +kernel
theorem subd7_0_1008 : subd7_0 [2, -5, 1] = true := by decide +kernel
theorem subd7_0_1009 : subd7_0 [2, -5, 2] = true := by decide +kernel
theorem subd7_0_1010 : subd7_0 [2, -5, 3] = true := by decide +kernel
theorem subd7_0_1011 : subd7_0 [2, -5, 4] = true := by decide +kernel
theorem subd7_0_1012 : subd7_0 [2, -5, 5] = true := by decide +kernel
theorem subd7_0_1013 : subd7_0 [2, -5, 6] = true := by decide +kernel
theorem subd7_0_1014 : subd7_0 [2, -5, 7] = true := by decide +kernel
theorem subd7_0_1015 : subd7_0 [2, -5, 8] = true := by decide +kernel
theorem subd7_0_1016 : subd7_0 [2, -4, -6] = true := by decide +kernel
theorem subd7_0_1017 : subd7_0 [2, -4, -5] = true := by decide +kernel
theorem subd7_0_1018 : subd7_0 [2, -4, -4] = true := by decide +kernel
theorem subd7_0_1019 : subd7_0 [2, -4, -3] = true := by decide +kernel
theorem subd7_0_1020 : subd7_0 [2, -4, -2] = true := by decide +kernel
theorem subd7_0_1021 : subd7_0 [2, -4, -1] = true := by decide +kernel
theorem subd7_0_1022 : subd7_0 [2, -4, 0] = true := by decide +kernel
theorem subd7_0_1023 : subd7_0 [2, -4, 1] = true := by decide +kernel
theorem sbd7_0_31 : ∀ q ∈ blkd7_0_31, subd7_0 q = true := by
  unfold blkd7_0_31
  exact List.forall_mem_cons.2 ⟨subd7_0_992, List.forall_mem_cons.2 ⟨subd7_0_993, List.forall_mem_cons.2 ⟨subd7_0_994, List.forall_mem_cons.2 ⟨subd7_0_995, List.forall_mem_cons.2 ⟨subd7_0_996, List.forall_mem_cons.2 ⟨subd7_0_997, List.forall_mem_cons.2 ⟨subd7_0_998, List.forall_mem_cons.2 ⟨subd7_0_999, List.forall_mem_cons.2 ⟨subd7_0_1000, List.forall_mem_cons.2 ⟨subd7_0_1001, List.forall_mem_cons.2 ⟨subd7_0_1002, List.forall_mem_cons.2 ⟨subd7_0_1003, List.forall_mem_cons.2 ⟨subd7_0_1004, List.forall_mem_cons.2 ⟨subd7_0_1005, List.forall_mem_cons.2 ⟨subd7_0_1006, List.forall_mem_cons.2 ⟨subd7_0_1007, List.forall_mem_cons.2 ⟨subd7_0_1008, List.forall_mem_cons.2 ⟨subd7_0_1009, List.forall_mem_cons.2 ⟨subd7_0_1010, List.forall_mem_cons.2 ⟨subd7_0_1011, List.forall_mem_cons.2 ⟨subd7_0_1012, List.forall_mem_cons.2 ⟨subd7_0_1013, List.forall_mem_cons.2 ⟨subd7_0_1014, List.forall_mem_cons.2 ⟨subd7_0_1015, List.forall_mem_cons.2 ⟨subd7_0_1016, List.forall_mem_cons.2 ⟨subd7_0_1017, List.forall_mem_cons.2 ⟨subd7_0_1018, List.forall_mem_cons.2 ⟨subd7_0_1019, List.forall_mem_cons.2 ⟨subd7_0_1020, List.forall_mem_cons.2 ⟨subd7_0_1021, List.forall_mem_cons.2 ⟨subd7_0_1022, List.forall_mem_cons.2 ⟨subd7_0_1023, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_1024 : subd7_0 [2, -4, 2] = true := by decide +kernel
theorem subd7_0_1025 : subd7_0 [2, -4, 3] = true := by decide +kernel
theorem subd7_0_1026 : subd7_0 [2, -4, 4] = true := by decide +kernel
theorem subd7_0_1027 : subd7_0 [2, -4, 5] = true := by decide +kernel
theorem subd7_0_1028 : subd7_0 [2, -4, 6] = true := by decide +kernel
theorem subd7_0_1029 : subd7_0 [2, -4, 7] = true := by decide +kernel
theorem subd7_0_1030 : subd7_0 [2, -4, 8] = true := by decide +kernel
theorem subd7_0_1031 : subd7_0 [2, -4, 9] = true := by decide +kernel
theorem subd7_0_1032 : subd7_0 [2, -3, -7] = true := by decide +kernel
theorem subd7_0_1033 : subd7_0 [2, -3, -6] = true := by decide +kernel
theorem subd7_0_1034 : subd7_0 [2, -3, -5] = true := by decide +kernel
theorem subd7_0_1035 : subd7_0 [2, -3, -4] = true := by decide +kernel
theorem subd7_0_1036 : subd7_0 [2, -3, -3] = true := by decide +kernel
theorem subd7_0_1037 : subd7_0 [2, -3, -2] = true := by decide +kernel
theorem subd7_0_1038 : subd7_0 [2, -3, -1] = true := by decide +kernel
theorem subd7_0_1039 : subd7_0 [2, -3, 0] = true := by decide +kernel
theorem subd7_0_1040 : subd7_0 [2, -3, 1] = true := by decide +kernel
theorem subd7_0_1041 : subd7_0 [2, -3, 2] = true := by decide +kernel
theorem subd7_0_1042 : subd7_0 [2, -3, 3] = true := by decide +kernel
theorem subd7_0_1043 : subd7_0 [2, -3, 4] = true := by decide +kernel
theorem subd7_0_1044 : subd7_0 [2, -3, 5] = true := by decide +kernel
theorem subd7_0_1045 : subd7_0 [2, -3, 6] = true := by decide +kernel
theorem subd7_0_1046 : subd7_0 [2, -3, 7] = true := by decide +kernel
theorem subd7_0_1047 : subd7_0 [2, -3, 8] = true := by decide +kernel
theorem subd7_0_1048 : subd7_0 [2, -3, 9] = true := by decide +kernel
theorem subd7_0_1049 : subd7_0 [2, -2, -8] = true := by decide +kernel
theorem subd7_0_1050 : subd7_0 [2, -2, -7] = true := by decide +kernel
theorem subd7_0_1051 : subd7_0 [2, -2, -6] = true := by decide +kernel
theorem subd7_0_1052 : subd7_0 [2, -2, -5] = true := by decide +kernel
theorem subd7_0_1053 : subd7_0 [2, -2, -4] = true := by decide +kernel
theorem subd7_0_1054 : subd7_0 [2, -2, -3] = true := by decide +kernel
theorem subd7_0_1055 : subd7_0 [2, -2, -2] = true := by decide +kernel
theorem sbd7_0_32 : ∀ q ∈ blkd7_0_32, subd7_0 q = true := by
  unfold blkd7_0_32
  exact List.forall_mem_cons.2 ⟨subd7_0_1024, List.forall_mem_cons.2 ⟨subd7_0_1025, List.forall_mem_cons.2 ⟨subd7_0_1026, List.forall_mem_cons.2 ⟨subd7_0_1027, List.forall_mem_cons.2 ⟨subd7_0_1028, List.forall_mem_cons.2 ⟨subd7_0_1029, List.forall_mem_cons.2 ⟨subd7_0_1030, List.forall_mem_cons.2 ⟨subd7_0_1031, List.forall_mem_cons.2 ⟨subd7_0_1032, List.forall_mem_cons.2 ⟨subd7_0_1033, List.forall_mem_cons.2 ⟨subd7_0_1034, List.forall_mem_cons.2 ⟨subd7_0_1035, List.forall_mem_cons.2 ⟨subd7_0_1036, List.forall_mem_cons.2 ⟨subd7_0_1037, List.forall_mem_cons.2 ⟨subd7_0_1038, List.forall_mem_cons.2 ⟨subd7_0_1039, List.forall_mem_cons.2 ⟨subd7_0_1040, List.forall_mem_cons.2 ⟨subd7_0_1041, List.forall_mem_cons.2 ⟨subd7_0_1042, List.forall_mem_cons.2 ⟨subd7_0_1043, List.forall_mem_cons.2 ⟨subd7_0_1044, List.forall_mem_cons.2 ⟨subd7_0_1045, List.forall_mem_cons.2 ⟨subd7_0_1046, List.forall_mem_cons.2 ⟨subd7_0_1047, List.forall_mem_cons.2 ⟨subd7_0_1048, List.forall_mem_cons.2 ⟨subd7_0_1049, List.forall_mem_cons.2 ⟨subd7_0_1050, List.forall_mem_cons.2 ⟨subd7_0_1051, List.forall_mem_cons.2 ⟨subd7_0_1052, List.forall_mem_cons.2 ⟨subd7_0_1053, List.forall_mem_cons.2 ⟨subd7_0_1054, List.forall_mem_cons.2 ⟨subd7_0_1055, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_1056 : subd7_0 [2, -2, -1] = true := by decide +kernel
theorem subd7_0_1057 : subd7_0 [2, -2, 0] = true := by decide +kernel
theorem subd7_0_1058 : subd7_0 [2, -2, 1] = true := by decide +kernel
theorem subd7_0_1059 : subd7_0 [2, -2, 2] = true := by decide +kernel
theorem subd7_0_1060 : subd7_0 [2, -2, 3] = true := by decide +kernel
theorem subd7_0_1061 : subd7_0 [2, -2, 4] = true := by decide +kernel
theorem subd7_0_1062 : subd7_0 [2, -2, 5] = true := by decide +kernel
theorem subd7_0_1063 : subd7_0 [2, -2, 6] = true := by decide +kernel
theorem subd7_0_1064 : subd7_0 [2, -2, 7] = true := by decide +kernel
theorem subd7_0_1065 : subd7_0 [2, -2, 8] = true := by decide +kernel
theorem subd7_0_1066 : subd7_0 [2, -2, 9] = true := by decide +kernel
theorem subd7_0_1067 : subd7_0 [2, -1, -8] = true := by decide +kernel
theorem subd7_0_1068 : subd7_0 [2, -1, -7] = true := by decide +kernel
theorem subd7_0_1069 : subd7_0 [2, -1, -6] = true := by decide +kernel
theorem subd7_0_1070 : subd7_0 [2, -1, -5] = true := by decide +kernel
theorem subd7_0_1071 : subd7_0 [2, -1, -4] = true := by decide +kernel
theorem subd7_0_1072 : subd7_0 [2, -1, -3] = true := by decide +kernel
theorem subd7_0_1073 : subd7_0 [2, -1, -2] = true := by decide +kernel
theorem subd7_0_1074 : subd7_0 [2, -1, -1] = true := by decide +kernel
theorem subd7_0_1075 : subd7_0 [2, -1, 0] = true := by decide +kernel
theorem subd7_0_1076 : subd7_0 [2, -1, 1] = true := by decide +kernel
theorem subd7_0_1077 : subd7_0 [2, -1, 2] = true := by decide +kernel
theorem subd7_0_1078 : subd7_0 [2, -1, 3] = true := by decide +kernel
theorem subd7_0_1079 : subd7_0 [2, -1, 4] = true := by decide +kernel
theorem subd7_0_1080 : subd7_0 [2, -1, 5] = true := by decide +kernel
theorem subd7_0_1081 : subd7_0 [2, -1, 6] = true := by decide +kernel
theorem subd7_0_1082 : subd7_0 [2, -1, 7] = true := by decide +kernel
theorem subd7_0_1083 : subd7_0 [2, -1, 8] = true := by decide +kernel
theorem subd7_0_1084 : subd7_0 [2, 0, -9] = true := by decide +kernel
theorem subd7_0_1085 : subd7_0 [2, 0, -8] = true := by decide +kernel
theorem subd7_0_1086 : subd7_0 [2, 0, -7] = true := by decide +kernel
theorem subd7_0_1087 : subd7_0 [2, 0, -6] = true := by decide +kernel
theorem sbd7_0_33 : ∀ q ∈ blkd7_0_33, subd7_0 q = true := by
  unfold blkd7_0_33
  exact List.forall_mem_cons.2 ⟨subd7_0_1056, List.forall_mem_cons.2 ⟨subd7_0_1057, List.forall_mem_cons.2 ⟨subd7_0_1058, List.forall_mem_cons.2 ⟨subd7_0_1059, List.forall_mem_cons.2 ⟨subd7_0_1060, List.forall_mem_cons.2 ⟨subd7_0_1061, List.forall_mem_cons.2 ⟨subd7_0_1062, List.forall_mem_cons.2 ⟨subd7_0_1063, List.forall_mem_cons.2 ⟨subd7_0_1064, List.forall_mem_cons.2 ⟨subd7_0_1065, List.forall_mem_cons.2 ⟨subd7_0_1066, List.forall_mem_cons.2 ⟨subd7_0_1067, List.forall_mem_cons.2 ⟨subd7_0_1068, List.forall_mem_cons.2 ⟨subd7_0_1069, List.forall_mem_cons.2 ⟨subd7_0_1070, List.forall_mem_cons.2 ⟨subd7_0_1071, List.forall_mem_cons.2 ⟨subd7_0_1072, List.forall_mem_cons.2 ⟨subd7_0_1073, List.forall_mem_cons.2 ⟨subd7_0_1074, List.forall_mem_cons.2 ⟨subd7_0_1075, List.forall_mem_cons.2 ⟨subd7_0_1076, List.forall_mem_cons.2 ⟨subd7_0_1077, List.forall_mem_cons.2 ⟨subd7_0_1078, List.forall_mem_cons.2 ⟨subd7_0_1079, List.forall_mem_cons.2 ⟨subd7_0_1080, List.forall_mem_cons.2 ⟨subd7_0_1081, List.forall_mem_cons.2 ⟨subd7_0_1082, List.forall_mem_cons.2 ⟨subd7_0_1083, List.forall_mem_cons.2 ⟨subd7_0_1084, List.forall_mem_cons.2 ⟨subd7_0_1085, List.forall_mem_cons.2 ⟨subd7_0_1086, List.forall_mem_cons.2 ⟨subd7_0_1087, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_1088 : subd7_0 [2, 0, -5] = true := by decide +kernel
theorem subd7_0_1089 : subd7_0 [2, 0, -4] = true := by decide +kernel
theorem subd7_0_1090 : subd7_0 [2, 0, -3] = true := by decide +kernel
theorem subd7_0_1091 : subd7_0 [2, 0, -2] = true := by decide +kernel
theorem subd7_0_1092 : subd7_0 [2, 0, -1] = true := by decide +kernel
theorem subd7_0_1093 : subd7_0 [2, 0, 0] = true := by decide +kernel
theorem subd7_0_1094 : subd7_0 [2, 0, 1] = true := by decide +kernel
theorem subd7_0_1095 : subd7_0 [2, 0, 2] = true := by decide +kernel
theorem subd7_0_1096 : subd7_0 [2, 0, 3] = true := by decide +kernel
theorem subd7_0_1097 : subd7_0 [2, 0, 4] = true := by decide +kernel
theorem subd7_0_1098 : subd7_0 [2, 0, 5] = true := by decide +kernel
theorem subd7_0_1099 : subd7_0 [2, 0, 6] = true := by decide +kernel
theorem subd7_0_1100 : subd7_0 [2, 0, 7] = true := by decide +kernel
theorem subd7_0_1101 : subd7_0 [2, 0, 8] = true := by decide +kernel
theorem subd7_0_1102 : subd7_0 [2, 1, -9] = true := by decide +kernel
theorem subd7_0_1103 : subd7_0 [2, 1, -8] = true := by decide +kernel
theorem subd7_0_1104 : subd7_0 [2, 1, -7] = true := by decide +kernel
theorem subd7_0_1105 : subd7_0 [2, 1, -6] = true := by decide +kernel
theorem subd7_0_1106 : subd7_0 [2, 1, -5] = true := by decide +kernel
theorem subd7_0_1107 : subd7_0 [2, 1, -4] = true := by decide +kernel
theorem subd7_0_1108 : subd7_0 [2, 1, -3] = true := by decide +kernel
theorem subd7_0_1109 : subd7_0 [2, 1, -2] = true := by decide +kernel
theorem subd7_0_1110 : subd7_0 [2, 1, -1] = true := by decide +kernel
theorem subd7_0_1111 : subd7_0 [2, 1, 0] = true := by decide +kernel
theorem subd7_0_1112 : subd7_0 [2, 1, 1] = true := by decide +kernel
theorem subd7_0_1113 : subd7_0 [2, 1, 2] = true := by decide +kernel
theorem subd7_0_1114 : subd7_0 [2, 1, 3] = true := by decide +kernel
theorem subd7_0_1115 : subd7_0 [2, 1, 4] = true := by decide +kernel
theorem subd7_0_1116 : subd7_0 [2, 1, 5] = true := by decide +kernel
theorem subd7_0_1117 : subd7_0 [2, 1, 6] = true := by decide +kernel
theorem subd7_0_1118 : subd7_0 [2, 1, 7] = true := by decide +kernel
theorem subd7_0_1119 : subd7_0 [2, 2, -9] = true := by decide +kernel
theorem sbd7_0_34 : ∀ q ∈ blkd7_0_34, subd7_0 q = true := by
  unfold blkd7_0_34
  exact List.forall_mem_cons.2 ⟨subd7_0_1088, List.forall_mem_cons.2 ⟨subd7_0_1089, List.forall_mem_cons.2 ⟨subd7_0_1090, List.forall_mem_cons.2 ⟨subd7_0_1091, List.forall_mem_cons.2 ⟨subd7_0_1092, List.forall_mem_cons.2 ⟨subd7_0_1093, List.forall_mem_cons.2 ⟨subd7_0_1094, List.forall_mem_cons.2 ⟨subd7_0_1095, List.forall_mem_cons.2 ⟨subd7_0_1096, List.forall_mem_cons.2 ⟨subd7_0_1097, List.forall_mem_cons.2 ⟨subd7_0_1098, List.forall_mem_cons.2 ⟨subd7_0_1099, List.forall_mem_cons.2 ⟨subd7_0_1100, List.forall_mem_cons.2 ⟨subd7_0_1101, List.forall_mem_cons.2 ⟨subd7_0_1102, List.forall_mem_cons.2 ⟨subd7_0_1103, List.forall_mem_cons.2 ⟨subd7_0_1104, List.forall_mem_cons.2 ⟨subd7_0_1105, List.forall_mem_cons.2 ⟨subd7_0_1106, List.forall_mem_cons.2 ⟨subd7_0_1107, List.forall_mem_cons.2 ⟨subd7_0_1108, List.forall_mem_cons.2 ⟨subd7_0_1109, List.forall_mem_cons.2 ⟨subd7_0_1110, List.forall_mem_cons.2 ⟨subd7_0_1111, List.forall_mem_cons.2 ⟨subd7_0_1112, List.forall_mem_cons.2 ⟨subd7_0_1113, List.forall_mem_cons.2 ⟨subd7_0_1114, List.forall_mem_cons.2 ⟨subd7_0_1115, List.forall_mem_cons.2 ⟨subd7_0_1116, List.forall_mem_cons.2 ⟨subd7_0_1117, List.forall_mem_cons.2 ⟨subd7_0_1118, List.forall_mem_cons.2 ⟨subd7_0_1119, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_1120 : subd7_0 [2, 2, -8] = true := by decide +kernel
theorem subd7_0_1121 : subd7_0 [2, 2, -7] = true := by decide +kernel
theorem subd7_0_1122 : subd7_0 [2, 2, -6] = true := by decide +kernel
theorem subd7_0_1123 : subd7_0 [2, 2, -5] = true := by decide +kernel
theorem subd7_0_1124 : subd7_0 [2, 2, -4] = true := by decide +kernel
theorem subd7_0_1125 : subd7_0 [2, 2, -3] = true := by decide +kernel
theorem subd7_0_1126 : subd7_0 [2, 2, -2] = true := by decide +kernel
theorem subd7_0_1127 : subd7_0 [2, 2, -1] = true := by decide +kernel
theorem subd7_0_1128 : subd7_0 [2, 2, 0] = true := by decide +kernel
theorem subd7_0_1129 : subd7_0 [2, 2, 1] = true := by decide +kernel
theorem subd7_0_1130 : subd7_0 [2, 2, 2] = true := by decide +kernel
theorem subd7_0_1131 : subd7_0 [2, 2, 3] = true := by decide +kernel
theorem subd7_0_1132 : subd7_0 [2, 2, 4] = true := by decide +kernel
theorem subd7_0_1133 : subd7_0 [2, 2, 5] = true := by decide +kernel
theorem subd7_0_1134 : subd7_0 [2, 2, 6] = true := by decide +kernel
theorem subd7_0_1135 : subd7_0 [2, 2, 7] = true := by decide +kernel
theorem subd7_0_1136 : subd7_0 [2, 3, -9] = true := by decide +kernel
theorem subd7_0_1137 : subd7_0 [2, 3, -8] = true := by decide +kernel
theorem subd7_0_1138 : subd7_0 [2, 3, -7] = true := by decide +kernel
theorem subd7_0_1139 : subd7_0 [2, 3, -6] = true := by decide +kernel
theorem subd7_0_1140 : subd7_0 [2, 3, -5] = true := by decide +kernel
theorem subd7_0_1141 : subd7_0 [2, 3, -4] = true := by decide +kernel
theorem subd7_0_1142 : subd7_0 [2, 3, -3] = true := by decide +kernel
theorem subd7_0_1143 : subd7_0 [2, 3, -2] = true := by decide +kernel
theorem subd7_0_1144 : subd7_0 [2, 3, -1] = true := by decide +kernel
theorem subd7_0_1145 : subd7_0 [2, 3, 0] = true := by decide +kernel
theorem subd7_0_1146 : subd7_0 [2, 3, 1] = true := by decide +kernel
theorem subd7_0_1147 : subd7_0 [2, 3, 2] = true := by decide +kernel
theorem subd7_0_1148 : subd7_0 [2, 3, 3] = true := by decide +kernel
theorem subd7_0_1149 : subd7_0 [2, 3, 4] = true := by decide +kernel
theorem subd7_0_1150 : subd7_0 [2, 3, 5] = true := by decide +kernel
theorem subd7_0_1151 : subd7_0 [2, 3, 6] = true := by decide +kernel
theorem sbd7_0_35 : ∀ q ∈ blkd7_0_35, subd7_0 q = true := by
  unfold blkd7_0_35
  exact List.forall_mem_cons.2 ⟨subd7_0_1120, List.forall_mem_cons.2 ⟨subd7_0_1121, List.forall_mem_cons.2 ⟨subd7_0_1122, List.forall_mem_cons.2 ⟨subd7_0_1123, List.forall_mem_cons.2 ⟨subd7_0_1124, List.forall_mem_cons.2 ⟨subd7_0_1125, List.forall_mem_cons.2 ⟨subd7_0_1126, List.forall_mem_cons.2 ⟨subd7_0_1127, List.forall_mem_cons.2 ⟨subd7_0_1128, List.forall_mem_cons.2 ⟨subd7_0_1129, List.forall_mem_cons.2 ⟨subd7_0_1130, List.forall_mem_cons.2 ⟨subd7_0_1131, List.forall_mem_cons.2 ⟨subd7_0_1132, List.forall_mem_cons.2 ⟨subd7_0_1133, List.forall_mem_cons.2 ⟨subd7_0_1134, List.forall_mem_cons.2 ⟨subd7_0_1135, List.forall_mem_cons.2 ⟨subd7_0_1136, List.forall_mem_cons.2 ⟨subd7_0_1137, List.forall_mem_cons.2 ⟨subd7_0_1138, List.forall_mem_cons.2 ⟨subd7_0_1139, List.forall_mem_cons.2 ⟨subd7_0_1140, List.forall_mem_cons.2 ⟨subd7_0_1141, List.forall_mem_cons.2 ⟨subd7_0_1142, List.forall_mem_cons.2 ⟨subd7_0_1143, List.forall_mem_cons.2 ⟨subd7_0_1144, List.forall_mem_cons.2 ⟨subd7_0_1145, List.forall_mem_cons.2 ⟨subd7_0_1146, List.forall_mem_cons.2 ⟨subd7_0_1147, List.forall_mem_cons.2 ⟨subd7_0_1148, List.forall_mem_cons.2 ⟨subd7_0_1149, List.forall_mem_cons.2 ⟨subd7_0_1150, List.forall_mem_cons.2 ⟨subd7_0_1151, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_1152 : subd7_0 [2, 4, -9] = true := by decide +kernel
theorem subd7_0_1153 : subd7_0 [2, 4, -8] = true := by decide +kernel
theorem subd7_0_1154 : subd7_0 [2, 4, -7] = true := by decide +kernel
theorem subd7_0_1155 : subd7_0 [2, 4, -6] = true := by decide +kernel
theorem subd7_0_1156 : subd7_0 [2, 4, -5] = true := by decide +kernel
theorem subd7_0_1157 : subd7_0 [2, 4, -4] = true := by decide +kernel
theorem subd7_0_1158 : subd7_0 [2, 4, -3] = true := by decide +kernel
theorem subd7_0_1159 : subd7_0 [2, 4, -2] = true := by decide +kernel
theorem subd7_0_1160 : subd7_0 [2, 4, -1] = true := by decide +kernel
theorem subd7_0_1161 : subd7_0 [2, 4, 0] = true := by decide +kernel
theorem subd7_0_1162 : subd7_0 [2, 4, 1] = true := by decide +kernel
theorem subd7_0_1163 : subd7_0 [2, 4, 2] = true := by decide +kernel
theorem subd7_0_1164 : subd7_0 [2, 4, 3] = true := by decide +kernel
theorem subd7_0_1165 : subd7_0 [2, 4, 4] = true := by decide +kernel
theorem subd7_0_1166 : subd7_0 [2, 4, 5] = true := by decide +kernel
theorem subd7_0_1167 : subd7_0 [2, 5] = true := by decide +kernel
theorem subd7_0_1168 : subd7_0 [2, 6] = true := by decide +kernel
theorem subd7_0_1169 : subd7_0 [2, 7] = true := by decide +kernel
theorem subd7_0_1170 : subd7_0 [3, -8] = true := by decide +kernel
theorem subd7_0_1171 : subd7_0 [3, -7] = true := by decide +kernel
theorem subd7_0_1172 : subd7_0 [3, -6] = true := by decide +kernel
theorem subd7_0_1173 : subd7_0 [3, -5] = true := by decide +kernel
theorem subd7_0_1174 : subd7_0 [3, -4, -6] = true := by decide +kernel
theorem subd7_0_1175 : subd7_0 [3, -4, -5] = true := by decide +kernel
theorem subd7_0_1176 : subd7_0 [3, -4, -4] = true := by decide +kernel
theorem subd7_0_1177 : subd7_0 [3, -4, -3] = true := by decide +kernel
theorem subd7_0_1178 : subd7_0 [3, -4, -2] = true := by decide +kernel
theorem subd7_0_1179 : subd7_0 [3, -4, -1] = true := by decide +kernel
theorem subd7_0_1180 : subd7_0 [3, -4, 0] = true := by decide +kernel
theorem subd7_0_1181 : subd7_0 [3, -4, 1] = true := by decide +kernel
theorem subd7_0_1182 : subd7_0 [3, -4, 2] = true := by decide +kernel
theorem subd7_0_1183 : subd7_0 [3, -4, 3] = true := by decide +kernel
theorem sbd7_0_36 : ∀ q ∈ blkd7_0_36, subd7_0 q = true := by
  unfold blkd7_0_36
  exact List.forall_mem_cons.2 ⟨subd7_0_1152, List.forall_mem_cons.2 ⟨subd7_0_1153, List.forall_mem_cons.2 ⟨subd7_0_1154, List.forall_mem_cons.2 ⟨subd7_0_1155, List.forall_mem_cons.2 ⟨subd7_0_1156, List.forall_mem_cons.2 ⟨subd7_0_1157, List.forall_mem_cons.2 ⟨subd7_0_1158, List.forall_mem_cons.2 ⟨subd7_0_1159, List.forall_mem_cons.2 ⟨subd7_0_1160, List.forall_mem_cons.2 ⟨subd7_0_1161, List.forall_mem_cons.2 ⟨subd7_0_1162, List.forall_mem_cons.2 ⟨subd7_0_1163, List.forall_mem_cons.2 ⟨subd7_0_1164, List.forall_mem_cons.2 ⟨subd7_0_1165, List.forall_mem_cons.2 ⟨subd7_0_1166, List.forall_mem_cons.2 ⟨subd7_0_1167, List.forall_mem_cons.2 ⟨subd7_0_1168, List.forall_mem_cons.2 ⟨subd7_0_1169, List.forall_mem_cons.2 ⟨subd7_0_1170, List.forall_mem_cons.2 ⟨subd7_0_1171, List.forall_mem_cons.2 ⟨subd7_0_1172, List.forall_mem_cons.2 ⟨subd7_0_1173, List.forall_mem_cons.2 ⟨subd7_0_1174, List.forall_mem_cons.2 ⟨subd7_0_1175, List.forall_mem_cons.2 ⟨subd7_0_1176, List.forall_mem_cons.2 ⟨subd7_0_1177, List.forall_mem_cons.2 ⟨subd7_0_1178, List.forall_mem_cons.2 ⟨subd7_0_1179, List.forall_mem_cons.2 ⟨subd7_0_1180, List.forall_mem_cons.2 ⟨subd7_0_1181, List.forall_mem_cons.2 ⟨subd7_0_1182, List.forall_mem_cons.2 ⟨subd7_0_1183, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_1184 : subd7_0 [3, -4, 4] = true := by decide +kernel
theorem subd7_0_1185 : subd7_0 [3, -4, 5] = true := by decide +kernel
theorem subd7_0_1186 : subd7_0 [3, -4, 6] = true := by decide +kernel
theorem subd7_0_1187 : subd7_0 [3, -4, 7] = true := by decide +kernel
theorem subd7_0_1188 : subd7_0 [3, -4, 8] = true := by decide +kernel
theorem subd7_0_1189 : subd7_0 [3, -3, -7] = true := by decide +kernel
theorem subd7_0_1190 : subd7_0 [3, -3, -6] = true := by decide +kernel
theorem subd7_0_1191 : subd7_0 [3, -3, -5] = true := by decide +kernel
theorem subd7_0_1192 : subd7_0 [3, -3, -4] = true := by decide +kernel
theorem subd7_0_1193 : subd7_0 [3, -3, -3] = true := by decide +kernel
theorem subd7_0_1194 : subd7_0 [3, -3, -2] = true := by decide +kernel
theorem subd7_0_1195 : subd7_0 [3, -3, -1] = true := by decide +kernel
theorem subd7_0_1196 : subd7_0 [3, -3, 0] = true := by decide +kernel
theorem subd7_0_1197 : subd7_0 [3, -3, 1] = true := by decide +kernel
theorem subd7_0_1198 : subd7_0 [3, -3, 2] = true := by decide +kernel
theorem subd7_0_1199 : subd7_0 [3, -3, 3] = true := by decide +kernel
theorem subd7_0_1200 : subd7_0 [3, -3, 4] = true := by decide +kernel
theorem subd7_0_1201 : subd7_0 [3, -3, 5] = true := by decide +kernel
theorem subd7_0_1202 : subd7_0 [3, -3, 6] = true := by decide +kernel
theorem subd7_0_1203 : subd7_0 [3, -3, 7] = true := by decide +kernel
theorem subd7_0_1204 : subd7_0 [3, -3, 8] = true := by decide +kernel
theorem subd7_0_1205 : subd7_0 [3, -2, -7] = true := by decide +kernel
theorem subd7_0_1206 : subd7_0 [3, -2, -6] = true := by decide +kernel
theorem subd7_0_1207 : subd7_0 [3, -2, -5] = true := by decide +kernel
theorem subd7_0_1208 : subd7_0 [3, -2, -4] = true := by decide +kernel
theorem subd7_0_1209 : subd7_0 [3, -2, -3] = true := by decide +kernel
theorem subd7_0_1210 : subd7_0 [3, -2, -2] = true := by decide +kernel
theorem subd7_0_1211 : subd7_0 [3, -2, -1] = true := by decide +kernel
theorem subd7_0_1212 : subd7_0 [3, -2, 0] = true := by decide +kernel
theorem subd7_0_1213 : subd7_0 [3, -2, 1] = true := by decide +kernel
theorem subd7_0_1214 : subd7_0 [3, -2, 2] = true := by decide +kernel
theorem subd7_0_1215 : subd7_0 [3, -2, 3] = true := by decide +kernel
theorem sbd7_0_37 : ∀ q ∈ blkd7_0_37, subd7_0 q = true := by
  unfold blkd7_0_37
  exact List.forall_mem_cons.2 ⟨subd7_0_1184, List.forall_mem_cons.2 ⟨subd7_0_1185, List.forall_mem_cons.2 ⟨subd7_0_1186, List.forall_mem_cons.2 ⟨subd7_0_1187, List.forall_mem_cons.2 ⟨subd7_0_1188, List.forall_mem_cons.2 ⟨subd7_0_1189, List.forall_mem_cons.2 ⟨subd7_0_1190, List.forall_mem_cons.2 ⟨subd7_0_1191, List.forall_mem_cons.2 ⟨subd7_0_1192, List.forall_mem_cons.2 ⟨subd7_0_1193, List.forall_mem_cons.2 ⟨subd7_0_1194, List.forall_mem_cons.2 ⟨subd7_0_1195, List.forall_mem_cons.2 ⟨subd7_0_1196, List.forall_mem_cons.2 ⟨subd7_0_1197, List.forall_mem_cons.2 ⟨subd7_0_1198, List.forall_mem_cons.2 ⟨subd7_0_1199, List.forall_mem_cons.2 ⟨subd7_0_1200, List.forall_mem_cons.2 ⟨subd7_0_1201, List.forall_mem_cons.2 ⟨subd7_0_1202, List.forall_mem_cons.2 ⟨subd7_0_1203, List.forall_mem_cons.2 ⟨subd7_0_1204, List.forall_mem_cons.2 ⟨subd7_0_1205, List.forall_mem_cons.2 ⟨subd7_0_1206, List.forall_mem_cons.2 ⟨subd7_0_1207, List.forall_mem_cons.2 ⟨subd7_0_1208, List.forall_mem_cons.2 ⟨subd7_0_1209, List.forall_mem_cons.2 ⟨subd7_0_1210, List.forall_mem_cons.2 ⟨subd7_0_1211, List.forall_mem_cons.2 ⟨subd7_0_1212, List.forall_mem_cons.2 ⟨subd7_0_1213, List.forall_mem_cons.2 ⟨subd7_0_1214, List.forall_mem_cons.2 ⟨subd7_0_1215, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_1216 : subd7_0 [3, -2, 4] = true := by decide +kernel
theorem subd7_0_1217 : subd7_0 [3, -2, 5] = true := by decide +kernel
theorem subd7_0_1218 : subd7_0 [3, -2, 6] = true := by decide +kernel
theorem subd7_0_1219 : subd7_0 [3, -2, 7] = true := by decide +kernel
theorem subd7_0_1220 : subd7_0 [3, -2, 8] = true := by decide +kernel
theorem subd7_0_1221 : subd7_0 [3, -1, -8] = true := by decide +kernel
theorem subd7_0_1222 : subd7_0 [3, -1, -7] = true := by decide +kernel
theorem subd7_0_1223 : subd7_0 [3, -1, -6] = true := by decide +kernel
theorem subd7_0_1224 : subd7_0 [3, -1, -5] = true := by decide +kernel
theorem subd7_0_1225 : subd7_0 [3, -1, -4] = true := by decide +kernel
theorem subd7_0_1226 : subd7_0 [3, -1, -3] = true := by decide +kernel
theorem subd7_0_1227 : subd7_0 [3, -1, -2] = true := by decide +kernel
theorem subd7_0_1228 : subd7_0 [3, -1, -1] = true := by decide +kernel
theorem subd7_0_1229 : subd7_0 [3, -1, 0] = true := by decide +kernel
theorem subd7_0_1230 : subd7_0 [3, -1, 1] = true := by decide +kernel
theorem subd7_0_1231 : subd7_0 [3, -1, 2] = true := by decide +kernel
theorem subd7_0_1232 : subd7_0 [3, -1, 3] = true := by decide +kernel
theorem subd7_0_1233 : subd7_0 [3, -1, 4] = true := by decide +kernel
theorem subd7_0_1234 : subd7_0 [3, -1, 5] = true := by decide +kernel
theorem subd7_0_1235 : subd7_0 [3, -1, 6] = true := by decide +kernel
theorem subd7_0_1236 : subd7_0 [3, -1, 7] = true := by decide +kernel
theorem subd7_0_1237 : subd7_0 [3, -1, 8] = true := by decide +kernel
theorem subd7_0_1238 : subd7_0 [3, 0, -8] = true := by decide +kernel
theorem subd7_0_1239 : subd7_0 [3, 0, -7] = true := by decide +kernel
theorem subd7_0_1240 : subd7_0 [3, 0, -6] = true := by decide +kernel
theorem subd7_0_1241 : subd7_0 [3, 0, -5] = true := by decide +kernel
theorem subd7_0_1242 : subd7_0 [3, 0, -4] = true := by decide +kernel
theorem subd7_0_1243 : subd7_0 [3, 0, -3] = true := by decide +kernel
theorem subd7_0_1244 : subd7_0 [3, 0, -2] = true := by decide +kernel
theorem subd7_0_1245 : subd7_0 [3, 0, -1] = true := by decide +kernel
theorem subd7_0_1246 : subd7_0 [3, 0, 0] = true := by decide +kernel
theorem subd7_0_1247 : subd7_0 [3, 0, 1] = true := by decide +kernel
theorem sbd7_0_38 : ∀ q ∈ blkd7_0_38, subd7_0 q = true := by
  unfold blkd7_0_38
  exact List.forall_mem_cons.2 ⟨subd7_0_1216, List.forall_mem_cons.2 ⟨subd7_0_1217, List.forall_mem_cons.2 ⟨subd7_0_1218, List.forall_mem_cons.2 ⟨subd7_0_1219, List.forall_mem_cons.2 ⟨subd7_0_1220, List.forall_mem_cons.2 ⟨subd7_0_1221, List.forall_mem_cons.2 ⟨subd7_0_1222, List.forall_mem_cons.2 ⟨subd7_0_1223, List.forall_mem_cons.2 ⟨subd7_0_1224, List.forall_mem_cons.2 ⟨subd7_0_1225, List.forall_mem_cons.2 ⟨subd7_0_1226, List.forall_mem_cons.2 ⟨subd7_0_1227, List.forall_mem_cons.2 ⟨subd7_0_1228, List.forall_mem_cons.2 ⟨subd7_0_1229, List.forall_mem_cons.2 ⟨subd7_0_1230, List.forall_mem_cons.2 ⟨subd7_0_1231, List.forall_mem_cons.2 ⟨subd7_0_1232, List.forall_mem_cons.2 ⟨subd7_0_1233, List.forall_mem_cons.2 ⟨subd7_0_1234, List.forall_mem_cons.2 ⟨subd7_0_1235, List.forall_mem_cons.2 ⟨subd7_0_1236, List.forall_mem_cons.2 ⟨subd7_0_1237, List.forall_mem_cons.2 ⟨subd7_0_1238, List.forall_mem_cons.2 ⟨subd7_0_1239, List.forall_mem_cons.2 ⟨subd7_0_1240, List.forall_mem_cons.2 ⟨subd7_0_1241, List.forall_mem_cons.2 ⟨subd7_0_1242, List.forall_mem_cons.2 ⟨subd7_0_1243, List.forall_mem_cons.2 ⟨subd7_0_1244, List.forall_mem_cons.2 ⟨subd7_0_1245, List.forall_mem_cons.2 ⟨subd7_0_1246, List.forall_mem_cons.2 ⟨subd7_0_1247, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_1248 : subd7_0 [3, 0, 2] = true := by decide +kernel
theorem subd7_0_1249 : subd7_0 [3, 0, 3] = true := by decide +kernel
theorem subd7_0_1250 : subd7_0 [3, 0, 4] = true := by decide +kernel
theorem subd7_0_1251 : subd7_0 [3, 0, 5] = true := by decide +kernel
theorem subd7_0_1252 : subd7_0 [3, 0, 6] = true := by decide +kernel
theorem subd7_0_1253 : subd7_0 [3, 0, 7] = true := by decide +kernel
theorem subd7_0_1254 : subd7_0 [3, 1, -9] = true := by decide +kernel
theorem subd7_0_1255 : subd7_0 [3, 1, -8] = true := by decide +kernel
theorem subd7_0_1256 : subd7_0 [3, 1, -7] = true := by decide +kernel
theorem subd7_0_1257 : subd7_0 [3, 1, -6] = true := by decide +kernel
theorem subd7_0_1258 : subd7_0 [3, 1, -5] = true := by decide +kernel
theorem subd7_0_1259 : subd7_0 [3, 1, -4] = true := by decide +kernel
theorem subd7_0_1260 : subd7_0 [3, 1, -3] = true := by decide +kernel
theorem subd7_0_1261 : subd7_0 [3, 1, -2] = true := by decide +kernel
theorem subd7_0_1262 : subd7_0 [3, 1, -1] = true := by decide +kernel
theorem subd7_0_1263 : subd7_0 [3, 1, 0] = true := by decide +kernel
theorem subd7_0_1264 : subd7_0 [3, 1, 1] = true := by decide +kernel
theorem subd7_0_1265 : subd7_0 [3, 1, 2] = true := by decide +kernel
theorem subd7_0_1266 : subd7_0 [3, 1, 3] = true := by decide +kernel
theorem subd7_0_1267 : subd7_0 [3, 1, 4] = true := by decide +kernel
theorem subd7_0_1268 : subd7_0 [3, 1, 5] = true := by decide +kernel
theorem subd7_0_1269 : subd7_0 [3, 1, 6] = true := by decide +kernel
theorem subd7_0_1270 : subd7_0 [3, 1, 7] = true := by decide +kernel
theorem subd7_0_1271 : subd7_0 [3, 2, -9] = true := by decide +kernel
theorem subd7_0_1272 : subd7_0 [3, 2, -8] = true := by decide +kernel
theorem subd7_0_1273 : subd7_0 [3, 2, -7] = true := by decide +kernel
theorem subd7_0_1274 : subd7_0 [3, 2, -6] = true := by decide +kernel
theorem subd7_0_1275 : subd7_0 [3, 2, -5] = true := by decide +kernel
theorem subd7_0_1276 : subd7_0 [3, 2, -4] = true := by decide +kernel
theorem subd7_0_1277 : subd7_0 [3, 2, -3] = true := by decide +kernel
theorem subd7_0_1278 : subd7_0 [3, 2, -2] = true := by decide +kernel
theorem subd7_0_1279 : subd7_0 [3, 2, -1] = true := by decide +kernel
theorem sbd7_0_39 : ∀ q ∈ blkd7_0_39, subd7_0 q = true := by
  unfold blkd7_0_39
  exact List.forall_mem_cons.2 ⟨subd7_0_1248, List.forall_mem_cons.2 ⟨subd7_0_1249, List.forall_mem_cons.2 ⟨subd7_0_1250, List.forall_mem_cons.2 ⟨subd7_0_1251, List.forall_mem_cons.2 ⟨subd7_0_1252, List.forall_mem_cons.2 ⟨subd7_0_1253, List.forall_mem_cons.2 ⟨subd7_0_1254, List.forall_mem_cons.2 ⟨subd7_0_1255, List.forall_mem_cons.2 ⟨subd7_0_1256, List.forall_mem_cons.2 ⟨subd7_0_1257, List.forall_mem_cons.2 ⟨subd7_0_1258, List.forall_mem_cons.2 ⟨subd7_0_1259, List.forall_mem_cons.2 ⟨subd7_0_1260, List.forall_mem_cons.2 ⟨subd7_0_1261, List.forall_mem_cons.2 ⟨subd7_0_1262, List.forall_mem_cons.2 ⟨subd7_0_1263, List.forall_mem_cons.2 ⟨subd7_0_1264, List.forall_mem_cons.2 ⟨subd7_0_1265, List.forall_mem_cons.2 ⟨subd7_0_1266, List.forall_mem_cons.2 ⟨subd7_0_1267, List.forall_mem_cons.2 ⟨subd7_0_1268, List.forall_mem_cons.2 ⟨subd7_0_1269, List.forall_mem_cons.2 ⟨subd7_0_1270, List.forall_mem_cons.2 ⟨subd7_0_1271, List.forall_mem_cons.2 ⟨subd7_0_1272, List.forall_mem_cons.2 ⟨subd7_0_1273, List.forall_mem_cons.2 ⟨subd7_0_1274, List.forall_mem_cons.2 ⟨subd7_0_1275, List.forall_mem_cons.2 ⟨subd7_0_1276, List.forall_mem_cons.2 ⟨subd7_0_1277, List.forall_mem_cons.2 ⟨subd7_0_1278, List.forall_mem_cons.2 ⟨subd7_0_1279, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C093
