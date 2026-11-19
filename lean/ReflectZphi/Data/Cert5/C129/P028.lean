import ReflectZphi.Data.Cert5.C129.Base

namespace ReflectZphi.Data.Cert5.C129

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_3_832 : subd8_3 [2, 2, 0] = true := by decide +kernel
theorem subd8_3_833 : subd8_3 [2, 2, 1] = true := by decide +kernel
theorem subd8_3_834 : subd8_3 [2, 2, 2] = true := by decide +kernel
theorem subd8_3_835 : subd8_3 [2, 2, 3] = true := by decide +kernel
theorem subd8_3_836 : subd8_3 [2, 2, 4] = true := by decide +kernel
theorem subd8_3_837 : subd8_3 [2, 2, 5] = true := by decide +kernel
theorem subd8_3_838 : subd8_3 [2, 2, 6] = true := by decide +kernel
theorem subd8_3_839 : subd8_3 [2, 2, 7] = true := by decide +kernel
theorem subd8_3_840 : subd8_3 [2, 2, 8] = true := by decide +kernel
theorem subd8_3_841 : subd8_3 [2, 2, 9] = true := by decide +kernel
theorem subd8_3_842 : subd8_3 [2, 3, -8] = true := by decide +kernel
theorem subd8_3_843 : subd8_3 [2, 3, -7] = true := by decide +kernel
theorem subd8_3_844 : subd8_3 [2, 3, -6] = true := by decide +kernel
theorem subd8_3_845 : subd8_3 [2, 3, -5] = true := by decide +kernel
theorem subd8_3_846 : subd8_3 [2, 3, -4] = true := by decide +kernel
theorem subd8_3_847 : subd8_3 [2, 3, -3] = true := by decide +kernel
theorem subd8_3_848 : subd8_3 [2, 3, -2] = true := by decide +kernel
theorem subd8_3_849 : subd8_3 [2, 3, -1] = true := by decide +kernel
theorem subd8_3_850 : subd8_3 [2, 3, 0] = true := by decide +kernel
theorem subd8_3_851 : subd8_3 [2, 3, 1] = true := by decide +kernel
theorem subd8_3_852 : subd8_3 [2, 3, 2] = true := by decide +kernel
theorem subd8_3_853 : subd8_3 [2, 3, 3] = true := by decide +kernel
theorem subd8_3_854 : subd8_3 [2, 3, 4] = true := by decide +kernel
theorem subd8_3_855 : subd8_3 [2, 3, 5] = true := by decide +kernel
theorem subd8_3_856 : subd8_3 [2, 3, 6] = true := by decide +kernel
theorem subd8_3_857 : subd8_3 [3, -3] = true := by decide +kernel
theorem subd8_3_858 : subd8_3 [3, -2] = true := by decide +kernel
theorem subd8_3_859 : subd8_3 [3, -1, -7] = true := by decide +kernel
theorem subd8_3_860 : subd8_3 [3, -1, -6] = true := by decide +kernel
theorem subd8_3_861 : subd8_3 [3, -1, -5] = true := by decide +kernel
theorem subd8_3_862 : subd8_3 [3, -1, -4] = true := by decide +kernel
theorem subd8_3_863 : subd8_3 [3, -1, -3] = true := by decide +kernel
theorem sbd8_3_26 : ∀ q ∈ blkd8_3_26, subd8_3 q = true := by
  unfold blkd8_3_26
  exact List.forall_mem_cons.2 ⟨subd8_3_832, List.forall_mem_cons.2 ⟨subd8_3_833, List.forall_mem_cons.2 ⟨subd8_3_834, List.forall_mem_cons.2 ⟨subd8_3_835, List.forall_mem_cons.2 ⟨subd8_3_836, List.forall_mem_cons.2 ⟨subd8_3_837, List.forall_mem_cons.2 ⟨subd8_3_838, List.forall_mem_cons.2 ⟨subd8_3_839, List.forall_mem_cons.2 ⟨subd8_3_840, List.forall_mem_cons.2 ⟨subd8_3_841, List.forall_mem_cons.2 ⟨subd8_3_842, List.forall_mem_cons.2 ⟨subd8_3_843, List.forall_mem_cons.2 ⟨subd8_3_844, List.forall_mem_cons.2 ⟨subd8_3_845, List.forall_mem_cons.2 ⟨subd8_3_846, List.forall_mem_cons.2 ⟨subd8_3_847, List.forall_mem_cons.2 ⟨subd8_3_848, List.forall_mem_cons.2 ⟨subd8_3_849, List.forall_mem_cons.2 ⟨subd8_3_850, List.forall_mem_cons.2 ⟨subd8_3_851, List.forall_mem_cons.2 ⟨subd8_3_852, List.forall_mem_cons.2 ⟨subd8_3_853, List.forall_mem_cons.2 ⟨subd8_3_854, List.forall_mem_cons.2 ⟨subd8_3_855, List.forall_mem_cons.2 ⟨subd8_3_856, List.forall_mem_cons.2 ⟨subd8_3_857, List.forall_mem_cons.2 ⟨subd8_3_858, List.forall_mem_cons.2 ⟨subd8_3_859, List.forall_mem_cons.2 ⟨subd8_3_860, List.forall_mem_cons.2 ⟨subd8_3_861, List.forall_mem_cons.2 ⟨subd8_3_862, List.forall_mem_cons.2 ⟨subd8_3_863, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_864 : subd8_3 [3, -1, -2] = true := by decide +kernel
theorem subd8_3_865 : subd8_3 [3, -1, -1] = true := by decide +kernel
theorem subd8_3_866 : subd8_3 [3, -1, 0] = true := by decide +kernel
theorem subd8_3_867 : subd8_3 [3, -1, 1] = true := by decide +kernel
theorem subd8_3_868 : subd8_3 [3, -1, 2] = true := by decide +kernel
theorem subd8_3_869 : subd8_3 [3, -1, 3] = true := by decide +kernel
theorem subd8_3_870 : subd8_3 [3, -1, 4] = true := by decide +kernel
theorem subd8_3_871 : subd8_3 [3, -1, 5] = true := by decide +kernel
theorem subd8_3_872 : subd8_3 [3, -1, 6] = true := by decide +kernel
theorem subd8_3_873 : subd8_3 [3, -1, 7] = true := by decide +kernel
theorem subd8_3_874 : subd8_3 [3, -1, 8] = true := by decide +kernel
theorem subd8_3_875 : subd8_3 [3, -1, 9] = true := by decide +kernel
theorem subd8_3_876 : subd8_3 [3, -1, 10] = true := by decide +kernel
theorem subd8_3_877 : subd8_3 [3, 0, -9] = true := by decide +kernel
theorem subd8_3_878 : subd8_3 [3, 0, -8] = true := by decide +kernel
theorem subd8_3_879 : subd8_3 [3, 0, -7] = true := by decide +kernel
theorem subd8_3_880 : subd8_3 [3, 0, -6] = true := by decide +kernel
theorem subd8_3_881 : subd8_3 [3, 0, -5] = true := by decide +kernel
theorem subd8_3_882 : subd8_3 [3, 0, -4] = true := by decide +kernel
theorem subd8_3_883 : subd8_3 [3, 0, -3] = true := by decide +kernel
theorem subd8_3_884 : subd8_3 [3, 0, -2] = true := by decide +kernel
theorem subd8_3_885 : subd8_3 [3, 0, -1] = true := by decide +kernel
theorem subd8_3_886 : subd8_3 [3, 0, 0] = true := by decide +kernel
theorem subd8_3_887 : subd8_3 [3, 0, 1] = true := by decide +kernel
theorem subd8_3_888 : subd8_3 [3, 0, 2] = true := by decide +kernel
theorem subd8_3_889 : subd8_3 [3, 0, 3] = true := by decide +kernel
theorem subd8_3_890 : subd8_3 [3, 0, 4] = true := by decide +kernel
theorem subd8_3_891 : subd8_3 [3, 0, 5] = true := by decide +kernel
theorem subd8_3_892 : subd8_3 [3, 0, 6] = true := by decide +kernel
theorem subd8_3_893 : subd8_3 [3, 0, 7] = true := by decide +kernel
theorem subd8_3_894 : subd8_3 [3, 0, 8] = true := by decide +kernel
theorem subd8_3_895 : subd8_3 [3, 0, 9] = true := by decide +kernel
theorem sbd8_3_27 : ∀ q ∈ blkd8_3_27, subd8_3 q = true := by
  unfold blkd8_3_27
  exact List.forall_mem_cons.2 ⟨subd8_3_864, List.forall_mem_cons.2 ⟨subd8_3_865, List.forall_mem_cons.2 ⟨subd8_3_866, List.forall_mem_cons.2 ⟨subd8_3_867, List.forall_mem_cons.2 ⟨subd8_3_868, List.forall_mem_cons.2 ⟨subd8_3_869, List.forall_mem_cons.2 ⟨subd8_3_870, List.forall_mem_cons.2 ⟨subd8_3_871, List.forall_mem_cons.2 ⟨subd8_3_872, List.forall_mem_cons.2 ⟨subd8_3_873, List.forall_mem_cons.2 ⟨subd8_3_874, List.forall_mem_cons.2 ⟨subd8_3_875, List.forall_mem_cons.2 ⟨subd8_3_876, List.forall_mem_cons.2 ⟨subd8_3_877, List.forall_mem_cons.2 ⟨subd8_3_878, List.forall_mem_cons.2 ⟨subd8_3_879, List.forall_mem_cons.2 ⟨subd8_3_880, List.forall_mem_cons.2 ⟨subd8_3_881, List.forall_mem_cons.2 ⟨subd8_3_882, List.forall_mem_cons.2 ⟨subd8_3_883, List.forall_mem_cons.2 ⟨subd8_3_884, List.forall_mem_cons.2 ⟨subd8_3_885, List.forall_mem_cons.2 ⟨subd8_3_886, List.forall_mem_cons.2 ⟨subd8_3_887, List.forall_mem_cons.2 ⟨subd8_3_888, List.forall_mem_cons.2 ⟨subd8_3_889, List.forall_mem_cons.2 ⟨subd8_3_890, List.forall_mem_cons.2 ⟨subd8_3_891, List.forall_mem_cons.2 ⟨subd8_3_892, List.forall_mem_cons.2 ⟨subd8_3_893, List.forall_mem_cons.2 ⟨subd8_3_894, List.forall_mem_cons.2 ⟨subd8_3_895, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_896 : subd8_3 [3, 0, 10] = true := by decide +kernel
theorem subd8_3_897 : subd8_3 [3, 1, -8] = true := by decide +kernel
theorem subd8_3_898 : subd8_3 [3, 1, -7] = true := by decide +kernel
theorem subd8_3_899 : subd8_3 [3, 1, -6] = true := by decide +kernel
theorem subd8_3_900 : subd8_3 [3, 1, -5] = true := by decide +kernel
theorem subd8_3_901 : subd8_3 [3, 1, -4] = true := by decide +kernel
theorem subd8_3_902 : subd8_3 [3, 1, -3] = true := by decide +kernel
theorem subd8_3_903 : subd8_3 [3, 1, -2] = true := by decide +kernel
theorem subd8_3_904 : subd8_3 [3, 1, -1] = true := by decide +kernel
theorem subd8_3_905 : subd8_3 [3, 1, 0] = true := by decide +kernel
theorem subd8_3_906 : subd8_3 [3, 1, 1] = true := by decide +kernel
theorem subd8_3_907 : subd8_3 [3, 1, 2] = true := by decide +kernel
theorem subd8_3_908 : subd8_3 [3, 1, 3] = true := by decide +kernel
theorem subd8_3_909 : subd8_3 [3, 1, 4] = true := by decide +kernel
theorem subd8_3_910 : subd8_3 [3, 1, 5] = true := by decide +kernel
theorem subd8_3_911 : subd8_3 [3, 1, 6] = true := by decide +kernel
theorem subd8_3_912 : subd8_3 [3, 1, 7] = true := by decide +kernel
theorem subd8_3_913 : subd8_3 [3, 1, 8] = true := by decide +kernel
theorem subd8_3_914 : subd8_3 [3, 1, 9] = true := by decide +kernel
theorem subd8_3_915 : subd8_3 [3, 2, -7] = true := by decide +kernel
theorem subd8_3_916 : subd8_3 [3, 2, -6] = true := by decide +kernel
theorem subd8_3_917 : subd8_3 [3, 2, -5] = true := by decide +kernel
theorem subd8_3_918 : subd8_3 [3, 2, -4] = true := by decide +kernel
theorem subd8_3_919 : subd8_3 [3, 2, -3] = true := by decide +kernel
theorem subd8_3_920 : subd8_3 [3, 2, -2] = true := by decide +kernel
theorem subd8_3_921 : subd8_3 [3, 2, -1] = true := by decide +kernel
theorem subd8_3_922 : subd8_3 [3, 2, 0] = true := by decide +kernel
theorem subd8_3_923 : subd8_3 [3, 2, 1] = true := by decide +kernel
theorem subd8_3_924 : subd8_3 [3, 2, 2] = true := by decide +kernel
theorem subd8_3_925 : subd8_3 [3, 2, 3] = true := by decide +kernel
theorem subd8_3_926 : subd8_3 [3, 2, 4] = true := by decide +kernel
theorem subd8_3_927 : subd8_3 [3, 2, 5] = true := by decide +kernel
theorem sbd8_3_28 : ∀ q ∈ blkd8_3_28, subd8_3 q = true := by
  unfold blkd8_3_28
  exact List.forall_mem_cons.2 ⟨subd8_3_896, List.forall_mem_cons.2 ⟨subd8_3_897, List.forall_mem_cons.2 ⟨subd8_3_898, List.forall_mem_cons.2 ⟨subd8_3_899, List.forall_mem_cons.2 ⟨subd8_3_900, List.forall_mem_cons.2 ⟨subd8_3_901, List.forall_mem_cons.2 ⟨subd8_3_902, List.forall_mem_cons.2 ⟨subd8_3_903, List.forall_mem_cons.2 ⟨subd8_3_904, List.forall_mem_cons.2 ⟨subd8_3_905, List.forall_mem_cons.2 ⟨subd8_3_906, List.forall_mem_cons.2 ⟨subd8_3_907, List.forall_mem_cons.2 ⟨subd8_3_908, List.forall_mem_cons.2 ⟨subd8_3_909, List.forall_mem_cons.2 ⟨subd8_3_910, List.forall_mem_cons.2 ⟨subd8_3_911, List.forall_mem_cons.2 ⟨subd8_3_912, List.forall_mem_cons.2 ⟨subd8_3_913, List.forall_mem_cons.2 ⟨subd8_3_914, List.forall_mem_cons.2 ⟨subd8_3_915, List.forall_mem_cons.2 ⟨subd8_3_916, List.forall_mem_cons.2 ⟨subd8_3_917, List.forall_mem_cons.2 ⟨subd8_3_918, List.forall_mem_cons.2 ⟨subd8_3_919, List.forall_mem_cons.2 ⟨subd8_3_920, List.forall_mem_cons.2 ⟨subd8_3_921, List.forall_mem_cons.2 ⟨subd8_3_922, List.forall_mem_cons.2 ⟨subd8_3_923, List.forall_mem_cons.2 ⟨subd8_3_924, List.forall_mem_cons.2 ⟨subd8_3_925, List.forall_mem_cons.2 ⟨subd8_3_926, List.forall_mem_cons.2 ⟨subd8_3_927, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_928 : subd8_3 [3, 2, 6] = true := by decide +kernel
theorem sbd8_3_29 : ∀ q ∈ blkd8_3_29, subd8_3 q = true := by
  unfold blkd8_3_29
  exact List.forall_mem_cons.2 ⟨subd8_3_928, List.forall_mem_nil _⟩
theorem ld_okd9_0 : ldCheck G d9_0.U d9_0.ms ldd9_0 = true := by decide +kernel
theorem pre_okd9_0 : subPre G cell9 d9_0 = true := by decide +kernel
theorem subd9_0_0 : subd9_0 [-4, -3] = true := by decide +kernel
theorem subd9_0_1 : subd9_0 [-4, -2] = true := by decide +kernel
theorem subd9_0_2 : subd9_0 [-4, -1] = true := by decide +kernel
theorem subd9_0_3 : subd9_0 [-4, 0] = true := by decide +kernel
theorem subd9_0_4 : subd9_0 [-4, 1] = true := by decide +kernel
theorem subd9_0_5 : subd9_0 [-4, 2] = true := by decide +kernel
theorem subd9_0_6 : subd9_0 [-4, 3] = true := by decide +kernel
theorem subd9_0_7 : subd9_0 [-4, 4] = true := by decide +kernel
theorem subd9_0_8 : subd9_0 [-3, -4] = true := by decide +kernel
theorem subd9_0_9 : subd9_0 [-3, -3] = true := by decide +kernel
theorem subd9_0_10 : subd9_0 [-3, -2] = true := by decide +kernel
theorem subd9_0_11 : subd9_0 [-3, -1] = true := by decide +kernel
theorem subd9_0_12 : subd9_0 [-3, 0] = true := by decide +kernel
theorem subd9_0_13 : subd9_0 [-3, 1] = true := by decide +kernel
theorem subd9_0_14 : subd9_0 [-3, 2] = true := by decide +kernel
theorem subd9_0_15 : subd9_0 [-3, 3] = true := by decide +kernel
theorem subd9_0_16 : subd9_0 [-3, 4] = true := by decide +kernel
theorem subd9_0_17 : subd9_0 [-3, 5] = true := by decide +kernel
theorem subd9_0_18 : subd9_0 [-2, -5] = true := by decide +kernel
theorem subd9_0_19 : subd9_0 [-2, -4] = true := by decide +kernel
theorem subd9_0_20 : subd9_0 [-2, -3] = true := by decide +kernel
theorem subd9_0_21 : subd9_0 [-2, -2] = true := by decide +kernel
theorem subd9_0_22 : subd9_0 [-2, -1] = true := by decide +kernel
theorem subd9_0_23 : subd9_0 [-2, 0, -7] = true := by decide +kernel
theorem subd9_0_24 : subd9_0 [-2, 0, -6] = true := by decide +kernel
theorem subd9_0_25 : subd9_0 [-2, 0, -5] = true := by decide +kernel
theorem subd9_0_26 : subd9_0 [-2, 0, -4] = true := by decide +kernel
theorem subd9_0_27 : subd9_0 [-2, 0, -3] = true := by decide +kernel
theorem subd9_0_28 : subd9_0 [-2, 0, -2] = true := by decide +kernel
theorem subd9_0_29 : subd9_0 [-2, 0, -1] = true := by decide +kernel
theorem subd9_0_30 : subd9_0 [-2, 0, 0] = true := by decide +kernel
theorem subd9_0_31 : subd9_0 [-2, 0, 1] = true := by decide +kernel
theorem sbd9_0_0 : ∀ q ∈ blkd9_0_0, subd9_0 q = true := by
  unfold blkd9_0_0
  exact List.forall_mem_cons.2 ⟨subd9_0_0, List.forall_mem_cons.2 ⟨subd9_0_1, List.forall_mem_cons.2 ⟨subd9_0_2, List.forall_mem_cons.2 ⟨subd9_0_3, List.forall_mem_cons.2 ⟨subd9_0_4, List.forall_mem_cons.2 ⟨subd9_0_5, List.forall_mem_cons.2 ⟨subd9_0_6, List.forall_mem_cons.2 ⟨subd9_0_7, List.forall_mem_cons.2 ⟨subd9_0_8, List.forall_mem_cons.2 ⟨subd9_0_9, List.forall_mem_cons.2 ⟨subd9_0_10, List.forall_mem_cons.2 ⟨subd9_0_11, List.forall_mem_cons.2 ⟨subd9_0_12, List.forall_mem_cons.2 ⟨subd9_0_13, List.forall_mem_cons.2 ⟨subd9_0_14, List.forall_mem_cons.2 ⟨subd9_0_15, List.forall_mem_cons.2 ⟨subd9_0_16, List.forall_mem_cons.2 ⟨subd9_0_17, List.forall_mem_cons.2 ⟨subd9_0_18, List.forall_mem_cons.2 ⟨subd9_0_19, List.forall_mem_cons.2 ⟨subd9_0_20, List.forall_mem_cons.2 ⟨subd9_0_21, List.forall_mem_cons.2 ⟨subd9_0_22, List.forall_mem_cons.2 ⟨subd9_0_23, List.forall_mem_cons.2 ⟨subd9_0_24, List.forall_mem_cons.2 ⟨subd9_0_25, List.forall_mem_cons.2 ⟨subd9_0_26, List.forall_mem_cons.2 ⟨subd9_0_27, List.forall_mem_cons.2 ⟨subd9_0_28, List.forall_mem_cons.2 ⟨subd9_0_29, List.forall_mem_cons.2 ⟨subd9_0_30, List.forall_mem_cons.2 ⟨subd9_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_32 : subd9_0 [-2, 0, 2] = true := by decide +kernel
theorem subd9_0_33 : subd9_0 [-2, 0, 3] = true := by decide +kernel
theorem subd9_0_34 : subd9_0 [-2, 0, 4] = true := by decide +kernel
theorem subd9_0_35 : subd9_0 [-2, 0, 5] = true := by decide +kernel
theorem subd9_0_36 : subd9_0 [-2, 0, 6] = true := by decide +kernel
theorem subd9_0_37 : subd9_0 [-2, 1, -7] = true := by decide +kernel
theorem subd9_0_38 : subd9_0 [-2, 1, -6] = true := by decide +kernel
theorem subd9_0_39 : subd9_0 [-2, 1, -5] = true := by decide +kernel
theorem subd9_0_40 : subd9_0 [-2, 1, -4] = true := by decide +kernel
theorem subd9_0_41 : subd9_0 [-2, 1, -3] = true := by decide +kernel
theorem subd9_0_42 : subd9_0 [-2, 1, -2] = true := by decide +kernel
theorem subd9_0_43 : subd9_0 [-2, 1, -1] = true := by decide +kernel
theorem subd9_0_44 : subd9_0 [-2, 1, 0] = true := by decide +kernel
theorem subd9_0_45 : subd9_0 [-2, 1, 1] = true := by decide +kernel
theorem subd9_0_46 : subd9_0 [-2, 1, 2] = true := by decide +kernel
theorem subd9_0_47 : subd9_0 [-2, 1, 3] = true := by decide +kernel
theorem subd9_0_48 : subd9_0 [-2, 1, 4] = true := by decide +kernel
theorem subd9_0_49 : subd9_0 [-2, 1, 5] = true := by decide +kernel
theorem subd9_0_50 : subd9_0 [-2, 1, 6] = true := by decide +kernel
theorem subd9_0_51 : subd9_0 [-2, 2] = true := by decide +kernel
theorem subd9_0_52 : subd9_0 [-2, 3] = true := by decide +kernel
theorem subd9_0_53 : subd9_0 [-2, 4] = true := by decide +kernel
theorem subd9_0_54 : subd9_0 [-2, 5] = true := by decide +kernel
theorem subd9_0_55 : subd9_0 [-1, -6] = true := by decide +kernel
theorem subd9_0_56 : subd9_0 [-1, -5] = true := by decide +kernel
theorem subd9_0_57 : subd9_0 [-1, -4] = true := by decide +kernel
theorem subd9_0_58 : subd9_0 [-1, -3] = true := by decide +kernel
theorem subd9_0_59 : subd9_0 [-1, -2] = true := by decide +kernel
theorem subd9_0_60 : subd9_0 [-1, -1, -7] = true := by decide +kernel
theorem subd9_0_61 : subd9_0 [-1, -1, -6] = true := by decide +kernel
theorem subd9_0_62 : subd9_0 [-1, -1, -5] = true := by decide +kernel
theorem subd9_0_63 : subd9_0 [-1, -1, -4] = true := by decide +kernel
theorem sbd9_0_1 : ∀ q ∈ blkd9_0_1, subd9_0 q = true := by
  unfold blkd9_0_1
  exact List.forall_mem_cons.2 ⟨subd9_0_32, List.forall_mem_cons.2 ⟨subd9_0_33, List.forall_mem_cons.2 ⟨subd9_0_34, List.forall_mem_cons.2 ⟨subd9_0_35, List.forall_mem_cons.2 ⟨subd9_0_36, List.forall_mem_cons.2 ⟨subd9_0_37, List.forall_mem_cons.2 ⟨subd9_0_38, List.forall_mem_cons.2 ⟨subd9_0_39, List.forall_mem_cons.2 ⟨subd9_0_40, List.forall_mem_cons.2 ⟨subd9_0_41, List.forall_mem_cons.2 ⟨subd9_0_42, List.forall_mem_cons.2 ⟨subd9_0_43, List.forall_mem_cons.2 ⟨subd9_0_44, List.forall_mem_cons.2 ⟨subd9_0_45, List.forall_mem_cons.2 ⟨subd9_0_46, List.forall_mem_cons.2 ⟨subd9_0_47, List.forall_mem_cons.2 ⟨subd9_0_48, List.forall_mem_cons.2 ⟨subd9_0_49, List.forall_mem_cons.2 ⟨subd9_0_50, List.forall_mem_cons.2 ⟨subd9_0_51, List.forall_mem_cons.2 ⟨subd9_0_52, List.forall_mem_cons.2 ⟨subd9_0_53, List.forall_mem_cons.2 ⟨subd9_0_54, List.forall_mem_cons.2 ⟨subd9_0_55, List.forall_mem_cons.2 ⟨subd9_0_56, List.forall_mem_cons.2 ⟨subd9_0_57, List.forall_mem_cons.2 ⟨subd9_0_58, List.forall_mem_cons.2 ⟨subd9_0_59, List.forall_mem_cons.2 ⟨subd9_0_60, List.forall_mem_cons.2 ⟨subd9_0_61, List.forall_mem_cons.2 ⟨subd9_0_62, List.forall_mem_cons.2 ⟨subd9_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_64 : subd9_0 [-1, -1, -3] = true := by decide +kernel
theorem subd9_0_65 : subd9_0 [-1, -1, -2] = true := by decide +kernel
theorem subd9_0_66 : subd9_0 [-1, -1, -1] = true := by decide +kernel
theorem subd9_0_67 : subd9_0 [-1, -1, 0] = true := by decide +kernel
theorem subd9_0_68 : subd9_0 [-1, -1, 1] = true := by decide +kernel
theorem subd9_0_69 : subd9_0 [-1, -1, 2] = true := by decide +kernel
theorem subd9_0_70 : subd9_0 [-1, -1, 3] = true := by decide +kernel
theorem subd9_0_71 : subd9_0 [-1, -1, 4] = true := by decide +kernel
theorem subd9_0_72 : subd9_0 [-1, -1, 5] = true := by decide +kernel
theorem subd9_0_73 : subd9_0 [-1, -1, 6] = true := by decide +kernel
theorem subd9_0_74 : subd9_0 [-1, 0, -7] = true := by decide +kernel
theorem subd9_0_75 : subd9_0 [-1, 0, -6] = true := by decide +kernel
theorem subd9_0_76 : subd9_0 [-1, 0, -5] = true := by decide +kernel
theorem subd9_0_77 : subd9_0 [-1, 0, -4] = true := by decide +kernel
theorem subd9_0_78 : subd9_0 [-1, 0, -3] = true := by decide +kernel
theorem subd9_0_79 : subd9_0 [-1, 0, -2] = true := by decide +kernel
theorem subd9_0_80 : subd9_0 [-1, 0, -1] = true := by decide +kernel
theorem subd9_0_81 : subd9_0 [-1, 0, 0] = true := by decide +kernel
theorem subd9_0_82 : subd9_0 [-1, 0, 1] = true := by decide +kernel
theorem subd9_0_83 : subd9_0 [-1, 0, 2] = true := by decide +kernel
theorem subd9_0_84 : subd9_0 [-1, 0, 3] = true := by decide +kernel
theorem subd9_0_85 : subd9_0 [-1, 0, 4] = true := by decide +kernel
theorem subd9_0_86 : subd9_0 [-1, 0, 5] = true := by decide +kernel
theorem subd9_0_87 : subd9_0 [-1, 0, 6] = true := by decide +kernel
theorem subd9_0_88 : subd9_0 [-1, 1, -7] = true := by decide +kernel
theorem subd9_0_89 : subd9_0 [-1, 1, -6] = true := by decide +kernel
theorem subd9_0_90 : subd9_0 [-1, 1, -5] = true := by decide +kernel
theorem subd9_0_91 : subd9_0 [-1, 1, -4] = true := by decide +kernel
theorem subd9_0_92 : subd9_0 [-1, 1, -3] = true := by decide +kernel
theorem subd9_0_93 : subd9_0 [-1, 1, -2] = true := by decide +kernel
theorem subd9_0_94 : subd9_0 [-1, 1, -1] = true := by decide +kernel
theorem subd9_0_95 : subd9_0 [-1, 1, 0] = true := by decide +kernel
theorem sbd9_0_2 : ∀ q ∈ blkd9_0_2, subd9_0 q = true := by
  unfold blkd9_0_2
  exact List.forall_mem_cons.2 ⟨subd9_0_64, List.forall_mem_cons.2 ⟨subd9_0_65, List.forall_mem_cons.2 ⟨subd9_0_66, List.forall_mem_cons.2 ⟨subd9_0_67, List.forall_mem_cons.2 ⟨subd9_0_68, List.forall_mem_cons.2 ⟨subd9_0_69, List.forall_mem_cons.2 ⟨subd9_0_70, List.forall_mem_cons.2 ⟨subd9_0_71, List.forall_mem_cons.2 ⟨subd9_0_72, List.forall_mem_cons.2 ⟨subd9_0_73, List.forall_mem_cons.2 ⟨subd9_0_74, List.forall_mem_cons.2 ⟨subd9_0_75, List.forall_mem_cons.2 ⟨subd9_0_76, List.forall_mem_cons.2 ⟨subd9_0_77, List.forall_mem_cons.2 ⟨subd9_0_78, List.forall_mem_cons.2 ⟨subd9_0_79, List.forall_mem_cons.2 ⟨subd9_0_80, List.forall_mem_cons.2 ⟨subd9_0_81, List.forall_mem_cons.2 ⟨subd9_0_82, List.forall_mem_cons.2 ⟨subd9_0_83, List.forall_mem_cons.2 ⟨subd9_0_84, List.forall_mem_cons.2 ⟨subd9_0_85, List.forall_mem_cons.2 ⟨subd9_0_86, List.forall_mem_cons.2 ⟨subd9_0_87, List.forall_mem_cons.2 ⟨subd9_0_88, List.forall_mem_cons.2 ⟨subd9_0_89, List.forall_mem_cons.2 ⟨subd9_0_90, List.forall_mem_cons.2 ⟨subd9_0_91, List.forall_mem_cons.2 ⟨subd9_0_92, List.forall_mem_cons.2 ⟨subd9_0_93, List.forall_mem_cons.2 ⟨subd9_0_94, List.forall_mem_cons.2 ⟨subd9_0_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_96 : subd9_0 [-1, 1, 1] = true := by decide +kernel
theorem subd9_0_97 : subd9_0 [-1, 1, 2] = true := by decide +kernel
theorem subd9_0_98 : subd9_0 [-1, 1, 3] = true := by decide +kernel
theorem subd9_0_99 : subd9_0 [-1, 1, 4] = true := by decide +kernel
theorem subd9_0_100 : subd9_0 [-1, 1, 5] = true := by decide +kernel
theorem subd9_0_101 : subd9_0 [-1, 1, 6] = true := by decide +kernel
theorem subd9_0_102 : subd9_0 [-1, 2, -7] = true := by decide +kernel
theorem subd9_0_103 : subd9_0 [-1, 2, -6] = true := by decide +kernel
theorem subd9_0_104 : subd9_0 [-1, 2, -5] = true := by decide +kernel
theorem subd9_0_105 : subd9_0 [-1, 2, -4] = true := by decide +kernel
theorem subd9_0_106 : subd9_0 [-1, 2, -3] = true := by decide +kernel
theorem subd9_0_107 : subd9_0 [-1, 2, -2] = true := by decide +kernel
theorem subd9_0_108 : subd9_0 [-1, 2, -1] = true := by decide +kernel
theorem subd9_0_109 : subd9_0 [-1, 2, 0] = true := by decide +kernel
theorem subd9_0_110 : subd9_0 [-1, 2, 1] = true := by decide +kernel
theorem subd9_0_111 : subd9_0 [-1, 2, 2] = true := by decide +kernel
theorem subd9_0_112 : subd9_0 [-1, 2, 3] = true := by decide +kernel
theorem subd9_0_113 : subd9_0 [-1, 2, 4] = true := by decide +kernel
theorem subd9_0_114 : subd9_0 [-1, 2, 5] = true := by decide +kernel
theorem subd9_0_115 : subd9_0 [-1, 2, 6] = true := by decide +kernel
theorem subd9_0_116 : subd9_0 [-1, 3] = true := by decide +kernel
theorem subd9_0_117 : subd9_0 [-1, 4] = true := by decide +kernel
theorem subd9_0_118 : subd9_0 [-1, 5] = true := by decide +kernel
theorem subd9_0_119 : subd9_0 [0, -6] = true := by decide +kernel
theorem subd9_0_120 : subd9_0 [0, -5] = true := by decide +kernel
theorem subd9_0_121 : subd9_0 [0, -4] = true := by decide +kernel
theorem subd9_0_122 : subd9_0 [0, -3] = true := by decide +kernel
theorem subd9_0_123 : subd9_0 [0, -2, -7] = true := by decide +kernel
theorem subd9_0_124 : subd9_0 [0, -2, -6] = true := by decide +kernel
theorem subd9_0_125 : subd9_0 [0, -2, -5] = true := by decide +kernel
theorem subd9_0_126 : subd9_0 [0, -2, -4] = true := by decide +kernel
theorem subd9_0_127 : subd9_0 [0, -2, -3] = true := by decide +kernel
theorem sbd9_0_3 : ∀ q ∈ blkd9_0_3, subd9_0 q = true := by
  unfold blkd9_0_3
  exact List.forall_mem_cons.2 ⟨subd9_0_96, List.forall_mem_cons.2 ⟨subd9_0_97, List.forall_mem_cons.2 ⟨subd9_0_98, List.forall_mem_cons.2 ⟨subd9_0_99, List.forall_mem_cons.2 ⟨subd9_0_100, List.forall_mem_cons.2 ⟨subd9_0_101, List.forall_mem_cons.2 ⟨subd9_0_102, List.forall_mem_cons.2 ⟨subd9_0_103, List.forall_mem_cons.2 ⟨subd9_0_104, List.forall_mem_cons.2 ⟨subd9_0_105, List.forall_mem_cons.2 ⟨subd9_0_106, List.forall_mem_cons.2 ⟨subd9_0_107, List.forall_mem_cons.2 ⟨subd9_0_108, List.forall_mem_cons.2 ⟨subd9_0_109, List.forall_mem_cons.2 ⟨subd9_0_110, List.forall_mem_cons.2 ⟨subd9_0_111, List.forall_mem_cons.2 ⟨subd9_0_112, List.forall_mem_cons.2 ⟨subd9_0_113, List.forall_mem_cons.2 ⟨subd9_0_114, List.forall_mem_cons.2 ⟨subd9_0_115, List.forall_mem_cons.2 ⟨subd9_0_116, List.forall_mem_cons.2 ⟨subd9_0_117, List.forall_mem_cons.2 ⟨subd9_0_118, List.forall_mem_cons.2 ⟨subd9_0_119, List.forall_mem_cons.2 ⟨subd9_0_120, List.forall_mem_cons.2 ⟨subd9_0_121, List.forall_mem_cons.2 ⟨subd9_0_122, List.forall_mem_cons.2 ⟨subd9_0_123, List.forall_mem_cons.2 ⟨subd9_0_124, List.forall_mem_cons.2 ⟨subd9_0_125, List.forall_mem_cons.2 ⟨subd9_0_126, List.forall_mem_cons.2 ⟨subd9_0_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_128 : subd9_0 [0, -2, -2] = true := by decide +kernel
theorem subd9_0_129 : subd9_0 [0, -2, -1] = true := by decide +kernel
theorem subd9_0_130 : subd9_0 [0, -2, 0] = true := by decide +kernel
theorem subd9_0_131 : subd9_0 [0, -2, 1] = true := by decide +kernel
theorem subd9_0_132 : subd9_0 [0, -2, 2] = true := by decide +kernel
theorem subd9_0_133 : subd9_0 [0, -2, 3] = true := by decide +kernel
theorem subd9_0_134 : subd9_0 [0, -2, 4] = true := by decide +kernel
theorem subd9_0_135 : subd9_0 [0, -2, 5] = true := by decide +kernel
theorem subd9_0_136 : subd9_0 [0, -2, 6] = true := by decide +kernel
theorem subd9_0_137 : subd9_0 [0, -1, -7] = true := by decide +kernel
theorem subd9_0_138 : subd9_0 [0, -1, -6] = true := by decide +kernel
theorem subd9_0_139 : subd9_0 [0, -1, -5] = true := by decide +kernel
theorem subd9_0_140 : subd9_0 [0, -1, -4] = true := by decide +kernel
theorem subd9_0_141 : subd9_0 [0, -1, -3] = true := by decide +kernel
theorem subd9_0_142 : subd9_0 [0, -1, -2] = true := by decide +kernel
theorem subd9_0_143 : subd9_0 [0, -1, -1] = true := by decide +kernel
theorem subd9_0_144 : subd9_0 [0, -1, 0] = true := by decide +kernel
theorem subd9_0_145 : subd9_0 [0, -1, 1] = true := by decide +kernel
theorem subd9_0_146 : subd9_0 [0, -1, 2] = true := by decide +kernel
theorem subd9_0_147 : subd9_0 [0, -1, 3] = true := by decide +kernel
theorem subd9_0_148 : subd9_0 [0, -1, 4] = true := by decide +kernel
theorem subd9_0_149 : subd9_0 [0, -1, 5] = true := by decide +kernel
theorem subd9_0_150 : subd9_0 [0, -1, 6] = true := by decide +kernel
theorem subd9_0_151 : subd9_0 [0, 0, -7] = true := by decide +kernel
theorem subd9_0_152 : subd9_0 [0, 0, -6] = true := by decide +kernel
theorem subd9_0_153 : subd9_0 [0, 0, -5] = true := by decide +kernel
theorem subd9_0_154 : subd9_0 [0, 0, -4] = true := by decide +kernel
theorem subd9_0_155 : subd9_0 [0, 0, -3] = true := by decide +kernel
theorem subd9_0_156 : subd9_0 [0, 0, -2] = true := by decide +kernel
theorem subd9_0_157 : subd9_0 [0, 0, -1] = true := by decide +kernel
theorem subd9_0_158 : subd9_0 [0, 0, 0] = true := by decide +kernel
theorem subd9_0_159 : subd9_0 [0, 0, 1] = true := by decide +kernel
theorem sbd9_0_4 : ∀ q ∈ blkd9_0_4, subd9_0 q = true := by
  unfold blkd9_0_4
  exact List.forall_mem_cons.2 ⟨subd9_0_128, List.forall_mem_cons.2 ⟨subd9_0_129, List.forall_mem_cons.2 ⟨subd9_0_130, List.forall_mem_cons.2 ⟨subd9_0_131, List.forall_mem_cons.2 ⟨subd9_0_132, List.forall_mem_cons.2 ⟨subd9_0_133, List.forall_mem_cons.2 ⟨subd9_0_134, List.forall_mem_cons.2 ⟨subd9_0_135, List.forall_mem_cons.2 ⟨subd9_0_136, List.forall_mem_cons.2 ⟨subd9_0_137, List.forall_mem_cons.2 ⟨subd9_0_138, List.forall_mem_cons.2 ⟨subd9_0_139, List.forall_mem_cons.2 ⟨subd9_0_140, List.forall_mem_cons.2 ⟨subd9_0_141, List.forall_mem_cons.2 ⟨subd9_0_142, List.forall_mem_cons.2 ⟨subd9_0_143, List.forall_mem_cons.2 ⟨subd9_0_144, List.forall_mem_cons.2 ⟨subd9_0_145, List.forall_mem_cons.2 ⟨subd9_0_146, List.forall_mem_cons.2 ⟨subd9_0_147, List.forall_mem_cons.2 ⟨subd9_0_148, List.forall_mem_cons.2 ⟨subd9_0_149, List.forall_mem_cons.2 ⟨subd9_0_150, List.forall_mem_cons.2 ⟨subd9_0_151, List.forall_mem_cons.2 ⟨subd9_0_152, List.forall_mem_cons.2 ⟨subd9_0_153, List.forall_mem_cons.2 ⟨subd9_0_154, List.forall_mem_cons.2 ⟨subd9_0_155, List.forall_mem_cons.2 ⟨subd9_0_156, List.forall_mem_cons.2 ⟨subd9_0_157, List.forall_mem_cons.2 ⟨subd9_0_158, List.forall_mem_cons.2 ⟨subd9_0_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_160 : subd9_0 [0, 0, 2] = true := by decide +kernel
theorem subd9_0_161 : subd9_0 [0, 0, 3] = true := by decide +kernel
theorem subd9_0_162 : subd9_0 [0, 0, 4] = true := by decide +kernel
theorem subd9_0_163 : subd9_0 [0, 0, 5] = true := by decide +kernel
theorem subd9_0_164 : subd9_0 [0, 0, 6] = true := by decide +kernel
theorem subd9_0_165 : subd9_0 [0, 1, -7] = true := by decide +kernel
theorem subd9_0_166 : subd9_0 [0, 1, -6] = true := by decide +kernel
theorem subd9_0_167 : subd9_0 [0, 1, -5] = true := by decide +kernel
theorem subd9_0_168 : subd9_0 [0, 1, -4] = true := by decide +kernel
theorem subd9_0_169 : subd9_0 [0, 1, -3] = true := by decide +kernel
theorem subd9_0_170 : subd9_0 [0, 1, -2] = true := by decide +kernel
theorem subd9_0_171 : subd9_0 [0, 1, -1] = true := by decide +kernel
theorem subd9_0_172 : subd9_0 [0, 1, 0] = true := by decide +kernel
theorem subd9_0_173 : subd9_0 [0, 1, 1] = true := by decide +kernel
theorem subd9_0_174 : subd9_0 [0, 1, 2] = true := by decide +kernel
theorem subd9_0_175 : subd9_0 [0, 1, 3] = true := by decide +kernel
theorem subd9_0_176 : subd9_0 [0, 1, 4] = true := by decide +kernel
theorem subd9_0_177 : subd9_0 [0, 1, 5] = true := by decide +kernel
theorem subd9_0_178 : subd9_0 [0, 1, 6] = true := by decide +kernel
theorem subd9_0_179 : subd9_0 [0, 2, -7] = true := by decide +kernel
theorem subd9_0_180 : subd9_0 [0, 2, -6] = true := by decide +kernel
theorem subd9_0_181 : subd9_0 [0, 2, -5] = true := by decide +kernel
theorem subd9_0_182 : subd9_0 [0, 2, -4] = true := by decide +kernel
theorem subd9_0_183 : subd9_0 [0, 2, -3] = true := by decide +kernel
theorem subd9_0_184 : subd9_0 [0, 2, -2] = true := by decide +kernel
theorem subd9_0_185 : subd9_0 [0, 2, -1] = true := by decide +kernel
theorem subd9_0_186 : subd9_0 [0, 2, 0] = true := by decide +kernel
theorem subd9_0_187 : subd9_0 [0, 2, 1] = true := by decide +kernel
theorem subd9_0_188 : subd9_0 [0, 2, 2] = true := by decide +kernel
theorem subd9_0_189 : subd9_0 [0, 2, 3] = true := by decide +kernel
theorem subd9_0_190 : subd9_0 [0, 2, 4] = true := by decide +kernel
theorem subd9_0_191 : subd9_0 [0, 2, 5] = true := by decide +kernel
theorem sbd9_0_5 : ∀ q ∈ blkd9_0_5, subd9_0 q = true := by
  unfold blkd9_0_5
  exact List.forall_mem_cons.2 ⟨subd9_0_160, List.forall_mem_cons.2 ⟨subd9_0_161, List.forall_mem_cons.2 ⟨subd9_0_162, List.forall_mem_cons.2 ⟨subd9_0_163, List.forall_mem_cons.2 ⟨subd9_0_164, List.forall_mem_cons.2 ⟨subd9_0_165, List.forall_mem_cons.2 ⟨subd9_0_166, List.forall_mem_cons.2 ⟨subd9_0_167, List.forall_mem_cons.2 ⟨subd9_0_168, List.forall_mem_cons.2 ⟨subd9_0_169, List.forall_mem_cons.2 ⟨subd9_0_170, List.forall_mem_cons.2 ⟨subd9_0_171, List.forall_mem_cons.2 ⟨subd9_0_172, List.forall_mem_cons.2 ⟨subd9_0_173, List.forall_mem_cons.2 ⟨subd9_0_174, List.forall_mem_cons.2 ⟨subd9_0_175, List.forall_mem_cons.2 ⟨subd9_0_176, List.forall_mem_cons.2 ⟨subd9_0_177, List.forall_mem_cons.2 ⟨subd9_0_178, List.forall_mem_cons.2 ⟨subd9_0_179, List.forall_mem_cons.2 ⟨subd9_0_180, List.forall_mem_cons.2 ⟨subd9_0_181, List.forall_mem_cons.2 ⟨subd9_0_182, List.forall_mem_cons.2 ⟨subd9_0_183, List.forall_mem_cons.2 ⟨subd9_0_184, List.forall_mem_cons.2 ⟨subd9_0_185, List.forall_mem_cons.2 ⟨subd9_0_186, List.forall_mem_cons.2 ⟨subd9_0_187, List.forall_mem_cons.2 ⟨subd9_0_188, List.forall_mem_cons.2 ⟨subd9_0_189, List.forall_mem_cons.2 ⟨subd9_0_190, List.forall_mem_cons.2 ⟨subd9_0_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_192 : subd9_0 [0, 2, 6] = true := by decide +kernel
theorem subd9_0_193 : subd9_0 [0, 3] = true := by decide +kernel
theorem subd9_0_194 : subd9_0 [0, 4] = true := by decide +kernel
theorem subd9_0_195 : subd9_0 [0, 5] = true := by decide +kernel
theorem subd9_0_196 : subd9_0 [1, -6] = true := by decide +kernel
theorem subd9_0_197 : subd9_0 [1, -5] = true := by decide +kernel
theorem subd9_0_198 : subd9_0 [1, -4] = true := by decide +kernel
theorem subd9_0_199 : subd9_0 [1, -3] = true := by decide +kernel
theorem subd9_0_200 : subd9_0 [1, -2, -7] = true := by decide +kernel
theorem subd9_0_201 : subd9_0 [1, -2, -6] = true := by decide +kernel
theorem subd9_0_202 : subd9_0 [1, -2, -5] = true := by decide +kernel
theorem subd9_0_203 : subd9_0 [1, -2, -4] = true := by decide +kernel
theorem subd9_0_204 : subd9_0 [1, -2, -3] = true := by decide +kernel
theorem subd9_0_205 : subd9_0 [1, -2, -2] = true := by decide +kernel
theorem subd9_0_206 : subd9_0 [1, -2, -1] = true := by decide +kernel
theorem subd9_0_207 : subd9_0 [1, -2, 0] = true := by decide +kernel
theorem subd9_0_208 : subd9_0 [1, -2, 1] = true := by decide +kernel
theorem subd9_0_209 : subd9_0 [1, -2, 2] = true := by decide +kernel
theorem subd9_0_210 : subd9_0 [1, -2, 3] = true := by decide +kernel
theorem subd9_0_211 : subd9_0 [1, -2, 4] = true := by decide +kernel
theorem subd9_0_212 : subd9_0 [1, -2, 5] = true := by decide +kernel
theorem subd9_0_213 : subd9_0 [1, -2, 6] = true := by decide +kernel
theorem subd9_0_214 : subd9_0 [1, -1, -7] = true := by decide +kernel
theorem subd9_0_215 : subd9_0 [1, -1, -6] = true := by decide +kernel
theorem subd9_0_216 : subd9_0 [1, -1, -5] = true := by decide +kernel
theorem subd9_0_217 : subd9_0 [1, -1, -4] = true := by decide +kernel
theorem subd9_0_218 : subd9_0 [1, -1, -3] = true := by decide +kernel
theorem subd9_0_219 : subd9_0 [1, -1, -2] = true := by decide +kernel
theorem subd9_0_220 : subd9_0 [1, -1, -1] = true := by decide +kernel
theorem subd9_0_221 : subd9_0 [1, -1, 0] = true := by decide +kernel
theorem subd9_0_222 : subd9_0 [1, -1, 1] = true := by decide +kernel
theorem subd9_0_223 : subd9_0 [1, -1, 2] = true := by decide +kernel
theorem sbd9_0_6 : ∀ q ∈ blkd9_0_6, subd9_0 q = true := by
  unfold blkd9_0_6
  exact List.forall_mem_cons.2 ⟨subd9_0_192, List.forall_mem_cons.2 ⟨subd9_0_193, List.forall_mem_cons.2 ⟨subd9_0_194, List.forall_mem_cons.2 ⟨subd9_0_195, List.forall_mem_cons.2 ⟨subd9_0_196, List.forall_mem_cons.2 ⟨subd9_0_197, List.forall_mem_cons.2 ⟨subd9_0_198, List.forall_mem_cons.2 ⟨subd9_0_199, List.forall_mem_cons.2 ⟨subd9_0_200, List.forall_mem_cons.2 ⟨subd9_0_201, List.forall_mem_cons.2 ⟨subd9_0_202, List.forall_mem_cons.2 ⟨subd9_0_203, List.forall_mem_cons.2 ⟨subd9_0_204, List.forall_mem_cons.2 ⟨subd9_0_205, List.forall_mem_cons.2 ⟨subd9_0_206, List.forall_mem_cons.2 ⟨subd9_0_207, List.forall_mem_cons.2 ⟨subd9_0_208, List.forall_mem_cons.2 ⟨subd9_0_209, List.forall_mem_cons.2 ⟨subd9_0_210, List.forall_mem_cons.2 ⟨subd9_0_211, List.forall_mem_cons.2 ⟨subd9_0_212, List.forall_mem_cons.2 ⟨subd9_0_213, List.forall_mem_cons.2 ⟨subd9_0_214, List.forall_mem_cons.2 ⟨subd9_0_215, List.forall_mem_cons.2 ⟨subd9_0_216, List.forall_mem_cons.2 ⟨subd9_0_217, List.forall_mem_cons.2 ⟨subd9_0_218, List.forall_mem_cons.2 ⟨subd9_0_219, List.forall_mem_cons.2 ⟨subd9_0_220, List.forall_mem_cons.2 ⟨subd9_0_221, List.forall_mem_cons.2 ⟨subd9_0_222, List.forall_mem_cons.2 ⟨subd9_0_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C129
