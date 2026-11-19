import ReflectZphi.Data.Cert5.C110.Base

namespace ReflectZphi.Data.Cert5.C110

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_4_832 : subd8_4 [3, -2, 0] = true := by decide +kernel
theorem subd8_4_833 : subd8_4 [3, -2, 1] = true := by decide +kernel
theorem subd8_4_834 : subd8_4 [3, -2, 2] = true := by decide +kernel
theorem subd8_4_835 : subd8_4 [3, -2, 3] = true := by decide +kernel
theorem subd8_4_836 : subd8_4 [3, -2, 4] = true := by decide +kernel
theorem subd8_4_837 : subd8_4 [3, -2, 5] = true := by decide +kernel
theorem subd8_4_838 : subd8_4 [3, -2, 6] = true := by decide +kernel
theorem subd8_4_839 : subd8_4 [3, -1, -7] = true := by decide +kernel
theorem subd8_4_840 : subd8_4 [3, -1, -6] = true := by decide +kernel
theorem subd8_4_841 : subd8_4 [3, -1, -5] = true := by decide +kernel
theorem subd8_4_842 : subd8_4 [3, -1, -4] = true := by decide +kernel
theorem subd8_4_843 : subd8_4 [3, -1, -3] = true := by decide +kernel
theorem subd8_4_844 : subd8_4 [3, -1, -2] = true := by decide +kernel
theorem subd8_4_845 : subd8_4 [3, -1, -1] = true := by decide +kernel
theorem subd8_4_846 : subd8_4 [3, -1, 0] = true := by decide +kernel
theorem subd8_4_847 : subd8_4 [3, -1, 1] = true := by decide +kernel
theorem subd8_4_848 : subd8_4 [3, -1, 2] = true := by decide +kernel
theorem subd8_4_849 : subd8_4 [3, -1, 3] = true := by decide +kernel
theorem subd8_4_850 : subd8_4 [3, -1, 4] = true := by decide +kernel
theorem subd8_4_851 : subd8_4 [3, -1, 5] = true := by decide +kernel
theorem subd8_4_852 : subd8_4 [3, -1, 6] = true := by decide +kernel
theorem subd8_4_853 : subd8_4 [3, -1, 7] = true := by decide +kernel
theorem subd8_4_854 : subd8_4 [3, 0, -6] = true := by decide +kernel
theorem subd8_4_855 : subd8_4 [3, 0, -5] = true := by decide +kernel
theorem subd8_4_856 : subd8_4 [3, 0, -4] = true := by decide +kernel
theorem subd8_4_857 : subd8_4 [3, 0, -3] = true := by decide +kernel
theorem subd8_4_858 : subd8_4 [3, 0, -2] = true := by decide +kernel
theorem subd8_4_859 : subd8_4 [3, 0, -1] = true := by decide +kernel
theorem subd8_4_860 : subd8_4 [3, 0, 0] = true := by decide +kernel
theorem subd8_4_861 : subd8_4 [3, 0, 1] = true := by decide +kernel
theorem subd8_4_862 : subd8_4 [3, 0, 2] = true := by decide +kernel
theorem subd8_4_863 : subd8_4 [3, 0, 3] = true := by decide +kernel
theorem sbd8_4_26 : ∀ q ∈ blkd8_4_26, subd8_4 q = true := by
  unfold blkd8_4_26
  exact List.forall_mem_cons.2 ⟨subd8_4_832, List.forall_mem_cons.2 ⟨subd8_4_833, List.forall_mem_cons.2 ⟨subd8_4_834, List.forall_mem_cons.2 ⟨subd8_4_835, List.forall_mem_cons.2 ⟨subd8_4_836, List.forall_mem_cons.2 ⟨subd8_4_837, List.forall_mem_cons.2 ⟨subd8_4_838, List.forall_mem_cons.2 ⟨subd8_4_839, List.forall_mem_cons.2 ⟨subd8_4_840, List.forall_mem_cons.2 ⟨subd8_4_841, List.forall_mem_cons.2 ⟨subd8_4_842, List.forall_mem_cons.2 ⟨subd8_4_843, List.forall_mem_cons.2 ⟨subd8_4_844, List.forall_mem_cons.2 ⟨subd8_4_845, List.forall_mem_cons.2 ⟨subd8_4_846, List.forall_mem_cons.2 ⟨subd8_4_847, List.forall_mem_cons.2 ⟨subd8_4_848, List.forall_mem_cons.2 ⟨subd8_4_849, List.forall_mem_cons.2 ⟨subd8_4_850, List.forall_mem_cons.2 ⟨subd8_4_851, List.forall_mem_cons.2 ⟨subd8_4_852, List.forall_mem_cons.2 ⟨subd8_4_853, List.forall_mem_cons.2 ⟨subd8_4_854, List.forall_mem_cons.2 ⟨subd8_4_855, List.forall_mem_cons.2 ⟨subd8_4_856, List.forall_mem_cons.2 ⟨subd8_4_857, List.forall_mem_cons.2 ⟨subd8_4_858, List.forall_mem_cons.2 ⟨subd8_4_859, List.forall_mem_cons.2 ⟨subd8_4_860, List.forall_mem_cons.2 ⟨subd8_4_861, List.forall_mem_cons.2 ⟨subd8_4_862, List.forall_mem_cons.2 ⟨subd8_4_863, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_4_864 : subd8_4 [3, 0, 4] = true := by decide +kernel
theorem subd8_4_865 : subd8_4 [3, 0, 5] = true := by decide +kernel
theorem subd8_4_866 : subd8_4 [3, 0, 6] = true := by decide +kernel
theorem subd8_4_867 : subd8_4 [3, 0, 7] = true := by decide +kernel
theorem subd8_4_868 : subd8_4 [3, 0, 8] = true := by decide +kernel
theorem subd8_4_869 : subd8_4 [3, 1, -6] = true := by decide +kernel
theorem subd8_4_870 : subd8_4 [3, 1, -5] = true := by decide +kernel
theorem subd8_4_871 : subd8_4 [3, 1, -4] = true := by decide +kernel
theorem subd8_4_872 : subd8_4 [3, 1, -3] = true := by decide +kernel
theorem subd8_4_873 : subd8_4 [3, 1, -2] = true := by decide +kernel
theorem subd8_4_874 : subd8_4 [3, 1, -1] = true := by decide +kernel
theorem subd8_4_875 : subd8_4 [3, 1, 0] = true := by decide +kernel
theorem subd8_4_876 : subd8_4 [3, 1, 1] = true := by decide +kernel
theorem subd8_4_877 : subd8_4 [3, 1, 2] = true := by decide +kernel
theorem subd8_4_878 : subd8_4 [3, 1, 3] = true := by decide +kernel
theorem subd8_4_879 : subd8_4 [3, 1, 4] = true := by decide +kernel
theorem subd8_4_880 : subd8_4 [3, 1, 5] = true := by decide +kernel
theorem subd8_4_881 : subd8_4 [3, 1, 6] = true := by decide +kernel
theorem subd8_4_882 : subd8_4 [3, 1, 7] = true := by decide +kernel
theorem subd8_4_883 : subd8_4 [3, 1, 8] = true := by decide +kernel
theorem subd8_4_884 : subd8_4 [3, 2, -5] = true := by decide +kernel
theorem subd8_4_885 : subd8_4 [3, 2, -4] = true := by decide +kernel
theorem subd8_4_886 : subd8_4 [3, 2, -3] = true := by decide +kernel
theorem subd8_4_887 : subd8_4 [3, 2, -2] = true := by decide +kernel
theorem subd8_4_888 : subd8_4 [3, 2, -1] = true := by decide +kernel
theorem subd8_4_889 : subd8_4 [3, 2, 0] = true := by decide +kernel
theorem subd8_4_890 : subd8_4 [3, 2, 1] = true := by decide +kernel
theorem subd8_4_891 : subd8_4 [3, 2, 2] = true := by decide +kernel
theorem subd8_4_892 : subd8_4 [3, 2, 3] = true := by decide +kernel
theorem subd8_4_893 : subd8_4 [3, 2, 4] = true := by decide +kernel
theorem subd8_4_894 : subd8_4 [3, 2, 5] = true := by decide +kernel
theorem subd8_4_895 : subd8_4 [3, 2, 6] = true := by decide +kernel
theorem sbd8_4_27 : ∀ q ∈ blkd8_4_27, subd8_4 q = true := by
  unfold blkd8_4_27
  exact List.forall_mem_cons.2 ⟨subd8_4_864, List.forall_mem_cons.2 ⟨subd8_4_865, List.forall_mem_cons.2 ⟨subd8_4_866, List.forall_mem_cons.2 ⟨subd8_4_867, List.forall_mem_cons.2 ⟨subd8_4_868, List.forall_mem_cons.2 ⟨subd8_4_869, List.forall_mem_cons.2 ⟨subd8_4_870, List.forall_mem_cons.2 ⟨subd8_4_871, List.forall_mem_cons.2 ⟨subd8_4_872, List.forall_mem_cons.2 ⟨subd8_4_873, List.forall_mem_cons.2 ⟨subd8_4_874, List.forall_mem_cons.2 ⟨subd8_4_875, List.forall_mem_cons.2 ⟨subd8_4_876, List.forall_mem_cons.2 ⟨subd8_4_877, List.forall_mem_cons.2 ⟨subd8_4_878, List.forall_mem_cons.2 ⟨subd8_4_879, List.forall_mem_cons.2 ⟨subd8_4_880, List.forall_mem_cons.2 ⟨subd8_4_881, List.forall_mem_cons.2 ⟨subd8_4_882, List.forall_mem_cons.2 ⟨subd8_4_883, List.forall_mem_cons.2 ⟨subd8_4_884, List.forall_mem_cons.2 ⟨subd8_4_885, List.forall_mem_cons.2 ⟨subd8_4_886, List.forall_mem_cons.2 ⟨subd8_4_887, List.forall_mem_cons.2 ⟨subd8_4_888, List.forall_mem_cons.2 ⟨subd8_4_889, List.forall_mem_cons.2 ⟨subd8_4_890, List.forall_mem_cons.2 ⟨subd8_4_891, List.forall_mem_cons.2 ⟨subd8_4_892, List.forall_mem_cons.2 ⟨subd8_4_893, List.forall_mem_cons.2 ⟨subd8_4_894, List.forall_mem_cons.2 ⟨subd8_4_895, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_4_896 : subd8_4 [3, 2, 7] = true := by decide +kernel
theorem subd8_4_897 : subd8_4 [3, 2, 8] = true := by decide +kernel
theorem subd8_4_898 : subd8_4 [3, 3] = true := by decide +kernel
theorem subd8_4_899 : subd8_4 [3, 4] = true := by decide +kernel
theorem subd8_4_900 : subd8_4 [3, 5] = true := by decide +kernel
theorem subd8_4_901 : subd8_4 [3, 6] = true := by decide +kernel
theorem subd8_4_902 : subd8_4 [4, -7] = true := by decide +kernel
theorem subd8_4_903 : subd8_4 [4, -6] = true := by decide +kernel
theorem subd8_4_904 : subd8_4 [4, -5] = true := by decide +kernel
theorem subd8_4_905 : subd8_4 [4, -4] = true := by decide +kernel
theorem subd8_4_906 : subd8_4 [4, -3] = true := by decide +kernel
theorem subd8_4_907 : subd8_4 [4, -2] = true := by decide +kernel
theorem subd8_4_908 : subd8_4 [4, -1, -6] = true := by decide +kernel
theorem subd8_4_909 : subd8_4 [4, -1, -5] = true := by decide +kernel
theorem subd8_4_910 : subd8_4 [4, -1, -4] = true := by decide +kernel
theorem subd8_4_911 : subd8_4 [4, -1, -3] = true := by decide +kernel
theorem subd8_4_912 : subd8_4 [4, -1, -2] = true := by decide +kernel
theorem subd8_4_913 : subd8_4 [4, -1, -1] = true := by decide +kernel
theorem subd8_4_914 : subd8_4 [4, -1, 0] = true := by decide +kernel
theorem subd8_4_915 : subd8_4 [4, -1, 1] = true := by decide +kernel
theorem subd8_4_916 : subd8_4 [4, -1, 2] = true := by decide +kernel
theorem subd8_4_917 : subd8_4 [4, -1, 3] = true := by decide +kernel
theorem subd8_4_918 : subd8_4 [4, -1, 4] = true := by decide +kernel
theorem subd8_4_919 : subd8_4 [4, -1, 5] = true := by decide +kernel
theorem subd8_4_920 : subd8_4 [4, -1, 6] = true := by decide +kernel
theorem subd8_4_921 : subd8_4 [4, -1, 7] = true := by decide +kernel
theorem subd8_4_922 : subd8_4 [4, 0, -5] = true := by decide +kernel
theorem subd8_4_923 : subd8_4 [4, 0, -4] = true := by decide +kernel
theorem subd8_4_924 : subd8_4 [4, 0, -3] = true := by decide +kernel
theorem subd8_4_925 : subd8_4 [4, 0, -2] = true := by decide +kernel
theorem subd8_4_926 : subd8_4 [4, 0, -1] = true := by decide +kernel
theorem subd8_4_927 : subd8_4 [4, 0, 0] = true := by decide +kernel
theorem sbd8_4_28 : ∀ q ∈ blkd8_4_28, subd8_4 q = true := by
  unfold blkd8_4_28
  exact List.forall_mem_cons.2 ⟨subd8_4_896, List.forall_mem_cons.2 ⟨subd8_4_897, List.forall_mem_cons.2 ⟨subd8_4_898, List.forall_mem_cons.2 ⟨subd8_4_899, List.forall_mem_cons.2 ⟨subd8_4_900, List.forall_mem_cons.2 ⟨subd8_4_901, List.forall_mem_cons.2 ⟨subd8_4_902, List.forall_mem_cons.2 ⟨subd8_4_903, List.forall_mem_cons.2 ⟨subd8_4_904, List.forall_mem_cons.2 ⟨subd8_4_905, List.forall_mem_cons.2 ⟨subd8_4_906, List.forall_mem_cons.2 ⟨subd8_4_907, List.forall_mem_cons.2 ⟨subd8_4_908, List.forall_mem_cons.2 ⟨subd8_4_909, List.forall_mem_cons.2 ⟨subd8_4_910, List.forall_mem_cons.2 ⟨subd8_4_911, List.forall_mem_cons.2 ⟨subd8_4_912, List.forall_mem_cons.2 ⟨subd8_4_913, List.forall_mem_cons.2 ⟨subd8_4_914, List.forall_mem_cons.2 ⟨subd8_4_915, List.forall_mem_cons.2 ⟨subd8_4_916, List.forall_mem_cons.2 ⟨subd8_4_917, List.forall_mem_cons.2 ⟨subd8_4_918, List.forall_mem_cons.2 ⟨subd8_4_919, List.forall_mem_cons.2 ⟨subd8_4_920, List.forall_mem_cons.2 ⟨subd8_4_921, List.forall_mem_cons.2 ⟨subd8_4_922, List.forall_mem_cons.2 ⟨subd8_4_923, List.forall_mem_cons.2 ⟨subd8_4_924, List.forall_mem_cons.2 ⟨subd8_4_925, List.forall_mem_cons.2 ⟨subd8_4_926, List.forall_mem_cons.2 ⟨subd8_4_927, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_4_928 : subd8_4 [4, 0, 1] = true := by decide +kernel
theorem subd8_4_929 : subd8_4 [4, 0, 2] = true := by decide +kernel
theorem subd8_4_930 : subd8_4 [4, 0, 3] = true := by decide +kernel
theorem subd8_4_931 : subd8_4 [4, 0, 4] = true := by decide +kernel
theorem subd8_4_932 : subd8_4 [4, 0, 5] = true := by decide +kernel
theorem subd8_4_933 : subd8_4 [4, 0, 6] = true := by decide +kernel
theorem subd8_4_934 : subd8_4 [4, 0, 7] = true := by decide +kernel
theorem subd8_4_935 : subd8_4 [4, 1] = true := by decide +kernel
theorem subd8_4_936 : subd8_4 [4, 2] = true := by decide +kernel
theorem subd8_4_937 : subd8_4 [4, 3] = true := by decide +kernel
theorem subd8_4_938 : subd8_4 [4, 4] = true := by decide +kernel
theorem subd8_4_939 : subd8_4 [4, 5] = true := by decide +kernel
theorem subd8_4_940 : subd8_4 [5, -6] = true := by decide +kernel
theorem subd8_4_941 : subd8_4 [5, -5] = true := by decide +kernel
theorem subd8_4_942 : subd8_4 [5, -4] = true := by decide +kernel
theorem subd8_4_943 : subd8_4 [5, -3] = true := by decide +kernel
theorem subd8_4_944 : subd8_4 [5, -2] = true := by decide +kernel
theorem subd8_4_945 : subd8_4 [5, -1] = true := by decide +kernel
theorem subd8_4_946 : subd8_4 [5, 0] = true := by decide +kernel
theorem subd8_4_947 : subd8_4 [5, 1] = true := by decide +kernel
theorem subd8_4_948 : subd8_4 [5, 2] = true := by decide +kernel
theorem subd8_4_949 : subd8_4 [5, 3] = true := by decide +kernel
theorem subd8_4_950 : subd8_4 [5, 4] = true := by decide +kernel
theorem subd8_4_951 : subd8_4 [6, -5] = true := by decide +kernel
theorem subd8_4_952 : subd8_4 [6, -4] = true := by decide +kernel
theorem subd8_4_953 : subd8_4 [6, -3] = true := by decide +kernel
theorem subd8_4_954 : subd8_4 [6, -2] = true := by decide +kernel
theorem subd8_4_955 : subd8_4 [6, -1] = true := by decide +kernel
theorem subd8_4_956 : subd8_4 [6, 0] = true := by decide +kernel
theorem subd8_4_957 : subd8_4 [6, 1] = true := by decide +kernel
theorem subd8_4_958 : subd8_4 [6, 2] = true := by decide +kernel
theorem sbd8_4_29 : ∀ q ∈ blkd8_4_29, subd8_4 q = true := by
  unfold blkd8_4_29
  exact List.forall_mem_cons.2 ⟨subd8_4_928, List.forall_mem_cons.2 ⟨subd8_4_929, List.forall_mem_cons.2 ⟨subd8_4_930, List.forall_mem_cons.2 ⟨subd8_4_931, List.forall_mem_cons.2 ⟨subd8_4_932, List.forall_mem_cons.2 ⟨subd8_4_933, List.forall_mem_cons.2 ⟨subd8_4_934, List.forall_mem_cons.2 ⟨subd8_4_935, List.forall_mem_cons.2 ⟨subd8_4_936, List.forall_mem_cons.2 ⟨subd8_4_937, List.forall_mem_cons.2 ⟨subd8_4_938, List.forall_mem_cons.2 ⟨subd8_4_939, List.forall_mem_cons.2 ⟨subd8_4_940, List.forall_mem_cons.2 ⟨subd8_4_941, List.forall_mem_cons.2 ⟨subd8_4_942, List.forall_mem_cons.2 ⟨subd8_4_943, List.forall_mem_cons.2 ⟨subd8_4_944, List.forall_mem_cons.2 ⟨subd8_4_945, List.forall_mem_cons.2 ⟨subd8_4_946, List.forall_mem_cons.2 ⟨subd8_4_947, List.forall_mem_cons.2 ⟨subd8_4_948, List.forall_mem_cons.2 ⟨subd8_4_949, List.forall_mem_cons.2 ⟨subd8_4_950, List.forall_mem_cons.2 ⟨subd8_4_951, List.forall_mem_cons.2 ⟨subd8_4_952, List.forall_mem_cons.2 ⟨subd8_4_953, List.forall_mem_cons.2 ⟨subd8_4_954, List.forall_mem_cons.2 ⟨subd8_4_955, List.forall_mem_cons.2 ⟨subd8_4_956, List.forall_mem_cons.2 ⟨subd8_4_957, List.forall_mem_cons.2 ⟨subd8_4_958, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_0 : ldCheck G d9_0.U d9_0.ms ldd9_0 = true := by decide +kernel
theorem pre_okd9_0 : subPre G cell9 d9_0 = true := by decide +kernel
theorem subd9_0_0 : subd9_0 [-4] = true := by decide +kernel
theorem subd9_0_1 : subd9_0 [-3, -3] = true := by decide +kernel
theorem subd9_0_2 : subd9_0 [-3, -2] = true := by decide +kernel
theorem subd9_0_3 : subd9_0 [-3, -1] = true := by decide +kernel
theorem subd9_0_4 : subd9_0 [-3, 0] = true := by decide +kernel
theorem subd9_0_5 : subd9_0 [-3, 1] = true := by decide +kernel
theorem subd9_0_6 : subd9_0 [-3, 2] = true := by decide +kernel
theorem subd9_0_7 : subd9_0 [-3, 3] = true := by decide +kernel
theorem subd9_0_8 : subd9_0 [-2, -4] = true := by decide +kernel
theorem subd9_0_9 : subd9_0 [-2, -3] = true := by decide +kernel
theorem subd9_0_10 : subd9_0 [-2, -2] = true := by decide +kernel
theorem subd9_0_11 : subd9_0 [-2, -1] = true := by decide +kernel
theorem subd9_0_12 : subd9_0 [-2, 0] = true := by decide +kernel
theorem subd9_0_13 : subd9_0 [-2, 1] = true := by decide +kernel
theorem subd9_0_14 : subd9_0 [-2, 2] = true := by decide +kernel
theorem subd9_0_15 : subd9_0 [-2, 3] = true := by decide +kernel
theorem subd9_0_16 : subd9_0 [-1, -4] = true := by decide +kernel
theorem subd9_0_17 : subd9_0 [-1, -3] = true := by decide +kernel
theorem subd9_0_18 : subd9_0 [-1, -2] = true := by decide +kernel
theorem subd9_0_19 : subd9_0 [-1, -1] = true := by decide +kernel
theorem subd9_0_20 : subd9_0 [-1, 0] = true := by decide +kernel
theorem subd9_0_21 : subd9_0 [-1, 1] = true := by decide +kernel
theorem subd9_0_22 : subd9_0 [-1, 2] = true := by decide +kernel
theorem subd9_0_23 : subd9_0 [-1, 3] = true := by decide +kernel
theorem subd9_0_24 : subd9_0 [0, -5] = true := by decide +kernel
theorem subd9_0_25 : subd9_0 [0, -4] = true := by decide +kernel
theorem subd9_0_26 : subd9_0 [0, -3] = true := by decide +kernel
theorem subd9_0_27 : subd9_0 [0, -2] = true := by decide +kernel
theorem subd9_0_28 : subd9_0 [0, -1] = true := by decide +kernel
theorem subd9_0_29 : subd9_0 [0, 0] = true := by decide +kernel
theorem subd9_0_30 : subd9_0 [0, 1] = true := by decide +kernel
theorem subd9_0_31 : subd9_0 [0, 2] = true := by decide +kernel
theorem sbd9_0_0 : ∀ q ∈ blkd9_0_0, subd9_0 q = true := by
  unfold blkd9_0_0
  exact List.forall_mem_cons.2 ⟨subd9_0_0, List.forall_mem_cons.2 ⟨subd9_0_1, List.forall_mem_cons.2 ⟨subd9_0_2, List.forall_mem_cons.2 ⟨subd9_0_3, List.forall_mem_cons.2 ⟨subd9_0_4, List.forall_mem_cons.2 ⟨subd9_0_5, List.forall_mem_cons.2 ⟨subd9_0_6, List.forall_mem_cons.2 ⟨subd9_0_7, List.forall_mem_cons.2 ⟨subd9_0_8, List.forall_mem_cons.2 ⟨subd9_0_9, List.forall_mem_cons.2 ⟨subd9_0_10, List.forall_mem_cons.2 ⟨subd9_0_11, List.forall_mem_cons.2 ⟨subd9_0_12, List.forall_mem_cons.2 ⟨subd9_0_13, List.forall_mem_cons.2 ⟨subd9_0_14, List.forall_mem_cons.2 ⟨subd9_0_15, List.forall_mem_cons.2 ⟨subd9_0_16, List.forall_mem_cons.2 ⟨subd9_0_17, List.forall_mem_cons.2 ⟨subd9_0_18, List.forall_mem_cons.2 ⟨subd9_0_19, List.forall_mem_cons.2 ⟨subd9_0_20, List.forall_mem_cons.2 ⟨subd9_0_21, List.forall_mem_cons.2 ⟨subd9_0_22, List.forall_mem_cons.2 ⟨subd9_0_23, List.forall_mem_cons.2 ⟨subd9_0_24, List.forall_mem_cons.2 ⟨subd9_0_25, List.forall_mem_cons.2 ⟨subd9_0_26, List.forall_mem_cons.2 ⟨subd9_0_27, List.forall_mem_cons.2 ⟨subd9_0_28, List.forall_mem_cons.2 ⟨subd9_0_29, List.forall_mem_cons.2 ⟨subd9_0_30, List.forall_mem_cons.2 ⟨subd9_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_32 : subd9_0 [0, 3] = true := by decide +kernel
theorem subd9_0_33 : subd9_0 [0, 4] = true := by decide +kernel
theorem subd9_0_34 : subd9_0 [1, -4] = true := by decide +kernel
theorem subd9_0_35 : subd9_0 [1, -3] = true := by decide +kernel
theorem subd9_0_36 : subd9_0 [1, -2] = true := by decide +kernel
theorem subd9_0_37 : subd9_0 [1, -1] = true := by decide +kernel
theorem subd9_0_38 : subd9_0 [1, 0] = true := by decide +kernel
theorem subd9_0_39 : subd9_0 [1, 1] = true := by decide +kernel
theorem subd9_0_40 : subd9_0 [1, 2] = true := by decide +kernel
theorem subd9_0_41 : subd9_0 [1, 3] = true := by decide +kernel
theorem subd9_0_42 : subd9_0 [2, -4] = true := by decide +kernel
theorem subd9_0_43 : subd9_0 [2, -3] = true := by decide +kernel
theorem subd9_0_44 : subd9_0 [2, -2] = true := by decide +kernel
theorem subd9_0_45 : subd9_0 [2, -1] = true := by decide +kernel
theorem subd9_0_46 : subd9_0 [2, 0] = true := by decide +kernel
theorem subd9_0_47 : subd9_0 [2, 1] = true := by decide +kernel
theorem subd9_0_48 : subd9_0 [2, 2] = true := by decide +kernel
theorem subd9_0_49 : subd9_0 [2, 3] = true := by decide +kernel
theorem subd9_0_50 : subd9_0 [3, -4] = true := by decide +kernel
theorem subd9_0_51 : subd9_0 [3, -3] = true := by decide +kernel
theorem subd9_0_52 : subd9_0 [3, -2] = true := by decide +kernel
theorem subd9_0_53 : subd9_0 [3, -1] = true := by decide +kernel
theorem subd9_0_54 : subd9_0 [3, 0] = true := by decide +kernel
theorem subd9_0_55 : subd9_0 [3, 1] = true := by decide +kernel
theorem subd9_0_56 : subd9_0 [3, 2] = true := by decide +kernel
theorem subd9_0_57 : subd9_0 [4] = true := by decide +kernel
theorem sbd9_0_1 : ∀ q ∈ blkd9_0_1, subd9_0 q = true := by
  unfold blkd9_0_1
  exact List.forall_mem_cons.2 ⟨subd9_0_32, List.forall_mem_cons.2 ⟨subd9_0_33, List.forall_mem_cons.2 ⟨subd9_0_34, List.forall_mem_cons.2 ⟨subd9_0_35, List.forall_mem_cons.2 ⟨subd9_0_36, List.forall_mem_cons.2 ⟨subd9_0_37, List.forall_mem_cons.2 ⟨subd9_0_38, List.forall_mem_cons.2 ⟨subd9_0_39, List.forall_mem_cons.2 ⟨subd9_0_40, List.forall_mem_cons.2 ⟨subd9_0_41, List.forall_mem_cons.2 ⟨subd9_0_42, List.forall_mem_cons.2 ⟨subd9_0_43, List.forall_mem_cons.2 ⟨subd9_0_44, List.forall_mem_cons.2 ⟨subd9_0_45, List.forall_mem_cons.2 ⟨subd9_0_46, List.forall_mem_cons.2 ⟨subd9_0_47, List.forall_mem_cons.2 ⟨subd9_0_48, List.forall_mem_cons.2 ⟨subd9_0_49, List.forall_mem_cons.2 ⟨subd9_0_50, List.forall_mem_cons.2 ⟨subd9_0_51, List.forall_mem_cons.2 ⟨subd9_0_52, List.forall_mem_cons.2 ⟨subd9_0_53, List.forall_mem_cons.2 ⟨subd9_0_54, List.forall_mem_cons.2 ⟨subd9_0_55, List.forall_mem_cons.2 ⟨subd9_0_56, List.forall_mem_cons.2 ⟨subd9_0_57, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C110
