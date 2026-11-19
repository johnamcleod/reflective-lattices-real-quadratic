import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_3_832 : subd6_3 [2, 1, 7] = true := by decide +kernel
theorem subd6_3_833 : subd6_3 [2, 1, 8] = true := by decide +kernel
theorem subd6_3_834 : subd6_3 [2, 2, -9] = true := by decide +kernel
theorem subd6_3_835 : subd6_3 [2, 2, -8] = true := by decide +kernel
theorem subd6_3_836 : subd6_3 [2, 2, -7] = true := by decide +kernel
theorem subd6_3_837 : subd6_3 [2, 2, -6] = true := by decide +kernel
theorem subd6_3_838 : subd6_3 [2, 2, -5] = true := by decide +kernel
theorem subd6_3_839 : subd6_3 [2, 2, -4] = true := by decide +kernel
theorem subd6_3_840 : subd6_3 [2, 2, -3] = true := by decide +kernel
theorem subd6_3_841 : subd6_3 [2, 2, -2] = true := by decide +kernel
theorem subd6_3_842 : subd6_3 [2, 2, -1] = true := by decide +kernel
theorem subd6_3_843 : subd6_3 [2, 2, 0] = true := by decide +kernel
theorem subd6_3_844 : subd6_3 [2, 2, 1] = true := by decide +kernel
theorem subd6_3_845 : subd6_3 [2, 2, 2] = true := by decide +kernel
theorem subd6_3_846 : subd6_3 [2, 2, 3] = true := by decide +kernel
theorem subd6_3_847 : subd6_3 [2, 2, 4] = true := by decide +kernel
theorem subd6_3_848 : subd6_3 [2, 2, 5] = true := by decide +kernel
theorem subd6_3_849 : subd6_3 [2, 2, 6] = true := by decide +kernel
theorem subd6_3_850 : subd6_3 [2, 2, 7] = true := by decide +kernel
theorem subd6_3_851 : subd6_3 [2, 3, -9] = true := by decide +kernel
theorem subd6_3_852 : subd6_3 [2, 3, -8] = true := by decide +kernel
theorem subd6_3_853 : subd6_3 [2, 3, -7] = true := by decide +kernel
theorem subd6_3_854 : subd6_3 [2, 3, -6] = true := by decide +kernel
theorem subd6_3_855 : subd6_3 [2, 3, -5] = true := by decide +kernel
theorem subd6_3_856 : subd6_3 [2, 3, -4] = true := by decide +kernel
theorem subd6_3_857 : subd6_3 [2, 3, -3] = true := by decide +kernel
theorem subd6_3_858 : subd6_3 [2, 3, -2] = true := by decide +kernel
theorem subd6_3_859 : subd6_3 [2, 3, -1] = true := by decide +kernel
theorem subd6_3_860 : subd6_3 [2, 3, 0] = true := by decide +kernel
theorem subd6_3_861 : subd6_3 [2, 3, 1] = true := by decide +kernel
theorem subd6_3_862 : subd6_3 [2, 3, 2] = true := by decide +kernel
theorem subd6_3_863 : subd6_3 [2, 3, 3] = true := by decide +kernel
theorem sbd6_3_26 : ∀ q ∈ blkd6_3_26, subd6_3 q = true := by
  unfold blkd6_3_26
  exact List.forall_mem_cons.2 ⟨subd6_3_832, List.forall_mem_cons.2 ⟨subd6_3_833, List.forall_mem_cons.2 ⟨subd6_3_834, List.forall_mem_cons.2 ⟨subd6_3_835, List.forall_mem_cons.2 ⟨subd6_3_836, List.forall_mem_cons.2 ⟨subd6_3_837, List.forall_mem_cons.2 ⟨subd6_3_838, List.forall_mem_cons.2 ⟨subd6_3_839, List.forall_mem_cons.2 ⟨subd6_3_840, List.forall_mem_cons.2 ⟨subd6_3_841, List.forall_mem_cons.2 ⟨subd6_3_842, List.forall_mem_cons.2 ⟨subd6_3_843, List.forall_mem_cons.2 ⟨subd6_3_844, List.forall_mem_cons.2 ⟨subd6_3_845, List.forall_mem_cons.2 ⟨subd6_3_846, List.forall_mem_cons.2 ⟨subd6_3_847, List.forall_mem_cons.2 ⟨subd6_3_848, List.forall_mem_cons.2 ⟨subd6_3_849, List.forall_mem_cons.2 ⟨subd6_3_850, List.forall_mem_cons.2 ⟨subd6_3_851, List.forall_mem_cons.2 ⟨subd6_3_852, List.forall_mem_cons.2 ⟨subd6_3_853, List.forall_mem_cons.2 ⟨subd6_3_854, List.forall_mem_cons.2 ⟨subd6_3_855, List.forall_mem_cons.2 ⟨subd6_3_856, List.forall_mem_cons.2 ⟨subd6_3_857, List.forall_mem_cons.2 ⟨subd6_3_858, List.forall_mem_cons.2 ⟨subd6_3_859, List.forall_mem_cons.2 ⟨subd6_3_860, List.forall_mem_cons.2 ⟨subd6_3_861, List.forall_mem_cons.2 ⟨subd6_3_862, List.forall_mem_cons.2 ⟨subd6_3_863, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_3_864 : subd6_3 [2, 3, 4] = true := by decide +kernel
theorem subd6_3_865 : subd6_3 [2, 3, 5] = true := by decide +kernel
theorem subd6_3_866 : subd6_3 [2, 3, 6] = true := by decide +kernel
theorem subd6_3_867 : subd6_3 [2, 4, -8] = true := by decide +kernel
theorem subd6_3_868 : subd6_3 [2, 4, -7] = true := by decide +kernel
theorem subd6_3_869 : subd6_3 [2, 4, -6] = true := by decide +kernel
theorem subd6_3_870 : subd6_3 [2, 4, -5] = true := by decide +kernel
theorem subd6_3_871 : subd6_3 [2, 4, -4] = true := by decide +kernel
theorem subd6_3_872 : subd6_3 [2, 4, -3] = true := by decide +kernel
theorem subd6_3_873 : subd6_3 [2, 4, -2] = true := by decide +kernel
theorem subd6_3_874 : subd6_3 [2, 4, -1] = true := by decide +kernel
theorem subd6_3_875 : subd6_3 [2, 4, 0] = true := by decide +kernel
theorem subd6_3_876 : subd6_3 [2, 4, 1] = true := by decide +kernel
theorem subd6_3_877 : subd6_3 [2, 4, 2] = true := by decide +kernel
theorem subd6_3_878 : subd6_3 [2, 4, 3] = true := by decide +kernel
theorem subd6_3_879 : subd6_3 [2, 4, 4] = true := by decide +kernel
theorem subd6_3_880 : subd6_3 [2, 4, 5] = true := by decide +kernel
theorem subd6_3_881 : subd6_3 [2, 5] = true := by decide +kernel
theorem subd6_3_882 : subd6_3 [3, -5] = true := by decide +kernel
theorem subd6_3_883 : subd6_3 [3, -4] = true := by decide +kernel
theorem subd6_3_884 : subd6_3 [3, -3] = true := by decide +kernel
theorem subd6_3_885 : subd6_3 [3, -2, -6] = true := by decide +kernel
theorem subd6_3_886 : subd6_3 [3, -2, -5] = true := by decide +kernel
theorem subd6_3_887 : subd6_3 [3, -2, -4] = true := by decide +kernel
theorem subd6_3_888 : subd6_3 [3, -2, -3] = true := by decide +kernel
theorem subd6_3_889 : subd6_3 [3, -2, -2] = true := by decide +kernel
theorem subd6_3_890 : subd6_3 [3, -2, -1] = true := by decide +kernel
theorem subd6_3_891 : subd6_3 [3, -2, 0] = true := by decide +kernel
theorem subd6_3_892 : subd6_3 [3, -2, 1] = true := by decide +kernel
theorem subd6_3_893 : subd6_3 [3, -2, 2] = true := by decide +kernel
theorem subd6_3_894 : subd6_3 [3, -2, 3] = true := by decide +kernel
theorem subd6_3_895 : subd6_3 [3, -2, 4] = true := by decide +kernel
theorem sbd6_3_27 : ∀ q ∈ blkd6_3_27, subd6_3 q = true := by
  unfold blkd6_3_27
  exact List.forall_mem_cons.2 ⟨subd6_3_864, List.forall_mem_cons.2 ⟨subd6_3_865, List.forall_mem_cons.2 ⟨subd6_3_866, List.forall_mem_cons.2 ⟨subd6_3_867, List.forall_mem_cons.2 ⟨subd6_3_868, List.forall_mem_cons.2 ⟨subd6_3_869, List.forall_mem_cons.2 ⟨subd6_3_870, List.forall_mem_cons.2 ⟨subd6_3_871, List.forall_mem_cons.2 ⟨subd6_3_872, List.forall_mem_cons.2 ⟨subd6_3_873, List.forall_mem_cons.2 ⟨subd6_3_874, List.forall_mem_cons.2 ⟨subd6_3_875, List.forall_mem_cons.2 ⟨subd6_3_876, List.forall_mem_cons.2 ⟨subd6_3_877, List.forall_mem_cons.2 ⟨subd6_3_878, List.forall_mem_cons.2 ⟨subd6_3_879, List.forall_mem_cons.2 ⟨subd6_3_880, List.forall_mem_cons.2 ⟨subd6_3_881, List.forall_mem_cons.2 ⟨subd6_3_882, List.forall_mem_cons.2 ⟨subd6_3_883, List.forall_mem_cons.2 ⟨subd6_3_884, List.forall_mem_cons.2 ⟨subd6_3_885, List.forall_mem_cons.2 ⟨subd6_3_886, List.forall_mem_cons.2 ⟨subd6_3_887, List.forall_mem_cons.2 ⟨subd6_3_888, List.forall_mem_cons.2 ⟨subd6_3_889, List.forall_mem_cons.2 ⟨subd6_3_890, List.forall_mem_cons.2 ⟨subd6_3_891, List.forall_mem_cons.2 ⟨subd6_3_892, List.forall_mem_cons.2 ⟨subd6_3_893, List.forall_mem_cons.2 ⟨subd6_3_894, List.forall_mem_cons.2 ⟨subd6_3_895, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_3_896 : subd6_3 [3, -2, 5] = true := by decide +kernel
theorem subd6_3_897 : subd6_3 [3, -2, 6] = true := by decide +kernel
theorem subd6_3_898 : subd6_3 [3, -2, 7] = true := by decide +kernel
theorem subd6_3_899 : subd6_3 [3, -1, -7] = true := by decide +kernel
theorem subd6_3_900 : subd6_3 [3, -1, -6] = true := by decide +kernel
theorem subd6_3_901 : subd6_3 [3, -1, -5] = true := by decide +kernel
theorem subd6_3_902 : subd6_3 [3, -1, -4] = true := by decide +kernel
theorem subd6_3_903 : subd6_3 [3, -1, -3] = true := by decide +kernel
theorem subd6_3_904 : subd6_3 [3, -1, -2] = true := by decide +kernel
theorem subd6_3_905 : subd6_3 [3, -1, -1] = true := by decide +kernel
theorem subd6_3_906 : subd6_3 [3, -1, 0] = true := by decide +kernel
theorem subd6_3_907 : subd6_3 [3, -1, 1] = true := by decide +kernel
theorem subd6_3_908 : subd6_3 [3, -1, 2] = true := by decide +kernel
theorem subd6_3_909 : subd6_3 [3, -1, 3] = true := by decide +kernel
theorem subd6_3_910 : subd6_3 [3, -1, 4] = true := by decide +kernel
theorem subd6_3_911 : subd6_3 [3, -1, 5] = true := by decide +kernel
theorem subd6_3_912 : subd6_3 [3, -1, 6] = true := by decide +kernel
theorem subd6_3_913 : subd6_3 [3, -1, 7] = true := by decide +kernel
theorem subd6_3_914 : subd6_3 [3, -1, 8] = true := by decide +kernel
theorem subd6_3_915 : subd6_3 [3, 0, -8] = true := by decide +kernel
theorem subd6_3_916 : subd6_3 [3, 0, -7] = true := by decide +kernel
theorem subd6_3_917 : subd6_3 [3, 0, -6] = true := by decide +kernel
theorem subd6_3_918 : subd6_3 [3, 0, -5] = true := by decide +kernel
theorem subd6_3_919 : subd6_3 [3, 0, -4] = true := by decide +kernel
theorem subd6_3_920 : subd6_3 [3, 0, -3] = true := by decide +kernel
theorem subd6_3_921 : subd6_3 [3, 0, -2] = true := by decide +kernel
theorem subd6_3_922 : subd6_3 [3, 0, -1] = true := by decide +kernel
theorem subd6_3_923 : subd6_3 [3, 0, 0] = true := by decide +kernel
theorem subd6_3_924 : subd6_3 [3, 0, 1] = true := by decide +kernel
theorem subd6_3_925 : subd6_3 [3, 0, 2] = true := by decide +kernel
theorem subd6_3_926 : subd6_3 [3, 0, 3] = true := by decide +kernel
theorem subd6_3_927 : subd6_3 [3, 0, 4] = true := by decide +kernel
theorem sbd6_3_28 : ∀ q ∈ blkd6_3_28, subd6_3 q = true := by
  unfold blkd6_3_28
  exact List.forall_mem_cons.2 ⟨subd6_3_896, List.forall_mem_cons.2 ⟨subd6_3_897, List.forall_mem_cons.2 ⟨subd6_3_898, List.forall_mem_cons.2 ⟨subd6_3_899, List.forall_mem_cons.2 ⟨subd6_3_900, List.forall_mem_cons.2 ⟨subd6_3_901, List.forall_mem_cons.2 ⟨subd6_3_902, List.forall_mem_cons.2 ⟨subd6_3_903, List.forall_mem_cons.2 ⟨subd6_3_904, List.forall_mem_cons.2 ⟨subd6_3_905, List.forall_mem_cons.2 ⟨subd6_3_906, List.forall_mem_cons.2 ⟨subd6_3_907, List.forall_mem_cons.2 ⟨subd6_3_908, List.forall_mem_cons.2 ⟨subd6_3_909, List.forall_mem_cons.2 ⟨subd6_3_910, List.forall_mem_cons.2 ⟨subd6_3_911, List.forall_mem_cons.2 ⟨subd6_3_912, List.forall_mem_cons.2 ⟨subd6_3_913, List.forall_mem_cons.2 ⟨subd6_3_914, List.forall_mem_cons.2 ⟨subd6_3_915, List.forall_mem_cons.2 ⟨subd6_3_916, List.forall_mem_cons.2 ⟨subd6_3_917, List.forall_mem_cons.2 ⟨subd6_3_918, List.forall_mem_cons.2 ⟨subd6_3_919, List.forall_mem_cons.2 ⟨subd6_3_920, List.forall_mem_cons.2 ⟨subd6_3_921, List.forall_mem_cons.2 ⟨subd6_3_922, List.forall_mem_cons.2 ⟨subd6_3_923, List.forall_mem_cons.2 ⟨subd6_3_924, List.forall_mem_cons.2 ⟨subd6_3_925, List.forall_mem_cons.2 ⟨subd6_3_926, List.forall_mem_cons.2 ⟨subd6_3_927, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_3_928 : subd6_3 [3, 0, 5] = true := by decide +kernel
theorem subd6_3_929 : subd6_3 [3, 0, 6] = true := by decide +kernel
theorem subd6_3_930 : subd6_3 [3, 0, 7] = true := by decide +kernel
theorem subd6_3_931 : subd6_3 [3, 0, 8] = true := by decide +kernel
theorem subd6_3_932 : subd6_3 [3, 1, -8] = true := by decide +kernel
theorem subd6_3_933 : subd6_3 [3, 1, -7] = true := by decide +kernel
theorem subd6_3_934 : subd6_3 [3, 1, -6] = true := by decide +kernel
theorem subd6_3_935 : subd6_3 [3, 1, -5] = true := by decide +kernel
theorem subd6_3_936 : subd6_3 [3, 1, -4] = true := by decide +kernel
theorem subd6_3_937 : subd6_3 [3, 1, -3] = true := by decide +kernel
theorem subd6_3_938 : subd6_3 [3, 1, -2] = true := by decide +kernel
theorem subd6_3_939 : subd6_3 [3, 1, -1] = true := by decide +kernel
theorem subd6_3_940 : subd6_3 [3, 1, 0] = true := by decide +kernel
theorem subd6_3_941 : subd6_3 [3, 1, 1] = true := by decide +kernel
theorem subd6_3_942 : subd6_3 [3, 1, 2] = true := by decide +kernel
theorem subd6_3_943 : subd6_3 [3, 1, 3] = true := by decide +kernel
theorem subd6_3_944 : subd6_3 [3, 1, 4] = true := by decide +kernel
theorem subd6_3_945 : subd6_3 [3, 1, 5] = true := by decide +kernel
theorem subd6_3_946 : subd6_3 [3, 1, 6] = true := by decide +kernel
theorem subd6_3_947 : subd6_3 [3, 1, 7] = true := by decide +kernel
theorem subd6_3_948 : subd6_3 [3, 2, -8] = true := by decide +kernel
theorem subd6_3_949 : subd6_3 [3, 2, -7] = true := by decide +kernel
theorem subd6_3_950 : subd6_3 [3, 2, -6] = true := by decide +kernel
theorem subd6_3_951 : subd6_3 [3, 2, -5] = true := by decide +kernel
theorem subd6_3_952 : subd6_3 [3, 2, -4] = true := by decide +kernel
theorem subd6_3_953 : subd6_3 [3, 2, -3] = true := by decide +kernel
theorem subd6_3_954 : subd6_3 [3, 2, -2] = true := by decide +kernel
theorem subd6_3_955 : subd6_3 [3, 2, -1] = true := by decide +kernel
theorem subd6_3_956 : subd6_3 [3, 2, 0] = true := by decide +kernel
theorem subd6_3_957 : subd6_3 [3, 2, 1] = true := by decide +kernel
theorem subd6_3_958 : subd6_3 [3, 2, 2] = true := by decide +kernel
theorem subd6_3_959 : subd6_3 [3, 2, 3] = true := by decide +kernel
theorem sbd6_3_29 : ∀ q ∈ blkd6_3_29, subd6_3 q = true := by
  unfold blkd6_3_29
  exact List.forall_mem_cons.2 ⟨subd6_3_928, List.forall_mem_cons.2 ⟨subd6_3_929, List.forall_mem_cons.2 ⟨subd6_3_930, List.forall_mem_cons.2 ⟨subd6_3_931, List.forall_mem_cons.2 ⟨subd6_3_932, List.forall_mem_cons.2 ⟨subd6_3_933, List.forall_mem_cons.2 ⟨subd6_3_934, List.forall_mem_cons.2 ⟨subd6_3_935, List.forall_mem_cons.2 ⟨subd6_3_936, List.forall_mem_cons.2 ⟨subd6_3_937, List.forall_mem_cons.2 ⟨subd6_3_938, List.forall_mem_cons.2 ⟨subd6_3_939, List.forall_mem_cons.2 ⟨subd6_3_940, List.forall_mem_cons.2 ⟨subd6_3_941, List.forall_mem_cons.2 ⟨subd6_3_942, List.forall_mem_cons.2 ⟨subd6_3_943, List.forall_mem_cons.2 ⟨subd6_3_944, List.forall_mem_cons.2 ⟨subd6_3_945, List.forall_mem_cons.2 ⟨subd6_3_946, List.forall_mem_cons.2 ⟨subd6_3_947, List.forall_mem_cons.2 ⟨subd6_3_948, List.forall_mem_cons.2 ⟨subd6_3_949, List.forall_mem_cons.2 ⟨subd6_3_950, List.forall_mem_cons.2 ⟨subd6_3_951, List.forall_mem_cons.2 ⟨subd6_3_952, List.forall_mem_cons.2 ⟨subd6_3_953, List.forall_mem_cons.2 ⟨subd6_3_954, List.forall_mem_cons.2 ⟨subd6_3_955, List.forall_mem_cons.2 ⟨subd6_3_956, List.forall_mem_cons.2 ⟨subd6_3_957, List.forall_mem_cons.2 ⟨subd6_3_958, List.forall_mem_cons.2 ⟨subd6_3_959, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_3_960 : subd6_3 [3, 2, 4] = true := by decide +kernel
theorem subd6_3_961 : subd6_3 [3, 2, 5] = true := by decide +kernel
theorem subd6_3_962 : subd6_3 [3, 2, 6] = true := by decide +kernel
theorem subd6_3_963 : subd6_3 [3, 2, 7] = true := by decide +kernel
theorem subd6_3_964 : subd6_3 [3, 3, -8] = true := by decide +kernel
theorem subd6_3_965 : subd6_3 [3, 3, -7] = true := by decide +kernel
theorem subd6_3_966 : subd6_3 [3, 3, -6] = true := by decide +kernel
theorem subd6_3_967 : subd6_3 [3, 3, -5] = true := by decide +kernel
theorem subd6_3_968 : subd6_3 [3, 3, -4] = true := by decide +kernel
theorem subd6_3_969 : subd6_3 [3, 3, -3] = true := by decide +kernel
theorem subd6_3_970 : subd6_3 [3, 3, -2] = true := by decide +kernel
theorem subd6_3_971 : subd6_3 [3, 3, -1] = true := by decide +kernel
theorem subd6_3_972 : subd6_3 [3, 3, 0] = true := by decide +kernel
theorem subd6_3_973 : subd6_3 [3, 3, 1] = true := by decide +kernel
theorem subd6_3_974 : subd6_3 [3, 3, 2] = true := by decide +kernel
theorem subd6_3_975 : subd6_3 [3, 3, 3] = true := by decide +kernel
theorem subd6_3_976 : subd6_3 [3, 3, 4] = true := by decide +kernel
theorem subd6_3_977 : subd6_3 [3, 3, 5] = true := by decide +kernel
theorem subd6_3_978 : subd6_3 [3, 3, 6] = true := by decide +kernel
theorem subd6_3_979 : subd6_3 [3, 4] = true := by decide +kernel
theorem subd6_3_980 : subd6_3 [3, 5] = true := by decide +kernel
theorem subd6_3_981 : subd6_3 [4, -4] = true := by decide +kernel
theorem subd6_3_982 : subd6_3 [4, -3] = true := by decide +kernel
theorem subd6_3_983 : subd6_3 [4, -2] = true := by decide +kernel
theorem subd6_3_984 : subd6_3 [4, -1] = true := by decide +kernel
theorem subd6_3_985 : subd6_3 [4, 0, -6] = true := by decide +kernel
theorem subd6_3_986 : subd6_3 [4, 0, -5] = true := by decide +kernel
theorem subd6_3_987 : subd6_3 [4, 0, -4] = true := by decide +kernel
theorem subd6_3_988 : subd6_3 [4, 0, -3] = true := by decide +kernel
theorem subd6_3_989 : subd6_3 [4, 0, -2] = true := by decide +kernel
theorem subd6_3_990 : subd6_3 [4, 0, -1] = true := by decide +kernel
theorem subd6_3_991 : subd6_3 [4, 0, 0] = true := by decide +kernel
theorem sbd6_3_30 : ∀ q ∈ blkd6_3_30, subd6_3 q = true := by
  unfold blkd6_3_30
  exact List.forall_mem_cons.2 ⟨subd6_3_960, List.forall_mem_cons.2 ⟨subd6_3_961, List.forall_mem_cons.2 ⟨subd6_3_962, List.forall_mem_cons.2 ⟨subd6_3_963, List.forall_mem_cons.2 ⟨subd6_3_964, List.forall_mem_cons.2 ⟨subd6_3_965, List.forall_mem_cons.2 ⟨subd6_3_966, List.forall_mem_cons.2 ⟨subd6_3_967, List.forall_mem_cons.2 ⟨subd6_3_968, List.forall_mem_cons.2 ⟨subd6_3_969, List.forall_mem_cons.2 ⟨subd6_3_970, List.forall_mem_cons.2 ⟨subd6_3_971, List.forall_mem_cons.2 ⟨subd6_3_972, List.forall_mem_cons.2 ⟨subd6_3_973, List.forall_mem_cons.2 ⟨subd6_3_974, List.forall_mem_cons.2 ⟨subd6_3_975, List.forall_mem_cons.2 ⟨subd6_3_976, List.forall_mem_cons.2 ⟨subd6_3_977, List.forall_mem_cons.2 ⟨subd6_3_978, List.forall_mem_cons.2 ⟨subd6_3_979, List.forall_mem_cons.2 ⟨subd6_3_980, List.forall_mem_cons.2 ⟨subd6_3_981, List.forall_mem_cons.2 ⟨subd6_3_982, List.forall_mem_cons.2 ⟨subd6_3_983, List.forall_mem_cons.2 ⟨subd6_3_984, List.forall_mem_cons.2 ⟨subd6_3_985, List.forall_mem_cons.2 ⟨subd6_3_986, List.forall_mem_cons.2 ⟨subd6_3_987, List.forall_mem_cons.2 ⟨subd6_3_988, List.forall_mem_cons.2 ⟨subd6_3_989, List.forall_mem_cons.2 ⟨subd6_3_990, List.forall_mem_cons.2 ⟨subd6_3_991, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_3_992 : subd6_3 [4, 0, 1] = true := by decide +kernel
theorem subd6_3_993 : subd6_3 [4, 0, 2] = true := by decide +kernel
theorem subd6_3_994 : subd6_3 [4, 0, 3] = true := by decide +kernel
theorem subd6_3_995 : subd6_3 [4, 0, 4] = true := by decide +kernel
theorem subd6_3_996 : subd6_3 [4, 0, 5] = true := by decide +kernel
theorem subd6_3_997 : subd6_3 [4, 0, 6] = true := by decide +kernel
theorem subd6_3_998 : subd6_3 [4, 0, 7] = true := by decide +kernel
theorem subd6_3_999 : subd6_3 [4, 1, -7] = true := by decide +kernel
theorem subd6_3_1000 : subd6_3 [4, 1, -6] = true := by decide +kernel
theorem subd6_3_1001 : subd6_3 [4, 1, -5] = true := by decide +kernel
theorem subd6_3_1002 : subd6_3 [4, 1, -4] = true := by decide +kernel
theorem subd6_3_1003 : subd6_3 [4, 1, -3] = true := by decide +kernel
theorem subd6_3_1004 : subd6_3 [4, 1, -2] = true := by decide +kernel
theorem subd6_3_1005 : subd6_3 [4, 1, -1] = true := by decide +kernel
theorem subd6_3_1006 : subd6_3 [4, 1, 0] = true := by decide +kernel
theorem subd6_3_1007 : subd6_3 [4, 1, 1] = true := by decide +kernel
theorem subd6_3_1008 : subd6_3 [4, 1, 2] = true := by decide +kernel
theorem subd6_3_1009 : subd6_3 [4, 1, 3] = true := by decide +kernel
theorem subd6_3_1010 : subd6_3 [4, 1, 4] = true := by decide +kernel
theorem subd6_3_1011 : subd6_3 [4, 1, 5] = true := by decide +kernel
theorem subd6_3_1012 : subd6_3 [4, 1, 6] = true := by decide +kernel
theorem subd6_3_1013 : subd6_3 [4, 2] = true := by decide +kernel
theorem subd6_3_1014 : subd6_3 [4, 3] = true := by decide +kernel
theorem subd6_3_1015 : subd6_3 [4, 4] = true := by decide +kernel
theorem subd6_3_1016 : subd6_3 [5, -3] = true := by decide +kernel
theorem subd6_3_1017 : subd6_3 [5, -2] = true := by decide +kernel
theorem subd6_3_1018 : subd6_3 [5, -1] = true := by decide +kernel
theorem subd6_3_1019 : subd6_3 [5, 0] = true := by decide +kernel
theorem subd6_3_1020 : subd6_3 [5, 1] = true := by decide +kernel
theorem subd6_3_1021 : subd6_3 [5, 2] = true := by decide +kernel
theorem subd6_3_1022 : subd6_3 [5, 3] = true := by decide +kernel
theorem sbd6_3_31 : ∀ q ∈ blkd6_3_31, subd6_3 q = true := by
  unfold blkd6_3_31
  exact List.forall_mem_cons.2 ⟨subd6_3_992, List.forall_mem_cons.2 ⟨subd6_3_993, List.forall_mem_cons.2 ⟨subd6_3_994, List.forall_mem_cons.2 ⟨subd6_3_995, List.forall_mem_cons.2 ⟨subd6_3_996, List.forall_mem_cons.2 ⟨subd6_3_997, List.forall_mem_cons.2 ⟨subd6_3_998, List.forall_mem_cons.2 ⟨subd6_3_999, List.forall_mem_cons.2 ⟨subd6_3_1000, List.forall_mem_cons.2 ⟨subd6_3_1001, List.forall_mem_cons.2 ⟨subd6_3_1002, List.forall_mem_cons.2 ⟨subd6_3_1003, List.forall_mem_cons.2 ⟨subd6_3_1004, List.forall_mem_cons.2 ⟨subd6_3_1005, List.forall_mem_cons.2 ⟨subd6_3_1006, List.forall_mem_cons.2 ⟨subd6_3_1007, List.forall_mem_cons.2 ⟨subd6_3_1008, List.forall_mem_cons.2 ⟨subd6_3_1009, List.forall_mem_cons.2 ⟨subd6_3_1010, List.forall_mem_cons.2 ⟨subd6_3_1011, List.forall_mem_cons.2 ⟨subd6_3_1012, List.forall_mem_cons.2 ⟨subd6_3_1013, List.forall_mem_cons.2 ⟨subd6_3_1014, List.forall_mem_cons.2 ⟨subd6_3_1015, List.forall_mem_cons.2 ⟨subd6_3_1016, List.forall_mem_cons.2 ⟨subd6_3_1017, List.forall_mem_cons.2 ⟨subd6_3_1018, List.forall_mem_cons.2 ⟨subd6_3_1019, List.forall_mem_cons.2 ⟨subd6_3_1020, List.forall_mem_cons.2 ⟨subd6_3_1021, List.forall_mem_cons.2 ⟨subd6_3_1022, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_4 : ldCheck G d6_4.U d6_4.ms ldd6_4 = true := by decide +kernel
theorem pre_okd6_4 : subPre G cell6 d6_4 = true := by decide +kernel
theorem subd6_4_0 : subd6_4 [-6] = true := by decide +kernel
theorem subd6_4_1 : subd6_4 [-5, -6] = true := by decide +kernel
theorem subd6_4_2 : subd6_4 [-5, -5] = true := by decide +kernel
theorem subd6_4_3 : subd6_4 [-5, -4] = true := by decide +kernel
theorem subd6_4_4 : subd6_4 [-5, -3] = true := by decide +kernel
theorem subd6_4_5 : subd6_4 [-5, -2] = true := by decide +kernel
theorem subd6_4_6 : subd6_4 [-5, -1] = true := by decide +kernel
theorem subd6_4_7 : subd6_4 [-5, 0] = true := by decide +kernel
theorem subd6_4_8 : subd6_4 [-5, 1] = true := by decide +kernel
theorem subd6_4_9 : subd6_4 [-5, 2] = true := by decide +kernel
theorem subd6_4_10 : subd6_4 [-5, 3] = true := by decide +kernel
theorem subd6_4_11 : subd6_4 [-4, -7] = true := by decide +kernel
theorem subd6_4_12 : subd6_4 [-4, -6] = true := by decide +kernel
theorem subd6_4_13 : subd6_4 [-4, -5] = true := by decide +kernel
theorem subd6_4_14 : subd6_4 [-4, -4] = true := by decide +kernel
theorem subd6_4_15 : subd6_4 [-4, -3] = true := by decide +kernel
theorem subd6_4_16 : subd6_4 [-4, -2] = true := by decide +kernel
theorem subd6_4_17 : subd6_4 [-4, -1] = true := by decide +kernel
theorem subd6_4_18 : subd6_4 [-4, 0] = true := by decide +kernel
theorem subd6_4_19 : subd6_4 [-4, 1] = true := by decide +kernel
theorem subd6_4_20 : subd6_4 [-4, 2] = true := by decide +kernel
theorem subd6_4_21 : subd6_4 [-4, 3] = true := by decide +kernel
theorem subd6_4_22 : subd6_4 [-4, 4] = true := by decide +kernel
theorem subd6_4_23 : subd6_4 [-4, 5] = true := by decide +kernel
theorem subd6_4_24 : subd6_4 [-3, -7] = true := by decide +kernel
theorem subd6_4_25 : subd6_4 [-3, -6] = true := by decide +kernel
theorem subd6_4_26 : subd6_4 [-3, -5] = true := by decide +kernel
theorem subd6_4_27 : subd6_4 [-3, -4] = true := by decide +kernel
theorem subd6_4_28 : subd6_4 [-3, -3] = true := by decide +kernel
theorem subd6_4_29 : subd6_4 [-3, -2] = true := by decide +kernel
theorem subd6_4_30 : subd6_4 [-3, -1] = true := by decide +kernel
theorem subd6_4_31 : subd6_4 [-3, 0] = true := by decide +kernel
theorem sbd6_4_0 : ∀ q ∈ blkd6_4_0, subd6_4 q = true := by
  unfold blkd6_4_0
  exact List.forall_mem_cons.2 ⟨subd6_4_0, List.forall_mem_cons.2 ⟨subd6_4_1, List.forall_mem_cons.2 ⟨subd6_4_2, List.forall_mem_cons.2 ⟨subd6_4_3, List.forall_mem_cons.2 ⟨subd6_4_4, List.forall_mem_cons.2 ⟨subd6_4_5, List.forall_mem_cons.2 ⟨subd6_4_6, List.forall_mem_cons.2 ⟨subd6_4_7, List.forall_mem_cons.2 ⟨subd6_4_8, List.forall_mem_cons.2 ⟨subd6_4_9, List.forall_mem_cons.2 ⟨subd6_4_10, List.forall_mem_cons.2 ⟨subd6_4_11, List.forall_mem_cons.2 ⟨subd6_4_12, List.forall_mem_cons.2 ⟨subd6_4_13, List.forall_mem_cons.2 ⟨subd6_4_14, List.forall_mem_cons.2 ⟨subd6_4_15, List.forall_mem_cons.2 ⟨subd6_4_16, List.forall_mem_cons.2 ⟨subd6_4_17, List.forall_mem_cons.2 ⟨subd6_4_18, List.forall_mem_cons.2 ⟨subd6_4_19, List.forall_mem_cons.2 ⟨subd6_4_20, List.forall_mem_cons.2 ⟨subd6_4_21, List.forall_mem_cons.2 ⟨subd6_4_22, List.forall_mem_cons.2 ⟨subd6_4_23, List.forall_mem_cons.2 ⟨subd6_4_24, List.forall_mem_cons.2 ⟨subd6_4_25, List.forall_mem_cons.2 ⟨subd6_4_26, List.forall_mem_cons.2 ⟨subd6_4_27, List.forall_mem_cons.2 ⟨subd6_4_28, List.forall_mem_cons.2 ⟨subd6_4_29, List.forall_mem_cons.2 ⟨subd6_4_30, List.forall_mem_cons.2 ⟨subd6_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C135
