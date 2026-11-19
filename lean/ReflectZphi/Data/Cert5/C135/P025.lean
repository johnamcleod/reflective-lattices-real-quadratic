import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_3_832 : subd7_3 [2, 0, 7] = true := by decide +kernel
theorem subd7_3_833 : subd7_3 [2, 0, 8] = true := by decide +kernel
theorem subd7_3_834 : subd7_3 [2, 1, -7] = true := by decide +kernel
theorem subd7_3_835 : subd7_3 [2, 1, -6] = true := by decide +kernel
theorem subd7_3_836 : subd7_3 [2, 1, -5] = true := by decide +kernel
theorem subd7_3_837 : subd7_3 [2, 1, -4] = true := by decide +kernel
theorem subd7_3_838 : subd7_3 [2, 1, -3] = true := by decide +kernel
theorem subd7_3_839 : subd7_3 [2, 1, -2] = true := by decide +kernel
theorem subd7_3_840 : subd7_3 [2, 1, -1] = true := by decide +kernel
theorem subd7_3_841 : subd7_3 [2, 1, 0] = true := by decide +kernel
theorem subd7_3_842 : subd7_3 [2, 1, 1] = true := by decide +kernel
theorem subd7_3_843 : subd7_3 [2, 1, 2] = true := by decide +kernel
theorem subd7_3_844 : subd7_3 [2, 1, 3] = true := by decide +kernel
theorem subd7_3_845 : subd7_3 [2, 1, 4] = true := by decide +kernel
theorem subd7_3_846 : subd7_3 [2, 1, 5] = true := by decide +kernel
theorem subd7_3_847 : subd7_3 [2, 1, 6] = true := by decide +kernel
theorem subd7_3_848 : subd7_3 [2, 1, 7] = true := by decide +kernel
theorem subd7_3_849 : subd7_3 [2, 1, 8] = true := by decide +kernel
theorem subd7_3_850 : subd7_3 [2, 2, -7] = true := by decide +kernel
theorem subd7_3_851 : subd7_3 [2, 2, -6] = true := by decide +kernel
theorem subd7_3_852 : subd7_3 [2, 2, -5] = true := by decide +kernel
theorem subd7_3_853 : subd7_3 [2, 2, -4] = true := by decide +kernel
theorem subd7_3_854 : subd7_3 [2, 2, -3] = true := by decide +kernel
theorem subd7_3_855 : subd7_3 [2, 2, -2] = true := by decide +kernel
theorem subd7_3_856 : subd7_3 [2, 2, -1] = true := by decide +kernel
theorem subd7_3_857 : subd7_3 [2, 2, 0] = true := by decide +kernel
theorem subd7_3_858 : subd7_3 [2, 2, 1] = true := by decide +kernel
theorem subd7_3_859 : subd7_3 [2, 2, 2] = true := by decide +kernel
theorem subd7_3_860 : subd7_3 [2, 2, 3] = true := by decide +kernel
theorem subd7_3_861 : subd7_3 [2, 2, 4] = true := by decide +kernel
theorem subd7_3_862 : subd7_3 [2, 2, 5] = true := by decide +kernel
theorem subd7_3_863 : subd7_3 [2, 2, 6] = true := by decide +kernel
theorem sbd7_3_26 : ∀ q ∈ blkd7_3_26, subd7_3 q = true := by
  unfold blkd7_3_26
  exact List.forall_mem_cons.2 ⟨subd7_3_832, List.forall_mem_cons.2 ⟨subd7_3_833, List.forall_mem_cons.2 ⟨subd7_3_834, List.forall_mem_cons.2 ⟨subd7_3_835, List.forall_mem_cons.2 ⟨subd7_3_836, List.forall_mem_cons.2 ⟨subd7_3_837, List.forall_mem_cons.2 ⟨subd7_3_838, List.forall_mem_cons.2 ⟨subd7_3_839, List.forall_mem_cons.2 ⟨subd7_3_840, List.forall_mem_cons.2 ⟨subd7_3_841, List.forall_mem_cons.2 ⟨subd7_3_842, List.forall_mem_cons.2 ⟨subd7_3_843, List.forall_mem_cons.2 ⟨subd7_3_844, List.forall_mem_cons.2 ⟨subd7_3_845, List.forall_mem_cons.2 ⟨subd7_3_846, List.forall_mem_cons.2 ⟨subd7_3_847, List.forall_mem_cons.2 ⟨subd7_3_848, List.forall_mem_cons.2 ⟨subd7_3_849, List.forall_mem_cons.2 ⟨subd7_3_850, List.forall_mem_cons.2 ⟨subd7_3_851, List.forall_mem_cons.2 ⟨subd7_3_852, List.forall_mem_cons.2 ⟨subd7_3_853, List.forall_mem_cons.2 ⟨subd7_3_854, List.forall_mem_cons.2 ⟨subd7_3_855, List.forall_mem_cons.2 ⟨subd7_3_856, List.forall_mem_cons.2 ⟨subd7_3_857, List.forall_mem_cons.2 ⟨subd7_3_858, List.forall_mem_cons.2 ⟨subd7_3_859, List.forall_mem_cons.2 ⟨subd7_3_860, List.forall_mem_cons.2 ⟨subd7_3_861, List.forall_mem_cons.2 ⟨subd7_3_862, List.forall_mem_cons.2 ⟨subd7_3_863, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_864 : subd7_3 [2, 2, 7] = true := by decide +kernel
theorem subd7_3_865 : subd7_3 [2, 2, 8] = true := by decide +kernel
theorem subd7_3_866 : subd7_3 [2, 3, -7] = true := by decide +kernel
theorem subd7_3_867 : subd7_3 [2, 3, -6] = true := by decide +kernel
theorem subd7_3_868 : subd7_3 [2, 3, -5] = true := by decide +kernel
theorem subd7_3_869 : subd7_3 [2, 3, -4] = true := by decide +kernel
theorem subd7_3_870 : subd7_3 [2, 3, -3] = true := by decide +kernel
theorem subd7_3_871 : subd7_3 [2, 3, -2] = true := by decide +kernel
theorem subd7_3_872 : subd7_3 [2, 3, -1] = true := by decide +kernel
theorem subd7_3_873 : subd7_3 [2, 3, 0] = true := by decide +kernel
theorem subd7_3_874 : subd7_3 [2, 3, 1] = true := by decide +kernel
theorem subd7_3_875 : subd7_3 [2, 3, 2] = true := by decide +kernel
theorem subd7_3_876 : subd7_3 [2, 3, 3] = true := by decide +kernel
theorem subd7_3_877 : subd7_3 [2, 3, 4] = true := by decide +kernel
theorem subd7_3_878 : subd7_3 [2, 3, 5] = true := by decide +kernel
theorem subd7_3_879 : subd7_3 [2, 3, 6] = true := by decide +kernel
theorem subd7_3_880 : subd7_3 [2, 3, 7] = true := by decide +kernel
theorem subd7_3_881 : subd7_3 [2, 3, 8] = true := by decide +kernel
theorem subd7_3_882 : subd7_3 [2, 4, -6] = true := by decide +kernel
theorem subd7_3_883 : subd7_3 [2, 4, -5] = true := by decide +kernel
theorem subd7_3_884 : subd7_3 [2, 4, -4] = true := by decide +kernel
theorem subd7_3_885 : subd7_3 [2, 4, -3] = true := by decide +kernel
theorem subd7_3_886 : subd7_3 [2, 4, -2] = true := by decide +kernel
theorem subd7_3_887 : subd7_3 [2, 4, -1] = true := by decide +kernel
theorem subd7_3_888 : subd7_3 [2, 4, 0] = true := by decide +kernel
theorem subd7_3_889 : subd7_3 [2, 4, 1] = true := by decide +kernel
theorem subd7_3_890 : subd7_3 [2, 4, 2] = true := by decide +kernel
theorem subd7_3_891 : subd7_3 [2, 4, 3] = true := by decide +kernel
theorem subd7_3_892 : subd7_3 [2, 4, 4] = true := by decide +kernel
theorem subd7_3_893 : subd7_3 [2, 4, 5] = true := by decide +kernel
theorem subd7_3_894 : subd7_3 [2, 4, 6] = true := by decide +kernel
theorem subd7_3_895 : subd7_3 [2, 4, 7] = true := by decide +kernel
theorem sbd7_3_27 : ∀ q ∈ blkd7_3_27, subd7_3 q = true := by
  unfold blkd7_3_27
  exact List.forall_mem_cons.2 ⟨subd7_3_864, List.forall_mem_cons.2 ⟨subd7_3_865, List.forall_mem_cons.2 ⟨subd7_3_866, List.forall_mem_cons.2 ⟨subd7_3_867, List.forall_mem_cons.2 ⟨subd7_3_868, List.forall_mem_cons.2 ⟨subd7_3_869, List.forall_mem_cons.2 ⟨subd7_3_870, List.forall_mem_cons.2 ⟨subd7_3_871, List.forall_mem_cons.2 ⟨subd7_3_872, List.forall_mem_cons.2 ⟨subd7_3_873, List.forall_mem_cons.2 ⟨subd7_3_874, List.forall_mem_cons.2 ⟨subd7_3_875, List.forall_mem_cons.2 ⟨subd7_3_876, List.forall_mem_cons.2 ⟨subd7_3_877, List.forall_mem_cons.2 ⟨subd7_3_878, List.forall_mem_cons.2 ⟨subd7_3_879, List.forall_mem_cons.2 ⟨subd7_3_880, List.forall_mem_cons.2 ⟨subd7_3_881, List.forall_mem_cons.2 ⟨subd7_3_882, List.forall_mem_cons.2 ⟨subd7_3_883, List.forall_mem_cons.2 ⟨subd7_3_884, List.forall_mem_cons.2 ⟨subd7_3_885, List.forall_mem_cons.2 ⟨subd7_3_886, List.forall_mem_cons.2 ⟨subd7_3_887, List.forall_mem_cons.2 ⟨subd7_3_888, List.forall_mem_cons.2 ⟨subd7_3_889, List.forall_mem_cons.2 ⟨subd7_3_890, List.forall_mem_cons.2 ⟨subd7_3_891, List.forall_mem_cons.2 ⟨subd7_3_892, List.forall_mem_cons.2 ⟨subd7_3_893, List.forall_mem_cons.2 ⟨subd7_3_894, List.forall_mem_cons.2 ⟨subd7_3_895, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_896 : subd7_3 [2, 5] = true := by decide +kernel
theorem subd7_3_897 : subd7_3 [2, 6] = true := by decide +kernel
theorem subd7_3_898 : subd7_3 [2, 7] = true := by decide +kernel
theorem subd7_3_899 : subd7_3 [3, -6] = true := by decide +kernel
theorem subd7_3_900 : subd7_3 [3, -5] = true := by decide +kernel
theorem subd7_3_901 : subd7_3 [3, -4] = true := by decide +kernel
theorem subd7_3_902 : subd7_3 [3, -3] = true := by decide +kernel
theorem subd7_3_903 : subd7_3 [3, -2, -6] = true := by decide +kernel
theorem subd7_3_904 : subd7_3 [3, -2, -5] = true := by decide +kernel
theorem subd7_3_905 : subd7_3 [3, -2, -4] = true := by decide +kernel
theorem subd7_3_906 : subd7_3 [3, -2, -3] = true := by decide +kernel
theorem subd7_3_907 : subd7_3 [3, -2, -2] = true := by decide +kernel
theorem subd7_3_908 : subd7_3 [3, -2, -1] = true := by decide +kernel
theorem subd7_3_909 : subd7_3 [3, -2, 0] = true := by decide +kernel
theorem subd7_3_910 : subd7_3 [3, -2, 1] = true := by decide +kernel
theorem subd7_3_911 : subd7_3 [3, -2, 2] = true := by decide +kernel
theorem subd7_3_912 : subd7_3 [3, -2, 3] = true := by decide +kernel
theorem subd7_3_913 : subd7_3 [3, -2, 4] = true := by decide +kernel
theorem subd7_3_914 : subd7_3 [3, -2, 5] = true := by decide +kernel
theorem subd7_3_915 : subd7_3 [3, -2, 6] = true := by decide +kernel
theorem subd7_3_916 : subd7_3 [3, -2, 7] = true := by decide +kernel
theorem subd7_3_917 : subd7_3 [3, -1, -6] = true := by decide +kernel
theorem subd7_3_918 : subd7_3 [3, -1, -5] = true := by decide +kernel
theorem subd7_3_919 : subd7_3 [3, -1, -4] = true := by decide +kernel
theorem subd7_3_920 : subd7_3 [3, -1, -3] = true := by decide +kernel
theorem subd7_3_921 : subd7_3 [3, -1, -2] = true := by decide +kernel
theorem subd7_3_922 : subd7_3 [3, -1, -1] = true := by decide +kernel
theorem subd7_3_923 : subd7_3 [3, -1, 0] = true := by decide +kernel
theorem subd7_3_924 : subd7_3 [3, -1, 1] = true := by decide +kernel
theorem subd7_3_925 : subd7_3 [3, -1, 2] = true := by decide +kernel
theorem subd7_3_926 : subd7_3 [3, -1, 3] = true := by decide +kernel
theorem subd7_3_927 : subd7_3 [3, -1, 4] = true := by decide +kernel
theorem sbd7_3_28 : ∀ q ∈ blkd7_3_28, subd7_3 q = true := by
  unfold blkd7_3_28
  exact List.forall_mem_cons.2 ⟨subd7_3_896, List.forall_mem_cons.2 ⟨subd7_3_897, List.forall_mem_cons.2 ⟨subd7_3_898, List.forall_mem_cons.2 ⟨subd7_3_899, List.forall_mem_cons.2 ⟨subd7_3_900, List.forall_mem_cons.2 ⟨subd7_3_901, List.forall_mem_cons.2 ⟨subd7_3_902, List.forall_mem_cons.2 ⟨subd7_3_903, List.forall_mem_cons.2 ⟨subd7_3_904, List.forall_mem_cons.2 ⟨subd7_3_905, List.forall_mem_cons.2 ⟨subd7_3_906, List.forall_mem_cons.2 ⟨subd7_3_907, List.forall_mem_cons.2 ⟨subd7_3_908, List.forall_mem_cons.2 ⟨subd7_3_909, List.forall_mem_cons.2 ⟨subd7_3_910, List.forall_mem_cons.2 ⟨subd7_3_911, List.forall_mem_cons.2 ⟨subd7_3_912, List.forall_mem_cons.2 ⟨subd7_3_913, List.forall_mem_cons.2 ⟨subd7_3_914, List.forall_mem_cons.2 ⟨subd7_3_915, List.forall_mem_cons.2 ⟨subd7_3_916, List.forall_mem_cons.2 ⟨subd7_3_917, List.forall_mem_cons.2 ⟨subd7_3_918, List.forall_mem_cons.2 ⟨subd7_3_919, List.forall_mem_cons.2 ⟨subd7_3_920, List.forall_mem_cons.2 ⟨subd7_3_921, List.forall_mem_cons.2 ⟨subd7_3_922, List.forall_mem_cons.2 ⟨subd7_3_923, List.forall_mem_cons.2 ⟨subd7_3_924, List.forall_mem_cons.2 ⟨subd7_3_925, List.forall_mem_cons.2 ⟨subd7_3_926, List.forall_mem_cons.2 ⟨subd7_3_927, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_928 : subd7_3 [3, -1, 5] = true := by decide +kernel
theorem subd7_3_929 : subd7_3 [3, -1, 6] = true := by decide +kernel
theorem subd7_3_930 : subd7_3 [3, -1, 7] = true := by decide +kernel
theorem subd7_3_931 : subd7_3 [3, -1, 8] = true := by decide +kernel
theorem subd7_3_932 : subd7_3 [3, 0, -7] = true := by decide +kernel
theorem subd7_3_933 : subd7_3 [3, 0, -6] = true := by decide +kernel
theorem subd7_3_934 : subd7_3 [3, 0, -5] = true := by decide +kernel
theorem subd7_3_935 : subd7_3 [3, 0, -4] = true := by decide +kernel
theorem subd7_3_936 : subd7_3 [3, 0, -3] = true := by decide +kernel
theorem subd7_3_937 : subd7_3 [3, 0, -2] = true := by decide +kernel
theorem subd7_3_938 : subd7_3 [3, 0, -1] = true := by decide +kernel
theorem subd7_3_939 : subd7_3 [3, 0, 0] = true := by decide +kernel
theorem subd7_3_940 : subd7_3 [3, 0, 1] = true := by decide +kernel
theorem subd7_3_941 : subd7_3 [3, 0, 2] = true := by decide +kernel
theorem subd7_3_942 : subd7_3 [3, 0, 3] = true := by decide +kernel
theorem subd7_3_943 : subd7_3 [3, 0, 4] = true := by decide +kernel
theorem subd7_3_944 : subd7_3 [3, 0, 5] = true := by decide +kernel
theorem subd7_3_945 : subd7_3 [3, 0, 6] = true := by decide +kernel
theorem subd7_3_946 : subd7_3 [3, 0, 7] = true := by decide +kernel
theorem subd7_3_947 : subd7_3 [3, 0, 8] = true := by decide +kernel
theorem subd7_3_948 : subd7_3 [3, 1, -7] = true := by decide +kernel
theorem subd7_3_949 : subd7_3 [3, 1, -6] = true := by decide +kernel
theorem subd7_3_950 : subd7_3 [3, 1, -5] = true := by decide +kernel
theorem subd7_3_951 : subd7_3 [3, 1, -4] = true := by decide +kernel
theorem subd7_3_952 : subd7_3 [3, 1, -3] = true := by decide +kernel
theorem subd7_3_953 : subd7_3 [3, 1, -2] = true := by decide +kernel
theorem subd7_3_954 : subd7_3 [3, 1, -1] = true := by decide +kernel
theorem subd7_3_955 : subd7_3 [3, 1, 0] = true := by decide +kernel
theorem subd7_3_956 : subd7_3 [3, 1, 1] = true := by decide +kernel
theorem subd7_3_957 : subd7_3 [3, 1, 2] = true := by decide +kernel
theorem subd7_3_958 : subd7_3 [3, 1, 3] = true := by decide +kernel
theorem subd7_3_959 : subd7_3 [3, 1, 4] = true := by decide +kernel
theorem sbd7_3_29 : ∀ q ∈ blkd7_3_29, subd7_3 q = true := by
  unfold blkd7_3_29
  exact List.forall_mem_cons.2 ⟨subd7_3_928, List.forall_mem_cons.2 ⟨subd7_3_929, List.forall_mem_cons.2 ⟨subd7_3_930, List.forall_mem_cons.2 ⟨subd7_3_931, List.forall_mem_cons.2 ⟨subd7_3_932, List.forall_mem_cons.2 ⟨subd7_3_933, List.forall_mem_cons.2 ⟨subd7_3_934, List.forall_mem_cons.2 ⟨subd7_3_935, List.forall_mem_cons.2 ⟨subd7_3_936, List.forall_mem_cons.2 ⟨subd7_3_937, List.forall_mem_cons.2 ⟨subd7_3_938, List.forall_mem_cons.2 ⟨subd7_3_939, List.forall_mem_cons.2 ⟨subd7_3_940, List.forall_mem_cons.2 ⟨subd7_3_941, List.forall_mem_cons.2 ⟨subd7_3_942, List.forall_mem_cons.2 ⟨subd7_3_943, List.forall_mem_cons.2 ⟨subd7_3_944, List.forall_mem_cons.2 ⟨subd7_3_945, List.forall_mem_cons.2 ⟨subd7_3_946, List.forall_mem_cons.2 ⟨subd7_3_947, List.forall_mem_cons.2 ⟨subd7_3_948, List.forall_mem_cons.2 ⟨subd7_3_949, List.forall_mem_cons.2 ⟨subd7_3_950, List.forall_mem_cons.2 ⟨subd7_3_951, List.forall_mem_cons.2 ⟨subd7_3_952, List.forall_mem_cons.2 ⟨subd7_3_953, List.forall_mem_cons.2 ⟨subd7_3_954, List.forall_mem_cons.2 ⟨subd7_3_955, List.forall_mem_cons.2 ⟨subd7_3_956, List.forall_mem_cons.2 ⟨subd7_3_957, List.forall_mem_cons.2 ⟨subd7_3_958, List.forall_mem_cons.2 ⟨subd7_3_959, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_960 : subd7_3 [3, 1, 5] = true := by decide +kernel
theorem subd7_3_961 : subd7_3 [3, 1, 6] = true := by decide +kernel
theorem subd7_3_962 : subd7_3 [3, 1, 7] = true := by decide +kernel
theorem subd7_3_963 : subd7_3 [3, 1, 8] = true := by decide +kernel
theorem subd7_3_964 : subd7_3 [3, 2, -6] = true := by decide +kernel
theorem subd7_3_965 : subd7_3 [3, 2, -5] = true := by decide +kernel
theorem subd7_3_966 : subd7_3 [3, 2, -4] = true := by decide +kernel
theorem subd7_3_967 : subd7_3 [3, 2, -3] = true := by decide +kernel
theorem subd7_3_968 : subd7_3 [3, 2, -2] = true := by decide +kernel
theorem subd7_3_969 : subd7_3 [3, 2, -1] = true := by decide +kernel
theorem subd7_3_970 : subd7_3 [3, 2, 0] = true := by decide +kernel
theorem subd7_3_971 : subd7_3 [3, 2, 1] = true := by decide +kernel
theorem subd7_3_972 : subd7_3 [3, 2, 2] = true := by decide +kernel
theorem subd7_3_973 : subd7_3 [3, 2, 3] = true := by decide +kernel
theorem subd7_3_974 : subd7_3 [3, 2, 4] = true := by decide +kernel
theorem subd7_3_975 : subd7_3 [3, 2, 5] = true := by decide +kernel
theorem subd7_3_976 : subd7_3 [3, 2, 6] = true := by decide +kernel
theorem subd7_3_977 : subd7_3 [3, 2, 7] = true := by decide +kernel
theorem subd7_3_978 : subd7_3 [3, 2, 8] = true := by decide +kernel
theorem subd7_3_979 : subd7_3 [3, 3, -6] = true := by decide +kernel
theorem subd7_3_980 : subd7_3 [3, 3, -5] = true := by decide +kernel
theorem subd7_3_981 : subd7_3 [3, 3, -4] = true := by decide +kernel
theorem subd7_3_982 : subd7_3 [3, 3, -3] = true := by decide +kernel
theorem subd7_3_983 : subd7_3 [3, 3, -2] = true := by decide +kernel
theorem subd7_3_984 : subd7_3 [3, 3, -1] = true := by decide +kernel
theorem subd7_3_985 : subd7_3 [3, 3, 0] = true := by decide +kernel
theorem subd7_3_986 : subd7_3 [3, 3, 1] = true := by decide +kernel
theorem subd7_3_987 : subd7_3 [3, 3, 2] = true := by decide +kernel
theorem subd7_3_988 : subd7_3 [3, 3, 3] = true := by decide +kernel
theorem subd7_3_989 : subd7_3 [3, 3, 4] = true := by decide +kernel
theorem subd7_3_990 : subd7_3 [3, 3, 5] = true := by decide +kernel
theorem subd7_3_991 : subd7_3 [3, 3, 6] = true := by decide +kernel
theorem sbd7_3_30 : ∀ q ∈ blkd7_3_30, subd7_3 q = true := by
  unfold blkd7_3_30
  exact List.forall_mem_cons.2 ⟨subd7_3_960, List.forall_mem_cons.2 ⟨subd7_3_961, List.forall_mem_cons.2 ⟨subd7_3_962, List.forall_mem_cons.2 ⟨subd7_3_963, List.forall_mem_cons.2 ⟨subd7_3_964, List.forall_mem_cons.2 ⟨subd7_3_965, List.forall_mem_cons.2 ⟨subd7_3_966, List.forall_mem_cons.2 ⟨subd7_3_967, List.forall_mem_cons.2 ⟨subd7_3_968, List.forall_mem_cons.2 ⟨subd7_3_969, List.forall_mem_cons.2 ⟨subd7_3_970, List.forall_mem_cons.2 ⟨subd7_3_971, List.forall_mem_cons.2 ⟨subd7_3_972, List.forall_mem_cons.2 ⟨subd7_3_973, List.forall_mem_cons.2 ⟨subd7_3_974, List.forall_mem_cons.2 ⟨subd7_3_975, List.forall_mem_cons.2 ⟨subd7_3_976, List.forall_mem_cons.2 ⟨subd7_3_977, List.forall_mem_cons.2 ⟨subd7_3_978, List.forall_mem_cons.2 ⟨subd7_3_979, List.forall_mem_cons.2 ⟨subd7_3_980, List.forall_mem_cons.2 ⟨subd7_3_981, List.forall_mem_cons.2 ⟨subd7_3_982, List.forall_mem_cons.2 ⟨subd7_3_983, List.forall_mem_cons.2 ⟨subd7_3_984, List.forall_mem_cons.2 ⟨subd7_3_985, List.forall_mem_cons.2 ⟨subd7_3_986, List.forall_mem_cons.2 ⟨subd7_3_987, List.forall_mem_cons.2 ⟨subd7_3_988, List.forall_mem_cons.2 ⟨subd7_3_989, List.forall_mem_cons.2 ⟨subd7_3_990, List.forall_mem_cons.2 ⟨subd7_3_991, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_992 : subd7_3 [3, 3, 7] = true := by decide +kernel
theorem subd7_3_993 : subd7_3 [3, 3, 8] = true := by decide +kernel
theorem subd7_3_994 : subd7_3 [3, 4] = true := by decide +kernel
theorem subd7_3_995 : subd7_3 [3, 5] = true := by decide +kernel
theorem subd7_3_996 : subd7_3 [3, 6] = true := by decide +kernel
theorem subd7_3_997 : subd7_3 [4, -6] = true := by decide +kernel
theorem subd7_3_998 : subd7_3 [4, -5] = true := by decide +kernel
theorem subd7_3_999 : subd7_3 [4, -4] = true := by decide +kernel
theorem subd7_3_1000 : subd7_3 [4, -3] = true := by decide +kernel
theorem subd7_3_1001 : subd7_3 [4, -2] = true := by decide +kernel
theorem subd7_3_1002 : subd7_3 [4, -1, -5] = true := by decide +kernel
theorem subd7_3_1003 : subd7_3 [4, -1, -4] = true := by decide +kernel
theorem subd7_3_1004 : subd7_3 [4, -1, -3] = true := by decide +kernel
theorem subd7_3_1005 : subd7_3 [4, -1, -2] = true := by decide +kernel
theorem subd7_3_1006 : subd7_3 [4, -1, -1] = true := by decide +kernel
theorem subd7_3_1007 : subd7_3 [4, -1, 0] = true := by decide +kernel
theorem subd7_3_1008 : subd7_3 [4, -1, 1] = true := by decide +kernel
theorem subd7_3_1009 : subd7_3 [4, -1, 2] = true := by decide +kernel
theorem subd7_3_1010 : subd7_3 [4, -1, 3] = true := by decide +kernel
theorem subd7_3_1011 : subd7_3 [4, -1, 4] = true := by decide +kernel
theorem subd7_3_1012 : subd7_3 [4, -1, 5] = true := by decide +kernel
theorem subd7_3_1013 : subd7_3 [4, -1, 6] = true := by decide +kernel
theorem subd7_3_1014 : subd7_3 [4, -1, 7] = true := by decide +kernel
theorem subd7_3_1015 : subd7_3 [4, 0, -5] = true := by decide +kernel
theorem subd7_3_1016 : subd7_3 [4, 0, -4] = true := by decide +kernel
theorem subd7_3_1017 : subd7_3 [4, 0, -3] = true := by decide +kernel
theorem subd7_3_1018 : subd7_3 [4, 0, -2] = true := by decide +kernel
theorem subd7_3_1019 : subd7_3 [4, 0, -1] = true := by decide +kernel
theorem subd7_3_1020 : subd7_3 [4, 0, 0] = true := by decide +kernel
theorem subd7_3_1021 : subd7_3 [4, 0, 1] = true := by decide +kernel
theorem subd7_3_1022 : subd7_3 [4, 0, 2] = true := by decide +kernel
theorem subd7_3_1023 : subd7_3 [4, 0, 3] = true := by decide +kernel
theorem sbd7_3_31 : ∀ q ∈ blkd7_3_31, subd7_3 q = true := by
  unfold blkd7_3_31
  exact List.forall_mem_cons.2 ⟨subd7_3_992, List.forall_mem_cons.2 ⟨subd7_3_993, List.forall_mem_cons.2 ⟨subd7_3_994, List.forall_mem_cons.2 ⟨subd7_3_995, List.forall_mem_cons.2 ⟨subd7_3_996, List.forall_mem_cons.2 ⟨subd7_3_997, List.forall_mem_cons.2 ⟨subd7_3_998, List.forall_mem_cons.2 ⟨subd7_3_999, List.forall_mem_cons.2 ⟨subd7_3_1000, List.forall_mem_cons.2 ⟨subd7_3_1001, List.forall_mem_cons.2 ⟨subd7_3_1002, List.forall_mem_cons.2 ⟨subd7_3_1003, List.forall_mem_cons.2 ⟨subd7_3_1004, List.forall_mem_cons.2 ⟨subd7_3_1005, List.forall_mem_cons.2 ⟨subd7_3_1006, List.forall_mem_cons.2 ⟨subd7_3_1007, List.forall_mem_cons.2 ⟨subd7_3_1008, List.forall_mem_cons.2 ⟨subd7_3_1009, List.forall_mem_cons.2 ⟨subd7_3_1010, List.forall_mem_cons.2 ⟨subd7_3_1011, List.forall_mem_cons.2 ⟨subd7_3_1012, List.forall_mem_cons.2 ⟨subd7_3_1013, List.forall_mem_cons.2 ⟨subd7_3_1014, List.forall_mem_cons.2 ⟨subd7_3_1015, List.forall_mem_cons.2 ⟨subd7_3_1016, List.forall_mem_cons.2 ⟨subd7_3_1017, List.forall_mem_cons.2 ⟨subd7_3_1018, List.forall_mem_cons.2 ⟨subd7_3_1019, List.forall_mem_cons.2 ⟨subd7_3_1020, List.forall_mem_cons.2 ⟨subd7_3_1021, List.forall_mem_cons.2 ⟨subd7_3_1022, List.forall_mem_cons.2 ⟨subd7_3_1023, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_1024 : subd7_3 [4, 0, 4] = true := by decide +kernel
theorem subd7_3_1025 : subd7_3 [4, 0, 5] = true := by decide +kernel
theorem subd7_3_1026 : subd7_3 [4, 0, 6] = true := by decide +kernel
theorem subd7_3_1027 : subd7_3 [4, 0, 7] = true := by decide +kernel
theorem subd7_3_1028 : subd7_3 [4, 0, 8] = true := by decide +kernel
theorem subd7_3_1029 : subd7_3 [4, 1, -5] = true := by decide +kernel
theorem subd7_3_1030 : subd7_3 [4, 1, -4] = true := by decide +kernel
theorem subd7_3_1031 : subd7_3 [4, 1, -3] = true := by decide +kernel
theorem subd7_3_1032 : subd7_3 [4, 1, -2] = true := by decide +kernel
theorem subd7_3_1033 : subd7_3 [4, 1, -1] = true := by decide +kernel
theorem subd7_3_1034 : subd7_3 [4, 1, 0] = true := by decide +kernel
theorem subd7_3_1035 : subd7_3 [4, 1, 1] = true := by decide +kernel
theorem subd7_3_1036 : subd7_3 [4, 1, 2] = true := by decide +kernel
theorem subd7_3_1037 : subd7_3 [4, 1, 3] = true := by decide +kernel
theorem subd7_3_1038 : subd7_3 [4, 1, 4] = true := by decide +kernel
theorem subd7_3_1039 : subd7_3 [4, 1, 5] = true := by decide +kernel
theorem subd7_3_1040 : subd7_3 [4, 1, 6] = true := by decide +kernel
theorem subd7_3_1041 : subd7_3 [4, 1, 7] = true := by decide +kernel
theorem subd7_3_1042 : subd7_3 [4, 1, 8] = true := by decide +kernel
theorem subd7_3_1043 : subd7_3 [4, 2, -5] = true := by decide +kernel
theorem subd7_3_1044 : subd7_3 [4, 2, -4] = true := by decide +kernel
theorem subd7_3_1045 : subd7_3 [4, 2, -3] = true := by decide +kernel
theorem subd7_3_1046 : subd7_3 [4, 2, -2] = true := by decide +kernel
theorem subd7_3_1047 : subd7_3 [4, 2, -1] = true := by decide +kernel
theorem subd7_3_1048 : subd7_3 [4, 2, 0] = true := by decide +kernel
theorem subd7_3_1049 : subd7_3 [4, 2, 1] = true := by decide +kernel
theorem subd7_3_1050 : subd7_3 [4, 2, 2] = true := by decide +kernel
theorem subd7_3_1051 : subd7_3 [4, 2, 3] = true := by decide +kernel
theorem subd7_3_1052 : subd7_3 [4, 2, 4] = true := by decide +kernel
theorem subd7_3_1053 : subd7_3 [4, 2, 5] = true := by decide +kernel
theorem subd7_3_1054 : subd7_3 [4, 2, 6] = true := by decide +kernel
theorem subd7_3_1055 : subd7_3 [4, 2, 7] = true := by decide +kernel
theorem sbd7_3_32 : ∀ q ∈ blkd7_3_32, subd7_3 q = true := by
  unfold blkd7_3_32
  exact List.forall_mem_cons.2 ⟨subd7_3_1024, List.forall_mem_cons.2 ⟨subd7_3_1025, List.forall_mem_cons.2 ⟨subd7_3_1026, List.forall_mem_cons.2 ⟨subd7_3_1027, List.forall_mem_cons.2 ⟨subd7_3_1028, List.forall_mem_cons.2 ⟨subd7_3_1029, List.forall_mem_cons.2 ⟨subd7_3_1030, List.forall_mem_cons.2 ⟨subd7_3_1031, List.forall_mem_cons.2 ⟨subd7_3_1032, List.forall_mem_cons.2 ⟨subd7_3_1033, List.forall_mem_cons.2 ⟨subd7_3_1034, List.forall_mem_cons.2 ⟨subd7_3_1035, List.forall_mem_cons.2 ⟨subd7_3_1036, List.forall_mem_cons.2 ⟨subd7_3_1037, List.forall_mem_cons.2 ⟨subd7_3_1038, List.forall_mem_cons.2 ⟨subd7_3_1039, List.forall_mem_cons.2 ⟨subd7_3_1040, List.forall_mem_cons.2 ⟨subd7_3_1041, List.forall_mem_cons.2 ⟨subd7_3_1042, List.forall_mem_cons.2 ⟨subd7_3_1043, List.forall_mem_cons.2 ⟨subd7_3_1044, List.forall_mem_cons.2 ⟨subd7_3_1045, List.forall_mem_cons.2 ⟨subd7_3_1046, List.forall_mem_cons.2 ⟨subd7_3_1047, List.forall_mem_cons.2 ⟨subd7_3_1048, List.forall_mem_cons.2 ⟨subd7_3_1049, List.forall_mem_cons.2 ⟨subd7_3_1050, List.forall_mem_cons.2 ⟨subd7_3_1051, List.forall_mem_cons.2 ⟨subd7_3_1052, List.forall_mem_cons.2 ⟨subd7_3_1053, List.forall_mem_cons.2 ⟨subd7_3_1054, List.forall_mem_cons.2 ⟨subd7_3_1055, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_1056 : subd7_3 [4, 2, 8] = true := by decide +kernel
theorem subd7_3_1057 : subd7_3 [4, 3] = true := by decide +kernel
theorem subd7_3_1058 : subd7_3 [4, 4] = true := by decide +kernel
theorem subd7_3_1059 : subd7_3 [4, 5] = true := by decide +kernel
theorem subd7_3_1060 : subd7_3 [4, 6] = true := by decide +kernel
theorem subd7_3_1061 : subd7_3 [5, -4] = true := by decide +kernel
theorem subd7_3_1062 : subd7_3 [5, -3] = true := by decide +kernel
theorem subd7_3_1063 : subd7_3 [5, -2] = true := by decide +kernel
theorem subd7_3_1064 : subd7_3 [5, -1] = true := by decide +kernel
theorem subd7_3_1065 : subd7_3 [5, 0] = true := by decide +kernel
theorem subd7_3_1066 : subd7_3 [5, 1] = true := by decide +kernel
theorem subd7_3_1067 : subd7_3 [5, 2] = true := by decide +kernel
theorem subd7_3_1068 : subd7_3 [5, 3] = true := by decide +kernel
theorem subd7_3_1069 : subd7_3 [5, 4] = true := by decide +kernel
theorem subd7_3_1070 : subd7_3 [5, 5] = true := by decide +kernel
theorem subd7_3_1071 : subd7_3 [6, -3] = true := by decide +kernel
theorem subd7_3_1072 : subd7_3 [6, -2] = true := by decide +kernel
theorem subd7_3_1073 : subd7_3 [6, -1] = true := by decide +kernel
theorem subd7_3_1074 : subd7_3 [6, 0] = true := by decide +kernel
theorem subd7_3_1075 : subd7_3 [6, 1] = true := by decide +kernel
theorem subd7_3_1076 : subd7_3 [6, 2] = true := by decide +kernel
theorem subd7_3_1077 : subd7_3 [6, 3] = true := by decide +kernel
theorem subd7_3_1078 : subd7_3 [6, 4] = true := by decide +kernel
theorem sbd7_3_33 : ∀ q ∈ blkd7_3_33, subd7_3 q = true := by
  unfold blkd7_3_33
  exact List.forall_mem_cons.2 ⟨subd7_3_1056, List.forall_mem_cons.2 ⟨subd7_3_1057, List.forall_mem_cons.2 ⟨subd7_3_1058, List.forall_mem_cons.2 ⟨subd7_3_1059, List.forall_mem_cons.2 ⟨subd7_3_1060, List.forall_mem_cons.2 ⟨subd7_3_1061, List.forall_mem_cons.2 ⟨subd7_3_1062, List.forall_mem_cons.2 ⟨subd7_3_1063, List.forall_mem_cons.2 ⟨subd7_3_1064, List.forall_mem_cons.2 ⟨subd7_3_1065, List.forall_mem_cons.2 ⟨subd7_3_1066, List.forall_mem_cons.2 ⟨subd7_3_1067, List.forall_mem_cons.2 ⟨subd7_3_1068, List.forall_mem_cons.2 ⟨subd7_3_1069, List.forall_mem_cons.2 ⟨subd7_3_1070, List.forall_mem_cons.2 ⟨subd7_3_1071, List.forall_mem_cons.2 ⟨subd7_3_1072, List.forall_mem_cons.2 ⟨subd7_3_1073, List.forall_mem_cons.2 ⟨subd7_3_1074, List.forall_mem_cons.2 ⟨subd7_3_1075, List.forall_mem_cons.2 ⟨subd7_3_1076, List.forall_mem_cons.2 ⟨subd7_3_1077, List.forall_mem_cons.2 ⟨subd7_3_1078, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_4 : ldCheck G d7_4.U d7_4.ms ldd7_4 = true := by decide +kernel
theorem pre_okd7_4 : subPre G cell7 d7_4 = true := by decide +kernel
theorem subd7_4_0 : subd7_4 [-5] = true := by decide +kernel
theorem subd7_4_1 : subd7_4 [-4, -4] = true := by decide +kernel
theorem subd7_4_2 : subd7_4 [-4, -3] = true := by decide +kernel
theorem subd7_4_3 : subd7_4 [-4, -2] = true := by decide +kernel
theorem subd7_4_4 : subd7_4 [-4, -1] = true := by decide +kernel
theorem subd7_4_5 : subd7_4 [-4, 0] = true := by decide +kernel
theorem subd7_4_6 : subd7_4 [-4, 1] = true := by decide +kernel
theorem subd7_4_7 : subd7_4 [-4, 2] = true := by decide +kernel
theorem subd7_4_8 : subd7_4 [-4, 3] = true := by decide +kernel
theorem subd7_4_9 : subd7_4 [-3, -5] = true := by decide +kernel
theorem subd7_4_10 : subd7_4 [-3, -4] = true := by decide +kernel
theorem subd7_4_11 : subd7_4 [-3, -3] = true := by decide +kernel
theorem subd7_4_12 : subd7_4 [-3, -2] = true := by decide +kernel
theorem subd7_4_13 : subd7_4 [-3, -1, -7] = true := by decide +kernel
theorem subd7_4_14 : subd7_4 [-3, -1, -6] = true := by decide +kernel
theorem subd7_4_15 : subd7_4 [-3, -1, -5] = true := by decide +kernel
theorem subd7_4_16 : subd7_4 [-3, -1, -4] = true := by decide +kernel
theorem subd7_4_17 : subd7_4 [-3, -1, -3] = true := by decide +kernel
theorem subd7_4_18 : subd7_4 [-3, -1, -2] = true := by decide +kernel
theorem subd7_4_19 : subd7_4 [-3, -1, -1] = true := by decide +kernel
theorem subd7_4_20 : subd7_4 [-3, -1, 0] = true := by decide +kernel
theorem subd7_4_21 : subd7_4 [-3, -1, 1] = true := by decide +kernel
theorem subd7_4_22 : subd7_4 [-3, -1, 2] = true := by decide +kernel
theorem subd7_4_23 : subd7_4 [-3, -1, 3] = true := by decide +kernel
theorem subd7_4_24 : subd7_4 [-3, -1, 4] = true := by decide +kernel
theorem subd7_4_25 : subd7_4 [-3, -1, 5] = true := by decide +kernel
theorem subd7_4_26 : subd7_4 [-3, -1, 6] = true := by decide +kernel
theorem subd7_4_27 : subd7_4 [-3, 0, -7] = true := by decide +kernel
theorem subd7_4_28 : subd7_4 [-3, 0, -6] = true := by decide +kernel
theorem subd7_4_29 : subd7_4 [-3, 0, -5] = true := by decide +kernel
theorem subd7_4_30 : subd7_4 [-3, 0, -4] = true := by decide +kernel
theorem subd7_4_31 : subd7_4 [-3, 0, -3] = true := by decide +kernel
theorem sbd7_4_0 : ∀ q ∈ blkd7_4_0, subd7_4 q = true := by
  unfold blkd7_4_0
  exact List.forall_mem_cons.2 ⟨subd7_4_0, List.forall_mem_cons.2 ⟨subd7_4_1, List.forall_mem_cons.2 ⟨subd7_4_2, List.forall_mem_cons.2 ⟨subd7_4_3, List.forall_mem_cons.2 ⟨subd7_4_4, List.forall_mem_cons.2 ⟨subd7_4_5, List.forall_mem_cons.2 ⟨subd7_4_6, List.forall_mem_cons.2 ⟨subd7_4_7, List.forall_mem_cons.2 ⟨subd7_4_8, List.forall_mem_cons.2 ⟨subd7_4_9, List.forall_mem_cons.2 ⟨subd7_4_10, List.forall_mem_cons.2 ⟨subd7_4_11, List.forall_mem_cons.2 ⟨subd7_4_12, List.forall_mem_cons.2 ⟨subd7_4_13, List.forall_mem_cons.2 ⟨subd7_4_14, List.forall_mem_cons.2 ⟨subd7_4_15, List.forall_mem_cons.2 ⟨subd7_4_16, List.forall_mem_cons.2 ⟨subd7_4_17, List.forall_mem_cons.2 ⟨subd7_4_18, List.forall_mem_cons.2 ⟨subd7_4_19, List.forall_mem_cons.2 ⟨subd7_4_20, List.forall_mem_cons.2 ⟨subd7_4_21, List.forall_mem_cons.2 ⟨subd7_4_22, List.forall_mem_cons.2 ⟨subd7_4_23, List.forall_mem_cons.2 ⟨subd7_4_24, List.forall_mem_cons.2 ⟨subd7_4_25, List.forall_mem_cons.2 ⟨subd7_4_26, List.forall_mem_cons.2 ⟨subd7_4_27, List.forall_mem_cons.2 ⟨subd7_4_28, List.forall_mem_cons.2 ⟨subd7_4_29, List.forall_mem_cons.2 ⟨subd7_4_30, List.forall_mem_cons.2 ⟨subd7_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C135
