import ReflectZphi.Data.Cert5.C044.Base

namespace ReflectZphi.Data.Cert5.C044
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub3_832 : sub3 [2, 1, -2] = true := by decide +kernel
theorem sub3_833 : sub3 [2, 1, -1] = true := by decide +kernel
theorem sub3_834 : sub3 [2, 1, 0] = true := by decide +kernel
theorem sub3_835 : sub3 [2, 1, 1] = true := by decide +kernel
theorem sub3_836 : sub3 [2, 1, 2] = true := by decide +kernel
theorem sub3_837 : sub3 [2, 1, 3] = true := by decide +kernel
theorem sub3_838 : sub3 [2, 1, 4] = true := by decide +kernel
theorem sub3_839 : sub3 [2, 1, 5] = true := by decide +kernel
theorem sub3_840 : sub3 [2, 1, 6] = true := by decide +kernel
theorem sub3_841 : sub3 [2, 1, 7] = true := by decide +kernel
theorem sub3_842 : sub3 [2, 1, 8] = true := by decide +kernel
theorem sub3_843 : sub3 [2, 2, -9] = true := by decide +kernel
theorem sub3_844 : sub3 [2, 2, -8] = true := by decide +kernel
theorem sub3_845 : sub3 [2, 2, -7] = true := by decide +kernel
theorem sub3_846 : sub3 [2, 2, -6] = true := by decide +kernel
theorem sub3_847 : sub3 [2, 2, -5] = true := by decide +kernel
theorem sub3_848 : sub3 [2, 2, -4] = true := by decide +kernel
theorem sub3_849 : sub3 [2, 2, -3] = true := by decide +kernel
theorem sub3_850 : sub3 [2, 2, -2] = true := by decide +kernel
theorem sub3_851 : sub3 [2, 2, -1] = true := by decide +kernel
theorem sub3_852 : sub3 [2, 2, 0] = true := by decide +kernel
theorem sub3_853 : sub3 [2, 2, 1] = true := by decide +kernel
theorem sub3_854 : sub3 [2, 2, 2] = true := by decide +kernel
theorem sub3_855 : sub3 [2, 2, 3] = true := by decide +kernel
theorem sub3_856 : sub3 [2, 2, 4] = true := by decide +kernel
theorem sub3_857 : sub3 [2, 2, 5] = true := by decide +kernel
theorem sub3_858 : sub3 [2, 2, 6] = true := by decide +kernel
theorem sub3_859 : sub3 [2, 2, 7] = true := by decide +kernel
theorem sub3_860 : sub3 [2, 2, 8] = true := by decide +kernel
theorem sub3_861 : sub3 [2, 3, -8] = true := by decide +kernel
theorem sub3_862 : sub3 [2, 3, -7] = true := by decide +kernel
theorem sub3_863 : sub3 [2, 3, -6] = true := by decide +kernel
theorem sb3_26 : ∀ q ∈ blk3_26, sub3 q = true := by
  unfold blk3_26
  exact List.forall_mem_cons.2 ⟨sub3_832, List.forall_mem_cons.2 ⟨sub3_833, List.forall_mem_cons.2 ⟨sub3_834, List.forall_mem_cons.2 ⟨sub3_835, List.forall_mem_cons.2 ⟨sub3_836, List.forall_mem_cons.2 ⟨sub3_837, List.forall_mem_cons.2 ⟨sub3_838, List.forall_mem_cons.2 ⟨sub3_839, List.forall_mem_cons.2 ⟨sub3_840, List.forall_mem_cons.2 ⟨sub3_841, List.forall_mem_cons.2 ⟨sub3_842, List.forall_mem_cons.2 ⟨sub3_843, List.forall_mem_cons.2 ⟨sub3_844, List.forall_mem_cons.2 ⟨sub3_845, List.forall_mem_cons.2 ⟨sub3_846, List.forall_mem_cons.2 ⟨sub3_847, List.forall_mem_cons.2 ⟨sub3_848, List.forall_mem_cons.2 ⟨sub3_849, List.forall_mem_cons.2 ⟨sub3_850, List.forall_mem_cons.2 ⟨sub3_851, List.forall_mem_cons.2 ⟨sub3_852, List.forall_mem_cons.2 ⟨sub3_853, List.forall_mem_cons.2 ⟨sub3_854, List.forall_mem_cons.2 ⟨sub3_855, List.forall_mem_cons.2 ⟨sub3_856, List.forall_mem_cons.2 ⟨sub3_857, List.forall_mem_cons.2 ⟨sub3_858, List.forall_mem_cons.2 ⟨sub3_859, List.forall_mem_cons.2 ⟨sub3_860, List.forall_mem_cons.2 ⟨sub3_861, List.forall_mem_cons.2 ⟨sub3_862, List.forall_mem_cons.2 ⟨sub3_863, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_864 : sub3 [2, 3, -5] = true := by decide +kernel
theorem sub3_865 : sub3 [2, 3, -4] = true := by decide +kernel
theorem sub3_866 : sub3 [2, 3, -3] = true := by decide +kernel
theorem sub3_867 : sub3 [2, 3, -2] = true := by decide +kernel
theorem sub3_868 : sub3 [2, 3, -1] = true := by decide +kernel
theorem sub3_869 : sub3 [2, 3, 0] = true := by decide +kernel
theorem sub3_870 : sub3 [2, 3, 1] = true := by decide +kernel
theorem sub3_871 : sub3 [2, 3, 2] = true := by decide +kernel
theorem sub3_872 : sub3 [2, 3, 3] = true := by decide +kernel
theorem sub3_873 : sub3 [2, 3, 4] = true := by decide +kernel
theorem sub3_874 : sub3 [2, 3, 5] = true := by decide +kernel
theorem sub3_875 : sub3 [2, 3, 6] = true := by decide +kernel
theorem sub3_876 : sub3 [2, 3, 7] = true := by decide +kernel
theorem sub3_877 : sub3 [2, 3, 8] = true := by decide +kernel
theorem sub3_878 : sub3 [2, 4, -7] = true := by decide +kernel
theorem sub3_879 : sub3 [2, 4, -6] = true := by decide +kernel
theorem sub3_880 : sub3 [2, 4, -5] = true := by decide +kernel
theorem sub3_881 : sub3 [2, 4, -4] = true := by decide +kernel
theorem sub3_882 : sub3 [2, 4, -3] = true := by decide +kernel
theorem sub3_883 : sub3 [2, 4, -2] = true := by decide +kernel
theorem sub3_884 : sub3 [2, 4, -1] = true := by decide +kernel
theorem sub3_885 : sub3 [2, 4, 0] = true := by decide +kernel
theorem sub3_886 : sub3 [2, 4, 1] = true := by decide +kernel
theorem sub3_887 : sub3 [2, 4, 2] = true := by decide +kernel
theorem sub3_888 : sub3 [2, 4, 3] = true := by decide +kernel
theorem sub3_889 : sub3 [2, 4, 4] = true := by decide +kernel
theorem sub3_890 : sub3 [2, 4, 5] = true := by decide +kernel
theorem sub3_891 : sub3 [2, 4, 6] = true := by decide +kernel
theorem sub3_892 : sub3 [2, 4, 7] = true := by decide +kernel
theorem sub3_893 : sub3 [2, 5] = true := by decide +kernel
theorem sub3_894 : sub3 [2, 6] = true := by decide +kernel
theorem sub3_895 : sub3 [3, -5] = true := by decide +kernel
theorem sb3_27 : ∀ q ∈ blk3_27, sub3 q = true := by
  unfold blk3_27
  exact List.forall_mem_cons.2 ⟨sub3_864, List.forall_mem_cons.2 ⟨sub3_865, List.forall_mem_cons.2 ⟨sub3_866, List.forall_mem_cons.2 ⟨sub3_867, List.forall_mem_cons.2 ⟨sub3_868, List.forall_mem_cons.2 ⟨sub3_869, List.forall_mem_cons.2 ⟨sub3_870, List.forall_mem_cons.2 ⟨sub3_871, List.forall_mem_cons.2 ⟨sub3_872, List.forall_mem_cons.2 ⟨sub3_873, List.forall_mem_cons.2 ⟨sub3_874, List.forall_mem_cons.2 ⟨sub3_875, List.forall_mem_cons.2 ⟨sub3_876, List.forall_mem_cons.2 ⟨sub3_877, List.forall_mem_cons.2 ⟨sub3_878, List.forall_mem_cons.2 ⟨sub3_879, List.forall_mem_cons.2 ⟨sub3_880, List.forall_mem_cons.2 ⟨sub3_881, List.forall_mem_cons.2 ⟨sub3_882, List.forall_mem_cons.2 ⟨sub3_883, List.forall_mem_cons.2 ⟨sub3_884, List.forall_mem_cons.2 ⟨sub3_885, List.forall_mem_cons.2 ⟨sub3_886, List.forall_mem_cons.2 ⟨sub3_887, List.forall_mem_cons.2 ⟨sub3_888, List.forall_mem_cons.2 ⟨sub3_889, List.forall_mem_cons.2 ⟨sub3_890, List.forall_mem_cons.2 ⟨sub3_891, List.forall_mem_cons.2 ⟨sub3_892, List.forall_mem_cons.2 ⟨sub3_893, List.forall_mem_cons.2 ⟨sub3_894, List.forall_mem_cons.2 ⟨sub3_895, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_896 : sub3 [3, -4] = true := by decide +kernel
theorem sub3_897 : sub3 [3, -3] = true := by decide +kernel
theorem sub3_898 : sub3 [3, -2] = true := by decide +kernel
theorem sub3_899 : sub3 [3, -1, -8] = true := by decide +kernel
theorem sub3_900 : sub3 [3, -1, -7] = true := by decide +kernel
theorem sub3_901 : sub3 [3, -1, -6] = true := by decide +kernel
theorem sub3_902 : sub3 [3, -1, -5] = true := by decide +kernel
theorem sub3_903 : sub3 [3, -1, -4] = true := by decide +kernel
theorem sub3_904 : sub3 [3, -1, -3] = true := by decide +kernel
theorem sub3_905 : sub3 [3, -1, -2] = true := by decide +kernel
theorem sub3_906 : sub3 [3, -1, -1] = true := by decide +kernel
theorem sub3_907 : sub3 [3, -1, 0] = true := by decide +kernel
theorem sub3_908 : sub3 [3, -1, 1] = true := by decide +kernel
theorem sub3_909 : sub3 [3, -1, 2] = true := by decide +kernel
theorem sub3_910 : sub3 [3, -1, 3] = true := by decide +kernel
theorem sub3_911 : sub3 [3, -1, 4] = true := by decide +kernel
theorem sub3_912 : sub3 [3, -1, 5] = true := by decide +kernel
theorem sub3_913 : sub3 [3, -1, 6] = true := by decide +kernel
theorem sub3_914 : sub3 [3, 0, -9] = true := by decide +kernel
theorem sub3_915 : sub3 [3, 0, -8] = true := by decide +kernel
theorem sub3_916 : sub3 [3, 0, -7] = true := by decide +kernel
theorem sub3_917 : sub3 [3, 0, -6] = true := by decide +kernel
theorem sub3_918 : sub3 [3, 0, -5] = true := by decide +kernel
theorem sub3_919 : sub3 [3, 0, -4] = true := by decide +kernel
theorem sub3_920 : sub3 [3, 0, -3] = true := by decide +kernel
theorem sub3_921 : sub3 [3, 0, -2] = true := by decide +kernel
theorem sub3_922 : sub3 [3, 0, -1] = true := by decide +kernel
theorem sub3_923 : sub3 [3, 0, 0] = true := by decide +kernel
theorem sub3_924 : sub3 [3, 0, 1] = true := by decide +kernel
theorem sub3_925 : sub3 [3, 0, 2] = true := by decide +kernel
theorem sub3_926 : sub3 [3, 0, 3] = true := by decide +kernel
theorem sub3_927 : sub3 [3, 0, 4] = true := by decide +kernel
theorem sb3_28 : ∀ q ∈ blk3_28, sub3 q = true := by
  unfold blk3_28
  exact List.forall_mem_cons.2 ⟨sub3_896, List.forall_mem_cons.2 ⟨sub3_897, List.forall_mem_cons.2 ⟨sub3_898, List.forall_mem_cons.2 ⟨sub3_899, List.forall_mem_cons.2 ⟨sub3_900, List.forall_mem_cons.2 ⟨sub3_901, List.forall_mem_cons.2 ⟨sub3_902, List.forall_mem_cons.2 ⟨sub3_903, List.forall_mem_cons.2 ⟨sub3_904, List.forall_mem_cons.2 ⟨sub3_905, List.forall_mem_cons.2 ⟨sub3_906, List.forall_mem_cons.2 ⟨sub3_907, List.forall_mem_cons.2 ⟨sub3_908, List.forall_mem_cons.2 ⟨sub3_909, List.forall_mem_cons.2 ⟨sub3_910, List.forall_mem_cons.2 ⟨sub3_911, List.forall_mem_cons.2 ⟨sub3_912, List.forall_mem_cons.2 ⟨sub3_913, List.forall_mem_cons.2 ⟨sub3_914, List.forall_mem_cons.2 ⟨sub3_915, List.forall_mem_cons.2 ⟨sub3_916, List.forall_mem_cons.2 ⟨sub3_917, List.forall_mem_cons.2 ⟨sub3_918, List.forall_mem_cons.2 ⟨sub3_919, List.forall_mem_cons.2 ⟨sub3_920, List.forall_mem_cons.2 ⟨sub3_921, List.forall_mem_cons.2 ⟨sub3_922, List.forall_mem_cons.2 ⟨sub3_923, List.forall_mem_cons.2 ⟨sub3_924, List.forall_mem_cons.2 ⟨sub3_925, List.forall_mem_cons.2 ⟨sub3_926, List.forall_mem_cons.2 ⟨sub3_927, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_928 : sub3 [3, 0, 5] = true := by decide +kernel
theorem sub3_929 : sub3 [3, 0, 6] = true := by decide +kernel
theorem sub3_930 : sub3 [3, 0, 7] = true := by decide +kernel
theorem sub3_931 : sub3 [3, 1, -9] = true := by decide +kernel
theorem sub3_932 : sub3 [3, 1, -8] = true := by decide +kernel
theorem sub3_933 : sub3 [3, 1, -7] = true := by decide +kernel
theorem sub3_934 : sub3 [3, 1, -6] = true := by decide +kernel
theorem sub3_935 : sub3 [3, 1, -5] = true := by decide +kernel
theorem sub3_936 : sub3 [3, 1, -4] = true := by decide +kernel
theorem sub3_937 : sub3 [3, 1, -3] = true := by decide +kernel
theorem sub3_938 : sub3 [3, 1, -2] = true := by decide +kernel
theorem sub3_939 : sub3 [3, 1, -1] = true := by decide +kernel
theorem sub3_940 : sub3 [3, 1, 0] = true := by decide +kernel
theorem sub3_941 : sub3 [3, 1, 1] = true := by decide +kernel
theorem sub3_942 : sub3 [3, 1, 2] = true := by decide +kernel
theorem sub3_943 : sub3 [3, 1, 3] = true := by decide +kernel
theorem sub3_944 : sub3 [3, 1, 4] = true := by decide +kernel
theorem sub3_945 : sub3 [3, 1, 5] = true := by decide +kernel
theorem sub3_946 : sub3 [3, 1, 6] = true := by decide +kernel
theorem sub3_947 : sub3 [3, 1, 7] = true := by decide +kernel
theorem sub3_948 : sub3 [3, 2, -8] = true := by decide +kernel
theorem sub3_949 : sub3 [3, 2, -7] = true := by decide +kernel
theorem sub3_950 : sub3 [3, 2, -6] = true := by decide +kernel
theorem sub3_951 : sub3 [3, 2, -5] = true := by decide +kernel
theorem sub3_952 : sub3 [3, 2, -4] = true := by decide +kernel
theorem sub3_953 : sub3 [3, 2, -3] = true := by decide +kernel
theorem sub3_954 : sub3 [3, 2, -2] = true := by decide +kernel
theorem sub3_955 : sub3 [3, 2, -1] = true := by decide +kernel
theorem sub3_956 : sub3 [3, 2, 0] = true := by decide +kernel
theorem sub3_957 : sub3 [3, 2, 1] = true := by decide +kernel
theorem sub3_958 : sub3 [3, 2, 2] = true := by decide +kernel
theorem sub3_959 : sub3 [3, 2, 3] = true := by decide +kernel
theorem sb3_29 : ∀ q ∈ blk3_29, sub3 q = true := by
  unfold blk3_29
  exact List.forall_mem_cons.2 ⟨sub3_928, List.forall_mem_cons.2 ⟨sub3_929, List.forall_mem_cons.2 ⟨sub3_930, List.forall_mem_cons.2 ⟨sub3_931, List.forall_mem_cons.2 ⟨sub3_932, List.forall_mem_cons.2 ⟨sub3_933, List.forall_mem_cons.2 ⟨sub3_934, List.forall_mem_cons.2 ⟨sub3_935, List.forall_mem_cons.2 ⟨sub3_936, List.forall_mem_cons.2 ⟨sub3_937, List.forall_mem_cons.2 ⟨sub3_938, List.forall_mem_cons.2 ⟨sub3_939, List.forall_mem_cons.2 ⟨sub3_940, List.forall_mem_cons.2 ⟨sub3_941, List.forall_mem_cons.2 ⟨sub3_942, List.forall_mem_cons.2 ⟨sub3_943, List.forall_mem_cons.2 ⟨sub3_944, List.forall_mem_cons.2 ⟨sub3_945, List.forall_mem_cons.2 ⟨sub3_946, List.forall_mem_cons.2 ⟨sub3_947, List.forall_mem_cons.2 ⟨sub3_948, List.forall_mem_cons.2 ⟨sub3_949, List.forall_mem_cons.2 ⟨sub3_950, List.forall_mem_cons.2 ⟨sub3_951, List.forall_mem_cons.2 ⟨sub3_952, List.forall_mem_cons.2 ⟨sub3_953, List.forall_mem_cons.2 ⟨sub3_954, List.forall_mem_cons.2 ⟨sub3_955, List.forall_mem_cons.2 ⟨sub3_956, List.forall_mem_cons.2 ⟨sub3_957, List.forall_mem_cons.2 ⟨sub3_958, List.forall_mem_cons.2 ⟨sub3_959, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_960 : sub3 [3, 2, 4] = true := by decide +kernel
theorem sub3_961 : sub3 [3, 2, 5] = true := by decide +kernel
theorem sub3_962 : sub3 [3, 2, 6] = true := by decide +kernel
theorem sub3_963 : sub3 [3, 2, 7] = true := by decide +kernel
theorem sub3_964 : sub3 [3, 3, -8] = true := by decide +kernel
theorem sub3_965 : sub3 [3, 3, -7] = true := by decide +kernel
theorem sub3_966 : sub3 [3, 3, -6] = true := by decide +kernel
theorem sub3_967 : sub3 [3, 3, -5] = true := by decide +kernel
theorem sub3_968 : sub3 [3, 3, -4] = true := by decide +kernel
theorem sub3_969 : sub3 [3, 3, -3] = true := by decide +kernel
theorem sub3_970 : sub3 [3, 3, -2] = true := by decide +kernel
theorem sub3_971 : sub3 [3, 3, -1] = true := by decide +kernel
theorem sub3_972 : sub3 [3, 3, 0] = true := by decide +kernel
theorem sub3_973 : sub3 [3, 3, 1] = true := by decide +kernel
theorem sub3_974 : sub3 [3, 3, 2] = true := by decide +kernel
theorem sub3_975 : sub3 [3, 3, 3] = true := by decide +kernel
theorem sub3_976 : sub3 [3, 3, 4] = true := by decide +kernel
theorem sub3_977 : sub3 [3, 3, 5] = true := by decide +kernel
theorem sub3_978 : sub3 [3, 3, 6] = true := by decide +kernel
theorem sub3_979 : sub3 [3, 3, 7] = true := by decide +kernel
theorem sub3_980 : sub3 [3, 4, -7] = true := by decide +kernel
theorem sub3_981 : sub3 [3, 4, -6] = true := by decide +kernel
theorem sub3_982 : sub3 [3, 4, -5] = true := by decide +kernel
theorem sub3_983 : sub3 [3, 4, -4] = true := by decide +kernel
theorem sub3_984 : sub3 [3, 4, -3] = true := by decide +kernel
theorem sub3_985 : sub3 [3, 4, -2] = true := by decide +kernel
theorem sub3_986 : sub3 [3, 4, -1] = true := by decide +kernel
theorem sub3_987 : sub3 [3, 4, 0] = true := by decide +kernel
theorem sub3_988 : sub3 [3, 4, 1] = true := by decide +kernel
theorem sub3_989 : sub3 [3, 4, 2] = true := by decide +kernel
theorem sub3_990 : sub3 [3, 4, 3] = true := by decide +kernel
theorem sub3_991 : sub3 [3, 4, 4] = true := by decide +kernel
theorem sb3_30 : ∀ q ∈ blk3_30, sub3 q = true := by
  unfold blk3_30
  exact List.forall_mem_cons.2 ⟨sub3_960, List.forall_mem_cons.2 ⟨sub3_961, List.forall_mem_cons.2 ⟨sub3_962, List.forall_mem_cons.2 ⟨sub3_963, List.forall_mem_cons.2 ⟨sub3_964, List.forall_mem_cons.2 ⟨sub3_965, List.forall_mem_cons.2 ⟨sub3_966, List.forall_mem_cons.2 ⟨sub3_967, List.forall_mem_cons.2 ⟨sub3_968, List.forall_mem_cons.2 ⟨sub3_969, List.forall_mem_cons.2 ⟨sub3_970, List.forall_mem_cons.2 ⟨sub3_971, List.forall_mem_cons.2 ⟨sub3_972, List.forall_mem_cons.2 ⟨sub3_973, List.forall_mem_cons.2 ⟨sub3_974, List.forall_mem_cons.2 ⟨sub3_975, List.forall_mem_cons.2 ⟨sub3_976, List.forall_mem_cons.2 ⟨sub3_977, List.forall_mem_cons.2 ⟨sub3_978, List.forall_mem_cons.2 ⟨sub3_979, List.forall_mem_cons.2 ⟨sub3_980, List.forall_mem_cons.2 ⟨sub3_981, List.forall_mem_cons.2 ⟨sub3_982, List.forall_mem_cons.2 ⟨sub3_983, List.forall_mem_cons.2 ⟨sub3_984, List.forall_mem_cons.2 ⟨sub3_985, List.forall_mem_cons.2 ⟨sub3_986, List.forall_mem_cons.2 ⟨sub3_987, List.forall_mem_cons.2 ⟨sub3_988, List.forall_mem_cons.2 ⟨sub3_989, List.forall_mem_cons.2 ⟨sub3_990, List.forall_mem_cons.2 ⟨sub3_991, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_992 : sub3 [3, 4, 5] = true := by decide +kernel
theorem sub3_993 : sub3 [3, 4, 6] = true := by decide +kernel
theorem sub3_994 : sub3 [3, 5] = true := by decide +kernel
theorem sub3_995 : sub3 [3, 6] = true := by decide +kernel
theorem sub3_996 : sub3 [4, -3] = true := by decide +kernel
theorem sub3_997 : sub3 [4, -2] = true := by decide +kernel
theorem sub3_998 : sub3 [4, -1] = true := by decide +kernel
theorem sub3_999 : sub3 [4, 0] = true := by decide +kernel
theorem sub3_1000 : sub3 [4, 1, -7] = true := by decide +kernel
theorem sub3_1001 : sub3 [4, 1, -6] = true := by decide +kernel
theorem sub3_1002 : sub3 [4, 1, -5] = true := by decide +kernel
theorem sub3_1003 : sub3 [4, 1, -4] = true := by decide +kernel
theorem sub3_1004 : sub3 [4, 1, -3] = true := by decide +kernel
theorem sub3_1005 : sub3 [4, 1, -2] = true := by decide +kernel
theorem sub3_1006 : sub3 [4, 1, -1] = true := by decide +kernel
theorem sub3_1007 : sub3 [4, 1, 0] = true := by decide +kernel
theorem sub3_1008 : sub3 [4, 1, 1] = true := by decide +kernel
theorem sub3_1009 : sub3 [4, 1, 2] = true := by decide +kernel
theorem sub3_1010 : sub3 [4, 1, 3] = true := by decide +kernel
theorem sub3_1011 : sub3 [4, 1, 4] = true := by decide +kernel
theorem sub3_1012 : sub3 [4, 1, 5] = true := by decide +kernel
theorem sub3_1013 : sub3 [4, 2, -7] = true := by decide +kernel
theorem sub3_1014 : sub3 [4, 2, -6] = true := by decide +kernel
theorem sub3_1015 : sub3 [4, 2, -5] = true := by decide +kernel
theorem sub3_1016 : sub3 [4, 2, -4] = true := by decide +kernel
theorem sub3_1017 : sub3 [4, 2, -3] = true := by decide +kernel
theorem sub3_1018 : sub3 [4, 2, -2] = true := by decide +kernel
theorem sub3_1019 : sub3 [4, 2, -1] = true := by decide +kernel
theorem sub3_1020 : sub3 [4, 2, 0] = true := by decide +kernel
theorem sub3_1021 : sub3 [4, 2, 1] = true := by decide +kernel
theorem sub3_1022 : sub3 [4, 2, 2] = true := by decide +kernel
theorem sub3_1023 : sub3 [4, 2, 3] = true := by decide +kernel
theorem sb3_31 : ∀ q ∈ blk3_31, sub3 q = true := by
  unfold blk3_31
  exact List.forall_mem_cons.2 ⟨sub3_992, List.forall_mem_cons.2 ⟨sub3_993, List.forall_mem_cons.2 ⟨sub3_994, List.forall_mem_cons.2 ⟨sub3_995, List.forall_mem_cons.2 ⟨sub3_996, List.forall_mem_cons.2 ⟨sub3_997, List.forall_mem_cons.2 ⟨sub3_998, List.forall_mem_cons.2 ⟨sub3_999, List.forall_mem_cons.2 ⟨sub3_1000, List.forall_mem_cons.2 ⟨sub3_1001, List.forall_mem_cons.2 ⟨sub3_1002, List.forall_mem_cons.2 ⟨sub3_1003, List.forall_mem_cons.2 ⟨sub3_1004, List.forall_mem_cons.2 ⟨sub3_1005, List.forall_mem_cons.2 ⟨sub3_1006, List.forall_mem_cons.2 ⟨sub3_1007, List.forall_mem_cons.2 ⟨sub3_1008, List.forall_mem_cons.2 ⟨sub3_1009, List.forall_mem_cons.2 ⟨sub3_1010, List.forall_mem_cons.2 ⟨sub3_1011, List.forall_mem_cons.2 ⟨sub3_1012, List.forall_mem_cons.2 ⟨sub3_1013, List.forall_mem_cons.2 ⟨sub3_1014, List.forall_mem_cons.2 ⟨sub3_1015, List.forall_mem_cons.2 ⟨sub3_1016, List.forall_mem_cons.2 ⟨sub3_1017, List.forall_mem_cons.2 ⟨sub3_1018, List.forall_mem_cons.2 ⟨sub3_1019, List.forall_mem_cons.2 ⟨sub3_1020, List.forall_mem_cons.2 ⟨sub3_1021, List.forall_mem_cons.2 ⟨sub3_1022, List.forall_mem_cons.2 ⟨sub3_1023, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_1024 : sub3 [4, 2, 4] = true := by decide +kernel
theorem sub3_1025 : sub3 [4, 2, 5] = true := by decide +kernel
theorem sub3_1026 : sub3 [4, 3] = true := by decide +kernel
theorem sub3_1027 : sub3 [4, 4] = true := by decide +kernel
theorem sub3_1028 : sub3 [4, 5] = true := by decide +kernel
theorem sub3_1029 : sub3 [5, -1] = true := by decide +kernel
theorem sub3_1030 : sub3 [5, 0] = true := by decide +kernel
theorem sub3_1031 : sub3 [5, 1] = true := by decide +kernel
theorem sub3_1032 : sub3 [5, 2] = true := by decide +kernel
theorem sub3_1033 : sub3 [5, 3] = true := by decide +kernel
theorem sub3_1034 : sub3 [5, 4] = true := by decide +kernel
theorem sb3_32 : ∀ q ∈ blk3_32, sub3 q = true := by
  unfold blk3_32
  exact List.forall_mem_cons.2 ⟨sub3_1024, List.forall_mem_cons.2 ⟨sub3_1025, List.forall_mem_cons.2 ⟨sub3_1026, List.forall_mem_cons.2 ⟨sub3_1027, List.forall_mem_cons.2 ⟨sub3_1028, List.forall_mem_cons.2 ⟨sub3_1029, List.forall_mem_cons.2 ⟨sub3_1030, List.forall_mem_cons.2 ⟨sub3_1031, List.forall_mem_cons.2 ⟨sub3_1032, List.forall_mem_cons.2 ⟨sub3_1033, List.forall_mem_cons.2 ⟨sub3_1034, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_0 : sub4 [-6, -4] = true := by decide +kernel
theorem sub4_1 : sub4 [-6, -3] = true := by decide +kernel
theorem sub4_2 : sub4 [-6, -2] = true := by decide +kernel
theorem sub4_3 : sub4 [-6, -1] = true := by decide +kernel
theorem sub4_4 : sub4 [-6, 0] = true := by decide +kernel
theorem sub4_5 : sub4 [-6, 1] = true := by decide +kernel
theorem sub4_6 : sub4 [-6, 2] = true := by decide +kernel
theorem sub4_7 : sub4 [-6, 3] = true := by decide +kernel
theorem sub4_8 : sub4 [-5, -5] = true := by decide +kernel
theorem sub4_9 : sub4 [-5, -4] = true := by decide +kernel
theorem sub4_10 : sub4 [-5, -3] = true := by decide +kernel
theorem sub4_11 : sub4 [-5, -2] = true := by decide +kernel
theorem sub4_12 : sub4 [-5, -1] = true := by decide +kernel
theorem sub4_13 : sub4 [-5, 0] = true := by decide +kernel
theorem sub4_14 : sub4 [-5, 1] = true := by decide +kernel
theorem sub4_15 : sub4 [-5, 2] = true := by decide +kernel
theorem sub4_16 : sub4 [-5, 3] = true := by decide +kernel
theorem sub4_17 : sub4 [-5, 4] = true := by decide +kernel
theorem sub4_18 : sub4 [-4, -6] = true := by decide +kernel
theorem sub4_19 : sub4 [-4, -5] = true := by decide +kernel
theorem sub4_20 : sub4 [-4, -4] = true := by decide +kernel
theorem sub4_21 : sub4 [-4, -3] = true := by decide +kernel
theorem sub4_22 : sub4 [-4, -2] = true := by decide +kernel
theorem sub4_23 : sub4 [-4, -1, -7] = true := by decide +kernel
theorem sub4_24 : sub4 [-4, -1, -6] = true := by decide +kernel
theorem sub4_25 : sub4 [-4, -1, -5] = true := by decide +kernel
theorem sub4_26 : sub4 [-4, -1, -4] = true := by decide +kernel
theorem sub4_27 : sub4 [-4, -1, -3] = true := by decide +kernel
theorem sub4_28 : sub4 [-4, -1, -2] = true := by decide +kernel
theorem sub4_29 : sub4 [-4, -1, -1] = true := by decide +kernel
theorem sub4_30 : sub4 [-4, -1, 0] = true := by decide +kernel
theorem sub4_31 : sub4 [-4, -1, 1] = true := by decide +kernel
theorem sb4_0 : ∀ q ∈ blk4_0, sub4 q = true := by
  unfold blk4_0
  exact List.forall_mem_cons.2 ⟨sub4_0, List.forall_mem_cons.2 ⟨sub4_1, List.forall_mem_cons.2 ⟨sub4_2, List.forall_mem_cons.2 ⟨sub4_3, List.forall_mem_cons.2 ⟨sub4_4, List.forall_mem_cons.2 ⟨sub4_5, List.forall_mem_cons.2 ⟨sub4_6, List.forall_mem_cons.2 ⟨sub4_7, List.forall_mem_cons.2 ⟨sub4_8, List.forall_mem_cons.2 ⟨sub4_9, List.forall_mem_cons.2 ⟨sub4_10, List.forall_mem_cons.2 ⟨sub4_11, List.forall_mem_cons.2 ⟨sub4_12, List.forall_mem_cons.2 ⟨sub4_13, List.forall_mem_cons.2 ⟨sub4_14, List.forall_mem_cons.2 ⟨sub4_15, List.forall_mem_cons.2 ⟨sub4_16, List.forall_mem_cons.2 ⟨sub4_17, List.forall_mem_cons.2 ⟨sub4_18, List.forall_mem_cons.2 ⟨sub4_19, List.forall_mem_cons.2 ⟨sub4_20, List.forall_mem_cons.2 ⟨sub4_21, List.forall_mem_cons.2 ⟨sub4_22, List.forall_mem_cons.2 ⟨sub4_23, List.forall_mem_cons.2 ⟨sub4_24, List.forall_mem_cons.2 ⟨sub4_25, List.forall_mem_cons.2 ⟨sub4_26, List.forall_mem_cons.2 ⟨sub4_27, List.forall_mem_cons.2 ⟨sub4_28, List.forall_mem_cons.2 ⟨sub4_29, List.forall_mem_cons.2 ⟨sub4_30, List.forall_mem_cons.2 ⟨sub4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_32 : sub4 [-4, -1, 2] = true := by decide +kernel
theorem sub4_33 : sub4 [-4, -1, 3] = true := by decide +kernel
theorem sub4_34 : sub4 [-4, -1, 4] = true := by decide +kernel
theorem sub4_35 : sub4 [-4, -1, 5] = true := by decide +kernel
theorem sub4_36 : sub4 [-4, -1, 6] = true := by decide +kernel
theorem sub4_37 : sub4 [-4, 0, -7] = true := by decide +kernel
theorem sub4_38 : sub4 [-4, 0, -6] = true := by decide +kernel
theorem sub4_39 : sub4 [-4, 0, -5] = true := by decide +kernel
theorem sub4_40 : sub4 [-4, 0, -4] = true := by decide +kernel
theorem sub4_41 : sub4 [-4, 0, -3] = true := by decide +kernel
theorem sub4_42 : sub4 [-4, 0, -2] = true := by decide +kernel
theorem sub4_43 : sub4 [-4, 0, -1] = true := by decide +kernel
theorem sub4_44 : sub4 [-4, 0, 0] = true := by decide +kernel
theorem sub4_45 : sub4 [-4, 0, 1] = true := by decide +kernel
theorem sub4_46 : sub4 [-4, 0, 2] = true := by decide +kernel
theorem sub4_47 : sub4 [-4, 0, 3] = true := by decide +kernel
theorem sub4_48 : sub4 [-4, 0, 4] = true := by decide +kernel
theorem sub4_49 : sub4 [-4, 0, 5] = true := by decide +kernel
theorem sub4_50 : sub4 [-4, 0, 6] = true := by decide +kernel
theorem sub4_51 : sub4 [-4, 1, -6] = true := by decide +kernel
theorem sub4_52 : sub4 [-4, 1, -5] = true := by decide +kernel
theorem sub4_53 : sub4 [-4, 1, -4] = true := by decide +kernel
theorem sub4_54 : sub4 [-4, 1, -3] = true := by decide +kernel
theorem sub4_55 : sub4 [-4, 1, -2] = true := by decide +kernel
theorem sub4_56 : sub4 [-4, 1, -1] = true := by decide +kernel
theorem sub4_57 : sub4 [-4, 1, 0] = true := by decide +kernel
theorem sub4_58 : sub4 [-4, 1, 1] = true := by decide +kernel
theorem sub4_59 : sub4 [-4, 1, 2] = true := by decide +kernel
theorem sub4_60 : sub4 [-4, 1, 3] = true := by decide +kernel
theorem sub4_61 : sub4 [-4, 1, 4] = true := by decide +kernel
theorem sub4_62 : sub4 [-4, 1, 5] = true := by decide +kernel
theorem sub4_63 : sub4 [-4, 1, 6] = true := by decide +kernel
theorem sb4_1 : ∀ q ∈ blk4_1, sub4 q = true := by
  unfold blk4_1
  exact List.forall_mem_cons.2 ⟨sub4_32, List.forall_mem_cons.2 ⟨sub4_33, List.forall_mem_cons.2 ⟨sub4_34, List.forall_mem_cons.2 ⟨sub4_35, List.forall_mem_cons.2 ⟨sub4_36, List.forall_mem_cons.2 ⟨sub4_37, List.forall_mem_cons.2 ⟨sub4_38, List.forall_mem_cons.2 ⟨sub4_39, List.forall_mem_cons.2 ⟨sub4_40, List.forall_mem_cons.2 ⟨sub4_41, List.forall_mem_cons.2 ⟨sub4_42, List.forall_mem_cons.2 ⟨sub4_43, List.forall_mem_cons.2 ⟨sub4_44, List.forall_mem_cons.2 ⟨sub4_45, List.forall_mem_cons.2 ⟨sub4_46, List.forall_mem_cons.2 ⟨sub4_47, List.forall_mem_cons.2 ⟨sub4_48, List.forall_mem_cons.2 ⟨sub4_49, List.forall_mem_cons.2 ⟨sub4_50, List.forall_mem_cons.2 ⟨sub4_51, List.forall_mem_cons.2 ⟨sub4_52, List.forall_mem_cons.2 ⟨sub4_53, List.forall_mem_cons.2 ⟨sub4_54, List.forall_mem_cons.2 ⟨sub4_55, List.forall_mem_cons.2 ⟨sub4_56, List.forall_mem_cons.2 ⟨sub4_57, List.forall_mem_cons.2 ⟨sub4_58, List.forall_mem_cons.2 ⟨sub4_59, List.forall_mem_cons.2 ⟨sub4_60, List.forall_mem_cons.2 ⟨sub4_61, List.forall_mem_cons.2 ⟨sub4_62, List.forall_mem_cons.2 ⟨sub4_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_64 : sub4 [-4, 2] = true := by decide +kernel
theorem sub4_65 : sub4 [-4, 3] = true := by decide +kernel
theorem sub4_66 : sub4 [-4, 4] = true := by decide +kernel
theorem sub4_67 : sub4 [-4, 5] = true := by decide +kernel
theorem sub4_68 : sub4 [-3, -7] = true := by decide +kernel
theorem sub4_69 : sub4 [-3, -6] = true := by decide +kernel
theorem sub4_70 : sub4 [-3, -5] = true := by decide +kernel
theorem sub4_71 : sub4 [-3, -4] = true := by decide +kernel
theorem sub4_72 : sub4 [-3, -3, -7] = true := by decide +kernel
theorem sub4_73 : sub4 [-3, -3, -6] = true := by decide +kernel
theorem sub4_74 : sub4 [-3, -3, -5] = true := by decide +kernel
theorem sub4_75 : sub4 [-3, -3, -4] = true := by decide +kernel
theorem sub4_76 : sub4 [-3, -3, -3] = true := by decide +kernel
theorem sub4_77 : sub4 [-3, -3, -2] = true := by decide +kernel
theorem sub4_78 : sub4 [-3, -3, -1] = true := by decide +kernel
theorem sub4_79 : sub4 [-3, -3, 0] = true := by decide +kernel
theorem sub4_80 : sub4 [-3, -3, 1] = true := by decide +kernel
theorem sub4_81 : sub4 [-3, -3, 2] = true := by decide +kernel
theorem sub4_82 : sub4 [-3, -3, 3] = true := by decide +kernel
theorem sub4_83 : sub4 [-3, -3, 4] = true := by decide +kernel
theorem sub4_84 : sub4 [-3, -3, 5] = true := by decide +kernel
theorem sub4_85 : sub4 [-3, -3, 6] = true := by decide +kernel
theorem sub4_86 : sub4 [-3, -2, -7] = true := by decide +kernel
theorem sub4_87 : sub4 [-3, -2, -6] = true := by decide +kernel
theorem sub4_88 : sub4 [-3, -2, -5] = true := by decide +kernel
theorem sub4_89 : sub4 [-3, -2, -4] = true := by decide +kernel
theorem sub4_90 : sub4 [-3, -2, -3] = true := by decide +kernel
theorem sub4_91 : sub4 [-3, -2, -2] = true := by decide +kernel
theorem sub4_92 : sub4 [-3, -2, -1] = true := by decide +kernel
theorem sub4_93 : sub4 [-3, -2, 0] = true := by decide +kernel
theorem sub4_94 : sub4 [-3, -2, 1] = true := by decide +kernel
theorem sub4_95 : sub4 [-3, -2, 2] = true := by decide +kernel
theorem sb4_2 : ∀ q ∈ blk4_2, sub4 q = true := by
  unfold blk4_2
  exact List.forall_mem_cons.2 ⟨sub4_64, List.forall_mem_cons.2 ⟨sub4_65, List.forall_mem_cons.2 ⟨sub4_66, List.forall_mem_cons.2 ⟨sub4_67, List.forall_mem_cons.2 ⟨sub4_68, List.forall_mem_cons.2 ⟨sub4_69, List.forall_mem_cons.2 ⟨sub4_70, List.forall_mem_cons.2 ⟨sub4_71, List.forall_mem_cons.2 ⟨sub4_72, List.forall_mem_cons.2 ⟨sub4_73, List.forall_mem_cons.2 ⟨sub4_74, List.forall_mem_cons.2 ⟨sub4_75, List.forall_mem_cons.2 ⟨sub4_76, List.forall_mem_cons.2 ⟨sub4_77, List.forall_mem_cons.2 ⟨sub4_78, List.forall_mem_cons.2 ⟨sub4_79, List.forall_mem_cons.2 ⟨sub4_80, List.forall_mem_cons.2 ⟨sub4_81, List.forall_mem_cons.2 ⟨sub4_82, List.forall_mem_cons.2 ⟨sub4_83, List.forall_mem_cons.2 ⟨sub4_84, List.forall_mem_cons.2 ⟨sub4_85, List.forall_mem_cons.2 ⟨sub4_86, List.forall_mem_cons.2 ⟨sub4_87, List.forall_mem_cons.2 ⟨sub4_88, List.forall_mem_cons.2 ⟨sub4_89, List.forall_mem_cons.2 ⟨sub4_90, List.forall_mem_cons.2 ⟨sub4_91, List.forall_mem_cons.2 ⟨sub4_92, List.forall_mem_cons.2 ⟨sub4_93, List.forall_mem_cons.2 ⟨sub4_94, List.forall_mem_cons.2 ⟨sub4_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_96 : sub4 [-3, -2, 3] = true := by decide +kernel
theorem sub4_97 : sub4 [-3, -2, 4] = true := by decide +kernel
theorem sub4_98 : sub4 [-3, -2, 5] = true := by decide +kernel
theorem sub4_99 : sub4 [-3, -2, 6] = true := by decide +kernel
theorem sub4_100 : sub4 [-3, -1, -7] = true := by decide +kernel
theorem sub4_101 : sub4 [-3, -1, -6] = true := by decide +kernel
theorem sub4_102 : sub4 [-3, -1, -5] = true := by decide +kernel
theorem sub4_103 : sub4 [-3, -1, -4] = true := by decide +kernel
theorem sub4_104 : sub4 [-3, -1, -3] = true := by decide +kernel
theorem sub4_105 : sub4 [-3, -1, -2] = true := by decide +kernel
theorem sub4_106 : sub4 [-3, -1, -1] = true := by decide +kernel
theorem sub4_107 : sub4 [-3, -1, 0] = true := by decide +kernel
theorem sub4_108 : sub4 [-3, -1, 1] = true := by decide +kernel
theorem sub4_109 : sub4 [-3, -1, 2] = true := by decide +kernel
theorem sub4_110 : sub4 [-3, -1, 3] = true := by decide +kernel
theorem sub4_111 : sub4 [-3, -1, 4] = true := by decide +kernel
theorem sub4_112 : sub4 [-3, -1, 5] = true := by decide +kernel
theorem sub4_113 : sub4 [-3, -1, 6] = true := by decide +kernel
theorem sub4_114 : sub4 [-3, -1, 7] = true := by decide +kernel
theorem sub4_115 : sub4 [-3, 0, -7] = true := by decide +kernel
theorem sub4_116 : sub4 [-3, 0, -6] = true := by decide +kernel
theorem sub4_117 : sub4 [-3, 0, -5] = true := by decide +kernel
theorem sub4_118 : sub4 [-3, 0, -4] = true := by decide +kernel
theorem sub4_119 : sub4 [-3, 0, -3] = true := by decide +kernel
theorem sub4_120 : sub4 [-3, 0, -2] = true := by decide +kernel
theorem sub4_121 : sub4 [-3, 0, -1] = true := by decide +kernel
theorem sub4_122 : sub4 [-3, 0, 0] = true := by decide +kernel
theorem sub4_123 : sub4 [-3, 0, 1] = true := by decide +kernel
theorem sub4_124 : sub4 [-3, 0, 2] = true := by decide +kernel
theorem sub4_125 : sub4 [-3, 0, 3] = true := by decide +kernel
theorem sub4_126 : sub4 [-3, 0, 4] = true := by decide +kernel
theorem sub4_127 : sub4 [-3, 0, 5] = true := by decide +kernel
theorem sb4_3 : ∀ q ∈ blk4_3, sub4 q = true := by
  unfold blk4_3
  exact List.forall_mem_cons.2 ⟨sub4_96, List.forall_mem_cons.2 ⟨sub4_97, List.forall_mem_cons.2 ⟨sub4_98, List.forall_mem_cons.2 ⟨sub4_99, List.forall_mem_cons.2 ⟨sub4_100, List.forall_mem_cons.2 ⟨sub4_101, List.forall_mem_cons.2 ⟨sub4_102, List.forall_mem_cons.2 ⟨sub4_103, List.forall_mem_cons.2 ⟨sub4_104, List.forall_mem_cons.2 ⟨sub4_105, List.forall_mem_cons.2 ⟨sub4_106, List.forall_mem_cons.2 ⟨sub4_107, List.forall_mem_cons.2 ⟨sub4_108, List.forall_mem_cons.2 ⟨sub4_109, List.forall_mem_cons.2 ⟨sub4_110, List.forall_mem_cons.2 ⟨sub4_111, List.forall_mem_cons.2 ⟨sub4_112, List.forall_mem_cons.2 ⟨sub4_113, List.forall_mem_cons.2 ⟨sub4_114, List.forall_mem_cons.2 ⟨sub4_115, List.forall_mem_cons.2 ⟨sub4_116, List.forall_mem_cons.2 ⟨sub4_117, List.forall_mem_cons.2 ⟨sub4_118, List.forall_mem_cons.2 ⟨sub4_119, List.forall_mem_cons.2 ⟨sub4_120, List.forall_mem_cons.2 ⟨sub4_121, List.forall_mem_cons.2 ⟨sub4_122, List.forall_mem_cons.2 ⟨sub4_123, List.forall_mem_cons.2 ⟨sub4_124, List.forall_mem_cons.2 ⟨sub4_125, List.forall_mem_cons.2 ⟨sub4_126, List.forall_mem_cons.2 ⟨sub4_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_128 : sub4 [-3, 0, 6] = true := by decide +kernel
theorem sub4_129 : sub4 [-3, 0, 7] = true := by decide +kernel
theorem sub4_130 : sub4 [-3, 1, -7] = true := by decide +kernel
theorem sub4_131 : sub4 [-3, 1, -6] = true := by decide +kernel
theorem sub4_132 : sub4 [-3, 1, -5] = true := by decide +kernel
theorem sub4_133 : sub4 [-3, 1, -4] = true := by decide +kernel
theorem sub4_134 : sub4 [-3, 1, -3] = true := by decide +kernel
theorem sub4_135 : sub4 [-3, 1, -2] = true := by decide +kernel
theorem sub4_136 : sub4 [-3, 1, -1] = true := by decide +kernel
theorem sub4_137 : sub4 [-3, 1, 0] = true := by decide +kernel
theorem sub4_138 : sub4 [-3, 1, 1] = true := by decide +kernel
theorem sub4_139 : sub4 [-3, 1, 2] = true := by decide +kernel
theorem sub4_140 : sub4 [-3, 1, 3] = true := by decide +kernel
theorem sub4_141 : sub4 [-3, 1, 4] = true := by decide +kernel
theorem sub4_142 : sub4 [-3, 1, 5] = true := by decide +kernel
theorem sub4_143 : sub4 [-3, 1, 6] = true := by decide +kernel
theorem sub4_144 : sub4 [-3, 1, 7] = true := by decide +kernel
theorem sub4_145 : sub4 [-3, 2, -7] = true := by decide +kernel
theorem sub4_146 : sub4 [-3, 2, -6] = true := by decide +kernel
theorem sub4_147 : sub4 [-3, 2, -5] = true := by decide +kernel
theorem sub4_148 : sub4 [-3, 2, -4] = true := by decide +kernel
theorem sub4_149 : sub4 [-3, 2, -3] = true := by decide +kernel
theorem sub4_150 : sub4 [-3, 2, -2] = true := by decide +kernel
theorem sub4_151 : sub4 [-3, 2, -1] = true := by decide +kernel
theorem sub4_152 : sub4 [-3, 2, 0] = true := by decide +kernel
theorem sub4_153 : sub4 [-3, 2, 1] = true := by decide +kernel
theorem sub4_154 : sub4 [-3, 2, 2] = true := by decide +kernel
theorem sub4_155 : sub4 [-3, 2, 3] = true := by decide +kernel
theorem sub4_156 : sub4 [-3, 2, 4] = true := by decide +kernel
theorem sub4_157 : sub4 [-3, 2, 5] = true := by decide +kernel
theorem sub4_158 : sub4 [-3, 2, 6] = true := by decide +kernel
theorem sub4_159 : sub4 [-3, 2, 7] = true := by decide +kernel
theorem sb4_4 : ∀ q ∈ blk4_4, sub4 q = true := by
  unfold blk4_4
  exact List.forall_mem_cons.2 ⟨sub4_128, List.forall_mem_cons.2 ⟨sub4_129, List.forall_mem_cons.2 ⟨sub4_130, List.forall_mem_cons.2 ⟨sub4_131, List.forall_mem_cons.2 ⟨sub4_132, List.forall_mem_cons.2 ⟨sub4_133, List.forall_mem_cons.2 ⟨sub4_134, List.forall_mem_cons.2 ⟨sub4_135, List.forall_mem_cons.2 ⟨sub4_136, List.forall_mem_cons.2 ⟨sub4_137, List.forall_mem_cons.2 ⟨sub4_138, List.forall_mem_cons.2 ⟨sub4_139, List.forall_mem_cons.2 ⟨sub4_140, List.forall_mem_cons.2 ⟨sub4_141, List.forall_mem_cons.2 ⟨sub4_142, List.forall_mem_cons.2 ⟨sub4_143, List.forall_mem_cons.2 ⟨sub4_144, List.forall_mem_cons.2 ⟨sub4_145, List.forall_mem_cons.2 ⟨sub4_146, List.forall_mem_cons.2 ⟨sub4_147, List.forall_mem_cons.2 ⟨sub4_148, List.forall_mem_cons.2 ⟨sub4_149, List.forall_mem_cons.2 ⟨sub4_150, List.forall_mem_cons.2 ⟨sub4_151, List.forall_mem_cons.2 ⟨sub4_152, List.forall_mem_cons.2 ⟨sub4_153, List.forall_mem_cons.2 ⟨sub4_154, List.forall_mem_cons.2 ⟨sub4_155, List.forall_mem_cons.2 ⟨sub4_156, List.forall_mem_cons.2 ⟨sub4_157, List.forall_mem_cons.2 ⟨sub4_158, List.forall_mem_cons.2 ⟨sub4_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C044
