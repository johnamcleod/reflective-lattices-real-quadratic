import ReflectZphi.Data.Cert5.C083.Base

namespace ReflectZphi.Data.Cert5.C083
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub3_896 : sub3 [1, 1, -5] = true := by decide +kernel
theorem sub3_897 : sub3 [1, 1, -4] = true := by decide +kernel
theorem sub3_898 : sub3 [1, 1, -3] = true := by decide +kernel
theorem sub3_899 : sub3 [1, 1, -2] = true := by decide +kernel
theorem sub3_900 : sub3 [1, 1, -1] = true := by decide +kernel
theorem sub3_901 : sub3 [1, 1, 0] = true := by decide +kernel
theorem sub3_902 : sub3 [1, 1, 1] = true := by decide +kernel
theorem sub3_903 : sub3 [1, 1, 2] = true := by decide +kernel
theorem sub3_904 : sub3 [1, 1, 3] = true := by decide +kernel
theorem sub3_905 : sub3 [1, 1, 4] = true := by decide +kernel
theorem sub3_906 : sub3 [1, 1, 5] = true := by decide +kernel
theorem sub3_907 : sub3 [1, 1, 6] = true := by decide +kernel
theorem sub3_908 : sub3 [1, 1, 7] = true := by decide +kernel
theorem sub3_909 : sub3 [1, 1, 8] = true := by decide +kernel
theorem sub3_910 : sub3 [1, 1, 9] = true := by decide +kernel
theorem sub3_911 : sub3 [1, 2, -9] = true := by decide +kernel
theorem sub3_912 : sub3 [1, 2, -8] = true := by decide +kernel
theorem sub3_913 : sub3 [1, 2, -7] = true := by decide +kernel
theorem sub3_914 : sub3 [1, 2, -6] = true := by decide +kernel
theorem sub3_915 : sub3 [1, 2, -5] = true := by decide +kernel
theorem sub3_916 : sub3 [1, 2, -4] = true := by decide +kernel
theorem sub3_917 : sub3 [1, 2, -3] = true := by decide +kernel
theorem sub3_918 : sub3 [1, 2, -2] = true := by decide +kernel
theorem sub3_919 : sub3 [1, 2, -1] = true := by decide +kernel
theorem sub3_920 : sub3 [1, 2, 0] = true := by decide +kernel
theorem sub3_921 : sub3 [1, 2, 1] = true := by decide +kernel
theorem sub3_922 : sub3 [1, 2, 2] = true := by decide +kernel
theorem sub3_923 : sub3 [1, 2, 3] = true := by decide +kernel
theorem sub3_924 : sub3 [1, 2, 4] = true := by decide +kernel
theorem sub3_925 : sub3 [1, 2, 5] = true := by decide +kernel
theorem sub3_926 : sub3 [1, 2, 6] = true := by decide +kernel
theorem sub3_927 : sub3 [1, 2, 7] = true := by decide +kernel
theorem sb3_28 : ∀ q ∈ blk3_28, sub3 q = true := by
  unfold blk3_28
  exact List.forall_mem_cons.2 ⟨sub3_896, List.forall_mem_cons.2 ⟨sub3_897, List.forall_mem_cons.2 ⟨sub3_898, List.forall_mem_cons.2 ⟨sub3_899, List.forall_mem_cons.2 ⟨sub3_900, List.forall_mem_cons.2 ⟨sub3_901, List.forall_mem_cons.2 ⟨sub3_902, List.forall_mem_cons.2 ⟨sub3_903, List.forall_mem_cons.2 ⟨sub3_904, List.forall_mem_cons.2 ⟨sub3_905, List.forall_mem_cons.2 ⟨sub3_906, List.forall_mem_cons.2 ⟨sub3_907, List.forall_mem_cons.2 ⟨sub3_908, List.forall_mem_cons.2 ⟨sub3_909, List.forall_mem_cons.2 ⟨sub3_910, List.forall_mem_cons.2 ⟨sub3_911, List.forall_mem_cons.2 ⟨sub3_912, List.forall_mem_cons.2 ⟨sub3_913, List.forall_mem_cons.2 ⟨sub3_914, List.forall_mem_cons.2 ⟨sub3_915, List.forall_mem_cons.2 ⟨sub3_916, List.forall_mem_cons.2 ⟨sub3_917, List.forall_mem_cons.2 ⟨sub3_918, List.forall_mem_cons.2 ⟨sub3_919, List.forall_mem_cons.2 ⟨sub3_920, List.forall_mem_cons.2 ⟨sub3_921, List.forall_mem_cons.2 ⟨sub3_922, List.forall_mem_cons.2 ⟨sub3_923, List.forall_mem_cons.2 ⟨sub3_924, List.forall_mem_cons.2 ⟨sub3_925, List.forall_mem_cons.2 ⟨sub3_926, List.forall_mem_cons.2 ⟨sub3_927, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_928 : sub3 [1, 2, 8] = true := by decide +kernel
theorem sub3_929 : sub3 [1, 3, -9] = true := by decide +kernel
theorem sub3_930 : sub3 [1, 3, -8] = true := by decide +kernel
theorem sub3_931 : sub3 [1, 3, -7] = true := by decide +kernel
theorem sub3_932 : sub3 [1, 3, -6] = true := by decide +kernel
theorem sub3_933 : sub3 [1, 3, -5] = true := by decide +kernel
theorem sub3_934 : sub3 [1, 3, -4] = true := by decide +kernel
theorem sub3_935 : sub3 [1, 3, -3] = true := by decide +kernel
theorem sub3_936 : sub3 [1, 3, -2] = true := by decide +kernel
theorem sub3_937 : sub3 [1, 3, -1] = true := by decide +kernel
theorem sub3_938 : sub3 [1, 3, 0] = true := by decide +kernel
theorem sub3_939 : sub3 [1, 3, 1] = true := by decide +kernel
theorem sub3_940 : sub3 [1, 3, 2] = true := by decide +kernel
theorem sub3_941 : sub3 [1, 3, 3] = true := by decide +kernel
theorem sub3_942 : sub3 [1, 3, 4] = true := by decide +kernel
theorem sub3_943 : sub3 [1, 3, 5] = true := by decide +kernel
theorem sub3_944 : sub3 [1, 3, 6] = true := by decide +kernel
theorem sub3_945 : sub3 [1, 3, 7] = true := by decide +kernel
theorem sub3_946 : sub3 [1, 4, -8] = true := by decide +kernel
theorem sub3_947 : sub3 [1, 4, -7] = true := by decide +kernel
theorem sub3_948 : sub3 [1, 4, -6] = true := by decide +kernel
theorem sub3_949 : sub3 [1, 4, -5] = true := by decide +kernel
theorem sub3_950 : sub3 [1, 4, -4] = true := by decide +kernel
theorem sub3_951 : sub3 [1, 4, -3] = true := by decide +kernel
theorem sub3_952 : sub3 [1, 4, -2] = true := by decide +kernel
theorem sub3_953 : sub3 [1, 4, -1] = true := by decide +kernel
theorem sub3_954 : sub3 [1, 4, 0] = true := by decide +kernel
theorem sub3_955 : sub3 [1, 4, 1] = true := by decide +kernel
theorem sub3_956 : sub3 [1, 4, 2] = true := by decide +kernel
theorem sub3_957 : sub3 [1, 4, 3] = true := by decide +kernel
theorem sub3_958 : sub3 [1, 4, 4] = true := by decide +kernel
theorem sub3_959 : sub3 [1, 4, 5] = true := by decide +kernel
theorem sb3_29 : ∀ q ∈ blk3_29, sub3 q = true := by
  unfold blk3_29
  exact List.forall_mem_cons.2 ⟨sub3_928, List.forall_mem_cons.2 ⟨sub3_929, List.forall_mem_cons.2 ⟨sub3_930, List.forall_mem_cons.2 ⟨sub3_931, List.forall_mem_cons.2 ⟨sub3_932, List.forall_mem_cons.2 ⟨sub3_933, List.forall_mem_cons.2 ⟨sub3_934, List.forall_mem_cons.2 ⟨sub3_935, List.forall_mem_cons.2 ⟨sub3_936, List.forall_mem_cons.2 ⟨sub3_937, List.forall_mem_cons.2 ⟨sub3_938, List.forall_mem_cons.2 ⟨sub3_939, List.forall_mem_cons.2 ⟨sub3_940, List.forall_mem_cons.2 ⟨sub3_941, List.forall_mem_cons.2 ⟨sub3_942, List.forall_mem_cons.2 ⟨sub3_943, List.forall_mem_cons.2 ⟨sub3_944, List.forall_mem_cons.2 ⟨sub3_945, List.forall_mem_cons.2 ⟨sub3_946, List.forall_mem_cons.2 ⟨sub3_947, List.forall_mem_cons.2 ⟨sub3_948, List.forall_mem_cons.2 ⟨sub3_949, List.forall_mem_cons.2 ⟨sub3_950, List.forall_mem_cons.2 ⟨sub3_951, List.forall_mem_cons.2 ⟨sub3_952, List.forall_mem_cons.2 ⟨sub3_953, List.forall_mem_cons.2 ⟨sub3_954, List.forall_mem_cons.2 ⟨sub3_955, List.forall_mem_cons.2 ⟨sub3_956, List.forall_mem_cons.2 ⟨sub3_957, List.forall_mem_cons.2 ⟨sub3_958, List.forall_mem_cons.2 ⟨sub3_959, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_960 : sub3 [1, 4, 6] = true := by decide +kernel
theorem sub3_961 : sub3 [1, 5] = true := by decide +kernel
theorem sub3_962 : sub3 [1, 6] = true := by decide +kernel
theorem sub3_963 : sub3 [2, -8] = true := by decide +kernel
theorem sub3_964 : sub3 [2, -7] = true := by decide +kernel
theorem sub3_965 : sub3 [2, -6] = true := by decide +kernel
theorem sub3_966 : sub3 [2, -5, -6] = true := by decide +kernel
theorem sub3_967 : sub3 [2, -5, -5] = true := by decide +kernel
theorem sub3_968 : sub3 [2, -5, -4] = true := by decide +kernel
theorem sub3_969 : sub3 [2, -5, -3] = true := by decide +kernel
theorem sub3_970 : sub3 [2, -5, -2] = true := by decide +kernel
theorem sub3_971 : sub3 [2, -5, -1] = true := by decide +kernel
theorem sub3_972 : sub3 [2, -5, 0] = true := by decide +kernel
theorem sub3_973 : sub3 [2, -5, 1] = true := by decide +kernel
theorem sub3_974 : sub3 [2, -5, 2] = true := by decide +kernel
theorem sub3_975 : sub3 [2, -5, 3] = true := by decide +kernel
theorem sub3_976 : sub3 [2, -5, 4] = true := by decide +kernel
theorem sub3_977 : sub3 [2, -5, 5] = true := by decide +kernel
theorem sub3_978 : sub3 [2, -5, 6] = true := by decide +kernel
theorem sub3_979 : sub3 [2, -5, 7] = true := by decide +kernel
theorem sub3_980 : sub3 [2, -5, 8] = true := by decide +kernel
theorem sub3_981 : sub3 [2, -4, -7] = true := by decide +kernel
theorem sub3_982 : sub3 [2, -4, -6] = true := by decide +kernel
theorem sub3_983 : sub3 [2, -4, -5] = true := by decide +kernel
theorem sub3_984 : sub3 [2, -4, -4] = true := by decide +kernel
theorem sub3_985 : sub3 [2, -4, -3] = true := by decide +kernel
theorem sub3_986 : sub3 [2, -4, -2] = true := by decide +kernel
theorem sub3_987 : sub3 [2, -4, -1] = true := by decide +kernel
theorem sub3_988 : sub3 [2, -4, 0] = true := by decide +kernel
theorem sub3_989 : sub3 [2, -4, 1] = true := by decide +kernel
theorem sub3_990 : sub3 [2, -4, 2] = true := by decide +kernel
theorem sub3_991 : sub3 [2, -4, 3] = true := by decide +kernel
theorem sb3_30 : ∀ q ∈ blk3_30, sub3 q = true := by
  unfold blk3_30
  exact List.forall_mem_cons.2 ⟨sub3_960, List.forall_mem_cons.2 ⟨sub3_961, List.forall_mem_cons.2 ⟨sub3_962, List.forall_mem_cons.2 ⟨sub3_963, List.forall_mem_cons.2 ⟨sub3_964, List.forall_mem_cons.2 ⟨sub3_965, List.forall_mem_cons.2 ⟨sub3_966, List.forall_mem_cons.2 ⟨sub3_967, List.forall_mem_cons.2 ⟨sub3_968, List.forall_mem_cons.2 ⟨sub3_969, List.forall_mem_cons.2 ⟨sub3_970, List.forall_mem_cons.2 ⟨sub3_971, List.forall_mem_cons.2 ⟨sub3_972, List.forall_mem_cons.2 ⟨sub3_973, List.forall_mem_cons.2 ⟨sub3_974, List.forall_mem_cons.2 ⟨sub3_975, List.forall_mem_cons.2 ⟨sub3_976, List.forall_mem_cons.2 ⟨sub3_977, List.forall_mem_cons.2 ⟨sub3_978, List.forall_mem_cons.2 ⟨sub3_979, List.forall_mem_cons.2 ⟨sub3_980, List.forall_mem_cons.2 ⟨sub3_981, List.forall_mem_cons.2 ⟨sub3_982, List.forall_mem_cons.2 ⟨sub3_983, List.forall_mem_cons.2 ⟨sub3_984, List.forall_mem_cons.2 ⟨sub3_985, List.forall_mem_cons.2 ⟨sub3_986, List.forall_mem_cons.2 ⟨sub3_987, List.forall_mem_cons.2 ⟨sub3_988, List.forall_mem_cons.2 ⟨sub3_989, List.forall_mem_cons.2 ⟨sub3_990, List.forall_mem_cons.2 ⟨sub3_991, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_992 : sub3 [2, -4, 4] = true := by decide +kernel
theorem sub3_993 : sub3 [2, -4, 5] = true := by decide +kernel
theorem sub3_994 : sub3 [2, -4, 6] = true := by decide +kernel
theorem sub3_995 : sub3 [2, -4, 7] = true := by decide +kernel
theorem sub3_996 : sub3 [2, -4, 8] = true := by decide +kernel
theorem sub3_997 : sub3 [2, -4, 9] = true := by decide +kernel
theorem sub3_998 : sub3 [2, -3, -8] = true := by decide +kernel
theorem sub3_999 : sub3 [2, -3, -7] = true := by decide +kernel
theorem sub3_1000 : sub3 [2, -3, -6] = true := by decide +kernel
theorem sub3_1001 : sub3 [2, -3, -5] = true := by decide +kernel
theorem sub3_1002 : sub3 [2, -3, -4] = true := by decide +kernel
theorem sub3_1003 : sub3 [2, -3, -3] = true := by decide +kernel
theorem sub3_1004 : sub3 [2, -3, -2] = true := by decide +kernel
theorem sub3_1005 : sub3 [2, -3, -1] = true := by decide +kernel
theorem sub3_1006 : sub3 [2, -3, 0] = true := by decide +kernel
theorem sub3_1007 : sub3 [2, -3, 1] = true := by decide +kernel
theorem sub3_1008 : sub3 [2, -3, 2] = true := by decide +kernel
theorem sub3_1009 : sub3 [2, -3, 3] = true := by decide +kernel
theorem sub3_1010 : sub3 [2, -3, 4] = true := by decide +kernel
theorem sub3_1011 : sub3 [2, -3, 5] = true := by decide +kernel
theorem sub3_1012 : sub3 [2, -3, 6] = true := by decide +kernel
theorem sub3_1013 : sub3 [2, -3, 7] = true := by decide +kernel
theorem sub3_1014 : sub3 [2, -3, 8] = true := by decide +kernel
theorem sub3_1015 : sub3 [2, -3, 9] = true := by decide +kernel
theorem sub3_1016 : sub3 [2, -2, -9] = true := by decide +kernel
theorem sub3_1017 : sub3 [2, -2, -8] = true := by decide +kernel
theorem sub3_1018 : sub3 [2, -2, -7] = true := by decide +kernel
theorem sub3_1019 : sub3 [2, -2, -6] = true := by decide +kernel
theorem sub3_1020 : sub3 [2, -2, -5] = true := by decide +kernel
theorem sub3_1021 : sub3 [2, -2, -4] = true := by decide +kernel
theorem sub3_1022 : sub3 [2, -2, -3] = true := by decide +kernel
theorem sub3_1023 : sub3 [2, -2, -2] = true := by decide +kernel
theorem sb3_31 : ∀ q ∈ blk3_31, sub3 q = true := by
  unfold blk3_31
  exact List.forall_mem_cons.2 ⟨sub3_992, List.forall_mem_cons.2 ⟨sub3_993, List.forall_mem_cons.2 ⟨sub3_994, List.forall_mem_cons.2 ⟨sub3_995, List.forall_mem_cons.2 ⟨sub3_996, List.forall_mem_cons.2 ⟨sub3_997, List.forall_mem_cons.2 ⟨sub3_998, List.forall_mem_cons.2 ⟨sub3_999, List.forall_mem_cons.2 ⟨sub3_1000, List.forall_mem_cons.2 ⟨sub3_1001, List.forall_mem_cons.2 ⟨sub3_1002, List.forall_mem_cons.2 ⟨sub3_1003, List.forall_mem_cons.2 ⟨sub3_1004, List.forall_mem_cons.2 ⟨sub3_1005, List.forall_mem_cons.2 ⟨sub3_1006, List.forall_mem_cons.2 ⟨sub3_1007, List.forall_mem_cons.2 ⟨sub3_1008, List.forall_mem_cons.2 ⟨sub3_1009, List.forall_mem_cons.2 ⟨sub3_1010, List.forall_mem_cons.2 ⟨sub3_1011, List.forall_mem_cons.2 ⟨sub3_1012, List.forall_mem_cons.2 ⟨sub3_1013, List.forall_mem_cons.2 ⟨sub3_1014, List.forall_mem_cons.2 ⟨sub3_1015, List.forall_mem_cons.2 ⟨sub3_1016, List.forall_mem_cons.2 ⟨sub3_1017, List.forall_mem_cons.2 ⟨sub3_1018, List.forall_mem_cons.2 ⟨sub3_1019, List.forall_mem_cons.2 ⟨sub3_1020, List.forall_mem_cons.2 ⟨sub3_1021, List.forall_mem_cons.2 ⟨sub3_1022, List.forall_mem_cons.2 ⟨sub3_1023, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_1024 : sub3 [2, -2, -1] = true := by decide +kernel
theorem sub3_1025 : sub3 [2, -2, 0] = true := by decide +kernel
theorem sub3_1026 : sub3 [2, -2, 1] = true := by decide +kernel
theorem sub3_1027 : sub3 [2, -2, 2] = true := by decide +kernel
theorem sub3_1028 : sub3 [2, -2, 3] = true := by decide +kernel
theorem sub3_1029 : sub3 [2, -2, 4] = true := by decide +kernel
theorem sub3_1030 : sub3 [2, -2, 5] = true := by decide +kernel
theorem sub3_1031 : sub3 [2, -2, 6] = true := by decide +kernel
theorem sub3_1032 : sub3 [2, -2, 7] = true := by decide +kernel
theorem sub3_1033 : sub3 [2, -2, 8] = true := by decide +kernel
theorem sub3_1034 : sub3 [2, -2, 9] = true := by decide +kernel
theorem sub3_1035 : sub3 [2, -1, -9] = true := by decide +kernel
theorem sub3_1036 : sub3 [2, -1, -8] = true := by decide +kernel
theorem sub3_1037 : sub3 [2, -1, -7] = true := by decide +kernel
theorem sub3_1038 : sub3 [2, -1, -6] = true := by decide +kernel
theorem sub3_1039 : sub3 [2, -1, -5] = true := by decide +kernel
theorem sub3_1040 : sub3 [2, -1, -4] = true := by decide +kernel
theorem sub3_1041 : sub3 [2, -1, -3] = true := by decide +kernel
theorem sub3_1042 : sub3 [2, -1, -2] = true := by decide +kernel
theorem sub3_1043 : sub3 [2, -1, -1] = true := by decide +kernel
theorem sub3_1044 : sub3 [2, -1, 0] = true := by decide +kernel
theorem sub3_1045 : sub3 [2, -1, 1] = true := by decide +kernel
theorem sub3_1046 : sub3 [2, -1, 2] = true := by decide +kernel
theorem sub3_1047 : sub3 [2, -1, 3] = true := by decide +kernel
theorem sub3_1048 : sub3 [2, -1, 4] = true := by decide +kernel
theorem sub3_1049 : sub3 [2, -1, 5] = true := by decide +kernel
theorem sub3_1050 : sub3 [2, -1, 6] = true := by decide +kernel
theorem sub3_1051 : sub3 [2, -1, 7] = true := by decide +kernel
theorem sub3_1052 : sub3 [2, -1, 8] = true := by decide +kernel
theorem sub3_1053 : sub3 [2, -1, 9] = true := by decide +kernel
theorem sub3_1054 : sub3 [2, 0, -9] = true := by decide +kernel
theorem sub3_1055 : sub3 [2, 0, -8] = true := by decide +kernel
theorem sb3_32 : ∀ q ∈ blk3_32, sub3 q = true := by
  unfold blk3_32
  exact List.forall_mem_cons.2 ⟨sub3_1024, List.forall_mem_cons.2 ⟨sub3_1025, List.forall_mem_cons.2 ⟨sub3_1026, List.forall_mem_cons.2 ⟨sub3_1027, List.forall_mem_cons.2 ⟨sub3_1028, List.forall_mem_cons.2 ⟨sub3_1029, List.forall_mem_cons.2 ⟨sub3_1030, List.forall_mem_cons.2 ⟨sub3_1031, List.forall_mem_cons.2 ⟨sub3_1032, List.forall_mem_cons.2 ⟨sub3_1033, List.forall_mem_cons.2 ⟨sub3_1034, List.forall_mem_cons.2 ⟨sub3_1035, List.forall_mem_cons.2 ⟨sub3_1036, List.forall_mem_cons.2 ⟨sub3_1037, List.forall_mem_cons.2 ⟨sub3_1038, List.forall_mem_cons.2 ⟨sub3_1039, List.forall_mem_cons.2 ⟨sub3_1040, List.forall_mem_cons.2 ⟨sub3_1041, List.forall_mem_cons.2 ⟨sub3_1042, List.forall_mem_cons.2 ⟨sub3_1043, List.forall_mem_cons.2 ⟨sub3_1044, List.forall_mem_cons.2 ⟨sub3_1045, List.forall_mem_cons.2 ⟨sub3_1046, List.forall_mem_cons.2 ⟨sub3_1047, List.forall_mem_cons.2 ⟨sub3_1048, List.forall_mem_cons.2 ⟨sub3_1049, List.forall_mem_cons.2 ⟨sub3_1050, List.forall_mem_cons.2 ⟨sub3_1051, List.forall_mem_cons.2 ⟨sub3_1052, List.forall_mem_cons.2 ⟨sub3_1053, List.forall_mem_cons.2 ⟨sub3_1054, List.forall_mem_cons.2 ⟨sub3_1055, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_1056 : sub3 [2, 0, -7] = true := by decide +kernel
theorem sub3_1057 : sub3 [2, 0, -6] = true := by decide +kernel
theorem sub3_1058 : sub3 [2, 0, -5] = true := by decide +kernel
theorem sub3_1059 : sub3 [2, 0, -4] = true := by decide +kernel
theorem sub3_1060 : sub3 [2, 0, -3] = true := by decide +kernel
theorem sub3_1061 : sub3 [2, 0, -2] = true := by decide +kernel
theorem sub3_1062 : sub3 [2, 0, -1] = true := by decide +kernel
theorem sub3_1063 : sub3 [2, 0, 0] = true := by decide +kernel
theorem sub3_1064 : sub3 [2, 0, 1] = true := by decide +kernel
theorem sub3_1065 : sub3 [2, 0, 2] = true := by decide +kernel
theorem sub3_1066 : sub3 [2, 0, 3] = true := by decide +kernel
theorem sub3_1067 : sub3 [2, 0, 4] = true := by decide +kernel
theorem sub3_1068 : sub3 [2, 0, 5] = true := by decide +kernel
theorem sub3_1069 : sub3 [2, 0, 6] = true := by decide +kernel
theorem sub3_1070 : sub3 [2, 0, 7] = true := by decide +kernel
theorem sub3_1071 : sub3 [2, 0, 8] = true := by decide +kernel
theorem sub3_1072 : sub3 [2, 0, 9] = true := by decide +kernel
theorem sub3_1073 : sub3 [2, 1, -9] = true := by decide +kernel
theorem sub3_1074 : sub3 [2, 1, -8] = true := by decide +kernel
theorem sub3_1075 : sub3 [2, 1, -7] = true := by decide +kernel
theorem sub3_1076 : sub3 [2, 1, -6] = true := by decide +kernel
theorem sub3_1077 : sub3 [2, 1, -5] = true := by decide +kernel
theorem sub3_1078 : sub3 [2, 1, -4] = true := by decide +kernel
theorem sub3_1079 : sub3 [2, 1, -3] = true := by decide +kernel
theorem sub3_1080 : sub3 [2, 1, -2] = true := by decide +kernel
theorem sub3_1081 : sub3 [2, 1, -1] = true := by decide +kernel
theorem sub3_1082 : sub3 [2, 1, 0] = true := by decide +kernel
theorem sub3_1083 : sub3 [2, 1, 1] = true := by decide +kernel
theorem sub3_1084 : sub3 [2, 1, 2] = true := by decide +kernel
theorem sub3_1085 : sub3 [2, 1, 3] = true := by decide +kernel
theorem sub3_1086 : sub3 [2, 1, 4] = true := by decide +kernel
theorem sub3_1087 : sub3 [2, 1, 5] = true := by decide +kernel
theorem sb3_33 : ∀ q ∈ blk3_33, sub3 q = true := by
  unfold blk3_33
  exact List.forall_mem_cons.2 ⟨sub3_1056, List.forall_mem_cons.2 ⟨sub3_1057, List.forall_mem_cons.2 ⟨sub3_1058, List.forall_mem_cons.2 ⟨sub3_1059, List.forall_mem_cons.2 ⟨sub3_1060, List.forall_mem_cons.2 ⟨sub3_1061, List.forall_mem_cons.2 ⟨sub3_1062, List.forall_mem_cons.2 ⟨sub3_1063, List.forall_mem_cons.2 ⟨sub3_1064, List.forall_mem_cons.2 ⟨sub3_1065, List.forall_mem_cons.2 ⟨sub3_1066, List.forall_mem_cons.2 ⟨sub3_1067, List.forall_mem_cons.2 ⟨sub3_1068, List.forall_mem_cons.2 ⟨sub3_1069, List.forall_mem_cons.2 ⟨sub3_1070, List.forall_mem_cons.2 ⟨sub3_1071, List.forall_mem_cons.2 ⟨sub3_1072, List.forall_mem_cons.2 ⟨sub3_1073, List.forall_mem_cons.2 ⟨sub3_1074, List.forall_mem_cons.2 ⟨sub3_1075, List.forall_mem_cons.2 ⟨sub3_1076, List.forall_mem_cons.2 ⟨sub3_1077, List.forall_mem_cons.2 ⟨sub3_1078, List.forall_mem_cons.2 ⟨sub3_1079, List.forall_mem_cons.2 ⟨sub3_1080, List.forall_mem_cons.2 ⟨sub3_1081, List.forall_mem_cons.2 ⟨sub3_1082, List.forall_mem_cons.2 ⟨sub3_1083, List.forall_mem_cons.2 ⟨sub3_1084, List.forall_mem_cons.2 ⟨sub3_1085, List.forall_mem_cons.2 ⟨sub3_1086, List.forall_mem_cons.2 ⟨sub3_1087, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_1088 : sub3 [2, 1, 6] = true := by decide +kernel
theorem sub3_1089 : sub3 [2, 1, 7] = true := by decide +kernel
theorem sub3_1090 : sub3 [2, 1, 8] = true := by decide +kernel
theorem sub3_1091 : sub3 [2, 2, -9] = true := by decide +kernel
theorem sub3_1092 : sub3 [2, 2, -8] = true := by decide +kernel
theorem sub3_1093 : sub3 [2, 2, -7] = true := by decide +kernel
theorem sub3_1094 : sub3 [2, 2, -6] = true := by decide +kernel
theorem sub3_1095 : sub3 [2, 2, -5] = true := by decide +kernel
theorem sub3_1096 : sub3 [2, 2, -4] = true := by decide +kernel
theorem sub3_1097 : sub3 [2, 2, -3] = true := by decide +kernel
theorem sub3_1098 : sub3 [2, 2, -2] = true := by decide +kernel
theorem sub3_1099 : sub3 [2, 2, -1] = true := by decide +kernel
theorem sub3_1100 : sub3 [2, 2, 0] = true := by decide +kernel
theorem sub3_1101 : sub3 [2, 2, 1] = true := by decide +kernel
theorem sub3_1102 : sub3 [2, 2, 2] = true := by decide +kernel
theorem sub3_1103 : sub3 [2, 2, 3] = true := by decide +kernel
theorem sub3_1104 : sub3 [2, 2, 4] = true := by decide +kernel
theorem sub3_1105 : sub3 [2, 2, 5] = true := by decide +kernel
theorem sub3_1106 : sub3 [2, 2, 6] = true := by decide +kernel
theorem sub3_1107 : sub3 [2, 2, 7] = true := by decide +kernel
theorem sub3_1108 : sub3 [2, 2, 8] = true := by decide +kernel
theorem sub3_1109 : sub3 [2, 3, -8] = true := by decide +kernel
theorem sub3_1110 : sub3 [2, 3, -7] = true := by decide +kernel
theorem sub3_1111 : sub3 [2, 3, -6] = true := by decide +kernel
theorem sub3_1112 : sub3 [2, 3, -5] = true := by decide +kernel
theorem sub3_1113 : sub3 [2, 3, -4] = true := by decide +kernel
theorem sub3_1114 : sub3 [2, 3, -3] = true := by decide +kernel
theorem sub3_1115 : sub3 [2, 3, -2] = true := by decide +kernel
theorem sub3_1116 : sub3 [2, 3, -1] = true := by decide +kernel
theorem sub3_1117 : sub3 [2, 3, 0] = true := by decide +kernel
theorem sub3_1118 : sub3 [2, 3, 1] = true := by decide +kernel
theorem sub3_1119 : sub3 [2, 3, 2] = true := by decide +kernel
theorem sb3_34 : ∀ q ∈ blk3_34, sub3 q = true := by
  unfold blk3_34
  exact List.forall_mem_cons.2 ⟨sub3_1088, List.forall_mem_cons.2 ⟨sub3_1089, List.forall_mem_cons.2 ⟨sub3_1090, List.forall_mem_cons.2 ⟨sub3_1091, List.forall_mem_cons.2 ⟨sub3_1092, List.forall_mem_cons.2 ⟨sub3_1093, List.forall_mem_cons.2 ⟨sub3_1094, List.forall_mem_cons.2 ⟨sub3_1095, List.forall_mem_cons.2 ⟨sub3_1096, List.forall_mem_cons.2 ⟨sub3_1097, List.forall_mem_cons.2 ⟨sub3_1098, List.forall_mem_cons.2 ⟨sub3_1099, List.forall_mem_cons.2 ⟨sub3_1100, List.forall_mem_cons.2 ⟨sub3_1101, List.forall_mem_cons.2 ⟨sub3_1102, List.forall_mem_cons.2 ⟨sub3_1103, List.forall_mem_cons.2 ⟨sub3_1104, List.forall_mem_cons.2 ⟨sub3_1105, List.forall_mem_cons.2 ⟨sub3_1106, List.forall_mem_cons.2 ⟨sub3_1107, List.forall_mem_cons.2 ⟨sub3_1108, List.forall_mem_cons.2 ⟨sub3_1109, List.forall_mem_cons.2 ⟨sub3_1110, List.forall_mem_cons.2 ⟨sub3_1111, List.forall_mem_cons.2 ⟨sub3_1112, List.forall_mem_cons.2 ⟨sub3_1113, List.forall_mem_cons.2 ⟨sub3_1114, List.forall_mem_cons.2 ⟨sub3_1115, List.forall_mem_cons.2 ⟨sub3_1116, List.forall_mem_cons.2 ⟨sub3_1117, List.forall_mem_cons.2 ⟨sub3_1118, List.forall_mem_cons.2 ⟨sub3_1119, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_1120 : sub3 [2, 3, 3] = true := by decide +kernel
theorem sub3_1121 : sub3 [2, 3, 4] = true := by decide +kernel
theorem sub3_1122 : sub3 [2, 3, 5] = true := by decide +kernel
theorem sub3_1123 : sub3 [2, 3, 6] = true := by decide +kernel
theorem sub3_1124 : sub3 [2, 3, 7] = true := by decide +kernel
theorem sub3_1125 : sub3 [2, 4] = true := by decide +kernel
theorem sub3_1126 : sub3 [2, 5] = true := by decide +kernel
theorem sub3_1127 : sub3 [3, -8] = true := by decide +kernel
theorem sub3_1128 : sub3 [3, -7] = true := by decide +kernel
theorem sub3_1129 : sub3 [3, -6] = true := by decide +kernel
theorem sub3_1130 : sub3 [3, -5, -6] = true := by decide +kernel
theorem sub3_1131 : sub3 [3, -5, -5] = true := by decide +kernel
theorem sub3_1132 : sub3 [3, -5, -4] = true := by decide +kernel
theorem sub3_1133 : sub3 [3, -5, -3] = true := by decide +kernel
theorem sub3_1134 : sub3 [3, -5, -2] = true := by decide +kernel
theorem sub3_1135 : sub3 [3, -5, -1] = true := by decide +kernel
theorem sub3_1136 : sub3 [3, -5, 0] = true := by decide +kernel
theorem sub3_1137 : sub3 [3, -5, 1] = true := by decide +kernel
theorem sub3_1138 : sub3 [3, -5, 2] = true := by decide +kernel
theorem sub3_1139 : sub3 [3, -5, 3] = true := by decide +kernel
theorem sub3_1140 : sub3 [3, -5, 4] = true := by decide +kernel
theorem sub3_1141 : sub3 [3, -5, 5] = true := by decide +kernel
theorem sub3_1142 : sub3 [3, -5, 6] = true := by decide +kernel
theorem sub3_1143 : sub3 [3, -5, 7] = true := by decide +kernel
theorem sub3_1144 : sub3 [3, -5, 8] = true := by decide +kernel
theorem sub3_1145 : sub3 [3, -4, -7] = true := by decide +kernel
theorem sub3_1146 : sub3 [3, -4, -6] = true := by decide +kernel
theorem sub3_1147 : sub3 [3, -4, -5] = true := by decide +kernel
theorem sub3_1148 : sub3 [3, -4, -4] = true := by decide +kernel
theorem sub3_1149 : sub3 [3, -4, -3] = true := by decide +kernel
theorem sub3_1150 : sub3 [3, -4, -2] = true := by decide +kernel
theorem sub3_1151 : sub3 [3, -4, -1] = true := by decide +kernel
theorem sb3_35 : ∀ q ∈ blk3_35, sub3 q = true := by
  unfold blk3_35
  exact List.forall_mem_cons.2 ⟨sub3_1120, List.forall_mem_cons.2 ⟨sub3_1121, List.forall_mem_cons.2 ⟨sub3_1122, List.forall_mem_cons.2 ⟨sub3_1123, List.forall_mem_cons.2 ⟨sub3_1124, List.forall_mem_cons.2 ⟨sub3_1125, List.forall_mem_cons.2 ⟨sub3_1126, List.forall_mem_cons.2 ⟨sub3_1127, List.forall_mem_cons.2 ⟨sub3_1128, List.forall_mem_cons.2 ⟨sub3_1129, List.forall_mem_cons.2 ⟨sub3_1130, List.forall_mem_cons.2 ⟨sub3_1131, List.forall_mem_cons.2 ⟨sub3_1132, List.forall_mem_cons.2 ⟨sub3_1133, List.forall_mem_cons.2 ⟨sub3_1134, List.forall_mem_cons.2 ⟨sub3_1135, List.forall_mem_cons.2 ⟨sub3_1136, List.forall_mem_cons.2 ⟨sub3_1137, List.forall_mem_cons.2 ⟨sub3_1138, List.forall_mem_cons.2 ⟨sub3_1139, List.forall_mem_cons.2 ⟨sub3_1140, List.forall_mem_cons.2 ⟨sub3_1141, List.forall_mem_cons.2 ⟨sub3_1142, List.forall_mem_cons.2 ⟨sub3_1143, List.forall_mem_cons.2 ⟨sub3_1144, List.forall_mem_cons.2 ⟨sub3_1145, List.forall_mem_cons.2 ⟨sub3_1146, List.forall_mem_cons.2 ⟨sub3_1147, List.forall_mem_cons.2 ⟨sub3_1148, List.forall_mem_cons.2 ⟨sub3_1149, List.forall_mem_cons.2 ⟨sub3_1150, List.forall_mem_cons.2 ⟨sub3_1151, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_1152 : sub3 [3, -4, 0] = true := by decide +kernel
theorem sub3_1153 : sub3 [3, -4, 1] = true := by decide +kernel
theorem sub3_1154 : sub3 [3, -4, 2] = true := by decide +kernel
theorem sub3_1155 : sub3 [3, -4, 3] = true := by decide +kernel
theorem sub3_1156 : sub3 [3, -4, 4] = true := by decide +kernel
theorem sub3_1157 : sub3 [3, -4, 5] = true := by decide +kernel
theorem sub3_1158 : sub3 [3, -4, 6] = true := by decide +kernel
theorem sub3_1159 : sub3 [3, -4, 7] = true := by decide +kernel
theorem sub3_1160 : sub3 [3, -4, 8] = true := by decide +kernel
theorem sub3_1161 : sub3 [3, -4, 9] = true := by decide +kernel
theorem sub3_1162 : sub3 [3, -3, -7] = true := by decide +kernel
theorem sub3_1163 : sub3 [3, -3, -6] = true := by decide +kernel
theorem sub3_1164 : sub3 [3, -3, -5] = true := by decide +kernel
theorem sub3_1165 : sub3 [3, -3, -4] = true := by decide +kernel
theorem sub3_1166 : sub3 [3, -3, -3] = true := by decide +kernel
theorem sub3_1167 : sub3 [3, -3, -2] = true := by decide +kernel
theorem sub3_1168 : sub3 [3, -3, -1] = true := by decide +kernel
theorem sub3_1169 : sub3 [3, -3, 0] = true := by decide +kernel
theorem sub3_1170 : sub3 [3, -3, 1] = true := by decide +kernel
theorem sub3_1171 : sub3 [3, -3, 2] = true := by decide +kernel
theorem sub3_1172 : sub3 [3, -3, 3] = true := by decide +kernel
theorem sub3_1173 : sub3 [3, -3, 4] = true := by decide +kernel
theorem sub3_1174 : sub3 [3, -3, 5] = true := by decide +kernel
theorem sub3_1175 : sub3 [3, -3, 6] = true := by decide +kernel
theorem sub3_1176 : sub3 [3, -3, 7] = true := by decide +kernel
theorem sub3_1177 : sub3 [3, -3, 8] = true := by decide +kernel
theorem sub3_1178 : sub3 [3, -3, 9] = true := by decide +kernel
theorem sub3_1179 : sub3 [3, -2, -8] = true := by decide +kernel
theorem sub3_1180 : sub3 [3, -2, -7] = true := by decide +kernel
theorem sub3_1181 : sub3 [3, -2, -6] = true := by decide +kernel
theorem sub3_1182 : sub3 [3, -2, -5] = true := by decide +kernel
theorem sub3_1183 : sub3 [3, -2, -4] = true := by decide +kernel
theorem sb3_36 : ∀ q ∈ blk3_36, sub3 q = true := by
  unfold blk3_36
  exact List.forall_mem_cons.2 ⟨sub3_1152, List.forall_mem_cons.2 ⟨sub3_1153, List.forall_mem_cons.2 ⟨sub3_1154, List.forall_mem_cons.2 ⟨sub3_1155, List.forall_mem_cons.2 ⟨sub3_1156, List.forall_mem_cons.2 ⟨sub3_1157, List.forall_mem_cons.2 ⟨sub3_1158, List.forall_mem_cons.2 ⟨sub3_1159, List.forall_mem_cons.2 ⟨sub3_1160, List.forall_mem_cons.2 ⟨sub3_1161, List.forall_mem_cons.2 ⟨sub3_1162, List.forall_mem_cons.2 ⟨sub3_1163, List.forall_mem_cons.2 ⟨sub3_1164, List.forall_mem_cons.2 ⟨sub3_1165, List.forall_mem_cons.2 ⟨sub3_1166, List.forall_mem_cons.2 ⟨sub3_1167, List.forall_mem_cons.2 ⟨sub3_1168, List.forall_mem_cons.2 ⟨sub3_1169, List.forall_mem_cons.2 ⟨sub3_1170, List.forall_mem_cons.2 ⟨sub3_1171, List.forall_mem_cons.2 ⟨sub3_1172, List.forall_mem_cons.2 ⟨sub3_1173, List.forall_mem_cons.2 ⟨sub3_1174, List.forall_mem_cons.2 ⟨sub3_1175, List.forall_mem_cons.2 ⟨sub3_1176, List.forall_mem_cons.2 ⟨sub3_1177, List.forall_mem_cons.2 ⟨sub3_1178, List.forall_mem_cons.2 ⟨sub3_1179, List.forall_mem_cons.2 ⟨sub3_1180, List.forall_mem_cons.2 ⟨sub3_1181, List.forall_mem_cons.2 ⟨sub3_1182, List.forall_mem_cons.2 ⟨sub3_1183, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_1184 : sub3 [3, -2, -3] = true := by decide +kernel
theorem sub3_1185 : sub3 [3, -2, -2] = true := by decide +kernel
theorem sub3_1186 : sub3 [3, -2, -1] = true := by decide +kernel
theorem sub3_1187 : sub3 [3, -2, 0] = true := by decide +kernel
theorem sub3_1188 : sub3 [3, -2, 1] = true := by decide +kernel
theorem sub3_1189 : sub3 [3, -2, 2] = true := by decide +kernel
theorem sub3_1190 : sub3 [3, -2, 3] = true := by decide +kernel
theorem sub3_1191 : sub3 [3, -2, 4] = true := by decide +kernel
theorem sub3_1192 : sub3 [3, -2, 5] = true := by decide +kernel
theorem sub3_1193 : sub3 [3, -2, 6] = true := by decide +kernel
theorem sub3_1194 : sub3 [3, -2, 7] = true := by decide +kernel
theorem sub3_1195 : sub3 [3, -2, 8] = true := by decide +kernel
theorem sub3_1196 : sub3 [3, -2, 9] = true := by decide +kernel
theorem sub3_1197 : sub3 [3, -1, -8] = true := by decide +kernel
theorem sub3_1198 : sub3 [3, -1, -7] = true := by decide +kernel
theorem sub3_1199 : sub3 [3, -1, -6] = true := by decide +kernel
theorem sub3_1200 : sub3 [3, -1, -5] = true := by decide +kernel
theorem sub3_1201 : sub3 [3, -1, -4] = true := by decide +kernel
theorem sub3_1202 : sub3 [3, -1, -3] = true := by decide +kernel
theorem sub3_1203 : sub3 [3, -1, -2] = true := by decide +kernel
theorem sub3_1204 : sub3 [3, -1, -1] = true := by decide +kernel
theorem sub3_1205 : sub3 [3, -1, 0] = true := by decide +kernel
theorem sub3_1206 : sub3 [3, -1, 1] = true := by decide +kernel
theorem sub3_1207 : sub3 [3, -1, 2] = true := by decide +kernel
theorem sub3_1208 : sub3 [3, -1, 3] = true := by decide +kernel
theorem sub3_1209 : sub3 [3, -1, 4] = true := by decide +kernel
theorem sub3_1210 : sub3 [3, -1, 5] = true := by decide +kernel
theorem sub3_1211 : sub3 [3, -1, 6] = true := by decide +kernel
theorem sub3_1212 : sub3 [3, -1, 7] = true := by decide +kernel
theorem sub3_1213 : sub3 [3, -1, 8] = true := by decide +kernel
theorem sub3_1214 : sub3 [3, -1, 9] = true := by decide +kernel
theorem sub3_1215 : sub3 [3, 0, -8] = true := by decide +kernel
theorem sb3_37 : ∀ q ∈ blk3_37, sub3 q = true := by
  unfold blk3_37
  exact List.forall_mem_cons.2 ⟨sub3_1184, List.forall_mem_cons.2 ⟨sub3_1185, List.forall_mem_cons.2 ⟨sub3_1186, List.forall_mem_cons.2 ⟨sub3_1187, List.forall_mem_cons.2 ⟨sub3_1188, List.forall_mem_cons.2 ⟨sub3_1189, List.forall_mem_cons.2 ⟨sub3_1190, List.forall_mem_cons.2 ⟨sub3_1191, List.forall_mem_cons.2 ⟨sub3_1192, List.forall_mem_cons.2 ⟨sub3_1193, List.forall_mem_cons.2 ⟨sub3_1194, List.forall_mem_cons.2 ⟨sub3_1195, List.forall_mem_cons.2 ⟨sub3_1196, List.forall_mem_cons.2 ⟨sub3_1197, List.forall_mem_cons.2 ⟨sub3_1198, List.forall_mem_cons.2 ⟨sub3_1199, List.forall_mem_cons.2 ⟨sub3_1200, List.forall_mem_cons.2 ⟨sub3_1201, List.forall_mem_cons.2 ⟨sub3_1202, List.forall_mem_cons.2 ⟨sub3_1203, List.forall_mem_cons.2 ⟨sub3_1204, List.forall_mem_cons.2 ⟨sub3_1205, List.forall_mem_cons.2 ⟨sub3_1206, List.forall_mem_cons.2 ⟨sub3_1207, List.forall_mem_cons.2 ⟨sub3_1208, List.forall_mem_cons.2 ⟨sub3_1209, List.forall_mem_cons.2 ⟨sub3_1210, List.forall_mem_cons.2 ⟨sub3_1211, List.forall_mem_cons.2 ⟨sub3_1212, List.forall_mem_cons.2 ⟨sub3_1213, List.forall_mem_cons.2 ⟨sub3_1214, List.forall_mem_cons.2 ⟨sub3_1215, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_1216 : sub3 [3, 0, -7] = true := by decide +kernel
theorem sub3_1217 : sub3 [3, 0, -6] = true := by decide +kernel
theorem sub3_1218 : sub3 [3, 0, -5] = true := by decide +kernel
theorem sub3_1219 : sub3 [3, 0, -4] = true := by decide +kernel
theorem sub3_1220 : sub3 [3, 0, -3] = true := by decide +kernel
theorem sub3_1221 : sub3 [3, 0, -2] = true := by decide +kernel
theorem sub3_1222 : sub3 [3, 0, -1] = true := by decide +kernel
theorem sub3_1223 : sub3 [3, 0, 0] = true := by decide +kernel
theorem sub3_1224 : sub3 [3, 0, 1] = true := by decide +kernel
theorem sub3_1225 : sub3 [3, 0, 2] = true := by decide +kernel
theorem sub3_1226 : sub3 [3, 0, 3] = true := by decide +kernel
theorem sub3_1227 : sub3 [3, 0, 4] = true := by decide +kernel
theorem sub3_1228 : sub3 [3, 0, 5] = true := by decide +kernel
theorem sub3_1229 : sub3 [3, 0, 6] = true := by decide +kernel
theorem sub3_1230 : sub3 [3, 0, 7] = true := by decide +kernel
theorem sub3_1231 : sub3 [3, 0, 8] = true := by decide +kernel
theorem sub3_1232 : sub3 [3, 1, -8] = true := by decide +kernel
theorem sub3_1233 : sub3 [3, 1, -7] = true := by decide +kernel
theorem sub3_1234 : sub3 [3, 1, -6] = true := by decide +kernel
theorem sub3_1235 : sub3 [3, 1, -5] = true := by decide +kernel
theorem sub3_1236 : sub3 [3, 1, -4] = true := by decide +kernel
theorem sub3_1237 : sub3 [3, 1, -3] = true := by decide +kernel
theorem sub3_1238 : sub3 [3, 1, -2] = true := by decide +kernel
theorem sub3_1239 : sub3 [3, 1, -1] = true := by decide +kernel
theorem sub3_1240 : sub3 [3, 1, 0] = true := by decide +kernel
theorem sub3_1241 : sub3 [3, 1, 1] = true := by decide +kernel
theorem sub3_1242 : sub3 [3, 1, 2] = true := by decide +kernel
theorem sub3_1243 : sub3 [3, 1, 3] = true := by decide +kernel
theorem sub3_1244 : sub3 [3, 1, 4] = true := by decide +kernel
theorem sub3_1245 : sub3 [3, 1, 5] = true := by decide +kernel
theorem sub3_1246 : sub3 [3, 1, 6] = true := by decide +kernel
theorem sub3_1247 : sub3 [3, 1, 7] = true := by decide +kernel
theorem sb3_38 : ∀ q ∈ blk3_38, sub3 q = true := by
  unfold blk3_38
  exact List.forall_mem_cons.2 ⟨sub3_1216, List.forall_mem_cons.2 ⟨sub3_1217, List.forall_mem_cons.2 ⟨sub3_1218, List.forall_mem_cons.2 ⟨sub3_1219, List.forall_mem_cons.2 ⟨sub3_1220, List.forall_mem_cons.2 ⟨sub3_1221, List.forall_mem_cons.2 ⟨sub3_1222, List.forall_mem_cons.2 ⟨sub3_1223, List.forall_mem_cons.2 ⟨sub3_1224, List.forall_mem_cons.2 ⟨sub3_1225, List.forall_mem_cons.2 ⟨sub3_1226, List.forall_mem_cons.2 ⟨sub3_1227, List.forall_mem_cons.2 ⟨sub3_1228, List.forall_mem_cons.2 ⟨sub3_1229, List.forall_mem_cons.2 ⟨sub3_1230, List.forall_mem_cons.2 ⟨sub3_1231, List.forall_mem_cons.2 ⟨sub3_1232, List.forall_mem_cons.2 ⟨sub3_1233, List.forall_mem_cons.2 ⟨sub3_1234, List.forall_mem_cons.2 ⟨sub3_1235, List.forall_mem_cons.2 ⟨sub3_1236, List.forall_mem_cons.2 ⟨sub3_1237, List.forall_mem_cons.2 ⟨sub3_1238, List.forall_mem_cons.2 ⟨sub3_1239, List.forall_mem_cons.2 ⟨sub3_1240, List.forall_mem_cons.2 ⟨sub3_1241, List.forall_mem_cons.2 ⟨sub3_1242, List.forall_mem_cons.2 ⟨sub3_1243, List.forall_mem_cons.2 ⟨sub3_1244, List.forall_mem_cons.2 ⟨sub3_1245, List.forall_mem_cons.2 ⟨sub3_1246, List.forall_mem_cons.2 ⟨sub3_1247, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_1248 : sub3 [3, 1, 8] = true := by decide +kernel
theorem sub3_1249 : sub3 [3, 2, -7] = true := by decide +kernel
theorem sub3_1250 : sub3 [3, 2, -6] = true := by decide +kernel
theorem sub3_1251 : sub3 [3, 2, -5] = true := by decide +kernel
theorem sub3_1252 : sub3 [3, 2, -4] = true := by decide +kernel
theorem sub3_1253 : sub3 [3, 2, -3] = true := by decide +kernel
theorem sub3_1254 : sub3 [3, 2, -2] = true := by decide +kernel
theorem sub3_1255 : sub3 [3, 2, -1] = true := by decide +kernel
theorem sub3_1256 : sub3 [3, 2, 0] = true := by decide +kernel
theorem sub3_1257 : sub3 [3, 2, 1] = true := by decide +kernel
theorem sub3_1258 : sub3 [3, 2, 2] = true := by decide +kernel
theorem sub3_1259 : sub3 [3, 2, 3] = true := by decide +kernel
theorem sub3_1260 : sub3 [3, 2, 4] = true := by decide +kernel
theorem sub3_1261 : sub3 [3, 2, 5] = true := by decide +kernel
theorem sub3_1262 : sub3 [3, 2, 6] = true := by decide +kernel
theorem sub3_1263 : sub3 [3, 2, 7] = true := by decide +kernel
theorem sub3_1264 : sub3 [3, 3] = true := by decide +kernel
theorem sub3_1265 : sub3 [3, 4] = true := by decide +kernel
theorem sub3_1266 : sub3 [4, -8] = true := by decide +kernel
theorem sub3_1267 : sub3 [4, -7] = true := by decide +kernel
theorem sub3_1268 : sub3 [4, -6] = true := by decide +kernel
theorem sub3_1269 : sub3 [4, -5] = true := by decide +kernel
theorem sub3_1270 : sub3 [4, -4, -5] = true := by decide +kernel
theorem sub3_1271 : sub3 [4, -4, -4] = true := by decide +kernel
theorem sub3_1272 : sub3 [4, -4, -3] = true := by decide +kernel
theorem sub3_1273 : sub3 [4, -4, -2] = true := by decide +kernel
theorem sub3_1274 : sub3 [4, -4, -1] = true := by decide +kernel
theorem sub3_1275 : sub3 [4, -4, 0] = true := by decide +kernel
theorem sub3_1276 : sub3 [4, -4, 1] = true := by decide +kernel
theorem sub3_1277 : sub3 [4, -4, 2] = true := by decide +kernel
theorem sub3_1278 : sub3 [4, -4, 3] = true := by decide +kernel
theorem sub3_1279 : sub3 [4, -4, 4] = true := by decide +kernel
theorem sb3_39 : ∀ q ∈ blk3_39, sub3 q = true := by
  unfold blk3_39
  exact List.forall_mem_cons.2 ⟨sub3_1248, List.forall_mem_cons.2 ⟨sub3_1249, List.forall_mem_cons.2 ⟨sub3_1250, List.forall_mem_cons.2 ⟨sub3_1251, List.forall_mem_cons.2 ⟨sub3_1252, List.forall_mem_cons.2 ⟨sub3_1253, List.forall_mem_cons.2 ⟨sub3_1254, List.forall_mem_cons.2 ⟨sub3_1255, List.forall_mem_cons.2 ⟨sub3_1256, List.forall_mem_cons.2 ⟨sub3_1257, List.forall_mem_cons.2 ⟨sub3_1258, List.forall_mem_cons.2 ⟨sub3_1259, List.forall_mem_cons.2 ⟨sub3_1260, List.forall_mem_cons.2 ⟨sub3_1261, List.forall_mem_cons.2 ⟨sub3_1262, List.forall_mem_cons.2 ⟨sub3_1263, List.forall_mem_cons.2 ⟨sub3_1264, List.forall_mem_cons.2 ⟨sub3_1265, List.forall_mem_cons.2 ⟨sub3_1266, List.forall_mem_cons.2 ⟨sub3_1267, List.forall_mem_cons.2 ⟨sub3_1268, List.forall_mem_cons.2 ⟨sub3_1269, List.forall_mem_cons.2 ⟨sub3_1270, List.forall_mem_cons.2 ⟨sub3_1271, List.forall_mem_cons.2 ⟨sub3_1272, List.forall_mem_cons.2 ⟨sub3_1273, List.forall_mem_cons.2 ⟨sub3_1274, List.forall_mem_cons.2 ⟨sub3_1275, List.forall_mem_cons.2 ⟨sub3_1276, List.forall_mem_cons.2 ⟨sub3_1277, List.forall_mem_cons.2 ⟨sub3_1278, List.forall_mem_cons.2 ⟨sub3_1279, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_1280 : sub3 [4, -4, 5] = true := by decide +kernel
theorem sub3_1281 : sub3 [4, -4, 6] = true := by decide +kernel
theorem sub3_1282 : sub3 [4, -4, 7] = true := by decide +kernel
theorem sub3_1283 : sub3 [4, -4, 8] = true := by decide +kernel
theorem sub3_1284 : sub3 [4, -3, -6] = true := by decide +kernel
theorem sub3_1285 : sub3 [4, -3, -5] = true := by decide +kernel
theorem sub3_1286 : sub3 [4, -3, -4] = true := by decide +kernel
theorem sub3_1287 : sub3 [4, -3, -3] = true := by decide +kernel
theorem sub3_1288 : sub3 [4, -3, -2] = true := by decide +kernel
theorem sub3_1289 : sub3 [4, -3, -1] = true := by decide +kernel
theorem sub3_1290 : sub3 [4, -3, 0] = true := by decide +kernel
theorem sub3_1291 : sub3 [4, -3, 1] = true := by decide +kernel
theorem sub3_1292 : sub3 [4, -3, 2] = true := by decide +kernel
theorem sub3_1293 : sub3 [4, -3, 3] = true := by decide +kernel
theorem sub3_1294 : sub3 [4, -3, 4] = true := by decide +kernel
theorem sub3_1295 : sub3 [4, -3, 5] = true := by decide +kernel
theorem sub3_1296 : sub3 [4, -3, 6] = true := by decide +kernel
theorem sub3_1297 : sub3 [4, -3, 7] = true := by decide +kernel
theorem sub3_1298 : sub3 [4, -3, 8] = true := by decide +kernel
theorem sub3_1299 : sub3 [4, -2, -6] = true := by decide +kernel
theorem sub3_1300 : sub3 [4, -2, -5] = true := by decide +kernel
theorem sub3_1301 : sub3 [4, -2, -4] = true := by decide +kernel
theorem sub3_1302 : sub3 [4, -2, -3] = true := by decide +kernel
theorem sub3_1303 : sub3 [4, -2, -2] = true := by decide +kernel
theorem sub3_1304 : sub3 [4, -2, -1] = true := by decide +kernel
theorem sub3_1305 : sub3 [4, -2, 0] = true := by decide +kernel
theorem sub3_1306 : sub3 [4, -2, 1] = true := by decide +kernel
theorem sub3_1307 : sub3 [4, -2, 2] = true := by decide +kernel
theorem sub3_1308 : sub3 [4, -2, 3] = true := by decide +kernel
theorem sub3_1309 : sub3 [4, -2, 4] = true := by decide +kernel
theorem sub3_1310 : sub3 [4, -2, 5] = true := by decide +kernel
theorem sub3_1311 : sub3 [4, -2, 6] = true := by decide +kernel
theorem sb3_40 : ∀ q ∈ blk3_40, sub3 q = true := by
  unfold blk3_40
  exact List.forall_mem_cons.2 ⟨sub3_1280, List.forall_mem_cons.2 ⟨sub3_1281, List.forall_mem_cons.2 ⟨sub3_1282, List.forall_mem_cons.2 ⟨sub3_1283, List.forall_mem_cons.2 ⟨sub3_1284, List.forall_mem_cons.2 ⟨sub3_1285, List.forall_mem_cons.2 ⟨sub3_1286, List.forall_mem_cons.2 ⟨sub3_1287, List.forall_mem_cons.2 ⟨sub3_1288, List.forall_mem_cons.2 ⟨sub3_1289, List.forall_mem_cons.2 ⟨sub3_1290, List.forall_mem_cons.2 ⟨sub3_1291, List.forall_mem_cons.2 ⟨sub3_1292, List.forall_mem_cons.2 ⟨sub3_1293, List.forall_mem_cons.2 ⟨sub3_1294, List.forall_mem_cons.2 ⟨sub3_1295, List.forall_mem_cons.2 ⟨sub3_1296, List.forall_mem_cons.2 ⟨sub3_1297, List.forall_mem_cons.2 ⟨sub3_1298, List.forall_mem_cons.2 ⟨sub3_1299, List.forall_mem_cons.2 ⟨sub3_1300, List.forall_mem_cons.2 ⟨sub3_1301, List.forall_mem_cons.2 ⟨sub3_1302, List.forall_mem_cons.2 ⟨sub3_1303, List.forall_mem_cons.2 ⟨sub3_1304, List.forall_mem_cons.2 ⟨sub3_1305, List.forall_mem_cons.2 ⟨sub3_1306, List.forall_mem_cons.2 ⟨sub3_1307, List.forall_mem_cons.2 ⟨sub3_1308, List.forall_mem_cons.2 ⟨sub3_1309, List.forall_mem_cons.2 ⟨sub3_1310, List.forall_mem_cons.2 ⟨sub3_1311, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_1312 : sub3 [4, -2, 7] = true := by decide +kernel
theorem sub3_1313 : sub3 [4, -2, 8] = true := by decide +kernel
theorem sub3_1314 : sub3 [4, -1, -7] = true := by decide +kernel
theorem sub3_1315 : sub3 [4, -1, -6] = true := by decide +kernel
theorem sub3_1316 : sub3 [4, -1, -5] = true := by decide +kernel
theorem sub3_1317 : sub3 [4, -1, -4] = true := by decide +kernel
theorem sub3_1318 : sub3 [4, -1, -3] = true := by decide +kernel
theorem sub3_1319 : sub3 [4, -1, -2] = true := by decide +kernel
theorem sub3_1320 : sub3 [4, -1, -1] = true := by decide +kernel
theorem sub3_1321 : sub3 [4, -1, 0] = true := by decide +kernel
theorem sub3_1322 : sub3 [4, -1, 1] = true := by decide +kernel
theorem sub3_1323 : sub3 [4, -1, 2] = true := by decide +kernel
theorem sub3_1324 : sub3 [4, -1, 3] = true := by decide +kernel
theorem sub3_1325 : sub3 [4, -1, 4] = true := by decide +kernel
theorem sub3_1326 : sub3 [4, -1, 5] = true := by decide +kernel
theorem sub3_1327 : sub3 [4, -1, 6] = true := by decide +kernel
theorem sub3_1328 : sub3 [4, -1, 7] = true := by decide +kernel
theorem sub3_1329 : sub3 [4, -1, 8] = true := by decide +kernel
theorem sub3_1330 : sub3 [4, 0, -6] = true := by decide +kernel
theorem sub3_1331 : sub3 [4, 0, -5] = true := by decide +kernel
theorem sub3_1332 : sub3 [4, 0, -4] = true := by decide +kernel
theorem sub3_1333 : sub3 [4, 0, -3] = true := by decide +kernel
theorem sub3_1334 : sub3 [4, 0, -2] = true := by decide +kernel
theorem sub3_1335 : sub3 [4, 0, -1] = true := by decide +kernel
theorem sub3_1336 : sub3 [4, 0, 0] = true := by decide +kernel
theorem sub3_1337 : sub3 [4, 0, 1] = true := by decide +kernel
theorem sub3_1338 : sub3 [4, 0, 2] = true := by decide +kernel
theorem sub3_1339 : sub3 [4, 0, 3] = true := by decide +kernel
theorem sub3_1340 : sub3 [4, 0, 4] = true := by decide +kernel
theorem sub3_1341 : sub3 [4, 0, 5] = true := by decide +kernel
theorem sub3_1342 : sub3 [4, 0, 6] = true := by decide +kernel
theorem sub3_1343 : sub3 [4, 0, 7] = true := by decide +kernel
theorem sb3_41 : ∀ q ∈ blk3_41, sub3 q = true := by
  unfold blk3_41
  exact List.forall_mem_cons.2 ⟨sub3_1312, List.forall_mem_cons.2 ⟨sub3_1313, List.forall_mem_cons.2 ⟨sub3_1314, List.forall_mem_cons.2 ⟨sub3_1315, List.forall_mem_cons.2 ⟨sub3_1316, List.forall_mem_cons.2 ⟨sub3_1317, List.forall_mem_cons.2 ⟨sub3_1318, List.forall_mem_cons.2 ⟨sub3_1319, List.forall_mem_cons.2 ⟨sub3_1320, List.forall_mem_cons.2 ⟨sub3_1321, List.forall_mem_cons.2 ⟨sub3_1322, List.forall_mem_cons.2 ⟨sub3_1323, List.forall_mem_cons.2 ⟨sub3_1324, List.forall_mem_cons.2 ⟨sub3_1325, List.forall_mem_cons.2 ⟨sub3_1326, List.forall_mem_cons.2 ⟨sub3_1327, List.forall_mem_cons.2 ⟨sub3_1328, List.forall_mem_cons.2 ⟨sub3_1329, List.forall_mem_cons.2 ⟨sub3_1330, List.forall_mem_cons.2 ⟨sub3_1331, List.forall_mem_cons.2 ⟨sub3_1332, List.forall_mem_cons.2 ⟨sub3_1333, List.forall_mem_cons.2 ⟨sub3_1334, List.forall_mem_cons.2 ⟨sub3_1335, List.forall_mem_cons.2 ⟨sub3_1336, List.forall_mem_cons.2 ⟨sub3_1337, List.forall_mem_cons.2 ⟨sub3_1338, List.forall_mem_cons.2 ⟨sub3_1339, List.forall_mem_cons.2 ⟨sub3_1340, List.forall_mem_cons.2 ⟨sub3_1341, List.forall_mem_cons.2 ⟨sub3_1342, List.forall_mem_cons.2 ⟨sub3_1343, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C083
