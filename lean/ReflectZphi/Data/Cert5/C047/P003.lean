import ReflectZphi.Data.Cert5.C047.Base

namespace ReflectZphi.Data.Cert5.C047
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub3_928 : sub3 [2, 0, -6] = true := by decide +kernel
theorem sub3_929 : sub3 [2, 0, -5] = true := by decide +kernel
theorem sub3_930 : sub3 [2, 0, -4] = true := by decide +kernel
theorem sub3_931 : sub3 [2, 0, -3] = true := by decide +kernel
theorem sub3_932 : sub3 [2, 0, -2] = true := by decide +kernel
theorem sub3_933 : sub3 [2, 0, -1] = true := by decide +kernel
theorem sub3_934 : sub3 [2, 0, 0] = true := by decide +kernel
theorem sub3_935 : sub3 [2, 0, 1] = true := by decide +kernel
theorem sub3_936 : sub3 [2, 0, 2] = true := by decide +kernel
theorem sub3_937 : sub3 [2, 0, 3] = true := by decide +kernel
theorem sub3_938 : sub3 [2, 0, 4] = true := by decide +kernel
theorem sub3_939 : sub3 [2, 0, 5] = true := by decide +kernel
theorem sub3_940 : sub3 [2, 0, 6] = true := by decide +kernel
theorem sub3_941 : sub3 [2, 0, 7] = true := by decide +kernel
theorem sub3_942 : sub3 [2, 0, 8] = true := by decide +kernel
theorem sub3_943 : sub3 [2, 1, -9] = true := by decide +kernel
theorem sub3_944 : sub3 [2, 1, -8] = true := by decide +kernel
theorem sub3_945 : sub3 [2, 1, -7] = true := by decide +kernel
theorem sub3_946 : sub3 [2, 1, -6] = true := by decide +kernel
theorem sub3_947 : sub3 [2, 1, -5] = true := by decide +kernel
theorem sub3_948 : sub3 [2, 1, -4] = true := by decide +kernel
theorem sub3_949 : sub3 [2, 1, -3] = true := by decide +kernel
theorem sub3_950 : sub3 [2, 1, -2] = true := by decide +kernel
theorem sub3_951 : sub3 [2, 1, -1] = true := by decide +kernel
theorem sub3_952 : sub3 [2, 1, 0] = true := by decide +kernel
theorem sub3_953 : sub3 [2, 1, 1] = true := by decide +kernel
theorem sub3_954 : sub3 [2, 1, 2] = true := by decide +kernel
theorem sub3_955 : sub3 [2, 1, 3] = true := by decide +kernel
theorem sub3_956 : sub3 [2, 1, 4] = true := by decide +kernel
theorem sub3_957 : sub3 [2, 1, 5] = true := by decide +kernel
theorem sub3_958 : sub3 [2, 1, 6] = true := by decide +kernel
theorem sub3_959 : sub3 [2, 1, 7] = true := by decide +kernel
theorem sb3_29 : ∀ q ∈ blk3_29, sub3 q = true := by
  unfold blk3_29
  exact List.forall_mem_cons.2 ⟨sub3_928, List.forall_mem_cons.2 ⟨sub3_929, List.forall_mem_cons.2 ⟨sub3_930, List.forall_mem_cons.2 ⟨sub3_931, List.forall_mem_cons.2 ⟨sub3_932, List.forall_mem_cons.2 ⟨sub3_933, List.forall_mem_cons.2 ⟨sub3_934, List.forall_mem_cons.2 ⟨sub3_935, List.forall_mem_cons.2 ⟨sub3_936, List.forall_mem_cons.2 ⟨sub3_937, List.forall_mem_cons.2 ⟨sub3_938, List.forall_mem_cons.2 ⟨sub3_939, List.forall_mem_cons.2 ⟨sub3_940, List.forall_mem_cons.2 ⟨sub3_941, List.forall_mem_cons.2 ⟨sub3_942, List.forall_mem_cons.2 ⟨sub3_943, List.forall_mem_cons.2 ⟨sub3_944, List.forall_mem_cons.2 ⟨sub3_945, List.forall_mem_cons.2 ⟨sub3_946, List.forall_mem_cons.2 ⟨sub3_947, List.forall_mem_cons.2 ⟨sub3_948, List.forall_mem_cons.2 ⟨sub3_949, List.forall_mem_cons.2 ⟨sub3_950, List.forall_mem_cons.2 ⟨sub3_951, List.forall_mem_cons.2 ⟨sub3_952, List.forall_mem_cons.2 ⟨sub3_953, List.forall_mem_cons.2 ⟨sub3_954, List.forall_mem_cons.2 ⟨sub3_955, List.forall_mem_cons.2 ⟨sub3_956, List.forall_mem_cons.2 ⟨sub3_957, List.forall_mem_cons.2 ⟨sub3_958, List.forall_mem_cons.2 ⟨sub3_959, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_960 : sub3 [2, 1, 8] = true := by decide +kernel
theorem sub3_961 : sub3 [2, 2, -8] = true := by decide +kernel
theorem sub3_962 : sub3 [2, 2, -7] = true := by decide +kernel
theorem sub3_963 : sub3 [2, 2, -6] = true := by decide +kernel
theorem sub3_964 : sub3 [2, 2, -5] = true := by decide +kernel
theorem sub3_965 : sub3 [2, 2, -4] = true := by decide +kernel
theorem sub3_966 : sub3 [2, 2, -3] = true := by decide +kernel
theorem sub3_967 : sub3 [2, 2, -2] = true := by decide +kernel
theorem sub3_968 : sub3 [2, 2, -1] = true := by decide +kernel
theorem sub3_969 : sub3 [2, 2, 0] = true := by decide +kernel
theorem sub3_970 : sub3 [2, 2, 1] = true := by decide +kernel
theorem sub3_971 : sub3 [2, 2, 2] = true := by decide +kernel
theorem sub3_972 : sub3 [2, 2, 3] = true := by decide +kernel
theorem sub3_973 : sub3 [2, 2, 4] = true := by decide +kernel
theorem sub3_974 : sub3 [2, 2, 5] = true := by decide +kernel
theorem sub3_975 : sub3 [2, 2, 6] = true := by decide +kernel
theorem sub3_976 : sub3 [2, 2, 7] = true := by decide +kernel
theorem sub3_977 : sub3 [2, 2, 8] = true := by decide +kernel
theorem sub3_978 : sub3 [2, 3, -8] = true := by decide +kernel
theorem sub3_979 : sub3 [2, 3, -7] = true := by decide +kernel
theorem sub3_980 : sub3 [2, 3, -6] = true := by decide +kernel
theorem sub3_981 : sub3 [2, 3, -5] = true := by decide +kernel
theorem sub3_982 : sub3 [2, 3, -4] = true := by decide +kernel
theorem sub3_983 : sub3 [2, 3, -3] = true := by decide +kernel
theorem sub3_984 : sub3 [2, 3, -2] = true := by decide +kernel
theorem sub3_985 : sub3 [2, 3, -1] = true := by decide +kernel
theorem sub3_986 : sub3 [2, 3, 0] = true := by decide +kernel
theorem sub3_987 : sub3 [2, 3, 1] = true := by decide +kernel
theorem sub3_988 : sub3 [2, 3, 2] = true := by decide +kernel
theorem sub3_989 : sub3 [2, 3, 3] = true := by decide +kernel
theorem sub3_990 : sub3 [2, 3, 4] = true := by decide +kernel
theorem sub3_991 : sub3 [2, 3, 5] = true := by decide +kernel
theorem sb3_30 : ∀ q ∈ blk3_30, sub3 q = true := by
  unfold blk3_30
  exact List.forall_mem_cons.2 ⟨sub3_960, List.forall_mem_cons.2 ⟨sub3_961, List.forall_mem_cons.2 ⟨sub3_962, List.forall_mem_cons.2 ⟨sub3_963, List.forall_mem_cons.2 ⟨sub3_964, List.forall_mem_cons.2 ⟨sub3_965, List.forall_mem_cons.2 ⟨sub3_966, List.forall_mem_cons.2 ⟨sub3_967, List.forall_mem_cons.2 ⟨sub3_968, List.forall_mem_cons.2 ⟨sub3_969, List.forall_mem_cons.2 ⟨sub3_970, List.forall_mem_cons.2 ⟨sub3_971, List.forall_mem_cons.2 ⟨sub3_972, List.forall_mem_cons.2 ⟨sub3_973, List.forall_mem_cons.2 ⟨sub3_974, List.forall_mem_cons.2 ⟨sub3_975, List.forall_mem_cons.2 ⟨sub3_976, List.forall_mem_cons.2 ⟨sub3_977, List.forall_mem_cons.2 ⟨sub3_978, List.forall_mem_cons.2 ⟨sub3_979, List.forall_mem_cons.2 ⟨sub3_980, List.forall_mem_cons.2 ⟨sub3_981, List.forall_mem_cons.2 ⟨sub3_982, List.forall_mem_cons.2 ⟨sub3_983, List.forall_mem_cons.2 ⟨sub3_984, List.forall_mem_cons.2 ⟨sub3_985, List.forall_mem_cons.2 ⟨sub3_986, List.forall_mem_cons.2 ⟨sub3_987, List.forall_mem_cons.2 ⟨sub3_988, List.forall_mem_cons.2 ⟨sub3_989, List.forall_mem_cons.2 ⟨sub3_990, List.forall_mem_cons.2 ⟨sub3_991, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_992 : sub3 [2, 3, 6] = true := by decide +kernel
theorem sub3_993 : sub3 [2, 3, 7] = true := by decide +kernel
theorem sub3_994 : sub3 [2, 3, 8] = true := by decide +kernel
theorem sub3_995 : sub3 [2, 4] = true := by decide +kernel
theorem sub3_996 : sub3 [2, 5] = true := by decide +kernel
theorem sub3_997 : sub3 [2, 6] = true := by decide +kernel
theorem sub3_998 : sub3 [3, -7] = true := by decide +kernel
theorem sub3_999 : sub3 [3, -6] = true := by decide +kernel
theorem sub3_1000 : sub3 [3, -5] = true := by decide +kernel
theorem sub3_1001 : sub3 [3, -4] = true := by decide +kernel
theorem sub3_1002 : sub3 [3, -3, -9] = true := by decide +kernel
theorem sub3_1003 : sub3 [3, -3, -8] = true := by decide +kernel
theorem sub3_1004 : sub3 [3, -3, -7] = true := by decide +kernel
theorem sub3_1005 : sub3 [3, -3, -6] = true := by decide +kernel
theorem sub3_1006 : sub3 [3, -3, -5] = true := by decide +kernel
theorem sub3_1007 : sub3 [3, -3, -4] = true := by decide +kernel
theorem sub3_1008 : sub3 [3, -3, -3] = true := by decide +kernel
theorem sub3_1009 : sub3 [3, -3, -2] = true := by decide +kernel
theorem sub3_1010 : sub3 [3, -3, -1] = true := by decide +kernel
theorem sub3_1011 : sub3 [3, -3, 0] = true := by decide +kernel
theorem sub3_1012 : sub3 [3, -3, 1] = true := by decide +kernel
theorem sub3_1013 : sub3 [3, -3, 2] = true := by decide +kernel
theorem sub3_1014 : sub3 [3, -3, 3] = true := by decide +kernel
theorem sub3_1015 : sub3 [3, -3, 4] = true := by decide +kernel
theorem sub3_1016 : sub3 [3, -3, 5] = true := by decide +kernel
theorem sub3_1017 : sub3 [3, -3, 6] = true := by decide +kernel
theorem sub3_1018 : sub3 [3, -2, -9] = true := by decide +kernel
theorem sub3_1019 : sub3 [3, -2, -8] = true := by decide +kernel
theorem sub3_1020 : sub3 [3, -2, -7] = true := by decide +kernel
theorem sub3_1021 : sub3 [3, -2, -6] = true := by decide +kernel
theorem sub3_1022 : sub3 [3, -2, -5] = true := by decide +kernel
theorem sub3_1023 : sub3 [3, -2, -4] = true := by decide +kernel
theorem sb3_31 : ∀ q ∈ blk3_31, sub3 q = true := by
  unfold blk3_31
  exact List.forall_mem_cons.2 ⟨sub3_992, List.forall_mem_cons.2 ⟨sub3_993, List.forall_mem_cons.2 ⟨sub3_994, List.forall_mem_cons.2 ⟨sub3_995, List.forall_mem_cons.2 ⟨sub3_996, List.forall_mem_cons.2 ⟨sub3_997, List.forall_mem_cons.2 ⟨sub3_998, List.forall_mem_cons.2 ⟨sub3_999, List.forall_mem_cons.2 ⟨sub3_1000, List.forall_mem_cons.2 ⟨sub3_1001, List.forall_mem_cons.2 ⟨sub3_1002, List.forall_mem_cons.2 ⟨sub3_1003, List.forall_mem_cons.2 ⟨sub3_1004, List.forall_mem_cons.2 ⟨sub3_1005, List.forall_mem_cons.2 ⟨sub3_1006, List.forall_mem_cons.2 ⟨sub3_1007, List.forall_mem_cons.2 ⟨sub3_1008, List.forall_mem_cons.2 ⟨sub3_1009, List.forall_mem_cons.2 ⟨sub3_1010, List.forall_mem_cons.2 ⟨sub3_1011, List.forall_mem_cons.2 ⟨sub3_1012, List.forall_mem_cons.2 ⟨sub3_1013, List.forall_mem_cons.2 ⟨sub3_1014, List.forall_mem_cons.2 ⟨sub3_1015, List.forall_mem_cons.2 ⟨sub3_1016, List.forall_mem_cons.2 ⟨sub3_1017, List.forall_mem_cons.2 ⟨sub3_1018, List.forall_mem_cons.2 ⟨sub3_1019, List.forall_mem_cons.2 ⟨sub3_1020, List.forall_mem_cons.2 ⟨sub3_1021, List.forall_mem_cons.2 ⟨sub3_1022, List.forall_mem_cons.2 ⟨sub3_1023, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_1024 : sub3 [3, -2, -3] = true := by decide +kernel
theorem sub3_1025 : sub3 [3, -2, -2] = true := by decide +kernel
theorem sub3_1026 : sub3 [3, -2, -1] = true := by decide +kernel
theorem sub3_1027 : sub3 [3, -2, 0] = true := by decide +kernel
theorem sub3_1028 : sub3 [3, -2, 1] = true := by decide +kernel
theorem sub3_1029 : sub3 [3, -2, 2] = true := by decide +kernel
theorem sub3_1030 : sub3 [3, -2, 3] = true := by decide +kernel
theorem sub3_1031 : sub3 [3, -2, 4] = true := by decide +kernel
theorem sub3_1032 : sub3 [3, -2, 5] = true := by decide +kernel
theorem sub3_1033 : sub3 [3, -2, 6] = true := by decide +kernel
theorem sub3_1034 : sub3 [3, -2, 7] = true := by decide +kernel
theorem sub3_1035 : sub3 [3, -1, -9] = true := by decide +kernel
theorem sub3_1036 : sub3 [3, -1, -8] = true := by decide +kernel
theorem sub3_1037 : sub3 [3, -1, -7] = true := by decide +kernel
theorem sub3_1038 : sub3 [3, -1, -6] = true := by decide +kernel
theorem sub3_1039 : sub3 [3, -1, -5] = true := by decide +kernel
theorem sub3_1040 : sub3 [3, -1, -4] = true := by decide +kernel
theorem sub3_1041 : sub3 [3, -1, -3] = true := by decide +kernel
theorem sub3_1042 : sub3 [3, -1, -2] = true := by decide +kernel
theorem sub3_1043 : sub3 [3, -1, -1] = true := by decide +kernel
theorem sub3_1044 : sub3 [3, -1, 0] = true := by decide +kernel
theorem sub3_1045 : sub3 [3, -1, 1] = true := by decide +kernel
theorem sub3_1046 : sub3 [3, -1, 2] = true := by decide +kernel
theorem sub3_1047 : sub3 [3, -1, 3] = true := by decide +kernel
theorem sub3_1048 : sub3 [3, -1, 4] = true := by decide +kernel
theorem sub3_1049 : sub3 [3, -1, 5] = true := by decide +kernel
theorem sub3_1050 : sub3 [3, -1, 6] = true := by decide +kernel
theorem sub3_1051 : sub3 [3, -1, 7] = true := by decide +kernel
theorem sub3_1052 : sub3 [3, 0, -9] = true := by decide +kernel
theorem sub3_1053 : sub3 [3, 0, -8] = true := by decide +kernel
theorem sub3_1054 : sub3 [3, 0, -7] = true := by decide +kernel
theorem sub3_1055 : sub3 [3, 0, -6] = true := by decide +kernel
theorem sb3_32 : ∀ q ∈ blk3_32, sub3 q = true := by
  unfold blk3_32
  exact List.forall_mem_cons.2 ⟨sub3_1024, List.forall_mem_cons.2 ⟨sub3_1025, List.forall_mem_cons.2 ⟨sub3_1026, List.forall_mem_cons.2 ⟨sub3_1027, List.forall_mem_cons.2 ⟨sub3_1028, List.forall_mem_cons.2 ⟨sub3_1029, List.forall_mem_cons.2 ⟨sub3_1030, List.forall_mem_cons.2 ⟨sub3_1031, List.forall_mem_cons.2 ⟨sub3_1032, List.forall_mem_cons.2 ⟨sub3_1033, List.forall_mem_cons.2 ⟨sub3_1034, List.forall_mem_cons.2 ⟨sub3_1035, List.forall_mem_cons.2 ⟨sub3_1036, List.forall_mem_cons.2 ⟨sub3_1037, List.forall_mem_cons.2 ⟨sub3_1038, List.forall_mem_cons.2 ⟨sub3_1039, List.forall_mem_cons.2 ⟨sub3_1040, List.forall_mem_cons.2 ⟨sub3_1041, List.forall_mem_cons.2 ⟨sub3_1042, List.forall_mem_cons.2 ⟨sub3_1043, List.forall_mem_cons.2 ⟨sub3_1044, List.forall_mem_cons.2 ⟨sub3_1045, List.forall_mem_cons.2 ⟨sub3_1046, List.forall_mem_cons.2 ⟨sub3_1047, List.forall_mem_cons.2 ⟨sub3_1048, List.forall_mem_cons.2 ⟨sub3_1049, List.forall_mem_cons.2 ⟨sub3_1050, List.forall_mem_cons.2 ⟨sub3_1051, List.forall_mem_cons.2 ⟨sub3_1052, List.forall_mem_cons.2 ⟨sub3_1053, List.forall_mem_cons.2 ⟨sub3_1054, List.forall_mem_cons.2 ⟨sub3_1055, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_1056 : sub3 [3, 0, -5] = true := by decide +kernel
theorem sub3_1057 : sub3 [3, 0, -4] = true := by decide +kernel
theorem sub3_1058 : sub3 [3, 0, -3] = true := by decide +kernel
theorem sub3_1059 : sub3 [3, 0, -2] = true := by decide +kernel
theorem sub3_1060 : sub3 [3, 0, -1] = true := by decide +kernel
theorem sub3_1061 : sub3 [3, 0, 0] = true := by decide +kernel
theorem sub3_1062 : sub3 [3, 0, 1] = true := by decide +kernel
theorem sub3_1063 : sub3 [3, 0, 2] = true := by decide +kernel
theorem sub3_1064 : sub3 [3, 0, 3] = true := by decide +kernel
theorem sub3_1065 : sub3 [3, 0, 4] = true := by decide +kernel
theorem sub3_1066 : sub3 [3, 0, 5] = true := by decide +kernel
theorem sub3_1067 : sub3 [3, 0, 6] = true := by decide +kernel
theorem sub3_1068 : sub3 [3, 0, 7] = true := by decide +kernel
theorem sub3_1069 : sub3 [3, 0, 8] = true := by decide +kernel
theorem sub3_1070 : sub3 [3, 1, -8] = true := by decide +kernel
theorem sub3_1071 : sub3 [3, 1, -7] = true := by decide +kernel
theorem sub3_1072 : sub3 [3, 1, -6] = true := by decide +kernel
theorem sub3_1073 : sub3 [3, 1, -5] = true := by decide +kernel
theorem sub3_1074 : sub3 [3, 1, -4] = true := by decide +kernel
theorem sub3_1075 : sub3 [3, 1, -3] = true := by decide +kernel
theorem sub3_1076 : sub3 [3, 1, -2] = true := by decide +kernel
theorem sub3_1077 : sub3 [3, 1, -1] = true := by decide +kernel
theorem sub3_1078 : sub3 [3, 1, 0] = true := by decide +kernel
theorem sub3_1079 : sub3 [3, 1, 1] = true := by decide +kernel
theorem sub3_1080 : sub3 [3, 1, 2] = true := by decide +kernel
theorem sub3_1081 : sub3 [3, 1, 3] = true := by decide +kernel
theorem sub3_1082 : sub3 [3, 1, 4] = true := by decide +kernel
theorem sub3_1083 : sub3 [3, 1, 5] = true := by decide +kernel
theorem sub3_1084 : sub3 [3, 1, 6] = true := by decide +kernel
theorem sub3_1085 : sub3 [3, 1, 7] = true := by decide +kernel
theorem sub3_1086 : sub3 [3, 1, 8] = true := by decide +kernel
theorem sub3_1087 : sub3 [3, 2, -8] = true := by decide +kernel
theorem sb3_33 : ∀ q ∈ blk3_33, sub3 q = true := by
  unfold blk3_33
  exact List.forall_mem_cons.2 ⟨sub3_1056, List.forall_mem_cons.2 ⟨sub3_1057, List.forall_mem_cons.2 ⟨sub3_1058, List.forall_mem_cons.2 ⟨sub3_1059, List.forall_mem_cons.2 ⟨sub3_1060, List.forall_mem_cons.2 ⟨sub3_1061, List.forall_mem_cons.2 ⟨sub3_1062, List.forall_mem_cons.2 ⟨sub3_1063, List.forall_mem_cons.2 ⟨sub3_1064, List.forall_mem_cons.2 ⟨sub3_1065, List.forall_mem_cons.2 ⟨sub3_1066, List.forall_mem_cons.2 ⟨sub3_1067, List.forall_mem_cons.2 ⟨sub3_1068, List.forall_mem_cons.2 ⟨sub3_1069, List.forall_mem_cons.2 ⟨sub3_1070, List.forall_mem_cons.2 ⟨sub3_1071, List.forall_mem_cons.2 ⟨sub3_1072, List.forall_mem_cons.2 ⟨sub3_1073, List.forall_mem_cons.2 ⟨sub3_1074, List.forall_mem_cons.2 ⟨sub3_1075, List.forall_mem_cons.2 ⟨sub3_1076, List.forall_mem_cons.2 ⟨sub3_1077, List.forall_mem_cons.2 ⟨sub3_1078, List.forall_mem_cons.2 ⟨sub3_1079, List.forall_mem_cons.2 ⟨sub3_1080, List.forall_mem_cons.2 ⟨sub3_1081, List.forall_mem_cons.2 ⟨sub3_1082, List.forall_mem_cons.2 ⟨sub3_1083, List.forall_mem_cons.2 ⟨sub3_1084, List.forall_mem_cons.2 ⟨sub3_1085, List.forall_mem_cons.2 ⟨sub3_1086, List.forall_mem_cons.2 ⟨sub3_1087, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_1088 : sub3 [3, 2, -7] = true := by decide +kernel
theorem sub3_1089 : sub3 [3, 2, -6] = true := by decide +kernel
theorem sub3_1090 : sub3 [3, 2, -5] = true := by decide +kernel
theorem sub3_1091 : sub3 [3, 2, -4] = true := by decide +kernel
theorem sub3_1092 : sub3 [3, 2, -3] = true := by decide +kernel
theorem sub3_1093 : sub3 [3, 2, -2] = true := by decide +kernel
theorem sub3_1094 : sub3 [3, 2, -1] = true := by decide +kernel
theorem sub3_1095 : sub3 [3, 2, 0] = true := by decide +kernel
theorem sub3_1096 : sub3 [3, 2, 1] = true := by decide +kernel
theorem sub3_1097 : sub3 [3, 2, 2] = true := by decide +kernel
theorem sub3_1098 : sub3 [3, 2, 3] = true := by decide +kernel
theorem sub3_1099 : sub3 [3, 2, 4] = true := by decide +kernel
theorem sub3_1100 : sub3 [3, 2, 5] = true := by decide +kernel
theorem sub3_1101 : sub3 [3, 2, 6] = true := by decide +kernel
theorem sub3_1102 : sub3 [3, 2, 7] = true := by decide +kernel
theorem sub3_1103 : sub3 [3, 3, -7] = true := by decide +kernel
theorem sub3_1104 : sub3 [3, 3, -6] = true := by decide +kernel
theorem sub3_1105 : sub3 [3, 3, -5] = true := by decide +kernel
theorem sub3_1106 : sub3 [3, 3, -4] = true := by decide +kernel
theorem sub3_1107 : sub3 [3, 3, -3] = true := by decide +kernel
theorem sub3_1108 : sub3 [3, 3, -2] = true := by decide +kernel
theorem sub3_1109 : sub3 [3, 3, -1] = true := by decide +kernel
theorem sub3_1110 : sub3 [3, 3, 0] = true := by decide +kernel
theorem sub3_1111 : sub3 [3, 3, 1] = true := by decide +kernel
theorem sub3_1112 : sub3 [3, 3, 2] = true := by decide +kernel
theorem sub3_1113 : sub3 [3, 3, 3] = true := by decide +kernel
theorem sub3_1114 : sub3 [3, 3, 4] = true := by decide +kernel
theorem sub3_1115 : sub3 [3, 3, 5] = true := by decide +kernel
theorem sub3_1116 : sub3 [3, 3, 6] = true := by decide +kernel
theorem sub3_1117 : sub3 [3, 3, 7] = true := by decide +kernel
theorem sub3_1118 : sub3 [3, 4] = true := by decide +kernel
theorem sub3_1119 : sub3 [3, 5] = true := by decide +kernel
theorem sb3_34 : ∀ q ∈ blk3_34, sub3 q = true := by
  unfold blk3_34
  exact List.forall_mem_cons.2 ⟨sub3_1088, List.forall_mem_cons.2 ⟨sub3_1089, List.forall_mem_cons.2 ⟨sub3_1090, List.forall_mem_cons.2 ⟨sub3_1091, List.forall_mem_cons.2 ⟨sub3_1092, List.forall_mem_cons.2 ⟨sub3_1093, List.forall_mem_cons.2 ⟨sub3_1094, List.forall_mem_cons.2 ⟨sub3_1095, List.forall_mem_cons.2 ⟨sub3_1096, List.forall_mem_cons.2 ⟨sub3_1097, List.forall_mem_cons.2 ⟨sub3_1098, List.forall_mem_cons.2 ⟨sub3_1099, List.forall_mem_cons.2 ⟨sub3_1100, List.forall_mem_cons.2 ⟨sub3_1101, List.forall_mem_cons.2 ⟨sub3_1102, List.forall_mem_cons.2 ⟨sub3_1103, List.forall_mem_cons.2 ⟨sub3_1104, List.forall_mem_cons.2 ⟨sub3_1105, List.forall_mem_cons.2 ⟨sub3_1106, List.forall_mem_cons.2 ⟨sub3_1107, List.forall_mem_cons.2 ⟨sub3_1108, List.forall_mem_cons.2 ⟨sub3_1109, List.forall_mem_cons.2 ⟨sub3_1110, List.forall_mem_cons.2 ⟨sub3_1111, List.forall_mem_cons.2 ⟨sub3_1112, List.forall_mem_cons.2 ⟨sub3_1113, List.forall_mem_cons.2 ⟨sub3_1114, List.forall_mem_cons.2 ⟨sub3_1115, List.forall_mem_cons.2 ⟨sub3_1116, List.forall_mem_cons.2 ⟨sub3_1117, List.forall_mem_cons.2 ⟨sub3_1118, List.forall_mem_cons.2 ⟨sub3_1119, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_1120 : sub3 [4, -6] = true := by decide +kernel
theorem sub3_1121 : sub3 [4, -5] = true := by decide +kernel
theorem sub3_1122 : sub3 [4, -4] = true := by decide +kernel
theorem sub3_1123 : sub3 [4, -3] = true := by decide +kernel
theorem sub3_1124 : sub3 [4, -2, -8] = true := by decide +kernel
theorem sub3_1125 : sub3 [4, -2, -7] = true := by decide +kernel
theorem sub3_1126 : sub3 [4, -2, -6] = true := by decide +kernel
theorem sub3_1127 : sub3 [4, -2, -5] = true := by decide +kernel
theorem sub3_1128 : sub3 [4, -2, -4] = true := by decide +kernel
theorem sub3_1129 : sub3 [4, -2, -3] = true := by decide +kernel
theorem sub3_1130 : sub3 [4, -2, -2] = true := by decide +kernel
theorem sub3_1131 : sub3 [4, -2, -1] = true := by decide +kernel
theorem sub3_1132 : sub3 [4, -2, 0] = true := by decide +kernel
theorem sub3_1133 : sub3 [4, -2, 1] = true := by decide +kernel
theorem sub3_1134 : sub3 [4, -2, 2] = true := by decide +kernel
theorem sub3_1135 : sub3 [4, -2, 3] = true := by decide +kernel
theorem sub3_1136 : sub3 [4, -2, 4] = true := by decide +kernel
theorem sub3_1137 : sub3 [4, -2, 5] = true := by decide +kernel
theorem sub3_1138 : sub3 [4, -2, 6] = true := by decide +kernel
theorem sub3_1139 : sub3 [4, -1, -8] = true := by decide +kernel
theorem sub3_1140 : sub3 [4, -1, -7] = true := by decide +kernel
theorem sub3_1141 : sub3 [4, -1, -6] = true := by decide +kernel
theorem sub3_1142 : sub3 [4, -1, -5] = true := by decide +kernel
theorem sub3_1143 : sub3 [4, -1, -4] = true := by decide +kernel
theorem sub3_1144 : sub3 [4, -1, -3] = true := by decide +kernel
theorem sub3_1145 : sub3 [4, -1, -2] = true := by decide +kernel
theorem sub3_1146 : sub3 [4, -1, -1] = true := by decide +kernel
theorem sub3_1147 : sub3 [4, -1, 0] = true := by decide +kernel
theorem sub3_1148 : sub3 [4, -1, 1] = true := by decide +kernel
theorem sub3_1149 : sub3 [4, -1, 2] = true := by decide +kernel
theorem sub3_1150 : sub3 [4, -1, 3] = true := by decide +kernel
theorem sub3_1151 : sub3 [4, -1, 4] = true := by decide +kernel
theorem sb3_35 : ∀ q ∈ blk3_35, sub3 q = true := by
  unfold blk3_35
  exact List.forall_mem_cons.2 ⟨sub3_1120, List.forall_mem_cons.2 ⟨sub3_1121, List.forall_mem_cons.2 ⟨sub3_1122, List.forall_mem_cons.2 ⟨sub3_1123, List.forall_mem_cons.2 ⟨sub3_1124, List.forall_mem_cons.2 ⟨sub3_1125, List.forall_mem_cons.2 ⟨sub3_1126, List.forall_mem_cons.2 ⟨sub3_1127, List.forall_mem_cons.2 ⟨sub3_1128, List.forall_mem_cons.2 ⟨sub3_1129, List.forall_mem_cons.2 ⟨sub3_1130, List.forall_mem_cons.2 ⟨sub3_1131, List.forall_mem_cons.2 ⟨sub3_1132, List.forall_mem_cons.2 ⟨sub3_1133, List.forall_mem_cons.2 ⟨sub3_1134, List.forall_mem_cons.2 ⟨sub3_1135, List.forall_mem_cons.2 ⟨sub3_1136, List.forall_mem_cons.2 ⟨sub3_1137, List.forall_mem_cons.2 ⟨sub3_1138, List.forall_mem_cons.2 ⟨sub3_1139, List.forall_mem_cons.2 ⟨sub3_1140, List.forall_mem_cons.2 ⟨sub3_1141, List.forall_mem_cons.2 ⟨sub3_1142, List.forall_mem_cons.2 ⟨sub3_1143, List.forall_mem_cons.2 ⟨sub3_1144, List.forall_mem_cons.2 ⟨sub3_1145, List.forall_mem_cons.2 ⟨sub3_1146, List.forall_mem_cons.2 ⟨sub3_1147, List.forall_mem_cons.2 ⟨sub3_1148, List.forall_mem_cons.2 ⟨sub3_1149, List.forall_mem_cons.2 ⟨sub3_1150, List.forall_mem_cons.2 ⟨sub3_1151, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_1152 : sub3 [4, -1, 5] = true := by decide +kernel
theorem sub3_1153 : sub3 [4, -1, 6] = true := by decide +kernel
theorem sub3_1154 : sub3 [4, 0, -8] = true := by decide +kernel
theorem sub3_1155 : sub3 [4, 0, -7] = true := by decide +kernel
theorem sub3_1156 : sub3 [4, 0, -6] = true := by decide +kernel
theorem sub3_1157 : sub3 [4, 0, -5] = true := by decide +kernel
theorem sub3_1158 : sub3 [4, 0, -4] = true := by decide +kernel
theorem sub3_1159 : sub3 [4, 0, -3] = true := by decide +kernel
theorem sub3_1160 : sub3 [4, 0, -2] = true := by decide +kernel
theorem sub3_1161 : sub3 [4, 0, -1] = true := by decide +kernel
theorem sub3_1162 : sub3 [4, 0, 0] = true := by decide +kernel
theorem sub3_1163 : sub3 [4, 0, 1] = true := by decide +kernel
theorem sub3_1164 : sub3 [4, 0, 2] = true := by decide +kernel
theorem sub3_1165 : sub3 [4, 0, 3] = true := by decide +kernel
theorem sub3_1166 : sub3 [4, 0, 4] = true := by decide +kernel
theorem sub3_1167 : sub3 [4, 0, 5] = true := by decide +kernel
theorem sub3_1168 : sub3 [4, 0, 6] = true := by decide +kernel
theorem sub3_1169 : sub3 [4, 0, 7] = true := by decide +kernel
theorem sub3_1170 : sub3 [4, 1, -7] = true := by decide +kernel
theorem sub3_1171 : sub3 [4, 1, -6] = true := by decide +kernel
theorem sub3_1172 : sub3 [4, 1, -5] = true := by decide +kernel
theorem sub3_1173 : sub3 [4, 1, -4] = true := by decide +kernel
theorem sub3_1174 : sub3 [4, 1, -3] = true := by decide +kernel
theorem sub3_1175 : sub3 [4, 1, -2] = true := by decide +kernel
theorem sub3_1176 : sub3 [4, 1, -1] = true := by decide +kernel
theorem sub3_1177 : sub3 [4, 1, 0] = true := by decide +kernel
theorem sub3_1178 : sub3 [4, 1, 1] = true := by decide +kernel
theorem sub3_1179 : sub3 [4, 1, 2] = true := by decide +kernel
theorem sub3_1180 : sub3 [4, 1, 3] = true := by decide +kernel
theorem sub3_1181 : sub3 [4, 1, 4] = true := by decide +kernel
theorem sub3_1182 : sub3 [4, 1, 5] = true := by decide +kernel
theorem sub3_1183 : sub3 [4, 1, 6] = true := by decide +kernel
theorem sb3_36 : ∀ q ∈ blk3_36, sub3 q = true := by
  unfold blk3_36
  exact List.forall_mem_cons.2 ⟨sub3_1152, List.forall_mem_cons.2 ⟨sub3_1153, List.forall_mem_cons.2 ⟨sub3_1154, List.forall_mem_cons.2 ⟨sub3_1155, List.forall_mem_cons.2 ⟨sub3_1156, List.forall_mem_cons.2 ⟨sub3_1157, List.forall_mem_cons.2 ⟨sub3_1158, List.forall_mem_cons.2 ⟨sub3_1159, List.forall_mem_cons.2 ⟨sub3_1160, List.forall_mem_cons.2 ⟨sub3_1161, List.forall_mem_cons.2 ⟨sub3_1162, List.forall_mem_cons.2 ⟨sub3_1163, List.forall_mem_cons.2 ⟨sub3_1164, List.forall_mem_cons.2 ⟨sub3_1165, List.forall_mem_cons.2 ⟨sub3_1166, List.forall_mem_cons.2 ⟨sub3_1167, List.forall_mem_cons.2 ⟨sub3_1168, List.forall_mem_cons.2 ⟨sub3_1169, List.forall_mem_cons.2 ⟨sub3_1170, List.forall_mem_cons.2 ⟨sub3_1171, List.forall_mem_cons.2 ⟨sub3_1172, List.forall_mem_cons.2 ⟨sub3_1173, List.forall_mem_cons.2 ⟨sub3_1174, List.forall_mem_cons.2 ⟨sub3_1175, List.forall_mem_cons.2 ⟨sub3_1176, List.forall_mem_cons.2 ⟨sub3_1177, List.forall_mem_cons.2 ⟨sub3_1178, List.forall_mem_cons.2 ⟨sub3_1179, List.forall_mem_cons.2 ⟨sub3_1180, List.forall_mem_cons.2 ⟨sub3_1181, List.forall_mem_cons.2 ⟨sub3_1182, List.forall_mem_cons.2 ⟨sub3_1183, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_1184 : sub3 [4, 1, 7] = true := by decide +kernel
theorem sub3_1185 : sub3 [4, 2] = true := by decide +kernel
theorem sub3_1186 : sub3 [4, 3] = true := by decide +kernel
theorem sub3_1187 : sub3 [4, 4] = true := by decide +kernel
theorem sub3_1188 : sub3 [5, -6] = true := by decide +kernel
theorem sub3_1189 : sub3 [5, -5] = true := by decide +kernel
theorem sub3_1190 : sub3 [5, -4] = true := by decide +kernel
theorem sub3_1191 : sub3 [5, -3] = true := by decide +kernel
theorem sub3_1192 : sub3 [5, -2] = true := by decide +kernel
theorem sub3_1193 : sub3 [5, -1] = true := by decide +kernel
theorem sub3_1194 : sub3 [5, 0] = true := by decide +kernel
theorem sub3_1195 : sub3 [5, 1] = true := by decide +kernel
theorem sub3_1196 : sub3 [5, 2] = true := by decide +kernel
theorem sub3_1197 : sub3 [5, 3] = true := by decide +kernel
theorem sub3_1198 : sub3 [6, -4] = true := by decide +kernel
theorem sub3_1199 : sub3 [6, -3] = true := by decide +kernel
theorem sub3_1200 : sub3 [6, -2] = true := by decide +kernel
theorem sub3_1201 : sub3 [6, -1] = true := by decide +kernel
theorem sub3_1202 : sub3 [6, 0] = true := by decide +kernel
theorem sub3_1203 : sub3 [6, 1] = true := by decide +kernel
theorem sub3_1204 : sub3 [6, 2] = true := by decide +kernel
theorem sb3_37 : ∀ q ∈ blk3_37, sub3 q = true := by
  unfold blk3_37
  exact List.forall_mem_cons.2 ⟨sub3_1184, List.forall_mem_cons.2 ⟨sub3_1185, List.forall_mem_cons.2 ⟨sub3_1186, List.forall_mem_cons.2 ⟨sub3_1187, List.forall_mem_cons.2 ⟨sub3_1188, List.forall_mem_cons.2 ⟨sub3_1189, List.forall_mem_cons.2 ⟨sub3_1190, List.forall_mem_cons.2 ⟨sub3_1191, List.forall_mem_cons.2 ⟨sub3_1192, List.forall_mem_cons.2 ⟨sub3_1193, List.forall_mem_cons.2 ⟨sub3_1194, List.forall_mem_cons.2 ⟨sub3_1195, List.forall_mem_cons.2 ⟨sub3_1196, List.forall_mem_cons.2 ⟨sub3_1197, List.forall_mem_cons.2 ⟨sub3_1198, List.forall_mem_cons.2 ⟨sub3_1199, List.forall_mem_cons.2 ⟨sub3_1200, List.forall_mem_cons.2 ⟨sub3_1201, List.forall_mem_cons.2 ⟨sub3_1202, List.forall_mem_cons.2 ⟨sub3_1203, List.forall_mem_cons.2 ⟨sub3_1204, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_0 : sub4 [-5, -1] = true := by decide +kernel
theorem sub4_1 : sub4 [-5, 0] = true := by decide +kernel
theorem sub4_2 : sub4 [-5, 1] = true := by decide +kernel
theorem sub4_3 : sub4 [-5, 2] = true := by decide +kernel
theorem sub4_4 : sub4 [-5, 3] = true := by decide +kernel
theorem sub4_5 : sub4 [-5, 4] = true := by decide +kernel
theorem sub4_6 : sub4 [-4, -3] = true := by decide +kernel
theorem sub4_7 : sub4 [-4, -2] = true := by decide +kernel
theorem sub4_8 : sub4 [-4, -1] = true := by decide +kernel
theorem sub4_9 : sub4 [-4, 0, -7] = true := by decide +kernel
theorem sub4_10 : sub4 [-4, 0, -6] = true := by decide +kernel
theorem sub4_11 : sub4 [-4, 0, -5] = true := by decide +kernel
theorem sub4_12 : sub4 [-4, 0, -4] = true := by decide +kernel
theorem sub4_13 : sub4 [-4, 0, -3] = true := by decide +kernel
theorem sub4_14 : sub4 [-4, 0, -2] = true := by decide +kernel
theorem sub4_15 : sub4 [-4, 0, -1] = true := by decide +kernel
theorem sub4_16 : sub4 [-4, 0, 0] = true := by decide +kernel
theorem sub4_17 : sub4 [-4, 0, 1] = true := by decide +kernel
theorem sub4_18 : sub4 [-4, 0, 2] = true := by decide +kernel
theorem sub4_19 : sub4 [-4, 0, 3] = true := by decide +kernel
theorem sub4_20 : sub4 [-4, 0, 4] = true := by decide +kernel
theorem sub4_21 : sub4 [-4, 0, 5] = true := by decide +kernel
theorem sub4_22 : sub4 [-4, 0, 6] = true := by decide +kernel
theorem sub4_23 : sub4 [-4, 0, 7] = true := by decide +kernel
theorem sub4_24 : sub4 [-4, 0, 8] = true := by decide +kernel
theorem sub4_25 : sub4 [-4, 1, -7] = true := by decide +kernel
theorem sub4_26 : sub4 [-4, 1, -6] = true := by decide +kernel
theorem sub4_27 : sub4 [-4, 1, -5] = true := by decide +kernel
theorem sub4_28 : sub4 [-4, 1, -4] = true := by decide +kernel
theorem sub4_29 : sub4 [-4, 1, -3] = true := by decide +kernel
theorem sub4_30 : sub4 [-4, 1, -2] = true := by decide +kernel
theorem sub4_31 : sub4 [-4, 1, -1] = true := by decide +kernel
theorem sb4_0 : ∀ q ∈ blk4_0, sub4 q = true := by
  unfold blk4_0
  exact List.forall_mem_cons.2 ⟨sub4_0, List.forall_mem_cons.2 ⟨sub4_1, List.forall_mem_cons.2 ⟨sub4_2, List.forall_mem_cons.2 ⟨sub4_3, List.forall_mem_cons.2 ⟨sub4_4, List.forall_mem_cons.2 ⟨sub4_5, List.forall_mem_cons.2 ⟨sub4_6, List.forall_mem_cons.2 ⟨sub4_7, List.forall_mem_cons.2 ⟨sub4_8, List.forall_mem_cons.2 ⟨sub4_9, List.forall_mem_cons.2 ⟨sub4_10, List.forall_mem_cons.2 ⟨sub4_11, List.forall_mem_cons.2 ⟨sub4_12, List.forall_mem_cons.2 ⟨sub4_13, List.forall_mem_cons.2 ⟨sub4_14, List.forall_mem_cons.2 ⟨sub4_15, List.forall_mem_cons.2 ⟨sub4_16, List.forall_mem_cons.2 ⟨sub4_17, List.forall_mem_cons.2 ⟨sub4_18, List.forall_mem_cons.2 ⟨sub4_19, List.forall_mem_cons.2 ⟨sub4_20, List.forall_mem_cons.2 ⟨sub4_21, List.forall_mem_cons.2 ⟨sub4_22, List.forall_mem_cons.2 ⟨sub4_23, List.forall_mem_cons.2 ⟨sub4_24, List.forall_mem_cons.2 ⟨sub4_25, List.forall_mem_cons.2 ⟨sub4_26, List.forall_mem_cons.2 ⟨sub4_27, List.forall_mem_cons.2 ⟨sub4_28, List.forall_mem_cons.2 ⟨sub4_29, List.forall_mem_cons.2 ⟨sub4_30, List.forall_mem_cons.2 ⟨sub4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_32 : sub4 [-4, 1, 0] = true := by decide +kernel
theorem sub4_33 : sub4 [-4, 1, 1] = true := by decide +kernel
theorem sub4_34 : sub4 [-4, 1, 2] = true := by decide +kernel
theorem sub4_35 : sub4 [-4, 1, 3] = true := by decide +kernel
theorem sub4_36 : sub4 [-4, 1, 4] = true := by decide +kernel
theorem sub4_37 : sub4 [-4, 1, 5] = true := by decide +kernel
theorem sub4_38 : sub4 [-4, 1, 6] = true := by decide +kernel
theorem sub4_39 : sub4 [-4, 1, 7] = true := by decide +kernel
theorem sub4_40 : sub4 [-4, 1, 8] = true := by decide +kernel
theorem sub4_41 : sub4 [-4, 1, 9] = true := by decide +kernel
theorem sub4_42 : sub4 [-4, 2, -7] = true := by decide +kernel
theorem sub4_43 : sub4 [-4, 2, -6] = true := by decide +kernel
theorem sub4_44 : sub4 [-4, 2, -5] = true := by decide +kernel
theorem sub4_45 : sub4 [-4, 2, -4] = true := by decide +kernel
theorem sub4_46 : sub4 [-4, 2, -3] = true := by decide +kernel
theorem sub4_47 : sub4 [-4, 2, -2] = true := by decide +kernel
theorem sub4_48 : sub4 [-4, 2, -1] = true := by decide +kernel
theorem sub4_49 : sub4 [-4, 2, 0] = true := by decide +kernel
theorem sub4_50 : sub4 [-4, 2, 1] = true := by decide +kernel
theorem sub4_51 : sub4 [-4, 2, 2] = true := by decide +kernel
theorem sub4_52 : sub4 [-4, 2, 3] = true := by decide +kernel
theorem sub4_53 : sub4 [-4, 2, 4] = true := by decide +kernel
theorem sub4_54 : sub4 [-4, 2, 5] = true := by decide +kernel
theorem sub4_55 : sub4 [-4, 2, 6] = true := by decide +kernel
theorem sub4_56 : sub4 [-4, 2, 7] = true := by decide +kernel
theorem sub4_57 : sub4 [-4, 2, 8] = true := by decide +kernel
theorem sub4_58 : sub4 [-4, 2, 9] = true := by decide +kernel
theorem sub4_59 : sub4 [-4, 3, -7] = true := by decide +kernel
theorem sub4_60 : sub4 [-4, 3, -6] = true := by decide +kernel
theorem sub4_61 : sub4 [-4, 3, -5] = true := by decide +kernel
theorem sub4_62 : sub4 [-4, 3, -4] = true := by decide +kernel
theorem sub4_63 : sub4 [-4, 3, -3] = true := by decide +kernel
theorem sb4_1 : ∀ q ∈ blk4_1, sub4 q = true := by
  unfold blk4_1
  exact List.forall_mem_cons.2 ⟨sub4_32, List.forall_mem_cons.2 ⟨sub4_33, List.forall_mem_cons.2 ⟨sub4_34, List.forall_mem_cons.2 ⟨sub4_35, List.forall_mem_cons.2 ⟨sub4_36, List.forall_mem_cons.2 ⟨sub4_37, List.forall_mem_cons.2 ⟨sub4_38, List.forall_mem_cons.2 ⟨sub4_39, List.forall_mem_cons.2 ⟨sub4_40, List.forall_mem_cons.2 ⟨sub4_41, List.forall_mem_cons.2 ⟨sub4_42, List.forall_mem_cons.2 ⟨sub4_43, List.forall_mem_cons.2 ⟨sub4_44, List.forall_mem_cons.2 ⟨sub4_45, List.forall_mem_cons.2 ⟨sub4_46, List.forall_mem_cons.2 ⟨sub4_47, List.forall_mem_cons.2 ⟨sub4_48, List.forall_mem_cons.2 ⟨sub4_49, List.forall_mem_cons.2 ⟨sub4_50, List.forall_mem_cons.2 ⟨sub4_51, List.forall_mem_cons.2 ⟨sub4_52, List.forall_mem_cons.2 ⟨sub4_53, List.forall_mem_cons.2 ⟨sub4_54, List.forall_mem_cons.2 ⟨sub4_55, List.forall_mem_cons.2 ⟨sub4_56, List.forall_mem_cons.2 ⟨sub4_57, List.forall_mem_cons.2 ⟨sub4_58, List.forall_mem_cons.2 ⟨sub4_59, List.forall_mem_cons.2 ⟨sub4_60, List.forall_mem_cons.2 ⟨sub4_61, List.forall_mem_cons.2 ⟨sub4_62, List.forall_mem_cons.2 ⟨sub4_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_64 : sub4 [-4, 3, -2] = true := by decide +kernel
theorem sub4_65 : sub4 [-4, 3, -1] = true := by decide +kernel
theorem sub4_66 : sub4 [-4, 3, 0] = true := by decide +kernel
theorem sub4_67 : sub4 [-4, 3, 1] = true := by decide +kernel
theorem sub4_68 : sub4 [-4, 3, 2] = true := by decide +kernel
theorem sub4_69 : sub4 [-4, 3, 3] = true := by decide +kernel
theorem sub4_70 : sub4 [-4, 3, 4] = true := by decide +kernel
theorem sub4_71 : sub4 [-4, 3, 5] = true := by decide +kernel
theorem sub4_72 : sub4 [-4, 3, 6] = true := by decide +kernel
theorem sub4_73 : sub4 [-4, 3, 7] = true := by decide +kernel
theorem sub4_74 : sub4 [-4, 3, 8] = true := by decide +kernel
theorem sub4_75 : sub4 [-4, 4, -6] = true := by decide +kernel
theorem sub4_76 : sub4 [-4, 4, -5] = true := by decide +kernel
theorem sub4_77 : sub4 [-4, 4, -4] = true := by decide +kernel
theorem sub4_78 : sub4 [-4, 4, -3] = true := by decide +kernel
theorem sub4_79 : sub4 [-4, 4, -2] = true := by decide +kernel
theorem sub4_80 : sub4 [-4, 4, -1] = true := by decide +kernel
theorem sub4_81 : sub4 [-4, 4, 0] = true := by decide +kernel
theorem sub4_82 : sub4 [-4, 4, 1] = true := by decide +kernel
theorem sub4_83 : sub4 [-4, 4, 2] = true := by decide +kernel
theorem sub4_84 : sub4 [-4, 4, 3] = true := by decide +kernel
theorem sub4_85 : sub4 [-4, 4, 4] = true := by decide +kernel
theorem sub4_86 : sub4 [-4, 4, 5] = true := by decide +kernel
theorem sub4_87 : sub4 [-4, 4, 6] = true := by decide +kernel
theorem sub4_88 : sub4 [-4, 4, 7] = true := by decide +kernel
theorem sub4_89 : sub4 [-4, 4, 8] = true := by decide +kernel
theorem sub4_90 : sub4 [-4, 5] = true := by decide +kernel
theorem sub4_91 : sub4 [-3, -4] = true := by decide +kernel
theorem sub4_92 : sub4 [-3, -3] = true := by decide +kernel
theorem sub4_93 : sub4 [-3, -2, -7] = true := by decide +kernel
theorem sub4_94 : sub4 [-3, -2, -6] = true := by decide +kernel
theorem sub4_95 : sub4 [-3, -2, -5] = true := by decide +kernel
theorem sb4_2 : ∀ q ∈ blk4_2, sub4 q = true := by
  unfold blk4_2
  exact List.forall_mem_cons.2 ⟨sub4_64, List.forall_mem_cons.2 ⟨sub4_65, List.forall_mem_cons.2 ⟨sub4_66, List.forall_mem_cons.2 ⟨sub4_67, List.forall_mem_cons.2 ⟨sub4_68, List.forall_mem_cons.2 ⟨sub4_69, List.forall_mem_cons.2 ⟨sub4_70, List.forall_mem_cons.2 ⟨sub4_71, List.forall_mem_cons.2 ⟨sub4_72, List.forall_mem_cons.2 ⟨sub4_73, List.forall_mem_cons.2 ⟨sub4_74, List.forall_mem_cons.2 ⟨sub4_75, List.forall_mem_cons.2 ⟨sub4_76, List.forall_mem_cons.2 ⟨sub4_77, List.forall_mem_cons.2 ⟨sub4_78, List.forall_mem_cons.2 ⟨sub4_79, List.forall_mem_cons.2 ⟨sub4_80, List.forall_mem_cons.2 ⟨sub4_81, List.forall_mem_cons.2 ⟨sub4_82, List.forall_mem_cons.2 ⟨sub4_83, List.forall_mem_cons.2 ⟨sub4_84, List.forall_mem_cons.2 ⟨sub4_85, List.forall_mem_cons.2 ⟨sub4_86, List.forall_mem_cons.2 ⟨sub4_87, List.forall_mem_cons.2 ⟨sub4_88, List.forall_mem_cons.2 ⟨sub4_89, List.forall_mem_cons.2 ⟨sub4_90, List.forall_mem_cons.2 ⟨sub4_91, List.forall_mem_cons.2 ⟨sub4_92, List.forall_mem_cons.2 ⟨sub4_93, List.forall_mem_cons.2 ⟨sub4_94, List.forall_mem_cons.2 ⟨sub4_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_96 : sub4 [-3, -2, -4] = true := by decide +kernel
theorem sub4_97 : sub4 [-3, -2, -3] = true := by decide +kernel
theorem sub4_98 : sub4 [-3, -2, -2] = true := by decide +kernel
theorem sub4_99 : sub4 [-3, -2, -1] = true := by decide +kernel
theorem sub4_100 : sub4 [-3, -2, 0] = true := by decide +kernel
theorem sub4_101 : sub4 [-3, -2, 1] = true := by decide +kernel
theorem sub4_102 : sub4 [-3, -2, 2] = true := by decide +kernel
theorem sub4_103 : sub4 [-3, -2, 3] = true := by decide +kernel
theorem sub4_104 : sub4 [-3, -2, 4] = true := by decide +kernel
theorem sub4_105 : sub4 [-3, -2, 5] = true := by decide +kernel
theorem sub4_106 : sub4 [-3, -2, 6] = true := by decide +kernel
theorem sub4_107 : sub4 [-3, -2, 7] = true := by decide +kernel
theorem sub4_108 : sub4 [-3, -2, 8] = true := by decide +kernel
theorem sub4_109 : sub4 [-3, -1, -9] = true := by decide +kernel
theorem sub4_110 : sub4 [-3, -1, -8] = true := by decide +kernel
theorem sub4_111 : sub4 [-3, -1, -7] = true := by decide +kernel
theorem sub4_112 : sub4 [-3, -1, -6] = true := by decide +kernel
theorem sub4_113 : sub4 [-3, -1, -5] = true := by decide +kernel
theorem sub4_114 : sub4 [-3, -1, -4] = true := by decide +kernel
theorem sub4_115 : sub4 [-3, -1, -3] = true := by decide +kernel
theorem sub4_116 : sub4 [-3, -1, -2] = true := by decide +kernel
theorem sub4_117 : sub4 [-3, -1, -1] = true := by decide +kernel
theorem sub4_118 : sub4 [-3, -1, 0] = true := by decide +kernel
theorem sub4_119 : sub4 [-3, -1, 1] = true := by decide +kernel
theorem sub4_120 : sub4 [-3, -1, 2] = true := by decide +kernel
theorem sub4_121 : sub4 [-3, -1, 3] = true := by decide +kernel
theorem sub4_122 : sub4 [-3, -1, 4] = true := by decide +kernel
theorem sub4_123 : sub4 [-3, -1, 5] = true := by decide +kernel
theorem sub4_124 : sub4 [-3, -1, 6] = true := by decide +kernel
theorem sub4_125 : sub4 [-3, -1, 7] = true := by decide +kernel
theorem sub4_126 : sub4 [-3, -1, 8] = true := by decide +kernel
theorem sub4_127 : sub4 [-3, -1, 9] = true := by decide +kernel
theorem sb4_3 : ∀ q ∈ blk4_3, sub4 q = true := by
  unfold blk4_3
  exact List.forall_mem_cons.2 ⟨sub4_96, List.forall_mem_cons.2 ⟨sub4_97, List.forall_mem_cons.2 ⟨sub4_98, List.forall_mem_cons.2 ⟨sub4_99, List.forall_mem_cons.2 ⟨sub4_100, List.forall_mem_cons.2 ⟨sub4_101, List.forall_mem_cons.2 ⟨sub4_102, List.forall_mem_cons.2 ⟨sub4_103, List.forall_mem_cons.2 ⟨sub4_104, List.forall_mem_cons.2 ⟨sub4_105, List.forall_mem_cons.2 ⟨sub4_106, List.forall_mem_cons.2 ⟨sub4_107, List.forall_mem_cons.2 ⟨sub4_108, List.forall_mem_cons.2 ⟨sub4_109, List.forall_mem_cons.2 ⟨sub4_110, List.forall_mem_cons.2 ⟨sub4_111, List.forall_mem_cons.2 ⟨sub4_112, List.forall_mem_cons.2 ⟨sub4_113, List.forall_mem_cons.2 ⟨sub4_114, List.forall_mem_cons.2 ⟨sub4_115, List.forall_mem_cons.2 ⟨sub4_116, List.forall_mem_cons.2 ⟨sub4_117, List.forall_mem_cons.2 ⟨sub4_118, List.forall_mem_cons.2 ⟨sub4_119, List.forall_mem_cons.2 ⟨sub4_120, List.forall_mem_cons.2 ⟨sub4_121, List.forall_mem_cons.2 ⟨sub4_122, List.forall_mem_cons.2 ⟨sub4_123, List.forall_mem_cons.2 ⟨sub4_124, List.forall_mem_cons.2 ⟨sub4_125, List.forall_mem_cons.2 ⟨sub4_126, List.forall_mem_cons.2 ⟨sub4_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C047
