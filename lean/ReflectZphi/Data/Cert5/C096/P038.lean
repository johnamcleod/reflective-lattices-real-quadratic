import ReflectZphi.Data.Cert5.C096.Base

namespace ReflectZphi.Data.Cert5.C096

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_3_960 : subd9_3 [2, 0, -4] = true := by decide +kernel
theorem subd9_3_961 : subd9_3 [2, 0, -3] = true := by decide +kernel
theorem subd9_3_962 : subd9_3 [2, 0, -2] = true := by decide +kernel
theorem subd9_3_963 : subd9_3 [2, 0, -1] = true := by decide +kernel
theorem subd9_3_964 : subd9_3 [2, 0, 0] = true := by decide +kernel
theorem subd9_3_965 : subd9_3 [2, 0, 1] = true := by decide +kernel
theorem subd9_3_966 : subd9_3 [2, 0, 2] = true := by decide +kernel
theorem subd9_3_967 : subd9_3 [2, 0, 3] = true := by decide +kernel
theorem subd9_3_968 : subd9_3 [2, 0, 4] = true := by decide +kernel
theorem subd9_3_969 : subd9_3 [2, 0, 5] = true := by decide +kernel
theorem subd9_3_970 : subd9_3 [2, 0, 6] = true := by decide +kernel
theorem subd9_3_971 : subd9_3 [2, 0, 7] = true := by decide +kernel
theorem subd9_3_972 : subd9_3 [2, 0, 8] = true := by decide +kernel
theorem subd9_3_973 : subd9_3 [2, 0, 9] = true := by decide +kernel
theorem subd9_3_974 : subd9_3 [2, 1, -9] = true := by decide +kernel
theorem subd9_3_975 : subd9_3 [2, 1, -8] = true := by decide +kernel
theorem subd9_3_976 : subd9_3 [2, 1, -7] = true := by decide +kernel
theorem subd9_3_977 : subd9_3 [2, 1, -6] = true := by decide +kernel
theorem subd9_3_978 : subd9_3 [2, 1, -5] = true := by decide +kernel
theorem subd9_3_979 : subd9_3 [2, 1, -4] = true := by decide +kernel
theorem subd9_3_980 : subd9_3 [2, 1, -3] = true := by decide +kernel
theorem subd9_3_981 : subd9_3 [2, 1, -2] = true := by decide +kernel
theorem subd9_3_982 : subd9_3 [2, 1, -1] = true := by decide +kernel
theorem subd9_3_983 : subd9_3 [2, 1, 0] = true := by decide +kernel
theorem subd9_3_984 : subd9_3 [2, 1, 1] = true := by decide +kernel
theorem subd9_3_985 : subd9_3 [2, 1, 2] = true := by decide +kernel
theorem subd9_3_986 : subd9_3 [2, 1, 3] = true := by decide +kernel
theorem subd9_3_987 : subd9_3 [2, 1, 4] = true := by decide +kernel
theorem subd9_3_988 : subd9_3 [2, 1, 5] = true := by decide +kernel
theorem subd9_3_989 : subd9_3 [2, 1, 6] = true := by decide +kernel
theorem subd9_3_990 : subd9_3 [2, 1, 7] = true := by decide +kernel
theorem subd9_3_991 : subd9_3 [2, 1, 8] = true := by decide +kernel
theorem sbd9_3_30 : ∀ q ∈ blkd9_3_30, subd9_3 q = true := by
  unfold blkd9_3_30
  exact List.forall_mem_cons.2 ⟨subd9_3_960, List.forall_mem_cons.2 ⟨subd9_3_961, List.forall_mem_cons.2 ⟨subd9_3_962, List.forall_mem_cons.2 ⟨subd9_3_963, List.forall_mem_cons.2 ⟨subd9_3_964, List.forall_mem_cons.2 ⟨subd9_3_965, List.forall_mem_cons.2 ⟨subd9_3_966, List.forall_mem_cons.2 ⟨subd9_3_967, List.forall_mem_cons.2 ⟨subd9_3_968, List.forall_mem_cons.2 ⟨subd9_3_969, List.forall_mem_cons.2 ⟨subd9_3_970, List.forall_mem_cons.2 ⟨subd9_3_971, List.forall_mem_cons.2 ⟨subd9_3_972, List.forall_mem_cons.2 ⟨subd9_3_973, List.forall_mem_cons.2 ⟨subd9_3_974, List.forall_mem_cons.2 ⟨subd9_3_975, List.forall_mem_cons.2 ⟨subd9_3_976, List.forall_mem_cons.2 ⟨subd9_3_977, List.forall_mem_cons.2 ⟨subd9_3_978, List.forall_mem_cons.2 ⟨subd9_3_979, List.forall_mem_cons.2 ⟨subd9_3_980, List.forall_mem_cons.2 ⟨subd9_3_981, List.forall_mem_cons.2 ⟨subd9_3_982, List.forall_mem_cons.2 ⟨subd9_3_983, List.forall_mem_cons.2 ⟨subd9_3_984, List.forall_mem_cons.2 ⟨subd9_3_985, List.forall_mem_cons.2 ⟨subd9_3_986, List.forall_mem_cons.2 ⟨subd9_3_987, List.forall_mem_cons.2 ⟨subd9_3_988, List.forall_mem_cons.2 ⟨subd9_3_989, List.forall_mem_cons.2 ⟨subd9_3_990, List.forall_mem_cons.2 ⟨subd9_3_991, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_992 : subd9_3 [2, 1, 9] = true := by decide +kernel
theorem subd9_3_993 : subd9_3 [2, 2, -9] = true := by decide +kernel
theorem subd9_3_994 : subd9_3 [2, 2, -8] = true := by decide +kernel
theorem subd9_3_995 : subd9_3 [2, 2, -7] = true := by decide +kernel
theorem subd9_3_996 : subd9_3 [2, 2, -6] = true := by decide +kernel
theorem subd9_3_997 : subd9_3 [2, 2, -5] = true := by decide +kernel
theorem subd9_3_998 : subd9_3 [2, 2, -4] = true := by decide +kernel
theorem subd9_3_999 : subd9_3 [2, 2, -3] = true := by decide +kernel
theorem subd9_3_1000 : subd9_3 [2, 2, -2] = true := by decide +kernel
theorem subd9_3_1001 : subd9_3 [2, 2, -1] = true := by decide +kernel
theorem subd9_3_1002 : subd9_3 [2, 2, 0] = true := by decide +kernel
theorem subd9_3_1003 : subd9_3 [2, 2, 1] = true := by decide +kernel
theorem subd9_3_1004 : subd9_3 [2, 2, 2] = true := by decide +kernel
theorem subd9_3_1005 : subd9_3 [2, 2, 3] = true := by decide +kernel
theorem subd9_3_1006 : subd9_3 [2, 2, 4] = true := by decide +kernel
theorem subd9_3_1007 : subd9_3 [2, 2, 5] = true := by decide +kernel
theorem subd9_3_1008 : subd9_3 [2, 2, 6] = true := by decide +kernel
theorem subd9_3_1009 : subd9_3 [2, 2, 7] = true := by decide +kernel
theorem subd9_3_1010 : subd9_3 [2, 2, 8] = true := by decide +kernel
theorem subd9_3_1011 : subd9_3 [2, 2, 9] = true := by decide +kernel
theorem subd9_3_1012 : subd9_3 [2, 3, -8] = true := by decide +kernel
theorem subd9_3_1013 : subd9_3 [2, 3, -7] = true := by decide +kernel
theorem subd9_3_1014 : subd9_3 [2, 3, -6] = true := by decide +kernel
theorem subd9_3_1015 : subd9_3 [2, 3, -5] = true := by decide +kernel
theorem subd9_3_1016 : subd9_3 [2, 3, -4] = true := by decide +kernel
theorem subd9_3_1017 : subd9_3 [2, 3, -3] = true := by decide +kernel
theorem subd9_3_1018 : subd9_3 [2, 3, -2] = true := by decide +kernel
theorem subd9_3_1019 : subd9_3 [2, 3, -1] = true := by decide +kernel
theorem subd9_3_1020 : subd9_3 [2, 3, 0] = true := by decide +kernel
theorem subd9_3_1021 : subd9_3 [2, 3, 1] = true := by decide +kernel
theorem subd9_3_1022 : subd9_3 [2, 3, 2] = true := by decide +kernel
theorem subd9_3_1023 : subd9_3 [2, 3, 3] = true := by decide +kernel
theorem sbd9_3_31 : ∀ q ∈ blkd9_3_31, subd9_3 q = true := by
  unfold blkd9_3_31
  exact List.forall_mem_cons.2 ⟨subd9_3_992, List.forall_mem_cons.2 ⟨subd9_3_993, List.forall_mem_cons.2 ⟨subd9_3_994, List.forall_mem_cons.2 ⟨subd9_3_995, List.forall_mem_cons.2 ⟨subd9_3_996, List.forall_mem_cons.2 ⟨subd9_3_997, List.forall_mem_cons.2 ⟨subd9_3_998, List.forall_mem_cons.2 ⟨subd9_3_999, List.forall_mem_cons.2 ⟨subd9_3_1000, List.forall_mem_cons.2 ⟨subd9_3_1001, List.forall_mem_cons.2 ⟨subd9_3_1002, List.forall_mem_cons.2 ⟨subd9_3_1003, List.forall_mem_cons.2 ⟨subd9_3_1004, List.forall_mem_cons.2 ⟨subd9_3_1005, List.forall_mem_cons.2 ⟨subd9_3_1006, List.forall_mem_cons.2 ⟨subd9_3_1007, List.forall_mem_cons.2 ⟨subd9_3_1008, List.forall_mem_cons.2 ⟨subd9_3_1009, List.forall_mem_cons.2 ⟨subd9_3_1010, List.forall_mem_cons.2 ⟨subd9_3_1011, List.forall_mem_cons.2 ⟨subd9_3_1012, List.forall_mem_cons.2 ⟨subd9_3_1013, List.forall_mem_cons.2 ⟨subd9_3_1014, List.forall_mem_cons.2 ⟨subd9_3_1015, List.forall_mem_cons.2 ⟨subd9_3_1016, List.forall_mem_cons.2 ⟨subd9_3_1017, List.forall_mem_cons.2 ⟨subd9_3_1018, List.forall_mem_cons.2 ⟨subd9_3_1019, List.forall_mem_cons.2 ⟨subd9_3_1020, List.forall_mem_cons.2 ⟨subd9_3_1021, List.forall_mem_cons.2 ⟨subd9_3_1022, List.forall_mem_cons.2 ⟨subd9_3_1023, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_1024 : subd9_3 [2, 3, 4] = true := by decide +kernel
theorem subd9_3_1025 : subd9_3 [2, 3, 5] = true := by decide +kernel
theorem subd9_3_1026 : subd9_3 [2, 3, 6] = true := by decide +kernel
theorem subd9_3_1027 : subd9_3 [2, 3, 7] = true := by decide +kernel
theorem subd9_3_1028 : subd9_3 [2, 3, 8] = true := by decide +kernel
theorem subd9_3_1029 : subd9_3 [2, 4, -7] = true := by decide +kernel
theorem subd9_3_1030 : subd9_3 [2, 4, -6] = true := by decide +kernel
theorem subd9_3_1031 : subd9_3 [2, 4, -5] = true := by decide +kernel
theorem subd9_3_1032 : subd9_3 [2, 4, -4] = true := by decide +kernel
theorem subd9_3_1033 : subd9_3 [2, 4, -3] = true := by decide +kernel
theorem subd9_3_1034 : subd9_3 [2, 4, -2] = true := by decide +kernel
theorem subd9_3_1035 : subd9_3 [2, 4, -1] = true := by decide +kernel
theorem subd9_3_1036 : subd9_3 [2, 4, 0] = true := by decide +kernel
theorem subd9_3_1037 : subd9_3 [2, 4, 1] = true := by decide +kernel
theorem subd9_3_1038 : subd9_3 [2, 4, 2] = true := by decide +kernel
theorem subd9_3_1039 : subd9_3 [2, 4, 3] = true := by decide +kernel
theorem subd9_3_1040 : subd9_3 [2, 4, 4] = true := by decide +kernel
theorem subd9_3_1041 : subd9_3 [2, 4, 5] = true := by decide +kernel
theorem subd9_3_1042 : subd9_3 [2, 4, 6] = true := by decide +kernel
theorem subd9_3_1043 : subd9_3 [2, 4, 7] = true := by decide +kernel
theorem subd9_3_1044 : subd9_3 [2, 5] = true := by decide +kernel
theorem subd9_3_1045 : subd9_3 [3, -6] = true := by decide +kernel
theorem subd9_3_1046 : subd9_3 [3, -5] = true := by decide +kernel
theorem subd9_3_1047 : subd9_3 [3, -4] = true := by decide +kernel
theorem subd9_3_1048 : subd9_3 [3, -3, -7] = true := by decide +kernel
theorem subd9_3_1049 : subd9_3 [3, -3, -6] = true := by decide +kernel
theorem subd9_3_1050 : subd9_3 [3, -3, -5] = true := by decide +kernel
theorem subd9_3_1051 : subd9_3 [3, -3, -4] = true := by decide +kernel
theorem subd9_3_1052 : subd9_3 [3, -3, -3] = true := by decide +kernel
theorem subd9_3_1053 : subd9_3 [3, -3, -2] = true := by decide +kernel
theorem subd9_3_1054 : subd9_3 [3, -3, -1] = true := by decide +kernel
theorem subd9_3_1055 : subd9_3 [3, -3, 0] = true := by decide +kernel
theorem sbd9_3_32 : ∀ q ∈ blkd9_3_32, subd9_3 q = true := by
  unfold blkd9_3_32
  exact List.forall_mem_cons.2 ⟨subd9_3_1024, List.forall_mem_cons.2 ⟨subd9_3_1025, List.forall_mem_cons.2 ⟨subd9_3_1026, List.forall_mem_cons.2 ⟨subd9_3_1027, List.forall_mem_cons.2 ⟨subd9_3_1028, List.forall_mem_cons.2 ⟨subd9_3_1029, List.forall_mem_cons.2 ⟨subd9_3_1030, List.forall_mem_cons.2 ⟨subd9_3_1031, List.forall_mem_cons.2 ⟨subd9_3_1032, List.forall_mem_cons.2 ⟨subd9_3_1033, List.forall_mem_cons.2 ⟨subd9_3_1034, List.forall_mem_cons.2 ⟨subd9_3_1035, List.forall_mem_cons.2 ⟨subd9_3_1036, List.forall_mem_cons.2 ⟨subd9_3_1037, List.forall_mem_cons.2 ⟨subd9_3_1038, List.forall_mem_cons.2 ⟨subd9_3_1039, List.forall_mem_cons.2 ⟨subd9_3_1040, List.forall_mem_cons.2 ⟨subd9_3_1041, List.forall_mem_cons.2 ⟨subd9_3_1042, List.forall_mem_cons.2 ⟨subd9_3_1043, List.forall_mem_cons.2 ⟨subd9_3_1044, List.forall_mem_cons.2 ⟨subd9_3_1045, List.forall_mem_cons.2 ⟨subd9_3_1046, List.forall_mem_cons.2 ⟨subd9_3_1047, List.forall_mem_cons.2 ⟨subd9_3_1048, List.forall_mem_cons.2 ⟨subd9_3_1049, List.forall_mem_cons.2 ⟨subd9_3_1050, List.forall_mem_cons.2 ⟨subd9_3_1051, List.forall_mem_cons.2 ⟨subd9_3_1052, List.forall_mem_cons.2 ⟨subd9_3_1053, List.forall_mem_cons.2 ⟨subd9_3_1054, List.forall_mem_cons.2 ⟨subd9_3_1055, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_1056 : subd9_3 [3, -3, 1] = true := by decide +kernel
theorem subd9_3_1057 : subd9_3 [3, -3, 2] = true := by decide +kernel
theorem subd9_3_1058 : subd9_3 [3, -3, 3] = true := by decide +kernel
theorem subd9_3_1059 : subd9_3 [3, -3, 4] = true := by decide +kernel
theorem subd9_3_1060 : subd9_3 [3, -3, 5] = true := by decide +kernel
theorem subd9_3_1061 : subd9_3 [3, -3, 6] = true := by decide +kernel
theorem subd9_3_1062 : subd9_3 [3, -3, 7] = true := by decide +kernel
theorem subd9_3_1063 : subd9_3 [3, -2, -8] = true := by decide +kernel
theorem subd9_3_1064 : subd9_3 [3, -2, -7] = true := by decide +kernel
theorem subd9_3_1065 : subd9_3 [3, -2, -6] = true := by decide +kernel
theorem subd9_3_1066 : subd9_3 [3, -2, -5] = true := by decide +kernel
theorem subd9_3_1067 : subd9_3 [3, -2, -4] = true := by decide +kernel
theorem subd9_3_1068 : subd9_3 [3, -2, -3] = true := by decide +kernel
theorem subd9_3_1069 : subd9_3 [3, -2, -2] = true := by decide +kernel
theorem subd9_3_1070 : subd9_3 [3, -2, -1] = true := by decide +kernel
theorem subd9_3_1071 : subd9_3 [3, -2, 0] = true := by decide +kernel
theorem subd9_3_1072 : subd9_3 [3, -2, 1] = true := by decide +kernel
theorem subd9_3_1073 : subd9_3 [3, -2, 2] = true := by decide +kernel
theorem subd9_3_1074 : subd9_3 [3, -2, 3] = true := by decide +kernel
theorem subd9_3_1075 : subd9_3 [3, -2, 4] = true := by decide +kernel
theorem subd9_3_1076 : subd9_3 [3, -2, 5] = true := by decide +kernel
theorem subd9_3_1077 : subd9_3 [3, -2, 6] = true := by decide +kernel
theorem subd9_3_1078 : subd9_3 [3, -2, 7] = true := by decide +kernel
theorem subd9_3_1079 : subd9_3 [3, -2, 8] = true := by decide +kernel
theorem subd9_3_1080 : subd9_3 [3, -1, -9] = true := by decide +kernel
theorem subd9_3_1081 : subd9_3 [3, -1, -8] = true := by decide +kernel
theorem subd9_3_1082 : subd9_3 [3, -1, -7] = true := by decide +kernel
theorem subd9_3_1083 : subd9_3 [3, -1, -6] = true := by decide +kernel
theorem subd9_3_1084 : subd9_3 [3, -1, -5] = true := by decide +kernel
theorem subd9_3_1085 : subd9_3 [3, -1, -4] = true := by decide +kernel
theorem subd9_3_1086 : subd9_3 [3, -1, -3] = true := by decide +kernel
theorem subd9_3_1087 : subd9_3 [3, -1, -2] = true := by decide +kernel
theorem sbd9_3_33 : ∀ q ∈ blkd9_3_33, subd9_3 q = true := by
  unfold blkd9_3_33
  exact List.forall_mem_cons.2 ⟨subd9_3_1056, List.forall_mem_cons.2 ⟨subd9_3_1057, List.forall_mem_cons.2 ⟨subd9_3_1058, List.forall_mem_cons.2 ⟨subd9_3_1059, List.forall_mem_cons.2 ⟨subd9_3_1060, List.forall_mem_cons.2 ⟨subd9_3_1061, List.forall_mem_cons.2 ⟨subd9_3_1062, List.forall_mem_cons.2 ⟨subd9_3_1063, List.forall_mem_cons.2 ⟨subd9_3_1064, List.forall_mem_cons.2 ⟨subd9_3_1065, List.forall_mem_cons.2 ⟨subd9_3_1066, List.forall_mem_cons.2 ⟨subd9_3_1067, List.forall_mem_cons.2 ⟨subd9_3_1068, List.forall_mem_cons.2 ⟨subd9_3_1069, List.forall_mem_cons.2 ⟨subd9_3_1070, List.forall_mem_cons.2 ⟨subd9_3_1071, List.forall_mem_cons.2 ⟨subd9_3_1072, List.forall_mem_cons.2 ⟨subd9_3_1073, List.forall_mem_cons.2 ⟨subd9_3_1074, List.forall_mem_cons.2 ⟨subd9_3_1075, List.forall_mem_cons.2 ⟨subd9_3_1076, List.forall_mem_cons.2 ⟨subd9_3_1077, List.forall_mem_cons.2 ⟨subd9_3_1078, List.forall_mem_cons.2 ⟨subd9_3_1079, List.forall_mem_cons.2 ⟨subd9_3_1080, List.forall_mem_cons.2 ⟨subd9_3_1081, List.forall_mem_cons.2 ⟨subd9_3_1082, List.forall_mem_cons.2 ⟨subd9_3_1083, List.forall_mem_cons.2 ⟨subd9_3_1084, List.forall_mem_cons.2 ⟨subd9_3_1085, List.forall_mem_cons.2 ⟨subd9_3_1086, List.forall_mem_cons.2 ⟨subd9_3_1087, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_1088 : subd9_3 [3, -1, -1] = true := by decide +kernel
theorem subd9_3_1089 : subd9_3 [3, -1, 0] = true := by decide +kernel
theorem subd9_3_1090 : subd9_3 [3, -1, 1] = true := by decide +kernel
theorem subd9_3_1091 : subd9_3 [3, -1, 2] = true := by decide +kernel
theorem subd9_3_1092 : subd9_3 [3, -1, 3] = true := by decide +kernel
theorem subd9_3_1093 : subd9_3 [3, -1, 4] = true := by decide +kernel
theorem subd9_3_1094 : subd9_3 [3, -1, 5] = true := by decide +kernel
theorem subd9_3_1095 : subd9_3 [3, -1, 6] = true := by decide +kernel
theorem subd9_3_1096 : subd9_3 [3, -1, 7] = true := by decide +kernel
theorem subd9_3_1097 : subd9_3 [3, -1, 8] = true := by decide +kernel
theorem subd9_3_1098 : subd9_3 [3, 0, -9] = true := by decide +kernel
theorem subd9_3_1099 : subd9_3 [3, 0, -8] = true := by decide +kernel
theorem subd9_3_1100 : subd9_3 [3, 0, -7] = true := by decide +kernel
theorem subd9_3_1101 : subd9_3 [3, 0, -6] = true := by decide +kernel
theorem subd9_3_1102 : subd9_3 [3, 0, -5] = true := by decide +kernel
theorem subd9_3_1103 : subd9_3 [3, 0, -4] = true := by decide +kernel
theorem subd9_3_1104 : subd9_3 [3, 0, -3] = true := by decide +kernel
theorem subd9_3_1105 : subd9_3 [3, 0, -2] = true := by decide +kernel
theorem subd9_3_1106 : subd9_3 [3, 0, -1] = true := by decide +kernel
theorem subd9_3_1107 : subd9_3 [3, 0, 0] = true := by decide +kernel
theorem subd9_3_1108 : subd9_3 [3, 0, 1] = true := by decide +kernel
theorem subd9_3_1109 : subd9_3 [3, 0, 2] = true := by decide +kernel
theorem subd9_3_1110 : subd9_3 [3, 0, 3] = true := by decide +kernel
theorem subd9_3_1111 : subd9_3 [3, 0, 4] = true := by decide +kernel
theorem subd9_3_1112 : subd9_3 [3, 0, 5] = true := by decide +kernel
theorem subd9_3_1113 : subd9_3 [3, 0, 6] = true := by decide +kernel
theorem subd9_3_1114 : subd9_3 [3, 0, 7] = true := by decide +kernel
theorem subd9_3_1115 : subd9_3 [3, 0, 8] = true := by decide +kernel
theorem subd9_3_1116 : subd9_3 [3, 1, -8] = true := by decide +kernel
theorem subd9_3_1117 : subd9_3 [3, 1, -7] = true := by decide +kernel
theorem subd9_3_1118 : subd9_3 [3, 1, -6] = true := by decide +kernel
theorem subd9_3_1119 : subd9_3 [3, 1, -5] = true := by decide +kernel
theorem sbd9_3_34 : ∀ q ∈ blkd9_3_34, subd9_3 q = true := by
  unfold blkd9_3_34
  exact List.forall_mem_cons.2 ⟨subd9_3_1088, List.forall_mem_cons.2 ⟨subd9_3_1089, List.forall_mem_cons.2 ⟨subd9_3_1090, List.forall_mem_cons.2 ⟨subd9_3_1091, List.forall_mem_cons.2 ⟨subd9_3_1092, List.forall_mem_cons.2 ⟨subd9_3_1093, List.forall_mem_cons.2 ⟨subd9_3_1094, List.forall_mem_cons.2 ⟨subd9_3_1095, List.forall_mem_cons.2 ⟨subd9_3_1096, List.forall_mem_cons.2 ⟨subd9_3_1097, List.forall_mem_cons.2 ⟨subd9_3_1098, List.forall_mem_cons.2 ⟨subd9_3_1099, List.forall_mem_cons.2 ⟨subd9_3_1100, List.forall_mem_cons.2 ⟨subd9_3_1101, List.forall_mem_cons.2 ⟨subd9_3_1102, List.forall_mem_cons.2 ⟨subd9_3_1103, List.forall_mem_cons.2 ⟨subd9_3_1104, List.forall_mem_cons.2 ⟨subd9_3_1105, List.forall_mem_cons.2 ⟨subd9_3_1106, List.forall_mem_cons.2 ⟨subd9_3_1107, List.forall_mem_cons.2 ⟨subd9_3_1108, List.forall_mem_cons.2 ⟨subd9_3_1109, List.forall_mem_cons.2 ⟨subd9_3_1110, List.forall_mem_cons.2 ⟨subd9_3_1111, List.forall_mem_cons.2 ⟨subd9_3_1112, List.forall_mem_cons.2 ⟨subd9_3_1113, List.forall_mem_cons.2 ⟨subd9_3_1114, List.forall_mem_cons.2 ⟨subd9_3_1115, List.forall_mem_cons.2 ⟨subd9_3_1116, List.forall_mem_cons.2 ⟨subd9_3_1117, List.forall_mem_cons.2 ⟨subd9_3_1118, List.forall_mem_cons.2 ⟨subd9_3_1119, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_1120 : subd9_3 [3, 1, -4] = true := by decide +kernel
theorem subd9_3_1121 : subd9_3 [3, 1, -3] = true := by decide +kernel
theorem subd9_3_1122 : subd9_3 [3, 1, -2] = true := by decide +kernel
theorem subd9_3_1123 : subd9_3 [3, 1, -1] = true := by decide +kernel
theorem subd9_3_1124 : subd9_3 [3, 1, 0] = true := by decide +kernel
theorem subd9_3_1125 : subd9_3 [3, 1, 1] = true := by decide +kernel
theorem subd9_3_1126 : subd9_3 [3, 1, 2] = true := by decide +kernel
theorem subd9_3_1127 : subd9_3 [3, 1, 3] = true := by decide +kernel
theorem subd9_3_1128 : subd9_3 [3, 1, 4] = true := by decide +kernel
theorem subd9_3_1129 : subd9_3 [3, 1, 5] = true := by decide +kernel
theorem subd9_3_1130 : subd9_3 [3, 1, 6] = true := by decide +kernel
theorem subd9_3_1131 : subd9_3 [3, 1, 7] = true := by decide +kernel
theorem subd9_3_1132 : subd9_3 [3, 1, 8] = true := by decide +kernel
theorem subd9_3_1133 : subd9_3 [3, 2, -8] = true := by decide +kernel
theorem subd9_3_1134 : subd9_3 [3, 2, -7] = true := by decide +kernel
theorem subd9_3_1135 : subd9_3 [3, 2, -6] = true := by decide +kernel
theorem subd9_3_1136 : subd9_3 [3, 2, -5] = true := by decide +kernel
theorem subd9_3_1137 : subd9_3 [3, 2, -4] = true := by decide +kernel
theorem subd9_3_1138 : subd9_3 [3, 2, -3] = true := by decide +kernel
theorem subd9_3_1139 : subd9_3 [3, 2, -2] = true := by decide +kernel
theorem subd9_3_1140 : subd9_3 [3, 2, -1] = true := by decide +kernel
theorem subd9_3_1141 : subd9_3 [3, 2, 0] = true := by decide +kernel
theorem subd9_3_1142 : subd9_3 [3, 2, 1] = true := by decide +kernel
theorem subd9_3_1143 : subd9_3 [3, 2, 2] = true := by decide +kernel
theorem subd9_3_1144 : subd9_3 [3, 2, 3] = true := by decide +kernel
theorem subd9_3_1145 : subd9_3 [3, 2, 4] = true := by decide +kernel
theorem subd9_3_1146 : subd9_3 [3, 2, 5] = true := by decide +kernel
theorem subd9_3_1147 : subd9_3 [3, 2, 6] = true := by decide +kernel
theorem subd9_3_1148 : subd9_3 [3, 2, 7] = true := by decide +kernel
theorem subd9_3_1149 : subd9_3 [3, 2, 8] = true := by decide +kernel
theorem subd9_3_1150 : subd9_3 [3, 3, -7] = true := by decide +kernel
theorem subd9_3_1151 : subd9_3 [3, 3, -6] = true := by decide +kernel
theorem sbd9_3_35 : ∀ q ∈ blkd9_3_35, subd9_3 q = true := by
  unfold blkd9_3_35
  exact List.forall_mem_cons.2 ⟨subd9_3_1120, List.forall_mem_cons.2 ⟨subd9_3_1121, List.forall_mem_cons.2 ⟨subd9_3_1122, List.forall_mem_cons.2 ⟨subd9_3_1123, List.forall_mem_cons.2 ⟨subd9_3_1124, List.forall_mem_cons.2 ⟨subd9_3_1125, List.forall_mem_cons.2 ⟨subd9_3_1126, List.forall_mem_cons.2 ⟨subd9_3_1127, List.forall_mem_cons.2 ⟨subd9_3_1128, List.forall_mem_cons.2 ⟨subd9_3_1129, List.forall_mem_cons.2 ⟨subd9_3_1130, List.forall_mem_cons.2 ⟨subd9_3_1131, List.forall_mem_cons.2 ⟨subd9_3_1132, List.forall_mem_cons.2 ⟨subd9_3_1133, List.forall_mem_cons.2 ⟨subd9_3_1134, List.forall_mem_cons.2 ⟨subd9_3_1135, List.forall_mem_cons.2 ⟨subd9_3_1136, List.forall_mem_cons.2 ⟨subd9_3_1137, List.forall_mem_cons.2 ⟨subd9_3_1138, List.forall_mem_cons.2 ⟨subd9_3_1139, List.forall_mem_cons.2 ⟨subd9_3_1140, List.forall_mem_cons.2 ⟨subd9_3_1141, List.forall_mem_cons.2 ⟨subd9_3_1142, List.forall_mem_cons.2 ⟨subd9_3_1143, List.forall_mem_cons.2 ⟨subd9_3_1144, List.forall_mem_cons.2 ⟨subd9_3_1145, List.forall_mem_cons.2 ⟨subd9_3_1146, List.forall_mem_cons.2 ⟨subd9_3_1147, List.forall_mem_cons.2 ⟨subd9_3_1148, List.forall_mem_cons.2 ⟨subd9_3_1149, List.forall_mem_cons.2 ⟨subd9_3_1150, List.forall_mem_cons.2 ⟨subd9_3_1151, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_1152 : subd9_3 [3, 3, -5] = true := by decide +kernel
theorem subd9_3_1153 : subd9_3 [3, 3, -4] = true := by decide +kernel
theorem subd9_3_1154 : subd9_3 [3, 3, -3] = true := by decide +kernel
theorem subd9_3_1155 : subd9_3 [3, 3, -2] = true := by decide +kernel
theorem subd9_3_1156 : subd9_3 [3, 3, -1] = true := by decide +kernel
theorem subd9_3_1157 : subd9_3 [3, 3, 0] = true := by decide +kernel
theorem subd9_3_1158 : subd9_3 [3, 3, 1] = true := by decide +kernel
theorem subd9_3_1159 : subd9_3 [3, 3, 2] = true := by decide +kernel
theorem subd9_3_1160 : subd9_3 [3, 3, 3] = true := by decide +kernel
theorem subd9_3_1161 : subd9_3 [3, 3, 4] = true := by decide +kernel
theorem subd9_3_1162 : subd9_3 [3, 3, 5] = true := by decide +kernel
theorem subd9_3_1163 : subd9_3 [3, 3, 6] = true := by decide +kernel
theorem subd9_3_1164 : subd9_3 [3, 3, 7] = true := by decide +kernel
theorem subd9_3_1165 : subd9_3 [3, 4] = true := by decide +kernel
theorem subd9_3_1166 : subd9_3 [3, 5] = true := by decide +kernel
theorem subd9_3_1167 : subd9_3 [4, -5] = true := by decide +kernel
theorem subd9_3_1168 : subd9_3 [4, -4] = true := by decide +kernel
theorem subd9_3_1169 : subd9_3 [4, -3] = true := by decide +kernel
theorem subd9_3_1170 : subd9_3 [4, -2, -7] = true := by decide +kernel
theorem subd9_3_1171 : subd9_3 [4, -2, -6] = true := by decide +kernel
theorem subd9_3_1172 : subd9_3 [4, -2, -5] = true := by decide +kernel
theorem subd9_3_1173 : subd9_3 [4, -2, -4] = true := by decide +kernel
theorem subd9_3_1174 : subd9_3 [4, -2, -3] = true := by decide +kernel
theorem subd9_3_1175 : subd9_3 [4, -2, -2] = true := by decide +kernel
theorem subd9_3_1176 : subd9_3 [4, -2, -1] = true := by decide +kernel
theorem subd9_3_1177 : subd9_3 [4, -2, 0] = true := by decide +kernel
theorem subd9_3_1178 : subd9_3 [4, -2, 1] = true := by decide +kernel
theorem subd9_3_1179 : subd9_3 [4, -2, 2] = true := by decide +kernel
theorem subd9_3_1180 : subd9_3 [4, -2, 3] = true := by decide +kernel
theorem subd9_3_1181 : subd9_3 [4, -2, 4] = true := by decide +kernel
theorem subd9_3_1182 : subd9_3 [4, -2, 5] = true := by decide +kernel
theorem subd9_3_1183 : subd9_3 [4, -2, 6] = true := by decide +kernel
theorem sbd9_3_36 : ∀ q ∈ blkd9_3_36, subd9_3 q = true := by
  unfold blkd9_3_36
  exact List.forall_mem_cons.2 ⟨subd9_3_1152, List.forall_mem_cons.2 ⟨subd9_3_1153, List.forall_mem_cons.2 ⟨subd9_3_1154, List.forall_mem_cons.2 ⟨subd9_3_1155, List.forall_mem_cons.2 ⟨subd9_3_1156, List.forall_mem_cons.2 ⟨subd9_3_1157, List.forall_mem_cons.2 ⟨subd9_3_1158, List.forall_mem_cons.2 ⟨subd9_3_1159, List.forall_mem_cons.2 ⟨subd9_3_1160, List.forall_mem_cons.2 ⟨subd9_3_1161, List.forall_mem_cons.2 ⟨subd9_3_1162, List.forall_mem_cons.2 ⟨subd9_3_1163, List.forall_mem_cons.2 ⟨subd9_3_1164, List.forall_mem_cons.2 ⟨subd9_3_1165, List.forall_mem_cons.2 ⟨subd9_3_1166, List.forall_mem_cons.2 ⟨subd9_3_1167, List.forall_mem_cons.2 ⟨subd9_3_1168, List.forall_mem_cons.2 ⟨subd9_3_1169, List.forall_mem_cons.2 ⟨subd9_3_1170, List.forall_mem_cons.2 ⟨subd9_3_1171, List.forall_mem_cons.2 ⟨subd9_3_1172, List.forall_mem_cons.2 ⟨subd9_3_1173, List.forall_mem_cons.2 ⟨subd9_3_1174, List.forall_mem_cons.2 ⟨subd9_3_1175, List.forall_mem_cons.2 ⟨subd9_3_1176, List.forall_mem_cons.2 ⟨subd9_3_1177, List.forall_mem_cons.2 ⟨subd9_3_1178, List.forall_mem_cons.2 ⟨subd9_3_1179, List.forall_mem_cons.2 ⟨subd9_3_1180, List.forall_mem_cons.2 ⟨subd9_3_1181, List.forall_mem_cons.2 ⟨subd9_3_1182, List.forall_mem_cons.2 ⟨subd9_3_1183, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_1184 : subd9_3 [4, -2, 7] = true := by decide +kernel
theorem subd9_3_1185 : subd9_3 [4, -1, -7] = true := by decide +kernel
theorem subd9_3_1186 : subd9_3 [4, -1, -6] = true := by decide +kernel
theorem subd9_3_1187 : subd9_3 [4, -1, -5] = true := by decide +kernel
theorem subd9_3_1188 : subd9_3 [4, -1, -4] = true := by decide +kernel
theorem subd9_3_1189 : subd9_3 [4, -1, -3] = true := by decide +kernel
theorem subd9_3_1190 : subd9_3 [4, -1, -2] = true := by decide +kernel
theorem subd9_3_1191 : subd9_3 [4, -1, -1] = true := by decide +kernel
theorem subd9_3_1192 : subd9_3 [4, -1, 0] = true := by decide +kernel
theorem subd9_3_1193 : subd9_3 [4, -1, 1] = true := by decide +kernel
theorem subd9_3_1194 : subd9_3 [4, -1, 2] = true := by decide +kernel
theorem subd9_3_1195 : subd9_3 [4, -1, 3] = true := by decide +kernel
theorem subd9_3_1196 : subd9_3 [4, -1, 4] = true := by decide +kernel
theorem subd9_3_1197 : subd9_3 [4, -1, 5] = true := by decide +kernel
theorem subd9_3_1198 : subd9_3 [4, -1, 6] = true := by decide +kernel
theorem subd9_3_1199 : subd9_3 [4, -1, 7] = true := by decide +kernel
theorem subd9_3_1200 : subd9_3 [4, 0, -7] = true := by decide +kernel
theorem subd9_3_1201 : subd9_3 [4, 0, -6] = true := by decide +kernel
theorem subd9_3_1202 : subd9_3 [4, 0, -5] = true := by decide +kernel
theorem subd9_3_1203 : subd9_3 [4, 0, -4] = true := by decide +kernel
theorem subd9_3_1204 : subd9_3 [4, 0, -3] = true := by decide +kernel
theorem subd9_3_1205 : subd9_3 [4, 0, -2] = true := by decide +kernel
theorem subd9_3_1206 : subd9_3 [4, 0, -1] = true := by decide +kernel
theorem subd9_3_1207 : subd9_3 [4, 0, 0] = true := by decide +kernel
theorem subd9_3_1208 : subd9_3 [4, 0, 1] = true := by decide +kernel
theorem subd9_3_1209 : subd9_3 [4, 0, 2] = true := by decide +kernel
theorem subd9_3_1210 : subd9_3 [4, 0, 3] = true := by decide +kernel
theorem subd9_3_1211 : subd9_3 [4, 0, 4] = true := by decide +kernel
theorem subd9_3_1212 : subd9_3 [4, 0, 5] = true := by decide +kernel
theorem subd9_3_1213 : subd9_3 [4, 0, 6] = true := by decide +kernel
theorem subd9_3_1214 : subd9_3 [4, 0, 7] = true := by decide +kernel
theorem subd9_3_1215 : subd9_3 [4, 0, 8] = true := by decide +kernel
theorem sbd9_3_37 : ∀ q ∈ blkd9_3_37, subd9_3 q = true := by
  unfold blkd9_3_37
  exact List.forall_mem_cons.2 ⟨subd9_3_1184, List.forall_mem_cons.2 ⟨subd9_3_1185, List.forall_mem_cons.2 ⟨subd9_3_1186, List.forall_mem_cons.2 ⟨subd9_3_1187, List.forall_mem_cons.2 ⟨subd9_3_1188, List.forall_mem_cons.2 ⟨subd9_3_1189, List.forall_mem_cons.2 ⟨subd9_3_1190, List.forall_mem_cons.2 ⟨subd9_3_1191, List.forall_mem_cons.2 ⟨subd9_3_1192, List.forall_mem_cons.2 ⟨subd9_3_1193, List.forall_mem_cons.2 ⟨subd9_3_1194, List.forall_mem_cons.2 ⟨subd9_3_1195, List.forall_mem_cons.2 ⟨subd9_3_1196, List.forall_mem_cons.2 ⟨subd9_3_1197, List.forall_mem_cons.2 ⟨subd9_3_1198, List.forall_mem_cons.2 ⟨subd9_3_1199, List.forall_mem_cons.2 ⟨subd9_3_1200, List.forall_mem_cons.2 ⟨subd9_3_1201, List.forall_mem_cons.2 ⟨subd9_3_1202, List.forall_mem_cons.2 ⟨subd9_3_1203, List.forall_mem_cons.2 ⟨subd9_3_1204, List.forall_mem_cons.2 ⟨subd9_3_1205, List.forall_mem_cons.2 ⟨subd9_3_1206, List.forall_mem_cons.2 ⟨subd9_3_1207, List.forall_mem_cons.2 ⟨subd9_3_1208, List.forall_mem_cons.2 ⟨subd9_3_1209, List.forall_mem_cons.2 ⟨subd9_3_1210, List.forall_mem_cons.2 ⟨subd9_3_1211, List.forall_mem_cons.2 ⟨subd9_3_1212, List.forall_mem_cons.2 ⟨subd9_3_1213, List.forall_mem_cons.2 ⟨subd9_3_1214, List.forall_mem_cons.2 ⟨subd9_3_1215, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_1216 : subd9_3 [4, 1, -7] = true := by decide +kernel
theorem subd9_3_1217 : subd9_3 [4, 1, -6] = true := by decide +kernel
theorem subd9_3_1218 : subd9_3 [4, 1, -5] = true := by decide +kernel
theorem subd9_3_1219 : subd9_3 [4, 1, -4] = true := by decide +kernel
theorem subd9_3_1220 : subd9_3 [4, 1, -3] = true := by decide +kernel
theorem subd9_3_1221 : subd9_3 [4, 1, -2] = true := by decide +kernel
theorem subd9_3_1222 : subd9_3 [4, 1, -1] = true := by decide +kernel
theorem subd9_3_1223 : subd9_3 [4, 1, 0] = true := by decide +kernel
theorem subd9_3_1224 : subd9_3 [4, 1, 1] = true := by decide +kernel
theorem subd9_3_1225 : subd9_3 [4, 1, 2] = true := by decide +kernel
theorem subd9_3_1226 : subd9_3 [4, 1, 3] = true := by decide +kernel
theorem subd9_3_1227 : subd9_3 [4, 1, 4] = true := by decide +kernel
theorem subd9_3_1228 : subd9_3 [4, 1, 5] = true := by decide +kernel
theorem subd9_3_1229 : subd9_3 [4, 1, 6] = true := by decide +kernel
theorem subd9_3_1230 : subd9_3 [4, 1, 7] = true := by decide +kernel
theorem subd9_3_1231 : subd9_3 [4, 2, -7] = true := by decide +kernel
theorem subd9_3_1232 : subd9_3 [4, 2, -6] = true := by decide +kernel
theorem subd9_3_1233 : subd9_3 [4, 2, -5] = true := by decide +kernel
theorem subd9_3_1234 : subd9_3 [4, 2, -4] = true := by decide +kernel
theorem subd9_3_1235 : subd9_3 [4, 2, -3] = true := by decide +kernel
theorem subd9_3_1236 : subd9_3 [4, 2, -2] = true := by decide +kernel
theorem subd9_3_1237 : subd9_3 [4, 2, -1] = true := by decide +kernel
theorem subd9_3_1238 : subd9_3 [4, 2, 0] = true := by decide +kernel
theorem subd9_3_1239 : subd9_3 [4, 2, 1] = true := by decide +kernel
theorem subd9_3_1240 : subd9_3 [4, 2, 2] = true := by decide +kernel
theorem subd9_3_1241 : subd9_3 [4, 2, 3] = true := by decide +kernel
theorem subd9_3_1242 : subd9_3 [4, 2, 4] = true := by decide +kernel
theorem subd9_3_1243 : subd9_3 [4, 2, 5] = true := by decide +kernel
theorem subd9_3_1244 : subd9_3 [4, 2, 6] = true := by decide +kernel
theorem subd9_3_1245 : subd9_3 [4, 2, 7] = true := by decide +kernel
theorem subd9_3_1246 : subd9_3 [4, 3] = true := by decide +kernel
theorem subd9_3_1247 : subd9_3 [4, 4] = true := by decide +kernel
theorem sbd9_3_38 : ∀ q ∈ blkd9_3_38, subd9_3 q = true := by
  unfold blkd9_3_38
  exact List.forall_mem_cons.2 ⟨subd9_3_1216, List.forall_mem_cons.2 ⟨subd9_3_1217, List.forall_mem_cons.2 ⟨subd9_3_1218, List.forall_mem_cons.2 ⟨subd9_3_1219, List.forall_mem_cons.2 ⟨subd9_3_1220, List.forall_mem_cons.2 ⟨subd9_3_1221, List.forall_mem_cons.2 ⟨subd9_3_1222, List.forall_mem_cons.2 ⟨subd9_3_1223, List.forall_mem_cons.2 ⟨subd9_3_1224, List.forall_mem_cons.2 ⟨subd9_3_1225, List.forall_mem_cons.2 ⟨subd9_3_1226, List.forall_mem_cons.2 ⟨subd9_3_1227, List.forall_mem_cons.2 ⟨subd9_3_1228, List.forall_mem_cons.2 ⟨subd9_3_1229, List.forall_mem_cons.2 ⟨subd9_3_1230, List.forall_mem_cons.2 ⟨subd9_3_1231, List.forall_mem_cons.2 ⟨subd9_3_1232, List.forall_mem_cons.2 ⟨subd9_3_1233, List.forall_mem_cons.2 ⟨subd9_3_1234, List.forall_mem_cons.2 ⟨subd9_3_1235, List.forall_mem_cons.2 ⟨subd9_3_1236, List.forall_mem_cons.2 ⟨subd9_3_1237, List.forall_mem_cons.2 ⟨subd9_3_1238, List.forall_mem_cons.2 ⟨subd9_3_1239, List.forall_mem_cons.2 ⟨subd9_3_1240, List.forall_mem_cons.2 ⟨subd9_3_1241, List.forall_mem_cons.2 ⟨subd9_3_1242, List.forall_mem_cons.2 ⟨subd9_3_1243, List.forall_mem_cons.2 ⟨subd9_3_1244, List.forall_mem_cons.2 ⟨subd9_3_1245, List.forall_mem_cons.2 ⟨subd9_3_1246, List.forall_mem_cons.2 ⟨subd9_3_1247, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_1248 : subd9_3 [5, -4] = true := by decide +kernel
theorem subd9_3_1249 : subd9_3 [5, -3] = true := by decide +kernel
theorem subd9_3_1250 : subd9_3 [5, -2] = true := by decide +kernel
theorem subd9_3_1251 : subd9_3 [5, -1] = true := by decide +kernel
theorem subd9_3_1252 : subd9_3 [5, 0] = true := by decide +kernel
theorem subd9_3_1253 : subd9_3 [5, 1] = true := by decide +kernel
theorem subd9_3_1254 : subd9_3 [5, 2] = true := by decide +kernel
theorem subd9_3_1255 : subd9_3 [5, 3] = true := by decide +kernel
theorem subd9_3_1256 : subd9_3 [6] = true := by decide +kernel
theorem sbd9_3_39 : ∀ q ∈ blkd9_3_39, subd9_3 q = true := by
  unfold blkd9_3_39
  exact List.forall_mem_cons.2 ⟨subd9_3_1248, List.forall_mem_cons.2 ⟨subd9_3_1249, List.forall_mem_cons.2 ⟨subd9_3_1250, List.forall_mem_cons.2 ⟨subd9_3_1251, List.forall_mem_cons.2 ⟨subd9_3_1252, List.forall_mem_cons.2 ⟨subd9_3_1253, List.forall_mem_cons.2 ⟨subd9_3_1254, List.forall_mem_cons.2 ⟨subd9_3_1255, List.forall_mem_cons.2 ⟨subd9_3_1256, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_4 : ldCheck G d9_4.U d9_4.ms ldd9_4 = true := by decide +kernel
theorem pre_okd9_4 : subPre G cell9 d9_4 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C096
