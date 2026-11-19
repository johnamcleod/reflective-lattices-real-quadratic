import ReflectZphi.Data.Cert5.C093.Base

namespace ReflectZphi.Data.Cert5.C093

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_0_960 : subd6_0 [1, -1, -1] = true := by decide +kernel
theorem subd6_0_961 : subd6_0 [1, -1, 0] = true := by decide +kernel
theorem subd6_0_962 : subd6_0 [1, -1, 1] = true := by decide +kernel
theorem subd6_0_963 : subd6_0 [1, -1, 2] = true := by decide +kernel
theorem subd6_0_964 : subd6_0 [1, -1, 3] = true := by decide +kernel
theorem subd6_0_965 : subd6_0 [1, -1, 4] = true := by decide +kernel
theorem subd6_0_966 : subd6_0 [1, -1, 5] = true := by decide +kernel
theorem subd6_0_967 : subd6_0 [1, -1, 6] = true := by decide +kernel
theorem subd6_0_968 : subd6_0 [1, -1, 7] = true := by decide +kernel
theorem subd6_0_969 : subd6_0 [1, -1, 8] = true := by decide +kernel
theorem subd6_0_970 : subd6_0 [1, 0, -9] = true := by decide +kernel
theorem subd6_0_971 : subd6_0 [1, 0, -8] = true := by decide +kernel
theorem subd6_0_972 : subd6_0 [1, 0, -7] = true := by decide +kernel
theorem subd6_0_973 : subd6_0 [1, 0, -6] = true := by decide +kernel
theorem subd6_0_974 : subd6_0 [1, 0, -5] = true := by decide +kernel
theorem subd6_0_975 : subd6_0 [1, 0, -4] = true := by decide +kernel
theorem subd6_0_976 : subd6_0 [1, 0, -3] = true := by decide +kernel
theorem subd6_0_977 : subd6_0 [1, 0, -2] = true := by decide +kernel
theorem subd6_0_978 : subd6_0 [1, 0, -1] = true := by decide +kernel
theorem subd6_0_979 : subd6_0 [1, 0, 0] = true := by decide +kernel
theorem subd6_0_980 : subd6_0 [1, 0, 1] = true := by decide +kernel
theorem subd6_0_981 : subd6_0 [1, 0, 2] = true := by decide +kernel
theorem subd6_0_982 : subd6_0 [1, 0, 3] = true := by decide +kernel
theorem subd6_0_983 : subd6_0 [1, 0, 4] = true := by decide +kernel
theorem subd6_0_984 : subd6_0 [1, 0, 5] = true := by decide +kernel
theorem subd6_0_985 : subd6_0 [1, 0, 6] = true := by decide +kernel
theorem subd6_0_986 : subd6_0 [1, 0, 7] = true := by decide +kernel
theorem subd6_0_987 : subd6_0 [1, 0, 8] = true := by decide +kernel
theorem subd6_0_988 : subd6_0 [1, 1, -9] = true := by decide +kernel
theorem subd6_0_989 : subd6_0 [1, 1, -8] = true := by decide +kernel
theorem subd6_0_990 : subd6_0 [1, 1, -7] = true := by decide +kernel
theorem subd6_0_991 : subd6_0 [1, 1, -6] = true := by decide +kernel
theorem sbd6_0_30 : ∀ q ∈ blkd6_0_30, subd6_0 q = true := by
  unfold blkd6_0_30
  exact List.forall_mem_cons.2 ⟨subd6_0_960, List.forall_mem_cons.2 ⟨subd6_0_961, List.forall_mem_cons.2 ⟨subd6_0_962, List.forall_mem_cons.2 ⟨subd6_0_963, List.forall_mem_cons.2 ⟨subd6_0_964, List.forall_mem_cons.2 ⟨subd6_0_965, List.forall_mem_cons.2 ⟨subd6_0_966, List.forall_mem_cons.2 ⟨subd6_0_967, List.forall_mem_cons.2 ⟨subd6_0_968, List.forall_mem_cons.2 ⟨subd6_0_969, List.forall_mem_cons.2 ⟨subd6_0_970, List.forall_mem_cons.2 ⟨subd6_0_971, List.forall_mem_cons.2 ⟨subd6_0_972, List.forall_mem_cons.2 ⟨subd6_0_973, List.forall_mem_cons.2 ⟨subd6_0_974, List.forall_mem_cons.2 ⟨subd6_0_975, List.forall_mem_cons.2 ⟨subd6_0_976, List.forall_mem_cons.2 ⟨subd6_0_977, List.forall_mem_cons.2 ⟨subd6_0_978, List.forall_mem_cons.2 ⟨subd6_0_979, List.forall_mem_cons.2 ⟨subd6_0_980, List.forall_mem_cons.2 ⟨subd6_0_981, List.forall_mem_cons.2 ⟨subd6_0_982, List.forall_mem_cons.2 ⟨subd6_0_983, List.forall_mem_cons.2 ⟨subd6_0_984, List.forall_mem_cons.2 ⟨subd6_0_985, List.forall_mem_cons.2 ⟨subd6_0_986, List.forall_mem_cons.2 ⟨subd6_0_987, List.forall_mem_cons.2 ⟨subd6_0_988, List.forall_mem_cons.2 ⟨subd6_0_989, List.forall_mem_cons.2 ⟨subd6_0_990, List.forall_mem_cons.2 ⟨subd6_0_991, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_992 : subd6_0 [1, 1, -5] = true := by decide +kernel
theorem subd6_0_993 : subd6_0 [1, 1, -4] = true := by decide +kernel
theorem subd6_0_994 : subd6_0 [1, 1, -3] = true := by decide +kernel
theorem subd6_0_995 : subd6_0 [1, 1, -2] = true := by decide +kernel
theorem subd6_0_996 : subd6_0 [1, 1, -1] = true := by decide +kernel
theorem subd6_0_997 : subd6_0 [1, 1, 0] = true := by decide +kernel
theorem subd6_0_998 : subd6_0 [1, 1, 1] = true := by decide +kernel
theorem subd6_0_999 : subd6_0 [1, 1, 2] = true := by decide +kernel
theorem subd6_0_1000 : subd6_0 [1, 1, 3] = true := by decide +kernel
theorem subd6_0_1001 : subd6_0 [1, 1, 4] = true := by decide +kernel
theorem subd6_0_1002 : subd6_0 [1, 1, 5] = true := by decide +kernel
theorem subd6_0_1003 : subd6_0 [1, 1, 6] = true := by decide +kernel
theorem subd6_0_1004 : subd6_0 [1, 1, 7] = true := by decide +kernel
theorem subd6_0_1005 : subd6_0 [1, 1, 8] = true := by decide +kernel
theorem subd6_0_1006 : subd6_0 [1, 2, -9] = true := by decide +kernel
theorem subd6_0_1007 : subd6_0 [1, 2, -8] = true := by decide +kernel
theorem subd6_0_1008 : subd6_0 [1, 2, -7] = true := by decide +kernel
theorem subd6_0_1009 : subd6_0 [1, 2, -6] = true := by decide +kernel
theorem subd6_0_1010 : subd6_0 [1, 2, -5] = true := by decide +kernel
theorem subd6_0_1011 : subd6_0 [1, 2, -4] = true := by decide +kernel
theorem subd6_0_1012 : subd6_0 [1, 2, -3] = true := by decide +kernel
theorem subd6_0_1013 : subd6_0 [1, 2, -2] = true := by decide +kernel
theorem subd6_0_1014 : subd6_0 [1, 2, -1] = true := by decide +kernel
theorem subd6_0_1015 : subd6_0 [1, 2, 0] = true := by decide +kernel
theorem subd6_0_1016 : subd6_0 [1, 2, 1] = true := by decide +kernel
theorem subd6_0_1017 : subd6_0 [1, 2, 2] = true := by decide +kernel
theorem subd6_0_1018 : subd6_0 [1, 2, 3] = true := by decide +kernel
theorem subd6_0_1019 : subd6_0 [1, 2, 4] = true := by decide +kernel
theorem subd6_0_1020 : subd6_0 [1, 2, 5] = true := by decide +kernel
theorem subd6_0_1021 : subd6_0 [1, 2, 6] = true := by decide +kernel
theorem subd6_0_1022 : subd6_0 [1, 2, 7] = true := by decide +kernel
theorem subd6_0_1023 : subd6_0 [1, 3, -9] = true := by decide +kernel
theorem sbd6_0_31 : ∀ q ∈ blkd6_0_31, subd6_0 q = true := by
  unfold blkd6_0_31
  exact List.forall_mem_cons.2 ⟨subd6_0_992, List.forall_mem_cons.2 ⟨subd6_0_993, List.forall_mem_cons.2 ⟨subd6_0_994, List.forall_mem_cons.2 ⟨subd6_0_995, List.forall_mem_cons.2 ⟨subd6_0_996, List.forall_mem_cons.2 ⟨subd6_0_997, List.forall_mem_cons.2 ⟨subd6_0_998, List.forall_mem_cons.2 ⟨subd6_0_999, List.forall_mem_cons.2 ⟨subd6_0_1000, List.forall_mem_cons.2 ⟨subd6_0_1001, List.forall_mem_cons.2 ⟨subd6_0_1002, List.forall_mem_cons.2 ⟨subd6_0_1003, List.forall_mem_cons.2 ⟨subd6_0_1004, List.forall_mem_cons.2 ⟨subd6_0_1005, List.forall_mem_cons.2 ⟨subd6_0_1006, List.forall_mem_cons.2 ⟨subd6_0_1007, List.forall_mem_cons.2 ⟨subd6_0_1008, List.forall_mem_cons.2 ⟨subd6_0_1009, List.forall_mem_cons.2 ⟨subd6_0_1010, List.forall_mem_cons.2 ⟨subd6_0_1011, List.forall_mem_cons.2 ⟨subd6_0_1012, List.forall_mem_cons.2 ⟨subd6_0_1013, List.forall_mem_cons.2 ⟨subd6_0_1014, List.forall_mem_cons.2 ⟨subd6_0_1015, List.forall_mem_cons.2 ⟨subd6_0_1016, List.forall_mem_cons.2 ⟨subd6_0_1017, List.forall_mem_cons.2 ⟨subd6_0_1018, List.forall_mem_cons.2 ⟨subd6_0_1019, List.forall_mem_cons.2 ⟨subd6_0_1020, List.forall_mem_cons.2 ⟨subd6_0_1021, List.forall_mem_cons.2 ⟨subd6_0_1022, List.forall_mem_cons.2 ⟨subd6_0_1023, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_1024 : subd6_0 [1, 3, -8] = true := by decide +kernel
theorem subd6_0_1025 : subd6_0 [1, 3, -7] = true := by decide +kernel
theorem subd6_0_1026 : subd6_0 [1, 3, -6] = true := by decide +kernel
theorem subd6_0_1027 : subd6_0 [1, 3, -5] = true := by decide +kernel
theorem subd6_0_1028 : subd6_0 [1, 3, -4] = true := by decide +kernel
theorem subd6_0_1029 : subd6_0 [1, 3, -3] = true := by decide +kernel
theorem subd6_0_1030 : subd6_0 [1, 3, -2] = true := by decide +kernel
theorem subd6_0_1031 : subd6_0 [1, 3, -1] = true := by decide +kernel
theorem subd6_0_1032 : subd6_0 [1, 3, 0] = true := by decide +kernel
theorem subd6_0_1033 : subd6_0 [1, 3, 1] = true := by decide +kernel
theorem subd6_0_1034 : subd6_0 [1, 3, 2] = true := by decide +kernel
theorem subd6_0_1035 : subd6_0 [1, 3, 3] = true := by decide +kernel
theorem subd6_0_1036 : subd6_0 [1, 3, 4] = true := by decide +kernel
theorem subd6_0_1037 : subd6_0 [1, 3, 5] = true := by decide +kernel
theorem subd6_0_1038 : subd6_0 [1, 3, 6] = true := by decide +kernel
theorem subd6_0_1039 : subd6_0 [1, 3, 7] = true := by decide +kernel
theorem subd6_0_1040 : subd6_0 [1, 4, -8] = true := by decide +kernel
theorem subd6_0_1041 : subd6_0 [1, 4, -7] = true := by decide +kernel
theorem subd6_0_1042 : subd6_0 [1, 4, -6] = true := by decide +kernel
theorem subd6_0_1043 : subd6_0 [1, 4, -5] = true := by decide +kernel
theorem subd6_0_1044 : subd6_0 [1, 4, -4] = true := by decide +kernel
theorem subd6_0_1045 : subd6_0 [1, 4, -3] = true := by decide +kernel
theorem subd6_0_1046 : subd6_0 [1, 4, -2] = true := by decide +kernel
theorem subd6_0_1047 : subd6_0 [1, 4, -1] = true := by decide +kernel
theorem subd6_0_1048 : subd6_0 [1, 4, 0] = true := by decide +kernel
theorem subd6_0_1049 : subd6_0 [1, 4, 1] = true := by decide +kernel
theorem subd6_0_1050 : subd6_0 [1, 4, 2] = true := by decide +kernel
theorem subd6_0_1051 : subd6_0 [1, 4, 3] = true := by decide +kernel
theorem subd6_0_1052 : subd6_0 [1, 4, 4] = true := by decide +kernel
theorem subd6_0_1053 : subd6_0 [1, 4, 5] = true := by decide +kernel
theorem subd6_0_1054 : subd6_0 [1, 4, 6] = true := by decide +kernel
theorem subd6_0_1055 : subd6_0 [1, 5, -8] = true := by decide +kernel
theorem sbd6_0_32 : ∀ q ∈ blkd6_0_32, subd6_0 q = true := by
  unfold blkd6_0_32
  exact List.forall_mem_cons.2 ⟨subd6_0_1024, List.forall_mem_cons.2 ⟨subd6_0_1025, List.forall_mem_cons.2 ⟨subd6_0_1026, List.forall_mem_cons.2 ⟨subd6_0_1027, List.forall_mem_cons.2 ⟨subd6_0_1028, List.forall_mem_cons.2 ⟨subd6_0_1029, List.forall_mem_cons.2 ⟨subd6_0_1030, List.forall_mem_cons.2 ⟨subd6_0_1031, List.forall_mem_cons.2 ⟨subd6_0_1032, List.forall_mem_cons.2 ⟨subd6_0_1033, List.forall_mem_cons.2 ⟨subd6_0_1034, List.forall_mem_cons.2 ⟨subd6_0_1035, List.forall_mem_cons.2 ⟨subd6_0_1036, List.forall_mem_cons.2 ⟨subd6_0_1037, List.forall_mem_cons.2 ⟨subd6_0_1038, List.forall_mem_cons.2 ⟨subd6_0_1039, List.forall_mem_cons.2 ⟨subd6_0_1040, List.forall_mem_cons.2 ⟨subd6_0_1041, List.forall_mem_cons.2 ⟨subd6_0_1042, List.forall_mem_cons.2 ⟨subd6_0_1043, List.forall_mem_cons.2 ⟨subd6_0_1044, List.forall_mem_cons.2 ⟨subd6_0_1045, List.forall_mem_cons.2 ⟨subd6_0_1046, List.forall_mem_cons.2 ⟨subd6_0_1047, List.forall_mem_cons.2 ⟨subd6_0_1048, List.forall_mem_cons.2 ⟨subd6_0_1049, List.forall_mem_cons.2 ⟨subd6_0_1050, List.forall_mem_cons.2 ⟨subd6_0_1051, List.forall_mem_cons.2 ⟨subd6_0_1052, List.forall_mem_cons.2 ⟨subd6_0_1053, List.forall_mem_cons.2 ⟨subd6_0_1054, List.forall_mem_cons.2 ⟨subd6_0_1055, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_1056 : subd6_0 [1, 5, -7] = true := by decide +kernel
theorem subd6_0_1057 : subd6_0 [1, 5, -6] = true := by decide +kernel
theorem subd6_0_1058 : subd6_0 [1, 5, -5] = true := by decide +kernel
theorem subd6_0_1059 : subd6_0 [1, 5, -4] = true := by decide +kernel
theorem subd6_0_1060 : subd6_0 [1, 5, -3] = true := by decide +kernel
theorem subd6_0_1061 : subd6_0 [1, 5, -2] = true := by decide +kernel
theorem subd6_0_1062 : subd6_0 [1, 5, -1] = true := by decide +kernel
theorem subd6_0_1063 : subd6_0 [1, 5, 0] = true := by decide +kernel
theorem subd6_0_1064 : subd6_0 [1, 5, 1] = true := by decide +kernel
theorem subd6_0_1065 : subd6_0 [1, 5, 2] = true := by decide +kernel
theorem subd6_0_1066 : subd6_0 [1, 5, 3] = true := by decide +kernel
theorem subd6_0_1067 : subd6_0 [1, 5, 4] = true := by decide +kernel
theorem subd6_0_1068 : subd6_0 [1, 5, 5] = true := by decide +kernel
theorem subd6_0_1069 : subd6_0 [1, 6] = true := by decide +kernel
theorem subd6_0_1070 : subd6_0 [1, 7] = true := by decide +kernel
theorem subd6_0_1071 : subd6_0 [2, -9] = true := by decide +kernel
theorem subd6_0_1072 : subd6_0 [2, -8] = true := by decide +kernel
theorem subd6_0_1073 : subd6_0 [2, -7] = true := by decide +kernel
theorem subd6_0_1074 : subd6_0 [2, -6] = true := by decide +kernel
theorem subd6_0_1075 : subd6_0 [2, -5, -7] = true := by decide +kernel
theorem subd6_0_1076 : subd6_0 [2, -5, -6] = true := by decide +kernel
theorem subd6_0_1077 : subd6_0 [2, -5, -5] = true := by decide +kernel
theorem subd6_0_1078 : subd6_0 [2, -5, -4] = true := by decide +kernel
theorem subd6_0_1079 : subd6_0 [2, -5, -3] = true := by decide +kernel
theorem subd6_0_1080 : subd6_0 [2, -5, -2] = true := by decide +kernel
theorem subd6_0_1081 : subd6_0 [2, -5, -1] = true := by decide +kernel
theorem subd6_0_1082 : subd6_0 [2, -5, 0] = true := by decide +kernel
theorem subd6_0_1083 : subd6_0 [2, -5, 1] = true := by decide +kernel
theorem subd6_0_1084 : subd6_0 [2, -5, 2] = true := by decide +kernel
theorem subd6_0_1085 : subd6_0 [2, -5, 3] = true := by decide +kernel
theorem subd6_0_1086 : subd6_0 [2, -5, 4] = true := by decide +kernel
theorem subd6_0_1087 : subd6_0 [2, -5, 5] = true := by decide +kernel
theorem sbd6_0_33 : ∀ q ∈ blkd6_0_33, subd6_0 q = true := by
  unfold blkd6_0_33
  exact List.forall_mem_cons.2 ⟨subd6_0_1056, List.forall_mem_cons.2 ⟨subd6_0_1057, List.forall_mem_cons.2 ⟨subd6_0_1058, List.forall_mem_cons.2 ⟨subd6_0_1059, List.forall_mem_cons.2 ⟨subd6_0_1060, List.forall_mem_cons.2 ⟨subd6_0_1061, List.forall_mem_cons.2 ⟨subd6_0_1062, List.forall_mem_cons.2 ⟨subd6_0_1063, List.forall_mem_cons.2 ⟨subd6_0_1064, List.forall_mem_cons.2 ⟨subd6_0_1065, List.forall_mem_cons.2 ⟨subd6_0_1066, List.forall_mem_cons.2 ⟨subd6_0_1067, List.forall_mem_cons.2 ⟨subd6_0_1068, List.forall_mem_cons.2 ⟨subd6_0_1069, List.forall_mem_cons.2 ⟨subd6_0_1070, List.forall_mem_cons.2 ⟨subd6_0_1071, List.forall_mem_cons.2 ⟨subd6_0_1072, List.forall_mem_cons.2 ⟨subd6_0_1073, List.forall_mem_cons.2 ⟨subd6_0_1074, List.forall_mem_cons.2 ⟨subd6_0_1075, List.forall_mem_cons.2 ⟨subd6_0_1076, List.forall_mem_cons.2 ⟨subd6_0_1077, List.forall_mem_cons.2 ⟨subd6_0_1078, List.forall_mem_cons.2 ⟨subd6_0_1079, List.forall_mem_cons.2 ⟨subd6_0_1080, List.forall_mem_cons.2 ⟨subd6_0_1081, List.forall_mem_cons.2 ⟨subd6_0_1082, List.forall_mem_cons.2 ⟨subd6_0_1083, List.forall_mem_cons.2 ⟨subd6_0_1084, List.forall_mem_cons.2 ⟨subd6_0_1085, List.forall_mem_cons.2 ⟨subd6_0_1086, List.forall_mem_cons.2 ⟨subd6_0_1087, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_1088 : subd6_0 [2, -5, 6] = true := by decide +kernel
theorem subd6_0_1089 : subd6_0 [2, -5, 7] = true := by decide +kernel
theorem subd6_0_1090 : subd6_0 [2, -4, -7] = true := by decide +kernel
theorem subd6_0_1091 : subd6_0 [2, -4, -6] = true := by decide +kernel
theorem subd6_0_1092 : subd6_0 [2, -4, -5] = true := by decide +kernel
theorem subd6_0_1093 : subd6_0 [2, -4, -4] = true := by decide +kernel
theorem subd6_0_1094 : subd6_0 [2, -4, -3] = true := by decide +kernel
theorem subd6_0_1095 : subd6_0 [2, -4, -2] = true := by decide +kernel
theorem subd6_0_1096 : subd6_0 [2, -4, -1] = true := by decide +kernel
theorem subd6_0_1097 : subd6_0 [2, -4, 0] = true := by decide +kernel
theorem subd6_0_1098 : subd6_0 [2, -4, 1] = true := by decide +kernel
theorem subd6_0_1099 : subd6_0 [2, -4, 2] = true := by decide +kernel
theorem subd6_0_1100 : subd6_0 [2, -4, 3] = true := by decide +kernel
theorem subd6_0_1101 : subd6_0 [2, -4, 4] = true := by decide +kernel
theorem subd6_0_1102 : subd6_0 [2, -4, 5] = true := by decide +kernel
theorem subd6_0_1103 : subd6_0 [2, -4, 6] = true := by decide +kernel
theorem subd6_0_1104 : subd6_0 [2, -4, 7] = true := by decide +kernel
theorem subd6_0_1105 : subd6_0 [2, -3, -8] = true := by decide +kernel
theorem subd6_0_1106 : subd6_0 [2, -3, -7] = true := by decide +kernel
theorem subd6_0_1107 : subd6_0 [2, -3, -6] = true := by decide +kernel
theorem subd6_0_1108 : subd6_0 [2, -3, -5] = true := by decide +kernel
theorem subd6_0_1109 : subd6_0 [2, -3, -4] = true := by decide +kernel
theorem subd6_0_1110 : subd6_0 [2, -3, -3] = true := by decide +kernel
theorem subd6_0_1111 : subd6_0 [2, -3, -2] = true := by decide +kernel
theorem subd6_0_1112 : subd6_0 [2, -3, -1] = true := by decide +kernel
theorem subd6_0_1113 : subd6_0 [2, -3, 0] = true := by decide +kernel
theorem subd6_0_1114 : subd6_0 [2, -3, 1] = true := by decide +kernel
theorem subd6_0_1115 : subd6_0 [2, -3, 2] = true := by decide +kernel
theorem subd6_0_1116 : subd6_0 [2, -3, 3] = true := by decide +kernel
theorem subd6_0_1117 : subd6_0 [2, -3, 4] = true := by decide +kernel
theorem subd6_0_1118 : subd6_0 [2, -3, 5] = true := by decide +kernel
theorem subd6_0_1119 : subd6_0 [2, -3, 6] = true := by decide +kernel
theorem sbd6_0_34 : ∀ q ∈ blkd6_0_34, subd6_0 q = true := by
  unfold blkd6_0_34
  exact List.forall_mem_cons.2 ⟨subd6_0_1088, List.forall_mem_cons.2 ⟨subd6_0_1089, List.forall_mem_cons.2 ⟨subd6_0_1090, List.forall_mem_cons.2 ⟨subd6_0_1091, List.forall_mem_cons.2 ⟨subd6_0_1092, List.forall_mem_cons.2 ⟨subd6_0_1093, List.forall_mem_cons.2 ⟨subd6_0_1094, List.forall_mem_cons.2 ⟨subd6_0_1095, List.forall_mem_cons.2 ⟨subd6_0_1096, List.forall_mem_cons.2 ⟨subd6_0_1097, List.forall_mem_cons.2 ⟨subd6_0_1098, List.forall_mem_cons.2 ⟨subd6_0_1099, List.forall_mem_cons.2 ⟨subd6_0_1100, List.forall_mem_cons.2 ⟨subd6_0_1101, List.forall_mem_cons.2 ⟨subd6_0_1102, List.forall_mem_cons.2 ⟨subd6_0_1103, List.forall_mem_cons.2 ⟨subd6_0_1104, List.forall_mem_cons.2 ⟨subd6_0_1105, List.forall_mem_cons.2 ⟨subd6_0_1106, List.forall_mem_cons.2 ⟨subd6_0_1107, List.forall_mem_cons.2 ⟨subd6_0_1108, List.forall_mem_cons.2 ⟨subd6_0_1109, List.forall_mem_cons.2 ⟨subd6_0_1110, List.forall_mem_cons.2 ⟨subd6_0_1111, List.forall_mem_cons.2 ⟨subd6_0_1112, List.forall_mem_cons.2 ⟨subd6_0_1113, List.forall_mem_cons.2 ⟨subd6_0_1114, List.forall_mem_cons.2 ⟨subd6_0_1115, List.forall_mem_cons.2 ⟨subd6_0_1116, List.forall_mem_cons.2 ⟨subd6_0_1117, List.forall_mem_cons.2 ⟨subd6_0_1118, List.forall_mem_cons.2 ⟨subd6_0_1119, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_1120 : subd6_0 [2, -3, 7] = true := by decide +kernel
theorem subd6_0_1121 : subd6_0 [2, -2, -8] = true := by decide +kernel
theorem subd6_0_1122 : subd6_0 [2, -2, -7] = true := by decide +kernel
theorem subd6_0_1123 : subd6_0 [2, -2, -6] = true := by decide +kernel
theorem subd6_0_1124 : subd6_0 [2, -2, -5] = true := by decide +kernel
theorem subd6_0_1125 : subd6_0 [2, -2, -4] = true := by decide +kernel
theorem subd6_0_1126 : subd6_0 [2, -2, -3] = true := by decide +kernel
theorem subd6_0_1127 : subd6_0 [2, -2, -2] = true := by decide +kernel
theorem subd6_0_1128 : subd6_0 [2, -2, -1] = true := by decide +kernel
theorem subd6_0_1129 : subd6_0 [2, -2, 0] = true := by decide +kernel
theorem subd6_0_1130 : subd6_0 [2, -2, 1] = true := by decide +kernel
theorem subd6_0_1131 : subd6_0 [2, -2, 2] = true := by decide +kernel
theorem subd6_0_1132 : subd6_0 [2, -2, 3] = true := by decide +kernel
theorem subd6_0_1133 : subd6_0 [2, -2, 4] = true := by decide +kernel
theorem subd6_0_1134 : subd6_0 [2, -2, 5] = true := by decide +kernel
theorem subd6_0_1135 : subd6_0 [2, -2, 6] = true := by decide +kernel
theorem subd6_0_1136 : subd6_0 [2, -2, 7] = true := by decide +kernel
theorem subd6_0_1137 : subd6_0 [2, -2, 8] = true := by decide +kernel
theorem subd6_0_1138 : subd6_0 [2, -1, -9] = true := by decide +kernel
theorem subd6_0_1139 : subd6_0 [2, -1, -8] = true := by decide +kernel
theorem subd6_0_1140 : subd6_0 [2, -1, -7] = true := by decide +kernel
theorem subd6_0_1141 : subd6_0 [2, -1, -6] = true := by decide +kernel
theorem subd6_0_1142 : subd6_0 [2, -1, -5] = true := by decide +kernel
theorem subd6_0_1143 : subd6_0 [2, -1, -4] = true := by decide +kernel
theorem subd6_0_1144 : subd6_0 [2, -1, -3] = true := by decide +kernel
theorem subd6_0_1145 : subd6_0 [2, -1, -2] = true := by decide +kernel
theorem subd6_0_1146 : subd6_0 [2, -1, -1] = true := by decide +kernel
theorem subd6_0_1147 : subd6_0 [2, -1, 0] = true := by decide +kernel
theorem subd6_0_1148 : subd6_0 [2, -1, 1] = true := by decide +kernel
theorem subd6_0_1149 : subd6_0 [2, -1, 2] = true := by decide +kernel
theorem subd6_0_1150 : subd6_0 [2, -1, 3] = true := by decide +kernel
theorem subd6_0_1151 : subd6_0 [2, -1, 4] = true := by decide +kernel
theorem sbd6_0_35 : ∀ q ∈ blkd6_0_35, subd6_0 q = true := by
  unfold blkd6_0_35
  exact List.forall_mem_cons.2 ⟨subd6_0_1120, List.forall_mem_cons.2 ⟨subd6_0_1121, List.forall_mem_cons.2 ⟨subd6_0_1122, List.forall_mem_cons.2 ⟨subd6_0_1123, List.forall_mem_cons.2 ⟨subd6_0_1124, List.forall_mem_cons.2 ⟨subd6_0_1125, List.forall_mem_cons.2 ⟨subd6_0_1126, List.forall_mem_cons.2 ⟨subd6_0_1127, List.forall_mem_cons.2 ⟨subd6_0_1128, List.forall_mem_cons.2 ⟨subd6_0_1129, List.forall_mem_cons.2 ⟨subd6_0_1130, List.forall_mem_cons.2 ⟨subd6_0_1131, List.forall_mem_cons.2 ⟨subd6_0_1132, List.forall_mem_cons.2 ⟨subd6_0_1133, List.forall_mem_cons.2 ⟨subd6_0_1134, List.forall_mem_cons.2 ⟨subd6_0_1135, List.forall_mem_cons.2 ⟨subd6_0_1136, List.forall_mem_cons.2 ⟨subd6_0_1137, List.forall_mem_cons.2 ⟨subd6_0_1138, List.forall_mem_cons.2 ⟨subd6_0_1139, List.forall_mem_cons.2 ⟨subd6_0_1140, List.forall_mem_cons.2 ⟨subd6_0_1141, List.forall_mem_cons.2 ⟨subd6_0_1142, List.forall_mem_cons.2 ⟨subd6_0_1143, List.forall_mem_cons.2 ⟨subd6_0_1144, List.forall_mem_cons.2 ⟨subd6_0_1145, List.forall_mem_cons.2 ⟨subd6_0_1146, List.forall_mem_cons.2 ⟨subd6_0_1147, List.forall_mem_cons.2 ⟨subd6_0_1148, List.forall_mem_cons.2 ⟨subd6_0_1149, List.forall_mem_cons.2 ⟨subd6_0_1150, List.forall_mem_cons.2 ⟨subd6_0_1151, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_1152 : subd6_0 [2, -1, 5] = true := by decide +kernel
theorem subd6_0_1153 : subd6_0 [2, -1, 6] = true := by decide +kernel
theorem subd6_0_1154 : subd6_0 [2, -1, 7] = true := by decide +kernel
theorem subd6_0_1155 : subd6_0 [2, -1, 8] = true := by decide +kernel
theorem subd6_0_1156 : subd6_0 [2, 0, -9] = true := by decide +kernel
theorem subd6_0_1157 : subd6_0 [2, 0, -8] = true := by decide +kernel
theorem subd6_0_1158 : subd6_0 [2, 0, -7] = true := by decide +kernel
theorem subd6_0_1159 : subd6_0 [2, 0, -6] = true := by decide +kernel
theorem subd6_0_1160 : subd6_0 [2, 0, -5] = true := by decide +kernel
theorem subd6_0_1161 : subd6_0 [2, 0, -4] = true := by decide +kernel
theorem subd6_0_1162 : subd6_0 [2, 0, -3] = true := by decide +kernel
theorem subd6_0_1163 : subd6_0 [2, 0, -2] = true := by decide +kernel
theorem subd6_0_1164 : subd6_0 [2, 0, -1] = true := by decide +kernel
theorem subd6_0_1165 : subd6_0 [2, 0, 0] = true := by decide +kernel
theorem subd6_0_1166 : subd6_0 [2, 0, 1] = true := by decide +kernel
theorem subd6_0_1167 : subd6_0 [2, 0, 2] = true := by decide +kernel
theorem subd6_0_1168 : subd6_0 [2, 0, 3] = true := by decide +kernel
theorem subd6_0_1169 : subd6_0 [2, 0, 4] = true := by decide +kernel
theorem subd6_0_1170 : subd6_0 [2, 0, 5] = true := by decide +kernel
theorem subd6_0_1171 : subd6_0 [2, 0, 6] = true := by decide +kernel
theorem subd6_0_1172 : subd6_0 [2, 0, 7] = true := by decide +kernel
theorem subd6_0_1173 : subd6_0 [2, 0, 8] = true := by decide +kernel
theorem subd6_0_1174 : subd6_0 [2, 1, -9] = true := by decide +kernel
theorem subd6_0_1175 : subd6_0 [2, 1, -8] = true := by decide +kernel
theorem subd6_0_1176 : subd6_0 [2, 1, -7] = true := by decide +kernel
theorem subd6_0_1177 : subd6_0 [2, 1, -6] = true := by decide +kernel
theorem subd6_0_1178 : subd6_0 [2, 1, -5] = true := by decide +kernel
theorem subd6_0_1179 : subd6_0 [2, 1, -4] = true := by decide +kernel
theorem subd6_0_1180 : subd6_0 [2, 1, -3] = true := by decide +kernel
theorem subd6_0_1181 : subd6_0 [2, 1, -2] = true := by decide +kernel
theorem subd6_0_1182 : subd6_0 [2, 1, -1] = true := by decide +kernel
theorem subd6_0_1183 : subd6_0 [2, 1, 0] = true := by decide +kernel
theorem sbd6_0_36 : ∀ q ∈ blkd6_0_36, subd6_0 q = true := by
  unfold blkd6_0_36
  exact List.forall_mem_cons.2 ⟨subd6_0_1152, List.forall_mem_cons.2 ⟨subd6_0_1153, List.forall_mem_cons.2 ⟨subd6_0_1154, List.forall_mem_cons.2 ⟨subd6_0_1155, List.forall_mem_cons.2 ⟨subd6_0_1156, List.forall_mem_cons.2 ⟨subd6_0_1157, List.forall_mem_cons.2 ⟨subd6_0_1158, List.forall_mem_cons.2 ⟨subd6_0_1159, List.forall_mem_cons.2 ⟨subd6_0_1160, List.forall_mem_cons.2 ⟨subd6_0_1161, List.forall_mem_cons.2 ⟨subd6_0_1162, List.forall_mem_cons.2 ⟨subd6_0_1163, List.forall_mem_cons.2 ⟨subd6_0_1164, List.forall_mem_cons.2 ⟨subd6_0_1165, List.forall_mem_cons.2 ⟨subd6_0_1166, List.forall_mem_cons.2 ⟨subd6_0_1167, List.forall_mem_cons.2 ⟨subd6_0_1168, List.forall_mem_cons.2 ⟨subd6_0_1169, List.forall_mem_cons.2 ⟨subd6_0_1170, List.forall_mem_cons.2 ⟨subd6_0_1171, List.forall_mem_cons.2 ⟨subd6_0_1172, List.forall_mem_cons.2 ⟨subd6_0_1173, List.forall_mem_cons.2 ⟨subd6_0_1174, List.forall_mem_cons.2 ⟨subd6_0_1175, List.forall_mem_cons.2 ⟨subd6_0_1176, List.forall_mem_cons.2 ⟨subd6_0_1177, List.forall_mem_cons.2 ⟨subd6_0_1178, List.forall_mem_cons.2 ⟨subd6_0_1179, List.forall_mem_cons.2 ⟨subd6_0_1180, List.forall_mem_cons.2 ⟨subd6_0_1181, List.forall_mem_cons.2 ⟨subd6_0_1182, List.forall_mem_cons.2 ⟨subd6_0_1183, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_1184 : subd6_0 [2, 1, 1] = true := by decide +kernel
theorem subd6_0_1185 : subd6_0 [2, 1, 2] = true := by decide +kernel
theorem subd6_0_1186 : subd6_0 [2, 1, 3] = true := by decide +kernel
theorem subd6_0_1187 : subd6_0 [2, 1, 4] = true := by decide +kernel
theorem subd6_0_1188 : subd6_0 [2, 1, 5] = true := by decide +kernel
theorem subd6_0_1189 : subd6_0 [2, 1, 6] = true := by decide +kernel
theorem subd6_0_1190 : subd6_0 [2, 1, 7] = true := by decide +kernel
theorem subd6_0_1191 : subd6_0 [2, 2, -9] = true := by decide +kernel
theorem subd6_0_1192 : subd6_0 [2, 2, -8] = true := by decide +kernel
theorem subd6_0_1193 : subd6_0 [2, 2, -7] = true := by decide +kernel
theorem subd6_0_1194 : subd6_0 [2, 2, -6] = true := by decide +kernel
theorem subd6_0_1195 : subd6_0 [2, 2, -5] = true := by decide +kernel
theorem subd6_0_1196 : subd6_0 [2, 2, -4] = true := by decide +kernel
theorem subd6_0_1197 : subd6_0 [2, 2, -3] = true := by decide +kernel
theorem subd6_0_1198 : subd6_0 [2, 2, -2] = true := by decide +kernel
theorem subd6_0_1199 : subd6_0 [2, 2, -1] = true := by decide +kernel
theorem subd6_0_1200 : subd6_0 [2, 2, 0] = true := by decide +kernel
theorem subd6_0_1201 : subd6_0 [2, 2, 1] = true := by decide +kernel
theorem subd6_0_1202 : subd6_0 [2, 2, 2] = true := by decide +kernel
theorem subd6_0_1203 : subd6_0 [2, 2, 3] = true := by decide +kernel
theorem subd6_0_1204 : subd6_0 [2, 2, 4] = true := by decide +kernel
theorem subd6_0_1205 : subd6_0 [2, 2, 5] = true := by decide +kernel
theorem subd6_0_1206 : subd6_0 [2, 2, 6] = true := by decide +kernel
theorem subd6_0_1207 : subd6_0 [2, 2, 7] = true := by decide +kernel
theorem subd6_0_1208 : subd6_0 [2, 3, -9] = true := by decide +kernel
theorem subd6_0_1209 : subd6_0 [2, 3, -8] = true := by decide +kernel
theorem subd6_0_1210 : subd6_0 [2, 3, -7] = true := by decide +kernel
theorem subd6_0_1211 : subd6_0 [2, 3, -6] = true := by decide +kernel
theorem subd6_0_1212 : subd6_0 [2, 3, -5] = true := by decide +kernel
theorem subd6_0_1213 : subd6_0 [2, 3, -4] = true := by decide +kernel
theorem subd6_0_1214 : subd6_0 [2, 3, -3] = true := by decide +kernel
theorem subd6_0_1215 : subd6_0 [2, 3, -2] = true := by decide +kernel
theorem sbd6_0_37 : ∀ q ∈ blkd6_0_37, subd6_0 q = true := by
  unfold blkd6_0_37
  exact List.forall_mem_cons.2 ⟨subd6_0_1184, List.forall_mem_cons.2 ⟨subd6_0_1185, List.forall_mem_cons.2 ⟨subd6_0_1186, List.forall_mem_cons.2 ⟨subd6_0_1187, List.forall_mem_cons.2 ⟨subd6_0_1188, List.forall_mem_cons.2 ⟨subd6_0_1189, List.forall_mem_cons.2 ⟨subd6_0_1190, List.forall_mem_cons.2 ⟨subd6_0_1191, List.forall_mem_cons.2 ⟨subd6_0_1192, List.forall_mem_cons.2 ⟨subd6_0_1193, List.forall_mem_cons.2 ⟨subd6_0_1194, List.forall_mem_cons.2 ⟨subd6_0_1195, List.forall_mem_cons.2 ⟨subd6_0_1196, List.forall_mem_cons.2 ⟨subd6_0_1197, List.forall_mem_cons.2 ⟨subd6_0_1198, List.forall_mem_cons.2 ⟨subd6_0_1199, List.forall_mem_cons.2 ⟨subd6_0_1200, List.forall_mem_cons.2 ⟨subd6_0_1201, List.forall_mem_cons.2 ⟨subd6_0_1202, List.forall_mem_cons.2 ⟨subd6_0_1203, List.forall_mem_cons.2 ⟨subd6_0_1204, List.forall_mem_cons.2 ⟨subd6_0_1205, List.forall_mem_cons.2 ⟨subd6_0_1206, List.forall_mem_cons.2 ⟨subd6_0_1207, List.forall_mem_cons.2 ⟨subd6_0_1208, List.forall_mem_cons.2 ⟨subd6_0_1209, List.forall_mem_cons.2 ⟨subd6_0_1210, List.forall_mem_cons.2 ⟨subd6_0_1211, List.forall_mem_cons.2 ⟨subd6_0_1212, List.forall_mem_cons.2 ⟨subd6_0_1213, List.forall_mem_cons.2 ⟨subd6_0_1214, List.forall_mem_cons.2 ⟨subd6_0_1215, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_1216 : subd6_0 [2, 3, -1] = true := by decide +kernel
theorem subd6_0_1217 : subd6_0 [2, 3, 0] = true := by decide +kernel
theorem subd6_0_1218 : subd6_0 [2, 3, 1] = true := by decide +kernel
theorem subd6_0_1219 : subd6_0 [2, 3, 2] = true := by decide +kernel
theorem subd6_0_1220 : subd6_0 [2, 3, 3] = true := by decide +kernel
theorem subd6_0_1221 : subd6_0 [2, 3, 4] = true := by decide +kernel
theorem subd6_0_1222 : subd6_0 [2, 3, 5] = true := by decide +kernel
theorem subd6_0_1223 : subd6_0 [2, 3, 6] = true := by decide +kernel
theorem subd6_0_1224 : subd6_0 [2, 4, -8] = true := by decide +kernel
theorem subd6_0_1225 : subd6_0 [2, 4, -7] = true := by decide +kernel
theorem subd6_0_1226 : subd6_0 [2, 4, -6] = true := by decide +kernel
theorem subd6_0_1227 : subd6_0 [2, 4, -5] = true := by decide +kernel
theorem subd6_0_1228 : subd6_0 [2, 4, -4] = true := by decide +kernel
theorem subd6_0_1229 : subd6_0 [2, 4, -3] = true := by decide +kernel
theorem subd6_0_1230 : subd6_0 [2, 4, -2] = true := by decide +kernel
theorem subd6_0_1231 : subd6_0 [2, 4, -1] = true := by decide +kernel
theorem subd6_0_1232 : subd6_0 [2, 4, 0] = true := by decide +kernel
theorem subd6_0_1233 : subd6_0 [2, 4, 1] = true := by decide +kernel
theorem subd6_0_1234 : subd6_0 [2, 4, 2] = true := by decide +kernel
theorem subd6_0_1235 : subd6_0 [2, 4, 3] = true := by decide +kernel
theorem subd6_0_1236 : subd6_0 [2, 4, 4] = true := by decide +kernel
theorem subd6_0_1237 : subd6_0 [2, 4, 5] = true := by decide +kernel
theorem subd6_0_1238 : subd6_0 [2, 4, 6] = true := by decide +kernel
theorem subd6_0_1239 : subd6_0 [2, 5] = true := by decide +kernel
theorem subd6_0_1240 : subd6_0 [2, 6] = true := by decide +kernel
theorem subd6_0_1241 : subd6_0 [2, 7] = true := by decide +kernel
theorem subd6_0_1242 : subd6_0 [3, -8] = true := by decide +kernel
theorem subd6_0_1243 : subd6_0 [3, -7] = true := by decide +kernel
theorem subd6_0_1244 : subd6_0 [3, -6] = true := by decide +kernel
theorem subd6_0_1245 : subd6_0 [3, -5] = true := by decide +kernel
theorem subd6_0_1246 : subd6_0 [3, -4, -7] = true := by decide +kernel
theorem subd6_0_1247 : subd6_0 [3, -4, -6] = true := by decide +kernel
theorem sbd6_0_38 : ∀ q ∈ blkd6_0_38, subd6_0 q = true := by
  unfold blkd6_0_38
  exact List.forall_mem_cons.2 ⟨subd6_0_1216, List.forall_mem_cons.2 ⟨subd6_0_1217, List.forall_mem_cons.2 ⟨subd6_0_1218, List.forall_mem_cons.2 ⟨subd6_0_1219, List.forall_mem_cons.2 ⟨subd6_0_1220, List.forall_mem_cons.2 ⟨subd6_0_1221, List.forall_mem_cons.2 ⟨subd6_0_1222, List.forall_mem_cons.2 ⟨subd6_0_1223, List.forall_mem_cons.2 ⟨subd6_0_1224, List.forall_mem_cons.2 ⟨subd6_0_1225, List.forall_mem_cons.2 ⟨subd6_0_1226, List.forall_mem_cons.2 ⟨subd6_0_1227, List.forall_mem_cons.2 ⟨subd6_0_1228, List.forall_mem_cons.2 ⟨subd6_0_1229, List.forall_mem_cons.2 ⟨subd6_0_1230, List.forall_mem_cons.2 ⟨subd6_0_1231, List.forall_mem_cons.2 ⟨subd6_0_1232, List.forall_mem_cons.2 ⟨subd6_0_1233, List.forall_mem_cons.2 ⟨subd6_0_1234, List.forall_mem_cons.2 ⟨subd6_0_1235, List.forall_mem_cons.2 ⟨subd6_0_1236, List.forall_mem_cons.2 ⟨subd6_0_1237, List.forall_mem_cons.2 ⟨subd6_0_1238, List.forall_mem_cons.2 ⟨subd6_0_1239, List.forall_mem_cons.2 ⟨subd6_0_1240, List.forall_mem_cons.2 ⟨subd6_0_1241, List.forall_mem_cons.2 ⟨subd6_0_1242, List.forall_mem_cons.2 ⟨subd6_0_1243, List.forall_mem_cons.2 ⟨subd6_0_1244, List.forall_mem_cons.2 ⟨subd6_0_1245, List.forall_mem_cons.2 ⟨subd6_0_1246, List.forall_mem_cons.2 ⟨subd6_0_1247, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_1248 : subd6_0 [3, -4, -5] = true := by decide +kernel
theorem subd6_0_1249 : subd6_0 [3, -4, -4] = true := by decide +kernel
theorem subd6_0_1250 : subd6_0 [3, -4, -3] = true := by decide +kernel
theorem subd6_0_1251 : subd6_0 [3, -4, -2] = true := by decide +kernel
theorem subd6_0_1252 : subd6_0 [3, -4, -1] = true := by decide +kernel
theorem subd6_0_1253 : subd6_0 [3, -4, 0] = true := by decide +kernel
theorem subd6_0_1254 : subd6_0 [3, -4, 1] = true := by decide +kernel
theorem subd6_0_1255 : subd6_0 [3, -4, 2] = true := by decide +kernel
theorem subd6_0_1256 : subd6_0 [3, -4, 3] = true := by decide +kernel
theorem subd6_0_1257 : subd6_0 [3, -4, 4] = true := by decide +kernel
theorem subd6_0_1258 : subd6_0 [3, -4, 5] = true := by decide +kernel
theorem subd6_0_1259 : subd6_0 [3, -4, 6] = true := by decide +kernel
theorem subd6_0_1260 : subd6_0 [3, -4, 7] = true := by decide +kernel
theorem subd6_0_1261 : subd6_0 [3, -3, -8] = true := by decide +kernel
theorem subd6_0_1262 : subd6_0 [3, -3, -7] = true := by decide +kernel
theorem subd6_0_1263 : subd6_0 [3, -3, -6] = true := by decide +kernel
theorem subd6_0_1264 : subd6_0 [3, -3, -5] = true := by decide +kernel
theorem subd6_0_1265 : subd6_0 [3, -3, -4] = true := by decide +kernel
theorem subd6_0_1266 : subd6_0 [3, -3, -3] = true := by decide +kernel
theorem subd6_0_1267 : subd6_0 [3, -3, -2] = true := by decide +kernel
theorem subd6_0_1268 : subd6_0 [3, -3, -1] = true := by decide +kernel
theorem subd6_0_1269 : subd6_0 [3, -3, 0] = true := by decide +kernel
theorem subd6_0_1270 : subd6_0 [3, -3, 1] = true := by decide +kernel
theorem subd6_0_1271 : subd6_0 [3, -3, 2] = true := by decide +kernel
theorem subd6_0_1272 : subd6_0 [3, -3, 3] = true := by decide +kernel
theorem subd6_0_1273 : subd6_0 [3, -3, 4] = true := by decide +kernel
theorem subd6_0_1274 : subd6_0 [3, -3, 5] = true := by decide +kernel
theorem subd6_0_1275 : subd6_0 [3, -3, 6] = true := by decide +kernel
theorem subd6_0_1276 : subd6_0 [3, -3, 7] = true := by decide +kernel
theorem subd6_0_1277 : subd6_0 [3, -2, -8] = true := by decide +kernel
theorem subd6_0_1278 : subd6_0 [3, -2, -7] = true := by decide +kernel
theorem subd6_0_1279 : subd6_0 [3, -2, -6] = true := by decide +kernel
theorem sbd6_0_39 : ∀ q ∈ blkd6_0_39, subd6_0 q = true := by
  unfold blkd6_0_39
  exact List.forall_mem_cons.2 ⟨subd6_0_1248, List.forall_mem_cons.2 ⟨subd6_0_1249, List.forall_mem_cons.2 ⟨subd6_0_1250, List.forall_mem_cons.2 ⟨subd6_0_1251, List.forall_mem_cons.2 ⟨subd6_0_1252, List.forall_mem_cons.2 ⟨subd6_0_1253, List.forall_mem_cons.2 ⟨subd6_0_1254, List.forall_mem_cons.2 ⟨subd6_0_1255, List.forall_mem_cons.2 ⟨subd6_0_1256, List.forall_mem_cons.2 ⟨subd6_0_1257, List.forall_mem_cons.2 ⟨subd6_0_1258, List.forall_mem_cons.2 ⟨subd6_0_1259, List.forall_mem_cons.2 ⟨subd6_0_1260, List.forall_mem_cons.2 ⟨subd6_0_1261, List.forall_mem_cons.2 ⟨subd6_0_1262, List.forall_mem_cons.2 ⟨subd6_0_1263, List.forall_mem_cons.2 ⟨subd6_0_1264, List.forall_mem_cons.2 ⟨subd6_0_1265, List.forall_mem_cons.2 ⟨subd6_0_1266, List.forall_mem_cons.2 ⟨subd6_0_1267, List.forall_mem_cons.2 ⟨subd6_0_1268, List.forall_mem_cons.2 ⟨subd6_0_1269, List.forall_mem_cons.2 ⟨subd6_0_1270, List.forall_mem_cons.2 ⟨subd6_0_1271, List.forall_mem_cons.2 ⟨subd6_0_1272, List.forall_mem_cons.2 ⟨subd6_0_1273, List.forall_mem_cons.2 ⟨subd6_0_1274, List.forall_mem_cons.2 ⟨subd6_0_1275, List.forall_mem_cons.2 ⟨subd6_0_1276, List.forall_mem_cons.2 ⟨subd6_0_1277, List.forall_mem_cons.2 ⟨subd6_0_1278, List.forall_mem_cons.2 ⟨subd6_0_1279, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_1280 : subd6_0 [3, -2, -5] = true := by decide +kernel
theorem subd6_0_1281 : subd6_0 [3, -2, -4] = true := by decide +kernel
theorem subd6_0_1282 : subd6_0 [3, -2, -3] = true := by decide +kernel
theorem subd6_0_1283 : subd6_0 [3, -2, -2] = true := by decide +kernel
theorem subd6_0_1284 : subd6_0 [3, -2, -1] = true := by decide +kernel
theorem subd6_0_1285 : subd6_0 [3, -2, 0] = true := by decide +kernel
theorem subd6_0_1286 : subd6_0 [3, -2, 1] = true := by decide +kernel
theorem subd6_0_1287 : subd6_0 [3, -2, 2] = true := by decide +kernel
theorem subd6_0_1288 : subd6_0 [3, -2, 3] = true := by decide +kernel
theorem subd6_0_1289 : subd6_0 [3, -2, 4] = true := by decide +kernel
theorem subd6_0_1290 : subd6_0 [3, -2, 5] = true := by decide +kernel
theorem subd6_0_1291 : subd6_0 [3, -2, 6] = true := by decide +kernel
theorem subd6_0_1292 : subd6_0 [3, -2, 7] = true := by decide +kernel
theorem subd6_0_1293 : subd6_0 [3, -1, -9] = true := by decide +kernel
theorem subd6_0_1294 : subd6_0 [3, -1, -8] = true := by decide +kernel
theorem subd6_0_1295 : subd6_0 [3, -1, -7] = true := by decide +kernel
theorem subd6_0_1296 : subd6_0 [3, -1, -6] = true := by decide +kernel
theorem subd6_0_1297 : subd6_0 [3, -1, -5] = true := by decide +kernel
theorem subd6_0_1298 : subd6_0 [3, -1, -4] = true := by decide +kernel
theorem subd6_0_1299 : subd6_0 [3, -1, -3] = true := by decide +kernel
theorem subd6_0_1300 : subd6_0 [3, -1, -2] = true := by decide +kernel
theorem subd6_0_1301 : subd6_0 [3, -1, -1] = true := by decide +kernel
theorem subd6_0_1302 : subd6_0 [3, -1, 0] = true := by decide +kernel
theorem subd6_0_1303 : subd6_0 [3, -1, 1] = true := by decide +kernel
theorem subd6_0_1304 : subd6_0 [3, -1, 2] = true := by decide +kernel
theorem subd6_0_1305 : subd6_0 [3, -1, 3] = true := by decide +kernel
theorem subd6_0_1306 : subd6_0 [3, -1, 4] = true := by decide +kernel
theorem subd6_0_1307 : subd6_0 [3, -1, 5] = true := by decide +kernel
theorem subd6_0_1308 : subd6_0 [3, -1, 6] = true := by decide +kernel
theorem subd6_0_1309 : subd6_0 [3, -1, 7] = true := by decide +kernel
theorem subd6_0_1310 : subd6_0 [3, 0, -9] = true := by decide +kernel
theorem subd6_0_1311 : subd6_0 [3, 0, -8] = true := by decide +kernel
theorem sbd6_0_40 : ∀ q ∈ blkd6_0_40, subd6_0 q = true := by
  unfold blkd6_0_40
  exact List.forall_mem_cons.2 ⟨subd6_0_1280, List.forall_mem_cons.2 ⟨subd6_0_1281, List.forall_mem_cons.2 ⟨subd6_0_1282, List.forall_mem_cons.2 ⟨subd6_0_1283, List.forall_mem_cons.2 ⟨subd6_0_1284, List.forall_mem_cons.2 ⟨subd6_0_1285, List.forall_mem_cons.2 ⟨subd6_0_1286, List.forall_mem_cons.2 ⟨subd6_0_1287, List.forall_mem_cons.2 ⟨subd6_0_1288, List.forall_mem_cons.2 ⟨subd6_0_1289, List.forall_mem_cons.2 ⟨subd6_0_1290, List.forall_mem_cons.2 ⟨subd6_0_1291, List.forall_mem_cons.2 ⟨subd6_0_1292, List.forall_mem_cons.2 ⟨subd6_0_1293, List.forall_mem_cons.2 ⟨subd6_0_1294, List.forall_mem_cons.2 ⟨subd6_0_1295, List.forall_mem_cons.2 ⟨subd6_0_1296, List.forall_mem_cons.2 ⟨subd6_0_1297, List.forall_mem_cons.2 ⟨subd6_0_1298, List.forall_mem_cons.2 ⟨subd6_0_1299, List.forall_mem_cons.2 ⟨subd6_0_1300, List.forall_mem_cons.2 ⟨subd6_0_1301, List.forall_mem_cons.2 ⟨subd6_0_1302, List.forall_mem_cons.2 ⟨subd6_0_1303, List.forall_mem_cons.2 ⟨subd6_0_1304, List.forall_mem_cons.2 ⟨subd6_0_1305, List.forall_mem_cons.2 ⟨subd6_0_1306, List.forall_mem_cons.2 ⟨subd6_0_1307, List.forall_mem_cons.2 ⟨subd6_0_1308, List.forall_mem_cons.2 ⟨subd6_0_1309, List.forall_mem_cons.2 ⟨subd6_0_1310, List.forall_mem_cons.2 ⟨subd6_0_1311, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_1312 : subd6_0 [3, 0, -7] = true := by decide +kernel
theorem subd6_0_1313 : subd6_0 [3, 0, -6] = true := by decide +kernel
theorem subd6_0_1314 : subd6_0 [3, 0, -5] = true := by decide +kernel
theorem subd6_0_1315 : subd6_0 [3, 0, -4] = true := by decide +kernel
theorem subd6_0_1316 : subd6_0 [3, 0, -3] = true := by decide +kernel
theorem subd6_0_1317 : subd6_0 [3, 0, -2] = true := by decide +kernel
theorem subd6_0_1318 : subd6_0 [3, 0, -1] = true := by decide +kernel
theorem subd6_0_1319 : subd6_0 [3, 0, 0] = true := by decide +kernel
theorem subd6_0_1320 : subd6_0 [3, 0, 1] = true := by decide +kernel
theorem subd6_0_1321 : subd6_0 [3, 0, 2] = true := by decide +kernel
theorem subd6_0_1322 : subd6_0 [3, 0, 3] = true := by decide +kernel
theorem subd6_0_1323 : subd6_0 [3, 0, 4] = true := by decide +kernel
theorem subd6_0_1324 : subd6_0 [3, 0, 5] = true := by decide +kernel
theorem subd6_0_1325 : subd6_0 [3, 0, 6] = true := by decide +kernel
theorem subd6_0_1326 : subd6_0 [3, 0, 7] = true := by decide +kernel
theorem subd6_0_1327 : subd6_0 [3, 1, -9] = true := by decide +kernel
theorem subd6_0_1328 : subd6_0 [3, 1, -8] = true := by decide +kernel
theorem subd6_0_1329 : subd6_0 [3, 1, -7] = true := by decide +kernel
theorem subd6_0_1330 : subd6_0 [3, 1, -6] = true := by decide +kernel
theorem subd6_0_1331 : subd6_0 [3, 1, -5] = true := by decide +kernel
theorem subd6_0_1332 : subd6_0 [3, 1, -4] = true := by decide +kernel
theorem subd6_0_1333 : subd6_0 [3, 1, -3] = true := by decide +kernel
theorem subd6_0_1334 : subd6_0 [3, 1, -2] = true := by decide +kernel
theorem subd6_0_1335 : subd6_0 [3, 1, -1] = true := by decide +kernel
theorem subd6_0_1336 : subd6_0 [3, 1, 0] = true := by decide +kernel
theorem subd6_0_1337 : subd6_0 [3, 1, 1] = true := by decide +kernel
theorem subd6_0_1338 : subd6_0 [3, 1, 2] = true := by decide +kernel
theorem subd6_0_1339 : subd6_0 [3, 1, 3] = true := by decide +kernel
theorem subd6_0_1340 : subd6_0 [3, 1, 4] = true := by decide +kernel
theorem subd6_0_1341 : subd6_0 [3, 1, 5] = true := by decide +kernel
theorem subd6_0_1342 : subd6_0 [3, 1, 6] = true := by decide +kernel
theorem subd6_0_1343 : subd6_0 [3, 1, 7] = true := by decide +kernel
theorem sbd6_0_41 : ∀ q ∈ blkd6_0_41, subd6_0 q = true := by
  unfold blkd6_0_41
  exact List.forall_mem_cons.2 ⟨subd6_0_1312, List.forall_mem_cons.2 ⟨subd6_0_1313, List.forall_mem_cons.2 ⟨subd6_0_1314, List.forall_mem_cons.2 ⟨subd6_0_1315, List.forall_mem_cons.2 ⟨subd6_0_1316, List.forall_mem_cons.2 ⟨subd6_0_1317, List.forall_mem_cons.2 ⟨subd6_0_1318, List.forall_mem_cons.2 ⟨subd6_0_1319, List.forall_mem_cons.2 ⟨subd6_0_1320, List.forall_mem_cons.2 ⟨subd6_0_1321, List.forall_mem_cons.2 ⟨subd6_0_1322, List.forall_mem_cons.2 ⟨subd6_0_1323, List.forall_mem_cons.2 ⟨subd6_0_1324, List.forall_mem_cons.2 ⟨subd6_0_1325, List.forall_mem_cons.2 ⟨subd6_0_1326, List.forall_mem_cons.2 ⟨subd6_0_1327, List.forall_mem_cons.2 ⟨subd6_0_1328, List.forall_mem_cons.2 ⟨subd6_0_1329, List.forall_mem_cons.2 ⟨subd6_0_1330, List.forall_mem_cons.2 ⟨subd6_0_1331, List.forall_mem_cons.2 ⟨subd6_0_1332, List.forall_mem_cons.2 ⟨subd6_0_1333, List.forall_mem_cons.2 ⟨subd6_0_1334, List.forall_mem_cons.2 ⟨subd6_0_1335, List.forall_mem_cons.2 ⟨subd6_0_1336, List.forall_mem_cons.2 ⟨subd6_0_1337, List.forall_mem_cons.2 ⟨subd6_0_1338, List.forall_mem_cons.2 ⟨subd6_0_1339, List.forall_mem_cons.2 ⟨subd6_0_1340, List.forall_mem_cons.2 ⟨subd6_0_1341, List.forall_mem_cons.2 ⟨subd6_0_1342, List.forall_mem_cons.2 ⟨subd6_0_1343, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_1344 : subd6_0 [3, 2, -9] = true := by decide +kernel
theorem subd6_0_1345 : subd6_0 [3, 2, -8] = true := by decide +kernel
theorem subd6_0_1346 : subd6_0 [3, 2, -7] = true := by decide +kernel
theorem subd6_0_1347 : subd6_0 [3, 2, -6] = true := by decide +kernel
theorem subd6_0_1348 : subd6_0 [3, 2, -5] = true := by decide +kernel
theorem subd6_0_1349 : subd6_0 [3, 2, -4] = true := by decide +kernel
theorem subd6_0_1350 : subd6_0 [3, 2, -3] = true := by decide +kernel
theorem subd6_0_1351 : subd6_0 [3, 2, -2] = true := by decide +kernel
theorem subd6_0_1352 : subd6_0 [3, 2, -1] = true := by decide +kernel
theorem subd6_0_1353 : subd6_0 [3, 2, 0] = true := by decide +kernel
theorem subd6_0_1354 : subd6_0 [3, 2, 1] = true := by decide +kernel
theorem subd6_0_1355 : subd6_0 [3, 2, 2] = true := by decide +kernel
theorem subd6_0_1356 : subd6_0 [3, 2, 3] = true := by decide +kernel
theorem subd6_0_1357 : subd6_0 [3, 2, 4] = true := by decide +kernel
theorem subd6_0_1358 : subd6_0 [3, 2, 5] = true := by decide +kernel
theorem subd6_0_1359 : subd6_0 [3, 2, 6] = true := by decide +kernel
theorem subd6_0_1360 : subd6_0 [3, 3, -8] = true := by decide +kernel
theorem subd6_0_1361 : subd6_0 [3, 3, -7] = true := by decide +kernel
theorem subd6_0_1362 : subd6_0 [3, 3, -6] = true := by decide +kernel
theorem subd6_0_1363 : subd6_0 [3, 3, -5] = true := by decide +kernel
theorem subd6_0_1364 : subd6_0 [3, 3, -4] = true := by decide +kernel
theorem subd6_0_1365 : subd6_0 [3, 3, -3] = true := by decide +kernel
theorem subd6_0_1366 : subd6_0 [3, 3, -2] = true := by decide +kernel
theorem subd6_0_1367 : subd6_0 [3, 3, -1] = true := by decide +kernel
theorem subd6_0_1368 : subd6_0 [3, 3, 0] = true := by decide +kernel
theorem subd6_0_1369 : subd6_0 [3, 3, 1] = true := by decide +kernel
theorem subd6_0_1370 : subd6_0 [3, 3, 2] = true := by decide +kernel
theorem subd6_0_1371 : subd6_0 [3, 3, 3] = true := by decide +kernel
theorem subd6_0_1372 : subd6_0 [3, 3, 4] = true := by decide +kernel
theorem subd6_0_1373 : subd6_0 [3, 3, 5] = true := by decide +kernel
theorem subd6_0_1374 : subd6_0 [3, 3, 6] = true := by decide +kernel
theorem subd6_0_1375 : subd6_0 [3, 4, -8] = true := by decide +kernel
theorem sbd6_0_42 : ∀ q ∈ blkd6_0_42, subd6_0 q = true := by
  unfold blkd6_0_42
  exact List.forall_mem_cons.2 ⟨subd6_0_1344, List.forall_mem_cons.2 ⟨subd6_0_1345, List.forall_mem_cons.2 ⟨subd6_0_1346, List.forall_mem_cons.2 ⟨subd6_0_1347, List.forall_mem_cons.2 ⟨subd6_0_1348, List.forall_mem_cons.2 ⟨subd6_0_1349, List.forall_mem_cons.2 ⟨subd6_0_1350, List.forall_mem_cons.2 ⟨subd6_0_1351, List.forall_mem_cons.2 ⟨subd6_0_1352, List.forall_mem_cons.2 ⟨subd6_0_1353, List.forall_mem_cons.2 ⟨subd6_0_1354, List.forall_mem_cons.2 ⟨subd6_0_1355, List.forall_mem_cons.2 ⟨subd6_0_1356, List.forall_mem_cons.2 ⟨subd6_0_1357, List.forall_mem_cons.2 ⟨subd6_0_1358, List.forall_mem_cons.2 ⟨subd6_0_1359, List.forall_mem_cons.2 ⟨subd6_0_1360, List.forall_mem_cons.2 ⟨subd6_0_1361, List.forall_mem_cons.2 ⟨subd6_0_1362, List.forall_mem_cons.2 ⟨subd6_0_1363, List.forall_mem_cons.2 ⟨subd6_0_1364, List.forall_mem_cons.2 ⟨subd6_0_1365, List.forall_mem_cons.2 ⟨subd6_0_1366, List.forall_mem_cons.2 ⟨subd6_0_1367, List.forall_mem_cons.2 ⟨subd6_0_1368, List.forall_mem_cons.2 ⟨subd6_0_1369, List.forall_mem_cons.2 ⟨subd6_0_1370, List.forall_mem_cons.2 ⟨subd6_0_1371, List.forall_mem_cons.2 ⟨subd6_0_1372, List.forall_mem_cons.2 ⟨subd6_0_1373, List.forall_mem_cons.2 ⟨subd6_0_1374, List.forall_mem_cons.2 ⟨subd6_0_1375, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_1376 : subd6_0 [3, 4, -7] = true := by decide +kernel
theorem subd6_0_1377 : subd6_0 [3, 4, -6] = true := by decide +kernel
theorem subd6_0_1378 : subd6_0 [3, 4, -5] = true := by decide +kernel
theorem subd6_0_1379 : subd6_0 [3, 4, -4] = true := by decide +kernel
theorem subd6_0_1380 : subd6_0 [3, 4, -3] = true := by decide +kernel
theorem subd6_0_1381 : subd6_0 [3, 4, -2] = true := by decide +kernel
theorem subd6_0_1382 : subd6_0 [3, 4, -1] = true := by decide +kernel
theorem subd6_0_1383 : subd6_0 [3, 4, 0] = true := by decide +kernel
theorem subd6_0_1384 : subd6_0 [3, 4, 1] = true := by decide +kernel
theorem subd6_0_1385 : subd6_0 [3, 4, 2] = true := by decide +kernel
theorem subd6_0_1386 : subd6_0 [3, 4, 3] = true := by decide +kernel
theorem subd6_0_1387 : subd6_0 [3, 4, 4] = true := by decide +kernel
theorem subd6_0_1388 : subd6_0 [3, 4, 5] = true := by decide +kernel
theorem subd6_0_1389 : subd6_0 [3, 5] = true := by decide +kernel
theorem subd6_0_1390 : subd6_0 [3, 6] = true := by decide +kernel
theorem subd6_0_1391 : subd6_0 [3, 7] = true := by decide +kernel
theorem subd6_0_1392 : subd6_0 [4, -8] = true := by decide +kernel
theorem subd6_0_1393 : subd6_0 [4, -7] = true := by decide +kernel
theorem subd6_0_1394 : subd6_0 [4, -6] = true := by decide +kernel
theorem subd6_0_1395 : subd6_0 [4, -5] = true := by decide +kernel
theorem subd6_0_1396 : subd6_0 [4, -4, -7] = true := by decide +kernel
theorem subd6_0_1397 : subd6_0 [4, -4, -6] = true := by decide +kernel
theorem subd6_0_1398 : subd6_0 [4, -4, -5] = true := by decide +kernel
theorem subd6_0_1399 : subd6_0 [4, -4, -4] = true := by decide +kernel
theorem subd6_0_1400 : subd6_0 [4, -4, -3] = true := by decide +kernel
theorem subd6_0_1401 : subd6_0 [4, -4, -2] = true := by decide +kernel
theorem subd6_0_1402 : subd6_0 [4, -4, -1] = true := by decide +kernel
theorem subd6_0_1403 : subd6_0 [4, -4, 0] = true := by decide +kernel
theorem subd6_0_1404 : subd6_0 [4, -4, 1] = true := by decide +kernel
theorem subd6_0_1405 : subd6_0 [4, -4, 2] = true := by decide +kernel
theorem subd6_0_1406 : subd6_0 [4, -4, 3] = true := by decide +kernel
theorem subd6_0_1407 : subd6_0 [4, -4, 4] = true := by decide +kernel
theorem sbd6_0_43 : ∀ q ∈ blkd6_0_43, subd6_0 q = true := by
  unfold blkd6_0_43
  exact List.forall_mem_cons.2 ⟨subd6_0_1376, List.forall_mem_cons.2 ⟨subd6_0_1377, List.forall_mem_cons.2 ⟨subd6_0_1378, List.forall_mem_cons.2 ⟨subd6_0_1379, List.forall_mem_cons.2 ⟨subd6_0_1380, List.forall_mem_cons.2 ⟨subd6_0_1381, List.forall_mem_cons.2 ⟨subd6_0_1382, List.forall_mem_cons.2 ⟨subd6_0_1383, List.forall_mem_cons.2 ⟨subd6_0_1384, List.forall_mem_cons.2 ⟨subd6_0_1385, List.forall_mem_cons.2 ⟨subd6_0_1386, List.forall_mem_cons.2 ⟨subd6_0_1387, List.forall_mem_cons.2 ⟨subd6_0_1388, List.forall_mem_cons.2 ⟨subd6_0_1389, List.forall_mem_cons.2 ⟨subd6_0_1390, List.forall_mem_cons.2 ⟨subd6_0_1391, List.forall_mem_cons.2 ⟨subd6_0_1392, List.forall_mem_cons.2 ⟨subd6_0_1393, List.forall_mem_cons.2 ⟨subd6_0_1394, List.forall_mem_cons.2 ⟨subd6_0_1395, List.forall_mem_cons.2 ⟨subd6_0_1396, List.forall_mem_cons.2 ⟨subd6_0_1397, List.forall_mem_cons.2 ⟨subd6_0_1398, List.forall_mem_cons.2 ⟨subd6_0_1399, List.forall_mem_cons.2 ⟨subd6_0_1400, List.forall_mem_cons.2 ⟨subd6_0_1401, List.forall_mem_cons.2 ⟨subd6_0_1402, List.forall_mem_cons.2 ⟨subd6_0_1403, List.forall_mem_cons.2 ⟨subd6_0_1404, List.forall_mem_cons.2 ⟨subd6_0_1405, List.forall_mem_cons.2 ⟨subd6_0_1406, List.forall_mem_cons.2 ⟨subd6_0_1407, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_1408 : subd6_0 [4, -4, 5] = true := by decide +kernel
theorem subd6_0_1409 : subd6_0 [4, -4, 6] = true := by decide +kernel
theorem subd6_0_1410 : subd6_0 [4, -3, -7] = true := by decide +kernel
theorem subd6_0_1411 : subd6_0 [4, -3, -6] = true := by decide +kernel
theorem subd6_0_1412 : subd6_0 [4, -3, -5] = true := by decide +kernel
theorem subd6_0_1413 : subd6_0 [4, -3, -4] = true := by decide +kernel
theorem subd6_0_1414 : subd6_0 [4, -3, -3] = true := by decide +kernel
theorem subd6_0_1415 : subd6_0 [4, -3, -2] = true := by decide +kernel
theorem subd6_0_1416 : subd6_0 [4, -3, -1] = true := by decide +kernel
theorem subd6_0_1417 : subd6_0 [4, -3, 0] = true := by decide +kernel
theorem subd6_0_1418 : subd6_0 [4, -3, 1] = true := by decide +kernel
theorem subd6_0_1419 : subd6_0 [4, -3, 2] = true := by decide +kernel
theorem subd6_0_1420 : subd6_0 [4, -3, 3] = true := by decide +kernel
theorem subd6_0_1421 : subd6_0 [4, -3, 4] = true := by decide +kernel
theorem subd6_0_1422 : subd6_0 [4, -3, 5] = true := by decide +kernel
theorem subd6_0_1423 : subd6_0 [4, -3, 6] = true := by decide +kernel
theorem subd6_0_1424 : subd6_0 [4, -2, -8] = true := by decide +kernel
theorem subd6_0_1425 : subd6_0 [4, -2, -7] = true := by decide +kernel
theorem subd6_0_1426 : subd6_0 [4, -2, -6] = true := by decide +kernel
theorem subd6_0_1427 : subd6_0 [4, -2, -5] = true := by decide +kernel
theorem subd6_0_1428 : subd6_0 [4, -2, -4] = true := by decide +kernel
theorem subd6_0_1429 : subd6_0 [4, -2, -3] = true := by decide +kernel
theorem subd6_0_1430 : subd6_0 [4, -2, -2] = true := by decide +kernel
theorem subd6_0_1431 : subd6_0 [4, -2, -1] = true := by decide +kernel
theorem subd6_0_1432 : subd6_0 [4, -2, 0] = true := by decide +kernel
theorem subd6_0_1433 : subd6_0 [4, -2, 1] = true := by decide +kernel
theorem subd6_0_1434 : subd6_0 [4, -2, 2] = true := by decide +kernel
theorem subd6_0_1435 : subd6_0 [4, -2, 3] = true := by decide +kernel
theorem subd6_0_1436 : subd6_0 [4, -2, 4] = true := by decide +kernel
theorem subd6_0_1437 : subd6_0 [4, -2, 5] = true := by decide +kernel
theorem subd6_0_1438 : subd6_0 [4, -2, 6] = true := by decide +kernel
theorem subd6_0_1439 : subd6_0 [4, -1, -8] = true := by decide +kernel
theorem sbd6_0_44 : ∀ q ∈ blkd6_0_44, subd6_0 q = true := by
  unfold blkd6_0_44
  exact List.forall_mem_cons.2 ⟨subd6_0_1408, List.forall_mem_cons.2 ⟨subd6_0_1409, List.forall_mem_cons.2 ⟨subd6_0_1410, List.forall_mem_cons.2 ⟨subd6_0_1411, List.forall_mem_cons.2 ⟨subd6_0_1412, List.forall_mem_cons.2 ⟨subd6_0_1413, List.forall_mem_cons.2 ⟨subd6_0_1414, List.forall_mem_cons.2 ⟨subd6_0_1415, List.forall_mem_cons.2 ⟨subd6_0_1416, List.forall_mem_cons.2 ⟨subd6_0_1417, List.forall_mem_cons.2 ⟨subd6_0_1418, List.forall_mem_cons.2 ⟨subd6_0_1419, List.forall_mem_cons.2 ⟨subd6_0_1420, List.forall_mem_cons.2 ⟨subd6_0_1421, List.forall_mem_cons.2 ⟨subd6_0_1422, List.forall_mem_cons.2 ⟨subd6_0_1423, List.forall_mem_cons.2 ⟨subd6_0_1424, List.forall_mem_cons.2 ⟨subd6_0_1425, List.forall_mem_cons.2 ⟨subd6_0_1426, List.forall_mem_cons.2 ⟨subd6_0_1427, List.forall_mem_cons.2 ⟨subd6_0_1428, List.forall_mem_cons.2 ⟨subd6_0_1429, List.forall_mem_cons.2 ⟨subd6_0_1430, List.forall_mem_cons.2 ⟨subd6_0_1431, List.forall_mem_cons.2 ⟨subd6_0_1432, List.forall_mem_cons.2 ⟨subd6_0_1433, List.forall_mem_cons.2 ⟨subd6_0_1434, List.forall_mem_cons.2 ⟨subd6_0_1435, List.forall_mem_cons.2 ⟨subd6_0_1436, List.forall_mem_cons.2 ⟨subd6_0_1437, List.forall_mem_cons.2 ⟨subd6_0_1438, List.forall_mem_cons.2 ⟨subd6_0_1439, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_1440 : subd6_0 [4, -1, -7] = true := by decide +kernel
theorem subd6_0_1441 : subd6_0 [4, -1, -6] = true := by decide +kernel
theorem subd6_0_1442 : subd6_0 [4, -1, -5] = true := by decide +kernel
theorem subd6_0_1443 : subd6_0 [4, -1, -4] = true := by decide +kernel
theorem subd6_0_1444 : subd6_0 [4, -1, -3] = true := by decide +kernel
theorem subd6_0_1445 : subd6_0 [4, -1, -2] = true := by decide +kernel
theorem subd6_0_1446 : subd6_0 [4, -1, -1] = true := by decide +kernel
theorem subd6_0_1447 : subd6_0 [4, -1, 0] = true := by decide +kernel
theorem subd6_0_1448 : subd6_0 [4, -1, 1] = true := by decide +kernel
theorem subd6_0_1449 : subd6_0 [4, -1, 2] = true := by decide +kernel
theorem subd6_0_1450 : subd6_0 [4, -1, 3] = true := by decide +kernel
theorem subd6_0_1451 : subd6_0 [4, -1, 4] = true := by decide +kernel
theorem subd6_0_1452 : subd6_0 [4, -1, 5] = true := by decide +kernel
theorem subd6_0_1453 : subd6_0 [4, -1, 6] = true := by decide +kernel
theorem subd6_0_1454 : subd6_0 [4, -1, 7] = true := by decide +kernel
theorem subd6_0_1455 : subd6_0 [4, 0, -8] = true := by decide +kernel
theorem subd6_0_1456 : subd6_0 [4, 0, -7] = true := by decide +kernel
theorem subd6_0_1457 : subd6_0 [4, 0, -6] = true := by decide +kernel
theorem subd6_0_1458 : subd6_0 [4, 0, -5] = true := by decide +kernel
theorem subd6_0_1459 : subd6_0 [4, 0, -4] = true := by decide +kernel
theorem subd6_0_1460 : subd6_0 [4, 0, -3] = true := by decide +kernel
theorem subd6_0_1461 : subd6_0 [4, 0, -2] = true := by decide +kernel
theorem subd6_0_1462 : subd6_0 [4, 0, -1] = true := by decide +kernel
theorem subd6_0_1463 : subd6_0 [4, 0, 0] = true := by decide +kernel
theorem subd6_0_1464 : subd6_0 [4, 0, 1] = true := by decide +kernel
theorem subd6_0_1465 : subd6_0 [4, 0, 2] = true := by decide +kernel
theorem subd6_0_1466 : subd6_0 [4, 0, 3] = true := by decide +kernel
theorem subd6_0_1467 : subd6_0 [4, 0, 4] = true := by decide +kernel
theorem subd6_0_1468 : subd6_0 [4, 0, 5] = true := by decide +kernel
theorem subd6_0_1469 : subd6_0 [4, 0, 6] = true := by decide +kernel
theorem subd6_0_1470 : subd6_0 [4, 1, -8] = true := by decide +kernel
theorem subd6_0_1471 : subd6_0 [4, 1, -7] = true := by decide +kernel
theorem sbd6_0_45 : ∀ q ∈ blkd6_0_45, subd6_0 q = true := by
  unfold blkd6_0_45
  exact List.forall_mem_cons.2 ⟨subd6_0_1440, List.forall_mem_cons.2 ⟨subd6_0_1441, List.forall_mem_cons.2 ⟨subd6_0_1442, List.forall_mem_cons.2 ⟨subd6_0_1443, List.forall_mem_cons.2 ⟨subd6_0_1444, List.forall_mem_cons.2 ⟨subd6_0_1445, List.forall_mem_cons.2 ⟨subd6_0_1446, List.forall_mem_cons.2 ⟨subd6_0_1447, List.forall_mem_cons.2 ⟨subd6_0_1448, List.forall_mem_cons.2 ⟨subd6_0_1449, List.forall_mem_cons.2 ⟨subd6_0_1450, List.forall_mem_cons.2 ⟨subd6_0_1451, List.forall_mem_cons.2 ⟨subd6_0_1452, List.forall_mem_cons.2 ⟨subd6_0_1453, List.forall_mem_cons.2 ⟨subd6_0_1454, List.forall_mem_cons.2 ⟨subd6_0_1455, List.forall_mem_cons.2 ⟨subd6_0_1456, List.forall_mem_cons.2 ⟨subd6_0_1457, List.forall_mem_cons.2 ⟨subd6_0_1458, List.forall_mem_cons.2 ⟨subd6_0_1459, List.forall_mem_cons.2 ⟨subd6_0_1460, List.forall_mem_cons.2 ⟨subd6_0_1461, List.forall_mem_cons.2 ⟨subd6_0_1462, List.forall_mem_cons.2 ⟨subd6_0_1463, List.forall_mem_cons.2 ⟨subd6_0_1464, List.forall_mem_cons.2 ⟨subd6_0_1465, List.forall_mem_cons.2 ⟨subd6_0_1466, List.forall_mem_cons.2 ⟨subd6_0_1467, List.forall_mem_cons.2 ⟨subd6_0_1468, List.forall_mem_cons.2 ⟨subd6_0_1469, List.forall_mem_cons.2 ⟨subd6_0_1470, List.forall_mem_cons.2 ⟨subd6_0_1471, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C093
