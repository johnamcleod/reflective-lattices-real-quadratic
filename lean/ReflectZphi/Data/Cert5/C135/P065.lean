import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd10_3_960 : subd10_3 [2, 0, 7] = true := by decide +kernel
theorem subd10_3_961 : subd10_3 [2, 0, 8] = true := by decide +kernel
theorem subd10_3_962 : subd10_3 [2, 1, -9] = true := by decide +kernel
theorem subd10_3_963 : subd10_3 [2, 1, -8] = true := by decide +kernel
theorem subd10_3_964 : subd10_3 [2, 1, -7] = true := by decide +kernel
theorem subd10_3_965 : subd10_3 [2, 1, -6] = true := by decide +kernel
theorem subd10_3_966 : subd10_3 [2, 1, -5] = true := by decide +kernel
theorem subd10_3_967 : subd10_3 [2, 1, -4] = true := by decide +kernel
theorem subd10_3_968 : subd10_3 [2, 1, -3] = true := by decide +kernel
theorem subd10_3_969 : subd10_3 [2, 1, -2] = true := by decide +kernel
theorem subd10_3_970 : subd10_3 [2, 1, -1] = true := by decide +kernel
theorem subd10_3_971 : subd10_3 [2, 1, 0] = true := by decide +kernel
theorem subd10_3_972 : subd10_3 [2, 1, 1] = true := by decide +kernel
theorem subd10_3_973 : subd10_3 [2, 1, 2] = true := by decide +kernel
theorem subd10_3_974 : subd10_3 [2, 1, 3] = true := by decide +kernel
theorem subd10_3_975 : subd10_3 [2, 1, 4] = true := by decide +kernel
theorem subd10_3_976 : subd10_3 [2, 1, 5] = true := by decide +kernel
theorem subd10_3_977 : subd10_3 [2, 1, 6] = true := by decide +kernel
theorem subd10_3_978 : subd10_3 [2, 1, 7] = true := by decide +kernel
theorem subd10_3_979 : subd10_3 [2, 1, 8] = true := by decide +kernel
theorem subd10_3_980 : subd10_3 [2, 2, -9] = true := by decide +kernel
theorem subd10_3_981 : subd10_3 [2, 2, -8] = true := by decide +kernel
theorem subd10_3_982 : subd10_3 [2, 2, -7] = true := by decide +kernel
theorem subd10_3_983 : subd10_3 [2, 2, -6] = true := by decide +kernel
theorem subd10_3_984 : subd10_3 [2, 2, -5] = true := by decide +kernel
theorem subd10_3_985 : subd10_3 [2, 2, -4] = true := by decide +kernel
theorem subd10_3_986 : subd10_3 [2, 2, -3] = true := by decide +kernel
theorem subd10_3_987 : subd10_3 [2, 2, -2] = true := by decide +kernel
theorem subd10_3_988 : subd10_3 [2, 2, -1] = true := by decide +kernel
theorem subd10_3_989 : subd10_3 [2, 2, 0] = true := by decide +kernel
theorem subd10_3_990 : subd10_3 [2, 2, 1] = true := by decide +kernel
theorem subd10_3_991 : subd10_3 [2, 2, 2] = true := by decide +kernel
theorem sbd10_3_30 : ∀ q ∈ blkd10_3_30, subd10_3 q = true := by
  unfold blkd10_3_30
  exact List.forall_mem_cons.2 ⟨subd10_3_960, List.forall_mem_cons.2 ⟨subd10_3_961, List.forall_mem_cons.2 ⟨subd10_3_962, List.forall_mem_cons.2 ⟨subd10_3_963, List.forall_mem_cons.2 ⟨subd10_3_964, List.forall_mem_cons.2 ⟨subd10_3_965, List.forall_mem_cons.2 ⟨subd10_3_966, List.forall_mem_cons.2 ⟨subd10_3_967, List.forall_mem_cons.2 ⟨subd10_3_968, List.forall_mem_cons.2 ⟨subd10_3_969, List.forall_mem_cons.2 ⟨subd10_3_970, List.forall_mem_cons.2 ⟨subd10_3_971, List.forall_mem_cons.2 ⟨subd10_3_972, List.forall_mem_cons.2 ⟨subd10_3_973, List.forall_mem_cons.2 ⟨subd10_3_974, List.forall_mem_cons.2 ⟨subd10_3_975, List.forall_mem_cons.2 ⟨subd10_3_976, List.forall_mem_cons.2 ⟨subd10_3_977, List.forall_mem_cons.2 ⟨subd10_3_978, List.forall_mem_cons.2 ⟨subd10_3_979, List.forall_mem_cons.2 ⟨subd10_3_980, List.forall_mem_cons.2 ⟨subd10_3_981, List.forall_mem_cons.2 ⟨subd10_3_982, List.forall_mem_cons.2 ⟨subd10_3_983, List.forall_mem_cons.2 ⟨subd10_3_984, List.forall_mem_cons.2 ⟨subd10_3_985, List.forall_mem_cons.2 ⟨subd10_3_986, List.forall_mem_cons.2 ⟨subd10_3_987, List.forall_mem_cons.2 ⟨subd10_3_988, List.forall_mem_cons.2 ⟨subd10_3_989, List.forall_mem_cons.2 ⟨subd10_3_990, List.forall_mem_cons.2 ⟨subd10_3_991, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_992 : subd10_3 [2, 2, 3] = true := by decide +kernel
theorem subd10_3_993 : subd10_3 [2, 2, 4] = true := by decide +kernel
theorem subd10_3_994 : subd10_3 [2, 2, 5] = true := by decide +kernel
theorem subd10_3_995 : subd10_3 [2, 2, 6] = true := by decide +kernel
theorem subd10_3_996 : subd10_3 [2, 2, 7] = true := by decide +kernel
theorem subd10_3_997 : subd10_3 [2, 3, -9] = true := by decide +kernel
theorem subd10_3_998 : subd10_3 [2, 3, -8] = true := by decide +kernel
theorem subd10_3_999 : subd10_3 [2, 3, -7] = true := by decide +kernel
theorem subd10_3_1000 : subd10_3 [2, 3, -6] = true := by decide +kernel
theorem subd10_3_1001 : subd10_3 [2, 3, -5] = true := by decide +kernel
theorem subd10_3_1002 : subd10_3 [2, 3, -4] = true := by decide +kernel
theorem subd10_3_1003 : subd10_3 [2, 3, -3] = true := by decide +kernel
theorem subd10_3_1004 : subd10_3 [2, 3, -2] = true := by decide +kernel
theorem subd10_3_1005 : subd10_3 [2, 3, -1] = true := by decide +kernel
theorem subd10_3_1006 : subd10_3 [2, 3, 0] = true := by decide +kernel
theorem subd10_3_1007 : subd10_3 [2, 3, 1] = true := by decide +kernel
theorem subd10_3_1008 : subd10_3 [2, 3, 2] = true := by decide +kernel
theorem subd10_3_1009 : subd10_3 [2, 3, 3] = true := by decide +kernel
theorem subd10_3_1010 : subd10_3 [2, 3, 4] = true := by decide +kernel
theorem subd10_3_1011 : subd10_3 [2, 3, 5] = true := by decide +kernel
theorem subd10_3_1012 : subd10_3 [2, 3, 6] = true := by decide +kernel
theorem subd10_3_1013 : subd10_3 [2, 4, -8] = true := by decide +kernel
theorem subd10_3_1014 : subd10_3 [2, 4, -7] = true := by decide +kernel
theorem subd10_3_1015 : subd10_3 [2, 4, -6] = true := by decide +kernel
theorem subd10_3_1016 : subd10_3 [2, 4, -5] = true := by decide +kernel
theorem subd10_3_1017 : subd10_3 [2, 4, -4] = true := by decide +kernel
theorem subd10_3_1018 : subd10_3 [2, 4, -3] = true := by decide +kernel
theorem subd10_3_1019 : subd10_3 [2, 4, -2] = true := by decide +kernel
theorem subd10_3_1020 : subd10_3 [2, 4, -1] = true := by decide +kernel
theorem subd10_3_1021 : subd10_3 [2, 4, 0] = true := by decide +kernel
theorem subd10_3_1022 : subd10_3 [2, 4, 1] = true := by decide +kernel
theorem subd10_3_1023 : subd10_3 [2, 4, 2] = true := by decide +kernel
theorem sbd10_3_31 : ∀ q ∈ blkd10_3_31, subd10_3 q = true := by
  unfold blkd10_3_31
  exact List.forall_mem_cons.2 ⟨subd10_3_992, List.forall_mem_cons.2 ⟨subd10_3_993, List.forall_mem_cons.2 ⟨subd10_3_994, List.forall_mem_cons.2 ⟨subd10_3_995, List.forall_mem_cons.2 ⟨subd10_3_996, List.forall_mem_cons.2 ⟨subd10_3_997, List.forall_mem_cons.2 ⟨subd10_3_998, List.forall_mem_cons.2 ⟨subd10_3_999, List.forall_mem_cons.2 ⟨subd10_3_1000, List.forall_mem_cons.2 ⟨subd10_3_1001, List.forall_mem_cons.2 ⟨subd10_3_1002, List.forall_mem_cons.2 ⟨subd10_3_1003, List.forall_mem_cons.2 ⟨subd10_3_1004, List.forall_mem_cons.2 ⟨subd10_3_1005, List.forall_mem_cons.2 ⟨subd10_3_1006, List.forall_mem_cons.2 ⟨subd10_3_1007, List.forall_mem_cons.2 ⟨subd10_3_1008, List.forall_mem_cons.2 ⟨subd10_3_1009, List.forall_mem_cons.2 ⟨subd10_3_1010, List.forall_mem_cons.2 ⟨subd10_3_1011, List.forall_mem_cons.2 ⟨subd10_3_1012, List.forall_mem_cons.2 ⟨subd10_3_1013, List.forall_mem_cons.2 ⟨subd10_3_1014, List.forall_mem_cons.2 ⟨subd10_3_1015, List.forall_mem_cons.2 ⟨subd10_3_1016, List.forall_mem_cons.2 ⟨subd10_3_1017, List.forall_mem_cons.2 ⟨subd10_3_1018, List.forall_mem_cons.2 ⟨subd10_3_1019, List.forall_mem_cons.2 ⟨subd10_3_1020, List.forall_mem_cons.2 ⟨subd10_3_1021, List.forall_mem_cons.2 ⟨subd10_3_1022, List.forall_mem_cons.2 ⟨subd10_3_1023, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_1024 : subd10_3 [2, 4, 3] = true := by decide +kernel
theorem subd10_3_1025 : subd10_3 [2, 4, 4] = true := by decide +kernel
theorem subd10_3_1026 : subd10_3 [2, 4, 5] = true := by decide +kernel
theorem subd10_3_1027 : subd10_3 [2, 5] = true := by decide +kernel
theorem subd10_3_1028 : subd10_3 [2, 6] = true := by decide +kernel
theorem subd10_3_1029 : subd10_3 [3, -7] = true := by decide +kernel
theorem subd10_3_1030 : subd10_3 [3, -6] = true := by decide +kernel
theorem subd10_3_1031 : subd10_3 [3, -5] = true := by decide +kernel
theorem subd10_3_1032 : subd10_3 [3, -4] = true := by decide +kernel
theorem subd10_3_1033 : subd10_3 [3, -3, -7] = true := by decide +kernel
theorem subd10_3_1034 : subd10_3 [3, -3, -6] = true := by decide +kernel
theorem subd10_3_1035 : subd10_3 [3, -3, -5] = true := by decide +kernel
theorem subd10_3_1036 : subd10_3 [3, -3, -4] = true := by decide +kernel
theorem subd10_3_1037 : subd10_3 [3, -3, -3] = true := by decide +kernel
theorem subd10_3_1038 : subd10_3 [3, -3, -2] = true := by decide +kernel
theorem subd10_3_1039 : subd10_3 [3, -3, -1] = true := by decide +kernel
theorem subd10_3_1040 : subd10_3 [3, -3, 0] = true := by decide +kernel
theorem subd10_3_1041 : subd10_3 [3, -3, 1] = true := by decide +kernel
theorem subd10_3_1042 : subd10_3 [3, -3, 2] = true := by decide +kernel
theorem subd10_3_1043 : subd10_3 [3, -3, 3] = true := by decide +kernel
theorem subd10_3_1044 : subd10_3 [3, -3, 4] = true := by decide +kernel
theorem subd10_3_1045 : subd10_3 [3, -3, 5] = true := by decide +kernel
theorem subd10_3_1046 : subd10_3 [3, -3, 6] = true := by decide +kernel
theorem subd10_3_1047 : subd10_3 [3, -3, 7] = true := by decide +kernel
theorem subd10_3_1048 : subd10_3 [3, -3, 8] = true := by decide +kernel
theorem subd10_3_1049 : subd10_3 [3, -2, -8] = true := by decide +kernel
theorem subd10_3_1050 : subd10_3 [3, -2, -7] = true := by decide +kernel
theorem subd10_3_1051 : subd10_3 [3, -2, -6] = true := by decide +kernel
theorem subd10_3_1052 : subd10_3 [3, -2, -5] = true := by decide +kernel
theorem subd10_3_1053 : subd10_3 [3, -2, -4] = true := by decide +kernel
theorem subd10_3_1054 : subd10_3 [3, -2, -3] = true := by decide +kernel
theorem subd10_3_1055 : subd10_3 [3, -2, -2] = true := by decide +kernel
theorem sbd10_3_32 : ∀ q ∈ blkd10_3_32, subd10_3 q = true := by
  unfold blkd10_3_32
  exact List.forall_mem_cons.2 ⟨subd10_3_1024, List.forall_mem_cons.2 ⟨subd10_3_1025, List.forall_mem_cons.2 ⟨subd10_3_1026, List.forall_mem_cons.2 ⟨subd10_3_1027, List.forall_mem_cons.2 ⟨subd10_3_1028, List.forall_mem_cons.2 ⟨subd10_3_1029, List.forall_mem_cons.2 ⟨subd10_3_1030, List.forall_mem_cons.2 ⟨subd10_3_1031, List.forall_mem_cons.2 ⟨subd10_3_1032, List.forall_mem_cons.2 ⟨subd10_3_1033, List.forall_mem_cons.2 ⟨subd10_3_1034, List.forall_mem_cons.2 ⟨subd10_3_1035, List.forall_mem_cons.2 ⟨subd10_3_1036, List.forall_mem_cons.2 ⟨subd10_3_1037, List.forall_mem_cons.2 ⟨subd10_3_1038, List.forall_mem_cons.2 ⟨subd10_3_1039, List.forall_mem_cons.2 ⟨subd10_3_1040, List.forall_mem_cons.2 ⟨subd10_3_1041, List.forall_mem_cons.2 ⟨subd10_3_1042, List.forall_mem_cons.2 ⟨subd10_3_1043, List.forall_mem_cons.2 ⟨subd10_3_1044, List.forall_mem_cons.2 ⟨subd10_3_1045, List.forall_mem_cons.2 ⟨subd10_3_1046, List.forall_mem_cons.2 ⟨subd10_3_1047, List.forall_mem_cons.2 ⟨subd10_3_1048, List.forall_mem_cons.2 ⟨subd10_3_1049, List.forall_mem_cons.2 ⟨subd10_3_1050, List.forall_mem_cons.2 ⟨subd10_3_1051, List.forall_mem_cons.2 ⟨subd10_3_1052, List.forall_mem_cons.2 ⟨subd10_3_1053, List.forall_mem_cons.2 ⟨subd10_3_1054, List.forall_mem_cons.2 ⟨subd10_3_1055, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_1056 : subd10_3 [3, -2, -1] = true := by decide +kernel
theorem subd10_3_1057 : subd10_3 [3, -2, 0] = true := by decide +kernel
theorem subd10_3_1058 : subd10_3 [3, -2, 1] = true := by decide +kernel
theorem subd10_3_1059 : subd10_3 [3, -2, 2] = true := by decide +kernel
theorem subd10_3_1060 : subd10_3 [3, -2, 3] = true := by decide +kernel
theorem subd10_3_1061 : subd10_3 [3, -2, 4] = true := by decide +kernel
theorem subd10_3_1062 : subd10_3 [3, -2, 5] = true := by decide +kernel
theorem subd10_3_1063 : subd10_3 [3, -2, 6] = true := by decide +kernel
theorem subd10_3_1064 : subd10_3 [3, -2, 7] = true := by decide +kernel
theorem subd10_3_1065 : subd10_3 [3, -2, 8] = true := by decide +kernel
theorem subd10_3_1066 : subd10_3 [3, -1, -8] = true := by decide +kernel
theorem subd10_3_1067 : subd10_3 [3, -1, -7] = true := by decide +kernel
theorem subd10_3_1068 : subd10_3 [3, -1, -6] = true := by decide +kernel
theorem subd10_3_1069 : subd10_3 [3, -1, -5] = true := by decide +kernel
theorem subd10_3_1070 : subd10_3 [3, -1, -4] = true := by decide +kernel
theorem subd10_3_1071 : subd10_3 [3, -1, -3] = true := by decide +kernel
theorem subd10_3_1072 : subd10_3 [3, -1, -2] = true := by decide +kernel
theorem subd10_3_1073 : subd10_3 [3, -1, -1] = true := by decide +kernel
theorem subd10_3_1074 : subd10_3 [3, -1, 0] = true := by decide +kernel
theorem subd10_3_1075 : subd10_3 [3, -1, 1] = true := by decide +kernel
theorem subd10_3_1076 : subd10_3 [3, -1, 2] = true := by decide +kernel
theorem subd10_3_1077 : subd10_3 [3, -1, 3] = true := by decide +kernel
theorem subd10_3_1078 : subd10_3 [3, -1, 4] = true := by decide +kernel
theorem subd10_3_1079 : subd10_3 [3, -1, 5] = true := by decide +kernel
theorem subd10_3_1080 : subd10_3 [3, -1, 6] = true := by decide +kernel
theorem subd10_3_1081 : subd10_3 [3, -1, 7] = true := by decide +kernel
theorem subd10_3_1082 : subd10_3 [3, -1, 8] = true := by decide +kernel
theorem subd10_3_1083 : subd10_3 [3, 0, -9] = true := by decide +kernel
theorem subd10_3_1084 : subd10_3 [3, 0, -8] = true := by decide +kernel
theorem subd10_3_1085 : subd10_3 [3, 0, -7] = true := by decide +kernel
theorem subd10_3_1086 : subd10_3 [3, 0, -6] = true := by decide +kernel
theorem subd10_3_1087 : subd10_3 [3, 0, -5] = true := by decide +kernel
theorem sbd10_3_33 : ∀ q ∈ blkd10_3_33, subd10_3 q = true := by
  unfold blkd10_3_33
  exact List.forall_mem_cons.2 ⟨subd10_3_1056, List.forall_mem_cons.2 ⟨subd10_3_1057, List.forall_mem_cons.2 ⟨subd10_3_1058, List.forall_mem_cons.2 ⟨subd10_3_1059, List.forall_mem_cons.2 ⟨subd10_3_1060, List.forall_mem_cons.2 ⟨subd10_3_1061, List.forall_mem_cons.2 ⟨subd10_3_1062, List.forall_mem_cons.2 ⟨subd10_3_1063, List.forall_mem_cons.2 ⟨subd10_3_1064, List.forall_mem_cons.2 ⟨subd10_3_1065, List.forall_mem_cons.2 ⟨subd10_3_1066, List.forall_mem_cons.2 ⟨subd10_3_1067, List.forall_mem_cons.2 ⟨subd10_3_1068, List.forall_mem_cons.2 ⟨subd10_3_1069, List.forall_mem_cons.2 ⟨subd10_3_1070, List.forall_mem_cons.2 ⟨subd10_3_1071, List.forall_mem_cons.2 ⟨subd10_3_1072, List.forall_mem_cons.2 ⟨subd10_3_1073, List.forall_mem_cons.2 ⟨subd10_3_1074, List.forall_mem_cons.2 ⟨subd10_3_1075, List.forall_mem_cons.2 ⟨subd10_3_1076, List.forall_mem_cons.2 ⟨subd10_3_1077, List.forall_mem_cons.2 ⟨subd10_3_1078, List.forall_mem_cons.2 ⟨subd10_3_1079, List.forall_mem_cons.2 ⟨subd10_3_1080, List.forall_mem_cons.2 ⟨subd10_3_1081, List.forall_mem_cons.2 ⟨subd10_3_1082, List.forall_mem_cons.2 ⟨subd10_3_1083, List.forall_mem_cons.2 ⟨subd10_3_1084, List.forall_mem_cons.2 ⟨subd10_3_1085, List.forall_mem_cons.2 ⟨subd10_3_1086, List.forall_mem_cons.2 ⟨subd10_3_1087, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_1088 : subd10_3 [3, 0, -4] = true := by decide +kernel
theorem subd10_3_1089 : subd10_3 [3, 0, -3] = true := by decide +kernel
theorem subd10_3_1090 : subd10_3 [3, 0, -2] = true := by decide +kernel
theorem subd10_3_1091 : subd10_3 [3, 0, -1] = true := by decide +kernel
theorem subd10_3_1092 : subd10_3 [3, 0, 0] = true := by decide +kernel
theorem subd10_3_1093 : subd10_3 [3, 0, 1] = true := by decide +kernel
theorem subd10_3_1094 : subd10_3 [3, 0, 2] = true := by decide +kernel
theorem subd10_3_1095 : subd10_3 [3, 0, 3] = true := by decide +kernel
theorem subd10_3_1096 : subd10_3 [3, 0, 4] = true := by decide +kernel
theorem subd10_3_1097 : subd10_3 [3, 0, 5] = true := by decide +kernel
theorem subd10_3_1098 : subd10_3 [3, 0, 6] = true := by decide +kernel
theorem subd10_3_1099 : subd10_3 [3, 0, 7] = true := by decide +kernel
theorem subd10_3_1100 : subd10_3 [3, 0, 8] = true := by decide +kernel
theorem subd10_3_1101 : subd10_3 [3, 1, -9] = true := by decide +kernel
theorem subd10_3_1102 : subd10_3 [3, 1, -8] = true := by decide +kernel
theorem subd10_3_1103 : subd10_3 [3, 1, -7] = true := by decide +kernel
theorem subd10_3_1104 : subd10_3 [3, 1, -6] = true := by decide +kernel
theorem subd10_3_1105 : subd10_3 [3, 1, -5] = true := by decide +kernel
theorem subd10_3_1106 : subd10_3 [3, 1, -4] = true := by decide +kernel
theorem subd10_3_1107 : subd10_3 [3, 1, -3] = true := by decide +kernel
theorem subd10_3_1108 : subd10_3 [3, 1, -2] = true := by decide +kernel
theorem subd10_3_1109 : subd10_3 [3, 1, -1] = true := by decide +kernel
theorem subd10_3_1110 : subd10_3 [3, 1, 0] = true := by decide +kernel
theorem subd10_3_1111 : subd10_3 [3, 1, 1] = true := by decide +kernel
theorem subd10_3_1112 : subd10_3 [3, 1, 2] = true := by decide +kernel
theorem subd10_3_1113 : subd10_3 [3, 1, 3] = true := by decide +kernel
theorem subd10_3_1114 : subd10_3 [3, 1, 4] = true := by decide +kernel
theorem subd10_3_1115 : subd10_3 [3, 1, 5] = true := by decide +kernel
theorem subd10_3_1116 : subd10_3 [3, 1, 6] = true := by decide +kernel
theorem subd10_3_1117 : subd10_3 [3, 1, 7] = true := by decide +kernel
theorem subd10_3_1118 : subd10_3 [3, 2, -9] = true := by decide +kernel
theorem subd10_3_1119 : subd10_3 [3, 2, -8] = true := by decide +kernel
theorem sbd10_3_34 : ∀ q ∈ blkd10_3_34, subd10_3 q = true := by
  unfold blkd10_3_34
  exact List.forall_mem_cons.2 ⟨subd10_3_1088, List.forall_mem_cons.2 ⟨subd10_3_1089, List.forall_mem_cons.2 ⟨subd10_3_1090, List.forall_mem_cons.2 ⟨subd10_3_1091, List.forall_mem_cons.2 ⟨subd10_3_1092, List.forall_mem_cons.2 ⟨subd10_3_1093, List.forall_mem_cons.2 ⟨subd10_3_1094, List.forall_mem_cons.2 ⟨subd10_3_1095, List.forall_mem_cons.2 ⟨subd10_3_1096, List.forall_mem_cons.2 ⟨subd10_3_1097, List.forall_mem_cons.2 ⟨subd10_3_1098, List.forall_mem_cons.2 ⟨subd10_3_1099, List.forall_mem_cons.2 ⟨subd10_3_1100, List.forall_mem_cons.2 ⟨subd10_3_1101, List.forall_mem_cons.2 ⟨subd10_3_1102, List.forall_mem_cons.2 ⟨subd10_3_1103, List.forall_mem_cons.2 ⟨subd10_3_1104, List.forall_mem_cons.2 ⟨subd10_3_1105, List.forall_mem_cons.2 ⟨subd10_3_1106, List.forall_mem_cons.2 ⟨subd10_3_1107, List.forall_mem_cons.2 ⟨subd10_3_1108, List.forall_mem_cons.2 ⟨subd10_3_1109, List.forall_mem_cons.2 ⟨subd10_3_1110, List.forall_mem_cons.2 ⟨subd10_3_1111, List.forall_mem_cons.2 ⟨subd10_3_1112, List.forall_mem_cons.2 ⟨subd10_3_1113, List.forall_mem_cons.2 ⟨subd10_3_1114, List.forall_mem_cons.2 ⟨subd10_3_1115, List.forall_mem_cons.2 ⟨subd10_3_1116, List.forall_mem_cons.2 ⟨subd10_3_1117, List.forall_mem_cons.2 ⟨subd10_3_1118, List.forall_mem_cons.2 ⟨subd10_3_1119, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_1120 : subd10_3 [3, 2, -7] = true := by decide +kernel
theorem subd10_3_1121 : subd10_3 [3, 2, -6] = true := by decide +kernel
theorem subd10_3_1122 : subd10_3 [3, 2, -5] = true := by decide +kernel
theorem subd10_3_1123 : subd10_3 [3, 2, -4] = true := by decide +kernel
theorem subd10_3_1124 : subd10_3 [3, 2, -3] = true := by decide +kernel
theorem subd10_3_1125 : subd10_3 [3, 2, -2] = true := by decide +kernel
theorem subd10_3_1126 : subd10_3 [3, 2, -1] = true := by decide +kernel
theorem subd10_3_1127 : subd10_3 [3, 2, 0] = true := by decide +kernel
theorem subd10_3_1128 : subd10_3 [3, 2, 1] = true := by decide +kernel
theorem subd10_3_1129 : subd10_3 [3, 2, 2] = true := by decide +kernel
theorem subd10_3_1130 : subd10_3 [3, 2, 3] = true := by decide +kernel
theorem subd10_3_1131 : subd10_3 [3, 2, 4] = true := by decide +kernel
theorem subd10_3_1132 : subd10_3 [3, 2, 5] = true := by decide +kernel
theorem subd10_3_1133 : subd10_3 [3, 2, 6] = true := by decide +kernel
theorem subd10_3_1134 : subd10_3 [3, 3, -8] = true := by decide +kernel
theorem subd10_3_1135 : subd10_3 [3, 3, -7] = true := by decide +kernel
theorem subd10_3_1136 : subd10_3 [3, 3, -6] = true := by decide +kernel
theorem subd10_3_1137 : subd10_3 [3, 3, -5] = true := by decide +kernel
theorem subd10_3_1138 : subd10_3 [3, 3, -4] = true := by decide +kernel
theorem subd10_3_1139 : subd10_3 [3, 3, -3] = true := by decide +kernel
theorem subd10_3_1140 : subd10_3 [3, 3, -2] = true := by decide +kernel
theorem subd10_3_1141 : subd10_3 [3, 3, -1] = true := by decide +kernel
theorem subd10_3_1142 : subd10_3 [3, 3, 0] = true := by decide +kernel
theorem subd10_3_1143 : subd10_3 [3, 3, 1] = true := by decide +kernel
theorem subd10_3_1144 : subd10_3 [3, 3, 2] = true := by decide +kernel
theorem subd10_3_1145 : subd10_3 [3, 3, 3] = true := by decide +kernel
theorem subd10_3_1146 : subd10_3 [3, 3, 4] = true := by decide +kernel
theorem subd10_3_1147 : subd10_3 [3, 3, 5] = true := by decide +kernel
theorem subd10_3_1148 : subd10_3 [3, 4] = true := by decide +kernel
theorem subd10_3_1149 : subd10_3 [3, 5] = true := by decide +kernel
theorem subd10_3_1150 : subd10_3 [4, -6] = true := by decide +kernel
theorem subd10_3_1151 : subd10_3 [4, -5] = true := by decide +kernel
theorem sbd10_3_35 : ∀ q ∈ blkd10_3_35, subd10_3 q = true := by
  unfold blkd10_3_35
  exact List.forall_mem_cons.2 ⟨subd10_3_1120, List.forall_mem_cons.2 ⟨subd10_3_1121, List.forall_mem_cons.2 ⟨subd10_3_1122, List.forall_mem_cons.2 ⟨subd10_3_1123, List.forall_mem_cons.2 ⟨subd10_3_1124, List.forall_mem_cons.2 ⟨subd10_3_1125, List.forall_mem_cons.2 ⟨subd10_3_1126, List.forall_mem_cons.2 ⟨subd10_3_1127, List.forall_mem_cons.2 ⟨subd10_3_1128, List.forall_mem_cons.2 ⟨subd10_3_1129, List.forall_mem_cons.2 ⟨subd10_3_1130, List.forall_mem_cons.2 ⟨subd10_3_1131, List.forall_mem_cons.2 ⟨subd10_3_1132, List.forall_mem_cons.2 ⟨subd10_3_1133, List.forall_mem_cons.2 ⟨subd10_3_1134, List.forall_mem_cons.2 ⟨subd10_3_1135, List.forall_mem_cons.2 ⟨subd10_3_1136, List.forall_mem_cons.2 ⟨subd10_3_1137, List.forall_mem_cons.2 ⟨subd10_3_1138, List.forall_mem_cons.2 ⟨subd10_3_1139, List.forall_mem_cons.2 ⟨subd10_3_1140, List.forall_mem_cons.2 ⟨subd10_3_1141, List.forall_mem_cons.2 ⟨subd10_3_1142, List.forall_mem_cons.2 ⟨subd10_3_1143, List.forall_mem_cons.2 ⟨subd10_3_1144, List.forall_mem_cons.2 ⟨subd10_3_1145, List.forall_mem_cons.2 ⟨subd10_3_1146, List.forall_mem_cons.2 ⟨subd10_3_1147, List.forall_mem_cons.2 ⟨subd10_3_1148, List.forall_mem_cons.2 ⟨subd10_3_1149, List.forall_mem_cons.2 ⟨subd10_3_1150, List.forall_mem_cons.2 ⟨subd10_3_1151, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_1152 : subd10_3 [4, -4] = true := by decide +kernel
theorem subd10_3_1153 : subd10_3 [4, -3, -6] = true := by decide +kernel
theorem subd10_3_1154 : subd10_3 [4, -3, -5] = true := by decide +kernel
theorem subd10_3_1155 : subd10_3 [4, -3, -4] = true := by decide +kernel
theorem subd10_3_1156 : subd10_3 [4, -3, -3] = true := by decide +kernel
theorem subd10_3_1157 : subd10_3 [4, -3, -2] = true := by decide +kernel
theorem subd10_3_1158 : subd10_3 [4, -3, -1] = true := by decide +kernel
theorem subd10_3_1159 : subd10_3 [4, -3, 0] = true := by decide +kernel
theorem subd10_3_1160 : subd10_3 [4, -3, 1] = true := by decide +kernel
theorem subd10_3_1161 : subd10_3 [4, -3, 2] = true := by decide +kernel
theorem subd10_3_1162 : subd10_3 [4, -3, 3] = true := by decide +kernel
theorem subd10_3_1163 : subd10_3 [4, -3, 4] = true := by decide +kernel
theorem subd10_3_1164 : subd10_3 [4, -3, 5] = true := by decide +kernel
theorem subd10_3_1165 : subd10_3 [4, -3, 6] = true := by decide +kernel
theorem subd10_3_1166 : subd10_3 [4, -3, 7] = true := by decide +kernel
theorem subd10_3_1167 : subd10_3 [4, -2, -7] = true := by decide +kernel
theorem subd10_3_1168 : subd10_3 [4, -2, -6] = true := by decide +kernel
theorem subd10_3_1169 : subd10_3 [4, -2, -5] = true := by decide +kernel
theorem subd10_3_1170 : subd10_3 [4, -2, -4] = true := by decide +kernel
theorem subd10_3_1171 : subd10_3 [4, -2, -3] = true := by decide +kernel
theorem subd10_3_1172 : subd10_3 [4, -2, -2] = true := by decide +kernel
theorem subd10_3_1173 : subd10_3 [4, -2, -1] = true := by decide +kernel
theorem subd10_3_1174 : subd10_3 [4, -2, 0] = true := by decide +kernel
theorem subd10_3_1175 : subd10_3 [4, -2, 1] = true := by decide +kernel
theorem subd10_3_1176 : subd10_3 [4, -2, 2] = true := by decide +kernel
theorem subd10_3_1177 : subd10_3 [4, -2, 3] = true := by decide +kernel
theorem subd10_3_1178 : subd10_3 [4, -2, 4] = true := by decide +kernel
theorem subd10_3_1179 : subd10_3 [4, -2, 5] = true := by decide +kernel
theorem subd10_3_1180 : subd10_3 [4, -2, 6] = true := by decide +kernel
theorem subd10_3_1181 : subd10_3 [4, -2, 7] = true := by decide +kernel
theorem subd10_3_1182 : subd10_3 [4, -1, -7] = true := by decide +kernel
theorem subd10_3_1183 : subd10_3 [4, -1, -6] = true := by decide +kernel
theorem sbd10_3_36 : ∀ q ∈ blkd10_3_36, subd10_3 q = true := by
  unfold blkd10_3_36
  exact List.forall_mem_cons.2 ⟨subd10_3_1152, List.forall_mem_cons.2 ⟨subd10_3_1153, List.forall_mem_cons.2 ⟨subd10_3_1154, List.forall_mem_cons.2 ⟨subd10_3_1155, List.forall_mem_cons.2 ⟨subd10_3_1156, List.forall_mem_cons.2 ⟨subd10_3_1157, List.forall_mem_cons.2 ⟨subd10_3_1158, List.forall_mem_cons.2 ⟨subd10_3_1159, List.forall_mem_cons.2 ⟨subd10_3_1160, List.forall_mem_cons.2 ⟨subd10_3_1161, List.forall_mem_cons.2 ⟨subd10_3_1162, List.forall_mem_cons.2 ⟨subd10_3_1163, List.forall_mem_cons.2 ⟨subd10_3_1164, List.forall_mem_cons.2 ⟨subd10_3_1165, List.forall_mem_cons.2 ⟨subd10_3_1166, List.forall_mem_cons.2 ⟨subd10_3_1167, List.forall_mem_cons.2 ⟨subd10_3_1168, List.forall_mem_cons.2 ⟨subd10_3_1169, List.forall_mem_cons.2 ⟨subd10_3_1170, List.forall_mem_cons.2 ⟨subd10_3_1171, List.forall_mem_cons.2 ⟨subd10_3_1172, List.forall_mem_cons.2 ⟨subd10_3_1173, List.forall_mem_cons.2 ⟨subd10_3_1174, List.forall_mem_cons.2 ⟨subd10_3_1175, List.forall_mem_cons.2 ⟨subd10_3_1176, List.forall_mem_cons.2 ⟨subd10_3_1177, List.forall_mem_cons.2 ⟨subd10_3_1178, List.forall_mem_cons.2 ⟨subd10_3_1179, List.forall_mem_cons.2 ⟨subd10_3_1180, List.forall_mem_cons.2 ⟨subd10_3_1181, List.forall_mem_cons.2 ⟨subd10_3_1182, List.forall_mem_cons.2 ⟨subd10_3_1183, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_1184 : subd10_3 [4, -1, -5] = true := by decide +kernel
theorem subd10_3_1185 : subd10_3 [4, -1, -4] = true := by decide +kernel
theorem subd10_3_1186 : subd10_3 [4, -1, -3] = true := by decide +kernel
theorem subd10_3_1187 : subd10_3 [4, -1, -2] = true := by decide +kernel
theorem subd10_3_1188 : subd10_3 [4, -1, -1] = true := by decide +kernel
theorem subd10_3_1189 : subd10_3 [4, -1, 0] = true := by decide +kernel
theorem subd10_3_1190 : subd10_3 [4, -1, 1] = true := by decide +kernel
theorem subd10_3_1191 : subd10_3 [4, -1, 2] = true := by decide +kernel
theorem subd10_3_1192 : subd10_3 [4, -1, 3] = true := by decide +kernel
theorem subd10_3_1193 : subd10_3 [4, -1, 4] = true := by decide +kernel
theorem subd10_3_1194 : subd10_3 [4, -1, 5] = true := by decide +kernel
theorem subd10_3_1195 : subd10_3 [4, -1, 6] = true := by decide +kernel
theorem subd10_3_1196 : subd10_3 [4, -1, 7] = true := by decide +kernel
theorem subd10_3_1197 : subd10_3 [4, 0, -8] = true := by decide +kernel
theorem subd10_3_1198 : subd10_3 [4, 0, -7] = true := by decide +kernel
theorem subd10_3_1199 : subd10_3 [4, 0, -6] = true := by decide +kernel
theorem subd10_3_1200 : subd10_3 [4, 0, -5] = true := by decide +kernel
theorem subd10_3_1201 : subd10_3 [4, 0, -4] = true := by decide +kernel
theorem subd10_3_1202 : subd10_3 [4, 0, -3] = true := by decide +kernel
theorem subd10_3_1203 : subd10_3 [4, 0, -2] = true := by decide +kernel
theorem subd10_3_1204 : subd10_3 [4, 0, -1] = true := by decide +kernel
theorem subd10_3_1205 : subd10_3 [4, 0, 0] = true := by decide +kernel
theorem subd10_3_1206 : subd10_3 [4, 0, 1] = true := by decide +kernel
theorem subd10_3_1207 : subd10_3 [4, 0, 2] = true := by decide +kernel
theorem subd10_3_1208 : subd10_3 [4, 0, 3] = true := by decide +kernel
theorem subd10_3_1209 : subd10_3 [4, 0, 4] = true := by decide +kernel
theorem subd10_3_1210 : subd10_3 [4, 0, 5] = true := by decide +kernel
theorem subd10_3_1211 : subd10_3 [4, 0, 6] = true := by decide +kernel
theorem subd10_3_1212 : subd10_3 [4, 0, 7] = true := by decide +kernel
theorem subd10_3_1213 : subd10_3 [4, 1, -8] = true := by decide +kernel
theorem subd10_3_1214 : subd10_3 [4, 1, -7] = true := by decide +kernel
theorem subd10_3_1215 : subd10_3 [4, 1, -6] = true := by decide +kernel
theorem sbd10_3_37 : ∀ q ∈ blkd10_3_37, subd10_3 q = true := by
  unfold blkd10_3_37
  exact List.forall_mem_cons.2 ⟨subd10_3_1184, List.forall_mem_cons.2 ⟨subd10_3_1185, List.forall_mem_cons.2 ⟨subd10_3_1186, List.forall_mem_cons.2 ⟨subd10_3_1187, List.forall_mem_cons.2 ⟨subd10_3_1188, List.forall_mem_cons.2 ⟨subd10_3_1189, List.forall_mem_cons.2 ⟨subd10_3_1190, List.forall_mem_cons.2 ⟨subd10_3_1191, List.forall_mem_cons.2 ⟨subd10_3_1192, List.forall_mem_cons.2 ⟨subd10_3_1193, List.forall_mem_cons.2 ⟨subd10_3_1194, List.forall_mem_cons.2 ⟨subd10_3_1195, List.forall_mem_cons.2 ⟨subd10_3_1196, List.forall_mem_cons.2 ⟨subd10_3_1197, List.forall_mem_cons.2 ⟨subd10_3_1198, List.forall_mem_cons.2 ⟨subd10_3_1199, List.forall_mem_cons.2 ⟨subd10_3_1200, List.forall_mem_cons.2 ⟨subd10_3_1201, List.forall_mem_cons.2 ⟨subd10_3_1202, List.forall_mem_cons.2 ⟨subd10_3_1203, List.forall_mem_cons.2 ⟨subd10_3_1204, List.forall_mem_cons.2 ⟨subd10_3_1205, List.forall_mem_cons.2 ⟨subd10_3_1206, List.forall_mem_cons.2 ⟨subd10_3_1207, List.forall_mem_cons.2 ⟨subd10_3_1208, List.forall_mem_cons.2 ⟨subd10_3_1209, List.forall_mem_cons.2 ⟨subd10_3_1210, List.forall_mem_cons.2 ⟨subd10_3_1211, List.forall_mem_cons.2 ⟨subd10_3_1212, List.forall_mem_cons.2 ⟨subd10_3_1213, List.forall_mem_cons.2 ⟨subd10_3_1214, List.forall_mem_cons.2 ⟨subd10_3_1215, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_1216 : subd10_3 [4, 1, -5] = true := by decide +kernel
theorem subd10_3_1217 : subd10_3 [4, 1, -4] = true := by decide +kernel
theorem subd10_3_1218 : subd10_3 [4, 1, -3] = true := by decide +kernel
theorem subd10_3_1219 : subd10_3 [4, 1, -2] = true := by decide +kernel
theorem subd10_3_1220 : subd10_3 [4, 1, -1] = true := by decide +kernel
theorem subd10_3_1221 : subd10_3 [4, 1, 0] = true := by decide +kernel
theorem subd10_3_1222 : subd10_3 [4, 1, 1] = true := by decide +kernel
theorem subd10_3_1223 : subd10_3 [4, 1, 2] = true := by decide +kernel
theorem subd10_3_1224 : subd10_3 [4, 1, 3] = true := by decide +kernel
theorem subd10_3_1225 : subd10_3 [4, 1, 4] = true := by decide +kernel
theorem subd10_3_1226 : subd10_3 [4, 1, 5] = true := by decide +kernel
theorem subd10_3_1227 : subd10_3 [4, 1, 6] = true := by decide +kernel
theorem subd10_3_1228 : subd10_3 [4, 2, -8] = true := by decide +kernel
theorem subd10_3_1229 : subd10_3 [4, 2, -7] = true := by decide +kernel
theorem subd10_3_1230 : subd10_3 [4, 2, -6] = true := by decide +kernel
theorem subd10_3_1231 : subd10_3 [4, 2, -5] = true := by decide +kernel
theorem subd10_3_1232 : subd10_3 [4, 2, -4] = true := by decide +kernel
theorem subd10_3_1233 : subd10_3 [4, 2, -3] = true := by decide +kernel
theorem subd10_3_1234 : subd10_3 [4, 2, -2] = true := by decide +kernel
theorem subd10_3_1235 : subd10_3 [4, 2, -1] = true := by decide +kernel
theorem subd10_3_1236 : subd10_3 [4, 2, 0] = true := by decide +kernel
theorem subd10_3_1237 : subd10_3 [4, 2, 1] = true := by decide +kernel
theorem subd10_3_1238 : subd10_3 [4, 2, 2] = true := by decide +kernel
theorem subd10_3_1239 : subd10_3 [4, 2, 3] = true := by decide +kernel
theorem subd10_3_1240 : subd10_3 [4, 2, 4] = true := by decide +kernel
theorem subd10_3_1241 : subd10_3 [4, 2, 5] = true := by decide +kernel
theorem subd10_3_1242 : subd10_3 [4, 2, 6] = true := by decide +kernel
theorem subd10_3_1243 : subd10_3 [4, 3] = true := by decide +kernel
theorem subd10_3_1244 : subd10_3 [4, 4] = true := by decide +kernel
theorem subd10_3_1245 : subd10_3 [5, -5] = true := by decide +kernel
theorem subd10_3_1246 : subd10_3 [5, -4] = true := by decide +kernel
theorem subd10_3_1247 : subd10_3 [5, -3] = true := by decide +kernel
theorem sbd10_3_38 : ∀ q ∈ blkd10_3_38, subd10_3 q = true := by
  unfold blkd10_3_38
  exact List.forall_mem_cons.2 ⟨subd10_3_1216, List.forall_mem_cons.2 ⟨subd10_3_1217, List.forall_mem_cons.2 ⟨subd10_3_1218, List.forall_mem_cons.2 ⟨subd10_3_1219, List.forall_mem_cons.2 ⟨subd10_3_1220, List.forall_mem_cons.2 ⟨subd10_3_1221, List.forall_mem_cons.2 ⟨subd10_3_1222, List.forall_mem_cons.2 ⟨subd10_3_1223, List.forall_mem_cons.2 ⟨subd10_3_1224, List.forall_mem_cons.2 ⟨subd10_3_1225, List.forall_mem_cons.2 ⟨subd10_3_1226, List.forall_mem_cons.2 ⟨subd10_3_1227, List.forall_mem_cons.2 ⟨subd10_3_1228, List.forall_mem_cons.2 ⟨subd10_3_1229, List.forall_mem_cons.2 ⟨subd10_3_1230, List.forall_mem_cons.2 ⟨subd10_3_1231, List.forall_mem_cons.2 ⟨subd10_3_1232, List.forall_mem_cons.2 ⟨subd10_3_1233, List.forall_mem_cons.2 ⟨subd10_3_1234, List.forall_mem_cons.2 ⟨subd10_3_1235, List.forall_mem_cons.2 ⟨subd10_3_1236, List.forall_mem_cons.2 ⟨subd10_3_1237, List.forall_mem_cons.2 ⟨subd10_3_1238, List.forall_mem_cons.2 ⟨subd10_3_1239, List.forall_mem_cons.2 ⟨subd10_3_1240, List.forall_mem_cons.2 ⟨subd10_3_1241, List.forall_mem_cons.2 ⟨subd10_3_1242, List.forall_mem_cons.2 ⟨subd10_3_1243, List.forall_mem_cons.2 ⟨subd10_3_1244, List.forall_mem_cons.2 ⟨subd10_3_1245, List.forall_mem_cons.2 ⟨subd10_3_1246, List.forall_mem_cons.2 ⟨subd10_3_1247, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_1248 : subd10_3 [5, -2] = true := by decide +kernel
theorem subd10_3_1249 : subd10_3 [5, -1] = true := by decide +kernel
theorem subd10_3_1250 : subd10_3 [5, 0] = true := by decide +kernel
theorem subd10_3_1251 : subd10_3 [5, 1] = true := by decide +kernel
theorem subd10_3_1252 : subd10_3 [5, 2] = true := by decide +kernel
theorem subd10_3_1253 : subd10_3 [5, 3] = true := by decide +kernel
theorem subd10_3_1254 : subd10_3 [6, -4] = true := by decide +kernel
theorem subd10_3_1255 : subd10_3 [6, -3] = true := by decide +kernel
theorem subd10_3_1256 : subd10_3 [6, -2] = true := by decide +kernel
theorem subd10_3_1257 : subd10_3 [6, -1] = true := by decide +kernel
theorem subd10_3_1258 : subd10_3 [6, 0] = true := by decide +kernel
theorem subd10_3_1259 : subd10_3 [6, 1] = true := by decide +kernel
theorem subd10_3_1260 : subd10_3 [6, 2] = true := by decide +kernel
theorem sbd10_3_39 : ∀ q ∈ blkd10_3_39, subd10_3 q = true := by
  unfold blkd10_3_39
  exact List.forall_mem_cons.2 ⟨subd10_3_1248, List.forall_mem_cons.2 ⟨subd10_3_1249, List.forall_mem_cons.2 ⟨subd10_3_1250, List.forall_mem_cons.2 ⟨subd10_3_1251, List.forall_mem_cons.2 ⟨subd10_3_1252, List.forall_mem_cons.2 ⟨subd10_3_1253, List.forall_mem_cons.2 ⟨subd10_3_1254, List.forall_mem_cons.2 ⟨subd10_3_1255, List.forall_mem_cons.2 ⟨subd10_3_1256, List.forall_mem_cons.2 ⟨subd10_3_1257, List.forall_mem_cons.2 ⟨subd10_3_1258, List.forall_mem_cons.2 ⟨subd10_3_1259, List.forall_mem_cons.2 ⟨subd10_3_1260, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_4 : ldCheck G d10_4.U d10_4.ms ldd10_4 = true := by decide +kernel
theorem pre_okd10_4 : subPre G cell10 d10_4 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C135
