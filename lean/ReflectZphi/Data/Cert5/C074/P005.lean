import ReflectZphi.Data.Cert5.C074.Base

namespace ReflectZphi.Data.Cert5.C074
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub7_960 : sub7 [1, 2, -8] = true := by decide +kernel
theorem sub7_961 : sub7 [1, 2, -7] = true := by decide +kernel
theorem sub7_962 : sub7 [1, 2, -6] = true := by decide +kernel
theorem sub7_963 : sub7 [1, 2, -5] = true := by decide +kernel
theorem sub7_964 : sub7 [1, 2, -4] = true := by decide +kernel
theorem sub7_965 : sub7 [1, 2, -3] = true := by decide +kernel
theorem sub7_966 : sub7 [1, 2, -2] = true := by decide +kernel
theorem sub7_967 : sub7 [1, 2, -1] = true := by decide +kernel
theorem sub7_968 : sub7 [1, 2, 0] = true := by decide +kernel
theorem sub7_969 : sub7 [1, 2, 1] = true := by decide +kernel
theorem sub7_970 : sub7 [1, 2, 2] = true := by decide +kernel
theorem sub7_971 : sub7 [1, 2, 3] = true := by decide +kernel
theorem sub7_972 : sub7 [1, 2, 4] = true := by decide +kernel
theorem sub7_973 : sub7 [1, 2, 5] = true := by decide +kernel
theorem sub7_974 : sub7 [1, 2, 6] = true := by decide +kernel
theorem sub7_975 : sub7 [1, 2, 7] = true := by decide +kernel
theorem sub7_976 : sub7 [1, 2, 8] = true := by decide +kernel
theorem sub7_977 : sub7 [1, 2, 9] = true := by decide +kernel
theorem sub7_978 : sub7 [1, 3, -9] = true := by decide +kernel
theorem sub7_979 : sub7 [1, 3, -8] = true := by decide +kernel
theorem sub7_980 : sub7 [1, 3, -7] = true := by decide +kernel
theorem sub7_981 : sub7 [1, 3, -6] = true := by decide +kernel
theorem sub7_982 : sub7 [1, 3, -5] = true := by decide +kernel
theorem sub7_983 : sub7 [1, 3, -4] = true := by decide +kernel
theorem sub7_984 : sub7 [1, 3, -3] = true := by decide +kernel
theorem sub7_985 : sub7 [1, 3, -2] = true := by decide +kernel
theorem sub7_986 : sub7 [1, 3, -1] = true := by decide +kernel
theorem sub7_987 : sub7 [1, 3, 0] = true := by decide +kernel
theorem sub7_988 : sub7 [1, 3, 1] = true := by decide +kernel
theorem sub7_989 : sub7 [1, 3, 2] = true := by decide +kernel
theorem sub7_990 : sub7 [1, 3, 3] = true := by decide +kernel
theorem sub7_991 : sub7 [1, 3, 4] = true := by decide +kernel
theorem sb7_30 : ∀ q ∈ blk7_30, sub7 q = true := by
  unfold blk7_30
  exact List.forall_mem_cons.2 ⟨sub7_960, List.forall_mem_cons.2 ⟨sub7_961, List.forall_mem_cons.2 ⟨sub7_962, List.forall_mem_cons.2 ⟨sub7_963, List.forall_mem_cons.2 ⟨sub7_964, List.forall_mem_cons.2 ⟨sub7_965, List.forall_mem_cons.2 ⟨sub7_966, List.forall_mem_cons.2 ⟨sub7_967, List.forall_mem_cons.2 ⟨sub7_968, List.forall_mem_cons.2 ⟨sub7_969, List.forall_mem_cons.2 ⟨sub7_970, List.forall_mem_cons.2 ⟨sub7_971, List.forall_mem_cons.2 ⟨sub7_972, List.forall_mem_cons.2 ⟨sub7_973, List.forall_mem_cons.2 ⟨sub7_974, List.forall_mem_cons.2 ⟨sub7_975, List.forall_mem_cons.2 ⟨sub7_976, List.forall_mem_cons.2 ⟨sub7_977, List.forall_mem_cons.2 ⟨sub7_978, List.forall_mem_cons.2 ⟨sub7_979, List.forall_mem_cons.2 ⟨sub7_980, List.forall_mem_cons.2 ⟨sub7_981, List.forall_mem_cons.2 ⟨sub7_982, List.forall_mem_cons.2 ⟨sub7_983, List.forall_mem_cons.2 ⟨sub7_984, List.forall_mem_cons.2 ⟨sub7_985, List.forall_mem_cons.2 ⟨sub7_986, List.forall_mem_cons.2 ⟨sub7_987, List.forall_mem_cons.2 ⟨sub7_988, List.forall_mem_cons.2 ⟨sub7_989, List.forall_mem_cons.2 ⟨sub7_990, List.forall_mem_cons.2 ⟨sub7_991, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_992 : sub7 [1, 3, 5] = true := by decide +kernel
theorem sub7_993 : sub7 [1, 3, 6] = true := by decide +kernel
theorem sub7_994 : sub7 [1, 3, 7] = true := by decide +kernel
theorem sub7_995 : sub7 [1, 3, 8] = true := by decide +kernel
theorem sub7_996 : sub7 [1, 3, 9] = true := by decide +kernel
theorem sub7_997 : sub7 [1, 4, -8] = true := by decide +kernel
theorem sub7_998 : sub7 [1, 4, -7] = true := by decide +kernel
theorem sub7_999 : sub7 [1, 4, -6] = true := by decide +kernel
theorem sub7_1000 : sub7 [1, 4, -5] = true := by decide +kernel
theorem sub7_1001 : sub7 [1, 4, -4] = true := by decide +kernel
theorem sub7_1002 : sub7 [1, 4, -3] = true := by decide +kernel
theorem sub7_1003 : sub7 [1, 4, -2] = true := by decide +kernel
theorem sub7_1004 : sub7 [1, 4, -1] = true := by decide +kernel
theorem sub7_1005 : sub7 [1, 4, 0] = true := by decide +kernel
theorem sub7_1006 : sub7 [1, 4, 1] = true := by decide +kernel
theorem sub7_1007 : sub7 [1, 4, 2] = true := by decide +kernel
theorem sub7_1008 : sub7 [1, 4, 3] = true := by decide +kernel
theorem sub7_1009 : sub7 [1, 4, 4] = true := by decide +kernel
theorem sub7_1010 : sub7 [1, 4, 5] = true := by decide +kernel
theorem sub7_1011 : sub7 [1, 4, 6] = true := by decide +kernel
theorem sub7_1012 : sub7 [1, 4, 7] = true := by decide +kernel
theorem sub7_1013 : sub7 [1, 4, 8] = true := by decide +kernel
theorem sub7_1014 : sub7 [1, 4, 9] = true := by decide +kernel
theorem sub7_1015 : sub7 [1, 5, -7] = true := by decide +kernel
theorem sub7_1016 : sub7 [1, 5, -6] = true := by decide +kernel
theorem sub7_1017 : sub7 [1, 5, -5] = true := by decide +kernel
theorem sub7_1018 : sub7 [1, 5, -4] = true := by decide +kernel
theorem sub7_1019 : sub7 [1, 5, -3] = true := by decide +kernel
theorem sub7_1020 : sub7 [1, 5, -2] = true := by decide +kernel
theorem sub7_1021 : sub7 [1, 5, -1] = true := by decide +kernel
theorem sub7_1022 : sub7 [1, 5, 0] = true := by decide +kernel
theorem sub7_1023 : sub7 [1, 5, 1] = true := by decide +kernel
theorem sb7_31 : ∀ q ∈ blk7_31, sub7 q = true := by
  unfold blk7_31
  exact List.forall_mem_cons.2 ⟨sub7_992, List.forall_mem_cons.2 ⟨sub7_993, List.forall_mem_cons.2 ⟨sub7_994, List.forall_mem_cons.2 ⟨sub7_995, List.forall_mem_cons.2 ⟨sub7_996, List.forall_mem_cons.2 ⟨sub7_997, List.forall_mem_cons.2 ⟨sub7_998, List.forall_mem_cons.2 ⟨sub7_999, List.forall_mem_cons.2 ⟨sub7_1000, List.forall_mem_cons.2 ⟨sub7_1001, List.forall_mem_cons.2 ⟨sub7_1002, List.forall_mem_cons.2 ⟨sub7_1003, List.forall_mem_cons.2 ⟨sub7_1004, List.forall_mem_cons.2 ⟨sub7_1005, List.forall_mem_cons.2 ⟨sub7_1006, List.forall_mem_cons.2 ⟨sub7_1007, List.forall_mem_cons.2 ⟨sub7_1008, List.forall_mem_cons.2 ⟨sub7_1009, List.forall_mem_cons.2 ⟨sub7_1010, List.forall_mem_cons.2 ⟨sub7_1011, List.forall_mem_cons.2 ⟨sub7_1012, List.forall_mem_cons.2 ⟨sub7_1013, List.forall_mem_cons.2 ⟨sub7_1014, List.forall_mem_cons.2 ⟨sub7_1015, List.forall_mem_cons.2 ⟨sub7_1016, List.forall_mem_cons.2 ⟨sub7_1017, List.forall_mem_cons.2 ⟨sub7_1018, List.forall_mem_cons.2 ⟨sub7_1019, List.forall_mem_cons.2 ⟨sub7_1020, List.forall_mem_cons.2 ⟨sub7_1021, List.forall_mem_cons.2 ⟨sub7_1022, List.forall_mem_cons.2 ⟨sub7_1023, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_1024 : sub7 [1, 5, 2] = true := by decide +kernel
theorem sub7_1025 : sub7 [1, 5, 3] = true := by decide +kernel
theorem sub7_1026 : sub7 [1, 5, 4] = true := by decide +kernel
theorem sub7_1027 : sub7 [1, 5, 5] = true := by decide +kernel
theorem sub7_1028 : sub7 [1, 5, 6] = true := by decide +kernel
theorem sub7_1029 : sub7 [1, 5, 7] = true := by decide +kernel
theorem sub7_1030 : sub7 [1, 5, 8] = true := by decide +kernel
theorem sub7_1031 : sub7 [1, 6] = true := by decide +kernel
theorem sub7_1032 : sub7 [1, 7] = true := by decide +kernel
theorem sub7_1033 : sub7 [1, 8] = true := by decide +kernel
theorem sub7_1034 : sub7 [2, -7] = true := by decide +kernel
theorem sub7_1035 : sub7 [2, -6] = true := by decide +kernel
theorem sub7_1036 : sub7 [2, -5] = true := by decide +kernel
theorem sub7_1037 : sub7 [2, -4] = true := by decide +kernel
theorem sub7_1038 : sub7 [2, -3, -8] = true := by decide +kernel
theorem sub7_1039 : sub7 [2, -3, -7] = true := by decide +kernel
theorem sub7_1040 : sub7 [2, -3, -6] = true := by decide +kernel
theorem sub7_1041 : sub7 [2, -3, -5] = true := by decide +kernel
theorem sub7_1042 : sub7 [2, -3, -4] = true := by decide +kernel
theorem sub7_1043 : sub7 [2, -3, -3] = true := by decide +kernel
theorem sub7_1044 : sub7 [2, -3, -2] = true := by decide +kernel
theorem sub7_1045 : sub7 [2, -3, -1] = true := by decide +kernel
theorem sub7_1046 : sub7 [2, -3, 0] = true := by decide +kernel
theorem sub7_1047 : sub7 [2, -3, 1] = true := by decide +kernel
theorem sub7_1048 : sub7 [2, -3, 2] = true := by decide +kernel
theorem sub7_1049 : sub7 [2, -3, 3] = true := by decide +kernel
theorem sub7_1050 : sub7 [2, -3, 4] = true := by decide +kernel
theorem sub7_1051 : sub7 [2, -3, 5] = true := by decide +kernel
theorem sub7_1052 : sub7 [2, -3, 6] = true := by decide +kernel
theorem sub7_1053 : sub7 [2, -3, 7] = true := by decide +kernel
theorem sub7_1054 : sub7 [2, -2, -9] = true := by decide +kernel
theorem sub7_1055 : sub7 [2, -2, -8] = true := by decide +kernel
theorem sb7_32 : ∀ q ∈ blk7_32, sub7 q = true := by
  unfold blk7_32
  exact List.forall_mem_cons.2 ⟨sub7_1024, List.forall_mem_cons.2 ⟨sub7_1025, List.forall_mem_cons.2 ⟨sub7_1026, List.forall_mem_cons.2 ⟨sub7_1027, List.forall_mem_cons.2 ⟨sub7_1028, List.forall_mem_cons.2 ⟨sub7_1029, List.forall_mem_cons.2 ⟨sub7_1030, List.forall_mem_cons.2 ⟨sub7_1031, List.forall_mem_cons.2 ⟨sub7_1032, List.forall_mem_cons.2 ⟨sub7_1033, List.forall_mem_cons.2 ⟨sub7_1034, List.forall_mem_cons.2 ⟨sub7_1035, List.forall_mem_cons.2 ⟨sub7_1036, List.forall_mem_cons.2 ⟨sub7_1037, List.forall_mem_cons.2 ⟨sub7_1038, List.forall_mem_cons.2 ⟨sub7_1039, List.forall_mem_cons.2 ⟨sub7_1040, List.forall_mem_cons.2 ⟨sub7_1041, List.forall_mem_cons.2 ⟨sub7_1042, List.forall_mem_cons.2 ⟨sub7_1043, List.forall_mem_cons.2 ⟨sub7_1044, List.forall_mem_cons.2 ⟨sub7_1045, List.forall_mem_cons.2 ⟨sub7_1046, List.forall_mem_cons.2 ⟨sub7_1047, List.forall_mem_cons.2 ⟨sub7_1048, List.forall_mem_cons.2 ⟨sub7_1049, List.forall_mem_cons.2 ⟨sub7_1050, List.forall_mem_cons.2 ⟨sub7_1051, List.forall_mem_cons.2 ⟨sub7_1052, List.forall_mem_cons.2 ⟨sub7_1053, List.forall_mem_cons.2 ⟨sub7_1054, List.forall_mem_cons.2 ⟨sub7_1055, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_1056 : sub7 [2, -2, -7] = true := by decide +kernel
theorem sub7_1057 : sub7 [2, -2, -6] = true := by decide +kernel
theorem sub7_1058 : sub7 [2, -2, -5] = true := by decide +kernel
theorem sub7_1059 : sub7 [2, -2, -4] = true := by decide +kernel
theorem sub7_1060 : sub7 [2, -2, -3] = true := by decide +kernel
theorem sub7_1061 : sub7 [2, -2, -2] = true := by decide +kernel
theorem sub7_1062 : sub7 [2, -2, -1] = true := by decide +kernel
theorem sub7_1063 : sub7 [2, -2, 0] = true := by decide +kernel
theorem sub7_1064 : sub7 [2, -2, 1] = true := by decide +kernel
theorem sub7_1065 : sub7 [2, -2, 2] = true := by decide +kernel
theorem sub7_1066 : sub7 [2, -2, 3] = true := by decide +kernel
theorem sub7_1067 : sub7 [2, -2, 4] = true := by decide +kernel
theorem sub7_1068 : sub7 [2, -2, 5] = true := by decide +kernel
theorem sub7_1069 : sub7 [2, -2, 6] = true := by decide +kernel
theorem sub7_1070 : sub7 [2, -2, 7] = true := by decide +kernel
theorem sub7_1071 : sub7 [2, -2, 8] = true := by decide +kernel
theorem sub7_1072 : sub7 [2, -1, -9] = true := by decide +kernel
theorem sub7_1073 : sub7 [2, -1, -8] = true := by decide +kernel
theorem sub7_1074 : sub7 [2, -1, -7] = true := by decide +kernel
theorem sub7_1075 : sub7 [2, -1, -6] = true := by decide +kernel
theorem sub7_1076 : sub7 [2, -1, -5] = true := by decide +kernel
theorem sub7_1077 : sub7 [2, -1, -4] = true := by decide +kernel
theorem sub7_1078 : sub7 [2, -1, -3] = true := by decide +kernel
theorem sub7_1079 : sub7 [2, -1, -2] = true := by decide +kernel
theorem sub7_1080 : sub7 [2, -1, -1] = true := by decide +kernel
theorem sub7_1081 : sub7 [2, -1, 0] = true := by decide +kernel
theorem sub7_1082 : sub7 [2, -1, 1] = true := by decide +kernel
theorem sub7_1083 : sub7 [2, -1, 2] = true := by decide +kernel
theorem sub7_1084 : sub7 [2, -1, 3] = true := by decide +kernel
theorem sub7_1085 : sub7 [2, -1, 4] = true := by decide +kernel
theorem sub7_1086 : sub7 [2, -1, 5] = true := by decide +kernel
theorem sub7_1087 : sub7 [2, -1, 6] = true := by decide +kernel
theorem sb7_33 : ∀ q ∈ blk7_33, sub7 q = true := by
  unfold blk7_33
  exact List.forall_mem_cons.2 ⟨sub7_1056, List.forall_mem_cons.2 ⟨sub7_1057, List.forall_mem_cons.2 ⟨sub7_1058, List.forall_mem_cons.2 ⟨sub7_1059, List.forall_mem_cons.2 ⟨sub7_1060, List.forall_mem_cons.2 ⟨sub7_1061, List.forall_mem_cons.2 ⟨sub7_1062, List.forall_mem_cons.2 ⟨sub7_1063, List.forall_mem_cons.2 ⟨sub7_1064, List.forall_mem_cons.2 ⟨sub7_1065, List.forall_mem_cons.2 ⟨sub7_1066, List.forall_mem_cons.2 ⟨sub7_1067, List.forall_mem_cons.2 ⟨sub7_1068, List.forall_mem_cons.2 ⟨sub7_1069, List.forall_mem_cons.2 ⟨sub7_1070, List.forall_mem_cons.2 ⟨sub7_1071, List.forall_mem_cons.2 ⟨sub7_1072, List.forall_mem_cons.2 ⟨sub7_1073, List.forall_mem_cons.2 ⟨sub7_1074, List.forall_mem_cons.2 ⟨sub7_1075, List.forall_mem_cons.2 ⟨sub7_1076, List.forall_mem_cons.2 ⟨sub7_1077, List.forall_mem_cons.2 ⟨sub7_1078, List.forall_mem_cons.2 ⟨sub7_1079, List.forall_mem_cons.2 ⟨sub7_1080, List.forall_mem_cons.2 ⟨sub7_1081, List.forall_mem_cons.2 ⟨sub7_1082, List.forall_mem_cons.2 ⟨sub7_1083, List.forall_mem_cons.2 ⟨sub7_1084, List.forall_mem_cons.2 ⟨sub7_1085, List.forall_mem_cons.2 ⟨sub7_1086, List.forall_mem_cons.2 ⟨sub7_1087, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_1088 : sub7 [2, -1, 7] = true := by decide +kernel
theorem sub7_1089 : sub7 [2, -1, 8] = true := by decide +kernel
theorem sub7_1090 : sub7 [2, -1, 9] = true := by decide +kernel
theorem sub7_1091 : sub7 [2, 0, -9] = true := by decide +kernel
theorem sub7_1092 : sub7 [2, 0, -8] = true := by decide +kernel
theorem sub7_1093 : sub7 [2, 0, -7] = true := by decide +kernel
theorem sub7_1094 : sub7 [2, 0, -6] = true := by decide +kernel
theorem sub7_1095 : sub7 [2, 0, -5] = true := by decide +kernel
theorem sub7_1096 : sub7 [2, 0, -4] = true := by decide +kernel
theorem sub7_1097 : sub7 [2, 0, -3] = true := by decide +kernel
theorem sub7_1098 : sub7 [2, 0, -2] = true := by decide +kernel
theorem sub7_1099 : sub7 [2, 0, -1] = true := by decide +kernel
theorem sub7_1100 : sub7 [2, 0, 0] = true := by decide +kernel
theorem sub7_1101 : sub7 [2, 0, 1] = true := by decide +kernel
theorem sub7_1102 : sub7 [2, 0, 2] = true := by decide +kernel
theorem sub7_1103 : sub7 [2, 0, 3] = true := by decide +kernel
theorem sub7_1104 : sub7 [2, 0, 4] = true := by decide +kernel
theorem sub7_1105 : sub7 [2, 0, 5] = true := by decide +kernel
theorem sub7_1106 : sub7 [2, 0, 6] = true := by decide +kernel
theorem sub7_1107 : sub7 [2, 0, 7] = true := by decide +kernel
theorem sub7_1108 : sub7 [2, 0, 8] = true := by decide +kernel
theorem sub7_1109 : sub7 [2, 0, 9] = true := by decide +kernel
theorem sub7_1110 : sub7 [2, 1, -9] = true := by decide +kernel
theorem sub7_1111 : sub7 [2, 1, -8] = true := by decide +kernel
theorem sub7_1112 : sub7 [2, 1, -7] = true := by decide +kernel
theorem sub7_1113 : sub7 [2, 1, -6] = true := by decide +kernel
theorem sub7_1114 : sub7 [2, 1, -5] = true := by decide +kernel
theorem sub7_1115 : sub7 [2, 1, -4] = true := by decide +kernel
theorem sub7_1116 : sub7 [2, 1, -3] = true := by decide +kernel
theorem sub7_1117 : sub7 [2, 1, -2] = true := by decide +kernel
theorem sub7_1118 : sub7 [2, 1, -1] = true := by decide +kernel
theorem sub7_1119 : sub7 [2, 1, 0] = true := by decide +kernel
theorem sb7_34 : ∀ q ∈ blk7_34, sub7 q = true := by
  unfold blk7_34
  exact List.forall_mem_cons.2 ⟨sub7_1088, List.forall_mem_cons.2 ⟨sub7_1089, List.forall_mem_cons.2 ⟨sub7_1090, List.forall_mem_cons.2 ⟨sub7_1091, List.forall_mem_cons.2 ⟨sub7_1092, List.forall_mem_cons.2 ⟨sub7_1093, List.forall_mem_cons.2 ⟨sub7_1094, List.forall_mem_cons.2 ⟨sub7_1095, List.forall_mem_cons.2 ⟨sub7_1096, List.forall_mem_cons.2 ⟨sub7_1097, List.forall_mem_cons.2 ⟨sub7_1098, List.forall_mem_cons.2 ⟨sub7_1099, List.forall_mem_cons.2 ⟨sub7_1100, List.forall_mem_cons.2 ⟨sub7_1101, List.forall_mem_cons.2 ⟨sub7_1102, List.forall_mem_cons.2 ⟨sub7_1103, List.forall_mem_cons.2 ⟨sub7_1104, List.forall_mem_cons.2 ⟨sub7_1105, List.forall_mem_cons.2 ⟨sub7_1106, List.forall_mem_cons.2 ⟨sub7_1107, List.forall_mem_cons.2 ⟨sub7_1108, List.forall_mem_cons.2 ⟨sub7_1109, List.forall_mem_cons.2 ⟨sub7_1110, List.forall_mem_cons.2 ⟨sub7_1111, List.forall_mem_cons.2 ⟨sub7_1112, List.forall_mem_cons.2 ⟨sub7_1113, List.forall_mem_cons.2 ⟨sub7_1114, List.forall_mem_cons.2 ⟨sub7_1115, List.forall_mem_cons.2 ⟨sub7_1116, List.forall_mem_cons.2 ⟨sub7_1117, List.forall_mem_cons.2 ⟨sub7_1118, List.forall_mem_cons.2 ⟨sub7_1119, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_1120 : sub7 [2, 1, 1] = true := by decide +kernel
theorem sub7_1121 : sub7 [2, 1, 2] = true := by decide +kernel
theorem sub7_1122 : sub7 [2, 1, 3] = true := by decide +kernel
theorem sub7_1123 : sub7 [2, 1, 4] = true := by decide +kernel
theorem sub7_1124 : sub7 [2, 1, 5] = true := by decide +kernel
theorem sub7_1125 : sub7 [2, 1, 6] = true := by decide +kernel
theorem sub7_1126 : sub7 [2, 1, 7] = true := by decide +kernel
theorem sub7_1127 : sub7 [2, 1, 8] = true := by decide +kernel
theorem sub7_1128 : sub7 [2, 1, 9] = true := by decide +kernel
theorem sub7_1129 : sub7 [2, 2, -9] = true := by decide +kernel
theorem sub7_1130 : sub7 [2, 2, -8] = true := by decide +kernel
theorem sub7_1131 : sub7 [2, 2, -7] = true := by decide +kernel
theorem sub7_1132 : sub7 [2, 2, -6] = true := by decide +kernel
theorem sub7_1133 : sub7 [2, 2, -5] = true := by decide +kernel
theorem sub7_1134 : sub7 [2, 2, -4] = true := by decide +kernel
theorem sub7_1135 : sub7 [2, 2, -3] = true := by decide +kernel
theorem sub7_1136 : sub7 [2, 2, -2] = true := by decide +kernel
theorem sub7_1137 : sub7 [2, 2, -1] = true := by decide +kernel
theorem sub7_1138 : sub7 [2, 2, 0] = true := by decide +kernel
theorem sub7_1139 : sub7 [2, 2, 1] = true := by decide +kernel
theorem sub7_1140 : sub7 [2, 2, 2] = true := by decide +kernel
theorem sub7_1141 : sub7 [2, 2, 3] = true := by decide +kernel
theorem sub7_1142 : sub7 [2, 2, 4] = true := by decide +kernel
theorem sub7_1143 : sub7 [2, 2, 5] = true := by decide +kernel
theorem sub7_1144 : sub7 [2, 2, 6] = true := by decide +kernel
theorem sub7_1145 : sub7 [2, 2, 7] = true := by decide +kernel
theorem sub7_1146 : sub7 [2, 2, 8] = true := by decide +kernel
theorem sub7_1147 : sub7 [2, 2, 9] = true := by decide +kernel
theorem sub7_1148 : sub7 [2, 3, -9] = true := by decide +kernel
theorem sub7_1149 : sub7 [2, 3, -8] = true := by decide +kernel
theorem sub7_1150 : sub7 [2, 3, -7] = true := by decide +kernel
theorem sub7_1151 : sub7 [2, 3, -6] = true := by decide +kernel
theorem sb7_35 : ∀ q ∈ blk7_35, sub7 q = true := by
  unfold blk7_35
  exact List.forall_mem_cons.2 ⟨sub7_1120, List.forall_mem_cons.2 ⟨sub7_1121, List.forall_mem_cons.2 ⟨sub7_1122, List.forall_mem_cons.2 ⟨sub7_1123, List.forall_mem_cons.2 ⟨sub7_1124, List.forall_mem_cons.2 ⟨sub7_1125, List.forall_mem_cons.2 ⟨sub7_1126, List.forall_mem_cons.2 ⟨sub7_1127, List.forall_mem_cons.2 ⟨sub7_1128, List.forall_mem_cons.2 ⟨sub7_1129, List.forall_mem_cons.2 ⟨sub7_1130, List.forall_mem_cons.2 ⟨sub7_1131, List.forall_mem_cons.2 ⟨sub7_1132, List.forall_mem_cons.2 ⟨sub7_1133, List.forall_mem_cons.2 ⟨sub7_1134, List.forall_mem_cons.2 ⟨sub7_1135, List.forall_mem_cons.2 ⟨sub7_1136, List.forall_mem_cons.2 ⟨sub7_1137, List.forall_mem_cons.2 ⟨sub7_1138, List.forall_mem_cons.2 ⟨sub7_1139, List.forall_mem_cons.2 ⟨sub7_1140, List.forall_mem_cons.2 ⟨sub7_1141, List.forall_mem_cons.2 ⟨sub7_1142, List.forall_mem_cons.2 ⟨sub7_1143, List.forall_mem_cons.2 ⟨sub7_1144, List.forall_mem_cons.2 ⟨sub7_1145, List.forall_mem_cons.2 ⟨sub7_1146, List.forall_mem_cons.2 ⟨sub7_1147, List.forall_mem_cons.2 ⟨sub7_1148, List.forall_mem_cons.2 ⟨sub7_1149, List.forall_mem_cons.2 ⟨sub7_1150, List.forall_mem_cons.2 ⟨sub7_1151, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_1152 : sub7 [2, 3, -5] = true := by decide +kernel
theorem sub7_1153 : sub7 [2, 3, -4] = true := by decide +kernel
theorem sub7_1154 : sub7 [2, 3, -3] = true := by decide +kernel
theorem sub7_1155 : sub7 [2, 3, -2] = true := by decide +kernel
theorem sub7_1156 : sub7 [2, 3, -1] = true := by decide +kernel
theorem sub7_1157 : sub7 [2, 3, 0] = true := by decide +kernel
theorem sub7_1158 : sub7 [2, 3, 1] = true := by decide +kernel
theorem sub7_1159 : sub7 [2, 3, 2] = true := by decide +kernel
theorem sub7_1160 : sub7 [2, 3, 3] = true := by decide +kernel
theorem sub7_1161 : sub7 [2, 3, 4] = true := by decide +kernel
theorem sub7_1162 : sub7 [2, 3, 5] = true := by decide +kernel
theorem sub7_1163 : sub7 [2, 3, 6] = true := by decide +kernel
theorem sub7_1164 : sub7 [2, 3, 7] = true := by decide +kernel
theorem sub7_1165 : sub7 [2, 3, 8] = true := by decide +kernel
theorem sub7_1166 : sub7 [2, 3, 9] = true := by decide +kernel
theorem sub7_1167 : sub7 [2, 4, -8] = true := by decide +kernel
theorem sub7_1168 : sub7 [2, 4, -7] = true := by decide +kernel
theorem sub7_1169 : sub7 [2, 4, -6] = true := by decide +kernel
theorem sub7_1170 : sub7 [2, 4, -5] = true := by decide +kernel
theorem sub7_1171 : sub7 [2, 4, -4] = true := by decide +kernel
theorem sub7_1172 : sub7 [2, 4, -3] = true := by decide +kernel
theorem sub7_1173 : sub7 [2, 4, -2] = true := by decide +kernel
theorem sub7_1174 : sub7 [2, 4, -1] = true := by decide +kernel
theorem sub7_1175 : sub7 [2, 4, 0] = true := by decide +kernel
theorem sub7_1176 : sub7 [2, 4, 1] = true := by decide +kernel
theorem sub7_1177 : sub7 [2, 4, 2] = true := by decide +kernel
theorem sub7_1178 : sub7 [2, 4, 3] = true := by decide +kernel
theorem sub7_1179 : sub7 [2, 4, 4] = true := by decide +kernel
theorem sub7_1180 : sub7 [2, 4, 5] = true := by decide +kernel
theorem sub7_1181 : sub7 [2, 4, 6] = true := by decide +kernel
theorem sub7_1182 : sub7 [2, 4, 7] = true := by decide +kernel
theorem sub7_1183 : sub7 [2, 4, 8] = true := by decide +kernel
theorem sb7_36 : ∀ q ∈ blk7_36, sub7 q = true := by
  unfold blk7_36
  exact List.forall_mem_cons.2 ⟨sub7_1152, List.forall_mem_cons.2 ⟨sub7_1153, List.forall_mem_cons.2 ⟨sub7_1154, List.forall_mem_cons.2 ⟨sub7_1155, List.forall_mem_cons.2 ⟨sub7_1156, List.forall_mem_cons.2 ⟨sub7_1157, List.forall_mem_cons.2 ⟨sub7_1158, List.forall_mem_cons.2 ⟨sub7_1159, List.forall_mem_cons.2 ⟨sub7_1160, List.forall_mem_cons.2 ⟨sub7_1161, List.forall_mem_cons.2 ⟨sub7_1162, List.forall_mem_cons.2 ⟨sub7_1163, List.forall_mem_cons.2 ⟨sub7_1164, List.forall_mem_cons.2 ⟨sub7_1165, List.forall_mem_cons.2 ⟨sub7_1166, List.forall_mem_cons.2 ⟨sub7_1167, List.forall_mem_cons.2 ⟨sub7_1168, List.forall_mem_cons.2 ⟨sub7_1169, List.forall_mem_cons.2 ⟨sub7_1170, List.forall_mem_cons.2 ⟨sub7_1171, List.forall_mem_cons.2 ⟨sub7_1172, List.forall_mem_cons.2 ⟨sub7_1173, List.forall_mem_cons.2 ⟨sub7_1174, List.forall_mem_cons.2 ⟨sub7_1175, List.forall_mem_cons.2 ⟨sub7_1176, List.forall_mem_cons.2 ⟨sub7_1177, List.forall_mem_cons.2 ⟨sub7_1178, List.forall_mem_cons.2 ⟨sub7_1179, List.forall_mem_cons.2 ⟨sub7_1180, List.forall_mem_cons.2 ⟨sub7_1181, List.forall_mem_cons.2 ⟨sub7_1182, List.forall_mem_cons.2 ⟨sub7_1183, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_1184 : sub7 [2, 4, 9] = true := by decide +kernel
theorem sub7_1185 : sub7 [2, 5, -7] = true := by decide +kernel
theorem sub7_1186 : sub7 [2, 5, -6] = true := by decide +kernel
theorem sub7_1187 : sub7 [2, 5, -5] = true := by decide +kernel
theorem sub7_1188 : sub7 [2, 5, -4] = true := by decide +kernel
theorem sub7_1189 : sub7 [2, 5, -3] = true := by decide +kernel
theorem sub7_1190 : sub7 [2, 5, -2] = true := by decide +kernel
theorem sub7_1191 : sub7 [2, 5, -1] = true := by decide +kernel
theorem sub7_1192 : sub7 [2, 5, 0] = true := by decide +kernel
theorem sub7_1193 : sub7 [2, 5, 1] = true := by decide +kernel
theorem sub7_1194 : sub7 [2, 5, 2] = true := by decide +kernel
theorem sub7_1195 : sub7 [2, 5, 3] = true := by decide +kernel
theorem sub7_1196 : sub7 [2, 5, 4] = true := by decide +kernel
theorem sub7_1197 : sub7 [2, 5, 5] = true := by decide +kernel
theorem sub7_1198 : sub7 [2, 5, 6] = true := by decide +kernel
theorem sub7_1199 : sub7 [2, 5, 7] = true := by decide +kernel
theorem sub7_1200 : sub7 [2, 5, 8] = true := by decide +kernel
theorem sub7_1201 : sub7 [2, 6] = true := by decide +kernel
theorem sub7_1202 : sub7 [2, 7] = true := by decide +kernel
theorem sub7_1203 : sub7 [2, 8] = true := by decide +kernel
theorem sub7_1204 : sub7 [3, -6] = true := by decide +kernel
theorem sub7_1205 : sub7 [3, -5] = true := by decide +kernel
theorem sub7_1206 : sub7 [3, -4] = true := by decide +kernel
theorem sub7_1207 : sub7 [3, -3] = true := by decide +kernel
theorem sub7_1208 : sub7 [3, -2, -8] = true := by decide +kernel
theorem sub7_1209 : sub7 [3, -2, -7] = true := by decide +kernel
theorem sub7_1210 : sub7 [3, -2, -6] = true := by decide +kernel
theorem sub7_1211 : sub7 [3, -2, -5] = true := by decide +kernel
theorem sub7_1212 : sub7 [3, -2, -4] = true := by decide +kernel
theorem sub7_1213 : sub7 [3, -2, -3] = true := by decide +kernel
theorem sub7_1214 : sub7 [3, -2, -2] = true := by decide +kernel
theorem sub7_1215 : sub7 [3, -2, -1] = true := by decide +kernel
theorem sb7_37 : ∀ q ∈ blk7_37, sub7 q = true := by
  unfold blk7_37
  exact List.forall_mem_cons.2 ⟨sub7_1184, List.forall_mem_cons.2 ⟨sub7_1185, List.forall_mem_cons.2 ⟨sub7_1186, List.forall_mem_cons.2 ⟨sub7_1187, List.forall_mem_cons.2 ⟨sub7_1188, List.forall_mem_cons.2 ⟨sub7_1189, List.forall_mem_cons.2 ⟨sub7_1190, List.forall_mem_cons.2 ⟨sub7_1191, List.forall_mem_cons.2 ⟨sub7_1192, List.forall_mem_cons.2 ⟨sub7_1193, List.forall_mem_cons.2 ⟨sub7_1194, List.forall_mem_cons.2 ⟨sub7_1195, List.forall_mem_cons.2 ⟨sub7_1196, List.forall_mem_cons.2 ⟨sub7_1197, List.forall_mem_cons.2 ⟨sub7_1198, List.forall_mem_cons.2 ⟨sub7_1199, List.forall_mem_cons.2 ⟨sub7_1200, List.forall_mem_cons.2 ⟨sub7_1201, List.forall_mem_cons.2 ⟨sub7_1202, List.forall_mem_cons.2 ⟨sub7_1203, List.forall_mem_cons.2 ⟨sub7_1204, List.forall_mem_cons.2 ⟨sub7_1205, List.forall_mem_cons.2 ⟨sub7_1206, List.forall_mem_cons.2 ⟨sub7_1207, List.forall_mem_cons.2 ⟨sub7_1208, List.forall_mem_cons.2 ⟨sub7_1209, List.forall_mem_cons.2 ⟨sub7_1210, List.forall_mem_cons.2 ⟨sub7_1211, List.forall_mem_cons.2 ⟨sub7_1212, List.forall_mem_cons.2 ⟨sub7_1213, List.forall_mem_cons.2 ⟨sub7_1214, List.forall_mem_cons.2 ⟨sub7_1215, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_1216 : sub7 [3, -2, 0] = true := by decide +kernel
theorem sub7_1217 : sub7 [3, -2, 1] = true := by decide +kernel
theorem sub7_1218 : sub7 [3, -2, 2] = true := by decide +kernel
theorem sub7_1219 : sub7 [3, -2, 3] = true := by decide +kernel
theorem sub7_1220 : sub7 [3, -2, 4] = true := by decide +kernel
theorem sub7_1221 : sub7 [3, -2, 5] = true := by decide +kernel
theorem sub7_1222 : sub7 [3, -2, 6] = true := by decide +kernel
theorem sub7_1223 : sub7 [3, -2, 7] = true := by decide +kernel
theorem sub7_1224 : sub7 [3, -1, -8] = true := by decide +kernel
theorem sub7_1225 : sub7 [3, -1, -7] = true := by decide +kernel
theorem sub7_1226 : sub7 [3, -1, -6] = true := by decide +kernel
theorem sub7_1227 : sub7 [3, -1, -5] = true := by decide +kernel
theorem sub7_1228 : sub7 [3, -1, -4] = true := by decide +kernel
theorem sub7_1229 : sub7 [3, -1, -3] = true := by decide +kernel
theorem sub7_1230 : sub7 [3, -1, -2] = true := by decide +kernel
theorem sub7_1231 : sub7 [3, -1, -1] = true := by decide +kernel
theorem sub7_1232 : sub7 [3, -1, 0] = true := by decide +kernel
theorem sub7_1233 : sub7 [3, -1, 1] = true := by decide +kernel
theorem sub7_1234 : sub7 [3, -1, 2] = true := by decide +kernel
theorem sub7_1235 : sub7 [3, -1, 3] = true := by decide +kernel
theorem sub7_1236 : sub7 [3, -1, 4] = true := by decide +kernel
theorem sub7_1237 : sub7 [3, -1, 5] = true := by decide +kernel
theorem sub7_1238 : sub7 [3, -1, 6] = true := by decide +kernel
theorem sub7_1239 : sub7 [3, -1, 7] = true := by decide +kernel
theorem sub7_1240 : sub7 [3, -1, 8] = true := by decide +kernel
theorem sub7_1241 : sub7 [3, 0, -8] = true := by decide +kernel
theorem sub7_1242 : sub7 [3, 0, -7] = true := by decide +kernel
theorem sub7_1243 : sub7 [3, 0, -6] = true := by decide +kernel
theorem sub7_1244 : sub7 [3, 0, -5] = true := by decide +kernel
theorem sub7_1245 : sub7 [3, 0, -4] = true := by decide +kernel
theorem sub7_1246 : sub7 [3, 0, -3] = true := by decide +kernel
theorem sub7_1247 : sub7 [3, 0, -2] = true := by decide +kernel
theorem sb7_38 : ∀ q ∈ blk7_38, sub7 q = true := by
  unfold blk7_38
  exact List.forall_mem_cons.2 ⟨sub7_1216, List.forall_mem_cons.2 ⟨sub7_1217, List.forall_mem_cons.2 ⟨sub7_1218, List.forall_mem_cons.2 ⟨sub7_1219, List.forall_mem_cons.2 ⟨sub7_1220, List.forall_mem_cons.2 ⟨sub7_1221, List.forall_mem_cons.2 ⟨sub7_1222, List.forall_mem_cons.2 ⟨sub7_1223, List.forall_mem_cons.2 ⟨sub7_1224, List.forall_mem_cons.2 ⟨sub7_1225, List.forall_mem_cons.2 ⟨sub7_1226, List.forall_mem_cons.2 ⟨sub7_1227, List.forall_mem_cons.2 ⟨sub7_1228, List.forall_mem_cons.2 ⟨sub7_1229, List.forall_mem_cons.2 ⟨sub7_1230, List.forall_mem_cons.2 ⟨sub7_1231, List.forall_mem_cons.2 ⟨sub7_1232, List.forall_mem_cons.2 ⟨sub7_1233, List.forall_mem_cons.2 ⟨sub7_1234, List.forall_mem_cons.2 ⟨sub7_1235, List.forall_mem_cons.2 ⟨sub7_1236, List.forall_mem_cons.2 ⟨sub7_1237, List.forall_mem_cons.2 ⟨sub7_1238, List.forall_mem_cons.2 ⟨sub7_1239, List.forall_mem_cons.2 ⟨sub7_1240, List.forall_mem_cons.2 ⟨sub7_1241, List.forall_mem_cons.2 ⟨sub7_1242, List.forall_mem_cons.2 ⟨sub7_1243, List.forall_mem_cons.2 ⟨sub7_1244, List.forall_mem_cons.2 ⟨sub7_1245, List.forall_mem_cons.2 ⟨sub7_1246, List.forall_mem_cons.2 ⟨sub7_1247, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_1248 : sub7 [3, 0, -1] = true := by decide +kernel
theorem sub7_1249 : sub7 [3, 0, 0] = true := by decide +kernel
theorem sub7_1250 : sub7 [3, 0, 1] = true := by decide +kernel
theorem sub7_1251 : sub7 [3, 0, 2] = true := by decide +kernel
theorem sub7_1252 : sub7 [3, 0, 3] = true := by decide +kernel
theorem sub7_1253 : sub7 [3, 0, 4] = true := by decide +kernel
theorem sub7_1254 : sub7 [3, 0, 5] = true := by decide +kernel
theorem sub7_1255 : sub7 [3, 0, 6] = true := by decide +kernel
theorem sub7_1256 : sub7 [3, 0, 7] = true := by decide +kernel
theorem sub7_1257 : sub7 [3, 0, 8] = true := by decide +kernel
theorem sub7_1258 : sub7 [3, 0, 9] = true := by decide +kernel
theorem sub7_1259 : sub7 [3, 1, -9] = true := by decide +kernel
theorem sub7_1260 : sub7 [3, 1, -8] = true := by decide +kernel
theorem sub7_1261 : sub7 [3, 1, -7] = true := by decide +kernel
theorem sub7_1262 : sub7 [3, 1, -6] = true := by decide +kernel
theorem sub7_1263 : sub7 [3, 1, -5] = true := by decide +kernel
theorem sub7_1264 : sub7 [3, 1, -4] = true := by decide +kernel
theorem sub7_1265 : sub7 [3, 1, -3] = true := by decide +kernel
theorem sub7_1266 : sub7 [3, 1, -2] = true := by decide +kernel
theorem sub7_1267 : sub7 [3, 1, -1] = true := by decide +kernel
theorem sub7_1268 : sub7 [3, 1, 0] = true := by decide +kernel
theorem sub7_1269 : sub7 [3, 1, 1] = true := by decide +kernel
theorem sub7_1270 : sub7 [3, 1, 2] = true := by decide +kernel
theorem sub7_1271 : sub7 [3, 1, 3] = true := by decide +kernel
theorem sub7_1272 : sub7 [3, 1, 4] = true := by decide +kernel
theorem sub7_1273 : sub7 [3, 1, 5] = true := by decide +kernel
theorem sub7_1274 : sub7 [3, 1, 6] = true := by decide +kernel
theorem sub7_1275 : sub7 [3, 1, 7] = true := by decide +kernel
theorem sub7_1276 : sub7 [3, 1, 8] = true := by decide +kernel
theorem sub7_1277 : sub7 [3, 1, 9] = true := by decide +kernel
theorem sub7_1278 : sub7 [3, 2, -8] = true := by decide +kernel
theorem sub7_1279 : sub7 [3, 2, -7] = true := by decide +kernel
theorem sb7_39 : ∀ q ∈ blk7_39, sub7 q = true := by
  unfold blk7_39
  exact List.forall_mem_cons.2 ⟨sub7_1248, List.forall_mem_cons.2 ⟨sub7_1249, List.forall_mem_cons.2 ⟨sub7_1250, List.forall_mem_cons.2 ⟨sub7_1251, List.forall_mem_cons.2 ⟨sub7_1252, List.forall_mem_cons.2 ⟨sub7_1253, List.forall_mem_cons.2 ⟨sub7_1254, List.forall_mem_cons.2 ⟨sub7_1255, List.forall_mem_cons.2 ⟨sub7_1256, List.forall_mem_cons.2 ⟨sub7_1257, List.forall_mem_cons.2 ⟨sub7_1258, List.forall_mem_cons.2 ⟨sub7_1259, List.forall_mem_cons.2 ⟨sub7_1260, List.forall_mem_cons.2 ⟨sub7_1261, List.forall_mem_cons.2 ⟨sub7_1262, List.forall_mem_cons.2 ⟨sub7_1263, List.forall_mem_cons.2 ⟨sub7_1264, List.forall_mem_cons.2 ⟨sub7_1265, List.forall_mem_cons.2 ⟨sub7_1266, List.forall_mem_cons.2 ⟨sub7_1267, List.forall_mem_cons.2 ⟨sub7_1268, List.forall_mem_cons.2 ⟨sub7_1269, List.forall_mem_cons.2 ⟨sub7_1270, List.forall_mem_cons.2 ⟨sub7_1271, List.forall_mem_cons.2 ⟨sub7_1272, List.forall_mem_cons.2 ⟨sub7_1273, List.forall_mem_cons.2 ⟨sub7_1274, List.forall_mem_cons.2 ⟨sub7_1275, List.forall_mem_cons.2 ⟨sub7_1276, List.forall_mem_cons.2 ⟨sub7_1277, List.forall_mem_cons.2 ⟨sub7_1278, List.forall_mem_cons.2 ⟨sub7_1279, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_1280 : sub7 [3, 2, -6] = true := by decide +kernel
theorem sub7_1281 : sub7 [3, 2, -5] = true := by decide +kernel
theorem sub7_1282 : sub7 [3, 2, -4] = true := by decide +kernel
theorem sub7_1283 : sub7 [3, 2, -3] = true := by decide +kernel
theorem sub7_1284 : sub7 [3, 2, -2] = true := by decide +kernel
theorem sub7_1285 : sub7 [3, 2, -1] = true := by decide +kernel
theorem sub7_1286 : sub7 [3, 2, 0] = true := by decide +kernel
theorem sub7_1287 : sub7 [3, 2, 1] = true := by decide +kernel
theorem sub7_1288 : sub7 [3, 2, 2] = true := by decide +kernel
theorem sub7_1289 : sub7 [3, 2, 3] = true := by decide +kernel
theorem sub7_1290 : sub7 [3, 2, 4] = true := by decide +kernel
theorem sub7_1291 : sub7 [3, 2, 5] = true := by decide +kernel
theorem sub7_1292 : sub7 [3, 2, 6] = true := by decide +kernel
theorem sub7_1293 : sub7 [3, 2, 7] = true := by decide +kernel
theorem sub7_1294 : sub7 [3, 2, 8] = true := by decide +kernel
theorem sub7_1295 : sub7 [3, 2, 9] = true := by decide +kernel
theorem sub7_1296 : sub7 [3, 3, -8] = true := by decide +kernel
theorem sub7_1297 : sub7 [3, 3, -7] = true := by decide +kernel
theorem sub7_1298 : sub7 [3, 3, -6] = true := by decide +kernel
theorem sub7_1299 : sub7 [3, 3, -5] = true := by decide +kernel
theorem sub7_1300 : sub7 [3, 3, -4] = true := by decide +kernel
theorem sub7_1301 : sub7 [3, 3, -3] = true := by decide +kernel
theorem sub7_1302 : sub7 [3, 3, -2] = true := by decide +kernel
theorem sub7_1303 : sub7 [3, 3, -1] = true := by decide +kernel
theorem sub7_1304 : sub7 [3, 3, 0] = true := by decide +kernel
theorem sub7_1305 : sub7 [3, 3, 1] = true := by decide +kernel
theorem sub7_1306 : sub7 [3, 3, 2] = true := by decide +kernel
theorem sub7_1307 : sub7 [3, 3, 3] = true := by decide +kernel
theorem sub7_1308 : sub7 [3, 3, 4] = true := by decide +kernel
theorem sub7_1309 : sub7 [3, 3, 5] = true := by decide +kernel
theorem sub7_1310 : sub7 [3, 3, 6] = true := by decide +kernel
theorem sub7_1311 : sub7 [3, 3, 7] = true := by decide +kernel
theorem sb7_40 : ∀ q ∈ blk7_40, sub7 q = true := by
  unfold blk7_40
  exact List.forall_mem_cons.2 ⟨sub7_1280, List.forall_mem_cons.2 ⟨sub7_1281, List.forall_mem_cons.2 ⟨sub7_1282, List.forall_mem_cons.2 ⟨sub7_1283, List.forall_mem_cons.2 ⟨sub7_1284, List.forall_mem_cons.2 ⟨sub7_1285, List.forall_mem_cons.2 ⟨sub7_1286, List.forall_mem_cons.2 ⟨sub7_1287, List.forall_mem_cons.2 ⟨sub7_1288, List.forall_mem_cons.2 ⟨sub7_1289, List.forall_mem_cons.2 ⟨sub7_1290, List.forall_mem_cons.2 ⟨sub7_1291, List.forall_mem_cons.2 ⟨sub7_1292, List.forall_mem_cons.2 ⟨sub7_1293, List.forall_mem_cons.2 ⟨sub7_1294, List.forall_mem_cons.2 ⟨sub7_1295, List.forall_mem_cons.2 ⟨sub7_1296, List.forall_mem_cons.2 ⟨sub7_1297, List.forall_mem_cons.2 ⟨sub7_1298, List.forall_mem_cons.2 ⟨sub7_1299, List.forall_mem_cons.2 ⟨sub7_1300, List.forall_mem_cons.2 ⟨sub7_1301, List.forall_mem_cons.2 ⟨sub7_1302, List.forall_mem_cons.2 ⟨sub7_1303, List.forall_mem_cons.2 ⟨sub7_1304, List.forall_mem_cons.2 ⟨sub7_1305, List.forall_mem_cons.2 ⟨sub7_1306, List.forall_mem_cons.2 ⟨sub7_1307, List.forall_mem_cons.2 ⟨sub7_1308, List.forall_mem_cons.2 ⟨sub7_1309, List.forall_mem_cons.2 ⟨sub7_1310, List.forall_mem_cons.2 ⟨sub7_1311, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_1312 : sub7 [3, 3, 8] = true := by decide +kernel
theorem sub7_1313 : sub7 [3, 3, 9] = true := by decide +kernel
theorem sub7_1314 : sub7 [3, 4, -8] = true := by decide +kernel
theorem sub7_1315 : sub7 [3, 4, -7] = true := by decide +kernel
theorem sub7_1316 : sub7 [3, 4, -6] = true := by decide +kernel
theorem sub7_1317 : sub7 [3, 4, -5] = true := by decide +kernel
theorem sub7_1318 : sub7 [3, 4, -4] = true := by decide +kernel
theorem sub7_1319 : sub7 [3, 4, -3] = true := by decide +kernel
theorem sub7_1320 : sub7 [3, 4, -2] = true := by decide +kernel
theorem sub7_1321 : sub7 [3, 4, -1] = true := by decide +kernel
theorem sub7_1322 : sub7 [3, 4, 0] = true := by decide +kernel
theorem sub7_1323 : sub7 [3, 4, 1] = true := by decide +kernel
theorem sub7_1324 : sub7 [3, 4, 2] = true := by decide +kernel
theorem sub7_1325 : sub7 [3, 4, 3] = true := by decide +kernel
theorem sub7_1326 : sub7 [3, 4, 4] = true := by decide +kernel
theorem sub7_1327 : sub7 [3, 4, 5] = true := by decide +kernel
theorem sub7_1328 : sub7 [3, 4, 6] = true := by decide +kernel
theorem sub7_1329 : sub7 [3, 4, 7] = true := by decide +kernel
theorem sub7_1330 : sub7 [3, 4, 8] = true := by decide +kernel
theorem sub7_1331 : sub7 [3, 4, 9] = true := by decide +kernel
theorem sub7_1332 : sub7 [3, 5, -7] = true := by decide +kernel
theorem sub7_1333 : sub7 [3, 5, -6] = true := by decide +kernel
theorem sub7_1334 : sub7 [3, 5, -5] = true := by decide +kernel
theorem sub7_1335 : sub7 [3, 5, -4] = true := by decide +kernel
theorem sub7_1336 : sub7 [3, 5, -3] = true := by decide +kernel
theorem sub7_1337 : sub7 [3, 5, -2] = true := by decide +kernel
theorem sub7_1338 : sub7 [3, 5, -1] = true := by decide +kernel
theorem sub7_1339 : sub7 [3, 5, 0] = true := by decide +kernel
theorem sub7_1340 : sub7 [3, 5, 1] = true := by decide +kernel
theorem sub7_1341 : sub7 [3, 5, 2] = true := by decide +kernel
theorem sub7_1342 : sub7 [3, 5, 3] = true := by decide +kernel
theorem sub7_1343 : sub7 [3, 5, 4] = true := by decide +kernel
theorem sb7_41 : ∀ q ∈ blk7_41, sub7 q = true := by
  unfold blk7_41
  exact List.forall_mem_cons.2 ⟨sub7_1312, List.forall_mem_cons.2 ⟨sub7_1313, List.forall_mem_cons.2 ⟨sub7_1314, List.forall_mem_cons.2 ⟨sub7_1315, List.forall_mem_cons.2 ⟨sub7_1316, List.forall_mem_cons.2 ⟨sub7_1317, List.forall_mem_cons.2 ⟨sub7_1318, List.forall_mem_cons.2 ⟨sub7_1319, List.forall_mem_cons.2 ⟨sub7_1320, List.forall_mem_cons.2 ⟨sub7_1321, List.forall_mem_cons.2 ⟨sub7_1322, List.forall_mem_cons.2 ⟨sub7_1323, List.forall_mem_cons.2 ⟨sub7_1324, List.forall_mem_cons.2 ⟨sub7_1325, List.forall_mem_cons.2 ⟨sub7_1326, List.forall_mem_cons.2 ⟨sub7_1327, List.forall_mem_cons.2 ⟨sub7_1328, List.forall_mem_cons.2 ⟨sub7_1329, List.forall_mem_cons.2 ⟨sub7_1330, List.forall_mem_cons.2 ⟨sub7_1331, List.forall_mem_cons.2 ⟨sub7_1332, List.forall_mem_cons.2 ⟨sub7_1333, List.forall_mem_cons.2 ⟨sub7_1334, List.forall_mem_cons.2 ⟨sub7_1335, List.forall_mem_cons.2 ⟨sub7_1336, List.forall_mem_cons.2 ⟨sub7_1337, List.forall_mem_cons.2 ⟨sub7_1338, List.forall_mem_cons.2 ⟨sub7_1339, List.forall_mem_cons.2 ⟨sub7_1340, List.forall_mem_cons.2 ⟨sub7_1341, List.forall_mem_cons.2 ⟨sub7_1342, List.forall_mem_cons.2 ⟨sub7_1343, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_1344 : sub7 [3, 5, 5] = true := by decide +kernel
theorem sub7_1345 : sub7 [3, 5, 6] = true := by decide +kernel
theorem sub7_1346 : sub7 [3, 5, 7] = true := by decide +kernel
theorem sub7_1347 : sub7 [3, 5, 8] = true := by decide +kernel
theorem sub7_1348 : sub7 [3, 6] = true := by decide +kernel
theorem sub7_1349 : sub7 [3, 7] = true := by decide +kernel
theorem sub7_1350 : sub7 [3, 8] = true := by decide +kernel
theorem sub7_1351 : sub7 [4, -5] = true := by decide +kernel
theorem sub7_1352 : sub7 [4, -4] = true := by decide +kernel
theorem sub7_1353 : sub7 [4, -3] = true := by decide +kernel
theorem sub7_1354 : sub7 [4, -2] = true := by decide +kernel
theorem sub7_1355 : sub7 [4, -1] = true := by decide +kernel
theorem sub7_1356 : sub7 [4, 0, -8] = true := by decide +kernel
theorem sub7_1357 : sub7 [4, 0, -7] = true := by decide +kernel
theorem sub7_1358 : sub7 [4, 0, -6] = true := by decide +kernel
theorem sub7_1359 : sub7 [4, 0, -5] = true := by decide +kernel
theorem sub7_1360 : sub7 [4, 0, -4] = true := by decide +kernel
theorem sub7_1361 : sub7 [4, 0, -3] = true := by decide +kernel
theorem sub7_1362 : sub7 [4, 0, -2] = true := by decide +kernel
theorem sub7_1363 : sub7 [4, 0, -1] = true := by decide +kernel
theorem sub7_1364 : sub7 [4, 0, 0] = true := by decide +kernel
theorem sub7_1365 : sub7 [4, 0, 1] = true := by decide +kernel
theorem sub7_1366 : sub7 [4, 0, 2] = true := by decide +kernel
theorem sub7_1367 : sub7 [4, 0, 3] = true := by decide +kernel
theorem sub7_1368 : sub7 [4, 0, 4] = true := by decide +kernel
theorem sub7_1369 : sub7 [4, 0, 5] = true := by decide +kernel
theorem sub7_1370 : sub7 [4, 0, 6] = true := by decide +kernel
theorem sub7_1371 : sub7 [4, 0, 7] = true := by decide +kernel
theorem sub7_1372 : sub7 [4, 0, 8] = true := by decide +kernel
theorem sub7_1373 : sub7 [4, 1, -8] = true := by decide +kernel
theorem sub7_1374 : sub7 [4, 1, -7] = true := by decide +kernel
theorem sub7_1375 : sub7 [4, 1, -6] = true := by decide +kernel
theorem sb7_42 : ∀ q ∈ blk7_42, sub7 q = true := by
  unfold blk7_42
  exact List.forall_mem_cons.2 ⟨sub7_1344, List.forall_mem_cons.2 ⟨sub7_1345, List.forall_mem_cons.2 ⟨sub7_1346, List.forall_mem_cons.2 ⟨sub7_1347, List.forall_mem_cons.2 ⟨sub7_1348, List.forall_mem_cons.2 ⟨sub7_1349, List.forall_mem_cons.2 ⟨sub7_1350, List.forall_mem_cons.2 ⟨sub7_1351, List.forall_mem_cons.2 ⟨sub7_1352, List.forall_mem_cons.2 ⟨sub7_1353, List.forall_mem_cons.2 ⟨sub7_1354, List.forall_mem_cons.2 ⟨sub7_1355, List.forall_mem_cons.2 ⟨sub7_1356, List.forall_mem_cons.2 ⟨sub7_1357, List.forall_mem_cons.2 ⟨sub7_1358, List.forall_mem_cons.2 ⟨sub7_1359, List.forall_mem_cons.2 ⟨sub7_1360, List.forall_mem_cons.2 ⟨sub7_1361, List.forall_mem_cons.2 ⟨sub7_1362, List.forall_mem_cons.2 ⟨sub7_1363, List.forall_mem_cons.2 ⟨sub7_1364, List.forall_mem_cons.2 ⟨sub7_1365, List.forall_mem_cons.2 ⟨sub7_1366, List.forall_mem_cons.2 ⟨sub7_1367, List.forall_mem_cons.2 ⟨sub7_1368, List.forall_mem_cons.2 ⟨sub7_1369, List.forall_mem_cons.2 ⟨sub7_1370, List.forall_mem_cons.2 ⟨sub7_1371, List.forall_mem_cons.2 ⟨sub7_1372, List.forall_mem_cons.2 ⟨sub7_1373, List.forall_mem_cons.2 ⟨sub7_1374, List.forall_mem_cons.2 ⟨sub7_1375, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_1376 : sub7 [4, 1, -5] = true := by decide +kernel
theorem sub7_1377 : sub7 [4, 1, -4] = true := by decide +kernel
theorem sub7_1378 : sub7 [4, 1, -3] = true := by decide +kernel
theorem sub7_1379 : sub7 [4, 1, -2] = true := by decide +kernel
theorem sub7_1380 : sub7 [4, 1, -1] = true := by decide +kernel
theorem sub7_1381 : sub7 [4, 1, 0] = true := by decide +kernel
theorem sub7_1382 : sub7 [4, 1, 1] = true := by decide +kernel
theorem sub7_1383 : sub7 [4, 1, 2] = true := by decide +kernel
theorem sub7_1384 : sub7 [4, 1, 3] = true := by decide +kernel
theorem sub7_1385 : sub7 [4, 1, 4] = true := by decide +kernel
theorem sub7_1386 : sub7 [4, 1, 5] = true := by decide +kernel
theorem sub7_1387 : sub7 [4, 1, 6] = true := by decide +kernel
theorem sub7_1388 : sub7 [4, 1, 7] = true := by decide +kernel
theorem sub7_1389 : sub7 [4, 1, 8] = true := by decide +kernel
theorem sub7_1390 : sub7 [4, 2, -8] = true := by decide +kernel
theorem sub7_1391 : sub7 [4, 2, -7] = true := by decide +kernel
theorem sub7_1392 : sub7 [4, 2, -6] = true := by decide +kernel
theorem sub7_1393 : sub7 [4, 2, -5] = true := by decide +kernel
theorem sub7_1394 : sub7 [4, 2, -4] = true := by decide +kernel
theorem sub7_1395 : sub7 [4, 2, -3] = true := by decide +kernel
theorem sub7_1396 : sub7 [4, 2, -2] = true := by decide +kernel
theorem sub7_1397 : sub7 [4, 2, -1] = true := by decide +kernel
theorem sub7_1398 : sub7 [4, 2, 0] = true := by decide +kernel
theorem sub7_1399 : sub7 [4, 2, 1] = true := by decide +kernel
theorem sub7_1400 : sub7 [4, 2, 2] = true := by decide +kernel
theorem sub7_1401 : sub7 [4, 2, 3] = true := by decide +kernel
theorem sub7_1402 : sub7 [4, 2, 4] = true := by decide +kernel
theorem sub7_1403 : sub7 [4, 2, 5] = true := by decide +kernel
theorem sub7_1404 : sub7 [4, 2, 6] = true := by decide +kernel
theorem sub7_1405 : sub7 [4, 2, 7] = true := by decide +kernel
theorem sub7_1406 : sub7 [4, 2, 8] = true := by decide +kernel
theorem sub7_1407 : sub7 [4, 3, -7] = true := by decide +kernel
theorem sb7_43 : ∀ q ∈ blk7_43, sub7 q = true := by
  unfold blk7_43
  exact List.forall_mem_cons.2 ⟨sub7_1376, List.forall_mem_cons.2 ⟨sub7_1377, List.forall_mem_cons.2 ⟨sub7_1378, List.forall_mem_cons.2 ⟨sub7_1379, List.forall_mem_cons.2 ⟨sub7_1380, List.forall_mem_cons.2 ⟨sub7_1381, List.forall_mem_cons.2 ⟨sub7_1382, List.forall_mem_cons.2 ⟨sub7_1383, List.forall_mem_cons.2 ⟨sub7_1384, List.forall_mem_cons.2 ⟨sub7_1385, List.forall_mem_cons.2 ⟨sub7_1386, List.forall_mem_cons.2 ⟨sub7_1387, List.forall_mem_cons.2 ⟨sub7_1388, List.forall_mem_cons.2 ⟨sub7_1389, List.forall_mem_cons.2 ⟨sub7_1390, List.forall_mem_cons.2 ⟨sub7_1391, List.forall_mem_cons.2 ⟨sub7_1392, List.forall_mem_cons.2 ⟨sub7_1393, List.forall_mem_cons.2 ⟨sub7_1394, List.forall_mem_cons.2 ⟨sub7_1395, List.forall_mem_cons.2 ⟨sub7_1396, List.forall_mem_cons.2 ⟨sub7_1397, List.forall_mem_cons.2 ⟨sub7_1398, List.forall_mem_cons.2 ⟨sub7_1399, List.forall_mem_cons.2 ⟨sub7_1400, List.forall_mem_cons.2 ⟨sub7_1401, List.forall_mem_cons.2 ⟨sub7_1402, List.forall_mem_cons.2 ⟨sub7_1403, List.forall_mem_cons.2 ⟨sub7_1404, List.forall_mem_cons.2 ⟨sub7_1405, List.forall_mem_cons.2 ⟨sub7_1406, List.forall_mem_cons.2 ⟨sub7_1407, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_1408 : sub7 [4, 3, -6] = true := by decide +kernel
theorem sub7_1409 : sub7 [4, 3, -5] = true := by decide +kernel
theorem sub7_1410 : sub7 [4, 3, -4] = true := by decide +kernel
theorem sub7_1411 : sub7 [4, 3, -3] = true := by decide +kernel
theorem sub7_1412 : sub7 [4, 3, -2] = true := by decide +kernel
theorem sub7_1413 : sub7 [4, 3, -1] = true := by decide +kernel
theorem sub7_1414 : sub7 [4, 3, 0] = true := by decide +kernel
theorem sub7_1415 : sub7 [4, 3, 1] = true := by decide +kernel
theorem sub7_1416 : sub7 [4, 3, 2] = true := by decide +kernel
theorem sub7_1417 : sub7 [4, 3, 3] = true := by decide +kernel
theorem sub7_1418 : sub7 [4, 3, 4] = true := by decide +kernel
theorem sub7_1419 : sub7 [4, 3, 5] = true := by decide +kernel
theorem sub7_1420 : sub7 [4, 3, 6] = true := by decide +kernel
theorem sub7_1421 : sub7 [4, 3, 7] = true := by decide +kernel
theorem sub7_1422 : sub7 [4, 3, 8] = true := by decide +kernel
theorem sub7_1423 : sub7 [4, 3, 9] = true := by decide +kernel
theorem sub7_1424 : sub7 [4, 4, -7] = true := by decide +kernel
theorem sub7_1425 : sub7 [4, 4, -6] = true := by decide +kernel
theorem sub7_1426 : sub7 [4, 4, -5] = true := by decide +kernel
theorem sub7_1427 : sub7 [4, 4, -4] = true := by decide +kernel
theorem sub7_1428 : sub7 [4, 4, -3] = true := by decide +kernel
theorem sub7_1429 : sub7 [4, 4, -2] = true := by decide +kernel
theorem sub7_1430 : sub7 [4, 4, -1] = true := by decide +kernel
theorem sub7_1431 : sub7 [4, 4, 0] = true := by decide +kernel
theorem sub7_1432 : sub7 [4, 4, 1] = true := by decide +kernel
theorem sub7_1433 : sub7 [4, 4, 2] = true := by decide +kernel
theorem sub7_1434 : sub7 [4, 4, 3] = true := by decide +kernel
theorem sub7_1435 : sub7 [4, 4, 4] = true := by decide +kernel
theorem sub7_1436 : sub7 [4, 4, 5] = true := by decide +kernel
theorem sub7_1437 : sub7 [4, 4, 6] = true := by decide +kernel
theorem sub7_1438 : sub7 [4, 4, 7] = true := by decide +kernel
theorem sub7_1439 : sub7 [4, 4, 8] = true := by decide +kernel
theorem sb7_44 : ∀ q ∈ blk7_44, sub7 q = true := by
  unfold blk7_44
  exact List.forall_mem_cons.2 ⟨sub7_1408, List.forall_mem_cons.2 ⟨sub7_1409, List.forall_mem_cons.2 ⟨sub7_1410, List.forall_mem_cons.2 ⟨sub7_1411, List.forall_mem_cons.2 ⟨sub7_1412, List.forall_mem_cons.2 ⟨sub7_1413, List.forall_mem_cons.2 ⟨sub7_1414, List.forall_mem_cons.2 ⟨sub7_1415, List.forall_mem_cons.2 ⟨sub7_1416, List.forall_mem_cons.2 ⟨sub7_1417, List.forall_mem_cons.2 ⟨sub7_1418, List.forall_mem_cons.2 ⟨sub7_1419, List.forall_mem_cons.2 ⟨sub7_1420, List.forall_mem_cons.2 ⟨sub7_1421, List.forall_mem_cons.2 ⟨sub7_1422, List.forall_mem_cons.2 ⟨sub7_1423, List.forall_mem_cons.2 ⟨sub7_1424, List.forall_mem_cons.2 ⟨sub7_1425, List.forall_mem_cons.2 ⟨sub7_1426, List.forall_mem_cons.2 ⟨sub7_1427, List.forall_mem_cons.2 ⟨sub7_1428, List.forall_mem_cons.2 ⟨sub7_1429, List.forall_mem_cons.2 ⟨sub7_1430, List.forall_mem_cons.2 ⟨sub7_1431, List.forall_mem_cons.2 ⟨sub7_1432, List.forall_mem_cons.2 ⟨sub7_1433, List.forall_mem_cons.2 ⟨sub7_1434, List.forall_mem_cons.2 ⟨sub7_1435, List.forall_mem_cons.2 ⟨sub7_1436, List.forall_mem_cons.2 ⟨sub7_1437, List.forall_mem_cons.2 ⟨sub7_1438, List.forall_mem_cons.2 ⟨sub7_1439, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C074
