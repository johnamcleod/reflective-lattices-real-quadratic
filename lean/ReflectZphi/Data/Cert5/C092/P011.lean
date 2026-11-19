import ReflectZphi.Data.Cert5.C092.Base

namespace ReflectZphi.Data.Cert5.C092
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub8_992 : sub8 [2, 2, -2] = true := by decide +kernel
theorem sub8_993 : sub8 [2, 2, -1] = true := by decide +kernel
theorem sub8_994 : sub8 [2, 2, 0] = true := by decide +kernel
theorem sub8_995 : sub8 [2, 2, 1] = true := by decide +kernel
theorem sub8_996 : sub8 [2, 2, 2] = true := by decide +kernel
theorem sub8_997 : sub8 [2, 2, 3] = true := by decide +kernel
theorem sub8_998 : sub8 [2, 2, 4] = true := by decide +kernel
theorem sub8_999 : sub8 [2, 2, 5] = true := by decide +kernel
theorem sub8_1000 : sub8 [2, 2, 6] = true := by decide +kernel
theorem sub8_1001 : sub8 [2, 3, -10] = true := by decide +kernel
theorem sub8_1002 : sub8 [2, 3, -9] = true := by decide +kernel
theorem sub8_1003 : sub8 [2, 3, -8] = true := by decide +kernel
theorem sub8_1004 : sub8 [2, 3, -7] = true := by decide +kernel
theorem sub8_1005 : sub8 [2, 3, -6] = true := by decide +kernel
theorem sub8_1006 : sub8 [2, 3, -5] = true := by decide +kernel
theorem sub8_1007 : sub8 [2, 3, -4] = true := by decide +kernel
theorem sub8_1008 : sub8 [2, 3, -3] = true := by decide +kernel
theorem sub8_1009 : sub8 [2, 3, -2] = true := by decide +kernel
theorem sub8_1010 : sub8 [2, 3, -1] = true := by decide +kernel
theorem sub8_1011 : sub8 [2, 3, 0] = true := by decide +kernel
theorem sub8_1012 : sub8 [2, 3, 1] = true := by decide +kernel
theorem sub8_1013 : sub8 [2, 3, 2] = true := by decide +kernel
theorem sub8_1014 : sub8 [2, 3, 3] = true := by decide +kernel
theorem sub8_1015 : sub8 [2, 3, 4] = true := by decide +kernel
theorem sub8_1016 : sub8 [2, 3, 5] = true := by decide +kernel
theorem sub8_1017 : sub8 [2, 4] = true := by decide +kernel
theorem sub8_1018 : sub8 [2, 5] = true := by decide +kernel
theorem sub8_1019 : sub8 [2, 6] = true := by decide +kernel
theorem sub8_1020 : sub8 [3, -8] = true := by decide +kernel
theorem sub8_1021 : sub8 [3, -7] = true := by decide +kernel
theorem sub8_1022 : sub8 [3, -6] = true := by decide +kernel
theorem sub8_1023 : sub8 [3, -5] = true := by decide +kernel
theorem sb8_31 : ∀ q ∈ blk8_31, sub8 q = true := by
  unfold blk8_31
  exact List.forall_mem_cons.2 ⟨sub8_992, List.forall_mem_cons.2 ⟨sub8_993, List.forall_mem_cons.2 ⟨sub8_994, List.forall_mem_cons.2 ⟨sub8_995, List.forall_mem_cons.2 ⟨sub8_996, List.forall_mem_cons.2 ⟨sub8_997, List.forall_mem_cons.2 ⟨sub8_998, List.forall_mem_cons.2 ⟨sub8_999, List.forall_mem_cons.2 ⟨sub8_1000, List.forall_mem_cons.2 ⟨sub8_1001, List.forall_mem_cons.2 ⟨sub8_1002, List.forall_mem_cons.2 ⟨sub8_1003, List.forall_mem_cons.2 ⟨sub8_1004, List.forall_mem_cons.2 ⟨sub8_1005, List.forall_mem_cons.2 ⟨sub8_1006, List.forall_mem_cons.2 ⟨sub8_1007, List.forall_mem_cons.2 ⟨sub8_1008, List.forall_mem_cons.2 ⟨sub8_1009, List.forall_mem_cons.2 ⟨sub8_1010, List.forall_mem_cons.2 ⟨sub8_1011, List.forall_mem_cons.2 ⟨sub8_1012, List.forall_mem_cons.2 ⟨sub8_1013, List.forall_mem_cons.2 ⟨sub8_1014, List.forall_mem_cons.2 ⟨sub8_1015, List.forall_mem_cons.2 ⟨sub8_1016, List.forall_mem_cons.2 ⟨sub8_1017, List.forall_mem_cons.2 ⟨sub8_1018, List.forall_mem_cons.2 ⟨sub8_1019, List.forall_mem_cons.2 ⟨sub8_1020, List.forall_mem_cons.2 ⟨sub8_1021, List.forall_mem_cons.2 ⟨sub8_1022, List.forall_mem_cons.2 ⟨sub8_1023, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_1024 : sub8 [3, -4, -8] = true := by decide +kernel
theorem sub8_1025 : sub8 [3, -4, -7] = true := by decide +kernel
theorem sub8_1026 : sub8 [3, -4, -6] = true := by decide +kernel
theorem sub8_1027 : sub8 [3, -4, -5] = true := by decide +kernel
theorem sub8_1028 : sub8 [3, -4, -4] = true := by decide +kernel
theorem sub8_1029 : sub8 [3, -4, -3] = true := by decide +kernel
theorem sub8_1030 : sub8 [3, -4, -2] = true := by decide +kernel
theorem sub8_1031 : sub8 [3, -4, -1] = true := by decide +kernel
theorem sub8_1032 : sub8 [3, -4, 0] = true := by decide +kernel
theorem sub8_1033 : sub8 [3, -4, 1] = true := by decide +kernel
theorem sub8_1034 : sub8 [3, -4, 2] = true := by decide +kernel
theorem sub8_1035 : sub8 [3, -4, 3] = true := by decide +kernel
theorem sub8_1036 : sub8 [3, -4, 4] = true := by decide +kernel
theorem sub8_1037 : sub8 [3, -4, 5] = true := by decide +kernel
theorem sub8_1038 : sub8 [3, -4, 6] = true := by decide +kernel
theorem sub8_1039 : sub8 [3, -3, -9] = true := by decide +kernel
theorem sub8_1040 : sub8 [3, -3, -8] = true := by decide +kernel
theorem sub8_1041 : sub8 [3, -3, -7] = true := by decide +kernel
theorem sub8_1042 : sub8 [3, -3, -6] = true := by decide +kernel
theorem sub8_1043 : sub8 [3, -3, -5] = true := by decide +kernel
theorem sub8_1044 : sub8 [3, -3, -4] = true := by decide +kernel
theorem sub8_1045 : sub8 [3, -3, -3] = true := by decide +kernel
theorem sub8_1046 : sub8 [3, -3, -2] = true := by decide +kernel
theorem sub8_1047 : sub8 [3, -3, -1] = true := by decide +kernel
theorem sub8_1048 : sub8 [3, -3, 0] = true := by decide +kernel
theorem sub8_1049 : sub8 [3, -3, 1] = true := by decide +kernel
theorem sub8_1050 : sub8 [3, -3, 2] = true := by decide +kernel
theorem sub8_1051 : sub8 [3, -3, 3] = true := by decide +kernel
theorem sub8_1052 : sub8 [3, -3, 4] = true := by decide +kernel
theorem sub8_1053 : sub8 [3, -3, 5] = true := by decide +kernel
theorem sub8_1054 : sub8 [3, -3, 6] = true := by decide +kernel
theorem sub8_1055 : sub8 [3, -3, 7] = true := by decide +kernel
theorem sb8_32 : ∀ q ∈ blk8_32, sub8 q = true := by
  unfold blk8_32
  exact List.forall_mem_cons.2 ⟨sub8_1024, List.forall_mem_cons.2 ⟨sub8_1025, List.forall_mem_cons.2 ⟨sub8_1026, List.forall_mem_cons.2 ⟨sub8_1027, List.forall_mem_cons.2 ⟨sub8_1028, List.forall_mem_cons.2 ⟨sub8_1029, List.forall_mem_cons.2 ⟨sub8_1030, List.forall_mem_cons.2 ⟨sub8_1031, List.forall_mem_cons.2 ⟨sub8_1032, List.forall_mem_cons.2 ⟨sub8_1033, List.forall_mem_cons.2 ⟨sub8_1034, List.forall_mem_cons.2 ⟨sub8_1035, List.forall_mem_cons.2 ⟨sub8_1036, List.forall_mem_cons.2 ⟨sub8_1037, List.forall_mem_cons.2 ⟨sub8_1038, List.forall_mem_cons.2 ⟨sub8_1039, List.forall_mem_cons.2 ⟨sub8_1040, List.forall_mem_cons.2 ⟨sub8_1041, List.forall_mem_cons.2 ⟨sub8_1042, List.forall_mem_cons.2 ⟨sub8_1043, List.forall_mem_cons.2 ⟨sub8_1044, List.forall_mem_cons.2 ⟨sub8_1045, List.forall_mem_cons.2 ⟨sub8_1046, List.forall_mem_cons.2 ⟨sub8_1047, List.forall_mem_cons.2 ⟨sub8_1048, List.forall_mem_cons.2 ⟨sub8_1049, List.forall_mem_cons.2 ⟨sub8_1050, List.forall_mem_cons.2 ⟨sub8_1051, List.forall_mem_cons.2 ⟨sub8_1052, List.forall_mem_cons.2 ⟨sub8_1053, List.forall_mem_cons.2 ⟨sub8_1054, List.forall_mem_cons.2 ⟨sub8_1055, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_1056 : sub8 [3, -2, -9] = true := by decide +kernel
theorem sub8_1057 : sub8 [3, -2, -8] = true := by decide +kernel
theorem sub8_1058 : sub8 [3, -2, -7] = true := by decide +kernel
theorem sub8_1059 : sub8 [3, -2, -6] = true := by decide +kernel
theorem sub8_1060 : sub8 [3, -2, -5] = true := by decide +kernel
theorem sub8_1061 : sub8 [3, -2, -4] = true := by decide +kernel
theorem sub8_1062 : sub8 [3, -2, -3] = true := by decide +kernel
theorem sub8_1063 : sub8 [3, -2, -2] = true := by decide +kernel
theorem sub8_1064 : sub8 [3, -2, -1] = true := by decide +kernel
theorem sub8_1065 : sub8 [3, -2, 0] = true := by decide +kernel
theorem sub8_1066 : sub8 [3, -2, 1] = true := by decide +kernel
theorem sub8_1067 : sub8 [3, -2, 2] = true := by decide +kernel
theorem sub8_1068 : sub8 [3, -2, 3] = true := by decide +kernel
theorem sub8_1069 : sub8 [3, -2, 4] = true := by decide +kernel
theorem sub8_1070 : sub8 [3, -2, 5] = true := by decide +kernel
theorem sub8_1071 : sub8 [3, -2, 6] = true := by decide +kernel
theorem sub8_1072 : sub8 [3, -2, 7] = true := by decide +kernel
theorem sub8_1073 : sub8 [3, -1, -10] = true := by decide +kernel
theorem sub8_1074 : sub8 [3, -1, -9] = true := by decide +kernel
theorem sub8_1075 : sub8 [3, -1, -8] = true := by decide +kernel
theorem sub8_1076 : sub8 [3, -1, -7] = true := by decide +kernel
theorem sub8_1077 : sub8 [3, -1, -6] = true := by decide +kernel
theorem sub8_1078 : sub8 [3, -1, -5] = true := by decide +kernel
theorem sub8_1079 : sub8 [3, -1, -4] = true := by decide +kernel
theorem sub8_1080 : sub8 [3, -1, -3] = true := by decide +kernel
theorem sub8_1081 : sub8 [3, -1, -2] = true := by decide +kernel
theorem sub8_1082 : sub8 [3, -1, -1] = true := by decide +kernel
theorem sub8_1083 : sub8 [3, -1, 0] = true := by decide +kernel
theorem sub8_1084 : sub8 [3, -1, 1] = true := by decide +kernel
theorem sub8_1085 : sub8 [3, -1, 2] = true := by decide +kernel
theorem sub8_1086 : sub8 [3, -1, 3] = true := by decide +kernel
theorem sub8_1087 : sub8 [3, -1, 4] = true := by decide +kernel
theorem sb8_33 : ∀ q ∈ blk8_33, sub8 q = true := by
  unfold blk8_33
  exact List.forall_mem_cons.2 ⟨sub8_1056, List.forall_mem_cons.2 ⟨sub8_1057, List.forall_mem_cons.2 ⟨sub8_1058, List.forall_mem_cons.2 ⟨sub8_1059, List.forall_mem_cons.2 ⟨sub8_1060, List.forall_mem_cons.2 ⟨sub8_1061, List.forall_mem_cons.2 ⟨sub8_1062, List.forall_mem_cons.2 ⟨sub8_1063, List.forall_mem_cons.2 ⟨sub8_1064, List.forall_mem_cons.2 ⟨sub8_1065, List.forall_mem_cons.2 ⟨sub8_1066, List.forall_mem_cons.2 ⟨sub8_1067, List.forall_mem_cons.2 ⟨sub8_1068, List.forall_mem_cons.2 ⟨sub8_1069, List.forall_mem_cons.2 ⟨sub8_1070, List.forall_mem_cons.2 ⟨sub8_1071, List.forall_mem_cons.2 ⟨sub8_1072, List.forall_mem_cons.2 ⟨sub8_1073, List.forall_mem_cons.2 ⟨sub8_1074, List.forall_mem_cons.2 ⟨sub8_1075, List.forall_mem_cons.2 ⟨sub8_1076, List.forall_mem_cons.2 ⟨sub8_1077, List.forall_mem_cons.2 ⟨sub8_1078, List.forall_mem_cons.2 ⟨sub8_1079, List.forall_mem_cons.2 ⟨sub8_1080, List.forall_mem_cons.2 ⟨sub8_1081, List.forall_mem_cons.2 ⟨sub8_1082, List.forall_mem_cons.2 ⟨sub8_1083, List.forall_mem_cons.2 ⟨sub8_1084, List.forall_mem_cons.2 ⟨sub8_1085, List.forall_mem_cons.2 ⟨sub8_1086, List.forall_mem_cons.2 ⟨sub8_1087, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_1088 : sub8 [3, -1, 5] = true := by decide +kernel
theorem sub8_1089 : sub8 [3, -1, 6] = true := by decide +kernel
theorem sub8_1090 : sub8 [3, 0, -10] = true := by decide +kernel
theorem sub8_1091 : sub8 [3, 0, -9] = true := by decide +kernel
theorem sub8_1092 : sub8 [3, 0, -8] = true := by decide +kernel
theorem sub8_1093 : sub8 [3, 0, -7] = true := by decide +kernel
theorem sub8_1094 : sub8 [3, 0, -6] = true := by decide +kernel
theorem sub8_1095 : sub8 [3, 0, -5] = true := by decide +kernel
theorem sub8_1096 : sub8 [3, 0, -4] = true := by decide +kernel
theorem sub8_1097 : sub8 [3, 0, -3] = true := by decide +kernel
theorem sub8_1098 : sub8 [3, 0, -2] = true := by decide +kernel
theorem sub8_1099 : sub8 [3, 0, -1] = true := by decide +kernel
theorem sub8_1100 : sub8 [3, 0, 0] = true := by decide +kernel
theorem sub8_1101 : sub8 [3, 0, 1] = true := by decide +kernel
theorem sub8_1102 : sub8 [3, 0, 2] = true := by decide +kernel
theorem sub8_1103 : sub8 [3, 0, 3] = true := by decide +kernel
theorem sub8_1104 : sub8 [3, 0, 4] = true := by decide +kernel
theorem sub8_1105 : sub8 [3, 0, 5] = true := by decide +kernel
theorem sub8_1106 : sub8 [3, 0, 6] = true := by decide +kernel
theorem sub8_1107 : sub8 [3, 1, -10] = true := by decide +kernel
theorem sub8_1108 : sub8 [3, 1, -9] = true := by decide +kernel
theorem sub8_1109 : sub8 [3, 1, -8] = true := by decide +kernel
theorem sub8_1110 : sub8 [3, 1, -7] = true := by decide +kernel
theorem sub8_1111 : sub8 [3, 1, -6] = true := by decide +kernel
theorem sub8_1112 : sub8 [3, 1, -5] = true := by decide +kernel
theorem sub8_1113 : sub8 [3, 1, -4] = true := by decide +kernel
theorem sub8_1114 : sub8 [3, 1, -3] = true := by decide +kernel
theorem sub8_1115 : sub8 [3, 1, -2] = true := by decide +kernel
theorem sub8_1116 : sub8 [3, 1, -1] = true := by decide +kernel
theorem sub8_1117 : sub8 [3, 1, 0] = true := by decide +kernel
theorem sub8_1118 : sub8 [3, 1, 1] = true := by decide +kernel
theorem sub8_1119 : sub8 [3, 1, 2] = true := by decide +kernel
theorem sb8_34 : ∀ q ∈ blk8_34, sub8 q = true := by
  unfold blk8_34
  exact List.forall_mem_cons.2 ⟨sub8_1088, List.forall_mem_cons.2 ⟨sub8_1089, List.forall_mem_cons.2 ⟨sub8_1090, List.forall_mem_cons.2 ⟨sub8_1091, List.forall_mem_cons.2 ⟨sub8_1092, List.forall_mem_cons.2 ⟨sub8_1093, List.forall_mem_cons.2 ⟨sub8_1094, List.forall_mem_cons.2 ⟨sub8_1095, List.forall_mem_cons.2 ⟨sub8_1096, List.forall_mem_cons.2 ⟨sub8_1097, List.forall_mem_cons.2 ⟨sub8_1098, List.forall_mem_cons.2 ⟨sub8_1099, List.forall_mem_cons.2 ⟨sub8_1100, List.forall_mem_cons.2 ⟨sub8_1101, List.forall_mem_cons.2 ⟨sub8_1102, List.forall_mem_cons.2 ⟨sub8_1103, List.forall_mem_cons.2 ⟨sub8_1104, List.forall_mem_cons.2 ⟨sub8_1105, List.forall_mem_cons.2 ⟨sub8_1106, List.forall_mem_cons.2 ⟨sub8_1107, List.forall_mem_cons.2 ⟨sub8_1108, List.forall_mem_cons.2 ⟨sub8_1109, List.forall_mem_cons.2 ⟨sub8_1110, List.forall_mem_cons.2 ⟨sub8_1111, List.forall_mem_cons.2 ⟨sub8_1112, List.forall_mem_cons.2 ⟨sub8_1113, List.forall_mem_cons.2 ⟨sub8_1114, List.forall_mem_cons.2 ⟨sub8_1115, List.forall_mem_cons.2 ⟨sub8_1116, List.forall_mem_cons.2 ⟨sub8_1117, List.forall_mem_cons.2 ⟨sub8_1118, List.forall_mem_cons.2 ⟨sub8_1119, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_1120 : sub8 [3, 1, 3] = true := by decide +kernel
theorem sub8_1121 : sub8 [3, 1, 4] = true := by decide +kernel
theorem sub8_1122 : sub8 [3, 1, 5] = true := by decide +kernel
theorem sub8_1123 : sub8 [3, 1, 6] = true := by decide +kernel
theorem sub8_1124 : sub8 [3, 2, -10] = true := by decide +kernel
theorem sub8_1125 : sub8 [3, 2, -9] = true := by decide +kernel
theorem sub8_1126 : sub8 [3, 2, -8] = true := by decide +kernel
theorem sub8_1127 : sub8 [3, 2, -7] = true := by decide +kernel
theorem sub8_1128 : sub8 [3, 2, -6] = true := by decide +kernel
theorem sub8_1129 : sub8 [3, 2, -5] = true := by decide +kernel
theorem sub8_1130 : sub8 [3, 2, -4] = true := by decide +kernel
theorem sub8_1131 : sub8 [3, 2, -3] = true := by decide +kernel
theorem sub8_1132 : sub8 [3, 2, -2] = true := by decide +kernel
theorem sub8_1133 : sub8 [3, 2, -1] = true := by decide +kernel
theorem sub8_1134 : sub8 [3, 2, 0] = true := by decide +kernel
theorem sub8_1135 : sub8 [3, 2, 1] = true := by decide +kernel
theorem sub8_1136 : sub8 [3, 2, 2] = true := by decide +kernel
theorem sub8_1137 : sub8 [3, 2, 3] = true := by decide +kernel
theorem sub8_1138 : sub8 [3, 2, 4] = true := by decide +kernel
theorem sub8_1139 : sub8 [3, 2, 5] = true := by decide +kernel
theorem sub8_1140 : sub8 [3, 3] = true := by decide +kernel
theorem sub8_1141 : sub8 [3, 4] = true := by decide +kernel
theorem sub8_1142 : sub8 [3, 5] = true := by decide +kernel
theorem sub8_1143 : sub8 [3, 6] = true := by decide +kernel
theorem sub8_1144 : sub8 [4, -8] = true := by decide +kernel
theorem sub8_1145 : sub8 [4, -7] = true := by decide +kernel
theorem sub8_1146 : sub8 [4, -6] = true := by decide +kernel
theorem sub8_1147 : sub8 [4, -5] = true := by decide +kernel
theorem sub8_1148 : sub8 [4, -4, -8] = true := by decide +kernel
theorem sub8_1149 : sub8 [4, -4, -7] = true := by decide +kernel
theorem sub8_1150 : sub8 [4, -4, -6] = true := by decide +kernel
theorem sub8_1151 : sub8 [4, -4, -5] = true := by decide +kernel
theorem sb8_35 : ∀ q ∈ blk8_35, sub8 q = true := by
  unfold blk8_35
  exact List.forall_mem_cons.2 ⟨sub8_1120, List.forall_mem_cons.2 ⟨sub8_1121, List.forall_mem_cons.2 ⟨sub8_1122, List.forall_mem_cons.2 ⟨sub8_1123, List.forall_mem_cons.2 ⟨sub8_1124, List.forall_mem_cons.2 ⟨sub8_1125, List.forall_mem_cons.2 ⟨sub8_1126, List.forall_mem_cons.2 ⟨sub8_1127, List.forall_mem_cons.2 ⟨sub8_1128, List.forall_mem_cons.2 ⟨sub8_1129, List.forall_mem_cons.2 ⟨sub8_1130, List.forall_mem_cons.2 ⟨sub8_1131, List.forall_mem_cons.2 ⟨sub8_1132, List.forall_mem_cons.2 ⟨sub8_1133, List.forall_mem_cons.2 ⟨sub8_1134, List.forall_mem_cons.2 ⟨sub8_1135, List.forall_mem_cons.2 ⟨sub8_1136, List.forall_mem_cons.2 ⟨sub8_1137, List.forall_mem_cons.2 ⟨sub8_1138, List.forall_mem_cons.2 ⟨sub8_1139, List.forall_mem_cons.2 ⟨sub8_1140, List.forall_mem_cons.2 ⟨sub8_1141, List.forall_mem_cons.2 ⟨sub8_1142, List.forall_mem_cons.2 ⟨sub8_1143, List.forall_mem_cons.2 ⟨sub8_1144, List.forall_mem_cons.2 ⟨sub8_1145, List.forall_mem_cons.2 ⟨sub8_1146, List.forall_mem_cons.2 ⟨sub8_1147, List.forall_mem_cons.2 ⟨sub8_1148, List.forall_mem_cons.2 ⟨sub8_1149, List.forall_mem_cons.2 ⟨sub8_1150, List.forall_mem_cons.2 ⟨sub8_1151, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_1152 : sub8 [4, -4, -4] = true := by decide +kernel
theorem sub8_1153 : sub8 [4, -4, -3] = true := by decide +kernel
theorem sub8_1154 : sub8 [4, -4, -2] = true := by decide +kernel
theorem sub8_1155 : sub8 [4, -4, -1] = true := by decide +kernel
theorem sub8_1156 : sub8 [4, -4, 0] = true := by decide +kernel
theorem sub8_1157 : sub8 [4, -4, 1] = true := by decide +kernel
theorem sub8_1158 : sub8 [4, -4, 2] = true := by decide +kernel
theorem sub8_1159 : sub8 [4, -4, 3] = true := by decide +kernel
theorem sub8_1160 : sub8 [4, -4, 4] = true := by decide +kernel
theorem sub8_1161 : sub8 [4, -4, 5] = true := by decide +kernel
theorem sub8_1162 : sub8 [4, -4, 6] = true := by decide +kernel
theorem sub8_1163 : sub8 [4, -3, -9] = true := by decide +kernel
theorem sub8_1164 : sub8 [4, -3, -8] = true := by decide +kernel
theorem sub8_1165 : sub8 [4, -3, -7] = true := by decide +kernel
theorem sub8_1166 : sub8 [4, -3, -6] = true := by decide +kernel
theorem sub8_1167 : sub8 [4, -3, -5] = true := by decide +kernel
theorem sub8_1168 : sub8 [4, -3, -4] = true := by decide +kernel
theorem sub8_1169 : sub8 [4, -3, -3] = true := by decide +kernel
theorem sub8_1170 : sub8 [4, -3, -2] = true := by decide +kernel
theorem sub8_1171 : sub8 [4, -3, -1] = true := by decide +kernel
theorem sub8_1172 : sub8 [4, -3, 0] = true := by decide +kernel
theorem sub8_1173 : sub8 [4, -3, 1] = true := by decide +kernel
theorem sub8_1174 : sub8 [4, -3, 2] = true := by decide +kernel
theorem sub8_1175 : sub8 [4, -3, 3] = true := by decide +kernel
theorem sub8_1176 : sub8 [4, -3, 4] = true := by decide +kernel
theorem sub8_1177 : sub8 [4, -3, 5] = true := by decide +kernel
theorem sub8_1178 : sub8 [4, -3, 6] = true := by decide +kernel
theorem sub8_1179 : sub8 [4, -2, -9] = true := by decide +kernel
theorem sub8_1180 : sub8 [4, -2, -8] = true := by decide +kernel
theorem sub8_1181 : sub8 [4, -2, -7] = true := by decide +kernel
theorem sub8_1182 : sub8 [4, -2, -6] = true := by decide +kernel
theorem sub8_1183 : sub8 [4, -2, -5] = true := by decide +kernel
theorem sb8_36 : ∀ q ∈ blk8_36, sub8 q = true := by
  unfold blk8_36
  exact List.forall_mem_cons.2 ⟨sub8_1152, List.forall_mem_cons.2 ⟨sub8_1153, List.forall_mem_cons.2 ⟨sub8_1154, List.forall_mem_cons.2 ⟨sub8_1155, List.forall_mem_cons.2 ⟨sub8_1156, List.forall_mem_cons.2 ⟨sub8_1157, List.forall_mem_cons.2 ⟨sub8_1158, List.forall_mem_cons.2 ⟨sub8_1159, List.forall_mem_cons.2 ⟨sub8_1160, List.forall_mem_cons.2 ⟨sub8_1161, List.forall_mem_cons.2 ⟨sub8_1162, List.forall_mem_cons.2 ⟨sub8_1163, List.forall_mem_cons.2 ⟨sub8_1164, List.forall_mem_cons.2 ⟨sub8_1165, List.forall_mem_cons.2 ⟨sub8_1166, List.forall_mem_cons.2 ⟨sub8_1167, List.forall_mem_cons.2 ⟨sub8_1168, List.forall_mem_cons.2 ⟨sub8_1169, List.forall_mem_cons.2 ⟨sub8_1170, List.forall_mem_cons.2 ⟨sub8_1171, List.forall_mem_cons.2 ⟨sub8_1172, List.forall_mem_cons.2 ⟨sub8_1173, List.forall_mem_cons.2 ⟨sub8_1174, List.forall_mem_cons.2 ⟨sub8_1175, List.forall_mem_cons.2 ⟨sub8_1176, List.forall_mem_cons.2 ⟨sub8_1177, List.forall_mem_cons.2 ⟨sub8_1178, List.forall_mem_cons.2 ⟨sub8_1179, List.forall_mem_cons.2 ⟨sub8_1180, List.forall_mem_cons.2 ⟨sub8_1181, List.forall_mem_cons.2 ⟨sub8_1182, List.forall_mem_cons.2 ⟨sub8_1183, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_1184 : sub8 [4, -2, -4] = true := by decide +kernel
theorem sub8_1185 : sub8 [4, -2, -3] = true := by decide +kernel
theorem sub8_1186 : sub8 [4, -2, -2] = true := by decide +kernel
theorem sub8_1187 : sub8 [4, -2, -1] = true := by decide +kernel
theorem sub8_1188 : sub8 [4, -2, 0] = true := by decide +kernel
theorem sub8_1189 : sub8 [4, -2, 1] = true := by decide +kernel
theorem sub8_1190 : sub8 [4, -2, 2] = true := by decide +kernel
theorem sub8_1191 : sub8 [4, -2, 3] = true := by decide +kernel
theorem sub8_1192 : sub8 [4, -2, 4] = true := by decide +kernel
theorem sub8_1193 : sub8 [4, -2, 5] = true := by decide +kernel
theorem sub8_1194 : sub8 [4, -2, 6] = true := by decide +kernel
theorem sub8_1195 : sub8 [4, -1, -9] = true := by decide +kernel
theorem sub8_1196 : sub8 [4, -1, -8] = true := by decide +kernel
theorem sub8_1197 : sub8 [4, -1, -7] = true := by decide +kernel
theorem sub8_1198 : sub8 [4, -1, -6] = true := by decide +kernel
theorem sub8_1199 : sub8 [4, -1, -5] = true := by decide +kernel
theorem sub8_1200 : sub8 [4, -1, -4] = true := by decide +kernel
theorem sub8_1201 : sub8 [4, -1, -3] = true := by decide +kernel
theorem sub8_1202 : sub8 [4, -1, -2] = true := by decide +kernel
theorem sub8_1203 : sub8 [4, -1, -1] = true := by decide +kernel
theorem sub8_1204 : sub8 [4, -1, 0] = true := by decide +kernel
theorem sub8_1205 : sub8 [4, -1, 1] = true := by decide +kernel
theorem sub8_1206 : sub8 [4, -1, 2] = true := by decide +kernel
theorem sub8_1207 : sub8 [4, -1, 3] = true := by decide +kernel
theorem sub8_1208 : sub8 [4, -1, 4] = true := by decide +kernel
theorem sub8_1209 : sub8 [4, -1, 5] = true := by decide +kernel
theorem sub8_1210 : sub8 [4, 0, -10] = true := by decide +kernel
theorem sub8_1211 : sub8 [4, 0, -9] = true := by decide +kernel
theorem sub8_1212 : sub8 [4, 0, -8] = true := by decide +kernel
theorem sub8_1213 : sub8 [4, 0, -7] = true := by decide +kernel
theorem sub8_1214 : sub8 [4, 0, -6] = true := by decide +kernel
theorem sub8_1215 : sub8 [4, 0, -5] = true := by decide +kernel
theorem sb8_37 : ∀ q ∈ blk8_37, sub8 q = true := by
  unfold blk8_37
  exact List.forall_mem_cons.2 ⟨sub8_1184, List.forall_mem_cons.2 ⟨sub8_1185, List.forall_mem_cons.2 ⟨sub8_1186, List.forall_mem_cons.2 ⟨sub8_1187, List.forall_mem_cons.2 ⟨sub8_1188, List.forall_mem_cons.2 ⟨sub8_1189, List.forall_mem_cons.2 ⟨sub8_1190, List.forall_mem_cons.2 ⟨sub8_1191, List.forall_mem_cons.2 ⟨sub8_1192, List.forall_mem_cons.2 ⟨sub8_1193, List.forall_mem_cons.2 ⟨sub8_1194, List.forall_mem_cons.2 ⟨sub8_1195, List.forall_mem_cons.2 ⟨sub8_1196, List.forall_mem_cons.2 ⟨sub8_1197, List.forall_mem_cons.2 ⟨sub8_1198, List.forall_mem_cons.2 ⟨sub8_1199, List.forall_mem_cons.2 ⟨sub8_1200, List.forall_mem_cons.2 ⟨sub8_1201, List.forall_mem_cons.2 ⟨sub8_1202, List.forall_mem_cons.2 ⟨sub8_1203, List.forall_mem_cons.2 ⟨sub8_1204, List.forall_mem_cons.2 ⟨sub8_1205, List.forall_mem_cons.2 ⟨sub8_1206, List.forall_mem_cons.2 ⟨sub8_1207, List.forall_mem_cons.2 ⟨sub8_1208, List.forall_mem_cons.2 ⟨sub8_1209, List.forall_mem_cons.2 ⟨sub8_1210, List.forall_mem_cons.2 ⟨sub8_1211, List.forall_mem_cons.2 ⟨sub8_1212, List.forall_mem_cons.2 ⟨sub8_1213, List.forall_mem_cons.2 ⟨sub8_1214, List.forall_mem_cons.2 ⟨sub8_1215, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_1216 : sub8 [4, 0, -4] = true := by decide +kernel
theorem sub8_1217 : sub8 [4, 0, -3] = true := by decide +kernel
theorem sub8_1218 : sub8 [4, 0, -2] = true := by decide +kernel
theorem sub8_1219 : sub8 [4, 0, -1] = true := by decide +kernel
theorem sub8_1220 : sub8 [4, 0, 0] = true := by decide +kernel
theorem sub8_1221 : sub8 [4, 0, 1] = true := by decide +kernel
theorem sub8_1222 : sub8 [4, 0, 2] = true := by decide +kernel
theorem sub8_1223 : sub8 [4, 0, 3] = true := by decide +kernel
theorem sub8_1224 : sub8 [4, 0, 4] = true := by decide +kernel
theorem sub8_1225 : sub8 [4, 0, 5] = true := by decide +kernel
theorem sub8_1226 : sub8 [4, 1, -10] = true := by decide +kernel
theorem sub8_1227 : sub8 [4, 1, -9] = true := by decide +kernel
theorem sub8_1228 : sub8 [4, 1, -8] = true := by decide +kernel
theorem sub8_1229 : sub8 [4, 1, -7] = true := by decide +kernel
theorem sub8_1230 : sub8 [4, 1, -6] = true := by decide +kernel
theorem sub8_1231 : sub8 [4, 1, -5] = true := by decide +kernel
theorem sub8_1232 : sub8 [4, 1, -4] = true := by decide +kernel
theorem sub8_1233 : sub8 [4, 1, -3] = true := by decide +kernel
theorem sub8_1234 : sub8 [4, 1, -2] = true := by decide +kernel
theorem sub8_1235 : sub8 [4, 1, -1] = true := by decide +kernel
theorem sub8_1236 : sub8 [4, 1, 0] = true := by decide +kernel
theorem sub8_1237 : sub8 [4, 1, 1] = true := by decide +kernel
theorem sub8_1238 : sub8 [4, 1, 2] = true := by decide +kernel
theorem sub8_1239 : sub8 [4, 1, 3] = true := by decide +kernel
theorem sub8_1240 : sub8 [4, 1, 4] = true := by decide +kernel
theorem sub8_1241 : sub8 [4, 2] = true := by decide +kernel
theorem sub8_1242 : sub8 [4, 3] = true := by decide +kernel
theorem sub8_1243 : sub8 [4, 4] = true := by decide +kernel
theorem sub8_1244 : sub8 [4, 5] = true := by decide +kernel
theorem sub8_1245 : sub8 [5, -8] = true := by decide +kernel
theorem sub8_1246 : sub8 [5, -7] = true := by decide +kernel
theorem sub8_1247 : sub8 [5, -6] = true := by decide +kernel
theorem sb8_38 : ∀ q ∈ blk8_38, sub8 q = true := by
  unfold blk8_38
  exact List.forall_mem_cons.2 ⟨sub8_1216, List.forall_mem_cons.2 ⟨sub8_1217, List.forall_mem_cons.2 ⟨sub8_1218, List.forall_mem_cons.2 ⟨sub8_1219, List.forall_mem_cons.2 ⟨sub8_1220, List.forall_mem_cons.2 ⟨sub8_1221, List.forall_mem_cons.2 ⟨sub8_1222, List.forall_mem_cons.2 ⟨sub8_1223, List.forall_mem_cons.2 ⟨sub8_1224, List.forall_mem_cons.2 ⟨sub8_1225, List.forall_mem_cons.2 ⟨sub8_1226, List.forall_mem_cons.2 ⟨sub8_1227, List.forall_mem_cons.2 ⟨sub8_1228, List.forall_mem_cons.2 ⟨sub8_1229, List.forall_mem_cons.2 ⟨sub8_1230, List.forall_mem_cons.2 ⟨sub8_1231, List.forall_mem_cons.2 ⟨sub8_1232, List.forall_mem_cons.2 ⟨sub8_1233, List.forall_mem_cons.2 ⟨sub8_1234, List.forall_mem_cons.2 ⟨sub8_1235, List.forall_mem_cons.2 ⟨sub8_1236, List.forall_mem_cons.2 ⟨sub8_1237, List.forall_mem_cons.2 ⟨sub8_1238, List.forall_mem_cons.2 ⟨sub8_1239, List.forall_mem_cons.2 ⟨sub8_1240, List.forall_mem_cons.2 ⟨sub8_1241, List.forall_mem_cons.2 ⟨sub8_1242, List.forall_mem_cons.2 ⟨sub8_1243, List.forall_mem_cons.2 ⟨sub8_1244, List.forall_mem_cons.2 ⟨sub8_1245, List.forall_mem_cons.2 ⟨sub8_1246, List.forall_mem_cons.2 ⟨sub8_1247, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_1248 : sub8 [5, -5] = true := by decide +kernel
theorem sub8_1249 : sub8 [5, -4] = true := by decide +kernel
theorem sub8_1250 : sub8 [5, -3] = true := by decide +kernel
theorem sub8_1251 : sub8 [5, -2] = true := by decide +kernel
theorem sub8_1252 : sub8 [5, -1] = true := by decide +kernel
theorem sub8_1253 : sub8 [5, 0] = true := by decide +kernel
theorem sub8_1254 : sub8 [5, 1] = true := by decide +kernel
theorem sub8_1255 : sub8 [5, 2] = true := by decide +kernel
theorem sub8_1256 : sub8 [5, 3] = true := by decide +kernel
theorem sub8_1257 : sub8 [5, 4] = true := by decide +kernel
theorem sub8_1258 : sub8 [6, -7] = true := by decide +kernel
theorem sub8_1259 : sub8 [6, -6] = true := by decide +kernel
theorem sub8_1260 : sub8 [6, -5] = true := by decide +kernel
theorem sub8_1261 : sub8 [6, -4] = true := by decide +kernel
theorem sub8_1262 : sub8 [6, -3] = true := by decide +kernel
theorem sub8_1263 : sub8 [6, -2] = true := by decide +kernel
theorem sub8_1264 : sub8 [6, -1] = true := by decide +kernel
theorem sub8_1265 : sub8 [6, 0] = true := by decide +kernel
theorem sub8_1266 : sub8 [6, 1] = true := by decide +kernel
theorem sub8_1267 : sub8 [6, 2] = true := by decide +kernel
theorem sub8_1268 : sub8 [6, 3] = true := by decide +kernel
theorem sub8_1269 : sub8 [7, -6] = true := by decide +kernel
theorem sub8_1270 : sub8 [7, -5] = true := by decide +kernel
theorem sub8_1271 : sub8 [7, -4] = true := by decide +kernel
theorem sub8_1272 : sub8 [7, -3] = true := by decide +kernel
theorem sub8_1273 : sub8 [7, -2] = true := by decide +kernel
theorem sub8_1274 : sub8 [7, -1] = true := by decide +kernel
theorem sub8_1275 : sub8 [7, 0] = true := by decide +kernel
theorem sub8_1276 : sub8 [7, 1] = true := by decide +kernel
theorem sb8_39 : ∀ q ∈ blk8_39, sub8 q = true := by
  unfold blk8_39
  exact List.forall_mem_cons.2 ⟨sub8_1248, List.forall_mem_cons.2 ⟨sub8_1249, List.forall_mem_cons.2 ⟨sub8_1250, List.forall_mem_cons.2 ⟨sub8_1251, List.forall_mem_cons.2 ⟨sub8_1252, List.forall_mem_cons.2 ⟨sub8_1253, List.forall_mem_cons.2 ⟨sub8_1254, List.forall_mem_cons.2 ⟨sub8_1255, List.forall_mem_cons.2 ⟨sub8_1256, List.forall_mem_cons.2 ⟨sub8_1257, List.forall_mem_cons.2 ⟨sub8_1258, List.forall_mem_cons.2 ⟨sub8_1259, List.forall_mem_cons.2 ⟨sub8_1260, List.forall_mem_cons.2 ⟨sub8_1261, List.forall_mem_cons.2 ⟨sub8_1262, List.forall_mem_cons.2 ⟨sub8_1263, List.forall_mem_cons.2 ⟨sub8_1264, List.forall_mem_cons.2 ⟨sub8_1265, List.forall_mem_cons.2 ⟨sub8_1266, List.forall_mem_cons.2 ⟨sub8_1267, List.forall_mem_cons.2 ⟨sub8_1268, List.forall_mem_cons.2 ⟨sub8_1269, List.forall_mem_cons.2 ⟨sub8_1270, List.forall_mem_cons.2 ⟨sub8_1271, List.forall_mem_cons.2 ⟨sub8_1272, List.forall_mem_cons.2 ⟨sub8_1273, List.forall_mem_cons.2 ⟨sub8_1274, List.forall_mem_cons.2 ⟨sub8_1275, List.forall_mem_cons.2 ⟨sub8_1276, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C092
