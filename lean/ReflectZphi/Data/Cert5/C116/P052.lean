import ReflectZphi.Data.Cert5.C116.Base

namespace ReflectZphi.Data.Cert5.C116

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd10_1_1088 : subd10_1 [2, 3, -8] = true := by decide +kernel
theorem subd10_1_1089 : subd10_1 [2, 3, -7] = true := by decide +kernel
theorem subd10_1_1090 : subd10_1 [2, 3, -6] = true := by decide +kernel
theorem subd10_1_1091 : subd10_1 [2, 3, -5] = true := by decide +kernel
theorem subd10_1_1092 : subd10_1 [2, 3, -4] = true := by decide +kernel
theorem subd10_1_1093 : subd10_1 [2, 3, -3] = true := by decide +kernel
theorem subd10_1_1094 : subd10_1 [2, 3, -2] = true := by decide +kernel
theorem subd10_1_1095 : subd10_1 [2, 3, -1] = true := by decide +kernel
theorem subd10_1_1096 : subd10_1 [2, 3, 0] = true := by decide +kernel
theorem subd10_1_1097 : subd10_1 [2, 3, 1] = true := by decide +kernel
theorem subd10_1_1098 : subd10_1 [2, 3, 2] = true := by decide +kernel
theorem subd10_1_1099 : subd10_1 [2, 3, 3] = true := by decide +kernel
theorem subd10_1_1100 : subd10_1 [2, 3, 4] = true := by decide +kernel
theorem subd10_1_1101 : subd10_1 [2, 3, 5] = true := by decide +kernel
theorem subd10_1_1102 : subd10_1 [2, 3, 6] = true := by decide +kernel
theorem subd10_1_1103 : subd10_1 [2, 4, -8] = true := by decide +kernel
theorem subd10_1_1104 : subd10_1 [2, 4, -7] = true := by decide +kernel
theorem subd10_1_1105 : subd10_1 [2, 4, -6] = true := by decide +kernel
theorem subd10_1_1106 : subd10_1 [2, 4, -5] = true := by decide +kernel
theorem subd10_1_1107 : subd10_1 [2, 4, -4] = true := by decide +kernel
theorem subd10_1_1108 : subd10_1 [2, 4, -3] = true := by decide +kernel
theorem subd10_1_1109 : subd10_1 [2, 4, -2] = true := by decide +kernel
theorem subd10_1_1110 : subd10_1 [2, 4, -1] = true := by decide +kernel
theorem subd10_1_1111 : subd10_1 [2, 4, 0] = true := by decide +kernel
theorem subd10_1_1112 : subd10_1 [2, 4, 1] = true := by decide +kernel
theorem subd10_1_1113 : subd10_1 [2, 4, 2] = true := by decide +kernel
theorem subd10_1_1114 : subd10_1 [2, 4, 3] = true := by decide +kernel
theorem subd10_1_1115 : subd10_1 [2, 4, 4] = true := by decide +kernel
theorem subd10_1_1116 : subd10_1 [2, 4, 5] = true := by decide +kernel
theorem subd10_1_1117 : subd10_1 [2, 5] = true := by decide +kernel
theorem subd10_1_1118 : subd10_1 [2, 6] = true := by decide +kernel
theorem subd10_1_1119 : subd10_1 [2, 7] = true := by decide +kernel
theorem sbd10_1_34 : ∀ q ∈ blkd10_1_34, subd10_1 q = true := by
  unfold blkd10_1_34
  exact List.forall_mem_cons.2 ⟨subd10_1_1088, List.forall_mem_cons.2 ⟨subd10_1_1089, List.forall_mem_cons.2 ⟨subd10_1_1090, List.forall_mem_cons.2 ⟨subd10_1_1091, List.forall_mem_cons.2 ⟨subd10_1_1092, List.forall_mem_cons.2 ⟨subd10_1_1093, List.forall_mem_cons.2 ⟨subd10_1_1094, List.forall_mem_cons.2 ⟨subd10_1_1095, List.forall_mem_cons.2 ⟨subd10_1_1096, List.forall_mem_cons.2 ⟨subd10_1_1097, List.forall_mem_cons.2 ⟨subd10_1_1098, List.forall_mem_cons.2 ⟨subd10_1_1099, List.forall_mem_cons.2 ⟨subd10_1_1100, List.forall_mem_cons.2 ⟨subd10_1_1101, List.forall_mem_cons.2 ⟨subd10_1_1102, List.forall_mem_cons.2 ⟨subd10_1_1103, List.forall_mem_cons.2 ⟨subd10_1_1104, List.forall_mem_cons.2 ⟨subd10_1_1105, List.forall_mem_cons.2 ⟨subd10_1_1106, List.forall_mem_cons.2 ⟨subd10_1_1107, List.forall_mem_cons.2 ⟨subd10_1_1108, List.forall_mem_cons.2 ⟨subd10_1_1109, List.forall_mem_cons.2 ⟨subd10_1_1110, List.forall_mem_cons.2 ⟨subd10_1_1111, List.forall_mem_cons.2 ⟨subd10_1_1112, List.forall_mem_cons.2 ⟨subd10_1_1113, List.forall_mem_cons.2 ⟨subd10_1_1114, List.forall_mem_cons.2 ⟨subd10_1_1115, List.forall_mem_cons.2 ⟨subd10_1_1116, List.forall_mem_cons.2 ⟨subd10_1_1117, List.forall_mem_cons.2 ⟨subd10_1_1118, List.forall_mem_cons.2 ⟨subd10_1_1119, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_1120 : subd10_1 [3, -10] = true := by decide +kernel
theorem subd10_1_1121 : subd10_1 [3, -9] = true := by decide +kernel
theorem subd10_1_1122 : subd10_1 [3, -8] = true := by decide +kernel
theorem subd10_1_1123 : subd10_1 [3, -7] = true := by decide +kernel
theorem subd10_1_1124 : subd10_1 [3, -6] = true := by decide +kernel
theorem subd10_1_1125 : subd10_1 [3, -5, -7] = true := by decide +kernel
theorem subd10_1_1126 : subd10_1 [3, -5, -6] = true := by decide +kernel
theorem subd10_1_1127 : subd10_1 [3, -5, -5] = true := by decide +kernel
theorem subd10_1_1128 : subd10_1 [3, -5, -4] = true := by decide +kernel
theorem subd10_1_1129 : subd10_1 [3, -5, -3] = true := by decide +kernel
theorem subd10_1_1130 : subd10_1 [3, -5, -2] = true := by decide +kernel
theorem subd10_1_1131 : subd10_1 [3, -5, -1] = true := by decide +kernel
theorem subd10_1_1132 : subd10_1 [3, -5, 0] = true := by decide +kernel
theorem subd10_1_1133 : subd10_1 [3, -5, 1] = true := by decide +kernel
theorem subd10_1_1134 : subd10_1 [3, -5, 2] = true := by decide +kernel
theorem subd10_1_1135 : subd10_1 [3, -5, 3] = true := by decide +kernel
theorem subd10_1_1136 : subd10_1 [3, -5, 4] = true := by decide +kernel
theorem subd10_1_1137 : subd10_1 [3, -5, 5] = true := by decide +kernel
theorem subd10_1_1138 : subd10_1 [3, -5, 6] = true := by decide +kernel
theorem subd10_1_1139 : subd10_1 [3, -4, -7] = true := by decide +kernel
theorem subd10_1_1140 : subd10_1 [3, -4, -6] = true := by decide +kernel
theorem subd10_1_1141 : subd10_1 [3, -4, -5] = true := by decide +kernel
theorem subd10_1_1142 : subd10_1 [3, -4, -4] = true := by decide +kernel
theorem subd10_1_1143 : subd10_1 [3, -4, -3] = true := by decide +kernel
theorem subd10_1_1144 : subd10_1 [3, -4, -2] = true := by decide +kernel
theorem subd10_1_1145 : subd10_1 [3, -4, -1] = true := by decide +kernel
theorem subd10_1_1146 : subd10_1 [3, -4, 0] = true := by decide +kernel
theorem subd10_1_1147 : subd10_1 [3, -4, 1] = true := by decide +kernel
theorem subd10_1_1148 : subd10_1 [3, -4, 2] = true := by decide +kernel
theorem subd10_1_1149 : subd10_1 [3, -4, 3] = true := by decide +kernel
theorem subd10_1_1150 : subd10_1 [3, -4, 4] = true := by decide +kernel
theorem subd10_1_1151 : subd10_1 [3, -4, 5] = true := by decide +kernel
theorem sbd10_1_35 : ∀ q ∈ blkd10_1_35, subd10_1 q = true := by
  unfold blkd10_1_35
  exact List.forall_mem_cons.2 ⟨subd10_1_1120, List.forall_mem_cons.2 ⟨subd10_1_1121, List.forall_mem_cons.2 ⟨subd10_1_1122, List.forall_mem_cons.2 ⟨subd10_1_1123, List.forall_mem_cons.2 ⟨subd10_1_1124, List.forall_mem_cons.2 ⟨subd10_1_1125, List.forall_mem_cons.2 ⟨subd10_1_1126, List.forall_mem_cons.2 ⟨subd10_1_1127, List.forall_mem_cons.2 ⟨subd10_1_1128, List.forall_mem_cons.2 ⟨subd10_1_1129, List.forall_mem_cons.2 ⟨subd10_1_1130, List.forall_mem_cons.2 ⟨subd10_1_1131, List.forall_mem_cons.2 ⟨subd10_1_1132, List.forall_mem_cons.2 ⟨subd10_1_1133, List.forall_mem_cons.2 ⟨subd10_1_1134, List.forall_mem_cons.2 ⟨subd10_1_1135, List.forall_mem_cons.2 ⟨subd10_1_1136, List.forall_mem_cons.2 ⟨subd10_1_1137, List.forall_mem_cons.2 ⟨subd10_1_1138, List.forall_mem_cons.2 ⟨subd10_1_1139, List.forall_mem_cons.2 ⟨subd10_1_1140, List.forall_mem_cons.2 ⟨subd10_1_1141, List.forall_mem_cons.2 ⟨subd10_1_1142, List.forall_mem_cons.2 ⟨subd10_1_1143, List.forall_mem_cons.2 ⟨subd10_1_1144, List.forall_mem_cons.2 ⟨subd10_1_1145, List.forall_mem_cons.2 ⟨subd10_1_1146, List.forall_mem_cons.2 ⟨subd10_1_1147, List.forall_mem_cons.2 ⟨subd10_1_1148, List.forall_mem_cons.2 ⟨subd10_1_1149, List.forall_mem_cons.2 ⟨subd10_1_1150, List.forall_mem_cons.2 ⟨subd10_1_1151, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_1152 : subd10_1 [3, -4, 6] = true := by decide +kernel
theorem subd10_1_1153 : subd10_1 [3, -4, 7] = true := by decide +kernel
theorem subd10_1_1154 : subd10_1 [3, -3, -8] = true := by decide +kernel
theorem subd10_1_1155 : subd10_1 [3, -3, -7] = true := by decide +kernel
theorem subd10_1_1156 : subd10_1 [3, -3, -6] = true := by decide +kernel
theorem subd10_1_1157 : subd10_1 [3, -3, -5] = true := by decide +kernel
theorem subd10_1_1158 : subd10_1 [3, -3, -4] = true := by decide +kernel
theorem subd10_1_1159 : subd10_1 [3, -3, -3] = true := by decide +kernel
theorem subd10_1_1160 : subd10_1 [3, -3, -2] = true := by decide +kernel
theorem subd10_1_1161 : subd10_1 [3, -3, -1] = true := by decide +kernel
theorem subd10_1_1162 : subd10_1 [3, -3, 0] = true := by decide +kernel
theorem subd10_1_1163 : subd10_1 [3, -3, 1] = true := by decide +kernel
theorem subd10_1_1164 : subd10_1 [3, -3, 2] = true := by decide +kernel
theorem subd10_1_1165 : subd10_1 [3, -3, 3] = true := by decide +kernel
theorem subd10_1_1166 : subd10_1 [3, -3, 4] = true := by decide +kernel
theorem subd10_1_1167 : subd10_1 [3, -3, 5] = true := by decide +kernel
theorem subd10_1_1168 : subd10_1 [3, -3, 6] = true := by decide +kernel
theorem subd10_1_1169 : subd10_1 [3, -3, 7] = true := by decide +kernel
theorem subd10_1_1170 : subd10_1 [3, -2, -8] = true := by decide +kernel
theorem subd10_1_1171 : subd10_1 [3, -2, -7] = true := by decide +kernel
theorem subd10_1_1172 : subd10_1 [3, -2, -6] = true := by decide +kernel
theorem subd10_1_1173 : subd10_1 [3, -2, -5] = true := by decide +kernel
theorem subd10_1_1174 : subd10_1 [3, -2, -4] = true := by decide +kernel
theorem subd10_1_1175 : subd10_1 [3, -2, -3] = true := by decide +kernel
theorem subd10_1_1176 : subd10_1 [3, -2, -2] = true := by decide +kernel
theorem subd10_1_1177 : subd10_1 [3, -2, -1] = true := by decide +kernel
theorem subd10_1_1178 : subd10_1 [3, -2, 0] = true := by decide +kernel
theorem subd10_1_1179 : subd10_1 [3, -2, 1] = true := by decide +kernel
theorem subd10_1_1180 : subd10_1 [3, -2, 2] = true := by decide +kernel
theorem subd10_1_1181 : subd10_1 [3, -2, 3] = true := by decide +kernel
theorem subd10_1_1182 : subd10_1 [3, -2, 4] = true := by decide +kernel
theorem subd10_1_1183 : subd10_1 [3, -2, 5] = true := by decide +kernel
theorem sbd10_1_36 : ∀ q ∈ blkd10_1_36, subd10_1 q = true := by
  unfold blkd10_1_36
  exact List.forall_mem_cons.2 ⟨subd10_1_1152, List.forall_mem_cons.2 ⟨subd10_1_1153, List.forall_mem_cons.2 ⟨subd10_1_1154, List.forall_mem_cons.2 ⟨subd10_1_1155, List.forall_mem_cons.2 ⟨subd10_1_1156, List.forall_mem_cons.2 ⟨subd10_1_1157, List.forall_mem_cons.2 ⟨subd10_1_1158, List.forall_mem_cons.2 ⟨subd10_1_1159, List.forall_mem_cons.2 ⟨subd10_1_1160, List.forall_mem_cons.2 ⟨subd10_1_1161, List.forall_mem_cons.2 ⟨subd10_1_1162, List.forall_mem_cons.2 ⟨subd10_1_1163, List.forall_mem_cons.2 ⟨subd10_1_1164, List.forall_mem_cons.2 ⟨subd10_1_1165, List.forall_mem_cons.2 ⟨subd10_1_1166, List.forall_mem_cons.2 ⟨subd10_1_1167, List.forall_mem_cons.2 ⟨subd10_1_1168, List.forall_mem_cons.2 ⟨subd10_1_1169, List.forall_mem_cons.2 ⟨subd10_1_1170, List.forall_mem_cons.2 ⟨subd10_1_1171, List.forall_mem_cons.2 ⟨subd10_1_1172, List.forall_mem_cons.2 ⟨subd10_1_1173, List.forall_mem_cons.2 ⟨subd10_1_1174, List.forall_mem_cons.2 ⟨subd10_1_1175, List.forall_mem_cons.2 ⟨subd10_1_1176, List.forall_mem_cons.2 ⟨subd10_1_1177, List.forall_mem_cons.2 ⟨subd10_1_1178, List.forall_mem_cons.2 ⟨subd10_1_1179, List.forall_mem_cons.2 ⟨subd10_1_1180, List.forall_mem_cons.2 ⟨subd10_1_1181, List.forall_mem_cons.2 ⟨subd10_1_1182, List.forall_mem_cons.2 ⟨subd10_1_1183, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_1184 : subd10_1 [3, -2, 6] = true := by decide +kernel
theorem subd10_1_1185 : subd10_1 [3, -2, 7] = true := by decide +kernel
theorem subd10_1_1186 : subd10_1 [3, -1, -8] = true := by decide +kernel
theorem subd10_1_1187 : subd10_1 [3, -1, -7] = true := by decide +kernel
theorem subd10_1_1188 : subd10_1 [3, -1, -6] = true := by decide +kernel
theorem subd10_1_1189 : subd10_1 [3, -1, -5] = true := by decide +kernel
theorem subd10_1_1190 : subd10_1 [3, -1, -4] = true := by decide +kernel
theorem subd10_1_1191 : subd10_1 [3, -1, -3] = true := by decide +kernel
theorem subd10_1_1192 : subd10_1 [3, -1, -2] = true := by decide +kernel
theorem subd10_1_1193 : subd10_1 [3, -1, -1] = true := by decide +kernel
theorem subd10_1_1194 : subd10_1 [3, -1, 0] = true := by decide +kernel
theorem subd10_1_1195 : subd10_1 [3, -1, 1] = true := by decide +kernel
theorem subd10_1_1196 : subd10_1 [3, -1, 2] = true := by decide +kernel
theorem subd10_1_1197 : subd10_1 [3, -1, 3] = true := by decide +kernel
theorem subd10_1_1198 : subd10_1 [3, -1, 4] = true := by decide +kernel
theorem subd10_1_1199 : subd10_1 [3, -1, 5] = true := by decide +kernel
theorem subd10_1_1200 : subd10_1 [3, -1, 6] = true := by decide +kernel
theorem subd10_1_1201 : subd10_1 [3, -1, 7] = true := by decide +kernel
theorem subd10_1_1202 : subd10_1 [3, 0, -8] = true := by decide +kernel
theorem subd10_1_1203 : subd10_1 [3, 0, -7] = true := by decide +kernel
theorem subd10_1_1204 : subd10_1 [3, 0, -6] = true := by decide +kernel
theorem subd10_1_1205 : subd10_1 [3, 0, -5] = true := by decide +kernel
theorem subd10_1_1206 : subd10_1 [3, 0, -4] = true := by decide +kernel
theorem subd10_1_1207 : subd10_1 [3, 0, -3] = true := by decide +kernel
theorem subd10_1_1208 : subd10_1 [3, 0, -2] = true := by decide +kernel
theorem subd10_1_1209 : subd10_1 [3, 0, -1] = true := by decide +kernel
theorem subd10_1_1210 : subd10_1 [3, 0, 0] = true := by decide +kernel
theorem subd10_1_1211 : subd10_1 [3, 0, 1] = true := by decide +kernel
theorem subd10_1_1212 : subd10_1 [3, 0, 2] = true := by decide +kernel
theorem subd10_1_1213 : subd10_1 [3, 0, 3] = true := by decide +kernel
theorem subd10_1_1214 : subd10_1 [3, 0, 4] = true := by decide +kernel
theorem subd10_1_1215 : subd10_1 [3, 0, 5] = true := by decide +kernel
theorem sbd10_1_37 : ∀ q ∈ blkd10_1_37, subd10_1 q = true := by
  unfold blkd10_1_37
  exact List.forall_mem_cons.2 ⟨subd10_1_1184, List.forall_mem_cons.2 ⟨subd10_1_1185, List.forall_mem_cons.2 ⟨subd10_1_1186, List.forall_mem_cons.2 ⟨subd10_1_1187, List.forall_mem_cons.2 ⟨subd10_1_1188, List.forall_mem_cons.2 ⟨subd10_1_1189, List.forall_mem_cons.2 ⟨subd10_1_1190, List.forall_mem_cons.2 ⟨subd10_1_1191, List.forall_mem_cons.2 ⟨subd10_1_1192, List.forall_mem_cons.2 ⟨subd10_1_1193, List.forall_mem_cons.2 ⟨subd10_1_1194, List.forall_mem_cons.2 ⟨subd10_1_1195, List.forall_mem_cons.2 ⟨subd10_1_1196, List.forall_mem_cons.2 ⟨subd10_1_1197, List.forall_mem_cons.2 ⟨subd10_1_1198, List.forall_mem_cons.2 ⟨subd10_1_1199, List.forall_mem_cons.2 ⟨subd10_1_1200, List.forall_mem_cons.2 ⟨subd10_1_1201, List.forall_mem_cons.2 ⟨subd10_1_1202, List.forall_mem_cons.2 ⟨subd10_1_1203, List.forall_mem_cons.2 ⟨subd10_1_1204, List.forall_mem_cons.2 ⟨subd10_1_1205, List.forall_mem_cons.2 ⟨subd10_1_1206, List.forall_mem_cons.2 ⟨subd10_1_1207, List.forall_mem_cons.2 ⟨subd10_1_1208, List.forall_mem_cons.2 ⟨subd10_1_1209, List.forall_mem_cons.2 ⟨subd10_1_1210, List.forall_mem_cons.2 ⟨subd10_1_1211, List.forall_mem_cons.2 ⟨subd10_1_1212, List.forall_mem_cons.2 ⟨subd10_1_1213, List.forall_mem_cons.2 ⟨subd10_1_1214, List.forall_mem_cons.2 ⟨subd10_1_1215, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_1216 : subd10_1 [3, 0, 6] = true := by decide +kernel
theorem subd10_1_1217 : subd10_1 [3, 1, -8] = true := by decide +kernel
theorem subd10_1_1218 : subd10_1 [3, 1, -7] = true := by decide +kernel
theorem subd10_1_1219 : subd10_1 [3, 1, -6] = true := by decide +kernel
theorem subd10_1_1220 : subd10_1 [3, 1, -5] = true := by decide +kernel
theorem subd10_1_1221 : subd10_1 [3, 1, -4] = true := by decide +kernel
theorem subd10_1_1222 : subd10_1 [3, 1, -3] = true := by decide +kernel
theorem subd10_1_1223 : subd10_1 [3, 1, -2] = true := by decide +kernel
theorem subd10_1_1224 : subd10_1 [3, 1, -1] = true := by decide +kernel
theorem subd10_1_1225 : subd10_1 [3, 1, 0] = true := by decide +kernel
theorem subd10_1_1226 : subd10_1 [3, 1, 1] = true := by decide +kernel
theorem subd10_1_1227 : subd10_1 [3, 1, 2] = true := by decide +kernel
theorem subd10_1_1228 : subd10_1 [3, 1, 3] = true := by decide +kernel
theorem subd10_1_1229 : subd10_1 [3, 1, 4] = true := by decide +kernel
theorem subd10_1_1230 : subd10_1 [3, 1, 5] = true := by decide +kernel
theorem subd10_1_1231 : subd10_1 [3, 1, 6] = true := by decide +kernel
theorem subd10_1_1232 : subd10_1 [3, 2, -8] = true := by decide +kernel
theorem subd10_1_1233 : subd10_1 [3, 2, -7] = true := by decide +kernel
theorem subd10_1_1234 : subd10_1 [3, 2, -6] = true := by decide +kernel
theorem subd10_1_1235 : subd10_1 [3, 2, -5] = true := by decide +kernel
theorem subd10_1_1236 : subd10_1 [3, 2, -4] = true := by decide +kernel
theorem subd10_1_1237 : subd10_1 [3, 2, -3] = true := by decide +kernel
theorem subd10_1_1238 : subd10_1 [3, 2, -2] = true := by decide +kernel
theorem subd10_1_1239 : subd10_1 [3, 2, -1] = true := by decide +kernel
theorem subd10_1_1240 : subd10_1 [3, 2, 0] = true := by decide +kernel
theorem subd10_1_1241 : subd10_1 [3, 2, 1] = true := by decide +kernel
theorem subd10_1_1242 : subd10_1 [3, 2, 2] = true := by decide +kernel
theorem subd10_1_1243 : subd10_1 [3, 2, 3] = true := by decide +kernel
theorem subd10_1_1244 : subd10_1 [3, 2, 4] = true := by decide +kernel
theorem subd10_1_1245 : subd10_1 [3, 2, 5] = true := by decide +kernel
theorem subd10_1_1246 : subd10_1 [3, 3, -8] = true := by decide +kernel
theorem subd10_1_1247 : subd10_1 [3, 3, -7] = true := by decide +kernel
theorem sbd10_1_38 : ∀ q ∈ blkd10_1_38, subd10_1 q = true := by
  unfold blkd10_1_38
  exact List.forall_mem_cons.2 ⟨subd10_1_1216, List.forall_mem_cons.2 ⟨subd10_1_1217, List.forall_mem_cons.2 ⟨subd10_1_1218, List.forall_mem_cons.2 ⟨subd10_1_1219, List.forall_mem_cons.2 ⟨subd10_1_1220, List.forall_mem_cons.2 ⟨subd10_1_1221, List.forall_mem_cons.2 ⟨subd10_1_1222, List.forall_mem_cons.2 ⟨subd10_1_1223, List.forall_mem_cons.2 ⟨subd10_1_1224, List.forall_mem_cons.2 ⟨subd10_1_1225, List.forall_mem_cons.2 ⟨subd10_1_1226, List.forall_mem_cons.2 ⟨subd10_1_1227, List.forall_mem_cons.2 ⟨subd10_1_1228, List.forall_mem_cons.2 ⟨subd10_1_1229, List.forall_mem_cons.2 ⟨subd10_1_1230, List.forall_mem_cons.2 ⟨subd10_1_1231, List.forall_mem_cons.2 ⟨subd10_1_1232, List.forall_mem_cons.2 ⟨subd10_1_1233, List.forall_mem_cons.2 ⟨subd10_1_1234, List.forall_mem_cons.2 ⟨subd10_1_1235, List.forall_mem_cons.2 ⟨subd10_1_1236, List.forall_mem_cons.2 ⟨subd10_1_1237, List.forall_mem_cons.2 ⟨subd10_1_1238, List.forall_mem_cons.2 ⟨subd10_1_1239, List.forall_mem_cons.2 ⟨subd10_1_1240, List.forall_mem_cons.2 ⟨subd10_1_1241, List.forall_mem_cons.2 ⟨subd10_1_1242, List.forall_mem_cons.2 ⟨subd10_1_1243, List.forall_mem_cons.2 ⟨subd10_1_1244, List.forall_mem_cons.2 ⟨subd10_1_1245, List.forall_mem_cons.2 ⟨subd10_1_1246, List.forall_mem_cons.2 ⟨subd10_1_1247, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_1248 : subd10_1 [3, 3, -6] = true := by decide +kernel
theorem subd10_1_1249 : subd10_1 [3, 3, -5] = true := by decide +kernel
theorem subd10_1_1250 : subd10_1 [3, 3, -4] = true := by decide +kernel
theorem subd10_1_1251 : subd10_1 [3, 3, -3] = true := by decide +kernel
theorem subd10_1_1252 : subd10_1 [3, 3, -2] = true := by decide +kernel
theorem subd10_1_1253 : subd10_1 [3, 3, -1] = true := by decide +kernel
theorem subd10_1_1254 : subd10_1 [3, 3, 0] = true := by decide +kernel
theorem subd10_1_1255 : subd10_1 [3, 3, 1] = true := by decide +kernel
theorem subd10_1_1256 : subd10_1 [3, 3, 2] = true := by decide +kernel
theorem subd10_1_1257 : subd10_1 [3, 3, 3] = true := by decide +kernel
theorem subd10_1_1258 : subd10_1 [3, 3, 4] = true := by decide +kernel
theorem subd10_1_1259 : subd10_1 [3, 3, 5] = true := by decide +kernel
theorem subd10_1_1260 : subd10_1 [3, 4] = true := by decide +kernel
theorem subd10_1_1261 : subd10_1 [3, 5] = true := by decide +kernel
theorem subd10_1_1262 : subd10_1 [3, 6] = true := by decide +kernel
theorem subd10_1_1263 : subd10_1 [4, -10] = true := by decide +kernel
theorem subd10_1_1264 : subd10_1 [4, -9] = true := by decide +kernel
theorem subd10_1_1265 : subd10_1 [4, -8] = true := by decide +kernel
theorem subd10_1_1266 : subd10_1 [4, -7] = true := by decide +kernel
theorem subd10_1_1267 : subd10_1 [4, -6] = true := by decide +kernel
theorem subd10_1_1268 : subd10_1 [4, -5] = true := by decide +kernel
theorem subd10_1_1269 : subd10_1 [4, -4, -7] = true := by decide +kernel
theorem subd10_1_1270 : subd10_1 [4, -4, -6] = true := by decide +kernel
theorem subd10_1_1271 : subd10_1 [4, -4, -5] = true := by decide +kernel
theorem subd10_1_1272 : subd10_1 [4, -4, -4] = true := by decide +kernel
theorem subd10_1_1273 : subd10_1 [4, -4, -3] = true := by decide +kernel
theorem subd10_1_1274 : subd10_1 [4, -4, -2] = true := by decide +kernel
theorem subd10_1_1275 : subd10_1 [4, -4, -1] = true := by decide +kernel
theorem subd10_1_1276 : subd10_1 [4, -4, 0] = true := by decide +kernel
theorem subd10_1_1277 : subd10_1 [4, -4, 1] = true := by decide +kernel
theorem subd10_1_1278 : subd10_1 [4, -4, 2] = true := by decide +kernel
theorem subd10_1_1279 : subd10_1 [4, -4, 3] = true := by decide +kernel
theorem sbd10_1_39 : ∀ q ∈ blkd10_1_39, subd10_1 q = true := by
  unfold blkd10_1_39
  exact List.forall_mem_cons.2 ⟨subd10_1_1248, List.forall_mem_cons.2 ⟨subd10_1_1249, List.forall_mem_cons.2 ⟨subd10_1_1250, List.forall_mem_cons.2 ⟨subd10_1_1251, List.forall_mem_cons.2 ⟨subd10_1_1252, List.forall_mem_cons.2 ⟨subd10_1_1253, List.forall_mem_cons.2 ⟨subd10_1_1254, List.forall_mem_cons.2 ⟨subd10_1_1255, List.forall_mem_cons.2 ⟨subd10_1_1256, List.forall_mem_cons.2 ⟨subd10_1_1257, List.forall_mem_cons.2 ⟨subd10_1_1258, List.forall_mem_cons.2 ⟨subd10_1_1259, List.forall_mem_cons.2 ⟨subd10_1_1260, List.forall_mem_cons.2 ⟨subd10_1_1261, List.forall_mem_cons.2 ⟨subd10_1_1262, List.forall_mem_cons.2 ⟨subd10_1_1263, List.forall_mem_cons.2 ⟨subd10_1_1264, List.forall_mem_cons.2 ⟨subd10_1_1265, List.forall_mem_cons.2 ⟨subd10_1_1266, List.forall_mem_cons.2 ⟨subd10_1_1267, List.forall_mem_cons.2 ⟨subd10_1_1268, List.forall_mem_cons.2 ⟨subd10_1_1269, List.forall_mem_cons.2 ⟨subd10_1_1270, List.forall_mem_cons.2 ⟨subd10_1_1271, List.forall_mem_cons.2 ⟨subd10_1_1272, List.forall_mem_cons.2 ⟨subd10_1_1273, List.forall_mem_cons.2 ⟨subd10_1_1274, List.forall_mem_cons.2 ⟨subd10_1_1275, List.forall_mem_cons.2 ⟨subd10_1_1276, List.forall_mem_cons.2 ⟨subd10_1_1277, List.forall_mem_cons.2 ⟨subd10_1_1278, List.forall_mem_cons.2 ⟨subd10_1_1279, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_1280 : subd10_1 [4, -4, 4] = true := by decide +kernel
theorem subd10_1_1281 : subd10_1 [4, -4, 5] = true := by decide +kernel
theorem subd10_1_1282 : subd10_1 [4, -4, 6] = true := by decide +kernel
theorem subd10_1_1283 : subd10_1 [4, -3, -7] = true := by decide +kernel
theorem subd10_1_1284 : subd10_1 [4, -3, -6] = true := by decide +kernel
theorem subd10_1_1285 : subd10_1 [4, -3, -5] = true := by decide +kernel
theorem subd10_1_1286 : subd10_1 [4, -3, -4] = true := by decide +kernel
theorem subd10_1_1287 : subd10_1 [4, -3, -3] = true := by decide +kernel
theorem subd10_1_1288 : subd10_1 [4, -3, -2] = true := by decide +kernel
theorem subd10_1_1289 : subd10_1 [4, -3, -1] = true := by decide +kernel
theorem subd10_1_1290 : subd10_1 [4, -3, 0] = true := by decide +kernel
theorem subd10_1_1291 : subd10_1 [4, -3, 1] = true := by decide +kernel
theorem subd10_1_1292 : subd10_1 [4, -3, 2] = true := by decide +kernel
theorem subd10_1_1293 : subd10_1 [4, -3, 3] = true := by decide +kernel
theorem subd10_1_1294 : subd10_1 [4, -3, 4] = true := by decide +kernel
theorem subd10_1_1295 : subd10_1 [4, -3, 5] = true := by decide +kernel
theorem subd10_1_1296 : subd10_1 [4, -3, 6] = true := by decide +kernel
theorem subd10_1_1297 : subd10_1 [4, -2, -8] = true := by decide +kernel
theorem subd10_1_1298 : subd10_1 [4, -2, -7] = true := by decide +kernel
theorem subd10_1_1299 : subd10_1 [4, -2, -6] = true := by decide +kernel
theorem subd10_1_1300 : subd10_1 [4, -2, -5] = true := by decide +kernel
theorem subd10_1_1301 : subd10_1 [4, -2, -4] = true := by decide +kernel
theorem subd10_1_1302 : subd10_1 [4, -2, -3] = true := by decide +kernel
theorem subd10_1_1303 : subd10_1 [4, -2, -2] = true := by decide +kernel
theorem subd10_1_1304 : subd10_1 [4, -2, -1] = true := by decide +kernel
theorem subd10_1_1305 : subd10_1 [4, -2, 0] = true := by decide +kernel
theorem subd10_1_1306 : subd10_1 [4, -2, 1] = true := by decide +kernel
theorem subd10_1_1307 : subd10_1 [4, -2, 2] = true := by decide +kernel
theorem subd10_1_1308 : subd10_1 [4, -2, 3] = true := by decide +kernel
theorem subd10_1_1309 : subd10_1 [4, -2, 4] = true := by decide +kernel
theorem subd10_1_1310 : subd10_1 [4, -2, 5] = true := by decide +kernel
theorem subd10_1_1311 : subd10_1 [4, -2, 6] = true := by decide +kernel
theorem sbd10_1_40 : ∀ q ∈ blkd10_1_40, subd10_1 q = true := by
  unfold blkd10_1_40
  exact List.forall_mem_cons.2 ⟨subd10_1_1280, List.forall_mem_cons.2 ⟨subd10_1_1281, List.forall_mem_cons.2 ⟨subd10_1_1282, List.forall_mem_cons.2 ⟨subd10_1_1283, List.forall_mem_cons.2 ⟨subd10_1_1284, List.forall_mem_cons.2 ⟨subd10_1_1285, List.forall_mem_cons.2 ⟨subd10_1_1286, List.forall_mem_cons.2 ⟨subd10_1_1287, List.forall_mem_cons.2 ⟨subd10_1_1288, List.forall_mem_cons.2 ⟨subd10_1_1289, List.forall_mem_cons.2 ⟨subd10_1_1290, List.forall_mem_cons.2 ⟨subd10_1_1291, List.forall_mem_cons.2 ⟨subd10_1_1292, List.forall_mem_cons.2 ⟨subd10_1_1293, List.forall_mem_cons.2 ⟨subd10_1_1294, List.forall_mem_cons.2 ⟨subd10_1_1295, List.forall_mem_cons.2 ⟨subd10_1_1296, List.forall_mem_cons.2 ⟨subd10_1_1297, List.forall_mem_cons.2 ⟨subd10_1_1298, List.forall_mem_cons.2 ⟨subd10_1_1299, List.forall_mem_cons.2 ⟨subd10_1_1300, List.forall_mem_cons.2 ⟨subd10_1_1301, List.forall_mem_cons.2 ⟨subd10_1_1302, List.forall_mem_cons.2 ⟨subd10_1_1303, List.forall_mem_cons.2 ⟨subd10_1_1304, List.forall_mem_cons.2 ⟨subd10_1_1305, List.forall_mem_cons.2 ⟨subd10_1_1306, List.forall_mem_cons.2 ⟨subd10_1_1307, List.forall_mem_cons.2 ⟨subd10_1_1308, List.forall_mem_cons.2 ⟨subd10_1_1309, List.forall_mem_cons.2 ⟨subd10_1_1310, List.forall_mem_cons.2 ⟨subd10_1_1311, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_1312 : subd10_1 [4, -1, -8] = true := by decide +kernel
theorem subd10_1_1313 : subd10_1 [4, -1, -7] = true := by decide +kernel
theorem subd10_1_1314 : subd10_1 [4, -1, -6] = true := by decide +kernel
theorem subd10_1_1315 : subd10_1 [4, -1, -5] = true := by decide +kernel
theorem subd10_1_1316 : subd10_1 [4, -1, -4] = true := by decide +kernel
theorem subd10_1_1317 : subd10_1 [4, -1, -3] = true := by decide +kernel
theorem subd10_1_1318 : subd10_1 [4, -1, -2] = true := by decide +kernel
theorem subd10_1_1319 : subd10_1 [4, -1, -1] = true := by decide +kernel
theorem subd10_1_1320 : subd10_1 [4, -1, 0] = true := by decide +kernel
theorem subd10_1_1321 : subd10_1 [4, -1, 1] = true := by decide +kernel
theorem subd10_1_1322 : subd10_1 [4, -1, 2] = true := by decide +kernel
theorem subd10_1_1323 : subd10_1 [4, -1, 3] = true := by decide +kernel
theorem subd10_1_1324 : subd10_1 [4, -1, 4] = true := by decide +kernel
theorem subd10_1_1325 : subd10_1 [4, -1, 5] = true := by decide +kernel
theorem subd10_1_1326 : subd10_1 [4, -1, 6] = true := by decide +kernel
theorem subd10_1_1327 : subd10_1 [4, 0, -8] = true := by decide +kernel
theorem subd10_1_1328 : subd10_1 [4, 0, -7] = true := by decide +kernel
theorem subd10_1_1329 : subd10_1 [4, 0, -6] = true := by decide +kernel
theorem subd10_1_1330 : subd10_1 [4, 0, -5] = true := by decide +kernel
theorem subd10_1_1331 : subd10_1 [4, 0, -4] = true := by decide +kernel
theorem subd10_1_1332 : subd10_1 [4, 0, -3] = true := by decide +kernel
theorem subd10_1_1333 : subd10_1 [4, 0, -2] = true := by decide +kernel
theorem subd10_1_1334 : subd10_1 [4, 0, -1] = true := by decide +kernel
theorem subd10_1_1335 : subd10_1 [4, 0, 0] = true := by decide +kernel
theorem subd10_1_1336 : subd10_1 [4, 0, 1] = true := by decide +kernel
theorem subd10_1_1337 : subd10_1 [4, 0, 2] = true := by decide +kernel
theorem subd10_1_1338 : subd10_1 [4, 0, 3] = true := by decide +kernel
theorem subd10_1_1339 : subd10_1 [4, 0, 4] = true := by decide +kernel
theorem subd10_1_1340 : subd10_1 [4, 0, 5] = true := by decide +kernel
theorem subd10_1_1341 : subd10_1 [4, 0, 6] = true := by decide +kernel
theorem subd10_1_1342 : subd10_1 [4, 1, -8] = true := by decide +kernel
theorem subd10_1_1343 : subd10_1 [4, 1, -7] = true := by decide +kernel
theorem sbd10_1_41 : ∀ q ∈ blkd10_1_41, subd10_1 q = true := by
  unfold blkd10_1_41
  exact List.forall_mem_cons.2 ⟨subd10_1_1312, List.forall_mem_cons.2 ⟨subd10_1_1313, List.forall_mem_cons.2 ⟨subd10_1_1314, List.forall_mem_cons.2 ⟨subd10_1_1315, List.forall_mem_cons.2 ⟨subd10_1_1316, List.forall_mem_cons.2 ⟨subd10_1_1317, List.forall_mem_cons.2 ⟨subd10_1_1318, List.forall_mem_cons.2 ⟨subd10_1_1319, List.forall_mem_cons.2 ⟨subd10_1_1320, List.forall_mem_cons.2 ⟨subd10_1_1321, List.forall_mem_cons.2 ⟨subd10_1_1322, List.forall_mem_cons.2 ⟨subd10_1_1323, List.forall_mem_cons.2 ⟨subd10_1_1324, List.forall_mem_cons.2 ⟨subd10_1_1325, List.forall_mem_cons.2 ⟨subd10_1_1326, List.forall_mem_cons.2 ⟨subd10_1_1327, List.forall_mem_cons.2 ⟨subd10_1_1328, List.forall_mem_cons.2 ⟨subd10_1_1329, List.forall_mem_cons.2 ⟨subd10_1_1330, List.forall_mem_cons.2 ⟨subd10_1_1331, List.forall_mem_cons.2 ⟨subd10_1_1332, List.forall_mem_cons.2 ⟨subd10_1_1333, List.forall_mem_cons.2 ⟨subd10_1_1334, List.forall_mem_cons.2 ⟨subd10_1_1335, List.forall_mem_cons.2 ⟨subd10_1_1336, List.forall_mem_cons.2 ⟨subd10_1_1337, List.forall_mem_cons.2 ⟨subd10_1_1338, List.forall_mem_cons.2 ⟨subd10_1_1339, List.forall_mem_cons.2 ⟨subd10_1_1340, List.forall_mem_cons.2 ⟨subd10_1_1341, List.forall_mem_cons.2 ⟨subd10_1_1342, List.forall_mem_cons.2 ⟨subd10_1_1343, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_1344 : subd10_1 [4, 1, -6] = true := by decide +kernel
theorem subd10_1_1345 : subd10_1 [4, 1, -5] = true := by decide +kernel
theorem subd10_1_1346 : subd10_1 [4, 1, -4] = true := by decide +kernel
theorem subd10_1_1347 : subd10_1 [4, 1, -3] = true := by decide +kernel
theorem subd10_1_1348 : subd10_1 [4, 1, -2] = true := by decide +kernel
theorem subd10_1_1349 : subd10_1 [4, 1, -1] = true := by decide +kernel
theorem subd10_1_1350 : subd10_1 [4, 1, 0] = true := by decide +kernel
theorem subd10_1_1351 : subd10_1 [4, 1, 1] = true := by decide +kernel
theorem subd10_1_1352 : subd10_1 [4, 1, 2] = true := by decide +kernel
theorem subd10_1_1353 : subd10_1 [4, 1, 3] = true := by decide +kernel
theorem subd10_1_1354 : subd10_1 [4, 1, 4] = true := by decide +kernel
theorem subd10_1_1355 : subd10_1 [4, 1, 5] = true := by decide +kernel
theorem subd10_1_1356 : subd10_1 [4, 2] = true := by decide +kernel
theorem subd10_1_1357 : subd10_1 [4, 3] = true := by decide +kernel
theorem subd10_1_1358 : subd10_1 [4, 4] = true := by decide +kernel
theorem subd10_1_1359 : subd10_1 [4, 5] = true := by decide +kernel
theorem subd10_1_1360 : subd10_1 [5, -9] = true := by decide +kernel
theorem subd10_1_1361 : subd10_1 [5, -8] = true := by decide +kernel
theorem subd10_1_1362 : subd10_1 [5, -7] = true := by decide +kernel
theorem subd10_1_1363 : subd10_1 [5, -6] = true := by decide +kernel
theorem subd10_1_1364 : subd10_1 [5, -5] = true := by decide +kernel
theorem subd10_1_1365 : subd10_1 [5, -4] = true := by decide +kernel
theorem subd10_1_1366 : subd10_1 [5, -3] = true := by decide +kernel
theorem subd10_1_1367 : subd10_1 [5, -2] = true := by decide +kernel
theorem subd10_1_1368 : subd10_1 [5, -1] = true := by decide +kernel
theorem subd10_1_1369 : subd10_1 [5, 0] = true := by decide +kernel
theorem subd10_1_1370 : subd10_1 [5, 1] = true := by decide +kernel
theorem subd10_1_1371 : subd10_1 [5, 2] = true := by decide +kernel
theorem subd10_1_1372 : subd10_1 [5, 3] = true := by decide +kernel
theorem subd10_1_1373 : subd10_1 [5, 4] = true := by decide +kernel
theorem subd10_1_1374 : subd10_1 [6, -8] = true := by decide +kernel
theorem subd10_1_1375 : subd10_1 [6, -7] = true := by decide +kernel
theorem sbd10_1_42 : ∀ q ∈ blkd10_1_42, subd10_1 q = true := by
  unfold blkd10_1_42
  exact List.forall_mem_cons.2 ⟨subd10_1_1344, List.forall_mem_cons.2 ⟨subd10_1_1345, List.forall_mem_cons.2 ⟨subd10_1_1346, List.forall_mem_cons.2 ⟨subd10_1_1347, List.forall_mem_cons.2 ⟨subd10_1_1348, List.forall_mem_cons.2 ⟨subd10_1_1349, List.forall_mem_cons.2 ⟨subd10_1_1350, List.forall_mem_cons.2 ⟨subd10_1_1351, List.forall_mem_cons.2 ⟨subd10_1_1352, List.forall_mem_cons.2 ⟨subd10_1_1353, List.forall_mem_cons.2 ⟨subd10_1_1354, List.forall_mem_cons.2 ⟨subd10_1_1355, List.forall_mem_cons.2 ⟨subd10_1_1356, List.forall_mem_cons.2 ⟨subd10_1_1357, List.forall_mem_cons.2 ⟨subd10_1_1358, List.forall_mem_cons.2 ⟨subd10_1_1359, List.forall_mem_cons.2 ⟨subd10_1_1360, List.forall_mem_cons.2 ⟨subd10_1_1361, List.forall_mem_cons.2 ⟨subd10_1_1362, List.forall_mem_cons.2 ⟨subd10_1_1363, List.forall_mem_cons.2 ⟨subd10_1_1364, List.forall_mem_cons.2 ⟨subd10_1_1365, List.forall_mem_cons.2 ⟨subd10_1_1366, List.forall_mem_cons.2 ⟨subd10_1_1367, List.forall_mem_cons.2 ⟨subd10_1_1368, List.forall_mem_cons.2 ⟨subd10_1_1369, List.forall_mem_cons.2 ⟨subd10_1_1370, List.forall_mem_cons.2 ⟨subd10_1_1371, List.forall_mem_cons.2 ⟨subd10_1_1372, List.forall_mem_cons.2 ⟨subd10_1_1373, List.forall_mem_cons.2 ⟨subd10_1_1374, List.forall_mem_cons.2 ⟨subd10_1_1375, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_1376 : subd10_1 [6, -6] = true := by decide +kernel
theorem subd10_1_1377 : subd10_1 [6, -5] = true := by decide +kernel
theorem subd10_1_1378 : subd10_1 [6, -4] = true := by decide +kernel
theorem subd10_1_1379 : subd10_1 [6, -3] = true := by decide +kernel
theorem subd10_1_1380 : subd10_1 [6, -2] = true := by decide +kernel
theorem subd10_1_1381 : subd10_1 [6, -1] = true := by decide +kernel
theorem subd10_1_1382 : subd10_1 [6, 0] = true := by decide +kernel
theorem subd10_1_1383 : subd10_1 [6, 1] = true := by decide +kernel
theorem subd10_1_1384 : subd10_1 [6, 2] = true := by decide +kernel
theorem subd10_1_1385 : subd10_1 [7, -7] = true := by decide +kernel
theorem subd10_1_1386 : subd10_1 [7, -6] = true := by decide +kernel
theorem subd10_1_1387 : subd10_1 [7, -5] = true := by decide +kernel
theorem subd10_1_1388 : subd10_1 [7, -4] = true := by decide +kernel
theorem subd10_1_1389 : subd10_1 [7, -3] = true := by decide +kernel
theorem subd10_1_1390 : subd10_1 [7, -2] = true := by decide +kernel
theorem subd10_1_1391 : subd10_1 [7, -1] = true := by decide +kernel
theorem subd10_1_1392 : subd10_1 [7, 0] = true := by decide +kernel
theorem sbd10_1_43 : ∀ q ∈ blkd10_1_43, subd10_1 q = true := by
  unfold blkd10_1_43
  exact List.forall_mem_cons.2 ⟨subd10_1_1376, List.forall_mem_cons.2 ⟨subd10_1_1377, List.forall_mem_cons.2 ⟨subd10_1_1378, List.forall_mem_cons.2 ⟨subd10_1_1379, List.forall_mem_cons.2 ⟨subd10_1_1380, List.forall_mem_cons.2 ⟨subd10_1_1381, List.forall_mem_cons.2 ⟨subd10_1_1382, List.forall_mem_cons.2 ⟨subd10_1_1383, List.forall_mem_cons.2 ⟨subd10_1_1384, List.forall_mem_cons.2 ⟨subd10_1_1385, List.forall_mem_cons.2 ⟨subd10_1_1386, List.forall_mem_cons.2 ⟨subd10_1_1387, List.forall_mem_cons.2 ⟨subd10_1_1388, List.forall_mem_cons.2 ⟨subd10_1_1389, List.forall_mem_cons.2 ⟨subd10_1_1390, List.forall_mem_cons.2 ⟨subd10_1_1391, List.forall_mem_cons.2 ⟨subd10_1_1392, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C116
