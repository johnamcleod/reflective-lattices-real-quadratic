import ReflectZphi.Data.Cert5.C121.Base

namespace ReflectZphi.Data.Cert5.C121

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd4_2_1152 : subd4_2 [2, 3, -2] = true := by decide +kernel
theorem subd4_2_1153 : subd4_2 [2, 3, -1] = true := by decide +kernel
theorem subd4_2_1154 : subd4_2 [2, 3, 0] = true := by decide +kernel
theorem subd4_2_1155 : subd4_2 [2, 3, 1] = true := by decide +kernel
theorem subd4_2_1156 : subd4_2 [2, 3, 2] = true := by decide +kernel
theorem subd4_2_1157 : subd4_2 [2, 3, 3] = true := by decide +kernel
theorem subd4_2_1158 : subd4_2 [2, 3, 4] = true := by decide +kernel
theorem subd4_2_1159 : subd4_2 [2, 3, 5] = true := by decide +kernel
theorem subd4_2_1160 : subd4_2 [2, 3, 6] = true := by decide +kernel
theorem subd4_2_1161 : subd4_2 [2, 3, 7] = true := by decide +kernel
theorem subd4_2_1162 : subd4_2 [2, 3, 8] = true := by decide +kernel
theorem subd4_2_1163 : subd4_2 [2, 3, 9] = true := by decide +kernel
theorem subd4_2_1164 : subd4_2 [2, 4, -8] = true := by decide +kernel
theorem subd4_2_1165 : subd4_2 [2, 4, -7] = true := by decide +kernel
theorem subd4_2_1166 : subd4_2 [2, 4, -6] = true := by decide +kernel
theorem subd4_2_1167 : subd4_2 [2, 4, -5] = true := by decide +kernel
theorem subd4_2_1168 : subd4_2 [2, 4, -4] = true := by decide +kernel
theorem subd4_2_1169 : subd4_2 [2, 4, -3] = true := by decide +kernel
theorem subd4_2_1170 : subd4_2 [2, 4, -2] = true := by decide +kernel
theorem subd4_2_1171 : subd4_2 [2, 4, -1] = true := by decide +kernel
theorem subd4_2_1172 : subd4_2 [2, 4, 0] = true := by decide +kernel
theorem subd4_2_1173 : subd4_2 [2, 4, 1] = true := by decide +kernel
theorem subd4_2_1174 : subd4_2 [2, 4, 2] = true := by decide +kernel
theorem subd4_2_1175 : subd4_2 [2, 4, 3] = true := by decide +kernel
theorem subd4_2_1176 : subd4_2 [2, 4, 4] = true := by decide +kernel
theorem subd4_2_1177 : subd4_2 [2, 4, 5] = true := by decide +kernel
theorem subd4_2_1178 : subd4_2 [2, 4, 6] = true := by decide +kernel
theorem subd4_2_1179 : subd4_2 [2, 4, 7] = true := by decide +kernel
theorem subd4_2_1180 : subd4_2 [2, 4, 8] = true := by decide +kernel
theorem subd4_2_1181 : subd4_2 [2, 4, 9] = true := by decide +kernel
theorem subd4_2_1182 : subd4_2 [2, 5, -6] = true := by decide +kernel
theorem subd4_2_1183 : subd4_2 [2, 5, -5] = true := by decide +kernel
theorem sbd4_2_36 : ∀ q ∈ blkd4_2_36, subd4_2 q = true := by
  unfold blkd4_2_36
  exact List.forall_mem_cons.2 ⟨subd4_2_1152, List.forall_mem_cons.2 ⟨subd4_2_1153, List.forall_mem_cons.2 ⟨subd4_2_1154, List.forall_mem_cons.2 ⟨subd4_2_1155, List.forall_mem_cons.2 ⟨subd4_2_1156, List.forall_mem_cons.2 ⟨subd4_2_1157, List.forall_mem_cons.2 ⟨subd4_2_1158, List.forall_mem_cons.2 ⟨subd4_2_1159, List.forall_mem_cons.2 ⟨subd4_2_1160, List.forall_mem_cons.2 ⟨subd4_2_1161, List.forall_mem_cons.2 ⟨subd4_2_1162, List.forall_mem_cons.2 ⟨subd4_2_1163, List.forall_mem_cons.2 ⟨subd4_2_1164, List.forall_mem_cons.2 ⟨subd4_2_1165, List.forall_mem_cons.2 ⟨subd4_2_1166, List.forall_mem_cons.2 ⟨subd4_2_1167, List.forall_mem_cons.2 ⟨subd4_2_1168, List.forall_mem_cons.2 ⟨subd4_2_1169, List.forall_mem_cons.2 ⟨subd4_2_1170, List.forall_mem_cons.2 ⟨subd4_2_1171, List.forall_mem_cons.2 ⟨subd4_2_1172, List.forall_mem_cons.2 ⟨subd4_2_1173, List.forall_mem_cons.2 ⟨subd4_2_1174, List.forall_mem_cons.2 ⟨subd4_2_1175, List.forall_mem_cons.2 ⟨subd4_2_1176, List.forall_mem_cons.2 ⟨subd4_2_1177, List.forall_mem_cons.2 ⟨subd4_2_1178, List.forall_mem_cons.2 ⟨subd4_2_1179, List.forall_mem_cons.2 ⟨subd4_2_1180, List.forall_mem_cons.2 ⟨subd4_2_1181, List.forall_mem_cons.2 ⟨subd4_2_1182, List.forall_mem_cons.2 ⟨subd4_2_1183, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_2_1184 : subd4_2 [2, 5, -4] = true := by decide +kernel
theorem subd4_2_1185 : subd4_2 [2, 5, -3] = true := by decide +kernel
theorem subd4_2_1186 : subd4_2 [2, 5, -2] = true := by decide +kernel
theorem subd4_2_1187 : subd4_2 [2, 5, -1] = true := by decide +kernel
theorem subd4_2_1188 : subd4_2 [2, 5, 0] = true := by decide +kernel
theorem subd4_2_1189 : subd4_2 [2, 5, 1] = true := by decide +kernel
theorem subd4_2_1190 : subd4_2 [2, 5, 2] = true := by decide +kernel
theorem subd4_2_1191 : subd4_2 [2, 5, 3] = true := by decide +kernel
theorem subd4_2_1192 : subd4_2 [2, 5, 4] = true := by decide +kernel
theorem subd4_2_1193 : subd4_2 [2, 5, 5] = true := by decide +kernel
theorem subd4_2_1194 : subd4_2 [2, 5, 6] = true := by decide +kernel
theorem subd4_2_1195 : subd4_2 [2, 5, 7] = true := by decide +kernel
theorem subd4_2_1196 : subd4_2 [2, 5, 8] = true := by decide +kernel
theorem subd4_2_1197 : subd4_2 [2, 6] = true := by decide +kernel
theorem subd4_2_1198 : subd4_2 [2, 7] = true := by decide +kernel
theorem subd4_2_1199 : subd4_2 [3, -6] = true := by decide +kernel
theorem subd4_2_1200 : subd4_2 [3, -5] = true := by decide +kernel
theorem subd4_2_1201 : subd4_2 [3, -4] = true := by decide +kernel
theorem subd4_2_1202 : subd4_2 [3, -3] = true := by decide +kernel
theorem subd4_2_1203 : subd4_2 [3, -2, -8] = true := by decide +kernel
theorem subd4_2_1204 : subd4_2 [3, -2, -7] = true := by decide +kernel
theorem subd4_2_1205 : subd4_2 [3, -2, -6] = true := by decide +kernel
theorem subd4_2_1206 : subd4_2 [3, -2, -5] = true := by decide +kernel
theorem subd4_2_1207 : subd4_2 [3, -2, -4] = true := by decide +kernel
theorem subd4_2_1208 : subd4_2 [3, -2, -3] = true := by decide +kernel
theorem subd4_2_1209 : subd4_2 [3, -2, -2] = true := by decide +kernel
theorem subd4_2_1210 : subd4_2 [3, -2, -1] = true := by decide +kernel
theorem subd4_2_1211 : subd4_2 [3, -2, 0] = true := by decide +kernel
theorem subd4_2_1212 : subd4_2 [3, -2, 1] = true := by decide +kernel
theorem subd4_2_1213 : subd4_2 [3, -2, 2] = true := by decide +kernel
theorem subd4_2_1214 : subd4_2 [3, -2, 3] = true := by decide +kernel
theorem subd4_2_1215 : subd4_2 [3, -2, 4] = true := by decide +kernel
theorem sbd4_2_37 : ∀ q ∈ blkd4_2_37, subd4_2 q = true := by
  unfold blkd4_2_37
  exact List.forall_mem_cons.2 ⟨subd4_2_1184, List.forall_mem_cons.2 ⟨subd4_2_1185, List.forall_mem_cons.2 ⟨subd4_2_1186, List.forall_mem_cons.2 ⟨subd4_2_1187, List.forall_mem_cons.2 ⟨subd4_2_1188, List.forall_mem_cons.2 ⟨subd4_2_1189, List.forall_mem_cons.2 ⟨subd4_2_1190, List.forall_mem_cons.2 ⟨subd4_2_1191, List.forall_mem_cons.2 ⟨subd4_2_1192, List.forall_mem_cons.2 ⟨subd4_2_1193, List.forall_mem_cons.2 ⟨subd4_2_1194, List.forall_mem_cons.2 ⟨subd4_2_1195, List.forall_mem_cons.2 ⟨subd4_2_1196, List.forall_mem_cons.2 ⟨subd4_2_1197, List.forall_mem_cons.2 ⟨subd4_2_1198, List.forall_mem_cons.2 ⟨subd4_2_1199, List.forall_mem_cons.2 ⟨subd4_2_1200, List.forall_mem_cons.2 ⟨subd4_2_1201, List.forall_mem_cons.2 ⟨subd4_2_1202, List.forall_mem_cons.2 ⟨subd4_2_1203, List.forall_mem_cons.2 ⟨subd4_2_1204, List.forall_mem_cons.2 ⟨subd4_2_1205, List.forall_mem_cons.2 ⟨subd4_2_1206, List.forall_mem_cons.2 ⟨subd4_2_1207, List.forall_mem_cons.2 ⟨subd4_2_1208, List.forall_mem_cons.2 ⟨subd4_2_1209, List.forall_mem_cons.2 ⟨subd4_2_1210, List.forall_mem_cons.2 ⟨subd4_2_1211, List.forall_mem_cons.2 ⟨subd4_2_1212, List.forall_mem_cons.2 ⟨subd4_2_1213, List.forall_mem_cons.2 ⟨subd4_2_1214, List.forall_mem_cons.2 ⟨subd4_2_1215, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_2_1216 : subd4_2 [3, -2, 5] = true := by decide +kernel
theorem subd4_2_1217 : subd4_2 [3, -2, 6] = true := by decide +kernel
theorem subd4_2_1218 : subd4_2 [3, -2, 7] = true := by decide +kernel
theorem subd4_2_1219 : subd4_2 [3, -1, -9] = true := by decide +kernel
theorem subd4_2_1220 : subd4_2 [3, -1, -8] = true := by decide +kernel
theorem subd4_2_1221 : subd4_2 [3, -1, -7] = true := by decide +kernel
theorem subd4_2_1222 : subd4_2 [3, -1, -6] = true := by decide +kernel
theorem subd4_2_1223 : subd4_2 [3, -1, -5] = true := by decide +kernel
theorem subd4_2_1224 : subd4_2 [3, -1, -4] = true := by decide +kernel
theorem subd4_2_1225 : subd4_2 [3, -1, -3] = true := by decide +kernel
theorem subd4_2_1226 : subd4_2 [3, -1, -2] = true := by decide +kernel
theorem subd4_2_1227 : subd4_2 [3, -1, -1] = true := by decide +kernel
theorem subd4_2_1228 : subd4_2 [3, -1, 0] = true := by decide +kernel
theorem subd4_2_1229 : subd4_2 [3, -1, 1] = true := by decide +kernel
theorem subd4_2_1230 : subd4_2 [3, -1, 2] = true := by decide +kernel
theorem subd4_2_1231 : subd4_2 [3, -1, 3] = true := by decide +kernel
theorem subd4_2_1232 : subd4_2 [3, -1, 4] = true := by decide +kernel
theorem subd4_2_1233 : subd4_2 [3, -1, 5] = true := by decide +kernel
theorem subd4_2_1234 : subd4_2 [3, -1, 6] = true := by decide +kernel
theorem subd4_2_1235 : subd4_2 [3, -1, 7] = true := by decide +kernel
theorem subd4_2_1236 : subd4_2 [3, 0, -9] = true := by decide +kernel
theorem subd4_2_1237 : subd4_2 [3, 0, -8] = true := by decide +kernel
theorem subd4_2_1238 : subd4_2 [3, 0, -7] = true := by decide +kernel
theorem subd4_2_1239 : subd4_2 [3, 0, -6] = true := by decide +kernel
theorem subd4_2_1240 : subd4_2 [3, 0, -5] = true := by decide +kernel
theorem subd4_2_1241 : subd4_2 [3, 0, -4] = true := by decide +kernel
theorem subd4_2_1242 : subd4_2 [3, 0, -3] = true := by decide +kernel
theorem subd4_2_1243 : subd4_2 [3, 0, -2] = true := by decide +kernel
theorem subd4_2_1244 : subd4_2 [3, 0, -1] = true := by decide +kernel
theorem subd4_2_1245 : subd4_2 [3, 0, 0] = true := by decide +kernel
theorem subd4_2_1246 : subd4_2 [3, 0, 1] = true := by decide +kernel
theorem subd4_2_1247 : subd4_2 [3, 0, 2] = true := by decide +kernel
theorem sbd4_2_38 : ∀ q ∈ blkd4_2_38, subd4_2 q = true := by
  unfold blkd4_2_38
  exact List.forall_mem_cons.2 ⟨subd4_2_1216, List.forall_mem_cons.2 ⟨subd4_2_1217, List.forall_mem_cons.2 ⟨subd4_2_1218, List.forall_mem_cons.2 ⟨subd4_2_1219, List.forall_mem_cons.2 ⟨subd4_2_1220, List.forall_mem_cons.2 ⟨subd4_2_1221, List.forall_mem_cons.2 ⟨subd4_2_1222, List.forall_mem_cons.2 ⟨subd4_2_1223, List.forall_mem_cons.2 ⟨subd4_2_1224, List.forall_mem_cons.2 ⟨subd4_2_1225, List.forall_mem_cons.2 ⟨subd4_2_1226, List.forall_mem_cons.2 ⟨subd4_2_1227, List.forall_mem_cons.2 ⟨subd4_2_1228, List.forall_mem_cons.2 ⟨subd4_2_1229, List.forall_mem_cons.2 ⟨subd4_2_1230, List.forall_mem_cons.2 ⟨subd4_2_1231, List.forall_mem_cons.2 ⟨subd4_2_1232, List.forall_mem_cons.2 ⟨subd4_2_1233, List.forall_mem_cons.2 ⟨subd4_2_1234, List.forall_mem_cons.2 ⟨subd4_2_1235, List.forall_mem_cons.2 ⟨subd4_2_1236, List.forall_mem_cons.2 ⟨subd4_2_1237, List.forall_mem_cons.2 ⟨subd4_2_1238, List.forall_mem_cons.2 ⟨subd4_2_1239, List.forall_mem_cons.2 ⟨subd4_2_1240, List.forall_mem_cons.2 ⟨subd4_2_1241, List.forall_mem_cons.2 ⟨subd4_2_1242, List.forall_mem_cons.2 ⟨subd4_2_1243, List.forall_mem_cons.2 ⟨subd4_2_1244, List.forall_mem_cons.2 ⟨subd4_2_1245, List.forall_mem_cons.2 ⟨subd4_2_1246, List.forall_mem_cons.2 ⟨subd4_2_1247, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_2_1248 : subd4_2 [3, 0, 3] = true := by decide +kernel
theorem subd4_2_1249 : subd4_2 [3, 0, 4] = true := by decide +kernel
theorem subd4_2_1250 : subd4_2 [3, 0, 5] = true := by decide +kernel
theorem subd4_2_1251 : subd4_2 [3, 0, 6] = true := by decide +kernel
theorem subd4_2_1252 : subd4_2 [3, 0, 7] = true := by decide +kernel
theorem subd4_2_1253 : subd4_2 [3, 0, 8] = true := by decide +kernel
theorem subd4_2_1254 : subd4_2 [3, 1, -9] = true := by decide +kernel
theorem subd4_2_1255 : subd4_2 [3, 1, -8] = true := by decide +kernel
theorem subd4_2_1256 : subd4_2 [3, 1, -7] = true := by decide +kernel
theorem subd4_2_1257 : subd4_2 [3, 1, -6] = true := by decide +kernel
theorem subd4_2_1258 : subd4_2 [3, 1, -5] = true := by decide +kernel
theorem subd4_2_1259 : subd4_2 [3, 1, -4] = true := by decide +kernel
theorem subd4_2_1260 : subd4_2 [3, 1, -3] = true := by decide +kernel
theorem subd4_2_1261 : subd4_2 [3, 1, -2] = true := by decide +kernel
theorem subd4_2_1262 : subd4_2 [3, 1, -1] = true := by decide +kernel
theorem subd4_2_1263 : subd4_2 [3, 1, 0] = true := by decide +kernel
theorem subd4_2_1264 : subd4_2 [3, 1, 1] = true := by decide +kernel
theorem subd4_2_1265 : subd4_2 [3, 1, 2] = true := by decide +kernel
theorem subd4_2_1266 : subd4_2 [3, 1, 3] = true := by decide +kernel
theorem subd4_2_1267 : subd4_2 [3, 1, 4] = true := by decide +kernel
theorem subd4_2_1268 : subd4_2 [3, 1, 5] = true := by decide +kernel
theorem subd4_2_1269 : subd4_2 [3, 1, 6] = true := by decide +kernel
theorem subd4_2_1270 : subd4_2 [3, 1, 7] = true := by decide +kernel
theorem subd4_2_1271 : subd4_2 [3, 1, 8] = true := by decide +kernel
theorem subd4_2_1272 : subd4_2 [3, 1, 9] = true := by decide +kernel
theorem subd4_2_1273 : subd4_2 [3, 2, -8] = true := by decide +kernel
theorem subd4_2_1274 : subd4_2 [3, 2, -7] = true := by decide +kernel
theorem subd4_2_1275 : subd4_2 [3, 2, -6] = true := by decide +kernel
theorem subd4_2_1276 : subd4_2 [3, 2, -5] = true := by decide +kernel
theorem subd4_2_1277 : subd4_2 [3, 2, -4] = true := by decide +kernel
theorem subd4_2_1278 : subd4_2 [3, 2, -3] = true := by decide +kernel
theorem subd4_2_1279 : subd4_2 [3, 2, -2] = true := by decide +kernel
theorem sbd4_2_39 : ∀ q ∈ blkd4_2_39, subd4_2 q = true := by
  unfold blkd4_2_39
  exact List.forall_mem_cons.2 ⟨subd4_2_1248, List.forall_mem_cons.2 ⟨subd4_2_1249, List.forall_mem_cons.2 ⟨subd4_2_1250, List.forall_mem_cons.2 ⟨subd4_2_1251, List.forall_mem_cons.2 ⟨subd4_2_1252, List.forall_mem_cons.2 ⟨subd4_2_1253, List.forall_mem_cons.2 ⟨subd4_2_1254, List.forall_mem_cons.2 ⟨subd4_2_1255, List.forall_mem_cons.2 ⟨subd4_2_1256, List.forall_mem_cons.2 ⟨subd4_2_1257, List.forall_mem_cons.2 ⟨subd4_2_1258, List.forall_mem_cons.2 ⟨subd4_2_1259, List.forall_mem_cons.2 ⟨subd4_2_1260, List.forall_mem_cons.2 ⟨subd4_2_1261, List.forall_mem_cons.2 ⟨subd4_2_1262, List.forall_mem_cons.2 ⟨subd4_2_1263, List.forall_mem_cons.2 ⟨subd4_2_1264, List.forall_mem_cons.2 ⟨subd4_2_1265, List.forall_mem_cons.2 ⟨subd4_2_1266, List.forall_mem_cons.2 ⟨subd4_2_1267, List.forall_mem_cons.2 ⟨subd4_2_1268, List.forall_mem_cons.2 ⟨subd4_2_1269, List.forall_mem_cons.2 ⟨subd4_2_1270, List.forall_mem_cons.2 ⟨subd4_2_1271, List.forall_mem_cons.2 ⟨subd4_2_1272, List.forall_mem_cons.2 ⟨subd4_2_1273, List.forall_mem_cons.2 ⟨subd4_2_1274, List.forall_mem_cons.2 ⟨subd4_2_1275, List.forall_mem_cons.2 ⟨subd4_2_1276, List.forall_mem_cons.2 ⟨subd4_2_1277, List.forall_mem_cons.2 ⟨subd4_2_1278, List.forall_mem_cons.2 ⟨subd4_2_1279, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_2_1280 : subd4_2 [3, 2, -1] = true := by decide +kernel
theorem subd4_2_1281 : subd4_2 [3, 2, 0] = true := by decide +kernel
theorem subd4_2_1282 : subd4_2 [3, 2, 1] = true := by decide +kernel
theorem subd4_2_1283 : subd4_2 [3, 2, 2] = true := by decide +kernel
theorem subd4_2_1284 : subd4_2 [3, 2, 3] = true := by decide +kernel
theorem subd4_2_1285 : subd4_2 [3, 2, 4] = true := by decide +kernel
theorem subd4_2_1286 : subd4_2 [3, 2, 5] = true := by decide +kernel
theorem subd4_2_1287 : subd4_2 [3, 2, 6] = true := by decide +kernel
theorem subd4_2_1288 : subd4_2 [3, 2, 7] = true := by decide +kernel
theorem subd4_2_1289 : subd4_2 [3, 2, 8] = true := by decide +kernel
theorem subd4_2_1290 : subd4_2 [3, 2, 9] = true := by decide +kernel
theorem subd4_2_1291 : subd4_2 [3, 3, -8] = true := by decide +kernel
theorem subd4_2_1292 : subd4_2 [3, 3, -7] = true := by decide +kernel
theorem subd4_2_1293 : subd4_2 [3, 3, -6] = true := by decide +kernel
theorem subd4_2_1294 : subd4_2 [3, 3, -5] = true := by decide +kernel
theorem subd4_2_1295 : subd4_2 [3, 3, -4] = true := by decide +kernel
theorem subd4_2_1296 : subd4_2 [3, 3, -3] = true := by decide +kernel
theorem subd4_2_1297 : subd4_2 [3, 3, -2] = true := by decide +kernel
theorem subd4_2_1298 : subd4_2 [3, 3, -1] = true := by decide +kernel
theorem subd4_2_1299 : subd4_2 [3, 3, 0] = true := by decide +kernel
theorem subd4_2_1300 : subd4_2 [3, 3, 1] = true := by decide +kernel
theorem subd4_2_1301 : subd4_2 [3, 3, 2] = true := by decide +kernel
theorem subd4_2_1302 : subd4_2 [3, 3, 3] = true := by decide +kernel
theorem subd4_2_1303 : subd4_2 [3, 3, 4] = true := by decide +kernel
theorem subd4_2_1304 : subd4_2 [3, 3, 5] = true := by decide +kernel
theorem subd4_2_1305 : subd4_2 [3, 3, 6] = true := by decide +kernel
theorem subd4_2_1306 : subd4_2 [3, 3, 7] = true := by decide +kernel
theorem subd4_2_1307 : subd4_2 [3, 3, 8] = true := by decide +kernel
theorem subd4_2_1308 : subd4_2 [3, 3, 9] = true := by decide +kernel
theorem subd4_2_1309 : subd4_2 [3, 4, -7] = true := by decide +kernel
theorem subd4_2_1310 : subd4_2 [3, 4, -6] = true := by decide +kernel
theorem subd4_2_1311 : subd4_2 [3, 4, -5] = true := by decide +kernel
theorem sbd4_2_40 : ∀ q ∈ blkd4_2_40, subd4_2 q = true := by
  unfold blkd4_2_40
  exact List.forall_mem_cons.2 ⟨subd4_2_1280, List.forall_mem_cons.2 ⟨subd4_2_1281, List.forall_mem_cons.2 ⟨subd4_2_1282, List.forall_mem_cons.2 ⟨subd4_2_1283, List.forall_mem_cons.2 ⟨subd4_2_1284, List.forall_mem_cons.2 ⟨subd4_2_1285, List.forall_mem_cons.2 ⟨subd4_2_1286, List.forall_mem_cons.2 ⟨subd4_2_1287, List.forall_mem_cons.2 ⟨subd4_2_1288, List.forall_mem_cons.2 ⟨subd4_2_1289, List.forall_mem_cons.2 ⟨subd4_2_1290, List.forall_mem_cons.2 ⟨subd4_2_1291, List.forall_mem_cons.2 ⟨subd4_2_1292, List.forall_mem_cons.2 ⟨subd4_2_1293, List.forall_mem_cons.2 ⟨subd4_2_1294, List.forall_mem_cons.2 ⟨subd4_2_1295, List.forall_mem_cons.2 ⟨subd4_2_1296, List.forall_mem_cons.2 ⟨subd4_2_1297, List.forall_mem_cons.2 ⟨subd4_2_1298, List.forall_mem_cons.2 ⟨subd4_2_1299, List.forall_mem_cons.2 ⟨subd4_2_1300, List.forall_mem_cons.2 ⟨subd4_2_1301, List.forall_mem_cons.2 ⟨subd4_2_1302, List.forall_mem_cons.2 ⟨subd4_2_1303, List.forall_mem_cons.2 ⟨subd4_2_1304, List.forall_mem_cons.2 ⟨subd4_2_1305, List.forall_mem_cons.2 ⟨subd4_2_1306, List.forall_mem_cons.2 ⟨subd4_2_1307, List.forall_mem_cons.2 ⟨subd4_2_1308, List.forall_mem_cons.2 ⟨subd4_2_1309, List.forall_mem_cons.2 ⟨subd4_2_1310, List.forall_mem_cons.2 ⟨subd4_2_1311, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_2_1312 : subd4_2 [3, 4, -4] = true := by decide +kernel
theorem subd4_2_1313 : subd4_2 [3, 4, -3] = true := by decide +kernel
theorem subd4_2_1314 : subd4_2 [3, 4, -2] = true := by decide +kernel
theorem subd4_2_1315 : subd4_2 [3, 4, -1] = true := by decide +kernel
theorem subd4_2_1316 : subd4_2 [3, 4, 0] = true := by decide +kernel
theorem subd4_2_1317 : subd4_2 [3, 4, 1] = true := by decide +kernel
theorem subd4_2_1318 : subd4_2 [3, 4, 2] = true := by decide +kernel
theorem subd4_2_1319 : subd4_2 [3, 4, 3] = true := by decide +kernel
theorem subd4_2_1320 : subd4_2 [3, 4, 4] = true := by decide +kernel
theorem subd4_2_1321 : subd4_2 [3, 4, 5] = true := by decide +kernel
theorem subd4_2_1322 : subd4_2 [3, 4, 6] = true := by decide +kernel
theorem subd4_2_1323 : subd4_2 [3, 4, 7] = true := by decide +kernel
theorem subd4_2_1324 : subd4_2 [3, 4, 8] = true := by decide +kernel
theorem subd4_2_1325 : subd4_2 [3, 5, -6] = true := by decide +kernel
theorem subd4_2_1326 : subd4_2 [3, 5, -5] = true := by decide +kernel
theorem subd4_2_1327 : subd4_2 [3, 5, -4] = true := by decide +kernel
theorem subd4_2_1328 : subd4_2 [3, 5, -3] = true := by decide +kernel
theorem subd4_2_1329 : subd4_2 [3, 5, -2] = true := by decide +kernel
theorem subd4_2_1330 : subd4_2 [3, 5, -1] = true := by decide +kernel
theorem subd4_2_1331 : subd4_2 [3, 5, 0] = true := by decide +kernel
theorem subd4_2_1332 : subd4_2 [3, 5, 1] = true := by decide +kernel
theorem subd4_2_1333 : subd4_2 [3, 5, 2] = true := by decide +kernel
theorem subd4_2_1334 : subd4_2 [3, 5, 3] = true := by decide +kernel
theorem subd4_2_1335 : subd4_2 [3, 5, 4] = true := by decide +kernel
theorem subd4_2_1336 : subd4_2 [3, 5, 5] = true := by decide +kernel
theorem subd4_2_1337 : subd4_2 [3, 5, 6] = true := by decide +kernel
theorem subd4_2_1338 : subd4_2 [3, 5, 7] = true := by decide +kernel
theorem subd4_2_1339 : subd4_2 [3, 5, 8] = true := by decide +kernel
theorem subd4_2_1340 : subd4_2 [3, 6] = true := by decide +kernel
theorem subd4_2_1341 : subd4_2 [3, 7] = true := by decide +kernel
theorem subd4_2_1342 : subd4_2 [4, -4] = true := by decide +kernel
theorem subd4_2_1343 : subd4_2 [4, -3] = true := by decide +kernel
theorem sbd4_2_41 : ∀ q ∈ blkd4_2_41, subd4_2 q = true := by
  unfold blkd4_2_41
  exact List.forall_mem_cons.2 ⟨subd4_2_1312, List.forall_mem_cons.2 ⟨subd4_2_1313, List.forall_mem_cons.2 ⟨subd4_2_1314, List.forall_mem_cons.2 ⟨subd4_2_1315, List.forall_mem_cons.2 ⟨subd4_2_1316, List.forall_mem_cons.2 ⟨subd4_2_1317, List.forall_mem_cons.2 ⟨subd4_2_1318, List.forall_mem_cons.2 ⟨subd4_2_1319, List.forall_mem_cons.2 ⟨subd4_2_1320, List.forall_mem_cons.2 ⟨subd4_2_1321, List.forall_mem_cons.2 ⟨subd4_2_1322, List.forall_mem_cons.2 ⟨subd4_2_1323, List.forall_mem_cons.2 ⟨subd4_2_1324, List.forall_mem_cons.2 ⟨subd4_2_1325, List.forall_mem_cons.2 ⟨subd4_2_1326, List.forall_mem_cons.2 ⟨subd4_2_1327, List.forall_mem_cons.2 ⟨subd4_2_1328, List.forall_mem_cons.2 ⟨subd4_2_1329, List.forall_mem_cons.2 ⟨subd4_2_1330, List.forall_mem_cons.2 ⟨subd4_2_1331, List.forall_mem_cons.2 ⟨subd4_2_1332, List.forall_mem_cons.2 ⟨subd4_2_1333, List.forall_mem_cons.2 ⟨subd4_2_1334, List.forall_mem_cons.2 ⟨subd4_2_1335, List.forall_mem_cons.2 ⟨subd4_2_1336, List.forall_mem_cons.2 ⟨subd4_2_1337, List.forall_mem_cons.2 ⟨subd4_2_1338, List.forall_mem_cons.2 ⟨subd4_2_1339, List.forall_mem_cons.2 ⟨subd4_2_1340, List.forall_mem_cons.2 ⟨subd4_2_1341, List.forall_mem_cons.2 ⟨subd4_2_1342, List.forall_mem_cons.2 ⟨subd4_2_1343, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_2_1344 : subd4_2 [4, -2] = true := by decide +kernel
theorem subd4_2_1345 : subd4_2 [4, -1, -7] = true := by decide +kernel
theorem subd4_2_1346 : subd4_2 [4, -1, -6] = true := by decide +kernel
theorem subd4_2_1347 : subd4_2 [4, -1, -5] = true := by decide +kernel
theorem subd4_2_1348 : subd4_2 [4, -1, -4] = true := by decide +kernel
theorem subd4_2_1349 : subd4_2 [4, -1, -3] = true := by decide +kernel
theorem subd4_2_1350 : subd4_2 [4, -1, -2] = true := by decide +kernel
theorem subd4_2_1351 : subd4_2 [4, -1, -1] = true := by decide +kernel
theorem subd4_2_1352 : subd4_2 [4, -1, 0] = true := by decide +kernel
theorem subd4_2_1353 : subd4_2 [4, -1, 1] = true := by decide +kernel
theorem subd4_2_1354 : subd4_2 [4, -1, 2] = true := by decide +kernel
theorem subd4_2_1355 : subd4_2 [4, -1, 3] = true := by decide +kernel
theorem subd4_2_1356 : subd4_2 [4, -1, 4] = true := by decide +kernel
theorem subd4_2_1357 : subd4_2 [4, -1, 5] = true := by decide +kernel
theorem subd4_2_1358 : subd4_2 [4, -1, 6] = true := by decide +kernel
theorem subd4_2_1359 : subd4_2 [4, 0, -8] = true := by decide +kernel
theorem subd4_2_1360 : subd4_2 [4, 0, -7] = true := by decide +kernel
theorem subd4_2_1361 : subd4_2 [4, 0, -6] = true := by decide +kernel
theorem subd4_2_1362 : subd4_2 [4, 0, -5] = true := by decide +kernel
theorem subd4_2_1363 : subd4_2 [4, 0, -4] = true := by decide +kernel
theorem subd4_2_1364 : subd4_2 [4, 0, -3] = true := by decide +kernel
theorem subd4_2_1365 : subd4_2 [4, 0, -2] = true := by decide +kernel
theorem subd4_2_1366 : subd4_2 [4, 0, -1] = true := by decide +kernel
theorem subd4_2_1367 : subd4_2 [4, 0, 0] = true := by decide +kernel
theorem subd4_2_1368 : subd4_2 [4, 0, 1] = true := by decide +kernel
theorem subd4_2_1369 : subd4_2 [4, 0, 2] = true := by decide +kernel
theorem subd4_2_1370 : subd4_2 [4, 0, 3] = true := by decide +kernel
theorem subd4_2_1371 : subd4_2 [4, 0, 4] = true := by decide +kernel
theorem subd4_2_1372 : subd4_2 [4, 0, 5] = true := by decide +kernel
theorem subd4_2_1373 : subd4_2 [4, 0, 6] = true := by decide +kernel
theorem subd4_2_1374 : subd4_2 [4, 0, 7] = true := by decide +kernel
theorem subd4_2_1375 : subd4_2 [4, 1, -8] = true := by decide +kernel
theorem sbd4_2_42 : ∀ q ∈ blkd4_2_42, subd4_2 q = true := by
  unfold blkd4_2_42
  exact List.forall_mem_cons.2 ⟨subd4_2_1344, List.forall_mem_cons.2 ⟨subd4_2_1345, List.forall_mem_cons.2 ⟨subd4_2_1346, List.forall_mem_cons.2 ⟨subd4_2_1347, List.forall_mem_cons.2 ⟨subd4_2_1348, List.forall_mem_cons.2 ⟨subd4_2_1349, List.forall_mem_cons.2 ⟨subd4_2_1350, List.forall_mem_cons.2 ⟨subd4_2_1351, List.forall_mem_cons.2 ⟨subd4_2_1352, List.forall_mem_cons.2 ⟨subd4_2_1353, List.forall_mem_cons.2 ⟨subd4_2_1354, List.forall_mem_cons.2 ⟨subd4_2_1355, List.forall_mem_cons.2 ⟨subd4_2_1356, List.forall_mem_cons.2 ⟨subd4_2_1357, List.forall_mem_cons.2 ⟨subd4_2_1358, List.forall_mem_cons.2 ⟨subd4_2_1359, List.forall_mem_cons.2 ⟨subd4_2_1360, List.forall_mem_cons.2 ⟨subd4_2_1361, List.forall_mem_cons.2 ⟨subd4_2_1362, List.forall_mem_cons.2 ⟨subd4_2_1363, List.forall_mem_cons.2 ⟨subd4_2_1364, List.forall_mem_cons.2 ⟨subd4_2_1365, List.forall_mem_cons.2 ⟨subd4_2_1366, List.forall_mem_cons.2 ⟨subd4_2_1367, List.forall_mem_cons.2 ⟨subd4_2_1368, List.forall_mem_cons.2 ⟨subd4_2_1369, List.forall_mem_cons.2 ⟨subd4_2_1370, List.forall_mem_cons.2 ⟨subd4_2_1371, List.forall_mem_cons.2 ⟨subd4_2_1372, List.forall_mem_cons.2 ⟨subd4_2_1373, List.forall_mem_cons.2 ⟨subd4_2_1374, List.forall_mem_cons.2 ⟨subd4_2_1375, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_2_1376 : subd4_2 [4, 1, -7] = true := by decide +kernel
theorem subd4_2_1377 : subd4_2 [4, 1, -6] = true := by decide +kernel
theorem subd4_2_1378 : subd4_2 [4, 1, -5] = true := by decide +kernel
theorem subd4_2_1379 : subd4_2 [4, 1, -4] = true := by decide +kernel
theorem subd4_2_1380 : subd4_2 [4, 1, -3] = true := by decide +kernel
theorem subd4_2_1381 : subd4_2 [4, 1, -2] = true := by decide +kernel
theorem subd4_2_1382 : subd4_2 [4, 1, -1] = true := by decide +kernel
theorem subd4_2_1383 : subd4_2 [4, 1, 0] = true := by decide +kernel
theorem subd4_2_1384 : subd4_2 [4, 1, 1] = true := by decide +kernel
theorem subd4_2_1385 : subd4_2 [4, 1, 2] = true := by decide +kernel
theorem subd4_2_1386 : subd4_2 [4, 1, 3] = true := by decide +kernel
theorem subd4_2_1387 : subd4_2 [4, 1, 4] = true := by decide +kernel
theorem subd4_2_1388 : subd4_2 [4, 1, 5] = true := by decide +kernel
theorem subd4_2_1389 : subd4_2 [4, 1, 6] = true := by decide +kernel
theorem subd4_2_1390 : subd4_2 [4, 1, 7] = true := by decide +kernel
theorem subd4_2_1391 : subd4_2 [4, 1, 8] = true := by decide +kernel
theorem subd4_2_1392 : subd4_2 [4, 2, -7] = true := by decide +kernel
theorem subd4_2_1393 : subd4_2 [4, 2, -6] = true := by decide +kernel
theorem subd4_2_1394 : subd4_2 [4, 2, -5] = true := by decide +kernel
theorem subd4_2_1395 : subd4_2 [4, 2, -4] = true := by decide +kernel
theorem subd4_2_1396 : subd4_2 [4, 2, -3] = true := by decide +kernel
theorem subd4_2_1397 : subd4_2 [4, 2, -2] = true := by decide +kernel
theorem subd4_2_1398 : subd4_2 [4, 2, -1] = true := by decide +kernel
theorem subd4_2_1399 : subd4_2 [4, 2, 0] = true := by decide +kernel
theorem subd4_2_1400 : subd4_2 [4, 2, 1] = true := by decide +kernel
theorem subd4_2_1401 : subd4_2 [4, 2, 2] = true := by decide +kernel
theorem subd4_2_1402 : subd4_2 [4, 2, 3] = true := by decide +kernel
theorem subd4_2_1403 : subd4_2 [4, 2, 4] = true := by decide +kernel
theorem subd4_2_1404 : subd4_2 [4, 2, 5] = true := by decide +kernel
theorem subd4_2_1405 : subd4_2 [4, 2, 6] = true := by decide +kernel
theorem subd4_2_1406 : subd4_2 [4, 2, 7] = true := by decide +kernel
theorem subd4_2_1407 : subd4_2 [4, 2, 8] = true := by decide +kernel
theorem sbd4_2_43 : ∀ q ∈ blkd4_2_43, subd4_2 q = true := by
  unfold blkd4_2_43
  exact List.forall_mem_cons.2 ⟨subd4_2_1376, List.forall_mem_cons.2 ⟨subd4_2_1377, List.forall_mem_cons.2 ⟨subd4_2_1378, List.forall_mem_cons.2 ⟨subd4_2_1379, List.forall_mem_cons.2 ⟨subd4_2_1380, List.forall_mem_cons.2 ⟨subd4_2_1381, List.forall_mem_cons.2 ⟨subd4_2_1382, List.forall_mem_cons.2 ⟨subd4_2_1383, List.forall_mem_cons.2 ⟨subd4_2_1384, List.forall_mem_cons.2 ⟨subd4_2_1385, List.forall_mem_cons.2 ⟨subd4_2_1386, List.forall_mem_cons.2 ⟨subd4_2_1387, List.forall_mem_cons.2 ⟨subd4_2_1388, List.forall_mem_cons.2 ⟨subd4_2_1389, List.forall_mem_cons.2 ⟨subd4_2_1390, List.forall_mem_cons.2 ⟨subd4_2_1391, List.forall_mem_cons.2 ⟨subd4_2_1392, List.forall_mem_cons.2 ⟨subd4_2_1393, List.forall_mem_cons.2 ⟨subd4_2_1394, List.forall_mem_cons.2 ⟨subd4_2_1395, List.forall_mem_cons.2 ⟨subd4_2_1396, List.forall_mem_cons.2 ⟨subd4_2_1397, List.forall_mem_cons.2 ⟨subd4_2_1398, List.forall_mem_cons.2 ⟨subd4_2_1399, List.forall_mem_cons.2 ⟨subd4_2_1400, List.forall_mem_cons.2 ⟨subd4_2_1401, List.forall_mem_cons.2 ⟨subd4_2_1402, List.forall_mem_cons.2 ⟨subd4_2_1403, List.forall_mem_cons.2 ⟨subd4_2_1404, List.forall_mem_cons.2 ⟨subd4_2_1405, List.forall_mem_cons.2 ⟨subd4_2_1406, List.forall_mem_cons.2 ⟨subd4_2_1407, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_2_1408 : subd4_2 [4, 3, -7] = true := by decide +kernel
theorem subd4_2_1409 : subd4_2 [4, 3, -6] = true := by decide +kernel
theorem subd4_2_1410 : subd4_2 [4, 3, -5] = true := by decide +kernel
theorem subd4_2_1411 : subd4_2 [4, 3, -4] = true := by decide +kernel
theorem subd4_2_1412 : subd4_2 [4, 3, -3] = true := by decide +kernel
theorem subd4_2_1413 : subd4_2 [4, 3, -2] = true := by decide +kernel
theorem subd4_2_1414 : subd4_2 [4, 3, -1] = true := by decide +kernel
theorem subd4_2_1415 : subd4_2 [4, 3, 0] = true := by decide +kernel
theorem subd4_2_1416 : subd4_2 [4, 3, 1] = true := by decide +kernel
theorem subd4_2_1417 : subd4_2 [4, 3, 2] = true := by decide +kernel
theorem subd4_2_1418 : subd4_2 [4, 3, 3] = true := by decide +kernel
theorem subd4_2_1419 : subd4_2 [4, 3, 4] = true := by decide +kernel
theorem subd4_2_1420 : subd4_2 [4, 3, 5] = true := by decide +kernel
theorem subd4_2_1421 : subd4_2 [4, 3, 6] = true := by decide +kernel
theorem subd4_2_1422 : subd4_2 [4, 3, 7] = true := by decide +kernel
theorem subd4_2_1423 : subd4_2 [4, 3, 8] = true := by decide +kernel
theorem subd4_2_1424 : subd4_2 [4, 4, -6] = true := by decide +kernel
theorem subd4_2_1425 : subd4_2 [4, 4, -5] = true := by decide +kernel
theorem subd4_2_1426 : subd4_2 [4, 4, -4] = true := by decide +kernel
theorem subd4_2_1427 : subd4_2 [4, 4, -3] = true := by decide +kernel
theorem subd4_2_1428 : subd4_2 [4, 4, -2] = true := by decide +kernel
theorem subd4_2_1429 : subd4_2 [4, 4, -1] = true := by decide +kernel
theorem subd4_2_1430 : subd4_2 [4, 4, 0] = true := by decide +kernel
theorem subd4_2_1431 : subd4_2 [4, 4, 1] = true := by decide +kernel
theorem subd4_2_1432 : subd4_2 [4, 4, 2] = true := by decide +kernel
theorem subd4_2_1433 : subd4_2 [4, 4, 3] = true := by decide +kernel
theorem subd4_2_1434 : subd4_2 [4, 4, 4] = true := by decide +kernel
theorem subd4_2_1435 : subd4_2 [4, 4, 5] = true := by decide +kernel
theorem subd4_2_1436 : subd4_2 [4, 4, 6] = true := by decide +kernel
theorem subd4_2_1437 : subd4_2 [4, 4, 7] = true := by decide +kernel
theorem subd4_2_1438 : subd4_2 [4, 4, 8] = true := by decide +kernel
theorem subd4_2_1439 : subd4_2 [4, 5] = true := by decide +kernel
theorem sbd4_2_44 : ∀ q ∈ blkd4_2_44, subd4_2 q = true := by
  unfold blkd4_2_44
  exact List.forall_mem_cons.2 ⟨subd4_2_1408, List.forall_mem_cons.2 ⟨subd4_2_1409, List.forall_mem_cons.2 ⟨subd4_2_1410, List.forall_mem_cons.2 ⟨subd4_2_1411, List.forall_mem_cons.2 ⟨subd4_2_1412, List.forall_mem_cons.2 ⟨subd4_2_1413, List.forall_mem_cons.2 ⟨subd4_2_1414, List.forall_mem_cons.2 ⟨subd4_2_1415, List.forall_mem_cons.2 ⟨subd4_2_1416, List.forall_mem_cons.2 ⟨subd4_2_1417, List.forall_mem_cons.2 ⟨subd4_2_1418, List.forall_mem_cons.2 ⟨subd4_2_1419, List.forall_mem_cons.2 ⟨subd4_2_1420, List.forall_mem_cons.2 ⟨subd4_2_1421, List.forall_mem_cons.2 ⟨subd4_2_1422, List.forall_mem_cons.2 ⟨subd4_2_1423, List.forall_mem_cons.2 ⟨subd4_2_1424, List.forall_mem_cons.2 ⟨subd4_2_1425, List.forall_mem_cons.2 ⟨subd4_2_1426, List.forall_mem_cons.2 ⟨subd4_2_1427, List.forall_mem_cons.2 ⟨subd4_2_1428, List.forall_mem_cons.2 ⟨subd4_2_1429, List.forall_mem_cons.2 ⟨subd4_2_1430, List.forall_mem_cons.2 ⟨subd4_2_1431, List.forall_mem_cons.2 ⟨subd4_2_1432, List.forall_mem_cons.2 ⟨subd4_2_1433, List.forall_mem_cons.2 ⟨subd4_2_1434, List.forall_mem_cons.2 ⟨subd4_2_1435, List.forall_mem_cons.2 ⟨subd4_2_1436, List.forall_mem_cons.2 ⟨subd4_2_1437, List.forall_mem_cons.2 ⟨subd4_2_1438, List.forall_mem_cons.2 ⟨subd4_2_1439, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_2_1440 : subd4_2 [4, 6] = true := by decide +kernel
theorem subd4_2_1441 : subd4_2 [4, 7] = true := by decide +kernel
theorem subd4_2_1442 : subd4_2 [5, -3] = true := by decide +kernel
theorem subd4_2_1443 : subd4_2 [5, -2] = true := by decide +kernel
theorem subd4_2_1444 : subd4_2 [5, -1] = true := by decide +kernel
theorem subd4_2_1445 : subd4_2 [5, 0] = true := by decide +kernel
theorem subd4_2_1446 : subd4_2 [5, 1] = true := by decide +kernel
theorem subd4_2_1447 : subd4_2 [5, 2] = true := by decide +kernel
theorem subd4_2_1448 : subd4_2 [5, 3] = true := by decide +kernel
theorem subd4_2_1449 : subd4_2 [5, 4] = true := by decide +kernel
theorem subd4_2_1450 : subd4_2 [5, 5] = true := by decide +kernel
theorem subd4_2_1451 : subd4_2 [5, 6] = true := by decide +kernel
theorem subd4_2_1452 : subd4_2 [6] = true := by decide +kernel
theorem sbd4_2_45 : ∀ q ∈ blkd4_2_45, subd4_2 q = true := by
  unfold blkd4_2_45
  exact List.forall_mem_cons.2 ⟨subd4_2_1440, List.forall_mem_cons.2 ⟨subd4_2_1441, List.forall_mem_cons.2 ⟨subd4_2_1442, List.forall_mem_cons.2 ⟨subd4_2_1443, List.forall_mem_cons.2 ⟨subd4_2_1444, List.forall_mem_cons.2 ⟨subd4_2_1445, List.forall_mem_cons.2 ⟨subd4_2_1446, List.forall_mem_cons.2 ⟨subd4_2_1447, List.forall_mem_cons.2 ⟨subd4_2_1448, List.forall_mem_cons.2 ⟨subd4_2_1449, List.forall_mem_cons.2 ⟨subd4_2_1450, List.forall_mem_cons.2 ⟨subd4_2_1451, List.forall_mem_cons.2 ⟨subd4_2_1452, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd4_3 : ldCheck G d4_3.U d4_3.ms ldd4_3 = true := by decide +kernel
theorem pre_okd4_3 : subPre G cell4 d4_3 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C121
