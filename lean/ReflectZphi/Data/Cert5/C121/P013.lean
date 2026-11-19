import ReflectZphi.Data.Cert5.C121.Base

namespace ReflectZphi.Data.Cert5.C121

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd5_2_1152 : subd5_2 [3, 2, -7] = true := by decide +kernel
theorem subd5_2_1153 : subd5_2 [3, 2, -6] = true := by decide +kernel
theorem subd5_2_1154 : subd5_2 [3, 2, -5] = true := by decide +kernel
theorem subd5_2_1155 : subd5_2 [3, 2, -4] = true := by decide +kernel
theorem subd5_2_1156 : subd5_2 [3, 2, -3] = true := by decide +kernel
theorem subd5_2_1157 : subd5_2 [3, 2, -2] = true := by decide +kernel
theorem subd5_2_1158 : subd5_2 [3, 2, -1] = true := by decide +kernel
theorem subd5_2_1159 : subd5_2 [3, 2, 0] = true := by decide +kernel
theorem subd5_2_1160 : subd5_2 [3, 2, 1] = true := by decide +kernel
theorem subd5_2_1161 : subd5_2 [3, 2, 2] = true := by decide +kernel
theorem subd5_2_1162 : subd5_2 [3, 2, 3] = true := by decide +kernel
theorem subd5_2_1163 : subd5_2 [3, 2, 4] = true := by decide +kernel
theorem subd5_2_1164 : subd5_2 [3, 2, 5] = true := by decide +kernel
theorem subd5_2_1165 : subd5_2 [3, 2, 6] = true := by decide +kernel
theorem subd5_2_1166 : subd5_2 [3, 2, 7] = true := by decide +kernel
theorem subd5_2_1167 : subd5_2 [3, 2, 8] = true := by decide +kernel
theorem subd5_2_1168 : subd5_2 [3, 3, -8] = true := by decide +kernel
theorem subd5_2_1169 : subd5_2 [3, 3, -7] = true := by decide +kernel
theorem subd5_2_1170 : subd5_2 [3, 3, -6] = true := by decide +kernel
theorem subd5_2_1171 : subd5_2 [3, 3, -5] = true := by decide +kernel
theorem subd5_2_1172 : subd5_2 [3, 3, -4] = true := by decide +kernel
theorem subd5_2_1173 : subd5_2 [3, 3, -3] = true := by decide +kernel
theorem subd5_2_1174 : subd5_2 [3, 3, -2] = true := by decide +kernel
theorem subd5_2_1175 : subd5_2 [3, 3, -1] = true := by decide +kernel
theorem subd5_2_1176 : subd5_2 [3, 3, 0] = true := by decide +kernel
theorem subd5_2_1177 : subd5_2 [3, 3, 1] = true := by decide +kernel
theorem subd5_2_1178 : subd5_2 [3, 3, 2] = true := by decide +kernel
theorem subd5_2_1179 : subd5_2 [3, 3, 3] = true := by decide +kernel
theorem subd5_2_1180 : subd5_2 [3, 3, 4] = true := by decide +kernel
theorem subd5_2_1181 : subd5_2 [3, 3, 5] = true := by decide +kernel
theorem subd5_2_1182 : subd5_2 [3, 3, 6] = true := by decide +kernel
theorem subd5_2_1183 : subd5_2 [3, 3, 7] = true := by decide +kernel
theorem sbd5_2_36 : ∀ q ∈ blkd5_2_36, subd5_2 q = true := by
  unfold blkd5_2_36
  exact List.forall_mem_cons.2 ⟨subd5_2_1152, List.forall_mem_cons.2 ⟨subd5_2_1153, List.forall_mem_cons.2 ⟨subd5_2_1154, List.forall_mem_cons.2 ⟨subd5_2_1155, List.forall_mem_cons.2 ⟨subd5_2_1156, List.forall_mem_cons.2 ⟨subd5_2_1157, List.forall_mem_cons.2 ⟨subd5_2_1158, List.forall_mem_cons.2 ⟨subd5_2_1159, List.forall_mem_cons.2 ⟨subd5_2_1160, List.forall_mem_cons.2 ⟨subd5_2_1161, List.forall_mem_cons.2 ⟨subd5_2_1162, List.forall_mem_cons.2 ⟨subd5_2_1163, List.forall_mem_cons.2 ⟨subd5_2_1164, List.forall_mem_cons.2 ⟨subd5_2_1165, List.forall_mem_cons.2 ⟨subd5_2_1166, List.forall_mem_cons.2 ⟨subd5_2_1167, List.forall_mem_cons.2 ⟨subd5_2_1168, List.forall_mem_cons.2 ⟨subd5_2_1169, List.forall_mem_cons.2 ⟨subd5_2_1170, List.forall_mem_cons.2 ⟨subd5_2_1171, List.forall_mem_cons.2 ⟨subd5_2_1172, List.forall_mem_cons.2 ⟨subd5_2_1173, List.forall_mem_cons.2 ⟨subd5_2_1174, List.forall_mem_cons.2 ⟨subd5_2_1175, List.forall_mem_cons.2 ⟨subd5_2_1176, List.forall_mem_cons.2 ⟨subd5_2_1177, List.forall_mem_cons.2 ⟨subd5_2_1178, List.forall_mem_cons.2 ⟨subd5_2_1179, List.forall_mem_cons.2 ⟨subd5_2_1180, List.forall_mem_cons.2 ⟨subd5_2_1181, List.forall_mem_cons.2 ⟨subd5_2_1182, List.forall_mem_cons.2 ⟨subd5_2_1183, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_1184 : subd5_2 [3, 4, -8] = true := by decide +kernel
theorem subd5_2_1185 : subd5_2 [3, 4, -7] = true := by decide +kernel
theorem subd5_2_1186 : subd5_2 [3, 4, -6] = true := by decide +kernel
theorem subd5_2_1187 : subd5_2 [3, 4, -5] = true := by decide +kernel
theorem subd5_2_1188 : subd5_2 [3, 4, -4] = true := by decide +kernel
theorem subd5_2_1189 : subd5_2 [3, 4, -3] = true := by decide +kernel
theorem subd5_2_1190 : subd5_2 [3, 4, -2] = true := by decide +kernel
theorem subd5_2_1191 : subd5_2 [3, 4, -1] = true := by decide +kernel
theorem subd5_2_1192 : subd5_2 [3, 4, 0] = true := by decide +kernel
theorem subd5_2_1193 : subd5_2 [3, 4, 1] = true := by decide +kernel
theorem subd5_2_1194 : subd5_2 [3, 4, 2] = true := by decide +kernel
theorem subd5_2_1195 : subd5_2 [3, 4, 3] = true := by decide +kernel
theorem subd5_2_1196 : subd5_2 [3, 4, 4] = true := by decide +kernel
theorem subd5_2_1197 : subd5_2 [3, 4, 5] = true := by decide +kernel
theorem subd5_2_1198 : subd5_2 [3, 4, 6] = true := by decide +kernel
theorem subd5_2_1199 : subd5_2 [3, 4, 7] = true := by decide +kernel
theorem subd5_2_1200 : subd5_2 [3, 5, -8] = true := by decide +kernel
theorem subd5_2_1201 : subd5_2 [3, 5, -7] = true := by decide +kernel
theorem subd5_2_1202 : subd5_2 [3, 5, -6] = true := by decide +kernel
theorem subd5_2_1203 : subd5_2 [3, 5, -5] = true := by decide +kernel
theorem subd5_2_1204 : subd5_2 [3, 5, -4] = true := by decide +kernel
theorem subd5_2_1205 : subd5_2 [3, 5, -3] = true := by decide +kernel
theorem subd5_2_1206 : subd5_2 [3, 5, -2] = true := by decide +kernel
theorem subd5_2_1207 : subd5_2 [3, 5, -1] = true := by decide +kernel
theorem subd5_2_1208 : subd5_2 [3, 5, 0] = true := by decide +kernel
theorem subd5_2_1209 : subd5_2 [3, 5, 1] = true := by decide +kernel
theorem subd5_2_1210 : subd5_2 [3, 5, 2] = true := by decide +kernel
theorem subd5_2_1211 : subd5_2 [3, 5, 3] = true := by decide +kernel
theorem subd5_2_1212 : subd5_2 [3, 5, 4] = true := by decide +kernel
theorem subd5_2_1213 : subd5_2 [3, 5, 5] = true := by decide +kernel
theorem subd5_2_1214 : subd5_2 [3, 5, 6] = true := by decide +kernel
theorem subd5_2_1215 : subd5_2 [3, 6] = true := by decide +kernel
theorem sbd5_2_37 : ∀ q ∈ blkd5_2_37, subd5_2 q = true := by
  unfold blkd5_2_37
  exact List.forall_mem_cons.2 ⟨subd5_2_1184, List.forall_mem_cons.2 ⟨subd5_2_1185, List.forall_mem_cons.2 ⟨subd5_2_1186, List.forall_mem_cons.2 ⟨subd5_2_1187, List.forall_mem_cons.2 ⟨subd5_2_1188, List.forall_mem_cons.2 ⟨subd5_2_1189, List.forall_mem_cons.2 ⟨subd5_2_1190, List.forall_mem_cons.2 ⟨subd5_2_1191, List.forall_mem_cons.2 ⟨subd5_2_1192, List.forall_mem_cons.2 ⟨subd5_2_1193, List.forall_mem_cons.2 ⟨subd5_2_1194, List.forall_mem_cons.2 ⟨subd5_2_1195, List.forall_mem_cons.2 ⟨subd5_2_1196, List.forall_mem_cons.2 ⟨subd5_2_1197, List.forall_mem_cons.2 ⟨subd5_2_1198, List.forall_mem_cons.2 ⟨subd5_2_1199, List.forall_mem_cons.2 ⟨subd5_2_1200, List.forall_mem_cons.2 ⟨subd5_2_1201, List.forall_mem_cons.2 ⟨subd5_2_1202, List.forall_mem_cons.2 ⟨subd5_2_1203, List.forall_mem_cons.2 ⟨subd5_2_1204, List.forall_mem_cons.2 ⟨subd5_2_1205, List.forall_mem_cons.2 ⟨subd5_2_1206, List.forall_mem_cons.2 ⟨subd5_2_1207, List.forall_mem_cons.2 ⟨subd5_2_1208, List.forall_mem_cons.2 ⟨subd5_2_1209, List.forall_mem_cons.2 ⟨subd5_2_1210, List.forall_mem_cons.2 ⟨subd5_2_1211, List.forall_mem_cons.2 ⟨subd5_2_1212, List.forall_mem_cons.2 ⟨subd5_2_1213, List.forall_mem_cons.2 ⟨subd5_2_1214, List.forall_mem_cons.2 ⟨subd5_2_1215, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_1216 : subd5_2 [3, 7] = true := by decide +kernel
theorem subd5_2_1217 : subd5_2 [3, 8] = true := by decide +kernel
theorem subd5_2_1218 : subd5_2 [4, -5] = true := by decide +kernel
theorem subd5_2_1219 : subd5_2 [4, -4] = true := by decide +kernel
theorem subd5_2_1220 : subd5_2 [4, -3] = true := by decide +kernel
theorem subd5_2_1221 : subd5_2 [4, -2] = true := by decide +kernel
theorem subd5_2_1222 : subd5_2 [4, -1] = true := by decide +kernel
theorem subd5_2_1223 : subd5_2 [4, 0, -6] = true := by decide +kernel
theorem subd5_2_1224 : subd5_2 [4, 0, -5] = true := by decide +kernel
theorem subd5_2_1225 : subd5_2 [4, 0, -4] = true := by decide +kernel
theorem subd5_2_1226 : subd5_2 [4, 0, -3] = true := by decide +kernel
theorem subd5_2_1227 : subd5_2 [4, 0, -2] = true := by decide +kernel
theorem subd5_2_1228 : subd5_2 [4, 0, -1] = true := by decide +kernel
theorem subd5_2_1229 : subd5_2 [4, 0, 0] = true := by decide +kernel
theorem subd5_2_1230 : subd5_2 [4, 0, 1] = true := by decide +kernel
theorem subd5_2_1231 : subd5_2 [4, 0, 2] = true := by decide +kernel
theorem subd5_2_1232 : subd5_2 [4, 0, 3] = true := by decide +kernel
theorem subd5_2_1233 : subd5_2 [4, 0, 4] = true := by decide +kernel
theorem subd5_2_1234 : subd5_2 [4, 0, 5] = true := by decide +kernel
theorem subd5_2_1235 : subd5_2 [4, 0, 6] = true := by decide +kernel
theorem subd5_2_1236 : subd5_2 [4, 0, 7] = true := by decide +kernel
theorem subd5_2_1237 : subd5_2 [4, 0, 8] = true := by decide +kernel
theorem subd5_2_1238 : subd5_2 [4, 1, -6] = true := by decide +kernel
theorem subd5_2_1239 : subd5_2 [4, 1, -5] = true := by decide +kernel
theorem subd5_2_1240 : subd5_2 [4, 1, -4] = true := by decide +kernel
theorem subd5_2_1241 : subd5_2 [4, 1, -3] = true := by decide +kernel
theorem subd5_2_1242 : subd5_2 [4, 1, -2] = true := by decide +kernel
theorem subd5_2_1243 : subd5_2 [4, 1, -1] = true := by decide +kernel
theorem subd5_2_1244 : subd5_2 [4, 1, 0] = true := by decide +kernel
theorem subd5_2_1245 : subd5_2 [4, 1, 1] = true := by decide +kernel
theorem subd5_2_1246 : subd5_2 [4, 1, 2] = true := by decide +kernel
theorem subd5_2_1247 : subd5_2 [4, 1, 3] = true := by decide +kernel
theorem sbd5_2_38 : ∀ q ∈ blkd5_2_38, subd5_2 q = true := by
  unfold blkd5_2_38
  exact List.forall_mem_cons.2 ⟨subd5_2_1216, List.forall_mem_cons.2 ⟨subd5_2_1217, List.forall_mem_cons.2 ⟨subd5_2_1218, List.forall_mem_cons.2 ⟨subd5_2_1219, List.forall_mem_cons.2 ⟨subd5_2_1220, List.forall_mem_cons.2 ⟨subd5_2_1221, List.forall_mem_cons.2 ⟨subd5_2_1222, List.forall_mem_cons.2 ⟨subd5_2_1223, List.forall_mem_cons.2 ⟨subd5_2_1224, List.forall_mem_cons.2 ⟨subd5_2_1225, List.forall_mem_cons.2 ⟨subd5_2_1226, List.forall_mem_cons.2 ⟨subd5_2_1227, List.forall_mem_cons.2 ⟨subd5_2_1228, List.forall_mem_cons.2 ⟨subd5_2_1229, List.forall_mem_cons.2 ⟨subd5_2_1230, List.forall_mem_cons.2 ⟨subd5_2_1231, List.forall_mem_cons.2 ⟨subd5_2_1232, List.forall_mem_cons.2 ⟨subd5_2_1233, List.forall_mem_cons.2 ⟨subd5_2_1234, List.forall_mem_cons.2 ⟨subd5_2_1235, List.forall_mem_cons.2 ⟨subd5_2_1236, List.forall_mem_cons.2 ⟨subd5_2_1237, List.forall_mem_cons.2 ⟨subd5_2_1238, List.forall_mem_cons.2 ⟨subd5_2_1239, List.forall_mem_cons.2 ⟨subd5_2_1240, List.forall_mem_cons.2 ⟨subd5_2_1241, List.forall_mem_cons.2 ⟨subd5_2_1242, List.forall_mem_cons.2 ⟨subd5_2_1243, List.forall_mem_cons.2 ⟨subd5_2_1244, List.forall_mem_cons.2 ⟨subd5_2_1245, List.forall_mem_cons.2 ⟨subd5_2_1246, List.forall_mem_cons.2 ⟨subd5_2_1247, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_1248 : subd5_2 [4, 1, 4] = true := by decide +kernel
theorem subd5_2_1249 : subd5_2 [4, 1, 5] = true := by decide +kernel
theorem subd5_2_1250 : subd5_2 [4, 1, 6] = true := by decide +kernel
theorem subd5_2_1251 : subd5_2 [4, 1, 7] = true := by decide +kernel
theorem subd5_2_1252 : subd5_2 [4, 1, 8] = true := by decide +kernel
theorem subd5_2_1253 : subd5_2 [4, 2, -7] = true := by decide +kernel
theorem subd5_2_1254 : subd5_2 [4, 2, -6] = true := by decide +kernel
theorem subd5_2_1255 : subd5_2 [4, 2, -5] = true := by decide +kernel
theorem subd5_2_1256 : subd5_2 [4, 2, -4] = true := by decide +kernel
theorem subd5_2_1257 : subd5_2 [4, 2, -3] = true := by decide +kernel
theorem subd5_2_1258 : subd5_2 [4, 2, -2] = true := by decide +kernel
theorem subd5_2_1259 : subd5_2 [4, 2, -1] = true := by decide +kernel
theorem subd5_2_1260 : subd5_2 [4, 2, 0] = true := by decide +kernel
theorem subd5_2_1261 : subd5_2 [4, 2, 1] = true := by decide +kernel
theorem subd5_2_1262 : subd5_2 [4, 2, 2] = true := by decide +kernel
theorem subd5_2_1263 : subd5_2 [4, 2, 3] = true := by decide +kernel
theorem subd5_2_1264 : subd5_2 [4, 2, 4] = true := by decide +kernel
theorem subd5_2_1265 : subd5_2 [4, 2, 5] = true := by decide +kernel
theorem subd5_2_1266 : subd5_2 [4, 2, 6] = true := by decide +kernel
theorem subd5_2_1267 : subd5_2 [4, 2, 7] = true := by decide +kernel
theorem subd5_2_1268 : subd5_2 [4, 3, -7] = true := by decide +kernel
theorem subd5_2_1269 : subd5_2 [4, 3, -6] = true := by decide +kernel
theorem subd5_2_1270 : subd5_2 [4, 3, -5] = true := by decide +kernel
theorem subd5_2_1271 : subd5_2 [4, 3, -4] = true := by decide +kernel
theorem subd5_2_1272 : subd5_2 [4, 3, -3] = true := by decide +kernel
theorem subd5_2_1273 : subd5_2 [4, 3, -2] = true := by decide +kernel
theorem subd5_2_1274 : subd5_2 [4, 3, -1] = true := by decide +kernel
theorem subd5_2_1275 : subd5_2 [4, 3, 0] = true := by decide +kernel
theorem subd5_2_1276 : subd5_2 [4, 3, 1] = true := by decide +kernel
theorem subd5_2_1277 : subd5_2 [4, 3, 2] = true := by decide +kernel
theorem subd5_2_1278 : subd5_2 [4, 3, 3] = true := by decide +kernel
theorem subd5_2_1279 : subd5_2 [4, 3, 4] = true := by decide +kernel
theorem sbd5_2_39 : ∀ q ∈ blkd5_2_39, subd5_2 q = true := by
  unfold blkd5_2_39
  exact List.forall_mem_cons.2 ⟨subd5_2_1248, List.forall_mem_cons.2 ⟨subd5_2_1249, List.forall_mem_cons.2 ⟨subd5_2_1250, List.forall_mem_cons.2 ⟨subd5_2_1251, List.forall_mem_cons.2 ⟨subd5_2_1252, List.forall_mem_cons.2 ⟨subd5_2_1253, List.forall_mem_cons.2 ⟨subd5_2_1254, List.forall_mem_cons.2 ⟨subd5_2_1255, List.forall_mem_cons.2 ⟨subd5_2_1256, List.forall_mem_cons.2 ⟨subd5_2_1257, List.forall_mem_cons.2 ⟨subd5_2_1258, List.forall_mem_cons.2 ⟨subd5_2_1259, List.forall_mem_cons.2 ⟨subd5_2_1260, List.forall_mem_cons.2 ⟨subd5_2_1261, List.forall_mem_cons.2 ⟨subd5_2_1262, List.forall_mem_cons.2 ⟨subd5_2_1263, List.forall_mem_cons.2 ⟨subd5_2_1264, List.forall_mem_cons.2 ⟨subd5_2_1265, List.forall_mem_cons.2 ⟨subd5_2_1266, List.forall_mem_cons.2 ⟨subd5_2_1267, List.forall_mem_cons.2 ⟨subd5_2_1268, List.forall_mem_cons.2 ⟨subd5_2_1269, List.forall_mem_cons.2 ⟨subd5_2_1270, List.forall_mem_cons.2 ⟨subd5_2_1271, List.forall_mem_cons.2 ⟨subd5_2_1272, List.forall_mem_cons.2 ⟨subd5_2_1273, List.forall_mem_cons.2 ⟨subd5_2_1274, List.forall_mem_cons.2 ⟨subd5_2_1275, List.forall_mem_cons.2 ⟨subd5_2_1276, List.forall_mem_cons.2 ⟨subd5_2_1277, List.forall_mem_cons.2 ⟨subd5_2_1278, List.forall_mem_cons.2 ⟨subd5_2_1279, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_1280 : subd5_2 [4, 3, 5] = true := by decide +kernel
theorem subd5_2_1281 : subd5_2 [4, 3, 6] = true := by decide +kernel
theorem subd5_2_1282 : subd5_2 [4, 3, 7] = true := by decide +kernel
theorem subd5_2_1283 : subd5_2 [4, 4, -7] = true := by decide +kernel
theorem subd5_2_1284 : subd5_2 [4, 4, -6] = true := by decide +kernel
theorem subd5_2_1285 : subd5_2 [4, 4, -5] = true := by decide +kernel
theorem subd5_2_1286 : subd5_2 [4, 4, -4] = true := by decide +kernel
theorem subd5_2_1287 : subd5_2 [4, 4, -3] = true := by decide +kernel
theorem subd5_2_1288 : subd5_2 [4, 4, -2] = true := by decide +kernel
theorem subd5_2_1289 : subd5_2 [4, 4, -1] = true := by decide +kernel
theorem subd5_2_1290 : subd5_2 [4, 4, 0] = true := by decide +kernel
theorem subd5_2_1291 : subd5_2 [4, 4, 1] = true := by decide +kernel
theorem subd5_2_1292 : subd5_2 [4, 4, 2] = true := by decide +kernel
theorem subd5_2_1293 : subd5_2 [4, 4, 3] = true := by decide +kernel
theorem subd5_2_1294 : subd5_2 [4, 4, 4] = true := by decide +kernel
theorem subd5_2_1295 : subd5_2 [4, 4, 5] = true := by decide +kernel
theorem subd5_2_1296 : subd5_2 [4, 4, 6] = true := by decide +kernel
theorem subd5_2_1297 : subd5_2 [4, 5] = true := by decide +kernel
theorem subd5_2_1298 : subd5_2 [4, 6] = true := by decide +kernel
theorem subd5_2_1299 : subd5_2 [4, 7] = true := by decide +kernel
theorem subd5_2_1300 : subd5_2 [5, -3] = true := by decide +kernel
theorem subd5_2_1301 : subd5_2 [5, -2] = true := by decide +kernel
theorem subd5_2_1302 : subd5_2 [5, -1] = true := by decide +kernel
theorem subd5_2_1303 : subd5_2 [5, 0] = true := by decide +kernel
theorem subd5_2_1304 : subd5_2 [5, 1] = true := by decide +kernel
theorem subd5_2_1305 : subd5_2 [5, 2] = true := by decide +kernel
theorem subd5_2_1306 : subd5_2 [5, 3] = true := by decide +kernel
theorem subd5_2_1307 : subd5_2 [5, 4] = true := by decide +kernel
theorem subd5_2_1308 : subd5_2 [5, 5] = true := by decide +kernel
theorem subd5_2_1309 : subd5_2 [5, 6] = true := by decide +kernel
theorem subd5_2_1310 : subd5_2 [5, 7] = true := by decide +kernel
theorem subd5_2_1311 : subd5_2 [6, -1] = true := by decide +kernel
theorem sbd5_2_40 : ∀ q ∈ blkd5_2_40, subd5_2 q = true := by
  unfold blkd5_2_40
  exact List.forall_mem_cons.2 ⟨subd5_2_1280, List.forall_mem_cons.2 ⟨subd5_2_1281, List.forall_mem_cons.2 ⟨subd5_2_1282, List.forall_mem_cons.2 ⟨subd5_2_1283, List.forall_mem_cons.2 ⟨subd5_2_1284, List.forall_mem_cons.2 ⟨subd5_2_1285, List.forall_mem_cons.2 ⟨subd5_2_1286, List.forall_mem_cons.2 ⟨subd5_2_1287, List.forall_mem_cons.2 ⟨subd5_2_1288, List.forall_mem_cons.2 ⟨subd5_2_1289, List.forall_mem_cons.2 ⟨subd5_2_1290, List.forall_mem_cons.2 ⟨subd5_2_1291, List.forall_mem_cons.2 ⟨subd5_2_1292, List.forall_mem_cons.2 ⟨subd5_2_1293, List.forall_mem_cons.2 ⟨subd5_2_1294, List.forall_mem_cons.2 ⟨subd5_2_1295, List.forall_mem_cons.2 ⟨subd5_2_1296, List.forall_mem_cons.2 ⟨subd5_2_1297, List.forall_mem_cons.2 ⟨subd5_2_1298, List.forall_mem_cons.2 ⟨subd5_2_1299, List.forall_mem_cons.2 ⟨subd5_2_1300, List.forall_mem_cons.2 ⟨subd5_2_1301, List.forall_mem_cons.2 ⟨subd5_2_1302, List.forall_mem_cons.2 ⟨subd5_2_1303, List.forall_mem_cons.2 ⟨subd5_2_1304, List.forall_mem_cons.2 ⟨subd5_2_1305, List.forall_mem_cons.2 ⟨subd5_2_1306, List.forall_mem_cons.2 ⟨subd5_2_1307, List.forall_mem_cons.2 ⟨subd5_2_1308, List.forall_mem_cons.2 ⟨subd5_2_1309, List.forall_mem_cons.2 ⟨subd5_2_1310, List.forall_mem_cons.2 ⟨subd5_2_1311, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_1312 : subd5_2 [6, 0] = true := by decide +kernel
theorem subd5_2_1313 : subd5_2 [6, 1] = true := by decide +kernel
theorem subd5_2_1314 : subd5_2 [6, 2] = true := by decide +kernel
theorem subd5_2_1315 : subd5_2 [6, 3] = true := by decide +kernel
theorem subd5_2_1316 : subd5_2 [6, 4] = true := by decide +kernel
theorem subd5_2_1317 : subd5_2 [6, 5] = true := by decide +kernel
theorem subd5_2_1318 : subd5_2 [6, 6] = true := by decide +kernel
theorem sbd5_2_41 : ∀ q ∈ blkd5_2_41, subd5_2 q = true := by
  unfold blkd5_2_41
  exact List.forall_mem_cons.2 ⟨subd5_2_1312, List.forall_mem_cons.2 ⟨subd5_2_1313, List.forall_mem_cons.2 ⟨subd5_2_1314, List.forall_mem_cons.2 ⟨subd5_2_1315, List.forall_mem_cons.2 ⟨subd5_2_1316, List.forall_mem_cons.2 ⟨subd5_2_1317, List.forall_mem_cons.2 ⟨subd5_2_1318, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_3 : ldCheck G d5_3.U d5_3.ms ldd5_3 = true := by decide +kernel
theorem pre_okd5_3 : subPre G cell5 d5_3 = true := by decide +kernel
theorem subd5_3_0 : subd5_3 [-3] = true := by decide +kernel
theorem subd5_3_1 : subd5_3 [-2, -3] = true := by decide +kernel
theorem subd5_3_2 : subd5_3 [-2, -2] = true := by decide +kernel
theorem subd5_3_3 : subd5_3 [-2, -1] = true := by decide +kernel
theorem subd5_3_4 : subd5_3 [-2, 0] = true := by decide +kernel
theorem subd5_3_5 : subd5_3 [-2, 1] = true := by decide +kernel
theorem subd5_3_6 : subd5_3 [-2, 2] = true := by decide +kernel
theorem subd5_3_7 : subd5_3 [-2, 3] = true := by decide +kernel
theorem subd5_3_8 : subd5_3 [-1, -4] = true := by decide +kernel
theorem subd5_3_9 : subd5_3 [-1, -3] = true := by decide +kernel
theorem subd5_3_10 : subd5_3 [-1, -2] = true := by decide +kernel
theorem subd5_3_11 : subd5_3 [-1, -1] = true := by decide +kernel
theorem subd5_3_12 : subd5_3 [-1, 0] = true := by decide +kernel
theorem subd5_3_13 : subd5_3 [-1, 1] = true := by decide +kernel
theorem subd5_3_14 : subd5_3 [-1, 2] = true := by decide +kernel
theorem subd5_3_15 : subd5_3 [-1, 3] = true := by decide +kernel
theorem subd5_3_16 : subd5_3 [0, -4] = true := by decide +kernel
theorem subd5_3_17 : subd5_3 [0, -3] = true := by decide +kernel
theorem subd5_3_18 : subd5_3 [0, -2] = true := by decide +kernel
theorem subd5_3_19 : subd5_3 [0, -1] = true := by decide +kernel
theorem subd5_3_20 : subd5_3 [0, 0] = true := by decide +kernel
theorem subd5_3_21 : subd5_3 [0, 1] = true := by decide +kernel
theorem subd5_3_22 : subd5_3 [0, 2] = true := by decide +kernel
theorem subd5_3_23 : subd5_3 [0, 3] = true := by decide +kernel
theorem subd5_3_24 : subd5_3 [1, -4] = true := by decide +kernel
theorem subd5_3_25 : subd5_3 [1, -3] = true := by decide +kernel
theorem subd5_3_26 : subd5_3 [1, -2] = true := by decide +kernel
theorem subd5_3_27 : subd5_3 [1, -1] = true := by decide +kernel
theorem subd5_3_28 : subd5_3 [1, 0] = true := by decide +kernel
theorem subd5_3_29 : subd5_3 [1, 1] = true := by decide +kernel
theorem subd5_3_30 : subd5_3 [1, 2] = true := by decide +kernel
theorem subd5_3_31 : subd5_3 [1, 3] = true := by decide +kernel
theorem sbd5_3_0 : ∀ q ∈ blkd5_3_0, subd5_3 q = true := by
  unfold blkd5_3_0
  exact List.forall_mem_cons.2 ⟨subd5_3_0, List.forall_mem_cons.2 ⟨subd5_3_1, List.forall_mem_cons.2 ⟨subd5_3_2, List.forall_mem_cons.2 ⟨subd5_3_3, List.forall_mem_cons.2 ⟨subd5_3_4, List.forall_mem_cons.2 ⟨subd5_3_5, List.forall_mem_cons.2 ⟨subd5_3_6, List.forall_mem_cons.2 ⟨subd5_3_7, List.forall_mem_cons.2 ⟨subd5_3_8, List.forall_mem_cons.2 ⟨subd5_3_9, List.forall_mem_cons.2 ⟨subd5_3_10, List.forall_mem_cons.2 ⟨subd5_3_11, List.forall_mem_cons.2 ⟨subd5_3_12, List.forall_mem_cons.2 ⟨subd5_3_13, List.forall_mem_cons.2 ⟨subd5_3_14, List.forall_mem_cons.2 ⟨subd5_3_15, List.forall_mem_cons.2 ⟨subd5_3_16, List.forall_mem_cons.2 ⟨subd5_3_17, List.forall_mem_cons.2 ⟨subd5_3_18, List.forall_mem_cons.2 ⟨subd5_3_19, List.forall_mem_cons.2 ⟨subd5_3_20, List.forall_mem_cons.2 ⟨subd5_3_21, List.forall_mem_cons.2 ⟨subd5_3_22, List.forall_mem_cons.2 ⟨subd5_3_23, List.forall_mem_cons.2 ⟨subd5_3_24, List.forall_mem_cons.2 ⟨subd5_3_25, List.forall_mem_cons.2 ⟨subd5_3_26, List.forall_mem_cons.2 ⟨subd5_3_27, List.forall_mem_cons.2 ⟨subd5_3_28, List.forall_mem_cons.2 ⟨subd5_3_29, List.forall_mem_cons.2 ⟨subd5_3_30, List.forall_mem_cons.2 ⟨subd5_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_3_32 : subd5_3 [2, -4] = true := by decide +kernel
theorem subd5_3_33 : subd5_3 [2, -3] = true := by decide +kernel
theorem subd5_3_34 : subd5_3 [2, -2] = true := by decide +kernel
theorem subd5_3_35 : subd5_3 [2, -1] = true := by decide +kernel
theorem subd5_3_36 : subd5_3 [2, 0] = true := by decide +kernel
theorem subd5_3_37 : subd5_3 [2, 1] = true := by decide +kernel
theorem subd5_3_38 : subd5_3 [2, 2] = true := by decide +kernel
theorem subd5_3_39 : subd5_3 [3] = true := by decide +kernel
theorem sbd5_3_1 : ∀ q ∈ blkd5_3_1, subd5_3 q = true := by
  unfold blkd5_3_1
  exact List.forall_mem_cons.2 ⟨subd5_3_32, List.forall_mem_cons.2 ⟨subd5_3_33, List.forall_mem_cons.2 ⟨subd5_3_34, List.forall_mem_cons.2 ⟨subd5_3_35, List.forall_mem_cons.2 ⟨subd5_3_36, List.forall_mem_cons.2 ⟨subd5_3_37, List.forall_mem_cons.2 ⟨subd5_3_38, List.forall_mem_cons.2 ⟨subd5_3_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C121
