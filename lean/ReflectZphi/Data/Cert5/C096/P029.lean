import ReflectZphi.Data.Cert5.C096.Base

namespace ReflectZphi.Data.Cert5.C096

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_3_1184 : subd8_3 [2, 3, -1] = true := by decide +kernel
theorem subd8_3_1185 : subd8_3 [2, 3, 0] = true := by decide +kernel
theorem subd8_3_1186 : subd8_3 [2, 3, 1] = true := by decide +kernel
theorem subd8_3_1187 : subd8_3 [2, 3, 2] = true := by decide +kernel
theorem subd8_3_1188 : subd8_3 [2, 3, 3] = true := by decide +kernel
theorem subd8_3_1189 : subd8_3 [2, 3, 4] = true := by decide +kernel
theorem subd8_3_1190 : subd8_3 [2, 3, 5] = true := by decide +kernel
theorem subd8_3_1191 : subd8_3 [2, 3, 6] = true := by decide +kernel
theorem subd8_3_1192 : subd8_3 [2, 3, 7] = true := by decide +kernel
theorem subd8_3_1193 : subd8_3 [2, 3, 8] = true := by decide +kernel
theorem subd8_3_1194 : subd8_3 [2, 3, 9] = true := by decide +kernel
theorem subd8_3_1195 : subd8_3 [2, 3, 10] = true := by decide +kernel
theorem subd8_3_1196 : subd8_3 [2, 4, -6] = true := by decide +kernel
theorem subd8_3_1197 : subd8_3 [2, 4, -5] = true := by decide +kernel
theorem subd8_3_1198 : subd8_3 [2, 4, -4] = true := by decide +kernel
theorem subd8_3_1199 : subd8_3 [2, 4, -3] = true := by decide +kernel
theorem subd8_3_1200 : subd8_3 [2, 4, -2] = true := by decide +kernel
theorem subd8_3_1201 : subd8_3 [2, 4, -1] = true := by decide +kernel
theorem subd8_3_1202 : subd8_3 [2, 4, 0] = true := by decide +kernel
theorem subd8_3_1203 : subd8_3 [2, 4, 1] = true := by decide +kernel
theorem subd8_3_1204 : subd8_3 [2, 4, 2] = true := by decide +kernel
theorem subd8_3_1205 : subd8_3 [2, 4, 3] = true := by decide +kernel
theorem subd8_3_1206 : subd8_3 [2, 4, 4] = true := by decide +kernel
theorem subd8_3_1207 : subd8_3 [2, 4, 5] = true := by decide +kernel
theorem subd8_3_1208 : subd8_3 [2, 4, 6] = true := by decide +kernel
theorem subd8_3_1209 : subd8_3 [2, 4, 7] = true := by decide +kernel
theorem subd8_3_1210 : subd8_3 [2, 4, 8] = true := by decide +kernel
theorem subd8_3_1211 : subd8_3 [2, 4, 9] = true := by decide +kernel
theorem subd8_3_1212 : subd8_3 [2, 4, 10] = true := by decide +kernel
theorem subd8_3_1213 : subd8_3 [2, 5, -5] = true := by decide +kernel
theorem subd8_3_1214 : subd8_3 [2, 5, -4] = true := by decide +kernel
theorem subd8_3_1215 : subd8_3 [2, 5, -3] = true := by decide +kernel
theorem sbd8_3_37 : ∀ q ∈ blkd8_3_37, subd8_3 q = true := by
  unfold blkd8_3_37
  exact List.forall_mem_cons.2 ⟨subd8_3_1184, List.forall_mem_cons.2 ⟨subd8_3_1185, List.forall_mem_cons.2 ⟨subd8_3_1186, List.forall_mem_cons.2 ⟨subd8_3_1187, List.forall_mem_cons.2 ⟨subd8_3_1188, List.forall_mem_cons.2 ⟨subd8_3_1189, List.forall_mem_cons.2 ⟨subd8_3_1190, List.forall_mem_cons.2 ⟨subd8_3_1191, List.forall_mem_cons.2 ⟨subd8_3_1192, List.forall_mem_cons.2 ⟨subd8_3_1193, List.forall_mem_cons.2 ⟨subd8_3_1194, List.forall_mem_cons.2 ⟨subd8_3_1195, List.forall_mem_cons.2 ⟨subd8_3_1196, List.forall_mem_cons.2 ⟨subd8_3_1197, List.forall_mem_cons.2 ⟨subd8_3_1198, List.forall_mem_cons.2 ⟨subd8_3_1199, List.forall_mem_cons.2 ⟨subd8_3_1200, List.forall_mem_cons.2 ⟨subd8_3_1201, List.forall_mem_cons.2 ⟨subd8_3_1202, List.forall_mem_cons.2 ⟨subd8_3_1203, List.forall_mem_cons.2 ⟨subd8_3_1204, List.forall_mem_cons.2 ⟨subd8_3_1205, List.forall_mem_cons.2 ⟨subd8_3_1206, List.forall_mem_cons.2 ⟨subd8_3_1207, List.forall_mem_cons.2 ⟨subd8_3_1208, List.forall_mem_cons.2 ⟨subd8_3_1209, List.forall_mem_cons.2 ⟨subd8_3_1210, List.forall_mem_cons.2 ⟨subd8_3_1211, List.forall_mem_cons.2 ⟨subd8_3_1212, List.forall_mem_cons.2 ⟨subd8_3_1213, List.forall_mem_cons.2 ⟨subd8_3_1214, List.forall_mem_cons.2 ⟨subd8_3_1215, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_1216 : subd8_3 [2, 5, -2] = true := by decide +kernel
theorem subd8_3_1217 : subd8_3 [2, 5, -1] = true := by decide +kernel
theorem subd8_3_1218 : subd8_3 [2, 5, 0] = true := by decide +kernel
theorem subd8_3_1219 : subd8_3 [2, 5, 1] = true := by decide +kernel
theorem subd8_3_1220 : subd8_3 [2, 5, 2] = true := by decide +kernel
theorem subd8_3_1221 : subd8_3 [2, 5, 3] = true := by decide +kernel
theorem subd8_3_1222 : subd8_3 [2, 5, 4] = true := by decide +kernel
theorem subd8_3_1223 : subd8_3 [2, 5, 5] = true := by decide +kernel
theorem subd8_3_1224 : subd8_3 [2, 5, 6] = true := by decide +kernel
theorem subd8_3_1225 : subd8_3 [2, 5, 7] = true := by decide +kernel
theorem subd8_3_1226 : subd8_3 [2, 5, 8] = true := by decide +kernel
theorem subd8_3_1227 : subd8_3 [2, 5, 9] = true := by decide +kernel
theorem subd8_3_1228 : subd8_3 [2, 6] = true := by decide +kernel
theorem subd8_3_1229 : subd8_3 [2, 7] = true := by decide +kernel
theorem subd8_3_1230 : subd8_3 [3, -6] = true := by decide +kernel
theorem subd8_3_1231 : subd8_3 [3, -5] = true := by decide +kernel
theorem subd8_3_1232 : subd8_3 [3, -4] = true := by decide +kernel
theorem subd8_3_1233 : subd8_3 [3, -3, -7] = true := by decide +kernel
theorem subd8_3_1234 : subd8_3 [3, -3, -6] = true := by decide +kernel
theorem subd8_3_1235 : subd8_3 [3, -3, -5] = true := by decide +kernel
theorem subd8_3_1236 : subd8_3 [3, -3, -4] = true := by decide +kernel
theorem subd8_3_1237 : subd8_3 [3, -3, -3] = true := by decide +kernel
theorem subd8_3_1238 : subd8_3 [3, -3, -2] = true := by decide +kernel
theorem subd8_3_1239 : subd8_3 [3, -3, -1] = true := by decide +kernel
theorem subd8_3_1240 : subd8_3 [3, -3, 0] = true := by decide +kernel
theorem subd8_3_1241 : subd8_3 [3, -3, 1] = true := by decide +kernel
theorem subd8_3_1242 : subd8_3 [3, -3, 2] = true := by decide +kernel
theorem subd8_3_1243 : subd8_3 [3, -3, 3] = true := by decide +kernel
theorem subd8_3_1244 : subd8_3 [3, -3, 4] = true := by decide +kernel
theorem subd8_3_1245 : subd8_3 [3, -3, 5] = true := by decide +kernel
theorem subd8_3_1246 : subd8_3 [3, -3, 6] = true := by decide +kernel
theorem subd8_3_1247 : subd8_3 [3, -2, -8] = true := by decide +kernel
theorem sbd8_3_38 : ∀ q ∈ blkd8_3_38, subd8_3 q = true := by
  unfold blkd8_3_38
  exact List.forall_mem_cons.2 ⟨subd8_3_1216, List.forall_mem_cons.2 ⟨subd8_3_1217, List.forall_mem_cons.2 ⟨subd8_3_1218, List.forall_mem_cons.2 ⟨subd8_3_1219, List.forall_mem_cons.2 ⟨subd8_3_1220, List.forall_mem_cons.2 ⟨subd8_3_1221, List.forall_mem_cons.2 ⟨subd8_3_1222, List.forall_mem_cons.2 ⟨subd8_3_1223, List.forall_mem_cons.2 ⟨subd8_3_1224, List.forall_mem_cons.2 ⟨subd8_3_1225, List.forall_mem_cons.2 ⟨subd8_3_1226, List.forall_mem_cons.2 ⟨subd8_3_1227, List.forall_mem_cons.2 ⟨subd8_3_1228, List.forall_mem_cons.2 ⟨subd8_3_1229, List.forall_mem_cons.2 ⟨subd8_3_1230, List.forall_mem_cons.2 ⟨subd8_3_1231, List.forall_mem_cons.2 ⟨subd8_3_1232, List.forall_mem_cons.2 ⟨subd8_3_1233, List.forall_mem_cons.2 ⟨subd8_3_1234, List.forall_mem_cons.2 ⟨subd8_3_1235, List.forall_mem_cons.2 ⟨subd8_3_1236, List.forall_mem_cons.2 ⟨subd8_3_1237, List.forall_mem_cons.2 ⟨subd8_3_1238, List.forall_mem_cons.2 ⟨subd8_3_1239, List.forall_mem_cons.2 ⟨subd8_3_1240, List.forall_mem_cons.2 ⟨subd8_3_1241, List.forall_mem_cons.2 ⟨subd8_3_1242, List.forall_mem_cons.2 ⟨subd8_3_1243, List.forall_mem_cons.2 ⟨subd8_3_1244, List.forall_mem_cons.2 ⟨subd8_3_1245, List.forall_mem_cons.2 ⟨subd8_3_1246, List.forall_mem_cons.2 ⟨subd8_3_1247, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_1248 : subd8_3 [3, -2, -7] = true := by decide +kernel
theorem subd8_3_1249 : subd8_3 [3, -2, -6] = true := by decide +kernel
theorem subd8_3_1250 : subd8_3 [3, -2, -5] = true := by decide +kernel
theorem subd8_3_1251 : subd8_3 [3, -2, -4] = true := by decide +kernel
theorem subd8_3_1252 : subd8_3 [3, -2, -3] = true := by decide +kernel
theorem subd8_3_1253 : subd8_3 [3, -2, -2] = true := by decide +kernel
theorem subd8_3_1254 : subd8_3 [3, -2, -1] = true := by decide +kernel
theorem subd8_3_1255 : subd8_3 [3, -2, 0] = true := by decide +kernel
theorem subd8_3_1256 : subd8_3 [3, -2, 1] = true := by decide +kernel
theorem subd8_3_1257 : subd8_3 [3, -2, 2] = true := by decide +kernel
theorem subd8_3_1258 : subd8_3 [3, -2, 3] = true := by decide +kernel
theorem subd8_3_1259 : subd8_3 [3, -2, 4] = true := by decide +kernel
theorem subd8_3_1260 : subd8_3 [3, -2, 5] = true := by decide +kernel
theorem subd8_3_1261 : subd8_3 [3, -2, 6] = true := by decide +kernel
theorem subd8_3_1262 : subd8_3 [3, -2, 7] = true := by decide +kernel
theorem subd8_3_1263 : subd8_3 [3, -1, -8] = true := by decide +kernel
theorem subd8_3_1264 : subd8_3 [3, -1, -7] = true := by decide +kernel
theorem subd8_3_1265 : subd8_3 [3, -1, -6] = true := by decide +kernel
theorem subd8_3_1266 : subd8_3 [3, -1, -5] = true := by decide +kernel
theorem subd8_3_1267 : subd8_3 [3, -1, -4] = true := by decide +kernel
theorem subd8_3_1268 : subd8_3 [3, -1, -3] = true := by decide +kernel
theorem subd8_3_1269 : subd8_3 [3, -1, -2] = true := by decide +kernel
theorem subd8_3_1270 : subd8_3 [3, -1, -1] = true := by decide +kernel
theorem subd8_3_1271 : subd8_3 [3, -1, 0] = true := by decide +kernel
theorem subd8_3_1272 : subd8_3 [3, -1, 1] = true := by decide +kernel
theorem subd8_3_1273 : subd8_3 [3, -1, 2] = true := by decide +kernel
theorem subd8_3_1274 : subd8_3 [3, -1, 3] = true := by decide +kernel
theorem subd8_3_1275 : subd8_3 [3, -1, 4] = true := by decide +kernel
theorem subd8_3_1276 : subd8_3 [3, -1, 5] = true := by decide +kernel
theorem subd8_3_1277 : subd8_3 [3, -1, 6] = true := by decide +kernel
theorem subd8_3_1278 : subd8_3 [3, -1, 7] = true := by decide +kernel
theorem subd8_3_1279 : subd8_3 [3, -1, 8] = true := by decide +kernel
theorem sbd8_3_39 : ∀ q ∈ blkd8_3_39, subd8_3 q = true := by
  unfold blkd8_3_39
  exact List.forall_mem_cons.2 ⟨subd8_3_1248, List.forall_mem_cons.2 ⟨subd8_3_1249, List.forall_mem_cons.2 ⟨subd8_3_1250, List.forall_mem_cons.2 ⟨subd8_3_1251, List.forall_mem_cons.2 ⟨subd8_3_1252, List.forall_mem_cons.2 ⟨subd8_3_1253, List.forall_mem_cons.2 ⟨subd8_3_1254, List.forall_mem_cons.2 ⟨subd8_3_1255, List.forall_mem_cons.2 ⟨subd8_3_1256, List.forall_mem_cons.2 ⟨subd8_3_1257, List.forall_mem_cons.2 ⟨subd8_3_1258, List.forall_mem_cons.2 ⟨subd8_3_1259, List.forall_mem_cons.2 ⟨subd8_3_1260, List.forall_mem_cons.2 ⟨subd8_3_1261, List.forall_mem_cons.2 ⟨subd8_3_1262, List.forall_mem_cons.2 ⟨subd8_3_1263, List.forall_mem_cons.2 ⟨subd8_3_1264, List.forall_mem_cons.2 ⟨subd8_3_1265, List.forall_mem_cons.2 ⟨subd8_3_1266, List.forall_mem_cons.2 ⟨subd8_3_1267, List.forall_mem_cons.2 ⟨subd8_3_1268, List.forall_mem_cons.2 ⟨subd8_3_1269, List.forall_mem_cons.2 ⟨subd8_3_1270, List.forall_mem_cons.2 ⟨subd8_3_1271, List.forall_mem_cons.2 ⟨subd8_3_1272, List.forall_mem_cons.2 ⟨subd8_3_1273, List.forall_mem_cons.2 ⟨subd8_3_1274, List.forall_mem_cons.2 ⟨subd8_3_1275, List.forall_mem_cons.2 ⟨subd8_3_1276, List.forall_mem_cons.2 ⟨subd8_3_1277, List.forall_mem_cons.2 ⟨subd8_3_1278, List.forall_mem_cons.2 ⟨subd8_3_1279, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_1280 : subd8_3 [3, 0, -7] = true := by decide +kernel
theorem subd8_3_1281 : subd8_3 [3, 0, -6] = true := by decide +kernel
theorem subd8_3_1282 : subd8_3 [3, 0, -5] = true := by decide +kernel
theorem subd8_3_1283 : subd8_3 [3, 0, -4] = true := by decide +kernel
theorem subd8_3_1284 : subd8_3 [3, 0, -3] = true := by decide +kernel
theorem subd8_3_1285 : subd8_3 [3, 0, -2] = true := by decide +kernel
theorem subd8_3_1286 : subd8_3 [3, 0, -1] = true := by decide +kernel
theorem subd8_3_1287 : subd8_3 [3, 0, 0] = true := by decide +kernel
theorem subd8_3_1288 : subd8_3 [3, 0, 1] = true := by decide +kernel
theorem subd8_3_1289 : subd8_3 [3, 0, 2] = true := by decide +kernel
theorem subd8_3_1290 : subd8_3 [3, 0, 3] = true := by decide +kernel
theorem subd8_3_1291 : subd8_3 [3, 0, 4] = true := by decide +kernel
theorem subd8_3_1292 : subd8_3 [3, 0, 5] = true := by decide +kernel
theorem subd8_3_1293 : subd8_3 [3, 0, 6] = true := by decide +kernel
theorem subd8_3_1294 : subd8_3 [3, 0, 7] = true := by decide +kernel
theorem subd8_3_1295 : subd8_3 [3, 0, 8] = true := by decide +kernel
theorem subd8_3_1296 : subd8_3 [3, 0, 9] = true := by decide +kernel
theorem subd8_3_1297 : subd8_3 [3, 1, -7] = true := by decide +kernel
theorem subd8_3_1298 : subd8_3 [3, 1, -6] = true := by decide +kernel
theorem subd8_3_1299 : subd8_3 [3, 1, -5] = true := by decide +kernel
theorem subd8_3_1300 : subd8_3 [3, 1, -4] = true := by decide +kernel
theorem subd8_3_1301 : subd8_3 [3, 1, -3] = true := by decide +kernel
theorem subd8_3_1302 : subd8_3 [3, 1, -2] = true := by decide +kernel
theorem subd8_3_1303 : subd8_3 [3, 1, -1] = true := by decide +kernel
theorem subd8_3_1304 : subd8_3 [3, 1, 0] = true := by decide +kernel
theorem subd8_3_1305 : subd8_3 [3, 1, 1] = true := by decide +kernel
theorem subd8_3_1306 : subd8_3 [3, 1, 2] = true := by decide +kernel
theorem subd8_3_1307 : subd8_3 [3, 1, 3] = true := by decide +kernel
theorem subd8_3_1308 : subd8_3 [3, 1, 4] = true := by decide +kernel
theorem subd8_3_1309 : subd8_3 [3, 1, 5] = true := by decide +kernel
theorem subd8_3_1310 : subd8_3 [3, 1, 6] = true := by decide +kernel
theorem subd8_3_1311 : subd8_3 [3, 1, 7] = true := by decide +kernel
theorem sbd8_3_40 : ∀ q ∈ blkd8_3_40, subd8_3 q = true := by
  unfold blkd8_3_40
  exact List.forall_mem_cons.2 ⟨subd8_3_1280, List.forall_mem_cons.2 ⟨subd8_3_1281, List.forall_mem_cons.2 ⟨subd8_3_1282, List.forall_mem_cons.2 ⟨subd8_3_1283, List.forall_mem_cons.2 ⟨subd8_3_1284, List.forall_mem_cons.2 ⟨subd8_3_1285, List.forall_mem_cons.2 ⟨subd8_3_1286, List.forall_mem_cons.2 ⟨subd8_3_1287, List.forall_mem_cons.2 ⟨subd8_3_1288, List.forall_mem_cons.2 ⟨subd8_3_1289, List.forall_mem_cons.2 ⟨subd8_3_1290, List.forall_mem_cons.2 ⟨subd8_3_1291, List.forall_mem_cons.2 ⟨subd8_3_1292, List.forall_mem_cons.2 ⟨subd8_3_1293, List.forall_mem_cons.2 ⟨subd8_3_1294, List.forall_mem_cons.2 ⟨subd8_3_1295, List.forall_mem_cons.2 ⟨subd8_3_1296, List.forall_mem_cons.2 ⟨subd8_3_1297, List.forall_mem_cons.2 ⟨subd8_3_1298, List.forall_mem_cons.2 ⟨subd8_3_1299, List.forall_mem_cons.2 ⟨subd8_3_1300, List.forall_mem_cons.2 ⟨subd8_3_1301, List.forall_mem_cons.2 ⟨subd8_3_1302, List.forall_mem_cons.2 ⟨subd8_3_1303, List.forall_mem_cons.2 ⟨subd8_3_1304, List.forall_mem_cons.2 ⟨subd8_3_1305, List.forall_mem_cons.2 ⟨subd8_3_1306, List.forall_mem_cons.2 ⟨subd8_3_1307, List.forall_mem_cons.2 ⟨subd8_3_1308, List.forall_mem_cons.2 ⟨subd8_3_1309, List.forall_mem_cons.2 ⟨subd8_3_1310, List.forall_mem_cons.2 ⟨subd8_3_1311, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_1312 : subd8_3 [3, 1, 8] = true := by decide +kernel
theorem subd8_3_1313 : subd8_3 [3, 1, 9] = true := by decide +kernel
theorem subd8_3_1314 : subd8_3 [3, 2, -7] = true := by decide +kernel
theorem subd8_3_1315 : subd8_3 [3, 2, -6] = true := by decide +kernel
theorem subd8_3_1316 : subd8_3 [3, 2, -5] = true := by decide +kernel
theorem subd8_3_1317 : subd8_3 [3, 2, -4] = true := by decide +kernel
theorem subd8_3_1318 : subd8_3 [3, 2, -3] = true := by decide +kernel
theorem subd8_3_1319 : subd8_3 [3, 2, -2] = true := by decide +kernel
theorem subd8_3_1320 : subd8_3 [3, 2, -1] = true := by decide +kernel
theorem subd8_3_1321 : subd8_3 [3, 2, 0] = true := by decide +kernel
theorem subd8_3_1322 : subd8_3 [3, 2, 1] = true := by decide +kernel
theorem subd8_3_1323 : subd8_3 [3, 2, 2] = true := by decide +kernel
theorem subd8_3_1324 : subd8_3 [3, 2, 3] = true := by decide +kernel
theorem subd8_3_1325 : subd8_3 [3, 2, 4] = true := by decide +kernel
theorem subd8_3_1326 : subd8_3 [3, 2, 5] = true := by decide +kernel
theorem subd8_3_1327 : subd8_3 [3, 2, 6] = true := by decide +kernel
theorem subd8_3_1328 : subd8_3 [3, 2, 7] = true := by decide +kernel
theorem subd8_3_1329 : subd8_3 [3, 2, 8] = true := by decide +kernel
theorem subd8_3_1330 : subd8_3 [3, 2, 9] = true := by decide +kernel
theorem subd8_3_1331 : subd8_3 [3, 2, 10] = true := by decide +kernel
theorem subd8_3_1332 : subd8_3 [3, 3, -6] = true := by decide +kernel
theorem subd8_3_1333 : subd8_3 [3, 3, -5] = true := by decide +kernel
theorem subd8_3_1334 : subd8_3 [3, 3, -4] = true := by decide +kernel
theorem subd8_3_1335 : subd8_3 [3, 3, -3] = true := by decide +kernel
theorem subd8_3_1336 : subd8_3 [3, 3, -2] = true := by decide +kernel
theorem subd8_3_1337 : subd8_3 [3, 3, -1] = true := by decide +kernel
theorem subd8_3_1338 : subd8_3 [3, 3, 0] = true := by decide +kernel
theorem subd8_3_1339 : subd8_3 [3, 3, 1] = true := by decide +kernel
theorem subd8_3_1340 : subd8_3 [3, 3, 2] = true := by decide +kernel
theorem subd8_3_1341 : subd8_3 [3, 3, 3] = true := by decide +kernel
theorem subd8_3_1342 : subd8_3 [3, 3, 4] = true := by decide +kernel
theorem subd8_3_1343 : subd8_3 [3, 3, 5] = true := by decide +kernel
theorem sbd8_3_41 : ∀ q ∈ blkd8_3_41, subd8_3 q = true := by
  unfold blkd8_3_41
  exact List.forall_mem_cons.2 ⟨subd8_3_1312, List.forall_mem_cons.2 ⟨subd8_3_1313, List.forall_mem_cons.2 ⟨subd8_3_1314, List.forall_mem_cons.2 ⟨subd8_3_1315, List.forall_mem_cons.2 ⟨subd8_3_1316, List.forall_mem_cons.2 ⟨subd8_3_1317, List.forall_mem_cons.2 ⟨subd8_3_1318, List.forall_mem_cons.2 ⟨subd8_3_1319, List.forall_mem_cons.2 ⟨subd8_3_1320, List.forall_mem_cons.2 ⟨subd8_3_1321, List.forall_mem_cons.2 ⟨subd8_3_1322, List.forall_mem_cons.2 ⟨subd8_3_1323, List.forall_mem_cons.2 ⟨subd8_3_1324, List.forall_mem_cons.2 ⟨subd8_3_1325, List.forall_mem_cons.2 ⟨subd8_3_1326, List.forall_mem_cons.2 ⟨subd8_3_1327, List.forall_mem_cons.2 ⟨subd8_3_1328, List.forall_mem_cons.2 ⟨subd8_3_1329, List.forall_mem_cons.2 ⟨subd8_3_1330, List.forall_mem_cons.2 ⟨subd8_3_1331, List.forall_mem_cons.2 ⟨subd8_3_1332, List.forall_mem_cons.2 ⟨subd8_3_1333, List.forall_mem_cons.2 ⟨subd8_3_1334, List.forall_mem_cons.2 ⟨subd8_3_1335, List.forall_mem_cons.2 ⟨subd8_3_1336, List.forall_mem_cons.2 ⟨subd8_3_1337, List.forall_mem_cons.2 ⟨subd8_3_1338, List.forall_mem_cons.2 ⟨subd8_3_1339, List.forall_mem_cons.2 ⟨subd8_3_1340, List.forall_mem_cons.2 ⟨subd8_3_1341, List.forall_mem_cons.2 ⟨subd8_3_1342, List.forall_mem_cons.2 ⟨subd8_3_1343, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_1344 : subd8_3 [3, 3, 6] = true := by decide +kernel
theorem subd8_3_1345 : subd8_3 [3, 3, 7] = true := by decide +kernel
theorem subd8_3_1346 : subd8_3 [3, 3, 8] = true := by decide +kernel
theorem subd8_3_1347 : subd8_3 [3, 3, 9] = true := by decide +kernel
theorem subd8_3_1348 : subd8_3 [3, 3, 10] = true := by decide +kernel
theorem subd8_3_1349 : subd8_3 [3, 4, -5] = true := by decide +kernel
theorem subd8_3_1350 : subd8_3 [3, 4, -4] = true := by decide +kernel
theorem subd8_3_1351 : subd8_3 [3, 4, -3] = true := by decide +kernel
theorem subd8_3_1352 : subd8_3 [3, 4, -2] = true := by decide +kernel
theorem subd8_3_1353 : subd8_3 [3, 4, -1] = true := by decide +kernel
theorem subd8_3_1354 : subd8_3 [3, 4, 0] = true := by decide +kernel
theorem subd8_3_1355 : subd8_3 [3, 4, 1] = true := by decide +kernel
theorem subd8_3_1356 : subd8_3 [3, 4, 2] = true := by decide +kernel
theorem subd8_3_1357 : subd8_3 [3, 4, 3] = true := by decide +kernel
theorem subd8_3_1358 : subd8_3 [3, 4, 4] = true := by decide +kernel
theorem subd8_3_1359 : subd8_3 [3, 4, 5] = true := by decide +kernel
theorem subd8_3_1360 : subd8_3 [3, 4, 6] = true := by decide +kernel
theorem subd8_3_1361 : subd8_3 [3, 4, 7] = true := by decide +kernel
theorem subd8_3_1362 : subd8_3 [3, 4, 8] = true := by decide +kernel
theorem subd8_3_1363 : subd8_3 [3, 4, 9] = true := by decide +kernel
theorem subd8_3_1364 : subd8_3 [3, 4, 10] = true := by decide +kernel
theorem subd8_3_1365 : subd8_3 [3, 5, -4] = true := by decide +kernel
theorem subd8_3_1366 : subd8_3 [3, 5, -3] = true := by decide +kernel
theorem subd8_3_1367 : subd8_3 [3, 5, -2] = true := by decide +kernel
theorem subd8_3_1368 : subd8_3 [3, 5, -1] = true := by decide +kernel
theorem subd8_3_1369 : subd8_3 [3, 5, 0] = true := by decide +kernel
theorem subd8_3_1370 : subd8_3 [3, 5, 1] = true := by decide +kernel
theorem subd8_3_1371 : subd8_3 [3, 5, 2] = true := by decide +kernel
theorem subd8_3_1372 : subd8_3 [3, 5, 3] = true := by decide +kernel
theorem subd8_3_1373 : subd8_3 [3, 5, 4] = true := by decide +kernel
theorem subd8_3_1374 : subd8_3 [3, 5, 5] = true := by decide +kernel
theorem subd8_3_1375 : subd8_3 [3, 5, 6] = true := by decide +kernel
theorem sbd8_3_42 : ∀ q ∈ blkd8_3_42, subd8_3 q = true := by
  unfold blkd8_3_42
  exact List.forall_mem_cons.2 ⟨subd8_3_1344, List.forall_mem_cons.2 ⟨subd8_3_1345, List.forall_mem_cons.2 ⟨subd8_3_1346, List.forall_mem_cons.2 ⟨subd8_3_1347, List.forall_mem_cons.2 ⟨subd8_3_1348, List.forall_mem_cons.2 ⟨subd8_3_1349, List.forall_mem_cons.2 ⟨subd8_3_1350, List.forall_mem_cons.2 ⟨subd8_3_1351, List.forall_mem_cons.2 ⟨subd8_3_1352, List.forall_mem_cons.2 ⟨subd8_3_1353, List.forall_mem_cons.2 ⟨subd8_3_1354, List.forall_mem_cons.2 ⟨subd8_3_1355, List.forall_mem_cons.2 ⟨subd8_3_1356, List.forall_mem_cons.2 ⟨subd8_3_1357, List.forall_mem_cons.2 ⟨subd8_3_1358, List.forall_mem_cons.2 ⟨subd8_3_1359, List.forall_mem_cons.2 ⟨subd8_3_1360, List.forall_mem_cons.2 ⟨subd8_3_1361, List.forall_mem_cons.2 ⟨subd8_3_1362, List.forall_mem_cons.2 ⟨subd8_3_1363, List.forall_mem_cons.2 ⟨subd8_3_1364, List.forall_mem_cons.2 ⟨subd8_3_1365, List.forall_mem_cons.2 ⟨subd8_3_1366, List.forall_mem_cons.2 ⟨subd8_3_1367, List.forall_mem_cons.2 ⟨subd8_3_1368, List.forall_mem_cons.2 ⟨subd8_3_1369, List.forall_mem_cons.2 ⟨subd8_3_1370, List.forall_mem_cons.2 ⟨subd8_3_1371, List.forall_mem_cons.2 ⟨subd8_3_1372, List.forall_mem_cons.2 ⟨subd8_3_1373, List.forall_mem_cons.2 ⟨subd8_3_1374, List.forall_mem_cons.2 ⟨subd8_3_1375, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_1376 : subd8_3 [3, 5, 7] = true := by decide +kernel
theorem subd8_3_1377 : subd8_3 [3, 5, 8] = true := by decide +kernel
theorem subd8_3_1378 : subd8_3 [3, 5, 9] = true := by decide +kernel
theorem subd8_3_1379 : subd8_3 [3, 6] = true := by decide +kernel
theorem subd8_3_1380 : subd8_3 [3, 7] = true := by decide +kernel
theorem subd8_3_1381 : subd8_3 [4, -5] = true := by decide +kernel
theorem subd8_3_1382 : subd8_3 [4, -4] = true := by decide +kernel
theorem subd8_3_1383 : subd8_3 [4, -3] = true := by decide +kernel
theorem subd8_3_1384 : subd8_3 [4, -2, -6] = true := by decide +kernel
theorem subd8_3_1385 : subd8_3 [4, -2, -5] = true := by decide +kernel
theorem subd8_3_1386 : subd8_3 [4, -2, -4] = true := by decide +kernel
theorem subd8_3_1387 : subd8_3 [4, -2, -3] = true := by decide +kernel
theorem subd8_3_1388 : subd8_3 [4, -2, -2] = true := by decide +kernel
theorem subd8_3_1389 : subd8_3 [4, -2, -1] = true := by decide +kernel
theorem subd8_3_1390 : subd8_3 [4, -2, 0] = true := by decide +kernel
theorem subd8_3_1391 : subd8_3 [4, -2, 1] = true := by decide +kernel
theorem subd8_3_1392 : subd8_3 [4, -2, 2] = true := by decide +kernel
theorem subd8_3_1393 : subd8_3 [4, -2, 3] = true := by decide +kernel
theorem subd8_3_1394 : subd8_3 [4, -2, 4] = true := by decide +kernel
theorem subd8_3_1395 : subd8_3 [4, -2, 5] = true := by decide +kernel
theorem subd8_3_1396 : subd8_3 [4, -2, 6] = true := by decide +kernel
theorem subd8_3_1397 : subd8_3 [4, -1, -6] = true := by decide +kernel
theorem subd8_3_1398 : subd8_3 [4, -1, -5] = true := by decide +kernel
theorem subd8_3_1399 : subd8_3 [4, -1, -4] = true := by decide +kernel
theorem subd8_3_1400 : subd8_3 [4, -1, -3] = true := by decide +kernel
theorem subd8_3_1401 : subd8_3 [4, -1, -2] = true := by decide +kernel
theorem subd8_3_1402 : subd8_3 [4, -1, -1] = true := by decide +kernel
theorem subd8_3_1403 : subd8_3 [4, -1, 0] = true := by decide +kernel
theorem subd8_3_1404 : subd8_3 [4, -1, 1] = true := by decide +kernel
theorem subd8_3_1405 : subd8_3 [4, -1, 2] = true := by decide +kernel
theorem subd8_3_1406 : subd8_3 [4, -1, 3] = true := by decide +kernel
theorem subd8_3_1407 : subd8_3 [4, -1, 4] = true := by decide +kernel
theorem sbd8_3_43 : ∀ q ∈ blkd8_3_43, subd8_3 q = true := by
  unfold blkd8_3_43
  exact List.forall_mem_cons.2 ⟨subd8_3_1376, List.forall_mem_cons.2 ⟨subd8_3_1377, List.forall_mem_cons.2 ⟨subd8_3_1378, List.forall_mem_cons.2 ⟨subd8_3_1379, List.forall_mem_cons.2 ⟨subd8_3_1380, List.forall_mem_cons.2 ⟨subd8_3_1381, List.forall_mem_cons.2 ⟨subd8_3_1382, List.forall_mem_cons.2 ⟨subd8_3_1383, List.forall_mem_cons.2 ⟨subd8_3_1384, List.forall_mem_cons.2 ⟨subd8_3_1385, List.forall_mem_cons.2 ⟨subd8_3_1386, List.forall_mem_cons.2 ⟨subd8_3_1387, List.forall_mem_cons.2 ⟨subd8_3_1388, List.forall_mem_cons.2 ⟨subd8_3_1389, List.forall_mem_cons.2 ⟨subd8_3_1390, List.forall_mem_cons.2 ⟨subd8_3_1391, List.forall_mem_cons.2 ⟨subd8_3_1392, List.forall_mem_cons.2 ⟨subd8_3_1393, List.forall_mem_cons.2 ⟨subd8_3_1394, List.forall_mem_cons.2 ⟨subd8_3_1395, List.forall_mem_cons.2 ⟨subd8_3_1396, List.forall_mem_cons.2 ⟨subd8_3_1397, List.forall_mem_cons.2 ⟨subd8_3_1398, List.forall_mem_cons.2 ⟨subd8_3_1399, List.forall_mem_cons.2 ⟨subd8_3_1400, List.forall_mem_cons.2 ⟨subd8_3_1401, List.forall_mem_cons.2 ⟨subd8_3_1402, List.forall_mem_cons.2 ⟨subd8_3_1403, List.forall_mem_cons.2 ⟨subd8_3_1404, List.forall_mem_cons.2 ⟨subd8_3_1405, List.forall_mem_cons.2 ⟨subd8_3_1406, List.forall_mem_cons.2 ⟨subd8_3_1407, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_1408 : subd8_3 [4, -1, 5] = true := by decide +kernel
theorem subd8_3_1409 : subd8_3 [4, -1, 6] = true := by decide +kernel
theorem subd8_3_1410 : subd8_3 [4, -1, 7] = true := by decide +kernel
theorem subd8_3_1411 : subd8_3 [4, 0, -6] = true := by decide +kernel
theorem subd8_3_1412 : subd8_3 [4, 0, -5] = true := by decide +kernel
theorem subd8_3_1413 : subd8_3 [4, 0, -4] = true := by decide +kernel
theorem subd8_3_1414 : subd8_3 [4, 0, -3] = true := by decide +kernel
theorem subd8_3_1415 : subd8_3 [4, 0, -2] = true := by decide +kernel
theorem subd8_3_1416 : subd8_3 [4, 0, -1] = true := by decide +kernel
theorem subd8_3_1417 : subd8_3 [4, 0, 0] = true := by decide +kernel
theorem subd8_3_1418 : subd8_3 [4, 0, 1] = true := by decide +kernel
theorem subd8_3_1419 : subd8_3 [4, 0, 2] = true := by decide +kernel
theorem subd8_3_1420 : subd8_3 [4, 0, 3] = true := by decide +kernel
theorem subd8_3_1421 : subd8_3 [4, 0, 4] = true := by decide +kernel
theorem subd8_3_1422 : subd8_3 [4, 0, 5] = true := by decide +kernel
theorem subd8_3_1423 : subd8_3 [4, 0, 6] = true := by decide +kernel
theorem subd8_3_1424 : subd8_3 [4, 0, 7] = true := by decide +kernel
theorem subd8_3_1425 : subd8_3 [4, 0, 8] = true := by decide +kernel
theorem subd8_3_1426 : subd8_3 [4, 1, -6] = true := by decide +kernel
theorem subd8_3_1427 : subd8_3 [4, 1, -5] = true := by decide +kernel
theorem subd8_3_1428 : subd8_3 [4, 1, -4] = true := by decide +kernel
theorem subd8_3_1429 : subd8_3 [4, 1, -3] = true := by decide +kernel
theorem subd8_3_1430 : subd8_3 [4, 1, -2] = true := by decide +kernel
theorem subd8_3_1431 : subd8_3 [4, 1, -1] = true := by decide +kernel
theorem subd8_3_1432 : subd8_3 [4, 1, 0] = true := by decide +kernel
theorem subd8_3_1433 : subd8_3 [4, 1, 1] = true := by decide +kernel
theorem subd8_3_1434 : subd8_3 [4, 1, 2] = true := by decide +kernel
theorem subd8_3_1435 : subd8_3 [4, 1, 3] = true := by decide +kernel
theorem subd8_3_1436 : subd8_3 [4, 1, 4] = true := by decide +kernel
theorem subd8_3_1437 : subd8_3 [4, 1, 5] = true := by decide +kernel
theorem subd8_3_1438 : subd8_3 [4, 1, 6] = true := by decide +kernel
theorem subd8_3_1439 : subd8_3 [4, 1, 7] = true := by decide +kernel
theorem sbd8_3_44 : ∀ q ∈ blkd8_3_44, subd8_3 q = true := by
  unfold blkd8_3_44
  exact List.forall_mem_cons.2 ⟨subd8_3_1408, List.forall_mem_cons.2 ⟨subd8_3_1409, List.forall_mem_cons.2 ⟨subd8_3_1410, List.forall_mem_cons.2 ⟨subd8_3_1411, List.forall_mem_cons.2 ⟨subd8_3_1412, List.forall_mem_cons.2 ⟨subd8_3_1413, List.forall_mem_cons.2 ⟨subd8_3_1414, List.forall_mem_cons.2 ⟨subd8_3_1415, List.forall_mem_cons.2 ⟨subd8_3_1416, List.forall_mem_cons.2 ⟨subd8_3_1417, List.forall_mem_cons.2 ⟨subd8_3_1418, List.forall_mem_cons.2 ⟨subd8_3_1419, List.forall_mem_cons.2 ⟨subd8_3_1420, List.forall_mem_cons.2 ⟨subd8_3_1421, List.forall_mem_cons.2 ⟨subd8_3_1422, List.forall_mem_cons.2 ⟨subd8_3_1423, List.forall_mem_cons.2 ⟨subd8_3_1424, List.forall_mem_cons.2 ⟨subd8_3_1425, List.forall_mem_cons.2 ⟨subd8_3_1426, List.forall_mem_cons.2 ⟨subd8_3_1427, List.forall_mem_cons.2 ⟨subd8_3_1428, List.forall_mem_cons.2 ⟨subd8_3_1429, List.forall_mem_cons.2 ⟨subd8_3_1430, List.forall_mem_cons.2 ⟨subd8_3_1431, List.forall_mem_cons.2 ⟨subd8_3_1432, List.forall_mem_cons.2 ⟨subd8_3_1433, List.forall_mem_cons.2 ⟨subd8_3_1434, List.forall_mem_cons.2 ⟨subd8_3_1435, List.forall_mem_cons.2 ⟨subd8_3_1436, List.forall_mem_cons.2 ⟨subd8_3_1437, List.forall_mem_cons.2 ⟨subd8_3_1438, List.forall_mem_cons.2 ⟨subd8_3_1439, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_1440 : subd8_3 [4, 1, 8] = true := by decide +kernel
theorem subd8_3_1441 : subd8_3 [4, 1, 9] = true := by decide +kernel
theorem subd8_3_1442 : subd8_3 [4, 2, -6] = true := by decide +kernel
theorem subd8_3_1443 : subd8_3 [4, 2, -5] = true := by decide +kernel
theorem subd8_3_1444 : subd8_3 [4, 2, -4] = true := by decide +kernel
theorem subd8_3_1445 : subd8_3 [4, 2, -3] = true := by decide +kernel
theorem subd8_3_1446 : subd8_3 [4, 2, -2] = true := by decide +kernel
theorem subd8_3_1447 : subd8_3 [4, 2, -1] = true := by decide +kernel
theorem subd8_3_1448 : subd8_3 [4, 2, 0] = true := by decide +kernel
theorem subd8_3_1449 : subd8_3 [4, 2, 1] = true := by decide +kernel
theorem subd8_3_1450 : subd8_3 [4, 2, 2] = true := by decide +kernel
theorem subd8_3_1451 : subd8_3 [4, 2, 3] = true := by decide +kernel
theorem subd8_3_1452 : subd8_3 [4, 2, 4] = true := by decide +kernel
theorem subd8_3_1453 : subd8_3 [4, 2, 5] = true := by decide +kernel
theorem subd8_3_1454 : subd8_3 [4, 2, 6] = true := by decide +kernel
theorem subd8_3_1455 : subd8_3 [4, 2, 7] = true := by decide +kernel
theorem subd8_3_1456 : subd8_3 [4, 2, 8] = true := by decide +kernel
theorem subd8_3_1457 : subd8_3 [4, 2, 9] = true := by decide +kernel
theorem subd8_3_1458 : subd8_3 [4, 3, -5] = true := by decide +kernel
theorem subd8_3_1459 : subd8_3 [4, 3, -4] = true := by decide +kernel
theorem subd8_3_1460 : subd8_3 [4, 3, -3] = true := by decide +kernel
theorem subd8_3_1461 : subd8_3 [4, 3, -2] = true := by decide +kernel
theorem subd8_3_1462 : subd8_3 [4, 3, -1] = true := by decide +kernel
theorem subd8_3_1463 : subd8_3 [4, 3, 0] = true := by decide +kernel
theorem subd8_3_1464 : subd8_3 [4, 3, 1] = true := by decide +kernel
theorem subd8_3_1465 : subd8_3 [4, 3, 2] = true := by decide +kernel
theorem subd8_3_1466 : subd8_3 [4, 3, 3] = true := by decide +kernel
theorem subd8_3_1467 : subd8_3 [4, 3, 4] = true := by decide +kernel
theorem subd8_3_1468 : subd8_3 [4, 3, 5] = true := by decide +kernel
theorem subd8_3_1469 : subd8_3 [4, 3, 6] = true := by decide +kernel
theorem subd8_3_1470 : subd8_3 [4, 3, 7] = true := by decide +kernel
theorem subd8_3_1471 : subd8_3 [4, 3, 8] = true := by decide +kernel
theorem sbd8_3_45 : ∀ q ∈ blkd8_3_45, subd8_3 q = true := by
  unfold blkd8_3_45
  exact List.forall_mem_cons.2 ⟨subd8_3_1440, List.forall_mem_cons.2 ⟨subd8_3_1441, List.forall_mem_cons.2 ⟨subd8_3_1442, List.forall_mem_cons.2 ⟨subd8_3_1443, List.forall_mem_cons.2 ⟨subd8_3_1444, List.forall_mem_cons.2 ⟨subd8_3_1445, List.forall_mem_cons.2 ⟨subd8_3_1446, List.forall_mem_cons.2 ⟨subd8_3_1447, List.forall_mem_cons.2 ⟨subd8_3_1448, List.forall_mem_cons.2 ⟨subd8_3_1449, List.forall_mem_cons.2 ⟨subd8_3_1450, List.forall_mem_cons.2 ⟨subd8_3_1451, List.forall_mem_cons.2 ⟨subd8_3_1452, List.forall_mem_cons.2 ⟨subd8_3_1453, List.forall_mem_cons.2 ⟨subd8_3_1454, List.forall_mem_cons.2 ⟨subd8_3_1455, List.forall_mem_cons.2 ⟨subd8_3_1456, List.forall_mem_cons.2 ⟨subd8_3_1457, List.forall_mem_cons.2 ⟨subd8_3_1458, List.forall_mem_cons.2 ⟨subd8_3_1459, List.forall_mem_cons.2 ⟨subd8_3_1460, List.forall_mem_cons.2 ⟨subd8_3_1461, List.forall_mem_cons.2 ⟨subd8_3_1462, List.forall_mem_cons.2 ⟨subd8_3_1463, List.forall_mem_cons.2 ⟨subd8_3_1464, List.forall_mem_cons.2 ⟨subd8_3_1465, List.forall_mem_cons.2 ⟨subd8_3_1466, List.forall_mem_cons.2 ⟨subd8_3_1467, List.forall_mem_cons.2 ⟨subd8_3_1468, List.forall_mem_cons.2 ⟨subd8_3_1469, List.forall_mem_cons.2 ⟨subd8_3_1470, List.forall_mem_cons.2 ⟨subd8_3_1471, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_1472 : subd8_3 [4, 3, 9] = true := by decide +kernel
theorem subd8_3_1473 : subd8_3 [4, 4, -4] = true := by decide +kernel
theorem subd8_3_1474 : subd8_3 [4, 4, -3] = true := by decide +kernel
theorem subd8_3_1475 : subd8_3 [4, 4, -2] = true := by decide +kernel
theorem subd8_3_1476 : subd8_3 [4, 4, -1] = true := by decide +kernel
theorem subd8_3_1477 : subd8_3 [4, 4, 0] = true := by decide +kernel
theorem subd8_3_1478 : subd8_3 [4, 4, 1] = true := by decide +kernel
theorem subd8_3_1479 : subd8_3 [4, 4, 2] = true := by decide +kernel
theorem subd8_3_1480 : subd8_3 [4, 4, 3] = true := by decide +kernel
theorem subd8_3_1481 : subd8_3 [4, 4, 4] = true := by decide +kernel
theorem subd8_3_1482 : subd8_3 [4, 4, 5] = true := by decide +kernel
theorem subd8_3_1483 : subd8_3 [4, 4, 6] = true := by decide +kernel
theorem subd8_3_1484 : subd8_3 [4, 4, 7] = true := by decide +kernel
theorem subd8_3_1485 : subd8_3 [4, 4, 8] = true := by decide +kernel
theorem subd8_3_1486 : subd8_3 [4, 4, 9] = true := by decide +kernel
theorem subd8_3_1487 : subd8_3 [4, 5] = true := by decide +kernel
theorem subd8_3_1488 : subd8_3 [4, 6] = true := by decide +kernel
theorem subd8_3_1489 : subd8_3 [4, 7] = true := by decide +kernel
theorem subd8_3_1490 : subd8_3 [5, -4] = true := by decide +kernel
theorem subd8_3_1491 : subd8_3 [5, -3] = true := by decide +kernel
theorem subd8_3_1492 : subd8_3 [5, -2] = true := by decide +kernel
theorem subd8_3_1493 : subd8_3 [5, -1] = true := by decide +kernel
theorem subd8_3_1494 : subd8_3 [5, 0] = true := by decide +kernel
theorem subd8_3_1495 : subd8_3 [5, 1] = true := by decide +kernel
theorem subd8_3_1496 : subd8_3 [5, 2, -4] = true := by decide +kernel
theorem subd8_3_1497 : subd8_3 [5, 2, -3] = true := by decide +kernel
theorem subd8_3_1498 : subd8_3 [5, 2, -2] = true := by decide +kernel
theorem subd8_3_1499 : subd8_3 [5, 2, -1] = true := by decide +kernel
theorem subd8_3_1500 : subd8_3 [5, 2, 0] = true := by decide +kernel
theorem subd8_3_1501 : subd8_3 [5, 2, 1] = true := by decide +kernel
theorem subd8_3_1502 : subd8_3 [5, 2, 2] = true := by decide +kernel
theorem subd8_3_1503 : subd8_3 [5, 2, 3] = true := by decide +kernel
theorem sbd8_3_46 : ∀ q ∈ blkd8_3_46, subd8_3 q = true := by
  unfold blkd8_3_46
  exact List.forall_mem_cons.2 ⟨subd8_3_1472, List.forall_mem_cons.2 ⟨subd8_3_1473, List.forall_mem_cons.2 ⟨subd8_3_1474, List.forall_mem_cons.2 ⟨subd8_3_1475, List.forall_mem_cons.2 ⟨subd8_3_1476, List.forall_mem_cons.2 ⟨subd8_3_1477, List.forall_mem_cons.2 ⟨subd8_3_1478, List.forall_mem_cons.2 ⟨subd8_3_1479, List.forall_mem_cons.2 ⟨subd8_3_1480, List.forall_mem_cons.2 ⟨subd8_3_1481, List.forall_mem_cons.2 ⟨subd8_3_1482, List.forall_mem_cons.2 ⟨subd8_3_1483, List.forall_mem_cons.2 ⟨subd8_3_1484, List.forall_mem_cons.2 ⟨subd8_3_1485, List.forall_mem_cons.2 ⟨subd8_3_1486, List.forall_mem_cons.2 ⟨subd8_3_1487, List.forall_mem_cons.2 ⟨subd8_3_1488, List.forall_mem_cons.2 ⟨subd8_3_1489, List.forall_mem_cons.2 ⟨subd8_3_1490, List.forall_mem_cons.2 ⟨subd8_3_1491, List.forall_mem_cons.2 ⟨subd8_3_1492, List.forall_mem_cons.2 ⟨subd8_3_1493, List.forall_mem_cons.2 ⟨subd8_3_1494, List.forall_mem_cons.2 ⟨subd8_3_1495, List.forall_mem_cons.2 ⟨subd8_3_1496, List.forall_mem_cons.2 ⟨subd8_3_1497, List.forall_mem_cons.2 ⟨subd8_3_1498, List.forall_mem_cons.2 ⟨subd8_3_1499, List.forall_mem_cons.2 ⟨subd8_3_1500, List.forall_mem_cons.2 ⟨subd8_3_1501, List.forall_mem_cons.2 ⟨subd8_3_1502, List.forall_mem_cons.2 ⟨subd8_3_1503, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_1504 : subd8_3 [5, 2, 4] = true := by decide +kernel
theorem subd8_3_1505 : subd8_3 [5, 2, 5] = true := by decide +kernel
theorem subd8_3_1506 : subd8_3 [5, 2, 6] = true := by decide +kernel
theorem subd8_3_1507 : subd8_3 [5, 2, 7] = true := by decide +kernel
theorem subd8_3_1508 : subd8_3 [5, 2, 8] = true := by decide +kernel
theorem subd8_3_1509 : subd8_3 [5, 3] = true := by decide +kernel
theorem subd8_3_1510 : subd8_3 [5, 4] = true := by decide +kernel
theorem subd8_3_1511 : subd8_3 [5, 5] = true := by decide +kernel
theorem subd8_3_1512 : subd8_3 [5, 6] = true := by decide +kernel
theorem subd8_3_1513 : subd8_3 [6, -2] = true := by decide +kernel
theorem subd8_3_1514 : subd8_3 [6, -1] = true := by decide +kernel
theorem subd8_3_1515 : subd8_3 [6, 0] = true := by decide +kernel
theorem subd8_3_1516 : subd8_3 [6, 1] = true := by decide +kernel
theorem subd8_3_1517 : subd8_3 [6, 2] = true := by decide +kernel
theorem subd8_3_1518 : subd8_3 [6, 3] = true := by decide +kernel
theorem subd8_3_1519 : subd8_3 [6, 4] = true := by decide +kernel
theorem subd8_3_1520 : subd8_3 [6, 5] = true := by decide +kernel
theorem sbd8_3_47 : ∀ q ∈ blkd8_3_47, subd8_3 q = true := by
  unfold blkd8_3_47
  exact List.forall_mem_cons.2 ⟨subd8_3_1504, List.forall_mem_cons.2 ⟨subd8_3_1505, List.forall_mem_cons.2 ⟨subd8_3_1506, List.forall_mem_cons.2 ⟨subd8_3_1507, List.forall_mem_cons.2 ⟨subd8_3_1508, List.forall_mem_cons.2 ⟨subd8_3_1509, List.forall_mem_cons.2 ⟨subd8_3_1510, List.forall_mem_cons.2 ⟨subd8_3_1511, List.forall_mem_cons.2 ⟨subd8_3_1512, List.forall_mem_cons.2 ⟨subd8_3_1513, List.forall_mem_cons.2 ⟨subd8_3_1514, List.forall_mem_cons.2 ⟨subd8_3_1515, List.forall_mem_cons.2 ⟨subd8_3_1516, List.forall_mem_cons.2 ⟨subd8_3_1517, List.forall_mem_cons.2 ⟨subd8_3_1518, List.forall_mem_cons.2 ⟨subd8_3_1519, List.forall_mem_cons.2 ⟨subd8_3_1520, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_4 : ldCheck G d8_4.U d8_4.ms ldd8_4 = true := by decide +kernel
theorem pre_okd8_4 : subPre G cell8 d8_4 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C096
