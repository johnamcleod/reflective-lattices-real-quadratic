import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd19_1_1184 : subd19_1 [3, 2, -4] = true := by decide +kernel
theorem subd19_1_1185 : subd19_1 [3, 2, -3] = true := by decide +kernel
theorem subd19_1_1186 : subd19_1 [3, 2, -2] = true := by decide +kernel
theorem subd19_1_1187 : subd19_1 [3, 2, -1] = true := by decide +kernel
theorem subd19_1_1188 : subd19_1 [3, 2, 0] = true := by decide +kernel
theorem subd19_1_1189 : subd19_1 [3, 2, 1] = true := by decide +kernel
theorem subd19_1_1190 : subd19_1 [3, 2, 2] = true := by decide +kernel
theorem subd19_1_1191 : subd19_1 [3, 2, 3] = true := by decide +kernel
theorem subd19_1_1192 : subd19_1 [3, 2, 4] = true := by decide +kernel
theorem subd19_1_1193 : subd19_1 [3, 2, 5] = true := by decide +kernel
theorem subd19_1_1194 : subd19_1 [3, 2, 6] = true := by decide +kernel
theorem subd19_1_1195 : subd19_1 [3, 3, -8] = true := by decide +kernel
theorem subd19_1_1196 : subd19_1 [3, 3, -7] = true := by decide +kernel
theorem subd19_1_1197 : subd19_1 [3, 3, -6] = true := by decide +kernel
theorem subd19_1_1198 : subd19_1 [3, 3, -5] = true := by decide +kernel
theorem subd19_1_1199 : subd19_1 [3, 3, -4] = true := by decide +kernel
theorem subd19_1_1200 : subd19_1 [3, 3, -3] = true := by decide +kernel
theorem subd19_1_1201 : subd19_1 [3, 3, -2] = true := by decide +kernel
theorem subd19_1_1202 : subd19_1 [3, 3, -1] = true := by decide +kernel
theorem subd19_1_1203 : subd19_1 [3, 3, 0] = true := by decide +kernel
theorem subd19_1_1204 : subd19_1 [3, 3, 1] = true := by decide +kernel
theorem subd19_1_1205 : subd19_1 [3, 3, 2] = true := by decide +kernel
theorem subd19_1_1206 : subd19_1 [3, 3, 3] = true := by decide +kernel
theorem subd19_1_1207 : subd19_1 [3, 3, 4] = true := by decide +kernel
theorem subd19_1_1208 : subd19_1 [3, 3, 5] = true := by decide +kernel
theorem subd19_1_1209 : subd19_1 [3, 3, 6] = true := by decide +kernel
theorem subd19_1_1210 : subd19_1 [3, 4] = true := by decide +kernel
theorem subd19_1_1211 : subd19_1 [3, 5] = true := by decide +kernel
theorem subd19_1_1212 : subd19_1 [3, 6] = true := by decide +kernel
theorem subd19_1_1213 : subd19_1 [3, 7] = true := by decide +kernel
theorem subd19_1_1214 : subd19_1 [3, 8] = true := by decide +kernel
theorem subd19_1_1215 : subd19_1 [4, -9] = true := by decide +kernel
theorem sbd19_1_37 : ∀ q ∈ blkd19_1_37, subd19_1 q = true := by
  unfold blkd19_1_37
  exact List.forall_mem_cons.2 ⟨subd19_1_1184, List.forall_mem_cons.2 ⟨subd19_1_1185, List.forall_mem_cons.2 ⟨subd19_1_1186, List.forall_mem_cons.2 ⟨subd19_1_1187, List.forall_mem_cons.2 ⟨subd19_1_1188, List.forall_mem_cons.2 ⟨subd19_1_1189, List.forall_mem_cons.2 ⟨subd19_1_1190, List.forall_mem_cons.2 ⟨subd19_1_1191, List.forall_mem_cons.2 ⟨subd19_1_1192, List.forall_mem_cons.2 ⟨subd19_1_1193, List.forall_mem_cons.2 ⟨subd19_1_1194, List.forall_mem_cons.2 ⟨subd19_1_1195, List.forall_mem_cons.2 ⟨subd19_1_1196, List.forall_mem_cons.2 ⟨subd19_1_1197, List.forall_mem_cons.2 ⟨subd19_1_1198, List.forall_mem_cons.2 ⟨subd19_1_1199, List.forall_mem_cons.2 ⟨subd19_1_1200, List.forall_mem_cons.2 ⟨subd19_1_1201, List.forall_mem_cons.2 ⟨subd19_1_1202, List.forall_mem_cons.2 ⟨subd19_1_1203, List.forall_mem_cons.2 ⟨subd19_1_1204, List.forall_mem_cons.2 ⟨subd19_1_1205, List.forall_mem_cons.2 ⟨subd19_1_1206, List.forall_mem_cons.2 ⟨subd19_1_1207, List.forall_mem_cons.2 ⟨subd19_1_1208, List.forall_mem_cons.2 ⟨subd19_1_1209, List.forall_mem_cons.2 ⟨subd19_1_1210, List.forall_mem_cons.2 ⟨subd19_1_1211, List.forall_mem_cons.2 ⟨subd19_1_1212, List.forall_mem_cons.2 ⟨subd19_1_1213, List.forall_mem_cons.2 ⟨subd19_1_1214, List.forall_mem_cons.2 ⟨subd19_1_1215, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_1_1216 : subd19_1 [4, -8] = true := by decide +kernel
theorem subd19_1_1217 : subd19_1 [4, -7] = true := by decide +kernel
theorem subd19_1_1218 : subd19_1 [4, -6] = true := by decide +kernel
theorem subd19_1_1219 : subd19_1 [4, -5] = true := by decide +kernel
theorem subd19_1_1220 : subd19_1 [4, -4] = true := by decide +kernel
theorem subd19_1_1221 : subd19_1 [4, -3, -10] = true := by decide +kernel
theorem subd19_1_1222 : subd19_1 [4, -3, -9] = true := by decide +kernel
theorem subd19_1_1223 : subd19_1 [4, -3, -8] = true := by decide +kernel
theorem subd19_1_1224 : subd19_1 [4, -3, -7] = true := by decide +kernel
theorem subd19_1_1225 : subd19_1 [4, -3, -6] = true := by decide +kernel
theorem subd19_1_1226 : subd19_1 [4, -3, -5] = true := by decide +kernel
theorem subd19_1_1227 : subd19_1 [4, -3, -4] = true := by decide +kernel
theorem subd19_1_1228 : subd19_1 [4, -3, -3] = true := by decide +kernel
theorem subd19_1_1229 : subd19_1 [4, -3, -2] = true := by decide +kernel
theorem subd19_1_1230 : subd19_1 [4, -3, -1] = true := by decide +kernel
theorem subd19_1_1231 : subd19_1 [4, -3, 0] = true := by decide +kernel
theorem subd19_1_1232 : subd19_1 [4, -3, 1] = true := by decide +kernel
theorem subd19_1_1233 : subd19_1 [4, -3, 2] = true := by decide +kernel
theorem subd19_1_1234 : subd19_1 [4, -3, 3] = true := by decide +kernel
theorem subd19_1_1235 : subd19_1 [4, -2, -10] = true := by decide +kernel
theorem subd19_1_1236 : subd19_1 [4, -2, -9] = true := by decide +kernel
theorem subd19_1_1237 : subd19_1 [4, -2, -8] = true := by decide +kernel
theorem subd19_1_1238 : subd19_1 [4, -2, -7] = true := by decide +kernel
theorem subd19_1_1239 : subd19_1 [4, -2, -6] = true := by decide +kernel
theorem subd19_1_1240 : subd19_1 [4, -2, -5] = true := by decide +kernel
theorem subd19_1_1241 : subd19_1 [4, -2, -4] = true := by decide +kernel
theorem subd19_1_1242 : subd19_1 [4, -2, -3] = true := by decide +kernel
theorem subd19_1_1243 : subd19_1 [4, -2, -2] = true := by decide +kernel
theorem subd19_1_1244 : subd19_1 [4, -2, -1] = true := by decide +kernel
theorem subd19_1_1245 : subd19_1 [4, -2, 0] = true := by decide +kernel
theorem subd19_1_1246 : subd19_1 [4, -2, 1] = true := by decide +kernel
theorem subd19_1_1247 : subd19_1 [4, -2, 2] = true := by decide +kernel
theorem sbd19_1_38 : ∀ q ∈ blkd19_1_38, subd19_1 q = true := by
  unfold blkd19_1_38
  exact List.forall_mem_cons.2 ⟨subd19_1_1216, List.forall_mem_cons.2 ⟨subd19_1_1217, List.forall_mem_cons.2 ⟨subd19_1_1218, List.forall_mem_cons.2 ⟨subd19_1_1219, List.forall_mem_cons.2 ⟨subd19_1_1220, List.forall_mem_cons.2 ⟨subd19_1_1221, List.forall_mem_cons.2 ⟨subd19_1_1222, List.forall_mem_cons.2 ⟨subd19_1_1223, List.forall_mem_cons.2 ⟨subd19_1_1224, List.forall_mem_cons.2 ⟨subd19_1_1225, List.forall_mem_cons.2 ⟨subd19_1_1226, List.forall_mem_cons.2 ⟨subd19_1_1227, List.forall_mem_cons.2 ⟨subd19_1_1228, List.forall_mem_cons.2 ⟨subd19_1_1229, List.forall_mem_cons.2 ⟨subd19_1_1230, List.forall_mem_cons.2 ⟨subd19_1_1231, List.forall_mem_cons.2 ⟨subd19_1_1232, List.forall_mem_cons.2 ⟨subd19_1_1233, List.forall_mem_cons.2 ⟨subd19_1_1234, List.forall_mem_cons.2 ⟨subd19_1_1235, List.forall_mem_cons.2 ⟨subd19_1_1236, List.forall_mem_cons.2 ⟨subd19_1_1237, List.forall_mem_cons.2 ⟨subd19_1_1238, List.forall_mem_cons.2 ⟨subd19_1_1239, List.forall_mem_cons.2 ⟨subd19_1_1240, List.forall_mem_cons.2 ⟨subd19_1_1241, List.forall_mem_cons.2 ⟨subd19_1_1242, List.forall_mem_cons.2 ⟨subd19_1_1243, List.forall_mem_cons.2 ⟨subd19_1_1244, List.forall_mem_cons.2 ⟨subd19_1_1245, List.forall_mem_cons.2 ⟨subd19_1_1246, List.forall_mem_cons.2 ⟨subd19_1_1247, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_1_1248 : subd19_1 [4, -2, 3] = true := by decide +kernel
theorem subd19_1_1249 : subd19_1 [4, -2, 4] = true := by decide +kernel
theorem subd19_1_1250 : subd19_1 [4, -1, -10] = true := by decide +kernel
theorem subd19_1_1251 : subd19_1 [4, -1, -9] = true := by decide +kernel
theorem subd19_1_1252 : subd19_1 [4, -1, -8] = true := by decide +kernel
theorem subd19_1_1253 : subd19_1 [4, -1, -7] = true := by decide +kernel
theorem subd19_1_1254 : subd19_1 [4, -1, -6] = true := by decide +kernel
theorem subd19_1_1255 : subd19_1 [4, -1, -5] = true := by decide +kernel
theorem subd19_1_1256 : subd19_1 [4, -1, -4] = true := by decide +kernel
theorem subd19_1_1257 : subd19_1 [4, -1, -3] = true := by decide +kernel
theorem subd19_1_1258 : subd19_1 [4, -1, -2] = true := by decide +kernel
theorem subd19_1_1259 : subd19_1 [4, -1, -1] = true := by decide +kernel
theorem subd19_1_1260 : subd19_1 [4, -1, 0] = true := by decide +kernel
theorem subd19_1_1261 : subd19_1 [4, -1, 1] = true := by decide +kernel
theorem subd19_1_1262 : subd19_1 [4, -1, 2] = true := by decide +kernel
theorem subd19_1_1263 : subd19_1 [4, -1, 3] = true := by decide +kernel
theorem subd19_1_1264 : subd19_1 [4, -1, 4] = true := by decide +kernel
theorem subd19_1_1265 : subd19_1 [4, 0, -9] = true := by decide +kernel
theorem subd19_1_1266 : subd19_1 [4, 0, -8] = true := by decide +kernel
theorem subd19_1_1267 : subd19_1 [4, 0, -7] = true := by decide +kernel
theorem subd19_1_1268 : subd19_1 [4, 0, -6] = true := by decide +kernel
theorem subd19_1_1269 : subd19_1 [4, 0, -5] = true := by decide +kernel
theorem subd19_1_1270 : subd19_1 [4, 0, -4] = true := by decide +kernel
theorem subd19_1_1271 : subd19_1 [4, 0, -3] = true := by decide +kernel
theorem subd19_1_1272 : subd19_1 [4, 0, -2] = true := by decide +kernel
theorem subd19_1_1273 : subd19_1 [4, 0, -1] = true := by decide +kernel
theorem subd19_1_1274 : subd19_1 [4, 0, 0] = true := by decide +kernel
theorem subd19_1_1275 : subd19_1 [4, 0, 1] = true := by decide +kernel
theorem subd19_1_1276 : subd19_1 [4, 0, 2] = true := by decide +kernel
theorem subd19_1_1277 : subd19_1 [4, 0, 3] = true := by decide +kernel
theorem subd19_1_1278 : subd19_1 [4, 0, 4] = true := by decide +kernel
theorem subd19_1_1279 : subd19_1 [4, 1, -9] = true := by decide +kernel
theorem sbd19_1_39 : ∀ q ∈ blkd19_1_39, subd19_1 q = true := by
  unfold blkd19_1_39
  exact List.forall_mem_cons.2 ⟨subd19_1_1248, List.forall_mem_cons.2 ⟨subd19_1_1249, List.forall_mem_cons.2 ⟨subd19_1_1250, List.forall_mem_cons.2 ⟨subd19_1_1251, List.forall_mem_cons.2 ⟨subd19_1_1252, List.forall_mem_cons.2 ⟨subd19_1_1253, List.forall_mem_cons.2 ⟨subd19_1_1254, List.forall_mem_cons.2 ⟨subd19_1_1255, List.forall_mem_cons.2 ⟨subd19_1_1256, List.forall_mem_cons.2 ⟨subd19_1_1257, List.forall_mem_cons.2 ⟨subd19_1_1258, List.forall_mem_cons.2 ⟨subd19_1_1259, List.forall_mem_cons.2 ⟨subd19_1_1260, List.forall_mem_cons.2 ⟨subd19_1_1261, List.forall_mem_cons.2 ⟨subd19_1_1262, List.forall_mem_cons.2 ⟨subd19_1_1263, List.forall_mem_cons.2 ⟨subd19_1_1264, List.forall_mem_cons.2 ⟨subd19_1_1265, List.forall_mem_cons.2 ⟨subd19_1_1266, List.forall_mem_cons.2 ⟨subd19_1_1267, List.forall_mem_cons.2 ⟨subd19_1_1268, List.forall_mem_cons.2 ⟨subd19_1_1269, List.forall_mem_cons.2 ⟨subd19_1_1270, List.forall_mem_cons.2 ⟨subd19_1_1271, List.forall_mem_cons.2 ⟨subd19_1_1272, List.forall_mem_cons.2 ⟨subd19_1_1273, List.forall_mem_cons.2 ⟨subd19_1_1274, List.forall_mem_cons.2 ⟨subd19_1_1275, List.forall_mem_cons.2 ⟨subd19_1_1276, List.forall_mem_cons.2 ⟨subd19_1_1277, List.forall_mem_cons.2 ⟨subd19_1_1278, List.forall_mem_cons.2 ⟨subd19_1_1279, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_1_1280 : subd19_1 [4, 1, -8] = true := by decide +kernel
theorem subd19_1_1281 : subd19_1 [4, 1, -7] = true := by decide +kernel
theorem subd19_1_1282 : subd19_1 [4, 1, -6] = true := by decide +kernel
theorem subd19_1_1283 : subd19_1 [4, 1, -5] = true := by decide +kernel
theorem subd19_1_1284 : subd19_1 [4, 1, -4] = true := by decide +kernel
theorem subd19_1_1285 : subd19_1 [4, 1, -3] = true := by decide +kernel
theorem subd19_1_1286 : subd19_1 [4, 1, -2] = true := by decide +kernel
theorem subd19_1_1287 : subd19_1 [4, 1, -1] = true := by decide +kernel
theorem subd19_1_1288 : subd19_1 [4, 1, 0] = true := by decide +kernel
theorem subd19_1_1289 : subd19_1 [4, 1, 1] = true := by decide +kernel
theorem subd19_1_1290 : subd19_1 [4, 1, 2] = true := by decide +kernel
theorem subd19_1_1291 : subd19_1 [4, 1, 3] = true := by decide +kernel
theorem subd19_1_1292 : subd19_1 [4, 1, 4] = true := by decide +kernel
theorem subd19_1_1293 : subd19_1 [4, 1, 5] = true := by decide +kernel
theorem subd19_1_1294 : subd19_1 [4, 2, -8] = true := by decide +kernel
theorem subd19_1_1295 : subd19_1 [4, 2, -7] = true := by decide +kernel
theorem subd19_1_1296 : subd19_1 [4, 2, -6] = true := by decide +kernel
theorem subd19_1_1297 : subd19_1 [4, 2, -5] = true := by decide +kernel
theorem subd19_1_1298 : subd19_1 [4, 2, -4] = true := by decide +kernel
theorem subd19_1_1299 : subd19_1 [4, 2, -3] = true := by decide +kernel
theorem subd19_1_1300 : subd19_1 [4, 2, -2] = true := by decide +kernel
theorem subd19_1_1301 : subd19_1 [4, 2, -1] = true := by decide +kernel
theorem subd19_1_1302 : subd19_1 [4, 2, 0] = true := by decide +kernel
theorem subd19_1_1303 : subd19_1 [4, 2, 1] = true := by decide +kernel
theorem subd19_1_1304 : subd19_1 [4, 2, 2] = true := by decide +kernel
theorem subd19_1_1305 : subd19_1 [4, 2, 3] = true := by decide +kernel
theorem subd19_1_1306 : subd19_1 [4, 2, 4] = true := by decide +kernel
theorem subd19_1_1307 : subd19_1 [4, 2, 5] = true := by decide +kernel
theorem subd19_1_1308 : subd19_1 [4, 3, -8] = true := by decide +kernel
theorem subd19_1_1309 : subd19_1 [4, 3, -7] = true := by decide +kernel
theorem subd19_1_1310 : subd19_1 [4, 3, -6] = true := by decide +kernel
theorem subd19_1_1311 : subd19_1 [4, 3, -5] = true := by decide +kernel
theorem sbd19_1_40 : ∀ q ∈ blkd19_1_40, subd19_1 q = true := by
  unfold blkd19_1_40
  exact List.forall_mem_cons.2 ⟨subd19_1_1280, List.forall_mem_cons.2 ⟨subd19_1_1281, List.forall_mem_cons.2 ⟨subd19_1_1282, List.forall_mem_cons.2 ⟨subd19_1_1283, List.forall_mem_cons.2 ⟨subd19_1_1284, List.forall_mem_cons.2 ⟨subd19_1_1285, List.forall_mem_cons.2 ⟨subd19_1_1286, List.forall_mem_cons.2 ⟨subd19_1_1287, List.forall_mem_cons.2 ⟨subd19_1_1288, List.forall_mem_cons.2 ⟨subd19_1_1289, List.forall_mem_cons.2 ⟨subd19_1_1290, List.forall_mem_cons.2 ⟨subd19_1_1291, List.forall_mem_cons.2 ⟨subd19_1_1292, List.forall_mem_cons.2 ⟨subd19_1_1293, List.forall_mem_cons.2 ⟨subd19_1_1294, List.forall_mem_cons.2 ⟨subd19_1_1295, List.forall_mem_cons.2 ⟨subd19_1_1296, List.forall_mem_cons.2 ⟨subd19_1_1297, List.forall_mem_cons.2 ⟨subd19_1_1298, List.forall_mem_cons.2 ⟨subd19_1_1299, List.forall_mem_cons.2 ⟨subd19_1_1300, List.forall_mem_cons.2 ⟨subd19_1_1301, List.forall_mem_cons.2 ⟨subd19_1_1302, List.forall_mem_cons.2 ⟨subd19_1_1303, List.forall_mem_cons.2 ⟨subd19_1_1304, List.forall_mem_cons.2 ⟨subd19_1_1305, List.forall_mem_cons.2 ⟨subd19_1_1306, List.forall_mem_cons.2 ⟨subd19_1_1307, List.forall_mem_cons.2 ⟨subd19_1_1308, List.forall_mem_cons.2 ⟨subd19_1_1309, List.forall_mem_cons.2 ⟨subd19_1_1310, List.forall_mem_cons.2 ⟨subd19_1_1311, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_1_1312 : subd19_1 [4, 3, -4] = true := by decide +kernel
theorem subd19_1_1313 : subd19_1 [4, 3, -3] = true := by decide +kernel
theorem subd19_1_1314 : subd19_1 [4, 3, -2] = true := by decide +kernel
theorem subd19_1_1315 : subd19_1 [4, 3, -1] = true := by decide +kernel
theorem subd19_1_1316 : subd19_1 [4, 3, 0] = true := by decide +kernel
theorem subd19_1_1317 : subd19_1 [4, 3, 1] = true := by decide +kernel
theorem subd19_1_1318 : subd19_1 [4, 3, 2] = true := by decide +kernel
theorem subd19_1_1319 : subd19_1 [4, 3, 3] = true := by decide +kernel
theorem subd19_1_1320 : subd19_1 [4, 3, 4] = true := by decide +kernel
theorem subd19_1_1321 : subd19_1 [4, 3, 5] = true := by decide +kernel
theorem subd19_1_1322 : subd19_1 [4, 4] = true := by decide +kernel
theorem subd19_1_1323 : subd19_1 [4, 5] = true := by decide +kernel
theorem subd19_1_1324 : subd19_1 [4, 6] = true := by decide +kernel
theorem subd19_1_1325 : subd19_1 [4, 7] = true := by decide +kernel
theorem subd19_1_1326 : subd19_1 [4, 8] = true := by decide +kernel
theorem subd19_1_1327 : subd19_1 [5, -8] = true := by decide +kernel
theorem subd19_1_1328 : subd19_1 [5, -7] = true := by decide +kernel
theorem subd19_1_1329 : subd19_1 [5, -6] = true := by decide +kernel
theorem subd19_1_1330 : subd19_1 [5, -5] = true := by decide +kernel
theorem subd19_1_1331 : subd19_1 [5, -4] = true := by decide +kernel
theorem subd19_1_1332 : subd19_1 [5, -3] = true := by decide +kernel
theorem subd19_1_1333 : subd19_1 [5, -2] = true := by decide +kernel
theorem subd19_1_1334 : subd19_1 [5, -1] = true := by decide +kernel
theorem subd19_1_1335 : subd19_1 [5, 0, -9] = true := by decide +kernel
theorem subd19_1_1336 : subd19_1 [5, 0, -8] = true := by decide +kernel
theorem subd19_1_1337 : subd19_1 [5, 0, -7] = true := by decide +kernel
theorem subd19_1_1338 : subd19_1 [5, 0, -6] = true := by decide +kernel
theorem subd19_1_1339 : subd19_1 [5, 0, -5] = true := by decide +kernel
theorem subd19_1_1340 : subd19_1 [5, 0, -4] = true := by decide +kernel
theorem subd19_1_1341 : subd19_1 [5, 0, -3] = true := by decide +kernel
theorem subd19_1_1342 : subd19_1 [5, 0, -2] = true := by decide +kernel
theorem subd19_1_1343 : subd19_1 [5, 0, -1] = true := by decide +kernel
theorem sbd19_1_41 : ∀ q ∈ blkd19_1_41, subd19_1 q = true := by
  unfold blkd19_1_41
  exact List.forall_mem_cons.2 ⟨subd19_1_1312, List.forall_mem_cons.2 ⟨subd19_1_1313, List.forall_mem_cons.2 ⟨subd19_1_1314, List.forall_mem_cons.2 ⟨subd19_1_1315, List.forall_mem_cons.2 ⟨subd19_1_1316, List.forall_mem_cons.2 ⟨subd19_1_1317, List.forall_mem_cons.2 ⟨subd19_1_1318, List.forall_mem_cons.2 ⟨subd19_1_1319, List.forall_mem_cons.2 ⟨subd19_1_1320, List.forall_mem_cons.2 ⟨subd19_1_1321, List.forall_mem_cons.2 ⟨subd19_1_1322, List.forall_mem_cons.2 ⟨subd19_1_1323, List.forall_mem_cons.2 ⟨subd19_1_1324, List.forall_mem_cons.2 ⟨subd19_1_1325, List.forall_mem_cons.2 ⟨subd19_1_1326, List.forall_mem_cons.2 ⟨subd19_1_1327, List.forall_mem_cons.2 ⟨subd19_1_1328, List.forall_mem_cons.2 ⟨subd19_1_1329, List.forall_mem_cons.2 ⟨subd19_1_1330, List.forall_mem_cons.2 ⟨subd19_1_1331, List.forall_mem_cons.2 ⟨subd19_1_1332, List.forall_mem_cons.2 ⟨subd19_1_1333, List.forall_mem_cons.2 ⟨subd19_1_1334, List.forall_mem_cons.2 ⟨subd19_1_1335, List.forall_mem_cons.2 ⟨subd19_1_1336, List.forall_mem_cons.2 ⟨subd19_1_1337, List.forall_mem_cons.2 ⟨subd19_1_1338, List.forall_mem_cons.2 ⟨subd19_1_1339, List.forall_mem_cons.2 ⟨subd19_1_1340, List.forall_mem_cons.2 ⟨subd19_1_1341, List.forall_mem_cons.2 ⟨subd19_1_1342, List.forall_mem_cons.2 ⟨subd19_1_1343, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_1_1344 : subd19_1 [5, 0, 0] = true := by decide +kernel
theorem subd19_1_1345 : subd19_1 [5, 0, 1] = true := by decide +kernel
theorem subd19_1_1346 : subd19_1 [5, 0, 2] = true := by decide +kernel
theorem subd19_1_1347 : subd19_1 [5, 0, 3] = true := by decide +kernel
theorem subd19_1_1348 : subd19_1 [5, 0, 4] = true := by decide +kernel
theorem subd19_1_1349 : subd19_1 [5, 1] = true := by decide +kernel
theorem subd19_1_1350 : subd19_1 [5, 2] = true := by decide +kernel
theorem subd19_1_1351 : subd19_1 [5, 3] = true := by decide +kernel
theorem subd19_1_1352 : subd19_1 [5, 4] = true := by decide +kernel
theorem subd19_1_1353 : subd19_1 [5, 5] = true := by decide +kernel
theorem subd19_1_1354 : subd19_1 [5, 6] = true := by decide +kernel
theorem subd19_1_1355 : subd19_1 [5, 7] = true := by decide +kernel
theorem subd19_1_1356 : subd19_1 [6, -8] = true := by decide +kernel
theorem subd19_1_1357 : subd19_1 [6, -7] = true := by decide +kernel
theorem subd19_1_1358 : subd19_1 [6, -6] = true := by decide +kernel
theorem subd19_1_1359 : subd19_1 [6, -5] = true := by decide +kernel
theorem subd19_1_1360 : subd19_1 [6, -4] = true := by decide +kernel
theorem subd19_1_1361 : subd19_1 [6, -3] = true := by decide +kernel
theorem subd19_1_1362 : subd19_1 [6, -2] = true := by decide +kernel
theorem subd19_1_1363 : subd19_1 [6, -1] = true := by decide +kernel
theorem subd19_1_1364 : subd19_1 [6, 0] = true := by decide +kernel
theorem subd19_1_1365 : subd19_1 [6, 1] = true := by decide +kernel
theorem subd19_1_1366 : subd19_1 [6, 2] = true := by decide +kernel
theorem subd19_1_1367 : subd19_1 [6, 3] = true := by decide +kernel
theorem subd19_1_1368 : subd19_1 [6, 4] = true := by decide +kernel
theorem subd19_1_1369 : subd19_1 [6, 5] = true := by decide +kernel
theorem subd19_1_1370 : subd19_1 [6, 6] = true := by decide +kernel
theorem subd19_1_1371 : subd19_1 [7, -7] = true := by decide +kernel
theorem subd19_1_1372 : subd19_1 [7, -6] = true := by decide +kernel
theorem subd19_1_1373 : subd19_1 [7, -5] = true := by decide +kernel
theorem subd19_1_1374 : subd19_1 [7, -4] = true := by decide +kernel
theorem subd19_1_1375 : subd19_1 [7, -3] = true := by decide +kernel
theorem sbd19_1_42 : ∀ q ∈ blkd19_1_42, subd19_1 q = true := by
  unfold blkd19_1_42
  exact List.forall_mem_cons.2 ⟨subd19_1_1344, List.forall_mem_cons.2 ⟨subd19_1_1345, List.forall_mem_cons.2 ⟨subd19_1_1346, List.forall_mem_cons.2 ⟨subd19_1_1347, List.forall_mem_cons.2 ⟨subd19_1_1348, List.forall_mem_cons.2 ⟨subd19_1_1349, List.forall_mem_cons.2 ⟨subd19_1_1350, List.forall_mem_cons.2 ⟨subd19_1_1351, List.forall_mem_cons.2 ⟨subd19_1_1352, List.forall_mem_cons.2 ⟨subd19_1_1353, List.forall_mem_cons.2 ⟨subd19_1_1354, List.forall_mem_cons.2 ⟨subd19_1_1355, List.forall_mem_cons.2 ⟨subd19_1_1356, List.forall_mem_cons.2 ⟨subd19_1_1357, List.forall_mem_cons.2 ⟨subd19_1_1358, List.forall_mem_cons.2 ⟨subd19_1_1359, List.forall_mem_cons.2 ⟨subd19_1_1360, List.forall_mem_cons.2 ⟨subd19_1_1361, List.forall_mem_cons.2 ⟨subd19_1_1362, List.forall_mem_cons.2 ⟨subd19_1_1363, List.forall_mem_cons.2 ⟨subd19_1_1364, List.forall_mem_cons.2 ⟨subd19_1_1365, List.forall_mem_cons.2 ⟨subd19_1_1366, List.forall_mem_cons.2 ⟨subd19_1_1367, List.forall_mem_cons.2 ⟨subd19_1_1368, List.forall_mem_cons.2 ⟨subd19_1_1369, List.forall_mem_cons.2 ⟨subd19_1_1370, List.forall_mem_cons.2 ⟨subd19_1_1371, List.forall_mem_cons.2 ⟨subd19_1_1372, List.forall_mem_cons.2 ⟨subd19_1_1373, List.forall_mem_cons.2 ⟨subd19_1_1374, List.forall_mem_cons.2 ⟨subd19_1_1375, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_1_1376 : subd19_1 [7, -2] = true := by decide +kernel
theorem subd19_1_1377 : subd19_1 [7, -1] = true := by decide +kernel
theorem subd19_1_1378 : subd19_1 [7, 0] = true := by decide +kernel
theorem subd19_1_1379 : subd19_1 [7, 1] = true := by decide +kernel
theorem subd19_1_1380 : subd19_1 [7, 2] = true := by decide +kernel
theorem subd19_1_1381 : subd19_1 [7, 3] = true := by decide +kernel
theorem subd19_1_1382 : subd19_1 [7, 4] = true := by decide +kernel
theorem subd19_1_1383 : subd19_1 [7, 5] = true := by decide +kernel
theorem subd19_1_1384 : subd19_1 [8, -5] = true := by decide +kernel
theorem subd19_1_1385 : subd19_1 [8, -4] = true := by decide +kernel
theorem subd19_1_1386 : subd19_1 [8, -3] = true := by decide +kernel
theorem subd19_1_1387 : subd19_1 [8, -2] = true := by decide +kernel
theorem subd19_1_1388 : subd19_1 [8, -1] = true := by decide +kernel
theorem subd19_1_1389 : subd19_1 [8, 0] = true := by decide +kernel
theorem subd19_1_1390 : subd19_1 [8, 1] = true := by decide +kernel
theorem subd19_1_1391 : subd19_1 [8, 2] = true := by decide +kernel
theorem subd19_1_1392 : subd19_1 [8, 3] = true := by decide +kernel
theorem subd19_1_1393 : subd19_1 [8, 4] = true := by decide +kernel
theorem subd19_1_1394 : subd19_1 [9] = true := by decide +kernel
theorem sbd19_1_43 : ∀ q ∈ blkd19_1_43, subd19_1 q = true := by
  unfold blkd19_1_43
  exact List.forall_mem_cons.2 ⟨subd19_1_1376, List.forall_mem_cons.2 ⟨subd19_1_1377, List.forall_mem_cons.2 ⟨subd19_1_1378, List.forall_mem_cons.2 ⟨subd19_1_1379, List.forall_mem_cons.2 ⟨subd19_1_1380, List.forall_mem_cons.2 ⟨subd19_1_1381, List.forall_mem_cons.2 ⟨subd19_1_1382, List.forall_mem_cons.2 ⟨subd19_1_1383, List.forall_mem_cons.2 ⟨subd19_1_1384, List.forall_mem_cons.2 ⟨subd19_1_1385, List.forall_mem_cons.2 ⟨subd19_1_1386, List.forall_mem_cons.2 ⟨subd19_1_1387, List.forall_mem_cons.2 ⟨subd19_1_1388, List.forall_mem_cons.2 ⟨subd19_1_1389, List.forall_mem_cons.2 ⟨subd19_1_1390, List.forall_mem_cons.2 ⟨subd19_1_1391, List.forall_mem_cons.2 ⟨subd19_1_1392, List.forall_mem_cons.2 ⟨subd19_1_1393, List.forall_mem_cons.2 ⟨subd19_1_1394, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd19_2 : ldCheck G d19_2.U d19_2.ms ldd19_2 = true := by decide +kernel
theorem pre_okd19_2 : subPre G cell19 d19_2 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C143
