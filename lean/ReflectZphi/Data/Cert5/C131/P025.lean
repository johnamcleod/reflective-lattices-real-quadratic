import ReflectZphi.Data.Cert5.C131.Base

namespace ReflectZphi.Data.Cert5.C131

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd12_0_1152 : subd12_0 [3, -2, 0] = true := by decide +kernel
theorem subd12_0_1153 : subd12_0 [3, -2, 1] = true := by decide +kernel
theorem subd12_0_1154 : subd12_0 [3, -2, 2] = true := by decide +kernel
theorem subd12_0_1155 : subd12_0 [3, -2, 3] = true := by decide +kernel
theorem subd12_0_1156 : subd12_0 [3, -2, 4] = true := by decide +kernel
theorem subd12_0_1157 : subd12_0 [3, -2, 5] = true := by decide +kernel
theorem subd12_0_1158 : subd12_0 [3, -2, 6] = true := by decide +kernel
theorem subd12_0_1159 : subd12_0 [3, -1, -8] = true := by decide +kernel
theorem subd12_0_1160 : subd12_0 [3, -1, -7] = true := by decide +kernel
theorem subd12_0_1161 : subd12_0 [3, -1, -6] = true := by decide +kernel
theorem subd12_0_1162 : subd12_0 [3, -1, -5] = true := by decide +kernel
theorem subd12_0_1163 : subd12_0 [3, -1, -4] = true := by decide +kernel
theorem subd12_0_1164 : subd12_0 [3, -1, -3] = true := by decide +kernel
theorem subd12_0_1165 : subd12_0 [3, -1, -2] = true := by decide +kernel
theorem subd12_0_1166 : subd12_0 [3, -1, -1] = true := by decide +kernel
theorem subd12_0_1167 : subd12_0 [3, -1, 0] = true := by decide +kernel
theorem subd12_0_1168 : subd12_0 [3, -1, 1] = true := by decide +kernel
theorem subd12_0_1169 : subd12_0 [3, -1, 2] = true := by decide +kernel
theorem subd12_0_1170 : subd12_0 [3, -1, 3] = true := by decide +kernel
theorem subd12_0_1171 : subd12_0 [3, -1, 4] = true := by decide +kernel
theorem subd12_0_1172 : subd12_0 [3, -1, 5] = true := by decide +kernel
theorem subd12_0_1173 : subd12_0 [3, -1, 6] = true := by decide +kernel
theorem subd12_0_1174 : subd12_0 [3, -1, 7] = true := by decide +kernel
theorem subd12_0_1175 : subd12_0 [3, 0, -8] = true := by decide +kernel
theorem subd12_0_1176 : subd12_0 [3, 0, -7] = true := by decide +kernel
theorem subd12_0_1177 : subd12_0 [3, 0, -6] = true := by decide +kernel
theorem subd12_0_1178 : subd12_0 [3, 0, -5] = true := by decide +kernel
theorem subd12_0_1179 : subd12_0 [3, 0, -4] = true := by decide +kernel
theorem subd12_0_1180 : subd12_0 [3, 0, -3] = true := by decide +kernel
theorem subd12_0_1181 : subd12_0 [3, 0, -2] = true := by decide +kernel
theorem subd12_0_1182 : subd12_0 [3, 0, -1] = true := by decide +kernel
theorem subd12_0_1183 : subd12_0 [3, 0, 0] = true := by decide +kernel
theorem sbd12_0_36 : ∀ q ∈ blkd12_0_36, subd12_0 q = true := by
  unfold blkd12_0_36
  exact List.forall_mem_cons.2 ⟨subd12_0_1152, List.forall_mem_cons.2 ⟨subd12_0_1153, List.forall_mem_cons.2 ⟨subd12_0_1154, List.forall_mem_cons.2 ⟨subd12_0_1155, List.forall_mem_cons.2 ⟨subd12_0_1156, List.forall_mem_cons.2 ⟨subd12_0_1157, List.forall_mem_cons.2 ⟨subd12_0_1158, List.forall_mem_cons.2 ⟨subd12_0_1159, List.forall_mem_cons.2 ⟨subd12_0_1160, List.forall_mem_cons.2 ⟨subd12_0_1161, List.forall_mem_cons.2 ⟨subd12_0_1162, List.forall_mem_cons.2 ⟨subd12_0_1163, List.forall_mem_cons.2 ⟨subd12_0_1164, List.forall_mem_cons.2 ⟨subd12_0_1165, List.forall_mem_cons.2 ⟨subd12_0_1166, List.forall_mem_cons.2 ⟨subd12_0_1167, List.forall_mem_cons.2 ⟨subd12_0_1168, List.forall_mem_cons.2 ⟨subd12_0_1169, List.forall_mem_cons.2 ⟨subd12_0_1170, List.forall_mem_cons.2 ⟨subd12_0_1171, List.forall_mem_cons.2 ⟨subd12_0_1172, List.forall_mem_cons.2 ⟨subd12_0_1173, List.forall_mem_cons.2 ⟨subd12_0_1174, List.forall_mem_cons.2 ⟨subd12_0_1175, List.forall_mem_cons.2 ⟨subd12_0_1176, List.forall_mem_cons.2 ⟨subd12_0_1177, List.forall_mem_cons.2 ⟨subd12_0_1178, List.forall_mem_cons.2 ⟨subd12_0_1179, List.forall_mem_cons.2 ⟨subd12_0_1180, List.forall_mem_cons.2 ⟨subd12_0_1181, List.forall_mem_cons.2 ⟨subd12_0_1182, List.forall_mem_cons.2 ⟨subd12_0_1183, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_1184 : subd12_0 [3, 0, 1] = true := by decide +kernel
theorem subd12_0_1185 : subd12_0 [3, 0, 2] = true := by decide +kernel
theorem subd12_0_1186 : subd12_0 [3, 0, 3] = true := by decide +kernel
theorem subd12_0_1187 : subd12_0 [3, 0, 4] = true := by decide +kernel
theorem subd12_0_1188 : subd12_0 [3, 0, 5] = true := by decide +kernel
theorem subd12_0_1189 : subd12_0 [3, 0, 6] = true := by decide +kernel
theorem subd12_0_1190 : subd12_0 [3, 0, 7] = true := by decide +kernel
theorem subd12_0_1191 : subd12_0 [3, 1, -7] = true := by decide +kernel
theorem subd12_0_1192 : subd12_0 [3, 1, -6] = true := by decide +kernel
theorem subd12_0_1193 : subd12_0 [3, 1, -5] = true := by decide +kernel
theorem subd12_0_1194 : subd12_0 [3, 1, -4] = true := by decide +kernel
theorem subd12_0_1195 : subd12_0 [3, 1, -3] = true := by decide +kernel
theorem subd12_0_1196 : subd12_0 [3, 1, -2] = true := by decide +kernel
theorem subd12_0_1197 : subd12_0 [3, 1, -1] = true := by decide +kernel
theorem subd12_0_1198 : subd12_0 [3, 1, 0] = true := by decide +kernel
theorem subd12_0_1199 : subd12_0 [3, 1, 1] = true := by decide +kernel
theorem subd12_0_1200 : subd12_0 [3, 1, 2] = true := by decide +kernel
theorem subd12_0_1201 : subd12_0 [3, 1, 3] = true := by decide +kernel
theorem subd12_0_1202 : subd12_0 [3, 1, 4] = true := by decide +kernel
theorem subd12_0_1203 : subd12_0 [3, 1, 5] = true := by decide +kernel
theorem subd12_0_1204 : subd12_0 [3, 1, 6] = true := by decide +kernel
theorem subd12_0_1205 : subd12_0 [3, 1, 7] = true := by decide +kernel
theorem subd12_0_1206 : subd12_0 [3, 2, -7] = true := by decide +kernel
theorem subd12_0_1207 : subd12_0 [3, 2, -6] = true := by decide +kernel
theorem subd12_0_1208 : subd12_0 [3, 2, -5] = true := by decide +kernel
theorem subd12_0_1209 : subd12_0 [3, 2, -4] = true := by decide +kernel
theorem subd12_0_1210 : subd12_0 [3, 2, -3] = true := by decide +kernel
theorem subd12_0_1211 : subd12_0 [3, 2, -2] = true := by decide +kernel
theorem subd12_0_1212 : subd12_0 [3, 2, -1] = true := by decide +kernel
theorem subd12_0_1213 : subd12_0 [3, 2, 0] = true := by decide +kernel
theorem subd12_0_1214 : subd12_0 [3, 2, 1] = true := by decide +kernel
theorem subd12_0_1215 : subd12_0 [3, 2, 2] = true := by decide +kernel
theorem sbd12_0_37 : ∀ q ∈ blkd12_0_37, subd12_0 q = true := by
  unfold blkd12_0_37
  exact List.forall_mem_cons.2 ⟨subd12_0_1184, List.forall_mem_cons.2 ⟨subd12_0_1185, List.forall_mem_cons.2 ⟨subd12_0_1186, List.forall_mem_cons.2 ⟨subd12_0_1187, List.forall_mem_cons.2 ⟨subd12_0_1188, List.forall_mem_cons.2 ⟨subd12_0_1189, List.forall_mem_cons.2 ⟨subd12_0_1190, List.forall_mem_cons.2 ⟨subd12_0_1191, List.forall_mem_cons.2 ⟨subd12_0_1192, List.forall_mem_cons.2 ⟨subd12_0_1193, List.forall_mem_cons.2 ⟨subd12_0_1194, List.forall_mem_cons.2 ⟨subd12_0_1195, List.forall_mem_cons.2 ⟨subd12_0_1196, List.forall_mem_cons.2 ⟨subd12_0_1197, List.forall_mem_cons.2 ⟨subd12_0_1198, List.forall_mem_cons.2 ⟨subd12_0_1199, List.forall_mem_cons.2 ⟨subd12_0_1200, List.forall_mem_cons.2 ⟨subd12_0_1201, List.forall_mem_cons.2 ⟨subd12_0_1202, List.forall_mem_cons.2 ⟨subd12_0_1203, List.forall_mem_cons.2 ⟨subd12_0_1204, List.forall_mem_cons.2 ⟨subd12_0_1205, List.forall_mem_cons.2 ⟨subd12_0_1206, List.forall_mem_cons.2 ⟨subd12_0_1207, List.forall_mem_cons.2 ⟨subd12_0_1208, List.forall_mem_cons.2 ⟨subd12_0_1209, List.forall_mem_cons.2 ⟨subd12_0_1210, List.forall_mem_cons.2 ⟨subd12_0_1211, List.forall_mem_cons.2 ⟨subd12_0_1212, List.forall_mem_cons.2 ⟨subd12_0_1213, List.forall_mem_cons.2 ⟨subd12_0_1214, List.forall_mem_cons.2 ⟨subd12_0_1215, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_1216 : subd12_0 [3, 2, 3] = true := by decide +kernel
theorem subd12_0_1217 : subd12_0 [3, 2, 4] = true := by decide +kernel
theorem subd12_0_1218 : subd12_0 [3, 2, 5] = true := by decide +kernel
theorem subd12_0_1219 : subd12_0 [3, 2, 6] = true := by decide +kernel
theorem subd12_0_1220 : subd12_0 [3, 2, 7] = true := by decide +kernel
theorem subd12_0_1221 : subd12_0 [3, 2, 8] = true := by decide +kernel
theorem subd12_0_1222 : subd12_0 [3, 3, -6] = true := by decide +kernel
theorem subd12_0_1223 : subd12_0 [3, 3, -5] = true := by decide +kernel
theorem subd12_0_1224 : subd12_0 [3, 3, -4] = true := by decide +kernel
theorem subd12_0_1225 : subd12_0 [3, 3, -3] = true := by decide +kernel
theorem subd12_0_1226 : subd12_0 [3, 3, -2] = true := by decide +kernel
theorem subd12_0_1227 : subd12_0 [3, 3, -1] = true := by decide +kernel
theorem subd12_0_1228 : subd12_0 [3, 3, 0] = true := by decide +kernel
theorem subd12_0_1229 : subd12_0 [3, 3, 1] = true := by decide +kernel
theorem subd12_0_1230 : subd12_0 [3, 3, 2] = true := by decide +kernel
theorem subd12_0_1231 : subd12_0 [3, 3, 3] = true := by decide +kernel
theorem subd12_0_1232 : subd12_0 [3, 3, 4] = true := by decide +kernel
theorem subd12_0_1233 : subd12_0 [3, 3, 5] = true := by decide +kernel
theorem subd12_0_1234 : subd12_0 [3, 3, 6] = true := by decide +kernel
theorem subd12_0_1235 : subd12_0 [3, 3, 7] = true := by decide +kernel
theorem subd12_0_1236 : subd12_0 [3, 3, 8] = true := by decide +kernel
theorem subd12_0_1237 : subd12_0 [3, 4] = true := by decide +kernel
theorem subd12_0_1238 : subd12_0 [3, 5] = true := by decide +kernel
theorem subd12_0_1239 : subd12_0 [3, 6] = true := by decide +kernel
theorem subd12_0_1240 : subd12_0 [3, 7] = true := by decide +kernel
theorem subd12_0_1241 : subd12_0 [4, -8] = true := by decide +kernel
theorem subd12_0_1242 : subd12_0 [4, -7] = true := by decide +kernel
theorem subd12_0_1243 : subd12_0 [4, -6] = true := by decide +kernel
theorem subd12_0_1244 : subd12_0 [4, -5] = true := by decide +kernel
theorem subd12_0_1245 : subd12_0 [4, -4] = true := by decide +kernel
theorem subd12_0_1246 : subd12_0 [4, -3, -8] = true := by decide +kernel
theorem subd12_0_1247 : subd12_0 [4, -3, -7] = true := by decide +kernel
theorem sbd12_0_38 : ∀ q ∈ blkd12_0_38, subd12_0 q = true := by
  unfold blkd12_0_38
  exact List.forall_mem_cons.2 ⟨subd12_0_1216, List.forall_mem_cons.2 ⟨subd12_0_1217, List.forall_mem_cons.2 ⟨subd12_0_1218, List.forall_mem_cons.2 ⟨subd12_0_1219, List.forall_mem_cons.2 ⟨subd12_0_1220, List.forall_mem_cons.2 ⟨subd12_0_1221, List.forall_mem_cons.2 ⟨subd12_0_1222, List.forall_mem_cons.2 ⟨subd12_0_1223, List.forall_mem_cons.2 ⟨subd12_0_1224, List.forall_mem_cons.2 ⟨subd12_0_1225, List.forall_mem_cons.2 ⟨subd12_0_1226, List.forall_mem_cons.2 ⟨subd12_0_1227, List.forall_mem_cons.2 ⟨subd12_0_1228, List.forall_mem_cons.2 ⟨subd12_0_1229, List.forall_mem_cons.2 ⟨subd12_0_1230, List.forall_mem_cons.2 ⟨subd12_0_1231, List.forall_mem_cons.2 ⟨subd12_0_1232, List.forall_mem_cons.2 ⟨subd12_0_1233, List.forall_mem_cons.2 ⟨subd12_0_1234, List.forall_mem_cons.2 ⟨subd12_0_1235, List.forall_mem_cons.2 ⟨subd12_0_1236, List.forall_mem_cons.2 ⟨subd12_0_1237, List.forall_mem_cons.2 ⟨subd12_0_1238, List.forall_mem_cons.2 ⟨subd12_0_1239, List.forall_mem_cons.2 ⟨subd12_0_1240, List.forall_mem_cons.2 ⟨subd12_0_1241, List.forall_mem_cons.2 ⟨subd12_0_1242, List.forall_mem_cons.2 ⟨subd12_0_1243, List.forall_mem_cons.2 ⟨subd12_0_1244, List.forall_mem_cons.2 ⟨subd12_0_1245, List.forall_mem_cons.2 ⟨subd12_0_1246, List.forall_mem_cons.2 ⟨subd12_0_1247, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_1248 : subd12_0 [4, -3, -6] = true := by decide +kernel
theorem subd12_0_1249 : subd12_0 [4, -3, -5] = true := by decide +kernel
theorem subd12_0_1250 : subd12_0 [4, -3, -4] = true := by decide +kernel
theorem subd12_0_1251 : subd12_0 [4, -3, -3] = true := by decide +kernel
theorem subd12_0_1252 : subd12_0 [4, -3, -2] = true := by decide +kernel
theorem subd12_0_1253 : subd12_0 [4, -3, -1] = true := by decide +kernel
theorem subd12_0_1254 : subd12_0 [4, -3, 0] = true := by decide +kernel
theorem subd12_0_1255 : subd12_0 [4, -3, 1] = true := by decide +kernel
theorem subd12_0_1256 : subd12_0 [4, -3, 2] = true := by decide +kernel
theorem subd12_0_1257 : subd12_0 [4, -3, 3] = true := by decide +kernel
theorem subd12_0_1258 : subd12_0 [4, -3, 4] = true := by decide +kernel
theorem subd12_0_1259 : subd12_0 [4, -3, 5] = true := by decide +kernel
theorem subd12_0_1260 : subd12_0 [4, -2, -8] = true := by decide +kernel
theorem subd12_0_1261 : subd12_0 [4, -2, -7] = true := by decide +kernel
theorem subd12_0_1262 : subd12_0 [4, -2, -6] = true := by decide +kernel
theorem subd12_0_1263 : subd12_0 [4, -2, -5] = true := by decide +kernel
theorem subd12_0_1264 : subd12_0 [4, -2, -4] = true := by decide +kernel
theorem subd12_0_1265 : subd12_0 [4, -2, -3] = true := by decide +kernel
theorem subd12_0_1266 : subd12_0 [4, -2, -2] = true := by decide +kernel
theorem subd12_0_1267 : subd12_0 [4, -2, -1] = true := by decide +kernel
theorem subd12_0_1268 : subd12_0 [4, -2, 0] = true := by decide +kernel
theorem subd12_0_1269 : subd12_0 [4, -2, 1] = true := by decide +kernel
theorem subd12_0_1270 : subd12_0 [4, -2, 2] = true := by decide +kernel
theorem subd12_0_1271 : subd12_0 [4, -2, 3] = true := by decide +kernel
theorem subd12_0_1272 : subd12_0 [4, -2, 4] = true := by decide +kernel
theorem subd12_0_1273 : subd12_0 [4, -2, 5] = true := by decide +kernel
theorem subd12_0_1274 : subd12_0 [4, -2, 6] = true := by decide +kernel
theorem subd12_0_1275 : subd12_0 [4, -1, -8] = true := by decide +kernel
theorem subd12_0_1276 : subd12_0 [4, -1, -7] = true := by decide +kernel
theorem subd12_0_1277 : subd12_0 [4, -1, -6] = true := by decide +kernel
theorem subd12_0_1278 : subd12_0 [4, -1, -5] = true := by decide +kernel
theorem subd12_0_1279 : subd12_0 [4, -1, -4] = true := by decide +kernel
theorem sbd12_0_39 : ∀ q ∈ blkd12_0_39, subd12_0 q = true := by
  unfold blkd12_0_39
  exact List.forall_mem_cons.2 ⟨subd12_0_1248, List.forall_mem_cons.2 ⟨subd12_0_1249, List.forall_mem_cons.2 ⟨subd12_0_1250, List.forall_mem_cons.2 ⟨subd12_0_1251, List.forall_mem_cons.2 ⟨subd12_0_1252, List.forall_mem_cons.2 ⟨subd12_0_1253, List.forall_mem_cons.2 ⟨subd12_0_1254, List.forall_mem_cons.2 ⟨subd12_0_1255, List.forall_mem_cons.2 ⟨subd12_0_1256, List.forall_mem_cons.2 ⟨subd12_0_1257, List.forall_mem_cons.2 ⟨subd12_0_1258, List.forall_mem_cons.2 ⟨subd12_0_1259, List.forall_mem_cons.2 ⟨subd12_0_1260, List.forall_mem_cons.2 ⟨subd12_0_1261, List.forall_mem_cons.2 ⟨subd12_0_1262, List.forall_mem_cons.2 ⟨subd12_0_1263, List.forall_mem_cons.2 ⟨subd12_0_1264, List.forall_mem_cons.2 ⟨subd12_0_1265, List.forall_mem_cons.2 ⟨subd12_0_1266, List.forall_mem_cons.2 ⟨subd12_0_1267, List.forall_mem_cons.2 ⟨subd12_0_1268, List.forall_mem_cons.2 ⟨subd12_0_1269, List.forall_mem_cons.2 ⟨subd12_0_1270, List.forall_mem_cons.2 ⟨subd12_0_1271, List.forall_mem_cons.2 ⟨subd12_0_1272, List.forall_mem_cons.2 ⟨subd12_0_1273, List.forall_mem_cons.2 ⟨subd12_0_1274, List.forall_mem_cons.2 ⟨subd12_0_1275, List.forall_mem_cons.2 ⟨subd12_0_1276, List.forall_mem_cons.2 ⟨subd12_0_1277, List.forall_mem_cons.2 ⟨subd12_0_1278, List.forall_mem_cons.2 ⟨subd12_0_1279, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_1280 : subd12_0 [4, -1, -3] = true := by decide +kernel
theorem subd12_0_1281 : subd12_0 [4, -1, -2] = true := by decide +kernel
theorem subd12_0_1282 : subd12_0 [4, -1, -1] = true := by decide +kernel
theorem subd12_0_1283 : subd12_0 [4, -1, 0] = true := by decide +kernel
theorem subd12_0_1284 : subd12_0 [4, -1, 1] = true := by decide +kernel
theorem subd12_0_1285 : subd12_0 [4, -1, 2] = true := by decide +kernel
theorem subd12_0_1286 : subd12_0 [4, -1, 3] = true := by decide +kernel
theorem subd12_0_1287 : subd12_0 [4, -1, 4] = true := by decide +kernel
theorem subd12_0_1288 : subd12_0 [4, -1, 5] = true := by decide +kernel
theorem subd12_0_1289 : subd12_0 [4, -1, 6] = true := by decide +kernel
theorem subd12_0_1290 : subd12_0 [4, 0, -7] = true := by decide +kernel
theorem subd12_0_1291 : subd12_0 [4, 0, -6] = true := by decide +kernel
theorem subd12_0_1292 : subd12_0 [4, 0, -5] = true := by decide +kernel
theorem subd12_0_1293 : subd12_0 [4, 0, -4] = true := by decide +kernel
theorem subd12_0_1294 : subd12_0 [4, 0, -3] = true := by decide +kernel
theorem subd12_0_1295 : subd12_0 [4, 0, -2] = true := by decide +kernel
theorem subd12_0_1296 : subd12_0 [4, 0, -1] = true := by decide +kernel
theorem subd12_0_1297 : subd12_0 [4, 0, 0] = true := by decide +kernel
theorem subd12_0_1298 : subd12_0 [4, 0, 1] = true := by decide +kernel
theorem subd12_0_1299 : subd12_0 [4, 0, 2] = true := by decide +kernel
theorem subd12_0_1300 : subd12_0 [4, 0, 3] = true := by decide +kernel
theorem subd12_0_1301 : subd12_0 [4, 0, 4] = true := by decide +kernel
theorem subd12_0_1302 : subd12_0 [4, 0, 5] = true := by decide +kernel
theorem subd12_0_1303 : subd12_0 [4, 0, 6] = true := by decide +kernel
theorem subd12_0_1304 : subd12_0 [4, 0, 7] = true := by decide +kernel
theorem subd12_0_1305 : subd12_0 [4, 1, -7] = true := by decide +kernel
theorem subd12_0_1306 : subd12_0 [4, 1, -6] = true := by decide +kernel
theorem subd12_0_1307 : subd12_0 [4, 1, -5] = true := by decide +kernel
theorem subd12_0_1308 : subd12_0 [4, 1, -4] = true := by decide +kernel
theorem subd12_0_1309 : subd12_0 [4, 1, -3] = true := by decide +kernel
theorem subd12_0_1310 : subd12_0 [4, 1, -2] = true := by decide +kernel
theorem subd12_0_1311 : subd12_0 [4, 1, -1] = true := by decide +kernel
theorem sbd12_0_40 : ∀ q ∈ blkd12_0_40, subd12_0 q = true := by
  unfold blkd12_0_40
  exact List.forall_mem_cons.2 ⟨subd12_0_1280, List.forall_mem_cons.2 ⟨subd12_0_1281, List.forall_mem_cons.2 ⟨subd12_0_1282, List.forall_mem_cons.2 ⟨subd12_0_1283, List.forall_mem_cons.2 ⟨subd12_0_1284, List.forall_mem_cons.2 ⟨subd12_0_1285, List.forall_mem_cons.2 ⟨subd12_0_1286, List.forall_mem_cons.2 ⟨subd12_0_1287, List.forall_mem_cons.2 ⟨subd12_0_1288, List.forall_mem_cons.2 ⟨subd12_0_1289, List.forall_mem_cons.2 ⟨subd12_0_1290, List.forall_mem_cons.2 ⟨subd12_0_1291, List.forall_mem_cons.2 ⟨subd12_0_1292, List.forall_mem_cons.2 ⟨subd12_0_1293, List.forall_mem_cons.2 ⟨subd12_0_1294, List.forall_mem_cons.2 ⟨subd12_0_1295, List.forall_mem_cons.2 ⟨subd12_0_1296, List.forall_mem_cons.2 ⟨subd12_0_1297, List.forall_mem_cons.2 ⟨subd12_0_1298, List.forall_mem_cons.2 ⟨subd12_0_1299, List.forall_mem_cons.2 ⟨subd12_0_1300, List.forall_mem_cons.2 ⟨subd12_0_1301, List.forall_mem_cons.2 ⟨subd12_0_1302, List.forall_mem_cons.2 ⟨subd12_0_1303, List.forall_mem_cons.2 ⟨subd12_0_1304, List.forall_mem_cons.2 ⟨subd12_0_1305, List.forall_mem_cons.2 ⟨subd12_0_1306, List.forall_mem_cons.2 ⟨subd12_0_1307, List.forall_mem_cons.2 ⟨subd12_0_1308, List.forall_mem_cons.2 ⟨subd12_0_1309, List.forall_mem_cons.2 ⟨subd12_0_1310, List.forall_mem_cons.2 ⟨subd12_0_1311, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_1312 : subd12_0 [4, 1, 0] = true := by decide +kernel
theorem subd12_0_1313 : subd12_0 [4, 1, 1] = true := by decide +kernel
theorem subd12_0_1314 : subd12_0 [4, 1, 2] = true := by decide +kernel
theorem subd12_0_1315 : subd12_0 [4, 1, 3] = true := by decide +kernel
theorem subd12_0_1316 : subd12_0 [4, 1, 4] = true := by decide +kernel
theorem subd12_0_1317 : subd12_0 [4, 1, 5] = true := by decide +kernel
theorem subd12_0_1318 : subd12_0 [4, 1, 6] = true := by decide +kernel
theorem subd12_0_1319 : subd12_0 [4, 1, 7] = true := by decide +kernel
theorem subd12_0_1320 : subd12_0 [4, 2, -6] = true := by decide +kernel
theorem subd12_0_1321 : subd12_0 [4, 2, -5] = true := by decide +kernel
theorem subd12_0_1322 : subd12_0 [4, 2, -4] = true := by decide +kernel
theorem subd12_0_1323 : subd12_0 [4, 2, -3] = true := by decide +kernel
theorem subd12_0_1324 : subd12_0 [4, 2, -2] = true := by decide +kernel
theorem subd12_0_1325 : subd12_0 [4, 2, -1] = true := by decide +kernel
theorem subd12_0_1326 : subd12_0 [4, 2, 0] = true := by decide +kernel
theorem subd12_0_1327 : subd12_0 [4, 2, 1] = true := by decide +kernel
theorem subd12_0_1328 : subd12_0 [4, 2, 2] = true := by decide +kernel
theorem subd12_0_1329 : subd12_0 [4, 2, 3] = true := by decide +kernel
theorem subd12_0_1330 : subd12_0 [4, 2, 4] = true := by decide +kernel
theorem subd12_0_1331 : subd12_0 [4, 2, 5] = true := by decide +kernel
theorem subd12_0_1332 : subd12_0 [4, 2, 6] = true := by decide +kernel
theorem subd12_0_1333 : subd12_0 [4, 2, 7] = true := by decide +kernel
theorem subd12_0_1334 : subd12_0 [4, 3] = true := by decide +kernel
theorem subd12_0_1335 : subd12_0 [4, 4] = true := by decide +kernel
theorem subd12_0_1336 : subd12_0 [4, 5] = true := by decide +kernel
theorem subd12_0_1337 : subd12_0 [4, 6] = true := by decide +kernel
theorem subd12_0_1338 : subd12_0 [5, -8] = true := by decide +kernel
theorem subd12_0_1339 : subd12_0 [5, -7] = true := by decide +kernel
theorem subd12_0_1340 : subd12_0 [5, -6] = true := by decide +kernel
theorem subd12_0_1341 : subd12_0 [5, -5] = true := by decide +kernel
theorem subd12_0_1342 : subd12_0 [5, -4] = true := by decide +kernel
theorem subd12_0_1343 : subd12_0 [5, -3] = true := by decide +kernel
theorem sbd12_0_41 : ∀ q ∈ blkd12_0_41, subd12_0 q = true := by
  unfold blkd12_0_41
  exact List.forall_mem_cons.2 ⟨subd12_0_1312, List.forall_mem_cons.2 ⟨subd12_0_1313, List.forall_mem_cons.2 ⟨subd12_0_1314, List.forall_mem_cons.2 ⟨subd12_0_1315, List.forall_mem_cons.2 ⟨subd12_0_1316, List.forall_mem_cons.2 ⟨subd12_0_1317, List.forall_mem_cons.2 ⟨subd12_0_1318, List.forall_mem_cons.2 ⟨subd12_0_1319, List.forall_mem_cons.2 ⟨subd12_0_1320, List.forall_mem_cons.2 ⟨subd12_0_1321, List.forall_mem_cons.2 ⟨subd12_0_1322, List.forall_mem_cons.2 ⟨subd12_0_1323, List.forall_mem_cons.2 ⟨subd12_0_1324, List.forall_mem_cons.2 ⟨subd12_0_1325, List.forall_mem_cons.2 ⟨subd12_0_1326, List.forall_mem_cons.2 ⟨subd12_0_1327, List.forall_mem_cons.2 ⟨subd12_0_1328, List.forall_mem_cons.2 ⟨subd12_0_1329, List.forall_mem_cons.2 ⟨subd12_0_1330, List.forall_mem_cons.2 ⟨subd12_0_1331, List.forall_mem_cons.2 ⟨subd12_0_1332, List.forall_mem_cons.2 ⟨subd12_0_1333, List.forall_mem_cons.2 ⟨subd12_0_1334, List.forall_mem_cons.2 ⟨subd12_0_1335, List.forall_mem_cons.2 ⟨subd12_0_1336, List.forall_mem_cons.2 ⟨subd12_0_1337, List.forall_mem_cons.2 ⟨subd12_0_1338, List.forall_mem_cons.2 ⟨subd12_0_1339, List.forall_mem_cons.2 ⟨subd12_0_1340, List.forall_mem_cons.2 ⟨subd12_0_1341, List.forall_mem_cons.2 ⟨subd12_0_1342, List.forall_mem_cons.2 ⟨subd12_0_1343, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_1344 : subd12_0 [5, -2] = true := by decide +kernel
theorem subd12_0_1345 : subd12_0 [5, -1] = true := by decide +kernel
theorem subd12_0_1346 : subd12_0 [5, 0] = true := by decide +kernel
theorem subd12_0_1347 : subd12_0 [5, 1] = true := by decide +kernel
theorem subd12_0_1348 : subd12_0 [5, 2] = true := by decide +kernel
theorem subd12_0_1349 : subd12_0 [5, 3] = true := by decide +kernel
theorem subd12_0_1350 : subd12_0 [5, 4] = true := by decide +kernel
theorem subd12_0_1351 : subd12_0 [5, 5] = true := by decide +kernel
theorem subd12_0_1352 : subd12_0 [6, -7] = true := by decide +kernel
theorem subd12_0_1353 : subd12_0 [6, -6] = true := by decide +kernel
theorem subd12_0_1354 : subd12_0 [6, -5] = true := by decide +kernel
theorem subd12_0_1355 : subd12_0 [6, -4] = true := by decide +kernel
theorem subd12_0_1356 : subd12_0 [6, -3] = true := by decide +kernel
theorem subd12_0_1357 : subd12_0 [6, -2] = true := by decide +kernel
theorem subd12_0_1358 : subd12_0 [6, -1] = true := by decide +kernel
theorem subd12_0_1359 : subd12_0 [6, 0] = true := by decide +kernel
theorem subd12_0_1360 : subd12_0 [6, 1] = true := by decide +kernel
theorem subd12_0_1361 : subd12_0 [6, 2] = true := by decide +kernel
theorem subd12_0_1362 : subd12_0 [6, 3] = true := by decide +kernel
theorem subd12_0_1363 : subd12_0 [6, 4] = true := by decide +kernel
theorem subd12_0_1364 : subd12_0 [7, -6] = true := by decide +kernel
theorem subd12_0_1365 : subd12_0 [7, -5] = true := by decide +kernel
theorem subd12_0_1366 : subd12_0 [7, -4] = true := by decide +kernel
theorem subd12_0_1367 : subd12_0 [7, -3] = true := by decide +kernel
theorem subd12_0_1368 : subd12_0 [7, -2] = true := by decide +kernel
theorem subd12_0_1369 : subd12_0 [7, -1] = true := by decide +kernel
theorem subd12_0_1370 : subd12_0 [7, 0] = true := by decide +kernel
theorem subd12_0_1371 : subd12_0 [7, 1] = true := by decide +kernel
theorem subd12_0_1372 : subd12_0 [7, 2] = true := by decide +kernel
theorem sbd12_0_42 : ∀ q ∈ blkd12_0_42, subd12_0 q = true := by
  unfold blkd12_0_42
  exact List.forall_mem_cons.2 ⟨subd12_0_1344, List.forall_mem_cons.2 ⟨subd12_0_1345, List.forall_mem_cons.2 ⟨subd12_0_1346, List.forall_mem_cons.2 ⟨subd12_0_1347, List.forall_mem_cons.2 ⟨subd12_0_1348, List.forall_mem_cons.2 ⟨subd12_0_1349, List.forall_mem_cons.2 ⟨subd12_0_1350, List.forall_mem_cons.2 ⟨subd12_0_1351, List.forall_mem_cons.2 ⟨subd12_0_1352, List.forall_mem_cons.2 ⟨subd12_0_1353, List.forall_mem_cons.2 ⟨subd12_0_1354, List.forall_mem_cons.2 ⟨subd12_0_1355, List.forall_mem_cons.2 ⟨subd12_0_1356, List.forall_mem_cons.2 ⟨subd12_0_1357, List.forall_mem_cons.2 ⟨subd12_0_1358, List.forall_mem_cons.2 ⟨subd12_0_1359, List.forall_mem_cons.2 ⟨subd12_0_1360, List.forall_mem_cons.2 ⟨subd12_0_1361, List.forall_mem_cons.2 ⟨subd12_0_1362, List.forall_mem_cons.2 ⟨subd12_0_1363, List.forall_mem_cons.2 ⟨subd12_0_1364, List.forall_mem_cons.2 ⟨subd12_0_1365, List.forall_mem_cons.2 ⟨subd12_0_1366, List.forall_mem_cons.2 ⟨subd12_0_1367, List.forall_mem_cons.2 ⟨subd12_0_1368, List.forall_mem_cons.2 ⟨subd12_0_1369, List.forall_mem_cons.2 ⟨subd12_0_1370, List.forall_mem_cons.2 ⟨subd12_0_1371, List.forall_mem_cons.2 ⟨subd12_0_1372, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd12_1 : ldCheck G d12_1.U d12_1.ms ldd12_1 = true := by decide +kernel
theorem pre_okd12_1 : subPre G cell12 d12_1 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C131
