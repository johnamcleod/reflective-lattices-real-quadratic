import ReflectZphi.Data.Cert5.C101.Base

namespace ReflectZphi.Data.Cert5.C101

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd13_0_224 : subd13_0 [1, 0, -3] = true := by decide +kernel
theorem subd13_0_225 : subd13_0 [1, 0, -2] = true := by decide +kernel
theorem subd13_0_226 : subd13_0 [1, 0, -1] = true := by decide +kernel
theorem subd13_0_227 : subd13_0 [1, 0, 0] = true := by decide +kernel
theorem subd13_0_228 : subd13_0 [1, 0, 1] = true := by decide +kernel
theorem subd13_0_229 : subd13_0 [1, 0, 2] = true := by decide +kernel
theorem subd13_0_230 : subd13_0 [1, 0, 3] = true := by decide +kernel
theorem subd13_0_231 : subd13_0 [1, 0, 4] = true := by decide +kernel
theorem subd13_0_232 : subd13_0 [1, 0, 5] = true := by decide +kernel
theorem subd13_0_233 : subd13_0 [1, 0, 6] = true := by decide +kernel
theorem subd13_0_234 : subd13_0 [1, 0, 7] = true := by decide +kernel
theorem subd13_0_235 : subd13_0 [1, 1, -7] = true := by decide +kernel
theorem subd13_0_236 : subd13_0 [1, 1, -6] = true := by decide +kernel
theorem subd13_0_237 : subd13_0 [1, 1, -5] = true := by decide +kernel
theorem subd13_0_238 : subd13_0 [1, 1, -4] = true := by decide +kernel
theorem subd13_0_239 : subd13_0 [1, 1, -3] = true := by decide +kernel
theorem subd13_0_240 : subd13_0 [1, 1, -2] = true := by decide +kernel
theorem subd13_0_241 : subd13_0 [1, 1, -1] = true := by decide +kernel
theorem subd13_0_242 : subd13_0 [1, 1, 0] = true := by decide +kernel
theorem subd13_0_243 : subd13_0 [1, 1, 1] = true := by decide +kernel
theorem subd13_0_244 : subd13_0 [1, 1, 2] = true := by decide +kernel
theorem subd13_0_245 : subd13_0 [1, 1, 3] = true := by decide +kernel
theorem subd13_0_246 : subd13_0 [1, 1, 4] = true := by decide +kernel
theorem subd13_0_247 : subd13_0 [1, 1, 5] = true := by decide +kernel
theorem subd13_0_248 : subd13_0 [1, 1, 6] = true := by decide +kernel
theorem subd13_0_249 : subd13_0 [1, 2] = true := by decide +kernel
theorem subd13_0_250 : subd13_0 [1, 3] = true := by decide +kernel
theorem subd13_0_251 : subd13_0 [1, 4] = true := by decide +kernel
theorem subd13_0_252 : subd13_0 [2, -5] = true := by decide +kernel
theorem subd13_0_253 : subd13_0 [2, -4] = true := by decide +kernel
theorem subd13_0_254 : subd13_0 [2, -3] = true := by decide +kernel
theorem subd13_0_255 : subd13_0 [2, -2] = true := by decide +kernel
theorem sbd13_0_7 : ∀ q ∈ blkd13_0_7, subd13_0 q = true := by
  unfold blkd13_0_7
  exact List.forall_mem_cons.2 ⟨subd13_0_224, List.forall_mem_cons.2 ⟨subd13_0_225, List.forall_mem_cons.2 ⟨subd13_0_226, List.forall_mem_cons.2 ⟨subd13_0_227, List.forall_mem_cons.2 ⟨subd13_0_228, List.forall_mem_cons.2 ⟨subd13_0_229, List.forall_mem_cons.2 ⟨subd13_0_230, List.forall_mem_cons.2 ⟨subd13_0_231, List.forall_mem_cons.2 ⟨subd13_0_232, List.forall_mem_cons.2 ⟨subd13_0_233, List.forall_mem_cons.2 ⟨subd13_0_234, List.forall_mem_cons.2 ⟨subd13_0_235, List.forall_mem_cons.2 ⟨subd13_0_236, List.forall_mem_cons.2 ⟨subd13_0_237, List.forall_mem_cons.2 ⟨subd13_0_238, List.forall_mem_cons.2 ⟨subd13_0_239, List.forall_mem_cons.2 ⟨subd13_0_240, List.forall_mem_cons.2 ⟨subd13_0_241, List.forall_mem_cons.2 ⟨subd13_0_242, List.forall_mem_cons.2 ⟨subd13_0_243, List.forall_mem_cons.2 ⟨subd13_0_244, List.forall_mem_cons.2 ⟨subd13_0_245, List.forall_mem_cons.2 ⟨subd13_0_246, List.forall_mem_cons.2 ⟨subd13_0_247, List.forall_mem_cons.2 ⟨subd13_0_248, List.forall_mem_cons.2 ⟨subd13_0_249, List.forall_mem_cons.2 ⟨subd13_0_250, List.forall_mem_cons.2 ⟨subd13_0_251, List.forall_mem_cons.2 ⟨subd13_0_252, List.forall_mem_cons.2 ⟨subd13_0_253, List.forall_mem_cons.2 ⟨subd13_0_254, List.forall_mem_cons.2 ⟨subd13_0_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_0_256 : subd13_0 [2, -1, -6] = true := by decide +kernel
theorem subd13_0_257 : subd13_0 [2, -1, -5] = true := by decide +kernel
theorem subd13_0_258 : subd13_0 [2, -1, -4] = true := by decide +kernel
theorem subd13_0_259 : subd13_0 [2, -1, -3] = true := by decide +kernel
theorem subd13_0_260 : subd13_0 [2, -1, -2] = true := by decide +kernel
theorem subd13_0_261 : subd13_0 [2, -1, -1] = true := by decide +kernel
theorem subd13_0_262 : subd13_0 [2, -1, 0] = true := by decide +kernel
theorem subd13_0_263 : subd13_0 [2, -1, 1] = true := by decide +kernel
theorem subd13_0_264 : subd13_0 [2, -1, 2] = true := by decide +kernel
theorem subd13_0_265 : subd13_0 [2, -1, 3] = true := by decide +kernel
theorem subd13_0_266 : subd13_0 [2, -1, 4] = true := by decide +kernel
theorem subd13_0_267 : subd13_0 [2, -1, 5] = true := by decide +kernel
theorem subd13_0_268 : subd13_0 [2, -1, 6] = true := by decide +kernel
theorem subd13_0_269 : subd13_0 [2, -1, 7] = true := by decide +kernel
theorem subd13_0_270 : subd13_0 [2, 0, -6] = true := by decide +kernel
theorem subd13_0_271 : subd13_0 [2, 0, -5] = true := by decide +kernel
theorem subd13_0_272 : subd13_0 [2, 0, -4] = true := by decide +kernel
theorem subd13_0_273 : subd13_0 [2, 0, -3] = true := by decide +kernel
theorem subd13_0_274 : subd13_0 [2, 0, -2] = true := by decide +kernel
theorem subd13_0_275 : subd13_0 [2, 0, -1] = true := by decide +kernel
theorem subd13_0_276 : subd13_0 [2, 0, 0] = true := by decide +kernel
theorem subd13_0_277 : subd13_0 [2, 0, 1] = true := by decide +kernel
theorem subd13_0_278 : subd13_0 [2, 0, 2] = true := by decide +kernel
theorem subd13_0_279 : subd13_0 [2, 0, 3] = true := by decide +kernel
theorem subd13_0_280 : subd13_0 [2, 0, 4] = true := by decide +kernel
theorem subd13_0_281 : subd13_0 [2, 0, 5] = true := by decide +kernel
theorem subd13_0_282 : subd13_0 [2, 0, 6] = true := by decide +kernel
theorem subd13_0_283 : subd13_0 [2, 0, 7] = true := by decide +kernel
theorem subd13_0_284 : subd13_0 [2, 1] = true := by decide +kernel
theorem subd13_0_285 : subd13_0 [2, 2] = true := by decide +kernel
theorem subd13_0_286 : subd13_0 [2, 3] = true := by decide +kernel
theorem subd13_0_287 : subd13_0 [2, 4] = true := by decide +kernel
theorem sbd13_0_8 : ∀ q ∈ blkd13_0_8, subd13_0 q = true := by
  unfold blkd13_0_8
  exact List.forall_mem_cons.2 ⟨subd13_0_256, List.forall_mem_cons.2 ⟨subd13_0_257, List.forall_mem_cons.2 ⟨subd13_0_258, List.forall_mem_cons.2 ⟨subd13_0_259, List.forall_mem_cons.2 ⟨subd13_0_260, List.forall_mem_cons.2 ⟨subd13_0_261, List.forall_mem_cons.2 ⟨subd13_0_262, List.forall_mem_cons.2 ⟨subd13_0_263, List.forall_mem_cons.2 ⟨subd13_0_264, List.forall_mem_cons.2 ⟨subd13_0_265, List.forall_mem_cons.2 ⟨subd13_0_266, List.forall_mem_cons.2 ⟨subd13_0_267, List.forall_mem_cons.2 ⟨subd13_0_268, List.forall_mem_cons.2 ⟨subd13_0_269, List.forall_mem_cons.2 ⟨subd13_0_270, List.forall_mem_cons.2 ⟨subd13_0_271, List.forall_mem_cons.2 ⟨subd13_0_272, List.forall_mem_cons.2 ⟨subd13_0_273, List.forall_mem_cons.2 ⟨subd13_0_274, List.forall_mem_cons.2 ⟨subd13_0_275, List.forall_mem_cons.2 ⟨subd13_0_276, List.forall_mem_cons.2 ⟨subd13_0_277, List.forall_mem_cons.2 ⟨subd13_0_278, List.forall_mem_cons.2 ⟨subd13_0_279, List.forall_mem_cons.2 ⟨subd13_0_280, List.forall_mem_cons.2 ⟨subd13_0_281, List.forall_mem_cons.2 ⟨subd13_0_282, List.forall_mem_cons.2 ⟨subd13_0_283, List.forall_mem_cons.2 ⟨subd13_0_284, List.forall_mem_cons.2 ⟨subd13_0_285, List.forall_mem_cons.2 ⟨subd13_0_286, List.forall_mem_cons.2 ⟨subd13_0_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_0_288 : subd13_0 [3, -5] = true := by decide +kernel
theorem subd13_0_289 : subd13_0 [3, -4] = true := by decide +kernel
theorem subd13_0_290 : subd13_0 [3, -3] = true := by decide +kernel
theorem subd13_0_291 : subd13_0 [3, -2] = true := by decide +kernel
theorem subd13_0_292 : subd13_0 [3, -1] = true := by decide +kernel
theorem subd13_0_293 : subd13_0 [3, 0] = true := by decide +kernel
theorem subd13_0_294 : subd13_0 [3, 1] = true := by decide +kernel
theorem subd13_0_295 : subd13_0 [3, 2] = true := by decide +kernel
theorem subd13_0_296 : subd13_0 [3, 3] = true := by decide +kernel
theorem subd13_0_297 : subd13_0 [4, -3] = true := by decide +kernel
theorem subd13_0_298 : subd13_0 [4, -2] = true := by decide +kernel
theorem subd13_0_299 : subd13_0 [4, -1] = true := by decide +kernel
theorem subd13_0_300 : subd13_0 [4, 0] = true := by decide +kernel
theorem subd13_0_301 : subd13_0 [4, 1] = true := by decide +kernel
theorem subd13_0_302 : subd13_0 [4, 2] = true := by decide +kernel
theorem sbd13_0_9 : ∀ q ∈ blkd13_0_9, subd13_0 q = true := by
  unfold blkd13_0_9
  exact List.forall_mem_cons.2 ⟨subd13_0_288, List.forall_mem_cons.2 ⟨subd13_0_289, List.forall_mem_cons.2 ⟨subd13_0_290, List.forall_mem_cons.2 ⟨subd13_0_291, List.forall_mem_cons.2 ⟨subd13_0_292, List.forall_mem_cons.2 ⟨subd13_0_293, List.forall_mem_cons.2 ⟨subd13_0_294, List.forall_mem_cons.2 ⟨subd13_0_295, List.forall_mem_cons.2 ⟨subd13_0_296, List.forall_mem_cons.2 ⟨subd13_0_297, List.forall_mem_cons.2 ⟨subd13_0_298, List.forall_mem_cons.2 ⟨subd13_0_299, List.forall_mem_cons.2 ⟨subd13_0_300, List.forall_mem_cons.2 ⟨subd13_0_301, List.forall_mem_cons.2 ⟨subd13_0_302, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd13_1 : ldCheck G d13_1.U d13_1.ms ldd13_1 = true := by decide +kernel
theorem pre_okd13_1 : subPre G cell13 d13_1 = true := by decide +kernel
theorem subd13_1_0 : subd13_1 [-1, -2] = true := by decide +kernel
theorem subd13_1_1 : subd13_1 [-1, -1, -15] = true := by decide +kernel
theorem subd13_1_2 : subd13_1 [-1, -1, -14] = true := by decide +kernel
theorem subd13_1_3 : subd13_1 [-1, -1, -13] = true := by decide +kernel
theorem subd13_1_4 : subd13_1 [-1, -1, -12] = true := by decide +kernel
theorem subd13_1_5 : subd13_1 [-1, -1, -11] = true := by decide +kernel
theorem subd13_1_6 : subd13_1 [-1, -1, -10] = true := by decide +kernel
theorem subd13_1_7 : subd13_1 [-1, -1, -9] = true := by decide +kernel
theorem subd13_1_8 : subd13_1 [-1, -1, -8] = true := by decide +kernel
theorem subd13_1_9 : subd13_1 [-1, -1, -7] = true := by decide +kernel
theorem subd13_1_10 : subd13_1 [-1, -1, -6] = true := by decide +kernel
theorem subd13_1_11 : subd13_1 [-1, -1, -5] = true := by decide +kernel
theorem subd13_1_12 : subd13_1 [-1, -1, -4] = true := by decide +kernel
theorem subd13_1_13 : subd13_1 [-1, -1, -3] = true := by decide +kernel
theorem subd13_1_14 : subd13_1 [-1, -1, -2] = true := by decide +kernel
theorem subd13_1_15 : subd13_1 [-1, -1, -1] = true := by decide +kernel
theorem subd13_1_16 : subd13_1 [-1, -1, 0] = true := by decide +kernel
theorem subd13_1_17 : subd13_1 [-1, -1, 1] = true := by decide +kernel
theorem subd13_1_18 : subd13_1 [-1, -1, 2] = true := by decide +kernel
theorem subd13_1_19 : subd13_1 [-1, -1, 3] = true := by decide +kernel
theorem subd13_1_20 : subd13_1 [-1, -1, 4] = true := by decide +kernel
theorem subd13_1_21 : subd13_1 [-1, -1, 5] = true := by decide +kernel
theorem subd13_1_22 : subd13_1 [-1, -1, 6] = true := by decide +kernel
theorem subd13_1_23 : subd13_1 [-1, -1, 7] = true := by decide +kernel
theorem subd13_1_24 : subd13_1 [-1, -1, 8] = true := by decide +kernel
theorem subd13_1_25 : subd13_1 [-1, -1, 9] = true := by decide +kernel
theorem subd13_1_26 : subd13_1 [-1, -1, 10] = true := by decide +kernel
theorem subd13_1_27 : subd13_1 [-1, -1, 11] = true := by decide +kernel
theorem subd13_1_28 : subd13_1 [-1, -1, 12] = true := by decide +kernel
theorem subd13_1_29 : subd13_1 [-1, -1, 13] = true := by decide +kernel
theorem subd13_1_30 : subd13_1 [-1, 0, -20] = true := by decide +kernel
theorem subd13_1_31 : subd13_1 [-1, 0, -19] = true := by decide +kernel
theorem sbd13_1_0 : ∀ q ∈ blkd13_1_0, subd13_1 q = true := by
  unfold blkd13_1_0
  exact List.forall_mem_cons.2 ⟨subd13_1_0, List.forall_mem_cons.2 ⟨subd13_1_1, List.forall_mem_cons.2 ⟨subd13_1_2, List.forall_mem_cons.2 ⟨subd13_1_3, List.forall_mem_cons.2 ⟨subd13_1_4, List.forall_mem_cons.2 ⟨subd13_1_5, List.forall_mem_cons.2 ⟨subd13_1_6, List.forall_mem_cons.2 ⟨subd13_1_7, List.forall_mem_cons.2 ⟨subd13_1_8, List.forall_mem_cons.2 ⟨subd13_1_9, List.forall_mem_cons.2 ⟨subd13_1_10, List.forall_mem_cons.2 ⟨subd13_1_11, List.forall_mem_cons.2 ⟨subd13_1_12, List.forall_mem_cons.2 ⟨subd13_1_13, List.forall_mem_cons.2 ⟨subd13_1_14, List.forall_mem_cons.2 ⟨subd13_1_15, List.forall_mem_cons.2 ⟨subd13_1_16, List.forall_mem_cons.2 ⟨subd13_1_17, List.forall_mem_cons.2 ⟨subd13_1_18, List.forall_mem_cons.2 ⟨subd13_1_19, List.forall_mem_cons.2 ⟨subd13_1_20, List.forall_mem_cons.2 ⟨subd13_1_21, List.forall_mem_cons.2 ⟨subd13_1_22, List.forall_mem_cons.2 ⟨subd13_1_23, List.forall_mem_cons.2 ⟨subd13_1_24, List.forall_mem_cons.2 ⟨subd13_1_25, List.forall_mem_cons.2 ⟨subd13_1_26, List.forall_mem_cons.2 ⟨subd13_1_27, List.forall_mem_cons.2 ⟨subd13_1_28, List.forall_mem_cons.2 ⟨subd13_1_29, List.forall_mem_cons.2 ⟨subd13_1_30, List.forall_mem_cons.2 ⟨subd13_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_1_32 : subd13_1 [-1, 0, -18] = true := by decide +kernel
theorem subd13_1_33 : subd13_1 [-1, 0, -17] = true := by decide +kernel
theorem subd13_1_34 : subd13_1 [-1, 0, -16] = true := by decide +kernel
theorem subd13_1_35 : subd13_1 [-1, 0, -15] = true := by decide +kernel
theorem subd13_1_36 : subd13_1 [-1, 0, -14] = true := by decide +kernel
theorem subd13_1_37 : subd13_1 [-1, 0, -13] = true := by decide +kernel
theorem subd13_1_38 : subd13_1 [-1, 0, -12] = true := by decide +kernel
theorem subd13_1_39 : subd13_1 [-1, 0, -11] = true := by decide +kernel
theorem subd13_1_40 : subd13_1 [-1, 0, -10] = true := by decide +kernel
theorem subd13_1_41 : subd13_1 [-1, 0, -9] = true := by decide +kernel
theorem subd13_1_42 : subd13_1 [-1, 0, -8] = true := by decide +kernel
theorem subd13_1_43 : subd13_1 [-1, 0, -7] = true := by decide +kernel
theorem subd13_1_44 : subd13_1 [-1, 0, -6] = true := by decide +kernel
theorem subd13_1_45 : subd13_1 [-1, 0, -5] = true := by decide +kernel
theorem subd13_1_46 : subd13_1 [-1, 0, -4] = true := by decide +kernel
theorem subd13_1_47 : subd13_1 [-1, 0, -3] = true := by decide +kernel
theorem subd13_1_48 : subd13_1 [-1, 0, -2] = true := by decide +kernel
theorem subd13_1_49 : subd13_1 [-1, 0, -1] = true := by decide +kernel
theorem subd13_1_50 : subd13_1 [-1, 0, 0] = true := by decide +kernel
theorem subd13_1_51 : subd13_1 [-1, 0, 1] = true := by decide +kernel
theorem subd13_1_52 : subd13_1 [-1, 0, 2] = true := by decide +kernel
theorem subd13_1_53 : subd13_1 [-1, 0, 3] = true := by decide +kernel
theorem subd13_1_54 : subd13_1 [-1, 0, 4] = true := by decide +kernel
theorem subd13_1_55 : subd13_1 [-1, 0, 5] = true := by decide +kernel
theorem subd13_1_56 : subd13_1 [-1, 0, 6] = true := by decide +kernel
theorem subd13_1_57 : subd13_1 [-1, 0, 7] = true := by decide +kernel
theorem subd13_1_58 : subd13_1 [-1, 0, 8] = true := by decide +kernel
theorem subd13_1_59 : subd13_1 [-1, 0, 9] = true := by decide +kernel
theorem subd13_1_60 : subd13_1 [-1, 0, 10] = true := by decide +kernel
theorem subd13_1_61 : subd13_1 [-1, 0, 11] = true := by decide +kernel
theorem subd13_1_62 : subd13_1 [-1, 0, 12] = true := by decide +kernel
theorem subd13_1_63 : subd13_1 [-1, 0, 13] = true := by decide +kernel
theorem sbd13_1_1 : ∀ q ∈ blkd13_1_1, subd13_1 q = true := by
  unfold blkd13_1_1
  exact List.forall_mem_cons.2 ⟨subd13_1_32, List.forall_mem_cons.2 ⟨subd13_1_33, List.forall_mem_cons.2 ⟨subd13_1_34, List.forall_mem_cons.2 ⟨subd13_1_35, List.forall_mem_cons.2 ⟨subd13_1_36, List.forall_mem_cons.2 ⟨subd13_1_37, List.forall_mem_cons.2 ⟨subd13_1_38, List.forall_mem_cons.2 ⟨subd13_1_39, List.forall_mem_cons.2 ⟨subd13_1_40, List.forall_mem_cons.2 ⟨subd13_1_41, List.forall_mem_cons.2 ⟨subd13_1_42, List.forall_mem_cons.2 ⟨subd13_1_43, List.forall_mem_cons.2 ⟨subd13_1_44, List.forall_mem_cons.2 ⟨subd13_1_45, List.forall_mem_cons.2 ⟨subd13_1_46, List.forall_mem_cons.2 ⟨subd13_1_47, List.forall_mem_cons.2 ⟨subd13_1_48, List.forall_mem_cons.2 ⟨subd13_1_49, List.forall_mem_cons.2 ⟨subd13_1_50, List.forall_mem_cons.2 ⟨subd13_1_51, List.forall_mem_cons.2 ⟨subd13_1_52, List.forall_mem_cons.2 ⟨subd13_1_53, List.forall_mem_cons.2 ⟨subd13_1_54, List.forall_mem_cons.2 ⟨subd13_1_55, List.forall_mem_cons.2 ⟨subd13_1_56, List.forall_mem_cons.2 ⟨subd13_1_57, List.forall_mem_cons.2 ⟨subd13_1_58, List.forall_mem_cons.2 ⟨subd13_1_59, List.forall_mem_cons.2 ⟨subd13_1_60, List.forall_mem_cons.2 ⟨subd13_1_61, List.forall_mem_cons.2 ⟨subd13_1_62, List.forall_mem_cons.2 ⟨subd13_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_1_64 : subd13_1 [-1, 0, 14] = true := by decide +kernel
theorem subd13_1_65 : subd13_1 [-1, 0, 15] = true := by decide +kernel
theorem subd13_1_66 : subd13_1 [-1, 0, 16] = true := by decide +kernel
theorem subd13_1_67 : subd13_1 [-1, 0, 17] = true := by decide +kernel
theorem subd13_1_68 : subd13_1 [-1, 0, 18] = true := by decide +kernel
theorem subd13_1_69 : subd13_1 [-1, 1, -14] = true := by decide +kernel
theorem subd13_1_70 : subd13_1 [-1, 1, -13] = true := by decide +kernel
theorem subd13_1_71 : subd13_1 [-1, 1, -12] = true := by decide +kernel
theorem subd13_1_72 : subd13_1 [-1, 1, -11] = true := by decide +kernel
theorem subd13_1_73 : subd13_1 [-1, 1, -10] = true := by decide +kernel
theorem subd13_1_74 : subd13_1 [-1, 1, -9] = true := by decide +kernel
theorem subd13_1_75 : subd13_1 [-1, 1, -8] = true := by decide +kernel
theorem subd13_1_76 : subd13_1 [-1, 1, -7] = true := by decide +kernel
theorem subd13_1_77 : subd13_1 [-1, 1, -6] = true := by decide +kernel
theorem subd13_1_78 : subd13_1 [-1, 1, -5] = true := by decide +kernel
theorem subd13_1_79 : subd13_1 [-1, 1, -4] = true := by decide +kernel
theorem subd13_1_80 : subd13_1 [-1, 1, -3] = true := by decide +kernel
theorem subd13_1_81 : subd13_1 [-1, 1, -2] = true := by decide +kernel
theorem subd13_1_82 : subd13_1 [-1, 1, -1] = true := by decide +kernel
theorem subd13_1_83 : subd13_1 [-1, 1, 0] = true := by decide +kernel
theorem subd13_1_84 : subd13_1 [-1, 1, 1] = true := by decide +kernel
theorem subd13_1_85 : subd13_1 [-1, 1, 2] = true := by decide +kernel
theorem subd13_1_86 : subd13_1 [-1, 1, 3] = true := by decide +kernel
theorem subd13_1_87 : subd13_1 [-1, 1, 4] = true := by decide +kernel
theorem subd13_1_88 : subd13_1 [-1, 1, 5] = true := by decide +kernel
theorem subd13_1_89 : subd13_1 [-1, 1, 6] = true := by decide +kernel
theorem subd13_1_90 : subd13_1 [-1, 1, 7] = true := by decide +kernel
theorem subd13_1_91 : subd13_1 [-1, 1, 8] = true := by decide +kernel
theorem subd13_1_92 : subd13_1 [-1, 1, 9] = true := by decide +kernel
theorem subd13_1_93 : subd13_1 [-1, 1, 10] = true := by decide +kernel
theorem subd13_1_94 : subd13_1 [-1, 1, 11] = true := by decide +kernel
theorem subd13_1_95 : subd13_1 [-1, 1, 12] = true := by decide +kernel
theorem sbd13_1_2 : ∀ q ∈ blkd13_1_2, subd13_1 q = true := by
  unfold blkd13_1_2
  exact List.forall_mem_cons.2 ⟨subd13_1_64, List.forall_mem_cons.2 ⟨subd13_1_65, List.forall_mem_cons.2 ⟨subd13_1_66, List.forall_mem_cons.2 ⟨subd13_1_67, List.forall_mem_cons.2 ⟨subd13_1_68, List.forall_mem_cons.2 ⟨subd13_1_69, List.forall_mem_cons.2 ⟨subd13_1_70, List.forall_mem_cons.2 ⟨subd13_1_71, List.forall_mem_cons.2 ⟨subd13_1_72, List.forall_mem_cons.2 ⟨subd13_1_73, List.forall_mem_cons.2 ⟨subd13_1_74, List.forall_mem_cons.2 ⟨subd13_1_75, List.forall_mem_cons.2 ⟨subd13_1_76, List.forall_mem_cons.2 ⟨subd13_1_77, List.forall_mem_cons.2 ⟨subd13_1_78, List.forall_mem_cons.2 ⟨subd13_1_79, List.forall_mem_cons.2 ⟨subd13_1_80, List.forall_mem_cons.2 ⟨subd13_1_81, List.forall_mem_cons.2 ⟨subd13_1_82, List.forall_mem_cons.2 ⟨subd13_1_83, List.forall_mem_cons.2 ⟨subd13_1_84, List.forall_mem_cons.2 ⟨subd13_1_85, List.forall_mem_cons.2 ⟨subd13_1_86, List.forall_mem_cons.2 ⟨subd13_1_87, List.forall_mem_cons.2 ⟨subd13_1_88, List.forall_mem_cons.2 ⟨subd13_1_89, List.forall_mem_cons.2 ⟨subd13_1_90, List.forall_mem_cons.2 ⟨subd13_1_91, List.forall_mem_cons.2 ⟨subd13_1_92, List.forall_mem_cons.2 ⟨subd13_1_93, List.forall_mem_cons.2 ⟨subd13_1_94, List.forall_mem_cons.2 ⟨subd13_1_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_1_96 : subd13_1 [0, -2] = true := by decide +kernel
theorem subd13_1_97 : subd13_1 [0, -1, -20] = true := by decide +kernel
theorem subd13_1_98 : subd13_1 [0, -1, -19] = true := by decide +kernel
theorem subd13_1_99 : subd13_1 [0, -1, -18] = true := by decide +kernel
theorem subd13_1_100 : subd13_1 [0, -1, -17] = true := by decide +kernel
theorem subd13_1_101 : subd13_1 [0, -1, -16] = true := by decide +kernel
theorem subd13_1_102 : subd13_1 [0, -1, -15] = true := by decide +kernel
theorem subd13_1_103 : subd13_1 [0, -1, -14] = true := by decide +kernel
theorem subd13_1_104 : subd13_1 [0, -1, -13] = true := by decide +kernel
theorem subd13_1_105 : subd13_1 [0, -1, -12] = true := by decide +kernel
theorem subd13_1_106 : subd13_1 [0, -1, -11] = true := by decide +kernel
theorem subd13_1_107 : subd13_1 [0, -1, -10] = true := by decide +kernel
theorem subd13_1_108 : subd13_1 [0, -1, -9] = true := by decide +kernel
theorem subd13_1_109 : subd13_1 [0, -1, -8] = true := by decide +kernel
theorem subd13_1_110 : subd13_1 [0, -1, -7] = true := by decide +kernel
theorem subd13_1_111 : subd13_1 [0, -1, -6] = true := by decide +kernel
theorem subd13_1_112 : subd13_1 [0, -1, -5] = true := by decide +kernel
theorem subd13_1_113 : subd13_1 [0, -1, -4] = true := by decide +kernel
theorem subd13_1_114 : subd13_1 [0, -1, -3] = true := by decide +kernel
theorem subd13_1_115 : subd13_1 [0, -1, -2] = true := by decide +kernel
theorem subd13_1_116 : subd13_1 [0, -1, -1] = true := by decide +kernel
theorem subd13_1_117 : subd13_1 [0, -1, 0] = true := by decide +kernel
theorem subd13_1_118 : subd13_1 [0, -1, 1] = true := by decide +kernel
theorem subd13_1_119 : subd13_1 [0, -1, 2] = true := by decide +kernel
theorem subd13_1_120 : subd13_1 [0, -1, 3] = true := by decide +kernel
theorem subd13_1_121 : subd13_1 [0, -1, 4] = true := by decide +kernel
theorem subd13_1_122 : subd13_1 [0, -1, 5] = true := by decide +kernel
theorem subd13_1_123 : subd13_1 [0, -1, 6] = true := by decide +kernel
theorem subd13_1_124 : subd13_1 [0, -1, 7] = true := by decide +kernel
theorem subd13_1_125 : subd13_1 [0, -1, 8] = true := by decide +kernel
theorem subd13_1_126 : subd13_1 [0, -1, 9] = true := by decide +kernel
theorem subd13_1_127 : subd13_1 [0, -1, 10] = true := by decide +kernel
theorem sbd13_1_3 : ∀ q ∈ blkd13_1_3, subd13_1 q = true := by
  unfold blkd13_1_3
  exact List.forall_mem_cons.2 ⟨subd13_1_96, List.forall_mem_cons.2 ⟨subd13_1_97, List.forall_mem_cons.2 ⟨subd13_1_98, List.forall_mem_cons.2 ⟨subd13_1_99, List.forall_mem_cons.2 ⟨subd13_1_100, List.forall_mem_cons.2 ⟨subd13_1_101, List.forall_mem_cons.2 ⟨subd13_1_102, List.forall_mem_cons.2 ⟨subd13_1_103, List.forall_mem_cons.2 ⟨subd13_1_104, List.forall_mem_cons.2 ⟨subd13_1_105, List.forall_mem_cons.2 ⟨subd13_1_106, List.forall_mem_cons.2 ⟨subd13_1_107, List.forall_mem_cons.2 ⟨subd13_1_108, List.forall_mem_cons.2 ⟨subd13_1_109, List.forall_mem_cons.2 ⟨subd13_1_110, List.forall_mem_cons.2 ⟨subd13_1_111, List.forall_mem_cons.2 ⟨subd13_1_112, List.forall_mem_cons.2 ⟨subd13_1_113, List.forall_mem_cons.2 ⟨subd13_1_114, List.forall_mem_cons.2 ⟨subd13_1_115, List.forall_mem_cons.2 ⟨subd13_1_116, List.forall_mem_cons.2 ⟨subd13_1_117, List.forall_mem_cons.2 ⟨subd13_1_118, List.forall_mem_cons.2 ⟨subd13_1_119, List.forall_mem_cons.2 ⟨subd13_1_120, List.forall_mem_cons.2 ⟨subd13_1_121, List.forall_mem_cons.2 ⟨subd13_1_122, List.forall_mem_cons.2 ⟨subd13_1_123, List.forall_mem_cons.2 ⟨subd13_1_124, List.forall_mem_cons.2 ⟨subd13_1_125, List.forall_mem_cons.2 ⟨subd13_1_126, List.forall_mem_cons.2 ⟨subd13_1_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_1_128 : subd13_1 [0, -1, 11] = true := by decide +kernel
theorem subd13_1_129 : subd13_1 [0, -1, 12] = true := by decide +kernel
theorem subd13_1_130 : subd13_1 [0, -1, 13] = true := by decide +kernel
theorem subd13_1_131 : subd13_1 [0, -1, 14] = true := by decide +kernel
theorem subd13_1_132 : subd13_1 [0, -1, 15] = true := by decide +kernel
theorem subd13_1_133 : subd13_1 [0, -1, 16] = true := by decide +kernel
theorem subd13_1_134 : subd13_1 [0, -1, 17] = true := by decide +kernel
theorem subd13_1_135 : subd13_1 [0, -1, 18] = true := by decide +kernel
theorem subd13_1_136 : subd13_1 [0, 0, -24] = true := by decide +kernel
theorem subd13_1_137 : subd13_1 [0, 0, -23] = true := by decide +kernel
theorem subd13_1_138 : subd13_1 [0, 0, -22] = true := by decide +kernel
theorem subd13_1_139 : subd13_1 [0, 0, -21] = true := by decide +kernel
theorem subd13_1_140 : subd13_1 [0, 0, -20] = true := by decide +kernel
theorem subd13_1_141 : subd13_1 [0, 0, -19] = true := by decide +kernel
theorem subd13_1_142 : subd13_1 [0, 0, -18] = true := by decide +kernel
theorem subd13_1_143 : subd13_1 [0, 0, -17] = true := by decide +kernel
theorem subd13_1_144 : subd13_1 [0, 0, -16] = true := by decide +kernel
theorem subd13_1_145 : subd13_1 [0, 0, -15] = true := by decide +kernel
theorem subd13_1_146 : subd13_1 [0, 0, -14] = true := by decide +kernel
theorem subd13_1_147 : subd13_1 [0, 0, -13] = true := by decide +kernel
theorem subd13_1_148 : subd13_1 [0, 0, -12] = true := by decide +kernel
theorem subd13_1_149 : subd13_1 [0, 0, -11] = true := by decide +kernel
theorem subd13_1_150 : subd13_1 [0, 0, -10] = true := by decide +kernel
theorem subd13_1_151 : subd13_1 [0, 0, -9] = true := by decide +kernel
theorem subd13_1_152 : subd13_1 [0, 0, -8] = true := by decide +kernel
theorem subd13_1_153 : subd13_1 [0, 0, -7] = true := by decide +kernel
theorem subd13_1_154 : subd13_1 [0, 0, -6] = true := by decide +kernel
theorem subd13_1_155 : subd13_1 [0, 0, -5] = true := by decide +kernel
theorem subd13_1_156 : subd13_1 [0, 0, -4] = true := by decide +kernel
theorem subd13_1_157 : subd13_1 [0, 0, -3] = true := by decide +kernel
theorem subd13_1_158 : subd13_1 [0, 0, -2] = true := by decide +kernel
theorem subd13_1_159 : subd13_1 [0, 0, -1] = true := by decide +kernel
theorem sbd13_1_4 : ∀ q ∈ blkd13_1_4, subd13_1 q = true := by
  unfold blkd13_1_4
  exact List.forall_mem_cons.2 ⟨subd13_1_128, List.forall_mem_cons.2 ⟨subd13_1_129, List.forall_mem_cons.2 ⟨subd13_1_130, List.forall_mem_cons.2 ⟨subd13_1_131, List.forall_mem_cons.2 ⟨subd13_1_132, List.forall_mem_cons.2 ⟨subd13_1_133, List.forall_mem_cons.2 ⟨subd13_1_134, List.forall_mem_cons.2 ⟨subd13_1_135, List.forall_mem_cons.2 ⟨subd13_1_136, List.forall_mem_cons.2 ⟨subd13_1_137, List.forall_mem_cons.2 ⟨subd13_1_138, List.forall_mem_cons.2 ⟨subd13_1_139, List.forall_mem_cons.2 ⟨subd13_1_140, List.forall_mem_cons.2 ⟨subd13_1_141, List.forall_mem_cons.2 ⟨subd13_1_142, List.forall_mem_cons.2 ⟨subd13_1_143, List.forall_mem_cons.2 ⟨subd13_1_144, List.forall_mem_cons.2 ⟨subd13_1_145, List.forall_mem_cons.2 ⟨subd13_1_146, List.forall_mem_cons.2 ⟨subd13_1_147, List.forall_mem_cons.2 ⟨subd13_1_148, List.forall_mem_cons.2 ⟨subd13_1_149, List.forall_mem_cons.2 ⟨subd13_1_150, List.forall_mem_cons.2 ⟨subd13_1_151, List.forall_mem_cons.2 ⟨subd13_1_152, List.forall_mem_cons.2 ⟨subd13_1_153, List.forall_mem_cons.2 ⟨subd13_1_154, List.forall_mem_cons.2 ⟨subd13_1_155, List.forall_mem_cons.2 ⟨subd13_1_156, List.forall_mem_cons.2 ⟨subd13_1_157, List.forall_mem_cons.2 ⟨subd13_1_158, List.forall_mem_cons.2 ⟨subd13_1_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C101
