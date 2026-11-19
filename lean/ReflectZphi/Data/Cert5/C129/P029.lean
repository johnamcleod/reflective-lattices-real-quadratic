import ReflectZphi.Data.Cert5.C129.Base

namespace ReflectZphi.Data.Cert5.C129

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_0_224 : subd9_0 [1, -1, 3] = true := by decide +kernel
theorem subd9_0_225 : subd9_0 [1, -1, 4] = true := by decide +kernel
theorem subd9_0_226 : subd9_0 [1, -1, 5] = true := by decide +kernel
theorem subd9_0_227 : subd9_0 [1, -1, 6] = true := by decide +kernel
theorem subd9_0_228 : subd9_0 [1, 0, -7] = true := by decide +kernel
theorem subd9_0_229 : subd9_0 [1, 0, -6] = true := by decide +kernel
theorem subd9_0_230 : subd9_0 [1, 0, -5] = true := by decide +kernel
theorem subd9_0_231 : subd9_0 [1, 0, -4] = true := by decide +kernel
theorem subd9_0_232 : subd9_0 [1, 0, -3] = true := by decide +kernel
theorem subd9_0_233 : subd9_0 [1, 0, -2] = true := by decide +kernel
theorem subd9_0_234 : subd9_0 [1, 0, -1] = true := by decide +kernel
theorem subd9_0_235 : subd9_0 [1, 0, 0] = true := by decide +kernel
theorem subd9_0_236 : subd9_0 [1, 0, 1] = true := by decide +kernel
theorem subd9_0_237 : subd9_0 [1, 0, 2] = true := by decide +kernel
theorem subd9_0_238 : subd9_0 [1, 0, 3] = true := by decide +kernel
theorem subd9_0_239 : subd9_0 [1, 0, 4] = true := by decide +kernel
theorem subd9_0_240 : subd9_0 [1, 0, 5] = true := by decide +kernel
theorem subd9_0_241 : subd9_0 [1, 0, 6] = true := by decide +kernel
theorem subd9_0_242 : subd9_0 [1, 1, -7] = true := by decide +kernel
theorem subd9_0_243 : subd9_0 [1, 1, -6] = true := by decide +kernel
theorem subd9_0_244 : subd9_0 [1, 1, -5] = true := by decide +kernel
theorem subd9_0_245 : subd9_0 [1, 1, -4] = true := by decide +kernel
theorem subd9_0_246 : subd9_0 [1, 1, -3] = true := by decide +kernel
theorem subd9_0_247 : subd9_0 [1, 1, -2] = true := by decide +kernel
theorem subd9_0_248 : subd9_0 [1, 1, -1] = true := by decide +kernel
theorem subd9_0_249 : subd9_0 [1, 1, 0] = true := by decide +kernel
theorem subd9_0_250 : subd9_0 [1, 1, 1] = true := by decide +kernel
theorem subd9_0_251 : subd9_0 [1, 1, 2] = true := by decide +kernel
theorem subd9_0_252 : subd9_0 [1, 1, 3] = true := by decide +kernel
theorem subd9_0_253 : subd9_0 [1, 1, 4] = true := by decide +kernel
theorem subd9_0_254 : subd9_0 [1, 1, 5] = true := by decide +kernel
theorem subd9_0_255 : subd9_0 [1, 1, 6] = true := by decide +kernel
theorem sbd9_0_7 : ∀ q ∈ blkd9_0_7, subd9_0 q = true := by
  unfold blkd9_0_7
  exact List.forall_mem_cons.2 ⟨subd9_0_224, List.forall_mem_cons.2 ⟨subd9_0_225, List.forall_mem_cons.2 ⟨subd9_0_226, List.forall_mem_cons.2 ⟨subd9_0_227, List.forall_mem_cons.2 ⟨subd9_0_228, List.forall_mem_cons.2 ⟨subd9_0_229, List.forall_mem_cons.2 ⟨subd9_0_230, List.forall_mem_cons.2 ⟨subd9_0_231, List.forall_mem_cons.2 ⟨subd9_0_232, List.forall_mem_cons.2 ⟨subd9_0_233, List.forall_mem_cons.2 ⟨subd9_0_234, List.forall_mem_cons.2 ⟨subd9_0_235, List.forall_mem_cons.2 ⟨subd9_0_236, List.forall_mem_cons.2 ⟨subd9_0_237, List.forall_mem_cons.2 ⟨subd9_0_238, List.forall_mem_cons.2 ⟨subd9_0_239, List.forall_mem_cons.2 ⟨subd9_0_240, List.forall_mem_cons.2 ⟨subd9_0_241, List.forall_mem_cons.2 ⟨subd9_0_242, List.forall_mem_cons.2 ⟨subd9_0_243, List.forall_mem_cons.2 ⟨subd9_0_244, List.forall_mem_cons.2 ⟨subd9_0_245, List.forall_mem_cons.2 ⟨subd9_0_246, List.forall_mem_cons.2 ⟨subd9_0_247, List.forall_mem_cons.2 ⟨subd9_0_248, List.forall_mem_cons.2 ⟨subd9_0_249, List.forall_mem_cons.2 ⟨subd9_0_250, List.forall_mem_cons.2 ⟨subd9_0_251, List.forall_mem_cons.2 ⟨subd9_0_252, List.forall_mem_cons.2 ⟨subd9_0_253, List.forall_mem_cons.2 ⟨subd9_0_254, List.forall_mem_cons.2 ⟨subd9_0_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_256 : subd9_0 [1, 2] = true := by decide +kernel
theorem subd9_0_257 : subd9_0 [1, 3] = true := by decide +kernel
theorem subd9_0_258 : subd9_0 [1, 4] = true := by decide +kernel
theorem subd9_0_259 : subd9_0 [1, 5] = true := by decide +kernel
theorem subd9_0_260 : subd9_0 [2, -6] = true := by decide +kernel
theorem subd9_0_261 : subd9_0 [2, -5] = true := by decide +kernel
theorem subd9_0_262 : subd9_0 [2, -4] = true := by decide +kernel
theorem subd9_0_263 : subd9_0 [2, -3] = true := by decide +kernel
theorem subd9_0_264 : subd9_0 [2, -2] = true := by decide +kernel
theorem subd9_0_265 : subd9_0 [2, -1, -7] = true := by decide +kernel
theorem subd9_0_266 : subd9_0 [2, -1, -6] = true := by decide +kernel
theorem subd9_0_267 : subd9_0 [2, -1, -5] = true := by decide +kernel
theorem subd9_0_268 : subd9_0 [2, -1, -4] = true := by decide +kernel
theorem subd9_0_269 : subd9_0 [2, -1, -3] = true := by decide +kernel
theorem subd9_0_270 : subd9_0 [2, -1, -2] = true := by decide +kernel
theorem subd9_0_271 : subd9_0 [2, -1, -1] = true := by decide +kernel
theorem subd9_0_272 : subd9_0 [2, -1, 0] = true := by decide +kernel
theorem subd9_0_273 : subd9_0 [2, -1, 1] = true := by decide +kernel
theorem subd9_0_274 : subd9_0 [2, -1, 2] = true := by decide +kernel
theorem subd9_0_275 : subd9_0 [2, -1, 3] = true := by decide +kernel
theorem subd9_0_276 : subd9_0 [2, -1, 4] = true := by decide +kernel
theorem subd9_0_277 : subd9_0 [2, -1, 5] = true := by decide +kernel
theorem subd9_0_278 : subd9_0 [2, -1, 6] = true := by decide +kernel
theorem subd9_0_279 : subd9_0 [2, 0, -7] = true := by decide +kernel
theorem subd9_0_280 : subd9_0 [2, 0, -6] = true := by decide +kernel
theorem subd9_0_281 : subd9_0 [2, 0, -5] = true := by decide +kernel
theorem subd9_0_282 : subd9_0 [2, 0, -4] = true := by decide +kernel
theorem subd9_0_283 : subd9_0 [2, 0, -3] = true := by decide +kernel
theorem subd9_0_284 : subd9_0 [2, 0, -2] = true := by decide +kernel
theorem subd9_0_285 : subd9_0 [2, 0, -1] = true := by decide +kernel
theorem subd9_0_286 : subd9_0 [2, 0, 0] = true := by decide +kernel
theorem subd9_0_287 : subd9_0 [2, 0, 1] = true := by decide +kernel
theorem sbd9_0_8 : ∀ q ∈ blkd9_0_8, subd9_0 q = true := by
  unfold blkd9_0_8
  exact List.forall_mem_cons.2 ⟨subd9_0_256, List.forall_mem_cons.2 ⟨subd9_0_257, List.forall_mem_cons.2 ⟨subd9_0_258, List.forall_mem_cons.2 ⟨subd9_0_259, List.forall_mem_cons.2 ⟨subd9_0_260, List.forall_mem_cons.2 ⟨subd9_0_261, List.forall_mem_cons.2 ⟨subd9_0_262, List.forall_mem_cons.2 ⟨subd9_0_263, List.forall_mem_cons.2 ⟨subd9_0_264, List.forall_mem_cons.2 ⟨subd9_0_265, List.forall_mem_cons.2 ⟨subd9_0_266, List.forall_mem_cons.2 ⟨subd9_0_267, List.forall_mem_cons.2 ⟨subd9_0_268, List.forall_mem_cons.2 ⟨subd9_0_269, List.forall_mem_cons.2 ⟨subd9_0_270, List.forall_mem_cons.2 ⟨subd9_0_271, List.forall_mem_cons.2 ⟨subd9_0_272, List.forall_mem_cons.2 ⟨subd9_0_273, List.forall_mem_cons.2 ⟨subd9_0_274, List.forall_mem_cons.2 ⟨subd9_0_275, List.forall_mem_cons.2 ⟨subd9_0_276, List.forall_mem_cons.2 ⟨subd9_0_277, List.forall_mem_cons.2 ⟨subd9_0_278, List.forall_mem_cons.2 ⟨subd9_0_279, List.forall_mem_cons.2 ⟨subd9_0_280, List.forall_mem_cons.2 ⟨subd9_0_281, List.forall_mem_cons.2 ⟨subd9_0_282, List.forall_mem_cons.2 ⟨subd9_0_283, List.forall_mem_cons.2 ⟨subd9_0_284, List.forall_mem_cons.2 ⟨subd9_0_285, List.forall_mem_cons.2 ⟨subd9_0_286, List.forall_mem_cons.2 ⟨subd9_0_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_288 : subd9_0 [2, 0, 2] = true := by decide +kernel
theorem subd9_0_289 : subd9_0 [2, 0, 3] = true := by decide +kernel
theorem subd9_0_290 : subd9_0 [2, 0, 4] = true := by decide +kernel
theorem subd9_0_291 : subd9_0 [2, 0, 5] = true := by decide +kernel
theorem subd9_0_292 : subd9_0 [2, 0, 6] = true := by decide +kernel
theorem subd9_0_293 : subd9_0 [2, 1] = true := by decide +kernel
theorem subd9_0_294 : subd9_0 [2, 2] = true := by decide +kernel
theorem subd9_0_295 : subd9_0 [2, 3] = true := by decide +kernel
theorem subd9_0_296 : subd9_0 [2, 4] = true := by decide +kernel
theorem subd9_0_297 : subd9_0 [3, -6] = true := by decide +kernel
theorem subd9_0_298 : subd9_0 [3, -5] = true := by decide +kernel
theorem subd9_0_299 : subd9_0 [3, -4] = true := by decide +kernel
theorem subd9_0_300 : subd9_0 [3, -3] = true := by decide +kernel
theorem subd9_0_301 : subd9_0 [3, -2] = true := by decide +kernel
theorem subd9_0_302 : subd9_0 [3, -1] = true := by decide +kernel
theorem subd9_0_303 : subd9_0 [3, 0] = true := by decide +kernel
theorem subd9_0_304 : subd9_0 [3, 1] = true := by decide +kernel
theorem subd9_0_305 : subd9_0 [3, 2] = true := by decide +kernel
theorem subd9_0_306 : subd9_0 [3, 3] = true := by decide +kernel
theorem subd9_0_307 : subd9_0 [4, -5] = true := by decide +kernel
theorem subd9_0_308 : subd9_0 [4, -4] = true := by decide +kernel
theorem subd9_0_309 : subd9_0 [4, -3] = true := by decide +kernel
theorem subd9_0_310 : subd9_0 [4, -2] = true := by decide +kernel
theorem subd9_0_311 : subd9_0 [4, -1] = true := by decide +kernel
theorem subd9_0_312 : subd9_0 [4, 0] = true := by decide +kernel
theorem subd9_0_313 : subd9_0 [4, 1] = true := by decide +kernel
theorem subd9_0_314 : subd9_0 [4, 2] = true := by decide +kernel
theorem sbd9_0_9 : ∀ q ∈ blkd9_0_9, subd9_0 q = true := by
  unfold blkd9_0_9
  exact List.forall_mem_cons.2 ⟨subd9_0_288, List.forall_mem_cons.2 ⟨subd9_0_289, List.forall_mem_cons.2 ⟨subd9_0_290, List.forall_mem_cons.2 ⟨subd9_0_291, List.forall_mem_cons.2 ⟨subd9_0_292, List.forall_mem_cons.2 ⟨subd9_0_293, List.forall_mem_cons.2 ⟨subd9_0_294, List.forall_mem_cons.2 ⟨subd9_0_295, List.forall_mem_cons.2 ⟨subd9_0_296, List.forall_mem_cons.2 ⟨subd9_0_297, List.forall_mem_cons.2 ⟨subd9_0_298, List.forall_mem_cons.2 ⟨subd9_0_299, List.forall_mem_cons.2 ⟨subd9_0_300, List.forall_mem_cons.2 ⟨subd9_0_301, List.forall_mem_cons.2 ⟨subd9_0_302, List.forall_mem_cons.2 ⟨subd9_0_303, List.forall_mem_cons.2 ⟨subd9_0_304, List.forall_mem_cons.2 ⟨subd9_0_305, List.forall_mem_cons.2 ⟨subd9_0_306, List.forall_mem_cons.2 ⟨subd9_0_307, List.forall_mem_cons.2 ⟨subd9_0_308, List.forall_mem_cons.2 ⟨subd9_0_309, List.forall_mem_cons.2 ⟨subd9_0_310, List.forall_mem_cons.2 ⟨subd9_0_311, List.forall_mem_cons.2 ⟨subd9_0_312, List.forall_mem_cons.2 ⟨subd9_0_313, List.forall_mem_cons.2 ⟨subd9_0_314, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_1 : ldCheck G d9_1.U d9_1.ms ldd9_1 = true := by decide +kernel
theorem pre_okd9_1 : subPre G cell9 d9_1 = true := by decide +kernel
theorem subd9_1_0 : subd9_1 [-3, -4] = true := by decide +kernel
theorem subd9_1_1 : subd9_1 [-3, -3] = true := by decide +kernel
theorem subd9_1_2 : subd9_1 [-3, -2] = true := by decide +kernel
theorem subd9_1_3 : subd9_1 [-3, -1] = true := by decide +kernel
theorem subd9_1_4 : subd9_1 [-3, 0] = true := by decide +kernel
theorem subd9_1_5 : subd9_1 [-3, 1] = true := by decide +kernel
theorem subd9_1_6 : subd9_1 [-2, -5] = true := by decide +kernel
theorem subd9_1_7 : subd9_1 [-2, -4] = true := by decide +kernel
theorem subd9_1_8 : subd9_1 [-2, -3] = true := by decide +kernel
theorem subd9_1_9 : subd9_1 [-2, -2] = true := by decide +kernel
theorem subd9_1_10 : subd9_1 [-2, -1, -7] = true := by decide +kernel
theorem subd9_1_11 : subd9_1 [-2, -1, -6] = true := by decide +kernel
theorem subd9_1_12 : subd9_1 [-2, -1, -5] = true := by decide +kernel
theorem subd9_1_13 : subd9_1 [-2, -1, -4] = true := by decide +kernel
theorem subd9_1_14 : subd9_1 [-2, -1, -3] = true := by decide +kernel
theorem subd9_1_15 : subd9_1 [-2, -1, -2] = true := by decide +kernel
theorem subd9_1_16 : subd9_1 [-2, -1, -1] = true := by decide +kernel
theorem subd9_1_17 : subd9_1 [-2, -1, 0] = true := by decide +kernel
theorem subd9_1_18 : subd9_1 [-2, -1, 1] = true := by decide +kernel
theorem subd9_1_19 : subd9_1 [-2, -1, 2] = true := by decide +kernel
theorem subd9_1_20 : subd9_1 [-2, -1, 3] = true := by decide +kernel
theorem subd9_1_21 : subd9_1 [-2, -1, 4] = true := by decide +kernel
theorem subd9_1_22 : subd9_1 [-2, -1, 5] = true := by decide +kernel
theorem subd9_1_23 : subd9_1 [-2, -1, 6] = true := by decide +kernel
theorem subd9_1_24 : subd9_1 [-2, 0, -6] = true := by decide +kernel
theorem subd9_1_25 : subd9_1 [-2, 0, -5] = true := by decide +kernel
theorem subd9_1_26 : subd9_1 [-2, 0, -4] = true := by decide +kernel
theorem subd9_1_27 : subd9_1 [-2, 0, -3] = true := by decide +kernel
theorem subd9_1_28 : subd9_1 [-2, 0, -2] = true := by decide +kernel
theorem subd9_1_29 : subd9_1 [-2, 0, -1] = true := by decide +kernel
theorem subd9_1_30 : subd9_1 [-2, 0, 0] = true := by decide +kernel
theorem subd9_1_31 : subd9_1 [-2, 0, 1] = true := by decide +kernel
theorem sbd9_1_0 : ∀ q ∈ blkd9_1_0, subd9_1 q = true := by
  unfold blkd9_1_0
  exact List.forall_mem_cons.2 ⟨subd9_1_0, List.forall_mem_cons.2 ⟨subd9_1_1, List.forall_mem_cons.2 ⟨subd9_1_2, List.forall_mem_cons.2 ⟨subd9_1_3, List.forall_mem_cons.2 ⟨subd9_1_4, List.forall_mem_cons.2 ⟨subd9_1_5, List.forall_mem_cons.2 ⟨subd9_1_6, List.forall_mem_cons.2 ⟨subd9_1_7, List.forall_mem_cons.2 ⟨subd9_1_8, List.forall_mem_cons.2 ⟨subd9_1_9, List.forall_mem_cons.2 ⟨subd9_1_10, List.forall_mem_cons.2 ⟨subd9_1_11, List.forall_mem_cons.2 ⟨subd9_1_12, List.forall_mem_cons.2 ⟨subd9_1_13, List.forall_mem_cons.2 ⟨subd9_1_14, List.forall_mem_cons.2 ⟨subd9_1_15, List.forall_mem_cons.2 ⟨subd9_1_16, List.forall_mem_cons.2 ⟨subd9_1_17, List.forall_mem_cons.2 ⟨subd9_1_18, List.forall_mem_cons.2 ⟨subd9_1_19, List.forall_mem_cons.2 ⟨subd9_1_20, List.forall_mem_cons.2 ⟨subd9_1_21, List.forall_mem_cons.2 ⟨subd9_1_22, List.forall_mem_cons.2 ⟨subd9_1_23, List.forall_mem_cons.2 ⟨subd9_1_24, List.forall_mem_cons.2 ⟨subd9_1_25, List.forall_mem_cons.2 ⟨subd9_1_26, List.forall_mem_cons.2 ⟨subd9_1_27, List.forall_mem_cons.2 ⟨subd9_1_28, List.forall_mem_cons.2 ⟨subd9_1_29, List.forall_mem_cons.2 ⟨subd9_1_30, List.forall_mem_cons.2 ⟨subd9_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_32 : subd9_1 [-2, 0, 2] = true := by decide +kernel
theorem subd9_1_33 : subd9_1 [-2, 0, 3] = true := by decide +kernel
theorem subd9_1_34 : subd9_1 [-2, 0, 4] = true := by decide +kernel
theorem subd9_1_35 : subd9_1 [-2, 0, 5] = true := by decide +kernel
theorem subd9_1_36 : subd9_1 [-2, 0, 6] = true := by decide +kernel
theorem subd9_1_37 : subd9_1 [-2, 1] = true := by decide +kernel
theorem subd9_1_38 : subd9_1 [-2, 2] = true := by decide +kernel
theorem subd9_1_39 : subd9_1 [-1, -5] = true := by decide +kernel
theorem subd9_1_40 : subd9_1 [-1, -4] = true := by decide +kernel
theorem subd9_1_41 : subd9_1 [-1, -3] = true := by decide +kernel
theorem subd9_1_42 : subd9_1 [-1, -2, -7] = true := by decide +kernel
theorem subd9_1_43 : subd9_1 [-1, -2, -6] = true := by decide +kernel
theorem subd9_1_44 : subd9_1 [-1, -2, -5] = true := by decide +kernel
theorem subd9_1_45 : subd9_1 [-1, -2, -4] = true := by decide +kernel
theorem subd9_1_46 : subd9_1 [-1, -2, -3] = true := by decide +kernel
theorem subd9_1_47 : subd9_1 [-1, -2, -2] = true := by decide +kernel
theorem subd9_1_48 : subd9_1 [-1, -2, -1] = true := by decide +kernel
theorem subd9_1_49 : subd9_1 [-1, -2, 0] = true := by decide +kernel
theorem subd9_1_50 : subd9_1 [-1, -2, 1] = true := by decide +kernel
theorem subd9_1_51 : subd9_1 [-1, -2, 2] = true := by decide +kernel
theorem subd9_1_52 : subd9_1 [-1, -2, 3] = true := by decide +kernel
theorem subd9_1_53 : subd9_1 [-1, -2, 4] = true := by decide +kernel
theorem subd9_1_54 : subd9_1 [-1, -2, 5] = true := by decide +kernel
theorem subd9_1_55 : subd9_1 [-1, -2, 6] = true := by decide +kernel
theorem subd9_1_56 : subd9_1 [-1, -1, -8] = true := by decide +kernel
theorem subd9_1_57 : subd9_1 [-1, -1, -7] = true := by decide +kernel
theorem subd9_1_58 : subd9_1 [-1, -1, -6] = true := by decide +kernel
theorem subd9_1_59 : subd9_1 [-1, -1, -5] = true := by decide +kernel
theorem subd9_1_60 : subd9_1 [-1, -1, -4] = true := by decide +kernel
theorem subd9_1_61 : subd9_1 [-1, -1, -3] = true := by decide +kernel
theorem subd9_1_62 : subd9_1 [-1, -1, -2] = true := by decide +kernel
theorem subd9_1_63 : subd9_1 [-1, -1, -1] = true := by decide +kernel
theorem sbd9_1_1 : ∀ q ∈ blkd9_1_1, subd9_1 q = true := by
  unfold blkd9_1_1
  exact List.forall_mem_cons.2 ⟨subd9_1_32, List.forall_mem_cons.2 ⟨subd9_1_33, List.forall_mem_cons.2 ⟨subd9_1_34, List.forall_mem_cons.2 ⟨subd9_1_35, List.forall_mem_cons.2 ⟨subd9_1_36, List.forall_mem_cons.2 ⟨subd9_1_37, List.forall_mem_cons.2 ⟨subd9_1_38, List.forall_mem_cons.2 ⟨subd9_1_39, List.forall_mem_cons.2 ⟨subd9_1_40, List.forall_mem_cons.2 ⟨subd9_1_41, List.forall_mem_cons.2 ⟨subd9_1_42, List.forall_mem_cons.2 ⟨subd9_1_43, List.forall_mem_cons.2 ⟨subd9_1_44, List.forall_mem_cons.2 ⟨subd9_1_45, List.forall_mem_cons.2 ⟨subd9_1_46, List.forall_mem_cons.2 ⟨subd9_1_47, List.forall_mem_cons.2 ⟨subd9_1_48, List.forall_mem_cons.2 ⟨subd9_1_49, List.forall_mem_cons.2 ⟨subd9_1_50, List.forall_mem_cons.2 ⟨subd9_1_51, List.forall_mem_cons.2 ⟨subd9_1_52, List.forall_mem_cons.2 ⟨subd9_1_53, List.forall_mem_cons.2 ⟨subd9_1_54, List.forall_mem_cons.2 ⟨subd9_1_55, List.forall_mem_cons.2 ⟨subd9_1_56, List.forall_mem_cons.2 ⟨subd9_1_57, List.forall_mem_cons.2 ⟨subd9_1_58, List.forall_mem_cons.2 ⟨subd9_1_59, List.forall_mem_cons.2 ⟨subd9_1_60, List.forall_mem_cons.2 ⟨subd9_1_61, List.forall_mem_cons.2 ⟨subd9_1_62, List.forall_mem_cons.2 ⟨subd9_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_64 : subd9_1 [-1, -1, 0] = true := by decide +kernel
theorem subd9_1_65 : subd9_1 [-1, -1, 1] = true := by decide +kernel
theorem subd9_1_66 : subd9_1 [-1, -1, 2] = true := by decide +kernel
theorem subd9_1_67 : subd9_1 [-1, -1, 3] = true := by decide +kernel
theorem subd9_1_68 : subd9_1 [-1, -1, 4] = true := by decide +kernel
theorem subd9_1_69 : subd9_1 [-1, -1, 5] = true := by decide +kernel
theorem subd9_1_70 : subd9_1 [-1, -1, 6] = true := by decide +kernel
theorem subd9_1_71 : subd9_1 [-1, -1, 7] = true := by decide +kernel
theorem subd9_1_72 : subd9_1 [-1, 0, -8] = true := by decide +kernel
theorem subd9_1_73 : subd9_1 [-1, 0, -7] = true := by decide +kernel
theorem subd9_1_74 : subd9_1 [-1, 0, -6] = true := by decide +kernel
theorem subd9_1_75 : subd9_1 [-1, 0, -5] = true := by decide +kernel
theorem subd9_1_76 : subd9_1 [-1, 0, -4] = true := by decide +kernel
theorem subd9_1_77 : subd9_1 [-1, 0, -3] = true := by decide +kernel
theorem subd9_1_78 : subd9_1 [-1, 0, -2] = true := by decide +kernel
theorem subd9_1_79 : subd9_1 [-1, 0, -1] = true := by decide +kernel
theorem subd9_1_80 : subd9_1 [-1, 0, 0] = true := by decide +kernel
theorem subd9_1_81 : subd9_1 [-1, 0, 1] = true := by decide +kernel
theorem subd9_1_82 : subd9_1 [-1, 0, 2] = true := by decide +kernel
theorem subd9_1_83 : subd9_1 [-1, 0, 3] = true := by decide +kernel
theorem subd9_1_84 : subd9_1 [-1, 0, 4] = true := by decide +kernel
theorem subd9_1_85 : subd9_1 [-1, 0, 5] = true := by decide +kernel
theorem subd9_1_86 : subd9_1 [-1, 0, 6] = true := by decide +kernel
theorem subd9_1_87 : subd9_1 [-1, 0, 7] = true := by decide +kernel
theorem subd9_1_88 : subd9_1 [-1, 1, -7] = true := by decide +kernel
theorem subd9_1_89 : subd9_1 [-1, 1, -6] = true := by decide +kernel
theorem subd9_1_90 : subd9_1 [-1, 1, -5] = true := by decide +kernel
theorem subd9_1_91 : subd9_1 [-1, 1, -4] = true := by decide +kernel
theorem subd9_1_92 : subd9_1 [-1, 1, -3] = true := by decide +kernel
theorem subd9_1_93 : subd9_1 [-1, 1, -2] = true := by decide +kernel
theorem subd9_1_94 : subd9_1 [-1, 1, -1] = true := by decide +kernel
theorem subd9_1_95 : subd9_1 [-1, 1, 0] = true := by decide +kernel
theorem sbd9_1_2 : ∀ q ∈ blkd9_1_2, subd9_1 q = true := by
  unfold blkd9_1_2
  exact List.forall_mem_cons.2 ⟨subd9_1_64, List.forall_mem_cons.2 ⟨subd9_1_65, List.forall_mem_cons.2 ⟨subd9_1_66, List.forall_mem_cons.2 ⟨subd9_1_67, List.forall_mem_cons.2 ⟨subd9_1_68, List.forall_mem_cons.2 ⟨subd9_1_69, List.forall_mem_cons.2 ⟨subd9_1_70, List.forall_mem_cons.2 ⟨subd9_1_71, List.forall_mem_cons.2 ⟨subd9_1_72, List.forall_mem_cons.2 ⟨subd9_1_73, List.forall_mem_cons.2 ⟨subd9_1_74, List.forall_mem_cons.2 ⟨subd9_1_75, List.forall_mem_cons.2 ⟨subd9_1_76, List.forall_mem_cons.2 ⟨subd9_1_77, List.forall_mem_cons.2 ⟨subd9_1_78, List.forall_mem_cons.2 ⟨subd9_1_79, List.forall_mem_cons.2 ⟨subd9_1_80, List.forall_mem_cons.2 ⟨subd9_1_81, List.forall_mem_cons.2 ⟨subd9_1_82, List.forall_mem_cons.2 ⟨subd9_1_83, List.forall_mem_cons.2 ⟨subd9_1_84, List.forall_mem_cons.2 ⟨subd9_1_85, List.forall_mem_cons.2 ⟨subd9_1_86, List.forall_mem_cons.2 ⟨subd9_1_87, List.forall_mem_cons.2 ⟨subd9_1_88, List.forall_mem_cons.2 ⟨subd9_1_89, List.forall_mem_cons.2 ⟨subd9_1_90, List.forall_mem_cons.2 ⟨subd9_1_91, List.forall_mem_cons.2 ⟨subd9_1_92, List.forall_mem_cons.2 ⟨subd9_1_93, List.forall_mem_cons.2 ⟨subd9_1_94, List.forall_mem_cons.2 ⟨subd9_1_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_96 : subd9_1 [-1, 1, 1] = true := by decide +kernel
theorem subd9_1_97 : subd9_1 [-1, 1, 2] = true := by decide +kernel
theorem subd9_1_98 : subd9_1 [-1, 1, 3] = true := by decide +kernel
theorem subd9_1_99 : subd9_1 [-1, 1, 4] = true := by decide +kernel
theorem subd9_1_100 : subd9_1 [-1, 1, 5] = true := by decide +kernel
theorem subd9_1_101 : subd9_1 [-1, 1, 6] = true := by decide +kernel
theorem subd9_1_102 : subd9_1 [-1, 1, 7] = true := by decide +kernel
theorem subd9_1_103 : subd9_1 [-1, 2] = true := by decide +kernel
theorem subd9_1_104 : subd9_1 [-1, 3] = true := by decide +kernel
theorem subd9_1_105 : subd9_1 [0, -5] = true := by decide +kernel
theorem subd9_1_106 : subd9_1 [0, -4] = true := by decide +kernel
theorem subd9_1_107 : subd9_1 [0, -3] = true := by decide +kernel
theorem subd9_1_108 : subd9_1 [0, -2, -7] = true := by decide +kernel
theorem subd9_1_109 : subd9_1 [0, -2, -6] = true := by decide +kernel
theorem subd9_1_110 : subd9_1 [0, -2, -5] = true := by decide +kernel
theorem subd9_1_111 : subd9_1 [0, -2, -4] = true := by decide +kernel
theorem subd9_1_112 : subd9_1 [0, -2, -3] = true := by decide +kernel
theorem subd9_1_113 : subd9_1 [0, -2, -2] = true := by decide +kernel
theorem subd9_1_114 : subd9_1 [0, -2, -1] = true := by decide +kernel
theorem subd9_1_115 : subd9_1 [0, -2, 0] = true := by decide +kernel
theorem subd9_1_116 : subd9_1 [0, -2, 1] = true := by decide +kernel
theorem subd9_1_117 : subd9_1 [0, -2, 2] = true := by decide +kernel
theorem subd9_1_118 : subd9_1 [0, -2, 3] = true := by decide +kernel
theorem subd9_1_119 : subd9_1 [0, -2, 4] = true := by decide +kernel
theorem subd9_1_120 : subd9_1 [0, -2, 5] = true := by decide +kernel
theorem subd9_1_121 : subd9_1 [0, -2, 6] = true := by decide +kernel
theorem subd9_1_122 : subd9_1 [0, -1, -8] = true := by decide +kernel
theorem subd9_1_123 : subd9_1 [0, -1, -7] = true := by decide +kernel
theorem subd9_1_124 : subd9_1 [0, -1, -6] = true := by decide +kernel
theorem subd9_1_125 : subd9_1 [0, -1, -5] = true := by decide +kernel
theorem subd9_1_126 : subd9_1 [0, -1, -4] = true := by decide +kernel
theorem subd9_1_127 : subd9_1 [0, -1, -3] = true := by decide +kernel
theorem sbd9_1_3 : ∀ q ∈ blkd9_1_3, subd9_1 q = true := by
  unfold blkd9_1_3
  exact List.forall_mem_cons.2 ⟨subd9_1_96, List.forall_mem_cons.2 ⟨subd9_1_97, List.forall_mem_cons.2 ⟨subd9_1_98, List.forall_mem_cons.2 ⟨subd9_1_99, List.forall_mem_cons.2 ⟨subd9_1_100, List.forall_mem_cons.2 ⟨subd9_1_101, List.forall_mem_cons.2 ⟨subd9_1_102, List.forall_mem_cons.2 ⟨subd9_1_103, List.forall_mem_cons.2 ⟨subd9_1_104, List.forall_mem_cons.2 ⟨subd9_1_105, List.forall_mem_cons.2 ⟨subd9_1_106, List.forall_mem_cons.2 ⟨subd9_1_107, List.forall_mem_cons.2 ⟨subd9_1_108, List.forall_mem_cons.2 ⟨subd9_1_109, List.forall_mem_cons.2 ⟨subd9_1_110, List.forall_mem_cons.2 ⟨subd9_1_111, List.forall_mem_cons.2 ⟨subd9_1_112, List.forall_mem_cons.2 ⟨subd9_1_113, List.forall_mem_cons.2 ⟨subd9_1_114, List.forall_mem_cons.2 ⟨subd9_1_115, List.forall_mem_cons.2 ⟨subd9_1_116, List.forall_mem_cons.2 ⟨subd9_1_117, List.forall_mem_cons.2 ⟨subd9_1_118, List.forall_mem_cons.2 ⟨subd9_1_119, List.forall_mem_cons.2 ⟨subd9_1_120, List.forall_mem_cons.2 ⟨subd9_1_121, List.forall_mem_cons.2 ⟨subd9_1_122, List.forall_mem_cons.2 ⟨subd9_1_123, List.forall_mem_cons.2 ⟨subd9_1_124, List.forall_mem_cons.2 ⟨subd9_1_125, List.forall_mem_cons.2 ⟨subd9_1_126, List.forall_mem_cons.2 ⟨subd9_1_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_128 : subd9_1 [0, -1, -2] = true := by decide +kernel
theorem subd9_1_129 : subd9_1 [0, -1, -1] = true := by decide +kernel
theorem subd9_1_130 : subd9_1 [0, -1, 0] = true := by decide +kernel
theorem subd9_1_131 : subd9_1 [0, -1, 1] = true := by decide +kernel
theorem subd9_1_132 : subd9_1 [0, -1, 2] = true := by decide +kernel
theorem subd9_1_133 : subd9_1 [0, -1, 3] = true := by decide +kernel
theorem subd9_1_134 : subd9_1 [0, -1, 4] = true := by decide +kernel
theorem subd9_1_135 : subd9_1 [0, -1, 5] = true := by decide +kernel
theorem subd9_1_136 : subd9_1 [0, -1, 6] = true := by decide +kernel
theorem subd9_1_137 : subd9_1 [0, -1, 7] = true := by decide +kernel
theorem subd9_1_138 : subd9_1 [0, 0, -8] = true := by decide +kernel
theorem subd9_1_139 : subd9_1 [0, 0, -7] = true := by decide +kernel
theorem subd9_1_140 : subd9_1 [0, 0, -6] = true := by decide +kernel
theorem subd9_1_141 : subd9_1 [0, 0, -5] = true := by decide +kernel
theorem subd9_1_142 : subd9_1 [0, 0, -4] = true := by decide +kernel
theorem subd9_1_143 : subd9_1 [0, 0, -3] = true := by decide +kernel
theorem subd9_1_144 : subd9_1 [0, 0, -2] = true := by decide +kernel
theorem subd9_1_145 : subd9_1 [0, 0, -1] = true := by decide +kernel
theorem subd9_1_146 : subd9_1 [0, 0, 0] = true := by decide +kernel
theorem subd9_1_147 : subd9_1 [0, 0, 1] = true := by decide +kernel
theorem subd9_1_148 : subd9_1 [0, 0, 2] = true := by decide +kernel
theorem subd9_1_149 : subd9_1 [0, 0, 3] = true := by decide +kernel
theorem subd9_1_150 : subd9_1 [0, 0, 4] = true := by decide +kernel
theorem subd9_1_151 : subd9_1 [0, 0, 5] = true := by decide +kernel
theorem subd9_1_152 : subd9_1 [0, 0, 6] = true := by decide +kernel
theorem subd9_1_153 : subd9_1 [0, 0, 7] = true := by decide +kernel
theorem subd9_1_154 : subd9_1 [0, 1, -8] = true := by decide +kernel
theorem subd9_1_155 : subd9_1 [0, 1, -7] = true := by decide +kernel
theorem subd9_1_156 : subd9_1 [0, 1, -6] = true := by decide +kernel
theorem subd9_1_157 : subd9_1 [0, 1, -5] = true := by decide +kernel
theorem subd9_1_158 : subd9_1 [0, 1, -4] = true := by decide +kernel
theorem subd9_1_159 : subd9_1 [0, 1, -3] = true := by decide +kernel
theorem sbd9_1_4 : ∀ q ∈ blkd9_1_4, subd9_1 q = true := by
  unfold blkd9_1_4
  exact List.forall_mem_cons.2 ⟨subd9_1_128, List.forall_mem_cons.2 ⟨subd9_1_129, List.forall_mem_cons.2 ⟨subd9_1_130, List.forall_mem_cons.2 ⟨subd9_1_131, List.forall_mem_cons.2 ⟨subd9_1_132, List.forall_mem_cons.2 ⟨subd9_1_133, List.forall_mem_cons.2 ⟨subd9_1_134, List.forall_mem_cons.2 ⟨subd9_1_135, List.forall_mem_cons.2 ⟨subd9_1_136, List.forall_mem_cons.2 ⟨subd9_1_137, List.forall_mem_cons.2 ⟨subd9_1_138, List.forall_mem_cons.2 ⟨subd9_1_139, List.forall_mem_cons.2 ⟨subd9_1_140, List.forall_mem_cons.2 ⟨subd9_1_141, List.forall_mem_cons.2 ⟨subd9_1_142, List.forall_mem_cons.2 ⟨subd9_1_143, List.forall_mem_cons.2 ⟨subd9_1_144, List.forall_mem_cons.2 ⟨subd9_1_145, List.forall_mem_cons.2 ⟨subd9_1_146, List.forall_mem_cons.2 ⟨subd9_1_147, List.forall_mem_cons.2 ⟨subd9_1_148, List.forall_mem_cons.2 ⟨subd9_1_149, List.forall_mem_cons.2 ⟨subd9_1_150, List.forall_mem_cons.2 ⟨subd9_1_151, List.forall_mem_cons.2 ⟨subd9_1_152, List.forall_mem_cons.2 ⟨subd9_1_153, List.forall_mem_cons.2 ⟨subd9_1_154, List.forall_mem_cons.2 ⟨subd9_1_155, List.forall_mem_cons.2 ⟨subd9_1_156, List.forall_mem_cons.2 ⟨subd9_1_157, List.forall_mem_cons.2 ⟨subd9_1_158, List.forall_mem_cons.2 ⟨subd9_1_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_160 : subd9_1 [0, 1, -2] = true := by decide +kernel
theorem subd9_1_161 : subd9_1 [0, 1, -1] = true := by decide +kernel
theorem subd9_1_162 : subd9_1 [0, 1, 0] = true := by decide +kernel
theorem subd9_1_163 : subd9_1 [0, 1, 1] = true := by decide +kernel
theorem subd9_1_164 : subd9_1 [0, 1, 2] = true := by decide +kernel
theorem subd9_1_165 : subd9_1 [0, 1, 3] = true := by decide +kernel
theorem subd9_1_166 : subd9_1 [0, 1, 4] = true := by decide +kernel
theorem subd9_1_167 : subd9_1 [0, 1, 5] = true := by decide +kernel
theorem subd9_1_168 : subd9_1 [0, 1, 6] = true := by decide +kernel
theorem subd9_1_169 : subd9_1 [0, 1, 7] = true := by decide +kernel
theorem subd9_1_170 : subd9_1 [0, 2, -7] = true := by decide +kernel
theorem subd9_1_171 : subd9_1 [0, 2, -6] = true := by decide +kernel
theorem subd9_1_172 : subd9_1 [0, 2, -5] = true := by decide +kernel
theorem subd9_1_173 : subd9_1 [0, 2, -4] = true := by decide +kernel
theorem subd9_1_174 : subd9_1 [0, 2, -3] = true := by decide +kernel
theorem subd9_1_175 : subd9_1 [0, 2, -2] = true := by decide +kernel
theorem subd9_1_176 : subd9_1 [0, 2, -1] = true := by decide +kernel
theorem subd9_1_177 : subd9_1 [0, 2, 0] = true := by decide +kernel
theorem subd9_1_178 : subd9_1 [0, 2, 1] = true := by decide +kernel
theorem subd9_1_179 : subd9_1 [0, 2, 2] = true := by decide +kernel
theorem subd9_1_180 : subd9_1 [0, 2, 3] = true := by decide +kernel
theorem subd9_1_181 : subd9_1 [0, 2, 4] = true := by decide +kernel
theorem subd9_1_182 : subd9_1 [0, 2, 5] = true := by decide +kernel
theorem subd9_1_183 : subd9_1 [0, 2, 6] = true := by decide +kernel
theorem subd9_1_184 : subd9_1 [0, 3] = true := by decide +kernel
theorem subd9_1_185 : subd9_1 [0, 4] = true := by decide +kernel
theorem subd9_1_186 : subd9_1 [1, -4] = true := by decide +kernel
theorem subd9_1_187 : subd9_1 [1, -3] = true := by decide +kernel
theorem subd9_1_188 : subd9_1 [1, -2] = true := by decide +kernel
theorem subd9_1_189 : subd9_1 [1, -1, -8] = true := by decide +kernel
theorem subd9_1_190 : subd9_1 [1, -1, -7] = true := by decide +kernel
theorem subd9_1_191 : subd9_1 [1, -1, -6] = true := by decide +kernel
theorem sbd9_1_5 : ∀ q ∈ blkd9_1_5, subd9_1 q = true := by
  unfold blkd9_1_5
  exact List.forall_mem_cons.2 ⟨subd9_1_160, List.forall_mem_cons.2 ⟨subd9_1_161, List.forall_mem_cons.2 ⟨subd9_1_162, List.forall_mem_cons.2 ⟨subd9_1_163, List.forall_mem_cons.2 ⟨subd9_1_164, List.forall_mem_cons.2 ⟨subd9_1_165, List.forall_mem_cons.2 ⟨subd9_1_166, List.forall_mem_cons.2 ⟨subd9_1_167, List.forall_mem_cons.2 ⟨subd9_1_168, List.forall_mem_cons.2 ⟨subd9_1_169, List.forall_mem_cons.2 ⟨subd9_1_170, List.forall_mem_cons.2 ⟨subd9_1_171, List.forall_mem_cons.2 ⟨subd9_1_172, List.forall_mem_cons.2 ⟨subd9_1_173, List.forall_mem_cons.2 ⟨subd9_1_174, List.forall_mem_cons.2 ⟨subd9_1_175, List.forall_mem_cons.2 ⟨subd9_1_176, List.forall_mem_cons.2 ⟨subd9_1_177, List.forall_mem_cons.2 ⟨subd9_1_178, List.forall_mem_cons.2 ⟨subd9_1_179, List.forall_mem_cons.2 ⟨subd9_1_180, List.forall_mem_cons.2 ⟨subd9_1_181, List.forall_mem_cons.2 ⟨subd9_1_182, List.forall_mem_cons.2 ⟨subd9_1_183, List.forall_mem_cons.2 ⟨subd9_1_184, List.forall_mem_cons.2 ⟨subd9_1_185, List.forall_mem_cons.2 ⟨subd9_1_186, List.forall_mem_cons.2 ⟨subd9_1_187, List.forall_mem_cons.2 ⟨subd9_1_188, List.forall_mem_cons.2 ⟨subd9_1_189, List.forall_mem_cons.2 ⟨subd9_1_190, List.forall_mem_cons.2 ⟨subd9_1_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_192 : subd9_1 [1, -1, -5] = true := by decide +kernel
theorem subd9_1_193 : subd9_1 [1, -1, -4] = true := by decide +kernel
theorem subd9_1_194 : subd9_1 [1, -1, -3] = true := by decide +kernel
theorem subd9_1_195 : subd9_1 [1, -1, -2] = true := by decide +kernel
theorem subd9_1_196 : subd9_1 [1, -1, -1] = true := by decide +kernel
theorem subd9_1_197 : subd9_1 [1, -1, 0] = true := by decide +kernel
theorem subd9_1_198 : subd9_1 [1, -1, 1] = true := by decide +kernel
theorem subd9_1_199 : subd9_1 [1, -1, 2] = true := by decide +kernel
theorem subd9_1_200 : subd9_1 [1, -1, 3] = true := by decide +kernel
theorem subd9_1_201 : subd9_1 [1, -1, 4] = true := by decide +kernel
theorem subd9_1_202 : subd9_1 [1, -1, 5] = true := by decide +kernel
theorem subd9_1_203 : subd9_1 [1, -1, 6] = true := by decide +kernel
theorem subd9_1_204 : subd9_1 [1, 0, -8] = true := by decide +kernel
theorem subd9_1_205 : subd9_1 [1, 0, -7] = true := by decide +kernel
theorem subd9_1_206 : subd9_1 [1, 0, -6] = true := by decide +kernel
theorem subd9_1_207 : subd9_1 [1, 0, -5] = true := by decide +kernel
theorem subd9_1_208 : subd9_1 [1, 0, -4] = true := by decide +kernel
theorem subd9_1_209 : subd9_1 [1, 0, -3] = true := by decide +kernel
theorem subd9_1_210 : subd9_1 [1, 0, -2] = true := by decide +kernel
theorem subd9_1_211 : subd9_1 [1, 0, -1] = true := by decide +kernel
theorem subd9_1_212 : subd9_1 [1, 0, 0] = true := by decide +kernel
theorem subd9_1_213 : subd9_1 [1, 0, 1] = true := by decide +kernel
theorem subd9_1_214 : subd9_1 [1, 0, 2] = true := by decide +kernel
theorem subd9_1_215 : subd9_1 [1, 0, 3] = true := by decide +kernel
theorem subd9_1_216 : subd9_1 [1, 0, 4] = true := by decide +kernel
theorem subd9_1_217 : subd9_1 [1, 0, 5] = true := by decide +kernel
theorem subd9_1_218 : subd9_1 [1, 0, 6] = true := by decide +kernel
theorem subd9_1_219 : subd9_1 [1, 0, 7] = true := by decide +kernel
theorem subd9_1_220 : subd9_1 [1, 1, -8] = true := by decide +kernel
theorem subd9_1_221 : subd9_1 [1, 1, -7] = true := by decide +kernel
theorem subd9_1_222 : subd9_1 [1, 1, -6] = true := by decide +kernel
theorem subd9_1_223 : subd9_1 [1, 1, -5] = true := by decide +kernel
theorem sbd9_1_6 : ∀ q ∈ blkd9_1_6, subd9_1 q = true := by
  unfold blkd9_1_6
  exact List.forall_mem_cons.2 ⟨subd9_1_192, List.forall_mem_cons.2 ⟨subd9_1_193, List.forall_mem_cons.2 ⟨subd9_1_194, List.forall_mem_cons.2 ⟨subd9_1_195, List.forall_mem_cons.2 ⟨subd9_1_196, List.forall_mem_cons.2 ⟨subd9_1_197, List.forall_mem_cons.2 ⟨subd9_1_198, List.forall_mem_cons.2 ⟨subd9_1_199, List.forall_mem_cons.2 ⟨subd9_1_200, List.forall_mem_cons.2 ⟨subd9_1_201, List.forall_mem_cons.2 ⟨subd9_1_202, List.forall_mem_cons.2 ⟨subd9_1_203, List.forall_mem_cons.2 ⟨subd9_1_204, List.forall_mem_cons.2 ⟨subd9_1_205, List.forall_mem_cons.2 ⟨subd9_1_206, List.forall_mem_cons.2 ⟨subd9_1_207, List.forall_mem_cons.2 ⟨subd9_1_208, List.forall_mem_cons.2 ⟨subd9_1_209, List.forall_mem_cons.2 ⟨subd9_1_210, List.forall_mem_cons.2 ⟨subd9_1_211, List.forall_mem_cons.2 ⟨subd9_1_212, List.forall_mem_cons.2 ⟨subd9_1_213, List.forall_mem_cons.2 ⟨subd9_1_214, List.forall_mem_cons.2 ⟨subd9_1_215, List.forall_mem_cons.2 ⟨subd9_1_216, List.forall_mem_cons.2 ⟨subd9_1_217, List.forall_mem_cons.2 ⟨subd9_1_218, List.forall_mem_cons.2 ⟨subd9_1_219, List.forall_mem_cons.2 ⟨subd9_1_220, List.forall_mem_cons.2 ⟨subd9_1_221, List.forall_mem_cons.2 ⟨subd9_1_222, List.forall_mem_cons.2 ⟨subd9_1_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C129
