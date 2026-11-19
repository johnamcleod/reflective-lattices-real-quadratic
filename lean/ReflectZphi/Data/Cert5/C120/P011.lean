import ReflectZphi.Data.Cert5.C120.Base

namespace ReflectZphi.Data.Cert5.C120
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub9_224 : sub9 [1, -1, 1] = true := by decide +kernel
theorem sub9_225 : sub9 [1, -1, 2] = true := by decide +kernel
theorem sub9_226 : sub9 [1, -1, 3] = true := by decide +kernel
theorem sub9_227 : sub9 [1, -1, 4] = true := by decide +kernel
theorem sub9_228 : sub9 [1, -1, 5] = true := by decide +kernel
theorem sub9_229 : sub9 [1, -1, 6] = true := by decide +kernel
theorem sub9_230 : sub9 [1, -1, 7] = true := by decide +kernel
theorem sub9_231 : sub9 [1, 0, -7] = true := by decide +kernel
theorem sub9_232 : sub9 [1, 0, -6] = true := by decide +kernel
theorem sub9_233 : sub9 [1, 0, -5] = true := by decide +kernel
theorem sub9_234 : sub9 [1, 0, -4] = true := by decide +kernel
theorem sub9_235 : sub9 [1, 0, -3] = true := by decide +kernel
theorem sub9_236 : sub9 [1, 0, -2] = true := by decide +kernel
theorem sub9_237 : sub9 [1, 0, -1] = true := by decide +kernel
theorem sub9_238 : sub9 [1, 0, 0] = true := by decide +kernel
theorem sub9_239 : sub9 [1, 0, 1] = true := by decide +kernel
theorem sub9_240 : sub9 [1, 0, 2] = true := by decide +kernel
theorem sub9_241 : sub9 [1, 0, 3] = true := by decide +kernel
theorem sub9_242 : sub9 [1, 0, 4] = true := by decide +kernel
theorem sub9_243 : sub9 [1, 0, 5] = true := by decide +kernel
theorem sub9_244 : sub9 [1, 0, 6] = true := by decide +kernel
theorem sub9_245 : sub9 [1, 0, 7] = true := by decide +kernel
theorem sub9_246 : sub9 [1, 1, -7] = true := by decide +kernel
theorem sub9_247 : sub9 [1, 1, -6] = true := by decide +kernel
theorem sub9_248 : sub9 [1, 1, -5] = true := by decide +kernel
theorem sub9_249 : sub9 [1, 1, -4] = true := by decide +kernel
theorem sub9_250 : sub9 [1, 1, -3] = true := by decide +kernel
theorem sub9_251 : sub9 [1, 1, -2] = true := by decide +kernel
theorem sub9_252 : sub9 [1, 1, -1] = true := by decide +kernel
theorem sub9_253 : sub9 [1, 1, 0] = true := by decide +kernel
theorem sub9_254 : sub9 [1, 1, 1] = true := by decide +kernel
theorem sub9_255 : sub9 [1, 1, 2] = true := by decide +kernel
theorem sb9_7 : ∀ q ∈ blk9_7, sub9 q = true := by
  unfold blk9_7
  exact List.forall_mem_cons.2 ⟨sub9_224, List.forall_mem_cons.2 ⟨sub9_225, List.forall_mem_cons.2 ⟨sub9_226, List.forall_mem_cons.2 ⟨sub9_227, List.forall_mem_cons.2 ⟨sub9_228, List.forall_mem_cons.2 ⟨sub9_229, List.forall_mem_cons.2 ⟨sub9_230, List.forall_mem_cons.2 ⟨sub9_231, List.forall_mem_cons.2 ⟨sub9_232, List.forall_mem_cons.2 ⟨sub9_233, List.forall_mem_cons.2 ⟨sub9_234, List.forall_mem_cons.2 ⟨sub9_235, List.forall_mem_cons.2 ⟨sub9_236, List.forall_mem_cons.2 ⟨sub9_237, List.forall_mem_cons.2 ⟨sub9_238, List.forall_mem_cons.2 ⟨sub9_239, List.forall_mem_cons.2 ⟨sub9_240, List.forall_mem_cons.2 ⟨sub9_241, List.forall_mem_cons.2 ⟨sub9_242, List.forall_mem_cons.2 ⟨sub9_243, List.forall_mem_cons.2 ⟨sub9_244, List.forall_mem_cons.2 ⟨sub9_245, List.forall_mem_cons.2 ⟨sub9_246, List.forall_mem_cons.2 ⟨sub9_247, List.forall_mem_cons.2 ⟨sub9_248, List.forall_mem_cons.2 ⟨sub9_249, List.forall_mem_cons.2 ⟨sub9_250, List.forall_mem_cons.2 ⟨sub9_251, List.forall_mem_cons.2 ⟨sub9_252, List.forall_mem_cons.2 ⟨sub9_253, List.forall_mem_cons.2 ⟨sub9_254, List.forall_mem_cons.2 ⟨sub9_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_256 : sub9 [1, 1, 3] = true := by decide +kernel
theorem sub9_257 : sub9 [1, 1, 4] = true := by decide +kernel
theorem sub9_258 : sub9 [1, 1, 5] = true := by decide +kernel
theorem sub9_259 : sub9 [1, 1, 6] = true := by decide +kernel
theorem sub9_260 : sub9 [1, 1, 7] = true := by decide +kernel
theorem sub9_261 : sub9 [1, 2, -7] = true := by decide +kernel
theorem sub9_262 : sub9 [1, 2, -6] = true := by decide +kernel
theorem sub9_263 : sub9 [1, 2, -5] = true := by decide +kernel
theorem sub9_264 : sub9 [1, 2, -4] = true := by decide +kernel
theorem sub9_265 : sub9 [1, 2, -3] = true := by decide +kernel
theorem sub9_266 : sub9 [1, 2, -2] = true := by decide +kernel
theorem sub9_267 : sub9 [1, 2, -1] = true := by decide +kernel
theorem sub9_268 : sub9 [1, 2, 0] = true := by decide +kernel
theorem sub9_269 : sub9 [1, 2, 1] = true := by decide +kernel
theorem sub9_270 : sub9 [1, 2, 2] = true := by decide +kernel
theorem sub9_271 : sub9 [1, 2, 3] = true := by decide +kernel
theorem sub9_272 : sub9 [1, 2, 4] = true := by decide +kernel
theorem sub9_273 : sub9 [1, 2, 5] = true := by decide +kernel
theorem sub9_274 : sub9 [1, 2, 6] = true := by decide +kernel
theorem sub9_275 : sub9 [1, 3] = true := by decide +kernel
theorem sub9_276 : sub9 [1, 4] = true := by decide +kernel
theorem sub9_277 : sub9 [1, 5] = true := by decide +kernel
theorem sub9_278 : sub9 [2, -5] = true := by decide +kernel
theorem sub9_279 : sub9 [2, -4] = true := by decide +kernel
theorem sub9_280 : sub9 [2, -3] = true := by decide +kernel
theorem sub9_281 : sub9 [2, -2] = true := by decide +kernel
theorem sub9_282 : sub9 [2, -1] = true := by decide +kernel
theorem sub9_283 : sub9 [2, 0, -6] = true := by decide +kernel
theorem sub9_284 : sub9 [2, 0, -5] = true := by decide +kernel
theorem sub9_285 : sub9 [2, 0, -4] = true := by decide +kernel
theorem sub9_286 : sub9 [2, 0, -3] = true := by decide +kernel
theorem sub9_287 : sub9 [2, 0, -2] = true := by decide +kernel
theorem sb9_8 : ∀ q ∈ blk9_8, sub9 q = true := by
  unfold blk9_8
  exact List.forall_mem_cons.2 ⟨sub9_256, List.forall_mem_cons.2 ⟨sub9_257, List.forall_mem_cons.2 ⟨sub9_258, List.forall_mem_cons.2 ⟨sub9_259, List.forall_mem_cons.2 ⟨sub9_260, List.forall_mem_cons.2 ⟨sub9_261, List.forall_mem_cons.2 ⟨sub9_262, List.forall_mem_cons.2 ⟨sub9_263, List.forall_mem_cons.2 ⟨sub9_264, List.forall_mem_cons.2 ⟨sub9_265, List.forall_mem_cons.2 ⟨sub9_266, List.forall_mem_cons.2 ⟨sub9_267, List.forall_mem_cons.2 ⟨sub9_268, List.forall_mem_cons.2 ⟨sub9_269, List.forall_mem_cons.2 ⟨sub9_270, List.forall_mem_cons.2 ⟨sub9_271, List.forall_mem_cons.2 ⟨sub9_272, List.forall_mem_cons.2 ⟨sub9_273, List.forall_mem_cons.2 ⟨sub9_274, List.forall_mem_cons.2 ⟨sub9_275, List.forall_mem_cons.2 ⟨sub9_276, List.forall_mem_cons.2 ⟨sub9_277, List.forall_mem_cons.2 ⟨sub9_278, List.forall_mem_cons.2 ⟨sub9_279, List.forall_mem_cons.2 ⟨sub9_280, List.forall_mem_cons.2 ⟨sub9_281, List.forall_mem_cons.2 ⟨sub9_282, List.forall_mem_cons.2 ⟨sub9_283, List.forall_mem_cons.2 ⟨sub9_284, List.forall_mem_cons.2 ⟨sub9_285, List.forall_mem_cons.2 ⟨sub9_286, List.forall_mem_cons.2 ⟨sub9_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_288 : sub9 [2, 0, -1] = true := by decide +kernel
theorem sub9_289 : sub9 [2, 0, 0] = true := by decide +kernel
theorem sub9_290 : sub9 [2, 0, 1] = true := by decide +kernel
theorem sub9_291 : sub9 [2, 0, 2] = true := by decide +kernel
theorem sub9_292 : sub9 [2, 0, 3] = true := by decide +kernel
theorem sub9_293 : sub9 [2, 0, 4] = true := by decide +kernel
theorem sub9_294 : sub9 [2, 0, 5] = true := by decide +kernel
theorem sub9_295 : sub9 [2, 0, 6] = true := by decide +kernel
theorem sub9_296 : sub9 [2, 0, 7] = true := by decide +kernel
theorem sub9_297 : sub9 [2, 1, -6] = true := by decide +kernel
theorem sub9_298 : sub9 [2, 1, -5] = true := by decide +kernel
theorem sub9_299 : sub9 [2, 1, -4] = true := by decide +kernel
theorem sub9_300 : sub9 [2, 1, -3] = true := by decide +kernel
theorem sub9_301 : sub9 [2, 1, -2] = true := by decide +kernel
theorem sub9_302 : sub9 [2, 1, -1] = true := by decide +kernel
theorem sub9_303 : sub9 [2, 1, 0] = true := by decide +kernel
theorem sub9_304 : sub9 [2, 1, 1] = true := by decide +kernel
theorem sub9_305 : sub9 [2, 1, 2] = true := by decide +kernel
theorem sub9_306 : sub9 [2, 1, 3] = true := by decide +kernel
theorem sub9_307 : sub9 [2, 1, 4] = true := by decide +kernel
theorem sub9_308 : sub9 [2, 1, 5] = true := by decide +kernel
theorem sub9_309 : sub9 [2, 1, 6] = true := by decide +kernel
theorem sub9_310 : sub9 [2, 1, 7] = true := by decide +kernel
theorem sub9_311 : sub9 [2, 2] = true := by decide +kernel
theorem sub9_312 : sub9 [2, 3] = true := by decide +kernel
theorem sub9_313 : sub9 [2, 4] = true := by decide +kernel
theorem sub9_314 : sub9 [2, 5] = true := by decide +kernel
theorem sub9_315 : sub9 [3, -5] = true := by decide +kernel
theorem sub9_316 : sub9 [3, -4] = true := by decide +kernel
theorem sub9_317 : sub9 [3, -3] = true := by decide +kernel
theorem sub9_318 : sub9 [3, -2] = true := by decide +kernel
theorem sub9_319 : sub9 [3, -1] = true := by decide +kernel
theorem sb9_9 : ∀ q ∈ blk9_9, sub9 q = true := by
  unfold blk9_9
  exact List.forall_mem_cons.2 ⟨sub9_288, List.forall_mem_cons.2 ⟨sub9_289, List.forall_mem_cons.2 ⟨sub9_290, List.forall_mem_cons.2 ⟨sub9_291, List.forall_mem_cons.2 ⟨sub9_292, List.forall_mem_cons.2 ⟨sub9_293, List.forall_mem_cons.2 ⟨sub9_294, List.forall_mem_cons.2 ⟨sub9_295, List.forall_mem_cons.2 ⟨sub9_296, List.forall_mem_cons.2 ⟨sub9_297, List.forall_mem_cons.2 ⟨sub9_298, List.forall_mem_cons.2 ⟨sub9_299, List.forall_mem_cons.2 ⟨sub9_300, List.forall_mem_cons.2 ⟨sub9_301, List.forall_mem_cons.2 ⟨sub9_302, List.forall_mem_cons.2 ⟨sub9_303, List.forall_mem_cons.2 ⟨sub9_304, List.forall_mem_cons.2 ⟨sub9_305, List.forall_mem_cons.2 ⟨sub9_306, List.forall_mem_cons.2 ⟨sub9_307, List.forall_mem_cons.2 ⟨sub9_308, List.forall_mem_cons.2 ⟨sub9_309, List.forall_mem_cons.2 ⟨sub9_310, List.forall_mem_cons.2 ⟨sub9_311, List.forall_mem_cons.2 ⟨sub9_312, List.forall_mem_cons.2 ⟨sub9_313, List.forall_mem_cons.2 ⟨sub9_314, List.forall_mem_cons.2 ⟨sub9_315, List.forall_mem_cons.2 ⟨sub9_316, List.forall_mem_cons.2 ⟨sub9_317, List.forall_mem_cons.2 ⟨sub9_318, List.forall_mem_cons.2 ⟨sub9_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_320 : sub9 [3, 0] = true := by decide +kernel
theorem sub9_321 : sub9 [3, 1] = true := by decide +kernel
theorem sub9_322 : sub9 [3, 2] = true := by decide +kernel
theorem sub9_323 : sub9 [3, 3] = true := by decide +kernel
theorem sub9_324 : sub9 [3, 4] = true := by decide +kernel
theorem sub9_325 : sub9 [3, 5] = true := by decide +kernel
theorem sub9_326 : sub9 [4, -4] = true := by decide +kernel
theorem sub9_327 : sub9 [4, -3] = true := by decide +kernel
theorem sub9_328 : sub9 [4, -2] = true := by decide +kernel
theorem sub9_329 : sub9 [4, -1] = true := by decide +kernel
theorem sub9_330 : sub9 [4, 0] = true := by decide +kernel
theorem sub9_331 : sub9 [4, 1] = true := by decide +kernel
theorem sub9_332 : sub9 [4, 2] = true := by decide +kernel
theorem sub9_333 : sub9 [4, 3] = true := by decide +kernel
theorem sub9_334 : sub9 [4, 4] = true := by decide +kernel
theorem sub9_335 : sub9 [4, 5] = true := by decide +kernel
theorem sub9_336 : sub9 [5, -3] = true := by decide +kernel
theorem sub9_337 : sub9 [5, -2] = true := by decide +kernel
theorem sub9_338 : sub9 [5, -1] = true := by decide +kernel
theorem sub9_339 : sub9 [5, 0] = true := by decide +kernel
theorem sub9_340 : sub9 [5, 1] = true := by decide +kernel
theorem sub9_341 : sub9 [5, 2] = true := by decide +kernel
theorem sub9_342 : sub9 [5, 3] = true := by decide +kernel
theorem sub9_343 : sub9 [5, 4] = true := by decide +kernel
theorem sub9_344 : sub9 [6] = true := by decide +kernel
theorem sb9_10 : ∀ q ∈ blk9_10, sub9 q = true := by
  unfold blk9_10
  exact List.forall_mem_cons.2 ⟨sub9_320, List.forall_mem_cons.2 ⟨sub9_321, List.forall_mem_cons.2 ⟨sub9_322, List.forall_mem_cons.2 ⟨sub9_323, List.forall_mem_cons.2 ⟨sub9_324, List.forall_mem_cons.2 ⟨sub9_325, List.forall_mem_cons.2 ⟨sub9_326, List.forall_mem_cons.2 ⟨sub9_327, List.forall_mem_cons.2 ⟨sub9_328, List.forall_mem_cons.2 ⟨sub9_329, List.forall_mem_cons.2 ⟨sub9_330, List.forall_mem_cons.2 ⟨sub9_331, List.forall_mem_cons.2 ⟨sub9_332, List.forall_mem_cons.2 ⟨sub9_333, List.forall_mem_cons.2 ⟨sub9_334, List.forall_mem_cons.2 ⟨sub9_335, List.forall_mem_cons.2 ⟨sub9_336, List.forall_mem_cons.2 ⟨sub9_337, List.forall_mem_cons.2 ⟨sub9_338, List.forall_mem_cons.2 ⟨sub9_339, List.forall_mem_cons.2 ⟨sub9_340, List.forall_mem_cons.2 ⟨sub9_341, List.forall_mem_cons.2 ⟨sub9_342, List.forall_mem_cons.2 ⟨sub9_343, List.forall_mem_cons.2 ⟨sub9_344, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_0 : sub10 [-5] = true := by decide +kernel
theorem sub10_1 : sub10 [-4, -6] = true := by decide +kernel
theorem sub10_2 : sub10 [-4, -5] = true := by decide +kernel
theorem sub10_3 : sub10 [-4, -4] = true := by decide +kernel
theorem sub10_4 : sub10 [-4, -3] = true := by decide +kernel
theorem sub10_5 : sub10 [-4, -2] = true := by decide +kernel
theorem sub10_6 : sub10 [-4, -1] = true := by decide +kernel
theorem sub10_7 : sub10 [-4, 0] = true := by decide +kernel
theorem sub10_8 : sub10 [-4, 1] = true := by decide +kernel
theorem sub10_9 : sub10 [-3, -7] = true := by decide +kernel
theorem sub10_10 : sub10 [-3, -6] = true := by decide +kernel
theorem sub10_11 : sub10 [-3, -5] = true := by decide +kernel
theorem sub10_12 : sub10 [-3, -4] = true := by decide +kernel
theorem sub10_13 : sub10 [-3, -3] = true := by decide +kernel
theorem sub10_14 : sub10 [-3, -2] = true := by decide +kernel
theorem sub10_15 : sub10 [-3, -1] = true := by decide +kernel
theorem sub10_16 : sub10 [-3, 0] = true := by decide +kernel
theorem sub10_17 : sub10 [-3, 1] = true := by decide +kernel
theorem sub10_18 : sub10 [-3, 2] = true := by decide +kernel
theorem sub10_19 : sub10 [-3, 3] = true := by decide +kernel
theorem sub10_20 : sub10 [-2, -7] = true := by decide +kernel
theorem sub10_21 : sub10 [-2, -6] = true := by decide +kernel
theorem sub10_22 : sub10 [-2, -5] = true := by decide +kernel
theorem sub10_23 : sub10 [-2, -4] = true := by decide +kernel
theorem sub10_24 : sub10 [-2, -3] = true := by decide +kernel
theorem sub10_25 : sub10 [-2, -2, -7] = true := by decide +kernel
theorem sub10_26 : sub10 [-2, -2, -6] = true := by decide +kernel
theorem sub10_27 : sub10 [-2, -2, -5] = true := by decide +kernel
theorem sub10_28 : sub10 [-2, -2, -4] = true := by decide +kernel
theorem sub10_29 : sub10 [-2, -2, -3] = true := by decide +kernel
theorem sub10_30 : sub10 [-2, -2, -2] = true := by decide +kernel
theorem sub10_31 : sub10 [-2, -2, -1] = true := by decide +kernel
theorem sb10_0 : ∀ q ∈ blk10_0, sub10 q = true := by
  unfold blk10_0
  exact List.forall_mem_cons.2 ⟨sub10_0, List.forall_mem_cons.2 ⟨sub10_1, List.forall_mem_cons.2 ⟨sub10_2, List.forall_mem_cons.2 ⟨sub10_3, List.forall_mem_cons.2 ⟨sub10_4, List.forall_mem_cons.2 ⟨sub10_5, List.forall_mem_cons.2 ⟨sub10_6, List.forall_mem_cons.2 ⟨sub10_7, List.forall_mem_cons.2 ⟨sub10_8, List.forall_mem_cons.2 ⟨sub10_9, List.forall_mem_cons.2 ⟨sub10_10, List.forall_mem_cons.2 ⟨sub10_11, List.forall_mem_cons.2 ⟨sub10_12, List.forall_mem_cons.2 ⟨sub10_13, List.forall_mem_cons.2 ⟨sub10_14, List.forall_mem_cons.2 ⟨sub10_15, List.forall_mem_cons.2 ⟨sub10_16, List.forall_mem_cons.2 ⟨sub10_17, List.forall_mem_cons.2 ⟨sub10_18, List.forall_mem_cons.2 ⟨sub10_19, List.forall_mem_cons.2 ⟨sub10_20, List.forall_mem_cons.2 ⟨sub10_21, List.forall_mem_cons.2 ⟨sub10_22, List.forall_mem_cons.2 ⟨sub10_23, List.forall_mem_cons.2 ⟨sub10_24, List.forall_mem_cons.2 ⟨sub10_25, List.forall_mem_cons.2 ⟨sub10_26, List.forall_mem_cons.2 ⟨sub10_27, List.forall_mem_cons.2 ⟨sub10_28, List.forall_mem_cons.2 ⟨sub10_29, List.forall_mem_cons.2 ⟨sub10_30, List.forall_mem_cons.2 ⟨sub10_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_32 : sub10 [-2, -2, 0] = true := by decide +kernel
theorem sub10_33 : sub10 [-2, -2, 1] = true := by decide +kernel
theorem sub10_34 : sub10 [-2, -2, 2] = true := by decide +kernel
theorem sub10_35 : sub10 [-2, -2, 3] = true := by decide +kernel
theorem sub10_36 : sub10 [-2, -2, 4] = true := by decide +kernel
theorem sub10_37 : sub10 [-2, -2, 5] = true := by decide +kernel
theorem sub10_38 : sub10 [-2, -2, 6] = true := by decide +kernel
theorem sub10_39 : sub10 [-2, -2, 7] = true := by decide +kernel
theorem sub10_40 : sub10 [-2, -1, -8] = true := by decide +kernel
theorem sub10_41 : sub10 [-2, -1, -7] = true := by decide +kernel
theorem sub10_42 : sub10 [-2, -1, -6] = true := by decide +kernel
theorem sub10_43 : sub10 [-2, -1, -5] = true := by decide +kernel
theorem sub10_44 : sub10 [-2, -1, -4] = true := by decide +kernel
theorem sub10_45 : sub10 [-2, -1, -3] = true := by decide +kernel
theorem sub10_46 : sub10 [-2, -1, -2] = true := by decide +kernel
theorem sub10_47 : sub10 [-2, -1, -1] = true := by decide +kernel
theorem sub10_48 : sub10 [-2, -1, 0] = true := by decide +kernel
theorem sub10_49 : sub10 [-2, -1, 1] = true := by decide +kernel
theorem sub10_50 : sub10 [-2, -1, 2] = true := by decide +kernel
theorem sub10_51 : sub10 [-2, -1, 3] = true := by decide +kernel
theorem sub10_52 : sub10 [-2, -1, 4] = true := by decide +kernel
theorem sub10_53 : sub10 [-2, -1, 5] = true := by decide +kernel
theorem sub10_54 : sub10 [-2, -1, 6] = true := by decide +kernel
theorem sub10_55 : sub10 [-2, 0, -8] = true := by decide +kernel
theorem sub10_56 : sub10 [-2, 0, -7] = true := by decide +kernel
theorem sub10_57 : sub10 [-2, 0, -6] = true := by decide +kernel
theorem sub10_58 : sub10 [-2, 0, -5] = true := by decide +kernel
theorem sub10_59 : sub10 [-2, 0, -4] = true := by decide +kernel
theorem sub10_60 : sub10 [-2, 0, -3] = true := by decide +kernel
theorem sub10_61 : sub10 [-2, 0, -2] = true := by decide +kernel
theorem sub10_62 : sub10 [-2, 0, -1] = true := by decide +kernel
theorem sub10_63 : sub10 [-2, 0, 0] = true := by decide +kernel
theorem sb10_1 : ∀ q ∈ blk10_1, sub10 q = true := by
  unfold blk10_1
  exact List.forall_mem_cons.2 ⟨sub10_32, List.forall_mem_cons.2 ⟨sub10_33, List.forall_mem_cons.2 ⟨sub10_34, List.forall_mem_cons.2 ⟨sub10_35, List.forall_mem_cons.2 ⟨sub10_36, List.forall_mem_cons.2 ⟨sub10_37, List.forall_mem_cons.2 ⟨sub10_38, List.forall_mem_cons.2 ⟨sub10_39, List.forall_mem_cons.2 ⟨sub10_40, List.forall_mem_cons.2 ⟨sub10_41, List.forall_mem_cons.2 ⟨sub10_42, List.forall_mem_cons.2 ⟨sub10_43, List.forall_mem_cons.2 ⟨sub10_44, List.forall_mem_cons.2 ⟨sub10_45, List.forall_mem_cons.2 ⟨sub10_46, List.forall_mem_cons.2 ⟨sub10_47, List.forall_mem_cons.2 ⟨sub10_48, List.forall_mem_cons.2 ⟨sub10_49, List.forall_mem_cons.2 ⟨sub10_50, List.forall_mem_cons.2 ⟨sub10_51, List.forall_mem_cons.2 ⟨sub10_52, List.forall_mem_cons.2 ⟨sub10_53, List.forall_mem_cons.2 ⟨sub10_54, List.forall_mem_cons.2 ⟨sub10_55, List.forall_mem_cons.2 ⟨sub10_56, List.forall_mem_cons.2 ⟨sub10_57, List.forall_mem_cons.2 ⟨sub10_58, List.forall_mem_cons.2 ⟨sub10_59, List.forall_mem_cons.2 ⟨sub10_60, List.forall_mem_cons.2 ⟨sub10_61, List.forall_mem_cons.2 ⟨sub10_62, List.forall_mem_cons.2 ⟨sub10_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_64 : sub10 [-2, 0, 1] = true := by decide +kernel
theorem sub10_65 : sub10 [-2, 0, 2] = true := by decide +kernel
theorem sub10_66 : sub10 [-2, 0, 3] = true := by decide +kernel
theorem sub10_67 : sub10 [-2, 0, 4] = true := by decide +kernel
theorem sub10_68 : sub10 [-2, 0, 5] = true := by decide +kernel
theorem sub10_69 : sub10 [-2, 0, 6] = true := by decide +kernel
theorem sub10_70 : sub10 [-2, 1] = true := by decide +kernel
theorem sub10_71 : sub10 [-2, 2] = true := by decide +kernel
theorem sub10_72 : sub10 [-2, 3] = true := by decide +kernel
theorem sub10_73 : sub10 [-2, 4] = true := by decide +kernel
theorem sub10_74 : sub10 [-1, -7] = true := by decide +kernel
theorem sub10_75 : sub10 [-1, -6] = true := by decide +kernel
theorem sub10_76 : sub10 [-1, -5] = true := by decide +kernel
theorem sub10_77 : sub10 [-1, -4] = true := by decide +kernel
theorem sub10_78 : sub10 [-1, -3, -7] = true := by decide +kernel
theorem sub10_79 : sub10 [-1, -3, -6] = true := by decide +kernel
theorem sub10_80 : sub10 [-1, -3, -5] = true := by decide +kernel
theorem sub10_81 : sub10 [-1, -3, -4] = true := by decide +kernel
theorem sub10_82 : sub10 [-1, -3, -3] = true := by decide +kernel
theorem sub10_83 : sub10 [-1, -3, -2] = true := by decide +kernel
theorem sub10_84 : sub10 [-1, -3, -1] = true := by decide +kernel
theorem sub10_85 : sub10 [-1, -3, 0] = true := by decide +kernel
theorem sub10_86 : sub10 [-1, -3, 1] = true := by decide +kernel
theorem sub10_87 : sub10 [-1, -3, 2] = true := by decide +kernel
theorem sub10_88 : sub10 [-1, -3, 3] = true := by decide +kernel
theorem sub10_89 : sub10 [-1, -3, 4] = true := by decide +kernel
theorem sub10_90 : sub10 [-1, -3, 5] = true := by decide +kernel
theorem sub10_91 : sub10 [-1, -3, 6] = true := by decide +kernel
theorem sub10_92 : sub10 [-1, -3, 7] = true := by decide +kernel
theorem sub10_93 : sub10 [-1, -2, -7] = true := by decide +kernel
theorem sub10_94 : sub10 [-1, -2, -6] = true := by decide +kernel
theorem sub10_95 : sub10 [-1, -2, -5] = true := by decide +kernel
theorem sb10_2 : ∀ q ∈ blk10_2, sub10 q = true := by
  unfold blk10_2
  exact List.forall_mem_cons.2 ⟨sub10_64, List.forall_mem_cons.2 ⟨sub10_65, List.forall_mem_cons.2 ⟨sub10_66, List.forall_mem_cons.2 ⟨sub10_67, List.forall_mem_cons.2 ⟨sub10_68, List.forall_mem_cons.2 ⟨sub10_69, List.forall_mem_cons.2 ⟨sub10_70, List.forall_mem_cons.2 ⟨sub10_71, List.forall_mem_cons.2 ⟨sub10_72, List.forall_mem_cons.2 ⟨sub10_73, List.forall_mem_cons.2 ⟨sub10_74, List.forall_mem_cons.2 ⟨sub10_75, List.forall_mem_cons.2 ⟨sub10_76, List.forall_mem_cons.2 ⟨sub10_77, List.forall_mem_cons.2 ⟨sub10_78, List.forall_mem_cons.2 ⟨sub10_79, List.forall_mem_cons.2 ⟨sub10_80, List.forall_mem_cons.2 ⟨sub10_81, List.forall_mem_cons.2 ⟨sub10_82, List.forall_mem_cons.2 ⟨sub10_83, List.forall_mem_cons.2 ⟨sub10_84, List.forall_mem_cons.2 ⟨sub10_85, List.forall_mem_cons.2 ⟨sub10_86, List.forall_mem_cons.2 ⟨sub10_87, List.forall_mem_cons.2 ⟨sub10_88, List.forall_mem_cons.2 ⟨sub10_89, List.forall_mem_cons.2 ⟨sub10_90, List.forall_mem_cons.2 ⟨sub10_91, List.forall_mem_cons.2 ⟨sub10_92, List.forall_mem_cons.2 ⟨sub10_93, List.forall_mem_cons.2 ⟨sub10_94, List.forall_mem_cons.2 ⟨sub10_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C120
