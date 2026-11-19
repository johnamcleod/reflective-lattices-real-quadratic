import ReflectZphi.Data.Cert5.C121.Base

namespace ReflectZphi.Data.Cert5.C121

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd4_2_224 : subd4_2 [-3, 1, -2] = true := by decide +kernel
theorem subd4_2_225 : subd4_2 [-3, 1, -1] = true := by decide +kernel
theorem subd4_2_226 : subd4_2 [-3, 1, 0] = true := by decide +kernel
theorem subd4_2_227 : subd4_2 [-3, 1, 1] = true := by decide +kernel
theorem subd4_2_228 : subd4_2 [-3, 1, 2] = true := by decide +kernel
theorem subd4_2_229 : subd4_2 [-3, 1, 3] = true := by decide +kernel
theorem subd4_2_230 : subd4_2 [-3, 1, 4] = true := by decide +kernel
theorem subd4_2_231 : subd4_2 [-3, 1, 5] = true := by decide +kernel
theorem subd4_2_232 : subd4_2 [-3, 1, 6] = true := by decide +kernel
theorem subd4_2_233 : subd4_2 [-3, 1, 7] = true := by decide +kernel
theorem subd4_2_234 : subd4_2 [-3, 1, 8] = true := by decide +kernel
theorem subd4_2_235 : subd4_2 [-3, 2, -8] = true := by decide +kernel
theorem subd4_2_236 : subd4_2 [-3, 2, -7] = true := by decide +kernel
theorem subd4_2_237 : subd4_2 [-3, 2, -6] = true := by decide +kernel
theorem subd4_2_238 : subd4_2 [-3, 2, -5] = true := by decide +kernel
theorem subd4_2_239 : subd4_2 [-3, 2, -4] = true := by decide +kernel
theorem subd4_2_240 : subd4_2 [-3, 2, -3] = true := by decide +kernel
theorem subd4_2_241 : subd4_2 [-3, 2, -2] = true := by decide +kernel
theorem subd4_2_242 : subd4_2 [-3, 2, -1] = true := by decide +kernel
theorem subd4_2_243 : subd4_2 [-3, 2, 0] = true := by decide +kernel
theorem subd4_2_244 : subd4_2 [-3, 2, 1] = true := by decide +kernel
theorem subd4_2_245 : subd4_2 [-3, 2, 2] = true := by decide +kernel
theorem subd4_2_246 : subd4_2 [-3, 2, 3] = true := by decide +kernel
theorem subd4_2_247 : subd4_2 [-3, 2, 4] = true := by decide +kernel
theorem subd4_2_248 : subd4_2 [-3, 2, 5] = true := by decide +kernel
theorem subd4_2_249 : subd4_2 [-3, 2, 6] = true := by decide +kernel
theorem subd4_2_250 : subd4_2 [-3, 2, 7] = true := by decide +kernel
theorem subd4_2_251 : subd4_2 [-3, 3] = true := by decide +kernel
theorem subd4_2_252 : subd4_2 [-3, 4] = true := by decide +kernel
theorem subd4_2_253 : subd4_2 [-3, 5] = true := by decide +kernel
theorem subd4_2_254 : subd4_2 [-2, -8] = true := by decide +kernel
theorem subd4_2_255 : subd4_2 [-2, -7] = true := by decide +kernel
theorem sbd4_2_7 : ∀ q ∈ blkd4_2_7, subd4_2 q = true := by
  unfold blkd4_2_7
  exact List.forall_mem_cons.2 ⟨subd4_2_224, List.forall_mem_cons.2 ⟨subd4_2_225, List.forall_mem_cons.2 ⟨subd4_2_226, List.forall_mem_cons.2 ⟨subd4_2_227, List.forall_mem_cons.2 ⟨subd4_2_228, List.forall_mem_cons.2 ⟨subd4_2_229, List.forall_mem_cons.2 ⟨subd4_2_230, List.forall_mem_cons.2 ⟨subd4_2_231, List.forall_mem_cons.2 ⟨subd4_2_232, List.forall_mem_cons.2 ⟨subd4_2_233, List.forall_mem_cons.2 ⟨subd4_2_234, List.forall_mem_cons.2 ⟨subd4_2_235, List.forall_mem_cons.2 ⟨subd4_2_236, List.forall_mem_cons.2 ⟨subd4_2_237, List.forall_mem_cons.2 ⟨subd4_2_238, List.forall_mem_cons.2 ⟨subd4_2_239, List.forall_mem_cons.2 ⟨subd4_2_240, List.forall_mem_cons.2 ⟨subd4_2_241, List.forall_mem_cons.2 ⟨subd4_2_242, List.forall_mem_cons.2 ⟨subd4_2_243, List.forall_mem_cons.2 ⟨subd4_2_244, List.forall_mem_cons.2 ⟨subd4_2_245, List.forall_mem_cons.2 ⟨subd4_2_246, List.forall_mem_cons.2 ⟨subd4_2_247, List.forall_mem_cons.2 ⟨subd4_2_248, List.forall_mem_cons.2 ⟨subd4_2_249, List.forall_mem_cons.2 ⟨subd4_2_250, List.forall_mem_cons.2 ⟨subd4_2_251, List.forall_mem_cons.2 ⟨subd4_2_252, List.forall_mem_cons.2 ⟨subd4_2_253, List.forall_mem_cons.2 ⟨subd4_2_254, List.forall_mem_cons.2 ⟨subd4_2_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_2_256 : subd4_2 [-2, -6] = true := by decide +kernel
theorem subd4_2_257 : subd4_2 [-2, -5, -9] = true := by decide +kernel
theorem subd4_2_258 : subd4_2 [-2, -5, -8] = true := by decide +kernel
theorem subd4_2_259 : subd4_2 [-2, -5, -7] = true := by decide +kernel
theorem subd4_2_260 : subd4_2 [-2, -5, -6] = true := by decide +kernel
theorem subd4_2_261 : subd4_2 [-2, -5, -5] = true := by decide +kernel
theorem subd4_2_262 : subd4_2 [-2, -5, -4] = true := by decide +kernel
theorem subd4_2_263 : subd4_2 [-2, -5, -3] = true := by decide +kernel
theorem subd4_2_264 : subd4_2 [-2, -5, -2] = true := by decide +kernel
theorem subd4_2_265 : subd4_2 [-2, -5, -1] = true := by decide +kernel
theorem subd4_2_266 : subd4_2 [-2, -5, 0] = true := by decide +kernel
theorem subd4_2_267 : subd4_2 [-2, -5, 1] = true := by decide +kernel
theorem subd4_2_268 : subd4_2 [-2, -5, 2] = true := by decide +kernel
theorem subd4_2_269 : subd4_2 [-2, -5, 3] = true := by decide +kernel
theorem subd4_2_270 : subd4_2 [-2, -5, 4] = true := by decide +kernel
theorem subd4_2_271 : subd4_2 [-2, -5, 5] = true := by decide +kernel
theorem subd4_2_272 : subd4_2 [-2, -4, -10] = true := by decide +kernel
theorem subd4_2_273 : subd4_2 [-2, -4, -9] = true := by decide +kernel
theorem subd4_2_274 : subd4_2 [-2, -4, -8] = true := by decide +kernel
theorem subd4_2_275 : subd4_2 [-2, -4, -7] = true := by decide +kernel
theorem subd4_2_276 : subd4_2 [-2, -4, -6] = true := by decide +kernel
theorem subd4_2_277 : subd4_2 [-2, -4, -5] = true := by decide +kernel
theorem subd4_2_278 : subd4_2 [-2, -4, -4] = true := by decide +kernel
theorem subd4_2_279 : subd4_2 [-2, -4, -3] = true := by decide +kernel
theorem subd4_2_280 : subd4_2 [-2, -4, -2] = true := by decide +kernel
theorem subd4_2_281 : subd4_2 [-2, -4, -1] = true := by decide +kernel
theorem subd4_2_282 : subd4_2 [-2, -4, 0] = true := by decide +kernel
theorem subd4_2_283 : subd4_2 [-2, -4, 1] = true := by decide +kernel
theorem subd4_2_284 : subd4_2 [-2, -4, 2] = true := by decide +kernel
theorem subd4_2_285 : subd4_2 [-2, -4, 3] = true := by decide +kernel
theorem subd4_2_286 : subd4_2 [-2, -4, 4] = true := by decide +kernel
theorem subd4_2_287 : subd4_2 [-2, -4, 5] = true := by decide +kernel
theorem sbd4_2_8 : ∀ q ∈ blkd4_2_8, subd4_2 q = true := by
  unfold blkd4_2_8
  exact List.forall_mem_cons.2 ⟨subd4_2_256, List.forall_mem_cons.2 ⟨subd4_2_257, List.forall_mem_cons.2 ⟨subd4_2_258, List.forall_mem_cons.2 ⟨subd4_2_259, List.forall_mem_cons.2 ⟨subd4_2_260, List.forall_mem_cons.2 ⟨subd4_2_261, List.forall_mem_cons.2 ⟨subd4_2_262, List.forall_mem_cons.2 ⟨subd4_2_263, List.forall_mem_cons.2 ⟨subd4_2_264, List.forall_mem_cons.2 ⟨subd4_2_265, List.forall_mem_cons.2 ⟨subd4_2_266, List.forall_mem_cons.2 ⟨subd4_2_267, List.forall_mem_cons.2 ⟨subd4_2_268, List.forall_mem_cons.2 ⟨subd4_2_269, List.forall_mem_cons.2 ⟨subd4_2_270, List.forall_mem_cons.2 ⟨subd4_2_271, List.forall_mem_cons.2 ⟨subd4_2_272, List.forall_mem_cons.2 ⟨subd4_2_273, List.forall_mem_cons.2 ⟨subd4_2_274, List.forall_mem_cons.2 ⟨subd4_2_275, List.forall_mem_cons.2 ⟨subd4_2_276, List.forall_mem_cons.2 ⟨subd4_2_277, List.forall_mem_cons.2 ⟨subd4_2_278, List.forall_mem_cons.2 ⟨subd4_2_279, List.forall_mem_cons.2 ⟨subd4_2_280, List.forall_mem_cons.2 ⟨subd4_2_281, List.forall_mem_cons.2 ⟨subd4_2_282, List.forall_mem_cons.2 ⟨subd4_2_283, List.forall_mem_cons.2 ⟨subd4_2_284, List.forall_mem_cons.2 ⟨subd4_2_285, List.forall_mem_cons.2 ⟨subd4_2_286, List.forall_mem_cons.2 ⟨subd4_2_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_2_288 : subd4_2 [-2, -4, 6] = true := by decide +kernel
theorem subd4_2_289 : subd4_2 [-2, -4, 7] = true := by decide +kernel
theorem subd4_2_290 : subd4_2 [-2, -3, -10] = true := by decide +kernel
theorem subd4_2_291 : subd4_2 [-2, -3, -9] = true := by decide +kernel
theorem subd4_2_292 : subd4_2 [-2, -3, -8] = true := by decide +kernel
theorem subd4_2_293 : subd4_2 [-2, -3, -7] = true := by decide +kernel
theorem subd4_2_294 : subd4_2 [-2, -3, -6] = true := by decide +kernel
theorem subd4_2_295 : subd4_2 [-2, -3, -5] = true := by decide +kernel
theorem subd4_2_296 : subd4_2 [-2, -3, -4] = true := by decide +kernel
theorem subd4_2_297 : subd4_2 [-2, -3, -3] = true := by decide +kernel
theorem subd4_2_298 : subd4_2 [-2, -3, -2] = true := by decide +kernel
theorem subd4_2_299 : subd4_2 [-2, -3, -1] = true := by decide +kernel
theorem subd4_2_300 : subd4_2 [-2, -3, 0] = true := by decide +kernel
theorem subd4_2_301 : subd4_2 [-2, -3, 1] = true := by decide +kernel
theorem subd4_2_302 : subd4_2 [-2, -3, 2] = true := by decide +kernel
theorem subd4_2_303 : subd4_2 [-2, -3, 3] = true := by decide +kernel
theorem subd4_2_304 : subd4_2 [-2, -3, 4] = true := by decide +kernel
theorem subd4_2_305 : subd4_2 [-2, -3, 5] = true := by decide +kernel
theorem subd4_2_306 : subd4_2 [-2, -3, 6] = true := by decide +kernel
theorem subd4_2_307 : subd4_2 [-2, -3, 7] = true := by decide +kernel
theorem subd4_2_308 : subd4_2 [-2, -2, -10] = true := by decide +kernel
theorem subd4_2_309 : subd4_2 [-2, -2, -9] = true := by decide +kernel
theorem subd4_2_310 : subd4_2 [-2, -2, -8] = true := by decide +kernel
theorem subd4_2_311 : subd4_2 [-2, -2, -7] = true := by decide +kernel
theorem subd4_2_312 : subd4_2 [-2, -2, -6] = true := by decide +kernel
theorem subd4_2_313 : subd4_2 [-2, -2, -5] = true := by decide +kernel
theorem subd4_2_314 : subd4_2 [-2, -2, -4] = true := by decide +kernel
theorem subd4_2_315 : subd4_2 [-2, -2, -3] = true := by decide +kernel
theorem subd4_2_316 : subd4_2 [-2, -2, -2] = true := by decide +kernel
theorem subd4_2_317 : subd4_2 [-2, -2, -1] = true := by decide +kernel
theorem subd4_2_318 : subd4_2 [-2, -2, 0] = true := by decide +kernel
theorem subd4_2_319 : subd4_2 [-2, -2, 1] = true := by decide +kernel
theorem sbd4_2_9 : ∀ q ∈ blkd4_2_9, subd4_2 q = true := by
  unfold blkd4_2_9
  exact List.forall_mem_cons.2 ⟨subd4_2_288, List.forall_mem_cons.2 ⟨subd4_2_289, List.forall_mem_cons.2 ⟨subd4_2_290, List.forall_mem_cons.2 ⟨subd4_2_291, List.forall_mem_cons.2 ⟨subd4_2_292, List.forall_mem_cons.2 ⟨subd4_2_293, List.forall_mem_cons.2 ⟨subd4_2_294, List.forall_mem_cons.2 ⟨subd4_2_295, List.forall_mem_cons.2 ⟨subd4_2_296, List.forall_mem_cons.2 ⟨subd4_2_297, List.forall_mem_cons.2 ⟨subd4_2_298, List.forall_mem_cons.2 ⟨subd4_2_299, List.forall_mem_cons.2 ⟨subd4_2_300, List.forall_mem_cons.2 ⟨subd4_2_301, List.forall_mem_cons.2 ⟨subd4_2_302, List.forall_mem_cons.2 ⟨subd4_2_303, List.forall_mem_cons.2 ⟨subd4_2_304, List.forall_mem_cons.2 ⟨subd4_2_305, List.forall_mem_cons.2 ⟨subd4_2_306, List.forall_mem_cons.2 ⟨subd4_2_307, List.forall_mem_cons.2 ⟨subd4_2_308, List.forall_mem_cons.2 ⟨subd4_2_309, List.forall_mem_cons.2 ⟨subd4_2_310, List.forall_mem_cons.2 ⟨subd4_2_311, List.forall_mem_cons.2 ⟨subd4_2_312, List.forall_mem_cons.2 ⟨subd4_2_313, List.forall_mem_cons.2 ⟨subd4_2_314, List.forall_mem_cons.2 ⟨subd4_2_315, List.forall_mem_cons.2 ⟨subd4_2_316, List.forall_mem_cons.2 ⟨subd4_2_317, List.forall_mem_cons.2 ⟨subd4_2_318, List.forall_mem_cons.2 ⟨subd4_2_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_2_320 : subd4_2 [-2, -2, 2] = true := by decide +kernel
theorem subd4_2_321 : subd4_2 [-2, -2, 3] = true := by decide +kernel
theorem subd4_2_322 : subd4_2 [-2, -2, 4] = true := by decide +kernel
theorem subd4_2_323 : subd4_2 [-2, -2, 5] = true := by decide +kernel
theorem subd4_2_324 : subd4_2 [-2, -2, 6] = true := by decide +kernel
theorem subd4_2_325 : subd4_2 [-2, -2, 7] = true := by decide +kernel
theorem subd4_2_326 : subd4_2 [-2, -2, 8] = true := by decide +kernel
theorem subd4_2_327 : subd4_2 [-2, -1, -10] = true := by decide +kernel
theorem subd4_2_328 : subd4_2 [-2, -1, -9] = true := by decide +kernel
theorem subd4_2_329 : subd4_2 [-2, -1, -8] = true := by decide +kernel
theorem subd4_2_330 : subd4_2 [-2, -1, -7] = true := by decide +kernel
theorem subd4_2_331 : subd4_2 [-2, -1, -6] = true := by decide +kernel
theorem subd4_2_332 : subd4_2 [-2, -1, -5] = true := by decide +kernel
theorem subd4_2_333 : subd4_2 [-2, -1, -4] = true := by decide +kernel
theorem subd4_2_334 : subd4_2 [-2, -1, -3] = true := by decide +kernel
theorem subd4_2_335 : subd4_2 [-2, -1, -2] = true := by decide +kernel
theorem subd4_2_336 : subd4_2 [-2, -1, -1] = true := by decide +kernel
theorem subd4_2_337 : subd4_2 [-2, -1, 0] = true := by decide +kernel
theorem subd4_2_338 : subd4_2 [-2, -1, 1] = true := by decide +kernel
theorem subd4_2_339 : subd4_2 [-2, -1, 2] = true := by decide +kernel
theorem subd4_2_340 : subd4_2 [-2, -1, 3] = true := by decide +kernel
theorem subd4_2_341 : subd4_2 [-2, -1, 4] = true := by decide +kernel
theorem subd4_2_342 : subd4_2 [-2, -1, 5] = true := by decide +kernel
theorem subd4_2_343 : subd4_2 [-2, -1, 6] = true := by decide +kernel
theorem subd4_2_344 : subd4_2 [-2, -1, 7] = true := by decide +kernel
theorem subd4_2_345 : subd4_2 [-2, -1, 8] = true := by decide +kernel
theorem subd4_2_346 : subd4_2 [-2, 0, -10] = true := by decide +kernel
theorem subd4_2_347 : subd4_2 [-2, 0, -9] = true := by decide +kernel
theorem subd4_2_348 : subd4_2 [-2, 0, -8] = true := by decide +kernel
theorem subd4_2_349 : subd4_2 [-2, 0, -7] = true := by decide +kernel
theorem subd4_2_350 : subd4_2 [-2, 0, -6] = true := by decide +kernel
theorem subd4_2_351 : subd4_2 [-2, 0, -5] = true := by decide +kernel
theorem sbd4_2_10 : ∀ q ∈ blkd4_2_10, subd4_2 q = true := by
  unfold blkd4_2_10
  exact List.forall_mem_cons.2 ⟨subd4_2_320, List.forall_mem_cons.2 ⟨subd4_2_321, List.forall_mem_cons.2 ⟨subd4_2_322, List.forall_mem_cons.2 ⟨subd4_2_323, List.forall_mem_cons.2 ⟨subd4_2_324, List.forall_mem_cons.2 ⟨subd4_2_325, List.forall_mem_cons.2 ⟨subd4_2_326, List.forall_mem_cons.2 ⟨subd4_2_327, List.forall_mem_cons.2 ⟨subd4_2_328, List.forall_mem_cons.2 ⟨subd4_2_329, List.forall_mem_cons.2 ⟨subd4_2_330, List.forall_mem_cons.2 ⟨subd4_2_331, List.forall_mem_cons.2 ⟨subd4_2_332, List.forall_mem_cons.2 ⟨subd4_2_333, List.forall_mem_cons.2 ⟨subd4_2_334, List.forall_mem_cons.2 ⟨subd4_2_335, List.forall_mem_cons.2 ⟨subd4_2_336, List.forall_mem_cons.2 ⟨subd4_2_337, List.forall_mem_cons.2 ⟨subd4_2_338, List.forall_mem_cons.2 ⟨subd4_2_339, List.forall_mem_cons.2 ⟨subd4_2_340, List.forall_mem_cons.2 ⟨subd4_2_341, List.forall_mem_cons.2 ⟨subd4_2_342, List.forall_mem_cons.2 ⟨subd4_2_343, List.forall_mem_cons.2 ⟨subd4_2_344, List.forall_mem_cons.2 ⟨subd4_2_345, List.forall_mem_cons.2 ⟨subd4_2_346, List.forall_mem_cons.2 ⟨subd4_2_347, List.forall_mem_cons.2 ⟨subd4_2_348, List.forall_mem_cons.2 ⟨subd4_2_349, List.forall_mem_cons.2 ⟨subd4_2_350, List.forall_mem_cons.2 ⟨subd4_2_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_2_352 : subd4_2 [-2, 0, -4] = true := by decide +kernel
theorem subd4_2_353 : subd4_2 [-2, 0, -3] = true := by decide +kernel
theorem subd4_2_354 : subd4_2 [-2, 0, -2] = true := by decide +kernel
theorem subd4_2_355 : subd4_2 [-2, 0, -1] = true := by decide +kernel
theorem subd4_2_356 : subd4_2 [-2, 0, 0] = true := by decide +kernel
theorem subd4_2_357 : subd4_2 [-2, 0, 1] = true := by decide +kernel
theorem subd4_2_358 : subd4_2 [-2, 0, 2] = true := by decide +kernel
theorem subd4_2_359 : subd4_2 [-2, 0, 3] = true := by decide +kernel
theorem subd4_2_360 : subd4_2 [-2, 0, 4] = true := by decide +kernel
theorem subd4_2_361 : subd4_2 [-2, 0, 5] = true := by decide +kernel
theorem subd4_2_362 : subd4_2 [-2, 0, 6] = true := by decide +kernel
theorem subd4_2_363 : subd4_2 [-2, 0, 7] = true := by decide +kernel
theorem subd4_2_364 : subd4_2 [-2, 0, 8] = true := by decide +kernel
theorem subd4_2_365 : subd4_2 [-2, 0, 9] = true := by decide +kernel
theorem subd4_2_366 : subd4_2 [-2, 1, -9] = true := by decide +kernel
theorem subd4_2_367 : subd4_2 [-2, 1, -8] = true := by decide +kernel
theorem subd4_2_368 : subd4_2 [-2, 1, -7] = true := by decide +kernel
theorem subd4_2_369 : subd4_2 [-2, 1, -6] = true := by decide +kernel
theorem subd4_2_370 : subd4_2 [-2, 1, -5] = true := by decide +kernel
theorem subd4_2_371 : subd4_2 [-2, 1, -4] = true := by decide +kernel
theorem subd4_2_372 : subd4_2 [-2, 1, -3] = true := by decide +kernel
theorem subd4_2_373 : subd4_2 [-2, 1, -2] = true := by decide +kernel
theorem subd4_2_374 : subd4_2 [-2, 1, -1] = true := by decide +kernel
theorem subd4_2_375 : subd4_2 [-2, 1, 0] = true := by decide +kernel
theorem subd4_2_376 : subd4_2 [-2, 1, 1] = true := by decide +kernel
theorem subd4_2_377 : subd4_2 [-2, 1, 2] = true := by decide +kernel
theorem subd4_2_378 : subd4_2 [-2, 1, 3] = true := by decide +kernel
theorem subd4_2_379 : subd4_2 [-2, 1, 4] = true := by decide +kernel
theorem subd4_2_380 : subd4_2 [-2, 1, 5] = true := by decide +kernel
theorem subd4_2_381 : subd4_2 [-2, 1, 6] = true := by decide +kernel
theorem subd4_2_382 : subd4_2 [-2, 1, 7] = true := by decide +kernel
theorem subd4_2_383 : subd4_2 [-2, 1, 8] = true := by decide +kernel
theorem sbd4_2_11 : ∀ q ∈ blkd4_2_11, subd4_2 q = true := by
  unfold blkd4_2_11
  exact List.forall_mem_cons.2 ⟨subd4_2_352, List.forall_mem_cons.2 ⟨subd4_2_353, List.forall_mem_cons.2 ⟨subd4_2_354, List.forall_mem_cons.2 ⟨subd4_2_355, List.forall_mem_cons.2 ⟨subd4_2_356, List.forall_mem_cons.2 ⟨subd4_2_357, List.forall_mem_cons.2 ⟨subd4_2_358, List.forall_mem_cons.2 ⟨subd4_2_359, List.forall_mem_cons.2 ⟨subd4_2_360, List.forall_mem_cons.2 ⟨subd4_2_361, List.forall_mem_cons.2 ⟨subd4_2_362, List.forall_mem_cons.2 ⟨subd4_2_363, List.forall_mem_cons.2 ⟨subd4_2_364, List.forall_mem_cons.2 ⟨subd4_2_365, List.forall_mem_cons.2 ⟨subd4_2_366, List.forall_mem_cons.2 ⟨subd4_2_367, List.forall_mem_cons.2 ⟨subd4_2_368, List.forall_mem_cons.2 ⟨subd4_2_369, List.forall_mem_cons.2 ⟨subd4_2_370, List.forall_mem_cons.2 ⟨subd4_2_371, List.forall_mem_cons.2 ⟨subd4_2_372, List.forall_mem_cons.2 ⟨subd4_2_373, List.forall_mem_cons.2 ⟨subd4_2_374, List.forall_mem_cons.2 ⟨subd4_2_375, List.forall_mem_cons.2 ⟨subd4_2_376, List.forall_mem_cons.2 ⟨subd4_2_377, List.forall_mem_cons.2 ⟨subd4_2_378, List.forall_mem_cons.2 ⟨subd4_2_379, List.forall_mem_cons.2 ⟨subd4_2_380, List.forall_mem_cons.2 ⟨subd4_2_381, List.forall_mem_cons.2 ⟨subd4_2_382, List.forall_mem_cons.2 ⟨subd4_2_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_2_384 : subd4_2 [-2, 1, 9] = true := by decide +kernel
theorem subd4_2_385 : subd4_2 [-2, 2, -9] = true := by decide +kernel
theorem subd4_2_386 : subd4_2 [-2, 2, -8] = true := by decide +kernel
theorem subd4_2_387 : subd4_2 [-2, 2, -7] = true := by decide +kernel
theorem subd4_2_388 : subd4_2 [-2, 2, -6] = true := by decide +kernel
theorem subd4_2_389 : subd4_2 [-2, 2, -5] = true := by decide +kernel
theorem subd4_2_390 : subd4_2 [-2, 2, -4] = true := by decide +kernel
theorem subd4_2_391 : subd4_2 [-2, 2, -3] = true := by decide +kernel
theorem subd4_2_392 : subd4_2 [-2, 2, -2] = true := by decide +kernel
theorem subd4_2_393 : subd4_2 [-2, 2, -1] = true := by decide +kernel
theorem subd4_2_394 : subd4_2 [-2, 2, 0] = true := by decide +kernel
theorem subd4_2_395 : subd4_2 [-2, 2, 1] = true := by decide +kernel
theorem subd4_2_396 : subd4_2 [-2, 2, 2] = true := by decide +kernel
theorem subd4_2_397 : subd4_2 [-2, 2, 3] = true := by decide +kernel
theorem subd4_2_398 : subd4_2 [-2, 2, 4] = true := by decide +kernel
theorem subd4_2_399 : subd4_2 [-2, 2, 5] = true := by decide +kernel
theorem subd4_2_400 : subd4_2 [-2, 2, 6] = true := by decide +kernel
theorem subd4_2_401 : subd4_2 [-2, 2, 7] = true := by decide +kernel
theorem subd4_2_402 : subd4_2 [-2, 2, 8] = true := by decide +kernel
theorem subd4_2_403 : subd4_2 [-2, 3, -7] = true := by decide +kernel
theorem subd4_2_404 : subd4_2 [-2, 3, -6] = true := by decide +kernel
theorem subd4_2_405 : subd4_2 [-2, 3, -5] = true := by decide +kernel
theorem subd4_2_406 : subd4_2 [-2, 3, -4] = true := by decide +kernel
theorem subd4_2_407 : subd4_2 [-2, 3, -3] = true := by decide +kernel
theorem subd4_2_408 : subd4_2 [-2, 3, -2] = true := by decide +kernel
theorem subd4_2_409 : subd4_2 [-2, 3, -1] = true := by decide +kernel
theorem subd4_2_410 : subd4_2 [-2, 3, 0] = true := by decide +kernel
theorem subd4_2_411 : subd4_2 [-2, 3, 1] = true := by decide +kernel
theorem subd4_2_412 : subd4_2 [-2, 3, 2] = true := by decide +kernel
theorem subd4_2_413 : subd4_2 [-2, 3, 3] = true := by decide +kernel
theorem subd4_2_414 : subd4_2 [-2, 3, 4] = true := by decide +kernel
theorem subd4_2_415 : subd4_2 [-2, 3, 5] = true := by decide +kernel
theorem sbd4_2_12 : ∀ q ∈ blkd4_2_12, subd4_2 q = true := by
  unfold blkd4_2_12
  exact List.forall_mem_cons.2 ⟨subd4_2_384, List.forall_mem_cons.2 ⟨subd4_2_385, List.forall_mem_cons.2 ⟨subd4_2_386, List.forall_mem_cons.2 ⟨subd4_2_387, List.forall_mem_cons.2 ⟨subd4_2_388, List.forall_mem_cons.2 ⟨subd4_2_389, List.forall_mem_cons.2 ⟨subd4_2_390, List.forall_mem_cons.2 ⟨subd4_2_391, List.forall_mem_cons.2 ⟨subd4_2_392, List.forall_mem_cons.2 ⟨subd4_2_393, List.forall_mem_cons.2 ⟨subd4_2_394, List.forall_mem_cons.2 ⟨subd4_2_395, List.forall_mem_cons.2 ⟨subd4_2_396, List.forall_mem_cons.2 ⟨subd4_2_397, List.forall_mem_cons.2 ⟨subd4_2_398, List.forall_mem_cons.2 ⟨subd4_2_399, List.forall_mem_cons.2 ⟨subd4_2_400, List.forall_mem_cons.2 ⟨subd4_2_401, List.forall_mem_cons.2 ⟨subd4_2_402, List.forall_mem_cons.2 ⟨subd4_2_403, List.forall_mem_cons.2 ⟨subd4_2_404, List.forall_mem_cons.2 ⟨subd4_2_405, List.forall_mem_cons.2 ⟨subd4_2_406, List.forall_mem_cons.2 ⟨subd4_2_407, List.forall_mem_cons.2 ⟨subd4_2_408, List.forall_mem_cons.2 ⟨subd4_2_409, List.forall_mem_cons.2 ⟨subd4_2_410, List.forall_mem_cons.2 ⟨subd4_2_411, List.forall_mem_cons.2 ⟨subd4_2_412, List.forall_mem_cons.2 ⟨subd4_2_413, List.forall_mem_cons.2 ⟨subd4_2_414, List.forall_mem_cons.2 ⟨subd4_2_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_2_416 : subd4_2 [-2, 3, 6] = true := by decide +kernel
theorem subd4_2_417 : subd4_2 [-2, 3, 7] = true := by decide +kernel
theorem subd4_2_418 : subd4_2 [-2, 3, 8] = true := by decide +kernel
theorem subd4_2_419 : subd4_2 [-2, 4, -6] = true := by decide +kernel
theorem subd4_2_420 : subd4_2 [-2, 4, -5] = true := by decide +kernel
theorem subd4_2_421 : subd4_2 [-2, 4, -4] = true := by decide +kernel
theorem subd4_2_422 : subd4_2 [-2, 4, -3] = true := by decide +kernel
theorem subd4_2_423 : subd4_2 [-2, 4, -2] = true := by decide +kernel
theorem subd4_2_424 : subd4_2 [-2, 4, -1] = true := by decide +kernel
theorem subd4_2_425 : subd4_2 [-2, 4, 0] = true := by decide +kernel
theorem subd4_2_426 : subd4_2 [-2, 4, 1] = true := by decide +kernel
theorem subd4_2_427 : subd4_2 [-2, 4, 2] = true := by decide +kernel
theorem subd4_2_428 : subd4_2 [-2, 4, 3] = true := by decide +kernel
theorem subd4_2_429 : subd4_2 [-2, 4, 4] = true := by decide +kernel
theorem subd4_2_430 : subd4_2 [-2, 4, 5] = true := by decide +kernel
theorem subd4_2_431 : subd4_2 [-2, 4, 6] = true := by decide +kernel
theorem subd4_2_432 : subd4_2 [-2, 4, 7] = true := by decide +kernel
theorem subd4_2_433 : subd4_2 [-2, 5] = true := by decide +kernel
theorem subd4_2_434 : subd4_2 [-1, -8] = true := by decide +kernel
theorem subd4_2_435 : subd4_2 [-1, -7] = true := by decide +kernel
theorem subd4_2_436 : subd4_2 [-1, -6] = true := by decide +kernel
theorem subd4_2_437 : subd4_2 [-1, -5, -9] = true := by decide +kernel
theorem subd4_2_438 : subd4_2 [-1, -5, -8] = true := by decide +kernel
theorem subd4_2_439 : subd4_2 [-1, -5, -7] = true := by decide +kernel
theorem subd4_2_440 : subd4_2 [-1, -5, -6] = true := by decide +kernel
theorem subd4_2_441 : subd4_2 [-1, -5, -5] = true := by decide +kernel
theorem subd4_2_442 : subd4_2 [-1, -5, -4] = true := by decide +kernel
theorem subd4_2_443 : subd4_2 [-1, -5, -3] = true := by decide +kernel
theorem subd4_2_444 : subd4_2 [-1, -5, -2] = true := by decide +kernel
theorem subd4_2_445 : subd4_2 [-1, -5, -1] = true := by decide +kernel
theorem subd4_2_446 : subd4_2 [-1, -5, 0] = true := by decide +kernel
theorem subd4_2_447 : subd4_2 [-1, -5, 1] = true := by decide +kernel
theorem sbd4_2_13 : ∀ q ∈ blkd4_2_13, subd4_2 q = true := by
  unfold blkd4_2_13
  exact List.forall_mem_cons.2 ⟨subd4_2_416, List.forall_mem_cons.2 ⟨subd4_2_417, List.forall_mem_cons.2 ⟨subd4_2_418, List.forall_mem_cons.2 ⟨subd4_2_419, List.forall_mem_cons.2 ⟨subd4_2_420, List.forall_mem_cons.2 ⟨subd4_2_421, List.forall_mem_cons.2 ⟨subd4_2_422, List.forall_mem_cons.2 ⟨subd4_2_423, List.forall_mem_cons.2 ⟨subd4_2_424, List.forall_mem_cons.2 ⟨subd4_2_425, List.forall_mem_cons.2 ⟨subd4_2_426, List.forall_mem_cons.2 ⟨subd4_2_427, List.forall_mem_cons.2 ⟨subd4_2_428, List.forall_mem_cons.2 ⟨subd4_2_429, List.forall_mem_cons.2 ⟨subd4_2_430, List.forall_mem_cons.2 ⟨subd4_2_431, List.forall_mem_cons.2 ⟨subd4_2_432, List.forall_mem_cons.2 ⟨subd4_2_433, List.forall_mem_cons.2 ⟨subd4_2_434, List.forall_mem_cons.2 ⟨subd4_2_435, List.forall_mem_cons.2 ⟨subd4_2_436, List.forall_mem_cons.2 ⟨subd4_2_437, List.forall_mem_cons.2 ⟨subd4_2_438, List.forall_mem_cons.2 ⟨subd4_2_439, List.forall_mem_cons.2 ⟨subd4_2_440, List.forall_mem_cons.2 ⟨subd4_2_441, List.forall_mem_cons.2 ⟨subd4_2_442, List.forall_mem_cons.2 ⟨subd4_2_443, List.forall_mem_cons.2 ⟨subd4_2_444, List.forall_mem_cons.2 ⟨subd4_2_445, List.forall_mem_cons.2 ⟨subd4_2_446, List.forall_mem_cons.2 ⟨subd4_2_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_2_448 : subd4_2 [-1, -5, 2] = true := by decide +kernel
theorem subd4_2_449 : subd4_2 [-1, -5, 3] = true := by decide +kernel
theorem subd4_2_450 : subd4_2 [-1, -5, 4] = true := by decide +kernel
theorem subd4_2_451 : subd4_2 [-1, -5, 5] = true := by decide +kernel
theorem subd4_2_452 : subd4_2 [-1, -4, -10] = true := by decide +kernel
theorem subd4_2_453 : subd4_2 [-1, -4, -9] = true := by decide +kernel
theorem subd4_2_454 : subd4_2 [-1, -4, -8] = true := by decide +kernel
theorem subd4_2_455 : subd4_2 [-1, -4, -7] = true := by decide +kernel
theorem subd4_2_456 : subd4_2 [-1, -4, -6] = true := by decide +kernel
theorem subd4_2_457 : subd4_2 [-1, -4, -5] = true := by decide +kernel
theorem subd4_2_458 : subd4_2 [-1, -4, -4] = true := by decide +kernel
theorem subd4_2_459 : subd4_2 [-1, -4, -3] = true := by decide +kernel
theorem subd4_2_460 : subd4_2 [-1, -4, -2] = true := by decide +kernel
theorem subd4_2_461 : subd4_2 [-1, -4, -1] = true := by decide +kernel
theorem subd4_2_462 : subd4_2 [-1, -4, 0] = true := by decide +kernel
theorem subd4_2_463 : subd4_2 [-1, -4, 1] = true := by decide +kernel
theorem subd4_2_464 : subd4_2 [-1, -4, 2] = true := by decide +kernel
theorem subd4_2_465 : subd4_2 [-1, -4, 3] = true := by decide +kernel
theorem subd4_2_466 : subd4_2 [-1, -4, 4] = true := by decide +kernel
theorem subd4_2_467 : subd4_2 [-1, -4, 5] = true := by decide +kernel
theorem subd4_2_468 : subd4_2 [-1, -4, 6] = true := by decide +kernel
theorem subd4_2_469 : subd4_2 [-1, -4, 7] = true := by decide +kernel
theorem subd4_2_470 : subd4_2 [-1, -3, -10] = true := by decide +kernel
theorem subd4_2_471 : subd4_2 [-1, -3, -9] = true := by decide +kernel
theorem subd4_2_472 : subd4_2 [-1, -3, -8] = true := by decide +kernel
theorem subd4_2_473 : subd4_2 [-1, -3, -7] = true := by decide +kernel
theorem subd4_2_474 : subd4_2 [-1, -3, -6] = true := by decide +kernel
theorem subd4_2_475 : subd4_2 [-1, -3, -5] = true := by decide +kernel
theorem subd4_2_476 : subd4_2 [-1, -3, -4] = true := by decide +kernel
theorem subd4_2_477 : subd4_2 [-1, -3, -3] = true := by decide +kernel
theorem subd4_2_478 : subd4_2 [-1, -3, -2] = true := by decide +kernel
theorem subd4_2_479 : subd4_2 [-1, -3, -1] = true := by decide +kernel
theorem sbd4_2_14 : ∀ q ∈ blkd4_2_14, subd4_2 q = true := by
  unfold blkd4_2_14
  exact List.forall_mem_cons.2 ⟨subd4_2_448, List.forall_mem_cons.2 ⟨subd4_2_449, List.forall_mem_cons.2 ⟨subd4_2_450, List.forall_mem_cons.2 ⟨subd4_2_451, List.forall_mem_cons.2 ⟨subd4_2_452, List.forall_mem_cons.2 ⟨subd4_2_453, List.forall_mem_cons.2 ⟨subd4_2_454, List.forall_mem_cons.2 ⟨subd4_2_455, List.forall_mem_cons.2 ⟨subd4_2_456, List.forall_mem_cons.2 ⟨subd4_2_457, List.forall_mem_cons.2 ⟨subd4_2_458, List.forall_mem_cons.2 ⟨subd4_2_459, List.forall_mem_cons.2 ⟨subd4_2_460, List.forall_mem_cons.2 ⟨subd4_2_461, List.forall_mem_cons.2 ⟨subd4_2_462, List.forall_mem_cons.2 ⟨subd4_2_463, List.forall_mem_cons.2 ⟨subd4_2_464, List.forall_mem_cons.2 ⟨subd4_2_465, List.forall_mem_cons.2 ⟨subd4_2_466, List.forall_mem_cons.2 ⟨subd4_2_467, List.forall_mem_cons.2 ⟨subd4_2_468, List.forall_mem_cons.2 ⟨subd4_2_469, List.forall_mem_cons.2 ⟨subd4_2_470, List.forall_mem_cons.2 ⟨subd4_2_471, List.forall_mem_cons.2 ⟨subd4_2_472, List.forall_mem_cons.2 ⟨subd4_2_473, List.forall_mem_cons.2 ⟨subd4_2_474, List.forall_mem_cons.2 ⟨subd4_2_475, List.forall_mem_cons.2 ⟨subd4_2_476, List.forall_mem_cons.2 ⟨subd4_2_477, List.forall_mem_cons.2 ⟨subd4_2_478, List.forall_mem_cons.2 ⟨subd4_2_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_2_480 : subd4_2 [-1, -3, 0] = true := by decide +kernel
theorem subd4_2_481 : subd4_2 [-1, -3, 1] = true := by decide +kernel
theorem subd4_2_482 : subd4_2 [-1, -3, 2] = true := by decide +kernel
theorem subd4_2_483 : subd4_2 [-1, -3, 3] = true := by decide +kernel
theorem subd4_2_484 : subd4_2 [-1, -3, 4] = true := by decide +kernel
theorem subd4_2_485 : subd4_2 [-1, -3, 5] = true := by decide +kernel
theorem subd4_2_486 : subd4_2 [-1, -3, 6] = true := by decide +kernel
theorem subd4_2_487 : subd4_2 [-1, -3, 7] = true := by decide +kernel
theorem subd4_2_488 : subd4_2 [-1, -3, 8] = true := by decide +kernel
theorem subd4_2_489 : subd4_2 [-1, -2, -10] = true := by decide +kernel
theorem subd4_2_490 : subd4_2 [-1, -2, -9] = true := by decide +kernel
theorem subd4_2_491 : subd4_2 [-1, -2, -8] = true := by decide +kernel
theorem subd4_2_492 : subd4_2 [-1, -2, -7] = true := by decide +kernel
theorem subd4_2_493 : subd4_2 [-1, -2, -6] = true := by decide +kernel
theorem subd4_2_494 : subd4_2 [-1, -2, -5] = true := by decide +kernel
theorem subd4_2_495 : subd4_2 [-1, -2, -4] = true := by decide +kernel
theorem subd4_2_496 : subd4_2 [-1, -2, -3] = true := by decide +kernel
theorem subd4_2_497 : subd4_2 [-1, -2, -2] = true := by decide +kernel
theorem subd4_2_498 : subd4_2 [-1, -2, -1] = true := by decide +kernel
theorem subd4_2_499 : subd4_2 [-1, -2, 0] = true := by decide +kernel
theorem subd4_2_500 : subd4_2 [-1, -2, 1] = true := by decide +kernel
theorem subd4_2_501 : subd4_2 [-1, -2, 2] = true := by decide +kernel
theorem subd4_2_502 : subd4_2 [-1, -2, 3] = true := by decide +kernel
theorem subd4_2_503 : subd4_2 [-1, -2, 4] = true := by decide +kernel
theorem subd4_2_504 : subd4_2 [-1, -2, 5] = true := by decide +kernel
theorem subd4_2_505 : subd4_2 [-1, -2, 6] = true := by decide +kernel
theorem subd4_2_506 : subd4_2 [-1, -2, 7] = true := by decide +kernel
theorem subd4_2_507 : subd4_2 [-1, -2, 8] = true := by decide +kernel
theorem subd4_2_508 : subd4_2 [-1, -1, -10] = true := by decide +kernel
theorem subd4_2_509 : subd4_2 [-1, -1, -9] = true := by decide +kernel
theorem subd4_2_510 : subd4_2 [-1, -1, -8] = true := by decide +kernel
theorem subd4_2_511 : subd4_2 [-1, -1, -7] = true := by decide +kernel
theorem sbd4_2_15 : ∀ q ∈ blkd4_2_15, subd4_2 q = true := by
  unfold blkd4_2_15
  exact List.forall_mem_cons.2 ⟨subd4_2_480, List.forall_mem_cons.2 ⟨subd4_2_481, List.forall_mem_cons.2 ⟨subd4_2_482, List.forall_mem_cons.2 ⟨subd4_2_483, List.forall_mem_cons.2 ⟨subd4_2_484, List.forall_mem_cons.2 ⟨subd4_2_485, List.forall_mem_cons.2 ⟨subd4_2_486, List.forall_mem_cons.2 ⟨subd4_2_487, List.forall_mem_cons.2 ⟨subd4_2_488, List.forall_mem_cons.2 ⟨subd4_2_489, List.forall_mem_cons.2 ⟨subd4_2_490, List.forall_mem_cons.2 ⟨subd4_2_491, List.forall_mem_cons.2 ⟨subd4_2_492, List.forall_mem_cons.2 ⟨subd4_2_493, List.forall_mem_cons.2 ⟨subd4_2_494, List.forall_mem_cons.2 ⟨subd4_2_495, List.forall_mem_cons.2 ⟨subd4_2_496, List.forall_mem_cons.2 ⟨subd4_2_497, List.forall_mem_cons.2 ⟨subd4_2_498, List.forall_mem_cons.2 ⟨subd4_2_499, List.forall_mem_cons.2 ⟨subd4_2_500, List.forall_mem_cons.2 ⟨subd4_2_501, List.forall_mem_cons.2 ⟨subd4_2_502, List.forall_mem_cons.2 ⟨subd4_2_503, List.forall_mem_cons.2 ⟨subd4_2_504, List.forall_mem_cons.2 ⟨subd4_2_505, List.forall_mem_cons.2 ⟨subd4_2_506, List.forall_mem_cons.2 ⟨subd4_2_507, List.forall_mem_cons.2 ⟨subd4_2_508, List.forall_mem_cons.2 ⟨subd4_2_509, List.forall_mem_cons.2 ⟨subd4_2_510, List.forall_mem_cons.2 ⟨subd4_2_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_2_512 : subd4_2 [-1, -1, -6] = true := by decide +kernel
theorem subd4_2_513 : subd4_2 [-1, -1, -5] = true := by decide +kernel
theorem subd4_2_514 : subd4_2 [-1, -1, -4] = true := by decide +kernel
theorem subd4_2_515 : subd4_2 [-1, -1, -3] = true := by decide +kernel
theorem subd4_2_516 : subd4_2 [-1, -1, -2] = true := by decide +kernel
theorem subd4_2_517 : subd4_2 [-1, -1, -1] = true := by decide +kernel
theorem subd4_2_518 : subd4_2 [-1, -1, 0] = true := by decide +kernel
theorem subd4_2_519 : subd4_2 [-1, -1, 1] = true := by decide +kernel
theorem subd4_2_520 : subd4_2 [-1, -1, 2] = true := by decide +kernel
theorem subd4_2_521 : subd4_2 [-1, -1, 3] = true := by decide +kernel
theorem subd4_2_522 : subd4_2 [-1, -1, 4] = true := by decide +kernel
theorem subd4_2_523 : subd4_2 [-1, -1, 5] = true := by decide +kernel
theorem subd4_2_524 : subd4_2 [-1, -1, 6] = true := by decide +kernel
theorem subd4_2_525 : subd4_2 [-1, -1, 7] = true := by decide +kernel
theorem subd4_2_526 : subd4_2 [-1, -1, 8] = true := by decide +kernel
theorem subd4_2_527 : subd4_2 [-1, -1, 9] = true := by decide +kernel
theorem subd4_2_528 : subd4_2 [-1, 0, -10] = true := by decide +kernel
theorem subd4_2_529 : subd4_2 [-1, 0, -9] = true := by decide +kernel
theorem subd4_2_530 : subd4_2 [-1, 0, -8] = true := by decide +kernel
theorem subd4_2_531 : subd4_2 [-1, 0, -7] = true := by decide +kernel
theorem subd4_2_532 : subd4_2 [-1, 0, -6] = true := by decide +kernel
theorem subd4_2_533 : subd4_2 [-1, 0, -5] = true := by decide +kernel
theorem subd4_2_534 : subd4_2 [-1, 0, -4] = true := by decide +kernel
theorem subd4_2_535 : subd4_2 [-1, 0, -3] = true := by decide +kernel
theorem subd4_2_536 : subd4_2 [-1, 0, -2] = true := by decide +kernel
theorem subd4_2_537 : subd4_2 [-1, 0, -1] = true := by decide +kernel
theorem subd4_2_538 : subd4_2 [-1, 0, 0] = true := by decide +kernel
theorem subd4_2_539 : subd4_2 [-1, 0, 1] = true := by decide +kernel
theorem subd4_2_540 : subd4_2 [-1, 0, 2] = true := by decide +kernel
theorem subd4_2_541 : subd4_2 [-1, 0, 3] = true := by decide +kernel
theorem subd4_2_542 : subd4_2 [-1, 0, 4] = true := by decide +kernel
theorem subd4_2_543 : subd4_2 [-1, 0, 5] = true := by decide +kernel
theorem sbd4_2_16 : ∀ q ∈ blkd4_2_16, subd4_2 q = true := by
  unfold blkd4_2_16
  exact List.forall_mem_cons.2 ⟨subd4_2_512, List.forall_mem_cons.2 ⟨subd4_2_513, List.forall_mem_cons.2 ⟨subd4_2_514, List.forall_mem_cons.2 ⟨subd4_2_515, List.forall_mem_cons.2 ⟨subd4_2_516, List.forall_mem_cons.2 ⟨subd4_2_517, List.forall_mem_cons.2 ⟨subd4_2_518, List.forall_mem_cons.2 ⟨subd4_2_519, List.forall_mem_cons.2 ⟨subd4_2_520, List.forall_mem_cons.2 ⟨subd4_2_521, List.forall_mem_cons.2 ⟨subd4_2_522, List.forall_mem_cons.2 ⟨subd4_2_523, List.forall_mem_cons.2 ⟨subd4_2_524, List.forall_mem_cons.2 ⟨subd4_2_525, List.forall_mem_cons.2 ⟨subd4_2_526, List.forall_mem_cons.2 ⟨subd4_2_527, List.forall_mem_cons.2 ⟨subd4_2_528, List.forall_mem_cons.2 ⟨subd4_2_529, List.forall_mem_cons.2 ⟨subd4_2_530, List.forall_mem_cons.2 ⟨subd4_2_531, List.forall_mem_cons.2 ⟨subd4_2_532, List.forall_mem_cons.2 ⟨subd4_2_533, List.forall_mem_cons.2 ⟨subd4_2_534, List.forall_mem_cons.2 ⟨subd4_2_535, List.forall_mem_cons.2 ⟨subd4_2_536, List.forall_mem_cons.2 ⟨subd4_2_537, List.forall_mem_cons.2 ⟨subd4_2_538, List.forall_mem_cons.2 ⟨subd4_2_539, List.forall_mem_cons.2 ⟨subd4_2_540, List.forall_mem_cons.2 ⟨subd4_2_541, List.forall_mem_cons.2 ⟨subd4_2_542, List.forall_mem_cons.2 ⟨subd4_2_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_2_544 : subd4_2 [-1, 0, 6] = true := by decide +kernel
theorem subd4_2_545 : subd4_2 [-1, 0, 7] = true := by decide +kernel
theorem subd4_2_546 : subd4_2 [-1, 0, 8] = true := by decide +kernel
theorem subd4_2_547 : subd4_2 [-1, 0, 9] = true := by decide +kernel
theorem subd4_2_548 : subd4_2 [-1, 1, -10] = true := by decide +kernel
theorem subd4_2_549 : subd4_2 [-1, 1, -9] = true := by decide +kernel
theorem subd4_2_550 : subd4_2 [-1, 1, -8] = true := by decide +kernel
theorem subd4_2_551 : subd4_2 [-1, 1, -7] = true := by decide +kernel
theorem subd4_2_552 : subd4_2 [-1, 1, -6] = true := by decide +kernel
theorem subd4_2_553 : subd4_2 [-1, 1, -5] = true := by decide +kernel
theorem subd4_2_554 : subd4_2 [-1, 1, -4] = true := by decide +kernel
theorem subd4_2_555 : subd4_2 [-1, 1, -3] = true := by decide +kernel
theorem subd4_2_556 : subd4_2 [-1, 1, -2] = true := by decide +kernel
theorem subd4_2_557 : subd4_2 [-1, 1, -1] = true := by decide +kernel
theorem subd4_2_558 : subd4_2 [-1, 1, 0] = true := by decide +kernel
theorem subd4_2_559 : subd4_2 [-1, 1, 1] = true := by decide +kernel
theorem subd4_2_560 : subd4_2 [-1, 1, 2] = true := by decide +kernel
theorem subd4_2_561 : subd4_2 [-1, 1, 3] = true := by decide +kernel
theorem subd4_2_562 : subd4_2 [-1, 1, 4] = true := by decide +kernel
theorem subd4_2_563 : subd4_2 [-1, 1, 5] = true := by decide +kernel
theorem subd4_2_564 : subd4_2 [-1, 1, 6] = true := by decide +kernel
theorem subd4_2_565 : subd4_2 [-1, 1, 7] = true := by decide +kernel
theorem subd4_2_566 : subd4_2 [-1, 1, 8] = true := by decide +kernel
theorem subd4_2_567 : subd4_2 [-1, 1, 9] = true := by decide +kernel
theorem subd4_2_568 : subd4_2 [-1, 2, -9] = true := by decide +kernel
theorem subd4_2_569 : subd4_2 [-1, 2, -8] = true := by decide +kernel
theorem subd4_2_570 : subd4_2 [-1, 2, -7] = true := by decide +kernel
theorem subd4_2_571 : subd4_2 [-1, 2, -6] = true := by decide +kernel
theorem subd4_2_572 : subd4_2 [-1, 2, -5] = true := by decide +kernel
theorem subd4_2_573 : subd4_2 [-1, 2, -4] = true := by decide +kernel
theorem subd4_2_574 : subd4_2 [-1, 2, -3] = true := by decide +kernel
theorem subd4_2_575 : subd4_2 [-1, 2, -2] = true := by decide +kernel
theorem sbd4_2_17 : ∀ q ∈ blkd4_2_17, subd4_2 q = true := by
  unfold blkd4_2_17
  exact List.forall_mem_cons.2 ⟨subd4_2_544, List.forall_mem_cons.2 ⟨subd4_2_545, List.forall_mem_cons.2 ⟨subd4_2_546, List.forall_mem_cons.2 ⟨subd4_2_547, List.forall_mem_cons.2 ⟨subd4_2_548, List.forall_mem_cons.2 ⟨subd4_2_549, List.forall_mem_cons.2 ⟨subd4_2_550, List.forall_mem_cons.2 ⟨subd4_2_551, List.forall_mem_cons.2 ⟨subd4_2_552, List.forall_mem_cons.2 ⟨subd4_2_553, List.forall_mem_cons.2 ⟨subd4_2_554, List.forall_mem_cons.2 ⟨subd4_2_555, List.forall_mem_cons.2 ⟨subd4_2_556, List.forall_mem_cons.2 ⟨subd4_2_557, List.forall_mem_cons.2 ⟨subd4_2_558, List.forall_mem_cons.2 ⟨subd4_2_559, List.forall_mem_cons.2 ⟨subd4_2_560, List.forall_mem_cons.2 ⟨subd4_2_561, List.forall_mem_cons.2 ⟨subd4_2_562, List.forall_mem_cons.2 ⟨subd4_2_563, List.forall_mem_cons.2 ⟨subd4_2_564, List.forall_mem_cons.2 ⟨subd4_2_565, List.forall_mem_cons.2 ⟨subd4_2_566, List.forall_mem_cons.2 ⟨subd4_2_567, List.forall_mem_cons.2 ⟨subd4_2_568, List.forall_mem_cons.2 ⟨subd4_2_569, List.forall_mem_cons.2 ⟨subd4_2_570, List.forall_mem_cons.2 ⟨subd4_2_571, List.forall_mem_cons.2 ⟨subd4_2_572, List.forall_mem_cons.2 ⟨subd4_2_573, List.forall_mem_cons.2 ⟨subd4_2_574, List.forall_mem_cons.2 ⟨subd4_2_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_2_576 : subd4_2 [-1, 2, -1] = true := by decide +kernel
theorem subd4_2_577 : subd4_2 [-1, 2, 0] = true := by decide +kernel
theorem subd4_2_578 : subd4_2 [-1, 2, 1] = true := by decide +kernel
theorem subd4_2_579 : subd4_2 [-1, 2, 2] = true := by decide +kernel
theorem subd4_2_580 : subd4_2 [-1, 2, 3] = true := by decide +kernel
theorem subd4_2_581 : subd4_2 [-1, 2, 4] = true := by decide +kernel
theorem subd4_2_582 : subd4_2 [-1, 2, 5] = true := by decide +kernel
theorem subd4_2_583 : subd4_2 [-1, 2, 6] = true := by decide +kernel
theorem subd4_2_584 : subd4_2 [-1, 2, 7] = true := by decide +kernel
theorem subd4_2_585 : subd4_2 [-1, 2, 8] = true := by decide +kernel
theorem subd4_2_586 : subd4_2 [-1, 2, 9] = true := by decide +kernel
theorem subd4_2_587 : subd4_2 [-1, 3, -8] = true := by decide +kernel
theorem subd4_2_588 : subd4_2 [-1, 3, -7] = true := by decide +kernel
theorem subd4_2_589 : subd4_2 [-1, 3, -6] = true := by decide +kernel
theorem subd4_2_590 : subd4_2 [-1, 3, -5] = true := by decide +kernel
theorem subd4_2_591 : subd4_2 [-1, 3, -4] = true := by decide +kernel
theorem subd4_2_592 : subd4_2 [-1, 3, -3] = true := by decide +kernel
theorem subd4_2_593 : subd4_2 [-1, 3, -2] = true := by decide +kernel
theorem subd4_2_594 : subd4_2 [-1, 3, -1] = true := by decide +kernel
theorem subd4_2_595 : subd4_2 [-1, 3, 0] = true := by decide +kernel
theorem subd4_2_596 : subd4_2 [-1, 3, 1] = true := by decide +kernel
theorem subd4_2_597 : subd4_2 [-1, 3, 2] = true := by decide +kernel
theorem subd4_2_598 : subd4_2 [-1, 3, 3] = true := by decide +kernel
theorem subd4_2_599 : subd4_2 [-1, 3, 4] = true := by decide +kernel
theorem subd4_2_600 : subd4_2 [-1, 3, 5] = true := by decide +kernel
theorem subd4_2_601 : subd4_2 [-1, 3, 6] = true := by decide +kernel
theorem subd4_2_602 : subd4_2 [-1, 3, 7] = true := by decide +kernel
theorem subd4_2_603 : subd4_2 [-1, 3, 8] = true := by decide +kernel
theorem subd4_2_604 : subd4_2 [-1, 3, 9] = true := by decide +kernel
theorem subd4_2_605 : subd4_2 [-1, 4, -7] = true := by decide +kernel
theorem subd4_2_606 : subd4_2 [-1, 4, -6] = true := by decide +kernel
theorem subd4_2_607 : subd4_2 [-1, 4, -5] = true := by decide +kernel
theorem sbd4_2_18 : ∀ q ∈ blkd4_2_18, subd4_2 q = true := by
  unfold blkd4_2_18
  exact List.forall_mem_cons.2 ⟨subd4_2_576, List.forall_mem_cons.2 ⟨subd4_2_577, List.forall_mem_cons.2 ⟨subd4_2_578, List.forall_mem_cons.2 ⟨subd4_2_579, List.forall_mem_cons.2 ⟨subd4_2_580, List.forall_mem_cons.2 ⟨subd4_2_581, List.forall_mem_cons.2 ⟨subd4_2_582, List.forall_mem_cons.2 ⟨subd4_2_583, List.forall_mem_cons.2 ⟨subd4_2_584, List.forall_mem_cons.2 ⟨subd4_2_585, List.forall_mem_cons.2 ⟨subd4_2_586, List.forall_mem_cons.2 ⟨subd4_2_587, List.forall_mem_cons.2 ⟨subd4_2_588, List.forall_mem_cons.2 ⟨subd4_2_589, List.forall_mem_cons.2 ⟨subd4_2_590, List.forall_mem_cons.2 ⟨subd4_2_591, List.forall_mem_cons.2 ⟨subd4_2_592, List.forall_mem_cons.2 ⟨subd4_2_593, List.forall_mem_cons.2 ⟨subd4_2_594, List.forall_mem_cons.2 ⟨subd4_2_595, List.forall_mem_cons.2 ⟨subd4_2_596, List.forall_mem_cons.2 ⟨subd4_2_597, List.forall_mem_cons.2 ⟨subd4_2_598, List.forall_mem_cons.2 ⟨subd4_2_599, List.forall_mem_cons.2 ⟨subd4_2_600, List.forall_mem_cons.2 ⟨subd4_2_601, List.forall_mem_cons.2 ⟨subd4_2_602, List.forall_mem_cons.2 ⟨subd4_2_603, List.forall_mem_cons.2 ⟨subd4_2_604, List.forall_mem_cons.2 ⟨subd4_2_605, List.forall_mem_cons.2 ⟨subd4_2_606, List.forall_mem_cons.2 ⟨subd4_2_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_2_608 : subd4_2 [-1, 4, -4] = true := by decide +kernel
theorem subd4_2_609 : subd4_2 [-1, 4, -3] = true := by decide +kernel
theorem subd4_2_610 : subd4_2 [-1, 4, -2] = true := by decide +kernel
theorem subd4_2_611 : subd4_2 [-1, 4, -1] = true := by decide +kernel
theorem subd4_2_612 : subd4_2 [-1, 4, 0] = true := by decide +kernel
theorem subd4_2_613 : subd4_2 [-1, 4, 1] = true := by decide +kernel
theorem subd4_2_614 : subd4_2 [-1, 4, 2] = true := by decide +kernel
theorem subd4_2_615 : subd4_2 [-1, 4, 3] = true := by decide +kernel
theorem subd4_2_616 : subd4_2 [-1, 4, 4] = true := by decide +kernel
theorem subd4_2_617 : subd4_2 [-1, 4, 5] = true := by decide +kernel
theorem subd4_2_618 : subd4_2 [-1, 4, 6] = true := by decide +kernel
theorem subd4_2_619 : subd4_2 [-1, 4, 7] = true := by decide +kernel
theorem subd4_2_620 : subd4_2 [-1, 4, 8] = true := by decide +kernel
theorem subd4_2_621 : subd4_2 [-1, 5] = true := by decide +kernel
theorem subd4_2_622 : subd4_2 [-1, 6] = true := by decide +kernel
theorem subd4_2_623 : subd4_2 [0, -8] = true := by decide +kernel
theorem subd4_2_624 : subd4_2 [0, -7] = true := by decide +kernel
theorem subd4_2_625 : subd4_2 [0, -6] = true := by decide +kernel
theorem subd4_2_626 : subd4_2 [0, -5, -9] = true := by decide +kernel
theorem subd4_2_627 : subd4_2 [0, -5, -8] = true := by decide +kernel
theorem subd4_2_628 : subd4_2 [0, -5, -7] = true := by decide +kernel
theorem subd4_2_629 : subd4_2 [0, -5, -6] = true := by decide +kernel
theorem subd4_2_630 : subd4_2 [0, -5, -5] = true := by decide +kernel
theorem subd4_2_631 : subd4_2 [0, -5, -4] = true := by decide +kernel
theorem subd4_2_632 : subd4_2 [0, -5, -3] = true := by decide +kernel
theorem subd4_2_633 : subd4_2 [0, -5, -2] = true := by decide +kernel
theorem subd4_2_634 : subd4_2 [0, -5, -1] = true := by decide +kernel
theorem subd4_2_635 : subd4_2 [0, -5, 0] = true := by decide +kernel
theorem subd4_2_636 : subd4_2 [0, -5, 1] = true := by decide +kernel
theorem subd4_2_637 : subd4_2 [0, -5, 2] = true := by decide +kernel
theorem subd4_2_638 : subd4_2 [0, -5, 3] = true := by decide +kernel
theorem subd4_2_639 : subd4_2 [0, -5, 4] = true := by decide +kernel
theorem sbd4_2_19 : ∀ q ∈ blkd4_2_19, subd4_2 q = true := by
  unfold blkd4_2_19
  exact List.forall_mem_cons.2 ⟨subd4_2_608, List.forall_mem_cons.2 ⟨subd4_2_609, List.forall_mem_cons.2 ⟨subd4_2_610, List.forall_mem_cons.2 ⟨subd4_2_611, List.forall_mem_cons.2 ⟨subd4_2_612, List.forall_mem_cons.2 ⟨subd4_2_613, List.forall_mem_cons.2 ⟨subd4_2_614, List.forall_mem_cons.2 ⟨subd4_2_615, List.forall_mem_cons.2 ⟨subd4_2_616, List.forall_mem_cons.2 ⟨subd4_2_617, List.forall_mem_cons.2 ⟨subd4_2_618, List.forall_mem_cons.2 ⟨subd4_2_619, List.forall_mem_cons.2 ⟨subd4_2_620, List.forall_mem_cons.2 ⟨subd4_2_621, List.forall_mem_cons.2 ⟨subd4_2_622, List.forall_mem_cons.2 ⟨subd4_2_623, List.forall_mem_cons.2 ⟨subd4_2_624, List.forall_mem_cons.2 ⟨subd4_2_625, List.forall_mem_cons.2 ⟨subd4_2_626, List.forall_mem_cons.2 ⟨subd4_2_627, List.forall_mem_cons.2 ⟨subd4_2_628, List.forall_mem_cons.2 ⟨subd4_2_629, List.forall_mem_cons.2 ⟨subd4_2_630, List.forall_mem_cons.2 ⟨subd4_2_631, List.forall_mem_cons.2 ⟨subd4_2_632, List.forall_mem_cons.2 ⟨subd4_2_633, List.forall_mem_cons.2 ⟨subd4_2_634, List.forall_mem_cons.2 ⟨subd4_2_635, List.forall_mem_cons.2 ⟨subd4_2_636, List.forall_mem_cons.2 ⟨subd4_2_637, List.forall_mem_cons.2 ⟨subd4_2_638, List.forall_mem_cons.2 ⟨subd4_2_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_2_640 : subd4_2 [0, -5, 5] = true := by decide +kernel
theorem subd4_2_641 : subd4_2 [0, -4, -10] = true := by decide +kernel
theorem subd4_2_642 : subd4_2 [0, -4, -9] = true := by decide +kernel
theorem subd4_2_643 : subd4_2 [0, -4, -8] = true := by decide +kernel
theorem subd4_2_644 : subd4_2 [0, -4, -7] = true := by decide +kernel
theorem subd4_2_645 : subd4_2 [0, -4, -6] = true := by decide +kernel
theorem subd4_2_646 : subd4_2 [0, -4, -5] = true := by decide +kernel
theorem subd4_2_647 : subd4_2 [0, -4, -4] = true := by decide +kernel
theorem subd4_2_648 : subd4_2 [0, -4, -3] = true := by decide +kernel
theorem subd4_2_649 : subd4_2 [0, -4, -2] = true := by decide +kernel
theorem subd4_2_650 : subd4_2 [0, -4, -1] = true := by decide +kernel
theorem subd4_2_651 : subd4_2 [0, -4, 0] = true := by decide +kernel
theorem subd4_2_652 : subd4_2 [0, -4, 1] = true := by decide +kernel
theorem subd4_2_653 : subd4_2 [0, -4, 2] = true := by decide +kernel
theorem subd4_2_654 : subd4_2 [0, -4, 3] = true := by decide +kernel
theorem subd4_2_655 : subd4_2 [0, -4, 4] = true := by decide +kernel
theorem subd4_2_656 : subd4_2 [0, -4, 5] = true := by decide +kernel
theorem subd4_2_657 : subd4_2 [0, -4, 6] = true := by decide +kernel
theorem subd4_2_658 : subd4_2 [0, -4, 7] = true := by decide +kernel
theorem subd4_2_659 : subd4_2 [0, -3, -10] = true := by decide +kernel
theorem subd4_2_660 : subd4_2 [0, -3, -9] = true := by decide +kernel
theorem subd4_2_661 : subd4_2 [0, -3, -8] = true := by decide +kernel
theorem subd4_2_662 : subd4_2 [0, -3, -7] = true := by decide +kernel
theorem subd4_2_663 : subd4_2 [0, -3, -6] = true := by decide +kernel
theorem subd4_2_664 : subd4_2 [0, -3, -5] = true := by decide +kernel
theorem subd4_2_665 : subd4_2 [0, -3, -4] = true := by decide +kernel
theorem subd4_2_666 : subd4_2 [0, -3, -3] = true := by decide +kernel
theorem subd4_2_667 : subd4_2 [0, -3, -2] = true := by decide +kernel
theorem subd4_2_668 : subd4_2 [0, -3, -1] = true := by decide +kernel
theorem subd4_2_669 : subd4_2 [0, -3, 0] = true := by decide +kernel
theorem subd4_2_670 : subd4_2 [0, -3, 1] = true := by decide +kernel
theorem subd4_2_671 : subd4_2 [0, -3, 2] = true := by decide +kernel
theorem sbd4_2_20 : ∀ q ∈ blkd4_2_20, subd4_2 q = true := by
  unfold blkd4_2_20
  exact List.forall_mem_cons.2 ⟨subd4_2_640, List.forall_mem_cons.2 ⟨subd4_2_641, List.forall_mem_cons.2 ⟨subd4_2_642, List.forall_mem_cons.2 ⟨subd4_2_643, List.forall_mem_cons.2 ⟨subd4_2_644, List.forall_mem_cons.2 ⟨subd4_2_645, List.forall_mem_cons.2 ⟨subd4_2_646, List.forall_mem_cons.2 ⟨subd4_2_647, List.forall_mem_cons.2 ⟨subd4_2_648, List.forall_mem_cons.2 ⟨subd4_2_649, List.forall_mem_cons.2 ⟨subd4_2_650, List.forall_mem_cons.2 ⟨subd4_2_651, List.forall_mem_cons.2 ⟨subd4_2_652, List.forall_mem_cons.2 ⟨subd4_2_653, List.forall_mem_cons.2 ⟨subd4_2_654, List.forall_mem_cons.2 ⟨subd4_2_655, List.forall_mem_cons.2 ⟨subd4_2_656, List.forall_mem_cons.2 ⟨subd4_2_657, List.forall_mem_cons.2 ⟨subd4_2_658, List.forall_mem_cons.2 ⟨subd4_2_659, List.forall_mem_cons.2 ⟨subd4_2_660, List.forall_mem_cons.2 ⟨subd4_2_661, List.forall_mem_cons.2 ⟨subd4_2_662, List.forall_mem_cons.2 ⟨subd4_2_663, List.forall_mem_cons.2 ⟨subd4_2_664, List.forall_mem_cons.2 ⟨subd4_2_665, List.forall_mem_cons.2 ⟨subd4_2_666, List.forall_mem_cons.2 ⟨subd4_2_667, List.forall_mem_cons.2 ⟨subd4_2_668, List.forall_mem_cons.2 ⟨subd4_2_669, List.forall_mem_cons.2 ⟨subd4_2_670, List.forall_mem_cons.2 ⟨subd4_2_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C121
