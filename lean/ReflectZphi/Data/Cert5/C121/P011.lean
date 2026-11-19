import ReflectZphi.Data.Cert5.C121.Base

namespace ReflectZphi.Data.Cert5.C121

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd5_2_224 : subd5_2 [-3, 2, -2] = true := by decide +kernel
theorem subd5_2_225 : subd5_2 [-3, 2, -1] = true := by decide +kernel
theorem subd5_2_226 : subd5_2 [-3, 2, 0] = true := by decide +kernel
theorem subd5_2_227 : subd5_2 [-3, 2, 1] = true := by decide +kernel
theorem subd5_2_228 : subd5_2 [-3, 2, 2] = true := by decide +kernel
theorem subd5_2_229 : subd5_2 [-3, 2, 3] = true := by decide +kernel
theorem subd5_2_230 : subd5_2 [-3, 2, 4] = true := by decide +kernel
theorem subd5_2_231 : subd5_2 [-3, 2, 5] = true := by decide +kernel
theorem subd5_2_232 : subd5_2 [-3, 3] = true := by decide +kernel
theorem subd5_2_233 : subd5_2 [-3, 4] = true := by decide +kernel
theorem subd5_2_234 : subd5_2 [-3, 5] = true := by decide +kernel
theorem subd5_2_235 : subd5_2 [-2, -9] = true := by decide +kernel
theorem subd5_2_236 : subd5_2 [-2, -8] = true := by decide +kernel
theorem subd5_2_237 : subd5_2 [-2, -7] = true := by decide +kernel
theorem subd5_2_238 : subd5_2 [-2, -6] = true := by decide +kernel
theorem subd5_2_239 : subd5_2 [-2, -5, -7] = true := by decide +kernel
theorem subd5_2_240 : subd5_2 [-2, -5, -6] = true := by decide +kernel
theorem subd5_2_241 : subd5_2 [-2, -5, -5] = true := by decide +kernel
theorem subd5_2_242 : subd5_2 [-2, -5, -4] = true := by decide +kernel
theorem subd5_2_243 : subd5_2 [-2, -5, -3] = true := by decide +kernel
theorem subd5_2_244 : subd5_2 [-2, -5, -2] = true := by decide +kernel
theorem subd5_2_245 : subd5_2 [-2, -5, -1] = true := by decide +kernel
theorem subd5_2_246 : subd5_2 [-2, -5, 0] = true := by decide +kernel
theorem subd5_2_247 : subd5_2 [-2, -5, 1] = true := by decide +kernel
theorem subd5_2_248 : subd5_2 [-2, -5, 2] = true := by decide +kernel
theorem subd5_2_249 : subd5_2 [-2, -5, 3] = true := by decide +kernel
theorem subd5_2_250 : subd5_2 [-2, -5, 4] = true := by decide +kernel
theorem subd5_2_251 : subd5_2 [-2, -5, 5] = true := by decide +kernel
theorem subd5_2_252 : subd5_2 [-2, -5, 6] = true := by decide +kernel
theorem subd5_2_253 : subd5_2 [-2, -5, 7] = true := by decide +kernel
theorem subd5_2_254 : subd5_2 [-2, -4, -8] = true := by decide +kernel
theorem subd5_2_255 : subd5_2 [-2, -4, -7] = true := by decide +kernel
theorem sbd5_2_7 : ∀ q ∈ blkd5_2_7, subd5_2 q = true := by
  unfold blkd5_2_7
  exact List.forall_mem_cons.2 ⟨subd5_2_224, List.forall_mem_cons.2 ⟨subd5_2_225, List.forall_mem_cons.2 ⟨subd5_2_226, List.forall_mem_cons.2 ⟨subd5_2_227, List.forall_mem_cons.2 ⟨subd5_2_228, List.forall_mem_cons.2 ⟨subd5_2_229, List.forall_mem_cons.2 ⟨subd5_2_230, List.forall_mem_cons.2 ⟨subd5_2_231, List.forall_mem_cons.2 ⟨subd5_2_232, List.forall_mem_cons.2 ⟨subd5_2_233, List.forall_mem_cons.2 ⟨subd5_2_234, List.forall_mem_cons.2 ⟨subd5_2_235, List.forall_mem_cons.2 ⟨subd5_2_236, List.forall_mem_cons.2 ⟨subd5_2_237, List.forall_mem_cons.2 ⟨subd5_2_238, List.forall_mem_cons.2 ⟨subd5_2_239, List.forall_mem_cons.2 ⟨subd5_2_240, List.forall_mem_cons.2 ⟨subd5_2_241, List.forall_mem_cons.2 ⟨subd5_2_242, List.forall_mem_cons.2 ⟨subd5_2_243, List.forall_mem_cons.2 ⟨subd5_2_244, List.forall_mem_cons.2 ⟨subd5_2_245, List.forall_mem_cons.2 ⟨subd5_2_246, List.forall_mem_cons.2 ⟨subd5_2_247, List.forall_mem_cons.2 ⟨subd5_2_248, List.forall_mem_cons.2 ⟨subd5_2_249, List.forall_mem_cons.2 ⟨subd5_2_250, List.forall_mem_cons.2 ⟨subd5_2_251, List.forall_mem_cons.2 ⟨subd5_2_252, List.forall_mem_cons.2 ⟨subd5_2_253, List.forall_mem_cons.2 ⟨subd5_2_254, List.forall_mem_cons.2 ⟨subd5_2_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_256 : subd5_2 [-2, -4, -6] = true := by decide +kernel
theorem subd5_2_257 : subd5_2 [-2, -4, -5] = true := by decide +kernel
theorem subd5_2_258 : subd5_2 [-2, -4, -4] = true := by decide +kernel
theorem subd5_2_259 : subd5_2 [-2, -4, -3] = true := by decide +kernel
theorem subd5_2_260 : subd5_2 [-2, -4, -2] = true := by decide +kernel
theorem subd5_2_261 : subd5_2 [-2, -4, -1] = true := by decide +kernel
theorem subd5_2_262 : subd5_2 [-2, -4, 0] = true := by decide +kernel
theorem subd5_2_263 : subd5_2 [-2, -4, 1] = true := by decide +kernel
theorem subd5_2_264 : subd5_2 [-2, -4, 2] = true := by decide +kernel
theorem subd5_2_265 : subd5_2 [-2, -4, 3] = true := by decide +kernel
theorem subd5_2_266 : subd5_2 [-2, -4, 4] = true := by decide +kernel
theorem subd5_2_267 : subd5_2 [-2, -4, 5] = true := by decide +kernel
theorem subd5_2_268 : subd5_2 [-2, -4, 6] = true := by decide +kernel
theorem subd5_2_269 : subd5_2 [-2, -4, 7] = true := by decide +kernel
theorem subd5_2_270 : subd5_2 [-2, -4, 8] = true := by decide +kernel
theorem subd5_2_271 : subd5_2 [-2, -3, -8] = true := by decide +kernel
theorem subd5_2_272 : subd5_2 [-2, -3, -7] = true := by decide +kernel
theorem subd5_2_273 : subd5_2 [-2, -3, -6] = true := by decide +kernel
theorem subd5_2_274 : subd5_2 [-2, -3, -5] = true := by decide +kernel
theorem subd5_2_275 : subd5_2 [-2, -3, -4] = true := by decide +kernel
theorem subd5_2_276 : subd5_2 [-2, -3, -3] = true := by decide +kernel
theorem subd5_2_277 : subd5_2 [-2, -3, -2] = true := by decide +kernel
theorem subd5_2_278 : subd5_2 [-2, -3, -1] = true := by decide +kernel
theorem subd5_2_279 : subd5_2 [-2, -3, 0] = true := by decide +kernel
theorem subd5_2_280 : subd5_2 [-2, -3, 1] = true := by decide +kernel
theorem subd5_2_281 : subd5_2 [-2, -3, 2] = true := by decide +kernel
theorem subd5_2_282 : subd5_2 [-2, -3, 3] = true := by decide +kernel
theorem subd5_2_283 : subd5_2 [-2, -3, 4] = true := by decide +kernel
theorem subd5_2_284 : subd5_2 [-2, -3, 5] = true := by decide +kernel
theorem subd5_2_285 : subd5_2 [-2, -3, 6] = true := by decide +kernel
theorem subd5_2_286 : subd5_2 [-2, -3, 7] = true := by decide +kernel
theorem subd5_2_287 : subd5_2 [-2, -3, 8] = true := by decide +kernel
theorem sbd5_2_8 : ∀ q ∈ blkd5_2_8, subd5_2 q = true := by
  unfold blkd5_2_8
  exact List.forall_mem_cons.2 ⟨subd5_2_256, List.forall_mem_cons.2 ⟨subd5_2_257, List.forall_mem_cons.2 ⟨subd5_2_258, List.forall_mem_cons.2 ⟨subd5_2_259, List.forall_mem_cons.2 ⟨subd5_2_260, List.forall_mem_cons.2 ⟨subd5_2_261, List.forall_mem_cons.2 ⟨subd5_2_262, List.forall_mem_cons.2 ⟨subd5_2_263, List.forall_mem_cons.2 ⟨subd5_2_264, List.forall_mem_cons.2 ⟨subd5_2_265, List.forall_mem_cons.2 ⟨subd5_2_266, List.forall_mem_cons.2 ⟨subd5_2_267, List.forall_mem_cons.2 ⟨subd5_2_268, List.forall_mem_cons.2 ⟨subd5_2_269, List.forall_mem_cons.2 ⟨subd5_2_270, List.forall_mem_cons.2 ⟨subd5_2_271, List.forall_mem_cons.2 ⟨subd5_2_272, List.forall_mem_cons.2 ⟨subd5_2_273, List.forall_mem_cons.2 ⟨subd5_2_274, List.forall_mem_cons.2 ⟨subd5_2_275, List.forall_mem_cons.2 ⟨subd5_2_276, List.forall_mem_cons.2 ⟨subd5_2_277, List.forall_mem_cons.2 ⟨subd5_2_278, List.forall_mem_cons.2 ⟨subd5_2_279, List.forall_mem_cons.2 ⟨subd5_2_280, List.forall_mem_cons.2 ⟨subd5_2_281, List.forall_mem_cons.2 ⟨subd5_2_282, List.forall_mem_cons.2 ⟨subd5_2_283, List.forall_mem_cons.2 ⟨subd5_2_284, List.forall_mem_cons.2 ⟨subd5_2_285, List.forall_mem_cons.2 ⟨subd5_2_286, List.forall_mem_cons.2 ⟨subd5_2_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_288 : subd5_2 [-2, -2, -9] = true := by decide +kernel
theorem subd5_2_289 : subd5_2 [-2, -2, -8] = true := by decide +kernel
theorem subd5_2_290 : subd5_2 [-2, -2, -7] = true := by decide +kernel
theorem subd5_2_291 : subd5_2 [-2, -2, -6] = true := by decide +kernel
theorem subd5_2_292 : subd5_2 [-2, -2, -5] = true := by decide +kernel
theorem subd5_2_293 : subd5_2 [-2, -2, -4] = true := by decide +kernel
theorem subd5_2_294 : subd5_2 [-2, -2, -3] = true := by decide +kernel
theorem subd5_2_295 : subd5_2 [-2, -2, -2] = true := by decide +kernel
theorem subd5_2_296 : subd5_2 [-2, -2, -1] = true := by decide +kernel
theorem subd5_2_297 : subd5_2 [-2, -2, 0] = true := by decide +kernel
theorem subd5_2_298 : subd5_2 [-2, -2, 1] = true := by decide +kernel
theorem subd5_2_299 : subd5_2 [-2, -2, 2] = true := by decide +kernel
theorem subd5_2_300 : subd5_2 [-2, -2, 3] = true := by decide +kernel
theorem subd5_2_301 : subd5_2 [-2, -2, 4] = true := by decide +kernel
theorem subd5_2_302 : subd5_2 [-2, -2, 5] = true := by decide +kernel
theorem subd5_2_303 : subd5_2 [-2, -2, 6] = true := by decide +kernel
theorem subd5_2_304 : subd5_2 [-2, -2, 7] = true := by decide +kernel
theorem subd5_2_305 : subd5_2 [-2, -2, 8] = true := by decide +kernel
theorem subd5_2_306 : subd5_2 [-2, -1, -9] = true := by decide +kernel
theorem subd5_2_307 : subd5_2 [-2, -1, -8] = true := by decide +kernel
theorem subd5_2_308 : subd5_2 [-2, -1, -7] = true := by decide +kernel
theorem subd5_2_309 : subd5_2 [-2, -1, -6] = true := by decide +kernel
theorem subd5_2_310 : subd5_2 [-2, -1, -5] = true := by decide +kernel
theorem subd5_2_311 : subd5_2 [-2, -1, -4] = true := by decide +kernel
theorem subd5_2_312 : subd5_2 [-2, -1, -3] = true := by decide +kernel
theorem subd5_2_313 : subd5_2 [-2, -1, -2] = true := by decide +kernel
theorem subd5_2_314 : subd5_2 [-2, -1, -1] = true := by decide +kernel
theorem subd5_2_315 : subd5_2 [-2, -1, 0] = true := by decide +kernel
theorem subd5_2_316 : subd5_2 [-2, -1, 1] = true := by decide +kernel
theorem subd5_2_317 : subd5_2 [-2, -1, 2] = true := by decide +kernel
theorem subd5_2_318 : subd5_2 [-2, -1, 3] = true := by decide +kernel
theorem subd5_2_319 : subd5_2 [-2, -1, 4] = true := by decide +kernel
theorem sbd5_2_9 : ∀ q ∈ blkd5_2_9, subd5_2 q = true := by
  unfold blkd5_2_9
  exact List.forall_mem_cons.2 ⟨subd5_2_288, List.forall_mem_cons.2 ⟨subd5_2_289, List.forall_mem_cons.2 ⟨subd5_2_290, List.forall_mem_cons.2 ⟨subd5_2_291, List.forall_mem_cons.2 ⟨subd5_2_292, List.forall_mem_cons.2 ⟨subd5_2_293, List.forall_mem_cons.2 ⟨subd5_2_294, List.forall_mem_cons.2 ⟨subd5_2_295, List.forall_mem_cons.2 ⟨subd5_2_296, List.forall_mem_cons.2 ⟨subd5_2_297, List.forall_mem_cons.2 ⟨subd5_2_298, List.forall_mem_cons.2 ⟨subd5_2_299, List.forall_mem_cons.2 ⟨subd5_2_300, List.forall_mem_cons.2 ⟨subd5_2_301, List.forall_mem_cons.2 ⟨subd5_2_302, List.forall_mem_cons.2 ⟨subd5_2_303, List.forall_mem_cons.2 ⟨subd5_2_304, List.forall_mem_cons.2 ⟨subd5_2_305, List.forall_mem_cons.2 ⟨subd5_2_306, List.forall_mem_cons.2 ⟨subd5_2_307, List.forall_mem_cons.2 ⟨subd5_2_308, List.forall_mem_cons.2 ⟨subd5_2_309, List.forall_mem_cons.2 ⟨subd5_2_310, List.forall_mem_cons.2 ⟨subd5_2_311, List.forall_mem_cons.2 ⟨subd5_2_312, List.forall_mem_cons.2 ⟨subd5_2_313, List.forall_mem_cons.2 ⟨subd5_2_314, List.forall_mem_cons.2 ⟨subd5_2_315, List.forall_mem_cons.2 ⟨subd5_2_316, List.forall_mem_cons.2 ⟨subd5_2_317, List.forall_mem_cons.2 ⟨subd5_2_318, List.forall_mem_cons.2 ⟨subd5_2_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_320 : subd5_2 [-2, -1, 5] = true := by decide +kernel
theorem subd5_2_321 : subd5_2 [-2, -1, 6] = true := by decide +kernel
theorem subd5_2_322 : subd5_2 [-2, -1, 7] = true := by decide +kernel
theorem subd5_2_323 : subd5_2 [-2, 0, -9] = true := by decide +kernel
theorem subd5_2_324 : subd5_2 [-2, 0, -8] = true := by decide +kernel
theorem subd5_2_325 : subd5_2 [-2, 0, -7] = true := by decide +kernel
theorem subd5_2_326 : subd5_2 [-2, 0, -6] = true := by decide +kernel
theorem subd5_2_327 : subd5_2 [-2, 0, -5] = true := by decide +kernel
theorem subd5_2_328 : subd5_2 [-2, 0, -4] = true := by decide +kernel
theorem subd5_2_329 : subd5_2 [-2, 0, -3] = true := by decide +kernel
theorem subd5_2_330 : subd5_2 [-2, 0, -2] = true := by decide +kernel
theorem subd5_2_331 : subd5_2 [-2, 0, -1] = true := by decide +kernel
theorem subd5_2_332 : subd5_2 [-2, 0, 0] = true := by decide +kernel
theorem subd5_2_333 : subd5_2 [-2, 0, 1] = true := by decide +kernel
theorem subd5_2_334 : subd5_2 [-2, 0, 2] = true := by decide +kernel
theorem subd5_2_335 : subd5_2 [-2, 0, 3] = true := by decide +kernel
theorem subd5_2_336 : subd5_2 [-2, 0, 4] = true := by decide +kernel
theorem subd5_2_337 : subd5_2 [-2, 0, 5] = true := by decide +kernel
theorem subd5_2_338 : subd5_2 [-2, 0, 6] = true := by decide +kernel
theorem subd5_2_339 : subd5_2 [-2, 0, 7] = true := by decide +kernel
theorem subd5_2_340 : subd5_2 [-2, 1, -10] = true := by decide +kernel
theorem subd5_2_341 : subd5_2 [-2, 1, -9] = true := by decide +kernel
theorem subd5_2_342 : subd5_2 [-2, 1, -8] = true := by decide +kernel
theorem subd5_2_343 : subd5_2 [-2, 1, -7] = true := by decide +kernel
theorem subd5_2_344 : subd5_2 [-2, 1, -6] = true := by decide +kernel
theorem subd5_2_345 : subd5_2 [-2, 1, -5] = true := by decide +kernel
theorem subd5_2_346 : subd5_2 [-2, 1, -4] = true := by decide +kernel
theorem subd5_2_347 : subd5_2 [-2, 1, -3] = true := by decide +kernel
theorem subd5_2_348 : subd5_2 [-2, 1, -2] = true := by decide +kernel
theorem subd5_2_349 : subd5_2 [-2, 1, -1] = true := by decide +kernel
theorem subd5_2_350 : subd5_2 [-2, 1, 0] = true := by decide +kernel
theorem subd5_2_351 : subd5_2 [-2, 1, 1] = true := by decide +kernel
theorem sbd5_2_10 : ∀ q ∈ blkd5_2_10, subd5_2 q = true := by
  unfold blkd5_2_10
  exact List.forall_mem_cons.2 ⟨subd5_2_320, List.forall_mem_cons.2 ⟨subd5_2_321, List.forall_mem_cons.2 ⟨subd5_2_322, List.forall_mem_cons.2 ⟨subd5_2_323, List.forall_mem_cons.2 ⟨subd5_2_324, List.forall_mem_cons.2 ⟨subd5_2_325, List.forall_mem_cons.2 ⟨subd5_2_326, List.forall_mem_cons.2 ⟨subd5_2_327, List.forall_mem_cons.2 ⟨subd5_2_328, List.forall_mem_cons.2 ⟨subd5_2_329, List.forall_mem_cons.2 ⟨subd5_2_330, List.forall_mem_cons.2 ⟨subd5_2_331, List.forall_mem_cons.2 ⟨subd5_2_332, List.forall_mem_cons.2 ⟨subd5_2_333, List.forall_mem_cons.2 ⟨subd5_2_334, List.forall_mem_cons.2 ⟨subd5_2_335, List.forall_mem_cons.2 ⟨subd5_2_336, List.forall_mem_cons.2 ⟨subd5_2_337, List.forall_mem_cons.2 ⟨subd5_2_338, List.forall_mem_cons.2 ⟨subd5_2_339, List.forall_mem_cons.2 ⟨subd5_2_340, List.forall_mem_cons.2 ⟨subd5_2_341, List.forall_mem_cons.2 ⟨subd5_2_342, List.forall_mem_cons.2 ⟨subd5_2_343, List.forall_mem_cons.2 ⟨subd5_2_344, List.forall_mem_cons.2 ⟨subd5_2_345, List.forall_mem_cons.2 ⟨subd5_2_346, List.forall_mem_cons.2 ⟨subd5_2_347, List.forall_mem_cons.2 ⟨subd5_2_348, List.forall_mem_cons.2 ⟨subd5_2_349, List.forall_mem_cons.2 ⟨subd5_2_350, List.forall_mem_cons.2 ⟨subd5_2_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_352 : subd5_2 [-2, 1, 2] = true := by decide +kernel
theorem subd5_2_353 : subd5_2 [-2, 1, 3] = true := by decide +kernel
theorem subd5_2_354 : subd5_2 [-2, 1, 4] = true := by decide +kernel
theorem subd5_2_355 : subd5_2 [-2, 1, 5] = true := by decide +kernel
theorem subd5_2_356 : subd5_2 [-2, 1, 6] = true := by decide +kernel
theorem subd5_2_357 : subd5_2 [-2, 1, 7] = true := by decide +kernel
theorem subd5_2_358 : subd5_2 [-2, 2, -9] = true := by decide +kernel
theorem subd5_2_359 : subd5_2 [-2, 2, -8] = true := by decide +kernel
theorem subd5_2_360 : subd5_2 [-2, 2, -7] = true := by decide +kernel
theorem subd5_2_361 : subd5_2 [-2, 2, -6] = true := by decide +kernel
theorem subd5_2_362 : subd5_2 [-2, 2, -5] = true := by decide +kernel
theorem subd5_2_363 : subd5_2 [-2, 2, -4] = true := by decide +kernel
theorem subd5_2_364 : subd5_2 [-2, 2, -3] = true := by decide +kernel
theorem subd5_2_365 : subd5_2 [-2, 2, -2] = true := by decide +kernel
theorem subd5_2_366 : subd5_2 [-2, 2, -1] = true := by decide +kernel
theorem subd5_2_367 : subd5_2 [-2, 2, 0] = true := by decide +kernel
theorem subd5_2_368 : subd5_2 [-2, 2, 1] = true := by decide +kernel
theorem subd5_2_369 : subd5_2 [-2, 2, 2] = true := by decide +kernel
theorem subd5_2_370 : subd5_2 [-2, 2, 3] = true := by decide +kernel
theorem subd5_2_371 : subd5_2 [-2, 2, 4] = true := by decide +kernel
theorem subd5_2_372 : subd5_2 [-2, 2, 5] = true := by decide +kernel
theorem subd5_2_373 : subd5_2 [-2, 2, 6] = true := by decide +kernel
theorem subd5_2_374 : subd5_2 [-2, 3, -9] = true := by decide +kernel
theorem subd5_2_375 : subd5_2 [-2, 3, -8] = true := by decide +kernel
theorem subd5_2_376 : subd5_2 [-2, 3, -7] = true := by decide +kernel
theorem subd5_2_377 : subd5_2 [-2, 3, -6] = true := by decide +kernel
theorem subd5_2_378 : subd5_2 [-2, 3, -5] = true := by decide +kernel
theorem subd5_2_379 : subd5_2 [-2, 3, -4] = true := by decide +kernel
theorem subd5_2_380 : subd5_2 [-2, 3, -3] = true := by decide +kernel
theorem subd5_2_381 : subd5_2 [-2, 3, -2] = true := by decide +kernel
theorem subd5_2_382 : subd5_2 [-2, 3, -1] = true := by decide +kernel
theorem subd5_2_383 : subd5_2 [-2, 3, 0] = true := by decide +kernel
theorem sbd5_2_11 : ∀ q ∈ blkd5_2_11, subd5_2 q = true := by
  unfold blkd5_2_11
  exact List.forall_mem_cons.2 ⟨subd5_2_352, List.forall_mem_cons.2 ⟨subd5_2_353, List.forall_mem_cons.2 ⟨subd5_2_354, List.forall_mem_cons.2 ⟨subd5_2_355, List.forall_mem_cons.2 ⟨subd5_2_356, List.forall_mem_cons.2 ⟨subd5_2_357, List.forall_mem_cons.2 ⟨subd5_2_358, List.forall_mem_cons.2 ⟨subd5_2_359, List.forall_mem_cons.2 ⟨subd5_2_360, List.forall_mem_cons.2 ⟨subd5_2_361, List.forall_mem_cons.2 ⟨subd5_2_362, List.forall_mem_cons.2 ⟨subd5_2_363, List.forall_mem_cons.2 ⟨subd5_2_364, List.forall_mem_cons.2 ⟨subd5_2_365, List.forall_mem_cons.2 ⟨subd5_2_366, List.forall_mem_cons.2 ⟨subd5_2_367, List.forall_mem_cons.2 ⟨subd5_2_368, List.forall_mem_cons.2 ⟨subd5_2_369, List.forall_mem_cons.2 ⟨subd5_2_370, List.forall_mem_cons.2 ⟨subd5_2_371, List.forall_mem_cons.2 ⟨subd5_2_372, List.forall_mem_cons.2 ⟨subd5_2_373, List.forall_mem_cons.2 ⟨subd5_2_374, List.forall_mem_cons.2 ⟨subd5_2_375, List.forall_mem_cons.2 ⟨subd5_2_376, List.forall_mem_cons.2 ⟨subd5_2_377, List.forall_mem_cons.2 ⟨subd5_2_378, List.forall_mem_cons.2 ⟨subd5_2_379, List.forall_mem_cons.2 ⟨subd5_2_380, List.forall_mem_cons.2 ⟨subd5_2_381, List.forall_mem_cons.2 ⟨subd5_2_382, List.forall_mem_cons.2 ⟨subd5_2_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_384 : subd5_2 [-2, 3, 1] = true := by decide +kernel
theorem subd5_2_385 : subd5_2 [-2, 3, 2] = true := by decide +kernel
theorem subd5_2_386 : subd5_2 [-2, 3, 3] = true := by decide +kernel
theorem subd5_2_387 : subd5_2 [-2, 3, 4] = true := by decide +kernel
theorem subd5_2_388 : subd5_2 [-2, 3, 5] = true := by decide +kernel
theorem subd5_2_389 : subd5_2 [-2, 4] = true := by decide +kernel
theorem subd5_2_390 : subd5_2 [-2, 5] = true := by decide +kernel
theorem subd5_2_391 : subd5_2 [-2, 6] = true := by decide +kernel
theorem subd5_2_392 : subd5_2 [-1, -8] = true := by decide +kernel
theorem subd5_2_393 : subd5_2 [-1, -7] = true := by decide +kernel
theorem subd5_2_394 : subd5_2 [-1, -6] = true := by decide +kernel
theorem subd5_2_395 : subd5_2 [-1, -5, -6] = true := by decide +kernel
theorem subd5_2_396 : subd5_2 [-1, -5, -5] = true := by decide +kernel
theorem subd5_2_397 : subd5_2 [-1, -5, -4] = true := by decide +kernel
theorem subd5_2_398 : subd5_2 [-1, -5, -3] = true := by decide +kernel
theorem subd5_2_399 : subd5_2 [-1, -5, -2] = true := by decide +kernel
theorem subd5_2_400 : subd5_2 [-1, -5, -1] = true := by decide +kernel
theorem subd5_2_401 : subd5_2 [-1, -5, 0] = true := by decide +kernel
theorem subd5_2_402 : subd5_2 [-1, -5, 1] = true := by decide +kernel
theorem subd5_2_403 : subd5_2 [-1, -5, 2] = true := by decide +kernel
theorem subd5_2_404 : subd5_2 [-1, -5, 3] = true := by decide +kernel
theorem subd5_2_405 : subd5_2 [-1, -5, 4] = true := by decide +kernel
theorem subd5_2_406 : subd5_2 [-1, -5, 5] = true := by decide +kernel
theorem subd5_2_407 : subd5_2 [-1, -5, 6] = true := by decide +kernel
theorem subd5_2_408 : subd5_2 [-1, -5, 7] = true := by decide +kernel
theorem subd5_2_409 : subd5_2 [-1, -4, -7] = true := by decide +kernel
theorem subd5_2_410 : subd5_2 [-1, -4, -6] = true := by decide +kernel
theorem subd5_2_411 : subd5_2 [-1, -4, -5] = true := by decide +kernel
theorem subd5_2_412 : subd5_2 [-1, -4, -4] = true := by decide +kernel
theorem subd5_2_413 : subd5_2 [-1, -4, -3] = true := by decide +kernel
theorem subd5_2_414 : subd5_2 [-1, -4, -2] = true := by decide +kernel
theorem subd5_2_415 : subd5_2 [-1, -4, -1] = true := by decide +kernel
theorem sbd5_2_12 : ∀ q ∈ blkd5_2_12, subd5_2 q = true := by
  unfold blkd5_2_12
  exact List.forall_mem_cons.2 ⟨subd5_2_384, List.forall_mem_cons.2 ⟨subd5_2_385, List.forall_mem_cons.2 ⟨subd5_2_386, List.forall_mem_cons.2 ⟨subd5_2_387, List.forall_mem_cons.2 ⟨subd5_2_388, List.forall_mem_cons.2 ⟨subd5_2_389, List.forall_mem_cons.2 ⟨subd5_2_390, List.forall_mem_cons.2 ⟨subd5_2_391, List.forall_mem_cons.2 ⟨subd5_2_392, List.forall_mem_cons.2 ⟨subd5_2_393, List.forall_mem_cons.2 ⟨subd5_2_394, List.forall_mem_cons.2 ⟨subd5_2_395, List.forall_mem_cons.2 ⟨subd5_2_396, List.forall_mem_cons.2 ⟨subd5_2_397, List.forall_mem_cons.2 ⟨subd5_2_398, List.forall_mem_cons.2 ⟨subd5_2_399, List.forall_mem_cons.2 ⟨subd5_2_400, List.forall_mem_cons.2 ⟨subd5_2_401, List.forall_mem_cons.2 ⟨subd5_2_402, List.forall_mem_cons.2 ⟨subd5_2_403, List.forall_mem_cons.2 ⟨subd5_2_404, List.forall_mem_cons.2 ⟨subd5_2_405, List.forall_mem_cons.2 ⟨subd5_2_406, List.forall_mem_cons.2 ⟨subd5_2_407, List.forall_mem_cons.2 ⟨subd5_2_408, List.forall_mem_cons.2 ⟨subd5_2_409, List.forall_mem_cons.2 ⟨subd5_2_410, List.forall_mem_cons.2 ⟨subd5_2_411, List.forall_mem_cons.2 ⟨subd5_2_412, List.forall_mem_cons.2 ⟨subd5_2_413, List.forall_mem_cons.2 ⟨subd5_2_414, List.forall_mem_cons.2 ⟨subd5_2_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_416 : subd5_2 [-1, -4, 0] = true := by decide +kernel
theorem subd5_2_417 : subd5_2 [-1, -4, 1] = true := by decide +kernel
theorem subd5_2_418 : subd5_2 [-1, -4, 2] = true := by decide +kernel
theorem subd5_2_419 : subd5_2 [-1, -4, 3] = true := by decide +kernel
theorem subd5_2_420 : subd5_2 [-1, -4, 4] = true := by decide +kernel
theorem subd5_2_421 : subd5_2 [-1, -4, 5] = true := by decide +kernel
theorem subd5_2_422 : subd5_2 [-1, -4, 6] = true := by decide +kernel
theorem subd5_2_423 : subd5_2 [-1, -4, 7] = true := by decide +kernel
theorem subd5_2_424 : subd5_2 [-1, -4, 8] = true := by decide +kernel
theorem subd5_2_425 : subd5_2 [-1, -3, -8] = true := by decide +kernel
theorem subd5_2_426 : subd5_2 [-1, -3, -7] = true := by decide +kernel
theorem subd5_2_427 : subd5_2 [-1, -3, -6] = true := by decide +kernel
theorem subd5_2_428 : subd5_2 [-1, -3, -5] = true := by decide +kernel
theorem subd5_2_429 : subd5_2 [-1, -3, -4] = true := by decide +kernel
theorem subd5_2_430 : subd5_2 [-1, -3, -3] = true := by decide +kernel
theorem subd5_2_431 : subd5_2 [-1, -3, -2] = true := by decide +kernel
theorem subd5_2_432 : subd5_2 [-1, -3, -1] = true := by decide +kernel
theorem subd5_2_433 : subd5_2 [-1, -3, 0] = true := by decide +kernel
theorem subd5_2_434 : subd5_2 [-1, -3, 1] = true := by decide +kernel
theorem subd5_2_435 : subd5_2 [-1, -3, 2] = true := by decide +kernel
theorem subd5_2_436 : subd5_2 [-1, -3, 3] = true := by decide +kernel
theorem subd5_2_437 : subd5_2 [-1, -3, 4] = true := by decide +kernel
theorem subd5_2_438 : subd5_2 [-1, -3, 5] = true := by decide +kernel
theorem subd5_2_439 : subd5_2 [-1, -3, 6] = true := by decide +kernel
theorem subd5_2_440 : subd5_2 [-1, -3, 7] = true := by decide +kernel
theorem subd5_2_441 : subd5_2 [-1, -3, 8] = true := by decide +kernel
theorem subd5_2_442 : subd5_2 [-1, -2, -9] = true := by decide +kernel
theorem subd5_2_443 : subd5_2 [-1, -2, -8] = true := by decide +kernel
theorem subd5_2_444 : subd5_2 [-1, -2, -7] = true := by decide +kernel
theorem subd5_2_445 : subd5_2 [-1, -2, -6] = true := by decide +kernel
theorem subd5_2_446 : subd5_2 [-1, -2, -5] = true := by decide +kernel
theorem subd5_2_447 : subd5_2 [-1, -2, -4] = true := by decide +kernel
theorem sbd5_2_13 : ∀ q ∈ blkd5_2_13, subd5_2 q = true := by
  unfold blkd5_2_13
  exact List.forall_mem_cons.2 ⟨subd5_2_416, List.forall_mem_cons.2 ⟨subd5_2_417, List.forall_mem_cons.2 ⟨subd5_2_418, List.forall_mem_cons.2 ⟨subd5_2_419, List.forall_mem_cons.2 ⟨subd5_2_420, List.forall_mem_cons.2 ⟨subd5_2_421, List.forall_mem_cons.2 ⟨subd5_2_422, List.forall_mem_cons.2 ⟨subd5_2_423, List.forall_mem_cons.2 ⟨subd5_2_424, List.forall_mem_cons.2 ⟨subd5_2_425, List.forall_mem_cons.2 ⟨subd5_2_426, List.forall_mem_cons.2 ⟨subd5_2_427, List.forall_mem_cons.2 ⟨subd5_2_428, List.forall_mem_cons.2 ⟨subd5_2_429, List.forall_mem_cons.2 ⟨subd5_2_430, List.forall_mem_cons.2 ⟨subd5_2_431, List.forall_mem_cons.2 ⟨subd5_2_432, List.forall_mem_cons.2 ⟨subd5_2_433, List.forall_mem_cons.2 ⟨subd5_2_434, List.forall_mem_cons.2 ⟨subd5_2_435, List.forall_mem_cons.2 ⟨subd5_2_436, List.forall_mem_cons.2 ⟨subd5_2_437, List.forall_mem_cons.2 ⟨subd5_2_438, List.forall_mem_cons.2 ⟨subd5_2_439, List.forall_mem_cons.2 ⟨subd5_2_440, List.forall_mem_cons.2 ⟨subd5_2_441, List.forall_mem_cons.2 ⟨subd5_2_442, List.forall_mem_cons.2 ⟨subd5_2_443, List.forall_mem_cons.2 ⟨subd5_2_444, List.forall_mem_cons.2 ⟨subd5_2_445, List.forall_mem_cons.2 ⟨subd5_2_446, List.forall_mem_cons.2 ⟨subd5_2_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_448 : subd5_2 [-1, -2, -3] = true := by decide +kernel
theorem subd5_2_449 : subd5_2 [-1, -2, -2] = true := by decide +kernel
theorem subd5_2_450 : subd5_2 [-1, -2, -1] = true := by decide +kernel
theorem subd5_2_451 : subd5_2 [-1, -2, 0] = true := by decide +kernel
theorem subd5_2_452 : subd5_2 [-1, -2, 1] = true := by decide +kernel
theorem subd5_2_453 : subd5_2 [-1, -2, 2] = true := by decide +kernel
theorem subd5_2_454 : subd5_2 [-1, -2, 3] = true := by decide +kernel
theorem subd5_2_455 : subd5_2 [-1, -2, 4] = true := by decide +kernel
theorem subd5_2_456 : subd5_2 [-1, -2, 5] = true := by decide +kernel
theorem subd5_2_457 : subd5_2 [-1, -2, 6] = true := by decide +kernel
theorem subd5_2_458 : subd5_2 [-1, -2, 7] = true := by decide +kernel
theorem subd5_2_459 : subd5_2 [-1, -2, 8] = true := by decide +kernel
theorem subd5_2_460 : subd5_2 [-1, -1, -9] = true := by decide +kernel
theorem subd5_2_461 : subd5_2 [-1, -1, -8] = true := by decide +kernel
theorem subd5_2_462 : subd5_2 [-1, -1, -7] = true := by decide +kernel
theorem subd5_2_463 : subd5_2 [-1, -1, -6] = true := by decide +kernel
theorem subd5_2_464 : subd5_2 [-1, -1, -5] = true := by decide +kernel
theorem subd5_2_465 : subd5_2 [-1, -1, -4] = true := by decide +kernel
theorem subd5_2_466 : subd5_2 [-1, -1, -3] = true := by decide +kernel
theorem subd5_2_467 : subd5_2 [-1, -1, -2] = true := by decide +kernel
theorem subd5_2_468 : subd5_2 [-1, -1, -1] = true := by decide +kernel
theorem subd5_2_469 : subd5_2 [-1, -1, 0] = true := by decide +kernel
theorem subd5_2_470 : subd5_2 [-1, -1, 1] = true := by decide +kernel
theorem subd5_2_471 : subd5_2 [-1, -1, 2] = true := by decide +kernel
theorem subd5_2_472 : subd5_2 [-1, -1, 3] = true := by decide +kernel
theorem subd5_2_473 : subd5_2 [-1, -1, 4] = true := by decide +kernel
theorem subd5_2_474 : subd5_2 [-1, -1, 5] = true := by decide +kernel
theorem subd5_2_475 : subd5_2 [-1, -1, 6] = true := by decide +kernel
theorem subd5_2_476 : subd5_2 [-1, -1, 7] = true := by decide +kernel
theorem subd5_2_477 : subd5_2 [-1, -1, 8] = true := by decide +kernel
theorem subd5_2_478 : subd5_2 [-1, 0, -9] = true := by decide +kernel
theorem subd5_2_479 : subd5_2 [-1, 0, -8] = true := by decide +kernel
theorem sbd5_2_14 : ∀ q ∈ blkd5_2_14, subd5_2 q = true := by
  unfold blkd5_2_14
  exact List.forall_mem_cons.2 ⟨subd5_2_448, List.forall_mem_cons.2 ⟨subd5_2_449, List.forall_mem_cons.2 ⟨subd5_2_450, List.forall_mem_cons.2 ⟨subd5_2_451, List.forall_mem_cons.2 ⟨subd5_2_452, List.forall_mem_cons.2 ⟨subd5_2_453, List.forall_mem_cons.2 ⟨subd5_2_454, List.forall_mem_cons.2 ⟨subd5_2_455, List.forall_mem_cons.2 ⟨subd5_2_456, List.forall_mem_cons.2 ⟨subd5_2_457, List.forall_mem_cons.2 ⟨subd5_2_458, List.forall_mem_cons.2 ⟨subd5_2_459, List.forall_mem_cons.2 ⟨subd5_2_460, List.forall_mem_cons.2 ⟨subd5_2_461, List.forall_mem_cons.2 ⟨subd5_2_462, List.forall_mem_cons.2 ⟨subd5_2_463, List.forall_mem_cons.2 ⟨subd5_2_464, List.forall_mem_cons.2 ⟨subd5_2_465, List.forall_mem_cons.2 ⟨subd5_2_466, List.forall_mem_cons.2 ⟨subd5_2_467, List.forall_mem_cons.2 ⟨subd5_2_468, List.forall_mem_cons.2 ⟨subd5_2_469, List.forall_mem_cons.2 ⟨subd5_2_470, List.forall_mem_cons.2 ⟨subd5_2_471, List.forall_mem_cons.2 ⟨subd5_2_472, List.forall_mem_cons.2 ⟨subd5_2_473, List.forall_mem_cons.2 ⟨subd5_2_474, List.forall_mem_cons.2 ⟨subd5_2_475, List.forall_mem_cons.2 ⟨subd5_2_476, List.forall_mem_cons.2 ⟨subd5_2_477, List.forall_mem_cons.2 ⟨subd5_2_478, List.forall_mem_cons.2 ⟨subd5_2_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_480 : subd5_2 [-1, 0, -7] = true := by decide +kernel
theorem subd5_2_481 : subd5_2 [-1, 0, -6] = true := by decide +kernel
theorem subd5_2_482 : subd5_2 [-1, 0, -5] = true := by decide +kernel
theorem subd5_2_483 : subd5_2 [-1, 0, -4] = true := by decide +kernel
theorem subd5_2_484 : subd5_2 [-1, 0, -3] = true := by decide +kernel
theorem subd5_2_485 : subd5_2 [-1, 0, -2] = true := by decide +kernel
theorem subd5_2_486 : subd5_2 [-1, 0, -1] = true := by decide +kernel
theorem subd5_2_487 : subd5_2 [-1, 0, 0] = true := by decide +kernel
theorem subd5_2_488 : subd5_2 [-1, 0, 1] = true := by decide +kernel
theorem subd5_2_489 : subd5_2 [-1, 0, 2] = true := by decide +kernel
theorem subd5_2_490 : subd5_2 [-1, 0, 3] = true := by decide +kernel
theorem subd5_2_491 : subd5_2 [-1, 0, 4] = true := by decide +kernel
theorem subd5_2_492 : subd5_2 [-1, 0, 5] = true := by decide +kernel
theorem subd5_2_493 : subd5_2 [-1, 0, 6] = true := by decide +kernel
theorem subd5_2_494 : subd5_2 [-1, 0, 7] = true := by decide +kernel
theorem subd5_2_495 : subd5_2 [-1, 0, 8] = true := by decide +kernel
theorem subd5_2_496 : subd5_2 [-1, 1, -10] = true := by decide +kernel
theorem subd5_2_497 : subd5_2 [-1, 1, -9] = true := by decide +kernel
theorem subd5_2_498 : subd5_2 [-1, 1, -8] = true := by decide +kernel
theorem subd5_2_499 : subd5_2 [-1, 1, -7] = true := by decide +kernel
theorem subd5_2_500 : subd5_2 [-1, 1, -6] = true := by decide +kernel
theorem subd5_2_501 : subd5_2 [-1, 1, -5] = true := by decide +kernel
theorem subd5_2_502 : subd5_2 [-1, 1, -4] = true := by decide +kernel
theorem subd5_2_503 : subd5_2 [-1, 1, -3] = true := by decide +kernel
theorem subd5_2_504 : subd5_2 [-1, 1, -2] = true := by decide +kernel
theorem subd5_2_505 : subd5_2 [-1, 1, -1] = true := by decide +kernel
theorem subd5_2_506 : subd5_2 [-1, 1, 0] = true := by decide +kernel
theorem subd5_2_507 : subd5_2 [-1, 1, 1] = true := by decide +kernel
theorem subd5_2_508 : subd5_2 [-1, 1, 2] = true := by decide +kernel
theorem subd5_2_509 : subd5_2 [-1, 1, 3] = true := by decide +kernel
theorem subd5_2_510 : subd5_2 [-1, 1, 4] = true := by decide +kernel
theorem subd5_2_511 : subd5_2 [-1, 1, 5] = true := by decide +kernel
theorem sbd5_2_15 : ∀ q ∈ blkd5_2_15, subd5_2 q = true := by
  unfold blkd5_2_15
  exact List.forall_mem_cons.2 ⟨subd5_2_480, List.forall_mem_cons.2 ⟨subd5_2_481, List.forall_mem_cons.2 ⟨subd5_2_482, List.forall_mem_cons.2 ⟨subd5_2_483, List.forall_mem_cons.2 ⟨subd5_2_484, List.forall_mem_cons.2 ⟨subd5_2_485, List.forall_mem_cons.2 ⟨subd5_2_486, List.forall_mem_cons.2 ⟨subd5_2_487, List.forall_mem_cons.2 ⟨subd5_2_488, List.forall_mem_cons.2 ⟨subd5_2_489, List.forall_mem_cons.2 ⟨subd5_2_490, List.forall_mem_cons.2 ⟨subd5_2_491, List.forall_mem_cons.2 ⟨subd5_2_492, List.forall_mem_cons.2 ⟨subd5_2_493, List.forall_mem_cons.2 ⟨subd5_2_494, List.forall_mem_cons.2 ⟨subd5_2_495, List.forall_mem_cons.2 ⟨subd5_2_496, List.forall_mem_cons.2 ⟨subd5_2_497, List.forall_mem_cons.2 ⟨subd5_2_498, List.forall_mem_cons.2 ⟨subd5_2_499, List.forall_mem_cons.2 ⟨subd5_2_500, List.forall_mem_cons.2 ⟨subd5_2_501, List.forall_mem_cons.2 ⟨subd5_2_502, List.forall_mem_cons.2 ⟨subd5_2_503, List.forall_mem_cons.2 ⟨subd5_2_504, List.forall_mem_cons.2 ⟨subd5_2_505, List.forall_mem_cons.2 ⟨subd5_2_506, List.forall_mem_cons.2 ⟨subd5_2_507, List.forall_mem_cons.2 ⟨subd5_2_508, List.forall_mem_cons.2 ⟨subd5_2_509, List.forall_mem_cons.2 ⟨subd5_2_510, List.forall_mem_cons.2 ⟨subd5_2_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_512 : subd5_2 [-1, 1, 6] = true := by decide +kernel
theorem subd5_2_513 : subd5_2 [-1, 1, 7] = true := by decide +kernel
theorem subd5_2_514 : subd5_2 [-1, 2, -10] = true := by decide +kernel
theorem subd5_2_515 : subd5_2 [-1, 2, -9] = true := by decide +kernel
theorem subd5_2_516 : subd5_2 [-1, 2, -8] = true := by decide +kernel
theorem subd5_2_517 : subd5_2 [-1, 2, -7] = true := by decide +kernel
theorem subd5_2_518 : subd5_2 [-1, 2, -6] = true := by decide +kernel
theorem subd5_2_519 : subd5_2 [-1, 2, -5] = true := by decide +kernel
theorem subd5_2_520 : subd5_2 [-1, 2, -4] = true := by decide +kernel
theorem subd5_2_521 : subd5_2 [-1, 2, -3] = true := by decide +kernel
theorem subd5_2_522 : subd5_2 [-1, 2, -2] = true := by decide +kernel
theorem subd5_2_523 : subd5_2 [-1, 2, -1] = true := by decide +kernel
theorem subd5_2_524 : subd5_2 [-1, 2, 0] = true := by decide +kernel
theorem subd5_2_525 : subd5_2 [-1, 2, 1] = true := by decide +kernel
theorem subd5_2_526 : subd5_2 [-1, 2, 2] = true := by decide +kernel
theorem subd5_2_527 : subd5_2 [-1, 2, 3] = true := by decide +kernel
theorem subd5_2_528 : subd5_2 [-1, 2, 4] = true := by decide +kernel
theorem subd5_2_529 : subd5_2 [-1, 2, 5] = true := by decide +kernel
theorem subd5_2_530 : subd5_2 [-1, 2, 6] = true := by decide +kernel
theorem subd5_2_531 : subd5_2 [-1, 2, 7] = true := by decide +kernel
theorem subd5_2_532 : subd5_2 [-1, 3, -9] = true := by decide +kernel
theorem subd5_2_533 : subd5_2 [-1, 3, -8] = true := by decide +kernel
theorem subd5_2_534 : subd5_2 [-1, 3, -7] = true := by decide +kernel
theorem subd5_2_535 : subd5_2 [-1, 3, -6] = true := by decide +kernel
theorem subd5_2_536 : subd5_2 [-1, 3, -5] = true := by decide +kernel
theorem subd5_2_537 : subd5_2 [-1, 3, -4] = true := by decide +kernel
theorem subd5_2_538 : subd5_2 [-1, 3, -3] = true := by decide +kernel
theorem subd5_2_539 : subd5_2 [-1, 3, -2] = true := by decide +kernel
theorem subd5_2_540 : subd5_2 [-1, 3, -1] = true := by decide +kernel
theorem subd5_2_541 : subd5_2 [-1, 3, 0] = true := by decide +kernel
theorem subd5_2_542 : subd5_2 [-1, 3, 1] = true := by decide +kernel
theorem subd5_2_543 : subd5_2 [-1, 3, 2] = true := by decide +kernel
theorem sbd5_2_16 : ∀ q ∈ blkd5_2_16, subd5_2 q = true := by
  unfold blkd5_2_16
  exact List.forall_mem_cons.2 ⟨subd5_2_512, List.forall_mem_cons.2 ⟨subd5_2_513, List.forall_mem_cons.2 ⟨subd5_2_514, List.forall_mem_cons.2 ⟨subd5_2_515, List.forall_mem_cons.2 ⟨subd5_2_516, List.forall_mem_cons.2 ⟨subd5_2_517, List.forall_mem_cons.2 ⟨subd5_2_518, List.forall_mem_cons.2 ⟨subd5_2_519, List.forall_mem_cons.2 ⟨subd5_2_520, List.forall_mem_cons.2 ⟨subd5_2_521, List.forall_mem_cons.2 ⟨subd5_2_522, List.forall_mem_cons.2 ⟨subd5_2_523, List.forall_mem_cons.2 ⟨subd5_2_524, List.forall_mem_cons.2 ⟨subd5_2_525, List.forall_mem_cons.2 ⟨subd5_2_526, List.forall_mem_cons.2 ⟨subd5_2_527, List.forall_mem_cons.2 ⟨subd5_2_528, List.forall_mem_cons.2 ⟨subd5_2_529, List.forall_mem_cons.2 ⟨subd5_2_530, List.forall_mem_cons.2 ⟨subd5_2_531, List.forall_mem_cons.2 ⟨subd5_2_532, List.forall_mem_cons.2 ⟨subd5_2_533, List.forall_mem_cons.2 ⟨subd5_2_534, List.forall_mem_cons.2 ⟨subd5_2_535, List.forall_mem_cons.2 ⟨subd5_2_536, List.forall_mem_cons.2 ⟨subd5_2_537, List.forall_mem_cons.2 ⟨subd5_2_538, List.forall_mem_cons.2 ⟨subd5_2_539, List.forall_mem_cons.2 ⟨subd5_2_540, List.forall_mem_cons.2 ⟨subd5_2_541, List.forall_mem_cons.2 ⟨subd5_2_542, List.forall_mem_cons.2 ⟨subd5_2_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_544 : subd5_2 [-1, 3, 3] = true := by decide +kernel
theorem subd5_2_545 : subd5_2 [-1, 3, 4] = true := by decide +kernel
theorem subd5_2_546 : subd5_2 [-1, 3, 5] = true := by decide +kernel
theorem subd5_2_547 : subd5_2 [-1, 3, 6] = true := by decide +kernel
theorem subd5_2_548 : subd5_2 [-1, 4, -9] = true := by decide +kernel
theorem subd5_2_549 : subd5_2 [-1, 4, -8] = true := by decide +kernel
theorem subd5_2_550 : subd5_2 [-1, 4, -7] = true := by decide +kernel
theorem subd5_2_551 : subd5_2 [-1, 4, -6] = true := by decide +kernel
theorem subd5_2_552 : subd5_2 [-1, 4, -5] = true := by decide +kernel
theorem subd5_2_553 : subd5_2 [-1, 4, -4] = true := by decide +kernel
theorem subd5_2_554 : subd5_2 [-1, 4, -3] = true := by decide +kernel
theorem subd5_2_555 : subd5_2 [-1, 4, -2] = true := by decide +kernel
theorem subd5_2_556 : subd5_2 [-1, 4, -1] = true := by decide +kernel
theorem subd5_2_557 : subd5_2 [-1, 4, 0] = true := by decide +kernel
theorem subd5_2_558 : subd5_2 [-1, 4, 1] = true := by decide +kernel
theorem subd5_2_559 : subd5_2 [-1, 4, 2] = true := by decide +kernel
theorem subd5_2_560 : subd5_2 [-1, 4, 3] = true := by decide +kernel
theorem subd5_2_561 : subd5_2 [-1, 4, 4] = true := by decide +kernel
theorem subd5_2_562 : subd5_2 [-1, 4, 5] = true := by decide +kernel
theorem subd5_2_563 : subd5_2 [-1, 5] = true := by decide +kernel
theorem subd5_2_564 : subd5_2 [-1, 6] = true := by decide +kernel
theorem subd5_2_565 : subd5_2 [0, -8] = true := by decide +kernel
theorem subd5_2_566 : subd5_2 [0, -7] = true := by decide +kernel
theorem subd5_2_567 : subd5_2 [0, -6] = true := by decide +kernel
theorem subd5_2_568 : subd5_2 [0, -5, -6] = true := by decide +kernel
theorem subd5_2_569 : subd5_2 [0, -5, -5] = true := by decide +kernel
theorem subd5_2_570 : subd5_2 [0, -5, -4] = true := by decide +kernel
theorem subd5_2_571 : subd5_2 [0, -5, -3] = true := by decide +kernel
theorem subd5_2_572 : subd5_2 [0, -5, -2] = true := by decide +kernel
theorem subd5_2_573 : subd5_2 [0, -5, -1] = true := by decide +kernel
theorem subd5_2_574 : subd5_2 [0, -5, 0] = true := by decide +kernel
theorem subd5_2_575 : subd5_2 [0, -5, 1] = true := by decide +kernel
theorem sbd5_2_17 : ∀ q ∈ blkd5_2_17, subd5_2 q = true := by
  unfold blkd5_2_17
  exact List.forall_mem_cons.2 ⟨subd5_2_544, List.forall_mem_cons.2 ⟨subd5_2_545, List.forall_mem_cons.2 ⟨subd5_2_546, List.forall_mem_cons.2 ⟨subd5_2_547, List.forall_mem_cons.2 ⟨subd5_2_548, List.forall_mem_cons.2 ⟨subd5_2_549, List.forall_mem_cons.2 ⟨subd5_2_550, List.forall_mem_cons.2 ⟨subd5_2_551, List.forall_mem_cons.2 ⟨subd5_2_552, List.forall_mem_cons.2 ⟨subd5_2_553, List.forall_mem_cons.2 ⟨subd5_2_554, List.forall_mem_cons.2 ⟨subd5_2_555, List.forall_mem_cons.2 ⟨subd5_2_556, List.forall_mem_cons.2 ⟨subd5_2_557, List.forall_mem_cons.2 ⟨subd5_2_558, List.forall_mem_cons.2 ⟨subd5_2_559, List.forall_mem_cons.2 ⟨subd5_2_560, List.forall_mem_cons.2 ⟨subd5_2_561, List.forall_mem_cons.2 ⟨subd5_2_562, List.forall_mem_cons.2 ⟨subd5_2_563, List.forall_mem_cons.2 ⟨subd5_2_564, List.forall_mem_cons.2 ⟨subd5_2_565, List.forall_mem_cons.2 ⟨subd5_2_566, List.forall_mem_cons.2 ⟨subd5_2_567, List.forall_mem_cons.2 ⟨subd5_2_568, List.forall_mem_cons.2 ⟨subd5_2_569, List.forall_mem_cons.2 ⟨subd5_2_570, List.forall_mem_cons.2 ⟨subd5_2_571, List.forall_mem_cons.2 ⟨subd5_2_572, List.forall_mem_cons.2 ⟨subd5_2_573, List.forall_mem_cons.2 ⟨subd5_2_574, List.forall_mem_cons.2 ⟨subd5_2_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_576 : subd5_2 [0, -5, 2] = true := by decide +kernel
theorem subd5_2_577 : subd5_2 [0, -5, 3] = true := by decide +kernel
theorem subd5_2_578 : subd5_2 [0, -5, 4] = true := by decide +kernel
theorem subd5_2_579 : subd5_2 [0, -5, 5] = true := by decide +kernel
theorem subd5_2_580 : subd5_2 [0, -5, 6] = true := by decide +kernel
theorem subd5_2_581 : subd5_2 [0, -5, 7] = true := by decide +kernel
theorem subd5_2_582 : subd5_2 [0, -4, -7] = true := by decide +kernel
theorem subd5_2_583 : subd5_2 [0, -4, -6] = true := by decide +kernel
theorem subd5_2_584 : subd5_2 [0, -4, -5] = true := by decide +kernel
theorem subd5_2_585 : subd5_2 [0, -4, -4] = true := by decide +kernel
theorem subd5_2_586 : subd5_2 [0, -4, -3] = true := by decide +kernel
theorem subd5_2_587 : subd5_2 [0, -4, -2] = true := by decide +kernel
theorem subd5_2_588 : subd5_2 [0, -4, -1] = true := by decide +kernel
theorem subd5_2_589 : subd5_2 [0, -4, 0] = true := by decide +kernel
theorem subd5_2_590 : subd5_2 [0, -4, 1] = true := by decide +kernel
theorem subd5_2_591 : subd5_2 [0, -4, 2] = true := by decide +kernel
theorem subd5_2_592 : subd5_2 [0, -4, 3] = true := by decide +kernel
theorem subd5_2_593 : subd5_2 [0, -4, 4] = true := by decide +kernel
theorem subd5_2_594 : subd5_2 [0, -4, 5] = true := by decide +kernel
theorem subd5_2_595 : subd5_2 [0, -4, 6] = true := by decide +kernel
theorem subd5_2_596 : subd5_2 [0, -4, 7] = true := by decide +kernel
theorem subd5_2_597 : subd5_2 [0, -4, 8] = true := by decide +kernel
theorem subd5_2_598 : subd5_2 [0, -3, -8] = true := by decide +kernel
theorem subd5_2_599 : subd5_2 [0, -3, -7] = true := by decide +kernel
theorem subd5_2_600 : subd5_2 [0, -3, -6] = true := by decide +kernel
theorem subd5_2_601 : subd5_2 [0, -3, -5] = true := by decide +kernel
theorem subd5_2_602 : subd5_2 [0, -3, -4] = true := by decide +kernel
theorem subd5_2_603 : subd5_2 [0, -3, -3] = true := by decide +kernel
theorem subd5_2_604 : subd5_2 [0, -3, -2] = true := by decide +kernel
theorem subd5_2_605 : subd5_2 [0, -3, -1] = true := by decide +kernel
theorem subd5_2_606 : subd5_2 [0, -3, 0] = true := by decide +kernel
theorem subd5_2_607 : subd5_2 [0, -3, 1] = true := by decide +kernel
theorem sbd5_2_18 : ∀ q ∈ blkd5_2_18, subd5_2 q = true := by
  unfold blkd5_2_18
  exact List.forall_mem_cons.2 ⟨subd5_2_576, List.forall_mem_cons.2 ⟨subd5_2_577, List.forall_mem_cons.2 ⟨subd5_2_578, List.forall_mem_cons.2 ⟨subd5_2_579, List.forall_mem_cons.2 ⟨subd5_2_580, List.forall_mem_cons.2 ⟨subd5_2_581, List.forall_mem_cons.2 ⟨subd5_2_582, List.forall_mem_cons.2 ⟨subd5_2_583, List.forall_mem_cons.2 ⟨subd5_2_584, List.forall_mem_cons.2 ⟨subd5_2_585, List.forall_mem_cons.2 ⟨subd5_2_586, List.forall_mem_cons.2 ⟨subd5_2_587, List.forall_mem_cons.2 ⟨subd5_2_588, List.forall_mem_cons.2 ⟨subd5_2_589, List.forall_mem_cons.2 ⟨subd5_2_590, List.forall_mem_cons.2 ⟨subd5_2_591, List.forall_mem_cons.2 ⟨subd5_2_592, List.forall_mem_cons.2 ⟨subd5_2_593, List.forall_mem_cons.2 ⟨subd5_2_594, List.forall_mem_cons.2 ⟨subd5_2_595, List.forall_mem_cons.2 ⟨subd5_2_596, List.forall_mem_cons.2 ⟨subd5_2_597, List.forall_mem_cons.2 ⟨subd5_2_598, List.forall_mem_cons.2 ⟨subd5_2_599, List.forall_mem_cons.2 ⟨subd5_2_600, List.forall_mem_cons.2 ⟨subd5_2_601, List.forall_mem_cons.2 ⟨subd5_2_602, List.forall_mem_cons.2 ⟨subd5_2_603, List.forall_mem_cons.2 ⟨subd5_2_604, List.forall_mem_cons.2 ⟨subd5_2_605, List.forall_mem_cons.2 ⟨subd5_2_606, List.forall_mem_cons.2 ⟨subd5_2_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_608 : subd5_2 [0, -3, 2] = true := by decide +kernel
theorem subd5_2_609 : subd5_2 [0, -3, 3] = true := by decide +kernel
theorem subd5_2_610 : subd5_2 [0, -3, 4] = true := by decide +kernel
theorem subd5_2_611 : subd5_2 [0, -3, 5] = true := by decide +kernel
theorem subd5_2_612 : subd5_2 [0, -3, 6] = true := by decide +kernel
theorem subd5_2_613 : subd5_2 [0, -3, 7] = true := by decide +kernel
theorem subd5_2_614 : subd5_2 [0, -3, 8] = true := by decide +kernel
theorem subd5_2_615 : subd5_2 [0, -2, -8] = true := by decide +kernel
theorem subd5_2_616 : subd5_2 [0, -2, -7] = true := by decide +kernel
theorem subd5_2_617 : subd5_2 [0, -2, -6] = true := by decide +kernel
theorem subd5_2_618 : subd5_2 [0, -2, -5] = true := by decide +kernel
theorem subd5_2_619 : subd5_2 [0, -2, -4] = true := by decide +kernel
theorem subd5_2_620 : subd5_2 [0, -2, -3] = true := by decide +kernel
theorem subd5_2_621 : subd5_2 [0, -2, -2] = true := by decide +kernel
theorem subd5_2_622 : subd5_2 [0, -2, -1] = true := by decide +kernel
theorem subd5_2_623 : subd5_2 [0, -2, 0] = true := by decide +kernel
theorem subd5_2_624 : subd5_2 [0, -2, 1] = true := by decide +kernel
theorem subd5_2_625 : subd5_2 [0, -2, 2] = true := by decide +kernel
theorem subd5_2_626 : subd5_2 [0, -2, 3] = true := by decide +kernel
theorem subd5_2_627 : subd5_2 [0, -2, 4] = true := by decide +kernel
theorem subd5_2_628 : subd5_2 [0, -2, 5] = true := by decide +kernel
theorem subd5_2_629 : subd5_2 [0, -2, 6] = true := by decide +kernel
theorem subd5_2_630 : subd5_2 [0, -2, 7] = true := by decide +kernel
theorem subd5_2_631 : subd5_2 [0, -2, 8] = true := by decide +kernel
theorem subd5_2_632 : subd5_2 [0, -2, 9] = true := by decide +kernel
theorem subd5_2_633 : subd5_2 [0, -1, -9] = true := by decide +kernel
theorem subd5_2_634 : subd5_2 [0, -1, -8] = true := by decide +kernel
theorem subd5_2_635 : subd5_2 [0, -1, -7] = true := by decide +kernel
theorem subd5_2_636 : subd5_2 [0, -1, -6] = true := by decide +kernel
theorem subd5_2_637 : subd5_2 [0, -1, -5] = true := by decide +kernel
theorem subd5_2_638 : subd5_2 [0, -1, -4] = true := by decide +kernel
theorem subd5_2_639 : subd5_2 [0, -1, -3] = true := by decide +kernel
theorem sbd5_2_19 : ∀ q ∈ blkd5_2_19, subd5_2 q = true := by
  unfold blkd5_2_19
  exact List.forall_mem_cons.2 ⟨subd5_2_608, List.forall_mem_cons.2 ⟨subd5_2_609, List.forall_mem_cons.2 ⟨subd5_2_610, List.forall_mem_cons.2 ⟨subd5_2_611, List.forall_mem_cons.2 ⟨subd5_2_612, List.forall_mem_cons.2 ⟨subd5_2_613, List.forall_mem_cons.2 ⟨subd5_2_614, List.forall_mem_cons.2 ⟨subd5_2_615, List.forall_mem_cons.2 ⟨subd5_2_616, List.forall_mem_cons.2 ⟨subd5_2_617, List.forall_mem_cons.2 ⟨subd5_2_618, List.forall_mem_cons.2 ⟨subd5_2_619, List.forall_mem_cons.2 ⟨subd5_2_620, List.forall_mem_cons.2 ⟨subd5_2_621, List.forall_mem_cons.2 ⟨subd5_2_622, List.forall_mem_cons.2 ⟨subd5_2_623, List.forall_mem_cons.2 ⟨subd5_2_624, List.forall_mem_cons.2 ⟨subd5_2_625, List.forall_mem_cons.2 ⟨subd5_2_626, List.forall_mem_cons.2 ⟨subd5_2_627, List.forall_mem_cons.2 ⟨subd5_2_628, List.forall_mem_cons.2 ⟨subd5_2_629, List.forall_mem_cons.2 ⟨subd5_2_630, List.forall_mem_cons.2 ⟨subd5_2_631, List.forall_mem_cons.2 ⟨subd5_2_632, List.forall_mem_cons.2 ⟨subd5_2_633, List.forall_mem_cons.2 ⟨subd5_2_634, List.forall_mem_cons.2 ⟨subd5_2_635, List.forall_mem_cons.2 ⟨subd5_2_636, List.forall_mem_cons.2 ⟨subd5_2_637, List.forall_mem_cons.2 ⟨subd5_2_638, List.forall_mem_cons.2 ⟨subd5_2_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_640 : subd5_2 [0, -1, -2] = true := by decide +kernel
theorem subd5_2_641 : subd5_2 [0, -1, -1] = true := by decide +kernel
theorem subd5_2_642 : subd5_2 [0, -1, 0] = true := by decide +kernel
theorem subd5_2_643 : subd5_2 [0, -1, 1] = true := by decide +kernel
theorem subd5_2_644 : subd5_2 [0, -1, 2] = true := by decide +kernel
theorem subd5_2_645 : subd5_2 [0, -1, 3] = true := by decide +kernel
theorem subd5_2_646 : subd5_2 [0, -1, 4] = true := by decide +kernel
theorem subd5_2_647 : subd5_2 [0, -1, 5] = true := by decide +kernel
theorem subd5_2_648 : subd5_2 [0, -1, 6] = true := by decide +kernel
theorem subd5_2_649 : subd5_2 [0, -1, 7] = true := by decide +kernel
theorem subd5_2_650 : subd5_2 [0, -1, 8] = true := by decide +kernel
theorem subd5_2_651 : subd5_2 [0, 0, -9] = true := by decide +kernel
theorem subd5_2_652 : subd5_2 [0, 0, -8] = true := by decide +kernel
theorem subd5_2_653 : subd5_2 [0, 0, -7] = true := by decide +kernel
theorem subd5_2_654 : subd5_2 [0, 0, -6] = true := by decide +kernel
theorem subd5_2_655 : subd5_2 [0, 0, -5] = true := by decide +kernel
theorem subd5_2_656 : subd5_2 [0, 0, -4] = true := by decide +kernel
theorem subd5_2_657 : subd5_2 [0, 0, -3] = true := by decide +kernel
theorem subd5_2_658 : subd5_2 [0, 0, -2] = true := by decide +kernel
theorem subd5_2_659 : subd5_2 [0, 0, -1] = true := by decide +kernel
theorem subd5_2_660 : subd5_2 [0, 0, 0] = true := by decide +kernel
theorem subd5_2_661 : subd5_2 [0, 0, 1] = true := by decide +kernel
theorem subd5_2_662 : subd5_2 [0, 0, 2] = true := by decide +kernel
theorem subd5_2_663 : subd5_2 [0, 0, 3] = true := by decide +kernel
theorem subd5_2_664 : subd5_2 [0, 0, 4] = true := by decide +kernel
theorem subd5_2_665 : subd5_2 [0, 0, 5] = true := by decide +kernel
theorem subd5_2_666 : subd5_2 [0, 0, 6] = true := by decide +kernel
theorem subd5_2_667 : subd5_2 [0, 0, 7] = true := by decide +kernel
theorem subd5_2_668 : subd5_2 [0, 0, 8] = true := by decide +kernel
theorem subd5_2_669 : subd5_2 [0, 1, -9] = true := by decide +kernel
theorem subd5_2_670 : subd5_2 [0, 1, -8] = true := by decide +kernel
theorem subd5_2_671 : subd5_2 [0, 1, -7] = true := by decide +kernel
theorem sbd5_2_20 : ∀ q ∈ blkd5_2_20, subd5_2 q = true := by
  unfold blkd5_2_20
  exact List.forall_mem_cons.2 ⟨subd5_2_640, List.forall_mem_cons.2 ⟨subd5_2_641, List.forall_mem_cons.2 ⟨subd5_2_642, List.forall_mem_cons.2 ⟨subd5_2_643, List.forall_mem_cons.2 ⟨subd5_2_644, List.forall_mem_cons.2 ⟨subd5_2_645, List.forall_mem_cons.2 ⟨subd5_2_646, List.forall_mem_cons.2 ⟨subd5_2_647, List.forall_mem_cons.2 ⟨subd5_2_648, List.forall_mem_cons.2 ⟨subd5_2_649, List.forall_mem_cons.2 ⟨subd5_2_650, List.forall_mem_cons.2 ⟨subd5_2_651, List.forall_mem_cons.2 ⟨subd5_2_652, List.forall_mem_cons.2 ⟨subd5_2_653, List.forall_mem_cons.2 ⟨subd5_2_654, List.forall_mem_cons.2 ⟨subd5_2_655, List.forall_mem_cons.2 ⟨subd5_2_656, List.forall_mem_cons.2 ⟨subd5_2_657, List.forall_mem_cons.2 ⟨subd5_2_658, List.forall_mem_cons.2 ⟨subd5_2_659, List.forall_mem_cons.2 ⟨subd5_2_660, List.forall_mem_cons.2 ⟨subd5_2_661, List.forall_mem_cons.2 ⟨subd5_2_662, List.forall_mem_cons.2 ⟨subd5_2_663, List.forall_mem_cons.2 ⟨subd5_2_664, List.forall_mem_cons.2 ⟨subd5_2_665, List.forall_mem_cons.2 ⟨subd5_2_666, List.forall_mem_cons.2 ⟨subd5_2_667, List.forall_mem_cons.2 ⟨subd5_2_668, List.forall_mem_cons.2 ⟨subd5_2_669, List.forall_mem_cons.2 ⟨subd5_2_670, List.forall_mem_cons.2 ⟨subd5_2_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C121
