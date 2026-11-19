import ReflectZphi.Data.Cert5.C097.Base

namespace ReflectZphi.Data.Cert5.C097
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub7_224 : sub7 [0, 2, 4] = true := by decide +kernel
theorem sub7_225 : sub7 [0, 2, 5] = true := by decide +kernel
theorem sub7_226 : sub7 [0, 2, 6] = true := by decide +kernel
theorem sub7_227 : sub7 [0, 3] = true := by decide +kernel
theorem sub7_228 : sub7 [0, 4] = true := by decide +kernel
theorem sub7_229 : sub7 [0, 5] = true := by decide +kernel
theorem sub7_230 : sub7 [0, 6] = true := by decide +kernel
theorem sub7_231 : sub7 [0, 7] = true := by decide +kernel
theorem sub7_232 : sub7 [1, -8] = true := by decide +kernel
theorem sub7_233 : sub7 [1, -7] = true := by decide +kernel
theorem sub7_234 : sub7 [1, -6] = true := by decide +kernel
theorem sub7_235 : sub7 [1, -5] = true := by decide +kernel
theorem sub7_236 : sub7 [1, -4] = true := by decide +kernel
theorem sub7_237 : sub7 [1, -3] = true := by decide +kernel
theorem sub7_238 : sub7 [1, -2, -7] = true := by decide +kernel
theorem sub7_239 : sub7 [1, -2, -6] = true := by decide +kernel
theorem sub7_240 : sub7 [1, -2, -5] = true := by decide +kernel
theorem sub7_241 : sub7 [1, -2, -4] = true := by decide +kernel
theorem sub7_242 : sub7 [1, -2, -3] = true := by decide +kernel
theorem sub7_243 : sub7 [1, -2, -2] = true := by decide +kernel
theorem sub7_244 : sub7 [1, -2, -1] = true := by decide +kernel
theorem sub7_245 : sub7 [1, -2, 0] = true := by decide +kernel
theorem sub7_246 : sub7 [1, -2, 1] = true := by decide +kernel
theorem sub7_247 : sub7 [1, -2, 2] = true := by decide +kernel
theorem sub7_248 : sub7 [1, -2, 3] = true := by decide +kernel
theorem sub7_249 : sub7 [1, -2, 4] = true := by decide +kernel
theorem sub7_250 : sub7 [1, -2, 5] = true := by decide +kernel
theorem sub7_251 : sub7 [1, -1, -7] = true := by decide +kernel
theorem sub7_252 : sub7 [1, -1, -6] = true := by decide +kernel
theorem sub7_253 : sub7 [1, -1, -5] = true := by decide +kernel
theorem sub7_254 : sub7 [1, -1, -4] = true := by decide +kernel
theorem sub7_255 : sub7 [1, -1, -3] = true := by decide +kernel
theorem sb7_7 : ∀ q ∈ blk7_7, sub7 q = true := by
  unfold blk7_7
  exact List.forall_mem_cons.2 ⟨sub7_224, List.forall_mem_cons.2 ⟨sub7_225, List.forall_mem_cons.2 ⟨sub7_226, List.forall_mem_cons.2 ⟨sub7_227, List.forall_mem_cons.2 ⟨sub7_228, List.forall_mem_cons.2 ⟨sub7_229, List.forall_mem_cons.2 ⟨sub7_230, List.forall_mem_cons.2 ⟨sub7_231, List.forall_mem_cons.2 ⟨sub7_232, List.forall_mem_cons.2 ⟨sub7_233, List.forall_mem_cons.2 ⟨sub7_234, List.forall_mem_cons.2 ⟨sub7_235, List.forall_mem_cons.2 ⟨sub7_236, List.forall_mem_cons.2 ⟨sub7_237, List.forall_mem_cons.2 ⟨sub7_238, List.forall_mem_cons.2 ⟨sub7_239, List.forall_mem_cons.2 ⟨sub7_240, List.forall_mem_cons.2 ⟨sub7_241, List.forall_mem_cons.2 ⟨sub7_242, List.forall_mem_cons.2 ⟨sub7_243, List.forall_mem_cons.2 ⟨sub7_244, List.forall_mem_cons.2 ⟨sub7_245, List.forall_mem_cons.2 ⟨sub7_246, List.forall_mem_cons.2 ⟨sub7_247, List.forall_mem_cons.2 ⟨sub7_248, List.forall_mem_cons.2 ⟨sub7_249, List.forall_mem_cons.2 ⟨sub7_250, List.forall_mem_cons.2 ⟨sub7_251, List.forall_mem_cons.2 ⟨sub7_252, List.forall_mem_cons.2 ⟨sub7_253, List.forall_mem_cons.2 ⟨sub7_254, List.forall_mem_cons.2 ⟨sub7_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_256 : sub7 [1, -1, -2] = true := by decide +kernel
theorem sub7_257 : sub7 [1, -1, -1] = true := by decide +kernel
theorem sub7_258 : sub7 [1, -1, 0] = true := by decide +kernel
theorem sub7_259 : sub7 [1, -1, 1] = true := by decide +kernel
theorem sub7_260 : sub7 [1, -1, 2] = true := by decide +kernel
theorem sub7_261 : sub7 [1, -1, 3] = true := by decide +kernel
theorem sub7_262 : sub7 [1, -1, 4] = true := by decide +kernel
theorem sub7_263 : sub7 [1, -1, 5] = true := by decide +kernel
theorem sub7_264 : sub7 [1, -1, 6] = true := by decide +kernel
theorem sub7_265 : sub7 [1, 0, -6] = true := by decide +kernel
theorem sub7_266 : sub7 [1, 0, -5] = true := by decide +kernel
theorem sub7_267 : sub7 [1, 0, -4] = true := by decide +kernel
theorem sub7_268 : sub7 [1, 0, -3] = true := by decide +kernel
theorem sub7_269 : sub7 [1, 0, -2] = true := by decide +kernel
theorem sub7_270 : sub7 [1, 0, -1] = true := by decide +kernel
theorem sub7_271 : sub7 [1, 0, 0] = true := by decide +kernel
theorem sub7_272 : sub7 [1, 0, 1] = true := by decide +kernel
theorem sub7_273 : sub7 [1, 0, 2] = true := by decide +kernel
theorem sub7_274 : sub7 [1, 0, 3] = true := by decide +kernel
theorem sub7_275 : sub7 [1, 0, 4] = true := by decide +kernel
theorem sub7_276 : sub7 [1, 0, 5] = true := by decide +kernel
theorem sub7_277 : sub7 [1, 0, 6] = true := by decide +kernel
theorem sub7_278 : sub7 [1, 1, -6] = true := by decide +kernel
theorem sub7_279 : sub7 [1, 1, -5] = true := by decide +kernel
theorem sub7_280 : sub7 [1, 1, -4] = true := by decide +kernel
theorem sub7_281 : sub7 [1, 1, -3] = true := by decide +kernel
theorem sub7_282 : sub7 [1, 1, -2] = true := by decide +kernel
theorem sub7_283 : sub7 [1, 1, -1] = true := by decide +kernel
theorem sub7_284 : sub7 [1, 1, 0] = true := by decide +kernel
theorem sub7_285 : sub7 [1, 1, 1] = true := by decide +kernel
theorem sub7_286 : sub7 [1, 1, 2] = true := by decide +kernel
theorem sub7_287 : sub7 [1, 1, 3] = true := by decide +kernel
theorem sb7_8 : ∀ q ∈ blk7_8, sub7 q = true := by
  unfold blk7_8
  exact List.forall_mem_cons.2 ⟨sub7_256, List.forall_mem_cons.2 ⟨sub7_257, List.forall_mem_cons.2 ⟨sub7_258, List.forall_mem_cons.2 ⟨sub7_259, List.forall_mem_cons.2 ⟨sub7_260, List.forall_mem_cons.2 ⟨sub7_261, List.forall_mem_cons.2 ⟨sub7_262, List.forall_mem_cons.2 ⟨sub7_263, List.forall_mem_cons.2 ⟨sub7_264, List.forall_mem_cons.2 ⟨sub7_265, List.forall_mem_cons.2 ⟨sub7_266, List.forall_mem_cons.2 ⟨sub7_267, List.forall_mem_cons.2 ⟨sub7_268, List.forall_mem_cons.2 ⟨sub7_269, List.forall_mem_cons.2 ⟨sub7_270, List.forall_mem_cons.2 ⟨sub7_271, List.forall_mem_cons.2 ⟨sub7_272, List.forall_mem_cons.2 ⟨sub7_273, List.forall_mem_cons.2 ⟨sub7_274, List.forall_mem_cons.2 ⟨sub7_275, List.forall_mem_cons.2 ⟨sub7_276, List.forall_mem_cons.2 ⟨sub7_277, List.forall_mem_cons.2 ⟨sub7_278, List.forall_mem_cons.2 ⟨sub7_279, List.forall_mem_cons.2 ⟨sub7_280, List.forall_mem_cons.2 ⟨sub7_281, List.forall_mem_cons.2 ⟨sub7_282, List.forall_mem_cons.2 ⟨sub7_283, List.forall_mem_cons.2 ⟨sub7_284, List.forall_mem_cons.2 ⟨sub7_285, List.forall_mem_cons.2 ⟨sub7_286, List.forall_mem_cons.2 ⟨sub7_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_288 : sub7 [1, 1, 4] = true := by decide +kernel
theorem sub7_289 : sub7 [1, 1, 5] = true := by decide +kernel
theorem sub7_290 : sub7 [1, 1, 6] = true := by decide +kernel
theorem sub7_291 : sub7 [1, 2, -5] = true := by decide +kernel
theorem sub7_292 : sub7 [1, 2, -4] = true := by decide +kernel
theorem sub7_293 : sub7 [1, 2, -3] = true := by decide +kernel
theorem sub7_294 : sub7 [1, 2, -2] = true := by decide +kernel
theorem sub7_295 : sub7 [1, 2, -1] = true := by decide +kernel
theorem sub7_296 : sub7 [1, 2, 0] = true := by decide +kernel
theorem sub7_297 : sub7 [1, 2, 1] = true := by decide +kernel
theorem sub7_298 : sub7 [1, 2, 2] = true := by decide +kernel
theorem sub7_299 : sub7 [1, 2, 3] = true := by decide +kernel
theorem sub7_300 : sub7 [1, 2, 4] = true := by decide +kernel
theorem sub7_301 : sub7 [1, 2, 5] = true := by decide +kernel
theorem sub7_302 : sub7 [1, 2, 6] = true := by decide +kernel
theorem sub7_303 : sub7 [1, 3] = true := by decide +kernel
theorem sub7_304 : sub7 [1, 4] = true := by decide +kernel
theorem sub7_305 : sub7 [1, 5] = true := by decide +kernel
theorem sub7_306 : sub7 [1, 6] = true := by decide +kernel
theorem sub7_307 : sub7 [1, 7] = true := by decide +kernel
theorem sub7_308 : sub7 [2, -8] = true := by decide +kernel
theorem sub7_309 : sub7 [2, -7] = true := by decide +kernel
theorem sub7_310 : sub7 [2, -6] = true := by decide +kernel
theorem sub7_311 : sub7 [2, -5] = true := by decide +kernel
theorem sub7_312 : sub7 [2, -4] = true := by decide +kernel
theorem sub7_313 : sub7 [2, -3] = true := by decide +kernel
theorem sub7_314 : sub7 [2, -2] = true := by decide +kernel
theorem sub7_315 : sub7 [2, -1, -6] = true := by decide +kernel
theorem sub7_316 : sub7 [2, -1, -5] = true := by decide +kernel
theorem sub7_317 : sub7 [2, -1, -4] = true := by decide +kernel
theorem sub7_318 : sub7 [2, -1, -3] = true := by decide +kernel
theorem sub7_319 : sub7 [2, -1, -2] = true := by decide +kernel
theorem sb7_9 : ∀ q ∈ blk7_9, sub7 q = true := by
  unfold blk7_9
  exact List.forall_mem_cons.2 ⟨sub7_288, List.forall_mem_cons.2 ⟨sub7_289, List.forall_mem_cons.2 ⟨sub7_290, List.forall_mem_cons.2 ⟨sub7_291, List.forall_mem_cons.2 ⟨sub7_292, List.forall_mem_cons.2 ⟨sub7_293, List.forall_mem_cons.2 ⟨sub7_294, List.forall_mem_cons.2 ⟨sub7_295, List.forall_mem_cons.2 ⟨sub7_296, List.forall_mem_cons.2 ⟨sub7_297, List.forall_mem_cons.2 ⟨sub7_298, List.forall_mem_cons.2 ⟨sub7_299, List.forall_mem_cons.2 ⟨sub7_300, List.forall_mem_cons.2 ⟨sub7_301, List.forall_mem_cons.2 ⟨sub7_302, List.forall_mem_cons.2 ⟨sub7_303, List.forall_mem_cons.2 ⟨sub7_304, List.forall_mem_cons.2 ⟨sub7_305, List.forall_mem_cons.2 ⟨sub7_306, List.forall_mem_cons.2 ⟨sub7_307, List.forall_mem_cons.2 ⟨sub7_308, List.forall_mem_cons.2 ⟨sub7_309, List.forall_mem_cons.2 ⟨sub7_310, List.forall_mem_cons.2 ⟨sub7_311, List.forall_mem_cons.2 ⟨sub7_312, List.forall_mem_cons.2 ⟨sub7_313, List.forall_mem_cons.2 ⟨sub7_314, List.forall_mem_cons.2 ⟨sub7_315, List.forall_mem_cons.2 ⟨sub7_316, List.forall_mem_cons.2 ⟨sub7_317, List.forall_mem_cons.2 ⟨sub7_318, List.forall_mem_cons.2 ⟨sub7_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_320 : sub7 [2, -1, -1] = true := by decide +kernel
theorem sub7_321 : sub7 [2, -1, 0] = true := by decide +kernel
theorem sub7_322 : sub7 [2, -1, 1] = true := by decide +kernel
theorem sub7_323 : sub7 [2, -1, 2] = true := by decide +kernel
theorem sub7_324 : sub7 [2, -1, 3] = true := by decide +kernel
theorem sub7_325 : sub7 [2, -1, 4] = true := by decide +kernel
theorem sub7_326 : sub7 [2, -1, 5] = true := by decide +kernel
theorem sub7_327 : sub7 [2, -1, 6] = true := by decide +kernel
theorem sub7_328 : sub7 [2, 0, -6] = true := by decide +kernel
theorem sub7_329 : sub7 [2, 0, -5] = true := by decide +kernel
theorem sub7_330 : sub7 [2, 0, -4] = true := by decide +kernel
theorem sub7_331 : sub7 [2, 0, -3] = true := by decide +kernel
theorem sub7_332 : sub7 [2, 0, -2] = true := by decide +kernel
theorem sub7_333 : sub7 [2, 0, -1] = true := by decide +kernel
theorem sub7_334 : sub7 [2, 0, 0] = true := by decide +kernel
theorem sub7_335 : sub7 [2, 0, 1] = true := by decide +kernel
theorem sub7_336 : sub7 [2, 0, 2] = true := by decide +kernel
theorem sub7_337 : sub7 [2, 0, 3] = true := by decide +kernel
theorem sub7_338 : sub7 [2, 0, 4] = true := by decide +kernel
theorem sub7_339 : sub7 [2, 0, 5] = true := by decide +kernel
theorem sub7_340 : sub7 [2, 0, 6] = true := by decide +kernel
theorem sub7_341 : sub7 [2, 1] = true := by decide +kernel
theorem sub7_342 : sub7 [2, 2] = true := by decide +kernel
theorem sub7_343 : sub7 [2, 3] = true := by decide +kernel
theorem sub7_344 : sub7 [2, 4] = true := by decide +kernel
theorem sub7_345 : sub7 [2, 5] = true := by decide +kernel
theorem sub7_346 : sub7 [2, 6] = true := by decide +kernel
theorem sub7_347 : sub7 [2, 7] = true := by decide +kernel
theorem sub7_348 : sub7 [3, -7] = true := by decide +kernel
theorem sub7_349 : sub7 [3, -6] = true := by decide +kernel
theorem sub7_350 : sub7 [3, -5] = true := by decide +kernel
theorem sub7_351 : sub7 [3, -4] = true := by decide +kernel
theorem sb7_10 : ∀ q ∈ blk7_10, sub7 q = true := by
  unfold blk7_10
  exact List.forall_mem_cons.2 ⟨sub7_320, List.forall_mem_cons.2 ⟨sub7_321, List.forall_mem_cons.2 ⟨sub7_322, List.forall_mem_cons.2 ⟨sub7_323, List.forall_mem_cons.2 ⟨sub7_324, List.forall_mem_cons.2 ⟨sub7_325, List.forall_mem_cons.2 ⟨sub7_326, List.forall_mem_cons.2 ⟨sub7_327, List.forall_mem_cons.2 ⟨sub7_328, List.forall_mem_cons.2 ⟨sub7_329, List.forall_mem_cons.2 ⟨sub7_330, List.forall_mem_cons.2 ⟨sub7_331, List.forall_mem_cons.2 ⟨sub7_332, List.forall_mem_cons.2 ⟨sub7_333, List.forall_mem_cons.2 ⟨sub7_334, List.forall_mem_cons.2 ⟨sub7_335, List.forall_mem_cons.2 ⟨sub7_336, List.forall_mem_cons.2 ⟨sub7_337, List.forall_mem_cons.2 ⟨sub7_338, List.forall_mem_cons.2 ⟨sub7_339, List.forall_mem_cons.2 ⟨sub7_340, List.forall_mem_cons.2 ⟨sub7_341, List.forall_mem_cons.2 ⟨sub7_342, List.forall_mem_cons.2 ⟨sub7_343, List.forall_mem_cons.2 ⟨sub7_344, List.forall_mem_cons.2 ⟨sub7_345, List.forall_mem_cons.2 ⟨sub7_346, List.forall_mem_cons.2 ⟨sub7_347, List.forall_mem_cons.2 ⟨sub7_348, List.forall_mem_cons.2 ⟨sub7_349, List.forall_mem_cons.2 ⟨sub7_350, List.forall_mem_cons.2 ⟨sub7_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_352 : sub7 [3, -3] = true := by decide +kernel
theorem sub7_353 : sub7 [3, -2] = true := by decide +kernel
theorem sub7_354 : sub7 [3, -1] = true := by decide +kernel
theorem sub7_355 : sub7 [3, 0] = true := by decide +kernel
theorem sub7_356 : sub7 [3, 1] = true := by decide +kernel
theorem sub7_357 : sub7 [3, 2] = true := by decide +kernel
theorem sub7_358 : sub7 [3, 3] = true := by decide +kernel
theorem sub7_359 : sub7 [3, 4] = true := by decide +kernel
theorem sub7_360 : sub7 [3, 5] = true := by decide +kernel
theorem sub7_361 : sub7 [3, 6] = true := by decide +kernel
theorem sub7_362 : sub7 [4, -7] = true := by decide +kernel
theorem sub7_363 : sub7 [4, -6] = true := by decide +kernel
theorem sub7_364 : sub7 [4, -5] = true := by decide +kernel
theorem sub7_365 : sub7 [4, -4] = true := by decide +kernel
theorem sub7_366 : sub7 [4, -3] = true := by decide +kernel
theorem sub7_367 : sub7 [4, -2] = true := by decide +kernel
theorem sub7_368 : sub7 [4, -1] = true := by decide +kernel
theorem sub7_369 : sub7 [4, 0] = true := by decide +kernel
theorem sub7_370 : sub7 [4, 1] = true := by decide +kernel
theorem sub7_371 : sub7 [4, 2] = true := by decide +kernel
theorem sub7_372 : sub7 [4, 3] = true := by decide +kernel
theorem sub7_373 : sub7 [4, 4] = true := by decide +kernel
theorem sub7_374 : sub7 [4, 5] = true := by decide +kernel
theorem sub7_375 : sub7 [5, -6] = true := by decide +kernel
theorem sub7_376 : sub7 [5, -5] = true := by decide +kernel
theorem sub7_377 : sub7 [5, -4] = true := by decide +kernel
theorem sub7_378 : sub7 [5, -3] = true := by decide +kernel
theorem sub7_379 : sub7 [5, -2] = true := by decide +kernel
theorem sub7_380 : sub7 [5, -1] = true := by decide +kernel
theorem sub7_381 : sub7 [5, 0] = true := by decide +kernel
theorem sub7_382 : sub7 [5, 1] = true := by decide +kernel
theorem sub7_383 : sub7 [5, 2] = true := by decide +kernel
theorem sb7_11 : ∀ q ∈ blk7_11, sub7 q = true := by
  unfold blk7_11
  exact List.forall_mem_cons.2 ⟨sub7_352, List.forall_mem_cons.2 ⟨sub7_353, List.forall_mem_cons.2 ⟨sub7_354, List.forall_mem_cons.2 ⟨sub7_355, List.forall_mem_cons.2 ⟨sub7_356, List.forall_mem_cons.2 ⟨sub7_357, List.forall_mem_cons.2 ⟨sub7_358, List.forall_mem_cons.2 ⟨sub7_359, List.forall_mem_cons.2 ⟨sub7_360, List.forall_mem_cons.2 ⟨sub7_361, List.forall_mem_cons.2 ⟨sub7_362, List.forall_mem_cons.2 ⟨sub7_363, List.forall_mem_cons.2 ⟨sub7_364, List.forall_mem_cons.2 ⟨sub7_365, List.forall_mem_cons.2 ⟨sub7_366, List.forall_mem_cons.2 ⟨sub7_367, List.forall_mem_cons.2 ⟨sub7_368, List.forall_mem_cons.2 ⟨sub7_369, List.forall_mem_cons.2 ⟨sub7_370, List.forall_mem_cons.2 ⟨sub7_371, List.forall_mem_cons.2 ⟨sub7_372, List.forall_mem_cons.2 ⟨sub7_373, List.forall_mem_cons.2 ⟨sub7_374, List.forall_mem_cons.2 ⟨sub7_375, List.forall_mem_cons.2 ⟨sub7_376, List.forall_mem_cons.2 ⟨sub7_377, List.forall_mem_cons.2 ⟨sub7_378, List.forall_mem_cons.2 ⟨sub7_379, List.forall_mem_cons.2 ⟨sub7_380, List.forall_mem_cons.2 ⟨sub7_381, List.forall_mem_cons.2 ⟨sub7_382, List.forall_mem_cons.2 ⟨sub7_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_384 : sub7 [5, 3] = true := by decide +kernel
theorem sub7_385 : sub7 [5, 4] = true := by decide +kernel
theorem sub7_386 : sub7 [6] = true := by decide +kernel
theorem sb7_12 : ∀ q ∈ blk7_12, sub7 q = true := by
  unfold blk7_12
  exact List.forall_mem_cons.2 ⟨sub7_384, List.forall_mem_cons.2 ⟨sub7_385, List.forall_mem_cons.2 ⟨sub7_386, List.forall_mem_nil _⟩⟩⟩

end ReflectZphi.Data.Cert5.C097
