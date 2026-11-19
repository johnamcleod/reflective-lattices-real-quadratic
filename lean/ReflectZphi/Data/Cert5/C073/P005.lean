import ReflectZphi.Data.Cert5.C073.Base

namespace ReflectZphi.Data.Cert5.C073
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub5_224 : sub5 [-1, 0, -2] = true := by decide +kernel
theorem sub5_225 : sub5 [-1, 0, -1] = true := by decide +kernel
theorem sub5_226 : sub5 [-1, 0, 0] = true := by decide +kernel
theorem sub5_227 : sub5 [-1, 0, 1] = true := by decide +kernel
theorem sub5_228 : sub5 [-1, 0, 2] = true := by decide +kernel
theorem sub5_229 : sub5 [-1, 0, 3] = true := by decide +kernel
theorem sub5_230 : sub5 [-1, 0, 4] = true := by decide +kernel
theorem sub5_231 : sub5 [-1, 0, 5] = true := by decide +kernel
theorem sub5_232 : sub5 [-1, 0, 6] = true := by decide +kernel
theorem sub5_233 : sub5 [-1, 0, 7] = true := by decide +kernel
theorem sub5_234 : sub5 [-1, 0, 8] = true := by decide +kernel
theorem sub5_235 : sub5 [-1, 1, -10] = true := by decide +kernel
theorem sub5_236 : sub5 [-1, 1, -9] = true := by decide +kernel
theorem sub5_237 : sub5 [-1, 1, -8] = true := by decide +kernel
theorem sub5_238 : sub5 [-1, 1, -7] = true := by decide +kernel
theorem sub5_239 : sub5 [-1, 1, -6] = true := by decide +kernel
theorem sub5_240 : sub5 [-1, 1, -5] = true := by decide +kernel
theorem sub5_241 : sub5 [-1, 1, -4] = true := by decide +kernel
theorem sub5_242 : sub5 [-1, 1, -3] = true := by decide +kernel
theorem sub5_243 : sub5 [-1, 1, -2] = true := by decide +kernel
theorem sub5_244 : sub5 [-1, 1, -1] = true := by decide +kernel
theorem sub5_245 : sub5 [-1, 1, 0] = true := by decide +kernel
theorem sub5_246 : sub5 [-1, 1, 1] = true := by decide +kernel
theorem sub5_247 : sub5 [-1, 1, 2] = true := by decide +kernel
theorem sub5_248 : sub5 [-1, 1, 3] = true := by decide +kernel
theorem sub5_249 : sub5 [-1, 1, 4] = true := by decide +kernel
theorem sub5_250 : sub5 [-1, 1, 5] = true := by decide +kernel
theorem sub5_251 : sub5 [-1, 1, 6] = true := by decide +kernel
theorem sub5_252 : sub5 [-1, 1, 7] = true := by decide +kernel
theorem sub5_253 : sub5 [-1, 1, 8] = true := by decide +kernel
theorem sub5_254 : sub5 [-1, 2, -10] = true := by decide +kernel
theorem sub5_255 : sub5 [-1, 2, -9] = true := by decide +kernel
theorem sb5_7 : ∀ q ∈ blk5_7, sub5 q = true := by
  unfold blk5_7
  exact List.forall_mem_cons.2 ⟨sub5_224, List.forall_mem_cons.2 ⟨sub5_225, List.forall_mem_cons.2 ⟨sub5_226, List.forall_mem_cons.2 ⟨sub5_227, List.forall_mem_cons.2 ⟨sub5_228, List.forall_mem_cons.2 ⟨sub5_229, List.forall_mem_cons.2 ⟨sub5_230, List.forall_mem_cons.2 ⟨sub5_231, List.forall_mem_cons.2 ⟨sub5_232, List.forall_mem_cons.2 ⟨sub5_233, List.forall_mem_cons.2 ⟨sub5_234, List.forall_mem_cons.2 ⟨sub5_235, List.forall_mem_cons.2 ⟨sub5_236, List.forall_mem_cons.2 ⟨sub5_237, List.forall_mem_cons.2 ⟨sub5_238, List.forall_mem_cons.2 ⟨sub5_239, List.forall_mem_cons.2 ⟨sub5_240, List.forall_mem_cons.2 ⟨sub5_241, List.forall_mem_cons.2 ⟨sub5_242, List.forall_mem_cons.2 ⟨sub5_243, List.forall_mem_cons.2 ⟨sub5_244, List.forall_mem_cons.2 ⟨sub5_245, List.forall_mem_cons.2 ⟨sub5_246, List.forall_mem_cons.2 ⟨sub5_247, List.forall_mem_cons.2 ⟨sub5_248, List.forall_mem_cons.2 ⟨sub5_249, List.forall_mem_cons.2 ⟨sub5_250, List.forall_mem_cons.2 ⟨sub5_251, List.forall_mem_cons.2 ⟨sub5_252, List.forall_mem_cons.2 ⟨sub5_253, List.forall_mem_cons.2 ⟨sub5_254, List.forall_mem_cons.2 ⟨sub5_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_256 : sub5 [-1, 2, -8] = true := by decide +kernel
theorem sub5_257 : sub5 [-1, 2, -7] = true := by decide +kernel
theorem sub5_258 : sub5 [-1, 2, -6] = true := by decide +kernel
theorem sub5_259 : sub5 [-1, 2, -5] = true := by decide +kernel
theorem sub5_260 : sub5 [-1, 2, -4] = true := by decide +kernel
theorem sub5_261 : sub5 [-1, 2, -3] = true := by decide +kernel
theorem sub5_262 : sub5 [-1, 2, -2] = true := by decide +kernel
theorem sub5_263 : sub5 [-1, 2, -1] = true := by decide +kernel
theorem sub5_264 : sub5 [-1, 2, 0] = true := by decide +kernel
theorem sub5_265 : sub5 [-1, 2, 1] = true := by decide +kernel
theorem sub5_266 : sub5 [-1, 2, 2] = true := by decide +kernel
theorem sub5_267 : sub5 [-1, 2, 3] = true := by decide +kernel
theorem sub5_268 : sub5 [-1, 2, 4] = true := by decide +kernel
theorem sub5_269 : sub5 [-1, 2, 5] = true := by decide +kernel
theorem sub5_270 : sub5 [-1, 2, 6] = true := by decide +kernel
theorem sub5_271 : sub5 [-1, 2, 7] = true := by decide +kernel
theorem sub5_272 : sub5 [-1, 3, -9] = true := by decide +kernel
theorem sub5_273 : sub5 [-1, 3, -8] = true := by decide +kernel
theorem sub5_274 : sub5 [-1, 3, -7] = true := by decide +kernel
theorem sub5_275 : sub5 [-1, 3, -6] = true := by decide +kernel
theorem sub5_276 : sub5 [-1, 3, -5] = true := by decide +kernel
theorem sub5_277 : sub5 [-1, 3, -4] = true := by decide +kernel
theorem sub5_278 : sub5 [-1, 3, -3] = true := by decide +kernel
theorem sub5_279 : sub5 [-1, 3, -2] = true := by decide +kernel
theorem sub5_280 : sub5 [-1, 3, -1] = true := by decide +kernel
theorem sub5_281 : sub5 [-1, 3, 0] = true := by decide +kernel
theorem sub5_282 : sub5 [-1, 3, 1] = true := by decide +kernel
theorem sub5_283 : sub5 [-1, 3, 2] = true := by decide +kernel
theorem sub5_284 : sub5 [-1, 3, 3] = true := by decide +kernel
theorem sub5_285 : sub5 [-1, 3, 4] = true := by decide +kernel
theorem sub5_286 : sub5 [-1, 3, 5] = true := by decide +kernel
theorem sub5_287 : sub5 [-1, 4] = true := by decide +kernel
theorem sb5_8 : ∀ q ∈ blk5_8, sub5 q = true := by
  unfold blk5_8
  exact List.forall_mem_cons.2 ⟨sub5_256, List.forall_mem_cons.2 ⟨sub5_257, List.forall_mem_cons.2 ⟨sub5_258, List.forall_mem_cons.2 ⟨sub5_259, List.forall_mem_cons.2 ⟨sub5_260, List.forall_mem_cons.2 ⟨sub5_261, List.forall_mem_cons.2 ⟨sub5_262, List.forall_mem_cons.2 ⟨sub5_263, List.forall_mem_cons.2 ⟨sub5_264, List.forall_mem_cons.2 ⟨sub5_265, List.forall_mem_cons.2 ⟨sub5_266, List.forall_mem_cons.2 ⟨sub5_267, List.forall_mem_cons.2 ⟨sub5_268, List.forall_mem_cons.2 ⟨sub5_269, List.forall_mem_cons.2 ⟨sub5_270, List.forall_mem_cons.2 ⟨sub5_271, List.forall_mem_cons.2 ⟨sub5_272, List.forall_mem_cons.2 ⟨sub5_273, List.forall_mem_cons.2 ⟨sub5_274, List.forall_mem_cons.2 ⟨sub5_275, List.forall_mem_cons.2 ⟨sub5_276, List.forall_mem_cons.2 ⟨sub5_277, List.forall_mem_cons.2 ⟨sub5_278, List.forall_mem_cons.2 ⟨sub5_279, List.forall_mem_cons.2 ⟨sub5_280, List.forall_mem_cons.2 ⟨sub5_281, List.forall_mem_cons.2 ⟨sub5_282, List.forall_mem_cons.2 ⟨sub5_283, List.forall_mem_cons.2 ⟨sub5_284, List.forall_mem_cons.2 ⟨sub5_285, List.forall_mem_cons.2 ⟨sub5_286, List.forall_mem_cons.2 ⟨sub5_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_288 : sub5 [0, -6] = true := by decide +kernel
theorem sub5_289 : sub5 [0, -5] = true := by decide +kernel
theorem sub5_290 : sub5 [0, -4] = true := by decide +kernel
theorem sub5_291 : sub5 [0, -3, -7] = true := by decide +kernel
theorem sub5_292 : sub5 [0, -3, -6] = true := by decide +kernel
theorem sub5_293 : sub5 [0, -3, -5] = true := by decide +kernel
theorem sub5_294 : sub5 [0, -3, -4] = true := by decide +kernel
theorem sub5_295 : sub5 [0, -3, -3] = true := by decide +kernel
theorem sub5_296 : sub5 [0, -3, -2] = true := by decide +kernel
theorem sub5_297 : sub5 [0, -3, -1] = true := by decide +kernel
theorem sub5_298 : sub5 [0, -3, 0] = true := by decide +kernel
theorem sub5_299 : sub5 [0, -3, 1] = true := by decide +kernel
theorem sub5_300 : sub5 [0, -3, 2] = true := by decide +kernel
theorem sub5_301 : sub5 [0, -3, 3] = true := by decide +kernel
theorem sub5_302 : sub5 [0, -3, 4] = true := by decide +kernel
theorem sub5_303 : sub5 [0, -3, 5] = true := by decide +kernel
theorem sub5_304 : sub5 [0, -3, 6] = true := by decide +kernel
theorem sub5_305 : sub5 [0, -3, 7] = true := by decide +kernel
theorem sub5_306 : sub5 [0, -3, 8] = true := by decide +kernel
theorem sub5_307 : sub5 [0, -2, -8] = true := by decide +kernel
theorem sub5_308 : sub5 [0, -2, -7] = true := by decide +kernel
theorem sub5_309 : sub5 [0, -2, -6] = true := by decide +kernel
theorem sub5_310 : sub5 [0, -2, -5] = true := by decide +kernel
theorem sub5_311 : sub5 [0, -2, -4] = true := by decide +kernel
theorem sub5_312 : sub5 [0, -2, -3] = true := by decide +kernel
theorem sub5_313 : sub5 [0, -2, -2] = true := by decide +kernel
theorem sub5_314 : sub5 [0, -2, -1] = true := by decide +kernel
theorem sub5_315 : sub5 [0, -2, 0] = true := by decide +kernel
theorem sub5_316 : sub5 [0, -2, 1] = true := by decide +kernel
theorem sub5_317 : sub5 [0, -2, 2] = true := by decide +kernel
theorem sub5_318 : sub5 [0, -2, 3] = true := by decide +kernel
theorem sub5_319 : sub5 [0, -2, 4] = true := by decide +kernel
theorem sb5_9 : ∀ q ∈ blk5_9, sub5 q = true := by
  unfold blk5_9
  exact List.forall_mem_cons.2 ⟨sub5_288, List.forall_mem_cons.2 ⟨sub5_289, List.forall_mem_cons.2 ⟨sub5_290, List.forall_mem_cons.2 ⟨sub5_291, List.forall_mem_cons.2 ⟨sub5_292, List.forall_mem_cons.2 ⟨sub5_293, List.forall_mem_cons.2 ⟨sub5_294, List.forall_mem_cons.2 ⟨sub5_295, List.forall_mem_cons.2 ⟨sub5_296, List.forall_mem_cons.2 ⟨sub5_297, List.forall_mem_cons.2 ⟨sub5_298, List.forall_mem_cons.2 ⟨sub5_299, List.forall_mem_cons.2 ⟨sub5_300, List.forall_mem_cons.2 ⟨sub5_301, List.forall_mem_cons.2 ⟨sub5_302, List.forall_mem_cons.2 ⟨sub5_303, List.forall_mem_cons.2 ⟨sub5_304, List.forall_mem_cons.2 ⟨sub5_305, List.forall_mem_cons.2 ⟨sub5_306, List.forall_mem_cons.2 ⟨sub5_307, List.forall_mem_cons.2 ⟨sub5_308, List.forall_mem_cons.2 ⟨sub5_309, List.forall_mem_cons.2 ⟨sub5_310, List.forall_mem_cons.2 ⟨sub5_311, List.forall_mem_cons.2 ⟨sub5_312, List.forall_mem_cons.2 ⟨sub5_313, List.forall_mem_cons.2 ⟨sub5_314, List.forall_mem_cons.2 ⟨sub5_315, List.forall_mem_cons.2 ⟨sub5_316, List.forall_mem_cons.2 ⟨sub5_317, List.forall_mem_cons.2 ⟨sub5_318, List.forall_mem_cons.2 ⟨sub5_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_320 : sub5 [0, -2, 5] = true := by decide +kernel
theorem sub5_321 : sub5 [0, -2, 6] = true := by decide +kernel
theorem sub5_322 : sub5 [0, -2, 7] = true := by decide +kernel
theorem sub5_323 : sub5 [0, -2, 8] = true := by decide +kernel
theorem sub5_324 : sub5 [0, -2, 9] = true := by decide +kernel
theorem sub5_325 : sub5 [0, -1, -9] = true := by decide +kernel
theorem sub5_326 : sub5 [0, -1, -8] = true := by decide +kernel
theorem sub5_327 : sub5 [0, -1, -7] = true := by decide +kernel
theorem sub5_328 : sub5 [0, -1, -6] = true := by decide +kernel
theorem sub5_329 : sub5 [0, -1, -5] = true := by decide +kernel
theorem sub5_330 : sub5 [0, -1, -4] = true := by decide +kernel
theorem sub5_331 : sub5 [0, -1, -3] = true := by decide +kernel
theorem sub5_332 : sub5 [0, -1, -2] = true := by decide +kernel
theorem sub5_333 : sub5 [0, -1, -1] = true := by decide +kernel
theorem sub5_334 : sub5 [0, -1, 0] = true := by decide +kernel
theorem sub5_335 : sub5 [0, -1, 1] = true := by decide +kernel
theorem sub5_336 : sub5 [0, -1, 2] = true := by decide +kernel
theorem sub5_337 : sub5 [0, -1, 3] = true := by decide +kernel
theorem sub5_338 : sub5 [0, -1, 4] = true := by decide +kernel
theorem sub5_339 : sub5 [0, -1, 5] = true := by decide +kernel
theorem sub5_340 : sub5 [0, -1, 6] = true := by decide +kernel
theorem sub5_341 : sub5 [0, -1, 7] = true := by decide +kernel
theorem sub5_342 : sub5 [0, -1, 8] = true := by decide +kernel
theorem sub5_343 : sub5 [0, -1, 9] = true := by decide +kernel
theorem sub5_344 : sub5 [0, 0, -10] = true := by decide +kernel
theorem sub5_345 : sub5 [0, 0, -9] = true := by decide +kernel
theorem sub5_346 : sub5 [0, 0, -8] = true := by decide +kernel
theorem sub5_347 : sub5 [0, 0, -7] = true := by decide +kernel
theorem sub5_348 : sub5 [0, 0, -6] = true := by decide +kernel
theorem sub5_349 : sub5 [0, 0, -5] = true := by decide +kernel
theorem sub5_350 : sub5 [0, 0, -4] = true := by decide +kernel
theorem sub5_351 : sub5 [0, 0, -3] = true := by decide +kernel
theorem sb5_10 : ∀ q ∈ blk5_10, sub5 q = true := by
  unfold blk5_10
  exact List.forall_mem_cons.2 ⟨sub5_320, List.forall_mem_cons.2 ⟨sub5_321, List.forall_mem_cons.2 ⟨sub5_322, List.forall_mem_cons.2 ⟨sub5_323, List.forall_mem_cons.2 ⟨sub5_324, List.forall_mem_cons.2 ⟨sub5_325, List.forall_mem_cons.2 ⟨sub5_326, List.forall_mem_cons.2 ⟨sub5_327, List.forall_mem_cons.2 ⟨sub5_328, List.forall_mem_cons.2 ⟨sub5_329, List.forall_mem_cons.2 ⟨sub5_330, List.forall_mem_cons.2 ⟨sub5_331, List.forall_mem_cons.2 ⟨sub5_332, List.forall_mem_cons.2 ⟨sub5_333, List.forall_mem_cons.2 ⟨sub5_334, List.forall_mem_cons.2 ⟨sub5_335, List.forall_mem_cons.2 ⟨sub5_336, List.forall_mem_cons.2 ⟨sub5_337, List.forall_mem_cons.2 ⟨sub5_338, List.forall_mem_cons.2 ⟨sub5_339, List.forall_mem_cons.2 ⟨sub5_340, List.forall_mem_cons.2 ⟨sub5_341, List.forall_mem_cons.2 ⟨sub5_342, List.forall_mem_cons.2 ⟨sub5_343, List.forall_mem_cons.2 ⟨sub5_344, List.forall_mem_cons.2 ⟨sub5_345, List.forall_mem_cons.2 ⟨sub5_346, List.forall_mem_cons.2 ⟨sub5_347, List.forall_mem_cons.2 ⟨sub5_348, List.forall_mem_cons.2 ⟨sub5_349, List.forall_mem_cons.2 ⟨sub5_350, List.forall_mem_cons.2 ⟨sub5_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_352 : sub5 [0, 0, -2] = true := by decide +kernel
theorem sub5_353 : sub5 [0, 0, -1] = true := by decide +kernel
theorem sub5_354 : sub5 [0, 0, 0] = true := by decide +kernel
theorem sub5_355 : sub5 [0, 0, 1] = true := by decide +kernel
theorem sub5_356 : sub5 [0, 0, 2] = true := by decide +kernel
theorem sub5_357 : sub5 [0, 0, 3] = true := by decide +kernel
theorem sub5_358 : sub5 [0, 0, 4] = true := by decide +kernel
theorem sub5_359 : sub5 [0, 0, 5] = true := by decide +kernel
theorem sub5_360 : sub5 [0, 0, 6] = true := by decide +kernel
theorem sub5_361 : sub5 [0, 0, 7] = true := by decide +kernel
theorem sub5_362 : sub5 [0, 0, 8] = true := by decide +kernel
theorem sub5_363 : sub5 [0, 0, 9] = true := by decide +kernel
theorem sub5_364 : sub5 [0, 1, -10] = true := by decide +kernel
theorem sub5_365 : sub5 [0, 1, -9] = true := by decide +kernel
theorem sub5_366 : sub5 [0, 1, -8] = true := by decide +kernel
theorem sub5_367 : sub5 [0, 1, -7] = true := by decide +kernel
theorem sub5_368 : sub5 [0, 1, -6] = true := by decide +kernel
theorem sub5_369 : sub5 [0, 1, -5] = true := by decide +kernel
theorem sub5_370 : sub5 [0, 1, -4] = true := by decide +kernel
theorem sub5_371 : sub5 [0, 1, -3] = true := by decide +kernel
theorem sub5_372 : sub5 [0, 1, -2] = true := by decide +kernel
theorem sub5_373 : sub5 [0, 1, -1] = true := by decide +kernel
theorem sub5_374 : sub5 [0, 1, 0] = true := by decide +kernel
theorem sub5_375 : sub5 [0, 1, 1] = true := by decide +kernel
theorem sub5_376 : sub5 [0, 1, 2] = true := by decide +kernel
theorem sub5_377 : sub5 [0, 1, 3] = true := by decide +kernel
theorem sub5_378 : sub5 [0, 1, 4] = true := by decide +kernel
theorem sub5_379 : sub5 [0, 1, 5] = true := by decide +kernel
theorem sub5_380 : sub5 [0, 1, 6] = true := by decide +kernel
theorem sub5_381 : sub5 [0, 1, 7] = true := by decide +kernel
theorem sub5_382 : sub5 [0, 1, 8] = true := by decide +kernel
theorem sub5_383 : sub5 [0, 2, -10] = true := by decide +kernel
theorem sb5_11 : ∀ q ∈ blk5_11, sub5 q = true := by
  unfold blk5_11
  exact List.forall_mem_cons.2 ⟨sub5_352, List.forall_mem_cons.2 ⟨sub5_353, List.forall_mem_cons.2 ⟨sub5_354, List.forall_mem_cons.2 ⟨sub5_355, List.forall_mem_cons.2 ⟨sub5_356, List.forall_mem_cons.2 ⟨sub5_357, List.forall_mem_cons.2 ⟨sub5_358, List.forall_mem_cons.2 ⟨sub5_359, List.forall_mem_cons.2 ⟨sub5_360, List.forall_mem_cons.2 ⟨sub5_361, List.forall_mem_cons.2 ⟨sub5_362, List.forall_mem_cons.2 ⟨sub5_363, List.forall_mem_cons.2 ⟨sub5_364, List.forall_mem_cons.2 ⟨sub5_365, List.forall_mem_cons.2 ⟨sub5_366, List.forall_mem_cons.2 ⟨sub5_367, List.forall_mem_cons.2 ⟨sub5_368, List.forall_mem_cons.2 ⟨sub5_369, List.forall_mem_cons.2 ⟨sub5_370, List.forall_mem_cons.2 ⟨sub5_371, List.forall_mem_cons.2 ⟨sub5_372, List.forall_mem_cons.2 ⟨sub5_373, List.forall_mem_cons.2 ⟨sub5_374, List.forall_mem_cons.2 ⟨sub5_375, List.forall_mem_cons.2 ⟨sub5_376, List.forall_mem_cons.2 ⟨sub5_377, List.forall_mem_cons.2 ⟨sub5_378, List.forall_mem_cons.2 ⟨sub5_379, List.forall_mem_cons.2 ⟨sub5_380, List.forall_mem_cons.2 ⟨sub5_381, List.forall_mem_cons.2 ⟨sub5_382, List.forall_mem_cons.2 ⟨sub5_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_384 : sub5 [0, 2, -9] = true := by decide +kernel
theorem sub5_385 : sub5 [0, 2, -8] = true := by decide +kernel
theorem sub5_386 : sub5 [0, 2, -7] = true := by decide +kernel
theorem sub5_387 : sub5 [0, 2, -6] = true := by decide +kernel
theorem sub5_388 : sub5 [0, 2, -5] = true := by decide +kernel
theorem sub5_389 : sub5 [0, 2, -4] = true := by decide +kernel
theorem sub5_390 : sub5 [0, 2, -3] = true := by decide +kernel
theorem sub5_391 : sub5 [0, 2, -2] = true := by decide +kernel
theorem sub5_392 : sub5 [0, 2, -1] = true := by decide +kernel
theorem sub5_393 : sub5 [0, 2, 0] = true := by decide +kernel
theorem sub5_394 : sub5 [0, 2, 1] = true := by decide +kernel
theorem sub5_395 : sub5 [0, 2, 2] = true := by decide +kernel
theorem sub5_396 : sub5 [0, 2, 3] = true := by decide +kernel
theorem sub5_397 : sub5 [0, 2, 4] = true := by decide +kernel
theorem sub5_398 : sub5 [0, 2, 5] = true := by decide +kernel
theorem sub5_399 : sub5 [0, 2, 6] = true := by decide +kernel
theorem sub5_400 : sub5 [0, 2, 7] = true := by decide +kernel
theorem sub5_401 : sub5 [0, 3, -9] = true := by decide +kernel
theorem sub5_402 : sub5 [0, 3, -8] = true := by decide +kernel
theorem sub5_403 : sub5 [0, 3, -7] = true := by decide +kernel
theorem sub5_404 : sub5 [0, 3, -6] = true := by decide +kernel
theorem sub5_405 : sub5 [0, 3, -5] = true := by decide +kernel
theorem sub5_406 : sub5 [0, 3, -4] = true := by decide +kernel
theorem sub5_407 : sub5 [0, 3, -3] = true := by decide +kernel
theorem sub5_408 : sub5 [0, 3, -2] = true := by decide +kernel
theorem sub5_409 : sub5 [0, 3, -1] = true := by decide +kernel
theorem sub5_410 : sub5 [0, 3, 0] = true := by decide +kernel
theorem sub5_411 : sub5 [0, 3, 1] = true := by decide +kernel
theorem sub5_412 : sub5 [0, 3, 2] = true := by decide +kernel
theorem sub5_413 : sub5 [0, 3, 3] = true := by decide +kernel
theorem sub5_414 : sub5 [0, 3, 4] = true := by decide +kernel
theorem sub5_415 : sub5 [0, 3, 5] = true := by decide +kernel
theorem sb5_12 : ∀ q ∈ blk5_12, sub5 q = true := by
  unfold blk5_12
  exact List.forall_mem_cons.2 ⟨sub5_384, List.forall_mem_cons.2 ⟨sub5_385, List.forall_mem_cons.2 ⟨sub5_386, List.forall_mem_cons.2 ⟨sub5_387, List.forall_mem_cons.2 ⟨sub5_388, List.forall_mem_cons.2 ⟨sub5_389, List.forall_mem_cons.2 ⟨sub5_390, List.forall_mem_cons.2 ⟨sub5_391, List.forall_mem_cons.2 ⟨sub5_392, List.forall_mem_cons.2 ⟨sub5_393, List.forall_mem_cons.2 ⟨sub5_394, List.forall_mem_cons.2 ⟨sub5_395, List.forall_mem_cons.2 ⟨sub5_396, List.forall_mem_cons.2 ⟨sub5_397, List.forall_mem_cons.2 ⟨sub5_398, List.forall_mem_cons.2 ⟨sub5_399, List.forall_mem_cons.2 ⟨sub5_400, List.forall_mem_cons.2 ⟨sub5_401, List.forall_mem_cons.2 ⟨sub5_402, List.forall_mem_cons.2 ⟨sub5_403, List.forall_mem_cons.2 ⟨sub5_404, List.forall_mem_cons.2 ⟨sub5_405, List.forall_mem_cons.2 ⟨sub5_406, List.forall_mem_cons.2 ⟨sub5_407, List.forall_mem_cons.2 ⟨sub5_408, List.forall_mem_cons.2 ⟨sub5_409, List.forall_mem_cons.2 ⟨sub5_410, List.forall_mem_cons.2 ⟨sub5_411, List.forall_mem_cons.2 ⟨sub5_412, List.forall_mem_cons.2 ⟨sub5_413, List.forall_mem_cons.2 ⟨sub5_414, List.forall_mem_cons.2 ⟨sub5_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_416 : sub5 [0, 3, 6] = true := by decide +kernel
theorem sub5_417 : sub5 [0, 4] = true := by decide +kernel
theorem sub5_418 : sub5 [0, 5] = true := by decide +kernel
theorem sub5_419 : sub5 [1, -5] = true := by decide +kernel
theorem sub5_420 : sub5 [1, -4] = true := by decide +kernel
theorem sub5_421 : sub5 [1, -3, -6] = true := by decide +kernel
theorem sub5_422 : sub5 [1, -3, -5] = true := by decide +kernel
theorem sub5_423 : sub5 [1, -3, -4] = true := by decide +kernel
theorem sub5_424 : sub5 [1, -3, -3] = true := by decide +kernel
theorem sub5_425 : sub5 [1, -3, -2] = true := by decide +kernel
theorem sub5_426 : sub5 [1, -3, -1] = true := by decide +kernel
theorem sub5_427 : sub5 [1, -3, 0] = true := by decide +kernel
theorem sub5_428 : sub5 [1, -3, 1] = true := by decide +kernel
theorem sub5_429 : sub5 [1, -3, 2] = true := by decide +kernel
theorem sub5_430 : sub5 [1, -3, 3] = true := by decide +kernel
theorem sub5_431 : sub5 [1, -3, 4] = true := by decide +kernel
theorem sub5_432 : sub5 [1, -3, 5] = true := by decide +kernel
theorem sub5_433 : sub5 [1, -3, 6] = true := by decide +kernel
theorem sub5_434 : sub5 [1, -3, 7] = true := by decide +kernel
theorem sub5_435 : sub5 [1, -3, 8] = true := by decide +kernel
theorem sub5_436 : sub5 [1, -2, -8] = true := by decide +kernel
theorem sub5_437 : sub5 [1, -2, -7] = true := by decide +kernel
theorem sub5_438 : sub5 [1, -2, -6] = true := by decide +kernel
theorem sub5_439 : sub5 [1, -2, -5] = true := by decide +kernel
theorem sub5_440 : sub5 [1, -2, -4] = true := by decide +kernel
theorem sub5_441 : sub5 [1, -2, -3] = true := by decide +kernel
theorem sub5_442 : sub5 [1, -2, -2] = true := by decide +kernel
theorem sub5_443 : sub5 [1, -2, -1] = true := by decide +kernel
theorem sub5_444 : sub5 [1, -2, 0] = true := by decide +kernel
theorem sub5_445 : sub5 [1, -2, 1] = true := by decide +kernel
theorem sub5_446 : sub5 [1, -2, 2] = true := by decide +kernel
theorem sub5_447 : sub5 [1, -2, 3] = true := by decide +kernel
theorem sb5_13 : ∀ q ∈ blk5_13, sub5 q = true := by
  unfold blk5_13
  exact List.forall_mem_cons.2 ⟨sub5_416, List.forall_mem_cons.2 ⟨sub5_417, List.forall_mem_cons.2 ⟨sub5_418, List.forall_mem_cons.2 ⟨sub5_419, List.forall_mem_cons.2 ⟨sub5_420, List.forall_mem_cons.2 ⟨sub5_421, List.forall_mem_cons.2 ⟨sub5_422, List.forall_mem_cons.2 ⟨sub5_423, List.forall_mem_cons.2 ⟨sub5_424, List.forall_mem_cons.2 ⟨sub5_425, List.forall_mem_cons.2 ⟨sub5_426, List.forall_mem_cons.2 ⟨sub5_427, List.forall_mem_cons.2 ⟨sub5_428, List.forall_mem_cons.2 ⟨sub5_429, List.forall_mem_cons.2 ⟨sub5_430, List.forall_mem_cons.2 ⟨sub5_431, List.forall_mem_cons.2 ⟨sub5_432, List.forall_mem_cons.2 ⟨sub5_433, List.forall_mem_cons.2 ⟨sub5_434, List.forall_mem_cons.2 ⟨sub5_435, List.forall_mem_cons.2 ⟨sub5_436, List.forall_mem_cons.2 ⟨sub5_437, List.forall_mem_cons.2 ⟨sub5_438, List.forall_mem_cons.2 ⟨sub5_439, List.forall_mem_cons.2 ⟨sub5_440, List.forall_mem_cons.2 ⟨sub5_441, List.forall_mem_cons.2 ⟨sub5_442, List.forall_mem_cons.2 ⟨sub5_443, List.forall_mem_cons.2 ⟨sub5_444, List.forall_mem_cons.2 ⟨sub5_445, List.forall_mem_cons.2 ⟨sub5_446, List.forall_mem_cons.2 ⟨sub5_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_448 : sub5 [1, -2, 4] = true := by decide +kernel
theorem sub5_449 : sub5 [1, -2, 5] = true := by decide +kernel
theorem sub5_450 : sub5 [1, -2, 6] = true := by decide +kernel
theorem sub5_451 : sub5 [1, -2, 7] = true := by decide +kernel
theorem sub5_452 : sub5 [1, -2, 8] = true := by decide +kernel
theorem sub5_453 : sub5 [1, -2, 9] = true := by decide +kernel
theorem sub5_454 : sub5 [1, -1, -9] = true := by decide +kernel
theorem sub5_455 : sub5 [1, -1, -8] = true := by decide +kernel
theorem sub5_456 : sub5 [1, -1, -7] = true := by decide +kernel
theorem sub5_457 : sub5 [1, -1, -6] = true := by decide +kernel
theorem sub5_458 : sub5 [1, -1, -5] = true := by decide +kernel
theorem sub5_459 : sub5 [1, -1, -4] = true := by decide +kernel
theorem sub5_460 : sub5 [1, -1, -3] = true := by decide +kernel
theorem sub5_461 : sub5 [1, -1, -2] = true := by decide +kernel
theorem sub5_462 : sub5 [1, -1, -1] = true := by decide +kernel
theorem sub5_463 : sub5 [1, -1, 0] = true := by decide +kernel
theorem sub5_464 : sub5 [1, -1, 1] = true := by decide +kernel
theorem sub5_465 : sub5 [1, -1, 2] = true := by decide +kernel
theorem sub5_466 : sub5 [1, -1, 3] = true := by decide +kernel
theorem sub5_467 : sub5 [1, -1, 4] = true := by decide +kernel
theorem sub5_468 : sub5 [1, -1, 5] = true := by decide +kernel
theorem sub5_469 : sub5 [1, -1, 6] = true := by decide +kernel
theorem sub5_470 : sub5 [1, -1, 7] = true := by decide +kernel
theorem sub5_471 : sub5 [1, -1, 8] = true := by decide +kernel
theorem sub5_472 : sub5 [1, -1, 9] = true := by decide +kernel
theorem sub5_473 : sub5 [1, 0, -9] = true := by decide +kernel
theorem sub5_474 : sub5 [1, 0, -8] = true := by decide +kernel
theorem sub5_475 : sub5 [1, 0, -7] = true := by decide +kernel
theorem sub5_476 : sub5 [1, 0, -6] = true := by decide +kernel
theorem sub5_477 : sub5 [1, 0, -5] = true := by decide +kernel
theorem sub5_478 : sub5 [1, 0, -4] = true := by decide +kernel
theorem sub5_479 : sub5 [1, 0, -3] = true := by decide +kernel
theorem sb5_14 : ∀ q ∈ blk5_14, sub5 q = true := by
  unfold blk5_14
  exact List.forall_mem_cons.2 ⟨sub5_448, List.forall_mem_cons.2 ⟨sub5_449, List.forall_mem_cons.2 ⟨sub5_450, List.forall_mem_cons.2 ⟨sub5_451, List.forall_mem_cons.2 ⟨sub5_452, List.forall_mem_cons.2 ⟨sub5_453, List.forall_mem_cons.2 ⟨sub5_454, List.forall_mem_cons.2 ⟨sub5_455, List.forall_mem_cons.2 ⟨sub5_456, List.forall_mem_cons.2 ⟨sub5_457, List.forall_mem_cons.2 ⟨sub5_458, List.forall_mem_cons.2 ⟨sub5_459, List.forall_mem_cons.2 ⟨sub5_460, List.forall_mem_cons.2 ⟨sub5_461, List.forall_mem_cons.2 ⟨sub5_462, List.forall_mem_cons.2 ⟨sub5_463, List.forall_mem_cons.2 ⟨sub5_464, List.forall_mem_cons.2 ⟨sub5_465, List.forall_mem_cons.2 ⟨sub5_466, List.forall_mem_cons.2 ⟨sub5_467, List.forall_mem_cons.2 ⟨sub5_468, List.forall_mem_cons.2 ⟨sub5_469, List.forall_mem_cons.2 ⟨sub5_470, List.forall_mem_cons.2 ⟨sub5_471, List.forall_mem_cons.2 ⟨sub5_472, List.forall_mem_cons.2 ⟨sub5_473, List.forall_mem_cons.2 ⟨sub5_474, List.forall_mem_cons.2 ⟨sub5_475, List.forall_mem_cons.2 ⟨sub5_476, List.forall_mem_cons.2 ⟨sub5_477, List.forall_mem_cons.2 ⟨sub5_478, List.forall_mem_cons.2 ⟨sub5_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_480 : sub5 [1, 0, -2] = true := by decide +kernel
theorem sub5_481 : sub5 [1, 0, -1] = true := by decide +kernel
theorem sub5_482 : sub5 [1, 0, 0] = true := by decide +kernel
theorem sub5_483 : sub5 [1, 0, 1] = true := by decide +kernel
theorem sub5_484 : sub5 [1, 0, 2] = true := by decide +kernel
theorem sub5_485 : sub5 [1, 0, 3] = true := by decide +kernel
theorem sub5_486 : sub5 [1, 0, 4] = true := by decide +kernel
theorem sub5_487 : sub5 [1, 0, 5] = true := by decide +kernel
theorem sub5_488 : sub5 [1, 0, 6] = true := by decide +kernel
theorem sub5_489 : sub5 [1, 0, 7] = true := by decide +kernel
theorem sub5_490 : sub5 [1, 0, 8] = true := by decide +kernel
theorem sub5_491 : sub5 [1, 0, 9] = true := by decide +kernel
theorem sub5_492 : sub5 [1, 1, -10] = true := by decide +kernel
theorem sub5_493 : sub5 [1, 1, -9] = true := by decide +kernel
theorem sub5_494 : sub5 [1, 1, -8] = true := by decide +kernel
theorem sub5_495 : sub5 [1, 1, -7] = true := by decide +kernel
theorem sub5_496 : sub5 [1, 1, -6] = true := by decide +kernel
theorem sub5_497 : sub5 [1, 1, -5] = true := by decide +kernel
theorem sub5_498 : sub5 [1, 1, -4] = true := by decide +kernel
theorem sub5_499 : sub5 [1, 1, -3] = true := by decide +kernel
theorem sub5_500 : sub5 [1, 1, -2] = true := by decide +kernel
theorem sub5_501 : sub5 [1, 1, -1] = true := by decide +kernel
theorem sub5_502 : sub5 [1, 1, 0] = true := by decide +kernel
theorem sub5_503 : sub5 [1, 1, 1] = true := by decide +kernel
theorem sub5_504 : sub5 [1, 1, 2] = true := by decide +kernel
theorem sub5_505 : sub5 [1, 1, 3] = true := by decide +kernel
theorem sub5_506 : sub5 [1, 1, 4] = true := by decide +kernel
theorem sub5_507 : sub5 [1, 1, 5] = true := by decide +kernel
theorem sub5_508 : sub5 [1, 1, 6] = true := by decide +kernel
theorem sub5_509 : sub5 [1, 1, 7] = true := by decide +kernel
theorem sub5_510 : sub5 [1, 1, 8] = true := by decide +kernel
theorem sub5_511 : sub5 [1, 2, -10] = true := by decide +kernel
theorem sb5_15 : ∀ q ∈ blk5_15, sub5 q = true := by
  unfold blk5_15
  exact List.forall_mem_cons.2 ⟨sub5_480, List.forall_mem_cons.2 ⟨sub5_481, List.forall_mem_cons.2 ⟨sub5_482, List.forall_mem_cons.2 ⟨sub5_483, List.forall_mem_cons.2 ⟨sub5_484, List.forall_mem_cons.2 ⟨sub5_485, List.forall_mem_cons.2 ⟨sub5_486, List.forall_mem_cons.2 ⟨sub5_487, List.forall_mem_cons.2 ⟨sub5_488, List.forall_mem_cons.2 ⟨sub5_489, List.forall_mem_cons.2 ⟨sub5_490, List.forall_mem_cons.2 ⟨sub5_491, List.forall_mem_cons.2 ⟨sub5_492, List.forall_mem_cons.2 ⟨sub5_493, List.forall_mem_cons.2 ⟨sub5_494, List.forall_mem_cons.2 ⟨sub5_495, List.forall_mem_cons.2 ⟨sub5_496, List.forall_mem_cons.2 ⟨sub5_497, List.forall_mem_cons.2 ⟨sub5_498, List.forall_mem_cons.2 ⟨sub5_499, List.forall_mem_cons.2 ⟨sub5_500, List.forall_mem_cons.2 ⟨sub5_501, List.forall_mem_cons.2 ⟨sub5_502, List.forall_mem_cons.2 ⟨sub5_503, List.forall_mem_cons.2 ⟨sub5_504, List.forall_mem_cons.2 ⟨sub5_505, List.forall_mem_cons.2 ⟨sub5_506, List.forall_mem_cons.2 ⟨sub5_507, List.forall_mem_cons.2 ⟨sub5_508, List.forall_mem_cons.2 ⟨sub5_509, List.forall_mem_cons.2 ⟨sub5_510, List.forall_mem_cons.2 ⟨sub5_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_512 : sub5 [1, 2, -9] = true := by decide +kernel
theorem sub5_513 : sub5 [1, 2, -8] = true := by decide +kernel
theorem sub5_514 : sub5 [1, 2, -7] = true := by decide +kernel
theorem sub5_515 : sub5 [1, 2, -6] = true := by decide +kernel
theorem sub5_516 : sub5 [1, 2, -5] = true := by decide +kernel
theorem sub5_517 : sub5 [1, 2, -4] = true := by decide +kernel
theorem sub5_518 : sub5 [1, 2, -3] = true := by decide +kernel
theorem sub5_519 : sub5 [1, 2, -2] = true := by decide +kernel
theorem sub5_520 : sub5 [1, 2, -1] = true := by decide +kernel
theorem sub5_521 : sub5 [1, 2, 0] = true := by decide +kernel
theorem sub5_522 : sub5 [1, 2, 1] = true := by decide +kernel
theorem sub5_523 : sub5 [1, 2, 2] = true := by decide +kernel
theorem sub5_524 : sub5 [1, 2, 3] = true := by decide +kernel
theorem sub5_525 : sub5 [1, 2, 4] = true := by decide +kernel
theorem sub5_526 : sub5 [1, 2, 5] = true := by decide +kernel
theorem sub5_527 : sub5 [1, 2, 6] = true := by decide +kernel
theorem sub5_528 : sub5 [1, 2, 7] = true := by decide +kernel
theorem sub5_529 : sub5 [1, 2, 8] = true := by decide +kernel
theorem sub5_530 : sub5 [1, 3, -9] = true := by decide +kernel
theorem sub5_531 : sub5 [1, 3, -8] = true := by decide +kernel
theorem sub5_532 : sub5 [1, 3, -7] = true := by decide +kernel
theorem sub5_533 : sub5 [1, 3, -6] = true := by decide +kernel
theorem sub5_534 : sub5 [1, 3, -5] = true := by decide +kernel
theorem sub5_535 : sub5 [1, 3, -4] = true := by decide +kernel
theorem sub5_536 : sub5 [1, 3, -3] = true := by decide +kernel
theorem sub5_537 : sub5 [1, 3, -2] = true := by decide +kernel
theorem sub5_538 : sub5 [1, 3, -1] = true := by decide +kernel
theorem sub5_539 : sub5 [1, 3, 0] = true := by decide +kernel
theorem sub5_540 : sub5 [1, 3, 1] = true := by decide +kernel
theorem sub5_541 : sub5 [1, 3, 2] = true := by decide +kernel
theorem sub5_542 : sub5 [1, 3, 3] = true := by decide +kernel
theorem sub5_543 : sub5 [1, 3, 4] = true := by decide +kernel
theorem sb5_16 : ∀ q ∈ blk5_16, sub5 q = true := by
  unfold blk5_16
  exact List.forall_mem_cons.2 ⟨sub5_512, List.forall_mem_cons.2 ⟨sub5_513, List.forall_mem_cons.2 ⟨sub5_514, List.forall_mem_cons.2 ⟨sub5_515, List.forall_mem_cons.2 ⟨sub5_516, List.forall_mem_cons.2 ⟨sub5_517, List.forall_mem_cons.2 ⟨sub5_518, List.forall_mem_cons.2 ⟨sub5_519, List.forall_mem_cons.2 ⟨sub5_520, List.forall_mem_cons.2 ⟨sub5_521, List.forall_mem_cons.2 ⟨sub5_522, List.forall_mem_cons.2 ⟨sub5_523, List.forall_mem_cons.2 ⟨sub5_524, List.forall_mem_cons.2 ⟨sub5_525, List.forall_mem_cons.2 ⟨sub5_526, List.forall_mem_cons.2 ⟨sub5_527, List.forall_mem_cons.2 ⟨sub5_528, List.forall_mem_cons.2 ⟨sub5_529, List.forall_mem_cons.2 ⟨sub5_530, List.forall_mem_cons.2 ⟨sub5_531, List.forall_mem_cons.2 ⟨sub5_532, List.forall_mem_cons.2 ⟨sub5_533, List.forall_mem_cons.2 ⟨sub5_534, List.forall_mem_cons.2 ⟨sub5_535, List.forall_mem_cons.2 ⟨sub5_536, List.forall_mem_cons.2 ⟨sub5_537, List.forall_mem_cons.2 ⟨sub5_538, List.forall_mem_cons.2 ⟨sub5_539, List.forall_mem_cons.2 ⟨sub5_540, List.forall_mem_cons.2 ⟨sub5_541, List.forall_mem_cons.2 ⟨sub5_542, List.forall_mem_cons.2 ⟨sub5_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_544 : sub5 [1, 3, 5] = true := by decide +kernel
theorem sub5_545 : sub5 [1, 3, 6] = true := by decide +kernel
theorem sub5_546 : sub5 [1, 4] = true := by decide +kernel
theorem sub5_547 : sub5 [1, 5] = true := by decide +kernel
theorem sub5_548 : sub5 [2, -4] = true := by decide +kernel
theorem sub5_549 : sub5 [2, -3] = true := by decide +kernel
theorem sub5_550 : sub5 [2, -2, -6] = true := by decide +kernel
theorem sub5_551 : sub5 [2, -2, -5] = true := by decide +kernel
theorem sub5_552 : sub5 [2, -2, -4] = true := by decide +kernel
theorem sub5_553 : sub5 [2, -2, -3] = true := by decide +kernel
theorem sub5_554 : sub5 [2, -2, -2] = true := by decide +kernel
theorem sub5_555 : sub5 [2, -2, -1] = true := by decide +kernel
theorem sub5_556 : sub5 [2, -2, 0] = true := by decide +kernel
theorem sub5_557 : sub5 [2, -2, 1] = true := by decide +kernel
theorem sub5_558 : sub5 [2, -2, 2] = true := by decide +kernel
theorem sub5_559 : sub5 [2, -2, 3] = true := by decide +kernel
theorem sub5_560 : sub5 [2, -2, 4] = true := by decide +kernel
theorem sub5_561 : sub5 [2, -2, 5] = true := by decide +kernel
theorem sub5_562 : sub5 [2, -2, 6] = true := by decide +kernel
theorem sub5_563 : sub5 [2, -2, 7] = true := by decide +kernel
theorem sub5_564 : sub5 [2, -1, -8] = true := by decide +kernel
theorem sub5_565 : sub5 [2, -1, -7] = true := by decide +kernel
theorem sub5_566 : sub5 [2, -1, -6] = true := by decide +kernel
theorem sub5_567 : sub5 [2, -1, -5] = true := by decide +kernel
theorem sub5_568 : sub5 [2, -1, -4] = true := by decide +kernel
theorem sub5_569 : sub5 [2, -1, -3] = true := by decide +kernel
theorem sub5_570 : sub5 [2, -1, -2] = true := by decide +kernel
theorem sub5_571 : sub5 [2, -1, -1] = true := by decide +kernel
theorem sub5_572 : sub5 [2, -1, 0] = true := by decide +kernel
theorem sub5_573 : sub5 [2, -1, 1] = true := by decide +kernel
theorem sub5_574 : sub5 [2, -1, 2] = true := by decide +kernel
theorem sub5_575 : sub5 [2, -1, 3] = true := by decide +kernel
theorem sb5_17 : ∀ q ∈ blk5_17, sub5 q = true := by
  unfold blk5_17
  exact List.forall_mem_cons.2 ⟨sub5_544, List.forall_mem_cons.2 ⟨sub5_545, List.forall_mem_cons.2 ⟨sub5_546, List.forall_mem_cons.2 ⟨sub5_547, List.forall_mem_cons.2 ⟨sub5_548, List.forall_mem_cons.2 ⟨sub5_549, List.forall_mem_cons.2 ⟨sub5_550, List.forall_mem_cons.2 ⟨sub5_551, List.forall_mem_cons.2 ⟨sub5_552, List.forall_mem_cons.2 ⟨sub5_553, List.forall_mem_cons.2 ⟨sub5_554, List.forall_mem_cons.2 ⟨sub5_555, List.forall_mem_cons.2 ⟨sub5_556, List.forall_mem_cons.2 ⟨sub5_557, List.forall_mem_cons.2 ⟨sub5_558, List.forall_mem_cons.2 ⟨sub5_559, List.forall_mem_cons.2 ⟨sub5_560, List.forall_mem_cons.2 ⟨sub5_561, List.forall_mem_cons.2 ⟨sub5_562, List.forall_mem_cons.2 ⟨sub5_563, List.forall_mem_cons.2 ⟨sub5_564, List.forall_mem_cons.2 ⟨sub5_565, List.forall_mem_cons.2 ⟨sub5_566, List.forall_mem_cons.2 ⟨sub5_567, List.forall_mem_cons.2 ⟨sub5_568, List.forall_mem_cons.2 ⟨sub5_569, List.forall_mem_cons.2 ⟨sub5_570, List.forall_mem_cons.2 ⟨sub5_571, List.forall_mem_cons.2 ⟨sub5_572, List.forall_mem_cons.2 ⟨sub5_573, List.forall_mem_cons.2 ⟨sub5_574, List.forall_mem_cons.2 ⟨sub5_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_576 : sub5 [2, -1, 4] = true := by decide +kernel
theorem sub5_577 : sub5 [2, -1, 5] = true := by decide +kernel
theorem sub5_578 : sub5 [2, -1, 6] = true := by decide +kernel
theorem sub5_579 : sub5 [2, -1, 7] = true := by decide +kernel
theorem sub5_580 : sub5 [2, -1, 8] = true := by decide +kernel
theorem sub5_581 : sub5 [2, 0, -8] = true := by decide +kernel
theorem sub5_582 : sub5 [2, 0, -7] = true := by decide +kernel
theorem sub5_583 : sub5 [2, 0, -6] = true := by decide +kernel
theorem sub5_584 : sub5 [2, 0, -5] = true := by decide +kernel
theorem sub5_585 : sub5 [2, 0, -4] = true := by decide +kernel
theorem sub5_586 : sub5 [2, 0, -3] = true := by decide +kernel
theorem sub5_587 : sub5 [2, 0, -2] = true := by decide +kernel
theorem sub5_588 : sub5 [2, 0, -1] = true := by decide +kernel
theorem sub5_589 : sub5 [2, 0, 0] = true := by decide +kernel
theorem sub5_590 : sub5 [2, 0, 1] = true := by decide +kernel
theorem sub5_591 : sub5 [2, 0, 2] = true := by decide +kernel
theorem sub5_592 : sub5 [2, 0, 3] = true := by decide +kernel
theorem sub5_593 : sub5 [2, 0, 4] = true := by decide +kernel
theorem sub5_594 : sub5 [2, 0, 5] = true := by decide +kernel
theorem sub5_595 : sub5 [2, 0, 6] = true := by decide +kernel
theorem sub5_596 : sub5 [2, 0, 7] = true := by decide +kernel
theorem sub5_597 : sub5 [2, 0, 8] = true := by decide +kernel
theorem sub5_598 : sub5 [2, 1, -9] = true := by decide +kernel
theorem sub5_599 : sub5 [2, 1, -8] = true := by decide +kernel
theorem sub5_600 : sub5 [2, 1, -7] = true := by decide +kernel
theorem sub5_601 : sub5 [2, 1, -6] = true := by decide +kernel
theorem sub5_602 : sub5 [2, 1, -5] = true := by decide +kernel
theorem sub5_603 : sub5 [2, 1, -4] = true := by decide +kernel
theorem sub5_604 : sub5 [2, 1, -3] = true := by decide +kernel
theorem sub5_605 : sub5 [2, 1, -2] = true := by decide +kernel
theorem sub5_606 : sub5 [2, 1, -1] = true := by decide +kernel
theorem sub5_607 : sub5 [2, 1, 0] = true := by decide +kernel
theorem sb5_18 : ∀ q ∈ blk5_18, sub5 q = true := by
  unfold blk5_18
  exact List.forall_mem_cons.2 ⟨sub5_576, List.forall_mem_cons.2 ⟨sub5_577, List.forall_mem_cons.2 ⟨sub5_578, List.forall_mem_cons.2 ⟨sub5_579, List.forall_mem_cons.2 ⟨sub5_580, List.forall_mem_cons.2 ⟨sub5_581, List.forall_mem_cons.2 ⟨sub5_582, List.forall_mem_cons.2 ⟨sub5_583, List.forall_mem_cons.2 ⟨sub5_584, List.forall_mem_cons.2 ⟨sub5_585, List.forall_mem_cons.2 ⟨sub5_586, List.forall_mem_cons.2 ⟨sub5_587, List.forall_mem_cons.2 ⟨sub5_588, List.forall_mem_cons.2 ⟨sub5_589, List.forall_mem_cons.2 ⟨sub5_590, List.forall_mem_cons.2 ⟨sub5_591, List.forall_mem_cons.2 ⟨sub5_592, List.forall_mem_cons.2 ⟨sub5_593, List.forall_mem_cons.2 ⟨sub5_594, List.forall_mem_cons.2 ⟨sub5_595, List.forall_mem_cons.2 ⟨sub5_596, List.forall_mem_cons.2 ⟨sub5_597, List.forall_mem_cons.2 ⟨sub5_598, List.forall_mem_cons.2 ⟨sub5_599, List.forall_mem_cons.2 ⟨sub5_600, List.forall_mem_cons.2 ⟨sub5_601, List.forall_mem_cons.2 ⟨sub5_602, List.forall_mem_cons.2 ⟨sub5_603, List.forall_mem_cons.2 ⟨sub5_604, List.forall_mem_cons.2 ⟨sub5_605, List.forall_mem_cons.2 ⟨sub5_606, List.forall_mem_cons.2 ⟨sub5_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_608 : sub5 [2, 1, 1] = true := by decide +kernel
theorem sub5_609 : sub5 [2, 1, 2] = true := by decide +kernel
theorem sub5_610 : sub5 [2, 1, 3] = true := by decide +kernel
theorem sub5_611 : sub5 [2, 1, 4] = true := by decide +kernel
theorem sub5_612 : sub5 [2, 1, 5] = true := by decide +kernel
theorem sub5_613 : sub5 [2, 1, 6] = true := by decide +kernel
theorem sub5_614 : sub5 [2, 1, 7] = true := by decide +kernel
theorem sub5_615 : sub5 [2, 1, 8] = true := by decide +kernel
theorem sub5_616 : sub5 [2, 2, -9] = true := by decide +kernel
theorem sub5_617 : sub5 [2, 2, -8] = true := by decide +kernel
theorem sub5_618 : sub5 [2, 2, -7] = true := by decide +kernel
theorem sub5_619 : sub5 [2, 2, -6] = true := by decide +kernel
theorem sub5_620 : sub5 [2, 2, -5] = true := by decide +kernel
theorem sub5_621 : sub5 [2, 2, -4] = true := by decide +kernel
theorem sub5_622 : sub5 [2, 2, -3] = true := by decide +kernel
theorem sub5_623 : sub5 [2, 2, -2] = true := by decide +kernel
theorem sub5_624 : sub5 [2, 2, -1] = true := by decide +kernel
theorem sub5_625 : sub5 [2, 2, 0] = true := by decide +kernel
theorem sub5_626 : sub5 [2, 2, 1] = true := by decide +kernel
theorem sub5_627 : sub5 [2, 2, 2] = true := by decide +kernel
theorem sub5_628 : sub5 [2, 2, 3] = true := by decide +kernel
theorem sub5_629 : sub5 [2, 2, 4] = true := by decide +kernel
theorem sub5_630 : sub5 [2, 2, 5] = true := by decide +kernel
theorem sub5_631 : sub5 [2, 2, 6] = true := by decide +kernel
theorem sub5_632 : sub5 [2, 2, 7] = true := by decide +kernel
theorem sub5_633 : sub5 [2, 3, -9] = true := by decide +kernel
theorem sub5_634 : sub5 [2, 3, -8] = true := by decide +kernel
theorem sub5_635 : sub5 [2, 3, -7] = true := by decide +kernel
theorem sub5_636 : sub5 [2, 3, -6] = true := by decide +kernel
theorem sub5_637 : sub5 [2, 3, -5] = true := by decide +kernel
theorem sub5_638 : sub5 [2, 3, -4] = true := by decide +kernel
theorem sub5_639 : sub5 [2, 3, -3] = true := by decide +kernel
theorem sb5_19 : ∀ q ∈ blk5_19, sub5 q = true := by
  unfold blk5_19
  exact List.forall_mem_cons.2 ⟨sub5_608, List.forall_mem_cons.2 ⟨sub5_609, List.forall_mem_cons.2 ⟨sub5_610, List.forall_mem_cons.2 ⟨sub5_611, List.forall_mem_cons.2 ⟨sub5_612, List.forall_mem_cons.2 ⟨sub5_613, List.forall_mem_cons.2 ⟨sub5_614, List.forall_mem_cons.2 ⟨sub5_615, List.forall_mem_cons.2 ⟨sub5_616, List.forall_mem_cons.2 ⟨sub5_617, List.forall_mem_cons.2 ⟨sub5_618, List.forall_mem_cons.2 ⟨sub5_619, List.forall_mem_cons.2 ⟨sub5_620, List.forall_mem_cons.2 ⟨sub5_621, List.forall_mem_cons.2 ⟨sub5_622, List.forall_mem_cons.2 ⟨sub5_623, List.forall_mem_cons.2 ⟨sub5_624, List.forall_mem_cons.2 ⟨sub5_625, List.forall_mem_cons.2 ⟨sub5_626, List.forall_mem_cons.2 ⟨sub5_627, List.forall_mem_cons.2 ⟨sub5_628, List.forall_mem_cons.2 ⟨sub5_629, List.forall_mem_cons.2 ⟨sub5_630, List.forall_mem_cons.2 ⟨sub5_631, List.forall_mem_cons.2 ⟨sub5_632, List.forall_mem_cons.2 ⟨sub5_633, List.forall_mem_cons.2 ⟨sub5_634, List.forall_mem_cons.2 ⟨sub5_635, List.forall_mem_cons.2 ⟨sub5_636, List.forall_mem_cons.2 ⟨sub5_637, List.forall_mem_cons.2 ⟨sub5_638, List.forall_mem_cons.2 ⟨sub5_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_640 : sub5 [2, 3, -2] = true := by decide +kernel
theorem sub5_641 : sub5 [2, 3, -1] = true := by decide +kernel
theorem sub5_642 : sub5 [2, 3, 0] = true := by decide +kernel
theorem sub5_643 : sub5 [2, 3, 1] = true := by decide +kernel
theorem sub5_644 : sub5 [2, 3, 2] = true := by decide +kernel
theorem sub5_645 : sub5 [2, 3, 3] = true := by decide +kernel
theorem sub5_646 : sub5 [2, 3, 4] = true := by decide +kernel
theorem sub5_647 : sub5 [2, 3, 5] = true := by decide +kernel
theorem sub5_648 : sub5 [2, 3, 6] = true := by decide +kernel
theorem sub5_649 : sub5 [2, 4] = true := by decide +kernel
theorem sub5_650 : sub5 [2, 5] = true := by decide +kernel
theorem sub5_651 : sub5 [3, -3] = true := by decide +kernel
theorem sub5_652 : sub5 [3, -2] = true := by decide +kernel
theorem sub5_653 : sub5 [3, -1] = true := by decide +kernel
theorem sub5_654 : sub5 [3, 0, -7] = true := by decide +kernel
theorem sub5_655 : sub5 [3, 0, -6] = true := by decide +kernel
theorem sub5_656 : sub5 [3, 0, -5] = true := by decide +kernel
theorem sub5_657 : sub5 [3, 0, -4] = true := by decide +kernel
theorem sub5_658 : sub5 [3, 0, -3] = true := by decide +kernel
theorem sub5_659 : sub5 [3, 0, -2] = true := by decide +kernel
theorem sub5_660 : sub5 [3, 0, -1] = true := by decide +kernel
theorem sub5_661 : sub5 [3, 0, 0] = true := by decide +kernel
theorem sub5_662 : sub5 [3, 0, 1] = true := by decide +kernel
theorem sub5_663 : sub5 [3, 0, 2] = true := by decide +kernel
theorem sub5_664 : sub5 [3, 0, 3] = true := by decide +kernel
theorem sub5_665 : sub5 [3, 0, 4] = true := by decide +kernel
theorem sub5_666 : sub5 [3, 0, 5] = true := by decide +kernel
theorem sub5_667 : sub5 [3, 0, 6] = true := by decide +kernel
theorem sub5_668 : sub5 [3, 0, 7] = true := by decide +kernel
theorem sub5_669 : sub5 [3, 1, -7] = true := by decide +kernel
theorem sub5_670 : sub5 [3, 1, -6] = true := by decide +kernel
theorem sub5_671 : sub5 [3, 1, -5] = true := by decide +kernel
theorem sb5_20 : ∀ q ∈ blk5_20, sub5 q = true := by
  unfold blk5_20
  exact List.forall_mem_cons.2 ⟨sub5_640, List.forall_mem_cons.2 ⟨sub5_641, List.forall_mem_cons.2 ⟨sub5_642, List.forall_mem_cons.2 ⟨sub5_643, List.forall_mem_cons.2 ⟨sub5_644, List.forall_mem_cons.2 ⟨sub5_645, List.forall_mem_cons.2 ⟨sub5_646, List.forall_mem_cons.2 ⟨sub5_647, List.forall_mem_cons.2 ⟨sub5_648, List.forall_mem_cons.2 ⟨sub5_649, List.forall_mem_cons.2 ⟨sub5_650, List.forall_mem_cons.2 ⟨sub5_651, List.forall_mem_cons.2 ⟨sub5_652, List.forall_mem_cons.2 ⟨sub5_653, List.forall_mem_cons.2 ⟨sub5_654, List.forall_mem_cons.2 ⟨sub5_655, List.forall_mem_cons.2 ⟨sub5_656, List.forall_mem_cons.2 ⟨sub5_657, List.forall_mem_cons.2 ⟨sub5_658, List.forall_mem_cons.2 ⟨sub5_659, List.forall_mem_cons.2 ⟨sub5_660, List.forall_mem_cons.2 ⟨sub5_661, List.forall_mem_cons.2 ⟨sub5_662, List.forall_mem_cons.2 ⟨sub5_663, List.forall_mem_cons.2 ⟨sub5_664, List.forall_mem_cons.2 ⟨sub5_665, List.forall_mem_cons.2 ⟨sub5_666, List.forall_mem_cons.2 ⟨sub5_667, List.forall_mem_cons.2 ⟨sub5_668, List.forall_mem_cons.2 ⟨sub5_669, List.forall_mem_cons.2 ⟨sub5_670, List.forall_mem_cons.2 ⟨sub5_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C073
