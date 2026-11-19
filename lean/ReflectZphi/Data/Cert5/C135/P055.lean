import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_5_256 : subd9_5 [0, -2, 10] = true := by decide +kernel
theorem subd9_5_257 : subd9_5 [0, -1, -11] = true := by decide +kernel
theorem subd9_5_258 : subd9_5 [0, -1, -10] = true := by decide +kernel
theorem subd9_5_259 : subd9_5 [0, -1, -9] = true := by decide +kernel
theorem subd9_5_260 : subd9_5 [0, -1, -8] = true := by decide +kernel
theorem subd9_5_261 : subd9_5 [0, -1, -7] = true := by decide +kernel
theorem subd9_5_262 : subd9_5 [0, -1, -6] = true := by decide +kernel
theorem subd9_5_263 : subd9_5 [0, -1, -5] = true := by decide +kernel
theorem subd9_5_264 : subd9_5 [0, -1, -4] = true := by decide +kernel
theorem subd9_5_265 : subd9_5 [0, -1, -3] = true := by decide +kernel
theorem subd9_5_266 : subd9_5 [0, -1, -2] = true := by decide +kernel
theorem subd9_5_267 : subd9_5 [0, -1, -1] = true := by decide +kernel
theorem subd9_5_268 : subd9_5 [0, -1, 0] = true := by decide +kernel
theorem subd9_5_269 : subd9_5 [0, -1, 1] = true := by decide +kernel
theorem subd9_5_270 : subd9_5 [0, -1, 2] = true := by decide +kernel
theorem subd9_5_271 : subd9_5 [0, -1, 3] = true := by decide +kernel
theorem subd9_5_272 : subd9_5 [0, -1, 4] = true := by decide +kernel
theorem subd9_5_273 : subd9_5 [0, -1, 5] = true := by decide +kernel
theorem subd9_5_274 : subd9_5 [0, -1, 6] = true := by decide +kernel
theorem subd9_5_275 : subd9_5 [0, -1, 7] = true := by decide +kernel
theorem subd9_5_276 : subd9_5 [0, -1, 8] = true := by decide +kernel
theorem subd9_5_277 : subd9_5 [0, -1, 9] = true := by decide +kernel
theorem subd9_5_278 : subd9_5 [0, -1, 10] = true := by decide +kernel
theorem subd9_5_279 : subd9_5 [0, -1, 11] = true := by decide +kernel
theorem subd9_5_280 : subd9_5 [0, 0, -12] = true := by decide +kernel
theorem subd9_5_281 : subd9_5 [0, 0, -11] = true := by decide +kernel
theorem subd9_5_282 : subd9_5 [0, 0, -10] = true := by decide +kernel
theorem subd9_5_283 : subd9_5 [0, 0, -9] = true := by decide +kernel
theorem subd9_5_284 : subd9_5 [0, 0, -8] = true := by decide +kernel
theorem subd9_5_285 : subd9_5 [0, 0, -7] = true := by decide +kernel
theorem subd9_5_286 : subd9_5 [0, 0, -6] = true := by decide +kernel
theorem subd9_5_287 : subd9_5 [0, 0, -5] = true := by decide +kernel
theorem sbd9_5_8 : ∀ q ∈ blkd9_5_8, subd9_5 q = true := by
  unfold blkd9_5_8
  exact List.forall_mem_cons.2 ⟨subd9_5_256, List.forall_mem_cons.2 ⟨subd9_5_257, List.forall_mem_cons.2 ⟨subd9_5_258, List.forall_mem_cons.2 ⟨subd9_5_259, List.forall_mem_cons.2 ⟨subd9_5_260, List.forall_mem_cons.2 ⟨subd9_5_261, List.forall_mem_cons.2 ⟨subd9_5_262, List.forall_mem_cons.2 ⟨subd9_5_263, List.forall_mem_cons.2 ⟨subd9_5_264, List.forall_mem_cons.2 ⟨subd9_5_265, List.forall_mem_cons.2 ⟨subd9_5_266, List.forall_mem_cons.2 ⟨subd9_5_267, List.forall_mem_cons.2 ⟨subd9_5_268, List.forall_mem_cons.2 ⟨subd9_5_269, List.forall_mem_cons.2 ⟨subd9_5_270, List.forall_mem_cons.2 ⟨subd9_5_271, List.forall_mem_cons.2 ⟨subd9_5_272, List.forall_mem_cons.2 ⟨subd9_5_273, List.forall_mem_cons.2 ⟨subd9_5_274, List.forall_mem_cons.2 ⟨subd9_5_275, List.forall_mem_cons.2 ⟨subd9_5_276, List.forall_mem_cons.2 ⟨subd9_5_277, List.forall_mem_cons.2 ⟨subd9_5_278, List.forall_mem_cons.2 ⟨subd9_5_279, List.forall_mem_cons.2 ⟨subd9_5_280, List.forall_mem_cons.2 ⟨subd9_5_281, List.forall_mem_cons.2 ⟨subd9_5_282, List.forall_mem_cons.2 ⟨subd9_5_283, List.forall_mem_cons.2 ⟨subd9_5_284, List.forall_mem_cons.2 ⟨subd9_5_285, List.forall_mem_cons.2 ⟨subd9_5_286, List.forall_mem_cons.2 ⟨subd9_5_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_5_288 : subd9_5 [0, 0, -4] = true := by decide +kernel
theorem subd9_5_289 : subd9_5 [0, 0, -3] = true := by decide +kernel
theorem subd9_5_290 : subd9_5 [0, 0, -2] = true := by decide +kernel
theorem subd9_5_291 : subd9_5 [0, 0, -1] = true := by decide +kernel
theorem subd9_5_292 : subd9_5 [0, 0, 0] = true := by decide +kernel
theorem subd9_5_293 : subd9_5 [0, 0, 1] = true := by decide +kernel
theorem subd9_5_294 : subd9_5 [0, 0, 2] = true := by decide +kernel
theorem subd9_5_295 : subd9_5 [0, 0, 3] = true := by decide +kernel
theorem subd9_5_296 : subd9_5 [0, 0, 4] = true := by decide +kernel
theorem subd9_5_297 : subd9_5 [0, 0, 5] = true := by decide +kernel
theorem subd9_5_298 : subd9_5 [0, 0, 6] = true := by decide +kernel
theorem subd9_5_299 : subd9_5 [0, 0, 7] = true := by decide +kernel
theorem subd9_5_300 : subd9_5 [0, 0, 8] = true := by decide +kernel
theorem subd9_5_301 : subd9_5 [0, 0, 9] = true := by decide +kernel
theorem subd9_5_302 : subd9_5 [0, 0, 10] = true := by decide +kernel
theorem subd9_5_303 : subd9_5 [0, 0, 11] = true := by decide +kernel
theorem subd9_5_304 : subd9_5 [0, 1, -12] = true := by decide +kernel
theorem subd9_5_305 : subd9_5 [0, 1, -11] = true := by decide +kernel
theorem subd9_5_306 : subd9_5 [0, 1, -10] = true := by decide +kernel
theorem subd9_5_307 : subd9_5 [0, 1, -9] = true := by decide +kernel
theorem subd9_5_308 : subd9_5 [0, 1, -8] = true := by decide +kernel
theorem subd9_5_309 : subd9_5 [0, 1, -7] = true := by decide +kernel
theorem subd9_5_310 : subd9_5 [0, 1, -6] = true := by decide +kernel
theorem subd9_5_311 : subd9_5 [0, 1, -5] = true := by decide +kernel
theorem subd9_5_312 : subd9_5 [0, 1, -4] = true := by decide +kernel
theorem subd9_5_313 : subd9_5 [0, 1, -3] = true := by decide +kernel
theorem subd9_5_314 : subd9_5 [0, 1, -2] = true := by decide +kernel
theorem subd9_5_315 : subd9_5 [0, 1, -1] = true := by decide +kernel
theorem subd9_5_316 : subd9_5 [0, 1, 0] = true := by decide +kernel
theorem subd9_5_317 : subd9_5 [0, 1, 1] = true := by decide +kernel
theorem subd9_5_318 : subd9_5 [0, 1, 2] = true := by decide +kernel
theorem subd9_5_319 : subd9_5 [0, 1, 3] = true := by decide +kernel
theorem sbd9_5_9 : ∀ q ∈ blkd9_5_9, subd9_5 q = true := by
  unfold blkd9_5_9
  exact List.forall_mem_cons.2 ⟨subd9_5_288, List.forall_mem_cons.2 ⟨subd9_5_289, List.forall_mem_cons.2 ⟨subd9_5_290, List.forall_mem_cons.2 ⟨subd9_5_291, List.forall_mem_cons.2 ⟨subd9_5_292, List.forall_mem_cons.2 ⟨subd9_5_293, List.forall_mem_cons.2 ⟨subd9_5_294, List.forall_mem_cons.2 ⟨subd9_5_295, List.forall_mem_cons.2 ⟨subd9_5_296, List.forall_mem_cons.2 ⟨subd9_5_297, List.forall_mem_cons.2 ⟨subd9_5_298, List.forall_mem_cons.2 ⟨subd9_5_299, List.forall_mem_cons.2 ⟨subd9_5_300, List.forall_mem_cons.2 ⟨subd9_5_301, List.forall_mem_cons.2 ⟨subd9_5_302, List.forall_mem_cons.2 ⟨subd9_5_303, List.forall_mem_cons.2 ⟨subd9_5_304, List.forall_mem_cons.2 ⟨subd9_5_305, List.forall_mem_cons.2 ⟨subd9_5_306, List.forall_mem_cons.2 ⟨subd9_5_307, List.forall_mem_cons.2 ⟨subd9_5_308, List.forall_mem_cons.2 ⟨subd9_5_309, List.forall_mem_cons.2 ⟨subd9_5_310, List.forall_mem_cons.2 ⟨subd9_5_311, List.forall_mem_cons.2 ⟨subd9_5_312, List.forall_mem_cons.2 ⟨subd9_5_313, List.forall_mem_cons.2 ⟨subd9_5_314, List.forall_mem_cons.2 ⟨subd9_5_315, List.forall_mem_cons.2 ⟨subd9_5_316, List.forall_mem_cons.2 ⟨subd9_5_317, List.forall_mem_cons.2 ⟨subd9_5_318, List.forall_mem_cons.2 ⟨subd9_5_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_5_320 : subd9_5 [0, 1, 4] = true := by decide +kernel
theorem subd9_5_321 : subd9_5 [0, 1, 5] = true := by decide +kernel
theorem subd9_5_322 : subd9_5 [0, 1, 6] = true := by decide +kernel
theorem subd9_5_323 : subd9_5 [0, 1, 7] = true := by decide +kernel
theorem subd9_5_324 : subd9_5 [0, 1, 8] = true := by decide +kernel
theorem subd9_5_325 : subd9_5 [0, 1, 9] = true := by decide +kernel
theorem subd9_5_326 : subd9_5 [0, 1, 10] = true := by decide +kernel
theorem subd9_5_327 : subd9_5 [0, 2, -11] = true := by decide +kernel
theorem subd9_5_328 : subd9_5 [0, 2, -10] = true := by decide +kernel
theorem subd9_5_329 : subd9_5 [0, 2, -9] = true := by decide +kernel
theorem subd9_5_330 : subd9_5 [0, 2, -8] = true := by decide +kernel
theorem subd9_5_331 : subd9_5 [0, 2, -7] = true := by decide +kernel
theorem subd9_5_332 : subd9_5 [0, 2, -6] = true := by decide +kernel
theorem subd9_5_333 : subd9_5 [0, 2, -5] = true := by decide +kernel
theorem subd9_5_334 : subd9_5 [0, 2, -4] = true := by decide +kernel
theorem subd9_5_335 : subd9_5 [0, 2, -3] = true := by decide +kernel
theorem subd9_5_336 : subd9_5 [0, 2, -2] = true := by decide +kernel
theorem subd9_5_337 : subd9_5 [0, 2, -1] = true := by decide +kernel
theorem subd9_5_338 : subd9_5 [0, 2, 0] = true := by decide +kernel
theorem subd9_5_339 : subd9_5 [0, 2, 1] = true := by decide +kernel
theorem subd9_5_340 : subd9_5 [0, 2, 2] = true := by decide +kernel
theorem subd9_5_341 : subd9_5 [0, 2, 3] = true := by decide +kernel
theorem subd9_5_342 : subd9_5 [0, 2, 4] = true := by decide +kernel
theorem subd9_5_343 : subd9_5 [0, 2, 5] = true := by decide +kernel
theorem subd9_5_344 : subd9_5 [0, 2, 6] = true := by decide +kernel
theorem subd9_5_345 : subd9_5 [0, 2, 7] = true := by decide +kernel
theorem subd9_5_346 : subd9_5 [0, 2, 8] = true := by decide +kernel
theorem subd9_5_347 : subd9_5 [0, 2, 9] = true := by decide +kernel
theorem subd9_5_348 : subd9_5 [0, 3, -8] = true := by decide +kernel
theorem subd9_5_349 : subd9_5 [0, 3, -7] = true := by decide +kernel
theorem subd9_5_350 : subd9_5 [0, 3, -6] = true := by decide +kernel
theorem subd9_5_351 : subd9_5 [0, 3, -5] = true := by decide +kernel
theorem sbd9_5_10 : ∀ q ∈ blkd9_5_10, subd9_5 q = true := by
  unfold blkd9_5_10
  exact List.forall_mem_cons.2 ⟨subd9_5_320, List.forall_mem_cons.2 ⟨subd9_5_321, List.forall_mem_cons.2 ⟨subd9_5_322, List.forall_mem_cons.2 ⟨subd9_5_323, List.forall_mem_cons.2 ⟨subd9_5_324, List.forall_mem_cons.2 ⟨subd9_5_325, List.forall_mem_cons.2 ⟨subd9_5_326, List.forall_mem_cons.2 ⟨subd9_5_327, List.forall_mem_cons.2 ⟨subd9_5_328, List.forall_mem_cons.2 ⟨subd9_5_329, List.forall_mem_cons.2 ⟨subd9_5_330, List.forall_mem_cons.2 ⟨subd9_5_331, List.forall_mem_cons.2 ⟨subd9_5_332, List.forall_mem_cons.2 ⟨subd9_5_333, List.forall_mem_cons.2 ⟨subd9_5_334, List.forall_mem_cons.2 ⟨subd9_5_335, List.forall_mem_cons.2 ⟨subd9_5_336, List.forall_mem_cons.2 ⟨subd9_5_337, List.forall_mem_cons.2 ⟨subd9_5_338, List.forall_mem_cons.2 ⟨subd9_5_339, List.forall_mem_cons.2 ⟨subd9_5_340, List.forall_mem_cons.2 ⟨subd9_5_341, List.forall_mem_cons.2 ⟨subd9_5_342, List.forall_mem_cons.2 ⟨subd9_5_343, List.forall_mem_cons.2 ⟨subd9_5_344, List.forall_mem_cons.2 ⟨subd9_5_345, List.forall_mem_cons.2 ⟨subd9_5_346, List.forall_mem_cons.2 ⟨subd9_5_347, List.forall_mem_cons.2 ⟨subd9_5_348, List.forall_mem_cons.2 ⟨subd9_5_349, List.forall_mem_cons.2 ⟨subd9_5_350, List.forall_mem_cons.2 ⟨subd9_5_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_5_352 : subd9_5 [0, 3, -4] = true := by decide +kernel
theorem subd9_5_353 : subd9_5 [0, 3, -3] = true := by decide +kernel
theorem subd9_5_354 : subd9_5 [0, 3, -2] = true := by decide +kernel
theorem subd9_5_355 : subd9_5 [0, 3, -1] = true := by decide +kernel
theorem subd9_5_356 : subd9_5 [0, 3, 0] = true := by decide +kernel
theorem subd9_5_357 : subd9_5 [0, 3, 1] = true := by decide +kernel
theorem subd9_5_358 : subd9_5 [0, 3, 2] = true := by decide +kernel
theorem subd9_5_359 : subd9_5 [0, 3, 3] = true := by decide +kernel
theorem subd9_5_360 : subd9_5 [0, 3, 4] = true := by decide +kernel
theorem subd9_5_361 : subd9_5 [0, 3, 5] = true := by decide +kernel
theorem subd9_5_362 : subd9_5 [1, -4] = true := by decide +kernel
theorem subd9_5_363 : subd9_5 [1, -3] = true := by decide +kernel
theorem subd9_5_364 : subd9_5 [1, -2, -9] = true := by decide +kernel
theorem subd9_5_365 : subd9_5 [1, -2, -8] = true := by decide +kernel
theorem subd9_5_366 : subd9_5 [1, -2, -7] = true := by decide +kernel
theorem subd9_5_367 : subd9_5 [1, -2, -6] = true := by decide +kernel
theorem subd9_5_368 : subd9_5 [1, -2, -5] = true := by decide +kernel
theorem subd9_5_369 : subd9_5 [1, -2, -4] = true := by decide +kernel
theorem subd9_5_370 : subd9_5 [1, -2, -3] = true := by decide +kernel
theorem subd9_5_371 : subd9_5 [1, -2, -2] = true := by decide +kernel
theorem subd9_5_372 : subd9_5 [1, -2, -1] = true := by decide +kernel
theorem subd9_5_373 : subd9_5 [1, -2, 0] = true := by decide +kernel
theorem subd9_5_374 : subd9_5 [1, -2, 1] = true := by decide +kernel
theorem subd9_5_375 : subd9_5 [1, -2, 2] = true := by decide +kernel
theorem subd9_5_376 : subd9_5 [1, -2, 3] = true := by decide +kernel
theorem subd9_5_377 : subd9_5 [1, -2, 4] = true := by decide +kernel
theorem subd9_5_378 : subd9_5 [1, -2, 5] = true := by decide +kernel
theorem subd9_5_379 : subd9_5 [1, -2, 6] = true := by decide +kernel
theorem subd9_5_380 : subd9_5 [1, -2, 7] = true := by decide +kernel
theorem subd9_5_381 : subd9_5 [1, -2, 8] = true := by decide +kernel
theorem subd9_5_382 : subd9_5 [1, -2, 9] = true := by decide +kernel
theorem subd9_5_383 : subd9_5 [1, -1, -11] = true := by decide +kernel
theorem sbd9_5_11 : ∀ q ∈ blkd9_5_11, subd9_5 q = true := by
  unfold blkd9_5_11
  exact List.forall_mem_cons.2 ⟨subd9_5_352, List.forall_mem_cons.2 ⟨subd9_5_353, List.forall_mem_cons.2 ⟨subd9_5_354, List.forall_mem_cons.2 ⟨subd9_5_355, List.forall_mem_cons.2 ⟨subd9_5_356, List.forall_mem_cons.2 ⟨subd9_5_357, List.forall_mem_cons.2 ⟨subd9_5_358, List.forall_mem_cons.2 ⟨subd9_5_359, List.forall_mem_cons.2 ⟨subd9_5_360, List.forall_mem_cons.2 ⟨subd9_5_361, List.forall_mem_cons.2 ⟨subd9_5_362, List.forall_mem_cons.2 ⟨subd9_5_363, List.forall_mem_cons.2 ⟨subd9_5_364, List.forall_mem_cons.2 ⟨subd9_5_365, List.forall_mem_cons.2 ⟨subd9_5_366, List.forall_mem_cons.2 ⟨subd9_5_367, List.forall_mem_cons.2 ⟨subd9_5_368, List.forall_mem_cons.2 ⟨subd9_5_369, List.forall_mem_cons.2 ⟨subd9_5_370, List.forall_mem_cons.2 ⟨subd9_5_371, List.forall_mem_cons.2 ⟨subd9_5_372, List.forall_mem_cons.2 ⟨subd9_5_373, List.forall_mem_cons.2 ⟨subd9_5_374, List.forall_mem_cons.2 ⟨subd9_5_375, List.forall_mem_cons.2 ⟨subd9_5_376, List.forall_mem_cons.2 ⟨subd9_5_377, List.forall_mem_cons.2 ⟨subd9_5_378, List.forall_mem_cons.2 ⟨subd9_5_379, List.forall_mem_cons.2 ⟨subd9_5_380, List.forall_mem_cons.2 ⟨subd9_5_381, List.forall_mem_cons.2 ⟨subd9_5_382, List.forall_mem_cons.2 ⟨subd9_5_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_5_384 : subd9_5 [1, -1, -10] = true := by decide +kernel
theorem subd9_5_385 : subd9_5 [1, -1, -9] = true := by decide +kernel
theorem subd9_5_386 : subd9_5 [1, -1, -8] = true := by decide +kernel
theorem subd9_5_387 : subd9_5 [1, -1, -7] = true := by decide +kernel
theorem subd9_5_388 : subd9_5 [1, -1, -6] = true := by decide +kernel
theorem subd9_5_389 : subd9_5 [1, -1, -5] = true := by decide +kernel
theorem subd9_5_390 : subd9_5 [1, -1, -4] = true := by decide +kernel
theorem subd9_5_391 : subd9_5 [1, -1, -3] = true := by decide +kernel
theorem subd9_5_392 : subd9_5 [1, -1, -2] = true := by decide +kernel
theorem subd9_5_393 : subd9_5 [1, -1, -1] = true := by decide +kernel
theorem subd9_5_394 : subd9_5 [1, -1, 0] = true := by decide +kernel
theorem subd9_5_395 : subd9_5 [1, -1, 1] = true := by decide +kernel
theorem subd9_5_396 : subd9_5 [1, -1, 2] = true := by decide +kernel
theorem subd9_5_397 : subd9_5 [1, -1, 3] = true := by decide +kernel
theorem subd9_5_398 : subd9_5 [1, -1, 4] = true := by decide +kernel
theorem subd9_5_399 : subd9_5 [1, -1, 5] = true := by decide +kernel
theorem subd9_5_400 : subd9_5 [1, -1, 6] = true := by decide +kernel
theorem subd9_5_401 : subd9_5 [1, -1, 7] = true := by decide +kernel
theorem subd9_5_402 : subd9_5 [1, -1, 8] = true := by decide +kernel
theorem subd9_5_403 : subd9_5 [1, -1, 9] = true := by decide +kernel
theorem subd9_5_404 : subd9_5 [1, -1, 10] = true := by decide +kernel
theorem subd9_5_405 : subd9_5 [1, 0, -12] = true := by decide +kernel
theorem subd9_5_406 : subd9_5 [1, 0, -11] = true := by decide +kernel
theorem subd9_5_407 : subd9_5 [1, 0, -10] = true := by decide +kernel
theorem subd9_5_408 : subd9_5 [1, 0, -9] = true := by decide +kernel
theorem subd9_5_409 : subd9_5 [1, 0, -8] = true := by decide +kernel
theorem subd9_5_410 : subd9_5 [1, 0, -7] = true := by decide +kernel
theorem subd9_5_411 : subd9_5 [1, 0, -6] = true := by decide +kernel
theorem subd9_5_412 : subd9_5 [1, 0, -5] = true := by decide +kernel
theorem subd9_5_413 : subd9_5 [1, 0, -4] = true := by decide +kernel
theorem subd9_5_414 : subd9_5 [1, 0, -3] = true := by decide +kernel
theorem subd9_5_415 : subd9_5 [1, 0, -2] = true := by decide +kernel
theorem sbd9_5_12 : ∀ q ∈ blkd9_5_12, subd9_5 q = true := by
  unfold blkd9_5_12
  exact List.forall_mem_cons.2 ⟨subd9_5_384, List.forall_mem_cons.2 ⟨subd9_5_385, List.forall_mem_cons.2 ⟨subd9_5_386, List.forall_mem_cons.2 ⟨subd9_5_387, List.forall_mem_cons.2 ⟨subd9_5_388, List.forall_mem_cons.2 ⟨subd9_5_389, List.forall_mem_cons.2 ⟨subd9_5_390, List.forall_mem_cons.2 ⟨subd9_5_391, List.forall_mem_cons.2 ⟨subd9_5_392, List.forall_mem_cons.2 ⟨subd9_5_393, List.forall_mem_cons.2 ⟨subd9_5_394, List.forall_mem_cons.2 ⟨subd9_5_395, List.forall_mem_cons.2 ⟨subd9_5_396, List.forall_mem_cons.2 ⟨subd9_5_397, List.forall_mem_cons.2 ⟨subd9_5_398, List.forall_mem_cons.2 ⟨subd9_5_399, List.forall_mem_cons.2 ⟨subd9_5_400, List.forall_mem_cons.2 ⟨subd9_5_401, List.forall_mem_cons.2 ⟨subd9_5_402, List.forall_mem_cons.2 ⟨subd9_5_403, List.forall_mem_cons.2 ⟨subd9_5_404, List.forall_mem_cons.2 ⟨subd9_5_405, List.forall_mem_cons.2 ⟨subd9_5_406, List.forall_mem_cons.2 ⟨subd9_5_407, List.forall_mem_cons.2 ⟨subd9_5_408, List.forall_mem_cons.2 ⟨subd9_5_409, List.forall_mem_cons.2 ⟨subd9_5_410, List.forall_mem_cons.2 ⟨subd9_5_411, List.forall_mem_cons.2 ⟨subd9_5_412, List.forall_mem_cons.2 ⟨subd9_5_413, List.forall_mem_cons.2 ⟨subd9_5_414, List.forall_mem_cons.2 ⟨subd9_5_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_5_416 : subd9_5 [1, 0, -1] = true := by decide +kernel
theorem subd9_5_417 : subd9_5 [1, 0, 0] = true := by decide +kernel
theorem subd9_5_418 : subd9_5 [1, 0, 1] = true := by decide +kernel
theorem subd9_5_419 : subd9_5 [1, 0, 2] = true := by decide +kernel
theorem subd9_5_420 : subd9_5 [1, 0, 3] = true := by decide +kernel
theorem subd9_5_421 : subd9_5 [1, 0, 4] = true := by decide +kernel
theorem subd9_5_422 : subd9_5 [1, 0, 5] = true := by decide +kernel
theorem subd9_5_423 : subd9_5 [1, 0, 6] = true := by decide +kernel
theorem subd9_5_424 : subd9_5 [1, 0, 7] = true := by decide +kernel
theorem subd9_5_425 : subd9_5 [1, 0, 8] = true := by decide +kernel
theorem subd9_5_426 : subd9_5 [1, 0, 9] = true := by decide +kernel
theorem subd9_5_427 : subd9_5 [1, 0, 10] = true := by decide +kernel
theorem subd9_5_428 : subd9_5 [1, 1, -12] = true := by decide +kernel
theorem subd9_5_429 : subd9_5 [1, 1, -11] = true := by decide +kernel
theorem subd9_5_430 : subd9_5 [1, 1, -10] = true := by decide +kernel
theorem subd9_5_431 : subd9_5 [1, 1, -9] = true := by decide +kernel
theorem subd9_5_432 : subd9_5 [1, 1, -8] = true := by decide +kernel
theorem subd9_5_433 : subd9_5 [1, 1, -7] = true := by decide +kernel
theorem subd9_5_434 : subd9_5 [1, 1, -6] = true := by decide +kernel
theorem subd9_5_435 : subd9_5 [1, 1, -5] = true := by decide +kernel
theorem subd9_5_436 : subd9_5 [1, 1, -4] = true := by decide +kernel
theorem subd9_5_437 : subd9_5 [1, 1, -3] = true := by decide +kernel
theorem subd9_5_438 : subd9_5 [1, 1, -2] = true := by decide +kernel
theorem subd9_5_439 : subd9_5 [1, 1, -1] = true := by decide +kernel
theorem subd9_5_440 : subd9_5 [1, 1, 0] = true := by decide +kernel
theorem subd9_5_441 : subd9_5 [1, 1, 1] = true := by decide +kernel
theorem subd9_5_442 : subd9_5 [1, 1, 2] = true := by decide +kernel
theorem subd9_5_443 : subd9_5 [1, 1, 3] = true := by decide +kernel
theorem subd9_5_444 : subd9_5 [1, 1, 4] = true := by decide +kernel
theorem subd9_5_445 : subd9_5 [1, 1, 5] = true := by decide +kernel
theorem subd9_5_446 : subd9_5 [1, 1, 6] = true := by decide +kernel
theorem subd9_5_447 : subd9_5 [1, 1, 7] = true := by decide +kernel
theorem sbd9_5_13 : ∀ q ∈ blkd9_5_13, subd9_5 q = true := by
  unfold blkd9_5_13
  exact List.forall_mem_cons.2 ⟨subd9_5_416, List.forall_mem_cons.2 ⟨subd9_5_417, List.forall_mem_cons.2 ⟨subd9_5_418, List.forall_mem_cons.2 ⟨subd9_5_419, List.forall_mem_cons.2 ⟨subd9_5_420, List.forall_mem_cons.2 ⟨subd9_5_421, List.forall_mem_cons.2 ⟨subd9_5_422, List.forall_mem_cons.2 ⟨subd9_5_423, List.forall_mem_cons.2 ⟨subd9_5_424, List.forall_mem_cons.2 ⟨subd9_5_425, List.forall_mem_cons.2 ⟨subd9_5_426, List.forall_mem_cons.2 ⟨subd9_5_427, List.forall_mem_cons.2 ⟨subd9_5_428, List.forall_mem_cons.2 ⟨subd9_5_429, List.forall_mem_cons.2 ⟨subd9_5_430, List.forall_mem_cons.2 ⟨subd9_5_431, List.forall_mem_cons.2 ⟨subd9_5_432, List.forall_mem_cons.2 ⟨subd9_5_433, List.forall_mem_cons.2 ⟨subd9_5_434, List.forall_mem_cons.2 ⟨subd9_5_435, List.forall_mem_cons.2 ⟨subd9_5_436, List.forall_mem_cons.2 ⟨subd9_5_437, List.forall_mem_cons.2 ⟨subd9_5_438, List.forall_mem_cons.2 ⟨subd9_5_439, List.forall_mem_cons.2 ⟨subd9_5_440, List.forall_mem_cons.2 ⟨subd9_5_441, List.forall_mem_cons.2 ⟨subd9_5_442, List.forall_mem_cons.2 ⟨subd9_5_443, List.forall_mem_cons.2 ⟨subd9_5_444, List.forall_mem_cons.2 ⟨subd9_5_445, List.forall_mem_cons.2 ⟨subd9_5_446, List.forall_mem_cons.2 ⟨subd9_5_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_5_448 : subd9_5 [1, 1, 8] = true := by decide +kernel
theorem subd9_5_449 : subd9_5 [1, 1, 9] = true := by decide +kernel
theorem subd9_5_450 : subd9_5 [1, 1, 10] = true := by decide +kernel
theorem subd9_5_451 : subd9_5 [1, 2, -10] = true := by decide +kernel
theorem subd9_5_452 : subd9_5 [1, 2, -9] = true := by decide +kernel
theorem subd9_5_453 : subd9_5 [1, 2, -8] = true := by decide +kernel
theorem subd9_5_454 : subd9_5 [1, 2, -7] = true := by decide +kernel
theorem subd9_5_455 : subd9_5 [1, 2, -6] = true := by decide +kernel
theorem subd9_5_456 : subd9_5 [1, 2, -5] = true := by decide +kernel
theorem subd9_5_457 : subd9_5 [1, 2, -4] = true := by decide +kernel
theorem subd9_5_458 : subd9_5 [1, 2, -3] = true := by decide +kernel
theorem subd9_5_459 : subd9_5 [1, 2, -2] = true := by decide +kernel
theorem subd9_5_460 : subd9_5 [1, 2, -1] = true := by decide +kernel
theorem subd9_5_461 : subd9_5 [1, 2, 0] = true := by decide +kernel
theorem subd9_5_462 : subd9_5 [1, 2, 1] = true := by decide +kernel
theorem subd9_5_463 : subd9_5 [1, 2, 2] = true := by decide +kernel
theorem subd9_5_464 : subd9_5 [1, 2, 3] = true := by decide +kernel
theorem subd9_5_465 : subd9_5 [1, 2, 4] = true := by decide +kernel
theorem subd9_5_466 : subd9_5 [1, 2, 5] = true := by decide +kernel
theorem subd9_5_467 : subd9_5 [1, 2, 6] = true := by decide +kernel
theorem subd9_5_468 : subd9_5 [1, 2, 7] = true := by decide +kernel
theorem subd9_5_469 : subd9_5 [1, 2, 8] = true := by decide +kernel
theorem subd9_5_470 : subd9_5 [1, 3] = true := by decide +kernel
theorem subd9_5_471 : subd9_5 [2, -4] = true := by decide +kernel
theorem subd9_5_472 : subd9_5 [2, -3] = true := by decide +kernel
theorem subd9_5_473 : subd9_5 [2, -2, -8] = true := by decide +kernel
theorem subd9_5_474 : subd9_5 [2, -2, -7] = true := by decide +kernel
theorem subd9_5_475 : subd9_5 [2, -2, -6] = true := by decide +kernel
theorem subd9_5_476 : subd9_5 [2, -2, -5] = true := by decide +kernel
theorem subd9_5_477 : subd9_5 [2, -2, -4] = true := by decide +kernel
theorem subd9_5_478 : subd9_5 [2, -2, -3] = true := by decide +kernel
theorem subd9_5_479 : subd9_5 [2, -2, -2] = true := by decide +kernel
theorem sbd9_5_14 : ∀ q ∈ blkd9_5_14, subd9_5 q = true := by
  unfold blkd9_5_14
  exact List.forall_mem_cons.2 ⟨subd9_5_448, List.forall_mem_cons.2 ⟨subd9_5_449, List.forall_mem_cons.2 ⟨subd9_5_450, List.forall_mem_cons.2 ⟨subd9_5_451, List.forall_mem_cons.2 ⟨subd9_5_452, List.forall_mem_cons.2 ⟨subd9_5_453, List.forall_mem_cons.2 ⟨subd9_5_454, List.forall_mem_cons.2 ⟨subd9_5_455, List.forall_mem_cons.2 ⟨subd9_5_456, List.forall_mem_cons.2 ⟨subd9_5_457, List.forall_mem_cons.2 ⟨subd9_5_458, List.forall_mem_cons.2 ⟨subd9_5_459, List.forall_mem_cons.2 ⟨subd9_5_460, List.forall_mem_cons.2 ⟨subd9_5_461, List.forall_mem_cons.2 ⟨subd9_5_462, List.forall_mem_cons.2 ⟨subd9_5_463, List.forall_mem_cons.2 ⟨subd9_5_464, List.forall_mem_cons.2 ⟨subd9_5_465, List.forall_mem_cons.2 ⟨subd9_5_466, List.forall_mem_cons.2 ⟨subd9_5_467, List.forall_mem_cons.2 ⟨subd9_5_468, List.forall_mem_cons.2 ⟨subd9_5_469, List.forall_mem_cons.2 ⟨subd9_5_470, List.forall_mem_cons.2 ⟨subd9_5_471, List.forall_mem_cons.2 ⟨subd9_5_472, List.forall_mem_cons.2 ⟨subd9_5_473, List.forall_mem_cons.2 ⟨subd9_5_474, List.forall_mem_cons.2 ⟨subd9_5_475, List.forall_mem_cons.2 ⟨subd9_5_476, List.forall_mem_cons.2 ⟨subd9_5_477, List.forall_mem_cons.2 ⟨subd9_5_478, List.forall_mem_cons.2 ⟨subd9_5_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_5_480 : subd9_5 [2, -2, -1] = true := by decide +kernel
theorem subd9_5_481 : subd9_5 [2, -2, 0] = true := by decide +kernel
theorem subd9_5_482 : subd9_5 [2, -2, 1] = true := by decide +kernel
theorem subd9_5_483 : subd9_5 [2, -2, 2] = true := by decide +kernel
theorem subd9_5_484 : subd9_5 [2, -2, 3] = true := by decide +kernel
theorem subd9_5_485 : subd9_5 [2, -2, 4] = true := by decide +kernel
theorem subd9_5_486 : subd9_5 [2, -2, 5] = true := by decide +kernel
theorem subd9_5_487 : subd9_5 [2, -2, 6] = true := by decide +kernel
theorem subd9_5_488 : subd9_5 [2, -2, 7] = true := by decide +kernel
theorem subd9_5_489 : subd9_5 [2, -1, -10] = true := by decide +kernel
theorem subd9_5_490 : subd9_5 [2, -1, -9] = true := by decide +kernel
theorem subd9_5_491 : subd9_5 [2, -1, -8] = true := by decide +kernel
theorem subd9_5_492 : subd9_5 [2, -1, -7] = true := by decide +kernel
theorem subd9_5_493 : subd9_5 [2, -1, -6] = true := by decide +kernel
theorem subd9_5_494 : subd9_5 [2, -1, -5] = true := by decide +kernel
theorem subd9_5_495 : subd9_5 [2, -1, -4] = true := by decide +kernel
theorem subd9_5_496 : subd9_5 [2, -1, -3] = true := by decide +kernel
theorem subd9_5_497 : subd9_5 [2, -1, -2] = true := by decide +kernel
theorem subd9_5_498 : subd9_5 [2, -1, -1] = true := by decide +kernel
theorem subd9_5_499 : subd9_5 [2, -1, 0] = true := by decide +kernel
theorem subd9_5_500 : subd9_5 [2, -1, 1] = true := by decide +kernel
theorem subd9_5_501 : subd9_5 [2, -1, 2] = true := by decide +kernel
theorem subd9_5_502 : subd9_5 [2, -1, 3] = true := by decide +kernel
theorem subd9_5_503 : subd9_5 [2, -1, 4] = true := by decide +kernel
theorem subd9_5_504 : subd9_5 [2, -1, 5] = true := by decide +kernel
theorem subd9_5_505 : subd9_5 [2, -1, 6] = true := by decide +kernel
theorem subd9_5_506 : subd9_5 [2, -1, 7] = true := by decide +kernel
theorem subd9_5_507 : subd9_5 [2, -1, 8] = true := by decide +kernel
theorem subd9_5_508 : subd9_5 [2, 0, -11] = true := by decide +kernel
theorem subd9_5_509 : subd9_5 [2, 0, -10] = true := by decide +kernel
theorem subd9_5_510 : subd9_5 [2, 0, -9] = true := by decide +kernel
theorem subd9_5_511 : subd9_5 [2, 0, -8] = true := by decide +kernel
theorem sbd9_5_15 : ∀ q ∈ blkd9_5_15, subd9_5 q = true := by
  unfold blkd9_5_15
  exact List.forall_mem_cons.2 ⟨subd9_5_480, List.forall_mem_cons.2 ⟨subd9_5_481, List.forall_mem_cons.2 ⟨subd9_5_482, List.forall_mem_cons.2 ⟨subd9_5_483, List.forall_mem_cons.2 ⟨subd9_5_484, List.forall_mem_cons.2 ⟨subd9_5_485, List.forall_mem_cons.2 ⟨subd9_5_486, List.forall_mem_cons.2 ⟨subd9_5_487, List.forall_mem_cons.2 ⟨subd9_5_488, List.forall_mem_cons.2 ⟨subd9_5_489, List.forall_mem_cons.2 ⟨subd9_5_490, List.forall_mem_cons.2 ⟨subd9_5_491, List.forall_mem_cons.2 ⟨subd9_5_492, List.forall_mem_cons.2 ⟨subd9_5_493, List.forall_mem_cons.2 ⟨subd9_5_494, List.forall_mem_cons.2 ⟨subd9_5_495, List.forall_mem_cons.2 ⟨subd9_5_496, List.forall_mem_cons.2 ⟨subd9_5_497, List.forall_mem_cons.2 ⟨subd9_5_498, List.forall_mem_cons.2 ⟨subd9_5_499, List.forall_mem_cons.2 ⟨subd9_5_500, List.forall_mem_cons.2 ⟨subd9_5_501, List.forall_mem_cons.2 ⟨subd9_5_502, List.forall_mem_cons.2 ⟨subd9_5_503, List.forall_mem_cons.2 ⟨subd9_5_504, List.forall_mem_cons.2 ⟨subd9_5_505, List.forall_mem_cons.2 ⟨subd9_5_506, List.forall_mem_cons.2 ⟨subd9_5_507, List.forall_mem_cons.2 ⟨subd9_5_508, List.forall_mem_cons.2 ⟨subd9_5_509, List.forall_mem_cons.2 ⟨subd9_5_510, List.forall_mem_cons.2 ⟨subd9_5_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_5_512 : subd9_5 [2, 0, -7] = true := by decide +kernel
theorem subd9_5_513 : subd9_5 [2, 0, -6] = true := by decide +kernel
theorem subd9_5_514 : subd9_5 [2, 0, -5] = true := by decide +kernel
theorem subd9_5_515 : subd9_5 [2, 0, -4] = true := by decide +kernel
theorem subd9_5_516 : subd9_5 [2, 0, -3] = true := by decide +kernel
theorem subd9_5_517 : subd9_5 [2, 0, -2] = true := by decide +kernel
theorem subd9_5_518 : subd9_5 [2, 0, -1] = true := by decide +kernel
theorem subd9_5_519 : subd9_5 [2, 0, 0] = true := by decide +kernel
theorem subd9_5_520 : subd9_5 [2, 0, 1] = true := by decide +kernel
theorem subd9_5_521 : subd9_5 [2, 0, 2] = true := by decide +kernel
theorem subd9_5_522 : subd9_5 [2, 0, 3] = true := by decide +kernel
theorem subd9_5_523 : subd9_5 [2, 0, 4] = true := by decide +kernel
theorem subd9_5_524 : subd9_5 [2, 0, 5] = true := by decide +kernel
theorem subd9_5_525 : subd9_5 [2, 0, 6] = true := by decide +kernel
theorem subd9_5_526 : subd9_5 [2, 0, 7] = true := by decide +kernel
theorem subd9_5_527 : subd9_5 [2, 0, 8] = true := by decide +kernel
theorem subd9_5_528 : subd9_5 [2, 1, -10] = true := by decide +kernel
theorem subd9_5_529 : subd9_5 [2, 1, -9] = true := by decide +kernel
theorem subd9_5_530 : subd9_5 [2, 1, -8] = true := by decide +kernel
theorem subd9_5_531 : subd9_5 [2, 1, -7] = true := by decide +kernel
theorem subd9_5_532 : subd9_5 [2, 1, -6] = true := by decide +kernel
theorem subd9_5_533 : subd9_5 [2, 1, -5] = true := by decide +kernel
theorem subd9_5_534 : subd9_5 [2, 1, -4] = true := by decide +kernel
theorem subd9_5_535 : subd9_5 [2, 1, -3] = true := by decide +kernel
theorem subd9_5_536 : subd9_5 [2, 1, -2] = true := by decide +kernel
theorem subd9_5_537 : subd9_5 [2, 1, -1] = true := by decide +kernel
theorem subd9_5_538 : subd9_5 [2, 1, 0] = true := by decide +kernel
theorem subd9_5_539 : subd9_5 [2, 1, 1] = true := by decide +kernel
theorem subd9_5_540 : subd9_5 [2, 1, 2] = true := by decide +kernel
theorem subd9_5_541 : subd9_5 [2, 1, 3] = true := by decide +kernel
theorem subd9_5_542 : subd9_5 [2, 1, 4] = true := by decide +kernel
theorem subd9_5_543 : subd9_5 [2, 1, 5] = true := by decide +kernel
theorem sbd9_5_16 : ∀ q ∈ blkd9_5_16, subd9_5 q = true := by
  unfold blkd9_5_16
  exact List.forall_mem_cons.2 ⟨subd9_5_512, List.forall_mem_cons.2 ⟨subd9_5_513, List.forall_mem_cons.2 ⟨subd9_5_514, List.forall_mem_cons.2 ⟨subd9_5_515, List.forall_mem_cons.2 ⟨subd9_5_516, List.forall_mem_cons.2 ⟨subd9_5_517, List.forall_mem_cons.2 ⟨subd9_5_518, List.forall_mem_cons.2 ⟨subd9_5_519, List.forall_mem_cons.2 ⟨subd9_5_520, List.forall_mem_cons.2 ⟨subd9_5_521, List.forall_mem_cons.2 ⟨subd9_5_522, List.forall_mem_cons.2 ⟨subd9_5_523, List.forall_mem_cons.2 ⟨subd9_5_524, List.forall_mem_cons.2 ⟨subd9_5_525, List.forall_mem_cons.2 ⟨subd9_5_526, List.forall_mem_cons.2 ⟨subd9_5_527, List.forall_mem_cons.2 ⟨subd9_5_528, List.forall_mem_cons.2 ⟨subd9_5_529, List.forall_mem_cons.2 ⟨subd9_5_530, List.forall_mem_cons.2 ⟨subd9_5_531, List.forall_mem_cons.2 ⟨subd9_5_532, List.forall_mem_cons.2 ⟨subd9_5_533, List.forall_mem_cons.2 ⟨subd9_5_534, List.forall_mem_cons.2 ⟨subd9_5_535, List.forall_mem_cons.2 ⟨subd9_5_536, List.forall_mem_cons.2 ⟨subd9_5_537, List.forall_mem_cons.2 ⟨subd9_5_538, List.forall_mem_cons.2 ⟨subd9_5_539, List.forall_mem_cons.2 ⟨subd9_5_540, List.forall_mem_cons.2 ⟨subd9_5_541, List.forall_mem_cons.2 ⟨subd9_5_542, List.forall_mem_cons.2 ⟨subd9_5_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_5_544 : subd9_5 [2, 1, 6] = true := by decide +kernel
theorem subd9_5_545 : subd9_5 [2, 1, 7] = true := by decide +kernel
theorem subd9_5_546 : subd9_5 [2, 1, 8] = true := by decide +kernel
theorem subd9_5_547 : subd9_5 [2, 2, -9] = true := by decide +kernel
theorem subd9_5_548 : subd9_5 [2, 2, -8] = true := by decide +kernel
theorem subd9_5_549 : subd9_5 [2, 2, -7] = true := by decide +kernel
theorem subd9_5_550 : subd9_5 [2, 2, -6] = true := by decide +kernel
theorem subd9_5_551 : subd9_5 [2, 2, -5] = true := by decide +kernel
theorem subd9_5_552 : subd9_5 [2, 2, -4] = true := by decide +kernel
theorem subd9_5_553 : subd9_5 [2, 2, -3] = true := by decide +kernel
theorem subd9_5_554 : subd9_5 [2, 2, -2] = true := by decide +kernel
theorem subd9_5_555 : subd9_5 [2, 2, -1] = true := by decide +kernel
theorem subd9_5_556 : subd9_5 [2, 2, 0] = true := by decide +kernel
theorem subd9_5_557 : subd9_5 [2, 2, 1] = true := by decide +kernel
theorem subd9_5_558 : subd9_5 [2, 2, 2] = true := by decide +kernel
theorem subd9_5_559 : subd9_5 [2, 2, 3] = true := by decide +kernel
theorem subd9_5_560 : subd9_5 [2, 2, 4] = true := by decide +kernel
theorem subd9_5_561 : subd9_5 [2, 2, 5] = true := by decide +kernel
theorem subd9_5_562 : subd9_5 [2, 2, 6] = true := by decide +kernel
theorem subd9_5_563 : subd9_5 [2, 3] = true := by decide +kernel
theorem subd9_5_564 : subd9_5 [3, -3] = true := by decide +kernel
theorem subd9_5_565 : subd9_5 [3, -2] = true := by decide +kernel
theorem subd9_5_566 : subd9_5 [3, -1] = true := by decide +kernel
theorem subd9_5_567 : subd9_5 [3, 0, -8] = true := by decide +kernel
theorem subd9_5_568 : subd9_5 [3, 0, -7] = true := by decide +kernel
theorem subd9_5_569 : subd9_5 [3, 0, -6] = true := by decide +kernel
theorem subd9_5_570 : subd9_5 [3, 0, -5] = true := by decide +kernel
theorem subd9_5_571 : subd9_5 [3, 0, -4] = true := by decide +kernel
theorem subd9_5_572 : subd9_5 [3, 0, -3] = true := by decide +kernel
theorem subd9_5_573 : subd9_5 [3, 0, -2] = true := by decide +kernel
theorem subd9_5_574 : subd9_5 [3, 0, -1] = true := by decide +kernel
theorem subd9_5_575 : subd9_5 [3, 0, 0] = true := by decide +kernel
theorem sbd9_5_17 : ∀ q ∈ blkd9_5_17, subd9_5 q = true := by
  unfold blkd9_5_17
  exact List.forall_mem_cons.2 ⟨subd9_5_544, List.forall_mem_cons.2 ⟨subd9_5_545, List.forall_mem_cons.2 ⟨subd9_5_546, List.forall_mem_cons.2 ⟨subd9_5_547, List.forall_mem_cons.2 ⟨subd9_5_548, List.forall_mem_cons.2 ⟨subd9_5_549, List.forall_mem_cons.2 ⟨subd9_5_550, List.forall_mem_cons.2 ⟨subd9_5_551, List.forall_mem_cons.2 ⟨subd9_5_552, List.forall_mem_cons.2 ⟨subd9_5_553, List.forall_mem_cons.2 ⟨subd9_5_554, List.forall_mem_cons.2 ⟨subd9_5_555, List.forall_mem_cons.2 ⟨subd9_5_556, List.forall_mem_cons.2 ⟨subd9_5_557, List.forall_mem_cons.2 ⟨subd9_5_558, List.forall_mem_cons.2 ⟨subd9_5_559, List.forall_mem_cons.2 ⟨subd9_5_560, List.forall_mem_cons.2 ⟨subd9_5_561, List.forall_mem_cons.2 ⟨subd9_5_562, List.forall_mem_cons.2 ⟨subd9_5_563, List.forall_mem_cons.2 ⟨subd9_5_564, List.forall_mem_cons.2 ⟨subd9_5_565, List.forall_mem_cons.2 ⟨subd9_5_566, List.forall_mem_cons.2 ⟨subd9_5_567, List.forall_mem_cons.2 ⟨subd9_5_568, List.forall_mem_cons.2 ⟨subd9_5_569, List.forall_mem_cons.2 ⟨subd9_5_570, List.forall_mem_cons.2 ⟨subd9_5_571, List.forall_mem_cons.2 ⟨subd9_5_572, List.forall_mem_cons.2 ⟨subd9_5_573, List.forall_mem_cons.2 ⟨subd9_5_574, List.forall_mem_cons.2 ⟨subd9_5_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_5_576 : subd9_5 [3, 0, 1] = true := by decide +kernel
theorem subd9_5_577 : subd9_5 [3, 0, 2] = true := by decide +kernel
theorem subd9_5_578 : subd9_5 [3, 0, 3] = true := by decide +kernel
theorem subd9_5_579 : subd9_5 [3, 0, 4] = true := by decide +kernel
theorem subd9_5_580 : subd9_5 [3, 0, 5] = true := by decide +kernel
theorem subd9_5_581 : subd9_5 [3, 1] = true := by decide +kernel
theorem subd9_5_582 : subd9_5 [3, 2] = true := by decide +kernel
theorem sbd9_5_18 : ∀ q ∈ blkd9_5_18, subd9_5 q = true := by
  unfold blkd9_5_18
  exact List.forall_mem_cons.2 ⟨subd9_5_576, List.forall_mem_cons.2 ⟨subd9_5_577, List.forall_mem_cons.2 ⟨subd9_5_578, List.forall_mem_cons.2 ⟨subd9_5_579, List.forall_mem_cons.2 ⟨subd9_5_580, List.forall_mem_cons.2 ⟨subd9_5_581, List.forall_mem_cons.2 ⟨subd9_5_582, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_6 : ldCheck G d9_6.U d9_6.ms ldd9_6 = true := by decide +kernel
theorem pre_okd9_6 : subPre G cell9 d9_6 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C135
