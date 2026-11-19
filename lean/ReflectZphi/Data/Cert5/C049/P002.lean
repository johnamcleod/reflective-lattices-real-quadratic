import ReflectZphi.Data.Cert5.C049.Base

namespace ReflectZphi.Data.Cert5.C049
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub4_256 : sub4 [-1, 0, 0] = true := by decide +kernel
theorem sub4_257 : sub4 [-1, 0, 1] = true := by decide +kernel
theorem sub4_258 : sub4 [-1, 0, 2] = true := by decide +kernel
theorem sub4_259 : sub4 [-1, 0, 3] = true := by decide +kernel
theorem sub4_260 : sub4 [-1, 0, 4] = true := by decide +kernel
theorem sub4_261 : sub4 [-1, 0, 5] = true := by decide +kernel
theorem sub4_262 : sub4 [-1, 0, 6] = true := by decide +kernel
theorem sub4_263 : sub4 [-1, 0, 7] = true := by decide +kernel
theorem sub4_264 : sub4 [-1, 0, 8] = true := by decide +kernel
theorem sub4_265 : sub4 [-1, 1, -9] = true := by decide +kernel
theorem sub4_266 : sub4 [-1, 1, -8] = true := by decide +kernel
theorem sub4_267 : sub4 [-1, 1, -7] = true := by decide +kernel
theorem sub4_268 : sub4 [-1, 1, -6] = true := by decide +kernel
theorem sub4_269 : sub4 [-1, 1, -5] = true := by decide +kernel
theorem sub4_270 : sub4 [-1, 1, -4] = true := by decide +kernel
theorem sub4_271 : sub4 [-1, 1, -3] = true := by decide +kernel
theorem sub4_272 : sub4 [-1, 1, -2] = true := by decide +kernel
theorem sub4_273 : sub4 [-1, 1, -1] = true := by decide +kernel
theorem sub4_274 : sub4 [-1, 1, 0] = true := by decide +kernel
theorem sub4_275 : sub4 [-1, 1, 1] = true := by decide +kernel
theorem sub4_276 : sub4 [-1, 1, 2] = true := by decide +kernel
theorem sub4_277 : sub4 [-1, 1, 3] = true := by decide +kernel
theorem sub4_278 : sub4 [-1, 1, 4] = true := by decide +kernel
theorem sub4_279 : sub4 [-1, 1, 5] = true := by decide +kernel
theorem sub4_280 : sub4 [-1, 1, 6] = true := by decide +kernel
theorem sub4_281 : sub4 [-1, 1, 7] = true := by decide +kernel
theorem sub4_282 : sub4 [-1, 1, 8] = true := by decide +kernel
theorem sub4_283 : sub4 [-1, 2, -8] = true := by decide +kernel
theorem sub4_284 : sub4 [-1, 2, -7] = true := by decide +kernel
theorem sub4_285 : sub4 [-1, 2, -6] = true := by decide +kernel
theorem sub4_286 : sub4 [-1, 2, -5] = true := by decide +kernel
theorem sub4_287 : sub4 [-1, 2, -4] = true := by decide +kernel
theorem sb4_8 : ∀ q ∈ blk4_8, sub4 q = true := by
  unfold blk4_8
  exact List.forall_mem_cons.2 ⟨sub4_256, List.forall_mem_cons.2 ⟨sub4_257, List.forall_mem_cons.2 ⟨sub4_258, List.forall_mem_cons.2 ⟨sub4_259, List.forall_mem_cons.2 ⟨sub4_260, List.forall_mem_cons.2 ⟨sub4_261, List.forall_mem_cons.2 ⟨sub4_262, List.forall_mem_cons.2 ⟨sub4_263, List.forall_mem_cons.2 ⟨sub4_264, List.forall_mem_cons.2 ⟨sub4_265, List.forall_mem_cons.2 ⟨sub4_266, List.forall_mem_cons.2 ⟨sub4_267, List.forall_mem_cons.2 ⟨sub4_268, List.forall_mem_cons.2 ⟨sub4_269, List.forall_mem_cons.2 ⟨sub4_270, List.forall_mem_cons.2 ⟨sub4_271, List.forall_mem_cons.2 ⟨sub4_272, List.forall_mem_cons.2 ⟨sub4_273, List.forall_mem_cons.2 ⟨sub4_274, List.forall_mem_cons.2 ⟨sub4_275, List.forall_mem_cons.2 ⟨sub4_276, List.forall_mem_cons.2 ⟨sub4_277, List.forall_mem_cons.2 ⟨sub4_278, List.forall_mem_cons.2 ⟨sub4_279, List.forall_mem_cons.2 ⟨sub4_280, List.forall_mem_cons.2 ⟨sub4_281, List.forall_mem_cons.2 ⟨sub4_282, List.forall_mem_cons.2 ⟨sub4_283, List.forall_mem_cons.2 ⟨sub4_284, List.forall_mem_cons.2 ⟨sub4_285, List.forall_mem_cons.2 ⟨sub4_286, List.forall_mem_cons.2 ⟨sub4_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_288 : sub4 [-1, 2, -3] = true := by decide +kernel
theorem sub4_289 : sub4 [-1, 2, -2] = true := by decide +kernel
theorem sub4_290 : sub4 [-1, 2, -1] = true := by decide +kernel
theorem sub4_291 : sub4 [-1, 2, 0] = true := by decide +kernel
theorem sub4_292 : sub4 [-1, 2, 1] = true := by decide +kernel
theorem sub4_293 : sub4 [-1, 2, 2] = true := by decide +kernel
theorem sub4_294 : sub4 [-1, 2, 3] = true := by decide +kernel
theorem sub4_295 : sub4 [-1, 2, 4] = true := by decide +kernel
theorem sub4_296 : sub4 [-1, 2, 5] = true := by decide +kernel
theorem sub4_297 : sub4 [-1, 2, 6] = true := by decide +kernel
theorem sub4_298 : sub4 [-1, 2, 7] = true := by decide +kernel
theorem sub4_299 : sub4 [-1, 3] = true := by decide +kernel
theorem sub4_300 : sub4 [-1, 4] = true := by decide +kernel
theorem sub4_301 : sub4 [0, -6] = true := by decide +kernel
theorem sub4_302 : sub4 [0, -5] = true := by decide +kernel
theorem sub4_303 : sub4 [0, -4] = true := by decide +kernel
theorem sub4_304 : sub4 [0, -3, -8] = true := by decide +kernel
theorem sub4_305 : sub4 [0, -3, -7] = true := by decide +kernel
theorem sub4_306 : sub4 [0, -3, -6] = true := by decide +kernel
theorem sub4_307 : sub4 [0, -3, -5] = true := by decide +kernel
theorem sub4_308 : sub4 [0, -3, -4] = true := by decide +kernel
theorem sub4_309 : sub4 [0, -3, -3] = true := by decide +kernel
theorem sub4_310 : sub4 [0, -3, -2] = true := by decide +kernel
theorem sub4_311 : sub4 [0, -3, -1] = true := by decide +kernel
theorem sub4_312 : sub4 [0, -3, 0] = true := by decide +kernel
theorem sub4_313 : sub4 [0, -3, 1] = true := by decide +kernel
theorem sub4_314 : sub4 [0, -3, 2] = true := by decide +kernel
theorem sub4_315 : sub4 [0, -3, 3] = true := by decide +kernel
theorem sub4_316 : sub4 [0, -3, 4] = true := by decide +kernel
theorem sub4_317 : sub4 [0, -3, 5] = true := by decide +kernel
theorem sub4_318 : sub4 [0, -3, 6] = true := by decide +kernel
theorem sub4_319 : sub4 [0, -2, -9] = true := by decide +kernel
theorem sb4_9 : ∀ q ∈ blk4_9, sub4 q = true := by
  unfold blk4_9
  exact List.forall_mem_cons.2 ⟨sub4_288, List.forall_mem_cons.2 ⟨sub4_289, List.forall_mem_cons.2 ⟨sub4_290, List.forall_mem_cons.2 ⟨sub4_291, List.forall_mem_cons.2 ⟨sub4_292, List.forall_mem_cons.2 ⟨sub4_293, List.forall_mem_cons.2 ⟨sub4_294, List.forall_mem_cons.2 ⟨sub4_295, List.forall_mem_cons.2 ⟨sub4_296, List.forall_mem_cons.2 ⟨sub4_297, List.forall_mem_cons.2 ⟨sub4_298, List.forall_mem_cons.2 ⟨sub4_299, List.forall_mem_cons.2 ⟨sub4_300, List.forall_mem_cons.2 ⟨sub4_301, List.forall_mem_cons.2 ⟨sub4_302, List.forall_mem_cons.2 ⟨sub4_303, List.forall_mem_cons.2 ⟨sub4_304, List.forall_mem_cons.2 ⟨sub4_305, List.forall_mem_cons.2 ⟨sub4_306, List.forall_mem_cons.2 ⟨sub4_307, List.forall_mem_cons.2 ⟨sub4_308, List.forall_mem_cons.2 ⟨sub4_309, List.forall_mem_cons.2 ⟨sub4_310, List.forall_mem_cons.2 ⟨sub4_311, List.forall_mem_cons.2 ⟨sub4_312, List.forall_mem_cons.2 ⟨sub4_313, List.forall_mem_cons.2 ⟨sub4_314, List.forall_mem_cons.2 ⟨sub4_315, List.forall_mem_cons.2 ⟨sub4_316, List.forall_mem_cons.2 ⟨sub4_317, List.forall_mem_cons.2 ⟨sub4_318, List.forall_mem_cons.2 ⟨sub4_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_320 : sub4 [0, -2, -8] = true := by decide +kernel
theorem sub4_321 : sub4 [0, -2, -7] = true := by decide +kernel
theorem sub4_322 : sub4 [0, -2, -6] = true := by decide +kernel
theorem sub4_323 : sub4 [0, -2, -5] = true := by decide +kernel
theorem sub4_324 : sub4 [0, -2, -4] = true := by decide +kernel
theorem sub4_325 : sub4 [0, -2, -3] = true := by decide +kernel
theorem sub4_326 : sub4 [0, -2, -2] = true := by decide +kernel
theorem sub4_327 : sub4 [0, -2, -1] = true := by decide +kernel
theorem sub4_328 : sub4 [0, -2, 0] = true := by decide +kernel
theorem sub4_329 : sub4 [0, -2, 1] = true := by decide +kernel
theorem sub4_330 : sub4 [0, -2, 2] = true := by decide +kernel
theorem sub4_331 : sub4 [0, -2, 3] = true := by decide +kernel
theorem sub4_332 : sub4 [0, -2, 4] = true := by decide +kernel
theorem sub4_333 : sub4 [0, -2, 5] = true := by decide +kernel
theorem sub4_334 : sub4 [0, -2, 6] = true := by decide +kernel
theorem sub4_335 : sub4 [0, -2, 7] = true := by decide +kernel
theorem sub4_336 : sub4 [0, -1, -9] = true := by decide +kernel
theorem sub4_337 : sub4 [0, -1, -8] = true := by decide +kernel
theorem sub4_338 : sub4 [0, -1, -7] = true := by decide +kernel
theorem sub4_339 : sub4 [0, -1, -6] = true := by decide +kernel
theorem sub4_340 : sub4 [0, -1, -5] = true := by decide +kernel
theorem sub4_341 : sub4 [0, -1, -4] = true := by decide +kernel
theorem sub4_342 : sub4 [0, -1, -3] = true := by decide +kernel
theorem sub4_343 : sub4 [0, -1, -2] = true := by decide +kernel
theorem sub4_344 : sub4 [0, -1, -1] = true := by decide +kernel
theorem sub4_345 : sub4 [0, -1, 0] = true := by decide +kernel
theorem sub4_346 : sub4 [0, -1, 1] = true := by decide +kernel
theorem sub4_347 : sub4 [0, -1, 2] = true := by decide +kernel
theorem sub4_348 : sub4 [0, -1, 3] = true := by decide +kernel
theorem sub4_349 : sub4 [0, -1, 4] = true := by decide +kernel
theorem sub4_350 : sub4 [0, -1, 5] = true := by decide +kernel
theorem sub4_351 : sub4 [0, -1, 6] = true := by decide +kernel
theorem sb4_10 : ∀ q ∈ blk4_10, sub4 q = true := by
  unfold blk4_10
  exact List.forall_mem_cons.2 ⟨sub4_320, List.forall_mem_cons.2 ⟨sub4_321, List.forall_mem_cons.2 ⟨sub4_322, List.forall_mem_cons.2 ⟨sub4_323, List.forall_mem_cons.2 ⟨sub4_324, List.forall_mem_cons.2 ⟨sub4_325, List.forall_mem_cons.2 ⟨sub4_326, List.forall_mem_cons.2 ⟨sub4_327, List.forall_mem_cons.2 ⟨sub4_328, List.forall_mem_cons.2 ⟨sub4_329, List.forall_mem_cons.2 ⟨sub4_330, List.forall_mem_cons.2 ⟨sub4_331, List.forall_mem_cons.2 ⟨sub4_332, List.forall_mem_cons.2 ⟨sub4_333, List.forall_mem_cons.2 ⟨sub4_334, List.forall_mem_cons.2 ⟨sub4_335, List.forall_mem_cons.2 ⟨sub4_336, List.forall_mem_cons.2 ⟨sub4_337, List.forall_mem_cons.2 ⟨sub4_338, List.forall_mem_cons.2 ⟨sub4_339, List.forall_mem_cons.2 ⟨sub4_340, List.forall_mem_cons.2 ⟨sub4_341, List.forall_mem_cons.2 ⟨sub4_342, List.forall_mem_cons.2 ⟨sub4_343, List.forall_mem_cons.2 ⟨sub4_344, List.forall_mem_cons.2 ⟨sub4_345, List.forall_mem_cons.2 ⟨sub4_346, List.forall_mem_cons.2 ⟨sub4_347, List.forall_mem_cons.2 ⟨sub4_348, List.forall_mem_cons.2 ⟨sub4_349, List.forall_mem_cons.2 ⟨sub4_350, List.forall_mem_cons.2 ⟨sub4_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_352 : sub4 [0, -1, 7] = true := by decide +kernel
theorem sub4_353 : sub4 [0, -1, 8] = true := by decide +kernel
theorem sub4_354 : sub4 [0, 0, -9] = true := by decide +kernel
theorem sub4_355 : sub4 [0, 0, -8] = true := by decide +kernel
theorem sub4_356 : sub4 [0, 0, -7] = true := by decide +kernel
theorem sub4_357 : sub4 [0, 0, -6] = true := by decide +kernel
theorem sub4_358 : sub4 [0, 0, -5] = true := by decide +kernel
theorem sub4_359 : sub4 [0, 0, -4] = true := by decide +kernel
theorem sub4_360 : sub4 [0, 0, -3] = true := by decide +kernel
theorem sub4_361 : sub4 [0, 0, -2] = true := by decide +kernel
theorem sub4_362 : sub4 [0, 0, -1] = true := by decide +kernel
theorem sub4_363 : sub4 [0, 0, 0] = true := by decide +kernel
theorem sub4_364 : sub4 [0, 0, 1] = true := by decide +kernel
theorem sub4_365 : sub4 [0, 0, 2] = true := by decide +kernel
theorem sub4_366 : sub4 [0, 0, 3] = true := by decide +kernel
theorem sub4_367 : sub4 [0, 0, 4] = true := by decide +kernel
theorem sub4_368 : sub4 [0, 0, 5] = true := by decide +kernel
theorem sub4_369 : sub4 [0, 0, 6] = true := by decide +kernel
theorem sub4_370 : sub4 [0, 0, 7] = true := by decide +kernel
theorem sub4_371 : sub4 [0, 0, 8] = true := by decide +kernel
theorem sub4_372 : sub4 [0, 1, -9] = true := by decide +kernel
theorem sub4_373 : sub4 [0, 1, -8] = true := by decide +kernel
theorem sub4_374 : sub4 [0, 1, -7] = true := by decide +kernel
theorem sub4_375 : sub4 [0, 1, -6] = true := by decide +kernel
theorem sub4_376 : sub4 [0, 1, -5] = true := by decide +kernel
theorem sub4_377 : sub4 [0, 1, -4] = true := by decide +kernel
theorem sub4_378 : sub4 [0, 1, -3] = true := by decide +kernel
theorem sub4_379 : sub4 [0, 1, -2] = true := by decide +kernel
theorem sub4_380 : sub4 [0, 1, -1] = true := by decide +kernel
theorem sub4_381 : sub4 [0, 1, 0] = true := by decide +kernel
theorem sub4_382 : sub4 [0, 1, 1] = true := by decide +kernel
theorem sub4_383 : sub4 [0, 1, 2] = true := by decide +kernel
theorem sb4_11 : ∀ q ∈ blk4_11, sub4 q = true := by
  unfold blk4_11
  exact List.forall_mem_cons.2 ⟨sub4_352, List.forall_mem_cons.2 ⟨sub4_353, List.forall_mem_cons.2 ⟨sub4_354, List.forall_mem_cons.2 ⟨sub4_355, List.forall_mem_cons.2 ⟨sub4_356, List.forall_mem_cons.2 ⟨sub4_357, List.forall_mem_cons.2 ⟨sub4_358, List.forall_mem_cons.2 ⟨sub4_359, List.forall_mem_cons.2 ⟨sub4_360, List.forall_mem_cons.2 ⟨sub4_361, List.forall_mem_cons.2 ⟨sub4_362, List.forall_mem_cons.2 ⟨sub4_363, List.forall_mem_cons.2 ⟨sub4_364, List.forall_mem_cons.2 ⟨sub4_365, List.forall_mem_cons.2 ⟨sub4_366, List.forall_mem_cons.2 ⟨sub4_367, List.forall_mem_cons.2 ⟨sub4_368, List.forall_mem_cons.2 ⟨sub4_369, List.forall_mem_cons.2 ⟨sub4_370, List.forall_mem_cons.2 ⟨sub4_371, List.forall_mem_cons.2 ⟨sub4_372, List.forall_mem_cons.2 ⟨sub4_373, List.forall_mem_cons.2 ⟨sub4_374, List.forall_mem_cons.2 ⟨sub4_375, List.forall_mem_cons.2 ⟨sub4_376, List.forall_mem_cons.2 ⟨sub4_377, List.forall_mem_cons.2 ⟨sub4_378, List.forall_mem_cons.2 ⟨sub4_379, List.forall_mem_cons.2 ⟨sub4_380, List.forall_mem_cons.2 ⟨sub4_381, List.forall_mem_cons.2 ⟨sub4_382, List.forall_mem_cons.2 ⟨sub4_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_384 : sub4 [0, 1, 3] = true := by decide +kernel
theorem sub4_385 : sub4 [0, 1, 4] = true := by decide +kernel
theorem sub4_386 : sub4 [0, 1, 5] = true := by decide +kernel
theorem sub4_387 : sub4 [0, 1, 6] = true := by decide +kernel
theorem sub4_388 : sub4 [0, 1, 7] = true := by decide +kernel
theorem sub4_389 : sub4 [0, 1, 8] = true := by decide +kernel
theorem sub4_390 : sub4 [0, 2, -8] = true := by decide +kernel
theorem sub4_391 : sub4 [0, 2, -7] = true := by decide +kernel
theorem sub4_392 : sub4 [0, 2, -6] = true := by decide +kernel
theorem sub4_393 : sub4 [0, 2, -5] = true := by decide +kernel
theorem sub4_394 : sub4 [0, 2, -4] = true := by decide +kernel
theorem sub4_395 : sub4 [0, 2, -3] = true := by decide +kernel
theorem sub4_396 : sub4 [0, 2, -2] = true := by decide +kernel
theorem sub4_397 : sub4 [0, 2, -1] = true := by decide +kernel
theorem sub4_398 : sub4 [0, 2, 0] = true := by decide +kernel
theorem sub4_399 : sub4 [0, 2, 1] = true := by decide +kernel
theorem sub4_400 : sub4 [0, 2, 2] = true := by decide +kernel
theorem sub4_401 : sub4 [0, 2, 3] = true := by decide +kernel
theorem sub4_402 : sub4 [0, 2, 4] = true := by decide +kernel
theorem sub4_403 : sub4 [0, 2, 5] = true := by decide +kernel
theorem sub4_404 : sub4 [0, 2, 6] = true := by decide +kernel
theorem sub4_405 : sub4 [0, 2, 7] = true := by decide +kernel
theorem sub4_406 : sub4 [0, 2, 8] = true := by decide +kernel
theorem sub4_407 : sub4 [0, 3, -7] = true := by decide +kernel
theorem sub4_408 : sub4 [0, 3, -6] = true := by decide +kernel
theorem sub4_409 : sub4 [0, 3, -5] = true := by decide +kernel
theorem sub4_410 : sub4 [0, 3, -4] = true := by decide +kernel
theorem sub4_411 : sub4 [0, 3, -3] = true := by decide +kernel
theorem sub4_412 : sub4 [0, 3, -2] = true := by decide +kernel
theorem sub4_413 : sub4 [0, 3, -1] = true := by decide +kernel
theorem sub4_414 : sub4 [0, 3, 0] = true := by decide +kernel
theorem sub4_415 : sub4 [0, 3, 1] = true := by decide +kernel
theorem sb4_12 : ∀ q ∈ blk4_12, sub4 q = true := by
  unfold blk4_12
  exact List.forall_mem_cons.2 ⟨sub4_384, List.forall_mem_cons.2 ⟨sub4_385, List.forall_mem_cons.2 ⟨sub4_386, List.forall_mem_cons.2 ⟨sub4_387, List.forall_mem_cons.2 ⟨sub4_388, List.forall_mem_cons.2 ⟨sub4_389, List.forall_mem_cons.2 ⟨sub4_390, List.forall_mem_cons.2 ⟨sub4_391, List.forall_mem_cons.2 ⟨sub4_392, List.forall_mem_cons.2 ⟨sub4_393, List.forall_mem_cons.2 ⟨sub4_394, List.forall_mem_cons.2 ⟨sub4_395, List.forall_mem_cons.2 ⟨sub4_396, List.forall_mem_cons.2 ⟨sub4_397, List.forall_mem_cons.2 ⟨sub4_398, List.forall_mem_cons.2 ⟨sub4_399, List.forall_mem_cons.2 ⟨sub4_400, List.forall_mem_cons.2 ⟨sub4_401, List.forall_mem_cons.2 ⟨sub4_402, List.forall_mem_cons.2 ⟨sub4_403, List.forall_mem_cons.2 ⟨sub4_404, List.forall_mem_cons.2 ⟨sub4_405, List.forall_mem_cons.2 ⟨sub4_406, List.forall_mem_cons.2 ⟨sub4_407, List.forall_mem_cons.2 ⟨sub4_408, List.forall_mem_cons.2 ⟨sub4_409, List.forall_mem_cons.2 ⟨sub4_410, List.forall_mem_cons.2 ⟨sub4_411, List.forall_mem_cons.2 ⟨sub4_412, List.forall_mem_cons.2 ⟨sub4_413, List.forall_mem_cons.2 ⟨sub4_414, List.forall_mem_cons.2 ⟨sub4_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_416 : sub4 [0, 3, 2] = true := by decide +kernel
theorem sub4_417 : sub4 [0, 3, 3] = true := by decide +kernel
theorem sub4_418 : sub4 [0, 3, 4] = true := by decide +kernel
theorem sub4_419 : sub4 [0, 3, 5] = true := by decide +kernel
theorem sub4_420 : sub4 [0, 3, 6] = true := by decide +kernel
theorem sub4_421 : sub4 [0, 3, 7] = true := by decide +kernel
theorem sub4_422 : sub4 [0, 4] = true := by decide +kernel
theorem sub4_423 : sub4 [0, 5] = true := by decide +kernel
theorem sub4_424 : sub4 [1, -5] = true := by decide +kernel
theorem sub4_425 : sub4 [1, -4] = true := by decide +kernel
theorem sub4_426 : sub4 [1, -3] = true := by decide +kernel
theorem sub4_427 : sub4 [1, -2, -8] = true := by decide +kernel
theorem sub4_428 : sub4 [1, -2, -7] = true := by decide +kernel
theorem sub4_429 : sub4 [1, -2, -6] = true := by decide +kernel
theorem sub4_430 : sub4 [1, -2, -5] = true := by decide +kernel
theorem sub4_431 : sub4 [1, -2, -4] = true := by decide +kernel
theorem sub4_432 : sub4 [1, -2, -3] = true := by decide +kernel
theorem sub4_433 : sub4 [1, -2, -2] = true := by decide +kernel
theorem sub4_434 : sub4 [1, -2, -1] = true := by decide +kernel
theorem sub4_435 : sub4 [1, -2, 0] = true := by decide +kernel
theorem sub4_436 : sub4 [1, -2, 1] = true := by decide +kernel
theorem sub4_437 : sub4 [1, -2, 2] = true := by decide +kernel
theorem sub4_438 : sub4 [1, -2, 3] = true := by decide +kernel
theorem sub4_439 : sub4 [1, -2, 4] = true := by decide +kernel
theorem sub4_440 : sub4 [1, -2, 5] = true := by decide +kernel
theorem sub4_441 : sub4 [1, -2, 6] = true := by decide +kernel
theorem sub4_442 : sub4 [1, -2, 7] = true := by decide +kernel
theorem sub4_443 : sub4 [1, -1, -9] = true := by decide +kernel
theorem sub4_444 : sub4 [1, -1, -8] = true := by decide +kernel
theorem sub4_445 : sub4 [1, -1, -7] = true := by decide +kernel
theorem sub4_446 : sub4 [1, -1, -6] = true := by decide +kernel
theorem sub4_447 : sub4 [1, -1, -5] = true := by decide +kernel
theorem sb4_13 : ∀ q ∈ blk4_13, sub4 q = true := by
  unfold blk4_13
  exact List.forall_mem_cons.2 ⟨sub4_416, List.forall_mem_cons.2 ⟨sub4_417, List.forall_mem_cons.2 ⟨sub4_418, List.forall_mem_cons.2 ⟨sub4_419, List.forall_mem_cons.2 ⟨sub4_420, List.forall_mem_cons.2 ⟨sub4_421, List.forall_mem_cons.2 ⟨sub4_422, List.forall_mem_cons.2 ⟨sub4_423, List.forall_mem_cons.2 ⟨sub4_424, List.forall_mem_cons.2 ⟨sub4_425, List.forall_mem_cons.2 ⟨sub4_426, List.forall_mem_cons.2 ⟨sub4_427, List.forall_mem_cons.2 ⟨sub4_428, List.forall_mem_cons.2 ⟨sub4_429, List.forall_mem_cons.2 ⟨sub4_430, List.forall_mem_cons.2 ⟨sub4_431, List.forall_mem_cons.2 ⟨sub4_432, List.forall_mem_cons.2 ⟨sub4_433, List.forall_mem_cons.2 ⟨sub4_434, List.forall_mem_cons.2 ⟨sub4_435, List.forall_mem_cons.2 ⟨sub4_436, List.forall_mem_cons.2 ⟨sub4_437, List.forall_mem_cons.2 ⟨sub4_438, List.forall_mem_cons.2 ⟨sub4_439, List.forall_mem_cons.2 ⟨sub4_440, List.forall_mem_cons.2 ⟨sub4_441, List.forall_mem_cons.2 ⟨sub4_442, List.forall_mem_cons.2 ⟨sub4_443, List.forall_mem_cons.2 ⟨sub4_444, List.forall_mem_cons.2 ⟨sub4_445, List.forall_mem_cons.2 ⟨sub4_446, List.forall_mem_cons.2 ⟨sub4_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_448 : sub4 [1, -1, -4] = true := by decide +kernel
theorem sub4_449 : sub4 [1, -1, -3] = true := by decide +kernel
theorem sub4_450 : sub4 [1, -1, -2] = true := by decide +kernel
theorem sub4_451 : sub4 [1, -1, -1] = true := by decide +kernel
theorem sub4_452 : sub4 [1, -1, 0] = true := by decide +kernel
theorem sub4_453 : sub4 [1, -1, 1] = true := by decide +kernel
theorem sub4_454 : sub4 [1, -1, 2] = true := by decide +kernel
theorem sub4_455 : sub4 [1, -1, 3] = true := by decide +kernel
theorem sub4_456 : sub4 [1, -1, 4] = true := by decide +kernel
theorem sub4_457 : sub4 [1, -1, 5] = true := by decide +kernel
theorem sub4_458 : sub4 [1, -1, 6] = true := by decide +kernel
theorem sub4_459 : sub4 [1, -1, 7] = true := by decide +kernel
theorem sub4_460 : sub4 [1, -1, 8] = true := by decide +kernel
theorem sub4_461 : sub4 [1, 0, -9] = true := by decide +kernel
theorem sub4_462 : sub4 [1, 0, -8] = true := by decide +kernel
theorem sub4_463 : sub4 [1, 0, -7] = true := by decide +kernel
theorem sub4_464 : sub4 [1, 0, -6] = true := by decide +kernel
theorem sub4_465 : sub4 [1, 0, -5] = true := by decide +kernel
theorem sub4_466 : sub4 [1, 0, -4] = true := by decide +kernel
theorem sub4_467 : sub4 [1, 0, -3] = true := by decide +kernel
theorem sub4_468 : sub4 [1, 0, -2] = true := by decide +kernel
theorem sub4_469 : sub4 [1, 0, -1] = true := by decide +kernel
theorem sub4_470 : sub4 [1, 0, 0] = true := by decide +kernel
theorem sub4_471 : sub4 [1, 0, 1] = true := by decide +kernel
theorem sub4_472 : sub4 [1, 0, 2] = true := by decide +kernel
theorem sub4_473 : sub4 [1, 0, 3] = true := by decide +kernel
theorem sub4_474 : sub4 [1, 0, 4] = true := by decide +kernel
theorem sub4_475 : sub4 [1, 0, 5] = true := by decide +kernel
theorem sub4_476 : sub4 [1, 0, 6] = true := by decide +kernel
theorem sub4_477 : sub4 [1, 0, 7] = true := by decide +kernel
theorem sub4_478 : sub4 [1, 0, 8] = true := by decide +kernel
theorem sub4_479 : sub4 [1, 1, -8] = true := by decide +kernel
theorem sb4_14 : ∀ q ∈ blk4_14, sub4 q = true := by
  unfold blk4_14
  exact List.forall_mem_cons.2 ⟨sub4_448, List.forall_mem_cons.2 ⟨sub4_449, List.forall_mem_cons.2 ⟨sub4_450, List.forall_mem_cons.2 ⟨sub4_451, List.forall_mem_cons.2 ⟨sub4_452, List.forall_mem_cons.2 ⟨sub4_453, List.forall_mem_cons.2 ⟨sub4_454, List.forall_mem_cons.2 ⟨sub4_455, List.forall_mem_cons.2 ⟨sub4_456, List.forall_mem_cons.2 ⟨sub4_457, List.forall_mem_cons.2 ⟨sub4_458, List.forall_mem_cons.2 ⟨sub4_459, List.forall_mem_cons.2 ⟨sub4_460, List.forall_mem_cons.2 ⟨sub4_461, List.forall_mem_cons.2 ⟨sub4_462, List.forall_mem_cons.2 ⟨sub4_463, List.forall_mem_cons.2 ⟨sub4_464, List.forall_mem_cons.2 ⟨sub4_465, List.forall_mem_cons.2 ⟨sub4_466, List.forall_mem_cons.2 ⟨sub4_467, List.forall_mem_cons.2 ⟨sub4_468, List.forall_mem_cons.2 ⟨sub4_469, List.forall_mem_cons.2 ⟨sub4_470, List.forall_mem_cons.2 ⟨sub4_471, List.forall_mem_cons.2 ⟨sub4_472, List.forall_mem_cons.2 ⟨sub4_473, List.forall_mem_cons.2 ⟨sub4_474, List.forall_mem_cons.2 ⟨sub4_475, List.forall_mem_cons.2 ⟨sub4_476, List.forall_mem_cons.2 ⟨sub4_477, List.forall_mem_cons.2 ⟨sub4_478, List.forall_mem_cons.2 ⟨sub4_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_480 : sub4 [1, 1, -7] = true := by decide +kernel
theorem sub4_481 : sub4 [1, 1, -6] = true := by decide +kernel
theorem sub4_482 : sub4 [1, 1, -5] = true := by decide +kernel
theorem sub4_483 : sub4 [1, 1, -4] = true := by decide +kernel
theorem sub4_484 : sub4 [1, 1, -3] = true := by decide +kernel
theorem sub4_485 : sub4 [1, 1, -2] = true := by decide +kernel
theorem sub4_486 : sub4 [1, 1, -1] = true := by decide +kernel
theorem sub4_487 : sub4 [1, 1, 0] = true := by decide +kernel
theorem sub4_488 : sub4 [1, 1, 1] = true := by decide +kernel
theorem sub4_489 : sub4 [1, 1, 2] = true := by decide +kernel
theorem sub4_490 : sub4 [1, 1, 3] = true := by decide +kernel
theorem sub4_491 : sub4 [1, 1, 4] = true := by decide +kernel
theorem sub4_492 : sub4 [1, 1, 5] = true := by decide +kernel
theorem sub4_493 : sub4 [1, 1, 6] = true := by decide +kernel
theorem sub4_494 : sub4 [1, 1, 7] = true := by decide +kernel
theorem sub4_495 : sub4 [1, 1, 8] = true := by decide +kernel
theorem sub4_496 : sub4 [1, 2, -8] = true := by decide +kernel
theorem sub4_497 : sub4 [1, 2, -7] = true := by decide +kernel
theorem sub4_498 : sub4 [1, 2, -6] = true := by decide +kernel
theorem sub4_499 : sub4 [1, 2, -5] = true := by decide +kernel
theorem sub4_500 : sub4 [1, 2, -4] = true := by decide +kernel
theorem sub4_501 : sub4 [1, 2, -3] = true := by decide +kernel
theorem sub4_502 : sub4 [1, 2, -2] = true := by decide +kernel
theorem sub4_503 : sub4 [1, 2, -1] = true := by decide +kernel
theorem sub4_504 : sub4 [1, 2, 0] = true := by decide +kernel
theorem sub4_505 : sub4 [1, 2, 1] = true := by decide +kernel
theorem sub4_506 : sub4 [1, 2, 2] = true := by decide +kernel
theorem sub4_507 : sub4 [1, 2, 3] = true := by decide +kernel
theorem sub4_508 : sub4 [1, 2, 4] = true := by decide +kernel
theorem sub4_509 : sub4 [1, 2, 5] = true := by decide +kernel
theorem sub4_510 : sub4 [1, 2, 6] = true := by decide +kernel
theorem sub4_511 : sub4 [1, 2, 7] = true := by decide +kernel
theorem sb4_15 : ∀ q ∈ blk4_15, sub4 q = true := by
  unfold blk4_15
  exact List.forall_mem_cons.2 ⟨sub4_480, List.forall_mem_cons.2 ⟨sub4_481, List.forall_mem_cons.2 ⟨sub4_482, List.forall_mem_cons.2 ⟨sub4_483, List.forall_mem_cons.2 ⟨sub4_484, List.forall_mem_cons.2 ⟨sub4_485, List.forall_mem_cons.2 ⟨sub4_486, List.forall_mem_cons.2 ⟨sub4_487, List.forall_mem_cons.2 ⟨sub4_488, List.forall_mem_cons.2 ⟨sub4_489, List.forall_mem_cons.2 ⟨sub4_490, List.forall_mem_cons.2 ⟨sub4_491, List.forall_mem_cons.2 ⟨sub4_492, List.forall_mem_cons.2 ⟨sub4_493, List.forall_mem_cons.2 ⟨sub4_494, List.forall_mem_cons.2 ⟨sub4_495, List.forall_mem_cons.2 ⟨sub4_496, List.forall_mem_cons.2 ⟨sub4_497, List.forall_mem_cons.2 ⟨sub4_498, List.forall_mem_cons.2 ⟨sub4_499, List.forall_mem_cons.2 ⟨sub4_500, List.forall_mem_cons.2 ⟨sub4_501, List.forall_mem_cons.2 ⟨sub4_502, List.forall_mem_cons.2 ⟨sub4_503, List.forall_mem_cons.2 ⟨sub4_504, List.forall_mem_cons.2 ⟨sub4_505, List.forall_mem_cons.2 ⟨sub4_506, List.forall_mem_cons.2 ⟨sub4_507, List.forall_mem_cons.2 ⟨sub4_508, List.forall_mem_cons.2 ⟨sub4_509, List.forall_mem_cons.2 ⟨sub4_510, List.forall_mem_cons.2 ⟨sub4_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_512 : sub4 [1, 2, 8] = true := by decide +kernel
theorem sub4_513 : sub4 [1, 3, -6] = true := by decide +kernel
theorem sub4_514 : sub4 [1, 3, -5] = true := by decide +kernel
theorem sub4_515 : sub4 [1, 3, -4] = true := by decide +kernel
theorem sub4_516 : sub4 [1, 3, -3] = true := by decide +kernel
theorem sub4_517 : sub4 [1, 3, -2] = true := by decide +kernel
theorem sub4_518 : sub4 [1, 3, -1] = true := by decide +kernel
theorem sub4_519 : sub4 [1, 3, 0] = true := by decide +kernel
theorem sub4_520 : sub4 [1, 3, 1] = true := by decide +kernel
theorem sub4_521 : sub4 [1, 3, 2] = true := by decide +kernel
theorem sub4_522 : sub4 [1, 3, 3] = true := by decide +kernel
theorem sub4_523 : sub4 [1, 3, 4] = true := by decide +kernel
theorem sub4_524 : sub4 [1, 3, 5] = true := by decide +kernel
theorem sub4_525 : sub4 [1, 3, 6] = true := by decide +kernel
theorem sub4_526 : sub4 [1, 3, 7] = true := by decide +kernel
theorem sub4_527 : sub4 [1, 3, 8] = true := by decide +kernel
theorem sub4_528 : sub4 [1, 4] = true := by decide +kernel
theorem sub4_529 : sub4 [1, 5] = true := by decide +kernel
theorem sub4_530 : sub4 [2, -5] = true := by decide +kernel
theorem sub4_531 : sub4 [2, -4] = true := by decide +kernel
theorem sub4_532 : sub4 [2, -3] = true := by decide +kernel
theorem sub4_533 : sub4 [2, -2, -7] = true := by decide +kernel
theorem sub4_534 : sub4 [2, -2, -6] = true := by decide +kernel
theorem sub4_535 : sub4 [2, -2, -5] = true := by decide +kernel
theorem sub4_536 : sub4 [2, -2, -4] = true := by decide +kernel
theorem sub4_537 : sub4 [2, -2, -3] = true := by decide +kernel
theorem sub4_538 : sub4 [2, -2, -2] = true := by decide +kernel
theorem sub4_539 : sub4 [2, -2, -1] = true := by decide +kernel
theorem sub4_540 : sub4 [2, -2, 0] = true := by decide +kernel
theorem sub4_541 : sub4 [2, -2, 1] = true := by decide +kernel
theorem sub4_542 : sub4 [2, -2, 2] = true := by decide +kernel
theorem sub4_543 : sub4 [2, -2, 3] = true := by decide +kernel
theorem sb4_16 : ∀ q ∈ blk4_16, sub4 q = true := by
  unfold blk4_16
  exact List.forall_mem_cons.2 ⟨sub4_512, List.forall_mem_cons.2 ⟨sub4_513, List.forall_mem_cons.2 ⟨sub4_514, List.forall_mem_cons.2 ⟨sub4_515, List.forall_mem_cons.2 ⟨sub4_516, List.forall_mem_cons.2 ⟨sub4_517, List.forall_mem_cons.2 ⟨sub4_518, List.forall_mem_cons.2 ⟨sub4_519, List.forall_mem_cons.2 ⟨sub4_520, List.forall_mem_cons.2 ⟨sub4_521, List.forall_mem_cons.2 ⟨sub4_522, List.forall_mem_cons.2 ⟨sub4_523, List.forall_mem_cons.2 ⟨sub4_524, List.forall_mem_cons.2 ⟨sub4_525, List.forall_mem_cons.2 ⟨sub4_526, List.forall_mem_cons.2 ⟨sub4_527, List.forall_mem_cons.2 ⟨sub4_528, List.forall_mem_cons.2 ⟨sub4_529, List.forall_mem_cons.2 ⟨sub4_530, List.forall_mem_cons.2 ⟨sub4_531, List.forall_mem_cons.2 ⟨sub4_532, List.forall_mem_cons.2 ⟨sub4_533, List.forall_mem_cons.2 ⟨sub4_534, List.forall_mem_cons.2 ⟨sub4_535, List.forall_mem_cons.2 ⟨sub4_536, List.forall_mem_cons.2 ⟨sub4_537, List.forall_mem_cons.2 ⟨sub4_538, List.forall_mem_cons.2 ⟨sub4_539, List.forall_mem_cons.2 ⟨sub4_540, List.forall_mem_cons.2 ⟨sub4_541, List.forall_mem_cons.2 ⟨sub4_542, List.forall_mem_cons.2 ⟨sub4_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_544 : sub4 [2, -2, 4] = true := by decide +kernel
theorem sub4_545 : sub4 [2, -2, 5] = true := by decide +kernel
theorem sub4_546 : sub4 [2, -2, 6] = true := by decide +kernel
theorem sub4_547 : sub4 [2, -1, -8] = true := by decide +kernel
theorem sub4_548 : sub4 [2, -1, -7] = true := by decide +kernel
theorem sub4_549 : sub4 [2, -1, -6] = true := by decide +kernel
theorem sub4_550 : sub4 [2, -1, -5] = true := by decide +kernel
theorem sub4_551 : sub4 [2, -1, -4] = true := by decide +kernel
theorem sub4_552 : sub4 [2, -1, -3] = true := by decide +kernel
theorem sub4_553 : sub4 [2, -1, -2] = true := by decide +kernel
theorem sub4_554 : sub4 [2, -1, -1] = true := by decide +kernel
theorem sub4_555 : sub4 [2, -1, 0] = true := by decide +kernel
theorem sub4_556 : sub4 [2, -1, 1] = true := by decide +kernel
theorem sub4_557 : sub4 [2, -1, 2] = true := by decide +kernel
theorem sub4_558 : sub4 [2, -1, 3] = true := by decide +kernel
theorem sub4_559 : sub4 [2, -1, 4] = true := by decide +kernel
theorem sub4_560 : sub4 [2, -1, 5] = true := by decide +kernel
theorem sub4_561 : sub4 [2, -1, 6] = true := by decide +kernel
theorem sub4_562 : sub4 [2, -1, 7] = true := by decide +kernel
theorem sub4_563 : sub4 [2, 0, -8] = true := by decide +kernel
theorem sub4_564 : sub4 [2, 0, -7] = true := by decide +kernel
theorem sub4_565 : sub4 [2, 0, -6] = true := by decide +kernel
theorem sub4_566 : sub4 [2, 0, -5] = true := by decide +kernel
theorem sub4_567 : sub4 [2, 0, -4] = true := by decide +kernel
theorem sub4_568 : sub4 [2, 0, -3] = true := by decide +kernel
theorem sub4_569 : sub4 [2, 0, -2] = true := by decide +kernel
theorem sub4_570 : sub4 [2, 0, -1] = true := by decide +kernel
theorem sub4_571 : sub4 [2, 0, 0] = true := by decide +kernel
theorem sub4_572 : sub4 [2, 0, 1] = true := by decide +kernel
theorem sub4_573 : sub4 [2, 0, 2] = true := by decide +kernel
theorem sub4_574 : sub4 [2, 0, 3] = true := by decide +kernel
theorem sub4_575 : sub4 [2, 0, 4] = true := by decide +kernel
theorem sb4_17 : ∀ q ∈ blk4_17, sub4 q = true := by
  unfold blk4_17
  exact List.forall_mem_cons.2 ⟨sub4_544, List.forall_mem_cons.2 ⟨sub4_545, List.forall_mem_cons.2 ⟨sub4_546, List.forall_mem_cons.2 ⟨sub4_547, List.forall_mem_cons.2 ⟨sub4_548, List.forall_mem_cons.2 ⟨sub4_549, List.forall_mem_cons.2 ⟨sub4_550, List.forall_mem_cons.2 ⟨sub4_551, List.forall_mem_cons.2 ⟨sub4_552, List.forall_mem_cons.2 ⟨sub4_553, List.forall_mem_cons.2 ⟨sub4_554, List.forall_mem_cons.2 ⟨sub4_555, List.forall_mem_cons.2 ⟨sub4_556, List.forall_mem_cons.2 ⟨sub4_557, List.forall_mem_cons.2 ⟨sub4_558, List.forall_mem_cons.2 ⟨sub4_559, List.forall_mem_cons.2 ⟨sub4_560, List.forall_mem_cons.2 ⟨sub4_561, List.forall_mem_cons.2 ⟨sub4_562, List.forall_mem_cons.2 ⟨sub4_563, List.forall_mem_cons.2 ⟨sub4_564, List.forall_mem_cons.2 ⟨sub4_565, List.forall_mem_cons.2 ⟨sub4_566, List.forall_mem_cons.2 ⟨sub4_567, List.forall_mem_cons.2 ⟨sub4_568, List.forall_mem_cons.2 ⟨sub4_569, List.forall_mem_cons.2 ⟨sub4_570, List.forall_mem_cons.2 ⟨sub4_571, List.forall_mem_cons.2 ⟨sub4_572, List.forall_mem_cons.2 ⟨sub4_573, List.forall_mem_cons.2 ⟨sub4_574, List.forall_mem_cons.2 ⟨sub4_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_576 : sub4 [2, 0, 5] = true := by decide +kernel
theorem sub4_577 : sub4 [2, 0, 6] = true := by decide +kernel
theorem sub4_578 : sub4 [2, 0, 7] = true := by decide +kernel
theorem sub4_579 : sub4 [2, 0, 8] = true := by decide +kernel
theorem sub4_580 : sub4 [2, 1, -8] = true := by decide +kernel
theorem sub4_581 : sub4 [2, 1, -7] = true := by decide +kernel
theorem sub4_582 : sub4 [2, 1, -6] = true := by decide +kernel
theorem sub4_583 : sub4 [2, 1, -5] = true := by decide +kernel
theorem sub4_584 : sub4 [2, 1, -4] = true := by decide +kernel
theorem sub4_585 : sub4 [2, 1, -3] = true := by decide +kernel
theorem sub4_586 : sub4 [2, 1, -2] = true := by decide +kernel
theorem sub4_587 : sub4 [2, 1, -1] = true := by decide +kernel
theorem sub4_588 : sub4 [2, 1, 0] = true := by decide +kernel
theorem sub4_589 : sub4 [2, 1, 1] = true := by decide +kernel
theorem sub4_590 : sub4 [2, 1, 2] = true := by decide +kernel
theorem sub4_591 : sub4 [2, 1, 3] = true := by decide +kernel
theorem sub4_592 : sub4 [2, 1, 4] = true := by decide +kernel
theorem sub4_593 : sub4 [2, 1, 5] = true := by decide +kernel
theorem sub4_594 : sub4 [2, 1, 6] = true := by decide +kernel
theorem sub4_595 : sub4 [2, 1, 7] = true := by decide +kernel
theorem sub4_596 : sub4 [2, 1, 8] = true := by decide +kernel
theorem sub4_597 : sub4 [2, 2, -7] = true := by decide +kernel
theorem sub4_598 : sub4 [2, 2, -6] = true := by decide +kernel
theorem sub4_599 : sub4 [2, 2, -5] = true := by decide +kernel
theorem sub4_600 : sub4 [2, 2, -4] = true := by decide +kernel
theorem sub4_601 : sub4 [2, 2, -3] = true := by decide +kernel
theorem sub4_602 : sub4 [2, 2, -2] = true := by decide +kernel
theorem sub4_603 : sub4 [2, 2, -1] = true := by decide +kernel
theorem sub4_604 : sub4 [2, 2, 0] = true := by decide +kernel
theorem sub4_605 : sub4 [2, 2, 1] = true := by decide +kernel
theorem sub4_606 : sub4 [2, 2, 2] = true := by decide +kernel
theorem sub4_607 : sub4 [2, 2, 3] = true := by decide +kernel
theorem sb4_18 : ∀ q ∈ blk4_18, sub4 q = true := by
  unfold blk4_18
  exact List.forall_mem_cons.2 ⟨sub4_576, List.forall_mem_cons.2 ⟨sub4_577, List.forall_mem_cons.2 ⟨sub4_578, List.forall_mem_cons.2 ⟨sub4_579, List.forall_mem_cons.2 ⟨sub4_580, List.forall_mem_cons.2 ⟨sub4_581, List.forall_mem_cons.2 ⟨sub4_582, List.forall_mem_cons.2 ⟨sub4_583, List.forall_mem_cons.2 ⟨sub4_584, List.forall_mem_cons.2 ⟨sub4_585, List.forall_mem_cons.2 ⟨sub4_586, List.forall_mem_cons.2 ⟨sub4_587, List.forall_mem_cons.2 ⟨sub4_588, List.forall_mem_cons.2 ⟨sub4_589, List.forall_mem_cons.2 ⟨sub4_590, List.forall_mem_cons.2 ⟨sub4_591, List.forall_mem_cons.2 ⟨sub4_592, List.forall_mem_cons.2 ⟨sub4_593, List.forall_mem_cons.2 ⟨sub4_594, List.forall_mem_cons.2 ⟨sub4_595, List.forall_mem_cons.2 ⟨sub4_596, List.forall_mem_cons.2 ⟨sub4_597, List.forall_mem_cons.2 ⟨sub4_598, List.forall_mem_cons.2 ⟨sub4_599, List.forall_mem_cons.2 ⟨sub4_600, List.forall_mem_cons.2 ⟨sub4_601, List.forall_mem_cons.2 ⟨sub4_602, List.forall_mem_cons.2 ⟨sub4_603, List.forall_mem_cons.2 ⟨sub4_604, List.forall_mem_cons.2 ⟨sub4_605, List.forall_mem_cons.2 ⟨sub4_606, List.forall_mem_cons.2 ⟨sub4_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_608 : sub4 [2, 2, 4] = true := by decide +kernel
theorem sub4_609 : sub4 [2, 2, 5] = true := by decide +kernel
theorem sub4_610 : sub4 [2, 2, 6] = true := by decide +kernel
theorem sub4_611 : sub4 [2, 2, 7] = true := by decide +kernel
theorem sub4_612 : sub4 [2, 2, 8] = true := by decide +kernel
theorem sub4_613 : sub4 [2, 3, -6] = true := by decide +kernel
theorem sub4_614 : sub4 [2, 3, -5] = true := by decide +kernel
theorem sub4_615 : sub4 [2, 3, -4] = true := by decide +kernel
theorem sub4_616 : sub4 [2, 3, -3] = true := by decide +kernel
theorem sub4_617 : sub4 [2, 3, -2] = true := by decide +kernel
theorem sub4_618 : sub4 [2, 3, -1] = true := by decide +kernel
theorem sub4_619 : sub4 [2, 3, 0] = true := by decide +kernel
theorem sub4_620 : sub4 [2, 3, 1] = true := by decide +kernel
theorem sub4_621 : sub4 [2, 3, 2] = true := by decide +kernel
theorem sub4_622 : sub4 [2, 3, 3] = true := by decide +kernel
theorem sub4_623 : sub4 [2, 3, 4] = true := by decide +kernel
theorem sub4_624 : sub4 [2, 3, 5] = true := by decide +kernel
theorem sub4_625 : sub4 [2, 3, 6] = true := by decide +kernel
theorem sub4_626 : sub4 [2, 3, 7] = true := by decide +kernel
theorem sub4_627 : sub4 [2, 3, 8] = true := by decide +kernel
theorem sub4_628 : sub4 [2, 4] = true := by decide +kernel
theorem sub4_629 : sub4 [2, 5] = true := by decide +kernel
theorem sub4_630 : sub4 [3, -4] = true := by decide +kernel
theorem sub4_631 : sub4 [3, -3] = true := by decide +kernel
theorem sub4_632 : sub4 [3, -2] = true := by decide +kernel
theorem sub4_633 : sub4 [3, -1, -7] = true := by decide +kernel
theorem sub4_634 : sub4 [3, -1, -6] = true := by decide +kernel
theorem sub4_635 : sub4 [3, -1, -5] = true := by decide +kernel
theorem sub4_636 : sub4 [3, -1, -4] = true := by decide +kernel
theorem sub4_637 : sub4 [3, -1, -3] = true := by decide +kernel
theorem sub4_638 : sub4 [3, -1, -2] = true := by decide +kernel
theorem sub4_639 : sub4 [3, -1, -1] = true := by decide +kernel
theorem sb4_19 : ∀ q ∈ blk4_19, sub4 q = true := by
  unfold blk4_19
  exact List.forall_mem_cons.2 ⟨sub4_608, List.forall_mem_cons.2 ⟨sub4_609, List.forall_mem_cons.2 ⟨sub4_610, List.forall_mem_cons.2 ⟨sub4_611, List.forall_mem_cons.2 ⟨sub4_612, List.forall_mem_cons.2 ⟨sub4_613, List.forall_mem_cons.2 ⟨sub4_614, List.forall_mem_cons.2 ⟨sub4_615, List.forall_mem_cons.2 ⟨sub4_616, List.forall_mem_cons.2 ⟨sub4_617, List.forall_mem_cons.2 ⟨sub4_618, List.forall_mem_cons.2 ⟨sub4_619, List.forall_mem_cons.2 ⟨sub4_620, List.forall_mem_cons.2 ⟨sub4_621, List.forall_mem_cons.2 ⟨sub4_622, List.forall_mem_cons.2 ⟨sub4_623, List.forall_mem_cons.2 ⟨sub4_624, List.forall_mem_cons.2 ⟨sub4_625, List.forall_mem_cons.2 ⟨sub4_626, List.forall_mem_cons.2 ⟨sub4_627, List.forall_mem_cons.2 ⟨sub4_628, List.forall_mem_cons.2 ⟨sub4_629, List.forall_mem_cons.2 ⟨sub4_630, List.forall_mem_cons.2 ⟨sub4_631, List.forall_mem_cons.2 ⟨sub4_632, List.forall_mem_cons.2 ⟨sub4_633, List.forall_mem_cons.2 ⟨sub4_634, List.forall_mem_cons.2 ⟨sub4_635, List.forall_mem_cons.2 ⟨sub4_636, List.forall_mem_cons.2 ⟨sub4_637, List.forall_mem_cons.2 ⟨sub4_638, List.forall_mem_cons.2 ⟨sub4_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_640 : sub4 [3, -1, 0] = true := by decide +kernel
theorem sub4_641 : sub4 [3, -1, 1] = true := by decide +kernel
theorem sub4_642 : sub4 [3, -1, 2] = true := by decide +kernel
theorem sub4_643 : sub4 [3, -1, 3] = true := by decide +kernel
theorem sub4_644 : sub4 [3, -1, 4] = true := by decide +kernel
theorem sub4_645 : sub4 [3, -1, 5] = true := by decide +kernel
theorem sub4_646 : sub4 [3, -1, 6] = true := by decide +kernel
theorem sub4_647 : sub4 [3, -1, 7] = true := by decide +kernel
theorem sub4_648 : sub4 [3, 0, -7] = true := by decide +kernel
theorem sub4_649 : sub4 [3, 0, -6] = true := by decide +kernel
theorem sub4_650 : sub4 [3, 0, -5] = true := by decide +kernel
theorem sub4_651 : sub4 [3, 0, -4] = true := by decide +kernel
theorem sub4_652 : sub4 [3, 0, -3] = true := by decide +kernel
theorem sub4_653 : sub4 [3, 0, -2] = true := by decide +kernel
theorem sub4_654 : sub4 [3, 0, -1] = true := by decide +kernel
theorem sub4_655 : sub4 [3, 0, 0] = true := by decide +kernel
theorem sub4_656 : sub4 [3, 0, 1] = true := by decide +kernel
theorem sub4_657 : sub4 [3, 0, 2] = true := by decide +kernel
theorem sub4_658 : sub4 [3, 0, 3] = true := by decide +kernel
theorem sub4_659 : sub4 [3, 0, 4] = true := by decide +kernel
theorem sub4_660 : sub4 [3, 0, 5] = true := by decide +kernel
theorem sub4_661 : sub4 [3, 0, 6] = true := by decide +kernel
theorem sub4_662 : sub4 [3, 0, 7] = true := by decide +kernel
theorem sub4_663 : sub4 [3, 1, -7] = true := by decide +kernel
theorem sub4_664 : sub4 [3, 1, -6] = true := by decide +kernel
theorem sub4_665 : sub4 [3, 1, -5] = true := by decide +kernel
theorem sub4_666 : sub4 [3, 1, -4] = true := by decide +kernel
theorem sub4_667 : sub4 [3, 1, -3] = true := by decide +kernel
theorem sub4_668 : sub4 [3, 1, -2] = true := by decide +kernel
theorem sub4_669 : sub4 [3, 1, -1] = true := by decide +kernel
theorem sub4_670 : sub4 [3, 1, 0] = true := by decide +kernel
theorem sub4_671 : sub4 [3, 1, 1] = true := by decide +kernel
theorem sb4_20 : ∀ q ∈ blk4_20, sub4 q = true := by
  unfold blk4_20
  exact List.forall_mem_cons.2 ⟨sub4_640, List.forall_mem_cons.2 ⟨sub4_641, List.forall_mem_cons.2 ⟨sub4_642, List.forall_mem_cons.2 ⟨sub4_643, List.forall_mem_cons.2 ⟨sub4_644, List.forall_mem_cons.2 ⟨sub4_645, List.forall_mem_cons.2 ⟨sub4_646, List.forall_mem_cons.2 ⟨sub4_647, List.forall_mem_cons.2 ⟨sub4_648, List.forall_mem_cons.2 ⟨sub4_649, List.forall_mem_cons.2 ⟨sub4_650, List.forall_mem_cons.2 ⟨sub4_651, List.forall_mem_cons.2 ⟨sub4_652, List.forall_mem_cons.2 ⟨sub4_653, List.forall_mem_cons.2 ⟨sub4_654, List.forall_mem_cons.2 ⟨sub4_655, List.forall_mem_cons.2 ⟨sub4_656, List.forall_mem_cons.2 ⟨sub4_657, List.forall_mem_cons.2 ⟨sub4_658, List.forall_mem_cons.2 ⟨sub4_659, List.forall_mem_cons.2 ⟨sub4_660, List.forall_mem_cons.2 ⟨sub4_661, List.forall_mem_cons.2 ⟨sub4_662, List.forall_mem_cons.2 ⟨sub4_663, List.forall_mem_cons.2 ⟨sub4_664, List.forall_mem_cons.2 ⟨sub4_665, List.forall_mem_cons.2 ⟨sub4_666, List.forall_mem_cons.2 ⟨sub4_667, List.forall_mem_cons.2 ⟨sub4_668, List.forall_mem_cons.2 ⟨sub4_669, List.forall_mem_cons.2 ⟨sub4_670, List.forall_mem_cons.2 ⟨sub4_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_672 : sub4 [3, 1, 2] = true := by decide +kernel
theorem sub4_673 : sub4 [3, 1, 3] = true := by decide +kernel
theorem sub4_674 : sub4 [3, 1, 4] = true := by decide +kernel
theorem sub4_675 : sub4 [3, 1, 5] = true := by decide +kernel
theorem sub4_676 : sub4 [3, 1, 6] = true := by decide +kernel
theorem sub4_677 : sub4 [3, 1, 7] = true := by decide +kernel
theorem sub4_678 : sub4 [3, 1, 8] = true := by decide +kernel
theorem sub4_679 : sub4 [3, 2, -6] = true := by decide +kernel
theorem sub4_680 : sub4 [3, 2, -5] = true := by decide +kernel
theorem sub4_681 : sub4 [3, 2, -4] = true := by decide +kernel
theorem sub4_682 : sub4 [3, 2, -3] = true := by decide +kernel
theorem sub4_683 : sub4 [3, 2, -2] = true := by decide +kernel
theorem sub4_684 : sub4 [3, 2, -1] = true := by decide +kernel
theorem sub4_685 : sub4 [3, 2, 0] = true := by decide +kernel
theorem sub4_686 : sub4 [3, 2, 1] = true := by decide +kernel
theorem sub4_687 : sub4 [3, 2, 2] = true := by decide +kernel
theorem sub4_688 : sub4 [3, 2, 3] = true := by decide +kernel
theorem sub4_689 : sub4 [3, 2, 4] = true := by decide +kernel
theorem sub4_690 : sub4 [3, 2, 5] = true := by decide +kernel
theorem sub4_691 : sub4 [3, 2, 6] = true := by decide +kernel
theorem sub4_692 : sub4 [3, 2, 7] = true := by decide +kernel
theorem sub4_693 : sub4 [3, 2, 8] = true := by decide +kernel
theorem sub4_694 : sub4 [3, 3] = true := by decide +kernel
theorem sub4_695 : sub4 [3, 4] = true := by decide +kernel
theorem sub4_696 : sub4 [3, 5] = true := by decide +kernel
theorem sub4_697 : sub4 [4, -3] = true := by decide +kernel
theorem sub4_698 : sub4 [4, -2] = true := by decide +kernel
theorem sub4_699 : sub4 [4, -1] = true := by decide +kernel
theorem sub4_700 : sub4 [4, 0] = true := by decide +kernel
theorem sub4_701 : sub4 [4, 1, -6] = true := by decide +kernel
theorem sub4_702 : sub4 [4, 1, -5] = true := by decide +kernel
theorem sub4_703 : sub4 [4, 1, -4] = true := by decide +kernel
theorem sb4_21 : ∀ q ∈ blk4_21, sub4 q = true := by
  unfold blk4_21
  exact List.forall_mem_cons.2 ⟨sub4_672, List.forall_mem_cons.2 ⟨sub4_673, List.forall_mem_cons.2 ⟨sub4_674, List.forall_mem_cons.2 ⟨sub4_675, List.forall_mem_cons.2 ⟨sub4_676, List.forall_mem_cons.2 ⟨sub4_677, List.forall_mem_cons.2 ⟨sub4_678, List.forall_mem_cons.2 ⟨sub4_679, List.forall_mem_cons.2 ⟨sub4_680, List.forall_mem_cons.2 ⟨sub4_681, List.forall_mem_cons.2 ⟨sub4_682, List.forall_mem_cons.2 ⟨sub4_683, List.forall_mem_cons.2 ⟨sub4_684, List.forall_mem_cons.2 ⟨sub4_685, List.forall_mem_cons.2 ⟨sub4_686, List.forall_mem_cons.2 ⟨sub4_687, List.forall_mem_cons.2 ⟨sub4_688, List.forall_mem_cons.2 ⟨sub4_689, List.forall_mem_cons.2 ⟨sub4_690, List.forall_mem_cons.2 ⟨sub4_691, List.forall_mem_cons.2 ⟨sub4_692, List.forall_mem_cons.2 ⟨sub4_693, List.forall_mem_cons.2 ⟨sub4_694, List.forall_mem_cons.2 ⟨sub4_695, List.forall_mem_cons.2 ⟨sub4_696, List.forall_mem_cons.2 ⟨sub4_697, List.forall_mem_cons.2 ⟨sub4_698, List.forall_mem_cons.2 ⟨sub4_699, List.forall_mem_cons.2 ⟨sub4_700, List.forall_mem_cons.2 ⟨sub4_701, List.forall_mem_cons.2 ⟨sub4_702, List.forall_mem_cons.2 ⟨sub4_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C049
