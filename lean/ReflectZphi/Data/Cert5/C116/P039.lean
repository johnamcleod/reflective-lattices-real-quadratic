import ReflectZphi.Data.Cert5.C116.Base

namespace ReflectZphi.Data.Cert5.C116

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_1_256 : subd9_1 [-7, -9] = true := by decide +kernel
theorem subd9_1_257 : subd9_1 [-7, -8, -11] = true := by decide +kernel
theorem subd9_1_258 : subd9_1 [-7, -8, -10] = true := by decide +kernel
theorem subd9_1_259 : subd9_1 [-7, -8, -9] = true := by decide +kernel
theorem subd9_1_260 : subd9_1 [-7, -8, -8] = true := by decide +kernel
theorem subd9_1_261 : subd9_1 [-7, -8, -7] = true := by decide +kernel
theorem subd9_1_262 : subd9_1 [-7, -8, -6] = true := by decide +kernel
theorem subd9_1_263 : subd9_1 [-7, -8, -5] = true := by decide +kernel
theorem subd9_1_264 : subd9_1 [-7, -8, -4] = true := by decide +kernel
theorem subd9_1_265 : subd9_1 [-7, -8, -3] = true := by decide +kernel
theorem subd9_1_266 : subd9_1 [-7, -8, -2] = true := by decide +kernel
theorem subd9_1_267 : subd9_1 [-7, -8, -1] = true := by decide +kernel
theorem subd9_1_268 : subd9_1 [-7, -8, 0] = true := by decide +kernel
theorem subd9_1_269 : subd9_1 [-7, -8, 1] = true := by decide +kernel
theorem subd9_1_270 : subd9_1 [-7, -8, 2] = true := by decide +kernel
theorem subd9_1_271 : subd9_1 [-7, -8, 3] = true := by decide +kernel
theorem subd9_1_272 : subd9_1 [-7, -7, -11] = true := by decide +kernel
theorem subd9_1_273 : subd9_1 [-7, -7, -10] = true := by decide +kernel
theorem subd9_1_274 : subd9_1 [-7, -7, -9] = true := by decide +kernel
theorem subd9_1_275 : subd9_1 [-7, -7, -8] = true := by decide +kernel
theorem subd9_1_276 : subd9_1 [-7, -7, -7] = true := by decide +kernel
theorem subd9_1_277 : subd9_1 [-7, -7, -6] = true := by decide +kernel
theorem subd9_1_278 : subd9_1 [-7, -7, -5] = true := by decide +kernel
theorem subd9_1_279 : subd9_1 [-7, -7, -4] = true := by decide +kernel
theorem subd9_1_280 : subd9_1 [-7, -7, -3] = true := by decide +kernel
theorem subd9_1_281 : subd9_1 [-7, -7, -2] = true := by decide +kernel
theorem subd9_1_282 : subd9_1 [-7, -7, -1] = true := by decide +kernel
theorem subd9_1_283 : subd9_1 [-7, -7, 0] = true := by decide +kernel
theorem subd9_1_284 : subd9_1 [-7, -7, 1] = true := by decide +kernel
theorem subd9_1_285 : subd9_1 [-7, -7, 2] = true := by decide +kernel
theorem subd9_1_286 : subd9_1 [-7, -7, 3] = true := by decide +kernel
theorem subd9_1_287 : subd9_1 [-7, -7, 4] = true := by decide +kernel
theorem sbd9_1_8 : ∀ q ∈ blkd9_1_8, subd9_1 q = true := by
  unfold blkd9_1_8
  exact List.forall_mem_cons.2 ⟨subd9_1_256, List.forall_mem_cons.2 ⟨subd9_1_257, List.forall_mem_cons.2 ⟨subd9_1_258, List.forall_mem_cons.2 ⟨subd9_1_259, List.forall_mem_cons.2 ⟨subd9_1_260, List.forall_mem_cons.2 ⟨subd9_1_261, List.forall_mem_cons.2 ⟨subd9_1_262, List.forall_mem_cons.2 ⟨subd9_1_263, List.forall_mem_cons.2 ⟨subd9_1_264, List.forall_mem_cons.2 ⟨subd9_1_265, List.forall_mem_cons.2 ⟨subd9_1_266, List.forall_mem_cons.2 ⟨subd9_1_267, List.forall_mem_cons.2 ⟨subd9_1_268, List.forall_mem_cons.2 ⟨subd9_1_269, List.forall_mem_cons.2 ⟨subd9_1_270, List.forall_mem_cons.2 ⟨subd9_1_271, List.forall_mem_cons.2 ⟨subd9_1_272, List.forall_mem_cons.2 ⟨subd9_1_273, List.forall_mem_cons.2 ⟨subd9_1_274, List.forall_mem_cons.2 ⟨subd9_1_275, List.forall_mem_cons.2 ⟨subd9_1_276, List.forall_mem_cons.2 ⟨subd9_1_277, List.forall_mem_cons.2 ⟨subd9_1_278, List.forall_mem_cons.2 ⟨subd9_1_279, List.forall_mem_cons.2 ⟨subd9_1_280, List.forall_mem_cons.2 ⟨subd9_1_281, List.forall_mem_cons.2 ⟨subd9_1_282, List.forall_mem_cons.2 ⟨subd9_1_283, List.forall_mem_cons.2 ⟨subd9_1_284, List.forall_mem_cons.2 ⟨subd9_1_285, List.forall_mem_cons.2 ⟨subd9_1_286, List.forall_mem_cons.2 ⟨subd9_1_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_288 : subd9_1 [-7, -6, -11] = true := by decide +kernel
theorem subd9_1_289 : subd9_1 [-7, -6, -10] = true := by decide +kernel
theorem subd9_1_290 : subd9_1 [-7, -6, -9] = true := by decide +kernel
theorem subd9_1_291 : subd9_1 [-7, -6, -8] = true := by decide +kernel
theorem subd9_1_292 : subd9_1 [-7, -6, -7] = true := by decide +kernel
theorem subd9_1_293 : subd9_1 [-7, -6, -6] = true := by decide +kernel
theorem subd9_1_294 : subd9_1 [-7, -6, -5] = true := by decide +kernel
theorem subd9_1_295 : subd9_1 [-7, -6, -4] = true := by decide +kernel
theorem subd9_1_296 : subd9_1 [-7, -6, -3] = true := by decide +kernel
theorem subd9_1_297 : subd9_1 [-7, -6, -2] = true := by decide +kernel
theorem subd9_1_298 : subd9_1 [-7, -6, -1] = true := by decide +kernel
theorem subd9_1_299 : subd9_1 [-7, -6, 0] = true := by decide +kernel
theorem subd9_1_300 : subd9_1 [-7, -6, 1] = true := by decide +kernel
theorem subd9_1_301 : subd9_1 [-7, -6, 2] = true := by decide +kernel
theorem subd9_1_302 : subd9_1 [-7, -6, 3] = true := by decide +kernel
theorem subd9_1_303 : subd9_1 [-7, -6, 4] = true := by decide +kernel
theorem subd9_1_304 : subd9_1 [-7, -6, 5] = true := by decide +kernel
theorem subd9_1_305 : subd9_1 [-7, -5, -11] = true := by decide +kernel
theorem subd9_1_306 : subd9_1 [-7, -5, -10] = true := by decide +kernel
theorem subd9_1_307 : subd9_1 [-7, -5, -9] = true := by decide +kernel
theorem subd9_1_308 : subd9_1 [-7, -5, -8] = true := by decide +kernel
theorem subd9_1_309 : subd9_1 [-7, -5, -7] = true := by decide +kernel
theorem subd9_1_310 : subd9_1 [-7, -5, -6] = true := by decide +kernel
theorem subd9_1_311 : subd9_1 [-7, -5, -5] = true := by decide +kernel
theorem subd9_1_312 : subd9_1 [-7, -5, -4] = true := by decide +kernel
theorem subd9_1_313 : subd9_1 [-7, -5, -3] = true := by decide +kernel
theorem subd9_1_314 : subd9_1 [-7, -5, -2] = true := by decide +kernel
theorem subd9_1_315 : subd9_1 [-7, -5, -1] = true := by decide +kernel
theorem subd9_1_316 : subd9_1 [-7, -5, 0] = true := by decide +kernel
theorem subd9_1_317 : subd9_1 [-7, -5, 1] = true := by decide +kernel
theorem subd9_1_318 : subd9_1 [-7, -5, 2] = true := by decide +kernel
theorem subd9_1_319 : subd9_1 [-7, -5, 3] = true := by decide +kernel
theorem sbd9_1_9 : ∀ q ∈ blkd9_1_9, subd9_1 q = true := by
  unfold blkd9_1_9
  exact List.forall_mem_cons.2 ⟨subd9_1_288, List.forall_mem_cons.2 ⟨subd9_1_289, List.forall_mem_cons.2 ⟨subd9_1_290, List.forall_mem_cons.2 ⟨subd9_1_291, List.forall_mem_cons.2 ⟨subd9_1_292, List.forall_mem_cons.2 ⟨subd9_1_293, List.forall_mem_cons.2 ⟨subd9_1_294, List.forall_mem_cons.2 ⟨subd9_1_295, List.forall_mem_cons.2 ⟨subd9_1_296, List.forall_mem_cons.2 ⟨subd9_1_297, List.forall_mem_cons.2 ⟨subd9_1_298, List.forall_mem_cons.2 ⟨subd9_1_299, List.forall_mem_cons.2 ⟨subd9_1_300, List.forall_mem_cons.2 ⟨subd9_1_301, List.forall_mem_cons.2 ⟨subd9_1_302, List.forall_mem_cons.2 ⟨subd9_1_303, List.forall_mem_cons.2 ⟨subd9_1_304, List.forall_mem_cons.2 ⟨subd9_1_305, List.forall_mem_cons.2 ⟨subd9_1_306, List.forall_mem_cons.2 ⟨subd9_1_307, List.forall_mem_cons.2 ⟨subd9_1_308, List.forall_mem_cons.2 ⟨subd9_1_309, List.forall_mem_cons.2 ⟨subd9_1_310, List.forall_mem_cons.2 ⟨subd9_1_311, List.forall_mem_cons.2 ⟨subd9_1_312, List.forall_mem_cons.2 ⟨subd9_1_313, List.forall_mem_cons.2 ⟨subd9_1_314, List.forall_mem_cons.2 ⟨subd9_1_315, List.forall_mem_cons.2 ⟨subd9_1_316, List.forall_mem_cons.2 ⟨subd9_1_317, List.forall_mem_cons.2 ⟨subd9_1_318, List.forall_mem_cons.2 ⟨subd9_1_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_320 : subd9_1 [-7, -5, 4] = true := by decide +kernel
theorem subd9_1_321 : subd9_1 [-7, -5, 5] = true := by decide +kernel
theorem subd9_1_322 : subd9_1 [-7, -4, -11] = true := by decide +kernel
theorem subd9_1_323 : subd9_1 [-7, -4, -10] = true := by decide +kernel
theorem subd9_1_324 : subd9_1 [-7, -4, -9] = true := by decide +kernel
theorem subd9_1_325 : subd9_1 [-7, -4, -8] = true := by decide +kernel
theorem subd9_1_326 : subd9_1 [-7, -4, -7] = true := by decide +kernel
theorem subd9_1_327 : subd9_1 [-7, -4, -6] = true := by decide +kernel
theorem subd9_1_328 : subd9_1 [-7, -4, -5] = true := by decide +kernel
theorem subd9_1_329 : subd9_1 [-7, -4, -4] = true := by decide +kernel
theorem subd9_1_330 : subd9_1 [-7, -4, -3] = true := by decide +kernel
theorem subd9_1_331 : subd9_1 [-7, -4, -2] = true := by decide +kernel
theorem subd9_1_332 : subd9_1 [-7, -4, -1] = true := by decide +kernel
theorem subd9_1_333 : subd9_1 [-7, -4, 0] = true := by decide +kernel
theorem subd9_1_334 : subd9_1 [-7, -4, 1] = true := by decide +kernel
theorem subd9_1_335 : subd9_1 [-7, -4, 2] = true := by decide +kernel
theorem subd9_1_336 : subd9_1 [-7, -4, 3] = true := by decide +kernel
theorem subd9_1_337 : subd9_1 [-7, -4, 4] = true := by decide +kernel
theorem subd9_1_338 : subd9_1 [-7, -4, 5] = true := by decide +kernel
theorem subd9_1_339 : subd9_1 [-7, -4, 6] = true := by decide +kernel
theorem subd9_1_340 : subd9_1 [-7, -3, -10] = true := by decide +kernel
theorem subd9_1_341 : subd9_1 [-7, -3, -9] = true := by decide +kernel
theorem subd9_1_342 : subd9_1 [-7, -3, -8] = true := by decide +kernel
theorem subd9_1_343 : subd9_1 [-7, -3, -7] = true := by decide +kernel
theorem subd9_1_344 : subd9_1 [-7, -3, -6] = true := by decide +kernel
theorem subd9_1_345 : subd9_1 [-7, -3, -5] = true := by decide +kernel
theorem subd9_1_346 : subd9_1 [-7, -3, -4] = true := by decide +kernel
theorem subd9_1_347 : subd9_1 [-7, -3, -3] = true := by decide +kernel
theorem subd9_1_348 : subd9_1 [-7, -3, -2] = true := by decide +kernel
theorem subd9_1_349 : subd9_1 [-7, -3, -1] = true := by decide +kernel
theorem subd9_1_350 : subd9_1 [-7, -3, 0] = true := by decide +kernel
theorem subd9_1_351 : subd9_1 [-7, -3, 1] = true := by decide +kernel
theorem sbd9_1_10 : ∀ q ∈ blkd9_1_10, subd9_1 q = true := by
  unfold blkd9_1_10
  exact List.forall_mem_cons.2 ⟨subd9_1_320, List.forall_mem_cons.2 ⟨subd9_1_321, List.forall_mem_cons.2 ⟨subd9_1_322, List.forall_mem_cons.2 ⟨subd9_1_323, List.forall_mem_cons.2 ⟨subd9_1_324, List.forall_mem_cons.2 ⟨subd9_1_325, List.forall_mem_cons.2 ⟨subd9_1_326, List.forall_mem_cons.2 ⟨subd9_1_327, List.forall_mem_cons.2 ⟨subd9_1_328, List.forall_mem_cons.2 ⟨subd9_1_329, List.forall_mem_cons.2 ⟨subd9_1_330, List.forall_mem_cons.2 ⟨subd9_1_331, List.forall_mem_cons.2 ⟨subd9_1_332, List.forall_mem_cons.2 ⟨subd9_1_333, List.forall_mem_cons.2 ⟨subd9_1_334, List.forall_mem_cons.2 ⟨subd9_1_335, List.forall_mem_cons.2 ⟨subd9_1_336, List.forall_mem_cons.2 ⟨subd9_1_337, List.forall_mem_cons.2 ⟨subd9_1_338, List.forall_mem_cons.2 ⟨subd9_1_339, List.forall_mem_cons.2 ⟨subd9_1_340, List.forall_mem_cons.2 ⟨subd9_1_341, List.forall_mem_cons.2 ⟨subd9_1_342, List.forall_mem_cons.2 ⟨subd9_1_343, List.forall_mem_cons.2 ⟨subd9_1_344, List.forall_mem_cons.2 ⟨subd9_1_345, List.forall_mem_cons.2 ⟨subd9_1_346, List.forall_mem_cons.2 ⟨subd9_1_347, List.forall_mem_cons.2 ⟨subd9_1_348, List.forall_mem_cons.2 ⟨subd9_1_349, List.forall_mem_cons.2 ⟨subd9_1_350, List.forall_mem_cons.2 ⟨subd9_1_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_352 : subd9_1 [-7, -3, 2] = true := by decide +kernel
theorem subd9_1_353 : subd9_1 [-7, -3, 3] = true := by decide +kernel
theorem subd9_1_354 : subd9_1 [-7, -3, 4] = true := by decide +kernel
theorem subd9_1_355 : subd9_1 [-7, -3, 5] = true := by decide +kernel
theorem subd9_1_356 : subd9_1 [-7, -3, 6] = true := by decide +kernel
theorem subd9_1_357 : subd9_1 [-7, -2, -10] = true := by decide +kernel
theorem subd9_1_358 : subd9_1 [-7, -2, -9] = true := by decide +kernel
theorem subd9_1_359 : subd9_1 [-7, -2, -8] = true := by decide +kernel
theorem subd9_1_360 : subd9_1 [-7, -2, -7] = true := by decide +kernel
theorem subd9_1_361 : subd9_1 [-7, -2, -6] = true := by decide +kernel
theorem subd9_1_362 : subd9_1 [-7, -2, -5] = true := by decide +kernel
theorem subd9_1_363 : subd9_1 [-7, -2, -4] = true := by decide +kernel
theorem subd9_1_364 : subd9_1 [-7, -2, -3] = true := by decide +kernel
theorem subd9_1_365 : subd9_1 [-7, -2, -2] = true := by decide +kernel
theorem subd9_1_366 : subd9_1 [-7, -2, -1] = true := by decide +kernel
theorem subd9_1_367 : subd9_1 [-7, -2, 0] = true := by decide +kernel
theorem subd9_1_368 : subd9_1 [-7, -2, 1] = true := by decide +kernel
theorem subd9_1_369 : subd9_1 [-7, -2, 2] = true := by decide +kernel
theorem subd9_1_370 : subd9_1 [-7, -2, 3] = true := by decide +kernel
theorem subd9_1_371 : subd9_1 [-7, -2, 4] = true := by decide +kernel
theorem subd9_1_372 : subd9_1 [-7, -2, 5] = true := by decide +kernel
theorem subd9_1_373 : subd9_1 [-7, -2, 6] = true := by decide +kernel
theorem subd9_1_374 : subd9_1 [-7, -2, 7] = true := by decide +kernel
theorem subd9_1_375 : subd9_1 [-7, -1, -9] = true := by decide +kernel
theorem subd9_1_376 : subd9_1 [-7, -1, -8] = true := by decide +kernel
theorem subd9_1_377 : subd9_1 [-7, -1, -7] = true := by decide +kernel
theorem subd9_1_378 : subd9_1 [-7, -1, -6] = true := by decide +kernel
theorem subd9_1_379 : subd9_1 [-7, -1, -5] = true := by decide +kernel
theorem subd9_1_380 : subd9_1 [-7, -1, -4] = true := by decide +kernel
theorem subd9_1_381 : subd9_1 [-7, -1, -3] = true := by decide +kernel
theorem subd9_1_382 : subd9_1 [-7, -1, -2] = true := by decide +kernel
theorem subd9_1_383 : subd9_1 [-7, -1, -1] = true := by decide +kernel
theorem sbd9_1_11 : ∀ q ∈ blkd9_1_11, subd9_1 q = true := by
  unfold blkd9_1_11
  exact List.forall_mem_cons.2 ⟨subd9_1_352, List.forall_mem_cons.2 ⟨subd9_1_353, List.forall_mem_cons.2 ⟨subd9_1_354, List.forall_mem_cons.2 ⟨subd9_1_355, List.forall_mem_cons.2 ⟨subd9_1_356, List.forall_mem_cons.2 ⟨subd9_1_357, List.forall_mem_cons.2 ⟨subd9_1_358, List.forall_mem_cons.2 ⟨subd9_1_359, List.forall_mem_cons.2 ⟨subd9_1_360, List.forall_mem_cons.2 ⟨subd9_1_361, List.forall_mem_cons.2 ⟨subd9_1_362, List.forall_mem_cons.2 ⟨subd9_1_363, List.forall_mem_cons.2 ⟨subd9_1_364, List.forall_mem_cons.2 ⟨subd9_1_365, List.forall_mem_cons.2 ⟨subd9_1_366, List.forall_mem_cons.2 ⟨subd9_1_367, List.forall_mem_cons.2 ⟨subd9_1_368, List.forall_mem_cons.2 ⟨subd9_1_369, List.forall_mem_cons.2 ⟨subd9_1_370, List.forall_mem_cons.2 ⟨subd9_1_371, List.forall_mem_cons.2 ⟨subd9_1_372, List.forall_mem_cons.2 ⟨subd9_1_373, List.forall_mem_cons.2 ⟨subd9_1_374, List.forall_mem_cons.2 ⟨subd9_1_375, List.forall_mem_cons.2 ⟨subd9_1_376, List.forall_mem_cons.2 ⟨subd9_1_377, List.forall_mem_cons.2 ⟨subd9_1_378, List.forall_mem_cons.2 ⟨subd9_1_379, List.forall_mem_cons.2 ⟨subd9_1_380, List.forall_mem_cons.2 ⟨subd9_1_381, List.forall_mem_cons.2 ⟨subd9_1_382, List.forall_mem_cons.2 ⟨subd9_1_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_384 : subd9_1 [-7, -1, 0] = true := by decide +kernel
theorem subd9_1_385 : subd9_1 [-7, -1, 1] = true := by decide +kernel
theorem subd9_1_386 : subd9_1 [-7, -1, 2] = true := by decide +kernel
theorem subd9_1_387 : subd9_1 [-7, -1, 3] = true := by decide +kernel
theorem subd9_1_388 : subd9_1 [-7, -1, 4] = true := by decide +kernel
theorem subd9_1_389 : subd9_1 [-7, -1, 5] = true := by decide +kernel
theorem subd9_1_390 : subd9_1 [-7, -1, 6] = true := by decide +kernel
theorem subd9_1_391 : subd9_1 [-7, -1, 7] = true := by decide +kernel
theorem subd9_1_392 : subd9_1 [-7, 0, -9] = true := by decide +kernel
theorem subd9_1_393 : subd9_1 [-7, 0, -8] = true := by decide +kernel
theorem subd9_1_394 : subd9_1 [-7, 0, -7] = true := by decide +kernel
theorem subd9_1_395 : subd9_1 [-7, 0, -6] = true := by decide +kernel
theorem subd9_1_396 : subd9_1 [-7, 0, -5] = true := by decide +kernel
theorem subd9_1_397 : subd9_1 [-7, 0, -4] = true := by decide +kernel
theorem subd9_1_398 : subd9_1 [-7, 0, -3] = true := by decide +kernel
theorem subd9_1_399 : subd9_1 [-7, 0, -2] = true := by decide +kernel
theorem subd9_1_400 : subd9_1 [-7, 0, -1] = true := by decide +kernel
theorem subd9_1_401 : subd9_1 [-7, 0, 0] = true := by decide +kernel
theorem subd9_1_402 : subd9_1 [-7, 0, 1] = true := by decide +kernel
theorem subd9_1_403 : subd9_1 [-7, 0, 2] = true := by decide +kernel
theorem subd9_1_404 : subd9_1 [-7, 0, 3] = true := by decide +kernel
theorem subd9_1_405 : subd9_1 [-7, 0, 4] = true := by decide +kernel
theorem subd9_1_406 : subd9_1 [-7, 0, 5] = true := by decide +kernel
theorem subd9_1_407 : subd9_1 [-7, 0, 6] = true := by decide +kernel
theorem subd9_1_408 : subd9_1 [-7, 0, 7] = true := by decide +kernel
theorem subd9_1_409 : subd9_1 [-7, 0, 8] = true := by decide +kernel
theorem subd9_1_410 : subd9_1 [-7, 1, -8] = true := by decide +kernel
theorem subd9_1_411 : subd9_1 [-7, 1, -7] = true := by decide +kernel
theorem subd9_1_412 : subd9_1 [-7, 1, -6] = true := by decide +kernel
theorem subd9_1_413 : subd9_1 [-7, 1, -5] = true := by decide +kernel
theorem subd9_1_414 : subd9_1 [-7, 1, -4] = true := by decide +kernel
theorem subd9_1_415 : subd9_1 [-7, 1, -3] = true := by decide +kernel
theorem sbd9_1_12 : ∀ q ∈ blkd9_1_12, subd9_1 q = true := by
  unfold blkd9_1_12
  exact List.forall_mem_cons.2 ⟨subd9_1_384, List.forall_mem_cons.2 ⟨subd9_1_385, List.forall_mem_cons.2 ⟨subd9_1_386, List.forall_mem_cons.2 ⟨subd9_1_387, List.forall_mem_cons.2 ⟨subd9_1_388, List.forall_mem_cons.2 ⟨subd9_1_389, List.forall_mem_cons.2 ⟨subd9_1_390, List.forall_mem_cons.2 ⟨subd9_1_391, List.forall_mem_cons.2 ⟨subd9_1_392, List.forall_mem_cons.2 ⟨subd9_1_393, List.forall_mem_cons.2 ⟨subd9_1_394, List.forall_mem_cons.2 ⟨subd9_1_395, List.forall_mem_cons.2 ⟨subd9_1_396, List.forall_mem_cons.2 ⟨subd9_1_397, List.forall_mem_cons.2 ⟨subd9_1_398, List.forall_mem_cons.2 ⟨subd9_1_399, List.forall_mem_cons.2 ⟨subd9_1_400, List.forall_mem_cons.2 ⟨subd9_1_401, List.forall_mem_cons.2 ⟨subd9_1_402, List.forall_mem_cons.2 ⟨subd9_1_403, List.forall_mem_cons.2 ⟨subd9_1_404, List.forall_mem_cons.2 ⟨subd9_1_405, List.forall_mem_cons.2 ⟨subd9_1_406, List.forall_mem_cons.2 ⟨subd9_1_407, List.forall_mem_cons.2 ⟨subd9_1_408, List.forall_mem_cons.2 ⟨subd9_1_409, List.forall_mem_cons.2 ⟨subd9_1_410, List.forall_mem_cons.2 ⟨subd9_1_411, List.forall_mem_cons.2 ⟨subd9_1_412, List.forall_mem_cons.2 ⟨subd9_1_413, List.forall_mem_cons.2 ⟨subd9_1_414, List.forall_mem_cons.2 ⟨subd9_1_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_416 : subd9_1 [-7, 1, -2] = true := by decide +kernel
theorem subd9_1_417 : subd9_1 [-7, 1, -1] = true := by decide +kernel
theorem subd9_1_418 : subd9_1 [-7, 1, 0] = true := by decide +kernel
theorem subd9_1_419 : subd9_1 [-7, 1, 1] = true := by decide +kernel
theorem subd9_1_420 : subd9_1 [-7, 1, 2] = true := by decide +kernel
theorem subd9_1_421 : subd9_1 [-7, 1, 3] = true := by decide +kernel
theorem subd9_1_422 : subd9_1 [-7, 1, 4] = true := by decide +kernel
theorem subd9_1_423 : subd9_1 [-7, 1, 5] = true := by decide +kernel
theorem subd9_1_424 : subd9_1 [-7, 1, 6] = true := by decide +kernel
theorem subd9_1_425 : subd9_1 [-7, 1, 7] = true := by decide +kernel
theorem subd9_1_426 : subd9_1 [-7, 1, 8] = true := by decide +kernel
theorem subd9_1_427 : subd9_1 [-7, 2, -7] = true := by decide +kernel
theorem subd9_1_428 : subd9_1 [-7, 2, -6] = true := by decide +kernel
theorem subd9_1_429 : subd9_1 [-7, 2, -5] = true := by decide +kernel
theorem subd9_1_430 : subd9_1 [-7, 2, -4] = true := by decide +kernel
theorem subd9_1_431 : subd9_1 [-7, 2, -3] = true := by decide +kernel
theorem subd9_1_432 : subd9_1 [-7, 2, -2] = true := by decide +kernel
theorem subd9_1_433 : subd9_1 [-7, 2, -1] = true := by decide +kernel
theorem subd9_1_434 : subd9_1 [-7, 2, 0] = true := by decide +kernel
theorem subd9_1_435 : subd9_1 [-7, 2, 1] = true := by decide +kernel
theorem subd9_1_436 : subd9_1 [-7, 2, 2] = true := by decide +kernel
theorem subd9_1_437 : subd9_1 [-7, 2, 3] = true := by decide +kernel
theorem subd9_1_438 : subd9_1 [-7, 2, 4] = true := by decide +kernel
theorem subd9_1_439 : subd9_1 [-7, 2, 5] = true := by decide +kernel
theorem subd9_1_440 : subd9_1 [-7, 2, 6] = true := by decide +kernel
theorem subd9_1_441 : subd9_1 [-7, 2, 7] = true := by decide +kernel
theorem subd9_1_442 : subd9_1 [-7, 2, 8] = true := by decide +kernel
theorem subd9_1_443 : subd9_1 [-7, 3, -7] = true := by decide +kernel
theorem subd9_1_444 : subd9_1 [-7, 3, -6] = true := by decide +kernel
theorem subd9_1_445 : subd9_1 [-7, 3, -5] = true := by decide +kernel
theorem subd9_1_446 : subd9_1 [-7, 3, -4] = true := by decide +kernel
theorem subd9_1_447 : subd9_1 [-7, 3, -3] = true := by decide +kernel
theorem sbd9_1_13 : ∀ q ∈ blkd9_1_13, subd9_1 q = true := by
  unfold blkd9_1_13
  exact List.forall_mem_cons.2 ⟨subd9_1_416, List.forall_mem_cons.2 ⟨subd9_1_417, List.forall_mem_cons.2 ⟨subd9_1_418, List.forall_mem_cons.2 ⟨subd9_1_419, List.forall_mem_cons.2 ⟨subd9_1_420, List.forall_mem_cons.2 ⟨subd9_1_421, List.forall_mem_cons.2 ⟨subd9_1_422, List.forall_mem_cons.2 ⟨subd9_1_423, List.forall_mem_cons.2 ⟨subd9_1_424, List.forall_mem_cons.2 ⟨subd9_1_425, List.forall_mem_cons.2 ⟨subd9_1_426, List.forall_mem_cons.2 ⟨subd9_1_427, List.forall_mem_cons.2 ⟨subd9_1_428, List.forall_mem_cons.2 ⟨subd9_1_429, List.forall_mem_cons.2 ⟨subd9_1_430, List.forall_mem_cons.2 ⟨subd9_1_431, List.forall_mem_cons.2 ⟨subd9_1_432, List.forall_mem_cons.2 ⟨subd9_1_433, List.forall_mem_cons.2 ⟨subd9_1_434, List.forall_mem_cons.2 ⟨subd9_1_435, List.forall_mem_cons.2 ⟨subd9_1_436, List.forall_mem_cons.2 ⟨subd9_1_437, List.forall_mem_cons.2 ⟨subd9_1_438, List.forall_mem_cons.2 ⟨subd9_1_439, List.forall_mem_cons.2 ⟨subd9_1_440, List.forall_mem_cons.2 ⟨subd9_1_441, List.forall_mem_cons.2 ⟨subd9_1_442, List.forall_mem_cons.2 ⟨subd9_1_443, List.forall_mem_cons.2 ⟨subd9_1_444, List.forall_mem_cons.2 ⟨subd9_1_445, List.forall_mem_cons.2 ⟨subd9_1_446, List.forall_mem_cons.2 ⟨subd9_1_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_448 : subd9_1 [-7, 3, -2] = true := by decide +kernel
theorem subd9_1_449 : subd9_1 [-7, 3, -1] = true := by decide +kernel
theorem subd9_1_450 : subd9_1 [-7, 3, 0] = true := by decide +kernel
theorem subd9_1_451 : subd9_1 [-7, 3, 1] = true := by decide +kernel
theorem subd9_1_452 : subd9_1 [-7, 3, 2] = true := by decide +kernel
theorem subd9_1_453 : subd9_1 [-7, 3, 3] = true := by decide +kernel
theorem subd9_1_454 : subd9_1 [-7, 3, 4] = true := by decide +kernel
theorem subd9_1_455 : subd9_1 [-7, 3, 5] = true := by decide +kernel
theorem subd9_1_456 : subd9_1 [-7, 3, 6] = true := by decide +kernel
theorem subd9_1_457 : subd9_1 [-7, 3, 7] = true := by decide +kernel
theorem subd9_1_458 : subd9_1 [-7, 3, 8] = true := by decide +kernel
theorem subd9_1_459 : subd9_1 [-7, 4, -6] = true := by decide +kernel
theorem subd9_1_460 : subd9_1 [-7, 4, -5] = true := by decide +kernel
theorem subd9_1_461 : subd9_1 [-7, 4, -4] = true := by decide +kernel
theorem subd9_1_462 : subd9_1 [-7, 4, -3] = true := by decide +kernel
theorem subd9_1_463 : subd9_1 [-7, 4, -2] = true := by decide +kernel
theorem subd9_1_464 : subd9_1 [-7, 4, -1] = true := by decide +kernel
theorem subd9_1_465 : subd9_1 [-7, 4, 0] = true := by decide +kernel
theorem subd9_1_466 : subd9_1 [-7, 4, 1] = true := by decide +kernel
theorem subd9_1_467 : subd9_1 [-7, 4, 2] = true := by decide +kernel
theorem subd9_1_468 : subd9_1 [-7, 4, 3] = true := by decide +kernel
theorem subd9_1_469 : subd9_1 [-7, 4, 4] = true := by decide +kernel
theorem subd9_1_470 : subd9_1 [-7, 4, 5] = true := by decide +kernel
theorem subd9_1_471 : subd9_1 [-7, 4, 6] = true := by decide +kernel
theorem subd9_1_472 : subd9_1 [-7, 4, 7] = true := by decide +kernel
theorem subd9_1_473 : subd9_1 [-7, 4, 8] = true := by decide +kernel
theorem subd9_1_474 : subd9_1 [-7, 5] = true := by decide +kernel
theorem subd9_1_475 : subd9_1 [-7, 6] = true := by decide +kernel
theorem subd9_1_476 : subd9_1 [-7, 7] = true := by decide +kernel
theorem subd9_1_477 : subd9_1 [-7, 8] = true := by decide +kernel
theorem subd9_1_478 : subd9_1 [-6, -13] = true := by decide +kernel
theorem subd9_1_479 : subd9_1 [-6, -12] = true := by decide +kernel
theorem sbd9_1_14 : ∀ q ∈ blkd9_1_14, subd9_1 q = true := by
  unfold blkd9_1_14
  exact List.forall_mem_cons.2 ⟨subd9_1_448, List.forall_mem_cons.2 ⟨subd9_1_449, List.forall_mem_cons.2 ⟨subd9_1_450, List.forall_mem_cons.2 ⟨subd9_1_451, List.forall_mem_cons.2 ⟨subd9_1_452, List.forall_mem_cons.2 ⟨subd9_1_453, List.forall_mem_cons.2 ⟨subd9_1_454, List.forall_mem_cons.2 ⟨subd9_1_455, List.forall_mem_cons.2 ⟨subd9_1_456, List.forall_mem_cons.2 ⟨subd9_1_457, List.forall_mem_cons.2 ⟨subd9_1_458, List.forall_mem_cons.2 ⟨subd9_1_459, List.forall_mem_cons.2 ⟨subd9_1_460, List.forall_mem_cons.2 ⟨subd9_1_461, List.forall_mem_cons.2 ⟨subd9_1_462, List.forall_mem_cons.2 ⟨subd9_1_463, List.forall_mem_cons.2 ⟨subd9_1_464, List.forall_mem_cons.2 ⟨subd9_1_465, List.forall_mem_cons.2 ⟨subd9_1_466, List.forall_mem_cons.2 ⟨subd9_1_467, List.forall_mem_cons.2 ⟨subd9_1_468, List.forall_mem_cons.2 ⟨subd9_1_469, List.forall_mem_cons.2 ⟨subd9_1_470, List.forall_mem_cons.2 ⟨subd9_1_471, List.forall_mem_cons.2 ⟨subd9_1_472, List.forall_mem_cons.2 ⟨subd9_1_473, List.forall_mem_cons.2 ⟨subd9_1_474, List.forall_mem_cons.2 ⟨subd9_1_475, List.forall_mem_cons.2 ⟨subd9_1_476, List.forall_mem_cons.2 ⟨subd9_1_477, List.forall_mem_cons.2 ⟨subd9_1_478, List.forall_mem_cons.2 ⟨subd9_1_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_480 : subd9_1 [-6, -11] = true := by decide +kernel
theorem subd9_1_481 : subd9_1 [-6, -10] = true := by decide +kernel
theorem subd9_1_482 : subd9_1 [-6, -9] = true := by decide +kernel
theorem subd9_1_483 : subd9_1 [-6, -8, -11] = true := by decide +kernel
theorem subd9_1_484 : subd9_1 [-6, -8, -10] = true := by decide +kernel
theorem subd9_1_485 : subd9_1 [-6, -8, -9] = true := by decide +kernel
theorem subd9_1_486 : subd9_1 [-6, -8, -8] = true := by decide +kernel
theorem subd9_1_487 : subd9_1 [-6, -8, -7] = true := by decide +kernel
theorem subd9_1_488 : subd9_1 [-6, -8, -6] = true := by decide +kernel
theorem subd9_1_489 : subd9_1 [-6, -8, -5] = true := by decide +kernel
theorem subd9_1_490 : subd9_1 [-6, -8, -4] = true := by decide +kernel
theorem subd9_1_491 : subd9_1 [-6, -8, -3] = true := by decide +kernel
theorem subd9_1_492 : subd9_1 [-6, -8, -2] = true := by decide +kernel
theorem subd9_1_493 : subd9_1 [-6, -8, -1] = true := by decide +kernel
theorem subd9_1_494 : subd9_1 [-6, -8, 0] = true := by decide +kernel
theorem subd9_1_495 : subd9_1 [-6, -8, 1] = true := by decide +kernel
theorem subd9_1_496 : subd9_1 [-6, -8, 2] = true := by decide +kernel
theorem subd9_1_497 : subd9_1 [-6, -8, 3] = true := by decide +kernel
theorem subd9_1_498 : subd9_1 [-6, -7, -11] = true := by decide +kernel
theorem subd9_1_499 : subd9_1 [-6, -7, -10] = true := by decide +kernel
theorem subd9_1_500 : subd9_1 [-6, -7, -9] = true := by decide +kernel
theorem subd9_1_501 : subd9_1 [-6, -7, -8] = true := by decide +kernel
theorem subd9_1_502 : subd9_1 [-6, -7, -7] = true := by decide +kernel
theorem subd9_1_503 : subd9_1 [-6, -7, -6] = true := by decide +kernel
theorem subd9_1_504 : subd9_1 [-6, -7, -5] = true := by decide +kernel
theorem subd9_1_505 : subd9_1 [-6, -7, -4] = true := by decide +kernel
theorem subd9_1_506 : subd9_1 [-6, -7, -3] = true := by decide +kernel
theorem subd9_1_507 : subd9_1 [-6, -7, -2] = true := by decide +kernel
theorem subd9_1_508 : subd9_1 [-6, -7, -1] = true := by decide +kernel
theorem subd9_1_509 : subd9_1 [-6, -7, 0] = true := by decide +kernel
theorem subd9_1_510 : subd9_1 [-6, -7, 1] = true := by decide +kernel
theorem subd9_1_511 : subd9_1 [-6, -7, 2] = true := by decide +kernel
theorem sbd9_1_15 : ∀ q ∈ blkd9_1_15, subd9_1 q = true := by
  unfold blkd9_1_15
  exact List.forall_mem_cons.2 ⟨subd9_1_480, List.forall_mem_cons.2 ⟨subd9_1_481, List.forall_mem_cons.2 ⟨subd9_1_482, List.forall_mem_cons.2 ⟨subd9_1_483, List.forall_mem_cons.2 ⟨subd9_1_484, List.forall_mem_cons.2 ⟨subd9_1_485, List.forall_mem_cons.2 ⟨subd9_1_486, List.forall_mem_cons.2 ⟨subd9_1_487, List.forall_mem_cons.2 ⟨subd9_1_488, List.forall_mem_cons.2 ⟨subd9_1_489, List.forall_mem_cons.2 ⟨subd9_1_490, List.forall_mem_cons.2 ⟨subd9_1_491, List.forall_mem_cons.2 ⟨subd9_1_492, List.forall_mem_cons.2 ⟨subd9_1_493, List.forall_mem_cons.2 ⟨subd9_1_494, List.forall_mem_cons.2 ⟨subd9_1_495, List.forall_mem_cons.2 ⟨subd9_1_496, List.forall_mem_cons.2 ⟨subd9_1_497, List.forall_mem_cons.2 ⟨subd9_1_498, List.forall_mem_cons.2 ⟨subd9_1_499, List.forall_mem_cons.2 ⟨subd9_1_500, List.forall_mem_cons.2 ⟨subd9_1_501, List.forall_mem_cons.2 ⟨subd9_1_502, List.forall_mem_cons.2 ⟨subd9_1_503, List.forall_mem_cons.2 ⟨subd9_1_504, List.forall_mem_cons.2 ⟨subd9_1_505, List.forall_mem_cons.2 ⟨subd9_1_506, List.forall_mem_cons.2 ⟨subd9_1_507, List.forall_mem_cons.2 ⟨subd9_1_508, List.forall_mem_cons.2 ⟨subd9_1_509, List.forall_mem_cons.2 ⟨subd9_1_510, List.forall_mem_cons.2 ⟨subd9_1_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_512 : subd9_1 [-6, -7, 3] = true := by decide +kernel
theorem subd9_1_513 : subd9_1 [-6, -7, 4] = true := by decide +kernel
theorem subd9_1_514 : subd9_1 [-6, -6, -11] = true := by decide +kernel
theorem subd9_1_515 : subd9_1 [-6, -6, -10] = true := by decide +kernel
theorem subd9_1_516 : subd9_1 [-6, -6, -9] = true := by decide +kernel
theorem subd9_1_517 : subd9_1 [-6, -6, -8] = true := by decide +kernel
theorem subd9_1_518 : subd9_1 [-6, -6, -7] = true := by decide +kernel
theorem subd9_1_519 : subd9_1 [-6, -6, -6] = true := by decide +kernel
theorem subd9_1_520 : subd9_1 [-6, -6, -5] = true := by decide +kernel
theorem subd9_1_521 : subd9_1 [-6, -6, -4] = true := by decide +kernel
theorem subd9_1_522 : subd9_1 [-6, -6, -3] = true := by decide +kernel
theorem subd9_1_523 : subd9_1 [-6, -6, -2] = true := by decide +kernel
theorem subd9_1_524 : subd9_1 [-6, -6, -1] = true := by decide +kernel
theorem subd9_1_525 : subd9_1 [-6, -6, 0] = true := by decide +kernel
theorem subd9_1_526 : subd9_1 [-6, -6, 1] = true := by decide +kernel
theorem subd9_1_527 : subd9_1 [-6, -6, 2] = true := by decide +kernel
theorem subd9_1_528 : subd9_1 [-6, -6, 3] = true := by decide +kernel
theorem subd9_1_529 : subd9_1 [-6, -6, 4] = true := by decide +kernel
theorem subd9_1_530 : subd9_1 [-6, -6, 5] = true := by decide +kernel
theorem subd9_1_531 : subd9_1 [-6, -5, -11] = true := by decide +kernel
theorem subd9_1_532 : subd9_1 [-6, -5, -10] = true := by decide +kernel
theorem subd9_1_533 : subd9_1 [-6, -5, -9] = true := by decide +kernel
theorem subd9_1_534 : subd9_1 [-6, -5, -8] = true := by decide +kernel
theorem subd9_1_535 : subd9_1 [-6, -5, -7] = true := by decide +kernel
theorem subd9_1_536 : subd9_1 [-6, -5, -6] = true := by decide +kernel
theorem subd9_1_537 : subd9_1 [-6, -5, -5] = true := by decide +kernel
theorem subd9_1_538 : subd9_1 [-6, -5, -4] = true := by decide +kernel
theorem subd9_1_539 : subd9_1 [-6, -5, -3] = true := by decide +kernel
theorem subd9_1_540 : subd9_1 [-6, -5, -2] = true := by decide +kernel
theorem subd9_1_541 : subd9_1 [-6, -5, -1] = true := by decide +kernel
theorem subd9_1_542 : subd9_1 [-6, -5, 0] = true := by decide +kernel
theorem subd9_1_543 : subd9_1 [-6, -5, 1] = true := by decide +kernel
theorem sbd9_1_16 : ∀ q ∈ blkd9_1_16, subd9_1 q = true := by
  unfold blkd9_1_16
  exact List.forall_mem_cons.2 ⟨subd9_1_512, List.forall_mem_cons.2 ⟨subd9_1_513, List.forall_mem_cons.2 ⟨subd9_1_514, List.forall_mem_cons.2 ⟨subd9_1_515, List.forall_mem_cons.2 ⟨subd9_1_516, List.forall_mem_cons.2 ⟨subd9_1_517, List.forall_mem_cons.2 ⟨subd9_1_518, List.forall_mem_cons.2 ⟨subd9_1_519, List.forall_mem_cons.2 ⟨subd9_1_520, List.forall_mem_cons.2 ⟨subd9_1_521, List.forall_mem_cons.2 ⟨subd9_1_522, List.forall_mem_cons.2 ⟨subd9_1_523, List.forall_mem_cons.2 ⟨subd9_1_524, List.forall_mem_cons.2 ⟨subd9_1_525, List.forall_mem_cons.2 ⟨subd9_1_526, List.forall_mem_cons.2 ⟨subd9_1_527, List.forall_mem_cons.2 ⟨subd9_1_528, List.forall_mem_cons.2 ⟨subd9_1_529, List.forall_mem_cons.2 ⟨subd9_1_530, List.forall_mem_cons.2 ⟨subd9_1_531, List.forall_mem_cons.2 ⟨subd9_1_532, List.forall_mem_cons.2 ⟨subd9_1_533, List.forall_mem_cons.2 ⟨subd9_1_534, List.forall_mem_cons.2 ⟨subd9_1_535, List.forall_mem_cons.2 ⟨subd9_1_536, List.forall_mem_cons.2 ⟨subd9_1_537, List.forall_mem_cons.2 ⟨subd9_1_538, List.forall_mem_cons.2 ⟨subd9_1_539, List.forall_mem_cons.2 ⟨subd9_1_540, List.forall_mem_cons.2 ⟨subd9_1_541, List.forall_mem_cons.2 ⟨subd9_1_542, List.forall_mem_cons.2 ⟨subd9_1_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_544 : subd9_1 [-6, -5, 2] = true := by decide +kernel
theorem subd9_1_545 : subd9_1 [-6, -5, 3] = true := by decide +kernel
theorem subd9_1_546 : subd9_1 [-6, -5, 4] = true := by decide +kernel
theorem subd9_1_547 : subd9_1 [-6, -5, 5] = true := by decide +kernel
theorem subd9_1_548 : subd9_1 [-6, -5, 6] = true := by decide +kernel
theorem subd9_1_549 : subd9_1 [-6, -4, -11] = true := by decide +kernel
theorem subd9_1_550 : subd9_1 [-6, -4, -10] = true := by decide +kernel
theorem subd9_1_551 : subd9_1 [-6, -4, -9] = true := by decide +kernel
theorem subd9_1_552 : subd9_1 [-6, -4, -8] = true := by decide +kernel
theorem subd9_1_553 : subd9_1 [-6, -4, -7] = true := by decide +kernel
theorem subd9_1_554 : subd9_1 [-6, -4, -6] = true := by decide +kernel
theorem subd9_1_555 : subd9_1 [-6, -4, -5] = true := by decide +kernel
theorem subd9_1_556 : subd9_1 [-6, -4, -4] = true := by decide +kernel
theorem subd9_1_557 : subd9_1 [-6, -4, -3] = true := by decide +kernel
theorem subd9_1_558 : subd9_1 [-6, -4, -2] = true := by decide +kernel
theorem subd9_1_559 : subd9_1 [-6, -4, -1] = true := by decide +kernel
theorem subd9_1_560 : subd9_1 [-6, -4, 0] = true := by decide +kernel
theorem subd9_1_561 : subd9_1 [-6, -4, 1] = true := by decide +kernel
theorem subd9_1_562 : subd9_1 [-6, -4, 2] = true := by decide +kernel
theorem subd9_1_563 : subd9_1 [-6, -4, 3] = true := by decide +kernel
theorem subd9_1_564 : subd9_1 [-6, -4, 4] = true := by decide +kernel
theorem subd9_1_565 : subd9_1 [-6, -4, 5] = true := by decide +kernel
theorem subd9_1_566 : subd9_1 [-6, -4, 6] = true := by decide +kernel
theorem subd9_1_567 : subd9_1 [-6, -3, -11] = true := by decide +kernel
theorem subd9_1_568 : subd9_1 [-6, -3, -10] = true := by decide +kernel
theorem subd9_1_569 : subd9_1 [-6, -3, -9] = true := by decide +kernel
theorem subd9_1_570 : subd9_1 [-6, -3, -8] = true := by decide +kernel
theorem subd9_1_571 : subd9_1 [-6, -3, -7] = true := by decide +kernel
theorem subd9_1_572 : subd9_1 [-6, -3, -6] = true := by decide +kernel
theorem subd9_1_573 : subd9_1 [-6, -3, -5] = true := by decide +kernel
theorem subd9_1_574 : subd9_1 [-6, -3, -4] = true := by decide +kernel
theorem subd9_1_575 : subd9_1 [-6, -3, -3] = true := by decide +kernel
theorem sbd9_1_17 : ∀ q ∈ blkd9_1_17, subd9_1 q = true := by
  unfold blkd9_1_17
  exact List.forall_mem_cons.2 ⟨subd9_1_544, List.forall_mem_cons.2 ⟨subd9_1_545, List.forall_mem_cons.2 ⟨subd9_1_546, List.forall_mem_cons.2 ⟨subd9_1_547, List.forall_mem_cons.2 ⟨subd9_1_548, List.forall_mem_cons.2 ⟨subd9_1_549, List.forall_mem_cons.2 ⟨subd9_1_550, List.forall_mem_cons.2 ⟨subd9_1_551, List.forall_mem_cons.2 ⟨subd9_1_552, List.forall_mem_cons.2 ⟨subd9_1_553, List.forall_mem_cons.2 ⟨subd9_1_554, List.forall_mem_cons.2 ⟨subd9_1_555, List.forall_mem_cons.2 ⟨subd9_1_556, List.forall_mem_cons.2 ⟨subd9_1_557, List.forall_mem_cons.2 ⟨subd9_1_558, List.forall_mem_cons.2 ⟨subd9_1_559, List.forall_mem_cons.2 ⟨subd9_1_560, List.forall_mem_cons.2 ⟨subd9_1_561, List.forall_mem_cons.2 ⟨subd9_1_562, List.forall_mem_cons.2 ⟨subd9_1_563, List.forall_mem_cons.2 ⟨subd9_1_564, List.forall_mem_cons.2 ⟨subd9_1_565, List.forall_mem_cons.2 ⟨subd9_1_566, List.forall_mem_cons.2 ⟨subd9_1_567, List.forall_mem_cons.2 ⟨subd9_1_568, List.forall_mem_cons.2 ⟨subd9_1_569, List.forall_mem_cons.2 ⟨subd9_1_570, List.forall_mem_cons.2 ⟨subd9_1_571, List.forall_mem_cons.2 ⟨subd9_1_572, List.forall_mem_cons.2 ⟨subd9_1_573, List.forall_mem_cons.2 ⟨subd9_1_574, List.forall_mem_cons.2 ⟨subd9_1_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_576 : subd9_1 [-6, -3, -2] = true := by decide +kernel
theorem subd9_1_577 : subd9_1 [-6, -3, -1] = true := by decide +kernel
theorem subd9_1_578 : subd9_1 [-6, -3, 0] = true := by decide +kernel
theorem subd9_1_579 : subd9_1 [-6, -3, 1] = true := by decide +kernel
theorem subd9_1_580 : subd9_1 [-6, -3, 2] = true := by decide +kernel
theorem subd9_1_581 : subd9_1 [-6, -3, 3] = true := by decide +kernel
theorem subd9_1_582 : subd9_1 [-6, -3, 4] = true := by decide +kernel
theorem subd9_1_583 : subd9_1 [-6, -3, 5] = true := by decide +kernel
theorem subd9_1_584 : subd9_1 [-6, -3, 6] = true := by decide +kernel
theorem subd9_1_585 : subd9_1 [-6, -3, 7] = true := by decide +kernel
theorem subd9_1_586 : subd9_1 [-6, -2, -10] = true := by decide +kernel
theorem subd9_1_587 : subd9_1 [-6, -2, -9] = true := by decide +kernel
theorem subd9_1_588 : subd9_1 [-6, -2, -8] = true := by decide +kernel
theorem subd9_1_589 : subd9_1 [-6, -2, -7] = true := by decide +kernel
theorem subd9_1_590 : subd9_1 [-6, -2, -6] = true := by decide +kernel
theorem subd9_1_591 : subd9_1 [-6, -2, -5] = true := by decide +kernel
theorem subd9_1_592 : subd9_1 [-6, -2, -4] = true := by decide +kernel
theorem subd9_1_593 : subd9_1 [-6, -2, -3] = true := by decide +kernel
theorem subd9_1_594 : subd9_1 [-6, -2, -2] = true := by decide +kernel
theorem subd9_1_595 : subd9_1 [-6, -2, -1] = true := by decide +kernel
theorem subd9_1_596 : subd9_1 [-6, -2, 0] = true := by decide +kernel
theorem subd9_1_597 : subd9_1 [-6, -2, 1] = true := by decide +kernel
theorem subd9_1_598 : subd9_1 [-6, -2, 2] = true := by decide +kernel
theorem subd9_1_599 : subd9_1 [-6, -2, 3] = true := by decide +kernel
theorem subd9_1_600 : subd9_1 [-6, -2, 4] = true := by decide +kernel
theorem subd9_1_601 : subd9_1 [-6, -2, 5] = true := by decide +kernel
theorem subd9_1_602 : subd9_1 [-6, -2, 6] = true := by decide +kernel
theorem subd9_1_603 : subd9_1 [-6, -2, 7] = true := by decide +kernel
theorem subd9_1_604 : subd9_1 [-6, -1, -10] = true := by decide +kernel
theorem subd9_1_605 : subd9_1 [-6, -1, -9] = true := by decide +kernel
theorem subd9_1_606 : subd9_1 [-6, -1, -8] = true := by decide +kernel
theorem subd9_1_607 : subd9_1 [-6, -1, -7] = true := by decide +kernel
theorem sbd9_1_18 : ∀ q ∈ blkd9_1_18, subd9_1 q = true := by
  unfold blkd9_1_18
  exact List.forall_mem_cons.2 ⟨subd9_1_576, List.forall_mem_cons.2 ⟨subd9_1_577, List.forall_mem_cons.2 ⟨subd9_1_578, List.forall_mem_cons.2 ⟨subd9_1_579, List.forall_mem_cons.2 ⟨subd9_1_580, List.forall_mem_cons.2 ⟨subd9_1_581, List.forall_mem_cons.2 ⟨subd9_1_582, List.forall_mem_cons.2 ⟨subd9_1_583, List.forall_mem_cons.2 ⟨subd9_1_584, List.forall_mem_cons.2 ⟨subd9_1_585, List.forall_mem_cons.2 ⟨subd9_1_586, List.forall_mem_cons.2 ⟨subd9_1_587, List.forall_mem_cons.2 ⟨subd9_1_588, List.forall_mem_cons.2 ⟨subd9_1_589, List.forall_mem_cons.2 ⟨subd9_1_590, List.forall_mem_cons.2 ⟨subd9_1_591, List.forall_mem_cons.2 ⟨subd9_1_592, List.forall_mem_cons.2 ⟨subd9_1_593, List.forall_mem_cons.2 ⟨subd9_1_594, List.forall_mem_cons.2 ⟨subd9_1_595, List.forall_mem_cons.2 ⟨subd9_1_596, List.forall_mem_cons.2 ⟨subd9_1_597, List.forall_mem_cons.2 ⟨subd9_1_598, List.forall_mem_cons.2 ⟨subd9_1_599, List.forall_mem_cons.2 ⟨subd9_1_600, List.forall_mem_cons.2 ⟨subd9_1_601, List.forall_mem_cons.2 ⟨subd9_1_602, List.forall_mem_cons.2 ⟨subd9_1_603, List.forall_mem_cons.2 ⟨subd9_1_604, List.forall_mem_cons.2 ⟨subd9_1_605, List.forall_mem_cons.2 ⟨subd9_1_606, List.forall_mem_cons.2 ⟨subd9_1_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_608 : subd9_1 [-6, -1, -6] = true := by decide +kernel
theorem subd9_1_609 : subd9_1 [-6, -1, -5] = true := by decide +kernel
theorem subd9_1_610 : subd9_1 [-6, -1, -4] = true := by decide +kernel
theorem subd9_1_611 : subd9_1 [-6, -1, -3] = true := by decide +kernel
theorem subd9_1_612 : subd9_1 [-6, -1, -2] = true := by decide +kernel
theorem subd9_1_613 : subd9_1 [-6, -1, -1] = true := by decide +kernel
theorem subd9_1_614 : subd9_1 [-6, -1, 0] = true := by decide +kernel
theorem subd9_1_615 : subd9_1 [-6, -1, 1] = true := by decide +kernel
theorem subd9_1_616 : subd9_1 [-6, -1, 2] = true := by decide +kernel
theorem subd9_1_617 : subd9_1 [-6, -1, 3] = true := by decide +kernel
theorem subd9_1_618 : subd9_1 [-6, -1, 4] = true := by decide +kernel
theorem subd9_1_619 : subd9_1 [-6, -1, 5] = true := by decide +kernel
theorem subd9_1_620 : subd9_1 [-6, -1, 6] = true := by decide +kernel
theorem subd9_1_621 : subd9_1 [-6, -1, 7] = true := by decide +kernel
theorem subd9_1_622 : subd9_1 [-6, -1, 8] = true := by decide +kernel
theorem subd9_1_623 : subd9_1 [-6, 0, -9] = true := by decide +kernel
theorem subd9_1_624 : subd9_1 [-6, 0, -8] = true := by decide +kernel
theorem subd9_1_625 : subd9_1 [-6, 0, -7] = true := by decide +kernel
theorem subd9_1_626 : subd9_1 [-6, 0, -6] = true := by decide +kernel
theorem subd9_1_627 : subd9_1 [-6, 0, -5] = true := by decide +kernel
theorem subd9_1_628 : subd9_1 [-6, 0, -4] = true := by decide +kernel
theorem subd9_1_629 : subd9_1 [-6, 0, -3] = true := by decide +kernel
theorem subd9_1_630 : subd9_1 [-6, 0, -2] = true := by decide +kernel
theorem subd9_1_631 : subd9_1 [-6, 0, -1] = true := by decide +kernel
theorem subd9_1_632 : subd9_1 [-6, 0, 0] = true := by decide +kernel
theorem subd9_1_633 : subd9_1 [-6, 0, 1] = true := by decide +kernel
theorem subd9_1_634 : subd9_1 [-6, 0, 2] = true := by decide +kernel
theorem subd9_1_635 : subd9_1 [-6, 0, 3] = true := by decide +kernel
theorem subd9_1_636 : subd9_1 [-6, 0, 4] = true := by decide +kernel
theorem subd9_1_637 : subd9_1 [-6, 0, 5] = true := by decide +kernel
theorem subd9_1_638 : subd9_1 [-6, 0, 6] = true := by decide +kernel
theorem subd9_1_639 : subd9_1 [-6, 0, 7] = true := by decide +kernel
theorem sbd9_1_19 : ∀ q ∈ blkd9_1_19, subd9_1 q = true := by
  unfold blkd9_1_19
  exact List.forall_mem_cons.2 ⟨subd9_1_608, List.forall_mem_cons.2 ⟨subd9_1_609, List.forall_mem_cons.2 ⟨subd9_1_610, List.forall_mem_cons.2 ⟨subd9_1_611, List.forall_mem_cons.2 ⟨subd9_1_612, List.forall_mem_cons.2 ⟨subd9_1_613, List.forall_mem_cons.2 ⟨subd9_1_614, List.forall_mem_cons.2 ⟨subd9_1_615, List.forall_mem_cons.2 ⟨subd9_1_616, List.forall_mem_cons.2 ⟨subd9_1_617, List.forall_mem_cons.2 ⟨subd9_1_618, List.forall_mem_cons.2 ⟨subd9_1_619, List.forall_mem_cons.2 ⟨subd9_1_620, List.forall_mem_cons.2 ⟨subd9_1_621, List.forall_mem_cons.2 ⟨subd9_1_622, List.forall_mem_cons.2 ⟨subd9_1_623, List.forall_mem_cons.2 ⟨subd9_1_624, List.forall_mem_cons.2 ⟨subd9_1_625, List.forall_mem_cons.2 ⟨subd9_1_626, List.forall_mem_cons.2 ⟨subd9_1_627, List.forall_mem_cons.2 ⟨subd9_1_628, List.forall_mem_cons.2 ⟨subd9_1_629, List.forall_mem_cons.2 ⟨subd9_1_630, List.forall_mem_cons.2 ⟨subd9_1_631, List.forall_mem_cons.2 ⟨subd9_1_632, List.forall_mem_cons.2 ⟨subd9_1_633, List.forall_mem_cons.2 ⟨subd9_1_634, List.forall_mem_cons.2 ⟨subd9_1_635, List.forall_mem_cons.2 ⟨subd9_1_636, List.forall_mem_cons.2 ⟨subd9_1_637, List.forall_mem_cons.2 ⟨subd9_1_638, List.forall_mem_cons.2 ⟨subd9_1_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_640 : subd9_1 [-6, 0, 8] = true := by decide +kernel
theorem subd9_1_641 : subd9_1 [-6, 1, -9] = true := by decide +kernel
theorem subd9_1_642 : subd9_1 [-6, 1, -8] = true := by decide +kernel
theorem subd9_1_643 : subd9_1 [-6, 1, -7] = true := by decide +kernel
theorem subd9_1_644 : subd9_1 [-6, 1, -6] = true := by decide +kernel
theorem subd9_1_645 : subd9_1 [-6, 1, -5] = true := by decide +kernel
theorem subd9_1_646 : subd9_1 [-6, 1, -4] = true := by decide +kernel
theorem subd9_1_647 : subd9_1 [-6, 1, -3] = true := by decide +kernel
theorem subd9_1_648 : subd9_1 [-6, 1, -2] = true := by decide +kernel
theorem subd9_1_649 : subd9_1 [-6, 1, -1] = true := by decide +kernel
theorem subd9_1_650 : subd9_1 [-6, 1, 0] = true := by decide +kernel
theorem subd9_1_651 : subd9_1 [-6, 1, 1] = true := by decide +kernel
theorem subd9_1_652 : subd9_1 [-6, 1, 2] = true := by decide +kernel
theorem subd9_1_653 : subd9_1 [-6, 1, 3] = true := by decide +kernel
theorem subd9_1_654 : subd9_1 [-6, 1, 4] = true := by decide +kernel
theorem subd9_1_655 : subd9_1 [-6, 1, 5] = true := by decide +kernel
theorem subd9_1_656 : subd9_1 [-6, 1, 6] = true := by decide +kernel
theorem subd9_1_657 : subd9_1 [-6, 1, 7] = true := by decide +kernel
theorem subd9_1_658 : subd9_1 [-6, 1, 8] = true := by decide +kernel
theorem subd9_1_659 : subd9_1 [-6, 2, -8] = true := by decide +kernel
theorem subd9_1_660 : subd9_1 [-6, 2, -7] = true := by decide +kernel
theorem subd9_1_661 : subd9_1 [-6, 2, -6] = true := by decide +kernel
theorem subd9_1_662 : subd9_1 [-6, 2, -5] = true := by decide +kernel
theorem subd9_1_663 : subd9_1 [-6, 2, -4] = true := by decide +kernel
theorem subd9_1_664 : subd9_1 [-6, 2, -3] = true := by decide +kernel
theorem subd9_1_665 : subd9_1 [-6, 2, -2] = true := by decide +kernel
theorem subd9_1_666 : subd9_1 [-6, 2, -1] = true := by decide +kernel
theorem subd9_1_667 : subd9_1 [-6, 2, 0] = true := by decide +kernel
theorem subd9_1_668 : subd9_1 [-6, 2, 1] = true := by decide +kernel
theorem subd9_1_669 : subd9_1 [-6, 2, 2] = true := by decide +kernel
theorem subd9_1_670 : subd9_1 [-6, 2, 3] = true := by decide +kernel
theorem subd9_1_671 : subd9_1 [-6, 2, 4] = true := by decide +kernel
theorem sbd9_1_20 : ∀ q ∈ blkd9_1_20, subd9_1 q = true := by
  unfold blkd9_1_20
  exact List.forall_mem_cons.2 ⟨subd9_1_640, List.forall_mem_cons.2 ⟨subd9_1_641, List.forall_mem_cons.2 ⟨subd9_1_642, List.forall_mem_cons.2 ⟨subd9_1_643, List.forall_mem_cons.2 ⟨subd9_1_644, List.forall_mem_cons.2 ⟨subd9_1_645, List.forall_mem_cons.2 ⟨subd9_1_646, List.forall_mem_cons.2 ⟨subd9_1_647, List.forall_mem_cons.2 ⟨subd9_1_648, List.forall_mem_cons.2 ⟨subd9_1_649, List.forall_mem_cons.2 ⟨subd9_1_650, List.forall_mem_cons.2 ⟨subd9_1_651, List.forall_mem_cons.2 ⟨subd9_1_652, List.forall_mem_cons.2 ⟨subd9_1_653, List.forall_mem_cons.2 ⟨subd9_1_654, List.forall_mem_cons.2 ⟨subd9_1_655, List.forall_mem_cons.2 ⟨subd9_1_656, List.forall_mem_cons.2 ⟨subd9_1_657, List.forall_mem_cons.2 ⟨subd9_1_658, List.forall_mem_cons.2 ⟨subd9_1_659, List.forall_mem_cons.2 ⟨subd9_1_660, List.forall_mem_cons.2 ⟨subd9_1_661, List.forall_mem_cons.2 ⟨subd9_1_662, List.forall_mem_cons.2 ⟨subd9_1_663, List.forall_mem_cons.2 ⟨subd9_1_664, List.forall_mem_cons.2 ⟨subd9_1_665, List.forall_mem_cons.2 ⟨subd9_1_666, List.forall_mem_cons.2 ⟨subd9_1_667, List.forall_mem_cons.2 ⟨subd9_1_668, List.forall_mem_cons.2 ⟨subd9_1_669, List.forall_mem_cons.2 ⟨subd9_1_670, List.forall_mem_cons.2 ⟨subd9_1_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_672 : subd9_1 [-6, 2, 5] = true := by decide +kernel
theorem subd9_1_673 : subd9_1 [-6, 2, 6] = true := by decide +kernel
theorem subd9_1_674 : subd9_1 [-6, 2, 7] = true := by decide +kernel
theorem subd9_1_675 : subd9_1 [-6, 2, 8] = true := by decide +kernel
theorem subd9_1_676 : subd9_1 [-6, 2, 9] = true := by decide +kernel
theorem subd9_1_677 : subd9_1 [-6, 3, -7] = true := by decide +kernel
theorem subd9_1_678 : subd9_1 [-6, 3, -6] = true := by decide +kernel
theorem subd9_1_679 : subd9_1 [-6, 3, -5] = true := by decide +kernel
theorem subd9_1_680 : subd9_1 [-6, 3, -4] = true := by decide +kernel
theorem subd9_1_681 : subd9_1 [-6, 3, -3] = true := by decide +kernel
theorem subd9_1_682 : subd9_1 [-6, 3, -2] = true := by decide +kernel
theorem subd9_1_683 : subd9_1 [-6, 3, -1] = true := by decide +kernel
theorem subd9_1_684 : subd9_1 [-6, 3, 0] = true := by decide +kernel
theorem subd9_1_685 : subd9_1 [-6, 3, 1] = true := by decide +kernel
theorem subd9_1_686 : subd9_1 [-6, 3, 2] = true := by decide +kernel
theorem subd9_1_687 : subd9_1 [-6, 3, 3] = true := by decide +kernel
theorem subd9_1_688 : subd9_1 [-6, 3, 4] = true := by decide +kernel
theorem subd9_1_689 : subd9_1 [-6, 3, 5] = true := by decide +kernel
theorem subd9_1_690 : subd9_1 [-6, 3, 6] = true := by decide +kernel
theorem subd9_1_691 : subd9_1 [-6, 3, 7] = true := by decide +kernel
theorem subd9_1_692 : subd9_1 [-6, 3, 8] = true := by decide +kernel
theorem subd9_1_693 : subd9_1 [-6, 3, 9] = true := by decide +kernel
theorem subd9_1_694 : subd9_1 [-6, 4, -6] = true := by decide +kernel
theorem subd9_1_695 : subd9_1 [-6, 4, -5] = true := by decide +kernel
theorem subd9_1_696 : subd9_1 [-6, 4, -4] = true := by decide +kernel
theorem subd9_1_697 : subd9_1 [-6, 4, -3] = true := by decide +kernel
theorem subd9_1_698 : subd9_1 [-6, 4, -2] = true := by decide +kernel
theorem subd9_1_699 : subd9_1 [-6, 4, -1] = true := by decide +kernel
theorem subd9_1_700 : subd9_1 [-6, 4, 0] = true := by decide +kernel
theorem subd9_1_701 : subd9_1 [-6, 4, 1] = true := by decide +kernel
theorem subd9_1_702 : subd9_1 [-6, 4, 2] = true := by decide +kernel
theorem subd9_1_703 : subd9_1 [-6, 4, 3] = true := by decide +kernel
theorem sbd9_1_21 : ∀ q ∈ blkd9_1_21, subd9_1 q = true := by
  unfold blkd9_1_21
  exact List.forall_mem_cons.2 ⟨subd9_1_672, List.forall_mem_cons.2 ⟨subd9_1_673, List.forall_mem_cons.2 ⟨subd9_1_674, List.forall_mem_cons.2 ⟨subd9_1_675, List.forall_mem_cons.2 ⟨subd9_1_676, List.forall_mem_cons.2 ⟨subd9_1_677, List.forall_mem_cons.2 ⟨subd9_1_678, List.forall_mem_cons.2 ⟨subd9_1_679, List.forall_mem_cons.2 ⟨subd9_1_680, List.forall_mem_cons.2 ⟨subd9_1_681, List.forall_mem_cons.2 ⟨subd9_1_682, List.forall_mem_cons.2 ⟨subd9_1_683, List.forall_mem_cons.2 ⟨subd9_1_684, List.forall_mem_cons.2 ⟨subd9_1_685, List.forall_mem_cons.2 ⟨subd9_1_686, List.forall_mem_cons.2 ⟨subd9_1_687, List.forall_mem_cons.2 ⟨subd9_1_688, List.forall_mem_cons.2 ⟨subd9_1_689, List.forall_mem_cons.2 ⟨subd9_1_690, List.forall_mem_cons.2 ⟨subd9_1_691, List.forall_mem_cons.2 ⟨subd9_1_692, List.forall_mem_cons.2 ⟨subd9_1_693, List.forall_mem_cons.2 ⟨subd9_1_694, List.forall_mem_cons.2 ⟨subd9_1_695, List.forall_mem_cons.2 ⟨subd9_1_696, List.forall_mem_cons.2 ⟨subd9_1_697, List.forall_mem_cons.2 ⟨subd9_1_698, List.forall_mem_cons.2 ⟨subd9_1_699, List.forall_mem_cons.2 ⟨subd9_1_700, List.forall_mem_cons.2 ⟨subd9_1_701, List.forall_mem_cons.2 ⟨subd9_1_702, List.forall_mem_cons.2 ⟨subd9_1_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_704 : subd9_1 [-6, 4, 4] = true := by decide +kernel
theorem subd9_1_705 : subd9_1 [-6, 4, 5] = true := by decide +kernel
theorem subd9_1_706 : subd9_1 [-6, 4, 6] = true := by decide +kernel
theorem subd9_1_707 : subd9_1 [-6, 4, 7] = true := by decide +kernel
theorem subd9_1_708 : subd9_1 [-6, 4, 8] = true := by decide +kernel
theorem subd9_1_709 : subd9_1 [-6, 4, 9] = true := by decide +kernel
theorem subd9_1_710 : subd9_1 [-6, 5, -5] = true := by decide +kernel
theorem subd9_1_711 : subd9_1 [-6, 5, -4] = true := by decide +kernel
theorem subd9_1_712 : subd9_1 [-6, 5, -3] = true := by decide +kernel
theorem subd9_1_713 : subd9_1 [-6, 5, -2] = true := by decide +kernel
theorem subd9_1_714 : subd9_1 [-6, 5, -1] = true := by decide +kernel
theorem subd9_1_715 : subd9_1 [-6, 5, 0] = true := by decide +kernel
theorem subd9_1_716 : subd9_1 [-6, 5, 1] = true := by decide +kernel
theorem subd9_1_717 : subd9_1 [-6, 5, 2] = true := by decide +kernel
theorem subd9_1_718 : subd9_1 [-6, 5, 3] = true := by decide +kernel
theorem subd9_1_719 : subd9_1 [-6, 5, 4] = true := by decide +kernel
theorem subd9_1_720 : subd9_1 [-6, 5, 5] = true := by decide +kernel
theorem subd9_1_721 : subd9_1 [-6, 5, 6] = true := by decide +kernel
theorem subd9_1_722 : subd9_1 [-6, 5, 7] = true := by decide +kernel
theorem subd9_1_723 : subd9_1 [-6, 5, 8] = true := by decide +kernel
theorem subd9_1_724 : subd9_1 [-6, 5, 9] = true := by decide +kernel
theorem subd9_1_725 : subd9_1 [-6, 6] = true := by decide +kernel
theorem subd9_1_726 : subd9_1 [-6, 7] = true := by decide +kernel
theorem subd9_1_727 : subd9_1 [-6, 8] = true := by decide +kernel
theorem subd9_1_728 : subd9_1 [-5, -13] = true := by decide +kernel
theorem subd9_1_729 : subd9_1 [-5, -12] = true := by decide +kernel
theorem subd9_1_730 : subd9_1 [-5, -11] = true := by decide +kernel
theorem subd9_1_731 : subd9_1 [-5, -10] = true := by decide +kernel
theorem subd9_1_732 : subd9_1 [-5, -9, -11] = true := by decide +kernel
theorem subd9_1_733 : subd9_1 [-5, -9, -10] = true := by decide +kernel
theorem subd9_1_734 : subd9_1 [-5, -9, -9] = true := by decide +kernel
theorem subd9_1_735 : subd9_1 [-5, -9, -8] = true := by decide +kernel
theorem sbd9_1_22 : ∀ q ∈ blkd9_1_22, subd9_1 q = true := by
  unfold blkd9_1_22
  exact List.forall_mem_cons.2 ⟨subd9_1_704, List.forall_mem_cons.2 ⟨subd9_1_705, List.forall_mem_cons.2 ⟨subd9_1_706, List.forall_mem_cons.2 ⟨subd9_1_707, List.forall_mem_cons.2 ⟨subd9_1_708, List.forall_mem_cons.2 ⟨subd9_1_709, List.forall_mem_cons.2 ⟨subd9_1_710, List.forall_mem_cons.2 ⟨subd9_1_711, List.forall_mem_cons.2 ⟨subd9_1_712, List.forall_mem_cons.2 ⟨subd9_1_713, List.forall_mem_cons.2 ⟨subd9_1_714, List.forall_mem_cons.2 ⟨subd9_1_715, List.forall_mem_cons.2 ⟨subd9_1_716, List.forall_mem_cons.2 ⟨subd9_1_717, List.forall_mem_cons.2 ⟨subd9_1_718, List.forall_mem_cons.2 ⟨subd9_1_719, List.forall_mem_cons.2 ⟨subd9_1_720, List.forall_mem_cons.2 ⟨subd9_1_721, List.forall_mem_cons.2 ⟨subd9_1_722, List.forall_mem_cons.2 ⟨subd9_1_723, List.forall_mem_cons.2 ⟨subd9_1_724, List.forall_mem_cons.2 ⟨subd9_1_725, List.forall_mem_cons.2 ⟨subd9_1_726, List.forall_mem_cons.2 ⟨subd9_1_727, List.forall_mem_cons.2 ⟨subd9_1_728, List.forall_mem_cons.2 ⟨subd9_1_729, List.forall_mem_cons.2 ⟨subd9_1_730, List.forall_mem_cons.2 ⟨subd9_1_731, List.forall_mem_cons.2 ⟨subd9_1_732, List.forall_mem_cons.2 ⟨subd9_1_733, List.forall_mem_cons.2 ⟨subd9_1_734, List.forall_mem_cons.2 ⟨subd9_1_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_736 : subd9_1 [-5, -9, -7] = true := by decide +kernel
theorem subd9_1_737 : subd9_1 [-5, -9, -6] = true := by decide +kernel
theorem subd9_1_738 : subd9_1 [-5, -9, -5] = true := by decide +kernel
theorem subd9_1_739 : subd9_1 [-5, -9, -4] = true := by decide +kernel
theorem subd9_1_740 : subd9_1 [-5, -9, -3] = true := by decide +kernel
theorem subd9_1_741 : subd9_1 [-5, -9, -2] = true := by decide +kernel
theorem subd9_1_742 : subd9_1 [-5, -9, -1] = true := by decide +kernel
theorem subd9_1_743 : subd9_1 [-5, -9, 0] = true := by decide +kernel
theorem subd9_1_744 : subd9_1 [-5, -9, 1] = true := by decide +kernel
theorem subd9_1_745 : subd9_1 [-5, -9, 2] = true := by decide +kernel
theorem subd9_1_746 : subd9_1 [-5, -8, -12] = true := by decide +kernel
theorem subd9_1_747 : subd9_1 [-5, -8, -11] = true := by decide +kernel
theorem subd9_1_748 : subd9_1 [-5, -8, -10] = true := by decide +kernel
theorem subd9_1_749 : subd9_1 [-5, -8, -9] = true := by decide +kernel
theorem subd9_1_750 : subd9_1 [-5, -8, -8] = true := by decide +kernel
theorem subd9_1_751 : subd9_1 [-5, -8, -7] = true := by decide +kernel
theorem subd9_1_752 : subd9_1 [-5, -8, -6] = true := by decide +kernel
theorem subd9_1_753 : subd9_1 [-5, -8, -5] = true := by decide +kernel
theorem subd9_1_754 : subd9_1 [-5, -8, -4] = true := by decide +kernel
theorem subd9_1_755 : subd9_1 [-5, -8, -3] = true := by decide +kernel
theorem subd9_1_756 : subd9_1 [-5, -8, -2] = true := by decide +kernel
theorem subd9_1_757 : subd9_1 [-5, -8, -1] = true := by decide +kernel
theorem subd9_1_758 : subd9_1 [-5, -8, 0] = true := by decide +kernel
theorem subd9_1_759 : subd9_1 [-5, -8, 1] = true := by decide +kernel
theorem subd9_1_760 : subd9_1 [-5, -8, 2] = true := by decide +kernel
theorem subd9_1_761 : subd9_1 [-5, -8, 3] = true := by decide +kernel
theorem subd9_1_762 : subd9_1 [-5, -8, 4] = true := by decide +kernel
theorem subd9_1_763 : subd9_1 [-5, -7, -12] = true := by decide +kernel
theorem subd9_1_764 : subd9_1 [-5, -7, -11] = true := by decide +kernel
theorem subd9_1_765 : subd9_1 [-5, -7, -10] = true := by decide +kernel
theorem subd9_1_766 : subd9_1 [-5, -7, -9] = true := by decide +kernel
theorem subd9_1_767 : subd9_1 [-5, -7, -8] = true := by decide +kernel
theorem sbd9_1_23 : ∀ q ∈ blkd9_1_23, subd9_1 q = true := by
  unfold blkd9_1_23
  exact List.forall_mem_cons.2 ⟨subd9_1_736, List.forall_mem_cons.2 ⟨subd9_1_737, List.forall_mem_cons.2 ⟨subd9_1_738, List.forall_mem_cons.2 ⟨subd9_1_739, List.forall_mem_cons.2 ⟨subd9_1_740, List.forall_mem_cons.2 ⟨subd9_1_741, List.forall_mem_cons.2 ⟨subd9_1_742, List.forall_mem_cons.2 ⟨subd9_1_743, List.forall_mem_cons.2 ⟨subd9_1_744, List.forall_mem_cons.2 ⟨subd9_1_745, List.forall_mem_cons.2 ⟨subd9_1_746, List.forall_mem_cons.2 ⟨subd9_1_747, List.forall_mem_cons.2 ⟨subd9_1_748, List.forall_mem_cons.2 ⟨subd9_1_749, List.forall_mem_cons.2 ⟨subd9_1_750, List.forall_mem_cons.2 ⟨subd9_1_751, List.forall_mem_cons.2 ⟨subd9_1_752, List.forall_mem_cons.2 ⟨subd9_1_753, List.forall_mem_cons.2 ⟨subd9_1_754, List.forall_mem_cons.2 ⟨subd9_1_755, List.forall_mem_cons.2 ⟨subd9_1_756, List.forall_mem_cons.2 ⟨subd9_1_757, List.forall_mem_cons.2 ⟨subd9_1_758, List.forall_mem_cons.2 ⟨subd9_1_759, List.forall_mem_cons.2 ⟨subd9_1_760, List.forall_mem_cons.2 ⟨subd9_1_761, List.forall_mem_cons.2 ⟨subd9_1_762, List.forall_mem_cons.2 ⟨subd9_1_763, List.forall_mem_cons.2 ⟨subd9_1_764, List.forall_mem_cons.2 ⟨subd9_1_765, List.forall_mem_cons.2 ⟨subd9_1_766, List.forall_mem_cons.2 ⟨subd9_1_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_768 : subd9_1 [-5, -7, -7] = true := by decide +kernel
theorem subd9_1_769 : subd9_1 [-5, -7, -6] = true := by decide +kernel
theorem subd9_1_770 : subd9_1 [-5, -7, -5] = true := by decide +kernel
theorem subd9_1_771 : subd9_1 [-5, -7, -4] = true := by decide +kernel
theorem subd9_1_772 : subd9_1 [-5, -7, -3] = true := by decide +kernel
theorem subd9_1_773 : subd9_1 [-5, -7, -2] = true := by decide +kernel
theorem subd9_1_774 : subd9_1 [-5, -7, -1] = true := by decide +kernel
theorem subd9_1_775 : subd9_1 [-5, -7, 0] = true := by decide +kernel
theorem subd9_1_776 : subd9_1 [-5, -7, 1] = true := by decide +kernel
theorem subd9_1_777 : subd9_1 [-5, -7, 2] = true := by decide +kernel
theorem subd9_1_778 : subd9_1 [-5, -7, 3] = true := by decide +kernel
theorem subd9_1_779 : subd9_1 [-5, -7, 4] = true := by decide +kernel
theorem subd9_1_780 : subd9_1 [-5, -7, 5] = true := by decide +kernel
theorem subd9_1_781 : subd9_1 [-5, -6, -12] = true := by decide +kernel
theorem subd9_1_782 : subd9_1 [-5, -6, -11] = true := by decide +kernel
theorem subd9_1_783 : subd9_1 [-5, -6, -10] = true := by decide +kernel
theorem subd9_1_784 : subd9_1 [-5, -6, -9] = true := by decide +kernel
theorem subd9_1_785 : subd9_1 [-5, -6, -8] = true := by decide +kernel
theorem subd9_1_786 : subd9_1 [-5, -6, -7] = true := by decide +kernel
theorem subd9_1_787 : subd9_1 [-5, -6, -6] = true := by decide +kernel
theorem subd9_1_788 : subd9_1 [-5, -6, -5] = true := by decide +kernel
theorem subd9_1_789 : subd9_1 [-5, -6, -4] = true := by decide +kernel
theorem subd9_1_790 : subd9_1 [-5, -6, -3] = true := by decide +kernel
theorem subd9_1_791 : subd9_1 [-5, -6, -2] = true := by decide +kernel
theorem subd9_1_792 : subd9_1 [-5, -6, -1] = true := by decide +kernel
theorem subd9_1_793 : subd9_1 [-5, -6, 0] = true := by decide +kernel
theorem subd9_1_794 : subd9_1 [-5, -6, 1] = true := by decide +kernel
theorem subd9_1_795 : subd9_1 [-5, -6, 2] = true := by decide +kernel
theorem subd9_1_796 : subd9_1 [-5, -6, 3] = true := by decide +kernel
theorem subd9_1_797 : subd9_1 [-5, -6, 4] = true := by decide +kernel
theorem subd9_1_798 : subd9_1 [-5, -6, 5] = true := by decide +kernel
theorem subd9_1_799 : subd9_1 [-5, -5, -12] = true := by decide +kernel
theorem sbd9_1_24 : ∀ q ∈ blkd9_1_24, subd9_1 q = true := by
  unfold blkd9_1_24
  exact List.forall_mem_cons.2 ⟨subd9_1_768, List.forall_mem_cons.2 ⟨subd9_1_769, List.forall_mem_cons.2 ⟨subd9_1_770, List.forall_mem_cons.2 ⟨subd9_1_771, List.forall_mem_cons.2 ⟨subd9_1_772, List.forall_mem_cons.2 ⟨subd9_1_773, List.forall_mem_cons.2 ⟨subd9_1_774, List.forall_mem_cons.2 ⟨subd9_1_775, List.forall_mem_cons.2 ⟨subd9_1_776, List.forall_mem_cons.2 ⟨subd9_1_777, List.forall_mem_cons.2 ⟨subd9_1_778, List.forall_mem_cons.2 ⟨subd9_1_779, List.forall_mem_cons.2 ⟨subd9_1_780, List.forall_mem_cons.2 ⟨subd9_1_781, List.forall_mem_cons.2 ⟨subd9_1_782, List.forall_mem_cons.2 ⟨subd9_1_783, List.forall_mem_cons.2 ⟨subd9_1_784, List.forall_mem_cons.2 ⟨subd9_1_785, List.forall_mem_cons.2 ⟨subd9_1_786, List.forall_mem_cons.2 ⟨subd9_1_787, List.forall_mem_cons.2 ⟨subd9_1_788, List.forall_mem_cons.2 ⟨subd9_1_789, List.forall_mem_cons.2 ⟨subd9_1_790, List.forall_mem_cons.2 ⟨subd9_1_791, List.forall_mem_cons.2 ⟨subd9_1_792, List.forall_mem_cons.2 ⟨subd9_1_793, List.forall_mem_cons.2 ⟨subd9_1_794, List.forall_mem_cons.2 ⟨subd9_1_795, List.forall_mem_cons.2 ⟨subd9_1_796, List.forall_mem_cons.2 ⟨subd9_1_797, List.forall_mem_cons.2 ⟨subd9_1_798, List.forall_mem_cons.2 ⟨subd9_1_799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C116
