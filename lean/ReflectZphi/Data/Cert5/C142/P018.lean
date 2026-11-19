import ReflectZphi.Data.Cert5.C142.Base

namespace ReflectZphi.Data.Cert5.C142

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd11_2_256 : subd11_2 [0, 3] = true := by decide +kernel
theorem subd11_2_257 : subd11_2 [0, 4] = true := by decide +kernel
theorem subd11_2_258 : subd11_2 [0, 5] = true := by decide +kernel
theorem subd11_2_259 : subd11_2 [0, 6] = true := by decide +kernel
theorem subd11_2_260 : subd11_2 [1, -7] = true := by decide +kernel
theorem subd11_2_261 : subd11_2 [1, -6] = true := by decide +kernel
theorem subd11_2_262 : subd11_2 [1, -5] = true := by decide +kernel
theorem subd11_2_263 : subd11_2 [1, -4] = true := by decide +kernel
theorem subd11_2_264 : subd11_2 [1, -3] = true := by decide +kernel
theorem subd11_2_265 : subd11_2 [1, -2, -6] = true := by decide +kernel
theorem subd11_2_266 : subd11_2 [1, -2, -5] = true := by decide +kernel
theorem subd11_2_267 : subd11_2 [1, -2, -4] = true := by decide +kernel
theorem subd11_2_268 : subd11_2 [1, -2, -3] = true := by decide +kernel
theorem subd11_2_269 : subd11_2 [1, -2, -2] = true := by decide +kernel
theorem subd11_2_270 : subd11_2 [1, -2, -1] = true := by decide +kernel
theorem subd11_2_271 : subd11_2 [1, -2, 0] = true := by decide +kernel
theorem subd11_2_272 : subd11_2 [1, -2, 1] = true := by decide +kernel
theorem subd11_2_273 : subd11_2 [1, -2, 2] = true := by decide +kernel
theorem subd11_2_274 : subd11_2 [1, -2, 3] = true := by decide +kernel
theorem subd11_2_275 : subd11_2 [1, -2, 4] = true := by decide +kernel
theorem subd11_2_276 : subd11_2 [1, -2, 5] = true := by decide +kernel
theorem subd11_2_277 : subd11_2 [1, -2, 6] = true := by decide +kernel
theorem subd11_2_278 : subd11_2 [1, -2, 7] = true := by decide +kernel
theorem subd11_2_279 : subd11_2 [1, -1, -7] = true := by decide +kernel
theorem subd11_2_280 : subd11_2 [1, -1, -6] = true := by decide +kernel
theorem subd11_2_281 : subd11_2 [1, -1, -5] = true := by decide +kernel
theorem subd11_2_282 : subd11_2 [1, -1, -4] = true := by decide +kernel
theorem subd11_2_283 : subd11_2 [1, -1, -3] = true := by decide +kernel
theorem subd11_2_284 : subd11_2 [1, -1, -2] = true := by decide +kernel
theorem subd11_2_285 : subd11_2 [1, -1, -1] = true := by decide +kernel
theorem subd11_2_286 : subd11_2 [1, -1, 0] = true := by decide +kernel
theorem subd11_2_287 : subd11_2 [1, -1, 1] = true := by decide +kernel
theorem sbd11_2_8 : ∀ q ∈ blkd11_2_8, subd11_2 q = true := by
  unfold blkd11_2_8
  exact List.forall_mem_cons.2 ⟨subd11_2_256, List.forall_mem_cons.2 ⟨subd11_2_257, List.forall_mem_cons.2 ⟨subd11_2_258, List.forall_mem_cons.2 ⟨subd11_2_259, List.forall_mem_cons.2 ⟨subd11_2_260, List.forall_mem_cons.2 ⟨subd11_2_261, List.forall_mem_cons.2 ⟨subd11_2_262, List.forall_mem_cons.2 ⟨subd11_2_263, List.forall_mem_cons.2 ⟨subd11_2_264, List.forall_mem_cons.2 ⟨subd11_2_265, List.forall_mem_cons.2 ⟨subd11_2_266, List.forall_mem_cons.2 ⟨subd11_2_267, List.forall_mem_cons.2 ⟨subd11_2_268, List.forall_mem_cons.2 ⟨subd11_2_269, List.forall_mem_cons.2 ⟨subd11_2_270, List.forall_mem_cons.2 ⟨subd11_2_271, List.forall_mem_cons.2 ⟨subd11_2_272, List.forall_mem_cons.2 ⟨subd11_2_273, List.forall_mem_cons.2 ⟨subd11_2_274, List.forall_mem_cons.2 ⟨subd11_2_275, List.forall_mem_cons.2 ⟨subd11_2_276, List.forall_mem_cons.2 ⟨subd11_2_277, List.forall_mem_cons.2 ⟨subd11_2_278, List.forall_mem_cons.2 ⟨subd11_2_279, List.forall_mem_cons.2 ⟨subd11_2_280, List.forall_mem_cons.2 ⟨subd11_2_281, List.forall_mem_cons.2 ⟨subd11_2_282, List.forall_mem_cons.2 ⟨subd11_2_283, List.forall_mem_cons.2 ⟨subd11_2_284, List.forall_mem_cons.2 ⟨subd11_2_285, List.forall_mem_cons.2 ⟨subd11_2_286, List.forall_mem_cons.2 ⟨subd11_2_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_2_288 : subd11_2 [1, -1, 2] = true := by decide +kernel
theorem subd11_2_289 : subd11_2 [1, -1, 3] = true := by decide +kernel
theorem subd11_2_290 : subd11_2 [1, -1, 4] = true := by decide +kernel
theorem subd11_2_291 : subd11_2 [1, -1, 5] = true := by decide +kernel
theorem subd11_2_292 : subd11_2 [1, -1, 6] = true := by decide +kernel
theorem subd11_2_293 : subd11_2 [1, -1, 7] = true := by decide +kernel
theorem subd11_2_294 : subd11_2 [1, 0, -8] = true := by decide +kernel
theorem subd11_2_295 : subd11_2 [1, 0, -7] = true := by decide +kernel
theorem subd11_2_296 : subd11_2 [1, 0, -6] = true := by decide +kernel
theorem subd11_2_297 : subd11_2 [1, 0, -5] = true := by decide +kernel
theorem subd11_2_298 : subd11_2 [1, 0, -4] = true := by decide +kernel
theorem subd11_2_299 : subd11_2 [1, 0, -3] = true := by decide +kernel
theorem subd11_2_300 : subd11_2 [1, 0, -2] = true := by decide +kernel
theorem subd11_2_301 : subd11_2 [1, 0, -1] = true := by decide +kernel
theorem subd11_2_302 : subd11_2 [1, 0, 0] = true := by decide +kernel
theorem subd11_2_303 : subd11_2 [1, 0, 1] = true := by decide +kernel
theorem subd11_2_304 : subd11_2 [1, 0, 2] = true := by decide +kernel
theorem subd11_2_305 : subd11_2 [1, 0, 3] = true := by decide +kernel
theorem subd11_2_306 : subd11_2 [1, 0, 4] = true := by decide +kernel
theorem subd11_2_307 : subd11_2 [1, 0, 5] = true := by decide +kernel
theorem subd11_2_308 : subd11_2 [1, 0, 6] = true := by decide +kernel
theorem subd11_2_309 : subd11_2 [1, 1, -8] = true := by decide +kernel
theorem subd11_2_310 : subd11_2 [1, 1, -7] = true := by decide +kernel
theorem subd11_2_311 : subd11_2 [1, 1, -6] = true := by decide +kernel
theorem subd11_2_312 : subd11_2 [1, 1, -5] = true := by decide +kernel
theorem subd11_2_313 : subd11_2 [1, 1, -4] = true := by decide +kernel
theorem subd11_2_314 : subd11_2 [1, 1, -3] = true := by decide +kernel
theorem subd11_2_315 : subd11_2 [1, 1, -2] = true := by decide +kernel
theorem subd11_2_316 : subd11_2 [1, 1, -1] = true := by decide +kernel
theorem subd11_2_317 : subd11_2 [1, 1, 0] = true := by decide +kernel
theorem subd11_2_318 : subd11_2 [1, 1, 1] = true := by decide +kernel
theorem subd11_2_319 : subd11_2 [1, 1, 2] = true := by decide +kernel
theorem sbd11_2_9 : ∀ q ∈ blkd11_2_9, subd11_2 q = true := by
  unfold blkd11_2_9
  exact List.forall_mem_cons.2 ⟨subd11_2_288, List.forall_mem_cons.2 ⟨subd11_2_289, List.forall_mem_cons.2 ⟨subd11_2_290, List.forall_mem_cons.2 ⟨subd11_2_291, List.forall_mem_cons.2 ⟨subd11_2_292, List.forall_mem_cons.2 ⟨subd11_2_293, List.forall_mem_cons.2 ⟨subd11_2_294, List.forall_mem_cons.2 ⟨subd11_2_295, List.forall_mem_cons.2 ⟨subd11_2_296, List.forall_mem_cons.2 ⟨subd11_2_297, List.forall_mem_cons.2 ⟨subd11_2_298, List.forall_mem_cons.2 ⟨subd11_2_299, List.forall_mem_cons.2 ⟨subd11_2_300, List.forall_mem_cons.2 ⟨subd11_2_301, List.forall_mem_cons.2 ⟨subd11_2_302, List.forall_mem_cons.2 ⟨subd11_2_303, List.forall_mem_cons.2 ⟨subd11_2_304, List.forall_mem_cons.2 ⟨subd11_2_305, List.forall_mem_cons.2 ⟨subd11_2_306, List.forall_mem_cons.2 ⟨subd11_2_307, List.forall_mem_cons.2 ⟨subd11_2_308, List.forall_mem_cons.2 ⟨subd11_2_309, List.forall_mem_cons.2 ⟨subd11_2_310, List.forall_mem_cons.2 ⟨subd11_2_311, List.forall_mem_cons.2 ⟨subd11_2_312, List.forall_mem_cons.2 ⟨subd11_2_313, List.forall_mem_cons.2 ⟨subd11_2_314, List.forall_mem_cons.2 ⟨subd11_2_315, List.forall_mem_cons.2 ⟨subd11_2_316, List.forall_mem_cons.2 ⟨subd11_2_317, List.forall_mem_cons.2 ⟨subd11_2_318, List.forall_mem_cons.2 ⟨subd11_2_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_2_320 : subd11_2 [1, 1, 3] = true := by decide +kernel
theorem subd11_2_321 : subd11_2 [1, 1, 4] = true := by decide +kernel
theorem subd11_2_322 : subd11_2 [1, 1, 5] = true := by decide +kernel
theorem subd11_2_323 : subd11_2 [1, 1, 6] = true := by decide +kernel
theorem subd11_2_324 : subd11_2 [1, 2, -8] = true := by decide +kernel
theorem subd11_2_325 : subd11_2 [1, 2, -7] = true := by decide +kernel
theorem subd11_2_326 : subd11_2 [1, 2, -6] = true := by decide +kernel
theorem subd11_2_327 : subd11_2 [1, 2, -5] = true := by decide +kernel
theorem subd11_2_328 : subd11_2 [1, 2, -4] = true := by decide +kernel
theorem subd11_2_329 : subd11_2 [1, 2, -3] = true := by decide +kernel
theorem subd11_2_330 : subd11_2 [1, 2, -2] = true := by decide +kernel
theorem subd11_2_331 : subd11_2 [1, 2, -1] = true := by decide +kernel
theorem subd11_2_332 : subd11_2 [1, 2, 0] = true := by decide +kernel
theorem subd11_2_333 : subd11_2 [1, 2, 1] = true := by decide +kernel
theorem subd11_2_334 : subd11_2 [1, 2, 2] = true := by decide +kernel
theorem subd11_2_335 : subd11_2 [1, 2, 3] = true := by decide +kernel
theorem subd11_2_336 : subd11_2 [1, 2, 4] = true := by decide +kernel
theorem subd11_2_337 : subd11_2 [1, 2, 5] = true := by decide +kernel
theorem subd11_2_338 : subd11_2 [1, 3] = true := by decide +kernel
theorem subd11_2_339 : subd11_2 [1, 4] = true := by decide +kernel
theorem subd11_2_340 : subd11_2 [1, 5] = true := by decide +kernel
theorem subd11_2_341 : subd11_2 [1, 6] = true := by decide +kernel
theorem subd11_2_342 : subd11_2 [2, -6] = true := by decide +kernel
theorem subd11_2_343 : subd11_2 [2, -5] = true := by decide +kernel
theorem subd11_2_344 : subd11_2 [2, -4] = true := by decide +kernel
theorem subd11_2_345 : subd11_2 [2, -3] = true := by decide +kernel
theorem subd11_2_346 : subd11_2 [2, -2] = true := by decide +kernel
theorem subd11_2_347 : subd11_2 [2, -1] = true := by decide +kernel
theorem subd11_2_348 : subd11_2 [2, 0, -8] = true := by decide +kernel
theorem subd11_2_349 : subd11_2 [2, 0, -7] = true := by decide +kernel
theorem subd11_2_350 : subd11_2 [2, 0, -6] = true := by decide +kernel
theorem subd11_2_351 : subd11_2 [2, 0, -5] = true := by decide +kernel
theorem sbd11_2_10 : ∀ q ∈ blkd11_2_10, subd11_2 q = true := by
  unfold blkd11_2_10
  exact List.forall_mem_cons.2 ⟨subd11_2_320, List.forall_mem_cons.2 ⟨subd11_2_321, List.forall_mem_cons.2 ⟨subd11_2_322, List.forall_mem_cons.2 ⟨subd11_2_323, List.forall_mem_cons.2 ⟨subd11_2_324, List.forall_mem_cons.2 ⟨subd11_2_325, List.forall_mem_cons.2 ⟨subd11_2_326, List.forall_mem_cons.2 ⟨subd11_2_327, List.forall_mem_cons.2 ⟨subd11_2_328, List.forall_mem_cons.2 ⟨subd11_2_329, List.forall_mem_cons.2 ⟨subd11_2_330, List.forall_mem_cons.2 ⟨subd11_2_331, List.forall_mem_cons.2 ⟨subd11_2_332, List.forall_mem_cons.2 ⟨subd11_2_333, List.forall_mem_cons.2 ⟨subd11_2_334, List.forall_mem_cons.2 ⟨subd11_2_335, List.forall_mem_cons.2 ⟨subd11_2_336, List.forall_mem_cons.2 ⟨subd11_2_337, List.forall_mem_cons.2 ⟨subd11_2_338, List.forall_mem_cons.2 ⟨subd11_2_339, List.forall_mem_cons.2 ⟨subd11_2_340, List.forall_mem_cons.2 ⟨subd11_2_341, List.forall_mem_cons.2 ⟨subd11_2_342, List.forall_mem_cons.2 ⟨subd11_2_343, List.forall_mem_cons.2 ⟨subd11_2_344, List.forall_mem_cons.2 ⟨subd11_2_345, List.forall_mem_cons.2 ⟨subd11_2_346, List.forall_mem_cons.2 ⟨subd11_2_347, List.forall_mem_cons.2 ⟨subd11_2_348, List.forall_mem_cons.2 ⟨subd11_2_349, List.forall_mem_cons.2 ⟨subd11_2_350, List.forall_mem_cons.2 ⟨subd11_2_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_2_352 : subd11_2 [2, 0, -4] = true := by decide +kernel
theorem subd11_2_353 : subd11_2 [2, 0, -3] = true := by decide +kernel
theorem subd11_2_354 : subd11_2 [2, 0, -2] = true := by decide +kernel
theorem subd11_2_355 : subd11_2 [2, 0, -1] = true := by decide +kernel
theorem subd11_2_356 : subd11_2 [2, 0, 0] = true := by decide +kernel
theorem subd11_2_357 : subd11_2 [2, 0, 1] = true := by decide +kernel
theorem subd11_2_358 : subd11_2 [2, 0, 2] = true := by decide +kernel
theorem subd11_2_359 : subd11_2 [2, 0, 3] = true := by decide +kernel
theorem subd11_2_360 : subd11_2 [2, 0, 4] = true := by decide +kernel
theorem subd11_2_361 : subd11_2 [2, 0, 5] = true := by decide +kernel
theorem subd11_2_362 : subd11_2 [2, 0, 6] = true := by decide +kernel
theorem subd11_2_363 : subd11_2 [2, 1, -8] = true := by decide +kernel
theorem subd11_2_364 : subd11_2 [2, 1, -7] = true := by decide +kernel
theorem subd11_2_365 : subd11_2 [2, 1, -6] = true := by decide +kernel
theorem subd11_2_366 : subd11_2 [2, 1, -5] = true := by decide +kernel
theorem subd11_2_367 : subd11_2 [2, 1, -4] = true := by decide +kernel
theorem subd11_2_368 : subd11_2 [2, 1, -3] = true := by decide +kernel
theorem subd11_2_369 : subd11_2 [2, 1, -2] = true := by decide +kernel
theorem subd11_2_370 : subd11_2 [2, 1, -1] = true := by decide +kernel
theorem subd11_2_371 : subd11_2 [2, 1, 0] = true := by decide +kernel
theorem subd11_2_372 : subd11_2 [2, 1, 1] = true := by decide +kernel
theorem subd11_2_373 : subd11_2 [2, 1, 2] = true := by decide +kernel
theorem subd11_2_374 : subd11_2 [2, 1, 3] = true := by decide +kernel
theorem subd11_2_375 : subd11_2 [2, 1, 4] = true := by decide +kernel
theorem subd11_2_376 : subd11_2 [2, 1, 5] = true := by decide +kernel
theorem subd11_2_377 : subd11_2 [2, 2, -8] = true := by decide +kernel
theorem subd11_2_378 : subd11_2 [2, 2, -7] = true := by decide +kernel
theorem subd11_2_379 : subd11_2 [2, 2, -6] = true := by decide +kernel
theorem subd11_2_380 : subd11_2 [2, 2, -5] = true := by decide +kernel
theorem subd11_2_381 : subd11_2 [2, 2, -4] = true := by decide +kernel
theorem subd11_2_382 : subd11_2 [2, 2, -3] = true := by decide +kernel
theorem subd11_2_383 : subd11_2 [2, 2, -2] = true := by decide +kernel
theorem sbd11_2_11 : ∀ q ∈ blkd11_2_11, subd11_2 q = true := by
  unfold blkd11_2_11
  exact List.forall_mem_cons.2 ⟨subd11_2_352, List.forall_mem_cons.2 ⟨subd11_2_353, List.forall_mem_cons.2 ⟨subd11_2_354, List.forall_mem_cons.2 ⟨subd11_2_355, List.forall_mem_cons.2 ⟨subd11_2_356, List.forall_mem_cons.2 ⟨subd11_2_357, List.forall_mem_cons.2 ⟨subd11_2_358, List.forall_mem_cons.2 ⟨subd11_2_359, List.forall_mem_cons.2 ⟨subd11_2_360, List.forall_mem_cons.2 ⟨subd11_2_361, List.forall_mem_cons.2 ⟨subd11_2_362, List.forall_mem_cons.2 ⟨subd11_2_363, List.forall_mem_cons.2 ⟨subd11_2_364, List.forall_mem_cons.2 ⟨subd11_2_365, List.forall_mem_cons.2 ⟨subd11_2_366, List.forall_mem_cons.2 ⟨subd11_2_367, List.forall_mem_cons.2 ⟨subd11_2_368, List.forall_mem_cons.2 ⟨subd11_2_369, List.forall_mem_cons.2 ⟨subd11_2_370, List.forall_mem_cons.2 ⟨subd11_2_371, List.forall_mem_cons.2 ⟨subd11_2_372, List.forall_mem_cons.2 ⟨subd11_2_373, List.forall_mem_cons.2 ⟨subd11_2_374, List.forall_mem_cons.2 ⟨subd11_2_375, List.forall_mem_cons.2 ⟨subd11_2_376, List.forall_mem_cons.2 ⟨subd11_2_377, List.forall_mem_cons.2 ⟨subd11_2_378, List.forall_mem_cons.2 ⟨subd11_2_379, List.forall_mem_cons.2 ⟨subd11_2_380, List.forall_mem_cons.2 ⟨subd11_2_381, List.forall_mem_cons.2 ⟨subd11_2_382, List.forall_mem_cons.2 ⟨subd11_2_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_2_384 : subd11_2 [2, 2, -1] = true := by decide +kernel
theorem subd11_2_385 : subd11_2 [2, 2, 0] = true := by decide +kernel
theorem subd11_2_386 : subd11_2 [2, 2, 1] = true := by decide +kernel
theorem subd11_2_387 : subd11_2 [2, 2, 2] = true := by decide +kernel
theorem subd11_2_388 : subd11_2 [2, 2, 3] = true := by decide +kernel
theorem subd11_2_389 : subd11_2 [2, 2, 4] = true := by decide +kernel
theorem subd11_2_390 : subd11_2 [2, 2, 5] = true := by decide +kernel
theorem subd11_2_391 : subd11_2 [2, 3] = true := by decide +kernel
theorem subd11_2_392 : subd11_2 [2, 4] = true := by decide +kernel
theorem subd11_2_393 : subd11_2 [2, 5] = true := by decide +kernel
theorem subd11_2_394 : subd11_2 [2, 6] = true := by decide +kernel
theorem subd11_2_395 : subd11_2 [3, -6] = true := by decide +kernel
theorem subd11_2_396 : subd11_2 [3, -5] = true := by decide +kernel
theorem subd11_2_397 : subd11_2 [3, -4] = true := by decide +kernel
theorem subd11_2_398 : subd11_2 [3, -3] = true := by decide +kernel
theorem subd11_2_399 : subd11_2 [3, -2] = true := by decide +kernel
theorem subd11_2_400 : subd11_2 [3, -1] = true := by decide +kernel
theorem subd11_2_401 : subd11_2 [3, 0] = true := by decide +kernel
theorem subd11_2_402 : subd11_2 [3, 1] = true := by decide +kernel
theorem subd11_2_403 : subd11_2 [3, 2] = true := by decide +kernel
theorem subd11_2_404 : subd11_2 [3, 3] = true := by decide +kernel
theorem subd11_2_405 : subd11_2 [3, 4] = true := by decide +kernel
theorem subd11_2_406 : subd11_2 [3, 5] = true := by decide +kernel
theorem subd11_2_407 : subd11_2 [3, 6] = true := by decide +kernel
theorem subd11_2_408 : subd11_2 [4, -5] = true := by decide +kernel
theorem subd11_2_409 : subd11_2 [4, -4] = true := by decide +kernel
theorem subd11_2_410 : subd11_2 [4, -3] = true := by decide +kernel
theorem subd11_2_411 : subd11_2 [4, -2] = true := by decide +kernel
theorem subd11_2_412 : subd11_2 [4, -1] = true := by decide +kernel
theorem subd11_2_413 : subd11_2 [4, 0] = true := by decide +kernel
theorem subd11_2_414 : subd11_2 [4, 1] = true := by decide +kernel
theorem subd11_2_415 : subd11_2 [4, 2] = true := by decide +kernel
theorem sbd11_2_12 : ∀ q ∈ blkd11_2_12, subd11_2 q = true := by
  unfold blkd11_2_12
  exact List.forall_mem_cons.2 ⟨subd11_2_384, List.forall_mem_cons.2 ⟨subd11_2_385, List.forall_mem_cons.2 ⟨subd11_2_386, List.forall_mem_cons.2 ⟨subd11_2_387, List.forall_mem_cons.2 ⟨subd11_2_388, List.forall_mem_cons.2 ⟨subd11_2_389, List.forall_mem_cons.2 ⟨subd11_2_390, List.forall_mem_cons.2 ⟨subd11_2_391, List.forall_mem_cons.2 ⟨subd11_2_392, List.forall_mem_cons.2 ⟨subd11_2_393, List.forall_mem_cons.2 ⟨subd11_2_394, List.forall_mem_cons.2 ⟨subd11_2_395, List.forall_mem_cons.2 ⟨subd11_2_396, List.forall_mem_cons.2 ⟨subd11_2_397, List.forall_mem_cons.2 ⟨subd11_2_398, List.forall_mem_cons.2 ⟨subd11_2_399, List.forall_mem_cons.2 ⟨subd11_2_400, List.forall_mem_cons.2 ⟨subd11_2_401, List.forall_mem_cons.2 ⟨subd11_2_402, List.forall_mem_cons.2 ⟨subd11_2_403, List.forall_mem_cons.2 ⟨subd11_2_404, List.forall_mem_cons.2 ⟨subd11_2_405, List.forall_mem_cons.2 ⟨subd11_2_406, List.forall_mem_cons.2 ⟨subd11_2_407, List.forall_mem_cons.2 ⟨subd11_2_408, List.forall_mem_cons.2 ⟨subd11_2_409, List.forall_mem_cons.2 ⟨subd11_2_410, List.forall_mem_cons.2 ⟨subd11_2_411, List.forall_mem_cons.2 ⟨subd11_2_412, List.forall_mem_cons.2 ⟨subd11_2_413, List.forall_mem_cons.2 ⟨subd11_2_414, List.forall_mem_cons.2 ⟨subd11_2_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_2_416 : subd11_2 [4, 3] = true := by decide +kernel
theorem subd11_2_417 : subd11_2 [4, 4] = true := by decide +kernel
theorem subd11_2_418 : subd11_2 [4, 5] = true := by decide +kernel
theorem subd11_2_419 : subd11_2 [4, 6] = true := by decide +kernel
theorem subd11_2_420 : subd11_2 [5, -4] = true := by decide +kernel
theorem subd11_2_421 : subd11_2 [5, -3] = true := by decide +kernel
theorem subd11_2_422 : subd11_2 [5, -2] = true := by decide +kernel
theorem subd11_2_423 : subd11_2 [5, -1] = true := by decide +kernel
theorem subd11_2_424 : subd11_2 [5, 0] = true := by decide +kernel
theorem subd11_2_425 : subd11_2 [5, 1] = true := by decide +kernel
theorem subd11_2_426 : subd11_2 [5, 2] = true := by decide +kernel
theorem subd11_2_427 : subd11_2 [5, 3] = true := by decide +kernel
theorem subd11_2_428 : subd11_2 [5, 4] = true := by decide +kernel
theorem subd11_2_429 : subd11_2 [5, 5] = true := by decide +kernel
theorem subd11_2_430 : subd11_2 [6, -2] = true := by decide +kernel
theorem subd11_2_431 : subd11_2 [6, -1] = true := by decide +kernel
theorem subd11_2_432 : subd11_2 [6, 0] = true := by decide +kernel
theorem subd11_2_433 : subd11_2 [6, 1] = true := by decide +kernel
theorem subd11_2_434 : subd11_2 [6, 2] = true := by decide +kernel
theorem subd11_2_435 : subd11_2 [6, 3] = true := by decide +kernel
theorem subd11_2_436 : subd11_2 [6, 4] = true := by decide +kernel
theorem sbd11_2_13 : ∀ q ∈ blkd11_2_13, subd11_2 q = true := by
  unfold blkd11_2_13
  exact List.forall_mem_cons.2 ⟨subd11_2_416, List.forall_mem_cons.2 ⟨subd11_2_417, List.forall_mem_cons.2 ⟨subd11_2_418, List.forall_mem_cons.2 ⟨subd11_2_419, List.forall_mem_cons.2 ⟨subd11_2_420, List.forall_mem_cons.2 ⟨subd11_2_421, List.forall_mem_cons.2 ⟨subd11_2_422, List.forall_mem_cons.2 ⟨subd11_2_423, List.forall_mem_cons.2 ⟨subd11_2_424, List.forall_mem_cons.2 ⟨subd11_2_425, List.forall_mem_cons.2 ⟨subd11_2_426, List.forall_mem_cons.2 ⟨subd11_2_427, List.forall_mem_cons.2 ⟨subd11_2_428, List.forall_mem_cons.2 ⟨subd11_2_429, List.forall_mem_cons.2 ⟨subd11_2_430, List.forall_mem_cons.2 ⟨subd11_2_431, List.forall_mem_cons.2 ⟨subd11_2_432, List.forall_mem_cons.2 ⟨subd11_2_433, List.forall_mem_cons.2 ⟨subd11_2_434, List.forall_mem_cons.2 ⟨subd11_2_435, List.forall_mem_cons.2 ⟨subd11_2_436, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_3 : ldCheck G d11_3.U d11_3.ms ldd11_3 = true := by decide +kernel
theorem pre_okd11_3 : subPre G cell11 d11_3 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C142
