import ReflectZphi.Data.Cert5.C105.Base

namespace ReflectZphi.Data.Cert5.C105
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub8_256 : sub8 [1, 0, 1] = true := by decide +kernel
theorem sub8_257 : sub8 [1, 0, 2] = true := by decide +kernel
theorem sub8_258 : sub8 [1, 0, 3] = true := by decide +kernel
theorem sub8_259 : sub8 [1, 0, 4] = true := by decide +kernel
theorem sub8_260 : sub8 [1, 0, 5] = true := by decide +kernel
theorem sub8_261 : sub8 [1, 0, 6] = true := by decide +kernel
theorem sub8_262 : sub8 [1, 1, -7] = true := by decide +kernel
theorem sub8_263 : sub8 [1, 1, -6] = true := by decide +kernel
theorem sub8_264 : sub8 [1, 1, -5] = true := by decide +kernel
theorem sub8_265 : sub8 [1, 1, -4] = true := by decide +kernel
theorem sub8_266 : sub8 [1, 1, -3] = true := by decide +kernel
theorem sub8_267 : sub8 [1, 1, -2] = true := by decide +kernel
theorem sub8_268 : sub8 [1, 1, -1] = true := by decide +kernel
theorem sub8_269 : sub8 [1, 1, 0] = true := by decide +kernel
theorem sub8_270 : sub8 [1, 1, 1] = true := by decide +kernel
theorem sub8_271 : sub8 [1, 1, 2] = true := by decide +kernel
theorem sub8_272 : sub8 [1, 1, 3] = true := by decide +kernel
theorem sub8_273 : sub8 [1, 1, 4] = true := by decide +kernel
theorem sub8_274 : sub8 [1, 1, 5] = true := by decide +kernel
theorem sub8_275 : sub8 [1, 1, 6] = true := by decide +kernel
theorem sub8_276 : sub8 [1, 2, -7] = true := by decide +kernel
theorem sub8_277 : sub8 [1, 2, -6] = true := by decide +kernel
theorem sub8_278 : sub8 [1, 2, -5] = true := by decide +kernel
theorem sub8_279 : sub8 [1, 2, -4] = true := by decide +kernel
theorem sub8_280 : sub8 [1, 2, -3] = true := by decide +kernel
theorem sub8_281 : sub8 [1, 2, -2] = true := by decide +kernel
theorem sub8_282 : sub8 [1, 2, -1] = true := by decide +kernel
theorem sub8_283 : sub8 [1, 2, 0] = true := by decide +kernel
theorem sub8_284 : sub8 [1, 2, 1] = true := by decide +kernel
theorem sub8_285 : sub8 [1, 2, 2] = true := by decide +kernel
theorem sub8_286 : sub8 [1, 2, 3] = true := by decide +kernel
theorem sub8_287 : sub8 [1, 2, 4] = true := by decide +kernel
theorem sb8_8 : ∀ q ∈ blk8_8, sub8 q = true := by
  unfold blk8_8
  exact List.forall_mem_cons.2 ⟨sub8_256, List.forall_mem_cons.2 ⟨sub8_257, List.forall_mem_cons.2 ⟨sub8_258, List.forall_mem_cons.2 ⟨sub8_259, List.forall_mem_cons.2 ⟨sub8_260, List.forall_mem_cons.2 ⟨sub8_261, List.forall_mem_cons.2 ⟨sub8_262, List.forall_mem_cons.2 ⟨sub8_263, List.forall_mem_cons.2 ⟨sub8_264, List.forall_mem_cons.2 ⟨sub8_265, List.forall_mem_cons.2 ⟨sub8_266, List.forall_mem_cons.2 ⟨sub8_267, List.forall_mem_cons.2 ⟨sub8_268, List.forall_mem_cons.2 ⟨sub8_269, List.forall_mem_cons.2 ⟨sub8_270, List.forall_mem_cons.2 ⟨sub8_271, List.forall_mem_cons.2 ⟨sub8_272, List.forall_mem_cons.2 ⟨sub8_273, List.forall_mem_cons.2 ⟨sub8_274, List.forall_mem_cons.2 ⟨sub8_275, List.forall_mem_cons.2 ⟨sub8_276, List.forall_mem_cons.2 ⟨sub8_277, List.forall_mem_cons.2 ⟨sub8_278, List.forall_mem_cons.2 ⟨sub8_279, List.forall_mem_cons.2 ⟨sub8_280, List.forall_mem_cons.2 ⟨sub8_281, List.forall_mem_cons.2 ⟨sub8_282, List.forall_mem_cons.2 ⟨sub8_283, List.forall_mem_cons.2 ⟨sub8_284, List.forall_mem_cons.2 ⟨sub8_285, List.forall_mem_cons.2 ⟨sub8_286, List.forall_mem_cons.2 ⟨sub8_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_288 : sub8 [1, 2, 5] = true := by decide +kernel
theorem sub8_289 : sub8 [1, 2, 6] = true := by decide +kernel
theorem sub8_290 : sub8 [1, 3] = true := by decide +kernel
theorem sub8_291 : sub8 [1, 4] = true := by decide +kernel
theorem sub8_292 : sub8 [1, 5] = true := by decide +kernel
theorem sub8_293 : sub8 [1, 6] = true := by decide +kernel
theorem sub8_294 : sub8 [2, -6] = true := by decide +kernel
theorem sub8_295 : sub8 [2, -5] = true := by decide +kernel
theorem sub8_296 : sub8 [2, -4] = true := by decide +kernel
theorem sub8_297 : sub8 [2, -3] = true := by decide +kernel
theorem sub8_298 : sub8 [2, -2] = true := by decide +kernel
theorem sub8_299 : sub8 [2, -1] = true := by decide +kernel
theorem sub8_300 : sub8 [2, 0, -7] = true := by decide +kernel
theorem sub8_301 : sub8 [2, 0, -6] = true := by decide +kernel
theorem sub8_302 : sub8 [2, 0, -5] = true := by decide +kernel
theorem sub8_303 : sub8 [2, 0, -4] = true := by decide +kernel
theorem sub8_304 : sub8 [2, 0, -3] = true := by decide +kernel
theorem sub8_305 : sub8 [2, 0, -2] = true := by decide +kernel
theorem sub8_306 : sub8 [2, 0, -1] = true := by decide +kernel
theorem sub8_307 : sub8 [2, 0, 0] = true := by decide +kernel
theorem sub8_308 : sub8 [2, 0, 1] = true := by decide +kernel
theorem sub8_309 : sub8 [2, 0, 2] = true := by decide +kernel
theorem sub8_310 : sub8 [2, 0, 3] = true := by decide +kernel
theorem sub8_311 : sub8 [2, 0, 4] = true := by decide +kernel
theorem sub8_312 : sub8 [2, 0, 5] = true := by decide +kernel
theorem sub8_313 : sub8 [2, 1, -7] = true := by decide +kernel
theorem sub8_314 : sub8 [2, 1, -6] = true := by decide +kernel
theorem sub8_315 : sub8 [2, 1, -5] = true := by decide +kernel
theorem sub8_316 : sub8 [2, 1, -4] = true := by decide +kernel
theorem sub8_317 : sub8 [2, 1, -3] = true := by decide +kernel
theorem sub8_318 : sub8 [2, 1, -2] = true := by decide +kernel
theorem sub8_319 : sub8 [2, 1, -1] = true := by decide +kernel
theorem sb8_9 : ∀ q ∈ blk8_9, sub8 q = true := by
  unfold blk8_9
  exact List.forall_mem_cons.2 ⟨sub8_288, List.forall_mem_cons.2 ⟨sub8_289, List.forall_mem_cons.2 ⟨sub8_290, List.forall_mem_cons.2 ⟨sub8_291, List.forall_mem_cons.2 ⟨sub8_292, List.forall_mem_cons.2 ⟨sub8_293, List.forall_mem_cons.2 ⟨sub8_294, List.forall_mem_cons.2 ⟨sub8_295, List.forall_mem_cons.2 ⟨sub8_296, List.forall_mem_cons.2 ⟨sub8_297, List.forall_mem_cons.2 ⟨sub8_298, List.forall_mem_cons.2 ⟨sub8_299, List.forall_mem_cons.2 ⟨sub8_300, List.forall_mem_cons.2 ⟨sub8_301, List.forall_mem_cons.2 ⟨sub8_302, List.forall_mem_cons.2 ⟨sub8_303, List.forall_mem_cons.2 ⟨sub8_304, List.forall_mem_cons.2 ⟨sub8_305, List.forall_mem_cons.2 ⟨sub8_306, List.forall_mem_cons.2 ⟨sub8_307, List.forall_mem_cons.2 ⟨sub8_308, List.forall_mem_cons.2 ⟨sub8_309, List.forall_mem_cons.2 ⟨sub8_310, List.forall_mem_cons.2 ⟨sub8_311, List.forall_mem_cons.2 ⟨sub8_312, List.forall_mem_cons.2 ⟨sub8_313, List.forall_mem_cons.2 ⟨sub8_314, List.forall_mem_cons.2 ⟨sub8_315, List.forall_mem_cons.2 ⟨sub8_316, List.forall_mem_cons.2 ⟨sub8_317, List.forall_mem_cons.2 ⟨sub8_318, List.forall_mem_cons.2 ⟨sub8_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_320 : sub8 [2, 1, 0] = true := by decide +kernel
theorem sub8_321 : sub8 [2, 1, 1] = true := by decide +kernel
theorem sub8_322 : sub8 [2, 1, 2] = true := by decide +kernel
theorem sub8_323 : sub8 [2, 1, 3] = true := by decide +kernel
theorem sub8_324 : sub8 [2, 1, 4] = true := by decide +kernel
theorem sub8_325 : sub8 [2, 1, 5] = true := by decide +kernel
theorem sub8_326 : sub8 [2, 1, 6] = true := by decide +kernel
theorem sub8_327 : sub8 [2, 2, -7] = true := by decide +kernel
theorem sub8_328 : sub8 [2, 2, -6] = true := by decide +kernel
theorem sub8_329 : sub8 [2, 2, -5] = true := by decide +kernel
theorem sub8_330 : sub8 [2, 2, -4] = true := by decide +kernel
theorem sub8_331 : sub8 [2, 2, -3] = true := by decide +kernel
theorem sub8_332 : sub8 [2, 2, -2] = true := by decide +kernel
theorem sub8_333 : sub8 [2, 2, -1] = true := by decide +kernel
theorem sub8_334 : sub8 [2, 2, 0] = true := by decide +kernel
theorem sub8_335 : sub8 [2, 2, 1] = true := by decide +kernel
theorem sub8_336 : sub8 [2, 2, 2] = true := by decide +kernel
theorem sub8_337 : sub8 [2, 2, 3] = true := by decide +kernel
theorem sub8_338 : sub8 [2, 2, 4] = true := by decide +kernel
theorem sub8_339 : sub8 [2, 2, 5] = true := by decide +kernel
theorem sub8_340 : sub8 [2, 2, 6] = true := by decide +kernel
theorem sub8_341 : sub8 [2, 3] = true := by decide +kernel
theorem sub8_342 : sub8 [2, 4] = true := by decide +kernel
theorem sub8_343 : sub8 [2, 5] = true := by decide +kernel
theorem sub8_344 : sub8 [2, 6] = true := by decide +kernel
theorem sub8_345 : sub8 [3, -5] = true := by decide +kernel
theorem sub8_346 : sub8 [3, -4] = true := by decide +kernel
theorem sub8_347 : sub8 [3, -3] = true := by decide +kernel
theorem sub8_348 : sub8 [3, -2] = true := by decide +kernel
theorem sub8_349 : sub8 [3, -1] = true := by decide +kernel
theorem sub8_350 : sub8 [3, 0] = true := by decide +kernel
theorem sub8_351 : sub8 [3, 1] = true := by decide +kernel
theorem sb8_10 : ∀ q ∈ blk8_10, sub8 q = true := by
  unfold blk8_10
  exact List.forall_mem_cons.2 ⟨sub8_320, List.forall_mem_cons.2 ⟨sub8_321, List.forall_mem_cons.2 ⟨sub8_322, List.forall_mem_cons.2 ⟨sub8_323, List.forall_mem_cons.2 ⟨sub8_324, List.forall_mem_cons.2 ⟨sub8_325, List.forall_mem_cons.2 ⟨sub8_326, List.forall_mem_cons.2 ⟨sub8_327, List.forall_mem_cons.2 ⟨sub8_328, List.forall_mem_cons.2 ⟨sub8_329, List.forall_mem_cons.2 ⟨sub8_330, List.forall_mem_cons.2 ⟨sub8_331, List.forall_mem_cons.2 ⟨sub8_332, List.forall_mem_cons.2 ⟨sub8_333, List.forall_mem_cons.2 ⟨sub8_334, List.forall_mem_cons.2 ⟨sub8_335, List.forall_mem_cons.2 ⟨sub8_336, List.forall_mem_cons.2 ⟨sub8_337, List.forall_mem_cons.2 ⟨sub8_338, List.forall_mem_cons.2 ⟨sub8_339, List.forall_mem_cons.2 ⟨sub8_340, List.forall_mem_cons.2 ⟨sub8_341, List.forall_mem_cons.2 ⟨sub8_342, List.forall_mem_cons.2 ⟨sub8_343, List.forall_mem_cons.2 ⟨sub8_344, List.forall_mem_cons.2 ⟨sub8_345, List.forall_mem_cons.2 ⟨sub8_346, List.forall_mem_cons.2 ⟨sub8_347, List.forall_mem_cons.2 ⟨sub8_348, List.forall_mem_cons.2 ⟨sub8_349, List.forall_mem_cons.2 ⟨sub8_350, List.forall_mem_cons.2 ⟨sub8_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_352 : sub8 [3, 2] = true := by decide +kernel
theorem sub8_353 : sub8 [3, 3] = true := by decide +kernel
theorem sub8_354 : sub8 [3, 4] = true := by decide +kernel
theorem sub8_355 : sub8 [3, 5] = true := by decide +kernel
theorem sub8_356 : sub8 [3, 6] = true := by decide +kernel
theorem sub8_357 : sub8 [4, -5] = true := by decide +kernel
theorem sub8_358 : sub8 [4, -4] = true := by decide +kernel
theorem sub8_359 : sub8 [4, -3] = true := by decide +kernel
theorem sub8_360 : sub8 [4, -2] = true := by decide +kernel
theorem sub8_361 : sub8 [4, -1] = true := by decide +kernel
theorem sub8_362 : sub8 [4, 0] = true := by decide +kernel
theorem sub8_363 : sub8 [4, 1] = true := by decide +kernel
theorem sub8_364 : sub8 [4, 2] = true := by decide +kernel
theorem sub8_365 : sub8 [4, 3] = true := by decide +kernel
theorem sub8_366 : sub8 [4, 4] = true := by decide +kernel
theorem sub8_367 : sub8 [4, 5] = true := by decide +kernel
theorem sub8_368 : sub8 [4, 6] = true := by decide +kernel
theorem sub8_369 : sub8 [5, -3] = true := by decide +kernel
theorem sub8_370 : sub8 [5, -2] = true := by decide +kernel
theorem sub8_371 : sub8 [5, -1] = true := by decide +kernel
theorem sub8_372 : sub8 [5, 0] = true := by decide +kernel
theorem sub8_373 : sub8 [5, 1] = true := by decide +kernel
theorem sub8_374 : sub8 [5, 2] = true := by decide +kernel
theorem sub8_375 : sub8 [5, 3] = true := by decide +kernel
theorem sub8_376 : sub8 [5, 4] = true := by decide +kernel
theorem sub8_377 : sub8 [5, 5] = true := by decide +kernel
theorem sub8_378 : sub8 [6] = true := by decide +kernel
theorem sb8_11 : ∀ q ∈ blk8_11, sub8 q = true := by
  unfold blk8_11
  exact List.forall_mem_cons.2 ⟨sub8_352, List.forall_mem_cons.2 ⟨sub8_353, List.forall_mem_cons.2 ⟨sub8_354, List.forall_mem_cons.2 ⟨sub8_355, List.forall_mem_cons.2 ⟨sub8_356, List.forall_mem_cons.2 ⟨sub8_357, List.forall_mem_cons.2 ⟨sub8_358, List.forall_mem_cons.2 ⟨sub8_359, List.forall_mem_cons.2 ⟨sub8_360, List.forall_mem_cons.2 ⟨sub8_361, List.forall_mem_cons.2 ⟨sub8_362, List.forall_mem_cons.2 ⟨sub8_363, List.forall_mem_cons.2 ⟨sub8_364, List.forall_mem_cons.2 ⟨sub8_365, List.forall_mem_cons.2 ⟨sub8_366, List.forall_mem_cons.2 ⟨sub8_367, List.forall_mem_cons.2 ⟨sub8_368, List.forall_mem_cons.2 ⟨sub8_369, List.forall_mem_cons.2 ⟨sub8_370, List.forall_mem_cons.2 ⟨sub8_371, List.forall_mem_cons.2 ⟨sub8_372, List.forall_mem_cons.2 ⟨sub8_373, List.forall_mem_cons.2 ⟨sub8_374, List.forall_mem_cons.2 ⟨sub8_375, List.forall_mem_cons.2 ⟨sub8_376, List.forall_mem_cons.2 ⟨sub8_377, List.forall_mem_cons.2 ⟨sub8_378, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_0 : sub9 [-5, -3] = true := by decide +kernel
theorem sub9_1 : sub9 [-5, -2] = true := by decide +kernel
theorem sub9_2 : sub9 [-5, -1] = true := by decide +kernel
theorem sub9_3 : sub9 [-5, 0] = true := by decide +kernel
theorem sub9_4 : sub9 [-5, 1] = true := by decide +kernel
theorem sub9_5 : sub9 [-5, 2] = true := by decide +kernel
theorem sub9_6 : sub9 [-4, -4] = true := by decide +kernel
theorem sub9_7 : sub9 [-4, -3] = true := by decide +kernel
theorem sub9_8 : sub9 [-4, -2] = true := by decide +kernel
theorem sub9_9 : sub9 [-4, -1] = true := by decide +kernel
theorem sub9_10 : sub9 [-4, 0, -7] = true := by decide +kernel
theorem sub9_11 : sub9 [-4, 0, -6] = true := by decide +kernel
theorem sub9_12 : sub9 [-4, 0, -5] = true := by decide +kernel
theorem sub9_13 : sub9 [-4, 0, -4] = true := by decide +kernel
theorem sub9_14 : sub9 [-4, 0, -3] = true := by decide +kernel
theorem sub9_15 : sub9 [-4, 0, -2] = true := by decide +kernel
theorem sub9_16 : sub9 [-4, 0, -1] = true := by decide +kernel
theorem sub9_17 : sub9 [-4, 0, 0] = true := by decide +kernel
theorem sub9_18 : sub9 [-4, 0, 1] = true := by decide +kernel
theorem sub9_19 : sub9 [-4, 0, 2] = true := by decide +kernel
theorem sub9_20 : sub9 [-4, 0, 3] = true := by decide +kernel
theorem sub9_21 : sub9 [-4, 0, 4] = true := by decide +kernel
theorem sub9_22 : sub9 [-4, 0, 5] = true := by decide +kernel
theorem sub9_23 : sub9 [-4, 0, 6] = true := by decide +kernel
theorem sub9_24 : sub9 [-4, 1] = true := by decide +kernel
theorem sub9_25 : sub9 [-4, 2] = true := by decide +kernel
theorem sub9_26 : sub9 [-4, 3] = true := by decide +kernel
theorem sub9_27 : sub9 [-3, -5] = true := by decide +kernel
theorem sub9_28 : sub9 [-3, -4] = true := by decide +kernel
theorem sub9_29 : sub9 [-3, -3] = true := by decide +kernel
theorem sub9_30 : sub9 [-3, -2, -8] = true := by decide +kernel
theorem sub9_31 : sub9 [-3, -2, -7] = true := by decide +kernel
theorem sb9_0 : ∀ q ∈ blk9_0, sub9 q = true := by
  unfold blk9_0
  exact List.forall_mem_cons.2 ⟨sub9_0, List.forall_mem_cons.2 ⟨sub9_1, List.forall_mem_cons.2 ⟨sub9_2, List.forall_mem_cons.2 ⟨sub9_3, List.forall_mem_cons.2 ⟨sub9_4, List.forall_mem_cons.2 ⟨sub9_5, List.forall_mem_cons.2 ⟨sub9_6, List.forall_mem_cons.2 ⟨sub9_7, List.forall_mem_cons.2 ⟨sub9_8, List.forall_mem_cons.2 ⟨sub9_9, List.forall_mem_cons.2 ⟨sub9_10, List.forall_mem_cons.2 ⟨sub9_11, List.forall_mem_cons.2 ⟨sub9_12, List.forall_mem_cons.2 ⟨sub9_13, List.forall_mem_cons.2 ⟨sub9_14, List.forall_mem_cons.2 ⟨sub9_15, List.forall_mem_cons.2 ⟨sub9_16, List.forall_mem_cons.2 ⟨sub9_17, List.forall_mem_cons.2 ⟨sub9_18, List.forall_mem_cons.2 ⟨sub9_19, List.forall_mem_cons.2 ⟨sub9_20, List.forall_mem_cons.2 ⟨sub9_21, List.forall_mem_cons.2 ⟨sub9_22, List.forall_mem_cons.2 ⟨sub9_23, List.forall_mem_cons.2 ⟨sub9_24, List.forall_mem_cons.2 ⟨sub9_25, List.forall_mem_cons.2 ⟨sub9_26, List.forall_mem_cons.2 ⟨sub9_27, List.forall_mem_cons.2 ⟨sub9_28, List.forall_mem_cons.2 ⟨sub9_29, List.forall_mem_cons.2 ⟨sub9_30, List.forall_mem_cons.2 ⟨sub9_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_32 : sub9 [-3, -2, -6] = true := by decide +kernel
theorem sub9_33 : sub9 [-3, -2, -5] = true := by decide +kernel
theorem sub9_34 : sub9 [-3, -2, -4] = true := by decide +kernel
theorem sub9_35 : sub9 [-3, -2, -3] = true := by decide +kernel
theorem sub9_36 : sub9 [-3, -2, -2] = true := by decide +kernel
theorem sub9_37 : sub9 [-3, -2, -1] = true := by decide +kernel
theorem sub9_38 : sub9 [-3, -2, 0] = true := by decide +kernel
theorem sub9_39 : sub9 [-3, -2, 1] = true := by decide +kernel
theorem sub9_40 : sub9 [-3, -2, 2] = true := by decide +kernel
theorem sub9_41 : sub9 [-3, -2, 3] = true := by decide +kernel
theorem sub9_42 : sub9 [-3, -2, 4] = true := by decide +kernel
theorem sub9_43 : sub9 [-3, -2, 5] = true := by decide +kernel
theorem sub9_44 : sub9 [-3, -2, 6] = true := by decide +kernel
theorem sub9_45 : sub9 [-3, -2, 7] = true := by decide +kernel
theorem sub9_46 : sub9 [-3, -1, -8] = true := by decide +kernel
theorem sub9_47 : sub9 [-3, -1, -7] = true := by decide +kernel
theorem sub9_48 : sub9 [-3, -1, -6] = true := by decide +kernel
theorem sub9_49 : sub9 [-3, -1, -5] = true := by decide +kernel
theorem sub9_50 : sub9 [-3, -1, -4] = true := by decide +kernel
theorem sub9_51 : sub9 [-3, -1, -3] = true := by decide +kernel
theorem sub9_52 : sub9 [-3, -1, -2] = true := by decide +kernel
theorem sub9_53 : sub9 [-3, -1, -1] = true := by decide +kernel
theorem sub9_54 : sub9 [-3, -1, 0] = true := by decide +kernel
theorem sub9_55 : sub9 [-3, -1, 1] = true := by decide +kernel
theorem sub9_56 : sub9 [-3, -1, 2] = true := by decide +kernel
theorem sub9_57 : sub9 [-3, -1, 3] = true := by decide +kernel
theorem sub9_58 : sub9 [-3, -1, 4] = true := by decide +kernel
theorem sub9_59 : sub9 [-3, -1, 5] = true := by decide +kernel
theorem sub9_60 : sub9 [-3, -1, 6] = true := by decide +kernel
theorem sub9_61 : sub9 [-3, -1, 7] = true := by decide +kernel
theorem sub9_62 : sub9 [-3, 0, -8] = true := by decide +kernel
theorem sub9_63 : sub9 [-3, 0, -7] = true := by decide +kernel
theorem sb9_1 : ∀ q ∈ blk9_1, sub9 q = true := by
  unfold blk9_1
  exact List.forall_mem_cons.2 ⟨sub9_32, List.forall_mem_cons.2 ⟨sub9_33, List.forall_mem_cons.2 ⟨sub9_34, List.forall_mem_cons.2 ⟨sub9_35, List.forall_mem_cons.2 ⟨sub9_36, List.forall_mem_cons.2 ⟨sub9_37, List.forall_mem_cons.2 ⟨sub9_38, List.forall_mem_cons.2 ⟨sub9_39, List.forall_mem_cons.2 ⟨sub9_40, List.forall_mem_cons.2 ⟨sub9_41, List.forall_mem_cons.2 ⟨sub9_42, List.forall_mem_cons.2 ⟨sub9_43, List.forall_mem_cons.2 ⟨sub9_44, List.forall_mem_cons.2 ⟨sub9_45, List.forall_mem_cons.2 ⟨sub9_46, List.forall_mem_cons.2 ⟨sub9_47, List.forall_mem_cons.2 ⟨sub9_48, List.forall_mem_cons.2 ⟨sub9_49, List.forall_mem_cons.2 ⟨sub9_50, List.forall_mem_cons.2 ⟨sub9_51, List.forall_mem_cons.2 ⟨sub9_52, List.forall_mem_cons.2 ⟨sub9_53, List.forall_mem_cons.2 ⟨sub9_54, List.forall_mem_cons.2 ⟨sub9_55, List.forall_mem_cons.2 ⟨sub9_56, List.forall_mem_cons.2 ⟨sub9_57, List.forall_mem_cons.2 ⟨sub9_58, List.forall_mem_cons.2 ⟨sub9_59, List.forall_mem_cons.2 ⟨sub9_60, List.forall_mem_cons.2 ⟨sub9_61, List.forall_mem_cons.2 ⟨sub9_62, List.forall_mem_cons.2 ⟨sub9_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_64 : sub9 [-3, 0, -6] = true := by decide +kernel
theorem sub9_65 : sub9 [-3, 0, -5] = true := by decide +kernel
theorem sub9_66 : sub9 [-3, 0, -4] = true := by decide +kernel
theorem sub9_67 : sub9 [-3, 0, -3] = true := by decide +kernel
theorem sub9_68 : sub9 [-3, 0, -2] = true := by decide +kernel
theorem sub9_69 : sub9 [-3, 0, -1] = true := by decide +kernel
theorem sub9_70 : sub9 [-3, 0, 0] = true := by decide +kernel
theorem sub9_71 : sub9 [-3, 0, 1] = true := by decide +kernel
theorem sub9_72 : sub9 [-3, 0, 2] = true := by decide +kernel
theorem sub9_73 : sub9 [-3, 0, 3] = true := by decide +kernel
theorem sub9_74 : sub9 [-3, 0, 4] = true := by decide +kernel
theorem sub9_75 : sub9 [-3, 0, 5] = true := by decide +kernel
theorem sub9_76 : sub9 [-3, 0, 6] = true := by decide +kernel
theorem sub9_77 : sub9 [-3, 0, 7] = true := by decide +kernel
theorem sub9_78 : sub9 [-3, 0, 8] = true := by decide +kernel
theorem sub9_79 : sub9 [-3, 1, -8] = true := by decide +kernel
theorem sub9_80 : sub9 [-3, 1, -7] = true := by decide +kernel
theorem sub9_81 : sub9 [-3, 1, -6] = true := by decide +kernel
theorem sub9_82 : sub9 [-3, 1, -5] = true := by decide +kernel
theorem sub9_83 : sub9 [-3, 1, -4] = true := by decide +kernel
theorem sub9_84 : sub9 [-3, 1, -3] = true := by decide +kernel
theorem sub9_85 : sub9 [-3, 1, -2] = true := by decide +kernel
theorem sub9_86 : sub9 [-3, 1, -1] = true := by decide +kernel
theorem sub9_87 : sub9 [-3, 1, 0] = true := by decide +kernel
theorem sub9_88 : sub9 [-3, 1, 1] = true := by decide +kernel
theorem sub9_89 : sub9 [-3, 1, 2] = true := by decide +kernel
theorem sub9_90 : sub9 [-3, 1, 3] = true := by decide +kernel
theorem sub9_91 : sub9 [-3, 1, 4] = true := by decide +kernel
theorem sub9_92 : sub9 [-3, 1, 5] = true := by decide +kernel
theorem sub9_93 : sub9 [-3, 1, 6] = true := by decide +kernel
theorem sub9_94 : sub9 [-3, 1, 7] = true := by decide +kernel
theorem sub9_95 : sub9 [-3, 1, 8] = true := by decide +kernel
theorem sb9_2 : ∀ q ∈ blk9_2, sub9 q = true := by
  unfold blk9_2
  exact List.forall_mem_cons.2 ⟨sub9_64, List.forall_mem_cons.2 ⟨sub9_65, List.forall_mem_cons.2 ⟨sub9_66, List.forall_mem_cons.2 ⟨sub9_67, List.forall_mem_cons.2 ⟨sub9_68, List.forall_mem_cons.2 ⟨sub9_69, List.forall_mem_cons.2 ⟨sub9_70, List.forall_mem_cons.2 ⟨sub9_71, List.forall_mem_cons.2 ⟨sub9_72, List.forall_mem_cons.2 ⟨sub9_73, List.forall_mem_cons.2 ⟨sub9_74, List.forall_mem_cons.2 ⟨sub9_75, List.forall_mem_cons.2 ⟨sub9_76, List.forall_mem_cons.2 ⟨sub9_77, List.forall_mem_cons.2 ⟨sub9_78, List.forall_mem_cons.2 ⟨sub9_79, List.forall_mem_cons.2 ⟨sub9_80, List.forall_mem_cons.2 ⟨sub9_81, List.forall_mem_cons.2 ⟨sub9_82, List.forall_mem_cons.2 ⟨sub9_83, List.forall_mem_cons.2 ⟨sub9_84, List.forall_mem_cons.2 ⟨sub9_85, List.forall_mem_cons.2 ⟨sub9_86, List.forall_mem_cons.2 ⟨sub9_87, List.forall_mem_cons.2 ⟨sub9_88, List.forall_mem_cons.2 ⟨sub9_89, List.forall_mem_cons.2 ⟨sub9_90, List.forall_mem_cons.2 ⟨sub9_91, List.forall_mem_cons.2 ⟨sub9_92, List.forall_mem_cons.2 ⟨sub9_93, List.forall_mem_cons.2 ⟨sub9_94, List.forall_mem_cons.2 ⟨sub9_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_96 : sub9 [-3, 2, -7] = true := by decide +kernel
theorem sub9_97 : sub9 [-3, 2, -6] = true := by decide +kernel
theorem sub9_98 : sub9 [-3, 2, -5] = true := by decide +kernel
theorem sub9_99 : sub9 [-3, 2, -4] = true := by decide +kernel
theorem sub9_100 : sub9 [-3, 2, -3] = true := by decide +kernel
theorem sub9_101 : sub9 [-3, 2, -2] = true := by decide +kernel
theorem sub9_102 : sub9 [-3, 2, -1] = true := by decide +kernel
theorem sub9_103 : sub9 [-3, 2, 0] = true := by decide +kernel
theorem sub9_104 : sub9 [-3, 2, 1] = true := by decide +kernel
theorem sub9_105 : sub9 [-3, 2, 2] = true := by decide +kernel
theorem sub9_106 : sub9 [-3, 2, 3] = true := by decide +kernel
theorem sub9_107 : sub9 [-3, 2, 4] = true := by decide +kernel
theorem sub9_108 : sub9 [-3, 2, 5] = true := by decide +kernel
theorem sub9_109 : sub9 [-3, 2, 6] = true := by decide +kernel
theorem sub9_110 : sub9 [-3, 2, 7] = true := by decide +kernel
theorem sub9_111 : sub9 [-3, 3] = true := by decide +kernel
theorem sub9_112 : sub9 [-3, 4] = true := by decide +kernel
theorem sub9_113 : sub9 [-2, -6] = true := by decide +kernel
theorem sub9_114 : sub9 [-2, -5] = true := by decide +kernel
theorem sub9_115 : sub9 [-2, -4] = true := by decide +kernel
theorem sub9_116 : sub9 [-2, -3, -8] = true := by decide +kernel
theorem sub9_117 : sub9 [-2, -3, -7] = true := by decide +kernel
theorem sub9_118 : sub9 [-2, -3, -6] = true := by decide +kernel
theorem sub9_119 : sub9 [-2, -3, -5] = true := by decide +kernel
theorem sub9_120 : sub9 [-2, -3, -4] = true := by decide +kernel
theorem sub9_121 : sub9 [-2, -3, -3] = true := by decide +kernel
theorem sub9_122 : sub9 [-2, -3, -2] = true := by decide +kernel
theorem sub9_123 : sub9 [-2, -3, -1] = true := by decide +kernel
theorem sub9_124 : sub9 [-2, -3, 0] = true := by decide +kernel
theorem sub9_125 : sub9 [-2, -3, 1] = true := by decide +kernel
theorem sub9_126 : sub9 [-2, -3, 2] = true := by decide +kernel
theorem sub9_127 : sub9 [-2, -3, 3] = true := by decide +kernel
theorem sb9_3 : ∀ q ∈ blk9_3, sub9 q = true := by
  unfold blk9_3
  exact List.forall_mem_cons.2 ⟨sub9_96, List.forall_mem_cons.2 ⟨sub9_97, List.forall_mem_cons.2 ⟨sub9_98, List.forall_mem_cons.2 ⟨sub9_99, List.forall_mem_cons.2 ⟨sub9_100, List.forall_mem_cons.2 ⟨sub9_101, List.forall_mem_cons.2 ⟨sub9_102, List.forall_mem_cons.2 ⟨sub9_103, List.forall_mem_cons.2 ⟨sub9_104, List.forall_mem_cons.2 ⟨sub9_105, List.forall_mem_cons.2 ⟨sub9_106, List.forall_mem_cons.2 ⟨sub9_107, List.forall_mem_cons.2 ⟨sub9_108, List.forall_mem_cons.2 ⟨sub9_109, List.forall_mem_cons.2 ⟨sub9_110, List.forall_mem_cons.2 ⟨sub9_111, List.forall_mem_cons.2 ⟨sub9_112, List.forall_mem_cons.2 ⟨sub9_113, List.forall_mem_cons.2 ⟨sub9_114, List.forall_mem_cons.2 ⟨sub9_115, List.forall_mem_cons.2 ⟨sub9_116, List.forall_mem_cons.2 ⟨sub9_117, List.forall_mem_cons.2 ⟨sub9_118, List.forall_mem_cons.2 ⟨sub9_119, List.forall_mem_cons.2 ⟨sub9_120, List.forall_mem_cons.2 ⟨sub9_121, List.forall_mem_cons.2 ⟨sub9_122, List.forall_mem_cons.2 ⟨sub9_123, List.forall_mem_cons.2 ⟨sub9_124, List.forall_mem_cons.2 ⟨sub9_125, List.forall_mem_cons.2 ⟨sub9_126, List.forall_mem_cons.2 ⟨sub9_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_128 : sub9 [-2, -3, 4] = true := by decide +kernel
theorem sub9_129 : sub9 [-2, -3, 5] = true := by decide +kernel
theorem sub9_130 : sub9 [-2, -3, 6] = true := by decide +kernel
theorem sub9_131 : sub9 [-2, -3, 7] = true := by decide +kernel
theorem sub9_132 : sub9 [-2, -2, -9] = true := by decide +kernel
theorem sub9_133 : sub9 [-2, -2, -8] = true := by decide +kernel
theorem sub9_134 : sub9 [-2, -2, -7] = true := by decide +kernel
theorem sub9_135 : sub9 [-2, -2, -6] = true := by decide +kernel
theorem sub9_136 : sub9 [-2, -2, -5] = true := by decide +kernel
theorem sub9_137 : sub9 [-2, -2, -4] = true := by decide +kernel
theorem sub9_138 : sub9 [-2, -2, -3] = true := by decide +kernel
theorem sub9_139 : sub9 [-2, -2, -2] = true := by decide +kernel
theorem sub9_140 : sub9 [-2, -2, -1] = true := by decide +kernel
theorem sub9_141 : sub9 [-2, -2, 0] = true := by decide +kernel
theorem sub9_142 : sub9 [-2, -2, 1] = true := by decide +kernel
theorem sub9_143 : sub9 [-2, -2, 2] = true := by decide +kernel
theorem sub9_144 : sub9 [-2, -2, 3] = true := by decide +kernel
theorem sub9_145 : sub9 [-2, -2, 4] = true := by decide +kernel
theorem sub9_146 : sub9 [-2, -2, 5] = true := by decide +kernel
theorem sub9_147 : sub9 [-2, -2, 6] = true := by decide +kernel
theorem sub9_148 : sub9 [-2, -2, 7] = true := by decide +kernel
theorem sub9_149 : sub9 [-2, -2, 8] = true := by decide +kernel
theorem sub9_150 : sub9 [-2, -1, -9] = true := by decide +kernel
theorem sub9_151 : sub9 [-2, -1, -8] = true := by decide +kernel
theorem sub9_152 : sub9 [-2, -1, -7] = true := by decide +kernel
theorem sub9_153 : sub9 [-2, -1, -6] = true := by decide +kernel
theorem sub9_154 : sub9 [-2, -1, -5] = true := by decide +kernel
theorem sub9_155 : sub9 [-2, -1, -4] = true := by decide +kernel
theorem sub9_156 : sub9 [-2, -1, -3] = true := by decide +kernel
theorem sub9_157 : sub9 [-2, -1, -2] = true := by decide +kernel
theorem sub9_158 : sub9 [-2, -1, -1] = true := by decide +kernel
theorem sub9_159 : sub9 [-2, -1, 0] = true := by decide +kernel
theorem sb9_4 : ∀ q ∈ blk9_4, sub9 q = true := by
  unfold blk9_4
  exact List.forall_mem_cons.2 ⟨sub9_128, List.forall_mem_cons.2 ⟨sub9_129, List.forall_mem_cons.2 ⟨sub9_130, List.forall_mem_cons.2 ⟨sub9_131, List.forall_mem_cons.2 ⟨sub9_132, List.forall_mem_cons.2 ⟨sub9_133, List.forall_mem_cons.2 ⟨sub9_134, List.forall_mem_cons.2 ⟨sub9_135, List.forall_mem_cons.2 ⟨sub9_136, List.forall_mem_cons.2 ⟨sub9_137, List.forall_mem_cons.2 ⟨sub9_138, List.forall_mem_cons.2 ⟨sub9_139, List.forall_mem_cons.2 ⟨sub9_140, List.forall_mem_cons.2 ⟨sub9_141, List.forall_mem_cons.2 ⟨sub9_142, List.forall_mem_cons.2 ⟨sub9_143, List.forall_mem_cons.2 ⟨sub9_144, List.forall_mem_cons.2 ⟨sub9_145, List.forall_mem_cons.2 ⟨sub9_146, List.forall_mem_cons.2 ⟨sub9_147, List.forall_mem_cons.2 ⟨sub9_148, List.forall_mem_cons.2 ⟨sub9_149, List.forall_mem_cons.2 ⟨sub9_150, List.forall_mem_cons.2 ⟨sub9_151, List.forall_mem_cons.2 ⟨sub9_152, List.forall_mem_cons.2 ⟨sub9_153, List.forall_mem_cons.2 ⟨sub9_154, List.forall_mem_cons.2 ⟨sub9_155, List.forall_mem_cons.2 ⟨sub9_156, List.forall_mem_cons.2 ⟨sub9_157, List.forall_mem_cons.2 ⟨sub9_158, List.forall_mem_cons.2 ⟨sub9_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C105
