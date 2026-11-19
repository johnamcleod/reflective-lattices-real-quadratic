import ReflectZphi.Data.Cert5.C093.Base

namespace ReflectZphi.Data.Cert5.C093

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd11_0_256 : subd11_0 [1, -1, 1] = true := by decide +kernel
theorem subd11_0_257 : subd11_0 [1, -1, 2] = true := by decide +kernel
theorem subd11_0_258 : subd11_0 [1, -1, 3] = true := by decide +kernel
theorem subd11_0_259 : subd11_0 [1, -1, 4] = true := by decide +kernel
theorem subd11_0_260 : subd11_0 [1, -1, 5] = true := by decide +kernel
theorem subd11_0_261 : subd11_0 [1, -1, 6] = true := by decide +kernel
theorem subd11_0_262 : subd11_0 [1, -1, 7] = true := by decide +kernel
theorem subd11_0_263 : subd11_0 [1, -1, 8] = true := by decide +kernel
theorem subd11_0_264 : subd11_0 [1, 0, -9] = true := by decide +kernel
theorem subd11_0_265 : subd11_0 [1, 0, -8] = true := by decide +kernel
theorem subd11_0_266 : subd11_0 [1, 0, -7] = true := by decide +kernel
theorem subd11_0_267 : subd11_0 [1, 0, -6] = true := by decide +kernel
theorem subd11_0_268 : subd11_0 [1, 0, -5] = true := by decide +kernel
theorem subd11_0_269 : subd11_0 [1, 0, -4] = true := by decide +kernel
theorem subd11_0_270 : subd11_0 [1, 0, -3] = true := by decide +kernel
theorem subd11_0_271 : subd11_0 [1, 0, -2] = true := by decide +kernel
theorem subd11_0_272 : subd11_0 [1, 0, -1] = true := by decide +kernel
theorem subd11_0_273 : subd11_0 [1, 0, 0] = true := by decide +kernel
theorem subd11_0_274 : subd11_0 [1, 0, 1] = true := by decide +kernel
theorem subd11_0_275 : subd11_0 [1, 0, 2] = true := by decide +kernel
theorem subd11_0_276 : subd11_0 [1, 0, 3] = true := by decide +kernel
theorem subd11_0_277 : subd11_0 [1, 0, 4] = true := by decide +kernel
theorem subd11_0_278 : subd11_0 [1, 0, 5] = true := by decide +kernel
theorem subd11_0_279 : subd11_0 [1, 0, 6] = true := by decide +kernel
theorem subd11_0_280 : subd11_0 [1, 0, 7] = true := by decide +kernel
theorem subd11_0_281 : subd11_0 [1, 0, 8] = true := by decide +kernel
theorem subd11_0_282 : subd11_0 [1, 1, -9] = true := by decide +kernel
theorem subd11_0_283 : subd11_0 [1, 1, -8] = true := by decide +kernel
theorem subd11_0_284 : subd11_0 [1, 1, -7] = true := by decide +kernel
theorem subd11_0_285 : subd11_0 [1, 1, -6] = true := by decide +kernel
theorem subd11_0_286 : subd11_0 [1, 1, -5] = true := by decide +kernel
theorem subd11_0_287 : subd11_0 [1, 1, -4] = true := by decide +kernel
theorem sbd11_0_8 : ∀ q ∈ blkd11_0_8, subd11_0 q = true := by
  unfold blkd11_0_8
  exact List.forall_mem_cons.2 ⟨subd11_0_256, List.forall_mem_cons.2 ⟨subd11_0_257, List.forall_mem_cons.2 ⟨subd11_0_258, List.forall_mem_cons.2 ⟨subd11_0_259, List.forall_mem_cons.2 ⟨subd11_0_260, List.forall_mem_cons.2 ⟨subd11_0_261, List.forall_mem_cons.2 ⟨subd11_0_262, List.forall_mem_cons.2 ⟨subd11_0_263, List.forall_mem_cons.2 ⟨subd11_0_264, List.forall_mem_cons.2 ⟨subd11_0_265, List.forall_mem_cons.2 ⟨subd11_0_266, List.forall_mem_cons.2 ⟨subd11_0_267, List.forall_mem_cons.2 ⟨subd11_0_268, List.forall_mem_cons.2 ⟨subd11_0_269, List.forall_mem_cons.2 ⟨subd11_0_270, List.forall_mem_cons.2 ⟨subd11_0_271, List.forall_mem_cons.2 ⟨subd11_0_272, List.forall_mem_cons.2 ⟨subd11_0_273, List.forall_mem_cons.2 ⟨subd11_0_274, List.forall_mem_cons.2 ⟨subd11_0_275, List.forall_mem_cons.2 ⟨subd11_0_276, List.forall_mem_cons.2 ⟨subd11_0_277, List.forall_mem_cons.2 ⟨subd11_0_278, List.forall_mem_cons.2 ⟨subd11_0_279, List.forall_mem_cons.2 ⟨subd11_0_280, List.forall_mem_cons.2 ⟨subd11_0_281, List.forall_mem_cons.2 ⟨subd11_0_282, List.forall_mem_cons.2 ⟨subd11_0_283, List.forall_mem_cons.2 ⟨subd11_0_284, List.forall_mem_cons.2 ⟨subd11_0_285, List.forall_mem_cons.2 ⟨subd11_0_286, List.forall_mem_cons.2 ⟨subd11_0_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_288 : subd11_0 [1, 1, -3] = true := by decide +kernel
theorem subd11_0_289 : subd11_0 [1, 1, -2] = true := by decide +kernel
theorem subd11_0_290 : subd11_0 [1, 1, -1] = true := by decide +kernel
theorem subd11_0_291 : subd11_0 [1, 1, 0] = true := by decide +kernel
theorem subd11_0_292 : subd11_0 [1, 1, 1] = true := by decide +kernel
theorem subd11_0_293 : subd11_0 [1, 1, 2] = true := by decide +kernel
theorem subd11_0_294 : subd11_0 [1, 1, 3] = true := by decide +kernel
theorem subd11_0_295 : subd11_0 [1, 1, 4] = true := by decide +kernel
theorem subd11_0_296 : subd11_0 [1, 1, 5] = true := by decide +kernel
theorem subd11_0_297 : subd11_0 [1, 1, 6] = true := by decide +kernel
theorem subd11_0_298 : subd11_0 [1, 1, 7] = true := by decide +kernel
theorem subd11_0_299 : subd11_0 [1, 1, 8] = true := by decide +kernel
theorem subd11_0_300 : subd11_0 [1, 2] = true := by decide +kernel
theorem subd11_0_301 : subd11_0 [1, 3] = true := by decide +kernel
theorem subd11_0_302 : subd11_0 [2, -4] = true := by decide +kernel
theorem subd11_0_303 : subd11_0 [2, -3] = true := by decide +kernel
theorem subd11_0_304 : subd11_0 [2, -2, -6] = true := by decide +kernel
theorem subd11_0_305 : subd11_0 [2, -2, -5] = true := by decide +kernel
theorem subd11_0_306 : subd11_0 [2, -2, -4] = true := by decide +kernel
theorem subd11_0_307 : subd11_0 [2, -2, -3] = true := by decide +kernel
theorem subd11_0_308 : subd11_0 [2, -2, -2] = true := by decide +kernel
theorem subd11_0_309 : subd11_0 [2, -2, -1] = true := by decide +kernel
theorem subd11_0_310 : subd11_0 [2, -2, 0] = true := by decide +kernel
theorem subd11_0_311 : subd11_0 [2, -2, 1] = true := by decide +kernel
theorem subd11_0_312 : subd11_0 [2, -2, 2] = true := by decide +kernel
theorem subd11_0_313 : subd11_0 [2, -2, 3] = true := by decide +kernel
theorem subd11_0_314 : subd11_0 [2, -2, 4] = true := by decide +kernel
theorem subd11_0_315 : subd11_0 [2, -2, 5] = true := by decide +kernel
theorem subd11_0_316 : subd11_0 [2, -2, 6] = true := by decide +kernel
theorem subd11_0_317 : subd11_0 [2, -2, 7] = true := by decide +kernel
theorem subd11_0_318 : subd11_0 [2, -1, -7] = true := by decide +kernel
theorem subd11_0_319 : subd11_0 [2, -1, -6] = true := by decide +kernel
theorem sbd11_0_9 : ∀ q ∈ blkd11_0_9, subd11_0 q = true := by
  unfold blkd11_0_9
  exact List.forall_mem_cons.2 ⟨subd11_0_288, List.forall_mem_cons.2 ⟨subd11_0_289, List.forall_mem_cons.2 ⟨subd11_0_290, List.forall_mem_cons.2 ⟨subd11_0_291, List.forall_mem_cons.2 ⟨subd11_0_292, List.forall_mem_cons.2 ⟨subd11_0_293, List.forall_mem_cons.2 ⟨subd11_0_294, List.forall_mem_cons.2 ⟨subd11_0_295, List.forall_mem_cons.2 ⟨subd11_0_296, List.forall_mem_cons.2 ⟨subd11_0_297, List.forall_mem_cons.2 ⟨subd11_0_298, List.forall_mem_cons.2 ⟨subd11_0_299, List.forall_mem_cons.2 ⟨subd11_0_300, List.forall_mem_cons.2 ⟨subd11_0_301, List.forall_mem_cons.2 ⟨subd11_0_302, List.forall_mem_cons.2 ⟨subd11_0_303, List.forall_mem_cons.2 ⟨subd11_0_304, List.forall_mem_cons.2 ⟨subd11_0_305, List.forall_mem_cons.2 ⟨subd11_0_306, List.forall_mem_cons.2 ⟨subd11_0_307, List.forall_mem_cons.2 ⟨subd11_0_308, List.forall_mem_cons.2 ⟨subd11_0_309, List.forall_mem_cons.2 ⟨subd11_0_310, List.forall_mem_cons.2 ⟨subd11_0_311, List.forall_mem_cons.2 ⟨subd11_0_312, List.forall_mem_cons.2 ⟨subd11_0_313, List.forall_mem_cons.2 ⟨subd11_0_314, List.forall_mem_cons.2 ⟨subd11_0_315, List.forall_mem_cons.2 ⟨subd11_0_316, List.forall_mem_cons.2 ⟨subd11_0_317, List.forall_mem_cons.2 ⟨subd11_0_318, List.forall_mem_cons.2 ⟨subd11_0_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_320 : subd11_0 [2, -1, -5] = true := by decide +kernel
theorem subd11_0_321 : subd11_0 [2, -1, -4] = true := by decide +kernel
theorem subd11_0_322 : subd11_0 [2, -1, -3] = true := by decide +kernel
theorem subd11_0_323 : subd11_0 [2, -1, -2] = true := by decide +kernel
theorem subd11_0_324 : subd11_0 [2, -1, -1] = true := by decide +kernel
theorem subd11_0_325 : subd11_0 [2, -1, 0] = true := by decide +kernel
theorem subd11_0_326 : subd11_0 [2, -1, 1] = true := by decide +kernel
theorem subd11_0_327 : subd11_0 [2, -1, 2] = true := by decide +kernel
theorem subd11_0_328 : subd11_0 [2, -1, 3] = true := by decide +kernel
theorem subd11_0_329 : subd11_0 [2, -1, 4] = true := by decide +kernel
theorem subd11_0_330 : subd11_0 [2, -1, 5] = true := by decide +kernel
theorem subd11_0_331 : subd11_0 [2, -1, 6] = true := by decide +kernel
theorem subd11_0_332 : subd11_0 [2, -1, 7] = true := by decide +kernel
theorem subd11_0_333 : subd11_0 [2, -1, 8] = true := by decide +kernel
theorem subd11_0_334 : subd11_0 [2, 0, -8] = true := by decide +kernel
theorem subd11_0_335 : subd11_0 [2, 0, -7] = true := by decide +kernel
theorem subd11_0_336 : subd11_0 [2, 0, -6] = true := by decide +kernel
theorem subd11_0_337 : subd11_0 [2, 0, -5] = true := by decide +kernel
theorem subd11_0_338 : subd11_0 [2, 0, -4] = true := by decide +kernel
theorem subd11_0_339 : subd11_0 [2, 0, -3] = true := by decide +kernel
theorem subd11_0_340 : subd11_0 [2, 0, -2] = true := by decide +kernel
theorem subd11_0_341 : subd11_0 [2, 0, -1] = true := by decide +kernel
theorem subd11_0_342 : subd11_0 [2, 0, 0] = true := by decide +kernel
theorem subd11_0_343 : subd11_0 [2, 0, 1] = true := by decide +kernel
theorem subd11_0_344 : subd11_0 [2, 0, 2] = true := by decide +kernel
theorem subd11_0_345 : subd11_0 [2, 0, 3] = true := by decide +kernel
theorem subd11_0_346 : subd11_0 [2, 0, 4] = true := by decide +kernel
theorem subd11_0_347 : subd11_0 [2, 0, 5] = true := by decide +kernel
theorem subd11_0_348 : subd11_0 [2, 0, 6] = true := by decide +kernel
theorem subd11_0_349 : subd11_0 [2, 0, 7] = true := by decide +kernel
theorem subd11_0_350 : subd11_0 [2, 0, 8] = true := by decide +kernel
theorem subd11_0_351 : subd11_0 [2, 1, -7] = true := by decide +kernel
theorem sbd11_0_10 : ∀ q ∈ blkd11_0_10, subd11_0 q = true := by
  unfold blkd11_0_10
  exact List.forall_mem_cons.2 ⟨subd11_0_320, List.forall_mem_cons.2 ⟨subd11_0_321, List.forall_mem_cons.2 ⟨subd11_0_322, List.forall_mem_cons.2 ⟨subd11_0_323, List.forall_mem_cons.2 ⟨subd11_0_324, List.forall_mem_cons.2 ⟨subd11_0_325, List.forall_mem_cons.2 ⟨subd11_0_326, List.forall_mem_cons.2 ⟨subd11_0_327, List.forall_mem_cons.2 ⟨subd11_0_328, List.forall_mem_cons.2 ⟨subd11_0_329, List.forall_mem_cons.2 ⟨subd11_0_330, List.forall_mem_cons.2 ⟨subd11_0_331, List.forall_mem_cons.2 ⟨subd11_0_332, List.forall_mem_cons.2 ⟨subd11_0_333, List.forall_mem_cons.2 ⟨subd11_0_334, List.forall_mem_cons.2 ⟨subd11_0_335, List.forall_mem_cons.2 ⟨subd11_0_336, List.forall_mem_cons.2 ⟨subd11_0_337, List.forall_mem_cons.2 ⟨subd11_0_338, List.forall_mem_cons.2 ⟨subd11_0_339, List.forall_mem_cons.2 ⟨subd11_0_340, List.forall_mem_cons.2 ⟨subd11_0_341, List.forall_mem_cons.2 ⟨subd11_0_342, List.forall_mem_cons.2 ⟨subd11_0_343, List.forall_mem_cons.2 ⟨subd11_0_344, List.forall_mem_cons.2 ⟨subd11_0_345, List.forall_mem_cons.2 ⟨subd11_0_346, List.forall_mem_cons.2 ⟨subd11_0_347, List.forall_mem_cons.2 ⟨subd11_0_348, List.forall_mem_cons.2 ⟨subd11_0_349, List.forall_mem_cons.2 ⟨subd11_0_350, List.forall_mem_cons.2 ⟨subd11_0_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_352 : subd11_0 [2, 1, -6] = true := by decide +kernel
theorem subd11_0_353 : subd11_0 [2, 1, -5] = true := by decide +kernel
theorem subd11_0_354 : subd11_0 [2, 1, -4] = true := by decide +kernel
theorem subd11_0_355 : subd11_0 [2, 1, -3] = true := by decide +kernel
theorem subd11_0_356 : subd11_0 [2, 1, -2] = true := by decide +kernel
theorem subd11_0_357 : subd11_0 [2, 1, -1] = true := by decide +kernel
theorem subd11_0_358 : subd11_0 [2, 1, 0] = true := by decide +kernel
theorem subd11_0_359 : subd11_0 [2, 1, 1] = true := by decide +kernel
theorem subd11_0_360 : subd11_0 [2, 1, 2] = true := by decide +kernel
theorem subd11_0_361 : subd11_0 [2, 1, 3] = true := by decide +kernel
theorem subd11_0_362 : subd11_0 [2, 1, 4] = true := by decide +kernel
theorem subd11_0_363 : subd11_0 [2, 1, 5] = true := by decide +kernel
theorem subd11_0_364 : subd11_0 [2, 1, 6] = true := by decide +kernel
theorem subd11_0_365 : subd11_0 [2, 2] = true := by decide +kernel
theorem subd11_0_366 : subd11_0 [3, -3] = true := by decide +kernel
theorem subd11_0_367 : subd11_0 [3, -2] = true := by decide +kernel
theorem subd11_0_368 : subd11_0 [3, -1] = true := by decide +kernel
theorem subd11_0_369 : subd11_0 [3, 0] = true := by decide +kernel
theorem subd11_0_370 : subd11_0 [3, 1] = true := by decide +kernel
theorem sbd11_0_11 : ∀ q ∈ blkd11_0_11, subd11_0 q = true := by
  unfold blkd11_0_11
  exact List.forall_mem_cons.2 ⟨subd11_0_352, List.forall_mem_cons.2 ⟨subd11_0_353, List.forall_mem_cons.2 ⟨subd11_0_354, List.forall_mem_cons.2 ⟨subd11_0_355, List.forall_mem_cons.2 ⟨subd11_0_356, List.forall_mem_cons.2 ⟨subd11_0_357, List.forall_mem_cons.2 ⟨subd11_0_358, List.forall_mem_cons.2 ⟨subd11_0_359, List.forall_mem_cons.2 ⟨subd11_0_360, List.forall_mem_cons.2 ⟨subd11_0_361, List.forall_mem_cons.2 ⟨subd11_0_362, List.forall_mem_cons.2 ⟨subd11_0_363, List.forall_mem_cons.2 ⟨subd11_0_364, List.forall_mem_cons.2 ⟨subd11_0_365, List.forall_mem_cons.2 ⟨subd11_0_366, List.forall_mem_cons.2 ⟨subd11_0_367, List.forall_mem_cons.2 ⟨subd11_0_368, List.forall_mem_cons.2 ⟨subd11_0_369, List.forall_mem_cons.2 ⟨subd11_0_370, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_1 : ldCheck G d11_1.U d11_1.ms ldd11_1 = true := by decide +kernel
theorem pre_okd11_1 : subPre G cell11 d11_1 = true := by decide +kernel
theorem subd11_1_0 : subd11_1 [-3] = true := by decide +kernel
theorem subd11_1_1 : subd11_1 [-2] = true := by decide +kernel
theorem subd11_1_2 : subd11_1 [-1] = true := by decide +kernel
theorem subd11_1_3 : subd11_1 [0] = true := by decide +kernel
theorem subd11_1_4 : subd11_1 [1] = true := by decide +kernel
theorem subd11_1_5 : subd11_1 [2] = true := by decide +kernel
theorem subd11_1_6 : subd11_1 [3] = true := by decide +kernel
theorem sbd11_1_0 : ∀ q ∈ blkd11_1_0, subd11_1 q = true := by
  unfold blkd11_1_0
  exact List.forall_mem_cons.2 ⟨subd11_1_0, List.forall_mem_cons.2 ⟨subd11_1_1, List.forall_mem_cons.2 ⟨subd11_1_2, List.forall_mem_cons.2 ⟨subd11_1_3, List.forall_mem_cons.2 ⟨subd11_1_4, List.forall_mem_cons.2 ⟨subd11_1_5, List.forall_mem_cons.2 ⟨subd11_1_6, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_2 : ldCheck G d11_2.U d11_2.ms ldd11_2 = true := by decide +kernel
theorem pre_okd11_2 : subPre G cell11 d11_2 = true := by decide +kernel
theorem subd11_2_0 : subd11_2 [-1, -2] = true := by decide +kernel
theorem subd11_2_1 : subd11_2 [-1, -1] = true := by decide +kernel
theorem subd11_2_2 : subd11_2 [-1, 0] = true := by decide +kernel
theorem subd11_2_3 : subd11_2 [-1, 1] = true := by decide +kernel
theorem subd11_2_4 : subd11_2 [0, -2] = true := by decide +kernel
theorem subd11_2_5 : subd11_2 [0, -1] = true := by decide +kernel
theorem subd11_2_6 : subd11_2 [0, 0] = true := by decide +kernel
theorem subd11_2_7 : subd11_2 [0, 1] = true := by decide +kernel
theorem subd11_2_8 : subd11_2 [1, -2] = true := by decide +kernel
theorem subd11_2_9 : subd11_2 [1, -1] = true := by decide +kernel
theorem subd11_2_10 : subd11_2 [1, 0] = true := by decide +kernel
theorem subd11_2_11 : subd11_2 [1, 1] = true := by decide +kernel
theorem sbd11_2_0 : ∀ q ∈ blkd11_2_0, subd11_2 q = true := by
  unfold blkd11_2_0
  exact List.forall_mem_cons.2 ⟨subd11_2_0, List.forall_mem_cons.2 ⟨subd11_2_1, List.forall_mem_cons.2 ⟨subd11_2_2, List.forall_mem_cons.2 ⟨subd11_2_3, List.forall_mem_cons.2 ⟨subd11_2_4, List.forall_mem_cons.2 ⟨subd11_2_5, List.forall_mem_cons.2 ⟨subd11_2_6, List.forall_mem_cons.2 ⟨subd11_2_7, List.forall_mem_cons.2 ⟨subd11_2_8, List.forall_mem_cons.2 ⟨subd11_2_9, List.forall_mem_cons.2 ⟨subd11_2_10, List.forall_mem_cons.2 ⟨subd11_2_11, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_3 : ldCheck G d11_3.U d11_3.ms ldd11_3 = true := by decide +kernel
theorem pre_okd11_3 : subPre G cell11 d11_3 = true := by decide +kernel
theorem subd11_3_0 : subd11_3 [-2] = true := by decide +kernel
theorem subd11_3_1 : subd11_3 [-1, -3] = true := by decide +kernel
theorem subd11_3_2 : subd11_3 [-1, -2] = true := by decide +kernel
theorem subd11_3_3 : subd11_3 [-1, -1] = true := by decide +kernel
theorem subd11_3_4 : subd11_3 [-1, 0] = true := by decide +kernel
theorem subd11_3_5 : subd11_3 [-1, 1] = true := by decide +kernel
theorem subd11_3_6 : subd11_3 [-1, 2] = true := by decide +kernel
theorem subd11_3_7 : subd11_3 [0, -3] = true := by decide +kernel
theorem subd11_3_8 : subd11_3 [0, -2] = true := by decide +kernel
theorem subd11_3_9 : subd11_3 [0, -1] = true := by decide +kernel
theorem subd11_3_10 : subd11_3 [0, 0] = true := by decide +kernel
theorem subd11_3_11 : subd11_3 [0, 1] = true := by decide +kernel
theorem subd11_3_12 : subd11_3 [0, 2] = true := by decide +kernel
theorem subd11_3_13 : subd11_3 [1, -3] = true := by decide +kernel
theorem subd11_3_14 : subd11_3 [1, -2] = true := by decide +kernel
theorem subd11_3_15 : subd11_3 [1, -1] = true := by decide +kernel
theorem subd11_3_16 : subd11_3 [1, 0] = true := by decide +kernel
theorem subd11_3_17 : subd11_3 [1, 1] = true := by decide +kernel
theorem subd11_3_18 : subd11_3 [1, 2] = true := by decide +kernel
theorem subd11_3_19 : subd11_3 [2] = true := by decide +kernel
theorem sbd11_3_0 : ∀ q ∈ blkd11_3_0, subd11_3 q = true := by
  unfold blkd11_3_0
  exact List.forall_mem_cons.2 ⟨subd11_3_0, List.forall_mem_cons.2 ⟨subd11_3_1, List.forall_mem_cons.2 ⟨subd11_3_2, List.forall_mem_cons.2 ⟨subd11_3_3, List.forall_mem_cons.2 ⟨subd11_3_4, List.forall_mem_cons.2 ⟨subd11_3_5, List.forall_mem_cons.2 ⟨subd11_3_6, List.forall_mem_cons.2 ⟨subd11_3_7, List.forall_mem_cons.2 ⟨subd11_3_8, List.forall_mem_cons.2 ⟨subd11_3_9, List.forall_mem_cons.2 ⟨subd11_3_10, List.forall_mem_cons.2 ⟨subd11_3_11, List.forall_mem_cons.2 ⟨subd11_3_12, List.forall_mem_cons.2 ⟨subd11_3_13, List.forall_mem_cons.2 ⟨subd11_3_14, List.forall_mem_cons.2 ⟨subd11_3_15, List.forall_mem_cons.2 ⟨subd11_3_16, List.forall_mem_cons.2 ⟨subd11_3_17, List.forall_mem_cons.2 ⟨subd11_3_18, List.forall_mem_cons.2 ⟨subd11_3_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_4 : ldCheck G d11_4.U d11_4.ms ldd11_4 = true := by decide +kernel
theorem pre_okd11_4 : subPre G cell11 d11_4 = true := by decide +kernel
theorem subd11_4_0 : subd11_4 [-2] = true := by decide +kernel
theorem subd11_4_1 : subd11_4 [-1] = true := by decide +kernel
theorem subd11_4_2 : subd11_4 [0] = true := by decide +kernel
theorem subd11_4_3 : subd11_4 [1] = true := by decide +kernel
theorem subd11_4_4 : subd11_4 [2] = true := by decide +kernel
theorem sbd11_4_0 : ∀ q ∈ blkd11_4_0, subd11_4 q = true := by
  unfold blkd11_4_0
  exact List.forall_mem_cons.2 ⟨subd11_4_0, List.forall_mem_cons.2 ⟨subd11_4_1, List.forall_mem_cons.2 ⟨subd11_4_2, List.forall_mem_cons.2 ⟨subd11_4_3, List.forall_mem_cons.2 ⟨subd11_4_4, List.forall_mem_nil _⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C093
