import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_8_288 : subd6_8 [0, 1, 15] = true := by decide +kernel
theorem subd6_8_289 : subd6_8 [0, 1, 16] = true := by decide +kernel
theorem subd6_8_290 : subd6_8 [0, 1, 17] = true := by decide +kernel
theorem subd6_8_291 : subd6_8 [0, 1, 18] = true := by decide +kernel
theorem subd6_8_292 : subd6_8 [0, 1, 19] = true := by decide +kernel
theorem subd6_8_293 : subd6_8 [0, 1, 20] = true := by decide +kernel
theorem subd6_8_294 : subd6_8 [0, 1, 21] = true := by decide +kernel
theorem subd6_8_295 : subd6_8 [0, 1, 22] = true := by decide +kernel
theorem subd6_8_296 : subd6_8 [0, 1, 23] = true := by decide +kernel
theorem subd6_8_297 : subd6_8 [0, 1, 24] = true := by decide +kernel
theorem subd6_8_298 : subd6_8 [0, 1, 25] = true := by decide +kernel
theorem subd6_8_299 : subd6_8 [0, 1, 26] = true := by decide +kernel
theorem subd6_8_300 : subd6_8 [0, 1, 27] = true := by decide +kernel
theorem subd6_8_301 : subd6_8 [0, 1, 28] = true := by decide +kernel
theorem subd6_8_302 : subd6_8 [0, 1, 29] = true := by decide +kernel
theorem subd6_8_303 : subd6_8 [0, 1, 30] = true := by decide +kernel
theorem subd6_8_304 : subd6_8 [0, 1, 31] = true := by decide +kernel
theorem subd6_8_305 : subd6_8 [1, -1] = true := by decide +kernel
theorem subd6_8_306 : subd6_8 [1, 0, -25] = true := by decide +kernel
theorem subd6_8_307 : subd6_8 [1, 0, -24] = true := by decide +kernel
theorem subd6_8_308 : subd6_8 [1, 0, -23] = true := by decide +kernel
theorem subd6_8_309 : subd6_8 [1, 0, -22] = true := by decide +kernel
theorem subd6_8_310 : subd6_8 [1, 0, -21] = true := by decide +kernel
theorem subd6_8_311 : subd6_8 [1, 0, -20] = true := by decide +kernel
theorem subd6_8_312 : subd6_8 [1, 0, -19] = true := by decide +kernel
theorem subd6_8_313 : subd6_8 [1, 0, -18] = true := by decide +kernel
theorem subd6_8_314 : subd6_8 [1, 0, -17] = true := by decide +kernel
theorem subd6_8_315 : subd6_8 [1, 0, -16] = true := by decide +kernel
theorem subd6_8_316 : subd6_8 [1, 0, -15] = true := by decide +kernel
theorem subd6_8_317 : subd6_8 [1, 0, -14] = true := by decide +kernel
theorem subd6_8_318 : subd6_8 [1, 0, -13] = true := by decide +kernel
theorem subd6_8_319 : subd6_8 [1, 0, -12] = true := by decide +kernel
theorem sbd6_8_9 : ∀ q ∈ blkd6_8_9, subd6_8 q = true := by
  unfold blkd6_8_9
  exact List.forall_mem_cons.2 ⟨subd6_8_288, List.forall_mem_cons.2 ⟨subd6_8_289, List.forall_mem_cons.2 ⟨subd6_8_290, List.forall_mem_cons.2 ⟨subd6_8_291, List.forall_mem_cons.2 ⟨subd6_8_292, List.forall_mem_cons.2 ⟨subd6_8_293, List.forall_mem_cons.2 ⟨subd6_8_294, List.forall_mem_cons.2 ⟨subd6_8_295, List.forall_mem_cons.2 ⟨subd6_8_296, List.forall_mem_cons.2 ⟨subd6_8_297, List.forall_mem_cons.2 ⟨subd6_8_298, List.forall_mem_cons.2 ⟨subd6_8_299, List.forall_mem_cons.2 ⟨subd6_8_300, List.forall_mem_cons.2 ⟨subd6_8_301, List.forall_mem_cons.2 ⟨subd6_8_302, List.forall_mem_cons.2 ⟨subd6_8_303, List.forall_mem_cons.2 ⟨subd6_8_304, List.forall_mem_cons.2 ⟨subd6_8_305, List.forall_mem_cons.2 ⟨subd6_8_306, List.forall_mem_cons.2 ⟨subd6_8_307, List.forall_mem_cons.2 ⟨subd6_8_308, List.forall_mem_cons.2 ⟨subd6_8_309, List.forall_mem_cons.2 ⟨subd6_8_310, List.forall_mem_cons.2 ⟨subd6_8_311, List.forall_mem_cons.2 ⟨subd6_8_312, List.forall_mem_cons.2 ⟨subd6_8_313, List.forall_mem_cons.2 ⟨subd6_8_314, List.forall_mem_cons.2 ⟨subd6_8_315, List.forall_mem_cons.2 ⟨subd6_8_316, List.forall_mem_cons.2 ⟨subd6_8_317, List.forall_mem_cons.2 ⟨subd6_8_318, List.forall_mem_cons.2 ⟨subd6_8_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_8_320 : subd6_8 [1, 0, -11] = true := by decide +kernel
theorem subd6_8_321 : subd6_8 [1, 0, -10] = true := by decide +kernel
theorem subd6_8_322 : subd6_8 [1, 0, -9] = true := by decide +kernel
theorem subd6_8_323 : subd6_8 [1, 0, -8] = true := by decide +kernel
theorem subd6_8_324 : subd6_8 [1, 0, -7] = true := by decide +kernel
theorem subd6_8_325 : subd6_8 [1, 0, -6] = true := by decide +kernel
theorem subd6_8_326 : subd6_8 [1, 0, -5] = true := by decide +kernel
theorem subd6_8_327 : subd6_8 [1, 0, -4] = true := by decide +kernel
theorem subd6_8_328 : subd6_8 [1, 0, -3] = true := by decide +kernel
theorem subd6_8_329 : subd6_8 [1, 0, -2] = true := by decide +kernel
theorem subd6_8_330 : subd6_8 [1, 0, -1] = true := by decide +kernel
theorem subd6_8_331 : subd6_8 [1, 0, 0] = true := by decide +kernel
theorem subd6_8_332 : subd6_8 [1, 0, 1] = true := by decide +kernel
theorem subd6_8_333 : subd6_8 [1, 0, 2] = true := by decide +kernel
theorem subd6_8_334 : subd6_8 [1, 0, 3] = true := by decide +kernel
theorem subd6_8_335 : subd6_8 [1, 0, 4] = true := by decide +kernel
theorem subd6_8_336 : subd6_8 [1, 0, 5] = true := by decide +kernel
theorem subd6_8_337 : subd6_8 [1, 0, 6] = true := by decide +kernel
theorem subd6_8_338 : subd6_8 [1, 0, 7] = true := by decide +kernel
theorem subd6_8_339 : subd6_8 [1, 0, 8] = true := by decide +kernel
theorem subd6_8_340 : subd6_8 [1, 0, 9] = true := by decide +kernel
theorem subd6_8_341 : subd6_8 [1, 0, 10] = true := by decide +kernel
theorem subd6_8_342 : subd6_8 [1, 0, 11] = true := by decide +kernel
theorem subd6_8_343 : subd6_8 [1, 0, 12] = true := by decide +kernel
theorem subd6_8_344 : subd6_8 [1, 0, 13] = true := by decide +kernel
theorem subd6_8_345 : subd6_8 [1, 0, 14] = true := by decide +kernel
theorem subd6_8_346 : subd6_8 [1, 0, 15] = true := by decide +kernel
theorem subd6_8_347 : subd6_8 [1, 0, 16] = true := by decide +kernel
theorem subd6_8_348 : subd6_8 [1, 0, 17] = true := by decide +kernel
theorem subd6_8_349 : subd6_8 [1, 0, 18] = true := by decide +kernel
theorem subd6_8_350 : subd6_8 [1, 0, 19] = true := by decide +kernel
theorem subd6_8_351 : subd6_8 [1, 0, 20] = true := by decide +kernel
theorem sbd6_8_10 : ∀ q ∈ blkd6_8_10, subd6_8 q = true := by
  unfold blkd6_8_10
  exact List.forall_mem_cons.2 ⟨subd6_8_320, List.forall_mem_cons.2 ⟨subd6_8_321, List.forall_mem_cons.2 ⟨subd6_8_322, List.forall_mem_cons.2 ⟨subd6_8_323, List.forall_mem_cons.2 ⟨subd6_8_324, List.forall_mem_cons.2 ⟨subd6_8_325, List.forall_mem_cons.2 ⟨subd6_8_326, List.forall_mem_cons.2 ⟨subd6_8_327, List.forall_mem_cons.2 ⟨subd6_8_328, List.forall_mem_cons.2 ⟨subd6_8_329, List.forall_mem_cons.2 ⟨subd6_8_330, List.forall_mem_cons.2 ⟨subd6_8_331, List.forall_mem_cons.2 ⟨subd6_8_332, List.forall_mem_cons.2 ⟨subd6_8_333, List.forall_mem_cons.2 ⟨subd6_8_334, List.forall_mem_cons.2 ⟨subd6_8_335, List.forall_mem_cons.2 ⟨subd6_8_336, List.forall_mem_cons.2 ⟨subd6_8_337, List.forall_mem_cons.2 ⟨subd6_8_338, List.forall_mem_cons.2 ⟨subd6_8_339, List.forall_mem_cons.2 ⟨subd6_8_340, List.forall_mem_cons.2 ⟨subd6_8_341, List.forall_mem_cons.2 ⟨subd6_8_342, List.forall_mem_cons.2 ⟨subd6_8_343, List.forall_mem_cons.2 ⟨subd6_8_344, List.forall_mem_cons.2 ⟨subd6_8_345, List.forall_mem_cons.2 ⟨subd6_8_346, List.forall_mem_cons.2 ⟨subd6_8_347, List.forall_mem_cons.2 ⟨subd6_8_348, List.forall_mem_cons.2 ⟨subd6_8_349, List.forall_mem_cons.2 ⟨subd6_8_350, List.forall_mem_cons.2 ⟨subd6_8_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_8_352 : subd6_8 [1, 0, 21] = true := by decide +kernel
theorem subd6_8_353 : subd6_8 [1, 0, 22] = true := by decide +kernel
theorem subd6_8_354 : subd6_8 [1, 0, 23] = true := by decide +kernel
theorem subd6_8_355 : subd6_8 [1, 0, 24] = true := by decide +kernel
theorem subd6_8_356 : subd6_8 [1, 0, 25] = true := by decide +kernel
theorem subd6_8_357 : subd6_8 [1, 1, -19] = true := by decide +kernel
theorem subd6_8_358 : subd6_8 [1, 1, -18] = true := by decide +kernel
theorem subd6_8_359 : subd6_8 [1, 1, -17] = true := by decide +kernel
theorem subd6_8_360 : subd6_8 [1, 1, -16] = true := by decide +kernel
theorem subd6_8_361 : subd6_8 [1, 1, -15] = true := by decide +kernel
theorem subd6_8_362 : subd6_8 [1, 1, -14] = true := by decide +kernel
theorem subd6_8_363 : subd6_8 [1, 1, -13] = true := by decide +kernel
theorem subd6_8_364 : subd6_8 [1, 1, -12] = true := by decide +kernel
theorem subd6_8_365 : subd6_8 [1, 1, -11] = true := by decide +kernel
theorem subd6_8_366 : subd6_8 [1, 1, -10] = true := by decide +kernel
theorem subd6_8_367 : subd6_8 [1, 1, -9] = true := by decide +kernel
theorem subd6_8_368 : subd6_8 [1, 1, -8] = true := by decide +kernel
theorem subd6_8_369 : subd6_8 [1, 1, -7] = true := by decide +kernel
theorem subd6_8_370 : subd6_8 [1, 1, -6] = true := by decide +kernel
theorem subd6_8_371 : subd6_8 [1, 1, -5] = true := by decide +kernel
theorem subd6_8_372 : subd6_8 [1, 1, -4] = true := by decide +kernel
theorem subd6_8_373 : subd6_8 [1, 1, -3] = true := by decide +kernel
theorem subd6_8_374 : subd6_8 [1, 1, -2] = true := by decide +kernel
theorem subd6_8_375 : subd6_8 [1, 1, -1] = true := by decide +kernel
theorem subd6_8_376 : subd6_8 [1, 1, 0] = true := by decide +kernel
theorem subd6_8_377 : subd6_8 [1, 1, 1] = true := by decide +kernel
theorem subd6_8_378 : subd6_8 [1, 1, 2] = true := by decide +kernel
theorem subd6_8_379 : subd6_8 [1, 1, 3] = true := by decide +kernel
theorem subd6_8_380 : subd6_8 [1, 1, 4] = true := by decide +kernel
theorem subd6_8_381 : subd6_8 [1, 1, 5] = true := by decide +kernel
theorem subd6_8_382 : subd6_8 [1, 1, 6] = true := by decide +kernel
theorem subd6_8_383 : subd6_8 [1, 1, 7] = true := by decide +kernel
theorem sbd6_8_11 : ∀ q ∈ blkd6_8_11, subd6_8 q = true := by
  unfold blkd6_8_11
  exact List.forall_mem_cons.2 ⟨subd6_8_352, List.forall_mem_cons.2 ⟨subd6_8_353, List.forall_mem_cons.2 ⟨subd6_8_354, List.forall_mem_cons.2 ⟨subd6_8_355, List.forall_mem_cons.2 ⟨subd6_8_356, List.forall_mem_cons.2 ⟨subd6_8_357, List.forall_mem_cons.2 ⟨subd6_8_358, List.forall_mem_cons.2 ⟨subd6_8_359, List.forall_mem_cons.2 ⟨subd6_8_360, List.forall_mem_cons.2 ⟨subd6_8_361, List.forall_mem_cons.2 ⟨subd6_8_362, List.forall_mem_cons.2 ⟨subd6_8_363, List.forall_mem_cons.2 ⟨subd6_8_364, List.forall_mem_cons.2 ⟨subd6_8_365, List.forall_mem_cons.2 ⟨subd6_8_366, List.forall_mem_cons.2 ⟨subd6_8_367, List.forall_mem_cons.2 ⟨subd6_8_368, List.forall_mem_cons.2 ⟨subd6_8_369, List.forall_mem_cons.2 ⟨subd6_8_370, List.forall_mem_cons.2 ⟨subd6_8_371, List.forall_mem_cons.2 ⟨subd6_8_372, List.forall_mem_cons.2 ⟨subd6_8_373, List.forall_mem_cons.2 ⟨subd6_8_374, List.forall_mem_cons.2 ⟨subd6_8_375, List.forall_mem_cons.2 ⟨subd6_8_376, List.forall_mem_cons.2 ⟨subd6_8_377, List.forall_mem_cons.2 ⟨subd6_8_378, List.forall_mem_cons.2 ⟨subd6_8_379, List.forall_mem_cons.2 ⟨subd6_8_380, List.forall_mem_cons.2 ⟨subd6_8_381, List.forall_mem_cons.2 ⟨subd6_8_382, List.forall_mem_cons.2 ⟨subd6_8_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_8_384 : subd6_8 [1, 1, 8] = true := by decide +kernel
theorem subd6_8_385 : subd6_8 [1, 1, 9] = true := by decide +kernel
theorem subd6_8_386 : subd6_8 [1, 1, 10] = true := by decide +kernel
theorem subd6_8_387 : subd6_8 [1, 1, 11] = true := by decide +kernel
theorem subd6_8_388 : subd6_8 [1, 1, 12] = true := by decide +kernel
theorem subd6_8_389 : subd6_8 [1, 1, 13] = true := by decide +kernel
theorem subd6_8_390 : subd6_8 [1, 1, 14] = true := by decide +kernel
theorem subd6_8_391 : subd6_8 [1, 1, 15] = true := by decide +kernel
theorem subd6_8_392 : subd6_8 [1, 1, 16] = true := by decide +kernel
theorem subd6_8_393 : subd6_8 [1, 1, 17] = true := by decide +kernel
theorem subd6_8_394 : subd6_8 [1, 1, 18] = true := by decide +kernel
theorem subd6_8_395 : subd6_8 [1, 1, 19] = true := by decide +kernel
theorem subd6_8_396 : subd6_8 [1, 1, 20] = true := by decide +kernel
theorem sbd6_8_12 : ∀ q ∈ blkd6_8_12, subd6_8 q = true := by
  unfold blkd6_8_12
  exact List.forall_mem_cons.2 ⟨subd6_8_384, List.forall_mem_cons.2 ⟨subd6_8_385, List.forall_mem_cons.2 ⟨subd6_8_386, List.forall_mem_cons.2 ⟨subd6_8_387, List.forall_mem_cons.2 ⟨subd6_8_388, List.forall_mem_cons.2 ⟨subd6_8_389, List.forall_mem_cons.2 ⟨subd6_8_390, List.forall_mem_cons.2 ⟨subd6_8_391, List.forall_mem_cons.2 ⟨subd6_8_392, List.forall_mem_cons.2 ⟨subd6_8_393, List.forall_mem_cons.2 ⟨subd6_8_394, List.forall_mem_cons.2 ⟨subd6_8_395, List.forall_mem_cons.2 ⟨subd6_8_396, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_9 : ldCheck G d6_9.U d6_9.ms ldd6_9 = true := by decide +kernel
theorem pre_okd6_9 : subPre G cell6 d6_9 = true := by decide +kernel
theorem subd6_9_0 : subd6_9 [-5, -4] = true := by decide +kernel
theorem subd6_9_1 : subd6_9 [-5, -3] = true := by decide +kernel
theorem subd6_9_2 : subd6_9 [-5, -2] = true := by decide +kernel
theorem subd6_9_3 : subd6_9 [-5, -1] = true := by decide +kernel
theorem subd6_9_4 : subd6_9 [-5, 0] = true := by decide +kernel
theorem subd6_9_5 : subd6_9 [-5, 1] = true := by decide +kernel
theorem subd6_9_6 : subd6_9 [-5, 2] = true := by decide +kernel
theorem subd6_9_7 : subd6_9 [-5, 3] = true := by decide +kernel
theorem subd6_9_8 : subd6_9 [-4, -5] = true := by decide +kernel
theorem subd6_9_9 : subd6_9 [-4, -4] = true := by decide +kernel
theorem subd6_9_10 : subd6_9 [-4, -3] = true := by decide +kernel
theorem subd6_9_11 : subd6_9 [-4, -2] = true := by decide +kernel
theorem subd6_9_12 : subd6_9 [-4, -1] = true := by decide +kernel
theorem subd6_9_13 : subd6_9 [-4, 0] = true := by decide +kernel
theorem subd6_9_14 : subd6_9 [-4, 1] = true := by decide +kernel
theorem subd6_9_15 : subd6_9 [-4, 2] = true := by decide +kernel
theorem subd6_9_16 : subd6_9 [-4, 3] = true := by decide +kernel
theorem subd6_9_17 : subd6_9 [-4, 4] = true := by decide +kernel
theorem subd6_9_18 : subd6_9 [-3, -6] = true := by decide +kernel
theorem subd6_9_19 : subd6_9 [-3, -5] = true := by decide +kernel
theorem subd6_9_20 : subd6_9 [-3, -4] = true := by decide +kernel
theorem subd6_9_21 : subd6_9 [-3, -3] = true := by decide +kernel
theorem subd6_9_22 : subd6_9 [-3, -2, -8] = true := by decide +kernel
theorem subd6_9_23 : subd6_9 [-3, -2, -7] = true := by decide +kernel
theorem subd6_9_24 : subd6_9 [-3, -2, -6] = true := by decide +kernel
theorem subd6_9_25 : subd6_9 [-3, -2, -5] = true := by decide +kernel
theorem subd6_9_26 : subd6_9 [-3, -2, -4] = true := by decide +kernel
theorem subd6_9_27 : subd6_9 [-3, -2, -3] = true := by decide +kernel
theorem subd6_9_28 : subd6_9 [-3, -2, -2] = true := by decide +kernel
theorem subd6_9_29 : subd6_9 [-3, -2, -1] = true := by decide +kernel
theorem subd6_9_30 : subd6_9 [-3, -2, 0] = true := by decide +kernel
theorem subd6_9_31 : subd6_9 [-3, -2, 1] = true := by decide +kernel
theorem sbd6_9_0 : ∀ q ∈ blkd6_9_0, subd6_9 q = true := by
  unfold blkd6_9_0
  exact List.forall_mem_cons.2 ⟨subd6_9_0, List.forall_mem_cons.2 ⟨subd6_9_1, List.forall_mem_cons.2 ⟨subd6_9_2, List.forall_mem_cons.2 ⟨subd6_9_3, List.forall_mem_cons.2 ⟨subd6_9_4, List.forall_mem_cons.2 ⟨subd6_9_5, List.forall_mem_cons.2 ⟨subd6_9_6, List.forall_mem_cons.2 ⟨subd6_9_7, List.forall_mem_cons.2 ⟨subd6_9_8, List.forall_mem_cons.2 ⟨subd6_9_9, List.forall_mem_cons.2 ⟨subd6_9_10, List.forall_mem_cons.2 ⟨subd6_9_11, List.forall_mem_cons.2 ⟨subd6_9_12, List.forall_mem_cons.2 ⟨subd6_9_13, List.forall_mem_cons.2 ⟨subd6_9_14, List.forall_mem_cons.2 ⟨subd6_9_15, List.forall_mem_cons.2 ⟨subd6_9_16, List.forall_mem_cons.2 ⟨subd6_9_17, List.forall_mem_cons.2 ⟨subd6_9_18, List.forall_mem_cons.2 ⟨subd6_9_19, List.forall_mem_cons.2 ⟨subd6_9_20, List.forall_mem_cons.2 ⟨subd6_9_21, List.forall_mem_cons.2 ⟨subd6_9_22, List.forall_mem_cons.2 ⟨subd6_9_23, List.forall_mem_cons.2 ⟨subd6_9_24, List.forall_mem_cons.2 ⟨subd6_9_25, List.forall_mem_cons.2 ⟨subd6_9_26, List.forall_mem_cons.2 ⟨subd6_9_27, List.forall_mem_cons.2 ⟨subd6_9_28, List.forall_mem_cons.2 ⟨subd6_9_29, List.forall_mem_cons.2 ⟨subd6_9_30, List.forall_mem_cons.2 ⟨subd6_9_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_9_32 : subd6_9 [-3, -2, 2] = true := by decide +kernel
theorem subd6_9_33 : subd6_9 [-3, -2, 3] = true := by decide +kernel
theorem subd6_9_34 : subd6_9 [-3, -2, 4] = true := by decide +kernel
theorem subd6_9_35 : subd6_9 [-3, -2, 5] = true := by decide +kernel
theorem subd6_9_36 : subd6_9 [-3, -1, -9] = true := by decide +kernel
theorem subd6_9_37 : subd6_9 [-3, -1, -8] = true := by decide +kernel
theorem subd6_9_38 : subd6_9 [-3, -1, -7] = true := by decide +kernel
theorem subd6_9_39 : subd6_9 [-3, -1, -6] = true := by decide +kernel
theorem subd6_9_40 : subd6_9 [-3, -1, -5] = true := by decide +kernel
theorem subd6_9_41 : subd6_9 [-3, -1, -4] = true := by decide +kernel
theorem subd6_9_42 : subd6_9 [-3, -1, -3] = true := by decide +kernel
theorem subd6_9_43 : subd6_9 [-3, -1, -2] = true := by decide +kernel
theorem subd6_9_44 : subd6_9 [-3, -1, -1] = true := by decide +kernel
theorem subd6_9_45 : subd6_9 [-3, -1, 0] = true := by decide +kernel
theorem subd6_9_46 : subd6_9 [-3, -1, 1] = true := by decide +kernel
theorem subd6_9_47 : subd6_9 [-3, -1, 2] = true := by decide +kernel
theorem subd6_9_48 : subd6_9 [-3, -1, 3] = true := by decide +kernel
theorem subd6_9_49 : subd6_9 [-3, -1, 4] = true := by decide +kernel
theorem subd6_9_50 : subd6_9 [-3, -1, 5] = true := by decide +kernel
theorem subd6_9_51 : subd6_9 [-3, 0, -9] = true := by decide +kernel
theorem subd6_9_52 : subd6_9 [-3, 0, -8] = true := by decide +kernel
theorem subd6_9_53 : subd6_9 [-3, 0, -7] = true := by decide +kernel
theorem subd6_9_54 : subd6_9 [-3, 0, -6] = true := by decide +kernel
theorem subd6_9_55 : subd6_9 [-3, 0, -5] = true := by decide +kernel
theorem subd6_9_56 : subd6_9 [-3, 0, -4] = true := by decide +kernel
theorem subd6_9_57 : subd6_9 [-3, 0, -3] = true := by decide +kernel
theorem subd6_9_58 : subd6_9 [-3, 0, -2] = true := by decide +kernel
theorem subd6_9_59 : subd6_9 [-3, 0, -1] = true := by decide +kernel
theorem subd6_9_60 : subd6_9 [-3, 0, 0] = true := by decide +kernel
theorem subd6_9_61 : subd6_9 [-3, 0, 1] = true := by decide +kernel
theorem subd6_9_62 : subd6_9 [-3, 0, 2] = true := by decide +kernel
theorem subd6_9_63 : subd6_9 [-3, 0, 3] = true := by decide +kernel
theorem sbd6_9_1 : ∀ q ∈ blkd6_9_1, subd6_9 q = true := by
  unfold blkd6_9_1
  exact List.forall_mem_cons.2 ⟨subd6_9_32, List.forall_mem_cons.2 ⟨subd6_9_33, List.forall_mem_cons.2 ⟨subd6_9_34, List.forall_mem_cons.2 ⟨subd6_9_35, List.forall_mem_cons.2 ⟨subd6_9_36, List.forall_mem_cons.2 ⟨subd6_9_37, List.forall_mem_cons.2 ⟨subd6_9_38, List.forall_mem_cons.2 ⟨subd6_9_39, List.forall_mem_cons.2 ⟨subd6_9_40, List.forall_mem_cons.2 ⟨subd6_9_41, List.forall_mem_cons.2 ⟨subd6_9_42, List.forall_mem_cons.2 ⟨subd6_9_43, List.forall_mem_cons.2 ⟨subd6_9_44, List.forall_mem_cons.2 ⟨subd6_9_45, List.forall_mem_cons.2 ⟨subd6_9_46, List.forall_mem_cons.2 ⟨subd6_9_47, List.forall_mem_cons.2 ⟨subd6_9_48, List.forall_mem_cons.2 ⟨subd6_9_49, List.forall_mem_cons.2 ⟨subd6_9_50, List.forall_mem_cons.2 ⟨subd6_9_51, List.forall_mem_cons.2 ⟨subd6_9_52, List.forall_mem_cons.2 ⟨subd6_9_53, List.forall_mem_cons.2 ⟨subd6_9_54, List.forall_mem_cons.2 ⟨subd6_9_55, List.forall_mem_cons.2 ⟨subd6_9_56, List.forall_mem_cons.2 ⟨subd6_9_57, List.forall_mem_cons.2 ⟨subd6_9_58, List.forall_mem_cons.2 ⟨subd6_9_59, List.forall_mem_cons.2 ⟨subd6_9_60, List.forall_mem_cons.2 ⟨subd6_9_61, List.forall_mem_cons.2 ⟨subd6_9_62, List.forall_mem_cons.2 ⟨subd6_9_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C124
