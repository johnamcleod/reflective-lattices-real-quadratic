import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd4_5_288 : subd4_5 [1, 0, 1] = true := by decide +kernel
theorem subd4_5_289 : subd4_5 [1, 0, 2] = true := by decide +kernel
theorem subd4_5_290 : subd4_5 [1, 0, 3] = true := by decide +kernel
theorem subd4_5_291 : subd4_5 [1, 0, 4] = true := by decide +kernel
theorem subd4_5_292 : subd4_5 [1, 0, 5] = true := by decide +kernel
theorem subd4_5_293 : subd4_5 [1, 0, 6] = true := by decide +kernel
theorem subd4_5_294 : subd4_5 [1, 0, 7] = true := by decide +kernel
theorem subd4_5_295 : subd4_5 [1, 0, 8] = true := by decide +kernel
theorem subd4_5_296 : subd4_5 [1, 0, 9] = true := by decide +kernel
theorem subd4_5_297 : subd4_5 [1, 0, 10] = true := by decide +kernel
theorem subd4_5_298 : subd4_5 [1, 0, 11] = true := by decide +kernel
theorem subd4_5_299 : subd4_5 [1, 1, -11] = true := by decide +kernel
theorem subd4_5_300 : subd4_5 [1, 1, -10] = true := by decide +kernel
theorem subd4_5_301 : subd4_5 [1, 1, -9] = true := by decide +kernel
theorem subd4_5_302 : subd4_5 [1, 1, -8] = true := by decide +kernel
theorem subd4_5_303 : subd4_5 [1, 1, -7] = true := by decide +kernel
theorem subd4_5_304 : subd4_5 [1, 1, -6] = true := by decide +kernel
theorem subd4_5_305 : subd4_5 [1, 1, -5] = true := by decide +kernel
theorem subd4_5_306 : subd4_5 [1, 1, -4] = true := by decide +kernel
theorem subd4_5_307 : subd4_5 [1, 1, -3] = true := by decide +kernel
theorem subd4_5_308 : subd4_5 [1, 1, -2] = true := by decide +kernel
theorem subd4_5_309 : subd4_5 [1, 1, -1] = true := by decide +kernel
theorem subd4_5_310 : subd4_5 [1, 1, 0] = true := by decide +kernel
theorem subd4_5_311 : subd4_5 [1, 1, 1] = true := by decide +kernel
theorem subd4_5_312 : subd4_5 [1, 1, 2] = true := by decide +kernel
theorem subd4_5_313 : subd4_5 [1, 1, 3] = true := by decide +kernel
theorem subd4_5_314 : subd4_5 [1, 1, 4] = true := by decide +kernel
theorem subd4_5_315 : subd4_5 [1, 1, 5] = true := by decide +kernel
theorem subd4_5_316 : subd4_5 [1, 1, 6] = true := by decide +kernel
theorem subd4_5_317 : subd4_5 [1, 1, 7] = true := by decide +kernel
theorem subd4_5_318 : subd4_5 [1, 1, 8] = true := by decide +kernel
theorem subd4_5_319 : subd4_5 [1, 1, 9] = true := by decide +kernel
theorem sbd4_5_9 : ∀ q ∈ blkd4_5_9, subd4_5 q = true := by
  unfold blkd4_5_9
  exact List.forall_mem_cons.2 ⟨subd4_5_288, List.forall_mem_cons.2 ⟨subd4_5_289, List.forall_mem_cons.2 ⟨subd4_5_290, List.forall_mem_cons.2 ⟨subd4_5_291, List.forall_mem_cons.2 ⟨subd4_5_292, List.forall_mem_cons.2 ⟨subd4_5_293, List.forall_mem_cons.2 ⟨subd4_5_294, List.forall_mem_cons.2 ⟨subd4_5_295, List.forall_mem_cons.2 ⟨subd4_5_296, List.forall_mem_cons.2 ⟨subd4_5_297, List.forall_mem_cons.2 ⟨subd4_5_298, List.forall_mem_cons.2 ⟨subd4_5_299, List.forall_mem_cons.2 ⟨subd4_5_300, List.forall_mem_cons.2 ⟨subd4_5_301, List.forall_mem_cons.2 ⟨subd4_5_302, List.forall_mem_cons.2 ⟨subd4_5_303, List.forall_mem_cons.2 ⟨subd4_5_304, List.forall_mem_cons.2 ⟨subd4_5_305, List.forall_mem_cons.2 ⟨subd4_5_306, List.forall_mem_cons.2 ⟨subd4_5_307, List.forall_mem_cons.2 ⟨subd4_5_308, List.forall_mem_cons.2 ⟨subd4_5_309, List.forall_mem_cons.2 ⟨subd4_5_310, List.forall_mem_cons.2 ⟨subd4_5_311, List.forall_mem_cons.2 ⟨subd4_5_312, List.forall_mem_cons.2 ⟨subd4_5_313, List.forall_mem_cons.2 ⟨subd4_5_314, List.forall_mem_cons.2 ⟨subd4_5_315, List.forall_mem_cons.2 ⟨subd4_5_316, List.forall_mem_cons.2 ⟨subd4_5_317, List.forall_mem_cons.2 ⟨subd4_5_318, List.forall_mem_cons.2 ⟨subd4_5_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_5_320 : subd4_5 [1, 1, 10] = true := by decide +kernel
theorem subd4_5_321 : subd4_5 [1, 1, 11] = true := by decide +kernel
theorem subd4_5_322 : subd4_5 [1, 2, -8] = true := by decide +kernel
theorem subd4_5_323 : subd4_5 [1, 2, -7] = true := by decide +kernel
theorem subd4_5_324 : subd4_5 [1, 2, -6] = true := by decide +kernel
theorem subd4_5_325 : subd4_5 [1, 2, -5] = true := by decide +kernel
theorem subd4_5_326 : subd4_5 [1, 2, -4] = true := by decide +kernel
theorem subd4_5_327 : subd4_5 [1, 2, -3] = true := by decide +kernel
theorem subd4_5_328 : subd4_5 [1, 2, -2] = true := by decide +kernel
theorem subd4_5_329 : subd4_5 [1, 2, -1] = true := by decide +kernel
theorem subd4_5_330 : subd4_5 [1, 2, 0] = true := by decide +kernel
theorem subd4_5_331 : subd4_5 [1, 2, 1] = true := by decide +kernel
theorem subd4_5_332 : subd4_5 [1, 2, 2] = true := by decide +kernel
theorem subd4_5_333 : subd4_5 [1, 2, 3] = true := by decide +kernel
theorem subd4_5_334 : subd4_5 [1, 2, 4] = true := by decide +kernel
theorem subd4_5_335 : subd4_5 [1, 2, 5] = true := by decide +kernel
theorem subd4_5_336 : subd4_5 [1, 2, 6] = true := by decide +kernel
theorem subd4_5_337 : subd4_5 [1, 2, 7] = true := by decide +kernel
theorem subd4_5_338 : subd4_5 [1, 2, 8] = true := by decide +kernel
theorem subd4_5_339 : subd4_5 [2, -2] = true := by decide +kernel
theorem subd4_5_340 : subd4_5 [2, -1, -7] = true := by decide +kernel
theorem subd4_5_341 : subd4_5 [2, -1, -6] = true := by decide +kernel
theorem subd4_5_342 : subd4_5 [2, -1, -5] = true := by decide +kernel
theorem subd4_5_343 : subd4_5 [2, -1, -4] = true := by decide +kernel
theorem subd4_5_344 : subd4_5 [2, -1, -3] = true := by decide +kernel
theorem subd4_5_345 : subd4_5 [2, -1, -2] = true := by decide +kernel
theorem subd4_5_346 : subd4_5 [2, -1, -1] = true := by decide +kernel
theorem subd4_5_347 : subd4_5 [2, -1, 0] = true := by decide +kernel
theorem subd4_5_348 : subd4_5 [2, -1, 1] = true := by decide +kernel
theorem subd4_5_349 : subd4_5 [2, -1, 2] = true := by decide +kernel
theorem subd4_5_350 : subd4_5 [2, -1, 3] = true := by decide +kernel
theorem subd4_5_351 : subd4_5 [2, -1, 4] = true := by decide +kernel
theorem sbd4_5_10 : ∀ q ∈ blkd4_5_10, subd4_5 q = true := by
  unfold blkd4_5_10
  exact List.forall_mem_cons.2 ⟨subd4_5_320, List.forall_mem_cons.2 ⟨subd4_5_321, List.forall_mem_cons.2 ⟨subd4_5_322, List.forall_mem_cons.2 ⟨subd4_5_323, List.forall_mem_cons.2 ⟨subd4_5_324, List.forall_mem_cons.2 ⟨subd4_5_325, List.forall_mem_cons.2 ⟨subd4_5_326, List.forall_mem_cons.2 ⟨subd4_5_327, List.forall_mem_cons.2 ⟨subd4_5_328, List.forall_mem_cons.2 ⟨subd4_5_329, List.forall_mem_cons.2 ⟨subd4_5_330, List.forall_mem_cons.2 ⟨subd4_5_331, List.forall_mem_cons.2 ⟨subd4_5_332, List.forall_mem_cons.2 ⟨subd4_5_333, List.forall_mem_cons.2 ⟨subd4_5_334, List.forall_mem_cons.2 ⟨subd4_5_335, List.forall_mem_cons.2 ⟨subd4_5_336, List.forall_mem_cons.2 ⟨subd4_5_337, List.forall_mem_cons.2 ⟨subd4_5_338, List.forall_mem_cons.2 ⟨subd4_5_339, List.forall_mem_cons.2 ⟨subd4_5_340, List.forall_mem_cons.2 ⟨subd4_5_341, List.forall_mem_cons.2 ⟨subd4_5_342, List.forall_mem_cons.2 ⟨subd4_5_343, List.forall_mem_cons.2 ⟨subd4_5_344, List.forall_mem_cons.2 ⟨subd4_5_345, List.forall_mem_cons.2 ⟨subd4_5_346, List.forall_mem_cons.2 ⟨subd4_5_347, List.forall_mem_cons.2 ⟨subd4_5_348, List.forall_mem_cons.2 ⟨subd4_5_349, List.forall_mem_cons.2 ⟨subd4_5_350, List.forall_mem_cons.2 ⟨subd4_5_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_5_352 : subd4_5 [2, -1, 5] = true := by decide +kernel
theorem subd4_5_353 : subd4_5 [2, -1, 6] = true := by decide +kernel
theorem subd4_5_354 : subd4_5 [2, -1, 7] = true := by decide +kernel
theorem subd4_5_355 : subd4_5 [2, 0, -9] = true := by decide +kernel
theorem subd4_5_356 : subd4_5 [2, 0, -8] = true := by decide +kernel
theorem subd4_5_357 : subd4_5 [2, 0, -7] = true := by decide +kernel
theorem subd4_5_358 : subd4_5 [2, 0, -6] = true := by decide +kernel
theorem subd4_5_359 : subd4_5 [2, 0, -5] = true := by decide +kernel
theorem subd4_5_360 : subd4_5 [2, 0, -4] = true := by decide +kernel
theorem subd4_5_361 : subd4_5 [2, 0, -3] = true := by decide +kernel
theorem subd4_5_362 : subd4_5 [2, 0, -2] = true := by decide +kernel
theorem subd4_5_363 : subd4_5 [2, 0, -1] = true := by decide +kernel
theorem subd4_5_364 : subd4_5 [2, 0, 0] = true := by decide +kernel
theorem subd4_5_365 : subd4_5 [2, 0, 1] = true := by decide +kernel
theorem subd4_5_366 : subd4_5 [2, 0, 2] = true := by decide +kernel
theorem subd4_5_367 : subd4_5 [2, 0, 3] = true := by decide +kernel
theorem subd4_5_368 : subd4_5 [2, 0, 4] = true := by decide +kernel
theorem subd4_5_369 : subd4_5 [2, 0, 5] = true := by decide +kernel
theorem subd4_5_370 : subd4_5 [2, 0, 6] = true := by decide +kernel
theorem subd4_5_371 : subd4_5 [2, 0, 7] = true := by decide +kernel
theorem subd4_5_372 : subd4_5 [2, 0, 8] = true := by decide +kernel
theorem subd4_5_373 : subd4_5 [2, 0, 9] = true := by decide +kernel
theorem subd4_5_374 : subd4_5 [2, 0, 10] = true := by decide +kernel
theorem subd4_5_375 : subd4_5 [2, 1, -9] = true := by decide +kernel
theorem subd4_5_376 : subd4_5 [2, 1, -8] = true := by decide +kernel
theorem subd4_5_377 : subd4_5 [2, 1, -7] = true := by decide +kernel
theorem subd4_5_378 : subd4_5 [2, 1, -6] = true := by decide +kernel
theorem subd4_5_379 : subd4_5 [2, 1, -5] = true := by decide +kernel
theorem subd4_5_380 : subd4_5 [2, 1, -4] = true := by decide +kernel
theorem subd4_5_381 : subd4_5 [2, 1, -3] = true := by decide +kernel
theorem subd4_5_382 : subd4_5 [2, 1, -2] = true := by decide +kernel
theorem subd4_5_383 : subd4_5 [2, 1, -1] = true := by decide +kernel
theorem sbd4_5_11 : ∀ q ∈ blkd4_5_11, subd4_5 q = true := by
  unfold blkd4_5_11
  exact List.forall_mem_cons.2 ⟨subd4_5_352, List.forall_mem_cons.2 ⟨subd4_5_353, List.forall_mem_cons.2 ⟨subd4_5_354, List.forall_mem_cons.2 ⟨subd4_5_355, List.forall_mem_cons.2 ⟨subd4_5_356, List.forall_mem_cons.2 ⟨subd4_5_357, List.forall_mem_cons.2 ⟨subd4_5_358, List.forall_mem_cons.2 ⟨subd4_5_359, List.forall_mem_cons.2 ⟨subd4_5_360, List.forall_mem_cons.2 ⟨subd4_5_361, List.forall_mem_cons.2 ⟨subd4_5_362, List.forall_mem_cons.2 ⟨subd4_5_363, List.forall_mem_cons.2 ⟨subd4_5_364, List.forall_mem_cons.2 ⟨subd4_5_365, List.forall_mem_cons.2 ⟨subd4_5_366, List.forall_mem_cons.2 ⟨subd4_5_367, List.forall_mem_cons.2 ⟨subd4_5_368, List.forall_mem_cons.2 ⟨subd4_5_369, List.forall_mem_cons.2 ⟨subd4_5_370, List.forall_mem_cons.2 ⟨subd4_5_371, List.forall_mem_cons.2 ⟨subd4_5_372, List.forall_mem_cons.2 ⟨subd4_5_373, List.forall_mem_cons.2 ⟨subd4_5_374, List.forall_mem_cons.2 ⟨subd4_5_375, List.forall_mem_cons.2 ⟨subd4_5_376, List.forall_mem_cons.2 ⟨subd4_5_377, List.forall_mem_cons.2 ⟨subd4_5_378, List.forall_mem_cons.2 ⟨subd4_5_379, List.forall_mem_cons.2 ⟨subd4_5_380, List.forall_mem_cons.2 ⟨subd4_5_381, List.forall_mem_cons.2 ⟨subd4_5_382, List.forall_mem_cons.2 ⟨subd4_5_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_5_384 : subd4_5 [2, 1, 0] = true := by decide +kernel
theorem subd4_5_385 : subd4_5 [2, 1, 1] = true := by decide +kernel
theorem subd4_5_386 : subd4_5 [2, 1, 2] = true := by decide +kernel
theorem subd4_5_387 : subd4_5 [2, 1, 3] = true := by decide +kernel
theorem subd4_5_388 : subd4_5 [2, 1, 4] = true := by decide +kernel
theorem subd4_5_389 : subd4_5 [2, 1, 5] = true := by decide +kernel
theorem subd4_5_390 : subd4_5 [2, 1, 6] = true := by decide +kernel
theorem subd4_5_391 : subd4_5 [2, 1, 7] = true := by decide +kernel
theorem subd4_5_392 : subd4_5 [2, 1, 8] = true := by decide +kernel
theorem subd4_5_393 : subd4_5 [2, 1, 9] = true := by decide +kernel
theorem subd4_5_394 : subd4_5 [2, 1, 10] = true := by decide +kernel
theorem subd4_5_395 : subd4_5 [2, 2] = true := by decide +kernel
theorem subd4_5_396 : subd4_5 [3] = true := by decide +kernel
theorem sbd4_5_12 : ∀ q ∈ blkd4_5_12, subd4_5 q = true := by
  unfold blkd4_5_12
  exact List.forall_mem_cons.2 ⟨subd4_5_384, List.forall_mem_cons.2 ⟨subd4_5_385, List.forall_mem_cons.2 ⟨subd4_5_386, List.forall_mem_cons.2 ⟨subd4_5_387, List.forall_mem_cons.2 ⟨subd4_5_388, List.forall_mem_cons.2 ⟨subd4_5_389, List.forall_mem_cons.2 ⟨subd4_5_390, List.forall_mem_cons.2 ⟨subd4_5_391, List.forall_mem_cons.2 ⟨subd4_5_392, List.forall_mem_cons.2 ⟨subd4_5_393, List.forall_mem_cons.2 ⟨subd4_5_394, List.forall_mem_cons.2 ⟨subd4_5_395, List.forall_mem_cons.2 ⟨subd4_5_396, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd4_6 : ldCheck G d4_6.U d4_6.ms ldd4_6 = true := by decide +kernel
theorem pre_okd4_6 : subPre G cell4 d4_6 = true := by decide +kernel
theorem subd4_6_0 : subd4_6 [-5] = true := by decide +kernel
theorem subd4_6_1 : subd4_6 [-4, -3] = true := by decide +kernel
theorem subd4_6_2 : subd4_6 [-4, -2] = true := by decide +kernel
theorem subd4_6_3 : subd4_6 [-4, -1] = true := by decide +kernel
theorem subd4_6_4 : subd4_6 [-4, 0] = true := by decide +kernel
theorem subd4_6_5 : subd4_6 [-4, 1] = true := by decide +kernel
theorem subd4_6_6 : subd4_6 [-4, 2] = true := by decide +kernel
theorem subd4_6_7 : subd4_6 [-4, 3] = true := by decide +kernel
theorem subd4_6_8 : subd4_6 [-3, -4] = true := by decide +kernel
theorem subd4_6_9 : subd4_6 [-3, -3] = true := by decide +kernel
theorem subd4_6_10 : subd4_6 [-3, -2] = true := by decide +kernel
theorem subd4_6_11 : subd4_6 [-3, -1] = true := by decide +kernel
theorem subd4_6_12 : subd4_6 [-3, 0] = true := by decide +kernel
theorem subd4_6_13 : subd4_6 [-3, 1] = true := by decide +kernel
theorem subd4_6_14 : subd4_6 [-3, 2] = true := by decide +kernel
theorem subd4_6_15 : subd4_6 [-3, 3] = true := by decide +kernel
theorem subd4_6_16 : subd4_6 [-3, 4] = true := by decide +kernel
theorem subd4_6_17 : subd4_6 [-2, -5] = true := by decide +kernel
theorem subd4_6_18 : subd4_6 [-2, -4] = true := by decide +kernel
theorem subd4_6_19 : subd4_6 [-2, -3] = true := by decide +kernel
theorem subd4_6_20 : subd4_6 [-2, -2] = true := by decide +kernel
theorem subd4_6_21 : subd4_6 [-2, -1] = true := by decide +kernel
theorem subd4_6_22 : subd4_6 [-2, 0, -7] = true := by decide +kernel
theorem subd4_6_23 : subd4_6 [-2, 0, -6] = true := by decide +kernel
theorem subd4_6_24 : subd4_6 [-2, 0, -5] = true := by decide +kernel
theorem subd4_6_25 : subd4_6 [-2, 0, -4] = true := by decide +kernel
theorem subd4_6_26 : subd4_6 [-2, 0, -3] = true := by decide +kernel
theorem subd4_6_27 : subd4_6 [-2, 0, -2] = true := by decide +kernel
theorem subd4_6_28 : subd4_6 [-2, 0, -1] = true := by decide +kernel
theorem subd4_6_29 : subd4_6 [-2, 0, 0] = true := by decide +kernel
theorem subd4_6_30 : subd4_6 [-2, 0, 1] = true := by decide +kernel
theorem subd4_6_31 : subd4_6 [-2, 0, 2] = true := by decide +kernel
theorem sbd4_6_0 : ∀ q ∈ blkd4_6_0, subd4_6 q = true := by
  unfold blkd4_6_0
  exact List.forall_mem_cons.2 ⟨subd4_6_0, List.forall_mem_cons.2 ⟨subd4_6_1, List.forall_mem_cons.2 ⟨subd4_6_2, List.forall_mem_cons.2 ⟨subd4_6_3, List.forall_mem_cons.2 ⟨subd4_6_4, List.forall_mem_cons.2 ⟨subd4_6_5, List.forall_mem_cons.2 ⟨subd4_6_6, List.forall_mem_cons.2 ⟨subd4_6_7, List.forall_mem_cons.2 ⟨subd4_6_8, List.forall_mem_cons.2 ⟨subd4_6_9, List.forall_mem_cons.2 ⟨subd4_6_10, List.forall_mem_cons.2 ⟨subd4_6_11, List.forall_mem_cons.2 ⟨subd4_6_12, List.forall_mem_cons.2 ⟨subd4_6_13, List.forall_mem_cons.2 ⟨subd4_6_14, List.forall_mem_cons.2 ⟨subd4_6_15, List.forall_mem_cons.2 ⟨subd4_6_16, List.forall_mem_cons.2 ⟨subd4_6_17, List.forall_mem_cons.2 ⟨subd4_6_18, List.forall_mem_cons.2 ⟨subd4_6_19, List.forall_mem_cons.2 ⟨subd4_6_20, List.forall_mem_cons.2 ⟨subd4_6_21, List.forall_mem_cons.2 ⟨subd4_6_22, List.forall_mem_cons.2 ⟨subd4_6_23, List.forall_mem_cons.2 ⟨subd4_6_24, List.forall_mem_cons.2 ⟨subd4_6_25, List.forall_mem_cons.2 ⟨subd4_6_26, List.forall_mem_cons.2 ⟨subd4_6_27, List.forall_mem_cons.2 ⟨subd4_6_28, List.forall_mem_cons.2 ⟨subd4_6_29, List.forall_mem_cons.2 ⟨subd4_6_30, List.forall_mem_cons.2 ⟨subd4_6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_6_32 : subd4_6 [-2, 0, 3] = true := by decide +kernel
theorem subd4_6_33 : subd4_6 [-2, 0, 4] = true := by decide +kernel
theorem subd4_6_34 : subd4_6 [-2, 0, 5] = true := by decide +kernel
theorem subd4_6_35 : subd4_6 [-2, 0, 6] = true := by decide +kernel
theorem subd4_6_36 : subd4_6 [-2, 1, -7] = true := by decide +kernel
theorem subd4_6_37 : subd4_6 [-2, 1, -6] = true := by decide +kernel
theorem subd4_6_38 : subd4_6 [-2, 1, -5] = true := by decide +kernel
theorem subd4_6_39 : subd4_6 [-2, 1, -4] = true := by decide +kernel
theorem subd4_6_40 : subd4_6 [-2, 1, -3] = true := by decide +kernel
theorem subd4_6_41 : subd4_6 [-2, 1, -2] = true := by decide +kernel
theorem subd4_6_42 : subd4_6 [-2, 1, -1] = true := by decide +kernel
theorem subd4_6_43 : subd4_6 [-2, 1, 0] = true := by decide +kernel
theorem subd4_6_44 : subd4_6 [-2, 1, 1] = true := by decide +kernel
theorem subd4_6_45 : subd4_6 [-2, 1, 2] = true := by decide +kernel
theorem subd4_6_46 : subd4_6 [-2, 1, 3] = true := by decide +kernel
theorem subd4_6_47 : subd4_6 [-2, 1, 4] = true := by decide +kernel
theorem subd4_6_48 : subd4_6 [-2, 1, 5] = true := by decide +kernel
theorem subd4_6_49 : subd4_6 [-2, 1, 6] = true := by decide +kernel
theorem subd4_6_50 : subd4_6 [-2, 2] = true := by decide +kernel
theorem subd4_6_51 : subd4_6 [-2, 3] = true := by decide +kernel
theorem subd4_6_52 : subd4_6 [-2, 4] = true := by decide +kernel
theorem subd4_6_53 : subd4_6 [-2, 5] = true := by decide +kernel
theorem subd4_6_54 : subd4_6 [-1, -6] = true := by decide +kernel
theorem subd4_6_55 : subd4_6 [-1, -5] = true := by decide +kernel
theorem subd4_6_56 : subd4_6 [-1, -4] = true := by decide +kernel
theorem subd4_6_57 : subd4_6 [-1, -3] = true := by decide +kernel
theorem subd4_6_58 : subd4_6 [-1, -2] = true := by decide +kernel
theorem subd4_6_59 : subd4_6 [-1, -1, -7] = true := by decide +kernel
theorem subd4_6_60 : subd4_6 [-1, -1, -6] = true := by decide +kernel
theorem subd4_6_61 : subd4_6 [-1, -1, -5] = true := by decide +kernel
theorem subd4_6_62 : subd4_6 [-1, -1, -4] = true := by decide +kernel
theorem subd4_6_63 : subd4_6 [-1, -1, -3] = true := by decide +kernel
theorem sbd4_6_1 : ∀ q ∈ blkd4_6_1, subd4_6 q = true := by
  unfold blkd4_6_1
  exact List.forall_mem_cons.2 ⟨subd4_6_32, List.forall_mem_cons.2 ⟨subd4_6_33, List.forall_mem_cons.2 ⟨subd4_6_34, List.forall_mem_cons.2 ⟨subd4_6_35, List.forall_mem_cons.2 ⟨subd4_6_36, List.forall_mem_cons.2 ⟨subd4_6_37, List.forall_mem_cons.2 ⟨subd4_6_38, List.forall_mem_cons.2 ⟨subd4_6_39, List.forall_mem_cons.2 ⟨subd4_6_40, List.forall_mem_cons.2 ⟨subd4_6_41, List.forall_mem_cons.2 ⟨subd4_6_42, List.forall_mem_cons.2 ⟨subd4_6_43, List.forall_mem_cons.2 ⟨subd4_6_44, List.forall_mem_cons.2 ⟨subd4_6_45, List.forall_mem_cons.2 ⟨subd4_6_46, List.forall_mem_cons.2 ⟨subd4_6_47, List.forall_mem_cons.2 ⟨subd4_6_48, List.forall_mem_cons.2 ⟨subd4_6_49, List.forall_mem_cons.2 ⟨subd4_6_50, List.forall_mem_cons.2 ⟨subd4_6_51, List.forall_mem_cons.2 ⟨subd4_6_52, List.forall_mem_cons.2 ⟨subd4_6_53, List.forall_mem_cons.2 ⟨subd4_6_54, List.forall_mem_cons.2 ⟨subd4_6_55, List.forall_mem_cons.2 ⟨subd4_6_56, List.forall_mem_cons.2 ⟨subd4_6_57, List.forall_mem_cons.2 ⟨subd4_6_58, List.forall_mem_cons.2 ⟨subd4_6_59, List.forall_mem_cons.2 ⟨subd4_6_60, List.forall_mem_cons.2 ⟨subd4_6_61, List.forall_mem_cons.2 ⟨subd4_6_62, List.forall_mem_cons.2 ⟨subd4_6_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_6_64 : subd4_6 [-1, -1, -2] = true := by decide +kernel
theorem subd4_6_65 : subd4_6 [-1, -1, -1] = true := by decide +kernel
theorem subd4_6_66 : subd4_6 [-1, -1, 0] = true := by decide +kernel
theorem subd4_6_67 : subd4_6 [-1, -1, 1] = true := by decide +kernel
theorem subd4_6_68 : subd4_6 [-1, -1, 2] = true := by decide +kernel
theorem subd4_6_69 : subd4_6 [-1, -1, 3] = true := by decide +kernel
theorem subd4_6_70 : subd4_6 [-1, -1, 4] = true := by decide +kernel
theorem subd4_6_71 : subd4_6 [-1, -1, 5] = true := by decide +kernel
theorem subd4_6_72 : subd4_6 [-1, -1, 6] = true := by decide +kernel
theorem subd4_6_73 : subd4_6 [-1, 0, -7] = true := by decide +kernel
theorem subd4_6_74 : subd4_6 [-1, 0, -6] = true := by decide +kernel
theorem subd4_6_75 : subd4_6 [-1, 0, -5] = true := by decide +kernel
theorem subd4_6_76 : subd4_6 [-1, 0, -4] = true := by decide +kernel
theorem subd4_6_77 : subd4_6 [-1, 0, -3] = true := by decide +kernel
theorem subd4_6_78 : subd4_6 [-1, 0, -2] = true := by decide +kernel
theorem subd4_6_79 : subd4_6 [-1, 0, -1] = true := by decide +kernel
theorem subd4_6_80 : subd4_6 [-1, 0, 0] = true := by decide +kernel
theorem subd4_6_81 : subd4_6 [-1, 0, 1] = true := by decide +kernel
theorem subd4_6_82 : subd4_6 [-1, 0, 2] = true := by decide +kernel
theorem subd4_6_83 : subd4_6 [-1, 0, 3] = true := by decide +kernel
theorem subd4_6_84 : subd4_6 [-1, 0, 4] = true := by decide +kernel
theorem subd4_6_85 : subd4_6 [-1, 0, 5] = true := by decide +kernel
theorem subd4_6_86 : subd4_6 [-1, 0, 6] = true := by decide +kernel
theorem subd4_6_87 : subd4_6 [-1, 1, -7] = true := by decide +kernel
theorem subd4_6_88 : subd4_6 [-1, 1, -6] = true := by decide +kernel
theorem subd4_6_89 : subd4_6 [-1, 1, -5] = true := by decide +kernel
theorem subd4_6_90 : subd4_6 [-1, 1, -4] = true := by decide +kernel
theorem subd4_6_91 : subd4_6 [-1, 1, -3] = true := by decide +kernel
theorem subd4_6_92 : subd4_6 [-1, 1, -2] = true := by decide +kernel
theorem subd4_6_93 : subd4_6 [-1, 1, -1] = true := by decide +kernel
theorem subd4_6_94 : subd4_6 [-1, 1, 0] = true := by decide +kernel
theorem subd4_6_95 : subd4_6 [-1, 1, 1] = true := by decide +kernel
theorem sbd4_6_2 : ∀ q ∈ blkd4_6_2, subd4_6 q = true := by
  unfold blkd4_6_2
  exact List.forall_mem_cons.2 ⟨subd4_6_64, List.forall_mem_cons.2 ⟨subd4_6_65, List.forall_mem_cons.2 ⟨subd4_6_66, List.forall_mem_cons.2 ⟨subd4_6_67, List.forall_mem_cons.2 ⟨subd4_6_68, List.forall_mem_cons.2 ⟨subd4_6_69, List.forall_mem_cons.2 ⟨subd4_6_70, List.forall_mem_cons.2 ⟨subd4_6_71, List.forall_mem_cons.2 ⟨subd4_6_72, List.forall_mem_cons.2 ⟨subd4_6_73, List.forall_mem_cons.2 ⟨subd4_6_74, List.forall_mem_cons.2 ⟨subd4_6_75, List.forall_mem_cons.2 ⟨subd4_6_76, List.forall_mem_cons.2 ⟨subd4_6_77, List.forall_mem_cons.2 ⟨subd4_6_78, List.forall_mem_cons.2 ⟨subd4_6_79, List.forall_mem_cons.2 ⟨subd4_6_80, List.forall_mem_cons.2 ⟨subd4_6_81, List.forall_mem_cons.2 ⟨subd4_6_82, List.forall_mem_cons.2 ⟨subd4_6_83, List.forall_mem_cons.2 ⟨subd4_6_84, List.forall_mem_cons.2 ⟨subd4_6_85, List.forall_mem_cons.2 ⟨subd4_6_86, List.forall_mem_cons.2 ⟨subd4_6_87, List.forall_mem_cons.2 ⟨subd4_6_88, List.forall_mem_cons.2 ⟨subd4_6_89, List.forall_mem_cons.2 ⟨subd4_6_90, List.forall_mem_cons.2 ⟨subd4_6_91, List.forall_mem_cons.2 ⟨subd4_6_92, List.forall_mem_cons.2 ⟨subd4_6_93, List.forall_mem_cons.2 ⟨subd4_6_94, List.forall_mem_cons.2 ⟨subd4_6_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_6_96 : subd4_6 [-1, 1, 2] = true := by decide +kernel
theorem subd4_6_97 : subd4_6 [-1, 1, 3] = true := by decide +kernel
theorem subd4_6_98 : subd4_6 [-1, 1, 4] = true := by decide +kernel
theorem subd4_6_99 : subd4_6 [-1, 1, 5] = true := by decide +kernel
theorem subd4_6_100 : subd4_6 [-1, 1, 6] = true := by decide +kernel
theorem subd4_6_101 : subd4_6 [-1, 2, -6] = true := by decide +kernel
theorem subd4_6_102 : subd4_6 [-1, 2, -5] = true := by decide +kernel
theorem subd4_6_103 : subd4_6 [-1, 2, -4] = true := by decide +kernel
theorem subd4_6_104 : subd4_6 [-1, 2, -3] = true := by decide +kernel
theorem subd4_6_105 : subd4_6 [-1, 2, -2] = true := by decide +kernel
theorem subd4_6_106 : subd4_6 [-1, 2, -1] = true := by decide +kernel
theorem subd4_6_107 : subd4_6 [-1, 2, 0] = true := by decide +kernel
theorem subd4_6_108 : subd4_6 [-1, 2, 1] = true := by decide +kernel
theorem subd4_6_109 : subd4_6 [-1, 2, 2] = true := by decide +kernel
theorem subd4_6_110 : subd4_6 [-1, 2, 3] = true := by decide +kernel
theorem subd4_6_111 : subd4_6 [-1, 2, 4] = true := by decide +kernel
theorem subd4_6_112 : subd4_6 [-1, 2, 5] = true := by decide +kernel
theorem subd4_6_113 : subd4_6 [-1, 2, 6] = true := by decide +kernel
theorem subd4_6_114 : subd4_6 [-1, 3] = true := by decide +kernel
theorem subd4_6_115 : subd4_6 [-1, 4] = true := by decide +kernel
theorem subd4_6_116 : subd4_6 [-1, 5] = true := by decide +kernel
theorem subd4_6_117 : subd4_6 [0, -6] = true := by decide +kernel
theorem subd4_6_118 : subd4_6 [0, -5] = true := by decide +kernel
theorem subd4_6_119 : subd4_6 [0, -4] = true := by decide +kernel
theorem subd4_6_120 : subd4_6 [0, -3] = true := by decide +kernel
theorem subd4_6_121 : subd4_6 [0, -2, -7] = true := by decide +kernel
theorem subd4_6_122 : subd4_6 [0, -2, -6] = true := by decide +kernel
theorem subd4_6_123 : subd4_6 [0, -2, -5] = true := by decide +kernel
theorem subd4_6_124 : subd4_6 [0, -2, -4] = true := by decide +kernel
theorem subd4_6_125 : subd4_6 [0, -2, -3] = true := by decide +kernel
theorem subd4_6_126 : subd4_6 [0, -2, -2] = true := by decide +kernel
theorem subd4_6_127 : subd4_6 [0, -2, -1] = true := by decide +kernel
theorem sbd4_6_3 : ∀ q ∈ blkd4_6_3, subd4_6 q = true := by
  unfold blkd4_6_3
  exact List.forall_mem_cons.2 ⟨subd4_6_96, List.forall_mem_cons.2 ⟨subd4_6_97, List.forall_mem_cons.2 ⟨subd4_6_98, List.forall_mem_cons.2 ⟨subd4_6_99, List.forall_mem_cons.2 ⟨subd4_6_100, List.forall_mem_cons.2 ⟨subd4_6_101, List.forall_mem_cons.2 ⟨subd4_6_102, List.forall_mem_cons.2 ⟨subd4_6_103, List.forall_mem_cons.2 ⟨subd4_6_104, List.forall_mem_cons.2 ⟨subd4_6_105, List.forall_mem_cons.2 ⟨subd4_6_106, List.forall_mem_cons.2 ⟨subd4_6_107, List.forall_mem_cons.2 ⟨subd4_6_108, List.forall_mem_cons.2 ⟨subd4_6_109, List.forall_mem_cons.2 ⟨subd4_6_110, List.forall_mem_cons.2 ⟨subd4_6_111, List.forall_mem_cons.2 ⟨subd4_6_112, List.forall_mem_cons.2 ⟨subd4_6_113, List.forall_mem_cons.2 ⟨subd4_6_114, List.forall_mem_cons.2 ⟨subd4_6_115, List.forall_mem_cons.2 ⟨subd4_6_116, List.forall_mem_cons.2 ⟨subd4_6_117, List.forall_mem_cons.2 ⟨subd4_6_118, List.forall_mem_cons.2 ⟨subd4_6_119, List.forall_mem_cons.2 ⟨subd4_6_120, List.forall_mem_cons.2 ⟨subd4_6_121, List.forall_mem_cons.2 ⟨subd4_6_122, List.forall_mem_cons.2 ⟨subd4_6_123, List.forall_mem_cons.2 ⟨subd4_6_124, List.forall_mem_cons.2 ⟨subd4_6_125, List.forall_mem_cons.2 ⟨subd4_6_126, List.forall_mem_cons.2 ⟨subd4_6_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_6_128 : subd4_6 [0, -2, 0] = true := by decide +kernel
theorem subd4_6_129 : subd4_6 [0, -2, 1] = true := by decide +kernel
theorem subd4_6_130 : subd4_6 [0, -2, 2] = true := by decide +kernel
theorem subd4_6_131 : subd4_6 [0, -2, 3] = true := by decide +kernel
theorem subd4_6_132 : subd4_6 [0, -2, 4] = true := by decide +kernel
theorem subd4_6_133 : subd4_6 [0, -2, 5] = true := by decide +kernel
theorem subd4_6_134 : subd4_6 [0, -1, -7] = true := by decide +kernel
theorem subd4_6_135 : subd4_6 [0, -1, -6] = true := by decide +kernel
theorem subd4_6_136 : subd4_6 [0, -1, -5] = true := by decide +kernel
theorem subd4_6_137 : subd4_6 [0, -1, -4] = true := by decide +kernel
theorem subd4_6_138 : subd4_6 [0, -1, -3] = true := by decide +kernel
theorem subd4_6_139 : subd4_6 [0, -1, -2] = true := by decide +kernel
theorem subd4_6_140 : subd4_6 [0, -1, -1] = true := by decide +kernel
theorem subd4_6_141 : subd4_6 [0, -1, 0] = true := by decide +kernel
theorem subd4_6_142 : subd4_6 [0, -1, 1] = true := by decide +kernel
theorem subd4_6_143 : subd4_6 [0, -1, 2] = true := by decide +kernel
theorem subd4_6_144 : subd4_6 [0, -1, 3] = true := by decide +kernel
theorem subd4_6_145 : subd4_6 [0, -1, 4] = true := by decide +kernel
theorem subd4_6_146 : subd4_6 [0, -1, 5] = true := by decide +kernel
theorem subd4_6_147 : subd4_6 [0, -1, 6] = true := by decide +kernel
theorem subd4_6_148 : subd4_6 [0, 0, -7] = true := by decide +kernel
theorem subd4_6_149 : subd4_6 [0, 0, -6] = true := by decide +kernel
theorem subd4_6_150 : subd4_6 [0, 0, -5] = true := by decide +kernel
theorem subd4_6_151 : subd4_6 [0, 0, -4] = true := by decide +kernel
theorem subd4_6_152 : subd4_6 [0, 0, -3] = true := by decide +kernel
theorem subd4_6_153 : subd4_6 [0, 0, -2] = true := by decide +kernel
theorem subd4_6_154 : subd4_6 [0, 0, -1] = true := by decide +kernel
theorem subd4_6_155 : subd4_6 [0, 0, 0] = true := by decide +kernel
theorem subd4_6_156 : subd4_6 [0, 0, 1] = true := by decide +kernel
theorem subd4_6_157 : subd4_6 [0, 0, 2] = true := by decide +kernel
theorem subd4_6_158 : subd4_6 [0, 0, 3] = true := by decide +kernel
theorem subd4_6_159 : subd4_6 [0, 0, 4] = true := by decide +kernel
theorem sbd4_6_4 : ∀ q ∈ blkd4_6_4, subd4_6 q = true := by
  unfold blkd4_6_4
  exact List.forall_mem_cons.2 ⟨subd4_6_128, List.forall_mem_cons.2 ⟨subd4_6_129, List.forall_mem_cons.2 ⟨subd4_6_130, List.forall_mem_cons.2 ⟨subd4_6_131, List.forall_mem_cons.2 ⟨subd4_6_132, List.forall_mem_cons.2 ⟨subd4_6_133, List.forall_mem_cons.2 ⟨subd4_6_134, List.forall_mem_cons.2 ⟨subd4_6_135, List.forall_mem_cons.2 ⟨subd4_6_136, List.forall_mem_cons.2 ⟨subd4_6_137, List.forall_mem_cons.2 ⟨subd4_6_138, List.forall_mem_cons.2 ⟨subd4_6_139, List.forall_mem_cons.2 ⟨subd4_6_140, List.forall_mem_cons.2 ⟨subd4_6_141, List.forall_mem_cons.2 ⟨subd4_6_142, List.forall_mem_cons.2 ⟨subd4_6_143, List.forall_mem_cons.2 ⟨subd4_6_144, List.forall_mem_cons.2 ⟨subd4_6_145, List.forall_mem_cons.2 ⟨subd4_6_146, List.forall_mem_cons.2 ⟨subd4_6_147, List.forall_mem_cons.2 ⟨subd4_6_148, List.forall_mem_cons.2 ⟨subd4_6_149, List.forall_mem_cons.2 ⟨subd4_6_150, List.forall_mem_cons.2 ⟨subd4_6_151, List.forall_mem_cons.2 ⟨subd4_6_152, List.forall_mem_cons.2 ⟨subd4_6_153, List.forall_mem_cons.2 ⟨subd4_6_154, List.forall_mem_cons.2 ⟨subd4_6_155, List.forall_mem_cons.2 ⟨subd4_6_156, List.forall_mem_cons.2 ⟨subd4_6_157, List.forall_mem_cons.2 ⟨subd4_6_158, List.forall_mem_cons.2 ⟨subd4_6_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_6_160 : subd4_6 [0, 0, 5] = true := by decide +kernel
theorem subd4_6_161 : subd4_6 [0, 0, 6] = true := by decide +kernel
theorem subd4_6_162 : subd4_6 [0, 1, -7] = true := by decide +kernel
theorem subd4_6_163 : subd4_6 [0, 1, -6] = true := by decide +kernel
theorem subd4_6_164 : subd4_6 [0, 1, -5] = true := by decide +kernel
theorem subd4_6_165 : subd4_6 [0, 1, -4] = true := by decide +kernel
theorem subd4_6_166 : subd4_6 [0, 1, -3] = true := by decide +kernel
theorem subd4_6_167 : subd4_6 [0, 1, -2] = true := by decide +kernel
theorem subd4_6_168 : subd4_6 [0, 1, -1] = true := by decide +kernel
theorem subd4_6_169 : subd4_6 [0, 1, 0] = true := by decide +kernel
theorem subd4_6_170 : subd4_6 [0, 1, 1] = true := by decide +kernel
theorem subd4_6_171 : subd4_6 [0, 1, 2] = true := by decide +kernel
theorem subd4_6_172 : subd4_6 [0, 1, 3] = true := by decide +kernel
theorem subd4_6_173 : subd4_6 [0, 1, 4] = true := by decide +kernel
theorem subd4_6_174 : subd4_6 [0, 1, 5] = true := by decide +kernel
theorem subd4_6_175 : subd4_6 [0, 1, 6] = true := by decide +kernel
theorem subd4_6_176 : subd4_6 [0, 2, -6] = true := by decide +kernel
theorem subd4_6_177 : subd4_6 [0, 2, -5] = true := by decide +kernel
theorem subd4_6_178 : subd4_6 [0, 2, -4] = true := by decide +kernel
theorem subd4_6_179 : subd4_6 [0, 2, -3] = true := by decide +kernel
theorem subd4_6_180 : subd4_6 [0, 2, -2] = true := by decide +kernel
theorem subd4_6_181 : subd4_6 [0, 2, -1] = true := by decide +kernel
theorem subd4_6_182 : subd4_6 [0, 2, 0] = true := by decide +kernel
theorem subd4_6_183 : subd4_6 [0, 2, 1] = true := by decide +kernel
theorem subd4_6_184 : subd4_6 [0, 2, 2] = true := by decide +kernel
theorem subd4_6_185 : subd4_6 [0, 2, 3] = true := by decide +kernel
theorem subd4_6_186 : subd4_6 [0, 2, 4] = true := by decide +kernel
theorem subd4_6_187 : subd4_6 [0, 2, 5] = true := by decide +kernel
theorem subd4_6_188 : subd4_6 [0, 2, 6] = true := by decide +kernel
theorem subd4_6_189 : subd4_6 [0, 3] = true := by decide +kernel
theorem subd4_6_190 : subd4_6 [0, 4] = true := by decide +kernel
theorem subd4_6_191 : subd4_6 [0, 5] = true := by decide +kernel
theorem sbd4_6_5 : ∀ q ∈ blkd4_6_5, subd4_6 q = true := by
  unfold blkd4_6_5
  exact List.forall_mem_cons.2 ⟨subd4_6_160, List.forall_mem_cons.2 ⟨subd4_6_161, List.forall_mem_cons.2 ⟨subd4_6_162, List.forall_mem_cons.2 ⟨subd4_6_163, List.forall_mem_cons.2 ⟨subd4_6_164, List.forall_mem_cons.2 ⟨subd4_6_165, List.forall_mem_cons.2 ⟨subd4_6_166, List.forall_mem_cons.2 ⟨subd4_6_167, List.forall_mem_cons.2 ⟨subd4_6_168, List.forall_mem_cons.2 ⟨subd4_6_169, List.forall_mem_cons.2 ⟨subd4_6_170, List.forall_mem_cons.2 ⟨subd4_6_171, List.forall_mem_cons.2 ⟨subd4_6_172, List.forall_mem_cons.2 ⟨subd4_6_173, List.forall_mem_cons.2 ⟨subd4_6_174, List.forall_mem_cons.2 ⟨subd4_6_175, List.forall_mem_cons.2 ⟨subd4_6_176, List.forall_mem_cons.2 ⟨subd4_6_177, List.forall_mem_cons.2 ⟨subd4_6_178, List.forall_mem_cons.2 ⟨subd4_6_179, List.forall_mem_cons.2 ⟨subd4_6_180, List.forall_mem_cons.2 ⟨subd4_6_181, List.forall_mem_cons.2 ⟨subd4_6_182, List.forall_mem_cons.2 ⟨subd4_6_183, List.forall_mem_cons.2 ⟨subd4_6_184, List.forall_mem_cons.2 ⟨subd4_6_185, List.forall_mem_cons.2 ⟨subd4_6_186, List.forall_mem_cons.2 ⟨subd4_6_187, List.forall_mem_cons.2 ⟨subd4_6_188, List.forall_mem_cons.2 ⟨subd4_6_189, List.forall_mem_cons.2 ⟨subd4_6_190, List.forall_mem_cons.2 ⟨subd4_6_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
