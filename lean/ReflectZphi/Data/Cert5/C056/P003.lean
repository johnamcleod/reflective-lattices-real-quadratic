import ReflectZphi.Data.Cert5.C056.Base

namespace ReflectZphi.Data.Cert5.C056
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub5_288 : sub5 [1, 1, 0] = true := by decide +kernel
theorem sub5_289 : sub5 [1, 1, 1] = true := by decide +kernel
theorem sub5_290 : sub5 [1, 1, 2] = true := by decide +kernel
theorem sub5_291 : sub5 [1, 1, 3] = true := by decide +kernel
theorem sub5_292 : sub5 [1, 1, 4] = true := by decide +kernel
theorem sub5_293 : sub5 [1, 1, 5] = true := by decide +kernel
theorem sub5_294 : sub5 [1, 1, 6] = true := by decide +kernel
theorem sub5_295 : sub5 [1, 2, -7] = true := by decide +kernel
theorem sub5_296 : sub5 [1, 2, -6] = true := by decide +kernel
theorem sub5_297 : sub5 [1, 2, -5] = true := by decide +kernel
theorem sub5_298 : sub5 [1, 2, -4] = true := by decide +kernel
theorem sub5_299 : sub5 [1, 2, -3] = true := by decide +kernel
theorem sub5_300 : sub5 [1, 2, -2] = true := by decide +kernel
theorem sub5_301 : sub5 [1, 2, -1] = true := by decide +kernel
theorem sub5_302 : sub5 [1, 2, 0] = true := by decide +kernel
theorem sub5_303 : sub5 [1, 2, 1] = true := by decide +kernel
theorem sub5_304 : sub5 [1, 2, 2] = true := by decide +kernel
theorem sub5_305 : sub5 [1, 2, 3] = true := by decide +kernel
theorem sub5_306 : sub5 [1, 2, 4] = true := by decide +kernel
theorem sub5_307 : sub5 [1, 2, 5] = true := by decide +kernel
theorem sub5_308 : sub5 [1, 2, 6] = true := by decide +kernel
theorem sub5_309 : sub5 [1, 3] = true := by decide +kernel
theorem sub5_310 : sub5 [1, 4] = true := by decide +kernel
theorem sub5_311 : sub5 [1, 5] = true := by decide +kernel
theorem sub5_312 : sub5 [2, -6] = true := by decide +kernel
theorem sub5_313 : sub5 [2, -5] = true := by decide +kernel
theorem sub5_314 : sub5 [2, -4] = true := by decide +kernel
theorem sub5_315 : sub5 [2, -3] = true := by decide +kernel
theorem sub5_316 : sub5 [2, -2] = true := by decide +kernel
theorem sub5_317 : sub5 [2, -1, -7] = true := by decide +kernel
theorem sub5_318 : sub5 [2, -1, -6] = true := by decide +kernel
theorem sub5_319 : sub5 [2, -1, -5] = true := by decide +kernel
theorem sb5_9 : ∀ q ∈ blk5_9, sub5 q = true := by
  unfold blk5_9
  exact List.forall_mem_cons.2 ⟨sub5_288, List.forall_mem_cons.2 ⟨sub5_289, List.forall_mem_cons.2 ⟨sub5_290, List.forall_mem_cons.2 ⟨sub5_291, List.forall_mem_cons.2 ⟨sub5_292, List.forall_mem_cons.2 ⟨sub5_293, List.forall_mem_cons.2 ⟨sub5_294, List.forall_mem_cons.2 ⟨sub5_295, List.forall_mem_cons.2 ⟨sub5_296, List.forall_mem_cons.2 ⟨sub5_297, List.forall_mem_cons.2 ⟨sub5_298, List.forall_mem_cons.2 ⟨sub5_299, List.forall_mem_cons.2 ⟨sub5_300, List.forall_mem_cons.2 ⟨sub5_301, List.forall_mem_cons.2 ⟨sub5_302, List.forall_mem_cons.2 ⟨sub5_303, List.forall_mem_cons.2 ⟨sub5_304, List.forall_mem_cons.2 ⟨sub5_305, List.forall_mem_cons.2 ⟨sub5_306, List.forall_mem_cons.2 ⟨sub5_307, List.forall_mem_cons.2 ⟨sub5_308, List.forall_mem_cons.2 ⟨sub5_309, List.forall_mem_cons.2 ⟨sub5_310, List.forall_mem_cons.2 ⟨sub5_311, List.forall_mem_cons.2 ⟨sub5_312, List.forall_mem_cons.2 ⟨sub5_313, List.forall_mem_cons.2 ⟨sub5_314, List.forall_mem_cons.2 ⟨sub5_315, List.forall_mem_cons.2 ⟨sub5_316, List.forall_mem_cons.2 ⟨sub5_317, List.forall_mem_cons.2 ⟨sub5_318, List.forall_mem_cons.2 ⟨sub5_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_320 : sub5 [2, -1, -4] = true := by decide +kernel
theorem sub5_321 : sub5 [2, -1, -3] = true := by decide +kernel
theorem sub5_322 : sub5 [2, -1, -2] = true := by decide +kernel
theorem sub5_323 : sub5 [2, -1, -1] = true := by decide +kernel
theorem sub5_324 : sub5 [2, -1, 0] = true := by decide +kernel
theorem sub5_325 : sub5 [2, -1, 1] = true := by decide +kernel
theorem sub5_326 : sub5 [2, -1, 2] = true := by decide +kernel
theorem sub5_327 : sub5 [2, -1, 3] = true := by decide +kernel
theorem sub5_328 : sub5 [2, -1, 4] = true := by decide +kernel
theorem sub5_329 : sub5 [2, -1, 5] = true := by decide +kernel
theorem sub5_330 : sub5 [2, -1, 6] = true := by decide +kernel
theorem sub5_331 : sub5 [2, 0, -7] = true := by decide +kernel
theorem sub5_332 : sub5 [2, 0, -6] = true := by decide +kernel
theorem sub5_333 : sub5 [2, 0, -5] = true := by decide +kernel
theorem sub5_334 : sub5 [2, 0, -4] = true := by decide +kernel
theorem sub5_335 : sub5 [2, 0, -3] = true := by decide +kernel
theorem sub5_336 : sub5 [2, 0, -2] = true := by decide +kernel
theorem sub5_337 : sub5 [2, 0, -1] = true := by decide +kernel
theorem sub5_338 : sub5 [2, 0, 0] = true := by decide +kernel
theorem sub5_339 : sub5 [2, 0, 1] = true := by decide +kernel
theorem sub5_340 : sub5 [2, 0, 2] = true := by decide +kernel
theorem sub5_341 : sub5 [2, 0, 3] = true := by decide +kernel
theorem sub5_342 : sub5 [2, 0, 4] = true := by decide +kernel
theorem sub5_343 : sub5 [2, 0, 5] = true := by decide +kernel
theorem sub5_344 : sub5 [2, 0, 6] = true := by decide +kernel
theorem sub5_345 : sub5 [2, 1, -7] = true := by decide +kernel
theorem sub5_346 : sub5 [2, 1, -6] = true := by decide +kernel
theorem sub5_347 : sub5 [2, 1, -5] = true := by decide +kernel
theorem sub5_348 : sub5 [2, 1, -4] = true := by decide +kernel
theorem sub5_349 : sub5 [2, 1, -3] = true := by decide +kernel
theorem sub5_350 : sub5 [2, 1, -2] = true := by decide +kernel
theorem sub5_351 : sub5 [2, 1, -1] = true := by decide +kernel
theorem sb5_10 : ∀ q ∈ blk5_10, sub5 q = true := by
  unfold blk5_10
  exact List.forall_mem_cons.2 ⟨sub5_320, List.forall_mem_cons.2 ⟨sub5_321, List.forall_mem_cons.2 ⟨sub5_322, List.forall_mem_cons.2 ⟨sub5_323, List.forall_mem_cons.2 ⟨sub5_324, List.forall_mem_cons.2 ⟨sub5_325, List.forall_mem_cons.2 ⟨sub5_326, List.forall_mem_cons.2 ⟨sub5_327, List.forall_mem_cons.2 ⟨sub5_328, List.forall_mem_cons.2 ⟨sub5_329, List.forall_mem_cons.2 ⟨sub5_330, List.forall_mem_cons.2 ⟨sub5_331, List.forall_mem_cons.2 ⟨sub5_332, List.forall_mem_cons.2 ⟨sub5_333, List.forall_mem_cons.2 ⟨sub5_334, List.forall_mem_cons.2 ⟨sub5_335, List.forall_mem_cons.2 ⟨sub5_336, List.forall_mem_cons.2 ⟨sub5_337, List.forall_mem_cons.2 ⟨sub5_338, List.forall_mem_cons.2 ⟨sub5_339, List.forall_mem_cons.2 ⟨sub5_340, List.forall_mem_cons.2 ⟨sub5_341, List.forall_mem_cons.2 ⟨sub5_342, List.forall_mem_cons.2 ⟨sub5_343, List.forall_mem_cons.2 ⟨sub5_344, List.forall_mem_cons.2 ⟨sub5_345, List.forall_mem_cons.2 ⟨sub5_346, List.forall_mem_cons.2 ⟨sub5_347, List.forall_mem_cons.2 ⟨sub5_348, List.forall_mem_cons.2 ⟨sub5_349, List.forall_mem_cons.2 ⟨sub5_350, List.forall_mem_cons.2 ⟨sub5_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_352 : sub5 [2, 1, 0] = true := by decide +kernel
theorem sub5_353 : sub5 [2, 1, 1] = true := by decide +kernel
theorem sub5_354 : sub5 [2, 1, 2] = true := by decide +kernel
theorem sub5_355 : sub5 [2, 1, 3] = true := by decide +kernel
theorem sub5_356 : sub5 [2, 1, 4] = true := by decide +kernel
theorem sub5_357 : sub5 [2, 1, 5] = true := by decide +kernel
theorem sub5_358 : sub5 [2, 1, 6] = true := by decide +kernel
theorem sub5_359 : sub5 [2, 2] = true := by decide +kernel
theorem sub5_360 : sub5 [2, 3] = true := by decide +kernel
theorem sub5_361 : sub5 [2, 4] = true := by decide +kernel
theorem sub5_362 : sub5 [2, 5] = true := by decide +kernel
theorem sub5_363 : sub5 [3, -6] = true := by decide +kernel
theorem sub5_364 : sub5 [3, -5] = true := by decide +kernel
theorem sub5_365 : sub5 [3, -4] = true := by decide +kernel
theorem sub5_366 : sub5 [3, -3] = true := by decide +kernel
theorem sub5_367 : sub5 [3, -2] = true := by decide +kernel
theorem sub5_368 : sub5 [3, -1] = true := by decide +kernel
theorem sub5_369 : sub5 [3, 0] = true := by decide +kernel
theorem sub5_370 : sub5 [3, 1] = true := by decide +kernel
theorem sub5_371 : sub5 [3, 2] = true := by decide +kernel
theorem sub5_372 : sub5 [3, 3] = true := by decide +kernel
theorem sub5_373 : sub5 [3, 4] = true := by decide +kernel
theorem sub5_374 : sub5 [3, 5] = true := by decide +kernel
theorem sub5_375 : sub5 [4, -5] = true := by decide +kernel
theorem sub5_376 : sub5 [4, -4] = true := by decide +kernel
theorem sub5_377 : sub5 [4, -3] = true := by decide +kernel
theorem sub5_378 : sub5 [4, -2] = true := by decide +kernel
theorem sub5_379 : sub5 [4, -1] = true := by decide +kernel
theorem sub5_380 : sub5 [4, 0] = true := by decide +kernel
theorem sub5_381 : sub5 [4, 1] = true := by decide +kernel
theorem sub5_382 : sub5 [4, 2] = true := by decide +kernel
theorem sub5_383 : sub5 [4, 3] = true := by decide +kernel
theorem sb5_11 : ∀ q ∈ blk5_11, sub5 q = true := by
  unfold blk5_11
  exact List.forall_mem_cons.2 ⟨sub5_352, List.forall_mem_cons.2 ⟨sub5_353, List.forall_mem_cons.2 ⟨sub5_354, List.forall_mem_cons.2 ⟨sub5_355, List.forall_mem_cons.2 ⟨sub5_356, List.forall_mem_cons.2 ⟨sub5_357, List.forall_mem_cons.2 ⟨sub5_358, List.forall_mem_cons.2 ⟨sub5_359, List.forall_mem_cons.2 ⟨sub5_360, List.forall_mem_cons.2 ⟨sub5_361, List.forall_mem_cons.2 ⟨sub5_362, List.forall_mem_cons.2 ⟨sub5_363, List.forall_mem_cons.2 ⟨sub5_364, List.forall_mem_cons.2 ⟨sub5_365, List.forall_mem_cons.2 ⟨sub5_366, List.forall_mem_cons.2 ⟨sub5_367, List.forall_mem_cons.2 ⟨sub5_368, List.forall_mem_cons.2 ⟨sub5_369, List.forall_mem_cons.2 ⟨sub5_370, List.forall_mem_cons.2 ⟨sub5_371, List.forall_mem_cons.2 ⟨sub5_372, List.forall_mem_cons.2 ⟨sub5_373, List.forall_mem_cons.2 ⟨sub5_374, List.forall_mem_cons.2 ⟨sub5_375, List.forall_mem_cons.2 ⟨sub5_376, List.forall_mem_cons.2 ⟨sub5_377, List.forall_mem_cons.2 ⟨sub5_378, List.forall_mem_cons.2 ⟨sub5_379, List.forall_mem_cons.2 ⟨sub5_380, List.forall_mem_cons.2 ⟨sub5_381, List.forall_mem_cons.2 ⟨sub5_382, List.forall_mem_cons.2 ⟨sub5_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_384 : sub5 [4, 4] = true := by decide +kernel
theorem sub5_385 : sub5 [5, -4] = true := by decide +kernel
theorem sub5_386 : sub5 [5, -3] = true := by decide +kernel
theorem sub5_387 : sub5 [5, -2] = true := by decide +kernel
theorem sub5_388 : sub5 [5, -1] = true := by decide +kernel
theorem sub5_389 : sub5 [5, 0] = true := by decide +kernel
theorem sub5_390 : sub5 [5, 1] = true := by decide +kernel
theorem sub5_391 : sub5 [5, 2] = true := by decide +kernel
theorem sub5_392 : sub5 [5, 3] = true := by decide +kernel
theorem sb5_12 : ∀ q ∈ blk5_12, sub5 q = true := by
  unfold blk5_12
  exact List.forall_mem_cons.2 ⟨sub5_384, List.forall_mem_cons.2 ⟨sub5_385, List.forall_mem_cons.2 ⟨sub5_386, List.forall_mem_cons.2 ⟨sub5_387, List.forall_mem_cons.2 ⟨sub5_388, List.forall_mem_cons.2 ⟨sub5_389, List.forall_mem_cons.2 ⟨sub5_390, List.forall_mem_cons.2 ⟨sub5_391, List.forall_mem_cons.2 ⟨sub5_392, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_0 : sub6 [-6] = true := by decide +kernel
theorem sub6_1 : sub6 [-5, -6] = true := by decide +kernel
theorem sub6_2 : sub6 [-5, -5] = true := by decide +kernel
theorem sub6_3 : sub6 [-5, -4] = true := by decide +kernel
theorem sub6_4 : sub6 [-5, -3] = true := by decide +kernel
theorem sub6_5 : sub6 [-5, -2] = true := by decide +kernel
theorem sub6_6 : sub6 [-5, -1] = true := by decide +kernel
theorem sub6_7 : sub6 [-5, 0] = true := by decide +kernel
theorem sub6_8 : sub6 [-4, -6] = true := by decide +kernel
theorem sub6_9 : sub6 [-4, -5] = true := by decide +kernel
theorem sub6_10 : sub6 [-4, -4] = true := by decide +kernel
theorem sub6_11 : sub6 [-4, -3] = true := by decide +kernel
theorem sub6_12 : sub6 [-4, -2] = true := by decide +kernel
theorem sub6_13 : sub6 [-4, -1] = true := by decide +kernel
theorem sub6_14 : sub6 [-4, 0] = true := by decide +kernel
theorem sub6_15 : sub6 [-4, 1] = true := by decide +kernel
theorem sub6_16 : sub6 [-3, -6] = true := by decide +kernel
theorem sub6_17 : sub6 [-3, -5] = true := by decide +kernel
theorem sub6_18 : sub6 [-3, -4] = true := by decide +kernel
theorem sub6_19 : sub6 [-3, -3] = true := by decide +kernel
theorem sub6_20 : sub6 [-3, -2] = true := by decide +kernel
theorem sub6_21 : sub6 [-3, -1] = true := by decide +kernel
theorem sub6_22 : sub6 [-3, 0] = true := by decide +kernel
theorem sub6_23 : sub6 [-3, 1] = true := by decide +kernel
theorem sub6_24 : sub6 [-3, 2] = true := by decide +kernel
theorem sub6_25 : sub6 [-2, -6] = true := by decide +kernel
theorem sub6_26 : sub6 [-2, -5] = true := by decide +kernel
theorem sub6_27 : sub6 [-2, -4] = true := by decide +kernel
theorem sub6_28 : sub6 [-2, -3] = true := by decide +kernel
theorem sub6_29 : sub6 [-2, -2] = true := by decide +kernel
theorem sub6_30 : sub6 [-2, -1] = true := by decide +kernel
theorem sub6_31 : sub6 [-2, 0] = true := by decide +kernel
theorem sb6_0 : ∀ q ∈ blk6_0, sub6 q = true := by
  unfold blk6_0
  exact List.forall_mem_cons.2 ⟨sub6_0, List.forall_mem_cons.2 ⟨sub6_1, List.forall_mem_cons.2 ⟨sub6_2, List.forall_mem_cons.2 ⟨sub6_3, List.forall_mem_cons.2 ⟨sub6_4, List.forall_mem_cons.2 ⟨sub6_5, List.forall_mem_cons.2 ⟨sub6_6, List.forall_mem_cons.2 ⟨sub6_7, List.forall_mem_cons.2 ⟨sub6_8, List.forall_mem_cons.2 ⟨sub6_9, List.forall_mem_cons.2 ⟨sub6_10, List.forall_mem_cons.2 ⟨sub6_11, List.forall_mem_cons.2 ⟨sub6_12, List.forall_mem_cons.2 ⟨sub6_13, List.forall_mem_cons.2 ⟨sub6_14, List.forall_mem_cons.2 ⟨sub6_15, List.forall_mem_cons.2 ⟨sub6_16, List.forall_mem_cons.2 ⟨sub6_17, List.forall_mem_cons.2 ⟨sub6_18, List.forall_mem_cons.2 ⟨sub6_19, List.forall_mem_cons.2 ⟨sub6_20, List.forall_mem_cons.2 ⟨sub6_21, List.forall_mem_cons.2 ⟨sub6_22, List.forall_mem_cons.2 ⟨sub6_23, List.forall_mem_cons.2 ⟨sub6_24, List.forall_mem_cons.2 ⟨sub6_25, List.forall_mem_cons.2 ⟨sub6_26, List.forall_mem_cons.2 ⟨sub6_27, List.forall_mem_cons.2 ⟨sub6_28, List.forall_mem_cons.2 ⟨sub6_29, List.forall_mem_cons.2 ⟨sub6_30, List.forall_mem_cons.2 ⟨sub6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_32 : sub6 [-2, 1] = true := by decide +kernel
theorem sub6_33 : sub6 [-2, 2] = true := by decide +kernel
theorem sub6_34 : sub6 [-2, 3] = true := by decide +kernel
theorem sub6_35 : sub6 [-1, -6] = true := by decide +kernel
theorem sub6_36 : sub6 [-1, -5] = true := by decide +kernel
theorem sub6_37 : sub6 [-1, -4] = true := by decide +kernel
theorem sub6_38 : sub6 [-1, -3] = true := by decide +kernel
theorem sub6_39 : sub6 [-1, -2] = true := by decide +kernel
theorem sub6_40 : sub6 [-1, -1] = true := by decide +kernel
theorem sub6_41 : sub6 [-1, 0] = true := by decide +kernel
theorem sub6_42 : sub6 [-1, 1] = true := by decide +kernel
theorem sub6_43 : sub6 [-1, 2] = true := by decide +kernel
theorem sub6_44 : sub6 [-1, 3] = true := by decide +kernel
theorem sub6_45 : sub6 [-1, 4] = true := by decide +kernel
theorem sub6_46 : sub6 [0, -5] = true := by decide +kernel
theorem sub6_47 : sub6 [0, -4] = true := by decide +kernel
theorem sub6_48 : sub6 [0, -3] = true := by decide +kernel
theorem sub6_49 : sub6 [0, -2] = true := by decide +kernel
theorem sub6_50 : sub6 [0, -1] = true := by decide +kernel
theorem sub6_51 : sub6 [0, 0] = true := by decide +kernel
theorem sub6_52 : sub6 [0, 1] = true := by decide +kernel
theorem sub6_53 : sub6 [0, 2] = true := by decide +kernel
theorem sub6_54 : sub6 [0, 3] = true := by decide +kernel
theorem sub6_55 : sub6 [0, 4] = true := by decide +kernel
theorem sub6_56 : sub6 [1, -5] = true := by decide +kernel
theorem sub6_57 : sub6 [1, -4] = true := by decide +kernel
theorem sub6_58 : sub6 [1, -3] = true := by decide +kernel
theorem sub6_59 : sub6 [1, -2] = true := by decide +kernel
theorem sub6_60 : sub6 [1, -1] = true := by decide +kernel
theorem sub6_61 : sub6 [1, 0] = true := by decide +kernel
theorem sub6_62 : sub6 [1, 1] = true := by decide +kernel
theorem sub6_63 : sub6 [1, 2] = true := by decide +kernel
theorem sb6_1 : ∀ q ∈ blk6_1, sub6 q = true := by
  unfold blk6_1
  exact List.forall_mem_cons.2 ⟨sub6_32, List.forall_mem_cons.2 ⟨sub6_33, List.forall_mem_cons.2 ⟨sub6_34, List.forall_mem_cons.2 ⟨sub6_35, List.forall_mem_cons.2 ⟨sub6_36, List.forall_mem_cons.2 ⟨sub6_37, List.forall_mem_cons.2 ⟨sub6_38, List.forall_mem_cons.2 ⟨sub6_39, List.forall_mem_cons.2 ⟨sub6_40, List.forall_mem_cons.2 ⟨sub6_41, List.forall_mem_cons.2 ⟨sub6_42, List.forall_mem_cons.2 ⟨sub6_43, List.forall_mem_cons.2 ⟨sub6_44, List.forall_mem_cons.2 ⟨sub6_45, List.forall_mem_cons.2 ⟨sub6_46, List.forall_mem_cons.2 ⟨sub6_47, List.forall_mem_cons.2 ⟨sub6_48, List.forall_mem_cons.2 ⟨sub6_49, List.forall_mem_cons.2 ⟨sub6_50, List.forall_mem_cons.2 ⟨sub6_51, List.forall_mem_cons.2 ⟨sub6_52, List.forall_mem_cons.2 ⟨sub6_53, List.forall_mem_cons.2 ⟨sub6_54, List.forall_mem_cons.2 ⟨sub6_55, List.forall_mem_cons.2 ⟨sub6_56, List.forall_mem_cons.2 ⟨sub6_57, List.forall_mem_cons.2 ⟨sub6_58, List.forall_mem_cons.2 ⟨sub6_59, List.forall_mem_cons.2 ⟨sub6_60, List.forall_mem_cons.2 ⟨sub6_61, List.forall_mem_cons.2 ⟨sub6_62, List.forall_mem_cons.2 ⟨sub6_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C056
