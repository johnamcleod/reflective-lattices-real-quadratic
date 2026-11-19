import ReflectZphi.Data.Cert5.C058.Base

namespace ReflectZphi.Data.Cert5.C058
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub5_320 : sub5 [2, 0, 2] = true := by decide +kernel
theorem sub5_321 : sub5 [2, 0, 3] = true := by decide +kernel
theorem sub5_322 : sub5 [2, 0, 4] = true := by decide +kernel
theorem sub5_323 : sub5 [2, 0, 5] = true := by decide +kernel
theorem sub5_324 : sub5 [2, 0, 6] = true := by decide +kernel
theorem sub5_325 : sub5 [2, 1] = true := by decide +kernel
theorem sub5_326 : sub5 [2, 2] = true := by decide +kernel
theorem sub5_327 : sub5 [2, 3] = true := by decide +kernel
theorem sub5_328 : sub5 [2, 4] = true := by decide +kernel
theorem sub5_329 : sub5 [2, 5] = true := by decide +kernel
theorem sub5_330 : sub5 [3, -8] = true := by decide +kernel
theorem sub5_331 : sub5 [3, -7] = true := by decide +kernel
theorem sub5_332 : sub5 [3, -6] = true := by decide +kernel
theorem sub5_333 : sub5 [3, -5] = true := by decide +kernel
theorem sub5_334 : sub5 [3, -4] = true := by decide +kernel
theorem sub5_335 : sub5 [3, -3] = true := by decide +kernel
theorem sub5_336 : sub5 [3, -2] = true := by decide +kernel
theorem sub5_337 : sub5 [3, -1] = true := by decide +kernel
theorem sub5_338 : sub5 [3, 0] = true := by decide +kernel
theorem sub5_339 : sub5 [3, 1] = true := by decide +kernel
theorem sub5_340 : sub5 [3, 2] = true := by decide +kernel
theorem sub5_341 : sub5 [3, 3] = true := by decide +kernel
theorem sub5_342 : sub5 [3, 4] = true := by decide +kernel
theorem sub5_343 : sub5 [3, 5] = true := by decide +kernel
theorem sub5_344 : sub5 [4, -8] = true := by decide +kernel
theorem sub5_345 : sub5 [4, -7] = true := by decide +kernel
theorem sub5_346 : sub5 [4, -6] = true := by decide +kernel
theorem sub5_347 : sub5 [4, -5] = true := by decide +kernel
theorem sub5_348 : sub5 [4, -4] = true := by decide +kernel
theorem sub5_349 : sub5 [4, -3] = true := by decide +kernel
theorem sub5_350 : sub5 [4, -2] = true := by decide +kernel
theorem sub5_351 : sub5 [4, -1] = true := by decide +kernel
theorem sb5_10 : ∀ q ∈ blk5_10, sub5 q = true := by
  unfold blk5_10
  exact List.forall_mem_cons.2 ⟨sub5_320, List.forall_mem_cons.2 ⟨sub5_321, List.forall_mem_cons.2 ⟨sub5_322, List.forall_mem_cons.2 ⟨sub5_323, List.forall_mem_cons.2 ⟨sub5_324, List.forall_mem_cons.2 ⟨sub5_325, List.forall_mem_cons.2 ⟨sub5_326, List.forall_mem_cons.2 ⟨sub5_327, List.forall_mem_cons.2 ⟨sub5_328, List.forall_mem_cons.2 ⟨sub5_329, List.forall_mem_cons.2 ⟨sub5_330, List.forall_mem_cons.2 ⟨sub5_331, List.forall_mem_cons.2 ⟨sub5_332, List.forall_mem_cons.2 ⟨sub5_333, List.forall_mem_cons.2 ⟨sub5_334, List.forall_mem_cons.2 ⟨sub5_335, List.forall_mem_cons.2 ⟨sub5_336, List.forall_mem_cons.2 ⟨sub5_337, List.forall_mem_cons.2 ⟨sub5_338, List.forall_mem_cons.2 ⟨sub5_339, List.forall_mem_cons.2 ⟨sub5_340, List.forall_mem_cons.2 ⟨sub5_341, List.forall_mem_cons.2 ⟨sub5_342, List.forall_mem_cons.2 ⟨sub5_343, List.forall_mem_cons.2 ⟨sub5_344, List.forall_mem_cons.2 ⟨sub5_345, List.forall_mem_cons.2 ⟨sub5_346, List.forall_mem_cons.2 ⟨sub5_347, List.forall_mem_cons.2 ⟨sub5_348, List.forall_mem_cons.2 ⟨sub5_349, List.forall_mem_cons.2 ⟨sub5_350, List.forall_mem_cons.2 ⟨sub5_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_352 : sub5 [4, 0] = true := by decide +kernel
theorem sub5_353 : sub5 [4, 1] = true := by decide +kernel
theorem sub5_354 : sub5 [4, 2] = true := by decide +kernel
theorem sub5_355 : sub5 [4, 3] = true := by decide +kernel
theorem sub5_356 : sub5 [5, -7] = true := by decide +kernel
theorem sub5_357 : sub5 [5, -6] = true := by decide +kernel
theorem sub5_358 : sub5 [5, -5] = true := by decide +kernel
theorem sub5_359 : sub5 [5, -4] = true := by decide +kernel
theorem sub5_360 : sub5 [5, -3] = true := by decide +kernel
theorem sub5_361 : sub5 [5, -2] = true := by decide +kernel
theorem sub5_362 : sub5 [5, -1] = true := by decide +kernel
theorem sub5_363 : sub5 [5, 0] = true := by decide +kernel
theorem sub5_364 : sub5 [5, 1] = true := by decide +kernel
theorem sub5_365 : sub5 [5, 2] = true := by decide +kernel
theorem sub5_366 : sub5 [6] = true := by decide +kernel
theorem sb5_11 : ∀ q ∈ blk5_11, sub5 q = true := by
  unfold blk5_11
  exact List.forall_mem_cons.2 ⟨sub5_352, List.forall_mem_cons.2 ⟨sub5_353, List.forall_mem_cons.2 ⟨sub5_354, List.forall_mem_cons.2 ⟨sub5_355, List.forall_mem_cons.2 ⟨sub5_356, List.forall_mem_cons.2 ⟨sub5_357, List.forall_mem_cons.2 ⟨sub5_358, List.forall_mem_cons.2 ⟨sub5_359, List.forall_mem_cons.2 ⟨sub5_360, List.forall_mem_cons.2 ⟨sub5_361, List.forall_mem_cons.2 ⟨sub5_362, List.forall_mem_cons.2 ⟨sub5_363, List.forall_mem_cons.2 ⟨sub5_364, List.forall_mem_cons.2 ⟨sub5_365, List.forall_mem_cons.2 ⟨sub5_366, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_0 : sub6 [-3] = true := by decide +kernel
theorem sub6_1 : sub6 [-2, -3] = true := by decide +kernel
theorem sub6_2 : sub6 [-2, -2] = true := by decide +kernel
theorem sub6_3 : sub6 [-2, -1] = true := by decide +kernel
theorem sub6_4 : sub6 [-2, 0] = true := by decide +kernel
theorem sub6_5 : sub6 [-2, 1] = true := by decide +kernel
theorem sub6_6 : sub6 [-2, 2] = true := by decide +kernel
theorem sub6_7 : sub6 [-1, -4] = true := by decide +kernel
theorem sub6_8 : sub6 [-1, -3] = true := by decide +kernel
theorem sub6_9 : sub6 [-1, -2] = true := by decide +kernel
theorem sub6_10 : sub6 [-1, -1] = true := by decide +kernel
theorem sub6_11 : sub6 [-1, 0] = true := by decide +kernel
theorem sub6_12 : sub6 [-1, 1] = true := by decide +kernel
theorem sub6_13 : sub6 [-1, 2] = true := by decide +kernel
theorem sub6_14 : sub6 [0, -4] = true := by decide +kernel
theorem sub6_15 : sub6 [0, -3] = true := by decide +kernel
theorem sub6_16 : sub6 [0, -2] = true := by decide +kernel
theorem sub6_17 : sub6 [0, -1] = true := by decide +kernel
theorem sub6_18 : sub6 [0, 0] = true := by decide +kernel
theorem sub6_19 : sub6 [0, 1] = true := by decide +kernel
theorem sub6_20 : sub6 [0, 2] = true := by decide +kernel
theorem sub6_21 : sub6 [0, 3] = true := by decide +kernel
theorem sub6_22 : sub6 [1, -3] = true := by decide +kernel
theorem sub6_23 : sub6 [1, -2] = true := by decide +kernel
theorem sub6_24 : sub6 [1, -1] = true := by decide +kernel
theorem sub6_25 : sub6 [1, 0] = true := by decide +kernel
theorem sub6_26 : sub6 [1, 1] = true := by decide +kernel
theorem sub6_27 : sub6 [1, 2] = true := by decide +kernel
theorem sub6_28 : sub6 [1, 3] = true := by decide +kernel
theorem sub6_29 : sub6 [2, -3] = true := by decide +kernel
theorem sub6_30 : sub6 [2, -2] = true := by decide +kernel
theorem sub6_31 : sub6 [2, -1] = true := by decide +kernel
theorem sb6_0 : ∀ q ∈ blk6_0, sub6 q = true := by
  unfold blk6_0
  exact List.forall_mem_cons.2 ⟨sub6_0, List.forall_mem_cons.2 ⟨sub6_1, List.forall_mem_cons.2 ⟨sub6_2, List.forall_mem_cons.2 ⟨sub6_3, List.forall_mem_cons.2 ⟨sub6_4, List.forall_mem_cons.2 ⟨sub6_5, List.forall_mem_cons.2 ⟨sub6_6, List.forall_mem_cons.2 ⟨sub6_7, List.forall_mem_cons.2 ⟨sub6_8, List.forall_mem_cons.2 ⟨sub6_9, List.forall_mem_cons.2 ⟨sub6_10, List.forall_mem_cons.2 ⟨sub6_11, List.forall_mem_cons.2 ⟨sub6_12, List.forall_mem_cons.2 ⟨sub6_13, List.forall_mem_cons.2 ⟨sub6_14, List.forall_mem_cons.2 ⟨sub6_15, List.forall_mem_cons.2 ⟨sub6_16, List.forall_mem_cons.2 ⟨sub6_17, List.forall_mem_cons.2 ⟨sub6_18, List.forall_mem_cons.2 ⟨sub6_19, List.forall_mem_cons.2 ⟨sub6_20, List.forall_mem_cons.2 ⟨sub6_21, List.forall_mem_cons.2 ⟨sub6_22, List.forall_mem_cons.2 ⟨sub6_23, List.forall_mem_cons.2 ⟨sub6_24, List.forall_mem_cons.2 ⟨sub6_25, List.forall_mem_cons.2 ⟨sub6_26, List.forall_mem_cons.2 ⟨sub6_27, List.forall_mem_cons.2 ⟨sub6_28, List.forall_mem_cons.2 ⟨sub6_29, List.forall_mem_cons.2 ⟨sub6_30, List.forall_mem_cons.2 ⟨sub6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_32 : sub6 [2, 0] = true := by decide +kernel
theorem sub6_33 : sub6 [2, 1] = true := by decide +kernel
theorem sub6_34 : sub6 [2, 2] = true := by decide +kernel
theorem sub6_35 : sub6 [3] = true := by decide +kernel
theorem sb6_1 : ∀ q ∈ blk6_1, sub6 q = true := by
  unfold blk6_1
  exact List.forall_mem_cons.2 ⟨sub6_32, List.forall_mem_cons.2 ⟨sub6_33, List.forall_mem_cons.2 ⟨sub6_34, List.forall_mem_cons.2 ⟨sub6_35, List.forall_mem_nil _⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C058
