import ReflectZphi.Data.Cert5.C060.Base

namespace ReflectZphi.Data.Cert5.C060
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub4_352 : sub4 [2, 4] = true := by decide +kernel
theorem sub4_353 : sub4 [2, 5] = true := by decide +kernel
theorem sub4_354 : sub4 [2, 6] = true := by decide +kernel
theorem sub4_355 : sub4 [2, 7] = true := by decide +kernel
theorem sub4_356 : sub4 [2, 8] = true := by decide +kernel
theorem sub4_357 : sub4 [3, -7] = true := by decide +kernel
theorem sub4_358 : sub4 [3, -6] = true := by decide +kernel
theorem sub4_359 : sub4 [3, -5] = true := by decide +kernel
theorem sub4_360 : sub4 [3, -4] = true := by decide +kernel
theorem sub4_361 : sub4 [3, -3] = true := by decide +kernel
theorem sub4_362 : sub4 [3, -2] = true := by decide +kernel
theorem sub4_363 : sub4 [3, -1] = true := by decide +kernel
theorem sub4_364 : sub4 [3, 0] = true := by decide +kernel
theorem sub4_365 : sub4 [3, 1] = true := by decide +kernel
theorem sub4_366 : sub4 [3, 2] = true := by decide +kernel
theorem sub4_367 : sub4 [3, 3] = true := by decide +kernel
theorem sub4_368 : sub4 [3, 4] = true := by decide +kernel
theorem sub4_369 : sub4 [3, 5] = true := by decide +kernel
theorem sub4_370 : sub4 [3, 6] = true := by decide +kernel
theorem sub4_371 : sub4 [3, 7] = true := by decide +kernel
theorem sub4_372 : sub4 [3, 8] = true := by decide +kernel
theorem sub4_373 : sub4 [4, -6] = true := by decide +kernel
theorem sub4_374 : sub4 [4, -5] = true := by decide +kernel
theorem sub4_375 : sub4 [4, -4] = true := by decide +kernel
theorem sub4_376 : sub4 [4, -3] = true := by decide +kernel
theorem sub4_377 : sub4 [4, -2] = true := by decide +kernel
theorem sub4_378 : sub4 [4, -1] = true := by decide +kernel
theorem sub4_379 : sub4 [4, 0] = true := by decide +kernel
theorem sub4_380 : sub4 [4, 1] = true := by decide +kernel
theorem sub4_381 : sub4 [4, 2] = true := by decide +kernel
theorem sub4_382 : sub4 [4, 3] = true := by decide +kernel
theorem sub4_383 : sub4 [4, 4] = true := by decide +kernel
theorem sb4_11 : ∀ q ∈ blk4_11, sub4 q = true := by
  unfold blk4_11
  exact List.forall_mem_cons.2 ⟨sub4_352, List.forall_mem_cons.2 ⟨sub4_353, List.forall_mem_cons.2 ⟨sub4_354, List.forall_mem_cons.2 ⟨sub4_355, List.forall_mem_cons.2 ⟨sub4_356, List.forall_mem_cons.2 ⟨sub4_357, List.forall_mem_cons.2 ⟨sub4_358, List.forall_mem_cons.2 ⟨sub4_359, List.forall_mem_cons.2 ⟨sub4_360, List.forall_mem_cons.2 ⟨sub4_361, List.forall_mem_cons.2 ⟨sub4_362, List.forall_mem_cons.2 ⟨sub4_363, List.forall_mem_cons.2 ⟨sub4_364, List.forall_mem_cons.2 ⟨sub4_365, List.forall_mem_cons.2 ⟨sub4_366, List.forall_mem_cons.2 ⟨sub4_367, List.forall_mem_cons.2 ⟨sub4_368, List.forall_mem_cons.2 ⟨sub4_369, List.forall_mem_cons.2 ⟨sub4_370, List.forall_mem_cons.2 ⟨sub4_371, List.forall_mem_cons.2 ⟨sub4_372, List.forall_mem_cons.2 ⟨sub4_373, List.forall_mem_cons.2 ⟨sub4_374, List.forall_mem_cons.2 ⟨sub4_375, List.forall_mem_cons.2 ⟨sub4_376, List.forall_mem_cons.2 ⟨sub4_377, List.forall_mem_cons.2 ⟨sub4_378, List.forall_mem_cons.2 ⟨sub4_379, List.forall_mem_cons.2 ⟨sub4_380, List.forall_mem_cons.2 ⟨sub4_381, List.forall_mem_cons.2 ⟨sub4_382, List.forall_mem_cons.2 ⟨sub4_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_384 : sub4 [4, 5] = true := by decide +kernel
theorem sub4_385 : sub4 [4, 6] = true := by decide +kernel
theorem sub4_386 : sub4 [4, 7] = true := by decide +kernel
theorem sub4_387 : sub4 [5, -5] = true := by decide +kernel
theorem sub4_388 : sub4 [5, -4] = true := by decide +kernel
theorem sub4_389 : sub4 [5, -3] = true := by decide +kernel
theorem sub4_390 : sub4 [5, -2] = true := by decide +kernel
theorem sub4_391 : sub4 [5, -1] = true := by decide +kernel
theorem sub4_392 : sub4 [5, 0] = true := by decide +kernel
theorem sub4_393 : sub4 [5, 1] = true := by decide +kernel
theorem sub4_394 : sub4 [5, 2] = true := by decide +kernel
theorem sub4_395 : sub4 [5, 3] = true := by decide +kernel
theorem sub4_396 : sub4 [5, 4] = true := by decide +kernel
theorem sub4_397 : sub4 [5, 5] = true := by decide +kernel
theorem sub4_398 : sub4 [5, 6] = true := by decide +kernel
theorem sub4_399 : sub4 [5, 7] = true := by decide +kernel
theorem sub4_400 : sub4 [6, -3] = true := by decide +kernel
theorem sub4_401 : sub4 [6, -2] = true := by decide +kernel
theorem sub4_402 : sub4 [6, -1] = true := by decide +kernel
theorem sub4_403 : sub4 [6, 0] = true := by decide +kernel
theorem sub4_404 : sub4 [6, 1] = true := by decide +kernel
theorem sub4_405 : sub4 [6, 2] = true := by decide +kernel
theorem sub4_406 : sub4 [6, 3] = true := by decide +kernel
theorem sub4_407 : sub4 [6, 4] = true := by decide +kernel
theorem sub4_408 : sub4 [6, 5] = true := by decide +kernel
theorem sub4_409 : sub4 [6, 6] = true := by decide +kernel
theorem sub4_410 : sub4 [7] = true := by decide +kernel
theorem sb4_12 : ∀ q ∈ blk4_12, sub4 q = true := by
  unfold blk4_12
  exact List.forall_mem_cons.2 ⟨sub4_384, List.forall_mem_cons.2 ⟨sub4_385, List.forall_mem_cons.2 ⟨sub4_386, List.forall_mem_cons.2 ⟨sub4_387, List.forall_mem_cons.2 ⟨sub4_388, List.forall_mem_cons.2 ⟨sub4_389, List.forall_mem_cons.2 ⟨sub4_390, List.forall_mem_cons.2 ⟨sub4_391, List.forall_mem_cons.2 ⟨sub4_392, List.forall_mem_cons.2 ⟨sub4_393, List.forall_mem_cons.2 ⟨sub4_394, List.forall_mem_cons.2 ⟨sub4_395, List.forall_mem_cons.2 ⟨sub4_396, List.forall_mem_cons.2 ⟨sub4_397, List.forall_mem_cons.2 ⟨sub4_398, List.forall_mem_cons.2 ⟨sub4_399, List.forall_mem_cons.2 ⟨sub4_400, List.forall_mem_cons.2 ⟨sub4_401, List.forall_mem_cons.2 ⟨sub4_402, List.forall_mem_cons.2 ⟨sub4_403, List.forall_mem_cons.2 ⟨sub4_404, List.forall_mem_cons.2 ⟨sub4_405, List.forall_mem_cons.2 ⟨sub4_406, List.forall_mem_cons.2 ⟨sub4_407, List.forall_mem_cons.2 ⟨sub4_408, List.forall_mem_cons.2 ⟨sub4_409, List.forall_mem_cons.2 ⟨sub4_410, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_0 : sub5 [-6, -6] = true := by decide +kernel
theorem sub5_1 : sub5 [-6, -5] = true := by decide +kernel
theorem sub5_2 : sub5 [-6, -4] = true := by decide +kernel
theorem sub5_3 : sub5 [-6, -3] = true := by decide +kernel
theorem sub5_4 : sub5 [-6, -2] = true := by decide +kernel
theorem sub5_5 : sub5 [-6, -1] = true := by decide +kernel
theorem sub5_6 : sub5 [-6, 0] = true := by decide +kernel
theorem sub5_7 : sub5 [-5, -8] = true := by decide +kernel
theorem sub5_8 : sub5 [-5, -7] = true := by decide +kernel
theorem sub5_9 : sub5 [-5, -6] = true := by decide +kernel
theorem sub5_10 : sub5 [-5, -5] = true := by decide +kernel
theorem sub5_11 : sub5 [-5, -4] = true := by decide +kernel
theorem sub5_12 : sub5 [-5, -3] = true := by decide +kernel
theorem sub5_13 : sub5 [-5, -2] = true := by decide +kernel
theorem sub5_14 : sub5 [-5, -1] = true := by decide +kernel
theorem sub5_15 : sub5 [-5, 0] = true := by decide +kernel
theorem sub5_16 : sub5 [-5, 1] = true := by decide +kernel
theorem sub5_17 : sub5 [-5, 2] = true := by decide +kernel
theorem sub5_18 : sub5 [-4, -8] = true := by decide +kernel
theorem sub5_19 : sub5 [-4, -7] = true := by decide +kernel
theorem sub5_20 : sub5 [-4, -6] = true := by decide +kernel
theorem sub5_21 : sub5 [-4, -5] = true := by decide +kernel
theorem sub5_22 : sub5 [-4, -4] = true := by decide +kernel
theorem sub5_23 : sub5 [-4, -3] = true := by decide +kernel
theorem sub5_24 : sub5 [-4, -2] = true := by decide +kernel
theorem sub5_25 : sub5 [-4, -1] = true := by decide +kernel
theorem sub5_26 : sub5 [-4, 0] = true := by decide +kernel
theorem sub5_27 : sub5 [-4, 1] = true := by decide +kernel
theorem sub5_28 : sub5 [-4, 2] = true := by decide +kernel
theorem sub5_29 : sub5 [-4, 3] = true := by decide +kernel
theorem sub5_30 : sub5 [-3, -8] = true := by decide +kernel
theorem sub5_31 : sub5 [-3, -7] = true := by decide +kernel
theorem sb5_0 : ∀ q ∈ blk5_0, sub5 q = true := by
  unfold blk5_0
  exact List.forall_mem_cons.2 ⟨sub5_0, List.forall_mem_cons.2 ⟨sub5_1, List.forall_mem_cons.2 ⟨sub5_2, List.forall_mem_cons.2 ⟨sub5_3, List.forall_mem_cons.2 ⟨sub5_4, List.forall_mem_cons.2 ⟨sub5_5, List.forall_mem_cons.2 ⟨sub5_6, List.forall_mem_cons.2 ⟨sub5_7, List.forall_mem_cons.2 ⟨sub5_8, List.forall_mem_cons.2 ⟨sub5_9, List.forall_mem_cons.2 ⟨sub5_10, List.forall_mem_cons.2 ⟨sub5_11, List.forall_mem_cons.2 ⟨sub5_12, List.forall_mem_cons.2 ⟨sub5_13, List.forall_mem_cons.2 ⟨sub5_14, List.forall_mem_cons.2 ⟨sub5_15, List.forall_mem_cons.2 ⟨sub5_16, List.forall_mem_cons.2 ⟨sub5_17, List.forall_mem_cons.2 ⟨sub5_18, List.forall_mem_cons.2 ⟨sub5_19, List.forall_mem_cons.2 ⟨sub5_20, List.forall_mem_cons.2 ⟨sub5_21, List.forall_mem_cons.2 ⟨sub5_22, List.forall_mem_cons.2 ⟨sub5_23, List.forall_mem_cons.2 ⟨sub5_24, List.forall_mem_cons.2 ⟨sub5_25, List.forall_mem_cons.2 ⟨sub5_26, List.forall_mem_cons.2 ⟨sub5_27, List.forall_mem_cons.2 ⟨sub5_28, List.forall_mem_cons.2 ⟨sub5_29, List.forall_mem_cons.2 ⟨sub5_30, List.forall_mem_cons.2 ⟨sub5_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_32 : sub5 [-3, -6] = true := by decide +kernel
theorem sub5_33 : sub5 [-3, -5] = true := by decide +kernel
theorem sub5_34 : sub5 [-3, -4] = true := by decide +kernel
theorem sub5_35 : sub5 [-3, -3] = true := by decide +kernel
theorem sub5_36 : sub5 [-3, -2] = true := by decide +kernel
theorem sub5_37 : sub5 [-3, -1, -8] = true := by decide +kernel
theorem sub5_38 : sub5 [-3, -1, -7] = true := by decide +kernel
theorem sub5_39 : sub5 [-3, -1, -6] = true := by decide +kernel
theorem sub5_40 : sub5 [-3, -1, -5] = true := by decide +kernel
theorem sub5_41 : sub5 [-3, -1, -4] = true := by decide +kernel
theorem sub5_42 : sub5 [-3, -1, -3] = true := by decide +kernel
theorem sub5_43 : sub5 [-3, -1, -2] = true := by decide +kernel
theorem sub5_44 : sub5 [-3, -1, -1] = true := by decide +kernel
theorem sub5_45 : sub5 [-3, -1, 0] = true := by decide +kernel
theorem sub5_46 : sub5 [-3, -1, 1] = true := by decide +kernel
theorem sub5_47 : sub5 [-3, -1, 2] = true := by decide +kernel
theorem sub5_48 : sub5 [-3, -1, 3] = true := by decide +kernel
theorem sub5_49 : sub5 [-3, -1, 4] = true := by decide +kernel
theorem sub5_50 : sub5 [-3, -1, 5] = true := by decide +kernel
theorem sub5_51 : sub5 [-3, 0] = true := by decide +kernel
theorem sub5_52 : sub5 [-3, 1] = true := by decide +kernel
theorem sub5_53 : sub5 [-3, 2] = true := by decide +kernel
theorem sub5_54 : sub5 [-3, 3] = true := by decide +kernel
theorem sub5_55 : sub5 [-3, 4] = true := by decide +kernel
theorem sub5_56 : sub5 [-3, 5] = true := by decide +kernel
theorem sub5_57 : sub5 [-2, -8] = true := by decide +kernel
theorem sub5_58 : sub5 [-2, -7] = true := by decide +kernel
theorem sub5_59 : sub5 [-2, -6] = true := by decide +kernel
theorem sub5_60 : sub5 [-2, -5] = true := by decide +kernel
theorem sub5_61 : sub5 [-2, -4] = true := by decide +kernel
theorem sub5_62 : sub5 [-2, -3, -9] = true := by decide +kernel
theorem sub5_63 : sub5 [-2, -3, -8] = true := by decide +kernel
theorem sb5_1 : ∀ q ∈ blk5_1, sub5 q = true := by
  unfold blk5_1
  exact List.forall_mem_cons.2 ⟨sub5_32, List.forall_mem_cons.2 ⟨sub5_33, List.forall_mem_cons.2 ⟨sub5_34, List.forall_mem_cons.2 ⟨sub5_35, List.forall_mem_cons.2 ⟨sub5_36, List.forall_mem_cons.2 ⟨sub5_37, List.forall_mem_cons.2 ⟨sub5_38, List.forall_mem_cons.2 ⟨sub5_39, List.forall_mem_cons.2 ⟨sub5_40, List.forall_mem_cons.2 ⟨sub5_41, List.forall_mem_cons.2 ⟨sub5_42, List.forall_mem_cons.2 ⟨sub5_43, List.forall_mem_cons.2 ⟨sub5_44, List.forall_mem_cons.2 ⟨sub5_45, List.forall_mem_cons.2 ⟨sub5_46, List.forall_mem_cons.2 ⟨sub5_47, List.forall_mem_cons.2 ⟨sub5_48, List.forall_mem_cons.2 ⟨sub5_49, List.forall_mem_cons.2 ⟨sub5_50, List.forall_mem_cons.2 ⟨sub5_51, List.forall_mem_cons.2 ⟨sub5_52, List.forall_mem_cons.2 ⟨sub5_53, List.forall_mem_cons.2 ⟨sub5_54, List.forall_mem_cons.2 ⟨sub5_55, List.forall_mem_cons.2 ⟨sub5_56, List.forall_mem_cons.2 ⟨sub5_57, List.forall_mem_cons.2 ⟨sub5_58, List.forall_mem_cons.2 ⟨sub5_59, List.forall_mem_cons.2 ⟨sub5_60, List.forall_mem_cons.2 ⟨sub5_61, List.forall_mem_cons.2 ⟨sub5_62, List.forall_mem_cons.2 ⟨sub5_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C060
