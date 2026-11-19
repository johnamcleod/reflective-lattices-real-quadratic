import ReflectZphi.Data.Cert5.C141.Base

namespace ReflectZphi.Data.Cert5.C141

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_0_352 : subd8_0 [2, 1, 0] = true := by decide +kernel
theorem subd8_0_353 : subd8_0 [2, 1, 1] = true := by decide +kernel
theorem subd8_0_354 : subd8_0 [2, 1, 2] = true := by decide +kernel
theorem subd8_0_355 : subd8_0 [2, 1, 3] = true := by decide +kernel
theorem subd8_0_356 : subd8_0 [2, 1, 4] = true := by decide +kernel
theorem subd8_0_357 : subd8_0 [2, 1, 5] = true := by decide +kernel
theorem subd8_0_358 : subd8_0 [2, 1, 6] = true := by decide +kernel
theorem subd8_0_359 : subd8_0 [2, 1, 7] = true := by decide +kernel
theorem subd8_0_360 : subd8_0 [2, 2, -5] = true := by decide +kernel
theorem subd8_0_361 : subd8_0 [2, 2, -4] = true := by decide +kernel
theorem subd8_0_362 : subd8_0 [2, 2, -3] = true := by decide +kernel
theorem subd8_0_363 : subd8_0 [2, 2, -2] = true := by decide +kernel
theorem subd8_0_364 : subd8_0 [2, 2, -1] = true := by decide +kernel
theorem subd8_0_365 : subd8_0 [2, 2, 0] = true := by decide +kernel
theorem subd8_0_366 : subd8_0 [2, 2, 1] = true := by decide +kernel
theorem subd8_0_367 : subd8_0 [2, 2, 2] = true := by decide +kernel
theorem subd8_0_368 : subd8_0 [2, 2, 3] = true := by decide +kernel
theorem subd8_0_369 : subd8_0 [2, 2, 4] = true := by decide +kernel
theorem subd8_0_370 : subd8_0 [2, 2, 5] = true := by decide +kernel
theorem subd8_0_371 : subd8_0 [2, 2, 6] = true := by decide +kernel
theorem subd8_0_372 : subd8_0 [2, 2, 7] = true := by decide +kernel
theorem subd8_0_373 : subd8_0 [2, 3] = true := by decide +kernel
theorem subd8_0_374 : subd8_0 [2, 4] = true := by decide +kernel
theorem subd8_0_375 : subd8_0 [3, -4] = true := by decide +kernel
theorem subd8_0_376 : subd8_0 [3, -3] = true := by decide +kernel
theorem subd8_0_377 : subd8_0 [3, -2] = true := by decide +kernel
theorem subd8_0_378 : subd8_0 [3, -1] = true := by decide +kernel
theorem subd8_0_379 : subd8_0 [3, 0] = true := by decide +kernel
theorem subd8_0_380 : subd8_0 [3, 1] = true := by decide +kernel
theorem subd8_0_381 : subd8_0 [3, 2] = true := by decide +kernel
theorem subd8_0_382 : subd8_0 [3, 3] = true := by decide +kernel
theorem subd8_0_383 : subd8_0 [3, 4] = true := by decide +kernel
theorem sbd8_0_11 : ∀ q ∈ blkd8_0_11, subd8_0 q = true := by
  unfold blkd8_0_11
  exact List.forall_mem_cons.2 ⟨subd8_0_352, List.forall_mem_cons.2 ⟨subd8_0_353, List.forall_mem_cons.2 ⟨subd8_0_354, List.forall_mem_cons.2 ⟨subd8_0_355, List.forall_mem_cons.2 ⟨subd8_0_356, List.forall_mem_cons.2 ⟨subd8_0_357, List.forall_mem_cons.2 ⟨subd8_0_358, List.forall_mem_cons.2 ⟨subd8_0_359, List.forall_mem_cons.2 ⟨subd8_0_360, List.forall_mem_cons.2 ⟨subd8_0_361, List.forall_mem_cons.2 ⟨subd8_0_362, List.forall_mem_cons.2 ⟨subd8_0_363, List.forall_mem_cons.2 ⟨subd8_0_364, List.forall_mem_cons.2 ⟨subd8_0_365, List.forall_mem_cons.2 ⟨subd8_0_366, List.forall_mem_cons.2 ⟨subd8_0_367, List.forall_mem_cons.2 ⟨subd8_0_368, List.forall_mem_cons.2 ⟨subd8_0_369, List.forall_mem_cons.2 ⟨subd8_0_370, List.forall_mem_cons.2 ⟨subd8_0_371, List.forall_mem_cons.2 ⟨subd8_0_372, List.forall_mem_cons.2 ⟨subd8_0_373, List.forall_mem_cons.2 ⟨subd8_0_374, List.forall_mem_cons.2 ⟨subd8_0_375, List.forall_mem_cons.2 ⟨subd8_0_376, List.forall_mem_cons.2 ⟨subd8_0_377, List.forall_mem_cons.2 ⟨subd8_0_378, List.forall_mem_cons.2 ⟨subd8_0_379, List.forall_mem_cons.2 ⟨subd8_0_380, List.forall_mem_cons.2 ⟨subd8_0_381, List.forall_mem_cons.2 ⟨subd8_0_382, List.forall_mem_cons.2 ⟨subd8_0_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_384 : subd8_0 [4, -3] = true := by decide +kernel
theorem subd8_0_385 : subd8_0 [4, -2] = true := by decide +kernel
theorem subd8_0_386 : subd8_0 [4, -1] = true := by decide +kernel
theorem subd8_0_387 : subd8_0 [4, 0] = true := by decide +kernel
theorem subd8_0_388 : subd8_0 [4, 1] = true := by decide +kernel
theorem subd8_0_389 : subd8_0 [4, 2] = true := by decide +kernel
theorem subd8_0_390 : subd8_0 [4, 3] = true := by decide +kernel
theorem subd8_0_391 : subd8_0 [4, 4] = true := by decide +kernel
theorem subd8_0_392 : subd8_0 [5] = true := by decide +kernel
theorem sbd8_0_12 : ∀ q ∈ blkd8_0_12, subd8_0 q = true := by
  unfold blkd8_0_12
  exact List.forall_mem_cons.2 ⟨subd8_0_384, List.forall_mem_cons.2 ⟨subd8_0_385, List.forall_mem_cons.2 ⟨subd8_0_386, List.forall_mem_cons.2 ⟨subd8_0_387, List.forall_mem_cons.2 ⟨subd8_0_388, List.forall_mem_cons.2 ⟨subd8_0_389, List.forall_mem_cons.2 ⟨subd8_0_390, List.forall_mem_cons.2 ⟨subd8_0_391, List.forall_mem_cons.2 ⟨subd8_0_392, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_1 : ldCheck G d8_1.U d8_1.ms ldd8_1 = true := by decide +kernel
theorem pre_okd8_1 : subPre G cell8 d8_1 = true := by decide +kernel
theorem subd8_1_0 : subd8_1 [-2, -1] = true := by decide +kernel
theorem subd8_1_1 : subd8_1 [-2, 0] = true := by decide +kernel
theorem subd8_1_2 : subd8_1 [-2, 1] = true := by decide +kernel
theorem subd8_1_3 : subd8_1 [-2, 2] = true := by decide +kernel
theorem subd8_1_4 : subd8_1 [-1, -3] = true := by decide +kernel
theorem subd8_1_5 : subd8_1 [-1, -2] = true := by decide +kernel
theorem subd8_1_6 : subd8_1 [-1, -1] = true := by decide +kernel
theorem subd8_1_7 : subd8_1 [-1, 0] = true := by decide +kernel
theorem subd8_1_8 : subd8_1 [-1, 1] = true := by decide +kernel
theorem subd8_1_9 : subd8_1 [-1, 2] = true := by decide +kernel
theorem subd8_1_10 : subd8_1 [-1, 3] = true := by decide +kernel
theorem subd8_1_11 : subd8_1 [0, -3] = true := by decide +kernel
theorem subd8_1_12 : subd8_1 [0, -2] = true := by decide +kernel
theorem subd8_1_13 : subd8_1 [0, -1] = true := by decide +kernel
theorem subd8_1_14 : subd8_1 [0, 0] = true := by decide +kernel
theorem subd8_1_15 : subd8_1 [0, 1] = true := by decide +kernel
theorem subd8_1_16 : subd8_1 [0, 2] = true := by decide +kernel
theorem subd8_1_17 : subd8_1 [1, -4] = true := by decide +kernel
theorem subd8_1_18 : subd8_1 [1, -3] = true := by decide +kernel
theorem subd8_1_19 : subd8_1 [1, -2] = true := by decide +kernel
theorem subd8_1_20 : subd8_1 [1, -1] = true := by decide +kernel
theorem subd8_1_21 : subd8_1 [1, 0] = true := by decide +kernel
theorem subd8_1_22 : subd8_1 [1, 1] = true := by decide +kernel
theorem subd8_1_23 : subd8_1 [1, 2] = true := by decide +kernel
theorem subd8_1_24 : subd8_1 [2, -3] = true := by decide +kernel
theorem subd8_1_25 : subd8_1 [2, -2] = true := by decide +kernel
theorem subd8_1_26 : subd8_1 [2, -1] = true := by decide +kernel
theorem subd8_1_27 : subd8_1 [2, 0] = true := by decide +kernel
theorem sbd8_1_0 : ∀ q ∈ blkd8_1_0, subd8_1 q = true := by
  unfold blkd8_1_0
  exact List.forall_mem_cons.2 ⟨subd8_1_0, List.forall_mem_cons.2 ⟨subd8_1_1, List.forall_mem_cons.2 ⟨subd8_1_2, List.forall_mem_cons.2 ⟨subd8_1_3, List.forall_mem_cons.2 ⟨subd8_1_4, List.forall_mem_cons.2 ⟨subd8_1_5, List.forall_mem_cons.2 ⟨subd8_1_6, List.forall_mem_cons.2 ⟨subd8_1_7, List.forall_mem_cons.2 ⟨subd8_1_8, List.forall_mem_cons.2 ⟨subd8_1_9, List.forall_mem_cons.2 ⟨subd8_1_10, List.forall_mem_cons.2 ⟨subd8_1_11, List.forall_mem_cons.2 ⟨subd8_1_12, List.forall_mem_cons.2 ⟨subd8_1_13, List.forall_mem_cons.2 ⟨subd8_1_14, List.forall_mem_cons.2 ⟨subd8_1_15, List.forall_mem_cons.2 ⟨subd8_1_16, List.forall_mem_cons.2 ⟨subd8_1_17, List.forall_mem_cons.2 ⟨subd8_1_18, List.forall_mem_cons.2 ⟨subd8_1_19, List.forall_mem_cons.2 ⟨subd8_1_20, List.forall_mem_cons.2 ⟨subd8_1_21, List.forall_mem_cons.2 ⟨subd8_1_22, List.forall_mem_cons.2 ⟨subd8_1_23, List.forall_mem_cons.2 ⟨subd8_1_24, List.forall_mem_cons.2 ⟨subd8_1_25, List.forall_mem_cons.2 ⟨subd8_1_26, List.forall_mem_cons.2 ⟨subd8_1_27, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_2 : ldCheck G d8_2.U d8_2.ms ldd8_2 = true := by decide +kernel
theorem pre_okd8_2 : subPre G cell8 d8_2 = true := by decide +kernel
theorem subd8_2_0 : subd8_2 [-5, -4] = true := by decide +kernel
theorem subd8_2_1 : subd8_2 [-5, -3] = true := by decide +kernel
theorem subd8_2_2 : subd8_2 [-5, -2] = true := by decide +kernel
theorem subd8_2_3 : subd8_2 [-5, -1] = true := by decide +kernel
theorem subd8_2_4 : subd8_2 [-5, 0] = true := by decide +kernel
theorem subd8_2_5 : subd8_2 [-5, 1] = true := by decide +kernel
theorem subd8_2_6 : subd8_2 [-4, -5] = true := by decide +kernel
theorem subd8_2_7 : subd8_2 [-4, -4] = true := by decide +kernel
theorem subd8_2_8 : subd8_2 [-4, -3] = true := by decide +kernel
theorem subd8_2_9 : subd8_2 [-4, -2] = true := by decide +kernel
theorem subd8_2_10 : subd8_2 [-4, -1] = true := by decide +kernel
theorem subd8_2_11 : subd8_2 [-4, 0] = true := by decide +kernel
theorem subd8_2_12 : subd8_2 [-4, 1] = true := by decide +kernel
theorem subd8_2_13 : subd8_2 [-4, 2] = true := by decide +kernel
theorem subd8_2_14 : subd8_2 [-3, -5] = true := by decide +kernel
theorem subd8_2_15 : subd8_2 [-3, -4] = true := by decide +kernel
theorem subd8_2_16 : subd8_2 [-3, -3] = true := by decide +kernel
theorem subd8_2_17 : subd8_2 [-3, -2] = true := by decide +kernel
theorem subd8_2_18 : subd8_2 [-3, -1] = true := by decide +kernel
theorem subd8_2_19 : subd8_2 [-3, 0] = true := by decide +kernel
theorem subd8_2_20 : subd8_2 [-3, 1] = true := by decide +kernel
theorem subd8_2_21 : subd8_2 [-3, 2] = true := by decide +kernel
theorem subd8_2_22 : subd8_2 [-3, 3] = true := by decide +kernel
theorem subd8_2_23 : subd8_2 [-2, -6] = true := by decide +kernel
theorem subd8_2_24 : subd8_2 [-2, -5] = true := by decide +kernel
theorem subd8_2_25 : subd8_2 [-2, -4] = true := by decide +kernel
theorem subd8_2_26 : subd8_2 [-2, -3] = true := by decide +kernel
theorem subd8_2_27 : subd8_2 [-2, -2] = true := by decide +kernel
theorem subd8_2_28 : subd8_2 [-2, -1] = true := by decide +kernel
theorem subd8_2_29 : subd8_2 [-2, 0] = true := by decide +kernel
theorem subd8_2_30 : subd8_2 [-2, 1] = true := by decide +kernel
theorem subd8_2_31 : subd8_2 [-2, 2] = true := by decide +kernel
theorem sbd8_2_0 : ∀ q ∈ blkd8_2_0, subd8_2 q = true := by
  unfold blkd8_2_0
  exact List.forall_mem_cons.2 ⟨subd8_2_0, List.forall_mem_cons.2 ⟨subd8_2_1, List.forall_mem_cons.2 ⟨subd8_2_2, List.forall_mem_cons.2 ⟨subd8_2_3, List.forall_mem_cons.2 ⟨subd8_2_4, List.forall_mem_cons.2 ⟨subd8_2_5, List.forall_mem_cons.2 ⟨subd8_2_6, List.forall_mem_cons.2 ⟨subd8_2_7, List.forall_mem_cons.2 ⟨subd8_2_8, List.forall_mem_cons.2 ⟨subd8_2_9, List.forall_mem_cons.2 ⟨subd8_2_10, List.forall_mem_cons.2 ⟨subd8_2_11, List.forall_mem_cons.2 ⟨subd8_2_12, List.forall_mem_cons.2 ⟨subd8_2_13, List.forall_mem_cons.2 ⟨subd8_2_14, List.forall_mem_cons.2 ⟨subd8_2_15, List.forall_mem_cons.2 ⟨subd8_2_16, List.forall_mem_cons.2 ⟨subd8_2_17, List.forall_mem_cons.2 ⟨subd8_2_18, List.forall_mem_cons.2 ⟨subd8_2_19, List.forall_mem_cons.2 ⟨subd8_2_20, List.forall_mem_cons.2 ⟨subd8_2_21, List.forall_mem_cons.2 ⟨subd8_2_22, List.forall_mem_cons.2 ⟨subd8_2_23, List.forall_mem_cons.2 ⟨subd8_2_24, List.forall_mem_cons.2 ⟨subd8_2_25, List.forall_mem_cons.2 ⟨subd8_2_26, List.forall_mem_cons.2 ⟨subd8_2_27, List.forall_mem_cons.2 ⟨subd8_2_28, List.forall_mem_cons.2 ⟨subd8_2_29, List.forall_mem_cons.2 ⟨subd8_2_30, List.forall_mem_cons.2 ⟨subd8_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C141
