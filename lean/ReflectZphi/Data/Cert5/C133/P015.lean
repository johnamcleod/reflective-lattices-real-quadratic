import ReflectZphi.Data.Cert5.C133.Base

namespace ReflectZphi.Data.Cert5.C133

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_3_384 : subd9_3 [2, -1, 7] = true := by decide +kernel
theorem subd9_3_385 : subd9_3 [2, 0, -10] = true := by decide +kernel
theorem subd9_3_386 : subd9_3 [2, 0, -9] = true := by decide +kernel
theorem subd9_3_387 : subd9_3 [2, 0, -8] = true := by decide +kernel
theorem subd9_3_388 : subd9_3 [2, 0, -7] = true := by decide +kernel
theorem subd9_3_389 : subd9_3 [2, 0, -6] = true := by decide +kernel
theorem subd9_3_390 : subd9_3 [2, 0, -5] = true := by decide +kernel
theorem subd9_3_391 : subd9_3 [2, 0, -4] = true := by decide +kernel
theorem subd9_3_392 : subd9_3 [2, 0, -3] = true := by decide +kernel
theorem subd9_3_393 : subd9_3 [2, 0, -2] = true := by decide +kernel
theorem subd9_3_394 : subd9_3 [2, 0, -1] = true := by decide +kernel
theorem subd9_3_395 : subd9_3 [2, 0, 0] = true := by decide +kernel
theorem subd9_3_396 : subd9_3 [2, 0, 1] = true := by decide +kernel
theorem subd9_3_397 : subd9_3 [2, 0, 2] = true := by decide +kernel
theorem subd9_3_398 : subd9_3 [2, 0, 3] = true := by decide +kernel
theorem subd9_3_399 : subd9_3 [2, 0, 4] = true := by decide +kernel
theorem subd9_3_400 : subd9_3 [2, 0, 5] = true := by decide +kernel
theorem subd9_3_401 : subd9_3 [2, 0, 6] = true := by decide +kernel
theorem subd9_3_402 : subd9_3 [2, 0, 7] = true := by decide +kernel
theorem subd9_3_403 : subd9_3 [2, 0, 8] = true := by decide +kernel
theorem subd9_3_404 : subd9_3 [2, 1, -9] = true := by decide +kernel
theorem subd9_3_405 : subd9_3 [2, 1, -8] = true := by decide +kernel
theorem subd9_3_406 : subd9_3 [2, 1, -7] = true := by decide +kernel
theorem subd9_3_407 : subd9_3 [2, 1, -6] = true := by decide +kernel
theorem subd9_3_408 : subd9_3 [2, 1, -5] = true := by decide +kernel
theorem subd9_3_409 : subd9_3 [2, 1, -4] = true := by decide +kernel
theorem subd9_3_410 : subd9_3 [2, 1, -3] = true := by decide +kernel
theorem subd9_3_411 : subd9_3 [2, 1, -2] = true := by decide +kernel
theorem subd9_3_412 : subd9_3 [2, 1, -1] = true := by decide +kernel
theorem subd9_3_413 : subd9_3 [2, 1, 0] = true := by decide +kernel
theorem subd9_3_414 : subd9_3 [2, 1, 1] = true := by decide +kernel
theorem subd9_3_415 : subd9_3 [2, 1, 2] = true := by decide +kernel
theorem sbd9_3_12 : ∀ q ∈ blkd9_3_12, subd9_3 q = true := by
  unfold blkd9_3_12
  exact List.forall_mem_cons.2 ⟨subd9_3_384, List.forall_mem_cons.2 ⟨subd9_3_385, List.forall_mem_cons.2 ⟨subd9_3_386, List.forall_mem_cons.2 ⟨subd9_3_387, List.forall_mem_cons.2 ⟨subd9_3_388, List.forall_mem_cons.2 ⟨subd9_3_389, List.forall_mem_cons.2 ⟨subd9_3_390, List.forall_mem_cons.2 ⟨subd9_3_391, List.forall_mem_cons.2 ⟨subd9_3_392, List.forall_mem_cons.2 ⟨subd9_3_393, List.forall_mem_cons.2 ⟨subd9_3_394, List.forall_mem_cons.2 ⟨subd9_3_395, List.forall_mem_cons.2 ⟨subd9_3_396, List.forall_mem_cons.2 ⟨subd9_3_397, List.forall_mem_cons.2 ⟨subd9_3_398, List.forall_mem_cons.2 ⟨subd9_3_399, List.forall_mem_cons.2 ⟨subd9_3_400, List.forall_mem_cons.2 ⟨subd9_3_401, List.forall_mem_cons.2 ⟨subd9_3_402, List.forall_mem_cons.2 ⟨subd9_3_403, List.forall_mem_cons.2 ⟨subd9_3_404, List.forall_mem_cons.2 ⟨subd9_3_405, List.forall_mem_cons.2 ⟨subd9_3_406, List.forall_mem_cons.2 ⟨subd9_3_407, List.forall_mem_cons.2 ⟨subd9_3_408, List.forall_mem_cons.2 ⟨subd9_3_409, List.forall_mem_cons.2 ⟨subd9_3_410, List.forall_mem_cons.2 ⟨subd9_3_411, List.forall_mem_cons.2 ⟨subd9_3_412, List.forall_mem_cons.2 ⟨subd9_3_413, List.forall_mem_cons.2 ⟨subd9_3_414, List.forall_mem_cons.2 ⟨subd9_3_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_416 : subd9_3 [2, 1, 3] = true := by decide +kernel
theorem subd9_3_417 : subd9_3 [2, 1, 4] = true := by decide +kernel
theorem subd9_3_418 : subd9_3 [2, 1, 5] = true := by decide +kernel
theorem subd9_3_419 : subd9_3 [2, 1, 6] = true := by decide +kernel
theorem subd9_3_420 : subd9_3 [2, 1, 7] = true := by decide +kernel
theorem subd9_3_421 : subd9_3 [2, 2] = true := by decide +kernel
theorem subd9_3_422 : subd9_3 [3] = true := by decide +kernel
theorem sbd9_3_13 : ∀ q ∈ blkd9_3_13, subd9_3 q = true := by
  unfold blkd9_3_13
  exact List.forall_mem_cons.2 ⟨subd9_3_416, List.forall_mem_cons.2 ⟨subd9_3_417, List.forall_mem_cons.2 ⟨subd9_3_418, List.forall_mem_cons.2 ⟨subd9_3_419, List.forall_mem_cons.2 ⟨subd9_3_420, List.forall_mem_cons.2 ⟨subd9_3_421, List.forall_mem_cons.2 ⟨subd9_3_422, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_0 : ldCheck G d10_0.U d10_0.ms ldd10_0 = true := by decide +kernel
theorem pre_okd10_0 : subPre G cell10 d10_0 = true := by decide +kernel
theorem subd10_0_0 : subd10_0 [-2] = true := by decide +kernel
theorem subd10_0_1 : subd10_0 [-1, -3] = true := by decide +kernel
theorem subd10_0_2 : subd10_0 [-1, -2] = true := by decide +kernel
theorem subd10_0_3 : subd10_0 [-1, -1] = true := by decide +kernel
theorem subd10_0_4 : subd10_0 [-1, 0] = true := by decide +kernel
theorem subd10_0_5 : subd10_0 [-1, 1] = true := by decide +kernel
theorem subd10_0_6 : subd10_0 [-1, 2] = true := by decide +kernel
theorem subd10_0_7 : subd10_0 [0, -3] = true := by decide +kernel
theorem subd10_0_8 : subd10_0 [0, -2] = true := by decide +kernel
theorem subd10_0_9 : subd10_0 [0, -1] = true := by decide +kernel
theorem subd10_0_10 : subd10_0 [0, 0] = true := by decide +kernel
theorem subd10_0_11 : subd10_0 [0, 1] = true := by decide +kernel
theorem subd10_0_12 : subd10_0 [0, 2] = true := by decide +kernel
theorem subd10_0_13 : subd10_0 [1, -3] = true := by decide +kernel
theorem subd10_0_14 : subd10_0 [1, -2] = true := by decide +kernel
theorem subd10_0_15 : subd10_0 [1, -1] = true := by decide +kernel
theorem subd10_0_16 : subd10_0 [1, 0] = true := by decide +kernel
theorem subd10_0_17 : subd10_0 [1, 1] = true := by decide +kernel
theorem subd10_0_18 : subd10_0 [1, 2] = true := by decide +kernel
theorem subd10_0_19 : subd10_0 [2] = true := by decide +kernel
theorem sbd10_0_0 : ∀ q ∈ blkd10_0_0, subd10_0 q = true := by
  unfold blkd10_0_0
  exact List.forall_mem_cons.2 ⟨subd10_0_0, List.forall_mem_cons.2 ⟨subd10_0_1, List.forall_mem_cons.2 ⟨subd10_0_2, List.forall_mem_cons.2 ⟨subd10_0_3, List.forall_mem_cons.2 ⟨subd10_0_4, List.forall_mem_cons.2 ⟨subd10_0_5, List.forall_mem_cons.2 ⟨subd10_0_6, List.forall_mem_cons.2 ⟨subd10_0_7, List.forall_mem_cons.2 ⟨subd10_0_8, List.forall_mem_cons.2 ⟨subd10_0_9, List.forall_mem_cons.2 ⟨subd10_0_10, List.forall_mem_cons.2 ⟨subd10_0_11, List.forall_mem_cons.2 ⟨subd10_0_12, List.forall_mem_cons.2 ⟨subd10_0_13, List.forall_mem_cons.2 ⟨subd10_0_14, List.forall_mem_cons.2 ⟨subd10_0_15, List.forall_mem_cons.2 ⟨subd10_0_16, List.forall_mem_cons.2 ⟨subd10_0_17, List.forall_mem_cons.2 ⟨subd10_0_18, List.forall_mem_cons.2 ⟨subd10_0_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_1 : ldCheck G d10_1.U d10_1.ms ldd10_1 = true := by decide +kernel
theorem pre_okd10_1 : subPre G cell10 d10_1 = true := by decide +kernel
theorem subd10_1_0 : subd10_1 [-1, -2] = true := by decide +kernel
theorem subd10_1_1 : subd10_1 [-1, -1] = true := by decide +kernel
theorem subd10_1_2 : subd10_1 [-1, 0] = true := by decide +kernel
theorem subd10_1_3 : subd10_1 [-1, 1] = true := by decide +kernel
theorem subd10_1_4 : subd10_1 [0, -2] = true := by decide +kernel
theorem subd10_1_5 : subd10_1 [0, -1] = true := by decide +kernel
theorem subd10_1_6 : subd10_1 [0, 0, -7] = true := by decide +kernel
theorem subd10_1_7 : subd10_1 [0, 0, -6] = true := by decide +kernel
theorem subd10_1_8 : subd10_1 [0, 0, -5] = true := by decide +kernel
theorem subd10_1_9 : subd10_1 [0, 0, -4] = true := by decide +kernel
theorem subd10_1_10 : subd10_1 [0, 0, -3] = true := by decide +kernel
theorem subd10_1_11 : subd10_1 [0, 0, -2] = true := by decide +kernel
theorem subd10_1_12 : subd10_1 [0, 0, -1] = true := by decide +kernel
theorem subd10_1_13 : subd10_1 [0, 0, 0] = true := by decide +kernel
theorem subd10_1_14 : subd10_1 [0, 0, 1] = true := by decide +kernel
theorem subd10_1_15 : subd10_1 [0, 0, 2] = true := by decide +kernel
theorem subd10_1_16 : subd10_1 [0, 0, 3] = true := by decide +kernel
theorem subd10_1_17 : subd10_1 [0, 0, 4] = true := by decide +kernel
theorem subd10_1_18 : subd10_1 [0, 0, 5] = true := by decide +kernel
theorem subd10_1_19 : subd10_1 [0, 0, 6] = true := by decide +kernel
theorem subd10_1_20 : subd10_1 [0, 1] = true := by decide +kernel
theorem subd10_1_21 : subd10_1 [1, -2] = true := by decide +kernel
theorem subd10_1_22 : subd10_1 [1, -1] = true := by decide +kernel
theorem subd10_1_23 : subd10_1 [1, 0] = true := by decide +kernel
theorem subd10_1_24 : subd10_1 [1, 1] = true := by decide +kernel
theorem sbd10_1_0 : ∀ q ∈ blkd10_1_0, subd10_1 q = true := by
  unfold blkd10_1_0
  exact List.forall_mem_cons.2 ⟨subd10_1_0, List.forall_mem_cons.2 ⟨subd10_1_1, List.forall_mem_cons.2 ⟨subd10_1_2, List.forall_mem_cons.2 ⟨subd10_1_3, List.forall_mem_cons.2 ⟨subd10_1_4, List.forall_mem_cons.2 ⟨subd10_1_5, List.forall_mem_cons.2 ⟨subd10_1_6, List.forall_mem_cons.2 ⟨subd10_1_7, List.forall_mem_cons.2 ⟨subd10_1_8, List.forall_mem_cons.2 ⟨subd10_1_9, List.forall_mem_cons.2 ⟨subd10_1_10, List.forall_mem_cons.2 ⟨subd10_1_11, List.forall_mem_cons.2 ⟨subd10_1_12, List.forall_mem_cons.2 ⟨subd10_1_13, List.forall_mem_cons.2 ⟨subd10_1_14, List.forall_mem_cons.2 ⟨subd10_1_15, List.forall_mem_cons.2 ⟨subd10_1_16, List.forall_mem_cons.2 ⟨subd10_1_17, List.forall_mem_cons.2 ⟨subd10_1_18, List.forall_mem_cons.2 ⟨subd10_1_19, List.forall_mem_cons.2 ⟨subd10_1_20, List.forall_mem_cons.2 ⟨subd10_1_21, List.forall_mem_cons.2 ⟨subd10_1_22, List.forall_mem_cons.2 ⟨subd10_1_23, List.forall_mem_cons.2 ⟨subd10_1_24, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_2 : ldCheck G d10_2.U d10_2.ms ldd10_2 = true := by decide +kernel
theorem pre_okd10_2 : subPre G cell10 d10_2 = true := by decide +kernel
theorem subd10_2_0 : subd10_2 [-5] = true := by decide +kernel
theorem subd10_2_1 : subd10_2 [-4, -4] = true := by decide +kernel
theorem subd10_2_2 : subd10_2 [-4, -3] = true := by decide +kernel
theorem subd10_2_3 : subd10_2 [-4, -2] = true := by decide +kernel
theorem subd10_2_4 : subd10_2 [-4, -1] = true := by decide +kernel
theorem subd10_2_5 : subd10_2 [-4, 0] = true := by decide +kernel
theorem subd10_2_6 : subd10_2 [-4, 1] = true := by decide +kernel
theorem subd10_2_7 : subd10_2 [-4, 2] = true := by decide +kernel
theorem subd10_2_8 : subd10_2 [-4, 3] = true := by decide +kernel
theorem subd10_2_9 : subd10_2 [-3, -5] = true := by decide +kernel
theorem subd10_2_10 : subd10_2 [-3, -4] = true := by decide +kernel
theorem subd10_2_11 : subd10_2 [-3, -3] = true := by decide +kernel
theorem subd10_2_12 : subd10_2 [-3, -2] = true := by decide +kernel
theorem subd10_2_13 : subd10_2 [-3, -1] = true := by decide +kernel
theorem subd10_2_14 : subd10_2 [-3, 0, -6] = true := by decide +kernel
theorem subd10_2_15 : subd10_2 [-3, 0, -5] = true := by decide +kernel
theorem subd10_2_16 : subd10_2 [-3, 0, -4] = true := by decide +kernel
theorem subd10_2_17 : subd10_2 [-3, 0, -3] = true := by decide +kernel
theorem subd10_2_18 : subd10_2 [-3, 0, -2] = true := by decide +kernel
theorem subd10_2_19 : subd10_2 [-3, 0, -1] = true := by decide +kernel
theorem subd10_2_20 : subd10_2 [-3, 0, 0] = true := by decide +kernel
theorem subd10_2_21 : subd10_2 [-3, 0, 1] = true := by decide +kernel
theorem subd10_2_22 : subd10_2 [-3, 0, 2] = true := by decide +kernel
theorem subd10_2_23 : subd10_2 [-3, 0, 3] = true := by decide +kernel
theorem subd10_2_24 : subd10_2 [-3, 0, 4] = true := by decide +kernel
theorem subd10_2_25 : subd10_2 [-3, 0, 5] = true := by decide +kernel
theorem subd10_2_26 : subd10_2 [-3, 0, 6] = true := by decide +kernel
theorem subd10_2_27 : subd10_2 [-3, 0, 7] = true := by decide +kernel
theorem subd10_2_28 : subd10_2 [-3, 1] = true := by decide +kernel
theorem subd10_2_29 : subd10_2 [-3, 2] = true := by decide +kernel
theorem subd10_2_30 : subd10_2 [-3, 3] = true := by decide +kernel
theorem subd10_2_31 : subd10_2 [-3, 4] = true := by decide +kernel
theorem sbd10_2_0 : ∀ q ∈ blkd10_2_0, subd10_2 q = true := by
  unfold blkd10_2_0
  exact List.forall_mem_cons.2 ⟨subd10_2_0, List.forall_mem_cons.2 ⟨subd10_2_1, List.forall_mem_cons.2 ⟨subd10_2_2, List.forall_mem_cons.2 ⟨subd10_2_3, List.forall_mem_cons.2 ⟨subd10_2_4, List.forall_mem_cons.2 ⟨subd10_2_5, List.forall_mem_cons.2 ⟨subd10_2_6, List.forall_mem_cons.2 ⟨subd10_2_7, List.forall_mem_cons.2 ⟨subd10_2_8, List.forall_mem_cons.2 ⟨subd10_2_9, List.forall_mem_cons.2 ⟨subd10_2_10, List.forall_mem_cons.2 ⟨subd10_2_11, List.forall_mem_cons.2 ⟨subd10_2_12, List.forall_mem_cons.2 ⟨subd10_2_13, List.forall_mem_cons.2 ⟨subd10_2_14, List.forall_mem_cons.2 ⟨subd10_2_15, List.forall_mem_cons.2 ⟨subd10_2_16, List.forall_mem_cons.2 ⟨subd10_2_17, List.forall_mem_cons.2 ⟨subd10_2_18, List.forall_mem_cons.2 ⟨subd10_2_19, List.forall_mem_cons.2 ⟨subd10_2_20, List.forall_mem_cons.2 ⟨subd10_2_21, List.forall_mem_cons.2 ⟨subd10_2_22, List.forall_mem_cons.2 ⟨subd10_2_23, List.forall_mem_cons.2 ⟨subd10_2_24, List.forall_mem_cons.2 ⟨subd10_2_25, List.forall_mem_cons.2 ⟨subd10_2_26, List.forall_mem_cons.2 ⟨subd10_2_27, List.forall_mem_cons.2 ⟨subd10_2_28, List.forall_mem_cons.2 ⟨subd10_2_29, List.forall_mem_cons.2 ⟨subd10_2_30, List.forall_mem_cons.2 ⟨subd10_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_2_32 : subd10_2 [-2, -5] = true := by decide +kernel
theorem subd10_2_33 : subd10_2 [-2, -4] = true := by decide +kernel
theorem subd10_2_34 : subd10_2 [-2, -3] = true := by decide +kernel
theorem subd10_2_35 : subd10_2 [-2, -2, -6] = true := by decide +kernel
theorem subd10_2_36 : subd10_2 [-2, -2, -5] = true := by decide +kernel
theorem subd10_2_37 : subd10_2 [-2, -2, -4] = true := by decide +kernel
theorem subd10_2_38 : subd10_2 [-2, -2, -3] = true := by decide +kernel
theorem subd10_2_39 : subd10_2 [-2, -2, -2] = true := by decide +kernel
theorem subd10_2_40 : subd10_2 [-2, -2, -1] = true := by decide +kernel
theorem subd10_2_41 : subd10_2 [-2, -2, 0] = true := by decide +kernel
theorem subd10_2_42 : subd10_2 [-2, -2, 1] = true := by decide +kernel
theorem subd10_2_43 : subd10_2 [-2, -2, 2] = true := by decide +kernel
theorem subd10_2_44 : subd10_2 [-2, -2, 3] = true := by decide +kernel
theorem subd10_2_45 : subd10_2 [-2, -2, 4] = true := by decide +kernel
theorem subd10_2_46 : subd10_2 [-2, -2, 5] = true := by decide +kernel
theorem subd10_2_47 : subd10_2 [-2, -2, 6] = true := by decide +kernel
theorem subd10_2_48 : subd10_2 [-2, -2, 7] = true := by decide +kernel
theorem subd10_2_49 : subd10_2 [-2, -1, -7] = true := by decide +kernel
theorem subd10_2_50 : subd10_2 [-2, -1, -6] = true := by decide +kernel
theorem subd10_2_51 : subd10_2 [-2, -1, -5] = true := by decide +kernel
theorem subd10_2_52 : subd10_2 [-2, -1, -4] = true := by decide +kernel
theorem subd10_2_53 : subd10_2 [-2, -1, -3] = true := by decide +kernel
theorem subd10_2_54 : subd10_2 [-2, -1, -2] = true := by decide +kernel
theorem subd10_2_55 : subd10_2 [-2, -1, -1] = true := by decide +kernel
theorem subd10_2_56 : subd10_2 [-2, -1, 0] = true := by decide +kernel
theorem subd10_2_57 : subd10_2 [-2, -1, 1] = true := by decide +kernel
theorem subd10_2_58 : subd10_2 [-2, -1, 2] = true := by decide +kernel
theorem subd10_2_59 : subd10_2 [-2, -1, 3] = true := by decide +kernel
theorem subd10_2_60 : subd10_2 [-2, -1, 4] = true := by decide +kernel
theorem subd10_2_61 : subd10_2 [-2, -1, 5] = true := by decide +kernel
theorem subd10_2_62 : subd10_2 [-2, -1, 6] = true := by decide +kernel
theorem subd10_2_63 : subd10_2 [-2, -1, 7] = true := by decide +kernel
theorem sbd10_2_1 : ∀ q ∈ blkd10_2_1, subd10_2 q = true := by
  unfold blkd10_2_1
  exact List.forall_mem_cons.2 ⟨subd10_2_32, List.forall_mem_cons.2 ⟨subd10_2_33, List.forall_mem_cons.2 ⟨subd10_2_34, List.forall_mem_cons.2 ⟨subd10_2_35, List.forall_mem_cons.2 ⟨subd10_2_36, List.forall_mem_cons.2 ⟨subd10_2_37, List.forall_mem_cons.2 ⟨subd10_2_38, List.forall_mem_cons.2 ⟨subd10_2_39, List.forall_mem_cons.2 ⟨subd10_2_40, List.forall_mem_cons.2 ⟨subd10_2_41, List.forall_mem_cons.2 ⟨subd10_2_42, List.forall_mem_cons.2 ⟨subd10_2_43, List.forall_mem_cons.2 ⟨subd10_2_44, List.forall_mem_cons.2 ⟨subd10_2_45, List.forall_mem_cons.2 ⟨subd10_2_46, List.forall_mem_cons.2 ⟨subd10_2_47, List.forall_mem_cons.2 ⟨subd10_2_48, List.forall_mem_cons.2 ⟨subd10_2_49, List.forall_mem_cons.2 ⟨subd10_2_50, List.forall_mem_cons.2 ⟨subd10_2_51, List.forall_mem_cons.2 ⟨subd10_2_52, List.forall_mem_cons.2 ⟨subd10_2_53, List.forall_mem_cons.2 ⟨subd10_2_54, List.forall_mem_cons.2 ⟨subd10_2_55, List.forall_mem_cons.2 ⟨subd10_2_56, List.forall_mem_cons.2 ⟨subd10_2_57, List.forall_mem_cons.2 ⟨subd10_2_58, List.forall_mem_cons.2 ⟨subd10_2_59, List.forall_mem_cons.2 ⟨subd10_2_60, List.forall_mem_cons.2 ⟨subd10_2_61, List.forall_mem_cons.2 ⟨subd10_2_62, List.forall_mem_cons.2 ⟨subd10_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_2_64 : subd10_2 [-2, -1, 8] = true := by decide +kernel
theorem subd10_2_65 : subd10_2 [-2, 0, -8] = true := by decide +kernel
theorem subd10_2_66 : subd10_2 [-2, 0, -7] = true := by decide +kernel
theorem subd10_2_67 : subd10_2 [-2, 0, -6] = true := by decide +kernel
theorem subd10_2_68 : subd10_2 [-2, 0, -5] = true := by decide +kernel
theorem subd10_2_69 : subd10_2 [-2, 0, -4] = true := by decide +kernel
theorem subd10_2_70 : subd10_2 [-2, 0, -3] = true := by decide +kernel
theorem subd10_2_71 : subd10_2 [-2, 0, -2] = true := by decide +kernel
theorem subd10_2_72 : subd10_2 [-2, 0, -1] = true := by decide +kernel
theorem subd10_2_73 : subd10_2 [-2, 0, 0] = true := by decide +kernel
theorem subd10_2_74 : subd10_2 [-2, 0, 1] = true := by decide +kernel
theorem subd10_2_75 : subd10_2 [-2, 0, 2] = true := by decide +kernel
theorem subd10_2_76 : subd10_2 [-2, 0, 3] = true := by decide +kernel
theorem subd10_2_77 : subd10_2 [-2, 0, 4] = true := by decide +kernel
theorem subd10_2_78 : subd10_2 [-2, 0, 5] = true := by decide +kernel
theorem subd10_2_79 : subd10_2 [-2, 0, 6] = true := by decide +kernel
theorem subd10_2_80 : subd10_2 [-2, 0, 7] = true := by decide +kernel
theorem subd10_2_81 : subd10_2 [-2, 1, -8] = true := by decide +kernel
theorem subd10_2_82 : subd10_2 [-2, 1, -7] = true := by decide +kernel
theorem subd10_2_83 : subd10_2 [-2, 1, -6] = true := by decide +kernel
theorem subd10_2_84 : subd10_2 [-2, 1, -5] = true := by decide +kernel
theorem subd10_2_85 : subd10_2 [-2, 1, -4] = true := by decide +kernel
theorem subd10_2_86 : subd10_2 [-2, 1, -3] = true := by decide +kernel
theorem subd10_2_87 : subd10_2 [-2, 1, -2] = true := by decide +kernel
theorem subd10_2_88 : subd10_2 [-2, 1, -1] = true := by decide +kernel
theorem subd10_2_89 : subd10_2 [-2, 1, 0] = true := by decide +kernel
theorem subd10_2_90 : subd10_2 [-2, 1, 1] = true := by decide +kernel
theorem subd10_2_91 : subd10_2 [-2, 1, 2] = true := by decide +kernel
theorem subd10_2_92 : subd10_2 [-2, 1, 3] = true := by decide +kernel
theorem subd10_2_93 : subd10_2 [-2, 1, 4] = true := by decide +kernel
theorem subd10_2_94 : subd10_2 [-2, 1, 5] = true := by decide +kernel
theorem subd10_2_95 : subd10_2 [-2, 1, 6] = true := by decide +kernel
theorem sbd10_2_2 : ∀ q ∈ blkd10_2_2, subd10_2 q = true := by
  unfold blkd10_2_2
  exact List.forall_mem_cons.2 ⟨subd10_2_64, List.forall_mem_cons.2 ⟨subd10_2_65, List.forall_mem_cons.2 ⟨subd10_2_66, List.forall_mem_cons.2 ⟨subd10_2_67, List.forall_mem_cons.2 ⟨subd10_2_68, List.forall_mem_cons.2 ⟨subd10_2_69, List.forall_mem_cons.2 ⟨subd10_2_70, List.forall_mem_cons.2 ⟨subd10_2_71, List.forall_mem_cons.2 ⟨subd10_2_72, List.forall_mem_cons.2 ⟨subd10_2_73, List.forall_mem_cons.2 ⟨subd10_2_74, List.forall_mem_cons.2 ⟨subd10_2_75, List.forall_mem_cons.2 ⟨subd10_2_76, List.forall_mem_cons.2 ⟨subd10_2_77, List.forall_mem_cons.2 ⟨subd10_2_78, List.forall_mem_cons.2 ⟨subd10_2_79, List.forall_mem_cons.2 ⟨subd10_2_80, List.forall_mem_cons.2 ⟨subd10_2_81, List.forall_mem_cons.2 ⟨subd10_2_82, List.forall_mem_cons.2 ⟨subd10_2_83, List.forall_mem_cons.2 ⟨subd10_2_84, List.forall_mem_cons.2 ⟨subd10_2_85, List.forall_mem_cons.2 ⟨subd10_2_86, List.forall_mem_cons.2 ⟨subd10_2_87, List.forall_mem_cons.2 ⟨subd10_2_88, List.forall_mem_cons.2 ⟨subd10_2_89, List.forall_mem_cons.2 ⟨subd10_2_90, List.forall_mem_cons.2 ⟨subd10_2_91, List.forall_mem_cons.2 ⟨subd10_2_92, List.forall_mem_cons.2 ⟨subd10_2_93, List.forall_mem_cons.2 ⟨subd10_2_94, List.forall_mem_cons.2 ⟨subd10_2_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C133
