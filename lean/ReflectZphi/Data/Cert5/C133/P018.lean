import ReflectZphi.Data.Cert5.C133.Base

namespace ReflectZphi.Data.Cert5.C133

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd10_3_384 : subd10_3 [2, -1, 0] = true := by decide +kernel
theorem subd10_3_385 : subd10_3 [2, -1, 1] = true := by decide +kernel
theorem subd10_3_386 : subd10_3 [2, -1, 2] = true := by decide +kernel
theorem subd10_3_387 : subd10_3 [2, -1, 3] = true := by decide +kernel
theorem subd10_3_388 : subd10_3 [2, -1, 4] = true := by decide +kernel
theorem subd10_3_389 : subd10_3 [2, -1, 5] = true := by decide +kernel
theorem subd10_3_390 : subd10_3 [2, -1, 6] = true := by decide +kernel
theorem subd10_3_391 : subd10_3 [2, -1, 7] = true := by decide +kernel
theorem subd10_3_392 : subd10_3 [2, -1, 8] = true := by decide +kernel
theorem subd10_3_393 : subd10_3 [2, 0, -9] = true := by decide +kernel
theorem subd10_3_394 : subd10_3 [2, 0, -8] = true := by decide +kernel
theorem subd10_3_395 : subd10_3 [2, 0, -7] = true := by decide +kernel
theorem subd10_3_396 : subd10_3 [2, 0, -6] = true := by decide +kernel
theorem subd10_3_397 : subd10_3 [2, 0, -5] = true := by decide +kernel
theorem subd10_3_398 : subd10_3 [2, 0, -4] = true := by decide +kernel
theorem subd10_3_399 : subd10_3 [2, 0, -3] = true := by decide +kernel
theorem subd10_3_400 : subd10_3 [2, 0, -2] = true := by decide +kernel
theorem subd10_3_401 : subd10_3 [2, 0, -1] = true := by decide +kernel
theorem subd10_3_402 : subd10_3 [2, 0, 0] = true := by decide +kernel
theorem subd10_3_403 : subd10_3 [2, 0, 1] = true := by decide +kernel
theorem subd10_3_404 : subd10_3 [2, 0, 2] = true := by decide +kernel
theorem subd10_3_405 : subd10_3 [2, 0, 3] = true := by decide +kernel
theorem subd10_3_406 : subd10_3 [2, 0, 4] = true := by decide +kernel
theorem subd10_3_407 : subd10_3 [2, 0, 5] = true := by decide +kernel
theorem subd10_3_408 : subd10_3 [2, 0, 6] = true := by decide +kernel
theorem subd10_3_409 : subd10_3 [2, 0, 7] = true := by decide +kernel
theorem subd10_3_410 : subd10_3 [2, 0, 8] = true := by decide +kernel
theorem subd10_3_411 : subd10_3 [2, 0, 9] = true := by decide +kernel
theorem subd10_3_412 : subd10_3 [2, 1, -9] = true := by decide +kernel
theorem subd10_3_413 : subd10_3 [2, 1, -8] = true := by decide +kernel
theorem subd10_3_414 : subd10_3 [2, 1, -7] = true := by decide +kernel
theorem subd10_3_415 : subd10_3 [2, 1, -6] = true := by decide +kernel
theorem sbd10_3_12 : ∀ q ∈ blkd10_3_12, subd10_3 q = true := by
  unfold blkd10_3_12
  exact List.forall_mem_cons.2 ⟨subd10_3_384, List.forall_mem_cons.2 ⟨subd10_3_385, List.forall_mem_cons.2 ⟨subd10_3_386, List.forall_mem_cons.2 ⟨subd10_3_387, List.forall_mem_cons.2 ⟨subd10_3_388, List.forall_mem_cons.2 ⟨subd10_3_389, List.forall_mem_cons.2 ⟨subd10_3_390, List.forall_mem_cons.2 ⟨subd10_3_391, List.forall_mem_cons.2 ⟨subd10_3_392, List.forall_mem_cons.2 ⟨subd10_3_393, List.forall_mem_cons.2 ⟨subd10_3_394, List.forall_mem_cons.2 ⟨subd10_3_395, List.forall_mem_cons.2 ⟨subd10_3_396, List.forall_mem_cons.2 ⟨subd10_3_397, List.forall_mem_cons.2 ⟨subd10_3_398, List.forall_mem_cons.2 ⟨subd10_3_399, List.forall_mem_cons.2 ⟨subd10_3_400, List.forall_mem_cons.2 ⟨subd10_3_401, List.forall_mem_cons.2 ⟨subd10_3_402, List.forall_mem_cons.2 ⟨subd10_3_403, List.forall_mem_cons.2 ⟨subd10_3_404, List.forall_mem_cons.2 ⟨subd10_3_405, List.forall_mem_cons.2 ⟨subd10_3_406, List.forall_mem_cons.2 ⟨subd10_3_407, List.forall_mem_cons.2 ⟨subd10_3_408, List.forall_mem_cons.2 ⟨subd10_3_409, List.forall_mem_cons.2 ⟨subd10_3_410, List.forall_mem_cons.2 ⟨subd10_3_411, List.forall_mem_cons.2 ⟨subd10_3_412, List.forall_mem_cons.2 ⟨subd10_3_413, List.forall_mem_cons.2 ⟨subd10_3_414, List.forall_mem_cons.2 ⟨subd10_3_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_416 : subd10_3 [2, 1, -5] = true := by decide +kernel
theorem subd10_3_417 : subd10_3 [2, 1, -4] = true := by decide +kernel
theorem subd10_3_418 : subd10_3 [2, 1, -3] = true := by decide +kernel
theorem subd10_3_419 : subd10_3 [2, 1, -2] = true := by decide +kernel
theorem subd10_3_420 : subd10_3 [2, 1, -1] = true := by decide +kernel
theorem subd10_3_421 : subd10_3 [2, 1, 0] = true := by decide +kernel
theorem subd10_3_422 : subd10_3 [2, 1, 1] = true := by decide +kernel
theorem subd10_3_423 : subd10_3 [2, 1, 2] = true := by decide +kernel
theorem subd10_3_424 : subd10_3 [2, 1, 3] = true := by decide +kernel
theorem subd10_3_425 : subd10_3 [2, 1, 4] = true := by decide +kernel
theorem subd10_3_426 : subd10_3 [2, 1, 5] = true := by decide +kernel
theorem subd10_3_427 : subd10_3 [2, 1, 6] = true := by decide +kernel
theorem subd10_3_428 : subd10_3 [2, 1, 7] = true := by decide +kernel
theorem subd10_3_429 : subd10_3 [2, 1, 8] = true := by decide +kernel
theorem subd10_3_430 : subd10_3 [2, 2] = true := by decide +kernel
theorem subd10_3_431 : subd10_3 [3, -2] = true := by decide +kernel
theorem subd10_3_432 : subd10_3 [3, -1] = true := by decide +kernel
theorem subd10_3_433 : subd10_3 [3, 0] = true := by decide +kernel
theorem subd10_3_434 : subd10_3 [3, 1] = true := by decide +kernel
theorem sbd10_3_13 : ∀ q ∈ blkd10_3_13, subd10_3 q = true := by
  unfold blkd10_3_13
  exact List.forall_mem_cons.2 ⟨subd10_3_416, List.forall_mem_cons.2 ⟨subd10_3_417, List.forall_mem_cons.2 ⟨subd10_3_418, List.forall_mem_cons.2 ⟨subd10_3_419, List.forall_mem_cons.2 ⟨subd10_3_420, List.forall_mem_cons.2 ⟨subd10_3_421, List.forall_mem_cons.2 ⟨subd10_3_422, List.forall_mem_cons.2 ⟨subd10_3_423, List.forall_mem_cons.2 ⟨subd10_3_424, List.forall_mem_cons.2 ⟨subd10_3_425, List.forall_mem_cons.2 ⟨subd10_3_426, List.forall_mem_cons.2 ⟨subd10_3_427, List.forall_mem_cons.2 ⟨subd10_3_428, List.forall_mem_cons.2 ⟨subd10_3_429, List.forall_mem_cons.2 ⟨subd10_3_430, List.forall_mem_cons.2 ⟨subd10_3_431, List.forall_mem_cons.2 ⟨subd10_3_432, List.forall_mem_cons.2 ⟨subd10_3_433, List.forall_mem_cons.2 ⟨subd10_3_434, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_0 : ldCheck G d11_0.U d11_0.ms ldd11_0 = true := by decide +kernel
theorem pre_okd11_0 : subPre G cell11 d11_0 = true := by decide +kernel
theorem subd11_0_0 : subd11_0 [-2] = true := by decide +kernel
theorem subd11_0_1 : subd11_0 [-1] = true := by decide +kernel
theorem subd11_0_2 : subd11_0 [0] = true := by decide +kernel
theorem subd11_0_3 : subd11_0 [1] = true := by decide +kernel
theorem subd11_0_4 : subd11_0 [2] = true := by decide +kernel
theorem sbd11_0_0 : ∀ q ∈ blkd11_0_0, subd11_0 q = true := by
  unfold blkd11_0_0
  exact List.forall_mem_cons.2 ⟨subd11_0_0, List.forall_mem_cons.2 ⟨subd11_0_1, List.forall_mem_cons.2 ⟨subd11_0_2, List.forall_mem_cons.2 ⟨subd11_0_3, List.forall_mem_cons.2 ⟨subd11_0_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd11_1 : ldCheck G d11_1.U d11_1.ms ldd11_1 = true := by decide +kernel
theorem pre_okd11_1 : subPre G cell11 d11_1 = true := by decide +kernel
theorem subd11_1_0 : subd11_1 [-1] = true := by decide +kernel
theorem subd11_1_1 : subd11_1 [0, -2] = true := by decide +kernel
theorem subd11_1_2 : subd11_1 [0, -1] = true := by decide +kernel
theorem subd11_1_3 : subd11_1 [0, 0] = true := by decide +kernel
theorem subd11_1_4 : subd11_1 [0, 1] = true := by decide +kernel
theorem subd11_1_5 : subd11_1 [1] = true := by decide +kernel
theorem sbd11_1_0 : ∀ q ∈ blkd11_1_0, subd11_1 q = true := by
  unfold blkd11_1_0
  exact List.forall_mem_cons.2 ⟨subd11_1_0, List.forall_mem_cons.2 ⟨subd11_1_1, List.forall_mem_cons.2 ⟨subd11_1_2, List.forall_mem_cons.2 ⟨subd11_1_3, List.forall_mem_cons.2 ⟨subd11_1_4, List.forall_mem_cons.2 ⟨subd11_1_5, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd11_2 : ldCheck G d11_2.U d11_2.ms ldd11_2 = true := by decide +kernel
theorem pre_okd11_2 : subPre G cell11 d11_2 = true := by decide +kernel
theorem subd11_2_0 : subd11_2 [-3, -2] = true := by decide +kernel
theorem subd11_2_1 : subd11_2 [-3, -1] = true := by decide +kernel
theorem subd11_2_2 : subd11_2 [-3, 0] = true := by decide +kernel
theorem subd11_2_3 : subd11_2 [-3, 1] = true := by decide +kernel
theorem subd11_2_4 : subd11_2 [-3, 2] = true := by decide +kernel
theorem subd11_2_5 : subd11_2 [-3, 3] = true := by decide +kernel
theorem subd11_2_6 : subd11_2 [-2, -3] = true := by decide +kernel
theorem subd11_2_7 : subd11_2 [-2, -2] = true := by decide +kernel
theorem subd11_2_8 : subd11_2 [-2, -1] = true := by decide +kernel
theorem subd11_2_9 : subd11_2 [-2, 0] = true := by decide +kernel
theorem subd11_2_10 : subd11_2 [-2, 1] = true := by decide +kernel
theorem subd11_2_11 : subd11_2 [-2, 2] = true := by decide +kernel
theorem subd11_2_12 : subd11_2 [-2, 3] = true := by decide +kernel
theorem subd11_2_13 : subd11_2 [-2, 4] = true := by decide +kernel
theorem subd11_2_14 : subd11_2 [-1, -4] = true := by decide +kernel
theorem subd11_2_15 : subd11_2 [-1, -3] = true := by decide +kernel
theorem subd11_2_16 : subd11_2 [-1, -2] = true := by decide +kernel
theorem subd11_2_17 : subd11_2 [-1, -1] = true := by decide +kernel
theorem subd11_2_18 : subd11_2 [-1, 0] = true := by decide +kernel
theorem subd11_2_19 : subd11_2 [-1, 1] = true := by decide +kernel
theorem subd11_2_20 : subd11_2 [-1, 2] = true := by decide +kernel
theorem subd11_2_21 : subd11_2 [-1, 3] = true := by decide +kernel
theorem subd11_2_22 : subd11_2 [-1, 4] = true := by decide +kernel
theorem subd11_2_23 : subd11_2 [0, -5] = true := by decide +kernel
theorem subd11_2_24 : subd11_2 [0, -4] = true := by decide +kernel
theorem subd11_2_25 : subd11_2 [0, -3] = true := by decide +kernel
theorem subd11_2_26 : subd11_2 [0, -2] = true := by decide +kernel
theorem subd11_2_27 : subd11_2 [0, -1] = true := by decide +kernel
theorem subd11_2_28 : subd11_2 [0, 0] = true := by decide +kernel
theorem subd11_2_29 : subd11_2 [0, 1] = true := by decide +kernel
theorem subd11_2_30 : subd11_2 [0, 2] = true := by decide +kernel
theorem subd11_2_31 : subd11_2 [0, 3] = true := by decide +kernel
theorem sbd11_2_0 : ∀ q ∈ blkd11_2_0, subd11_2 q = true := by
  unfold blkd11_2_0
  exact List.forall_mem_cons.2 ⟨subd11_2_0, List.forall_mem_cons.2 ⟨subd11_2_1, List.forall_mem_cons.2 ⟨subd11_2_2, List.forall_mem_cons.2 ⟨subd11_2_3, List.forall_mem_cons.2 ⟨subd11_2_4, List.forall_mem_cons.2 ⟨subd11_2_5, List.forall_mem_cons.2 ⟨subd11_2_6, List.forall_mem_cons.2 ⟨subd11_2_7, List.forall_mem_cons.2 ⟨subd11_2_8, List.forall_mem_cons.2 ⟨subd11_2_9, List.forall_mem_cons.2 ⟨subd11_2_10, List.forall_mem_cons.2 ⟨subd11_2_11, List.forall_mem_cons.2 ⟨subd11_2_12, List.forall_mem_cons.2 ⟨subd11_2_13, List.forall_mem_cons.2 ⟨subd11_2_14, List.forall_mem_cons.2 ⟨subd11_2_15, List.forall_mem_cons.2 ⟨subd11_2_16, List.forall_mem_cons.2 ⟨subd11_2_17, List.forall_mem_cons.2 ⟨subd11_2_18, List.forall_mem_cons.2 ⟨subd11_2_19, List.forall_mem_cons.2 ⟨subd11_2_20, List.forall_mem_cons.2 ⟨subd11_2_21, List.forall_mem_cons.2 ⟨subd11_2_22, List.forall_mem_cons.2 ⟨subd11_2_23, List.forall_mem_cons.2 ⟨subd11_2_24, List.forall_mem_cons.2 ⟨subd11_2_25, List.forall_mem_cons.2 ⟨subd11_2_26, List.forall_mem_cons.2 ⟨subd11_2_27, List.forall_mem_cons.2 ⟨subd11_2_28, List.forall_mem_cons.2 ⟨subd11_2_29, List.forall_mem_cons.2 ⟨subd11_2_30, List.forall_mem_cons.2 ⟨subd11_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_2_32 : subd11_2 [0, 4] = true := by decide +kernel
theorem subd11_2_33 : subd11_2 [1, -5] = true := by decide +kernel
theorem subd11_2_34 : subd11_2 [1, -4] = true := by decide +kernel
theorem subd11_2_35 : subd11_2 [1, -3] = true := by decide +kernel
theorem subd11_2_36 : subd11_2 [1, -2] = true := by decide +kernel
theorem subd11_2_37 : subd11_2 [1, -1] = true := by decide +kernel
theorem subd11_2_38 : subd11_2 [1, 0] = true := by decide +kernel
theorem subd11_2_39 : subd11_2 [1, 1] = true := by decide +kernel
theorem subd11_2_40 : subd11_2 [1, 2] = true := by decide +kernel
theorem subd11_2_41 : subd11_2 [1, 3] = true := by decide +kernel
theorem subd11_2_42 : subd11_2 [2, -5] = true := by decide +kernel
theorem subd11_2_43 : subd11_2 [2, -4] = true := by decide +kernel
theorem subd11_2_44 : subd11_2 [2, -3] = true := by decide +kernel
theorem subd11_2_45 : subd11_2 [2, -2] = true := by decide +kernel
theorem subd11_2_46 : subd11_2 [2, -1] = true := by decide +kernel
theorem subd11_2_47 : subd11_2 [2, 0] = true := by decide +kernel
theorem subd11_2_48 : subd11_2 [2, 1] = true := by decide +kernel
theorem subd11_2_49 : subd11_2 [2, 2] = true := by decide +kernel
theorem subd11_2_50 : subd11_2 [3, -4] = true := by decide +kernel
theorem subd11_2_51 : subd11_2 [3, -3] = true := by decide +kernel
theorem subd11_2_52 : subd11_2 [3, -2] = true := by decide +kernel
theorem subd11_2_53 : subd11_2 [3, -1] = true := by decide +kernel
theorem subd11_2_54 : subd11_2 [3, 0] = true := by decide +kernel
theorem subd11_2_55 : subd11_2 [3, 1] = true := by decide +kernel
theorem sbd11_2_1 : ∀ q ∈ blkd11_2_1, subd11_2 q = true := by
  unfold blkd11_2_1
  exact List.forall_mem_cons.2 ⟨subd11_2_32, List.forall_mem_cons.2 ⟨subd11_2_33, List.forall_mem_cons.2 ⟨subd11_2_34, List.forall_mem_cons.2 ⟨subd11_2_35, List.forall_mem_cons.2 ⟨subd11_2_36, List.forall_mem_cons.2 ⟨subd11_2_37, List.forall_mem_cons.2 ⟨subd11_2_38, List.forall_mem_cons.2 ⟨subd11_2_39, List.forall_mem_cons.2 ⟨subd11_2_40, List.forall_mem_cons.2 ⟨subd11_2_41, List.forall_mem_cons.2 ⟨subd11_2_42, List.forall_mem_cons.2 ⟨subd11_2_43, List.forall_mem_cons.2 ⟨subd11_2_44, List.forall_mem_cons.2 ⟨subd11_2_45, List.forall_mem_cons.2 ⟨subd11_2_46, List.forall_mem_cons.2 ⟨subd11_2_47, List.forall_mem_cons.2 ⟨subd11_2_48, List.forall_mem_cons.2 ⟨subd11_2_49, List.forall_mem_cons.2 ⟨subd11_2_50, List.forall_mem_cons.2 ⟨subd11_2_51, List.forall_mem_cons.2 ⟨subd11_2_52, List.forall_mem_cons.2 ⟨subd11_2_53, List.forall_mem_cons.2 ⟨subd11_2_54, List.forall_mem_cons.2 ⟨subd11_2_55, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_3 : ldCheck G d11_3.U d11_3.ms ldd11_3 = true := by decide +kernel
theorem pre_okd11_3 : subPre G cell11 d11_3 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C133
