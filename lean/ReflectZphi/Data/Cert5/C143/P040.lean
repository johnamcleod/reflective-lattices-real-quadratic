import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd16_1_384 : subd16_1 [3, -3] = true := by decide +kernel
theorem subd16_1_385 : subd16_1 [3, -2] = true := by decide +kernel
theorem subd16_1_386 : subd16_1 [3, -1] = true := by decide +kernel
theorem subd16_1_387 : subd16_1 [3, 0] = true := by decide +kernel
theorem subd16_1_388 : subd16_1 [3, 1] = true := by decide +kernel
theorem subd16_1_389 : subd16_1 [3, 2] = true := by decide +kernel
theorem subd16_1_390 : subd16_1 [3, 3] = true := by decide +kernel
theorem subd16_1_391 : subd16_1 [3, 4] = true := by decide +kernel
theorem subd16_1_392 : subd16_1 [4, -7] = true := by decide +kernel
theorem subd16_1_393 : subd16_1 [4, -6] = true := by decide +kernel
theorem subd16_1_394 : subd16_1 [4, -5] = true := by decide +kernel
theorem subd16_1_395 : subd16_1 [4, -4] = true := by decide +kernel
theorem subd16_1_396 : subd16_1 [4, -3] = true := by decide +kernel
theorem subd16_1_397 : subd16_1 [4, -2] = true := by decide +kernel
theorem subd16_1_398 : subd16_1 [4, -1] = true := by decide +kernel
theorem subd16_1_399 : subd16_1 [4, 0] = true := by decide +kernel
theorem subd16_1_400 : subd16_1 [4, 1] = true := by decide +kernel
theorem subd16_1_401 : subd16_1 [4, 2] = true := by decide +kernel
theorem subd16_1_402 : subd16_1 [4, 3] = true := by decide +kernel
theorem subd16_1_403 : subd16_1 [5, -7] = true := by decide +kernel
theorem subd16_1_404 : subd16_1 [5, -6] = true := by decide +kernel
theorem subd16_1_405 : subd16_1 [5, -5] = true := by decide +kernel
theorem subd16_1_406 : subd16_1 [5, -4] = true := by decide +kernel
theorem subd16_1_407 : subd16_1 [5, -3] = true := by decide +kernel
theorem subd16_1_408 : subd16_1 [5, -2] = true := by decide +kernel
theorem subd16_1_409 : subd16_1 [5, -1] = true := by decide +kernel
theorem subd16_1_410 : subd16_1 [5, 0] = true := by decide +kernel
theorem subd16_1_411 : subd16_1 [5, 1] = true := by decide +kernel
theorem subd16_1_412 : subd16_1 [5, 2] = true := by decide +kernel
theorem subd16_1_413 : subd16_1 [5, 3] = true := by decide +kernel
theorem subd16_1_414 : subd16_1 [6, -6] = true := by decide +kernel
theorem subd16_1_415 : subd16_1 [6, -5] = true := by decide +kernel
theorem sbd16_1_12 : ∀ q ∈ blkd16_1_12, subd16_1 q = true := by
  unfold blkd16_1_12
  exact List.forall_mem_cons.2 ⟨subd16_1_384, List.forall_mem_cons.2 ⟨subd16_1_385, List.forall_mem_cons.2 ⟨subd16_1_386, List.forall_mem_cons.2 ⟨subd16_1_387, List.forall_mem_cons.2 ⟨subd16_1_388, List.forall_mem_cons.2 ⟨subd16_1_389, List.forall_mem_cons.2 ⟨subd16_1_390, List.forall_mem_cons.2 ⟨subd16_1_391, List.forall_mem_cons.2 ⟨subd16_1_392, List.forall_mem_cons.2 ⟨subd16_1_393, List.forall_mem_cons.2 ⟨subd16_1_394, List.forall_mem_cons.2 ⟨subd16_1_395, List.forall_mem_cons.2 ⟨subd16_1_396, List.forall_mem_cons.2 ⟨subd16_1_397, List.forall_mem_cons.2 ⟨subd16_1_398, List.forall_mem_cons.2 ⟨subd16_1_399, List.forall_mem_cons.2 ⟨subd16_1_400, List.forall_mem_cons.2 ⟨subd16_1_401, List.forall_mem_cons.2 ⟨subd16_1_402, List.forall_mem_cons.2 ⟨subd16_1_403, List.forall_mem_cons.2 ⟨subd16_1_404, List.forall_mem_cons.2 ⟨subd16_1_405, List.forall_mem_cons.2 ⟨subd16_1_406, List.forall_mem_cons.2 ⟨subd16_1_407, List.forall_mem_cons.2 ⟨subd16_1_408, List.forall_mem_cons.2 ⟨subd16_1_409, List.forall_mem_cons.2 ⟨subd16_1_410, List.forall_mem_cons.2 ⟨subd16_1_411, List.forall_mem_cons.2 ⟨subd16_1_412, List.forall_mem_cons.2 ⟨subd16_1_413, List.forall_mem_cons.2 ⟨subd16_1_414, List.forall_mem_cons.2 ⟨subd16_1_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_1_416 : subd16_1 [6, -4] = true := by decide +kernel
theorem subd16_1_417 : subd16_1 [6, -3] = true := by decide +kernel
theorem subd16_1_418 : subd16_1 [6, -2] = true := by decide +kernel
theorem subd16_1_419 : subd16_1 [6, -1] = true := by decide +kernel
theorem subd16_1_420 : subd16_1 [6, 0] = true := by decide +kernel
theorem subd16_1_421 : subd16_1 [6, 1] = true := by decide +kernel
theorem subd16_1_422 : subd16_1 [7] = true := by decide +kernel
theorem sbd16_1_13 : ∀ q ∈ blkd16_1_13, subd16_1 q = true := by
  unfold blkd16_1_13
  exact List.forall_mem_cons.2 ⟨subd16_1_416, List.forall_mem_cons.2 ⟨subd16_1_417, List.forall_mem_cons.2 ⟨subd16_1_418, List.forall_mem_cons.2 ⟨subd16_1_419, List.forall_mem_cons.2 ⟨subd16_1_420, List.forall_mem_cons.2 ⟨subd16_1_421, List.forall_mem_cons.2 ⟨subd16_1_422, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd16_2 : ldCheck G d16_2.U d16_2.ms ldd16_2 = true := by decide +kernel
theorem pre_okd16_2 : subPre G cell16 d16_2 = true := by decide +kernel
theorem subd16_2_0 : subd16_2 [-6] = true := by decide +kernel
theorem subd16_2_1 : subd16_2 [-5, -5] = true := by decide +kernel
theorem subd16_2_2 : subd16_2 [-5, -4] = true := by decide +kernel
theorem subd16_2_3 : subd16_2 [-5, -3] = true := by decide +kernel
theorem subd16_2_4 : subd16_2 [-5, -2] = true := by decide +kernel
theorem subd16_2_5 : subd16_2 [-5, -1] = true := by decide +kernel
theorem subd16_2_6 : subd16_2 [-5, 0] = true := by decide +kernel
theorem subd16_2_7 : subd16_2 [-5, 1] = true := by decide +kernel
theorem subd16_2_8 : subd16_2 [-5, 2] = true := by decide +kernel
theorem subd16_2_9 : subd16_2 [-5, 3] = true := by decide +kernel
theorem subd16_2_10 : subd16_2 [-5, 4] = true := by decide +kernel
theorem subd16_2_11 : subd16_2 [-4, -6] = true := by decide +kernel
theorem subd16_2_12 : subd16_2 [-4, -5] = true := by decide +kernel
theorem subd16_2_13 : subd16_2 [-4, -4] = true := by decide +kernel
theorem subd16_2_14 : subd16_2 [-4, -3] = true := by decide +kernel
theorem subd16_2_15 : subd16_2 [-4, -2] = true := by decide +kernel
theorem subd16_2_16 : subd16_2 [-4, -1] = true := by decide +kernel
theorem subd16_2_17 : subd16_2 [-4, 0] = true := by decide +kernel
theorem subd16_2_18 : subd16_2 [-4, 1] = true := by decide +kernel
theorem subd16_2_19 : subd16_2 [-4, 2] = true := by decide +kernel
theorem subd16_2_20 : subd16_2 [-4, 3] = true := by decide +kernel
theorem subd16_2_21 : subd16_2 [-4, 4] = true := by decide +kernel
theorem subd16_2_22 : subd16_2 [-4, 5] = true := by decide +kernel
theorem subd16_2_23 : subd16_2 [-3, -6] = true := by decide +kernel
theorem subd16_2_24 : subd16_2 [-3, -5] = true := by decide +kernel
theorem subd16_2_25 : subd16_2 [-3, -4] = true := by decide +kernel
theorem subd16_2_26 : subd16_2 [-3, -3] = true := by decide +kernel
theorem subd16_2_27 : subd16_2 [-3, -2] = true := by decide +kernel
theorem subd16_2_28 : subd16_2 [-3, -1] = true := by decide +kernel
theorem subd16_2_29 : subd16_2 [-3, 0] = true := by decide +kernel
theorem subd16_2_30 : subd16_2 [-3, 1] = true := by decide +kernel
theorem subd16_2_31 : subd16_2 [-3, 2] = true := by decide +kernel
theorem sbd16_2_0 : ∀ q ∈ blkd16_2_0, subd16_2 q = true := by
  unfold blkd16_2_0
  exact List.forall_mem_cons.2 ⟨subd16_2_0, List.forall_mem_cons.2 ⟨subd16_2_1, List.forall_mem_cons.2 ⟨subd16_2_2, List.forall_mem_cons.2 ⟨subd16_2_3, List.forall_mem_cons.2 ⟨subd16_2_4, List.forall_mem_cons.2 ⟨subd16_2_5, List.forall_mem_cons.2 ⟨subd16_2_6, List.forall_mem_cons.2 ⟨subd16_2_7, List.forall_mem_cons.2 ⟨subd16_2_8, List.forall_mem_cons.2 ⟨subd16_2_9, List.forall_mem_cons.2 ⟨subd16_2_10, List.forall_mem_cons.2 ⟨subd16_2_11, List.forall_mem_cons.2 ⟨subd16_2_12, List.forall_mem_cons.2 ⟨subd16_2_13, List.forall_mem_cons.2 ⟨subd16_2_14, List.forall_mem_cons.2 ⟨subd16_2_15, List.forall_mem_cons.2 ⟨subd16_2_16, List.forall_mem_cons.2 ⟨subd16_2_17, List.forall_mem_cons.2 ⟨subd16_2_18, List.forall_mem_cons.2 ⟨subd16_2_19, List.forall_mem_cons.2 ⟨subd16_2_20, List.forall_mem_cons.2 ⟨subd16_2_21, List.forall_mem_cons.2 ⟨subd16_2_22, List.forall_mem_cons.2 ⟨subd16_2_23, List.forall_mem_cons.2 ⟨subd16_2_24, List.forall_mem_cons.2 ⟨subd16_2_25, List.forall_mem_cons.2 ⟨subd16_2_26, List.forall_mem_cons.2 ⟨subd16_2_27, List.forall_mem_cons.2 ⟨subd16_2_28, List.forall_mem_cons.2 ⟨subd16_2_29, List.forall_mem_cons.2 ⟨subd16_2_30, List.forall_mem_cons.2 ⟨subd16_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
