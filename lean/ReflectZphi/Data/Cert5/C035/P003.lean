import ReflectZphi.Data.Cert5.C035.Base

namespace ReflectZphi.Data.Cert5.C035
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub2_416 : sub2 [3, -3] = true := by decide +kernel
theorem sub2_417 : sub2 [3, -2] = true := by decide +kernel
theorem sub2_418 : sub2 [3, -1] = true := by decide +kernel
theorem sub2_419 : sub2 [3, 0] = true := by decide +kernel
theorem sub2_420 : sub2 [3, 1] = true := by decide +kernel
theorem sub2_421 : sub2 [3, 2] = true := by decide +kernel
theorem sub2_422 : sub2 [3, 3] = true := by decide +kernel
theorem sub2_423 : sub2 [3, 4] = true := by decide +kernel
theorem sub2_424 : sub2 [3, 5] = true := by decide +kernel
theorem sub2_425 : sub2 [3, 6] = true := by decide +kernel
theorem sub2_426 : sub2 [4, -5] = true := by decide +kernel
theorem sub2_427 : sub2 [4, -4] = true := by decide +kernel
theorem sub2_428 : sub2 [4, -3] = true := by decide +kernel
theorem sub2_429 : sub2 [4, -2] = true := by decide +kernel
theorem sub2_430 : sub2 [4, -1] = true := by decide +kernel
theorem sub2_431 : sub2 [4, 0] = true := by decide +kernel
theorem sub2_432 : sub2 [4, 1] = true := by decide +kernel
theorem sub2_433 : sub2 [4, 2] = true := by decide +kernel
theorem sub2_434 : sub2 [4, 3] = true := by decide +kernel
theorem sub2_435 : sub2 [4, 4] = true := by decide +kernel
theorem sub2_436 : sub2 [4, 5] = true := by decide +kernel
theorem sub2_437 : sub2 [4, 6] = true := by decide +kernel
theorem sub2_438 : sub2 [5, -3] = true := by decide +kernel
theorem sub2_439 : sub2 [5, -2] = true := by decide +kernel
theorem sub2_440 : sub2 [5, -1] = true := by decide +kernel
theorem sub2_441 : sub2 [5, 0] = true := by decide +kernel
theorem sub2_442 : sub2 [5, 1] = true := by decide +kernel
theorem sub2_443 : sub2 [5, 2] = true := by decide +kernel
theorem sub2_444 : sub2 [5, 3] = true := by decide +kernel
theorem sub2_445 : sub2 [5, 4] = true := by decide +kernel
theorem sub2_446 : sub2 [5, 5] = true := by decide +kernel
theorem sub2_447 : sub2 [5, 6] = true := by decide +kernel
theorem sb2_13 : ∀ q ∈ blk2_13, sub2 q = true := by
  unfold blk2_13
  exact List.forall_mem_cons.2 ⟨sub2_416, List.forall_mem_cons.2 ⟨sub2_417, List.forall_mem_cons.2 ⟨sub2_418, List.forall_mem_cons.2 ⟨sub2_419, List.forall_mem_cons.2 ⟨sub2_420, List.forall_mem_cons.2 ⟨sub2_421, List.forall_mem_cons.2 ⟨sub2_422, List.forall_mem_cons.2 ⟨sub2_423, List.forall_mem_cons.2 ⟨sub2_424, List.forall_mem_cons.2 ⟨sub2_425, List.forall_mem_cons.2 ⟨sub2_426, List.forall_mem_cons.2 ⟨sub2_427, List.forall_mem_cons.2 ⟨sub2_428, List.forall_mem_cons.2 ⟨sub2_429, List.forall_mem_cons.2 ⟨sub2_430, List.forall_mem_cons.2 ⟨sub2_431, List.forall_mem_cons.2 ⟨sub2_432, List.forall_mem_cons.2 ⟨sub2_433, List.forall_mem_cons.2 ⟨sub2_434, List.forall_mem_cons.2 ⟨sub2_435, List.forall_mem_cons.2 ⟨sub2_436, List.forall_mem_cons.2 ⟨sub2_437, List.forall_mem_cons.2 ⟨sub2_438, List.forall_mem_cons.2 ⟨sub2_439, List.forall_mem_cons.2 ⟨sub2_440, List.forall_mem_cons.2 ⟨sub2_441, List.forall_mem_cons.2 ⟨sub2_442, List.forall_mem_cons.2 ⟨sub2_443, List.forall_mem_cons.2 ⟨sub2_444, List.forall_mem_cons.2 ⟨sub2_445, List.forall_mem_cons.2 ⟨sub2_446, List.forall_mem_cons.2 ⟨sub2_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_448 : sub2 [6, -2] = true := by decide +kernel
theorem sub2_449 : sub2 [6, -1] = true := by decide +kernel
theorem sub2_450 : sub2 [6, 0] = true := by decide +kernel
theorem sub2_451 : sub2 [6, 1] = true := by decide +kernel
theorem sub2_452 : sub2 [6, 2] = true := by decide +kernel
theorem sub2_453 : sub2 [6, 3] = true := by decide +kernel
theorem sub2_454 : sub2 [6, 4] = true := by decide +kernel
theorem sb2_14 : ∀ q ∈ blk2_14, sub2 q = true := by
  unfold blk2_14
  exact List.forall_mem_cons.2 ⟨sub2_448, List.forall_mem_cons.2 ⟨sub2_449, List.forall_mem_cons.2 ⟨sub2_450, List.forall_mem_cons.2 ⟨sub2_451, List.forall_mem_cons.2 ⟨sub2_452, List.forall_mem_cons.2 ⟨sub2_453, List.forall_mem_cons.2 ⟨sub2_454, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem sub3_0 : sub3 [-6] = true := by decide +kernel
theorem sub3_1 : sub3 [-5, -2] = true := by decide +kernel
theorem sub3_2 : sub3 [-5, -1] = true := by decide +kernel
theorem sub3_3 : sub3 [-5, 0] = true := by decide +kernel
theorem sub3_4 : sub3 [-5, 1] = true := by decide +kernel
theorem sub3_5 : sub3 [-5, 2] = true := by decide +kernel
theorem sub3_6 : sub3 [-5, 3] = true := by decide +kernel
theorem sub3_7 : sub3 [-4, -4] = true := by decide +kernel
theorem sub3_8 : sub3 [-4, -3] = true := by decide +kernel
theorem sub3_9 : sub3 [-4, -2] = true := by decide +kernel
theorem sub3_10 : sub3 [-4, -1] = true := by decide +kernel
theorem sub3_11 : sub3 [-4, 0] = true := by decide +kernel
theorem sub3_12 : sub3 [-4, 1] = true := by decide +kernel
theorem sub3_13 : sub3 [-4, 2] = true := by decide +kernel
theorem sub3_14 : sub3 [-4, 3] = true := by decide +kernel
theorem sub3_15 : sub3 [-4, 4] = true := by decide +kernel
theorem sub3_16 : sub3 [-3, -4] = true := by decide +kernel
theorem sub3_17 : sub3 [-3, -3] = true := by decide +kernel
theorem sub3_18 : sub3 [-3, -2] = true := by decide +kernel
theorem sub3_19 : sub3 [-3, -1] = true := by decide +kernel
theorem sub3_20 : sub3 [-3, 0] = true := by decide +kernel
theorem sub3_21 : sub3 [-3, 1] = true := by decide +kernel
theorem sub3_22 : sub3 [-3, 2] = true := by decide +kernel
theorem sub3_23 : sub3 [-3, 3] = true := by decide +kernel
theorem sub3_24 : sub3 [-3, 4] = true := by decide +kernel
theorem sub3_25 : sub3 [-3, 5] = true := by decide +kernel
theorem sub3_26 : sub3 [-2, -5] = true := by decide +kernel
theorem sub3_27 : sub3 [-2, -4] = true := by decide +kernel
theorem sub3_28 : sub3 [-2, -3] = true := by decide +kernel
theorem sub3_29 : sub3 [-2, -2] = true := by decide +kernel
theorem sub3_30 : sub3 [-2, -1] = true := by decide +kernel
theorem sub3_31 : sub3 [-2, 0] = true := by decide +kernel
theorem sb3_0 : ∀ q ∈ blk3_0, sub3 q = true := by
  unfold blk3_0
  exact List.forall_mem_cons.2 ⟨sub3_0, List.forall_mem_cons.2 ⟨sub3_1, List.forall_mem_cons.2 ⟨sub3_2, List.forall_mem_cons.2 ⟨sub3_3, List.forall_mem_cons.2 ⟨sub3_4, List.forall_mem_cons.2 ⟨sub3_5, List.forall_mem_cons.2 ⟨sub3_6, List.forall_mem_cons.2 ⟨sub3_7, List.forall_mem_cons.2 ⟨sub3_8, List.forall_mem_cons.2 ⟨sub3_9, List.forall_mem_cons.2 ⟨sub3_10, List.forall_mem_cons.2 ⟨sub3_11, List.forall_mem_cons.2 ⟨sub3_12, List.forall_mem_cons.2 ⟨sub3_13, List.forall_mem_cons.2 ⟨sub3_14, List.forall_mem_cons.2 ⟨sub3_15, List.forall_mem_cons.2 ⟨sub3_16, List.forall_mem_cons.2 ⟨sub3_17, List.forall_mem_cons.2 ⟨sub3_18, List.forall_mem_cons.2 ⟨sub3_19, List.forall_mem_cons.2 ⟨sub3_20, List.forall_mem_cons.2 ⟨sub3_21, List.forall_mem_cons.2 ⟨sub3_22, List.forall_mem_cons.2 ⟨sub3_23, List.forall_mem_cons.2 ⟨sub3_24, List.forall_mem_cons.2 ⟨sub3_25, List.forall_mem_cons.2 ⟨sub3_26, List.forall_mem_cons.2 ⟨sub3_27, List.forall_mem_cons.2 ⟨sub3_28, List.forall_mem_cons.2 ⟨sub3_29, List.forall_mem_cons.2 ⟨sub3_30, List.forall_mem_cons.2 ⟨sub3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_32 : sub3 [-2, 1] = true := by decide +kernel
theorem sub3_33 : sub3 [-2, 2] = true := by decide +kernel
theorem sub3_34 : sub3 [-2, 3] = true := by decide +kernel
theorem sub3_35 : sub3 [-2, 4] = true := by decide +kernel
theorem sub3_36 : sub3 [-2, 5] = true := by decide +kernel
theorem sub3_37 : sub3 [-1, -5] = true := by decide +kernel
theorem sub3_38 : sub3 [-1, -4] = true := by decide +kernel
theorem sub3_39 : sub3 [-1, -3] = true := by decide +kernel
theorem sub3_40 : sub3 [-1, -2] = true := by decide +kernel
theorem sub3_41 : sub3 [-1, -1] = true := by decide +kernel
theorem sub3_42 : sub3 [-1, 0] = true := by decide +kernel
theorem sub3_43 : sub3 [-1, 1] = true := by decide +kernel
theorem sub3_44 : sub3 [-1, 2] = true := by decide +kernel
theorem sub3_45 : sub3 [-1, 3] = true := by decide +kernel
theorem sub3_46 : sub3 [-1, 4] = true := by decide +kernel
theorem sub3_47 : sub3 [-1, 5] = true := by decide +kernel
theorem sub3_48 : sub3 [0, -6] = true := by decide +kernel
theorem sub3_49 : sub3 [0, -5] = true := by decide +kernel
theorem sub3_50 : sub3 [0, -4] = true := by decide +kernel
theorem sub3_51 : sub3 [0, -3] = true := by decide +kernel
theorem sub3_52 : sub3 [0, -2] = true := by decide +kernel
theorem sub3_53 : sub3 [0, -1] = true := by decide +kernel
theorem sub3_54 : sub3 [0, 0] = true := by decide +kernel
theorem sub3_55 : sub3 [0, 1] = true := by decide +kernel
theorem sub3_56 : sub3 [0, 2] = true := by decide +kernel
theorem sub3_57 : sub3 [0, 3] = true := by decide +kernel
theorem sub3_58 : sub3 [0, 4] = true := by decide +kernel
theorem sub3_59 : sub3 [0, 5] = true := by decide +kernel
theorem sub3_60 : sub3 [1, -6] = true := by decide +kernel
theorem sub3_61 : sub3 [1, -5] = true := by decide +kernel
theorem sub3_62 : sub3 [1, -4] = true := by decide +kernel
theorem sub3_63 : sub3 [1, -3] = true := by decide +kernel
theorem sb3_1 : ∀ q ∈ blk3_1, sub3 q = true := by
  unfold blk3_1
  exact List.forall_mem_cons.2 ⟨sub3_32, List.forall_mem_cons.2 ⟨sub3_33, List.forall_mem_cons.2 ⟨sub3_34, List.forall_mem_cons.2 ⟨sub3_35, List.forall_mem_cons.2 ⟨sub3_36, List.forall_mem_cons.2 ⟨sub3_37, List.forall_mem_cons.2 ⟨sub3_38, List.forall_mem_cons.2 ⟨sub3_39, List.forall_mem_cons.2 ⟨sub3_40, List.forall_mem_cons.2 ⟨sub3_41, List.forall_mem_cons.2 ⟨sub3_42, List.forall_mem_cons.2 ⟨sub3_43, List.forall_mem_cons.2 ⟨sub3_44, List.forall_mem_cons.2 ⟨sub3_45, List.forall_mem_cons.2 ⟨sub3_46, List.forall_mem_cons.2 ⟨sub3_47, List.forall_mem_cons.2 ⟨sub3_48, List.forall_mem_cons.2 ⟨sub3_49, List.forall_mem_cons.2 ⟨sub3_50, List.forall_mem_cons.2 ⟨sub3_51, List.forall_mem_cons.2 ⟨sub3_52, List.forall_mem_cons.2 ⟨sub3_53, List.forall_mem_cons.2 ⟨sub3_54, List.forall_mem_cons.2 ⟨sub3_55, List.forall_mem_cons.2 ⟨sub3_56, List.forall_mem_cons.2 ⟨sub3_57, List.forall_mem_cons.2 ⟨sub3_58, List.forall_mem_cons.2 ⟨sub3_59, List.forall_mem_cons.2 ⟨sub3_60, List.forall_mem_cons.2 ⟨sub3_61, List.forall_mem_cons.2 ⟨sub3_62, List.forall_mem_cons.2 ⟨sub3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C035
