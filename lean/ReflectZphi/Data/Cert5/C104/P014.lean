import ReflectZphi.Data.Cert5.C104.Base

namespace ReflectZphi.Data.Cert5.C104
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub9_416 : sub9 [4, 0] = true := by decide +kernel
theorem sub9_417 : sub9 [4, 1] = true := by decide +kernel
theorem sub9_418 : sub9 [4, 2] = true := by decide +kernel
theorem sub9_419 : sub9 [4, 3] = true := by decide +kernel
theorem sub9_420 : sub9 [4, 4] = true := by decide +kernel
theorem sub9_421 : sub9 [4, 5] = true := by decide +kernel
theorem sub9_422 : sub9 [4, 6] = true := by decide +kernel
theorem sub9_423 : sub9 [5, -3] = true := by decide +kernel
theorem sub9_424 : sub9 [5, -2] = true := by decide +kernel
theorem sub9_425 : sub9 [5, -1] = true := by decide +kernel
theorem sub9_426 : sub9 [5, 0] = true := by decide +kernel
theorem sub9_427 : sub9 [5, 1] = true := by decide +kernel
theorem sub9_428 : sub9 [5, 2] = true := by decide +kernel
theorem sub9_429 : sub9 [5, 3] = true := by decide +kernel
theorem sub9_430 : sub9 [5, 4] = true := by decide +kernel
theorem sub9_431 : sub9 [5, 5] = true := by decide +kernel
theorem sub9_432 : sub9 [6] = true := by decide +kernel
theorem sb9_13 : ∀ q ∈ blk9_13, sub9 q = true := by
  unfold blk9_13
  exact List.forall_mem_cons.2 ⟨sub9_416, List.forall_mem_cons.2 ⟨sub9_417, List.forall_mem_cons.2 ⟨sub9_418, List.forall_mem_cons.2 ⟨sub9_419, List.forall_mem_cons.2 ⟨sub9_420, List.forall_mem_cons.2 ⟨sub9_421, List.forall_mem_cons.2 ⟨sub9_422, List.forall_mem_cons.2 ⟨sub9_423, List.forall_mem_cons.2 ⟨sub9_424, List.forall_mem_cons.2 ⟨sub9_425, List.forall_mem_cons.2 ⟨sub9_426, List.forall_mem_cons.2 ⟨sub9_427, List.forall_mem_cons.2 ⟨sub9_428, List.forall_mem_cons.2 ⟨sub9_429, List.forall_mem_cons.2 ⟨sub9_430, List.forall_mem_cons.2 ⟨sub9_431, List.forall_mem_cons.2 ⟨sub9_432, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_0 : sub10 [-4] = true := by decide +kernel
theorem sub10_1 : sub10 [-3, -5] = true := by decide +kernel
theorem sub10_2 : sub10 [-3, -4] = true := by decide +kernel
theorem sub10_3 : sub10 [-3, -3] = true := by decide +kernel
theorem sub10_4 : sub10 [-3, -2] = true := by decide +kernel
theorem sub10_5 : sub10 [-3, -1] = true := by decide +kernel
theorem sub10_6 : sub10 [-3, 0] = true := by decide +kernel
theorem sub10_7 : sub10 [-3, 1] = true := by decide +kernel
theorem sub10_8 : sub10 [-3, 2] = true := by decide +kernel
theorem sub10_9 : sub10 [-2, -5] = true := by decide +kernel
theorem sub10_10 : sub10 [-2, -4] = true := by decide +kernel
theorem sub10_11 : sub10 [-2, -3] = true := by decide +kernel
theorem sub10_12 : sub10 [-2, -2] = true := by decide +kernel
theorem sub10_13 : sub10 [-2, -1] = true := by decide +kernel
theorem sub10_14 : sub10 [-2, 0] = true := by decide +kernel
theorem sub10_15 : sub10 [-2, 1] = true := by decide +kernel
theorem sub10_16 : sub10 [-2, 2] = true := by decide +kernel
theorem sub10_17 : sub10 [-2, 3] = true := by decide +kernel
theorem sub10_18 : sub10 [-1, -5] = true := by decide +kernel
theorem sub10_19 : sub10 [-1, -4] = true := by decide +kernel
theorem sub10_20 : sub10 [-1, -3] = true := by decide +kernel
theorem sub10_21 : sub10 [-1, -2] = true := by decide +kernel
theorem sub10_22 : sub10 [-1, -1] = true := by decide +kernel
theorem sub10_23 : sub10 [-1, 0] = true := by decide +kernel
theorem sub10_24 : sub10 [-1, 1] = true := by decide +kernel
theorem sub10_25 : sub10 [-1, 2] = true := by decide +kernel
theorem sub10_26 : sub10 [-1, 3] = true := by decide +kernel
theorem sub10_27 : sub10 [0, -5] = true := by decide +kernel
theorem sub10_28 : sub10 [0, -4] = true := by decide +kernel
theorem sub10_29 : sub10 [0, -3] = true := by decide +kernel
theorem sub10_30 : sub10 [0, -2] = true := by decide +kernel
theorem sub10_31 : sub10 [0, -1] = true := by decide +kernel
theorem sb10_0 : ∀ q ∈ blk10_0, sub10 q = true := by
  unfold blk10_0
  exact List.forall_mem_cons.2 ⟨sub10_0, List.forall_mem_cons.2 ⟨sub10_1, List.forall_mem_cons.2 ⟨sub10_2, List.forall_mem_cons.2 ⟨sub10_3, List.forall_mem_cons.2 ⟨sub10_4, List.forall_mem_cons.2 ⟨sub10_5, List.forall_mem_cons.2 ⟨sub10_6, List.forall_mem_cons.2 ⟨sub10_7, List.forall_mem_cons.2 ⟨sub10_8, List.forall_mem_cons.2 ⟨sub10_9, List.forall_mem_cons.2 ⟨sub10_10, List.forall_mem_cons.2 ⟨sub10_11, List.forall_mem_cons.2 ⟨sub10_12, List.forall_mem_cons.2 ⟨sub10_13, List.forall_mem_cons.2 ⟨sub10_14, List.forall_mem_cons.2 ⟨sub10_15, List.forall_mem_cons.2 ⟨sub10_16, List.forall_mem_cons.2 ⟨sub10_17, List.forall_mem_cons.2 ⟨sub10_18, List.forall_mem_cons.2 ⟨sub10_19, List.forall_mem_cons.2 ⟨sub10_20, List.forall_mem_cons.2 ⟨sub10_21, List.forall_mem_cons.2 ⟨sub10_22, List.forall_mem_cons.2 ⟨sub10_23, List.forall_mem_cons.2 ⟨sub10_24, List.forall_mem_cons.2 ⟨sub10_25, List.forall_mem_cons.2 ⟨sub10_26, List.forall_mem_cons.2 ⟨sub10_27, List.forall_mem_cons.2 ⟨sub10_28, List.forall_mem_cons.2 ⟨sub10_29, List.forall_mem_cons.2 ⟨sub10_30, List.forall_mem_cons.2 ⟨sub10_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_32 : sub10 [0, 0] = true := by decide +kernel
theorem sub10_33 : sub10 [0, 1] = true := by decide +kernel
theorem sub10_34 : sub10 [0, 2] = true := by decide +kernel
theorem sub10_35 : sub10 [0, 3] = true := by decide +kernel
theorem sub10_36 : sub10 [0, 4] = true := by decide +kernel
theorem sub10_37 : sub10 [1, -4] = true := by decide +kernel
theorem sub10_38 : sub10 [1, -3] = true := by decide +kernel
theorem sub10_39 : sub10 [1, -2] = true := by decide +kernel
theorem sub10_40 : sub10 [1, -1] = true := by decide +kernel
theorem sub10_41 : sub10 [1, 0] = true := by decide +kernel
theorem sub10_42 : sub10 [1, 1] = true := by decide +kernel
theorem sub10_43 : sub10 [1, 2] = true := by decide +kernel
theorem sub10_44 : sub10 [1, 3] = true := by decide +kernel
theorem sub10_45 : sub10 [1, 4] = true := by decide +kernel
theorem sub10_46 : sub10 [2, -4] = true := by decide +kernel
theorem sub10_47 : sub10 [2, -3] = true := by decide +kernel
theorem sub10_48 : sub10 [2, -2] = true := by decide +kernel
theorem sub10_49 : sub10 [2, -1] = true := by decide +kernel
theorem sub10_50 : sub10 [2, 0] = true := by decide +kernel
theorem sub10_51 : sub10 [2, 1] = true := by decide +kernel
theorem sub10_52 : sub10 [2, 2] = true := by decide +kernel
theorem sub10_53 : sub10 [2, 3] = true := by decide +kernel
theorem sub10_54 : sub10 [2, 4] = true := by decide +kernel
theorem sub10_55 : sub10 [3, -3] = true := by decide +kernel
theorem sub10_56 : sub10 [3, -2] = true := by decide +kernel
theorem sub10_57 : sub10 [3, -1] = true := by decide +kernel
theorem sub10_58 : sub10 [3, 0] = true := by decide +kernel
theorem sub10_59 : sub10 [3, 1] = true := by decide +kernel
theorem sub10_60 : sub10 [3, 2] = true := by decide +kernel
theorem sub10_61 : sub10 [3, 3] = true := by decide +kernel
theorem sub10_62 : sub10 [3, 4] = true := by decide +kernel
theorem sub10_63 : sub10 [4] = true := by decide +kernel
theorem sb10_1 : ∀ q ∈ blk10_1, sub10 q = true := by
  unfold blk10_1
  exact List.forall_mem_cons.2 ⟨sub10_32, List.forall_mem_cons.2 ⟨sub10_33, List.forall_mem_cons.2 ⟨sub10_34, List.forall_mem_cons.2 ⟨sub10_35, List.forall_mem_cons.2 ⟨sub10_36, List.forall_mem_cons.2 ⟨sub10_37, List.forall_mem_cons.2 ⟨sub10_38, List.forall_mem_cons.2 ⟨sub10_39, List.forall_mem_cons.2 ⟨sub10_40, List.forall_mem_cons.2 ⟨sub10_41, List.forall_mem_cons.2 ⟨sub10_42, List.forall_mem_cons.2 ⟨sub10_43, List.forall_mem_cons.2 ⟨sub10_44, List.forall_mem_cons.2 ⟨sub10_45, List.forall_mem_cons.2 ⟨sub10_46, List.forall_mem_cons.2 ⟨sub10_47, List.forall_mem_cons.2 ⟨sub10_48, List.forall_mem_cons.2 ⟨sub10_49, List.forall_mem_cons.2 ⟨sub10_50, List.forall_mem_cons.2 ⟨sub10_51, List.forall_mem_cons.2 ⟨sub10_52, List.forall_mem_cons.2 ⟨sub10_53, List.forall_mem_cons.2 ⟨sub10_54, List.forall_mem_cons.2 ⟨sub10_55, List.forall_mem_cons.2 ⟨sub10_56, List.forall_mem_cons.2 ⟨sub10_57, List.forall_mem_cons.2 ⟨sub10_58, List.forall_mem_cons.2 ⟨sub10_59, List.forall_mem_cons.2 ⟨sub10_60, List.forall_mem_cons.2 ⟨sub10_61, List.forall_mem_cons.2 ⟨sub10_62, List.forall_mem_cons.2 ⟨sub10_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub11_0 : sub11 [-3] = true := by decide +kernel
theorem sub11_1 : sub11 [-2, -2] = true := by decide +kernel
theorem sub11_2 : sub11 [-2, -1] = true := by decide +kernel
theorem sub11_3 : sub11 [-2, 0] = true := by decide +kernel
theorem sub11_4 : sub11 [-2, 1] = true := by decide +kernel
theorem sub11_5 : sub11 [-2, 2] = true := by decide +kernel
theorem sub11_6 : sub11 [-2, 3] = true := by decide +kernel
theorem sub11_7 : sub11 [-1, -3] = true := by decide +kernel
theorem sub11_8 : sub11 [-1, -2] = true := by decide +kernel
theorem sub11_9 : sub11 [-1, -1] = true := by decide +kernel
theorem sub11_10 : sub11 [-1, 0] = true := by decide +kernel
theorem sub11_11 : sub11 [-1, 1] = true := by decide +kernel
theorem sub11_12 : sub11 [-1, 2] = true := by decide +kernel
theorem sub11_13 : sub11 [-1, 3] = true := by decide +kernel
theorem sub11_14 : sub11 [0, -4] = true := by decide +kernel
theorem sub11_15 : sub11 [0, -3] = true := by decide +kernel
theorem sub11_16 : sub11 [0, -2] = true := by decide +kernel
theorem sub11_17 : sub11 [0, -1] = true := by decide +kernel
theorem sub11_18 : sub11 [0, 0] = true := by decide +kernel
theorem sub11_19 : sub11 [0, 1] = true := by decide +kernel
theorem sub11_20 : sub11 [0, 2] = true := by decide +kernel
theorem sub11_21 : sub11 [0, 3] = true := by decide +kernel
theorem sub11_22 : sub11 [1, -4] = true := by decide +kernel
theorem sub11_23 : sub11 [1, -3] = true := by decide +kernel
theorem sub11_24 : sub11 [1, -2] = true := by decide +kernel
theorem sub11_25 : sub11 [1, -1] = true := by decide +kernel
theorem sub11_26 : sub11 [1, 0] = true := by decide +kernel
theorem sub11_27 : sub11 [1, 1] = true := by decide +kernel
theorem sub11_28 : sub11 [1, 2] = true := by decide +kernel
theorem sub11_29 : sub11 [2, -4] = true := by decide +kernel
theorem sub11_30 : sub11 [2, -3] = true := by decide +kernel
theorem sub11_31 : sub11 [2, -2] = true := by decide +kernel
theorem sb11_0 : ∀ q ∈ blk11_0, sub11 q = true := by
  unfold blk11_0
  exact List.forall_mem_cons.2 ⟨sub11_0, List.forall_mem_cons.2 ⟨sub11_1, List.forall_mem_cons.2 ⟨sub11_2, List.forall_mem_cons.2 ⟨sub11_3, List.forall_mem_cons.2 ⟨sub11_4, List.forall_mem_cons.2 ⟨sub11_5, List.forall_mem_cons.2 ⟨sub11_6, List.forall_mem_cons.2 ⟨sub11_7, List.forall_mem_cons.2 ⟨sub11_8, List.forall_mem_cons.2 ⟨sub11_9, List.forall_mem_cons.2 ⟨sub11_10, List.forall_mem_cons.2 ⟨sub11_11, List.forall_mem_cons.2 ⟨sub11_12, List.forall_mem_cons.2 ⟨sub11_13, List.forall_mem_cons.2 ⟨sub11_14, List.forall_mem_cons.2 ⟨sub11_15, List.forall_mem_cons.2 ⟨sub11_16, List.forall_mem_cons.2 ⟨sub11_17, List.forall_mem_cons.2 ⟨sub11_18, List.forall_mem_cons.2 ⟨sub11_19, List.forall_mem_cons.2 ⟨sub11_20, List.forall_mem_cons.2 ⟨sub11_21, List.forall_mem_cons.2 ⟨sub11_22, List.forall_mem_cons.2 ⟨sub11_23, List.forall_mem_cons.2 ⟨sub11_24, List.forall_mem_cons.2 ⟨sub11_25, List.forall_mem_cons.2 ⟨sub11_26, List.forall_mem_cons.2 ⟨sub11_27, List.forall_mem_cons.2 ⟨sub11_28, List.forall_mem_cons.2 ⟨sub11_29, List.forall_mem_cons.2 ⟨sub11_30, List.forall_mem_cons.2 ⟨sub11_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub11_32 : sub11 [2, -1] = true := by decide +kernel
theorem sub11_33 : sub11 [2, 0] = true := by decide +kernel
theorem sub11_34 : sub11 [2, 1] = true := by decide +kernel
theorem sub11_35 : sub11 [3] = true := by decide +kernel
theorem sb11_1 : ∀ q ∈ blk11_1, sub11 q = true := by
  unfold blk11_1
  exact List.forall_mem_cons.2 ⟨sub11_32, List.forall_mem_cons.2 ⟨sub11_33, List.forall_mem_cons.2 ⟨sub11_34, List.forall_mem_cons.2 ⟨sub11_35, List.forall_mem_nil _⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C104
