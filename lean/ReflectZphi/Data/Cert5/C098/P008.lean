import ReflectZphi.Data.Cert5.C098.Base

namespace ReflectZphi.Data.Cert5.C098
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub8_480 : sub8 [4, -2] = true := by decide +kernel
theorem sub8_481 : sub8 [4, -1] = true := by decide +kernel
theorem sub8_482 : sub8 [4, 0] = true := by decide +kernel
theorem sub8_483 : sub8 [4, 1] = true := by decide +kernel
theorem sub8_484 : sub8 [4, 2] = true := by decide +kernel
theorem sub8_485 : sub8 [5, -5] = true := by decide +kernel
theorem sub8_486 : sub8 [5, -4] = true := by decide +kernel
theorem sub8_487 : sub8 [5, -3] = true := by decide +kernel
theorem sub8_488 : sub8 [5, -2] = true := by decide +kernel
theorem sub8_489 : sub8 [5, -1] = true := by decide +kernel
theorem sub8_490 : sub8 [5, 0] = true := by decide +kernel
theorem sb8_15 : ∀ q ∈ blk8_15, sub8 q = true := by
  unfold blk8_15
  exact List.forall_mem_cons.2 ⟨sub8_480, List.forall_mem_cons.2 ⟨sub8_481, List.forall_mem_cons.2 ⟨sub8_482, List.forall_mem_cons.2 ⟨sub8_483, List.forall_mem_cons.2 ⟨sub8_484, List.forall_mem_cons.2 ⟨sub8_485, List.forall_mem_cons.2 ⟨sub8_486, List.forall_mem_cons.2 ⟨sub8_487, List.forall_mem_cons.2 ⟨sub8_488, List.forall_mem_cons.2 ⟨sub8_489, List.forall_mem_cons.2 ⟨sub8_490, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_0 : sub9 [-4] = true := by decide +kernel
theorem sub9_1 : sub9 [-3, -3] = true := by decide +kernel
theorem sub9_2 : sub9 [-3, -2] = true := by decide +kernel
theorem sub9_3 : sub9 [-3, -1] = true := by decide +kernel
theorem sub9_4 : sub9 [-3, 0] = true := by decide +kernel
theorem sub9_5 : sub9 [-3, 1] = true := by decide +kernel
theorem sub9_6 : sub9 [-3, 2] = true := by decide +kernel
theorem sub9_7 : sub9 [-3, 3] = true := by decide +kernel
theorem sub9_8 : sub9 [-3, 4] = true := by decide +kernel
theorem sub9_9 : sub9 [-2, -4] = true := by decide +kernel
theorem sub9_10 : sub9 [-2, -3] = true := by decide +kernel
theorem sub9_11 : sub9 [-2, -2] = true := by decide +kernel
theorem sub9_12 : sub9 [-2, -1] = true := by decide +kernel
theorem sub9_13 : sub9 [-2, 0] = true := by decide +kernel
theorem sub9_14 : sub9 [-2, 1] = true := by decide +kernel
theorem sub9_15 : sub9 [-2, 2] = true := by decide +kernel
theorem sub9_16 : sub9 [-2, 3] = true := by decide +kernel
theorem sub9_17 : sub9 [-2, 4] = true := by decide +kernel
theorem sub9_18 : sub9 [-2, 5] = true := by decide +kernel
theorem sub9_19 : sub9 [-1, -5] = true := by decide +kernel
theorem sub9_20 : sub9 [-1, -4] = true := by decide +kernel
theorem sub9_21 : sub9 [-1, -3] = true := by decide +kernel
theorem sub9_22 : sub9 [-1, -2] = true := by decide +kernel
theorem sub9_23 : sub9 [-1, -1] = true := by decide +kernel
theorem sub9_24 : sub9 [-1, 0] = true := by decide +kernel
theorem sub9_25 : sub9 [-1, 1] = true := by decide +kernel
theorem sub9_26 : sub9 [-1, 2] = true := by decide +kernel
theorem sub9_27 : sub9 [-1, 3] = true := by decide +kernel
theorem sub9_28 : sub9 [-1, 4] = true := by decide +kernel
theorem sub9_29 : sub9 [-1, 5] = true := by decide +kernel
theorem sub9_30 : sub9 [0, -6] = true := by decide +kernel
theorem sub9_31 : sub9 [0, -5] = true := by decide +kernel
theorem sb9_0 : ∀ q ∈ blk9_0, sub9 q = true := by
  unfold blk9_0
  exact List.forall_mem_cons.2 ⟨sub9_0, List.forall_mem_cons.2 ⟨sub9_1, List.forall_mem_cons.2 ⟨sub9_2, List.forall_mem_cons.2 ⟨sub9_3, List.forall_mem_cons.2 ⟨sub9_4, List.forall_mem_cons.2 ⟨sub9_5, List.forall_mem_cons.2 ⟨sub9_6, List.forall_mem_cons.2 ⟨sub9_7, List.forall_mem_cons.2 ⟨sub9_8, List.forall_mem_cons.2 ⟨sub9_9, List.forall_mem_cons.2 ⟨sub9_10, List.forall_mem_cons.2 ⟨sub9_11, List.forall_mem_cons.2 ⟨sub9_12, List.forall_mem_cons.2 ⟨sub9_13, List.forall_mem_cons.2 ⟨sub9_14, List.forall_mem_cons.2 ⟨sub9_15, List.forall_mem_cons.2 ⟨sub9_16, List.forall_mem_cons.2 ⟨sub9_17, List.forall_mem_cons.2 ⟨sub9_18, List.forall_mem_cons.2 ⟨sub9_19, List.forall_mem_cons.2 ⟨sub9_20, List.forall_mem_cons.2 ⟨sub9_21, List.forall_mem_cons.2 ⟨sub9_22, List.forall_mem_cons.2 ⟨sub9_23, List.forall_mem_cons.2 ⟨sub9_24, List.forall_mem_cons.2 ⟨sub9_25, List.forall_mem_cons.2 ⟨sub9_26, List.forall_mem_cons.2 ⟨sub9_27, List.forall_mem_cons.2 ⟨sub9_28, List.forall_mem_cons.2 ⟨sub9_29, List.forall_mem_cons.2 ⟨sub9_30, List.forall_mem_cons.2 ⟨sub9_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_32 : sub9 [0, -4] = true := by decide +kernel
theorem sub9_33 : sub9 [0, -3] = true := by decide +kernel
theorem sub9_34 : sub9 [0, -2] = true := by decide +kernel
theorem sub9_35 : sub9 [0, -1] = true := by decide +kernel
theorem sub9_36 : sub9 [0, 0] = true := by decide +kernel
theorem sub9_37 : sub9 [0, 1] = true := by decide +kernel
theorem sub9_38 : sub9 [0, 2] = true := by decide +kernel
theorem sub9_39 : sub9 [0, 3] = true := by decide +kernel
theorem sub9_40 : sub9 [0, 4] = true := by decide +kernel
theorem sub9_41 : sub9 [0, 5] = true := by decide +kernel
theorem sub9_42 : sub9 [1, -6] = true := by decide +kernel
theorem sub9_43 : sub9 [1, -5] = true := by decide +kernel
theorem sub9_44 : sub9 [1, -4] = true := by decide +kernel
theorem sub9_45 : sub9 [1, -3] = true := by decide +kernel
theorem sub9_46 : sub9 [1, -2] = true := by decide +kernel
theorem sub9_47 : sub9 [1, -1] = true := by decide +kernel
theorem sub9_48 : sub9 [1, 0] = true := by decide +kernel
theorem sub9_49 : sub9 [1, 1] = true := by decide +kernel
theorem sub9_50 : sub9 [1, 2] = true := by decide +kernel
theorem sub9_51 : sub9 [1, 3] = true := by decide +kernel
theorem sub9_52 : sub9 [1, 4] = true := by decide +kernel
theorem sub9_53 : sub9 [2, -6] = true := by decide +kernel
theorem sub9_54 : sub9 [2, -5] = true := by decide +kernel
theorem sub9_55 : sub9 [2, -4] = true := by decide +kernel
theorem sub9_56 : sub9 [2, -3] = true := by decide +kernel
theorem sub9_57 : sub9 [2, -2] = true := by decide +kernel
theorem sub9_58 : sub9 [2, -1] = true := by decide +kernel
theorem sub9_59 : sub9 [2, 0] = true := by decide +kernel
theorem sub9_60 : sub9 [2, 1] = true := by decide +kernel
theorem sub9_61 : sub9 [2, 2] = true := by decide +kernel
theorem sub9_62 : sub9 [2, 3] = true := by decide +kernel
theorem sub9_63 : sub9 [3, -5] = true := by decide +kernel
theorem sb9_1 : ∀ q ∈ blk9_1, sub9 q = true := by
  unfold blk9_1
  exact List.forall_mem_cons.2 ⟨sub9_32, List.forall_mem_cons.2 ⟨sub9_33, List.forall_mem_cons.2 ⟨sub9_34, List.forall_mem_cons.2 ⟨sub9_35, List.forall_mem_cons.2 ⟨sub9_36, List.forall_mem_cons.2 ⟨sub9_37, List.forall_mem_cons.2 ⟨sub9_38, List.forall_mem_cons.2 ⟨sub9_39, List.forall_mem_cons.2 ⟨sub9_40, List.forall_mem_cons.2 ⟨sub9_41, List.forall_mem_cons.2 ⟨sub9_42, List.forall_mem_cons.2 ⟨sub9_43, List.forall_mem_cons.2 ⟨sub9_44, List.forall_mem_cons.2 ⟨sub9_45, List.forall_mem_cons.2 ⟨sub9_46, List.forall_mem_cons.2 ⟨sub9_47, List.forall_mem_cons.2 ⟨sub9_48, List.forall_mem_cons.2 ⟨sub9_49, List.forall_mem_cons.2 ⟨sub9_50, List.forall_mem_cons.2 ⟨sub9_51, List.forall_mem_cons.2 ⟨sub9_52, List.forall_mem_cons.2 ⟨sub9_53, List.forall_mem_cons.2 ⟨sub9_54, List.forall_mem_cons.2 ⟨sub9_55, List.forall_mem_cons.2 ⟨sub9_56, List.forall_mem_cons.2 ⟨sub9_57, List.forall_mem_cons.2 ⟨sub9_58, List.forall_mem_cons.2 ⟨sub9_59, List.forall_mem_cons.2 ⟨sub9_60, List.forall_mem_cons.2 ⟨sub9_61, List.forall_mem_cons.2 ⟨sub9_62, List.forall_mem_cons.2 ⟨sub9_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_64 : sub9 [3, -4] = true := by decide +kernel
theorem sub9_65 : sub9 [3, -3] = true := by decide +kernel
theorem sub9_66 : sub9 [3, -2] = true := by decide +kernel
theorem sub9_67 : sub9 [3, -1] = true := by decide +kernel
theorem sub9_68 : sub9 [3, 0] = true := by decide +kernel
theorem sub9_69 : sub9 [3, 1] = true := by decide +kernel
theorem sub9_70 : sub9 [3, 2] = true := by decide +kernel
theorem sub9_71 : sub9 [4] = true := by decide +kernel
theorem sb9_2 : ∀ q ∈ blk9_2, sub9 q = true := by
  unfold blk9_2
  exact List.forall_mem_cons.2 ⟨sub9_64, List.forall_mem_cons.2 ⟨sub9_65, List.forall_mem_cons.2 ⟨sub9_66, List.forall_mem_cons.2 ⟨sub9_67, List.forall_mem_cons.2 ⟨sub9_68, List.forall_mem_cons.2 ⟨sub9_69, List.forall_mem_cons.2 ⟨sub9_70, List.forall_mem_cons.2 ⟨sub9_71, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C098
