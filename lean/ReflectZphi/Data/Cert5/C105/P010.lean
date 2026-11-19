import ReflectZphi.Data.Cert5.C105.Base

namespace ReflectZphi.Data.Cert5.C105
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub12_0 : sub12 [-4] = true := by decide +kernel
theorem sub12_1 : sub12 [-3, -5] = true := by decide +kernel
theorem sub12_2 : sub12 [-3, -4] = true := by decide +kernel
theorem sub12_3 : sub12 [-3, -3] = true := by decide +kernel
theorem sub12_4 : sub12 [-3, -2] = true := by decide +kernel
theorem sub12_5 : sub12 [-3, -1] = true := by decide +kernel
theorem sub12_6 : sub12 [-3, 0] = true := by decide +kernel
theorem sub12_7 : sub12 [-3, 1] = true := by decide +kernel
theorem sub12_8 : sub12 [-3, 2] = true := by decide +kernel
theorem sub12_9 : sub12 [-2, -5] = true := by decide +kernel
theorem sub12_10 : sub12 [-2, -4] = true := by decide +kernel
theorem sub12_11 : sub12 [-2, -3] = true := by decide +kernel
theorem sub12_12 : sub12 [-2, -2] = true := by decide +kernel
theorem sub12_13 : sub12 [-2, -1] = true := by decide +kernel
theorem sub12_14 : sub12 [-2, 0] = true := by decide +kernel
theorem sub12_15 : sub12 [-2, 1] = true := by decide +kernel
theorem sub12_16 : sub12 [-2, 2] = true := by decide +kernel
theorem sub12_17 : sub12 [-2, 3] = true := by decide +kernel
theorem sub12_18 : sub12 [-1, -5] = true := by decide +kernel
theorem sub12_19 : sub12 [-1, -4] = true := by decide +kernel
theorem sub12_20 : sub12 [-1, -3] = true := by decide +kernel
theorem sub12_21 : sub12 [-1, -2] = true := by decide +kernel
theorem sub12_22 : sub12 [-1, -1] = true := by decide +kernel
theorem sub12_23 : sub12 [-1, 0] = true := by decide +kernel
theorem sub12_24 : sub12 [-1, 1] = true := by decide +kernel
theorem sub12_25 : sub12 [-1, 2] = true := by decide +kernel
theorem sub12_26 : sub12 [-1, 3] = true := by decide +kernel
theorem sub12_27 : sub12 [0, -5] = true := by decide +kernel
theorem sub12_28 : sub12 [0, -4] = true := by decide +kernel
theorem sub12_29 : sub12 [0, -3] = true := by decide +kernel
theorem sub12_30 : sub12 [0, -2] = true := by decide +kernel
theorem sub12_31 : sub12 [0, -1] = true := by decide +kernel
theorem sb12_0 : ∀ q ∈ blk12_0, sub12 q = true := by
  unfold blk12_0
  exact List.forall_mem_cons.2 ⟨sub12_0, List.forall_mem_cons.2 ⟨sub12_1, List.forall_mem_cons.2 ⟨sub12_2, List.forall_mem_cons.2 ⟨sub12_3, List.forall_mem_cons.2 ⟨sub12_4, List.forall_mem_cons.2 ⟨sub12_5, List.forall_mem_cons.2 ⟨sub12_6, List.forall_mem_cons.2 ⟨sub12_7, List.forall_mem_cons.2 ⟨sub12_8, List.forall_mem_cons.2 ⟨sub12_9, List.forall_mem_cons.2 ⟨sub12_10, List.forall_mem_cons.2 ⟨sub12_11, List.forall_mem_cons.2 ⟨sub12_12, List.forall_mem_cons.2 ⟨sub12_13, List.forall_mem_cons.2 ⟨sub12_14, List.forall_mem_cons.2 ⟨sub12_15, List.forall_mem_cons.2 ⟨sub12_16, List.forall_mem_cons.2 ⟨sub12_17, List.forall_mem_cons.2 ⟨sub12_18, List.forall_mem_cons.2 ⟨sub12_19, List.forall_mem_cons.2 ⟨sub12_20, List.forall_mem_cons.2 ⟨sub12_21, List.forall_mem_cons.2 ⟨sub12_22, List.forall_mem_cons.2 ⟨sub12_23, List.forall_mem_cons.2 ⟨sub12_24, List.forall_mem_cons.2 ⟨sub12_25, List.forall_mem_cons.2 ⟨sub12_26, List.forall_mem_cons.2 ⟨sub12_27, List.forall_mem_cons.2 ⟨sub12_28, List.forall_mem_cons.2 ⟨sub12_29, List.forall_mem_cons.2 ⟨sub12_30, List.forall_mem_cons.2 ⟨sub12_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub12_32 : sub12 [0, 0] = true := by decide +kernel
theorem sub12_33 : sub12 [0, 1] = true := by decide +kernel
theorem sub12_34 : sub12 [0, 2] = true := by decide +kernel
theorem sub12_35 : sub12 [0, 3] = true := by decide +kernel
theorem sub12_36 : sub12 [0, 4] = true := by decide +kernel
theorem sub12_37 : sub12 [1, -4] = true := by decide +kernel
theorem sub12_38 : sub12 [1, -3] = true := by decide +kernel
theorem sub12_39 : sub12 [1, -2] = true := by decide +kernel
theorem sub12_40 : sub12 [1, -1] = true := by decide +kernel
theorem sub12_41 : sub12 [1, 0] = true := by decide +kernel
theorem sub12_42 : sub12 [1, 1] = true := by decide +kernel
theorem sub12_43 : sub12 [1, 2] = true := by decide +kernel
theorem sub12_44 : sub12 [1, 3] = true := by decide +kernel
theorem sub12_45 : sub12 [1, 4] = true := by decide +kernel
theorem sub12_46 : sub12 [2, -4] = true := by decide +kernel
theorem sub12_47 : sub12 [2, -3] = true := by decide +kernel
theorem sub12_48 : sub12 [2, -2] = true := by decide +kernel
theorem sub12_49 : sub12 [2, -1] = true := by decide +kernel
theorem sub12_50 : sub12 [2, 0] = true := by decide +kernel
theorem sub12_51 : sub12 [2, 1] = true := by decide +kernel
theorem sub12_52 : sub12 [2, 2] = true := by decide +kernel
theorem sub12_53 : sub12 [2, 3] = true := by decide +kernel
theorem sub12_54 : sub12 [2, 4] = true := by decide +kernel
theorem sub12_55 : sub12 [3, -3] = true := by decide +kernel
theorem sub12_56 : sub12 [3, -2] = true := by decide +kernel
theorem sub12_57 : sub12 [3, -1] = true := by decide +kernel
theorem sub12_58 : sub12 [3, 0] = true := by decide +kernel
theorem sub12_59 : sub12 [3, 1] = true := by decide +kernel
theorem sub12_60 : sub12 [3, 2] = true := by decide +kernel
theorem sub12_61 : sub12 [3, 3] = true := by decide +kernel
theorem sub12_62 : sub12 [3, 4] = true := by decide +kernel
theorem sub12_63 : sub12 [4] = true := by decide +kernel
theorem sb12_1 : ∀ q ∈ blk12_1, sub12 q = true := by
  unfold blk12_1
  exact List.forall_mem_cons.2 ⟨sub12_32, List.forall_mem_cons.2 ⟨sub12_33, List.forall_mem_cons.2 ⟨sub12_34, List.forall_mem_cons.2 ⟨sub12_35, List.forall_mem_cons.2 ⟨sub12_36, List.forall_mem_cons.2 ⟨sub12_37, List.forall_mem_cons.2 ⟨sub12_38, List.forall_mem_cons.2 ⟨sub12_39, List.forall_mem_cons.2 ⟨sub12_40, List.forall_mem_cons.2 ⟨sub12_41, List.forall_mem_cons.2 ⟨sub12_42, List.forall_mem_cons.2 ⟨sub12_43, List.forall_mem_cons.2 ⟨sub12_44, List.forall_mem_cons.2 ⟨sub12_45, List.forall_mem_cons.2 ⟨sub12_46, List.forall_mem_cons.2 ⟨sub12_47, List.forall_mem_cons.2 ⟨sub12_48, List.forall_mem_cons.2 ⟨sub12_49, List.forall_mem_cons.2 ⟨sub12_50, List.forall_mem_cons.2 ⟨sub12_51, List.forall_mem_cons.2 ⟨sub12_52, List.forall_mem_cons.2 ⟨sub12_53, List.forall_mem_cons.2 ⟨sub12_54, List.forall_mem_cons.2 ⟨sub12_55, List.forall_mem_cons.2 ⟨sub12_56, List.forall_mem_cons.2 ⟨sub12_57, List.forall_mem_cons.2 ⟨sub12_58, List.forall_mem_cons.2 ⟨sub12_59, List.forall_mem_cons.2 ⟨sub12_60, List.forall_mem_cons.2 ⟨sub12_61, List.forall_mem_cons.2 ⟨sub12_62, List.forall_mem_cons.2 ⟨sub12_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub13_0 : sub13 [-3] = true := by decide +kernel
theorem sub13_1 : sub13 [-2] = true := by decide +kernel
theorem sub13_2 : sub13 [-1] = true := by decide +kernel
theorem sub13_3 : sub13 [0, -4] = true := by decide +kernel
theorem sub13_4 : sub13 [0, -3] = true := by decide +kernel
theorem sub13_5 : sub13 [0, -2] = true := by decide +kernel
theorem sub13_6 : sub13 [0, -1] = true := by decide +kernel
theorem sub13_7 : sub13 [0, 0] = true := by decide +kernel
theorem sub13_8 : sub13 [0, 1] = true := by decide +kernel
theorem sub13_9 : sub13 [0, 2] = true := by decide +kernel
theorem sub13_10 : sub13 [0, 3] = true := by decide +kernel
theorem sub13_11 : sub13 [1] = true := by decide +kernel
theorem sub13_12 : sub13 [2] = true := by decide +kernel
theorem sub13_13 : sub13 [3] = true := by decide +kernel
theorem sb13_0 : ∀ q ∈ blk13_0, sub13 q = true := by
  unfold blk13_0
  exact List.forall_mem_cons.2 ⟨sub13_0, List.forall_mem_cons.2 ⟨sub13_1, List.forall_mem_cons.2 ⟨sub13_2, List.forall_mem_cons.2 ⟨sub13_3, List.forall_mem_cons.2 ⟨sub13_4, List.forall_mem_cons.2 ⟨sub13_5, List.forall_mem_cons.2 ⟨sub13_6, List.forall_mem_cons.2 ⟨sub13_7, List.forall_mem_cons.2 ⟨sub13_8, List.forall_mem_cons.2 ⟨sub13_9, List.forall_mem_cons.2 ⟨sub13_10, List.forall_mem_cons.2 ⟨sub13_11, List.forall_mem_cons.2 ⟨sub13_12, List.forall_mem_cons.2 ⟨sub13_13, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C105
