import ReflectZphi.Data.Cert5.C083.Base

namespace ReflectZphi.Data.Cert5.C083
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub0_0 : sub0 [-3] = true := by decide +kernel
theorem sub0_1 : sub0 [-2, -3] = true := by decide +kernel
theorem sub0_2 : sub0 [-2, -2] = true := by decide +kernel
theorem sub0_3 : sub0 [-2, -1] = true := by decide +kernel
theorem sub0_4 : sub0 [-2, 0] = true := by decide +kernel
theorem sub0_5 : sub0 [-2, 1] = true := by decide +kernel
theorem sub0_6 : sub0 [-2, 2] = true := by decide +kernel
theorem sub0_7 : sub0 [-2, 3] = true := by decide +kernel
theorem sub0_8 : sub0 [-1, -4] = true := by decide +kernel
theorem sub0_9 : sub0 [-1, -3] = true := by decide +kernel
theorem sub0_10 : sub0 [-1, -2] = true := by decide +kernel
theorem sub0_11 : sub0 [-1, -1] = true := by decide +kernel
theorem sub0_12 : sub0 [-1, 0] = true := by decide +kernel
theorem sub0_13 : sub0 [-1, 1] = true := by decide +kernel
theorem sub0_14 : sub0 [-1, 2] = true := by decide +kernel
theorem sub0_15 : sub0 [-1, 3] = true := by decide +kernel
theorem sub0_16 : sub0 [0, -4] = true := by decide +kernel
theorem sub0_17 : sub0 [0, -3] = true := by decide +kernel
theorem sub0_18 : sub0 [0, -2] = true := by decide +kernel
theorem sub0_19 : sub0 [0, -1] = true := by decide +kernel
theorem sub0_20 : sub0 [0, 0] = true := by decide +kernel
theorem sub0_21 : sub0 [0, 1] = true := by decide +kernel
theorem sub0_22 : sub0 [0, 2] = true := by decide +kernel
theorem sub0_23 : sub0 [0, 3] = true := by decide +kernel
theorem sub0_24 : sub0 [1, -4] = true := by decide +kernel
theorem sub0_25 : sub0 [1, -3] = true := by decide +kernel
theorem sub0_26 : sub0 [1, -2] = true := by decide +kernel
theorem sub0_27 : sub0 [1, -1] = true := by decide +kernel
theorem sub0_28 : sub0 [1, 0] = true := by decide +kernel
theorem sub0_29 : sub0 [1, 1] = true := by decide +kernel
theorem sub0_30 : sub0 [1, 2] = true := by decide +kernel
theorem sub0_31 : sub0 [1, 3] = true := by decide +kernel
theorem sb0_0 : ∀ q ∈ blk0_0, sub0 q = true := by
  unfold blk0_0
  exact List.forall_mem_cons.2 ⟨sub0_0, List.forall_mem_cons.2 ⟨sub0_1, List.forall_mem_cons.2 ⟨sub0_2, List.forall_mem_cons.2 ⟨sub0_3, List.forall_mem_cons.2 ⟨sub0_4, List.forall_mem_cons.2 ⟨sub0_5, List.forall_mem_cons.2 ⟨sub0_6, List.forall_mem_cons.2 ⟨sub0_7, List.forall_mem_cons.2 ⟨sub0_8, List.forall_mem_cons.2 ⟨sub0_9, List.forall_mem_cons.2 ⟨sub0_10, List.forall_mem_cons.2 ⟨sub0_11, List.forall_mem_cons.2 ⟨sub0_12, List.forall_mem_cons.2 ⟨sub0_13, List.forall_mem_cons.2 ⟨sub0_14, List.forall_mem_cons.2 ⟨sub0_15, List.forall_mem_cons.2 ⟨sub0_16, List.forall_mem_cons.2 ⟨sub0_17, List.forall_mem_cons.2 ⟨sub0_18, List.forall_mem_cons.2 ⟨sub0_19, List.forall_mem_cons.2 ⟨sub0_20, List.forall_mem_cons.2 ⟨sub0_21, List.forall_mem_cons.2 ⟨sub0_22, List.forall_mem_cons.2 ⟨sub0_23, List.forall_mem_cons.2 ⟨sub0_24, List.forall_mem_cons.2 ⟨sub0_25, List.forall_mem_cons.2 ⟨sub0_26, List.forall_mem_cons.2 ⟨sub0_27, List.forall_mem_cons.2 ⟨sub0_28, List.forall_mem_cons.2 ⟨sub0_29, List.forall_mem_cons.2 ⟨sub0_30, List.forall_mem_cons.2 ⟨sub0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub0_32 : sub0 [2, -4] = true := by decide +kernel
theorem sub0_33 : sub0 [2, -3] = true := by decide +kernel
theorem sub0_34 : sub0 [2, -2] = true := by decide +kernel
theorem sub0_35 : sub0 [2, -1] = true := by decide +kernel
theorem sub0_36 : sub0 [2, 0] = true := by decide +kernel
theorem sub0_37 : sub0 [2, 1] = true := by decide +kernel
theorem sub0_38 : sub0 [2, 2] = true := by decide +kernel
theorem sub0_39 : sub0 [3] = true := by decide +kernel
theorem sb0_1 : ∀ q ∈ blk0_1, sub0 q = true := by
  unfold blk0_1
  exact List.forall_mem_cons.2 ⟨sub0_32, List.forall_mem_cons.2 ⟨sub0_33, List.forall_mem_cons.2 ⟨sub0_34, List.forall_mem_cons.2 ⟨sub0_35, List.forall_mem_cons.2 ⟨sub0_36, List.forall_mem_cons.2 ⟨sub0_37, List.forall_mem_cons.2 ⟨sub0_38, List.forall_mem_cons.2 ⟨sub0_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub1_0 : sub1 [-4] = true := by decide +kernel
theorem sub1_1 : sub1 [-3, -4] = true := by decide +kernel
theorem sub1_2 : sub1 [-3, -3] = true := by decide +kernel
theorem sub1_3 : sub1 [-3, -2] = true := by decide +kernel
theorem sub1_4 : sub1 [-3, -1] = true := by decide +kernel
theorem sub1_5 : sub1 [-3, 0] = true := by decide +kernel
theorem sub1_6 : sub1 [-3, 1] = true := by decide +kernel
theorem sub1_7 : sub1 [-3, 2] = true := by decide +kernel
theorem sub1_8 : sub1 [-2, -4] = true := by decide +kernel
theorem sub1_9 : sub1 [-2, -3] = true := by decide +kernel
theorem sub1_10 : sub1 [-2, -2] = true := by decide +kernel
theorem sub1_11 : sub1 [-2, -1] = true := by decide +kernel
theorem sub1_12 : sub1 [-2, 0] = true := by decide +kernel
theorem sub1_13 : sub1 [-2, 1] = true := by decide +kernel
theorem sub1_14 : sub1 [-2, 2] = true := by decide +kernel
theorem sub1_15 : sub1 [-2, 3] = true := by decide +kernel
theorem sub1_16 : sub1 [-1, -5] = true := by decide +kernel
theorem sub1_17 : sub1 [-1, -4] = true := by decide +kernel
theorem sub1_18 : sub1 [-1, -3] = true := by decide +kernel
theorem sub1_19 : sub1 [-1, -2] = true := by decide +kernel
theorem sub1_20 : sub1 [-1, -1] = true := by decide +kernel
theorem sub1_21 : sub1 [-1, 0] = true := by decide +kernel
theorem sub1_22 : sub1 [-1, 1] = true := by decide +kernel
theorem sub1_23 : sub1 [-1, 2] = true := by decide +kernel
theorem sub1_24 : sub1 [-1, 3] = true := by decide +kernel
theorem sub1_25 : sub1 [-1, 4] = true := by decide +kernel
theorem sub1_26 : sub1 [0, -5] = true := by decide +kernel
theorem sub1_27 : sub1 [0, -4] = true := by decide +kernel
theorem sub1_28 : sub1 [0, -3] = true := by decide +kernel
theorem sub1_29 : sub1 [0, -2] = true := by decide +kernel
theorem sub1_30 : sub1 [0, -1] = true := by decide +kernel
theorem sub1_31 : sub1 [0, 0] = true := by decide +kernel
theorem sb1_0 : ∀ q ∈ blk1_0, sub1 q = true := by
  unfold blk1_0
  exact List.forall_mem_cons.2 ⟨sub1_0, List.forall_mem_cons.2 ⟨sub1_1, List.forall_mem_cons.2 ⟨sub1_2, List.forall_mem_cons.2 ⟨sub1_3, List.forall_mem_cons.2 ⟨sub1_4, List.forall_mem_cons.2 ⟨sub1_5, List.forall_mem_cons.2 ⟨sub1_6, List.forall_mem_cons.2 ⟨sub1_7, List.forall_mem_cons.2 ⟨sub1_8, List.forall_mem_cons.2 ⟨sub1_9, List.forall_mem_cons.2 ⟨sub1_10, List.forall_mem_cons.2 ⟨sub1_11, List.forall_mem_cons.2 ⟨sub1_12, List.forall_mem_cons.2 ⟨sub1_13, List.forall_mem_cons.2 ⟨sub1_14, List.forall_mem_cons.2 ⟨sub1_15, List.forall_mem_cons.2 ⟨sub1_16, List.forall_mem_cons.2 ⟨sub1_17, List.forall_mem_cons.2 ⟨sub1_18, List.forall_mem_cons.2 ⟨sub1_19, List.forall_mem_cons.2 ⟨sub1_20, List.forall_mem_cons.2 ⟨sub1_21, List.forall_mem_cons.2 ⟨sub1_22, List.forall_mem_cons.2 ⟨sub1_23, List.forall_mem_cons.2 ⟨sub1_24, List.forall_mem_cons.2 ⟨sub1_25, List.forall_mem_cons.2 ⟨sub1_26, List.forall_mem_cons.2 ⟨sub1_27, List.forall_mem_cons.2 ⟨sub1_28, List.forall_mem_cons.2 ⟨sub1_29, List.forall_mem_cons.2 ⟨sub1_30, List.forall_mem_cons.2 ⟨sub1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub1_32 : sub1 [0, 1] = true := by decide +kernel
theorem sub1_33 : sub1 [0, 2] = true := by decide +kernel
theorem sub1_34 : sub1 [0, 3] = true := by decide +kernel
theorem sub1_35 : sub1 [0, 4] = true := by decide +kernel
theorem sub1_36 : sub1 [1, -5] = true := by decide +kernel
theorem sub1_37 : sub1 [1, -4] = true := by decide +kernel
theorem sub1_38 : sub1 [1, -3] = true := by decide +kernel
theorem sub1_39 : sub1 [1, -2] = true := by decide +kernel
theorem sub1_40 : sub1 [1, -1] = true := by decide +kernel
theorem sub1_41 : sub1 [1, 0] = true := by decide +kernel
theorem sub1_42 : sub1 [1, 1] = true := by decide +kernel
theorem sub1_43 : sub1 [1, 2] = true := by decide +kernel
theorem sub1_44 : sub1 [1, 3] = true := by decide +kernel
theorem sub1_45 : sub1 [1, 4] = true := by decide +kernel
theorem sub1_46 : sub1 [2, -4] = true := by decide +kernel
theorem sub1_47 : sub1 [2, -3] = true := by decide +kernel
theorem sub1_48 : sub1 [2, -2] = true := by decide +kernel
theorem sub1_49 : sub1 [2, -1] = true := by decide +kernel
theorem sub1_50 : sub1 [2, 0] = true := by decide +kernel
theorem sub1_51 : sub1 [2, 1] = true := by decide +kernel
theorem sub1_52 : sub1 [2, 2] = true := by decide +kernel
theorem sub1_53 : sub1 [2, 3] = true := by decide +kernel
theorem sub1_54 : sub1 [3, -3] = true := by decide +kernel
theorem sub1_55 : sub1 [3, -2] = true := by decide +kernel
theorem sub1_56 : sub1 [3, -1] = true := by decide +kernel
theorem sub1_57 : sub1 [3, 0] = true := by decide +kernel
theorem sub1_58 : sub1 [3, 1] = true := by decide +kernel
theorem sub1_59 : sub1 [3, 2] = true := by decide +kernel
theorem sub1_60 : sub1 [3, 3] = true := by decide +kernel
theorem sub1_61 : sub1 [4] = true := by decide +kernel
theorem sb1_1 : ∀ q ∈ blk1_1, sub1 q = true := by
  unfold blk1_1
  exact List.forall_mem_cons.2 ⟨sub1_32, List.forall_mem_cons.2 ⟨sub1_33, List.forall_mem_cons.2 ⟨sub1_34, List.forall_mem_cons.2 ⟨sub1_35, List.forall_mem_cons.2 ⟨sub1_36, List.forall_mem_cons.2 ⟨sub1_37, List.forall_mem_cons.2 ⟨sub1_38, List.forall_mem_cons.2 ⟨sub1_39, List.forall_mem_cons.2 ⟨sub1_40, List.forall_mem_cons.2 ⟨sub1_41, List.forall_mem_cons.2 ⟨sub1_42, List.forall_mem_cons.2 ⟨sub1_43, List.forall_mem_cons.2 ⟨sub1_44, List.forall_mem_cons.2 ⟨sub1_45, List.forall_mem_cons.2 ⟨sub1_46, List.forall_mem_cons.2 ⟨sub1_47, List.forall_mem_cons.2 ⟨sub1_48, List.forall_mem_cons.2 ⟨sub1_49, List.forall_mem_cons.2 ⟨sub1_50, List.forall_mem_cons.2 ⟨sub1_51, List.forall_mem_cons.2 ⟨sub1_52, List.forall_mem_cons.2 ⟨sub1_53, List.forall_mem_cons.2 ⟨sub1_54, List.forall_mem_cons.2 ⟨sub1_55, List.forall_mem_cons.2 ⟨sub1_56, List.forall_mem_cons.2 ⟨sub1_57, List.forall_mem_cons.2 ⟨sub1_58, List.forall_mem_cons.2 ⟨sub1_59, List.forall_mem_cons.2 ⟨sub1_60, List.forall_mem_cons.2 ⟨sub1_61, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C083
