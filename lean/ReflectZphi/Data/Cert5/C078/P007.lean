import ReflectZphi.Data.Cert5.C078.Base

namespace ReflectZphi.Data.Cert5.C078
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub6_0 : sub6 [-3, -3] = true := by decide +kernel
theorem sub6_1 : sub6 [-3, -2] = true := by decide +kernel
theorem sub6_2 : sub6 [-3, -1] = true := by decide +kernel
theorem sub6_3 : sub6 [-3, 0] = true := by decide +kernel
theorem sub6_4 : sub6 [-3, 1] = true := by decide +kernel
theorem sub6_5 : sub6 [-3, 2] = true := by decide +kernel
theorem sub6_6 : sub6 [-3, 3] = true := by decide +kernel
theorem sub6_7 : sub6 [-2, -4] = true := by decide +kernel
theorem sub6_8 : sub6 [-2, -3] = true := by decide +kernel
theorem sub6_9 : sub6 [-2, -2] = true := by decide +kernel
theorem sub6_10 : sub6 [-2, -1] = true := by decide +kernel
theorem sub6_11 : sub6 [-2, 0] = true := by decide +kernel
theorem sub6_12 : sub6 [-2, 1] = true := by decide +kernel
theorem sub6_13 : sub6 [-2, 2] = true := by decide +kernel
theorem sub6_14 : sub6 [-2, 3] = true := by decide +kernel
theorem sub6_15 : sub6 [-1, -4] = true := by decide +kernel
theorem sub6_16 : sub6 [-1, -3] = true := by decide +kernel
theorem sub6_17 : sub6 [-1, -2] = true := by decide +kernel
theorem sub6_18 : sub6 [-1, -1] = true := by decide +kernel
theorem sub6_19 : sub6 [-1, 0] = true := by decide +kernel
theorem sub6_20 : sub6 [-1, 1] = true := by decide +kernel
theorem sub6_21 : sub6 [-1, 2] = true := by decide +kernel
theorem sub6_22 : sub6 [-1, 3] = true := by decide +kernel
theorem sub6_23 : sub6 [-1, 4] = true := by decide +kernel
theorem sub6_24 : sub6 [0, -5] = true := by decide +kernel
theorem sub6_25 : sub6 [0, -4] = true := by decide +kernel
theorem sub6_26 : sub6 [0, -3] = true := by decide +kernel
theorem sub6_27 : sub6 [0, -2] = true := by decide +kernel
theorem sub6_28 : sub6 [0, -1] = true := by decide +kernel
theorem sub6_29 : sub6 [0, 0] = true := by decide +kernel
theorem sub6_30 : sub6 [0, 1] = true := by decide +kernel
theorem sub6_31 : sub6 [0, 2] = true := by decide +kernel
theorem sb6_0 : ∀ q ∈ blk6_0, sub6 q = true := by
  unfold blk6_0
  exact List.forall_mem_cons.2 ⟨sub6_0, List.forall_mem_cons.2 ⟨sub6_1, List.forall_mem_cons.2 ⟨sub6_2, List.forall_mem_cons.2 ⟨sub6_3, List.forall_mem_cons.2 ⟨sub6_4, List.forall_mem_cons.2 ⟨sub6_5, List.forall_mem_cons.2 ⟨sub6_6, List.forall_mem_cons.2 ⟨sub6_7, List.forall_mem_cons.2 ⟨sub6_8, List.forall_mem_cons.2 ⟨sub6_9, List.forall_mem_cons.2 ⟨sub6_10, List.forall_mem_cons.2 ⟨sub6_11, List.forall_mem_cons.2 ⟨sub6_12, List.forall_mem_cons.2 ⟨sub6_13, List.forall_mem_cons.2 ⟨sub6_14, List.forall_mem_cons.2 ⟨sub6_15, List.forall_mem_cons.2 ⟨sub6_16, List.forall_mem_cons.2 ⟨sub6_17, List.forall_mem_cons.2 ⟨sub6_18, List.forall_mem_cons.2 ⟨sub6_19, List.forall_mem_cons.2 ⟨sub6_20, List.forall_mem_cons.2 ⟨sub6_21, List.forall_mem_cons.2 ⟨sub6_22, List.forall_mem_cons.2 ⟨sub6_23, List.forall_mem_cons.2 ⟨sub6_24, List.forall_mem_cons.2 ⟨sub6_25, List.forall_mem_cons.2 ⟨sub6_26, List.forall_mem_cons.2 ⟨sub6_27, List.forall_mem_cons.2 ⟨sub6_28, List.forall_mem_cons.2 ⟨sub6_29, List.forall_mem_cons.2 ⟨sub6_30, List.forall_mem_cons.2 ⟨sub6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_32 : sub6 [0, 3] = true := by decide +kernel
theorem sub6_33 : sub6 [0, 4] = true := by decide +kernel
theorem sub6_34 : sub6 [1, -5] = true := by decide +kernel
theorem sub6_35 : sub6 [1, -4] = true := by decide +kernel
theorem sub6_36 : sub6 [1, -3] = true := by decide +kernel
theorem sub6_37 : sub6 [1, -2] = true := by decide +kernel
theorem sub6_38 : sub6 [1, -1] = true := by decide +kernel
theorem sub6_39 : sub6 [1, 0] = true := by decide +kernel
theorem sub6_40 : sub6 [1, 1] = true := by decide +kernel
theorem sub6_41 : sub6 [1, 2] = true := by decide +kernel
theorem sub6_42 : sub6 [1, 3] = true := by decide +kernel
theorem sub6_43 : sub6 [2, -4] = true := by decide +kernel
theorem sub6_44 : sub6 [2, -3] = true := by decide +kernel
theorem sub6_45 : sub6 [2, -2] = true := by decide +kernel
theorem sub6_46 : sub6 [2, -1] = true := by decide +kernel
theorem sub6_47 : sub6 [2, 0] = true := by decide +kernel
theorem sub6_48 : sub6 [2, 1] = true := by decide +kernel
theorem sub6_49 : sub6 [2, 2] = true := by decide +kernel
theorem sub6_50 : sub6 [2, 3] = true := by decide +kernel
theorem sub6_51 : sub6 [3, -4] = true := by decide +kernel
theorem sub6_52 : sub6 [3, -3] = true := by decide +kernel
theorem sub6_53 : sub6 [3, -2] = true := by decide +kernel
theorem sub6_54 : sub6 [3, -1] = true := by decide +kernel
theorem sub6_55 : sub6 [3, 0] = true := by decide +kernel
theorem sub6_56 : sub6 [3, 1] = true := by decide +kernel
theorem sub6_57 : sub6 [3, 2] = true := by decide +kernel
theorem sb6_1 : ∀ q ∈ blk6_1, sub6 q = true := by
  unfold blk6_1
  exact List.forall_mem_cons.2 ⟨sub6_32, List.forall_mem_cons.2 ⟨sub6_33, List.forall_mem_cons.2 ⟨sub6_34, List.forall_mem_cons.2 ⟨sub6_35, List.forall_mem_cons.2 ⟨sub6_36, List.forall_mem_cons.2 ⟨sub6_37, List.forall_mem_cons.2 ⟨sub6_38, List.forall_mem_cons.2 ⟨sub6_39, List.forall_mem_cons.2 ⟨sub6_40, List.forall_mem_cons.2 ⟨sub6_41, List.forall_mem_cons.2 ⟨sub6_42, List.forall_mem_cons.2 ⟨sub6_43, List.forall_mem_cons.2 ⟨sub6_44, List.forall_mem_cons.2 ⟨sub6_45, List.forall_mem_cons.2 ⟨sub6_46, List.forall_mem_cons.2 ⟨sub6_47, List.forall_mem_cons.2 ⟨sub6_48, List.forall_mem_cons.2 ⟨sub6_49, List.forall_mem_cons.2 ⟨sub6_50, List.forall_mem_cons.2 ⟨sub6_51, List.forall_mem_cons.2 ⟨sub6_52, List.forall_mem_cons.2 ⟨sub6_53, List.forall_mem_cons.2 ⟨sub6_54, List.forall_mem_cons.2 ⟨sub6_55, List.forall_mem_cons.2 ⟨sub6_56, List.forall_mem_cons.2 ⟨sub6_57, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_0 : sub7 [-4] = true := by decide +kernel
theorem sub7_1 : sub7 [-3, -4] = true := by decide +kernel
theorem sub7_2 : sub7 [-3, -3] = true := by decide +kernel
theorem sub7_3 : sub7 [-3, -2] = true := by decide +kernel
theorem sub7_4 : sub7 [-3, -1] = true := by decide +kernel
theorem sub7_5 : sub7 [-3, 0] = true := by decide +kernel
theorem sub7_6 : sub7 [-3, 1] = true := by decide +kernel
theorem sub7_7 : sub7 [-3, 2] = true := by decide +kernel
theorem sub7_8 : sub7 [-2, -4] = true := by decide +kernel
theorem sub7_9 : sub7 [-2, -3] = true := by decide +kernel
theorem sub7_10 : sub7 [-2, -2] = true := by decide +kernel
theorem sub7_11 : sub7 [-2, -1] = true := by decide +kernel
theorem sub7_12 : sub7 [-2, 0] = true := by decide +kernel
theorem sub7_13 : sub7 [-2, 1] = true := by decide +kernel
theorem sub7_14 : sub7 [-2, 2] = true := by decide +kernel
theorem sub7_15 : sub7 [-2, 3] = true := by decide +kernel
theorem sub7_16 : sub7 [-1, -5] = true := by decide +kernel
theorem sub7_17 : sub7 [-1, -4] = true := by decide +kernel
theorem sub7_18 : sub7 [-1, -3] = true := by decide +kernel
theorem sub7_19 : sub7 [-1, -2] = true := by decide +kernel
theorem sub7_20 : sub7 [-1, -1] = true := by decide +kernel
theorem sub7_21 : sub7 [-1, 0] = true := by decide +kernel
theorem sub7_22 : sub7 [-1, 1] = true := by decide +kernel
theorem sub7_23 : sub7 [-1, 2] = true := by decide +kernel
theorem sub7_24 : sub7 [-1, 3] = true := by decide +kernel
theorem sub7_25 : sub7 [0, -4] = true := by decide +kernel
theorem sub7_26 : sub7 [0, -3] = true := by decide +kernel
theorem sub7_27 : sub7 [0, -2] = true := by decide +kernel
theorem sub7_28 : sub7 [0, -1] = true := by decide +kernel
theorem sub7_29 : sub7 [0, 0] = true := by decide +kernel
theorem sub7_30 : sub7 [0, 1] = true := by decide +kernel
theorem sub7_31 : sub7 [0, 2] = true := by decide +kernel
theorem sb7_0 : ∀ q ∈ blk7_0, sub7 q = true := by
  unfold blk7_0
  exact List.forall_mem_cons.2 ⟨sub7_0, List.forall_mem_cons.2 ⟨sub7_1, List.forall_mem_cons.2 ⟨sub7_2, List.forall_mem_cons.2 ⟨sub7_3, List.forall_mem_cons.2 ⟨sub7_4, List.forall_mem_cons.2 ⟨sub7_5, List.forall_mem_cons.2 ⟨sub7_6, List.forall_mem_cons.2 ⟨sub7_7, List.forall_mem_cons.2 ⟨sub7_8, List.forall_mem_cons.2 ⟨sub7_9, List.forall_mem_cons.2 ⟨sub7_10, List.forall_mem_cons.2 ⟨sub7_11, List.forall_mem_cons.2 ⟨sub7_12, List.forall_mem_cons.2 ⟨sub7_13, List.forall_mem_cons.2 ⟨sub7_14, List.forall_mem_cons.2 ⟨sub7_15, List.forall_mem_cons.2 ⟨sub7_16, List.forall_mem_cons.2 ⟨sub7_17, List.forall_mem_cons.2 ⟨sub7_18, List.forall_mem_cons.2 ⟨sub7_19, List.forall_mem_cons.2 ⟨sub7_20, List.forall_mem_cons.2 ⟨sub7_21, List.forall_mem_cons.2 ⟨sub7_22, List.forall_mem_cons.2 ⟨sub7_23, List.forall_mem_cons.2 ⟨sub7_24, List.forall_mem_cons.2 ⟨sub7_25, List.forall_mem_cons.2 ⟨sub7_26, List.forall_mem_cons.2 ⟨sub7_27, List.forall_mem_cons.2 ⟨sub7_28, List.forall_mem_cons.2 ⟨sub7_29, List.forall_mem_cons.2 ⟨sub7_30, List.forall_mem_cons.2 ⟨sub7_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_32 : sub7 [0, 3] = true := by decide +kernel
theorem sub7_33 : sub7 [1, -4] = true := by decide +kernel
theorem sub7_34 : sub7 [1, -3] = true := by decide +kernel
theorem sub7_35 : sub7 [1, -2] = true := by decide +kernel
theorem sub7_36 : sub7 [1, -1] = true := by decide +kernel
theorem sub7_37 : sub7 [1, 0] = true := by decide +kernel
theorem sub7_38 : sub7 [1, 1] = true := by decide +kernel
theorem sub7_39 : sub7 [1, 2] = true := by decide +kernel
theorem sub7_40 : sub7 [1, 3] = true := by decide +kernel
theorem sub7_41 : sub7 [1, 4] = true := by decide +kernel
theorem sub7_42 : sub7 [2, -4] = true := by decide +kernel
theorem sub7_43 : sub7 [2, -3] = true := by decide +kernel
theorem sub7_44 : sub7 [2, -2] = true := by decide +kernel
theorem sub7_45 : sub7 [2, -1] = true := by decide +kernel
theorem sub7_46 : sub7 [2, 0] = true := by decide +kernel
theorem sub7_47 : sub7 [2, 1] = true := by decide +kernel
theorem sub7_48 : sub7 [2, 2] = true := by decide +kernel
theorem sub7_49 : sub7 [2, 3] = true := by decide +kernel
theorem sub7_50 : sub7 [3, -3] = true := by decide +kernel
theorem sub7_51 : sub7 [3, -2] = true := by decide +kernel
theorem sub7_52 : sub7 [3, -1] = true := by decide +kernel
theorem sub7_53 : sub7 [3, 0] = true := by decide +kernel
theorem sub7_54 : sub7 [3, 1] = true := by decide +kernel
theorem sub7_55 : sub7 [3, 2] = true := by decide +kernel
theorem sub7_56 : sub7 [3, 3] = true := by decide +kernel
theorem sub7_57 : sub7 [4] = true := by decide +kernel
theorem sb7_1 : ∀ q ∈ blk7_1, sub7 q = true := by
  unfold blk7_1
  exact List.forall_mem_cons.2 ⟨sub7_32, List.forall_mem_cons.2 ⟨sub7_33, List.forall_mem_cons.2 ⟨sub7_34, List.forall_mem_cons.2 ⟨sub7_35, List.forall_mem_cons.2 ⟨sub7_36, List.forall_mem_cons.2 ⟨sub7_37, List.forall_mem_cons.2 ⟨sub7_38, List.forall_mem_cons.2 ⟨sub7_39, List.forall_mem_cons.2 ⟨sub7_40, List.forall_mem_cons.2 ⟨sub7_41, List.forall_mem_cons.2 ⟨sub7_42, List.forall_mem_cons.2 ⟨sub7_43, List.forall_mem_cons.2 ⟨sub7_44, List.forall_mem_cons.2 ⟨sub7_45, List.forall_mem_cons.2 ⟨sub7_46, List.forall_mem_cons.2 ⟨sub7_47, List.forall_mem_cons.2 ⟨sub7_48, List.forall_mem_cons.2 ⟨sub7_49, List.forall_mem_cons.2 ⟨sub7_50, List.forall_mem_cons.2 ⟨sub7_51, List.forall_mem_cons.2 ⟨sub7_52, List.forall_mem_cons.2 ⟨sub7_53, List.forall_mem_cons.2 ⟨sub7_54, List.forall_mem_cons.2 ⟨sub7_55, List.forall_mem_cons.2 ⟨sub7_56, List.forall_mem_cons.2 ⟨sub7_57, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C078
