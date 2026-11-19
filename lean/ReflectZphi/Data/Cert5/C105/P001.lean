import ReflectZphi.Data.Cert5.C105.Base

namespace ReflectZphi.Data.Cert5.C105
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub4_0 : sub4 [-4] = true := by decide +kernel
theorem sub4_1 : sub4 [-3, -3] = true := by decide +kernel
theorem sub4_2 : sub4 [-3, -2] = true := by decide +kernel
theorem sub4_3 : sub4 [-3, -1] = true := by decide +kernel
theorem sub4_4 : sub4 [-3, 0] = true := by decide +kernel
theorem sub4_5 : sub4 [-3, 1] = true := by decide +kernel
theorem sub4_6 : sub4 [-3, 2] = true := by decide +kernel
theorem sub4_7 : sub4 [-3, 3] = true := by decide +kernel
theorem sub4_8 : sub4 [-2, -4] = true := by decide +kernel
theorem sub4_9 : sub4 [-2, -3] = true := by decide +kernel
theorem sub4_10 : sub4 [-2, -2] = true := by decide +kernel
theorem sub4_11 : sub4 [-2, -1] = true := by decide +kernel
theorem sub4_12 : sub4 [-2, 0] = true := by decide +kernel
theorem sub4_13 : sub4 [-2, 1] = true := by decide +kernel
theorem sub4_14 : sub4 [-2, 2] = true := by decide +kernel
theorem sub4_15 : sub4 [-2, 3] = true := by decide +kernel
theorem sub4_16 : sub4 [-2, 4] = true := by decide +kernel
theorem sub4_17 : sub4 [-1, -5] = true := by decide +kernel
theorem sub4_18 : sub4 [-1, -4] = true := by decide +kernel
theorem sub4_19 : sub4 [-1, -3] = true := by decide +kernel
theorem sub4_20 : sub4 [-1, -2] = true := by decide +kernel
theorem sub4_21 : sub4 [-1, -1] = true := by decide +kernel
theorem sub4_22 : sub4 [-1, 0] = true := by decide +kernel
theorem sub4_23 : sub4 [-1, 1] = true := by decide +kernel
theorem sub4_24 : sub4 [-1, 2] = true := by decide +kernel
theorem sub4_25 : sub4 [-1, 3] = true := by decide +kernel
theorem sub4_26 : sub4 [-1, 4] = true := by decide +kernel
theorem sub4_27 : sub4 [0, -5] = true := by decide +kernel
theorem sub4_28 : sub4 [0, -4] = true := by decide +kernel
theorem sub4_29 : sub4 [0, -3] = true := by decide +kernel
theorem sub4_30 : sub4 [0, -2] = true := by decide +kernel
theorem sub4_31 : sub4 [0, -1] = true := by decide +kernel
theorem sb4_0 : ∀ q ∈ blk4_0, sub4 q = true := by
  unfold blk4_0
  exact List.forall_mem_cons.2 ⟨sub4_0, List.forall_mem_cons.2 ⟨sub4_1, List.forall_mem_cons.2 ⟨sub4_2, List.forall_mem_cons.2 ⟨sub4_3, List.forall_mem_cons.2 ⟨sub4_4, List.forall_mem_cons.2 ⟨sub4_5, List.forall_mem_cons.2 ⟨sub4_6, List.forall_mem_cons.2 ⟨sub4_7, List.forall_mem_cons.2 ⟨sub4_8, List.forall_mem_cons.2 ⟨sub4_9, List.forall_mem_cons.2 ⟨sub4_10, List.forall_mem_cons.2 ⟨sub4_11, List.forall_mem_cons.2 ⟨sub4_12, List.forall_mem_cons.2 ⟨sub4_13, List.forall_mem_cons.2 ⟨sub4_14, List.forall_mem_cons.2 ⟨sub4_15, List.forall_mem_cons.2 ⟨sub4_16, List.forall_mem_cons.2 ⟨sub4_17, List.forall_mem_cons.2 ⟨sub4_18, List.forall_mem_cons.2 ⟨sub4_19, List.forall_mem_cons.2 ⟨sub4_20, List.forall_mem_cons.2 ⟨sub4_21, List.forall_mem_cons.2 ⟨sub4_22, List.forall_mem_cons.2 ⟨sub4_23, List.forall_mem_cons.2 ⟨sub4_24, List.forall_mem_cons.2 ⟨sub4_25, List.forall_mem_cons.2 ⟨sub4_26, List.forall_mem_cons.2 ⟨sub4_27, List.forall_mem_cons.2 ⟨sub4_28, List.forall_mem_cons.2 ⟨sub4_29, List.forall_mem_cons.2 ⟨sub4_30, List.forall_mem_cons.2 ⟨sub4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_32 : sub4 [0, 0] = true := by decide +kernel
theorem sub4_33 : sub4 [0, 1] = true := by decide +kernel
theorem sub4_34 : sub4 [0, 2] = true := by decide +kernel
theorem sub4_35 : sub4 [0, 3] = true := by decide +kernel
theorem sub4_36 : sub4 [0, 4] = true := by decide +kernel
theorem sub4_37 : sub4 [1, -5] = true := by decide +kernel
theorem sub4_38 : sub4 [1, -4] = true := by decide +kernel
theorem sub4_39 : sub4 [1, -3] = true := by decide +kernel
theorem sub4_40 : sub4 [1, -2] = true := by decide +kernel
theorem sub4_41 : sub4 [1, -1] = true := by decide +kernel
theorem sub4_42 : sub4 [1, 0] = true := by decide +kernel
theorem sub4_43 : sub4 [1, 1] = true := by decide +kernel
theorem sub4_44 : sub4 [1, 2] = true := by decide +kernel
theorem sub4_45 : sub4 [1, 3] = true := by decide +kernel
theorem sub4_46 : sub4 [1, 4] = true := by decide +kernel
theorem sub4_47 : sub4 [2, -5] = true := by decide +kernel
theorem sub4_48 : sub4 [2, -4] = true := by decide +kernel
theorem sub4_49 : sub4 [2, -3] = true := by decide +kernel
theorem sub4_50 : sub4 [2, -2] = true := by decide +kernel
theorem sub4_51 : sub4 [2, -1] = true := by decide +kernel
theorem sub4_52 : sub4 [2, 0] = true := by decide +kernel
theorem sub4_53 : sub4 [2, 1] = true := by decide +kernel
theorem sub4_54 : sub4 [2, 2] = true := by decide +kernel
theorem sub4_55 : sub4 [2, 3] = true := by decide +kernel
theorem sub4_56 : sub4 [3, -4] = true := by decide +kernel
theorem sub4_57 : sub4 [3, -3] = true := by decide +kernel
theorem sub4_58 : sub4 [3, -2] = true := by decide +kernel
theorem sub4_59 : sub4 [3, -1] = true := by decide +kernel
theorem sub4_60 : sub4 [3, 0] = true := by decide +kernel
theorem sub4_61 : sub4 [3, 1] = true := by decide +kernel
theorem sub4_62 : sub4 [3, 2] = true := by decide +kernel
theorem sub4_63 : sub4 [4] = true := by decide +kernel
theorem sb4_1 : ∀ q ∈ blk4_1, sub4 q = true := by
  unfold blk4_1
  exact List.forall_mem_cons.2 ⟨sub4_32, List.forall_mem_cons.2 ⟨sub4_33, List.forall_mem_cons.2 ⟨sub4_34, List.forall_mem_cons.2 ⟨sub4_35, List.forall_mem_cons.2 ⟨sub4_36, List.forall_mem_cons.2 ⟨sub4_37, List.forall_mem_cons.2 ⟨sub4_38, List.forall_mem_cons.2 ⟨sub4_39, List.forall_mem_cons.2 ⟨sub4_40, List.forall_mem_cons.2 ⟨sub4_41, List.forall_mem_cons.2 ⟨sub4_42, List.forall_mem_cons.2 ⟨sub4_43, List.forall_mem_cons.2 ⟨sub4_44, List.forall_mem_cons.2 ⟨sub4_45, List.forall_mem_cons.2 ⟨sub4_46, List.forall_mem_cons.2 ⟨sub4_47, List.forall_mem_cons.2 ⟨sub4_48, List.forall_mem_cons.2 ⟨sub4_49, List.forall_mem_cons.2 ⟨sub4_50, List.forall_mem_cons.2 ⟨sub4_51, List.forall_mem_cons.2 ⟨sub4_52, List.forall_mem_cons.2 ⟨sub4_53, List.forall_mem_cons.2 ⟨sub4_54, List.forall_mem_cons.2 ⟨sub4_55, List.forall_mem_cons.2 ⟨sub4_56, List.forall_mem_cons.2 ⟨sub4_57, List.forall_mem_cons.2 ⟨sub4_58, List.forall_mem_cons.2 ⟨sub4_59, List.forall_mem_cons.2 ⟨sub4_60, List.forall_mem_cons.2 ⟨sub4_61, List.forall_mem_cons.2 ⟨sub4_62, List.forall_mem_cons.2 ⟨sub4_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_0 : sub5 [-4] = true := by decide +kernel
theorem sub5_1 : sub5 [-3, -4] = true := by decide +kernel
theorem sub5_2 : sub5 [-3, -3] = true := by decide +kernel
theorem sub5_3 : sub5 [-3, -2] = true := by decide +kernel
theorem sub5_4 : sub5 [-3, -1] = true := by decide +kernel
theorem sub5_5 : sub5 [-3, 0] = true := by decide +kernel
theorem sub5_6 : sub5 [-3, 1] = true := by decide +kernel
theorem sub5_7 : sub5 [-3, 2] = true := by decide +kernel
theorem sub5_8 : sub5 [-2, -5] = true := by decide +kernel
theorem sub5_9 : sub5 [-2, -4] = true := by decide +kernel
theorem sub5_10 : sub5 [-2, -3] = true := by decide +kernel
theorem sub5_11 : sub5 [-2, -2] = true := by decide +kernel
theorem sub5_12 : sub5 [-2, -1] = true := by decide +kernel
theorem sub5_13 : sub5 [-2, 0] = true := by decide +kernel
theorem sub5_14 : sub5 [-2, 1] = true := by decide +kernel
theorem sub5_15 : sub5 [-2, 2] = true := by decide +kernel
theorem sub5_16 : sub5 [-2, 3] = true := by decide +kernel
theorem sub5_17 : sub5 [-1, -5] = true := by decide +kernel
theorem sub5_18 : sub5 [-1, -4] = true := by decide +kernel
theorem sub5_19 : sub5 [-1, -3] = true := by decide +kernel
theorem sub5_20 : sub5 [-1, -2] = true := by decide +kernel
theorem sub5_21 : sub5 [-1, -1] = true := by decide +kernel
theorem sub5_22 : sub5 [-1, 0] = true := by decide +kernel
theorem sub5_23 : sub5 [-1, 1] = true := by decide +kernel
theorem sub5_24 : sub5 [-1, 2] = true := by decide +kernel
theorem sub5_25 : sub5 [-1, 3] = true := by decide +kernel
theorem sub5_26 : sub5 [-1, 4] = true := by decide +kernel
theorem sub5_27 : sub5 [0, -5] = true := by decide +kernel
theorem sub5_28 : sub5 [0, -4] = true := by decide +kernel
theorem sub5_29 : sub5 [0, -3] = true := by decide +kernel
theorem sub5_30 : sub5 [0, -2] = true := by decide +kernel
theorem sub5_31 : sub5 [0, -1] = true := by decide +kernel
theorem sb5_0 : ∀ q ∈ blk5_0, sub5 q = true := by
  unfold blk5_0
  exact List.forall_mem_cons.2 ⟨sub5_0, List.forall_mem_cons.2 ⟨sub5_1, List.forall_mem_cons.2 ⟨sub5_2, List.forall_mem_cons.2 ⟨sub5_3, List.forall_mem_cons.2 ⟨sub5_4, List.forall_mem_cons.2 ⟨sub5_5, List.forall_mem_cons.2 ⟨sub5_6, List.forall_mem_cons.2 ⟨sub5_7, List.forall_mem_cons.2 ⟨sub5_8, List.forall_mem_cons.2 ⟨sub5_9, List.forall_mem_cons.2 ⟨sub5_10, List.forall_mem_cons.2 ⟨sub5_11, List.forall_mem_cons.2 ⟨sub5_12, List.forall_mem_cons.2 ⟨sub5_13, List.forall_mem_cons.2 ⟨sub5_14, List.forall_mem_cons.2 ⟨sub5_15, List.forall_mem_cons.2 ⟨sub5_16, List.forall_mem_cons.2 ⟨sub5_17, List.forall_mem_cons.2 ⟨sub5_18, List.forall_mem_cons.2 ⟨sub5_19, List.forall_mem_cons.2 ⟨sub5_20, List.forall_mem_cons.2 ⟨sub5_21, List.forall_mem_cons.2 ⟨sub5_22, List.forall_mem_cons.2 ⟨sub5_23, List.forall_mem_cons.2 ⟨sub5_24, List.forall_mem_cons.2 ⟨sub5_25, List.forall_mem_cons.2 ⟨sub5_26, List.forall_mem_cons.2 ⟨sub5_27, List.forall_mem_cons.2 ⟨sub5_28, List.forall_mem_cons.2 ⟨sub5_29, List.forall_mem_cons.2 ⟨sub5_30, List.forall_mem_cons.2 ⟨sub5_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_32 : sub5 [0, 0] = true := by decide +kernel
theorem sub5_33 : sub5 [0, 1] = true := by decide +kernel
theorem sub5_34 : sub5 [0, 2] = true := by decide +kernel
theorem sub5_35 : sub5 [0, 3] = true := by decide +kernel
theorem sub5_36 : sub5 [0, 4] = true := by decide +kernel
theorem sub5_37 : sub5 [1, -5] = true := by decide +kernel
theorem sub5_38 : sub5 [1, -4] = true := by decide +kernel
theorem sub5_39 : sub5 [1, -3] = true := by decide +kernel
theorem sub5_40 : sub5 [1, -2] = true := by decide +kernel
theorem sub5_41 : sub5 [1, -1] = true := by decide +kernel
theorem sub5_42 : sub5 [1, 0] = true := by decide +kernel
theorem sub5_43 : sub5 [1, 1] = true := by decide +kernel
theorem sub5_44 : sub5 [1, 2] = true := by decide +kernel
theorem sub5_45 : sub5 [1, 3] = true := by decide +kernel
theorem sub5_46 : sub5 [1, 4] = true := by decide +kernel
theorem sub5_47 : sub5 [2, -4] = true := by decide +kernel
theorem sub5_48 : sub5 [2, -3] = true := by decide +kernel
theorem sub5_49 : sub5 [2, -2] = true := by decide +kernel
theorem sub5_50 : sub5 [2, -1] = true := by decide +kernel
theorem sub5_51 : sub5 [2, 0] = true := by decide +kernel
theorem sub5_52 : sub5 [2, 1] = true := by decide +kernel
theorem sub5_53 : sub5 [2, 2] = true := by decide +kernel
theorem sub5_54 : sub5 [2, 3] = true := by decide +kernel
theorem sub5_55 : sub5 [2, 4] = true := by decide +kernel
theorem sub5_56 : sub5 [3, -3] = true := by decide +kernel
theorem sub5_57 : sub5 [3, -2] = true := by decide +kernel
theorem sub5_58 : sub5 [3, -1] = true := by decide +kernel
theorem sub5_59 : sub5 [3, 0] = true := by decide +kernel
theorem sub5_60 : sub5 [3, 1] = true := by decide +kernel
theorem sub5_61 : sub5 [3, 2] = true := by decide +kernel
theorem sub5_62 : sub5 [3, 3] = true := by decide +kernel
theorem sub5_63 : sub5 [4] = true := by decide +kernel
theorem sb5_1 : ∀ q ∈ blk5_1, sub5 q = true := by
  unfold blk5_1
  exact List.forall_mem_cons.2 ⟨sub5_32, List.forall_mem_cons.2 ⟨sub5_33, List.forall_mem_cons.2 ⟨sub5_34, List.forall_mem_cons.2 ⟨sub5_35, List.forall_mem_cons.2 ⟨sub5_36, List.forall_mem_cons.2 ⟨sub5_37, List.forall_mem_cons.2 ⟨sub5_38, List.forall_mem_cons.2 ⟨sub5_39, List.forall_mem_cons.2 ⟨sub5_40, List.forall_mem_cons.2 ⟨sub5_41, List.forall_mem_cons.2 ⟨sub5_42, List.forall_mem_cons.2 ⟨sub5_43, List.forall_mem_cons.2 ⟨sub5_44, List.forall_mem_cons.2 ⟨sub5_45, List.forall_mem_cons.2 ⟨sub5_46, List.forall_mem_cons.2 ⟨sub5_47, List.forall_mem_cons.2 ⟨sub5_48, List.forall_mem_cons.2 ⟨sub5_49, List.forall_mem_cons.2 ⟨sub5_50, List.forall_mem_cons.2 ⟨sub5_51, List.forall_mem_cons.2 ⟨sub5_52, List.forall_mem_cons.2 ⟨sub5_53, List.forall_mem_cons.2 ⟨sub5_54, List.forall_mem_cons.2 ⟨sub5_55, List.forall_mem_cons.2 ⟨sub5_56, List.forall_mem_cons.2 ⟨sub5_57, List.forall_mem_cons.2 ⟨sub5_58, List.forall_mem_cons.2 ⟨sub5_59, List.forall_mem_cons.2 ⟨sub5_60, List.forall_mem_cons.2 ⟨sub5_61, List.forall_mem_cons.2 ⟨sub5_62, List.forall_mem_cons.2 ⟨sub5_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_0 : sub6 [-2, -2] = true := by decide +kernel
theorem sub6_1 : sub6 [-2, -1] = true := by decide +kernel
theorem sub6_2 : sub6 [-2, 0] = true := by decide +kernel
theorem sub6_3 : sub6 [-2, 1] = true := by decide +kernel
theorem sub6_4 : sub6 [-2, 2] = true := by decide +kernel
theorem sub6_5 : sub6 [-2, 3] = true := by decide +kernel
theorem sub6_6 : sub6 [-1, -3] = true := by decide +kernel
theorem sub6_7 : sub6 [-1, -2] = true := by decide +kernel
theorem sub6_8 : sub6 [-1, -1] = true := by decide +kernel
theorem sub6_9 : sub6 [-1, 0, -7] = true := by decide +kernel
theorem sub6_10 : sub6 [-1, 0, -6] = true := by decide +kernel
theorem sub6_11 : sub6 [-1, 0, -5] = true := by decide +kernel
theorem sub6_12 : sub6 [-1, 0, -4] = true := by decide +kernel
theorem sub6_13 : sub6 [-1, 0, -3] = true := by decide +kernel
theorem sub6_14 : sub6 [-1, 0, -2] = true := by decide +kernel
theorem sub6_15 : sub6 [-1, 0, -1] = true := by decide +kernel
theorem sub6_16 : sub6 [-1, 0, 0] = true := by decide +kernel
theorem sub6_17 : sub6 [-1, 0, 1] = true := by decide +kernel
theorem sub6_18 : sub6 [-1, 0, 2] = true := by decide +kernel
theorem sub6_19 : sub6 [-1, 0, 3] = true := by decide +kernel
theorem sub6_20 : sub6 [-1, 0, 4] = true := by decide +kernel
theorem sub6_21 : sub6 [-1, 0, 5] = true := by decide +kernel
theorem sub6_22 : sub6 [-1, 0, 6] = true := by decide +kernel
theorem sub6_23 : sub6 [-1, 0, 7] = true := by decide +kernel
theorem sub6_24 : sub6 [-1, 1, -7] = true := by decide +kernel
theorem sub6_25 : sub6 [-1, 1, -6] = true := by decide +kernel
theorem sub6_26 : sub6 [-1, 1, -5] = true := by decide +kernel
theorem sub6_27 : sub6 [-1, 1, -4] = true := by decide +kernel
theorem sub6_28 : sub6 [-1, 1, -3] = true := by decide +kernel
theorem sub6_29 : sub6 [-1, 1, -2] = true := by decide +kernel
theorem sub6_30 : sub6 [-1, 1, -1] = true := by decide +kernel
theorem sub6_31 : sub6 [-1, 1, 0] = true := by decide +kernel
theorem sb6_0 : ∀ q ∈ blk6_0, sub6 q = true := by
  unfold blk6_0
  exact List.forall_mem_cons.2 ⟨sub6_0, List.forall_mem_cons.2 ⟨sub6_1, List.forall_mem_cons.2 ⟨sub6_2, List.forall_mem_cons.2 ⟨sub6_3, List.forall_mem_cons.2 ⟨sub6_4, List.forall_mem_cons.2 ⟨sub6_5, List.forall_mem_cons.2 ⟨sub6_6, List.forall_mem_cons.2 ⟨sub6_7, List.forall_mem_cons.2 ⟨sub6_8, List.forall_mem_cons.2 ⟨sub6_9, List.forall_mem_cons.2 ⟨sub6_10, List.forall_mem_cons.2 ⟨sub6_11, List.forall_mem_cons.2 ⟨sub6_12, List.forall_mem_cons.2 ⟨sub6_13, List.forall_mem_cons.2 ⟨sub6_14, List.forall_mem_cons.2 ⟨sub6_15, List.forall_mem_cons.2 ⟨sub6_16, List.forall_mem_cons.2 ⟨sub6_17, List.forall_mem_cons.2 ⟨sub6_18, List.forall_mem_cons.2 ⟨sub6_19, List.forall_mem_cons.2 ⟨sub6_20, List.forall_mem_cons.2 ⟨sub6_21, List.forall_mem_cons.2 ⟨sub6_22, List.forall_mem_cons.2 ⟨sub6_23, List.forall_mem_cons.2 ⟨sub6_24, List.forall_mem_cons.2 ⟨sub6_25, List.forall_mem_cons.2 ⟨sub6_26, List.forall_mem_cons.2 ⟨sub6_27, List.forall_mem_cons.2 ⟨sub6_28, List.forall_mem_cons.2 ⟨sub6_29, List.forall_mem_cons.2 ⟨sub6_30, List.forall_mem_cons.2 ⟨sub6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C105
