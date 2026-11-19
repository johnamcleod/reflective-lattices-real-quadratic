import ReflectZphi.Data.Cert5.C074.Base

namespace ReflectZphi.Data.Cert5.C074
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub5_0 : sub5 [-3] = true := by decide +kernel
theorem sub5_1 : sub5 [-2, -3] = true := by decide +kernel
theorem sub5_2 : sub5 [-2, -2] = true := by decide +kernel
theorem sub5_3 : sub5 [-2, -1] = true := by decide +kernel
theorem sub5_4 : sub5 [-2, 0] = true := by decide +kernel
theorem sub5_5 : sub5 [-2, 1] = true := by decide +kernel
theorem sub5_6 : sub5 [-2, 2] = true := by decide +kernel
theorem sub5_7 : sub5 [-2, 3] = true := by decide +kernel
theorem sub5_8 : sub5 [-1, -4] = true := by decide +kernel
theorem sub5_9 : sub5 [-1, -3] = true := by decide +kernel
theorem sub5_10 : sub5 [-1, -2] = true := by decide +kernel
theorem sub5_11 : sub5 [-1, -1] = true := by decide +kernel
theorem sub5_12 : sub5 [-1, 0] = true := by decide +kernel
theorem sub5_13 : sub5 [-1, 1] = true := by decide +kernel
theorem sub5_14 : sub5 [-1, 2] = true := by decide +kernel
theorem sub5_15 : sub5 [-1, 3] = true := by decide +kernel
theorem sub5_16 : sub5 [0, -4] = true := by decide +kernel
theorem sub5_17 : sub5 [0, -3] = true := by decide +kernel
theorem sub5_18 : sub5 [0, -2] = true := by decide +kernel
theorem sub5_19 : sub5 [0, -1] = true := by decide +kernel
theorem sub5_20 : sub5 [0, 0] = true := by decide +kernel
theorem sub5_21 : sub5 [0, 1] = true := by decide +kernel
theorem sub5_22 : sub5 [0, 2] = true := by decide +kernel
theorem sub5_23 : sub5 [0, 3] = true := by decide +kernel
theorem sub5_24 : sub5 [1, -4] = true := by decide +kernel
theorem sub5_25 : sub5 [1, -3] = true := by decide +kernel
theorem sub5_26 : sub5 [1, -2] = true := by decide +kernel
theorem sub5_27 : sub5 [1, -1] = true := by decide +kernel
theorem sub5_28 : sub5 [1, 0] = true := by decide +kernel
theorem sub5_29 : sub5 [1, 1] = true := by decide +kernel
theorem sub5_30 : sub5 [1, 2] = true := by decide +kernel
theorem sub5_31 : sub5 [1, 3] = true := by decide +kernel
theorem sb5_0 : ∀ q ∈ blk5_0, sub5 q = true := by
  unfold blk5_0
  exact List.forall_mem_cons.2 ⟨sub5_0, List.forall_mem_cons.2 ⟨sub5_1, List.forall_mem_cons.2 ⟨sub5_2, List.forall_mem_cons.2 ⟨sub5_3, List.forall_mem_cons.2 ⟨sub5_4, List.forall_mem_cons.2 ⟨sub5_5, List.forall_mem_cons.2 ⟨sub5_6, List.forall_mem_cons.2 ⟨sub5_7, List.forall_mem_cons.2 ⟨sub5_8, List.forall_mem_cons.2 ⟨sub5_9, List.forall_mem_cons.2 ⟨sub5_10, List.forall_mem_cons.2 ⟨sub5_11, List.forall_mem_cons.2 ⟨sub5_12, List.forall_mem_cons.2 ⟨sub5_13, List.forall_mem_cons.2 ⟨sub5_14, List.forall_mem_cons.2 ⟨sub5_15, List.forall_mem_cons.2 ⟨sub5_16, List.forall_mem_cons.2 ⟨sub5_17, List.forall_mem_cons.2 ⟨sub5_18, List.forall_mem_cons.2 ⟨sub5_19, List.forall_mem_cons.2 ⟨sub5_20, List.forall_mem_cons.2 ⟨sub5_21, List.forall_mem_cons.2 ⟨sub5_22, List.forall_mem_cons.2 ⟨sub5_23, List.forall_mem_cons.2 ⟨sub5_24, List.forall_mem_cons.2 ⟨sub5_25, List.forall_mem_cons.2 ⟨sub5_26, List.forall_mem_cons.2 ⟨sub5_27, List.forall_mem_cons.2 ⟨sub5_28, List.forall_mem_cons.2 ⟨sub5_29, List.forall_mem_cons.2 ⟨sub5_30, List.forall_mem_cons.2 ⟨sub5_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_32 : sub5 [2, -4] = true := by decide +kernel
theorem sub5_33 : sub5 [2, -3] = true := by decide +kernel
theorem sub5_34 : sub5 [2, -2] = true := by decide +kernel
theorem sub5_35 : sub5 [2, -1] = true := by decide +kernel
theorem sub5_36 : sub5 [2, 0] = true := by decide +kernel
theorem sub5_37 : sub5 [2, 1] = true := by decide +kernel
theorem sub5_38 : sub5 [2, 2] = true := by decide +kernel
theorem sub5_39 : sub5 [3] = true := by decide +kernel
theorem sb5_1 : ∀ q ∈ blk5_1, sub5 q = true := by
  unfold blk5_1
  exact List.forall_mem_cons.2 ⟨sub5_32, List.forall_mem_cons.2 ⟨sub5_33, List.forall_mem_cons.2 ⟨sub5_34, List.forall_mem_cons.2 ⟨sub5_35, List.forall_mem_cons.2 ⟨sub5_36, List.forall_mem_cons.2 ⟨sub5_37, List.forall_mem_cons.2 ⟨sub5_38, List.forall_mem_cons.2 ⟨sub5_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_0 : sub6 [-4] = true := by decide +kernel
theorem sub6_1 : sub6 [-3, -4] = true := by decide +kernel
theorem sub6_2 : sub6 [-3, -3] = true := by decide +kernel
theorem sub6_3 : sub6 [-3, -2] = true := by decide +kernel
theorem sub6_4 : sub6 [-3, -1] = true := by decide +kernel
theorem sub6_5 : sub6 [-3, 0] = true := by decide +kernel
theorem sub6_6 : sub6 [-3, 1] = true := by decide +kernel
theorem sub6_7 : sub6 [-3, 2] = true := by decide +kernel
theorem sub6_8 : sub6 [-3, 3] = true := by decide +kernel
theorem sub6_9 : sub6 [-2, -5] = true := by decide +kernel
theorem sub6_10 : sub6 [-2, -4] = true := by decide +kernel
theorem sub6_11 : sub6 [-2, -3] = true := by decide +kernel
theorem sub6_12 : sub6 [-2, -2] = true := by decide +kernel
theorem sub6_13 : sub6 [-2, -1] = true := by decide +kernel
theorem sub6_14 : sub6 [-2, 0] = true := by decide +kernel
theorem sub6_15 : sub6 [-2, 1] = true := by decide +kernel
theorem sub6_16 : sub6 [-2, 2] = true := by decide +kernel
theorem sub6_17 : sub6 [-2, 3] = true := by decide +kernel
theorem sub6_18 : sub6 [-2, 4] = true := by decide +kernel
theorem sub6_19 : sub6 [-1, -5] = true := by decide +kernel
theorem sub6_20 : sub6 [-1, -4] = true := by decide +kernel
theorem sub6_21 : sub6 [-1, -3] = true := by decide +kernel
theorem sub6_22 : sub6 [-1, -2] = true := by decide +kernel
theorem sub6_23 : sub6 [-1, -1] = true := by decide +kernel
theorem sub6_24 : sub6 [-1, 0] = true := by decide +kernel
theorem sub6_25 : sub6 [-1, 1] = true := by decide +kernel
theorem sub6_26 : sub6 [-1, 2] = true := by decide +kernel
theorem sub6_27 : sub6 [-1, 3] = true := by decide +kernel
theorem sub6_28 : sub6 [-1, 4] = true := by decide +kernel
theorem sub6_29 : sub6 [0, -5] = true := by decide +kernel
theorem sub6_30 : sub6 [0, -4] = true := by decide +kernel
theorem sub6_31 : sub6 [0, -3] = true := by decide +kernel
theorem sb6_0 : ∀ q ∈ blk6_0, sub6 q = true := by
  unfold blk6_0
  exact List.forall_mem_cons.2 ⟨sub6_0, List.forall_mem_cons.2 ⟨sub6_1, List.forall_mem_cons.2 ⟨sub6_2, List.forall_mem_cons.2 ⟨sub6_3, List.forall_mem_cons.2 ⟨sub6_4, List.forall_mem_cons.2 ⟨sub6_5, List.forall_mem_cons.2 ⟨sub6_6, List.forall_mem_cons.2 ⟨sub6_7, List.forall_mem_cons.2 ⟨sub6_8, List.forall_mem_cons.2 ⟨sub6_9, List.forall_mem_cons.2 ⟨sub6_10, List.forall_mem_cons.2 ⟨sub6_11, List.forall_mem_cons.2 ⟨sub6_12, List.forall_mem_cons.2 ⟨sub6_13, List.forall_mem_cons.2 ⟨sub6_14, List.forall_mem_cons.2 ⟨sub6_15, List.forall_mem_cons.2 ⟨sub6_16, List.forall_mem_cons.2 ⟨sub6_17, List.forall_mem_cons.2 ⟨sub6_18, List.forall_mem_cons.2 ⟨sub6_19, List.forall_mem_cons.2 ⟨sub6_20, List.forall_mem_cons.2 ⟨sub6_21, List.forall_mem_cons.2 ⟨sub6_22, List.forall_mem_cons.2 ⟨sub6_23, List.forall_mem_cons.2 ⟨sub6_24, List.forall_mem_cons.2 ⟨sub6_25, List.forall_mem_cons.2 ⟨sub6_26, List.forall_mem_cons.2 ⟨sub6_27, List.forall_mem_cons.2 ⟨sub6_28, List.forall_mem_cons.2 ⟨sub6_29, List.forall_mem_cons.2 ⟨sub6_30, List.forall_mem_cons.2 ⟨sub6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_32 : sub6 [0, -2] = true := by decide +kernel
theorem sub6_33 : sub6 [0, -1] = true := by decide +kernel
theorem sub6_34 : sub6 [0, 0, -7] = true := by decide +kernel
theorem sub6_35 : sub6 [0, 0, -6] = true := by decide +kernel
theorem sub6_36 : sub6 [0, 0, -5] = true := by decide +kernel
theorem sub6_37 : sub6 [0, 0, -4] = true := by decide +kernel
theorem sub6_38 : sub6 [0, 0, -3] = true := by decide +kernel
theorem sub6_39 : sub6 [0, 0, -2] = true := by decide +kernel
theorem sub6_40 : sub6 [0, 0, -1] = true := by decide +kernel
theorem sub6_41 : sub6 [0, 0, 0] = true := by decide +kernel
theorem sub6_42 : sub6 [0, 0, 1] = true := by decide +kernel
theorem sub6_43 : sub6 [0, 0, 2] = true := by decide +kernel
theorem sub6_44 : sub6 [0, 0, 3] = true := by decide +kernel
theorem sub6_45 : sub6 [0, 0, 4] = true := by decide +kernel
theorem sub6_46 : sub6 [0, 0, 5] = true := by decide +kernel
theorem sub6_47 : sub6 [0, 0, 6] = true := by decide +kernel
theorem sub6_48 : sub6 [0, 1] = true := by decide +kernel
theorem sub6_49 : sub6 [0, 2] = true := by decide +kernel
theorem sub6_50 : sub6 [0, 3] = true := by decide +kernel
theorem sub6_51 : sub6 [0, 4] = true := by decide +kernel
theorem sub6_52 : sub6 [1, -5] = true := by decide +kernel
theorem sub6_53 : sub6 [1, -4] = true := by decide +kernel
theorem sub6_54 : sub6 [1, -3] = true := by decide +kernel
theorem sub6_55 : sub6 [1, -2] = true := by decide +kernel
theorem sub6_56 : sub6 [1, -1] = true := by decide +kernel
theorem sub6_57 : sub6 [1, 0] = true := by decide +kernel
theorem sub6_58 : sub6 [1, 1] = true := by decide +kernel
theorem sub6_59 : sub6 [1, 2] = true := by decide +kernel
theorem sub6_60 : sub6 [1, 3] = true := by decide +kernel
theorem sub6_61 : sub6 [1, 4] = true := by decide +kernel
theorem sub6_62 : sub6 [2, -5] = true := by decide +kernel
theorem sub6_63 : sub6 [2, -4] = true := by decide +kernel
theorem sb6_1 : ∀ q ∈ blk6_1, sub6 q = true := by
  unfold blk6_1
  exact List.forall_mem_cons.2 ⟨sub6_32, List.forall_mem_cons.2 ⟨sub6_33, List.forall_mem_cons.2 ⟨sub6_34, List.forall_mem_cons.2 ⟨sub6_35, List.forall_mem_cons.2 ⟨sub6_36, List.forall_mem_cons.2 ⟨sub6_37, List.forall_mem_cons.2 ⟨sub6_38, List.forall_mem_cons.2 ⟨sub6_39, List.forall_mem_cons.2 ⟨sub6_40, List.forall_mem_cons.2 ⟨sub6_41, List.forall_mem_cons.2 ⟨sub6_42, List.forall_mem_cons.2 ⟨sub6_43, List.forall_mem_cons.2 ⟨sub6_44, List.forall_mem_cons.2 ⟨sub6_45, List.forall_mem_cons.2 ⟨sub6_46, List.forall_mem_cons.2 ⟨sub6_47, List.forall_mem_cons.2 ⟨sub6_48, List.forall_mem_cons.2 ⟨sub6_49, List.forall_mem_cons.2 ⟨sub6_50, List.forall_mem_cons.2 ⟨sub6_51, List.forall_mem_cons.2 ⟨sub6_52, List.forall_mem_cons.2 ⟨sub6_53, List.forall_mem_cons.2 ⟨sub6_54, List.forall_mem_cons.2 ⟨sub6_55, List.forall_mem_cons.2 ⟨sub6_56, List.forall_mem_cons.2 ⟨sub6_57, List.forall_mem_cons.2 ⟨sub6_58, List.forall_mem_cons.2 ⟨sub6_59, List.forall_mem_cons.2 ⟨sub6_60, List.forall_mem_cons.2 ⟨sub6_61, List.forall_mem_cons.2 ⟨sub6_62, List.forall_mem_cons.2 ⟨sub6_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_64 : sub6 [2, -3] = true := by decide +kernel
theorem sub6_65 : sub6 [2, -2] = true := by decide +kernel
theorem sub6_66 : sub6 [2, -1] = true := by decide +kernel
theorem sub6_67 : sub6 [2, 0] = true := by decide +kernel
theorem sub6_68 : sub6 [2, 1] = true := by decide +kernel
theorem sub6_69 : sub6 [2, 2] = true := by decide +kernel
theorem sub6_70 : sub6 [2, 3] = true := by decide +kernel
theorem sub6_71 : sub6 [2, 4] = true := by decide +kernel
theorem sub6_72 : sub6 [3, -4] = true := by decide +kernel
theorem sub6_73 : sub6 [3, -3] = true := by decide +kernel
theorem sub6_74 : sub6 [3, -2] = true := by decide +kernel
theorem sub6_75 : sub6 [3, -1] = true := by decide +kernel
theorem sub6_76 : sub6 [3, 0] = true := by decide +kernel
theorem sub6_77 : sub6 [3, 1] = true := by decide +kernel
theorem sub6_78 : sub6 [3, 2] = true := by decide +kernel
theorem sub6_79 : sub6 [3, 3] = true := by decide +kernel
theorem sub6_80 : sub6 [4] = true := by decide +kernel
theorem sb6_2 : ∀ q ∈ blk6_2, sub6 q = true := by
  unfold blk6_2
  exact List.forall_mem_cons.2 ⟨sub6_64, List.forall_mem_cons.2 ⟨sub6_65, List.forall_mem_cons.2 ⟨sub6_66, List.forall_mem_cons.2 ⟨sub6_67, List.forall_mem_cons.2 ⟨sub6_68, List.forall_mem_cons.2 ⟨sub6_69, List.forall_mem_cons.2 ⟨sub6_70, List.forall_mem_cons.2 ⟨sub6_71, List.forall_mem_cons.2 ⟨sub6_72, List.forall_mem_cons.2 ⟨sub6_73, List.forall_mem_cons.2 ⟨sub6_74, List.forall_mem_cons.2 ⟨sub6_75, List.forall_mem_cons.2 ⟨sub6_76, List.forall_mem_cons.2 ⟨sub6_77, List.forall_mem_cons.2 ⟨sub6_78, List.forall_mem_cons.2 ⟨sub6_79, List.forall_mem_cons.2 ⟨sub6_80, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C074
