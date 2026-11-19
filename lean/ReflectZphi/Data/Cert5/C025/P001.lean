import ReflectZphi.Data.Cert5.C025.Base

namespace ReflectZphi.Data.Cert5.C025
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub2_32 : sub2 [-1, -1] = true := by decide +kernel
theorem sub2_33 : sub2 [-1, 0] = true := by decide +kernel
theorem sub2_34 : sub2 [-1, 1] = true := by decide +kernel
theorem sub2_35 : sub2 [-1, 2] = true := by decide +kernel
theorem sub2_36 : sub2 [-1, 3] = true := by decide +kernel
theorem sub2_37 : sub2 [-1, 4] = true := by decide +kernel
theorem sub2_38 : sub2 [0, -6] = true := by decide +kernel
theorem sub2_39 : sub2 [0, -5] = true := by decide +kernel
theorem sub2_40 : sub2 [0, -4] = true := by decide +kernel
theorem sub2_41 : sub2 [0, -3] = true := by decide +kernel
theorem sub2_42 : sub2 [0, -2] = true := by decide +kernel
theorem sub2_43 : sub2 [0, -1] = true := by decide +kernel
theorem sub2_44 : sub2 [0, 0] = true := by decide +kernel
theorem sub2_45 : sub2 [0, 1] = true := by decide +kernel
theorem sub2_46 : sub2 [0, 2] = true := by decide +kernel
theorem sub2_47 : sub2 [0, 3] = true := by decide +kernel
theorem sub2_48 : sub2 [0, 4] = true := by decide +kernel
theorem sub2_49 : sub2 [0, 5] = true := by decide +kernel
theorem sub2_50 : sub2 [1, -5] = true := by decide +kernel
theorem sub2_51 : sub2 [1, -4] = true := by decide +kernel
theorem sub2_52 : sub2 [1, -3] = true := by decide +kernel
theorem sub2_53 : sub2 [1, -2] = true := by decide +kernel
theorem sub2_54 : sub2 [1, -1] = true := by decide +kernel
theorem sub2_55 : sub2 [1, 0] = true := by decide +kernel
theorem sub2_56 : sub2 [1, 1] = true := by decide +kernel
theorem sub2_57 : sub2 [1, 2] = true := by decide +kernel
theorem sub2_58 : sub2 [1, 3] = true := by decide +kernel
theorem sub2_59 : sub2 [1, 4] = true := by decide +kernel
theorem sub2_60 : sub2 [1, 5] = true := by decide +kernel
theorem sub2_61 : sub2 [2, -5] = true := by decide +kernel
theorem sub2_62 : sub2 [2, -4] = true := by decide +kernel
theorem sub2_63 : sub2 [2, -3] = true := by decide +kernel
theorem sb2_1 : ∀ q ∈ blk2_1, sub2 q = true := by
  unfold blk2_1
  exact List.forall_mem_cons.2 ⟨sub2_32, List.forall_mem_cons.2 ⟨sub2_33, List.forall_mem_cons.2 ⟨sub2_34, List.forall_mem_cons.2 ⟨sub2_35, List.forall_mem_cons.2 ⟨sub2_36, List.forall_mem_cons.2 ⟨sub2_37, List.forall_mem_cons.2 ⟨sub2_38, List.forall_mem_cons.2 ⟨sub2_39, List.forall_mem_cons.2 ⟨sub2_40, List.forall_mem_cons.2 ⟨sub2_41, List.forall_mem_cons.2 ⟨sub2_42, List.forall_mem_cons.2 ⟨sub2_43, List.forall_mem_cons.2 ⟨sub2_44, List.forall_mem_cons.2 ⟨sub2_45, List.forall_mem_cons.2 ⟨sub2_46, List.forall_mem_cons.2 ⟨sub2_47, List.forall_mem_cons.2 ⟨sub2_48, List.forall_mem_cons.2 ⟨sub2_49, List.forall_mem_cons.2 ⟨sub2_50, List.forall_mem_cons.2 ⟨sub2_51, List.forall_mem_cons.2 ⟨sub2_52, List.forall_mem_cons.2 ⟨sub2_53, List.forall_mem_cons.2 ⟨sub2_54, List.forall_mem_cons.2 ⟨sub2_55, List.forall_mem_cons.2 ⟨sub2_56, List.forall_mem_cons.2 ⟨sub2_57, List.forall_mem_cons.2 ⟨sub2_58, List.forall_mem_cons.2 ⟨sub2_59, List.forall_mem_cons.2 ⟨sub2_60, List.forall_mem_cons.2 ⟨sub2_61, List.forall_mem_cons.2 ⟨sub2_62, List.forall_mem_cons.2 ⟨sub2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_64 : sub2 [2, -2] = true := by decide +kernel
theorem sub2_65 : sub2 [2, -1] = true := by decide +kernel
theorem sub2_66 : sub2 [2, 0] = true := by decide +kernel
theorem sub2_67 : sub2 [2, 1] = true := by decide +kernel
theorem sub2_68 : sub2 [2, 2] = true := by decide +kernel
theorem sub2_69 : sub2 [2, 3] = true := by decide +kernel
theorem sub2_70 : sub2 [2, 4] = true := by decide +kernel
theorem sub2_71 : sub2 [2, 5] = true := by decide +kernel
theorem sub2_72 : sub2 [3, -3] = true := by decide +kernel
theorem sub2_73 : sub2 [3, -2] = true := by decide +kernel
theorem sub2_74 : sub2 [3, -1] = true := by decide +kernel
theorem sub2_75 : sub2 [3, 0] = true := by decide +kernel
theorem sub2_76 : sub2 [3, 1] = true := by decide +kernel
theorem sub2_77 : sub2 [3, 2] = true := by decide +kernel
theorem sub2_78 : sub2 [3, 3] = true := by decide +kernel
theorem sub2_79 : sub2 [3, 4] = true := by decide +kernel
theorem sub2_80 : sub2 [3, 5] = true := by decide +kernel
theorem sub2_81 : sub2 [4, -2] = true := by decide +kernel
theorem sub2_82 : sub2 [4, -1] = true := by decide +kernel
theorem sub2_83 : sub2 [4, 0] = true := by decide +kernel
theorem sub2_84 : sub2 [4, 1] = true := by decide +kernel
theorem sub2_85 : sub2 [4, 2] = true := by decide +kernel
theorem sub2_86 : sub2 [4, 3] = true := by decide +kernel
theorem sub2_87 : sub2 [4, 4] = true := by decide +kernel
theorem sb2_2 : ∀ q ∈ blk2_2, sub2 q = true := by
  unfold blk2_2
  exact List.forall_mem_cons.2 ⟨sub2_64, List.forall_mem_cons.2 ⟨sub2_65, List.forall_mem_cons.2 ⟨sub2_66, List.forall_mem_cons.2 ⟨sub2_67, List.forall_mem_cons.2 ⟨sub2_68, List.forall_mem_cons.2 ⟨sub2_69, List.forall_mem_cons.2 ⟨sub2_70, List.forall_mem_cons.2 ⟨sub2_71, List.forall_mem_cons.2 ⟨sub2_72, List.forall_mem_cons.2 ⟨sub2_73, List.forall_mem_cons.2 ⟨sub2_74, List.forall_mem_cons.2 ⟨sub2_75, List.forall_mem_cons.2 ⟨sub2_76, List.forall_mem_cons.2 ⟨sub2_77, List.forall_mem_cons.2 ⟨sub2_78, List.forall_mem_cons.2 ⟨sub2_79, List.forall_mem_cons.2 ⟨sub2_80, List.forall_mem_cons.2 ⟨sub2_81, List.forall_mem_cons.2 ⟨sub2_82, List.forall_mem_cons.2 ⟨sub2_83, List.forall_mem_cons.2 ⟨sub2_84, List.forall_mem_cons.2 ⟨sub2_85, List.forall_mem_cons.2 ⟨sub2_86, List.forall_mem_cons.2 ⟨sub2_87, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_0 : sub3 [-5] = true := by decide +kernel
theorem sub3_1 : sub3 [-4, -5] = true := by decide +kernel
theorem sub3_2 : sub3 [-4, -4] = true := by decide +kernel
theorem sub3_3 : sub3 [-4, -3] = true := by decide +kernel
theorem sub3_4 : sub3 [-4, -2] = true := by decide +kernel
theorem sub3_5 : sub3 [-4, -1] = true := by decide +kernel
theorem sub3_6 : sub3 [-4, 0] = true := by decide +kernel
theorem sub3_7 : sub3 [-4, 1] = true := by decide +kernel
theorem sub3_8 : sub3 [-4, 2] = true := by decide +kernel
theorem sub3_9 : sub3 [-4, 3] = true := by decide +kernel
theorem sub3_10 : sub3 [-4, 4] = true := by decide +kernel
theorem sub3_11 : sub3 [-3, -5] = true := by decide +kernel
theorem sub3_12 : sub3 [-3, -4] = true := by decide +kernel
theorem sub3_13 : sub3 [-3, -3] = true := by decide +kernel
theorem sub3_14 : sub3 [-3, -2] = true := by decide +kernel
theorem sub3_15 : sub3 [-3, -1] = true := by decide +kernel
theorem sub3_16 : sub3 [-3, 0] = true := by decide +kernel
theorem sub3_17 : sub3 [-3, 1] = true := by decide +kernel
theorem sub3_18 : sub3 [-3, 2] = true := by decide +kernel
theorem sub3_19 : sub3 [-3, 3] = true := by decide +kernel
theorem sub3_20 : sub3 [-3, 4] = true := by decide +kernel
theorem sub3_21 : sub3 [-3, 5] = true := by decide +kernel
theorem sub3_22 : sub3 [-2, -6] = true := by decide +kernel
theorem sub3_23 : sub3 [-2, -5] = true := by decide +kernel
theorem sub3_24 : sub3 [-2, -4] = true := by decide +kernel
theorem sub3_25 : sub3 [-2, -3] = true := by decide +kernel
theorem sub3_26 : sub3 [-2, -2] = true := by decide +kernel
theorem sub3_27 : sub3 [-2, -1] = true := by decide +kernel
theorem sub3_28 : sub3 [-2, 0] = true := by decide +kernel
theorem sub3_29 : sub3 [-2, 1] = true := by decide +kernel
theorem sub3_30 : sub3 [-2, 2] = true := by decide +kernel
theorem sub3_31 : sub3 [-2, 3] = true := by decide +kernel
theorem sb3_0 : ∀ q ∈ blk3_0, sub3 q = true := by
  unfold blk3_0
  exact List.forall_mem_cons.2 ⟨sub3_0, List.forall_mem_cons.2 ⟨sub3_1, List.forall_mem_cons.2 ⟨sub3_2, List.forall_mem_cons.2 ⟨sub3_3, List.forall_mem_cons.2 ⟨sub3_4, List.forall_mem_cons.2 ⟨sub3_5, List.forall_mem_cons.2 ⟨sub3_6, List.forall_mem_cons.2 ⟨sub3_7, List.forall_mem_cons.2 ⟨sub3_8, List.forall_mem_cons.2 ⟨sub3_9, List.forall_mem_cons.2 ⟨sub3_10, List.forall_mem_cons.2 ⟨sub3_11, List.forall_mem_cons.2 ⟨sub3_12, List.forall_mem_cons.2 ⟨sub3_13, List.forall_mem_cons.2 ⟨sub3_14, List.forall_mem_cons.2 ⟨sub3_15, List.forall_mem_cons.2 ⟨sub3_16, List.forall_mem_cons.2 ⟨sub3_17, List.forall_mem_cons.2 ⟨sub3_18, List.forall_mem_cons.2 ⟨sub3_19, List.forall_mem_cons.2 ⟨sub3_20, List.forall_mem_cons.2 ⟨sub3_21, List.forall_mem_cons.2 ⟨sub3_22, List.forall_mem_cons.2 ⟨sub3_23, List.forall_mem_cons.2 ⟨sub3_24, List.forall_mem_cons.2 ⟨sub3_25, List.forall_mem_cons.2 ⟨sub3_26, List.forall_mem_cons.2 ⟨sub3_27, List.forall_mem_cons.2 ⟨sub3_28, List.forall_mem_cons.2 ⟨sub3_29, List.forall_mem_cons.2 ⟨sub3_30, List.forall_mem_cons.2 ⟨sub3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub3_32 : sub3 [-2, 4] = true := by decide +kernel
theorem sub3_33 : sub3 [-2, 5] = true := by decide +kernel
theorem sub3_34 : sub3 [-1, -6] = true := by decide +kernel
theorem sub3_35 : sub3 [-1, -5] = true := by decide +kernel
theorem sub3_36 : sub3 [-1, -4] = true := by decide +kernel
theorem sub3_37 : sub3 [-1, -3] = true := by decide +kernel
theorem sub3_38 : sub3 [-1, -2] = true := by decide +kernel
theorem sub3_39 : sub3 [-1, -1] = true := by decide +kernel
theorem sub3_40 : sub3 [-1, 0] = true := by decide +kernel
theorem sub3_41 : sub3 [-1, 1] = true := by decide +kernel
theorem sub3_42 : sub3 [-1, 2] = true := by decide +kernel
theorem sub3_43 : sub3 [-1, 3] = true := by decide +kernel
theorem sub3_44 : sub3 [-1, 4] = true := by decide +kernel
theorem sub3_45 : sub3 [-1, 5] = true := by decide +kernel
theorem sub3_46 : sub3 [0, -6] = true := by decide +kernel
theorem sub3_47 : sub3 [0, -5] = true := by decide +kernel
theorem sub3_48 : sub3 [0, -4] = true := by decide +kernel
theorem sub3_49 : sub3 [0, -3] = true := by decide +kernel
theorem sub3_50 : sub3 [0, -2] = true := by decide +kernel
theorem sub3_51 : sub3 [0, -1] = true := by decide +kernel
theorem sub3_52 : sub3 [0, 0] = true := by decide +kernel
theorem sub3_53 : sub3 [0, 1] = true := by decide +kernel
theorem sub3_54 : sub3 [0, 2] = true := by decide +kernel
theorem sub3_55 : sub3 [0, 3] = true := by decide +kernel
theorem sub3_56 : sub3 [0, 4] = true := by decide +kernel
theorem sub3_57 : sub3 [0, 5] = true := by decide +kernel
theorem sub3_58 : sub3 [1, -6] = true := by decide +kernel
theorem sub3_59 : sub3 [1, -5] = true := by decide +kernel
theorem sub3_60 : sub3 [1, -4] = true := by decide +kernel
theorem sub3_61 : sub3 [1, -3] = true := by decide +kernel
theorem sub3_62 : sub3 [1, -2] = true := by decide +kernel
theorem sub3_63 : sub3 [1, -1] = true := by decide +kernel
theorem sb3_1 : ∀ q ∈ blk3_1, sub3 q = true := by
  unfold blk3_1
  exact List.forall_mem_cons.2 ⟨sub3_32, List.forall_mem_cons.2 ⟨sub3_33, List.forall_mem_cons.2 ⟨sub3_34, List.forall_mem_cons.2 ⟨sub3_35, List.forall_mem_cons.2 ⟨sub3_36, List.forall_mem_cons.2 ⟨sub3_37, List.forall_mem_cons.2 ⟨sub3_38, List.forall_mem_cons.2 ⟨sub3_39, List.forall_mem_cons.2 ⟨sub3_40, List.forall_mem_cons.2 ⟨sub3_41, List.forall_mem_cons.2 ⟨sub3_42, List.forall_mem_cons.2 ⟨sub3_43, List.forall_mem_cons.2 ⟨sub3_44, List.forall_mem_cons.2 ⟨sub3_45, List.forall_mem_cons.2 ⟨sub3_46, List.forall_mem_cons.2 ⟨sub3_47, List.forall_mem_cons.2 ⟨sub3_48, List.forall_mem_cons.2 ⟨sub3_49, List.forall_mem_cons.2 ⟨sub3_50, List.forall_mem_cons.2 ⟨sub3_51, List.forall_mem_cons.2 ⟨sub3_52, List.forall_mem_cons.2 ⟨sub3_53, List.forall_mem_cons.2 ⟨sub3_54, List.forall_mem_cons.2 ⟨sub3_55, List.forall_mem_cons.2 ⟨sub3_56, List.forall_mem_cons.2 ⟨sub3_57, List.forall_mem_cons.2 ⟨sub3_58, List.forall_mem_cons.2 ⟨sub3_59, List.forall_mem_cons.2 ⟨sub3_60, List.forall_mem_cons.2 ⟨sub3_61, List.forall_mem_cons.2 ⟨sub3_62, List.forall_mem_cons.2 ⟨sub3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C025
