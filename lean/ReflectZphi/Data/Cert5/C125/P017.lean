import ReflectZphi.Data.Cert5.C125.Base

namespace ReflectZphi.Data.Cert5.C125
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub11_0 : sub11 [-4, -4] = true := by decide +kernel
theorem sub11_1 : sub11 [-4, -3] = true := by decide +kernel
theorem sub11_2 : sub11 [-4, -2] = true := by decide +kernel
theorem sub11_3 : sub11 [-4, -1] = true := by decide +kernel
theorem sub11_4 : sub11 [-4, 0] = true := by decide +kernel
theorem sub11_5 : sub11 [-4, 1] = true := by decide +kernel
theorem sub11_6 : sub11 [-4, 2] = true := by decide +kernel
theorem sub11_7 : sub11 [-4, 3] = true := by decide +kernel
theorem sub11_8 : sub11 [-3, -5] = true := by decide +kernel
theorem sub11_9 : sub11 [-3, -4] = true := by decide +kernel
theorem sub11_10 : sub11 [-3, -3] = true := by decide +kernel
theorem sub11_11 : sub11 [-3, -2] = true := by decide +kernel
theorem sub11_12 : sub11 [-3, -1] = true := by decide +kernel
theorem sub11_13 : sub11 [-3, 0] = true := by decide +kernel
theorem sub11_14 : sub11 [-3, 1] = true := by decide +kernel
theorem sub11_15 : sub11 [-3, 2] = true := by decide +kernel
theorem sub11_16 : sub11 [-3, 3] = true := by decide +kernel
theorem sub11_17 : sub11 [-3, 4] = true := by decide +kernel
theorem sub11_18 : sub11 [-2, -6] = true := by decide +kernel
theorem sub11_19 : sub11 [-2, -5] = true := by decide +kernel
theorem sub11_20 : sub11 [-2, -4] = true := by decide +kernel
theorem sub11_21 : sub11 [-2, -3] = true := by decide +kernel
theorem sub11_22 : sub11 [-2, -2] = true := by decide +kernel
theorem sub11_23 : sub11 [-2, -1] = true := by decide +kernel
theorem sub11_24 : sub11 [-2, 0] = true := by decide +kernel
theorem sub11_25 : sub11 [-2, 1] = true := by decide +kernel
theorem sub11_26 : sub11 [-2, 2] = true := by decide +kernel
theorem sub11_27 : sub11 [-2, 3] = true := by decide +kernel
theorem sub11_28 : sub11 [-2, 4] = true := by decide +kernel
theorem sub11_29 : sub11 [-2, 5] = true := by decide +kernel
theorem sub11_30 : sub11 [-1, -6] = true := by decide +kernel
theorem sub11_31 : sub11 [-1, -5] = true := by decide +kernel
theorem sb11_0 : ∀ q ∈ blk11_0, sub11 q = true := by
  unfold blk11_0
  exact List.forall_mem_cons.2 ⟨sub11_0, List.forall_mem_cons.2 ⟨sub11_1, List.forall_mem_cons.2 ⟨sub11_2, List.forall_mem_cons.2 ⟨sub11_3, List.forall_mem_cons.2 ⟨sub11_4, List.forall_mem_cons.2 ⟨sub11_5, List.forall_mem_cons.2 ⟨sub11_6, List.forall_mem_cons.2 ⟨sub11_7, List.forall_mem_cons.2 ⟨sub11_8, List.forall_mem_cons.2 ⟨sub11_9, List.forall_mem_cons.2 ⟨sub11_10, List.forall_mem_cons.2 ⟨sub11_11, List.forall_mem_cons.2 ⟨sub11_12, List.forall_mem_cons.2 ⟨sub11_13, List.forall_mem_cons.2 ⟨sub11_14, List.forall_mem_cons.2 ⟨sub11_15, List.forall_mem_cons.2 ⟨sub11_16, List.forall_mem_cons.2 ⟨sub11_17, List.forall_mem_cons.2 ⟨sub11_18, List.forall_mem_cons.2 ⟨sub11_19, List.forall_mem_cons.2 ⟨sub11_20, List.forall_mem_cons.2 ⟨sub11_21, List.forall_mem_cons.2 ⟨sub11_22, List.forall_mem_cons.2 ⟨sub11_23, List.forall_mem_cons.2 ⟨sub11_24, List.forall_mem_cons.2 ⟨sub11_25, List.forall_mem_cons.2 ⟨sub11_26, List.forall_mem_cons.2 ⟨sub11_27, List.forall_mem_cons.2 ⟨sub11_28, List.forall_mem_cons.2 ⟨sub11_29, List.forall_mem_cons.2 ⟨sub11_30, List.forall_mem_cons.2 ⟨sub11_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub11_32 : sub11 [-1, -4] = true := by decide +kernel
theorem sub11_33 : sub11 [-1, -3] = true := by decide +kernel
theorem sub11_34 : sub11 [-1, -2] = true := by decide +kernel
theorem sub11_35 : sub11 [-1, -1] = true := by decide +kernel
theorem sub11_36 : sub11 [-1, 0] = true := by decide +kernel
theorem sub11_37 : sub11 [-1, 1] = true := by decide +kernel
theorem sub11_38 : sub11 [-1, 2] = true := by decide +kernel
theorem sub11_39 : sub11 [-1, 3] = true := by decide +kernel
theorem sub11_40 : sub11 [-1, 4] = true := by decide +kernel
theorem sub11_41 : sub11 [-1, 5] = true := by decide +kernel
theorem sub11_42 : sub11 [0, -6] = true := by decide +kernel
theorem sub11_43 : sub11 [0, -5] = true := by decide +kernel
theorem sub11_44 : sub11 [0, -4] = true := by decide +kernel
theorem sub11_45 : sub11 [0, -3] = true := by decide +kernel
theorem sub11_46 : sub11 [0, -2] = true := by decide +kernel
theorem sub11_47 : sub11 [0, -1] = true := by decide +kernel
theorem sub11_48 : sub11 [0, 0] = true := by decide +kernel
theorem sub11_49 : sub11 [0, 1] = true := by decide +kernel
theorem sub11_50 : sub11 [0, 2] = true := by decide +kernel
theorem sub11_51 : sub11 [0, 3] = true := by decide +kernel
theorem sub11_52 : sub11 [0, 4] = true := by decide +kernel
theorem sub11_53 : sub11 [0, 5] = true := by decide +kernel
theorem sub11_54 : sub11 [1, -6] = true := by decide +kernel
theorem sub11_55 : sub11 [1, -5] = true := by decide +kernel
theorem sub11_56 : sub11 [1, -4] = true := by decide +kernel
theorem sub11_57 : sub11 [1, -3] = true := by decide +kernel
theorem sub11_58 : sub11 [1, -2] = true := by decide +kernel
theorem sub11_59 : sub11 [1, -1] = true := by decide +kernel
theorem sub11_60 : sub11 [1, 0] = true := by decide +kernel
theorem sub11_61 : sub11 [1, 1] = true := by decide +kernel
theorem sub11_62 : sub11 [1, 2] = true := by decide +kernel
theorem sub11_63 : sub11 [1, 3] = true := by decide +kernel
theorem sb11_1 : ∀ q ∈ blk11_1, sub11 q = true := by
  unfold blk11_1
  exact List.forall_mem_cons.2 ⟨sub11_32, List.forall_mem_cons.2 ⟨sub11_33, List.forall_mem_cons.2 ⟨sub11_34, List.forall_mem_cons.2 ⟨sub11_35, List.forall_mem_cons.2 ⟨sub11_36, List.forall_mem_cons.2 ⟨sub11_37, List.forall_mem_cons.2 ⟨sub11_38, List.forall_mem_cons.2 ⟨sub11_39, List.forall_mem_cons.2 ⟨sub11_40, List.forall_mem_cons.2 ⟨sub11_41, List.forall_mem_cons.2 ⟨sub11_42, List.forall_mem_cons.2 ⟨sub11_43, List.forall_mem_cons.2 ⟨sub11_44, List.forall_mem_cons.2 ⟨sub11_45, List.forall_mem_cons.2 ⟨sub11_46, List.forall_mem_cons.2 ⟨sub11_47, List.forall_mem_cons.2 ⟨sub11_48, List.forall_mem_cons.2 ⟨sub11_49, List.forall_mem_cons.2 ⟨sub11_50, List.forall_mem_cons.2 ⟨sub11_51, List.forall_mem_cons.2 ⟨sub11_52, List.forall_mem_cons.2 ⟨sub11_53, List.forall_mem_cons.2 ⟨sub11_54, List.forall_mem_cons.2 ⟨sub11_55, List.forall_mem_cons.2 ⟨sub11_56, List.forall_mem_cons.2 ⟨sub11_57, List.forall_mem_cons.2 ⟨sub11_58, List.forall_mem_cons.2 ⟨sub11_59, List.forall_mem_cons.2 ⟨sub11_60, List.forall_mem_cons.2 ⟨sub11_61, List.forall_mem_cons.2 ⟨sub11_62, List.forall_mem_cons.2 ⟨sub11_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub11_64 : sub11 [1, 4] = true := by decide +kernel
theorem sub11_65 : sub11 [1, 5] = true := by decide +kernel
theorem sub11_66 : sub11 [2, -6] = true := by decide +kernel
theorem sub11_67 : sub11 [2, -5] = true := by decide +kernel
theorem sub11_68 : sub11 [2, -4] = true := by decide +kernel
theorem sub11_69 : sub11 [2, -3] = true := by decide +kernel
theorem sub11_70 : sub11 [2, -2] = true := by decide +kernel
theorem sub11_71 : sub11 [2, -1] = true := by decide +kernel
theorem sub11_72 : sub11 [2, 0] = true := by decide +kernel
theorem sub11_73 : sub11 [2, 1] = true := by decide +kernel
theorem sub11_74 : sub11 [2, 2] = true := by decide +kernel
theorem sub11_75 : sub11 [2, 3] = true := by decide +kernel
theorem sub11_76 : sub11 [2, 4] = true := by decide +kernel
theorem sub11_77 : sub11 [2, 5] = true := by decide +kernel
theorem sub11_78 : sub11 [3, -5] = true := by decide +kernel
theorem sub11_79 : sub11 [3, -4] = true := by decide +kernel
theorem sub11_80 : sub11 [3, -3] = true := by decide +kernel
theorem sub11_81 : sub11 [3, -2] = true := by decide +kernel
theorem sub11_82 : sub11 [3, -1] = true := by decide +kernel
theorem sub11_83 : sub11 [3, 0] = true := by decide +kernel
theorem sub11_84 : sub11 [3, 1] = true := by decide +kernel
theorem sub11_85 : sub11 [3, 2] = true := by decide +kernel
theorem sub11_86 : sub11 [3, 3] = true := by decide +kernel
theorem sub11_87 : sub11 [3, 4] = true := by decide +kernel
theorem sub11_88 : sub11 [4, -4] = true := by decide +kernel
theorem sub11_89 : sub11 [4, -3] = true := by decide +kernel
theorem sub11_90 : sub11 [4, -2] = true := by decide +kernel
theorem sub11_91 : sub11 [4, -1] = true := by decide +kernel
theorem sub11_92 : sub11 [4, 0] = true := by decide +kernel
theorem sub11_93 : sub11 [4, 1] = true := by decide +kernel
theorem sub11_94 : sub11 [4, 2] = true := by decide +kernel
theorem sub11_95 : sub11 [4, 3] = true := by decide +kernel
theorem sb11_2 : ∀ q ∈ blk11_2, sub11 q = true := by
  unfold blk11_2
  exact List.forall_mem_cons.2 ⟨sub11_64, List.forall_mem_cons.2 ⟨sub11_65, List.forall_mem_cons.2 ⟨sub11_66, List.forall_mem_cons.2 ⟨sub11_67, List.forall_mem_cons.2 ⟨sub11_68, List.forall_mem_cons.2 ⟨sub11_69, List.forall_mem_cons.2 ⟨sub11_70, List.forall_mem_cons.2 ⟨sub11_71, List.forall_mem_cons.2 ⟨sub11_72, List.forall_mem_cons.2 ⟨sub11_73, List.forall_mem_cons.2 ⟨sub11_74, List.forall_mem_cons.2 ⟨sub11_75, List.forall_mem_cons.2 ⟨sub11_76, List.forall_mem_cons.2 ⟨sub11_77, List.forall_mem_cons.2 ⟨sub11_78, List.forall_mem_cons.2 ⟨sub11_79, List.forall_mem_cons.2 ⟨sub11_80, List.forall_mem_cons.2 ⟨sub11_81, List.forall_mem_cons.2 ⟨sub11_82, List.forall_mem_cons.2 ⟨sub11_83, List.forall_mem_cons.2 ⟨sub11_84, List.forall_mem_cons.2 ⟨sub11_85, List.forall_mem_cons.2 ⟨sub11_86, List.forall_mem_cons.2 ⟨sub11_87, List.forall_mem_cons.2 ⟨sub11_88, List.forall_mem_cons.2 ⟨sub11_89, List.forall_mem_cons.2 ⟨sub11_90, List.forall_mem_cons.2 ⟨sub11_91, List.forall_mem_cons.2 ⟨sub11_92, List.forall_mem_cons.2 ⟨sub11_93, List.forall_mem_cons.2 ⟨sub11_94, List.forall_mem_cons.2 ⟨sub11_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub12_0 : sub12 [-3] = true := by decide +kernel
theorem sub12_1 : sub12 [-2, -3] = true := by decide +kernel
theorem sub12_2 : sub12 [-2, -2] = true := by decide +kernel
theorem sub12_3 : sub12 [-2, -1] = true := by decide +kernel
theorem sub12_4 : sub12 [-2, 0] = true := by decide +kernel
theorem sub12_5 : sub12 [-2, 1] = true := by decide +kernel
theorem sub12_6 : sub12 [-2, 2] = true := by decide +kernel
theorem sub12_7 : sub12 [-1, -4] = true := by decide +kernel
theorem sub12_8 : sub12 [-1, -3] = true := by decide +kernel
theorem sub12_9 : sub12 [-1, -2] = true := by decide +kernel
theorem sub12_10 : sub12 [-1, -1] = true := by decide +kernel
theorem sub12_11 : sub12 [-1, 0] = true := by decide +kernel
theorem sub12_12 : sub12 [-1, 1] = true := by decide +kernel
theorem sub12_13 : sub12 [-1, 2] = true := by decide +kernel
theorem sub12_14 : sub12 [-1, 3] = true := by decide +kernel
theorem sub12_15 : sub12 [0, -4] = true := by decide +kernel
theorem sub12_16 : sub12 [0, -3] = true := by decide +kernel
theorem sub12_17 : sub12 [0, -2] = true := by decide +kernel
theorem sub12_18 : sub12 [0, -1] = true := by decide +kernel
theorem sub12_19 : sub12 [0, 0] = true := by decide +kernel
theorem sub12_20 : sub12 [0, 1] = true := by decide +kernel
theorem sub12_21 : sub12 [0, 2] = true := by decide +kernel
theorem sub12_22 : sub12 [0, 3] = true := by decide +kernel
theorem sub12_23 : sub12 [1, -4] = true := by decide +kernel
theorem sub12_24 : sub12 [1, -3] = true := by decide +kernel
theorem sub12_25 : sub12 [1, -2] = true := by decide +kernel
theorem sub12_26 : sub12 [1, -1] = true := by decide +kernel
theorem sub12_27 : sub12 [1, 0] = true := by decide +kernel
theorem sub12_28 : sub12 [1, 1] = true := by decide +kernel
theorem sub12_29 : sub12 [1, 2] = true := by decide +kernel
theorem sub12_30 : sub12 [1, 3] = true := by decide +kernel
theorem sub12_31 : sub12 [2, -3] = true := by decide +kernel
theorem sb12_0 : ∀ q ∈ blk12_0, sub12 q = true := by
  unfold blk12_0
  exact List.forall_mem_cons.2 ⟨sub12_0, List.forall_mem_cons.2 ⟨sub12_1, List.forall_mem_cons.2 ⟨sub12_2, List.forall_mem_cons.2 ⟨sub12_3, List.forall_mem_cons.2 ⟨sub12_4, List.forall_mem_cons.2 ⟨sub12_5, List.forall_mem_cons.2 ⟨sub12_6, List.forall_mem_cons.2 ⟨sub12_7, List.forall_mem_cons.2 ⟨sub12_8, List.forall_mem_cons.2 ⟨sub12_9, List.forall_mem_cons.2 ⟨sub12_10, List.forall_mem_cons.2 ⟨sub12_11, List.forall_mem_cons.2 ⟨sub12_12, List.forall_mem_cons.2 ⟨sub12_13, List.forall_mem_cons.2 ⟨sub12_14, List.forall_mem_cons.2 ⟨sub12_15, List.forall_mem_cons.2 ⟨sub12_16, List.forall_mem_cons.2 ⟨sub12_17, List.forall_mem_cons.2 ⟨sub12_18, List.forall_mem_cons.2 ⟨sub12_19, List.forall_mem_cons.2 ⟨sub12_20, List.forall_mem_cons.2 ⟨sub12_21, List.forall_mem_cons.2 ⟨sub12_22, List.forall_mem_cons.2 ⟨sub12_23, List.forall_mem_cons.2 ⟨sub12_24, List.forall_mem_cons.2 ⟨sub12_25, List.forall_mem_cons.2 ⟨sub12_26, List.forall_mem_cons.2 ⟨sub12_27, List.forall_mem_cons.2 ⟨sub12_28, List.forall_mem_cons.2 ⟨sub12_29, List.forall_mem_cons.2 ⟨sub12_30, List.forall_mem_cons.2 ⟨sub12_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C125
