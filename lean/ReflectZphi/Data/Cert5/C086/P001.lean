import ReflectZphi.Data.Cert5.C086.Base

namespace ReflectZphi.Data.Cert5.C086
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub1_64 : sub1 [1, 5] = true := by decide +kernel
theorem sub1_65 : sub1 [2, -5] = true := by decide +kernel
theorem sub1_66 : sub1 [2, -4] = true := by decide +kernel
theorem sub1_67 : sub1 [2, -3] = true := by decide +kernel
theorem sub1_68 : sub1 [2, -2] = true := by decide +kernel
theorem sub1_69 : sub1 [2, -1] = true := by decide +kernel
theorem sub1_70 : sub1 [2, 0] = true := by decide +kernel
theorem sub1_71 : sub1 [2, 1] = true := by decide +kernel
theorem sub1_72 : sub1 [2, 2] = true := by decide +kernel
theorem sub1_73 : sub1 [2, 3] = true := by decide +kernel
theorem sub1_74 : sub1 [2, 4] = true := by decide +kernel
theorem sub1_75 : sub1 [3, -5] = true := by decide +kernel
theorem sub1_76 : sub1 [3, -4] = true := by decide +kernel
theorem sub1_77 : sub1 [3, -3] = true := by decide +kernel
theorem sub1_78 : sub1 [3, -2] = true := by decide +kernel
theorem sub1_79 : sub1 [3, -1] = true := by decide +kernel
theorem sub1_80 : sub1 [3, 0] = true := by decide +kernel
theorem sub1_81 : sub1 [3, 1] = true := by decide +kernel
theorem sub1_82 : sub1 [3, 2] = true := by decide +kernel
theorem sub1_83 : sub1 [3, 3] = true := by decide +kernel
theorem sub1_84 : sub1 [3, 4] = true := by decide +kernel
theorem sub1_85 : sub1 [4, -4] = true := by decide +kernel
theorem sub1_86 : sub1 [4, -3] = true := by decide +kernel
theorem sub1_87 : sub1 [4, -2] = true := by decide +kernel
theorem sub1_88 : sub1 [4, -1] = true := by decide +kernel
theorem sub1_89 : sub1 [4, 0] = true := by decide +kernel
theorem sub1_90 : sub1 [4, 1] = true := by decide +kernel
theorem sub1_91 : sub1 [4, 2] = true := by decide +kernel
theorem sub1_92 : sub1 [4, 3] = true := by decide +kernel
theorem sub1_93 : sub1 [5] = true := by decide +kernel
theorem sb1_2 : ∀ q ∈ blk1_2, sub1 q = true := by
  unfold blk1_2
  exact List.forall_mem_cons.2 ⟨sub1_64, List.forall_mem_cons.2 ⟨sub1_65, List.forall_mem_cons.2 ⟨sub1_66, List.forall_mem_cons.2 ⟨sub1_67, List.forall_mem_cons.2 ⟨sub1_68, List.forall_mem_cons.2 ⟨sub1_69, List.forall_mem_cons.2 ⟨sub1_70, List.forall_mem_cons.2 ⟨sub1_71, List.forall_mem_cons.2 ⟨sub1_72, List.forall_mem_cons.2 ⟨sub1_73, List.forall_mem_cons.2 ⟨sub1_74, List.forall_mem_cons.2 ⟨sub1_75, List.forall_mem_cons.2 ⟨sub1_76, List.forall_mem_cons.2 ⟨sub1_77, List.forall_mem_cons.2 ⟨sub1_78, List.forall_mem_cons.2 ⟨sub1_79, List.forall_mem_cons.2 ⟨sub1_80, List.forall_mem_cons.2 ⟨sub1_81, List.forall_mem_cons.2 ⟨sub1_82, List.forall_mem_cons.2 ⟨sub1_83, List.forall_mem_cons.2 ⟨sub1_84, List.forall_mem_cons.2 ⟨sub1_85, List.forall_mem_cons.2 ⟨sub1_86, List.forall_mem_cons.2 ⟨sub1_87, List.forall_mem_cons.2 ⟨sub1_88, List.forall_mem_cons.2 ⟨sub1_89, List.forall_mem_cons.2 ⟨sub1_90, List.forall_mem_cons.2 ⟨sub1_91, List.forall_mem_cons.2 ⟨sub1_92, List.forall_mem_cons.2 ⟨sub1_93, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_0 : sub2 [-4, -5] = true := by decide +kernel
theorem sub2_1 : sub2 [-4, -4] = true := by decide +kernel
theorem sub2_2 : sub2 [-4, -3] = true := by decide +kernel
theorem sub2_3 : sub2 [-4, -2] = true := by decide +kernel
theorem sub2_4 : sub2 [-4, -1] = true := by decide +kernel
theorem sub2_5 : sub2 [-4, 0] = true := by decide +kernel
theorem sub2_6 : sub2 [-4, 1] = true := by decide +kernel
theorem sub2_7 : sub2 [-3, -6] = true := by decide +kernel
theorem sub2_8 : sub2 [-3, -5] = true := by decide +kernel
theorem sub2_9 : sub2 [-3, -4] = true := by decide +kernel
theorem sub2_10 : sub2 [-3, -3] = true := by decide +kernel
theorem sub2_11 : sub2 [-3, -2] = true := by decide +kernel
theorem sub2_12 : sub2 [-3, -1] = true := by decide +kernel
theorem sub2_13 : sub2 [-3, 0] = true := by decide +kernel
theorem sub2_14 : sub2 [-3, 1] = true := by decide +kernel
theorem sub2_15 : sub2 [-3, 2] = true := by decide +kernel
theorem sub2_16 : sub2 [-3, 3] = true := by decide +kernel
theorem sub2_17 : sub2 [-2, -6] = true := by decide +kernel
theorem sub2_18 : sub2 [-2, -5] = true := by decide +kernel
theorem sub2_19 : sub2 [-2, -4] = true := by decide +kernel
theorem sub2_20 : sub2 [-2, -3] = true := by decide +kernel
theorem sub2_21 : sub2 [-2, -2] = true := by decide +kernel
theorem sub2_22 : sub2 [-2, -1] = true := by decide +kernel
theorem sub2_23 : sub2 [-2, 0] = true := by decide +kernel
theorem sub2_24 : sub2 [-2, 1] = true := by decide +kernel
theorem sub2_25 : sub2 [-2, 2] = true := by decide +kernel
theorem sub2_26 : sub2 [-2, 3] = true := by decide +kernel
theorem sub2_27 : sub2 [-2, 4] = true := by decide +kernel
theorem sub2_28 : sub2 [-1, -6] = true := by decide +kernel
theorem sub2_29 : sub2 [-1, -5] = true := by decide +kernel
theorem sub2_30 : sub2 [-1, -4] = true := by decide +kernel
theorem sub2_31 : sub2 [-1, -3] = true := by decide +kernel
theorem sb2_0 : ∀ q ∈ blk2_0, sub2 q = true := by
  unfold blk2_0
  exact List.forall_mem_cons.2 ⟨sub2_0, List.forall_mem_cons.2 ⟨sub2_1, List.forall_mem_cons.2 ⟨sub2_2, List.forall_mem_cons.2 ⟨sub2_3, List.forall_mem_cons.2 ⟨sub2_4, List.forall_mem_cons.2 ⟨sub2_5, List.forall_mem_cons.2 ⟨sub2_6, List.forall_mem_cons.2 ⟨sub2_7, List.forall_mem_cons.2 ⟨sub2_8, List.forall_mem_cons.2 ⟨sub2_9, List.forall_mem_cons.2 ⟨sub2_10, List.forall_mem_cons.2 ⟨sub2_11, List.forall_mem_cons.2 ⟨sub2_12, List.forall_mem_cons.2 ⟨sub2_13, List.forall_mem_cons.2 ⟨sub2_14, List.forall_mem_cons.2 ⟨sub2_15, List.forall_mem_cons.2 ⟨sub2_16, List.forall_mem_cons.2 ⟨sub2_17, List.forall_mem_cons.2 ⟨sub2_18, List.forall_mem_cons.2 ⟨sub2_19, List.forall_mem_cons.2 ⟨sub2_20, List.forall_mem_cons.2 ⟨sub2_21, List.forall_mem_cons.2 ⟨sub2_22, List.forall_mem_cons.2 ⟨sub2_23, List.forall_mem_cons.2 ⟨sub2_24, List.forall_mem_cons.2 ⟨sub2_25, List.forall_mem_cons.2 ⟨sub2_26, List.forall_mem_cons.2 ⟨sub2_27, List.forall_mem_cons.2 ⟨sub2_28, List.forall_mem_cons.2 ⟨sub2_29, List.forall_mem_cons.2 ⟨sub2_30, List.forall_mem_cons.2 ⟨sub2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_32 : sub2 [-1, -2] = true := by decide +kernel
theorem sub2_33 : sub2 [-1, -1] = true := by decide +kernel
theorem sub2_34 : sub2 [-1, 0] = true := by decide +kernel
theorem sub2_35 : sub2 [-1, 1] = true := by decide +kernel
theorem sub2_36 : sub2 [-1, 2] = true := by decide +kernel
theorem sub2_37 : sub2 [-1, 3] = true := by decide +kernel
theorem sub2_38 : sub2 [-1, 4] = true := by decide +kernel
theorem sub2_39 : sub2 [-1, 5] = true := by decide +kernel
theorem sub2_40 : sub2 [0, -6] = true := by decide +kernel
theorem sub2_41 : sub2 [0, -5] = true := by decide +kernel
theorem sub2_42 : sub2 [0, -4] = true := by decide +kernel
theorem sub2_43 : sub2 [0, -3] = true := by decide +kernel
theorem sub2_44 : sub2 [0, -2] = true := by decide +kernel
theorem sub2_45 : sub2 [0, -1] = true := by decide +kernel
theorem sub2_46 : sub2 [0, 0] = true := by decide +kernel
theorem sub2_47 : sub2 [0, 1] = true := by decide +kernel
theorem sub2_48 : sub2 [0, 2] = true := by decide +kernel
theorem sub2_49 : sub2 [0, 3] = true := by decide +kernel
theorem sub2_50 : sub2 [0, 4] = true := by decide +kernel
theorem sub2_51 : sub2 [0, 5] = true := by decide +kernel
theorem sub2_52 : sub2 [1, -6] = true := by decide +kernel
theorem sub2_53 : sub2 [1, -5] = true := by decide +kernel
theorem sub2_54 : sub2 [1, -4] = true := by decide +kernel
theorem sub2_55 : sub2 [1, -3] = true := by decide +kernel
theorem sub2_56 : sub2 [1, -2] = true := by decide +kernel
theorem sub2_57 : sub2 [1, -1] = true := by decide +kernel
theorem sub2_58 : sub2 [1, 0] = true := by decide +kernel
theorem sub2_59 : sub2 [1, 1] = true := by decide +kernel
theorem sub2_60 : sub2 [1, 2] = true := by decide +kernel
theorem sub2_61 : sub2 [1, 3] = true := by decide +kernel
theorem sub2_62 : sub2 [1, 4] = true := by decide +kernel
theorem sub2_63 : sub2 [1, 5] = true := by decide +kernel
theorem sb2_1 : ∀ q ∈ blk2_1, sub2 q = true := by
  unfold blk2_1
  exact List.forall_mem_cons.2 ⟨sub2_32, List.forall_mem_cons.2 ⟨sub2_33, List.forall_mem_cons.2 ⟨sub2_34, List.forall_mem_cons.2 ⟨sub2_35, List.forall_mem_cons.2 ⟨sub2_36, List.forall_mem_cons.2 ⟨sub2_37, List.forall_mem_cons.2 ⟨sub2_38, List.forall_mem_cons.2 ⟨sub2_39, List.forall_mem_cons.2 ⟨sub2_40, List.forall_mem_cons.2 ⟨sub2_41, List.forall_mem_cons.2 ⟨sub2_42, List.forall_mem_cons.2 ⟨sub2_43, List.forall_mem_cons.2 ⟨sub2_44, List.forall_mem_cons.2 ⟨sub2_45, List.forall_mem_cons.2 ⟨sub2_46, List.forall_mem_cons.2 ⟨sub2_47, List.forall_mem_cons.2 ⟨sub2_48, List.forall_mem_cons.2 ⟨sub2_49, List.forall_mem_cons.2 ⟨sub2_50, List.forall_mem_cons.2 ⟨sub2_51, List.forall_mem_cons.2 ⟨sub2_52, List.forall_mem_cons.2 ⟨sub2_53, List.forall_mem_cons.2 ⟨sub2_54, List.forall_mem_cons.2 ⟨sub2_55, List.forall_mem_cons.2 ⟨sub2_56, List.forall_mem_cons.2 ⟨sub2_57, List.forall_mem_cons.2 ⟨sub2_58, List.forall_mem_cons.2 ⟨sub2_59, List.forall_mem_cons.2 ⟨sub2_60, List.forall_mem_cons.2 ⟨sub2_61, List.forall_mem_cons.2 ⟨sub2_62, List.forall_mem_cons.2 ⟨sub2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_64 : sub2 [2, -5] = true := by decide +kernel
theorem sub2_65 : sub2 [2, -4] = true := by decide +kernel
theorem sub2_66 : sub2 [2, -3] = true := by decide +kernel
theorem sub2_67 : sub2 [2, -2] = true := by decide +kernel
theorem sub2_68 : sub2 [2, -1] = true := by decide +kernel
theorem sub2_69 : sub2 [2, 0] = true := by decide +kernel
theorem sub2_70 : sub2 [2, 1] = true := by decide +kernel
theorem sub2_71 : sub2 [2, 2] = true := by decide +kernel
theorem sub2_72 : sub2 [2, 3] = true := by decide +kernel
theorem sub2_73 : sub2 [2, 4] = true := by decide +kernel
theorem sub2_74 : sub2 [2, 5] = true := by decide +kernel
theorem sub2_75 : sub2 [3, -4] = true := by decide +kernel
theorem sub2_76 : sub2 [3, -3] = true := by decide +kernel
theorem sub2_77 : sub2 [3, -2] = true := by decide +kernel
theorem sub2_78 : sub2 [3, -1] = true := by decide +kernel
theorem sub2_79 : sub2 [3, 0] = true := by decide +kernel
theorem sub2_80 : sub2 [3, 1] = true := by decide +kernel
theorem sub2_81 : sub2 [3, 2] = true := by decide +kernel
theorem sub2_82 : sub2 [3, 3] = true := by decide +kernel
theorem sub2_83 : sub2 [3, 4] = true := by decide +kernel
theorem sub2_84 : sub2 [3, 5] = true := by decide +kernel
theorem sub2_85 : sub2 [4, -2] = true := by decide +kernel
theorem sub2_86 : sub2 [4, -1] = true := by decide +kernel
theorem sub2_87 : sub2 [4, 0] = true := by decide +kernel
theorem sub2_88 : sub2 [4, 1] = true := by decide +kernel
theorem sub2_89 : sub2 [4, 2] = true := by decide +kernel
theorem sub2_90 : sub2 [4, 3] = true := by decide +kernel
theorem sub2_91 : sub2 [4, 4] = true := by decide +kernel
theorem sb2_2 : ∀ q ∈ blk2_2, sub2 q = true := by
  unfold blk2_2
  exact List.forall_mem_cons.2 ⟨sub2_64, List.forall_mem_cons.2 ⟨sub2_65, List.forall_mem_cons.2 ⟨sub2_66, List.forall_mem_cons.2 ⟨sub2_67, List.forall_mem_cons.2 ⟨sub2_68, List.forall_mem_cons.2 ⟨sub2_69, List.forall_mem_cons.2 ⟨sub2_70, List.forall_mem_cons.2 ⟨sub2_71, List.forall_mem_cons.2 ⟨sub2_72, List.forall_mem_cons.2 ⟨sub2_73, List.forall_mem_cons.2 ⟨sub2_74, List.forall_mem_cons.2 ⟨sub2_75, List.forall_mem_cons.2 ⟨sub2_76, List.forall_mem_cons.2 ⟨sub2_77, List.forall_mem_cons.2 ⟨sub2_78, List.forall_mem_cons.2 ⟨sub2_79, List.forall_mem_cons.2 ⟨sub2_80, List.forall_mem_cons.2 ⟨sub2_81, List.forall_mem_cons.2 ⟨sub2_82, List.forall_mem_cons.2 ⟨sub2_83, List.forall_mem_cons.2 ⟨sub2_84, List.forall_mem_cons.2 ⟨sub2_85, List.forall_mem_cons.2 ⟨sub2_86, List.forall_mem_cons.2 ⟨sub2_87, List.forall_mem_cons.2 ⟨sub2_88, List.forall_mem_cons.2 ⟨sub2_89, List.forall_mem_cons.2 ⟨sub2_90, List.forall_mem_cons.2 ⟨sub2_91, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C086
