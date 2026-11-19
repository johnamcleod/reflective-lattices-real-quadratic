import ReflectZphi.Data.Cert5.C092.Base

namespace ReflectZphi.Data.Cert5.C092
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
theorem sub5_0 : sub5 [-5, -3] = true := by decide +kernel
theorem sub5_1 : sub5 [-5, -2] = true := by decide +kernel
theorem sub5_2 : sub5 [-5, -1] = true := by decide +kernel
theorem sub5_3 : sub5 [-5, 0] = true := by decide +kernel
theorem sub5_4 : sub5 [-5, 1] = true := by decide +kernel
theorem sub5_5 : sub5 [-5, 2] = true := by decide +kernel
theorem sub5_6 : sub5 [-4, -5] = true := by decide +kernel
theorem sub5_7 : sub5 [-4, -4] = true := by decide +kernel
theorem sub5_8 : sub5 [-4, -3] = true := by decide +kernel
theorem sub5_9 : sub5 [-4, -2] = true := by decide +kernel
theorem sub5_10 : sub5 [-4, -1] = true := by decide +kernel
theorem sub5_11 : sub5 [-4, 0] = true := by decide +kernel
theorem sub5_12 : sub5 [-4, 1] = true := by decide +kernel
theorem sub5_13 : sub5 [-4, 2] = true := by decide +kernel
theorem sub5_14 : sub5 [-4, 3] = true := by decide +kernel
theorem sub5_15 : sub5 [-3, -5] = true := by decide +kernel
theorem sub5_16 : sub5 [-3, -4] = true := by decide +kernel
theorem sub5_17 : sub5 [-3, -3] = true := by decide +kernel
theorem sub5_18 : sub5 [-3, -2] = true := by decide +kernel
theorem sub5_19 : sub5 [-3, -1, -6] = true := by decide +kernel
theorem sub5_20 : sub5 [-3, -1, -5] = true := by decide +kernel
theorem sub5_21 : sub5 [-3, -1, -4] = true := by decide +kernel
theorem sub5_22 : sub5 [-3, -1, -3] = true := by decide +kernel
theorem sub5_23 : sub5 [-3, -1, -2] = true := by decide +kernel
theorem sub5_24 : sub5 [-3, -1, -1] = true := by decide +kernel
theorem sub5_25 : sub5 [-3, -1, 0] = true := by decide +kernel
theorem sub5_26 : sub5 [-3, -1, 1] = true := by decide +kernel
theorem sub5_27 : sub5 [-3, -1, 2] = true := by decide +kernel
theorem sub5_28 : sub5 [-3, -1, 3] = true := by decide +kernel
theorem sub5_29 : sub5 [-3, -1, 4] = true := by decide +kernel
theorem sub5_30 : sub5 [-3, -1, 5] = true := by decide +kernel
theorem sub5_31 : sub5 [-3, -1, 6] = true := by decide +kernel
theorem sb5_0 : ∀ q ∈ blk5_0, sub5 q = true := by
  unfold blk5_0
  exact List.forall_mem_cons.2 ⟨sub5_0, List.forall_mem_cons.2 ⟨sub5_1, List.forall_mem_cons.2 ⟨sub5_2, List.forall_mem_cons.2 ⟨sub5_3, List.forall_mem_cons.2 ⟨sub5_4, List.forall_mem_cons.2 ⟨sub5_5, List.forall_mem_cons.2 ⟨sub5_6, List.forall_mem_cons.2 ⟨sub5_7, List.forall_mem_cons.2 ⟨sub5_8, List.forall_mem_cons.2 ⟨sub5_9, List.forall_mem_cons.2 ⟨sub5_10, List.forall_mem_cons.2 ⟨sub5_11, List.forall_mem_cons.2 ⟨sub5_12, List.forall_mem_cons.2 ⟨sub5_13, List.forall_mem_cons.2 ⟨sub5_14, List.forall_mem_cons.2 ⟨sub5_15, List.forall_mem_cons.2 ⟨sub5_16, List.forall_mem_cons.2 ⟨sub5_17, List.forall_mem_cons.2 ⟨sub5_18, List.forall_mem_cons.2 ⟨sub5_19, List.forall_mem_cons.2 ⟨sub5_20, List.forall_mem_cons.2 ⟨sub5_21, List.forall_mem_cons.2 ⟨sub5_22, List.forall_mem_cons.2 ⟨sub5_23, List.forall_mem_cons.2 ⟨sub5_24, List.forall_mem_cons.2 ⟨sub5_25, List.forall_mem_cons.2 ⟨sub5_26, List.forall_mem_cons.2 ⟨sub5_27, List.forall_mem_cons.2 ⟨sub5_28, List.forall_mem_cons.2 ⟨sub5_29, List.forall_mem_cons.2 ⟨sub5_30, List.forall_mem_cons.2 ⟨sub5_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_32 : sub5 [-3, 0, -6] = true := by decide +kernel
theorem sub5_33 : sub5 [-3, 0, -5] = true := by decide +kernel
theorem sub5_34 : sub5 [-3, 0, -4] = true := by decide +kernel
theorem sub5_35 : sub5 [-3, 0, -3] = true := by decide +kernel
theorem sub5_36 : sub5 [-3, 0, -2] = true := by decide +kernel
theorem sub5_37 : sub5 [-3, 0, -1] = true := by decide +kernel
theorem sub5_38 : sub5 [-3, 0, 0] = true := by decide +kernel
theorem sub5_39 : sub5 [-3, 0, 1] = true := by decide +kernel
theorem sub5_40 : sub5 [-3, 0, 2] = true := by decide +kernel
theorem sub5_41 : sub5 [-3, 0, 3] = true := by decide +kernel
theorem sub5_42 : sub5 [-3, 0, 4] = true := by decide +kernel
theorem sub5_43 : sub5 [-3, 0, 5] = true := by decide +kernel
theorem sub5_44 : sub5 [-3, 0, 6] = true := by decide +kernel
theorem sub5_45 : sub5 [-3, 0, 7] = true := by decide +kernel
theorem sub5_46 : sub5 [-3, 1, -6] = true := by decide +kernel
theorem sub5_47 : sub5 [-3, 1, -5] = true := by decide +kernel
theorem sub5_48 : sub5 [-3, 1, -4] = true := by decide +kernel
theorem sub5_49 : sub5 [-3, 1, -3] = true := by decide +kernel
theorem sub5_50 : sub5 [-3, 1, -2] = true := by decide +kernel
theorem sub5_51 : sub5 [-3, 1, -1] = true := by decide +kernel
theorem sub5_52 : sub5 [-3, 1, 0] = true := by decide +kernel
theorem sub5_53 : sub5 [-3, 1, 1] = true := by decide +kernel
theorem sub5_54 : sub5 [-3, 1, 2] = true := by decide +kernel
theorem sub5_55 : sub5 [-3, 1, 3] = true := by decide +kernel
theorem sub5_56 : sub5 [-3, 1, 4] = true := by decide +kernel
theorem sub5_57 : sub5 [-3, 1, 5] = true := by decide +kernel
theorem sub5_58 : sub5 [-3, 1, 6] = true := by decide +kernel
theorem sub5_59 : sub5 [-3, 1, 7] = true := by decide +kernel
theorem sub5_60 : sub5 [-3, 2] = true := by decide +kernel
theorem sub5_61 : sub5 [-3, 3] = true := by decide +kernel
theorem sub5_62 : sub5 [-3, 4] = true := by decide +kernel
theorem sub5_63 : sub5 [-2, -6] = true := by decide +kernel
theorem sb5_1 : ∀ q ∈ blk5_1, sub5 q = true := by
  unfold blk5_1
  exact List.forall_mem_cons.2 ⟨sub5_32, List.forall_mem_cons.2 ⟨sub5_33, List.forall_mem_cons.2 ⟨sub5_34, List.forall_mem_cons.2 ⟨sub5_35, List.forall_mem_cons.2 ⟨sub5_36, List.forall_mem_cons.2 ⟨sub5_37, List.forall_mem_cons.2 ⟨sub5_38, List.forall_mem_cons.2 ⟨sub5_39, List.forall_mem_cons.2 ⟨sub5_40, List.forall_mem_cons.2 ⟨sub5_41, List.forall_mem_cons.2 ⟨sub5_42, List.forall_mem_cons.2 ⟨sub5_43, List.forall_mem_cons.2 ⟨sub5_44, List.forall_mem_cons.2 ⟨sub5_45, List.forall_mem_cons.2 ⟨sub5_46, List.forall_mem_cons.2 ⟨sub5_47, List.forall_mem_cons.2 ⟨sub5_48, List.forall_mem_cons.2 ⟨sub5_49, List.forall_mem_cons.2 ⟨sub5_50, List.forall_mem_cons.2 ⟨sub5_51, List.forall_mem_cons.2 ⟨sub5_52, List.forall_mem_cons.2 ⟨sub5_53, List.forall_mem_cons.2 ⟨sub5_54, List.forall_mem_cons.2 ⟨sub5_55, List.forall_mem_cons.2 ⟨sub5_56, List.forall_mem_cons.2 ⟨sub5_57, List.forall_mem_cons.2 ⟨sub5_58, List.forall_mem_cons.2 ⟨sub5_59, List.forall_mem_cons.2 ⟨sub5_60, List.forall_mem_cons.2 ⟨sub5_61, List.forall_mem_cons.2 ⟨sub5_62, List.forall_mem_cons.2 ⟨sub5_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_64 : sub5 [-2, -5] = true := by decide +kernel
theorem sub5_65 : sub5 [-2, -4] = true := by decide +kernel
theorem sub5_66 : sub5 [-2, -3] = true := by decide +kernel
theorem sub5_67 : sub5 [-2, -2, -7] = true := by decide +kernel
theorem sub5_68 : sub5 [-2, -2, -6] = true := by decide +kernel
theorem sub5_69 : sub5 [-2, -2, -5] = true := by decide +kernel
theorem sub5_70 : sub5 [-2, -2, -4] = true := by decide +kernel
theorem sub5_71 : sub5 [-2, -2, -3] = true := by decide +kernel
theorem sub5_72 : sub5 [-2, -2, -2] = true := by decide +kernel
theorem sub5_73 : sub5 [-2, -2, -1] = true := by decide +kernel
theorem sub5_74 : sub5 [-2, -2, 0] = true := by decide +kernel
theorem sub5_75 : sub5 [-2, -2, 1] = true := by decide +kernel
theorem sub5_76 : sub5 [-2, -2, 2] = true := by decide +kernel
theorem sub5_77 : sub5 [-2, -2, 3] = true := by decide +kernel
theorem sub5_78 : sub5 [-2, -2, 4] = true := by decide +kernel
theorem sub5_79 : sub5 [-2, -2, 5] = true := by decide +kernel
theorem sub5_80 : sub5 [-2, -2, 6] = true := by decide +kernel
theorem sub5_81 : sub5 [-2, -1, -7] = true := by decide +kernel
theorem sub5_82 : sub5 [-2, -1, -6] = true := by decide +kernel
theorem sub5_83 : sub5 [-2, -1, -5] = true := by decide +kernel
theorem sub5_84 : sub5 [-2, -1, -4] = true := by decide +kernel
theorem sub5_85 : sub5 [-2, -1, -3] = true := by decide +kernel
theorem sub5_86 : sub5 [-2, -1, -2] = true := by decide +kernel
theorem sub5_87 : sub5 [-2, -1, -1] = true := by decide +kernel
theorem sub5_88 : sub5 [-2, -1, 0] = true := by decide +kernel
theorem sub5_89 : sub5 [-2, -1, 1] = true := by decide +kernel
theorem sub5_90 : sub5 [-2, -1, 2] = true := by decide +kernel
theorem sub5_91 : sub5 [-2, -1, 3] = true := by decide +kernel
theorem sub5_92 : sub5 [-2, -1, 4] = true := by decide +kernel
theorem sub5_93 : sub5 [-2, -1, 5] = true := by decide +kernel
theorem sub5_94 : sub5 [-2, -1, 6] = true := by decide +kernel
theorem sub5_95 : sub5 [-2, -1, 7] = true := by decide +kernel
theorem sb5_2 : ∀ q ∈ blk5_2, sub5 q = true := by
  unfold blk5_2
  exact List.forall_mem_cons.2 ⟨sub5_64, List.forall_mem_cons.2 ⟨sub5_65, List.forall_mem_cons.2 ⟨sub5_66, List.forall_mem_cons.2 ⟨sub5_67, List.forall_mem_cons.2 ⟨sub5_68, List.forall_mem_cons.2 ⟨sub5_69, List.forall_mem_cons.2 ⟨sub5_70, List.forall_mem_cons.2 ⟨sub5_71, List.forall_mem_cons.2 ⟨sub5_72, List.forall_mem_cons.2 ⟨sub5_73, List.forall_mem_cons.2 ⟨sub5_74, List.forall_mem_cons.2 ⟨sub5_75, List.forall_mem_cons.2 ⟨sub5_76, List.forall_mem_cons.2 ⟨sub5_77, List.forall_mem_cons.2 ⟨sub5_78, List.forall_mem_cons.2 ⟨sub5_79, List.forall_mem_cons.2 ⟨sub5_80, List.forall_mem_cons.2 ⟨sub5_81, List.forall_mem_cons.2 ⟨sub5_82, List.forall_mem_cons.2 ⟨sub5_83, List.forall_mem_cons.2 ⟨sub5_84, List.forall_mem_cons.2 ⟨sub5_85, List.forall_mem_cons.2 ⟨sub5_86, List.forall_mem_cons.2 ⟨sub5_87, List.forall_mem_cons.2 ⟨sub5_88, List.forall_mem_cons.2 ⟨sub5_89, List.forall_mem_cons.2 ⟨sub5_90, List.forall_mem_cons.2 ⟨sub5_91, List.forall_mem_cons.2 ⟨sub5_92, List.forall_mem_cons.2 ⟨sub5_93, List.forall_mem_cons.2 ⟨sub5_94, List.forall_mem_cons.2 ⟨sub5_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_96 : sub5 [-2, 0, -7] = true := by decide +kernel
theorem sub5_97 : sub5 [-2, 0, -6] = true := by decide +kernel
theorem sub5_98 : sub5 [-2, 0, -5] = true := by decide +kernel
theorem sub5_99 : sub5 [-2, 0, -4] = true := by decide +kernel
theorem sub5_100 : sub5 [-2, 0, -3] = true := by decide +kernel
theorem sub5_101 : sub5 [-2, 0, -2] = true := by decide +kernel
theorem sub5_102 : sub5 [-2, 0, -1] = true := by decide +kernel
theorem sub5_103 : sub5 [-2, 0, 0] = true := by decide +kernel
theorem sub5_104 : sub5 [-2, 0, 1] = true := by decide +kernel
theorem sub5_105 : sub5 [-2, 0, 2] = true := by decide +kernel
theorem sub5_106 : sub5 [-2, 0, 3] = true := by decide +kernel
theorem sub5_107 : sub5 [-2, 0, 4] = true := by decide +kernel
theorem sub5_108 : sub5 [-2, 0, 5] = true := by decide +kernel
theorem sub5_109 : sub5 [-2, 0, 6] = true := by decide +kernel
theorem sub5_110 : sub5 [-2, 0, 7] = true := by decide +kernel
theorem sub5_111 : sub5 [-2, 1, -7] = true := by decide +kernel
theorem sub5_112 : sub5 [-2, 1, -6] = true := by decide +kernel
theorem sub5_113 : sub5 [-2, 1, -5] = true := by decide +kernel
theorem sub5_114 : sub5 [-2, 1, -4] = true := by decide +kernel
theorem sub5_115 : sub5 [-2, 1, -3] = true := by decide +kernel
theorem sub5_116 : sub5 [-2, 1, -2] = true := by decide +kernel
theorem sub5_117 : sub5 [-2, 1, -1] = true := by decide +kernel
theorem sub5_118 : sub5 [-2, 1, 0] = true := by decide +kernel
theorem sub5_119 : sub5 [-2, 1, 1] = true := by decide +kernel
theorem sub5_120 : sub5 [-2, 1, 2] = true := by decide +kernel
theorem sub5_121 : sub5 [-2, 1, 3] = true := by decide +kernel
theorem sub5_122 : sub5 [-2, 1, 4] = true := by decide +kernel
theorem sub5_123 : sub5 [-2, 1, 5] = true := by decide +kernel
theorem sub5_124 : sub5 [-2, 1, 6] = true := by decide +kernel
theorem sub5_125 : sub5 [-2, 1, 7] = true := by decide +kernel
theorem sub5_126 : sub5 [-2, 2, -6] = true := by decide +kernel
theorem sub5_127 : sub5 [-2, 2, -5] = true := by decide +kernel
theorem sb5_3 : ∀ q ∈ blk5_3, sub5 q = true := by
  unfold blk5_3
  exact List.forall_mem_cons.2 ⟨sub5_96, List.forall_mem_cons.2 ⟨sub5_97, List.forall_mem_cons.2 ⟨sub5_98, List.forall_mem_cons.2 ⟨sub5_99, List.forall_mem_cons.2 ⟨sub5_100, List.forall_mem_cons.2 ⟨sub5_101, List.forall_mem_cons.2 ⟨sub5_102, List.forall_mem_cons.2 ⟨sub5_103, List.forall_mem_cons.2 ⟨sub5_104, List.forall_mem_cons.2 ⟨sub5_105, List.forall_mem_cons.2 ⟨sub5_106, List.forall_mem_cons.2 ⟨sub5_107, List.forall_mem_cons.2 ⟨sub5_108, List.forall_mem_cons.2 ⟨sub5_109, List.forall_mem_cons.2 ⟨sub5_110, List.forall_mem_cons.2 ⟨sub5_111, List.forall_mem_cons.2 ⟨sub5_112, List.forall_mem_cons.2 ⟨sub5_113, List.forall_mem_cons.2 ⟨sub5_114, List.forall_mem_cons.2 ⟨sub5_115, List.forall_mem_cons.2 ⟨sub5_116, List.forall_mem_cons.2 ⟨sub5_117, List.forall_mem_cons.2 ⟨sub5_118, List.forall_mem_cons.2 ⟨sub5_119, List.forall_mem_cons.2 ⟨sub5_120, List.forall_mem_cons.2 ⟨sub5_121, List.forall_mem_cons.2 ⟨sub5_122, List.forall_mem_cons.2 ⟨sub5_123, List.forall_mem_cons.2 ⟨sub5_124, List.forall_mem_cons.2 ⟨sub5_125, List.forall_mem_cons.2 ⟨sub5_126, List.forall_mem_cons.2 ⟨sub5_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_128 : sub5 [-2, 2, -4] = true := by decide +kernel
theorem sub5_129 : sub5 [-2, 2, -3] = true := by decide +kernel
theorem sub5_130 : sub5 [-2, 2, -2] = true := by decide +kernel
theorem sub5_131 : sub5 [-2, 2, -1] = true := by decide +kernel
theorem sub5_132 : sub5 [-2, 2, 0] = true := by decide +kernel
theorem sub5_133 : sub5 [-2, 2, 1] = true := by decide +kernel
theorem sub5_134 : sub5 [-2, 2, 2] = true := by decide +kernel
theorem sub5_135 : sub5 [-2, 2, 3] = true := by decide +kernel
theorem sub5_136 : sub5 [-2, 2, 4] = true := by decide +kernel
theorem sub5_137 : sub5 [-2, 2, 5] = true := by decide +kernel
theorem sub5_138 : sub5 [-2, 2, 6] = true := by decide +kernel
theorem sub5_139 : sub5 [-2, 2, 7] = true := by decide +kernel
theorem sub5_140 : sub5 [-2, 3] = true := by decide +kernel
theorem sub5_141 : sub5 [-2, 4] = true := by decide +kernel
theorem sub5_142 : sub5 [-2, 5] = true := by decide +kernel
theorem sub5_143 : sub5 [-1, -6] = true := by decide +kernel
theorem sub5_144 : sub5 [-1, -5] = true := by decide +kernel
theorem sub5_145 : sub5 [-1, -4] = true := by decide +kernel
theorem sub5_146 : sub5 [-1, -3, -7] = true := by decide +kernel
theorem sub5_147 : sub5 [-1, -3, -6] = true := by decide +kernel
theorem sub5_148 : sub5 [-1, -3, -5] = true := by decide +kernel
theorem sub5_149 : sub5 [-1, -3, -4] = true := by decide +kernel
theorem sub5_150 : sub5 [-1, -3, -3] = true := by decide +kernel
theorem sub5_151 : sub5 [-1, -3, -2] = true := by decide +kernel
theorem sub5_152 : sub5 [-1, -3, -1] = true := by decide +kernel
theorem sub5_153 : sub5 [-1, -3, 0] = true := by decide +kernel
theorem sub5_154 : sub5 [-1, -3, 1] = true := by decide +kernel
theorem sub5_155 : sub5 [-1, -3, 2] = true := by decide +kernel
theorem sub5_156 : sub5 [-1, -3, 3] = true := by decide +kernel
theorem sub5_157 : sub5 [-1, -3, 4] = true := by decide +kernel
theorem sub5_158 : sub5 [-1, -3, 5] = true := by decide +kernel
theorem sub5_159 : sub5 [-1, -2, -8] = true := by decide +kernel
theorem sb5_4 : ∀ q ∈ blk5_4, sub5 q = true := by
  unfold blk5_4
  exact List.forall_mem_cons.2 ⟨sub5_128, List.forall_mem_cons.2 ⟨sub5_129, List.forall_mem_cons.2 ⟨sub5_130, List.forall_mem_cons.2 ⟨sub5_131, List.forall_mem_cons.2 ⟨sub5_132, List.forall_mem_cons.2 ⟨sub5_133, List.forall_mem_cons.2 ⟨sub5_134, List.forall_mem_cons.2 ⟨sub5_135, List.forall_mem_cons.2 ⟨sub5_136, List.forall_mem_cons.2 ⟨sub5_137, List.forall_mem_cons.2 ⟨sub5_138, List.forall_mem_cons.2 ⟨sub5_139, List.forall_mem_cons.2 ⟨sub5_140, List.forall_mem_cons.2 ⟨sub5_141, List.forall_mem_cons.2 ⟨sub5_142, List.forall_mem_cons.2 ⟨sub5_143, List.forall_mem_cons.2 ⟨sub5_144, List.forall_mem_cons.2 ⟨sub5_145, List.forall_mem_cons.2 ⟨sub5_146, List.forall_mem_cons.2 ⟨sub5_147, List.forall_mem_cons.2 ⟨sub5_148, List.forall_mem_cons.2 ⟨sub5_149, List.forall_mem_cons.2 ⟨sub5_150, List.forall_mem_cons.2 ⟨sub5_151, List.forall_mem_cons.2 ⟨sub5_152, List.forall_mem_cons.2 ⟨sub5_153, List.forall_mem_cons.2 ⟨sub5_154, List.forall_mem_cons.2 ⟨sub5_155, List.forall_mem_cons.2 ⟨sub5_156, List.forall_mem_cons.2 ⟨sub5_157, List.forall_mem_cons.2 ⟨sub5_158, List.forall_mem_cons.2 ⟨sub5_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C092
