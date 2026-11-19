import ReflectZphi.Data.Cert5.C120.Base

namespace ReflectZphi.Data.Cert5.C120
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub4_0 : sub4 [-6] = true := by decide +kernel
theorem sub4_1 : sub4 [-5, -5] = true := by decide +kernel
theorem sub4_2 : sub4 [-5, -4] = true := by decide +kernel
theorem sub4_3 : sub4 [-5, -3] = true := by decide +kernel
theorem sub4_4 : sub4 [-5, -2] = true := by decide +kernel
theorem sub4_5 : sub4 [-5, -1] = true := by decide +kernel
theorem sub4_6 : sub4 [-5, 0] = true := by decide +kernel
theorem sub4_7 : sub4 [-5, 1] = true := by decide +kernel
theorem sub4_8 : sub4 [-5, 2] = true := by decide +kernel
theorem sub4_9 : sub4 [-4, -5] = true := by decide +kernel
theorem sub4_10 : sub4 [-4, -4] = true := by decide +kernel
theorem sub4_11 : sub4 [-4, -3] = true := by decide +kernel
theorem sub4_12 : sub4 [-4, -2] = true := by decide +kernel
theorem sub4_13 : sub4 [-4, -1] = true := by decide +kernel
theorem sub4_14 : sub4 [-4, 0] = true := by decide +kernel
theorem sub4_15 : sub4 [-4, 1] = true := by decide +kernel
theorem sub4_16 : sub4 [-4, 2] = true := by decide +kernel
theorem sub4_17 : sub4 [-4, 3] = true := by decide +kernel
theorem sub4_18 : sub4 [-3, -6] = true := by decide +kernel
theorem sub4_19 : sub4 [-3, -5] = true := by decide +kernel
theorem sub4_20 : sub4 [-3, -4] = true := by decide +kernel
theorem sub4_21 : sub4 [-3, -3] = true := by decide +kernel
theorem sub4_22 : sub4 [-3, -2] = true := by decide +kernel
theorem sub4_23 : sub4 [-3, -1] = true := by decide +kernel
theorem sub4_24 : sub4 [-3, 0] = true := by decide +kernel
theorem sub4_25 : sub4 [-3, 1] = true := by decide +kernel
theorem sub4_26 : sub4 [-3, 2] = true := by decide +kernel
theorem sub4_27 : sub4 [-3, 3] = true := by decide +kernel
theorem sub4_28 : sub4 [-3, 4] = true := by decide +kernel
theorem sub4_29 : sub4 [-2, -6] = true := by decide +kernel
theorem sub4_30 : sub4 [-2, -5] = true := by decide +kernel
theorem sub4_31 : sub4 [-2, -4] = true := by decide +kernel
theorem sb4_0 : ∀ q ∈ blk4_0, sub4 q = true := by
  unfold blk4_0
  exact List.forall_mem_cons.2 ⟨sub4_0, List.forall_mem_cons.2 ⟨sub4_1, List.forall_mem_cons.2 ⟨sub4_2, List.forall_mem_cons.2 ⟨sub4_3, List.forall_mem_cons.2 ⟨sub4_4, List.forall_mem_cons.2 ⟨sub4_5, List.forall_mem_cons.2 ⟨sub4_6, List.forall_mem_cons.2 ⟨sub4_7, List.forall_mem_cons.2 ⟨sub4_8, List.forall_mem_cons.2 ⟨sub4_9, List.forall_mem_cons.2 ⟨sub4_10, List.forall_mem_cons.2 ⟨sub4_11, List.forall_mem_cons.2 ⟨sub4_12, List.forall_mem_cons.2 ⟨sub4_13, List.forall_mem_cons.2 ⟨sub4_14, List.forall_mem_cons.2 ⟨sub4_15, List.forall_mem_cons.2 ⟨sub4_16, List.forall_mem_cons.2 ⟨sub4_17, List.forall_mem_cons.2 ⟨sub4_18, List.forall_mem_cons.2 ⟨sub4_19, List.forall_mem_cons.2 ⟨sub4_20, List.forall_mem_cons.2 ⟨sub4_21, List.forall_mem_cons.2 ⟨sub4_22, List.forall_mem_cons.2 ⟨sub4_23, List.forall_mem_cons.2 ⟨sub4_24, List.forall_mem_cons.2 ⟨sub4_25, List.forall_mem_cons.2 ⟨sub4_26, List.forall_mem_cons.2 ⟨sub4_27, List.forall_mem_cons.2 ⟨sub4_28, List.forall_mem_cons.2 ⟨sub4_29, List.forall_mem_cons.2 ⟨sub4_30, List.forall_mem_cons.2 ⟨sub4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_32 : sub4 [-2, -3] = true := by decide +kernel
theorem sub4_33 : sub4 [-2, -2] = true := by decide +kernel
theorem sub4_34 : sub4 [-2, -1] = true := by decide +kernel
theorem sub4_35 : sub4 [-2, 0] = true := by decide +kernel
theorem sub4_36 : sub4 [-2, 1] = true := by decide +kernel
theorem sub4_37 : sub4 [-2, 2] = true := by decide +kernel
theorem sub4_38 : sub4 [-2, 3] = true := by decide +kernel
theorem sub4_39 : sub4 [-2, 4] = true := by decide +kernel
theorem sub4_40 : sub4 [-1, -6] = true := by decide +kernel
theorem sub4_41 : sub4 [-1, -5] = true := by decide +kernel
theorem sub4_42 : sub4 [-1, -4] = true := by decide +kernel
theorem sub4_43 : sub4 [-1, -3] = true := by decide +kernel
theorem sub4_44 : sub4 [-1, -2] = true := by decide +kernel
theorem sub4_45 : sub4 [-1, -1] = true := by decide +kernel
theorem sub4_46 : sub4 [-1, 0] = true := by decide +kernel
theorem sub4_47 : sub4 [-1, 1] = true := by decide +kernel
theorem sub4_48 : sub4 [-1, 2] = true := by decide +kernel
theorem sub4_49 : sub4 [-1, 3] = true := by decide +kernel
theorem sub4_50 : sub4 [-1, 4] = true := by decide +kernel
theorem sub4_51 : sub4 [-1, 5] = true := by decide +kernel
theorem sub4_52 : sub4 [0, -6] = true := by decide +kernel
theorem sub4_53 : sub4 [0, -5] = true := by decide +kernel
theorem sub4_54 : sub4 [0, -4] = true := by decide +kernel
theorem sub4_55 : sub4 [0, -3] = true := by decide +kernel
theorem sub4_56 : sub4 [0, -2] = true := by decide +kernel
theorem sub4_57 : sub4 [0, -1] = true := by decide +kernel
theorem sub4_58 : sub4 [0, 0] = true := by decide +kernel
theorem sub4_59 : sub4 [0, 1] = true := by decide +kernel
theorem sub4_60 : sub4 [0, 2] = true := by decide +kernel
theorem sub4_61 : sub4 [0, 3] = true := by decide +kernel
theorem sub4_62 : sub4 [0, 4] = true := by decide +kernel
theorem sub4_63 : sub4 [0, 5] = true := by decide +kernel
theorem sb4_1 : ∀ q ∈ blk4_1, sub4 q = true := by
  unfold blk4_1
  exact List.forall_mem_cons.2 ⟨sub4_32, List.forall_mem_cons.2 ⟨sub4_33, List.forall_mem_cons.2 ⟨sub4_34, List.forall_mem_cons.2 ⟨sub4_35, List.forall_mem_cons.2 ⟨sub4_36, List.forall_mem_cons.2 ⟨sub4_37, List.forall_mem_cons.2 ⟨sub4_38, List.forall_mem_cons.2 ⟨sub4_39, List.forall_mem_cons.2 ⟨sub4_40, List.forall_mem_cons.2 ⟨sub4_41, List.forall_mem_cons.2 ⟨sub4_42, List.forall_mem_cons.2 ⟨sub4_43, List.forall_mem_cons.2 ⟨sub4_44, List.forall_mem_cons.2 ⟨sub4_45, List.forall_mem_cons.2 ⟨sub4_46, List.forall_mem_cons.2 ⟨sub4_47, List.forall_mem_cons.2 ⟨sub4_48, List.forall_mem_cons.2 ⟨sub4_49, List.forall_mem_cons.2 ⟨sub4_50, List.forall_mem_cons.2 ⟨sub4_51, List.forall_mem_cons.2 ⟨sub4_52, List.forall_mem_cons.2 ⟨sub4_53, List.forall_mem_cons.2 ⟨sub4_54, List.forall_mem_cons.2 ⟨sub4_55, List.forall_mem_cons.2 ⟨sub4_56, List.forall_mem_cons.2 ⟨sub4_57, List.forall_mem_cons.2 ⟨sub4_58, List.forall_mem_cons.2 ⟨sub4_59, List.forall_mem_cons.2 ⟨sub4_60, List.forall_mem_cons.2 ⟨sub4_61, List.forall_mem_cons.2 ⟨sub4_62, List.forall_mem_cons.2 ⟨sub4_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_64 : sub4 [1, -6] = true := by decide +kernel
theorem sub4_65 : sub4 [1, -5] = true := by decide +kernel
theorem sub4_66 : sub4 [1, -4] = true := by decide +kernel
theorem sub4_67 : sub4 [1, -3] = true := by decide +kernel
theorem sub4_68 : sub4 [1, -2] = true := by decide +kernel
theorem sub4_69 : sub4 [1, -1] = true := by decide +kernel
theorem sub4_70 : sub4 [1, 0] = true := by decide +kernel
theorem sub4_71 : sub4 [1, 1] = true := by decide +kernel
theorem sub4_72 : sub4 [1, 2] = true := by decide +kernel
theorem sub4_73 : sub4 [1, 3] = true := by decide +kernel
theorem sub4_74 : sub4 [1, 4] = true := by decide +kernel
theorem sub4_75 : sub4 [1, 5] = true := by decide +kernel
theorem sub4_76 : sub4 [2, -5] = true := by decide +kernel
theorem sub4_77 : sub4 [2, -4] = true := by decide +kernel
theorem sub4_78 : sub4 [2, -3] = true := by decide +kernel
theorem sub4_79 : sub4 [2, -2] = true := by decide +kernel
theorem sub4_80 : sub4 [2, -1] = true := by decide +kernel
theorem sub4_81 : sub4 [2, 0] = true := by decide +kernel
theorem sub4_82 : sub4 [2, 1] = true := by decide +kernel
theorem sub4_83 : sub4 [2, 2] = true := by decide +kernel
theorem sub4_84 : sub4 [2, 3] = true := by decide +kernel
theorem sub4_85 : sub4 [2, 4] = true := by decide +kernel
theorem sub4_86 : sub4 [2, 5] = true := by decide +kernel
theorem sub4_87 : sub4 [3, -5] = true := by decide +kernel
theorem sub4_88 : sub4 [3, -4] = true := by decide +kernel
theorem sub4_89 : sub4 [3, -3] = true := by decide +kernel
theorem sub4_90 : sub4 [3, -2] = true := by decide +kernel
theorem sub4_91 : sub4 [3, -1] = true := by decide +kernel
theorem sub4_92 : sub4 [3, 0] = true := by decide +kernel
theorem sub4_93 : sub4 [3, 1] = true := by decide +kernel
theorem sub4_94 : sub4 [3, 2] = true := by decide +kernel
theorem sub4_95 : sub4 [3, 3] = true := by decide +kernel
theorem sb4_2 : ∀ q ∈ blk4_2, sub4 q = true := by
  unfold blk4_2
  exact List.forall_mem_cons.2 ⟨sub4_64, List.forall_mem_cons.2 ⟨sub4_65, List.forall_mem_cons.2 ⟨sub4_66, List.forall_mem_cons.2 ⟨sub4_67, List.forall_mem_cons.2 ⟨sub4_68, List.forall_mem_cons.2 ⟨sub4_69, List.forall_mem_cons.2 ⟨sub4_70, List.forall_mem_cons.2 ⟨sub4_71, List.forall_mem_cons.2 ⟨sub4_72, List.forall_mem_cons.2 ⟨sub4_73, List.forall_mem_cons.2 ⟨sub4_74, List.forall_mem_cons.2 ⟨sub4_75, List.forall_mem_cons.2 ⟨sub4_76, List.forall_mem_cons.2 ⟨sub4_77, List.forall_mem_cons.2 ⟨sub4_78, List.forall_mem_cons.2 ⟨sub4_79, List.forall_mem_cons.2 ⟨sub4_80, List.forall_mem_cons.2 ⟨sub4_81, List.forall_mem_cons.2 ⟨sub4_82, List.forall_mem_cons.2 ⟨sub4_83, List.forall_mem_cons.2 ⟨sub4_84, List.forall_mem_cons.2 ⟨sub4_85, List.forall_mem_cons.2 ⟨sub4_86, List.forall_mem_cons.2 ⟨sub4_87, List.forall_mem_cons.2 ⟨sub4_88, List.forall_mem_cons.2 ⟨sub4_89, List.forall_mem_cons.2 ⟨sub4_90, List.forall_mem_cons.2 ⟨sub4_91, List.forall_mem_cons.2 ⟨sub4_92, List.forall_mem_cons.2 ⟨sub4_93, List.forall_mem_cons.2 ⟨sub4_94, List.forall_mem_cons.2 ⟨sub4_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_96 : sub4 [3, 4] = true := by decide +kernel
theorem sub4_97 : sub4 [3, 5] = true := by decide +kernel
theorem sub4_98 : sub4 [4, -4] = true := by decide +kernel
theorem sub4_99 : sub4 [4, -3] = true := by decide +kernel
theorem sub4_100 : sub4 [4, -2] = true := by decide +kernel
theorem sub4_101 : sub4 [4, -1] = true := by decide +kernel
theorem sub4_102 : sub4 [4, 0] = true := by decide +kernel
theorem sub4_103 : sub4 [4, 1] = true := by decide +kernel
theorem sub4_104 : sub4 [4, 2] = true := by decide +kernel
theorem sub4_105 : sub4 [4, 3] = true := by decide +kernel
theorem sub4_106 : sub4 [4, 4] = true := by decide +kernel
theorem sub4_107 : sub4 [5, -3] = true := by decide +kernel
theorem sub4_108 : sub4 [5, -2] = true := by decide +kernel
theorem sub4_109 : sub4 [5, -1] = true := by decide +kernel
theorem sub4_110 : sub4 [5, 0] = true := by decide +kernel
theorem sub4_111 : sub4 [5, 1] = true := by decide +kernel
theorem sub4_112 : sub4 [5, 2] = true := by decide +kernel
theorem sub4_113 : sub4 [5, 3] = true := by decide +kernel
theorem sub4_114 : sub4 [5, 4] = true := by decide +kernel
theorem sub4_115 : sub4 [6] = true := by decide +kernel
theorem sb4_3 : ∀ q ∈ blk4_3, sub4 q = true := by
  unfold blk4_3
  exact List.forall_mem_cons.2 ⟨sub4_96, List.forall_mem_cons.2 ⟨sub4_97, List.forall_mem_cons.2 ⟨sub4_98, List.forall_mem_cons.2 ⟨sub4_99, List.forall_mem_cons.2 ⟨sub4_100, List.forall_mem_cons.2 ⟨sub4_101, List.forall_mem_cons.2 ⟨sub4_102, List.forall_mem_cons.2 ⟨sub4_103, List.forall_mem_cons.2 ⟨sub4_104, List.forall_mem_cons.2 ⟨sub4_105, List.forall_mem_cons.2 ⟨sub4_106, List.forall_mem_cons.2 ⟨sub4_107, List.forall_mem_cons.2 ⟨sub4_108, List.forall_mem_cons.2 ⟨sub4_109, List.forall_mem_cons.2 ⟨sub4_110, List.forall_mem_cons.2 ⟨sub4_111, List.forall_mem_cons.2 ⟨sub4_112, List.forall_mem_cons.2 ⟨sub4_113, List.forall_mem_cons.2 ⟨sub4_114, List.forall_mem_cons.2 ⟨sub4_115, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C120
