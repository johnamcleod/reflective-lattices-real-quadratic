import ReflectZphi.Data.Cert5.C104.Base

namespace ReflectZphi.Data.Cert5.C104
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub4_64 : sub4 [0, -3] = true := by decide +kernel
theorem sub4_65 : sub4 [0, -2] = true := by decide +kernel
theorem sub4_66 : sub4 [0, -1] = true := by decide +kernel
theorem sub4_67 : sub4 [0, 0] = true := by decide +kernel
theorem sub4_68 : sub4 [0, 1] = true := by decide +kernel
theorem sub4_69 : sub4 [0, 2] = true := by decide +kernel
theorem sub4_70 : sub4 [0, 3] = true := by decide +kernel
theorem sub4_71 : sub4 [0, 4] = true := by decide +kernel
theorem sub4_72 : sub4 [0, 5] = true := by decide +kernel
theorem sub4_73 : sub4 [0, 6] = true := by decide +kernel
theorem sub4_74 : sub4 [1, -7] = true := by decide +kernel
theorem sub4_75 : sub4 [1, -6] = true := by decide +kernel
theorem sub4_76 : sub4 [1, -5] = true := by decide +kernel
theorem sub4_77 : sub4 [1, -4] = true := by decide +kernel
theorem sub4_78 : sub4 [1, -3] = true := by decide +kernel
theorem sub4_79 : sub4 [1, -2] = true := by decide +kernel
theorem sub4_80 : sub4 [1, -1] = true := by decide +kernel
theorem sub4_81 : sub4 [1, 0] = true := by decide +kernel
theorem sub4_82 : sub4 [1, 1] = true := by decide +kernel
theorem sub4_83 : sub4 [1, 2] = true := by decide +kernel
theorem sub4_84 : sub4 [1, 3] = true := by decide +kernel
theorem sub4_85 : sub4 [1, 4] = true := by decide +kernel
theorem sub4_86 : sub4 [1, 5] = true := by decide +kernel
theorem sub4_87 : sub4 [1, 6] = true := by decide +kernel
theorem sub4_88 : sub4 [2, -7] = true := by decide +kernel
theorem sub4_89 : sub4 [2, -6] = true := by decide +kernel
theorem sub4_90 : sub4 [2, -5] = true := by decide +kernel
theorem sub4_91 : sub4 [2, -4] = true := by decide +kernel
theorem sub4_92 : sub4 [2, -3] = true := by decide +kernel
theorem sub4_93 : sub4 [2, -2] = true := by decide +kernel
theorem sub4_94 : sub4 [2, -1] = true := by decide +kernel
theorem sub4_95 : sub4 [2, 0] = true := by decide +kernel
theorem sb4_2 : ∀ q ∈ blk4_2, sub4 q = true := by
  unfold blk4_2
  exact List.forall_mem_cons.2 ⟨sub4_64, List.forall_mem_cons.2 ⟨sub4_65, List.forall_mem_cons.2 ⟨sub4_66, List.forall_mem_cons.2 ⟨sub4_67, List.forall_mem_cons.2 ⟨sub4_68, List.forall_mem_cons.2 ⟨sub4_69, List.forall_mem_cons.2 ⟨sub4_70, List.forall_mem_cons.2 ⟨sub4_71, List.forall_mem_cons.2 ⟨sub4_72, List.forall_mem_cons.2 ⟨sub4_73, List.forall_mem_cons.2 ⟨sub4_74, List.forall_mem_cons.2 ⟨sub4_75, List.forall_mem_cons.2 ⟨sub4_76, List.forall_mem_cons.2 ⟨sub4_77, List.forall_mem_cons.2 ⟨sub4_78, List.forall_mem_cons.2 ⟨sub4_79, List.forall_mem_cons.2 ⟨sub4_80, List.forall_mem_cons.2 ⟨sub4_81, List.forall_mem_cons.2 ⟨sub4_82, List.forall_mem_cons.2 ⟨sub4_83, List.forall_mem_cons.2 ⟨sub4_84, List.forall_mem_cons.2 ⟨sub4_85, List.forall_mem_cons.2 ⟨sub4_86, List.forall_mem_cons.2 ⟨sub4_87, List.forall_mem_cons.2 ⟨sub4_88, List.forall_mem_cons.2 ⟨sub4_89, List.forall_mem_cons.2 ⟨sub4_90, List.forall_mem_cons.2 ⟨sub4_91, List.forall_mem_cons.2 ⟨sub4_92, List.forall_mem_cons.2 ⟨sub4_93, List.forall_mem_cons.2 ⟨sub4_94, List.forall_mem_cons.2 ⟨sub4_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_96 : sub4 [2, 1] = true := by decide +kernel
theorem sub4_97 : sub4 [2, 2] = true := by decide +kernel
theorem sub4_98 : sub4 [2, 3] = true := by decide +kernel
theorem sub4_99 : sub4 [2, 4] = true := by decide +kernel
theorem sub4_100 : sub4 [2, 5] = true := by decide +kernel
theorem sub4_101 : sub4 [3, -6] = true := by decide +kernel
theorem sub4_102 : sub4 [3, -5] = true := by decide +kernel
theorem sub4_103 : sub4 [3, -4] = true := by decide +kernel
theorem sub4_104 : sub4 [3, -3] = true := by decide +kernel
theorem sub4_105 : sub4 [3, -2] = true := by decide +kernel
theorem sub4_106 : sub4 [3, -1] = true := by decide +kernel
theorem sub4_107 : sub4 [3, 0] = true := by decide +kernel
theorem sub4_108 : sub4 [3, 1] = true := by decide +kernel
theorem sub4_109 : sub4 [3, 2] = true := by decide +kernel
theorem sub4_110 : sub4 [3, 3] = true := by decide +kernel
theorem sub4_111 : sub4 [3, 4] = true := by decide +kernel
theorem sub4_112 : sub4 [3, 5] = true := by decide +kernel
theorem sub4_113 : sub4 [4, -6] = true := by decide +kernel
theorem sub4_114 : sub4 [4, -5] = true := by decide +kernel
theorem sub4_115 : sub4 [4, -4] = true := by decide +kernel
theorem sub4_116 : sub4 [4, -3] = true := by decide +kernel
theorem sub4_117 : sub4 [4, -2] = true := by decide +kernel
theorem sub4_118 : sub4 [4, -1] = true := by decide +kernel
theorem sub4_119 : sub4 [4, 0] = true := by decide +kernel
theorem sub4_120 : sub4 [4, 1] = true := by decide +kernel
theorem sub4_121 : sub4 [4, 2] = true := by decide +kernel
theorem sub4_122 : sub4 [4, 3] = true := by decide +kernel
theorem sub4_123 : sub4 [4, 4] = true := by decide +kernel
theorem sub4_124 : sub4 [5, -5] = true := by decide +kernel
theorem sub4_125 : sub4 [5, -4] = true := by decide +kernel
theorem sub4_126 : sub4 [5, -3] = true := by decide +kernel
theorem sub4_127 : sub4 [5, -2] = true := by decide +kernel
theorem sb4_3 : ∀ q ∈ blk4_3, sub4 q = true := by
  unfold blk4_3
  exact List.forall_mem_cons.2 ⟨sub4_96, List.forall_mem_cons.2 ⟨sub4_97, List.forall_mem_cons.2 ⟨sub4_98, List.forall_mem_cons.2 ⟨sub4_99, List.forall_mem_cons.2 ⟨sub4_100, List.forall_mem_cons.2 ⟨sub4_101, List.forall_mem_cons.2 ⟨sub4_102, List.forall_mem_cons.2 ⟨sub4_103, List.forall_mem_cons.2 ⟨sub4_104, List.forall_mem_cons.2 ⟨sub4_105, List.forall_mem_cons.2 ⟨sub4_106, List.forall_mem_cons.2 ⟨sub4_107, List.forall_mem_cons.2 ⟨sub4_108, List.forall_mem_cons.2 ⟨sub4_109, List.forall_mem_cons.2 ⟨sub4_110, List.forall_mem_cons.2 ⟨sub4_111, List.forall_mem_cons.2 ⟨sub4_112, List.forall_mem_cons.2 ⟨sub4_113, List.forall_mem_cons.2 ⟨sub4_114, List.forall_mem_cons.2 ⟨sub4_115, List.forall_mem_cons.2 ⟨sub4_116, List.forall_mem_cons.2 ⟨sub4_117, List.forall_mem_cons.2 ⟨sub4_118, List.forall_mem_cons.2 ⟨sub4_119, List.forall_mem_cons.2 ⟨sub4_120, List.forall_mem_cons.2 ⟨sub4_121, List.forall_mem_cons.2 ⟨sub4_122, List.forall_mem_cons.2 ⟨sub4_123, List.forall_mem_cons.2 ⟨sub4_124, List.forall_mem_cons.2 ⟨sub4_125, List.forall_mem_cons.2 ⟨sub4_126, List.forall_mem_cons.2 ⟨sub4_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_128 : sub4 [5, -1] = true := by decide +kernel
theorem sub4_129 : sub4 [5, 0] = true := by decide +kernel
theorem sub4_130 : sub4 [5, 1] = true := by decide +kernel
theorem sub4_131 : sub4 [5, 2] = true := by decide +kernel
theorem sub4_132 : sub4 [5, 3] = true := by decide +kernel
theorem sub4_133 : sub4 [6] = true := by decide +kernel
theorem sb4_4 : ∀ q ∈ blk4_4, sub4 q = true := by
  unfold blk4_4
  exact List.forall_mem_cons.2 ⟨sub4_128, List.forall_mem_cons.2 ⟨sub4_129, List.forall_mem_cons.2 ⟨sub4_130, List.forall_mem_cons.2 ⟨sub4_131, List.forall_mem_cons.2 ⟨sub4_132, List.forall_mem_cons.2 ⟨sub4_133, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem sub5_0 : sub5 [-5] = true := by decide +kernel
theorem sub5_1 : sub5 [-4, -6] = true := by decide +kernel
theorem sub5_2 : sub5 [-4, -5] = true := by decide +kernel
theorem sub5_3 : sub5 [-4, -4] = true := by decide +kernel
theorem sub5_4 : sub5 [-4, -3] = true := by decide +kernel
theorem sub5_5 : sub5 [-4, -2] = true := by decide +kernel
theorem sub5_6 : sub5 [-4, -1] = true := by decide +kernel
theorem sub5_7 : sub5 [-4, 0] = true := by decide +kernel
theorem sub5_8 : sub5 [-4, 1] = true := by decide +kernel
theorem sub5_9 : sub5 [-4, 2] = true := by decide +kernel
theorem sub5_10 : sub5 [-3, -6] = true := by decide +kernel
theorem sub5_11 : sub5 [-3, -5] = true := by decide +kernel
theorem sub5_12 : sub5 [-3, -4] = true := by decide +kernel
theorem sub5_13 : sub5 [-3, -3, -9] = true := by decide +kernel
theorem sub5_14 : sub5 [-3, -3, -8] = true := by decide +kernel
theorem sub5_15 : sub5 [-3, -3, -7] = true := by decide +kernel
theorem sub5_16 : sub5 [-3, -3, -6] = true := by decide +kernel
theorem sub5_17 : sub5 [-3, -3, -5] = true := by decide +kernel
theorem sub5_18 : sub5 [-3, -3, -4] = true := by decide +kernel
theorem sub5_19 : sub5 [-3, -3, -3] = true := by decide +kernel
theorem sub5_20 : sub5 [-3, -3, -2] = true := by decide +kernel
theorem sub5_21 : sub5 [-3, -3, -1] = true := by decide +kernel
theorem sub5_22 : sub5 [-3, -3, 0] = true := by decide +kernel
theorem sub5_23 : sub5 [-3, -3, 1] = true := by decide +kernel
theorem sub5_24 : sub5 [-3, -3, 2] = true := by decide +kernel
theorem sub5_25 : sub5 [-3, -3, 3] = true := by decide +kernel
theorem sub5_26 : sub5 [-3, -3, 4] = true := by decide +kernel
theorem sub5_27 : sub5 [-3, -3, 5] = true := by decide +kernel
theorem sub5_28 : sub5 [-3, -2, -9] = true := by decide +kernel
theorem sub5_29 : sub5 [-3, -2, -8] = true := by decide +kernel
theorem sub5_30 : sub5 [-3, -2, -7] = true := by decide +kernel
theorem sub5_31 : sub5 [-3, -2, -6] = true := by decide +kernel
theorem sb5_0 : ∀ q ∈ blk5_0, sub5 q = true := by
  unfold blk5_0
  exact List.forall_mem_cons.2 ⟨sub5_0, List.forall_mem_cons.2 ⟨sub5_1, List.forall_mem_cons.2 ⟨sub5_2, List.forall_mem_cons.2 ⟨sub5_3, List.forall_mem_cons.2 ⟨sub5_4, List.forall_mem_cons.2 ⟨sub5_5, List.forall_mem_cons.2 ⟨sub5_6, List.forall_mem_cons.2 ⟨sub5_7, List.forall_mem_cons.2 ⟨sub5_8, List.forall_mem_cons.2 ⟨sub5_9, List.forall_mem_cons.2 ⟨sub5_10, List.forall_mem_cons.2 ⟨sub5_11, List.forall_mem_cons.2 ⟨sub5_12, List.forall_mem_cons.2 ⟨sub5_13, List.forall_mem_cons.2 ⟨sub5_14, List.forall_mem_cons.2 ⟨sub5_15, List.forall_mem_cons.2 ⟨sub5_16, List.forall_mem_cons.2 ⟨sub5_17, List.forall_mem_cons.2 ⟨sub5_18, List.forall_mem_cons.2 ⟨sub5_19, List.forall_mem_cons.2 ⟨sub5_20, List.forall_mem_cons.2 ⟨sub5_21, List.forall_mem_cons.2 ⟨sub5_22, List.forall_mem_cons.2 ⟨sub5_23, List.forall_mem_cons.2 ⟨sub5_24, List.forall_mem_cons.2 ⟨sub5_25, List.forall_mem_cons.2 ⟨sub5_26, List.forall_mem_cons.2 ⟨sub5_27, List.forall_mem_cons.2 ⟨sub5_28, List.forall_mem_cons.2 ⟨sub5_29, List.forall_mem_cons.2 ⟨sub5_30, List.forall_mem_cons.2 ⟨sub5_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_32 : sub5 [-3, -2, -5] = true := by decide +kernel
theorem sub5_33 : sub5 [-3, -2, -4] = true := by decide +kernel
theorem sub5_34 : sub5 [-3, -2, -3] = true := by decide +kernel
theorem sub5_35 : sub5 [-3, -2, -2] = true := by decide +kernel
theorem sub5_36 : sub5 [-3, -2, -1] = true := by decide +kernel
theorem sub5_37 : sub5 [-3, -2, 0] = true := by decide +kernel
theorem sub5_38 : sub5 [-3, -2, 1] = true := by decide +kernel
theorem sub5_39 : sub5 [-3, -2, 2] = true := by decide +kernel
theorem sub5_40 : sub5 [-3, -2, 3] = true := by decide +kernel
theorem sub5_41 : sub5 [-3, -2, 4] = true := by decide +kernel
theorem sub5_42 : sub5 [-3, -2, 5] = true := by decide +kernel
theorem sub5_43 : sub5 [-3, -1, -9] = true := by decide +kernel
theorem sub5_44 : sub5 [-3, -1, -8] = true := by decide +kernel
theorem sub5_45 : sub5 [-3, -1, -7] = true := by decide +kernel
theorem sub5_46 : sub5 [-3, -1, -6] = true := by decide +kernel
theorem sub5_47 : sub5 [-3, -1, -5] = true := by decide +kernel
theorem sub5_48 : sub5 [-3, -1, -4] = true := by decide +kernel
theorem sub5_49 : sub5 [-3, -1, -3] = true := by decide +kernel
theorem sub5_50 : sub5 [-3, -1, -2] = true := by decide +kernel
theorem sub5_51 : sub5 [-3, -1, -1] = true := by decide +kernel
theorem sub5_52 : sub5 [-3, -1, 0] = true := by decide +kernel
theorem sub5_53 : sub5 [-3, -1, 1] = true := by decide +kernel
theorem sub5_54 : sub5 [-3, -1, 2] = true := by decide +kernel
theorem sub5_55 : sub5 [-3, -1, 3] = true := by decide +kernel
theorem sub5_56 : sub5 [-3, -1, 4] = true := by decide +kernel
theorem sub5_57 : sub5 [-3, -1, 5] = true := by decide +kernel
theorem sub5_58 : sub5 [-3, -1, 6] = true := by decide +kernel
theorem sub5_59 : sub5 [-3, 0, -8] = true := by decide +kernel
theorem sub5_60 : sub5 [-3, 0, -7] = true := by decide +kernel
theorem sub5_61 : sub5 [-3, 0, -6] = true := by decide +kernel
theorem sub5_62 : sub5 [-3, 0, -5] = true := by decide +kernel
theorem sub5_63 : sub5 [-3, 0, -4] = true := by decide +kernel
theorem sb5_1 : ∀ q ∈ blk5_1, sub5 q = true := by
  unfold blk5_1
  exact List.forall_mem_cons.2 ⟨sub5_32, List.forall_mem_cons.2 ⟨sub5_33, List.forall_mem_cons.2 ⟨sub5_34, List.forall_mem_cons.2 ⟨sub5_35, List.forall_mem_cons.2 ⟨sub5_36, List.forall_mem_cons.2 ⟨sub5_37, List.forall_mem_cons.2 ⟨sub5_38, List.forall_mem_cons.2 ⟨sub5_39, List.forall_mem_cons.2 ⟨sub5_40, List.forall_mem_cons.2 ⟨sub5_41, List.forall_mem_cons.2 ⟨sub5_42, List.forall_mem_cons.2 ⟨sub5_43, List.forall_mem_cons.2 ⟨sub5_44, List.forall_mem_cons.2 ⟨sub5_45, List.forall_mem_cons.2 ⟨sub5_46, List.forall_mem_cons.2 ⟨sub5_47, List.forall_mem_cons.2 ⟨sub5_48, List.forall_mem_cons.2 ⟨sub5_49, List.forall_mem_cons.2 ⟨sub5_50, List.forall_mem_cons.2 ⟨sub5_51, List.forall_mem_cons.2 ⟨sub5_52, List.forall_mem_cons.2 ⟨sub5_53, List.forall_mem_cons.2 ⟨sub5_54, List.forall_mem_cons.2 ⟨sub5_55, List.forall_mem_cons.2 ⟨sub5_56, List.forall_mem_cons.2 ⟨sub5_57, List.forall_mem_cons.2 ⟨sub5_58, List.forall_mem_cons.2 ⟨sub5_59, List.forall_mem_cons.2 ⟨sub5_60, List.forall_mem_cons.2 ⟨sub5_61, List.forall_mem_cons.2 ⟨sub5_62, List.forall_mem_cons.2 ⟨sub5_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_64 : sub5 [-3, 0, -3] = true := by decide +kernel
theorem sub5_65 : sub5 [-3, 0, -2] = true := by decide +kernel
theorem sub5_66 : sub5 [-3, 0, -1] = true := by decide +kernel
theorem sub5_67 : sub5 [-3, 0, 0] = true := by decide +kernel
theorem sub5_68 : sub5 [-3, 0, 1] = true := by decide +kernel
theorem sub5_69 : sub5 [-3, 0, 2] = true := by decide +kernel
theorem sub5_70 : sub5 [-3, 0, 3] = true := by decide +kernel
theorem sub5_71 : sub5 [-3, 0, 4] = true := by decide +kernel
theorem sub5_72 : sub5 [-3, 0, 5] = true := by decide +kernel
theorem sub5_73 : sub5 [-3, 0, 6] = true := by decide +kernel
theorem sub5_74 : sub5 [-3, 1] = true := by decide +kernel
theorem sub5_75 : sub5 [-3, 2] = true := by decide +kernel
theorem sub5_76 : sub5 [-3, 3] = true := by decide +kernel
theorem sub5_77 : sub5 [-2, -6] = true := by decide +kernel
theorem sub5_78 : sub5 [-2, -5] = true := by decide +kernel
theorem sub5_79 : sub5 [-2, -4] = true := by decide +kernel
theorem sub5_80 : sub5 [-2, -3, -9] = true := by decide +kernel
theorem sub5_81 : sub5 [-2, -3, -8] = true := by decide +kernel
theorem sub5_82 : sub5 [-2, -3, -7] = true := by decide +kernel
theorem sub5_83 : sub5 [-2, -3, -6] = true := by decide +kernel
theorem sub5_84 : sub5 [-2, -3, -5] = true := by decide +kernel
theorem sub5_85 : sub5 [-2, -3, -4] = true := by decide +kernel
theorem sub5_86 : sub5 [-2, -3, -3] = true := by decide +kernel
theorem sub5_87 : sub5 [-2, -3, -2] = true := by decide +kernel
theorem sub5_88 : sub5 [-2, -3, -1] = true := by decide +kernel
theorem sub5_89 : sub5 [-2, -3, 0] = true := by decide +kernel
theorem sub5_90 : sub5 [-2, -3, 1] = true := by decide +kernel
theorem sub5_91 : sub5 [-2, -3, 2] = true := by decide +kernel
theorem sub5_92 : sub5 [-2, -3, 3] = true := by decide +kernel
theorem sub5_93 : sub5 [-2, -3, 4] = true := by decide +kernel
theorem sub5_94 : sub5 [-2, -3, 5] = true := by decide +kernel
theorem sub5_95 : sub5 [-2, -3, 6] = true := by decide +kernel
theorem sb5_2 : ∀ q ∈ blk5_2, sub5 q = true := by
  unfold blk5_2
  exact List.forall_mem_cons.2 ⟨sub5_64, List.forall_mem_cons.2 ⟨sub5_65, List.forall_mem_cons.2 ⟨sub5_66, List.forall_mem_cons.2 ⟨sub5_67, List.forall_mem_cons.2 ⟨sub5_68, List.forall_mem_cons.2 ⟨sub5_69, List.forall_mem_cons.2 ⟨sub5_70, List.forall_mem_cons.2 ⟨sub5_71, List.forall_mem_cons.2 ⟨sub5_72, List.forall_mem_cons.2 ⟨sub5_73, List.forall_mem_cons.2 ⟨sub5_74, List.forall_mem_cons.2 ⟨sub5_75, List.forall_mem_cons.2 ⟨sub5_76, List.forall_mem_cons.2 ⟨sub5_77, List.forall_mem_cons.2 ⟨sub5_78, List.forall_mem_cons.2 ⟨sub5_79, List.forall_mem_cons.2 ⟨sub5_80, List.forall_mem_cons.2 ⟨sub5_81, List.forall_mem_cons.2 ⟨sub5_82, List.forall_mem_cons.2 ⟨sub5_83, List.forall_mem_cons.2 ⟨sub5_84, List.forall_mem_cons.2 ⟨sub5_85, List.forall_mem_cons.2 ⟨sub5_86, List.forall_mem_cons.2 ⟨sub5_87, List.forall_mem_cons.2 ⟨sub5_88, List.forall_mem_cons.2 ⟨sub5_89, List.forall_mem_cons.2 ⟨sub5_90, List.forall_mem_cons.2 ⟨sub5_91, List.forall_mem_cons.2 ⟨sub5_92, List.forall_mem_cons.2 ⟨sub5_93, List.forall_mem_cons.2 ⟨sub5_94, List.forall_mem_cons.2 ⟨sub5_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_96 : sub5 [-2, -2, -9] = true := by decide +kernel
theorem sub5_97 : sub5 [-2, -2, -8] = true := by decide +kernel
theorem sub5_98 : sub5 [-2, -2, -7] = true := by decide +kernel
theorem sub5_99 : sub5 [-2, -2, -6] = true := by decide +kernel
theorem sub5_100 : sub5 [-2, -2, -5] = true := by decide +kernel
theorem sub5_101 : sub5 [-2, -2, -4] = true := by decide +kernel
theorem sub5_102 : sub5 [-2, -2, -3] = true := by decide +kernel
theorem sub5_103 : sub5 [-2, -2, -2] = true := by decide +kernel
theorem sub5_104 : sub5 [-2, -2, -1] = true := by decide +kernel
theorem sub5_105 : sub5 [-2, -2, 0] = true := by decide +kernel
theorem sub5_106 : sub5 [-2, -2, 1] = true := by decide +kernel
theorem sub5_107 : sub5 [-2, -2, 2] = true := by decide +kernel
theorem sub5_108 : sub5 [-2, -2, 3] = true := by decide +kernel
theorem sub5_109 : sub5 [-2, -2, 4] = true := by decide +kernel
theorem sub5_110 : sub5 [-2, -2, 5] = true := by decide +kernel
theorem sub5_111 : sub5 [-2, -2, 6] = true := by decide +kernel
theorem sub5_112 : sub5 [-2, -1, -9] = true := by decide +kernel
theorem sub5_113 : sub5 [-2, -1, -8] = true := by decide +kernel
theorem sub5_114 : sub5 [-2, -1, -7] = true := by decide +kernel
theorem sub5_115 : sub5 [-2, -1, -6] = true := by decide +kernel
theorem sub5_116 : sub5 [-2, -1, -5] = true := by decide +kernel
theorem sub5_117 : sub5 [-2, -1, -4] = true := by decide +kernel
theorem sub5_118 : sub5 [-2, -1, -3] = true := by decide +kernel
theorem sub5_119 : sub5 [-2, -1, -2] = true := by decide +kernel
theorem sub5_120 : sub5 [-2, -1, -1] = true := by decide +kernel
theorem sub5_121 : sub5 [-2, -1, 0] = true := by decide +kernel
theorem sub5_122 : sub5 [-2, -1, 1] = true := by decide +kernel
theorem sub5_123 : sub5 [-2, -1, 2] = true := by decide +kernel
theorem sub5_124 : sub5 [-2, -1, 3] = true := by decide +kernel
theorem sub5_125 : sub5 [-2, -1, 4] = true := by decide +kernel
theorem sub5_126 : sub5 [-2, -1, 5] = true := by decide +kernel
theorem sub5_127 : sub5 [-2, -1, 6] = true := by decide +kernel
theorem sb5_3 : ∀ q ∈ blk5_3, sub5 q = true := by
  unfold blk5_3
  exact List.forall_mem_cons.2 ⟨sub5_96, List.forall_mem_cons.2 ⟨sub5_97, List.forall_mem_cons.2 ⟨sub5_98, List.forall_mem_cons.2 ⟨sub5_99, List.forall_mem_cons.2 ⟨sub5_100, List.forall_mem_cons.2 ⟨sub5_101, List.forall_mem_cons.2 ⟨sub5_102, List.forall_mem_cons.2 ⟨sub5_103, List.forall_mem_cons.2 ⟨sub5_104, List.forall_mem_cons.2 ⟨sub5_105, List.forall_mem_cons.2 ⟨sub5_106, List.forall_mem_cons.2 ⟨sub5_107, List.forall_mem_cons.2 ⟨sub5_108, List.forall_mem_cons.2 ⟨sub5_109, List.forall_mem_cons.2 ⟨sub5_110, List.forall_mem_cons.2 ⟨sub5_111, List.forall_mem_cons.2 ⟨sub5_112, List.forall_mem_cons.2 ⟨sub5_113, List.forall_mem_cons.2 ⟨sub5_114, List.forall_mem_cons.2 ⟨sub5_115, List.forall_mem_cons.2 ⟨sub5_116, List.forall_mem_cons.2 ⟨sub5_117, List.forall_mem_cons.2 ⟨sub5_118, List.forall_mem_cons.2 ⟨sub5_119, List.forall_mem_cons.2 ⟨sub5_120, List.forall_mem_cons.2 ⟨sub5_121, List.forall_mem_cons.2 ⟨sub5_122, List.forall_mem_cons.2 ⟨sub5_123, List.forall_mem_cons.2 ⟨sub5_124, List.forall_mem_cons.2 ⟨sub5_125, List.forall_mem_cons.2 ⟨sub5_126, List.forall_mem_cons.2 ⟨sub5_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C104
