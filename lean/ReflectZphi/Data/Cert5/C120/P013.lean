import ReflectZphi.Data.Cert5.C120.Base

namespace ReflectZphi.Data.Cert5.C120
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub11_0 : sub11 [-6] = true := by decide +kernel
theorem sub11_1 : sub11 [-5, -5] = true := by decide +kernel
theorem sub11_2 : sub11 [-5, -4] = true := by decide +kernel
theorem sub11_3 : sub11 [-5, -3] = true := by decide +kernel
theorem sub11_4 : sub11 [-5, -2] = true := by decide +kernel
theorem sub11_5 : sub11 [-5, -1] = true := by decide +kernel
theorem sub11_6 : sub11 [-5, 0] = true := by decide +kernel
theorem sub11_7 : sub11 [-5, 1] = true := by decide +kernel
theorem sub11_8 : sub11 [-5, 2] = true := by decide +kernel
theorem sub11_9 : sub11 [-5, 3] = true := by decide +kernel
theorem sub11_10 : sub11 [-5, 4] = true := by decide +kernel
theorem sub11_11 : sub11 [-4, -7] = true := by decide +kernel
theorem sub11_12 : sub11 [-4, -6] = true := by decide +kernel
theorem sub11_13 : sub11 [-4, -5] = true := by decide +kernel
theorem sub11_14 : sub11 [-4, -4] = true := by decide +kernel
theorem sub11_15 : sub11 [-4, -3] = true := by decide +kernel
theorem sub11_16 : sub11 [-4, -2] = true := by decide +kernel
theorem sub11_17 : sub11 [-4, -1] = true := by decide +kernel
theorem sub11_18 : sub11 [-4, 0] = true := by decide +kernel
theorem sub11_19 : sub11 [-4, 1] = true := by decide +kernel
theorem sub11_20 : sub11 [-4, 2] = true := by decide +kernel
theorem sub11_21 : sub11 [-4, 3] = true := by decide +kernel
theorem sub11_22 : sub11 [-4, 4] = true := by decide +kernel
theorem sub11_23 : sub11 [-4, 5] = true := by decide +kernel
theorem sub11_24 : sub11 [-3, -7] = true := by decide +kernel
theorem sub11_25 : sub11 [-3, -6] = true := by decide +kernel
theorem sub11_26 : sub11 [-3, -5] = true := by decide +kernel
theorem sub11_27 : sub11 [-3, -4] = true := by decide +kernel
theorem sub11_28 : sub11 [-3, -3] = true := by decide +kernel
theorem sub11_29 : sub11 [-3, -2] = true := by decide +kernel
theorem sub11_30 : sub11 [-3, -1] = true := by decide +kernel
theorem sub11_31 : sub11 [-3, 0] = true := by decide +kernel
theorem sb11_0 : ∀ q ∈ blk11_0, sub11 q = true := by
  unfold blk11_0
  exact List.forall_mem_cons.2 ⟨sub11_0, List.forall_mem_cons.2 ⟨sub11_1, List.forall_mem_cons.2 ⟨sub11_2, List.forall_mem_cons.2 ⟨sub11_3, List.forall_mem_cons.2 ⟨sub11_4, List.forall_mem_cons.2 ⟨sub11_5, List.forall_mem_cons.2 ⟨sub11_6, List.forall_mem_cons.2 ⟨sub11_7, List.forall_mem_cons.2 ⟨sub11_8, List.forall_mem_cons.2 ⟨sub11_9, List.forall_mem_cons.2 ⟨sub11_10, List.forall_mem_cons.2 ⟨sub11_11, List.forall_mem_cons.2 ⟨sub11_12, List.forall_mem_cons.2 ⟨sub11_13, List.forall_mem_cons.2 ⟨sub11_14, List.forall_mem_cons.2 ⟨sub11_15, List.forall_mem_cons.2 ⟨sub11_16, List.forall_mem_cons.2 ⟨sub11_17, List.forall_mem_cons.2 ⟨sub11_18, List.forall_mem_cons.2 ⟨sub11_19, List.forall_mem_cons.2 ⟨sub11_20, List.forall_mem_cons.2 ⟨sub11_21, List.forall_mem_cons.2 ⟨sub11_22, List.forall_mem_cons.2 ⟨sub11_23, List.forall_mem_cons.2 ⟨sub11_24, List.forall_mem_cons.2 ⟨sub11_25, List.forall_mem_cons.2 ⟨sub11_26, List.forall_mem_cons.2 ⟨sub11_27, List.forall_mem_cons.2 ⟨sub11_28, List.forall_mem_cons.2 ⟨sub11_29, List.forall_mem_cons.2 ⟨sub11_30, List.forall_mem_cons.2 ⟨sub11_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub11_32 : sub11 [-3, 1] = true := by decide +kernel
theorem sub11_33 : sub11 [-3, 2] = true := by decide +kernel
theorem sub11_34 : sub11 [-3, 3] = true := by decide +kernel
theorem sub11_35 : sub11 [-3, 4] = true := by decide +kernel
theorem sub11_36 : sub11 [-3, 5] = true := by decide +kernel
theorem sub11_37 : sub11 [-3, 6] = true := by decide +kernel
theorem sub11_38 : sub11 [-2, -8] = true := by decide +kernel
theorem sub11_39 : sub11 [-2, -7] = true := by decide +kernel
theorem sub11_40 : sub11 [-2, -6] = true := by decide +kernel
theorem sub11_41 : sub11 [-2, -5] = true := by decide +kernel
theorem sub11_42 : sub11 [-2, -4] = true := by decide +kernel
theorem sub11_43 : sub11 [-2, -3] = true := by decide +kernel
theorem sub11_44 : sub11 [-2, -2, -8] = true := by decide +kernel
theorem sub11_45 : sub11 [-2, -2, -7] = true := by decide +kernel
theorem sub11_46 : sub11 [-2, -2, -6] = true := by decide +kernel
theorem sub11_47 : sub11 [-2, -2, -5] = true := by decide +kernel
theorem sub11_48 : sub11 [-2, -2, -4] = true := by decide +kernel
theorem sub11_49 : sub11 [-2, -2, -3] = true := by decide +kernel
theorem sub11_50 : sub11 [-2, -2, -2] = true := by decide +kernel
theorem sub11_51 : sub11 [-2, -2, -1] = true := by decide +kernel
theorem sub11_52 : sub11 [-2, -2, 0] = true := by decide +kernel
theorem sub11_53 : sub11 [-2, -2, 1] = true := by decide +kernel
theorem sub11_54 : sub11 [-2, -2, 2] = true := by decide +kernel
theorem sub11_55 : sub11 [-2, -2, 3] = true := by decide +kernel
theorem sub11_56 : sub11 [-2, -2, 4] = true := by decide +kernel
theorem sub11_57 : sub11 [-2, -1, -8] = true := by decide +kernel
theorem sub11_58 : sub11 [-2, -1, -7] = true := by decide +kernel
theorem sub11_59 : sub11 [-2, -1, -6] = true := by decide +kernel
theorem sub11_60 : sub11 [-2, -1, -5] = true := by decide +kernel
theorem sub11_61 : sub11 [-2, -1, -4] = true := by decide +kernel
theorem sub11_62 : sub11 [-2, -1, -3] = true := by decide +kernel
theorem sub11_63 : sub11 [-2, -1, -2] = true := by decide +kernel
theorem sb11_1 : ∀ q ∈ blk11_1, sub11 q = true := by
  unfold blk11_1
  exact List.forall_mem_cons.2 ⟨sub11_32, List.forall_mem_cons.2 ⟨sub11_33, List.forall_mem_cons.2 ⟨sub11_34, List.forall_mem_cons.2 ⟨sub11_35, List.forall_mem_cons.2 ⟨sub11_36, List.forall_mem_cons.2 ⟨sub11_37, List.forall_mem_cons.2 ⟨sub11_38, List.forall_mem_cons.2 ⟨sub11_39, List.forall_mem_cons.2 ⟨sub11_40, List.forall_mem_cons.2 ⟨sub11_41, List.forall_mem_cons.2 ⟨sub11_42, List.forall_mem_cons.2 ⟨sub11_43, List.forall_mem_cons.2 ⟨sub11_44, List.forall_mem_cons.2 ⟨sub11_45, List.forall_mem_cons.2 ⟨sub11_46, List.forall_mem_cons.2 ⟨sub11_47, List.forall_mem_cons.2 ⟨sub11_48, List.forall_mem_cons.2 ⟨sub11_49, List.forall_mem_cons.2 ⟨sub11_50, List.forall_mem_cons.2 ⟨sub11_51, List.forall_mem_cons.2 ⟨sub11_52, List.forall_mem_cons.2 ⟨sub11_53, List.forall_mem_cons.2 ⟨sub11_54, List.forall_mem_cons.2 ⟨sub11_55, List.forall_mem_cons.2 ⟨sub11_56, List.forall_mem_cons.2 ⟨sub11_57, List.forall_mem_cons.2 ⟨sub11_58, List.forall_mem_cons.2 ⟨sub11_59, List.forall_mem_cons.2 ⟨sub11_60, List.forall_mem_cons.2 ⟨sub11_61, List.forall_mem_cons.2 ⟨sub11_62, List.forall_mem_cons.2 ⟨sub11_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub11_64 : sub11 [-2, -1, -1] = true := by decide +kernel
theorem sub11_65 : sub11 [-2, -1, 0] = true := by decide +kernel
theorem sub11_66 : sub11 [-2, -1, 1] = true := by decide +kernel
theorem sub11_67 : sub11 [-2, -1, 2] = true := by decide +kernel
theorem sub11_68 : sub11 [-2, -1, 3] = true := by decide +kernel
theorem sub11_69 : sub11 [-2, -1, 4] = true := by decide +kernel
theorem sub11_70 : sub11 [-2, -1, 5] = true := by decide +kernel
theorem sub11_71 : sub11 [-2, 0, -8] = true := by decide +kernel
theorem sub11_72 : sub11 [-2, 0, -7] = true := by decide +kernel
theorem sub11_73 : sub11 [-2, 0, -6] = true := by decide +kernel
theorem sub11_74 : sub11 [-2, 0, -5] = true := by decide +kernel
theorem sub11_75 : sub11 [-2, 0, -4] = true := by decide +kernel
theorem sub11_76 : sub11 [-2, 0, -3] = true := by decide +kernel
theorem sub11_77 : sub11 [-2, 0, -2] = true := by decide +kernel
theorem sub11_78 : sub11 [-2, 0, -1] = true := by decide +kernel
theorem sub11_79 : sub11 [-2, 0, 0] = true := by decide +kernel
theorem sub11_80 : sub11 [-2, 0, 1] = true := by decide +kernel
theorem sub11_81 : sub11 [-2, 0, 2] = true := by decide +kernel
theorem sub11_82 : sub11 [-2, 0, 3] = true := by decide +kernel
theorem sub11_83 : sub11 [-2, 0, 4] = true := by decide +kernel
theorem sub11_84 : sub11 [-2, 0, 5] = true := by decide +kernel
theorem sub11_85 : sub11 [-2, 1, -8] = true := by decide +kernel
theorem sub11_86 : sub11 [-2, 1, -7] = true := by decide +kernel
theorem sub11_87 : sub11 [-2, 1, -6] = true := by decide +kernel
theorem sub11_88 : sub11 [-2, 1, -5] = true := by decide +kernel
theorem sub11_89 : sub11 [-2, 1, -4] = true := by decide +kernel
theorem sub11_90 : sub11 [-2, 1, -3] = true := by decide +kernel
theorem sub11_91 : sub11 [-2, 1, -2] = true := by decide +kernel
theorem sub11_92 : sub11 [-2, 1, -1] = true := by decide +kernel
theorem sub11_93 : sub11 [-2, 1, 0] = true := by decide +kernel
theorem sub11_94 : sub11 [-2, 1, 1] = true := by decide +kernel
theorem sub11_95 : sub11 [-2, 1, 2] = true := by decide +kernel
theorem sb11_2 : ∀ q ∈ blk11_2, sub11 q = true := by
  unfold blk11_2
  exact List.forall_mem_cons.2 ⟨sub11_64, List.forall_mem_cons.2 ⟨sub11_65, List.forall_mem_cons.2 ⟨sub11_66, List.forall_mem_cons.2 ⟨sub11_67, List.forall_mem_cons.2 ⟨sub11_68, List.forall_mem_cons.2 ⟨sub11_69, List.forall_mem_cons.2 ⟨sub11_70, List.forall_mem_cons.2 ⟨sub11_71, List.forall_mem_cons.2 ⟨sub11_72, List.forall_mem_cons.2 ⟨sub11_73, List.forall_mem_cons.2 ⟨sub11_74, List.forall_mem_cons.2 ⟨sub11_75, List.forall_mem_cons.2 ⟨sub11_76, List.forall_mem_cons.2 ⟨sub11_77, List.forall_mem_cons.2 ⟨sub11_78, List.forall_mem_cons.2 ⟨sub11_79, List.forall_mem_cons.2 ⟨sub11_80, List.forall_mem_cons.2 ⟨sub11_81, List.forall_mem_cons.2 ⟨sub11_82, List.forall_mem_cons.2 ⟨sub11_83, List.forall_mem_cons.2 ⟨sub11_84, List.forall_mem_cons.2 ⟨sub11_85, List.forall_mem_cons.2 ⟨sub11_86, List.forall_mem_cons.2 ⟨sub11_87, List.forall_mem_cons.2 ⟨sub11_88, List.forall_mem_cons.2 ⟨sub11_89, List.forall_mem_cons.2 ⟨sub11_90, List.forall_mem_cons.2 ⟨sub11_91, List.forall_mem_cons.2 ⟨sub11_92, List.forall_mem_cons.2 ⟨sub11_93, List.forall_mem_cons.2 ⟨sub11_94, List.forall_mem_cons.2 ⟨sub11_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub11_96 : sub11 [-2, 1, 3] = true := by decide +kernel
theorem sub11_97 : sub11 [-2, 1, 4] = true := by decide +kernel
theorem sub11_98 : sub11 [-2, 1, 5] = true := by decide +kernel
theorem sub11_99 : sub11 [-2, 2, -7] = true := by decide +kernel
theorem sub11_100 : sub11 [-2, 2, -6] = true := by decide +kernel
theorem sub11_101 : sub11 [-2, 2, -5] = true := by decide +kernel
theorem sub11_102 : sub11 [-2, 2, -4] = true := by decide +kernel
theorem sub11_103 : sub11 [-2, 2, -3] = true := by decide +kernel
theorem sub11_104 : sub11 [-2, 2, -2] = true := by decide +kernel
theorem sub11_105 : sub11 [-2, 2, -1] = true := by decide +kernel
theorem sub11_106 : sub11 [-2, 2, 0] = true := by decide +kernel
theorem sub11_107 : sub11 [-2, 2, 1] = true := by decide +kernel
theorem sub11_108 : sub11 [-2, 2, 2] = true := by decide +kernel
theorem sub11_109 : sub11 [-2, 2, 3] = true := by decide +kernel
theorem sub11_110 : sub11 [-2, 2, 4] = true := by decide +kernel
theorem sub11_111 : sub11 [-2, 2, 5] = true := by decide +kernel
theorem sub11_112 : sub11 [-2, 3] = true := by decide +kernel
theorem sub11_113 : sub11 [-2, 4] = true := by decide +kernel
theorem sub11_114 : sub11 [-2, 5] = true := by decide +kernel
theorem sub11_115 : sub11 [-2, 6] = true := by decide +kernel
theorem sub11_116 : sub11 [-1, -8] = true := by decide +kernel
theorem sub11_117 : sub11 [-1, -7] = true := by decide +kernel
theorem sub11_118 : sub11 [-1, -6] = true := by decide +kernel
theorem sub11_119 : sub11 [-1, -5] = true := by decide +kernel
theorem sub11_120 : sub11 [-1, -4] = true := by decide +kernel
theorem sub11_121 : sub11 [-1, -3, -8] = true := by decide +kernel
theorem sub11_122 : sub11 [-1, -3, -7] = true := by decide +kernel
theorem sub11_123 : sub11 [-1, -3, -6] = true := by decide +kernel
theorem sub11_124 : sub11 [-1, -3, -5] = true := by decide +kernel
theorem sub11_125 : sub11 [-1, -3, -4] = true := by decide +kernel
theorem sub11_126 : sub11 [-1, -3, -3] = true := by decide +kernel
theorem sub11_127 : sub11 [-1, -3, -2] = true := by decide +kernel
theorem sb11_3 : ∀ q ∈ blk11_3, sub11 q = true := by
  unfold blk11_3
  exact List.forall_mem_cons.2 ⟨sub11_96, List.forall_mem_cons.2 ⟨sub11_97, List.forall_mem_cons.2 ⟨sub11_98, List.forall_mem_cons.2 ⟨sub11_99, List.forall_mem_cons.2 ⟨sub11_100, List.forall_mem_cons.2 ⟨sub11_101, List.forall_mem_cons.2 ⟨sub11_102, List.forall_mem_cons.2 ⟨sub11_103, List.forall_mem_cons.2 ⟨sub11_104, List.forall_mem_cons.2 ⟨sub11_105, List.forall_mem_cons.2 ⟨sub11_106, List.forall_mem_cons.2 ⟨sub11_107, List.forall_mem_cons.2 ⟨sub11_108, List.forall_mem_cons.2 ⟨sub11_109, List.forall_mem_cons.2 ⟨sub11_110, List.forall_mem_cons.2 ⟨sub11_111, List.forall_mem_cons.2 ⟨sub11_112, List.forall_mem_cons.2 ⟨sub11_113, List.forall_mem_cons.2 ⟨sub11_114, List.forall_mem_cons.2 ⟨sub11_115, List.forall_mem_cons.2 ⟨sub11_116, List.forall_mem_cons.2 ⟨sub11_117, List.forall_mem_cons.2 ⟨sub11_118, List.forall_mem_cons.2 ⟨sub11_119, List.forall_mem_cons.2 ⟨sub11_120, List.forall_mem_cons.2 ⟨sub11_121, List.forall_mem_cons.2 ⟨sub11_122, List.forall_mem_cons.2 ⟨sub11_123, List.forall_mem_cons.2 ⟨sub11_124, List.forall_mem_cons.2 ⟨sub11_125, List.forall_mem_cons.2 ⟨sub11_126, List.forall_mem_cons.2 ⟨sub11_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub11_128 : sub11 [-1, -3, -1] = true := by decide +kernel
theorem sub11_129 : sub11 [-1, -3, 0] = true := by decide +kernel
theorem sub11_130 : sub11 [-1, -3, 1] = true := by decide +kernel
theorem sub11_131 : sub11 [-1, -3, 2] = true := by decide +kernel
theorem sub11_132 : sub11 [-1, -3, 3] = true := by decide +kernel
theorem sub11_133 : sub11 [-1, -3, 4] = true := by decide +kernel
theorem sub11_134 : sub11 [-1, -3, 5] = true := by decide +kernel
theorem sub11_135 : sub11 [-1, -2, -8] = true := by decide +kernel
theorem sub11_136 : sub11 [-1, -2, -7] = true := by decide +kernel
theorem sub11_137 : sub11 [-1, -2, -6] = true := by decide +kernel
theorem sub11_138 : sub11 [-1, -2, -5] = true := by decide +kernel
theorem sub11_139 : sub11 [-1, -2, -4] = true := by decide +kernel
theorem sub11_140 : sub11 [-1, -2, -3] = true := by decide +kernel
theorem sub11_141 : sub11 [-1, -2, -2] = true := by decide +kernel
theorem sub11_142 : sub11 [-1, -2, -1] = true := by decide +kernel
theorem sub11_143 : sub11 [-1, -2, 0] = true := by decide +kernel
theorem sub11_144 : sub11 [-1, -2, 1] = true := by decide +kernel
theorem sub11_145 : sub11 [-1, -2, 2] = true := by decide +kernel
theorem sub11_146 : sub11 [-1, -2, 3] = true := by decide +kernel
theorem sub11_147 : sub11 [-1, -2, 4] = true := by decide +kernel
theorem sub11_148 : sub11 [-1, -2, 5] = true := by decide +kernel
theorem sub11_149 : sub11 [-1, -1, -8] = true := by decide +kernel
theorem sub11_150 : sub11 [-1, -1, -7] = true := by decide +kernel
theorem sub11_151 : sub11 [-1, -1, -6] = true := by decide +kernel
theorem sub11_152 : sub11 [-1, -1, -5] = true := by decide +kernel
theorem sub11_153 : sub11 [-1, -1, -4] = true := by decide +kernel
theorem sub11_154 : sub11 [-1, -1, -3] = true := by decide +kernel
theorem sub11_155 : sub11 [-1, -1, -2] = true := by decide +kernel
theorem sub11_156 : sub11 [-1, -1, -1] = true := by decide +kernel
theorem sub11_157 : sub11 [-1, -1, 0] = true := by decide +kernel
theorem sub11_158 : sub11 [-1, -1, 1] = true := by decide +kernel
theorem sub11_159 : sub11 [-1, -1, 2] = true := by decide +kernel
theorem sb11_4 : ∀ q ∈ blk11_4, sub11 q = true := by
  unfold blk11_4
  exact List.forall_mem_cons.2 ⟨sub11_128, List.forall_mem_cons.2 ⟨sub11_129, List.forall_mem_cons.2 ⟨sub11_130, List.forall_mem_cons.2 ⟨sub11_131, List.forall_mem_cons.2 ⟨sub11_132, List.forall_mem_cons.2 ⟨sub11_133, List.forall_mem_cons.2 ⟨sub11_134, List.forall_mem_cons.2 ⟨sub11_135, List.forall_mem_cons.2 ⟨sub11_136, List.forall_mem_cons.2 ⟨sub11_137, List.forall_mem_cons.2 ⟨sub11_138, List.forall_mem_cons.2 ⟨sub11_139, List.forall_mem_cons.2 ⟨sub11_140, List.forall_mem_cons.2 ⟨sub11_141, List.forall_mem_cons.2 ⟨sub11_142, List.forall_mem_cons.2 ⟨sub11_143, List.forall_mem_cons.2 ⟨sub11_144, List.forall_mem_cons.2 ⟨sub11_145, List.forall_mem_cons.2 ⟨sub11_146, List.forall_mem_cons.2 ⟨sub11_147, List.forall_mem_cons.2 ⟨sub11_148, List.forall_mem_cons.2 ⟨sub11_149, List.forall_mem_cons.2 ⟨sub11_150, List.forall_mem_cons.2 ⟨sub11_151, List.forall_mem_cons.2 ⟨sub11_152, List.forall_mem_cons.2 ⟨sub11_153, List.forall_mem_cons.2 ⟨sub11_154, List.forall_mem_cons.2 ⟨sub11_155, List.forall_mem_cons.2 ⟨sub11_156, List.forall_mem_cons.2 ⟨sub11_157, List.forall_mem_cons.2 ⟨sub11_158, List.forall_mem_cons.2 ⟨sub11_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub11_160 : sub11 [-1, -1, 3] = true := by decide +kernel
theorem sub11_161 : sub11 [-1, -1, 4] = true := by decide +kernel
theorem sub11_162 : sub11 [-1, -1, 5] = true := by decide +kernel
theorem sub11_163 : sub11 [-1, 0, -8] = true := by decide +kernel
theorem sub11_164 : sub11 [-1, 0, -7] = true := by decide +kernel
theorem sub11_165 : sub11 [-1, 0, -6] = true := by decide +kernel
theorem sub11_166 : sub11 [-1, 0, -5] = true := by decide +kernel
theorem sub11_167 : sub11 [-1, 0, -4] = true := by decide +kernel
theorem sub11_168 : sub11 [-1, 0, -3] = true := by decide +kernel
theorem sub11_169 : sub11 [-1, 0, -2] = true := by decide +kernel
theorem sub11_170 : sub11 [-1, 0, -1] = true := by decide +kernel
theorem sub11_171 : sub11 [-1, 0, 0] = true := by decide +kernel
theorem sub11_172 : sub11 [-1, 0, 1] = true := by decide +kernel
theorem sub11_173 : sub11 [-1, 0, 2] = true := by decide +kernel
theorem sub11_174 : sub11 [-1, 0, 3] = true := by decide +kernel
theorem sub11_175 : sub11 [-1, 0, 4] = true := by decide +kernel
theorem sub11_176 : sub11 [-1, 0, 5] = true := by decide +kernel
theorem sub11_177 : sub11 [-1, 0, 6] = true := by decide +kernel
theorem sub11_178 : sub11 [-1, 1, -7] = true := by decide +kernel
theorem sub11_179 : sub11 [-1, 1, -6] = true := by decide +kernel
theorem sub11_180 : sub11 [-1, 1, -5] = true := by decide +kernel
theorem sub11_181 : sub11 [-1, 1, -4] = true := by decide +kernel
theorem sub11_182 : sub11 [-1, 1, -3] = true := by decide +kernel
theorem sub11_183 : sub11 [-1, 1, -2] = true := by decide +kernel
theorem sub11_184 : sub11 [-1, 1, -1] = true := by decide +kernel
theorem sub11_185 : sub11 [-1, 1, 0] = true := by decide +kernel
theorem sub11_186 : sub11 [-1, 1, 1] = true := by decide +kernel
theorem sub11_187 : sub11 [-1, 1, 2] = true := by decide +kernel
theorem sub11_188 : sub11 [-1, 1, 3] = true := by decide +kernel
theorem sub11_189 : sub11 [-1, 1, 4] = true := by decide +kernel
theorem sub11_190 : sub11 [-1, 1, 5] = true := by decide +kernel
theorem sub11_191 : sub11 [-1, 1, 6] = true := by decide +kernel
theorem sb11_5 : ∀ q ∈ blk11_5, sub11 q = true := by
  unfold blk11_5
  exact List.forall_mem_cons.2 ⟨sub11_160, List.forall_mem_cons.2 ⟨sub11_161, List.forall_mem_cons.2 ⟨sub11_162, List.forall_mem_cons.2 ⟨sub11_163, List.forall_mem_cons.2 ⟨sub11_164, List.forall_mem_cons.2 ⟨sub11_165, List.forall_mem_cons.2 ⟨sub11_166, List.forall_mem_cons.2 ⟨sub11_167, List.forall_mem_cons.2 ⟨sub11_168, List.forall_mem_cons.2 ⟨sub11_169, List.forall_mem_cons.2 ⟨sub11_170, List.forall_mem_cons.2 ⟨sub11_171, List.forall_mem_cons.2 ⟨sub11_172, List.forall_mem_cons.2 ⟨sub11_173, List.forall_mem_cons.2 ⟨sub11_174, List.forall_mem_cons.2 ⟨sub11_175, List.forall_mem_cons.2 ⟨sub11_176, List.forall_mem_cons.2 ⟨sub11_177, List.forall_mem_cons.2 ⟨sub11_178, List.forall_mem_cons.2 ⟨sub11_179, List.forall_mem_cons.2 ⟨sub11_180, List.forall_mem_cons.2 ⟨sub11_181, List.forall_mem_cons.2 ⟨sub11_182, List.forall_mem_cons.2 ⟨sub11_183, List.forall_mem_cons.2 ⟨sub11_184, List.forall_mem_cons.2 ⟨sub11_185, List.forall_mem_cons.2 ⟨sub11_186, List.forall_mem_cons.2 ⟨sub11_187, List.forall_mem_cons.2 ⟨sub11_188, List.forall_mem_cons.2 ⟨sub11_189, List.forall_mem_cons.2 ⟨sub11_190, List.forall_mem_cons.2 ⟨sub11_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub11_192 : sub11 [-1, 2, -7] = true := by decide +kernel
theorem sub11_193 : sub11 [-1, 2, -6] = true := by decide +kernel
theorem sub11_194 : sub11 [-1, 2, -5] = true := by decide +kernel
theorem sub11_195 : sub11 [-1, 2, -4] = true := by decide +kernel
theorem sub11_196 : sub11 [-1, 2, -3] = true := by decide +kernel
theorem sub11_197 : sub11 [-1, 2, -2] = true := by decide +kernel
theorem sub11_198 : sub11 [-1, 2, -1] = true := by decide +kernel
theorem sub11_199 : sub11 [-1, 2, 0] = true := by decide +kernel
theorem sub11_200 : sub11 [-1, 2, 1] = true := by decide +kernel
theorem sub11_201 : sub11 [-1, 2, 2] = true := by decide +kernel
theorem sub11_202 : sub11 [-1, 2, 3] = true := by decide +kernel
theorem sub11_203 : sub11 [-1, 2, 4] = true := by decide +kernel
theorem sub11_204 : sub11 [-1, 2, 5] = true := by decide +kernel
theorem sub11_205 : sub11 [-1, 2, 6] = true := by decide +kernel
theorem sub11_206 : sub11 [-1, 3, -6] = true := by decide +kernel
theorem sub11_207 : sub11 [-1, 3, -5] = true := by decide +kernel
theorem sub11_208 : sub11 [-1, 3, -4] = true := by decide +kernel
theorem sub11_209 : sub11 [-1, 3, -3] = true := by decide +kernel
theorem sub11_210 : sub11 [-1, 3, -2] = true := by decide +kernel
theorem sub11_211 : sub11 [-1, 3, -1] = true := by decide +kernel
theorem sub11_212 : sub11 [-1, 3, 0] = true := by decide +kernel
theorem sub11_213 : sub11 [-1, 3, 1] = true := by decide +kernel
theorem sub11_214 : sub11 [-1, 3, 2] = true := by decide +kernel
theorem sub11_215 : sub11 [-1, 3, 3] = true := by decide +kernel
theorem sub11_216 : sub11 [-1, 3, 4] = true := by decide +kernel
theorem sub11_217 : sub11 [-1, 3, 5] = true := by decide +kernel
theorem sub11_218 : sub11 [-1, 3, 6] = true := by decide +kernel
theorem sub11_219 : sub11 [-1, 4] = true := by decide +kernel
theorem sub11_220 : sub11 [-1, 5] = true := by decide +kernel
theorem sub11_221 : sub11 [-1, 6] = true := by decide +kernel
theorem sub11_222 : sub11 [-1, 7] = true := by decide +kernel
theorem sub11_223 : sub11 [0, -8] = true := by decide +kernel
theorem sb11_6 : ∀ q ∈ blk11_6, sub11 q = true := by
  unfold blk11_6
  exact List.forall_mem_cons.2 ⟨sub11_192, List.forall_mem_cons.2 ⟨sub11_193, List.forall_mem_cons.2 ⟨sub11_194, List.forall_mem_cons.2 ⟨sub11_195, List.forall_mem_cons.2 ⟨sub11_196, List.forall_mem_cons.2 ⟨sub11_197, List.forall_mem_cons.2 ⟨sub11_198, List.forall_mem_cons.2 ⟨sub11_199, List.forall_mem_cons.2 ⟨sub11_200, List.forall_mem_cons.2 ⟨sub11_201, List.forall_mem_cons.2 ⟨sub11_202, List.forall_mem_cons.2 ⟨sub11_203, List.forall_mem_cons.2 ⟨sub11_204, List.forall_mem_cons.2 ⟨sub11_205, List.forall_mem_cons.2 ⟨sub11_206, List.forall_mem_cons.2 ⟨sub11_207, List.forall_mem_cons.2 ⟨sub11_208, List.forall_mem_cons.2 ⟨sub11_209, List.forall_mem_cons.2 ⟨sub11_210, List.forall_mem_cons.2 ⟨sub11_211, List.forall_mem_cons.2 ⟨sub11_212, List.forall_mem_cons.2 ⟨sub11_213, List.forall_mem_cons.2 ⟨sub11_214, List.forall_mem_cons.2 ⟨sub11_215, List.forall_mem_cons.2 ⟨sub11_216, List.forall_mem_cons.2 ⟨sub11_217, List.forall_mem_cons.2 ⟨sub11_218, List.forall_mem_cons.2 ⟨sub11_219, List.forall_mem_cons.2 ⟨sub11_220, List.forall_mem_cons.2 ⟨sub11_221, List.forall_mem_cons.2 ⟨sub11_222, List.forall_mem_cons.2 ⟨sub11_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub11_224 : sub11 [0, -7] = true := by decide +kernel
theorem sub11_225 : sub11 [0, -6] = true := by decide +kernel
theorem sub11_226 : sub11 [0, -5] = true := by decide +kernel
theorem sub11_227 : sub11 [0, -4] = true := by decide +kernel
theorem sub11_228 : sub11 [0, -3, -7] = true := by decide +kernel
theorem sub11_229 : sub11 [0, -3, -6] = true := by decide +kernel
theorem sub11_230 : sub11 [0, -3, -5] = true := by decide +kernel
theorem sub11_231 : sub11 [0, -3, -4] = true := by decide +kernel
theorem sub11_232 : sub11 [0, -3, -3] = true := by decide +kernel
theorem sub11_233 : sub11 [0, -3, -2] = true := by decide +kernel
theorem sub11_234 : sub11 [0, -3, -1] = true := by decide +kernel
theorem sub11_235 : sub11 [0, -3, 0] = true := by decide +kernel
theorem sub11_236 : sub11 [0, -3, 1] = true := by decide +kernel
theorem sub11_237 : sub11 [0, -3, 2] = true := by decide +kernel
theorem sub11_238 : sub11 [0, -3, 3] = true := by decide +kernel
theorem sub11_239 : sub11 [0, -3, 4] = true := by decide +kernel
theorem sub11_240 : sub11 [0, -3, 5] = true := by decide +kernel
theorem sub11_241 : sub11 [0, -2, -7] = true := by decide +kernel
theorem sub11_242 : sub11 [0, -2, -6] = true := by decide +kernel
theorem sub11_243 : sub11 [0, -2, -5] = true := by decide +kernel
theorem sub11_244 : sub11 [0, -2, -4] = true := by decide +kernel
theorem sub11_245 : sub11 [0, -2, -3] = true := by decide +kernel
theorem sub11_246 : sub11 [0, -2, -2] = true := by decide +kernel
theorem sub11_247 : sub11 [0, -2, -1] = true := by decide +kernel
theorem sub11_248 : sub11 [0, -2, 0] = true := by decide +kernel
theorem sub11_249 : sub11 [0, -2, 1] = true := by decide +kernel
theorem sub11_250 : sub11 [0, -2, 2] = true := by decide +kernel
theorem sub11_251 : sub11 [0, -2, 3] = true := by decide +kernel
theorem sub11_252 : sub11 [0, -2, 4] = true := by decide +kernel
theorem sub11_253 : sub11 [0, -2, 5] = true := by decide +kernel
theorem sub11_254 : sub11 [0, -2, 6] = true := by decide +kernel
theorem sub11_255 : sub11 [0, -1, -7] = true := by decide +kernel
theorem sb11_7 : ∀ q ∈ blk11_7, sub11 q = true := by
  unfold blk11_7
  exact List.forall_mem_cons.2 ⟨sub11_224, List.forall_mem_cons.2 ⟨sub11_225, List.forall_mem_cons.2 ⟨sub11_226, List.forall_mem_cons.2 ⟨sub11_227, List.forall_mem_cons.2 ⟨sub11_228, List.forall_mem_cons.2 ⟨sub11_229, List.forall_mem_cons.2 ⟨sub11_230, List.forall_mem_cons.2 ⟨sub11_231, List.forall_mem_cons.2 ⟨sub11_232, List.forall_mem_cons.2 ⟨sub11_233, List.forall_mem_cons.2 ⟨sub11_234, List.forall_mem_cons.2 ⟨sub11_235, List.forall_mem_cons.2 ⟨sub11_236, List.forall_mem_cons.2 ⟨sub11_237, List.forall_mem_cons.2 ⟨sub11_238, List.forall_mem_cons.2 ⟨sub11_239, List.forall_mem_cons.2 ⟨sub11_240, List.forall_mem_cons.2 ⟨sub11_241, List.forall_mem_cons.2 ⟨sub11_242, List.forall_mem_cons.2 ⟨sub11_243, List.forall_mem_cons.2 ⟨sub11_244, List.forall_mem_cons.2 ⟨sub11_245, List.forall_mem_cons.2 ⟨sub11_246, List.forall_mem_cons.2 ⟨sub11_247, List.forall_mem_cons.2 ⟨sub11_248, List.forall_mem_cons.2 ⟨sub11_249, List.forall_mem_cons.2 ⟨sub11_250, List.forall_mem_cons.2 ⟨sub11_251, List.forall_mem_cons.2 ⟨sub11_252, List.forall_mem_cons.2 ⟨sub11_253, List.forall_mem_cons.2 ⟨sub11_254, List.forall_mem_cons.2 ⟨sub11_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub11_256 : sub11 [0, -1, -6] = true := by decide +kernel
theorem sub11_257 : sub11 [0, -1, -5] = true := by decide +kernel
theorem sub11_258 : sub11 [0, -1, -4] = true := by decide +kernel
theorem sub11_259 : sub11 [0, -1, -3] = true := by decide +kernel
theorem sub11_260 : sub11 [0, -1, -2] = true := by decide +kernel
theorem sub11_261 : sub11 [0, -1, -1] = true := by decide +kernel
theorem sub11_262 : sub11 [0, -1, 0] = true := by decide +kernel
theorem sub11_263 : sub11 [0, -1, 1] = true := by decide +kernel
theorem sub11_264 : sub11 [0, -1, 2] = true := by decide +kernel
theorem sub11_265 : sub11 [0, -1, 3] = true := by decide +kernel
theorem sub11_266 : sub11 [0, -1, 4] = true := by decide +kernel
theorem sub11_267 : sub11 [0, -1, 5] = true := by decide +kernel
theorem sub11_268 : sub11 [0, -1, 6] = true := by decide +kernel
theorem sub11_269 : sub11 [0, 0, -7] = true := by decide +kernel
theorem sub11_270 : sub11 [0, 0, -6] = true := by decide +kernel
theorem sub11_271 : sub11 [0, 0, -5] = true := by decide +kernel
theorem sub11_272 : sub11 [0, 0, -4] = true := by decide +kernel
theorem sub11_273 : sub11 [0, 0, -3] = true := by decide +kernel
theorem sub11_274 : sub11 [0, 0, -2] = true := by decide +kernel
theorem sub11_275 : sub11 [0, 0, -1] = true := by decide +kernel
theorem sub11_276 : sub11 [0, 0, 0] = true := by decide +kernel
theorem sub11_277 : sub11 [0, 0, 1] = true := by decide +kernel
theorem sub11_278 : sub11 [0, 0, 2] = true := by decide +kernel
theorem sub11_279 : sub11 [0, 0, 3] = true := by decide +kernel
theorem sub11_280 : sub11 [0, 0, 4] = true := by decide +kernel
theorem sub11_281 : sub11 [0, 0, 5] = true := by decide +kernel
theorem sub11_282 : sub11 [0, 0, 6] = true := by decide +kernel
theorem sub11_283 : sub11 [0, 1, -7] = true := by decide +kernel
theorem sub11_284 : sub11 [0, 1, -6] = true := by decide +kernel
theorem sub11_285 : sub11 [0, 1, -5] = true := by decide +kernel
theorem sub11_286 : sub11 [0, 1, -4] = true := by decide +kernel
theorem sub11_287 : sub11 [0, 1, -3] = true := by decide +kernel
theorem sb11_8 : ∀ q ∈ blk11_8, sub11 q = true := by
  unfold blk11_8
  exact List.forall_mem_cons.2 ⟨sub11_256, List.forall_mem_cons.2 ⟨sub11_257, List.forall_mem_cons.2 ⟨sub11_258, List.forall_mem_cons.2 ⟨sub11_259, List.forall_mem_cons.2 ⟨sub11_260, List.forall_mem_cons.2 ⟨sub11_261, List.forall_mem_cons.2 ⟨sub11_262, List.forall_mem_cons.2 ⟨sub11_263, List.forall_mem_cons.2 ⟨sub11_264, List.forall_mem_cons.2 ⟨sub11_265, List.forall_mem_cons.2 ⟨sub11_266, List.forall_mem_cons.2 ⟨sub11_267, List.forall_mem_cons.2 ⟨sub11_268, List.forall_mem_cons.2 ⟨sub11_269, List.forall_mem_cons.2 ⟨sub11_270, List.forall_mem_cons.2 ⟨sub11_271, List.forall_mem_cons.2 ⟨sub11_272, List.forall_mem_cons.2 ⟨sub11_273, List.forall_mem_cons.2 ⟨sub11_274, List.forall_mem_cons.2 ⟨sub11_275, List.forall_mem_cons.2 ⟨sub11_276, List.forall_mem_cons.2 ⟨sub11_277, List.forall_mem_cons.2 ⟨sub11_278, List.forall_mem_cons.2 ⟨sub11_279, List.forall_mem_cons.2 ⟨sub11_280, List.forall_mem_cons.2 ⟨sub11_281, List.forall_mem_cons.2 ⟨sub11_282, List.forall_mem_cons.2 ⟨sub11_283, List.forall_mem_cons.2 ⟨sub11_284, List.forall_mem_cons.2 ⟨sub11_285, List.forall_mem_cons.2 ⟨sub11_286, List.forall_mem_cons.2 ⟨sub11_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C120
