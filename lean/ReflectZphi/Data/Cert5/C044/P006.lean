import ReflectZphi.Data.Cert5.C044.Base

namespace ReflectZphi.Data.Cert5.C044
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub5_0 : sub5 [-7, -1] = true := by decide +kernel
theorem sub5_1 : sub5 [-7, 0] = true := by decide +kernel
theorem sub5_2 : sub5 [-7, 1] = true := by decide +kernel
theorem sub5_3 : sub5 [-7, 2] = true := by decide +kernel
theorem sub5_4 : sub5 [-7, 3] = true := by decide +kernel
theorem sub5_5 : sub5 [-7, 4] = true := by decide +kernel
theorem sub5_6 : sub5 [-7, 5] = true := by decide +kernel
theorem sub5_7 : sub5 [-6, -4] = true := by decide +kernel
theorem sub5_8 : sub5 [-6, -3] = true := by decide +kernel
theorem sub5_9 : sub5 [-6, -2] = true := by decide +kernel
theorem sub5_10 : sub5 [-6, -1] = true := by decide +kernel
theorem sub5_11 : sub5 [-6, 0] = true := by decide +kernel
theorem sub5_12 : sub5 [-6, 1] = true := by decide +kernel
theorem sub5_13 : sub5 [-6, 2] = true := by decide +kernel
theorem sub5_14 : sub5 [-6, 3] = true := by decide +kernel
theorem sub5_15 : sub5 [-6, 4] = true := by decide +kernel
theorem sub5_16 : sub5 [-6, 5] = true := by decide +kernel
theorem sub5_17 : sub5 [-6, 6] = true := by decide +kernel
theorem sub5_18 : sub5 [-6, 7] = true := by decide +kernel
theorem sub5_19 : sub5 [-5, -5] = true := by decide +kernel
theorem sub5_20 : sub5 [-5, -4] = true := by decide +kernel
theorem sub5_21 : sub5 [-5, -3] = true := by decide +kernel
theorem sub5_22 : sub5 [-5, -2] = true := by decide +kernel
theorem sub5_23 : sub5 [-5, -1] = true := by decide +kernel
theorem sub5_24 : sub5 [-5, 0] = true := by decide +kernel
theorem sub5_25 : sub5 [-5, 1] = true := by decide +kernel
theorem sub5_26 : sub5 [-5, 2] = true := by decide +kernel
theorem sub5_27 : sub5 [-5, 3] = true := by decide +kernel
theorem sub5_28 : sub5 [-5, 4] = true := by decide +kernel
theorem sub5_29 : sub5 [-5, 5] = true := by decide +kernel
theorem sub5_30 : sub5 [-5, 6] = true := by decide +kernel
theorem sub5_31 : sub5 [-5, 7] = true := by decide +kernel
theorem sb5_0 : ∀ q ∈ blk5_0, sub5 q = true := by
  unfold blk5_0
  exact List.forall_mem_cons.2 ⟨sub5_0, List.forall_mem_cons.2 ⟨sub5_1, List.forall_mem_cons.2 ⟨sub5_2, List.forall_mem_cons.2 ⟨sub5_3, List.forall_mem_cons.2 ⟨sub5_4, List.forall_mem_cons.2 ⟨sub5_5, List.forall_mem_cons.2 ⟨sub5_6, List.forall_mem_cons.2 ⟨sub5_7, List.forall_mem_cons.2 ⟨sub5_8, List.forall_mem_cons.2 ⟨sub5_9, List.forall_mem_cons.2 ⟨sub5_10, List.forall_mem_cons.2 ⟨sub5_11, List.forall_mem_cons.2 ⟨sub5_12, List.forall_mem_cons.2 ⟨sub5_13, List.forall_mem_cons.2 ⟨sub5_14, List.forall_mem_cons.2 ⟨sub5_15, List.forall_mem_cons.2 ⟨sub5_16, List.forall_mem_cons.2 ⟨sub5_17, List.forall_mem_cons.2 ⟨sub5_18, List.forall_mem_cons.2 ⟨sub5_19, List.forall_mem_cons.2 ⟨sub5_20, List.forall_mem_cons.2 ⟨sub5_21, List.forall_mem_cons.2 ⟨sub5_22, List.forall_mem_cons.2 ⟨sub5_23, List.forall_mem_cons.2 ⟨sub5_24, List.forall_mem_cons.2 ⟨sub5_25, List.forall_mem_cons.2 ⟨sub5_26, List.forall_mem_cons.2 ⟨sub5_27, List.forall_mem_cons.2 ⟨sub5_28, List.forall_mem_cons.2 ⟨sub5_29, List.forall_mem_cons.2 ⟨sub5_30, List.forall_mem_cons.2 ⟨sub5_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_32 : sub5 [-5, 8] = true := by decide +kernel
theorem sub5_33 : sub5 [-4, -6] = true := by decide +kernel
theorem sub5_34 : sub5 [-4, -5] = true := by decide +kernel
theorem sub5_35 : sub5 [-4, -4] = true := by decide +kernel
theorem sub5_36 : sub5 [-4, -3] = true := by decide +kernel
theorem sub5_37 : sub5 [-4, -2] = true := by decide +kernel
theorem sub5_38 : sub5 [-4, -1] = true := by decide +kernel
theorem sub5_39 : sub5 [-4, 0] = true := by decide +kernel
theorem sub5_40 : sub5 [-4, 1] = true := by decide +kernel
theorem sub5_41 : sub5 [-4, 2] = true := by decide +kernel
theorem sub5_42 : sub5 [-4, 3] = true := by decide +kernel
theorem sub5_43 : sub5 [-4, 4] = true := by decide +kernel
theorem sub5_44 : sub5 [-4, 5] = true := by decide +kernel
theorem sub5_45 : sub5 [-4, 6] = true := by decide +kernel
theorem sub5_46 : sub5 [-4, 7] = true := by decide +kernel
theorem sub5_47 : sub5 [-4, 8] = true := by decide +kernel
theorem sub5_48 : sub5 [-3, -7] = true := by decide +kernel
theorem sub5_49 : sub5 [-3, -6] = true := by decide +kernel
theorem sub5_50 : sub5 [-3, -5] = true := by decide +kernel
theorem sub5_51 : sub5 [-3, -4] = true := by decide +kernel
theorem sub5_52 : sub5 [-3, -3] = true := by decide +kernel
theorem sub5_53 : sub5 [-3, -2] = true := by decide +kernel
theorem sub5_54 : sub5 [-3, -1, -6] = true := by decide +kernel
theorem sub5_55 : sub5 [-3, -1, -5] = true := by decide +kernel
theorem sub5_56 : sub5 [-3, -1, -4] = true := by decide +kernel
theorem sub5_57 : sub5 [-3, -1, -3] = true := by decide +kernel
theorem sub5_58 : sub5 [-3, -1, -2] = true := by decide +kernel
theorem sub5_59 : sub5 [-3, -1, -1] = true := by decide +kernel
theorem sub5_60 : sub5 [-3, -1, 0] = true := by decide +kernel
theorem sub5_61 : sub5 [-3, -1, 1] = true := by decide +kernel
theorem sub5_62 : sub5 [-3, -1, 2] = true := by decide +kernel
theorem sub5_63 : sub5 [-3, -1, 3] = true := by decide +kernel
theorem sb5_1 : ∀ q ∈ blk5_1, sub5 q = true := by
  unfold blk5_1
  exact List.forall_mem_cons.2 ⟨sub5_32, List.forall_mem_cons.2 ⟨sub5_33, List.forall_mem_cons.2 ⟨sub5_34, List.forall_mem_cons.2 ⟨sub5_35, List.forall_mem_cons.2 ⟨sub5_36, List.forall_mem_cons.2 ⟨sub5_37, List.forall_mem_cons.2 ⟨sub5_38, List.forall_mem_cons.2 ⟨sub5_39, List.forall_mem_cons.2 ⟨sub5_40, List.forall_mem_cons.2 ⟨sub5_41, List.forall_mem_cons.2 ⟨sub5_42, List.forall_mem_cons.2 ⟨sub5_43, List.forall_mem_cons.2 ⟨sub5_44, List.forall_mem_cons.2 ⟨sub5_45, List.forall_mem_cons.2 ⟨sub5_46, List.forall_mem_cons.2 ⟨sub5_47, List.forall_mem_cons.2 ⟨sub5_48, List.forall_mem_cons.2 ⟨sub5_49, List.forall_mem_cons.2 ⟨sub5_50, List.forall_mem_cons.2 ⟨sub5_51, List.forall_mem_cons.2 ⟨sub5_52, List.forall_mem_cons.2 ⟨sub5_53, List.forall_mem_cons.2 ⟨sub5_54, List.forall_mem_cons.2 ⟨sub5_55, List.forall_mem_cons.2 ⟨sub5_56, List.forall_mem_cons.2 ⟨sub5_57, List.forall_mem_cons.2 ⟨sub5_58, List.forall_mem_cons.2 ⟨sub5_59, List.forall_mem_cons.2 ⟨sub5_60, List.forall_mem_cons.2 ⟨sub5_61, List.forall_mem_cons.2 ⟨sub5_62, List.forall_mem_cons.2 ⟨sub5_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_64 : sub5 [-3, -1, 4] = true := by decide +kernel
theorem sub5_65 : sub5 [-3, -1, 5] = true := by decide +kernel
theorem sub5_66 : sub5 [-3, -1, 6] = true := by decide +kernel
theorem sub5_67 : sub5 [-3, -1, 7] = true := by decide +kernel
theorem sub5_68 : sub5 [-3, 0, -7] = true := by decide +kernel
theorem sub5_69 : sub5 [-3, 0, -6] = true := by decide +kernel
theorem sub5_70 : sub5 [-3, 0, -5] = true := by decide +kernel
theorem sub5_71 : sub5 [-3, 0, -4] = true := by decide +kernel
theorem sub5_72 : sub5 [-3, 0, -3] = true := by decide +kernel
theorem sub5_73 : sub5 [-3, 0, -2] = true := by decide +kernel
theorem sub5_74 : sub5 [-3, 0, -1] = true := by decide +kernel
theorem sub5_75 : sub5 [-3, 0, 0] = true := by decide +kernel
theorem sub5_76 : sub5 [-3, 0, 1] = true := by decide +kernel
theorem sub5_77 : sub5 [-3, 0, 2] = true := by decide +kernel
theorem sub5_78 : sub5 [-3, 0, 3] = true := by decide +kernel
theorem sub5_79 : sub5 [-3, 0, 4] = true := by decide +kernel
theorem sub5_80 : sub5 [-3, 0, 5] = true := by decide +kernel
theorem sub5_81 : sub5 [-3, 0, 6] = true := by decide +kernel
theorem sub5_82 : sub5 [-3, 1, -7] = true := by decide +kernel
theorem sub5_83 : sub5 [-3, 1, -6] = true := by decide +kernel
theorem sub5_84 : sub5 [-3, 1, -5] = true := by decide +kernel
theorem sub5_85 : sub5 [-3, 1, -4] = true := by decide +kernel
theorem sub5_86 : sub5 [-3, 1, -3] = true := by decide +kernel
theorem sub5_87 : sub5 [-3, 1, -2] = true := by decide +kernel
theorem sub5_88 : sub5 [-3, 1, -1] = true := by decide +kernel
theorem sub5_89 : sub5 [-3, 1, 0] = true := by decide +kernel
theorem sub5_90 : sub5 [-3, 1, 1] = true := by decide +kernel
theorem sub5_91 : sub5 [-3, 1, 2] = true := by decide +kernel
theorem sub5_92 : sub5 [-3, 1, 3] = true := by decide +kernel
theorem sub5_93 : sub5 [-3, 1, 4] = true := by decide +kernel
theorem sub5_94 : sub5 [-3, 1, 5] = true := by decide +kernel
theorem sub5_95 : sub5 [-3, 1, 6] = true := by decide +kernel
theorem sb5_2 : ∀ q ∈ blk5_2, sub5 q = true := by
  unfold blk5_2
  exact List.forall_mem_cons.2 ⟨sub5_64, List.forall_mem_cons.2 ⟨sub5_65, List.forall_mem_cons.2 ⟨sub5_66, List.forall_mem_cons.2 ⟨sub5_67, List.forall_mem_cons.2 ⟨sub5_68, List.forall_mem_cons.2 ⟨sub5_69, List.forall_mem_cons.2 ⟨sub5_70, List.forall_mem_cons.2 ⟨sub5_71, List.forall_mem_cons.2 ⟨sub5_72, List.forall_mem_cons.2 ⟨sub5_73, List.forall_mem_cons.2 ⟨sub5_74, List.forall_mem_cons.2 ⟨sub5_75, List.forall_mem_cons.2 ⟨sub5_76, List.forall_mem_cons.2 ⟨sub5_77, List.forall_mem_cons.2 ⟨sub5_78, List.forall_mem_cons.2 ⟨sub5_79, List.forall_mem_cons.2 ⟨sub5_80, List.forall_mem_cons.2 ⟨sub5_81, List.forall_mem_cons.2 ⟨sub5_82, List.forall_mem_cons.2 ⟨sub5_83, List.forall_mem_cons.2 ⟨sub5_84, List.forall_mem_cons.2 ⟨sub5_85, List.forall_mem_cons.2 ⟨sub5_86, List.forall_mem_cons.2 ⟨sub5_87, List.forall_mem_cons.2 ⟨sub5_88, List.forall_mem_cons.2 ⟨sub5_89, List.forall_mem_cons.2 ⟨sub5_90, List.forall_mem_cons.2 ⟨sub5_91, List.forall_mem_cons.2 ⟨sub5_92, List.forall_mem_cons.2 ⟨sub5_93, List.forall_mem_cons.2 ⟨sub5_94, List.forall_mem_cons.2 ⟨sub5_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_96 : sub5 [-3, 2, -8] = true := by decide +kernel
theorem sub5_97 : sub5 [-3, 2, -7] = true := by decide +kernel
theorem sub5_98 : sub5 [-3, 2, -6] = true := by decide +kernel
theorem sub5_99 : sub5 [-3, 2, -5] = true := by decide +kernel
theorem sub5_100 : sub5 [-3, 2, -4] = true := by decide +kernel
theorem sub5_101 : sub5 [-3, 2, -3] = true := by decide +kernel
theorem sub5_102 : sub5 [-3, 2, -2] = true := by decide +kernel
theorem sub5_103 : sub5 [-3, 2, -1] = true := by decide +kernel
theorem sub5_104 : sub5 [-3, 2, 0] = true := by decide +kernel
theorem sub5_105 : sub5 [-3, 2, 1] = true := by decide +kernel
theorem sub5_106 : sub5 [-3, 2, 2] = true := by decide +kernel
theorem sub5_107 : sub5 [-3, 2, 3] = true := by decide +kernel
theorem sub5_108 : sub5 [-3, 2, 4] = true := by decide +kernel
theorem sub5_109 : sub5 [-3, 2, 5] = true := by decide +kernel
theorem sub5_110 : sub5 [-3, 3, -8] = true := by decide +kernel
theorem sub5_111 : sub5 [-3, 3, -7] = true := by decide +kernel
theorem sub5_112 : sub5 [-3, 3, -6] = true := by decide +kernel
theorem sub5_113 : sub5 [-3, 3, -5] = true := by decide +kernel
theorem sub5_114 : sub5 [-3, 3, -4] = true := by decide +kernel
theorem sub5_115 : sub5 [-3, 3, -3] = true := by decide +kernel
theorem sub5_116 : sub5 [-3, 3, -2] = true := by decide +kernel
theorem sub5_117 : sub5 [-3, 3, -1] = true := by decide +kernel
theorem sub5_118 : sub5 [-3, 3, 0] = true := by decide +kernel
theorem sub5_119 : sub5 [-3, 3, 1] = true := by decide +kernel
theorem sub5_120 : sub5 [-3, 3, 2] = true := by decide +kernel
theorem sub5_121 : sub5 [-3, 3, 3] = true := by decide +kernel
theorem sub5_122 : sub5 [-3, 3, 4] = true := by decide +kernel
theorem sub5_123 : sub5 [-3, 3, 5] = true := by decide +kernel
theorem sub5_124 : sub5 [-3, 4] = true := by decide +kernel
theorem sub5_125 : sub5 [-3, 5] = true := by decide +kernel
theorem sub5_126 : sub5 [-3, 6] = true := by decide +kernel
theorem sub5_127 : sub5 [-3, 7] = true := by decide +kernel
theorem sb5_3 : ∀ q ∈ blk5_3, sub5 q = true := by
  unfold blk5_3
  exact List.forall_mem_cons.2 ⟨sub5_96, List.forall_mem_cons.2 ⟨sub5_97, List.forall_mem_cons.2 ⟨sub5_98, List.forall_mem_cons.2 ⟨sub5_99, List.forall_mem_cons.2 ⟨sub5_100, List.forall_mem_cons.2 ⟨sub5_101, List.forall_mem_cons.2 ⟨sub5_102, List.forall_mem_cons.2 ⟨sub5_103, List.forall_mem_cons.2 ⟨sub5_104, List.forall_mem_cons.2 ⟨sub5_105, List.forall_mem_cons.2 ⟨sub5_106, List.forall_mem_cons.2 ⟨sub5_107, List.forall_mem_cons.2 ⟨sub5_108, List.forall_mem_cons.2 ⟨sub5_109, List.forall_mem_cons.2 ⟨sub5_110, List.forall_mem_cons.2 ⟨sub5_111, List.forall_mem_cons.2 ⟨sub5_112, List.forall_mem_cons.2 ⟨sub5_113, List.forall_mem_cons.2 ⟨sub5_114, List.forall_mem_cons.2 ⟨sub5_115, List.forall_mem_cons.2 ⟨sub5_116, List.forall_mem_cons.2 ⟨sub5_117, List.forall_mem_cons.2 ⟨sub5_118, List.forall_mem_cons.2 ⟨sub5_119, List.forall_mem_cons.2 ⟨sub5_120, List.forall_mem_cons.2 ⟨sub5_121, List.forall_mem_cons.2 ⟨sub5_122, List.forall_mem_cons.2 ⟨sub5_123, List.forall_mem_cons.2 ⟨sub5_124, List.forall_mem_cons.2 ⟨sub5_125, List.forall_mem_cons.2 ⟨sub5_126, List.forall_mem_cons.2 ⟨sub5_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_128 : sub5 [-3, 8] = true := by decide +kernel
theorem sub5_129 : sub5 [-2, -8] = true := by decide +kernel
theorem sub5_130 : sub5 [-2, -7] = true := by decide +kernel
theorem sub5_131 : sub5 [-2, -6] = true := by decide +kernel
theorem sub5_132 : sub5 [-2, -5] = true := by decide +kernel
theorem sub5_133 : sub5 [-2, -4] = true := by decide +kernel
theorem sub5_134 : sub5 [-2, -3, -5] = true := by decide +kernel
theorem sub5_135 : sub5 [-2, -3, -4] = true := by decide +kernel
theorem sub5_136 : sub5 [-2, -3, -3] = true := by decide +kernel
theorem sub5_137 : sub5 [-2, -3, -2] = true := by decide +kernel
theorem sub5_138 : sub5 [-2, -3, -1] = true := by decide +kernel
theorem sub5_139 : sub5 [-2, -3, 0] = true := by decide +kernel
theorem sub5_140 : sub5 [-2, -3, 1] = true := by decide +kernel
theorem sub5_141 : sub5 [-2, -3, 2] = true := by decide +kernel
theorem sub5_142 : sub5 [-2, -3, 3] = true := by decide +kernel
theorem sub5_143 : sub5 [-2, -3, 4] = true := by decide +kernel
theorem sub5_144 : sub5 [-2, -3, 5] = true := by decide +kernel
theorem sub5_145 : sub5 [-2, -3, 6] = true := by decide +kernel
theorem sub5_146 : sub5 [-2, -3, 7] = true := by decide +kernel
theorem sub5_147 : sub5 [-2, -2, -6] = true := by decide +kernel
theorem sub5_148 : sub5 [-2, -2, -5] = true := by decide +kernel
theorem sub5_149 : sub5 [-2, -2, -4] = true := by decide +kernel
theorem sub5_150 : sub5 [-2, -2, -3] = true := by decide +kernel
theorem sub5_151 : sub5 [-2, -2, -2] = true := by decide +kernel
theorem sub5_152 : sub5 [-2, -2, -1] = true := by decide +kernel
theorem sub5_153 : sub5 [-2, -2, 0] = true := by decide +kernel
theorem sub5_154 : sub5 [-2, -2, 1] = true := by decide +kernel
theorem sub5_155 : sub5 [-2, -2, 2] = true := by decide +kernel
theorem sub5_156 : sub5 [-2, -2, 3] = true := by decide +kernel
theorem sub5_157 : sub5 [-2, -2, 4] = true := by decide +kernel
theorem sub5_158 : sub5 [-2, -2, 5] = true := by decide +kernel
theorem sub5_159 : sub5 [-2, -2, 6] = true := by decide +kernel
theorem sb5_4 : ∀ q ∈ blk5_4, sub5 q = true := by
  unfold blk5_4
  exact List.forall_mem_cons.2 ⟨sub5_128, List.forall_mem_cons.2 ⟨sub5_129, List.forall_mem_cons.2 ⟨sub5_130, List.forall_mem_cons.2 ⟨sub5_131, List.forall_mem_cons.2 ⟨sub5_132, List.forall_mem_cons.2 ⟨sub5_133, List.forall_mem_cons.2 ⟨sub5_134, List.forall_mem_cons.2 ⟨sub5_135, List.forall_mem_cons.2 ⟨sub5_136, List.forall_mem_cons.2 ⟨sub5_137, List.forall_mem_cons.2 ⟨sub5_138, List.forall_mem_cons.2 ⟨sub5_139, List.forall_mem_cons.2 ⟨sub5_140, List.forall_mem_cons.2 ⟨sub5_141, List.forall_mem_cons.2 ⟨sub5_142, List.forall_mem_cons.2 ⟨sub5_143, List.forall_mem_cons.2 ⟨sub5_144, List.forall_mem_cons.2 ⟨sub5_145, List.forall_mem_cons.2 ⟨sub5_146, List.forall_mem_cons.2 ⟨sub5_147, List.forall_mem_cons.2 ⟨sub5_148, List.forall_mem_cons.2 ⟨sub5_149, List.forall_mem_cons.2 ⟨sub5_150, List.forall_mem_cons.2 ⟨sub5_151, List.forall_mem_cons.2 ⟨sub5_152, List.forall_mem_cons.2 ⟨sub5_153, List.forall_mem_cons.2 ⟨sub5_154, List.forall_mem_cons.2 ⟨sub5_155, List.forall_mem_cons.2 ⟨sub5_156, List.forall_mem_cons.2 ⟨sub5_157, List.forall_mem_cons.2 ⟨sub5_158, List.forall_mem_cons.2 ⟨sub5_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_160 : sub5 [-2, -2, 7] = true := by decide +kernel
theorem sub5_161 : sub5 [-2, -1, -7] = true := by decide +kernel
theorem sub5_162 : sub5 [-2, -1, -6] = true := by decide +kernel
theorem sub5_163 : sub5 [-2, -1, -5] = true := by decide +kernel
theorem sub5_164 : sub5 [-2, -1, -4] = true := by decide +kernel
theorem sub5_165 : sub5 [-2, -1, -3] = true := by decide +kernel
theorem sub5_166 : sub5 [-2, -1, -2] = true := by decide +kernel
theorem sub5_167 : sub5 [-2, -1, -1] = true := by decide +kernel
theorem sub5_168 : sub5 [-2, -1, 0] = true := by decide +kernel
theorem sub5_169 : sub5 [-2, -1, 1] = true := by decide +kernel
theorem sub5_170 : sub5 [-2, -1, 2] = true := by decide +kernel
theorem sub5_171 : sub5 [-2, -1, 3] = true := by decide +kernel
theorem sub5_172 : sub5 [-2, -1, 4] = true := by decide +kernel
theorem sub5_173 : sub5 [-2, -1, 5] = true := by decide +kernel
theorem sub5_174 : sub5 [-2, -1, 6] = true := by decide +kernel
theorem sub5_175 : sub5 [-2, -1, 7] = true := by decide +kernel
theorem sub5_176 : sub5 [-2, 0, -7] = true := by decide +kernel
theorem sub5_177 : sub5 [-2, 0, -6] = true := by decide +kernel
theorem sub5_178 : sub5 [-2, 0, -5] = true := by decide +kernel
theorem sub5_179 : sub5 [-2, 0, -4] = true := by decide +kernel
theorem sub5_180 : sub5 [-2, 0, -3] = true := by decide +kernel
theorem sub5_181 : sub5 [-2, 0, -2] = true := by decide +kernel
theorem sub5_182 : sub5 [-2, 0, -1] = true := by decide +kernel
theorem sub5_183 : sub5 [-2, 0, 0] = true := by decide +kernel
theorem sub5_184 : sub5 [-2, 0, 1] = true := by decide +kernel
theorem sub5_185 : sub5 [-2, 0, 2] = true := by decide +kernel
theorem sub5_186 : sub5 [-2, 0, 3] = true := by decide +kernel
theorem sub5_187 : sub5 [-2, 0, 4] = true := by decide +kernel
theorem sub5_188 : sub5 [-2, 0, 5] = true := by decide +kernel
theorem sub5_189 : sub5 [-2, 0, 6] = true := by decide +kernel
theorem sub5_190 : sub5 [-2, 0, 7] = true := by decide +kernel
theorem sub5_191 : sub5 [-2, 1, -8] = true := by decide +kernel
theorem sb5_5 : ∀ q ∈ blk5_5, sub5 q = true := by
  unfold blk5_5
  exact List.forall_mem_cons.2 ⟨sub5_160, List.forall_mem_cons.2 ⟨sub5_161, List.forall_mem_cons.2 ⟨sub5_162, List.forall_mem_cons.2 ⟨sub5_163, List.forall_mem_cons.2 ⟨sub5_164, List.forall_mem_cons.2 ⟨sub5_165, List.forall_mem_cons.2 ⟨sub5_166, List.forall_mem_cons.2 ⟨sub5_167, List.forall_mem_cons.2 ⟨sub5_168, List.forall_mem_cons.2 ⟨sub5_169, List.forall_mem_cons.2 ⟨sub5_170, List.forall_mem_cons.2 ⟨sub5_171, List.forall_mem_cons.2 ⟨sub5_172, List.forall_mem_cons.2 ⟨sub5_173, List.forall_mem_cons.2 ⟨sub5_174, List.forall_mem_cons.2 ⟨sub5_175, List.forall_mem_cons.2 ⟨sub5_176, List.forall_mem_cons.2 ⟨sub5_177, List.forall_mem_cons.2 ⟨sub5_178, List.forall_mem_cons.2 ⟨sub5_179, List.forall_mem_cons.2 ⟨sub5_180, List.forall_mem_cons.2 ⟨sub5_181, List.forall_mem_cons.2 ⟨sub5_182, List.forall_mem_cons.2 ⟨sub5_183, List.forall_mem_cons.2 ⟨sub5_184, List.forall_mem_cons.2 ⟨sub5_185, List.forall_mem_cons.2 ⟨sub5_186, List.forall_mem_cons.2 ⟨sub5_187, List.forall_mem_cons.2 ⟨sub5_188, List.forall_mem_cons.2 ⟨sub5_189, List.forall_mem_cons.2 ⟨sub5_190, List.forall_mem_cons.2 ⟨sub5_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_192 : sub5 [-2, 1, -7] = true := by decide +kernel
theorem sub5_193 : sub5 [-2, 1, -6] = true := by decide +kernel
theorem sub5_194 : sub5 [-2, 1, -5] = true := by decide +kernel
theorem sub5_195 : sub5 [-2, 1, -4] = true := by decide +kernel
theorem sub5_196 : sub5 [-2, 1, -3] = true := by decide +kernel
theorem sub5_197 : sub5 [-2, 1, -2] = true := by decide +kernel
theorem sub5_198 : sub5 [-2, 1, -1] = true := by decide +kernel
theorem sub5_199 : sub5 [-2, 1, 0] = true := by decide +kernel
theorem sub5_200 : sub5 [-2, 1, 1] = true := by decide +kernel
theorem sub5_201 : sub5 [-2, 1, 2] = true := by decide +kernel
theorem sub5_202 : sub5 [-2, 1, 3] = true := by decide +kernel
theorem sub5_203 : sub5 [-2, 1, 4] = true := by decide +kernel
theorem sub5_204 : sub5 [-2, 1, 5] = true := by decide +kernel
theorem sub5_205 : sub5 [-2, 1, 6] = true := by decide +kernel
theorem sub5_206 : sub5 [-2, 2, -8] = true := by decide +kernel
theorem sub5_207 : sub5 [-2, 2, -7] = true := by decide +kernel
theorem sub5_208 : sub5 [-2, 2, -6] = true := by decide +kernel
theorem sub5_209 : sub5 [-2, 2, -5] = true := by decide +kernel
theorem sub5_210 : sub5 [-2, 2, -4] = true := by decide +kernel
theorem sub5_211 : sub5 [-2, 2, -3] = true := by decide +kernel
theorem sub5_212 : sub5 [-2, 2, -2] = true := by decide +kernel
theorem sub5_213 : sub5 [-2, 2, -1] = true := by decide +kernel
theorem sub5_214 : sub5 [-2, 2, 0] = true := by decide +kernel
theorem sub5_215 : sub5 [-2, 2, 1] = true := by decide +kernel
theorem sub5_216 : sub5 [-2, 2, 2] = true := by decide +kernel
theorem sub5_217 : sub5 [-2, 2, 3] = true := by decide +kernel
theorem sub5_218 : sub5 [-2, 2, 4] = true := by decide +kernel
theorem sub5_219 : sub5 [-2, 2, 5] = true := by decide +kernel
theorem sub5_220 : sub5 [-2, 2, 6] = true := by decide +kernel
theorem sub5_221 : sub5 [-2, 3, -8] = true := by decide +kernel
theorem sub5_222 : sub5 [-2, 3, -7] = true := by decide +kernel
theorem sub5_223 : sub5 [-2, 3, -6] = true := by decide +kernel
theorem sb5_6 : ∀ q ∈ blk5_6, sub5 q = true := by
  unfold blk5_6
  exact List.forall_mem_cons.2 ⟨sub5_192, List.forall_mem_cons.2 ⟨sub5_193, List.forall_mem_cons.2 ⟨sub5_194, List.forall_mem_cons.2 ⟨sub5_195, List.forall_mem_cons.2 ⟨sub5_196, List.forall_mem_cons.2 ⟨sub5_197, List.forall_mem_cons.2 ⟨sub5_198, List.forall_mem_cons.2 ⟨sub5_199, List.forall_mem_cons.2 ⟨sub5_200, List.forall_mem_cons.2 ⟨sub5_201, List.forall_mem_cons.2 ⟨sub5_202, List.forall_mem_cons.2 ⟨sub5_203, List.forall_mem_cons.2 ⟨sub5_204, List.forall_mem_cons.2 ⟨sub5_205, List.forall_mem_cons.2 ⟨sub5_206, List.forall_mem_cons.2 ⟨sub5_207, List.forall_mem_cons.2 ⟨sub5_208, List.forall_mem_cons.2 ⟨sub5_209, List.forall_mem_cons.2 ⟨sub5_210, List.forall_mem_cons.2 ⟨sub5_211, List.forall_mem_cons.2 ⟨sub5_212, List.forall_mem_cons.2 ⟨sub5_213, List.forall_mem_cons.2 ⟨sub5_214, List.forall_mem_cons.2 ⟨sub5_215, List.forall_mem_cons.2 ⟨sub5_216, List.forall_mem_cons.2 ⟨sub5_217, List.forall_mem_cons.2 ⟨sub5_218, List.forall_mem_cons.2 ⟨sub5_219, List.forall_mem_cons.2 ⟨sub5_220, List.forall_mem_cons.2 ⟨sub5_221, List.forall_mem_cons.2 ⟨sub5_222, List.forall_mem_cons.2 ⟨sub5_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_224 : sub5 [-2, 3, -5] = true := by decide +kernel
theorem sub5_225 : sub5 [-2, 3, -4] = true := by decide +kernel
theorem sub5_226 : sub5 [-2, 3, -3] = true := by decide +kernel
theorem sub5_227 : sub5 [-2, 3, -2] = true := by decide +kernel
theorem sub5_228 : sub5 [-2, 3, -1] = true := by decide +kernel
theorem sub5_229 : sub5 [-2, 3, 0] = true := by decide +kernel
theorem sub5_230 : sub5 [-2, 3, 1] = true := by decide +kernel
theorem sub5_231 : sub5 [-2, 3, 2] = true := by decide +kernel
theorem sub5_232 : sub5 [-2, 3, 3] = true := by decide +kernel
theorem sub5_233 : sub5 [-2, 3, 4] = true := by decide +kernel
theorem sub5_234 : sub5 [-2, 3, 5] = true := by decide +kernel
theorem sub5_235 : sub5 [-2, 4, -9] = true := by decide +kernel
theorem sub5_236 : sub5 [-2, 4, -8] = true := by decide +kernel
theorem sub5_237 : sub5 [-2, 4, -7] = true := by decide +kernel
theorem sub5_238 : sub5 [-2, 4, -6] = true := by decide +kernel
theorem sub5_239 : sub5 [-2, 4, -5] = true := by decide +kernel
theorem sub5_240 : sub5 [-2, 4, -4] = true := by decide +kernel
theorem sub5_241 : sub5 [-2, 4, -3] = true := by decide +kernel
theorem sub5_242 : sub5 [-2, 4, -2] = true := by decide +kernel
theorem sub5_243 : sub5 [-2, 4, -1] = true := by decide +kernel
theorem sub5_244 : sub5 [-2, 4, 0] = true := by decide +kernel
theorem sub5_245 : sub5 [-2, 4, 1] = true := by decide +kernel
theorem sub5_246 : sub5 [-2, 4, 2] = true := by decide +kernel
theorem sub5_247 : sub5 [-2, 4, 3] = true := by decide +kernel
theorem sub5_248 : sub5 [-2, 4, 4] = true := by decide +kernel
theorem sub5_249 : sub5 [-2, 5] = true := by decide +kernel
theorem sub5_250 : sub5 [-2, 6] = true := by decide +kernel
theorem sub5_251 : sub5 [-2, 7] = true := by decide +kernel
theorem sub5_252 : sub5 [-2, 8] = true := by decide +kernel
theorem sub5_253 : sub5 [-1, -9] = true := by decide +kernel
theorem sub5_254 : sub5 [-1, -8] = true := by decide +kernel
theorem sub5_255 : sub5 [-1, -7] = true := by decide +kernel
theorem sb5_7 : ∀ q ∈ blk5_7, sub5 q = true := by
  unfold blk5_7
  exact List.forall_mem_cons.2 ⟨sub5_224, List.forall_mem_cons.2 ⟨sub5_225, List.forall_mem_cons.2 ⟨sub5_226, List.forall_mem_cons.2 ⟨sub5_227, List.forall_mem_cons.2 ⟨sub5_228, List.forall_mem_cons.2 ⟨sub5_229, List.forall_mem_cons.2 ⟨sub5_230, List.forall_mem_cons.2 ⟨sub5_231, List.forall_mem_cons.2 ⟨sub5_232, List.forall_mem_cons.2 ⟨sub5_233, List.forall_mem_cons.2 ⟨sub5_234, List.forall_mem_cons.2 ⟨sub5_235, List.forall_mem_cons.2 ⟨sub5_236, List.forall_mem_cons.2 ⟨sub5_237, List.forall_mem_cons.2 ⟨sub5_238, List.forall_mem_cons.2 ⟨sub5_239, List.forall_mem_cons.2 ⟨sub5_240, List.forall_mem_cons.2 ⟨sub5_241, List.forall_mem_cons.2 ⟨sub5_242, List.forall_mem_cons.2 ⟨sub5_243, List.forall_mem_cons.2 ⟨sub5_244, List.forall_mem_cons.2 ⟨sub5_245, List.forall_mem_cons.2 ⟨sub5_246, List.forall_mem_cons.2 ⟨sub5_247, List.forall_mem_cons.2 ⟨sub5_248, List.forall_mem_cons.2 ⟨sub5_249, List.forall_mem_cons.2 ⟨sub5_250, List.forall_mem_cons.2 ⟨sub5_251, List.forall_mem_cons.2 ⟨sub5_252, List.forall_mem_cons.2 ⟨sub5_253, List.forall_mem_cons.2 ⟨sub5_254, List.forall_mem_cons.2 ⟨sub5_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C044
