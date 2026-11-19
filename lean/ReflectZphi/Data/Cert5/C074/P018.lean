import ReflectZphi.Data.Cert5.C074.Base

namespace ReflectZphi.Data.Cert5.C074
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub11_32 : sub11 [-4, 0, 1] = true := by decide +kernel
theorem sub11_33 : sub11 [-4, 0, 2] = true := by decide +kernel
theorem sub11_34 : sub11 [-4, 0, 3] = true := by decide +kernel
theorem sub11_35 : sub11 [-4, 0, 4] = true := by decide +kernel
theorem sub11_36 : sub11 [-4, 0, 5] = true := by decide +kernel
theorem sub11_37 : sub11 [-4, 0, 6] = true := by decide +kernel
theorem sub11_38 : sub11 [-4, 0, 7] = true := by decide +kernel
theorem sub11_39 : sub11 [-4, 1] = true := by decide +kernel
theorem sub11_40 : sub11 [-4, 2] = true := by decide +kernel
theorem sub11_41 : sub11 [-4, 3] = true := by decide +kernel
theorem sub11_42 : sub11 [-3, -6] = true := by decide +kernel
theorem sub11_43 : sub11 [-3, -5] = true := by decide +kernel
theorem sub11_44 : sub11 [-3, -4] = true := by decide +kernel
theorem sub11_45 : sub11 [-3, -3, -8] = true := by decide +kernel
theorem sub11_46 : sub11 [-3, -3, -7] = true := by decide +kernel
theorem sub11_47 : sub11 [-3, -3, -6] = true := by decide +kernel
theorem sub11_48 : sub11 [-3, -3, -5] = true := by decide +kernel
theorem sub11_49 : sub11 [-3, -3, -4] = true := by decide +kernel
theorem sub11_50 : sub11 [-3, -3, -3] = true := by decide +kernel
theorem sub11_51 : sub11 [-3, -3, -2] = true := by decide +kernel
theorem sub11_52 : sub11 [-3, -3, -1] = true := by decide +kernel
theorem sub11_53 : sub11 [-3, -3, 0] = true := by decide +kernel
theorem sub11_54 : sub11 [-3, -3, 1] = true := by decide +kernel
theorem sub11_55 : sub11 [-3, -3, 2] = true := by decide +kernel
theorem sub11_56 : sub11 [-3, -3, 3] = true := by decide +kernel
theorem sub11_57 : sub11 [-3, -3, 4] = true := by decide +kernel
theorem sub11_58 : sub11 [-3, -3, 5] = true := by decide +kernel
theorem sub11_59 : sub11 [-3, -2, -8] = true := by decide +kernel
theorem sub11_60 : sub11 [-3, -2, -7] = true := by decide +kernel
theorem sub11_61 : sub11 [-3, -2, -6] = true := by decide +kernel
theorem sub11_62 : sub11 [-3, -2, -5] = true := by decide +kernel
theorem sub11_63 : sub11 [-3, -2, -4] = true := by decide +kernel
theorem sb11_1 : ∀ q ∈ blk11_1, sub11 q = true := by
  unfold blk11_1
  exact List.forall_mem_cons.2 ⟨sub11_32, List.forall_mem_cons.2 ⟨sub11_33, List.forall_mem_cons.2 ⟨sub11_34, List.forall_mem_cons.2 ⟨sub11_35, List.forall_mem_cons.2 ⟨sub11_36, List.forall_mem_cons.2 ⟨sub11_37, List.forall_mem_cons.2 ⟨sub11_38, List.forall_mem_cons.2 ⟨sub11_39, List.forall_mem_cons.2 ⟨sub11_40, List.forall_mem_cons.2 ⟨sub11_41, List.forall_mem_cons.2 ⟨sub11_42, List.forall_mem_cons.2 ⟨sub11_43, List.forall_mem_cons.2 ⟨sub11_44, List.forall_mem_cons.2 ⟨sub11_45, List.forall_mem_cons.2 ⟨sub11_46, List.forall_mem_cons.2 ⟨sub11_47, List.forall_mem_cons.2 ⟨sub11_48, List.forall_mem_cons.2 ⟨sub11_49, List.forall_mem_cons.2 ⟨sub11_50, List.forall_mem_cons.2 ⟨sub11_51, List.forall_mem_cons.2 ⟨sub11_52, List.forall_mem_cons.2 ⟨sub11_53, List.forall_mem_cons.2 ⟨sub11_54, List.forall_mem_cons.2 ⟨sub11_55, List.forall_mem_cons.2 ⟨sub11_56, List.forall_mem_cons.2 ⟨sub11_57, List.forall_mem_cons.2 ⟨sub11_58, List.forall_mem_cons.2 ⟨sub11_59, List.forall_mem_cons.2 ⟨sub11_60, List.forall_mem_cons.2 ⟨sub11_61, List.forall_mem_cons.2 ⟨sub11_62, List.forall_mem_cons.2 ⟨sub11_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub11_64 : sub11 [-3, -2, -3] = true := by decide +kernel
theorem sub11_65 : sub11 [-3, -2, -2] = true := by decide +kernel
theorem sub11_66 : sub11 [-3, -2, -1] = true := by decide +kernel
theorem sub11_67 : sub11 [-3, -2, 0] = true := by decide +kernel
theorem sub11_68 : sub11 [-3, -2, 1] = true := by decide +kernel
theorem sub11_69 : sub11 [-3, -2, 2] = true := by decide +kernel
theorem sub11_70 : sub11 [-3, -2, 3] = true := by decide +kernel
theorem sub11_71 : sub11 [-3, -2, 4] = true := by decide +kernel
theorem sub11_72 : sub11 [-3, -2, 5] = true := by decide +kernel
theorem sub11_73 : sub11 [-3, -2, 6] = true := by decide +kernel
theorem sub11_74 : sub11 [-3, -2, 7] = true := by decide +kernel
theorem sub11_75 : sub11 [-3, -1, -8] = true := by decide +kernel
theorem sub11_76 : sub11 [-3, -1, -7] = true := by decide +kernel
theorem sub11_77 : sub11 [-3, -1, -6] = true := by decide +kernel
theorem sub11_78 : sub11 [-3, -1, -5] = true := by decide +kernel
theorem sub11_79 : sub11 [-3, -1, -4] = true := by decide +kernel
theorem sub11_80 : sub11 [-3, -1, -3] = true := by decide +kernel
theorem sub11_81 : sub11 [-3, -1, -2] = true := by decide +kernel
theorem sub11_82 : sub11 [-3, -1, -1] = true := by decide +kernel
theorem sub11_83 : sub11 [-3, -1, 0] = true := by decide +kernel
theorem sub11_84 : sub11 [-3, -1, 1] = true := by decide +kernel
theorem sub11_85 : sub11 [-3, -1, 2] = true := by decide +kernel
theorem sub11_86 : sub11 [-3, -1, 3] = true := by decide +kernel
theorem sub11_87 : sub11 [-3, -1, 4] = true := by decide +kernel
theorem sub11_88 : sub11 [-3, -1, 5] = true := by decide +kernel
theorem sub11_89 : sub11 [-3, -1, 6] = true := by decide +kernel
theorem sub11_90 : sub11 [-3, -1, 7] = true := by decide +kernel
theorem sub11_91 : sub11 [-3, 0, -8] = true := by decide +kernel
theorem sub11_92 : sub11 [-3, 0, -7] = true := by decide +kernel
theorem sub11_93 : sub11 [-3, 0, -6] = true := by decide +kernel
theorem sub11_94 : sub11 [-3, 0, -5] = true := by decide +kernel
theorem sub11_95 : sub11 [-3, 0, -4] = true := by decide +kernel
theorem sb11_2 : ∀ q ∈ blk11_2, sub11 q = true := by
  unfold blk11_2
  exact List.forall_mem_cons.2 ⟨sub11_64, List.forall_mem_cons.2 ⟨sub11_65, List.forall_mem_cons.2 ⟨sub11_66, List.forall_mem_cons.2 ⟨sub11_67, List.forall_mem_cons.2 ⟨sub11_68, List.forall_mem_cons.2 ⟨sub11_69, List.forall_mem_cons.2 ⟨sub11_70, List.forall_mem_cons.2 ⟨sub11_71, List.forall_mem_cons.2 ⟨sub11_72, List.forall_mem_cons.2 ⟨sub11_73, List.forall_mem_cons.2 ⟨sub11_74, List.forall_mem_cons.2 ⟨sub11_75, List.forall_mem_cons.2 ⟨sub11_76, List.forall_mem_cons.2 ⟨sub11_77, List.forall_mem_cons.2 ⟨sub11_78, List.forall_mem_cons.2 ⟨sub11_79, List.forall_mem_cons.2 ⟨sub11_80, List.forall_mem_cons.2 ⟨sub11_81, List.forall_mem_cons.2 ⟨sub11_82, List.forall_mem_cons.2 ⟨sub11_83, List.forall_mem_cons.2 ⟨sub11_84, List.forall_mem_cons.2 ⟨sub11_85, List.forall_mem_cons.2 ⟨sub11_86, List.forall_mem_cons.2 ⟨sub11_87, List.forall_mem_cons.2 ⟨sub11_88, List.forall_mem_cons.2 ⟨sub11_89, List.forall_mem_cons.2 ⟨sub11_90, List.forall_mem_cons.2 ⟨sub11_91, List.forall_mem_cons.2 ⟨sub11_92, List.forall_mem_cons.2 ⟨sub11_93, List.forall_mem_cons.2 ⟨sub11_94, List.forall_mem_cons.2 ⟨sub11_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub11_96 : sub11 [-3, 0, -3] = true := by decide +kernel
theorem sub11_97 : sub11 [-3, 0, -2] = true := by decide +kernel
theorem sub11_98 : sub11 [-3, 0, -1] = true := by decide +kernel
theorem sub11_99 : sub11 [-3, 0, 0] = true := by decide +kernel
theorem sub11_100 : sub11 [-3, 0, 1] = true := by decide +kernel
theorem sub11_101 : sub11 [-3, 0, 2] = true := by decide +kernel
theorem sub11_102 : sub11 [-3, 0, 3] = true := by decide +kernel
theorem sub11_103 : sub11 [-3, 0, 4] = true := by decide +kernel
theorem sub11_104 : sub11 [-3, 0, 5] = true := by decide +kernel
theorem sub11_105 : sub11 [-3, 0, 6] = true := by decide +kernel
theorem sub11_106 : sub11 [-3, 0, 7] = true := by decide +kernel
theorem sub11_107 : sub11 [-3, 0, 8] = true := by decide +kernel
theorem sub11_108 : sub11 [-3, 1, -7] = true := by decide +kernel
theorem sub11_109 : sub11 [-3, 1, -6] = true := by decide +kernel
theorem sub11_110 : sub11 [-3, 1, -5] = true := by decide +kernel
theorem sub11_111 : sub11 [-3, 1, -4] = true := by decide +kernel
theorem sub11_112 : sub11 [-3, 1, -3] = true := by decide +kernel
theorem sub11_113 : sub11 [-3, 1, -2] = true := by decide +kernel
theorem sub11_114 : sub11 [-3, 1, -1] = true := by decide +kernel
theorem sub11_115 : sub11 [-3, 1, 0] = true := by decide +kernel
theorem sub11_116 : sub11 [-3, 1, 1] = true := by decide +kernel
theorem sub11_117 : sub11 [-3, 1, 2] = true := by decide +kernel
theorem sub11_118 : sub11 [-3, 1, 3] = true := by decide +kernel
theorem sub11_119 : sub11 [-3, 1, 4] = true := by decide +kernel
theorem sub11_120 : sub11 [-3, 1, 5] = true := by decide +kernel
theorem sub11_121 : sub11 [-3, 1, 6] = true := by decide +kernel
theorem sub11_122 : sub11 [-3, 1, 7] = true := by decide +kernel
theorem sub11_123 : sub11 [-3, 1, 8] = true := by decide +kernel
theorem sub11_124 : sub11 [-3, 2, -6] = true := by decide +kernel
theorem sub11_125 : sub11 [-3, 2, -5] = true := by decide +kernel
theorem sub11_126 : sub11 [-3, 2, -4] = true := by decide +kernel
theorem sub11_127 : sub11 [-3, 2, -3] = true := by decide +kernel
theorem sb11_3 : ∀ q ∈ blk11_3, sub11 q = true := by
  unfold blk11_3
  exact List.forall_mem_cons.2 ⟨sub11_96, List.forall_mem_cons.2 ⟨sub11_97, List.forall_mem_cons.2 ⟨sub11_98, List.forall_mem_cons.2 ⟨sub11_99, List.forall_mem_cons.2 ⟨sub11_100, List.forall_mem_cons.2 ⟨sub11_101, List.forall_mem_cons.2 ⟨sub11_102, List.forall_mem_cons.2 ⟨sub11_103, List.forall_mem_cons.2 ⟨sub11_104, List.forall_mem_cons.2 ⟨sub11_105, List.forall_mem_cons.2 ⟨sub11_106, List.forall_mem_cons.2 ⟨sub11_107, List.forall_mem_cons.2 ⟨sub11_108, List.forall_mem_cons.2 ⟨sub11_109, List.forall_mem_cons.2 ⟨sub11_110, List.forall_mem_cons.2 ⟨sub11_111, List.forall_mem_cons.2 ⟨sub11_112, List.forall_mem_cons.2 ⟨sub11_113, List.forall_mem_cons.2 ⟨sub11_114, List.forall_mem_cons.2 ⟨sub11_115, List.forall_mem_cons.2 ⟨sub11_116, List.forall_mem_cons.2 ⟨sub11_117, List.forall_mem_cons.2 ⟨sub11_118, List.forall_mem_cons.2 ⟨sub11_119, List.forall_mem_cons.2 ⟨sub11_120, List.forall_mem_cons.2 ⟨sub11_121, List.forall_mem_cons.2 ⟨sub11_122, List.forall_mem_cons.2 ⟨sub11_123, List.forall_mem_cons.2 ⟨sub11_124, List.forall_mem_cons.2 ⟨sub11_125, List.forall_mem_cons.2 ⟨sub11_126, List.forall_mem_cons.2 ⟨sub11_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub11_128 : sub11 [-3, 2, -2] = true := by decide +kernel
theorem sub11_129 : sub11 [-3, 2, -1] = true := by decide +kernel
theorem sub11_130 : sub11 [-3, 2, 0] = true := by decide +kernel
theorem sub11_131 : sub11 [-3, 2, 1] = true := by decide +kernel
theorem sub11_132 : sub11 [-3, 2, 2] = true := by decide +kernel
theorem sub11_133 : sub11 [-3, 2, 3] = true := by decide +kernel
theorem sub11_134 : sub11 [-3, 2, 4] = true := by decide +kernel
theorem sub11_135 : sub11 [-3, 2, 5] = true := by decide +kernel
theorem sub11_136 : sub11 [-3, 2, 6] = true := by decide +kernel
theorem sub11_137 : sub11 [-3, 2, 7] = true := by decide +kernel
theorem sub11_138 : sub11 [-3, 2, 8] = true := by decide +kernel
theorem sub11_139 : sub11 [-3, 3] = true := by decide +kernel
theorem sub11_140 : sub11 [-3, 4] = true := by decide +kernel
theorem sub11_141 : sub11 [-2, -6] = true := by decide +kernel
theorem sub11_142 : sub11 [-2, -5] = true := by decide +kernel
theorem sub11_143 : sub11 [-2, -4, -8] = true := by decide +kernel
theorem sub11_144 : sub11 [-2, -4, -7] = true := by decide +kernel
theorem sub11_145 : sub11 [-2, -4, -6] = true := by decide +kernel
theorem sub11_146 : sub11 [-2, -4, -5] = true := by decide +kernel
theorem sub11_147 : sub11 [-2, -4, -4] = true := by decide +kernel
theorem sub11_148 : sub11 [-2, -4, -3] = true := by decide +kernel
theorem sub11_149 : sub11 [-2, -4, -2] = true := by decide +kernel
theorem sub11_150 : sub11 [-2, -4, -1] = true := by decide +kernel
theorem sub11_151 : sub11 [-2, -4, 0] = true := by decide +kernel
theorem sub11_152 : sub11 [-2, -4, 1] = true := by decide +kernel
theorem sub11_153 : sub11 [-2, -4, 2] = true := by decide +kernel
theorem sub11_154 : sub11 [-2, -4, 3] = true := by decide +kernel
theorem sub11_155 : sub11 [-2, -4, 4] = true := by decide +kernel
theorem sub11_156 : sub11 [-2, -3, -9] = true := by decide +kernel
theorem sub11_157 : sub11 [-2, -3, -8] = true := by decide +kernel
theorem sub11_158 : sub11 [-2, -3, -7] = true := by decide +kernel
theorem sub11_159 : sub11 [-2, -3, -6] = true := by decide +kernel
theorem sb11_4 : ∀ q ∈ blk11_4, sub11 q = true := by
  unfold blk11_4
  exact List.forall_mem_cons.2 ⟨sub11_128, List.forall_mem_cons.2 ⟨sub11_129, List.forall_mem_cons.2 ⟨sub11_130, List.forall_mem_cons.2 ⟨sub11_131, List.forall_mem_cons.2 ⟨sub11_132, List.forall_mem_cons.2 ⟨sub11_133, List.forall_mem_cons.2 ⟨sub11_134, List.forall_mem_cons.2 ⟨sub11_135, List.forall_mem_cons.2 ⟨sub11_136, List.forall_mem_cons.2 ⟨sub11_137, List.forall_mem_cons.2 ⟨sub11_138, List.forall_mem_cons.2 ⟨sub11_139, List.forall_mem_cons.2 ⟨sub11_140, List.forall_mem_cons.2 ⟨sub11_141, List.forall_mem_cons.2 ⟨sub11_142, List.forall_mem_cons.2 ⟨sub11_143, List.forall_mem_cons.2 ⟨sub11_144, List.forall_mem_cons.2 ⟨sub11_145, List.forall_mem_cons.2 ⟨sub11_146, List.forall_mem_cons.2 ⟨sub11_147, List.forall_mem_cons.2 ⟨sub11_148, List.forall_mem_cons.2 ⟨sub11_149, List.forall_mem_cons.2 ⟨sub11_150, List.forall_mem_cons.2 ⟨sub11_151, List.forall_mem_cons.2 ⟨sub11_152, List.forall_mem_cons.2 ⟨sub11_153, List.forall_mem_cons.2 ⟨sub11_154, List.forall_mem_cons.2 ⟨sub11_155, List.forall_mem_cons.2 ⟨sub11_156, List.forall_mem_cons.2 ⟨sub11_157, List.forall_mem_cons.2 ⟨sub11_158, List.forall_mem_cons.2 ⟨sub11_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub11_160 : sub11 [-2, -3, -5] = true := by decide +kernel
theorem sub11_161 : sub11 [-2, -3, -4] = true := by decide +kernel
theorem sub11_162 : sub11 [-2, -3, -3] = true := by decide +kernel
theorem sub11_163 : sub11 [-2, -3, -2] = true := by decide +kernel
theorem sub11_164 : sub11 [-2, -3, -1] = true := by decide +kernel
theorem sub11_165 : sub11 [-2, -3, 0] = true := by decide +kernel
theorem sub11_166 : sub11 [-2, -3, 1] = true := by decide +kernel
theorem sub11_167 : sub11 [-2, -3, 2] = true := by decide +kernel
theorem sub11_168 : sub11 [-2, -3, 3] = true := by decide +kernel
theorem sub11_169 : sub11 [-2, -3, 4] = true := by decide +kernel
theorem sub11_170 : sub11 [-2, -3, 5] = true := by decide +kernel
theorem sub11_171 : sub11 [-2, -3, 6] = true := by decide +kernel
theorem sub11_172 : sub11 [-2, -2, -9] = true := by decide +kernel
theorem sub11_173 : sub11 [-2, -2, -8] = true := by decide +kernel
theorem sub11_174 : sub11 [-2, -2, -7] = true := by decide +kernel
theorem sub11_175 : sub11 [-2, -2, -6] = true := by decide +kernel
theorem sub11_176 : sub11 [-2, -2, -5] = true := by decide +kernel
theorem sub11_177 : sub11 [-2, -2, -4] = true := by decide +kernel
theorem sub11_178 : sub11 [-2, -2, -3] = true := by decide +kernel
theorem sub11_179 : sub11 [-2, -2, -2] = true := by decide +kernel
theorem sub11_180 : sub11 [-2, -2, -1] = true := by decide +kernel
theorem sub11_181 : sub11 [-2, -2, 0] = true := by decide +kernel
theorem sub11_182 : sub11 [-2, -2, 1] = true := by decide +kernel
theorem sub11_183 : sub11 [-2, -2, 2] = true := by decide +kernel
theorem sub11_184 : sub11 [-2, -2, 3] = true := by decide +kernel
theorem sub11_185 : sub11 [-2, -2, 4] = true := by decide +kernel
theorem sub11_186 : sub11 [-2, -2, 5] = true := by decide +kernel
theorem sub11_187 : sub11 [-2, -2, 6] = true := by decide +kernel
theorem sub11_188 : sub11 [-2, -2, 7] = true := by decide +kernel
theorem sub11_189 : sub11 [-2, -1, -9] = true := by decide +kernel
theorem sub11_190 : sub11 [-2, -1, -8] = true := by decide +kernel
theorem sub11_191 : sub11 [-2, -1, -7] = true := by decide +kernel
theorem sb11_5 : ∀ q ∈ blk11_5, sub11 q = true := by
  unfold blk11_5
  exact List.forall_mem_cons.2 ⟨sub11_160, List.forall_mem_cons.2 ⟨sub11_161, List.forall_mem_cons.2 ⟨sub11_162, List.forall_mem_cons.2 ⟨sub11_163, List.forall_mem_cons.2 ⟨sub11_164, List.forall_mem_cons.2 ⟨sub11_165, List.forall_mem_cons.2 ⟨sub11_166, List.forall_mem_cons.2 ⟨sub11_167, List.forall_mem_cons.2 ⟨sub11_168, List.forall_mem_cons.2 ⟨sub11_169, List.forall_mem_cons.2 ⟨sub11_170, List.forall_mem_cons.2 ⟨sub11_171, List.forall_mem_cons.2 ⟨sub11_172, List.forall_mem_cons.2 ⟨sub11_173, List.forall_mem_cons.2 ⟨sub11_174, List.forall_mem_cons.2 ⟨sub11_175, List.forall_mem_cons.2 ⟨sub11_176, List.forall_mem_cons.2 ⟨sub11_177, List.forall_mem_cons.2 ⟨sub11_178, List.forall_mem_cons.2 ⟨sub11_179, List.forall_mem_cons.2 ⟨sub11_180, List.forall_mem_cons.2 ⟨sub11_181, List.forall_mem_cons.2 ⟨sub11_182, List.forall_mem_cons.2 ⟨sub11_183, List.forall_mem_cons.2 ⟨sub11_184, List.forall_mem_cons.2 ⟨sub11_185, List.forall_mem_cons.2 ⟨sub11_186, List.forall_mem_cons.2 ⟨sub11_187, List.forall_mem_cons.2 ⟨sub11_188, List.forall_mem_cons.2 ⟨sub11_189, List.forall_mem_cons.2 ⟨sub11_190, List.forall_mem_cons.2 ⟨sub11_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub11_192 : sub11 [-2, -1, -6] = true := by decide +kernel
theorem sub11_193 : sub11 [-2, -1, -5] = true := by decide +kernel
theorem sub11_194 : sub11 [-2, -1, -4] = true := by decide +kernel
theorem sub11_195 : sub11 [-2, -1, -3] = true := by decide +kernel
theorem sub11_196 : sub11 [-2, -1, -2] = true := by decide +kernel
theorem sub11_197 : sub11 [-2, -1, -1] = true := by decide +kernel
theorem sub11_198 : sub11 [-2, -1, 0] = true := by decide +kernel
theorem sub11_199 : sub11 [-2, -1, 1] = true := by decide +kernel
theorem sub11_200 : sub11 [-2, -1, 2] = true := by decide +kernel
theorem sub11_201 : sub11 [-2, -1, 3] = true := by decide +kernel
theorem sub11_202 : sub11 [-2, -1, 4] = true := by decide +kernel
theorem sub11_203 : sub11 [-2, -1, 5] = true := by decide +kernel
theorem sub11_204 : sub11 [-2, -1, 6] = true := by decide +kernel
theorem sub11_205 : sub11 [-2, -1, 7] = true := by decide +kernel
theorem sub11_206 : sub11 [-2, -1, 8] = true := by decide +kernel
theorem sub11_207 : sub11 [-2, 0, -9] = true := by decide +kernel
theorem sub11_208 : sub11 [-2, 0, -8] = true := by decide +kernel
theorem sub11_209 : sub11 [-2, 0, -7] = true := by decide +kernel
theorem sub11_210 : sub11 [-2, 0, -6] = true := by decide +kernel
theorem sub11_211 : sub11 [-2, 0, -5] = true := by decide +kernel
theorem sub11_212 : sub11 [-2, 0, -4] = true := by decide +kernel
theorem sub11_213 : sub11 [-2, 0, -3] = true := by decide +kernel
theorem sub11_214 : sub11 [-2, 0, -2] = true := by decide +kernel
theorem sub11_215 : sub11 [-2, 0, -1] = true := by decide +kernel
theorem sub11_216 : sub11 [-2, 0, 0] = true := by decide +kernel
theorem sub11_217 : sub11 [-2, 0, 1] = true := by decide +kernel
theorem sub11_218 : sub11 [-2, 0, 2] = true := by decide +kernel
theorem sub11_219 : sub11 [-2, 0, 3] = true := by decide +kernel
theorem sub11_220 : sub11 [-2, 0, 4] = true := by decide +kernel
theorem sub11_221 : sub11 [-2, 0, 5] = true := by decide +kernel
theorem sub11_222 : sub11 [-2, 0, 6] = true := by decide +kernel
theorem sub11_223 : sub11 [-2, 0, 7] = true := by decide +kernel
theorem sb11_6 : ∀ q ∈ blk11_6, sub11 q = true := by
  unfold blk11_6
  exact List.forall_mem_cons.2 ⟨sub11_192, List.forall_mem_cons.2 ⟨sub11_193, List.forall_mem_cons.2 ⟨sub11_194, List.forall_mem_cons.2 ⟨sub11_195, List.forall_mem_cons.2 ⟨sub11_196, List.forall_mem_cons.2 ⟨sub11_197, List.forall_mem_cons.2 ⟨sub11_198, List.forall_mem_cons.2 ⟨sub11_199, List.forall_mem_cons.2 ⟨sub11_200, List.forall_mem_cons.2 ⟨sub11_201, List.forall_mem_cons.2 ⟨sub11_202, List.forall_mem_cons.2 ⟨sub11_203, List.forall_mem_cons.2 ⟨sub11_204, List.forall_mem_cons.2 ⟨sub11_205, List.forall_mem_cons.2 ⟨sub11_206, List.forall_mem_cons.2 ⟨sub11_207, List.forall_mem_cons.2 ⟨sub11_208, List.forall_mem_cons.2 ⟨sub11_209, List.forall_mem_cons.2 ⟨sub11_210, List.forall_mem_cons.2 ⟨sub11_211, List.forall_mem_cons.2 ⟨sub11_212, List.forall_mem_cons.2 ⟨sub11_213, List.forall_mem_cons.2 ⟨sub11_214, List.forall_mem_cons.2 ⟨sub11_215, List.forall_mem_cons.2 ⟨sub11_216, List.forall_mem_cons.2 ⟨sub11_217, List.forall_mem_cons.2 ⟨sub11_218, List.forall_mem_cons.2 ⟨sub11_219, List.forall_mem_cons.2 ⟨sub11_220, List.forall_mem_cons.2 ⟨sub11_221, List.forall_mem_cons.2 ⟨sub11_222, List.forall_mem_cons.2 ⟨sub11_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub11_224 : sub11 [-2, 0, 8] = true := by decide +kernel
theorem sub11_225 : sub11 [-2, 1, -8] = true := by decide +kernel
theorem sub11_226 : sub11 [-2, 1, -7] = true := by decide +kernel
theorem sub11_227 : sub11 [-2, 1, -6] = true := by decide +kernel
theorem sub11_228 : sub11 [-2, 1, -5] = true := by decide +kernel
theorem sub11_229 : sub11 [-2, 1, -4] = true := by decide +kernel
theorem sub11_230 : sub11 [-2, 1, -3] = true := by decide +kernel
theorem sub11_231 : sub11 [-2, 1, -2] = true := by decide +kernel
theorem sub11_232 : sub11 [-2, 1, -1] = true := by decide +kernel
theorem sub11_233 : sub11 [-2, 1, 0] = true := by decide +kernel
theorem sub11_234 : sub11 [-2, 1, 1] = true := by decide +kernel
theorem sub11_235 : sub11 [-2, 1, 2] = true := by decide +kernel
theorem sub11_236 : sub11 [-2, 1, 3] = true := by decide +kernel
theorem sub11_237 : sub11 [-2, 1, 4] = true := by decide +kernel
theorem sub11_238 : sub11 [-2, 1, 5] = true := by decide +kernel
theorem sub11_239 : sub11 [-2, 1, 6] = true := by decide +kernel
theorem sub11_240 : sub11 [-2, 1, 7] = true := by decide +kernel
theorem sub11_241 : sub11 [-2, 1, 8] = true := by decide +kernel
theorem sub11_242 : sub11 [-2, 1, 9] = true := by decide +kernel
theorem sub11_243 : sub11 [-2, 2, -7] = true := by decide +kernel
theorem sub11_244 : sub11 [-2, 2, -6] = true := by decide +kernel
theorem sub11_245 : sub11 [-2, 2, -5] = true := by decide +kernel
theorem sub11_246 : sub11 [-2, 2, -4] = true := by decide +kernel
theorem sub11_247 : sub11 [-2, 2, -3] = true := by decide +kernel
theorem sub11_248 : sub11 [-2, 2, -2] = true := by decide +kernel
theorem sub11_249 : sub11 [-2, 2, -1] = true := by decide +kernel
theorem sub11_250 : sub11 [-2, 2, 0] = true := by decide +kernel
theorem sub11_251 : sub11 [-2, 2, 1] = true := by decide +kernel
theorem sub11_252 : sub11 [-2, 2, 2] = true := by decide +kernel
theorem sub11_253 : sub11 [-2, 2, 3] = true := by decide +kernel
theorem sub11_254 : sub11 [-2, 2, 4] = true := by decide +kernel
theorem sub11_255 : sub11 [-2, 2, 5] = true := by decide +kernel
theorem sb11_7 : ∀ q ∈ blk11_7, sub11 q = true := by
  unfold blk11_7
  exact List.forall_mem_cons.2 ⟨sub11_224, List.forall_mem_cons.2 ⟨sub11_225, List.forall_mem_cons.2 ⟨sub11_226, List.forall_mem_cons.2 ⟨sub11_227, List.forall_mem_cons.2 ⟨sub11_228, List.forall_mem_cons.2 ⟨sub11_229, List.forall_mem_cons.2 ⟨sub11_230, List.forall_mem_cons.2 ⟨sub11_231, List.forall_mem_cons.2 ⟨sub11_232, List.forall_mem_cons.2 ⟨sub11_233, List.forall_mem_cons.2 ⟨sub11_234, List.forall_mem_cons.2 ⟨sub11_235, List.forall_mem_cons.2 ⟨sub11_236, List.forall_mem_cons.2 ⟨sub11_237, List.forall_mem_cons.2 ⟨sub11_238, List.forall_mem_cons.2 ⟨sub11_239, List.forall_mem_cons.2 ⟨sub11_240, List.forall_mem_cons.2 ⟨sub11_241, List.forall_mem_cons.2 ⟨sub11_242, List.forall_mem_cons.2 ⟨sub11_243, List.forall_mem_cons.2 ⟨sub11_244, List.forall_mem_cons.2 ⟨sub11_245, List.forall_mem_cons.2 ⟨sub11_246, List.forall_mem_cons.2 ⟨sub11_247, List.forall_mem_cons.2 ⟨sub11_248, List.forall_mem_cons.2 ⟨sub11_249, List.forall_mem_cons.2 ⟨sub11_250, List.forall_mem_cons.2 ⟨sub11_251, List.forall_mem_cons.2 ⟨sub11_252, List.forall_mem_cons.2 ⟨sub11_253, List.forall_mem_cons.2 ⟨sub11_254, List.forall_mem_cons.2 ⟨sub11_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub11_256 : sub11 [-2, 2, 6] = true := by decide +kernel
theorem sub11_257 : sub11 [-2, 2, 7] = true := by decide +kernel
theorem sub11_258 : sub11 [-2, 2, 8] = true := by decide +kernel
theorem sub11_259 : sub11 [-2, 2, 9] = true := by decide +kernel
theorem sub11_260 : sub11 [-2, 3, -6] = true := by decide +kernel
theorem sub11_261 : sub11 [-2, 3, -5] = true := by decide +kernel
theorem sub11_262 : sub11 [-2, 3, -4] = true := by decide +kernel
theorem sub11_263 : sub11 [-2, 3, -3] = true := by decide +kernel
theorem sub11_264 : sub11 [-2, 3, -2] = true := by decide +kernel
theorem sub11_265 : sub11 [-2, 3, -1] = true := by decide +kernel
theorem sub11_266 : sub11 [-2, 3, 0] = true := by decide +kernel
theorem sub11_267 : sub11 [-2, 3, 1] = true := by decide +kernel
theorem sub11_268 : sub11 [-2, 3, 2] = true := by decide +kernel
theorem sub11_269 : sub11 [-2, 3, 3] = true := by decide +kernel
theorem sub11_270 : sub11 [-2, 3, 4] = true := by decide +kernel
theorem sub11_271 : sub11 [-2, 3, 5] = true := by decide +kernel
theorem sub11_272 : sub11 [-2, 3, 6] = true := by decide +kernel
theorem sub11_273 : sub11 [-2, 3, 7] = true := by decide +kernel
theorem sub11_274 : sub11 [-2, 3, 8] = true := by decide +kernel
theorem sub11_275 : sub11 [-2, 4] = true := by decide +kernel
theorem sub11_276 : sub11 [-2, 5] = true := by decide +kernel
theorem sub11_277 : sub11 [-1, -7] = true := by decide +kernel
theorem sub11_278 : sub11 [-1, -6] = true := by decide +kernel
theorem sub11_279 : sub11 [-1, -5] = true := by decide +kernel
theorem sub11_280 : sub11 [-1, -4, -9] = true := by decide +kernel
theorem sub11_281 : sub11 [-1, -4, -8] = true := by decide +kernel
theorem sub11_282 : sub11 [-1, -4, -7] = true := by decide +kernel
theorem sub11_283 : sub11 [-1, -4, -6] = true := by decide +kernel
theorem sub11_284 : sub11 [-1, -4, -5] = true := by decide +kernel
theorem sub11_285 : sub11 [-1, -4, -4] = true := by decide +kernel
theorem sub11_286 : sub11 [-1, -4, -3] = true := by decide +kernel
theorem sub11_287 : sub11 [-1, -4, -2] = true := by decide +kernel
theorem sb11_8 : ∀ q ∈ blk11_8, sub11 q = true := by
  unfold blk11_8
  exact List.forall_mem_cons.2 ⟨sub11_256, List.forall_mem_cons.2 ⟨sub11_257, List.forall_mem_cons.2 ⟨sub11_258, List.forall_mem_cons.2 ⟨sub11_259, List.forall_mem_cons.2 ⟨sub11_260, List.forall_mem_cons.2 ⟨sub11_261, List.forall_mem_cons.2 ⟨sub11_262, List.forall_mem_cons.2 ⟨sub11_263, List.forall_mem_cons.2 ⟨sub11_264, List.forall_mem_cons.2 ⟨sub11_265, List.forall_mem_cons.2 ⟨sub11_266, List.forall_mem_cons.2 ⟨sub11_267, List.forall_mem_cons.2 ⟨sub11_268, List.forall_mem_cons.2 ⟨sub11_269, List.forall_mem_cons.2 ⟨sub11_270, List.forall_mem_cons.2 ⟨sub11_271, List.forall_mem_cons.2 ⟨sub11_272, List.forall_mem_cons.2 ⟨sub11_273, List.forall_mem_cons.2 ⟨sub11_274, List.forall_mem_cons.2 ⟨sub11_275, List.forall_mem_cons.2 ⟨sub11_276, List.forall_mem_cons.2 ⟨sub11_277, List.forall_mem_cons.2 ⟨sub11_278, List.forall_mem_cons.2 ⟨sub11_279, List.forall_mem_cons.2 ⟨sub11_280, List.forall_mem_cons.2 ⟨sub11_281, List.forall_mem_cons.2 ⟨sub11_282, List.forall_mem_cons.2 ⟨sub11_283, List.forall_mem_cons.2 ⟨sub11_284, List.forall_mem_cons.2 ⟨sub11_285, List.forall_mem_cons.2 ⟨sub11_286, List.forall_mem_cons.2 ⟨sub11_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub11_288 : sub11 [-1, -4, -1] = true := by decide +kernel
theorem sub11_289 : sub11 [-1, -4, 0] = true := by decide +kernel
theorem sub11_290 : sub11 [-1, -4, 1] = true := by decide +kernel
theorem sub11_291 : sub11 [-1, -4, 2] = true := by decide +kernel
theorem sub11_292 : sub11 [-1, -4, 3] = true := by decide +kernel
theorem sub11_293 : sub11 [-1, -4, 4] = true := by decide +kernel
theorem sub11_294 : sub11 [-1, -4, 5] = true := by decide +kernel
theorem sub11_295 : sub11 [-1, -3, -10] = true := by decide +kernel
theorem sub11_296 : sub11 [-1, -3, -9] = true := by decide +kernel
theorem sub11_297 : sub11 [-1, -3, -8] = true := by decide +kernel
theorem sub11_298 : sub11 [-1, -3, -7] = true := by decide +kernel
theorem sub11_299 : sub11 [-1, -3, -6] = true := by decide +kernel
theorem sub11_300 : sub11 [-1, -3, -5] = true := by decide +kernel
theorem sub11_301 : sub11 [-1, -3, -4] = true := by decide +kernel
theorem sub11_302 : sub11 [-1, -3, -3] = true := by decide +kernel
theorem sub11_303 : sub11 [-1, -3, -2] = true := by decide +kernel
theorem sub11_304 : sub11 [-1, -3, -1] = true := by decide +kernel
theorem sub11_305 : sub11 [-1, -3, 0] = true := by decide +kernel
theorem sub11_306 : sub11 [-1, -3, 1] = true := by decide +kernel
theorem sub11_307 : sub11 [-1, -3, 2] = true := by decide +kernel
theorem sub11_308 : sub11 [-1, -3, 3] = true := by decide +kernel
theorem sub11_309 : sub11 [-1, -3, 4] = true := by decide +kernel
theorem sub11_310 : sub11 [-1, -3, 5] = true := by decide +kernel
theorem sub11_311 : sub11 [-1, -3, 6] = true := by decide +kernel
theorem sub11_312 : sub11 [-1, -2, -10] = true := by decide +kernel
theorem sub11_313 : sub11 [-1, -2, -9] = true := by decide +kernel
theorem sub11_314 : sub11 [-1, -2, -8] = true := by decide +kernel
theorem sub11_315 : sub11 [-1, -2, -7] = true := by decide +kernel
theorem sub11_316 : sub11 [-1, -2, -6] = true := by decide +kernel
theorem sub11_317 : sub11 [-1, -2, -5] = true := by decide +kernel
theorem sub11_318 : sub11 [-1, -2, -4] = true := by decide +kernel
theorem sub11_319 : sub11 [-1, -2, -3] = true := by decide +kernel
theorem sb11_9 : ∀ q ∈ blk11_9, sub11 q = true := by
  unfold blk11_9
  exact List.forall_mem_cons.2 ⟨sub11_288, List.forall_mem_cons.2 ⟨sub11_289, List.forall_mem_cons.2 ⟨sub11_290, List.forall_mem_cons.2 ⟨sub11_291, List.forall_mem_cons.2 ⟨sub11_292, List.forall_mem_cons.2 ⟨sub11_293, List.forall_mem_cons.2 ⟨sub11_294, List.forall_mem_cons.2 ⟨sub11_295, List.forall_mem_cons.2 ⟨sub11_296, List.forall_mem_cons.2 ⟨sub11_297, List.forall_mem_cons.2 ⟨sub11_298, List.forall_mem_cons.2 ⟨sub11_299, List.forall_mem_cons.2 ⟨sub11_300, List.forall_mem_cons.2 ⟨sub11_301, List.forall_mem_cons.2 ⟨sub11_302, List.forall_mem_cons.2 ⟨sub11_303, List.forall_mem_cons.2 ⟨sub11_304, List.forall_mem_cons.2 ⟨sub11_305, List.forall_mem_cons.2 ⟨sub11_306, List.forall_mem_cons.2 ⟨sub11_307, List.forall_mem_cons.2 ⟨sub11_308, List.forall_mem_cons.2 ⟨sub11_309, List.forall_mem_cons.2 ⟨sub11_310, List.forall_mem_cons.2 ⟨sub11_311, List.forall_mem_cons.2 ⟨sub11_312, List.forall_mem_cons.2 ⟨sub11_313, List.forall_mem_cons.2 ⟨sub11_314, List.forall_mem_cons.2 ⟨sub11_315, List.forall_mem_cons.2 ⟨sub11_316, List.forall_mem_cons.2 ⟨sub11_317, List.forall_mem_cons.2 ⟨sub11_318, List.forall_mem_cons.2 ⟨sub11_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub11_320 : sub11 [-1, -2, -2] = true := by decide +kernel
theorem sub11_321 : sub11 [-1, -2, -1] = true := by decide +kernel
theorem sub11_322 : sub11 [-1, -2, 0] = true := by decide +kernel
theorem sub11_323 : sub11 [-1, -2, 1] = true := by decide +kernel
theorem sub11_324 : sub11 [-1, -2, 2] = true := by decide +kernel
theorem sub11_325 : sub11 [-1, -2, 3] = true := by decide +kernel
theorem sub11_326 : sub11 [-1, -2, 4] = true := by decide +kernel
theorem sub11_327 : sub11 [-1, -2, 5] = true := by decide +kernel
theorem sub11_328 : sub11 [-1, -2, 6] = true := by decide +kernel
theorem sub11_329 : sub11 [-1, -2, 7] = true := by decide +kernel
theorem sub11_330 : sub11 [-1, -1, -10] = true := by decide +kernel
theorem sub11_331 : sub11 [-1, -1, -9] = true := by decide +kernel
theorem sub11_332 : sub11 [-1, -1, -8] = true := by decide +kernel
theorem sub11_333 : sub11 [-1, -1, -7] = true := by decide +kernel
theorem sub11_334 : sub11 [-1, -1, -6] = true := by decide +kernel
theorem sub11_335 : sub11 [-1, -1, -5] = true := by decide +kernel
theorem sub11_336 : sub11 [-1, -1, -4] = true := by decide +kernel
theorem sub11_337 : sub11 [-1, -1, -3] = true := by decide +kernel
theorem sub11_338 : sub11 [-1, -1, -2] = true := by decide +kernel
theorem sub11_339 : sub11 [-1, -1, -1] = true := by decide +kernel
theorem sub11_340 : sub11 [-1, -1, 0] = true := by decide +kernel
theorem sub11_341 : sub11 [-1, -1, 1] = true := by decide +kernel
theorem sub11_342 : sub11 [-1, -1, 2] = true := by decide +kernel
theorem sub11_343 : sub11 [-1, -1, 3] = true := by decide +kernel
theorem sub11_344 : sub11 [-1, -1, 4] = true := by decide +kernel
theorem sub11_345 : sub11 [-1, -1, 5] = true := by decide +kernel
theorem sub11_346 : sub11 [-1, -1, 6] = true := by decide +kernel
theorem sub11_347 : sub11 [-1, -1, 7] = true := by decide +kernel
theorem sub11_348 : sub11 [-1, -1, 8] = true := by decide +kernel
theorem sub11_349 : sub11 [-1, 0, -9] = true := by decide +kernel
theorem sub11_350 : sub11 [-1, 0, -8] = true := by decide +kernel
theorem sub11_351 : sub11 [-1, 0, -7] = true := by decide +kernel
theorem sb11_10 : ∀ q ∈ blk11_10, sub11 q = true := by
  unfold blk11_10
  exact List.forall_mem_cons.2 ⟨sub11_320, List.forall_mem_cons.2 ⟨sub11_321, List.forall_mem_cons.2 ⟨sub11_322, List.forall_mem_cons.2 ⟨sub11_323, List.forall_mem_cons.2 ⟨sub11_324, List.forall_mem_cons.2 ⟨sub11_325, List.forall_mem_cons.2 ⟨sub11_326, List.forall_mem_cons.2 ⟨sub11_327, List.forall_mem_cons.2 ⟨sub11_328, List.forall_mem_cons.2 ⟨sub11_329, List.forall_mem_cons.2 ⟨sub11_330, List.forall_mem_cons.2 ⟨sub11_331, List.forall_mem_cons.2 ⟨sub11_332, List.forall_mem_cons.2 ⟨sub11_333, List.forall_mem_cons.2 ⟨sub11_334, List.forall_mem_cons.2 ⟨sub11_335, List.forall_mem_cons.2 ⟨sub11_336, List.forall_mem_cons.2 ⟨sub11_337, List.forall_mem_cons.2 ⟨sub11_338, List.forall_mem_cons.2 ⟨sub11_339, List.forall_mem_cons.2 ⟨sub11_340, List.forall_mem_cons.2 ⟨sub11_341, List.forall_mem_cons.2 ⟨sub11_342, List.forall_mem_cons.2 ⟨sub11_343, List.forall_mem_cons.2 ⟨sub11_344, List.forall_mem_cons.2 ⟨sub11_345, List.forall_mem_cons.2 ⟨sub11_346, List.forall_mem_cons.2 ⟨sub11_347, List.forall_mem_cons.2 ⟨sub11_348, List.forall_mem_cons.2 ⟨sub11_349, List.forall_mem_cons.2 ⟨sub11_350, List.forall_mem_cons.2 ⟨sub11_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub11_352 : sub11 [-1, 0, -6] = true := by decide +kernel
theorem sub11_353 : sub11 [-1, 0, -5] = true := by decide +kernel
theorem sub11_354 : sub11 [-1, 0, -4] = true := by decide +kernel
theorem sub11_355 : sub11 [-1, 0, -3] = true := by decide +kernel
theorem sub11_356 : sub11 [-1, 0, -2] = true := by decide +kernel
theorem sub11_357 : sub11 [-1, 0, -1] = true := by decide +kernel
theorem sub11_358 : sub11 [-1, 0, 0] = true := by decide +kernel
theorem sub11_359 : sub11 [-1, 0, 1] = true := by decide +kernel
theorem sub11_360 : sub11 [-1, 0, 2] = true := by decide +kernel
theorem sub11_361 : sub11 [-1, 0, 3] = true := by decide +kernel
theorem sub11_362 : sub11 [-1, 0, 4] = true := by decide +kernel
theorem sub11_363 : sub11 [-1, 0, 5] = true := by decide +kernel
theorem sub11_364 : sub11 [-1, 0, 6] = true := by decide +kernel
theorem sub11_365 : sub11 [-1, 0, 7] = true := by decide +kernel
theorem sub11_366 : sub11 [-1, 0, 8] = true := by decide +kernel
theorem sub11_367 : sub11 [-1, 0, 9] = true := by decide +kernel
theorem sub11_368 : sub11 [-1, 1, -9] = true := by decide +kernel
theorem sub11_369 : sub11 [-1, 1, -8] = true := by decide +kernel
theorem sub11_370 : sub11 [-1, 1, -7] = true := by decide +kernel
theorem sub11_371 : sub11 [-1, 1, -6] = true := by decide +kernel
theorem sub11_372 : sub11 [-1, 1, -5] = true := by decide +kernel
theorem sub11_373 : sub11 [-1, 1, -4] = true := by decide +kernel
theorem sub11_374 : sub11 [-1, 1, -3] = true := by decide +kernel
theorem sub11_375 : sub11 [-1, 1, -2] = true := by decide +kernel
theorem sub11_376 : sub11 [-1, 1, -1] = true := by decide +kernel
theorem sub11_377 : sub11 [-1, 1, 0] = true := by decide +kernel
theorem sub11_378 : sub11 [-1, 1, 1] = true := by decide +kernel
theorem sub11_379 : sub11 [-1, 1, 2] = true := by decide +kernel
theorem sub11_380 : sub11 [-1, 1, 3] = true := by decide +kernel
theorem sub11_381 : sub11 [-1, 1, 4] = true := by decide +kernel
theorem sub11_382 : sub11 [-1, 1, 5] = true := by decide +kernel
theorem sub11_383 : sub11 [-1, 1, 6] = true := by decide +kernel
theorem sb11_11 : ∀ q ∈ blk11_11, sub11 q = true := by
  unfold blk11_11
  exact List.forall_mem_cons.2 ⟨sub11_352, List.forall_mem_cons.2 ⟨sub11_353, List.forall_mem_cons.2 ⟨sub11_354, List.forall_mem_cons.2 ⟨sub11_355, List.forall_mem_cons.2 ⟨sub11_356, List.forall_mem_cons.2 ⟨sub11_357, List.forall_mem_cons.2 ⟨sub11_358, List.forall_mem_cons.2 ⟨sub11_359, List.forall_mem_cons.2 ⟨sub11_360, List.forall_mem_cons.2 ⟨sub11_361, List.forall_mem_cons.2 ⟨sub11_362, List.forall_mem_cons.2 ⟨sub11_363, List.forall_mem_cons.2 ⟨sub11_364, List.forall_mem_cons.2 ⟨sub11_365, List.forall_mem_cons.2 ⟨sub11_366, List.forall_mem_cons.2 ⟨sub11_367, List.forall_mem_cons.2 ⟨sub11_368, List.forall_mem_cons.2 ⟨sub11_369, List.forall_mem_cons.2 ⟨sub11_370, List.forall_mem_cons.2 ⟨sub11_371, List.forall_mem_cons.2 ⟨sub11_372, List.forall_mem_cons.2 ⟨sub11_373, List.forall_mem_cons.2 ⟨sub11_374, List.forall_mem_cons.2 ⟨sub11_375, List.forall_mem_cons.2 ⟨sub11_376, List.forall_mem_cons.2 ⟨sub11_377, List.forall_mem_cons.2 ⟨sub11_378, List.forall_mem_cons.2 ⟨sub11_379, List.forall_mem_cons.2 ⟨sub11_380, List.forall_mem_cons.2 ⟨sub11_381, List.forall_mem_cons.2 ⟨sub11_382, List.forall_mem_cons.2 ⟨sub11_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub11_384 : sub11 [-1, 1, 7] = true := by decide +kernel
theorem sub11_385 : sub11 [-1, 1, 8] = true := by decide +kernel
theorem sub11_386 : sub11 [-1, 1, 9] = true := by decide +kernel
theorem sub11_387 : sub11 [-1, 2, -8] = true := by decide +kernel
theorem sub11_388 : sub11 [-1, 2, -7] = true := by decide +kernel
theorem sub11_389 : sub11 [-1, 2, -6] = true := by decide +kernel
theorem sub11_390 : sub11 [-1, 2, -5] = true := by decide +kernel
theorem sub11_391 : sub11 [-1, 2, -4] = true := by decide +kernel
theorem sub11_392 : sub11 [-1, 2, -3] = true := by decide +kernel
theorem sub11_393 : sub11 [-1, 2, -2] = true := by decide +kernel
theorem sub11_394 : sub11 [-1, 2, -1] = true := by decide +kernel
theorem sub11_395 : sub11 [-1, 2, 0] = true := by decide +kernel
theorem sub11_396 : sub11 [-1, 2, 1] = true := by decide +kernel
theorem sub11_397 : sub11 [-1, 2, 2] = true := by decide +kernel
theorem sub11_398 : sub11 [-1, 2, 3] = true := by decide +kernel
theorem sub11_399 : sub11 [-1, 2, 4] = true := by decide +kernel
theorem sub11_400 : sub11 [-1, 2, 5] = true := by decide +kernel
theorem sub11_401 : sub11 [-1, 2, 6] = true := by decide +kernel
theorem sub11_402 : sub11 [-1, 2, 7] = true := by decide +kernel
theorem sub11_403 : sub11 [-1, 2, 8] = true := by decide +kernel
theorem sub11_404 : sub11 [-1, 2, 9] = true := by decide +kernel
theorem sub11_405 : sub11 [-1, 3, -7] = true := by decide +kernel
theorem sub11_406 : sub11 [-1, 3, -6] = true := by decide +kernel
theorem sub11_407 : sub11 [-1, 3, -5] = true := by decide +kernel
theorem sub11_408 : sub11 [-1, 3, -4] = true := by decide +kernel
theorem sub11_409 : sub11 [-1, 3, -3] = true := by decide +kernel
theorem sub11_410 : sub11 [-1, 3, -2] = true := by decide +kernel
theorem sub11_411 : sub11 [-1, 3, -1] = true := by decide +kernel
theorem sub11_412 : sub11 [-1, 3, 0] = true := by decide +kernel
theorem sub11_413 : sub11 [-1, 3, 1] = true := by decide +kernel
theorem sub11_414 : sub11 [-1, 3, 2] = true := by decide +kernel
theorem sub11_415 : sub11 [-1, 3, 3] = true := by decide +kernel
theorem sb11_12 : ∀ q ∈ blk11_12, sub11 q = true := by
  unfold blk11_12
  exact List.forall_mem_cons.2 ⟨sub11_384, List.forall_mem_cons.2 ⟨sub11_385, List.forall_mem_cons.2 ⟨sub11_386, List.forall_mem_cons.2 ⟨sub11_387, List.forall_mem_cons.2 ⟨sub11_388, List.forall_mem_cons.2 ⟨sub11_389, List.forall_mem_cons.2 ⟨sub11_390, List.forall_mem_cons.2 ⟨sub11_391, List.forall_mem_cons.2 ⟨sub11_392, List.forall_mem_cons.2 ⟨sub11_393, List.forall_mem_cons.2 ⟨sub11_394, List.forall_mem_cons.2 ⟨sub11_395, List.forall_mem_cons.2 ⟨sub11_396, List.forall_mem_cons.2 ⟨sub11_397, List.forall_mem_cons.2 ⟨sub11_398, List.forall_mem_cons.2 ⟨sub11_399, List.forall_mem_cons.2 ⟨sub11_400, List.forall_mem_cons.2 ⟨sub11_401, List.forall_mem_cons.2 ⟨sub11_402, List.forall_mem_cons.2 ⟨sub11_403, List.forall_mem_cons.2 ⟨sub11_404, List.forall_mem_cons.2 ⟨sub11_405, List.forall_mem_cons.2 ⟨sub11_406, List.forall_mem_cons.2 ⟨sub11_407, List.forall_mem_cons.2 ⟨sub11_408, List.forall_mem_cons.2 ⟨sub11_409, List.forall_mem_cons.2 ⟨sub11_410, List.forall_mem_cons.2 ⟨sub11_411, List.forall_mem_cons.2 ⟨sub11_412, List.forall_mem_cons.2 ⟨sub11_413, List.forall_mem_cons.2 ⟨sub11_414, List.forall_mem_cons.2 ⟨sub11_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub11_416 : sub11 [-1, 3, 4] = true := by decide +kernel
theorem sub11_417 : sub11 [-1, 3, 5] = true := by decide +kernel
theorem sub11_418 : sub11 [-1, 3, 6] = true := by decide +kernel
theorem sub11_419 : sub11 [-1, 3, 7] = true := by decide +kernel
theorem sub11_420 : sub11 [-1, 3, 8] = true := by decide +kernel
theorem sub11_421 : sub11 [-1, 3, 9] = true := by decide +kernel
theorem sub11_422 : sub11 [-1, 4, -5] = true := by decide +kernel
theorem sub11_423 : sub11 [-1, 4, -4] = true := by decide +kernel
theorem sub11_424 : sub11 [-1, 4, -3] = true := by decide +kernel
theorem sub11_425 : sub11 [-1, 4, -2] = true := by decide +kernel
theorem sub11_426 : sub11 [-1, 4, -1] = true := by decide +kernel
theorem sub11_427 : sub11 [-1, 4, 0] = true := by decide +kernel
theorem sub11_428 : sub11 [-1, 4, 1] = true := by decide +kernel
theorem sub11_429 : sub11 [-1, 4, 2] = true := by decide +kernel
theorem sub11_430 : sub11 [-1, 4, 3] = true := by decide +kernel
theorem sub11_431 : sub11 [-1, 4, 4] = true := by decide +kernel
theorem sub11_432 : sub11 [-1, 4, 5] = true := by decide +kernel
theorem sub11_433 : sub11 [-1, 4, 6] = true := by decide +kernel
theorem sub11_434 : sub11 [-1, 4, 7] = true := by decide +kernel
theorem sub11_435 : sub11 [-1, 4, 8] = true := by decide +kernel
theorem sub11_436 : sub11 [-1, 5] = true := by decide +kernel
theorem sub11_437 : sub11 [0, -6] = true := by decide +kernel
theorem sub11_438 : sub11 [0, -5] = true := by decide +kernel
theorem sub11_439 : sub11 [0, -4, -9] = true := by decide +kernel
theorem sub11_440 : sub11 [0, -4, -8] = true := by decide +kernel
theorem sub11_441 : sub11 [0, -4, -7] = true := by decide +kernel
theorem sub11_442 : sub11 [0, -4, -6] = true := by decide +kernel
theorem sub11_443 : sub11 [0, -4, -5] = true := by decide +kernel
theorem sub11_444 : sub11 [0, -4, -4] = true := by decide +kernel
theorem sub11_445 : sub11 [0, -4, -3] = true := by decide +kernel
theorem sub11_446 : sub11 [0, -4, -2] = true := by decide +kernel
theorem sub11_447 : sub11 [0, -4, -1] = true := by decide +kernel
theorem sb11_13 : ∀ q ∈ blk11_13, sub11 q = true := by
  unfold blk11_13
  exact List.forall_mem_cons.2 ⟨sub11_416, List.forall_mem_cons.2 ⟨sub11_417, List.forall_mem_cons.2 ⟨sub11_418, List.forall_mem_cons.2 ⟨sub11_419, List.forall_mem_cons.2 ⟨sub11_420, List.forall_mem_cons.2 ⟨sub11_421, List.forall_mem_cons.2 ⟨sub11_422, List.forall_mem_cons.2 ⟨sub11_423, List.forall_mem_cons.2 ⟨sub11_424, List.forall_mem_cons.2 ⟨sub11_425, List.forall_mem_cons.2 ⟨sub11_426, List.forall_mem_cons.2 ⟨sub11_427, List.forall_mem_cons.2 ⟨sub11_428, List.forall_mem_cons.2 ⟨sub11_429, List.forall_mem_cons.2 ⟨sub11_430, List.forall_mem_cons.2 ⟨sub11_431, List.forall_mem_cons.2 ⟨sub11_432, List.forall_mem_cons.2 ⟨sub11_433, List.forall_mem_cons.2 ⟨sub11_434, List.forall_mem_cons.2 ⟨sub11_435, List.forall_mem_cons.2 ⟨sub11_436, List.forall_mem_cons.2 ⟨sub11_437, List.forall_mem_cons.2 ⟨sub11_438, List.forall_mem_cons.2 ⟨sub11_439, List.forall_mem_cons.2 ⟨sub11_440, List.forall_mem_cons.2 ⟨sub11_441, List.forall_mem_cons.2 ⟨sub11_442, List.forall_mem_cons.2 ⟨sub11_443, List.forall_mem_cons.2 ⟨sub11_444, List.forall_mem_cons.2 ⟨sub11_445, List.forall_mem_cons.2 ⟨sub11_446, List.forall_mem_cons.2 ⟨sub11_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub11_448 : sub11 [0, -4, 0] = true := by decide +kernel
theorem sub11_449 : sub11 [0, -4, 1] = true := by decide +kernel
theorem sub11_450 : sub11 [0, -4, 2] = true := by decide +kernel
theorem sub11_451 : sub11 [0, -4, 3] = true := by decide +kernel
theorem sub11_452 : sub11 [0, -4, 4] = true := by decide +kernel
theorem sub11_453 : sub11 [0, -4, 5] = true := by decide +kernel
theorem sub11_454 : sub11 [0, -3, -10] = true := by decide +kernel
theorem sub11_455 : sub11 [0, -3, -9] = true := by decide +kernel
theorem sub11_456 : sub11 [0, -3, -8] = true := by decide +kernel
theorem sub11_457 : sub11 [0, -3, -7] = true := by decide +kernel
theorem sub11_458 : sub11 [0, -3, -6] = true := by decide +kernel
theorem sub11_459 : sub11 [0, -3, -5] = true := by decide +kernel
theorem sub11_460 : sub11 [0, -3, -4] = true := by decide +kernel
theorem sub11_461 : sub11 [0, -3, -3] = true := by decide +kernel
theorem sub11_462 : sub11 [0, -3, -2] = true := by decide +kernel
theorem sub11_463 : sub11 [0, -3, -1] = true := by decide +kernel
theorem sub11_464 : sub11 [0, -3, 0] = true := by decide +kernel
theorem sub11_465 : sub11 [0, -3, 1] = true := by decide +kernel
theorem sub11_466 : sub11 [0, -3, 2] = true := by decide +kernel
theorem sub11_467 : sub11 [0, -3, 3] = true := by decide +kernel
theorem sub11_468 : sub11 [0, -3, 4] = true := by decide +kernel
theorem sub11_469 : sub11 [0, -3, 5] = true := by decide +kernel
theorem sub11_470 : sub11 [0, -3, 6] = true := by decide +kernel
theorem sub11_471 : sub11 [0, -2, -10] = true := by decide +kernel
theorem sub11_472 : sub11 [0, -2, -9] = true := by decide +kernel
theorem sub11_473 : sub11 [0, -2, -8] = true := by decide +kernel
theorem sub11_474 : sub11 [0, -2, -7] = true := by decide +kernel
theorem sub11_475 : sub11 [0, -2, -6] = true := by decide +kernel
theorem sub11_476 : sub11 [0, -2, -5] = true := by decide +kernel
theorem sub11_477 : sub11 [0, -2, -4] = true := by decide +kernel
theorem sub11_478 : sub11 [0, -2, -3] = true := by decide +kernel
theorem sub11_479 : sub11 [0, -2, -2] = true := by decide +kernel
theorem sb11_14 : ∀ q ∈ blk11_14, sub11 q = true := by
  unfold blk11_14
  exact List.forall_mem_cons.2 ⟨sub11_448, List.forall_mem_cons.2 ⟨sub11_449, List.forall_mem_cons.2 ⟨sub11_450, List.forall_mem_cons.2 ⟨sub11_451, List.forall_mem_cons.2 ⟨sub11_452, List.forall_mem_cons.2 ⟨sub11_453, List.forall_mem_cons.2 ⟨sub11_454, List.forall_mem_cons.2 ⟨sub11_455, List.forall_mem_cons.2 ⟨sub11_456, List.forall_mem_cons.2 ⟨sub11_457, List.forall_mem_cons.2 ⟨sub11_458, List.forall_mem_cons.2 ⟨sub11_459, List.forall_mem_cons.2 ⟨sub11_460, List.forall_mem_cons.2 ⟨sub11_461, List.forall_mem_cons.2 ⟨sub11_462, List.forall_mem_cons.2 ⟨sub11_463, List.forall_mem_cons.2 ⟨sub11_464, List.forall_mem_cons.2 ⟨sub11_465, List.forall_mem_cons.2 ⟨sub11_466, List.forall_mem_cons.2 ⟨sub11_467, List.forall_mem_cons.2 ⟨sub11_468, List.forall_mem_cons.2 ⟨sub11_469, List.forall_mem_cons.2 ⟨sub11_470, List.forall_mem_cons.2 ⟨sub11_471, List.forall_mem_cons.2 ⟨sub11_472, List.forall_mem_cons.2 ⟨sub11_473, List.forall_mem_cons.2 ⟨sub11_474, List.forall_mem_cons.2 ⟨sub11_475, List.forall_mem_cons.2 ⟨sub11_476, List.forall_mem_cons.2 ⟨sub11_477, List.forall_mem_cons.2 ⟨sub11_478, List.forall_mem_cons.2 ⟨sub11_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C074
