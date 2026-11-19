import ReflectZphi.Data.Cert5.C131.Base

namespace ReflectZphi.Data.Cert5.C131

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd10_0_64 : subd10_0 [-5, 1, 5] = true := by decide +kernel
theorem subd10_0_65 : subd10_0 [-5, 2, -8] = true := by decide +kernel
theorem subd10_0_66 : subd10_0 [-5, 2, -7] = true := by decide +kernel
theorem subd10_0_67 : subd10_0 [-5, 2, -6] = true := by decide +kernel
theorem subd10_0_68 : subd10_0 [-5, 2, -5] = true := by decide +kernel
theorem subd10_0_69 : subd10_0 [-5, 2, -4] = true := by decide +kernel
theorem subd10_0_70 : subd10_0 [-5, 2, -3] = true := by decide +kernel
theorem subd10_0_71 : subd10_0 [-5, 2, -2] = true := by decide +kernel
theorem subd10_0_72 : subd10_0 [-5, 2, -1] = true := by decide +kernel
theorem subd10_0_73 : subd10_0 [-5, 2, 0] = true := by decide +kernel
theorem subd10_0_74 : subd10_0 [-5, 2, 1] = true := by decide +kernel
theorem subd10_0_75 : subd10_0 [-5, 2, 2] = true := by decide +kernel
theorem subd10_0_76 : subd10_0 [-5, 2, 3] = true := by decide +kernel
theorem subd10_0_77 : subd10_0 [-5, 2, 4] = true := by decide +kernel
theorem subd10_0_78 : subd10_0 [-5, 3] = true := by decide +kernel
theorem subd10_0_79 : subd10_0 [-5, 4] = true := by decide +kernel
theorem subd10_0_80 : subd10_0 [-5, 5] = true := by decide +kernel
theorem subd10_0_81 : subd10_0 [-5, 6] = true := by decide +kernel
theorem subd10_0_82 : subd10_0 [-4, -7] = true := by decide +kernel
theorem subd10_0_83 : subd10_0 [-4, -6] = true := by decide +kernel
theorem subd10_0_84 : subd10_0 [-4, -5] = true := by decide +kernel
theorem subd10_0_85 : subd10_0 [-4, -4] = true := by decide +kernel
theorem subd10_0_86 : subd10_0 [-4, -3, -7] = true := by decide +kernel
theorem subd10_0_87 : subd10_0 [-4, -3, -6] = true := by decide +kernel
theorem subd10_0_88 : subd10_0 [-4, -3, -5] = true := by decide +kernel
theorem subd10_0_89 : subd10_0 [-4, -3, -4] = true := by decide +kernel
theorem subd10_0_90 : subd10_0 [-4, -3, -3] = true := by decide +kernel
theorem subd10_0_91 : subd10_0 [-4, -3, -2] = true := by decide +kernel
theorem subd10_0_92 : subd10_0 [-4, -3, -1] = true := by decide +kernel
theorem subd10_0_93 : subd10_0 [-4, -3, 0] = true := by decide +kernel
theorem subd10_0_94 : subd10_0 [-4, -3, 1] = true := by decide +kernel
theorem subd10_0_95 : subd10_0 [-4, -3, 2] = true := by decide +kernel
theorem sbd10_0_2 : ∀ q ∈ blkd10_0_2, subd10_0 q = true := by
  unfold blkd10_0_2
  exact List.forall_mem_cons.2 ⟨subd10_0_64, List.forall_mem_cons.2 ⟨subd10_0_65, List.forall_mem_cons.2 ⟨subd10_0_66, List.forall_mem_cons.2 ⟨subd10_0_67, List.forall_mem_cons.2 ⟨subd10_0_68, List.forall_mem_cons.2 ⟨subd10_0_69, List.forall_mem_cons.2 ⟨subd10_0_70, List.forall_mem_cons.2 ⟨subd10_0_71, List.forall_mem_cons.2 ⟨subd10_0_72, List.forall_mem_cons.2 ⟨subd10_0_73, List.forall_mem_cons.2 ⟨subd10_0_74, List.forall_mem_cons.2 ⟨subd10_0_75, List.forall_mem_cons.2 ⟨subd10_0_76, List.forall_mem_cons.2 ⟨subd10_0_77, List.forall_mem_cons.2 ⟨subd10_0_78, List.forall_mem_cons.2 ⟨subd10_0_79, List.forall_mem_cons.2 ⟨subd10_0_80, List.forall_mem_cons.2 ⟨subd10_0_81, List.forall_mem_cons.2 ⟨subd10_0_82, List.forall_mem_cons.2 ⟨subd10_0_83, List.forall_mem_cons.2 ⟨subd10_0_84, List.forall_mem_cons.2 ⟨subd10_0_85, List.forall_mem_cons.2 ⟨subd10_0_86, List.forall_mem_cons.2 ⟨subd10_0_87, List.forall_mem_cons.2 ⟨subd10_0_88, List.forall_mem_cons.2 ⟨subd10_0_89, List.forall_mem_cons.2 ⟨subd10_0_90, List.forall_mem_cons.2 ⟨subd10_0_91, List.forall_mem_cons.2 ⟨subd10_0_92, List.forall_mem_cons.2 ⟨subd10_0_93, List.forall_mem_cons.2 ⟨subd10_0_94, List.forall_mem_cons.2 ⟨subd10_0_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_96 : subd10_0 [-4, -3, 3] = true := by decide +kernel
theorem subd10_0_97 : subd10_0 [-4, -3, 4] = true := by decide +kernel
theorem subd10_0_98 : subd10_0 [-4, -3, 5] = true := by decide +kernel
theorem subd10_0_99 : subd10_0 [-4, -3, 6] = true := by decide +kernel
theorem subd10_0_100 : subd10_0 [-4, -2, -8] = true := by decide +kernel
theorem subd10_0_101 : subd10_0 [-4, -2, -7] = true := by decide +kernel
theorem subd10_0_102 : subd10_0 [-4, -2, -6] = true := by decide +kernel
theorem subd10_0_103 : subd10_0 [-4, -2, -5] = true := by decide +kernel
theorem subd10_0_104 : subd10_0 [-4, -2, -4] = true := by decide +kernel
theorem subd10_0_105 : subd10_0 [-4, -2, -3] = true := by decide +kernel
theorem subd10_0_106 : subd10_0 [-4, -2, -2] = true := by decide +kernel
theorem subd10_0_107 : subd10_0 [-4, -2, -1] = true := by decide +kernel
theorem subd10_0_108 : subd10_0 [-4, -2, 0] = true := by decide +kernel
theorem subd10_0_109 : subd10_0 [-4, -2, 1] = true := by decide +kernel
theorem subd10_0_110 : subd10_0 [-4, -2, 2] = true := by decide +kernel
theorem subd10_0_111 : subd10_0 [-4, -2, 3] = true := by decide +kernel
theorem subd10_0_112 : subd10_0 [-4, -2, 4] = true := by decide +kernel
theorem subd10_0_113 : subd10_0 [-4, -2, 5] = true := by decide +kernel
theorem subd10_0_114 : subd10_0 [-4, -2, 6] = true := by decide +kernel
theorem subd10_0_115 : subd10_0 [-4, -1, -9] = true := by decide +kernel
theorem subd10_0_116 : subd10_0 [-4, -1, -8] = true := by decide +kernel
theorem subd10_0_117 : subd10_0 [-4, -1, -7] = true := by decide +kernel
theorem subd10_0_118 : subd10_0 [-4, -1, -6] = true := by decide +kernel
theorem subd10_0_119 : subd10_0 [-4, -1, -5] = true := by decide +kernel
theorem subd10_0_120 : subd10_0 [-4, -1, -4] = true := by decide +kernel
theorem subd10_0_121 : subd10_0 [-4, -1, -3] = true := by decide +kernel
theorem subd10_0_122 : subd10_0 [-4, -1, -2] = true := by decide +kernel
theorem subd10_0_123 : subd10_0 [-4, -1, -1] = true := by decide +kernel
theorem subd10_0_124 : subd10_0 [-4, -1, 0] = true := by decide +kernel
theorem subd10_0_125 : subd10_0 [-4, -1, 1] = true := by decide +kernel
theorem subd10_0_126 : subd10_0 [-4, -1, 2] = true := by decide +kernel
theorem subd10_0_127 : subd10_0 [-4, -1, 3] = true := by decide +kernel
theorem sbd10_0_3 : ∀ q ∈ blkd10_0_3, subd10_0 q = true := by
  unfold blkd10_0_3
  exact List.forall_mem_cons.2 ⟨subd10_0_96, List.forall_mem_cons.2 ⟨subd10_0_97, List.forall_mem_cons.2 ⟨subd10_0_98, List.forall_mem_cons.2 ⟨subd10_0_99, List.forall_mem_cons.2 ⟨subd10_0_100, List.forall_mem_cons.2 ⟨subd10_0_101, List.forall_mem_cons.2 ⟨subd10_0_102, List.forall_mem_cons.2 ⟨subd10_0_103, List.forall_mem_cons.2 ⟨subd10_0_104, List.forall_mem_cons.2 ⟨subd10_0_105, List.forall_mem_cons.2 ⟨subd10_0_106, List.forall_mem_cons.2 ⟨subd10_0_107, List.forall_mem_cons.2 ⟨subd10_0_108, List.forall_mem_cons.2 ⟨subd10_0_109, List.forall_mem_cons.2 ⟨subd10_0_110, List.forall_mem_cons.2 ⟨subd10_0_111, List.forall_mem_cons.2 ⟨subd10_0_112, List.forall_mem_cons.2 ⟨subd10_0_113, List.forall_mem_cons.2 ⟨subd10_0_114, List.forall_mem_cons.2 ⟨subd10_0_115, List.forall_mem_cons.2 ⟨subd10_0_116, List.forall_mem_cons.2 ⟨subd10_0_117, List.forall_mem_cons.2 ⟨subd10_0_118, List.forall_mem_cons.2 ⟨subd10_0_119, List.forall_mem_cons.2 ⟨subd10_0_120, List.forall_mem_cons.2 ⟨subd10_0_121, List.forall_mem_cons.2 ⟨subd10_0_122, List.forall_mem_cons.2 ⟨subd10_0_123, List.forall_mem_cons.2 ⟨subd10_0_124, List.forall_mem_cons.2 ⟨subd10_0_125, List.forall_mem_cons.2 ⟨subd10_0_126, List.forall_mem_cons.2 ⟨subd10_0_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_128 : subd10_0 [-4, -1, 4] = true := by decide +kernel
theorem subd10_0_129 : subd10_0 [-4, -1, 5] = true := by decide +kernel
theorem subd10_0_130 : subd10_0 [-4, -1, 6] = true := by decide +kernel
theorem subd10_0_131 : subd10_0 [-4, 0, -9] = true := by decide +kernel
theorem subd10_0_132 : subd10_0 [-4, 0, -8] = true := by decide +kernel
theorem subd10_0_133 : subd10_0 [-4, 0, -7] = true := by decide +kernel
theorem subd10_0_134 : subd10_0 [-4, 0, -6] = true := by decide +kernel
theorem subd10_0_135 : subd10_0 [-4, 0, -5] = true := by decide +kernel
theorem subd10_0_136 : subd10_0 [-4, 0, -4] = true := by decide +kernel
theorem subd10_0_137 : subd10_0 [-4, 0, -3] = true := by decide +kernel
theorem subd10_0_138 : subd10_0 [-4, 0, -2] = true := by decide +kernel
theorem subd10_0_139 : subd10_0 [-4, 0, -1] = true := by decide +kernel
theorem subd10_0_140 : subd10_0 [-4, 0, 0] = true := by decide +kernel
theorem subd10_0_141 : subd10_0 [-4, 0, 1] = true := by decide +kernel
theorem subd10_0_142 : subd10_0 [-4, 0, 2] = true := by decide +kernel
theorem subd10_0_143 : subd10_0 [-4, 0, 3] = true := by decide +kernel
theorem subd10_0_144 : subd10_0 [-4, 0, 4] = true := by decide +kernel
theorem subd10_0_145 : subd10_0 [-4, 0, 5] = true := by decide +kernel
theorem subd10_0_146 : subd10_0 [-4, 0, 6] = true := by decide +kernel
theorem subd10_0_147 : subd10_0 [-4, 1, -9] = true := by decide +kernel
theorem subd10_0_148 : subd10_0 [-4, 1, -8] = true := by decide +kernel
theorem subd10_0_149 : subd10_0 [-4, 1, -7] = true := by decide +kernel
theorem subd10_0_150 : subd10_0 [-4, 1, -6] = true := by decide +kernel
theorem subd10_0_151 : subd10_0 [-4, 1, -5] = true := by decide +kernel
theorem subd10_0_152 : subd10_0 [-4, 1, -4] = true := by decide +kernel
theorem subd10_0_153 : subd10_0 [-4, 1, -3] = true := by decide +kernel
theorem subd10_0_154 : subd10_0 [-4, 1, -2] = true := by decide +kernel
theorem subd10_0_155 : subd10_0 [-4, 1, -1] = true := by decide +kernel
theorem subd10_0_156 : subd10_0 [-4, 1, 0] = true := by decide +kernel
theorem subd10_0_157 : subd10_0 [-4, 1, 1] = true := by decide +kernel
theorem subd10_0_158 : subd10_0 [-4, 1, 2] = true := by decide +kernel
theorem subd10_0_159 : subd10_0 [-4, 1, 3] = true := by decide +kernel
theorem sbd10_0_4 : ∀ q ∈ blkd10_0_4, subd10_0 q = true := by
  unfold blkd10_0_4
  exact List.forall_mem_cons.2 ⟨subd10_0_128, List.forall_mem_cons.2 ⟨subd10_0_129, List.forall_mem_cons.2 ⟨subd10_0_130, List.forall_mem_cons.2 ⟨subd10_0_131, List.forall_mem_cons.2 ⟨subd10_0_132, List.forall_mem_cons.2 ⟨subd10_0_133, List.forall_mem_cons.2 ⟨subd10_0_134, List.forall_mem_cons.2 ⟨subd10_0_135, List.forall_mem_cons.2 ⟨subd10_0_136, List.forall_mem_cons.2 ⟨subd10_0_137, List.forall_mem_cons.2 ⟨subd10_0_138, List.forall_mem_cons.2 ⟨subd10_0_139, List.forall_mem_cons.2 ⟨subd10_0_140, List.forall_mem_cons.2 ⟨subd10_0_141, List.forall_mem_cons.2 ⟨subd10_0_142, List.forall_mem_cons.2 ⟨subd10_0_143, List.forall_mem_cons.2 ⟨subd10_0_144, List.forall_mem_cons.2 ⟨subd10_0_145, List.forall_mem_cons.2 ⟨subd10_0_146, List.forall_mem_cons.2 ⟨subd10_0_147, List.forall_mem_cons.2 ⟨subd10_0_148, List.forall_mem_cons.2 ⟨subd10_0_149, List.forall_mem_cons.2 ⟨subd10_0_150, List.forall_mem_cons.2 ⟨subd10_0_151, List.forall_mem_cons.2 ⟨subd10_0_152, List.forall_mem_cons.2 ⟨subd10_0_153, List.forall_mem_cons.2 ⟨subd10_0_154, List.forall_mem_cons.2 ⟨subd10_0_155, List.forall_mem_cons.2 ⟨subd10_0_156, List.forall_mem_cons.2 ⟨subd10_0_157, List.forall_mem_cons.2 ⟨subd10_0_158, List.forall_mem_cons.2 ⟨subd10_0_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_160 : subd10_0 [-4, 1, 4] = true := by decide +kernel
theorem subd10_0_161 : subd10_0 [-4, 1, 5] = true := by decide +kernel
theorem subd10_0_162 : subd10_0 [-4, 1, 6] = true := by decide +kernel
theorem subd10_0_163 : subd10_0 [-4, 2, -9] = true := by decide +kernel
theorem subd10_0_164 : subd10_0 [-4, 2, -8] = true := by decide +kernel
theorem subd10_0_165 : subd10_0 [-4, 2, -7] = true := by decide +kernel
theorem subd10_0_166 : subd10_0 [-4, 2, -6] = true := by decide +kernel
theorem subd10_0_167 : subd10_0 [-4, 2, -5] = true := by decide +kernel
theorem subd10_0_168 : subd10_0 [-4, 2, -4] = true := by decide +kernel
theorem subd10_0_169 : subd10_0 [-4, 2, -3] = true := by decide +kernel
theorem subd10_0_170 : subd10_0 [-4, 2, -2] = true := by decide +kernel
theorem subd10_0_171 : subd10_0 [-4, 2, -1] = true := by decide +kernel
theorem subd10_0_172 : subd10_0 [-4, 2, 0] = true := by decide +kernel
theorem subd10_0_173 : subd10_0 [-4, 2, 1] = true := by decide +kernel
theorem subd10_0_174 : subd10_0 [-4, 2, 2] = true := by decide +kernel
theorem subd10_0_175 : subd10_0 [-4, 2, 3] = true := by decide +kernel
theorem subd10_0_176 : subd10_0 [-4, 2, 4] = true := by decide +kernel
theorem subd10_0_177 : subd10_0 [-4, 2, 5] = true := by decide +kernel
theorem subd10_0_178 : subd10_0 [-4, 3, -9] = true := by decide +kernel
theorem subd10_0_179 : subd10_0 [-4, 3, -8] = true := by decide +kernel
theorem subd10_0_180 : subd10_0 [-4, 3, -7] = true := by decide +kernel
theorem subd10_0_181 : subd10_0 [-4, 3, -6] = true := by decide +kernel
theorem subd10_0_182 : subd10_0 [-4, 3, -5] = true := by decide +kernel
theorem subd10_0_183 : subd10_0 [-4, 3, -4] = true := by decide +kernel
theorem subd10_0_184 : subd10_0 [-4, 3, -3] = true := by decide +kernel
theorem subd10_0_185 : subd10_0 [-4, 3, -2] = true := by decide +kernel
theorem subd10_0_186 : subd10_0 [-4, 3, -1] = true := by decide +kernel
theorem subd10_0_187 : subd10_0 [-4, 3, 0] = true := by decide +kernel
theorem subd10_0_188 : subd10_0 [-4, 3, 1] = true := by decide +kernel
theorem subd10_0_189 : subd10_0 [-4, 3, 2] = true := by decide +kernel
theorem subd10_0_190 : subd10_0 [-4, 3, 3] = true := by decide +kernel
theorem subd10_0_191 : subd10_0 [-4, 3, 4] = true := by decide +kernel
theorem sbd10_0_5 : ∀ q ∈ blkd10_0_5, subd10_0 q = true := by
  unfold blkd10_0_5
  exact List.forall_mem_cons.2 ⟨subd10_0_160, List.forall_mem_cons.2 ⟨subd10_0_161, List.forall_mem_cons.2 ⟨subd10_0_162, List.forall_mem_cons.2 ⟨subd10_0_163, List.forall_mem_cons.2 ⟨subd10_0_164, List.forall_mem_cons.2 ⟨subd10_0_165, List.forall_mem_cons.2 ⟨subd10_0_166, List.forall_mem_cons.2 ⟨subd10_0_167, List.forall_mem_cons.2 ⟨subd10_0_168, List.forall_mem_cons.2 ⟨subd10_0_169, List.forall_mem_cons.2 ⟨subd10_0_170, List.forall_mem_cons.2 ⟨subd10_0_171, List.forall_mem_cons.2 ⟨subd10_0_172, List.forall_mem_cons.2 ⟨subd10_0_173, List.forall_mem_cons.2 ⟨subd10_0_174, List.forall_mem_cons.2 ⟨subd10_0_175, List.forall_mem_cons.2 ⟨subd10_0_176, List.forall_mem_cons.2 ⟨subd10_0_177, List.forall_mem_cons.2 ⟨subd10_0_178, List.forall_mem_cons.2 ⟨subd10_0_179, List.forall_mem_cons.2 ⟨subd10_0_180, List.forall_mem_cons.2 ⟨subd10_0_181, List.forall_mem_cons.2 ⟨subd10_0_182, List.forall_mem_cons.2 ⟨subd10_0_183, List.forall_mem_cons.2 ⟨subd10_0_184, List.forall_mem_cons.2 ⟨subd10_0_185, List.forall_mem_cons.2 ⟨subd10_0_186, List.forall_mem_cons.2 ⟨subd10_0_187, List.forall_mem_cons.2 ⟨subd10_0_188, List.forall_mem_cons.2 ⟨subd10_0_189, List.forall_mem_cons.2 ⟨subd10_0_190, List.forall_mem_cons.2 ⟨subd10_0_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_192 : subd10_0 [-4, 3, 5] = true := by decide +kernel
theorem subd10_0_193 : subd10_0 [-4, 4, -8] = true := by decide +kernel
theorem subd10_0_194 : subd10_0 [-4, 4, -7] = true := by decide +kernel
theorem subd10_0_195 : subd10_0 [-4, 4, -6] = true := by decide +kernel
theorem subd10_0_196 : subd10_0 [-4, 4, -5] = true := by decide +kernel
theorem subd10_0_197 : subd10_0 [-4, 4, -4] = true := by decide +kernel
theorem subd10_0_198 : subd10_0 [-4, 4, -3] = true := by decide +kernel
theorem subd10_0_199 : subd10_0 [-4, 4, -2] = true := by decide +kernel
theorem subd10_0_200 : subd10_0 [-4, 4, -1] = true := by decide +kernel
theorem subd10_0_201 : subd10_0 [-4, 4, 0] = true := by decide +kernel
theorem subd10_0_202 : subd10_0 [-4, 4, 1] = true := by decide +kernel
theorem subd10_0_203 : subd10_0 [-4, 4, 2] = true := by decide +kernel
theorem subd10_0_204 : subd10_0 [-4, 4, 3] = true := by decide +kernel
theorem subd10_0_205 : subd10_0 [-4, 4, 4] = true := by decide +kernel
theorem subd10_0_206 : subd10_0 [-4, 5] = true := by decide +kernel
theorem subd10_0_207 : subd10_0 [-4, 6] = true := by decide +kernel
theorem subd10_0_208 : subd10_0 [-3, -7] = true := by decide +kernel
theorem subd10_0_209 : subd10_0 [-3, -6] = true := by decide +kernel
theorem subd10_0_210 : subd10_0 [-3, -5] = true := by decide +kernel
theorem subd10_0_211 : subd10_0 [-3, -4, -7] = true := by decide +kernel
theorem subd10_0_212 : subd10_0 [-3, -4, -6] = true := by decide +kernel
theorem subd10_0_213 : subd10_0 [-3, -4, -5] = true := by decide +kernel
theorem subd10_0_214 : subd10_0 [-3, -4, -4] = true := by decide +kernel
theorem subd10_0_215 : subd10_0 [-3, -4, -3] = true := by decide +kernel
theorem subd10_0_216 : subd10_0 [-3, -4, -2] = true := by decide +kernel
theorem subd10_0_217 : subd10_0 [-3, -4, -1] = true := by decide +kernel
theorem subd10_0_218 : subd10_0 [-3, -4, 0] = true := by decide +kernel
theorem subd10_0_219 : subd10_0 [-3, -4, 1] = true := by decide +kernel
theorem subd10_0_220 : subd10_0 [-3, -4, 2] = true := by decide +kernel
theorem subd10_0_221 : subd10_0 [-3, -4, 3] = true := by decide +kernel
theorem subd10_0_222 : subd10_0 [-3, -4, 4] = true := by decide +kernel
theorem subd10_0_223 : subd10_0 [-3, -4, 5] = true := by decide +kernel
theorem sbd10_0_6 : ∀ q ∈ blkd10_0_6, subd10_0 q = true := by
  unfold blkd10_0_6
  exact List.forall_mem_cons.2 ⟨subd10_0_192, List.forall_mem_cons.2 ⟨subd10_0_193, List.forall_mem_cons.2 ⟨subd10_0_194, List.forall_mem_cons.2 ⟨subd10_0_195, List.forall_mem_cons.2 ⟨subd10_0_196, List.forall_mem_cons.2 ⟨subd10_0_197, List.forall_mem_cons.2 ⟨subd10_0_198, List.forall_mem_cons.2 ⟨subd10_0_199, List.forall_mem_cons.2 ⟨subd10_0_200, List.forall_mem_cons.2 ⟨subd10_0_201, List.forall_mem_cons.2 ⟨subd10_0_202, List.forall_mem_cons.2 ⟨subd10_0_203, List.forall_mem_cons.2 ⟨subd10_0_204, List.forall_mem_cons.2 ⟨subd10_0_205, List.forall_mem_cons.2 ⟨subd10_0_206, List.forall_mem_cons.2 ⟨subd10_0_207, List.forall_mem_cons.2 ⟨subd10_0_208, List.forall_mem_cons.2 ⟨subd10_0_209, List.forall_mem_cons.2 ⟨subd10_0_210, List.forall_mem_cons.2 ⟨subd10_0_211, List.forall_mem_cons.2 ⟨subd10_0_212, List.forall_mem_cons.2 ⟨subd10_0_213, List.forall_mem_cons.2 ⟨subd10_0_214, List.forall_mem_cons.2 ⟨subd10_0_215, List.forall_mem_cons.2 ⟨subd10_0_216, List.forall_mem_cons.2 ⟨subd10_0_217, List.forall_mem_cons.2 ⟨subd10_0_218, List.forall_mem_cons.2 ⟨subd10_0_219, List.forall_mem_cons.2 ⟨subd10_0_220, List.forall_mem_cons.2 ⟨subd10_0_221, List.forall_mem_cons.2 ⟨subd10_0_222, List.forall_mem_cons.2 ⟨subd10_0_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_224 : subd10_0 [-3, -4, 6] = true := by decide +kernel
theorem subd10_0_225 : subd10_0 [-3, -3, -8] = true := by decide +kernel
theorem subd10_0_226 : subd10_0 [-3, -3, -7] = true := by decide +kernel
theorem subd10_0_227 : subd10_0 [-3, -3, -6] = true := by decide +kernel
theorem subd10_0_228 : subd10_0 [-3, -3, -5] = true := by decide +kernel
theorem subd10_0_229 : subd10_0 [-3, -3, -4] = true := by decide +kernel
theorem subd10_0_230 : subd10_0 [-3, -3, -3] = true := by decide +kernel
theorem subd10_0_231 : subd10_0 [-3, -3, -2] = true := by decide +kernel
theorem subd10_0_232 : subd10_0 [-3, -3, -1] = true := by decide +kernel
theorem subd10_0_233 : subd10_0 [-3, -3, 0] = true := by decide +kernel
theorem subd10_0_234 : subd10_0 [-3, -3, 1] = true := by decide +kernel
theorem subd10_0_235 : subd10_0 [-3, -3, 2] = true := by decide +kernel
theorem subd10_0_236 : subd10_0 [-3, -3, 3] = true := by decide +kernel
theorem subd10_0_237 : subd10_0 [-3, -3, 4] = true := by decide +kernel
theorem subd10_0_238 : subd10_0 [-3, -3, 5] = true := by decide +kernel
theorem subd10_0_239 : subd10_0 [-3, -3, 6] = true := by decide +kernel
theorem subd10_0_240 : subd10_0 [-3, -3, 7] = true := by decide +kernel
theorem subd10_0_241 : subd10_0 [-3, -2, -8] = true := by decide +kernel
theorem subd10_0_242 : subd10_0 [-3, -2, -7] = true := by decide +kernel
theorem subd10_0_243 : subd10_0 [-3, -2, -6] = true := by decide +kernel
theorem subd10_0_244 : subd10_0 [-3, -2, -5] = true := by decide +kernel
theorem subd10_0_245 : subd10_0 [-3, -2, -4] = true := by decide +kernel
theorem subd10_0_246 : subd10_0 [-3, -2, -3] = true := by decide +kernel
theorem subd10_0_247 : subd10_0 [-3, -2, -2] = true := by decide +kernel
theorem subd10_0_248 : subd10_0 [-3, -2, -1] = true := by decide +kernel
theorem subd10_0_249 : subd10_0 [-3, -2, 0] = true := by decide +kernel
theorem subd10_0_250 : subd10_0 [-3, -2, 1] = true := by decide +kernel
theorem subd10_0_251 : subd10_0 [-3, -2, 2] = true := by decide +kernel
theorem subd10_0_252 : subd10_0 [-3, -2, 3] = true := by decide +kernel
theorem subd10_0_253 : subd10_0 [-3, -2, 4] = true := by decide +kernel
theorem subd10_0_254 : subd10_0 [-3, -2, 5] = true := by decide +kernel
theorem subd10_0_255 : subd10_0 [-3, -2, 6] = true := by decide +kernel
theorem sbd10_0_7 : ∀ q ∈ blkd10_0_7, subd10_0 q = true := by
  unfold blkd10_0_7
  exact List.forall_mem_cons.2 ⟨subd10_0_224, List.forall_mem_cons.2 ⟨subd10_0_225, List.forall_mem_cons.2 ⟨subd10_0_226, List.forall_mem_cons.2 ⟨subd10_0_227, List.forall_mem_cons.2 ⟨subd10_0_228, List.forall_mem_cons.2 ⟨subd10_0_229, List.forall_mem_cons.2 ⟨subd10_0_230, List.forall_mem_cons.2 ⟨subd10_0_231, List.forall_mem_cons.2 ⟨subd10_0_232, List.forall_mem_cons.2 ⟨subd10_0_233, List.forall_mem_cons.2 ⟨subd10_0_234, List.forall_mem_cons.2 ⟨subd10_0_235, List.forall_mem_cons.2 ⟨subd10_0_236, List.forall_mem_cons.2 ⟨subd10_0_237, List.forall_mem_cons.2 ⟨subd10_0_238, List.forall_mem_cons.2 ⟨subd10_0_239, List.forall_mem_cons.2 ⟨subd10_0_240, List.forall_mem_cons.2 ⟨subd10_0_241, List.forall_mem_cons.2 ⟨subd10_0_242, List.forall_mem_cons.2 ⟨subd10_0_243, List.forall_mem_cons.2 ⟨subd10_0_244, List.forall_mem_cons.2 ⟨subd10_0_245, List.forall_mem_cons.2 ⟨subd10_0_246, List.forall_mem_cons.2 ⟨subd10_0_247, List.forall_mem_cons.2 ⟨subd10_0_248, List.forall_mem_cons.2 ⟨subd10_0_249, List.forall_mem_cons.2 ⟨subd10_0_250, List.forall_mem_cons.2 ⟨subd10_0_251, List.forall_mem_cons.2 ⟨subd10_0_252, List.forall_mem_cons.2 ⟨subd10_0_253, List.forall_mem_cons.2 ⟨subd10_0_254, List.forall_mem_cons.2 ⟨subd10_0_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_256 : subd10_0 [-3, -2, 7] = true := by decide +kernel
theorem subd10_0_257 : subd10_0 [-3, -1, -9] = true := by decide +kernel
theorem subd10_0_258 : subd10_0 [-3, -1, -8] = true := by decide +kernel
theorem subd10_0_259 : subd10_0 [-3, -1, -7] = true := by decide +kernel
theorem subd10_0_260 : subd10_0 [-3, -1, -6] = true := by decide +kernel
theorem subd10_0_261 : subd10_0 [-3, -1, -5] = true := by decide +kernel
theorem subd10_0_262 : subd10_0 [-3, -1, -4] = true := by decide +kernel
theorem subd10_0_263 : subd10_0 [-3, -1, -3] = true := by decide +kernel
theorem subd10_0_264 : subd10_0 [-3, -1, -2] = true := by decide +kernel
theorem subd10_0_265 : subd10_0 [-3, -1, -1] = true := by decide +kernel
theorem subd10_0_266 : subd10_0 [-3, -1, 0] = true := by decide +kernel
theorem subd10_0_267 : subd10_0 [-3, -1, 1] = true := by decide +kernel
theorem subd10_0_268 : subd10_0 [-3, -1, 2] = true := by decide +kernel
theorem subd10_0_269 : subd10_0 [-3, -1, 3] = true := by decide +kernel
theorem subd10_0_270 : subd10_0 [-3, -1, 4] = true := by decide +kernel
theorem subd10_0_271 : subd10_0 [-3, -1, 5] = true := by decide +kernel
theorem subd10_0_272 : subd10_0 [-3, -1, 6] = true := by decide +kernel
theorem subd10_0_273 : subd10_0 [-3, -1, 7] = true := by decide +kernel
theorem subd10_0_274 : subd10_0 [-3, 0, -9] = true := by decide +kernel
theorem subd10_0_275 : subd10_0 [-3, 0, -8] = true := by decide +kernel
theorem subd10_0_276 : subd10_0 [-3, 0, -7] = true := by decide +kernel
theorem subd10_0_277 : subd10_0 [-3, 0, -6] = true := by decide +kernel
theorem subd10_0_278 : subd10_0 [-3, 0, -5] = true := by decide +kernel
theorem subd10_0_279 : subd10_0 [-3, 0, -4] = true := by decide +kernel
theorem subd10_0_280 : subd10_0 [-3, 0, -3] = true := by decide +kernel
theorem subd10_0_281 : subd10_0 [-3, 0, -2] = true := by decide +kernel
theorem subd10_0_282 : subd10_0 [-3, 0, -1] = true := by decide +kernel
theorem subd10_0_283 : subd10_0 [-3, 0, 0] = true := by decide +kernel
theorem subd10_0_284 : subd10_0 [-3, 0, 1] = true := by decide +kernel
theorem subd10_0_285 : subd10_0 [-3, 0, 2] = true := by decide +kernel
theorem subd10_0_286 : subd10_0 [-3, 0, 3] = true := by decide +kernel
theorem subd10_0_287 : subd10_0 [-3, 0, 4] = true := by decide +kernel
theorem sbd10_0_8 : ∀ q ∈ blkd10_0_8, subd10_0 q = true := by
  unfold blkd10_0_8
  exact List.forall_mem_cons.2 ⟨subd10_0_256, List.forall_mem_cons.2 ⟨subd10_0_257, List.forall_mem_cons.2 ⟨subd10_0_258, List.forall_mem_cons.2 ⟨subd10_0_259, List.forall_mem_cons.2 ⟨subd10_0_260, List.forall_mem_cons.2 ⟨subd10_0_261, List.forall_mem_cons.2 ⟨subd10_0_262, List.forall_mem_cons.2 ⟨subd10_0_263, List.forall_mem_cons.2 ⟨subd10_0_264, List.forall_mem_cons.2 ⟨subd10_0_265, List.forall_mem_cons.2 ⟨subd10_0_266, List.forall_mem_cons.2 ⟨subd10_0_267, List.forall_mem_cons.2 ⟨subd10_0_268, List.forall_mem_cons.2 ⟨subd10_0_269, List.forall_mem_cons.2 ⟨subd10_0_270, List.forall_mem_cons.2 ⟨subd10_0_271, List.forall_mem_cons.2 ⟨subd10_0_272, List.forall_mem_cons.2 ⟨subd10_0_273, List.forall_mem_cons.2 ⟨subd10_0_274, List.forall_mem_cons.2 ⟨subd10_0_275, List.forall_mem_cons.2 ⟨subd10_0_276, List.forall_mem_cons.2 ⟨subd10_0_277, List.forall_mem_cons.2 ⟨subd10_0_278, List.forall_mem_cons.2 ⟨subd10_0_279, List.forall_mem_cons.2 ⟨subd10_0_280, List.forall_mem_cons.2 ⟨subd10_0_281, List.forall_mem_cons.2 ⟨subd10_0_282, List.forall_mem_cons.2 ⟨subd10_0_283, List.forall_mem_cons.2 ⟨subd10_0_284, List.forall_mem_cons.2 ⟨subd10_0_285, List.forall_mem_cons.2 ⟨subd10_0_286, List.forall_mem_cons.2 ⟨subd10_0_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_288 : subd10_0 [-3, 0, 5] = true := by decide +kernel
theorem subd10_0_289 : subd10_0 [-3, 0, 6] = true := by decide +kernel
theorem subd10_0_290 : subd10_0 [-3, 0, 7] = true := by decide +kernel
theorem subd10_0_291 : subd10_0 [-3, 1, -9] = true := by decide +kernel
theorem subd10_0_292 : subd10_0 [-3, 1, -8] = true := by decide +kernel
theorem subd10_0_293 : subd10_0 [-3, 1, -7] = true := by decide +kernel
theorem subd10_0_294 : subd10_0 [-3, 1, -6] = true := by decide +kernel
theorem subd10_0_295 : subd10_0 [-3, 1, -5] = true := by decide +kernel
theorem subd10_0_296 : subd10_0 [-3, 1, -4] = true := by decide +kernel
theorem subd10_0_297 : subd10_0 [-3, 1, -3] = true := by decide +kernel
theorem subd10_0_298 : subd10_0 [-3, 1, -2] = true := by decide +kernel
theorem subd10_0_299 : subd10_0 [-3, 1, -1] = true := by decide +kernel
theorem subd10_0_300 : subd10_0 [-3, 1, 0] = true := by decide +kernel
theorem subd10_0_301 : subd10_0 [-3, 1, 1] = true := by decide +kernel
theorem subd10_0_302 : subd10_0 [-3, 1, 2] = true := by decide +kernel
theorem subd10_0_303 : subd10_0 [-3, 1, 3] = true := by decide +kernel
theorem subd10_0_304 : subd10_0 [-3, 1, 4] = true := by decide +kernel
theorem subd10_0_305 : subd10_0 [-3, 1, 5] = true := by decide +kernel
theorem subd10_0_306 : subd10_0 [-3, 1, 6] = true := by decide +kernel
theorem subd10_0_307 : subd10_0 [-3, 1, 7] = true := by decide +kernel
theorem subd10_0_308 : subd10_0 [-3, 2, -9] = true := by decide +kernel
theorem subd10_0_309 : subd10_0 [-3, 2, -8] = true := by decide +kernel
theorem subd10_0_310 : subd10_0 [-3, 2, -7] = true := by decide +kernel
theorem subd10_0_311 : subd10_0 [-3, 2, -6] = true := by decide +kernel
theorem subd10_0_312 : subd10_0 [-3, 2, -5] = true := by decide +kernel
theorem subd10_0_313 : subd10_0 [-3, 2, -4] = true := by decide +kernel
theorem subd10_0_314 : subd10_0 [-3, 2, -3] = true := by decide +kernel
theorem subd10_0_315 : subd10_0 [-3, 2, -2] = true := by decide +kernel
theorem subd10_0_316 : subd10_0 [-3, 2, -1] = true := by decide +kernel
theorem subd10_0_317 : subd10_0 [-3, 2, 0] = true := by decide +kernel
theorem subd10_0_318 : subd10_0 [-3, 2, 1] = true := by decide +kernel
theorem subd10_0_319 : subd10_0 [-3, 2, 2] = true := by decide +kernel
theorem sbd10_0_9 : ∀ q ∈ blkd10_0_9, subd10_0 q = true := by
  unfold blkd10_0_9
  exact List.forall_mem_cons.2 ⟨subd10_0_288, List.forall_mem_cons.2 ⟨subd10_0_289, List.forall_mem_cons.2 ⟨subd10_0_290, List.forall_mem_cons.2 ⟨subd10_0_291, List.forall_mem_cons.2 ⟨subd10_0_292, List.forall_mem_cons.2 ⟨subd10_0_293, List.forall_mem_cons.2 ⟨subd10_0_294, List.forall_mem_cons.2 ⟨subd10_0_295, List.forall_mem_cons.2 ⟨subd10_0_296, List.forall_mem_cons.2 ⟨subd10_0_297, List.forall_mem_cons.2 ⟨subd10_0_298, List.forall_mem_cons.2 ⟨subd10_0_299, List.forall_mem_cons.2 ⟨subd10_0_300, List.forall_mem_cons.2 ⟨subd10_0_301, List.forall_mem_cons.2 ⟨subd10_0_302, List.forall_mem_cons.2 ⟨subd10_0_303, List.forall_mem_cons.2 ⟨subd10_0_304, List.forall_mem_cons.2 ⟨subd10_0_305, List.forall_mem_cons.2 ⟨subd10_0_306, List.forall_mem_cons.2 ⟨subd10_0_307, List.forall_mem_cons.2 ⟨subd10_0_308, List.forall_mem_cons.2 ⟨subd10_0_309, List.forall_mem_cons.2 ⟨subd10_0_310, List.forall_mem_cons.2 ⟨subd10_0_311, List.forall_mem_cons.2 ⟨subd10_0_312, List.forall_mem_cons.2 ⟨subd10_0_313, List.forall_mem_cons.2 ⟨subd10_0_314, List.forall_mem_cons.2 ⟨subd10_0_315, List.forall_mem_cons.2 ⟨subd10_0_316, List.forall_mem_cons.2 ⟨subd10_0_317, List.forall_mem_cons.2 ⟨subd10_0_318, List.forall_mem_cons.2 ⟨subd10_0_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_320 : subd10_0 [-3, 2, 3] = true := by decide +kernel
theorem subd10_0_321 : subd10_0 [-3, 2, 4] = true := by decide +kernel
theorem subd10_0_322 : subd10_0 [-3, 2, 5] = true := by decide +kernel
theorem subd10_0_323 : subd10_0 [-3, 2, 6] = true := by decide +kernel
theorem subd10_0_324 : subd10_0 [-3, 3, -9] = true := by decide +kernel
theorem subd10_0_325 : subd10_0 [-3, 3, -8] = true := by decide +kernel
theorem subd10_0_326 : subd10_0 [-3, 3, -7] = true := by decide +kernel
theorem subd10_0_327 : subd10_0 [-3, 3, -6] = true := by decide +kernel
theorem subd10_0_328 : subd10_0 [-3, 3, -5] = true := by decide +kernel
theorem subd10_0_329 : subd10_0 [-3, 3, -4] = true := by decide +kernel
theorem subd10_0_330 : subd10_0 [-3, 3, -3] = true := by decide +kernel
theorem subd10_0_331 : subd10_0 [-3, 3, -2] = true := by decide +kernel
theorem subd10_0_332 : subd10_0 [-3, 3, -1] = true := by decide +kernel
theorem subd10_0_333 : subd10_0 [-3, 3, 0] = true := by decide +kernel
theorem subd10_0_334 : subd10_0 [-3, 3, 1] = true := by decide +kernel
theorem subd10_0_335 : subd10_0 [-3, 3, 2] = true := by decide +kernel
theorem subd10_0_336 : subd10_0 [-3, 3, 3] = true := by decide +kernel
theorem subd10_0_337 : subd10_0 [-3, 3, 4] = true := by decide +kernel
theorem subd10_0_338 : subd10_0 [-3, 3, 5] = true := by decide +kernel
theorem subd10_0_339 : subd10_0 [-3, 3, 6] = true := by decide +kernel
theorem subd10_0_340 : subd10_0 [-3, 4, -9] = true := by decide +kernel
theorem subd10_0_341 : subd10_0 [-3, 4, -8] = true := by decide +kernel
theorem subd10_0_342 : subd10_0 [-3, 4, -7] = true := by decide +kernel
theorem subd10_0_343 : subd10_0 [-3, 4, -6] = true := by decide +kernel
theorem subd10_0_344 : subd10_0 [-3, 4, -5] = true := by decide +kernel
theorem subd10_0_345 : subd10_0 [-3, 4, -4] = true := by decide +kernel
theorem subd10_0_346 : subd10_0 [-3, 4, -3] = true := by decide +kernel
theorem subd10_0_347 : subd10_0 [-3, 4, -2] = true := by decide +kernel
theorem subd10_0_348 : subd10_0 [-3, 4, -1] = true := by decide +kernel
theorem subd10_0_349 : subd10_0 [-3, 4, 0] = true := by decide +kernel
theorem subd10_0_350 : subd10_0 [-3, 4, 1] = true := by decide +kernel
theorem subd10_0_351 : subd10_0 [-3, 4, 2] = true := by decide +kernel
theorem sbd10_0_10 : ∀ q ∈ blkd10_0_10, subd10_0 q = true := by
  unfold blkd10_0_10
  exact List.forall_mem_cons.2 ⟨subd10_0_320, List.forall_mem_cons.2 ⟨subd10_0_321, List.forall_mem_cons.2 ⟨subd10_0_322, List.forall_mem_cons.2 ⟨subd10_0_323, List.forall_mem_cons.2 ⟨subd10_0_324, List.forall_mem_cons.2 ⟨subd10_0_325, List.forall_mem_cons.2 ⟨subd10_0_326, List.forall_mem_cons.2 ⟨subd10_0_327, List.forall_mem_cons.2 ⟨subd10_0_328, List.forall_mem_cons.2 ⟨subd10_0_329, List.forall_mem_cons.2 ⟨subd10_0_330, List.forall_mem_cons.2 ⟨subd10_0_331, List.forall_mem_cons.2 ⟨subd10_0_332, List.forall_mem_cons.2 ⟨subd10_0_333, List.forall_mem_cons.2 ⟨subd10_0_334, List.forall_mem_cons.2 ⟨subd10_0_335, List.forall_mem_cons.2 ⟨subd10_0_336, List.forall_mem_cons.2 ⟨subd10_0_337, List.forall_mem_cons.2 ⟨subd10_0_338, List.forall_mem_cons.2 ⟨subd10_0_339, List.forall_mem_cons.2 ⟨subd10_0_340, List.forall_mem_cons.2 ⟨subd10_0_341, List.forall_mem_cons.2 ⟨subd10_0_342, List.forall_mem_cons.2 ⟨subd10_0_343, List.forall_mem_cons.2 ⟨subd10_0_344, List.forall_mem_cons.2 ⟨subd10_0_345, List.forall_mem_cons.2 ⟨subd10_0_346, List.forall_mem_cons.2 ⟨subd10_0_347, List.forall_mem_cons.2 ⟨subd10_0_348, List.forall_mem_cons.2 ⟨subd10_0_349, List.forall_mem_cons.2 ⟨subd10_0_350, List.forall_mem_cons.2 ⟨subd10_0_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_352 : subd10_0 [-3, 4, 3] = true := by decide +kernel
theorem subd10_0_353 : subd10_0 [-3, 4, 4] = true := by decide +kernel
theorem subd10_0_354 : subd10_0 [-3, 4, 5] = true := by decide +kernel
theorem subd10_0_355 : subd10_0 [-3, 5] = true := by decide +kernel
theorem subd10_0_356 : subd10_0 [-3, 6] = true := by decide +kernel
theorem subd10_0_357 : subd10_0 [-3, 7] = true := by decide +kernel
theorem subd10_0_358 : subd10_0 [-2, -8] = true := by decide +kernel
theorem subd10_0_359 : subd10_0 [-2, -7] = true := by decide +kernel
theorem subd10_0_360 : subd10_0 [-2, -6] = true := by decide +kernel
theorem subd10_0_361 : subd10_0 [-2, -5] = true := by decide +kernel
theorem subd10_0_362 : subd10_0 [-2, -4, -7] = true := by decide +kernel
theorem subd10_0_363 : subd10_0 [-2, -4, -6] = true := by decide +kernel
theorem subd10_0_364 : subd10_0 [-2, -4, -5] = true := by decide +kernel
theorem subd10_0_365 : subd10_0 [-2, -4, -4] = true := by decide +kernel
theorem subd10_0_366 : subd10_0 [-2, -4, -3] = true := by decide +kernel
theorem subd10_0_367 : subd10_0 [-2, -4, -2] = true := by decide +kernel
theorem subd10_0_368 : subd10_0 [-2, -4, -1] = true := by decide +kernel
theorem subd10_0_369 : subd10_0 [-2, -4, 0] = true := by decide +kernel
theorem subd10_0_370 : subd10_0 [-2, -4, 1] = true := by decide +kernel
theorem subd10_0_371 : subd10_0 [-2, -4, 2] = true := by decide +kernel
theorem subd10_0_372 : subd10_0 [-2, -4, 3] = true := by decide +kernel
theorem subd10_0_373 : subd10_0 [-2, -4, 4] = true := by decide +kernel
theorem subd10_0_374 : subd10_0 [-2, -4, 5] = true := by decide +kernel
theorem subd10_0_375 : subd10_0 [-2, -4, 6] = true := by decide +kernel
theorem subd10_0_376 : subd10_0 [-2, -4, 7] = true := by decide +kernel
theorem subd10_0_377 : subd10_0 [-2, -3, -8] = true := by decide +kernel
theorem subd10_0_378 : subd10_0 [-2, -3, -7] = true := by decide +kernel
theorem subd10_0_379 : subd10_0 [-2, -3, -6] = true := by decide +kernel
theorem subd10_0_380 : subd10_0 [-2, -3, -5] = true := by decide +kernel
theorem subd10_0_381 : subd10_0 [-2, -3, -4] = true := by decide +kernel
theorem subd10_0_382 : subd10_0 [-2, -3, -3] = true := by decide +kernel
theorem subd10_0_383 : subd10_0 [-2, -3, -2] = true := by decide +kernel
theorem sbd10_0_11 : ∀ q ∈ blkd10_0_11, subd10_0 q = true := by
  unfold blkd10_0_11
  exact List.forall_mem_cons.2 ⟨subd10_0_352, List.forall_mem_cons.2 ⟨subd10_0_353, List.forall_mem_cons.2 ⟨subd10_0_354, List.forall_mem_cons.2 ⟨subd10_0_355, List.forall_mem_cons.2 ⟨subd10_0_356, List.forall_mem_cons.2 ⟨subd10_0_357, List.forall_mem_cons.2 ⟨subd10_0_358, List.forall_mem_cons.2 ⟨subd10_0_359, List.forall_mem_cons.2 ⟨subd10_0_360, List.forall_mem_cons.2 ⟨subd10_0_361, List.forall_mem_cons.2 ⟨subd10_0_362, List.forall_mem_cons.2 ⟨subd10_0_363, List.forall_mem_cons.2 ⟨subd10_0_364, List.forall_mem_cons.2 ⟨subd10_0_365, List.forall_mem_cons.2 ⟨subd10_0_366, List.forall_mem_cons.2 ⟨subd10_0_367, List.forall_mem_cons.2 ⟨subd10_0_368, List.forall_mem_cons.2 ⟨subd10_0_369, List.forall_mem_cons.2 ⟨subd10_0_370, List.forall_mem_cons.2 ⟨subd10_0_371, List.forall_mem_cons.2 ⟨subd10_0_372, List.forall_mem_cons.2 ⟨subd10_0_373, List.forall_mem_cons.2 ⟨subd10_0_374, List.forall_mem_cons.2 ⟨subd10_0_375, List.forall_mem_cons.2 ⟨subd10_0_376, List.forall_mem_cons.2 ⟨subd10_0_377, List.forall_mem_cons.2 ⟨subd10_0_378, List.forall_mem_cons.2 ⟨subd10_0_379, List.forall_mem_cons.2 ⟨subd10_0_380, List.forall_mem_cons.2 ⟨subd10_0_381, List.forall_mem_cons.2 ⟨subd10_0_382, List.forall_mem_cons.2 ⟨subd10_0_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_384 : subd10_0 [-2, -3, -1] = true := by decide +kernel
theorem subd10_0_385 : subd10_0 [-2, -3, 0] = true := by decide +kernel
theorem subd10_0_386 : subd10_0 [-2, -3, 1] = true := by decide +kernel
theorem subd10_0_387 : subd10_0 [-2, -3, 2] = true := by decide +kernel
theorem subd10_0_388 : subd10_0 [-2, -3, 3] = true := by decide +kernel
theorem subd10_0_389 : subd10_0 [-2, -3, 4] = true := by decide +kernel
theorem subd10_0_390 : subd10_0 [-2, -3, 5] = true := by decide +kernel
theorem subd10_0_391 : subd10_0 [-2, -3, 6] = true := by decide +kernel
theorem subd10_0_392 : subd10_0 [-2, -3, 7] = true := by decide +kernel
theorem subd10_0_393 : subd10_0 [-2, -2, -9] = true := by decide +kernel
theorem subd10_0_394 : subd10_0 [-2, -2, -8] = true := by decide +kernel
theorem subd10_0_395 : subd10_0 [-2, -2, -7] = true := by decide +kernel
theorem subd10_0_396 : subd10_0 [-2, -2, -6] = true := by decide +kernel
theorem subd10_0_397 : subd10_0 [-2, -2, -5] = true := by decide +kernel
theorem subd10_0_398 : subd10_0 [-2, -2, -4] = true := by decide +kernel
theorem subd10_0_399 : subd10_0 [-2, -2, -3] = true := by decide +kernel
theorem subd10_0_400 : subd10_0 [-2, -2, -2] = true := by decide +kernel
theorem subd10_0_401 : subd10_0 [-2, -2, -1] = true := by decide +kernel
theorem subd10_0_402 : subd10_0 [-2, -2, 0] = true := by decide +kernel
theorem subd10_0_403 : subd10_0 [-2, -2, 1] = true := by decide +kernel
theorem subd10_0_404 : subd10_0 [-2, -2, 2] = true := by decide +kernel
theorem subd10_0_405 : subd10_0 [-2, -2, 3] = true := by decide +kernel
theorem subd10_0_406 : subd10_0 [-2, -2, 4] = true := by decide +kernel
theorem subd10_0_407 : subd10_0 [-2, -2, 5] = true := by decide +kernel
theorem subd10_0_408 : subd10_0 [-2, -2, 6] = true := by decide +kernel
theorem subd10_0_409 : subd10_0 [-2, -2, 7] = true := by decide +kernel
theorem subd10_0_410 : subd10_0 [-2, -2, 8] = true := by decide +kernel
theorem subd10_0_411 : subd10_0 [-2, -1, -9] = true := by decide +kernel
theorem subd10_0_412 : subd10_0 [-2, -1, -8] = true := by decide +kernel
theorem subd10_0_413 : subd10_0 [-2, -1, -7] = true := by decide +kernel
theorem subd10_0_414 : subd10_0 [-2, -1, -6] = true := by decide +kernel
theorem subd10_0_415 : subd10_0 [-2, -1, -5] = true := by decide +kernel
theorem sbd10_0_12 : ∀ q ∈ blkd10_0_12, subd10_0 q = true := by
  unfold blkd10_0_12
  exact List.forall_mem_cons.2 ⟨subd10_0_384, List.forall_mem_cons.2 ⟨subd10_0_385, List.forall_mem_cons.2 ⟨subd10_0_386, List.forall_mem_cons.2 ⟨subd10_0_387, List.forall_mem_cons.2 ⟨subd10_0_388, List.forall_mem_cons.2 ⟨subd10_0_389, List.forall_mem_cons.2 ⟨subd10_0_390, List.forall_mem_cons.2 ⟨subd10_0_391, List.forall_mem_cons.2 ⟨subd10_0_392, List.forall_mem_cons.2 ⟨subd10_0_393, List.forall_mem_cons.2 ⟨subd10_0_394, List.forall_mem_cons.2 ⟨subd10_0_395, List.forall_mem_cons.2 ⟨subd10_0_396, List.forall_mem_cons.2 ⟨subd10_0_397, List.forall_mem_cons.2 ⟨subd10_0_398, List.forall_mem_cons.2 ⟨subd10_0_399, List.forall_mem_cons.2 ⟨subd10_0_400, List.forall_mem_cons.2 ⟨subd10_0_401, List.forall_mem_cons.2 ⟨subd10_0_402, List.forall_mem_cons.2 ⟨subd10_0_403, List.forall_mem_cons.2 ⟨subd10_0_404, List.forall_mem_cons.2 ⟨subd10_0_405, List.forall_mem_cons.2 ⟨subd10_0_406, List.forall_mem_cons.2 ⟨subd10_0_407, List.forall_mem_cons.2 ⟨subd10_0_408, List.forall_mem_cons.2 ⟨subd10_0_409, List.forall_mem_cons.2 ⟨subd10_0_410, List.forall_mem_cons.2 ⟨subd10_0_411, List.forall_mem_cons.2 ⟨subd10_0_412, List.forall_mem_cons.2 ⟨subd10_0_413, List.forall_mem_cons.2 ⟨subd10_0_414, List.forall_mem_cons.2 ⟨subd10_0_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_416 : subd10_0 [-2, -1, -4] = true := by decide +kernel
theorem subd10_0_417 : subd10_0 [-2, -1, -3] = true := by decide +kernel
theorem subd10_0_418 : subd10_0 [-2, -1, -2] = true := by decide +kernel
theorem subd10_0_419 : subd10_0 [-2, -1, -1] = true := by decide +kernel
theorem subd10_0_420 : subd10_0 [-2, -1, 0] = true := by decide +kernel
theorem subd10_0_421 : subd10_0 [-2, -1, 1] = true := by decide +kernel
theorem subd10_0_422 : subd10_0 [-2, -1, 2] = true := by decide +kernel
theorem subd10_0_423 : subd10_0 [-2, -1, 3] = true := by decide +kernel
theorem subd10_0_424 : subd10_0 [-2, -1, 4] = true := by decide +kernel
theorem subd10_0_425 : subd10_0 [-2, -1, 5] = true := by decide +kernel
theorem subd10_0_426 : subd10_0 [-2, -1, 6] = true := by decide +kernel
theorem subd10_0_427 : subd10_0 [-2, -1, 7] = true := by decide +kernel
theorem subd10_0_428 : subd10_0 [-2, -1, 8] = true := by decide +kernel
theorem subd10_0_429 : subd10_0 [-2, 0, -9] = true := by decide +kernel
theorem subd10_0_430 : subd10_0 [-2, 0, -8] = true := by decide +kernel
theorem subd10_0_431 : subd10_0 [-2, 0, -7] = true := by decide +kernel
theorem subd10_0_432 : subd10_0 [-2, 0, -6] = true := by decide +kernel
theorem subd10_0_433 : subd10_0 [-2, 0, -5] = true := by decide +kernel
theorem subd10_0_434 : subd10_0 [-2, 0, -4] = true := by decide +kernel
theorem subd10_0_435 : subd10_0 [-2, 0, -3] = true := by decide +kernel
theorem subd10_0_436 : subd10_0 [-2, 0, -2] = true := by decide +kernel
theorem subd10_0_437 : subd10_0 [-2, 0, -1] = true := by decide +kernel
theorem subd10_0_438 : subd10_0 [-2, 0, 0] = true := by decide +kernel
theorem subd10_0_439 : subd10_0 [-2, 0, 1] = true := by decide +kernel
theorem subd10_0_440 : subd10_0 [-2, 0, 2] = true := by decide +kernel
theorem subd10_0_441 : subd10_0 [-2, 0, 3] = true := by decide +kernel
theorem subd10_0_442 : subd10_0 [-2, 0, 4] = true := by decide +kernel
theorem subd10_0_443 : subd10_0 [-2, 0, 5] = true := by decide +kernel
theorem subd10_0_444 : subd10_0 [-2, 0, 6] = true := by decide +kernel
theorem subd10_0_445 : subd10_0 [-2, 0, 7] = true := by decide +kernel
theorem subd10_0_446 : subd10_0 [-2, 0, 8] = true := by decide +kernel
theorem subd10_0_447 : subd10_0 [-2, 1, -10] = true := by decide +kernel
theorem sbd10_0_13 : ∀ q ∈ blkd10_0_13, subd10_0 q = true := by
  unfold blkd10_0_13
  exact List.forall_mem_cons.2 ⟨subd10_0_416, List.forall_mem_cons.2 ⟨subd10_0_417, List.forall_mem_cons.2 ⟨subd10_0_418, List.forall_mem_cons.2 ⟨subd10_0_419, List.forall_mem_cons.2 ⟨subd10_0_420, List.forall_mem_cons.2 ⟨subd10_0_421, List.forall_mem_cons.2 ⟨subd10_0_422, List.forall_mem_cons.2 ⟨subd10_0_423, List.forall_mem_cons.2 ⟨subd10_0_424, List.forall_mem_cons.2 ⟨subd10_0_425, List.forall_mem_cons.2 ⟨subd10_0_426, List.forall_mem_cons.2 ⟨subd10_0_427, List.forall_mem_cons.2 ⟨subd10_0_428, List.forall_mem_cons.2 ⟨subd10_0_429, List.forall_mem_cons.2 ⟨subd10_0_430, List.forall_mem_cons.2 ⟨subd10_0_431, List.forall_mem_cons.2 ⟨subd10_0_432, List.forall_mem_cons.2 ⟨subd10_0_433, List.forall_mem_cons.2 ⟨subd10_0_434, List.forall_mem_cons.2 ⟨subd10_0_435, List.forall_mem_cons.2 ⟨subd10_0_436, List.forall_mem_cons.2 ⟨subd10_0_437, List.forall_mem_cons.2 ⟨subd10_0_438, List.forall_mem_cons.2 ⟨subd10_0_439, List.forall_mem_cons.2 ⟨subd10_0_440, List.forall_mem_cons.2 ⟨subd10_0_441, List.forall_mem_cons.2 ⟨subd10_0_442, List.forall_mem_cons.2 ⟨subd10_0_443, List.forall_mem_cons.2 ⟨subd10_0_444, List.forall_mem_cons.2 ⟨subd10_0_445, List.forall_mem_cons.2 ⟨subd10_0_446, List.forall_mem_cons.2 ⟨subd10_0_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_448 : subd10_0 [-2, 1, -9] = true := by decide +kernel
theorem subd10_0_449 : subd10_0 [-2, 1, -8] = true := by decide +kernel
theorem subd10_0_450 : subd10_0 [-2, 1, -7] = true := by decide +kernel
theorem subd10_0_451 : subd10_0 [-2, 1, -6] = true := by decide +kernel
theorem subd10_0_452 : subd10_0 [-2, 1, -5] = true := by decide +kernel
theorem subd10_0_453 : subd10_0 [-2, 1, -4] = true := by decide +kernel
theorem subd10_0_454 : subd10_0 [-2, 1, -3] = true := by decide +kernel
theorem subd10_0_455 : subd10_0 [-2, 1, -2] = true := by decide +kernel
theorem subd10_0_456 : subd10_0 [-2, 1, -1] = true := by decide +kernel
theorem subd10_0_457 : subd10_0 [-2, 1, 0] = true := by decide +kernel
theorem subd10_0_458 : subd10_0 [-2, 1, 1] = true := by decide +kernel
theorem subd10_0_459 : subd10_0 [-2, 1, 2] = true := by decide +kernel
theorem subd10_0_460 : subd10_0 [-2, 1, 3] = true := by decide +kernel
theorem subd10_0_461 : subd10_0 [-2, 1, 4] = true := by decide +kernel
theorem subd10_0_462 : subd10_0 [-2, 1, 5] = true := by decide +kernel
theorem subd10_0_463 : subd10_0 [-2, 1, 6] = true := by decide +kernel
theorem subd10_0_464 : subd10_0 [-2, 1, 7] = true := by decide +kernel
theorem subd10_0_465 : subd10_0 [-2, 2, -10] = true := by decide +kernel
theorem subd10_0_466 : subd10_0 [-2, 2, -9] = true := by decide +kernel
theorem subd10_0_467 : subd10_0 [-2, 2, -8] = true := by decide +kernel
theorem subd10_0_468 : subd10_0 [-2, 2, -7] = true := by decide +kernel
theorem subd10_0_469 : subd10_0 [-2, 2, -6] = true := by decide +kernel
theorem subd10_0_470 : subd10_0 [-2, 2, -5] = true := by decide +kernel
theorem subd10_0_471 : subd10_0 [-2, 2, -4] = true := by decide +kernel
theorem subd10_0_472 : subd10_0 [-2, 2, -3] = true := by decide +kernel
theorem subd10_0_473 : subd10_0 [-2, 2, -2] = true := by decide +kernel
theorem subd10_0_474 : subd10_0 [-2, 2, -1] = true := by decide +kernel
theorem subd10_0_475 : subd10_0 [-2, 2, 0] = true := by decide +kernel
theorem subd10_0_476 : subd10_0 [-2, 2, 1] = true := by decide +kernel
theorem subd10_0_477 : subd10_0 [-2, 2, 2] = true := by decide +kernel
theorem subd10_0_478 : subd10_0 [-2, 2, 3] = true := by decide +kernel
theorem subd10_0_479 : subd10_0 [-2, 2, 4] = true := by decide +kernel
theorem sbd10_0_14 : ∀ q ∈ blkd10_0_14, subd10_0 q = true := by
  unfold blkd10_0_14
  exact List.forall_mem_cons.2 ⟨subd10_0_448, List.forall_mem_cons.2 ⟨subd10_0_449, List.forall_mem_cons.2 ⟨subd10_0_450, List.forall_mem_cons.2 ⟨subd10_0_451, List.forall_mem_cons.2 ⟨subd10_0_452, List.forall_mem_cons.2 ⟨subd10_0_453, List.forall_mem_cons.2 ⟨subd10_0_454, List.forall_mem_cons.2 ⟨subd10_0_455, List.forall_mem_cons.2 ⟨subd10_0_456, List.forall_mem_cons.2 ⟨subd10_0_457, List.forall_mem_cons.2 ⟨subd10_0_458, List.forall_mem_cons.2 ⟨subd10_0_459, List.forall_mem_cons.2 ⟨subd10_0_460, List.forall_mem_cons.2 ⟨subd10_0_461, List.forall_mem_cons.2 ⟨subd10_0_462, List.forall_mem_cons.2 ⟨subd10_0_463, List.forall_mem_cons.2 ⟨subd10_0_464, List.forall_mem_cons.2 ⟨subd10_0_465, List.forall_mem_cons.2 ⟨subd10_0_466, List.forall_mem_cons.2 ⟨subd10_0_467, List.forall_mem_cons.2 ⟨subd10_0_468, List.forall_mem_cons.2 ⟨subd10_0_469, List.forall_mem_cons.2 ⟨subd10_0_470, List.forall_mem_cons.2 ⟨subd10_0_471, List.forall_mem_cons.2 ⟨subd10_0_472, List.forall_mem_cons.2 ⟨subd10_0_473, List.forall_mem_cons.2 ⟨subd10_0_474, List.forall_mem_cons.2 ⟨subd10_0_475, List.forall_mem_cons.2 ⟨subd10_0_476, List.forall_mem_cons.2 ⟨subd10_0_477, List.forall_mem_cons.2 ⟨subd10_0_478, List.forall_mem_cons.2 ⟨subd10_0_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_0_480 : subd10_0 [-2, 2, 5] = true := by decide +kernel
theorem subd10_0_481 : subd10_0 [-2, 2, 6] = true := by decide +kernel
theorem subd10_0_482 : subd10_0 [-2, 2, 7] = true := by decide +kernel
theorem subd10_0_483 : subd10_0 [-2, 3, -9] = true := by decide +kernel
theorem subd10_0_484 : subd10_0 [-2, 3, -8] = true := by decide +kernel
theorem subd10_0_485 : subd10_0 [-2, 3, -7] = true := by decide +kernel
theorem subd10_0_486 : subd10_0 [-2, 3, -6] = true := by decide +kernel
theorem subd10_0_487 : subd10_0 [-2, 3, -5] = true := by decide +kernel
theorem subd10_0_488 : subd10_0 [-2, 3, -4] = true := by decide +kernel
theorem subd10_0_489 : subd10_0 [-2, 3, -3] = true := by decide +kernel
theorem subd10_0_490 : subd10_0 [-2, 3, -2] = true := by decide +kernel
theorem subd10_0_491 : subd10_0 [-2, 3, -1] = true := by decide +kernel
theorem subd10_0_492 : subd10_0 [-2, 3, 0] = true := by decide +kernel
theorem subd10_0_493 : subd10_0 [-2, 3, 1] = true := by decide +kernel
theorem subd10_0_494 : subd10_0 [-2, 3, 2] = true := by decide +kernel
theorem subd10_0_495 : subd10_0 [-2, 3, 3] = true := by decide +kernel
theorem subd10_0_496 : subd10_0 [-2, 3, 4] = true := by decide +kernel
theorem subd10_0_497 : subd10_0 [-2, 3, 5] = true := by decide +kernel
theorem subd10_0_498 : subd10_0 [-2, 3, 6] = true := by decide +kernel
theorem subd10_0_499 : subd10_0 [-2, 4, -9] = true := by decide +kernel
theorem subd10_0_500 : subd10_0 [-2, 4, -8] = true := by decide +kernel
theorem subd10_0_501 : subd10_0 [-2, 4, -7] = true := by decide +kernel
theorem subd10_0_502 : subd10_0 [-2, 4, -6] = true := by decide +kernel
theorem subd10_0_503 : subd10_0 [-2, 4, -5] = true := by decide +kernel
theorem subd10_0_504 : subd10_0 [-2, 4, -4] = true := by decide +kernel
theorem subd10_0_505 : subd10_0 [-2, 4, -3] = true := by decide +kernel
theorem subd10_0_506 : subd10_0 [-2, 4, -2] = true := by decide +kernel
theorem subd10_0_507 : subd10_0 [-2, 4, -1] = true := by decide +kernel
theorem subd10_0_508 : subd10_0 [-2, 4, 0] = true := by decide +kernel
theorem subd10_0_509 : subd10_0 [-2, 4, 1] = true := by decide +kernel
theorem subd10_0_510 : subd10_0 [-2, 4, 2] = true := by decide +kernel
theorem subd10_0_511 : subd10_0 [-2, 4, 3] = true := by decide +kernel
theorem sbd10_0_15 : ∀ q ∈ blkd10_0_15, subd10_0 q = true := by
  unfold blkd10_0_15
  exact List.forall_mem_cons.2 ⟨subd10_0_480, List.forall_mem_cons.2 ⟨subd10_0_481, List.forall_mem_cons.2 ⟨subd10_0_482, List.forall_mem_cons.2 ⟨subd10_0_483, List.forall_mem_cons.2 ⟨subd10_0_484, List.forall_mem_cons.2 ⟨subd10_0_485, List.forall_mem_cons.2 ⟨subd10_0_486, List.forall_mem_cons.2 ⟨subd10_0_487, List.forall_mem_cons.2 ⟨subd10_0_488, List.forall_mem_cons.2 ⟨subd10_0_489, List.forall_mem_cons.2 ⟨subd10_0_490, List.forall_mem_cons.2 ⟨subd10_0_491, List.forall_mem_cons.2 ⟨subd10_0_492, List.forall_mem_cons.2 ⟨subd10_0_493, List.forall_mem_cons.2 ⟨subd10_0_494, List.forall_mem_cons.2 ⟨subd10_0_495, List.forall_mem_cons.2 ⟨subd10_0_496, List.forall_mem_cons.2 ⟨subd10_0_497, List.forall_mem_cons.2 ⟨subd10_0_498, List.forall_mem_cons.2 ⟨subd10_0_499, List.forall_mem_cons.2 ⟨subd10_0_500, List.forall_mem_cons.2 ⟨subd10_0_501, List.forall_mem_cons.2 ⟨subd10_0_502, List.forall_mem_cons.2 ⟨subd10_0_503, List.forall_mem_cons.2 ⟨subd10_0_504, List.forall_mem_cons.2 ⟨subd10_0_505, List.forall_mem_cons.2 ⟨subd10_0_506, List.forall_mem_cons.2 ⟨subd10_0_507, List.forall_mem_cons.2 ⟨subd10_0_508, List.forall_mem_cons.2 ⟨subd10_0_509, List.forall_mem_cons.2 ⟨subd10_0_510, List.forall_mem_cons.2 ⟨subd10_0_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C131
