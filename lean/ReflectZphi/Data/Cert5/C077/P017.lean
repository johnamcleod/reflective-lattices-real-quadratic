import ReflectZphi.Data.Cert5.C077.Base

namespace ReflectZphi.Data.Cert5.C077

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd10_1_96 : subd10_1 [-1, 1, -4] = true := by decide +kernel
theorem subd10_1_97 : subd10_1 [-1, 1, -3] = true := by decide +kernel
theorem subd10_1_98 : subd10_1 [-1, 1, -2] = true := by decide +kernel
theorem subd10_1_99 : subd10_1 [-1, 1, -1] = true := by decide +kernel
theorem subd10_1_100 : subd10_1 [-1, 1, 0] = true := by decide +kernel
theorem subd10_1_101 : subd10_1 [-1, 1, 1] = true := by decide +kernel
theorem subd10_1_102 : subd10_1 [-1, 1, 2] = true := by decide +kernel
theorem subd10_1_103 : subd10_1 [-1, 1, 3] = true := by decide +kernel
theorem subd10_1_104 : subd10_1 [-1, 1, 4] = true := by decide +kernel
theorem subd10_1_105 : subd10_1 [-1, 1, 5] = true := by decide +kernel
theorem subd10_1_106 : subd10_1 [-1, 1, 6] = true := by decide +kernel
theorem subd10_1_107 : subd10_1 [-1, 1, 7] = true := by decide +kernel
theorem subd10_1_108 : subd10_1 [-1, 2] = true := by decide +kernel
theorem subd10_1_109 : subd10_1 [-1, 3] = true := by decide +kernel
theorem subd10_1_110 : subd10_1 [-1, 4] = true := by decide +kernel
theorem subd10_1_111 : subd10_1 [-1, 5] = true := by decide +kernel
theorem subd10_1_112 : subd10_1 [-1, 6] = true := by decide +kernel
theorem subd10_1_113 : subd10_1 [-1, 7] = true := by decide +kernel
theorem subd10_1_114 : subd10_1 [-1, 8] = true := by decide +kernel
theorem subd10_1_115 : subd10_1 [0, -9] = true := by decide +kernel
theorem subd10_1_116 : subd10_1 [0, -8] = true := by decide +kernel
theorem subd10_1_117 : subd10_1 [0, -7] = true := by decide +kernel
theorem subd10_1_118 : subd10_1 [0, -6] = true := by decide +kernel
theorem subd10_1_119 : subd10_1 [0, -5] = true := by decide +kernel
theorem subd10_1_120 : subd10_1 [0, -4] = true := by decide +kernel
theorem subd10_1_121 : subd10_1 [0, -3] = true := by decide +kernel
theorem subd10_1_122 : subd10_1 [0, -2] = true := by decide +kernel
theorem subd10_1_123 : subd10_1 [0, -1, -7] = true := by decide +kernel
theorem subd10_1_124 : subd10_1 [0, -1, -6] = true := by decide +kernel
theorem subd10_1_125 : subd10_1 [0, -1, -5] = true := by decide +kernel
theorem subd10_1_126 : subd10_1 [0, -1, -4] = true := by decide +kernel
theorem subd10_1_127 : subd10_1 [0, -1, -3] = true := by decide +kernel
theorem sbd10_1_3 : ∀ q ∈ blkd10_1_3, subd10_1 q = true := by
  unfold blkd10_1_3
  exact List.forall_mem_cons.2 ⟨subd10_1_96, List.forall_mem_cons.2 ⟨subd10_1_97, List.forall_mem_cons.2 ⟨subd10_1_98, List.forall_mem_cons.2 ⟨subd10_1_99, List.forall_mem_cons.2 ⟨subd10_1_100, List.forall_mem_cons.2 ⟨subd10_1_101, List.forall_mem_cons.2 ⟨subd10_1_102, List.forall_mem_cons.2 ⟨subd10_1_103, List.forall_mem_cons.2 ⟨subd10_1_104, List.forall_mem_cons.2 ⟨subd10_1_105, List.forall_mem_cons.2 ⟨subd10_1_106, List.forall_mem_cons.2 ⟨subd10_1_107, List.forall_mem_cons.2 ⟨subd10_1_108, List.forall_mem_cons.2 ⟨subd10_1_109, List.forall_mem_cons.2 ⟨subd10_1_110, List.forall_mem_cons.2 ⟨subd10_1_111, List.forall_mem_cons.2 ⟨subd10_1_112, List.forall_mem_cons.2 ⟨subd10_1_113, List.forall_mem_cons.2 ⟨subd10_1_114, List.forall_mem_cons.2 ⟨subd10_1_115, List.forall_mem_cons.2 ⟨subd10_1_116, List.forall_mem_cons.2 ⟨subd10_1_117, List.forall_mem_cons.2 ⟨subd10_1_118, List.forall_mem_cons.2 ⟨subd10_1_119, List.forall_mem_cons.2 ⟨subd10_1_120, List.forall_mem_cons.2 ⟨subd10_1_121, List.forall_mem_cons.2 ⟨subd10_1_122, List.forall_mem_cons.2 ⟨subd10_1_123, List.forall_mem_cons.2 ⟨subd10_1_124, List.forall_mem_cons.2 ⟨subd10_1_125, List.forall_mem_cons.2 ⟨subd10_1_126, List.forall_mem_cons.2 ⟨subd10_1_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_128 : subd10_1 [0, -1, -2] = true := by decide +kernel
theorem subd10_1_129 : subd10_1 [0, -1, -1] = true := by decide +kernel
theorem subd10_1_130 : subd10_1 [0, -1, 0] = true := by decide +kernel
theorem subd10_1_131 : subd10_1 [0, -1, 1] = true := by decide +kernel
theorem subd10_1_132 : subd10_1 [0, -1, 2] = true := by decide +kernel
theorem subd10_1_133 : subd10_1 [0, -1, 3] = true := by decide +kernel
theorem subd10_1_134 : subd10_1 [0, -1, 4] = true := by decide +kernel
theorem subd10_1_135 : subd10_1 [0, -1, 5] = true := by decide +kernel
theorem subd10_1_136 : subd10_1 [0, -1, 6] = true := by decide +kernel
theorem subd10_1_137 : subd10_1 [0, 0, -7] = true := by decide +kernel
theorem subd10_1_138 : subd10_1 [0, 0, -6] = true := by decide +kernel
theorem subd10_1_139 : subd10_1 [0, 0, -5] = true := by decide +kernel
theorem subd10_1_140 : subd10_1 [0, 0, -4] = true := by decide +kernel
theorem subd10_1_141 : subd10_1 [0, 0, -3] = true := by decide +kernel
theorem subd10_1_142 : subd10_1 [0, 0, -2] = true := by decide +kernel
theorem subd10_1_143 : subd10_1 [0, 0, -1] = true := by decide +kernel
theorem subd10_1_144 : subd10_1 [0, 0, 0] = true := by decide +kernel
theorem subd10_1_145 : subd10_1 [0, 0, 1] = true := by decide +kernel
theorem subd10_1_146 : subd10_1 [0, 0, 2] = true := by decide +kernel
theorem subd10_1_147 : subd10_1 [0, 0, 3] = true := by decide +kernel
theorem subd10_1_148 : subd10_1 [0, 0, 4] = true := by decide +kernel
theorem subd10_1_149 : subd10_1 [0, 0, 5] = true := by decide +kernel
theorem subd10_1_150 : subd10_1 [0, 0, 6] = true := by decide +kernel
theorem subd10_1_151 : subd10_1 [0, 1, -7] = true := by decide +kernel
theorem subd10_1_152 : subd10_1 [0, 1, -6] = true := by decide +kernel
theorem subd10_1_153 : subd10_1 [0, 1, -5] = true := by decide +kernel
theorem subd10_1_154 : subd10_1 [0, 1, -4] = true := by decide +kernel
theorem subd10_1_155 : subd10_1 [0, 1, -3] = true := by decide +kernel
theorem subd10_1_156 : subd10_1 [0, 1, -2] = true := by decide +kernel
theorem subd10_1_157 : subd10_1 [0, 1, -1] = true := by decide +kernel
theorem subd10_1_158 : subd10_1 [0, 1, 0] = true := by decide +kernel
theorem subd10_1_159 : subd10_1 [0, 1, 1] = true := by decide +kernel
theorem sbd10_1_4 : ∀ q ∈ blkd10_1_4, subd10_1 q = true := by
  unfold blkd10_1_4
  exact List.forall_mem_cons.2 ⟨subd10_1_128, List.forall_mem_cons.2 ⟨subd10_1_129, List.forall_mem_cons.2 ⟨subd10_1_130, List.forall_mem_cons.2 ⟨subd10_1_131, List.forall_mem_cons.2 ⟨subd10_1_132, List.forall_mem_cons.2 ⟨subd10_1_133, List.forall_mem_cons.2 ⟨subd10_1_134, List.forall_mem_cons.2 ⟨subd10_1_135, List.forall_mem_cons.2 ⟨subd10_1_136, List.forall_mem_cons.2 ⟨subd10_1_137, List.forall_mem_cons.2 ⟨subd10_1_138, List.forall_mem_cons.2 ⟨subd10_1_139, List.forall_mem_cons.2 ⟨subd10_1_140, List.forall_mem_cons.2 ⟨subd10_1_141, List.forall_mem_cons.2 ⟨subd10_1_142, List.forall_mem_cons.2 ⟨subd10_1_143, List.forall_mem_cons.2 ⟨subd10_1_144, List.forall_mem_cons.2 ⟨subd10_1_145, List.forall_mem_cons.2 ⟨subd10_1_146, List.forall_mem_cons.2 ⟨subd10_1_147, List.forall_mem_cons.2 ⟨subd10_1_148, List.forall_mem_cons.2 ⟨subd10_1_149, List.forall_mem_cons.2 ⟨subd10_1_150, List.forall_mem_cons.2 ⟨subd10_1_151, List.forall_mem_cons.2 ⟨subd10_1_152, List.forall_mem_cons.2 ⟨subd10_1_153, List.forall_mem_cons.2 ⟨subd10_1_154, List.forall_mem_cons.2 ⟨subd10_1_155, List.forall_mem_cons.2 ⟨subd10_1_156, List.forall_mem_cons.2 ⟨subd10_1_157, List.forall_mem_cons.2 ⟨subd10_1_158, List.forall_mem_cons.2 ⟨subd10_1_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_160 : subd10_1 [0, 1, 2] = true := by decide +kernel
theorem subd10_1_161 : subd10_1 [0, 1, 3] = true := by decide +kernel
theorem subd10_1_162 : subd10_1 [0, 1, 4] = true := by decide +kernel
theorem subd10_1_163 : subd10_1 [0, 1, 5] = true := by decide +kernel
theorem subd10_1_164 : subd10_1 [0, 1, 6] = true := by decide +kernel
theorem subd10_1_165 : subd10_1 [0, 2] = true := by decide +kernel
theorem subd10_1_166 : subd10_1 [0, 3] = true := by decide +kernel
theorem subd10_1_167 : subd10_1 [0, 4] = true := by decide +kernel
theorem subd10_1_168 : subd10_1 [0, 5] = true := by decide +kernel
theorem subd10_1_169 : subd10_1 [0, 6] = true := by decide +kernel
theorem subd10_1_170 : subd10_1 [0, 7] = true := by decide +kernel
theorem subd10_1_171 : subd10_1 [0, 8] = true := by decide +kernel
theorem subd10_1_172 : subd10_1 [1, -9] = true := by decide +kernel
theorem subd10_1_173 : subd10_1 [1, -8] = true := by decide +kernel
theorem subd10_1_174 : subd10_1 [1, -7] = true := by decide +kernel
theorem subd10_1_175 : subd10_1 [1, -6] = true := by decide +kernel
theorem subd10_1_176 : subd10_1 [1, -5] = true := by decide +kernel
theorem subd10_1_177 : subd10_1 [1, -4] = true := by decide +kernel
theorem subd10_1_178 : subd10_1 [1, -3] = true := by decide +kernel
theorem subd10_1_179 : subd10_1 [1, -2] = true := by decide +kernel
theorem subd10_1_180 : subd10_1 [1, -1, -8] = true := by decide +kernel
theorem subd10_1_181 : subd10_1 [1, -1, -7] = true := by decide +kernel
theorem subd10_1_182 : subd10_1 [1, -1, -6] = true := by decide +kernel
theorem subd10_1_183 : subd10_1 [1, -1, -5] = true := by decide +kernel
theorem subd10_1_184 : subd10_1 [1, -1, -4] = true := by decide +kernel
theorem subd10_1_185 : subd10_1 [1, -1, -3] = true := by decide +kernel
theorem subd10_1_186 : subd10_1 [1, -1, -2] = true := by decide +kernel
theorem subd10_1_187 : subd10_1 [1, -1, -1] = true := by decide +kernel
theorem subd10_1_188 : subd10_1 [1, -1, 0] = true := by decide +kernel
theorem subd10_1_189 : subd10_1 [1, -1, 1] = true := by decide +kernel
theorem subd10_1_190 : subd10_1 [1, -1, 2] = true := by decide +kernel
theorem subd10_1_191 : subd10_1 [1, -1, 3] = true := by decide +kernel
theorem sbd10_1_5 : ∀ q ∈ blkd10_1_5, subd10_1 q = true := by
  unfold blkd10_1_5
  exact List.forall_mem_cons.2 ⟨subd10_1_160, List.forall_mem_cons.2 ⟨subd10_1_161, List.forall_mem_cons.2 ⟨subd10_1_162, List.forall_mem_cons.2 ⟨subd10_1_163, List.forall_mem_cons.2 ⟨subd10_1_164, List.forall_mem_cons.2 ⟨subd10_1_165, List.forall_mem_cons.2 ⟨subd10_1_166, List.forall_mem_cons.2 ⟨subd10_1_167, List.forall_mem_cons.2 ⟨subd10_1_168, List.forall_mem_cons.2 ⟨subd10_1_169, List.forall_mem_cons.2 ⟨subd10_1_170, List.forall_mem_cons.2 ⟨subd10_1_171, List.forall_mem_cons.2 ⟨subd10_1_172, List.forall_mem_cons.2 ⟨subd10_1_173, List.forall_mem_cons.2 ⟨subd10_1_174, List.forall_mem_cons.2 ⟨subd10_1_175, List.forall_mem_cons.2 ⟨subd10_1_176, List.forall_mem_cons.2 ⟨subd10_1_177, List.forall_mem_cons.2 ⟨subd10_1_178, List.forall_mem_cons.2 ⟨subd10_1_179, List.forall_mem_cons.2 ⟨subd10_1_180, List.forall_mem_cons.2 ⟨subd10_1_181, List.forall_mem_cons.2 ⟨subd10_1_182, List.forall_mem_cons.2 ⟨subd10_1_183, List.forall_mem_cons.2 ⟨subd10_1_184, List.forall_mem_cons.2 ⟨subd10_1_185, List.forall_mem_cons.2 ⟨subd10_1_186, List.forall_mem_cons.2 ⟨subd10_1_187, List.forall_mem_cons.2 ⟨subd10_1_188, List.forall_mem_cons.2 ⟨subd10_1_189, List.forall_mem_cons.2 ⟨subd10_1_190, List.forall_mem_cons.2 ⟨subd10_1_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_1_192 : subd10_1 [1, -1, 4] = true := by decide +kernel
theorem subd10_1_193 : subd10_1 [1, -1, 5] = true := by decide +kernel
theorem subd10_1_194 : subd10_1 [1, 0, -7] = true := by decide +kernel
theorem subd10_1_195 : subd10_1 [1, 0, -6] = true := by decide +kernel
theorem subd10_1_196 : subd10_1 [1, 0, -5] = true := by decide +kernel
theorem subd10_1_197 : subd10_1 [1, 0, -4] = true := by decide +kernel
theorem subd10_1_198 : subd10_1 [1, 0, -3] = true := by decide +kernel
theorem subd10_1_199 : subd10_1 [1, 0, -2] = true := by decide +kernel
theorem subd10_1_200 : subd10_1 [1, 0, -1] = true := by decide +kernel
theorem subd10_1_201 : subd10_1 [1, 0, 0] = true := by decide +kernel
theorem subd10_1_202 : subd10_1 [1, 0, 1] = true := by decide +kernel
theorem subd10_1_203 : subd10_1 [1, 0, 2] = true := by decide +kernel
theorem subd10_1_204 : subd10_1 [1, 0, 3] = true := by decide +kernel
theorem subd10_1_205 : subd10_1 [1, 0, 4] = true := by decide +kernel
theorem subd10_1_206 : subd10_1 [1, 0, 5] = true := by decide +kernel
theorem subd10_1_207 : subd10_1 [1, 0, 6] = true := by decide +kernel
theorem subd10_1_208 : subd10_1 [1, 1] = true := by decide +kernel
theorem subd10_1_209 : subd10_1 [1, 2] = true := by decide +kernel
theorem subd10_1_210 : subd10_1 [1, 3] = true := by decide +kernel
theorem subd10_1_211 : subd10_1 [1, 4] = true := by decide +kernel
theorem subd10_1_212 : subd10_1 [1, 5] = true := by decide +kernel
theorem subd10_1_213 : subd10_1 [1, 6] = true := by decide +kernel
theorem subd10_1_214 : subd10_1 [1, 7] = true := by decide +kernel
theorem subd10_1_215 : subd10_1 [2, -9] = true := by decide +kernel
theorem subd10_1_216 : subd10_1 [2, -8] = true := by decide +kernel
theorem subd10_1_217 : subd10_1 [2, -7] = true := by decide +kernel
theorem subd10_1_218 : subd10_1 [2, -6] = true := by decide +kernel
theorem subd10_1_219 : subd10_1 [2, -5] = true := by decide +kernel
theorem subd10_1_220 : subd10_1 [2, -4] = true := by decide +kernel
theorem subd10_1_221 : subd10_1 [2, -3] = true := by decide +kernel
theorem subd10_1_222 : subd10_1 [2, -2] = true := by decide +kernel
theorem subd10_1_223 : subd10_1 [2, -1] = true := by decide +kernel
theorem sbd10_1_6 : ∀ q ∈ blkd10_1_6, subd10_1 q = true := by
  unfold blkd10_1_6
  exact List.forall_mem_cons.2 ⟨subd10_1_192, List.forall_mem_cons.2 ⟨subd10_1_193, List.forall_mem_cons.2 ⟨subd10_1_194, List.forall_mem_cons.2 ⟨subd10_1_195, List.forall_mem_cons.2 ⟨subd10_1_196, List.forall_mem_cons.2 ⟨subd10_1_197, List.forall_mem_cons.2 ⟨subd10_1_198, List.forall_mem_cons.2 ⟨subd10_1_199, List.forall_mem_cons.2 ⟨subd10_1_200, List.forall_mem_cons.2 ⟨subd10_1_201, List.forall_mem_cons.2 ⟨subd10_1_202, List.forall_mem_cons.2 ⟨subd10_1_203, List.forall_mem_cons.2 ⟨subd10_1_204, List.forall_mem_cons.2 ⟨subd10_1_205, List.forall_mem_cons.2 ⟨subd10_1_206, List.forall_mem_cons.2 ⟨subd10_1_207, List.forall_mem_cons.2 ⟨subd10_1_208, List.forall_mem_cons.2 ⟨subd10_1_209, List.forall_mem_cons.2 ⟨subd10_1_210, List.forall_mem_cons.2 ⟨subd10_1_211, List.forall_mem_cons.2 ⟨subd10_1_212, List.forall_mem_cons.2 ⟨subd10_1_213, List.forall_mem_cons.2 ⟨subd10_1_214, List.forall_mem_cons.2 ⟨subd10_1_215, List.forall_mem_cons.2 ⟨subd10_1_216, List.forall_mem_cons.2 ⟨subd10_1_217, List.forall_mem_cons.2 ⟨subd10_1_218, List.forall_mem_cons.2 ⟨subd10_1_219, List.forall_mem_cons.2 ⟨subd10_1_220, List.forall_mem_cons.2 ⟨subd10_1_221, List.forall_mem_cons.2 ⟨subd10_1_222, List.forall_mem_cons.2 ⟨subd10_1_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C077
