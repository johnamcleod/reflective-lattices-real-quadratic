import ReflectZphi.Data.Cert5.C141.Base

namespace ReflectZphi.Data.Cert5.C141

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_0_96 : subd7_0 [-2, -2, 0] = true := by decide +kernel
theorem subd7_0_97 : subd7_0 [-2, -2, 1] = true := by decide +kernel
theorem subd7_0_98 : subd7_0 [-2, -2, 2] = true := by decide +kernel
theorem subd7_0_99 : subd7_0 [-2, -2, 3] = true := by decide +kernel
theorem subd7_0_100 : subd7_0 [-2, -2, 4] = true := by decide +kernel
theorem subd7_0_101 : subd7_0 [-2, -2, 5] = true := by decide +kernel
theorem subd7_0_102 : subd7_0 [-2, -2, 6] = true := by decide +kernel
theorem subd7_0_103 : subd7_0 [-2, -1, -7] = true := by decide +kernel
theorem subd7_0_104 : subd7_0 [-2, -1, -6] = true := by decide +kernel
theorem subd7_0_105 : subd7_0 [-2, -1, -5] = true := by decide +kernel
theorem subd7_0_106 : subd7_0 [-2, -1, -4] = true := by decide +kernel
theorem subd7_0_107 : subd7_0 [-2, -1, -3] = true := by decide +kernel
theorem subd7_0_108 : subd7_0 [-2, -1, -2] = true := by decide +kernel
theorem subd7_0_109 : subd7_0 [-2, -1, -1] = true := by decide +kernel
theorem subd7_0_110 : subd7_0 [-2, -1, 0] = true := by decide +kernel
theorem subd7_0_111 : subd7_0 [-2, -1, 1] = true := by decide +kernel
theorem subd7_0_112 : subd7_0 [-2, -1, 2] = true := by decide +kernel
theorem subd7_0_113 : subd7_0 [-2, -1, 3] = true := by decide +kernel
theorem subd7_0_114 : subd7_0 [-2, -1, 4] = true := by decide +kernel
theorem subd7_0_115 : subd7_0 [-2, -1, 5] = true := by decide +kernel
theorem subd7_0_116 : subd7_0 [-2, -1, 6] = true := by decide +kernel
theorem subd7_0_117 : subd7_0 [-2, -1, 7] = true := by decide +kernel
theorem subd7_0_118 : subd7_0 [-2, 0, -7] = true := by decide +kernel
theorem subd7_0_119 : subd7_0 [-2, 0, -6] = true := by decide +kernel
theorem subd7_0_120 : subd7_0 [-2, 0, -5] = true := by decide +kernel
theorem subd7_0_121 : subd7_0 [-2, 0, -4] = true := by decide +kernel
theorem subd7_0_122 : subd7_0 [-2, 0, -3] = true := by decide +kernel
theorem subd7_0_123 : subd7_0 [-2, 0, -2] = true := by decide +kernel
theorem subd7_0_124 : subd7_0 [-2, 0, -1] = true := by decide +kernel
theorem subd7_0_125 : subd7_0 [-2, 0, 0] = true := by decide +kernel
theorem subd7_0_126 : subd7_0 [-2, 0, 1] = true := by decide +kernel
theorem subd7_0_127 : subd7_0 [-2, 0, 2] = true := by decide +kernel
theorem sbd7_0_3 : ∀ q ∈ blkd7_0_3, subd7_0 q = true := by
  unfold blkd7_0_3
  exact List.forall_mem_cons.2 ⟨subd7_0_96, List.forall_mem_cons.2 ⟨subd7_0_97, List.forall_mem_cons.2 ⟨subd7_0_98, List.forall_mem_cons.2 ⟨subd7_0_99, List.forall_mem_cons.2 ⟨subd7_0_100, List.forall_mem_cons.2 ⟨subd7_0_101, List.forall_mem_cons.2 ⟨subd7_0_102, List.forall_mem_cons.2 ⟨subd7_0_103, List.forall_mem_cons.2 ⟨subd7_0_104, List.forall_mem_cons.2 ⟨subd7_0_105, List.forall_mem_cons.2 ⟨subd7_0_106, List.forall_mem_cons.2 ⟨subd7_0_107, List.forall_mem_cons.2 ⟨subd7_0_108, List.forall_mem_cons.2 ⟨subd7_0_109, List.forall_mem_cons.2 ⟨subd7_0_110, List.forall_mem_cons.2 ⟨subd7_0_111, List.forall_mem_cons.2 ⟨subd7_0_112, List.forall_mem_cons.2 ⟨subd7_0_113, List.forall_mem_cons.2 ⟨subd7_0_114, List.forall_mem_cons.2 ⟨subd7_0_115, List.forall_mem_cons.2 ⟨subd7_0_116, List.forall_mem_cons.2 ⟨subd7_0_117, List.forall_mem_cons.2 ⟨subd7_0_118, List.forall_mem_cons.2 ⟨subd7_0_119, List.forall_mem_cons.2 ⟨subd7_0_120, List.forall_mem_cons.2 ⟨subd7_0_121, List.forall_mem_cons.2 ⟨subd7_0_122, List.forall_mem_cons.2 ⟨subd7_0_123, List.forall_mem_cons.2 ⟨subd7_0_124, List.forall_mem_cons.2 ⟨subd7_0_125, List.forall_mem_cons.2 ⟨subd7_0_126, List.forall_mem_cons.2 ⟨subd7_0_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_128 : subd7_0 [-2, 0, 3] = true := by decide +kernel
theorem subd7_0_129 : subd7_0 [-2, 0, 4] = true := by decide +kernel
theorem subd7_0_130 : subd7_0 [-2, 0, 5] = true := by decide +kernel
theorem subd7_0_131 : subd7_0 [-2, 0, 6] = true := by decide +kernel
theorem subd7_0_132 : subd7_0 [-2, 0, 7] = true := by decide +kernel
theorem subd7_0_133 : subd7_0 [-2, 1, -6] = true := by decide +kernel
theorem subd7_0_134 : subd7_0 [-2, 1, -5] = true := by decide +kernel
theorem subd7_0_135 : subd7_0 [-2, 1, -4] = true := by decide +kernel
theorem subd7_0_136 : subd7_0 [-2, 1, -3] = true := by decide +kernel
theorem subd7_0_137 : subd7_0 [-2, 1, -2] = true := by decide +kernel
theorem subd7_0_138 : subd7_0 [-2, 1, -1] = true := by decide +kernel
theorem subd7_0_139 : subd7_0 [-2, 1, 0] = true := by decide +kernel
theorem subd7_0_140 : subd7_0 [-2, 1, 1] = true := by decide +kernel
theorem subd7_0_141 : subd7_0 [-2, 1, 2] = true := by decide +kernel
theorem subd7_0_142 : subd7_0 [-2, 1, 3] = true := by decide +kernel
theorem subd7_0_143 : subd7_0 [-2, 1, 4] = true := by decide +kernel
theorem subd7_0_144 : subd7_0 [-2, 1, 5] = true := by decide +kernel
theorem subd7_0_145 : subd7_0 [-2, 1, 6] = true := by decide +kernel
theorem subd7_0_146 : subd7_0 [-2, 1, 7] = true := by decide +kernel
theorem subd7_0_147 : subd7_0 [-2, 2, -5] = true := by decide +kernel
theorem subd7_0_148 : subd7_0 [-2, 2, -4] = true := by decide +kernel
theorem subd7_0_149 : subd7_0 [-2, 2, -3] = true := by decide +kernel
theorem subd7_0_150 : subd7_0 [-2, 2, -2] = true := by decide +kernel
theorem subd7_0_151 : subd7_0 [-2, 2, -1] = true := by decide +kernel
theorem subd7_0_152 : subd7_0 [-2, 2, 0] = true := by decide +kernel
theorem subd7_0_153 : subd7_0 [-2, 2, 1] = true := by decide +kernel
theorem subd7_0_154 : subd7_0 [-2, 2, 2] = true := by decide +kernel
theorem subd7_0_155 : subd7_0 [-2, 2, 3] = true := by decide +kernel
theorem subd7_0_156 : subd7_0 [-2, 2, 4] = true := by decide +kernel
theorem subd7_0_157 : subd7_0 [-2, 2, 5] = true := by decide +kernel
theorem subd7_0_158 : subd7_0 [-2, 2, 6] = true := by decide +kernel
theorem subd7_0_159 : subd7_0 [-2, 2, 7] = true := by decide +kernel
theorem sbd7_0_4 : ∀ q ∈ blkd7_0_4, subd7_0 q = true := by
  unfold blkd7_0_4
  exact List.forall_mem_cons.2 ⟨subd7_0_128, List.forall_mem_cons.2 ⟨subd7_0_129, List.forall_mem_cons.2 ⟨subd7_0_130, List.forall_mem_cons.2 ⟨subd7_0_131, List.forall_mem_cons.2 ⟨subd7_0_132, List.forall_mem_cons.2 ⟨subd7_0_133, List.forall_mem_cons.2 ⟨subd7_0_134, List.forall_mem_cons.2 ⟨subd7_0_135, List.forall_mem_cons.2 ⟨subd7_0_136, List.forall_mem_cons.2 ⟨subd7_0_137, List.forall_mem_cons.2 ⟨subd7_0_138, List.forall_mem_cons.2 ⟨subd7_0_139, List.forall_mem_cons.2 ⟨subd7_0_140, List.forall_mem_cons.2 ⟨subd7_0_141, List.forall_mem_cons.2 ⟨subd7_0_142, List.forall_mem_cons.2 ⟨subd7_0_143, List.forall_mem_cons.2 ⟨subd7_0_144, List.forall_mem_cons.2 ⟨subd7_0_145, List.forall_mem_cons.2 ⟨subd7_0_146, List.forall_mem_cons.2 ⟨subd7_0_147, List.forall_mem_cons.2 ⟨subd7_0_148, List.forall_mem_cons.2 ⟨subd7_0_149, List.forall_mem_cons.2 ⟨subd7_0_150, List.forall_mem_cons.2 ⟨subd7_0_151, List.forall_mem_cons.2 ⟨subd7_0_152, List.forall_mem_cons.2 ⟨subd7_0_153, List.forall_mem_cons.2 ⟨subd7_0_154, List.forall_mem_cons.2 ⟨subd7_0_155, List.forall_mem_cons.2 ⟨subd7_0_156, List.forall_mem_cons.2 ⟨subd7_0_157, List.forall_mem_cons.2 ⟨subd7_0_158, List.forall_mem_cons.2 ⟨subd7_0_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_160 : subd7_0 [-2, 3] = true := by decide +kernel
theorem subd7_0_161 : subd7_0 [-2, 4] = true := by decide +kernel
theorem subd7_0_162 : subd7_0 [-2, 5] = true := by decide +kernel
theorem subd7_0_163 : subd7_0 [-1, -7] = true := by decide +kernel
theorem subd7_0_164 : subd7_0 [-1, -6] = true := by decide +kernel
theorem subd7_0_165 : subd7_0 [-1, -5] = true := by decide +kernel
theorem subd7_0_166 : subd7_0 [-1, -4] = true := by decide +kernel
theorem subd7_0_167 : subd7_0 [-1, -3, -8] = true := by decide +kernel
theorem subd7_0_168 : subd7_0 [-1, -3, -7] = true := by decide +kernel
theorem subd7_0_169 : subd7_0 [-1, -3, -6] = true := by decide +kernel
theorem subd7_0_170 : subd7_0 [-1, -3, -5] = true := by decide +kernel
theorem subd7_0_171 : subd7_0 [-1, -3, -4] = true := by decide +kernel
theorem subd7_0_172 : subd7_0 [-1, -3, -3] = true := by decide +kernel
theorem subd7_0_173 : subd7_0 [-1, -3, -2] = true := by decide +kernel
theorem subd7_0_174 : subd7_0 [-1, -3, -1] = true := by decide +kernel
theorem subd7_0_175 : subd7_0 [-1, -3, 0] = true := by decide +kernel
theorem subd7_0_176 : subd7_0 [-1, -3, 1] = true := by decide +kernel
theorem subd7_0_177 : subd7_0 [-1, -3, 2] = true := by decide +kernel
theorem subd7_0_178 : subd7_0 [-1, -3, 3] = true := by decide +kernel
theorem subd7_0_179 : subd7_0 [-1, -3, 4] = true := by decide +kernel
theorem subd7_0_180 : subd7_0 [-1, -3, 5] = true := by decide +kernel
theorem subd7_0_181 : subd7_0 [-1, -2, -8] = true := by decide +kernel
theorem subd7_0_182 : subd7_0 [-1, -2, -7] = true := by decide +kernel
theorem subd7_0_183 : subd7_0 [-1, -2, -6] = true := by decide +kernel
theorem subd7_0_184 : subd7_0 [-1, -2, -5] = true := by decide +kernel
theorem subd7_0_185 : subd7_0 [-1, -2, -4] = true := by decide +kernel
theorem subd7_0_186 : subd7_0 [-1, -2, -3] = true := by decide +kernel
theorem subd7_0_187 : subd7_0 [-1, -2, -2] = true := by decide +kernel
theorem subd7_0_188 : subd7_0 [-1, -2, -1] = true := by decide +kernel
theorem subd7_0_189 : subd7_0 [-1, -2, 0] = true := by decide +kernel
theorem subd7_0_190 : subd7_0 [-1, -2, 1] = true := by decide +kernel
theorem subd7_0_191 : subd7_0 [-1, -2, 2] = true := by decide +kernel
theorem sbd7_0_5 : ∀ q ∈ blkd7_0_5, subd7_0 q = true := by
  unfold blkd7_0_5
  exact List.forall_mem_cons.2 ⟨subd7_0_160, List.forall_mem_cons.2 ⟨subd7_0_161, List.forall_mem_cons.2 ⟨subd7_0_162, List.forall_mem_cons.2 ⟨subd7_0_163, List.forall_mem_cons.2 ⟨subd7_0_164, List.forall_mem_cons.2 ⟨subd7_0_165, List.forall_mem_cons.2 ⟨subd7_0_166, List.forall_mem_cons.2 ⟨subd7_0_167, List.forall_mem_cons.2 ⟨subd7_0_168, List.forall_mem_cons.2 ⟨subd7_0_169, List.forall_mem_cons.2 ⟨subd7_0_170, List.forall_mem_cons.2 ⟨subd7_0_171, List.forall_mem_cons.2 ⟨subd7_0_172, List.forall_mem_cons.2 ⟨subd7_0_173, List.forall_mem_cons.2 ⟨subd7_0_174, List.forall_mem_cons.2 ⟨subd7_0_175, List.forall_mem_cons.2 ⟨subd7_0_176, List.forall_mem_cons.2 ⟨subd7_0_177, List.forall_mem_cons.2 ⟨subd7_0_178, List.forall_mem_cons.2 ⟨subd7_0_179, List.forall_mem_cons.2 ⟨subd7_0_180, List.forall_mem_cons.2 ⟨subd7_0_181, List.forall_mem_cons.2 ⟨subd7_0_182, List.forall_mem_cons.2 ⟨subd7_0_183, List.forall_mem_cons.2 ⟨subd7_0_184, List.forall_mem_cons.2 ⟨subd7_0_185, List.forall_mem_cons.2 ⟨subd7_0_186, List.forall_mem_cons.2 ⟨subd7_0_187, List.forall_mem_cons.2 ⟨subd7_0_188, List.forall_mem_cons.2 ⟨subd7_0_189, List.forall_mem_cons.2 ⟨subd7_0_190, List.forall_mem_cons.2 ⟨subd7_0_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_192 : subd7_0 [-1, -2, 3] = true := by decide +kernel
theorem subd7_0_193 : subd7_0 [-1, -2, 4] = true := by decide +kernel
theorem subd7_0_194 : subd7_0 [-1, -2, 5] = true := by decide +kernel
theorem subd7_0_195 : subd7_0 [-1, -2, 6] = true := by decide +kernel
theorem subd7_0_196 : subd7_0 [-1, -1, -8] = true := by decide +kernel
theorem subd7_0_197 : subd7_0 [-1, -1, -7] = true := by decide +kernel
theorem subd7_0_198 : subd7_0 [-1, -1, -6] = true := by decide +kernel
theorem subd7_0_199 : subd7_0 [-1, -1, -5] = true := by decide +kernel
theorem subd7_0_200 : subd7_0 [-1, -1, -4] = true := by decide +kernel
theorem subd7_0_201 : subd7_0 [-1, -1, -3] = true := by decide +kernel
theorem subd7_0_202 : subd7_0 [-1, -1, -2] = true := by decide +kernel
theorem subd7_0_203 : subd7_0 [-1, -1, -1] = true := by decide +kernel
theorem subd7_0_204 : subd7_0 [-1, -1, 0] = true := by decide +kernel
theorem subd7_0_205 : subd7_0 [-1, -1, 1] = true := by decide +kernel
theorem subd7_0_206 : subd7_0 [-1, -1, 2] = true := by decide +kernel
theorem subd7_0_207 : subd7_0 [-1, -1, 3] = true := by decide +kernel
theorem subd7_0_208 : subd7_0 [-1, -1, 4] = true := by decide +kernel
theorem subd7_0_209 : subd7_0 [-1, -1, 5] = true := by decide +kernel
theorem subd7_0_210 : subd7_0 [-1, -1, 6] = true := by decide +kernel
theorem subd7_0_211 : subd7_0 [-1, -1, 7] = true := by decide +kernel
theorem subd7_0_212 : subd7_0 [-1, 0, -7] = true := by decide +kernel
theorem subd7_0_213 : subd7_0 [-1, 0, -6] = true := by decide +kernel
theorem subd7_0_214 : subd7_0 [-1, 0, -5] = true := by decide +kernel
theorem subd7_0_215 : subd7_0 [-1, 0, -4] = true := by decide +kernel
theorem subd7_0_216 : subd7_0 [-1, 0, -3] = true := by decide +kernel
theorem subd7_0_217 : subd7_0 [-1, 0, -2] = true := by decide +kernel
theorem subd7_0_218 : subd7_0 [-1, 0, -1] = true := by decide +kernel
theorem subd7_0_219 : subd7_0 [-1, 0, 0] = true := by decide +kernel
theorem subd7_0_220 : subd7_0 [-1, 0, 1] = true := by decide +kernel
theorem subd7_0_221 : subd7_0 [-1, 0, 2] = true := by decide +kernel
theorem subd7_0_222 : subd7_0 [-1, 0, 3] = true := by decide +kernel
theorem subd7_0_223 : subd7_0 [-1, 0, 4] = true := by decide +kernel
theorem sbd7_0_6 : ∀ q ∈ blkd7_0_6, subd7_0 q = true := by
  unfold blkd7_0_6
  exact List.forall_mem_cons.2 ⟨subd7_0_192, List.forall_mem_cons.2 ⟨subd7_0_193, List.forall_mem_cons.2 ⟨subd7_0_194, List.forall_mem_cons.2 ⟨subd7_0_195, List.forall_mem_cons.2 ⟨subd7_0_196, List.forall_mem_cons.2 ⟨subd7_0_197, List.forall_mem_cons.2 ⟨subd7_0_198, List.forall_mem_cons.2 ⟨subd7_0_199, List.forall_mem_cons.2 ⟨subd7_0_200, List.forall_mem_cons.2 ⟨subd7_0_201, List.forall_mem_cons.2 ⟨subd7_0_202, List.forall_mem_cons.2 ⟨subd7_0_203, List.forall_mem_cons.2 ⟨subd7_0_204, List.forall_mem_cons.2 ⟨subd7_0_205, List.forall_mem_cons.2 ⟨subd7_0_206, List.forall_mem_cons.2 ⟨subd7_0_207, List.forall_mem_cons.2 ⟨subd7_0_208, List.forall_mem_cons.2 ⟨subd7_0_209, List.forall_mem_cons.2 ⟨subd7_0_210, List.forall_mem_cons.2 ⟨subd7_0_211, List.forall_mem_cons.2 ⟨subd7_0_212, List.forall_mem_cons.2 ⟨subd7_0_213, List.forall_mem_cons.2 ⟨subd7_0_214, List.forall_mem_cons.2 ⟨subd7_0_215, List.forall_mem_cons.2 ⟨subd7_0_216, List.forall_mem_cons.2 ⟨subd7_0_217, List.forall_mem_cons.2 ⟨subd7_0_218, List.forall_mem_cons.2 ⟨subd7_0_219, List.forall_mem_cons.2 ⟨subd7_0_220, List.forall_mem_cons.2 ⟨subd7_0_221, List.forall_mem_cons.2 ⟨subd7_0_222, List.forall_mem_cons.2 ⟨subd7_0_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_224 : subd7_0 [-1, 0, 5] = true := by decide +kernel
theorem subd7_0_225 : subd7_0 [-1, 0, 6] = true := by decide +kernel
theorem subd7_0_226 : subd7_0 [-1, 0, 7] = true := by decide +kernel
theorem subd7_0_227 : subd7_0 [-1, 1, -7] = true := by decide +kernel
theorem subd7_0_228 : subd7_0 [-1, 1, -6] = true := by decide +kernel
theorem subd7_0_229 : subd7_0 [-1, 1, -5] = true := by decide +kernel
theorem subd7_0_230 : subd7_0 [-1, 1, -4] = true := by decide +kernel
theorem subd7_0_231 : subd7_0 [-1, 1, -3] = true := by decide +kernel
theorem subd7_0_232 : subd7_0 [-1, 1, -2] = true := by decide +kernel
theorem subd7_0_233 : subd7_0 [-1, 1, -1] = true := by decide +kernel
theorem subd7_0_234 : subd7_0 [-1, 1, 0] = true := by decide +kernel
theorem subd7_0_235 : subd7_0 [-1, 1, 1] = true := by decide +kernel
theorem subd7_0_236 : subd7_0 [-1, 1, 2] = true := by decide +kernel
theorem subd7_0_237 : subd7_0 [-1, 1, 3] = true := by decide +kernel
theorem subd7_0_238 : subd7_0 [-1, 1, 4] = true := by decide +kernel
theorem subd7_0_239 : subd7_0 [-1, 1, 5] = true := by decide +kernel
theorem subd7_0_240 : subd7_0 [-1, 1, 6] = true := by decide +kernel
theorem subd7_0_241 : subd7_0 [-1, 1, 7] = true := by decide +kernel
theorem subd7_0_242 : subd7_0 [-1, 2, -6] = true := by decide +kernel
theorem subd7_0_243 : subd7_0 [-1, 2, -5] = true := by decide +kernel
theorem subd7_0_244 : subd7_0 [-1, 2, -4] = true := by decide +kernel
theorem subd7_0_245 : subd7_0 [-1, 2, -3] = true := by decide +kernel
theorem subd7_0_246 : subd7_0 [-1, 2, -2] = true := by decide +kernel
theorem subd7_0_247 : subd7_0 [-1, 2, -1] = true := by decide +kernel
theorem subd7_0_248 : subd7_0 [-1, 2, 0] = true := by decide +kernel
theorem subd7_0_249 : subd7_0 [-1, 2, 1] = true := by decide +kernel
theorem subd7_0_250 : subd7_0 [-1, 2, 2] = true := by decide +kernel
theorem subd7_0_251 : subd7_0 [-1, 2, 3] = true := by decide +kernel
theorem subd7_0_252 : subd7_0 [-1, 2, 4] = true := by decide +kernel
theorem subd7_0_253 : subd7_0 [-1, 2, 5] = true := by decide +kernel
theorem subd7_0_254 : subd7_0 [-1, 2, 6] = true := by decide +kernel
theorem subd7_0_255 : subd7_0 [-1, 2, 7] = true := by decide +kernel
theorem sbd7_0_7 : ∀ q ∈ blkd7_0_7, subd7_0 q = true := by
  unfold blkd7_0_7
  exact List.forall_mem_cons.2 ⟨subd7_0_224, List.forall_mem_cons.2 ⟨subd7_0_225, List.forall_mem_cons.2 ⟨subd7_0_226, List.forall_mem_cons.2 ⟨subd7_0_227, List.forall_mem_cons.2 ⟨subd7_0_228, List.forall_mem_cons.2 ⟨subd7_0_229, List.forall_mem_cons.2 ⟨subd7_0_230, List.forall_mem_cons.2 ⟨subd7_0_231, List.forall_mem_cons.2 ⟨subd7_0_232, List.forall_mem_cons.2 ⟨subd7_0_233, List.forall_mem_cons.2 ⟨subd7_0_234, List.forall_mem_cons.2 ⟨subd7_0_235, List.forall_mem_cons.2 ⟨subd7_0_236, List.forall_mem_cons.2 ⟨subd7_0_237, List.forall_mem_cons.2 ⟨subd7_0_238, List.forall_mem_cons.2 ⟨subd7_0_239, List.forall_mem_cons.2 ⟨subd7_0_240, List.forall_mem_cons.2 ⟨subd7_0_241, List.forall_mem_cons.2 ⟨subd7_0_242, List.forall_mem_cons.2 ⟨subd7_0_243, List.forall_mem_cons.2 ⟨subd7_0_244, List.forall_mem_cons.2 ⟨subd7_0_245, List.forall_mem_cons.2 ⟨subd7_0_246, List.forall_mem_cons.2 ⟨subd7_0_247, List.forall_mem_cons.2 ⟨subd7_0_248, List.forall_mem_cons.2 ⟨subd7_0_249, List.forall_mem_cons.2 ⟨subd7_0_250, List.forall_mem_cons.2 ⟨subd7_0_251, List.forall_mem_cons.2 ⟨subd7_0_252, List.forall_mem_cons.2 ⟨subd7_0_253, List.forall_mem_cons.2 ⟨subd7_0_254, List.forall_mem_cons.2 ⟨subd7_0_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_256 : subd7_0 [-1, 2, 8] = true := by decide +kernel
theorem subd7_0_257 : subd7_0 [-1, 3, -5] = true := by decide +kernel
theorem subd7_0_258 : subd7_0 [-1, 3, -4] = true := by decide +kernel
theorem subd7_0_259 : subd7_0 [-1, 3, -3] = true := by decide +kernel
theorem subd7_0_260 : subd7_0 [-1, 3, -2] = true := by decide +kernel
theorem subd7_0_261 : subd7_0 [-1, 3, -1] = true := by decide +kernel
theorem subd7_0_262 : subd7_0 [-1, 3, 0] = true := by decide +kernel
theorem subd7_0_263 : subd7_0 [-1, 3, 1] = true := by decide +kernel
theorem subd7_0_264 : subd7_0 [-1, 3, 2] = true := by decide +kernel
theorem subd7_0_265 : subd7_0 [-1, 3, 3] = true := by decide +kernel
theorem subd7_0_266 : subd7_0 [-1, 3, 4] = true := by decide +kernel
theorem subd7_0_267 : subd7_0 [-1, 3, 5] = true := by decide +kernel
theorem subd7_0_268 : subd7_0 [-1, 3, 6] = true := by decide +kernel
theorem subd7_0_269 : subd7_0 [-1, 3, 7] = true := by decide +kernel
theorem subd7_0_270 : subd7_0 [-1, 4] = true := by decide +kernel
theorem subd7_0_271 : subd7_0 [-1, 5] = true := by decide +kernel
theorem subd7_0_272 : subd7_0 [-1, 6] = true := by decide +kernel
theorem subd7_0_273 : subd7_0 [0, -7] = true := by decide +kernel
theorem subd7_0_274 : subd7_0 [0, -6] = true := by decide +kernel
theorem subd7_0_275 : subd7_0 [0, -5] = true := by decide +kernel
theorem subd7_0_276 : subd7_0 [0, -4] = true := by decide +kernel
theorem subd7_0_277 : subd7_0 [0, -3, -8] = true := by decide +kernel
theorem subd7_0_278 : subd7_0 [0, -3, -7] = true := by decide +kernel
theorem subd7_0_279 : subd7_0 [0, -3, -6] = true := by decide +kernel
theorem subd7_0_280 : subd7_0 [0, -3, -5] = true := by decide +kernel
theorem subd7_0_281 : subd7_0 [0, -3, -4] = true := by decide +kernel
theorem subd7_0_282 : subd7_0 [0, -3, -3] = true := by decide +kernel
theorem subd7_0_283 : subd7_0 [0, -3, -2] = true := by decide +kernel
theorem subd7_0_284 : subd7_0 [0, -3, -1] = true := by decide +kernel
theorem subd7_0_285 : subd7_0 [0, -3, 0] = true := by decide +kernel
theorem subd7_0_286 : subd7_0 [0, -3, 1] = true := by decide +kernel
theorem subd7_0_287 : subd7_0 [0, -3, 2] = true := by decide +kernel
theorem sbd7_0_8 : ∀ q ∈ blkd7_0_8, subd7_0 q = true := by
  unfold blkd7_0_8
  exact List.forall_mem_cons.2 ⟨subd7_0_256, List.forall_mem_cons.2 ⟨subd7_0_257, List.forall_mem_cons.2 ⟨subd7_0_258, List.forall_mem_cons.2 ⟨subd7_0_259, List.forall_mem_cons.2 ⟨subd7_0_260, List.forall_mem_cons.2 ⟨subd7_0_261, List.forall_mem_cons.2 ⟨subd7_0_262, List.forall_mem_cons.2 ⟨subd7_0_263, List.forall_mem_cons.2 ⟨subd7_0_264, List.forall_mem_cons.2 ⟨subd7_0_265, List.forall_mem_cons.2 ⟨subd7_0_266, List.forall_mem_cons.2 ⟨subd7_0_267, List.forall_mem_cons.2 ⟨subd7_0_268, List.forall_mem_cons.2 ⟨subd7_0_269, List.forall_mem_cons.2 ⟨subd7_0_270, List.forall_mem_cons.2 ⟨subd7_0_271, List.forall_mem_cons.2 ⟨subd7_0_272, List.forall_mem_cons.2 ⟨subd7_0_273, List.forall_mem_cons.2 ⟨subd7_0_274, List.forall_mem_cons.2 ⟨subd7_0_275, List.forall_mem_cons.2 ⟨subd7_0_276, List.forall_mem_cons.2 ⟨subd7_0_277, List.forall_mem_cons.2 ⟨subd7_0_278, List.forall_mem_cons.2 ⟨subd7_0_279, List.forall_mem_cons.2 ⟨subd7_0_280, List.forall_mem_cons.2 ⟨subd7_0_281, List.forall_mem_cons.2 ⟨subd7_0_282, List.forall_mem_cons.2 ⟨subd7_0_283, List.forall_mem_cons.2 ⟨subd7_0_284, List.forall_mem_cons.2 ⟨subd7_0_285, List.forall_mem_cons.2 ⟨subd7_0_286, List.forall_mem_cons.2 ⟨subd7_0_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_288 : subd7_0 [0, -3, 3] = true := by decide +kernel
theorem subd7_0_289 : subd7_0 [0, -3, 4] = true := by decide +kernel
theorem subd7_0_290 : subd7_0 [0, -3, 5] = true := by decide +kernel
theorem subd7_0_291 : subd7_0 [0, -2, -8] = true := by decide +kernel
theorem subd7_0_292 : subd7_0 [0, -2, -7] = true := by decide +kernel
theorem subd7_0_293 : subd7_0 [0, -2, -6] = true := by decide +kernel
theorem subd7_0_294 : subd7_0 [0, -2, -5] = true := by decide +kernel
theorem subd7_0_295 : subd7_0 [0, -2, -4] = true := by decide +kernel
theorem subd7_0_296 : subd7_0 [0, -2, -3] = true := by decide +kernel
theorem subd7_0_297 : subd7_0 [0, -2, -2] = true := by decide +kernel
theorem subd7_0_298 : subd7_0 [0, -2, -1] = true := by decide +kernel
theorem subd7_0_299 : subd7_0 [0, -2, 0] = true := by decide +kernel
theorem subd7_0_300 : subd7_0 [0, -2, 1] = true := by decide +kernel
theorem subd7_0_301 : subd7_0 [0, -2, 2] = true := by decide +kernel
theorem subd7_0_302 : subd7_0 [0, -2, 3] = true := by decide +kernel
theorem subd7_0_303 : subd7_0 [0, -2, 4] = true := by decide +kernel
theorem subd7_0_304 : subd7_0 [0, -2, 5] = true := by decide +kernel
theorem subd7_0_305 : subd7_0 [0, -2, 6] = true := by decide +kernel
theorem subd7_0_306 : subd7_0 [0, -1, -8] = true := by decide +kernel
theorem subd7_0_307 : subd7_0 [0, -1, -7] = true := by decide +kernel
theorem subd7_0_308 : subd7_0 [0, -1, -6] = true := by decide +kernel
theorem subd7_0_309 : subd7_0 [0, -1, -5] = true := by decide +kernel
theorem subd7_0_310 : subd7_0 [0, -1, -4] = true := by decide +kernel
theorem subd7_0_311 : subd7_0 [0, -1, -3] = true := by decide +kernel
theorem subd7_0_312 : subd7_0 [0, -1, -2] = true := by decide +kernel
theorem subd7_0_313 : subd7_0 [0, -1, -1] = true := by decide +kernel
theorem subd7_0_314 : subd7_0 [0, -1, 0] = true := by decide +kernel
theorem subd7_0_315 : subd7_0 [0, -1, 1] = true := by decide +kernel
theorem subd7_0_316 : subd7_0 [0, -1, 2] = true := by decide +kernel
theorem subd7_0_317 : subd7_0 [0, -1, 3] = true := by decide +kernel
theorem subd7_0_318 : subd7_0 [0, -1, 4] = true := by decide +kernel
theorem subd7_0_319 : subd7_0 [0, -1, 5] = true := by decide +kernel
theorem sbd7_0_9 : ∀ q ∈ blkd7_0_9, subd7_0 q = true := by
  unfold blkd7_0_9
  exact List.forall_mem_cons.2 ⟨subd7_0_288, List.forall_mem_cons.2 ⟨subd7_0_289, List.forall_mem_cons.2 ⟨subd7_0_290, List.forall_mem_cons.2 ⟨subd7_0_291, List.forall_mem_cons.2 ⟨subd7_0_292, List.forall_mem_cons.2 ⟨subd7_0_293, List.forall_mem_cons.2 ⟨subd7_0_294, List.forall_mem_cons.2 ⟨subd7_0_295, List.forall_mem_cons.2 ⟨subd7_0_296, List.forall_mem_cons.2 ⟨subd7_0_297, List.forall_mem_cons.2 ⟨subd7_0_298, List.forall_mem_cons.2 ⟨subd7_0_299, List.forall_mem_cons.2 ⟨subd7_0_300, List.forall_mem_cons.2 ⟨subd7_0_301, List.forall_mem_cons.2 ⟨subd7_0_302, List.forall_mem_cons.2 ⟨subd7_0_303, List.forall_mem_cons.2 ⟨subd7_0_304, List.forall_mem_cons.2 ⟨subd7_0_305, List.forall_mem_cons.2 ⟨subd7_0_306, List.forall_mem_cons.2 ⟨subd7_0_307, List.forall_mem_cons.2 ⟨subd7_0_308, List.forall_mem_cons.2 ⟨subd7_0_309, List.forall_mem_cons.2 ⟨subd7_0_310, List.forall_mem_cons.2 ⟨subd7_0_311, List.forall_mem_cons.2 ⟨subd7_0_312, List.forall_mem_cons.2 ⟨subd7_0_313, List.forall_mem_cons.2 ⟨subd7_0_314, List.forall_mem_cons.2 ⟨subd7_0_315, List.forall_mem_cons.2 ⟨subd7_0_316, List.forall_mem_cons.2 ⟨subd7_0_317, List.forall_mem_cons.2 ⟨subd7_0_318, List.forall_mem_cons.2 ⟨subd7_0_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_320 : subd7_0 [0, -1, 6] = true := by decide +kernel
theorem subd7_0_321 : subd7_0 [0, 0, -8] = true := by decide +kernel
theorem subd7_0_322 : subd7_0 [0, 0, -7] = true := by decide +kernel
theorem subd7_0_323 : subd7_0 [0, 0, -6] = true := by decide +kernel
theorem subd7_0_324 : subd7_0 [0, 0, -5] = true := by decide +kernel
theorem subd7_0_325 : subd7_0 [0, 0, -4] = true := by decide +kernel
theorem subd7_0_326 : subd7_0 [0, 0, -3] = true := by decide +kernel
theorem subd7_0_327 : subd7_0 [0, 0, -2] = true := by decide +kernel
theorem subd7_0_328 : subd7_0 [0, 0, -1] = true := by decide +kernel
theorem subd7_0_329 : subd7_0 [0, 0, 0] = true := by decide +kernel
theorem subd7_0_330 : subd7_0 [0, 0, 1] = true := by decide +kernel
theorem subd7_0_331 : subd7_0 [0, 0, 2] = true := by decide +kernel
theorem subd7_0_332 : subd7_0 [0, 0, 3] = true := by decide +kernel
theorem subd7_0_333 : subd7_0 [0, 0, 4] = true := by decide +kernel
theorem subd7_0_334 : subd7_0 [0, 0, 5] = true := by decide +kernel
theorem subd7_0_335 : subd7_0 [0, 0, 6] = true := by decide +kernel
theorem subd7_0_336 : subd7_0 [0, 0, 7] = true := by decide +kernel
theorem subd7_0_337 : subd7_0 [0, 1, -7] = true := by decide +kernel
theorem subd7_0_338 : subd7_0 [0, 1, -6] = true := by decide +kernel
theorem subd7_0_339 : subd7_0 [0, 1, -5] = true := by decide +kernel
theorem subd7_0_340 : subd7_0 [0, 1, -4] = true := by decide +kernel
theorem subd7_0_341 : subd7_0 [0, 1, -3] = true := by decide +kernel
theorem subd7_0_342 : subd7_0 [0, 1, -2] = true := by decide +kernel
theorem subd7_0_343 : subd7_0 [0, 1, -1] = true := by decide +kernel
theorem subd7_0_344 : subd7_0 [0, 1, 0] = true := by decide +kernel
theorem subd7_0_345 : subd7_0 [0, 1, 1] = true := by decide +kernel
theorem subd7_0_346 : subd7_0 [0, 1, 2] = true := by decide +kernel
theorem subd7_0_347 : subd7_0 [0, 1, 3] = true := by decide +kernel
theorem subd7_0_348 : subd7_0 [0, 1, 4] = true := by decide +kernel
theorem subd7_0_349 : subd7_0 [0, 1, 5] = true := by decide +kernel
theorem subd7_0_350 : subd7_0 [0, 1, 6] = true := by decide +kernel
theorem subd7_0_351 : subd7_0 [0, 1, 7] = true := by decide +kernel
theorem sbd7_0_10 : ∀ q ∈ blkd7_0_10, subd7_0 q = true := by
  unfold blkd7_0_10
  exact List.forall_mem_cons.2 ⟨subd7_0_320, List.forall_mem_cons.2 ⟨subd7_0_321, List.forall_mem_cons.2 ⟨subd7_0_322, List.forall_mem_cons.2 ⟨subd7_0_323, List.forall_mem_cons.2 ⟨subd7_0_324, List.forall_mem_cons.2 ⟨subd7_0_325, List.forall_mem_cons.2 ⟨subd7_0_326, List.forall_mem_cons.2 ⟨subd7_0_327, List.forall_mem_cons.2 ⟨subd7_0_328, List.forall_mem_cons.2 ⟨subd7_0_329, List.forall_mem_cons.2 ⟨subd7_0_330, List.forall_mem_cons.2 ⟨subd7_0_331, List.forall_mem_cons.2 ⟨subd7_0_332, List.forall_mem_cons.2 ⟨subd7_0_333, List.forall_mem_cons.2 ⟨subd7_0_334, List.forall_mem_cons.2 ⟨subd7_0_335, List.forall_mem_cons.2 ⟨subd7_0_336, List.forall_mem_cons.2 ⟨subd7_0_337, List.forall_mem_cons.2 ⟨subd7_0_338, List.forall_mem_cons.2 ⟨subd7_0_339, List.forall_mem_cons.2 ⟨subd7_0_340, List.forall_mem_cons.2 ⟨subd7_0_341, List.forall_mem_cons.2 ⟨subd7_0_342, List.forall_mem_cons.2 ⟨subd7_0_343, List.forall_mem_cons.2 ⟨subd7_0_344, List.forall_mem_cons.2 ⟨subd7_0_345, List.forall_mem_cons.2 ⟨subd7_0_346, List.forall_mem_cons.2 ⟨subd7_0_347, List.forall_mem_cons.2 ⟨subd7_0_348, List.forall_mem_cons.2 ⟨subd7_0_349, List.forall_mem_cons.2 ⟨subd7_0_350, List.forall_mem_cons.2 ⟨subd7_0_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_352 : subd7_0 [0, 2, -7] = true := by decide +kernel
theorem subd7_0_353 : subd7_0 [0, 2, -6] = true := by decide +kernel
theorem subd7_0_354 : subd7_0 [0, 2, -5] = true := by decide +kernel
theorem subd7_0_355 : subd7_0 [0, 2, -4] = true := by decide +kernel
theorem subd7_0_356 : subd7_0 [0, 2, -3] = true := by decide +kernel
theorem subd7_0_357 : subd7_0 [0, 2, -2] = true := by decide +kernel
theorem subd7_0_358 : subd7_0 [0, 2, -1] = true := by decide +kernel
theorem subd7_0_359 : subd7_0 [0, 2, 0] = true := by decide +kernel
theorem subd7_0_360 : subd7_0 [0, 2, 1] = true := by decide +kernel
theorem subd7_0_361 : subd7_0 [0, 2, 2] = true := by decide +kernel
theorem subd7_0_362 : subd7_0 [0, 2, 3] = true := by decide +kernel
theorem subd7_0_363 : subd7_0 [0, 2, 4] = true := by decide +kernel
theorem subd7_0_364 : subd7_0 [0, 2, 5] = true := by decide +kernel
theorem subd7_0_365 : subd7_0 [0, 2, 6] = true := by decide +kernel
theorem subd7_0_366 : subd7_0 [0, 2, 7] = true := by decide +kernel
theorem subd7_0_367 : subd7_0 [0, 3, -6] = true := by decide +kernel
theorem subd7_0_368 : subd7_0 [0, 3, -5] = true := by decide +kernel
theorem subd7_0_369 : subd7_0 [0, 3, -4] = true := by decide +kernel
theorem subd7_0_370 : subd7_0 [0, 3, -3] = true := by decide +kernel
theorem subd7_0_371 : subd7_0 [0, 3, -2] = true := by decide +kernel
theorem subd7_0_372 : subd7_0 [0, 3, -1] = true := by decide +kernel
theorem subd7_0_373 : subd7_0 [0, 3, 0] = true := by decide +kernel
theorem subd7_0_374 : subd7_0 [0, 3, 1] = true := by decide +kernel
theorem subd7_0_375 : subd7_0 [0, 3, 2] = true := by decide +kernel
theorem subd7_0_376 : subd7_0 [0, 3, 3] = true := by decide +kernel
theorem subd7_0_377 : subd7_0 [0, 3, 4] = true := by decide +kernel
theorem subd7_0_378 : subd7_0 [0, 3, 5] = true := by decide +kernel
theorem subd7_0_379 : subd7_0 [0, 3, 6] = true := by decide +kernel
theorem subd7_0_380 : subd7_0 [0, 3, 7] = true := by decide +kernel
theorem subd7_0_381 : subd7_0 [0, 4] = true := by decide +kernel
theorem subd7_0_382 : subd7_0 [0, 5] = true := by decide +kernel
theorem subd7_0_383 : subd7_0 [0, 6] = true := by decide +kernel
theorem sbd7_0_11 : ∀ q ∈ blkd7_0_11, subd7_0 q = true := by
  unfold blkd7_0_11
  exact List.forall_mem_cons.2 ⟨subd7_0_352, List.forall_mem_cons.2 ⟨subd7_0_353, List.forall_mem_cons.2 ⟨subd7_0_354, List.forall_mem_cons.2 ⟨subd7_0_355, List.forall_mem_cons.2 ⟨subd7_0_356, List.forall_mem_cons.2 ⟨subd7_0_357, List.forall_mem_cons.2 ⟨subd7_0_358, List.forall_mem_cons.2 ⟨subd7_0_359, List.forall_mem_cons.2 ⟨subd7_0_360, List.forall_mem_cons.2 ⟨subd7_0_361, List.forall_mem_cons.2 ⟨subd7_0_362, List.forall_mem_cons.2 ⟨subd7_0_363, List.forall_mem_cons.2 ⟨subd7_0_364, List.forall_mem_cons.2 ⟨subd7_0_365, List.forall_mem_cons.2 ⟨subd7_0_366, List.forall_mem_cons.2 ⟨subd7_0_367, List.forall_mem_cons.2 ⟨subd7_0_368, List.forall_mem_cons.2 ⟨subd7_0_369, List.forall_mem_cons.2 ⟨subd7_0_370, List.forall_mem_cons.2 ⟨subd7_0_371, List.forall_mem_cons.2 ⟨subd7_0_372, List.forall_mem_cons.2 ⟨subd7_0_373, List.forall_mem_cons.2 ⟨subd7_0_374, List.forall_mem_cons.2 ⟨subd7_0_375, List.forall_mem_cons.2 ⟨subd7_0_376, List.forall_mem_cons.2 ⟨subd7_0_377, List.forall_mem_cons.2 ⟨subd7_0_378, List.forall_mem_cons.2 ⟨subd7_0_379, List.forall_mem_cons.2 ⟨subd7_0_380, List.forall_mem_cons.2 ⟨subd7_0_381, List.forall_mem_cons.2 ⟨subd7_0_382, List.forall_mem_cons.2 ⟨subd7_0_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_384 : subd7_0 [1, -7] = true := by decide +kernel
theorem subd7_0_385 : subd7_0 [1, -6] = true := by decide +kernel
theorem subd7_0_386 : subd7_0 [1, -5] = true := by decide +kernel
theorem subd7_0_387 : subd7_0 [1, -4] = true := by decide +kernel
theorem subd7_0_388 : subd7_0 [1, -3, -8] = true := by decide +kernel
theorem subd7_0_389 : subd7_0 [1, -3, -7] = true := by decide +kernel
theorem subd7_0_390 : subd7_0 [1, -3, -6] = true := by decide +kernel
theorem subd7_0_391 : subd7_0 [1, -3, -5] = true := by decide +kernel
theorem subd7_0_392 : subd7_0 [1, -3, -4] = true := by decide +kernel
theorem subd7_0_393 : subd7_0 [1, -3, -3] = true := by decide +kernel
theorem subd7_0_394 : subd7_0 [1, -3, -2] = true := by decide +kernel
theorem subd7_0_395 : subd7_0 [1, -3, -1] = true := by decide +kernel
theorem subd7_0_396 : subd7_0 [1, -3, 0] = true := by decide +kernel
theorem subd7_0_397 : subd7_0 [1, -3, 1] = true := by decide +kernel
theorem subd7_0_398 : subd7_0 [1, -3, 2] = true := by decide +kernel
theorem subd7_0_399 : subd7_0 [1, -3, 3] = true := by decide +kernel
theorem subd7_0_400 : subd7_0 [1, -3, 4] = true := by decide +kernel
theorem subd7_0_401 : subd7_0 [1, -2, -9] = true := by decide +kernel
theorem subd7_0_402 : subd7_0 [1, -2, -8] = true := by decide +kernel
theorem subd7_0_403 : subd7_0 [1, -2, -7] = true := by decide +kernel
theorem subd7_0_404 : subd7_0 [1, -2, -6] = true := by decide +kernel
theorem subd7_0_405 : subd7_0 [1, -2, -5] = true := by decide +kernel
theorem subd7_0_406 : subd7_0 [1, -2, -4] = true := by decide +kernel
theorem subd7_0_407 : subd7_0 [1, -2, -3] = true := by decide +kernel
theorem subd7_0_408 : subd7_0 [1, -2, -2] = true := by decide +kernel
theorem subd7_0_409 : subd7_0 [1, -2, -1] = true := by decide +kernel
theorem subd7_0_410 : subd7_0 [1, -2, 0] = true := by decide +kernel
theorem subd7_0_411 : subd7_0 [1, -2, 1] = true := by decide +kernel
theorem subd7_0_412 : subd7_0 [1, -2, 2] = true := by decide +kernel
theorem subd7_0_413 : subd7_0 [1, -2, 3] = true := by decide +kernel
theorem subd7_0_414 : subd7_0 [1, -2, 4] = true := by decide +kernel
theorem subd7_0_415 : subd7_0 [1, -2, 5] = true := by decide +kernel
theorem sbd7_0_12 : ∀ q ∈ blkd7_0_12, subd7_0 q = true := by
  unfold blkd7_0_12
  exact List.forall_mem_cons.2 ⟨subd7_0_384, List.forall_mem_cons.2 ⟨subd7_0_385, List.forall_mem_cons.2 ⟨subd7_0_386, List.forall_mem_cons.2 ⟨subd7_0_387, List.forall_mem_cons.2 ⟨subd7_0_388, List.forall_mem_cons.2 ⟨subd7_0_389, List.forall_mem_cons.2 ⟨subd7_0_390, List.forall_mem_cons.2 ⟨subd7_0_391, List.forall_mem_cons.2 ⟨subd7_0_392, List.forall_mem_cons.2 ⟨subd7_0_393, List.forall_mem_cons.2 ⟨subd7_0_394, List.forall_mem_cons.2 ⟨subd7_0_395, List.forall_mem_cons.2 ⟨subd7_0_396, List.forall_mem_cons.2 ⟨subd7_0_397, List.forall_mem_cons.2 ⟨subd7_0_398, List.forall_mem_cons.2 ⟨subd7_0_399, List.forall_mem_cons.2 ⟨subd7_0_400, List.forall_mem_cons.2 ⟨subd7_0_401, List.forall_mem_cons.2 ⟨subd7_0_402, List.forall_mem_cons.2 ⟨subd7_0_403, List.forall_mem_cons.2 ⟨subd7_0_404, List.forall_mem_cons.2 ⟨subd7_0_405, List.forall_mem_cons.2 ⟨subd7_0_406, List.forall_mem_cons.2 ⟨subd7_0_407, List.forall_mem_cons.2 ⟨subd7_0_408, List.forall_mem_cons.2 ⟨subd7_0_409, List.forall_mem_cons.2 ⟨subd7_0_410, List.forall_mem_cons.2 ⟨subd7_0_411, List.forall_mem_cons.2 ⟨subd7_0_412, List.forall_mem_cons.2 ⟨subd7_0_413, List.forall_mem_cons.2 ⟨subd7_0_414, List.forall_mem_cons.2 ⟨subd7_0_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_416 : subd7_0 [1, -1, -8] = true := by decide +kernel
theorem subd7_0_417 : subd7_0 [1, -1, -7] = true := by decide +kernel
theorem subd7_0_418 : subd7_0 [1, -1, -6] = true := by decide +kernel
theorem subd7_0_419 : subd7_0 [1, -1, -5] = true := by decide +kernel
theorem subd7_0_420 : subd7_0 [1, -1, -4] = true := by decide +kernel
theorem subd7_0_421 : subd7_0 [1, -1, -3] = true := by decide +kernel
theorem subd7_0_422 : subd7_0 [1, -1, -2] = true := by decide +kernel
theorem subd7_0_423 : subd7_0 [1, -1, -1] = true := by decide +kernel
theorem subd7_0_424 : subd7_0 [1, -1, 0] = true := by decide +kernel
theorem subd7_0_425 : subd7_0 [1, -1, 1] = true := by decide +kernel
theorem subd7_0_426 : subd7_0 [1, -1, 2] = true := by decide +kernel
theorem subd7_0_427 : subd7_0 [1, -1, 3] = true := by decide +kernel
theorem subd7_0_428 : subd7_0 [1, -1, 4] = true := by decide +kernel
theorem subd7_0_429 : subd7_0 [1, -1, 5] = true := by decide +kernel
theorem subd7_0_430 : subd7_0 [1, -1, 6] = true := by decide +kernel
theorem subd7_0_431 : subd7_0 [1, 0, -8] = true := by decide +kernel
theorem subd7_0_432 : subd7_0 [1, 0, -7] = true := by decide +kernel
theorem subd7_0_433 : subd7_0 [1, 0, -6] = true := by decide +kernel
theorem subd7_0_434 : subd7_0 [1, 0, -5] = true := by decide +kernel
theorem subd7_0_435 : subd7_0 [1, 0, -4] = true := by decide +kernel
theorem subd7_0_436 : subd7_0 [1, 0, -3] = true := by decide +kernel
theorem subd7_0_437 : subd7_0 [1, 0, -2] = true := by decide +kernel
theorem subd7_0_438 : subd7_0 [1, 0, -1] = true := by decide +kernel
theorem subd7_0_439 : subd7_0 [1, 0, 0] = true := by decide +kernel
theorem subd7_0_440 : subd7_0 [1, 0, 1] = true := by decide +kernel
theorem subd7_0_441 : subd7_0 [1, 0, 2] = true := by decide +kernel
theorem subd7_0_442 : subd7_0 [1, 0, 3] = true := by decide +kernel
theorem subd7_0_443 : subd7_0 [1, 0, 4] = true := by decide +kernel
theorem subd7_0_444 : subd7_0 [1, 0, 5] = true := by decide +kernel
theorem subd7_0_445 : subd7_0 [1, 0, 6] = true := by decide +kernel
theorem subd7_0_446 : subd7_0 [1, 1, -8] = true := by decide +kernel
theorem subd7_0_447 : subd7_0 [1, 1, -7] = true := by decide +kernel
theorem sbd7_0_13 : ∀ q ∈ blkd7_0_13, subd7_0 q = true := by
  unfold blkd7_0_13
  exact List.forall_mem_cons.2 ⟨subd7_0_416, List.forall_mem_cons.2 ⟨subd7_0_417, List.forall_mem_cons.2 ⟨subd7_0_418, List.forall_mem_cons.2 ⟨subd7_0_419, List.forall_mem_cons.2 ⟨subd7_0_420, List.forall_mem_cons.2 ⟨subd7_0_421, List.forall_mem_cons.2 ⟨subd7_0_422, List.forall_mem_cons.2 ⟨subd7_0_423, List.forall_mem_cons.2 ⟨subd7_0_424, List.forall_mem_cons.2 ⟨subd7_0_425, List.forall_mem_cons.2 ⟨subd7_0_426, List.forall_mem_cons.2 ⟨subd7_0_427, List.forall_mem_cons.2 ⟨subd7_0_428, List.forall_mem_cons.2 ⟨subd7_0_429, List.forall_mem_cons.2 ⟨subd7_0_430, List.forall_mem_cons.2 ⟨subd7_0_431, List.forall_mem_cons.2 ⟨subd7_0_432, List.forall_mem_cons.2 ⟨subd7_0_433, List.forall_mem_cons.2 ⟨subd7_0_434, List.forall_mem_cons.2 ⟨subd7_0_435, List.forall_mem_cons.2 ⟨subd7_0_436, List.forall_mem_cons.2 ⟨subd7_0_437, List.forall_mem_cons.2 ⟨subd7_0_438, List.forall_mem_cons.2 ⟨subd7_0_439, List.forall_mem_cons.2 ⟨subd7_0_440, List.forall_mem_cons.2 ⟨subd7_0_441, List.forall_mem_cons.2 ⟨subd7_0_442, List.forall_mem_cons.2 ⟨subd7_0_443, List.forall_mem_cons.2 ⟨subd7_0_444, List.forall_mem_cons.2 ⟨subd7_0_445, List.forall_mem_cons.2 ⟨subd7_0_446, List.forall_mem_cons.2 ⟨subd7_0_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_448 : subd7_0 [1, 1, -6] = true := by decide +kernel
theorem subd7_0_449 : subd7_0 [1, 1, -5] = true := by decide +kernel
theorem subd7_0_450 : subd7_0 [1, 1, -4] = true := by decide +kernel
theorem subd7_0_451 : subd7_0 [1, 1, -3] = true := by decide +kernel
theorem subd7_0_452 : subd7_0 [1, 1, -2] = true := by decide +kernel
theorem subd7_0_453 : subd7_0 [1, 1, -1] = true := by decide +kernel
theorem subd7_0_454 : subd7_0 [1, 1, 0] = true := by decide +kernel
theorem subd7_0_455 : subd7_0 [1, 1, 1] = true := by decide +kernel
theorem subd7_0_456 : subd7_0 [1, 1, 2] = true := by decide +kernel
theorem subd7_0_457 : subd7_0 [1, 1, 3] = true := by decide +kernel
theorem subd7_0_458 : subd7_0 [1, 1, 4] = true := by decide +kernel
theorem subd7_0_459 : subd7_0 [1, 1, 5] = true := by decide +kernel
theorem subd7_0_460 : subd7_0 [1, 1, 6] = true := by decide +kernel
theorem subd7_0_461 : subd7_0 [1, 1, 7] = true := by decide +kernel
theorem subd7_0_462 : subd7_0 [1, 2, -7] = true := by decide +kernel
theorem subd7_0_463 : subd7_0 [1, 2, -6] = true := by decide +kernel
theorem subd7_0_464 : subd7_0 [1, 2, -5] = true := by decide +kernel
theorem subd7_0_465 : subd7_0 [1, 2, -4] = true := by decide +kernel
theorem subd7_0_466 : subd7_0 [1, 2, -3] = true := by decide +kernel
theorem subd7_0_467 : subd7_0 [1, 2, -2] = true := by decide +kernel
theorem subd7_0_468 : subd7_0 [1, 2, -1] = true := by decide +kernel
theorem subd7_0_469 : subd7_0 [1, 2, 0] = true := by decide +kernel
theorem subd7_0_470 : subd7_0 [1, 2, 1] = true := by decide +kernel
theorem subd7_0_471 : subd7_0 [1, 2, 2] = true := by decide +kernel
theorem subd7_0_472 : subd7_0 [1, 2, 3] = true := by decide +kernel
theorem subd7_0_473 : subd7_0 [1, 2, 4] = true := by decide +kernel
theorem subd7_0_474 : subd7_0 [1, 2, 5] = true := by decide +kernel
theorem subd7_0_475 : subd7_0 [1, 2, 6] = true := by decide +kernel
theorem subd7_0_476 : subd7_0 [1, 2, 7] = true := by decide +kernel
theorem subd7_0_477 : subd7_0 [1, 3, -6] = true := by decide +kernel
theorem subd7_0_478 : subd7_0 [1, 3, -5] = true := by decide +kernel
theorem subd7_0_479 : subd7_0 [1, 3, -4] = true := by decide +kernel
theorem sbd7_0_14 : ∀ q ∈ blkd7_0_14, subd7_0 q = true := by
  unfold blkd7_0_14
  exact List.forall_mem_cons.2 ⟨subd7_0_448, List.forall_mem_cons.2 ⟨subd7_0_449, List.forall_mem_cons.2 ⟨subd7_0_450, List.forall_mem_cons.2 ⟨subd7_0_451, List.forall_mem_cons.2 ⟨subd7_0_452, List.forall_mem_cons.2 ⟨subd7_0_453, List.forall_mem_cons.2 ⟨subd7_0_454, List.forall_mem_cons.2 ⟨subd7_0_455, List.forall_mem_cons.2 ⟨subd7_0_456, List.forall_mem_cons.2 ⟨subd7_0_457, List.forall_mem_cons.2 ⟨subd7_0_458, List.forall_mem_cons.2 ⟨subd7_0_459, List.forall_mem_cons.2 ⟨subd7_0_460, List.forall_mem_cons.2 ⟨subd7_0_461, List.forall_mem_cons.2 ⟨subd7_0_462, List.forall_mem_cons.2 ⟨subd7_0_463, List.forall_mem_cons.2 ⟨subd7_0_464, List.forall_mem_cons.2 ⟨subd7_0_465, List.forall_mem_cons.2 ⟨subd7_0_466, List.forall_mem_cons.2 ⟨subd7_0_467, List.forall_mem_cons.2 ⟨subd7_0_468, List.forall_mem_cons.2 ⟨subd7_0_469, List.forall_mem_cons.2 ⟨subd7_0_470, List.forall_mem_cons.2 ⟨subd7_0_471, List.forall_mem_cons.2 ⟨subd7_0_472, List.forall_mem_cons.2 ⟨subd7_0_473, List.forall_mem_cons.2 ⟨subd7_0_474, List.forall_mem_cons.2 ⟨subd7_0_475, List.forall_mem_cons.2 ⟨subd7_0_476, List.forall_mem_cons.2 ⟨subd7_0_477, List.forall_mem_cons.2 ⟨subd7_0_478, List.forall_mem_cons.2 ⟨subd7_0_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_480 : subd7_0 [1, 3, -3] = true := by decide +kernel
theorem subd7_0_481 : subd7_0 [1, 3, -2] = true := by decide +kernel
theorem subd7_0_482 : subd7_0 [1, 3, -1] = true := by decide +kernel
theorem subd7_0_483 : subd7_0 [1, 3, 0] = true := by decide +kernel
theorem subd7_0_484 : subd7_0 [1, 3, 1] = true := by decide +kernel
theorem subd7_0_485 : subd7_0 [1, 3, 2] = true := by decide +kernel
theorem subd7_0_486 : subd7_0 [1, 3, 3] = true := by decide +kernel
theorem subd7_0_487 : subd7_0 [1, 3, 4] = true := by decide +kernel
theorem subd7_0_488 : subd7_0 [1, 3, 5] = true := by decide +kernel
theorem subd7_0_489 : subd7_0 [1, 3, 6] = true := by decide +kernel
theorem subd7_0_490 : subd7_0 [1, 3, 7] = true := by decide +kernel
theorem subd7_0_491 : subd7_0 [1, 4] = true := by decide +kernel
theorem subd7_0_492 : subd7_0 [1, 5] = true := by decide +kernel
theorem subd7_0_493 : subd7_0 [1, 6] = true := by decide +kernel
theorem subd7_0_494 : subd7_0 [2, -6] = true := by decide +kernel
theorem subd7_0_495 : subd7_0 [2, -5] = true := by decide +kernel
theorem subd7_0_496 : subd7_0 [2, -4] = true := by decide +kernel
theorem subd7_0_497 : subd7_0 [2, -3] = true := by decide +kernel
theorem subd7_0_498 : subd7_0 [2, -2, -8] = true := by decide +kernel
theorem subd7_0_499 : subd7_0 [2, -2, -7] = true := by decide +kernel
theorem subd7_0_500 : subd7_0 [2, -2, -6] = true := by decide +kernel
theorem subd7_0_501 : subd7_0 [2, -2, -5] = true := by decide +kernel
theorem subd7_0_502 : subd7_0 [2, -2, -4] = true := by decide +kernel
theorem subd7_0_503 : subd7_0 [2, -2, -3] = true := by decide +kernel
theorem subd7_0_504 : subd7_0 [2, -2, -2] = true := by decide +kernel
theorem subd7_0_505 : subd7_0 [2, -2, -1] = true := by decide +kernel
theorem subd7_0_506 : subd7_0 [2, -2, 0] = true := by decide +kernel
theorem subd7_0_507 : subd7_0 [2, -2, 1] = true := by decide +kernel
theorem subd7_0_508 : subd7_0 [2, -2, 2] = true := by decide +kernel
theorem subd7_0_509 : subd7_0 [2, -2, 3] = true := by decide +kernel
theorem subd7_0_510 : subd7_0 [2, -2, 4] = true := by decide +kernel
theorem subd7_0_511 : subd7_0 [2, -1, -8] = true := by decide +kernel
theorem sbd7_0_15 : ∀ q ∈ blkd7_0_15, subd7_0 q = true := by
  unfold blkd7_0_15
  exact List.forall_mem_cons.2 ⟨subd7_0_480, List.forall_mem_cons.2 ⟨subd7_0_481, List.forall_mem_cons.2 ⟨subd7_0_482, List.forall_mem_cons.2 ⟨subd7_0_483, List.forall_mem_cons.2 ⟨subd7_0_484, List.forall_mem_cons.2 ⟨subd7_0_485, List.forall_mem_cons.2 ⟨subd7_0_486, List.forall_mem_cons.2 ⟨subd7_0_487, List.forall_mem_cons.2 ⟨subd7_0_488, List.forall_mem_cons.2 ⟨subd7_0_489, List.forall_mem_cons.2 ⟨subd7_0_490, List.forall_mem_cons.2 ⟨subd7_0_491, List.forall_mem_cons.2 ⟨subd7_0_492, List.forall_mem_cons.2 ⟨subd7_0_493, List.forall_mem_cons.2 ⟨subd7_0_494, List.forall_mem_cons.2 ⟨subd7_0_495, List.forall_mem_cons.2 ⟨subd7_0_496, List.forall_mem_cons.2 ⟨subd7_0_497, List.forall_mem_cons.2 ⟨subd7_0_498, List.forall_mem_cons.2 ⟨subd7_0_499, List.forall_mem_cons.2 ⟨subd7_0_500, List.forall_mem_cons.2 ⟨subd7_0_501, List.forall_mem_cons.2 ⟨subd7_0_502, List.forall_mem_cons.2 ⟨subd7_0_503, List.forall_mem_cons.2 ⟨subd7_0_504, List.forall_mem_cons.2 ⟨subd7_0_505, List.forall_mem_cons.2 ⟨subd7_0_506, List.forall_mem_cons.2 ⟨subd7_0_507, List.forall_mem_cons.2 ⟨subd7_0_508, List.forall_mem_cons.2 ⟨subd7_0_509, List.forall_mem_cons.2 ⟨subd7_0_510, List.forall_mem_cons.2 ⟨subd7_0_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_512 : subd7_0 [2, -1, -7] = true := by decide +kernel
theorem subd7_0_513 : subd7_0 [2, -1, -6] = true := by decide +kernel
theorem subd7_0_514 : subd7_0 [2, -1, -5] = true := by decide +kernel
theorem subd7_0_515 : subd7_0 [2, -1, -4] = true := by decide +kernel
theorem subd7_0_516 : subd7_0 [2, -1, -3] = true := by decide +kernel
theorem subd7_0_517 : subd7_0 [2, -1, -2] = true := by decide +kernel
theorem subd7_0_518 : subd7_0 [2, -1, -1] = true := by decide +kernel
theorem subd7_0_519 : subd7_0 [2, -1, 0] = true := by decide +kernel
theorem subd7_0_520 : subd7_0 [2, -1, 1] = true := by decide +kernel
theorem subd7_0_521 : subd7_0 [2, -1, 2] = true := by decide +kernel
theorem subd7_0_522 : subd7_0 [2, -1, 3] = true := by decide +kernel
theorem subd7_0_523 : subd7_0 [2, -1, 4] = true := by decide +kernel
theorem subd7_0_524 : subd7_0 [2, -1, 5] = true := by decide +kernel
theorem subd7_0_525 : subd7_0 [2, 0, -8] = true := by decide +kernel
theorem subd7_0_526 : subd7_0 [2, 0, -7] = true := by decide +kernel
theorem subd7_0_527 : subd7_0 [2, 0, -6] = true := by decide +kernel
theorem subd7_0_528 : subd7_0 [2, 0, -5] = true := by decide +kernel
theorem subd7_0_529 : subd7_0 [2, 0, -4] = true := by decide +kernel
theorem subd7_0_530 : subd7_0 [2, 0, -3] = true := by decide +kernel
theorem subd7_0_531 : subd7_0 [2, 0, -2] = true := by decide +kernel
theorem subd7_0_532 : subd7_0 [2, 0, -1] = true := by decide +kernel
theorem subd7_0_533 : subd7_0 [2, 0, 0] = true := by decide +kernel
theorem subd7_0_534 : subd7_0 [2, 0, 1] = true := by decide +kernel
theorem subd7_0_535 : subd7_0 [2, 0, 2] = true := by decide +kernel
theorem subd7_0_536 : subd7_0 [2, 0, 3] = true := by decide +kernel
theorem subd7_0_537 : subd7_0 [2, 0, 4] = true := by decide +kernel
theorem subd7_0_538 : subd7_0 [2, 0, 5] = true := by decide +kernel
theorem subd7_0_539 : subd7_0 [2, 0, 6] = true := by decide +kernel
theorem subd7_0_540 : subd7_0 [2, 1, -8] = true := by decide +kernel
theorem subd7_0_541 : subd7_0 [2, 1, -7] = true := by decide +kernel
theorem subd7_0_542 : subd7_0 [2, 1, -6] = true := by decide +kernel
theorem subd7_0_543 : subd7_0 [2, 1, -5] = true := by decide +kernel
theorem sbd7_0_16 : ∀ q ∈ blkd7_0_16, subd7_0 q = true := by
  unfold blkd7_0_16
  exact List.forall_mem_cons.2 ⟨subd7_0_512, List.forall_mem_cons.2 ⟨subd7_0_513, List.forall_mem_cons.2 ⟨subd7_0_514, List.forall_mem_cons.2 ⟨subd7_0_515, List.forall_mem_cons.2 ⟨subd7_0_516, List.forall_mem_cons.2 ⟨subd7_0_517, List.forall_mem_cons.2 ⟨subd7_0_518, List.forall_mem_cons.2 ⟨subd7_0_519, List.forall_mem_cons.2 ⟨subd7_0_520, List.forall_mem_cons.2 ⟨subd7_0_521, List.forall_mem_cons.2 ⟨subd7_0_522, List.forall_mem_cons.2 ⟨subd7_0_523, List.forall_mem_cons.2 ⟨subd7_0_524, List.forall_mem_cons.2 ⟨subd7_0_525, List.forall_mem_cons.2 ⟨subd7_0_526, List.forall_mem_cons.2 ⟨subd7_0_527, List.forall_mem_cons.2 ⟨subd7_0_528, List.forall_mem_cons.2 ⟨subd7_0_529, List.forall_mem_cons.2 ⟨subd7_0_530, List.forall_mem_cons.2 ⟨subd7_0_531, List.forall_mem_cons.2 ⟨subd7_0_532, List.forall_mem_cons.2 ⟨subd7_0_533, List.forall_mem_cons.2 ⟨subd7_0_534, List.forall_mem_cons.2 ⟨subd7_0_535, List.forall_mem_cons.2 ⟨subd7_0_536, List.forall_mem_cons.2 ⟨subd7_0_537, List.forall_mem_cons.2 ⟨subd7_0_538, List.forall_mem_cons.2 ⟨subd7_0_539, List.forall_mem_cons.2 ⟨subd7_0_540, List.forall_mem_cons.2 ⟨subd7_0_541, List.forall_mem_cons.2 ⟨subd7_0_542, List.forall_mem_cons.2 ⟨subd7_0_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C141
