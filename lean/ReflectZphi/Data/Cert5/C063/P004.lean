import ReflectZphi.Data.Cert5.C063.Base

namespace ReflectZphi.Data.Cert5.C063
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub4_96 : sub4 [-2, 1, -3] = true := by decide +kernel
theorem sub4_97 : sub4 [-2, 1, -2] = true := by decide +kernel
theorem sub4_98 : sub4 [-2, 1, -1] = true := by decide +kernel
theorem sub4_99 : sub4 [-2, 1, 0] = true := by decide +kernel
theorem sub4_100 : sub4 [-2, 1, 1] = true := by decide +kernel
theorem sub4_101 : sub4 [-2, 1, 2] = true := by decide +kernel
theorem sub4_102 : sub4 [-2, 1, 3] = true := by decide +kernel
theorem sub4_103 : sub4 [-2, 1, 4] = true := by decide +kernel
theorem sub4_104 : sub4 [-2, 1, 5] = true := by decide +kernel
theorem sub4_105 : sub4 [-2, 1, 6] = true := by decide +kernel
theorem sub4_106 : sub4 [-2, 1, 7] = true := by decide +kernel
theorem sub4_107 : sub4 [-2, 2, -8] = true := by decide +kernel
theorem sub4_108 : sub4 [-2, 2, -7] = true := by decide +kernel
theorem sub4_109 : sub4 [-2, 2, -6] = true := by decide +kernel
theorem sub4_110 : sub4 [-2, 2, -5] = true := by decide +kernel
theorem sub4_111 : sub4 [-2, 2, -4] = true := by decide +kernel
theorem sub4_112 : sub4 [-2, 2, -3] = true := by decide +kernel
theorem sub4_113 : sub4 [-2, 2, -2] = true := by decide +kernel
theorem sub4_114 : sub4 [-2, 2, -1] = true := by decide +kernel
theorem sub4_115 : sub4 [-2, 2, 0] = true := by decide +kernel
theorem sub4_116 : sub4 [-2, 2, 1] = true := by decide +kernel
theorem sub4_117 : sub4 [-2, 2, 2] = true := by decide +kernel
theorem sub4_118 : sub4 [-2, 2, 3] = true := by decide +kernel
theorem sub4_119 : sub4 [-2, 2, 4] = true := by decide +kernel
theorem sub4_120 : sub4 [-2, 2, 5] = true := by decide +kernel
theorem sub4_121 : sub4 [-2, 2, 6] = true := by decide +kernel
theorem sub4_122 : sub4 [-2, 2, 7] = true := by decide +kernel
theorem sub4_123 : sub4 [-2, 3] = true := by decide +kernel
theorem sub4_124 : sub4 [-2, 4] = true := by decide +kernel
theorem sub4_125 : sub4 [-2, 5] = true := by decide +kernel
theorem sub4_126 : sub4 [-2, 6] = true := by decide +kernel
theorem sub4_127 : sub4 [-1, -6] = true := by decide +kernel
theorem sb4_3 : ∀ q ∈ blk4_3, sub4 q = true := by
  unfold blk4_3
  exact List.forall_mem_cons.2 ⟨sub4_96, List.forall_mem_cons.2 ⟨sub4_97, List.forall_mem_cons.2 ⟨sub4_98, List.forall_mem_cons.2 ⟨sub4_99, List.forall_mem_cons.2 ⟨sub4_100, List.forall_mem_cons.2 ⟨sub4_101, List.forall_mem_cons.2 ⟨sub4_102, List.forall_mem_cons.2 ⟨sub4_103, List.forall_mem_cons.2 ⟨sub4_104, List.forall_mem_cons.2 ⟨sub4_105, List.forall_mem_cons.2 ⟨sub4_106, List.forall_mem_cons.2 ⟨sub4_107, List.forall_mem_cons.2 ⟨sub4_108, List.forall_mem_cons.2 ⟨sub4_109, List.forall_mem_cons.2 ⟨sub4_110, List.forall_mem_cons.2 ⟨sub4_111, List.forall_mem_cons.2 ⟨sub4_112, List.forall_mem_cons.2 ⟨sub4_113, List.forall_mem_cons.2 ⟨sub4_114, List.forall_mem_cons.2 ⟨sub4_115, List.forall_mem_cons.2 ⟨sub4_116, List.forall_mem_cons.2 ⟨sub4_117, List.forall_mem_cons.2 ⟨sub4_118, List.forall_mem_cons.2 ⟨sub4_119, List.forall_mem_cons.2 ⟨sub4_120, List.forall_mem_cons.2 ⟨sub4_121, List.forall_mem_cons.2 ⟨sub4_122, List.forall_mem_cons.2 ⟨sub4_123, List.forall_mem_cons.2 ⟨sub4_124, List.forall_mem_cons.2 ⟨sub4_125, List.forall_mem_cons.2 ⟨sub4_126, List.forall_mem_cons.2 ⟨sub4_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_128 : sub4 [-1, -5] = true := by decide +kernel
theorem sub4_129 : sub4 [-1, -4] = true := by decide +kernel
theorem sub4_130 : sub4 [-1, -3] = true := by decide +kernel
theorem sub4_131 : sub4 [-1, -2] = true := by decide +kernel
theorem sub4_132 : sub4 [-1, -1, -8] = true := by decide +kernel
theorem sub4_133 : sub4 [-1, -1, -7] = true := by decide +kernel
theorem sub4_134 : sub4 [-1, -1, -6] = true := by decide +kernel
theorem sub4_135 : sub4 [-1, -1, -5] = true := by decide +kernel
theorem sub4_136 : sub4 [-1, -1, -4] = true := by decide +kernel
theorem sub4_137 : sub4 [-1, -1, -3] = true := by decide +kernel
theorem sub4_138 : sub4 [-1, -1, -2] = true := by decide +kernel
theorem sub4_139 : sub4 [-1, -1, -1] = true := by decide +kernel
theorem sub4_140 : sub4 [-1, -1, 0] = true := by decide +kernel
theorem sub4_141 : sub4 [-1, -1, 1] = true := by decide +kernel
theorem sub4_142 : sub4 [-1, -1, 2] = true := by decide +kernel
theorem sub4_143 : sub4 [-1, -1, 3] = true := by decide +kernel
theorem sub4_144 : sub4 [-1, -1, 4] = true := by decide +kernel
theorem sub4_145 : sub4 [-1, -1, 5] = true := by decide +kernel
theorem sub4_146 : sub4 [-1, -1, 6] = true := by decide +kernel
theorem sub4_147 : sub4 [-1, -1, 7] = true := by decide +kernel
theorem sub4_148 : sub4 [-1, 0, -9] = true := by decide +kernel
theorem sub4_149 : sub4 [-1, 0, -8] = true := by decide +kernel
theorem sub4_150 : sub4 [-1, 0, -7] = true := by decide +kernel
theorem sub4_151 : sub4 [-1, 0, -6] = true := by decide +kernel
theorem sub4_152 : sub4 [-1, 0, -5] = true := by decide +kernel
theorem sub4_153 : sub4 [-1, 0, -4] = true := by decide +kernel
theorem sub4_154 : sub4 [-1, 0, -3] = true := by decide +kernel
theorem sub4_155 : sub4 [-1, 0, -2] = true := by decide +kernel
theorem sub4_156 : sub4 [-1, 0, -1] = true := by decide +kernel
theorem sub4_157 : sub4 [-1, 0, 0] = true := by decide +kernel
theorem sub4_158 : sub4 [-1, 0, 1] = true := by decide +kernel
theorem sub4_159 : sub4 [-1, 0, 2] = true := by decide +kernel
theorem sb4_4 : ∀ q ∈ blk4_4, sub4 q = true := by
  unfold blk4_4
  exact List.forall_mem_cons.2 ⟨sub4_128, List.forall_mem_cons.2 ⟨sub4_129, List.forall_mem_cons.2 ⟨sub4_130, List.forall_mem_cons.2 ⟨sub4_131, List.forall_mem_cons.2 ⟨sub4_132, List.forall_mem_cons.2 ⟨sub4_133, List.forall_mem_cons.2 ⟨sub4_134, List.forall_mem_cons.2 ⟨sub4_135, List.forall_mem_cons.2 ⟨sub4_136, List.forall_mem_cons.2 ⟨sub4_137, List.forall_mem_cons.2 ⟨sub4_138, List.forall_mem_cons.2 ⟨sub4_139, List.forall_mem_cons.2 ⟨sub4_140, List.forall_mem_cons.2 ⟨sub4_141, List.forall_mem_cons.2 ⟨sub4_142, List.forall_mem_cons.2 ⟨sub4_143, List.forall_mem_cons.2 ⟨sub4_144, List.forall_mem_cons.2 ⟨sub4_145, List.forall_mem_cons.2 ⟨sub4_146, List.forall_mem_cons.2 ⟨sub4_147, List.forall_mem_cons.2 ⟨sub4_148, List.forall_mem_cons.2 ⟨sub4_149, List.forall_mem_cons.2 ⟨sub4_150, List.forall_mem_cons.2 ⟨sub4_151, List.forall_mem_cons.2 ⟨sub4_152, List.forall_mem_cons.2 ⟨sub4_153, List.forall_mem_cons.2 ⟨sub4_154, List.forall_mem_cons.2 ⟨sub4_155, List.forall_mem_cons.2 ⟨sub4_156, List.forall_mem_cons.2 ⟨sub4_157, List.forall_mem_cons.2 ⟨sub4_158, List.forall_mem_cons.2 ⟨sub4_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_160 : sub4 [-1, 0, 3] = true := by decide +kernel
theorem sub4_161 : sub4 [-1, 0, 4] = true := by decide +kernel
theorem sub4_162 : sub4 [-1, 0, 5] = true := by decide +kernel
theorem sub4_163 : sub4 [-1, 0, 6] = true := by decide +kernel
theorem sub4_164 : sub4 [-1, 0, 7] = true := by decide +kernel
theorem sub4_165 : sub4 [-1, 1, -8] = true := by decide +kernel
theorem sub4_166 : sub4 [-1, 1, -7] = true := by decide +kernel
theorem sub4_167 : sub4 [-1, 1, -6] = true := by decide +kernel
theorem sub4_168 : sub4 [-1, 1, -5] = true := by decide +kernel
theorem sub4_169 : sub4 [-1, 1, -4] = true := by decide +kernel
theorem sub4_170 : sub4 [-1, 1, -3] = true := by decide +kernel
theorem sub4_171 : sub4 [-1, 1, -2] = true := by decide +kernel
theorem sub4_172 : sub4 [-1, 1, -1] = true := by decide +kernel
theorem sub4_173 : sub4 [-1, 1, 0] = true := by decide +kernel
theorem sub4_174 : sub4 [-1, 1, 1] = true := by decide +kernel
theorem sub4_175 : sub4 [-1, 1, 2] = true := by decide +kernel
theorem sub4_176 : sub4 [-1, 1, 3] = true := by decide +kernel
theorem sub4_177 : sub4 [-1, 1, 4] = true := by decide +kernel
theorem sub4_178 : sub4 [-1, 1, 5] = true := by decide +kernel
theorem sub4_179 : sub4 [-1, 1, 6] = true := by decide +kernel
theorem sub4_180 : sub4 [-1, 1, 7] = true := by decide +kernel
theorem sub4_181 : sub4 [-1, 2, -8] = true := by decide +kernel
theorem sub4_182 : sub4 [-1, 2, -7] = true := by decide +kernel
theorem sub4_183 : sub4 [-1, 2, -6] = true := by decide +kernel
theorem sub4_184 : sub4 [-1, 2, -5] = true := by decide +kernel
theorem sub4_185 : sub4 [-1, 2, -4] = true := by decide +kernel
theorem sub4_186 : sub4 [-1, 2, -3] = true := by decide +kernel
theorem sub4_187 : sub4 [-1, 2, -2] = true := by decide +kernel
theorem sub4_188 : sub4 [-1, 2, -1] = true := by decide +kernel
theorem sub4_189 : sub4 [-1, 2, 0] = true := by decide +kernel
theorem sub4_190 : sub4 [-1, 2, 1] = true := by decide +kernel
theorem sub4_191 : sub4 [-1, 2, 2] = true := by decide +kernel
theorem sb4_5 : ∀ q ∈ blk4_5, sub4 q = true := by
  unfold blk4_5
  exact List.forall_mem_cons.2 ⟨sub4_160, List.forall_mem_cons.2 ⟨sub4_161, List.forall_mem_cons.2 ⟨sub4_162, List.forall_mem_cons.2 ⟨sub4_163, List.forall_mem_cons.2 ⟨sub4_164, List.forall_mem_cons.2 ⟨sub4_165, List.forall_mem_cons.2 ⟨sub4_166, List.forall_mem_cons.2 ⟨sub4_167, List.forall_mem_cons.2 ⟨sub4_168, List.forall_mem_cons.2 ⟨sub4_169, List.forall_mem_cons.2 ⟨sub4_170, List.forall_mem_cons.2 ⟨sub4_171, List.forall_mem_cons.2 ⟨sub4_172, List.forall_mem_cons.2 ⟨sub4_173, List.forall_mem_cons.2 ⟨sub4_174, List.forall_mem_cons.2 ⟨sub4_175, List.forall_mem_cons.2 ⟨sub4_176, List.forall_mem_cons.2 ⟨sub4_177, List.forall_mem_cons.2 ⟨sub4_178, List.forall_mem_cons.2 ⟨sub4_179, List.forall_mem_cons.2 ⟨sub4_180, List.forall_mem_cons.2 ⟨sub4_181, List.forall_mem_cons.2 ⟨sub4_182, List.forall_mem_cons.2 ⟨sub4_183, List.forall_mem_cons.2 ⟨sub4_184, List.forall_mem_cons.2 ⟨sub4_185, List.forall_mem_cons.2 ⟨sub4_186, List.forall_mem_cons.2 ⟨sub4_187, List.forall_mem_cons.2 ⟨sub4_188, List.forall_mem_cons.2 ⟨sub4_189, List.forall_mem_cons.2 ⟨sub4_190, List.forall_mem_cons.2 ⟨sub4_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_192 : sub4 [-1, 2, 3] = true := by decide +kernel
theorem sub4_193 : sub4 [-1, 2, 4] = true := by decide +kernel
theorem sub4_194 : sub4 [-1, 2, 5] = true := by decide +kernel
theorem sub4_195 : sub4 [-1, 2, 6] = true := by decide +kernel
theorem sub4_196 : sub4 [-1, 2, 7] = true := by decide +kernel
theorem sub4_197 : sub4 [-1, 3] = true := by decide +kernel
theorem sub4_198 : sub4 [-1, 4] = true := by decide +kernel
theorem sub4_199 : sub4 [-1, 5] = true := by decide +kernel
theorem sub4_200 : sub4 [-1, 6] = true := by decide +kernel
theorem sub4_201 : sub4 [0, -6] = true := by decide +kernel
theorem sub4_202 : sub4 [0, -5] = true := by decide +kernel
theorem sub4_203 : sub4 [0, -4] = true := by decide +kernel
theorem sub4_204 : sub4 [0, -3] = true := by decide +kernel
theorem sub4_205 : sub4 [0, -2, -8] = true := by decide +kernel
theorem sub4_206 : sub4 [0, -2, -7] = true := by decide +kernel
theorem sub4_207 : sub4 [0, -2, -6] = true := by decide +kernel
theorem sub4_208 : sub4 [0, -2, -5] = true := by decide +kernel
theorem sub4_209 : sub4 [0, -2, -4] = true := by decide +kernel
theorem sub4_210 : sub4 [0, -2, -3] = true := by decide +kernel
theorem sub4_211 : sub4 [0, -2, -2] = true := by decide +kernel
theorem sub4_212 : sub4 [0, -2, -1] = true := by decide +kernel
theorem sub4_213 : sub4 [0, -2, 0] = true := by decide +kernel
theorem sub4_214 : sub4 [0, -2, 1] = true := by decide +kernel
theorem sub4_215 : sub4 [0, -2, 2] = true := by decide +kernel
theorem sub4_216 : sub4 [0, -2, 3] = true := by decide +kernel
theorem sub4_217 : sub4 [0, -2, 4] = true := by decide +kernel
theorem sub4_218 : sub4 [0, -2, 5] = true := by decide +kernel
theorem sub4_219 : sub4 [0, -2, 6] = true := by decide +kernel
theorem sub4_220 : sub4 [0, -2, 7] = true := by decide +kernel
theorem sub4_221 : sub4 [0, -1, -8] = true := by decide +kernel
theorem sub4_222 : sub4 [0, -1, -7] = true := by decide +kernel
theorem sub4_223 : sub4 [0, -1, -6] = true := by decide +kernel
theorem sb4_6 : ∀ q ∈ blk4_6, sub4 q = true := by
  unfold blk4_6
  exact List.forall_mem_cons.2 ⟨sub4_192, List.forall_mem_cons.2 ⟨sub4_193, List.forall_mem_cons.2 ⟨sub4_194, List.forall_mem_cons.2 ⟨sub4_195, List.forall_mem_cons.2 ⟨sub4_196, List.forall_mem_cons.2 ⟨sub4_197, List.forall_mem_cons.2 ⟨sub4_198, List.forall_mem_cons.2 ⟨sub4_199, List.forall_mem_cons.2 ⟨sub4_200, List.forall_mem_cons.2 ⟨sub4_201, List.forall_mem_cons.2 ⟨sub4_202, List.forall_mem_cons.2 ⟨sub4_203, List.forall_mem_cons.2 ⟨sub4_204, List.forall_mem_cons.2 ⟨sub4_205, List.forall_mem_cons.2 ⟨sub4_206, List.forall_mem_cons.2 ⟨sub4_207, List.forall_mem_cons.2 ⟨sub4_208, List.forall_mem_cons.2 ⟨sub4_209, List.forall_mem_cons.2 ⟨sub4_210, List.forall_mem_cons.2 ⟨sub4_211, List.forall_mem_cons.2 ⟨sub4_212, List.forall_mem_cons.2 ⟨sub4_213, List.forall_mem_cons.2 ⟨sub4_214, List.forall_mem_cons.2 ⟨sub4_215, List.forall_mem_cons.2 ⟨sub4_216, List.forall_mem_cons.2 ⟨sub4_217, List.forall_mem_cons.2 ⟨sub4_218, List.forall_mem_cons.2 ⟨sub4_219, List.forall_mem_cons.2 ⟨sub4_220, List.forall_mem_cons.2 ⟨sub4_221, List.forall_mem_cons.2 ⟨sub4_222, List.forall_mem_cons.2 ⟨sub4_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_224 : sub4 [0, -1, -5] = true := by decide +kernel
theorem sub4_225 : sub4 [0, -1, -4] = true := by decide +kernel
theorem sub4_226 : sub4 [0, -1, -3] = true := by decide +kernel
theorem sub4_227 : sub4 [0, -1, -2] = true := by decide +kernel
theorem sub4_228 : sub4 [0, -1, -1] = true := by decide +kernel
theorem sub4_229 : sub4 [0, -1, 0] = true := by decide +kernel
theorem sub4_230 : sub4 [0, -1, 1] = true := by decide +kernel
theorem sub4_231 : sub4 [0, -1, 2] = true := by decide +kernel
theorem sub4_232 : sub4 [0, -1, 3] = true := by decide +kernel
theorem sub4_233 : sub4 [0, -1, 4] = true := by decide +kernel
theorem sub4_234 : sub4 [0, -1, 5] = true := by decide +kernel
theorem sub4_235 : sub4 [0, -1, 6] = true := by decide +kernel
theorem sub4_236 : sub4 [0, -1, 7] = true := by decide +kernel
theorem sub4_237 : sub4 [0, 0, -8] = true := by decide +kernel
theorem sub4_238 : sub4 [0, 0, -7] = true := by decide +kernel
theorem sub4_239 : sub4 [0, 0, -6] = true := by decide +kernel
theorem sub4_240 : sub4 [0, 0, -5] = true := by decide +kernel
theorem sub4_241 : sub4 [0, 0, -4] = true := by decide +kernel
theorem sub4_242 : sub4 [0, 0, -3] = true := by decide +kernel
theorem sub4_243 : sub4 [0, 0, -2] = true := by decide +kernel
theorem sub4_244 : sub4 [0, 0, -1] = true := by decide +kernel
theorem sub4_245 : sub4 [0, 0, 0] = true := by decide +kernel
theorem sub4_246 : sub4 [0, 0, 1] = true := by decide +kernel
theorem sub4_247 : sub4 [0, 0, 2] = true := by decide +kernel
theorem sub4_248 : sub4 [0, 0, 3] = true := by decide +kernel
theorem sub4_249 : sub4 [0, 0, 4] = true := by decide +kernel
theorem sub4_250 : sub4 [0, 0, 5] = true := by decide +kernel
theorem sub4_251 : sub4 [0, 0, 6] = true := by decide +kernel
theorem sub4_252 : sub4 [0, 0, 7] = true := by decide +kernel
theorem sub4_253 : sub4 [0, 1, -8] = true := by decide +kernel
theorem sub4_254 : sub4 [0, 1, -7] = true := by decide +kernel
theorem sub4_255 : sub4 [0, 1, -6] = true := by decide +kernel
theorem sb4_7 : ∀ q ∈ blk4_7, sub4 q = true := by
  unfold blk4_7
  exact List.forall_mem_cons.2 ⟨sub4_224, List.forall_mem_cons.2 ⟨sub4_225, List.forall_mem_cons.2 ⟨sub4_226, List.forall_mem_cons.2 ⟨sub4_227, List.forall_mem_cons.2 ⟨sub4_228, List.forall_mem_cons.2 ⟨sub4_229, List.forall_mem_cons.2 ⟨sub4_230, List.forall_mem_cons.2 ⟨sub4_231, List.forall_mem_cons.2 ⟨sub4_232, List.forall_mem_cons.2 ⟨sub4_233, List.forall_mem_cons.2 ⟨sub4_234, List.forall_mem_cons.2 ⟨sub4_235, List.forall_mem_cons.2 ⟨sub4_236, List.forall_mem_cons.2 ⟨sub4_237, List.forall_mem_cons.2 ⟨sub4_238, List.forall_mem_cons.2 ⟨sub4_239, List.forall_mem_cons.2 ⟨sub4_240, List.forall_mem_cons.2 ⟨sub4_241, List.forall_mem_cons.2 ⟨sub4_242, List.forall_mem_cons.2 ⟨sub4_243, List.forall_mem_cons.2 ⟨sub4_244, List.forall_mem_cons.2 ⟨sub4_245, List.forall_mem_cons.2 ⟨sub4_246, List.forall_mem_cons.2 ⟨sub4_247, List.forall_mem_cons.2 ⟨sub4_248, List.forall_mem_cons.2 ⟨sub4_249, List.forall_mem_cons.2 ⟨sub4_250, List.forall_mem_cons.2 ⟨sub4_251, List.forall_mem_cons.2 ⟨sub4_252, List.forall_mem_cons.2 ⟨sub4_253, List.forall_mem_cons.2 ⟨sub4_254, List.forall_mem_cons.2 ⟨sub4_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_256 : sub4 [0, 1, -5] = true := by decide +kernel
theorem sub4_257 : sub4 [0, 1, -4] = true := by decide +kernel
theorem sub4_258 : sub4 [0, 1, -3] = true := by decide +kernel
theorem sub4_259 : sub4 [0, 1, -2] = true := by decide +kernel
theorem sub4_260 : sub4 [0, 1, -1] = true := by decide +kernel
theorem sub4_261 : sub4 [0, 1, 0] = true := by decide +kernel
theorem sub4_262 : sub4 [0, 1, 1] = true := by decide +kernel
theorem sub4_263 : sub4 [0, 1, 2] = true := by decide +kernel
theorem sub4_264 : sub4 [0, 1, 3] = true := by decide +kernel
theorem sub4_265 : sub4 [0, 1, 4] = true := by decide +kernel
theorem sub4_266 : sub4 [0, 1, 5] = true := by decide +kernel
theorem sub4_267 : sub4 [0, 1, 6] = true := by decide +kernel
theorem sub4_268 : sub4 [0, 1, 7] = true := by decide +kernel
theorem sub4_269 : sub4 [0, 2, -8] = true := by decide +kernel
theorem sub4_270 : sub4 [0, 2, -7] = true := by decide +kernel
theorem sub4_271 : sub4 [0, 2, -6] = true := by decide +kernel
theorem sub4_272 : sub4 [0, 2, -5] = true := by decide +kernel
theorem sub4_273 : sub4 [0, 2, -4] = true := by decide +kernel
theorem sub4_274 : sub4 [0, 2, -3] = true := by decide +kernel
theorem sub4_275 : sub4 [0, 2, -2] = true := by decide +kernel
theorem sub4_276 : sub4 [0, 2, -1] = true := by decide +kernel
theorem sub4_277 : sub4 [0, 2, 0] = true := by decide +kernel
theorem sub4_278 : sub4 [0, 2, 1] = true := by decide +kernel
theorem sub4_279 : sub4 [0, 2, 2] = true := by decide +kernel
theorem sub4_280 : sub4 [0, 2, 3] = true := by decide +kernel
theorem sub4_281 : sub4 [0, 2, 4] = true := by decide +kernel
theorem sub4_282 : sub4 [0, 2, 5] = true := by decide +kernel
theorem sub4_283 : sub4 [0, 2, 6] = true := by decide +kernel
theorem sub4_284 : sub4 [0, 2, 7] = true := by decide +kernel
theorem sub4_285 : sub4 [0, 3] = true := by decide +kernel
theorem sub4_286 : sub4 [0, 4] = true := by decide +kernel
theorem sub4_287 : sub4 [0, 5] = true := by decide +kernel
theorem sb4_8 : ∀ q ∈ blk4_8, sub4 q = true := by
  unfold blk4_8
  exact List.forall_mem_cons.2 ⟨sub4_256, List.forall_mem_cons.2 ⟨sub4_257, List.forall_mem_cons.2 ⟨sub4_258, List.forall_mem_cons.2 ⟨sub4_259, List.forall_mem_cons.2 ⟨sub4_260, List.forall_mem_cons.2 ⟨sub4_261, List.forall_mem_cons.2 ⟨sub4_262, List.forall_mem_cons.2 ⟨sub4_263, List.forall_mem_cons.2 ⟨sub4_264, List.forall_mem_cons.2 ⟨sub4_265, List.forall_mem_cons.2 ⟨sub4_266, List.forall_mem_cons.2 ⟨sub4_267, List.forall_mem_cons.2 ⟨sub4_268, List.forall_mem_cons.2 ⟨sub4_269, List.forall_mem_cons.2 ⟨sub4_270, List.forall_mem_cons.2 ⟨sub4_271, List.forall_mem_cons.2 ⟨sub4_272, List.forall_mem_cons.2 ⟨sub4_273, List.forall_mem_cons.2 ⟨sub4_274, List.forall_mem_cons.2 ⟨sub4_275, List.forall_mem_cons.2 ⟨sub4_276, List.forall_mem_cons.2 ⟨sub4_277, List.forall_mem_cons.2 ⟨sub4_278, List.forall_mem_cons.2 ⟨sub4_279, List.forall_mem_cons.2 ⟨sub4_280, List.forall_mem_cons.2 ⟨sub4_281, List.forall_mem_cons.2 ⟨sub4_282, List.forall_mem_cons.2 ⟨sub4_283, List.forall_mem_cons.2 ⟨sub4_284, List.forall_mem_cons.2 ⟨sub4_285, List.forall_mem_cons.2 ⟨sub4_286, List.forall_mem_cons.2 ⟨sub4_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_288 : sub4 [1, -7] = true := by decide +kernel
theorem sub4_289 : sub4 [1, -6] = true := by decide +kernel
theorem sub4_290 : sub4 [1, -5] = true := by decide +kernel
theorem sub4_291 : sub4 [1, -4] = true := by decide +kernel
theorem sub4_292 : sub4 [1, -3] = true := by decide +kernel
theorem sub4_293 : sub4 [1, -2, -8] = true := by decide +kernel
theorem sub4_294 : sub4 [1, -2, -7] = true := by decide +kernel
theorem sub4_295 : sub4 [1, -2, -6] = true := by decide +kernel
theorem sub4_296 : sub4 [1, -2, -5] = true := by decide +kernel
theorem sub4_297 : sub4 [1, -2, -4] = true := by decide +kernel
theorem sub4_298 : sub4 [1, -2, -3] = true := by decide +kernel
theorem sub4_299 : sub4 [1, -2, -2] = true := by decide +kernel
theorem sub4_300 : sub4 [1, -2, -1] = true := by decide +kernel
theorem sub4_301 : sub4 [1, -2, 0] = true := by decide +kernel
theorem sub4_302 : sub4 [1, -2, 1] = true := by decide +kernel
theorem sub4_303 : sub4 [1, -2, 2] = true := by decide +kernel
theorem sub4_304 : sub4 [1, -2, 3] = true := by decide +kernel
theorem sub4_305 : sub4 [1, -2, 4] = true := by decide +kernel
theorem sub4_306 : sub4 [1, -2, 5] = true := by decide +kernel
theorem sub4_307 : sub4 [1, -2, 6] = true := by decide +kernel
theorem sub4_308 : sub4 [1, -2, 7] = true := by decide +kernel
theorem sub4_309 : sub4 [1, -1, -8] = true := by decide +kernel
theorem sub4_310 : sub4 [1, -1, -7] = true := by decide +kernel
theorem sub4_311 : sub4 [1, -1, -6] = true := by decide +kernel
theorem sub4_312 : sub4 [1, -1, -5] = true := by decide +kernel
theorem sub4_313 : sub4 [1, -1, -4] = true := by decide +kernel
theorem sub4_314 : sub4 [1, -1, -3] = true := by decide +kernel
theorem sub4_315 : sub4 [1, -1, -2] = true := by decide +kernel
theorem sub4_316 : sub4 [1, -1, -1] = true := by decide +kernel
theorem sub4_317 : sub4 [1, -1, 0] = true := by decide +kernel
theorem sub4_318 : sub4 [1, -1, 1] = true := by decide +kernel
theorem sub4_319 : sub4 [1, -1, 2] = true := by decide +kernel
theorem sb4_9 : ∀ q ∈ blk4_9, sub4 q = true := by
  unfold blk4_9
  exact List.forall_mem_cons.2 ⟨sub4_288, List.forall_mem_cons.2 ⟨sub4_289, List.forall_mem_cons.2 ⟨sub4_290, List.forall_mem_cons.2 ⟨sub4_291, List.forall_mem_cons.2 ⟨sub4_292, List.forall_mem_cons.2 ⟨sub4_293, List.forall_mem_cons.2 ⟨sub4_294, List.forall_mem_cons.2 ⟨sub4_295, List.forall_mem_cons.2 ⟨sub4_296, List.forall_mem_cons.2 ⟨sub4_297, List.forall_mem_cons.2 ⟨sub4_298, List.forall_mem_cons.2 ⟨sub4_299, List.forall_mem_cons.2 ⟨sub4_300, List.forall_mem_cons.2 ⟨sub4_301, List.forall_mem_cons.2 ⟨sub4_302, List.forall_mem_cons.2 ⟨sub4_303, List.forall_mem_cons.2 ⟨sub4_304, List.forall_mem_cons.2 ⟨sub4_305, List.forall_mem_cons.2 ⟨sub4_306, List.forall_mem_cons.2 ⟨sub4_307, List.forall_mem_cons.2 ⟨sub4_308, List.forall_mem_cons.2 ⟨sub4_309, List.forall_mem_cons.2 ⟨sub4_310, List.forall_mem_cons.2 ⟨sub4_311, List.forall_mem_cons.2 ⟨sub4_312, List.forall_mem_cons.2 ⟨sub4_313, List.forall_mem_cons.2 ⟨sub4_314, List.forall_mem_cons.2 ⟨sub4_315, List.forall_mem_cons.2 ⟨sub4_316, List.forall_mem_cons.2 ⟨sub4_317, List.forall_mem_cons.2 ⟨sub4_318, List.forall_mem_cons.2 ⟨sub4_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_320 : sub4 [1, -1, 3] = true := by decide +kernel
theorem sub4_321 : sub4 [1, -1, 4] = true := by decide +kernel
theorem sub4_322 : sub4 [1, -1, 5] = true := by decide +kernel
theorem sub4_323 : sub4 [1, -1, 6] = true := by decide +kernel
theorem sub4_324 : sub4 [1, -1, 7] = true := by decide +kernel
theorem sub4_325 : sub4 [1, 0, -8] = true := by decide +kernel
theorem sub4_326 : sub4 [1, 0, -7] = true := by decide +kernel
theorem sub4_327 : sub4 [1, 0, -6] = true := by decide +kernel
theorem sub4_328 : sub4 [1, 0, -5] = true := by decide +kernel
theorem sub4_329 : sub4 [1, 0, -4] = true := by decide +kernel
theorem sub4_330 : sub4 [1, 0, -3] = true := by decide +kernel
theorem sub4_331 : sub4 [1, 0, -2] = true := by decide +kernel
theorem sub4_332 : sub4 [1, 0, -1] = true := by decide +kernel
theorem sub4_333 : sub4 [1, 0, 0] = true := by decide +kernel
theorem sub4_334 : sub4 [1, 0, 1] = true := by decide +kernel
theorem sub4_335 : sub4 [1, 0, 2] = true := by decide +kernel
theorem sub4_336 : sub4 [1, 0, 3] = true := by decide +kernel
theorem sub4_337 : sub4 [1, 0, 4] = true := by decide +kernel
theorem sub4_338 : sub4 [1, 0, 5] = true := by decide +kernel
theorem sub4_339 : sub4 [1, 0, 6] = true := by decide +kernel
theorem sub4_340 : sub4 [1, 0, 7] = true := by decide +kernel
theorem sub4_341 : sub4 [1, 0, 8] = true := by decide +kernel
theorem sub4_342 : sub4 [1, 1, -8] = true := by decide +kernel
theorem sub4_343 : sub4 [1, 1, -7] = true := by decide +kernel
theorem sub4_344 : sub4 [1, 1, -6] = true := by decide +kernel
theorem sub4_345 : sub4 [1, 1, -5] = true := by decide +kernel
theorem sub4_346 : sub4 [1, 1, -4] = true := by decide +kernel
theorem sub4_347 : sub4 [1, 1, -3] = true := by decide +kernel
theorem sub4_348 : sub4 [1, 1, -2] = true := by decide +kernel
theorem sub4_349 : sub4 [1, 1, -1] = true := by decide +kernel
theorem sub4_350 : sub4 [1, 1, 0] = true := by decide +kernel
theorem sub4_351 : sub4 [1, 1, 1] = true := by decide +kernel
theorem sb4_10 : ∀ q ∈ blk4_10, sub4 q = true := by
  unfold blk4_10
  exact List.forall_mem_cons.2 ⟨sub4_320, List.forall_mem_cons.2 ⟨sub4_321, List.forall_mem_cons.2 ⟨sub4_322, List.forall_mem_cons.2 ⟨sub4_323, List.forall_mem_cons.2 ⟨sub4_324, List.forall_mem_cons.2 ⟨sub4_325, List.forall_mem_cons.2 ⟨sub4_326, List.forall_mem_cons.2 ⟨sub4_327, List.forall_mem_cons.2 ⟨sub4_328, List.forall_mem_cons.2 ⟨sub4_329, List.forall_mem_cons.2 ⟨sub4_330, List.forall_mem_cons.2 ⟨sub4_331, List.forall_mem_cons.2 ⟨sub4_332, List.forall_mem_cons.2 ⟨sub4_333, List.forall_mem_cons.2 ⟨sub4_334, List.forall_mem_cons.2 ⟨sub4_335, List.forall_mem_cons.2 ⟨sub4_336, List.forall_mem_cons.2 ⟨sub4_337, List.forall_mem_cons.2 ⟨sub4_338, List.forall_mem_cons.2 ⟨sub4_339, List.forall_mem_cons.2 ⟨sub4_340, List.forall_mem_cons.2 ⟨sub4_341, List.forall_mem_cons.2 ⟨sub4_342, List.forall_mem_cons.2 ⟨sub4_343, List.forall_mem_cons.2 ⟨sub4_344, List.forall_mem_cons.2 ⟨sub4_345, List.forall_mem_cons.2 ⟨sub4_346, List.forall_mem_cons.2 ⟨sub4_347, List.forall_mem_cons.2 ⟨sub4_348, List.forall_mem_cons.2 ⟨sub4_349, List.forall_mem_cons.2 ⟨sub4_350, List.forall_mem_cons.2 ⟨sub4_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_352 : sub4 [1, 1, 2] = true := by decide +kernel
theorem sub4_353 : sub4 [1, 1, 3] = true := by decide +kernel
theorem sub4_354 : sub4 [1, 1, 4] = true := by decide +kernel
theorem sub4_355 : sub4 [1, 1, 5] = true := by decide +kernel
theorem sub4_356 : sub4 [1, 1, 6] = true := by decide +kernel
theorem sub4_357 : sub4 [1, 1, 7] = true := by decide +kernel
theorem sub4_358 : sub4 [1, 2] = true := by decide +kernel
theorem sub4_359 : sub4 [1, 3] = true := by decide +kernel
theorem sub4_360 : sub4 [1, 4] = true := by decide +kernel
theorem sub4_361 : sub4 [1, 5] = true := by decide +kernel
theorem sub4_362 : sub4 [2, -7] = true := by decide +kernel
theorem sub4_363 : sub4 [2, -6] = true := by decide +kernel
theorem sub4_364 : sub4 [2, -5] = true := by decide +kernel
theorem sub4_365 : sub4 [2, -4] = true := by decide +kernel
theorem sub4_366 : sub4 [2, -3] = true := by decide +kernel
theorem sub4_367 : sub4 [2, -2, -8] = true := by decide +kernel
theorem sub4_368 : sub4 [2, -2, -7] = true := by decide +kernel
theorem sub4_369 : sub4 [2, -2, -6] = true := by decide +kernel
theorem sub4_370 : sub4 [2, -2, -5] = true := by decide +kernel
theorem sub4_371 : sub4 [2, -2, -4] = true := by decide +kernel
theorem sub4_372 : sub4 [2, -2, -3] = true := by decide +kernel
theorem sub4_373 : sub4 [2, -2, -2] = true := by decide +kernel
theorem sub4_374 : sub4 [2, -2, -1] = true := by decide +kernel
theorem sub4_375 : sub4 [2, -2, 0] = true := by decide +kernel
theorem sub4_376 : sub4 [2, -2, 1] = true := by decide +kernel
theorem sub4_377 : sub4 [2, -2, 2] = true := by decide +kernel
theorem sub4_378 : sub4 [2, -2, 3] = true := by decide +kernel
theorem sub4_379 : sub4 [2, -2, 4] = true := by decide +kernel
theorem sub4_380 : sub4 [2, -2, 5] = true := by decide +kernel
theorem sub4_381 : sub4 [2, -2, 6] = true := by decide +kernel
theorem sub4_382 : sub4 [2, -2, 7] = true := by decide +kernel
theorem sub4_383 : sub4 [2, -1, -8] = true := by decide +kernel
theorem sb4_11 : ∀ q ∈ blk4_11, sub4 q = true := by
  unfold blk4_11
  exact List.forall_mem_cons.2 ⟨sub4_352, List.forall_mem_cons.2 ⟨sub4_353, List.forall_mem_cons.2 ⟨sub4_354, List.forall_mem_cons.2 ⟨sub4_355, List.forall_mem_cons.2 ⟨sub4_356, List.forall_mem_cons.2 ⟨sub4_357, List.forall_mem_cons.2 ⟨sub4_358, List.forall_mem_cons.2 ⟨sub4_359, List.forall_mem_cons.2 ⟨sub4_360, List.forall_mem_cons.2 ⟨sub4_361, List.forall_mem_cons.2 ⟨sub4_362, List.forall_mem_cons.2 ⟨sub4_363, List.forall_mem_cons.2 ⟨sub4_364, List.forall_mem_cons.2 ⟨sub4_365, List.forall_mem_cons.2 ⟨sub4_366, List.forall_mem_cons.2 ⟨sub4_367, List.forall_mem_cons.2 ⟨sub4_368, List.forall_mem_cons.2 ⟨sub4_369, List.forall_mem_cons.2 ⟨sub4_370, List.forall_mem_cons.2 ⟨sub4_371, List.forall_mem_cons.2 ⟨sub4_372, List.forall_mem_cons.2 ⟨sub4_373, List.forall_mem_cons.2 ⟨sub4_374, List.forall_mem_cons.2 ⟨sub4_375, List.forall_mem_cons.2 ⟨sub4_376, List.forall_mem_cons.2 ⟨sub4_377, List.forall_mem_cons.2 ⟨sub4_378, List.forall_mem_cons.2 ⟨sub4_379, List.forall_mem_cons.2 ⟨sub4_380, List.forall_mem_cons.2 ⟨sub4_381, List.forall_mem_cons.2 ⟨sub4_382, List.forall_mem_cons.2 ⟨sub4_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_384 : sub4 [2, -1, -7] = true := by decide +kernel
theorem sub4_385 : sub4 [2, -1, -6] = true := by decide +kernel
theorem sub4_386 : sub4 [2, -1, -5] = true := by decide +kernel
theorem sub4_387 : sub4 [2, -1, -4] = true := by decide +kernel
theorem sub4_388 : sub4 [2, -1, -3] = true := by decide +kernel
theorem sub4_389 : sub4 [2, -1, -2] = true := by decide +kernel
theorem sub4_390 : sub4 [2, -1, -1] = true := by decide +kernel
theorem sub4_391 : sub4 [2, -1, 0] = true := by decide +kernel
theorem sub4_392 : sub4 [2, -1, 1] = true := by decide +kernel
theorem sub4_393 : sub4 [2, -1, 2] = true := by decide +kernel
theorem sub4_394 : sub4 [2, -1, 3] = true := by decide +kernel
theorem sub4_395 : sub4 [2, -1, 4] = true := by decide +kernel
theorem sub4_396 : sub4 [2, -1, 5] = true := by decide +kernel
theorem sub4_397 : sub4 [2, -1, 6] = true := by decide +kernel
theorem sub4_398 : sub4 [2, -1, 7] = true := by decide +kernel
theorem sub4_399 : sub4 [2, 0, -8] = true := by decide +kernel
theorem sub4_400 : sub4 [2, 0, -7] = true := by decide +kernel
theorem sub4_401 : sub4 [2, 0, -6] = true := by decide +kernel
theorem sub4_402 : sub4 [2, 0, -5] = true := by decide +kernel
theorem sub4_403 : sub4 [2, 0, -4] = true := by decide +kernel
theorem sub4_404 : sub4 [2, 0, -3] = true := by decide +kernel
theorem sub4_405 : sub4 [2, 0, -2] = true := by decide +kernel
theorem sub4_406 : sub4 [2, 0, -1] = true := by decide +kernel
theorem sub4_407 : sub4 [2, 0, 0] = true := by decide +kernel
theorem sub4_408 : sub4 [2, 0, 1] = true := by decide +kernel
theorem sub4_409 : sub4 [2, 0, 2] = true := by decide +kernel
theorem sub4_410 : sub4 [2, 0, 3] = true := by decide +kernel
theorem sub4_411 : sub4 [2, 0, 4] = true := by decide +kernel
theorem sub4_412 : sub4 [2, 0, 5] = true := by decide +kernel
theorem sub4_413 : sub4 [2, 0, 6] = true := by decide +kernel
theorem sub4_414 : sub4 [2, 0, 7] = true := by decide +kernel
theorem sub4_415 : sub4 [2, 1] = true := by decide +kernel
theorem sb4_12 : ∀ q ∈ blk4_12, sub4 q = true := by
  unfold blk4_12
  exact List.forall_mem_cons.2 ⟨sub4_384, List.forall_mem_cons.2 ⟨sub4_385, List.forall_mem_cons.2 ⟨sub4_386, List.forall_mem_cons.2 ⟨sub4_387, List.forall_mem_cons.2 ⟨sub4_388, List.forall_mem_cons.2 ⟨sub4_389, List.forall_mem_cons.2 ⟨sub4_390, List.forall_mem_cons.2 ⟨sub4_391, List.forall_mem_cons.2 ⟨sub4_392, List.forall_mem_cons.2 ⟨sub4_393, List.forall_mem_cons.2 ⟨sub4_394, List.forall_mem_cons.2 ⟨sub4_395, List.forall_mem_cons.2 ⟨sub4_396, List.forall_mem_cons.2 ⟨sub4_397, List.forall_mem_cons.2 ⟨sub4_398, List.forall_mem_cons.2 ⟨sub4_399, List.forall_mem_cons.2 ⟨sub4_400, List.forall_mem_cons.2 ⟨sub4_401, List.forall_mem_cons.2 ⟨sub4_402, List.forall_mem_cons.2 ⟨sub4_403, List.forall_mem_cons.2 ⟨sub4_404, List.forall_mem_cons.2 ⟨sub4_405, List.forall_mem_cons.2 ⟨sub4_406, List.forall_mem_cons.2 ⟨sub4_407, List.forall_mem_cons.2 ⟨sub4_408, List.forall_mem_cons.2 ⟨sub4_409, List.forall_mem_cons.2 ⟨sub4_410, List.forall_mem_cons.2 ⟨sub4_411, List.forall_mem_cons.2 ⟨sub4_412, List.forall_mem_cons.2 ⟨sub4_413, List.forall_mem_cons.2 ⟨sub4_414, List.forall_mem_cons.2 ⟨sub4_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub4_416 : sub4 [2, 2] = true := by decide +kernel
theorem sub4_417 : sub4 [2, 3] = true := by decide +kernel
theorem sub4_418 : sub4 [2, 4] = true := by decide +kernel
theorem sub4_419 : sub4 [3, -7] = true := by decide +kernel
theorem sub4_420 : sub4 [3, -6] = true := by decide +kernel
theorem sub4_421 : sub4 [3, -5] = true := by decide +kernel
theorem sub4_422 : sub4 [3, -4] = true := by decide +kernel
theorem sub4_423 : sub4 [3, -3] = true := by decide +kernel
theorem sub4_424 : sub4 [3, -2, -7] = true := by decide +kernel
theorem sub4_425 : sub4 [3, -2, -6] = true := by decide +kernel
theorem sub4_426 : sub4 [3, -2, -5] = true := by decide +kernel
theorem sub4_427 : sub4 [3, -2, -4] = true := by decide +kernel
theorem sub4_428 : sub4 [3, -2, -3] = true := by decide +kernel
theorem sub4_429 : sub4 [3, -2, -2] = true := by decide +kernel
theorem sub4_430 : sub4 [3, -2, -1] = true := by decide +kernel
theorem sub4_431 : sub4 [3, -2, 0] = true := by decide +kernel
theorem sub4_432 : sub4 [3, -2, 1] = true := by decide +kernel
theorem sub4_433 : sub4 [3, -2, 2] = true := by decide +kernel
theorem sub4_434 : sub4 [3, -2, 3] = true := by decide +kernel
theorem sub4_435 : sub4 [3, -2, 4] = true := by decide +kernel
theorem sub4_436 : sub4 [3, -2, 5] = true := by decide +kernel
theorem sub4_437 : sub4 [3, -2, 6] = true := by decide +kernel
theorem sub4_438 : sub4 [3, -2, 7] = true := by decide +kernel
theorem sub4_439 : sub4 [3, -1, -7] = true := by decide +kernel
theorem sub4_440 : sub4 [3, -1, -6] = true := by decide +kernel
theorem sub4_441 : sub4 [3, -1, -5] = true := by decide +kernel
theorem sub4_442 : sub4 [3, -1, -4] = true := by decide +kernel
theorem sub4_443 : sub4 [3, -1, -3] = true := by decide +kernel
theorem sub4_444 : sub4 [3, -1, -2] = true := by decide +kernel
theorem sub4_445 : sub4 [3, -1, -1] = true := by decide +kernel
theorem sub4_446 : sub4 [3, -1, 0] = true := by decide +kernel
theorem sub4_447 : sub4 [3, -1, 1] = true := by decide +kernel
theorem sb4_13 : ∀ q ∈ blk4_13, sub4 q = true := by
  unfold blk4_13
  exact List.forall_mem_cons.2 ⟨sub4_416, List.forall_mem_cons.2 ⟨sub4_417, List.forall_mem_cons.2 ⟨sub4_418, List.forall_mem_cons.2 ⟨sub4_419, List.forall_mem_cons.2 ⟨sub4_420, List.forall_mem_cons.2 ⟨sub4_421, List.forall_mem_cons.2 ⟨sub4_422, List.forall_mem_cons.2 ⟨sub4_423, List.forall_mem_cons.2 ⟨sub4_424, List.forall_mem_cons.2 ⟨sub4_425, List.forall_mem_cons.2 ⟨sub4_426, List.forall_mem_cons.2 ⟨sub4_427, List.forall_mem_cons.2 ⟨sub4_428, List.forall_mem_cons.2 ⟨sub4_429, List.forall_mem_cons.2 ⟨sub4_430, List.forall_mem_cons.2 ⟨sub4_431, List.forall_mem_cons.2 ⟨sub4_432, List.forall_mem_cons.2 ⟨sub4_433, List.forall_mem_cons.2 ⟨sub4_434, List.forall_mem_cons.2 ⟨sub4_435, List.forall_mem_cons.2 ⟨sub4_436, List.forall_mem_cons.2 ⟨sub4_437, List.forall_mem_cons.2 ⟨sub4_438, List.forall_mem_cons.2 ⟨sub4_439, List.forall_mem_cons.2 ⟨sub4_440, List.forall_mem_cons.2 ⟨sub4_441, List.forall_mem_cons.2 ⟨sub4_442, List.forall_mem_cons.2 ⟨sub4_443, List.forall_mem_cons.2 ⟨sub4_444, List.forall_mem_cons.2 ⟨sub4_445, List.forall_mem_cons.2 ⟨sub4_446, List.forall_mem_cons.2 ⟨sub4_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C063
