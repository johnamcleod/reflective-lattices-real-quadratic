import ReflectZphi.Data.Cert5.C105.Base

namespace ReflectZphi.Data.Cert5.C105
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub10_96 : sub10 [-2, -2, 4] = true := by decide +kernel
theorem sub10_97 : sub10 [-2, -2, 5] = true := by decide +kernel
theorem sub10_98 : sub10 [-2, -2, 6] = true := by decide +kernel
theorem sub10_99 : sub10 [-2, -1, -7] = true := by decide +kernel
theorem sub10_100 : sub10 [-2, -1, -6] = true := by decide +kernel
theorem sub10_101 : sub10 [-2, -1, -5] = true := by decide +kernel
theorem sub10_102 : sub10 [-2, -1, -4] = true := by decide +kernel
theorem sub10_103 : sub10 [-2, -1, -3] = true := by decide +kernel
theorem sub10_104 : sub10 [-2, -1, -2] = true := by decide +kernel
theorem sub10_105 : sub10 [-2, -1, -1] = true := by decide +kernel
theorem sub10_106 : sub10 [-2, -1, 0] = true := by decide +kernel
theorem sub10_107 : sub10 [-2, -1, 1] = true := by decide +kernel
theorem sub10_108 : sub10 [-2, -1, 2] = true := by decide +kernel
theorem sub10_109 : sub10 [-2, -1, 3] = true := by decide +kernel
theorem sub10_110 : sub10 [-2, -1, 4] = true := by decide +kernel
theorem sub10_111 : sub10 [-2, -1, 5] = true := by decide +kernel
theorem sub10_112 : sub10 [-2, -1, 6] = true := by decide +kernel
theorem sub10_113 : sub10 [-2, 0, -7] = true := by decide +kernel
theorem sub10_114 : sub10 [-2, 0, -6] = true := by decide +kernel
theorem sub10_115 : sub10 [-2, 0, -5] = true := by decide +kernel
theorem sub10_116 : sub10 [-2, 0, -4] = true := by decide +kernel
theorem sub10_117 : sub10 [-2, 0, -3] = true := by decide +kernel
theorem sub10_118 : sub10 [-2, 0, -2] = true := by decide +kernel
theorem sub10_119 : sub10 [-2, 0, -1] = true := by decide +kernel
theorem sub10_120 : sub10 [-2, 0, 0] = true := by decide +kernel
theorem sub10_121 : sub10 [-2, 0, 1] = true := by decide +kernel
theorem sub10_122 : sub10 [-2, 0, 2] = true := by decide +kernel
theorem sub10_123 : sub10 [-2, 0, 3] = true := by decide +kernel
theorem sub10_124 : sub10 [-2, 0, 4] = true := by decide +kernel
theorem sub10_125 : sub10 [-2, 0, 5] = true := by decide +kernel
theorem sub10_126 : sub10 [-2, 0, 6] = true := by decide +kernel
theorem sub10_127 : sub10 [-2, 0, 7] = true := by decide +kernel
theorem sb10_3 : ∀ q ∈ blk10_3, sub10 q = true := by
  unfold blk10_3
  exact List.forall_mem_cons.2 ⟨sub10_96, List.forall_mem_cons.2 ⟨sub10_97, List.forall_mem_cons.2 ⟨sub10_98, List.forall_mem_cons.2 ⟨sub10_99, List.forall_mem_cons.2 ⟨sub10_100, List.forall_mem_cons.2 ⟨sub10_101, List.forall_mem_cons.2 ⟨sub10_102, List.forall_mem_cons.2 ⟨sub10_103, List.forall_mem_cons.2 ⟨sub10_104, List.forall_mem_cons.2 ⟨sub10_105, List.forall_mem_cons.2 ⟨sub10_106, List.forall_mem_cons.2 ⟨sub10_107, List.forall_mem_cons.2 ⟨sub10_108, List.forall_mem_cons.2 ⟨sub10_109, List.forall_mem_cons.2 ⟨sub10_110, List.forall_mem_cons.2 ⟨sub10_111, List.forall_mem_cons.2 ⟨sub10_112, List.forall_mem_cons.2 ⟨sub10_113, List.forall_mem_cons.2 ⟨sub10_114, List.forall_mem_cons.2 ⟨sub10_115, List.forall_mem_cons.2 ⟨sub10_116, List.forall_mem_cons.2 ⟨sub10_117, List.forall_mem_cons.2 ⟨sub10_118, List.forall_mem_cons.2 ⟨sub10_119, List.forall_mem_cons.2 ⟨sub10_120, List.forall_mem_cons.2 ⟨sub10_121, List.forall_mem_cons.2 ⟨sub10_122, List.forall_mem_cons.2 ⟨sub10_123, List.forall_mem_cons.2 ⟨sub10_124, List.forall_mem_cons.2 ⟨sub10_125, List.forall_mem_cons.2 ⟨sub10_126, List.forall_mem_cons.2 ⟨sub10_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_128 : sub10 [-2, 1, -7] = true := by decide +kernel
theorem sub10_129 : sub10 [-2, 1, -6] = true := by decide +kernel
theorem sub10_130 : sub10 [-2, 1, -5] = true := by decide +kernel
theorem sub10_131 : sub10 [-2, 1, -4] = true := by decide +kernel
theorem sub10_132 : sub10 [-2, 1, -3] = true := by decide +kernel
theorem sub10_133 : sub10 [-2, 1, -2] = true := by decide +kernel
theorem sub10_134 : sub10 [-2, 1, -1] = true := by decide +kernel
theorem sub10_135 : sub10 [-2, 1, 0] = true := by decide +kernel
theorem sub10_136 : sub10 [-2, 1, 1] = true := by decide +kernel
theorem sub10_137 : sub10 [-2, 1, 2] = true := by decide +kernel
theorem sub10_138 : sub10 [-2, 1, 3] = true := by decide +kernel
theorem sub10_139 : sub10 [-2, 1, 4] = true := by decide +kernel
theorem sub10_140 : sub10 [-2, 1, 5] = true := by decide +kernel
theorem sub10_141 : sub10 [-2, 1, 6] = true := by decide +kernel
theorem sub10_142 : sub10 [-2, 1, 7] = true := by decide +kernel
theorem sub10_143 : sub10 [-2, 2, -7] = true := by decide +kernel
theorem sub10_144 : sub10 [-2, 2, -6] = true := by decide +kernel
theorem sub10_145 : sub10 [-2, 2, -5] = true := by decide +kernel
theorem sub10_146 : sub10 [-2, 2, -4] = true := by decide +kernel
theorem sub10_147 : sub10 [-2, 2, -3] = true := by decide +kernel
theorem sub10_148 : sub10 [-2, 2, -2] = true := by decide +kernel
theorem sub10_149 : sub10 [-2, 2, -1] = true := by decide +kernel
theorem sub10_150 : sub10 [-2, 2, 0] = true := by decide +kernel
theorem sub10_151 : sub10 [-2, 2, 1] = true := by decide +kernel
theorem sub10_152 : sub10 [-2, 2, 2] = true := by decide +kernel
theorem sub10_153 : sub10 [-2, 2, 3] = true := by decide +kernel
theorem sub10_154 : sub10 [-2, 2, 4] = true := by decide +kernel
theorem sub10_155 : sub10 [-2, 2, 5] = true := by decide +kernel
theorem sub10_156 : sub10 [-2, 2, 6] = true := by decide +kernel
theorem sub10_157 : sub10 [-2, 3] = true := by decide +kernel
theorem sub10_158 : sub10 [-2, 4] = true := by decide +kernel
theorem sub10_159 : sub10 [-2, 5] = true := by decide +kernel
theorem sb10_4 : ∀ q ∈ blk10_4, sub10 q = true := by
  unfold blk10_4
  exact List.forall_mem_cons.2 ⟨sub10_128, List.forall_mem_cons.2 ⟨sub10_129, List.forall_mem_cons.2 ⟨sub10_130, List.forall_mem_cons.2 ⟨sub10_131, List.forall_mem_cons.2 ⟨sub10_132, List.forall_mem_cons.2 ⟨sub10_133, List.forall_mem_cons.2 ⟨sub10_134, List.forall_mem_cons.2 ⟨sub10_135, List.forall_mem_cons.2 ⟨sub10_136, List.forall_mem_cons.2 ⟨sub10_137, List.forall_mem_cons.2 ⟨sub10_138, List.forall_mem_cons.2 ⟨sub10_139, List.forall_mem_cons.2 ⟨sub10_140, List.forall_mem_cons.2 ⟨sub10_141, List.forall_mem_cons.2 ⟨sub10_142, List.forall_mem_cons.2 ⟨sub10_143, List.forall_mem_cons.2 ⟨sub10_144, List.forall_mem_cons.2 ⟨sub10_145, List.forall_mem_cons.2 ⟨sub10_146, List.forall_mem_cons.2 ⟨sub10_147, List.forall_mem_cons.2 ⟨sub10_148, List.forall_mem_cons.2 ⟨sub10_149, List.forall_mem_cons.2 ⟨sub10_150, List.forall_mem_cons.2 ⟨sub10_151, List.forall_mem_cons.2 ⟨sub10_152, List.forall_mem_cons.2 ⟨sub10_153, List.forall_mem_cons.2 ⟨sub10_154, List.forall_mem_cons.2 ⟨sub10_155, List.forall_mem_cons.2 ⟨sub10_156, List.forall_mem_cons.2 ⟨sub10_157, List.forall_mem_cons.2 ⟨sub10_158, List.forall_mem_cons.2 ⟨sub10_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_160 : sub10 [-1, -6] = true := by decide +kernel
theorem sub10_161 : sub10 [-1, -5] = true := by decide +kernel
theorem sub10_162 : sub10 [-1, -4] = true := by decide +kernel
theorem sub10_163 : sub10 [-1, -3, -7] = true := by decide +kernel
theorem sub10_164 : sub10 [-1, -3, -6] = true := by decide +kernel
theorem sub10_165 : sub10 [-1, -3, -5] = true := by decide +kernel
theorem sub10_166 : sub10 [-1, -3, -4] = true := by decide +kernel
theorem sub10_167 : sub10 [-1, -3, -3] = true := by decide +kernel
theorem sub10_168 : sub10 [-1, -3, -2] = true := by decide +kernel
theorem sub10_169 : sub10 [-1, -3, -1] = true := by decide +kernel
theorem sub10_170 : sub10 [-1, -3, 0] = true := by decide +kernel
theorem sub10_171 : sub10 [-1, -3, 1] = true := by decide +kernel
theorem sub10_172 : sub10 [-1, -3, 2] = true := by decide +kernel
theorem sub10_173 : sub10 [-1, -3, 3] = true := by decide +kernel
theorem sub10_174 : sub10 [-1, -3, 4] = true := by decide +kernel
theorem sub10_175 : sub10 [-1, -3, 5] = true := by decide +kernel
theorem sub10_176 : sub10 [-1, -3, 6] = true := by decide +kernel
theorem sub10_177 : sub10 [-1, -2, -7] = true := by decide +kernel
theorem sub10_178 : sub10 [-1, -2, -6] = true := by decide +kernel
theorem sub10_179 : sub10 [-1, -2, -5] = true := by decide +kernel
theorem sub10_180 : sub10 [-1, -2, -4] = true := by decide +kernel
theorem sub10_181 : sub10 [-1, -2, -3] = true := by decide +kernel
theorem sub10_182 : sub10 [-1, -2, -2] = true := by decide +kernel
theorem sub10_183 : sub10 [-1, -2, -1] = true := by decide +kernel
theorem sub10_184 : sub10 [-1, -2, 0] = true := by decide +kernel
theorem sub10_185 : sub10 [-1, -2, 1] = true := by decide +kernel
theorem sub10_186 : sub10 [-1, -2, 2] = true := by decide +kernel
theorem sub10_187 : sub10 [-1, -2, 3] = true := by decide +kernel
theorem sub10_188 : sub10 [-1, -2, 4] = true := by decide +kernel
theorem sub10_189 : sub10 [-1, -2, 5] = true := by decide +kernel
theorem sub10_190 : sub10 [-1, -2, 6] = true := by decide +kernel
theorem sub10_191 : sub10 [-1, -1, -8] = true := by decide +kernel
theorem sb10_5 : ∀ q ∈ blk10_5, sub10 q = true := by
  unfold blk10_5
  exact List.forall_mem_cons.2 ⟨sub10_160, List.forall_mem_cons.2 ⟨sub10_161, List.forall_mem_cons.2 ⟨sub10_162, List.forall_mem_cons.2 ⟨sub10_163, List.forall_mem_cons.2 ⟨sub10_164, List.forall_mem_cons.2 ⟨sub10_165, List.forall_mem_cons.2 ⟨sub10_166, List.forall_mem_cons.2 ⟨sub10_167, List.forall_mem_cons.2 ⟨sub10_168, List.forall_mem_cons.2 ⟨sub10_169, List.forall_mem_cons.2 ⟨sub10_170, List.forall_mem_cons.2 ⟨sub10_171, List.forall_mem_cons.2 ⟨sub10_172, List.forall_mem_cons.2 ⟨sub10_173, List.forall_mem_cons.2 ⟨sub10_174, List.forall_mem_cons.2 ⟨sub10_175, List.forall_mem_cons.2 ⟨sub10_176, List.forall_mem_cons.2 ⟨sub10_177, List.forall_mem_cons.2 ⟨sub10_178, List.forall_mem_cons.2 ⟨sub10_179, List.forall_mem_cons.2 ⟨sub10_180, List.forall_mem_cons.2 ⟨sub10_181, List.forall_mem_cons.2 ⟨sub10_182, List.forall_mem_cons.2 ⟨sub10_183, List.forall_mem_cons.2 ⟨sub10_184, List.forall_mem_cons.2 ⟨sub10_185, List.forall_mem_cons.2 ⟨sub10_186, List.forall_mem_cons.2 ⟨sub10_187, List.forall_mem_cons.2 ⟨sub10_188, List.forall_mem_cons.2 ⟨sub10_189, List.forall_mem_cons.2 ⟨sub10_190, List.forall_mem_cons.2 ⟨sub10_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_192 : sub10 [-1, -1, -7] = true := by decide +kernel
theorem sub10_193 : sub10 [-1, -1, -6] = true := by decide +kernel
theorem sub10_194 : sub10 [-1, -1, -5] = true := by decide +kernel
theorem sub10_195 : sub10 [-1, -1, -4] = true := by decide +kernel
theorem sub10_196 : sub10 [-1, -1, -3] = true := by decide +kernel
theorem sub10_197 : sub10 [-1, -1, -2] = true := by decide +kernel
theorem sub10_198 : sub10 [-1, -1, -1] = true := by decide +kernel
theorem sub10_199 : sub10 [-1, -1, 0] = true := by decide +kernel
theorem sub10_200 : sub10 [-1, -1, 1] = true := by decide +kernel
theorem sub10_201 : sub10 [-1, -1, 2] = true := by decide +kernel
theorem sub10_202 : sub10 [-1, -1, 3] = true := by decide +kernel
theorem sub10_203 : sub10 [-1, -1, 4] = true := by decide +kernel
theorem sub10_204 : sub10 [-1, -1, 5] = true := by decide +kernel
theorem sub10_205 : sub10 [-1, -1, 6] = true := by decide +kernel
theorem sub10_206 : sub10 [-1, -1, 7] = true := by decide +kernel
theorem sub10_207 : sub10 [-1, 0, -8] = true := by decide +kernel
theorem sub10_208 : sub10 [-1, 0, -7] = true := by decide +kernel
theorem sub10_209 : sub10 [-1, 0, -6] = true := by decide +kernel
theorem sub10_210 : sub10 [-1, 0, -5] = true := by decide +kernel
theorem sub10_211 : sub10 [-1, 0, -4] = true := by decide +kernel
theorem sub10_212 : sub10 [-1, 0, -3] = true := by decide +kernel
theorem sub10_213 : sub10 [-1, 0, -2] = true := by decide +kernel
theorem sub10_214 : sub10 [-1, 0, -1] = true := by decide +kernel
theorem sub10_215 : sub10 [-1, 0, 0] = true := by decide +kernel
theorem sub10_216 : sub10 [-1, 0, 1] = true := by decide +kernel
theorem sub10_217 : sub10 [-1, 0, 2] = true := by decide +kernel
theorem sub10_218 : sub10 [-1, 0, 3] = true := by decide +kernel
theorem sub10_219 : sub10 [-1, 0, 4] = true := by decide +kernel
theorem sub10_220 : sub10 [-1, 0, 5] = true := by decide +kernel
theorem sub10_221 : sub10 [-1, 0, 6] = true := by decide +kernel
theorem sub10_222 : sub10 [-1, 0, 7] = true := by decide +kernel
theorem sub10_223 : sub10 [-1, 1, -7] = true := by decide +kernel
theorem sb10_6 : ∀ q ∈ blk10_6, sub10 q = true := by
  unfold blk10_6
  exact List.forall_mem_cons.2 ⟨sub10_192, List.forall_mem_cons.2 ⟨sub10_193, List.forall_mem_cons.2 ⟨sub10_194, List.forall_mem_cons.2 ⟨sub10_195, List.forall_mem_cons.2 ⟨sub10_196, List.forall_mem_cons.2 ⟨sub10_197, List.forall_mem_cons.2 ⟨sub10_198, List.forall_mem_cons.2 ⟨sub10_199, List.forall_mem_cons.2 ⟨sub10_200, List.forall_mem_cons.2 ⟨sub10_201, List.forall_mem_cons.2 ⟨sub10_202, List.forall_mem_cons.2 ⟨sub10_203, List.forall_mem_cons.2 ⟨sub10_204, List.forall_mem_cons.2 ⟨sub10_205, List.forall_mem_cons.2 ⟨sub10_206, List.forall_mem_cons.2 ⟨sub10_207, List.forall_mem_cons.2 ⟨sub10_208, List.forall_mem_cons.2 ⟨sub10_209, List.forall_mem_cons.2 ⟨sub10_210, List.forall_mem_cons.2 ⟨sub10_211, List.forall_mem_cons.2 ⟨sub10_212, List.forall_mem_cons.2 ⟨sub10_213, List.forall_mem_cons.2 ⟨sub10_214, List.forall_mem_cons.2 ⟨sub10_215, List.forall_mem_cons.2 ⟨sub10_216, List.forall_mem_cons.2 ⟨sub10_217, List.forall_mem_cons.2 ⟨sub10_218, List.forall_mem_cons.2 ⟨sub10_219, List.forall_mem_cons.2 ⟨sub10_220, List.forall_mem_cons.2 ⟨sub10_221, List.forall_mem_cons.2 ⟨sub10_222, List.forall_mem_cons.2 ⟨sub10_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_224 : sub10 [-1, 1, -6] = true := by decide +kernel
theorem sub10_225 : sub10 [-1, 1, -5] = true := by decide +kernel
theorem sub10_226 : sub10 [-1, 1, -4] = true := by decide +kernel
theorem sub10_227 : sub10 [-1, 1, -3] = true := by decide +kernel
theorem sub10_228 : sub10 [-1, 1, -2] = true := by decide +kernel
theorem sub10_229 : sub10 [-1, 1, -1] = true := by decide +kernel
theorem sub10_230 : sub10 [-1, 1, 0] = true := by decide +kernel
theorem sub10_231 : sub10 [-1, 1, 1] = true := by decide +kernel
theorem sub10_232 : sub10 [-1, 1, 2] = true := by decide +kernel
theorem sub10_233 : sub10 [-1, 1, 3] = true := by decide +kernel
theorem sub10_234 : sub10 [-1, 1, 4] = true := by decide +kernel
theorem sub10_235 : sub10 [-1, 1, 5] = true := by decide +kernel
theorem sub10_236 : sub10 [-1, 1, 6] = true := by decide +kernel
theorem sub10_237 : sub10 [-1, 1, 7] = true := by decide +kernel
theorem sub10_238 : sub10 [-1, 2, -7] = true := by decide +kernel
theorem sub10_239 : sub10 [-1, 2, -6] = true := by decide +kernel
theorem sub10_240 : sub10 [-1, 2, -5] = true := by decide +kernel
theorem sub10_241 : sub10 [-1, 2, -4] = true := by decide +kernel
theorem sub10_242 : sub10 [-1, 2, -3] = true := by decide +kernel
theorem sub10_243 : sub10 [-1, 2, -2] = true := by decide +kernel
theorem sub10_244 : sub10 [-1, 2, -1] = true := by decide +kernel
theorem sub10_245 : sub10 [-1, 2, 0] = true := by decide +kernel
theorem sub10_246 : sub10 [-1, 2, 1] = true := by decide +kernel
theorem sub10_247 : sub10 [-1, 2, 2] = true := by decide +kernel
theorem sub10_248 : sub10 [-1, 2, 3] = true := by decide +kernel
theorem sub10_249 : sub10 [-1, 2, 4] = true := by decide +kernel
theorem sub10_250 : sub10 [-1, 2, 5] = true := by decide +kernel
theorem sub10_251 : sub10 [-1, 2, 6] = true := by decide +kernel
theorem sub10_252 : sub10 [-1, 3] = true := by decide +kernel
theorem sub10_253 : sub10 [-1, 4] = true := by decide +kernel
theorem sub10_254 : sub10 [-1, 5] = true := by decide +kernel
theorem sub10_255 : sub10 [0, -6] = true := by decide +kernel
theorem sb10_7 : ∀ q ∈ blk10_7, sub10 q = true := by
  unfold blk10_7
  exact List.forall_mem_cons.2 ⟨sub10_224, List.forall_mem_cons.2 ⟨sub10_225, List.forall_mem_cons.2 ⟨sub10_226, List.forall_mem_cons.2 ⟨sub10_227, List.forall_mem_cons.2 ⟨sub10_228, List.forall_mem_cons.2 ⟨sub10_229, List.forall_mem_cons.2 ⟨sub10_230, List.forall_mem_cons.2 ⟨sub10_231, List.forall_mem_cons.2 ⟨sub10_232, List.forall_mem_cons.2 ⟨sub10_233, List.forall_mem_cons.2 ⟨sub10_234, List.forall_mem_cons.2 ⟨sub10_235, List.forall_mem_cons.2 ⟨sub10_236, List.forall_mem_cons.2 ⟨sub10_237, List.forall_mem_cons.2 ⟨sub10_238, List.forall_mem_cons.2 ⟨sub10_239, List.forall_mem_cons.2 ⟨sub10_240, List.forall_mem_cons.2 ⟨sub10_241, List.forall_mem_cons.2 ⟨sub10_242, List.forall_mem_cons.2 ⟨sub10_243, List.forall_mem_cons.2 ⟨sub10_244, List.forall_mem_cons.2 ⟨sub10_245, List.forall_mem_cons.2 ⟨sub10_246, List.forall_mem_cons.2 ⟨sub10_247, List.forall_mem_cons.2 ⟨sub10_248, List.forall_mem_cons.2 ⟨sub10_249, List.forall_mem_cons.2 ⟨sub10_250, List.forall_mem_cons.2 ⟨sub10_251, List.forall_mem_cons.2 ⟨sub10_252, List.forall_mem_cons.2 ⟨sub10_253, List.forall_mem_cons.2 ⟨sub10_254, List.forall_mem_cons.2 ⟨sub10_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_256 : sub10 [0, -5] = true := by decide +kernel
theorem sub10_257 : sub10 [0, -4] = true := by decide +kernel
theorem sub10_258 : sub10 [0, -3, -7] = true := by decide +kernel
theorem sub10_259 : sub10 [0, -3, -6] = true := by decide +kernel
theorem sub10_260 : sub10 [0, -3, -5] = true := by decide +kernel
theorem sub10_261 : sub10 [0, -3, -4] = true := by decide +kernel
theorem sub10_262 : sub10 [0, -3, -3] = true := by decide +kernel
theorem sub10_263 : sub10 [0, -3, -2] = true := by decide +kernel
theorem sub10_264 : sub10 [0, -3, -1] = true := by decide +kernel
theorem sub10_265 : sub10 [0, -3, 0] = true := by decide +kernel
theorem sub10_266 : sub10 [0, -3, 1] = true := by decide +kernel
theorem sub10_267 : sub10 [0, -3, 2] = true := by decide +kernel
theorem sub10_268 : sub10 [0, -3, 3] = true := by decide +kernel
theorem sub10_269 : sub10 [0, -3, 4] = true := by decide +kernel
theorem sub10_270 : sub10 [0, -3, 5] = true := by decide +kernel
theorem sub10_271 : sub10 [0, -3, 6] = true := by decide +kernel
theorem sub10_272 : sub10 [0, -2, -8] = true := by decide +kernel
theorem sub10_273 : sub10 [0, -2, -7] = true := by decide +kernel
theorem sub10_274 : sub10 [0, -2, -6] = true := by decide +kernel
theorem sub10_275 : sub10 [0, -2, -5] = true := by decide +kernel
theorem sub10_276 : sub10 [0, -2, -4] = true := by decide +kernel
theorem sub10_277 : sub10 [0, -2, -3] = true := by decide +kernel
theorem sub10_278 : sub10 [0, -2, -2] = true := by decide +kernel
theorem sub10_279 : sub10 [0, -2, -1] = true := by decide +kernel
theorem sub10_280 : sub10 [0, -2, 0] = true := by decide +kernel
theorem sub10_281 : sub10 [0, -2, 1] = true := by decide +kernel
theorem sub10_282 : sub10 [0, -2, 2] = true := by decide +kernel
theorem sub10_283 : sub10 [0, -2, 3] = true := by decide +kernel
theorem sub10_284 : sub10 [0, -2, 4] = true := by decide +kernel
theorem sub10_285 : sub10 [0, -2, 5] = true := by decide +kernel
theorem sub10_286 : sub10 [0, -2, 6] = true := by decide +kernel
theorem sub10_287 : sub10 [0, -1, -8] = true := by decide +kernel
theorem sb10_8 : ∀ q ∈ blk10_8, sub10 q = true := by
  unfold blk10_8
  exact List.forall_mem_cons.2 ⟨sub10_256, List.forall_mem_cons.2 ⟨sub10_257, List.forall_mem_cons.2 ⟨sub10_258, List.forall_mem_cons.2 ⟨sub10_259, List.forall_mem_cons.2 ⟨sub10_260, List.forall_mem_cons.2 ⟨sub10_261, List.forall_mem_cons.2 ⟨sub10_262, List.forall_mem_cons.2 ⟨sub10_263, List.forall_mem_cons.2 ⟨sub10_264, List.forall_mem_cons.2 ⟨sub10_265, List.forall_mem_cons.2 ⟨sub10_266, List.forall_mem_cons.2 ⟨sub10_267, List.forall_mem_cons.2 ⟨sub10_268, List.forall_mem_cons.2 ⟨sub10_269, List.forall_mem_cons.2 ⟨sub10_270, List.forall_mem_cons.2 ⟨sub10_271, List.forall_mem_cons.2 ⟨sub10_272, List.forall_mem_cons.2 ⟨sub10_273, List.forall_mem_cons.2 ⟨sub10_274, List.forall_mem_cons.2 ⟨sub10_275, List.forall_mem_cons.2 ⟨sub10_276, List.forall_mem_cons.2 ⟨sub10_277, List.forall_mem_cons.2 ⟨sub10_278, List.forall_mem_cons.2 ⟨sub10_279, List.forall_mem_cons.2 ⟨sub10_280, List.forall_mem_cons.2 ⟨sub10_281, List.forall_mem_cons.2 ⟨sub10_282, List.forall_mem_cons.2 ⟨sub10_283, List.forall_mem_cons.2 ⟨sub10_284, List.forall_mem_cons.2 ⟨sub10_285, List.forall_mem_cons.2 ⟨sub10_286, List.forall_mem_cons.2 ⟨sub10_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_288 : sub10 [0, -1, -7] = true := by decide +kernel
theorem sub10_289 : sub10 [0, -1, -6] = true := by decide +kernel
theorem sub10_290 : sub10 [0, -1, -5] = true := by decide +kernel
theorem sub10_291 : sub10 [0, -1, -4] = true := by decide +kernel
theorem sub10_292 : sub10 [0, -1, -3] = true := by decide +kernel
theorem sub10_293 : sub10 [0, -1, -2] = true := by decide +kernel
theorem sub10_294 : sub10 [0, -1, -1] = true := by decide +kernel
theorem sub10_295 : sub10 [0, -1, 0] = true := by decide +kernel
theorem sub10_296 : sub10 [0, -1, 1] = true := by decide +kernel
theorem sub10_297 : sub10 [0, -1, 2] = true := by decide +kernel
theorem sub10_298 : sub10 [0, -1, 3] = true := by decide +kernel
theorem sub10_299 : sub10 [0, -1, 4] = true := by decide +kernel
theorem sub10_300 : sub10 [0, -1, 5] = true := by decide +kernel
theorem sub10_301 : sub10 [0, -1, 6] = true := by decide +kernel
theorem sub10_302 : sub10 [0, -1, 7] = true := by decide +kernel
theorem sub10_303 : sub10 [0, 0, -8] = true := by decide +kernel
theorem sub10_304 : sub10 [0, 0, -7] = true := by decide +kernel
theorem sub10_305 : sub10 [0, 0, -6] = true := by decide +kernel
theorem sub10_306 : sub10 [0, 0, -5] = true := by decide +kernel
theorem sub10_307 : sub10 [0, 0, -4] = true := by decide +kernel
theorem sub10_308 : sub10 [0, 0, -3] = true := by decide +kernel
theorem sub10_309 : sub10 [0, 0, -2] = true := by decide +kernel
theorem sub10_310 : sub10 [0, 0, -1] = true := by decide +kernel
theorem sub10_311 : sub10 [0, 0, 0] = true := by decide +kernel
theorem sub10_312 : sub10 [0, 0, 1] = true := by decide +kernel
theorem sub10_313 : sub10 [0, 0, 2] = true := by decide +kernel
theorem sub10_314 : sub10 [0, 0, 3] = true := by decide +kernel
theorem sub10_315 : sub10 [0, 0, 4] = true := by decide +kernel
theorem sub10_316 : sub10 [0, 0, 5] = true := by decide +kernel
theorem sub10_317 : sub10 [0, 0, 6] = true := by decide +kernel
theorem sub10_318 : sub10 [0, 0, 7] = true := by decide +kernel
theorem sub10_319 : sub10 [0, 1, -8] = true := by decide +kernel
theorem sb10_9 : ∀ q ∈ blk10_9, sub10 q = true := by
  unfold blk10_9
  exact List.forall_mem_cons.2 ⟨sub10_288, List.forall_mem_cons.2 ⟨sub10_289, List.forall_mem_cons.2 ⟨sub10_290, List.forall_mem_cons.2 ⟨sub10_291, List.forall_mem_cons.2 ⟨sub10_292, List.forall_mem_cons.2 ⟨sub10_293, List.forall_mem_cons.2 ⟨sub10_294, List.forall_mem_cons.2 ⟨sub10_295, List.forall_mem_cons.2 ⟨sub10_296, List.forall_mem_cons.2 ⟨sub10_297, List.forall_mem_cons.2 ⟨sub10_298, List.forall_mem_cons.2 ⟨sub10_299, List.forall_mem_cons.2 ⟨sub10_300, List.forall_mem_cons.2 ⟨sub10_301, List.forall_mem_cons.2 ⟨sub10_302, List.forall_mem_cons.2 ⟨sub10_303, List.forall_mem_cons.2 ⟨sub10_304, List.forall_mem_cons.2 ⟨sub10_305, List.forall_mem_cons.2 ⟨sub10_306, List.forall_mem_cons.2 ⟨sub10_307, List.forall_mem_cons.2 ⟨sub10_308, List.forall_mem_cons.2 ⟨sub10_309, List.forall_mem_cons.2 ⟨sub10_310, List.forall_mem_cons.2 ⟨sub10_311, List.forall_mem_cons.2 ⟨sub10_312, List.forall_mem_cons.2 ⟨sub10_313, List.forall_mem_cons.2 ⟨sub10_314, List.forall_mem_cons.2 ⟨sub10_315, List.forall_mem_cons.2 ⟨sub10_316, List.forall_mem_cons.2 ⟨sub10_317, List.forall_mem_cons.2 ⟨sub10_318, List.forall_mem_cons.2 ⟨sub10_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_320 : sub10 [0, 1, -7] = true := by decide +kernel
theorem sub10_321 : sub10 [0, 1, -6] = true := by decide +kernel
theorem sub10_322 : sub10 [0, 1, -5] = true := by decide +kernel
theorem sub10_323 : sub10 [0, 1, -4] = true := by decide +kernel
theorem sub10_324 : sub10 [0, 1, -3] = true := by decide +kernel
theorem sub10_325 : sub10 [0, 1, -2] = true := by decide +kernel
theorem sub10_326 : sub10 [0, 1, -1] = true := by decide +kernel
theorem sub10_327 : sub10 [0, 1, 0] = true := by decide +kernel
theorem sub10_328 : sub10 [0, 1, 1] = true := by decide +kernel
theorem sub10_329 : sub10 [0, 1, 2] = true := by decide +kernel
theorem sub10_330 : sub10 [0, 1, 3] = true := by decide +kernel
theorem sub10_331 : sub10 [0, 1, 4] = true := by decide +kernel
theorem sub10_332 : sub10 [0, 1, 5] = true := by decide +kernel
theorem sub10_333 : sub10 [0, 1, 6] = true := by decide +kernel
theorem sub10_334 : sub10 [0, 1, 7] = true := by decide +kernel
theorem sub10_335 : sub10 [0, 2, -7] = true := by decide +kernel
theorem sub10_336 : sub10 [0, 2, -6] = true := by decide +kernel
theorem sub10_337 : sub10 [0, 2, -5] = true := by decide +kernel
theorem sub10_338 : sub10 [0, 2, -4] = true := by decide +kernel
theorem sub10_339 : sub10 [0, 2, -3] = true := by decide +kernel
theorem sub10_340 : sub10 [0, 2, -2] = true := by decide +kernel
theorem sub10_341 : sub10 [0, 2, -1] = true := by decide +kernel
theorem sub10_342 : sub10 [0, 2, 0] = true := by decide +kernel
theorem sub10_343 : sub10 [0, 2, 1] = true := by decide +kernel
theorem sub10_344 : sub10 [0, 2, 2] = true := by decide +kernel
theorem sub10_345 : sub10 [0, 2, 3] = true := by decide +kernel
theorem sub10_346 : sub10 [0, 2, 4] = true := by decide +kernel
theorem sub10_347 : sub10 [0, 2, 5] = true := by decide +kernel
theorem sub10_348 : sub10 [0, 2, 6] = true := by decide +kernel
theorem sub10_349 : sub10 [0, 2, 7] = true := by decide +kernel
theorem sub10_350 : sub10 [0, 3, -7] = true := by decide +kernel
theorem sub10_351 : sub10 [0, 3, -6] = true := by decide +kernel
theorem sb10_10 : ∀ q ∈ blk10_10, sub10 q = true := by
  unfold blk10_10
  exact List.forall_mem_cons.2 ⟨sub10_320, List.forall_mem_cons.2 ⟨sub10_321, List.forall_mem_cons.2 ⟨sub10_322, List.forall_mem_cons.2 ⟨sub10_323, List.forall_mem_cons.2 ⟨sub10_324, List.forall_mem_cons.2 ⟨sub10_325, List.forall_mem_cons.2 ⟨sub10_326, List.forall_mem_cons.2 ⟨sub10_327, List.forall_mem_cons.2 ⟨sub10_328, List.forall_mem_cons.2 ⟨sub10_329, List.forall_mem_cons.2 ⟨sub10_330, List.forall_mem_cons.2 ⟨sub10_331, List.forall_mem_cons.2 ⟨sub10_332, List.forall_mem_cons.2 ⟨sub10_333, List.forall_mem_cons.2 ⟨sub10_334, List.forall_mem_cons.2 ⟨sub10_335, List.forall_mem_cons.2 ⟨sub10_336, List.forall_mem_cons.2 ⟨sub10_337, List.forall_mem_cons.2 ⟨sub10_338, List.forall_mem_cons.2 ⟨sub10_339, List.forall_mem_cons.2 ⟨sub10_340, List.forall_mem_cons.2 ⟨sub10_341, List.forall_mem_cons.2 ⟨sub10_342, List.forall_mem_cons.2 ⟨sub10_343, List.forall_mem_cons.2 ⟨sub10_344, List.forall_mem_cons.2 ⟨sub10_345, List.forall_mem_cons.2 ⟨sub10_346, List.forall_mem_cons.2 ⟨sub10_347, List.forall_mem_cons.2 ⟨sub10_348, List.forall_mem_cons.2 ⟨sub10_349, List.forall_mem_cons.2 ⟨sub10_350, List.forall_mem_cons.2 ⟨sub10_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_352 : sub10 [0, 3, -5] = true := by decide +kernel
theorem sub10_353 : sub10 [0, 3, -4] = true := by decide +kernel
theorem sub10_354 : sub10 [0, 3, -3] = true := by decide +kernel
theorem sub10_355 : sub10 [0, 3, -2] = true := by decide +kernel
theorem sub10_356 : sub10 [0, 3, -1] = true := by decide +kernel
theorem sub10_357 : sub10 [0, 3, 0] = true := by decide +kernel
theorem sub10_358 : sub10 [0, 3, 1] = true := by decide +kernel
theorem sub10_359 : sub10 [0, 3, 2] = true := by decide +kernel
theorem sub10_360 : sub10 [0, 3, 3] = true := by decide +kernel
theorem sub10_361 : sub10 [0, 3, 4] = true := by decide +kernel
theorem sub10_362 : sub10 [0, 3, 5] = true := by decide +kernel
theorem sub10_363 : sub10 [0, 3, 6] = true := by decide +kernel
theorem sub10_364 : sub10 [0, 4] = true := by decide +kernel
theorem sub10_365 : sub10 [0, 5] = true := by decide +kernel
theorem sub10_366 : sub10 [1, -6] = true := by decide +kernel
theorem sub10_367 : sub10 [1, -5] = true := by decide +kernel
theorem sub10_368 : sub10 [1, -4] = true := by decide +kernel
theorem sub10_369 : sub10 [1, -3] = true := by decide +kernel
theorem sub10_370 : sub10 [1, -2, -7] = true := by decide +kernel
theorem sub10_371 : sub10 [1, -2, -6] = true := by decide +kernel
theorem sub10_372 : sub10 [1, -2, -5] = true := by decide +kernel
theorem sub10_373 : sub10 [1, -2, -4] = true := by decide +kernel
theorem sub10_374 : sub10 [1, -2, -3] = true := by decide +kernel
theorem sub10_375 : sub10 [1, -2, -2] = true := by decide +kernel
theorem sub10_376 : sub10 [1, -2, -1] = true := by decide +kernel
theorem sub10_377 : sub10 [1, -2, 0] = true := by decide +kernel
theorem sub10_378 : sub10 [1, -2, 1] = true := by decide +kernel
theorem sub10_379 : sub10 [1, -2, 2] = true := by decide +kernel
theorem sub10_380 : sub10 [1, -2, 3] = true := by decide +kernel
theorem sub10_381 : sub10 [1, -2, 4] = true := by decide +kernel
theorem sub10_382 : sub10 [1, -2, 5] = true := by decide +kernel
theorem sub10_383 : sub10 [1, -2, 6] = true := by decide +kernel
theorem sb10_11 : ∀ q ∈ blk10_11, sub10 q = true := by
  unfold blk10_11
  exact List.forall_mem_cons.2 ⟨sub10_352, List.forall_mem_cons.2 ⟨sub10_353, List.forall_mem_cons.2 ⟨sub10_354, List.forall_mem_cons.2 ⟨sub10_355, List.forall_mem_cons.2 ⟨sub10_356, List.forall_mem_cons.2 ⟨sub10_357, List.forall_mem_cons.2 ⟨sub10_358, List.forall_mem_cons.2 ⟨sub10_359, List.forall_mem_cons.2 ⟨sub10_360, List.forall_mem_cons.2 ⟨sub10_361, List.forall_mem_cons.2 ⟨sub10_362, List.forall_mem_cons.2 ⟨sub10_363, List.forall_mem_cons.2 ⟨sub10_364, List.forall_mem_cons.2 ⟨sub10_365, List.forall_mem_cons.2 ⟨sub10_366, List.forall_mem_cons.2 ⟨sub10_367, List.forall_mem_cons.2 ⟨sub10_368, List.forall_mem_cons.2 ⟨sub10_369, List.forall_mem_cons.2 ⟨sub10_370, List.forall_mem_cons.2 ⟨sub10_371, List.forall_mem_cons.2 ⟨sub10_372, List.forall_mem_cons.2 ⟨sub10_373, List.forall_mem_cons.2 ⟨sub10_374, List.forall_mem_cons.2 ⟨sub10_375, List.forall_mem_cons.2 ⟨sub10_376, List.forall_mem_cons.2 ⟨sub10_377, List.forall_mem_cons.2 ⟨sub10_378, List.forall_mem_cons.2 ⟨sub10_379, List.forall_mem_cons.2 ⟨sub10_380, List.forall_mem_cons.2 ⟨sub10_381, List.forall_mem_cons.2 ⟨sub10_382, List.forall_mem_cons.2 ⟨sub10_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_384 : sub10 [1, -1, -8] = true := by decide +kernel
theorem sub10_385 : sub10 [1, -1, -7] = true := by decide +kernel
theorem sub10_386 : sub10 [1, -1, -6] = true := by decide +kernel
theorem sub10_387 : sub10 [1, -1, -5] = true := by decide +kernel
theorem sub10_388 : sub10 [1, -1, -4] = true := by decide +kernel
theorem sub10_389 : sub10 [1, -1, -3] = true := by decide +kernel
theorem sub10_390 : sub10 [1, -1, -2] = true := by decide +kernel
theorem sub10_391 : sub10 [1, -1, -1] = true := by decide +kernel
theorem sub10_392 : sub10 [1, -1, 0] = true := by decide +kernel
theorem sub10_393 : sub10 [1, -1, 1] = true := by decide +kernel
theorem sub10_394 : sub10 [1, -1, 2] = true := by decide +kernel
theorem sub10_395 : sub10 [1, -1, 3] = true := by decide +kernel
theorem sub10_396 : sub10 [1, -1, 4] = true := by decide +kernel
theorem sub10_397 : sub10 [1, -1, 5] = true := by decide +kernel
theorem sub10_398 : sub10 [1, -1, 6] = true := by decide +kernel
theorem sub10_399 : sub10 [1, 0, -8] = true := by decide +kernel
theorem sub10_400 : sub10 [1, 0, -7] = true := by decide +kernel
theorem sub10_401 : sub10 [1, 0, -6] = true := by decide +kernel
theorem sub10_402 : sub10 [1, 0, -5] = true := by decide +kernel
theorem sub10_403 : sub10 [1, 0, -4] = true := by decide +kernel
theorem sub10_404 : sub10 [1, 0, -3] = true := by decide +kernel
theorem sub10_405 : sub10 [1, 0, -2] = true := by decide +kernel
theorem sub10_406 : sub10 [1, 0, -1] = true := by decide +kernel
theorem sub10_407 : sub10 [1, 0, 0] = true := by decide +kernel
theorem sub10_408 : sub10 [1, 0, 1] = true := by decide +kernel
theorem sub10_409 : sub10 [1, 0, 2] = true := by decide +kernel
theorem sub10_410 : sub10 [1, 0, 3] = true := by decide +kernel
theorem sub10_411 : sub10 [1, 0, 4] = true := by decide +kernel
theorem sub10_412 : sub10 [1, 0, 5] = true := by decide +kernel
theorem sub10_413 : sub10 [1, 0, 6] = true := by decide +kernel
theorem sub10_414 : sub10 [1, 0, 7] = true := by decide +kernel
theorem sub10_415 : sub10 [1, 1, -8] = true := by decide +kernel
theorem sb10_12 : ∀ q ∈ blk10_12, sub10 q = true := by
  unfold blk10_12
  exact List.forall_mem_cons.2 ⟨sub10_384, List.forall_mem_cons.2 ⟨sub10_385, List.forall_mem_cons.2 ⟨sub10_386, List.forall_mem_cons.2 ⟨sub10_387, List.forall_mem_cons.2 ⟨sub10_388, List.forall_mem_cons.2 ⟨sub10_389, List.forall_mem_cons.2 ⟨sub10_390, List.forall_mem_cons.2 ⟨sub10_391, List.forall_mem_cons.2 ⟨sub10_392, List.forall_mem_cons.2 ⟨sub10_393, List.forall_mem_cons.2 ⟨sub10_394, List.forall_mem_cons.2 ⟨sub10_395, List.forall_mem_cons.2 ⟨sub10_396, List.forall_mem_cons.2 ⟨sub10_397, List.forall_mem_cons.2 ⟨sub10_398, List.forall_mem_cons.2 ⟨sub10_399, List.forall_mem_cons.2 ⟨sub10_400, List.forall_mem_cons.2 ⟨sub10_401, List.forall_mem_cons.2 ⟨sub10_402, List.forall_mem_cons.2 ⟨sub10_403, List.forall_mem_cons.2 ⟨sub10_404, List.forall_mem_cons.2 ⟨sub10_405, List.forall_mem_cons.2 ⟨sub10_406, List.forall_mem_cons.2 ⟨sub10_407, List.forall_mem_cons.2 ⟨sub10_408, List.forall_mem_cons.2 ⟨sub10_409, List.forall_mem_cons.2 ⟨sub10_410, List.forall_mem_cons.2 ⟨sub10_411, List.forall_mem_cons.2 ⟨sub10_412, List.forall_mem_cons.2 ⟨sub10_413, List.forall_mem_cons.2 ⟨sub10_414, List.forall_mem_cons.2 ⟨sub10_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_416 : sub10 [1, 1, -7] = true := by decide +kernel
theorem sub10_417 : sub10 [1, 1, -6] = true := by decide +kernel
theorem sub10_418 : sub10 [1, 1, -5] = true := by decide +kernel
theorem sub10_419 : sub10 [1, 1, -4] = true := by decide +kernel
theorem sub10_420 : sub10 [1, 1, -3] = true := by decide +kernel
theorem sub10_421 : sub10 [1, 1, -2] = true := by decide +kernel
theorem sub10_422 : sub10 [1, 1, -1] = true := by decide +kernel
theorem sub10_423 : sub10 [1, 1, 0] = true := by decide +kernel
theorem sub10_424 : sub10 [1, 1, 1] = true := by decide +kernel
theorem sub10_425 : sub10 [1, 1, 2] = true := by decide +kernel
theorem sub10_426 : sub10 [1, 1, 3] = true := by decide +kernel
theorem sub10_427 : sub10 [1, 1, 4] = true := by decide +kernel
theorem sub10_428 : sub10 [1, 1, 5] = true := by decide +kernel
theorem sub10_429 : sub10 [1, 1, 6] = true := by decide +kernel
theorem sub10_430 : sub10 [1, 1, 7] = true := by decide +kernel
theorem sub10_431 : sub10 [1, 2, -7] = true := by decide +kernel
theorem sub10_432 : sub10 [1, 2, -6] = true := by decide +kernel
theorem sub10_433 : sub10 [1, 2, -5] = true := by decide +kernel
theorem sub10_434 : sub10 [1, 2, -4] = true := by decide +kernel
theorem sub10_435 : sub10 [1, 2, -3] = true := by decide +kernel
theorem sub10_436 : sub10 [1, 2, -2] = true := by decide +kernel
theorem sub10_437 : sub10 [1, 2, -1] = true := by decide +kernel
theorem sub10_438 : sub10 [1, 2, 0] = true := by decide +kernel
theorem sub10_439 : sub10 [1, 2, 1] = true := by decide +kernel
theorem sub10_440 : sub10 [1, 2, 2] = true := by decide +kernel
theorem sub10_441 : sub10 [1, 2, 3] = true := by decide +kernel
theorem sub10_442 : sub10 [1, 2, 4] = true := by decide +kernel
theorem sub10_443 : sub10 [1, 2, 5] = true := by decide +kernel
theorem sub10_444 : sub10 [1, 2, 6] = true := by decide +kernel
theorem sub10_445 : sub10 [1, 3, -7] = true := by decide +kernel
theorem sub10_446 : sub10 [1, 3, -6] = true := by decide +kernel
theorem sub10_447 : sub10 [1, 3, -5] = true := by decide +kernel
theorem sb10_13 : ∀ q ∈ blk10_13, sub10 q = true := by
  unfold blk10_13
  exact List.forall_mem_cons.2 ⟨sub10_416, List.forall_mem_cons.2 ⟨sub10_417, List.forall_mem_cons.2 ⟨sub10_418, List.forall_mem_cons.2 ⟨sub10_419, List.forall_mem_cons.2 ⟨sub10_420, List.forall_mem_cons.2 ⟨sub10_421, List.forall_mem_cons.2 ⟨sub10_422, List.forall_mem_cons.2 ⟨sub10_423, List.forall_mem_cons.2 ⟨sub10_424, List.forall_mem_cons.2 ⟨sub10_425, List.forall_mem_cons.2 ⟨sub10_426, List.forall_mem_cons.2 ⟨sub10_427, List.forall_mem_cons.2 ⟨sub10_428, List.forall_mem_cons.2 ⟨sub10_429, List.forall_mem_cons.2 ⟨sub10_430, List.forall_mem_cons.2 ⟨sub10_431, List.forall_mem_cons.2 ⟨sub10_432, List.forall_mem_cons.2 ⟨sub10_433, List.forall_mem_cons.2 ⟨sub10_434, List.forall_mem_cons.2 ⟨sub10_435, List.forall_mem_cons.2 ⟨sub10_436, List.forall_mem_cons.2 ⟨sub10_437, List.forall_mem_cons.2 ⟨sub10_438, List.forall_mem_cons.2 ⟨sub10_439, List.forall_mem_cons.2 ⟨sub10_440, List.forall_mem_cons.2 ⟨sub10_441, List.forall_mem_cons.2 ⟨sub10_442, List.forall_mem_cons.2 ⟨sub10_443, List.forall_mem_cons.2 ⟨sub10_444, List.forall_mem_cons.2 ⟨sub10_445, List.forall_mem_cons.2 ⟨sub10_446, List.forall_mem_cons.2 ⟨sub10_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_448 : sub10 [1, 3, -4] = true := by decide +kernel
theorem sub10_449 : sub10 [1, 3, -3] = true := by decide +kernel
theorem sub10_450 : sub10 [1, 3, -2] = true := by decide +kernel
theorem sub10_451 : sub10 [1, 3, -1] = true := by decide +kernel
theorem sub10_452 : sub10 [1, 3, 0] = true := by decide +kernel
theorem sub10_453 : sub10 [1, 3, 1] = true := by decide +kernel
theorem sub10_454 : sub10 [1, 3, 2] = true := by decide +kernel
theorem sub10_455 : sub10 [1, 3, 3] = true := by decide +kernel
theorem sub10_456 : sub10 [1, 3, 4] = true := by decide +kernel
theorem sub10_457 : sub10 [1, 3, 5] = true := by decide +kernel
theorem sub10_458 : sub10 [1, 3, 6] = true := by decide +kernel
theorem sub10_459 : sub10 [1, 4] = true := by decide +kernel
theorem sub10_460 : sub10 [1, 5] = true := by decide +kernel
theorem sub10_461 : sub10 [2, -6] = true := by decide +kernel
theorem sub10_462 : sub10 [2, -5] = true := by decide +kernel
theorem sub10_463 : sub10 [2, -4] = true := by decide +kernel
theorem sub10_464 : sub10 [2, -3] = true := by decide +kernel
theorem sub10_465 : sub10 [2, -2, -7] = true := by decide +kernel
theorem sub10_466 : sub10 [2, -2, -6] = true := by decide +kernel
theorem sub10_467 : sub10 [2, -2, -5] = true := by decide +kernel
theorem sub10_468 : sub10 [2, -2, -4] = true := by decide +kernel
theorem sub10_469 : sub10 [2, -2, -3] = true := by decide +kernel
theorem sub10_470 : sub10 [2, -2, -2] = true := by decide +kernel
theorem sub10_471 : sub10 [2, -2, -1] = true := by decide +kernel
theorem sub10_472 : sub10 [2, -2, 0] = true := by decide +kernel
theorem sub10_473 : sub10 [2, -2, 1] = true := by decide +kernel
theorem sub10_474 : sub10 [2, -2, 2] = true := by decide +kernel
theorem sub10_475 : sub10 [2, -2, 3] = true := by decide +kernel
theorem sub10_476 : sub10 [2, -2, 4] = true := by decide +kernel
theorem sub10_477 : sub10 [2, -2, 5] = true := by decide +kernel
theorem sub10_478 : sub10 [2, -2, 6] = true := by decide +kernel
theorem sub10_479 : sub10 [2, -1, -8] = true := by decide +kernel
theorem sb10_14 : ∀ q ∈ blk10_14, sub10 q = true := by
  unfold blk10_14
  exact List.forall_mem_cons.2 ⟨sub10_448, List.forall_mem_cons.2 ⟨sub10_449, List.forall_mem_cons.2 ⟨sub10_450, List.forall_mem_cons.2 ⟨sub10_451, List.forall_mem_cons.2 ⟨sub10_452, List.forall_mem_cons.2 ⟨sub10_453, List.forall_mem_cons.2 ⟨sub10_454, List.forall_mem_cons.2 ⟨sub10_455, List.forall_mem_cons.2 ⟨sub10_456, List.forall_mem_cons.2 ⟨sub10_457, List.forall_mem_cons.2 ⟨sub10_458, List.forall_mem_cons.2 ⟨sub10_459, List.forall_mem_cons.2 ⟨sub10_460, List.forall_mem_cons.2 ⟨sub10_461, List.forall_mem_cons.2 ⟨sub10_462, List.forall_mem_cons.2 ⟨sub10_463, List.forall_mem_cons.2 ⟨sub10_464, List.forall_mem_cons.2 ⟨sub10_465, List.forall_mem_cons.2 ⟨sub10_466, List.forall_mem_cons.2 ⟨sub10_467, List.forall_mem_cons.2 ⟨sub10_468, List.forall_mem_cons.2 ⟨sub10_469, List.forall_mem_cons.2 ⟨sub10_470, List.forall_mem_cons.2 ⟨sub10_471, List.forall_mem_cons.2 ⟨sub10_472, List.forall_mem_cons.2 ⟨sub10_473, List.forall_mem_cons.2 ⟨sub10_474, List.forall_mem_cons.2 ⟨sub10_475, List.forall_mem_cons.2 ⟨sub10_476, List.forall_mem_cons.2 ⟨sub10_477, List.forall_mem_cons.2 ⟨sub10_478, List.forall_mem_cons.2 ⟨sub10_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_480 : sub10 [2, -1, -7] = true := by decide +kernel
theorem sub10_481 : sub10 [2, -1, -6] = true := by decide +kernel
theorem sub10_482 : sub10 [2, -1, -5] = true := by decide +kernel
theorem sub10_483 : sub10 [2, -1, -4] = true := by decide +kernel
theorem sub10_484 : sub10 [2, -1, -3] = true := by decide +kernel
theorem sub10_485 : sub10 [2, -1, -2] = true := by decide +kernel
theorem sub10_486 : sub10 [2, -1, -1] = true := by decide +kernel
theorem sub10_487 : sub10 [2, -1, 0] = true := by decide +kernel
theorem sub10_488 : sub10 [2, -1, 1] = true := by decide +kernel
theorem sub10_489 : sub10 [2, -1, 2] = true := by decide +kernel
theorem sub10_490 : sub10 [2, -1, 3] = true := by decide +kernel
theorem sub10_491 : sub10 [2, -1, 4] = true := by decide +kernel
theorem sub10_492 : sub10 [2, -1, 5] = true := by decide +kernel
theorem sub10_493 : sub10 [2, -1, 6] = true := by decide +kernel
theorem sub10_494 : sub10 [2, 0, -8] = true := by decide +kernel
theorem sub10_495 : sub10 [2, 0, -7] = true := by decide +kernel
theorem sub10_496 : sub10 [2, 0, -6] = true := by decide +kernel
theorem sub10_497 : sub10 [2, 0, -5] = true := by decide +kernel
theorem sub10_498 : sub10 [2, 0, -4] = true := by decide +kernel
theorem sub10_499 : sub10 [2, 0, -3] = true := by decide +kernel
theorem sub10_500 : sub10 [2, 0, -2] = true := by decide +kernel
theorem sub10_501 : sub10 [2, 0, -1] = true := by decide +kernel
theorem sub10_502 : sub10 [2, 0, 0] = true := by decide +kernel
theorem sub10_503 : sub10 [2, 0, 1] = true := by decide +kernel
theorem sub10_504 : sub10 [2, 0, 2] = true := by decide +kernel
theorem sub10_505 : sub10 [2, 0, 3] = true := by decide +kernel
theorem sub10_506 : sub10 [2, 0, 4] = true := by decide +kernel
theorem sub10_507 : sub10 [2, 0, 5] = true := by decide +kernel
theorem sub10_508 : sub10 [2, 0, 6] = true := by decide +kernel
theorem sub10_509 : sub10 [2, 1, -7] = true := by decide +kernel
theorem sub10_510 : sub10 [2, 1, -6] = true := by decide +kernel
theorem sub10_511 : sub10 [2, 1, -5] = true := by decide +kernel
theorem sb10_15 : ∀ q ∈ blk10_15, sub10 q = true := by
  unfold blk10_15
  exact List.forall_mem_cons.2 ⟨sub10_480, List.forall_mem_cons.2 ⟨sub10_481, List.forall_mem_cons.2 ⟨sub10_482, List.forall_mem_cons.2 ⟨sub10_483, List.forall_mem_cons.2 ⟨sub10_484, List.forall_mem_cons.2 ⟨sub10_485, List.forall_mem_cons.2 ⟨sub10_486, List.forall_mem_cons.2 ⟨sub10_487, List.forall_mem_cons.2 ⟨sub10_488, List.forall_mem_cons.2 ⟨sub10_489, List.forall_mem_cons.2 ⟨sub10_490, List.forall_mem_cons.2 ⟨sub10_491, List.forall_mem_cons.2 ⟨sub10_492, List.forall_mem_cons.2 ⟨sub10_493, List.forall_mem_cons.2 ⟨sub10_494, List.forall_mem_cons.2 ⟨sub10_495, List.forall_mem_cons.2 ⟨sub10_496, List.forall_mem_cons.2 ⟨sub10_497, List.forall_mem_cons.2 ⟨sub10_498, List.forall_mem_cons.2 ⟨sub10_499, List.forall_mem_cons.2 ⟨sub10_500, List.forall_mem_cons.2 ⟨sub10_501, List.forall_mem_cons.2 ⟨sub10_502, List.forall_mem_cons.2 ⟨sub10_503, List.forall_mem_cons.2 ⟨sub10_504, List.forall_mem_cons.2 ⟨sub10_505, List.forall_mem_cons.2 ⟨sub10_506, List.forall_mem_cons.2 ⟨sub10_507, List.forall_mem_cons.2 ⟨sub10_508, List.forall_mem_cons.2 ⟨sub10_509, List.forall_mem_cons.2 ⟨sub10_510, List.forall_mem_cons.2 ⟨sub10_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_512 : sub10 [2, 1, -4] = true := by decide +kernel
theorem sub10_513 : sub10 [2, 1, -3] = true := by decide +kernel
theorem sub10_514 : sub10 [2, 1, -2] = true := by decide +kernel
theorem sub10_515 : sub10 [2, 1, -1] = true := by decide +kernel
theorem sub10_516 : sub10 [2, 1, 0] = true := by decide +kernel
theorem sub10_517 : sub10 [2, 1, 1] = true := by decide +kernel
theorem sub10_518 : sub10 [2, 1, 2] = true := by decide +kernel
theorem sub10_519 : sub10 [2, 1, 3] = true := by decide +kernel
theorem sub10_520 : sub10 [2, 1, 4] = true := by decide +kernel
theorem sub10_521 : sub10 [2, 1, 5] = true := by decide +kernel
theorem sub10_522 : sub10 [2, 1, 6] = true := by decide +kernel
theorem sub10_523 : sub10 [2, 2, -7] = true := by decide +kernel
theorem sub10_524 : sub10 [2, 2, -6] = true := by decide +kernel
theorem sub10_525 : sub10 [2, 2, -5] = true := by decide +kernel
theorem sub10_526 : sub10 [2, 2, -4] = true := by decide +kernel
theorem sub10_527 : sub10 [2, 2, -3] = true := by decide +kernel
theorem sub10_528 : sub10 [2, 2, -2] = true := by decide +kernel
theorem sub10_529 : sub10 [2, 2, -1] = true := by decide +kernel
theorem sub10_530 : sub10 [2, 2, 0] = true := by decide +kernel
theorem sub10_531 : sub10 [2, 2, 1] = true := by decide +kernel
theorem sub10_532 : sub10 [2, 2, 2] = true := by decide +kernel
theorem sub10_533 : sub10 [2, 2, 3] = true := by decide +kernel
theorem sub10_534 : sub10 [2, 2, 4] = true := by decide +kernel
theorem sub10_535 : sub10 [2, 2, 5] = true := by decide +kernel
theorem sub10_536 : sub10 [2, 2, 6] = true := by decide +kernel
theorem sub10_537 : sub10 [2, 3] = true := by decide +kernel
theorem sub10_538 : sub10 [2, 4] = true := by decide +kernel
theorem sub10_539 : sub10 [2, 5] = true := by decide +kernel
theorem sub10_540 : sub10 [3, -5] = true := by decide +kernel
theorem sub10_541 : sub10 [3, -4] = true := by decide +kernel
theorem sub10_542 : sub10 [3, -3] = true := by decide +kernel
theorem sub10_543 : sub10 [3, -2] = true := by decide +kernel
theorem sb10_16 : ∀ q ∈ blk10_16, sub10 q = true := by
  unfold blk10_16
  exact List.forall_mem_cons.2 ⟨sub10_512, List.forall_mem_cons.2 ⟨sub10_513, List.forall_mem_cons.2 ⟨sub10_514, List.forall_mem_cons.2 ⟨sub10_515, List.forall_mem_cons.2 ⟨sub10_516, List.forall_mem_cons.2 ⟨sub10_517, List.forall_mem_cons.2 ⟨sub10_518, List.forall_mem_cons.2 ⟨sub10_519, List.forall_mem_cons.2 ⟨sub10_520, List.forall_mem_cons.2 ⟨sub10_521, List.forall_mem_cons.2 ⟨sub10_522, List.forall_mem_cons.2 ⟨sub10_523, List.forall_mem_cons.2 ⟨sub10_524, List.forall_mem_cons.2 ⟨sub10_525, List.forall_mem_cons.2 ⟨sub10_526, List.forall_mem_cons.2 ⟨sub10_527, List.forall_mem_cons.2 ⟨sub10_528, List.forall_mem_cons.2 ⟨sub10_529, List.forall_mem_cons.2 ⟨sub10_530, List.forall_mem_cons.2 ⟨sub10_531, List.forall_mem_cons.2 ⟨sub10_532, List.forall_mem_cons.2 ⟨sub10_533, List.forall_mem_cons.2 ⟨sub10_534, List.forall_mem_cons.2 ⟨sub10_535, List.forall_mem_cons.2 ⟨sub10_536, List.forall_mem_cons.2 ⟨sub10_537, List.forall_mem_cons.2 ⟨sub10_538, List.forall_mem_cons.2 ⟨sub10_539, List.forall_mem_cons.2 ⟨sub10_540, List.forall_mem_cons.2 ⟨sub10_541, List.forall_mem_cons.2 ⟨sub10_542, List.forall_mem_cons.2 ⟨sub10_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C105
