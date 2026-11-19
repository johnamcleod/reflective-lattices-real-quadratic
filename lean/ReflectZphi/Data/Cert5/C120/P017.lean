import ReflectZphi.Data.Cert5.C120.Base

namespace ReflectZphi.Data.Cert5.C120
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub13_128 : sub13 [-3, 3, -6] = true := by decide +kernel
theorem sub13_129 : sub13 [-3, 3, -5] = true := by decide +kernel
theorem sub13_130 : sub13 [-3, 3, -4] = true := by decide +kernel
theorem sub13_131 : sub13 [-3, 3, -3] = true := by decide +kernel
theorem sub13_132 : sub13 [-3, 3, -2] = true := by decide +kernel
theorem sub13_133 : sub13 [-3, 3, -1] = true := by decide +kernel
theorem sub13_134 : sub13 [-3, 3, 0] = true := by decide +kernel
theorem sub13_135 : sub13 [-3, 3, 1] = true := by decide +kernel
theorem sub13_136 : sub13 [-3, 3, 2] = true := by decide +kernel
theorem sub13_137 : sub13 [-3, 3, 3] = true := by decide +kernel
theorem sub13_138 : sub13 [-3, 3, 4] = true := by decide +kernel
theorem sub13_139 : sub13 [-3, 3, 5] = true := by decide +kernel
theorem sub13_140 : sub13 [-3, 4] = true := by decide +kernel
theorem sub13_141 : sub13 [-3, 5] = true := by decide +kernel
theorem sub13_142 : sub13 [-3, 6] = true := by decide +kernel
theorem sub13_143 : sub13 [-3, 7] = true := by decide +kernel
theorem sub13_144 : sub13 [-2, -7] = true := by decide +kernel
theorem sub13_145 : sub13 [-2, -6] = true := by decide +kernel
theorem sub13_146 : sub13 [-2, -5] = true := by decide +kernel
theorem sub13_147 : sub13 [-2, -4] = true := by decide +kernel
theorem sub13_148 : sub13 [-2, -3, -6] = true := by decide +kernel
theorem sub13_149 : sub13 [-2, -3, -5] = true := by decide +kernel
theorem sub13_150 : sub13 [-2, -3, -4] = true := by decide +kernel
theorem sub13_151 : sub13 [-2, -3, -3] = true := by decide +kernel
theorem sub13_152 : sub13 [-2, -3, -2] = true := by decide +kernel
theorem sub13_153 : sub13 [-2, -3, -1] = true := by decide +kernel
theorem sub13_154 : sub13 [-2, -3, 0] = true := by decide +kernel
theorem sub13_155 : sub13 [-2, -3, 1] = true := by decide +kernel
theorem sub13_156 : sub13 [-2, -3, 2] = true := by decide +kernel
theorem sub13_157 : sub13 [-2, -3, 3] = true := by decide +kernel
theorem sub13_158 : sub13 [-2, -3, 4] = true := by decide +kernel
theorem sub13_159 : sub13 [-2, -3, 5] = true := by decide +kernel
theorem sb13_4 : ∀ q ∈ blk13_4, sub13 q = true := by
  unfold blk13_4
  exact List.forall_mem_cons.2 ⟨sub13_128, List.forall_mem_cons.2 ⟨sub13_129, List.forall_mem_cons.2 ⟨sub13_130, List.forall_mem_cons.2 ⟨sub13_131, List.forall_mem_cons.2 ⟨sub13_132, List.forall_mem_cons.2 ⟨sub13_133, List.forall_mem_cons.2 ⟨sub13_134, List.forall_mem_cons.2 ⟨sub13_135, List.forall_mem_cons.2 ⟨sub13_136, List.forall_mem_cons.2 ⟨sub13_137, List.forall_mem_cons.2 ⟨sub13_138, List.forall_mem_cons.2 ⟨sub13_139, List.forall_mem_cons.2 ⟨sub13_140, List.forall_mem_cons.2 ⟨sub13_141, List.forall_mem_cons.2 ⟨sub13_142, List.forall_mem_cons.2 ⟨sub13_143, List.forall_mem_cons.2 ⟨sub13_144, List.forall_mem_cons.2 ⟨sub13_145, List.forall_mem_cons.2 ⟨sub13_146, List.forall_mem_cons.2 ⟨sub13_147, List.forall_mem_cons.2 ⟨sub13_148, List.forall_mem_cons.2 ⟨sub13_149, List.forall_mem_cons.2 ⟨sub13_150, List.forall_mem_cons.2 ⟨sub13_151, List.forall_mem_cons.2 ⟨sub13_152, List.forall_mem_cons.2 ⟨sub13_153, List.forall_mem_cons.2 ⟨sub13_154, List.forall_mem_cons.2 ⟨sub13_155, List.forall_mem_cons.2 ⟨sub13_156, List.forall_mem_cons.2 ⟨sub13_157, List.forall_mem_cons.2 ⟨sub13_158, List.forall_mem_cons.2 ⟨sub13_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub13_160 : sub13 [-2, -3, 6] = true := by decide +kernel
theorem sub13_161 : sub13 [-2, -2, -7] = true := by decide +kernel
theorem sub13_162 : sub13 [-2, -2, -6] = true := by decide +kernel
theorem sub13_163 : sub13 [-2, -2, -5] = true := by decide +kernel
theorem sub13_164 : sub13 [-2, -2, -4] = true := by decide +kernel
theorem sub13_165 : sub13 [-2, -2, -3] = true := by decide +kernel
theorem sub13_166 : sub13 [-2, -2, -2] = true := by decide +kernel
theorem sub13_167 : sub13 [-2, -2, -1] = true := by decide +kernel
theorem sub13_168 : sub13 [-2, -2, 0] = true := by decide +kernel
theorem sub13_169 : sub13 [-2, -2, 1] = true := by decide +kernel
theorem sub13_170 : sub13 [-2, -2, 2] = true := by decide +kernel
theorem sub13_171 : sub13 [-2, -2, 3] = true := by decide +kernel
theorem sub13_172 : sub13 [-2, -2, 4] = true := by decide +kernel
theorem sub13_173 : sub13 [-2, -2, 5] = true := by decide +kernel
theorem sub13_174 : sub13 [-2, -2, 6] = true := by decide +kernel
theorem sub13_175 : sub13 [-2, -2, 7] = true := by decide +kernel
theorem sub13_176 : sub13 [-2, -1, -8] = true := by decide +kernel
theorem sub13_177 : sub13 [-2, -1, -7] = true := by decide +kernel
theorem sub13_178 : sub13 [-2, -1, -6] = true := by decide +kernel
theorem sub13_179 : sub13 [-2, -1, -5] = true := by decide +kernel
theorem sub13_180 : sub13 [-2, -1, -4] = true := by decide +kernel
theorem sub13_181 : sub13 [-2, -1, -3] = true := by decide +kernel
theorem sub13_182 : sub13 [-2, -1, -2] = true := by decide +kernel
theorem sub13_183 : sub13 [-2, -1, -1] = true := by decide +kernel
theorem sub13_184 : sub13 [-2, -1, 0] = true := by decide +kernel
theorem sub13_185 : sub13 [-2, -1, 1] = true := by decide +kernel
theorem sub13_186 : sub13 [-2, -1, 2] = true := by decide +kernel
theorem sub13_187 : sub13 [-2, -1, 3] = true := by decide +kernel
theorem sub13_188 : sub13 [-2, -1, 4] = true := by decide +kernel
theorem sub13_189 : sub13 [-2, -1, 5] = true := by decide +kernel
theorem sub13_190 : sub13 [-2, -1, 6] = true := by decide +kernel
theorem sub13_191 : sub13 [-2, -1, 7] = true := by decide +kernel
theorem sb13_5 : ∀ q ∈ blk13_5, sub13 q = true := by
  unfold blk13_5
  exact List.forall_mem_cons.2 ⟨sub13_160, List.forall_mem_cons.2 ⟨sub13_161, List.forall_mem_cons.2 ⟨sub13_162, List.forall_mem_cons.2 ⟨sub13_163, List.forall_mem_cons.2 ⟨sub13_164, List.forall_mem_cons.2 ⟨sub13_165, List.forall_mem_cons.2 ⟨sub13_166, List.forall_mem_cons.2 ⟨sub13_167, List.forall_mem_cons.2 ⟨sub13_168, List.forall_mem_cons.2 ⟨sub13_169, List.forall_mem_cons.2 ⟨sub13_170, List.forall_mem_cons.2 ⟨sub13_171, List.forall_mem_cons.2 ⟨sub13_172, List.forall_mem_cons.2 ⟨sub13_173, List.forall_mem_cons.2 ⟨sub13_174, List.forall_mem_cons.2 ⟨sub13_175, List.forall_mem_cons.2 ⟨sub13_176, List.forall_mem_cons.2 ⟨sub13_177, List.forall_mem_cons.2 ⟨sub13_178, List.forall_mem_cons.2 ⟨sub13_179, List.forall_mem_cons.2 ⟨sub13_180, List.forall_mem_cons.2 ⟨sub13_181, List.forall_mem_cons.2 ⟨sub13_182, List.forall_mem_cons.2 ⟨sub13_183, List.forall_mem_cons.2 ⟨sub13_184, List.forall_mem_cons.2 ⟨sub13_185, List.forall_mem_cons.2 ⟨sub13_186, List.forall_mem_cons.2 ⟨sub13_187, List.forall_mem_cons.2 ⟨sub13_188, List.forall_mem_cons.2 ⟨sub13_189, List.forall_mem_cons.2 ⟨sub13_190, List.forall_mem_cons.2 ⟨sub13_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub13_192 : sub13 [-2, 0, -8] = true := by decide +kernel
theorem sub13_193 : sub13 [-2, 0, -7] = true := by decide +kernel
theorem sub13_194 : sub13 [-2, 0, -6] = true := by decide +kernel
theorem sub13_195 : sub13 [-2, 0, -5] = true := by decide +kernel
theorem sub13_196 : sub13 [-2, 0, -4] = true := by decide +kernel
theorem sub13_197 : sub13 [-2, 0, -3] = true := by decide +kernel
theorem sub13_198 : sub13 [-2, 0, -2] = true := by decide +kernel
theorem sub13_199 : sub13 [-2, 0, -1] = true := by decide +kernel
theorem sub13_200 : sub13 [-2, 0, 0] = true := by decide +kernel
theorem sub13_201 : sub13 [-2, 0, 1] = true := by decide +kernel
theorem sub13_202 : sub13 [-2, 0, 2] = true := by decide +kernel
theorem sub13_203 : sub13 [-2, 0, 3] = true := by decide +kernel
theorem sub13_204 : sub13 [-2, 0, 4] = true := by decide +kernel
theorem sub13_205 : sub13 [-2, 0, 5] = true := by decide +kernel
theorem sub13_206 : sub13 [-2, 0, 6] = true := by decide +kernel
theorem sub13_207 : sub13 [-2, 1, -8] = true := by decide +kernel
theorem sub13_208 : sub13 [-2, 1, -7] = true := by decide +kernel
theorem sub13_209 : sub13 [-2, 1, -6] = true := by decide +kernel
theorem sub13_210 : sub13 [-2, 1, -5] = true := by decide +kernel
theorem sub13_211 : sub13 [-2, 1, -4] = true := by decide +kernel
theorem sub13_212 : sub13 [-2, 1, -3] = true := by decide +kernel
theorem sub13_213 : sub13 [-2, 1, -2] = true := by decide +kernel
theorem sub13_214 : sub13 [-2, 1, -1] = true := by decide +kernel
theorem sub13_215 : sub13 [-2, 1, 0] = true := by decide +kernel
theorem sub13_216 : sub13 [-2, 1, 1] = true := by decide +kernel
theorem sub13_217 : sub13 [-2, 1, 2] = true := by decide +kernel
theorem sub13_218 : sub13 [-2, 1, 3] = true := by decide +kernel
theorem sub13_219 : sub13 [-2, 1, 4] = true := by decide +kernel
theorem sub13_220 : sub13 [-2, 1, 5] = true := by decide +kernel
theorem sub13_221 : sub13 [-2, 1, 6] = true := by decide +kernel
theorem sub13_222 : sub13 [-2, 2, -8] = true := by decide +kernel
theorem sub13_223 : sub13 [-2, 2, -7] = true := by decide +kernel
theorem sb13_6 : ∀ q ∈ blk13_6, sub13 q = true := by
  unfold blk13_6
  exact List.forall_mem_cons.2 ⟨sub13_192, List.forall_mem_cons.2 ⟨sub13_193, List.forall_mem_cons.2 ⟨sub13_194, List.forall_mem_cons.2 ⟨sub13_195, List.forall_mem_cons.2 ⟨sub13_196, List.forall_mem_cons.2 ⟨sub13_197, List.forall_mem_cons.2 ⟨sub13_198, List.forall_mem_cons.2 ⟨sub13_199, List.forall_mem_cons.2 ⟨sub13_200, List.forall_mem_cons.2 ⟨sub13_201, List.forall_mem_cons.2 ⟨sub13_202, List.forall_mem_cons.2 ⟨sub13_203, List.forall_mem_cons.2 ⟨sub13_204, List.forall_mem_cons.2 ⟨sub13_205, List.forall_mem_cons.2 ⟨sub13_206, List.forall_mem_cons.2 ⟨sub13_207, List.forall_mem_cons.2 ⟨sub13_208, List.forall_mem_cons.2 ⟨sub13_209, List.forall_mem_cons.2 ⟨sub13_210, List.forall_mem_cons.2 ⟨sub13_211, List.forall_mem_cons.2 ⟨sub13_212, List.forall_mem_cons.2 ⟨sub13_213, List.forall_mem_cons.2 ⟨sub13_214, List.forall_mem_cons.2 ⟨sub13_215, List.forall_mem_cons.2 ⟨sub13_216, List.forall_mem_cons.2 ⟨sub13_217, List.forall_mem_cons.2 ⟨sub13_218, List.forall_mem_cons.2 ⟨sub13_219, List.forall_mem_cons.2 ⟨sub13_220, List.forall_mem_cons.2 ⟨sub13_221, List.forall_mem_cons.2 ⟨sub13_222, List.forall_mem_cons.2 ⟨sub13_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub13_224 : sub13 [-2, 2, -6] = true := by decide +kernel
theorem sub13_225 : sub13 [-2, 2, -5] = true := by decide +kernel
theorem sub13_226 : sub13 [-2, 2, -4] = true := by decide +kernel
theorem sub13_227 : sub13 [-2, 2, -3] = true := by decide +kernel
theorem sub13_228 : sub13 [-2, 2, -2] = true := by decide +kernel
theorem sub13_229 : sub13 [-2, 2, -1] = true := by decide +kernel
theorem sub13_230 : sub13 [-2, 2, 0] = true := by decide +kernel
theorem sub13_231 : sub13 [-2, 2, 1] = true := by decide +kernel
theorem sub13_232 : sub13 [-2, 2, 2] = true := by decide +kernel
theorem sub13_233 : sub13 [-2, 2, 3] = true := by decide +kernel
theorem sub13_234 : sub13 [-2, 2, 4] = true := by decide +kernel
theorem sub13_235 : sub13 [-2, 2, 5] = true := by decide +kernel
theorem sub13_236 : sub13 [-2, 2, 6] = true := by decide +kernel
theorem sub13_237 : sub13 [-2, 3, -8] = true := by decide +kernel
theorem sub13_238 : sub13 [-2, 3, -7] = true := by decide +kernel
theorem sub13_239 : sub13 [-2, 3, -6] = true := by decide +kernel
theorem sub13_240 : sub13 [-2, 3, -5] = true := by decide +kernel
theorem sub13_241 : sub13 [-2, 3, -4] = true := by decide +kernel
theorem sub13_242 : sub13 [-2, 3, -3] = true := by decide +kernel
theorem sub13_243 : sub13 [-2, 3, -2] = true := by decide +kernel
theorem sub13_244 : sub13 [-2, 3, -1] = true := by decide +kernel
theorem sub13_245 : sub13 [-2, 3, 0] = true := by decide +kernel
theorem sub13_246 : sub13 [-2, 3, 1] = true := by decide +kernel
theorem sub13_247 : sub13 [-2, 3, 2] = true := by decide +kernel
theorem sub13_248 : sub13 [-2, 3, 3] = true := by decide +kernel
theorem sub13_249 : sub13 [-2, 3, 4] = true := by decide +kernel
theorem sub13_250 : sub13 [-2, 3, 5] = true := by decide +kernel
theorem sub13_251 : sub13 [-2, 4, -8] = true := by decide +kernel
theorem sub13_252 : sub13 [-2, 4, -7] = true := by decide +kernel
theorem sub13_253 : sub13 [-2, 4, -6] = true := by decide +kernel
theorem sub13_254 : sub13 [-2, 4, -5] = true := by decide +kernel
theorem sub13_255 : sub13 [-2, 4, -4] = true := by decide +kernel
theorem sb13_7 : ∀ q ∈ blk13_7, sub13 q = true := by
  unfold blk13_7
  exact List.forall_mem_cons.2 ⟨sub13_224, List.forall_mem_cons.2 ⟨sub13_225, List.forall_mem_cons.2 ⟨sub13_226, List.forall_mem_cons.2 ⟨sub13_227, List.forall_mem_cons.2 ⟨sub13_228, List.forall_mem_cons.2 ⟨sub13_229, List.forall_mem_cons.2 ⟨sub13_230, List.forall_mem_cons.2 ⟨sub13_231, List.forall_mem_cons.2 ⟨sub13_232, List.forall_mem_cons.2 ⟨sub13_233, List.forall_mem_cons.2 ⟨sub13_234, List.forall_mem_cons.2 ⟨sub13_235, List.forall_mem_cons.2 ⟨sub13_236, List.forall_mem_cons.2 ⟨sub13_237, List.forall_mem_cons.2 ⟨sub13_238, List.forall_mem_cons.2 ⟨sub13_239, List.forall_mem_cons.2 ⟨sub13_240, List.forall_mem_cons.2 ⟨sub13_241, List.forall_mem_cons.2 ⟨sub13_242, List.forall_mem_cons.2 ⟨sub13_243, List.forall_mem_cons.2 ⟨sub13_244, List.forall_mem_cons.2 ⟨sub13_245, List.forall_mem_cons.2 ⟨sub13_246, List.forall_mem_cons.2 ⟨sub13_247, List.forall_mem_cons.2 ⟨sub13_248, List.forall_mem_cons.2 ⟨sub13_249, List.forall_mem_cons.2 ⟨sub13_250, List.forall_mem_cons.2 ⟨sub13_251, List.forall_mem_cons.2 ⟨sub13_252, List.forall_mem_cons.2 ⟨sub13_253, List.forall_mem_cons.2 ⟨sub13_254, List.forall_mem_cons.2 ⟨sub13_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub13_256 : sub13 [-2, 4, -3] = true := by decide +kernel
theorem sub13_257 : sub13 [-2, 4, -2] = true := by decide +kernel
theorem sub13_258 : sub13 [-2, 4, -1] = true := by decide +kernel
theorem sub13_259 : sub13 [-2, 4, 0] = true := by decide +kernel
theorem sub13_260 : sub13 [-2, 4, 1] = true := by decide +kernel
theorem sub13_261 : sub13 [-2, 4, 2] = true := by decide +kernel
theorem sub13_262 : sub13 [-2, 4, 3] = true := by decide +kernel
theorem sub13_263 : sub13 [-2, 4, 4] = true := by decide +kernel
theorem sub13_264 : sub13 [-2, 4, 5] = true := by decide +kernel
theorem sub13_265 : sub13 [-2, 5] = true := by decide +kernel
theorem sub13_266 : sub13 [-2, 6] = true := by decide +kernel
theorem sub13_267 : sub13 [-2, 7] = true := by decide +kernel
theorem sub13_268 : sub13 [-1, -8] = true := by decide +kernel
theorem sub13_269 : sub13 [-1, -7] = true := by decide +kernel
theorem sub13_270 : sub13 [-1, -6] = true := by decide +kernel
theorem sub13_271 : sub13 [-1, -5] = true := by decide +kernel
theorem sub13_272 : sub13 [-1, -4] = true := by decide +kernel
theorem sub13_273 : sub13 [-1, -3, -7] = true := by decide +kernel
theorem sub13_274 : sub13 [-1, -3, -6] = true := by decide +kernel
theorem sub13_275 : sub13 [-1, -3, -5] = true := by decide +kernel
theorem sub13_276 : sub13 [-1, -3, -4] = true := by decide +kernel
theorem sub13_277 : sub13 [-1, -3, -3] = true := by decide +kernel
theorem sub13_278 : sub13 [-1, -3, -2] = true := by decide +kernel
theorem sub13_279 : sub13 [-1, -3, -1] = true := by decide +kernel
theorem sub13_280 : sub13 [-1, -3, 0] = true := by decide +kernel
theorem sub13_281 : sub13 [-1, -3, 1] = true := by decide +kernel
theorem sub13_282 : sub13 [-1, -3, 2] = true := by decide +kernel
theorem sub13_283 : sub13 [-1, -3, 3] = true := by decide +kernel
theorem sub13_284 : sub13 [-1, -3, 4] = true := by decide +kernel
theorem sub13_285 : sub13 [-1, -3, 5] = true := by decide +kernel
theorem sub13_286 : sub13 [-1, -3, 6] = true := by decide +kernel
theorem sub13_287 : sub13 [-1, -3, 7] = true := by decide +kernel
theorem sb13_8 : ∀ q ∈ blk13_8, sub13 q = true := by
  unfold blk13_8
  exact List.forall_mem_cons.2 ⟨sub13_256, List.forall_mem_cons.2 ⟨sub13_257, List.forall_mem_cons.2 ⟨sub13_258, List.forall_mem_cons.2 ⟨sub13_259, List.forall_mem_cons.2 ⟨sub13_260, List.forall_mem_cons.2 ⟨sub13_261, List.forall_mem_cons.2 ⟨sub13_262, List.forall_mem_cons.2 ⟨sub13_263, List.forall_mem_cons.2 ⟨sub13_264, List.forall_mem_cons.2 ⟨sub13_265, List.forall_mem_cons.2 ⟨sub13_266, List.forall_mem_cons.2 ⟨sub13_267, List.forall_mem_cons.2 ⟨sub13_268, List.forall_mem_cons.2 ⟨sub13_269, List.forall_mem_cons.2 ⟨sub13_270, List.forall_mem_cons.2 ⟨sub13_271, List.forall_mem_cons.2 ⟨sub13_272, List.forall_mem_cons.2 ⟨sub13_273, List.forall_mem_cons.2 ⟨sub13_274, List.forall_mem_cons.2 ⟨sub13_275, List.forall_mem_cons.2 ⟨sub13_276, List.forall_mem_cons.2 ⟨sub13_277, List.forall_mem_cons.2 ⟨sub13_278, List.forall_mem_cons.2 ⟨sub13_279, List.forall_mem_cons.2 ⟨sub13_280, List.forall_mem_cons.2 ⟨sub13_281, List.forall_mem_cons.2 ⟨sub13_282, List.forall_mem_cons.2 ⟨sub13_283, List.forall_mem_cons.2 ⟨sub13_284, List.forall_mem_cons.2 ⟨sub13_285, List.forall_mem_cons.2 ⟨sub13_286, List.forall_mem_cons.2 ⟨sub13_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub13_288 : sub13 [-1, -2, -7] = true := by decide +kernel
theorem sub13_289 : sub13 [-1, -2, -6] = true := by decide +kernel
theorem sub13_290 : sub13 [-1, -2, -5] = true := by decide +kernel
theorem sub13_291 : sub13 [-1, -2, -4] = true := by decide +kernel
theorem sub13_292 : sub13 [-1, -2, -3] = true := by decide +kernel
theorem sub13_293 : sub13 [-1, -2, -2] = true := by decide +kernel
theorem sub13_294 : sub13 [-1, -2, -1] = true := by decide +kernel
theorem sub13_295 : sub13 [-1, -2, 0] = true := by decide +kernel
theorem sub13_296 : sub13 [-1, -2, 1] = true := by decide +kernel
theorem sub13_297 : sub13 [-1, -2, 2] = true := by decide +kernel
theorem sub13_298 : sub13 [-1, -2, 3] = true := by decide +kernel
theorem sub13_299 : sub13 [-1, -2, 4] = true := by decide +kernel
theorem sub13_300 : sub13 [-1, -2, 5] = true := by decide +kernel
theorem sub13_301 : sub13 [-1, -2, 6] = true := by decide +kernel
theorem sub13_302 : sub13 [-1, -2, 7] = true := by decide +kernel
theorem sub13_303 : sub13 [-1, -1, -8] = true := by decide +kernel
theorem sub13_304 : sub13 [-1, -1, -7] = true := by decide +kernel
theorem sub13_305 : sub13 [-1, -1, -6] = true := by decide +kernel
theorem sub13_306 : sub13 [-1, -1, -5] = true := by decide +kernel
theorem sub13_307 : sub13 [-1, -1, -4] = true := by decide +kernel
theorem sub13_308 : sub13 [-1, -1, -3] = true := by decide +kernel
theorem sub13_309 : sub13 [-1, -1, -2] = true := by decide +kernel
theorem sub13_310 : sub13 [-1, -1, -1] = true := by decide +kernel
theorem sub13_311 : sub13 [-1, -1, 0] = true := by decide +kernel
theorem sub13_312 : sub13 [-1, -1, 1] = true := by decide +kernel
theorem sub13_313 : sub13 [-1, -1, 2] = true := by decide +kernel
theorem sub13_314 : sub13 [-1, -1, 3] = true := by decide +kernel
theorem sub13_315 : sub13 [-1, -1, 4] = true := by decide +kernel
theorem sub13_316 : sub13 [-1, -1, 5] = true := by decide +kernel
theorem sub13_317 : sub13 [-1, -1, 6] = true := by decide +kernel
theorem sub13_318 : sub13 [-1, -1, 7] = true := by decide +kernel
theorem sub13_319 : sub13 [-1, 0, -8] = true := by decide +kernel
theorem sb13_9 : ∀ q ∈ blk13_9, sub13 q = true := by
  unfold blk13_9
  exact List.forall_mem_cons.2 ⟨sub13_288, List.forall_mem_cons.2 ⟨sub13_289, List.forall_mem_cons.2 ⟨sub13_290, List.forall_mem_cons.2 ⟨sub13_291, List.forall_mem_cons.2 ⟨sub13_292, List.forall_mem_cons.2 ⟨sub13_293, List.forall_mem_cons.2 ⟨sub13_294, List.forall_mem_cons.2 ⟨sub13_295, List.forall_mem_cons.2 ⟨sub13_296, List.forall_mem_cons.2 ⟨sub13_297, List.forall_mem_cons.2 ⟨sub13_298, List.forall_mem_cons.2 ⟨sub13_299, List.forall_mem_cons.2 ⟨sub13_300, List.forall_mem_cons.2 ⟨sub13_301, List.forall_mem_cons.2 ⟨sub13_302, List.forall_mem_cons.2 ⟨sub13_303, List.forall_mem_cons.2 ⟨sub13_304, List.forall_mem_cons.2 ⟨sub13_305, List.forall_mem_cons.2 ⟨sub13_306, List.forall_mem_cons.2 ⟨sub13_307, List.forall_mem_cons.2 ⟨sub13_308, List.forall_mem_cons.2 ⟨sub13_309, List.forall_mem_cons.2 ⟨sub13_310, List.forall_mem_cons.2 ⟨sub13_311, List.forall_mem_cons.2 ⟨sub13_312, List.forall_mem_cons.2 ⟨sub13_313, List.forall_mem_cons.2 ⟨sub13_314, List.forall_mem_cons.2 ⟨sub13_315, List.forall_mem_cons.2 ⟨sub13_316, List.forall_mem_cons.2 ⟨sub13_317, List.forall_mem_cons.2 ⟨sub13_318, List.forall_mem_cons.2 ⟨sub13_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub13_320 : sub13 [-1, 0, -7] = true := by decide +kernel
theorem sub13_321 : sub13 [-1, 0, -6] = true := by decide +kernel
theorem sub13_322 : sub13 [-1, 0, -5] = true := by decide +kernel
theorem sub13_323 : sub13 [-1, 0, -4] = true := by decide +kernel
theorem sub13_324 : sub13 [-1, 0, -3] = true := by decide +kernel
theorem sub13_325 : sub13 [-1, 0, -2] = true := by decide +kernel
theorem sub13_326 : sub13 [-1, 0, -1] = true := by decide +kernel
theorem sub13_327 : sub13 [-1, 0, 0] = true := by decide +kernel
theorem sub13_328 : sub13 [-1, 0, 1] = true := by decide +kernel
theorem sub13_329 : sub13 [-1, 0, 2] = true := by decide +kernel
theorem sub13_330 : sub13 [-1, 0, 3] = true := by decide +kernel
theorem sub13_331 : sub13 [-1, 0, 4] = true := by decide +kernel
theorem sub13_332 : sub13 [-1, 0, 5] = true := by decide +kernel
theorem sub13_333 : sub13 [-1, 0, 6] = true := by decide +kernel
theorem sub13_334 : sub13 [-1, 0, 7] = true := by decide +kernel
theorem sub13_335 : sub13 [-1, 1, -8] = true := by decide +kernel
theorem sub13_336 : sub13 [-1, 1, -7] = true := by decide +kernel
theorem sub13_337 : sub13 [-1, 1, -6] = true := by decide +kernel
theorem sub13_338 : sub13 [-1, 1, -5] = true := by decide +kernel
theorem sub13_339 : sub13 [-1, 1, -4] = true := by decide +kernel
theorem sub13_340 : sub13 [-1, 1, -3] = true := by decide +kernel
theorem sub13_341 : sub13 [-1, 1, -2] = true := by decide +kernel
theorem sub13_342 : sub13 [-1, 1, -1] = true := by decide +kernel
theorem sub13_343 : sub13 [-1, 1, 0] = true := by decide +kernel
theorem sub13_344 : sub13 [-1, 1, 1] = true := by decide +kernel
theorem sub13_345 : sub13 [-1, 1, 2] = true := by decide +kernel
theorem sub13_346 : sub13 [-1, 1, 3] = true := by decide +kernel
theorem sub13_347 : sub13 [-1, 1, 4] = true := by decide +kernel
theorem sub13_348 : sub13 [-1, 1, 5] = true := by decide +kernel
theorem sub13_349 : sub13 [-1, 1, 6] = true := by decide +kernel
theorem sub13_350 : sub13 [-1, 1, 7] = true := by decide +kernel
theorem sub13_351 : sub13 [-1, 2, -8] = true := by decide +kernel
theorem sb13_10 : ∀ q ∈ blk13_10, sub13 q = true := by
  unfold blk13_10
  exact List.forall_mem_cons.2 ⟨sub13_320, List.forall_mem_cons.2 ⟨sub13_321, List.forall_mem_cons.2 ⟨sub13_322, List.forall_mem_cons.2 ⟨sub13_323, List.forall_mem_cons.2 ⟨sub13_324, List.forall_mem_cons.2 ⟨sub13_325, List.forall_mem_cons.2 ⟨sub13_326, List.forall_mem_cons.2 ⟨sub13_327, List.forall_mem_cons.2 ⟨sub13_328, List.forall_mem_cons.2 ⟨sub13_329, List.forall_mem_cons.2 ⟨sub13_330, List.forall_mem_cons.2 ⟨sub13_331, List.forall_mem_cons.2 ⟨sub13_332, List.forall_mem_cons.2 ⟨sub13_333, List.forall_mem_cons.2 ⟨sub13_334, List.forall_mem_cons.2 ⟨sub13_335, List.forall_mem_cons.2 ⟨sub13_336, List.forall_mem_cons.2 ⟨sub13_337, List.forall_mem_cons.2 ⟨sub13_338, List.forall_mem_cons.2 ⟨sub13_339, List.forall_mem_cons.2 ⟨sub13_340, List.forall_mem_cons.2 ⟨sub13_341, List.forall_mem_cons.2 ⟨sub13_342, List.forall_mem_cons.2 ⟨sub13_343, List.forall_mem_cons.2 ⟨sub13_344, List.forall_mem_cons.2 ⟨sub13_345, List.forall_mem_cons.2 ⟨sub13_346, List.forall_mem_cons.2 ⟨sub13_347, List.forall_mem_cons.2 ⟨sub13_348, List.forall_mem_cons.2 ⟨sub13_349, List.forall_mem_cons.2 ⟨sub13_350, List.forall_mem_cons.2 ⟨sub13_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub13_352 : sub13 [-1, 2, -7] = true := by decide +kernel
theorem sub13_353 : sub13 [-1, 2, -6] = true := by decide +kernel
theorem sub13_354 : sub13 [-1, 2, -5] = true := by decide +kernel
theorem sub13_355 : sub13 [-1, 2, -4] = true := by decide +kernel
theorem sub13_356 : sub13 [-1, 2, -3] = true := by decide +kernel
theorem sub13_357 : sub13 [-1, 2, -2] = true := by decide +kernel
theorem sub13_358 : sub13 [-1, 2, -1] = true := by decide +kernel
theorem sub13_359 : sub13 [-1, 2, 0] = true := by decide +kernel
theorem sub13_360 : sub13 [-1, 2, 1] = true := by decide +kernel
theorem sub13_361 : sub13 [-1, 2, 2] = true := by decide +kernel
theorem sub13_362 : sub13 [-1, 2, 3] = true := by decide +kernel
theorem sub13_363 : sub13 [-1, 2, 4] = true := by decide +kernel
theorem sub13_364 : sub13 [-1, 2, 5] = true := by decide +kernel
theorem sub13_365 : sub13 [-1, 2, 6] = true := by decide +kernel
theorem sub13_366 : sub13 [-1, 3, -8] = true := by decide +kernel
theorem sub13_367 : sub13 [-1, 3, -7] = true := by decide +kernel
theorem sub13_368 : sub13 [-1, 3, -6] = true := by decide +kernel
theorem sub13_369 : sub13 [-1, 3, -5] = true := by decide +kernel
theorem sub13_370 : sub13 [-1, 3, -4] = true := by decide +kernel
theorem sub13_371 : sub13 [-1, 3, -3] = true := by decide +kernel
theorem sub13_372 : sub13 [-1, 3, -2] = true := by decide +kernel
theorem sub13_373 : sub13 [-1, 3, -1] = true := by decide +kernel
theorem sub13_374 : sub13 [-1, 3, 0] = true := by decide +kernel
theorem sub13_375 : sub13 [-1, 3, 1] = true := by decide +kernel
theorem sub13_376 : sub13 [-1, 3, 2] = true := by decide +kernel
theorem sub13_377 : sub13 [-1, 3, 3] = true := by decide +kernel
theorem sub13_378 : sub13 [-1, 3, 4] = true := by decide +kernel
theorem sub13_379 : sub13 [-1, 3, 5] = true := by decide +kernel
theorem sub13_380 : sub13 [-1, 3, 6] = true := by decide +kernel
theorem sub13_381 : sub13 [-1, 4, -8] = true := by decide +kernel
theorem sub13_382 : sub13 [-1, 4, -7] = true := by decide +kernel
theorem sub13_383 : sub13 [-1, 4, -6] = true := by decide +kernel
theorem sb13_11 : ∀ q ∈ blk13_11, sub13 q = true := by
  unfold blk13_11
  exact List.forall_mem_cons.2 ⟨sub13_352, List.forall_mem_cons.2 ⟨sub13_353, List.forall_mem_cons.2 ⟨sub13_354, List.forall_mem_cons.2 ⟨sub13_355, List.forall_mem_cons.2 ⟨sub13_356, List.forall_mem_cons.2 ⟨sub13_357, List.forall_mem_cons.2 ⟨sub13_358, List.forall_mem_cons.2 ⟨sub13_359, List.forall_mem_cons.2 ⟨sub13_360, List.forall_mem_cons.2 ⟨sub13_361, List.forall_mem_cons.2 ⟨sub13_362, List.forall_mem_cons.2 ⟨sub13_363, List.forall_mem_cons.2 ⟨sub13_364, List.forall_mem_cons.2 ⟨sub13_365, List.forall_mem_cons.2 ⟨sub13_366, List.forall_mem_cons.2 ⟨sub13_367, List.forall_mem_cons.2 ⟨sub13_368, List.forall_mem_cons.2 ⟨sub13_369, List.forall_mem_cons.2 ⟨sub13_370, List.forall_mem_cons.2 ⟨sub13_371, List.forall_mem_cons.2 ⟨sub13_372, List.forall_mem_cons.2 ⟨sub13_373, List.forall_mem_cons.2 ⟨sub13_374, List.forall_mem_cons.2 ⟨sub13_375, List.forall_mem_cons.2 ⟨sub13_376, List.forall_mem_cons.2 ⟨sub13_377, List.forall_mem_cons.2 ⟨sub13_378, List.forall_mem_cons.2 ⟨sub13_379, List.forall_mem_cons.2 ⟨sub13_380, List.forall_mem_cons.2 ⟨sub13_381, List.forall_mem_cons.2 ⟨sub13_382, List.forall_mem_cons.2 ⟨sub13_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub13_384 : sub13 [-1, 4, -5] = true := by decide +kernel
theorem sub13_385 : sub13 [-1, 4, -4] = true := by decide +kernel
theorem sub13_386 : sub13 [-1, 4, -3] = true := by decide +kernel
theorem sub13_387 : sub13 [-1, 4, -2] = true := by decide +kernel
theorem sub13_388 : sub13 [-1, 4, -1] = true := by decide +kernel
theorem sub13_389 : sub13 [-1, 4, 0] = true := by decide +kernel
theorem sub13_390 : sub13 [-1, 4, 1] = true := by decide +kernel
theorem sub13_391 : sub13 [-1, 4, 2] = true := by decide +kernel
theorem sub13_392 : sub13 [-1, 4, 3] = true := by decide +kernel
theorem sub13_393 : sub13 [-1, 4, 4] = true := by decide +kernel
theorem sub13_394 : sub13 [-1, 4, 5] = true := by decide +kernel
theorem sub13_395 : sub13 [-1, 5] = true := by decide +kernel
theorem sub13_396 : sub13 [-1, 6] = true := by decide +kernel
theorem sub13_397 : sub13 [-1, 7] = true := by decide +kernel
theorem sub13_398 : sub13 [0, -8] = true := by decide +kernel
theorem sub13_399 : sub13 [0, -7] = true := by decide +kernel
theorem sub13_400 : sub13 [0, -6] = true := by decide +kernel
theorem sub13_401 : sub13 [0, -5] = true := by decide +kernel
theorem sub13_402 : sub13 [0, -4, -6] = true := by decide +kernel
theorem sub13_403 : sub13 [0, -4, -5] = true := by decide +kernel
theorem sub13_404 : sub13 [0, -4, -4] = true := by decide +kernel
theorem sub13_405 : sub13 [0, -4, -3] = true := by decide +kernel
theorem sub13_406 : sub13 [0, -4, -2] = true := by decide +kernel
theorem sub13_407 : sub13 [0, -4, -1] = true := by decide +kernel
theorem sub13_408 : sub13 [0, -4, 0] = true := by decide +kernel
theorem sub13_409 : sub13 [0, -4, 1] = true := by decide +kernel
theorem sub13_410 : sub13 [0, -4, 2] = true := by decide +kernel
theorem sub13_411 : sub13 [0, -4, 3] = true := by decide +kernel
theorem sub13_412 : sub13 [0, -4, 4] = true := by decide +kernel
theorem sub13_413 : sub13 [0, -4, 5] = true := by decide +kernel
theorem sub13_414 : sub13 [0, -4, 6] = true := by decide +kernel
theorem sub13_415 : sub13 [0, -4, 7] = true := by decide +kernel
theorem sb13_12 : ∀ q ∈ blk13_12, sub13 q = true := by
  unfold blk13_12
  exact List.forall_mem_cons.2 ⟨sub13_384, List.forall_mem_cons.2 ⟨sub13_385, List.forall_mem_cons.2 ⟨sub13_386, List.forall_mem_cons.2 ⟨sub13_387, List.forall_mem_cons.2 ⟨sub13_388, List.forall_mem_cons.2 ⟨sub13_389, List.forall_mem_cons.2 ⟨sub13_390, List.forall_mem_cons.2 ⟨sub13_391, List.forall_mem_cons.2 ⟨sub13_392, List.forall_mem_cons.2 ⟨sub13_393, List.forall_mem_cons.2 ⟨sub13_394, List.forall_mem_cons.2 ⟨sub13_395, List.forall_mem_cons.2 ⟨sub13_396, List.forall_mem_cons.2 ⟨sub13_397, List.forall_mem_cons.2 ⟨sub13_398, List.forall_mem_cons.2 ⟨sub13_399, List.forall_mem_cons.2 ⟨sub13_400, List.forall_mem_cons.2 ⟨sub13_401, List.forall_mem_cons.2 ⟨sub13_402, List.forall_mem_cons.2 ⟨sub13_403, List.forall_mem_cons.2 ⟨sub13_404, List.forall_mem_cons.2 ⟨sub13_405, List.forall_mem_cons.2 ⟨sub13_406, List.forall_mem_cons.2 ⟨sub13_407, List.forall_mem_cons.2 ⟨sub13_408, List.forall_mem_cons.2 ⟨sub13_409, List.forall_mem_cons.2 ⟨sub13_410, List.forall_mem_cons.2 ⟨sub13_411, List.forall_mem_cons.2 ⟨sub13_412, List.forall_mem_cons.2 ⟨sub13_413, List.forall_mem_cons.2 ⟨sub13_414, List.forall_mem_cons.2 ⟨sub13_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub13_416 : sub13 [0, -3, -7] = true := by decide +kernel
theorem sub13_417 : sub13 [0, -3, -6] = true := by decide +kernel
theorem sub13_418 : sub13 [0, -3, -5] = true := by decide +kernel
theorem sub13_419 : sub13 [0, -3, -4] = true := by decide +kernel
theorem sub13_420 : sub13 [0, -3, -3] = true := by decide +kernel
theorem sub13_421 : sub13 [0, -3, -2] = true := by decide +kernel
theorem sub13_422 : sub13 [0, -3, -1] = true := by decide +kernel
theorem sub13_423 : sub13 [0, -3, 0] = true := by decide +kernel
theorem sub13_424 : sub13 [0, -3, 1] = true := by decide +kernel
theorem sub13_425 : sub13 [0, -3, 2] = true := by decide +kernel
theorem sub13_426 : sub13 [0, -3, 3] = true := by decide +kernel
theorem sub13_427 : sub13 [0, -3, 4] = true := by decide +kernel
theorem sub13_428 : sub13 [0, -3, 5] = true := by decide +kernel
theorem sub13_429 : sub13 [0, -3, 6] = true := by decide +kernel
theorem sub13_430 : sub13 [0, -3, 7] = true := by decide +kernel
theorem sub13_431 : sub13 [0, -2, -7] = true := by decide +kernel
theorem sub13_432 : sub13 [0, -2, -6] = true := by decide +kernel
theorem sub13_433 : sub13 [0, -2, -5] = true := by decide +kernel
theorem sub13_434 : sub13 [0, -2, -4] = true := by decide +kernel
theorem sub13_435 : sub13 [0, -2, -3] = true := by decide +kernel
theorem sub13_436 : sub13 [0, -2, -2] = true := by decide +kernel
theorem sub13_437 : sub13 [0, -2, -1] = true := by decide +kernel
theorem sub13_438 : sub13 [0, -2, 0] = true := by decide +kernel
theorem sub13_439 : sub13 [0, -2, 1] = true := by decide +kernel
theorem sub13_440 : sub13 [0, -2, 2] = true := by decide +kernel
theorem sub13_441 : sub13 [0, -2, 3] = true := by decide +kernel
theorem sub13_442 : sub13 [0, -2, 4] = true := by decide +kernel
theorem sub13_443 : sub13 [0, -2, 5] = true := by decide +kernel
theorem sub13_444 : sub13 [0, -2, 6] = true := by decide +kernel
theorem sub13_445 : sub13 [0, -2, 7] = true := by decide +kernel
theorem sub13_446 : sub13 [0, -1, -8] = true := by decide +kernel
theorem sub13_447 : sub13 [0, -1, -7] = true := by decide +kernel
theorem sb13_13 : ∀ q ∈ blk13_13, sub13 q = true := by
  unfold blk13_13
  exact List.forall_mem_cons.2 ⟨sub13_416, List.forall_mem_cons.2 ⟨sub13_417, List.forall_mem_cons.2 ⟨sub13_418, List.forall_mem_cons.2 ⟨sub13_419, List.forall_mem_cons.2 ⟨sub13_420, List.forall_mem_cons.2 ⟨sub13_421, List.forall_mem_cons.2 ⟨sub13_422, List.forall_mem_cons.2 ⟨sub13_423, List.forall_mem_cons.2 ⟨sub13_424, List.forall_mem_cons.2 ⟨sub13_425, List.forall_mem_cons.2 ⟨sub13_426, List.forall_mem_cons.2 ⟨sub13_427, List.forall_mem_cons.2 ⟨sub13_428, List.forall_mem_cons.2 ⟨sub13_429, List.forall_mem_cons.2 ⟨sub13_430, List.forall_mem_cons.2 ⟨sub13_431, List.forall_mem_cons.2 ⟨sub13_432, List.forall_mem_cons.2 ⟨sub13_433, List.forall_mem_cons.2 ⟨sub13_434, List.forall_mem_cons.2 ⟨sub13_435, List.forall_mem_cons.2 ⟨sub13_436, List.forall_mem_cons.2 ⟨sub13_437, List.forall_mem_cons.2 ⟨sub13_438, List.forall_mem_cons.2 ⟨sub13_439, List.forall_mem_cons.2 ⟨sub13_440, List.forall_mem_cons.2 ⟨sub13_441, List.forall_mem_cons.2 ⟨sub13_442, List.forall_mem_cons.2 ⟨sub13_443, List.forall_mem_cons.2 ⟨sub13_444, List.forall_mem_cons.2 ⟨sub13_445, List.forall_mem_cons.2 ⟨sub13_446, List.forall_mem_cons.2 ⟨sub13_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub13_448 : sub13 [0, -1, -6] = true := by decide +kernel
theorem sub13_449 : sub13 [0, -1, -5] = true := by decide +kernel
theorem sub13_450 : sub13 [0, -1, -4] = true := by decide +kernel
theorem sub13_451 : sub13 [0, -1, -3] = true := by decide +kernel
theorem sub13_452 : sub13 [0, -1, -2] = true := by decide +kernel
theorem sub13_453 : sub13 [0, -1, -1] = true := by decide +kernel
theorem sub13_454 : sub13 [0, -1, 0] = true := by decide +kernel
theorem sub13_455 : sub13 [0, -1, 1] = true := by decide +kernel
theorem sub13_456 : sub13 [0, -1, 2] = true := by decide +kernel
theorem sub13_457 : sub13 [0, -1, 3] = true := by decide +kernel
theorem sub13_458 : sub13 [0, -1, 4] = true := by decide +kernel
theorem sub13_459 : sub13 [0, -1, 5] = true := by decide +kernel
theorem sub13_460 : sub13 [0, -1, 6] = true := by decide +kernel
theorem sub13_461 : sub13 [0, -1, 7] = true := by decide +kernel
theorem sub13_462 : sub13 [0, 0, -8] = true := by decide +kernel
theorem sub13_463 : sub13 [0, 0, -7] = true := by decide +kernel
theorem sub13_464 : sub13 [0, 0, -6] = true := by decide +kernel
theorem sub13_465 : sub13 [0, 0, -5] = true := by decide +kernel
theorem sub13_466 : sub13 [0, 0, -4] = true := by decide +kernel
theorem sub13_467 : sub13 [0, 0, -3] = true := by decide +kernel
theorem sub13_468 : sub13 [0, 0, -2] = true := by decide +kernel
theorem sub13_469 : sub13 [0, 0, -1] = true := by decide +kernel
theorem sub13_470 : sub13 [0, 0, 0] = true := by decide +kernel
theorem sub13_471 : sub13 [0, 0, 1] = true := by decide +kernel
theorem sub13_472 : sub13 [0, 0, 2] = true := by decide +kernel
theorem sub13_473 : sub13 [0, 0, 3] = true := by decide +kernel
theorem sub13_474 : sub13 [0, 0, 4] = true := by decide +kernel
theorem sub13_475 : sub13 [0, 0, 5] = true := by decide +kernel
theorem sub13_476 : sub13 [0, 0, 6] = true := by decide +kernel
theorem sub13_477 : sub13 [0, 0, 7] = true := by decide +kernel
theorem sub13_478 : sub13 [0, 1, -8] = true := by decide +kernel
theorem sub13_479 : sub13 [0, 1, -7] = true := by decide +kernel
theorem sb13_14 : ∀ q ∈ blk13_14, sub13 q = true := by
  unfold blk13_14
  exact List.forall_mem_cons.2 ⟨sub13_448, List.forall_mem_cons.2 ⟨sub13_449, List.forall_mem_cons.2 ⟨sub13_450, List.forall_mem_cons.2 ⟨sub13_451, List.forall_mem_cons.2 ⟨sub13_452, List.forall_mem_cons.2 ⟨sub13_453, List.forall_mem_cons.2 ⟨sub13_454, List.forall_mem_cons.2 ⟨sub13_455, List.forall_mem_cons.2 ⟨sub13_456, List.forall_mem_cons.2 ⟨sub13_457, List.forall_mem_cons.2 ⟨sub13_458, List.forall_mem_cons.2 ⟨sub13_459, List.forall_mem_cons.2 ⟨sub13_460, List.forall_mem_cons.2 ⟨sub13_461, List.forall_mem_cons.2 ⟨sub13_462, List.forall_mem_cons.2 ⟨sub13_463, List.forall_mem_cons.2 ⟨sub13_464, List.forall_mem_cons.2 ⟨sub13_465, List.forall_mem_cons.2 ⟨sub13_466, List.forall_mem_cons.2 ⟨sub13_467, List.forall_mem_cons.2 ⟨sub13_468, List.forall_mem_cons.2 ⟨sub13_469, List.forall_mem_cons.2 ⟨sub13_470, List.forall_mem_cons.2 ⟨sub13_471, List.forall_mem_cons.2 ⟨sub13_472, List.forall_mem_cons.2 ⟨sub13_473, List.forall_mem_cons.2 ⟨sub13_474, List.forall_mem_cons.2 ⟨sub13_475, List.forall_mem_cons.2 ⟨sub13_476, List.forall_mem_cons.2 ⟨sub13_477, List.forall_mem_cons.2 ⟨sub13_478, List.forall_mem_cons.2 ⟨sub13_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub13_480 : sub13 [0, 1, -6] = true := by decide +kernel
theorem sub13_481 : sub13 [0, 1, -5] = true := by decide +kernel
theorem sub13_482 : sub13 [0, 1, -4] = true := by decide +kernel
theorem sub13_483 : sub13 [0, 1, -3] = true := by decide +kernel
theorem sub13_484 : sub13 [0, 1, -2] = true := by decide +kernel
theorem sub13_485 : sub13 [0, 1, -1] = true := by decide +kernel
theorem sub13_486 : sub13 [0, 1, 0] = true := by decide +kernel
theorem sub13_487 : sub13 [0, 1, 1] = true := by decide +kernel
theorem sub13_488 : sub13 [0, 1, 2] = true := by decide +kernel
theorem sub13_489 : sub13 [0, 1, 3] = true := by decide +kernel
theorem sub13_490 : sub13 [0, 1, 4] = true := by decide +kernel
theorem sub13_491 : sub13 [0, 1, 5] = true := by decide +kernel
theorem sub13_492 : sub13 [0, 1, 6] = true := by decide +kernel
theorem sub13_493 : sub13 [0, 1, 7] = true := by decide +kernel
theorem sub13_494 : sub13 [0, 2, -8] = true := by decide +kernel
theorem sub13_495 : sub13 [0, 2, -7] = true := by decide +kernel
theorem sub13_496 : sub13 [0, 2, -6] = true := by decide +kernel
theorem sub13_497 : sub13 [0, 2, -5] = true := by decide +kernel
theorem sub13_498 : sub13 [0, 2, -4] = true := by decide +kernel
theorem sub13_499 : sub13 [0, 2, -3] = true := by decide +kernel
theorem sub13_500 : sub13 [0, 2, -2] = true := by decide +kernel
theorem sub13_501 : sub13 [0, 2, -1] = true := by decide +kernel
theorem sub13_502 : sub13 [0, 2, 0] = true := by decide +kernel
theorem sub13_503 : sub13 [0, 2, 1] = true := by decide +kernel
theorem sub13_504 : sub13 [0, 2, 2] = true := by decide +kernel
theorem sub13_505 : sub13 [0, 2, 3] = true := by decide +kernel
theorem sub13_506 : sub13 [0, 2, 4] = true := by decide +kernel
theorem sub13_507 : sub13 [0, 2, 5] = true := by decide +kernel
theorem sub13_508 : sub13 [0, 2, 6] = true := by decide +kernel
theorem sub13_509 : sub13 [0, 3, -8] = true := by decide +kernel
theorem sub13_510 : sub13 [0, 3, -7] = true := by decide +kernel
theorem sub13_511 : sub13 [0, 3, -6] = true := by decide +kernel
theorem sb13_15 : ∀ q ∈ blk13_15, sub13 q = true := by
  unfold blk13_15
  exact List.forall_mem_cons.2 ⟨sub13_480, List.forall_mem_cons.2 ⟨sub13_481, List.forall_mem_cons.2 ⟨sub13_482, List.forall_mem_cons.2 ⟨sub13_483, List.forall_mem_cons.2 ⟨sub13_484, List.forall_mem_cons.2 ⟨sub13_485, List.forall_mem_cons.2 ⟨sub13_486, List.forall_mem_cons.2 ⟨sub13_487, List.forall_mem_cons.2 ⟨sub13_488, List.forall_mem_cons.2 ⟨sub13_489, List.forall_mem_cons.2 ⟨sub13_490, List.forall_mem_cons.2 ⟨sub13_491, List.forall_mem_cons.2 ⟨sub13_492, List.forall_mem_cons.2 ⟨sub13_493, List.forall_mem_cons.2 ⟨sub13_494, List.forall_mem_cons.2 ⟨sub13_495, List.forall_mem_cons.2 ⟨sub13_496, List.forall_mem_cons.2 ⟨sub13_497, List.forall_mem_cons.2 ⟨sub13_498, List.forall_mem_cons.2 ⟨sub13_499, List.forall_mem_cons.2 ⟨sub13_500, List.forall_mem_cons.2 ⟨sub13_501, List.forall_mem_cons.2 ⟨sub13_502, List.forall_mem_cons.2 ⟨sub13_503, List.forall_mem_cons.2 ⟨sub13_504, List.forall_mem_cons.2 ⟨sub13_505, List.forall_mem_cons.2 ⟨sub13_506, List.forall_mem_cons.2 ⟨sub13_507, List.forall_mem_cons.2 ⟨sub13_508, List.forall_mem_cons.2 ⟨sub13_509, List.forall_mem_cons.2 ⟨sub13_510, List.forall_mem_cons.2 ⟨sub13_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub13_512 : sub13 [0, 3, -5] = true := by decide +kernel
theorem sub13_513 : sub13 [0, 3, -4] = true := by decide +kernel
theorem sub13_514 : sub13 [0, 3, -3] = true := by decide +kernel
theorem sub13_515 : sub13 [0, 3, -2] = true := by decide +kernel
theorem sub13_516 : sub13 [0, 3, -1] = true := by decide +kernel
theorem sub13_517 : sub13 [0, 3, 0] = true := by decide +kernel
theorem sub13_518 : sub13 [0, 3, 1] = true := by decide +kernel
theorem sub13_519 : sub13 [0, 3, 2] = true := by decide +kernel
theorem sub13_520 : sub13 [0, 3, 3] = true := by decide +kernel
theorem sub13_521 : sub13 [0, 3, 4] = true := by decide +kernel
theorem sub13_522 : sub13 [0, 3, 5] = true := by decide +kernel
theorem sub13_523 : sub13 [0, 3, 6] = true := by decide +kernel
theorem sub13_524 : sub13 [0, 4, -8] = true := by decide +kernel
theorem sub13_525 : sub13 [0, 4, -7] = true := by decide +kernel
theorem sub13_526 : sub13 [0, 4, -6] = true := by decide +kernel
theorem sub13_527 : sub13 [0, 4, -5] = true := by decide +kernel
theorem sub13_528 : sub13 [0, 4, -4] = true := by decide +kernel
theorem sub13_529 : sub13 [0, 4, -3] = true := by decide +kernel
theorem sub13_530 : sub13 [0, 4, -2] = true := by decide +kernel
theorem sub13_531 : sub13 [0, 4, -1] = true := by decide +kernel
theorem sub13_532 : sub13 [0, 4, 0] = true := by decide +kernel
theorem sub13_533 : sub13 [0, 4, 1] = true := by decide +kernel
theorem sub13_534 : sub13 [0, 4, 2] = true := by decide +kernel
theorem sub13_535 : sub13 [0, 4, 3] = true := by decide +kernel
theorem sub13_536 : sub13 [0, 4, 4] = true := by decide +kernel
theorem sub13_537 : sub13 [0, 4, 5] = true := by decide +kernel
theorem sub13_538 : sub13 [0, 5] = true := by decide +kernel
theorem sub13_539 : sub13 [0, 6] = true := by decide +kernel
theorem sub13_540 : sub13 [0, 7] = true := by decide +kernel
theorem sub13_541 : sub13 [1, -8] = true := by decide +kernel
theorem sub13_542 : sub13 [1, -7] = true := by decide +kernel
theorem sub13_543 : sub13 [1, -6] = true := by decide +kernel
theorem sb13_16 : ∀ q ∈ blk13_16, sub13 q = true := by
  unfold blk13_16
  exact List.forall_mem_cons.2 ⟨sub13_512, List.forall_mem_cons.2 ⟨sub13_513, List.forall_mem_cons.2 ⟨sub13_514, List.forall_mem_cons.2 ⟨sub13_515, List.forall_mem_cons.2 ⟨sub13_516, List.forall_mem_cons.2 ⟨sub13_517, List.forall_mem_cons.2 ⟨sub13_518, List.forall_mem_cons.2 ⟨sub13_519, List.forall_mem_cons.2 ⟨sub13_520, List.forall_mem_cons.2 ⟨sub13_521, List.forall_mem_cons.2 ⟨sub13_522, List.forall_mem_cons.2 ⟨sub13_523, List.forall_mem_cons.2 ⟨sub13_524, List.forall_mem_cons.2 ⟨sub13_525, List.forall_mem_cons.2 ⟨sub13_526, List.forall_mem_cons.2 ⟨sub13_527, List.forall_mem_cons.2 ⟨sub13_528, List.forall_mem_cons.2 ⟨sub13_529, List.forall_mem_cons.2 ⟨sub13_530, List.forall_mem_cons.2 ⟨sub13_531, List.forall_mem_cons.2 ⟨sub13_532, List.forall_mem_cons.2 ⟨sub13_533, List.forall_mem_cons.2 ⟨sub13_534, List.forall_mem_cons.2 ⟨sub13_535, List.forall_mem_cons.2 ⟨sub13_536, List.forall_mem_cons.2 ⟨sub13_537, List.forall_mem_cons.2 ⟨sub13_538, List.forall_mem_cons.2 ⟨sub13_539, List.forall_mem_cons.2 ⟨sub13_540, List.forall_mem_cons.2 ⟨sub13_541, List.forall_mem_cons.2 ⟨sub13_542, List.forall_mem_cons.2 ⟨sub13_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub13_544 : sub13 [1, -5] = true := by decide +kernel
theorem sub13_545 : sub13 [1, -4, -6] = true := by decide +kernel
theorem sub13_546 : sub13 [1, -4, -5] = true := by decide +kernel
theorem sub13_547 : sub13 [1, -4, -4] = true := by decide +kernel
theorem sub13_548 : sub13 [1, -4, -3] = true := by decide +kernel
theorem sub13_549 : sub13 [1, -4, -2] = true := by decide +kernel
theorem sub13_550 : sub13 [1, -4, -1] = true := by decide +kernel
theorem sub13_551 : sub13 [1, -4, 0] = true := by decide +kernel
theorem sub13_552 : sub13 [1, -4, 1] = true := by decide +kernel
theorem sub13_553 : sub13 [1, -4, 2] = true := by decide +kernel
theorem sub13_554 : sub13 [1, -4, 3] = true := by decide +kernel
theorem sub13_555 : sub13 [1, -4, 4] = true := by decide +kernel
theorem sub13_556 : sub13 [1, -4, 5] = true := by decide +kernel
theorem sub13_557 : sub13 [1, -4, 6] = true := by decide +kernel
theorem sub13_558 : sub13 [1, -4, 7] = true := by decide +kernel
theorem sub13_559 : sub13 [1, -3, -7] = true := by decide +kernel
theorem sub13_560 : sub13 [1, -3, -6] = true := by decide +kernel
theorem sub13_561 : sub13 [1, -3, -5] = true := by decide +kernel
theorem sub13_562 : sub13 [1, -3, -4] = true := by decide +kernel
theorem sub13_563 : sub13 [1, -3, -3] = true := by decide +kernel
theorem sub13_564 : sub13 [1, -3, -2] = true := by decide +kernel
theorem sub13_565 : sub13 [1, -3, -1] = true := by decide +kernel
theorem sub13_566 : sub13 [1, -3, 0] = true := by decide +kernel
theorem sub13_567 : sub13 [1, -3, 1] = true := by decide +kernel
theorem sub13_568 : sub13 [1, -3, 2] = true := by decide +kernel
theorem sub13_569 : sub13 [1, -3, 3] = true := by decide +kernel
theorem sub13_570 : sub13 [1, -3, 4] = true := by decide +kernel
theorem sub13_571 : sub13 [1, -3, 5] = true := by decide +kernel
theorem sub13_572 : sub13 [1, -3, 6] = true := by decide +kernel
theorem sub13_573 : sub13 [1, -3, 7] = true := by decide +kernel
theorem sub13_574 : sub13 [1, -2, -7] = true := by decide +kernel
theorem sub13_575 : sub13 [1, -2, -6] = true := by decide +kernel
theorem sb13_17 : ∀ q ∈ blk13_17, sub13 q = true := by
  unfold blk13_17
  exact List.forall_mem_cons.2 ⟨sub13_544, List.forall_mem_cons.2 ⟨sub13_545, List.forall_mem_cons.2 ⟨sub13_546, List.forall_mem_cons.2 ⟨sub13_547, List.forall_mem_cons.2 ⟨sub13_548, List.forall_mem_cons.2 ⟨sub13_549, List.forall_mem_cons.2 ⟨sub13_550, List.forall_mem_cons.2 ⟨sub13_551, List.forall_mem_cons.2 ⟨sub13_552, List.forall_mem_cons.2 ⟨sub13_553, List.forall_mem_cons.2 ⟨sub13_554, List.forall_mem_cons.2 ⟨sub13_555, List.forall_mem_cons.2 ⟨sub13_556, List.forall_mem_cons.2 ⟨sub13_557, List.forall_mem_cons.2 ⟨sub13_558, List.forall_mem_cons.2 ⟨sub13_559, List.forall_mem_cons.2 ⟨sub13_560, List.forall_mem_cons.2 ⟨sub13_561, List.forall_mem_cons.2 ⟨sub13_562, List.forall_mem_cons.2 ⟨sub13_563, List.forall_mem_cons.2 ⟨sub13_564, List.forall_mem_cons.2 ⟨sub13_565, List.forall_mem_cons.2 ⟨sub13_566, List.forall_mem_cons.2 ⟨sub13_567, List.forall_mem_cons.2 ⟨sub13_568, List.forall_mem_cons.2 ⟨sub13_569, List.forall_mem_cons.2 ⟨sub13_570, List.forall_mem_cons.2 ⟨sub13_571, List.forall_mem_cons.2 ⟨sub13_572, List.forall_mem_cons.2 ⟨sub13_573, List.forall_mem_cons.2 ⟨sub13_574, List.forall_mem_cons.2 ⟨sub13_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C120
