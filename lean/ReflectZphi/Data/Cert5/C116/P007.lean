import ReflectZphi.Data.Cert5.C116.Base

namespace ReflectZphi.Data.Cert5.C116

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_1_160 : subd6_1 [-5, -7] = true := by decide +kernel
theorem subd6_1_161 : subd6_1 [-5, -6] = true := by decide +kernel
theorem subd6_1_162 : subd6_1 [-5, -5] = true := by decide +kernel
theorem subd6_1_163 : subd6_1 [-5, -4] = true := by decide +kernel
theorem subd6_1_164 : subd6_1 [-5, -3, -6] = true := by decide +kernel
theorem subd6_1_165 : subd6_1 [-5, -3, -5] = true := by decide +kernel
theorem subd6_1_166 : subd6_1 [-5, -3, -4] = true := by decide +kernel
theorem subd6_1_167 : subd6_1 [-5, -3, -3] = true := by decide +kernel
theorem subd6_1_168 : subd6_1 [-5, -3, -2] = true := by decide +kernel
theorem subd6_1_169 : subd6_1 [-5, -3, -1] = true := by decide +kernel
theorem subd6_1_170 : subd6_1 [-5, -3, 0] = true := by decide +kernel
theorem subd6_1_171 : subd6_1 [-5, -3, 1] = true := by decide +kernel
theorem subd6_1_172 : subd6_1 [-5, -3, 2] = true := by decide +kernel
theorem subd6_1_173 : subd6_1 [-5, -3, 3] = true := by decide +kernel
theorem subd6_1_174 : subd6_1 [-5, -3, 4] = true := by decide +kernel
theorem subd6_1_175 : subd6_1 [-5, -3, 5] = true := by decide +kernel
theorem subd6_1_176 : subd6_1 [-5, -3, 6] = true := by decide +kernel
theorem subd6_1_177 : subd6_1 [-5, -3, 7] = true := by decide +kernel
theorem subd6_1_178 : subd6_1 [-5, -3, 8] = true := by decide +kernel
theorem subd6_1_179 : subd6_1 [-5, -3, 9] = true := by decide +kernel
theorem subd6_1_180 : subd6_1 [-5, -2, -6] = true := by decide +kernel
theorem subd6_1_181 : subd6_1 [-5, -2, -5] = true := by decide +kernel
theorem subd6_1_182 : subd6_1 [-5, -2, -4] = true := by decide +kernel
theorem subd6_1_183 : subd6_1 [-5, -2, -3] = true := by decide +kernel
theorem subd6_1_184 : subd6_1 [-5, -2, -2] = true := by decide +kernel
theorem subd6_1_185 : subd6_1 [-5, -2, -1] = true := by decide +kernel
theorem subd6_1_186 : subd6_1 [-5, -2, 0] = true := by decide +kernel
theorem subd6_1_187 : subd6_1 [-5, -2, 1] = true := by decide +kernel
theorem subd6_1_188 : subd6_1 [-5, -2, 2] = true := by decide +kernel
theorem subd6_1_189 : subd6_1 [-5, -2, 3] = true := by decide +kernel
theorem subd6_1_190 : subd6_1 [-5, -2, 4] = true := by decide +kernel
theorem subd6_1_191 : subd6_1 [-5, -2, 5] = true := by decide +kernel
theorem sbd6_1_5 : ∀ q ∈ blkd6_1_5, subd6_1 q = true := by
  unfold blkd6_1_5
  exact List.forall_mem_cons.2 ⟨subd6_1_160, List.forall_mem_cons.2 ⟨subd6_1_161, List.forall_mem_cons.2 ⟨subd6_1_162, List.forall_mem_cons.2 ⟨subd6_1_163, List.forall_mem_cons.2 ⟨subd6_1_164, List.forall_mem_cons.2 ⟨subd6_1_165, List.forall_mem_cons.2 ⟨subd6_1_166, List.forall_mem_cons.2 ⟨subd6_1_167, List.forall_mem_cons.2 ⟨subd6_1_168, List.forall_mem_cons.2 ⟨subd6_1_169, List.forall_mem_cons.2 ⟨subd6_1_170, List.forall_mem_cons.2 ⟨subd6_1_171, List.forall_mem_cons.2 ⟨subd6_1_172, List.forall_mem_cons.2 ⟨subd6_1_173, List.forall_mem_cons.2 ⟨subd6_1_174, List.forall_mem_cons.2 ⟨subd6_1_175, List.forall_mem_cons.2 ⟨subd6_1_176, List.forall_mem_cons.2 ⟨subd6_1_177, List.forall_mem_cons.2 ⟨subd6_1_178, List.forall_mem_cons.2 ⟨subd6_1_179, List.forall_mem_cons.2 ⟨subd6_1_180, List.forall_mem_cons.2 ⟨subd6_1_181, List.forall_mem_cons.2 ⟨subd6_1_182, List.forall_mem_cons.2 ⟨subd6_1_183, List.forall_mem_cons.2 ⟨subd6_1_184, List.forall_mem_cons.2 ⟨subd6_1_185, List.forall_mem_cons.2 ⟨subd6_1_186, List.forall_mem_cons.2 ⟨subd6_1_187, List.forall_mem_cons.2 ⟨subd6_1_188, List.forall_mem_cons.2 ⟨subd6_1_189, List.forall_mem_cons.2 ⟨subd6_1_190, List.forall_mem_cons.2 ⟨subd6_1_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_192 : subd6_1 [-5, -2, 6] = true := by decide +kernel
theorem subd6_1_193 : subd6_1 [-5, -2, 7] = true := by decide +kernel
theorem subd6_1_194 : subd6_1 [-5, -2, 8] = true := by decide +kernel
theorem subd6_1_195 : subd6_1 [-5, -2, 9] = true := by decide +kernel
theorem subd6_1_196 : subd6_1 [-5, -1, -7] = true := by decide +kernel
theorem subd6_1_197 : subd6_1 [-5, -1, -6] = true := by decide +kernel
theorem subd6_1_198 : subd6_1 [-5, -1, -5] = true := by decide +kernel
theorem subd6_1_199 : subd6_1 [-5, -1, -4] = true := by decide +kernel
theorem subd6_1_200 : subd6_1 [-5, -1, -3] = true := by decide +kernel
theorem subd6_1_201 : subd6_1 [-5, -1, -2] = true := by decide +kernel
theorem subd6_1_202 : subd6_1 [-5, -1, -1] = true := by decide +kernel
theorem subd6_1_203 : subd6_1 [-5, -1, 0] = true := by decide +kernel
theorem subd6_1_204 : subd6_1 [-5, -1, 1] = true := by decide +kernel
theorem subd6_1_205 : subd6_1 [-5, -1, 2] = true := by decide +kernel
theorem subd6_1_206 : subd6_1 [-5, -1, 3] = true := by decide +kernel
theorem subd6_1_207 : subd6_1 [-5, -1, 4] = true := by decide +kernel
theorem subd6_1_208 : subd6_1 [-5, -1, 5] = true := by decide +kernel
theorem subd6_1_209 : subd6_1 [-5, -1, 6] = true := by decide +kernel
theorem subd6_1_210 : subd6_1 [-5, -1, 7] = true := by decide +kernel
theorem subd6_1_211 : subd6_1 [-5, -1, 8] = true := by decide +kernel
theorem subd6_1_212 : subd6_1 [-5, -1, 9] = true := by decide +kernel
theorem subd6_1_213 : subd6_1 [-5, -1, 10] = true := by decide +kernel
theorem subd6_1_214 : subd6_1 [-5, 0, -7] = true := by decide +kernel
theorem subd6_1_215 : subd6_1 [-5, 0, -6] = true := by decide +kernel
theorem subd6_1_216 : subd6_1 [-5, 0, -5] = true := by decide +kernel
theorem subd6_1_217 : subd6_1 [-5, 0, -4] = true := by decide +kernel
theorem subd6_1_218 : subd6_1 [-5, 0, -3] = true := by decide +kernel
theorem subd6_1_219 : subd6_1 [-5, 0, -2] = true := by decide +kernel
theorem subd6_1_220 : subd6_1 [-5, 0, -1] = true := by decide +kernel
theorem subd6_1_221 : subd6_1 [-5, 0, 0] = true := by decide +kernel
theorem subd6_1_222 : subd6_1 [-5, 0, 1] = true := by decide +kernel
theorem subd6_1_223 : subd6_1 [-5, 0, 2] = true := by decide +kernel
theorem sbd6_1_6 : ∀ q ∈ blkd6_1_6, subd6_1 q = true := by
  unfold blkd6_1_6
  exact List.forall_mem_cons.2 ⟨subd6_1_192, List.forall_mem_cons.2 ⟨subd6_1_193, List.forall_mem_cons.2 ⟨subd6_1_194, List.forall_mem_cons.2 ⟨subd6_1_195, List.forall_mem_cons.2 ⟨subd6_1_196, List.forall_mem_cons.2 ⟨subd6_1_197, List.forall_mem_cons.2 ⟨subd6_1_198, List.forall_mem_cons.2 ⟨subd6_1_199, List.forall_mem_cons.2 ⟨subd6_1_200, List.forall_mem_cons.2 ⟨subd6_1_201, List.forall_mem_cons.2 ⟨subd6_1_202, List.forall_mem_cons.2 ⟨subd6_1_203, List.forall_mem_cons.2 ⟨subd6_1_204, List.forall_mem_cons.2 ⟨subd6_1_205, List.forall_mem_cons.2 ⟨subd6_1_206, List.forall_mem_cons.2 ⟨subd6_1_207, List.forall_mem_cons.2 ⟨subd6_1_208, List.forall_mem_cons.2 ⟨subd6_1_209, List.forall_mem_cons.2 ⟨subd6_1_210, List.forall_mem_cons.2 ⟨subd6_1_211, List.forall_mem_cons.2 ⟨subd6_1_212, List.forall_mem_cons.2 ⟨subd6_1_213, List.forall_mem_cons.2 ⟨subd6_1_214, List.forall_mem_cons.2 ⟨subd6_1_215, List.forall_mem_cons.2 ⟨subd6_1_216, List.forall_mem_cons.2 ⟨subd6_1_217, List.forall_mem_cons.2 ⟨subd6_1_218, List.forall_mem_cons.2 ⟨subd6_1_219, List.forall_mem_cons.2 ⟨subd6_1_220, List.forall_mem_cons.2 ⟨subd6_1_221, List.forall_mem_cons.2 ⟨subd6_1_222, List.forall_mem_cons.2 ⟨subd6_1_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_224 : subd6_1 [-5, 0, 3] = true := by decide +kernel
theorem subd6_1_225 : subd6_1 [-5, 0, 4] = true := by decide +kernel
theorem subd6_1_226 : subd6_1 [-5, 0, 5] = true := by decide +kernel
theorem subd6_1_227 : subd6_1 [-5, 0, 6] = true := by decide +kernel
theorem subd6_1_228 : subd6_1 [-5, 0, 7] = true := by decide +kernel
theorem subd6_1_229 : subd6_1 [-5, 0, 8] = true := by decide +kernel
theorem subd6_1_230 : subd6_1 [-5, 0, 9] = true := by decide +kernel
theorem subd6_1_231 : subd6_1 [-5, 0, 10] = true := by decide +kernel
theorem subd6_1_232 : subd6_1 [-5, 1, -7] = true := by decide +kernel
theorem subd6_1_233 : subd6_1 [-5, 1, -6] = true := by decide +kernel
theorem subd6_1_234 : subd6_1 [-5, 1, -5] = true := by decide +kernel
theorem subd6_1_235 : subd6_1 [-5, 1, -4] = true := by decide +kernel
theorem subd6_1_236 : subd6_1 [-5, 1, -3] = true := by decide +kernel
theorem subd6_1_237 : subd6_1 [-5, 1, -2] = true := by decide +kernel
theorem subd6_1_238 : subd6_1 [-5, 1, -1] = true := by decide +kernel
theorem subd6_1_239 : subd6_1 [-5, 1, 0] = true := by decide +kernel
theorem subd6_1_240 : subd6_1 [-5, 1, 1] = true := by decide +kernel
theorem subd6_1_241 : subd6_1 [-5, 1, 2] = true := by decide +kernel
theorem subd6_1_242 : subd6_1 [-5, 1, 3] = true := by decide +kernel
theorem subd6_1_243 : subd6_1 [-5, 1, 4] = true := by decide +kernel
theorem subd6_1_244 : subd6_1 [-5, 1, 5] = true := by decide +kernel
theorem subd6_1_245 : subd6_1 [-5, 1, 6] = true := by decide +kernel
theorem subd6_1_246 : subd6_1 [-5, 1, 7] = true := by decide +kernel
theorem subd6_1_247 : subd6_1 [-5, 1, 8] = true := by decide +kernel
theorem subd6_1_248 : subd6_1 [-5, 1, 9] = true := by decide +kernel
theorem subd6_1_249 : subd6_1 [-5, 1, 10] = true := by decide +kernel
theorem subd6_1_250 : subd6_1 [-5, 2, -7] = true := by decide +kernel
theorem subd6_1_251 : subd6_1 [-5, 2, -6] = true := by decide +kernel
theorem subd6_1_252 : subd6_1 [-5, 2, -5] = true := by decide +kernel
theorem subd6_1_253 : subd6_1 [-5, 2, -4] = true := by decide +kernel
theorem subd6_1_254 : subd6_1 [-5, 2, -3] = true := by decide +kernel
theorem subd6_1_255 : subd6_1 [-5, 2, -2] = true := by decide +kernel
theorem sbd6_1_7 : ∀ q ∈ blkd6_1_7, subd6_1 q = true := by
  unfold blkd6_1_7
  exact List.forall_mem_cons.2 ⟨subd6_1_224, List.forall_mem_cons.2 ⟨subd6_1_225, List.forall_mem_cons.2 ⟨subd6_1_226, List.forall_mem_cons.2 ⟨subd6_1_227, List.forall_mem_cons.2 ⟨subd6_1_228, List.forall_mem_cons.2 ⟨subd6_1_229, List.forall_mem_cons.2 ⟨subd6_1_230, List.forall_mem_cons.2 ⟨subd6_1_231, List.forall_mem_cons.2 ⟨subd6_1_232, List.forall_mem_cons.2 ⟨subd6_1_233, List.forall_mem_cons.2 ⟨subd6_1_234, List.forall_mem_cons.2 ⟨subd6_1_235, List.forall_mem_cons.2 ⟨subd6_1_236, List.forall_mem_cons.2 ⟨subd6_1_237, List.forall_mem_cons.2 ⟨subd6_1_238, List.forall_mem_cons.2 ⟨subd6_1_239, List.forall_mem_cons.2 ⟨subd6_1_240, List.forall_mem_cons.2 ⟨subd6_1_241, List.forall_mem_cons.2 ⟨subd6_1_242, List.forall_mem_cons.2 ⟨subd6_1_243, List.forall_mem_cons.2 ⟨subd6_1_244, List.forall_mem_cons.2 ⟨subd6_1_245, List.forall_mem_cons.2 ⟨subd6_1_246, List.forall_mem_cons.2 ⟨subd6_1_247, List.forall_mem_cons.2 ⟨subd6_1_248, List.forall_mem_cons.2 ⟨subd6_1_249, List.forall_mem_cons.2 ⟨subd6_1_250, List.forall_mem_cons.2 ⟨subd6_1_251, List.forall_mem_cons.2 ⟨subd6_1_252, List.forall_mem_cons.2 ⟨subd6_1_253, List.forall_mem_cons.2 ⟨subd6_1_254, List.forall_mem_cons.2 ⟨subd6_1_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_256 : subd6_1 [-5, 2, -1] = true := by decide +kernel
theorem subd6_1_257 : subd6_1 [-5, 2, 0] = true := by decide +kernel
theorem subd6_1_258 : subd6_1 [-5, 2, 1] = true := by decide +kernel
theorem subd6_1_259 : subd6_1 [-5, 2, 2] = true := by decide +kernel
theorem subd6_1_260 : subd6_1 [-5, 2, 3] = true := by decide +kernel
theorem subd6_1_261 : subd6_1 [-5, 2, 4] = true := by decide +kernel
theorem subd6_1_262 : subd6_1 [-5, 2, 5] = true := by decide +kernel
theorem subd6_1_263 : subd6_1 [-5, 2, 6] = true := by decide +kernel
theorem subd6_1_264 : subd6_1 [-5, 2, 7] = true := by decide +kernel
theorem subd6_1_265 : subd6_1 [-5, 2, 8] = true := by decide +kernel
theorem subd6_1_266 : subd6_1 [-5, 2, 9] = true := by decide +kernel
theorem subd6_1_267 : subd6_1 [-5, 2, 10] = true := by decide +kernel
theorem subd6_1_268 : subd6_1 [-5, 3, -7] = true := by decide +kernel
theorem subd6_1_269 : subd6_1 [-5, 3, -6] = true := by decide +kernel
theorem subd6_1_270 : subd6_1 [-5, 3, -5] = true := by decide +kernel
theorem subd6_1_271 : subd6_1 [-5, 3, -4] = true := by decide +kernel
theorem subd6_1_272 : subd6_1 [-5, 3, -3] = true := by decide +kernel
theorem subd6_1_273 : subd6_1 [-5, 3, -2] = true := by decide +kernel
theorem subd6_1_274 : subd6_1 [-5, 3, -1] = true := by decide +kernel
theorem subd6_1_275 : subd6_1 [-5, 3, 0] = true := by decide +kernel
theorem subd6_1_276 : subd6_1 [-5, 3, 1] = true := by decide +kernel
theorem subd6_1_277 : subd6_1 [-5, 3, 2] = true := by decide +kernel
theorem subd6_1_278 : subd6_1 [-5, 3, 3] = true := by decide +kernel
theorem subd6_1_279 : subd6_1 [-5, 3, 4] = true := by decide +kernel
theorem subd6_1_280 : subd6_1 [-5, 3, 5] = true := by decide +kernel
theorem subd6_1_281 : subd6_1 [-5, 3, 6] = true := by decide +kernel
theorem subd6_1_282 : subd6_1 [-5, 3, 7] = true := by decide +kernel
theorem subd6_1_283 : subd6_1 [-5, 3, 8] = true := by decide +kernel
theorem subd6_1_284 : subd6_1 [-5, 3, 9] = true := by decide +kernel
theorem subd6_1_285 : subd6_1 [-5, 4, -7] = true := by decide +kernel
theorem subd6_1_286 : subd6_1 [-5, 4, -6] = true := by decide +kernel
theorem subd6_1_287 : subd6_1 [-5, 4, -5] = true := by decide +kernel
theorem sbd6_1_8 : ∀ q ∈ blkd6_1_8, subd6_1 q = true := by
  unfold blkd6_1_8
  exact List.forall_mem_cons.2 ⟨subd6_1_256, List.forall_mem_cons.2 ⟨subd6_1_257, List.forall_mem_cons.2 ⟨subd6_1_258, List.forall_mem_cons.2 ⟨subd6_1_259, List.forall_mem_cons.2 ⟨subd6_1_260, List.forall_mem_cons.2 ⟨subd6_1_261, List.forall_mem_cons.2 ⟨subd6_1_262, List.forall_mem_cons.2 ⟨subd6_1_263, List.forall_mem_cons.2 ⟨subd6_1_264, List.forall_mem_cons.2 ⟨subd6_1_265, List.forall_mem_cons.2 ⟨subd6_1_266, List.forall_mem_cons.2 ⟨subd6_1_267, List.forall_mem_cons.2 ⟨subd6_1_268, List.forall_mem_cons.2 ⟨subd6_1_269, List.forall_mem_cons.2 ⟨subd6_1_270, List.forall_mem_cons.2 ⟨subd6_1_271, List.forall_mem_cons.2 ⟨subd6_1_272, List.forall_mem_cons.2 ⟨subd6_1_273, List.forall_mem_cons.2 ⟨subd6_1_274, List.forall_mem_cons.2 ⟨subd6_1_275, List.forall_mem_cons.2 ⟨subd6_1_276, List.forall_mem_cons.2 ⟨subd6_1_277, List.forall_mem_cons.2 ⟨subd6_1_278, List.forall_mem_cons.2 ⟨subd6_1_279, List.forall_mem_cons.2 ⟨subd6_1_280, List.forall_mem_cons.2 ⟨subd6_1_281, List.forall_mem_cons.2 ⟨subd6_1_282, List.forall_mem_cons.2 ⟨subd6_1_283, List.forall_mem_cons.2 ⟨subd6_1_284, List.forall_mem_cons.2 ⟨subd6_1_285, List.forall_mem_cons.2 ⟨subd6_1_286, List.forall_mem_cons.2 ⟨subd6_1_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_288 : subd6_1 [-5, 4, -4] = true := by decide +kernel
theorem subd6_1_289 : subd6_1 [-5, 4, -3] = true := by decide +kernel
theorem subd6_1_290 : subd6_1 [-5, 4, -2] = true := by decide +kernel
theorem subd6_1_291 : subd6_1 [-5, 4, -1] = true := by decide +kernel
theorem subd6_1_292 : subd6_1 [-5, 4, 0] = true := by decide +kernel
theorem subd6_1_293 : subd6_1 [-5, 4, 1] = true := by decide +kernel
theorem subd6_1_294 : subd6_1 [-5, 4, 2] = true := by decide +kernel
theorem subd6_1_295 : subd6_1 [-5, 4, 3] = true := by decide +kernel
theorem subd6_1_296 : subd6_1 [-5, 4, 4] = true := by decide +kernel
theorem subd6_1_297 : subd6_1 [-5, 4, 5] = true := by decide +kernel
theorem subd6_1_298 : subd6_1 [-5, 4, 6] = true := by decide +kernel
theorem subd6_1_299 : subd6_1 [-5, 4, 7] = true := by decide +kernel
theorem subd6_1_300 : subd6_1 [-5, 4, 8] = true := by decide +kernel
theorem subd6_1_301 : subd6_1 [-5, 4, 9] = true := by decide +kernel
theorem subd6_1_302 : subd6_1 [-5, 5, -7] = true := by decide +kernel
theorem subd6_1_303 : subd6_1 [-5, 5, -6] = true := by decide +kernel
theorem subd6_1_304 : subd6_1 [-5, 5, -5] = true := by decide +kernel
theorem subd6_1_305 : subd6_1 [-5, 5, -4] = true := by decide +kernel
theorem subd6_1_306 : subd6_1 [-5, 5, -3] = true := by decide +kernel
theorem subd6_1_307 : subd6_1 [-5, 5, -2] = true := by decide +kernel
theorem subd6_1_308 : subd6_1 [-5, 5, -1] = true := by decide +kernel
theorem subd6_1_309 : subd6_1 [-5, 5, 0] = true := by decide +kernel
theorem subd6_1_310 : subd6_1 [-5, 5, 1] = true := by decide +kernel
theorem subd6_1_311 : subd6_1 [-5, 5, 2] = true := by decide +kernel
theorem subd6_1_312 : subd6_1 [-5, 5, 3] = true := by decide +kernel
theorem subd6_1_313 : subd6_1 [-5, 5, 4] = true := by decide +kernel
theorem subd6_1_314 : subd6_1 [-5, 5, 5] = true := by decide +kernel
theorem subd6_1_315 : subd6_1 [-5, 5, 6] = true := by decide +kernel
theorem subd6_1_316 : subd6_1 [-5, 5, 7] = true := by decide +kernel
theorem subd6_1_317 : subd6_1 [-5, 5, 8] = true := by decide +kernel
theorem subd6_1_318 : subd6_1 [-5, 5, 9] = true := by decide +kernel
theorem subd6_1_319 : subd6_1 [-5, 6, -7] = true := by decide +kernel
theorem sbd6_1_9 : ∀ q ∈ blkd6_1_9, subd6_1 q = true := by
  unfold blkd6_1_9
  exact List.forall_mem_cons.2 ⟨subd6_1_288, List.forall_mem_cons.2 ⟨subd6_1_289, List.forall_mem_cons.2 ⟨subd6_1_290, List.forall_mem_cons.2 ⟨subd6_1_291, List.forall_mem_cons.2 ⟨subd6_1_292, List.forall_mem_cons.2 ⟨subd6_1_293, List.forall_mem_cons.2 ⟨subd6_1_294, List.forall_mem_cons.2 ⟨subd6_1_295, List.forall_mem_cons.2 ⟨subd6_1_296, List.forall_mem_cons.2 ⟨subd6_1_297, List.forall_mem_cons.2 ⟨subd6_1_298, List.forall_mem_cons.2 ⟨subd6_1_299, List.forall_mem_cons.2 ⟨subd6_1_300, List.forall_mem_cons.2 ⟨subd6_1_301, List.forall_mem_cons.2 ⟨subd6_1_302, List.forall_mem_cons.2 ⟨subd6_1_303, List.forall_mem_cons.2 ⟨subd6_1_304, List.forall_mem_cons.2 ⟨subd6_1_305, List.forall_mem_cons.2 ⟨subd6_1_306, List.forall_mem_cons.2 ⟨subd6_1_307, List.forall_mem_cons.2 ⟨subd6_1_308, List.forall_mem_cons.2 ⟨subd6_1_309, List.forall_mem_cons.2 ⟨subd6_1_310, List.forall_mem_cons.2 ⟨subd6_1_311, List.forall_mem_cons.2 ⟨subd6_1_312, List.forall_mem_cons.2 ⟨subd6_1_313, List.forall_mem_cons.2 ⟨subd6_1_314, List.forall_mem_cons.2 ⟨subd6_1_315, List.forall_mem_cons.2 ⟨subd6_1_316, List.forall_mem_cons.2 ⟨subd6_1_317, List.forall_mem_cons.2 ⟨subd6_1_318, List.forall_mem_cons.2 ⟨subd6_1_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_320 : subd6_1 [-5, 6, -6] = true := by decide +kernel
theorem subd6_1_321 : subd6_1 [-5, 6, -5] = true := by decide +kernel
theorem subd6_1_322 : subd6_1 [-5, 6, -4] = true := by decide +kernel
theorem subd6_1_323 : subd6_1 [-5, 6, -3] = true := by decide +kernel
theorem subd6_1_324 : subd6_1 [-5, 6, -2] = true := by decide +kernel
theorem subd6_1_325 : subd6_1 [-5, 6, -1] = true := by decide +kernel
theorem subd6_1_326 : subd6_1 [-5, 6, 0] = true := by decide +kernel
theorem subd6_1_327 : subd6_1 [-5, 6, 1] = true := by decide +kernel
theorem subd6_1_328 : subd6_1 [-5, 6, 2] = true := by decide +kernel
theorem subd6_1_329 : subd6_1 [-5, 6, 3] = true := by decide +kernel
theorem subd6_1_330 : subd6_1 [-5, 6, 4] = true := by decide +kernel
theorem subd6_1_331 : subd6_1 [-5, 6, 5] = true := by decide +kernel
theorem subd6_1_332 : subd6_1 [-5, 6, 6] = true := by decide +kernel
theorem subd6_1_333 : subd6_1 [-5, 6, 7] = true := by decide +kernel
theorem subd6_1_334 : subd6_1 [-5, 6, 8] = true := by decide +kernel
theorem subd6_1_335 : subd6_1 [-5, 7] = true := by decide +kernel
theorem subd6_1_336 : subd6_1 [-5, 8] = true := by decide +kernel
theorem subd6_1_337 : subd6_1 [-5, 9] = true := by decide +kernel
theorem subd6_1_338 : subd6_1 [-5, 10] = true := by decide +kernel
theorem subd6_1_339 : subd6_1 [-4, -9] = true := by decide +kernel
theorem subd6_1_340 : subd6_1 [-4, -8] = true := by decide +kernel
theorem subd6_1_341 : subd6_1 [-4, -7] = true := by decide +kernel
theorem subd6_1_342 : subd6_1 [-4, -6] = true := by decide +kernel
theorem subd6_1_343 : subd6_1 [-4, -5, -5] = true := by decide +kernel
theorem subd6_1_344 : subd6_1 [-4, -5, -4] = true := by decide +kernel
theorem subd6_1_345 : subd6_1 [-4, -5, -3] = true := by decide +kernel
theorem subd6_1_346 : subd6_1 [-4, -5, -2] = true := by decide +kernel
theorem subd6_1_347 : subd6_1 [-4, -5, -1] = true := by decide +kernel
theorem subd6_1_348 : subd6_1 [-4, -5, 0] = true := by decide +kernel
theorem subd6_1_349 : subd6_1 [-4, -5, 1] = true := by decide +kernel
theorem subd6_1_350 : subd6_1 [-4, -5, 2] = true := by decide +kernel
theorem subd6_1_351 : subd6_1 [-4, -5, 3] = true := by decide +kernel
theorem sbd6_1_10 : ∀ q ∈ blkd6_1_10, subd6_1 q = true := by
  unfold blkd6_1_10
  exact List.forall_mem_cons.2 ⟨subd6_1_320, List.forall_mem_cons.2 ⟨subd6_1_321, List.forall_mem_cons.2 ⟨subd6_1_322, List.forall_mem_cons.2 ⟨subd6_1_323, List.forall_mem_cons.2 ⟨subd6_1_324, List.forall_mem_cons.2 ⟨subd6_1_325, List.forall_mem_cons.2 ⟨subd6_1_326, List.forall_mem_cons.2 ⟨subd6_1_327, List.forall_mem_cons.2 ⟨subd6_1_328, List.forall_mem_cons.2 ⟨subd6_1_329, List.forall_mem_cons.2 ⟨subd6_1_330, List.forall_mem_cons.2 ⟨subd6_1_331, List.forall_mem_cons.2 ⟨subd6_1_332, List.forall_mem_cons.2 ⟨subd6_1_333, List.forall_mem_cons.2 ⟨subd6_1_334, List.forall_mem_cons.2 ⟨subd6_1_335, List.forall_mem_cons.2 ⟨subd6_1_336, List.forall_mem_cons.2 ⟨subd6_1_337, List.forall_mem_cons.2 ⟨subd6_1_338, List.forall_mem_cons.2 ⟨subd6_1_339, List.forall_mem_cons.2 ⟨subd6_1_340, List.forall_mem_cons.2 ⟨subd6_1_341, List.forall_mem_cons.2 ⟨subd6_1_342, List.forall_mem_cons.2 ⟨subd6_1_343, List.forall_mem_cons.2 ⟨subd6_1_344, List.forall_mem_cons.2 ⟨subd6_1_345, List.forall_mem_cons.2 ⟨subd6_1_346, List.forall_mem_cons.2 ⟨subd6_1_347, List.forall_mem_cons.2 ⟨subd6_1_348, List.forall_mem_cons.2 ⟨subd6_1_349, List.forall_mem_cons.2 ⟨subd6_1_350, List.forall_mem_cons.2 ⟨subd6_1_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_352 : subd6_1 [-4, -5, 4] = true := by decide +kernel
theorem subd6_1_353 : subd6_1 [-4, -5, 5] = true := by decide +kernel
theorem subd6_1_354 : subd6_1 [-4, -5, 6] = true := by decide +kernel
theorem subd6_1_355 : subd6_1 [-4, -5, 7] = true := by decide +kernel
theorem subd6_1_356 : subd6_1 [-4, -5, 8] = true := by decide +kernel
theorem subd6_1_357 : subd6_1 [-4, -4, -6] = true := by decide +kernel
theorem subd6_1_358 : subd6_1 [-4, -4, -5] = true := by decide +kernel
theorem subd6_1_359 : subd6_1 [-4, -4, -4] = true := by decide +kernel
theorem subd6_1_360 : subd6_1 [-4, -4, -3] = true := by decide +kernel
theorem subd6_1_361 : subd6_1 [-4, -4, -2] = true := by decide +kernel
theorem subd6_1_362 : subd6_1 [-4, -4, -1] = true := by decide +kernel
theorem subd6_1_363 : subd6_1 [-4, -4, 0] = true := by decide +kernel
theorem subd6_1_364 : subd6_1 [-4, -4, 1] = true := by decide +kernel
theorem subd6_1_365 : subd6_1 [-4, -4, 2] = true := by decide +kernel
theorem subd6_1_366 : subd6_1 [-4, -4, 3] = true := by decide +kernel
theorem subd6_1_367 : subd6_1 [-4, -4, 4] = true := by decide +kernel
theorem subd6_1_368 : subd6_1 [-4, -4, 5] = true := by decide +kernel
theorem subd6_1_369 : subd6_1 [-4, -4, 6] = true := by decide +kernel
theorem subd6_1_370 : subd6_1 [-4, -4, 7] = true := by decide +kernel
theorem subd6_1_371 : subd6_1 [-4, -4, 8] = true := by decide +kernel
theorem subd6_1_372 : subd6_1 [-4, -4, 9] = true := by decide +kernel
theorem subd6_1_373 : subd6_1 [-4, -3, -7] = true := by decide +kernel
theorem subd6_1_374 : subd6_1 [-4, -3, -6] = true := by decide +kernel
theorem subd6_1_375 : subd6_1 [-4, -3, -5] = true := by decide +kernel
theorem subd6_1_376 : subd6_1 [-4, -3, -4] = true := by decide +kernel
theorem subd6_1_377 : subd6_1 [-4, -3, -3] = true := by decide +kernel
theorem subd6_1_378 : subd6_1 [-4, -3, -2] = true := by decide +kernel
theorem subd6_1_379 : subd6_1 [-4, -3, -1] = true := by decide +kernel
theorem subd6_1_380 : subd6_1 [-4, -3, 0] = true := by decide +kernel
theorem subd6_1_381 : subd6_1 [-4, -3, 1] = true := by decide +kernel
theorem subd6_1_382 : subd6_1 [-4, -3, 2] = true := by decide +kernel
theorem subd6_1_383 : subd6_1 [-4, -3, 3] = true := by decide +kernel
theorem sbd6_1_11 : ∀ q ∈ blkd6_1_11, subd6_1 q = true := by
  unfold blkd6_1_11
  exact List.forall_mem_cons.2 ⟨subd6_1_352, List.forall_mem_cons.2 ⟨subd6_1_353, List.forall_mem_cons.2 ⟨subd6_1_354, List.forall_mem_cons.2 ⟨subd6_1_355, List.forall_mem_cons.2 ⟨subd6_1_356, List.forall_mem_cons.2 ⟨subd6_1_357, List.forall_mem_cons.2 ⟨subd6_1_358, List.forall_mem_cons.2 ⟨subd6_1_359, List.forall_mem_cons.2 ⟨subd6_1_360, List.forall_mem_cons.2 ⟨subd6_1_361, List.forall_mem_cons.2 ⟨subd6_1_362, List.forall_mem_cons.2 ⟨subd6_1_363, List.forall_mem_cons.2 ⟨subd6_1_364, List.forall_mem_cons.2 ⟨subd6_1_365, List.forall_mem_cons.2 ⟨subd6_1_366, List.forall_mem_cons.2 ⟨subd6_1_367, List.forall_mem_cons.2 ⟨subd6_1_368, List.forall_mem_cons.2 ⟨subd6_1_369, List.forall_mem_cons.2 ⟨subd6_1_370, List.forall_mem_cons.2 ⟨subd6_1_371, List.forall_mem_cons.2 ⟨subd6_1_372, List.forall_mem_cons.2 ⟨subd6_1_373, List.forall_mem_cons.2 ⟨subd6_1_374, List.forall_mem_cons.2 ⟨subd6_1_375, List.forall_mem_cons.2 ⟨subd6_1_376, List.forall_mem_cons.2 ⟨subd6_1_377, List.forall_mem_cons.2 ⟨subd6_1_378, List.forall_mem_cons.2 ⟨subd6_1_379, List.forall_mem_cons.2 ⟨subd6_1_380, List.forall_mem_cons.2 ⟨subd6_1_381, List.forall_mem_cons.2 ⟨subd6_1_382, List.forall_mem_cons.2 ⟨subd6_1_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_384 : subd6_1 [-4, -3, 4] = true := by decide +kernel
theorem subd6_1_385 : subd6_1 [-4, -3, 5] = true := by decide +kernel
theorem subd6_1_386 : subd6_1 [-4, -3, 6] = true := by decide +kernel
theorem subd6_1_387 : subd6_1 [-4, -3, 7] = true := by decide +kernel
theorem subd6_1_388 : subd6_1 [-4, -3, 8] = true := by decide +kernel
theorem subd6_1_389 : subd6_1 [-4, -3, 9] = true := by decide +kernel
theorem subd6_1_390 : subd6_1 [-4, -2, -7] = true := by decide +kernel
theorem subd6_1_391 : subd6_1 [-4, -2, -6] = true := by decide +kernel
theorem subd6_1_392 : subd6_1 [-4, -2, -5] = true := by decide +kernel
theorem subd6_1_393 : subd6_1 [-4, -2, -4] = true := by decide +kernel
theorem subd6_1_394 : subd6_1 [-4, -2, -3] = true := by decide +kernel
theorem subd6_1_395 : subd6_1 [-4, -2, -2] = true := by decide +kernel
theorem subd6_1_396 : subd6_1 [-4, -2, -1] = true := by decide +kernel
theorem subd6_1_397 : subd6_1 [-4, -2, 0] = true := by decide +kernel
theorem subd6_1_398 : subd6_1 [-4, -2, 1] = true := by decide +kernel
theorem subd6_1_399 : subd6_1 [-4, -2, 2] = true := by decide +kernel
theorem subd6_1_400 : subd6_1 [-4, -2, 3] = true := by decide +kernel
theorem subd6_1_401 : subd6_1 [-4, -2, 4] = true := by decide +kernel
theorem subd6_1_402 : subd6_1 [-4, -2, 5] = true := by decide +kernel
theorem subd6_1_403 : subd6_1 [-4, -2, 6] = true := by decide +kernel
theorem subd6_1_404 : subd6_1 [-4, -2, 7] = true := by decide +kernel
theorem subd6_1_405 : subd6_1 [-4, -2, 8] = true := by decide +kernel
theorem subd6_1_406 : subd6_1 [-4, -2, 9] = true := by decide +kernel
theorem subd6_1_407 : subd6_1 [-4, -2, 10] = true := by decide +kernel
theorem subd6_1_408 : subd6_1 [-4, -1, -8] = true := by decide +kernel
theorem subd6_1_409 : subd6_1 [-4, -1, -7] = true := by decide +kernel
theorem subd6_1_410 : subd6_1 [-4, -1, -6] = true := by decide +kernel
theorem subd6_1_411 : subd6_1 [-4, -1, -5] = true := by decide +kernel
theorem subd6_1_412 : subd6_1 [-4, -1, -4] = true := by decide +kernel
theorem subd6_1_413 : subd6_1 [-4, -1, -3] = true := by decide +kernel
theorem subd6_1_414 : subd6_1 [-4, -1, -2] = true := by decide +kernel
theorem subd6_1_415 : subd6_1 [-4, -1, -1] = true := by decide +kernel
theorem sbd6_1_12 : ∀ q ∈ blkd6_1_12, subd6_1 q = true := by
  unfold blkd6_1_12
  exact List.forall_mem_cons.2 ⟨subd6_1_384, List.forall_mem_cons.2 ⟨subd6_1_385, List.forall_mem_cons.2 ⟨subd6_1_386, List.forall_mem_cons.2 ⟨subd6_1_387, List.forall_mem_cons.2 ⟨subd6_1_388, List.forall_mem_cons.2 ⟨subd6_1_389, List.forall_mem_cons.2 ⟨subd6_1_390, List.forall_mem_cons.2 ⟨subd6_1_391, List.forall_mem_cons.2 ⟨subd6_1_392, List.forall_mem_cons.2 ⟨subd6_1_393, List.forall_mem_cons.2 ⟨subd6_1_394, List.forall_mem_cons.2 ⟨subd6_1_395, List.forall_mem_cons.2 ⟨subd6_1_396, List.forall_mem_cons.2 ⟨subd6_1_397, List.forall_mem_cons.2 ⟨subd6_1_398, List.forall_mem_cons.2 ⟨subd6_1_399, List.forall_mem_cons.2 ⟨subd6_1_400, List.forall_mem_cons.2 ⟨subd6_1_401, List.forall_mem_cons.2 ⟨subd6_1_402, List.forall_mem_cons.2 ⟨subd6_1_403, List.forall_mem_cons.2 ⟨subd6_1_404, List.forall_mem_cons.2 ⟨subd6_1_405, List.forall_mem_cons.2 ⟨subd6_1_406, List.forall_mem_cons.2 ⟨subd6_1_407, List.forall_mem_cons.2 ⟨subd6_1_408, List.forall_mem_cons.2 ⟨subd6_1_409, List.forall_mem_cons.2 ⟨subd6_1_410, List.forall_mem_cons.2 ⟨subd6_1_411, List.forall_mem_cons.2 ⟨subd6_1_412, List.forall_mem_cons.2 ⟨subd6_1_413, List.forall_mem_cons.2 ⟨subd6_1_414, List.forall_mem_cons.2 ⟨subd6_1_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_416 : subd6_1 [-4, -1, 0] = true := by decide +kernel
theorem subd6_1_417 : subd6_1 [-4, -1, 1] = true := by decide +kernel
theorem subd6_1_418 : subd6_1 [-4, -1, 2] = true := by decide +kernel
theorem subd6_1_419 : subd6_1 [-4, -1, 3] = true := by decide +kernel
theorem subd6_1_420 : subd6_1 [-4, -1, 4] = true := by decide +kernel
theorem subd6_1_421 : subd6_1 [-4, -1, 5] = true := by decide +kernel
theorem subd6_1_422 : subd6_1 [-4, -1, 6] = true := by decide +kernel
theorem subd6_1_423 : subd6_1 [-4, -1, 7] = true := by decide +kernel
theorem subd6_1_424 : subd6_1 [-4, -1, 8] = true := by decide +kernel
theorem subd6_1_425 : subd6_1 [-4, -1, 9] = true := by decide +kernel
theorem subd6_1_426 : subd6_1 [-4, -1, 10] = true := by decide +kernel
theorem subd6_1_427 : subd6_1 [-4, 0, -8] = true := by decide +kernel
theorem subd6_1_428 : subd6_1 [-4, 0, -7] = true := by decide +kernel
theorem subd6_1_429 : subd6_1 [-4, 0, -6] = true := by decide +kernel
theorem subd6_1_430 : subd6_1 [-4, 0, -5] = true := by decide +kernel
theorem subd6_1_431 : subd6_1 [-4, 0, -4] = true := by decide +kernel
theorem subd6_1_432 : subd6_1 [-4, 0, -3] = true := by decide +kernel
theorem subd6_1_433 : subd6_1 [-4, 0, -2] = true := by decide +kernel
theorem subd6_1_434 : subd6_1 [-4, 0, -1] = true := by decide +kernel
theorem subd6_1_435 : subd6_1 [-4, 0, 0] = true := by decide +kernel
theorem subd6_1_436 : subd6_1 [-4, 0, 1] = true := by decide +kernel
theorem subd6_1_437 : subd6_1 [-4, 0, 2] = true := by decide +kernel
theorem subd6_1_438 : subd6_1 [-4, 0, 3] = true := by decide +kernel
theorem subd6_1_439 : subd6_1 [-4, 0, 4] = true := by decide +kernel
theorem subd6_1_440 : subd6_1 [-4, 0, 5] = true := by decide +kernel
theorem subd6_1_441 : subd6_1 [-4, 0, 6] = true := by decide +kernel
theorem subd6_1_442 : subd6_1 [-4, 0, 7] = true := by decide +kernel
theorem subd6_1_443 : subd6_1 [-4, 0, 8] = true := by decide +kernel
theorem subd6_1_444 : subd6_1 [-4, 0, 9] = true := by decide +kernel
theorem subd6_1_445 : subd6_1 [-4, 0, 10] = true := by decide +kernel
theorem subd6_1_446 : subd6_1 [-4, 1, -8] = true := by decide +kernel
theorem subd6_1_447 : subd6_1 [-4, 1, -7] = true := by decide +kernel
theorem sbd6_1_13 : ∀ q ∈ blkd6_1_13, subd6_1 q = true := by
  unfold blkd6_1_13
  exact List.forall_mem_cons.2 ⟨subd6_1_416, List.forall_mem_cons.2 ⟨subd6_1_417, List.forall_mem_cons.2 ⟨subd6_1_418, List.forall_mem_cons.2 ⟨subd6_1_419, List.forall_mem_cons.2 ⟨subd6_1_420, List.forall_mem_cons.2 ⟨subd6_1_421, List.forall_mem_cons.2 ⟨subd6_1_422, List.forall_mem_cons.2 ⟨subd6_1_423, List.forall_mem_cons.2 ⟨subd6_1_424, List.forall_mem_cons.2 ⟨subd6_1_425, List.forall_mem_cons.2 ⟨subd6_1_426, List.forall_mem_cons.2 ⟨subd6_1_427, List.forall_mem_cons.2 ⟨subd6_1_428, List.forall_mem_cons.2 ⟨subd6_1_429, List.forall_mem_cons.2 ⟨subd6_1_430, List.forall_mem_cons.2 ⟨subd6_1_431, List.forall_mem_cons.2 ⟨subd6_1_432, List.forall_mem_cons.2 ⟨subd6_1_433, List.forall_mem_cons.2 ⟨subd6_1_434, List.forall_mem_cons.2 ⟨subd6_1_435, List.forall_mem_cons.2 ⟨subd6_1_436, List.forall_mem_cons.2 ⟨subd6_1_437, List.forall_mem_cons.2 ⟨subd6_1_438, List.forall_mem_cons.2 ⟨subd6_1_439, List.forall_mem_cons.2 ⟨subd6_1_440, List.forall_mem_cons.2 ⟨subd6_1_441, List.forall_mem_cons.2 ⟨subd6_1_442, List.forall_mem_cons.2 ⟨subd6_1_443, List.forall_mem_cons.2 ⟨subd6_1_444, List.forall_mem_cons.2 ⟨subd6_1_445, List.forall_mem_cons.2 ⟨subd6_1_446, List.forall_mem_cons.2 ⟨subd6_1_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_448 : subd6_1 [-4, 1, -6] = true := by decide +kernel
theorem subd6_1_449 : subd6_1 [-4, 1, -5] = true := by decide +kernel
theorem subd6_1_450 : subd6_1 [-4, 1, -4] = true := by decide +kernel
theorem subd6_1_451 : subd6_1 [-4, 1, -3] = true := by decide +kernel
theorem subd6_1_452 : subd6_1 [-4, 1, -2] = true := by decide +kernel
theorem subd6_1_453 : subd6_1 [-4, 1, -1] = true := by decide +kernel
theorem subd6_1_454 : subd6_1 [-4, 1, 0] = true := by decide +kernel
theorem subd6_1_455 : subd6_1 [-4, 1, 1] = true := by decide +kernel
theorem subd6_1_456 : subd6_1 [-4, 1, 2] = true := by decide +kernel
theorem subd6_1_457 : subd6_1 [-4, 1, 3] = true := by decide +kernel
theorem subd6_1_458 : subd6_1 [-4, 1, 4] = true := by decide +kernel
theorem subd6_1_459 : subd6_1 [-4, 1, 5] = true := by decide +kernel
theorem subd6_1_460 : subd6_1 [-4, 1, 6] = true := by decide +kernel
theorem subd6_1_461 : subd6_1 [-4, 1, 7] = true := by decide +kernel
theorem subd6_1_462 : subd6_1 [-4, 1, 8] = true := by decide +kernel
theorem subd6_1_463 : subd6_1 [-4, 1, 9] = true := by decide +kernel
theorem subd6_1_464 : subd6_1 [-4, 1, 10] = true := by decide +kernel
theorem subd6_1_465 : subd6_1 [-4, 2, -8] = true := by decide +kernel
theorem subd6_1_466 : subd6_1 [-4, 2, -7] = true := by decide +kernel
theorem subd6_1_467 : subd6_1 [-4, 2, -6] = true := by decide +kernel
theorem subd6_1_468 : subd6_1 [-4, 2, -5] = true := by decide +kernel
theorem subd6_1_469 : subd6_1 [-4, 2, -4] = true := by decide +kernel
theorem subd6_1_470 : subd6_1 [-4, 2, -3] = true := by decide +kernel
theorem subd6_1_471 : subd6_1 [-4, 2, -2] = true := by decide +kernel
theorem subd6_1_472 : subd6_1 [-4, 2, -1] = true := by decide +kernel
theorem subd6_1_473 : subd6_1 [-4, 2, 0] = true := by decide +kernel
theorem subd6_1_474 : subd6_1 [-4, 2, 1] = true := by decide +kernel
theorem subd6_1_475 : subd6_1 [-4, 2, 2] = true := by decide +kernel
theorem subd6_1_476 : subd6_1 [-4, 2, 3] = true := by decide +kernel
theorem subd6_1_477 : subd6_1 [-4, 2, 4] = true := by decide +kernel
theorem subd6_1_478 : subd6_1 [-4, 2, 5] = true := by decide +kernel
theorem subd6_1_479 : subd6_1 [-4, 2, 6] = true := by decide +kernel
theorem sbd6_1_14 : ∀ q ∈ blkd6_1_14, subd6_1 q = true := by
  unfold blkd6_1_14
  exact List.forall_mem_cons.2 ⟨subd6_1_448, List.forall_mem_cons.2 ⟨subd6_1_449, List.forall_mem_cons.2 ⟨subd6_1_450, List.forall_mem_cons.2 ⟨subd6_1_451, List.forall_mem_cons.2 ⟨subd6_1_452, List.forall_mem_cons.2 ⟨subd6_1_453, List.forall_mem_cons.2 ⟨subd6_1_454, List.forall_mem_cons.2 ⟨subd6_1_455, List.forall_mem_cons.2 ⟨subd6_1_456, List.forall_mem_cons.2 ⟨subd6_1_457, List.forall_mem_cons.2 ⟨subd6_1_458, List.forall_mem_cons.2 ⟨subd6_1_459, List.forall_mem_cons.2 ⟨subd6_1_460, List.forall_mem_cons.2 ⟨subd6_1_461, List.forall_mem_cons.2 ⟨subd6_1_462, List.forall_mem_cons.2 ⟨subd6_1_463, List.forall_mem_cons.2 ⟨subd6_1_464, List.forall_mem_cons.2 ⟨subd6_1_465, List.forall_mem_cons.2 ⟨subd6_1_466, List.forall_mem_cons.2 ⟨subd6_1_467, List.forall_mem_cons.2 ⟨subd6_1_468, List.forall_mem_cons.2 ⟨subd6_1_469, List.forall_mem_cons.2 ⟨subd6_1_470, List.forall_mem_cons.2 ⟨subd6_1_471, List.forall_mem_cons.2 ⟨subd6_1_472, List.forall_mem_cons.2 ⟨subd6_1_473, List.forall_mem_cons.2 ⟨subd6_1_474, List.forall_mem_cons.2 ⟨subd6_1_475, List.forall_mem_cons.2 ⟨subd6_1_476, List.forall_mem_cons.2 ⟨subd6_1_477, List.forall_mem_cons.2 ⟨subd6_1_478, List.forall_mem_cons.2 ⟨subd6_1_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_480 : subd6_1 [-4, 2, 7] = true := by decide +kernel
theorem subd6_1_481 : subd6_1 [-4, 2, 8] = true := by decide +kernel
theorem subd6_1_482 : subd6_1 [-4, 2, 9] = true := by decide +kernel
theorem subd6_1_483 : subd6_1 [-4, 2, 10] = true := by decide +kernel
theorem subd6_1_484 : subd6_1 [-4, 3, -8] = true := by decide +kernel
theorem subd6_1_485 : subd6_1 [-4, 3, -7] = true := by decide +kernel
theorem subd6_1_486 : subd6_1 [-4, 3, -6] = true := by decide +kernel
theorem subd6_1_487 : subd6_1 [-4, 3, -5] = true := by decide +kernel
theorem subd6_1_488 : subd6_1 [-4, 3, -4] = true := by decide +kernel
theorem subd6_1_489 : subd6_1 [-4, 3, -3] = true := by decide +kernel
theorem subd6_1_490 : subd6_1 [-4, 3, -2] = true := by decide +kernel
theorem subd6_1_491 : subd6_1 [-4, 3, -1] = true := by decide +kernel
theorem subd6_1_492 : subd6_1 [-4, 3, 0] = true := by decide +kernel
theorem subd6_1_493 : subd6_1 [-4, 3, 1] = true := by decide +kernel
theorem subd6_1_494 : subd6_1 [-4, 3, 2] = true := by decide +kernel
theorem subd6_1_495 : subd6_1 [-4, 3, 3] = true := by decide +kernel
theorem subd6_1_496 : subd6_1 [-4, 3, 4] = true := by decide +kernel
theorem subd6_1_497 : subd6_1 [-4, 3, 5] = true := by decide +kernel
theorem subd6_1_498 : subd6_1 [-4, 3, 6] = true := by decide +kernel
theorem subd6_1_499 : subd6_1 [-4, 3, 7] = true := by decide +kernel
theorem subd6_1_500 : subd6_1 [-4, 3, 8] = true := by decide +kernel
theorem subd6_1_501 : subd6_1 [-4, 3, 9] = true := by decide +kernel
theorem subd6_1_502 : subd6_1 [-4, 3, 10] = true := by decide +kernel
theorem subd6_1_503 : subd6_1 [-4, 4, -8] = true := by decide +kernel
theorem subd6_1_504 : subd6_1 [-4, 4, -7] = true := by decide +kernel
theorem subd6_1_505 : subd6_1 [-4, 4, -6] = true := by decide +kernel
theorem subd6_1_506 : subd6_1 [-4, 4, -5] = true := by decide +kernel
theorem subd6_1_507 : subd6_1 [-4, 4, -4] = true := by decide +kernel
theorem subd6_1_508 : subd6_1 [-4, 4, -3] = true := by decide +kernel
theorem subd6_1_509 : subd6_1 [-4, 4, -2] = true := by decide +kernel
theorem subd6_1_510 : subd6_1 [-4, 4, -1] = true := by decide +kernel
theorem subd6_1_511 : subd6_1 [-4, 4, 0] = true := by decide +kernel
theorem sbd6_1_15 : ∀ q ∈ blkd6_1_15, subd6_1 q = true := by
  unfold blkd6_1_15
  exact List.forall_mem_cons.2 ⟨subd6_1_480, List.forall_mem_cons.2 ⟨subd6_1_481, List.forall_mem_cons.2 ⟨subd6_1_482, List.forall_mem_cons.2 ⟨subd6_1_483, List.forall_mem_cons.2 ⟨subd6_1_484, List.forall_mem_cons.2 ⟨subd6_1_485, List.forall_mem_cons.2 ⟨subd6_1_486, List.forall_mem_cons.2 ⟨subd6_1_487, List.forall_mem_cons.2 ⟨subd6_1_488, List.forall_mem_cons.2 ⟨subd6_1_489, List.forall_mem_cons.2 ⟨subd6_1_490, List.forall_mem_cons.2 ⟨subd6_1_491, List.forall_mem_cons.2 ⟨subd6_1_492, List.forall_mem_cons.2 ⟨subd6_1_493, List.forall_mem_cons.2 ⟨subd6_1_494, List.forall_mem_cons.2 ⟨subd6_1_495, List.forall_mem_cons.2 ⟨subd6_1_496, List.forall_mem_cons.2 ⟨subd6_1_497, List.forall_mem_cons.2 ⟨subd6_1_498, List.forall_mem_cons.2 ⟨subd6_1_499, List.forall_mem_cons.2 ⟨subd6_1_500, List.forall_mem_cons.2 ⟨subd6_1_501, List.forall_mem_cons.2 ⟨subd6_1_502, List.forall_mem_cons.2 ⟨subd6_1_503, List.forall_mem_cons.2 ⟨subd6_1_504, List.forall_mem_cons.2 ⟨subd6_1_505, List.forall_mem_cons.2 ⟨subd6_1_506, List.forall_mem_cons.2 ⟨subd6_1_507, List.forall_mem_cons.2 ⟨subd6_1_508, List.forall_mem_cons.2 ⟨subd6_1_509, List.forall_mem_cons.2 ⟨subd6_1_510, List.forall_mem_cons.2 ⟨subd6_1_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_512 : subd6_1 [-4, 4, 1] = true := by decide +kernel
theorem subd6_1_513 : subd6_1 [-4, 4, 2] = true := by decide +kernel
theorem subd6_1_514 : subd6_1 [-4, 4, 3] = true := by decide +kernel
theorem subd6_1_515 : subd6_1 [-4, 4, 4] = true := by decide +kernel
theorem subd6_1_516 : subd6_1 [-4, 4, 5] = true := by decide +kernel
theorem subd6_1_517 : subd6_1 [-4, 4, 6] = true := by decide +kernel
theorem subd6_1_518 : subd6_1 [-4, 4, 7] = true := by decide +kernel
theorem subd6_1_519 : subd6_1 [-4, 4, 8] = true := by decide +kernel
theorem subd6_1_520 : subd6_1 [-4, 4, 9] = true := by decide +kernel
theorem subd6_1_521 : subd6_1 [-4, 5, -8] = true := by decide +kernel
theorem subd6_1_522 : subd6_1 [-4, 5, -7] = true := by decide +kernel
theorem subd6_1_523 : subd6_1 [-4, 5, -6] = true := by decide +kernel
theorem subd6_1_524 : subd6_1 [-4, 5, -5] = true := by decide +kernel
theorem subd6_1_525 : subd6_1 [-4, 5, -4] = true := by decide +kernel
theorem subd6_1_526 : subd6_1 [-4, 5, -3] = true := by decide +kernel
theorem subd6_1_527 : subd6_1 [-4, 5, -2] = true := by decide +kernel
theorem subd6_1_528 : subd6_1 [-4, 5, -1] = true := by decide +kernel
theorem subd6_1_529 : subd6_1 [-4, 5, 0] = true := by decide +kernel
theorem subd6_1_530 : subd6_1 [-4, 5, 1] = true := by decide +kernel
theorem subd6_1_531 : subd6_1 [-4, 5, 2] = true := by decide +kernel
theorem subd6_1_532 : subd6_1 [-4, 5, 3] = true := by decide +kernel
theorem subd6_1_533 : subd6_1 [-4, 5, 4] = true := by decide +kernel
theorem subd6_1_534 : subd6_1 [-4, 5, 5] = true := by decide +kernel
theorem subd6_1_535 : subd6_1 [-4, 5, 6] = true := by decide +kernel
theorem subd6_1_536 : subd6_1 [-4, 5, 7] = true := by decide +kernel
theorem subd6_1_537 : subd6_1 [-4, 5, 8] = true := by decide +kernel
theorem subd6_1_538 : subd6_1 [-4, 5, 9] = true := by decide +kernel
theorem subd6_1_539 : subd6_1 [-4, 6, -7] = true := by decide +kernel
theorem subd6_1_540 : subd6_1 [-4, 6, -6] = true := by decide +kernel
theorem subd6_1_541 : subd6_1 [-4, 6, -5] = true := by decide +kernel
theorem subd6_1_542 : subd6_1 [-4, 6, -4] = true := by decide +kernel
theorem subd6_1_543 : subd6_1 [-4, 6, -3] = true := by decide +kernel
theorem sbd6_1_16 : ∀ q ∈ blkd6_1_16, subd6_1 q = true := by
  unfold blkd6_1_16
  exact List.forall_mem_cons.2 ⟨subd6_1_512, List.forall_mem_cons.2 ⟨subd6_1_513, List.forall_mem_cons.2 ⟨subd6_1_514, List.forall_mem_cons.2 ⟨subd6_1_515, List.forall_mem_cons.2 ⟨subd6_1_516, List.forall_mem_cons.2 ⟨subd6_1_517, List.forall_mem_cons.2 ⟨subd6_1_518, List.forall_mem_cons.2 ⟨subd6_1_519, List.forall_mem_cons.2 ⟨subd6_1_520, List.forall_mem_cons.2 ⟨subd6_1_521, List.forall_mem_cons.2 ⟨subd6_1_522, List.forall_mem_cons.2 ⟨subd6_1_523, List.forall_mem_cons.2 ⟨subd6_1_524, List.forall_mem_cons.2 ⟨subd6_1_525, List.forall_mem_cons.2 ⟨subd6_1_526, List.forall_mem_cons.2 ⟨subd6_1_527, List.forall_mem_cons.2 ⟨subd6_1_528, List.forall_mem_cons.2 ⟨subd6_1_529, List.forall_mem_cons.2 ⟨subd6_1_530, List.forall_mem_cons.2 ⟨subd6_1_531, List.forall_mem_cons.2 ⟨subd6_1_532, List.forall_mem_cons.2 ⟨subd6_1_533, List.forall_mem_cons.2 ⟨subd6_1_534, List.forall_mem_cons.2 ⟨subd6_1_535, List.forall_mem_cons.2 ⟨subd6_1_536, List.forall_mem_cons.2 ⟨subd6_1_537, List.forall_mem_cons.2 ⟨subd6_1_538, List.forall_mem_cons.2 ⟨subd6_1_539, List.forall_mem_cons.2 ⟨subd6_1_540, List.forall_mem_cons.2 ⟨subd6_1_541, List.forall_mem_cons.2 ⟨subd6_1_542, List.forall_mem_cons.2 ⟨subd6_1_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_544 : subd6_1 [-4, 6, -2] = true := by decide +kernel
theorem subd6_1_545 : subd6_1 [-4, 6, -1] = true := by decide +kernel
theorem subd6_1_546 : subd6_1 [-4, 6, 0] = true := by decide +kernel
theorem subd6_1_547 : subd6_1 [-4, 6, 1] = true := by decide +kernel
theorem subd6_1_548 : subd6_1 [-4, 6, 2] = true := by decide +kernel
theorem subd6_1_549 : subd6_1 [-4, 6, 3] = true := by decide +kernel
theorem subd6_1_550 : subd6_1 [-4, 6, 4] = true := by decide +kernel
theorem subd6_1_551 : subd6_1 [-4, 6, 5] = true := by decide +kernel
theorem subd6_1_552 : subd6_1 [-4, 6, 6] = true := by decide +kernel
theorem subd6_1_553 : subd6_1 [-4, 6, 7] = true := by decide +kernel
theorem subd6_1_554 : subd6_1 [-4, 6, 8] = true := by decide +kernel
theorem subd6_1_555 : subd6_1 [-4, 7, -7] = true := by decide +kernel
theorem subd6_1_556 : subd6_1 [-4, 7, -6] = true := by decide +kernel
theorem subd6_1_557 : subd6_1 [-4, 7, -5] = true := by decide +kernel
theorem subd6_1_558 : subd6_1 [-4, 7, -4] = true := by decide +kernel
theorem subd6_1_559 : subd6_1 [-4, 7, -3] = true := by decide +kernel
theorem subd6_1_560 : subd6_1 [-4, 7, -2] = true := by decide +kernel
theorem subd6_1_561 : subd6_1 [-4, 7, -1] = true := by decide +kernel
theorem subd6_1_562 : subd6_1 [-4, 7, 0] = true := by decide +kernel
theorem subd6_1_563 : subd6_1 [-4, 7, 1] = true := by decide +kernel
theorem subd6_1_564 : subd6_1 [-4, 7, 2] = true := by decide +kernel
theorem subd6_1_565 : subd6_1 [-4, 7, 3] = true := by decide +kernel
theorem subd6_1_566 : subd6_1 [-4, 7, 4] = true := by decide +kernel
theorem subd6_1_567 : subd6_1 [-4, 7, 5] = true := by decide +kernel
theorem subd6_1_568 : subd6_1 [-4, 7, 6] = true := by decide +kernel
theorem subd6_1_569 : subd6_1 [-4, 7, 7] = true := by decide +kernel
theorem subd6_1_570 : subd6_1 [-4, 7, 8] = true := by decide +kernel
theorem subd6_1_571 : subd6_1 [-4, 8] = true := by decide +kernel
theorem subd6_1_572 : subd6_1 [-4, 9] = true := by decide +kernel
theorem subd6_1_573 : subd6_1 [-4, 10] = true := by decide +kernel
theorem subd6_1_574 : subd6_1 [-3, -9] = true := by decide +kernel
theorem subd6_1_575 : subd6_1 [-3, -8] = true := by decide +kernel
theorem sbd6_1_17 : ∀ q ∈ blkd6_1_17, subd6_1 q = true := by
  unfold blkd6_1_17
  exact List.forall_mem_cons.2 ⟨subd6_1_544, List.forall_mem_cons.2 ⟨subd6_1_545, List.forall_mem_cons.2 ⟨subd6_1_546, List.forall_mem_cons.2 ⟨subd6_1_547, List.forall_mem_cons.2 ⟨subd6_1_548, List.forall_mem_cons.2 ⟨subd6_1_549, List.forall_mem_cons.2 ⟨subd6_1_550, List.forall_mem_cons.2 ⟨subd6_1_551, List.forall_mem_cons.2 ⟨subd6_1_552, List.forall_mem_cons.2 ⟨subd6_1_553, List.forall_mem_cons.2 ⟨subd6_1_554, List.forall_mem_cons.2 ⟨subd6_1_555, List.forall_mem_cons.2 ⟨subd6_1_556, List.forall_mem_cons.2 ⟨subd6_1_557, List.forall_mem_cons.2 ⟨subd6_1_558, List.forall_mem_cons.2 ⟨subd6_1_559, List.forall_mem_cons.2 ⟨subd6_1_560, List.forall_mem_cons.2 ⟨subd6_1_561, List.forall_mem_cons.2 ⟨subd6_1_562, List.forall_mem_cons.2 ⟨subd6_1_563, List.forall_mem_cons.2 ⟨subd6_1_564, List.forall_mem_cons.2 ⟨subd6_1_565, List.forall_mem_cons.2 ⟨subd6_1_566, List.forall_mem_cons.2 ⟨subd6_1_567, List.forall_mem_cons.2 ⟨subd6_1_568, List.forall_mem_cons.2 ⟨subd6_1_569, List.forall_mem_cons.2 ⟨subd6_1_570, List.forall_mem_cons.2 ⟨subd6_1_571, List.forall_mem_cons.2 ⟨subd6_1_572, List.forall_mem_cons.2 ⟨subd6_1_573, List.forall_mem_cons.2 ⟨subd6_1_574, List.forall_mem_cons.2 ⟨subd6_1_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_576 : subd6_1 [-3, -7] = true := by decide +kernel
theorem subd6_1_577 : subd6_1 [-3, -6, -6] = true := by decide +kernel
theorem subd6_1_578 : subd6_1 [-3, -6, -5] = true := by decide +kernel
theorem subd6_1_579 : subd6_1 [-3, -6, -4] = true := by decide +kernel
theorem subd6_1_580 : subd6_1 [-3, -6, -3] = true := by decide +kernel
theorem subd6_1_581 : subd6_1 [-3, -6, -2] = true := by decide +kernel
theorem subd6_1_582 : subd6_1 [-3, -6, -1] = true := by decide +kernel
theorem subd6_1_583 : subd6_1 [-3, -6, 0] = true := by decide +kernel
theorem subd6_1_584 : subd6_1 [-3, -6, 1] = true := by decide +kernel
theorem subd6_1_585 : subd6_1 [-3, -6, 2] = true := by decide +kernel
theorem subd6_1_586 : subd6_1 [-3, -6, 3] = true := by decide +kernel
theorem subd6_1_587 : subd6_1 [-3, -6, 4] = true := by decide +kernel
theorem subd6_1_588 : subd6_1 [-3, -6, 5] = true := by decide +kernel
theorem subd6_1_589 : subd6_1 [-3, -6, 6] = true := by decide +kernel
theorem subd6_1_590 : subd6_1 [-3, -6, 7] = true := by decide +kernel
theorem subd6_1_591 : subd6_1 [-3, -6, 8] = true := by decide +kernel
theorem subd6_1_592 : subd6_1 [-3, -5, -7] = true := by decide +kernel
theorem subd6_1_593 : subd6_1 [-3, -5, -6] = true := by decide +kernel
theorem subd6_1_594 : subd6_1 [-3, -5, -5] = true := by decide +kernel
theorem subd6_1_595 : subd6_1 [-3, -5, -4] = true := by decide +kernel
theorem subd6_1_596 : subd6_1 [-3, -5, -3] = true := by decide +kernel
theorem subd6_1_597 : subd6_1 [-3, -5, -2] = true := by decide +kernel
theorem subd6_1_598 : subd6_1 [-3, -5, -1] = true := by decide +kernel
theorem subd6_1_599 : subd6_1 [-3, -5, 0] = true := by decide +kernel
theorem subd6_1_600 : subd6_1 [-3, -5, 1] = true := by decide +kernel
theorem subd6_1_601 : subd6_1 [-3, -5, 2] = true := by decide +kernel
theorem subd6_1_602 : subd6_1 [-3, -5, 3] = true := by decide +kernel
theorem subd6_1_603 : subd6_1 [-3, -5, 4] = true := by decide +kernel
theorem subd6_1_604 : subd6_1 [-3, -5, 5] = true := by decide +kernel
theorem subd6_1_605 : subd6_1 [-3, -5, 6] = true := by decide +kernel
theorem subd6_1_606 : subd6_1 [-3, -5, 7] = true := by decide +kernel
theorem subd6_1_607 : subd6_1 [-3, -5, 8] = true := by decide +kernel
theorem sbd6_1_18 : ∀ q ∈ blkd6_1_18, subd6_1 q = true := by
  unfold blkd6_1_18
  exact List.forall_mem_cons.2 ⟨subd6_1_576, List.forall_mem_cons.2 ⟨subd6_1_577, List.forall_mem_cons.2 ⟨subd6_1_578, List.forall_mem_cons.2 ⟨subd6_1_579, List.forall_mem_cons.2 ⟨subd6_1_580, List.forall_mem_cons.2 ⟨subd6_1_581, List.forall_mem_cons.2 ⟨subd6_1_582, List.forall_mem_cons.2 ⟨subd6_1_583, List.forall_mem_cons.2 ⟨subd6_1_584, List.forall_mem_cons.2 ⟨subd6_1_585, List.forall_mem_cons.2 ⟨subd6_1_586, List.forall_mem_cons.2 ⟨subd6_1_587, List.forall_mem_cons.2 ⟨subd6_1_588, List.forall_mem_cons.2 ⟨subd6_1_589, List.forall_mem_cons.2 ⟨subd6_1_590, List.forall_mem_cons.2 ⟨subd6_1_591, List.forall_mem_cons.2 ⟨subd6_1_592, List.forall_mem_cons.2 ⟨subd6_1_593, List.forall_mem_cons.2 ⟨subd6_1_594, List.forall_mem_cons.2 ⟨subd6_1_595, List.forall_mem_cons.2 ⟨subd6_1_596, List.forall_mem_cons.2 ⟨subd6_1_597, List.forall_mem_cons.2 ⟨subd6_1_598, List.forall_mem_cons.2 ⟨subd6_1_599, List.forall_mem_cons.2 ⟨subd6_1_600, List.forall_mem_cons.2 ⟨subd6_1_601, List.forall_mem_cons.2 ⟨subd6_1_602, List.forall_mem_cons.2 ⟨subd6_1_603, List.forall_mem_cons.2 ⟨subd6_1_604, List.forall_mem_cons.2 ⟨subd6_1_605, List.forall_mem_cons.2 ⟨subd6_1_606, List.forall_mem_cons.2 ⟨subd6_1_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_608 : subd6_1 [-3, -5, 9] = true := by decide +kernel
theorem subd6_1_609 : subd6_1 [-3, -4, -7] = true := by decide +kernel
theorem subd6_1_610 : subd6_1 [-3, -4, -6] = true := by decide +kernel
theorem subd6_1_611 : subd6_1 [-3, -4, -5] = true := by decide +kernel
theorem subd6_1_612 : subd6_1 [-3, -4, -4] = true := by decide +kernel
theorem subd6_1_613 : subd6_1 [-3, -4, -3] = true := by decide +kernel
theorem subd6_1_614 : subd6_1 [-3, -4, -2] = true := by decide +kernel
theorem subd6_1_615 : subd6_1 [-3, -4, -1] = true := by decide +kernel
theorem subd6_1_616 : subd6_1 [-3, -4, 0] = true := by decide +kernel
theorem subd6_1_617 : subd6_1 [-3, -4, 1] = true := by decide +kernel
theorem subd6_1_618 : subd6_1 [-3, -4, 2] = true := by decide +kernel
theorem subd6_1_619 : subd6_1 [-3, -4, 3] = true := by decide +kernel
theorem subd6_1_620 : subd6_1 [-3, -4, 4] = true := by decide +kernel
theorem subd6_1_621 : subd6_1 [-3, -4, 5] = true := by decide +kernel
theorem subd6_1_622 : subd6_1 [-3, -4, 6] = true := by decide +kernel
theorem subd6_1_623 : subd6_1 [-3, -4, 7] = true := by decide +kernel
theorem subd6_1_624 : subd6_1 [-3, -4, 8] = true := by decide +kernel
theorem subd6_1_625 : subd6_1 [-3, -4, 9] = true := by decide +kernel
theorem subd6_1_626 : subd6_1 [-3, -3, -8] = true := by decide +kernel
theorem subd6_1_627 : subd6_1 [-3, -3, -7] = true := by decide +kernel
theorem subd6_1_628 : subd6_1 [-3, -3, -6] = true := by decide +kernel
theorem subd6_1_629 : subd6_1 [-3, -3, -5] = true := by decide +kernel
theorem subd6_1_630 : subd6_1 [-3, -3, -4] = true := by decide +kernel
theorem subd6_1_631 : subd6_1 [-3, -3, -3] = true := by decide +kernel
theorem subd6_1_632 : subd6_1 [-3, -3, -2] = true := by decide +kernel
theorem subd6_1_633 : subd6_1 [-3, -3, -1] = true := by decide +kernel
theorem subd6_1_634 : subd6_1 [-3, -3, 0] = true := by decide +kernel
theorem subd6_1_635 : subd6_1 [-3, -3, 1] = true := by decide +kernel
theorem subd6_1_636 : subd6_1 [-3, -3, 2] = true := by decide +kernel
theorem subd6_1_637 : subd6_1 [-3, -3, 3] = true := by decide +kernel
theorem subd6_1_638 : subd6_1 [-3, -3, 4] = true := by decide +kernel
theorem subd6_1_639 : subd6_1 [-3, -3, 5] = true := by decide +kernel
theorem sbd6_1_19 : ∀ q ∈ blkd6_1_19, subd6_1 q = true := by
  unfold blkd6_1_19
  exact List.forall_mem_cons.2 ⟨subd6_1_608, List.forall_mem_cons.2 ⟨subd6_1_609, List.forall_mem_cons.2 ⟨subd6_1_610, List.forall_mem_cons.2 ⟨subd6_1_611, List.forall_mem_cons.2 ⟨subd6_1_612, List.forall_mem_cons.2 ⟨subd6_1_613, List.forall_mem_cons.2 ⟨subd6_1_614, List.forall_mem_cons.2 ⟨subd6_1_615, List.forall_mem_cons.2 ⟨subd6_1_616, List.forall_mem_cons.2 ⟨subd6_1_617, List.forall_mem_cons.2 ⟨subd6_1_618, List.forall_mem_cons.2 ⟨subd6_1_619, List.forall_mem_cons.2 ⟨subd6_1_620, List.forall_mem_cons.2 ⟨subd6_1_621, List.forall_mem_cons.2 ⟨subd6_1_622, List.forall_mem_cons.2 ⟨subd6_1_623, List.forall_mem_cons.2 ⟨subd6_1_624, List.forall_mem_cons.2 ⟨subd6_1_625, List.forall_mem_cons.2 ⟨subd6_1_626, List.forall_mem_cons.2 ⟨subd6_1_627, List.forall_mem_cons.2 ⟨subd6_1_628, List.forall_mem_cons.2 ⟨subd6_1_629, List.forall_mem_cons.2 ⟨subd6_1_630, List.forall_mem_cons.2 ⟨subd6_1_631, List.forall_mem_cons.2 ⟨subd6_1_632, List.forall_mem_cons.2 ⟨subd6_1_633, List.forall_mem_cons.2 ⟨subd6_1_634, List.forall_mem_cons.2 ⟨subd6_1_635, List.forall_mem_cons.2 ⟨subd6_1_636, List.forall_mem_cons.2 ⟨subd6_1_637, List.forall_mem_cons.2 ⟨subd6_1_638, List.forall_mem_cons.2 ⟨subd6_1_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_640 : subd6_1 [-3, -3, 6] = true := by decide +kernel
theorem subd6_1_641 : subd6_1 [-3, -3, 7] = true := by decide +kernel
theorem subd6_1_642 : subd6_1 [-3, -3, 8] = true := by decide +kernel
theorem subd6_1_643 : subd6_1 [-3, -3, 9] = true := by decide +kernel
theorem subd6_1_644 : subd6_1 [-3, -3, 10] = true := by decide +kernel
theorem subd6_1_645 : subd6_1 [-3, -2, -8] = true := by decide +kernel
theorem subd6_1_646 : subd6_1 [-3, -2, -7] = true := by decide +kernel
theorem subd6_1_647 : subd6_1 [-3, -2, -6] = true := by decide +kernel
theorem subd6_1_648 : subd6_1 [-3, -2, -5] = true := by decide +kernel
theorem subd6_1_649 : subd6_1 [-3, -2, -4] = true := by decide +kernel
theorem subd6_1_650 : subd6_1 [-3, -2, -3] = true := by decide +kernel
theorem subd6_1_651 : subd6_1 [-3, -2, -2] = true := by decide +kernel
theorem subd6_1_652 : subd6_1 [-3, -2, -1] = true := by decide +kernel
theorem subd6_1_653 : subd6_1 [-3, -2, 0] = true := by decide +kernel
theorem subd6_1_654 : subd6_1 [-3, -2, 1] = true := by decide +kernel
theorem subd6_1_655 : subd6_1 [-3, -2, 2] = true := by decide +kernel
theorem subd6_1_656 : subd6_1 [-3, -2, 3] = true := by decide +kernel
theorem subd6_1_657 : subd6_1 [-3, -2, 4] = true := by decide +kernel
theorem subd6_1_658 : subd6_1 [-3, -2, 5] = true := by decide +kernel
theorem subd6_1_659 : subd6_1 [-3, -2, 6] = true := by decide +kernel
theorem subd6_1_660 : subd6_1 [-3, -2, 7] = true := by decide +kernel
theorem subd6_1_661 : subd6_1 [-3, -2, 8] = true := by decide +kernel
theorem subd6_1_662 : subd6_1 [-3, -2, 9] = true := by decide +kernel
theorem subd6_1_663 : subd6_1 [-3, -2, 10] = true := by decide +kernel
theorem subd6_1_664 : subd6_1 [-3, -1, -9] = true := by decide +kernel
theorem subd6_1_665 : subd6_1 [-3, -1, -8] = true := by decide +kernel
theorem subd6_1_666 : subd6_1 [-3, -1, -7] = true := by decide +kernel
theorem subd6_1_667 : subd6_1 [-3, -1, -6] = true := by decide +kernel
theorem subd6_1_668 : subd6_1 [-3, -1, -5] = true := by decide +kernel
theorem subd6_1_669 : subd6_1 [-3, -1, -4] = true := by decide +kernel
theorem subd6_1_670 : subd6_1 [-3, -1, -3] = true := by decide +kernel
theorem subd6_1_671 : subd6_1 [-3, -1, -2] = true := by decide +kernel
theorem sbd6_1_20 : ∀ q ∈ blkd6_1_20, subd6_1 q = true := by
  unfold blkd6_1_20
  exact List.forall_mem_cons.2 ⟨subd6_1_640, List.forall_mem_cons.2 ⟨subd6_1_641, List.forall_mem_cons.2 ⟨subd6_1_642, List.forall_mem_cons.2 ⟨subd6_1_643, List.forall_mem_cons.2 ⟨subd6_1_644, List.forall_mem_cons.2 ⟨subd6_1_645, List.forall_mem_cons.2 ⟨subd6_1_646, List.forall_mem_cons.2 ⟨subd6_1_647, List.forall_mem_cons.2 ⟨subd6_1_648, List.forall_mem_cons.2 ⟨subd6_1_649, List.forall_mem_cons.2 ⟨subd6_1_650, List.forall_mem_cons.2 ⟨subd6_1_651, List.forall_mem_cons.2 ⟨subd6_1_652, List.forall_mem_cons.2 ⟨subd6_1_653, List.forall_mem_cons.2 ⟨subd6_1_654, List.forall_mem_cons.2 ⟨subd6_1_655, List.forall_mem_cons.2 ⟨subd6_1_656, List.forall_mem_cons.2 ⟨subd6_1_657, List.forall_mem_cons.2 ⟨subd6_1_658, List.forall_mem_cons.2 ⟨subd6_1_659, List.forall_mem_cons.2 ⟨subd6_1_660, List.forall_mem_cons.2 ⟨subd6_1_661, List.forall_mem_cons.2 ⟨subd6_1_662, List.forall_mem_cons.2 ⟨subd6_1_663, List.forall_mem_cons.2 ⟨subd6_1_664, List.forall_mem_cons.2 ⟨subd6_1_665, List.forall_mem_cons.2 ⟨subd6_1_666, List.forall_mem_cons.2 ⟨subd6_1_667, List.forall_mem_cons.2 ⟨subd6_1_668, List.forall_mem_cons.2 ⟨subd6_1_669, List.forall_mem_cons.2 ⟨subd6_1_670, List.forall_mem_cons.2 ⟨subd6_1_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C116
