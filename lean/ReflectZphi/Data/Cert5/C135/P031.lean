import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_1_160 : subd8_1 [-1, -6] = true := by decide +kernel
theorem subd8_1_161 : subd8_1 [-1, -5] = true := by decide +kernel
theorem subd8_1_162 : subd8_1 [-1, -4] = true := by decide +kernel
theorem subd8_1_163 : subd8_1 [-1, -3, -8] = true := by decide +kernel
theorem subd8_1_164 : subd8_1 [-1, -3, -7] = true := by decide +kernel
theorem subd8_1_165 : subd8_1 [-1, -3, -6] = true := by decide +kernel
theorem subd8_1_166 : subd8_1 [-1, -3, -5] = true := by decide +kernel
theorem subd8_1_167 : subd8_1 [-1, -3, -4] = true := by decide +kernel
theorem subd8_1_168 : subd8_1 [-1, -3, -3] = true := by decide +kernel
theorem subd8_1_169 : subd8_1 [-1, -3, -2] = true := by decide +kernel
theorem subd8_1_170 : subd8_1 [-1, -3, -1] = true := by decide +kernel
theorem subd8_1_171 : subd8_1 [-1, -3, 0] = true := by decide +kernel
theorem subd8_1_172 : subd8_1 [-1, -3, 1] = true := by decide +kernel
theorem subd8_1_173 : subd8_1 [-1, -3, 2] = true := by decide +kernel
theorem subd8_1_174 : subd8_1 [-1, -3, 3] = true := by decide +kernel
theorem subd8_1_175 : subd8_1 [-1, -3, 4] = true := by decide +kernel
theorem subd8_1_176 : subd8_1 [-1, -3, 5] = true := by decide +kernel
theorem subd8_1_177 : subd8_1 [-1, -3, 6] = true := by decide +kernel
theorem subd8_1_178 : subd8_1 [-1, -2, -9] = true := by decide +kernel
theorem subd8_1_179 : subd8_1 [-1, -2, -8] = true := by decide +kernel
theorem subd8_1_180 : subd8_1 [-1, -2, -7] = true := by decide +kernel
theorem subd8_1_181 : subd8_1 [-1, -2, -6] = true := by decide +kernel
theorem subd8_1_182 : subd8_1 [-1, -2, -5] = true := by decide +kernel
theorem subd8_1_183 : subd8_1 [-1, -2, -4] = true := by decide +kernel
theorem subd8_1_184 : subd8_1 [-1, -2, -3] = true := by decide +kernel
theorem subd8_1_185 : subd8_1 [-1, -2, -2] = true := by decide +kernel
theorem subd8_1_186 : subd8_1 [-1, -2, -1] = true := by decide +kernel
theorem subd8_1_187 : subd8_1 [-1, -2, 0] = true := by decide +kernel
theorem subd8_1_188 : subd8_1 [-1, -2, 1] = true := by decide +kernel
theorem subd8_1_189 : subd8_1 [-1, -2, 2] = true := by decide +kernel
theorem subd8_1_190 : subd8_1 [-1, -2, 3] = true := by decide +kernel
theorem subd8_1_191 : subd8_1 [-1, -2, 4] = true := by decide +kernel
theorem sbd8_1_5 : ∀ q ∈ blkd8_1_5, subd8_1 q = true := by
  unfold blkd8_1_5
  exact List.forall_mem_cons.2 ⟨subd8_1_160, List.forall_mem_cons.2 ⟨subd8_1_161, List.forall_mem_cons.2 ⟨subd8_1_162, List.forall_mem_cons.2 ⟨subd8_1_163, List.forall_mem_cons.2 ⟨subd8_1_164, List.forall_mem_cons.2 ⟨subd8_1_165, List.forall_mem_cons.2 ⟨subd8_1_166, List.forall_mem_cons.2 ⟨subd8_1_167, List.forall_mem_cons.2 ⟨subd8_1_168, List.forall_mem_cons.2 ⟨subd8_1_169, List.forall_mem_cons.2 ⟨subd8_1_170, List.forall_mem_cons.2 ⟨subd8_1_171, List.forall_mem_cons.2 ⟨subd8_1_172, List.forall_mem_cons.2 ⟨subd8_1_173, List.forall_mem_cons.2 ⟨subd8_1_174, List.forall_mem_cons.2 ⟨subd8_1_175, List.forall_mem_cons.2 ⟨subd8_1_176, List.forall_mem_cons.2 ⟨subd8_1_177, List.forall_mem_cons.2 ⟨subd8_1_178, List.forall_mem_cons.2 ⟨subd8_1_179, List.forall_mem_cons.2 ⟨subd8_1_180, List.forall_mem_cons.2 ⟨subd8_1_181, List.forall_mem_cons.2 ⟨subd8_1_182, List.forall_mem_cons.2 ⟨subd8_1_183, List.forall_mem_cons.2 ⟨subd8_1_184, List.forall_mem_cons.2 ⟨subd8_1_185, List.forall_mem_cons.2 ⟨subd8_1_186, List.forall_mem_cons.2 ⟨subd8_1_187, List.forall_mem_cons.2 ⟨subd8_1_188, List.forall_mem_cons.2 ⟨subd8_1_189, List.forall_mem_cons.2 ⟨subd8_1_190, List.forall_mem_cons.2 ⟨subd8_1_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_192 : subd8_1 [-1, -2, 5] = true := by decide +kernel
theorem subd8_1_193 : subd8_1 [-1, -2, 6] = true := by decide +kernel
theorem subd8_1_194 : subd8_1 [-1, -2, 7] = true := by decide +kernel
theorem subd8_1_195 : subd8_1 [-1, -1, -8] = true := by decide +kernel
theorem subd8_1_196 : subd8_1 [-1, -1, -7] = true := by decide +kernel
theorem subd8_1_197 : subd8_1 [-1, -1, -6] = true := by decide +kernel
theorem subd8_1_198 : subd8_1 [-1, -1, -5] = true := by decide +kernel
theorem subd8_1_199 : subd8_1 [-1, -1, -4] = true := by decide +kernel
theorem subd8_1_200 : subd8_1 [-1, -1, -3] = true := by decide +kernel
theorem subd8_1_201 : subd8_1 [-1, -1, -2] = true := by decide +kernel
theorem subd8_1_202 : subd8_1 [-1, -1, -1] = true := by decide +kernel
theorem subd8_1_203 : subd8_1 [-1, -1, 0] = true := by decide +kernel
theorem subd8_1_204 : subd8_1 [-1, -1, 1] = true := by decide +kernel
theorem subd8_1_205 : subd8_1 [-1, -1, 2] = true := by decide +kernel
theorem subd8_1_206 : subd8_1 [-1, -1, 3] = true := by decide +kernel
theorem subd8_1_207 : subd8_1 [-1, -1, 4] = true := by decide +kernel
theorem subd8_1_208 : subd8_1 [-1, -1, 5] = true := by decide +kernel
theorem subd8_1_209 : subd8_1 [-1, -1, 6] = true := by decide +kernel
theorem subd8_1_210 : subd8_1 [-1, -1, 7] = true := by decide +kernel
theorem subd8_1_211 : subd8_1 [-1, -1, 8] = true := by decide +kernel
theorem subd8_1_212 : subd8_1 [-1, 0, -8] = true := by decide +kernel
theorem subd8_1_213 : subd8_1 [-1, 0, -7] = true := by decide +kernel
theorem subd8_1_214 : subd8_1 [-1, 0, -6] = true := by decide +kernel
theorem subd8_1_215 : subd8_1 [-1, 0, -5] = true := by decide +kernel
theorem subd8_1_216 : subd8_1 [-1, 0, -4] = true := by decide +kernel
theorem subd8_1_217 : subd8_1 [-1, 0, -3] = true := by decide +kernel
theorem subd8_1_218 : subd8_1 [-1, 0, -2] = true := by decide +kernel
theorem subd8_1_219 : subd8_1 [-1, 0, -1] = true := by decide +kernel
theorem subd8_1_220 : subd8_1 [-1, 0, 0] = true := by decide +kernel
theorem subd8_1_221 : subd8_1 [-1, 0, 1] = true := by decide +kernel
theorem subd8_1_222 : subd8_1 [-1, 0, 2] = true := by decide +kernel
theorem subd8_1_223 : subd8_1 [-1, 0, 3] = true := by decide +kernel
theorem sbd8_1_6 : ∀ q ∈ blkd8_1_6, subd8_1 q = true := by
  unfold blkd8_1_6
  exact List.forall_mem_cons.2 ⟨subd8_1_192, List.forall_mem_cons.2 ⟨subd8_1_193, List.forall_mem_cons.2 ⟨subd8_1_194, List.forall_mem_cons.2 ⟨subd8_1_195, List.forall_mem_cons.2 ⟨subd8_1_196, List.forall_mem_cons.2 ⟨subd8_1_197, List.forall_mem_cons.2 ⟨subd8_1_198, List.forall_mem_cons.2 ⟨subd8_1_199, List.forall_mem_cons.2 ⟨subd8_1_200, List.forall_mem_cons.2 ⟨subd8_1_201, List.forall_mem_cons.2 ⟨subd8_1_202, List.forall_mem_cons.2 ⟨subd8_1_203, List.forall_mem_cons.2 ⟨subd8_1_204, List.forall_mem_cons.2 ⟨subd8_1_205, List.forall_mem_cons.2 ⟨subd8_1_206, List.forall_mem_cons.2 ⟨subd8_1_207, List.forall_mem_cons.2 ⟨subd8_1_208, List.forall_mem_cons.2 ⟨subd8_1_209, List.forall_mem_cons.2 ⟨subd8_1_210, List.forall_mem_cons.2 ⟨subd8_1_211, List.forall_mem_cons.2 ⟨subd8_1_212, List.forall_mem_cons.2 ⟨subd8_1_213, List.forall_mem_cons.2 ⟨subd8_1_214, List.forall_mem_cons.2 ⟨subd8_1_215, List.forall_mem_cons.2 ⟨subd8_1_216, List.forall_mem_cons.2 ⟨subd8_1_217, List.forall_mem_cons.2 ⟨subd8_1_218, List.forall_mem_cons.2 ⟨subd8_1_219, List.forall_mem_cons.2 ⟨subd8_1_220, List.forall_mem_cons.2 ⟨subd8_1_221, List.forall_mem_cons.2 ⟨subd8_1_222, List.forall_mem_cons.2 ⟨subd8_1_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_224 : subd8_1 [-1, 0, 4] = true := by decide +kernel
theorem subd8_1_225 : subd8_1 [-1, 0, 5] = true := by decide +kernel
theorem subd8_1_226 : subd8_1 [-1, 0, 6] = true := by decide +kernel
theorem subd8_1_227 : subd8_1 [-1, 0, 7] = true := by decide +kernel
theorem subd8_1_228 : subd8_1 [-1, 0, 8] = true := by decide +kernel
theorem subd8_1_229 : subd8_1 [-1, 1, -8] = true := by decide +kernel
theorem subd8_1_230 : subd8_1 [-1, 1, -7] = true := by decide +kernel
theorem subd8_1_231 : subd8_1 [-1, 1, -6] = true := by decide +kernel
theorem subd8_1_232 : subd8_1 [-1, 1, -5] = true := by decide +kernel
theorem subd8_1_233 : subd8_1 [-1, 1, -4] = true := by decide +kernel
theorem subd8_1_234 : subd8_1 [-1, 1, -3] = true := by decide +kernel
theorem subd8_1_235 : subd8_1 [-1, 1, -2] = true := by decide +kernel
theorem subd8_1_236 : subd8_1 [-1, 1, -1] = true := by decide +kernel
theorem subd8_1_237 : subd8_1 [-1, 1, 0] = true := by decide +kernel
theorem subd8_1_238 : subd8_1 [-1, 1, 1] = true := by decide +kernel
theorem subd8_1_239 : subd8_1 [-1, 1, 2] = true := by decide +kernel
theorem subd8_1_240 : subd8_1 [-1, 1, 3] = true := by decide +kernel
theorem subd8_1_241 : subd8_1 [-1, 1, 4] = true := by decide +kernel
theorem subd8_1_242 : subd8_1 [-1, 1, 5] = true := by decide +kernel
theorem subd8_1_243 : subd8_1 [-1, 1, 6] = true := by decide +kernel
theorem subd8_1_244 : subd8_1 [-1, 1, 7] = true := by decide +kernel
theorem subd8_1_245 : subd8_1 [-1, 1, 8] = true := by decide +kernel
theorem subd8_1_246 : subd8_1 [-1, 2, -7] = true := by decide +kernel
theorem subd8_1_247 : subd8_1 [-1, 2, -6] = true := by decide +kernel
theorem subd8_1_248 : subd8_1 [-1, 2, -5] = true := by decide +kernel
theorem subd8_1_249 : subd8_1 [-1, 2, -4] = true := by decide +kernel
theorem subd8_1_250 : subd8_1 [-1, 2, -3] = true := by decide +kernel
theorem subd8_1_251 : subd8_1 [-1, 2, -2] = true := by decide +kernel
theorem subd8_1_252 : subd8_1 [-1, 2, -1] = true := by decide +kernel
theorem subd8_1_253 : subd8_1 [-1, 2, 0] = true := by decide +kernel
theorem subd8_1_254 : subd8_1 [-1, 2, 1] = true := by decide +kernel
theorem subd8_1_255 : subd8_1 [-1, 2, 2] = true := by decide +kernel
theorem sbd8_1_7 : ∀ q ∈ blkd8_1_7, subd8_1 q = true := by
  unfold blkd8_1_7
  exact List.forall_mem_cons.2 ⟨subd8_1_224, List.forall_mem_cons.2 ⟨subd8_1_225, List.forall_mem_cons.2 ⟨subd8_1_226, List.forall_mem_cons.2 ⟨subd8_1_227, List.forall_mem_cons.2 ⟨subd8_1_228, List.forall_mem_cons.2 ⟨subd8_1_229, List.forall_mem_cons.2 ⟨subd8_1_230, List.forall_mem_cons.2 ⟨subd8_1_231, List.forall_mem_cons.2 ⟨subd8_1_232, List.forall_mem_cons.2 ⟨subd8_1_233, List.forall_mem_cons.2 ⟨subd8_1_234, List.forall_mem_cons.2 ⟨subd8_1_235, List.forall_mem_cons.2 ⟨subd8_1_236, List.forall_mem_cons.2 ⟨subd8_1_237, List.forall_mem_cons.2 ⟨subd8_1_238, List.forall_mem_cons.2 ⟨subd8_1_239, List.forall_mem_cons.2 ⟨subd8_1_240, List.forall_mem_cons.2 ⟨subd8_1_241, List.forall_mem_cons.2 ⟨subd8_1_242, List.forall_mem_cons.2 ⟨subd8_1_243, List.forall_mem_cons.2 ⟨subd8_1_244, List.forall_mem_cons.2 ⟨subd8_1_245, List.forall_mem_cons.2 ⟨subd8_1_246, List.forall_mem_cons.2 ⟨subd8_1_247, List.forall_mem_cons.2 ⟨subd8_1_248, List.forall_mem_cons.2 ⟨subd8_1_249, List.forall_mem_cons.2 ⟨subd8_1_250, List.forall_mem_cons.2 ⟨subd8_1_251, List.forall_mem_cons.2 ⟨subd8_1_252, List.forall_mem_cons.2 ⟨subd8_1_253, List.forall_mem_cons.2 ⟨subd8_1_254, List.forall_mem_cons.2 ⟨subd8_1_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_256 : subd8_1 [-1, 2, 3] = true := by decide +kernel
theorem subd8_1_257 : subd8_1 [-1, 2, 4] = true := by decide +kernel
theorem subd8_1_258 : subd8_1 [-1, 2, 5] = true := by decide +kernel
theorem subd8_1_259 : subd8_1 [-1, 2, 6] = true := by decide +kernel
theorem subd8_1_260 : subd8_1 [-1, 2, 7] = true := by decide +kernel
theorem subd8_1_261 : subd8_1 [-1, 2, 8] = true := by decide +kernel
theorem subd8_1_262 : subd8_1 [-1, 3, -6] = true := by decide +kernel
theorem subd8_1_263 : subd8_1 [-1, 3, -5] = true := by decide +kernel
theorem subd8_1_264 : subd8_1 [-1, 3, -4] = true := by decide +kernel
theorem subd8_1_265 : subd8_1 [-1, 3, -3] = true := by decide +kernel
theorem subd8_1_266 : subd8_1 [-1, 3, -2] = true := by decide +kernel
theorem subd8_1_267 : subd8_1 [-1, 3, -1] = true := by decide +kernel
theorem subd8_1_268 : subd8_1 [-1, 3, 0] = true := by decide +kernel
theorem subd8_1_269 : subd8_1 [-1, 3, 1] = true := by decide +kernel
theorem subd8_1_270 : subd8_1 [-1, 3, 2] = true := by decide +kernel
theorem subd8_1_271 : subd8_1 [-1, 3, 3] = true := by decide +kernel
theorem subd8_1_272 : subd8_1 [-1, 3, 4] = true := by decide +kernel
theorem subd8_1_273 : subd8_1 [-1, 3, 5] = true := by decide +kernel
theorem subd8_1_274 : subd8_1 [-1, 3, 6] = true := by decide +kernel
theorem subd8_1_275 : subd8_1 [-1, 3, 7] = true := by decide +kernel
theorem subd8_1_276 : subd8_1 [-1, 3, 8] = true := by decide +kernel
theorem subd8_1_277 : subd8_1 [-1, 4] = true := by decide +kernel
theorem subd8_1_278 : subd8_1 [-1, 5] = true := by decide +kernel
theorem subd8_1_279 : subd8_1 [0, -7] = true := by decide +kernel
theorem subd8_1_280 : subd8_1 [0, -6] = true := by decide +kernel
theorem subd8_1_281 : subd8_1 [0, -5] = true := by decide +kernel
theorem subd8_1_282 : subd8_1 [0, -4] = true := by decide +kernel
theorem subd8_1_283 : subd8_1 [0, -3, -9] = true := by decide +kernel
theorem subd8_1_284 : subd8_1 [0, -3, -8] = true := by decide +kernel
theorem subd8_1_285 : subd8_1 [0, -3, -7] = true := by decide +kernel
theorem subd8_1_286 : subd8_1 [0, -3, -6] = true := by decide +kernel
theorem subd8_1_287 : subd8_1 [0, -3, -5] = true := by decide +kernel
theorem sbd8_1_8 : ∀ q ∈ blkd8_1_8, subd8_1 q = true := by
  unfold blkd8_1_8
  exact List.forall_mem_cons.2 ⟨subd8_1_256, List.forall_mem_cons.2 ⟨subd8_1_257, List.forall_mem_cons.2 ⟨subd8_1_258, List.forall_mem_cons.2 ⟨subd8_1_259, List.forall_mem_cons.2 ⟨subd8_1_260, List.forall_mem_cons.2 ⟨subd8_1_261, List.forall_mem_cons.2 ⟨subd8_1_262, List.forall_mem_cons.2 ⟨subd8_1_263, List.forall_mem_cons.2 ⟨subd8_1_264, List.forall_mem_cons.2 ⟨subd8_1_265, List.forall_mem_cons.2 ⟨subd8_1_266, List.forall_mem_cons.2 ⟨subd8_1_267, List.forall_mem_cons.2 ⟨subd8_1_268, List.forall_mem_cons.2 ⟨subd8_1_269, List.forall_mem_cons.2 ⟨subd8_1_270, List.forall_mem_cons.2 ⟨subd8_1_271, List.forall_mem_cons.2 ⟨subd8_1_272, List.forall_mem_cons.2 ⟨subd8_1_273, List.forall_mem_cons.2 ⟨subd8_1_274, List.forall_mem_cons.2 ⟨subd8_1_275, List.forall_mem_cons.2 ⟨subd8_1_276, List.forall_mem_cons.2 ⟨subd8_1_277, List.forall_mem_cons.2 ⟨subd8_1_278, List.forall_mem_cons.2 ⟨subd8_1_279, List.forall_mem_cons.2 ⟨subd8_1_280, List.forall_mem_cons.2 ⟨subd8_1_281, List.forall_mem_cons.2 ⟨subd8_1_282, List.forall_mem_cons.2 ⟨subd8_1_283, List.forall_mem_cons.2 ⟨subd8_1_284, List.forall_mem_cons.2 ⟨subd8_1_285, List.forall_mem_cons.2 ⟨subd8_1_286, List.forall_mem_cons.2 ⟨subd8_1_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_288 : subd8_1 [0, -3, -4] = true := by decide +kernel
theorem subd8_1_289 : subd8_1 [0, -3, -3] = true := by decide +kernel
theorem subd8_1_290 : subd8_1 [0, -3, -2] = true := by decide +kernel
theorem subd8_1_291 : subd8_1 [0, -3, -1] = true := by decide +kernel
theorem subd8_1_292 : subd8_1 [0, -3, 0] = true := by decide +kernel
theorem subd8_1_293 : subd8_1 [0, -3, 1] = true := by decide +kernel
theorem subd8_1_294 : subd8_1 [0, -3, 2] = true := by decide +kernel
theorem subd8_1_295 : subd8_1 [0, -3, 3] = true := by decide +kernel
theorem subd8_1_296 : subd8_1 [0, -3, 4] = true := by decide +kernel
theorem subd8_1_297 : subd8_1 [0, -3, 5] = true := by decide +kernel
theorem subd8_1_298 : subd8_1 [0, -3, 6] = true := by decide +kernel
theorem subd8_1_299 : subd8_1 [0, -2, -9] = true := by decide +kernel
theorem subd8_1_300 : subd8_1 [0, -2, -8] = true := by decide +kernel
theorem subd8_1_301 : subd8_1 [0, -2, -7] = true := by decide +kernel
theorem subd8_1_302 : subd8_1 [0, -2, -6] = true := by decide +kernel
theorem subd8_1_303 : subd8_1 [0, -2, -5] = true := by decide +kernel
theorem subd8_1_304 : subd8_1 [0, -2, -4] = true := by decide +kernel
theorem subd8_1_305 : subd8_1 [0, -2, -3] = true := by decide +kernel
theorem subd8_1_306 : subd8_1 [0, -2, -2] = true := by decide +kernel
theorem subd8_1_307 : subd8_1 [0, -2, -1] = true := by decide +kernel
theorem subd8_1_308 : subd8_1 [0, -2, 0] = true := by decide +kernel
theorem subd8_1_309 : subd8_1 [0, -2, 1] = true := by decide +kernel
theorem subd8_1_310 : subd8_1 [0, -2, 2] = true := by decide +kernel
theorem subd8_1_311 : subd8_1 [0, -2, 3] = true := by decide +kernel
theorem subd8_1_312 : subd8_1 [0, -2, 4] = true := by decide +kernel
theorem subd8_1_313 : subd8_1 [0, -2, 5] = true := by decide +kernel
theorem subd8_1_314 : subd8_1 [0, -2, 6] = true := by decide +kernel
theorem subd8_1_315 : subd8_1 [0, -2, 7] = true := by decide +kernel
theorem subd8_1_316 : subd8_1 [0, -1, -9] = true := by decide +kernel
theorem subd8_1_317 : subd8_1 [0, -1, -8] = true := by decide +kernel
theorem subd8_1_318 : subd8_1 [0, -1, -7] = true := by decide +kernel
theorem subd8_1_319 : subd8_1 [0, -1, -6] = true := by decide +kernel
theorem sbd8_1_9 : ∀ q ∈ blkd8_1_9, subd8_1 q = true := by
  unfold blkd8_1_9
  exact List.forall_mem_cons.2 ⟨subd8_1_288, List.forall_mem_cons.2 ⟨subd8_1_289, List.forall_mem_cons.2 ⟨subd8_1_290, List.forall_mem_cons.2 ⟨subd8_1_291, List.forall_mem_cons.2 ⟨subd8_1_292, List.forall_mem_cons.2 ⟨subd8_1_293, List.forall_mem_cons.2 ⟨subd8_1_294, List.forall_mem_cons.2 ⟨subd8_1_295, List.forall_mem_cons.2 ⟨subd8_1_296, List.forall_mem_cons.2 ⟨subd8_1_297, List.forall_mem_cons.2 ⟨subd8_1_298, List.forall_mem_cons.2 ⟨subd8_1_299, List.forall_mem_cons.2 ⟨subd8_1_300, List.forall_mem_cons.2 ⟨subd8_1_301, List.forall_mem_cons.2 ⟨subd8_1_302, List.forall_mem_cons.2 ⟨subd8_1_303, List.forall_mem_cons.2 ⟨subd8_1_304, List.forall_mem_cons.2 ⟨subd8_1_305, List.forall_mem_cons.2 ⟨subd8_1_306, List.forall_mem_cons.2 ⟨subd8_1_307, List.forall_mem_cons.2 ⟨subd8_1_308, List.forall_mem_cons.2 ⟨subd8_1_309, List.forall_mem_cons.2 ⟨subd8_1_310, List.forall_mem_cons.2 ⟨subd8_1_311, List.forall_mem_cons.2 ⟨subd8_1_312, List.forall_mem_cons.2 ⟨subd8_1_313, List.forall_mem_cons.2 ⟨subd8_1_314, List.forall_mem_cons.2 ⟨subd8_1_315, List.forall_mem_cons.2 ⟨subd8_1_316, List.forall_mem_cons.2 ⟨subd8_1_317, List.forall_mem_cons.2 ⟨subd8_1_318, List.forall_mem_cons.2 ⟨subd8_1_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_320 : subd8_1 [0, -1, -5] = true := by decide +kernel
theorem subd8_1_321 : subd8_1 [0, -1, -4] = true := by decide +kernel
theorem subd8_1_322 : subd8_1 [0, -1, -3] = true := by decide +kernel
theorem subd8_1_323 : subd8_1 [0, -1, -2] = true := by decide +kernel
theorem subd8_1_324 : subd8_1 [0, -1, -1] = true := by decide +kernel
theorem subd8_1_325 : subd8_1 [0, -1, 0] = true := by decide +kernel
theorem subd8_1_326 : subd8_1 [0, -1, 1] = true := by decide +kernel
theorem subd8_1_327 : subd8_1 [0, -1, 2] = true := by decide +kernel
theorem subd8_1_328 : subd8_1 [0, -1, 3] = true := by decide +kernel
theorem subd8_1_329 : subd8_1 [0, -1, 4] = true := by decide +kernel
theorem subd8_1_330 : subd8_1 [0, -1, 5] = true := by decide +kernel
theorem subd8_1_331 : subd8_1 [0, -1, 6] = true := by decide +kernel
theorem subd8_1_332 : subd8_1 [0, -1, 7] = true := by decide +kernel
theorem subd8_1_333 : subd8_1 [0, 0, -9] = true := by decide +kernel
theorem subd8_1_334 : subd8_1 [0, 0, -8] = true := by decide +kernel
theorem subd8_1_335 : subd8_1 [0, 0, -7] = true := by decide +kernel
theorem subd8_1_336 : subd8_1 [0, 0, -6] = true := by decide +kernel
theorem subd8_1_337 : subd8_1 [0, 0, -5] = true := by decide +kernel
theorem subd8_1_338 : subd8_1 [0, 0, -4] = true := by decide +kernel
theorem subd8_1_339 : subd8_1 [0, 0, -3] = true := by decide +kernel
theorem subd8_1_340 : subd8_1 [0, 0, -2] = true := by decide +kernel
theorem subd8_1_341 : subd8_1 [0, 0, -1] = true := by decide +kernel
theorem subd8_1_342 : subd8_1 [0, 0, 0] = true := by decide +kernel
theorem subd8_1_343 : subd8_1 [0, 0, 1] = true := by decide +kernel
theorem subd8_1_344 : subd8_1 [0, 0, 2] = true := by decide +kernel
theorem subd8_1_345 : subd8_1 [0, 0, 3] = true := by decide +kernel
theorem subd8_1_346 : subd8_1 [0, 0, 4] = true := by decide +kernel
theorem subd8_1_347 : subd8_1 [0, 0, 5] = true := by decide +kernel
theorem subd8_1_348 : subd8_1 [0, 0, 6] = true := by decide +kernel
theorem subd8_1_349 : subd8_1 [0, 0, 7] = true := by decide +kernel
theorem subd8_1_350 : subd8_1 [0, 0, 8] = true := by decide +kernel
theorem subd8_1_351 : subd8_1 [0, 1, -8] = true := by decide +kernel
theorem sbd8_1_10 : ∀ q ∈ blkd8_1_10, subd8_1 q = true := by
  unfold blkd8_1_10
  exact List.forall_mem_cons.2 ⟨subd8_1_320, List.forall_mem_cons.2 ⟨subd8_1_321, List.forall_mem_cons.2 ⟨subd8_1_322, List.forall_mem_cons.2 ⟨subd8_1_323, List.forall_mem_cons.2 ⟨subd8_1_324, List.forall_mem_cons.2 ⟨subd8_1_325, List.forall_mem_cons.2 ⟨subd8_1_326, List.forall_mem_cons.2 ⟨subd8_1_327, List.forall_mem_cons.2 ⟨subd8_1_328, List.forall_mem_cons.2 ⟨subd8_1_329, List.forall_mem_cons.2 ⟨subd8_1_330, List.forall_mem_cons.2 ⟨subd8_1_331, List.forall_mem_cons.2 ⟨subd8_1_332, List.forall_mem_cons.2 ⟨subd8_1_333, List.forall_mem_cons.2 ⟨subd8_1_334, List.forall_mem_cons.2 ⟨subd8_1_335, List.forall_mem_cons.2 ⟨subd8_1_336, List.forall_mem_cons.2 ⟨subd8_1_337, List.forall_mem_cons.2 ⟨subd8_1_338, List.forall_mem_cons.2 ⟨subd8_1_339, List.forall_mem_cons.2 ⟨subd8_1_340, List.forall_mem_cons.2 ⟨subd8_1_341, List.forall_mem_cons.2 ⟨subd8_1_342, List.forall_mem_cons.2 ⟨subd8_1_343, List.forall_mem_cons.2 ⟨subd8_1_344, List.forall_mem_cons.2 ⟨subd8_1_345, List.forall_mem_cons.2 ⟨subd8_1_346, List.forall_mem_cons.2 ⟨subd8_1_347, List.forall_mem_cons.2 ⟨subd8_1_348, List.forall_mem_cons.2 ⟨subd8_1_349, List.forall_mem_cons.2 ⟨subd8_1_350, List.forall_mem_cons.2 ⟨subd8_1_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_352 : subd8_1 [0, 1, -7] = true := by decide +kernel
theorem subd8_1_353 : subd8_1 [0, 1, -6] = true := by decide +kernel
theorem subd8_1_354 : subd8_1 [0, 1, -5] = true := by decide +kernel
theorem subd8_1_355 : subd8_1 [0, 1, -4] = true := by decide +kernel
theorem subd8_1_356 : subd8_1 [0, 1, -3] = true := by decide +kernel
theorem subd8_1_357 : subd8_1 [0, 1, -2] = true := by decide +kernel
theorem subd8_1_358 : subd8_1 [0, 1, -1] = true := by decide +kernel
theorem subd8_1_359 : subd8_1 [0, 1, 0] = true := by decide +kernel
theorem subd8_1_360 : subd8_1 [0, 1, 1] = true := by decide +kernel
theorem subd8_1_361 : subd8_1 [0, 1, 2] = true := by decide +kernel
theorem subd8_1_362 : subd8_1 [0, 1, 3] = true := by decide +kernel
theorem subd8_1_363 : subd8_1 [0, 1, 4] = true := by decide +kernel
theorem subd8_1_364 : subd8_1 [0, 1, 5] = true := by decide +kernel
theorem subd8_1_365 : subd8_1 [0, 1, 6] = true := by decide +kernel
theorem subd8_1_366 : subd8_1 [0, 1, 7] = true := by decide +kernel
theorem subd8_1_367 : subd8_1 [0, 1, 8] = true := by decide +kernel
theorem subd8_1_368 : subd8_1 [0, 2, -8] = true := by decide +kernel
theorem subd8_1_369 : subd8_1 [0, 2, -7] = true := by decide +kernel
theorem subd8_1_370 : subd8_1 [0, 2, -6] = true := by decide +kernel
theorem subd8_1_371 : subd8_1 [0, 2, -5] = true := by decide +kernel
theorem subd8_1_372 : subd8_1 [0, 2, -4] = true := by decide +kernel
theorem subd8_1_373 : subd8_1 [0, 2, -3] = true := by decide +kernel
theorem subd8_1_374 : subd8_1 [0, 2, -2] = true := by decide +kernel
theorem subd8_1_375 : subd8_1 [0, 2, -1] = true := by decide +kernel
theorem subd8_1_376 : subd8_1 [0, 2, 0] = true := by decide +kernel
theorem subd8_1_377 : subd8_1 [0, 2, 1] = true := by decide +kernel
theorem subd8_1_378 : subd8_1 [0, 2, 2] = true := by decide +kernel
theorem subd8_1_379 : subd8_1 [0, 2, 3] = true := by decide +kernel
theorem subd8_1_380 : subd8_1 [0, 2, 4] = true := by decide +kernel
theorem subd8_1_381 : subd8_1 [0, 2, 5] = true := by decide +kernel
theorem subd8_1_382 : subd8_1 [0, 2, 6] = true := by decide +kernel
theorem subd8_1_383 : subd8_1 [0, 2, 7] = true := by decide +kernel
theorem sbd8_1_11 : ∀ q ∈ blkd8_1_11, subd8_1 q = true := by
  unfold blkd8_1_11
  exact List.forall_mem_cons.2 ⟨subd8_1_352, List.forall_mem_cons.2 ⟨subd8_1_353, List.forall_mem_cons.2 ⟨subd8_1_354, List.forall_mem_cons.2 ⟨subd8_1_355, List.forall_mem_cons.2 ⟨subd8_1_356, List.forall_mem_cons.2 ⟨subd8_1_357, List.forall_mem_cons.2 ⟨subd8_1_358, List.forall_mem_cons.2 ⟨subd8_1_359, List.forall_mem_cons.2 ⟨subd8_1_360, List.forall_mem_cons.2 ⟨subd8_1_361, List.forall_mem_cons.2 ⟨subd8_1_362, List.forall_mem_cons.2 ⟨subd8_1_363, List.forall_mem_cons.2 ⟨subd8_1_364, List.forall_mem_cons.2 ⟨subd8_1_365, List.forall_mem_cons.2 ⟨subd8_1_366, List.forall_mem_cons.2 ⟨subd8_1_367, List.forall_mem_cons.2 ⟨subd8_1_368, List.forall_mem_cons.2 ⟨subd8_1_369, List.forall_mem_cons.2 ⟨subd8_1_370, List.forall_mem_cons.2 ⟨subd8_1_371, List.forall_mem_cons.2 ⟨subd8_1_372, List.forall_mem_cons.2 ⟨subd8_1_373, List.forall_mem_cons.2 ⟨subd8_1_374, List.forall_mem_cons.2 ⟨subd8_1_375, List.forall_mem_cons.2 ⟨subd8_1_376, List.forall_mem_cons.2 ⟨subd8_1_377, List.forall_mem_cons.2 ⟨subd8_1_378, List.forall_mem_cons.2 ⟨subd8_1_379, List.forall_mem_cons.2 ⟨subd8_1_380, List.forall_mem_cons.2 ⟨subd8_1_381, List.forall_mem_cons.2 ⟨subd8_1_382, List.forall_mem_cons.2 ⟨subd8_1_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_384 : subd8_1 [0, 2, 8] = true := by decide +kernel
theorem subd8_1_385 : subd8_1 [0, 3, -7] = true := by decide +kernel
theorem subd8_1_386 : subd8_1 [0, 3, -6] = true := by decide +kernel
theorem subd8_1_387 : subd8_1 [0, 3, -5] = true := by decide +kernel
theorem subd8_1_388 : subd8_1 [0, 3, -4] = true := by decide +kernel
theorem subd8_1_389 : subd8_1 [0, 3, -3] = true := by decide +kernel
theorem subd8_1_390 : subd8_1 [0, 3, -2] = true := by decide +kernel
theorem subd8_1_391 : subd8_1 [0, 3, -1] = true := by decide +kernel
theorem subd8_1_392 : subd8_1 [0, 3, 0] = true := by decide +kernel
theorem subd8_1_393 : subd8_1 [0, 3, 1] = true := by decide +kernel
theorem subd8_1_394 : subd8_1 [0, 3, 2] = true := by decide +kernel
theorem subd8_1_395 : subd8_1 [0, 3, 3] = true := by decide +kernel
theorem subd8_1_396 : subd8_1 [0, 3, 4] = true := by decide +kernel
theorem subd8_1_397 : subd8_1 [0, 3, 5] = true := by decide +kernel
theorem subd8_1_398 : subd8_1 [0, 3, 6] = true := by decide +kernel
theorem subd8_1_399 : subd8_1 [0, 3, 7] = true := by decide +kernel
theorem subd8_1_400 : subd8_1 [0, 3, 8] = true := by decide +kernel
theorem subd8_1_401 : subd8_1 [0, 4] = true := by decide +kernel
theorem subd8_1_402 : subd8_1 [0, 5] = true := by decide +kernel
theorem subd8_1_403 : subd8_1 [0, 6] = true := by decide +kernel
theorem subd8_1_404 : subd8_1 [1, -6] = true := by decide +kernel
theorem subd8_1_405 : subd8_1 [1, -5] = true := by decide +kernel
theorem subd8_1_406 : subd8_1 [1, -4] = true := by decide +kernel
theorem subd8_1_407 : subd8_1 [1, -3, -9] = true := by decide +kernel
theorem subd8_1_408 : subd8_1 [1, -3, -8] = true := by decide +kernel
theorem subd8_1_409 : subd8_1 [1, -3, -7] = true := by decide +kernel
theorem subd8_1_410 : subd8_1 [1, -3, -6] = true := by decide +kernel
theorem subd8_1_411 : subd8_1 [1, -3, -5] = true := by decide +kernel
theorem subd8_1_412 : subd8_1 [1, -3, -4] = true := by decide +kernel
theorem subd8_1_413 : subd8_1 [1, -3, -3] = true := by decide +kernel
theorem subd8_1_414 : subd8_1 [1, -3, -2] = true := by decide +kernel
theorem subd8_1_415 : subd8_1 [1, -3, -1] = true := by decide +kernel
theorem sbd8_1_12 : ∀ q ∈ blkd8_1_12, subd8_1 q = true := by
  unfold blkd8_1_12
  exact List.forall_mem_cons.2 ⟨subd8_1_384, List.forall_mem_cons.2 ⟨subd8_1_385, List.forall_mem_cons.2 ⟨subd8_1_386, List.forall_mem_cons.2 ⟨subd8_1_387, List.forall_mem_cons.2 ⟨subd8_1_388, List.forall_mem_cons.2 ⟨subd8_1_389, List.forall_mem_cons.2 ⟨subd8_1_390, List.forall_mem_cons.2 ⟨subd8_1_391, List.forall_mem_cons.2 ⟨subd8_1_392, List.forall_mem_cons.2 ⟨subd8_1_393, List.forall_mem_cons.2 ⟨subd8_1_394, List.forall_mem_cons.2 ⟨subd8_1_395, List.forall_mem_cons.2 ⟨subd8_1_396, List.forall_mem_cons.2 ⟨subd8_1_397, List.forall_mem_cons.2 ⟨subd8_1_398, List.forall_mem_cons.2 ⟨subd8_1_399, List.forall_mem_cons.2 ⟨subd8_1_400, List.forall_mem_cons.2 ⟨subd8_1_401, List.forall_mem_cons.2 ⟨subd8_1_402, List.forall_mem_cons.2 ⟨subd8_1_403, List.forall_mem_cons.2 ⟨subd8_1_404, List.forall_mem_cons.2 ⟨subd8_1_405, List.forall_mem_cons.2 ⟨subd8_1_406, List.forall_mem_cons.2 ⟨subd8_1_407, List.forall_mem_cons.2 ⟨subd8_1_408, List.forall_mem_cons.2 ⟨subd8_1_409, List.forall_mem_cons.2 ⟨subd8_1_410, List.forall_mem_cons.2 ⟨subd8_1_411, List.forall_mem_cons.2 ⟨subd8_1_412, List.forall_mem_cons.2 ⟨subd8_1_413, List.forall_mem_cons.2 ⟨subd8_1_414, List.forall_mem_cons.2 ⟨subd8_1_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_416 : subd8_1 [1, -3, 0] = true := by decide +kernel
theorem subd8_1_417 : subd8_1 [1, -3, 1] = true := by decide +kernel
theorem subd8_1_418 : subd8_1 [1, -3, 2] = true := by decide +kernel
theorem subd8_1_419 : subd8_1 [1, -3, 3] = true := by decide +kernel
theorem subd8_1_420 : subd8_1 [1, -3, 4] = true := by decide +kernel
theorem subd8_1_421 : subd8_1 [1, -3, 5] = true := by decide +kernel
theorem subd8_1_422 : subd8_1 [1, -2, -9] = true := by decide +kernel
theorem subd8_1_423 : subd8_1 [1, -2, -8] = true := by decide +kernel
theorem subd8_1_424 : subd8_1 [1, -2, -7] = true := by decide +kernel
theorem subd8_1_425 : subd8_1 [1, -2, -6] = true := by decide +kernel
theorem subd8_1_426 : subd8_1 [1, -2, -5] = true := by decide +kernel
theorem subd8_1_427 : subd8_1 [1, -2, -4] = true := by decide +kernel
theorem subd8_1_428 : subd8_1 [1, -2, -3] = true := by decide +kernel
theorem subd8_1_429 : subd8_1 [1, -2, -2] = true := by decide +kernel
theorem subd8_1_430 : subd8_1 [1, -2, -1] = true := by decide +kernel
theorem subd8_1_431 : subd8_1 [1, -2, 0] = true := by decide +kernel
theorem subd8_1_432 : subd8_1 [1, -2, 1] = true := by decide +kernel
theorem subd8_1_433 : subd8_1 [1, -2, 2] = true := by decide +kernel
theorem subd8_1_434 : subd8_1 [1, -2, 3] = true := by decide +kernel
theorem subd8_1_435 : subd8_1 [1, -2, 4] = true := by decide +kernel
theorem subd8_1_436 : subd8_1 [1, -2, 5] = true := by decide +kernel
theorem subd8_1_437 : subd8_1 [1, -2, 6] = true := by decide +kernel
theorem subd8_1_438 : subd8_1 [1, -1, -9] = true := by decide +kernel
theorem subd8_1_439 : subd8_1 [1, -1, -8] = true := by decide +kernel
theorem subd8_1_440 : subd8_1 [1, -1, -7] = true := by decide +kernel
theorem subd8_1_441 : subd8_1 [1, -1, -6] = true := by decide +kernel
theorem subd8_1_442 : subd8_1 [1, -1, -5] = true := by decide +kernel
theorem subd8_1_443 : subd8_1 [1, -1, -4] = true := by decide +kernel
theorem subd8_1_444 : subd8_1 [1, -1, -3] = true := by decide +kernel
theorem subd8_1_445 : subd8_1 [1, -1, -2] = true := by decide +kernel
theorem subd8_1_446 : subd8_1 [1, -1, -1] = true := by decide +kernel
theorem subd8_1_447 : subd8_1 [1, -1, 0] = true := by decide +kernel
theorem sbd8_1_13 : ∀ q ∈ blkd8_1_13, subd8_1 q = true := by
  unfold blkd8_1_13
  exact List.forall_mem_cons.2 ⟨subd8_1_416, List.forall_mem_cons.2 ⟨subd8_1_417, List.forall_mem_cons.2 ⟨subd8_1_418, List.forall_mem_cons.2 ⟨subd8_1_419, List.forall_mem_cons.2 ⟨subd8_1_420, List.forall_mem_cons.2 ⟨subd8_1_421, List.forall_mem_cons.2 ⟨subd8_1_422, List.forall_mem_cons.2 ⟨subd8_1_423, List.forall_mem_cons.2 ⟨subd8_1_424, List.forall_mem_cons.2 ⟨subd8_1_425, List.forall_mem_cons.2 ⟨subd8_1_426, List.forall_mem_cons.2 ⟨subd8_1_427, List.forall_mem_cons.2 ⟨subd8_1_428, List.forall_mem_cons.2 ⟨subd8_1_429, List.forall_mem_cons.2 ⟨subd8_1_430, List.forall_mem_cons.2 ⟨subd8_1_431, List.forall_mem_cons.2 ⟨subd8_1_432, List.forall_mem_cons.2 ⟨subd8_1_433, List.forall_mem_cons.2 ⟨subd8_1_434, List.forall_mem_cons.2 ⟨subd8_1_435, List.forall_mem_cons.2 ⟨subd8_1_436, List.forall_mem_cons.2 ⟨subd8_1_437, List.forall_mem_cons.2 ⟨subd8_1_438, List.forall_mem_cons.2 ⟨subd8_1_439, List.forall_mem_cons.2 ⟨subd8_1_440, List.forall_mem_cons.2 ⟨subd8_1_441, List.forall_mem_cons.2 ⟨subd8_1_442, List.forall_mem_cons.2 ⟨subd8_1_443, List.forall_mem_cons.2 ⟨subd8_1_444, List.forall_mem_cons.2 ⟨subd8_1_445, List.forall_mem_cons.2 ⟨subd8_1_446, List.forall_mem_cons.2 ⟨subd8_1_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_448 : subd8_1 [1, -1, 1] = true := by decide +kernel
theorem subd8_1_449 : subd8_1 [1, -1, 2] = true := by decide +kernel
theorem subd8_1_450 : subd8_1 [1, -1, 3] = true := by decide +kernel
theorem subd8_1_451 : subd8_1 [1, -1, 4] = true := by decide +kernel
theorem subd8_1_452 : subd8_1 [1, -1, 5] = true := by decide +kernel
theorem subd8_1_453 : subd8_1 [1, -1, 6] = true := by decide +kernel
theorem subd8_1_454 : subd8_1 [1, -1, 7] = true := by decide +kernel
theorem subd8_1_455 : subd8_1 [1, 0, -9] = true := by decide +kernel
theorem subd8_1_456 : subd8_1 [1, 0, -8] = true := by decide +kernel
theorem subd8_1_457 : subd8_1 [1, 0, -7] = true := by decide +kernel
theorem subd8_1_458 : subd8_1 [1, 0, -6] = true := by decide +kernel
theorem subd8_1_459 : subd8_1 [1, 0, -5] = true := by decide +kernel
theorem subd8_1_460 : subd8_1 [1, 0, -4] = true := by decide +kernel
theorem subd8_1_461 : subd8_1 [1, 0, -3] = true := by decide +kernel
theorem subd8_1_462 : subd8_1 [1, 0, -2] = true := by decide +kernel
theorem subd8_1_463 : subd8_1 [1, 0, -1] = true := by decide +kernel
theorem subd8_1_464 : subd8_1 [1, 0, 0] = true := by decide +kernel
theorem subd8_1_465 : subd8_1 [1, 0, 1] = true := by decide +kernel
theorem subd8_1_466 : subd8_1 [1, 0, 2] = true := by decide +kernel
theorem subd8_1_467 : subd8_1 [1, 0, 3] = true := by decide +kernel
theorem subd8_1_468 : subd8_1 [1, 0, 4] = true := by decide +kernel
theorem subd8_1_469 : subd8_1 [1, 0, 5] = true := by decide +kernel
theorem subd8_1_470 : subd8_1 [1, 0, 6] = true := by decide +kernel
theorem subd8_1_471 : subd8_1 [1, 0, 7] = true := by decide +kernel
theorem subd8_1_472 : subd8_1 [1, 1, -9] = true := by decide +kernel
theorem subd8_1_473 : subd8_1 [1, 1, -8] = true := by decide +kernel
theorem subd8_1_474 : subd8_1 [1, 1, -7] = true := by decide +kernel
theorem subd8_1_475 : subd8_1 [1, 1, -6] = true := by decide +kernel
theorem subd8_1_476 : subd8_1 [1, 1, -5] = true := by decide +kernel
theorem subd8_1_477 : subd8_1 [1, 1, -4] = true := by decide +kernel
theorem subd8_1_478 : subd8_1 [1, 1, -3] = true := by decide +kernel
theorem subd8_1_479 : subd8_1 [1, 1, -2] = true := by decide +kernel
theorem sbd8_1_14 : ∀ q ∈ blkd8_1_14, subd8_1 q = true := by
  unfold blkd8_1_14
  exact List.forall_mem_cons.2 ⟨subd8_1_448, List.forall_mem_cons.2 ⟨subd8_1_449, List.forall_mem_cons.2 ⟨subd8_1_450, List.forall_mem_cons.2 ⟨subd8_1_451, List.forall_mem_cons.2 ⟨subd8_1_452, List.forall_mem_cons.2 ⟨subd8_1_453, List.forall_mem_cons.2 ⟨subd8_1_454, List.forall_mem_cons.2 ⟨subd8_1_455, List.forall_mem_cons.2 ⟨subd8_1_456, List.forall_mem_cons.2 ⟨subd8_1_457, List.forall_mem_cons.2 ⟨subd8_1_458, List.forall_mem_cons.2 ⟨subd8_1_459, List.forall_mem_cons.2 ⟨subd8_1_460, List.forall_mem_cons.2 ⟨subd8_1_461, List.forall_mem_cons.2 ⟨subd8_1_462, List.forall_mem_cons.2 ⟨subd8_1_463, List.forall_mem_cons.2 ⟨subd8_1_464, List.forall_mem_cons.2 ⟨subd8_1_465, List.forall_mem_cons.2 ⟨subd8_1_466, List.forall_mem_cons.2 ⟨subd8_1_467, List.forall_mem_cons.2 ⟨subd8_1_468, List.forall_mem_cons.2 ⟨subd8_1_469, List.forall_mem_cons.2 ⟨subd8_1_470, List.forall_mem_cons.2 ⟨subd8_1_471, List.forall_mem_cons.2 ⟨subd8_1_472, List.forall_mem_cons.2 ⟨subd8_1_473, List.forall_mem_cons.2 ⟨subd8_1_474, List.forall_mem_cons.2 ⟨subd8_1_475, List.forall_mem_cons.2 ⟨subd8_1_476, List.forall_mem_cons.2 ⟨subd8_1_477, List.forall_mem_cons.2 ⟨subd8_1_478, List.forall_mem_cons.2 ⟨subd8_1_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_480 : subd8_1 [1, 1, -1] = true := by decide +kernel
theorem subd8_1_481 : subd8_1 [1, 1, 0] = true := by decide +kernel
theorem subd8_1_482 : subd8_1 [1, 1, 1] = true := by decide +kernel
theorem subd8_1_483 : subd8_1 [1, 1, 2] = true := by decide +kernel
theorem subd8_1_484 : subd8_1 [1, 1, 3] = true := by decide +kernel
theorem subd8_1_485 : subd8_1 [1, 1, 4] = true := by decide +kernel
theorem subd8_1_486 : subd8_1 [1, 1, 5] = true := by decide +kernel
theorem subd8_1_487 : subd8_1 [1, 1, 6] = true := by decide +kernel
theorem subd8_1_488 : subd8_1 [1, 1, 7] = true := by decide +kernel
theorem subd8_1_489 : subd8_1 [1, 2, -8] = true := by decide +kernel
theorem subd8_1_490 : subd8_1 [1, 2, -7] = true := by decide +kernel
theorem subd8_1_491 : subd8_1 [1, 2, -6] = true := by decide +kernel
theorem subd8_1_492 : subd8_1 [1, 2, -5] = true := by decide +kernel
theorem subd8_1_493 : subd8_1 [1, 2, -4] = true := by decide +kernel
theorem subd8_1_494 : subd8_1 [1, 2, -3] = true := by decide +kernel
theorem subd8_1_495 : subd8_1 [1, 2, -2] = true := by decide +kernel
theorem subd8_1_496 : subd8_1 [1, 2, -1] = true := by decide +kernel
theorem subd8_1_497 : subd8_1 [1, 2, 0] = true := by decide +kernel
theorem subd8_1_498 : subd8_1 [1, 2, 1] = true := by decide +kernel
theorem subd8_1_499 : subd8_1 [1, 2, 2] = true := by decide +kernel
theorem subd8_1_500 : subd8_1 [1, 2, 3] = true := by decide +kernel
theorem subd8_1_501 : subd8_1 [1, 2, 4] = true := by decide +kernel
theorem subd8_1_502 : subd8_1 [1, 2, 5] = true := by decide +kernel
theorem subd8_1_503 : subd8_1 [1, 2, 6] = true := by decide +kernel
theorem subd8_1_504 : subd8_1 [1, 2, 7] = true := by decide +kernel
theorem subd8_1_505 : subd8_1 [1, 2, 8] = true := by decide +kernel
theorem subd8_1_506 : subd8_1 [1, 3, -7] = true := by decide +kernel
theorem subd8_1_507 : subd8_1 [1, 3, -6] = true := by decide +kernel
theorem subd8_1_508 : subd8_1 [1, 3, -5] = true := by decide +kernel
theorem subd8_1_509 : subd8_1 [1, 3, -4] = true := by decide +kernel
theorem subd8_1_510 : subd8_1 [1, 3, -3] = true := by decide +kernel
theorem subd8_1_511 : subd8_1 [1, 3, -2] = true := by decide +kernel
theorem sbd8_1_15 : ∀ q ∈ blkd8_1_15, subd8_1 q = true := by
  unfold blkd8_1_15
  exact List.forall_mem_cons.2 ⟨subd8_1_480, List.forall_mem_cons.2 ⟨subd8_1_481, List.forall_mem_cons.2 ⟨subd8_1_482, List.forall_mem_cons.2 ⟨subd8_1_483, List.forall_mem_cons.2 ⟨subd8_1_484, List.forall_mem_cons.2 ⟨subd8_1_485, List.forall_mem_cons.2 ⟨subd8_1_486, List.forall_mem_cons.2 ⟨subd8_1_487, List.forall_mem_cons.2 ⟨subd8_1_488, List.forall_mem_cons.2 ⟨subd8_1_489, List.forall_mem_cons.2 ⟨subd8_1_490, List.forall_mem_cons.2 ⟨subd8_1_491, List.forall_mem_cons.2 ⟨subd8_1_492, List.forall_mem_cons.2 ⟨subd8_1_493, List.forall_mem_cons.2 ⟨subd8_1_494, List.forall_mem_cons.2 ⟨subd8_1_495, List.forall_mem_cons.2 ⟨subd8_1_496, List.forall_mem_cons.2 ⟨subd8_1_497, List.forall_mem_cons.2 ⟨subd8_1_498, List.forall_mem_cons.2 ⟨subd8_1_499, List.forall_mem_cons.2 ⟨subd8_1_500, List.forall_mem_cons.2 ⟨subd8_1_501, List.forall_mem_cons.2 ⟨subd8_1_502, List.forall_mem_cons.2 ⟨subd8_1_503, List.forall_mem_cons.2 ⟨subd8_1_504, List.forall_mem_cons.2 ⟨subd8_1_505, List.forall_mem_cons.2 ⟨subd8_1_506, List.forall_mem_cons.2 ⟨subd8_1_507, List.forall_mem_cons.2 ⟨subd8_1_508, List.forall_mem_cons.2 ⟨subd8_1_509, List.forall_mem_cons.2 ⟨subd8_1_510, List.forall_mem_cons.2 ⟨subd8_1_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_512 : subd8_1 [1, 3, -1] = true := by decide +kernel
theorem subd8_1_513 : subd8_1 [1, 3, 0] = true := by decide +kernel
theorem subd8_1_514 : subd8_1 [1, 3, 1] = true := by decide +kernel
theorem subd8_1_515 : subd8_1 [1, 3, 2] = true := by decide +kernel
theorem subd8_1_516 : subd8_1 [1, 3, 3] = true := by decide +kernel
theorem subd8_1_517 : subd8_1 [1, 3, 4] = true := by decide +kernel
theorem subd8_1_518 : subd8_1 [1, 3, 5] = true := by decide +kernel
theorem subd8_1_519 : subd8_1 [1, 3, 6] = true := by decide +kernel
theorem subd8_1_520 : subd8_1 [1, 3, 7] = true := by decide +kernel
theorem subd8_1_521 : subd8_1 [1, 4] = true := by decide +kernel
theorem subd8_1_522 : subd8_1 [1, 5] = true := by decide +kernel
theorem subd8_1_523 : subd8_1 [1, 6] = true := by decide +kernel
theorem subd8_1_524 : subd8_1 [2, -6] = true := by decide +kernel
theorem subd8_1_525 : subd8_1 [2, -5] = true := by decide +kernel
theorem subd8_1_526 : subd8_1 [2, -4] = true := by decide +kernel
theorem subd8_1_527 : subd8_1 [2, -3] = true := by decide +kernel
theorem subd8_1_528 : subd8_1 [2, -2, -9] = true := by decide +kernel
theorem subd8_1_529 : subd8_1 [2, -2, -8] = true := by decide +kernel
theorem subd8_1_530 : subd8_1 [2, -2, -7] = true := by decide +kernel
theorem subd8_1_531 : subd8_1 [2, -2, -6] = true := by decide +kernel
theorem subd8_1_532 : subd8_1 [2, -2, -5] = true := by decide +kernel
theorem subd8_1_533 : subd8_1 [2, -2, -4] = true := by decide +kernel
theorem subd8_1_534 : subd8_1 [2, -2, -3] = true := by decide +kernel
theorem subd8_1_535 : subd8_1 [2, -2, -2] = true := by decide +kernel
theorem subd8_1_536 : subd8_1 [2, -2, -1] = true := by decide +kernel
theorem subd8_1_537 : subd8_1 [2, -2, 0] = true := by decide +kernel
theorem subd8_1_538 : subd8_1 [2, -2, 1] = true := by decide +kernel
theorem subd8_1_539 : subd8_1 [2, -2, 2] = true := by decide +kernel
theorem subd8_1_540 : subd8_1 [2, -2, 3] = true := by decide +kernel
theorem subd8_1_541 : subd8_1 [2, -2, 4] = true := by decide +kernel
theorem subd8_1_542 : subd8_1 [2, -2, 5] = true := by decide +kernel
theorem subd8_1_543 : subd8_1 [2, -1, -9] = true := by decide +kernel
theorem sbd8_1_16 : ∀ q ∈ blkd8_1_16, subd8_1 q = true := by
  unfold blkd8_1_16
  exact List.forall_mem_cons.2 ⟨subd8_1_512, List.forall_mem_cons.2 ⟨subd8_1_513, List.forall_mem_cons.2 ⟨subd8_1_514, List.forall_mem_cons.2 ⟨subd8_1_515, List.forall_mem_cons.2 ⟨subd8_1_516, List.forall_mem_cons.2 ⟨subd8_1_517, List.forall_mem_cons.2 ⟨subd8_1_518, List.forall_mem_cons.2 ⟨subd8_1_519, List.forall_mem_cons.2 ⟨subd8_1_520, List.forall_mem_cons.2 ⟨subd8_1_521, List.forall_mem_cons.2 ⟨subd8_1_522, List.forall_mem_cons.2 ⟨subd8_1_523, List.forall_mem_cons.2 ⟨subd8_1_524, List.forall_mem_cons.2 ⟨subd8_1_525, List.forall_mem_cons.2 ⟨subd8_1_526, List.forall_mem_cons.2 ⟨subd8_1_527, List.forall_mem_cons.2 ⟨subd8_1_528, List.forall_mem_cons.2 ⟨subd8_1_529, List.forall_mem_cons.2 ⟨subd8_1_530, List.forall_mem_cons.2 ⟨subd8_1_531, List.forall_mem_cons.2 ⟨subd8_1_532, List.forall_mem_cons.2 ⟨subd8_1_533, List.forall_mem_cons.2 ⟨subd8_1_534, List.forall_mem_cons.2 ⟨subd8_1_535, List.forall_mem_cons.2 ⟨subd8_1_536, List.forall_mem_cons.2 ⟨subd8_1_537, List.forall_mem_cons.2 ⟨subd8_1_538, List.forall_mem_cons.2 ⟨subd8_1_539, List.forall_mem_cons.2 ⟨subd8_1_540, List.forall_mem_cons.2 ⟨subd8_1_541, List.forall_mem_cons.2 ⟨subd8_1_542, List.forall_mem_cons.2 ⟨subd8_1_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_544 : subd8_1 [2, -1, -8] = true := by decide +kernel
theorem subd8_1_545 : subd8_1 [2, -1, -7] = true := by decide +kernel
theorem subd8_1_546 : subd8_1 [2, -1, -6] = true := by decide +kernel
theorem subd8_1_547 : subd8_1 [2, -1, -5] = true := by decide +kernel
theorem subd8_1_548 : subd8_1 [2, -1, -4] = true := by decide +kernel
theorem subd8_1_549 : subd8_1 [2, -1, -3] = true := by decide +kernel
theorem subd8_1_550 : subd8_1 [2, -1, -2] = true := by decide +kernel
theorem subd8_1_551 : subd8_1 [2, -1, -1] = true := by decide +kernel
theorem subd8_1_552 : subd8_1 [2, -1, 0] = true := by decide +kernel
theorem subd8_1_553 : subd8_1 [2, -1, 1] = true := by decide +kernel
theorem subd8_1_554 : subd8_1 [2, -1, 2] = true := by decide +kernel
theorem subd8_1_555 : subd8_1 [2, -1, 3] = true := by decide +kernel
theorem subd8_1_556 : subd8_1 [2, -1, 4] = true := by decide +kernel
theorem subd8_1_557 : subd8_1 [2, -1, 5] = true := by decide +kernel
theorem subd8_1_558 : subd8_1 [2, -1, 6] = true := by decide +kernel
theorem subd8_1_559 : subd8_1 [2, 0, -9] = true := by decide +kernel
theorem subd8_1_560 : subd8_1 [2, 0, -8] = true := by decide +kernel
theorem subd8_1_561 : subd8_1 [2, 0, -7] = true := by decide +kernel
theorem subd8_1_562 : subd8_1 [2, 0, -6] = true := by decide +kernel
theorem subd8_1_563 : subd8_1 [2, 0, -5] = true := by decide +kernel
theorem subd8_1_564 : subd8_1 [2, 0, -4] = true := by decide +kernel
theorem subd8_1_565 : subd8_1 [2, 0, -3] = true := by decide +kernel
theorem subd8_1_566 : subd8_1 [2, 0, -2] = true := by decide +kernel
theorem subd8_1_567 : subd8_1 [2, 0, -1] = true := by decide +kernel
theorem subd8_1_568 : subd8_1 [2, 0, 0] = true := by decide +kernel
theorem subd8_1_569 : subd8_1 [2, 0, 1] = true := by decide +kernel
theorem subd8_1_570 : subd8_1 [2, 0, 2] = true := by decide +kernel
theorem subd8_1_571 : subd8_1 [2, 0, 3] = true := by decide +kernel
theorem subd8_1_572 : subd8_1 [2, 0, 4] = true := by decide +kernel
theorem subd8_1_573 : subd8_1 [2, 0, 5] = true := by decide +kernel
theorem subd8_1_574 : subd8_1 [2, 0, 6] = true := by decide +kernel
theorem subd8_1_575 : subd8_1 [2, 1, -9] = true := by decide +kernel
theorem sbd8_1_17 : ∀ q ∈ blkd8_1_17, subd8_1 q = true := by
  unfold blkd8_1_17
  exact List.forall_mem_cons.2 ⟨subd8_1_544, List.forall_mem_cons.2 ⟨subd8_1_545, List.forall_mem_cons.2 ⟨subd8_1_546, List.forall_mem_cons.2 ⟨subd8_1_547, List.forall_mem_cons.2 ⟨subd8_1_548, List.forall_mem_cons.2 ⟨subd8_1_549, List.forall_mem_cons.2 ⟨subd8_1_550, List.forall_mem_cons.2 ⟨subd8_1_551, List.forall_mem_cons.2 ⟨subd8_1_552, List.forall_mem_cons.2 ⟨subd8_1_553, List.forall_mem_cons.2 ⟨subd8_1_554, List.forall_mem_cons.2 ⟨subd8_1_555, List.forall_mem_cons.2 ⟨subd8_1_556, List.forall_mem_cons.2 ⟨subd8_1_557, List.forall_mem_cons.2 ⟨subd8_1_558, List.forall_mem_cons.2 ⟨subd8_1_559, List.forall_mem_cons.2 ⟨subd8_1_560, List.forall_mem_cons.2 ⟨subd8_1_561, List.forall_mem_cons.2 ⟨subd8_1_562, List.forall_mem_cons.2 ⟨subd8_1_563, List.forall_mem_cons.2 ⟨subd8_1_564, List.forall_mem_cons.2 ⟨subd8_1_565, List.forall_mem_cons.2 ⟨subd8_1_566, List.forall_mem_cons.2 ⟨subd8_1_567, List.forall_mem_cons.2 ⟨subd8_1_568, List.forall_mem_cons.2 ⟨subd8_1_569, List.forall_mem_cons.2 ⟨subd8_1_570, List.forall_mem_cons.2 ⟨subd8_1_571, List.forall_mem_cons.2 ⟨subd8_1_572, List.forall_mem_cons.2 ⟨subd8_1_573, List.forall_mem_cons.2 ⟨subd8_1_574, List.forall_mem_cons.2 ⟨subd8_1_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_576 : subd8_1 [2, 1, -8] = true := by decide +kernel
theorem subd8_1_577 : subd8_1 [2, 1, -7] = true := by decide +kernel
theorem subd8_1_578 : subd8_1 [2, 1, -6] = true := by decide +kernel
theorem subd8_1_579 : subd8_1 [2, 1, -5] = true := by decide +kernel
theorem subd8_1_580 : subd8_1 [2, 1, -4] = true := by decide +kernel
theorem subd8_1_581 : subd8_1 [2, 1, -3] = true := by decide +kernel
theorem subd8_1_582 : subd8_1 [2, 1, -2] = true := by decide +kernel
theorem subd8_1_583 : subd8_1 [2, 1, -1] = true := by decide +kernel
theorem subd8_1_584 : subd8_1 [2, 1, 0] = true := by decide +kernel
theorem subd8_1_585 : subd8_1 [2, 1, 1] = true := by decide +kernel
theorem subd8_1_586 : subd8_1 [2, 1, 2] = true := by decide +kernel
theorem subd8_1_587 : subd8_1 [2, 1, 3] = true := by decide +kernel
theorem subd8_1_588 : subd8_1 [2, 1, 4] = true := by decide +kernel
theorem subd8_1_589 : subd8_1 [2, 1, 5] = true := by decide +kernel
theorem subd8_1_590 : subd8_1 [2, 1, 6] = true := by decide +kernel
theorem subd8_1_591 : subd8_1 [2, 1, 7] = true := by decide +kernel
theorem subd8_1_592 : subd8_1 [2, 2, -8] = true := by decide +kernel
theorem subd8_1_593 : subd8_1 [2, 2, -7] = true := by decide +kernel
theorem subd8_1_594 : subd8_1 [2, 2, -6] = true := by decide +kernel
theorem subd8_1_595 : subd8_1 [2, 2, -5] = true := by decide +kernel
theorem subd8_1_596 : subd8_1 [2, 2, -4] = true := by decide +kernel
theorem subd8_1_597 : subd8_1 [2, 2, -3] = true := by decide +kernel
theorem subd8_1_598 : subd8_1 [2, 2, -2] = true := by decide +kernel
theorem subd8_1_599 : subd8_1 [2, 2, -1] = true := by decide +kernel
theorem subd8_1_600 : subd8_1 [2, 2, 0] = true := by decide +kernel
theorem subd8_1_601 : subd8_1 [2, 2, 1] = true := by decide +kernel
theorem subd8_1_602 : subd8_1 [2, 2, 2] = true := by decide +kernel
theorem subd8_1_603 : subd8_1 [2, 2, 3] = true := by decide +kernel
theorem subd8_1_604 : subd8_1 [2, 2, 4] = true := by decide +kernel
theorem subd8_1_605 : subd8_1 [2, 2, 5] = true := by decide +kernel
theorem subd8_1_606 : subd8_1 [2, 2, 6] = true := by decide +kernel
theorem subd8_1_607 : subd8_1 [2, 2, 7] = true := by decide +kernel
theorem sbd8_1_18 : ∀ q ∈ blkd8_1_18, subd8_1 q = true := by
  unfold blkd8_1_18
  exact List.forall_mem_cons.2 ⟨subd8_1_576, List.forall_mem_cons.2 ⟨subd8_1_577, List.forall_mem_cons.2 ⟨subd8_1_578, List.forall_mem_cons.2 ⟨subd8_1_579, List.forall_mem_cons.2 ⟨subd8_1_580, List.forall_mem_cons.2 ⟨subd8_1_581, List.forall_mem_cons.2 ⟨subd8_1_582, List.forall_mem_cons.2 ⟨subd8_1_583, List.forall_mem_cons.2 ⟨subd8_1_584, List.forall_mem_cons.2 ⟨subd8_1_585, List.forall_mem_cons.2 ⟨subd8_1_586, List.forall_mem_cons.2 ⟨subd8_1_587, List.forall_mem_cons.2 ⟨subd8_1_588, List.forall_mem_cons.2 ⟨subd8_1_589, List.forall_mem_cons.2 ⟨subd8_1_590, List.forall_mem_cons.2 ⟨subd8_1_591, List.forall_mem_cons.2 ⟨subd8_1_592, List.forall_mem_cons.2 ⟨subd8_1_593, List.forall_mem_cons.2 ⟨subd8_1_594, List.forall_mem_cons.2 ⟨subd8_1_595, List.forall_mem_cons.2 ⟨subd8_1_596, List.forall_mem_cons.2 ⟨subd8_1_597, List.forall_mem_cons.2 ⟨subd8_1_598, List.forall_mem_cons.2 ⟨subd8_1_599, List.forall_mem_cons.2 ⟨subd8_1_600, List.forall_mem_cons.2 ⟨subd8_1_601, List.forall_mem_cons.2 ⟨subd8_1_602, List.forall_mem_cons.2 ⟨subd8_1_603, List.forall_mem_cons.2 ⟨subd8_1_604, List.forall_mem_cons.2 ⟨subd8_1_605, List.forall_mem_cons.2 ⟨subd8_1_606, List.forall_mem_cons.2 ⟨subd8_1_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_608 : subd8_1 [2, 3, -7] = true := by decide +kernel
theorem subd8_1_609 : subd8_1 [2, 3, -6] = true := by decide +kernel
theorem subd8_1_610 : subd8_1 [2, 3, -5] = true := by decide +kernel
theorem subd8_1_611 : subd8_1 [2, 3, -4] = true := by decide +kernel
theorem subd8_1_612 : subd8_1 [2, 3, -3] = true := by decide +kernel
theorem subd8_1_613 : subd8_1 [2, 3, -2] = true := by decide +kernel
theorem subd8_1_614 : subd8_1 [2, 3, -1] = true := by decide +kernel
theorem subd8_1_615 : subd8_1 [2, 3, 0] = true := by decide +kernel
theorem subd8_1_616 : subd8_1 [2, 3, 1] = true := by decide +kernel
theorem subd8_1_617 : subd8_1 [2, 3, 2] = true := by decide +kernel
theorem subd8_1_618 : subd8_1 [2, 3, 3] = true := by decide +kernel
theorem subd8_1_619 : subd8_1 [2, 3, 4] = true := by decide +kernel
theorem subd8_1_620 : subd8_1 [2, 3, 5] = true := by decide +kernel
theorem subd8_1_621 : subd8_1 [2, 3, 6] = true := by decide +kernel
theorem subd8_1_622 : subd8_1 [2, 3, 7] = true := by decide +kernel
theorem subd8_1_623 : subd8_1 [2, 4] = true := by decide +kernel
theorem subd8_1_624 : subd8_1 [2, 5] = true := by decide +kernel
theorem subd8_1_625 : subd8_1 [2, 6] = true := by decide +kernel
theorem subd8_1_626 : subd8_1 [3, -5] = true := by decide +kernel
theorem subd8_1_627 : subd8_1 [3, -4] = true := by decide +kernel
theorem subd8_1_628 : subd8_1 [3, -3] = true := by decide +kernel
theorem subd8_1_629 : subd8_1 [3, -2] = true := by decide +kernel
theorem subd8_1_630 : subd8_1 [3, -1] = true := by decide +kernel
theorem subd8_1_631 : subd8_1 [3, 0, -9] = true := by decide +kernel
theorem subd8_1_632 : subd8_1 [3, 0, -8] = true := by decide +kernel
theorem subd8_1_633 : subd8_1 [3, 0, -7] = true := by decide +kernel
theorem subd8_1_634 : subd8_1 [3, 0, -6] = true := by decide +kernel
theorem subd8_1_635 : subd8_1 [3, 0, -5] = true := by decide +kernel
theorem subd8_1_636 : subd8_1 [3, 0, -4] = true := by decide +kernel
theorem subd8_1_637 : subd8_1 [3, 0, -3] = true := by decide +kernel
theorem subd8_1_638 : subd8_1 [3, 0, -2] = true := by decide +kernel
theorem subd8_1_639 : subd8_1 [3, 0, -1] = true := by decide +kernel
theorem sbd8_1_19 : ∀ q ∈ blkd8_1_19, subd8_1 q = true := by
  unfold blkd8_1_19
  exact List.forall_mem_cons.2 ⟨subd8_1_608, List.forall_mem_cons.2 ⟨subd8_1_609, List.forall_mem_cons.2 ⟨subd8_1_610, List.forall_mem_cons.2 ⟨subd8_1_611, List.forall_mem_cons.2 ⟨subd8_1_612, List.forall_mem_cons.2 ⟨subd8_1_613, List.forall_mem_cons.2 ⟨subd8_1_614, List.forall_mem_cons.2 ⟨subd8_1_615, List.forall_mem_cons.2 ⟨subd8_1_616, List.forall_mem_cons.2 ⟨subd8_1_617, List.forall_mem_cons.2 ⟨subd8_1_618, List.forall_mem_cons.2 ⟨subd8_1_619, List.forall_mem_cons.2 ⟨subd8_1_620, List.forall_mem_cons.2 ⟨subd8_1_621, List.forall_mem_cons.2 ⟨subd8_1_622, List.forall_mem_cons.2 ⟨subd8_1_623, List.forall_mem_cons.2 ⟨subd8_1_624, List.forall_mem_cons.2 ⟨subd8_1_625, List.forall_mem_cons.2 ⟨subd8_1_626, List.forall_mem_cons.2 ⟨subd8_1_627, List.forall_mem_cons.2 ⟨subd8_1_628, List.forall_mem_cons.2 ⟨subd8_1_629, List.forall_mem_cons.2 ⟨subd8_1_630, List.forall_mem_cons.2 ⟨subd8_1_631, List.forall_mem_cons.2 ⟨subd8_1_632, List.forall_mem_cons.2 ⟨subd8_1_633, List.forall_mem_cons.2 ⟨subd8_1_634, List.forall_mem_cons.2 ⟨subd8_1_635, List.forall_mem_cons.2 ⟨subd8_1_636, List.forall_mem_cons.2 ⟨subd8_1_637, List.forall_mem_cons.2 ⟨subd8_1_638, List.forall_mem_cons.2 ⟨subd8_1_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C135
