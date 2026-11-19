import ReflectZphi.Data.Cert5.C101.Base

namespace ReflectZphi.Data.Cert5.C101

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd13_1_160 : subd13_1 [0, 0, 0] = true := by decide +kernel
theorem subd13_1_161 : subd13_1 [0, 0, 1] = true := by decide +kernel
theorem subd13_1_162 : subd13_1 [0, 0, 2] = true := by decide +kernel
theorem subd13_1_163 : subd13_1 [0, 0, 3] = true := by decide +kernel
theorem subd13_1_164 : subd13_1 [0, 0, 4] = true := by decide +kernel
theorem subd13_1_165 : subd13_1 [0, 0, 5] = true := by decide +kernel
theorem subd13_1_166 : subd13_1 [0, 0, 6] = true := by decide +kernel
theorem subd13_1_167 : subd13_1 [0, 0, 7] = true := by decide +kernel
theorem subd13_1_168 : subd13_1 [0, 0, 8] = true := by decide +kernel
theorem subd13_1_169 : subd13_1 [0, 0, 9] = true := by decide +kernel
theorem subd13_1_170 : subd13_1 [0, 0, 10] = true := by decide +kernel
theorem subd13_1_171 : subd13_1 [0, 0, 11] = true := by decide +kernel
theorem subd13_1_172 : subd13_1 [0, 0, 12] = true := by decide +kernel
theorem subd13_1_173 : subd13_1 [0, 0, 13] = true := by decide +kernel
theorem subd13_1_174 : subd13_1 [0, 0, 14] = true := by decide +kernel
theorem subd13_1_175 : subd13_1 [0, 0, 15] = true := by decide +kernel
theorem subd13_1_176 : subd13_1 [0, 0, 16] = true := by decide +kernel
theorem subd13_1_177 : subd13_1 [0, 0, 17] = true := by decide +kernel
theorem subd13_1_178 : subd13_1 [0, 0, 18] = true := by decide +kernel
theorem subd13_1_179 : subd13_1 [0, 0, 19] = true := by decide +kernel
theorem subd13_1_180 : subd13_1 [0, 0, 20] = true := by decide +kernel
theorem subd13_1_181 : subd13_1 [0, 0, 21] = true := by decide +kernel
theorem subd13_1_182 : subd13_1 [0, 0, 22] = true := by decide +kernel
theorem subd13_1_183 : subd13_1 [0, 0, 23] = true := by decide +kernel
theorem subd13_1_184 : subd13_1 [0, 1, -19] = true := by decide +kernel
theorem subd13_1_185 : subd13_1 [0, 1, -18] = true := by decide +kernel
theorem subd13_1_186 : subd13_1 [0, 1, -17] = true := by decide +kernel
theorem subd13_1_187 : subd13_1 [0, 1, -16] = true := by decide +kernel
theorem subd13_1_188 : subd13_1 [0, 1, -15] = true := by decide +kernel
theorem subd13_1_189 : subd13_1 [0, 1, -14] = true := by decide +kernel
theorem subd13_1_190 : subd13_1 [0, 1, -13] = true := by decide +kernel
theorem subd13_1_191 : subd13_1 [0, 1, -12] = true := by decide +kernel
theorem sbd13_1_5 : ∀ q ∈ blkd13_1_5, subd13_1 q = true := by
  unfold blkd13_1_5
  exact List.forall_mem_cons.2 ⟨subd13_1_160, List.forall_mem_cons.2 ⟨subd13_1_161, List.forall_mem_cons.2 ⟨subd13_1_162, List.forall_mem_cons.2 ⟨subd13_1_163, List.forall_mem_cons.2 ⟨subd13_1_164, List.forall_mem_cons.2 ⟨subd13_1_165, List.forall_mem_cons.2 ⟨subd13_1_166, List.forall_mem_cons.2 ⟨subd13_1_167, List.forall_mem_cons.2 ⟨subd13_1_168, List.forall_mem_cons.2 ⟨subd13_1_169, List.forall_mem_cons.2 ⟨subd13_1_170, List.forall_mem_cons.2 ⟨subd13_1_171, List.forall_mem_cons.2 ⟨subd13_1_172, List.forall_mem_cons.2 ⟨subd13_1_173, List.forall_mem_cons.2 ⟨subd13_1_174, List.forall_mem_cons.2 ⟨subd13_1_175, List.forall_mem_cons.2 ⟨subd13_1_176, List.forall_mem_cons.2 ⟨subd13_1_177, List.forall_mem_cons.2 ⟨subd13_1_178, List.forall_mem_cons.2 ⟨subd13_1_179, List.forall_mem_cons.2 ⟨subd13_1_180, List.forall_mem_cons.2 ⟨subd13_1_181, List.forall_mem_cons.2 ⟨subd13_1_182, List.forall_mem_cons.2 ⟨subd13_1_183, List.forall_mem_cons.2 ⟨subd13_1_184, List.forall_mem_cons.2 ⟨subd13_1_185, List.forall_mem_cons.2 ⟨subd13_1_186, List.forall_mem_cons.2 ⟨subd13_1_187, List.forall_mem_cons.2 ⟨subd13_1_188, List.forall_mem_cons.2 ⟨subd13_1_189, List.forall_mem_cons.2 ⟨subd13_1_190, List.forall_mem_cons.2 ⟨subd13_1_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_1_192 : subd13_1 [0, 1, -11] = true := by decide +kernel
theorem subd13_1_193 : subd13_1 [0, 1, -10] = true := by decide +kernel
theorem subd13_1_194 : subd13_1 [0, 1, -9] = true := by decide +kernel
theorem subd13_1_195 : subd13_1 [0, 1, -8] = true := by decide +kernel
theorem subd13_1_196 : subd13_1 [0, 1, -7] = true := by decide +kernel
theorem subd13_1_197 : subd13_1 [0, 1, -6] = true := by decide +kernel
theorem subd13_1_198 : subd13_1 [0, 1, -5] = true := by decide +kernel
theorem subd13_1_199 : subd13_1 [0, 1, -4] = true := by decide +kernel
theorem subd13_1_200 : subd13_1 [0, 1, -3] = true := by decide +kernel
theorem subd13_1_201 : subd13_1 [0, 1, -2] = true := by decide +kernel
theorem subd13_1_202 : subd13_1 [0, 1, -1] = true := by decide +kernel
theorem subd13_1_203 : subd13_1 [0, 1, 0] = true := by decide +kernel
theorem subd13_1_204 : subd13_1 [0, 1, 1] = true := by decide +kernel
theorem subd13_1_205 : subd13_1 [0, 1, 2] = true := by decide +kernel
theorem subd13_1_206 : subd13_1 [0, 1, 3] = true := by decide +kernel
theorem subd13_1_207 : subd13_1 [0, 1, 4] = true := by decide +kernel
theorem subd13_1_208 : subd13_1 [0, 1, 5] = true := by decide +kernel
theorem subd13_1_209 : subd13_1 [0, 1, 6] = true := by decide +kernel
theorem subd13_1_210 : subd13_1 [0, 1, 7] = true := by decide +kernel
theorem subd13_1_211 : subd13_1 [0, 1, 8] = true := by decide +kernel
theorem subd13_1_212 : subd13_1 [0, 1, 9] = true := by decide +kernel
theorem subd13_1_213 : subd13_1 [0, 1, 10] = true := by decide +kernel
theorem subd13_1_214 : subd13_1 [0, 1, 11] = true := by decide +kernel
theorem subd13_1_215 : subd13_1 [0, 1, 12] = true := by decide +kernel
theorem subd13_1_216 : subd13_1 [0, 1, 13] = true := by decide +kernel
theorem subd13_1_217 : subd13_1 [0, 1, 14] = true := by decide +kernel
theorem subd13_1_218 : subd13_1 [0, 1, 15] = true := by decide +kernel
theorem subd13_1_219 : subd13_1 [0, 1, 16] = true := by decide +kernel
theorem subd13_1_220 : subd13_1 [0, 1, 17] = true := by decide +kernel
theorem subd13_1_221 : subd13_1 [0, 1, 18] = true := by decide +kernel
theorem subd13_1_222 : subd13_1 [0, 1, 19] = true := by decide +kernel
theorem subd13_1_223 : subd13_1 [1, -2] = true := by decide +kernel
theorem sbd13_1_6 : ∀ q ∈ blkd13_1_6, subd13_1 q = true := by
  unfold blkd13_1_6
  exact List.forall_mem_cons.2 ⟨subd13_1_192, List.forall_mem_cons.2 ⟨subd13_1_193, List.forall_mem_cons.2 ⟨subd13_1_194, List.forall_mem_cons.2 ⟨subd13_1_195, List.forall_mem_cons.2 ⟨subd13_1_196, List.forall_mem_cons.2 ⟨subd13_1_197, List.forall_mem_cons.2 ⟨subd13_1_198, List.forall_mem_cons.2 ⟨subd13_1_199, List.forall_mem_cons.2 ⟨subd13_1_200, List.forall_mem_cons.2 ⟨subd13_1_201, List.forall_mem_cons.2 ⟨subd13_1_202, List.forall_mem_cons.2 ⟨subd13_1_203, List.forall_mem_cons.2 ⟨subd13_1_204, List.forall_mem_cons.2 ⟨subd13_1_205, List.forall_mem_cons.2 ⟨subd13_1_206, List.forall_mem_cons.2 ⟨subd13_1_207, List.forall_mem_cons.2 ⟨subd13_1_208, List.forall_mem_cons.2 ⟨subd13_1_209, List.forall_mem_cons.2 ⟨subd13_1_210, List.forall_mem_cons.2 ⟨subd13_1_211, List.forall_mem_cons.2 ⟨subd13_1_212, List.forall_mem_cons.2 ⟨subd13_1_213, List.forall_mem_cons.2 ⟨subd13_1_214, List.forall_mem_cons.2 ⟨subd13_1_215, List.forall_mem_cons.2 ⟨subd13_1_216, List.forall_mem_cons.2 ⟨subd13_1_217, List.forall_mem_cons.2 ⟨subd13_1_218, List.forall_mem_cons.2 ⟨subd13_1_219, List.forall_mem_cons.2 ⟨subd13_1_220, List.forall_mem_cons.2 ⟨subd13_1_221, List.forall_mem_cons.2 ⟨subd13_1_222, List.forall_mem_cons.2 ⟨subd13_1_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_1_224 : subd13_1 [1, -1, -13] = true := by decide +kernel
theorem subd13_1_225 : subd13_1 [1, -1, -12] = true := by decide +kernel
theorem subd13_1_226 : subd13_1 [1, -1, -11] = true := by decide +kernel
theorem subd13_1_227 : subd13_1 [1, -1, -10] = true := by decide +kernel
theorem subd13_1_228 : subd13_1 [1, -1, -9] = true := by decide +kernel
theorem subd13_1_229 : subd13_1 [1, -1, -8] = true := by decide +kernel
theorem subd13_1_230 : subd13_1 [1, -1, -7] = true := by decide +kernel
theorem subd13_1_231 : subd13_1 [1, -1, -6] = true := by decide +kernel
theorem subd13_1_232 : subd13_1 [1, -1, -5] = true := by decide +kernel
theorem subd13_1_233 : subd13_1 [1, -1, -4] = true := by decide +kernel
theorem subd13_1_234 : subd13_1 [1, -1, -3] = true := by decide +kernel
theorem subd13_1_235 : subd13_1 [1, -1, -2] = true := by decide +kernel
theorem subd13_1_236 : subd13_1 [1, -1, -1] = true := by decide +kernel
theorem subd13_1_237 : subd13_1 [1, -1, 0] = true := by decide +kernel
theorem subd13_1_238 : subd13_1 [1, -1, 1] = true := by decide +kernel
theorem subd13_1_239 : subd13_1 [1, -1, 2] = true := by decide +kernel
theorem subd13_1_240 : subd13_1 [1, -1, 3] = true := by decide +kernel
theorem subd13_1_241 : subd13_1 [1, -1, 4] = true := by decide +kernel
theorem subd13_1_242 : subd13_1 [1, -1, 5] = true := by decide +kernel
theorem subd13_1_243 : subd13_1 [1, -1, 6] = true := by decide +kernel
theorem subd13_1_244 : subd13_1 [1, -1, 7] = true := by decide +kernel
theorem subd13_1_245 : subd13_1 [1, -1, 8] = true := by decide +kernel
theorem subd13_1_246 : subd13_1 [1, -1, 9] = true := by decide +kernel
theorem subd13_1_247 : subd13_1 [1, -1, 10] = true := by decide +kernel
theorem subd13_1_248 : subd13_1 [1, -1, 11] = true := by decide +kernel
theorem subd13_1_249 : subd13_1 [1, -1, 12] = true := by decide +kernel
theorem subd13_1_250 : subd13_1 [1, -1, 13] = true := by decide +kernel
theorem subd13_1_251 : subd13_1 [1, 0, -19] = true := by decide +kernel
theorem subd13_1_252 : subd13_1 [1, 0, -18] = true := by decide +kernel
theorem subd13_1_253 : subd13_1 [1, 0, -17] = true := by decide +kernel
theorem subd13_1_254 : subd13_1 [1, 0, -16] = true := by decide +kernel
theorem subd13_1_255 : subd13_1 [1, 0, -15] = true := by decide +kernel
theorem sbd13_1_7 : ∀ q ∈ blkd13_1_7, subd13_1 q = true := by
  unfold blkd13_1_7
  exact List.forall_mem_cons.2 ⟨subd13_1_224, List.forall_mem_cons.2 ⟨subd13_1_225, List.forall_mem_cons.2 ⟨subd13_1_226, List.forall_mem_cons.2 ⟨subd13_1_227, List.forall_mem_cons.2 ⟨subd13_1_228, List.forall_mem_cons.2 ⟨subd13_1_229, List.forall_mem_cons.2 ⟨subd13_1_230, List.forall_mem_cons.2 ⟨subd13_1_231, List.forall_mem_cons.2 ⟨subd13_1_232, List.forall_mem_cons.2 ⟨subd13_1_233, List.forall_mem_cons.2 ⟨subd13_1_234, List.forall_mem_cons.2 ⟨subd13_1_235, List.forall_mem_cons.2 ⟨subd13_1_236, List.forall_mem_cons.2 ⟨subd13_1_237, List.forall_mem_cons.2 ⟨subd13_1_238, List.forall_mem_cons.2 ⟨subd13_1_239, List.forall_mem_cons.2 ⟨subd13_1_240, List.forall_mem_cons.2 ⟨subd13_1_241, List.forall_mem_cons.2 ⟨subd13_1_242, List.forall_mem_cons.2 ⟨subd13_1_243, List.forall_mem_cons.2 ⟨subd13_1_244, List.forall_mem_cons.2 ⟨subd13_1_245, List.forall_mem_cons.2 ⟨subd13_1_246, List.forall_mem_cons.2 ⟨subd13_1_247, List.forall_mem_cons.2 ⟨subd13_1_248, List.forall_mem_cons.2 ⟨subd13_1_249, List.forall_mem_cons.2 ⟨subd13_1_250, List.forall_mem_cons.2 ⟨subd13_1_251, List.forall_mem_cons.2 ⟨subd13_1_252, List.forall_mem_cons.2 ⟨subd13_1_253, List.forall_mem_cons.2 ⟨subd13_1_254, List.forall_mem_cons.2 ⟨subd13_1_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_1_256 : subd13_1 [1, 0, -14] = true := by decide +kernel
theorem subd13_1_257 : subd13_1 [1, 0, -13] = true := by decide +kernel
theorem subd13_1_258 : subd13_1 [1, 0, -12] = true := by decide +kernel
theorem subd13_1_259 : subd13_1 [1, 0, -11] = true := by decide +kernel
theorem subd13_1_260 : subd13_1 [1, 0, -10] = true := by decide +kernel
theorem subd13_1_261 : subd13_1 [1, 0, -9] = true := by decide +kernel
theorem subd13_1_262 : subd13_1 [1, 0, -8] = true := by decide +kernel
theorem subd13_1_263 : subd13_1 [1, 0, -7] = true := by decide +kernel
theorem subd13_1_264 : subd13_1 [1, 0, -6] = true := by decide +kernel
theorem subd13_1_265 : subd13_1 [1, 0, -5] = true := by decide +kernel
theorem subd13_1_266 : subd13_1 [1, 0, -4] = true := by decide +kernel
theorem subd13_1_267 : subd13_1 [1, 0, -3] = true := by decide +kernel
theorem subd13_1_268 : subd13_1 [1, 0, -2] = true := by decide +kernel
theorem subd13_1_269 : subd13_1 [1, 0, -1] = true := by decide +kernel
theorem subd13_1_270 : subd13_1 [1, 0, 0] = true := by decide +kernel
theorem subd13_1_271 : subd13_1 [1, 0, 1] = true := by decide +kernel
theorem subd13_1_272 : subd13_1 [1, 0, 2] = true := by decide +kernel
theorem subd13_1_273 : subd13_1 [1, 0, 3] = true := by decide +kernel
theorem subd13_1_274 : subd13_1 [1, 0, 4] = true := by decide +kernel
theorem subd13_1_275 : subd13_1 [1, 0, 5] = true := by decide +kernel
theorem subd13_1_276 : subd13_1 [1, 0, 6] = true := by decide +kernel
theorem subd13_1_277 : subd13_1 [1, 0, 7] = true := by decide +kernel
theorem subd13_1_278 : subd13_1 [1, 0, 8] = true := by decide +kernel
theorem subd13_1_279 : subd13_1 [1, 0, 9] = true := by decide +kernel
theorem subd13_1_280 : subd13_1 [1, 0, 10] = true := by decide +kernel
theorem subd13_1_281 : subd13_1 [1, 0, 11] = true := by decide +kernel
theorem subd13_1_282 : subd13_1 [1, 0, 12] = true := by decide +kernel
theorem subd13_1_283 : subd13_1 [1, 0, 13] = true := by decide +kernel
theorem subd13_1_284 : subd13_1 [1, 0, 14] = true := by decide +kernel
theorem subd13_1_285 : subd13_1 [1, 0, 15] = true := by decide +kernel
theorem subd13_1_286 : subd13_1 [1, 0, 16] = true := by decide +kernel
theorem subd13_1_287 : subd13_1 [1, 0, 17] = true := by decide +kernel
theorem sbd13_1_8 : ∀ q ∈ blkd13_1_8, subd13_1 q = true := by
  unfold blkd13_1_8
  exact List.forall_mem_cons.2 ⟨subd13_1_256, List.forall_mem_cons.2 ⟨subd13_1_257, List.forall_mem_cons.2 ⟨subd13_1_258, List.forall_mem_cons.2 ⟨subd13_1_259, List.forall_mem_cons.2 ⟨subd13_1_260, List.forall_mem_cons.2 ⟨subd13_1_261, List.forall_mem_cons.2 ⟨subd13_1_262, List.forall_mem_cons.2 ⟨subd13_1_263, List.forall_mem_cons.2 ⟨subd13_1_264, List.forall_mem_cons.2 ⟨subd13_1_265, List.forall_mem_cons.2 ⟨subd13_1_266, List.forall_mem_cons.2 ⟨subd13_1_267, List.forall_mem_cons.2 ⟨subd13_1_268, List.forall_mem_cons.2 ⟨subd13_1_269, List.forall_mem_cons.2 ⟨subd13_1_270, List.forall_mem_cons.2 ⟨subd13_1_271, List.forall_mem_cons.2 ⟨subd13_1_272, List.forall_mem_cons.2 ⟨subd13_1_273, List.forall_mem_cons.2 ⟨subd13_1_274, List.forall_mem_cons.2 ⟨subd13_1_275, List.forall_mem_cons.2 ⟨subd13_1_276, List.forall_mem_cons.2 ⟨subd13_1_277, List.forall_mem_cons.2 ⟨subd13_1_278, List.forall_mem_cons.2 ⟨subd13_1_279, List.forall_mem_cons.2 ⟨subd13_1_280, List.forall_mem_cons.2 ⟨subd13_1_281, List.forall_mem_cons.2 ⟨subd13_1_282, List.forall_mem_cons.2 ⟨subd13_1_283, List.forall_mem_cons.2 ⟨subd13_1_284, List.forall_mem_cons.2 ⟨subd13_1_285, List.forall_mem_cons.2 ⟨subd13_1_286, List.forall_mem_cons.2 ⟨subd13_1_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd13_1_288 : subd13_1 [1, 0, 18] = true := by decide +kernel
theorem subd13_1_289 : subd13_1 [1, 0, 19] = true := by decide +kernel
theorem subd13_1_290 : subd13_1 [1, 1, -14] = true := by decide +kernel
theorem subd13_1_291 : subd13_1 [1, 1, -13] = true := by decide +kernel
theorem subd13_1_292 : subd13_1 [1, 1, -12] = true := by decide +kernel
theorem subd13_1_293 : subd13_1 [1, 1, -11] = true := by decide +kernel
theorem subd13_1_294 : subd13_1 [1, 1, -10] = true := by decide +kernel
theorem subd13_1_295 : subd13_1 [1, 1, -9] = true := by decide +kernel
theorem subd13_1_296 : subd13_1 [1, 1, -8] = true := by decide +kernel
theorem subd13_1_297 : subd13_1 [1, 1, -7] = true := by decide +kernel
theorem subd13_1_298 : subd13_1 [1, 1, -6] = true := by decide +kernel
theorem subd13_1_299 : subd13_1 [1, 1, -5] = true := by decide +kernel
theorem subd13_1_300 : subd13_1 [1, 1, -4] = true := by decide +kernel
theorem subd13_1_301 : subd13_1 [1, 1, -3] = true := by decide +kernel
theorem subd13_1_302 : subd13_1 [1, 1, -2] = true := by decide +kernel
theorem subd13_1_303 : subd13_1 [1, 1, -1] = true := by decide +kernel
theorem subd13_1_304 : subd13_1 [1, 1, 0] = true := by decide +kernel
theorem subd13_1_305 : subd13_1 [1, 1, 1] = true := by decide +kernel
theorem subd13_1_306 : subd13_1 [1, 1, 2] = true := by decide +kernel
theorem subd13_1_307 : subd13_1 [1, 1, 3] = true := by decide +kernel
theorem subd13_1_308 : subd13_1 [1, 1, 4] = true := by decide +kernel
theorem subd13_1_309 : subd13_1 [1, 1, 5] = true := by decide +kernel
theorem subd13_1_310 : subd13_1 [1, 1, 6] = true := by decide +kernel
theorem subd13_1_311 : subd13_1 [1, 1, 7] = true := by decide +kernel
theorem subd13_1_312 : subd13_1 [1, 1, 8] = true := by decide +kernel
theorem subd13_1_313 : subd13_1 [1, 1, 9] = true := by decide +kernel
theorem subd13_1_314 : subd13_1 [1, 1, 10] = true := by decide +kernel
theorem subd13_1_315 : subd13_1 [1, 1, 11] = true := by decide +kernel
theorem subd13_1_316 : subd13_1 [1, 1, 12] = true := by decide +kernel
theorem subd13_1_317 : subd13_1 [1, 1, 13] = true := by decide +kernel
theorem subd13_1_318 : subd13_1 [1, 1, 14] = true := by decide +kernel
theorem sbd13_1_9 : ∀ q ∈ blkd13_1_9, subd13_1 q = true := by
  unfold blkd13_1_9
  exact List.forall_mem_cons.2 ⟨subd13_1_288, List.forall_mem_cons.2 ⟨subd13_1_289, List.forall_mem_cons.2 ⟨subd13_1_290, List.forall_mem_cons.2 ⟨subd13_1_291, List.forall_mem_cons.2 ⟨subd13_1_292, List.forall_mem_cons.2 ⟨subd13_1_293, List.forall_mem_cons.2 ⟨subd13_1_294, List.forall_mem_cons.2 ⟨subd13_1_295, List.forall_mem_cons.2 ⟨subd13_1_296, List.forall_mem_cons.2 ⟨subd13_1_297, List.forall_mem_cons.2 ⟨subd13_1_298, List.forall_mem_cons.2 ⟨subd13_1_299, List.forall_mem_cons.2 ⟨subd13_1_300, List.forall_mem_cons.2 ⟨subd13_1_301, List.forall_mem_cons.2 ⟨subd13_1_302, List.forall_mem_cons.2 ⟨subd13_1_303, List.forall_mem_cons.2 ⟨subd13_1_304, List.forall_mem_cons.2 ⟨subd13_1_305, List.forall_mem_cons.2 ⟨subd13_1_306, List.forall_mem_cons.2 ⟨subd13_1_307, List.forall_mem_cons.2 ⟨subd13_1_308, List.forall_mem_cons.2 ⟨subd13_1_309, List.forall_mem_cons.2 ⟨subd13_1_310, List.forall_mem_cons.2 ⟨subd13_1_311, List.forall_mem_cons.2 ⟨subd13_1_312, List.forall_mem_cons.2 ⟨subd13_1_313, List.forall_mem_cons.2 ⟨subd13_1_314, List.forall_mem_cons.2 ⟨subd13_1_315, List.forall_mem_cons.2 ⟨subd13_1_316, List.forall_mem_cons.2 ⟨subd13_1_317, List.forall_mem_cons.2 ⟨subd13_1_318, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd14_0 : ldCheck G d14_0.U d14_0.ms ldd14_0 = true := by decide +kernel
theorem pre_okd14_0 : subPre G cell14 d14_0 = true := by decide +kernel
theorem subd14_0_0 : subd14_0 [-5] = true := by decide +kernel
theorem subd14_0_1 : subd14_0 [-4, -4] = true := by decide +kernel
theorem subd14_0_2 : subd14_0 [-4, -3] = true := by decide +kernel
theorem subd14_0_3 : subd14_0 [-4, -2] = true := by decide +kernel
theorem subd14_0_4 : subd14_0 [-4, -1] = true := by decide +kernel
theorem subd14_0_5 : subd14_0 [-4, 0] = true := by decide +kernel
theorem subd14_0_6 : subd14_0 [-4, 1] = true := by decide +kernel
theorem subd14_0_7 : subd14_0 [-4, 2] = true := by decide +kernel
theorem subd14_0_8 : subd14_0 [-4, 3] = true := by decide +kernel
theorem subd14_0_9 : subd14_0 [-3, -5] = true := by decide +kernel
theorem subd14_0_10 : subd14_0 [-3, -4] = true := by decide +kernel
theorem subd14_0_11 : subd14_0 [-3, -3] = true := by decide +kernel
theorem subd14_0_12 : subd14_0 [-3, -2] = true := by decide +kernel
theorem subd14_0_13 : subd14_0 [-3, -1] = true := by decide +kernel
theorem subd14_0_14 : subd14_0 [-3, 0] = true := by decide +kernel
theorem subd14_0_15 : subd14_0 [-3, 1] = true := by decide +kernel
theorem subd14_0_16 : subd14_0 [-3, 2] = true := by decide +kernel
theorem subd14_0_17 : subd14_0 [-3, 3] = true := by decide +kernel
theorem subd14_0_18 : subd14_0 [-3, 4] = true := by decide +kernel
theorem subd14_0_19 : subd14_0 [-2, -5] = true := by decide +kernel
theorem subd14_0_20 : subd14_0 [-2, -4] = true := by decide +kernel
theorem subd14_0_21 : subd14_0 [-2, -3] = true := by decide +kernel
theorem subd14_0_22 : subd14_0 [-2, -2] = true := by decide +kernel
theorem subd14_0_23 : subd14_0 [-2, -1] = true := by decide +kernel
theorem subd14_0_24 : subd14_0 [-2, 0, -7] = true := by decide +kernel
theorem subd14_0_25 : subd14_0 [-2, 0, -6] = true := by decide +kernel
theorem subd14_0_26 : subd14_0 [-2, 0, -5] = true := by decide +kernel
theorem subd14_0_27 : subd14_0 [-2, 0, -4] = true := by decide +kernel
theorem subd14_0_28 : subd14_0 [-2, 0, -3] = true := by decide +kernel
theorem subd14_0_29 : subd14_0 [-2, 0, -2] = true := by decide +kernel
theorem subd14_0_30 : subd14_0 [-2, 0, -1] = true := by decide +kernel
theorem subd14_0_31 : subd14_0 [-2, 0, 0] = true := by decide +kernel
theorem sbd14_0_0 : ∀ q ∈ blkd14_0_0, subd14_0 q = true := by
  unfold blkd14_0_0
  exact List.forall_mem_cons.2 ⟨subd14_0_0, List.forall_mem_cons.2 ⟨subd14_0_1, List.forall_mem_cons.2 ⟨subd14_0_2, List.forall_mem_cons.2 ⟨subd14_0_3, List.forall_mem_cons.2 ⟨subd14_0_4, List.forall_mem_cons.2 ⟨subd14_0_5, List.forall_mem_cons.2 ⟨subd14_0_6, List.forall_mem_cons.2 ⟨subd14_0_7, List.forall_mem_cons.2 ⟨subd14_0_8, List.forall_mem_cons.2 ⟨subd14_0_9, List.forall_mem_cons.2 ⟨subd14_0_10, List.forall_mem_cons.2 ⟨subd14_0_11, List.forall_mem_cons.2 ⟨subd14_0_12, List.forall_mem_cons.2 ⟨subd14_0_13, List.forall_mem_cons.2 ⟨subd14_0_14, List.forall_mem_cons.2 ⟨subd14_0_15, List.forall_mem_cons.2 ⟨subd14_0_16, List.forall_mem_cons.2 ⟨subd14_0_17, List.forall_mem_cons.2 ⟨subd14_0_18, List.forall_mem_cons.2 ⟨subd14_0_19, List.forall_mem_cons.2 ⟨subd14_0_20, List.forall_mem_cons.2 ⟨subd14_0_21, List.forall_mem_cons.2 ⟨subd14_0_22, List.forall_mem_cons.2 ⟨subd14_0_23, List.forall_mem_cons.2 ⟨subd14_0_24, List.forall_mem_cons.2 ⟨subd14_0_25, List.forall_mem_cons.2 ⟨subd14_0_26, List.forall_mem_cons.2 ⟨subd14_0_27, List.forall_mem_cons.2 ⟨subd14_0_28, List.forall_mem_cons.2 ⟨subd14_0_29, List.forall_mem_cons.2 ⟨subd14_0_30, List.forall_mem_cons.2 ⟨subd14_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_0_32 : subd14_0 [-2, 0, 1] = true := by decide +kernel
theorem subd14_0_33 : subd14_0 [-2, 0, 2] = true := by decide +kernel
theorem subd14_0_34 : subd14_0 [-2, 0, 3] = true := by decide +kernel
theorem subd14_0_35 : subd14_0 [-2, 0, 4] = true := by decide +kernel
theorem subd14_0_36 : subd14_0 [-2, 0, 5] = true := by decide +kernel
theorem subd14_0_37 : subd14_0 [-2, 0, 6] = true := by decide +kernel
theorem subd14_0_38 : subd14_0 [-2, 1, -7] = true := by decide +kernel
theorem subd14_0_39 : subd14_0 [-2, 1, -6] = true := by decide +kernel
theorem subd14_0_40 : subd14_0 [-2, 1, -5] = true := by decide +kernel
theorem subd14_0_41 : subd14_0 [-2, 1, -4] = true := by decide +kernel
theorem subd14_0_42 : subd14_0 [-2, 1, -3] = true := by decide +kernel
theorem subd14_0_43 : subd14_0 [-2, 1, -2] = true := by decide +kernel
theorem subd14_0_44 : subd14_0 [-2, 1, -1] = true := by decide +kernel
theorem subd14_0_45 : subd14_0 [-2, 1, 0] = true := by decide +kernel
theorem subd14_0_46 : subd14_0 [-2, 1, 1] = true := by decide +kernel
theorem subd14_0_47 : subd14_0 [-2, 1, 2] = true := by decide +kernel
theorem subd14_0_48 : subd14_0 [-2, 1, 3] = true := by decide +kernel
theorem subd14_0_49 : subd14_0 [-2, 1, 4] = true := by decide +kernel
theorem subd14_0_50 : subd14_0 [-2, 1, 5] = true := by decide +kernel
theorem subd14_0_51 : subd14_0 [-2, 1, 6] = true := by decide +kernel
theorem subd14_0_52 : subd14_0 [-2, 2] = true := by decide +kernel
theorem subd14_0_53 : subd14_0 [-2, 3] = true := by decide +kernel
theorem subd14_0_54 : subd14_0 [-2, 4] = true := by decide +kernel
theorem subd14_0_55 : subd14_0 [-2, 5] = true := by decide +kernel
theorem subd14_0_56 : subd14_0 [-1, -6] = true := by decide +kernel
theorem subd14_0_57 : subd14_0 [-1, -5] = true := by decide +kernel
theorem subd14_0_58 : subd14_0 [-1, -4] = true := by decide +kernel
theorem subd14_0_59 : subd14_0 [-1, -3] = true := by decide +kernel
theorem subd14_0_60 : subd14_0 [-1, -2] = true := by decide +kernel
theorem subd14_0_61 : subd14_0 [-1, -1, -7] = true := by decide +kernel
theorem subd14_0_62 : subd14_0 [-1, -1, -6] = true := by decide +kernel
theorem subd14_0_63 : subd14_0 [-1, -1, -5] = true := by decide +kernel
theorem sbd14_0_1 : ∀ q ∈ blkd14_0_1, subd14_0 q = true := by
  unfold blkd14_0_1
  exact List.forall_mem_cons.2 ⟨subd14_0_32, List.forall_mem_cons.2 ⟨subd14_0_33, List.forall_mem_cons.2 ⟨subd14_0_34, List.forall_mem_cons.2 ⟨subd14_0_35, List.forall_mem_cons.2 ⟨subd14_0_36, List.forall_mem_cons.2 ⟨subd14_0_37, List.forall_mem_cons.2 ⟨subd14_0_38, List.forall_mem_cons.2 ⟨subd14_0_39, List.forall_mem_cons.2 ⟨subd14_0_40, List.forall_mem_cons.2 ⟨subd14_0_41, List.forall_mem_cons.2 ⟨subd14_0_42, List.forall_mem_cons.2 ⟨subd14_0_43, List.forall_mem_cons.2 ⟨subd14_0_44, List.forall_mem_cons.2 ⟨subd14_0_45, List.forall_mem_cons.2 ⟨subd14_0_46, List.forall_mem_cons.2 ⟨subd14_0_47, List.forall_mem_cons.2 ⟨subd14_0_48, List.forall_mem_cons.2 ⟨subd14_0_49, List.forall_mem_cons.2 ⟨subd14_0_50, List.forall_mem_cons.2 ⟨subd14_0_51, List.forall_mem_cons.2 ⟨subd14_0_52, List.forall_mem_cons.2 ⟨subd14_0_53, List.forall_mem_cons.2 ⟨subd14_0_54, List.forall_mem_cons.2 ⟨subd14_0_55, List.forall_mem_cons.2 ⟨subd14_0_56, List.forall_mem_cons.2 ⟨subd14_0_57, List.forall_mem_cons.2 ⟨subd14_0_58, List.forall_mem_cons.2 ⟨subd14_0_59, List.forall_mem_cons.2 ⟨subd14_0_60, List.forall_mem_cons.2 ⟨subd14_0_61, List.forall_mem_cons.2 ⟨subd14_0_62, List.forall_mem_cons.2 ⟨subd14_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C101
