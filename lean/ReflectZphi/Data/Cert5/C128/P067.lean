import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_4_160 : subd9_4 [-1, 2, -11] = true := by decide +kernel
theorem subd9_4_161 : subd9_4 [-1, 2, -10] = true := by decide +kernel
theorem subd9_4_162 : subd9_4 [-1, 2, -9] = true := by decide +kernel
theorem subd9_4_163 : subd9_4 [-1, 2, -8] = true := by decide +kernel
theorem subd9_4_164 : subd9_4 [-1, 2, -7] = true := by decide +kernel
theorem subd9_4_165 : subd9_4 [-1, 2, -6] = true := by decide +kernel
theorem subd9_4_166 : subd9_4 [-1, 2, -5] = true := by decide +kernel
theorem subd9_4_167 : subd9_4 [-1, 2, -4] = true := by decide +kernel
theorem subd9_4_168 : subd9_4 [-1, 2, -3] = true := by decide +kernel
theorem subd9_4_169 : subd9_4 [-1, 2, -2] = true := by decide +kernel
theorem subd9_4_170 : subd9_4 [-1, 2, -1] = true := by decide +kernel
theorem subd9_4_171 : subd9_4 [-1, 2, 0] = true := by decide +kernel
theorem subd9_4_172 : subd9_4 [-1, 2, 1] = true := by decide +kernel
theorem subd9_4_173 : subd9_4 [-1, 2, 2] = true := by decide +kernel
theorem subd9_4_174 : subd9_4 [-1, 2, 3] = true := by decide +kernel
theorem subd9_4_175 : subd9_4 [-1, 2, 4] = true := by decide +kernel
theorem subd9_4_176 : subd9_4 [-1, 2, 5] = true := by decide +kernel
theorem subd9_4_177 : subd9_4 [-1, 2, 6] = true := by decide +kernel
theorem subd9_4_178 : subd9_4 [-1, 2, 7] = true := by decide +kernel
theorem subd9_4_179 : subd9_4 [-1, 2, 8] = true := by decide +kernel
theorem subd9_4_180 : subd9_4 [-1, 2, 9] = true := by decide +kernel
theorem subd9_4_181 : subd9_4 [-1, 2, 10] = true := by decide +kernel
theorem subd9_4_182 : subd9_4 [-1, 2, 11] = true := by decide +kernel
theorem subd9_4_183 : subd9_4 [-1, 3, -7] = true := by decide +kernel
theorem subd9_4_184 : subd9_4 [-1, 3, -6] = true := by decide +kernel
theorem subd9_4_185 : subd9_4 [-1, 3, -5] = true := by decide +kernel
theorem subd9_4_186 : subd9_4 [-1, 3, -4] = true := by decide +kernel
theorem subd9_4_187 : subd9_4 [-1, 3, -3] = true := by decide +kernel
theorem subd9_4_188 : subd9_4 [-1, 3, -2] = true := by decide +kernel
theorem subd9_4_189 : subd9_4 [-1, 3, -1] = true := by decide +kernel
theorem subd9_4_190 : subd9_4 [-1, 3, 0] = true := by decide +kernel
theorem subd9_4_191 : subd9_4 [-1, 3, 1] = true := by decide +kernel
theorem sbd9_4_5 : ∀ q ∈ blkd9_4_5, subd9_4 q = true := by
  unfold blkd9_4_5
  exact List.forall_mem_cons.2 ⟨subd9_4_160, List.forall_mem_cons.2 ⟨subd9_4_161, List.forall_mem_cons.2 ⟨subd9_4_162, List.forall_mem_cons.2 ⟨subd9_4_163, List.forall_mem_cons.2 ⟨subd9_4_164, List.forall_mem_cons.2 ⟨subd9_4_165, List.forall_mem_cons.2 ⟨subd9_4_166, List.forall_mem_cons.2 ⟨subd9_4_167, List.forall_mem_cons.2 ⟨subd9_4_168, List.forall_mem_cons.2 ⟨subd9_4_169, List.forall_mem_cons.2 ⟨subd9_4_170, List.forall_mem_cons.2 ⟨subd9_4_171, List.forall_mem_cons.2 ⟨subd9_4_172, List.forall_mem_cons.2 ⟨subd9_4_173, List.forall_mem_cons.2 ⟨subd9_4_174, List.forall_mem_cons.2 ⟨subd9_4_175, List.forall_mem_cons.2 ⟨subd9_4_176, List.forall_mem_cons.2 ⟨subd9_4_177, List.forall_mem_cons.2 ⟨subd9_4_178, List.forall_mem_cons.2 ⟨subd9_4_179, List.forall_mem_cons.2 ⟨subd9_4_180, List.forall_mem_cons.2 ⟨subd9_4_181, List.forall_mem_cons.2 ⟨subd9_4_182, List.forall_mem_cons.2 ⟨subd9_4_183, List.forall_mem_cons.2 ⟨subd9_4_184, List.forall_mem_cons.2 ⟨subd9_4_185, List.forall_mem_cons.2 ⟨subd9_4_186, List.forall_mem_cons.2 ⟨subd9_4_187, List.forall_mem_cons.2 ⟨subd9_4_188, List.forall_mem_cons.2 ⟨subd9_4_189, List.forall_mem_cons.2 ⟨subd9_4_190, List.forall_mem_cons.2 ⟨subd9_4_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_4_192 : subd9_4 [-1, 3, 2] = true := by decide +kernel
theorem subd9_4_193 : subd9_4 [-1, 3, 3] = true := by decide +kernel
theorem subd9_4_194 : subd9_4 [-1, 3, 4] = true := by decide +kernel
theorem subd9_4_195 : subd9_4 [-1, 3, 5] = true := by decide +kernel
theorem subd9_4_196 : subd9_4 [-1, 3, 6] = true := by decide +kernel
theorem subd9_4_197 : subd9_4 [0, -4] = true := by decide +kernel
theorem subd9_4_198 : subd9_4 [0, -3] = true := by decide +kernel
theorem subd9_4_199 : subd9_4 [0, -2, -11] = true := by decide +kernel
theorem subd9_4_200 : subd9_4 [0, -2, -10] = true := by decide +kernel
theorem subd9_4_201 : subd9_4 [0, -2, -9] = true := by decide +kernel
theorem subd9_4_202 : subd9_4 [0, -2, -8] = true := by decide +kernel
theorem subd9_4_203 : subd9_4 [0, -2, -7] = true := by decide +kernel
theorem subd9_4_204 : subd9_4 [0, -2, -6] = true := by decide +kernel
theorem subd9_4_205 : subd9_4 [0, -2, -5] = true := by decide +kernel
theorem subd9_4_206 : subd9_4 [0, -2, -4] = true := by decide +kernel
theorem subd9_4_207 : subd9_4 [0, -2, -3] = true := by decide +kernel
theorem subd9_4_208 : subd9_4 [0, -2, -2] = true := by decide +kernel
theorem subd9_4_209 : subd9_4 [0, -2, -1] = true := by decide +kernel
theorem subd9_4_210 : subd9_4 [0, -2, 0] = true := by decide +kernel
theorem subd9_4_211 : subd9_4 [0, -2, 1] = true := by decide +kernel
theorem subd9_4_212 : subd9_4 [0, -2, 2] = true := by decide +kernel
theorem subd9_4_213 : subd9_4 [0, -2, 3] = true := by decide +kernel
theorem subd9_4_214 : subd9_4 [0, -2, 4] = true := by decide +kernel
theorem subd9_4_215 : subd9_4 [0, -2, 5] = true := by decide +kernel
theorem subd9_4_216 : subd9_4 [0, -2, 6] = true := by decide +kernel
theorem subd9_4_217 : subd9_4 [0, -2, 7] = true := by decide +kernel
theorem subd9_4_218 : subd9_4 [0, -2, 8] = true := by decide +kernel
theorem subd9_4_219 : subd9_4 [0, -2, 9] = true := by decide +kernel
theorem subd9_4_220 : subd9_4 [0, -2, 10] = true := by decide +kernel
theorem subd9_4_221 : subd9_4 [0, -2, 11] = true := by decide +kernel
theorem subd9_4_222 : subd9_4 [0, -1, -14] = true := by decide +kernel
theorem subd9_4_223 : subd9_4 [0, -1, -13] = true := by decide +kernel
theorem sbd9_4_6 : ∀ q ∈ blkd9_4_6, subd9_4 q = true := by
  unfold blkd9_4_6
  exact List.forall_mem_cons.2 ⟨subd9_4_192, List.forall_mem_cons.2 ⟨subd9_4_193, List.forall_mem_cons.2 ⟨subd9_4_194, List.forall_mem_cons.2 ⟨subd9_4_195, List.forall_mem_cons.2 ⟨subd9_4_196, List.forall_mem_cons.2 ⟨subd9_4_197, List.forall_mem_cons.2 ⟨subd9_4_198, List.forall_mem_cons.2 ⟨subd9_4_199, List.forall_mem_cons.2 ⟨subd9_4_200, List.forall_mem_cons.2 ⟨subd9_4_201, List.forall_mem_cons.2 ⟨subd9_4_202, List.forall_mem_cons.2 ⟨subd9_4_203, List.forall_mem_cons.2 ⟨subd9_4_204, List.forall_mem_cons.2 ⟨subd9_4_205, List.forall_mem_cons.2 ⟨subd9_4_206, List.forall_mem_cons.2 ⟨subd9_4_207, List.forall_mem_cons.2 ⟨subd9_4_208, List.forall_mem_cons.2 ⟨subd9_4_209, List.forall_mem_cons.2 ⟨subd9_4_210, List.forall_mem_cons.2 ⟨subd9_4_211, List.forall_mem_cons.2 ⟨subd9_4_212, List.forall_mem_cons.2 ⟨subd9_4_213, List.forall_mem_cons.2 ⟨subd9_4_214, List.forall_mem_cons.2 ⟨subd9_4_215, List.forall_mem_cons.2 ⟨subd9_4_216, List.forall_mem_cons.2 ⟨subd9_4_217, List.forall_mem_cons.2 ⟨subd9_4_218, List.forall_mem_cons.2 ⟨subd9_4_219, List.forall_mem_cons.2 ⟨subd9_4_220, List.forall_mem_cons.2 ⟨subd9_4_221, List.forall_mem_cons.2 ⟨subd9_4_222, List.forall_mem_cons.2 ⟨subd9_4_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_4_224 : subd9_4 [0, -1, -12] = true := by decide +kernel
theorem subd9_4_225 : subd9_4 [0, -1, -11] = true := by decide +kernel
theorem subd9_4_226 : subd9_4 [0, -1, -10] = true := by decide +kernel
theorem subd9_4_227 : subd9_4 [0, -1, -9] = true := by decide +kernel
theorem subd9_4_228 : subd9_4 [0, -1, -8] = true := by decide +kernel
theorem subd9_4_229 : subd9_4 [0, -1, -7] = true := by decide +kernel
theorem subd9_4_230 : subd9_4 [0, -1, -6] = true := by decide +kernel
theorem subd9_4_231 : subd9_4 [0, -1, -5] = true := by decide +kernel
theorem subd9_4_232 : subd9_4 [0, -1, -4] = true := by decide +kernel
theorem subd9_4_233 : subd9_4 [0, -1, -3] = true := by decide +kernel
theorem subd9_4_234 : subd9_4 [0, -1, -2] = true := by decide +kernel
theorem subd9_4_235 : subd9_4 [0, -1, -1] = true := by decide +kernel
theorem subd9_4_236 : subd9_4 [0, -1, 0] = true := by decide +kernel
theorem subd9_4_237 : subd9_4 [0, -1, 1] = true := by decide +kernel
theorem subd9_4_238 : subd9_4 [0, -1, 2] = true := by decide +kernel
theorem subd9_4_239 : subd9_4 [0, -1, 3] = true := by decide +kernel
theorem subd9_4_240 : subd9_4 [0, -1, 4] = true := by decide +kernel
theorem subd9_4_241 : subd9_4 [0, -1, 5] = true := by decide +kernel
theorem subd9_4_242 : subd9_4 [0, -1, 6] = true := by decide +kernel
theorem subd9_4_243 : subd9_4 [0, -1, 7] = true := by decide +kernel
theorem subd9_4_244 : subd9_4 [0, -1, 8] = true := by decide +kernel
theorem subd9_4_245 : subd9_4 [0, -1, 9] = true := by decide +kernel
theorem subd9_4_246 : subd9_4 [0, -1, 10] = true := by decide +kernel
theorem subd9_4_247 : subd9_4 [0, -1, 11] = true := by decide +kernel
theorem subd9_4_248 : subd9_4 [0, -1, 12] = true := by decide +kernel
theorem subd9_4_249 : subd9_4 [0, -1, 13] = true := by decide +kernel
theorem subd9_4_250 : subd9_4 [0, 0, -15] = true := by decide +kernel
theorem subd9_4_251 : subd9_4 [0, 0, -14] = true := by decide +kernel
theorem subd9_4_252 : subd9_4 [0, 0, -13] = true := by decide +kernel
theorem subd9_4_253 : subd9_4 [0, 0, -12] = true := by decide +kernel
theorem subd9_4_254 : subd9_4 [0, 0, -11] = true := by decide +kernel
theorem subd9_4_255 : subd9_4 [0, 0, -10] = true := by decide +kernel
theorem sbd9_4_7 : ∀ q ∈ blkd9_4_7, subd9_4 q = true := by
  unfold blkd9_4_7
  exact List.forall_mem_cons.2 ⟨subd9_4_224, List.forall_mem_cons.2 ⟨subd9_4_225, List.forall_mem_cons.2 ⟨subd9_4_226, List.forall_mem_cons.2 ⟨subd9_4_227, List.forall_mem_cons.2 ⟨subd9_4_228, List.forall_mem_cons.2 ⟨subd9_4_229, List.forall_mem_cons.2 ⟨subd9_4_230, List.forall_mem_cons.2 ⟨subd9_4_231, List.forall_mem_cons.2 ⟨subd9_4_232, List.forall_mem_cons.2 ⟨subd9_4_233, List.forall_mem_cons.2 ⟨subd9_4_234, List.forall_mem_cons.2 ⟨subd9_4_235, List.forall_mem_cons.2 ⟨subd9_4_236, List.forall_mem_cons.2 ⟨subd9_4_237, List.forall_mem_cons.2 ⟨subd9_4_238, List.forall_mem_cons.2 ⟨subd9_4_239, List.forall_mem_cons.2 ⟨subd9_4_240, List.forall_mem_cons.2 ⟨subd9_4_241, List.forall_mem_cons.2 ⟨subd9_4_242, List.forall_mem_cons.2 ⟨subd9_4_243, List.forall_mem_cons.2 ⟨subd9_4_244, List.forall_mem_cons.2 ⟨subd9_4_245, List.forall_mem_cons.2 ⟨subd9_4_246, List.forall_mem_cons.2 ⟨subd9_4_247, List.forall_mem_cons.2 ⟨subd9_4_248, List.forall_mem_cons.2 ⟨subd9_4_249, List.forall_mem_cons.2 ⟨subd9_4_250, List.forall_mem_cons.2 ⟨subd9_4_251, List.forall_mem_cons.2 ⟨subd9_4_252, List.forall_mem_cons.2 ⟨subd9_4_253, List.forall_mem_cons.2 ⟨subd9_4_254, List.forall_mem_cons.2 ⟨subd9_4_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_4_256 : subd9_4 [0, 0, -9] = true := by decide +kernel
theorem subd9_4_257 : subd9_4 [0, 0, -8] = true := by decide +kernel
theorem subd9_4_258 : subd9_4 [0, 0, -7] = true := by decide +kernel
theorem subd9_4_259 : subd9_4 [0, 0, -6] = true := by decide +kernel
theorem subd9_4_260 : subd9_4 [0, 0, -5] = true := by decide +kernel
theorem subd9_4_261 : subd9_4 [0, 0, -4] = true := by decide +kernel
theorem subd9_4_262 : subd9_4 [0, 0, -3] = true := by decide +kernel
theorem subd9_4_263 : subd9_4 [0, 0, -2] = true := by decide +kernel
theorem subd9_4_264 : subd9_4 [0, 0, -1] = true := by decide +kernel
theorem subd9_4_265 : subd9_4 [0, 0, 0] = true := by decide +kernel
theorem subd9_4_266 : subd9_4 [0, 0, 1] = true := by decide +kernel
theorem subd9_4_267 : subd9_4 [0, 0, 2] = true := by decide +kernel
theorem subd9_4_268 : subd9_4 [0, 0, 3] = true := by decide +kernel
theorem subd9_4_269 : subd9_4 [0, 0, 4] = true := by decide +kernel
theorem subd9_4_270 : subd9_4 [0, 0, 5] = true := by decide +kernel
theorem subd9_4_271 : subd9_4 [0, 0, 6] = true := by decide +kernel
theorem subd9_4_272 : subd9_4 [0, 0, 7] = true := by decide +kernel
theorem subd9_4_273 : subd9_4 [0, 0, 8] = true := by decide +kernel
theorem subd9_4_274 : subd9_4 [0, 0, 9] = true := by decide +kernel
theorem subd9_4_275 : subd9_4 [0, 0, 10] = true := by decide +kernel
theorem subd9_4_276 : subd9_4 [0, 0, 11] = true := by decide +kernel
theorem subd9_4_277 : subd9_4 [0, 0, 12] = true := by decide +kernel
theorem subd9_4_278 : subd9_4 [0, 0, 13] = true := by decide +kernel
theorem subd9_4_279 : subd9_4 [0, 0, 14] = true := by decide +kernel
theorem subd9_4_280 : subd9_4 [0, 1, -14] = true := by decide +kernel
theorem subd9_4_281 : subd9_4 [0, 1, -13] = true := by decide +kernel
theorem subd9_4_282 : subd9_4 [0, 1, -12] = true := by decide +kernel
theorem subd9_4_283 : subd9_4 [0, 1, -11] = true := by decide +kernel
theorem subd9_4_284 : subd9_4 [0, 1, -10] = true := by decide +kernel
theorem subd9_4_285 : subd9_4 [0, 1, -9] = true := by decide +kernel
theorem subd9_4_286 : subd9_4 [0, 1, -8] = true := by decide +kernel
theorem subd9_4_287 : subd9_4 [0, 1, -7] = true := by decide +kernel
theorem sbd9_4_8 : ∀ q ∈ blkd9_4_8, subd9_4 q = true := by
  unfold blkd9_4_8
  exact List.forall_mem_cons.2 ⟨subd9_4_256, List.forall_mem_cons.2 ⟨subd9_4_257, List.forall_mem_cons.2 ⟨subd9_4_258, List.forall_mem_cons.2 ⟨subd9_4_259, List.forall_mem_cons.2 ⟨subd9_4_260, List.forall_mem_cons.2 ⟨subd9_4_261, List.forall_mem_cons.2 ⟨subd9_4_262, List.forall_mem_cons.2 ⟨subd9_4_263, List.forall_mem_cons.2 ⟨subd9_4_264, List.forall_mem_cons.2 ⟨subd9_4_265, List.forall_mem_cons.2 ⟨subd9_4_266, List.forall_mem_cons.2 ⟨subd9_4_267, List.forall_mem_cons.2 ⟨subd9_4_268, List.forall_mem_cons.2 ⟨subd9_4_269, List.forall_mem_cons.2 ⟨subd9_4_270, List.forall_mem_cons.2 ⟨subd9_4_271, List.forall_mem_cons.2 ⟨subd9_4_272, List.forall_mem_cons.2 ⟨subd9_4_273, List.forall_mem_cons.2 ⟨subd9_4_274, List.forall_mem_cons.2 ⟨subd9_4_275, List.forall_mem_cons.2 ⟨subd9_4_276, List.forall_mem_cons.2 ⟨subd9_4_277, List.forall_mem_cons.2 ⟨subd9_4_278, List.forall_mem_cons.2 ⟨subd9_4_279, List.forall_mem_cons.2 ⟨subd9_4_280, List.forall_mem_cons.2 ⟨subd9_4_281, List.forall_mem_cons.2 ⟨subd9_4_282, List.forall_mem_cons.2 ⟨subd9_4_283, List.forall_mem_cons.2 ⟨subd9_4_284, List.forall_mem_cons.2 ⟨subd9_4_285, List.forall_mem_cons.2 ⟨subd9_4_286, List.forall_mem_cons.2 ⟨subd9_4_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_4_288 : subd9_4 [0, 1, -6] = true := by decide +kernel
theorem subd9_4_289 : subd9_4 [0, 1, -5] = true := by decide +kernel
theorem subd9_4_290 : subd9_4 [0, 1, -4] = true := by decide +kernel
theorem subd9_4_291 : subd9_4 [0, 1, -3] = true := by decide +kernel
theorem subd9_4_292 : subd9_4 [0, 1, -2] = true := by decide +kernel
theorem subd9_4_293 : subd9_4 [0, 1, -1] = true := by decide +kernel
theorem subd9_4_294 : subd9_4 [0, 1, 0] = true := by decide +kernel
theorem subd9_4_295 : subd9_4 [0, 1, 1] = true := by decide +kernel
theorem subd9_4_296 : subd9_4 [0, 1, 2] = true := by decide +kernel
theorem subd9_4_297 : subd9_4 [0, 1, 3] = true := by decide +kernel
theorem subd9_4_298 : subd9_4 [0, 1, 4] = true := by decide +kernel
theorem subd9_4_299 : subd9_4 [0, 1, 5] = true := by decide +kernel
theorem subd9_4_300 : subd9_4 [0, 1, 6] = true := by decide +kernel
theorem subd9_4_301 : subd9_4 [0, 1, 7] = true := by decide +kernel
theorem subd9_4_302 : subd9_4 [0, 1, 8] = true := by decide +kernel
theorem subd9_4_303 : subd9_4 [0, 1, 9] = true := by decide +kernel
theorem subd9_4_304 : subd9_4 [0, 1, 10] = true := by decide +kernel
theorem subd9_4_305 : subd9_4 [0, 1, 11] = true := by decide +kernel
theorem subd9_4_306 : subd9_4 [0, 1, 12] = true := by decide +kernel
theorem subd9_4_307 : subd9_4 [0, 1, 13] = true := by decide +kernel
theorem subd9_4_308 : subd9_4 [0, 2, -12] = true := by decide +kernel
theorem subd9_4_309 : subd9_4 [0, 2, -11] = true := by decide +kernel
theorem subd9_4_310 : subd9_4 [0, 2, -10] = true := by decide +kernel
theorem subd9_4_311 : subd9_4 [0, 2, -9] = true := by decide +kernel
theorem subd9_4_312 : subd9_4 [0, 2, -8] = true := by decide +kernel
theorem subd9_4_313 : subd9_4 [0, 2, -7] = true := by decide +kernel
theorem subd9_4_314 : subd9_4 [0, 2, -6] = true := by decide +kernel
theorem subd9_4_315 : subd9_4 [0, 2, -5] = true := by decide +kernel
theorem subd9_4_316 : subd9_4 [0, 2, -4] = true := by decide +kernel
theorem subd9_4_317 : subd9_4 [0, 2, -3] = true := by decide +kernel
theorem subd9_4_318 : subd9_4 [0, 2, -2] = true := by decide +kernel
theorem subd9_4_319 : subd9_4 [0, 2, -1] = true := by decide +kernel
theorem sbd9_4_9 : ∀ q ∈ blkd9_4_9, subd9_4 q = true := by
  unfold blkd9_4_9
  exact List.forall_mem_cons.2 ⟨subd9_4_288, List.forall_mem_cons.2 ⟨subd9_4_289, List.forall_mem_cons.2 ⟨subd9_4_290, List.forall_mem_cons.2 ⟨subd9_4_291, List.forall_mem_cons.2 ⟨subd9_4_292, List.forall_mem_cons.2 ⟨subd9_4_293, List.forall_mem_cons.2 ⟨subd9_4_294, List.forall_mem_cons.2 ⟨subd9_4_295, List.forall_mem_cons.2 ⟨subd9_4_296, List.forall_mem_cons.2 ⟨subd9_4_297, List.forall_mem_cons.2 ⟨subd9_4_298, List.forall_mem_cons.2 ⟨subd9_4_299, List.forall_mem_cons.2 ⟨subd9_4_300, List.forall_mem_cons.2 ⟨subd9_4_301, List.forall_mem_cons.2 ⟨subd9_4_302, List.forall_mem_cons.2 ⟨subd9_4_303, List.forall_mem_cons.2 ⟨subd9_4_304, List.forall_mem_cons.2 ⟨subd9_4_305, List.forall_mem_cons.2 ⟨subd9_4_306, List.forall_mem_cons.2 ⟨subd9_4_307, List.forall_mem_cons.2 ⟨subd9_4_308, List.forall_mem_cons.2 ⟨subd9_4_309, List.forall_mem_cons.2 ⟨subd9_4_310, List.forall_mem_cons.2 ⟨subd9_4_311, List.forall_mem_cons.2 ⟨subd9_4_312, List.forall_mem_cons.2 ⟨subd9_4_313, List.forall_mem_cons.2 ⟨subd9_4_314, List.forall_mem_cons.2 ⟨subd9_4_315, List.forall_mem_cons.2 ⟨subd9_4_316, List.forall_mem_cons.2 ⟨subd9_4_317, List.forall_mem_cons.2 ⟨subd9_4_318, List.forall_mem_cons.2 ⟨subd9_4_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_4_320 : subd9_4 [0, 2, 0] = true := by decide +kernel
theorem subd9_4_321 : subd9_4 [0, 2, 1] = true := by decide +kernel
theorem subd9_4_322 : subd9_4 [0, 2, 2] = true := by decide +kernel
theorem subd9_4_323 : subd9_4 [0, 2, 3] = true := by decide +kernel
theorem subd9_4_324 : subd9_4 [0, 2, 4] = true := by decide +kernel
theorem subd9_4_325 : subd9_4 [0, 2, 5] = true := by decide +kernel
theorem subd9_4_326 : subd9_4 [0, 2, 6] = true := by decide +kernel
theorem subd9_4_327 : subd9_4 [0, 2, 7] = true := by decide +kernel
theorem subd9_4_328 : subd9_4 [0, 2, 8] = true := by decide +kernel
theorem subd9_4_329 : subd9_4 [0, 2, 9] = true := by decide +kernel
theorem subd9_4_330 : subd9_4 [0, 2, 10] = true := by decide +kernel
theorem subd9_4_331 : subd9_4 [0, 3] = true := by decide +kernel
theorem subd9_4_332 : subd9_4 [1, -4] = true := by decide +kernel
theorem subd9_4_333 : subd9_4 [1, -3, -7] = true := by decide +kernel
theorem subd9_4_334 : subd9_4 [1, -3, -6] = true := by decide +kernel
theorem subd9_4_335 : subd9_4 [1, -3, -5] = true := by decide +kernel
theorem subd9_4_336 : subd9_4 [1, -3, -4] = true := by decide +kernel
theorem subd9_4_337 : subd9_4 [1, -3, -3] = true := by decide +kernel
theorem subd9_4_338 : subd9_4 [1, -3, -2] = true := by decide +kernel
theorem subd9_4_339 : subd9_4 [1, -3, -1] = true := by decide +kernel
theorem subd9_4_340 : subd9_4 [1, -3, 0] = true := by decide +kernel
theorem subd9_4_341 : subd9_4 [1, -3, 1] = true := by decide +kernel
theorem subd9_4_342 : subd9_4 [1, -3, 2] = true := by decide +kernel
theorem subd9_4_343 : subd9_4 [1, -3, 3] = true := by decide +kernel
theorem subd9_4_344 : subd9_4 [1, -3, 4] = true := by decide +kernel
theorem subd9_4_345 : subd9_4 [1, -3, 5] = true := by decide +kernel
theorem subd9_4_346 : subd9_4 [1, -3, 6] = true := by decide +kernel
theorem subd9_4_347 : subd9_4 [1, -2, -12] = true := by decide +kernel
theorem subd9_4_348 : subd9_4 [1, -2, -11] = true := by decide +kernel
theorem subd9_4_349 : subd9_4 [1, -2, -10] = true := by decide +kernel
theorem subd9_4_350 : subd9_4 [1, -2, -9] = true := by decide +kernel
theorem subd9_4_351 : subd9_4 [1, -2, -8] = true := by decide +kernel
theorem sbd9_4_10 : ∀ q ∈ blkd9_4_10, subd9_4 q = true := by
  unfold blkd9_4_10
  exact List.forall_mem_cons.2 ⟨subd9_4_320, List.forall_mem_cons.2 ⟨subd9_4_321, List.forall_mem_cons.2 ⟨subd9_4_322, List.forall_mem_cons.2 ⟨subd9_4_323, List.forall_mem_cons.2 ⟨subd9_4_324, List.forall_mem_cons.2 ⟨subd9_4_325, List.forall_mem_cons.2 ⟨subd9_4_326, List.forall_mem_cons.2 ⟨subd9_4_327, List.forall_mem_cons.2 ⟨subd9_4_328, List.forall_mem_cons.2 ⟨subd9_4_329, List.forall_mem_cons.2 ⟨subd9_4_330, List.forall_mem_cons.2 ⟨subd9_4_331, List.forall_mem_cons.2 ⟨subd9_4_332, List.forall_mem_cons.2 ⟨subd9_4_333, List.forall_mem_cons.2 ⟨subd9_4_334, List.forall_mem_cons.2 ⟨subd9_4_335, List.forall_mem_cons.2 ⟨subd9_4_336, List.forall_mem_cons.2 ⟨subd9_4_337, List.forall_mem_cons.2 ⟨subd9_4_338, List.forall_mem_cons.2 ⟨subd9_4_339, List.forall_mem_cons.2 ⟨subd9_4_340, List.forall_mem_cons.2 ⟨subd9_4_341, List.forall_mem_cons.2 ⟨subd9_4_342, List.forall_mem_cons.2 ⟨subd9_4_343, List.forall_mem_cons.2 ⟨subd9_4_344, List.forall_mem_cons.2 ⟨subd9_4_345, List.forall_mem_cons.2 ⟨subd9_4_346, List.forall_mem_cons.2 ⟨subd9_4_347, List.forall_mem_cons.2 ⟨subd9_4_348, List.forall_mem_cons.2 ⟨subd9_4_349, List.forall_mem_cons.2 ⟨subd9_4_350, List.forall_mem_cons.2 ⟨subd9_4_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_4_352 : subd9_4 [1, -2, -7] = true := by decide +kernel
theorem subd9_4_353 : subd9_4 [1, -2, -6] = true := by decide +kernel
theorem subd9_4_354 : subd9_4 [1, -2, -5] = true := by decide +kernel
theorem subd9_4_355 : subd9_4 [1, -2, -4] = true := by decide +kernel
theorem subd9_4_356 : subd9_4 [1, -2, -3] = true := by decide +kernel
theorem subd9_4_357 : subd9_4 [1, -2, -2] = true := by decide +kernel
theorem subd9_4_358 : subd9_4 [1, -2, -1] = true := by decide +kernel
theorem subd9_4_359 : subd9_4 [1, -2, 0] = true := by decide +kernel
theorem subd9_4_360 : subd9_4 [1, -2, 1] = true := by decide +kernel
theorem subd9_4_361 : subd9_4 [1, -2, 2] = true := by decide +kernel
theorem subd9_4_362 : subd9_4 [1, -2, 3] = true := by decide +kernel
theorem subd9_4_363 : subd9_4 [1, -2, 4] = true := by decide +kernel
theorem subd9_4_364 : subd9_4 [1, -2, 5] = true := by decide +kernel
theorem subd9_4_365 : subd9_4 [1, -2, 6] = true := by decide +kernel
theorem subd9_4_366 : subd9_4 [1, -2, 7] = true := by decide +kernel
theorem subd9_4_367 : subd9_4 [1, -2, 8] = true := by decide +kernel
theorem subd9_4_368 : subd9_4 [1, -2, 9] = true := by decide +kernel
theorem subd9_4_369 : subd9_4 [1, -2, 10] = true := by decide +kernel
theorem subd9_4_370 : subd9_4 [1, -2, 11] = true := by decide +kernel
theorem subd9_4_371 : subd9_4 [1, -1, -14] = true := by decide +kernel
theorem subd9_4_372 : subd9_4 [1, -1, -13] = true := by decide +kernel
theorem subd9_4_373 : subd9_4 [1, -1, -12] = true := by decide +kernel
theorem subd9_4_374 : subd9_4 [1, -1, -11] = true := by decide +kernel
theorem subd9_4_375 : subd9_4 [1, -1, -10] = true := by decide +kernel
theorem subd9_4_376 : subd9_4 [1, -1, -9] = true := by decide +kernel
theorem subd9_4_377 : subd9_4 [1, -1, -8] = true := by decide +kernel
theorem subd9_4_378 : subd9_4 [1, -1, -7] = true := by decide +kernel
theorem subd9_4_379 : subd9_4 [1, -1, -6] = true := by decide +kernel
theorem subd9_4_380 : subd9_4 [1, -1, -5] = true := by decide +kernel
theorem subd9_4_381 : subd9_4 [1, -1, -4] = true := by decide +kernel
theorem subd9_4_382 : subd9_4 [1, -1, -3] = true := by decide +kernel
theorem subd9_4_383 : subd9_4 [1, -1, -2] = true := by decide +kernel
theorem sbd9_4_11 : ∀ q ∈ blkd9_4_11, subd9_4 q = true := by
  unfold blkd9_4_11
  exact List.forall_mem_cons.2 ⟨subd9_4_352, List.forall_mem_cons.2 ⟨subd9_4_353, List.forall_mem_cons.2 ⟨subd9_4_354, List.forall_mem_cons.2 ⟨subd9_4_355, List.forall_mem_cons.2 ⟨subd9_4_356, List.forall_mem_cons.2 ⟨subd9_4_357, List.forall_mem_cons.2 ⟨subd9_4_358, List.forall_mem_cons.2 ⟨subd9_4_359, List.forall_mem_cons.2 ⟨subd9_4_360, List.forall_mem_cons.2 ⟨subd9_4_361, List.forall_mem_cons.2 ⟨subd9_4_362, List.forall_mem_cons.2 ⟨subd9_4_363, List.forall_mem_cons.2 ⟨subd9_4_364, List.forall_mem_cons.2 ⟨subd9_4_365, List.forall_mem_cons.2 ⟨subd9_4_366, List.forall_mem_cons.2 ⟨subd9_4_367, List.forall_mem_cons.2 ⟨subd9_4_368, List.forall_mem_cons.2 ⟨subd9_4_369, List.forall_mem_cons.2 ⟨subd9_4_370, List.forall_mem_cons.2 ⟨subd9_4_371, List.forall_mem_cons.2 ⟨subd9_4_372, List.forall_mem_cons.2 ⟨subd9_4_373, List.forall_mem_cons.2 ⟨subd9_4_374, List.forall_mem_cons.2 ⟨subd9_4_375, List.forall_mem_cons.2 ⟨subd9_4_376, List.forall_mem_cons.2 ⟨subd9_4_377, List.forall_mem_cons.2 ⟨subd9_4_378, List.forall_mem_cons.2 ⟨subd9_4_379, List.forall_mem_cons.2 ⟨subd9_4_380, List.forall_mem_cons.2 ⟨subd9_4_381, List.forall_mem_cons.2 ⟨subd9_4_382, List.forall_mem_cons.2 ⟨subd9_4_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_4_384 : subd9_4 [1, -1, -1] = true := by decide +kernel
theorem subd9_4_385 : subd9_4 [1, -1, 0] = true := by decide +kernel
theorem subd9_4_386 : subd9_4 [1, -1, 1] = true := by decide +kernel
theorem subd9_4_387 : subd9_4 [1, -1, 2] = true := by decide +kernel
theorem subd9_4_388 : subd9_4 [1, -1, 3] = true := by decide +kernel
theorem subd9_4_389 : subd9_4 [1, -1, 4] = true := by decide +kernel
theorem subd9_4_390 : subd9_4 [1, -1, 5] = true := by decide +kernel
theorem subd9_4_391 : subd9_4 [1, -1, 6] = true := by decide +kernel
theorem subd9_4_392 : subd9_4 [1, -1, 7] = true := by decide +kernel
theorem subd9_4_393 : subd9_4 [1, -1, 8] = true := by decide +kernel
theorem subd9_4_394 : subd9_4 [1, -1, 9] = true := by decide +kernel
theorem subd9_4_395 : subd9_4 [1, -1, 10] = true := by decide +kernel
theorem subd9_4_396 : subd9_4 [1, -1, 11] = true := by decide +kernel
theorem subd9_4_397 : subd9_4 [1, -1, 12] = true := by decide +kernel
theorem subd9_4_398 : subd9_4 [1, 0, -14] = true := by decide +kernel
theorem subd9_4_399 : subd9_4 [1, 0, -13] = true := by decide +kernel
theorem subd9_4_400 : subd9_4 [1, 0, -12] = true := by decide +kernel
theorem subd9_4_401 : subd9_4 [1, 0, -11] = true := by decide +kernel
theorem subd9_4_402 : subd9_4 [1, 0, -10] = true := by decide +kernel
theorem subd9_4_403 : subd9_4 [1, 0, -9] = true := by decide +kernel
theorem subd9_4_404 : subd9_4 [1, 0, -8] = true := by decide +kernel
theorem subd9_4_405 : subd9_4 [1, 0, -7] = true := by decide +kernel
theorem subd9_4_406 : subd9_4 [1, 0, -6] = true := by decide +kernel
theorem subd9_4_407 : subd9_4 [1, 0, -5] = true := by decide +kernel
theorem subd9_4_408 : subd9_4 [1, 0, -4] = true := by decide +kernel
theorem subd9_4_409 : subd9_4 [1, 0, -3] = true := by decide +kernel
theorem subd9_4_410 : subd9_4 [1, 0, -2] = true := by decide +kernel
theorem subd9_4_411 : subd9_4 [1, 0, -1] = true := by decide +kernel
theorem subd9_4_412 : subd9_4 [1, 0, 0] = true := by decide +kernel
theorem subd9_4_413 : subd9_4 [1, 0, 1] = true := by decide +kernel
theorem subd9_4_414 : subd9_4 [1, 0, 2] = true := by decide +kernel
theorem subd9_4_415 : subd9_4 [1, 0, 3] = true := by decide +kernel
theorem sbd9_4_12 : ∀ q ∈ blkd9_4_12, subd9_4 q = true := by
  unfold blkd9_4_12
  exact List.forall_mem_cons.2 ⟨subd9_4_384, List.forall_mem_cons.2 ⟨subd9_4_385, List.forall_mem_cons.2 ⟨subd9_4_386, List.forall_mem_cons.2 ⟨subd9_4_387, List.forall_mem_cons.2 ⟨subd9_4_388, List.forall_mem_cons.2 ⟨subd9_4_389, List.forall_mem_cons.2 ⟨subd9_4_390, List.forall_mem_cons.2 ⟨subd9_4_391, List.forall_mem_cons.2 ⟨subd9_4_392, List.forall_mem_cons.2 ⟨subd9_4_393, List.forall_mem_cons.2 ⟨subd9_4_394, List.forall_mem_cons.2 ⟨subd9_4_395, List.forall_mem_cons.2 ⟨subd9_4_396, List.forall_mem_cons.2 ⟨subd9_4_397, List.forall_mem_cons.2 ⟨subd9_4_398, List.forall_mem_cons.2 ⟨subd9_4_399, List.forall_mem_cons.2 ⟨subd9_4_400, List.forall_mem_cons.2 ⟨subd9_4_401, List.forall_mem_cons.2 ⟨subd9_4_402, List.forall_mem_cons.2 ⟨subd9_4_403, List.forall_mem_cons.2 ⟨subd9_4_404, List.forall_mem_cons.2 ⟨subd9_4_405, List.forall_mem_cons.2 ⟨subd9_4_406, List.forall_mem_cons.2 ⟨subd9_4_407, List.forall_mem_cons.2 ⟨subd9_4_408, List.forall_mem_cons.2 ⟨subd9_4_409, List.forall_mem_cons.2 ⟨subd9_4_410, List.forall_mem_cons.2 ⟨subd9_4_411, List.forall_mem_cons.2 ⟨subd9_4_412, List.forall_mem_cons.2 ⟨subd9_4_413, List.forall_mem_cons.2 ⟨subd9_4_414, List.forall_mem_cons.2 ⟨subd9_4_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_4_416 : subd9_4 [1, 0, 4] = true := by decide +kernel
theorem subd9_4_417 : subd9_4 [1, 0, 5] = true := by decide +kernel
theorem subd9_4_418 : subd9_4 [1, 0, 6] = true := by decide +kernel
theorem subd9_4_419 : subd9_4 [1, 0, 7] = true := by decide +kernel
theorem subd9_4_420 : subd9_4 [1, 0, 8] = true := by decide +kernel
theorem subd9_4_421 : subd9_4 [1, 0, 9] = true := by decide +kernel
theorem subd9_4_422 : subd9_4 [1, 0, 10] = true := by decide +kernel
theorem subd9_4_423 : subd9_4 [1, 0, 11] = true := by decide +kernel
theorem subd9_4_424 : subd9_4 [1, 0, 12] = true := by decide +kernel
theorem subd9_4_425 : subd9_4 [1, 1, -13] = true := by decide +kernel
theorem subd9_4_426 : subd9_4 [1, 1, -12] = true := by decide +kernel
theorem subd9_4_427 : subd9_4 [1, 1, -11] = true := by decide +kernel
theorem subd9_4_428 : subd9_4 [1, 1, -10] = true := by decide +kernel
theorem subd9_4_429 : subd9_4 [1, 1, -9] = true := by decide +kernel
theorem subd9_4_430 : subd9_4 [1, 1, -8] = true := by decide +kernel
theorem subd9_4_431 : subd9_4 [1, 1, -7] = true := by decide +kernel
theorem subd9_4_432 : subd9_4 [1, 1, -6] = true := by decide +kernel
theorem subd9_4_433 : subd9_4 [1, 1, -5] = true := by decide +kernel
theorem subd9_4_434 : subd9_4 [1, 1, -4] = true := by decide +kernel
theorem subd9_4_435 : subd9_4 [1, 1, -3] = true := by decide +kernel
theorem subd9_4_436 : subd9_4 [1, 1, -2] = true := by decide +kernel
theorem subd9_4_437 : subd9_4 [1, 1, -1] = true := by decide +kernel
theorem subd9_4_438 : subd9_4 [1, 1, 0] = true := by decide +kernel
theorem subd9_4_439 : subd9_4 [1, 1, 1] = true := by decide +kernel
theorem subd9_4_440 : subd9_4 [1, 1, 2] = true := by decide +kernel
theorem subd9_4_441 : subd9_4 [1, 1, 3] = true := by decide +kernel
theorem subd9_4_442 : subd9_4 [1, 1, 4] = true := by decide +kernel
theorem subd9_4_443 : subd9_4 [1, 1, 5] = true := by decide +kernel
theorem subd9_4_444 : subd9_4 [1, 1, 6] = true := by decide +kernel
theorem subd9_4_445 : subd9_4 [1, 1, 7] = true := by decide +kernel
theorem subd9_4_446 : subd9_4 [1, 1, 8] = true := by decide +kernel
theorem subd9_4_447 : subd9_4 [1, 1, 9] = true := by decide +kernel
theorem sbd9_4_13 : ∀ q ∈ blkd9_4_13, subd9_4 q = true := by
  unfold blkd9_4_13
  exact List.forall_mem_cons.2 ⟨subd9_4_416, List.forall_mem_cons.2 ⟨subd9_4_417, List.forall_mem_cons.2 ⟨subd9_4_418, List.forall_mem_cons.2 ⟨subd9_4_419, List.forall_mem_cons.2 ⟨subd9_4_420, List.forall_mem_cons.2 ⟨subd9_4_421, List.forall_mem_cons.2 ⟨subd9_4_422, List.forall_mem_cons.2 ⟨subd9_4_423, List.forall_mem_cons.2 ⟨subd9_4_424, List.forall_mem_cons.2 ⟨subd9_4_425, List.forall_mem_cons.2 ⟨subd9_4_426, List.forall_mem_cons.2 ⟨subd9_4_427, List.forall_mem_cons.2 ⟨subd9_4_428, List.forall_mem_cons.2 ⟨subd9_4_429, List.forall_mem_cons.2 ⟨subd9_4_430, List.forall_mem_cons.2 ⟨subd9_4_431, List.forall_mem_cons.2 ⟨subd9_4_432, List.forall_mem_cons.2 ⟨subd9_4_433, List.forall_mem_cons.2 ⟨subd9_4_434, List.forall_mem_cons.2 ⟨subd9_4_435, List.forall_mem_cons.2 ⟨subd9_4_436, List.forall_mem_cons.2 ⟨subd9_4_437, List.forall_mem_cons.2 ⟨subd9_4_438, List.forall_mem_cons.2 ⟨subd9_4_439, List.forall_mem_cons.2 ⟨subd9_4_440, List.forall_mem_cons.2 ⟨subd9_4_441, List.forall_mem_cons.2 ⟨subd9_4_442, List.forall_mem_cons.2 ⟨subd9_4_443, List.forall_mem_cons.2 ⟨subd9_4_444, List.forall_mem_cons.2 ⟨subd9_4_445, List.forall_mem_cons.2 ⟨subd9_4_446, List.forall_mem_cons.2 ⟨subd9_4_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_4_448 : subd9_4 [1, 1, 10] = true := by decide +kernel
theorem subd9_4_449 : subd9_4 [1, 1, 11] = true := by decide +kernel
theorem subd9_4_450 : subd9_4 [1, 2, -9] = true := by decide +kernel
theorem subd9_4_451 : subd9_4 [1, 2, -8] = true := by decide +kernel
theorem subd9_4_452 : subd9_4 [1, 2, -7] = true := by decide +kernel
theorem subd9_4_453 : subd9_4 [1, 2, -6] = true := by decide +kernel
theorem subd9_4_454 : subd9_4 [1, 2, -5] = true := by decide +kernel
theorem subd9_4_455 : subd9_4 [1, 2, -4] = true := by decide +kernel
theorem subd9_4_456 : subd9_4 [1, 2, -3] = true := by decide +kernel
theorem subd9_4_457 : subd9_4 [1, 2, -2] = true := by decide +kernel
theorem subd9_4_458 : subd9_4 [1, 2, -1] = true := by decide +kernel
theorem subd9_4_459 : subd9_4 [1, 2, 0] = true := by decide +kernel
theorem subd9_4_460 : subd9_4 [1, 2, 1] = true := by decide +kernel
theorem subd9_4_461 : subd9_4 [1, 2, 2] = true := by decide +kernel
theorem subd9_4_462 : subd9_4 [1, 2, 3] = true := by decide +kernel
theorem subd9_4_463 : subd9_4 [1, 2, 4] = true := by decide +kernel
theorem subd9_4_464 : subd9_4 [1, 2, 5] = true := by decide +kernel
theorem subd9_4_465 : subd9_4 [1, 2, 6] = true := by decide +kernel
theorem subd9_4_466 : subd9_4 [2, -4] = true := by decide +kernel
theorem subd9_4_467 : subd9_4 [2, -3] = true := by decide +kernel
theorem subd9_4_468 : subd9_4 [2, -2, -10] = true := by decide +kernel
theorem subd9_4_469 : subd9_4 [2, -2, -9] = true := by decide +kernel
theorem subd9_4_470 : subd9_4 [2, -2, -8] = true := by decide +kernel
theorem subd9_4_471 : subd9_4 [2, -2, -7] = true := by decide +kernel
theorem subd9_4_472 : subd9_4 [2, -2, -6] = true := by decide +kernel
theorem subd9_4_473 : subd9_4 [2, -2, -5] = true := by decide +kernel
theorem subd9_4_474 : subd9_4 [2, -2, -4] = true := by decide +kernel
theorem subd9_4_475 : subd9_4 [2, -2, -3] = true := by decide +kernel
theorem subd9_4_476 : subd9_4 [2, -2, -2] = true := by decide +kernel
theorem subd9_4_477 : subd9_4 [2, -2, -1] = true := by decide +kernel
theorem subd9_4_478 : subd9_4 [2, -2, 0] = true := by decide +kernel
theorem subd9_4_479 : subd9_4 [2, -2, 1] = true := by decide +kernel
theorem sbd9_4_14 : ∀ q ∈ blkd9_4_14, subd9_4 q = true := by
  unfold blkd9_4_14
  exact List.forall_mem_cons.2 ⟨subd9_4_448, List.forall_mem_cons.2 ⟨subd9_4_449, List.forall_mem_cons.2 ⟨subd9_4_450, List.forall_mem_cons.2 ⟨subd9_4_451, List.forall_mem_cons.2 ⟨subd9_4_452, List.forall_mem_cons.2 ⟨subd9_4_453, List.forall_mem_cons.2 ⟨subd9_4_454, List.forall_mem_cons.2 ⟨subd9_4_455, List.forall_mem_cons.2 ⟨subd9_4_456, List.forall_mem_cons.2 ⟨subd9_4_457, List.forall_mem_cons.2 ⟨subd9_4_458, List.forall_mem_cons.2 ⟨subd9_4_459, List.forall_mem_cons.2 ⟨subd9_4_460, List.forall_mem_cons.2 ⟨subd9_4_461, List.forall_mem_cons.2 ⟨subd9_4_462, List.forall_mem_cons.2 ⟨subd9_4_463, List.forall_mem_cons.2 ⟨subd9_4_464, List.forall_mem_cons.2 ⟨subd9_4_465, List.forall_mem_cons.2 ⟨subd9_4_466, List.forall_mem_cons.2 ⟨subd9_4_467, List.forall_mem_cons.2 ⟨subd9_4_468, List.forall_mem_cons.2 ⟨subd9_4_469, List.forall_mem_cons.2 ⟨subd9_4_470, List.forall_mem_cons.2 ⟨subd9_4_471, List.forall_mem_cons.2 ⟨subd9_4_472, List.forall_mem_cons.2 ⟨subd9_4_473, List.forall_mem_cons.2 ⟨subd9_4_474, List.forall_mem_cons.2 ⟨subd9_4_475, List.forall_mem_cons.2 ⟨subd9_4_476, List.forall_mem_cons.2 ⟨subd9_4_477, List.forall_mem_cons.2 ⟨subd9_4_478, List.forall_mem_cons.2 ⟨subd9_4_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_4_480 : subd9_4 [2, -2, 2] = true := by decide +kernel
theorem subd9_4_481 : subd9_4 [2, -2, 3] = true := by decide +kernel
theorem subd9_4_482 : subd9_4 [2, -2, 4] = true := by decide +kernel
theorem subd9_4_483 : subd9_4 [2, -2, 5] = true := by decide +kernel
theorem subd9_4_484 : subd9_4 [2, -2, 6] = true := by decide +kernel
theorem subd9_4_485 : subd9_4 [2, -2, 7] = true := by decide +kernel
theorem subd9_4_486 : subd9_4 [2, -2, 8] = true := by decide +kernel
theorem subd9_4_487 : subd9_4 [2, -1, -11] = true := by decide +kernel
theorem subd9_4_488 : subd9_4 [2, -1, -10] = true := by decide +kernel
theorem subd9_4_489 : subd9_4 [2, -1, -9] = true := by decide +kernel
theorem subd9_4_490 : subd9_4 [2, -1, -8] = true := by decide +kernel
theorem subd9_4_491 : subd9_4 [2, -1, -7] = true := by decide +kernel
theorem subd9_4_492 : subd9_4 [2, -1, -6] = true := by decide +kernel
theorem subd9_4_493 : subd9_4 [2, -1, -5] = true := by decide +kernel
theorem subd9_4_494 : subd9_4 [2, -1, -4] = true := by decide +kernel
theorem subd9_4_495 : subd9_4 [2, -1, -3] = true := by decide +kernel
theorem subd9_4_496 : subd9_4 [2, -1, -2] = true := by decide +kernel
theorem subd9_4_497 : subd9_4 [2, -1, -1] = true := by decide +kernel
theorem subd9_4_498 : subd9_4 [2, -1, 0] = true := by decide +kernel
theorem subd9_4_499 : subd9_4 [2, -1, 1] = true := by decide +kernel
theorem subd9_4_500 : subd9_4 [2, -1, 2] = true := by decide +kernel
theorem subd9_4_501 : subd9_4 [2, -1, 3] = true := by decide +kernel
theorem subd9_4_502 : subd9_4 [2, -1, 4] = true := by decide +kernel
theorem subd9_4_503 : subd9_4 [2, -1, 5] = true := by decide +kernel
theorem subd9_4_504 : subd9_4 [2, -1, 6] = true := by decide +kernel
theorem subd9_4_505 : subd9_4 [2, -1, 7] = true := by decide +kernel
theorem subd9_4_506 : subd9_4 [2, -1, 8] = true := by decide +kernel
theorem subd9_4_507 : subd9_4 [2, -1, 9] = true := by decide +kernel
theorem subd9_4_508 : subd9_4 [2, 0, -11] = true := by decide +kernel
theorem subd9_4_509 : subd9_4 [2, 0, -10] = true := by decide +kernel
theorem subd9_4_510 : subd9_4 [2, 0, -9] = true := by decide +kernel
theorem subd9_4_511 : subd9_4 [2, 0, -8] = true := by decide +kernel
theorem sbd9_4_15 : ∀ q ∈ blkd9_4_15, subd9_4 q = true := by
  unfold blkd9_4_15
  exact List.forall_mem_cons.2 ⟨subd9_4_480, List.forall_mem_cons.2 ⟨subd9_4_481, List.forall_mem_cons.2 ⟨subd9_4_482, List.forall_mem_cons.2 ⟨subd9_4_483, List.forall_mem_cons.2 ⟨subd9_4_484, List.forall_mem_cons.2 ⟨subd9_4_485, List.forall_mem_cons.2 ⟨subd9_4_486, List.forall_mem_cons.2 ⟨subd9_4_487, List.forall_mem_cons.2 ⟨subd9_4_488, List.forall_mem_cons.2 ⟨subd9_4_489, List.forall_mem_cons.2 ⟨subd9_4_490, List.forall_mem_cons.2 ⟨subd9_4_491, List.forall_mem_cons.2 ⟨subd9_4_492, List.forall_mem_cons.2 ⟨subd9_4_493, List.forall_mem_cons.2 ⟨subd9_4_494, List.forall_mem_cons.2 ⟨subd9_4_495, List.forall_mem_cons.2 ⟨subd9_4_496, List.forall_mem_cons.2 ⟨subd9_4_497, List.forall_mem_cons.2 ⟨subd9_4_498, List.forall_mem_cons.2 ⟨subd9_4_499, List.forall_mem_cons.2 ⟨subd9_4_500, List.forall_mem_cons.2 ⟨subd9_4_501, List.forall_mem_cons.2 ⟨subd9_4_502, List.forall_mem_cons.2 ⟨subd9_4_503, List.forall_mem_cons.2 ⟨subd9_4_504, List.forall_mem_cons.2 ⟨subd9_4_505, List.forall_mem_cons.2 ⟨subd9_4_506, List.forall_mem_cons.2 ⟨subd9_4_507, List.forall_mem_cons.2 ⟨subd9_4_508, List.forall_mem_cons.2 ⟨subd9_4_509, List.forall_mem_cons.2 ⟨subd9_4_510, List.forall_mem_cons.2 ⟨subd9_4_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_4_512 : subd9_4 [2, 0, -7] = true := by decide +kernel
theorem subd9_4_513 : subd9_4 [2, 0, -6] = true := by decide +kernel
theorem subd9_4_514 : subd9_4 [2, 0, -5] = true := by decide +kernel
theorem subd9_4_515 : subd9_4 [2, 0, -4] = true := by decide +kernel
theorem subd9_4_516 : subd9_4 [2, 0, -3] = true := by decide +kernel
theorem subd9_4_517 : subd9_4 [2, 0, -2] = true := by decide +kernel
theorem subd9_4_518 : subd9_4 [2, 0, -1] = true := by decide +kernel
theorem subd9_4_519 : subd9_4 [2, 0, 0] = true := by decide +kernel
theorem subd9_4_520 : subd9_4 [2, 0, 1] = true := by decide +kernel
theorem subd9_4_521 : subd9_4 [2, 0, 2] = true := by decide +kernel
theorem subd9_4_522 : subd9_4 [2, 0, 3] = true := by decide +kernel
theorem subd9_4_523 : subd9_4 [2, 0, 4] = true := by decide +kernel
theorem subd9_4_524 : subd9_4 [2, 0, 5] = true := by decide +kernel
theorem subd9_4_525 : subd9_4 [2, 0, 6] = true := by decide +kernel
theorem subd9_4_526 : subd9_4 [2, 0, 7] = true := by decide +kernel
theorem subd9_4_527 : subd9_4 [2, 0, 8] = true := by decide +kernel
theorem subd9_4_528 : subd9_4 [2, 1] = true := by decide +kernel
theorem sbd9_4_16 : ∀ q ∈ blkd9_4_16, subd9_4 q = true := by
  unfold blkd9_4_16
  exact List.forall_mem_cons.2 ⟨subd9_4_512, List.forall_mem_cons.2 ⟨subd9_4_513, List.forall_mem_cons.2 ⟨subd9_4_514, List.forall_mem_cons.2 ⟨subd9_4_515, List.forall_mem_cons.2 ⟨subd9_4_516, List.forall_mem_cons.2 ⟨subd9_4_517, List.forall_mem_cons.2 ⟨subd9_4_518, List.forall_mem_cons.2 ⟨subd9_4_519, List.forall_mem_cons.2 ⟨subd9_4_520, List.forall_mem_cons.2 ⟨subd9_4_521, List.forall_mem_cons.2 ⟨subd9_4_522, List.forall_mem_cons.2 ⟨subd9_4_523, List.forall_mem_cons.2 ⟨subd9_4_524, List.forall_mem_cons.2 ⟨subd9_4_525, List.forall_mem_cons.2 ⟨subd9_4_526, List.forall_mem_cons.2 ⟨subd9_4_527, List.forall_mem_cons.2 ⟨subd9_4_528, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
