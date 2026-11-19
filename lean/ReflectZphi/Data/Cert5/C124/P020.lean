import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_8_192 : subd6_8 [0, 0, -7] = true := by decide +kernel
theorem subd6_8_193 : subd6_8 [0, 0, -6] = true := by decide +kernel
theorem subd6_8_194 : subd6_8 [0, 0, -5] = true := by decide +kernel
theorem subd6_8_195 : subd6_8 [0, 0, -4] = true := by decide +kernel
theorem subd6_8_196 : subd6_8 [0, 0, -3] = true := by decide +kernel
theorem subd6_8_197 : subd6_8 [0, 0, -2] = true := by decide +kernel
theorem subd6_8_198 : subd6_8 [0, 0, -1] = true := by decide +kernel
theorem subd6_8_199 : subd6_8 [0, 0, 0] = true := by decide +kernel
theorem subd6_8_200 : subd6_8 [0, 0, 1] = true := by decide +kernel
theorem subd6_8_201 : subd6_8 [0, 0, 2] = true := by decide +kernel
theorem subd6_8_202 : subd6_8 [0, 0, 3] = true := by decide +kernel
theorem subd6_8_203 : subd6_8 [0, 0, 4] = true := by decide +kernel
theorem subd6_8_204 : subd6_8 [0, 0, 5] = true := by decide +kernel
theorem subd6_8_205 : subd6_8 [0, 0, 6] = true := by decide +kernel
theorem subd6_8_206 : subd6_8 [0, 0, 7] = true := by decide +kernel
theorem subd6_8_207 : subd6_8 [0, 0, 8] = true := by decide +kernel
theorem subd6_8_208 : subd6_8 [0, 0, 9] = true := by decide +kernel
theorem subd6_8_209 : subd6_8 [0, 0, 10] = true := by decide +kernel
theorem subd6_8_210 : subd6_8 [0, 0, 11] = true := by decide +kernel
theorem subd6_8_211 : subd6_8 [0, 0, 12] = true := by decide +kernel
theorem subd6_8_212 : subd6_8 [0, 0, 13] = true := by decide +kernel
theorem subd6_8_213 : subd6_8 [0, 0, 14] = true := by decide +kernel
theorem subd6_8_214 : subd6_8 [0, 0, 15] = true := by decide +kernel
theorem subd6_8_215 : subd6_8 [0, 0, 16] = true := by decide +kernel
theorem subd6_8_216 : subd6_8 [0, 0, 17] = true := by decide +kernel
theorem subd6_8_217 : subd6_8 [0, 0, 18] = true := by decide +kernel
theorem subd6_8_218 : subd6_8 [0, 0, 19] = true := by decide +kernel
theorem subd6_8_219 : subd6_8 [0, 0, 20] = true := by decide +kernel
theorem subd6_8_220 : subd6_8 [0, 0, 21] = true := by decide +kernel
theorem subd6_8_221 : subd6_8 [0, 0, 22] = true := by decide +kernel
theorem subd6_8_222 : subd6_8 [0, 0, 23] = true := by decide +kernel
theorem subd6_8_223 : subd6_8 [0, 0, 24] = true := by decide +kernel
theorem sbd6_8_6 : ∀ q ∈ blkd6_8_6, subd6_8 q = true := by
  unfold blkd6_8_6
  exact List.forall_mem_cons.2 ⟨subd6_8_192, List.forall_mem_cons.2 ⟨subd6_8_193, List.forall_mem_cons.2 ⟨subd6_8_194, List.forall_mem_cons.2 ⟨subd6_8_195, List.forall_mem_cons.2 ⟨subd6_8_196, List.forall_mem_cons.2 ⟨subd6_8_197, List.forall_mem_cons.2 ⟨subd6_8_198, List.forall_mem_cons.2 ⟨subd6_8_199, List.forall_mem_cons.2 ⟨subd6_8_200, List.forall_mem_cons.2 ⟨subd6_8_201, List.forall_mem_cons.2 ⟨subd6_8_202, List.forall_mem_cons.2 ⟨subd6_8_203, List.forall_mem_cons.2 ⟨subd6_8_204, List.forall_mem_cons.2 ⟨subd6_8_205, List.forall_mem_cons.2 ⟨subd6_8_206, List.forall_mem_cons.2 ⟨subd6_8_207, List.forall_mem_cons.2 ⟨subd6_8_208, List.forall_mem_cons.2 ⟨subd6_8_209, List.forall_mem_cons.2 ⟨subd6_8_210, List.forall_mem_cons.2 ⟨subd6_8_211, List.forall_mem_cons.2 ⟨subd6_8_212, List.forall_mem_cons.2 ⟨subd6_8_213, List.forall_mem_cons.2 ⟨subd6_8_214, List.forall_mem_cons.2 ⟨subd6_8_215, List.forall_mem_cons.2 ⟨subd6_8_216, List.forall_mem_cons.2 ⟨subd6_8_217, List.forall_mem_cons.2 ⟨subd6_8_218, List.forall_mem_cons.2 ⟨subd6_8_219, List.forall_mem_cons.2 ⟨subd6_8_220, List.forall_mem_cons.2 ⟨subd6_8_221, List.forall_mem_cons.2 ⟨subd6_8_222, List.forall_mem_cons.2 ⟨subd6_8_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_8_224 : subd6_8 [0, 0, 25] = true := by decide +kernel
theorem subd6_8_225 : subd6_8 [0, 0, 26] = true := by decide +kernel
theorem subd6_8_226 : subd6_8 [0, 0, 27] = true := by decide +kernel
theorem subd6_8_227 : subd6_8 [0, 0, 28] = true := by decide +kernel
theorem subd6_8_228 : subd6_8 [0, 0, 29] = true := by decide +kernel
theorem subd6_8_229 : subd6_8 [0, 0, 30] = true := by decide +kernel
theorem subd6_8_230 : subd6_8 [0, 0, 31] = true := by decide +kernel
theorem subd6_8_231 : subd6_8 [0, 0, 32] = true := by decide +kernel
theorem subd6_8_232 : subd6_8 [0, 0, 33] = true := by decide +kernel
theorem subd6_8_233 : subd6_8 [0, 0, 34] = true := by decide +kernel
theorem subd6_8_234 : subd6_8 [0, 0, 35] = true := by decide +kernel
theorem subd6_8_235 : subd6_8 [0, 0, 36] = true := by decide +kernel
theorem subd6_8_236 : subd6_8 [0, 0, 37] = true := by decide +kernel
theorem subd6_8_237 : subd6_8 [0, 0, 38] = true := by decide +kernel
theorem subd6_8_238 : subd6_8 [0, 0, 39] = true := by decide +kernel
theorem subd6_8_239 : subd6_8 [0, 0, 40] = true := by decide +kernel
theorem subd6_8_240 : subd6_8 [0, 0, 41] = true := by decide +kernel
theorem subd6_8_241 : subd6_8 [0, 0, 42] = true := by decide +kernel
theorem subd6_8_242 : subd6_8 [0, 1, -31] = true := by decide +kernel
theorem subd6_8_243 : subd6_8 [0, 1, -30] = true := by decide +kernel
theorem subd6_8_244 : subd6_8 [0, 1, -29] = true := by decide +kernel
theorem subd6_8_245 : subd6_8 [0, 1, -28] = true := by decide +kernel
theorem subd6_8_246 : subd6_8 [0, 1, -27] = true := by decide +kernel
theorem subd6_8_247 : subd6_8 [0, 1, -26] = true := by decide +kernel
theorem subd6_8_248 : subd6_8 [0, 1, -25] = true := by decide +kernel
theorem subd6_8_249 : subd6_8 [0, 1, -24] = true := by decide +kernel
theorem subd6_8_250 : subd6_8 [0, 1, -23] = true := by decide +kernel
theorem subd6_8_251 : subd6_8 [0, 1, -22] = true := by decide +kernel
theorem subd6_8_252 : subd6_8 [0, 1, -21] = true := by decide +kernel
theorem subd6_8_253 : subd6_8 [0, 1, -20] = true := by decide +kernel
theorem subd6_8_254 : subd6_8 [0, 1, -19] = true := by decide +kernel
theorem subd6_8_255 : subd6_8 [0, 1, -18] = true := by decide +kernel
theorem sbd6_8_7 : ∀ q ∈ blkd6_8_7, subd6_8 q = true := by
  unfold blkd6_8_7
  exact List.forall_mem_cons.2 ⟨subd6_8_224, List.forall_mem_cons.2 ⟨subd6_8_225, List.forall_mem_cons.2 ⟨subd6_8_226, List.forall_mem_cons.2 ⟨subd6_8_227, List.forall_mem_cons.2 ⟨subd6_8_228, List.forall_mem_cons.2 ⟨subd6_8_229, List.forall_mem_cons.2 ⟨subd6_8_230, List.forall_mem_cons.2 ⟨subd6_8_231, List.forall_mem_cons.2 ⟨subd6_8_232, List.forall_mem_cons.2 ⟨subd6_8_233, List.forall_mem_cons.2 ⟨subd6_8_234, List.forall_mem_cons.2 ⟨subd6_8_235, List.forall_mem_cons.2 ⟨subd6_8_236, List.forall_mem_cons.2 ⟨subd6_8_237, List.forall_mem_cons.2 ⟨subd6_8_238, List.forall_mem_cons.2 ⟨subd6_8_239, List.forall_mem_cons.2 ⟨subd6_8_240, List.forall_mem_cons.2 ⟨subd6_8_241, List.forall_mem_cons.2 ⟨subd6_8_242, List.forall_mem_cons.2 ⟨subd6_8_243, List.forall_mem_cons.2 ⟨subd6_8_244, List.forall_mem_cons.2 ⟨subd6_8_245, List.forall_mem_cons.2 ⟨subd6_8_246, List.forall_mem_cons.2 ⟨subd6_8_247, List.forall_mem_cons.2 ⟨subd6_8_248, List.forall_mem_cons.2 ⟨subd6_8_249, List.forall_mem_cons.2 ⟨subd6_8_250, List.forall_mem_cons.2 ⟨subd6_8_251, List.forall_mem_cons.2 ⟨subd6_8_252, List.forall_mem_cons.2 ⟨subd6_8_253, List.forall_mem_cons.2 ⟨subd6_8_254, List.forall_mem_cons.2 ⟨subd6_8_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_8_256 : subd6_8 [0, 1, -17] = true := by decide +kernel
theorem subd6_8_257 : subd6_8 [0, 1, -16] = true := by decide +kernel
theorem subd6_8_258 : subd6_8 [0, 1, -15] = true := by decide +kernel
theorem subd6_8_259 : subd6_8 [0, 1, -14] = true := by decide +kernel
theorem subd6_8_260 : subd6_8 [0, 1, -13] = true := by decide +kernel
theorem subd6_8_261 : subd6_8 [0, 1, -12] = true := by decide +kernel
theorem subd6_8_262 : subd6_8 [0, 1, -11] = true := by decide +kernel
theorem subd6_8_263 : subd6_8 [0, 1, -10] = true := by decide +kernel
theorem subd6_8_264 : subd6_8 [0, 1, -9] = true := by decide +kernel
theorem subd6_8_265 : subd6_8 [0, 1, -8] = true := by decide +kernel
theorem subd6_8_266 : subd6_8 [0, 1, -7] = true := by decide +kernel
theorem subd6_8_267 : subd6_8 [0, 1, -6] = true := by decide +kernel
theorem subd6_8_268 : subd6_8 [0, 1, -5] = true := by decide +kernel
theorem subd6_8_269 : subd6_8 [0, 1, -4] = true := by decide +kernel
theorem subd6_8_270 : subd6_8 [0, 1, -3] = true := by decide +kernel
theorem subd6_8_271 : subd6_8 [0, 1, -2] = true := by decide +kernel
theorem subd6_8_272 : subd6_8 [0, 1, -1] = true := by decide +kernel
theorem subd6_8_273 : subd6_8 [0, 1, 0] = true := by decide +kernel
theorem subd6_8_274 : subd6_8 [0, 1, 1] = true := by decide +kernel
theorem subd6_8_275 : subd6_8 [0, 1, 2] = true := by decide +kernel
theorem subd6_8_276 : subd6_8 [0, 1, 3] = true := by decide +kernel
theorem subd6_8_277 : subd6_8 [0, 1, 4] = true := by decide +kernel
theorem subd6_8_278 : subd6_8 [0, 1, 5] = true := by decide +kernel
theorem subd6_8_279 : subd6_8 [0, 1, 6] = true := by decide +kernel
theorem subd6_8_280 : subd6_8 [0, 1, 7] = true := by decide +kernel
theorem subd6_8_281 : subd6_8 [0, 1, 8] = true := by decide +kernel
theorem subd6_8_282 : subd6_8 [0, 1, 9] = true := by decide +kernel
theorem subd6_8_283 : subd6_8 [0, 1, 10] = true := by decide +kernel
theorem subd6_8_284 : subd6_8 [0, 1, 11] = true := by decide +kernel
theorem subd6_8_285 : subd6_8 [0, 1, 12] = true := by decide +kernel
theorem subd6_8_286 : subd6_8 [0, 1, 13] = true := by decide +kernel
theorem subd6_8_287 : subd6_8 [0, 1, 14] = true := by decide +kernel
theorem sbd6_8_8 : ∀ q ∈ blkd6_8_8, subd6_8 q = true := by
  unfold blkd6_8_8
  exact List.forall_mem_cons.2 ⟨subd6_8_256, List.forall_mem_cons.2 ⟨subd6_8_257, List.forall_mem_cons.2 ⟨subd6_8_258, List.forall_mem_cons.2 ⟨subd6_8_259, List.forall_mem_cons.2 ⟨subd6_8_260, List.forall_mem_cons.2 ⟨subd6_8_261, List.forall_mem_cons.2 ⟨subd6_8_262, List.forall_mem_cons.2 ⟨subd6_8_263, List.forall_mem_cons.2 ⟨subd6_8_264, List.forall_mem_cons.2 ⟨subd6_8_265, List.forall_mem_cons.2 ⟨subd6_8_266, List.forall_mem_cons.2 ⟨subd6_8_267, List.forall_mem_cons.2 ⟨subd6_8_268, List.forall_mem_cons.2 ⟨subd6_8_269, List.forall_mem_cons.2 ⟨subd6_8_270, List.forall_mem_cons.2 ⟨subd6_8_271, List.forall_mem_cons.2 ⟨subd6_8_272, List.forall_mem_cons.2 ⟨subd6_8_273, List.forall_mem_cons.2 ⟨subd6_8_274, List.forall_mem_cons.2 ⟨subd6_8_275, List.forall_mem_cons.2 ⟨subd6_8_276, List.forall_mem_cons.2 ⟨subd6_8_277, List.forall_mem_cons.2 ⟨subd6_8_278, List.forall_mem_cons.2 ⟨subd6_8_279, List.forall_mem_cons.2 ⟨subd6_8_280, List.forall_mem_cons.2 ⟨subd6_8_281, List.forall_mem_cons.2 ⟨subd6_8_282, List.forall_mem_cons.2 ⟨subd6_8_283, List.forall_mem_cons.2 ⟨subd6_8_284, List.forall_mem_cons.2 ⟨subd6_8_285, List.forall_mem_cons.2 ⟨subd6_8_286, List.forall_mem_cons.2 ⟨subd6_8_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C124
