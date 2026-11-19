import ReflectZphi.Data.Cert5.C129.Base

namespace ReflectZphi.Data.Cert5.C129

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_0_192 : subd8_0 [-2, 2, 6] = true := by decide +kernel
theorem subd8_0_193 : subd8_0 [-2, 2, 7] = true := by decide +kernel
theorem subd8_0_194 : subd8_0 [-2, 3] = true := by decide +kernel
theorem subd8_0_195 : subd8_0 [-2, 4] = true := by decide +kernel
theorem subd8_0_196 : subd8_0 [-2, 5] = true := by decide +kernel
theorem subd8_0_197 : subd8_0 [-2, 6] = true := by decide +kernel
theorem subd8_0_198 : subd8_0 [-1, -8] = true := by decide +kernel
theorem subd8_0_199 : subd8_0 [-1, -7] = true := by decide +kernel
theorem subd8_0_200 : subd8_0 [-1, -6] = true := by decide +kernel
theorem subd8_0_201 : subd8_0 [-1, -5] = true := by decide +kernel
theorem subd8_0_202 : subd8_0 [-1, -4] = true := by decide +kernel
theorem subd8_0_203 : subd8_0 [-1, -3, -9] = true := by decide +kernel
theorem subd8_0_204 : subd8_0 [-1, -3, -8] = true := by decide +kernel
theorem subd8_0_205 : subd8_0 [-1, -3, -7] = true := by decide +kernel
theorem subd8_0_206 : subd8_0 [-1, -3, -6] = true := by decide +kernel
theorem subd8_0_207 : subd8_0 [-1, -3, -5] = true := by decide +kernel
theorem subd8_0_208 : subd8_0 [-1, -3, -4] = true := by decide +kernel
theorem subd8_0_209 : subd8_0 [-1, -3, -3] = true := by decide +kernel
theorem subd8_0_210 : subd8_0 [-1, -3, -2] = true := by decide +kernel
theorem subd8_0_211 : subd8_0 [-1, -3, -1] = true := by decide +kernel
theorem subd8_0_212 : subd8_0 [-1, -3, 0] = true := by decide +kernel
theorem subd8_0_213 : subd8_0 [-1, -3, 1] = true := by decide +kernel
theorem subd8_0_214 : subd8_0 [-1, -3, 2] = true := by decide +kernel
theorem subd8_0_215 : subd8_0 [-1, -3, 3] = true := by decide +kernel
theorem subd8_0_216 : subd8_0 [-1, -3, 4] = true := by decide +kernel
theorem subd8_0_217 : subd8_0 [-1, -3, 5] = true := by decide +kernel
theorem subd8_0_218 : subd8_0 [-1, -2, -9] = true := by decide +kernel
theorem subd8_0_219 : subd8_0 [-1, -2, -8] = true := by decide +kernel
theorem subd8_0_220 : subd8_0 [-1, -2, -7] = true := by decide +kernel
theorem subd8_0_221 : subd8_0 [-1, -2, -6] = true := by decide +kernel
theorem subd8_0_222 : subd8_0 [-1, -2, -5] = true := by decide +kernel
theorem subd8_0_223 : subd8_0 [-1, -2, -4] = true := by decide +kernel
theorem sbd8_0_6 : ∀ q ∈ blkd8_0_6, subd8_0 q = true := by
  unfold blkd8_0_6
  exact List.forall_mem_cons.2 ⟨subd8_0_192, List.forall_mem_cons.2 ⟨subd8_0_193, List.forall_mem_cons.2 ⟨subd8_0_194, List.forall_mem_cons.2 ⟨subd8_0_195, List.forall_mem_cons.2 ⟨subd8_0_196, List.forall_mem_cons.2 ⟨subd8_0_197, List.forall_mem_cons.2 ⟨subd8_0_198, List.forall_mem_cons.2 ⟨subd8_0_199, List.forall_mem_cons.2 ⟨subd8_0_200, List.forall_mem_cons.2 ⟨subd8_0_201, List.forall_mem_cons.2 ⟨subd8_0_202, List.forall_mem_cons.2 ⟨subd8_0_203, List.forall_mem_cons.2 ⟨subd8_0_204, List.forall_mem_cons.2 ⟨subd8_0_205, List.forall_mem_cons.2 ⟨subd8_0_206, List.forall_mem_cons.2 ⟨subd8_0_207, List.forall_mem_cons.2 ⟨subd8_0_208, List.forall_mem_cons.2 ⟨subd8_0_209, List.forall_mem_cons.2 ⟨subd8_0_210, List.forall_mem_cons.2 ⟨subd8_0_211, List.forall_mem_cons.2 ⟨subd8_0_212, List.forall_mem_cons.2 ⟨subd8_0_213, List.forall_mem_cons.2 ⟨subd8_0_214, List.forall_mem_cons.2 ⟨subd8_0_215, List.forall_mem_cons.2 ⟨subd8_0_216, List.forall_mem_cons.2 ⟨subd8_0_217, List.forall_mem_cons.2 ⟨subd8_0_218, List.forall_mem_cons.2 ⟨subd8_0_219, List.forall_mem_cons.2 ⟨subd8_0_220, List.forall_mem_cons.2 ⟨subd8_0_221, List.forall_mem_cons.2 ⟨subd8_0_222, List.forall_mem_cons.2 ⟨subd8_0_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_224 : subd8_0 [-1, -2, -3] = true := by decide +kernel
theorem subd8_0_225 : subd8_0 [-1, -2, -2] = true := by decide +kernel
theorem subd8_0_226 : subd8_0 [-1, -2, -1] = true := by decide +kernel
theorem subd8_0_227 : subd8_0 [-1, -2, 0] = true := by decide +kernel
theorem subd8_0_228 : subd8_0 [-1, -2, 1] = true := by decide +kernel
theorem subd8_0_229 : subd8_0 [-1, -2, 2] = true := by decide +kernel
theorem subd8_0_230 : subd8_0 [-1, -2, 3] = true := by decide +kernel
theorem subd8_0_231 : subd8_0 [-1, -2, 4] = true := by decide +kernel
theorem subd8_0_232 : subd8_0 [-1, -2, 5] = true := by decide +kernel
theorem subd8_0_233 : subd8_0 [-1, -1, -9] = true := by decide +kernel
theorem subd8_0_234 : subd8_0 [-1, -1, -8] = true := by decide +kernel
theorem subd8_0_235 : subd8_0 [-1, -1, -7] = true := by decide +kernel
theorem subd8_0_236 : subd8_0 [-1, -1, -6] = true := by decide +kernel
theorem subd8_0_237 : subd8_0 [-1, -1, -5] = true := by decide +kernel
theorem subd8_0_238 : subd8_0 [-1, -1, -4] = true := by decide +kernel
theorem subd8_0_239 : subd8_0 [-1, -1, -3] = true := by decide +kernel
theorem subd8_0_240 : subd8_0 [-1, -1, -2] = true := by decide +kernel
theorem subd8_0_241 : subd8_0 [-1, -1, -1] = true := by decide +kernel
theorem subd8_0_242 : subd8_0 [-1, -1, 0] = true := by decide +kernel
theorem subd8_0_243 : subd8_0 [-1, -1, 1] = true := by decide +kernel
theorem subd8_0_244 : subd8_0 [-1, -1, 2] = true := by decide +kernel
theorem subd8_0_245 : subd8_0 [-1, -1, 3] = true := by decide +kernel
theorem subd8_0_246 : subd8_0 [-1, -1, 4] = true := by decide +kernel
theorem subd8_0_247 : subd8_0 [-1, -1, 5] = true := by decide +kernel
theorem subd8_0_248 : subd8_0 [-1, -1, 6] = true := by decide +kernel
theorem subd8_0_249 : subd8_0 [-1, 0, -8] = true := by decide +kernel
theorem subd8_0_250 : subd8_0 [-1, 0, -7] = true := by decide +kernel
theorem subd8_0_251 : subd8_0 [-1, 0, -6] = true := by decide +kernel
theorem subd8_0_252 : subd8_0 [-1, 0, -5] = true := by decide +kernel
theorem subd8_0_253 : subd8_0 [-1, 0, -4] = true := by decide +kernel
theorem subd8_0_254 : subd8_0 [-1, 0, -3] = true := by decide +kernel
theorem subd8_0_255 : subd8_0 [-1, 0, -2] = true := by decide +kernel
theorem sbd8_0_7 : ∀ q ∈ blkd8_0_7, subd8_0 q = true := by
  unfold blkd8_0_7
  exact List.forall_mem_cons.2 ⟨subd8_0_224, List.forall_mem_cons.2 ⟨subd8_0_225, List.forall_mem_cons.2 ⟨subd8_0_226, List.forall_mem_cons.2 ⟨subd8_0_227, List.forall_mem_cons.2 ⟨subd8_0_228, List.forall_mem_cons.2 ⟨subd8_0_229, List.forall_mem_cons.2 ⟨subd8_0_230, List.forall_mem_cons.2 ⟨subd8_0_231, List.forall_mem_cons.2 ⟨subd8_0_232, List.forall_mem_cons.2 ⟨subd8_0_233, List.forall_mem_cons.2 ⟨subd8_0_234, List.forall_mem_cons.2 ⟨subd8_0_235, List.forall_mem_cons.2 ⟨subd8_0_236, List.forall_mem_cons.2 ⟨subd8_0_237, List.forall_mem_cons.2 ⟨subd8_0_238, List.forall_mem_cons.2 ⟨subd8_0_239, List.forall_mem_cons.2 ⟨subd8_0_240, List.forall_mem_cons.2 ⟨subd8_0_241, List.forall_mem_cons.2 ⟨subd8_0_242, List.forall_mem_cons.2 ⟨subd8_0_243, List.forall_mem_cons.2 ⟨subd8_0_244, List.forall_mem_cons.2 ⟨subd8_0_245, List.forall_mem_cons.2 ⟨subd8_0_246, List.forall_mem_cons.2 ⟨subd8_0_247, List.forall_mem_cons.2 ⟨subd8_0_248, List.forall_mem_cons.2 ⟨subd8_0_249, List.forall_mem_cons.2 ⟨subd8_0_250, List.forall_mem_cons.2 ⟨subd8_0_251, List.forall_mem_cons.2 ⟨subd8_0_252, List.forall_mem_cons.2 ⟨subd8_0_253, List.forall_mem_cons.2 ⟨subd8_0_254, List.forall_mem_cons.2 ⟨subd8_0_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_256 : subd8_0 [-1, 0, -1] = true := by decide +kernel
theorem subd8_0_257 : subd8_0 [-1, 0, 0] = true := by decide +kernel
theorem subd8_0_258 : subd8_0 [-1, 0, 1] = true := by decide +kernel
theorem subd8_0_259 : subd8_0 [-1, 0, 2] = true := by decide +kernel
theorem subd8_0_260 : subd8_0 [-1, 0, 3] = true := by decide +kernel
theorem subd8_0_261 : subd8_0 [-1, 0, 4] = true := by decide +kernel
theorem subd8_0_262 : subd8_0 [-1, 0, 5] = true := by decide +kernel
theorem subd8_0_263 : subd8_0 [-1, 0, 6] = true := by decide +kernel
theorem subd8_0_264 : subd8_0 [-1, 0, 7] = true := by decide +kernel
theorem subd8_0_265 : subd8_0 [-1, 1, -8] = true := by decide +kernel
theorem subd8_0_266 : subd8_0 [-1, 1, -7] = true := by decide +kernel
theorem subd8_0_267 : subd8_0 [-1, 1, -6] = true := by decide +kernel
theorem subd8_0_268 : subd8_0 [-1, 1, -5] = true := by decide +kernel
theorem subd8_0_269 : subd8_0 [-1, 1, -4] = true := by decide +kernel
theorem subd8_0_270 : subd8_0 [-1, 1, -3] = true := by decide +kernel
theorem subd8_0_271 : subd8_0 [-1, 1, -2] = true := by decide +kernel
theorem subd8_0_272 : subd8_0 [-1, 1, -1] = true := by decide +kernel
theorem subd8_0_273 : subd8_0 [-1, 1, 0] = true := by decide +kernel
theorem subd8_0_274 : subd8_0 [-1, 1, 1] = true := by decide +kernel
theorem subd8_0_275 : subd8_0 [-1, 1, 2] = true := by decide +kernel
theorem subd8_0_276 : subd8_0 [-1, 1, 3] = true := by decide +kernel
theorem subd8_0_277 : subd8_0 [-1, 1, 4] = true := by decide +kernel
theorem subd8_0_278 : subd8_0 [-1, 1, 5] = true := by decide +kernel
theorem subd8_0_279 : subd8_0 [-1, 1, 6] = true := by decide +kernel
theorem subd8_0_280 : subd8_0 [-1, 1, 7] = true := by decide +kernel
theorem subd8_0_281 : subd8_0 [-1, 2, -7] = true := by decide +kernel
theorem subd8_0_282 : subd8_0 [-1, 2, -6] = true := by decide +kernel
theorem subd8_0_283 : subd8_0 [-1, 2, -5] = true := by decide +kernel
theorem subd8_0_284 : subd8_0 [-1, 2, -4] = true := by decide +kernel
theorem subd8_0_285 : subd8_0 [-1, 2, -3] = true := by decide +kernel
theorem subd8_0_286 : subd8_0 [-1, 2, -2] = true := by decide +kernel
theorem subd8_0_287 : subd8_0 [-1, 2, -1] = true := by decide +kernel
theorem sbd8_0_8 : ∀ q ∈ blkd8_0_8, subd8_0 q = true := by
  unfold blkd8_0_8
  exact List.forall_mem_cons.2 ⟨subd8_0_256, List.forall_mem_cons.2 ⟨subd8_0_257, List.forall_mem_cons.2 ⟨subd8_0_258, List.forall_mem_cons.2 ⟨subd8_0_259, List.forall_mem_cons.2 ⟨subd8_0_260, List.forall_mem_cons.2 ⟨subd8_0_261, List.forall_mem_cons.2 ⟨subd8_0_262, List.forall_mem_cons.2 ⟨subd8_0_263, List.forall_mem_cons.2 ⟨subd8_0_264, List.forall_mem_cons.2 ⟨subd8_0_265, List.forall_mem_cons.2 ⟨subd8_0_266, List.forall_mem_cons.2 ⟨subd8_0_267, List.forall_mem_cons.2 ⟨subd8_0_268, List.forall_mem_cons.2 ⟨subd8_0_269, List.forall_mem_cons.2 ⟨subd8_0_270, List.forall_mem_cons.2 ⟨subd8_0_271, List.forall_mem_cons.2 ⟨subd8_0_272, List.forall_mem_cons.2 ⟨subd8_0_273, List.forall_mem_cons.2 ⟨subd8_0_274, List.forall_mem_cons.2 ⟨subd8_0_275, List.forall_mem_cons.2 ⟨subd8_0_276, List.forall_mem_cons.2 ⟨subd8_0_277, List.forall_mem_cons.2 ⟨subd8_0_278, List.forall_mem_cons.2 ⟨subd8_0_279, List.forall_mem_cons.2 ⟨subd8_0_280, List.forall_mem_cons.2 ⟨subd8_0_281, List.forall_mem_cons.2 ⟨subd8_0_282, List.forall_mem_cons.2 ⟨subd8_0_283, List.forall_mem_cons.2 ⟨subd8_0_284, List.forall_mem_cons.2 ⟨subd8_0_285, List.forall_mem_cons.2 ⟨subd8_0_286, List.forall_mem_cons.2 ⟨subd8_0_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_288 : subd8_0 [-1, 2, 0] = true := by decide +kernel
theorem subd8_0_289 : subd8_0 [-1, 2, 1] = true := by decide +kernel
theorem subd8_0_290 : subd8_0 [-1, 2, 2] = true := by decide +kernel
theorem subd8_0_291 : subd8_0 [-1, 2, 3] = true := by decide +kernel
theorem subd8_0_292 : subd8_0 [-1, 2, 4] = true := by decide +kernel
theorem subd8_0_293 : subd8_0 [-1, 2, 5] = true := by decide +kernel
theorem subd8_0_294 : subd8_0 [-1, 2, 6] = true := by decide +kernel
theorem subd8_0_295 : subd8_0 [-1, 2, 7] = true := by decide +kernel
theorem subd8_0_296 : subd8_0 [-1, 3, -6] = true := by decide +kernel
theorem subd8_0_297 : subd8_0 [-1, 3, -5] = true := by decide +kernel
theorem subd8_0_298 : subd8_0 [-1, 3, -4] = true := by decide +kernel
theorem subd8_0_299 : subd8_0 [-1, 3, -3] = true := by decide +kernel
theorem subd8_0_300 : subd8_0 [-1, 3, -2] = true := by decide +kernel
theorem subd8_0_301 : subd8_0 [-1, 3, -1] = true := by decide +kernel
theorem subd8_0_302 : subd8_0 [-1, 3, 0] = true := by decide +kernel
theorem subd8_0_303 : subd8_0 [-1, 3, 1] = true := by decide +kernel
theorem subd8_0_304 : subd8_0 [-1, 3, 2] = true := by decide +kernel
theorem subd8_0_305 : subd8_0 [-1, 3, 3] = true := by decide +kernel
theorem subd8_0_306 : subd8_0 [-1, 3, 4] = true := by decide +kernel
theorem subd8_0_307 : subd8_0 [-1, 3, 5] = true := by decide +kernel
theorem subd8_0_308 : subd8_0 [-1, 3, 6] = true := by decide +kernel
theorem subd8_0_309 : subd8_0 [-1, 3, 7] = true := by decide +kernel
theorem subd8_0_310 : subd8_0 [-1, 4] = true := by decide +kernel
theorem subd8_0_311 : subd8_0 [-1, 5] = true := by decide +kernel
theorem subd8_0_312 : subd8_0 [-1, 6] = true := by decide +kernel
theorem subd8_0_313 : subd8_0 [0, -8] = true := by decide +kernel
theorem subd8_0_314 : subd8_0 [0, -7] = true := by decide +kernel
theorem subd8_0_315 : subd8_0 [0, -6] = true := by decide +kernel
theorem subd8_0_316 : subd8_0 [0, -5] = true := by decide +kernel
theorem subd8_0_317 : subd8_0 [0, -4] = true := by decide +kernel
theorem subd8_0_318 : subd8_0 [0, -3, -9] = true := by decide +kernel
theorem subd8_0_319 : subd8_0 [0, -3, -8] = true := by decide +kernel
theorem sbd8_0_9 : ∀ q ∈ blkd8_0_9, subd8_0 q = true := by
  unfold blkd8_0_9
  exact List.forall_mem_cons.2 ⟨subd8_0_288, List.forall_mem_cons.2 ⟨subd8_0_289, List.forall_mem_cons.2 ⟨subd8_0_290, List.forall_mem_cons.2 ⟨subd8_0_291, List.forall_mem_cons.2 ⟨subd8_0_292, List.forall_mem_cons.2 ⟨subd8_0_293, List.forall_mem_cons.2 ⟨subd8_0_294, List.forall_mem_cons.2 ⟨subd8_0_295, List.forall_mem_cons.2 ⟨subd8_0_296, List.forall_mem_cons.2 ⟨subd8_0_297, List.forall_mem_cons.2 ⟨subd8_0_298, List.forall_mem_cons.2 ⟨subd8_0_299, List.forall_mem_cons.2 ⟨subd8_0_300, List.forall_mem_cons.2 ⟨subd8_0_301, List.forall_mem_cons.2 ⟨subd8_0_302, List.forall_mem_cons.2 ⟨subd8_0_303, List.forall_mem_cons.2 ⟨subd8_0_304, List.forall_mem_cons.2 ⟨subd8_0_305, List.forall_mem_cons.2 ⟨subd8_0_306, List.forall_mem_cons.2 ⟨subd8_0_307, List.forall_mem_cons.2 ⟨subd8_0_308, List.forall_mem_cons.2 ⟨subd8_0_309, List.forall_mem_cons.2 ⟨subd8_0_310, List.forall_mem_cons.2 ⟨subd8_0_311, List.forall_mem_cons.2 ⟨subd8_0_312, List.forall_mem_cons.2 ⟨subd8_0_313, List.forall_mem_cons.2 ⟨subd8_0_314, List.forall_mem_cons.2 ⟨subd8_0_315, List.forall_mem_cons.2 ⟨subd8_0_316, List.forall_mem_cons.2 ⟨subd8_0_317, List.forall_mem_cons.2 ⟨subd8_0_318, List.forall_mem_cons.2 ⟨subd8_0_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_320 : subd8_0 [0, -3, -7] = true := by decide +kernel
theorem subd8_0_321 : subd8_0 [0, -3, -6] = true := by decide +kernel
theorem subd8_0_322 : subd8_0 [0, -3, -5] = true := by decide +kernel
theorem subd8_0_323 : subd8_0 [0, -3, -4] = true := by decide +kernel
theorem subd8_0_324 : subd8_0 [0, -3, -3] = true := by decide +kernel
theorem subd8_0_325 : subd8_0 [0, -3, -2] = true := by decide +kernel
theorem subd8_0_326 : subd8_0 [0, -3, -1] = true := by decide +kernel
theorem subd8_0_327 : subd8_0 [0, -3, 0] = true := by decide +kernel
theorem subd8_0_328 : subd8_0 [0, -3, 1] = true := by decide +kernel
theorem subd8_0_329 : subd8_0 [0, -3, 2] = true := by decide +kernel
theorem subd8_0_330 : subd8_0 [0, -3, 3] = true := by decide +kernel
theorem subd8_0_331 : subd8_0 [0, -3, 4] = true := by decide +kernel
theorem subd8_0_332 : subd8_0 [0, -3, 5] = true := by decide +kernel
theorem subd8_0_333 : subd8_0 [0, -2, -9] = true := by decide +kernel
theorem subd8_0_334 : subd8_0 [0, -2, -8] = true := by decide +kernel
theorem subd8_0_335 : subd8_0 [0, -2, -7] = true := by decide +kernel
theorem subd8_0_336 : subd8_0 [0, -2, -6] = true := by decide +kernel
theorem subd8_0_337 : subd8_0 [0, -2, -5] = true := by decide +kernel
theorem subd8_0_338 : subd8_0 [0, -2, -4] = true := by decide +kernel
theorem subd8_0_339 : subd8_0 [0, -2, -3] = true := by decide +kernel
theorem subd8_0_340 : subd8_0 [0, -2, -2] = true := by decide +kernel
theorem subd8_0_341 : subd8_0 [0, -2, -1] = true := by decide +kernel
theorem subd8_0_342 : subd8_0 [0, -2, 0] = true := by decide +kernel
theorem subd8_0_343 : subd8_0 [0, -2, 1] = true := by decide +kernel
theorem subd8_0_344 : subd8_0 [0, -2, 2] = true := by decide +kernel
theorem subd8_0_345 : subd8_0 [0, -2, 3] = true := by decide +kernel
theorem subd8_0_346 : subd8_0 [0, -2, 4] = true := by decide +kernel
theorem subd8_0_347 : subd8_0 [0, -2, 5] = true := by decide +kernel
theorem subd8_0_348 : subd8_0 [0, -2, 6] = true := by decide +kernel
theorem subd8_0_349 : subd8_0 [0, -1, -9] = true := by decide +kernel
theorem subd8_0_350 : subd8_0 [0, -1, -8] = true := by decide +kernel
theorem subd8_0_351 : subd8_0 [0, -1, -7] = true := by decide +kernel
theorem sbd8_0_10 : ∀ q ∈ blkd8_0_10, subd8_0 q = true := by
  unfold blkd8_0_10
  exact List.forall_mem_cons.2 ⟨subd8_0_320, List.forall_mem_cons.2 ⟨subd8_0_321, List.forall_mem_cons.2 ⟨subd8_0_322, List.forall_mem_cons.2 ⟨subd8_0_323, List.forall_mem_cons.2 ⟨subd8_0_324, List.forall_mem_cons.2 ⟨subd8_0_325, List.forall_mem_cons.2 ⟨subd8_0_326, List.forall_mem_cons.2 ⟨subd8_0_327, List.forall_mem_cons.2 ⟨subd8_0_328, List.forall_mem_cons.2 ⟨subd8_0_329, List.forall_mem_cons.2 ⟨subd8_0_330, List.forall_mem_cons.2 ⟨subd8_0_331, List.forall_mem_cons.2 ⟨subd8_0_332, List.forall_mem_cons.2 ⟨subd8_0_333, List.forall_mem_cons.2 ⟨subd8_0_334, List.forall_mem_cons.2 ⟨subd8_0_335, List.forall_mem_cons.2 ⟨subd8_0_336, List.forall_mem_cons.2 ⟨subd8_0_337, List.forall_mem_cons.2 ⟨subd8_0_338, List.forall_mem_cons.2 ⟨subd8_0_339, List.forall_mem_cons.2 ⟨subd8_0_340, List.forall_mem_cons.2 ⟨subd8_0_341, List.forall_mem_cons.2 ⟨subd8_0_342, List.forall_mem_cons.2 ⟨subd8_0_343, List.forall_mem_cons.2 ⟨subd8_0_344, List.forall_mem_cons.2 ⟨subd8_0_345, List.forall_mem_cons.2 ⟨subd8_0_346, List.forall_mem_cons.2 ⟨subd8_0_347, List.forall_mem_cons.2 ⟨subd8_0_348, List.forall_mem_cons.2 ⟨subd8_0_349, List.forall_mem_cons.2 ⟨subd8_0_350, List.forall_mem_cons.2 ⟨subd8_0_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_352 : subd8_0 [0, -1, -6] = true := by decide +kernel
theorem subd8_0_353 : subd8_0 [0, -1, -5] = true := by decide +kernel
theorem subd8_0_354 : subd8_0 [0, -1, -4] = true := by decide +kernel
theorem subd8_0_355 : subd8_0 [0, -1, -3] = true := by decide +kernel
theorem subd8_0_356 : subd8_0 [0, -1, -2] = true := by decide +kernel
theorem subd8_0_357 : subd8_0 [0, -1, -1] = true := by decide +kernel
theorem subd8_0_358 : subd8_0 [0, -1, 0] = true := by decide +kernel
theorem subd8_0_359 : subd8_0 [0, -1, 1] = true := by decide +kernel
theorem subd8_0_360 : subd8_0 [0, -1, 2] = true := by decide +kernel
theorem subd8_0_361 : subd8_0 [0, -1, 3] = true := by decide +kernel
theorem subd8_0_362 : subd8_0 [0, -1, 4] = true := by decide +kernel
theorem subd8_0_363 : subd8_0 [0, -1, 5] = true := by decide +kernel
theorem subd8_0_364 : subd8_0 [0, -1, 6] = true := by decide +kernel
theorem subd8_0_365 : subd8_0 [0, -1, 7] = true := by decide +kernel
theorem subd8_0_366 : subd8_0 [0, 0, -8] = true := by decide +kernel
theorem subd8_0_367 : subd8_0 [0, 0, -7] = true := by decide +kernel
theorem subd8_0_368 : subd8_0 [0, 0, -6] = true := by decide +kernel
theorem subd8_0_369 : subd8_0 [0, 0, -5] = true := by decide +kernel
theorem subd8_0_370 : subd8_0 [0, 0, -4] = true := by decide +kernel
theorem subd8_0_371 : subd8_0 [0, 0, -3] = true := by decide +kernel
theorem subd8_0_372 : subd8_0 [0, 0, -2] = true := by decide +kernel
theorem subd8_0_373 : subd8_0 [0, 0, -1] = true := by decide +kernel
theorem subd8_0_374 : subd8_0 [0, 0, 0] = true := by decide +kernel
theorem subd8_0_375 : subd8_0 [0, 0, 1] = true := by decide +kernel
theorem subd8_0_376 : subd8_0 [0, 0, 2] = true := by decide +kernel
theorem subd8_0_377 : subd8_0 [0, 0, 3] = true := by decide +kernel
theorem subd8_0_378 : subd8_0 [0, 0, 4] = true := by decide +kernel
theorem subd8_0_379 : subd8_0 [0, 0, 5] = true := by decide +kernel
theorem subd8_0_380 : subd8_0 [0, 0, 6] = true := by decide +kernel
theorem subd8_0_381 : subd8_0 [0, 0, 7] = true := by decide +kernel
theorem subd8_0_382 : subd8_0 [0, 1, -8] = true := by decide +kernel
theorem subd8_0_383 : subd8_0 [0, 1, -7] = true := by decide +kernel
theorem sbd8_0_11 : ∀ q ∈ blkd8_0_11, subd8_0 q = true := by
  unfold blkd8_0_11
  exact List.forall_mem_cons.2 ⟨subd8_0_352, List.forall_mem_cons.2 ⟨subd8_0_353, List.forall_mem_cons.2 ⟨subd8_0_354, List.forall_mem_cons.2 ⟨subd8_0_355, List.forall_mem_cons.2 ⟨subd8_0_356, List.forall_mem_cons.2 ⟨subd8_0_357, List.forall_mem_cons.2 ⟨subd8_0_358, List.forall_mem_cons.2 ⟨subd8_0_359, List.forall_mem_cons.2 ⟨subd8_0_360, List.forall_mem_cons.2 ⟨subd8_0_361, List.forall_mem_cons.2 ⟨subd8_0_362, List.forall_mem_cons.2 ⟨subd8_0_363, List.forall_mem_cons.2 ⟨subd8_0_364, List.forall_mem_cons.2 ⟨subd8_0_365, List.forall_mem_cons.2 ⟨subd8_0_366, List.forall_mem_cons.2 ⟨subd8_0_367, List.forall_mem_cons.2 ⟨subd8_0_368, List.forall_mem_cons.2 ⟨subd8_0_369, List.forall_mem_cons.2 ⟨subd8_0_370, List.forall_mem_cons.2 ⟨subd8_0_371, List.forall_mem_cons.2 ⟨subd8_0_372, List.forall_mem_cons.2 ⟨subd8_0_373, List.forall_mem_cons.2 ⟨subd8_0_374, List.forall_mem_cons.2 ⟨subd8_0_375, List.forall_mem_cons.2 ⟨subd8_0_376, List.forall_mem_cons.2 ⟨subd8_0_377, List.forall_mem_cons.2 ⟨subd8_0_378, List.forall_mem_cons.2 ⟨subd8_0_379, List.forall_mem_cons.2 ⟨subd8_0_380, List.forall_mem_cons.2 ⟨subd8_0_381, List.forall_mem_cons.2 ⟨subd8_0_382, List.forall_mem_cons.2 ⟨subd8_0_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_384 : subd8_0 [0, 1, -6] = true := by decide +kernel
theorem subd8_0_385 : subd8_0 [0, 1, -5] = true := by decide +kernel
theorem subd8_0_386 : subd8_0 [0, 1, -4] = true := by decide +kernel
theorem subd8_0_387 : subd8_0 [0, 1, -3] = true := by decide +kernel
theorem subd8_0_388 : subd8_0 [0, 1, -2] = true := by decide +kernel
theorem subd8_0_389 : subd8_0 [0, 1, -1] = true := by decide +kernel
theorem subd8_0_390 : subd8_0 [0, 1, 0] = true := by decide +kernel
theorem subd8_0_391 : subd8_0 [0, 1, 1] = true := by decide +kernel
theorem subd8_0_392 : subd8_0 [0, 1, 2] = true := by decide +kernel
theorem subd8_0_393 : subd8_0 [0, 1, 3] = true := by decide +kernel
theorem subd8_0_394 : subd8_0 [0, 1, 4] = true := by decide +kernel
theorem subd8_0_395 : subd8_0 [0, 1, 5] = true := by decide +kernel
theorem subd8_0_396 : subd8_0 [0, 1, 6] = true := by decide +kernel
theorem subd8_0_397 : subd8_0 [0, 1, 7] = true := by decide +kernel
theorem subd8_0_398 : subd8_0 [0, 1, 8] = true := by decide +kernel
theorem subd8_0_399 : subd8_0 [0, 2, -7] = true := by decide +kernel
theorem subd8_0_400 : subd8_0 [0, 2, -6] = true := by decide +kernel
theorem subd8_0_401 : subd8_0 [0, 2, -5] = true := by decide +kernel
theorem subd8_0_402 : subd8_0 [0, 2, -4] = true := by decide +kernel
theorem subd8_0_403 : subd8_0 [0, 2, -3] = true := by decide +kernel
theorem subd8_0_404 : subd8_0 [0, 2, -2] = true := by decide +kernel
theorem subd8_0_405 : subd8_0 [0, 2, -1] = true := by decide +kernel
theorem subd8_0_406 : subd8_0 [0, 2, 0] = true := by decide +kernel
theorem subd8_0_407 : subd8_0 [0, 2, 1] = true := by decide +kernel
theorem subd8_0_408 : subd8_0 [0, 2, 2] = true := by decide +kernel
theorem subd8_0_409 : subd8_0 [0, 2, 3] = true := by decide +kernel
theorem subd8_0_410 : subd8_0 [0, 2, 4] = true := by decide +kernel
theorem subd8_0_411 : subd8_0 [0, 2, 5] = true := by decide +kernel
theorem subd8_0_412 : subd8_0 [0, 2, 6] = true := by decide +kernel
theorem subd8_0_413 : subd8_0 [0, 2, 7] = true := by decide +kernel
theorem subd8_0_414 : subd8_0 [0, 2, 8] = true := by decide +kernel
theorem subd8_0_415 : subd8_0 [0, 3, -6] = true := by decide +kernel
theorem sbd8_0_12 : ∀ q ∈ blkd8_0_12, subd8_0 q = true := by
  unfold blkd8_0_12
  exact List.forall_mem_cons.2 ⟨subd8_0_384, List.forall_mem_cons.2 ⟨subd8_0_385, List.forall_mem_cons.2 ⟨subd8_0_386, List.forall_mem_cons.2 ⟨subd8_0_387, List.forall_mem_cons.2 ⟨subd8_0_388, List.forall_mem_cons.2 ⟨subd8_0_389, List.forall_mem_cons.2 ⟨subd8_0_390, List.forall_mem_cons.2 ⟨subd8_0_391, List.forall_mem_cons.2 ⟨subd8_0_392, List.forall_mem_cons.2 ⟨subd8_0_393, List.forall_mem_cons.2 ⟨subd8_0_394, List.forall_mem_cons.2 ⟨subd8_0_395, List.forall_mem_cons.2 ⟨subd8_0_396, List.forall_mem_cons.2 ⟨subd8_0_397, List.forall_mem_cons.2 ⟨subd8_0_398, List.forall_mem_cons.2 ⟨subd8_0_399, List.forall_mem_cons.2 ⟨subd8_0_400, List.forall_mem_cons.2 ⟨subd8_0_401, List.forall_mem_cons.2 ⟨subd8_0_402, List.forall_mem_cons.2 ⟨subd8_0_403, List.forall_mem_cons.2 ⟨subd8_0_404, List.forall_mem_cons.2 ⟨subd8_0_405, List.forall_mem_cons.2 ⟨subd8_0_406, List.forall_mem_cons.2 ⟨subd8_0_407, List.forall_mem_cons.2 ⟨subd8_0_408, List.forall_mem_cons.2 ⟨subd8_0_409, List.forall_mem_cons.2 ⟨subd8_0_410, List.forall_mem_cons.2 ⟨subd8_0_411, List.forall_mem_cons.2 ⟨subd8_0_412, List.forall_mem_cons.2 ⟨subd8_0_413, List.forall_mem_cons.2 ⟨subd8_0_414, List.forall_mem_cons.2 ⟨subd8_0_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_416 : subd8_0 [0, 3, -5] = true := by decide +kernel
theorem subd8_0_417 : subd8_0 [0, 3, -4] = true := by decide +kernel
theorem subd8_0_418 : subd8_0 [0, 3, -3] = true := by decide +kernel
theorem subd8_0_419 : subd8_0 [0, 3, -2] = true := by decide +kernel
theorem subd8_0_420 : subd8_0 [0, 3, -1] = true := by decide +kernel
theorem subd8_0_421 : subd8_0 [0, 3, 0] = true := by decide +kernel
theorem subd8_0_422 : subd8_0 [0, 3, 1] = true := by decide +kernel
theorem subd8_0_423 : subd8_0 [0, 3, 2] = true := by decide +kernel
theorem subd8_0_424 : subd8_0 [0, 3, 3] = true := by decide +kernel
theorem subd8_0_425 : subd8_0 [0, 3, 4] = true := by decide +kernel
theorem subd8_0_426 : subd8_0 [0, 3, 5] = true := by decide +kernel
theorem subd8_0_427 : subd8_0 [0, 3, 6] = true := by decide +kernel
theorem subd8_0_428 : subd8_0 [0, 3, 7] = true := by decide +kernel
theorem subd8_0_429 : subd8_0 [0, 3, 8] = true := by decide +kernel
theorem subd8_0_430 : subd8_0 [0, 4] = true := by decide +kernel
theorem subd8_0_431 : subd8_0 [0, 5] = true := by decide +kernel
theorem subd8_0_432 : subd8_0 [0, 6] = true := by decide +kernel
theorem subd8_0_433 : subd8_0 [0, 7] = true := by decide +kernel
theorem subd8_0_434 : subd8_0 [1, -7] = true := by decide +kernel
theorem subd8_0_435 : subd8_0 [1, -6] = true := by decide +kernel
theorem subd8_0_436 : subd8_0 [1, -5] = true := by decide +kernel
theorem subd8_0_437 : subd8_0 [1, -4] = true := by decide +kernel
theorem subd8_0_438 : subd8_0 [1, -3, -8] = true := by decide +kernel
theorem subd8_0_439 : subd8_0 [1, -3, -7] = true := by decide +kernel
theorem subd8_0_440 : subd8_0 [1, -3, -6] = true := by decide +kernel
theorem subd8_0_441 : subd8_0 [1, -3, -5] = true := by decide +kernel
theorem subd8_0_442 : subd8_0 [1, -3, -4] = true := by decide +kernel
theorem subd8_0_443 : subd8_0 [1, -3, -3] = true := by decide +kernel
theorem subd8_0_444 : subd8_0 [1, -3, -2] = true := by decide +kernel
theorem subd8_0_445 : subd8_0 [1, -3, -1] = true := by decide +kernel
theorem subd8_0_446 : subd8_0 [1, -3, 0] = true := by decide +kernel
theorem subd8_0_447 : subd8_0 [1, -3, 1] = true := by decide +kernel
theorem sbd8_0_13 : ∀ q ∈ blkd8_0_13, subd8_0 q = true := by
  unfold blkd8_0_13
  exact List.forall_mem_cons.2 ⟨subd8_0_416, List.forall_mem_cons.2 ⟨subd8_0_417, List.forall_mem_cons.2 ⟨subd8_0_418, List.forall_mem_cons.2 ⟨subd8_0_419, List.forall_mem_cons.2 ⟨subd8_0_420, List.forall_mem_cons.2 ⟨subd8_0_421, List.forall_mem_cons.2 ⟨subd8_0_422, List.forall_mem_cons.2 ⟨subd8_0_423, List.forall_mem_cons.2 ⟨subd8_0_424, List.forall_mem_cons.2 ⟨subd8_0_425, List.forall_mem_cons.2 ⟨subd8_0_426, List.forall_mem_cons.2 ⟨subd8_0_427, List.forall_mem_cons.2 ⟨subd8_0_428, List.forall_mem_cons.2 ⟨subd8_0_429, List.forall_mem_cons.2 ⟨subd8_0_430, List.forall_mem_cons.2 ⟨subd8_0_431, List.forall_mem_cons.2 ⟨subd8_0_432, List.forall_mem_cons.2 ⟨subd8_0_433, List.forall_mem_cons.2 ⟨subd8_0_434, List.forall_mem_cons.2 ⟨subd8_0_435, List.forall_mem_cons.2 ⟨subd8_0_436, List.forall_mem_cons.2 ⟨subd8_0_437, List.forall_mem_cons.2 ⟨subd8_0_438, List.forall_mem_cons.2 ⟨subd8_0_439, List.forall_mem_cons.2 ⟨subd8_0_440, List.forall_mem_cons.2 ⟨subd8_0_441, List.forall_mem_cons.2 ⟨subd8_0_442, List.forall_mem_cons.2 ⟨subd8_0_443, List.forall_mem_cons.2 ⟨subd8_0_444, List.forall_mem_cons.2 ⟨subd8_0_445, List.forall_mem_cons.2 ⟨subd8_0_446, List.forall_mem_cons.2 ⟨subd8_0_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_448 : subd8_0 [1, -3, 2] = true := by decide +kernel
theorem subd8_0_449 : subd8_0 [1, -3, 3] = true := by decide +kernel
theorem subd8_0_450 : subd8_0 [1, -3, 4] = true := by decide +kernel
theorem subd8_0_451 : subd8_0 [1, -3, 5] = true := by decide +kernel
theorem subd8_0_452 : subd8_0 [1, -2, -8] = true := by decide +kernel
theorem subd8_0_453 : subd8_0 [1, -2, -7] = true := by decide +kernel
theorem subd8_0_454 : subd8_0 [1, -2, -6] = true := by decide +kernel
theorem subd8_0_455 : subd8_0 [1, -2, -5] = true := by decide +kernel
theorem subd8_0_456 : subd8_0 [1, -2, -4] = true := by decide +kernel
theorem subd8_0_457 : subd8_0 [1, -2, -3] = true := by decide +kernel
theorem subd8_0_458 : subd8_0 [1, -2, -2] = true := by decide +kernel
theorem subd8_0_459 : subd8_0 [1, -2, -1] = true := by decide +kernel
theorem subd8_0_460 : subd8_0 [1, -2, 0] = true := by decide +kernel
theorem subd8_0_461 : subd8_0 [1, -2, 1] = true := by decide +kernel
theorem subd8_0_462 : subd8_0 [1, -2, 2] = true := by decide +kernel
theorem subd8_0_463 : subd8_0 [1, -2, 3] = true := by decide +kernel
theorem subd8_0_464 : subd8_0 [1, -2, 4] = true := by decide +kernel
theorem subd8_0_465 : subd8_0 [1, -2, 5] = true := by decide +kernel
theorem subd8_0_466 : subd8_0 [1, -2, 6] = true := by decide +kernel
theorem subd8_0_467 : subd8_0 [1, -1, -8] = true := by decide +kernel
theorem subd8_0_468 : subd8_0 [1, -1, -7] = true := by decide +kernel
theorem subd8_0_469 : subd8_0 [1, -1, -6] = true := by decide +kernel
theorem subd8_0_470 : subd8_0 [1, -1, -5] = true := by decide +kernel
theorem subd8_0_471 : subd8_0 [1, -1, -4] = true := by decide +kernel
theorem subd8_0_472 : subd8_0 [1, -1, -3] = true := by decide +kernel
theorem subd8_0_473 : subd8_0 [1, -1, -2] = true := by decide +kernel
theorem subd8_0_474 : subd8_0 [1, -1, -1] = true := by decide +kernel
theorem subd8_0_475 : subd8_0 [1, -1, 0] = true := by decide +kernel
theorem subd8_0_476 : subd8_0 [1, -1, 1] = true := by decide +kernel
theorem subd8_0_477 : subd8_0 [1, -1, 2] = true := by decide +kernel
theorem subd8_0_478 : subd8_0 [1, -1, 3] = true := by decide +kernel
theorem subd8_0_479 : subd8_0 [1, -1, 4] = true := by decide +kernel
theorem sbd8_0_14 : ∀ q ∈ blkd8_0_14, subd8_0 q = true := by
  unfold blkd8_0_14
  exact List.forall_mem_cons.2 ⟨subd8_0_448, List.forall_mem_cons.2 ⟨subd8_0_449, List.forall_mem_cons.2 ⟨subd8_0_450, List.forall_mem_cons.2 ⟨subd8_0_451, List.forall_mem_cons.2 ⟨subd8_0_452, List.forall_mem_cons.2 ⟨subd8_0_453, List.forall_mem_cons.2 ⟨subd8_0_454, List.forall_mem_cons.2 ⟨subd8_0_455, List.forall_mem_cons.2 ⟨subd8_0_456, List.forall_mem_cons.2 ⟨subd8_0_457, List.forall_mem_cons.2 ⟨subd8_0_458, List.forall_mem_cons.2 ⟨subd8_0_459, List.forall_mem_cons.2 ⟨subd8_0_460, List.forall_mem_cons.2 ⟨subd8_0_461, List.forall_mem_cons.2 ⟨subd8_0_462, List.forall_mem_cons.2 ⟨subd8_0_463, List.forall_mem_cons.2 ⟨subd8_0_464, List.forall_mem_cons.2 ⟨subd8_0_465, List.forall_mem_cons.2 ⟨subd8_0_466, List.forall_mem_cons.2 ⟨subd8_0_467, List.forall_mem_cons.2 ⟨subd8_0_468, List.forall_mem_cons.2 ⟨subd8_0_469, List.forall_mem_cons.2 ⟨subd8_0_470, List.forall_mem_cons.2 ⟨subd8_0_471, List.forall_mem_cons.2 ⟨subd8_0_472, List.forall_mem_cons.2 ⟨subd8_0_473, List.forall_mem_cons.2 ⟨subd8_0_474, List.forall_mem_cons.2 ⟨subd8_0_475, List.forall_mem_cons.2 ⟨subd8_0_476, List.forall_mem_cons.2 ⟨subd8_0_477, List.forall_mem_cons.2 ⟨subd8_0_478, List.forall_mem_cons.2 ⟨subd8_0_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_480 : subd8_0 [1, -1, 5] = true := by decide +kernel
theorem subd8_0_481 : subd8_0 [1, -1, 6] = true := by decide +kernel
theorem subd8_0_482 : subd8_0 [1, -1, 7] = true := by decide +kernel
theorem subd8_0_483 : subd8_0 [1, 0, -8] = true := by decide +kernel
theorem subd8_0_484 : subd8_0 [1, 0, -7] = true := by decide +kernel
theorem subd8_0_485 : subd8_0 [1, 0, -6] = true := by decide +kernel
theorem subd8_0_486 : subd8_0 [1, 0, -5] = true := by decide +kernel
theorem subd8_0_487 : subd8_0 [1, 0, -4] = true := by decide +kernel
theorem subd8_0_488 : subd8_0 [1, 0, -3] = true := by decide +kernel
theorem subd8_0_489 : subd8_0 [1, 0, -2] = true := by decide +kernel
theorem subd8_0_490 : subd8_0 [1, 0, -1] = true := by decide +kernel
theorem subd8_0_491 : subd8_0 [1, 0, 0] = true := by decide +kernel
theorem subd8_0_492 : subd8_0 [1, 0, 1] = true := by decide +kernel
theorem subd8_0_493 : subd8_0 [1, 0, 2] = true := by decide +kernel
theorem subd8_0_494 : subd8_0 [1, 0, 3] = true := by decide +kernel
theorem subd8_0_495 : subd8_0 [1, 0, 4] = true := by decide +kernel
theorem subd8_0_496 : subd8_0 [1, 0, 5] = true := by decide +kernel
theorem subd8_0_497 : subd8_0 [1, 0, 6] = true := by decide +kernel
theorem subd8_0_498 : subd8_0 [1, 0, 7] = true := by decide +kernel
theorem subd8_0_499 : subd8_0 [1, 1, -7] = true := by decide +kernel
theorem subd8_0_500 : subd8_0 [1, 1, -6] = true := by decide +kernel
theorem subd8_0_501 : subd8_0 [1, 1, -5] = true := by decide +kernel
theorem subd8_0_502 : subd8_0 [1, 1, -4] = true := by decide +kernel
theorem subd8_0_503 : subd8_0 [1, 1, -3] = true := by decide +kernel
theorem subd8_0_504 : subd8_0 [1, 1, -2] = true := by decide +kernel
theorem subd8_0_505 : subd8_0 [1, 1, -1] = true := by decide +kernel
theorem subd8_0_506 : subd8_0 [1, 1, 0] = true := by decide +kernel
theorem subd8_0_507 : subd8_0 [1, 1, 1] = true := by decide +kernel
theorem subd8_0_508 : subd8_0 [1, 1, 2] = true := by decide +kernel
theorem subd8_0_509 : subd8_0 [1, 1, 3] = true := by decide +kernel
theorem subd8_0_510 : subd8_0 [1, 1, 4] = true := by decide +kernel
theorem subd8_0_511 : subd8_0 [1, 1, 5] = true := by decide +kernel
theorem sbd8_0_15 : ∀ q ∈ blkd8_0_15, subd8_0 q = true := by
  unfold blkd8_0_15
  exact List.forall_mem_cons.2 ⟨subd8_0_480, List.forall_mem_cons.2 ⟨subd8_0_481, List.forall_mem_cons.2 ⟨subd8_0_482, List.forall_mem_cons.2 ⟨subd8_0_483, List.forall_mem_cons.2 ⟨subd8_0_484, List.forall_mem_cons.2 ⟨subd8_0_485, List.forall_mem_cons.2 ⟨subd8_0_486, List.forall_mem_cons.2 ⟨subd8_0_487, List.forall_mem_cons.2 ⟨subd8_0_488, List.forall_mem_cons.2 ⟨subd8_0_489, List.forall_mem_cons.2 ⟨subd8_0_490, List.forall_mem_cons.2 ⟨subd8_0_491, List.forall_mem_cons.2 ⟨subd8_0_492, List.forall_mem_cons.2 ⟨subd8_0_493, List.forall_mem_cons.2 ⟨subd8_0_494, List.forall_mem_cons.2 ⟨subd8_0_495, List.forall_mem_cons.2 ⟨subd8_0_496, List.forall_mem_cons.2 ⟨subd8_0_497, List.forall_mem_cons.2 ⟨subd8_0_498, List.forall_mem_cons.2 ⟨subd8_0_499, List.forall_mem_cons.2 ⟨subd8_0_500, List.forall_mem_cons.2 ⟨subd8_0_501, List.forall_mem_cons.2 ⟨subd8_0_502, List.forall_mem_cons.2 ⟨subd8_0_503, List.forall_mem_cons.2 ⟨subd8_0_504, List.forall_mem_cons.2 ⟨subd8_0_505, List.forall_mem_cons.2 ⟨subd8_0_506, List.forall_mem_cons.2 ⟨subd8_0_507, List.forall_mem_cons.2 ⟨subd8_0_508, List.forall_mem_cons.2 ⟨subd8_0_509, List.forall_mem_cons.2 ⟨subd8_0_510, List.forall_mem_cons.2 ⟨subd8_0_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_512 : subd8_0 [1, 1, 6] = true := by decide +kernel
theorem subd8_0_513 : subd8_0 [1, 1, 7] = true := by decide +kernel
theorem subd8_0_514 : subd8_0 [1, 1, 8] = true := by decide +kernel
theorem subd8_0_515 : subd8_0 [1, 2, -6] = true := by decide +kernel
theorem subd8_0_516 : subd8_0 [1, 2, -5] = true := by decide +kernel
theorem subd8_0_517 : subd8_0 [1, 2, -4] = true := by decide +kernel
theorem subd8_0_518 : subd8_0 [1, 2, -3] = true := by decide +kernel
theorem subd8_0_519 : subd8_0 [1, 2, -2] = true := by decide +kernel
theorem subd8_0_520 : subd8_0 [1, 2, -1] = true := by decide +kernel
theorem subd8_0_521 : subd8_0 [1, 2, 0] = true := by decide +kernel
theorem subd8_0_522 : subd8_0 [1, 2, 1] = true := by decide +kernel
theorem subd8_0_523 : subd8_0 [1, 2, 2] = true := by decide +kernel
theorem subd8_0_524 : subd8_0 [1, 2, 3] = true := by decide +kernel
theorem subd8_0_525 : subd8_0 [1, 2, 4] = true := by decide +kernel
theorem subd8_0_526 : subd8_0 [1, 2, 5] = true := by decide +kernel
theorem subd8_0_527 : subd8_0 [1, 2, 6] = true := by decide +kernel
theorem subd8_0_528 : subd8_0 [1, 2, 7] = true := by decide +kernel
theorem subd8_0_529 : subd8_0 [1, 2, 8] = true := by decide +kernel
theorem subd8_0_530 : subd8_0 [1, 3, -6] = true := by decide +kernel
theorem subd8_0_531 : subd8_0 [1, 3, -5] = true := by decide +kernel
theorem subd8_0_532 : subd8_0 [1, 3, -4] = true := by decide +kernel
theorem subd8_0_533 : subd8_0 [1, 3, -3] = true := by decide +kernel
theorem subd8_0_534 : subd8_0 [1, 3, -2] = true := by decide +kernel
theorem subd8_0_535 : subd8_0 [1, 3, -1] = true := by decide +kernel
theorem subd8_0_536 : subd8_0 [1, 3, 0] = true := by decide +kernel
theorem subd8_0_537 : subd8_0 [1, 3, 1] = true := by decide +kernel
theorem subd8_0_538 : subd8_0 [1, 3, 2] = true := by decide +kernel
theorem subd8_0_539 : subd8_0 [1, 3, 3] = true := by decide +kernel
theorem subd8_0_540 : subd8_0 [1, 3, 4] = true := by decide +kernel
theorem subd8_0_541 : subd8_0 [1, 3, 5] = true := by decide +kernel
theorem subd8_0_542 : subd8_0 [1, 3, 6] = true := by decide +kernel
theorem subd8_0_543 : subd8_0 [1, 3, 7] = true := by decide +kernel
theorem sbd8_0_16 : ∀ q ∈ blkd8_0_16, subd8_0 q = true := by
  unfold blkd8_0_16
  exact List.forall_mem_cons.2 ⟨subd8_0_512, List.forall_mem_cons.2 ⟨subd8_0_513, List.forall_mem_cons.2 ⟨subd8_0_514, List.forall_mem_cons.2 ⟨subd8_0_515, List.forall_mem_cons.2 ⟨subd8_0_516, List.forall_mem_cons.2 ⟨subd8_0_517, List.forall_mem_cons.2 ⟨subd8_0_518, List.forall_mem_cons.2 ⟨subd8_0_519, List.forall_mem_cons.2 ⟨subd8_0_520, List.forall_mem_cons.2 ⟨subd8_0_521, List.forall_mem_cons.2 ⟨subd8_0_522, List.forall_mem_cons.2 ⟨subd8_0_523, List.forall_mem_cons.2 ⟨subd8_0_524, List.forall_mem_cons.2 ⟨subd8_0_525, List.forall_mem_cons.2 ⟨subd8_0_526, List.forall_mem_cons.2 ⟨subd8_0_527, List.forall_mem_cons.2 ⟨subd8_0_528, List.forall_mem_cons.2 ⟨subd8_0_529, List.forall_mem_cons.2 ⟨subd8_0_530, List.forall_mem_cons.2 ⟨subd8_0_531, List.forall_mem_cons.2 ⟨subd8_0_532, List.forall_mem_cons.2 ⟨subd8_0_533, List.forall_mem_cons.2 ⟨subd8_0_534, List.forall_mem_cons.2 ⟨subd8_0_535, List.forall_mem_cons.2 ⟨subd8_0_536, List.forall_mem_cons.2 ⟨subd8_0_537, List.forall_mem_cons.2 ⟨subd8_0_538, List.forall_mem_cons.2 ⟨subd8_0_539, List.forall_mem_cons.2 ⟨subd8_0_540, List.forall_mem_cons.2 ⟨subd8_0_541, List.forall_mem_cons.2 ⟨subd8_0_542, List.forall_mem_cons.2 ⟨subd8_0_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_544 : subd8_0 [1, 3, 8] = true := by decide +kernel
theorem subd8_0_545 : subd8_0 [1, 4] = true := by decide +kernel
theorem subd8_0_546 : subd8_0 [1, 5] = true := by decide +kernel
theorem subd8_0_547 : subd8_0 [1, 6] = true := by decide +kernel
theorem subd8_0_548 : subd8_0 [1, 7] = true := by decide +kernel
theorem subd8_0_549 : subd8_0 [2, -7] = true := by decide +kernel
theorem subd8_0_550 : subd8_0 [2, -6] = true := by decide +kernel
theorem subd8_0_551 : subd8_0 [2, -5] = true := by decide +kernel
theorem subd8_0_552 : subd8_0 [2, -4] = true := by decide +kernel
theorem subd8_0_553 : subd8_0 [2, -3] = true := by decide +kernel
theorem subd8_0_554 : subd8_0 [2, -2, -8] = true := by decide +kernel
theorem subd8_0_555 : subd8_0 [2, -2, -7] = true := by decide +kernel
theorem subd8_0_556 : subd8_0 [2, -2, -6] = true := by decide +kernel
theorem subd8_0_557 : subd8_0 [2, -2, -5] = true := by decide +kernel
theorem subd8_0_558 : subd8_0 [2, -2, -4] = true := by decide +kernel
theorem subd8_0_559 : subd8_0 [2, -2, -3] = true := by decide +kernel
theorem subd8_0_560 : subd8_0 [2, -2, -2] = true := by decide +kernel
theorem subd8_0_561 : subd8_0 [2, -2, -1] = true := by decide +kernel
theorem subd8_0_562 : subd8_0 [2, -2, 0] = true := by decide +kernel
theorem subd8_0_563 : subd8_0 [2, -2, 1] = true := by decide +kernel
theorem subd8_0_564 : subd8_0 [2, -2, 2] = true := by decide +kernel
theorem subd8_0_565 : subd8_0 [2, -2, 3] = true := by decide +kernel
theorem subd8_0_566 : subd8_0 [2, -2, 4] = true := by decide +kernel
theorem subd8_0_567 : subd8_0 [2, -2, 5] = true := by decide +kernel
theorem subd8_0_568 : subd8_0 [2, -2, 6] = true := by decide +kernel
theorem subd8_0_569 : subd8_0 [2, -1, -7] = true := by decide +kernel
theorem subd8_0_570 : subd8_0 [2, -1, -6] = true := by decide +kernel
theorem subd8_0_571 : subd8_0 [2, -1, -5] = true := by decide +kernel
theorem subd8_0_572 : subd8_0 [2, -1, -4] = true := by decide +kernel
theorem subd8_0_573 : subd8_0 [2, -1, -3] = true := by decide +kernel
theorem subd8_0_574 : subd8_0 [2, -1, -2] = true := by decide +kernel
theorem subd8_0_575 : subd8_0 [2, -1, -1] = true := by decide +kernel
theorem sbd8_0_17 : ∀ q ∈ blkd8_0_17, subd8_0 q = true := by
  unfold blkd8_0_17
  exact List.forall_mem_cons.2 ⟨subd8_0_544, List.forall_mem_cons.2 ⟨subd8_0_545, List.forall_mem_cons.2 ⟨subd8_0_546, List.forall_mem_cons.2 ⟨subd8_0_547, List.forall_mem_cons.2 ⟨subd8_0_548, List.forall_mem_cons.2 ⟨subd8_0_549, List.forall_mem_cons.2 ⟨subd8_0_550, List.forall_mem_cons.2 ⟨subd8_0_551, List.forall_mem_cons.2 ⟨subd8_0_552, List.forall_mem_cons.2 ⟨subd8_0_553, List.forall_mem_cons.2 ⟨subd8_0_554, List.forall_mem_cons.2 ⟨subd8_0_555, List.forall_mem_cons.2 ⟨subd8_0_556, List.forall_mem_cons.2 ⟨subd8_0_557, List.forall_mem_cons.2 ⟨subd8_0_558, List.forall_mem_cons.2 ⟨subd8_0_559, List.forall_mem_cons.2 ⟨subd8_0_560, List.forall_mem_cons.2 ⟨subd8_0_561, List.forall_mem_cons.2 ⟨subd8_0_562, List.forall_mem_cons.2 ⟨subd8_0_563, List.forall_mem_cons.2 ⟨subd8_0_564, List.forall_mem_cons.2 ⟨subd8_0_565, List.forall_mem_cons.2 ⟨subd8_0_566, List.forall_mem_cons.2 ⟨subd8_0_567, List.forall_mem_cons.2 ⟨subd8_0_568, List.forall_mem_cons.2 ⟨subd8_0_569, List.forall_mem_cons.2 ⟨subd8_0_570, List.forall_mem_cons.2 ⟨subd8_0_571, List.forall_mem_cons.2 ⟨subd8_0_572, List.forall_mem_cons.2 ⟨subd8_0_573, List.forall_mem_cons.2 ⟨subd8_0_574, List.forall_mem_cons.2 ⟨subd8_0_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_576 : subd8_0 [2, -1, 0] = true := by decide +kernel
theorem subd8_0_577 : subd8_0 [2, -1, 1] = true := by decide +kernel
theorem subd8_0_578 : subd8_0 [2, -1, 2] = true := by decide +kernel
theorem subd8_0_579 : subd8_0 [2, -1, 3] = true := by decide +kernel
theorem subd8_0_580 : subd8_0 [2, -1, 4] = true := by decide +kernel
theorem subd8_0_581 : subd8_0 [2, -1, 5] = true := by decide +kernel
theorem subd8_0_582 : subd8_0 [2, -1, 6] = true := by decide +kernel
theorem subd8_0_583 : subd8_0 [2, -1, 7] = true := by decide +kernel
theorem subd8_0_584 : subd8_0 [2, 0, -7] = true := by decide +kernel
theorem subd8_0_585 : subd8_0 [2, 0, -6] = true := by decide +kernel
theorem subd8_0_586 : subd8_0 [2, 0, -5] = true := by decide +kernel
theorem subd8_0_587 : subd8_0 [2, 0, -4] = true := by decide +kernel
theorem subd8_0_588 : subd8_0 [2, 0, -3] = true := by decide +kernel
theorem subd8_0_589 : subd8_0 [2, 0, -2] = true := by decide +kernel
theorem subd8_0_590 : subd8_0 [2, 0, -1] = true := by decide +kernel
theorem subd8_0_591 : subd8_0 [2, 0, 0] = true := by decide +kernel
theorem subd8_0_592 : subd8_0 [2, 0, 1] = true := by decide +kernel
theorem subd8_0_593 : subd8_0 [2, 0, 2] = true := by decide +kernel
theorem subd8_0_594 : subd8_0 [2, 0, 3] = true := by decide +kernel
theorem subd8_0_595 : subd8_0 [2, 0, 4] = true := by decide +kernel
theorem subd8_0_596 : subd8_0 [2, 0, 5] = true := by decide +kernel
theorem subd8_0_597 : subd8_0 [2, 0, 6] = true := by decide +kernel
theorem subd8_0_598 : subd8_0 [2, 0, 7] = true := by decide +kernel
theorem subd8_0_599 : subd8_0 [2, 0, 8] = true := by decide +kernel
theorem subd8_0_600 : subd8_0 [2, 1, -7] = true := by decide +kernel
theorem subd8_0_601 : subd8_0 [2, 1, -6] = true := by decide +kernel
theorem subd8_0_602 : subd8_0 [2, 1, -5] = true := by decide +kernel
theorem subd8_0_603 : subd8_0 [2, 1, -4] = true := by decide +kernel
theorem subd8_0_604 : subd8_0 [2, 1, -3] = true := by decide +kernel
theorem subd8_0_605 : subd8_0 [2, 1, -2] = true := by decide +kernel
theorem subd8_0_606 : subd8_0 [2, 1, -1] = true := by decide +kernel
theorem subd8_0_607 : subd8_0 [2, 1, 0] = true := by decide +kernel
theorem sbd8_0_18 : ∀ q ∈ blkd8_0_18, subd8_0 q = true := by
  unfold blkd8_0_18
  exact List.forall_mem_cons.2 ⟨subd8_0_576, List.forall_mem_cons.2 ⟨subd8_0_577, List.forall_mem_cons.2 ⟨subd8_0_578, List.forall_mem_cons.2 ⟨subd8_0_579, List.forall_mem_cons.2 ⟨subd8_0_580, List.forall_mem_cons.2 ⟨subd8_0_581, List.forall_mem_cons.2 ⟨subd8_0_582, List.forall_mem_cons.2 ⟨subd8_0_583, List.forall_mem_cons.2 ⟨subd8_0_584, List.forall_mem_cons.2 ⟨subd8_0_585, List.forall_mem_cons.2 ⟨subd8_0_586, List.forall_mem_cons.2 ⟨subd8_0_587, List.forall_mem_cons.2 ⟨subd8_0_588, List.forall_mem_cons.2 ⟨subd8_0_589, List.forall_mem_cons.2 ⟨subd8_0_590, List.forall_mem_cons.2 ⟨subd8_0_591, List.forall_mem_cons.2 ⟨subd8_0_592, List.forall_mem_cons.2 ⟨subd8_0_593, List.forall_mem_cons.2 ⟨subd8_0_594, List.forall_mem_cons.2 ⟨subd8_0_595, List.forall_mem_cons.2 ⟨subd8_0_596, List.forall_mem_cons.2 ⟨subd8_0_597, List.forall_mem_cons.2 ⟨subd8_0_598, List.forall_mem_cons.2 ⟨subd8_0_599, List.forall_mem_cons.2 ⟨subd8_0_600, List.forall_mem_cons.2 ⟨subd8_0_601, List.forall_mem_cons.2 ⟨subd8_0_602, List.forall_mem_cons.2 ⟨subd8_0_603, List.forall_mem_cons.2 ⟨subd8_0_604, List.forall_mem_cons.2 ⟨subd8_0_605, List.forall_mem_cons.2 ⟨subd8_0_606, List.forall_mem_cons.2 ⟨subd8_0_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C129
