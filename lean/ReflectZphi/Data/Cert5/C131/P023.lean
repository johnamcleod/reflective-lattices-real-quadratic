import ReflectZphi.Data.Cert5.C131.Base

namespace ReflectZphi.Data.Cert5.C131

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd12_0_192 : subd12_0 [-3, 0, 1] = true := by decide +kernel
theorem subd12_0_193 : subd12_0 [-3, 0, 2] = true := by decide +kernel
theorem subd12_0_194 : subd12_0 [-3, 0, 3] = true := by decide +kernel
theorem subd12_0_195 : subd12_0 [-3, 0, 4] = true := by decide +kernel
theorem subd12_0_196 : subd12_0 [-3, 0, 5] = true := by decide +kernel
theorem subd12_0_197 : subd12_0 [-3, 0, 6] = true := by decide +kernel
theorem subd12_0_198 : subd12_0 [-3, 0, 7] = true := by decide +kernel
theorem subd12_0_199 : subd12_0 [-3, 1, -8] = true := by decide +kernel
theorem subd12_0_200 : subd12_0 [-3, 1, -7] = true := by decide +kernel
theorem subd12_0_201 : subd12_0 [-3, 1, -6] = true := by decide +kernel
theorem subd12_0_202 : subd12_0 [-3, 1, -5] = true := by decide +kernel
theorem subd12_0_203 : subd12_0 [-3, 1, -4] = true := by decide +kernel
theorem subd12_0_204 : subd12_0 [-3, 1, -3] = true := by decide +kernel
theorem subd12_0_205 : subd12_0 [-3, 1, -2] = true := by decide +kernel
theorem subd12_0_206 : subd12_0 [-3, 1, -1] = true := by decide +kernel
theorem subd12_0_207 : subd12_0 [-3, 1, 0] = true := by decide +kernel
theorem subd12_0_208 : subd12_0 [-3, 1, 1] = true := by decide +kernel
theorem subd12_0_209 : subd12_0 [-3, 1, 2] = true := by decide +kernel
theorem subd12_0_210 : subd12_0 [-3, 1, 3] = true := by decide +kernel
theorem subd12_0_211 : subd12_0 [-3, 1, 4] = true := by decide +kernel
theorem subd12_0_212 : subd12_0 [-3, 1, 5] = true := by decide +kernel
theorem subd12_0_213 : subd12_0 [-3, 1, 6] = true := by decide +kernel
theorem subd12_0_214 : subd12_0 [-3, 1, 7] = true := by decide +kernel
theorem subd12_0_215 : subd12_0 [-3, 2, -7] = true := by decide +kernel
theorem subd12_0_216 : subd12_0 [-3, 2, -6] = true := by decide +kernel
theorem subd12_0_217 : subd12_0 [-3, 2, -5] = true := by decide +kernel
theorem subd12_0_218 : subd12_0 [-3, 2, -4] = true := by decide +kernel
theorem subd12_0_219 : subd12_0 [-3, 2, -3] = true := by decide +kernel
theorem subd12_0_220 : subd12_0 [-3, 2, -2] = true := by decide +kernel
theorem subd12_0_221 : subd12_0 [-3, 2, -1] = true := by decide +kernel
theorem subd12_0_222 : subd12_0 [-3, 2, 0] = true := by decide +kernel
theorem subd12_0_223 : subd12_0 [-3, 2, 1] = true := by decide +kernel
theorem sbd12_0_6 : ∀ q ∈ blkd12_0_6, subd12_0 q = true := by
  unfold blkd12_0_6
  exact List.forall_mem_cons.2 ⟨subd12_0_192, List.forall_mem_cons.2 ⟨subd12_0_193, List.forall_mem_cons.2 ⟨subd12_0_194, List.forall_mem_cons.2 ⟨subd12_0_195, List.forall_mem_cons.2 ⟨subd12_0_196, List.forall_mem_cons.2 ⟨subd12_0_197, List.forall_mem_cons.2 ⟨subd12_0_198, List.forall_mem_cons.2 ⟨subd12_0_199, List.forall_mem_cons.2 ⟨subd12_0_200, List.forall_mem_cons.2 ⟨subd12_0_201, List.forall_mem_cons.2 ⟨subd12_0_202, List.forall_mem_cons.2 ⟨subd12_0_203, List.forall_mem_cons.2 ⟨subd12_0_204, List.forall_mem_cons.2 ⟨subd12_0_205, List.forall_mem_cons.2 ⟨subd12_0_206, List.forall_mem_cons.2 ⟨subd12_0_207, List.forall_mem_cons.2 ⟨subd12_0_208, List.forall_mem_cons.2 ⟨subd12_0_209, List.forall_mem_cons.2 ⟨subd12_0_210, List.forall_mem_cons.2 ⟨subd12_0_211, List.forall_mem_cons.2 ⟨subd12_0_212, List.forall_mem_cons.2 ⟨subd12_0_213, List.forall_mem_cons.2 ⟨subd12_0_214, List.forall_mem_cons.2 ⟨subd12_0_215, List.forall_mem_cons.2 ⟨subd12_0_216, List.forall_mem_cons.2 ⟨subd12_0_217, List.forall_mem_cons.2 ⟨subd12_0_218, List.forall_mem_cons.2 ⟨subd12_0_219, List.forall_mem_cons.2 ⟨subd12_0_220, List.forall_mem_cons.2 ⟨subd12_0_221, List.forall_mem_cons.2 ⟨subd12_0_222, List.forall_mem_cons.2 ⟨subd12_0_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_224 : subd12_0 [-3, 2, 2] = true := by decide +kernel
theorem subd12_0_225 : subd12_0 [-3, 2, 3] = true := by decide +kernel
theorem subd12_0_226 : subd12_0 [-3, 2, 4] = true := by decide +kernel
theorem subd12_0_227 : subd12_0 [-3, 2, 5] = true := by decide +kernel
theorem subd12_0_228 : subd12_0 [-3, 2, 6] = true := by decide +kernel
theorem subd12_0_229 : subd12_0 [-3, 2, 7] = true := by decide +kernel
theorem subd12_0_230 : subd12_0 [-3, 2, 8] = true := by decide +kernel
theorem subd12_0_231 : subd12_0 [-3, 3, -6] = true := by decide +kernel
theorem subd12_0_232 : subd12_0 [-3, 3, -5] = true := by decide +kernel
theorem subd12_0_233 : subd12_0 [-3, 3, -4] = true := by decide +kernel
theorem subd12_0_234 : subd12_0 [-3, 3, -3] = true := by decide +kernel
theorem subd12_0_235 : subd12_0 [-3, 3, -2] = true := by decide +kernel
theorem subd12_0_236 : subd12_0 [-3, 3, -1] = true := by decide +kernel
theorem subd12_0_237 : subd12_0 [-3, 3, 0] = true := by decide +kernel
theorem subd12_0_238 : subd12_0 [-3, 3, 1] = true := by decide +kernel
theorem subd12_0_239 : subd12_0 [-3, 3, 2] = true := by decide +kernel
theorem subd12_0_240 : subd12_0 [-3, 3, 3] = true := by decide +kernel
theorem subd12_0_241 : subd12_0 [-3, 3, 4] = true := by decide +kernel
theorem subd12_0_242 : subd12_0 [-3, 3, 5] = true := by decide +kernel
theorem subd12_0_243 : subd12_0 [-3, 3, 6] = true := by decide +kernel
theorem subd12_0_244 : subd12_0 [-3, 3, 7] = true := by decide +kernel
theorem subd12_0_245 : subd12_0 [-3, 3, 8] = true := by decide +kernel
theorem subd12_0_246 : subd12_0 [-3, 4, -6] = true := by decide +kernel
theorem subd12_0_247 : subd12_0 [-3, 4, -5] = true := by decide +kernel
theorem subd12_0_248 : subd12_0 [-3, 4, -4] = true := by decide +kernel
theorem subd12_0_249 : subd12_0 [-3, 4, -3] = true := by decide +kernel
theorem subd12_0_250 : subd12_0 [-3, 4, -2] = true := by decide +kernel
theorem subd12_0_251 : subd12_0 [-3, 4, -1] = true := by decide +kernel
theorem subd12_0_252 : subd12_0 [-3, 4, 0] = true := by decide +kernel
theorem subd12_0_253 : subd12_0 [-3, 4, 1] = true := by decide +kernel
theorem subd12_0_254 : subd12_0 [-3, 4, 2] = true := by decide +kernel
theorem subd12_0_255 : subd12_0 [-3, 4, 3] = true := by decide +kernel
theorem sbd12_0_7 : ∀ q ∈ blkd12_0_7, subd12_0 q = true := by
  unfold blkd12_0_7
  exact List.forall_mem_cons.2 ⟨subd12_0_224, List.forall_mem_cons.2 ⟨subd12_0_225, List.forall_mem_cons.2 ⟨subd12_0_226, List.forall_mem_cons.2 ⟨subd12_0_227, List.forall_mem_cons.2 ⟨subd12_0_228, List.forall_mem_cons.2 ⟨subd12_0_229, List.forall_mem_cons.2 ⟨subd12_0_230, List.forall_mem_cons.2 ⟨subd12_0_231, List.forall_mem_cons.2 ⟨subd12_0_232, List.forall_mem_cons.2 ⟨subd12_0_233, List.forall_mem_cons.2 ⟨subd12_0_234, List.forall_mem_cons.2 ⟨subd12_0_235, List.forall_mem_cons.2 ⟨subd12_0_236, List.forall_mem_cons.2 ⟨subd12_0_237, List.forall_mem_cons.2 ⟨subd12_0_238, List.forall_mem_cons.2 ⟨subd12_0_239, List.forall_mem_cons.2 ⟨subd12_0_240, List.forall_mem_cons.2 ⟨subd12_0_241, List.forall_mem_cons.2 ⟨subd12_0_242, List.forall_mem_cons.2 ⟨subd12_0_243, List.forall_mem_cons.2 ⟨subd12_0_244, List.forall_mem_cons.2 ⟨subd12_0_245, List.forall_mem_cons.2 ⟨subd12_0_246, List.forall_mem_cons.2 ⟨subd12_0_247, List.forall_mem_cons.2 ⟨subd12_0_248, List.forall_mem_cons.2 ⟨subd12_0_249, List.forall_mem_cons.2 ⟨subd12_0_250, List.forall_mem_cons.2 ⟨subd12_0_251, List.forall_mem_cons.2 ⟨subd12_0_252, List.forall_mem_cons.2 ⟨subd12_0_253, List.forall_mem_cons.2 ⟨subd12_0_254, List.forall_mem_cons.2 ⟨subd12_0_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_256 : subd12_0 [-3, 4, 4] = true := by decide +kernel
theorem subd12_0_257 : subd12_0 [-3, 4, 5] = true := by decide +kernel
theorem subd12_0_258 : subd12_0 [-3, 4, 6] = true := by decide +kernel
theorem subd12_0_259 : subd12_0 [-3, 4, 7] = true := by decide +kernel
theorem subd12_0_260 : subd12_0 [-3, 4, 8] = true := by decide +kernel
theorem subd12_0_261 : subd12_0 [-3, 5] = true := by decide +kernel
theorem subd12_0_262 : subd12_0 [-3, 6] = true := by decide +kernel
theorem subd12_0_263 : subd12_0 [-3, 7] = true := by decide +kernel
theorem subd12_0_264 : subd12_0 [-3, 8] = true := by decide +kernel
theorem subd12_0_265 : subd12_0 [-2, -8] = true := by decide +kernel
theorem subd12_0_266 : subd12_0 [-2, -7] = true := by decide +kernel
theorem subd12_0_267 : subd12_0 [-2, -6] = true := by decide +kernel
theorem subd12_0_268 : subd12_0 [-2, -5] = true := by decide +kernel
theorem subd12_0_269 : subd12_0 [-2, -4, -9] = true := by decide +kernel
theorem subd12_0_270 : subd12_0 [-2, -4, -8] = true := by decide +kernel
theorem subd12_0_271 : subd12_0 [-2, -4, -7] = true := by decide +kernel
theorem subd12_0_272 : subd12_0 [-2, -4, -6] = true := by decide +kernel
theorem subd12_0_273 : subd12_0 [-2, -4, -5] = true := by decide +kernel
theorem subd12_0_274 : subd12_0 [-2, -4, -4] = true := by decide +kernel
theorem subd12_0_275 : subd12_0 [-2, -4, -3] = true := by decide +kernel
theorem subd12_0_276 : subd12_0 [-2, -4, -2] = true := by decide +kernel
theorem subd12_0_277 : subd12_0 [-2, -4, -1] = true := by decide +kernel
theorem subd12_0_278 : subd12_0 [-2, -4, 0] = true := by decide +kernel
theorem subd12_0_279 : subd12_0 [-2, -4, 1] = true := by decide +kernel
theorem subd12_0_280 : subd12_0 [-2, -4, 2] = true := by decide +kernel
theorem subd12_0_281 : subd12_0 [-2, -4, 3] = true := by decide +kernel
theorem subd12_0_282 : subd12_0 [-2, -4, 4] = true := by decide +kernel
theorem subd12_0_283 : subd12_0 [-2, -3, -9] = true := by decide +kernel
theorem subd12_0_284 : subd12_0 [-2, -3, -8] = true := by decide +kernel
theorem subd12_0_285 : subd12_0 [-2, -3, -7] = true := by decide +kernel
theorem subd12_0_286 : subd12_0 [-2, -3, -6] = true := by decide +kernel
theorem subd12_0_287 : subd12_0 [-2, -3, -5] = true := by decide +kernel
theorem sbd12_0_8 : ∀ q ∈ blkd12_0_8, subd12_0 q = true := by
  unfold blkd12_0_8
  exact List.forall_mem_cons.2 ⟨subd12_0_256, List.forall_mem_cons.2 ⟨subd12_0_257, List.forall_mem_cons.2 ⟨subd12_0_258, List.forall_mem_cons.2 ⟨subd12_0_259, List.forall_mem_cons.2 ⟨subd12_0_260, List.forall_mem_cons.2 ⟨subd12_0_261, List.forall_mem_cons.2 ⟨subd12_0_262, List.forall_mem_cons.2 ⟨subd12_0_263, List.forall_mem_cons.2 ⟨subd12_0_264, List.forall_mem_cons.2 ⟨subd12_0_265, List.forall_mem_cons.2 ⟨subd12_0_266, List.forall_mem_cons.2 ⟨subd12_0_267, List.forall_mem_cons.2 ⟨subd12_0_268, List.forall_mem_cons.2 ⟨subd12_0_269, List.forall_mem_cons.2 ⟨subd12_0_270, List.forall_mem_cons.2 ⟨subd12_0_271, List.forall_mem_cons.2 ⟨subd12_0_272, List.forall_mem_cons.2 ⟨subd12_0_273, List.forall_mem_cons.2 ⟨subd12_0_274, List.forall_mem_cons.2 ⟨subd12_0_275, List.forall_mem_cons.2 ⟨subd12_0_276, List.forall_mem_cons.2 ⟨subd12_0_277, List.forall_mem_cons.2 ⟨subd12_0_278, List.forall_mem_cons.2 ⟨subd12_0_279, List.forall_mem_cons.2 ⟨subd12_0_280, List.forall_mem_cons.2 ⟨subd12_0_281, List.forall_mem_cons.2 ⟨subd12_0_282, List.forall_mem_cons.2 ⟨subd12_0_283, List.forall_mem_cons.2 ⟨subd12_0_284, List.forall_mem_cons.2 ⟨subd12_0_285, List.forall_mem_cons.2 ⟨subd12_0_286, List.forall_mem_cons.2 ⟨subd12_0_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_288 : subd12_0 [-2, -3, -4] = true := by decide +kernel
theorem subd12_0_289 : subd12_0 [-2, -3, -3] = true := by decide +kernel
theorem subd12_0_290 : subd12_0 [-2, -3, -2] = true := by decide +kernel
theorem subd12_0_291 : subd12_0 [-2, -3, -1] = true := by decide +kernel
theorem subd12_0_292 : subd12_0 [-2, -3, 0] = true := by decide +kernel
theorem subd12_0_293 : subd12_0 [-2, -3, 1] = true := by decide +kernel
theorem subd12_0_294 : subd12_0 [-2, -3, 2] = true := by decide +kernel
theorem subd12_0_295 : subd12_0 [-2, -3, 3] = true := by decide +kernel
theorem subd12_0_296 : subd12_0 [-2, -3, 4] = true := by decide +kernel
theorem subd12_0_297 : subd12_0 [-2, -3, 5] = true := by decide +kernel
theorem subd12_0_298 : subd12_0 [-2, -2, -9] = true := by decide +kernel
theorem subd12_0_299 : subd12_0 [-2, -2, -8] = true := by decide +kernel
theorem subd12_0_300 : subd12_0 [-2, -2, -7] = true := by decide +kernel
theorem subd12_0_301 : subd12_0 [-2, -2, -6] = true := by decide +kernel
theorem subd12_0_302 : subd12_0 [-2, -2, -5] = true := by decide +kernel
theorem subd12_0_303 : subd12_0 [-2, -2, -4] = true := by decide +kernel
theorem subd12_0_304 : subd12_0 [-2, -2, -3] = true := by decide +kernel
theorem subd12_0_305 : subd12_0 [-2, -2, -2] = true := by decide +kernel
theorem subd12_0_306 : subd12_0 [-2, -2, -1] = true := by decide +kernel
theorem subd12_0_307 : subd12_0 [-2, -2, 0] = true := by decide +kernel
theorem subd12_0_308 : subd12_0 [-2, -2, 1] = true := by decide +kernel
theorem subd12_0_309 : subd12_0 [-2, -2, 2] = true := by decide +kernel
theorem subd12_0_310 : subd12_0 [-2, -2, 3] = true := by decide +kernel
theorem subd12_0_311 : subd12_0 [-2, -2, 4] = true := by decide +kernel
theorem subd12_0_312 : subd12_0 [-2, -2, 5] = true := by decide +kernel
theorem subd12_0_313 : subd12_0 [-2, -2, 6] = true := by decide +kernel
theorem subd12_0_314 : subd12_0 [-2, -1, -9] = true := by decide +kernel
theorem subd12_0_315 : subd12_0 [-2, -1, -8] = true := by decide +kernel
theorem subd12_0_316 : subd12_0 [-2, -1, -7] = true := by decide +kernel
theorem subd12_0_317 : subd12_0 [-2, -1, -6] = true := by decide +kernel
theorem subd12_0_318 : subd12_0 [-2, -1, -5] = true := by decide +kernel
theorem subd12_0_319 : subd12_0 [-2, -1, -4] = true := by decide +kernel
theorem sbd12_0_9 : ∀ q ∈ blkd12_0_9, subd12_0 q = true := by
  unfold blkd12_0_9
  exact List.forall_mem_cons.2 ⟨subd12_0_288, List.forall_mem_cons.2 ⟨subd12_0_289, List.forall_mem_cons.2 ⟨subd12_0_290, List.forall_mem_cons.2 ⟨subd12_0_291, List.forall_mem_cons.2 ⟨subd12_0_292, List.forall_mem_cons.2 ⟨subd12_0_293, List.forall_mem_cons.2 ⟨subd12_0_294, List.forall_mem_cons.2 ⟨subd12_0_295, List.forall_mem_cons.2 ⟨subd12_0_296, List.forall_mem_cons.2 ⟨subd12_0_297, List.forall_mem_cons.2 ⟨subd12_0_298, List.forall_mem_cons.2 ⟨subd12_0_299, List.forall_mem_cons.2 ⟨subd12_0_300, List.forall_mem_cons.2 ⟨subd12_0_301, List.forall_mem_cons.2 ⟨subd12_0_302, List.forall_mem_cons.2 ⟨subd12_0_303, List.forall_mem_cons.2 ⟨subd12_0_304, List.forall_mem_cons.2 ⟨subd12_0_305, List.forall_mem_cons.2 ⟨subd12_0_306, List.forall_mem_cons.2 ⟨subd12_0_307, List.forall_mem_cons.2 ⟨subd12_0_308, List.forall_mem_cons.2 ⟨subd12_0_309, List.forall_mem_cons.2 ⟨subd12_0_310, List.forall_mem_cons.2 ⟨subd12_0_311, List.forall_mem_cons.2 ⟨subd12_0_312, List.forall_mem_cons.2 ⟨subd12_0_313, List.forall_mem_cons.2 ⟨subd12_0_314, List.forall_mem_cons.2 ⟨subd12_0_315, List.forall_mem_cons.2 ⟨subd12_0_316, List.forall_mem_cons.2 ⟨subd12_0_317, List.forall_mem_cons.2 ⟨subd12_0_318, List.forall_mem_cons.2 ⟨subd12_0_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_320 : subd12_0 [-2, -1, -3] = true := by decide +kernel
theorem subd12_0_321 : subd12_0 [-2, -1, -2] = true := by decide +kernel
theorem subd12_0_322 : subd12_0 [-2, -1, -1] = true := by decide +kernel
theorem subd12_0_323 : subd12_0 [-2, -1, 0] = true := by decide +kernel
theorem subd12_0_324 : subd12_0 [-2, -1, 1] = true := by decide +kernel
theorem subd12_0_325 : subd12_0 [-2, -1, 2] = true := by decide +kernel
theorem subd12_0_326 : subd12_0 [-2, -1, 3] = true := by decide +kernel
theorem subd12_0_327 : subd12_0 [-2, -1, 4] = true := by decide +kernel
theorem subd12_0_328 : subd12_0 [-2, -1, 5] = true := by decide +kernel
theorem subd12_0_329 : subd12_0 [-2, -1, 6] = true := by decide +kernel
theorem subd12_0_330 : subd12_0 [-2, -1, 7] = true := by decide +kernel
theorem subd12_0_331 : subd12_0 [-2, 0, -8] = true := by decide +kernel
theorem subd12_0_332 : subd12_0 [-2, 0, -7] = true := by decide +kernel
theorem subd12_0_333 : subd12_0 [-2, 0, -6] = true := by decide +kernel
theorem subd12_0_334 : subd12_0 [-2, 0, -5] = true := by decide +kernel
theorem subd12_0_335 : subd12_0 [-2, 0, -4] = true := by decide +kernel
theorem subd12_0_336 : subd12_0 [-2, 0, -3] = true := by decide +kernel
theorem subd12_0_337 : subd12_0 [-2, 0, -2] = true := by decide +kernel
theorem subd12_0_338 : subd12_0 [-2, 0, -1] = true := by decide +kernel
theorem subd12_0_339 : subd12_0 [-2, 0, 0] = true := by decide +kernel
theorem subd12_0_340 : subd12_0 [-2, 0, 1] = true := by decide +kernel
theorem subd12_0_341 : subd12_0 [-2, 0, 2] = true := by decide +kernel
theorem subd12_0_342 : subd12_0 [-2, 0, 3] = true := by decide +kernel
theorem subd12_0_343 : subd12_0 [-2, 0, 4] = true := by decide +kernel
theorem subd12_0_344 : subd12_0 [-2, 0, 5] = true := by decide +kernel
theorem subd12_0_345 : subd12_0 [-2, 0, 6] = true := by decide +kernel
theorem subd12_0_346 : subd12_0 [-2, 0, 7] = true := by decide +kernel
theorem subd12_0_347 : subd12_0 [-2, 1, -8] = true := by decide +kernel
theorem subd12_0_348 : subd12_0 [-2, 1, -7] = true := by decide +kernel
theorem subd12_0_349 : subd12_0 [-2, 1, -6] = true := by decide +kernel
theorem subd12_0_350 : subd12_0 [-2, 1, -5] = true := by decide +kernel
theorem subd12_0_351 : subd12_0 [-2, 1, -4] = true := by decide +kernel
theorem sbd12_0_10 : ∀ q ∈ blkd12_0_10, subd12_0 q = true := by
  unfold blkd12_0_10
  exact List.forall_mem_cons.2 ⟨subd12_0_320, List.forall_mem_cons.2 ⟨subd12_0_321, List.forall_mem_cons.2 ⟨subd12_0_322, List.forall_mem_cons.2 ⟨subd12_0_323, List.forall_mem_cons.2 ⟨subd12_0_324, List.forall_mem_cons.2 ⟨subd12_0_325, List.forall_mem_cons.2 ⟨subd12_0_326, List.forall_mem_cons.2 ⟨subd12_0_327, List.forall_mem_cons.2 ⟨subd12_0_328, List.forall_mem_cons.2 ⟨subd12_0_329, List.forall_mem_cons.2 ⟨subd12_0_330, List.forall_mem_cons.2 ⟨subd12_0_331, List.forall_mem_cons.2 ⟨subd12_0_332, List.forall_mem_cons.2 ⟨subd12_0_333, List.forall_mem_cons.2 ⟨subd12_0_334, List.forall_mem_cons.2 ⟨subd12_0_335, List.forall_mem_cons.2 ⟨subd12_0_336, List.forall_mem_cons.2 ⟨subd12_0_337, List.forall_mem_cons.2 ⟨subd12_0_338, List.forall_mem_cons.2 ⟨subd12_0_339, List.forall_mem_cons.2 ⟨subd12_0_340, List.forall_mem_cons.2 ⟨subd12_0_341, List.forall_mem_cons.2 ⟨subd12_0_342, List.forall_mem_cons.2 ⟨subd12_0_343, List.forall_mem_cons.2 ⟨subd12_0_344, List.forall_mem_cons.2 ⟨subd12_0_345, List.forall_mem_cons.2 ⟨subd12_0_346, List.forall_mem_cons.2 ⟨subd12_0_347, List.forall_mem_cons.2 ⟨subd12_0_348, List.forall_mem_cons.2 ⟨subd12_0_349, List.forall_mem_cons.2 ⟨subd12_0_350, List.forall_mem_cons.2 ⟨subd12_0_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_352 : subd12_0 [-2, 1, -3] = true := by decide +kernel
theorem subd12_0_353 : subd12_0 [-2, 1, -2] = true := by decide +kernel
theorem subd12_0_354 : subd12_0 [-2, 1, -1] = true := by decide +kernel
theorem subd12_0_355 : subd12_0 [-2, 1, 0] = true := by decide +kernel
theorem subd12_0_356 : subd12_0 [-2, 1, 1] = true := by decide +kernel
theorem subd12_0_357 : subd12_0 [-2, 1, 2] = true := by decide +kernel
theorem subd12_0_358 : subd12_0 [-2, 1, 3] = true := by decide +kernel
theorem subd12_0_359 : subd12_0 [-2, 1, 4] = true := by decide +kernel
theorem subd12_0_360 : subd12_0 [-2, 1, 5] = true := by decide +kernel
theorem subd12_0_361 : subd12_0 [-2, 1, 6] = true := by decide +kernel
theorem subd12_0_362 : subd12_0 [-2, 1, 7] = true := by decide +kernel
theorem subd12_0_363 : subd12_0 [-2, 1, 8] = true := by decide +kernel
theorem subd12_0_364 : subd12_0 [-2, 2, -7] = true := by decide +kernel
theorem subd12_0_365 : subd12_0 [-2, 2, -6] = true := by decide +kernel
theorem subd12_0_366 : subd12_0 [-2, 2, -5] = true := by decide +kernel
theorem subd12_0_367 : subd12_0 [-2, 2, -4] = true := by decide +kernel
theorem subd12_0_368 : subd12_0 [-2, 2, -3] = true := by decide +kernel
theorem subd12_0_369 : subd12_0 [-2, 2, -2] = true := by decide +kernel
theorem subd12_0_370 : subd12_0 [-2, 2, -1] = true := by decide +kernel
theorem subd12_0_371 : subd12_0 [-2, 2, 0] = true := by decide +kernel
theorem subd12_0_372 : subd12_0 [-2, 2, 1] = true := by decide +kernel
theorem subd12_0_373 : subd12_0 [-2, 2, 2] = true := by decide +kernel
theorem subd12_0_374 : subd12_0 [-2, 2, 3] = true := by decide +kernel
theorem subd12_0_375 : subd12_0 [-2, 2, 4] = true := by decide +kernel
theorem subd12_0_376 : subd12_0 [-2, 2, 5] = true := by decide +kernel
theorem subd12_0_377 : subd12_0 [-2, 2, 6] = true := by decide +kernel
theorem subd12_0_378 : subd12_0 [-2, 2, 7] = true := by decide +kernel
theorem subd12_0_379 : subd12_0 [-2, 2, 8] = true := by decide +kernel
theorem subd12_0_380 : subd12_0 [-2, 3, -7] = true := by decide +kernel
theorem subd12_0_381 : subd12_0 [-2, 3, -6] = true := by decide +kernel
theorem subd12_0_382 : subd12_0 [-2, 3, -5] = true := by decide +kernel
theorem subd12_0_383 : subd12_0 [-2, 3, -4] = true := by decide +kernel
theorem sbd12_0_11 : ∀ q ∈ blkd12_0_11, subd12_0 q = true := by
  unfold blkd12_0_11
  exact List.forall_mem_cons.2 ⟨subd12_0_352, List.forall_mem_cons.2 ⟨subd12_0_353, List.forall_mem_cons.2 ⟨subd12_0_354, List.forall_mem_cons.2 ⟨subd12_0_355, List.forall_mem_cons.2 ⟨subd12_0_356, List.forall_mem_cons.2 ⟨subd12_0_357, List.forall_mem_cons.2 ⟨subd12_0_358, List.forall_mem_cons.2 ⟨subd12_0_359, List.forall_mem_cons.2 ⟨subd12_0_360, List.forall_mem_cons.2 ⟨subd12_0_361, List.forall_mem_cons.2 ⟨subd12_0_362, List.forall_mem_cons.2 ⟨subd12_0_363, List.forall_mem_cons.2 ⟨subd12_0_364, List.forall_mem_cons.2 ⟨subd12_0_365, List.forall_mem_cons.2 ⟨subd12_0_366, List.forall_mem_cons.2 ⟨subd12_0_367, List.forall_mem_cons.2 ⟨subd12_0_368, List.forall_mem_cons.2 ⟨subd12_0_369, List.forall_mem_cons.2 ⟨subd12_0_370, List.forall_mem_cons.2 ⟨subd12_0_371, List.forall_mem_cons.2 ⟨subd12_0_372, List.forall_mem_cons.2 ⟨subd12_0_373, List.forall_mem_cons.2 ⟨subd12_0_374, List.forall_mem_cons.2 ⟨subd12_0_375, List.forall_mem_cons.2 ⟨subd12_0_376, List.forall_mem_cons.2 ⟨subd12_0_377, List.forall_mem_cons.2 ⟨subd12_0_378, List.forall_mem_cons.2 ⟨subd12_0_379, List.forall_mem_cons.2 ⟨subd12_0_380, List.forall_mem_cons.2 ⟨subd12_0_381, List.forall_mem_cons.2 ⟨subd12_0_382, List.forall_mem_cons.2 ⟨subd12_0_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_384 : subd12_0 [-2, 3, -3] = true := by decide +kernel
theorem subd12_0_385 : subd12_0 [-2, 3, -2] = true := by decide +kernel
theorem subd12_0_386 : subd12_0 [-2, 3, -1] = true := by decide +kernel
theorem subd12_0_387 : subd12_0 [-2, 3, 0] = true := by decide +kernel
theorem subd12_0_388 : subd12_0 [-2, 3, 1] = true := by decide +kernel
theorem subd12_0_389 : subd12_0 [-2, 3, 2] = true := by decide +kernel
theorem subd12_0_390 : subd12_0 [-2, 3, 3] = true := by decide +kernel
theorem subd12_0_391 : subd12_0 [-2, 3, 4] = true := by decide +kernel
theorem subd12_0_392 : subd12_0 [-2, 3, 5] = true := by decide +kernel
theorem subd12_0_393 : subd12_0 [-2, 3, 6] = true := by decide +kernel
theorem subd12_0_394 : subd12_0 [-2, 3, 7] = true := by decide +kernel
theorem subd12_0_395 : subd12_0 [-2, 3, 8] = true := by decide +kernel
theorem subd12_0_396 : subd12_0 [-2, 4, -6] = true := by decide +kernel
theorem subd12_0_397 : subd12_0 [-2, 4, -5] = true := by decide +kernel
theorem subd12_0_398 : subd12_0 [-2, 4, -4] = true := by decide +kernel
theorem subd12_0_399 : subd12_0 [-2, 4, -3] = true := by decide +kernel
theorem subd12_0_400 : subd12_0 [-2, 4, -2] = true := by decide +kernel
theorem subd12_0_401 : subd12_0 [-2, 4, -1] = true := by decide +kernel
theorem subd12_0_402 : subd12_0 [-2, 4, 0] = true := by decide +kernel
theorem subd12_0_403 : subd12_0 [-2, 4, 1] = true := by decide +kernel
theorem subd12_0_404 : subd12_0 [-2, 4, 2] = true := by decide +kernel
theorem subd12_0_405 : subd12_0 [-2, 4, 3] = true := by decide +kernel
theorem subd12_0_406 : subd12_0 [-2, 4, 4] = true := by decide +kernel
theorem subd12_0_407 : subd12_0 [-2, 4, 5] = true := by decide +kernel
theorem subd12_0_408 : subd12_0 [-2, 4, 6] = true := by decide +kernel
theorem subd12_0_409 : subd12_0 [-2, 4, 7] = true := by decide +kernel
theorem subd12_0_410 : subd12_0 [-2, 4, 8] = true := by decide +kernel
theorem subd12_0_411 : subd12_0 [-2, 5, -5] = true := by decide +kernel
theorem subd12_0_412 : subd12_0 [-2, 5, -4] = true := by decide +kernel
theorem subd12_0_413 : subd12_0 [-2, 5, -3] = true := by decide +kernel
theorem subd12_0_414 : subd12_0 [-2, 5, -2] = true := by decide +kernel
theorem subd12_0_415 : subd12_0 [-2, 5, -1] = true := by decide +kernel
theorem sbd12_0_12 : ∀ q ∈ blkd12_0_12, subd12_0 q = true := by
  unfold blkd12_0_12
  exact List.forall_mem_cons.2 ⟨subd12_0_384, List.forall_mem_cons.2 ⟨subd12_0_385, List.forall_mem_cons.2 ⟨subd12_0_386, List.forall_mem_cons.2 ⟨subd12_0_387, List.forall_mem_cons.2 ⟨subd12_0_388, List.forall_mem_cons.2 ⟨subd12_0_389, List.forall_mem_cons.2 ⟨subd12_0_390, List.forall_mem_cons.2 ⟨subd12_0_391, List.forall_mem_cons.2 ⟨subd12_0_392, List.forall_mem_cons.2 ⟨subd12_0_393, List.forall_mem_cons.2 ⟨subd12_0_394, List.forall_mem_cons.2 ⟨subd12_0_395, List.forall_mem_cons.2 ⟨subd12_0_396, List.forall_mem_cons.2 ⟨subd12_0_397, List.forall_mem_cons.2 ⟨subd12_0_398, List.forall_mem_cons.2 ⟨subd12_0_399, List.forall_mem_cons.2 ⟨subd12_0_400, List.forall_mem_cons.2 ⟨subd12_0_401, List.forall_mem_cons.2 ⟨subd12_0_402, List.forall_mem_cons.2 ⟨subd12_0_403, List.forall_mem_cons.2 ⟨subd12_0_404, List.forall_mem_cons.2 ⟨subd12_0_405, List.forall_mem_cons.2 ⟨subd12_0_406, List.forall_mem_cons.2 ⟨subd12_0_407, List.forall_mem_cons.2 ⟨subd12_0_408, List.forall_mem_cons.2 ⟨subd12_0_409, List.forall_mem_cons.2 ⟨subd12_0_410, List.forall_mem_cons.2 ⟨subd12_0_411, List.forall_mem_cons.2 ⟨subd12_0_412, List.forall_mem_cons.2 ⟨subd12_0_413, List.forall_mem_cons.2 ⟨subd12_0_414, List.forall_mem_cons.2 ⟨subd12_0_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_416 : subd12_0 [-2, 5, 0] = true := by decide +kernel
theorem subd12_0_417 : subd12_0 [-2, 5, 1] = true := by decide +kernel
theorem subd12_0_418 : subd12_0 [-2, 5, 2] = true := by decide +kernel
theorem subd12_0_419 : subd12_0 [-2, 5, 3] = true := by decide +kernel
theorem subd12_0_420 : subd12_0 [-2, 5, 4] = true := by decide +kernel
theorem subd12_0_421 : subd12_0 [-2, 5, 5] = true := by decide +kernel
theorem subd12_0_422 : subd12_0 [-2, 5, 6] = true := by decide +kernel
theorem subd12_0_423 : subd12_0 [-2, 5, 7] = true := by decide +kernel
theorem subd12_0_424 : subd12_0 [-2, 5, 8] = true := by decide +kernel
theorem subd12_0_425 : subd12_0 [-2, 6] = true := by decide +kernel
theorem subd12_0_426 : subd12_0 [-2, 7] = true := by decide +kernel
theorem subd12_0_427 : subd12_0 [-2, 8] = true := by decide +kernel
theorem subd12_0_428 : subd12_0 [-1, -9] = true := by decide +kernel
theorem subd12_0_429 : subd12_0 [-1, -8] = true := by decide +kernel
theorem subd12_0_430 : subd12_0 [-1, -7] = true := by decide +kernel
theorem subd12_0_431 : subd12_0 [-1, -6] = true := by decide +kernel
theorem subd12_0_432 : subd12_0 [-1, -5] = true := by decide +kernel
theorem subd12_0_433 : subd12_0 [-1, -4, -9] = true := by decide +kernel
theorem subd12_0_434 : subd12_0 [-1, -4, -8] = true := by decide +kernel
theorem subd12_0_435 : subd12_0 [-1, -4, -7] = true := by decide +kernel
theorem subd12_0_436 : subd12_0 [-1, -4, -6] = true := by decide +kernel
theorem subd12_0_437 : subd12_0 [-1, -4, -5] = true := by decide +kernel
theorem subd12_0_438 : subd12_0 [-1, -4, -4] = true := by decide +kernel
theorem subd12_0_439 : subd12_0 [-1, -4, -3] = true := by decide +kernel
theorem subd12_0_440 : subd12_0 [-1, -4, -2] = true := by decide +kernel
theorem subd12_0_441 : subd12_0 [-1, -4, -1] = true := by decide +kernel
theorem subd12_0_442 : subd12_0 [-1, -4, 0] = true := by decide +kernel
theorem subd12_0_443 : subd12_0 [-1, -4, 1] = true := by decide +kernel
theorem subd12_0_444 : subd12_0 [-1, -4, 2] = true := by decide +kernel
theorem subd12_0_445 : subd12_0 [-1, -4, 3] = true := by decide +kernel
theorem subd12_0_446 : subd12_0 [-1, -4, 4] = true := by decide +kernel
theorem subd12_0_447 : subd12_0 [-1, -4, 5] = true := by decide +kernel
theorem sbd12_0_13 : ∀ q ∈ blkd12_0_13, subd12_0 q = true := by
  unfold blkd12_0_13
  exact List.forall_mem_cons.2 ⟨subd12_0_416, List.forall_mem_cons.2 ⟨subd12_0_417, List.forall_mem_cons.2 ⟨subd12_0_418, List.forall_mem_cons.2 ⟨subd12_0_419, List.forall_mem_cons.2 ⟨subd12_0_420, List.forall_mem_cons.2 ⟨subd12_0_421, List.forall_mem_cons.2 ⟨subd12_0_422, List.forall_mem_cons.2 ⟨subd12_0_423, List.forall_mem_cons.2 ⟨subd12_0_424, List.forall_mem_cons.2 ⟨subd12_0_425, List.forall_mem_cons.2 ⟨subd12_0_426, List.forall_mem_cons.2 ⟨subd12_0_427, List.forall_mem_cons.2 ⟨subd12_0_428, List.forall_mem_cons.2 ⟨subd12_0_429, List.forall_mem_cons.2 ⟨subd12_0_430, List.forall_mem_cons.2 ⟨subd12_0_431, List.forall_mem_cons.2 ⟨subd12_0_432, List.forall_mem_cons.2 ⟨subd12_0_433, List.forall_mem_cons.2 ⟨subd12_0_434, List.forall_mem_cons.2 ⟨subd12_0_435, List.forall_mem_cons.2 ⟨subd12_0_436, List.forall_mem_cons.2 ⟨subd12_0_437, List.forall_mem_cons.2 ⟨subd12_0_438, List.forall_mem_cons.2 ⟨subd12_0_439, List.forall_mem_cons.2 ⟨subd12_0_440, List.forall_mem_cons.2 ⟨subd12_0_441, List.forall_mem_cons.2 ⟨subd12_0_442, List.forall_mem_cons.2 ⟨subd12_0_443, List.forall_mem_cons.2 ⟨subd12_0_444, List.forall_mem_cons.2 ⟨subd12_0_445, List.forall_mem_cons.2 ⟨subd12_0_446, List.forall_mem_cons.2 ⟨subd12_0_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_448 : subd12_0 [-1, -3, -9] = true := by decide +kernel
theorem subd12_0_449 : subd12_0 [-1, -3, -8] = true := by decide +kernel
theorem subd12_0_450 : subd12_0 [-1, -3, -7] = true := by decide +kernel
theorem subd12_0_451 : subd12_0 [-1, -3, -6] = true := by decide +kernel
theorem subd12_0_452 : subd12_0 [-1, -3, -5] = true := by decide +kernel
theorem subd12_0_453 : subd12_0 [-1, -3, -4] = true := by decide +kernel
theorem subd12_0_454 : subd12_0 [-1, -3, -3] = true := by decide +kernel
theorem subd12_0_455 : subd12_0 [-1, -3, -2] = true := by decide +kernel
theorem subd12_0_456 : subd12_0 [-1, -3, -1] = true := by decide +kernel
theorem subd12_0_457 : subd12_0 [-1, -3, 0] = true := by decide +kernel
theorem subd12_0_458 : subd12_0 [-1, -3, 1] = true := by decide +kernel
theorem subd12_0_459 : subd12_0 [-1, -3, 2] = true := by decide +kernel
theorem subd12_0_460 : subd12_0 [-1, -3, 3] = true := by decide +kernel
theorem subd12_0_461 : subd12_0 [-1, -3, 4] = true := by decide +kernel
theorem subd12_0_462 : subd12_0 [-1, -3, 5] = true := by decide +kernel
theorem subd12_0_463 : subd12_0 [-1, -3, 6] = true := by decide +kernel
theorem subd12_0_464 : subd12_0 [-1, -2, -9] = true := by decide +kernel
theorem subd12_0_465 : subd12_0 [-1, -2, -8] = true := by decide +kernel
theorem subd12_0_466 : subd12_0 [-1, -2, -7] = true := by decide +kernel
theorem subd12_0_467 : subd12_0 [-1, -2, -6] = true := by decide +kernel
theorem subd12_0_468 : subd12_0 [-1, -2, -5] = true := by decide +kernel
theorem subd12_0_469 : subd12_0 [-1, -2, -4] = true := by decide +kernel
theorem subd12_0_470 : subd12_0 [-1, -2, -3] = true := by decide +kernel
theorem subd12_0_471 : subd12_0 [-1, -2, -2] = true := by decide +kernel
theorem subd12_0_472 : subd12_0 [-1, -2, -1] = true := by decide +kernel
theorem subd12_0_473 : subd12_0 [-1, -2, 0] = true := by decide +kernel
theorem subd12_0_474 : subd12_0 [-1, -2, 1] = true := by decide +kernel
theorem subd12_0_475 : subd12_0 [-1, -2, 2] = true := by decide +kernel
theorem subd12_0_476 : subd12_0 [-1, -2, 3] = true := by decide +kernel
theorem subd12_0_477 : subd12_0 [-1, -2, 4] = true := by decide +kernel
theorem subd12_0_478 : subd12_0 [-1, -2, 5] = true := by decide +kernel
theorem subd12_0_479 : subd12_0 [-1, -2, 6] = true := by decide +kernel
theorem sbd12_0_14 : ∀ q ∈ blkd12_0_14, subd12_0 q = true := by
  unfold blkd12_0_14
  exact List.forall_mem_cons.2 ⟨subd12_0_448, List.forall_mem_cons.2 ⟨subd12_0_449, List.forall_mem_cons.2 ⟨subd12_0_450, List.forall_mem_cons.2 ⟨subd12_0_451, List.forall_mem_cons.2 ⟨subd12_0_452, List.forall_mem_cons.2 ⟨subd12_0_453, List.forall_mem_cons.2 ⟨subd12_0_454, List.forall_mem_cons.2 ⟨subd12_0_455, List.forall_mem_cons.2 ⟨subd12_0_456, List.forall_mem_cons.2 ⟨subd12_0_457, List.forall_mem_cons.2 ⟨subd12_0_458, List.forall_mem_cons.2 ⟨subd12_0_459, List.forall_mem_cons.2 ⟨subd12_0_460, List.forall_mem_cons.2 ⟨subd12_0_461, List.forall_mem_cons.2 ⟨subd12_0_462, List.forall_mem_cons.2 ⟨subd12_0_463, List.forall_mem_cons.2 ⟨subd12_0_464, List.forall_mem_cons.2 ⟨subd12_0_465, List.forall_mem_cons.2 ⟨subd12_0_466, List.forall_mem_cons.2 ⟨subd12_0_467, List.forall_mem_cons.2 ⟨subd12_0_468, List.forall_mem_cons.2 ⟨subd12_0_469, List.forall_mem_cons.2 ⟨subd12_0_470, List.forall_mem_cons.2 ⟨subd12_0_471, List.forall_mem_cons.2 ⟨subd12_0_472, List.forall_mem_cons.2 ⟨subd12_0_473, List.forall_mem_cons.2 ⟨subd12_0_474, List.forall_mem_cons.2 ⟨subd12_0_475, List.forall_mem_cons.2 ⟨subd12_0_476, List.forall_mem_cons.2 ⟨subd12_0_477, List.forall_mem_cons.2 ⟨subd12_0_478, List.forall_mem_cons.2 ⟨subd12_0_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_480 : subd12_0 [-1, -1, -9] = true := by decide +kernel
theorem subd12_0_481 : subd12_0 [-1, -1, -8] = true := by decide +kernel
theorem subd12_0_482 : subd12_0 [-1, -1, -7] = true := by decide +kernel
theorem subd12_0_483 : subd12_0 [-1, -1, -6] = true := by decide +kernel
theorem subd12_0_484 : subd12_0 [-1, -1, -5] = true := by decide +kernel
theorem subd12_0_485 : subd12_0 [-1, -1, -4] = true := by decide +kernel
theorem subd12_0_486 : subd12_0 [-1, -1, -3] = true := by decide +kernel
theorem subd12_0_487 : subd12_0 [-1, -1, -2] = true := by decide +kernel
theorem subd12_0_488 : subd12_0 [-1, -1, -1] = true := by decide +kernel
theorem subd12_0_489 : subd12_0 [-1, -1, 0] = true := by decide +kernel
theorem subd12_0_490 : subd12_0 [-1, -1, 1] = true := by decide +kernel
theorem subd12_0_491 : subd12_0 [-1, -1, 2] = true := by decide +kernel
theorem subd12_0_492 : subd12_0 [-1, -1, 3] = true := by decide +kernel
theorem subd12_0_493 : subd12_0 [-1, -1, 4] = true := by decide +kernel
theorem subd12_0_494 : subd12_0 [-1, -1, 5] = true := by decide +kernel
theorem subd12_0_495 : subd12_0 [-1, -1, 6] = true := by decide +kernel
theorem subd12_0_496 : subd12_0 [-1, -1, 7] = true := by decide +kernel
theorem subd12_0_497 : subd12_0 [-1, 0, -9] = true := by decide +kernel
theorem subd12_0_498 : subd12_0 [-1, 0, -8] = true := by decide +kernel
theorem subd12_0_499 : subd12_0 [-1, 0, -7] = true := by decide +kernel
theorem subd12_0_500 : subd12_0 [-1, 0, -6] = true := by decide +kernel
theorem subd12_0_501 : subd12_0 [-1, 0, -5] = true := by decide +kernel
theorem subd12_0_502 : subd12_0 [-1, 0, -4] = true := by decide +kernel
theorem subd12_0_503 : subd12_0 [-1, 0, -3] = true := by decide +kernel
theorem subd12_0_504 : subd12_0 [-1, 0, -2] = true := by decide +kernel
theorem subd12_0_505 : subd12_0 [-1, 0, -1] = true := by decide +kernel
theorem subd12_0_506 : subd12_0 [-1, 0, 0] = true := by decide +kernel
theorem subd12_0_507 : subd12_0 [-1, 0, 1] = true := by decide +kernel
theorem subd12_0_508 : subd12_0 [-1, 0, 2] = true := by decide +kernel
theorem subd12_0_509 : subd12_0 [-1, 0, 3] = true := by decide +kernel
theorem subd12_0_510 : subd12_0 [-1, 0, 4] = true := by decide +kernel
theorem subd12_0_511 : subd12_0 [-1, 0, 5] = true := by decide +kernel
theorem sbd12_0_15 : ∀ q ∈ blkd12_0_15, subd12_0 q = true := by
  unfold blkd12_0_15
  exact List.forall_mem_cons.2 ⟨subd12_0_480, List.forall_mem_cons.2 ⟨subd12_0_481, List.forall_mem_cons.2 ⟨subd12_0_482, List.forall_mem_cons.2 ⟨subd12_0_483, List.forall_mem_cons.2 ⟨subd12_0_484, List.forall_mem_cons.2 ⟨subd12_0_485, List.forall_mem_cons.2 ⟨subd12_0_486, List.forall_mem_cons.2 ⟨subd12_0_487, List.forall_mem_cons.2 ⟨subd12_0_488, List.forall_mem_cons.2 ⟨subd12_0_489, List.forall_mem_cons.2 ⟨subd12_0_490, List.forall_mem_cons.2 ⟨subd12_0_491, List.forall_mem_cons.2 ⟨subd12_0_492, List.forall_mem_cons.2 ⟨subd12_0_493, List.forall_mem_cons.2 ⟨subd12_0_494, List.forall_mem_cons.2 ⟨subd12_0_495, List.forall_mem_cons.2 ⟨subd12_0_496, List.forall_mem_cons.2 ⟨subd12_0_497, List.forall_mem_cons.2 ⟨subd12_0_498, List.forall_mem_cons.2 ⟨subd12_0_499, List.forall_mem_cons.2 ⟨subd12_0_500, List.forall_mem_cons.2 ⟨subd12_0_501, List.forall_mem_cons.2 ⟨subd12_0_502, List.forall_mem_cons.2 ⟨subd12_0_503, List.forall_mem_cons.2 ⟨subd12_0_504, List.forall_mem_cons.2 ⟨subd12_0_505, List.forall_mem_cons.2 ⟨subd12_0_506, List.forall_mem_cons.2 ⟨subd12_0_507, List.forall_mem_cons.2 ⟨subd12_0_508, List.forall_mem_cons.2 ⟨subd12_0_509, List.forall_mem_cons.2 ⟨subd12_0_510, List.forall_mem_cons.2 ⟨subd12_0_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_512 : subd12_0 [-1, 0, 6] = true := by decide +kernel
theorem subd12_0_513 : subd12_0 [-1, 0, 7] = true := by decide +kernel
theorem subd12_0_514 : subd12_0 [-1, 1, -8] = true := by decide +kernel
theorem subd12_0_515 : subd12_0 [-1, 1, -7] = true := by decide +kernel
theorem subd12_0_516 : subd12_0 [-1, 1, -6] = true := by decide +kernel
theorem subd12_0_517 : subd12_0 [-1, 1, -5] = true := by decide +kernel
theorem subd12_0_518 : subd12_0 [-1, 1, -4] = true := by decide +kernel
theorem subd12_0_519 : subd12_0 [-1, 1, -3] = true := by decide +kernel
theorem subd12_0_520 : subd12_0 [-1, 1, -2] = true := by decide +kernel
theorem subd12_0_521 : subd12_0 [-1, 1, -1] = true := by decide +kernel
theorem subd12_0_522 : subd12_0 [-1, 1, 0] = true := by decide +kernel
theorem subd12_0_523 : subd12_0 [-1, 1, 1] = true := by decide +kernel
theorem subd12_0_524 : subd12_0 [-1, 1, 2] = true := by decide +kernel
theorem subd12_0_525 : subd12_0 [-1, 1, 3] = true := by decide +kernel
theorem subd12_0_526 : subd12_0 [-1, 1, 4] = true := by decide +kernel
theorem subd12_0_527 : subd12_0 [-1, 1, 5] = true := by decide +kernel
theorem subd12_0_528 : subd12_0 [-1, 1, 6] = true := by decide +kernel
theorem subd12_0_529 : subd12_0 [-1, 1, 7] = true := by decide +kernel
theorem subd12_0_530 : subd12_0 [-1, 1, 8] = true := by decide +kernel
theorem subd12_0_531 : subd12_0 [-1, 2, -8] = true := by decide +kernel
theorem subd12_0_532 : subd12_0 [-1, 2, -7] = true := by decide +kernel
theorem subd12_0_533 : subd12_0 [-1, 2, -6] = true := by decide +kernel
theorem subd12_0_534 : subd12_0 [-1, 2, -5] = true := by decide +kernel
theorem subd12_0_535 : subd12_0 [-1, 2, -4] = true := by decide +kernel
theorem subd12_0_536 : subd12_0 [-1, 2, -3] = true := by decide +kernel
theorem subd12_0_537 : subd12_0 [-1, 2, -2] = true := by decide +kernel
theorem subd12_0_538 : subd12_0 [-1, 2, -1] = true := by decide +kernel
theorem subd12_0_539 : subd12_0 [-1, 2, 0] = true := by decide +kernel
theorem subd12_0_540 : subd12_0 [-1, 2, 1] = true := by decide +kernel
theorem subd12_0_541 : subd12_0 [-1, 2, 2] = true := by decide +kernel
theorem subd12_0_542 : subd12_0 [-1, 2, 3] = true := by decide +kernel
theorem subd12_0_543 : subd12_0 [-1, 2, 4] = true := by decide +kernel
theorem sbd12_0_16 : ∀ q ∈ blkd12_0_16, subd12_0 q = true := by
  unfold blkd12_0_16
  exact List.forall_mem_cons.2 ⟨subd12_0_512, List.forall_mem_cons.2 ⟨subd12_0_513, List.forall_mem_cons.2 ⟨subd12_0_514, List.forall_mem_cons.2 ⟨subd12_0_515, List.forall_mem_cons.2 ⟨subd12_0_516, List.forall_mem_cons.2 ⟨subd12_0_517, List.forall_mem_cons.2 ⟨subd12_0_518, List.forall_mem_cons.2 ⟨subd12_0_519, List.forall_mem_cons.2 ⟨subd12_0_520, List.forall_mem_cons.2 ⟨subd12_0_521, List.forall_mem_cons.2 ⟨subd12_0_522, List.forall_mem_cons.2 ⟨subd12_0_523, List.forall_mem_cons.2 ⟨subd12_0_524, List.forall_mem_cons.2 ⟨subd12_0_525, List.forall_mem_cons.2 ⟨subd12_0_526, List.forall_mem_cons.2 ⟨subd12_0_527, List.forall_mem_cons.2 ⟨subd12_0_528, List.forall_mem_cons.2 ⟨subd12_0_529, List.forall_mem_cons.2 ⟨subd12_0_530, List.forall_mem_cons.2 ⟨subd12_0_531, List.forall_mem_cons.2 ⟨subd12_0_532, List.forall_mem_cons.2 ⟨subd12_0_533, List.forall_mem_cons.2 ⟨subd12_0_534, List.forall_mem_cons.2 ⟨subd12_0_535, List.forall_mem_cons.2 ⟨subd12_0_536, List.forall_mem_cons.2 ⟨subd12_0_537, List.forall_mem_cons.2 ⟨subd12_0_538, List.forall_mem_cons.2 ⟨subd12_0_539, List.forall_mem_cons.2 ⟨subd12_0_540, List.forall_mem_cons.2 ⟨subd12_0_541, List.forall_mem_cons.2 ⟨subd12_0_542, List.forall_mem_cons.2 ⟨subd12_0_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_544 : subd12_0 [-1, 2, 5] = true := by decide +kernel
theorem subd12_0_545 : subd12_0 [-1, 2, 6] = true := by decide +kernel
theorem subd12_0_546 : subd12_0 [-1, 2, 7] = true := by decide +kernel
theorem subd12_0_547 : subd12_0 [-1, 2, 8] = true := by decide +kernel
theorem subd12_0_548 : subd12_0 [-1, 3, -7] = true := by decide +kernel
theorem subd12_0_549 : subd12_0 [-1, 3, -6] = true := by decide +kernel
theorem subd12_0_550 : subd12_0 [-1, 3, -5] = true := by decide +kernel
theorem subd12_0_551 : subd12_0 [-1, 3, -4] = true := by decide +kernel
theorem subd12_0_552 : subd12_0 [-1, 3, -3] = true := by decide +kernel
theorem subd12_0_553 : subd12_0 [-1, 3, -2] = true := by decide +kernel
theorem subd12_0_554 : subd12_0 [-1, 3, -1] = true := by decide +kernel
theorem subd12_0_555 : subd12_0 [-1, 3, 0] = true := by decide +kernel
theorem subd12_0_556 : subd12_0 [-1, 3, 1] = true := by decide +kernel
theorem subd12_0_557 : subd12_0 [-1, 3, 2] = true := by decide +kernel
theorem subd12_0_558 : subd12_0 [-1, 3, 3] = true := by decide +kernel
theorem subd12_0_559 : subd12_0 [-1, 3, 4] = true := by decide +kernel
theorem subd12_0_560 : subd12_0 [-1, 3, 5] = true := by decide +kernel
theorem subd12_0_561 : subd12_0 [-1, 3, 6] = true := by decide +kernel
theorem subd12_0_562 : subd12_0 [-1, 3, 7] = true := by decide +kernel
theorem subd12_0_563 : subd12_0 [-1, 3, 8] = true := by decide +kernel
theorem subd12_0_564 : subd12_0 [-1, 4, -6] = true := by decide +kernel
theorem subd12_0_565 : subd12_0 [-1, 4, -5] = true := by decide +kernel
theorem subd12_0_566 : subd12_0 [-1, 4, -4] = true := by decide +kernel
theorem subd12_0_567 : subd12_0 [-1, 4, -3] = true := by decide +kernel
theorem subd12_0_568 : subd12_0 [-1, 4, -2] = true := by decide +kernel
theorem subd12_0_569 : subd12_0 [-1, 4, -1] = true := by decide +kernel
theorem subd12_0_570 : subd12_0 [-1, 4, 0] = true := by decide +kernel
theorem subd12_0_571 : subd12_0 [-1, 4, 1] = true := by decide +kernel
theorem subd12_0_572 : subd12_0 [-1, 4, 2] = true := by decide +kernel
theorem subd12_0_573 : subd12_0 [-1, 4, 3] = true := by decide +kernel
theorem subd12_0_574 : subd12_0 [-1, 4, 4] = true := by decide +kernel
theorem subd12_0_575 : subd12_0 [-1, 4, 5] = true := by decide +kernel
theorem sbd12_0_17 : ∀ q ∈ blkd12_0_17, subd12_0 q = true := by
  unfold blkd12_0_17
  exact List.forall_mem_cons.2 ⟨subd12_0_544, List.forall_mem_cons.2 ⟨subd12_0_545, List.forall_mem_cons.2 ⟨subd12_0_546, List.forall_mem_cons.2 ⟨subd12_0_547, List.forall_mem_cons.2 ⟨subd12_0_548, List.forall_mem_cons.2 ⟨subd12_0_549, List.forall_mem_cons.2 ⟨subd12_0_550, List.forall_mem_cons.2 ⟨subd12_0_551, List.forall_mem_cons.2 ⟨subd12_0_552, List.forall_mem_cons.2 ⟨subd12_0_553, List.forall_mem_cons.2 ⟨subd12_0_554, List.forall_mem_cons.2 ⟨subd12_0_555, List.forall_mem_cons.2 ⟨subd12_0_556, List.forall_mem_cons.2 ⟨subd12_0_557, List.forall_mem_cons.2 ⟨subd12_0_558, List.forall_mem_cons.2 ⟨subd12_0_559, List.forall_mem_cons.2 ⟨subd12_0_560, List.forall_mem_cons.2 ⟨subd12_0_561, List.forall_mem_cons.2 ⟨subd12_0_562, List.forall_mem_cons.2 ⟨subd12_0_563, List.forall_mem_cons.2 ⟨subd12_0_564, List.forall_mem_cons.2 ⟨subd12_0_565, List.forall_mem_cons.2 ⟨subd12_0_566, List.forall_mem_cons.2 ⟨subd12_0_567, List.forall_mem_cons.2 ⟨subd12_0_568, List.forall_mem_cons.2 ⟨subd12_0_569, List.forall_mem_cons.2 ⟨subd12_0_570, List.forall_mem_cons.2 ⟨subd12_0_571, List.forall_mem_cons.2 ⟨subd12_0_572, List.forall_mem_cons.2 ⟨subd12_0_573, List.forall_mem_cons.2 ⟨subd12_0_574, List.forall_mem_cons.2 ⟨subd12_0_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_576 : subd12_0 [-1, 4, 6] = true := by decide +kernel
theorem subd12_0_577 : subd12_0 [-1, 4, 7] = true := by decide +kernel
theorem subd12_0_578 : subd12_0 [-1, 4, 8] = true := by decide +kernel
theorem subd12_0_579 : subd12_0 [-1, 5, -5] = true := by decide +kernel
theorem subd12_0_580 : subd12_0 [-1, 5, -4] = true := by decide +kernel
theorem subd12_0_581 : subd12_0 [-1, 5, -3] = true := by decide +kernel
theorem subd12_0_582 : subd12_0 [-1, 5, -2] = true := by decide +kernel
theorem subd12_0_583 : subd12_0 [-1, 5, -1] = true := by decide +kernel
theorem subd12_0_584 : subd12_0 [-1, 5, 0] = true := by decide +kernel
theorem subd12_0_585 : subd12_0 [-1, 5, 1] = true := by decide +kernel
theorem subd12_0_586 : subd12_0 [-1, 5, 2] = true := by decide +kernel
theorem subd12_0_587 : subd12_0 [-1, 5, 3] = true := by decide +kernel
theorem subd12_0_588 : subd12_0 [-1, 5, 4] = true := by decide +kernel
theorem subd12_0_589 : subd12_0 [-1, 5, 5] = true := by decide +kernel
theorem subd12_0_590 : subd12_0 [-1, 5, 6] = true := by decide +kernel
theorem subd12_0_591 : subd12_0 [-1, 5, 7] = true := by decide +kernel
theorem subd12_0_592 : subd12_0 [-1, 5, 8] = true := by decide +kernel
theorem subd12_0_593 : subd12_0 [-1, 6] = true := by decide +kernel
theorem subd12_0_594 : subd12_0 [-1, 7] = true := by decide +kernel
theorem subd12_0_595 : subd12_0 [-1, 8] = true := by decide +kernel
theorem subd12_0_596 : subd12_0 [0, -9] = true := by decide +kernel
theorem subd12_0_597 : subd12_0 [0, -8] = true := by decide +kernel
theorem subd12_0_598 : subd12_0 [0, -7] = true := by decide +kernel
theorem subd12_0_599 : subd12_0 [0, -6] = true := by decide +kernel
theorem subd12_0_600 : subd12_0 [0, -5, -9] = true := by decide +kernel
theorem subd12_0_601 : subd12_0 [0, -5, -8] = true := by decide +kernel
theorem subd12_0_602 : subd12_0 [0, -5, -7] = true := by decide +kernel
theorem subd12_0_603 : subd12_0 [0, -5, -6] = true := by decide +kernel
theorem subd12_0_604 : subd12_0 [0, -5, -5] = true := by decide +kernel
theorem subd12_0_605 : subd12_0 [0, -5, -4] = true := by decide +kernel
theorem subd12_0_606 : subd12_0 [0, -5, -3] = true := by decide +kernel
theorem subd12_0_607 : subd12_0 [0, -5, -2] = true := by decide +kernel
theorem sbd12_0_18 : ∀ q ∈ blkd12_0_18, subd12_0 q = true := by
  unfold blkd12_0_18
  exact List.forall_mem_cons.2 ⟨subd12_0_576, List.forall_mem_cons.2 ⟨subd12_0_577, List.forall_mem_cons.2 ⟨subd12_0_578, List.forall_mem_cons.2 ⟨subd12_0_579, List.forall_mem_cons.2 ⟨subd12_0_580, List.forall_mem_cons.2 ⟨subd12_0_581, List.forall_mem_cons.2 ⟨subd12_0_582, List.forall_mem_cons.2 ⟨subd12_0_583, List.forall_mem_cons.2 ⟨subd12_0_584, List.forall_mem_cons.2 ⟨subd12_0_585, List.forall_mem_cons.2 ⟨subd12_0_586, List.forall_mem_cons.2 ⟨subd12_0_587, List.forall_mem_cons.2 ⟨subd12_0_588, List.forall_mem_cons.2 ⟨subd12_0_589, List.forall_mem_cons.2 ⟨subd12_0_590, List.forall_mem_cons.2 ⟨subd12_0_591, List.forall_mem_cons.2 ⟨subd12_0_592, List.forall_mem_cons.2 ⟨subd12_0_593, List.forall_mem_cons.2 ⟨subd12_0_594, List.forall_mem_cons.2 ⟨subd12_0_595, List.forall_mem_cons.2 ⟨subd12_0_596, List.forall_mem_cons.2 ⟨subd12_0_597, List.forall_mem_cons.2 ⟨subd12_0_598, List.forall_mem_cons.2 ⟨subd12_0_599, List.forall_mem_cons.2 ⟨subd12_0_600, List.forall_mem_cons.2 ⟨subd12_0_601, List.forall_mem_cons.2 ⟨subd12_0_602, List.forall_mem_cons.2 ⟨subd12_0_603, List.forall_mem_cons.2 ⟨subd12_0_604, List.forall_mem_cons.2 ⟨subd12_0_605, List.forall_mem_cons.2 ⟨subd12_0_606, List.forall_mem_cons.2 ⟨subd12_0_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_608 : subd12_0 [0, -5, -1] = true := by decide +kernel
theorem subd12_0_609 : subd12_0 [0, -5, 0] = true := by decide +kernel
theorem subd12_0_610 : subd12_0 [0, -5, 1] = true := by decide +kernel
theorem subd12_0_611 : subd12_0 [0, -5, 2] = true := by decide +kernel
theorem subd12_0_612 : subd12_0 [0, -5, 3] = true := by decide +kernel
theorem subd12_0_613 : subd12_0 [0, -5, 4] = true := by decide +kernel
theorem subd12_0_614 : subd12_0 [0, -4, -9] = true := by decide +kernel
theorem subd12_0_615 : subd12_0 [0, -4, -8] = true := by decide +kernel
theorem subd12_0_616 : subd12_0 [0, -4, -7] = true := by decide +kernel
theorem subd12_0_617 : subd12_0 [0, -4, -6] = true := by decide +kernel
theorem subd12_0_618 : subd12_0 [0, -4, -5] = true := by decide +kernel
theorem subd12_0_619 : subd12_0 [0, -4, -4] = true := by decide +kernel
theorem subd12_0_620 : subd12_0 [0, -4, -3] = true := by decide +kernel
theorem subd12_0_621 : subd12_0 [0, -4, -2] = true := by decide +kernel
theorem subd12_0_622 : subd12_0 [0, -4, -1] = true := by decide +kernel
theorem subd12_0_623 : subd12_0 [0, -4, 0] = true := by decide +kernel
theorem subd12_0_624 : subd12_0 [0, -4, 1] = true := by decide +kernel
theorem subd12_0_625 : subd12_0 [0, -4, 2] = true := by decide +kernel
theorem subd12_0_626 : subd12_0 [0, -4, 3] = true := by decide +kernel
theorem subd12_0_627 : subd12_0 [0, -4, 4] = true := by decide +kernel
theorem subd12_0_628 : subd12_0 [0, -4, 5] = true := by decide +kernel
theorem subd12_0_629 : subd12_0 [0, -3, -9] = true := by decide +kernel
theorem subd12_0_630 : subd12_0 [0, -3, -8] = true := by decide +kernel
theorem subd12_0_631 : subd12_0 [0, -3, -7] = true := by decide +kernel
theorem subd12_0_632 : subd12_0 [0, -3, -6] = true := by decide +kernel
theorem subd12_0_633 : subd12_0 [0, -3, -5] = true := by decide +kernel
theorem subd12_0_634 : subd12_0 [0, -3, -4] = true := by decide +kernel
theorem subd12_0_635 : subd12_0 [0, -3, -3] = true := by decide +kernel
theorem subd12_0_636 : subd12_0 [0, -3, -2] = true := by decide +kernel
theorem subd12_0_637 : subd12_0 [0, -3, -1] = true := by decide +kernel
theorem subd12_0_638 : subd12_0 [0, -3, 0] = true := by decide +kernel
theorem subd12_0_639 : subd12_0 [0, -3, 1] = true := by decide +kernel
theorem sbd12_0_19 : ∀ q ∈ blkd12_0_19, subd12_0 q = true := by
  unfold blkd12_0_19
  exact List.forall_mem_cons.2 ⟨subd12_0_608, List.forall_mem_cons.2 ⟨subd12_0_609, List.forall_mem_cons.2 ⟨subd12_0_610, List.forall_mem_cons.2 ⟨subd12_0_611, List.forall_mem_cons.2 ⟨subd12_0_612, List.forall_mem_cons.2 ⟨subd12_0_613, List.forall_mem_cons.2 ⟨subd12_0_614, List.forall_mem_cons.2 ⟨subd12_0_615, List.forall_mem_cons.2 ⟨subd12_0_616, List.forall_mem_cons.2 ⟨subd12_0_617, List.forall_mem_cons.2 ⟨subd12_0_618, List.forall_mem_cons.2 ⟨subd12_0_619, List.forall_mem_cons.2 ⟨subd12_0_620, List.forall_mem_cons.2 ⟨subd12_0_621, List.forall_mem_cons.2 ⟨subd12_0_622, List.forall_mem_cons.2 ⟨subd12_0_623, List.forall_mem_cons.2 ⟨subd12_0_624, List.forall_mem_cons.2 ⟨subd12_0_625, List.forall_mem_cons.2 ⟨subd12_0_626, List.forall_mem_cons.2 ⟨subd12_0_627, List.forall_mem_cons.2 ⟨subd12_0_628, List.forall_mem_cons.2 ⟨subd12_0_629, List.forall_mem_cons.2 ⟨subd12_0_630, List.forall_mem_cons.2 ⟨subd12_0_631, List.forall_mem_cons.2 ⟨subd12_0_632, List.forall_mem_cons.2 ⟨subd12_0_633, List.forall_mem_cons.2 ⟨subd12_0_634, List.forall_mem_cons.2 ⟨subd12_0_635, List.forall_mem_cons.2 ⟨subd12_0_636, List.forall_mem_cons.2 ⟨subd12_0_637, List.forall_mem_cons.2 ⟨subd12_0_638, List.forall_mem_cons.2 ⟨subd12_0_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_640 : subd12_0 [0, -3, 2] = true := by decide +kernel
theorem subd12_0_641 : subd12_0 [0, -3, 3] = true := by decide +kernel
theorem subd12_0_642 : subd12_0 [0, -3, 4] = true := by decide +kernel
theorem subd12_0_643 : subd12_0 [0, -3, 5] = true := by decide +kernel
theorem subd12_0_644 : subd12_0 [0, -3, 6] = true := by decide +kernel
theorem subd12_0_645 : subd12_0 [0, -2, -9] = true := by decide +kernel
theorem subd12_0_646 : subd12_0 [0, -2, -8] = true := by decide +kernel
theorem subd12_0_647 : subd12_0 [0, -2, -7] = true := by decide +kernel
theorem subd12_0_648 : subd12_0 [0, -2, -6] = true := by decide +kernel
theorem subd12_0_649 : subd12_0 [0, -2, -5] = true := by decide +kernel
theorem subd12_0_650 : subd12_0 [0, -2, -4] = true := by decide +kernel
theorem subd12_0_651 : subd12_0 [0, -2, -3] = true := by decide +kernel
theorem subd12_0_652 : subd12_0 [0, -2, -2] = true := by decide +kernel
theorem subd12_0_653 : subd12_0 [0, -2, -1] = true := by decide +kernel
theorem subd12_0_654 : subd12_0 [0, -2, 0] = true := by decide +kernel
theorem subd12_0_655 : subd12_0 [0, -2, 1] = true := by decide +kernel
theorem subd12_0_656 : subd12_0 [0, -2, 2] = true := by decide +kernel
theorem subd12_0_657 : subd12_0 [0, -2, 3] = true := by decide +kernel
theorem subd12_0_658 : subd12_0 [0, -2, 4] = true := by decide +kernel
theorem subd12_0_659 : subd12_0 [0, -2, 5] = true := by decide +kernel
theorem subd12_0_660 : subd12_0 [0, -2, 6] = true := by decide +kernel
theorem subd12_0_661 : subd12_0 [0, -1, -9] = true := by decide +kernel
theorem subd12_0_662 : subd12_0 [0, -1, -8] = true := by decide +kernel
theorem subd12_0_663 : subd12_0 [0, -1, -7] = true := by decide +kernel
theorem subd12_0_664 : subd12_0 [0, -1, -6] = true := by decide +kernel
theorem subd12_0_665 : subd12_0 [0, -1, -5] = true := by decide +kernel
theorem subd12_0_666 : subd12_0 [0, -1, -4] = true := by decide +kernel
theorem subd12_0_667 : subd12_0 [0, -1, -3] = true := by decide +kernel
theorem subd12_0_668 : subd12_0 [0, -1, -2] = true := by decide +kernel
theorem subd12_0_669 : subd12_0 [0, -1, -1] = true := by decide +kernel
theorem subd12_0_670 : subd12_0 [0, -1, 0] = true := by decide +kernel
theorem subd12_0_671 : subd12_0 [0, -1, 1] = true := by decide +kernel
theorem sbd12_0_20 : ∀ q ∈ blkd12_0_20, subd12_0 q = true := by
  unfold blkd12_0_20
  exact List.forall_mem_cons.2 ⟨subd12_0_640, List.forall_mem_cons.2 ⟨subd12_0_641, List.forall_mem_cons.2 ⟨subd12_0_642, List.forall_mem_cons.2 ⟨subd12_0_643, List.forall_mem_cons.2 ⟨subd12_0_644, List.forall_mem_cons.2 ⟨subd12_0_645, List.forall_mem_cons.2 ⟨subd12_0_646, List.forall_mem_cons.2 ⟨subd12_0_647, List.forall_mem_cons.2 ⟨subd12_0_648, List.forall_mem_cons.2 ⟨subd12_0_649, List.forall_mem_cons.2 ⟨subd12_0_650, List.forall_mem_cons.2 ⟨subd12_0_651, List.forall_mem_cons.2 ⟨subd12_0_652, List.forall_mem_cons.2 ⟨subd12_0_653, List.forall_mem_cons.2 ⟨subd12_0_654, List.forall_mem_cons.2 ⟨subd12_0_655, List.forall_mem_cons.2 ⟨subd12_0_656, List.forall_mem_cons.2 ⟨subd12_0_657, List.forall_mem_cons.2 ⟨subd12_0_658, List.forall_mem_cons.2 ⟨subd12_0_659, List.forall_mem_cons.2 ⟨subd12_0_660, List.forall_mem_cons.2 ⟨subd12_0_661, List.forall_mem_cons.2 ⟨subd12_0_662, List.forall_mem_cons.2 ⟨subd12_0_663, List.forall_mem_cons.2 ⟨subd12_0_664, List.forall_mem_cons.2 ⟨subd12_0_665, List.forall_mem_cons.2 ⟨subd12_0_666, List.forall_mem_cons.2 ⟨subd12_0_667, List.forall_mem_cons.2 ⟨subd12_0_668, List.forall_mem_cons.2 ⟨subd12_0_669, List.forall_mem_cons.2 ⟨subd12_0_670, List.forall_mem_cons.2 ⟨subd12_0_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C131
