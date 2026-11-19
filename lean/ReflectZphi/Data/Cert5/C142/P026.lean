import ReflectZphi.Data.Cert5.C142.Base

namespace ReflectZphi.Data.Cert5.C142

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd14_2_192 : subd14_2 [-2, 2, -1] = true := by decide +kernel
theorem subd14_2_193 : subd14_2 [-2, 2, 0] = true := by decide +kernel
theorem subd14_2_194 : subd14_2 [-2, 2, 1] = true := by decide +kernel
theorem subd14_2_195 : subd14_2 [-2, 2, 2] = true := by decide +kernel
theorem subd14_2_196 : subd14_2 [-2, 2, 3] = true := by decide +kernel
theorem subd14_2_197 : subd14_2 [-2, 2, 4] = true := by decide +kernel
theorem subd14_2_198 : subd14_2 [-2, 2, 5] = true := by decide +kernel
theorem subd14_2_199 : subd14_2 [-2, 2, 6] = true := by decide +kernel
theorem subd14_2_200 : subd14_2 [-2, 2, 7] = true := by decide +kernel
theorem subd14_2_201 : subd14_2 [-2, 3, -8] = true := by decide +kernel
theorem subd14_2_202 : subd14_2 [-2, 3, -7] = true := by decide +kernel
theorem subd14_2_203 : subd14_2 [-2, 3, -6] = true := by decide +kernel
theorem subd14_2_204 : subd14_2 [-2, 3, -5] = true := by decide +kernel
theorem subd14_2_205 : subd14_2 [-2, 3, -4] = true := by decide +kernel
theorem subd14_2_206 : subd14_2 [-2, 3, -3] = true := by decide +kernel
theorem subd14_2_207 : subd14_2 [-2, 3, -2] = true := by decide +kernel
theorem subd14_2_208 : subd14_2 [-2, 3, -1] = true := by decide +kernel
theorem subd14_2_209 : subd14_2 [-2, 3, 0] = true := by decide +kernel
theorem subd14_2_210 : subd14_2 [-2, 3, 1] = true := by decide +kernel
theorem subd14_2_211 : subd14_2 [-2, 3, 2] = true := by decide +kernel
theorem subd14_2_212 : subd14_2 [-2, 3, 3] = true := by decide +kernel
theorem subd14_2_213 : subd14_2 [-2, 3, 4] = true := by decide +kernel
theorem subd14_2_214 : subd14_2 [-2, 3, 5] = true := by decide +kernel
theorem subd14_2_215 : subd14_2 [-2, 3, 6] = true := by decide +kernel
theorem subd14_2_216 : subd14_2 [-2, 3, 7] = true := by decide +kernel
theorem subd14_2_217 : subd14_2 [-2, 4, -8] = true := by decide +kernel
theorem subd14_2_218 : subd14_2 [-2, 4, -7] = true := by decide +kernel
theorem subd14_2_219 : subd14_2 [-2, 4, -6] = true := by decide +kernel
theorem subd14_2_220 : subd14_2 [-2, 4, -5] = true := by decide +kernel
theorem subd14_2_221 : subd14_2 [-2, 4, -4] = true := by decide +kernel
theorem subd14_2_222 : subd14_2 [-2, 4, -3] = true := by decide +kernel
theorem subd14_2_223 : subd14_2 [-2, 4, -2] = true := by decide +kernel
theorem sbd14_2_6 : ∀ q ∈ blkd14_2_6, subd14_2 q = true := by
  unfold blkd14_2_6
  exact List.forall_mem_cons.2 ⟨subd14_2_192, List.forall_mem_cons.2 ⟨subd14_2_193, List.forall_mem_cons.2 ⟨subd14_2_194, List.forall_mem_cons.2 ⟨subd14_2_195, List.forall_mem_cons.2 ⟨subd14_2_196, List.forall_mem_cons.2 ⟨subd14_2_197, List.forall_mem_cons.2 ⟨subd14_2_198, List.forall_mem_cons.2 ⟨subd14_2_199, List.forall_mem_cons.2 ⟨subd14_2_200, List.forall_mem_cons.2 ⟨subd14_2_201, List.forall_mem_cons.2 ⟨subd14_2_202, List.forall_mem_cons.2 ⟨subd14_2_203, List.forall_mem_cons.2 ⟨subd14_2_204, List.forall_mem_cons.2 ⟨subd14_2_205, List.forall_mem_cons.2 ⟨subd14_2_206, List.forall_mem_cons.2 ⟨subd14_2_207, List.forall_mem_cons.2 ⟨subd14_2_208, List.forall_mem_cons.2 ⟨subd14_2_209, List.forall_mem_cons.2 ⟨subd14_2_210, List.forall_mem_cons.2 ⟨subd14_2_211, List.forall_mem_cons.2 ⟨subd14_2_212, List.forall_mem_cons.2 ⟨subd14_2_213, List.forall_mem_cons.2 ⟨subd14_2_214, List.forall_mem_cons.2 ⟨subd14_2_215, List.forall_mem_cons.2 ⟨subd14_2_216, List.forall_mem_cons.2 ⟨subd14_2_217, List.forall_mem_cons.2 ⟨subd14_2_218, List.forall_mem_cons.2 ⟨subd14_2_219, List.forall_mem_cons.2 ⟨subd14_2_220, List.forall_mem_cons.2 ⟨subd14_2_221, List.forall_mem_cons.2 ⟨subd14_2_222, List.forall_mem_cons.2 ⟨subd14_2_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_2_224 : subd14_2 [-2, 4, -1] = true := by decide +kernel
theorem subd14_2_225 : subd14_2 [-2, 4, 0] = true := by decide +kernel
theorem subd14_2_226 : subd14_2 [-2, 4, 1] = true := by decide +kernel
theorem subd14_2_227 : subd14_2 [-2, 4, 2] = true := by decide +kernel
theorem subd14_2_228 : subd14_2 [-2, 4, 3] = true := by decide +kernel
theorem subd14_2_229 : subd14_2 [-2, 4, 4] = true := by decide +kernel
theorem subd14_2_230 : subd14_2 [-2, 4, 5] = true := by decide +kernel
theorem subd14_2_231 : subd14_2 [-2, 4, 6] = true := by decide +kernel
theorem subd14_2_232 : subd14_2 [-2, 5] = true := by decide +kernel
theorem subd14_2_233 : subd14_2 [-2, 6] = true := by decide +kernel
theorem subd14_2_234 : subd14_2 [-1, -6] = true := by decide +kernel
theorem subd14_2_235 : subd14_2 [-1, -5] = true := by decide +kernel
theorem subd14_2_236 : subd14_2 [-1, -4] = true := by decide +kernel
theorem subd14_2_237 : subd14_2 [-1, -3, -8] = true := by decide +kernel
theorem subd14_2_238 : subd14_2 [-1, -3, -7] = true := by decide +kernel
theorem subd14_2_239 : subd14_2 [-1, -3, -6] = true := by decide +kernel
theorem subd14_2_240 : subd14_2 [-1, -3, -5] = true := by decide +kernel
theorem subd14_2_241 : subd14_2 [-1, -3, -4] = true := by decide +kernel
theorem subd14_2_242 : subd14_2 [-1, -3, -3] = true := by decide +kernel
theorem subd14_2_243 : subd14_2 [-1, -3, -2] = true := by decide +kernel
theorem subd14_2_244 : subd14_2 [-1, -3, -1] = true := by decide +kernel
theorem subd14_2_245 : subd14_2 [-1, -3, 0] = true := by decide +kernel
theorem subd14_2_246 : subd14_2 [-1, -3, 1] = true := by decide +kernel
theorem subd14_2_247 : subd14_2 [-1, -3, 2] = true := by decide +kernel
theorem subd14_2_248 : subd14_2 [-1, -3, 3] = true := by decide +kernel
theorem subd14_2_249 : subd14_2 [-1, -3, 4] = true := by decide +kernel
theorem subd14_2_250 : subd14_2 [-1, -3, 5] = true := by decide +kernel
theorem subd14_2_251 : subd14_2 [-1, -3, 6] = true := by decide +kernel
theorem subd14_2_252 : subd14_2 [-1, -2, -9] = true := by decide +kernel
theorem subd14_2_253 : subd14_2 [-1, -2, -8] = true := by decide +kernel
theorem subd14_2_254 : subd14_2 [-1, -2, -7] = true := by decide +kernel
theorem subd14_2_255 : subd14_2 [-1, -2, -6] = true := by decide +kernel
theorem sbd14_2_7 : ∀ q ∈ blkd14_2_7, subd14_2 q = true := by
  unfold blkd14_2_7
  exact List.forall_mem_cons.2 ⟨subd14_2_224, List.forall_mem_cons.2 ⟨subd14_2_225, List.forall_mem_cons.2 ⟨subd14_2_226, List.forall_mem_cons.2 ⟨subd14_2_227, List.forall_mem_cons.2 ⟨subd14_2_228, List.forall_mem_cons.2 ⟨subd14_2_229, List.forall_mem_cons.2 ⟨subd14_2_230, List.forall_mem_cons.2 ⟨subd14_2_231, List.forall_mem_cons.2 ⟨subd14_2_232, List.forall_mem_cons.2 ⟨subd14_2_233, List.forall_mem_cons.2 ⟨subd14_2_234, List.forall_mem_cons.2 ⟨subd14_2_235, List.forall_mem_cons.2 ⟨subd14_2_236, List.forall_mem_cons.2 ⟨subd14_2_237, List.forall_mem_cons.2 ⟨subd14_2_238, List.forall_mem_cons.2 ⟨subd14_2_239, List.forall_mem_cons.2 ⟨subd14_2_240, List.forall_mem_cons.2 ⟨subd14_2_241, List.forall_mem_cons.2 ⟨subd14_2_242, List.forall_mem_cons.2 ⟨subd14_2_243, List.forall_mem_cons.2 ⟨subd14_2_244, List.forall_mem_cons.2 ⟨subd14_2_245, List.forall_mem_cons.2 ⟨subd14_2_246, List.forall_mem_cons.2 ⟨subd14_2_247, List.forall_mem_cons.2 ⟨subd14_2_248, List.forall_mem_cons.2 ⟨subd14_2_249, List.forall_mem_cons.2 ⟨subd14_2_250, List.forall_mem_cons.2 ⟨subd14_2_251, List.forall_mem_cons.2 ⟨subd14_2_252, List.forall_mem_cons.2 ⟨subd14_2_253, List.forall_mem_cons.2 ⟨subd14_2_254, List.forall_mem_cons.2 ⟨subd14_2_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_2_256 : subd14_2 [-1, -2, -5] = true := by decide +kernel
theorem subd14_2_257 : subd14_2 [-1, -2, -4] = true := by decide +kernel
theorem subd14_2_258 : subd14_2 [-1, -2, -3] = true := by decide +kernel
theorem subd14_2_259 : subd14_2 [-1, -2, -2] = true := by decide +kernel
theorem subd14_2_260 : subd14_2 [-1, -2, -1] = true := by decide +kernel
theorem subd14_2_261 : subd14_2 [-1, -2, 0] = true := by decide +kernel
theorem subd14_2_262 : subd14_2 [-1, -2, 1] = true := by decide +kernel
theorem subd14_2_263 : subd14_2 [-1, -2, 2] = true := by decide +kernel
theorem subd14_2_264 : subd14_2 [-1, -2, 3] = true := by decide +kernel
theorem subd14_2_265 : subd14_2 [-1, -2, 4] = true := by decide +kernel
theorem subd14_2_266 : subd14_2 [-1, -2, 5] = true := by decide +kernel
theorem subd14_2_267 : subd14_2 [-1, -2, 6] = true := by decide +kernel
theorem subd14_2_268 : subd14_2 [-1, -2, 7] = true := by decide +kernel
theorem subd14_2_269 : subd14_2 [-1, -1, -9] = true := by decide +kernel
theorem subd14_2_270 : subd14_2 [-1, -1, -8] = true := by decide +kernel
theorem subd14_2_271 : subd14_2 [-1, -1, -7] = true := by decide +kernel
theorem subd14_2_272 : subd14_2 [-1, -1, -6] = true := by decide +kernel
theorem subd14_2_273 : subd14_2 [-1, -1, -5] = true := by decide +kernel
theorem subd14_2_274 : subd14_2 [-1, -1, -4] = true := by decide +kernel
theorem subd14_2_275 : subd14_2 [-1, -1, -3] = true := by decide +kernel
theorem subd14_2_276 : subd14_2 [-1, -1, -2] = true := by decide +kernel
theorem subd14_2_277 : subd14_2 [-1, -1, -1] = true := by decide +kernel
theorem subd14_2_278 : subd14_2 [-1, -1, 0] = true := by decide +kernel
theorem subd14_2_279 : subd14_2 [-1, -1, 1] = true := by decide +kernel
theorem subd14_2_280 : subd14_2 [-1, -1, 2] = true := by decide +kernel
theorem subd14_2_281 : subd14_2 [-1, -1, 3] = true := by decide +kernel
theorem subd14_2_282 : subd14_2 [-1, -1, 4] = true := by decide +kernel
theorem subd14_2_283 : subd14_2 [-1, -1, 5] = true := by decide +kernel
theorem subd14_2_284 : subd14_2 [-1, -1, 6] = true := by decide +kernel
theorem subd14_2_285 : subd14_2 [-1, -1, 7] = true := by decide +kernel
theorem subd14_2_286 : subd14_2 [-1, -1, 8] = true := by decide +kernel
theorem subd14_2_287 : subd14_2 [-1, 0, -10] = true := by decide +kernel
theorem sbd14_2_8 : ∀ q ∈ blkd14_2_8, subd14_2 q = true := by
  unfold blkd14_2_8
  exact List.forall_mem_cons.2 ⟨subd14_2_256, List.forall_mem_cons.2 ⟨subd14_2_257, List.forall_mem_cons.2 ⟨subd14_2_258, List.forall_mem_cons.2 ⟨subd14_2_259, List.forall_mem_cons.2 ⟨subd14_2_260, List.forall_mem_cons.2 ⟨subd14_2_261, List.forall_mem_cons.2 ⟨subd14_2_262, List.forall_mem_cons.2 ⟨subd14_2_263, List.forall_mem_cons.2 ⟨subd14_2_264, List.forall_mem_cons.2 ⟨subd14_2_265, List.forall_mem_cons.2 ⟨subd14_2_266, List.forall_mem_cons.2 ⟨subd14_2_267, List.forall_mem_cons.2 ⟨subd14_2_268, List.forall_mem_cons.2 ⟨subd14_2_269, List.forall_mem_cons.2 ⟨subd14_2_270, List.forall_mem_cons.2 ⟨subd14_2_271, List.forall_mem_cons.2 ⟨subd14_2_272, List.forall_mem_cons.2 ⟨subd14_2_273, List.forall_mem_cons.2 ⟨subd14_2_274, List.forall_mem_cons.2 ⟨subd14_2_275, List.forall_mem_cons.2 ⟨subd14_2_276, List.forall_mem_cons.2 ⟨subd14_2_277, List.forall_mem_cons.2 ⟨subd14_2_278, List.forall_mem_cons.2 ⟨subd14_2_279, List.forall_mem_cons.2 ⟨subd14_2_280, List.forall_mem_cons.2 ⟨subd14_2_281, List.forall_mem_cons.2 ⟨subd14_2_282, List.forall_mem_cons.2 ⟨subd14_2_283, List.forall_mem_cons.2 ⟨subd14_2_284, List.forall_mem_cons.2 ⟨subd14_2_285, List.forall_mem_cons.2 ⟨subd14_2_286, List.forall_mem_cons.2 ⟨subd14_2_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_2_288 : subd14_2 [-1, 0, -9] = true := by decide +kernel
theorem subd14_2_289 : subd14_2 [-1, 0, -8] = true := by decide +kernel
theorem subd14_2_290 : subd14_2 [-1, 0, -7] = true := by decide +kernel
theorem subd14_2_291 : subd14_2 [-1, 0, -6] = true := by decide +kernel
theorem subd14_2_292 : subd14_2 [-1, 0, -5] = true := by decide +kernel
theorem subd14_2_293 : subd14_2 [-1, 0, -4] = true := by decide +kernel
theorem subd14_2_294 : subd14_2 [-1, 0, -3] = true := by decide +kernel
theorem subd14_2_295 : subd14_2 [-1, 0, -2] = true := by decide +kernel
theorem subd14_2_296 : subd14_2 [-1, 0, -1] = true := by decide +kernel
theorem subd14_2_297 : subd14_2 [-1, 0, 0] = true := by decide +kernel
theorem subd14_2_298 : subd14_2 [-1, 0, 1] = true := by decide +kernel
theorem subd14_2_299 : subd14_2 [-1, 0, 2] = true := by decide +kernel
theorem subd14_2_300 : subd14_2 [-1, 0, 3] = true := by decide +kernel
theorem subd14_2_301 : subd14_2 [-1, 0, 4] = true := by decide +kernel
theorem subd14_2_302 : subd14_2 [-1, 0, 5] = true := by decide +kernel
theorem subd14_2_303 : subd14_2 [-1, 0, 6] = true := by decide +kernel
theorem subd14_2_304 : subd14_2 [-1, 0, 7] = true := by decide +kernel
theorem subd14_2_305 : subd14_2 [-1, 0, 8] = true := by decide +kernel
theorem subd14_2_306 : subd14_2 [-1, 1, -10] = true := by decide +kernel
theorem subd14_2_307 : subd14_2 [-1, 1, -9] = true := by decide +kernel
theorem subd14_2_308 : subd14_2 [-1, 1, -8] = true := by decide +kernel
theorem subd14_2_309 : subd14_2 [-1, 1, -7] = true := by decide +kernel
theorem subd14_2_310 : subd14_2 [-1, 1, -6] = true := by decide +kernel
theorem subd14_2_311 : subd14_2 [-1, 1, -5] = true := by decide +kernel
theorem subd14_2_312 : subd14_2 [-1, 1, -4] = true := by decide +kernel
theorem subd14_2_313 : subd14_2 [-1, 1, -3] = true := by decide +kernel
theorem subd14_2_314 : subd14_2 [-1, 1, -2] = true := by decide +kernel
theorem subd14_2_315 : subd14_2 [-1, 1, -1] = true := by decide +kernel
theorem subd14_2_316 : subd14_2 [-1, 1, 0] = true := by decide +kernel
theorem subd14_2_317 : subd14_2 [-1, 1, 1] = true := by decide +kernel
theorem subd14_2_318 : subd14_2 [-1, 1, 2] = true := by decide +kernel
theorem subd14_2_319 : subd14_2 [-1, 1, 3] = true := by decide +kernel
theorem sbd14_2_9 : ∀ q ∈ blkd14_2_9, subd14_2 q = true := by
  unfold blkd14_2_9
  exact List.forall_mem_cons.2 ⟨subd14_2_288, List.forall_mem_cons.2 ⟨subd14_2_289, List.forall_mem_cons.2 ⟨subd14_2_290, List.forall_mem_cons.2 ⟨subd14_2_291, List.forall_mem_cons.2 ⟨subd14_2_292, List.forall_mem_cons.2 ⟨subd14_2_293, List.forall_mem_cons.2 ⟨subd14_2_294, List.forall_mem_cons.2 ⟨subd14_2_295, List.forall_mem_cons.2 ⟨subd14_2_296, List.forall_mem_cons.2 ⟨subd14_2_297, List.forall_mem_cons.2 ⟨subd14_2_298, List.forall_mem_cons.2 ⟨subd14_2_299, List.forall_mem_cons.2 ⟨subd14_2_300, List.forall_mem_cons.2 ⟨subd14_2_301, List.forall_mem_cons.2 ⟨subd14_2_302, List.forall_mem_cons.2 ⟨subd14_2_303, List.forall_mem_cons.2 ⟨subd14_2_304, List.forall_mem_cons.2 ⟨subd14_2_305, List.forall_mem_cons.2 ⟨subd14_2_306, List.forall_mem_cons.2 ⟨subd14_2_307, List.forall_mem_cons.2 ⟨subd14_2_308, List.forall_mem_cons.2 ⟨subd14_2_309, List.forall_mem_cons.2 ⟨subd14_2_310, List.forall_mem_cons.2 ⟨subd14_2_311, List.forall_mem_cons.2 ⟨subd14_2_312, List.forall_mem_cons.2 ⟨subd14_2_313, List.forall_mem_cons.2 ⟨subd14_2_314, List.forall_mem_cons.2 ⟨subd14_2_315, List.forall_mem_cons.2 ⟨subd14_2_316, List.forall_mem_cons.2 ⟨subd14_2_317, List.forall_mem_cons.2 ⟨subd14_2_318, List.forall_mem_cons.2 ⟨subd14_2_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_2_320 : subd14_2 [-1, 1, 4] = true := by decide +kernel
theorem subd14_2_321 : subd14_2 [-1, 1, 5] = true := by decide +kernel
theorem subd14_2_322 : subd14_2 [-1, 1, 6] = true := by decide +kernel
theorem subd14_2_323 : subd14_2 [-1, 1, 7] = true := by decide +kernel
theorem subd14_2_324 : subd14_2 [-1, 1, 8] = true := by decide +kernel
theorem subd14_2_325 : subd14_2 [-1, 2, -9] = true := by decide +kernel
theorem subd14_2_326 : subd14_2 [-1, 2, -8] = true := by decide +kernel
theorem subd14_2_327 : subd14_2 [-1, 2, -7] = true := by decide +kernel
theorem subd14_2_328 : subd14_2 [-1, 2, -6] = true := by decide +kernel
theorem subd14_2_329 : subd14_2 [-1, 2, -5] = true := by decide +kernel
theorem subd14_2_330 : subd14_2 [-1, 2, -4] = true := by decide +kernel
theorem subd14_2_331 : subd14_2 [-1, 2, -3] = true := by decide +kernel
theorem subd14_2_332 : subd14_2 [-1, 2, -2] = true := by decide +kernel
theorem subd14_2_333 : subd14_2 [-1, 2, -1] = true := by decide +kernel
theorem subd14_2_334 : subd14_2 [-1, 2, 0] = true := by decide +kernel
theorem subd14_2_335 : subd14_2 [-1, 2, 1] = true := by decide +kernel
theorem subd14_2_336 : subd14_2 [-1, 2, 2] = true := by decide +kernel
theorem subd14_2_337 : subd14_2 [-1, 2, 3] = true := by decide +kernel
theorem subd14_2_338 : subd14_2 [-1, 2, 4] = true := by decide +kernel
theorem subd14_2_339 : subd14_2 [-1, 2, 5] = true := by decide +kernel
theorem subd14_2_340 : subd14_2 [-1, 2, 6] = true := by decide +kernel
theorem subd14_2_341 : subd14_2 [-1, 2, 7] = true := by decide +kernel
theorem subd14_2_342 : subd14_2 [-1, 2, 8] = true := by decide +kernel
theorem subd14_2_343 : subd14_2 [-1, 3, -9] = true := by decide +kernel
theorem subd14_2_344 : subd14_2 [-1, 3, -8] = true := by decide +kernel
theorem subd14_2_345 : subd14_2 [-1, 3, -7] = true := by decide +kernel
theorem subd14_2_346 : subd14_2 [-1, 3, -6] = true := by decide +kernel
theorem subd14_2_347 : subd14_2 [-1, 3, -5] = true := by decide +kernel
theorem subd14_2_348 : subd14_2 [-1, 3, -4] = true := by decide +kernel
theorem subd14_2_349 : subd14_2 [-1, 3, -3] = true := by decide +kernel
theorem subd14_2_350 : subd14_2 [-1, 3, -2] = true := by decide +kernel
theorem subd14_2_351 : subd14_2 [-1, 3, -1] = true := by decide +kernel
theorem sbd14_2_10 : ∀ q ∈ blkd14_2_10, subd14_2 q = true := by
  unfold blkd14_2_10
  exact List.forall_mem_cons.2 ⟨subd14_2_320, List.forall_mem_cons.2 ⟨subd14_2_321, List.forall_mem_cons.2 ⟨subd14_2_322, List.forall_mem_cons.2 ⟨subd14_2_323, List.forall_mem_cons.2 ⟨subd14_2_324, List.forall_mem_cons.2 ⟨subd14_2_325, List.forall_mem_cons.2 ⟨subd14_2_326, List.forall_mem_cons.2 ⟨subd14_2_327, List.forall_mem_cons.2 ⟨subd14_2_328, List.forall_mem_cons.2 ⟨subd14_2_329, List.forall_mem_cons.2 ⟨subd14_2_330, List.forall_mem_cons.2 ⟨subd14_2_331, List.forall_mem_cons.2 ⟨subd14_2_332, List.forall_mem_cons.2 ⟨subd14_2_333, List.forall_mem_cons.2 ⟨subd14_2_334, List.forall_mem_cons.2 ⟨subd14_2_335, List.forall_mem_cons.2 ⟨subd14_2_336, List.forall_mem_cons.2 ⟨subd14_2_337, List.forall_mem_cons.2 ⟨subd14_2_338, List.forall_mem_cons.2 ⟨subd14_2_339, List.forall_mem_cons.2 ⟨subd14_2_340, List.forall_mem_cons.2 ⟨subd14_2_341, List.forall_mem_cons.2 ⟨subd14_2_342, List.forall_mem_cons.2 ⟨subd14_2_343, List.forall_mem_cons.2 ⟨subd14_2_344, List.forall_mem_cons.2 ⟨subd14_2_345, List.forall_mem_cons.2 ⟨subd14_2_346, List.forall_mem_cons.2 ⟨subd14_2_347, List.forall_mem_cons.2 ⟨subd14_2_348, List.forall_mem_cons.2 ⟨subd14_2_349, List.forall_mem_cons.2 ⟨subd14_2_350, List.forall_mem_cons.2 ⟨subd14_2_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_2_352 : subd14_2 [-1, 3, 0] = true := by decide +kernel
theorem subd14_2_353 : subd14_2 [-1, 3, 1] = true := by decide +kernel
theorem subd14_2_354 : subd14_2 [-1, 3, 2] = true := by decide +kernel
theorem subd14_2_355 : subd14_2 [-1, 3, 3] = true := by decide +kernel
theorem subd14_2_356 : subd14_2 [-1, 3, 4] = true := by decide +kernel
theorem subd14_2_357 : subd14_2 [-1, 3, 5] = true := by decide +kernel
theorem subd14_2_358 : subd14_2 [-1, 3, 6] = true := by decide +kernel
theorem subd14_2_359 : subd14_2 [-1, 3, 7] = true := by decide +kernel
theorem subd14_2_360 : subd14_2 [-1, 4, -8] = true := by decide +kernel
theorem subd14_2_361 : subd14_2 [-1, 4, -7] = true := by decide +kernel
theorem subd14_2_362 : subd14_2 [-1, 4, -6] = true := by decide +kernel
theorem subd14_2_363 : subd14_2 [-1, 4, -5] = true := by decide +kernel
theorem subd14_2_364 : subd14_2 [-1, 4, -4] = true := by decide +kernel
theorem subd14_2_365 : subd14_2 [-1, 4, -3] = true := by decide +kernel
theorem subd14_2_366 : subd14_2 [-1, 4, -2] = true := by decide +kernel
theorem subd14_2_367 : subd14_2 [-1, 4, -1] = true := by decide +kernel
theorem subd14_2_368 : subd14_2 [-1, 4, 0] = true := by decide +kernel
theorem subd14_2_369 : subd14_2 [-1, 4, 1] = true := by decide +kernel
theorem subd14_2_370 : subd14_2 [-1, 4, 2] = true := by decide +kernel
theorem subd14_2_371 : subd14_2 [-1, 4, 3] = true := by decide +kernel
theorem subd14_2_372 : subd14_2 [-1, 4, 4] = true := by decide +kernel
theorem subd14_2_373 : subd14_2 [-1, 4, 5] = true := by decide +kernel
theorem subd14_2_374 : subd14_2 [-1, 4, 6] = true := by decide +kernel
theorem subd14_2_375 : subd14_2 [-1, 5] = true := by decide +kernel
theorem subd14_2_376 : subd14_2 [-1, 6] = true := by decide +kernel
theorem subd14_2_377 : subd14_2 [0, -7] = true := by decide +kernel
theorem subd14_2_378 : subd14_2 [0, -6] = true := by decide +kernel
theorem subd14_2_379 : subd14_2 [0, -5] = true := by decide +kernel
theorem subd14_2_380 : subd14_2 [0, -4, -8] = true := by decide +kernel
theorem subd14_2_381 : subd14_2 [0, -4, -7] = true := by decide +kernel
theorem subd14_2_382 : subd14_2 [0, -4, -6] = true := by decide +kernel
theorem subd14_2_383 : subd14_2 [0, -4, -5] = true := by decide +kernel
theorem sbd14_2_11 : ∀ q ∈ blkd14_2_11, subd14_2 q = true := by
  unfold blkd14_2_11
  exact List.forall_mem_cons.2 ⟨subd14_2_352, List.forall_mem_cons.2 ⟨subd14_2_353, List.forall_mem_cons.2 ⟨subd14_2_354, List.forall_mem_cons.2 ⟨subd14_2_355, List.forall_mem_cons.2 ⟨subd14_2_356, List.forall_mem_cons.2 ⟨subd14_2_357, List.forall_mem_cons.2 ⟨subd14_2_358, List.forall_mem_cons.2 ⟨subd14_2_359, List.forall_mem_cons.2 ⟨subd14_2_360, List.forall_mem_cons.2 ⟨subd14_2_361, List.forall_mem_cons.2 ⟨subd14_2_362, List.forall_mem_cons.2 ⟨subd14_2_363, List.forall_mem_cons.2 ⟨subd14_2_364, List.forall_mem_cons.2 ⟨subd14_2_365, List.forall_mem_cons.2 ⟨subd14_2_366, List.forall_mem_cons.2 ⟨subd14_2_367, List.forall_mem_cons.2 ⟨subd14_2_368, List.forall_mem_cons.2 ⟨subd14_2_369, List.forall_mem_cons.2 ⟨subd14_2_370, List.forall_mem_cons.2 ⟨subd14_2_371, List.forall_mem_cons.2 ⟨subd14_2_372, List.forall_mem_cons.2 ⟨subd14_2_373, List.forall_mem_cons.2 ⟨subd14_2_374, List.forall_mem_cons.2 ⟨subd14_2_375, List.forall_mem_cons.2 ⟨subd14_2_376, List.forall_mem_cons.2 ⟨subd14_2_377, List.forall_mem_cons.2 ⟨subd14_2_378, List.forall_mem_cons.2 ⟨subd14_2_379, List.forall_mem_cons.2 ⟨subd14_2_380, List.forall_mem_cons.2 ⟨subd14_2_381, List.forall_mem_cons.2 ⟨subd14_2_382, List.forall_mem_cons.2 ⟨subd14_2_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_2_384 : subd14_2 [0, -4, -4] = true := by decide +kernel
theorem subd14_2_385 : subd14_2 [0, -4, -3] = true := by decide +kernel
theorem subd14_2_386 : subd14_2 [0, -4, -2] = true := by decide +kernel
theorem subd14_2_387 : subd14_2 [0, -4, -1] = true := by decide +kernel
theorem subd14_2_388 : subd14_2 [0, -4, 0] = true := by decide +kernel
theorem subd14_2_389 : subd14_2 [0, -4, 1] = true := by decide +kernel
theorem subd14_2_390 : subd14_2 [0, -4, 2] = true := by decide +kernel
theorem subd14_2_391 : subd14_2 [0, -4, 3] = true := by decide +kernel
theorem subd14_2_392 : subd14_2 [0, -4, 4] = true := by decide +kernel
theorem subd14_2_393 : subd14_2 [0, -4, 5] = true := by decide +kernel
theorem subd14_2_394 : subd14_2 [0, -4, 6] = true := by decide +kernel
theorem subd14_2_395 : subd14_2 [0, -3, -9] = true := by decide +kernel
theorem subd14_2_396 : subd14_2 [0, -3, -8] = true := by decide +kernel
theorem subd14_2_397 : subd14_2 [0, -3, -7] = true := by decide +kernel
theorem subd14_2_398 : subd14_2 [0, -3, -6] = true := by decide +kernel
theorem subd14_2_399 : subd14_2 [0, -3, -5] = true := by decide +kernel
theorem subd14_2_400 : subd14_2 [0, -3, -4] = true := by decide +kernel
theorem subd14_2_401 : subd14_2 [0, -3, -3] = true := by decide +kernel
theorem subd14_2_402 : subd14_2 [0, -3, -2] = true := by decide +kernel
theorem subd14_2_403 : subd14_2 [0, -3, -1] = true := by decide +kernel
theorem subd14_2_404 : subd14_2 [0, -3, 0] = true := by decide +kernel
theorem subd14_2_405 : subd14_2 [0, -3, 1] = true := by decide +kernel
theorem subd14_2_406 : subd14_2 [0, -3, 2] = true := by decide +kernel
theorem subd14_2_407 : subd14_2 [0, -3, 3] = true := by decide +kernel
theorem subd14_2_408 : subd14_2 [0, -3, 4] = true := by decide +kernel
theorem subd14_2_409 : subd14_2 [0, -3, 5] = true := by decide +kernel
theorem subd14_2_410 : subd14_2 [0, -3, 6] = true := by decide +kernel
theorem subd14_2_411 : subd14_2 [0, -3, 7] = true := by decide +kernel
theorem subd14_2_412 : subd14_2 [0, -2, -9] = true := by decide +kernel
theorem subd14_2_413 : subd14_2 [0, -2, -8] = true := by decide +kernel
theorem subd14_2_414 : subd14_2 [0, -2, -7] = true := by decide +kernel
theorem subd14_2_415 : subd14_2 [0, -2, -6] = true := by decide +kernel
theorem sbd14_2_12 : ∀ q ∈ blkd14_2_12, subd14_2 q = true := by
  unfold blkd14_2_12
  exact List.forall_mem_cons.2 ⟨subd14_2_384, List.forall_mem_cons.2 ⟨subd14_2_385, List.forall_mem_cons.2 ⟨subd14_2_386, List.forall_mem_cons.2 ⟨subd14_2_387, List.forall_mem_cons.2 ⟨subd14_2_388, List.forall_mem_cons.2 ⟨subd14_2_389, List.forall_mem_cons.2 ⟨subd14_2_390, List.forall_mem_cons.2 ⟨subd14_2_391, List.forall_mem_cons.2 ⟨subd14_2_392, List.forall_mem_cons.2 ⟨subd14_2_393, List.forall_mem_cons.2 ⟨subd14_2_394, List.forall_mem_cons.2 ⟨subd14_2_395, List.forall_mem_cons.2 ⟨subd14_2_396, List.forall_mem_cons.2 ⟨subd14_2_397, List.forall_mem_cons.2 ⟨subd14_2_398, List.forall_mem_cons.2 ⟨subd14_2_399, List.forall_mem_cons.2 ⟨subd14_2_400, List.forall_mem_cons.2 ⟨subd14_2_401, List.forall_mem_cons.2 ⟨subd14_2_402, List.forall_mem_cons.2 ⟨subd14_2_403, List.forall_mem_cons.2 ⟨subd14_2_404, List.forall_mem_cons.2 ⟨subd14_2_405, List.forall_mem_cons.2 ⟨subd14_2_406, List.forall_mem_cons.2 ⟨subd14_2_407, List.forall_mem_cons.2 ⟨subd14_2_408, List.forall_mem_cons.2 ⟨subd14_2_409, List.forall_mem_cons.2 ⟨subd14_2_410, List.forall_mem_cons.2 ⟨subd14_2_411, List.forall_mem_cons.2 ⟨subd14_2_412, List.forall_mem_cons.2 ⟨subd14_2_413, List.forall_mem_cons.2 ⟨subd14_2_414, List.forall_mem_cons.2 ⟨subd14_2_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_2_416 : subd14_2 [0, -2, -5] = true := by decide +kernel
theorem subd14_2_417 : subd14_2 [0, -2, -4] = true := by decide +kernel
theorem subd14_2_418 : subd14_2 [0, -2, -3] = true := by decide +kernel
theorem subd14_2_419 : subd14_2 [0, -2, -2] = true := by decide +kernel
theorem subd14_2_420 : subd14_2 [0, -2, -1] = true := by decide +kernel
theorem subd14_2_421 : subd14_2 [0, -2, 0] = true := by decide +kernel
theorem subd14_2_422 : subd14_2 [0, -2, 1] = true := by decide +kernel
theorem subd14_2_423 : subd14_2 [0, -2, 2] = true := by decide +kernel
theorem subd14_2_424 : subd14_2 [0, -2, 3] = true := by decide +kernel
theorem subd14_2_425 : subd14_2 [0, -2, 4] = true := by decide +kernel
theorem subd14_2_426 : subd14_2 [0, -2, 5] = true := by decide +kernel
theorem subd14_2_427 : subd14_2 [0, -2, 6] = true := by decide +kernel
theorem subd14_2_428 : subd14_2 [0, -2, 7] = true := by decide +kernel
theorem subd14_2_429 : subd14_2 [0, -2, 8] = true := by decide +kernel
theorem subd14_2_430 : subd14_2 [0, -1, -9] = true := by decide +kernel
theorem subd14_2_431 : subd14_2 [0, -1, -8] = true := by decide +kernel
theorem subd14_2_432 : subd14_2 [0, -1, -7] = true := by decide +kernel
theorem subd14_2_433 : subd14_2 [0, -1, -6] = true := by decide +kernel
theorem subd14_2_434 : subd14_2 [0, -1, -5] = true := by decide +kernel
theorem subd14_2_435 : subd14_2 [0, -1, -4] = true := by decide +kernel
theorem subd14_2_436 : subd14_2 [0, -1, -3] = true := by decide +kernel
theorem subd14_2_437 : subd14_2 [0, -1, -2] = true := by decide +kernel
theorem subd14_2_438 : subd14_2 [0, -1, -1] = true := by decide +kernel
theorem subd14_2_439 : subd14_2 [0, -1, 0] = true := by decide +kernel
theorem subd14_2_440 : subd14_2 [0, -1, 1] = true := by decide +kernel
theorem subd14_2_441 : subd14_2 [0, -1, 2] = true := by decide +kernel
theorem subd14_2_442 : subd14_2 [0, -1, 3] = true := by decide +kernel
theorem subd14_2_443 : subd14_2 [0, -1, 4] = true := by decide +kernel
theorem subd14_2_444 : subd14_2 [0, -1, 5] = true := by decide +kernel
theorem subd14_2_445 : subd14_2 [0, -1, 6] = true := by decide +kernel
theorem subd14_2_446 : subd14_2 [0, -1, 7] = true := by decide +kernel
theorem subd14_2_447 : subd14_2 [0, -1, 8] = true := by decide +kernel
theorem sbd14_2_13 : ∀ q ∈ blkd14_2_13, subd14_2 q = true := by
  unfold blkd14_2_13
  exact List.forall_mem_cons.2 ⟨subd14_2_416, List.forall_mem_cons.2 ⟨subd14_2_417, List.forall_mem_cons.2 ⟨subd14_2_418, List.forall_mem_cons.2 ⟨subd14_2_419, List.forall_mem_cons.2 ⟨subd14_2_420, List.forall_mem_cons.2 ⟨subd14_2_421, List.forall_mem_cons.2 ⟨subd14_2_422, List.forall_mem_cons.2 ⟨subd14_2_423, List.forall_mem_cons.2 ⟨subd14_2_424, List.forall_mem_cons.2 ⟨subd14_2_425, List.forall_mem_cons.2 ⟨subd14_2_426, List.forall_mem_cons.2 ⟨subd14_2_427, List.forall_mem_cons.2 ⟨subd14_2_428, List.forall_mem_cons.2 ⟨subd14_2_429, List.forall_mem_cons.2 ⟨subd14_2_430, List.forall_mem_cons.2 ⟨subd14_2_431, List.forall_mem_cons.2 ⟨subd14_2_432, List.forall_mem_cons.2 ⟨subd14_2_433, List.forall_mem_cons.2 ⟨subd14_2_434, List.forall_mem_cons.2 ⟨subd14_2_435, List.forall_mem_cons.2 ⟨subd14_2_436, List.forall_mem_cons.2 ⟨subd14_2_437, List.forall_mem_cons.2 ⟨subd14_2_438, List.forall_mem_cons.2 ⟨subd14_2_439, List.forall_mem_cons.2 ⟨subd14_2_440, List.forall_mem_cons.2 ⟨subd14_2_441, List.forall_mem_cons.2 ⟨subd14_2_442, List.forall_mem_cons.2 ⟨subd14_2_443, List.forall_mem_cons.2 ⟨subd14_2_444, List.forall_mem_cons.2 ⟨subd14_2_445, List.forall_mem_cons.2 ⟨subd14_2_446, List.forall_mem_cons.2 ⟨subd14_2_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_2_448 : subd14_2 [0, 0, -10] = true := by decide +kernel
theorem subd14_2_449 : subd14_2 [0, 0, -9] = true := by decide +kernel
theorem subd14_2_450 : subd14_2 [0, 0, -8] = true := by decide +kernel
theorem subd14_2_451 : subd14_2 [0, 0, -7] = true := by decide +kernel
theorem subd14_2_452 : subd14_2 [0, 0, -6] = true := by decide +kernel
theorem subd14_2_453 : subd14_2 [0, 0, -5] = true := by decide +kernel
theorem subd14_2_454 : subd14_2 [0, 0, -4] = true := by decide +kernel
theorem subd14_2_455 : subd14_2 [0, 0, -3] = true := by decide +kernel
theorem subd14_2_456 : subd14_2 [0, 0, -2] = true := by decide +kernel
theorem subd14_2_457 : subd14_2 [0, 0, -1] = true := by decide +kernel
theorem subd14_2_458 : subd14_2 [0, 0, 0] = true := by decide +kernel
theorem subd14_2_459 : subd14_2 [0, 0, 1] = true := by decide +kernel
theorem subd14_2_460 : subd14_2 [0, 0, 2] = true := by decide +kernel
theorem subd14_2_461 : subd14_2 [0, 0, 3] = true := by decide +kernel
theorem subd14_2_462 : subd14_2 [0, 0, 4] = true := by decide +kernel
theorem subd14_2_463 : subd14_2 [0, 0, 5] = true := by decide +kernel
theorem subd14_2_464 : subd14_2 [0, 0, 6] = true := by decide +kernel
theorem subd14_2_465 : subd14_2 [0, 0, 7] = true := by decide +kernel
theorem subd14_2_466 : subd14_2 [0, 0, 8] = true := by decide +kernel
theorem subd14_2_467 : subd14_2 [0, 0, 9] = true := by decide +kernel
theorem subd14_2_468 : subd14_2 [0, 1, -9] = true := by decide +kernel
theorem subd14_2_469 : subd14_2 [0, 1, -8] = true := by decide +kernel
theorem subd14_2_470 : subd14_2 [0, 1, -7] = true := by decide +kernel
theorem subd14_2_471 : subd14_2 [0, 1, -6] = true := by decide +kernel
theorem subd14_2_472 : subd14_2 [0, 1, -5] = true := by decide +kernel
theorem subd14_2_473 : subd14_2 [0, 1, -4] = true := by decide +kernel
theorem subd14_2_474 : subd14_2 [0, 1, -3] = true := by decide +kernel
theorem subd14_2_475 : subd14_2 [0, 1, -2] = true := by decide +kernel
theorem subd14_2_476 : subd14_2 [0, 1, -1] = true := by decide +kernel
theorem subd14_2_477 : subd14_2 [0, 1, 0] = true := by decide +kernel
theorem subd14_2_478 : subd14_2 [0, 1, 1] = true := by decide +kernel
theorem subd14_2_479 : subd14_2 [0, 1, 2] = true := by decide +kernel
theorem sbd14_2_14 : ∀ q ∈ blkd14_2_14, subd14_2 q = true := by
  unfold blkd14_2_14
  exact List.forall_mem_cons.2 ⟨subd14_2_448, List.forall_mem_cons.2 ⟨subd14_2_449, List.forall_mem_cons.2 ⟨subd14_2_450, List.forall_mem_cons.2 ⟨subd14_2_451, List.forall_mem_cons.2 ⟨subd14_2_452, List.forall_mem_cons.2 ⟨subd14_2_453, List.forall_mem_cons.2 ⟨subd14_2_454, List.forall_mem_cons.2 ⟨subd14_2_455, List.forall_mem_cons.2 ⟨subd14_2_456, List.forall_mem_cons.2 ⟨subd14_2_457, List.forall_mem_cons.2 ⟨subd14_2_458, List.forall_mem_cons.2 ⟨subd14_2_459, List.forall_mem_cons.2 ⟨subd14_2_460, List.forall_mem_cons.2 ⟨subd14_2_461, List.forall_mem_cons.2 ⟨subd14_2_462, List.forall_mem_cons.2 ⟨subd14_2_463, List.forall_mem_cons.2 ⟨subd14_2_464, List.forall_mem_cons.2 ⟨subd14_2_465, List.forall_mem_cons.2 ⟨subd14_2_466, List.forall_mem_cons.2 ⟨subd14_2_467, List.forall_mem_cons.2 ⟨subd14_2_468, List.forall_mem_cons.2 ⟨subd14_2_469, List.forall_mem_cons.2 ⟨subd14_2_470, List.forall_mem_cons.2 ⟨subd14_2_471, List.forall_mem_cons.2 ⟨subd14_2_472, List.forall_mem_cons.2 ⟨subd14_2_473, List.forall_mem_cons.2 ⟨subd14_2_474, List.forall_mem_cons.2 ⟨subd14_2_475, List.forall_mem_cons.2 ⟨subd14_2_476, List.forall_mem_cons.2 ⟨subd14_2_477, List.forall_mem_cons.2 ⟨subd14_2_478, List.forall_mem_cons.2 ⟨subd14_2_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_2_480 : subd14_2 [0, 1, 3] = true := by decide +kernel
theorem subd14_2_481 : subd14_2 [0, 1, 4] = true := by decide +kernel
theorem subd14_2_482 : subd14_2 [0, 1, 5] = true := by decide +kernel
theorem subd14_2_483 : subd14_2 [0, 1, 6] = true := by decide +kernel
theorem subd14_2_484 : subd14_2 [0, 1, 7] = true := by decide +kernel
theorem subd14_2_485 : subd14_2 [0, 1, 8] = true := by decide +kernel
theorem subd14_2_486 : subd14_2 [0, 2, -9] = true := by decide +kernel
theorem subd14_2_487 : subd14_2 [0, 2, -8] = true := by decide +kernel
theorem subd14_2_488 : subd14_2 [0, 2, -7] = true := by decide +kernel
theorem subd14_2_489 : subd14_2 [0, 2, -6] = true := by decide +kernel
theorem subd14_2_490 : subd14_2 [0, 2, -5] = true := by decide +kernel
theorem subd14_2_491 : subd14_2 [0, 2, -4] = true := by decide +kernel
theorem subd14_2_492 : subd14_2 [0, 2, -3] = true := by decide +kernel
theorem subd14_2_493 : subd14_2 [0, 2, -2] = true := by decide +kernel
theorem subd14_2_494 : subd14_2 [0, 2, -1] = true := by decide +kernel
theorem subd14_2_495 : subd14_2 [0, 2, 0] = true := by decide +kernel
theorem subd14_2_496 : subd14_2 [0, 2, 1] = true := by decide +kernel
theorem subd14_2_497 : subd14_2 [0, 2, 2] = true := by decide +kernel
theorem subd14_2_498 : subd14_2 [0, 2, 3] = true := by decide +kernel
theorem subd14_2_499 : subd14_2 [0, 2, 4] = true := by decide +kernel
theorem subd14_2_500 : subd14_2 [0, 2, 5] = true := by decide +kernel
theorem subd14_2_501 : subd14_2 [0, 2, 6] = true := by decide +kernel
theorem subd14_2_502 : subd14_2 [0, 2, 7] = true := by decide +kernel
theorem subd14_2_503 : subd14_2 [0, 2, 8] = true := by decide +kernel
theorem subd14_2_504 : subd14_2 [0, 3, -8] = true := by decide +kernel
theorem subd14_2_505 : subd14_2 [0, 3, -7] = true := by decide +kernel
theorem subd14_2_506 : subd14_2 [0, 3, -6] = true := by decide +kernel
theorem subd14_2_507 : subd14_2 [0, 3, -5] = true := by decide +kernel
theorem subd14_2_508 : subd14_2 [0, 3, -4] = true := by decide +kernel
theorem subd14_2_509 : subd14_2 [0, 3, -3] = true := by decide +kernel
theorem subd14_2_510 : subd14_2 [0, 3, -2] = true := by decide +kernel
theorem subd14_2_511 : subd14_2 [0, 3, -1] = true := by decide +kernel
theorem sbd14_2_15 : ∀ q ∈ blkd14_2_15, subd14_2 q = true := by
  unfold blkd14_2_15
  exact List.forall_mem_cons.2 ⟨subd14_2_480, List.forall_mem_cons.2 ⟨subd14_2_481, List.forall_mem_cons.2 ⟨subd14_2_482, List.forall_mem_cons.2 ⟨subd14_2_483, List.forall_mem_cons.2 ⟨subd14_2_484, List.forall_mem_cons.2 ⟨subd14_2_485, List.forall_mem_cons.2 ⟨subd14_2_486, List.forall_mem_cons.2 ⟨subd14_2_487, List.forall_mem_cons.2 ⟨subd14_2_488, List.forall_mem_cons.2 ⟨subd14_2_489, List.forall_mem_cons.2 ⟨subd14_2_490, List.forall_mem_cons.2 ⟨subd14_2_491, List.forall_mem_cons.2 ⟨subd14_2_492, List.forall_mem_cons.2 ⟨subd14_2_493, List.forall_mem_cons.2 ⟨subd14_2_494, List.forall_mem_cons.2 ⟨subd14_2_495, List.forall_mem_cons.2 ⟨subd14_2_496, List.forall_mem_cons.2 ⟨subd14_2_497, List.forall_mem_cons.2 ⟨subd14_2_498, List.forall_mem_cons.2 ⟨subd14_2_499, List.forall_mem_cons.2 ⟨subd14_2_500, List.forall_mem_cons.2 ⟨subd14_2_501, List.forall_mem_cons.2 ⟨subd14_2_502, List.forall_mem_cons.2 ⟨subd14_2_503, List.forall_mem_cons.2 ⟨subd14_2_504, List.forall_mem_cons.2 ⟨subd14_2_505, List.forall_mem_cons.2 ⟨subd14_2_506, List.forall_mem_cons.2 ⟨subd14_2_507, List.forall_mem_cons.2 ⟨subd14_2_508, List.forall_mem_cons.2 ⟨subd14_2_509, List.forall_mem_cons.2 ⟨subd14_2_510, List.forall_mem_cons.2 ⟨subd14_2_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_2_512 : subd14_2 [0, 3, 0] = true := by decide +kernel
theorem subd14_2_513 : subd14_2 [0, 3, 1] = true := by decide +kernel
theorem subd14_2_514 : subd14_2 [0, 3, 2] = true := by decide +kernel
theorem subd14_2_515 : subd14_2 [0, 3, 3] = true := by decide +kernel
theorem subd14_2_516 : subd14_2 [0, 3, 4] = true := by decide +kernel
theorem subd14_2_517 : subd14_2 [0, 3, 5] = true := by decide +kernel
theorem subd14_2_518 : subd14_2 [0, 3, 6] = true := by decide +kernel
theorem subd14_2_519 : subd14_2 [0, 3, 7] = true := by decide +kernel
theorem subd14_2_520 : subd14_2 [0, 3, 8] = true := by decide +kernel
theorem subd14_2_521 : subd14_2 [0, 4, -7] = true := by decide +kernel
theorem subd14_2_522 : subd14_2 [0, 4, -6] = true := by decide +kernel
theorem subd14_2_523 : subd14_2 [0, 4, -5] = true := by decide +kernel
theorem subd14_2_524 : subd14_2 [0, 4, -4] = true := by decide +kernel
theorem subd14_2_525 : subd14_2 [0, 4, -3] = true := by decide +kernel
theorem subd14_2_526 : subd14_2 [0, 4, -2] = true := by decide +kernel
theorem subd14_2_527 : subd14_2 [0, 4, -1] = true := by decide +kernel
theorem subd14_2_528 : subd14_2 [0, 4, 0] = true := by decide +kernel
theorem subd14_2_529 : subd14_2 [0, 4, 1] = true := by decide +kernel
theorem subd14_2_530 : subd14_2 [0, 4, 2] = true := by decide +kernel
theorem subd14_2_531 : subd14_2 [0, 4, 3] = true := by decide +kernel
theorem subd14_2_532 : subd14_2 [0, 4, 4] = true := by decide +kernel
theorem subd14_2_533 : subd14_2 [0, 4, 5] = true := by decide +kernel
theorem subd14_2_534 : subd14_2 [0, 4, 6] = true := by decide +kernel
theorem subd14_2_535 : subd14_2 [0, 4, 7] = true := by decide +kernel
theorem subd14_2_536 : subd14_2 [0, 5] = true := by decide +kernel
theorem subd14_2_537 : subd14_2 [0, 6] = true := by decide +kernel
theorem subd14_2_538 : subd14_2 [1, -7] = true := by decide +kernel
theorem subd14_2_539 : subd14_2 [1, -6] = true := by decide +kernel
theorem subd14_2_540 : subd14_2 [1, -5] = true := by decide +kernel
theorem subd14_2_541 : subd14_2 [1, -4, -7] = true := by decide +kernel
theorem subd14_2_542 : subd14_2 [1, -4, -6] = true := by decide +kernel
theorem subd14_2_543 : subd14_2 [1, -4, -5] = true := by decide +kernel
theorem sbd14_2_16 : ∀ q ∈ blkd14_2_16, subd14_2 q = true := by
  unfold blkd14_2_16
  exact List.forall_mem_cons.2 ⟨subd14_2_512, List.forall_mem_cons.2 ⟨subd14_2_513, List.forall_mem_cons.2 ⟨subd14_2_514, List.forall_mem_cons.2 ⟨subd14_2_515, List.forall_mem_cons.2 ⟨subd14_2_516, List.forall_mem_cons.2 ⟨subd14_2_517, List.forall_mem_cons.2 ⟨subd14_2_518, List.forall_mem_cons.2 ⟨subd14_2_519, List.forall_mem_cons.2 ⟨subd14_2_520, List.forall_mem_cons.2 ⟨subd14_2_521, List.forall_mem_cons.2 ⟨subd14_2_522, List.forall_mem_cons.2 ⟨subd14_2_523, List.forall_mem_cons.2 ⟨subd14_2_524, List.forall_mem_cons.2 ⟨subd14_2_525, List.forall_mem_cons.2 ⟨subd14_2_526, List.forall_mem_cons.2 ⟨subd14_2_527, List.forall_mem_cons.2 ⟨subd14_2_528, List.forall_mem_cons.2 ⟨subd14_2_529, List.forall_mem_cons.2 ⟨subd14_2_530, List.forall_mem_cons.2 ⟨subd14_2_531, List.forall_mem_cons.2 ⟨subd14_2_532, List.forall_mem_cons.2 ⟨subd14_2_533, List.forall_mem_cons.2 ⟨subd14_2_534, List.forall_mem_cons.2 ⟨subd14_2_535, List.forall_mem_cons.2 ⟨subd14_2_536, List.forall_mem_cons.2 ⟨subd14_2_537, List.forall_mem_cons.2 ⟨subd14_2_538, List.forall_mem_cons.2 ⟨subd14_2_539, List.forall_mem_cons.2 ⟨subd14_2_540, List.forall_mem_cons.2 ⟨subd14_2_541, List.forall_mem_cons.2 ⟨subd14_2_542, List.forall_mem_cons.2 ⟨subd14_2_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_2_544 : subd14_2 [1, -4, -4] = true := by decide +kernel
theorem subd14_2_545 : subd14_2 [1, -4, -3] = true := by decide +kernel
theorem subd14_2_546 : subd14_2 [1, -4, -2] = true := by decide +kernel
theorem subd14_2_547 : subd14_2 [1, -4, -1] = true := by decide +kernel
theorem subd14_2_548 : subd14_2 [1, -4, 0] = true := by decide +kernel
theorem subd14_2_549 : subd14_2 [1, -4, 1] = true := by decide +kernel
theorem subd14_2_550 : subd14_2 [1, -4, 2] = true := by decide +kernel
theorem subd14_2_551 : subd14_2 [1, -4, 3] = true := by decide +kernel
theorem subd14_2_552 : subd14_2 [1, -4, 4] = true := by decide +kernel
theorem subd14_2_553 : subd14_2 [1, -4, 5] = true := by decide +kernel
theorem subd14_2_554 : subd14_2 [1, -4, 6] = true := by decide +kernel
theorem subd14_2_555 : subd14_2 [1, -4, 7] = true := by decide +kernel
theorem subd14_2_556 : subd14_2 [1, -3, -8] = true := by decide +kernel
theorem subd14_2_557 : subd14_2 [1, -3, -7] = true := by decide +kernel
theorem subd14_2_558 : subd14_2 [1, -3, -6] = true := by decide +kernel
theorem subd14_2_559 : subd14_2 [1, -3, -5] = true := by decide +kernel
theorem subd14_2_560 : subd14_2 [1, -3, -4] = true := by decide +kernel
theorem subd14_2_561 : subd14_2 [1, -3, -3] = true := by decide +kernel
theorem subd14_2_562 : subd14_2 [1, -3, -2] = true := by decide +kernel
theorem subd14_2_563 : subd14_2 [1, -3, -1] = true := by decide +kernel
theorem subd14_2_564 : subd14_2 [1, -3, 0] = true := by decide +kernel
theorem subd14_2_565 : subd14_2 [1, -3, 1] = true := by decide +kernel
theorem subd14_2_566 : subd14_2 [1, -3, 2] = true := by decide +kernel
theorem subd14_2_567 : subd14_2 [1, -3, 3] = true := by decide +kernel
theorem subd14_2_568 : subd14_2 [1, -3, 4] = true := by decide +kernel
theorem subd14_2_569 : subd14_2 [1, -3, 5] = true := by decide +kernel
theorem subd14_2_570 : subd14_2 [1, -3, 6] = true := by decide +kernel
theorem subd14_2_571 : subd14_2 [1, -3, 7] = true := by decide +kernel
theorem subd14_2_572 : subd14_2 [1, -3, 8] = true := by decide +kernel
theorem subd14_2_573 : subd14_2 [1, -2, -9] = true := by decide +kernel
theorem subd14_2_574 : subd14_2 [1, -2, -8] = true := by decide +kernel
theorem subd14_2_575 : subd14_2 [1, -2, -7] = true := by decide +kernel
theorem sbd14_2_17 : ∀ q ∈ blkd14_2_17, subd14_2 q = true := by
  unfold blkd14_2_17
  exact List.forall_mem_cons.2 ⟨subd14_2_544, List.forall_mem_cons.2 ⟨subd14_2_545, List.forall_mem_cons.2 ⟨subd14_2_546, List.forall_mem_cons.2 ⟨subd14_2_547, List.forall_mem_cons.2 ⟨subd14_2_548, List.forall_mem_cons.2 ⟨subd14_2_549, List.forall_mem_cons.2 ⟨subd14_2_550, List.forall_mem_cons.2 ⟨subd14_2_551, List.forall_mem_cons.2 ⟨subd14_2_552, List.forall_mem_cons.2 ⟨subd14_2_553, List.forall_mem_cons.2 ⟨subd14_2_554, List.forall_mem_cons.2 ⟨subd14_2_555, List.forall_mem_cons.2 ⟨subd14_2_556, List.forall_mem_cons.2 ⟨subd14_2_557, List.forall_mem_cons.2 ⟨subd14_2_558, List.forall_mem_cons.2 ⟨subd14_2_559, List.forall_mem_cons.2 ⟨subd14_2_560, List.forall_mem_cons.2 ⟨subd14_2_561, List.forall_mem_cons.2 ⟨subd14_2_562, List.forall_mem_cons.2 ⟨subd14_2_563, List.forall_mem_cons.2 ⟨subd14_2_564, List.forall_mem_cons.2 ⟨subd14_2_565, List.forall_mem_cons.2 ⟨subd14_2_566, List.forall_mem_cons.2 ⟨subd14_2_567, List.forall_mem_cons.2 ⟨subd14_2_568, List.forall_mem_cons.2 ⟨subd14_2_569, List.forall_mem_cons.2 ⟨subd14_2_570, List.forall_mem_cons.2 ⟨subd14_2_571, List.forall_mem_cons.2 ⟨subd14_2_572, List.forall_mem_cons.2 ⟨subd14_2_573, List.forall_mem_cons.2 ⟨subd14_2_574, List.forall_mem_cons.2 ⟨subd14_2_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_2_576 : subd14_2 [1, -2, -6] = true := by decide +kernel
theorem subd14_2_577 : subd14_2 [1, -2, -5] = true := by decide +kernel
theorem subd14_2_578 : subd14_2 [1, -2, -4] = true := by decide +kernel
theorem subd14_2_579 : subd14_2 [1, -2, -3] = true := by decide +kernel
theorem subd14_2_580 : subd14_2 [1, -2, -2] = true := by decide +kernel
theorem subd14_2_581 : subd14_2 [1, -2, -1] = true := by decide +kernel
theorem subd14_2_582 : subd14_2 [1, -2, 0] = true := by decide +kernel
theorem subd14_2_583 : subd14_2 [1, -2, 1] = true := by decide +kernel
theorem subd14_2_584 : subd14_2 [1, -2, 2] = true := by decide +kernel
theorem subd14_2_585 : subd14_2 [1, -2, 3] = true := by decide +kernel
theorem subd14_2_586 : subd14_2 [1, -2, 4] = true := by decide +kernel
theorem subd14_2_587 : subd14_2 [1, -2, 5] = true := by decide +kernel
theorem subd14_2_588 : subd14_2 [1, -2, 6] = true := by decide +kernel
theorem subd14_2_589 : subd14_2 [1, -2, 7] = true := by decide +kernel
theorem subd14_2_590 : subd14_2 [1, -2, 8] = true := by decide +kernel
theorem subd14_2_591 : subd14_2 [1, -1, -9] = true := by decide +kernel
theorem subd14_2_592 : subd14_2 [1, -1, -8] = true := by decide +kernel
theorem subd14_2_593 : subd14_2 [1, -1, -7] = true := by decide +kernel
theorem subd14_2_594 : subd14_2 [1, -1, -6] = true := by decide +kernel
theorem subd14_2_595 : subd14_2 [1, -1, -5] = true := by decide +kernel
theorem subd14_2_596 : subd14_2 [1, -1, -4] = true := by decide +kernel
theorem subd14_2_597 : subd14_2 [1, -1, -3] = true := by decide +kernel
theorem subd14_2_598 : subd14_2 [1, -1, -2] = true := by decide +kernel
theorem subd14_2_599 : subd14_2 [1, -1, -1] = true := by decide +kernel
theorem subd14_2_600 : subd14_2 [1, -1, 0] = true := by decide +kernel
theorem subd14_2_601 : subd14_2 [1, -1, 1] = true := by decide +kernel
theorem subd14_2_602 : subd14_2 [1, -1, 2] = true := by decide +kernel
theorem subd14_2_603 : subd14_2 [1, -1, 3] = true := by decide +kernel
theorem subd14_2_604 : subd14_2 [1, -1, 4] = true := by decide +kernel
theorem subd14_2_605 : subd14_2 [1, -1, 5] = true := by decide +kernel
theorem subd14_2_606 : subd14_2 [1, -1, 6] = true := by decide +kernel
theorem subd14_2_607 : subd14_2 [1, -1, 7] = true := by decide +kernel
theorem sbd14_2_18 : ∀ q ∈ blkd14_2_18, subd14_2 q = true := by
  unfold blkd14_2_18
  exact List.forall_mem_cons.2 ⟨subd14_2_576, List.forall_mem_cons.2 ⟨subd14_2_577, List.forall_mem_cons.2 ⟨subd14_2_578, List.forall_mem_cons.2 ⟨subd14_2_579, List.forall_mem_cons.2 ⟨subd14_2_580, List.forall_mem_cons.2 ⟨subd14_2_581, List.forall_mem_cons.2 ⟨subd14_2_582, List.forall_mem_cons.2 ⟨subd14_2_583, List.forall_mem_cons.2 ⟨subd14_2_584, List.forall_mem_cons.2 ⟨subd14_2_585, List.forall_mem_cons.2 ⟨subd14_2_586, List.forall_mem_cons.2 ⟨subd14_2_587, List.forall_mem_cons.2 ⟨subd14_2_588, List.forall_mem_cons.2 ⟨subd14_2_589, List.forall_mem_cons.2 ⟨subd14_2_590, List.forall_mem_cons.2 ⟨subd14_2_591, List.forall_mem_cons.2 ⟨subd14_2_592, List.forall_mem_cons.2 ⟨subd14_2_593, List.forall_mem_cons.2 ⟨subd14_2_594, List.forall_mem_cons.2 ⟨subd14_2_595, List.forall_mem_cons.2 ⟨subd14_2_596, List.forall_mem_cons.2 ⟨subd14_2_597, List.forall_mem_cons.2 ⟨subd14_2_598, List.forall_mem_cons.2 ⟨subd14_2_599, List.forall_mem_cons.2 ⟨subd14_2_600, List.forall_mem_cons.2 ⟨subd14_2_601, List.forall_mem_cons.2 ⟨subd14_2_602, List.forall_mem_cons.2 ⟨subd14_2_603, List.forall_mem_cons.2 ⟨subd14_2_604, List.forall_mem_cons.2 ⟨subd14_2_605, List.forall_mem_cons.2 ⟨subd14_2_606, List.forall_mem_cons.2 ⟨subd14_2_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_2_608 : subd14_2 [1, -1, 8] = true := by decide +kernel
theorem subd14_2_609 : subd14_2 [1, -1, 9] = true := by decide +kernel
theorem subd14_2_610 : subd14_2 [1, 0, -9] = true := by decide +kernel
theorem subd14_2_611 : subd14_2 [1, 0, -8] = true := by decide +kernel
theorem subd14_2_612 : subd14_2 [1, 0, -7] = true := by decide +kernel
theorem subd14_2_613 : subd14_2 [1, 0, -6] = true := by decide +kernel
theorem subd14_2_614 : subd14_2 [1, 0, -5] = true := by decide +kernel
theorem subd14_2_615 : subd14_2 [1, 0, -4] = true := by decide +kernel
theorem subd14_2_616 : subd14_2 [1, 0, -3] = true := by decide +kernel
theorem subd14_2_617 : subd14_2 [1, 0, -2] = true := by decide +kernel
theorem subd14_2_618 : subd14_2 [1, 0, -1] = true := by decide +kernel
theorem subd14_2_619 : subd14_2 [1, 0, 0] = true := by decide +kernel
theorem subd14_2_620 : subd14_2 [1, 0, 1] = true := by decide +kernel
theorem subd14_2_621 : subd14_2 [1, 0, 2] = true := by decide +kernel
theorem subd14_2_622 : subd14_2 [1, 0, 3] = true := by decide +kernel
theorem subd14_2_623 : subd14_2 [1, 0, 4] = true := by decide +kernel
theorem subd14_2_624 : subd14_2 [1, 0, 5] = true := by decide +kernel
theorem subd14_2_625 : subd14_2 [1, 0, 6] = true := by decide +kernel
theorem subd14_2_626 : subd14_2 [1, 0, 7] = true := by decide +kernel
theorem subd14_2_627 : subd14_2 [1, 0, 8] = true := by decide +kernel
theorem subd14_2_628 : subd14_2 [1, 0, 9] = true := by decide +kernel
theorem subd14_2_629 : subd14_2 [1, 1, -9] = true := by decide +kernel
theorem subd14_2_630 : subd14_2 [1, 1, -8] = true := by decide +kernel
theorem subd14_2_631 : subd14_2 [1, 1, -7] = true := by decide +kernel
theorem subd14_2_632 : subd14_2 [1, 1, -6] = true := by decide +kernel
theorem subd14_2_633 : subd14_2 [1, 1, -5] = true := by decide +kernel
theorem subd14_2_634 : subd14_2 [1, 1, -4] = true := by decide +kernel
theorem subd14_2_635 : subd14_2 [1, 1, -3] = true := by decide +kernel
theorem subd14_2_636 : subd14_2 [1, 1, -2] = true := by decide +kernel
theorem subd14_2_637 : subd14_2 [1, 1, -1] = true := by decide +kernel
theorem subd14_2_638 : subd14_2 [1, 1, 0] = true := by decide +kernel
theorem subd14_2_639 : subd14_2 [1, 1, 1] = true := by decide +kernel
theorem sbd14_2_19 : ∀ q ∈ blkd14_2_19, subd14_2 q = true := by
  unfold blkd14_2_19
  exact List.forall_mem_cons.2 ⟨subd14_2_608, List.forall_mem_cons.2 ⟨subd14_2_609, List.forall_mem_cons.2 ⟨subd14_2_610, List.forall_mem_cons.2 ⟨subd14_2_611, List.forall_mem_cons.2 ⟨subd14_2_612, List.forall_mem_cons.2 ⟨subd14_2_613, List.forall_mem_cons.2 ⟨subd14_2_614, List.forall_mem_cons.2 ⟨subd14_2_615, List.forall_mem_cons.2 ⟨subd14_2_616, List.forall_mem_cons.2 ⟨subd14_2_617, List.forall_mem_cons.2 ⟨subd14_2_618, List.forall_mem_cons.2 ⟨subd14_2_619, List.forall_mem_cons.2 ⟨subd14_2_620, List.forall_mem_cons.2 ⟨subd14_2_621, List.forall_mem_cons.2 ⟨subd14_2_622, List.forall_mem_cons.2 ⟨subd14_2_623, List.forall_mem_cons.2 ⟨subd14_2_624, List.forall_mem_cons.2 ⟨subd14_2_625, List.forall_mem_cons.2 ⟨subd14_2_626, List.forall_mem_cons.2 ⟨subd14_2_627, List.forall_mem_cons.2 ⟨subd14_2_628, List.forall_mem_cons.2 ⟨subd14_2_629, List.forall_mem_cons.2 ⟨subd14_2_630, List.forall_mem_cons.2 ⟨subd14_2_631, List.forall_mem_cons.2 ⟨subd14_2_632, List.forall_mem_cons.2 ⟨subd14_2_633, List.forall_mem_cons.2 ⟨subd14_2_634, List.forall_mem_cons.2 ⟨subd14_2_635, List.forall_mem_cons.2 ⟨subd14_2_636, List.forall_mem_cons.2 ⟨subd14_2_637, List.forall_mem_cons.2 ⟨subd14_2_638, List.forall_mem_cons.2 ⟨subd14_2_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_2_640 : subd14_2 [1, 1, 2] = true := by decide +kernel
theorem subd14_2_641 : subd14_2 [1, 1, 3] = true := by decide +kernel
theorem subd14_2_642 : subd14_2 [1, 1, 4] = true := by decide +kernel
theorem subd14_2_643 : subd14_2 [1, 1, 5] = true := by decide +kernel
theorem subd14_2_644 : subd14_2 [1, 1, 6] = true := by decide +kernel
theorem subd14_2_645 : subd14_2 [1, 1, 7] = true := by decide +kernel
theorem subd14_2_646 : subd14_2 [1, 1, 8] = true := by decide +kernel
theorem subd14_2_647 : subd14_2 [1, 2, -8] = true := by decide +kernel
theorem subd14_2_648 : subd14_2 [1, 2, -7] = true := by decide +kernel
theorem subd14_2_649 : subd14_2 [1, 2, -6] = true := by decide +kernel
theorem subd14_2_650 : subd14_2 [1, 2, -5] = true := by decide +kernel
theorem subd14_2_651 : subd14_2 [1, 2, -4] = true := by decide +kernel
theorem subd14_2_652 : subd14_2 [1, 2, -3] = true := by decide +kernel
theorem subd14_2_653 : subd14_2 [1, 2, -2] = true := by decide +kernel
theorem subd14_2_654 : subd14_2 [1, 2, -1] = true := by decide +kernel
theorem subd14_2_655 : subd14_2 [1, 2, 0] = true := by decide +kernel
theorem subd14_2_656 : subd14_2 [1, 2, 1] = true := by decide +kernel
theorem subd14_2_657 : subd14_2 [1, 2, 2] = true := by decide +kernel
theorem subd14_2_658 : subd14_2 [1, 2, 3] = true := by decide +kernel
theorem subd14_2_659 : subd14_2 [1, 2, 4] = true := by decide +kernel
theorem subd14_2_660 : subd14_2 [1, 2, 5] = true := by decide +kernel
theorem subd14_2_661 : subd14_2 [1, 2, 6] = true := by decide +kernel
theorem subd14_2_662 : subd14_2 [1, 2, 7] = true := by decide +kernel
theorem subd14_2_663 : subd14_2 [1, 2, 8] = true := by decide +kernel
theorem subd14_2_664 : subd14_2 [1, 3, -7] = true := by decide +kernel
theorem subd14_2_665 : subd14_2 [1, 3, -6] = true := by decide +kernel
theorem subd14_2_666 : subd14_2 [1, 3, -5] = true := by decide +kernel
theorem subd14_2_667 : subd14_2 [1, 3, -4] = true := by decide +kernel
theorem subd14_2_668 : subd14_2 [1, 3, -3] = true := by decide +kernel
theorem subd14_2_669 : subd14_2 [1, 3, -2] = true := by decide +kernel
theorem subd14_2_670 : subd14_2 [1, 3, -1] = true := by decide +kernel
theorem subd14_2_671 : subd14_2 [1, 3, 0] = true := by decide +kernel
theorem sbd14_2_20 : ∀ q ∈ blkd14_2_20, subd14_2 q = true := by
  unfold blkd14_2_20
  exact List.forall_mem_cons.2 ⟨subd14_2_640, List.forall_mem_cons.2 ⟨subd14_2_641, List.forall_mem_cons.2 ⟨subd14_2_642, List.forall_mem_cons.2 ⟨subd14_2_643, List.forall_mem_cons.2 ⟨subd14_2_644, List.forall_mem_cons.2 ⟨subd14_2_645, List.forall_mem_cons.2 ⟨subd14_2_646, List.forall_mem_cons.2 ⟨subd14_2_647, List.forall_mem_cons.2 ⟨subd14_2_648, List.forall_mem_cons.2 ⟨subd14_2_649, List.forall_mem_cons.2 ⟨subd14_2_650, List.forall_mem_cons.2 ⟨subd14_2_651, List.forall_mem_cons.2 ⟨subd14_2_652, List.forall_mem_cons.2 ⟨subd14_2_653, List.forall_mem_cons.2 ⟨subd14_2_654, List.forall_mem_cons.2 ⟨subd14_2_655, List.forall_mem_cons.2 ⟨subd14_2_656, List.forall_mem_cons.2 ⟨subd14_2_657, List.forall_mem_cons.2 ⟨subd14_2_658, List.forall_mem_cons.2 ⟨subd14_2_659, List.forall_mem_cons.2 ⟨subd14_2_660, List.forall_mem_cons.2 ⟨subd14_2_661, List.forall_mem_cons.2 ⟨subd14_2_662, List.forall_mem_cons.2 ⟨subd14_2_663, List.forall_mem_cons.2 ⟨subd14_2_664, List.forall_mem_cons.2 ⟨subd14_2_665, List.forall_mem_cons.2 ⟨subd14_2_666, List.forall_mem_cons.2 ⟨subd14_2_667, List.forall_mem_cons.2 ⟨subd14_2_668, List.forall_mem_cons.2 ⟨subd14_2_669, List.forall_mem_cons.2 ⟨subd14_2_670, List.forall_mem_cons.2 ⟨subd14_2_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C142
