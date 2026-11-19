import ReflectZphi.Data.Cert5.C111.Base

namespace ReflectZphi.Data.Cert5.C111

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd5_2_192 : subd5_2 [0, -1, -5] = true := by decide +kernel
theorem subd5_2_193 : subd5_2 [0, -1, -4] = true := by decide +kernel
theorem subd5_2_194 : subd5_2 [0, -1, -3] = true := by decide +kernel
theorem subd5_2_195 : subd5_2 [0, -1, -2] = true := by decide +kernel
theorem subd5_2_196 : subd5_2 [0, -1, -1] = true := by decide +kernel
theorem subd5_2_197 : subd5_2 [0, -1, 0] = true := by decide +kernel
theorem subd5_2_198 : subd5_2 [0, -1, 1] = true := by decide +kernel
theorem subd5_2_199 : subd5_2 [0, -1, 2] = true := by decide +kernel
theorem subd5_2_200 : subd5_2 [0, -1, 3] = true := by decide +kernel
theorem subd5_2_201 : subd5_2 [0, -1, 4] = true := by decide +kernel
theorem subd5_2_202 : subd5_2 [0, -1, 5] = true := by decide +kernel
theorem subd5_2_203 : subd5_2 [0, -1, 6] = true := by decide +kernel
theorem subd5_2_204 : subd5_2 [0, -1, 7] = true := by decide +kernel
theorem subd5_2_205 : subd5_2 [0, 0, -9] = true := by decide +kernel
theorem subd5_2_206 : subd5_2 [0, 0, -8] = true := by decide +kernel
theorem subd5_2_207 : subd5_2 [0, 0, -7] = true := by decide +kernel
theorem subd5_2_208 : subd5_2 [0, 0, -6] = true := by decide +kernel
theorem subd5_2_209 : subd5_2 [0, 0, -5] = true := by decide +kernel
theorem subd5_2_210 : subd5_2 [0, 0, -4] = true := by decide +kernel
theorem subd5_2_211 : subd5_2 [0, 0, -3] = true := by decide +kernel
theorem subd5_2_212 : subd5_2 [0, 0, -2] = true := by decide +kernel
theorem subd5_2_213 : subd5_2 [0, 0, -1] = true := by decide +kernel
theorem subd5_2_214 : subd5_2 [0, 0, 0] = true := by decide +kernel
theorem subd5_2_215 : subd5_2 [0, 0, 1] = true := by decide +kernel
theorem subd5_2_216 : subd5_2 [0, 0, 2] = true := by decide +kernel
theorem subd5_2_217 : subd5_2 [0, 0, 3] = true := by decide +kernel
theorem subd5_2_218 : subd5_2 [0, 0, 4] = true := by decide +kernel
theorem subd5_2_219 : subd5_2 [0, 0, 5] = true := by decide +kernel
theorem subd5_2_220 : subd5_2 [0, 0, 6] = true := by decide +kernel
theorem subd5_2_221 : subd5_2 [0, 0, 7] = true := by decide +kernel
theorem subd5_2_222 : subd5_2 [0, 0, 8] = true := by decide +kernel
theorem subd5_2_223 : subd5_2 [0, 1, -8] = true := by decide +kernel
theorem sbd5_2_6 : ∀ q ∈ blkd5_2_6, subd5_2 q = true := by
  unfold blkd5_2_6
  exact List.forall_mem_cons.2 ⟨subd5_2_192, List.forall_mem_cons.2 ⟨subd5_2_193, List.forall_mem_cons.2 ⟨subd5_2_194, List.forall_mem_cons.2 ⟨subd5_2_195, List.forall_mem_cons.2 ⟨subd5_2_196, List.forall_mem_cons.2 ⟨subd5_2_197, List.forall_mem_cons.2 ⟨subd5_2_198, List.forall_mem_cons.2 ⟨subd5_2_199, List.forall_mem_cons.2 ⟨subd5_2_200, List.forall_mem_cons.2 ⟨subd5_2_201, List.forall_mem_cons.2 ⟨subd5_2_202, List.forall_mem_cons.2 ⟨subd5_2_203, List.forall_mem_cons.2 ⟨subd5_2_204, List.forall_mem_cons.2 ⟨subd5_2_205, List.forall_mem_cons.2 ⟨subd5_2_206, List.forall_mem_cons.2 ⟨subd5_2_207, List.forall_mem_cons.2 ⟨subd5_2_208, List.forall_mem_cons.2 ⟨subd5_2_209, List.forall_mem_cons.2 ⟨subd5_2_210, List.forall_mem_cons.2 ⟨subd5_2_211, List.forall_mem_cons.2 ⟨subd5_2_212, List.forall_mem_cons.2 ⟨subd5_2_213, List.forall_mem_cons.2 ⟨subd5_2_214, List.forall_mem_cons.2 ⟨subd5_2_215, List.forall_mem_cons.2 ⟨subd5_2_216, List.forall_mem_cons.2 ⟨subd5_2_217, List.forall_mem_cons.2 ⟨subd5_2_218, List.forall_mem_cons.2 ⟨subd5_2_219, List.forall_mem_cons.2 ⟨subd5_2_220, List.forall_mem_cons.2 ⟨subd5_2_221, List.forall_mem_cons.2 ⟨subd5_2_222, List.forall_mem_cons.2 ⟨subd5_2_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_224 : subd5_2 [0, 1, -7] = true := by decide +kernel
theorem subd5_2_225 : subd5_2 [0, 1, -6] = true := by decide +kernel
theorem subd5_2_226 : subd5_2 [0, 1, -5] = true := by decide +kernel
theorem subd5_2_227 : subd5_2 [0, 1, -4] = true := by decide +kernel
theorem subd5_2_228 : subd5_2 [0, 1, -3] = true := by decide +kernel
theorem subd5_2_229 : subd5_2 [0, 1, -2] = true := by decide +kernel
theorem subd5_2_230 : subd5_2 [0, 1, -1] = true := by decide +kernel
theorem subd5_2_231 : subd5_2 [0, 1, 0] = true := by decide +kernel
theorem subd5_2_232 : subd5_2 [0, 1, 1] = true := by decide +kernel
theorem subd5_2_233 : subd5_2 [0, 1, 2] = true := by decide +kernel
theorem subd5_2_234 : subd5_2 [0, 1, 3] = true := by decide +kernel
theorem subd5_2_235 : subd5_2 [0, 1, 4] = true := by decide +kernel
theorem subd5_2_236 : subd5_2 [0, 1, 5] = true := by decide +kernel
theorem subd5_2_237 : subd5_2 [0, 1, 6] = true := by decide +kernel
theorem subd5_2_238 : subd5_2 [0, 1, 7] = true := by decide +kernel
theorem subd5_2_239 : subd5_2 [0, 1, 8] = true := by decide +kernel
theorem subd5_2_240 : subd5_2 [0, 2, -7] = true := by decide +kernel
theorem subd5_2_241 : subd5_2 [0, 2, -6] = true := by decide +kernel
theorem subd5_2_242 : subd5_2 [0, 2, -5] = true := by decide +kernel
theorem subd5_2_243 : subd5_2 [0, 2, -4] = true := by decide +kernel
theorem subd5_2_244 : subd5_2 [0, 2, -3] = true := by decide +kernel
theorem subd5_2_245 : subd5_2 [0, 2, -2] = true := by decide +kernel
theorem subd5_2_246 : subd5_2 [0, 2, -1] = true := by decide +kernel
theorem subd5_2_247 : subd5_2 [0, 2, 0] = true := by decide +kernel
theorem subd5_2_248 : subd5_2 [0, 2, 1] = true := by decide +kernel
theorem subd5_2_249 : subd5_2 [0, 2, 2] = true := by decide +kernel
theorem subd5_2_250 : subd5_2 [0, 2, 3] = true := by decide +kernel
theorem subd5_2_251 : subd5_2 [0, 2, 4] = true := by decide +kernel
theorem subd5_2_252 : subd5_2 [0, 2, 5] = true := by decide +kernel
theorem subd5_2_253 : subd5_2 [0, 2, 6] = true := by decide +kernel
theorem subd5_2_254 : subd5_2 [0, 2, 7] = true := by decide +kernel
theorem subd5_2_255 : subd5_2 [0, 2, 8] = true := by decide +kernel
theorem sbd5_2_7 : ∀ q ∈ blkd5_2_7, subd5_2 q = true := by
  unfold blkd5_2_7
  exact List.forall_mem_cons.2 ⟨subd5_2_224, List.forall_mem_cons.2 ⟨subd5_2_225, List.forall_mem_cons.2 ⟨subd5_2_226, List.forall_mem_cons.2 ⟨subd5_2_227, List.forall_mem_cons.2 ⟨subd5_2_228, List.forall_mem_cons.2 ⟨subd5_2_229, List.forall_mem_cons.2 ⟨subd5_2_230, List.forall_mem_cons.2 ⟨subd5_2_231, List.forall_mem_cons.2 ⟨subd5_2_232, List.forall_mem_cons.2 ⟨subd5_2_233, List.forall_mem_cons.2 ⟨subd5_2_234, List.forall_mem_cons.2 ⟨subd5_2_235, List.forall_mem_cons.2 ⟨subd5_2_236, List.forall_mem_cons.2 ⟨subd5_2_237, List.forall_mem_cons.2 ⟨subd5_2_238, List.forall_mem_cons.2 ⟨subd5_2_239, List.forall_mem_cons.2 ⟨subd5_2_240, List.forall_mem_cons.2 ⟨subd5_2_241, List.forall_mem_cons.2 ⟨subd5_2_242, List.forall_mem_cons.2 ⟨subd5_2_243, List.forall_mem_cons.2 ⟨subd5_2_244, List.forall_mem_cons.2 ⟨subd5_2_245, List.forall_mem_cons.2 ⟨subd5_2_246, List.forall_mem_cons.2 ⟨subd5_2_247, List.forall_mem_cons.2 ⟨subd5_2_248, List.forall_mem_cons.2 ⟨subd5_2_249, List.forall_mem_cons.2 ⟨subd5_2_250, List.forall_mem_cons.2 ⟨subd5_2_251, List.forall_mem_cons.2 ⟨subd5_2_252, List.forall_mem_cons.2 ⟨subd5_2_253, List.forall_mem_cons.2 ⟨subd5_2_254, List.forall_mem_cons.2 ⟨subd5_2_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_256 : subd5_2 [0, 3] = true := by decide +kernel
theorem subd5_2_257 : subd5_2 [0, 4] = true := by decide +kernel
theorem subd5_2_258 : subd5_2 [1, -5] = true := by decide +kernel
theorem subd5_2_259 : subd5_2 [1, -4] = true := by decide +kernel
theorem subd5_2_260 : subd5_2 [1, -3, -9] = true := by decide +kernel
theorem subd5_2_261 : subd5_2 [1, -3, -8] = true := by decide +kernel
theorem subd5_2_262 : subd5_2 [1, -3, -7] = true := by decide +kernel
theorem subd5_2_263 : subd5_2 [1, -3, -6] = true := by decide +kernel
theorem subd5_2_264 : subd5_2 [1, -3, -5] = true := by decide +kernel
theorem subd5_2_265 : subd5_2 [1, -3, -4] = true := by decide +kernel
theorem subd5_2_266 : subd5_2 [1, -3, -3] = true := by decide +kernel
theorem subd5_2_267 : subd5_2 [1, -3, -2] = true := by decide +kernel
theorem subd5_2_268 : subd5_2 [1, -3, -1] = true := by decide +kernel
theorem subd5_2_269 : subd5_2 [1, -3, 0] = true := by decide +kernel
theorem subd5_2_270 : subd5_2 [1, -3, 1] = true := by decide +kernel
theorem subd5_2_271 : subd5_2 [1, -3, 2] = true := by decide +kernel
theorem subd5_2_272 : subd5_2 [1, -3, 3] = true := by decide +kernel
theorem subd5_2_273 : subd5_2 [1, -3, 4] = true := by decide +kernel
theorem subd5_2_274 : subd5_2 [1, -2, -9] = true := by decide +kernel
theorem subd5_2_275 : subd5_2 [1, -2, -8] = true := by decide +kernel
theorem subd5_2_276 : subd5_2 [1, -2, -7] = true := by decide +kernel
theorem subd5_2_277 : subd5_2 [1, -2, -6] = true := by decide +kernel
theorem subd5_2_278 : subd5_2 [1, -2, -5] = true := by decide +kernel
theorem subd5_2_279 : subd5_2 [1, -2, -4] = true := by decide +kernel
theorem subd5_2_280 : subd5_2 [1, -2, -3] = true := by decide +kernel
theorem subd5_2_281 : subd5_2 [1, -2, -2] = true := by decide +kernel
theorem subd5_2_282 : subd5_2 [1, -2, -1] = true := by decide +kernel
theorem subd5_2_283 : subd5_2 [1, -2, 0] = true := by decide +kernel
theorem subd5_2_284 : subd5_2 [1, -2, 1] = true := by decide +kernel
theorem subd5_2_285 : subd5_2 [1, -2, 2] = true := by decide +kernel
theorem subd5_2_286 : subd5_2 [1, -2, 3] = true := by decide +kernel
theorem subd5_2_287 : subd5_2 [1, -2, 4] = true := by decide +kernel
theorem sbd5_2_8 : ∀ q ∈ blkd5_2_8, subd5_2 q = true := by
  unfold blkd5_2_8
  exact List.forall_mem_cons.2 ⟨subd5_2_256, List.forall_mem_cons.2 ⟨subd5_2_257, List.forall_mem_cons.2 ⟨subd5_2_258, List.forall_mem_cons.2 ⟨subd5_2_259, List.forall_mem_cons.2 ⟨subd5_2_260, List.forall_mem_cons.2 ⟨subd5_2_261, List.forall_mem_cons.2 ⟨subd5_2_262, List.forall_mem_cons.2 ⟨subd5_2_263, List.forall_mem_cons.2 ⟨subd5_2_264, List.forall_mem_cons.2 ⟨subd5_2_265, List.forall_mem_cons.2 ⟨subd5_2_266, List.forall_mem_cons.2 ⟨subd5_2_267, List.forall_mem_cons.2 ⟨subd5_2_268, List.forall_mem_cons.2 ⟨subd5_2_269, List.forall_mem_cons.2 ⟨subd5_2_270, List.forall_mem_cons.2 ⟨subd5_2_271, List.forall_mem_cons.2 ⟨subd5_2_272, List.forall_mem_cons.2 ⟨subd5_2_273, List.forall_mem_cons.2 ⟨subd5_2_274, List.forall_mem_cons.2 ⟨subd5_2_275, List.forall_mem_cons.2 ⟨subd5_2_276, List.forall_mem_cons.2 ⟨subd5_2_277, List.forall_mem_cons.2 ⟨subd5_2_278, List.forall_mem_cons.2 ⟨subd5_2_279, List.forall_mem_cons.2 ⟨subd5_2_280, List.forall_mem_cons.2 ⟨subd5_2_281, List.forall_mem_cons.2 ⟨subd5_2_282, List.forall_mem_cons.2 ⟨subd5_2_283, List.forall_mem_cons.2 ⟨subd5_2_284, List.forall_mem_cons.2 ⟨subd5_2_285, List.forall_mem_cons.2 ⟨subd5_2_286, List.forall_mem_cons.2 ⟨subd5_2_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_288 : subd5_2 [1, -2, 5] = true := by decide +kernel
theorem subd5_2_289 : subd5_2 [1, -2, 6] = true := by decide +kernel
theorem subd5_2_290 : subd5_2 [1, -1, -10] = true := by decide +kernel
theorem subd5_2_291 : subd5_2 [1, -1, -9] = true := by decide +kernel
theorem subd5_2_292 : subd5_2 [1, -1, -8] = true := by decide +kernel
theorem subd5_2_293 : subd5_2 [1, -1, -7] = true := by decide +kernel
theorem subd5_2_294 : subd5_2 [1, -1, -6] = true := by decide +kernel
theorem subd5_2_295 : subd5_2 [1, -1, -5] = true := by decide +kernel
theorem subd5_2_296 : subd5_2 [1, -1, -4] = true := by decide +kernel
theorem subd5_2_297 : subd5_2 [1, -1, -3] = true := by decide +kernel
theorem subd5_2_298 : subd5_2 [1, -1, -2] = true := by decide +kernel
theorem subd5_2_299 : subd5_2 [1, -1, -1] = true := by decide +kernel
theorem subd5_2_300 : subd5_2 [1, -1, 0] = true := by decide +kernel
theorem subd5_2_301 : subd5_2 [1, -1, 1] = true := by decide +kernel
theorem subd5_2_302 : subd5_2 [1, -1, 2] = true := by decide +kernel
theorem subd5_2_303 : subd5_2 [1, -1, 3] = true := by decide +kernel
theorem subd5_2_304 : subd5_2 [1, -1, 4] = true := by decide +kernel
theorem subd5_2_305 : subd5_2 [1, -1, 5] = true := by decide +kernel
theorem subd5_2_306 : subd5_2 [1, -1, 6] = true := by decide +kernel
theorem subd5_2_307 : subd5_2 [1, -1, 7] = true := by decide +kernel
theorem subd5_2_308 : subd5_2 [1, 0, -9] = true := by decide +kernel
theorem subd5_2_309 : subd5_2 [1, 0, -8] = true := by decide +kernel
theorem subd5_2_310 : subd5_2 [1, 0, -7] = true := by decide +kernel
theorem subd5_2_311 : subd5_2 [1, 0, -6] = true := by decide +kernel
theorem subd5_2_312 : subd5_2 [1, 0, -5] = true := by decide +kernel
theorem subd5_2_313 : subd5_2 [1, 0, -4] = true := by decide +kernel
theorem subd5_2_314 : subd5_2 [1, 0, -3] = true := by decide +kernel
theorem subd5_2_315 : subd5_2 [1, 0, -2] = true := by decide +kernel
theorem subd5_2_316 : subd5_2 [1, 0, -1] = true := by decide +kernel
theorem subd5_2_317 : subd5_2 [1, 0, 0] = true := by decide +kernel
theorem subd5_2_318 : subd5_2 [1, 0, 1] = true := by decide +kernel
theorem subd5_2_319 : subd5_2 [1, 0, 2] = true := by decide +kernel
theorem sbd5_2_9 : ∀ q ∈ blkd5_2_9, subd5_2 q = true := by
  unfold blkd5_2_9
  exact List.forall_mem_cons.2 ⟨subd5_2_288, List.forall_mem_cons.2 ⟨subd5_2_289, List.forall_mem_cons.2 ⟨subd5_2_290, List.forall_mem_cons.2 ⟨subd5_2_291, List.forall_mem_cons.2 ⟨subd5_2_292, List.forall_mem_cons.2 ⟨subd5_2_293, List.forall_mem_cons.2 ⟨subd5_2_294, List.forall_mem_cons.2 ⟨subd5_2_295, List.forall_mem_cons.2 ⟨subd5_2_296, List.forall_mem_cons.2 ⟨subd5_2_297, List.forall_mem_cons.2 ⟨subd5_2_298, List.forall_mem_cons.2 ⟨subd5_2_299, List.forall_mem_cons.2 ⟨subd5_2_300, List.forall_mem_cons.2 ⟨subd5_2_301, List.forall_mem_cons.2 ⟨subd5_2_302, List.forall_mem_cons.2 ⟨subd5_2_303, List.forall_mem_cons.2 ⟨subd5_2_304, List.forall_mem_cons.2 ⟨subd5_2_305, List.forall_mem_cons.2 ⟨subd5_2_306, List.forall_mem_cons.2 ⟨subd5_2_307, List.forall_mem_cons.2 ⟨subd5_2_308, List.forall_mem_cons.2 ⟨subd5_2_309, List.forall_mem_cons.2 ⟨subd5_2_310, List.forall_mem_cons.2 ⟨subd5_2_311, List.forall_mem_cons.2 ⟨subd5_2_312, List.forall_mem_cons.2 ⟨subd5_2_313, List.forall_mem_cons.2 ⟨subd5_2_314, List.forall_mem_cons.2 ⟨subd5_2_315, List.forall_mem_cons.2 ⟨subd5_2_316, List.forall_mem_cons.2 ⟨subd5_2_317, List.forall_mem_cons.2 ⟨subd5_2_318, List.forall_mem_cons.2 ⟨subd5_2_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_320 : subd5_2 [1, 0, 3] = true := by decide +kernel
theorem subd5_2_321 : subd5_2 [1, 0, 4] = true := by decide +kernel
theorem subd5_2_322 : subd5_2 [1, 0, 5] = true := by decide +kernel
theorem subd5_2_323 : subd5_2 [1, 0, 6] = true := by decide +kernel
theorem subd5_2_324 : subd5_2 [1, 0, 7] = true := by decide +kernel
theorem subd5_2_325 : subd5_2 [1, 1, -8] = true := by decide +kernel
theorem subd5_2_326 : subd5_2 [1, 1, -7] = true := by decide +kernel
theorem subd5_2_327 : subd5_2 [1, 1, -6] = true := by decide +kernel
theorem subd5_2_328 : subd5_2 [1, 1, -5] = true := by decide +kernel
theorem subd5_2_329 : subd5_2 [1, 1, -4] = true := by decide +kernel
theorem subd5_2_330 : subd5_2 [1, 1, -3] = true := by decide +kernel
theorem subd5_2_331 : subd5_2 [1, 1, -2] = true := by decide +kernel
theorem subd5_2_332 : subd5_2 [1, 1, -1] = true := by decide +kernel
theorem subd5_2_333 : subd5_2 [1, 1, 0] = true := by decide +kernel
theorem subd5_2_334 : subd5_2 [1, 1, 1] = true := by decide +kernel
theorem subd5_2_335 : subd5_2 [1, 1, 2] = true := by decide +kernel
theorem subd5_2_336 : subd5_2 [1, 1, 3] = true := by decide +kernel
theorem subd5_2_337 : subd5_2 [1, 1, 4] = true := by decide +kernel
theorem subd5_2_338 : subd5_2 [1, 1, 5] = true := by decide +kernel
theorem subd5_2_339 : subd5_2 [1, 1, 6] = true := by decide +kernel
theorem subd5_2_340 : subd5_2 [1, 1, 7] = true := by decide +kernel
theorem subd5_2_341 : subd5_2 [1, 2, -7] = true := by decide +kernel
theorem subd5_2_342 : subd5_2 [1, 2, -6] = true := by decide +kernel
theorem subd5_2_343 : subd5_2 [1, 2, -5] = true := by decide +kernel
theorem subd5_2_344 : subd5_2 [1, 2, -4] = true := by decide +kernel
theorem subd5_2_345 : subd5_2 [1, 2, -3] = true := by decide +kernel
theorem subd5_2_346 : subd5_2 [1, 2, -2] = true := by decide +kernel
theorem subd5_2_347 : subd5_2 [1, 2, -1] = true := by decide +kernel
theorem subd5_2_348 : subd5_2 [1, 2, 0] = true := by decide +kernel
theorem subd5_2_349 : subd5_2 [1, 2, 1] = true := by decide +kernel
theorem subd5_2_350 : subd5_2 [1, 2, 2] = true := by decide +kernel
theorem subd5_2_351 : subd5_2 [1, 2, 3] = true := by decide +kernel
theorem sbd5_2_10 : ∀ q ∈ blkd5_2_10, subd5_2 q = true := by
  unfold blkd5_2_10
  exact List.forall_mem_cons.2 ⟨subd5_2_320, List.forall_mem_cons.2 ⟨subd5_2_321, List.forall_mem_cons.2 ⟨subd5_2_322, List.forall_mem_cons.2 ⟨subd5_2_323, List.forall_mem_cons.2 ⟨subd5_2_324, List.forall_mem_cons.2 ⟨subd5_2_325, List.forall_mem_cons.2 ⟨subd5_2_326, List.forall_mem_cons.2 ⟨subd5_2_327, List.forall_mem_cons.2 ⟨subd5_2_328, List.forall_mem_cons.2 ⟨subd5_2_329, List.forall_mem_cons.2 ⟨subd5_2_330, List.forall_mem_cons.2 ⟨subd5_2_331, List.forall_mem_cons.2 ⟨subd5_2_332, List.forall_mem_cons.2 ⟨subd5_2_333, List.forall_mem_cons.2 ⟨subd5_2_334, List.forall_mem_cons.2 ⟨subd5_2_335, List.forall_mem_cons.2 ⟨subd5_2_336, List.forall_mem_cons.2 ⟨subd5_2_337, List.forall_mem_cons.2 ⟨subd5_2_338, List.forall_mem_cons.2 ⟨subd5_2_339, List.forall_mem_cons.2 ⟨subd5_2_340, List.forall_mem_cons.2 ⟨subd5_2_341, List.forall_mem_cons.2 ⟨subd5_2_342, List.forall_mem_cons.2 ⟨subd5_2_343, List.forall_mem_cons.2 ⟨subd5_2_344, List.forall_mem_cons.2 ⟨subd5_2_345, List.forall_mem_cons.2 ⟨subd5_2_346, List.forall_mem_cons.2 ⟨subd5_2_347, List.forall_mem_cons.2 ⟨subd5_2_348, List.forall_mem_cons.2 ⟨subd5_2_349, List.forall_mem_cons.2 ⟨subd5_2_350, List.forall_mem_cons.2 ⟨subd5_2_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_352 : subd5_2 [1, 2, 4] = true := by decide +kernel
theorem subd5_2_353 : subd5_2 [1, 2, 5] = true := by decide +kernel
theorem subd5_2_354 : subd5_2 [1, 2, 6] = true := by decide +kernel
theorem subd5_2_355 : subd5_2 [1, 2, 7] = true := by decide +kernel
theorem subd5_2_356 : subd5_2 [1, 3] = true := by decide +kernel
theorem subd5_2_357 : subd5_2 [2, -5] = true := by decide +kernel
theorem subd5_2_358 : subd5_2 [2, -4] = true := by decide +kernel
theorem subd5_2_359 : subd5_2 [2, -3] = true := by decide +kernel
theorem subd5_2_360 : subd5_2 [2, -2, -9] = true := by decide +kernel
theorem subd5_2_361 : subd5_2 [2, -2, -8] = true := by decide +kernel
theorem subd5_2_362 : subd5_2 [2, -2, -7] = true := by decide +kernel
theorem subd5_2_363 : subd5_2 [2, -2, -6] = true := by decide +kernel
theorem subd5_2_364 : subd5_2 [2, -2, -5] = true := by decide +kernel
theorem subd5_2_365 : subd5_2 [2, -2, -4] = true := by decide +kernel
theorem subd5_2_366 : subd5_2 [2, -2, -3] = true := by decide +kernel
theorem subd5_2_367 : subd5_2 [2, -2, -2] = true := by decide +kernel
theorem subd5_2_368 : subd5_2 [2, -2, -1] = true := by decide +kernel
theorem subd5_2_369 : subd5_2 [2, -2, 0] = true := by decide +kernel
theorem subd5_2_370 : subd5_2 [2, -2, 1] = true := by decide +kernel
theorem subd5_2_371 : subd5_2 [2, -2, 2] = true := by decide +kernel
theorem subd5_2_372 : subd5_2 [2, -2, 3] = true := by decide +kernel
theorem subd5_2_373 : subd5_2 [2, -2, 4] = true := by decide +kernel
theorem subd5_2_374 : subd5_2 [2, -2, 5] = true := by decide +kernel
theorem subd5_2_375 : subd5_2 [2, -1, -9] = true := by decide +kernel
theorem subd5_2_376 : subd5_2 [2, -1, -8] = true := by decide +kernel
theorem subd5_2_377 : subd5_2 [2, -1, -7] = true := by decide +kernel
theorem subd5_2_378 : subd5_2 [2, -1, -6] = true := by decide +kernel
theorem subd5_2_379 : subd5_2 [2, -1, -5] = true := by decide +kernel
theorem subd5_2_380 : subd5_2 [2, -1, -4] = true := by decide +kernel
theorem subd5_2_381 : subd5_2 [2, -1, -3] = true := by decide +kernel
theorem subd5_2_382 : subd5_2 [2, -1, -2] = true := by decide +kernel
theorem subd5_2_383 : subd5_2 [2, -1, -1] = true := by decide +kernel
theorem sbd5_2_11 : ∀ q ∈ blkd5_2_11, subd5_2 q = true := by
  unfold blkd5_2_11
  exact List.forall_mem_cons.2 ⟨subd5_2_352, List.forall_mem_cons.2 ⟨subd5_2_353, List.forall_mem_cons.2 ⟨subd5_2_354, List.forall_mem_cons.2 ⟨subd5_2_355, List.forall_mem_cons.2 ⟨subd5_2_356, List.forall_mem_cons.2 ⟨subd5_2_357, List.forall_mem_cons.2 ⟨subd5_2_358, List.forall_mem_cons.2 ⟨subd5_2_359, List.forall_mem_cons.2 ⟨subd5_2_360, List.forall_mem_cons.2 ⟨subd5_2_361, List.forall_mem_cons.2 ⟨subd5_2_362, List.forall_mem_cons.2 ⟨subd5_2_363, List.forall_mem_cons.2 ⟨subd5_2_364, List.forall_mem_cons.2 ⟨subd5_2_365, List.forall_mem_cons.2 ⟨subd5_2_366, List.forall_mem_cons.2 ⟨subd5_2_367, List.forall_mem_cons.2 ⟨subd5_2_368, List.forall_mem_cons.2 ⟨subd5_2_369, List.forall_mem_cons.2 ⟨subd5_2_370, List.forall_mem_cons.2 ⟨subd5_2_371, List.forall_mem_cons.2 ⟨subd5_2_372, List.forall_mem_cons.2 ⟨subd5_2_373, List.forall_mem_cons.2 ⟨subd5_2_374, List.forall_mem_cons.2 ⟨subd5_2_375, List.forall_mem_cons.2 ⟨subd5_2_376, List.forall_mem_cons.2 ⟨subd5_2_377, List.forall_mem_cons.2 ⟨subd5_2_378, List.forall_mem_cons.2 ⟨subd5_2_379, List.forall_mem_cons.2 ⟨subd5_2_380, List.forall_mem_cons.2 ⟨subd5_2_381, List.forall_mem_cons.2 ⟨subd5_2_382, List.forall_mem_cons.2 ⟨subd5_2_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_384 : subd5_2 [2, -1, 0] = true := by decide +kernel
theorem subd5_2_385 : subd5_2 [2, -1, 1] = true := by decide +kernel
theorem subd5_2_386 : subd5_2 [2, -1, 2] = true := by decide +kernel
theorem subd5_2_387 : subd5_2 [2, -1, 3] = true := by decide +kernel
theorem subd5_2_388 : subd5_2 [2, -1, 4] = true := by decide +kernel
theorem subd5_2_389 : subd5_2 [2, -1, 5] = true := by decide +kernel
theorem subd5_2_390 : subd5_2 [2, -1, 6] = true := by decide +kernel
theorem subd5_2_391 : subd5_2 [2, 0, -8] = true := by decide +kernel
theorem subd5_2_392 : subd5_2 [2, 0, -7] = true := by decide +kernel
theorem subd5_2_393 : subd5_2 [2, 0, -6] = true := by decide +kernel
theorem subd5_2_394 : subd5_2 [2, 0, -5] = true := by decide +kernel
theorem subd5_2_395 : subd5_2 [2, 0, -4] = true := by decide +kernel
theorem subd5_2_396 : subd5_2 [2, 0, -3] = true := by decide +kernel
theorem subd5_2_397 : subd5_2 [2, 0, -2] = true := by decide +kernel
theorem subd5_2_398 : subd5_2 [2, 0, -1] = true := by decide +kernel
theorem subd5_2_399 : subd5_2 [2, 0, 0] = true := by decide +kernel
theorem subd5_2_400 : subd5_2 [2, 0, 1] = true := by decide +kernel
theorem subd5_2_401 : subd5_2 [2, 0, 2] = true := by decide +kernel
theorem subd5_2_402 : subd5_2 [2, 0, 3] = true := by decide +kernel
theorem subd5_2_403 : subd5_2 [2, 0, 4] = true := by decide +kernel
theorem subd5_2_404 : subd5_2 [2, 0, 5] = true := by decide +kernel
theorem subd5_2_405 : subd5_2 [2, 0, 6] = true := by decide +kernel
theorem subd5_2_406 : subd5_2 [2, 1, -7] = true := by decide +kernel
theorem subd5_2_407 : subd5_2 [2, 1, -6] = true := by decide +kernel
theorem subd5_2_408 : subd5_2 [2, 1, -5] = true := by decide +kernel
theorem subd5_2_409 : subd5_2 [2, 1, -4] = true := by decide +kernel
theorem subd5_2_410 : subd5_2 [2, 1, -3] = true := by decide +kernel
theorem subd5_2_411 : subd5_2 [2, 1, -2] = true := by decide +kernel
theorem subd5_2_412 : subd5_2 [2, 1, -1] = true := by decide +kernel
theorem subd5_2_413 : subd5_2 [2, 1, 0] = true := by decide +kernel
theorem subd5_2_414 : subd5_2 [2, 1, 1] = true := by decide +kernel
theorem subd5_2_415 : subd5_2 [2, 1, 2] = true := by decide +kernel
theorem sbd5_2_12 : ∀ q ∈ blkd5_2_12, subd5_2 q = true := by
  unfold blkd5_2_12
  exact List.forall_mem_cons.2 ⟨subd5_2_384, List.forall_mem_cons.2 ⟨subd5_2_385, List.forall_mem_cons.2 ⟨subd5_2_386, List.forall_mem_cons.2 ⟨subd5_2_387, List.forall_mem_cons.2 ⟨subd5_2_388, List.forall_mem_cons.2 ⟨subd5_2_389, List.forall_mem_cons.2 ⟨subd5_2_390, List.forall_mem_cons.2 ⟨subd5_2_391, List.forall_mem_cons.2 ⟨subd5_2_392, List.forall_mem_cons.2 ⟨subd5_2_393, List.forall_mem_cons.2 ⟨subd5_2_394, List.forall_mem_cons.2 ⟨subd5_2_395, List.forall_mem_cons.2 ⟨subd5_2_396, List.forall_mem_cons.2 ⟨subd5_2_397, List.forall_mem_cons.2 ⟨subd5_2_398, List.forall_mem_cons.2 ⟨subd5_2_399, List.forall_mem_cons.2 ⟨subd5_2_400, List.forall_mem_cons.2 ⟨subd5_2_401, List.forall_mem_cons.2 ⟨subd5_2_402, List.forall_mem_cons.2 ⟨subd5_2_403, List.forall_mem_cons.2 ⟨subd5_2_404, List.forall_mem_cons.2 ⟨subd5_2_405, List.forall_mem_cons.2 ⟨subd5_2_406, List.forall_mem_cons.2 ⟨subd5_2_407, List.forall_mem_cons.2 ⟨subd5_2_408, List.forall_mem_cons.2 ⟨subd5_2_409, List.forall_mem_cons.2 ⟨subd5_2_410, List.forall_mem_cons.2 ⟨subd5_2_411, List.forall_mem_cons.2 ⟨subd5_2_412, List.forall_mem_cons.2 ⟨subd5_2_413, List.forall_mem_cons.2 ⟨subd5_2_414, List.forall_mem_cons.2 ⟨subd5_2_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_2_416 : subd5_2 [2, 1, 3] = true := by decide +kernel
theorem subd5_2_417 : subd5_2 [2, 1, 4] = true := by decide +kernel
theorem subd5_2_418 : subd5_2 [2, 1, 5] = true := by decide +kernel
theorem subd5_2_419 : subd5_2 [2, 1, 6] = true := by decide +kernel
theorem subd5_2_420 : subd5_2 [2, 2] = true := by decide +kernel
theorem subd5_2_421 : subd5_2 [3, -4] = true := by decide +kernel
theorem subd5_2_422 : subd5_2 [3, -3] = true := by decide +kernel
theorem subd5_2_423 : subd5_2 [3, -2] = true := by decide +kernel
theorem subd5_2_424 : subd5_2 [3, -1] = true := by decide +kernel
theorem subd5_2_425 : subd5_2 [3, 0] = true := by decide +kernel
theorem subd5_2_426 : subd5_2 [3, 1] = true := by decide +kernel
theorem sbd5_2_13 : ∀ q ∈ blkd5_2_13, subd5_2 q = true := by
  unfold blkd5_2_13
  exact List.forall_mem_cons.2 ⟨subd5_2_416, List.forall_mem_cons.2 ⟨subd5_2_417, List.forall_mem_cons.2 ⟨subd5_2_418, List.forall_mem_cons.2 ⟨subd5_2_419, List.forall_mem_cons.2 ⟨subd5_2_420, List.forall_mem_cons.2 ⟨subd5_2_421, List.forall_mem_cons.2 ⟨subd5_2_422, List.forall_mem_cons.2 ⟨subd5_2_423, List.forall_mem_cons.2 ⟨subd5_2_424, List.forall_mem_cons.2 ⟨subd5_2_425, List.forall_mem_cons.2 ⟨subd5_2_426, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_3 : ldCheck G d5_3.U d5_3.ms ldd5_3 = true := by decide +kernel
theorem pre_okd5_3 : subPre G cell5 d5_3 = true := by decide +kernel
theorem subd5_3_0 : subd5_3 [-4, -5] = true := by decide +kernel
theorem subd5_3_1 : subd5_3 [-4, -4] = true := by decide +kernel
theorem subd5_3_2 : subd5_3 [-4, -3] = true := by decide +kernel
theorem subd5_3_3 : subd5_3 [-4, -2] = true := by decide +kernel
theorem subd5_3_4 : subd5_3 [-4, -1] = true := by decide +kernel
theorem subd5_3_5 : subd5_3 [-4, 0] = true := by decide +kernel
theorem subd5_3_6 : subd5_3 [-3, -6] = true := by decide +kernel
theorem subd5_3_7 : subd5_3 [-3, -5] = true := by decide +kernel
theorem subd5_3_8 : subd5_3 [-3, -4] = true := by decide +kernel
theorem subd5_3_9 : subd5_3 [-3, -3] = true := by decide +kernel
theorem subd5_3_10 : subd5_3 [-3, -2] = true := by decide +kernel
theorem subd5_3_11 : subd5_3 [-3, -1] = true := by decide +kernel
theorem subd5_3_12 : subd5_3 [-3, 0] = true := by decide +kernel
theorem subd5_3_13 : subd5_3 [-3, 1] = true := by decide +kernel
theorem subd5_3_14 : subd5_3 [-3, 2] = true := by decide +kernel
theorem subd5_3_15 : subd5_3 [-2, -6] = true := by decide +kernel
theorem subd5_3_16 : subd5_3 [-2, -5] = true := by decide +kernel
theorem subd5_3_17 : subd5_3 [-2, -4] = true := by decide +kernel
theorem subd5_3_18 : subd5_3 [-2, -3] = true := by decide +kernel
theorem subd5_3_19 : subd5_3 [-2, -2, -7] = true := by decide +kernel
theorem subd5_3_20 : subd5_3 [-2, -2, -6] = true := by decide +kernel
theorem subd5_3_21 : subd5_3 [-2, -2, -5] = true := by decide +kernel
theorem subd5_3_22 : subd5_3 [-2, -2, -4] = true := by decide +kernel
theorem subd5_3_23 : subd5_3 [-2, -2, -3] = true := by decide +kernel
theorem subd5_3_24 : subd5_3 [-2, -2, -2] = true := by decide +kernel
theorem subd5_3_25 : subd5_3 [-2, -2, -1] = true := by decide +kernel
theorem subd5_3_26 : subd5_3 [-2, -2, 0] = true := by decide +kernel
theorem subd5_3_27 : subd5_3 [-2, -2, 1] = true := by decide +kernel
theorem subd5_3_28 : subd5_3 [-2, -2, 2] = true := by decide +kernel
theorem subd5_3_29 : subd5_3 [-2, -2, 3] = true := by decide +kernel
theorem subd5_3_30 : subd5_3 [-2, -2, 4] = true := by decide +kernel
theorem subd5_3_31 : subd5_3 [-2, -2, 5] = true := by decide +kernel
theorem sbd5_3_0 : ∀ q ∈ blkd5_3_0, subd5_3 q = true := by
  unfold blkd5_3_0
  exact List.forall_mem_cons.2 ⟨subd5_3_0, List.forall_mem_cons.2 ⟨subd5_3_1, List.forall_mem_cons.2 ⟨subd5_3_2, List.forall_mem_cons.2 ⟨subd5_3_3, List.forall_mem_cons.2 ⟨subd5_3_4, List.forall_mem_cons.2 ⟨subd5_3_5, List.forall_mem_cons.2 ⟨subd5_3_6, List.forall_mem_cons.2 ⟨subd5_3_7, List.forall_mem_cons.2 ⟨subd5_3_8, List.forall_mem_cons.2 ⟨subd5_3_9, List.forall_mem_cons.2 ⟨subd5_3_10, List.forall_mem_cons.2 ⟨subd5_3_11, List.forall_mem_cons.2 ⟨subd5_3_12, List.forall_mem_cons.2 ⟨subd5_3_13, List.forall_mem_cons.2 ⟨subd5_3_14, List.forall_mem_cons.2 ⟨subd5_3_15, List.forall_mem_cons.2 ⟨subd5_3_16, List.forall_mem_cons.2 ⟨subd5_3_17, List.forall_mem_cons.2 ⟨subd5_3_18, List.forall_mem_cons.2 ⟨subd5_3_19, List.forall_mem_cons.2 ⟨subd5_3_20, List.forall_mem_cons.2 ⟨subd5_3_21, List.forall_mem_cons.2 ⟨subd5_3_22, List.forall_mem_cons.2 ⟨subd5_3_23, List.forall_mem_cons.2 ⟨subd5_3_24, List.forall_mem_cons.2 ⟨subd5_3_25, List.forall_mem_cons.2 ⟨subd5_3_26, List.forall_mem_cons.2 ⟨subd5_3_27, List.forall_mem_cons.2 ⟨subd5_3_28, List.forall_mem_cons.2 ⟨subd5_3_29, List.forall_mem_cons.2 ⟨subd5_3_30, List.forall_mem_cons.2 ⟨subd5_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_3_32 : subd5_3 [-2, -2, 6] = true := by decide +kernel
theorem subd5_3_33 : subd5_3 [-2, -2, 7] = true := by decide +kernel
theorem subd5_3_34 : subd5_3 [-2, -1, -7] = true := by decide +kernel
theorem subd5_3_35 : subd5_3 [-2, -1, -6] = true := by decide +kernel
theorem subd5_3_36 : subd5_3 [-2, -1, -5] = true := by decide +kernel
theorem subd5_3_37 : subd5_3 [-2, -1, -4] = true := by decide +kernel
theorem subd5_3_38 : subd5_3 [-2, -1, -3] = true := by decide +kernel
theorem subd5_3_39 : subd5_3 [-2, -1, -2] = true := by decide +kernel
theorem subd5_3_40 : subd5_3 [-2, -1, -1] = true := by decide +kernel
theorem subd5_3_41 : subd5_3 [-2, -1, 0] = true := by decide +kernel
theorem subd5_3_42 : subd5_3 [-2, -1, 1] = true := by decide +kernel
theorem subd5_3_43 : subd5_3 [-2, -1, 2] = true := by decide +kernel
theorem subd5_3_44 : subd5_3 [-2, -1, 3] = true := by decide +kernel
theorem subd5_3_45 : subd5_3 [-2, -1, 4] = true := by decide +kernel
theorem subd5_3_46 : subd5_3 [-2, -1, 5] = true := by decide +kernel
theorem subd5_3_47 : subd5_3 [-2, -1, 6] = true := by decide +kernel
theorem subd5_3_48 : subd5_3 [-2, -1, 7] = true := by decide +kernel
theorem subd5_3_49 : subd5_3 [-2, -1, 8] = true := by decide +kernel
theorem subd5_3_50 : subd5_3 [-2, 0, -7] = true := by decide +kernel
theorem subd5_3_51 : subd5_3 [-2, 0, -6] = true := by decide +kernel
theorem subd5_3_52 : subd5_3 [-2, 0, -5] = true := by decide +kernel
theorem subd5_3_53 : subd5_3 [-2, 0, -4] = true := by decide +kernel
theorem subd5_3_54 : subd5_3 [-2, 0, -3] = true := by decide +kernel
theorem subd5_3_55 : subd5_3 [-2, 0, -2] = true := by decide +kernel
theorem subd5_3_56 : subd5_3 [-2, 0, -1] = true := by decide +kernel
theorem subd5_3_57 : subd5_3 [-2, 0, 0] = true := by decide +kernel
theorem subd5_3_58 : subd5_3 [-2, 0, 1] = true := by decide +kernel
theorem subd5_3_59 : subd5_3 [-2, 0, 2] = true := by decide +kernel
theorem subd5_3_60 : subd5_3 [-2, 0, 3] = true := by decide +kernel
theorem subd5_3_61 : subd5_3 [-2, 0, 4] = true := by decide +kernel
theorem subd5_3_62 : subd5_3 [-2, 0, 5] = true := by decide +kernel
theorem subd5_3_63 : subd5_3 [-2, 0, 6] = true := by decide +kernel
theorem sbd5_3_1 : ∀ q ∈ blkd5_3_1, subd5_3 q = true := by
  unfold blkd5_3_1
  exact List.forall_mem_cons.2 ⟨subd5_3_32, List.forall_mem_cons.2 ⟨subd5_3_33, List.forall_mem_cons.2 ⟨subd5_3_34, List.forall_mem_cons.2 ⟨subd5_3_35, List.forall_mem_cons.2 ⟨subd5_3_36, List.forall_mem_cons.2 ⟨subd5_3_37, List.forall_mem_cons.2 ⟨subd5_3_38, List.forall_mem_cons.2 ⟨subd5_3_39, List.forall_mem_cons.2 ⟨subd5_3_40, List.forall_mem_cons.2 ⟨subd5_3_41, List.forall_mem_cons.2 ⟨subd5_3_42, List.forall_mem_cons.2 ⟨subd5_3_43, List.forall_mem_cons.2 ⟨subd5_3_44, List.forall_mem_cons.2 ⟨subd5_3_45, List.forall_mem_cons.2 ⟨subd5_3_46, List.forall_mem_cons.2 ⟨subd5_3_47, List.forall_mem_cons.2 ⟨subd5_3_48, List.forall_mem_cons.2 ⟨subd5_3_49, List.forall_mem_cons.2 ⟨subd5_3_50, List.forall_mem_cons.2 ⟨subd5_3_51, List.forall_mem_cons.2 ⟨subd5_3_52, List.forall_mem_cons.2 ⟨subd5_3_53, List.forall_mem_cons.2 ⟨subd5_3_54, List.forall_mem_cons.2 ⟨subd5_3_55, List.forall_mem_cons.2 ⟨subd5_3_56, List.forall_mem_cons.2 ⟨subd5_3_57, List.forall_mem_cons.2 ⟨subd5_3_58, List.forall_mem_cons.2 ⟨subd5_3_59, List.forall_mem_cons.2 ⟨subd5_3_60, List.forall_mem_cons.2 ⟨subd5_3_61, List.forall_mem_cons.2 ⟨subd5_3_62, List.forall_mem_cons.2 ⟨subd5_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_3_64 : subd5_3 [-2, 0, 7] = true := by decide +kernel
theorem subd5_3_65 : subd5_3 [-2, 0, 8] = true := by decide +kernel
theorem subd5_3_66 : subd5_3 [-2, 1, -6] = true := by decide +kernel
theorem subd5_3_67 : subd5_3 [-2, 1, -5] = true := by decide +kernel
theorem subd5_3_68 : subd5_3 [-2, 1, -4] = true := by decide +kernel
theorem subd5_3_69 : subd5_3 [-2, 1, -3] = true := by decide +kernel
theorem subd5_3_70 : subd5_3 [-2, 1, -2] = true := by decide +kernel
theorem subd5_3_71 : subd5_3 [-2, 1, -1] = true := by decide +kernel
theorem subd5_3_72 : subd5_3 [-2, 1, 0] = true := by decide +kernel
theorem subd5_3_73 : subd5_3 [-2, 1, 1] = true := by decide +kernel
theorem subd5_3_74 : subd5_3 [-2, 1, 2] = true := by decide +kernel
theorem subd5_3_75 : subd5_3 [-2, 1, 3] = true := by decide +kernel
theorem subd5_3_76 : subd5_3 [-2, 1, 4] = true := by decide +kernel
theorem subd5_3_77 : subd5_3 [-2, 1, 5] = true := by decide +kernel
theorem subd5_3_78 : subd5_3 [-2, 1, 6] = true := by decide +kernel
theorem subd5_3_79 : subd5_3 [-2, 1, 7] = true := by decide +kernel
theorem subd5_3_80 : subd5_3 [-2, 1, 8] = true := by decide +kernel
theorem subd5_3_81 : subd5_3 [-2, 2] = true := by decide +kernel
theorem subd5_3_82 : subd5_3 [-2, 3] = true := by decide +kernel
theorem subd5_3_83 : subd5_3 [-1, -6] = true := by decide +kernel
theorem subd5_3_84 : subd5_3 [-1, -5] = true := by decide +kernel
theorem subd5_3_85 : subd5_3 [-1, -4] = true := by decide +kernel
theorem subd5_3_86 : subd5_3 [-1, -3, -8] = true := by decide +kernel
theorem subd5_3_87 : subd5_3 [-1, -3, -7] = true := by decide +kernel
theorem subd5_3_88 : subd5_3 [-1, -3, -6] = true := by decide +kernel
theorem subd5_3_89 : subd5_3 [-1, -3, -5] = true := by decide +kernel
theorem subd5_3_90 : subd5_3 [-1, -3, -4] = true := by decide +kernel
theorem subd5_3_91 : subd5_3 [-1, -3, -3] = true := by decide +kernel
theorem subd5_3_92 : subd5_3 [-1, -3, -2] = true := by decide +kernel
theorem subd5_3_93 : subd5_3 [-1, -3, -1] = true := by decide +kernel
theorem subd5_3_94 : subd5_3 [-1, -3, 0] = true := by decide +kernel
theorem subd5_3_95 : subd5_3 [-1, -3, 1] = true := by decide +kernel
theorem sbd5_3_2 : ∀ q ∈ blkd5_3_2, subd5_3 q = true := by
  unfold blkd5_3_2
  exact List.forall_mem_cons.2 ⟨subd5_3_64, List.forall_mem_cons.2 ⟨subd5_3_65, List.forall_mem_cons.2 ⟨subd5_3_66, List.forall_mem_cons.2 ⟨subd5_3_67, List.forall_mem_cons.2 ⟨subd5_3_68, List.forall_mem_cons.2 ⟨subd5_3_69, List.forall_mem_cons.2 ⟨subd5_3_70, List.forall_mem_cons.2 ⟨subd5_3_71, List.forall_mem_cons.2 ⟨subd5_3_72, List.forall_mem_cons.2 ⟨subd5_3_73, List.forall_mem_cons.2 ⟨subd5_3_74, List.forall_mem_cons.2 ⟨subd5_3_75, List.forall_mem_cons.2 ⟨subd5_3_76, List.forall_mem_cons.2 ⟨subd5_3_77, List.forall_mem_cons.2 ⟨subd5_3_78, List.forall_mem_cons.2 ⟨subd5_3_79, List.forall_mem_cons.2 ⟨subd5_3_80, List.forall_mem_cons.2 ⟨subd5_3_81, List.forall_mem_cons.2 ⟨subd5_3_82, List.forall_mem_cons.2 ⟨subd5_3_83, List.forall_mem_cons.2 ⟨subd5_3_84, List.forall_mem_cons.2 ⟨subd5_3_85, List.forall_mem_cons.2 ⟨subd5_3_86, List.forall_mem_cons.2 ⟨subd5_3_87, List.forall_mem_cons.2 ⟨subd5_3_88, List.forall_mem_cons.2 ⟨subd5_3_89, List.forall_mem_cons.2 ⟨subd5_3_90, List.forall_mem_cons.2 ⟨subd5_3_91, List.forall_mem_cons.2 ⟨subd5_3_92, List.forall_mem_cons.2 ⟨subd5_3_93, List.forall_mem_cons.2 ⟨subd5_3_94, List.forall_mem_cons.2 ⟨subd5_3_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_3_96 : subd5_3 [-1, -3, 2] = true := by decide +kernel
theorem subd5_3_97 : subd5_3 [-1, -3, 3] = true := by decide +kernel
theorem subd5_3_98 : subd5_3 [-1, -3, 4] = true := by decide +kernel
theorem subd5_3_99 : subd5_3 [-1, -3, 5] = true := by decide +kernel
theorem subd5_3_100 : subd5_3 [-1, -3, 6] = true := by decide +kernel
theorem subd5_3_101 : subd5_3 [-1, -2, -8] = true := by decide +kernel
theorem subd5_3_102 : subd5_3 [-1, -2, -7] = true := by decide +kernel
theorem subd5_3_103 : subd5_3 [-1, -2, -6] = true := by decide +kernel
theorem subd5_3_104 : subd5_3 [-1, -2, -5] = true := by decide +kernel
theorem subd5_3_105 : subd5_3 [-1, -2, -4] = true := by decide +kernel
theorem subd5_3_106 : subd5_3 [-1, -2, -3] = true := by decide +kernel
theorem subd5_3_107 : subd5_3 [-1, -2, -2] = true := by decide +kernel
theorem subd5_3_108 : subd5_3 [-1, -2, -1] = true := by decide +kernel
theorem subd5_3_109 : subd5_3 [-1, -2, 0] = true := by decide +kernel
theorem subd5_3_110 : subd5_3 [-1, -2, 1] = true := by decide +kernel
theorem subd5_3_111 : subd5_3 [-1, -2, 2] = true := by decide +kernel
theorem subd5_3_112 : subd5_3 [-1, -2, 3] = true := by decide +kernel
theorem subd5_3_113 : subd5_3 [-1, -2, 4] = true := by decide +kernel
theorem subd5_3_114 : subd5_3 [-1, -2, 5] = true := by decide +kernel
theorem subd5_3_115 : subd5_3 [-1, -2, 6] = true := by decide +kernel
theorem subd5_3_116 : subd5_3 [-1, -2, 7] = true := by decide +kernel
theorem subd5_3_117 : subd5_3 [-1, -1, -9] = true := by decide +kernel
theorem subd5_3_118 : subd5_3 [-1, -1, -8] = true := by decide +kernel
theorem subd5_3_119 : subd5_3 [-1, -1, -7] = true := by decide +kernel
theorem subd5_3_120 : subd5_3 [-1, -1, -6] = true := by decide +kernel
theorem subd5_3_121 : subd5_3 [-1, -1, -5] = true := by decide +kernel
theorem subd5_3_122 : subd5_3 [-1, -1, -4] = true := by decide +kernel
theorem subd5_3_123 : subd5_3 [-1, -1, -3] = true := by decide +kernel
theorem subd5_3_124 : subd5_3 [-1, -1, -2] = true := by decide +kernel
theorem subd5_3_125 : subd5_3 [-1, -1, -1] = true := by decide +kernel
theorem subd5_3_126 : subd5_3 [-1, -1, 0] = true := by decide +kernel
theorem subd5_3_127 : subd5_3 [-1, -1, 1] = true := by decide +kernel
theorem sbd5_3_3 : ∀ q ∈ blkd5_3_3, subd5_3 q = true := by
  unfold blkd5_3_3
  exact List.forall_mem_cons.2 ⟨subd5_3_96, List.forall_mem_cons.2 ⟨subd5_3_97, List.forall_mem_cons.2 ⟨subd5_3_98, List.forall_mem_cons.2 ⟨subd5_3_99, List.forall_mem_cons.2 ⟨subd5_3_100, List.forall_mem_cons.2 ⟨subd5_3_101, List.forall_mem_cons.2 ⟨subd5_3_102, List.forall_mem_cons.2 ⟨subd5_3_103, List.forall_mem_cons.2 ⟨subd5_3_104, List.forall_mem_cons.2 ⟨subd5_3_105, List.forall_mem_cons.2 ⟨subd5_3_106, List.forall_mem_cons.2 ⟨subd5_3_107, List.forall_mem_cons.2 ⟨subd5_3_108, List.forall_mem_cons.2 ⟨subd5_3_109, List.forall_mem_cons.2 ⟨subd5_3_110, List.forall_mem_cons.2 ⟨subd5_3_111, List.forall_mem_cons.2 ⟨subd5_3_112, List.forall_mem_cons.2 ⟨subd5_3_113, List.forall_mem_cons.2 ⟨subd5_3_114, List.forall_mem_cons.2 ⟨subd5_3_115, List.forall_mem_cons.2 ⟨subd5_3_116, List.forall_mem_cons.2 ⟨subd5_3_117, List.forall_mem_cons.2 ⟨subd5_3_118, List.forall_mem_cons.2 ⟨subd5_3_119, List.forall_mem_cons.2 ⟨subd5_3_120, List.forall_mem_cons.2 ⟨subd5_3_121, List.forall_mem_cons.2 ⟨subd5_3_122, List.forall_mem_cons.2 ⟨subd5_3_123, List.forall_mem_cons.2 ⟨subd5_3_124, List.forall_mem_cons.2 ⟨subd5_3_125, List.forall_mem_cons.2 ⟨subd5_3_126, List.forall_mem_cons.2 ⟨subd5_3_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C111
