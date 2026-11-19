import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_2_224 : subd8_2 [0, -1, -13] = true := by decide +kernel
theorem subd8_2_225 : subd8_2 [0, -1, -12] = true := by decide +kernel
theorem subd8_2_226 : subd8_2 [0, -1, -11] = true := by decide +kernel
theorem subd8_2_227 : subd8_2 [0, -1, -10] = true := by decide +kernel
theorem subd8_2_228 : subd8_2 [0, -1, -9] = true := by decide +kernel
theorem subd8_2_229 : subd8_2 [0, -1, -8] = true := by decide +kernel
theorem subd8_2_230 : subd8_2 [0, -1, -7] = true := by decide +kernel
theorem subd8_2_231 : subd8_2 [0, -1, -6] = true := by decide +kernel
theorem subd8_2_232 : subd8_2 [0, -1, -5] = true := by decide +kernel
theorem subd8_2_233 : subd8_2 [0, -1, -4] = true := by decide +kernel
theorem subd8_2_234 : subd8_2 [0, -1, -3] = true := by decide +kernel
theorem subd8_2_235 : subd8_2 [0, -1, -2] = true := by decide +kernel
theorem subd8_2_236 : subd8_2 [0, -1, -1] = true := by decide +kernel
theorem subd8_2_237 : subd8_2 [0, -1, 0] = true := by decide +kernel
theorem subd8_2_238 : subd8_2 [0, -1, 1] = true := by decide +kernel
theorem subd8_2_239 : subd8_2 [0, -1, 2] = true := by decide +kernel
theorem subd8_2_240 : subd8_2 [0, -1, 3] = true := by decide +kernel
theorem subd8_2_241 : subd8_2 [0, -1, 4] = true := by decide +kernel
theorem subd8_2_242 : subd8_2 [0, -1, 5] = true := by decide +kernel
theorem subd8_2_243 : subd8_2 [0, -1, 6] = true := by decide +kernel
theorem subd8_2_244 : subd8_2 [0, -1, 7] = true := by decide +kernel
theorem subd8_2_245 : subd8_2 [0, -1, 8] = true := by decide +kernel
theorem subd8_2_246 : subd8_2 [0, -1, 9] = true := by decide +kernel
theorem subd8_2_247 : subd8_2 [0, -1, 10] = true := by decide +kernel
theorem subd8_2_248 : subd8_2 [0, -1, 11] = true := by decide +kernel
theorem subd8_2_249 : subd8_2 [0, -1, 12] = true := by decide +kernel
theorem subd8_2_250 : subd8_2 [0, -1, 13] = true := by decide +kernel
theorem subd8_2_251 : subd8_2 [0, -1, 14] = true := by decide +kernel
theorem subd8_2_252 : subd8_2 [0, -1, 15] = true := by decide +kernel
theorem subd8_2_253 : subd8_2 [0, -1, 16] = true := by decide +kernel
theorem subd8_2_254 : subd8_2 [0, -1, 17] = true := by decide +kernel
theorem subd8_2_255 : subd8_2 [0, -1, 18] = true := by decide +kernel
theorem sbd8_2_7 : ∀ q ∈ blkd8_2_7, subd8_2 q = true := by
  unfold blkd8_2_7
  exact List.forall_mem_cons.2 ⟨subd8_2_224, List.forall_mem_cons.2 ⟨subd8_2_225, List.forall_mem_cons.2 ⟨subd8_2_226, List.forall_mem_cons.2 ⟨subd8_2_227, List.forall_mem_cons.2 ⟨subd8_2_228, List.forall_mem_cons.2 ⟨subd8_2_229, List.forall_mem_cons.2 ⟨subd8_2_230, List.forall_mem_cons.2 ⟨subd8_2_231, List.forall_mem_cons.2 ⟨subd8_2_232, List.forall_mem_cons.2 ⟨subd8_2_233, List.forall_mem_cons.2 ⟨subd8_2_234, List.forall_mem_cons.2 ⟨subd8_2_235, List.forall_mem_cons.2 ⟨subd8_2_236, List.forall_mem_cons.2 ⟨subd8_2_237, List.forall_mem_cons.2 ⟨subd8_2_238, List.forall_mem_cons.2 ⟨subd8_2_239, List.forall_mem_cons.2 ⟨subd8_2_240, List.forall_mem_cons.2 ⟨subd8_2_241, List.forall_mem_cons.2 ⟨subd8_2_242, List.forall_mem_cons.2 ⟨subd8_2_243, List.forall_mem_cons.2 ⟨subd8_2_244, List.forall_mem_cons.2 ⟨subd8_2_245, List.forall_mem_cons.2 ⟨subd8_2_246, List.forall_mem_cons.2 ⟨subd8_2_247, List.forall_mem_cons.2 ⟨subd8_2_248, List.forall_mem_cons.2 ⟨subd8_2_249, List.forall_mem_cons.2 ⟨subd8_2_250, List.forall_mem_cons.2 ⟨subd8_2_251, List.forall_mem_cons.2 ⟨subd8_2_252, List.forall_mem_cons.2 ⟨subd8_2_253, List.forall_mem_cons.2 ⟨subd8_2_254, List.forall_mem_cons.2 ⟨subd8_2_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_256 : subd8_2 [0, -1, 19] = true := by decide +kernel
theorem subd8_2_257 : subd8_2 [0, 0, -22] = true := by decide +kernel
theorem subd8_2_258 : subd8_2 [0, 0, -21] = true := by decide +kernel
theorem subd8_2_259 : subd8_2 [0, 0, -20] = true := by decide +kernel
theorem subd8_2_260 : subd8_2 [0, 0, -19] = true := by decide +kernel
theorem subd8_2_261 : subd8_2 [0, 0, -18] = true := by decide +kernel
theorem subd8_2_262 : subd8_2 [0, 0, -17] = true := by decide +kernel
theorem subd8_2_263 : subd8_2 [0, 0, -16] = true := by decide +kernel
theorem subd8_2_264 : subd8_2 [0, 0, -15] = true := by decide +kernel
theorem subd8_2_265 : subd8_2 [0, 0, -14] = true := by decide +kernel
theorem subd8_2_266 : subd8_2 [0, 0, -13] = true := by decide +kernel
theorem subd8_2_267 : subd8_2 [0, 0, -12] = true := by decide +kernel
theorem subd8_2_268 : subd8_2 [0, 0, -11] = true := by decide +kernel
theorem subd8_2_269 : subd8_2 [0, 0, -10] = true := by decide +kernel
theorem subd8_2_270 : subd8_2 [0, 0, -9] = true := by decide +kernel
theorem subd8_2_271 : subd8_2 [0, 0, -8] = true := by decide +kernel
theorem subd8_2_272 : subd8_2 [0, 0, -7] = true := by decide +kernel
theorem subd8_2_273 : subd8_2 [0, 0, -6] = true := by decide +kernel
theorem subd8_2_274 : subd8_2 [0, 0, -5] = true := by decide +kernel
theorem subd8_2_275 : subd8_2 [0, 0, -4] = true := by decide +kernel
theorem subd8_2_276 : subd8_2 [0, 0, -3] = true := by decide +kernel
theorem subd8_2_277 : subd8_2 [0, 0, -2] = true := by decide +kernel
theorem subd8_2_278 : subd8_2 [0, 0, -1] = true := by decide +kernel
theorem subd8_2_279 : subd8_2 [0, 0, 0] = true := by decide +kernel
theorem subd8_2_280 : subd8_2 [0, 0, 1] = true := by decide +kernel
theorem subd8_2_281 : subd8_2 [0, 0, 2] = true := by decide +kernel
theorem subd8_2_282 : subd8_2 [0, 0, 3] = true := by decide +kernel
theorem subd8_2_283 : subd8_2 [0, 0, 4] = true := by decide +kernel
theorem subd8_2_284 : subd8_2 [0, 0, 5] = true := by decide +kernel
theorem subd8_2_285 : subd8_2 [0, 0, 6] = true := by decide +kernel
theorem subd8_2_286 : subd8_2 [0, 0, 7] = true := by decide +kernel
theorem subd8_2_287 : subd8_2 [0, 0, 8] = true := by decide +kernel
theorem sbd8_2_8 : ∀ q ∈ blkd8_2_8, subd8_2 q = true := by
  unfold blkd8_2_8
  exact List.forall_mem_cons.2 ⟨subd8_2_256, List.forall_mem_cons.2 ⟨subd8_2_257, List.forall_mem_cons.2 ⟨subd8_2_258, List.forall_mem_cons.2 ⟨subd8_2_259, List.forall_mem_cons.2 ⟨subd8_2_260, List.forall_mem_cons.2 ⟨subd8_2_261, List.forall_mem_cons.2 ⟨subd8_2_262, List.forall_mem_cons.2 ⟨subd8_2_263, List.forall_mem_cons.2 ⟨subd8_2_264, List.forall_mem_cons.2 ⟨subd8_2_265, List.forall_mem_cons.2 ⟨subd8_2_266, List.forall_mem_cons.2 ⟨subd8_2_267, List.forall_mem_cons.2 ⟨subd8_2_268, List.forall_mem_cons.2 ⟨subd8_2_269, List.forall_mem_cons.2 ⟨subd8_2_270, List.forall_mem_cons.2 ⟨subd8_2_271, List.forall_mem_cons.2 ⟨subd8_2_272, List.forall_mem_cons.2 ⟨subd8_2_273, List.forall_mem_cons.2 ⟨subd8_2_274, List.forall_mem_cons.2 ⟨subd8_2_275, List.forall_mem_cons.2 ⟨subd8_2_276, List.forall_mem_cons.2 ⟨subd8_2_277, List.forall_mem_cons.2 ⟨subd8_2_278, List.forall_mem_cons.2 ⟨subd8_2_279, List.forall_mem_cons.2 ⟨subd8_2_280, List.forall_mem_cons.2 ⟨subd8_2_281, List.forall_mem_cons.2 ⟨subd8_2_282, List.forall_mem_cons.2 ⟨subd8_2_283, List.forall_mem_cons.2 ⟨subd8_2_284, List.forall_mem_cons.2 ⟨subd8_2_285, List.forall_mem_cons.2 ⟨subd8_2_286, List.forall_mem_cons.2 ⟨subd8_2_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_288 : subd8_2 [0, 0, 9] = true := by decide +kernel
theorem subd8_2_289 : subd8_2 [0, 0, 10] = true := by decide +kernel
theorem subd8_2_290 : subd8_2 [0, 0, 11] = true := by decide +kernel
theorem subd8_2_291 : subd8_2 [0, 0, 12] = true := by decide +kernel
theorem subd8_2_292 : subd8_2 [0, 0, 13] = true := by decide +kernel
theorem subd8_2_293 : subd8_2 [0, 0, 14] = true := by decide +kernel
theorem subd8_2_294 : subd8_2 [0, 0, 15] = true := by decide +kernel
theorem subd8_2_295 : subd8_2 [0, 0, 16] = true := by decide +kernel
theorem subd8_2_296 : subd8_2 [0, 0, 17] = true := by decide +kernel
theorem subd8_2_297 : subd8_2 [0, 0, 18] = true := by decide +kernel
theorem subd8_2_298 : subd8_2 [0, 0, 19] = true := by decide +kernel
theorem subd8_2_299 : subd8_2 [0, 0, 20] = true := by decide +kernel
theorem subd8_2_300 : subd8_2 [0, 0, 21] = true := by decide +kernel
theorem subd8_2_301 : subd8_2 [0, 1, -20] = true := by decide +kernel
theorem subd8_2_302 : subd8_2 [0, 1, -19] = true := by decide +kernel
theorem subd8_2_303 : subd8_2 [0, 1, -18] = true := by decide +kernel
theorem subd8_2_304 : subd8_2 [0, 1, -17] = true := by decide +kernel
theorem subd8_2_305 : subd8_2 [0, 1, -16] = true := by decide +kernel
theorem subd8_2_306 : subd8_2 [0, 1, -15] = true := by decide +kernel
theorem subd8_2_307 : subd8_2 [0, 1, -14] = true := by decide +kernel
theorem subd8_2_308 : subd8_2 [0, 1, -13] = true := by decide +kernel
theorem subd8_2_309 : subd8_2 [0, 1, -12] = true := by decide +kernel
theorem subd8_2_310 : subd8_2 [0, 1, -11] = true := by decide +kernel
theorem subd8_2_311 : subd8_2 [0, 1, -10] = true := by decide +kernel
theorem subd8_2_312 : subd8_2 [0, 1, -9] = true := by decide +kernel
theorem subd8_2_313 : subd8_2 [0, 1, -8] = true := by decide +kernel
theorem subd8_2_314 : subd8_2 [0, 1, -7] = true := by decide +kernel
theorem subd8_2_315 : subd8_2 [0, 1, -6] = true := by decide +kernel
theorem subd8_2_316 : subd8_2 [0, 1, -5] = true := by decide +kernel
theorem subd8_2_317 : subd8_2 [0, 1, -4] = true := by decide +kernel
theorem subd8_2_318 : subd8_2 [0, 1, -3] = true := by decide +kernel
theorem subd8_2_319 : subd8_2 [0, 1, -2] = true := by decide +kernel
theorem sbd8_2_9 : ∀ q ∈ blkd8_2_9, subd8_2 q = true := by
  unfold blkd8_2_9
  exact List.forall_mem_cons.2 ⟨subd8_2_288, List.forall_mem_cons.2 ⟨subd8_2_289, List.forall_mem_cons.2 ⟨subd8_2_290, List.forall_mem_cons.2 ⟨subd8_2_291, List.forall_mem_cons.2 ⟨subd8_2_292, List.forall_mem_cons.2 ⟨subd8_2_293, List.forall_mem_cons.2 ⟨subd8_2_294, List.forall_mem_cons.2 ⟨subd8_2_295, List.forall_mem_cons.2 ⟨subd8_2_296, List.forall_mem_cons.2 ⟨subd8_2_297, List.forall_mem_cons.2 ⟨subd8_2_298, List.forall_mem_cons.2 ⟨subd8_2_299, List.forall_mem_cons.2 ⟨subd8_2_300, List.forall_mem_cons.2 ⟨subd8_2_301, List.forall_mem_cons.2 ⟨subd8_2_302, List.forall_mem_cons.2 ⟨subd8_2_303, List.forall_mem_cons.2 ⟨subd8_2_304, List.forall_mem_cons.2 ⟨subd8_2_305, List.forall_mem_cons.2 ⟨subd8_2_306, List.forall_mem_cons.2 ⟨subd8_2_307, List.forall_mem_cons.2 ⟨subd8_2_308, List.forall_mem_cons.2 ⟨subd8_2_309, List.forall_mem_cons.2 ⟨subd8_2_310, List.forall_mem_cons.2 ⟨subd8_2_311, List.forall_mem_cons.2 ⟨subd8_2_312, List.forall_mem_cons.2 ⟨subd8_2_313, List.forall_mem_cons.2 ⟨subd8_2_314, List.forall_mem_cons.2 ⟨subd8_2_315, List.forall_mem_cons.2 ⟨subd8_2_316, List.forall_mem_cons.2 ⟨subd8_2_317, List.forall_mem_cons.2 ⟨subd8_2_318, List.forall_mem_cons.2 ⟨subd8_2_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_320 : subd8_2 [0, 1, -1] = true := by decide +kernel
theorem subd8_2_321 : subd8_2 [0, 1, 0] = true := by decide +kernel
theorem subd8_2_322 : subd8_2 [0, 1, 1] = true := by decide +kernel
theorem subd8_2_323 : subd8_2 [0, 1, 2] = true := by decide +kernel
theorem subd8_2_324 : subd8_2 [0, 1, 3] = true := by decide +kernel
theorem subd8_2_325 : subd8_2 [0, 1, 4] = true := by decide +kernel
theorem subd8_2_326 : subd8_2 [0, 1, 5] = true := by decide +kernel
theorem subd8_2_327 : subd8_2 [0, 1, 6] = true := by decide +kernel
theorem subd8_2_328 : subd8_2 [0, 1, 7] = true := by decide +kernel
theorem subd8_2_329 : subd8_2 [0, 1, 8] = true := by decide +kernel
theorem subd8_2_330 : subd8_2 [0, 1, 9] = true := by decide +kernel
theorem subd8_2_331 : subd8_2 [0, 1, 10] = true := by decide +kernel
theorem subd8_2_332 : subd8_2 [0, 1, 11] = true := by decide +kernel
theorem subd8_2_333 : subd8_2 [0, 1, 12] = true := by decide +kernel
theorem subd8_2_334 : subd8_2 [0, 1, 13] = true := by decide +kernel
theorem subd8_2_335 : subd8_2 [0, 1, 14] = true := by decide +kernel
theorem subd8_2_336 : subd8_2 [0, 1, 15] = true := by decide +kernel
theorem subd8_2_337 : subd8_2 [0, 1, 16] = true := by decide +kernel
theorem subd8_2_338 : subd8_2 [0, 1, 17] = true := by decide +kernel
theorem subd8_2_339 : subd8_2 [0, 1, 18] = true := by decide +kernel
theorem subd8_2_340 : subd8_2 [0, 1, 19] = true := by decide +kernel
theorem subd8_2_341 : subd8_2 [0, 1, 20] = true := by decide +kernel
theorem subd8_2_342 : subd8_2 [0, 2, -13] = true := by decide +kernel
theorem subd8_2_343 : subd8_2 [0, 2, -12] = true := by decide +kernel
theorem subd8_2_344 : subd8_2 [0, 2, -11] = true := by decide +kernel
theorem subd8_2_345 : subd8_2 [0, 2, -10] = true := by decide +kernel
theorem subd8_2_346 : subd8_2 [0, 2, -9] = true := by decide +kernel
theorem subd8_2_347 : subd8_2 [0, 2, -8] = true := by decide +kernel
theorem subd8_2_348 : subd8_2 [0, 2, -7] = true := by decide +kernel
theorem subd8_2_349 : subd8_2 [0, 2, -6] = true := by decide +kernel
theorem subd8_2_350 : subd8_2 [0, 2, -5] = true := by decide +kernel
theorem subd8_2_351 : subd8_2 [0, 2, -4] = true := by decide +kernel
theorem sbd8_2_10 : ∀ q ∈ blkd8_2_10, subd8_2 q = true := by
  unfold blkd8_2_10
  exact List.forall_mem_cons.2 ⟨subd8_2_320, List.forall_mem_cons.2 ⟨subd8_2_321, List.forall_mem_cons.2 ⟨subd8_2_322, List.forall_mem_cons.2 ⟨subd8_2_323, List.forall_mem_cons.2 ⟨subd8_2_324, List.forall_mem_cons.2 ⟨subd8_2_325, List.forall_mem_cons.2 ⟨subd8_2_326, List.forall_mem_cons.2 ⟨subd8_2_327, List.forall_mem_cons.2 ⟨subd8_2_328, List.forall_mem_cons.2 ⟨subd8_2_329, List.forall_mem_cons.2 ⟨subd8_2_330, List.forall_mem_cons.2 ⟨subd8_2_331, List.forall_mem_cons.2 ⟨subd8_2_332, List.forall_mem_cons.2 ⟨subd8_2_333, List.forall_mem_cons.2 ⟨subd8_2_334, List.forall_mem_cons.2 ⟨subd8_2_335, List.forall_mem_cons.2 ⟨subd8_2_336, List.forall_mem_cons.2 ⟨subd8_2_337, List.forall_mem_cons.2 ⟨subd8_2_338, List.forall_mem_cons.2 ⟨subd8_2_339, List.forall_mem_cons.2 ⟨subd8_2_340, List.forall_mem_cons.2 ⟨subd8_2_341, List.forall_mem_cons.2 ⟨subd8_2_342, List.forall_mem_cons.2 ⟨subd8_2_343, List.forall_mem_cons.2 ⟨subd8_2_344, List.forall_mem_cons.2 ⟨subd8_2_345, List.forall_mem_cons.2 ⟨subd8_2_346, List.forall_mem_cons.2 ⟨subd8_2_347, List.forall_mem_cons.2 ⟨subd8_2_348, List.forall_mem_cons.2 ⟨subd8_2_349, List.forall_mem_cons.2 ⟨subd8_2_350, List.forall_mem_cons.2 ⟨subd8_2_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_352 : subd8_2 [0, 2, -3] = true := by decide +kernel
theorem subd8_2_353 : subd8_2 [0, 2, -2] = true := by decide +kernel
theorem subd8_2_354 : subd8_2 [0, 2, -1] = true := by decide +kernel
theorem subd8_2_355 : subd8_2 [0, 2, 0] = true := by decide +kernel
theorem subd8_2_356 : subd8_2 [0, 2, 1] = true := by decide +kernel
theorem subd8_2_357 : subd8_2 [0, 2, 2] = true := by decide +kernel
theorem subd8_2_358 : subd8_2 [0, 2, 3] = true := by decide +kernel
theorem subd8_2_359 : subd8_2 [0, 2, 4] = true := by decide +kernel
theorem subd8_2_360 : subd8_2 [0, 2, 5] = true := by decide +kernel
theorem subd8_2_361 : subd8_2 [0, 2, 6] = true := by decide +kernel
theorem subd8_2_362 : subd8_2 [0, 2, 7] = true := by decide +kernel
theorem subd8_2_363 : subd8_2 [0, 2, 8] = true := by decide +kernel
theorem subd8_2_364 : subd8_2 [0, 2, 9] = true := by decide +kernel
theorem subd8_2_365 : subd8_2 [0, 2, 10] = true := by decide +kernel
theorem subd8_2_366 : subd8_2 [0, 2, 11] = true := by decide +kernel
theorem subd8_2_367 : subd8_2 [0, 2, 12] = true := by decide +kernel
theorem subd8_2_368 : subd8_2 [0, 2, 13] = true := by decide +kernel
theorem subd8_2_369 : subd8_2 [0, 2, 14] = true := by decide +kernel
theorem subd8_2_370 : subd8_2 [1, -3] = true := by decide +kernel
theorem subd8_2_371 : subd8_2 [1, -2] = true := by decide +kernel
theorem subd8_2_372 : subd8_2 [1, -1, -18] = true := by decide +kernel
theorem subd8_2_373 : subd8_2 [1, -1, -17] = true := by decide +kernel
theorem subd8_2_374 : subd8_2 [1, -1, -16] = true := by decide +kernel
theorem subd8_2_375 : subd8_2 [1, -1, -15] = true := by decide +kernel
theorem subd8_2_376 : subd8_2 [1, -1, -14] = true := by decide +kernel
theorem subd8_2_377 : subd8_2 [1, -1, -13] = true := by decide +kernel
theorem subd8_2_378 : subd8_2 [1, -1, -12] = true := by decide +kernel
theorem subd8_2_379 : subd8_2 [1, -1, -11] = true := by decide +kernel
theorem subd8_2_380 : subd8_2 [1, -1, -10] = true := by decide +kernel
theorem subd8_2_381 : subd8_2 [1, -1, -9] = true := by decide +kernel
theorem subd8_2_382 : subd8_2 [1, -1, -8] = true := by decide +kernel
theorem subd8_2_383 : subd8_2 [1, -1, -7] = true := by decide +kernel
theorem sbd8_2_11 : ∀ q ∈ blkd8_2_11, subd8_2 q = true := by
  unfold blkd8_2_11
  exact List.forall_mem_cons.2 ⟨subd8_2_352, List.forall_mem_cons.2 ⟨subd8_2_353, List.forall_mem_cons.2 ⟨subd8_2_354, List.forall_mem_cons.2 ⟨subd8_2_355, List.forall_mem_cons.2 ⟨subd8_2_356, List.forall_mem_cons.2 ⟨subd8_2_357, List.forall_mem_cons.2 ⟨subd8_2_358, List.forall_mem_cons.2 ⟨subd8_2_359, List.forall_mem_cons.2 ⟨subd8_2_360, List.forall_mem_cons.2 ⟨subd8_2_361, List.forall_mem_cons.2 ⟨subd8_2_362, List.forall_mem_cons.2 ⟨subd8_2_363, List.forall_mem_cons.2 ⟨subd8_2_364, List.forall_mem_cons.2 ⟨subd8_2_365, List.forall_mem_cons.2 ⟨subd8_2_366, List.forall_mem_cons.2 ⟨subd8_2_367, List.forall_mem_cons.2 ⟨subd8_2_368, List.forall_mem_cons.2 ⟨subd8_2_369, List.forall_mem_cons.2 ⟨subd8_2_370, List.forall_mem_cons.2 ⟨subd8_2_371, List.forall_mem_cons.2 ⟨subd8_2_372, List.forall_mem_cons.2 ⟨subd8_2_373, List.forall_mem_cons.2 ⟨subd8_2_374, List.forall_mem_cons.2 ⟨subd8_2_375, List.forall_mem_cons.2 ⟨subd8_2_376, List.forall_mem_cons.2 ⟨subd8_2_377, List.forall_mem_cons.2 ⟨subd8_2_378, List.forall_mem_cons.2 ⟨subd8_2_379, List.forall_mem_cons.2 ⟨subd8_2_380, List.forall_mem_cons.2 ⟨subd8_2_381, List.forall_mem_cons.2 ⟨subd8_2_382, List.forall_mem_cons.2 ⟨subd8_2_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_384 : subd8_2 [1, -1, -6] = true := by decide +kernel
theorem subd8_2_385 : subd8_2 [1, -1, -5] = true := by decide +kernel
theorem subd8_2_386 : subd8_2 [1, -1, -4] = true := by decide +kernel
theorem subd8_2_387 : subd8_2 [1, -1, -3] = true := by decide +kernel
theorem subd8_2_388 : subd8_2 [1, -1, -2] = true := by decide +kernel
theorem subd8_2_389 : subd8_2 [1, -1, -1] = true := by decide +kernel
theorem subd8_2_390 : subd8_2 [1, -1, 0] = true := by decide +kernel
theorem subd8_2_391 : subd8_2 [1, -1, 1] = true := by decide +kernel
theorem subd8_2_392 : subd8_2 [1, -1, 2] = true := by decide +kernel
theorem subd8_2_393 : subd8_2 [1, -1, 3] = true := by decide +kernel
theorem subd8_2_394 : subd8_2 [1, -1, 4] = true := by decide +kernel
theorem subd8_2_395 : subd8_2 [1, -1, 5] = true := by decide +kernel
theorem subd8_2_396 : subd8_2 [1, -1, 6] = true := by decide +kernel
theorem subd8_2_397 : subd8_2 [1, -1, 7] = true := by decide +kernel
theorem subd8_2_398 : subd8_2 [1, -1, 8] = true := by decide +kernel
theorem subd8_2_399 : subd8_2 [1, -1, 9] = true := by decide +kernel
theorem subd8_2_400 : subd8_2 [1, -1, 10] = true := by decide +kernel
theorem subd8_2_401 : subd8_2 [1, -1, 11] = true := by decide +kernel
theorem subd8_2_402 : subd8_2 [1, -1, 12] = true := by decide +kernel
theorem subd8_2_403 : subd8_2 [1, -1, 13] = true := by decide +kernel
theorem subd8_2_404 : subd8_2 [1, -1, 14] = true := by decide +kernel
theorem subd8_2_405 : subd8_2 [1, -1, 15] = true := by decide +kernel
theorem subd8_2_406 : subd8_2 [1, -1, 16] = true := by decide +kernel
theorem subd8_2_407 : subd8_2 [1, 0, -20] = true := by decide +kernel
theorem subd8_2_408 : subd8_2 [1, 0, -19] = true := by decide +kernel
theorem subd8_2_409 : subd8_2 [1, 0, -18] = true := by decide +kernel
theorem subd8_2_410 : subd8_2 [1, 0, -17] = true := by decide +kernel
theorem subd8_2_411 : subd8_2 [1, 0, -16] = true := by decide +kernel
theorem subd8_2_412 : subd8_2 [1, 0, -15] = true := by decide +kernel
theorem subd8_2_413 : subd8_2 [1, 0, -14] = true := by decide +kernel
theorem subd8_2_414 : subd8_2 [1, 0, -13] = true := by decide +kernel
theorem subd8_2_415 : subd8_2 [1, 0, -12] = true := by decide +kernel
theorem sbd8_2_12 : ∀ q ∈ blkd8_2_12, subd8_2 q = true := by
  unfold blkd8_2_12
  exact List.forall_mem_cons.2 ⟨subd8_2_384, List.forall_mem_cons.2 ⟨subd8_2_385, List.forall_mem_cons.2 ⟨subd8_2_386, List.forall_mem_cons.2 ⟨subd8_2_387, List.forall_mem_cons.2 ⟨subd8_2_388, List.forall_mem_cons.2 ⟨subd8_2_389, List.forall_mem_cons.2 ⟨subd8_2_390, List.forall_mem_cons.2 ⟨subd8_2_391, List.forall_mem_cons.2 ⟨subd8_2_392, List.forall_mem_cons.2 ⟨subd8_2_393, List.forall_mem_cons.2 ⟨subd8_2_394, List.forall_mem_cons.2 ⟨subd8_2_395, List.forall_mem_cons.2 ⟨subd8_2_396, List.forall_mem_cons.2 ⟨subd8_2_397, List.forall_mem_cons.2 ⟨subd8_2_398, List.forall_mem_cons.2 ⟨subd8_2_399, List.forall_mem_cons.2 ⟨subd8_2_400, List.forall_mem_cons.2 ⟨subd8_2_401, List.forall_mem_cons.2 ⟨subd8_2_402, List.forall_mem_cons.2 ⟨subd8_2_403, List.forall_mem_cons.2 ⟨subd8_2_404, List.forall_mem_cons.2 ⟨subd8_2_405, List.forall_mem_cons.2 ⟨subd8_2_406, List.forall_mem_cons.2 ⟨subd8_2_407, List.forall_mem_cons.2 ⟨subd8_2_408, List.forall_mem_cons.2 ⟨subd8_2_409, List.forall_mem_cons.2 ⟨subd8_2_410, List.forall_mem_cons.2 ⟨subd8_2_411, List.forall_mem_cons.2 ⟨subd8_2_412, List.forall_mem_cons.2 ⟨subd8_2_413, List.forall_mem_cons.2 ⟨subd8_2_414, List.forall_mem_cons.2 ⟨subd8_2_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_416 : subd8_2 [1, 0, -11] = true := by decide +kernel
theorem subd8_2_417 : subd8_2 [1, 0, -10] = true := by decide +kernel
theorem subd8_2_418 : subd8_2 [1, 0, -9] = true := by decide +kernel
theorem subd8_2_419 : subd8_2 [1, 0, -8] = true := by decide +kernel
theorem subd8_2_420 : subd8_2 [1, 0, -7] = true := by decide +kernel
theorem subd8_2_421 : subd8_2 [1, 0, -6] = true := by decide +kernel
theorem subd8_2_422 : subd8_2 [1, 0, -5] = true := by decide +kernel
theorem subd8_2_423 : subd8_2 [1, 0, -4] = true := by decide +kernel
theorem subd8_2_424 : subd8_2 [1, 0, -3] = true := by decide +kernel
theorem subd8_2_425 : subd8_2 [1, 0, -2] = true := by decide +kernel
theorem subd8_2_426 : subd8_2 [1, 0, -1] = true := by decide +kernel
theorem subd8_2_427 : subd8_2 [1, 0, 0] = true := by decide +kernel
theorem subd8_2_428 : subd8_2 [1, 0, 1] = true := by decide +kernel
theorem subd8_2_429 : subd8_2 [1, 0, 2] = true := by decide +kernel
theorem subd8_2_430 : subd8_2 [1, 0, 3] = true := by decide +kernel
theorem subd8_2_431 : subd8_2 [1, 0, 4] = true := by decide +kernel
theorem subd8_2_432 : subd8_2 [1, 0, 5] = true := by decide +kernel
theorem subd8_2_433 : subd8_2 [1, 0, 6] = true := by decide +kernel
theorem subd8_2_434 : subd8_2 [1, 0, 7] = true := by decide +kernel
theorem subd8_2_435 : subd8_2 [1, 0, 8] = true := by decide +kernel
theorem subd8_2_436 : subd8_2 [1, 0, 9] = true := by decide +kernel
theorem subd8_2_437 : subd8_2 [1, 0, 10] = true := by decide +kernel
theorem subd8_2_438 : subd8_2 [1, 0, 11] = true := by decide +kernel
theorem subd8_2_439 : subd8_2 [1, 0, 12] = true := by decide +kernel
theorem subd8_2_440 : subd8_2 [1, 0, 13] = true := by decide +kernel
theorem subd8_2_441 : subd8_2 [1, 0, 14] = true := by decide +kernel
theorem subd8_2_442 : subd8_2 [1, 0, 15] = true := by decide +kernel
theorem subd8_2_443 : subd8_2 [1, 0, 16] = true := by decide +kernel
theorem subd8_2_444 : subd8_2 [1, 0, 17] = true := by decide +kernel
theorem subd8_2_445 : subd8_2 [1, 0, 18] = true := by decide +kernel
theorem subd8_2_446 : subd8_2 [1, 0, 19] = true := by decide +kernel
theorem subd8_2_447 : subd8_2 [1, 1, -18] = true := by decide +kernel
theorem sbd8_2_13 : ∀ q ∈ blkd8_2_13, subd8_2 q = true := by
  unfold blkd8_2_13
  exact List.forall_mem_cons.2 ⟨subd8_2_416, List.forall_mem_cons.2 ⟨subd8_2_417, List.forall_mem_cons.2 ⟨subd8_2_418, List.forall_mem_cons.2 ⟨subd8_2_419, List.forall_mem_cons.2 ⟨subd8_2_420, List.forall_mem_cons.2 ⟨subd8_2_421, List.forall_mem_cons.2 ⟨subd8_2_422, List.forall_mem_cons.2 ⟨subd8_2_423, List.forall_mem_cons.2 ⟨subd8_2_424, List.forall_mem_cons.2 ⟨subd8_2_425, List.forall_mem_cons.2 ⟨subd8_2_426, List.forall_mem_cons.2 ⟨subd8_2_427, List.forall_mem_cons.2 ⟨subd8_2_428, List.forall_mem_cons.2 ⟨subd8_2_429, List.forall_mem_cons.2 ⟨subd8_2_430, List.forall_mem_cons.2 ⟨subd8_2_431, List.forall_mem_cons.2 ⟨subd8_2_432, List.forall_mem_cons.2 ⟨subd8_2_433, List.forall_mem_cons.2 ⟨subd8_2_434, List.forall_mem_cons.2 ⟨subd8_2_435, List.forall_mem_cons.2 ⟨subd8_2_436, List.forall_mem_cons.2 ⟨subd8_2_437, List.forall_mem_cons.2 ⟨subd8_2_438, List.forall_mem_cons.2 ⟨subd8_2_439, List.forall_mem_cons.2 ⟨subd8_2_440, List.forall_mem_cons.2 ⟨subd8_2_441, List.forall_mem_cons.2 ⟨subd8_2_442, List.forall_mem_cons.2 ⟨subd8_2_443, List.forall_mem_cons.2 ⟨subd8_2_444, List.forall_mem_cons.2 ⟨subd8_2_445, List.forall_mem_cons.2 ⟨subd8_2_446, List.forall_mem_cons.2 ⟨subd8_2_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_448 : subd8_2 [1, 1, -17] = true := by decide +kernel
theorem subd8_2_449 : subd8_2 [1, 1, -16] = true := by decide +kernel
theorem subd8_2_450 : subd8_2 [1, 1, -15] = true := by decide +kernel
theorem subd8_2_451 : subd8_2 [1, 1, -14] = true := by decide +kernel
theorem subd8_2_452 : subd8_2 [1, 1, -13] = true := by decide +kernel
theorem subd8_2_453 : subd8_2 [1, 1, -12] = true := by decide +kernel
theorem subd8_2_454 : subd8_2 [1, 1, -11] = true := by decide +kernel
theorem subd8_2_455 : subd8_2 [1, 1, -10] = true := by decide +kernel
theorem subd8_2_456 : subd8_2 [1, 1, -9] = true := by decide +kernel
theorem subd8_2_457 : subd8_2 [1, 1, -8] = true := by decide +kernel
theorem subd8_2_458 : subd8_2 [1, 1, -7] = true := by decide +kernel
theorem subd8_2_459 : subd8_2 [1, 1, -6] = true := by decide +kernel
theorem subd8_2_460 : subd8_2 [1, 1, -5] = true := by decide +kernel
theorem subd8_2_461 : subd8_2 [1, 1, -4] = true := by decide +kernel
theorem subd8_2_462 : subd8_2 [1, 1, -3] = true := by decide +kernel
theorem subd8_2_463 : subd8_2 [1, 1, -2] = true := by decide +kernel
theorem subd8_2_464 : subd8_2 [1, 1, -1] = true := by decide +kernel
theorem subd8_2_465 : subd8_2 [1, 1, 0] = true := by decide +kernel
theorem subd8_2_466 : subd8_2 [1, 1, 1] = true := by decide +kernel
theorem subd8_2_467 : subd8_2 [1, 1, 2] = true := by decide +kernel
theorem subd8_2_468 : subd8_2 [1, 1, 3] = true := by decide +kernel
theorem subd8_2_469 : subd8_2 [1, 1, 4] = true := by decide +kernel
theorem subd8_2_470 : subd8_2 [1, 1, 5] = true := by decide +kernel
theorem subd8_2_471 : subd8_2 [1, 1, 6] = true := by decide +kernel
theorem subd8_2_472 : subd8_2 [1, 1, 7] = true := by decide +kernel
theorem subd8_2_473 : subd8_2 [1, 1, 8] = true := by decide +kernel
theorem subd8_2_474 : subd8_2 [1, 1, 9] = true := by decide +kernel
theorem subd8_2_475 : subd8_2 [1, 1, 10] = true := by decide +kernel
theorem subd8_2_476 : subd8_2 [1, 1, 11] = true := by decide +kernel
theorem subd8_2_477 : subd8_2 [1, 1, 12] = true := by decide +kernel
theorem subd8_2_478 : subd8_2 [1, 1, 13] = true := by decide +kernel
theorem subd8_2_479 : subd8_2 [1, 1, 14] = true := by decide +kernel
theorem sbd8_2_14 : ∀ q ∈ blkd8_2_14, subd8_2 q = true := by
  unfold blkd8_2_14
  exact List.forall_mem_cons.2 ⟨subd8_2_448, List.forall_mem_cons.2 ⟨subd8_2_449, List.forall_mem_cons.2 ⟨subd8_2_450, List.forall_mem_cons.2 ⟨subd8_2_451, List.forall_mem_cons.2 ⟨subd8_2_452, List.forall_mem_cons.2 ⟨subd8_2_453, List.forall_mem_cons.2 ⟨subd8_2_454, List.forall_mem_cons.2 ⟨subd8_2_455, List.forall_mem_cons.2 ⟨subd8_2_456, List.forall_mem_cons.2 ⟨subd8_2_457, List.forall_mem_cons.2 ⟨subd8_2_458, List.forall_mem_cons.2 ⟨subd8_2_459, List.forall_mem_cons.2 ⟨subd8_2_460, List.forall_mem_cons.2 ⟨subd8_2_461, List.forall_mem_cons.2 ⟨subd8_2_462, List.forall_mem_cons.2 ⟨subd8_2_463, List.forall_mem_cons.2 ⟨subd8_2_464, List.forall_mem_cons.2 ⟨subd8_2_465, List.forall_mem_cons.2 ⟨subd8_2_466, List.forall_mem_cons.2 ⟨subd8_2_467, List.forall_mem_cons.2 ⟨subd8_2_468, List.forall_mem_cons.2 ⟨subd8_2_469, List.forall_mem_cons.2 ⟨subd8_2_470, List.forall_mem_cons.2 ⟨subd8_2_471, List.forall_mem_cons.2 ⟨subd8_2_472, List.forall_mem_cons.2 ⟨subd8_2_473, List.forall_mem_cons.2 ⟨subd8_2_474, List.forall_mem_cons.2 ⟨subd8_2_475, List.forall_mem_cons.2 ⟨subd8_2_476, List.forall_mem_cons.2 ⟨subd8_2_477, List.forall_mem_cons.2 ⟨subd8_2_478, List.forall_mem_cons.2 ⟨subd8_2_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_480 : subd8_2 [1, 1, 15] = true := by decide +kernel
theorem subd8_2_481 : subd8_2 [1, 1, 16] = true := by decide +kernel
theorem subd8_2_482 : subd8_2 [1, 1, 17] = true := by decide +kernel
theorem subd8_2_483 : subd8_2 [1, 1, 18] = true := by decide +kernel
theorem subd8_2_484 : subd8_2 [1, 2, -12] = true := by decide +kernel
theorem subd8_2_485 : subd8_2 [1, 2, -11] = true := by decide +kernel
theorem subd8_2_486 : subd8_2 [1, 2, -10] = true := by decide +kernel
theorem subd8_2_487 : subd8_2 [1, 2, -9] = true := by decide +kernel
theorem subd8_2_488 : subd8_2 [1, 2, -8] = true := by decide +kernel
theorem subd8_2_489 : subd8_2 [1, 2, -7] = true := by decide +kernel
theorem subd8_2_490 : subd8_2 [1, 2, -6] = true := by decide +kernel
theorem subd8_2_491 : subd8_2 [1, 2, -5] = true := by decide +kernel
theorem subd8_2_492 : subd8_2 [1, 2, -4] = true := by decide +kernel
theorem subd8_2_493 : subd8_2 [1, 2, -3] = true := by decide +kernel
theorem subd8_2_494 : subd8_2 [1, 2, -2] = true := by decide +kernel
theorem subd8_2_495 : subd8_2 [1, 2, -1] = true := by decide +kernel
theorem subd8_2_496 : subd8_2 [1, 2, 0] = true := by decide +kernel
theorem subd8_2_497 : subd8_2 [1, 2, 1] = true := by decide +kernel
theorem subd8_2_498 : subd8_2 [1, 2, 2] = true := by decide +kernel
theorem subd8_2_499 : subd8_2 [1, 2, 3] = true := by decide +kernel
theorem subd8_2_500 : subd8_2 [1, 2, 4] = true := by decide +kernel
theorem subd8_2_501 : subd8_2 [1, 2, 5] = true := by decide +kernel
theorem subd8_2_502 : subd8_2 [1, 2, 6] = true := by decide +kernel
theorem subd8_2_503 : subd8_2 [1, 2, 7] = true := by decide +kernel
theorem subd8_2_504 : subd8_2 [1, 2, 8] = true := by decide +kernel
theorem subd8_2_505 : subd8_2 [1, 2, 9] = true := by decide +kernel
theorem subd8_2_506 : subd8_2 [1, 2, 10] = true := by decide +kernel
theorem subd8_2_507 : subd8_2 [1, 2, 11] = true := by decide +kernel
theorem subd8_2_508 : subd8_2 [1, 2, 12] = true := by decide +kernel
theorem subd8_2_509 : subd8_2 [2, -2] = true := by decide +kernel
theorem subd8_2_510 : subd8_2 [2, -1] = true := by decide +kernel
theorem subd8_2_511 : subd8_2 [2, 0, -12] = true := by decide +kernel
theorem sbd8_2_15 : ∀ q ∈ blkd8_2_15, subd8_2 q = true := by
  unfold blkd8_2_15
  exact List.forall_mem_cons.2 ⟨subd8_2_480, List.forall_mem_cons.2 ⟨subd8_2_481, List.forall_mem_cons.2 ⟨subd8_2_482, List.forall_mem_cons.2 ⟨subd8_2_483, List.forall_mem_cons.2 ⟨subd8_2_484, List.forall_mem_cons.2 ⟨subd8_2_485, List.forall_mem_cons.2 ⟨subd8_2_486, List.forall_mem_cons.2 ⟨subd8_2_487, List.forall_mem_cons.2 ⟨subd8_2_488, List.forall_mem_cons.2 ⟨subd8_2_489, List.forall_mem_cons.2 ⟨subd8_2_490, List.forall_mem_cons.2 ⟨subd8_2_491, List.forall_mem_cons.2 ⟨subd8_2_492, List.forall_mem_cons.2 ⟨subd8_2_493, List.forall_mem_cons.2 ⟨subd8_2_494, List.forall_mem_cons.2 ⟨subd8_2_495, List.forall_mem_cons.2 ⟨subd8_2_496, List.forall_mem_cons.2 ⟨subd8_2_497, List.forall_mem_cons.2 ⟨subd8_2_498, List.forall_mem_cons.2 ⟨subd8_2_499, List.forall_mem_cons.2 ⟨subd8_2_500, List.forall_mem_cons.2 ⟨subd8_2_501, List.forall_mem_cons.2 ⟨subd8_2_502, List.forall_mem_cons.2 ⟨subd8_2_503, List.forall_mem_cons.2 ⟨subd8_2_504, List.forall_mem_cons.2 ⟨subd8_2_505, List.forall_mem_cons.2 ⟨subd8_2_506, List.forall_mem_cons.2 ⟨subd8_2_507, List.forall_mem_cons.2 ⟨subd8_2_508, List.forall_mem_cons.2 ⟨subd8_2_509, List.forall_mem_cons.2 ⟨subd8_2_510, List.forall_mem_cons.2 ⟨subd8_2_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C135
