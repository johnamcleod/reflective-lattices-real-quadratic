import ReflectZphi.Data.Cert5.C131.Base

namespace ReflectZphi.Data.Cert5.C131

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_0_224 : subd8_0 [0, 1, -9] = true := by decide +kernel
theorem subd8_0_225 : subd8_0 [0, 1, -8] = true := by decide +kernel
theorem subd8_0_226 : subd8_0 [0, 1, -7] = true := by decide +kernel
theorem subd8_0_227 : subd8_0 [0, 1, -6] = true := by decide +kernel
theorem subd8_0_228 : subd8_0 [0, 1, -5] = true := by decide +kernel
theorem subd8_0_229 : subd8_0 [0, 1, -4] = true := by decide +kernel
theorem subd8_0_230 : subd8_0 [0, 1, -3] = true := by decide +kernel
theorem subd8_0_231 : subd8_0 [0, 1, -2] = true := by decide +kernel
theorem subd8_0_232 : subd8_0 [0, 1, -1] = true := by decide +kernel
theorem subd8_0_233 : subd8_0 [0, 1, 0] = true := by decide +kernel
theorem subd8_0_234 : subd8_0 [0, 1, 1] = true := by decide +kernel
theorem subd8_0_235 : subd8_0 [0, 1, 2] = true := by decide +kernel
theorem subd8_0_236 : subd8_0 [0, 1, 3] = true := by decide +kernel
theorem subd8_0_237 : subd8_0 [0, 1, 4] = true := by decide +kernel
theorem subd8_0_238 : subd8_0 [0, 1, 5] = true := by decide +kernel
theorem subd8_0_239 : subd8_0 [0, 1, 6] = true := by decide +kernel
theorem subd8_0_240 : subd8_0 [0, 1, 7] = true := by decide +kernel
theorem subd8_0_241 : subd8_0 [0, 1, 8] = true := by decide +kernel
theorem subd8_0_242 : subd8_0 [0, 1, 9] = true := by decide +kernel
theorem subd8_0_243 : subd8_0 [0, 2, -9] = true := by decide +kernel
theorem subd8_0_244 : subd8_0 [0, 2, -8] = true := by decide +kernel
theorem subd8_0_245 : subd8_0 [0, 2, -7] = true := by decide +kernel
theorem subd8_0_246 : subd8_0 [0, 2, -6] = true := by decide +kernel
theorem subd8_0_247 : subd8_0 [0, 2, -5] = true := by decide +kernel
theorem subd8_0_248 : subd8_0 [0, 2, -4] = true := by decide +kernel
theorem subd8_0_249 : subd8_0 [0, 2, -3] = true := by decide +kernel
theorem subd8_0_250 : subd8_0 [0, 2, -2] = true := by decide +kernel
theorem subd8_0_251 : subd8_0 [0, 2, -1] = true := by decide +kernel
theorem subd8_0_252 : subd8_0 [0, 2, 0] = true := by decide +kernel
theorem subd8_0_253 : subd8_0 [0, 2, 1] = true := by decide +kernel
theorem subd8_0_254 : subd8_0 [0, 2, 2] = true := by decide +kernel
theorem subd8_0_255 : subd8_0 [0, 2, 3] = true := by decide +kernel
theorem sbd8_0_7 : ∀ q ∈ blkd8_0_7, subd8_0 q = true := by
  unfold blkd8_0_7
  exact List.forall_mem_cons.2 ⟨subd8_0_224, List.forall_mem_cons.2 ⟨subd8_0_225, List.forall_mem_cons.2 ⟨subd8_0_226, List.forall_mem_cons.2 ⟨subd8_0_227, List.forall_mem_cons.2 ⟨subd8_0_228, List.forall_mem_cons.2 ⟨subd8_0_229, List.forall_mem_cons.2 ⟨subd8_0_230, List.forall_mem_cons.2 ⟨subd8_0_231, List.forall_mem_cons.2 ⟨subd8_0_232, List.forall_mem_cons.2 ⟨subd8_0_233, List.forall_mem_cons.2 ⟨subd8_0_234, List.forall_mem_cons.2 ⟨subd8_0_235, List.forall_mem_cons.2 ⟨subd8_0_236, List.forall_mem_cons.2 ⟨subd8_0_237, List.forall_mem_cons.2 ⟨subd8_0_238, List.forall_mem_cons.2 ⟨subd8_0_239, List.forall_mem_cons.2 ⟨subd8_0_240, List.forall_mem_cons.2 ⟨subd8_0_241, List.forall_mem_cons.2 ⟨subd8_0_242, List.forall_mem_cons.2 ⟨subd8_0_243, List.forall_mem_cons.2 ⟨subd8_0_244, List.forall_mem_cons.2 ⟨subd8_0_245, List.forall_mem_cons.2 ⟨subd8_0_246, List.forall_mem_cons.2 ⟨subd8_0_247, List.forall_mem_cons.2 ⟨subd8_0_248, List.forall_mem_cons.2 ⟨subd8_0_249, List.forall_mem_cons.2 ⟨subd8_0_250, List.forall_mem_cons.2 ⟨subd8_0_251, List.forall_mem_cons.2 ⟨subd8_0_252, List.forall_mem_cons.2 ⟨subd8_0_253, List.forall_mem_cons.2 ⟨subd8_0_254, List.forall_mem_cons.2 ⟨subd8_0_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_256 : subd8_0 [0, 2, 4] = true := by decide +kernel
theorem subd8_0_257 : subd8_0 [0, 2, 5] = true := by decide +kernel
theorem subd8_0_258 : subd8_0 [0, 2, 6] = true := by decide +kernel
theorem subd8_0_259 : subd8_0 [0, 2, 7] = true := by decide +kernel
theorem subd8_0_260 : subd8_0 [0, 2, 8] = true := by decide +kernel
theorem subd8_0_261 : subd8_0 [0, 3] = true := by decide +kernel
theorem subd8_0_262 : subd8_0 [1, -3] = true := by decide +kernel
theorem subd8_0_263 : subd8_0 [1, -2, -7] = true := by decide +kernel
theorem subd8_0_264 : subd8_0 [1, -2, -6] = true := by decide +kernel
theorem subd8_0_265 : subd8_0 [1, -2, -5] = true := by decide +kernel
theorem subd8_0_266 : subd8_0 [1, -2, -4] = true := by decide +kernel
theorem subd8_0_267 : subd8_0 [1, -2, -3] = true := by decide +kernel
theorem subd8_0_268 : subd8_0 [1, -2, -2] = true := by decide +kernel
theorem subd8_0_269 : subd8_0 [1, -2, -1] = true := by decide +kernel
theorem subd8_0_270 : subd8_0 [1, -2, 0] = true := by decide +kernel
theorem subd8_0_271 : subd8_0 [1, -2, 1] = true := by decide +kernel
theorem subd8_0_272 : subd8_0 [1, -2, 2] = true := by decide +kernel
theorem subd8_0_273 : subd8_0 [1, -2, 3] = true := by decide +kernel
theorem subd8_0_274 : subd8_0 [1, -2, 4] = true := by decide +kernel
theorem subd8_0_275 : subd8_0 [1, -2, 5] = true := by decide +kernel
theorem subd8_0_276 : subd8_0 [1, -2, 6] = true := by decide +kernel
theorem subd8_0_277 : subd8_0 [1, -2, 7] = true := by decide +kernel
theorem subd8_0_278 : subd8_0 [1, -1, -9] = true := by decide +kernel
theorem subd8_0_279 : subd8_0 [1, -1, -8] = true := by decide +kernel
theorem subd8_0_280 : subd8_0 [1, -1, -7] = true := by decide +kernel
theorem subd8_0_281 : subd8_0 [1, -1, -6] = true := by decide +kernel
theorem subd8_0_282 : subd8_0 [1, -1, -5] = true := by decide +kernel
theorem subd8_0_283 : subd8_0 [1, -1, -4] = true := by decide +kernel
theorem subd8_0_284 : subd8_0 [1, -1, -3] = true := by decide +kernel
theorem subd8_0_285 : subd8_0 [1, -1, -2] = true := by decide +kernel
theorem subd8_0_286 : subd8_0 [1, -1, -1] = true := by decide +kernel
theorem subd8_0_287 : subd8_0 [1, -1, 0] = true := by decide +kernel
theorem sbd8_0_8 : ∀ q ∈ blkd8_0_8, subd8_0 q = true := by
  unfold blkd8_0_8
  exact List.forall_mem_cons.2 ⟨subd8_0_256, List.forall_mem_cons.2 ⟨subd8_0_257, List.forall_mem_cons.2 ⟨subd8_0_258, List.forall_mem_cons.2 ⟨subd8_0_259, List.forall_mem_cons.2 ⟨subd8_0_260, List.forall_mem_cons.2 ⟨subd8_0_261, List.forall_mem_cons.2 ⟨subd8_0_262, List.forall_mem_cons.2 ⟨subd8_0_263, List.forall_mem_cons.2 ⟨subd8_0_264, List.forall_mem_cons.2 ⟨subd8_0_265, List.forall_mem_cons.2 ⟨subd8_0_266, List.forall_mem_cons.2 ⟨subd8_0_267, List.forall_mem_cons.2 ⟨subd8_0_268, List.forall_mem_cons.2 ⟨subd8_0_269, List.forall_mem_cons.2 ⟨subd8_0_270, List.forall_mem_cons.2 ⟨subd8_0_271, List.forall_mem_cons.2 ⟨subd8_0_272, List.forall_mem_cons.2 ⟨subd8_0_273, List.forall_mem_cons.2 ⟨subd8_0_274, List.forall_mem_cons.2 ⟨subd8_0_275, List.forall_mem_cons.2 ⟨subd8_0_276, List.forall_mem_cons.2 ⟨subd8_0_277, List.forall_mem_cons.2 ⟨subd8_0_278, List.forall_mem_cons.2 ⟨subd8_0_279, List.forall_mem_cons.2 ⟨subd8_0_280, List.forall_mem_cons.2 ⟨subd8_0_281, List.forall_mem_cons.2 ⟨subd8_0_282, List.forall_mem_cons.2 ⟨subd8_0_283, List.forall_mem_cons.2 ⟨subd8_0_284, List.forall_mem_cons.2 ⟨subd8_0_285, List.forall_mem_cons.2 ⟨subd8_0_286, List.forall_mem_cons.2 ⟨subd8_0_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_288 : subd8_0 [1, -1, 1] = true := by decide +kernel
theorem subd8_0_289 : subd8_0 [1, -1, 2] = true := by decide +kernel
theorem subd8_0_290 : subd8_0 [1, -1, 3] = true := by decide +kernel
theorem subd8_0_291 : subd8_0 [1, -1, 4] = true := by decide +kernel
theorem subd8_0_292 : subd8_0 [1, -1, 5] = true := by decide +kernel
theorem subd8_0_293 : subd8_0 [1, -1, 6] = true := by decide +kernel
theorem subd8_0_294 : subd8_0 [1, -1, 7] = true := by decide +kernel
theorem subd8_0_295 : subd8_0 [1, -1, 8] = true := by decide +kernel
theorem subd8_0_296 : subd8_0 [1, -1, 9] = true := by decide +kernel
theorem subd8_0_297 : subd8_0 [1, 0, -10] = true := by decide +kernel
theorem subd8_0_298 : subd8_0 [1, 0, -9] = true := by decide +kernel
theorem subd8_0_299 : subd8_0 [1, 0, -8] = true := by decide +kernel
theorem subd8_0_300 : subd8_0 [1, 0, -7] = true := by decide +kernel
theorem subd8_0_301 : subd8_0 [1, 0, -6] = true := by decide +kernel
theorem subd8_0_302 : subd8_0 [1, 0, -5] = true := by decide +kernel
theorem subd8_0_303 : subd8_0 [1, 0, -4] = true := by decide +kernel
theorem subd8_0_304 : subd8_0 [1, 0, -3] = true := by decide +kernel
theorem subd8_0_305 : subd8_0 [1, 0, -2] = true := by decide +kernel
theorem subd8_0_306 : subd8_0 [1, 0, -1] = true := by decide +kernel
theorem subd8_0_307 : subd8_0 [1, 0, 0] = true := by decide +kernel
theorem subd8_0_308 : subd8_0 [1, 0, 1] = true := by decide +kernel
theorem subd8_0_309 : subd8_0 [1, 0, 2] = true := by decide +kernel
theorem subd8_0_310 : subd8_0 [1, 0, 3] = true := by decide +kernel
theorem subd8_0_311 : subd8_0 [1, 0, 4] = true := by decide +kernel
theorem subd8_0_312 : subd8_0 [1, 0, 5] = true := by decide +kernel
theorem subd8_0_313 : subd8_0 [1, 0, 6] = true := by decide +kernel
theorem subd8_0_314 : subd8_0 [1, 0, 7] = true := by decide +kernel
theorem subd8_0_315 : subd8_0 [1, 0, 8] = true := by decide +kernel
theorem subd8_0_316 : subd8_0 [1, 0, 9] = true := by decide +kernel
theorem subd8_0_317 : subd8_0 [1, 0, 10] = true := by decide +kernel
theorem subd8_0_318 : subd8_0 [1, 1, -10] = true := by decide +kernel
theorem subd8_0_319 : subd8_0 [1, 1, -9] = true := by decide +kernel
theorem sbd8_0_9 : ∀ q ∈ blkd8_0_9, subd8_0 q = true := by
  unfold blkd8_0_9
  exact List.forall_mem_cons.2 ⟨subd8_0_288, List.forall_mem_cons.2 ⟨subd8_0_289, List.forall_mem_cons.2 ⟨subd8_0_290, List.forall_mem_cons.2 ⟨subd8_0_291, List.forall_mem_cons.2 ⟨subd8_0_292, List.forall_mem_cons.2 ⟨subd8_0_293, List.forall_mem_cons.2 ⟨subd8_0_294, List.forall_mem_cons.2 ⟨subd8_0_295, List.forall_mem_cons.2 ⟨subd8_0_296, List.forall_mem_cons.2 ⟨subd8_0_297, List.forall_mem_cons.2 ⟨subd8_0_298, List.forall_mem_cons.2 ⟨subd8_0_299, List.forall_mem_cons.2 ⟨subd8_0_300, List.forall_mem_cons.2 ⟨subd8_0_301, List.forall_mem_cons.2 ⟨subd8_0_302, List.forall_mem_cons.2 ⟨subd8_0_303, List.forall_mem_cons.2 ⟨subd8_0_304, List.forall_mem_cons.2 ⟨subd8_0_305, List.forall_mem_cons.2 ⟨subd8_0_306, List.forall_mem_cons.2 ⟨subd8_0_307, List.forall_mem_cons.2 ⟨subd8_0_308, List.forall_mem_cons.2 ⟨subd8_0_309, List.forall_mem_cons.2 ⟨subd8_0_310, List.forall_mem_cons.2 ⟨subd8_0_311, List.forall_mem_cons.2 ⟨subd8_0_312, List.forall_mem_cons.2 ⟨subd8_0_313, List.forall_mem_cons.2 ⟨subd8_0_314, List.forall_mem_cons.2 ⟨subd8_0_315, List.forall_mem_cons.2 ⟨subd8_0_316, List.forall_mem_cons.2 ⟨subd8_0_317, List.forall_mem_cons.2 ⟨subd8_0_318, List.forall_mem_cons.2 ⟨subd8_0_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_320 : subd8_0 [1, 1, -8] = true := by decide +kernel
theorem subd8_0_321 : subd8_0 [1, 1, -7] = true := by decide +kernel
theorem subd8_0_322 : subd8_0 [1, 1, -6] = true := by decide +kernel
theorem subd8_0_323 : subd8_0 [1, 1, -5] = true := by decide +kernel
theorem subd8_0_324 : subd8_0 [1, 1, -4] = true := by decide +kernel
theorem subd8_0_325 : subd8_0 [1, 1, -3] = true := by decide +kernel
theorem subd8_0_326 : subd8_0 [1, 1, -2] = true := by decide +kernel
theorem subd8_0_327 : subd8_0 [1, 1, -1] = true := by decide +kernel
theorem subd8_0_328 : subd8_0 [1, 1, 0] = true := by decide +kernel
theorem subd8_0_329 : subd8_0 [1, 1, 1] = true := by decide +kernel
theorem subd8_0_330 : subd8_0 [1, 1, 2] = true := by decide +kernel
theorem subd8_0_331 : subd8_0 [1, 1, 3] = true := by decide +kernel
theorem subd8_0_332 : subd8_0 [1, 1, 4] = true := by decide +kernel
theorem subd8_0_333 : subd8_0 [1, 1, 5] = true := by decide +kernel
theorem subd8_0_334 : subd8_0 [1, 1, 6] = true := by decide +kernel
theorem subd8_0_335 : subd8_0 [1, 1, 7] = true := by decide +kernel
theorem subd8_0_336 : subd8_0 [1, 1, 8] = true := by decide +kernel
theorem subd8_0_337 : subd8_0 [1, 1, 9] = true := by decide +kernel
theorem subd8_0_338 : subd8_0 [1, 2, -9] = true := by decide +kernel
theorem subd8_0_339 : subd8_0 [1, 2, -8] = true := by decide +kernel
theorem subd8_0_340 : subd8_0 [1, 2, -7] = true := by decide +kernel
theorem subd8_0_341 : subd8_0 [1, 2, -6] = true := by decide +kernel
theorem subd8_0_342 : subd8_0 [1, 2, -5] = true := by decide +kernel
theorem subd8_0_343 : subd8_0 [1, 2, -4] = true := by decide +kernel
theorem subd8_0_344 : subd8_0 [1, 2, -3] = true := by decide +kernel
theorem subd8_0_345 : subd8_0 [1, 2, -2] = true := by decide +kernel
theorem subd8_0_346 : subd8_0 [1, 2, -1] = true := by decide +kernel
theorem subd8_0_347 : subd8_0 [1, 2, 0] = true := by decide +kernel
theorem subd8_0_348 : subd8_0 [1, 2, 1] = true := by decide +kernel
theorem subd8_0_349 : subd8_0 [1, 2, 2] = true := by decide +kernel
theorem subd8_0_350 : subd8_0 [1, 2, 3] = true := by decide +kernel
theorem subd8_0_351 : subd8_0 [1, 2, 4] = true := by decide +kernel
theorem sbd8_0_10 : ∀ q ∈ blkd8_0_10, subd8_0 q = true := by
  unfold blkd8_0_10
  exact List.forall_mem_cons.2 ⟨subd8_0_320, List.forall_mem_cons.2 ⟨subd8_0_321, List.forall_mem_cons.2 ⟨subd8_0_322, List.forall_mem_cons.2 ⟨subd8_0_323, List.forall_mem_cons.2 ⟨subd8_0_324, List.forall_mem_cons.2 ⟨subd8_0_325, List.forall_mem_cons.2 ⟨subd8_0_326, List.forall_mem_cons.2 ⟨subd8_0_327, List.forall_mem_cons.2 ⟨subd8_0_328, List.forall_mem_cons.2 ⟨subd8_0_329, List.forall_mem_cons.2 ⟨subd8_0_330, List.forall_mem_cons.2 ⟨subd8_0_331, List.forall_mem_cons.2 ⟨subd8_0_332, List.forall_mem_cons.2 ⟨subd8_0_333, List.forall_mem_cons.2 ⟨subd8_0_334, List.forall_mem_cons.2 ⟨subd8_0_335, List.forall_mem_cons.2 ⟨subd8_0_336, List.forall_mem_cons.2 ⟨subd8_0_337, List.forall_mem_cons.2 ⟨subd8_0_338, List.forall_mem_cons.2 ⟨subd8_0_339, List.forall_mem_cons.2 ⟨subd8_0_340, List.forall_mem_cons.2 ⟨subd8_0_341, List.forall_mem_cons.2 ⟨subd8_0_342, List.forall_mem_cons.2 ⟨subd8_0_343, List.forall_mem_cons.2 ⟨subd8_0_344, List.forall_mem_cons.2 ⟨subd8_0_345, List.forall_mem_cons.2 ⟨subd8_0_346, List.forall_mem_cons.2 ⟨subd8_0_347, List.forall_mem_cons.2 ⟨subd8_0_348, List.forall_mem_cons.2 ⟨subd8_0_349, List.forall_mem_cons.2 ⟨subd8_0_350, List.forall_mem_cons.2 ⟨subd8_0_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_352 : subd8_0 [1, 2, 5] = true := by decide +kernel
theorem subd8_0_353 : subd8_0 [1, 2, 6] = true := by decide +kernel
theorem subd8_0_354 : subd8_0 [1, 2, 7] = true := by decide +kernel
theorem subd8_0_355 : subd8_0 [1, 2, 8] = true := by decide +kernel
theorem subd8_0_356 : subd8_0 [1, 3] = true := by decide +kernel
theorem subd8_0_357 : subd8_0 [2, -2] = true := by decide +kernel
theorem subd8_0_358 : subd8_0 [2, -1, -6] = true := by decide +kernel
theorem subd8_0_359 : subd8_0 [2, -1, -5] = true := by decide +kernel
theorem subd8_0_360 : subd8_0 [2, -1, -4] = true := by decide +kernel
theorem subd8_0_361 : subd8_0 [2, -1, -3] = true := by decide +kernel
theorem subd8_0_362 : subd8_0 [2, -1, -2] = true := by decide +kernel
theorem subd8_0_363 : subd8_0 [2, -1, -1] = true := by decide +kernel
theorem subd8_0_364 : subd8_0 [2, -1, 0] = true := by decide +kernel
theorem subd8_0_365 : subd8_0 [2, -1, 1] = true := by decide +kernel
theorem subd8_0_366 : subd8_0 [2, -1, 2] = true := by decide +kernel
theorem subd8_0_367 : subd8_0 [2, -1, 3] = true := by decide +kernel
theorem subd8_0_368 : subd8_0 [2, -1, 4] = true := by decide +kernel
theorem subd8_0_369 : subd8_0 [2, -1, 5] = true := by decide +kernel
theorem subd8_0_370 : subd8_0 [2, -1, 6] = true := by decide +kernel
theorem subd8_0_371 : subd8_0 [2, 0, -8] = true := by decide +kernel
theorem subd8_0_372 : subd8_0 [2, 0, -7] = true := by decide +kernel
theorem subd8_0_373 : subd8_0 [2, 0, -6] = true := by decide +kernel
theorem subd8_0_374 : subd8_0 [2, 0, -5] = true := by decide +kernel
theorem subd8_0_375 : subd8_0 [2, 0, -4] = true := by decide +kernel
theorem subd8_0_376 : subd8_0 [2, 0, -3] = true := by decide +kernel
theorem subd8_0_377 : subd8_0 [2, 0, -2] = true := by decide +kernel
theorem subd8_0_378 : subd8_0 [2, 0, -1] = true := by decide +kernel
theorem subd8_0_379 : subd8_0 [2, 0, 0] = true := by decide +kernel
theorem subd8_0_380 : subd8_0 [2, 0, 1] = true := by decide +kernel
theorem subd8_0_381 : subd8_0 [2, 0, 2] = true := by decide +kernel
theorem subd8_0_382 : subd8_0 [2, 0, 3] = true := by decide +kernel
theorem subd8_0_383 : subd8_0 [2, 0, 4] = true := by decide +kernel
theorem sbd8_0_11 : ∀ q ∈ blkd8_0_11, subd8_0 q = true := by
  unfold blkd8_0_11
  exact List.forall_mem_cons.2 ⟨subd8_0_352, List.forall_mem_cons.2 ⟨subd8_0_353, List.forall_mem_cons.2 ⟨subd8_0_354, List.forall_mem_cons.2 ⟨subd8_0_355, List.forall_mem_cons.2 ⟨subd8_0_356, List.forall_mem_cons.2 ⟨subd8_0_357, List.forall_mem_cons.2 ⟨subd8_0_358, List.forall_mem_cons.2 ⟨subd8_0_359, List.forall_mem_cons.2 ⟨subd8_0_360, List.forall_mem_cons.2 ⟨subd8_0_361, List.forall_mem_cons.2 ⟨subd8_0_362, List.forall_mem_cons.2 ⟨subd8_0_363, List.forall_mem_cons.2 ⟨subd8_0_364, List.forall_mem_cons.2 ⟨subd8_0_365, List.forall_mem_cons.2 ⟨subd8_0_366, List.forall_mem_cons.2 ⟨subd8_0_367, List.forall_mem_cons.2 ⟨subd8_0_368, List.forall_mem_cons.2 ⟨subd8_0_369, List.forall_mem_cons.2 ⟨subd8_0_370, List.forall_mem_cons.2 ⟨subd8_0_371, List.forall_mem_cons.2 ⟨subd8_0_372, List.forall_mem_cons.2 ⟨subd8_0_373, List.forall_mem_cons.2 ⟨subd8_0_374, List.forall_mem_cons.2 ⟨subd8_0_375, List.forall_mem_cons.2 ⟨subd8_0_376, List.forall_mem_cons.2 ⟨subd8_0_377, List.forall_mem_cons.2 ⟨subd8_0_378, List.forall_mem_cons.2 ⟨subd8_0_379, List.forall_mem_cons.2 ⟨subd8_0_380, List.forall_mem_cons.2 ⟨subd8_0_381, List.forall_mem_cons.2 ⟨subd8_0_382, List.forall_mem_cons.2 ⟨subd8_0_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_384 : subd8_0 [2, 0, 5] = true := by decide +kernel
theorem subd8_0_385 : subd8_0 [2, 0, 6] = true := by decide +kernel
theorem subd8_0_386 : subd8_0 [2, 0, 7] = true := by decide +kernel
theorem subd8_0_387 : subd8_0 [2, 0, 8] = true := by decide +kernel
theorem subd8_0_388 : subd8_0 [2, 1, -8] = true := by decide +kernel
theorem subd8_0_389 : subd8_0 [2, 1, -7] = true := by decide +kernel
theorem subd8_0_390 : subd8_0 [2, 1, -6] = true := by decide +kernel
theorem subd8_0_391 : subd8_0 [2, 1, -5] = true := by decide +kernel
theorem subd8_0_392 : subd8_0 [2, 1, -4] = true := by decide +kernel
theorem subd8_0_393 : subd8_0 [2, 1, -3] = true := by decide +kernel
theorem subd8_0_394 : subd8_0 [2, 1, -2] = true := by decide +kernel
theorem subd8_0_395 : subd8_0 [2, 1, -1] = true := by decide +kernel
theorem subd8_0_396 : subd8_0 [2, 1, 0] = true := by decide +kernel
theorem subd8_0_397 : subd8_0 [2, 1, 1] = true := by decide +kernel
theorem subd8_0_398 : subd8_0 [2, 1, 2] = true := by decide +kernel
theorem subd8_0_399 : subd8_0 [2, 1, 3] = true := by decide +kernel
theorem subd8_0_400 : subd8_0 [2, 1, 4] = true := by decide +kernel
theorem subd8_0_401 : subd8_0 [2, 1, 5] = true := by decide +kernel
theorem subd8_0_402 : subd8_0 [2, 1, 6] = true := by decide +kernel
theorem subd8_0_403 : subd8_0 [2, 1, 7] = true := by decide +kernel
theorem subd8_0_404 : subd8_0 [2, 1, 8] = true := by decide +kernel
theorem subd8_0_405 : subd8_0 [2, 2, -7] = true := by decide +kernel
theorem subd8_0_406 : subd8_0 [2, 2, -6] = true := by decide +kernel
theorem subd8_0_407 : subd8_0 [2, 2, -5] = true := by decide +kernel
theorem subd8_0_408 : subd8_0 [2, 2, -4] = true := by decide +kernel
theorem subd8_0_409 : subd8_0 [2, 2, -3] = true := by decide +kernel
theorem subd8_0_410 : subd8_0 [2, 2, -2] = true := by decide +kernel
theorem subd8_0_411 : subd8_0 [2, 2, -1] = true := by decide +kernel
theorem subd8_0_412 : subd8_0 [2, 2, 0] = true := by decide +kernel
theorem subd8_0_413 : subd8_0 [2, 2, 1] = true := by decide +kernel
theorem subd8_0_414 : subd8_0 [2, 2, 2] = true := by decide +kernel
theorem subd8_0_415 : subd8_0 [2, 2, 3] = true := by decide +kernel
theorem sbd8_0_12 : ∀ q ∈ blkd8_0_12, subd8_0 q = true := by
  unfold blkd8_0_12
  exact List.forall_mem_cons.2 ⟨subd8_0_384, List.forall_mem_cons.2 ⟨subd8_0_385, List.forall_mem_cons.2 ⟨subd8_0_386, List.forall_mem_cons.2 ⟨subd8_0_387, List.forall_mem_cons.2 ⟨subd8_0_388, List.forall_mem_cons.2 ⟨subd8_0_389, List.forall_mem_cons.2 ⟨subd8_0_390, List.forall_mem_cons.2 ⟨subd8_0_391, List.forall_mem_cons.2 ⟨subd8_0_392, List.forall_mem_cons.2 ⟨subd8_0_393, List.forall_mem_cons.2 ⟨subd8_0_394, List.forall_mem_cons.2 ⟨subd8_0_395, List.forall_mem_cons.2 ⟨subd8_0_396, List.forall_mem_cons.2 ⟨subd8_0_397, List.forall_mem_cons.2 ⟨subd8_0_398, List.forall_mem_cons.2 ⟨subd8_0_399, List.forall_mem_cons.2 ⟨subd8_0_400, List.forall_mem_cons.2 ⟨subd8_0_401, List.forall_mem_cons.2 ⟨subd8_0_402, List.forall_mem_cons.2 ⟨subd8_0_403, List.forall_mem_cons.2 ⟨subd8_0_404, List.forall_mem_cons.2 ⟨subd8_0_405, List.forall_mem_cons.2 ⟨subd8_0_406, List.forall_mem_cons.2 ⟨subd8_0_407, List.forall_mem_cons.2 ⟨subd8_0_408, List.forall_mem_cons.2 ⟨subd8_0_409, List.forall_mem_cons.2 ⟨subd8_0_410, List.forall_mem_cons.2 ⟨subd8_0_411, List.forall_mem_cons.2 ⟨subd8_0_412, List.forall_mem_cons.2 ⟨subd8_0_413, List.forall_mem_cons.2 ⟨subd8_0_414, List.forall_mem_cons.2 ⟨subd8_0_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_416 : subd8_0 [2, 2, 4] = true := by decide +kernel
theorem subd8_0_417 : subd8_0 [2, 2, 5] = true := by decide +kernel
theorem subd8_0_418 : subd8_0 [2, 2, 6] = true := by decide +kernel
theorem subd8_0_419 : subd8_0 [2, 3] = true := by decide +kernel
theorem subd8_0_420 : subd8_0 [3] = true := by decide +kernel
theorem sbd8_0_13 : ∀ q ∈ blkd8_0_13, subd8_0 q = true := by
  unfold blkd8_0_13
  exact List.forall_mem_cons.2 ⟨subd8_0_416, List.forall_mem_cons.2 ⟨subd8_0_417, List.forall_mem_cons.2 ⟨subd8_0_418, List.forall_mem_cons.2 ⟨subd8_0_419, List.forall_mem_cons.2 ⟨subd8_0_420, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd8_1 : ldCheck G d8_1.U d8_1.ms ldd8_1 = true := by decide +kernel
theorem pre_okd8_1 : subPre G cell8 d8_1 = true := by decide +kernel
theorem subd8_1_0 : subd8_1 [-4] = true := by decide +kernel
theorem subd8_1_1 : subd8_1 [-3, -3] = true := by decide +kernel
theorem subd8_1_2 : subd8_1 [-3, -2] = true := by decide +kernel
theorem subd8_1_3 : subd8_1 [-3, -1] = true := by decide +kernel
theorem subd8_1_4 : subd8_1 [-3, 0] = true := by decide +kernel
theorem subd8_1_5 : subd8_1 [-3, 1] = true := by decide +kernel
theorem subd8_1_6 : subd8_1 [-3, 2] = true := by decide +kernel
theorem subd8_1_7 : subd8_1 [-3, 3] = true := by decide +kernel
theorem subd8_1_8 : subd8_1 [-3, 4] = true := by decide +kernel
theorem subd8_1_9 : subd8_1 [-3, 5] = true := by decide +kernel
theorem subd8_1_10 : subd8_1 [-2, -4] = true := by decide +kernel
theorem subd8_1_11 : subd8_1 [-2, -3] = true := by decide +kernel
theorem subd8_1_12 : subd8_1 [-2, -2] = true := by decide +kernel
theorem subd8_1_13 : subd8_1 [-2, -1] = true := by decide +kernel
theorem subd8_1_14 : subd8_1 [-2, 0] = true := by decide +kernel
theorem subd8_1_15 : subd8_1 [-2, 1] = true := by decide +kernel
theorem subd8_1_16 : subd8_1 [-2, 2] = true := by decide +kernel
theorem subd8_1_17 : subd8_1 [-2, 3] = true := by decide +kernel
theorem subd8_1_18 : subd8_1 [-2, 4] = true := by decide +kernel
theorem subd8_1_19 : subd8_1 [-2, 5] = true := by decide +kernel
theorem subd8_1_20 : subd8_1 [-1, -5] = true := by decide +kernel
theorem subd8_1_21 : subd8_1 [-1, -4] = true := by decide +kernel
theorem subd8_1_22 : subd8_1 [-1, -3] = true := by decide +kernel
theorem subd8_1_23 : subd8_1 [-1, -2] = true := by decide +kernel
theorem subd8_1_24 : subd8_1 [-1, -1] = true := by decide +kernel
theorem subd8_1_25 : subd8_1 [-1, 0] = true := by decide +kernel
theorem subd8_1_26 : subd8_1 [-1, 1] = true := by decide +kernel
theorem subd8_1_27 : subd8_1 [-1, 2] = true := by decide +kernel
theorem subd8_1_28 : subd8_1 [-1, 3] = true := by decide +kernel
theorem subd8_1_29 : subd8_1 [-1, 4] = true := by decide +kernel
theorem subd8_1_30 : subd8_1 [-1, 5] = true := by decide +kernel
theorem subd8_1_31 : subd8_1 [0, -5] = true := by decide +kernel
theorem sbd8_1_0 : ∀ q ∈ blkd8_1_0, subd8_1 q = true := by
  unfold blkd8_1_0
  exact List.forall_mem_cons.2 ⟨subd8_1_0, List.forall_mem_cons.2 ⟨subd8_1_1, List.forall_mem_cons.2 ⟨subd8_1_2, List.forall_mem_cons.2 ⟨subd8_1_3, List.forall_mem_cons.2 ⟨subd8_1_4, List.forall_mem_cons.2 ⟨subd8_1_5, List.forall_mem_cons.2 ⟨subd8_1_6, List.forall_mem_cons.2 ⟨subd8_1_7, List.forall_mem_cons.2 ⟨subd8_1_8, List.forall_mem_cons.2 ⟨subd8_1_9, List.forall_mem_cons.2 ⟨subd8_1_10, List.forall_mem_cons.2 ⟨subd8_1_11, List.forall_mem_cons.2 ⟨subd8_1_12, List.forall_mem_cons.2 ⟨subd8_1_13, List.forall_mem_cons.2 ⟨subd8_1_14, List.forall_mem_cons.2 ⟨subd8_1_15, List.forall_mem_cons.2 ⟨subd8_1_16, List.forall_mem_cons.2 ⟨subd8_1_17, List.forall_mem_cons.2 ⟨subd8_1_18, List.forall_mem_cons.2 ⟨subd8_1_19, List.forall_mem_cons.2 ⟨subd8_1_20, List.forall_mem_cons.2 ⟨subd8_1_21, List.forall_mem_cons.2 ⟨subd8_1_22, List.forall_mem_cons.2 ⟨subd8_1_23, List.forall_mem_cons.2 ⟨subd8_1_24, List.forall_mem_cons.2 ⟨subd8_1_25, List.forall_mem_cons.2 ⟨subd8_1_26, List.forall_mem_cons.2 ⟨subd8_1_27, List.forall_mem_cons.2 ⟨subd8_1_28, List.forall_mem_cons.2 ⟨subd8_1_29, List.forall_mem_cons.2 ⟨subd8_1_30, List.forall_mem_cons.2 ⟨subd8_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_32 : subd8_1 [0, -4] = true := by decide +kernel
theorem subd8_1_33 : subd8_1 [0, -3] = true := by decide +kernel
theorem subd8_1_34 : subd8_1 [0, -2] = true := by decide +kernel
theorem subd8_1_35 : subd8_1 [0, -1] = true := by decide +kernel
theorem subd8_1_36 : subd8_1 [0, 0] = true := by decide +kernel
theorem subd8_1_37 : subd8_1 [0, 1] = true := by decide +kernel
theorem subd8_1_38 : subd8_1 [0, 2] = true := by decide +kernel
theorem subd8_1_39 : subd8_1 [0, 3] = true := by decide +kernel
theorem subd8_1_40 : subd8_1 [0, 4] = true := by decide +kernel
theorem subd8_1_41 : subd8_1 [1, -6] = true := by decide +kernel
theorem subd8_1_42 : subd8_1 [1, -5] = true := by decide +kernel
theorem subd8_1_43 : subd8_1 [1, -4] = true := by decide +kernel
theorem subd8_1_44 : subd8_1 [1, -3] = true := by decide +kernel
theorem subd8_1_45 : subd8_1 [1, -2] = true := by decide +kernel
theorem subd8_1_46 : subd8_1 [1, -1] = true := by decide +kernel
theorem subd8_1_47 : subd8_1 [1, 0] = true := by decide +kernel
theorem subd8_1_48 : subd8_1 [1, 1] = true := by decide +kernel
theorem subd8_1_49 : subd8_1 [1, 2] = true := by decide +kernel
theorem subd8_1_50 : subd8_1 [1, 3] = true := by decide +kernel
theorem subd8_1_51 : subd8_1 [1, 4] = true := by decide +kernel
theorem subd8_1_52 : subd8_1 [2, -6] = true := by decide +kernel
theorem subd8_1_53 : subd8_1 [2, -5] = true := by decide +kernel
theorem subd8_1_54 : subd8_1 [2, -4] = true := by decide +kernel
theorem subd8_1_55 : subd8_1 [2, -3] = true := by decide +kernel
theorem subd8_1_56 : subd8_1 [2, -2] = true := by decide +kernel
theorem subd8_1_57 : subd8_1 [2, -1] = true := by decide +kernel
theorem subd8_1_58 : subd8_1 [2, 0] = true := by decide +kernel
theorem subd8_1_59 : subd8_1 [2, 1] = true := by decide +kernel
theorem subd8_1_60 : subd8_1 [2, 2] = true := by decide +kernel
theorem subd8_1_61 : subd8_1 [2, 3] = true := by decide +kernel
theorem subd8_1_62 : subd8_1 [3, -6] = true := by decide +kernel
theorem subd8_1_63 : subd8_1 [3, -5] = true := by decide +kernel
theorem sbd8_1_1 : ∀ q ∈ blkd8_1_1, subd8_1 q = true := by
  unfold blkd8_1_1
  exact List.forall_mem_cons.2 ⟨subd8_1_32, List.forall_mem_cons.2 ⟨subd8_1_33, List.forall_mem_cons.2 ⟨subd8_1_34, List.forall_mem_cons.2 ⟨subd8_1_35, List.forall_mem_cons.2 ⟨subd8_1_36, List.forall_mem_cons.2 ⟨subd8_1_37, List.forall_mem_cons.2 ⟨subd8_1_38, List.forall_mem_cons.2 ⟨subd8_1_39, List.forall_mem_cons.2 ⟨subd8_1_40, List.forall_mem_cons.2 ⟨subd8_1_41, List.forall_mem_cons.2 ⟨subd8_1_42, List.forall_mem_cons.2 ⟨subd8_1_43, List.forall_mem_cons.2 ⟨subd8_1_44, List.forall_mem_cons.2 ⟨subd8_1_45, List.forall_mem_cons.2 ⟨subd8_1_46, List.forall_mem_cons.2 ⟨subd8_1_47, List.forall_mem_cons.2 ⟨subd8_1_48, List.forall_mem_cons.2 ⟨subd8_1_49, List.forall_mem_cons.2 ⟨subd8_1_50, List.forall_mem_cons.2 ⟨subd8_1_51, List.forall_mem_cons.2 ⟨subd8_1_52, List.forall_mem_cons.2 ⟨subd8_1_53, List.forall_mem_cons.2 ⟨subd8_1_54, List.forall_mem_cons.2 ⟨subd8_1_55, List.forall_mem_cons.2 ⟨subd8_1_56, List.forall_mem_cons.2 ⟨subd8_1_57, List.forall_mem_cons.2 ⟨subd8_1_58, List.forall_mem_cons.2 ⟨subd8_1_59, List.forall_mem_cons.2 ⟨subd8_1_60, List.forall_mem_cons.2 ⟨subd8_1_61, List.forall_mem_cons.2 ⟨subd8_1_62, List.forall_mem_cons.2 ⟨subd8_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_64 : subd8_1 [3, -4] = true := by decide +kernel
theorem subd8_1_65 : subd8_1 [3, -3] = true := by decide +kernel
theorem subd8_1_66 : subd8_1 [3, -2] = true := by decide +kernel
theorem subd8_1_67 : subd8_1 [3, -1] = true := by decide +kernel
theorem subd8_1_68 : subd8_1 [3, 0] = true := by decide +kernel
theorem subd8_1_69 : subd8_1 [3, 1] = true := by decide +kernel
theorem subd8_1_70 : subd8_1 [3, 2] = true := by decide +kernel
theorem subd8_1_71 : subd8_1 [4] = true := by decide +kernel
theorem sbd8_1_2 : ∀ q ∈ blkd8_1_2, subd8_1 q = true := by
  unfold blkd8_1_2
  exact List.forall_mem_cons.2 ⟨subd8_1_64, List.forall_mem_cons.2 ⟨subd8_1_65, List.forall_mem_cons.2 ⟨subd8_1_66, List.forall_mem_cons.2 ⟨subd8_1_67, List.forall_mem_cons.2 ⟨subd8_1_68, List.forall_mem_cons.2 ⟨subd8_1_69, List.forall_mem_cons.2 ⟨subd8_1_70, List.forall_mem_cons.2 ⟨subd8_1_71, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_0 : ldCheck G d9_0.U d9_0.ms ldd9_0 = true := by decide +kernel
theorem pre_okd9_0 : subPre G cell9 d9_0 = true := by decide +kernel
theorem subd9_0_0 : subd9_0 [-5] = true := by decide +kernel
theorem subd9_0_1 : subd9_0 [-4, -6] = true := by decide +kernel
theorem subd9_0_2 : subd9_0 [-4, -5] = true := by decide +kernel
theorem subd9_0_3 : subd9_0 [-4, -4] = true := by decide +kernel
theorem subd9_0_4 : subd9_0 [-4, -3, -7] = true := by decide +kernel
theorem subd9_0_5 : subd9_0 [-4, -3, -6] = true := by decide +kernel
theorem subd9_0_6 : subd9_0 [-4, -3, -5] = true := by decide +kernel
theorem subd9_0_7 : subd9_0 [-4, -3, -4] = true := by decide +kernel
theorem subd9_0_8 : subd9_0 [-4, -3, -3] = true := by decide +kernel
theorem subd9_0_9 : subd9_0 [-4, -3, -2] = true := by decide +kernel
theorem subd9_0_10 : subd9_0 [-4, -3, -1] = true := by decide +kernel
theorem subd9_0_11 : subd9_0 [-4, -3, 0] = true := by decide +kernel
theorem subd9_0_12 : subd9_0 [-4, -3, 1] = true := by decide +kernel
theorem subd9_0_13 : subd9_0 [-4, -3, 2] = true := by decide +kernel
theorem subd9_0_14 : subd9_0 [-4, -3, 3] = true := by decide +kernel
theorem subd9_0_15 : subd9_0 [-4, -3, 4] = true := by decide +kernel
theorem subd9_0_16 : subd9_0 [-4, -3, 5] = true := by decide +kernel
theorem subd9_0_17 : subd9_0 [-4, -2, -8] = true := by decide +kernel
theorem subd9_0_18 : subd9_0 [-4, -2, -7] = true := by decide +kernel
theorem subd9_0_19 : subd9_0 [-4, -2, -6] = true := by decide +kernel
theorem subd9_0_20 : subd9_0 [-4, -2, -5] = true := by decide +kernel
theorem subd9_0_21 : subd9_0 [-4, -2, -4] = true := by decide +kernel
theorem subd9_0_22 : subd9_0 [-4, -2, -3] = true := by decide +kernel
theorem subd9_0_23 : subd9_0 [-4, -2, -2] = true := by decide +kernel
theorem subd9_0_24 : subd9_0 [-4, -2, -1] = true := by decide +kernel
theorem subd9_0_25 : subd9_0 [-4, -2, 0] = true := by decide +kernel
theorem subd9_0_26 : subd9_0 [-4, -2, 1] = true := by decide +kernel
theorem subd9_0_27 : subd9_0 [-4, -2, 2] = true := by decide +kernel
theorem subd9_0_28 : subd9_0 [-4, -2, 3] = true := by decide +kernel
theorem subd9_0_29 : subd9_0 [-4, -2, 4] = true := by decide +kernel
theorem subd9_0_30 : subd9_0 [-4, -2, 5] = true := by decide +kernel
theorem subd9_0_31 : subd9_0 [-4, -1, -8] = true := by decide +kernel
theorem sbd9_0_0 : ∀ q ∈ blkd9_0_0, subd9_0 q = true := by
  unfold blkd9_0_0
  exact List.forall_mem_cons.2 ⟨subd9_0_0, List.forall_mem_cons.2 ⟨subd9_0_1, List.forall_mem_cons.2 ⟨subd9_0_2, List.forall_mem_cons.2 ⟨subd9_0_3, List.forall_mem_cons.2 ⟨subd9_0_4, List.forall_mem_cons.2 ⟨subd9_0_5, List.forall_mem_cons.2 ⟨subd9_0_6, List.forall_mem_cons.2 ⟨subd9_0_7, List.forall_mem_cons.2 ⟨subd9_0_8, List.forall_mem_cons.2 ⟨subd9_0_9, List.forall_mem_cons.2 ⟨subd9_0_10, List.forall_mem_cons.2 ⟨subd9_0_11, List.forall_mem_cons.2 ⟨subd9_0_12, List.forall_mem_cons.2 ⟨subd9_0_13, List.forall_mem_cons.2 ⟨subd9_0_14, List.forall_mem_cons.2 ⟨subd9_0_15, List.forall_mem_cons.2 ⟨subd9_0_16, List.forall_mem_cons.2 ⟨subd9_0_17, List.forall_mem_cons.2 ⟨subd9_0_18, List.forall_mem_cons.2 ⟨subd9_0_19, List.forall_mem_cons.2 ⟨subd9_0_20, List.forall_mem_cons.2 ⟨subd9_0_21, List.forall_mem_cons.2 ⟨subd9_0_22, List.forall_mem_cons.2 ⟨subd9_0_23, List.forall_mem_cons.2 ⟨subd9_0_24, List.forall_mem_cons.2 ⟨subd9_0_25, List.forall_mem_cons.2 ⟨subd9_0_26, List.forall_mem_cons.2 ⟨subd9_0_27, List.forall_mem_cons.2 ⟨subd9_0_28, List.forall_mem_cons.2 ⟨subd9_0_29, List.forall_mem_cons.2 ⟨subd9_0_30, List.forall_mem_cons.2 ⟨subd9_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C131
