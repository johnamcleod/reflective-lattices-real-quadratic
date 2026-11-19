import ReflectZphi.Data.Cert5.C077.Base

namespace ReflectZphi.Data.Cert5.C077

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_3_224 : subd8_3 [0, 2, -5] = true := by decide +kernel
theorem subd8_3_225 : subd8_3 [0, 2, -4] = true := by decide +kernel
theorem subd8_3_226 : subd8_3 [0, 2, -3] = true := by decide +kernel
theorem subd8_3_227 : subd8_3 [0, 2, -2] = true := by decide +kernel
theorem subd8_3_228 : subd8_3 [0, 2, -1] = true := by decide +kernel
theorem subd8_3_229 : subd8_3 [0, 2, 0] = true := by decide +kernel
theorem subd8_3_230 : subd8_3 [0, 2, 1] = true := by decide +kernel
theorem subd8_3_231 : subd8_3 [0, 2, 2] = true := by decide +kernel
theorem subd8_3_232 : subd8_3 [0, 2, 3] = true := by decide +kernel
theorem subd8_3_233 : subd8_3 [0, 2, 4] = true := by decide +kernel
theorem subd8_3_234 : subd8_3 [0, 2, 5] = true := by decide +kernel
theorem subd8_3_235 : subd8_3 [0, 2, 6] = true := by decide +kernel
theorem subd8_3_236 : subd8_3 [0, 3] = true := by decide +kernel
theorem subd8_3_237 : subd8_3 [0, 4] = true := by decide +kernel
theorem subd8_3_238 : subd8_3 [0, 5] = true := by decide +kernel
theorem subd8_3_239 : subd8_3 [0, 6] = true := by decide +kernel
theorem subd8_3_240 : subd8_3 [0, 7] = true := by decide +kernel
theorem subd8_3_241 : subd8_3 [1, -8] = true := by decide +kernel
theorem subd8_3_242 : subd8_3 [1, -7] = true := by decide +kernel
theorem subd8_3_243 : subd8_3 [1, -6] = true := by decide +kernel
theorem subd8_3_244 : subd8_3 [1, -5] = true := by decide +kernel
theorem subd8_3_245 : subd8_3 [1, -4] = true := by decide +kernel
theorem subd8_3_246 : subd8_3 [1, -3] = true := by decide +kernel
theorem subd8_3_247 : subd8_3 [1, -2, -7] = true := by decide +kernel
theorem subd8_3_248 : subd8_3 [1, -2, -6] = true := by decide +kernel
theorem subd8_3_249 : subd8_3 [1, -2, -5] = true := by decide +kernel
theorem subd8_3_250 : subd8_3 [1, -2, -4] = true := by decide +kernel
theorem subd8_3_251 : subd8_3 [1, -2, -3] = true := by decide +kernel
theorem subd8_3_252 : subd8_3 [1, -2, -2] = true := by decide +kernel
theorem subd8_3_253 : subd8_3 [1, -2, -1] = true := by decide +kernel
theorem subd8_3_254 : subd8_3 [1, -2, 0] = true := by decide +kernel
theorem subd8_3_255 : subd8_3 [1, -2, 1] = true := by decide +kernel
theorem sbd8_3_7 : ∀ q ∈ blkd8_3_7, subd8_3 q = true := by
  unfold blkd8_3_7
  exact List.forall_mem_cons.2 ⟨subd8_3_224, List.forall_mem_cons.2 ⟨subd8_3_225, List.forall_mem_cons.2 ⟨subd8_3_226, List.forall_mem_cons.2 ⟨subd8_3_227, List.forall_mem_cons.2 ⟨subd8_3_228, List.forall_mem_cons.2 ⟨subd8_3_229, List.forall_mem_cons.2 ⟨subd8_3_230, List.forall_mem_cons.2 ⟨subd8_3_231, List.forall_mem_cons.2 ⟨subd8_3_232, List.forall_mem_cons.2 ⟨subd8_3_233, List.forall_mem_cons.2 ⟨subd8_3_234, List.forall_mem_cons.2 ⟨subd8_3_235, List.forall_mem_cons.2 ⟨subd8_3_236, List.forall_mem_cons.2 ⟨subd8_3_237, List.forall_mem_cons.2 ⟨subd8_3_238, List.forall_mem_cons.2 ⟨subd8_3_239, List.forall_mem_cons.2 ⟨subd8_3_240, List.forall_mem_cons.2 ⟨subd8_3_241, List.forall_mem_cons.2 ⟨subd8_3_242, List.forall_mem_cons.2 ⟨subd8_3_243, List.forall_mem_cons.2 ⟨subd8_3_244, List.forall_mem_cons.2 ⟨subd8_3_245, List.forall_mem_cons.2 ⟨subd8_3_246, List.forall_mem_cons.2 ⟨subd8_3_247, List.forall_mem_cons.2 ⟨subd8_3_248, List.forall_mem_cons.2 ⟨subd8_3_249, List.forall_mem_cons.2 ⟨subd8_3_250, List.forall_mem_cons.2 ⟨subd8_3_251, List.forall_mem_cons.2 ⟨subd8_3_252, List.forall_mem_cons.2 ⟨subd8_3_253, List.forall_mem_cons.2 ⟨subd8_3_254, List.forall_mem_cons.2 ⟨subd8_3_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_256 : subd8_3 [1, -2, 2] = true := by decide +kernel
theorem subd8_3_257 : subd8_3 [1, -2, 3] = true := by decide +kernel
theorem subd8_3_258 : subd8_3 [1, -2, 4] = true := by decide +kernel
theorem subd8_3_259 : subd8_3 [1, -2, 5] = true := by decide +kernel
theorem subd8_3_260 : subd8_3 [1, -1, -7] = true := by decide +kernel
theorem subd8_3_261 : subd8_3 [1, -1, -6] = true := by decide +kernel
theorem subd8_3_262 : subd8_3 [1, -1, -5] = true := by decide +kernel
theorem subd8_3_263 : subd8_3 [1, -1, -4] = true := by decide +kernel
theorem subd8_3_264 : subd8_3 [1, -1, -3] = true := by decide +kernel
theorem subd8_3_265 : subd8_3 [1, -1, -2] = true := by decide +kernel
theorem subd8_3_266 : subd8_3 [1, -1, -1] = true := by decide +kernel
theorem subd8_3_267 : subd8_3 [1, -1, 0] = true := by decide +kernel
theorem subd8_3_268 : subd8_3 [1, -1, 1] = true := by decide +kernel
theorem subd8_3_269 : subd8_3 [1, -1, 2] = true := by decide +kernel
theorem subd8_3_270 : subd8_3 [1, -1, 3] = true := by decide +kernel
theorem subd8_3_271 : subd8_3 [1, -1, 4] = true := by decide +kernel
theorem subd8_3_272 : subd8_3 [1, -1, 5] = true := by decide +kernel
theorem subd8_3_273 : subd8_3 [1, -1, 6] = true := by decide +kernel
theorem subd8_3_274 : subd8_3 [1, 0, -7] = true := by decide +kernel
theorem subd8_3_275 : subd8_3 [1, 0, -6] = true := by decide +kernel
theorem subd8_3_276 : subd8_3 [1, 0, -5] = true := by decide +kernel
theorem subd8_3_277 : subd8_3 [1, 0, -4] = true := by decide +kernel
theorem subd8_3_278 : subd8_3 [1, 0, -3] = true := by decide +kernel
theorem subd8_3_279 : subd8_3 [1, 0, -2] = true := by decide +kernel
theorem subd8_3_280 : subd8_3 [1, 0, -1] = true := by decide +kernel
theorem subd8_3_281 : subd8_3 [1, 0, 0] = true := by decide +kernel
theorem subd8_3_282 : subd8_3 [1, 0, 1] = true := by decide +kernel
theorem subd8_3_283 : subd8_3 [1, 0, 2] = true := by decide +kernel
theorem subd8_3_284 : subd8_3 [1, 0, 3] = true := by decide +kernel
theorem subd8_3_285 : subd8_3 [1, 0, 4] = true := by decide +kernel
theorem subd8_3_286 : subd8_3 [1, 0, 5] = true := by decide +kernel
theorem subd8_3_287 : subd8_3 [1, 0, 6] = true := by decide +kernel
theorem sbd8_3_8 : ∀ q ∈ blkd8_3_8, subd8_3 q = true := by
  unfold blkd8_3_8
  exact List.forall_mem_cons.2 ⟨subd8_3_256, List.forall_mem_cons.2 ⟨subd8_3_257, List.forall_mem_cons.2 ⟨subd8_3_258, List.forall_mem_cons.2 ⟨subd8_3_259, List.forall_mem_cons.2 ⟨subd8_3_260, List.forall_mem_cons.2 ⟨subd8_3_261, List.forall_mem_cons.2 ⟨subd8_3_262, List.forall_mem_cons.2 ⟨subd8_3_263, List.forall_mem_cons.2 ⟨subd8_3_264, List.forall_mem_cons.2 ⟨subd8_3_265, List.forall_mem_cons.2 ⟨subd8_3_266, List.forall_mem_cons.2 ⟨subd8_3_267, List.forall_mem_cons.2 ⟨subd8_3_268, List.forall_mem_cons.2 ⟨subd8_3_269, List.forall_mem_cons.2 ⟨subd8_3_270, List.forall_mem_cons.2 ⟨subd8_3_271, List.forall_mem_cons.2 ⟨subd8_3_272, List.forall_mem_cons.2 ⟨subd8_3_273, List.forall_mem_cons.2 ⟨subd8_3_274, List.forall_mem_cons.2 ⟨subd8_3_275, List.forall_mem_cons.2 ⟨subd8_3_276, List.forall_mem_cons.2 ⟨subd8_3_277, List.forall_mem_cons.2 ⟨subd8_3_278, List.forall_mem_cons.2 ⟨subd8_3_279, List.forall_mem_cons.2 ⟨subd8_3_280, List.forall_mem_cons.2 ⟨subd8_3_281, List.forall_mem_cons.2 ⟨subd8_3_282, List.forall_mem_cons.2 ⟨subd8_3_283, List.forall_mem_cons.2 ⟨subd8_3_284, List.forall_mem_cons.2 ⟨subd8_3_285, List.forall_mem_cons.2 ⟨subd8_3_286, List.forall_mem_cons.2 ⟨subd8_3_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_288 : subd8_3 [1, 1, -6] = true := by decide +kernel
theorem subd8_3_289 : subd8_3 [1, 1, -5] = true := by decide +kernel
theorem subd8_3_290 : subd8_3 [1, 1, -4] = true := by decide +kernel
theorem subd8_3_291 : subd8_3 [1, 1, -3] = true := by decide +kernel
theorem subd8_3_292 : subd8_3 [1, 1, -2] = true := by decide +kernel
theorem subd8_3_293 : subd8_3 [1, 1, -1] = true := by decide +kernel
theorem subd8_3_294 : subd8_3 [1, 1, 0] = true := by decide +kernel
theorem subd8_3_295 : subd8_3 [1, 1, 1] = true := by decide +kernel
theorem subd8_3_296 : subd8_3 [1, 1, 2] = true := by decide +kernel
theorem subd8_3_297 : subd8_3 [1, 1, 3] = true := by decide +kernel
theorem subd8_3_298 : subd8_3 [1, 1, 4] = true := by decide +kernel
theorem subd8_3_299 : subd8_3 [1, 1, 5] = true := by decide +kernel
theorem subd8_3_300 : subd8_3 [1, 1, 6] = true := by decide +kernel
theorem subd8_3_301 : subd8_3 [1, 2, -6] = true := by decide +kernel
theorem subd8_3_302 : subd8_3 [1, 2, -5] = true := by decide +kernel
theorem subd8_3_303 : subd8_3 [1, 2, -4] = true := by decide +kernel
theorem subd8_3_304 : subd8_3 [1, 2, -3] = true := by decide +kernel
theorem subd8_3_305 : subd8_3 [1, 2, -2] = true := by decide +kernel
theorem subd8_3_306 : subd8_3 [1, 2, -1] = true := by decide +kernel
theorem subd8_3_307 : subd8_3 [1, 2, 0] = true := by decide +kernel
theorem subd8_3_308 : subd8_3 [1, 2, 1] = true := by decide +kernel
theorem subd8_3_309 : subd8_3 [1, 2, 2] = true := by decide +kernel
theorem subd8_3_310 : subd8_3 [1, 2, 3] = true := by decide +kernel
theorem subd8_3_311 : subd8_3 [1, 2, 4] = true := by decide +kernel
theorem subd8_3_312 : subd8_3 [1, 2, 5] = true := by decide +kernel
theorem subd8_3_313 : subd8_3 [1, 2, 6] = true := by decide +kernel
theorem subd8_3_314 : subd8_3 [1, 3] = true := by decide +kernel
theorem subd8_3_315 : subd8_3 [1, 4] = true := by decide +kernel
theorem subd8_3_316 : subd8_3 [1, 5] = true := by decide +kernel
theorem subd8_3_317 : subd8_3 [1, 6] = true := by decide +kernel
theorem subd8_3_318 : subd8_3 [1, 7] = true := by decide +kernel
theorem subd8_3_319 : subd8_3 [2, -7] = true := by decide +kernel
theorem sbd8_3_9 : ∀ q ∈ blkd8_3_9, subd8_3 q = true := by
  unfold blkd8_3_9
  exact List.forall_mem_cons.2 ⟨subd8_3_288, List.forall_mem_cons.2 ⟨subd8_3_289, List.forall_mem_cons.2 ⟨subd8_3_290, List.forall_mem_cons.2 ⟨subd8_3_291, List.forall_mem_cons.2 ⟨subd8_3_292, List.forall_mem_cons.2 ⟨subd8_3_293, List.forall_mem_cons.2 ⟨subd8_3_294, List.forall_mem_cons.2 ⟨subd8_3_295, List.forall_mem_cons.2 ⟨subd8_3_296, List.forall_mem_cons.2 ⟨subd8_3_297, List.forall_mem_cons.2 ⟨subd8_3_298, List.forall_mem_cons.2 ⟨subd8_3_299, List.forall_mem_cons.2 ⟨subd8_3_300, List.forall_mem_cons.2 ⟨subd8_3_301, List.forall_mem_cons.2 ⟨subd8_3_302, List.forall_mem_cons.2 ⟨subd8_3_303, List.forall_mem_cons.2 ⟨subd8_3_304, List.forall_mem_cons.2 ⟨subd8_3_305, List.forall_mem_cons.2 ⟨subd8_3_306, List.forall_mem_cons.2 ⟨subd8_3_307, List.forall_mem_cons.2 ⟨subd8_3_308, List.forall_mem_cons.2 ⟨subd8_3_309, List.forall_mem_cons.2 ⟨subd8_3_310, List.forall_mem_cons.2 ⟨subd8_3_311, List.forall_mem_cons.2 ⟨subd8_3_312, List.forall_mem_cons.2 ⟨subd8_3_313, List.forall_mem_cons.2 ⟨subd8_3_314, List.forall_mem_cons.2 ⟨subd8_3_315, List.forall_mem_cons.2 ⟨subd8_3_316, List.forall_mem_cons.2 ⟨subd8_3_317, List.forall_mem_cons.2 ⟨subd8_3_318, List.forall_mem_cons.2 ⟨subd8_3_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_320 : subd8_3 [2, -6] = true := by decide +kernel
theorem subd8_3_321 : subd8_3 [2, -5] = true := by decide +kernel
theorem subd8_3_322 : subd8_3 [2, -4] = true := by decide +kernel
theorem subd8_3_323 : subd8_3 [2, -3] = true := by decide +kernel
theorem subd8_3_324 : subd8_3 [2, -2] = true := by decide +kernel
theorem subd8_3_325 : subd8_3 [2, -1, -6] = true := by decide +kernel
theorem subd8_3_326 : subd8_3 [2, -1, -5] = true := by decide +kernel
theorem subd8_3_327 : subd8_3 [2, -1, -4] = true := by decide +kernel
theorem subd8_3_328 : subd8_3 [2, -1, -3] = true := by decide +kernel
theorem subd8_3_329 : subd8_3 [2, -1, -2] = true := by decide +kernel
theorem subd8_3_330 : subd8_3 [2, -1, -1] = true := by decide +kernel
theorem subd8_3_331 : subd8_3 [2, -1, 0] = true := by decide +kernel
theorem subd8_3_332 : subd8_3 [2, -1, 1] = true := by decide +kernel
theorem subd8_3_333 : subd8_3 [2, -1, 2] = true := by decide +kernel
theorem subd8_3_334 : subd8_3 [2, -1, 3] = true := by decide +kernel
theorem subd8_3_335 : subd8_3 [2, -1, 4] = true := by decide +kernel
theorem subd8_3_336 : subd8_3 [2, -1, 5] = true := by decide +kernel
theorem subd8_3_337 : subd8_3 [2, 0, -6] = true := by decide +kernel
theorem subd8_3_338 : subd8_3 [2, 0, -5] = true := by decide +kernel
theorem subd8_3_339 : subd8_3 [2, 0, -4] = true := by decide +kernel
theorem subd8_3_340 : subd8_3 [2, 0, -3] = true := by decide +kernel
theorem subd8_3_341 : subd8_3 [2, 0, -2] = true := by decide +kernel
theorem subd8_3_342 : subd8_3 [2, 0, -1] = true := by decide +kernel
theorem subd8_3_343 : subd8_3 [2, 0, 0] = true := by decide +kernel
theorem subd8_3_344 : subd8_3 [2, 0, 1] = true := by decide +kernel
theorem subd8_3_345 : subd8_3 [2, 0, 2] = true := by decide +kernel
theorem subd8_3_346 : subd8_3 [2, 0, 3] = true := by decide +kernel
theorem subd8_3_347 : subd8_3 [2, 0, 4] = true := by decide +kernel
theorem subd8_3_348 : subd8_3 [2, 0, 5] = true := by decide +kernel
theorem subd8_3_349 : subd8_3 [2, 0, 6] = true := by decide +kernel
theorem subd8_3_350 : subd8_3 [2, 1, -6] = true := by decide +kernel
theorem subd8_3_351 : subd8_3 [2, 1, -5] = true := by decide +kernel
theorem sbd8_3_10 : ∀ q ∈ blkd8_3_10, subd8_3 q = true := by
  unfold blkd8_3_10
  exact List.forall_mem_cons.2 ⟨subd8_3_320, List.forall_mem_cons.2 ⟨subd8_3_321, List.forall_mem_cons.2 ⟨subd8_3_322, List.forall_mem_cons.2 ⟨subd8_3_323, List.forall_mem_cons.2 ⟨subd8_3_324, List.forall_mem_cons.2 ⟨subd8_3_325, List.forall_mem_cons.2 ⟨subd8_3_326, List.forall_mem_cons.2 ⟨subd8_3_327, List.forall_mem_cons.2 ⟨subd8_3_328, List.forall_mem_cons.2 ⟨subd8_3_329, List.forall_mem_cons.2 ⟨subd8_3_330, List.forall_mem_cons.2 ⟨subd8_3_331, List.forall_mem_cons.2 ⟨subd8_3_332, List.forall_mem_cons.2 ⟨subd8_3_333, List.forall_mem_cons.2 ⟨subd8_3_334, List.forall_mem_cons.2 ⟨subd8_3_335, List.forall_mem_cons.2 ⟨subd8_3_336, List.forall_mem_cons.2 ⟨subd8_3_337, List.forall_mem_cons.2 ⟨subd8_3_338, List.forall_mem_cons.2 ⟨subd8_3_339, List.forall_mem_cons.2 ⟨subd8_3_340, List.forall_mem_cons.2 ⟨subd8_3_341, List.forall_mem_cons.2 ⟨subd8_3_342, List.forall_mem_cons.2 ⟨subd8_3_343, List.forall_mem_cons.2 ⟨subd8_3_344, List.forall_mem_cons.2 ⟨subd8_3_345, List.forall_mem_cons.2 ⟨subd8_3_346, List.forall_mem_cons.2 ⟨subd8_3_347, List.forall_mem_cons.2 ⟨subd8_3_348, List.forall_mem_cons.2 ⟨subd8_3_349, List.forall_mem_cons.2 ⟨subd8_3_350, List.forall_mem_cons.2 ⟨subd8_3_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_352 : subd8_3 [2, 1, -4] = true := by decide +kernel
theorem subd8_3_353 : subd8_3 [2, 1, -3] = true := by decide +kernel
theorem subd8_3_354 : subd8_3 [2, 1, -2] = true := by decide +kernel
theorem subd8_3_355 : subd8_3 [2, 1, -1] = true := by decide +kernel
theorem subd8_3_356 : subd8_3 [2, 1, 0] = true := by decide +kernel
theorem subd8_3_357 : subd8_3 [2, 1, 1] = true := by decide +kernel
theorem subd8_3_358 : subd8_3 [2, 1, 2] = true := by decide +kernel
theorem subd8_3_359 : subd8_3 [2, 1, 3] = true := by decide +kernel
theorem subd8_3_360 : subd8_3 [2, 1, 4] = true := by decide +kernel
theorem subd8_3_361 : subd8_3 [2, 1, 5] = true := by decide +kernel
theorem subd8_3_362 : subd8_3 [2, 1, 6] = true := by decide +kernel
theorem subd8_3_363 : subd8_3 [2, 2] = true := by decide +kernel
theorem subd8_3_364 : subd8_3 [2, 3] = true := by decide +kernel
theorem subd8_3_365 : subd8_3 [2, 4] = true := by decide +kernel
theorem subd8_3_366 : subd8_3 [2, 5] = true := by decide +kernel
theorem subd8_3_367 : subd8_3 [2, 6] = true := by decide +kernel
theorem subd8_3_368 : subd8_3 [3, -7] = true := by decide +kernel
theorem subd8_3_369 : subd8_3 [3, -6] = true := by decide +kernel
theorem subd8_3_370 : subd8_3 [3, -5] = true := by decide +kernel
theorem subd8_3_371 : subd8_3 [3, -4] = true := by decide +kernel
theorem subd8_3_372 : subd8_3 [3, -3] = true := by decide +kernel
theorem subd8_3_373 : subd8_3 [3, -2] = true := by decide +kernel
theorem subd8_3_374 : subd8_3 [3, -1] = true := by decide +kernel
theorem subd8_3_375 : subd8_3 [3, 0] = true := by decide +kernel
theorem subd8_3_376 : subd8_3 [3, 1] = true := by decide +kernel
theorem subd8_3_377 : subd8_3 [3, 2] = true := by decide +kernel
theorem subd8_3_378 : subd8_3 [3, 3] = true := by decide +kernel
theorem subd8_3_379 : subd8_3 [3, 4] = true := by decide +kernel
theorem subd8_3_380 : subd8_3 [3, 5] = true := by decide +kernel
theorem subd8_3_381 : subd8_3 [3, 6] = true := by decide +kernel
theorem subd8_3_382 : subd8_3 [4, -6] = true := by decide +kernel
theorem subd8_3_383 : subd8_3 [4, -5] = true := by decide +kernel
theorem sbd8_3_11 : ∀ q ∈ blkd8_3_11, subd8_3 q = true := by
  unfold blkd8_3_11
  exact List.forall_mem_cons.2 ⟨subd8_3_352, List.forall_mem_cons.2 ⟨subd8_3_353, List.forall_mem_cons.2 ⟨subd8_3_354, List.forall_mem_cons.2 ⟨subd8_3_355, List.forall_mem_cons.2 ⟨subd8_3_356, List.forall_mem_cons.2 ⟨subd8_3_357, List.forall_mem_cons.2 ⟨subd8_3_358, List.forall_mem_cons.2 ⟨subd8_3_359, List.forall_mem_cons.2 ⟨subd8_3_360, List.forall_mem_cons.2 ⟨subd8_3_361, List.forall_mem_cons.2 ⟨subd8_3_362, List.forall_mem_cons.2 ⟨subd8_3_363, List.forall_mem_cons.2 ⟨subd8_3_364, List.forall_mem_cons.2 ⟨subd8_3_365, List.forall_mem_cons.2 ⟨subd8_3_366, List.forall_mem_cons.2 ⟨subd8_3_367, List.forall_mem_cons.2 ⟨subd8_3_368, List.forall_mem_cons.2 ⟨subd8_3_369, List.forall_mem_cons.2 ⟨subd8_3_370, List.forall_mem_cons.2 ⟨subd8_3_371, List.forall_mem_cons.2 ⟨subd8_3_372, List.forall_mem_cons.2 ⟨subd8_3_373, List.forall_mem_cons.2 ⟨subd8_3_374, List.forall_mem_cons.2 ⟨subd8_3_375, List.forall_mem_cons.2 ⟨subd8_3_376, List.forall_mem_cons.2 ⟨subd8_3_377, List.forall_mem_cons.2 ⟨subd8_3_378, List.forall_mem_cons.2 ⟨subd8_3_379, List.forall_mem_cons.2 ⟨subd8_3_380, List.forall_mem_cons.2 ⟨subd8_3_381, List.forall_mem_cons.2 ⟨subd8_3_382, List.forall_mem_cons.2 ⟨subd8_3_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_384 : subd8_3 [4, -4] = true := by decide +kernel
theorem subd8_3_385 : subd8_3 [4, -3] = true := by decide +kernel
theorem subd8_3_386 : subd8_3 [4, -2] = true := by decide +kernel
theorem subd8_3_387 : subd8_3 [4, -1] = true := by decide +kernel
theorem subd8_3_388 : subd8_3 [4, 0] = true := by decide +kernel
theorem subd8_3_389 : subd8_3 [4, 1] = true := by decide +kernel
theorem subd8_3_390 : subd8_3 [4, 2] = true := by decide +kernel
theorem subd8_3_391 : subd8_3 [4, 3] = true := by decide +kernel
theorem subd8_3_392 : subd8_3 [4, 4] = true := by decide +kernel
theorem subd8_3_393 : subd8_3 [4, 5] = true := by decide +kernel
theorem subd8_3_394 : subd8_3 [5, -5] = true := by decide +kernel
theorem subd8_3_395 : subd8_3 [5, -4] = true := by decide +kernel
theorem subd8_3_396 : subd8_3 [5, -3] = true := by decide +kernel
theorem subd8_3_397 : subd8_3 [5, -2] = true := by decide +kernel
theorem subd8_3_398 : subd8_3 [5, -1] = true := by decide +kernel
theorem subd8_3_399 : subd8_3 [5, 0] = true := by decide +kernel
theorem subd8_3_400 : subd8_3 [5, 1] = true := by decide +kernel
theorem subd8_3_401 : subd8_3 [5, 2] = true := by decide +kernel
theorem subd8_3_402 : subd8_3 [5, 3] = true := by decide +kernel
theorem subd8_3_403 : subd8_3 [5, 4] = true := by decide +kernel
theorem subd8_3_404 : subd8_3 [6] = true := by decide +kernel
theorem sbd8_3_12 : ∀ q ∈ blkd8_3_12, subd8_3 q = true := by
  unfold blkd8_3_12
  exact List.forall_mem_cons.2 ⟨subd8_3_384, List.forall_mem_cons.2 ⟨subd8_3_385, List.forall_mem_cons.2 ⟨subd8_3_386, List.forall_mem_cons.2 ⟨subd8_3_387, List.forall_mem_cons.2 ⟨subd8_3_388, List.forall_mem_cons.2 ⟨subd8_3_389, List.forall_mem_cons.2 ⟨subd8_3_390, List.forall_mem_cons.2 ⟨subd8_3_391, List.forall_mem_cons.2 ⟨subd8_3_392, List.forall_mem_cons.2 ⟨subd8_3_393, List.forall_mem_cons.2 ⟨subd8_3_394, List.forall_mem_cons.2 ⟨subd8_3_395, List.forall_mem_cons.2 ⟨subd8_3_396, List.forall_mem_cons.2 ⟨subd8_3_397, List.forall_mem_cons.2 ⟨subd8_3_398, List.forall_mem_cons.2 ⟨subd8_3_399, List.forall_mem_cons.2 ⟨subd8_3_400, List.forall_mem_cons.2 ⟨subd8_3_401, List.forall_mem_cons.2 ⟨subd8_3_402, List.forall_mem_cons.2 ⟨subd8_3_403, List.forall_mem_cons.2 ⟨subd8_3_404, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_0 : ldCheck G d9_0.U d9_0.ms ldd9_0 = true := by decide +kernel
theorem pre_okd9_0 : subPre G cell9 d9_0 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C077
