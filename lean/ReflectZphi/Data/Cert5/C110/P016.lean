import ReflectZphi.Data.Cert5.C110.Base

namespace ReflectZphi.Data.Cert5.C110

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_4_224 : subd7_4 [0, -3, -3] = true := by decide +kernel
theorem subd7_4_225 : subd7_4 [0, -3, -2] = true := by decide +kernel
theorem subd7_4_226 : subd7_4 [0, -3, -1] = true := by decide +kernel
theorem subd7_4_227 : subd7_4 [0, -3, 0] = true := by decide +kernel
theorem subd7_4_228 : subd7_4 [0, -3, 1] = true := by decide +kernel
theorem subd7_4_229 : subd7_4 [0, -3, 2] = true := by decide +kernel
theorem subd7_4_230 : subd7_4 [0, -3, 3] = true := by decide +kernel
theorem subd7_4_231 : subd7_4 [0, -3, 4] = true := by decide +kernel
theorem subd7_4_232 : subd7_4 [0, -3, 5] = true := by decide +kernel
theorem subd7_4_233 : subd7_4 [0, -2, -8] = true := by decide +kernel
theorem subd7_4_234 : subd7_4 [0, -2, -7] = true := by decide +kernel
theorem subd7_4_235 : subd7_4 [0, -2, -6] = true := by decide +kernel
theorem subd7_4_236 : subd7_4 [0, -2, -5] = true := by decide +kernel
theorem subd7_4_237 : subd7_4 [0, -2, -4] = true := by decide +kernel
theorem subd7_4_238 : subd7_4 [0, -2, -3] = true := by decide +kernel
theorem subd7_4_239 : subd7_4 [0, -2, -2] = true := by decide +kernel
theorem subd7_4_240 : subd7_4 [0, -2, -1] = true := by decide +kernel
theorem subd7_4_241 : subd7_4 [0, -2, 0] = true := by decide +kernel
theorem subd7_4_242 : subd7_4 [0, -2, 1] = true := by decide +kernel
theorem subd7_4_243 : subd7_4 [0, -2, 2] = true := by decide +kernel
theorem subd7_4_244 : subd7_4 [0, -2, 3] = true := by decide +kernel
theorem subd7_4_245 : subd7_4 [0, -2, 4] = true := by decide +kernel
theorem subd7_4_246 : subd7_4 [0, -2, 5] = true := by decide +kernel
theorem subd7_4_247 : subd7_4 [0, -1, -7] = true := by decide +kernel
theorem subd7_4_248 : subd7_4 [0, -1, -6] = true := by decide +kernel
theorem subd7_4_249 : subd7_4 [0, -1, -5] = true := by decide +kernel
theorem subd7_4_250 : subd7_4 [0, -1, -4] = true := by decide +kernel
theorem subd7_4_251 : subd7_4 [0, -1, -3] = true := by decide +kernel
theorem subd7_4_252 : subd7_4 [0, -1, -2] = true := by decide +kernel
theorem subd7_4_253 : subd7_4 [0, -1, -1] = true := by decide +kernel
theorem subd7_4_254 : subd7_4 [0, -1, 0] = true := by decide +kernel
theorem subd7_4_255 : subd7_4 [0, -1, 1] = true := by decide +kernel
theorem sbd7_4_7 : ∀ q ∈ blkd7_4_7, subd7_4 q = true := by
  unfold blkd7_4_7
  exact List.forall_mem_cons.2 ⟨subd7_4_224, List.forall_mem_cons.2 ⟨subd7_4_225, List.forall_mem_cons.2 ⟨subd7_4_226, List.forall_mem_cons.2 ⟨subd7_4_227, List.forall_mem_cons.2 ⟨subd7_4_228, List.forall_mem_cons.2 ⟨subd7_4_229, List.forall_mem_cons.2 ⟨subd7_4_230, List.forall_mem_cons.2 ⟨subd7_4_231, List.forall_mem_cons.2 ⟨subd7_4_232, List.forall_mem_cons.2 ⟨subd7_4_233, List.forall_mem_cons.2 ⟨subd7_4_234, List.forall_mem_cons.2 ⟨subd7_4_235, List.forall_mem_cons.2 ⟨subd7_4_236, List.forall_mem_cons.2 ⟨subd7_4_237, List.forall_mem_cons.2 ⟨subd7_4_238, List.forall_mem_cons.2 ⟨subd7_4_239, List.forall_mem_cons.2 ⟨subd7_4_240, List.forall_mem_cons.2 ⟨subd7_4_241, List.forall_mem_cons.2 ⟨subd7_4_242, List.forall_mem_cons.2 ⟨subd7_4_243, List.forall_mem_cons.2 ⟨subd7_4_244, List.forall_mem_cons.2 ⟨subd7_4_245, List.forall_mem_cons.2 ⟨subd7_4_246, List.forall_mem_cons.2 ⟨subd7_4_247, List.forall_mem_cons.2 ⟨subd7_4_248, List.forall_mem_cons.2 ⟨subd7_4_249, List.forall_mem_cons.2 ⟨subd7_4_250, List.forall_mem_cons.2 ⟨subd7_4_251, List.forall_mem_cons.2 ⟨subd7_4_252, List.forall_mem_cons.2 ⟨subd7_4_253, List.forall_mem_cons.2 ⟨subd7_4_254, List.forall_mem_cons.2 ⟨subd7_4_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_4_256 : subd7_4 [0, -1, 2] = true := by decide +kernel
theorem subd7_4_257 : subd7_4 [0, -1, 3] = true := by decide +kernel
theorem subd7_4_258 : subd7_4 [0, -1, 4] = true := by decide +kernel
theorem subd7_4_259 : subd7_4 [0, -1, 5] = true := by decide +kernel
theorem subd7_4_260 : subd7_4 [0, -1, 6] = true := by decide +kernel
theorem subd7_4_261 : subd7_4 [0, 0, -7] = true := by decide +kernel
theorem subd7_4_262 : subd7_4 [0, 0, -6] = true := by decide +kernel
theorem subd7_4_263 : subd7_4 [0, 0, -5] = true := by decide +kernel
theorem subd7_4_264 : subd7_4 [0, 0, -4] = true := by decide +kernel
theorem subd7_4_265 : subd7_4 [0, 0, -3] = true := by decide +kernel
theorem subd7_4_266 : subd7_4 [0, 0, -2] = true := by decide +kernel
theorem subd7_4_267 : subd7_4 [0, 0, -1] = true := by decide +kernel
theorem subd7_4_268 : subd7_4 [0, 0, 0] = true := by decide +kernel
theorem subd7_4_269 : subd7_4 [0, 0, 1] = true := by decide +kernel
theorem subd7_4_270 : subd7_4 [0, 0, 2] = true := by decide +kernel
theorem subd7_4_271 : subd7_4 [0, 0, 3] = true := by decide +kernel
theorem subd7_4_272 : subd7_4 [0, 0, 4] = true := by decide +kernel
theorem subd7_4_273 : subd7_4 [0, 0, 5] = true := by decide +kernel
theorem subd7_4_274 : subd7_4 [0, 0, 6] = true := by decide +kernel
theorem subd7_4_275 : subd7_4 [0, 1, -7] = true := by decide +kernel
theorem subd7_4_276 : subd7_4 [0, 1, -6] = true := by decide +kernel
theorem subd7_4_277 : subd7_4 [0, 1, -5] = true := by decide +kernel
theorem subd7_4_278 : subd7_4 [0, 1, -4] = true := by decide +kernel
theorem subd7_4_279 : subd7_4 [0, 1, -3] = true := by decide +kernel
theorem subd7_4_280 : subd7_4 [0, 1, -2] = true := by decide +kernel
theorem subd7_4_281 : subd7_4 [0, 1, -1] = true := by decide +kernel
theorem subd7_4_282 : subd7_4 [0, 1, 0] = true := by decide +kernel
theorem subd7_4_283 : subd7_4 [0, 1, 1] = true := by decide +kernel
theorem subd7_4_284 : subd7_4 [0, 1, 2] = true := by decide +kernel
theorem subd7_4_285 : subd7_4 [0, 1, 3] = true := by decide +kernel
theorem subd7_4_286 : subd7_4 [0, 1, 4] = true := by decide +kernel
theorem subd7_4_287 : subd7_4 [0, 1, 5] = true := by decide +kernel
theorem sbd7_4_8 : ∀ q ∈ blkd7_4_8, subd7_4 q = true := by
  unfold blkd7_4_8
  exact List.forall_mem_cons.2 ⟨subd7_4_256, List.forall_mem_cons.2 ⟨subd7_4_257, List.forall_mem_cons.2 ⟨subd7_4_258, List.forall_mem_cons.2 ⟨subd7_4_259, List.forall_mem_cons.2 ⟨subd7_4_260, List.forall_mem_cons.2 ⟨subd7_4_261, List.forall_mem_cons.2 ⟨subd7_4_262, List.forall_mem_cons.2 ⟨subd7_4_263, List.forall_mem_cons.2 ⟨subd7_4_264, List.forall_mem_cons.2 ⟨subd7_4_265, List.forall_mem_cons.2 ⟨subd7_4_266, List.forall_mem_cons.2 ⟨subd7_4_267, List.forall_mem_cons.2 ⟨subd7_4_268, List.forall_mem_cons.2 ⟨subd7_4_269, List.forall_mem_cons.2 ⟨subd7_4_270, List.forall_mem_cons.2 ⟨subd7_4_271, List.forall_mem_cons.2 ⟨subd7_4_272, List.forall_mem_cons.2 ⟨subd7_4_273, List.forall_mem_cons.2 ⟨subd7_4_274, List.forall_mem_cons.2 ⟨subd7_4_275, List.forall_mem_cons.2 ⟨subd7_4_276, List.forall_mem_cons.2 ⟨subd7_4_277, List.forall_mem_cons.2 ⟨subd7_4_278, List.forall_mem_cons.2 ⟨subd7_4_279, List.forall_mem_cons.2 ⟨subd7_4_280, List.forall_mem_cons.2 ⟨subd7_4_281, List.forall_mem_cons.2 ⟨subd7_4_282, List.forall_mem_cons.2 ⟨subd7_4_283, List.forall_mem_cons.2 ⟨subd7_4_284, List.forall_mem_cons.2 ⟨subd7_4_285, List.forall_mem_cons.2 ⟨subd7_4_286, List.forall_mem_cons.2 ⟨subd7_4_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_4_288 : subd7_4 [0, 1, 6] = true := by decide +kernel
theorem subd7_4_289 : subd7_4 [0, 2, -6] = true := by decide +kernel
theorem subd7_4_290 : subd7_4 [0, 2, -5] = true := by decide +kernel
theorem subd7_4_291 : subd7_4 [0, 2, -4] = true := by decide +kernel
theorem subd7_4_292 : subd7_4 [0, 2, -3] = true := by decide +kernel
theorem subd7_4_293 : subd7_4 [0, 2, -2] = true := by decide +kernel
theorem subd7_4_294 : subd7_4 [0, 2, -1] = true := by decide +kernel
theorem subd7_4_295 : subd7_4 [0, 2, 0] = true := by decide +kernel
theorem subd7_4_296 : subd7_4 [0, 2, 1] = true := by decide +kernel
theorem subd7_4_297 : subd7_4 [0, 2, 2] = true := by decide +kernel
theorem subd7_4_298 : subd7_4 [0, 2, 3] = true := by decide +kernel
theorem subd7_4_299 : subd7_4 [0, 2, 4] = true := by decide +kernel
theorem subd7_4_300 : subd7_4 [0, 2, 5] = true := by decide +kernel
theorem subd7_4_301 : subd7_4 [0, 2, 6] = true := by decide +kernel
theorem subd7_4_302 : subd7_4 [0, 2, 7] = true := by decide +kernel
theorem subd7_4_303 : subd7_4 [0, 3, -6] = true := by decide +kernel
theorem subd7_4_304 : subd7_4 [0, 3, -5] = true := by decide +kernel
theorem subd7_4_305 : subd7_4 [0, 3, -4] = true := by decide +kernel
theorem subd7_4_306 : subd7_4 [0, 3, -3] = true := by decide +kernel
theorem subd7_4_307 : subd7_4 [0, 3, -2] = true := by decide +kernel
theorem subd7_4_308 : subd7_4 [0, 3, -1] = true := by decide +kernel
theorem subd7_4_309 : subd7_4 [0, 3, 0] = true := by decide +kernel
theorem subd7_4_310 : subd7_4 [0, 3, 1] = true := by decide +kernel
theorem subd7_4_311 : subd7_4 [0, 3, 2] = true := by decide +kernel
theorem subd7_4_312 : subd7_4 [0, 3, 3] = true := by decide +kernel
theorem subd7_4_313 : subd7_4 [0, 3, 4] = true := by decide +kernel
theorem subd7_4_314 : subd7_4 [0, 3, 5] = true := by decide +kernel
theorem subd7_4_315 : subd7_4 [0, 3, 6] = true := by decide +kernel
theorem subd7_4_316 : subd7_4 [0, 3, 7] = true := by decide +kernel
theorem subd7_4_317 : subd7_4 [0, 4] = true := by decide +kernel
theorem subd7_4_318 : subd7_4 [0, 5] = true := by decide +kernel
theorem subd7_4_319 : subd7_4 [0, 6] = true := by decide +kernel
theorem sbd7_4_9 : ∀ q ∈ blkd7_4_9, subd7_4 q = true := by
  unfold blkd7_4_9
  exact List.forall_mem_cons.2 ⟨subd7_4_288, List.forall_mem_cons.2 ⟨subd7_4_289, List.forall_mem_cons.2 ⟨subd7_4_290, List.forall_mem_cons.2 ⟨subd7_4_291, List.forall_mem_cons.2 ⟨subd7_4_292, List.forall_mem_cons.2 ⟨subd7_4_293, List.forall_mem_cons.2 ⟨subd7_4_294, List.forall_mem_cons.2 ⟨subd7_4_295, List.forall_mem_cons.2 ⟨subd7_4_296, List.forall_mem_cons.2 ⟨subd7_4_297, List.forall_mem_cons.2 ⟨subd7_4_298, List.forall_mem_cons.2 ⟨subd7_4_299, List.forall_mem_cons.2 ⟨subd7_4_300, List.forall_mem_cons.2 ⟨subd7_4_301, List.forall_mem_cons.2 ⟨subd7_4_302, List.forall_mem_cons.2 ⟨subd7_4_303, List.forall_mem_cons.2 ⟨subd7_4_304, List.forall_mem_cons.2 ⟨subd7_4_305, List.forall_mem_cons.2 ⟨subd7_4_306, List.forall_mem_cons.2 ⟨subd7_4_307, List.forall_mem_cons.2 ⟨subd7_4_308, List.forall_mem_cons.2 ⟨subd7_4_309, List.forall_mem_cons.2 ⟨subd7_4_310, List.forall_mem_cons.2 ⟨subd7_4_311, List.forall_mem_cons.2 ⟨subd7_4_312, List.forall_mem_cons.2 ⟨subd7_4_313, List.forall_mem_cons.2 ⟨subd7_4_314, List.forall_mem_cons.2 ⟨subd7_4_315, List.forall_mem_cons.2 ⟨subd7_4_316, List.forall_mem_cons.2 ⟨subd7_4_317, List.forall_mem_cons.2 ⟨subd7_4_318, List.forall_mem_cons.2 ⟨subd7_4_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_4_320 : subd7_4 [0, 7] = true := by decide +kernel
theorem subd7_4_321 : subd7_4 [1, -9] = true := by decide +kernel
theorem subd7_4_322 : subd7_4 [1, -8] = true := by decide +kernel
theorem subd7_4_323 : subd7_4 [1, -7] = true := by decide +kernel
theorem subd7_4_324 : subd7_4 [1, -6] = true := by decide +kernel
theorem subd7_4_325 : subd7_4 [1, -5] = true := by decide +kernel
theorem subd7_4_326 : subd7_4 [1, -4] = true := by decide +kernel
theorem subd7_4_327 : subd7_4 [1, -3, -8] = true := by decide +kernel
theorem subd7_4_328 : subd7_4 [1, -3, -7] = true := by decide +kernel
theorem subd7_4_329 : subd7_4 [1, -3, -6] = true := by decide +kernel
theorem subd7_4_330 : subd7_4 [1, -3, -5] = true := by decide +kernel
theorem subd7_4_331 : subd7_4 [1, -3, -4] = true := by decide +kernel
theorem subd7_4_332 : subd7_4 [1, -3, -3] = true := by decide +kernel
theorem subd7_4_333 : subd7_4 [1, -3, -2] = true := by decide +kernel
theorem subd7_4_334 : subd7_4 [1, -3, -1] = true := by decide +kernel
theorem subd7_4_335 : subd7_4 [1, -3, 0] = true := by decide +kernel
theorem subd7_4_336 : subd7_4 [1, -3, 1] = true := by decide +kernel
theorem subd7_4_337 : subd7_4 [1, -3, 2] = true := by decide +kernel
theorem subd7_4_338 : subd7_4 [1, -3, 3] = true := by decide +kernel
theorem subd7_4_339 : subd7_4 [1, -3, 4] = true := by decide +kernel
theorem subd7_4_340 : subd7_4 [1, -3, 5] = true := by decide +kernel
theorem subd7_4_341 : subd7_4 [1, -2, -8] = true := by decide +kernel
theorem subd7_4_342 : subd7_4 [1, -2, -7] = true := by decide +kernel
theorem subd7_4_343 : subd7_4 [1, -2, -6] = true := by decide +kernel
theorem subd7_4_344 : subd7_4 [1, -2, -5] = true := by decide +kernel
theorem subd7_4_345 : subd7_4 [1, -2, -4] = true := by decide +kernel
theorem subd7_4_346 : subd7_4 [1, -2, -3] = true := by decide +kernel
theorem subd7_4_347 : subd7_4 [1, -2, -2] = true := by decide +kernel
theorem subd7_4_348 : subd7_4 [1, -2, -1] = true := by decide +kernel
theorem subd7_4_349 : subd7_4 [1, -2, 0] = true := by decide +kernel
theorem subd7_4_350 : subd7_4 [1, -2, 1] = true := by decide +kernel
theorem subd7_4_351 : subd7_4 [1, -2, 2] = true := by decide +kernel
theorem sbd7_4_10 : ∀ q ∈ blkd7_4_10, subd7_4 q = true := by
  unfold blkd7_4_10
  exact List.forall_mem_cons.2 ⟨subd7_4_320, List.forall_mem_cons.2 ⟨subd7_4_321, List.forall_mem_cons.2 ⟨subd7_4_322, List.forall_mem_cons.2 ⟨subd7_4_323, List.forall_mem_cons.2 ⟨subd7_4_324, List.forall_mem_cons.2 ⟨subd7_4_325, List.forall_mem_cons.2 ⟨subd7_4_326, List.forall_mem_cons.2 ⟨subd7_4_327, List.forall_mem_cons.2 ⟨subd7_4_328, List.forall_mem_cons.2 ⟨subd7_4_329, List.forall_mem_cons.2 ⟨subd7_4_330, List.forall_mem_cons.2 ⟨subd7_4_331, List.forall_mem_cons.2 ⟨subd7_4_332, List.forall_mem_cons.2 ⟨subd7_4_333, List.forall_mem_cons.2 ⟨subd7_4_334, List.forall_mem_cons.2 ⟨subd7_4_335, List.forall_mem_cons.2 ⟨subd7_4_336, List.forall_mem_cons.2 ⟨subd7_4_337, List.forall_mem_cons.2 ⟨subd7_4_338, List.forall_mem_cons.2 ⟨subd7_4_339, List.forall_mem_cons.2 ⟨subd7_4_340, List.forall_mem_cons.2 ⟨subd7_4_341, List.forall_mem_cons.2 ⟨subd7_4_342, List.forall_mem_cons.2 ⟨subd7_4_343, List.forall_mem_cons.2 ⟨subd7_4_344, List.forall_mem_cons.2 ⟨subd7_4_345, List.forall_mem_cons.2 ⟨subd7_4_346, List.forall_mem_cons.2 ⟨subd7_4_347, List.forall_mem_cons.2 ⟨subd7_4_348, List.forall_mem_cons.2 ⟨subd7_4_349, List.forall_mem_cons.2 ⟨subd7_4_350, List.forall_mem_cons.2 ⟨subd7_4_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_4_352 : subd7_4 [1, -2, 3] = true := by decide +kernel
theorem subd7_4_353 : subd7_4 [1, -2, 4] = true := by decide +kernel
theorem subd7_4_354 : subd7_4 [1, -2, 5] = true := by decide +kernel
theorem subd7_4_355 : subd7_4 [1, -1, -8] = true := by decide +kernel
theorem subd7_4_356 : subd7_4 [1, -1, -7] = true := by decide +kernel
theorem subd7_4_357 : subd7_4 [1, -1, -6] = true := by decide +kernel
theorem subd7_4_358 : subd7_4 [1, -1, -5] = true := by decide +kernel
theorem subd7_4_359 : subd7_4 [1, -1, -4] = true := by decide +kernel
theorem subd7_4_360 : subd7_4 [1, -1, -3] = true := by decide +kernel
theorem subd7_4_361 : subd7_4 [1, -1, -2] = true := by decide +kernel
theorem subd7_4_362 : subd7_4 [1, -1, -1] = true := by decide +kernel
theorem subd7_4_363 : subd7_4 [1, -1, 0] = true := by decide +kernel
theorem subd7_4_364 : subd7_4 [1, -1, 1] = true := by decide +kernel
theorem subd7_4_365 : subd7_4 [1, -1, 2] = true := by decide +kernel
theorem subd7_4_366 : subd7_4 [1, -1, 3] = true := by decide +kernel
theorem subd7_4_367 : subd7_4 [1, -1, 4] = true := by decide +kernel
theorem subd7_4_368 : subd7_4 [1, -1, 5] = true := by decide +kernel
theorem subd7_4_369 : subd7_4 [1, -1, 6] = true := by decide +kernel
theorem subd7_4_370 : subd7_4 [1, 0, -7] = true := by decide +kernel
theorem subd7_4_371 : subd7_4 [1, 0, -6] = true := by decide +kernel
theorem subd7_4_372 : subd7_4 [1, 0, -5] = true := by decide +kernel
theorem subd7_4_373 : subd7_4 [1, 0, -4] = true := by decide +kernel
theorem subd7_4_374 : subd7_4 [1, 0, -3] = true := by decide +kernel
theorem subd7_4_375 : subd7_4 [1, 0, -2] = true := by decide +kernel
theorem subd7_4_376 : subd7_4 [1, 0, -1] = true := by decide +kernel
theorem subd7_4_377 : subd7_4 [1, 0, 0] = true := by decide +kernel
theorem subd7_4_378 : subd7_4 [1, 0, 1] = true := by decide +kernel
theorem subd7_4_379 : subd7_4 [1, 0, 2] = true := by decide +kernel
theorem subd7_4_380 : subd7_4 [1, 0, 3] = true := by decide +kernel
theorem subd7_4_381 : subd7_4 [1, 0, 4] = true := by decide +kernel
theorem subd7_4_382 : subd7_4 [1, 0, 5] = true := by decide +kernel
theorem subd7_4_383 : subd7_4 [1, 0, 6] = true := by decide +kernel
theorem sbd7_4_11 : ∀ q ∈ blkd7_4_11, subd7_4 q = true := by
  unfold blkd7_4_11
  exact List.forall_mem_cons.2 ⟨subd7_4_352, List.forall_mem_cons.2 ⟨subd7_4_353, List.forall_mem_cons.2 ⟨subd7_4_354, List.forall_mem_cons.2 ⟨subd7_4_355, List.forall_mem_cons.2 ⟨subd7_4_356, List.forall_mem_cons.2 ⟨subd7_4_357, List.forall_mem_cons.2 ⟨subd7_4_358, List.forall_mem_cons.2 ⟨subd7_4_359, List.forall_mem_cons.2 ⟨subd7_4_360, List.forall_mem_cons.2 ⟨subd7_4_361, List.forall_mem_cons.2 ⟨subd7_4_362, List.forall_mem_cons.2 ⟨subd7_4_363, List.forall_mem_cons.2 ⟨subd7_4_364, List.forall_mem_cons.2 ⟨subd7_4_365, List.forall_mem_cons.2 ⟨subd7_4_366, List.forall_mem_cons.2 ⟨subd7_4_367, List.forall_mem_cons.2 ⟨subd7_4_368, List.forall_mem_cons.2 ⟨subd7_4_369, List.forall_mem_cons.2 ⟨subd7_4_370, List.forall_mem_cons.2 ⟨subd7_4_371, List.forall_mem_cons.2 ⟨subd7_4_372, List.forall_mem_cons.2 ⟨subd7_4_373, List.forall_mem_cons.2 ⟨subd7_4_374, List.forall_mem_cons.2 ⟨subd7_4_375, List.forall_mem_cons.2 ⟨subd7_4_376, List.forall_mem_cons.2 ⟨subd7_4_377, List.forall_mem_cons.2 ⟨subd7_4_378, List.forall_mem_cons.2 ⟨subd7_4_379, List.forall_mem_cons.2 ⟨subd7_4_380, List.forall_mem_cons.2 ⟨subd7_4_381, List.forall_mem_cons.2 ⟨subd7_4_382, List.forall_mem_cons.2 ⟨subd7_4_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_4_384 : subd7_4 [1, 1, -7] = true := by decide +kernel
theorem subd7_4_385 : subd7_4 [1, 1, -6] = true := by decide +kernel
theorem subd7_4_386 : subd7_4 [1, 1, -5] = true := by decide +kernel
theorem subd7_4_387 : subd7_4 [1, 1, -4] = true := by decide +kernel
theorem subd7_4_388 : subd7_4 [1, 1, -3] = true := by decide +kernel
theorem subd7_4_389 : subd7_4 [1, 1, -2] = true := by decide +kernel
theorem subd7_4_390 : subd7_4 [1, 1, -1] = true := by decide +kernel
theorem subd7_4_391 : subd7_4 [1, 1, 0] = true := by decide +kernel
theorem subd7_4_392 : subd7_4 [1, 1, 1] = true := by decide +kernel
theorem subd7_4_393 : subd7_4 [1, 1, 2] = true := by decide +kernel
theorem subd7_4_394 : subd7_4 [1, 1, 3] = true := by decide +kernel
theorem subd7_4_395 : subd7_4 [1, 1, 4] = true := by decide +kernel
theorem subd7_4_396 : subd7_4 [1, 1, 5] = true := by decide +kernel
theorem subd7_4_397 : subd7_4 [1, 1, 6] = true := by decide +kernel
theorem subd7_4_398 : subd7_4 [1, 2, -6] = true := by decide +kernel
theorem subd7_4_399 : subd7_4 [1, 2, -5] = true := by decide +kernel
theorem subd7_4_400 : subd7_4 [1, 2, -4] = true := by decide +kernel
theorem subd7_4_401 : subd7_4 [1, 2, -3] = true := by decide +kernel
theorem subd7_4_402 : subd7_4 [1, 2, -2] = true := by decide +kernel
theorem subd7_4_403 : subd7_4 [1, 2, -1] = true := by decide +kernel
theorem subd7_4_404 : subd7_4 [1, 2, 0] = true := by decide +kernel
theorem subd7_4_405 : subd7_4 [1, 2, 1] = true := by decide +kernel
theorem subd7_4_406 : subd7_4 [1, 2, 2] = true := by decide +kernel
theorem subd7_4_407 : subd7_4 [1, 2, 3] = true := by decide +kernel
theorem subd7_4_408 : subd7_4 [1, 2, 4] = true := by decide +kernel
theorem subd7_4_409 : subd7_4 [1, 2, 5] = true := by decide +kernel
theorem subd7_4_410 : subd7_4 [1, 2, 6] = true := by decide +kernel
theorem subd7_4_411 : subd7_4 [1, 3] = true := by decide +kernel
theorem subd7_4_412 : subd7_4 [1, 4] = true := by decide +kernel
theorem subd7_4_413 : subd7_4 [1, 5] = true := by decide +kernel
theorem subd7_4_414 : subd7_4 [1, 6] = true := by decide +kernel
theorem subd7_4_415 : subd7_4 [1, 7] = true := by decide +kernel
theorem sbd7_4_12 : ∀ q ∈ blkd7_4_12, subd7_4 q = true := by
  unfold blkd7_4_12
  exact List.forall_mem_cons.2 ⟨subd7_4_384, List.forall_mem_cons.2 ⟨subd7_4_385, List.forall_mem_cons.2 ⟨subd7_4_386, List.forall_mem_cons.2 ⟨subd7_4_387, List.forall_mem_cons.2 ⟨subd7_4_388, List.forall_mem_cons.2 ⟨subd7_4_389, List.forall_mem_cons.2 ⟨subd7_4_390, List.forall_mem_cons.2 ⟨subd7_4_391, List.forall_mem_cons.2 ⟨subd7_4_392, List.forall_mem_cons.2 ⟨subd7_4_393, List.forall_mem_cons.2 ⟨subd7_4_394, List.forall_mem_cons.2 ⟨subd7_4_395, List.forall_mem_cons.2 ⟨subd7_4_396, List.forall_mem_cons.2 ⟨subd7_4_397, List.forall_mem_cons.2 ⟨subd7_4_398, List.forall_mem_cons.2 ⟨subd7_4_399, List.forall_mem_cons.2 ⟨subd7_4_400, List.forall_mem_cons.2 ⟨subd7_4_401, List.forall_mem_cons.2 ⟨subd7_4_402, List.forall_mem_cons.2 ⟨subd7_4_403, List.forall_mem_cons.2 ⟨subd7_4_404, List.forall_mem_cons.2 ⟨subd7_4_405, List.forall_mem_cons.2 ⟨subd7_4_406, List.forall_mem_cons.2 ⟨subd7_4_407, List.forall_mem_cons.2 ⟨subd7_4_408, List.forall_mem_cons.2 ⟨subd7_4_409, List.forall_mem_cons.2 ⟨subd7_4_410, List.forall_mem_cons.2 ⟨subd7_4_411, List.forall_mem_cons.2 ⟨subd7_4_412, List.forall_mem_cons.2 ⟨subd7_4_413, List.forall_mem_cons.2 ⟨subd7_4_414, List.forall_mem_cons.2 ⟨subd7_4_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_4_416 : subd7_4 [2, -9] = true := by decide +kernel
theorem subd7_4_417 : subd7_4 [2, -8] = true := by decide +kernel
theorem subd7_4_418 : subd7_4 [2, -7] = true := by decide +kernel
theorem subd7_4_419 : subd7_4 [2, -6] = true := by decide +kernel
theorem subd7_4_420 : subd7_4 [2, -5] = true := by decide +kernel
theorem subd7_4_421 : subd7_4 [2, -4] = true := by decide +kernel
theorem subd7_4_422 : subd7_4 [2, -3] = true := by decide +kernel
theorem subd7_4_423 : subd7_4 [2, -2, -8] = true := by decide +kernel
theorem subd7_4_424 : subd7_4 [2, -2, -7] = true := by decide +kernel
theorem subd7_4_425 : subd7_4 [2, -2, -6] = true := by decide +kernel
theorem subd7_4_426 : subd7_4 [2, -2, -5] = true := by decide +kernel
theorem subd7_4_427 : subd7_4 [2, -2, -4] = true := by decide +kernel
theorem subd7_4_428 : subd7_4 [2, -2, -3] = true := by decide +kernel
theorem subd7_4_429 : subd7_4 [2, -2, -2] = true := by decide +kernel
theorem subd7_4_430 : subd7_4 [2, -2, -1] = true := by decide +kernel
theorem subd7_4_431 : subd7_4 [2, -2, 0] = true := by decide +kernel
theorem subd7_4_432 : subd7_4 [2, -2, 1] = true := by decide +kernel
theorem subd7_4_433 : subd7_4 [2, -2, 2] = true := by decide +kernel
theorem subd7_4_434 : subd7_4 [2, -2, 3] = true := by decide +kernel
theorem subd7_4_435 : subd7_4 [2, -2, 4] = true := by decide +kernel
theorem subd7_4_436 : subd7_4 [2, -2, 5] = true := by decide +kernel
theorem subd7_4_437 : subd7_4 [2, -1, -7] = true := by decide +kernel
theorem subd7_4_438 : subd7_4 [2, -1, -6] = true := by decide +kernel
theorem subd7_4_439 : subd7_4 [2, -1, -5] = true := by decide +kernel
theorem subd7_4_440 : subd7_4 [2, -1, -4] = true := by decide +kernel
theorem subd7_4_441 : subd7_4 [2, -1, -3] = true := by decide +kernel
theorem subd7_4_442 : subd7_4 [2, -1, -2] = true := by decide +kernel
theorem subd7_4_443 : subd7_4 [2, -1, -1] = true := by decide +kernel
theorem subd7_4_444 : subd7_4 [2, -1, 0] = true := by decide +kernel
theorem subd7_4_445 : subd7_4 [2, -1, 1] = true := by decide +kernel
theorem subd7_4_446 : subd7_4 [2, -1, 2] = true := by decide +kernel
theorem subd7_4_447 : subd7_4 [2, -1, 3] = true := by decide +kernel
theorem sbd7_4_13 : ∀ q ∈ blkd7_4_13, subd7_4 q = true := by
  unfold blkd7_4_13
  exact List.forall_mem_cons.2 ⟨subd7_4_416, List.forall_mem_cons.2 ⟨subd7_4_417, List.forall_mem_cons.2 ⟨subd7_4_418, List.forall_mem_cons.2 ⟨subd7_4_419, List.forall_mem_cons.2 ⟨subd7_4_420, List.forall_mem_cons.2 ⟨subd7_4_421, List.forall_mem_cons.2 ⟨subd7_4_422, List.forall_mem_cons.2 ⟨subd7_4_423, List.forall_mem_cons.2 ⟨subd7_4_424, List.forall_mem_cons.2 ⟨subd7_4_425, List.forall_mem_cons.2 ⟨subd7_4_426, List.forall_mem_cons.2 ⟨subd7_4_427, List.forall_mem_cons.2 ⟨subd7_4_428, List.forall_mem_cons.2 ⟨subd7_4_429, List.forall_mem_cons.2 ⟨subd7_4_430, List.forall_mem_cons.2 ⟨subd7_4_431, List.forall_mem_cons.2 ⟨subd7_4_432, List.forall_mem_cons.2 ⟨subd7_4_433, List.forall_mem_cons.2 ⟨subd7_4_434, List.forall_mem_cons.2 ⟨subd7_4_435, List.forall_mem_cons.2 ⟨subd7_4_436, List.forall_mem_cons.2 ⟨subd7_4_437, List.forall_mem_cons.2 ⟨subd7_4_438, List.forall_mem_cons.2 ⟨subd7_4_439, List.forall_mem_cons.2 ⟨subd7_4_440, List.forall_mem_cons.2 ⟨subd7_4_441, List.forall_mem_cons.2 ⟨subd7_4_442, List.forall_mem_cons.2 ⟨subd7_4_443, List.forall_mem_cons.2 ⟨subd7_4_444, List.forall_mem_cons.2 ⟨subd7_4_445, List.forall_mem_cons.2 ⟨subd7_4_446, List.forall_mem_cons.2 ⟨subd7_4_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_4_448 : subd7_4 [2, -1, 4] = true := by decide +kernel
theorem subd7_4_449 : subd7_4 [2, -1, 5] = true := by decide +kernel
theorem subd7_4_450 : subd7_4 [2, 0, -7] = true := by decide +kernel
theorem subd7_4_451 : subd7_4 [2, 0, -6] = true := by decide +kernel
theorem subd7_4_452 : subd7_4 [2, 0, -5] = true := by decide +kernel
theorem subd7_4_453 : subd7_4 [2, 0, -4] = true := by decide +kernel
theorem subd7_4_454 : subd7_4 [2, 0, -3] = true := by decide +kernel
theorem subd7_4_455 : subd7_4 [2, 0, -2] = true := by decide +kernel
theorem subd7_4_456 : subd7_4 [2, 0, -1] = true := by decide +kernel
theorem subd7_4_457 : subd7_4 [2, 0, 0] = true := by decide +kernel
theorem subd7_4_458 : subd7_4 [2, 0, 1] = true := by decide +kernel
theorem subd7_4_459 : subd7_4 [2, 0, 2] = true := by decide +kernel
theorem subd7_4_460 : subd7_4 [2, 0, 3] = true := by decide +kernel
theorem subd7_4_461 : subd7_4 [2, 0, 4] = true := by decide +kernel
theorem subd7_4_462 : subd7_4 [2, 0, 5] = true := by decide +kernel
theorem subd7_4_463 : subd7_4 [2, 0, 6] = true := by decide +kernel
theorem subd7_4_464 : subd7_4 [2, 1, -7] = true := by decide +kernel
theorem subd7_4_465 : subd7_4 [2, 1, -6] = true := by decide +kernel
theorem subd7_4_466 : subd7_4 [2, 1, -5] = true := by decide +kernel
theorem subd7_4_467 : subd7_4 [2, 1, -4] = true := by decide +kernel
theorem subd7_4_468 : subd7_4 [2, 1, -3] = true := by decide +kernel
theorem subd7_4_469 : subd7_4 [2, 1, -2] = true := by decide +kernel
theorem subd7_4_470 : subd7_4 [2, 1, -1] = true := by decide +kernel
theorem subd7_4_471 : subd7_4 [2, 1, 0] = true := by decide +kernel
theorem subd7_4_472 : subd7_4 [2, 1, 1] = true := by decide +kernel
theorem subd7_4_473 : subd7_4 [2, 1, 2] = true := by decide +kernel
theorem subd7_4_474 : subd7_4 [2, 1, 3] = true := by decide +kernel
theorem subd7_4_475 : subd7_4 [2, 1, 4] = true := by decide +kernel
theorem subd7_4_476 : subd7_4 [2, 1, 5] = true := by decide +kernel
theorem subd7_4_477 : subd7_4 [2, 1, 6] = true := by decide +kernel
theorem subd7_4_478 : subd7_4 [2, 2] = true := by decide +kernel
theorem subd7_4_479 : subd7_4 [2, 3] = true := by decide +kernel
theorem sbd7_4_14 : ∀ q ∈ blkd7_4_14, subd7_4 q = true := by
  unfold blkd7_4_14
  exact List.forall_mem_cons.2 ⟨subd7_4_448, List.forall_mem_cons.2 ⟨subd7_4_449, List.forall_mem_cons.2 ⟨subd7_4_450, List.forall_mem_cons.2 ⟨subd7_4_451, List.forall_mem_cons.2 ⟨subd7_4_452, List.forall_mem_cons.2 ⟨subd7_4_453, List.forall_mem_cons.2 ⟨subd7_4_454, List.forall_mem_cons.2 ⟨subd7_4_455, List.forall_mem_cons.2 ⟨subd7_4_456, List.forall_mem_cons.2 ⟨subd7_4_457, List.forall_mem_cons.2 ⟨subd7_4_458, List.forall_mem_cons.2 ⟨subd7_4_459, List.forall_mem_cons.2 ⟨subd7_4_460, List.forall_mem_cons.2 ⟨subd7_4_461, List.forall_mem_cons.2 ⟨subd7_4_462, List.forall_mem_cons.2 ⟨subd7_4_463, List.forall_mem_cons.2 ⟨subd7_4_464, List.forall_mem_cons.2 ⟨subd7_4_465, List.forall_mem_cons.2 ⟨subd7_4_466, List.forall_mem_cons.2 ⟨subd7_4_467, List.forall_mem_cons.2 ⟨subd7_4_468, List.forall_mem_cons.2 ⟨subd7_4_469, List.forall_mem_cons.2 ⟨subd7_4_470, List.forall_mem_cons.2 ⟨subd7_4_471, List.forall_mem_cons.2 ⟨subd7_4_472, List.forall_mem_cons.2 ⟨subd7_4_473, List.forall_mem_cons.2 ⟨subd7_4_474, List.forall_mem_cons.2 ⟨subd7_4_475, List.forall_mem_cons.2 ⟨subd7_4_476, List.forall_mem_cons.2 ⟨subd7_4_477, List.forall_mem_cons.2 ⟨subd7_4_478, List.forall_mem_cons.2 ⟨subd7_4_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_4_480 : subd7_4 [2, 4] = true := by decide +kernel
theorem subd7_4_481 : subd7_4 [2, 5] = true := by decide +kernel
theorem subd7_4_482 : subd7_4 [2, 6] = true := by decide +kernel
theorem subd7_4_483 : subd7_4 [3, -8] = true := by decide +kernel
theorem subd7_4_484 : subd7_4 [3, -7] = true := by decide +kernel
theorem subd7_4_485 : subd7_4 [3, -6] = true := by decide +kernel
theorem subd7_4_486 : subd7_4 [3, -5] = true := by decide +kernel
theorem subd7_4_487 : subd7_4 [3, -4] = true := by decide +kernel
theorem subd7_4_488 : subd7_4 [3, -3] = true := by decide +kernel
theorem subd7_4_489 : subd7_4 [3, -2] = true := by decide +kernel
theorem subd7_4_490 : subd7_4 [3, -1] = true := by decide +kernel
theorem subd7_4_491 : subd7_4 [3, 0] = true := by decide +kernel
theorem subd7_4_492 : subd7_4 [3, 1] = true := by decide +kernel
theorem subd7_4_493 : subd7_4 [3, 2] = true := by decide +kernel
theorem subd7_4_494 : subd7_4 [3, 3] = true := by decide +kernel
theorem subd7_4_495 : subd7_4 [3, 4] = true := by decide +kernel
theorem subd7_4_496 : subd7_4 [3, 5] = true := by decide +kernel
theorem subd7_4_497 : subd7_4 [3, 6] = true := by decide +kernel
theorem subd7_4_498 : subd7_4 [4, -8] = true := by decide +kernel
theorem subd7_4_499 : subd7_4 [4, -7] = true := by decide +kernel
theorem subd7_4_500 : subd7_4 [4, -6] = true := by decide +kernel
theorem subd7_4_501 : subd7_4 [4, -5] = true := by decide +kernel
theorem subd7_4_502 : subd7_4 [4, -4] = true := by decide +kernel
theorem subd7_4_503 : subd7_4 [4, -3] = true := by decide +kernel
theorem subd7_4_504 : subd7_4 [4, -2] = true := by decide +kernel
theorem subd7_4_505 : subd7_4 [4, -1] = true := by decide +kernel
theorem subd7_4_506 : subd7_4 [4, 0] = true := by decide +kernel
theorem subd7_4_507 : subd7_4 [4, 1] = true := by decide +kernel
theorem subd7_4_508 : subd7_4 [4, 2] = true := by decide +kernel
theorem subd7_4_509 : subd7_4 [4, 3] = true := by decide +kernel
theorem subd7_4_510 : subd7_4 [4, 4] = true := by decide +kernel
theorem subd7_4_511 : subd7_4 [4, 5] = true := by decide +kernel
theorem sbd7_4_15 : ∀ q ∈ blkd7_4_15, subd7_4 q = true := by
  unfold blkd7_4_15
  exact List.forall_mem_cons.2 ⟨subd7_4_480, List.forall_mem_cons.2 ⟨subd7_4_481, List.forall_mem_cons.2 ⟨subd7_4_482, List.forall_mem_cons.2 ⟨subd7_4_483, List.forall_mem_cons.2 ⟨subd7_4_484, List.forall_mem_cons.2 ⟨subd7_4_485, List.forall_mem_cons.2 ⟨subd7_4_486, List.forall_mem_cons.2 ⟨subd7_4_487, List.forall_mem_cons.2 ⟨subd7_4_488, List.forall_mem_cons.2 ⟨subd7_4_489, List.forall_mem_cons.2 ⟨subd7_4_490, List.forall_mem_cons.2 ⟨subd7_4_491, List.forall_mem_cons.2 ⟨subd7_4_492, List.forall_mem_cons.2 ⟨subd7_4_493, List.forall_mem_cons.2 ⟨subd7_4_494, List.forall_mem_cons.2 ⟨subd7_4_495, List.forall_mem_cons.2 ⟨subd7_4_496, List.forall_mem_cons.2 ⟨subd7_4_497, List.forall_mem_cons.2 ⟨subd7_4_498, List.forall_mem_cons.2 ⟨subd7_4_499, List.forall_mem_cons.2 ⟨subd7_4_500, List.forall_mem_cons.2 ⟨subd7_4_501, List.forall_mem_cons.2 ⟨subd7_4_502, List.forall_mem_cons.2 ⟨subd7_4_503, List.forall_mem_cons.2 ⟨subd7_4_504, List.forall_mem_cons.2 ⟨subd7_4_505, List.forall_mem_cons.2 ⟨subd7_4_506, List.forall_mem_cons.2 ⟨subd7_4_507, List.forall_mem_cons.2 ⟨subd7_4_508, List.forall_mem_cons.2 ⟨subd7_4_509, List.forall_mem_cons.2 ⟨subd7_4_510, List.forall_mem_cons.2 ⟨subd7_4_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C110
