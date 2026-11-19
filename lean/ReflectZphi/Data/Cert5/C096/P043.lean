import ReflectZphi.Data.Cert5.C096.Base

namespace ReflectZphi.Data.Cert5.C096

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd10_3_224 : subd10_3 [0, 1, -3] = true := by decide +kernel
theorem subd10_3_225 : subd10_3 [0, 1, -2] = true := by decide +kernel
theorem subd10_3_226 : subd10_3 [0, 1, -1] = true := by decide +kernel
theorem subd10_3_227 : subd10_3 [0, 1, 0] = true := by decide +kernel
theorem subd10_3_228 : subd10_3 [0, 1, 1] = true := by decide +kernel
theorem subd10_3_229 : subd10_3 [0, 1, 2] = true := by decide +kernel
theorem subd10_3_230 : subd10_3 [0, 1, 3] = true := by decide +kernel
theorem subd10_3_231 : subd10_3 [0, 1, 4] = true := by decide +kernel
theorem subd10_3_232 : subd10_3 [0, 1, 5] = true := by decide +kernel
theorem subd10_3_233 : subd10_3 [0, 1, 6] = true := by decide +kernel
theorem subd10_3_234 : subd10_3 [0, 2, -8] = true := by decide +kernel
theorem subd10_3_235 : subd10_3 [0, 2, -7] = true := by decide +kernel
theorem subd10_3_236 : subd10_3 [0, 2, -6] = true := by decide +kernel
theorem subd10_3_237 : subd10_3 [0, 2, -5] = true := by decide +kernel
theorem subd10_3_238 : subd10_3 [0, 2, -4] = true := by decide +kernel
theorem subd10_3_239 : subd10_3 [0, 2, -3] = true := by decide +kernel
theorem subd10_3_240 : subd10_3 [0, 2, -2] = true := by decide +kernel
theorem subd10_3_241 : subd10_3 [0, 2, -1] = true := by decide +kernel
theorem subd10_3_242 : subd10_3 [0, 2, 0] = true := by decide +kernel
theorem subd10_3_243 : subd10_3 [0, 2, 1] = true := by decide +kernel
theorem subd10_3_244 : subd10_3 [0, 2, 2] = true := by decide +kernel
theorem subd10_3_245 : subd10_3 [0, 2, 3] = true := by decide +kernel
theorem subd10_3_246 : subd10_3 [0, 2, 4] = true := by decide +kernel
theorem subd10_3_247 : subd10_3 [0, 2, 5] = true := by decide +kernel
theorem subd10_3_248 : subd10_3 [0, 2, 6] = true := by decide +kernel
theorem subd10_3_249 : subd10_3 [0, 3] = true := by decide +kernel
theorem subd10_3_250 : subd10_3 [0, 4] = true := by decide +kernel
theorem subd10_3_251 : subd10_3 [0, 5] = true := by decide +kernel
theorem subd10_3_252 : subd10_3 [0, 6] = true := by decide +kernel
theorem subd10_3_253 : subd10_3 [1, -7] = true := by decide +kernel
theorem subd10_3_254 : subd10_3 [1, -6] = true := by decide +kernel
theorem subd10_3_255 : subd10_3 [1, -5] = true := by decide +kernel
theorem sbd10_3_7 : ∀ q ∈ blkd10_3_7, subd10_3 q = true := by
  unfold blkd10_3_7
  exact List.forall_mem_cons.2 ⟨subd10_3_224, List.forall_mem_cons.2 ⟨subd10_3_225, List.forall_mem_cons.2 ⟨subd10_3_226, List.forall_mem_cons.2 ⟨subd10_3_227, List.forall_mem_cons.2 ⟨subd10_3_228, List.forall_mem_cons.2 ⟨subd10_3_229, List.forall_mem_cons.2 ⟨subd10_3_230, List.forall_mem_cons.2 ⟨subd10_3_231, List.forall_mem_cons.2 ⟨subd10_3_232, List.forall_mem_cons.2 ⟨subd10_3_233, List.forall_mem_cons.2 ⟨subd10_3_234, List.forall_mem_cons.2 ⟨subd10_3_235, List.forall_mem_cons.2 ⟨subd10_3_236, List.forall_mem_cons.2 ⟨subd10_3_237, List.forall_mem_cons.2 ⟨subd10_3_238, List.forall_mem_cons.2 ⟨subd10_3_239, List.forall_mem_cons.2 ⟨subd10_3_240, List.forall_mem_cons.2 ⟨subd10_3_241, List.forall_mem_cons.2 ⟨subd10_3_242, List.forall_mem_cons.2 ⟨subd10_3_243, List.forall_mem_cons.2 ⟨subd10_3_244, List.forall_mem_cons.2 ⟨subd10_3_245, List.forall_mem_cons.2 ⟨subd10_3_246, List.forall_mem_cons.2 ⟨subd10_3_247, List.forall_mem_cons.2 ⟨subd10_3_248, List.forall_mem_cons.2 ⟨subd10_3_249, List.forall_mem_cons.2 ⟨subd10_3_250, List.forall_mem_cons.2 ⟨subd10_3_251, List.forall_mem_cons.2 ⟨subd10_3_252, List.forall_mem_cons.2 ⟨subd10_3_253, List.forall_mem_cons.2 ⟨subd10_3_254, List.forall_mem_cons.2 ⟨subd10_3_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_256 : subd10_3 [1, -4] = true := by decide +kernel
theorem subd10_3_257 : subd10_3 [1, -3] = true := by decide +kernel
theorem subd10_3_258 : subd10_3 [1, -2, -6] = true := by decide +kernel
theorem subd10_3_259 : subd10_3 [1, -2, -5] = true := by decide +kernel
theorem subd10_3_260 : subd10_3 [1, -2, -4] = true := by decide +kernel
theorem subd10_3_261 : subd10_3 [1, -2, -3] = true := by decide +kernel
theorem subd10_3_262 : subd10_3 [1, -2, -2] = true := by decide +kernel
theorem subd10_3_263 : subd10_3 [1, -2, -1] = true := by decide +kernel
theorem subd10_3_264 : subd10_3 [1, -2, 0] = true := by decide +kernel
theorem subd10_3_265 : subd10_3 [1, -2, 1] = true := by decide +kernel
theorem subd10_3_266 : subd10_3 [1, -2, 2] = true := by decide +kernel
theorem subd10_3_267 : subd10_3 [1, -2, 3] = true := by decide +kernel
theorem subd10_3_268 : subd10_3 [1, -2, 4] = true := by decide +kernel
theorem subd10_3_269 : subd10_3 [1, -2, 5] = true := by decide +kernel
theorem subd10_3_270 : subd10_3 [1, -2, 6] = true := by decide +kernel
theorem subd10_3_271 : subd10_3 [1, -2, 7] = true := by decide +kernel
theorem subd10_3_272 : subd10_3 [1, -1, -7] = true := by decide +kernel
theorem subd10_3_273 : subd10_3 [1, -1, -6] = true := by decide +kernel
theorem subd10_3_274 : subd10_3 [1, -1, -5] = true := by decide +kernel
theorem subd10_3_275 : subd10_3 [1, -1, -4] = true := by decide +kernel
theorem subd10_3_276 : subd10_3 [1, -1, -3] = true := by decide +kernel
theorem subd10_3_277 : subd10_3 [1, -1, -2] = true := by decide +kernel
theorem subd10_3_278 : subd10_3 [1, -1, -1] = true := by decide +kernel
theorem subd10_3_279 : subd10_3 [1, -1, 0] = true := by decide +kernel
theorem subd10_3_280 : subd10_3 [1, -1, 1] = true := by decide +kernel
theorem subd10_3_281 : subd10_3 [1, -1, 2] = true := by decide +kernel
theorem subd10_3_282 : subd10_3 [1, -1, 3] = true := by decide +kernel
theorem subd10_3_283 : subd10_3 [1, -1, 4] = true := by decide +kernel
theorem subd10_3_284 : subd10_3 [1, -1, 5] = true := by decide +kernel
theorem subd10_3_285 : subd10_3 [1, -1, 6] = true := by decide +kernel
theorem subd10_3_286 : subd10_3 [1, -1, 7] = true := by decide +kernel
theorem subd10_3_287 : subd10_3 [1, 0, -7] = true := by decide +kernel
theorem sbd10_3_8 : ∀ q ∈ blkd10_3_8, subd10_3 q = true := by
  unfold blkd10_3_8
  exact List.forall_mem_cons.2 ⟨subd10_3_256, List.forall_mem_cons.2 ⟨subd10_3_257, List.forall_mem_cons.2 ⟨subd10_3_258, List.forall_mem_cons.2 ⟨subd10_3_259, List.forall_mem_cons.2 ⟨subd10_3_260, List.forall_mem_cons.2 ⟨subd10_3_261, List.forall_mem_cons.2 ⟨subd10_3_262, List.forall_mem_cons.2 ⟨subd10_3_263, List.forall_mem_cons.2 ⟨subd10_3_264, List.forall_mem_cons.2 ⟨subd10_3_265, List.forall_mem_cons.2 ⟨subd10_3_266, List.forall_mem_cons.2 ⟨subd10_3_267, List.forall_mem_cons.2 ⟨subd10_3_268, List.forall_mem_cons.2 ⟨subd10_3_269, List.forall_mem_cons.2 ⟨subd10_3_270, List.forall_mem_cons.2 ⟨subd10_3_271, List.forall_mem_cons.2 ⟨subd10_3_272, List.forall_mem_cons.2 ⟨subd10_3_273, List.forall_mem_cons.2 ⟨subd10_3_274, List.forall_mem_cons.2 ⟨subd10_3_275, List.forall_mem_cons.2 ⟨subd10_3_276, List.forall_mem_cons.2 ⟨subd10_3_277, List.forall_mem_cons.2 ⟨subd10_3_278, List.forall_mem_cons.2 ⟨subd10_3_279, List.forall_mem_cons.2 ⟨subd10_3_280, List.forall_mem_cons.2 ⟨subd10_3_281, List.forall_mem_cons.2 ⟨subd10_3_282, List.forall_mem_cons.2 ⟨subd10_3_283, List.forall_mem_cons.2 ⟨subd10_3_284, List.forall_mem_cons.2 ⟨subd10_3_285, List.forall_mem_cons.2 ⟨subd10_3_286, List.forall_mem_cons.2 ⟨subd10_3_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_288 : subd10_3 [1, 0, -6] = true := by decide +kernel
theorem subd10_3_289 : subd10_3 [1, 0, -5] = true := by decide +kernel
theorem subd10_3_290 : subd10_3 [1, 0, -4] = true := by decide +kernel
theorem subd10_3_291 : subd10_3 [1, 0, -3] = true := by decide +kernel
theorem subd10_3_292 : subd10_3 [1, 0, -2] = true := by decide +kernel
theorem subd10_3_293 : subd10_3 [1, 0, -1] = true := by decide +kernel
theorem subd10_3_294 : subd10_3 [1, 0, 0] = true := by decide +kernel
theorem subd10_3_295 : subd10_3 [1, 0, 1] = true := by decide +kernel
theorem subd10_3_296 : subd10_3 [1, 0, 2] = true := by decide +kernel
theorem subd10_3_297 : subd10_3 [1, 0, 3] = true := by decide +kernel
theorem subd10_3_298 : subd10_3 [1, 0, 4] = true := by decide +kernel
theorem subd10_3_299 : subd10_3 [1, 0, 5] = true := by decide +kernel
theorem subd10_3_300 : subd10_3 [1, 0, 6] = true := by decide +kernel
theorem subd10_3_301 : subd10_3 [1, 1, -7] = true := by decide +kernel
theorem subd10_3_302 : subd10_3 [1, 1, -6] = true := by decide +kernel
theorem subd10_3_303 : subd10_3 [1, 1, -5] = true := by decide +kernel
theorem subd10_3_304 : subd10_3 [1, 1, -4] = true := by decide +kernel
theorem subd10_3_305 : subd10_3 [1, 1, -3] = true := by decide +kernel
theorem subd10_3_306 : subd10_3 [1, 1, -2] = true := by decide +kernel
theorem subd10_3_307 : subd10_3 [1, 1, -1] = true := by decide +kernel
theorem subd10_3_308 : subd10_3 [1, 1, 0] = true := by decide +kernel
theorem subd10_3_309 : subd10_3 [1, 1, 1] = true := by decide +kernel
theorem subd10_3_310 : subd10_3 [1, 1, 2] = true := by decide +kernel
theorem subd10_3_311 : subd10_3 [1, 1, 3] = true := by decide +kernel
theorem subd10_3_312 : subd10_3 [1, 1, 4] = true := by decide +kernel
theorem subd10_3_313 : subd10_3 [1, 1, 5] = true := by decide +kernel
theorem subd10_3_314 : subd10_3 [1, 1, 6] = true := by decide +kernel
theorem subd10_3_315 : subd10_3 [1, 2, -7] = true := by decide +kernel
theorem subd10_3_316 : subd10_3 [1, 2, -6] = true := by decide +kernel
theorem subd10_3_317 : subd10_3 [1, 2, -5] = true := by decide +kernel
theorem subd10_3_318 : subd10_3 [1, 2, -4] = true := by decide +kernel
theorem subd10_3_319 : subd10_3 [1, 2, -3] = true := by decide +kernel
theorem sbd10_3_9 : ∀ q ∈ blkd10_3_9, subd10_3 q = true := by
  unfold blkd10_3_9
  exact List.forall_mem_cons.2 ⟨subd10_3_288, List.forall_mem_cons.2 ⟨subd10_3_289, List.forall_mem_cons.2 ⟨subd10_3_290, List.forall_mem_cons.2 ⟨subd10_3_291, List.forall_mem_cons.2 ⟨subd10_3_292, List.forall_mem_cons.2 ⟨subd10_3_293, List.forall_mem_cons.2 ⟨subd10_3_294, List.forall_mem_cons.2 ⟨subd10_3_295, List.forall_mem_cons.2 ⟨subd10_3_296, List.forall_mem_cons.2 ⟨subd10_3_297, List.forall_mem_cons.2 ⟨subd10_3_298, List.forall_mem_cons.2 ⟨subd10_3_299, List.forall_mem_cons.2 ⟨subd10_3_300, List.forall_mem_cons.2 ⟨subd10_3_301, List.forall_mem_cons.2 ⟨subd10_3_302, List.forall_mem_cons.2 ⟨subd10_3_303, List.forall_mem_cons.2 ⟨subd10_3_304, List.forall_mem_cons.2 ⟨subd10_3_305, List.forall_mem_cons.2 ⟨subd10_3_306, List.forall_mem_cons.2 ⟨subd10_3_307, List.forall_mem_cons.2 ⟨subd10_3_308, List.forall_mem_cons.2 ⟨subd10_3_309, List.forall_mem_cons.2 ⟨subd10_3_310, List.forall_mem_cons.2 ⟨subd10_3_311, List.forall_mem_cons.2 ⟨subd10_3_312, List.forall_mem_cons.2 ⟨subd10_3_313, List.forall_mem_cons.2 ⟨subd10_3_314, List.forall_mem_cons.2 ⟨subd10_3_315, List.forall_mem_cons.2 ⟨subd10_3_316, List.forall_mem_cons.2 ⟨subd10_3_317, List.forall_mem_cons.2 ⟨subd10_3_318, List.forall_mem_cons.2 ⟨subd10_3_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_320 : subd10_3 [1, 2, -2] = true := by decide +kernel
theorem subd10_3_321 : subd10_3 [1, 2, -1] = true := by decide +kernel
theorem subd10_3_322 : subd10_3 [1, 2, 0] = true := by decide +kernel
theorem subd10_3_323 : subd10_3 [1, 2, 1] = true := by decide +kernel
theorem subd10_3_324 : subd10_3 [1, 2, 2] = true := by decide +kernel
theorem subd10_3_325 : subd10_3 [1, 2, 3] = true := by decide +kernel
theorem subd10_3_326 : subd10_3 [1, 2, 4] = true := by decide +kernel
theorem subd10_3_327 : subd10_3 [1, 2, 5] = true := by decide +kernel
theorem subd10_3_328 : subd10_3 [1, 2, 6] = true := by decide +kernel
theorem subd10_3_329 : subd10_3 [1, 3] = true := by decide +kernel
theorem subd10_3_330 : subd10_3 [1, 4] = true := by decide +kernel
theorem subd10_3_331 : subd10_3 [1, 5] = true := by decide +kernel
theorem subd10_3_332 : subd10_3 [2, -6] = true := by decide +kernel
theorem subd10_3_333 : subd10_3 [2, -5] = true := by decide +kernel
theorem subd10_3_334 : subd10_3 [2, -4] = true := by decide +kernel
theorem subd10_3_335 : subd10_3 [2, -3] = true := by decide +kernel
theorem subd10_3_336 : subd10_3 [2, -2, -6] = true := by decide +kernel
theorem subd10_3_337 : subd10_3 [2, -2, -5] = true := by decide +kernel
theorem subd10_3_338 : subd10_3 [2, -2, -4] = true := by decide +kernel
theorem subd10_3_339 : subd10_3 [2, -2, -3] = true := by decide +kernel
theorem subd10_3_340 : subd10_3 [2, -2, -2] = true := by decide +kernel
theorem subd10_3_341 : subd10_3 [2, -2, -1] = true := by decide +kernel
theorem subd10_3_342 : subd10_3 [2, -2, 0] = true := by decide +kernel
theorem subd10_3_343 : subd10_3 [2, -2, 1] = true := by decide +kernel
theorem subd10_3_344 : subd10_3 [2, -2, 2] = true := by decide +kernel
theorem subd10_3_345 : subd10_3 [2, -2, 3] = true := by decide +kernel
theorem subd10_3_346 : subd10_3 [2, -2, 4] = true := by decide +kernel
theorem subd10_3_347 : subd10_3 [2, -2, 5] = true := by decide +kernel
theorem subd10_3_348 : subd10_3 [2, -2, 6] = true := by decide +kernel
theorem subd10_3_349 : subd10_3 [2, -1, -7] = true := by decide +kernel
theorem subd10_3_350 : subd10_3 [2, -1, -6] = true := by decide +kernel
theorem subd10_3_351 : subd10_3 [2, -1, -5] = true := by decide +kernel
theorem sbd10_3_10 : ∀ q ∈ blkd10_3_10, subd10_3 q = true := by
  unfold blkd10_3_10
  exact List.forall_mem_cons.2 ⟨subd10_3_320, List.forall_mem_cons.2 ⟨subd10_3_321, List.forall_mem_cons.2 ⟨subd10_3_322, List.forall_mem_cons.2 ⟨subd10_3_323, List.forall_mem_cons.2 ⟨subd10_3_324, List.forall_mem_cons.2 ⟨subd10_3_325, List.forall_mem_cons.2 ⟨subd10_3_326, List.forall_mem_cons.2 ⟨subd10_3_327, List.forall_mem_cons.2 ⟨subd10_3_328, List.forall_mem_cons.2 ⟨subd10_3_329, List.forall_mem_cons.2 ⟨subd10_3_330, List.forall_mem_cons.2 ⟨subd10_3_331, List.forall_mem_cons.2 ⟨subd10_3_332, List.forall_mem_cons.2 ⟨subd10_3_333, List.forall_mem_cons.2 ⟨subd10_3_334, List.forall_mem_cons.2 ⟨subd10_3_335, List.forall_mem_cons.2 ⟨subd10_3_336, List.forall_mem_cons.2 ⟨subd10_3_337, List.forall_mem_cons.2 ⟨subd10_3_338, List.forall_mem_cons.2 ⟨subd10_3_339, List.forall_mem_cons.2 ⟨subd10_3_340, List.forall_mem_cons.2 ⟨subd10_3_341, List.forall_mem_cons.2 ⟨subd10_3_342, List.forall_mem_cons.2 ⟨subd10_3_343, List.forall_mem_cons.2 ⟨subd10_3_344, List.forall_mem_cons.2 ⟨subd10_3_345, List.forall_mem_cons.2 ⟨subd10_3_346, List.forall_mem_cons.2 ⟨subd10_3_347, List.forall_mem_cons.2 ⟨subd10_3_348, List.forall_mem_cons.2 ⟨subd10_3_349, List.forall_mem_cons.2 ⟨subd10_3_350, List.forall_mem_cons.2 ⟨subd10_3_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_352 : subd10_3 [2, -1, -4] = true := by decide +kernel
theorem subd10_3_353 : subd10_3 [2, -1, -3] = true := by decide +kernel
theorem subd10_3_354 : subd10_3 [2, -1, -2] = true := by decide +kernel
theorem subd10_3_355 : subd10_3 [2, -1, -1] = true := by decide +kernel
theorem subd10_3_356 : subd10_3 [2, -1, 0] = true := by decide +kernel
theorem subd10_3_357 : subd10_3 [2, -1, 1] = true := by decide +kernel
theorem subd10_3_358 : subd10_3 [2, -1, 2] = true := by decide +kernel
theorem subd10_3_359 : subd10_3 [2, -1, 3] = true := by decide +kernel
theorem subd10_3_360 : subd10_3 [2, -1, 4] = true := by decide +kernel
theorem subd10_3_361 : subd10_3 [2, -1, 5] = true := by decide +kernel
theorem subd10_3_362 : subd10_3 [2, -1, 6] = true := by decide +kernel
theorem subd10_3_363 : subd10_3 [2, 0, -7] = true := by decide +kernel
theorem subd10_3_364 : subd10_3 [2, 0, -6] = true := by decide +kernel
theorem subd10_3_365 : subd10_3 [2, 0, -5] = true := by decide +kernel
theorem subd10_3_366 : subd10_3 [2, 0, -4] = true := by decide +kernel
theorem subd10_3_367 : subd10_3 [2, 0, -3] = true := by decide +kernel
theorem subd10_3_368 : subd10_3 [2, 0, -2] = true := by decide +kernel
theorem subd10_3_369 : subd10_3 [2, 0, -1] = true := by decide +kernel
theorem subd10_3_370 : subd10_3 [2, 0, 0] = true := by decide +kernel
theorem subd10_3_371 : subd10_3 [2, 0, 1] = true := by decide +kernel
theorem subd10_3_372 : subd10_3 [2, 0, 2] = true := by decide +kernel
theorem subd10_3_373 : subd10_3 [2, 0, 3] = true := by decide +kernel
theorem subd10_3_374 : subd10_3 [2, 0, 4] = true := by decide +kernel
theorem subd10_3_375 : subd10_3 [2, 0, 5] = true := by decide +kernel
theorem subd10_3_376 : subd10_3 [2, 0, 6] = true := by decide +kernel
theorem subd10_3_377 : subd10_3 [2, 1, -7] = true := by decide +kernel
theorem subd10_3_378 : subd10_3 [2, 1, -6] = true := by decide +kernel
theorem subd10_3_379 : subd10_3 [2, 1, -5] = true := by decide +kernel
theorem subd10_3_380 : subd10_3 [2, 1, -4] = true := by decide +kernel
theorem subd10_3_381 : subd10_3 [2, 1, -3] = true := by decide +kernel
theorem subd10_3_382 : subd10_3 [2, 1, -2] = true := by decide +kernel
theorem subd10_3_383 : subd10_3 [2, 1, -1] = true := by decide +kernel
theorem sbd10_3_11 : ∀ q ∈ blkd10_3_11, subd10_3 q = true := by
  unfold blkd10_3_11
  exact List.forall_mem_cons.2 ⟨subd10_3_352, List.forall_mem_cons.2 ⟨subd10_3_353, List.forall_mem_cons.2 ⟨subd10_3_354, List.forall_mem_cons.2 ⟨subd10_3_355, List.forall_mem_cons.2 ⟨subd10_3_356, List.forall_mem_cons.2 ⟨subd10_3_357, List.forall_mem_cons.2 ⟨subd10_3_358, List.forall_mem_cons.2 ⟨subd10_3_359, List.forall_mem_cons.2 ⟨subd10_3_360, List.forall_mem_cons.2 ⟨subd10_3_361, List.forall_mem_cons.2 ⟨subd10_3_362, List.forall_mem_cons.2 ⟨subd10_3_363, List.forall_mem_cons.2 ⟨subd10_3_364, List.forall_mem_cons.2 ⟨subd10_3_365, List.forall_mem_cons.2 ⟨subd10_3_366, List.forall_mem_cons.2 ⟨subd10_3_367, List.forall_mem_cons.2 ⟨subd10_3_368, List.forall_mem_cons.2 ⟨subd10_3_369, List.forall_mem_cons.2 ⟨subd10_3_370, List.forall_mem_cons.2 ⟨subd10_3_371, List.forall_mem_cons.2 ⟨subd10_3_372, List.forall_mem_cons.2 ⟨subd10_3_373, List.forall_mem_cons.2 ⟨subd10_3_374, List.forall_mem_cons.2 ⟨subd10_3_375, List.forall_mem_cons.2 ⟨subd10_3_376, List.forall_mem_cons.2 ⟨subd10_3_377, List.forall_mem_cons.2 ⟨subd10_3_378, List.forall_mem_cons.2 ⟨subd10_3_379, List.forall_mem_cons.2 ⟨subd10_3_380, List.forall_mem_cons.2 ⟨subd10_3_381, List.forall_mem_cons.2 ⟨subd10_3_382, List.forall_mem_cons.2 ⟨subd10_3_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_384 : subd10_3 [2, 1, 0] = true := by decide +kernel
theorem subd10_3_385 : subd10_3 [2, 1, 1] = true := by decide +kernel
theorem subd10_3_386 : subd10_3 [2, 1, 2] = true := by decide +kernel
theorem subd10_3_387 : subd10_3 [2, 1, 3] = true := by decide +kernel
theorem subd10_3_388 : subd10_3 [2, 1, 4] = true := by decide +kernel
theorem subd10_3_389 : subd10_3 [2, 1, 5] = true := by decide +kernel
theorem subd10_3_390 : subd10_3 [2, 1, 6] = true := by decide +kernel
theorem subd10_3_391 : subd10_3 [2, 2] = true := by decide +kernel
theorem subd10_3_392 : subd10_3 [2, 3] = true := by decide +kernel
theorem subd10_3_393 : subd10_3 [2, 4] = true := by decide +kernel
theorem subd10_3_394 : subd10_3 [2, 5] = true := by decide +kernel
theorem subd10_3_395 : subd10_3 [3, -6] = true := by decide +kernel
theorem subd10_3_396 : subd10_3 [3, -5] = true := by decide +kernel
theorem subd10_3_397 : subd10_3 [3, -4] = true := by decide +kernel
theorem subd10_3_398 : subd10_3 [3, -3] = true := by decide +kernel
theorem subd10_3_399 : subd10_3 [3, -2] = true := by decide +kernel
theorem subd10_3_400 : subd10_3 [3, -1] = true := by decide +kernel
theorem subd10_3_401 : subd10_3 [3, 0] = true := by decide +kernel
theorem subd10_3_402 : subd10_3 [3, 1] = true := by decide +kernel
theorem subd10_3_403 : subd10_3 [3, 2] = true := by decide +kernel
theorem subd10_3_404 : subd10_3 [3, 3] = true := by decide +kernel
theorem subd10_3_405 : subd10_3 [3, 4] = true := by decide +kernel
theorem subd10_3_406 : subd10_3 [4, -5] = true := by decide +kernel
theorem subd10_3_407 : subd10_3 [4, -4] = true := by decide +kernel
theorem subd10_3_408 : subd10_3 [4, -3] = true := by decide +kernel
theorem subd10_3_409 : subd10_3 [4, -2] = true := by decide +kernel
theorem subd10_3_410 : subd10_3 [4, -1] = true := by decide +kernel
theorem subd10_3_411 : subd10_3 [4, 0] = true := by decide +kernel
theorem subd10_3_412 : subd10_3 [4, 1] = true := by decide +kernel
theorem subd10_3_413 : subd10_3 [4, 2] = true := by decide +kernel
theorem subd10_3_414 : subd10_3 [4, 3] = true := by decide +kernel
theorem subd10_3_415 : subd10_3 [4, 4] = true := by decide +kernel
theorem sbd10_3_12 : ∀ q ∈ blkd10_3_12, subd10_3 q = true := by
  unfold blkd10_3_12
  exact List.forall_mem_cons.2 ⟨subd10_3_384, List.forall_mem_cons.2 ⟨subd10_3_385, List.forall_mem_cons.2 ⟨subd10_3_386, List.forall_mem_cons.2 ⟨subd10_3_387, List.forall_mem_cons.2 ⟨subd10_3_388, List.forall_mem_cons.2 ⟨subd10_3_389, List.forall_mem_cons.2 ⟨subd10_3_390, List.forall_mem_cons.2 ⟨subd10_3_391, List.forall_mem_cons.2 ⟨subd10_3_392, List.forall_mem_cons.2 ⟨subd10_3_393, List.forall_mem_cons.2 ⟨subd10_3_394, List.forall_mem_cons.2 ⟨subd10_3_395, List.forall_mem_cons.2 ⟨subd10_3_396, List.forall_mem_cons.2 ⟨subd10_3_397, List.forall_mem_cons.2 ⟨subd10_3_398, List.forall_mem_cons.2 ⟨subd10_3_399, List.forall_mem_cons.2 ⟨subd10_3_400, List.forall_mem_cons.2 ⟨subd10_3_401, List.forall_mem_cons.2 ⟨subd10_3_402, List.forall_mem_cons.2 ⟨subd10_3_403, List.forall_mem_cons.2 ⟨subd10_3_404, List.forall_mem_cons.2 ⟨subd10_3_405, List.forall_mem_cons.2 ⟨subd10_3_406, List.forall_mem_cons.2 ⟨subd10_3_407, List.forall_mem_cons.2 ⟨subd10_3_408, List.forall_mem_cons.2 ⟨subd10_3_409, List.forall_mem_cons.2 ⟨subd10_3_410, List.forall_mem_cons.2 ⟨subd10_3_411, List.forall_mem_cons.2 ⟨subd10_3_412, List.forall_mem_cons.2 ⟨subd10_3_413, List.forall_mem_cons.2 ⟨subd10_3_414, List.forall_mem_cons.2 ⟨subd10_3_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_416 : subd10_3 [5, -4] = true := by decide +kernel
theorem subd10_3_417 : subd10_3 [5, -3] = true := by decide +kernel
theorem subd10_3_418 : subd10_3 [5, -2] = true := by decide +kernel
theorem subd10_3_419 : subd10_3 [5, -1] = true := by decide +kernel
theorem subd10_3_420 : subd10_3 [5, 0] = true := by decide +kernel
theorem subd10_3_421 : subd10_3 [5, 1] = true := by decide +kernel
theorem subd10_3_422 : subd10_3 [5, 2] = true := by decide +kernel
theorem sbd10_3_13 : ∀ q ∈ blkd10_3_13, subd10_3 q = true := by
  unfold blkd10_3_13
  exact List.forall_mem_cons.2 ⟨subd10_3_416, List.forall_mem_cons.2 ⟨subd10_3_417, List.forall_mem_cons.2 ⟨subd10_3_418, List.forall_mem_cons.2 ⟨subd10_3_419, List.forall_mem_cons.2 ⟨subd10_3_420, List.forall_mem_cons.2 ⟨subd10_3_421, List.forall_mem_cons.2 ⟨subd10_3_422, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_4 : ldCheck G d10_4.U d10_4.ms ldd10_4 = true := by decide +kernel
theorem pre_okd10_4 : subPre G cell10 d10_4 = true := by decide +kernel
theorem subd10_4_0 : subd10_4 [-3] = true := by decide +kernel
theorem subd10_4_1 : subd10_4 [-2, -4] = true := by decide +kernel
theorem subd10_4_2 : subd10_4 [-2, -3] = true := by decide +kernel
theorem subd10_4_3 : subd10_4 [-2, -2] = true := by decide +kernel
theorem subd10_4_4 : subd10_4 [-2, -1] = true := by decide +kernel
theorem subd10_4_5 : subd10_4 [-2, 0] = true := by decide +kernel
theorem subd10_4_6 : subd10_4 [-2, 1] = true := by decide +kernel
theorem subd10_4_7 : subd10_4 [-2, 2] = true := by decide +kernel
theorem subd10_4_8 : subd10_4 [-2, 3] = true := by decide +kernel
theorem subd10_4_9 : subd10_4 [-2, 4] = true := by decide +kernel
theorem subd10_4_10 : subd10_4 [-1, -4] = true := by decide +kernel
theorem subd10_4_11 : subd10_4 [-1, -3] = true := by decide +kernel
theorem subd10_4_12 : subd10_4 [-1, -2] = true := by decide +kernel
theorem subd10_4_13 : subd10_4 [-1, -1] = true := by decide +kernel
theorem subd10_4_14 : subd10_4 [-1, 0] = true := by decide +kernel
theorem subd10_4_15 : subd10_4 [-1, 1] = true := by decide +kernel
theorem subd10_4_16 : subd10_4 [-1, 2] = true := by decide +kernel
theorem subd10_4_17 : subd10_4 [-1, 3] = true := by decide +kernel
theorem subd10_4_18 : subd10_4 [-1, 4] = true := by decide +kernel
theorem subd10_4_19 : subd10_4 [0, -5] = true := by decide +kernel
theorem subd10_4_20 : subd10_4 [0, -4] = true := by decide +kernel
theorem subd10_4_21 : subd10_4 [0, -3] = true := by decide +kernel
theorem subd10_4_22 : subd10_4 [0, -2] = true := by decide +kernel
theorem subd10_4_23 : subd10_4 [0, -1] = true := by decide +kernel
theorem subd10_4_24 : subd10_4 [0, 0] = true := by decide +kernel
theorem subd10_4_25 : subd10_4 [0, 1] = true := by decide +kernel
theorem subd10_4_26 : subd10_4 [0, 2] = true := by decide +kernel
theorem subd10_4_27 : subd10_4 [0, 3] = true := by decide +kernel
theorem subd10_4_28 : subd10_4 [0, 4] = true := by decide +kernel
theorem subd10_4_29 : subd10_4 [1, -5] = true := by decide +kernel
theorem subd10_4_30 : subd10_4 [1, -4] = true := by decide +kernel
theorem subd10_4_31 : subd10_4 [1, -3] = true := by decide +kernel
theorem sbd10_4_0 : ∀ q ∈ blkd10_4_0, subd10_4 q = true := by
  unfold blkd10_4_0
  exact List.forall_mem_cons.2 ⟨subd10_4_0, List.forall_mem_cons.2 ⟨subd10_4_1, List.forall_mem_cons.2 ⟨subd10_4_2, List.forall_mem_cons.2 ⟨subd10_4_3, List.forall_mem_cons.2 ⟨subd10_4_4, List.forall_mem_cons.2 ⟨subd10_4_5, List.forall_mem_cons.2 ⟨subd10_4_6, List.forall_mem_cons.2 ⟨subd10_4_7, List.forall_mem_cons.2 ⟨subd10_4_8, List.forall_mem_cons.2 ⟨subd10_4_9, List.forall_mem_cons.2 ⟨subd10_4_10, List.forall_mem_cons.2 ⟨subd10_4_11, List.forall_mem_cons.2 ⟨subd10_4_12, List.forall_mem_cons.2 ⟨subd10_4_13, List.forall_mem_cons.2 ⟨subd10_4_14, List.forall_mem_cons.2 ⟨subd10_4_15, List.forall_mem_cons.2 ⟨subd10_4_16, List.forall_mem_cons.2 ⟨subd10_4_17, List.forall_mem_cons.2 ⟨subd10_4_18, List.forall_mem_cons.2 ⟨subd10_4_19, List.forall_mem_cons.2 ⟨subd10_4_20, List.forall_mem_cons.2 ⟨subd10_4_21, List.forall_mem_cons.2 ⟨subd10_4_22, List.forall_mem_cons.2 ⟨subd10_4_23, List.forall_mem_cons.2 ⟨subd10_4_24, List.forall_mem_cons.2 ⟨subd10_4_25, List.forall_mem_cons.2 ⟨subd10_4_26, List.forall_mem_cons.2 ⟨subd10_4_27, List.forall_mem_cons.2 ⟨subd10_4_28, List.forall_mem_cons.2 ⟨subd10_4_29, List.forall_mem_cons.2 ⟨subd10_4_30, List.forall_mem_cons.2 ⟨subd10_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C096
