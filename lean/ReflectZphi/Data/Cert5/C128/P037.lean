import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_6_224 : subd6_6 [0, 2, 4] = true := by decide +kernel
theorem subd6_6_225 : subd6_6 [0, 2, 5] = true := by decide +kernel
theorem subd6_6_226 : subd6_6 [0, 3] = true := by decide +kernel
theorem subd6_6_227 : subd6_6 [0, 4] = true := by decide +kernel
theorem subd6_6_228 : subd6_6 [0, 5] = true := by decide +kernel
theorem subd6_6_229 : subd6_6 [1, -6] = true := by decide +kernel
theorem subd6_6_230 : subd6_6 [1, -5] = true := by decide +kernel
theorem subd6_6_231 : subd6_6 [1, -4] = true := by decide +kernel
theorem subd6_6_232 : subd6_6 [1, -3] = true := by decide +kernel
theorem subd6_6_233 : subd6_6 [1, -2, -6] = true := by decide +kernel
theorem subd6_6_234 : subd6_6 [1, -2, -5] = true := by decide +kernel
theorem subd6_6_235 : subd6_6 [1, -2, -4] = true := by decide +kernel
theorem subd6_6_236 : subd6_6 [1, -2, -3] = true := by decide +kernel
theorem subd6_6_237 : subd6_6 [1, -2, -2] = true := by decide +kernel
theorem subd6_6_238 : subd6_6 [1, -2, -1] = true := by decide +kernel
theorem subd6_6_239 : subd6_6 [1, -2, 0] = true := by decide +kernel
theorem subd6_6_240 : subd6_6 [1, -2, 1] = true := by decide +kernel
theorem subd6_6_241 : subd6_6 [1, -2, 2] = true := by decide +kernel
theorem subd6_6_242 : subd6_6 [1, -2, 3] = true := by decide +kernel
theorem subd6_6_243 : subd6_6 [1, -2, 4] = true := by decide +kernel
theorem subd6_6_244 : subd6_6 [1, -2, 5] = true := by decide +kernel
theorem subd6_6_245 : subd6_6 [1, -2, 6] = true := by decide +kernel
theorem subd6_6_246 : subd6_6 [1, -1, -7] = true := by decide +kernel
theorem subd6_6_247 : subd6_6 [1, -1, -6] = true := by decide +kernel
theorem subd6_6_248 : subd6_6 [1, -1, -5] = true := by decide +kernel
theorem subd6_6_249 : subd6_6 [1, -1, -4] = true := by decide +kernel
theorem subd6_6_250 : subd6_6 [1, -1, -3] = true := by decide +kernel
theorem subd6_6_251 : subd6_6 [1, -1, -2] = true := by decide +kernel
theorem subd6_6_252 : subd6_6 [1, -1, -1] = true := by decide +kernel
theorem subd6_6_253 : subd6_6 [1, -1, 0] = true := by decide +kernel
theorem subd6_6_254 : subd6_6 [1, -1, 1] = true := by decide +kernel
theorem subd6_6_255 : subd6_6 [1, -1, 2] = true := by decide +kernel
theorem sbd6_6_7 : ∀ q ∈ blkd6_6_7, subd6_6 q = true := by
  unfold blkd6_6_7
  exact List.forall_mem_cons.2 ⟨subd6_6_224, List.forall_mem_cons.2 ⟨subd6_6_225, List.forall_mem_cons.2 ⟨subd6_6_226, List.forall_mem_cons.2 ⟨subd6_6_227, List.forall_mem_cons.2 ⟨subd6_6_228, List.forall_mem_cons.2 ⟨subd6_6_229, List.forall_mem_cons.2 ⟨subd6_6_230, List.forall_mem_cons.2 ⟨subd6_6_231, List.forall_mem_cons.2 ⟨subd6_6_232, List.forall_mem_cons.2 ⟨subd6_6_233, List.forall_mem_cons.2 ⟨subd6_6_234, List.forall_mem_cons.2 ⟨subd6_6_235, List.forall_mem_cons.2 ⟨subd6_6_236, List.forall_mem_cons.2 ⟨subd6_6_237, List.forall_mem_cons.2 ⟨subd6_6_238, List.forall_mem_cons.2 ⟨subd6_6_239, List.forall_mem_cons.2 ⟨subd6_6_240, List.forall_mem_cons.2 ⟨subd6_6_241, List.forall_mem_cons.2 ⟨subd6_6_242, List.forall_mem_cons.2 ⟨subd6_6_243, List.forall_mem_cons.2 ⟨subd6_6_244, List.forall_mem_cons.2 ⟨subd6_6_245, List.forall_mem_cons.2 ⟨subd6_6_246, List.forall_mem_cons.2 ⟨subd6_6_247, List.forall_mem_cons.2 ⟨subd6_6_248, List.forall_mem_cons.2 ⟨subd6_6_249, List.forall_mem_cons.2 ⟨subd6_6_250, List.forall_mem_cons.2 ⟨subd6_6_251, List.forall_mem_cons.2 ⟨subd6_6_252, List.forall_mem_cons.2 ⟨subd6_6_253, List.forall_mem_cons.2 ⟨subd6_6_254, List.forall_mem_cons.2 ⟨subd6_6_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_6_256 : subd6_6 [1, -1, 3] = true := by decide +kernel
theorem subd6_6_257 : subd6_6 [1, -1, 4] = true := by decide +kernel
theorem subd6_6_258 : subd6_6 [1, -1, 5] = true := by decide +kernel
theorem subd6_6_259 : subd6_6 [1, -1, 6] = true := by decide +kernel
theorem subd6_6_260 : subd6_6 [1, -1, 7] = true := by decide +kernel
theorem subd6_6_261 : subd6_6 [1, 0, -7] = true := by decide +kernel
theorem subd6_6_262 : subd6_6 [1, 0, -6] = true := by decide +kernel
theorem subd6_6_263 : subd6_6 [1, 0, -5] = true := by decide +kernel
theorem subd6_6_264 : subd6_6 [1, 0, -4] = true := by decide +kernel
theorem subd6_6_265 : subd6_6 [1, 0, -3] = true := by decide +kernel
theorem subd6_6_266 : subd6_6 [1, 0, -2] = true := by decide +kernel
theorem subd6_6_267 : subd6_6 [1, 0, -1] = true := by decide +kernel
theorem subd6_6_268 : subd6_6 [1, 0, 0] = true := by decide +kernel
theorem subd6_6_269 : subd6_6 [1, 0, 1] = true := by decide +kernel
theorem subd6_6_270 : subd6_6 [1, 0, 2] = true := by decide +kernel
theorem subd6_6_271 : subd6_6 [1, 0, 3] = true := by decide +kernel
theorem subd6_6_272 : subd6_6 [1, 0, 4] = true := by decide +kernel
theorem subd6_6_273 : subd6_6 [1, 0, 5] = true := by decide +kernel
theorem subd6_6_274 : subd6_6 [1, 0, 6] = true := by decide +kernel
theorem subd6_6_275 : subd6_6 [1, 1, -7] = true := by decide +kernel
theorem subd6_6_276 : subd6_6 [1, 1, -6] = true := by decide +kernel
theorem subd6_6_277 : subd6_6 [1, 1, -5] = true := by decide +kernel
theorem subd6_6_278 : subd6_6 [1, 1, -4] = true := by decide +kernel
theorem subd6_6_279 : subd6_6 [1, 1, -3] = true := by decide +kernel
theorem subd6_6_280 : subd6_6 [1, 1, -2] = true := by decide +kernel
theorem subd6_6_281 : subd6_6 [1, 1, -1] = true := by decide +kernel
theorem subd6_6_282 : subd6_6 [1, 1, 0] = true := by decide +kernel
theorem subd6_6_283 : subd6_6 [1, 1, 1] = true := by decide +kernel
theorem subd6_6_284 : subd6_6 [1, 1, 2] = true := by decide +kernel
theorem subd6_6_285 : subd6_6 [1, 1, 3] = true := by decide +kernel
theorem subd6_6_286 : subd6_6 [1, 1, 4] = true := by decide +kernel
theorem subd6_6_287 : subd6_6 [1, 1, 5] = true := by decide +kernel
theorem sbd6_6_8 : ∀ q ∈ blkd6_6_8, subd6_6 q = true := by
  unfold blkd6_6_8
  exact List.forall_mem_cons.2 ⟨subd6_6_256, List.forall_mem_cons.2 ⟨subd6_6_257, List.forall_mem_cons.2 ⟨subd6_6_258, List.forall_mem_cons.2 ⟨subd6_6_259, List.forall_mem_cons.2 ⟨subd6_6_260, List.forall_mem_cons.2 ⟨subd6_6_261, List.forall_mem_cons.2 ⟨subd6_6_262, List.forall_mem_cons.2 ⟨subd6_6_263, List.forall_mem_cons.2 ⟨subd6_6_264, List.forall_mem_cons.2 ⟨subd6_6_265, List.forall_mem_cons.2 ⟨subd6_6_266, List.forall_mem_cons.2 ⟨subd6_6_267, List.forall_mem_cons.2 ⟨subd6_6_268, List.forall_mem_cons.2 ⟨subd6_6_269, List.forall_mem_cons.2 ⟨subd6_6_270, List.forall_mem_cons.2 ⟨subd6_6_271, List.forall_mem_cons.2 ⟨subd6_6_272, List.forall_mem_cons.2 ⟨subd6_6_273, List.forall_mem_cons.2 ⟨subd6_6_274, List.forall_mem_cons.2 ⟨subd6_6_275, List.forall_mem_cons.2 ⟨subd6_6_276, List.forall_mem_cons.2 ⟨subd6_6_277, List.forall_mem_cons.2 ⟨subd6_6_278, List.forall_mem_cons.2 ⟨subd6_6_279, List.forall_mem_cons.2 ⟨subd6_6_280, List.forall_mem_cons.2 ⟨subd6_6_281, List.forall_mem_cons.2 ⟨subd6_6_282, List.forall_mem_cons.2 ⟨subd6_6_283, List.forall_mem_cons.2 ⟨subd6_6_284, List.forall_mem_cons.2 ⟨subd6_6_285, List.forall_mem_cons.2 ⟨subd6_6_286, List.forall_mem_cons.2 ⟨subd6_6_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_6_288 : subd6_6 [1, 1, 6] = true := by decide +kernel
theorem subd6_6_289 : subd6_6 [1, 2, -7] = true := by decide +kernel
theorem subd6_6_290 : subd6_6 [1, 2, -6] = true := by decide +kernel
theorem subd6_6_291 : subd6_6 [1, 2, -5] = true := by decide +kernel
theorem subd6_6_292 : subd6_6 [1, 2, -4] = true := by decide +kernel
theorem subd6_6_293 : subd6_6 [1, 2, -3] = true := by decide +kernel
theorem subd6_6_294 : subd6_6 [1, 2, -2] = true := by decide +kernel
theorem subd6_6_295 : subd6_6 [1, 2, -1] = true := by decide +kernel
theorem subd6_6_296 : subd6_6 [1, 2, 0] = true := by decide +kernel
theorem subd6_6_297 : subd6_6 [1, 2, 1] = true := by decide +kernel
theorem subd6_6_298 : subd6_6 [1, 2, 2] = true := by decide +kernel
theorem subd6_6_299 : subd6_6 [1, 2, 3] = true := by decide +kernel
theorem subd6_6_300 : subd6_6 [1, 2, 4] = true := by decide +kernel
theorem subd6_6_301 : subd6_6 [1, 2, 5] = true := by decide +kernel
theorem subd6_6_302 : subd6_6 [1, 3] = true := by decide +kernel
theorem subd6_6_303 : subd6_6 [1, 4] = true := by decide +kernel
theorem subd6_6_304 : subd6_6 [1, 5] = true := by decide +kernel
theorem subd6_6_305 : subd6_6 [2, -6] = true := by decide +kernel
theorem subd6_6_306 : subd6_6 [2, -5] = true := by decide +kernel
theorem subd6_6_307 : subd6_6 [2, -4] = true := by decide +kernel
theorem subd6_6_308 : subd6_6 [2, -3] = true := by decide +kernel
theorem subd6_6_309 : subd6_6 [2, -2] = true := by decide +kernel
theorem subd6_6_310 : subd6_6 [2, -1, -6] = true := by decide +kernel
theorem subd6_6_311 : subd6_6 [2, -1, -5] = true := by decide +kernel
theorem subd6_6_312 : subd6_6 [2, -1, -4] = true := by decide +kernel
theorem subd6_6_313 : subd6_6 [2, -1, -3] = true := by decide +kernel
theorem subd6_6_314 : subd6_6 [2, -1, -2] = true := by decide +kernel
theorem subd6_6_315 : subd6_6 [2, -1, -1] = true := by decide +kernel
theorem subd6_6_316 : subd6_6 [2, -1, 0] = true := by decide +kernel
theorem subd6_6_317 : subd6_6 [2, -1, 1] = true := by decide +kernel
theorem subd6_6_318 : subd6_6 [2, -1, 2] = true := by decide +kernel
theorem subd6_6_319 : subd6_6 [2, -1, 3] = true := by decide +kernel
theorem sbd6_6_9 : ∀ q ∈ blkd6_6_9, subd6_6 q = true := by
  unfold blkd6_6_9
  exact List.forall_mem_cons.2 ⟨subd6_6_288, List.forall_mem_cons.2 ⟨subd6_6_289, List.forall_mem_cons.2 ⟨subd6_6_290, List.forall_mem_cons.2 ⟨subd6_6_291, List.forall_mem_cons.2 ⟨subd6_6_292, List.forall_mem_cons.2 ⟨subd6_6_293, List.forall_mem_cons.2 ⟨subd6_6_294, List.forall_mem_cons.2 ⟨subd6_6_295, List.forall_mem_cons.2 ⟨subd6_6_296, List.forall_mem_cons.2 ⟨subd6_6_297, List.forall_mem_cons.2 ⟨subd6_6_298, List.forall_mem_cons.2 ⟨subd6_6_299, List.forall_mem_cons.2 ⟨subd6_6_300, List.forall_mem_cons.2 ⟨subd6_6_301, List.forall_mem_cons.2 ⟨subd6_6_302, List.forall_mem_cons.2 ⟨subd6_6_303, List.forall_mem_cons.2 ⟨subd6_6_304, List.forall_mem_cons.2 ⟨subd6_6_305, List.forall_mem_cons.2 ⟨subd6_6_306, List.forall_mem_cons.2 ⟨subd6_6_307, List.forall_mem_cons.2 ⟨subd6_6_308, List.forall_mem_cons.2 ⟨subd6_6_309, List.forall_mem_cons.2 ⟨subd6_6_310, List.forall_mem_cons.2 ⟨subd6_6_311, List.forall_mem_cons.2 ⟨subd6_6_312, List.forall_mem_cons.2 ⟨subd6_6_313, List.forall_mem_cons.2 ⟨subd6_6_314, List.forall_mem_cons.2 ⟨subd6_6_315, List.forall_mem_cons.2 ⟨subd6_6_316, List.forall_mem_cons.2 ⟨subd6_6_317, List.forall_mem_cons.2 ⟨subd6_6_318, List.forall_mem_cons.2 ⟨subd6_6_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_6_320 : subd6_6 [2, -1, 4] = true := by decide +kernel
theorem subd6_6_321 : subd6_6 [2, -1, 5] = true := by decide +kernel
theorem subd6_6_322 : subd6_6 [2, -1, 6] = true := by decide +kernel
theorem subd6_6_323 : subd6_6 [2, 0, -7] = true := by decide +kernel
theorem subd6_6_324 : subd6_6 [2, 0, -6] = true := by decide +kernel
theorem subd6_6_325 : subd6_6 [2, 0, -5] = true := by decide +kernel
theorem subd6_6_326 : subd6_6 [2, 0, -4] = true := by decide +kernel
theorem subd6_6_327 : subd6_6 [2, 0, -3] = true := by decide +kernel
theorem subd6_6_328 : subd6_6 [2, 0, -2] = true := by decide +kernel
theorem subd6_6_329 : subd6_6 [2, 0, -1] = true := by decide +kernel
theorem subd6_6_330 : subd6_6 [2, 0, 0] = true := by decide +kernel
theorem subd6_6_331 : subd6_6 [2, 0, 1] = true := by decide +kernel
theorem subd6_6_332 : subd6_6 [2, 0, 2] = true := by decide +kernel
theorem subd6_6_333 : subd6_6 [2, 0, 3] = true := by decide +kernel
theorem subd6_6_334 : subd6_6 [2, 0, 4] = true := by decide +kernel
theorem subd6_6_335 : subd6_6 [2, 0, 5] = true := by decide +kernel
theorem subd6_6_336 : subd6_6 [2, 0, 6] = true := by decide +kernel
theorem subd6_6_337 : subd6_6 [2, 1, -7] = true := by decide +kernel
theorem subd6_6_338 : subd6_6 [2, 1, -6] = true := by decide +kernel
theorem subd6_6_339 : subd6_6 [2, 1, -5] = true := by decide +kernel
theorem subd6_6_340 : subd6_6 [2, 1, -4] = true := by decide +kernel
theorem subd6_6_341 : subd6_6 [2, 1, -3] = true := by decide +kernel
theorem subd6_6_342 : subd6_6 [2, 1, -2] = true := by decide +kernel
theorem subd6_6_343 : subd6_6 [2, 1, -1] = true := by decide +kernel
theorem subd6_6_344 : subd6_6 [2, 1, 0] = true := by decide +kernel
theorem subd6_6_345 : subd6_6 [2, 1, 1] = true := by decide +kernel
theorem subd6_6_346 : subd6_6 [2, 1, 2] = true := by decide +kernel
theorem subd6_6_347 : subd6_6 [2, 1, 3] = true := by decide +kernel
theorem subd6_6_348 : subd6_6 [2, 1, 4] = true := by decide +kernel
theorem subd6_6_349 : subd6_6 [2, 1, 5] = true := by decide +kernel
theorem subd6_6_350 : subd6_6 [2, 1, 6] = true := by decide +kernel
theorem subd6_6_351 : subd6_6 [2, 2] = true := by decide +kernel
theorem sbd6_6_10 : ∀ q ∈ blkd6_6_10, subd6_6 q = true := by
  unfold blkd6_6_10
  exact List.forall_mem_cons.2 ⟨subd6_6_320, List.forall_mem_cons.2 ⟨subd6_6_321, List.forall_mem_cons.2 ⟨subd6_6_322, List.forall_mem_cons.2 ⟨subd6_6_323, List.forall_mem_cons.2 ⟨subd6_6_324, List.forall_mem_cons.2 ⟨subd6_6_325, List.forall_mem_cons.2 ⟨subd6_6_326, List.forall_mem_cons.2 ⟨subd6_6_327, List.forall_mem_cons.2 ⟨subd6_6_328, List.forall_mem_cons.2 ⟨subd6_6_329, List.forall_mem_cons.2 ⟨subd6_6_330, List.forall_mem_cons.2 ⟨subd6_6_331, List.forall_mem_cons.2 ⟨subd6_6_332, List.forall_mem_cons.2 ⟨subd6_6_333, List.forall_mem_cons.2 ⟨subd6_6_334, List.forall_mem_cons.2 ⟨subd6_6_335, List.forall_mem_cons.2 ⟨subd6_6_336, List.forall_mem_cons.2 ⟨subd6_6_337, List.forall_mem_cons.2 ⟨subd6_6_338, List.forall_mem_cons.2 ⟨subd6_6_339, List.forall_mem_cons.2 ⟨subd6_6_340, List.forall_mem_cons.2 ⟨subd6_6_341, List.forall_mem_cons.2 ⟨subd6_6_342, List.forall_mem_cons.2 ⟨subd6_6_343, List.forall_mem_cons.2 ⟨subd6_6_344, List.forall_mem_cons.2 ⟨subd6_6_345, List.forall_mem_cons.2 ⟨subd6_6_346, List.forall_mem_cons.2 ⟨subd6_6_347, List.forall_mem_cons.2 ⟨subd6_6_348, List.forall_mem_cons.2 ⟨subd6_6_349, List.forall_mem_cons.2 ⟨subd6_6_350, List.forall_mem_cons.2 ⟨subd6_6_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_6_352 : subd6_6 [2, 3] = true := by decide +kernel
theorem subd6_6_353 : subd6_6 [2, 4] = true := by decide +kernel
theorem subd6_6_354 : subd6_6 [2, 5] = true := by decide +kernel
theorem subd6_6_355 : subd6_6 [3, -5] = true := by decide +kernel
theorem subd6_6_356 : subd6_6 [3, -4] = true := by decide +kernel
theorem subd6_6_357 : subd6_6 [3, -3] = true := by decide +kernel
theorem subd6_6_358 : subd6_6 [3, -2] = true := by decide +kernel
theorem subd6_6_359 : subd6_6 [3, -1] = true := by decide +kernel
theorem subd6_6_360 : subd6_6 [3, 0] = true := by decide +kernel
theorem subd6_6_361 : subd6_6 [3, 1] = true := by decide +kernel
theorem subd6_6_362 : subd6_6 [3, 2] = true := by decide +kernel
theorem subd6_6_363 : subd6_6 [3, 3] = true := by decide +kernel
theorem subd6_6_364 : subd6_6 [3, 4] = true := by decide +kernel
theorem subd6_6_365 : subd6_6 [4, -4] = true := by decide +kernel
theorem subd6_6_366 : subd6_6 [4, -3] = true := by decide +kernel
theorem subd6_6_367 : subd6_6 [4, -2] = true := by decide +kernel
theorem subd6_6_368 : subd6_6 [4, -1] = true := by decide +kernel
theorem subd6_6_369 : subd6_6 [4, 0] = true := by decide +kernel
theorem subd6_6_370 : subd6_6 [4, 1] = true := by decide +kernel
theorem subd6_6_371 : subd6_6 [4, 2] = true := by decide +kernel
theorem subd6_6_372 : subd6_6 [4, 3] = true := by decide +kernel
theorem subd6_6_373 : subd6_6 [4, 4] = true := by decide +kernel
theorem subd6_6_374 : subd6_6 [5, -3] = true := by decide +kernel
theorem subd6_6_375 : subd6_6 [5, -2] = true := by decide +kernel
theorem subd6_6_376 : subd6_6 [5, -1] = true := by decide +kernel
theorem subd6_6_377 : subd6_6 [5, 0] = true := by decide +kernel
theorem subd6_6_378 : subd6_6 [5, 1] = true := by decide +kernel
theorem subd6_6_379 : subd6_6 [5, 2] = true := by decide +kernel
theorem subd6_6_380 : subd6_6 [5, 3] = true := by decide +kernel
theorem sbd6_6_11 : ∀ q ∈ blkd6_6_11, subd6_6 q = true := by
  unfold blkd6_6_11
  exact List.forall_mem_cons.2 ⟨subd6_6_352, List.forall_mem_cons.2 ⟨subd6_6_353, List.forall_mem_cons.2 ⟨subd6_6_354, List.forall_mem_cons.2 ⟨subd6_6_355, List.forall_mem_cons.2 ⟨subd6_6_356, List.forall_mem_cons.2 ⟨subd6_6_357, List.forall_mem_cons.2 ⟨subd6_6_358, List.forall_mem_cons.2 ⟨subd6_6_359, List.forall_mem_cons.2 ⟨subd6_6_360, List.forall_mem_cons.2 ⟨subd6_6_361, List.forall_mem_cons.2 ⟨subd6_6_362, List.forall_mem_cons.2 ⟨subd6_6_363, List.forall_mem_cons.2 ⟨subd6_6_364, List.forall_mem_cons.2 ⟨subd6_6_365, List.forall_mem_cons.2 ⟨subd6_6_366, List.forall_mem_cons.2 ⟨subd6_6_367, List.forall_mem_cons.2 ⟨subd6_6_368, List.forall_mem_cons.2 ⟨subd6_6_369, List.forall_mem_cons.2 ⟨subd6_6_370, List.forall_mem_cons.2 ⟨subd6_6_371, List.forall_mem_cons.2 ⟨subd6_6_372, List.forall_mem_cons.2 ⟨subd6_6_373, List.forall_mem_cons.2 ⟨subd6_6_374, List.forall_mem_cons.2 ⟨subd6_6_375, List.forall_mem_cons.2 ⟨subd6_6_376, List.forall_mem_cons.2 ⟨subd6_6_377, List.forall_mem_cons.2 ⟨subd6_6_378, List.forall_mem_cons.2 ⟨subd6_6_379, List.forall_mem_cons.2 ⟨subd6_6_380, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_7 : ldCheck G d6_7.U d6_7.ms ldd6_7 = true := by decide +kernel
theorem pre_okd6_7 : subPre G cell6 d6_7 = true := by decide +kernel
theorem subd6_7_0 : subd6_7 [-5] = true := by decide +kernel
theorem subd6_7_1 : subd6_7 [-4, -3] = true := by decide +kernel
theorem subd6_7_2 : subd6_7 [-4, -2] = true := by decide +kernel
theorem subd6_7_3 : subd6_7 [-4, -1] = true := by decide +kernel
theorem subd6_7_4 : subd6_7 [-4, 0] = true := by decide +kernel
theorem subd6_7_5 : subd6_7 [-4, 1] = true := by decide +kernel
theorem subd6_7_6 : subd6_7 [-4, 2] = true := by decide +kernel
theorem subd6_7_7 : subd6_7 [-4, 3] = true := by decide +kernel
theorem subd6_7_8 : subd6_7 [-4, 4] = true := by decide +kernel
theorem subd6_7_9 : subd6_7 [-3, -4] = true := by decide +kernel
theorem subd6_7_10 : subd6_7 [-3, -3] = true := by decide +kernel
theorem subd6_7_11 : subd6_7 [-3, -2] = true := by decide +kernel
theorem subd6_7_12 : subd6_7 [-3, -1] = true := by decide +kernel
theorem subd6_7_13 : subd6_7 [-3, 0] = true := by decide +kernel
theorem subd6_7_14 : subd6_7 [-3, 1] = true := by decide +kernel
theorem subd6_7_15 : subd6_7 [-3, 2] = true := by decide +kernel
theorem subd6_7_16 : subd6_7 [-3, 3] = true := by decide +kernel
theorem subd6_7_17 : subd6_7 [-3, 4] = true := by decide +kernel
theorem subd6_7_18 : subd6_7 [-2, -5] = true := by decide +kernel
theorem subd6_7_19 : subd6_7 [-2, -4] = true := by decide +kernel
theorem subd6_7_20 : subd6_7 [-2, -3] = true := by decide +kernel
theorem subd6_7_21 : subd6_7 [-2, -2] = true := by decide +kernel
theorem subd6_7_22 : subd6_7 [-2, -1] = true := by decide +kernel
theorem subd6_7_23 : subd6_7 [-2, 0] = true := by decide +kernel
theorem subd6_7_24 : subd6_7 [-2, 1] = true := by decide +kernel
theorem subd6_7_25 : subd6_7 [-2, 2] = true := by decide +kernel
theorem subd6_7_26 : subd6_7 [-2, 3] = true := by decide +kernel
theorem subd6_7_27 : subd6_7 [-2, 4] = true := by decide +kernel
theorem subd6_7_28 : subd6_7 [-2, 5] = true := by decide +kernel
theorem subd6_7_29 : subd6_7 [-1, -6] = true := by decide +kernel
theorem subd6_7_30 : subd6_7 [-1, -5] = true := by decide +kernel
theorem subd6_7_31 : subd6_7 [-1, -4] = true := by decide +kernel
theorem sbd6_7_0 : ∀ q ∈ blkd6_7_0, subd6_7 q = true := by
  unfold blkd6_7_0
  exact List.forall_mem_cons.2 ⟨subd6_7_0, List.forall_mem_cons.2 ⟨subd6_7_1, List.forall_mem_cons.2 ⟨subd6_7_2, List.forall_mem_cons.2 ⟨subd6_7_3, List.forall_mem_cons.2 ⟨subd6_7_4, List.forall_mem_cons.2 ⟨subd6_7_5, List.forall_mem_cons.2 ⟨subd6_7_6, List.forall_mem_cons.2 ⟨subd6_7_7, List.forall_mem_cons.2 ⟨subd6_7_8, List.forall_mem_cons.2 ⟨subd6_7_9, List.forall_mem_cons.2 ⟨subd6_7_10, List.forall_mem_cons.2 ⟨subd6_7_11, List.forall_mem_cons.2 ⟨subd6_7_12, List.forall_mem_cons.2 ⟨subd6_7_13, List.forall_mem_cons.2 ⟨subd6_7_14, List.forall_mem_cons.2 ⟨subd6_7_15, List.forall_mem_cons.2 ⟨subd6_7_16, List.forall_mem_cons.2 ⟨subd6_7_17, List.forall_mem_cons.2 ⟨subd6_7_18, List.forall_mem_cons.2 ⟨subd6_7_19, List.forall_mem_cons.2 ⟨subd6_7_20, List.forall_mem_cons.2 ⟨subd6_7_21, List.forall_mem_cons.2 ⟨subd6_7_22, List.forall_mem_cons.2 ⟨subd6_7_23, List.forall_mem_cons.2 ⟨subd6_7_24, List.forall_mem_cons.2 ⟨subd6_7_25, List.forall_mem_cons.2 ⟨subd6_7_26, List.forall_mem_cons.2 ⟨subd6_7_27, List.forall_mem_cons.2 ⟨subd6_7_28, List.forall_mem_cons.2 ⟨subd6_7_29, List.forall_mem_cons.2 ⟨subd6_7_30, List.forall_mem_cons.2 ⟨subd6_7_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
