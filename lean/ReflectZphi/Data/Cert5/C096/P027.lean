import ReflectZphi.Data.Cert5.C096.Base

namespace ReflectZphi.Data.Cert5.C096

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_3_224 : subd8_3 [-3, -1, 6] = true := by decide +kernel
theorem subd8_3_225 : subd8_3 [-3, 0, -10] = true := by decide +kernel
theorem subd8_3_226 : subd8_3 [-3, 0, -9] = true := by decide +kernel
theorem subd8_3_227 : subd8_3 [-3, 0, -8] = true := by decide +kernel
theorem subd8_3_228 : subd8_3 [-3, 0, -7] = true := by decide +kernel
theorem subd8_3_229 : subd8_3 [-3, 0, -6] = true := by decide +kernel
theorem subd8_3_230 : subd8_3 [-3, 0, -5] = true := by decide +kernel
theorem subd8_3_231 : subd8_3 [-3, 0, -4] = true := by decide +kernel
theorem subd8_3_232 : subd8_3 [-3, 0, -3] = true := by decide +kernel
theorem subd8_3_233 : subd8_3 [-3, 0, -2] = true := by decide +kernel
theorem subd8_3_234 : subd8_3 [-3, 0, -1] = true := by decide +kernel
theorem subd8_3_235 : subd8_3 [-3, 0, 0] = true := by decide +kernel
theorem subd8_3_236 : subd8_3 [-3, 0, 1] = true := by decide +kernel
theorem subd8_3_237 : subd8_3 [-3, 0, 2] = true := by decide +kernel
theorem subd8_3_238 : subd8_3 [-3, 0, 3] = true := by decide +kernel
theorem subd8_3_239 : subd8_3 [-3, 0, 4] = true := by decide +kernel
theorem subd8_3_240 : subd8_3 [-3, 0, 5] = true := by decide +kernel
theorem subd8_3_241 : subd8_3 [-3, 0, 6] = true := by decide +kernel
theorem subd8_3_242 : subd8_3 [-3, 1, -9] = true := by decide +kernel
theorem subd8_3_243 : subd8_3 [-3, 1, -8] = true := by decide +kernel
theorem subd8_3_244 : subd8_3 [-3, 1, -7] = true := by decide +kernel
theorem subd8_3_245 : subd8_3 [-3, 1, -6] = true := by decide +kernel
theorem subd8_3_246 : subd8_3 [-3, 1, -5] = true := by decide +kernel
theorem subd8_3_247 : subd8_3 [-3, 1, -4] = true := by decide +kernel
theorem subd8_3_248 : subd8_3 [-3, 1, -3] = true := by decide +kernel
theorem subd8_3_249 : subd8_3 [-3, 1, -2] = true := by decide +kernel
theorem subd8_3_250 : subd8_3 [-3, 1, -1] = true := by decide +kernel
theorem subd8_3_251 : subd8_3 [-3, 1, 0] = true := by decide +kernel
theorem subd8_3_252 : subd8_3 [-3, 1, 1] = true := by decide +kernel
theorem subd8_3_253 : subd8_3 [-3, 1, 2] = true := by decide +kernel
theorem subd8_3_254 : subd8_3 [-3, 1, 3] = true := by decide +kernel
theorem subd8_3_255 : subd8_3 [-3, 1, 4] = true := by decide +kernel
theorem sbd8_3_7 : ∀ q ∈ blkd8_3_7, subd8_3 q = true := by
  unfold blkd8_3_7
  exact List.forall_mem_cons.2 ⟨subd8_3_224, List.forall_mem_cons.2 ⟨subd8_3_225, List.forall_mem_cons.2 ⟨subd8_3_226, List.forall_mem_cons.2 ⟨subd8_3_227, List.forall_mem_cons.2 ⟨subd8_3_228, List.forall_mem_cons.2 ⟨subd8_3_229, List.forall_mem_cons.2 ⟨subd8_3_230, List.forall_mem_cons.2 ⟨subd8_3_231, List.forall_mem_cons.2 ⟨subd8_3_232, List.forall_mem_cons.2 ⟨subd8_3_233, List.forall_mem_cons.2 ⟨subd8_3_234, List.forall_mem_cons.2 ⟨subd8_3_235, List.forall_mem_cons.2 ⟨subd8_3_236, List.forall_mem_cons.2 ⟨subd8_3_237, List.forall_mem_cons.2 ⟨subd8_3_238, List.forall_mem_cons.2 ⟨subd8_3_239, List.forall_mem_cons.2 ⟨subd8_3_240, List.forall_mem_cons.2 ⟨subd8_3_241, List.forall_mem_cons.2 ⟨subd8_3_242, List.forall_mem_cons.2 ⟨subd8_3_243, List.forall_mem_cons.2 ⟨subd8_3_244, List.forall_mem_cons.2 ⟨subd8_3_245, List.forall_mem_cons.2 ⟨subd8_3_246, List.forall_mem_cons.2 ⟨subd8_3_247, List.forall_mem_cons.2 ⟨subd8_3_248, List.forall_mem_cons.2 ⟨subd8_3_249, List.forall_mem_cons.2 ⟨subd8_3_250, List.forall_mem_cons.2 ⟨subd8_3_251, List.forall_mem_cons.2 ⟨subd8_3_252, List.forall_mem_cons.2 ⟨subd8_3_253, List.forall_mem_cons.2 ⟨subd8_3_254, List.forall_mem_cons.2 ⟨subd8_3_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_256 : subd8_3 [-3, 1, 5] = true := by decide +kernel
theorem subd8_3_257 : subd8_3 [-3, 1, 6] = true := by decide +kernel
theorem subd8_3_258 : subd8_3 [-3, 1, 7] = true := by decide +kernel
theorem subd8_3_259 : subd8_3 [-3, 2, -8] = true := by decide +kernel
theorem subd8_3_260 : subd8_3 [-3, 2, -7] = true := by decide +kernel
theorem subd8_3_261 : subd8_3 [-3, 2, -6] = true := by decide +kernel
theorem subd8_3_262 : subd8_3 [-3, 2, -5] = true := by decide +kernel
theorem subd8_3_263 : subd8_3 [-3, 2, -4] = true := by decide +kernel
theorem subd8_3_264 : subd8_3 [-3, 2, -3] = true := by decide +kernel
theorem subd8_3_265 : subd8_3 [-3, 2, -2] = true := by decide +kernel
theorem subd8_3_266 : subd8_3 [-3, 2, -1] = true := by decide +kernel
theorem subd8_3_267 : subd8_3 [-3, 2, 0] = true := by decide +kernel
theorem subd8_3_268 : subd8_3 [-3, 2, 1] = true := by decide +kernel
theorem subd8_3_269 : subd8_3 [-3, 2, 2] = true := by decide +kernel
theorem subd8_3_270 : subd8_3 [-3, 2, 3] = true := by decide +kernel
theorem subd8_3_271 : subd8_3 [-3, 2, 4] = true := by decide +kernel
theorem subd8_3_272 : subd8_3 [-3, 2, 5] = true := by decide +kernel
theorem subd8_3_273 : subd8_3 [-3, 2, 6] = true := by decide +kernel
theorem subd8_3_274 : subd8_3 [-3, 2, 7] = true := by decide +kernel
theorem subd8_3_275 : subd8_3 [-3, 3, -7] = true := by decide +kernel
theorem subd8_3_276 : subd8_3 [-3, 3, -6] = true := by decide +kernel
theorem subd8_3_277 : subd8_3 [-3, 3, -5] = true := by decide +kernel
theorem subd8_3_278 : subd8_3 [-3, 3, -4] = true := by decide +kernel
theorem subd8_3_279 : subd8_3 [-3, 3, -3] = true := by decide +kernel
theorem subd8_3_280 : subd8_3 [-3, 3, -2] = true := by decide +kernel
theorem subd8_3_281 : subd8_3 [-3, 3, -1] = true := by decide +kernel
theorem subd8_3_282 : subd8_3 [-3, 3, 0] = true := by decide +kernel
theorem subd8_3_283 : subd8_3 [-3, 3, 1] = true := by decide +kernel
theorem subd8_3_284 : subd8_3 [-3, 3, 2] = true := by decide +kernel
theorem subd8_3_285 : subd8_3 [-3, 3, 3] = true := by decide +kernel
theorem subd8_3_286 : subd8_3 [-3, 3, 4] = true := by decide +kernel
theorem subd8_3_287 : subd8_3 [-3, 3, 5] = true := by decide +kernel
theorem sbd8_3_8 : ∀ q ∈ blkd8_3_8, subd8_3 q = true := by
  unfold blkd8_3_8
  exact List.forall_mem_cons.2 ⟨subd8_3_256, List.forall_mem_cons.2 ⟨subd8_3_257, List.forall_mem_cons.2 ⟨subd8_3_258, List.forall_mem_cons.2 ⟨subd8_3_259, List.forall_mem_cons.2 ⟨subd8_3_260, List.forall_mem_cons.2 ⟨subd8_3_261, List.forall_mem_cons.2 ⟨subd8_3_262, List.forall_mem_cons.2 ⟨subd8_3_263, List.forall_mem_cons.2 ⟨subd8_3_264, List.forall_mem_cons.2 ⟨subd8_3_265, List.forall_mem_cons.2 ⟨subd8_3_266, List.forall_mem_cons.2 ⟨subd8_3_267, List.forall_mem_cons.2 ⟨subd8_3_268, List.forall_mem_cons.2 ⟨subd8_3_269, List.forall_mem_cons.2 ⟨subd8_3_270, List.forall_mem_cons.2 ⟨subd8_3_271, List.forall_mem_cons.2 ⟨subd8_3_272, List.forall_mem_cons.2 ⟨subd8_3_273, List.forall_mem_cons.2 ⟨subd8_3_274, List.forall_mem_cons.2 ⟨subd8_3_275, List.forall_mem_cons.2 ⟨subd8_3_276, List.forall_mem_cons.2 ⟨subd8_3_277, List.forall_mem_cons.2 ⟨subd8_3_278, List.forall_mem_cons.2 ⟨subd8_3_279, List.forall_mem_cons.2 ⟨subd8_3_280, List.forall_mem_cons.2 ⟨subd8_3_281, List.forall_mem_cons.2 ⟨subd8_3_282, List.forall_mem_cons.2 ⟨subd8_3_283, List.forall_mem_cons.2 ⟨subd8_3_284, List.forall_mem_cons.2 ⟨subd8_3_285, List.forall_mem_cons.2 ⟨subd8_3_286, List.forall_mem_cons.2 ⟨subd8_3_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_288 : subd8_3 [-3, 3, 6] = true := by decide +kernel
theorem subd8_3_289 : subd8_3 [-3, 4] = true := by decide +kernel
theorem subd8_3_290 : subd8_3 [-3, 5] = true := by decide +kernel
theorem subd8_3_291 : subd8_3 [-2, -8] = true := by decide +kernel
theorem subd8_3_292 : subd8_3 [-2, -7] = true := by decide +kernel
theorem subd8_3_293 : subd8_3 [-2, -6] = true := by decide +kernel
theorem subd8_3_294 : subd8_3 [-2, -5, -10] = true := by decide +kernel
theorem subd8_3_295 : subd8_3 [-2, -5, -9] = true := by decide +kernel
theorem subd8_3_296 : subd8_3 [-2, -5, -8] = true := by decide +kernel
theorem subd8_3_297 : subd8_3 [-2, -5, -7] = true := by decide +kernel
theorem subd8_3_298 : subd8_3 [-2, -5, -6] = true := by decide +kernel
theorem subd8_3_299 : subd8_3 [-2, -5, -5] = true := by decide +kernel
theorem subd8_3_300 : subd8_3 [-2, -5, -4] = true := by decide +kernel
theorem subd8_3_301 : subd8_3 [-2, -5, -3] = true := by decide +kernel
theorem subd8_3_302 : subd8_3 [-2, -5, -2] = true := by decide +kernel
theorem subd8_3_303 : subd8_3 [-2, -5, -1] = true := by decide +kernel
theorem subd8_3_304 : subd8_3 [-2, -5, 0] = true := by decide +kernel
theorem subd8_3_305 : subd8_3 [-2, -5, 1] = true := by decide +kernel
theorem subd8_3_306 : subd8_3 [-2, -5, 2] = true := by decide +kernel
theorem subd8_3_307 : subd8_3 [-2, -5, 3] = true := by decide +kernel
theorem subd8_3_308 : subd8_3 [-2, -5, 4] = true := by decide +kernel
theorem subd8_3_309 : subd8_3 [-2, -4, -11] = true := by decide +kernel
theorem subd8_3_310 : subd8_3 [-2, -4, -10] = true := by decide +kernel
theorem subd8_3_311 : subd8_3 [-2, -4, -9] = true := by decide +kernel
theorem subd8_3_312 : subd8_3 [-2, -4, -8] = true := by decide +kernel
theorem subd8_3_313 : subd8_3 [-2, -4, -7] = true := by decide +kernel
theorem subd8_3_314 : subd8_3 [-2, -4, -6] = true := by decide +kernel
theorem subd8_3_315 : subd8_3 [-2, -4, -5] = true := by decide +kernel
theorem subd8_3_316 : subd8_3 [-2, -4, -4] = true := by decide +kernel
theorem subd8_3_317 : subd8_3 [-2, -4, -3] = true := by decide +kernel
theorem subd8_3_318 : subd8_3 [-2, -4, -2] = true := by decide +kernel
theorem subd8_3_319 : subd8_3 [-2, -4, -1] = true := by decide +kernel
theorem sbd8_3_9 : ∀ q ∈ blkd8_3_9, subd8_3 q = true := by
  unfold blkd8_3_9
  exact List.forall_mem_cons.2 ⟨subd8_3_288, List.forall_mem_cons.2 ⟨subd8_3_289, List.forall_mem_cons.2 ⟨subd8_3_290, List.forall_mem_cons.2 ⟨subd8_3_291, List.forall_mem_cons.2 ⟨subd8_3_292, List.forall_mem_cons.2 ⟨subd8_3_293, List.forall_mem_cons.2 ⟨subd8_3_294, List.forall_mem_cons.2 ⟨subd8_3_295, List.forall_mem_cons.2 ⟨subd8_3_296, List.forall_mem_cons.2 ⟨subd8_3_297, List.forall_mem_cons.2 ⟨subd8_3_298, List.forall_mem_cons.2 ⟨subd8_3_299, List.forall_mem_cons.2 ⟨subd8_3_300, List.forall_mem_cons.2 ⟨subd8_3_301, List.forall_mem_cons.2 ⟨subd8_3_302, List.forall_mem_cons.2 ⟨subd8_3_303, List.forall_mem_cons.2 ⟨subd8_3_304, List.forall_mem_cons.2 ⟨subd8_3_305, List.forall_mem_cons.2 ⟨subd8_3_306, List.forall_mem_cons.2 ⟨subd8_3_307, List.forall_mem_cons.2 ⟨subd8_3_308, List.forall_mem_cons.2 ⟨subd8_3_309, List.forall_mem_cons.2 ⟨subd8_3_310, List.forall_mem_cons.2 ⟨subd8_3_311, List.forall_mem_cons.2 ⟨subd8_3_312, List.forall_mem_cons.2 ⟨subd8_3_313, List.forall_mem_cons.2 ⟨subd8_3_314, List.forall_mem_cons.2 ⟨subd8_3_315, List.forall_mem_cons.2 ⟨subd8_3_316, List.forall_mem_cons.2 ⟨subd8_3_317, List.forall_mem_cons.2 ⟨subd8_3_318, List.forall_mem_cons.2 ⟨subd8_3_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_320 : subd8_3 [-2, -4, 0] = true := by decide +kernel
theorem subd8_3_321 : subd8_3 [-2, -4, 1] = true := by decide +kernel
theorem subd8_3_322 : subd8_3 [-2, -4, 2] = true := by decide +kernel
theorem subd8_3_323 : subd8_3 [-2, -4, 3] = true := by decide +kernel
theorem subd8_3_324 : subd8_3 [-2, -4, 4] = true := by decide +kernel
theorem subd8_3_325 : subd8_3 [-2, -4, 5] = true := by decide +kernel
theorem subd8_3_326 : subd8_3 [-2, -3, -11] = true := by decide +kernel
theorem subd8_3_327 : subd8_3 [-2, -3, -10] = true := by decide +kernel
theorem subd8_3_328 : subd8_3 [-2, -3, -9] = true := by decide +kernel
theorem subd8_3_329 : subd8_3 [-2, -3, -8] = true := by decide +kernel
theorem subd8_3_330 : subd8_3 [-2, -3, -7] = true := by decide +kernel
theorem subd8_3_331 : subd8_3 [-2, -3, -6] = true := by decide +kernel
theorem subd8_3_332 : subd8_3 [-2, -3, -5] = true := by decide +kernel
theorem subd8_3_333 : subd8_3 [-2, -3, -4] = true := by decide +kernel
theorem subd8_3_334 : subd8_3 [-2, -3, -3] = true := by decide +kernel
theorem subd8_3_335 : subd8_3 [-2, -3, -2] = true := by decide +kernel
theorem subd8_3_336 : subd8_3 [-2, -3, -1] = true := by decide +kernel
theorem subd8_3_337 : subd8_3 [-2, -3, 0] = true := by decide +kernel
theorem subd8_3_338 : subd8_3 [-2, -3, 1] = true := by decide +kernel
theorem subd8_3_339 : subd8_3 [-2, -3, 2] = true := by decide +kernel
theorem subd8_3_340 : subd8_3 [-2, -3, 3] = true := by decide +kernel
theorem subd8_3_341 : subd8_3 [-2, -3, 4] = true := by decide +kernel
theorem subd8_3_342 : subd8_3 [-2, -3, 5] = true := by decide +kernel
theorem subd8_3_343 : subd8_3 [-2, -3, 6] = true := by decide +kernel
theorem subd8_3_344 : subd8_3 [-2, -2, -11] = true := by decide +kernel
theorem subd8_3_345 : subd8_3 [-2, -2, -10] = true := by decide +kernel
theorem subd8_3_346 : subd8_3 [-2, -2, -9] = true := by decide +kernel
theorem subd8_3_347 : subd8_3 [-2, -2, -8] = true := by decide +kernel
theorem subd8_3_348 : subd8_3 [-2, -2, -7] = true := by decide +kernel
theorem subd8_3_349 : subd8_3 [-2, -2, -6] = true := by decide +kernel
theorem subd8_3_350 : subd8_3 [-2, -2, -5] = true := by decide +kernel
theorem subd8_3_351 : subd8_3 [-2, -2, -4] = true := by decide +kernel
theorem sbd8_3_10 : ∀ q ∈ blkd8_3_10, subd8_3 q = true := by
  unfold blkd8_3_10
  exact List.forall_mem_cons.2 ⟨subd8_3_320, List.forall_mem_cons.2 ⟨subd8_3_321, List.forall_mem_cons.2 ⟨subd8_3_322, List.forall_mem_cons.2 ⟨subd8_3_323, List.forall_mem_cons.2 ⟨subd8_3_324, List.forall_mem_cons.2 ⟨subd8_3_325, List.forall_mem_cons.2 ⟨subd8_3_326, List.forall_mem_cons.2 ⟨subd8_3_327, List.forall_mem_cons.2 ⟨subd8_3_328, List.forall_mem_cons.2 ⟨subd8_3_329, List.forall_mem_cons.2 ⟨subd8_3_330, List.forall_mem_cons.2 ⟨subd8_3_331, List.forall_mem_cons.2 ⟨subd8_3_332, List.forall_mem_cons.2 ⟨subd8_3_333, List.forall_mem_cons.2 ⟨subd8_3_334, List.forall_mem_cons.2 ⟨subd8_3_335, List.forall_mem_cons.2 ⟨subd8_3_336, List.forall_mem_cons.2 ⟨subd8_3_337, List.forall_mem_cons.2 ⟨subd8_3_338, List.forall_mem_cons.2 ⟨subd8_3_339, List.forall_mem_cons.2 ⟨subd8_3_340, List.forall_mem_cons.2 ⟨subd8_3_341, List.forall_mem_cons.2 ⟨subd8_3_342, List.forall_mem_cons.2 ⟨subd8_3_343, List.forall_mem_cons.2 ⟨subd8_3_344, List.forall_mem_cons.2 ⟨subd8_3_345, List.forall_mem_cons.2 ⟨subd8_3_346, List.forall_mem_cons.2 ⟨subd8_3_347, List.forall_mem_cons.2 ⟨subd8_3_348, List.forall_mem_cons.2 ⟨subd8_3_349, List.forall_mem_cons.2 ⟨subd8_3_350, List.forall_mem_cons.2 ⟨subd8_3_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_352 : subd8_3 [-2, -2, -3] = true := by decide +kernel
theorem subd8_3_353 : subd8_3 [-2, -2, -2] = true := by decide +kernel
theorem subd8_3_354 : subd8_3 [-2, -2, -1] = true := by decide +kernel
theorem subd8_3_355 : subd8_3 [-2, -2, 0] = true := by decide +kernel
theorem subd8_3_356 : subd8_3 [-2, -2, 1] = true := by decide +kernel
theorem subd8_3_357 : subd8_3 [-2, -2, 2] = true := by decide +kernel
theorem subd8_3_358 : subd8_3 [-2, -2, 3] = true := by decide +kernel
theorem subd8_3_359 : subd8_3 [-2, -2, 4] = true := by decide +kernel
theorem subd8_3_360 : subd8_3 [-2, -2, 5] = true := by decide +kernel
theorem subd8_3_361 : subd8_3 [-2, -2, 6] = true := by decide +kernel
theorem subd8_3_362 : subd8_3 [-2, -1, -10] = true := by decide +kernel
theorem subd8_3_363 : subd8_3 [-2, -1, -9] = true := by decide +kernel
theorem subd8_3_364 : subd8_3 [-2, -1, -8] = true := by decide +kernel
theorem subd8_3_365 : subd8_3 [-2, -1, -7] = true := by decide +kernel
theorem subd8_3_366 : subd8_3 [-2, -1, -6] = true := by decide +kernel
theorem subd8_3_367 : subd8_3 [-2, -1, -5] = true := by decide +kernel
theorem subd8_3_368 : subd8_3 [-2, -1, -4] = true := by decide +kernel
theorem subd8_3_369 : subd8_3 [-2, -1, -3] = true := by decide +kernel
theorem subd8_3_370 : subd8_3 [-2, -1, -2] = true := by decide +kernel
theorem subd8_3_371 : subd8_3 [-2, -1, -1] = true := by decide +kernel
theorem subd8_3_372 : subd8_3 [-2, -1, 0] = true := by decide +kernel
theorem subd8_3_373 : subd8_3 [-2, -1, 1] = true := by decide +kernel
theorem subd8_3_374 : subd8_3 [-2, -1, 2] = true := by decide +kernel
theorem subd8_3_375 : subd8_3 [-2, -1, 3] = true := by decide +kernel
theorem subd8_3_376 : subd8_3 [-2, -1, 4] = true := by decide +kernel
theorem subd8_3_377 : subd8_3 [-2, -1, 5] = true := by decide +kernel
theorem subd8_3_378 : subd8_3 [-2, -1, 6] = true := by decide +kernel
theorem subd8_3_379 : subd8_3 [-2, -1, 7] = true := by decide +kernel
theorem subd8_3_380 : subd8_3 [-2, 0, -10] = true := by decide +kernel
theorem subd8_3_381 : subd8_3 [-2, 0, -9] = true := by decide +kernel
theorem subd8_3_382 : subd8_3 [-2, 0, -8] = true := by decide +kernel
theorem subd8_3_383 : subd8_3 [-2, 0, -7] = true := by decide +kernel
theorem sbd8_3_11 : ∀ q ∈ blkd8_3_11, subd8_3 q = true := by
  unfold blkd8_3_11
  exact List.forall_mem_cons.2 ⟨subd8_3_352, List.forall_mem_cons.2 ⟨subd8_3_353, List.forall_mem_cons.2 ⟨subd8_3_354, List.forall_mem_cons.2 ⟨subd8_3_355, List.forall_mem_cons.2 ⟨subd8_3_356, List.forall_mem_cons.2 ⟨subd8_3_357, List.forall_mem_cons.2 ⟨subd8_3_358, List.forall_mem_cons.2 ⟨subd8_3_359, List.forall_mem_cons.2 ⟨subd8_3_360, List.forall_mem_cons.2 ⟨subd8_3_361, List.forall_mem_cons.2 ⟨subd8_3_362, List.forall_mem_cons.2 ⟨subd8_3_363, List.forall_mem_cons.2 ⟨subd8_3_364, List.forall_mem_cons.2 ⟨subd8_3_365, List.forall_mem_cons.2 ⟨subd8_3_366, List.forall_mem_cons.2 ⟨subd8_3_367, List.forall_mem_cons.2 ⟨subd8_3_368, List.forall_mem_cons.2 ⟨subd8_3_369, List.forall_mem_cons.2 ⟨subd8_3_370, List.forall_mem_cons.2 ⟨subd8_3_371, List.forall_mem_cons.2 ⟨subd8_3_372, List.forall_mem_cons.2 ⟨subd8_3_373, List.forall_mem_cons.2 ⟨subd8_3_374, List.forall_mem_cons.2 ⟨subd8_3_375, List.forall_mem_cons.2 ⟨subd8_3_376, List.forall_mem_cons.2 ⟨subd8_3_377, List.forall_mem_cons.2 ⟨subd8_3_378, List.forall_mem_cons.2 ⟨subd8_3_379, List.forall_mem_cons.2 ⟨subd8_3_380, List.forall_mem_cons.2 ⟨subd8_3_381, List.forall_mem_cons.2 ⟨subd8_3_382, List.forall_mem_cons.2 ⟨subd8_3_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_384 : subd8_3 [-2, 0, -6] = true := by decide +kernel
theorem subd8_3_385 : subd8_3 [-2, 0, -5] = true := by decide +kernel
theorem subd8_3_386 : subd8_3 [-2, 0, -4] = true := by decide +kernel
theorem subd8_3_387 : subd8_3 [-2, 0, -3] = true := by decide +kernel
theorem subd8_3_388 : subd8_3 [-2, 0, -2] = true := by decide +kernel
theorem subd8_3_389 : subd8_3 [-2, 0, -1] = true := by decide +kernel
theorem subd8_3_390 : subd8_3 [-2, 0, 0] = true := by decide +kernel
theorem subd8_3_391 : subd8_3 [-2, 0, 1] = true := by decide +kernel
theorem subd8_3_392 : subd8_3 [-2, 0, 2] = true := by decide +kernel
theorem subd8_3_393 : subd8_3 [-2, 0, 3] = true := by decide +kernel
theorem subd8_3_394 : subd8_3 [-2, 0, 4] = true := by decide +kernel
theorem subd8_3_395 : subd8_3 [-2, 0, 5] = true := by decide +kernel
theorem subd8_3_396 : subd8_3 [-2, 0, 6] = true := by decide +kernel
theorem subd8_3_397 : subd8_3 [-2, 0, 7] = true := by decide +kernel
theorem subd8_3_398 : subd8_3 [-2, 1, -9] = true := by decide +kernel
theorem subd8_3_399 : subd8_3 [-2, 1, -8] = true := by decide +kernel
theorem subd8_3_400 : subd8_3 [-2, 1, -7] = true := by decide +kernel
theorem subd8_3_401 : subd8_3 [-2, 1, -6] = true := by decide +kernel
theorem subd8_3_402 : subd8_3 [-2, 1, -5] = true := by decide +kernel
theorem subd8_3_403 : subd8_3 [-2, 1, -4] = true := by decide +kernel
theorem subd8_3_404 : subd8_3 [-2, 1, -3] = true := by decide +kernel
theorem subd8_3_405 : subd8_3 [-2, 1, -2] = true := by decide +kernel
theorem subd8_3_406 : subd8_3 [-2, 1, -1] = true := by decide +kernel
theorem subd8_3_407 : subd8_3 [-2, 1, 0] = true := by decide +kernel
theorem subd8_3_408 : subd8_3 [-2, 1, 1] = true := by decide +kernel
theorem subd8_3_409 : subd8_3 [-2, 1, 2] = true := by decide +kernel
theorem subd8_3_410 : subd8_3 [-2, 1, 3] = true := by decide +kernel
theorem subd8_3_411 : subd8_3 [-2, 1, 4] = true := by decide +kernel
theorem subd8_3_412 : subd8_3 [-2, 1, 5] = true := by decide +kernel
theorem subd8_3_413 : subd8_3 [-2, 1, 6] = true := by decide +kernel
theorem subd8_3_414 : subd8_3 [-2, 1, 7] = true := by decide +kernel
theorem subd8_3_415 : subd8_3 [-2, 1, 8] = true := by decide +kernel
theorem sbd8_3_12 : ∀ q ∈ blkd8_3_12, subd8_3 q = true := by
  unfold blkd8_3_12
  exact List.forall_mem_cons.2 ⟨subd8_3_384, List.forall_mem_cons.2 ⟨subd8_3_385, List.forall_mem_cons.2 ⟨subd8_3_386, List.forall_mem_cons.2 ⟨subd8_3_387, List.forall_mem_cons.2 ⟨subd8_3_388, List.forall_mem_cons.2 ⟨subd8_3_389, List.forall_mem_cons.2 ⟨subd8_3_390, List.forall_mem_cons.2 ⟨subd8_3_391, List.forall_mem_cons.2 ⟨subd8_3_392, List.forall_mem_cons.2 ⟨subd8_3_393, List.forall_mem_cons.2 ⟨subd8_3_394, List.forall_mem_cons.2 ⟨subd8_3_395, List.forall_mem_cons.2 ⟨subd8_3_396, List.forall_mem_cons.2 ⟨subd8_3_397, List.forall_mem_cons.2 ⟨subd8_3_398, List.forall_mem_cons.2 ⟨subd8_3_399, List.forall_mem_cons.2 ⟨subd8_3_400, List.forall_mem_cons.2 ⟨subd8_3_401, List.forall_mem_cons.2 ⟨subd8_3_402, List.forall_mem_cons.2 ⟨subd8_3_403, List.forall_mem_cons.2 ⟨subd8_3_404, List.forall_mem_cons.2 ⟨subd8_3_405, List.forall_mem_cons.2 ⟨subd8_3_406, List.forall_mem_cons.2 ⟨subd8_3_407, List.forall_mem_cons.2 ⟨subd8_3_408, List.forall_mem_cons.2 ⟨subd8_3_409, List.forall_mem_cons.2 ⟨subd8_3_410, List.forall_mem_cons.2 ⟨subd8_3_411, List.forall_mem_cons.2 ⟨subd8_3_412, List.forall_mem_cons.2 ⟨subd8_3_413, List.forall_mem_cons.2 ⟨subd8_3_414, List.forall_mem_cons.2 ⟨subd8_3_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_416 : subd8_3 [-2, 2, -9] = true := by decide +kernel
theorem subd8_3_417 : subd8_3 [-2, 2, -8] = true := by decide +kernel
theorem subd8_3_418 : subd8_3 [-2, 2, -7] = true := by decide +kernel
theorem subd8_3_419 : subd8_3 [-2, 2, -6] = true := by decide +kernel
theorem subd8_3_420 : subd8_3 [-2, 2, -5] = true := by decide +kernel
theorem subd8_3_421 : subd8_3 [-2, 2, -4] = true := by decide +kernel
theorem subd8_3_422 : subd8_3 [-2, 2, -3] = true := by decide +kernel
theorem subd8_3_423 : subd8_3 [-2, 2, -2] = true := by decide +kernel
theorem subd8_3_424 : subd8_3 [-2, 2, -1] = true := by decide +kernel
theorem subd8_3_425 : subd8_3 [-2, 2, 0] = true := by decide +kernel
theorem subd8_3_426 : subd8_3 [-2, 2, 1] = true := by decide +kernel
theorem subd8_3_427 : subd8_3 [-2, 2, 2] = true := by decide +kernel
theorem subd8_3_428 : subd8_3 [-2, 2, 3] = true := by decide +kernel
theorem subd8_3_429 : subd8_3 [-2, 2, 4] = true := by decide +kernel
theorem subd8_3_430 : subd8_3 [-2, 2, 5] = true := by decide +kernel
theorem subd8_3_431 : subd8_3 [-2, 2, 6] = true := by decide +kernel
theorem subd8_3_432 : subd8_3 [-2, 2, 7] = true := by decide +kernel
theorem subd8_3_433 : subd8_3 [-2, 2, 8] = true := by decide +kernel
theorem subd8_3_434 : subd8_3 [-2, 3, -8] = true := by decide +kernel
theorem subd8_3_435 : subd8_3 [-2, 3, -7] = true := by decide +kernel
theorem subd8_3_436 : subd8_3 [-2, 3, -6] = true := by decide +kernel
theorem subd8_3_437 : subd8_3 [-2, 3, -5] = true := by decide +kernel
theorem subd8_3_438 : subd8_3 [-2, 3, -4] = true := by decide +kernel
theorem subd8_3_439 : subd8_3 [-2, 3, -3] = true := by decide +kernel
theorem subd8_3_440 : subd8_3 [-2, 3, -2] = true := by decide +kernel
theorem subd8_3_441 : subd8_3 [-2, 3, -1] = true := by decide +kernel
theorem subd8_3_442 : subd8_3 [-2, 3, 0] = true := by decide +kernel
theorem subd8_3_443 : subd8_3 [-2, 3, 1] = true := by decide +kernel
theorem subd8_3_444 : subd8_3 [-2, 3, 2] = true := by decide +kernel
theorem subd8_3_445 : subd8_3 [-2, 3, 3] = true := by decide +kernel
theorem subd8_3_446 : subd8_3 [-2, 3, 4] = true := by decide +kernel
theorem subd8_3_447 : subd8_3 [-2, 3, 5] = true := by decide +kernel
theorem sbd8_3_13 : ∀ q ∈ blkd8_3_13, subd8_3 q = true := by
  unfold blkd8_3_13
  exact List.forall_mem_cons.2 ⟨subd8_3_416, List.forall_mem_cons.2 ⟨subd8_3_417, List.forall_mem_cons.2 ⟨subd8_3_418, List.forall_mem_cons.2 ⟨subd8_3_419, List.forall_mem_cons.2 ⟨subd8_3_420, List.forall_mem_cons.2 ⟨subd8_3_421, List.forall_mem_cons.2 ⟨subd8_3_422, List.forall_mem_cons.2 ⟨subd8_3_423, List.forall_mem_cons.2 ⟨subd8_3_424, List.forall_mem_cons.2 ⟨subd8_3_425, List.forall_mem_cons.2 ⟨subd8_3_426, List.forall_mem_cons.2 ⟨subd8_3_427, List.forall_mem_cons.2 ⟨subd8_3_428, List.forall_mem_cons.2 ⟨subd8_3_429, List.forall_mem_cons.2 ⟨subd8_3_430, List.forall_mem_cons.2 ⟨subd8_3_431, List.forall_mem_cons.2 ⟨subd8_3_432, List.forall_mem_cons.2 ⟨subd8_3_433, List.forall_mem_cons.2 ⟨subd8_3_434, List.forall_mem_cons.2 ⟨subd8_3_435, List.forall_mem_cons.2 ⟨subd8_3_436, List.forall_mem_cons.2 ⟨subd8_3_437, List.forall_mem_cons.2 ⟨subd8_3_438, List.forall_mem_cons.2 ⟨subd8_3_439, List.forall_mem_cons.2 ⟨subd8_3_440, List.forall_mem_cons.2 ⟨subd8_3_441, List.forall_mem_cons.2 ⟨subd8_3_442, List.forall_mem_cons.2 ⟨subd8_3_443, List.forall_mem_cons.2 ⟨subd8_3_444, List.forall_mem_cons.2 ⟨subd8_3_445, List.forall_mem_cons.2 ⟨subd8_3_446, List.forall_mem_cons.2 ⟨subd8_3_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_448 : subd8_3 [-2, 3, 6] = true := by decide +kernel
theorem subd8_3_449 : subd8_3 [-2, 3, 7] = true := by decide +kernel
theorem subd8_3_450 : subd8_3 [-2, 3, 8] = true := by decide +kernel
theorem subd8_3_451 : subd8_3 [-2, 4, -6] = true := by decide +kernel
theorem subd8_3_452 : subd8_3 [-2, 4, -5] = true := by decide +kernel
theorem subd8_3_453 : subd8_3 [-2, 4, -4] = true := by decide +kernel
theorem subd8_3_454 : subd8_3 [-2, 4, -3] = true := by decide +kernel
theorem subd8_3_455 : subd8_3 [-2, 4, -2] = true := by decide +kernel
theorem subd8_3_456 : subd8_3 [-2, 4, -1] = true := by decide +kernel
theorem subd8_3_457 : subd8_3 [-2, 4, 0] = true := by decide +kernel
theorem subd8_3_458 : subd8_3 [-2, 4, 1] = true := by decide +kernel
theorem subd8_3_459 : subd8_3 [-2, 4, 2] = true := by decide +kernel
theorem subd8_3_460 : subd8_3 [-2, 4, 3] = true := by decide +kernel
theorem subd8_3_461 : subd8_3 [-2, 4, 4] = true := by decide +kernel
theorem subd8_3_462 : subd8_3 [-2, 4, 5] = true := by decide +kernel
theorem subd8_3_463 : subd8_3 [-2, 4, 6] = true := by decide +kernel
theorem subd8_3_464 : subd8_3 [-2, 4, 7] = true := by decide +kernel
theorem subd8_3_465 : subd8_3 [-2, 5] = true := by decide +kernel
theorem subd8_3_466 : subd8_3 [-2, 6] = true := by decide +kernel
theorem subd8_3_467 : subd8_3 [-1, -8] = true := by decide +kernel
theorem subd8_3_468 : subd8_3 [-1, -7] = true := by decide +kernel
theorem subd8_3_469 : subd8_3 [-1, -6] = true := by decide +kernel
theorem subd8_3_470 : subd8_3 [-1, -5, -10] = true := by decide +kernel
theorem subd8_3_471 : subd8_3 [-1, -5, -9] = true := by decide +kernel
theorem subd8_3_472 : subd8_3 [-1, -5, -8] = true := by decide +kernel
theorem subd8_3_473 : subd8_3 [-1, -5, -7] = true := by decide +kernel
theorem subd8_3_474 : subd8_3 [-1, -5, -6] = true := by decide +kernel
theorem subd8_3_475 : subd8_3 [-1, -5, -5] = true := by decide +kernel
theorem subd8_3_476 : subd8_3 [-1, -5, -4] = true := by decide +kernel
theorem subd8_3_477 : subd8_3 [-1, -5, -3] = true := by decide +kernel
theorem subd8_3_478 : subd8_3 [-1, -5, -2] = true := by decide +kernel
theorem subd8_3_479 : subd8_3 [-1, -5, -1] = true := by decide +kernel
theorem sbd8_3_14 : ∀ q ∈ blkd8_3_14, subd8_3 q = true := by
  unfold blkd8_3_14
  exact List.forall_mem_cons.2 ⟨subd8_3_448, List.forall_mem_cons.2 ⟨subd8_3_449, List.forall_mem_cons.2 ⟨subd8_3_450, List.forall_mem_cons.2 ⟨subd8_3_451, List.forall_mem_cons.2 ⟨subd8_3_452, List.forall_mem_cons.2 ⟨subd8_3_453, List.forall_mem_cons.2 ⟨subd8_3_454, List.forall_mem_cons.2 ⟨subd8_3_455, List.forall_mem_cons.2 ⟨subd8_3_456, List.forall_mem_cons.2 ⟨subd8_3_457, List.forall_mem_cons.2 ⟨subd8_3_458, List.forall_mem_cons.2 ⟨subd8_3_459, List.forall_mem_cons.2 ⟨subd8_3_460, List.forall_mem_cons.2 ⟨subd8_3_461, List.forall_mem_cons.2 ⟨subd8_3_462, List.forall_mem_cons.2 ⟨subd8_3_463, List.forall_mem_cons.2 ⟨subd8_3_464, List.forall_mem_cons.2 ⟨subd8_3_465, List.forall_mem_cons.2 ⟨subd8_3_466, List.forall_mem_cons.2 ⟨subd8_3_467, List.forall_mem_cons.2 ⟨subd8_3_468, List.forall_mem_cons.2 ⟨subd8_3_469, List.forall_mem_cons.2 ⟨subd8_3_470, List.forall_mem_cons.2 ⟨subd8_3_471, List.forall_mem_cons.2 ⟨subd8_3_472, List.forall_mem_cons.2 ⟨subd8_3_473, List.forall_mem_cons.2 ⟨subd8_3_474, List.forall_mem_cons.2 ⟨subd8_3_475, List.forall_mem_cons.2 ⟨subd8_3_476, List.forall_mem_cons.2 ⟨subd8_3_477, List.forall_mem_cons.2 ⟨subd8_3_478, List.forall_mem_cons.2 ⟨subd8_3_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_480 : subd8_3 [-1, -5, 0] = true := by decide +kernel
theorem subd8_3_481 : subd8_3 [-1, -5, 1] = true := by decide +kernel
theorem subd8_3_482 : subd8_3 [-1, -5, 2] = true := by decide +kernel
theorem subd8_3_483 : subd8_3 [-1, -5, 3] = true := by decide +kernel
theorem subd8_3_484 : subd8_3 [-1, -5, 4] = true := by decide +kernel
theorem subd8_3_485 : subd8_3 [-1, -4, -10] = true := by decide +kernel
theorem subd8_3_486 : subd8_3 [-1, -4, -9] = true := by decide +kernel
theorem subd8_3_487 : subd8_3 [-1, -4, -8] = true := by decide +kernel
theorem subd8_3_488 : subd8_3 [-1, -4, -7] = true := by decide +kernel
theorem subd8_3_489 : subd8_3 [-1, -4, -6] = true := by decide +kernel
theorem subd8_3_490 : subd8_3 [-1, -4, -5] = true := by decide +kernel
theorem subd8_3_491 : subd8_3 [-1, -4, -4] = true := by decide +kernel
theorem subd8_3_492 : subd8_3 [-1, -4, -3] = true := by decide +kernel
theorem subd8_3_493 : subd8_3 [-1, -4, -2] = true := by decide +kernel
theorem subd8_3_494 : subd8_3 [-1, -4, -1] = true := by decide +kernel
theorem subd8_3_495 : subd8_3 [-1, -4, 0] = true := by decide +kernel
theorem subd8_3_496 : subd8_3 [-1, -4, 1] = true := by decide +kernel
theorem subd8_3_497 : subd8_3 [-1, -4, 2] = true := by decide +kernel
theorem subd8_3_498 : subd8_3 [-1, -4, 3] = true := by decide +kernel
theorem subd8_3_499 : subd8_3 [-1, -4, 4] = true := by decide +kernel
theorem subd8_3_500 : subd8_3 [-1, -4, 5] = true := by decide +kernel
theorem subd8_3_501 : subd8_3 [-1, -3, -11] = true := by decide +kernel
theorem subd8_3_502 : subd8_3 [-1, -3, -10] = true := by decide +kernel
theorem subd8_3_503 : subd8_3 [-1, -3, -9] = true := by decide +kernel
theorem subd8_3_504 : subd8_3 [-1, -3, -8] = true := by decide +kernel
theorem subd8_3_505 : subd8_3 [-1, -3, -7] = true := by decide +kernel
theorem subd8_3_506 : subd8_3 [-1, -3, -6] = true := by decide +kernel
theorem subd8_3_507 : subd8_3 [-1, -3, -5] = true := by decide +kernel
theorem subd8_3_508 : subd8_3 [-1, -3, -4] = true := by decide +kernel
theorem subd8_3_509 : subd8_3 [-1, -3, -3] = true := by decide +kernel
theorem subd8_3_510 : subd8_3 [-1, -3, -2] = true := by decide +kernel
theorem subd8_3_511 : subd8_3 [-1, -3, -1] = true := by decide +kernel
theorem sbd8_3_15 : ∀ q ∈ blkd8_3_15, subd8_3 q = true := by
  unfold blkd8_3_15
  exact List.forall_mem_cons.2 ⟨subd8_3_480, List.forall_mem_cons.2 ⟨subd8_3_481, List.forall_mem_cons.2 ⟨subd8_3_482, List.forall_mem_cons.2 ⟨subd8_3_483, List.forall_mem_cons.2 ⟨subd8_3_484, List.forall_mem_cons.2 ⟨subd8_3_485, List.forall_mem_cons.2 ⟨subd8_3_486, List.forall_mem_cons.2 ⟨subd8_3_487, List.forall_mem_cons.2 ⟨subd8_3_488, List.forall_mem_cons.2 ⟨subd8_3_489, List.forall_mem_cons.2 ⟨subd8_3_490, List.forall_mem_cons.2 ⟨subd8_3_491, List.forall_mem_cons.2 ⟨subd8_3_492, List.forall_mem_cons.2 ⟨subd8_3_493, List.forall_mem_cons.2 ⟨subd8_3_494, List.forall_mem_cons.2 ⟨subd8_3_495, List.forall_mem_cons.2 ⟨subd8_3_496, List.forall_mem_cons.2 ⟨subd8_3_497, List.forall_mem_cons.2 ⟨subd8_3_498, List.forall_mem_cons.2 ⟨subd8_3_499, List.forall_mem_cons.2 ⟨subd8_3_500, List.forall_mem_cons.2 ⟨subd8_3_501, List.forall_mem_cons.2 ⟨subd8_3_502, List.forall_mem_cons.2 ⟨subd8_3_503, List.forall_mem_cons.2 ⟨subd8_3_504, List.forall_mem_cons.2 ⟨subd8_3_505, List.forall_mem_cons.2 ⟨subd8_3_506, List.forall_mem_cons.2 ⟨subd8_3_507, List.forall_mem_cons.2 ⟨subd8_3_508, List.forall_mem_cons.2 ⟨subd8_3_509, List.forall_mem_cons.2 ⟨subd8_3_510, List.forall_mem_cons.2 ⟨subd8_3_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_512 : subd8_3 [-1, -3, 0] = true := by decide +kernel
theorem subd8_3_513 : subd8_3 [-1, -3, 1] = true := by decide +kernel
theorem subd8_3_514 : subd8_3 [-1, -3, 2] = true := by decide +kernel
theorem subd8_3_515 : subd8_3 [-1, -3, 3] = true := by decide +kernel
theorem subd8_3_516 : subd8_3 [-1, -3, 4] = true := by decide +kernel
theorem subd8_3_517 : subd8_3 [-1, -3, 5] = true := by decide +kernel
theorem subd8_3_518 : subd8_3 [-1, -3, 6] = true := by decide +kernel
theorem subd8_3_519 : subd8_3 [-1, -2, -11] = true := by decide +kernel
theorem subd8_3_520 : subd8_3 [-1, -2, -10] = true := by decide +kernel
theorem subd8_3_521 : subd8_3 [-1, -2, -9] = true := by decide +kernel
theorem subd8_3_522 : subd8_3 [-1, -2, -8] = true := by decide +kernel
theorem subd8_3_523 : subd8_3 [-1, -2, -7] = true := by decide +kernel
theorem subd8_3_524 : subd8_3 [-1, -2, -6] = true := by decide +kernel
theorem subd8_3_525 : subd8_3 [-1, -2, -5] = true := by decide +kernel
theorem subd8_3_526 : subd8_3 [-1, -2, -4] = true := by decide +kernel
theorem subd8_3_527 : subd8_3 [-1, -2, -3] = true := by decide +kernel
theorem subd8_3_528 : subd8_3 [-1, -2, -2] = true := by decide +kernel
theorem subd8_3_529 : subd8_3 [-1, -2, -1] = true := by decide +kernel
theorem subd8_3_530 : subd8_3 [-1, -2, 0] = true := by decide +kernel
theorem subd8_3_531 : subd8_3 [-1, -2, 1] = true := by decide +kernel
theorem subd8_3_532 : subd8_3 [-1, -2, 2] = true := by decide +kernel
theorem subd8_3_533 : subd8_3 [-1, -2, 3] = true := by decide +kernel
theorem subd8_3_534 : subd8_3 [-1, -2, 4] = true := by decide +kernel
theorem subd8_3_535 : subd8_3 [-1, -2, 5] = true := by decide +kernel
theorem subd8_3_536 : subd8_3 [-1, -2, 6] = true := by decide +kernel
theorem subd8_3_537 : subd8_3 [-1, -2, 7] = true := by decide +kernel
theorem subd8_3_538 : subd8_3 [-1, -1, -10] = true := by decide +kernel
theorem subd8_3_539 : subd8_3 [-1, -1, -9] = true := by decide +kernel
theorem subd8_3_540 : subd8_3 [-1, -1, -8] = true := by decide +kernel
theorem subd8_3_541 : subd8_3 [-1, -1, -7] = true := by decide +kernel
theorem subd8_3_542 : subd8_3 [-1, -1, -6] = true := by decide +kernel
theorem subd8_3_543 : subd8_3 [-1, -1, -5] = true := by decide +kernel
theorem sbd8_3_16 : ∀ q ∈ blkd8_3_16, subd8_3 q = true := by
  unfold blkd8_3_16
  exact List.forall_mem_cons.2 ⟨subd8_3_512, List.forall_mem_cons.2 ⟨subd8_3_513, List.forall_mem_cons.2 ⟨subd8_3_514, List.forall_mem_cons.2 ⟨subd8_3_515, List.forall_mem_cons.2 ⟨subd8_3_516, List.forall_mem_cons.2 ⟨subd8_3_517, List.forall_mem_cons.2 ⟨subd8_3_518, List.forall_mem_cons.2 ⟨subd8_3_519, List.forall_mem_cons.2 ⟨subd8_3_520, List.forall_mem_cons.2 ⟨subd8_3_521, List.forall_mem_cons.2 ⟨subd8_3_522, List.forall_mem_cons.2 ⟨subd8_3_523, List.forall_mem_cons.2 ⟨subd8_3_524, List.forall_mem_cons.2 ⟨subd8_3_525, List.forall_mem_cons.2 ⟨subd8_3_526, List.forall_mem_cons.2 ⟨subd8_3_527, List.forall_mem_cons.2 ⟨subd8_3_528, List.forall_mem_cons.2 ⟨subd8_3_529, List.forall_mem_cons.2 ⟨subd8_3_530, List.forall_mem_cons.2 ⟨subd8_3_531, List.forall_mem_cons.2 ⟨subd8_3_532, List.forall_mem_cons.2 ⟨subd8_3_533, List.forall_mem_cons.2 ⟨subd8_3_534, List.forall_mem_cons.2 ⟨subd8_3_535, List.forall_mem_cons.2 ⟨subd8_3_536, List.forall_mem_cons.2 ⟨subd8_3_537, List.forall_mem_cons.2 ⟨subd8_3_538, List.forall_mem_cons.2 ⟨subd8_3_539, List.forall_mem_cons.2 ⟨subd8_3_540, List.forall_mem_cons.2 ⟨subd8_3_541, List.forall_mem_cons.2 ⟨subd8_3_542, List.forall_mem_cons.2 ⟨subd8_3_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_544 : subd8_3 [-1, -1, -4] = true := by decide +kernel
theorem subd8_3_545 : subd8_3 [-1, -1, -3] = true := by decide +kernel
theorem subd8_3_546 : subd8_3 [-1, -1, -2] = true := by decide +kernel
theorem subd8_3_547 : subd8_3 [-1, -1, -1] = true := by decide +kernel
theorem subd8_3_548 : subd8_3 [-1, -1, 0] = true := by decide +kernel
theorem subd8_3_549 : subd8_3 [-1, -1, 1] = true := by decide +kernel
theorem subd8_3_550 : subd8_3 [-1, -1, 2] = true := by decide +kernel
theorem subd8_3_551 : subd8_3 [-1, -1, 3] = true := by decide +kernel
theorem subd8_3_552 : subd8_3 [-1, -1, 4] = true := by decide +kernel
theorem subd8_3_553 : subd8_3 [-1, -1, 5] = true := by decide +kernel
theorem subd8_3_554 : subd8_3 [-1, -1, 6] = true := by decide +kernel
theorem subd8_3_555 : subd8_3 [-1, -1, 7] = true := by decide +kernel
theorem subd8_3_556 : subd8_3 [-1, -1, 8] = true := by decide +kernel
theorem subd8_3_557 : subd8_3 [-1, 0, -10] = true := by decide +kernel
theorem subd8_3_558 : subd8_3 [-1, 0, -9] = true := by decide +kernel
theorem subd8_3_559 : subd8_3 [-1, 0, -8] = true := by decide +kernel
theorem subd8_3_560 : subd8_3 [-1, 0, -7] = true := by decide +kernel
theorem subd8_3_561 : subd8_3 [-1, 0, -6] = true := by decide +kernel
theorem subd8_3_562 : subd8_3 [-1, 0, -5] = true := by decide +kernel
theorem subd8_3_563 : subd8_3 [-1, 0, -4] = true := by decide +kernel
theorem subd8_3_564 : subd8_3 [-1, 0, -3] = true := by decide +kernel
theorem subd8_3_565 : subd8_3 [-1, 0, -2] = true := by decide +kernel
theorem subd8_3_566 : subd8_3 [-1, 0, -1] = true := by decide +kernel
theorem subd8_3_567 : subd8_3 [-1, 0, 0] = true := by decide +kernel
theorem subd8_3_568 : subd8_3 [-1, 0, 1] = true := by decide +kernel
theorem subd8_3_569 : subd8_3 [-1, 0, 2] = true := by decide +kernel
theorem subd8_3_570 : subd8_3 [-1, 0, 3] = true := by decide +kernel
theorem subd8_3_571 : subd8_3 [-1, 0, 4] = true := by decide +kernel
theorem subd8_3_572 : subd8_3 [-1, 0, 5] = true := by decide +kernel
theorem subd8_3_573 : subd8_3 [-1, 0, 6] = true := by decide +kernel
theorem subd8_3_574 : subd8_3 [-1, 0, 7] = true := by decide +kernel
theorem subd8_3_575 : subd8_3 [-1, 0, 8] = true := by decide +kernel
theorem sbd8_3_17 : ∀ q ∈ blkd8_3_17, subd8_3 q = true := by
  unfold blkd8_3_17
  exact List.forall_mem_cons.2 ⟨subd8_3_544, List.forall_mem_cons.2 ⟨subd8_3_545, List.forall_mem_cons.2 ⟨subd8_3_546, List.forall_mem_cons.2 ⟨subd8_3_547, List.forall_mem_cons.2 ⟨subd8_3_548, List.forall_mem_cons.2 ⟨subd8_3_549, List.forall_mem_cons.2 ⟨subd8_3_550, List.forall_mem_cons.2 ⟨subd8_3_551, List.forall_mem_cons.2 ⟨subd8_3_552, List.forall_mem_cons.2 ⟨subd8_3_553, List.forall_mem_cons.2 ⟨subd8_3_554, List.forall_mem_cons.2 ⟨subd8_3_555, List.forall_mem_cons.2 ⟨subd8_3_556, List.forall_mem_cons.2 ⟨subd8_3_557, List.forall_mem_cons.2 ⟨subd8_3_558, List.forall_mem_cons.2 ⟨subd8_3_559, List.forall_mem_cons.2 ⟨subd8_3_560, List.forall_mem_cons.2 ⟨subd8_3_561, List.forall_mem_cons.2 ⟨subd8_3_562, List.forall_mem_cons.2 ⟨subd8_3_563, List.forall_mem_cons.2 ⟨subd8_3_564, List.forall_mem_cons.2 ⟨subd8_3_565, List.forall_mem_cons.2 ⟨subd8_3_566, List.forall_mem_cons.2 ⟨subd8_3_567, List.forall_mem_cons.2 ⟨subd8_3_568, List.forall_mem_cons.2 ⟨subd8_3_569, List.forall_mem_cons.2 ⟨subd8_3_570, List.forall_mem_cons.2 ⟨subd8_3_571, List.forall_mem_cons.2 ⟨subd8_3_572, List.forall_mem_cons.2 ⟨subd8_3_573, List.forall_mem_cons.2 ⟨subd8_3_574, List.forall_mem_cons.2 ⟨subd8_3_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_576 : subd8_3 [-1, 1, -9] = true := by decide +kernel
theorem subd8_3_577 : subd8_3 [-1, 1, -8] = true := by decide +kernel
theorem subd8_3_578 : subd8_3 [-1, 1, -7] = true := by decide +kernel
theorem subd8_3_579 : subd8_3 [-1, 1, -6] = true := by decide +kernel
theorem subd8_3_580 : subd8_3 [-1, 1, -5] = true := by decide +kernel
theorem subd8_3_581 : subd8_3 [-1, 1, -4] = true := by decide +kernel
theorem subd8_3_582 : subd8_3 [-1, 1, -3] = true := by decide +kernel
theorem subd8_3_583 : subd8_3 [-1, 1, -2] = true := by decide +kernel
theorem subd8_3_584 : subd8_3 [-1, 1, -1] = true := by decide +kernel
theorem subd8_3_585 : subd8_3 [-1, 1, 0] = true := by decide +kernel
theorem subd8_3_586 : subd8_3 [-1, 1, 1] = true := by decide +kernel
theorem subd8_3_587 : subd8_3 [-1, 1, 2] = true := by decide +kernel
theorem subd8_3_588 : subd8_3 [-1, 1, 3] = true := by decide +kernel
theorem subd8_3_589 : subd8_3 [-1, 1, 4] = true := by decide +kernel
theorem subd8_3_590 : subd8_3 [-1, 1, 5] = true := by decide +kernel
theorem subd8_3_591 : subd8_3 [-1, 1, 6] = true := by decide +kernel
theorem subd8_3_592 : subd8_3 [-1, 1, 7] = true := by decide +kernel
theorem subd8_3_593 : subd8_3 [-1, 1, 8] = true := by decide +kernel
theorem subd8_3_594 : subd8_3 [-1, 2, -9] = true := by decide +kernel
theorem subd8_3_595 : subd8_3 [-1, 2, -8] = true := by decide +kernel
theorem subd8_3_596 : subd8_3 [-1, 2, -7] = true := by decide +kernel
theorem subd8_3_597 : subd8_3 [-1, 2, -6] = true := by decide +kernel
theorem subd8_3_598 : subd8_3 [-1, 2, -5] = true := by decide +kernel
theorem subd8_3_599 : subd8_3 [-1, 2, -4] = true := by decide +kernel
theorem subd8_3_600 : subd8_3 [-1, 2, -3] = true := by decide +kernel
theorem subd8_3_601 : subd8_3 [-1, 2, -2] = true := by decide +kernel
theorem subd8_3_602 : subd8_3 [-1, 2, -1] = true := by decide +kernel
theorem subd8_3_603 : subd8_3 [-1, 2, 0] = true := by decide +kernel
theorem subd8_3_604 : subd8_3 [-1, 2, 1] = true := by decide +kernel
theorem subd8_3_605 : subd8_3 [-1, 2, 2] = true := by decide +kernel
theorem subd8_3_606 : subd8_3 [-1, 2, 3] = true := by decide +kernel
theorem subd8_3_607 : subd8_3 [-1, 2, 4] = true := by decide +kernel
theorem sbd8_3_18 : ∀ q ∈ blkd8_3_18, subd8_3 q = true := by
  unfold blkd8_3_18
  exact List.forall_mem_cons.2 ⟨subd8_3_576, List.forall_mem_cons.2 ⟨subd8_3_577, List.forall_mem_cons.2 ⟨subd8_3_578, List.forall_mem_cons.2 ⟨subd8_3_579, List.forall_mem_cons.2 ⟨subd8_3_580, List.forall_mem_cons.2 ⟨subd8_3_581, List.forall_mem_cons.2 ⟨subd8_3_582, List.forall_mem_cons.2 ⟨subd8_3_583, List.forall_mem_cons.2 ⟨subd8_3_584, List.forall_mem_cons.2 ⟨subd8_3_585, List.forall_mem_cons.2 ⟨subd8_3_586, List.forall_mem_cons.2 ⟨subd8_3_587, List.forall_mem_cons.2 ⟨subd8_3_588, List.forall_mem_cons.2 ⟨subd8_3_589, List.forall_mem_cons.2 ⟨subd8_3_590, List.forall_mem_cons.2 ⟨subd8_3_591, List.forall_mem_cons.2 ⟨subd8_3_592, List.forall_mem_cons.2 ⟨subd8_3_593, List.forall_mem_cons.2 ⟨subd8_3_594, List.forall_mem_cons.2 ⟨subd8_3_595, List.forall_mem_cons.2 ⟨subd8_3_596, List.forall_mem_cons.2 ⟨subd8_3_597, List.forall_mem_cons.2 ⟨subd8_3_598, List.forall_mem_cons.2 ⟨subd8_3_599, List.forall_mem_cons.2 ⟨subd8_3_600, List.forall_mem_cons.2 ⟨subd8_3_601, List.forall_mem_cons.2 ⟨subd8_3_602, List.forall_mem_cons.2 ⟨subd8_3_603, List.forall_mem_cons.2 ⟨subd8_3_604, List.forall_mem_cons.2 ⟨subd8_3_605, List.forall_mem_cons.2 ⟨subd8_3_606, List.forall_mem_cons.2 ⟨subd8_3_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_608 : subd8_3 [-1, 2, 5] = true := by decide +kernel
theorem subd8_3_609 : subd8_3 [-1, 2, 6] = true := by decide +kernel
theorem subd8_3_610 : subd8_3 [-1, 2, 7] = true := by decide +kernel
theorem subd8_3_611 : subd8_3 [-1, 2, 8] = true := by decide +kernel
theorem subd8_3_612 : subd8_3 [-1, 2, 9] = true := by decide +kernel
theorem subd8_3_613 : subd8_3 [-1, 3, -8] = true := by decide +kernel
theorem subd8_3_614 : subd8_3 [-1, 3, -7] = true := by decide +kernel
theorem subd8_3_615 : subd8_3 [-1, 3, -6] = true := by decide +kernel
theorem subd8_3_616 : subd8_3 [-1, 3, -5] = true := by decide +kernel
theorem subd8_3_617 : subd8_3 [-1, 3, -4] = true := by decide +kernel
theorem subd8_3_618 : subd8_3 [-1, 3, -3] = true := by decide +kernel
theorem subd8_3_619 : subd8_3 [-1, 3, -2] = true := by decide +kernel
theorem subd8_3_620 : subd8_3 [-1, 3, -1] = true := by decide +kernel
theorem subd8_3_621 : subd8_3 [-1, 3, 0] = true := by decide +kernel
theorem subd8_3_622 : subd8_3 [-1, 3, 1] = true := by decide +kernel
theorem subd8_3_623 : subd8_3 [-1, 3, 2] = true := by decide +kernel
theorem subd8_3_624 : subd8_3 [-1, 3, 3] = true := by decide +kernel
theorem subd8_3_625 : subd8_3 [-1, 3, 4] = true := by decide +kernel
theorem subd8_3_626 : subd8_3 [-1, 3, 5] = true := by decide +kernel
theorem subd8_3_627 : subd8_3 [-1, 3, 6] = true := by decide +kernel
theorem subd8_3_628 : subd8_3 [-1, 3, 7] = true := by decide +kernel
theorem subd8_3_629 : subd8_3 [-1, 3, 8] = true := by decide +kernel
theorem subd8_3_630 : subd8_3 [-1, 4, -7] = true := by decide +kernel
theorem subd8_3_631 : subd8_3 [-1, 4, -6] = true := by decide +kernel
theorem subd8_3_632 : subd8_3 [-1, 4, -5] = true := by decide +kernel
theorem subd8_3_633 : subd8_3 [-1, 4, -4] = true := by decide +kernel
theorem subd8_3_634 : subd8_3 [-1, 4, -3] = true := by decide +kernel
theorem subd8_3_635 : subd8_3 [-1, 4, -2] = true := by decide +kernel
theorem subd8_3_636 : subd8_3 [-1, 4, -1] = true := by decide +kernel
theorem subd8_3_637 : subd8_3 [-1, 4, 0] = true := by decide +kernel
theorem subd8_3_638 : subd8_3 [-1, 4, 1] = true := by decide +kernel
theorem subd8_3_639 : subd8_3 [-1, 4, 2] = true := by decide +kernel
theorem sbd8_3_19 : ∀ q ∈ blkd8_3_19, subd8_3 q = true := by
  unfold blkd8_3_19
  exact List.forall_mem_cons.2 ⟨subd8_3_608, List.forall_mem_cons.2 ⟨subd8_3_609, List.forall_mem_cons.2 ⟨subd8_3_610, List.forall_mem_cons.2 ⟨subd8_3_611, List.forall_mem_cons.2 ⟨subd8_3_612, List.forall_mem_cons.2 ⟨subd8_3_613, List.forall_mem_cons.2 ⟨subd8_3_614, List.forall_mem_cons.2 ⟨subd8_3_615, List.forall_mem_cons.2 ⟨subd8_3_616, List.forall_mem_cons.2 ⟨subd8_3_617, List.forall_mem_cons.2 ⟨subd8_3_618, List.forall_mem_cons.2 ⟨subd8_3_619, List.forall_mem_cons.2 ⟨subd8_3_620, List.forall_mem_cons.2 ⟨subd8_3_621, List.forall_mem_cons.2 ⟨subd8_3_622, List.forall_mem_cons.2 ⟨subd8_3_623, List.forall_mem_cons.2 ⟨subd8_3_624, List.forall_mem_cons.2 ⟨subd8_3_625, List.forall_mem_cons.2 ⟨subd8_3_626, List.forall_mem_cons.2 ⟨subd8_3_627, List.forall_mem_cons.2 ⟨subd8_3_628, List.forall_mem_cons.2 ⟨subd8_3_629, List.forall_mem_cons.2 ⟨subd8_3_630, List.forall_mem_cons.2 ⟨subd8_3_631, List.forall_mem_cons.2 ⟨subd8_3_632, List.forall_mem_cons.2 ⟨subd8_3_633, List.forall_mem_cons.2 ⟨subd8_3_634, List.forall_mem_cons.2 ⟨subd8_3_635, List.forall_mem_cons.2 ⟨subd8_3_636, List.forall_mem_cons.2 ⟨subd8_3_637, List.forall_mem_cons.2 ⟨subd8_3_638, List.forall_mem_cons.2 ⟨subd8_3_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_640 : subd8_3 [-1, 4, 3] = true := by decide +kernel
theorem subd8_3_641 : subd8_3 [-1, 4, 4] = true := by decide +kernel
theorem subd8_3_642 : subd8_3 [-1, 4, 5] = true := by decide +kernel
theorem subd8_3_643 : subd8_3 [-1, 4, 6] = true := by decide +kernel
theorem subd8_3_644 : subd8_3 [-1, 4, 7] = true := by decide +kernel
theorem subd8_3_645 : subd8_3 [-1, 4, 8] = true := by decide +kernel
theorem subd8_3_646 : subd8_3 [-1, 5, -5] = true := by decide +kernel
theorem subd8_3_647 : subd8_3 [-1, 5, -4] = true := by decide +kernel
theorem subd8_3_648 : subd8_3 [-1, 5, -3] = true := by decide +kernel
theorem subd8_3_649 : subd8_3 [-1, 5, -2] = true := by decide +kernel
theorem subd8_3_650 : subd8_3 [-1, 5, -1] = true := by decide +kernel
theorem subd8_3_651 : subd8_3 [-1, 5, 0] = true := by decide +kernel
theorem subd8_3_652 : subd8_3 [-1, 5, 1] = true := by decide +kernel
theorem subd8_3_653 : subd8_3 [-1, 5, 2] = true := by decide +kernel
theorem subd8_3_654 : subd8_3 [-1, 5, 3] = true := by decide +kernel
theorem subd8_3_655 : subd8_3 [-1, 5, 4] = true := by decide +kernel
theorem subd8_3_656 : subd8_3 [-1, 5, 5] = true := by decide +kernel
theorem subd8_3_657 : subd8_3 [-1, 5, 6] = true := by decide +kernel
theorem subd8_3_658 : subd8_3 [-1, 5, 7] = true := by decide +kernel
theorem subd8_3_659 : subd8_3 [-1, 5, 8] = true := by decide +kernel
theorem subd8_3_660 : subd8_3 [-1, 6] = true := by decide +kernel
theorem subd8_3_661 : subd8_3 [-1, 7] = true := by decide +kernel
theorem subd8_3_662 : subd8_3 [0, -8] = true := by decide +kernel
theorem subd8_3_663 : subd8_3 [0, -7] = true := by decide +kernel
theorem subd8_3_664 : subd8_3 [0, -6] = true := by decide +kernel
theorem subd8_3_665 : subd8_3 [0, -5, -9] = true := by decide +kernel
theorem subd8_3_666 : subd8_3 [0, -5, -8] = true := by decide +kernel
theorem subd8_3_667 : subd8_3 [0, -5, -7] = true := by decide +kernel
theorem subd8_3_668 : subd8_3 [0, -5, -6] = true := by decide +kernel
theorem subd8_3_669 : subd8_3 [0, -5, -5] = true := by decide +kernel
theorem subd8_3_670 : subd8_3 [0, -5, -4] = true := by decide +kernel
theorem subd8_3_671 : subd8_3 [0, -5, -3] = true := by decide +kernel
theorem sbd8_3_20 : ∀ q ∈ blkd8_3_20, subd8_3 q = true := by
  unfold blkd8_3_20
  exact List.forall_mem_cons.2 ⟨subd8_3_640, List.forall_mem_cons.2 ⟨subd8_3_641, List.forall_mem_cons.2 ⟨subd8_3_642, List.forall_mem_cons.2 ⟨subd8_3_643, List.forall_mem_cons.2 ⟨subd8_3_644, List.forall_mem_cons.2 ⟨subd8_3_645, List.forall_mem_cons.2 ⟨subd8_3_646, List.forall_mem_cons.2 ⟨subd8_3_647, List.forall_mem_cons.2 ⟨subd8_3_648, List.forall_mem_cons.2 ⟨subd8_3_649, List.forall_mem_cons.2 ⟨subd8_3_650, List.forall_mem_cons.2 ⟨subd8_3_651, List.forall_mem_cons.2 ⟨subd8_3_652, List.forall_mem_cons.2 ⟨subd8_3_653, List.forall_mem_cons.2 ⟨subd8_3_654, List.forall_mem_cons.2 ⟨subd8_3_655, List.forall_mem_cons.2 ⟨subd8_3_656, List.forall_mem_cons.2 ⟨subd8_3_657, List.forall_mem_cons.2 ⟨subd8_3_658, List.forall_mem_cons.2 ⟨subd8_3_659, List.forall_mem_cons.2 ⟨subd8_3_660, List.forall_mem_cons.2 ⟨subd8_3_661, List.forall_mem_cons.2 ⟨subd8_3_662, List.forall_mem_cons.2 ⟨subd8_3_663, List.forall_mem_cons.2 ⟨subd8_3_664, List.forall_mem_cons.2 ⟨subd8_3_665, List.forall_mem_cons.2 ⟨subd8_3_666, List.forall_mem_cons.2 ⟨subd8_3_667, List.forall_mem_cons.2 ⟨subd8_3_668, List.forall_mem_cons.2 ⟨subd8_3_669, List.forall_mem_cons.2 ⟨subd8_3_670, List.forall_mem_cons.2 ⟨subd8_3_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_672 : subd8_3 [0, -5, -2] = true := by decide +kernel
theorem subd8_3_673 : subd8_3 [0, -5, -1] = true := by decide +kernel
theorem subd8_3_674 : subd8_3 [0, -5, 0] = true := by decide +kernel
theorem subd8_3_675 : subd8_3 [0, -5, 1] = true := by decide +kernel
theorem subd8_3_676 : subd8_3 [0, -5, 2] = true := by decide +kernel
theorem subd8_3_677 : subd8_3 [0, -5, 3] = true := by decide +kernel
theorem subd8_3_678 : subd8_3 [0, -5, 4] = true := by decide +kernel
theorem subd8_3_679 : subd8_3 [0, -4, -10] = true := by decide +kernel
theorem subd8_3_680 : subd8_3 [0, -4, -9] = true := by decide +kernel
theorem subd8_3_681 : subd8_3 [0, -4, -8] = true := by decide +kernel
theorem subd8_3_682 : subd8_3 [0, -4, -7] = true := by decide +kernel
theorem subd8_3_683 : subd8_3 [0, -4, -6] = true := by decide +kernel
theorem subd8_3_684 : subd8_3 [0, -4, -5] = true := by decide +kernel
theorem subd8_3_685 : subd8_3 [0, -4, -4] = true := by decide +kernel
theorem subd8_3_686 : subd8_3 [0, -4, -3] = true := by decide +kernel
theorem subd8_3_687 : subd8_3 [0, -4, -2] = true := by decide +kernel
theorem subd8_3_688 : subd8_3 [0, -4, -1] = true := by decide +kernel
theorem subd8_3_689 : subd8_3 [0, -4, 0] = true := by decide +kernel
theorem subd8_3_690 : subd8_3 [0, -4, 1] = true := by decide +kernel
theorem subd8_3_691 : subd8_3 [0, -4, 2] = true := by decide +kernel
theorem subd8_3_692 : subd8_3 [0, -4, 3] = true := by decide +kernel
theorem subd8_3_693 : subd8_3 [0, -4, 4] = true := by decide +kernel
theorem subd8_3_694 : subd8_3 [0, -4, 5] = true := by decide +kernel
theorem subd8_3_695 : subd8_3 [0, -4, 6] = true := by decide +kernel
theorem subd8_3_696 : subd8_3 [0, -3, -10] = true := by decide +kernel
theorem subd8_3_697 : subd8_3 [0, -3, -9] = true := by decide +kernel
theorem subd8_3_698 : subd8_3 [0, -3, -8] = true := by decide +kernel
theorem subd8_3_699 : subd8_3 [0, -3, -7] = true := by decide +kernel
theorem subd8_3_700 : subd8_3 [0, -3, -6] = true := by decide +kernel
theorem subd8_3_701 : subd8_3 [0, -3, -5] = true := by decide +kernel
theorem subd8_3_702 : subd8_3 [0, -3, -4] = true := by decide +kernel
theorem subd8_3_703 : subd8_3 [0, -3, -3] = true := by decide +kernel
theorem sbd8_3_21 : ∀ q ∈ blkd8_3_21, subd8_3 q = true := by
  unfold blkd8_3_21
  exact List.forall_mem_cons.2 ⟨subd8_3_672, List.forall_mem_cons.2 ⟨subd8_3_673, List.forall_mem_cons.2 ⟨subd8_3_674, List.forall_mem_cons.2 ⟨subd8_3_675, List.forall_mem_cons.2 ⟨subd8_3_676, List.forall_mem_cons.2 ⟨subd8_3_677, List.forall_mem_cons.2 ⟨subd8_3_678, List.forall_mem_cons.2 ⟨subd8_3_679, List.forall_mem_cons.2 ⟨subd8_3_680, List.forall_mem_cons.2 ⟨subd8_3_681, List.forall_mem_cons.2 ⟨subd8_3_682, List.forall_mem_cons.2 ⟨subd8_3_683, List.forall_mem_cons.2 ⟨subd8_3_684, List.forall_mem_cons.2 ⟨subd8_3_685, List.forall_mem_cons.2 ⟨subd8_3_686, List.forall_mem_cons.2 ⟨subd8_3_687, List.forall_mem_cons.2 ⟨subd8_3_688, List.forall_mem_cons.2 ⟨subd8_3_689, List.forall_mem_cons.2 ⟨subd8_3_690, List.forall_mem_cons.2 ⟨subd8_3_691, List.forall_mem_cons.2 ⟨subd8_3_692, List.forall_mem_cons.2 ⟨subd8_3_693, List.forall_mem_cons.2 ⟨subd8_3_694, List.forall_mem_cons.2 ⟨subd8_3_695, List.forall_mem_cons.2 ⟨subd8_3_696, List.forall_mem_cons.2 ⟨subd8_3_697, List.forall_mem_cons.2 ⟨subd8_3_698, List.forall_mem_cons.2 ⟨subd8_3_699, List.forall_mem_cons.2 ⟨subd8_3_700, List.forall_mem_cons.2 ⟨subd8_3_701, List.forall_mem_cons.2 ⟨subd8_3_702, List.forall_mem_cons.2 ⟨subd8_3_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C096
