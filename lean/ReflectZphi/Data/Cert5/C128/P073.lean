import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_7_288 : subd9_7 [0, -2, -6] = true := by decide +kernel
theorem subd9_7_289 : subd9_7 [0, -2, -5] = true := by decide +kernel
theorem subd9_7_290 : subd9_7 [0, -2, -4] = true := by decide +kernel
theorem subd9_7_291 : subd9_7 [0, -2, -3] = true := by decide +kernel
theorem subd9_7_292 : subd9_7 [0, -2, -2] = true := by decide +kernel
theorem subd9_7_293 : subd9_7 [0, -2, -1] = true := by decide +kernel
theorem subd9_7_294 : subd9_7 [0, -2, 0] = true := by decide +kernel
theorem subd9_7_295 : subd9_7 [0, -2, 1] = true := by decide +kernel
theorem subd9_7_296 : subd9_7 [0, -2, 2] = true := by decide +kernel
theorem subd9_7_297 : subd9_7 [0, -2, 3] = true := by decide +kernel
theorem subd9_7_298 : subd9_7 [0, -2, 4] = true := by decide +kernel
theorem subd9_7_299 : subd9_7 [0, -2, 5] = true := by decide +kernel
theorem subd9_7_300 : subd9_7 [0, -2, 6] = true := by decide +kernel
theorem subd9_7_301 : subd9_7 [0, -1, -9] = true := by decide +kernel
theorem subd9_7_302 : subd9_7 [0, -1, -8] = true := by decide +kernel
theorem subd9_7_303 : subd9_7 [0, -1, -7] = true := by decide +kernel
theorem subd9_7_304 : subd9_7 [0, -1, -6] = true := by decide +kernel
theorem subd9_7_305 : subd9_7 [0, -1, -5] = true := by decide +kernel
theorem subd9_7_306 : subd9_7 [0, -1, -4] = true := by decide +kernel
theorem subd9_7_307 : subd9_7 [0, -1, -3] = true := by decide +kernel
theorem subd9_7_308 : subd9_7 [0, -1, -2] = true := by decide +kernel
theorem subd9_7_309 : subd9_7 [0, -1, -1] = true := by decide +kernel
theorem subd9_7_310 : subd9_7 [0, -1, 0] = true := by decide +kernel
theorem subd9_7_311 : subd9_7 [0, -1, 1] = true := by decide +kernel
theorem subd9_7_312 : subd9_7 [0, -1, 2] = true := by decide +kernel
theorem subd9_7_313 : subd9_7 [0, -1, 3] = true := by decide +kernel
theorem subd9_7_314 : subd9_7 [0, -1, 4] = true := by decide +kernel
theorem subd9_7_315 : subd9_7 [0, -1, 5] = true := by decide +kernel
theorem subd9_7_316 : subd9_7 [0, -1, 6] = true := by decide +kernel
theorem subd9_7_317 : subd9_7 [0, -1, 7] = true := by decide +kernel
theorem subd9_7_318 : subd9_7 [0, 0, -9] = true := by decide +kernel
theorem subd9_7_319 : subd9_7 [0, 0, -8] = true := by decide +kernel
theorem sbd9_7_9 : ∀ q ∈ blkd9_7_9, subd9_7 q = true := by
  unfold blkd9_7_9
  exact List.forall_mem_cons.2 ⟨subd9_7_288, List.forall_mem_cons.2 ⟨subd9_7_289, List.forall_mem_cons.2 ⟨subd9_7_290, List.forall_mem_cons.2 ⟨subd9_7_291, List.forall_mem_cons.2 ⟨subd9_7_292, List.forall_mem_cons.2 ⟨subd9_7_293, List.forall_mem_cons.2 ⟨subd9_7_294, List.forall_mem_cons.2 ⟨subd9_7_295, List.forall_mem_cons.2 ⟨subd9_7_296, List.forall_mem_cons.2 ⟨subd9_7_297, List.forall_mem_cons.2 ⟨subd9_7_298, List.forall_mem_cons.2 ⟨subd9_7_299, List.forall_mem_cons.2 ⟨subd9_7_300, List.forall_mem_cons.2 ⟨subd9_7_301, List.forall_mem_cons.2 ⟨subd9_7_302, List.forall_mem_cons.2 ⟨subd9_7_303, List.forall_mem_cons.2 ⟨subd9_7_304, List.forall_mem_cons.2 ⟨subd9_7_305, List.forall_mem_cons.2 ⟨subd9_7_306, List.forall_mem_cons.2 ⟨subd9_7_307, List.forall_mem_cons.2 ⟨subd9_7_308, List.forall_mem_cons.2 ⟨subd9_7_309, List.forall_mem_cons.2 ⟨subd9_7_310, List.forall_mem_cons.2 ⟨subd9_7_311, List.forall_mem_cons.2 ⟨subd9_7_312, List.forall_mem_cons.2 ⟨subd9_7_313, List.forall_mem_cons.2 ⟨subd9_7_314, List.forall_mem_cons.2 ⟨subd9_7_315, List.forall_mem_cons.2 ⟨subd9_7_316, List.forall_mem_cons.2 ⟨subd9_7_317, List.forall_mem_cons.2 ⟨subd9_7_318, List.forall_mem_cons.2 ⟨subd9_7_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_7_320 : subd9_7 [0, 0, -7] = true := by decide +kernel
theorem subd9_7_321 : subd9_7 [0, 0, -6] = true := by decide +kernel
theorem subd9_7_322 : subd9_7 [0, 0, -5] = true := by decide +kernel
theorem subd9_7_323 : subd9_7 [0, 0, -4] = true := by decide +kernel
theorem subd9_7_324 : subd9_7 [0, 0, -3] = true := by decide +kernel
theorem subd9_7_325 : subd9_7 [0, 0, -2] = true := by decide +kernel
theorem subd9_7_326 : subd9_7 [0, 0, -1] = true := by decide +kernel
theorem subd9_7_327 : subd9_7 [0, 0, 0] = true := by decide +kernel
theorem subd9_7_328 : subd9_7 [0, 0, 1] = true := by decide +kernel
theorem subd9_7_329 : subd9_7 [0, 0, 2] = true := by decide +kernel
theorem subd9_7_330 : subd9_7 [0, 0, 3] = true := by decide +kernel
theorem subd9_7_331 : subd9_7 [0, 0, 4] = true := by decide +kernel
theorem subd9_7_332 : subd9_7 [0, 0, 5] = true := by decide +kernel
theorem subd9_7_333 : subd9_7 [0, 0, 6] = true := by decide +kernel
theorem subd9_7_334 : subd9_7 [0, 0, 7] = true := by decide +kernel
theorem subd9_7_335 : subd9_7 [0, 0, 8] = true := by decide +kernel
theorem subd9_7_336 : subd9_7 [0, 1, -8] = true := by decide +kernel
theorem subd9_7_337 : subd9_7 [0, 1, -7] = true := by decide +kernel
theorem subd9_7_338 : subd9_7 [0, 1, -6] = true := by decide +kernel
theorem subd9_7_339 : subd9_7 [0, 1, -5] = true := by decide +kernel
theorem subd9_7_340 : subd9_7 [0, 1, -4] = true := by decide +kernel
theorem subd9_7_341 : subd9_7 [0, 1, -3] = true := by decide +kernel
theorem subd9_7_342 : subd9_7 [0, 1, -2] = true := by decide +kernel
theorem subd9_7_343 : subd9_7 [0, 1, -1] = true := by decide +kernel
theorem subd9_7_344 : subd9_7 [0, 1, 0] = true := by decide +kernel
theorem subd9_7_345 : subd9_7 [0, 1, 1] = true := by decide +kernel
theorem subd9_7_346 : subd9_7 [0, 1, 2] = true := by decide +kernel
theorem subd9_7_347 : subd9_7 [0, 1, 3] = true := by decide +kernel
theorem subd9_7_348 : subd9_7 [0, 1, 4] = true := by decide +kernel
theorem subd9_7_349 : subd9_7 [0, 1, 5] = true := by decide +kernel
theorem subd9_7_350 : subd9_7 [0, 1, 6] = true := by decide +kernel
theorem subd9_7_351 : subd9_7 [0, 1, 7] = true := by decide +kernel
theorem sbd9_7_10 : ∀ q ∈ blkd9_7_10, subd9_7 q = true := by
  unfold blkd9_7_10
  exact List.forall_mem_cons.2 ⟨subd9_7_320, List.forall_mem_cons.2 ⟨subd9_7_321, List.forall_mem_cons.2 ⟨subd9_7_322, List.forall_mem_cons.2 ⟨subd9_7_323, List.forall_mem_cons.2 ⟨subd9_7_324, List.forall_mem_cons.2 ⟨subd9_7_325, List.forall_mem_cons.2 ⟨subd9_7_326, List.forall_mem_cons.2 ⟨subd9_7_327, List.forall_mem_cons.2 ⟨subd9_7_328, List.forall_mem_cons.2 ⟨subd9_7_329, List.forall_mem_cons.2 ⟨subd9_7_330, List.forall_mem_cons.2 ⟨subd9_7_331, List.forall_mem_cons.2 ⟨subd9_7_332, List.forall_mem_cons.2 ⟨subd9_7_333, List.forall_mem_cons.2 ⟨subd9_7_334, List.forall_mem_cons.2 ⟨subd9_7_335, List.forall_mem_cons.2 ⟨subd9_7_336, List.forall_mem_cons.2 ⟨subd9_7_337, List.forall_mem_cons.2 ⟨subd9_7_338, List.forall_mem_cons.2 ⟨subd9_7_339, List.forall_mem_cons.2 ⟨subd9_7_340, List.forall_mem_cons.2 ⟨subd9_7_341, List.forall_mem_cons.2 ⟨subd9_7_342, List.forall_mem_cons.2 ⟨subd9_7_343, List.forall_mem_cons.2 ⟨subd9_7_344, List.forall_mem_cons.2 ⟨subd9_7_345, List.forall_mem_cons.2 ⟨subd9_7_346, List.forall_mem_cons.2 ⟨subd9_7_347, List.forall_mem_cons.2 ⟨subd9_7_348, List.forall_mem_cons.2 ⟨subd9_7_349, List.forall_mem_cons.2 ⟨subd9_7_350, List.forall_mem_cons.2 ⟨subd9_7_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_7_352 : subd9_7 [0, 1, 8] = true := by decide +kernel
theorem subd9_7_353 : subd9_7 [0, 2, -7] = true := by decide +kernel
theorem subd9_7_354 : subd9_7 [0, 2, -6] = true := by decide +kernel
theorem subd9_7_355 : subd9_7 [0, 2, -5] = true := by decide +kernel
theorem subd9_7_356 : subd9_7 [0, 2, -4] = true := by decide +kernel
theorem subd9_7_357 : subd9_7 [0, 2, -3] = true := by decide +kernel
theorem subd9_7_358 : subd9_7 [0, 2, -2] = true := by decide +kernel
theorem subd9_7_359 : subd9_7 [0, 2, -1] = true := by decide +kernel
theorem subd9_7_360 : subd9_7 [0, 2, 0] = true := by decide +kernel
theorem subd9_7_361 : subd9_7 [0, 2, 1] = true := by decide +kernel
theorem subd9_7_362 : subd9_7 [0, 2, 2] = true := by decide +kernel
theorem subd9_7_363 : subd9_7 [0, 2, 3] = true := by decide +kernel
theorem subd9_7_364 : subd9_7 [0, 2, 4] = true := by decide +kernel
theorem subd9_7_365 : subd9_7 [0, 2, 5] = true := by decide +kernel
theorem subd9_7_366 : subd9_7 [0, 2, 6] = true := by decide +kernel
theorem subd9_7_367 : subd9_7 [0, 2, 7] = true := by decide +kernel
theorem subd9_7_368 : subd9_7 [0, 2, 8] = true := by decide +kernel
theorem subd9_7_369 : subd9_7 [0, 3, -6] = true := by decide +kernel
theorem subd9_7_370 : subd9_7 [0, 3, -5] = true := by decide +kernel
theorem subd9_7_371 : subd9_7 [0, 3, -4] = true := by decide +kernel
theorem subd9_7_372 : subd9_7 [0, 3, -3] = true := by decide +kernel
theorem subd9_7_373 : subd9_7 [0, 3, -2] = true := by decide +kernel
theorem subd9_7_374 : subd9_7 [0, 3, -1] = true := by decide +kernel
theorem subd9_7_375 : subd9_7 [0, 3, 0] = true := by decide +kernel
theorem subd9_7_376 : subd9_7 [0, 3, 1] = true := by decide +kernel
theorem subd9_7_377 : subd9_7 [0, 3, 2] = true := by decide +kernel
theorem subd9_7_378 : subd9_7 [0, 3, 3] = true := by decide +kernel
theorem subd9_7_379 : subd9_7 [0, 3, 4] = true := by decide +kernel
theorem subd9_7_380 : subd9_7 [0, 3, 5] = true := by decide +kernel
theorem subd9_7_381 : subd9_7 [0, 3, 6] = true := by decide +kernel
theorem subd9_7_382 : subd9_7 [0, 3, 7] = true := by decide +kernel
theorem subd9_7_383 : subd9_7 [0, 3, 8] = true := by decide +kernel
theorem sbd9_7_11 : ∀ q ∈ blkd9_7_11, subd9_7 q = true := by
  unfold blkd9_7_11
  exact List.forall_mem_cons.2 ⟨subd9_7_352, List.forall_mem_cons.2 ⟨subd9_7_353, List.forall_mem_cons.2 ⟨subd9_7_354, List.forall_mem_cons.2 ⟨subd9_7_355, List.forall_mem_cons.2 ⟨subd9_7_356, List.forall_mem_cons.2 ⟨subd9_7_357, List.forall_mem_cons.2 ⟨subd9_7_358, List.forall_mem_cons.2 ⟨subd9_7_359, List.forall_mem_cons.2 ⟨subd9_7_360, List.forall_mem_cons.2 ⟨subd9_7_361, List.forall_mem_cons.2 ⟨subd9_7_362, List.forall_mem_cons.2 ⟨subd9_7_363, List.forall_mem_cons.2 ⟨subd9_7_364, List.forall_mem_cons.2 ⟨subd9_7_365, List.forall_mem_cons.2 ⟨subd9_7_366, List.forall_mem_cons.2 ⟨subd9_7_367, List.forall_mem_cons.2 ⟨subd9_7_368, List.forall_mem_cons.2 ⟨subd9_7_369, List.forall_mem_cons.2 ⟨subd9_7_370, List.forall_mem_cons.2 ⟨subd9_7_371, List.forall_mem_cons.2 ⟨subd9_7_372, List.forall_mem_cons.2 ⟨subd9_7_373, List.forall_mem_cons.2 ⟨subd9_7_374, List.forall_mem_cons.2 ⟨subd9_7_375, List.forall_mem_cons.2 ⟨subd9_7_376, List.forall_mem_cons.2 ⟨subd9_7_377, List.forall_mem_cons.2 ⟨subd9_7_378, List.forall_mem_cons.2 ⟨subd9_7_379, List.forall_mem_cons.2 ⟨subd9_7_380, List.forall_mem_cons.2 ⟨subd9_7_381, List.forall_mem_cons.2 ⟨subd9_7_382, List.forall_mem_cons.2 ⟨subd9_7_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_7_384 : subd9_7 [0, 4] = true := by decide +kernel
theorem subd9_7_385 : subd9_7 [0, 5] = true := by decide +kernel
theorem subd9_7_386 : subd9_7 [1, -6] = true := by decide +kernel
theorem subd9_7_387 : subd9_7 [1, -5] = true := by decide +kernel
theorem subd9_7_388 : subd9_7 [1, -4] = true := by decide +kernel
theorem subd9_7_389 : subd9_7 [1, -3, -9] = true := by decide +kernel
theorem subd9_7_390 : subd9_7 [1, -3, -8] = true := by decide +kernel
theorem subd9_7_391 : subd9_7 [1, -3, -7] = true := by decide +kernel
theorem subd9_7_392 : subd9_7 [1, -3, -6] = true := by decide +kernel
theorem subd9_7_393 : subd9_7 [1, -3, -5] = true := by decide +kernel
theorem subd9_7_394 : subd9_7 [1, -3, -4] = true := by decide +kernel
theorem subd9_7_395 : subd9_7 [1, -3, -3] = true := by decide +kernel
theorem subd9_7_396 : subd9_7 [1, -3, -2] = true := by decide +kernel
theorem subd9_7_397 : subd9_7 [1, -3, -1] = true := by decide +kernel
theorem subd9_7_398 : subd9_7 [1, -3, 0] = true := by decide +kernel
theorem subd9_7_399 : subd9_7 [1, -3, 1] = true := by decide +kernel
theorem subd9_7_400 : subd9_7 [1, -3, 2] = true := by decide +kernel
theorem subd9_7_401 : subd9_7 [1, -3, 3] = true := by decide +kernel
theorem subd9_7_402 : subd9_7 [1, -3, 4] = true := by decide +kernel
theorem subd9_7_403 : subd9_7 [1, -3, 5] = true := by decide +kernel
theorem subd9_7_404 : subd9_7 [1, -2, -9] = true := by decide +kernel
theorem subd9_7_405 : subd9_7 [1, -2, -8] = true := by decide +kernel
theorem subd9_7_406 : subd9_7 [1, -2, -7] = true := by decide +kernel
theorem subd9_7_407 : subd9_7 [1, -2, -6] = true := by decide +kernel
theorem subd9_7_408 : subd9_7 [1, -2, -5] = true := by decide +kernel
theorem subd9_7_409 : subd9_7 [1, -2, -4] = true := by decide +kernel
theorem subd9_7_410 : subd9_7 [1, -2, -3] = true := by decide +kernel
theorem subd9_7_411 : subd9_7 [1, -2, -2] = true := by decide +kernel
theorem subd9_7_412 : subd9_7 [1, -2, -1] = true := by decide +kernel
theorem subd9_7_413 : subd9_7 [1, -2, 0] = true := by decide +kernel
theorem subd9_7_414 : subd9_7 [1, -2, 1] = true := by decide +kernel
theorem subd9_7_415 : subd9_7 [1, -2, 2] = true := by decide +kernel
theorem sbd9_7_12 : ∀ q ∈ blkd9_7_12, subd9_7 q = true := by
  unfold blkd9_7_12
  exact List.forall_mem_cons.2 ⟨subd9_7_384, List.forall_mem_cons.2 ⟨subd9_7_385, List.forall_mem_cons.2 ⟨subd9_7_386, List.forall_mem_cons.2 ⟨subd9_7_387, List.forall_mem_cons.2 ⟨subd9_7_388, List.forall_mem_cons.2 ⟨subd9_7_389, List.forall_mem_cons.2 ⟨subd9_7_390, List.forall_mem_cons.2 ⟨subd9_7_391, List.forall_mem_cons.2 ⟨subd9_7_392, List.forall_mem_cons.2 ⟨subd9_7_393, List.forall_mem_cons.2 ⟨subd9_7_394, List.forall_mem_cons.2 ⟨subd9_7_395, List.forall_mem_cons.2 ⟨subd9_7_396, List.forall_mem_cons.2 ⟨subd9_7_397, List.forall_mem_cons.2 ⟨subd9_7_398, List.forall_mem_cons.2 ⟨subd9_7_399, List.forall_mem_cons.2 ⟨subd9_7_400, List.forall_mem_cons.2 ⟨subd9_7_401, List.forall_mem_cons.2 ⟨subd9_7_402, List.forall_mem_cons.2 ⟨subd9_7_403, List.forall_mem_cons.2 ⟨subd9_7_404, List.forall_mem_cons.2 ⟨subd9_7_405, List.forall_mem_cons.2 ⟨subd9_7_406, List.forall_mem_cons.2 ⟨subd9_7_407, List.forall_mem_cons.2 ⟨subd9_7_408, List.forall_mem_cons.2 ⟨subd9_7_409, List.forall_mem_cons.2 ⟨subd9_7_410, List.forall_mem_cons.2 ⟨subd9_7_411, List.forall_mem_cons.2 ⟨subd9_7_412, List.forall_mem_cons.2 ⟨subd9_7_413, List.forall_mem_cons.2 ⟨subd9_7_414, List.forall_mem_cons.2 ⟨subd9_7_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_7_416 : subd9_7 [1, -2, 3] = true := by decide +kernel
theorem subd9_7_417 : subd9_7 [1, -2, 4] = true := by decide +kernel
theorem subd9_7_418 : subd9_7 [1, -2, 5] = true := by decide +kernel
theorem subd9_7_419 : subd9_7 [1, -2, 6] = true := by decide +kernel
theorem subd9_7_420 : subd9_7 [1, -1, -9] = true := by decide +kernel
theorem subd9_7_421 : subd9_7 [1, -1, -8] = true := by decide +kernel
theorem subd9_7_422 : subd9_7 [1, -1, -7] = true := by decide +kernel
theorem subd9_7_423 : subd9_7 [1, -1, -6] = true := by decide +kernel
theorem subd9_7_424 : subd9_7 [1, -1, -5] = true := by decide +kernel
theorem subd9_7_425 : subd9_7 [1, -1, -4] = true := by decide +kernel
theorem subd9_7_426 : subd9_7 [1, -1, -3] = true := by decide +kernel
theorem subd9_7_427 : subd9_7 [1, -1, -2] = true := by decide +kernel
theorem subd9_7_428 : subd9_7 [1, -1, -1] = true := by decide +kernel
theorem subd9_7_429 : subd9_7 [1, -1, 0] = true := by decide +kernel
theorem subd9_7_430 : subd9_7 [1, -1, 1] = true := by decide +kernel
theorem subd9_7_431 : subd9_7 [1, -1, 2] = true := by decide +kernel
theorem subd9_7_432 : subd9_7 [1, -1, 3] = true := by decide +kernel
theorem subd9_7_433 : subd9_7 [1, -1, 4] = true := by decide +kernel
theorem subd9_7_434 : subd9_7 [1, -1, 5] = true := by decide +kernel
theorem subd9_7_435 : subd9_7 [1, -1, 6] = true := by decide +kernel
theorem subd9_7_436 : subd9_7 [1, -1, 7] = true := by decide +kernel
theorem subd9_7_437 : subd9_7 [1, 0, -9] = true := by decide +kernel
theorem subd9_7_438 : subd9_7 [1, 0, -8] = true := by decide +kernel
theorem subd9_7_439 : subd9_7 [1, 0, -7] = true := by decide +kernel
theorem subd9_7_440 : subd9_7 [1, 0, -6] = true := by decide +kernel
theorem subd9_7_441 : subd9_7 [1, 0, -5] = true := by decide +kernel
theorem subd9_7_442 : subd9_7 [1, 0, -4] = true := by decide +kernel
theorem subd9_7_443 : subd9_7 [1, 0, -3] = true := by decide +kernel
theorem subd9_7_444 : subd9_7 [1, 0, -2] = true := by decide +kernel
theorem subd9_7_445 : subd9_7 [1, 0, -1] = true := by decide +kernel
theorem subd9_7_446 : subd9_7 [1, 0, 0] = true := by decide +kernel
theorem subd9_7_447 : subd9_7 [1, 0, 1] = true := by decide +kernel
theorem sbd9_7_13 : ∀ q ∈ blkd9_7_13, subd9_7 q = true := by
  unfold blkd9_7_13
  exact List.forall_mem_cons.2 ⟨subd9_7_416, List.forall_mem_cons.2 ⟨subd9_7_417, List.forall_mem_cons.2 ⟨subd9_7_418, List.forall_mem_cons.2 ⟨subd9_7_419, List.forall_mem_cons.2 ⟨subd9_7_420, List.forall_mem_cons.2 ⟨subd9_7_421, List.forall_mem_cons.2 ⟨subd9_7_422, List.forall_mem_cons.2 ⟨subd9_7_423, List.forall_mem_cons.2 ⟨subd9_7_424, List.forall_mem_cons.2 ⟨subd9_7_425, List.forall_mem_cons.2 ⟨subd9_7_426, List.forall_mem_cons.2 ⟨subd9_7_427, List.forall_mem_cons.2 ⟨subd9_7_428, List.forall_mem_cons.2 ⟨subd9_7_429, List.forall_mem_cons.2 ⟨subd9_7_430, List.forall_mem_cons.2 ⟨subd9_7_431, List.forall_mem_cons.2 ⟨subd9_7_432, List.forall_mem_cons.2 ⟨subd9_7_433, List.forall_mem_cons.2 ⟨subd9_7_434, List.forall_mem_cons.2 ⟨subd9_7_435, List.forall_mem_cons.2 ⟨subd9_7_436, List.forall_mem_cons.2 ⟨subd9_7_437, List.forall_mem_cons.2 ⟨subd9_7_438, List.forall_mem_cons.2 ⟨subd9_7_439, List.forall_mem_cons.2 ⟨subd9_7_440, List.forall_mem_cons.2 ⟨subd9_7_441, List.forall_mem_cons.2 ⟨subd9_7_442, List.forall_mem_cons.2 ⟨subd9_7_443, List.forall_mem_cons.2 ⟨subd9_7_444, List.forall_mem_cons.2 ⟨subd9_7_445, List.forall_mem_cons.2 ⟨subd9_7_446, List.forall_mem_cons.2 ⟨subd9_7_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_7_448 : subd9_7 [1, 0, 2] = true := by decide +kernel
theorem subd9_7_449 : subd9_7 [1, 0, 3] = true := by decide +kernel
theorem subd9_7_450 : subd9_7 [1, 0, 4] = true := by decide +kernel
theorem subd9_7_451 : subd9_7 [1, 0, 5] = true := by decide +kernel
theorem subd9_7_452 : subd9_7 [1, 0, 6] = true := by decide +kernel
theorem subd9_7_453 : subd9_7 [1, 0, 7] = true := by decide +kernel
theorem subd9_7_454 : subd9_7 [1, 1, -8] = true := by decide +kernel
theorem subd9_7_455 : subd9_7 [1, 1, -7] = true := by decide +kernel
theorem subd9_7_456 : subd9_7 [1, 1, -6] = true := by decide +kernel
theorem subd9_7_457 : subd9_7 [1, 1, -5] = true := by decide +kernel
theorem subd9_7_458 : subd9_7 [1, 1, -4] = true := by decide +kernel
theorem subd9_7_459 : subd9_7 [1, 1, -3] = true := by decide +kernel
theorem subd9_7_460 : subd9_7 [1, 1, -2] = true := by decide +kernel
theorem subd9_7_461 : subd9_7 [1, 1, -1] = true := by decide +kernel
theorem subd9_7_462 : subd9_7 [1, 1, 0] = true := by decide +kernel
theorem subd9_7_463 : subd9_7 [1, 1, 1] = true := by decide +kernel
theorem subd9_7_464 : subd9_7 [1, 1, 2] = true := by decide +kernel
theorem subd9_7_465 : subd9_7 [1, 1, 3] = true := by decide +kernel
theorem subd9_7_466 : subd9_7 [1, 1, 4] = true := by decide +kernel
theorem subd9_7_467 : subd9_7 [1, 1, 5] = true := by decide +kernel
theorem subd9_7_468 : subd9_7 [1, 1, 6] = true := by decide +kernel
theorem subd9_7_469 : subd9_7 [1, 1, 7] = true := by decide +kernel
theorem subd9_7_470 : subd9_7 [1, 1, 8] = true := by decide +kernel
theorem subd9_7_471 : subd9_7 [1, 2, -7] = true := by decide +kernel
theorem subd9_7_472 : subd9_7 [1, 2, -6] = true := by decide +kernel
theorem subd9_7_473 : subd9_7 [1, 2, -5] = true := by decide +kernel
theorem subd9_7_474 : subd9_7 [1, 2, -4] = true := by decide +kernel
theorem subd9_7_475 : subd9_7 [1, 2, -3] = true := by decide +kernel
theorem subd9_7_476 : subd9_7 [1, 2, -2] = true := by decide +kernel
theorem subd9_7_477 : subd9_7 [1, 2, -1] = true := by decide +kernel
theorem subd9_7_478 : subd9_7 [1, 2, 0] = true := by decide +kernel
theorem subd9_7_479 : subd9_7 [1, 2, 1] = true := by decide +kernel
theorem sbd9_7_14 : ∀ q ∈ blkd9_7_14, subd9_7 q = true := by
  unfold blkd9_7_14
  exact List.forall_mem_cons.2 ⟨subd9_7_448, List.forall_mem_cons.2 ⟨subd9_7_449, List.forall_mem_cons.2 ⟨subd9_7_450, List.forall_mem_cons.2 ⟨subd9_7_451, List.forall_mem_cons.2 ⟨subd9_7_452, List.forall_mem_cons.2 ⟨subd9_7_453, List.forall_mem_cons.2 ⟨subd9_7_454, List.forall_mem_cons.2 ⟨subd9_7_455, List.forall_mem_cons.2 ⟨subd9_7_456, List.forall_mem_cons.2 ⟨subd9_7_457, List.forall_mem_cons.2 ⟨subd9_7_458, List.forall_mem_cons.2 ⟨subd9_7_459, List.forall_mem_cons.2 ⟨subd9_7_460, List.forall_mem_cons.2 ⟨subd9_7_461, List.forall_mem_cons.2 ⟨subd9_7_462, List.forall_mem_cons.2 ⟨subd9_7_463, List.forall_mem_cons.2 ⟨subd9_7_464, List.forall_mem_cons.2 ⟨subd9_7_465, List.forall_mem_cons.2 ⟨subd9_7_466, List.forall_mem_cons.2 ⟨subd9_7_467, List.forall_mem_cons.2 ⟨subd9_7_468, List.forall_mem_cons.2 ⟨subd9_7_469, List.forall_mem_cons.2 ⟨subd9_7_470, List.forall_mem_cons.2 ⟨subd9_7_471, List.forall_mem_cons.2 ⟨subd9_7_472, List.forall_mem_cons.2 ⟨subd9_7_473, List.forall_mem_cons.2 ⟨subd9_7_474, List.forall_mem_cons.2 ⟨subd9_7_475, List.forall_mem_cons.2 ⟨subd9_7_476, List.forall_mem_cons.2 ⟨subd9_7_477, List.forall_mem_cons.2 ⟨subd9_7_478, List.forall_mem_cons.2 ⟨subd9_7_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_7_480 : subd9_7 [1, 2, 2] = true := by decide +kernel
theorem subd9_7_481 : subd9_7 [1, 2, 3] = true := by decide +kernel
theorem subd9_7_482 : subd9_7 [1, 2, 4] = true := by decide +kernel
theorem subd9_7_483 : subd9_7 [1, 2, 5] = true := by decide +kernel
theorem subd9_7_484 : subd9_7 [1, 2, 6] = true := by decide +kernel
theorem subd9_7_485 : subd9_7 [1, 2, 7] = true := by decide +kernel
theorem subd9_7_486 : subd9_7 [1, 3, -6] = true := by decide +kernel
theorem subd9_7_487 : subd9_7 [1, 3, -5] = true := by decide +kernel
theorem subd9_7_488 : subd9_7 [1, 3, -4] = true := by decide +kernel
theorem subd9_7_489 : subd9_7 [1, 3, -3] = true := by decide +kernel
theorem subd9_7_490 : subd9_7 [1, 3, -2] = true := by decide +kernel
theorem subd9_7_491 : subd9_7 [1, 3, -1] = true := by decide +kernel
theorem subd9_7_492 : subd9_7 [1, 3, 0] = true := by decide +kernel
theorem subd9_7_493 : subd9_7 [1, 3, 1] = true := by decide +kernel
theorem subd9_7_494 : subd9_7 [1, 3, 2] = true := by decide +kernel
theorem subd9_7_495 : subd9_7 [1, 3, 3] = true := by decide +kernel
theorem subd9_7_496 : subd9_7 [1, 3, 4] = true := by decide +kernel
theorem subd9_7_497 : subd9_7 [1, 3, 5] = true := by decide +kernel
theorem subd9_7_498 : subd9_7 [1, 3, 6] = true := by decide +kernel
theorem subd9_7_499 : subd9_7 [1, 3, 7] = true := by decide +kernel
theorem subd9_7_500 : subd9_7 [1, 4] = true := by decide +kernel
theorem subd9_7_501 : subd9_7 [2, -6] = true := by decide +kernel
theorem subd9_7_502 : subd9_7 [2, -5] = true := by decide +kernel
theorem subd9_7_503 : subd9_7 [2, -4] = true := by decide +kernel
theorem subd9_7_504 : subd9_7 [2, -3, -9] = true := by decide +kernel
theorem subd9_7_505 : subd9_7 [2, -3, -8] = true := by decide +kernel
theorem subd9_7_506 : subd9_7 [2, -3, -7] = true := by decide +kernel
theorem subd9_7_507 : subd9_7 [2, -3, -6] = true := by decide +kernel
theorem subd9_7_508 : subd9_7 [2, -3, -5] = true := by decide +kernel
theorem subd9_7_509 : subd9_7 [2, -3, -4] = true := by decide +kernel
theorem subd9_7_510 : subd9_7 [2, -3, -3] = true := by decide +kernel
theorem subd9_7_511 : subd9_7 [2, -3, -2] = true := by decide +kernel
theorem sbd9_7_15 : ∀ q ∈ blkd9_7_15, subd9_7 q = true := by
  unfold blkd9_7_15
  exact List.forall_mem_cons.2 ⟨subd9_7_480, List.forall_mem_cons.2 ⟨subd9_7_481, List.forall_mem_cons.2 ⟨subd9_7_482, List.forall_mem_cons.2 ⟨subd9_7_483, List.forall_mem_cons.2 ⟨subd9_7_484, List.forall_mem_cons.2 ⟨subd9_7_485, List.forall_mem_cons.2 ⟨subd9_7_486, List.forall_mem_cons.2 ⟨subd9_7_487, List.forall_mem_cons.2 ⟨subd9_7_488, List.forall_mem_cons.2 ⟨subd9_7_489, List.forall_mem_cons.2 ⟨subd9_7_490, List.forall_mem_cons.2 ⟨subd9_7_491, List.forall_mem_cons.2 ⟨subd9_7_492, List.forall_mem_cons.2 ⟨subd9_7_493, List.forall_mem_cons.2 ⟨subd9_7_494, List.forall_mem_cons.2 ⟨subd9_7_495, List.forall_mem_cons.2 ⟨subd9_7_496, List.forall_mem_cons.2 ⟨subd9_7_497, List.forall_mem_cons.2 ⟨subd9_7_498, List.forall_mem_cons.2 ⟨subd9_7_499, List.forall_mem_cons.2 ⟨subd9_7_500, List.forall_mem_cons.2 ⟨subd9_7_501, List.forall_mem_cons.2 ⟨subd9_7_502, List.forall_mem_cons.2 ⟨subd9_7_503, List.forall_mem_cons.2 ⟨subd9_7_504, List.forall_mem_cons.2 ⟨subd9_7_505, List.forall_mem_cons.2 ⟨subd9_7_506, List.forall_mem_cons.2 ⟨subd9_7_507, List.forall_mem_cons.2 ⟨subd9_7_508, List.forall_mem_cons.2 ⟨subd9_7_509, List.forall_mem_cons.2 ⟨subd9_7_510, List.forall_mem_cons.2 ⟨subd9_7_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_7_512 : subd9_7 [2, -3, -1] = true := by decide +kernel
theorem subd9_7_513 : subd9_7 [2, -3, 0] = true := by decide +kernel
theorem subd9_7_514 : subd9_7 [2, -3, 1] = true := by decide +kernel
theorem subd9_7_515 : subd9_7 [2, -3, 2] = true := by decide +kernel
theorem subd9_7_516 : subd9_7 [2, -3, 3] = true := by decide +kernel
theorem subd9_7_517 : subd9_7 [2, -3, 4] = true := by decide +kernel
theorem subd9_7_518 : subd9_7 [2, -3, 5] = true := by decide +kernel
theorem subd9_7_519 : subd9_7 [2, -2, -9] = true := by decide +kernel
theorem subd9_7_520 : subd9_7 [2, -2, -8] = true := by decide +kernel
theorem subd9_7_521 : subd9_7 [2, -2, -7] = true := by decide +kernel
theorem subd9_7_522 : subd9_7 [2, -2, -6] = true := by decide +kernel
theorem subd9_7_523 : subd9_7 [2, -2, -5] = true := by decide +kernel
theorem subd9_7_524 : subd9_7 [2, -2, -4] = true := by decide +kernel
theorem subd9_7_525 : subd9_7 [2, -2, -3] = true := by decide +kernel
theorem subd9_7_526 : subd9_7 [2, -2, -2] = true := by decide +kernel
theorem subd9_7_527 : subd9_7 [2, -2, -1] = true := by decide +kernel
theorem subd9_7_528 : subd9_7 [2, -2, 0] = true := by decide +kernel
theorem subd9_7_529 : subd9_7 [2, -2, 1] = true := by decide +kernel
theorem subd9_7_530 : subd9_7 [2, -2, 2] = true := by decide +kernel
theorem subd9_7_531 : subd9_7 [2, -2, 3] = true := by decide +kernel
theorem subd9_7_532 : subd9_7 [2, -2, 4] = true := by decide +kernel
theorem subd9_7_533 : subd9_7 [2, -2, 5] = true := by decide +kernel
theorem subd9_7_534 : subd9_7 [2, -2, 6] = true := by decide +kernel
theorem subd9_7_535 : subd9_7 [2, -1, -9] = true := by decide +kernel
theorem subd9_7_536 : subd9_7 [2, -1, -8] = true := by decide +kernel
theorem subd9_7_537 : subd9_7 [2, -1, -7] = true := by decide +kernel
theorem subd9_7_538 : subd9_7 [2, -1, -6] = true := by decide +kernel
theorem subd9_7_539 : subd9_7 [2, -1, -5] = true := by decide +kernel
theorem subd9_7_540 : subd9_7 [2, -1, -4] = true := by decide +kernel
theorem subd9_7_541 : subd9_7 [2, -1, -3] = true := by decide +kernel
theorem subd9_7_542 : subd9_7 [2, -1, -2] = true := by decide +kernel
theorem subd9_7_543 : subd9_7 [2, -1, -1] = true := by decide +kernel
theorem sbd9_7_16 : ∀ q ∈ blkd9_7_16, subd9_7 q = true := by
  unfold blkd9_7_16
  exact List.forall_mem_cons.2 ⟨subd9_7_512, List.forall_mem_cons.2 ⟨subd9_7_513, List.forall_mem_cons.2 ⟨subd9_7_514, List.forall_mem_cons.2 ⟨subd9_7_515, List.forall_mem_cons.2 ⟨subd9_7_516, List.forall_mem_cons.2 ⟨subd9_7_517, List.forall_mem_cons.2 ⟨subd9_7_518, List.forall_mem_cons.2 ⟨subd9_7_519, List.forall_mem_cons.2 ⟨subd9_7_520, List.forall_mem_cons.2 ⟨subd9_7_521, List.forall_mem_cons.2 ⟨subd9_7_522, List.forall_mem_cons.2 ⟨subd9_7_523, List.forall_mem_cons.2 ⟨subd9_7_524, List.forall_mem_cons.2 ⟨subd9_7_525, List.forall_mem_cons.2 ⟨subd9_7_526, List.forall_mem_cons.2 ⟨subd9_7_527, List.forall_mem_cons.2 ⟨subd9_7_528, List.forall_mem_cons.2 ⟨subd9_7_529, List.forall_mem_cons.2 ⟨subd9_7_530, List.forall_mem_cons.2 ⟨subd9_7_531, List.forall_mem_cons.2 ⟨subd9_7_532, List.forall_mem_cons.2 ⟨subd9_7_533, List.forall_mem_cons.2 ⟨subd9_7_534, List.forall_mem_cons.2 ⟨subd9_7_535, List.forall_mem_cons.2 ⟨subd9_7_536, List.forall_mem_cons.2 ⟨subd9_7_537, List.forall_mem_cons.2 ⟨subd9_7_538, List.forall_mem_cons.2 ⟨subd9_7_539, List.forall_mem_cons.2 ⟨subd9_7_540, List.forall_mem_cons.2 ⟨subd9_7_541, List.forall_mem_cons.2 ⟨subd9_7_542, List.forall_mem_cons.2 ⟨subd9_7_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_7_544 : subd9_7 [2, -1, 0] = true := by decide +kernel
theorem subd9_7_545 : subd9_7 [2, -1, 1] = true := by decide +kernel
theorem subd9_7_546 : subd9_7 [2, -1, 2] = true := by decide +kernel
theorem subd9_7_547 : subd9_7 [2, -1, 3] = true := by decide +kernel
theorem subd9_7_548 : subd9_7 [2, -1, 4] = true := by decide +kernel
theorem subd9_7_549 : subd9_7 [2, -1, 5] = true := by decide +kernel
theorem subd9_7_550 : subd9_7 [2, -1, 6] = true := by decide +kernel
theorem subd9_7_551 : subd9_7 [2, 0, -8] = true := by decide +kernel
theorem subd9_7_552 : subd9_7 [2, 0, -7] = true := by decide +kernel
theorem subd9_7_553 : subd9_7 [2, 0, -6] = true := by decide +kernel
theorem subd9_7_554 : subd9_7 [2, 0, -5] = true := by decide +kernel
theorem subd9_7_555 : subd9_7 [2, 0, -4] = true := by decide +kernel
theorem subd9_7_556 : subd9_7 [2, 0, -3] = true := by decide +kernel
theorem subd9_7_557 : subd9_7 [2, 0, -2] = true := by decide +kernel
theorem subd9_7_558 : subd9_7 [2, 0, -1] = true := by decide +kernel
theorem subd9_7_559 : subd9_7 [2, 0, 0] = true := by decide +kernel
theorem subd9_7_560 : subd9_7 [2, 0, 1] = true := by decide +kernel
theorem subd9_7_561 : subd9_7 [2, 0, 2] = true := by decide +kernel
theorem subd9_7_562 : subd9_7 [2, 0, 3] = true := by decide +kernel
theorem subd9_7_563 : subd9_7 [2, 0, 4] = true := by decide +kernel
theorem subd9_7_564 : subd9_7 [2, 0, 5] = true := by decide +kernel
theorem subd9_7_565 : subd9_7 [2, 0, 6] = true := by decide +kernel
theorem subd9_7_566 : subd9_7 [2, 0, 7] = true := by decide +kernel
theorem subd9_7_567 : subd9_7 [2, 1, -8] = true := by decide +kernel
theorem subd9_7_568 : subd9_7 [2, 1, -7] = true := by decide +kernel
theorem subd9_7_569 : subd9_7 [2, 1, -6] = true := by decide +kernel
theorem subd9_7_570 : subd9_7 [2, 1, -5] = true := by decide +kernel
theorem subd9_7_571 : subd9_7 [2, 1, -4] = true := by decide +kernel
theorem subd9_7_572 : subd9_7 [2, 1, -3] = true := by decide +kernel
theorem subd9_7_573 : subd9_7 [2, 1, -2] = true := by decide +kernel
theorem subd9_7_574 : subd9_7 [2, 1, -1] = true := by decide +kernel
theorem subd9_7_575 : subd9_7 [2, 1, 0] = true := by decide +kernel
theorem sbd9_7_17 : ∀ q ∈ blkd9_7_17, subd9_7 q = true := by
  unfold blkd9_7_17
  exact List.forall_mem_cons.2 ⟨subd9_7_544, List.forall_mem_cons.2 ⟨subd9_7_545, List.forall_mem_cons.2 ⟨subd9_7_546, List.forall_mem_cons.2 ⟨subd9_7_547, List.forall_mem_cons.2 ⟨subd9_7_548, List.forall_mem_cons.2 ⟨subd9_7_549, List.forall_mem_cons.2 ⟨subd9_7_550, List.forall_mem_cons.2 ⟨subd9_7_551, List.forall_mem_cons.2 ⟨subd9_7_552, List.forall_mem_cons.2 ⟨subd9_7_553, List.forall_mem_cons.2 ⟨subd9_7_554, List.forall_mem_cons.2 ⟨subd9_7_555, List.forall_mem_cons.2 ⟨subd9_7_556, List.forall_mem_cons.2 ⟨subd9_7_557, List.forall_mem_cons.2 ⟨subd9_7_558, List.forall_mem_cons.2 ⟨subd9_7_559, List.forall_mem_cons.2 ⟨subd9_7_560, List.forall_mem_cons.2 ⟨subd9_7_561, List.forall_mem_cons.2 ⟨subd9_7_562, List.forall_mem_cons.2 ⟨subd9_7_563, List.forall_mem_cons.2 ⟨subd9_7_564, List.forall_mem_cons.2 ⟨subd9_7_565, List.forall_mem_cons.2 ⟨subd9_7_566, List.forall_mem_cons.2 ⟨subd9_7_567, List.forall_mem_cons.2 ⟨subd9_7_568, List.forall_mem_cons.2 ⟨subd9_7_569, List.forall_mem_cons.2 ⟨subd9_7_570, List.forall_mem_cons.2 ⟨subd9_7_571, List.forall_mem_cons.2 ⟨subd9_7_572, List.forall_mem_cons.2 ⟨subd9_7_573, List.forall_mem_cons.2 ⟨subd9_7_574, List.forall_mem_cons.2 ⟨subd9_7_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_7_576 : subd9_7 [2, 1, 1] = true := by decide +kernel
theorem subd9_7_577 : subd9_7 [2, 1, 2] = true := by decide +kernel
theorem subd9_7_578 : subd9_7 [2, 1, 3] = true := by decide +kernel
theorem subd9_7_579 : subd9_7 [2, 1, 4] = true := by decide +kernel
theorem subd9_7_580 : subd9_7 [2, 1, 5] = true := by decide +kernel
theorem subd9_7_581 : subd9_7 [2, 1, 6] = true := by decide +kernel
theorem subd9_7_582 : subd9_7 [2, 1, 7] = true := by decide +kernel
theorem subd9_7_583 : subd9_7 [2, 2, -6] = true := by decide +kernel
theorem subd9_7_584 : subd9_7 [2, 2, -5] = true := by decide +kernel
theorem subd9_7_585 : subd9_7 [2, 2, -4] = true := by decide +kernel
theorem subd9_7_586 : subd9_7 [2, 2, -3] = true := by decide +kernel
theorem subd9_7_587 : subd9_7 [2, 2, -2] = true := by decide +kernel
theorem subd9_7_588 : subd9_7 [2, 2, -1] = true := by decide +kernel
theorem subd9_7_589 : subd9_7 [2, 2, 0] = true := by decide +kernel
theorem subd9_7_590 : subd9_7 [2, 2, 1] = true := by decide +kernel
theorem subd9_7_591 : subd9_7 [2, 2, 2] = true := by decide +kernel
theorem subd9_7_592 : subd9_7 [2, 2, 3] = true := by decide +kernel
theorem subd9_7_593 : subd9_7 [2, 2, 4] = true := by decide +kernel
theorem subd9_7_594 : subd9_7 [2, 2, 5] = true := by decide +kernel
theorem subd9_7_595 : subd9_7 [2, 2, 6] = true := by decide +kernel
theorem subd9_7_596 : subd9_7 [2, 3] = true := by decide +kernel
theorem subd9_7_597 : subd9_7 [2, 4] = true := by decide +kernel
theorem subd9_7_598 : subd9_7 [3, -6] = true := by decide +kernel
theorem subd9_7_599 : subd9_7 [3, -5] = true := by decide +kernel
theorem subd9_7_600 : subd9_7 [3, -4] = true := by decide +kernel
theorem subd9_7_601 : subd9_7 [3, -3] = true := by decide +kernel
theorem subd9_7_602 : subd9_7 [3, -2, -8] = true := by decide +kernel
theorem subd9_7_603 : subd9_7 [3, -2, -7] = true := by decide +kernel
theorem subd9_7_604 : subd9_7 [3, -2, -6] = true := by decide +kernel
theorem subd9_7_605 : subd9_7 [3, -2, -5] = true := by decide +kernel
theorem subd9_7_606 : subd9_7 [3, -2, -4] = true := by decide +kernel
theorem subd9_7_607 : subd9_7 [3, -2, -3] = true := by decide +kernel
theorem sbd9_7_18 : ∀ q ∈ blkd9_7_18, subd9_7 q = true := by
  unfold blkd9_7_18
  exact List.forall_mem_cons.2 ⟨subd9_7_576, List.forall_mem_cons.2 ⟨subd9_7_577, List.forall_mem_cons.2 ⟨subd9_7_578, List.forall_mem_cons.2 ⟨subd9_7_579, List.forall_mem_cons.2 ⟨subd9_7_580, List.forall_mem_cons.2 ⟨subd9_7_581, List.forall_mem_cons.2 ⟨subd9_7_582, List.forall_mem_cons.2 ⟨subd9_7_583, List.forall_mem_cons.2 ⟨subd9_7_584, List.forall_mem_cons.2 ⟨subd9_7_585, List.forall_mem_cons.2 ⟨subd9_7_586, List.forall_mem_cons.2 ⟨subd9_7_587, List.forall_mem_cons.2 ⟨subd9_7_588, List.forall_mem_cons.2 ⟨subd9_7_589, List.forall_mem_cons.2 ⟨subd9_7_590, List.forall_mem_cons.2 ⟨subd9_7_591, List.forall_mem_cons.2 ⟨subd9_7_592, List.forall_mem_cons.2 ⟨subd9_7_593, List.forall_mem_cons.2 ⟨subd9_7_594, List.forall_mem_cons.2 ⟨subd9_7_595, List.forall_mem_cons.2 ⟨subd9_7_596, List.forall_mem_cons.2 ⟨subd9_7_597, List.forall_mem_cons.2 ⟨subd9_7_598, List.forall_mem_cons.2 ⟨subd9_7_599, List.forall_mem_cons.2 ⟨subd9_7_600, List.forall_mem_cons.2 ⟨subd9_7_601, List.forall_mem_cons.2 ⟨subd9_7_602, List.forall_mem_cons.2 ⟨subd9_7_603, List.forall_mem_cons.2 ⟨subd9_7_604, List.forall_mem_cons.2 ⟨subd9_7_605, List.forall_mem_cons.2 ⟨subd9_7_606, List.forall_mem_cons.2 ⟨subd9_7_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_7_608 : subd9_7 [3, -2, -2] = true := by decide +kernel
theorem subd9_7_609 : subd9_7 [3, -2, -1] = true := by decide +kernel
theorem subd9_7_610 : subd9_7 [3, -2, 0] = true := by decide +kernel
theorem subd9_7_611 : subd9_7 [3, -2, 1] = true := by decide +kernel
theorem subd9_7_612 : subd9_7 [3, -2, 2] = true := by decide +kernel
theorem subd9_7_613 : subd9_7 [3, -2, 3] = true := by decide +kernel
theorem subd9_7_614 : subd9_7 [3, -2, 4] = true := by decide +kernel
theorem subd9_7_615 : subd9_7 [3, -2, 5] = true := by decide +kernel
theorem subd9_7_616 : subd9_7 [3, -1, -8] = true := by decide +kernel
theorem subd9_7_617 : subd9_7 [3, -1, -7] = true := by decide +kernel
theorem subd9_7_618 : subd9_7 [3, -1, -6] = true := by decide +kernel
theorem subd9_7_619 : subd9_7 [3, -1, -5] = true := by decide +kernel
theorem subd9_7_620 : subd9_7 [3, -1, -4] = true := by decide +kernel
theorem subd9_7_621 : subd9_7 [3, -1, -3] = true := by decide +kernel
theorem subd9_7_622 : subd9_7 [3, -1, -2] = true := by decide +kernel
theorem subd9_7_623 : subd9_7 [3, -1, -1] = true := by decide +kernel
theorem subd9_7_624 : subd9_7 [3, -1, 0] = true := by decide +kernel
theorem subd9_7_625 : subd9_7 [3, -1, 1] = true := by decide +kernel
theorem subd9_7_626 : subd9_7 [3, -1, 2] = true := by decide +kernel
theorem subd9_7_627 : subd9_7 [3, -1, 3] = true := by decide +kernel
theorem subd9_7_628 : subd9_7 [3, -1, 4] = true := by decide +kernel
theorem subd9_7_629 : subd9_7 [3, -1, 5] = true := by decide +kernel
theorem subd9_7_630 : subd9_7 [3, 0, -7] = true := by decide +kernel
theorem subd9_7_631 : subd9_7 [3, 0, -6] = true := by decide +kernel
theorem subd9_7_632 : subd9_7 [3, 0, -5] = true := by decide +kernel
theorem subd9_7_633 : subd9_7 [3, 0, -4] = true := by decide +kernel
theorem subd9_7_634 : subd9_7 [3, 0, -3] = true := by decide +kernel
theorem subd9_7_635 : subd9_7 [3, 0, -2] = true := by decide +kernel
theorem subd9_7_636 : subd9_7 [3, 0, -1] = true := by decide +kernel
theorem subd9_7_637 : subd9_7 [3, 0, 0] = true := by decide +kernel
theorem subd9_7_638 : subd9_7 [3, 0, 1] = true := by decide +kernel
theorem subd9_7_639 : subd9_7 [3, 0, 2] = true := by decide +kernel
theorem sbd9_7_19 : ∀ q ∈ blkd9_7_19, subd9_7 q = true := by
  unfold blkd9_7_19
  exact List.forall_mem_cons.2 ⟨subd9_7_608, List.forall_mem_cons.2 ⟨subd9_7_609, List.forall_mem_cons.2 ⟨subd9_7_610, List.forall_mem_cons.2 ⟨subd9_7_611, List.forall_mem_cons.2 ⟨subd9_7_612, List.forall_mem_cons.2 ⟨subd9_7_613, List.forall_mem_cons.2 ⟨subd9_7_614, List.forall_mem_cons.2 ⟨subd9_7_615, List.forall_mem_cons.2 ⟨subd9_7_616, List.forall_mem_cons.2 ⟨subd9_7_617, List.forall_mem_cons.2 ⟨subd9_7_618, List.forall_mem_cons.2 ⟨subd9_7_619, List.forall_mem_cons.2 ⟨subd9_7_620, List.forall_mem_cons.2 ⟨subd9_7_621, List.forall_mem_cons.2 ⟨subd9_7_622, List.forall_mem_cons.2 ⟨subd9_7_623, List.forall_mem_cons.2 ⟨subd9_7_624, List.forall_mem_cons.2 ⟨subd9_7_625, List.forall_mem_cons.2 ⟨subd9_7_626, List.forall_mem_cons.2 ⟨subd9_7_627, List.forall_mem_cons.2 ⟨subd9_7_628, List.forall_mem_cons.2 ⟨subd9_7_629, List.forall_mem_cons.2 ⟨subd9_7_630, List.forall_mem_cons.2 ⟨subd9_7_631, List.forall_mem_cons.2 ⟨subd9_7_632, List.forall_mem_cons.2 ⟨subd9_7_633, List.forall_mem_cons.2 ⟨subd9_7_634, List.forall_mem_cons.2 ⟨subd9_7_635, List.forall_mem_cons.2 ⟨subd9_7_636, List.forall_mem_cons.2 ⟨subd9_7_637, List.forall_mem_cons.2 ⟨subd9_7_638, List.forall_mem_cons.2 ⟨subd9_7_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_7_640 : subd9_7 [3, 0, 3] = true := by decide +kernel
theorem subd9_7_641 : subd9_7 [3, 0, 4] = true := by decide +kernel
theorem subd9_7_642 : subd9_7 [3, 0, 5] = true := by decide +kernel
theorem subd9_7_643 : subd9_7 [3, 1] = true := by decide +kernel
theorem subd9_7_644 : subd9_7 [3, 2] = true := by decide +kernel
theorem subd9_7_645 : subd9_7 [3, 3] = true := by decide +kernel
theorem subd9_7_646 : subd9_7 [4, -5] = true := by decide +kernel
theorem subd9_7_647 : subd9_7 [4, -4] = true := by decide +kernel
theorem subd9_7_648 : subd9_7 [4, -3] = true := by decide +kernel
theorem subd9_7_649 : subd9_7 [4, -2] = true := by decide +kernel
theorem subd9_7_650 : subd9_7 [4, -1] = true := by decide +kernel
theorem subd9_7_651 : subd9_7 [4, 0] = true := by decide +kernel
theorem subd9_7_652 : subd9_7 [4, 1] = true := by decide +kernel
theorem sbd9_7_20 : ∀ q ∈ blkd9_7_20, subd9_7 q = true := by
  unfold blkd9_7_20
  exact List.forall_mem_cons.2 ⟨subd9_7_640, List.forall_mem_cons.2 ⟨subd9_7_641, List.forall_mem_cons.2 ⟨subd9_7_642, List.forall_mem_cons.2 ⟨subd9_7_643, List.forall_mem_cons.2 ⟨subd9_7_644, List.forall_mem_cons.2 ⟨subd9_7_645, List.forall_mem_cons.2 ⟨subd9_7_646, List.forall_mem_cons.2 ⟨subd9_7_647, List.forall_mem_cons.2 ⟨subd9_7_648, List.forall_mem_cons.2 ⟨subd9_7_649, List.forall_mem_cons.2 ⟨subd9_7_650, List.forall_mem_cons.2 ⟨subd9_7_651, List.forall_mem_cons.2 ⟨subd9_7_652, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_0 : ldCheck G d10_0.U d10_0.ms ldd10_0 = true := by decide +kernel
theorem pre_okd10_0 : subPre G cell10 d10_0 = true := by decide +kernel
theorem subd10_0_0 : subd10_0 [-2] = true := by decide +kernel
theorem subd10_0_1 : subd10_0 [-1] = true := by decide +kernel
theorem subd10_0_2 : subd10_0 [0, -3] = true := by decide +kernel
theorem subd10_0_3 : subd10_0 [0, -2] = true := by decide +kernel
theorem subd10_0_4 : subd10_0 [0, -1] = true := by decide +kernel
theorem subd10_0_5 : subd10_0 [0, 0] = true := by decide +kernel
theorem subd10_0_6 : subd10_0 [0, 1] = true := by decide +kernel
theorem subd10_0_7 : subd10_0 [0, 2] = true := by decide +kernel
theorem subd10_0_8 : subd10_0 [1] = true := by decide +kernel
theorem subd10_0_9 : subd10_0 [2] = true := by decide +kernel
theorem sbd10_0_0 : ∀ q ∈ blkd10_0_0, subd10_0 q = true := by
  unfold blkd10_0_0
  exact List.forall_mem_cons.2 ⟨subd10_0_0, List.forall_mem_cons.2 ⟨subd10_0_1, List.forall_mem_cons.2 ⟨subd10_0_2, List.forall_mem_cons.2 ⟨subd10_0_3, List.forall_mem_cons.2 ⟨subd10_0_4, List.forall_mem_cons.2 ⟨subd10_0_5, List.forall_mem_cons.2 ⟨subd10_0_6, List.forall_mem_cons.2 ⟨subd10_0_7, List.forall_mem_cons.2 ⟨subd10_0_8, List.forall_mem_cons.2 ⟨subd10_0_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
