import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_1_288 : subd7_1 [0, -2, 6] = true := by decide +kernel
theorem subd7_1_289 : subd7_1 [0, -1, -8] = true := by decide +kernel
theorem subd7_1_290 : subd7_1 [0, -1, -7] = true := by decide +kernel
theorem subd7_1_291 : subd7_1 [0, -1, -6] = true := by decide +kernel
theorem subd7_1_292 : subd7_1 [0, -1, -5] = true := by decide +kernel
theorem subd7_1_293 : subd7_1 [0, -1, -4] = true := by decide +kernel
theorem subd7_1_294 : subd7_1 [0, -1, -3] = true := by decide +kernel
theorem subd7_1_295 : subd7_1 [0, -1, -2] = true := by decide +kernel
theorem subd7_1_296 : subd7_1 [0, -1, -1] = true := by decide +kernel
theorem subd7_1_297 : subd7_1 [0, -1, 0] = true := by decide +kernel
theorem subd7_1_298 : subd7_1 [0, -1, 1] = true := by decide +kernel
theorem subd7_1_299 : subd7_1 [0, -1, 2] = true := by decide +kernel
theorem subd7_1_300 : subd7_1 [0, -1, 3] = true := by decide +kernel
theorem subd7_1_301 : subd7_1 [0, -1, 4] = true := by decide +kernel
theorem subd7_1_302 : subd7_1 [0, -1, 5] = true := by decide +kernel
theorem subd7_1_303 : subd7_1 [0, -1, 6] = true := by decide +kernel
theorem subd7_1_304 : subd7_1 [0, 0, -8] = true := by decide +kernel
theorem subd7_1_305 : subd7_1 [0, 0, -7] = true := by decide +kernel
theorem subd7_1_306 : subd7_1 [0, 0, -6] = true := by decide +kernel
theorem subd7_1_307 : subd7_1 [0, 0, -5] = true := by decide +kernel
theorem subd7_1_308 : subd7_1 [0, 0, -4] = true := by decide +kernel
theorem subd7_1_309 : subd7_1 [0, 0, -3] = true := by decide +kernel
theorem subd7_1_310 : subd7_1 [0, 0, -2] = true := by decide +kernel
theorem subd7_1_311 : subd7_1 [0, 0, -1] = true := by decide +kernel
theorem subd7_1_312 : subd7_1 [0, 0, 0] = true := by decide +kernel
theorem subd7_1_313 : subd7_1 [0, 0, 1] = true := by decide +kernel
theorem subd7_1_314 : subd7_1 [0, 0, 2] = true := by decide +kernel
theorem subd7_1_315 : subd7_1 [0, 0, 3] = true := by decide +kernel
theorem subd7_1_316 : subd7_1 [0, 0, 4] = true := by decide +kernel
theorem subd7_1_317 : subd7_1 [0, 0, 5] = true := by decide +kernel
theorem subd7_1_318 : subd7_1 [0, 0, 6] = true := by decide +kernel
theorem subd7_1_319 : subd7_1 [0, 0, 7] = true := by decide +kernel
theorem sbd7_1_9 : ∀ q ∈ blkd7_1_9, subd7_1 q = true := by
  unfold blkd7_1_9
  exact List.forall_mem_cons.2 ⟨subd7_1_288, List.forall_mem_cons.2 ⟨subd7_1_289, List.forall_mem_cons.2 ⟨subd7_1_290, List.forall_mem_cons.2 ⟨subd7_1_291, List.forall_mem_cons.2 ⟨subd7_1_292, List.forall_mem_cons.2 ⟨subd7_1_293, List.forall_mem_cons.2 ⟨subd7_1_294, List.forall_mem_cons.2 ⟨subd7_1_295, List.forall_mem_cons.2 ⟨subd7_1_296, List.forall_mem_cons.2 ⟨subd7_1_297, List.forall_mem_cons.2 ⟨subd7_1_298, List.forall_mem_cons.2 ⟨subd7_1_299, List.forall_mem_cons.2 ⟨subd7_1_300, List.forall_mem_cons.2 ⟨subd7_1_301, List.forall_mem_cons.2 ⟨subd7_1_302, List.forall_mem_cons.2 ⟨subd7_1_303, List.forall_mem_cons.2 ⟨subd7_1_304, List.forall_mem_cons.2 ⟨subd7_1_305, List.forall_mem_cons.2 ⟨subd7_1_306, List.forall_mem_cons.2 ⟨subd7_1_307, List.forall_mem_cons.2 ⟨subd7_1_308, List.forall_mem_cons.2 ⟨subd7_1_309, List.forall_mem_cons.2 ⟨subd7_1_310, List.forall_mem_cons.2 ⟨subd7_1_311, List.forall_mem_cons.2 ⟨subd7_1_312, List.forall_mem_cons.2 ⟨subd7_1_313, List.forall_mem_cons.2 ⟨subd7_1_314, List.forall_mem_cons.2 ⟨subd7_1_315, List.forall_mem_cons.2 ⟨subd7_1_316, List.forall_mem_cons.2 ⟨subd7_1_317, List.forall_mem_cons.2 ⟨subd7_1_318, List.forall_mem_cons.2 ⟨subd7_1_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_320 : subd7_1 [0, 1, -7] = true := by decide +kernel
theorem subd7_1_321 : subd7_1 [0, 1, -6] = true := by decide +kernel
theorem subd7_1_322 : subd7_1 [0, 1, -5] = true := by decide +kernel
theorem subd7_1_323 : subd7_1 [0, 1, -4] = true := by decide +kernel
theorem subd7_1_324 : subd7_1 [0, 1, -3] = true := by decide +kernel
theorem subd7_1_325 : subd7_1 [0, 1, -2] = true := by decide +kernel
theorem subd7_1_326 : subd7_1 [0, 1, -1] = true := by decide +kernel
theorem subd7_1_327 : subd7_1 [0, 1, 0] = true := by decide +kernel
theorem subd7_1_328 : subd7_1 [0, 1, 1] = true := by decide +kernel
theorem subd7_1_329 : subd7_1 [0, 1, 2] = true := by decide +kernel
theorem subd7_1_330 : subd7_1 [0, 1, 3] = true := by decide +kernel
theorem subd7_1_331 : subd7_1 [0, 1, 4] = true := by decide +kernel
theorem subd7_1_332 : subd7_1 [0, 1, 5] = true := by decide +kernel
theorem subd7_1_333 : subd7_1 [0, 1, 6] = true := by decide +kernel
theorem subd7_1_334 : subd7_1 [0, 1, 7] = true := by decide +kernel
theorem subd7_1_335 : subd7_1 [0, 2, -7] = true := by decide +kernel
theorem subd7_1_336 : subd7_1 [0, 2, -6] = true := by decide +kernel
theorem subd7_1_337 : subd7_1 [0, 2, -5] = true := by decide +kernel
theorem subd7_1_338 : subd7_1 [0, 2, -4] = true := by decide +kernel
theorem subd7_1_339 : subd7_1 [0, 2, -3] = true := by decide +kernel
theorem subd7_1_340 : subd7_1 [0, 2, -2] = true := by decide +kernel
theorem subd7_1_341 : subd7_1 [0, 2, -1] = true := by decide +kernel
theorem subd7_1_342 : subd7_1 [0, 2, 0] = true := by decide +kernel
theorem subd7_1_343 : subd7_1 [0, 2, 1] = true := by decide +kernel
theorem subd7_1_344 : subd7_1 [0, 2, 2] = true := by decide +kernel
theorem subd7_1_345 : subd7_1 [0, 2, 3] = true := by decide +kernel
theorem subd7_1_346 : subd7_1 [0, 2, 4] = true := by decide +kernel
theorem subd7_1_347 : subd7_1 [0, 2, 5] = true := by decide +kernel
theorem subd7_1_348 : subd7_1 [0, 2, 6] = true := by decide +kernel
theorem subd7_1_349 : subd7_1 [0, 2, 7] = true := by decide +kernel
theorem subd7_1_350 : subd7_1 [0, 2, 8] = true := by decide +kernel
theorem subd7_1_351 : subd7_1 [0, 3, -6] = true := by decide +kernel
theorem sbd7_1_10 : ∀ q ∈ blkd7_1_10, subd7_1 q = true := by
  unfold blkd7_1_10
  exact List.forall_mem_cons.2 ⟨subd7_1_320, List.forall_mem_cons.2 ⟨subd7_1_321, List.forall_mem_cons.2 ⟨subd7_1_322, List.forall_mem_cons.2 ⟨subd7_1_323, List.forall_mem_cons.2 ⟨subd7_1_324, List.forall_mem_cons.2 ⟨subd7_1_325, List.forall_mem_cons.2 ⟨subd7_1_326, List.forall_mem_cons.2 ⟨subd7_1_327, List.forall_mem_cons.2 ⟨subd7_1_328, List.forall_mem_cons.2 ⟨subd7_1_329, List.forall_mem_cons.2 ⟨subd7_1_330, List.forall_mem_cons.2 ⟨subd7_1_331, List.forall_mem_cons.2 ⟨subd7_1_332, List.forall_mem_cons.2 ⟨subd7_1_333, List.forall_mem_cons.2 ⟨subd7_1_334, List.forall_mem_cons.2 ⟨subd7_1_335, List.forall_mem_cons.2 ⟨subd7_1_336, List.forall_mem_cons.2 ⟨subd7_1_337, List.forall_mem_cons.2 ⟨subd7_1_338, List.forall_mem_cons.2 ⟨subd7_1_339, List.forall_mem_cons.2 ⟨subd7_1_340, List.forall_mem_cons.2 ⟨subd7_1_341, List.forall_mem_cons.2 ⟨subd7_1_342, List.forall_mem_cons.2 ⟨subd7_1_343, List.forall_mem_cons.2 ⟨subd7_1_344, List.forall_mem_cons.2 ⟨subd7_1_345, List.forall_mem_cons.2 ⟨subd7_1_346, List.forall_mem_cons.2 ⟨subd7_1_347, List.forall_mem_cons.2 ⟨subd7_1_348, List.forall_mem_cons.2 ⟨subd7_1_349, List.forall_mem_cons.2 ⟨subd7_1_350, List.forall_mem_cons.2 ⟨subd7_1_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_352 : subd7_1 [0, 3, -5] = true := by decide +kernel
theorem subd7_1_353 : subd7_1 [0, 3, -4] = true := by decide +kernel
theorem subd7_1_354 : subd7_1 [0, 3, -3] = true := by decide +kernel
theorem subd7_1_355 : subd7_1 [0, 3, -2] = true := by decide +kernel
theorem subd7_1_356 : subd7_1 [0, 3, -1] = true := by decide +kernel
theorem subd7_1_357 : subd7_1 [0, 3, 0] = true := by decide +kernel
theorem subd7_1_358 : subd7_1 [0, 3, 1] = true := by decide +kernel
theorem subd7_1_359 : subd7_1 [0, 3, 2] = true := by decide +kernel
theorem subd7_1_360 : subd7_1 [0, 3, 3] = true := by decide +kernel
theorem subd7_1_361 : subd7_1 [0, 3, 4] = true := by decide +kernel
theorem subd7_1_362 : subd7_1 [0, 3, 5] = true := by decide +kernel
theorem subd7_1_363 : subd7_1 [0, 3, 6] = true := by decide +kernel
theorem subd7_1_364 : subd7_1 [0, 3, 7] = true := by decide +kernel
theorem subd7_1_365 : subd7_1 [0, 3, 8] = true := by decide +kernel
theorem subd7_1_366 : subd7_1 [0, 4] = true := by decide +kernel
theorem subd7_1_367 : subd7_1 [0, 5] = true := by decide +kernel
theorem subd7_1_368 : subd7_1 [0, 6] = true := by decide +kernel
theorem subd7_1_369 : subd7_1 [1, -7] = true := by decide +kernel
theorem subd7_1_370 : subd7_1 [1, -6] = true := by decide +kernel
theorem subd7_1_371 : subd7_1 [1, -5] = true := by decide +kernel
theorem subd7_1_372 : subd7_1 [1, -4] = true := by decide +kernel
theorem subd7_1_373 : subd7_1 [1, -3, -9] = true := by decide +kernel
theorem subd7_1_374 : subd7_1 [1, -3, -8] = true := by decide +kernel
theorem subd7_1_375 : subd7_1 [1, -3, -7] = true := by decide +kernel
theorem subd7_1_376 : subd7_1 [1, -3, -6] = true := by decide +kernel
theorem subd7_1_377 : subd7_1 [1, -3, -5] = true := by decide +kernel
theorem subd7_1_378 : subd7_1 [1, -3, -4] = true := by decide +kernel
theorem subd7_1_379 : subd7_1 [1, -3, -3] = true := by decide +kernel
theorem subd7_1_380 : subd7_1 [1, -3, -2] = true := by decide +kernel
theorem subd7_1_381 : subd7_1 [1, -3, -1] = true := by decide +kernel
theorem subd7_1_382 : subd7_1 [1, -3, 0] = true := by decide +kernel
theorem subd7_1_383 : subd7_1 [1, -3, 1] = true := by decide +kernel
theorem sbd7_1_11 : ∀ q ∈ blkd7_1_11, subd7_1 q = true := by
  unfold blkd7_1_11
  exact List.forall_mem_cons.2 ⟨subd7_1_352, List.forall_mem_cons.2 ⟨subd7_1_353, List.forall_mem_cons.2 ⟨subd7_1_354, List.forall_mem_cons.2 ⟨subd7_1_355, List.forall_mem_cons.2 ⟨subd7_1_356, List.forall_mem_cons.2 ⟨subd7_1_357, List.forall_mem_cons.2 ⟨subd7_1_358, List.forall_mem_cons.2 ⟨subd7_1_359, List.forall_mem_cons.2 ⟨subd7_1_360, List.forall_mem_cons.2 ⟨subd7_1_361, List.forall_mem_cons.2 ⟨subd7_1_362, List.forall_mem_cons.2 ⟨subd7_1_363, List.forall_mem_cons.2 ⟨subd7_1_364, List.forall_mem_cons.2 ⟨subd7_1_365, List.forall_mem_cons.2 ⟨subd7_1_366, List.forall_mem_cons.2 ⟨subd7_1_367, List.forall_mem_cons.2 ⟨subd7_1_368, List.forall_mem_cons.2 ⟨subd7_1_369, List.forall_mem_cons.2 ⟨subd7_1_370, List.forall_mem_cons.2 ⟨subd7_1_371, List.forall_mem_cons.2 ⟨subd7_1_372, List.forall_mem_cons.2 ⟨subd7_1_373, List.forall_mem_cons.2 ⟨subd7_1_374, List.forall_mem_cons.2 ⟨subd7_1_375, List.forall_mem_cons.2 ⟨subd7_1_376, List.forall_mem_cons.2 ⟨subd7_1_377, List.forall_mem_cons.2 ⟨subd7_1_378, List.forall_mem_cons.2 ⟨subd7_1_379, List.forall_mem_cons.2 ⟨subd7_1_380, List.forall_mem_cons.2 ⟨subd7_1_381, List.forall_mem_cons.2 ⟨subd7_1_382, List.forall_mem_cons.2 ⟨subd7_1_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_384 : subd7_1 [1, -3, 2] = true := by decide +kernel
theorem subd7_1_385 : subd7_1 [1, -3, 3] = true := by decide +kernel
theorem subd7_1_386 : subd7_1 [1, -3, 4] = true := by decide +kernel
theorem subd7_1_387 : subd7_1 [1, -3, 5] = true := by decide +kernel
theorem subd7_1_388 : subd7_1 [1, -2, -9] = true := by decide +kernel
theorem subd7_1_389 : subd7_1 [1, -2, -8] = true := by decide +kernel
theorem subd7_1_390 : subd7_1 [1, -2, -7] = true := by decide +kernel
theorem subd7_1_391 : subd7_1 [1, -2, -6] = true := by decide +kernel
theorem subd7_1_392 : subd7_1 [1, -2, -5] = true := by decide +kernel
theorem subd7_1_393 : subd7_1 [1, -2, -4] = true := by decide +kernel
theorem subd7_1_394 : subd7_1 [1, -2, -3] = true := by decide +kernel
theorem subd7_1_395 : subd7_1 [1, -2, -2] = true := by decide +kernel
theorem subd7_1_396 : subd7_1 [1, -2, -1] = true := by decide +kernel
theorem subd7_1_397 : subd7_1 [1, -2, 0] = true := by decide +kernel
theorem subd7_1_398 : subd7_1 [1, -2, 1] = true := by decide +kernel
theorem subd7_1_399 : subd7_1 [1, -2, 2] = true := by decide +kernel
theorem subd7_1_400 : subd7_1 [1, -2, 3] = true := by decide +kernel
theorem subd7_1_401 : subd7_1 [1, -2, 4] = true := by decide +kernel
theorem subd7_1_402 : subd7_1 [1, -2, 5] = true := by decide +kernel
theorem subd7_1_403 : subd7_1 [1, -2, 6] = true := by decide +kernel
theorem subd7_1_404 : subd7_1 [1, -1, -8] = true := by decide +kernel
theorem subd7_1_405 : subd7_1 [1, -1, -7] = true := by decide +kernel
theorem subd7_1_406 : subd7_1 [1, -1, -6] = true := by decide +kernel
theorem subd7_1_407 : subd7_1 [1, -1, -5] = true := by decide +kernel
theorem subd7_1_408 : subd7_1 [1, -1, -4] = true := by decide +kernel
theorem subd7_1_409 : subd7_1 [1, -1, -3] = true := by decide +kernel
theorem subd7_1_410 : subd7_1 [1, -1, -2] = true := by decide +kernel
theorem subd7_1_411 : subd7_1 [1, -1, -1] = true := by decide +kernel
theorem subd7_1_412 : subd7_1 [1, -1, 0] = true := by decide +kernel
theorem subd7_1_413 : subd7_1 [1, -1, 1] = true := by decide +kernel
theorem subd7_1_414 : subd7_1 [1, -1, 2] = true := by decide +kernel
theorem subd7_1_415 : subd7_1 [1, -1, 3] = true := by decide +kernel
theorem sbd7_1_12 : ∀ q ∈ blkd7_1_12, subd7_1 q = true := by
  unfold blkd7_1_12
  exact List.forall_mem_cons.2 ⟨subd7_1_384, List.forall_mem_cons.2 ⟨subd7_1_385, List.forall_mem_cons.2 ⟨subd7_1_386, List.forall_mem_cons.2 ⟨subd7_1_387, List.forall_mem_cons.2 ⟨subd7_1_388, List.forall_mem_cons.2 ⟨subd7_1_389, List.forall_mem_cons.2 ⟨subd7_1_390, List.forall_mem_cons.2 ⟨subd7_1_391, List.forall_mem_cons.2 ⟨subd7_1_392, List.forall_mem_cons.2 ⟨subd7_1_393, List.forall_mem_cons.2 ⟨subd7_1_394, List.forall_mem_cons.2 ⟨subd7_1_395, List.forall_mem_cons.2 ⟨subd7_1_396, List.forall_mem_cons.2 ⟨subd7_1_397, List.forall_mem_cons.2 ⟨subd7_1_398, List.forall_mem_cons.2 ⟨subd7_1_399, List.forall_mem_cons.2 ⟨subd7_1_400, List.forall_mem_cons.2 ⟨subd7_1_401, List.forall_mem_cons.2 ⟨subd7_1_402, List.forall_mem_cons.2 ⟨subd7_1_403, List.forall_mem_cons.2 ⟨subd7_1_404, List.forall_mem_cons.2 ⟨subd7_1_405, List.forall_mem_cons.2 ⟨subd7_1_406, List.forall_mem_cons.2 ⟨subd7_1_407, List.forall_mem_cons.2 ⟨subd7_1_408, List.forall_mem_cons.2 ⟨subd7_1_409, List.forall_mem_cons.2 ⟨subd7_1_410, List.forall_mem_cons.2 ⟨subd7_1_411, List.forall_mem_cons.2 ⟨subd7_1_412, List.forall_mem_cons.2 ⟨subd7_1_413, List.forall_mem_cons.2 ⟨subd7_1_414, List.forall_mem_cons.2 ⟨subd7_1_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_416 : subd7_1 [1, -1, 4] = true := by decide +kernel
theorem subd7_1_417 : subd7_1 [1, -1, 5] = true := by decide +kernel
theorem subd7_1_418 : subd7_1 [1, -1, 6] = true := by decide +kernel
theorem subd7_1_419 : subd7_1 [1, 0, -8] = true := by decide +kernel
theorem subd7_1_420 : subd7_1 [1, 0, -7] = true := by decide +kernel
theorem subd7_1_421 : subd7_1 [1, 0, -6] = true := by decide +kernel
theorem subd7_1_422 : subd7_1 [1, 0, -5] = true := by decide +kernel
theorem subd7_1_423 : subd7_1 [1, 0, -4] = true := by decide +kernel
theorem subd7_1_424 : subd7_1 [1, 0, -3] = true := by decide +kernel
theorem subd7_1_425 : subd7_1 [1, 0, -2] = true := by decide +kernel
theorem subd7_1_426 : subd7_1 [1, 0, -1] = true := by decide +kernel
theorem subd7_1_427 : subd7_1 [1, 0, 0] = true := by decide +kernel
theorem subd7_1_428 : subd7_1 [1, 0, 1] = true := by decide +kernel
theorem subd7_1_429 : subd7_1 [1, 0, 2] = true := by decide +kernel
theorem subd7_1_430 : subd7_1 [1, 0, 3] = true := by decide +kernel
theorem subd7_1_431 : subd7_1 [1, 0, 4] = true := by decide +kernel
theorem subd7_1_432 : subd7_1 [1, 0, 5] = true := by decide +kernel
theorem subd7_1_433 : subd7_1 [1, 0, 6] = true := by decide +kernel
theorem subd7_1_434 : subd7_1 [1, 0, 7] = true := by decide +kernel
theorem subd7_1_435 : subd7_1 [1, 1, -8] = true := by decide +kernel
theorem subd7_1_436 : subd7_1 [1, 1, -7] = true := by decide +kernel
theorem subd7_1_437 : subd7_1 [1, 1, -6] = true := by decide +kernel
theorem subd7_1_438 : subd7_1 [1, 1, -5] = true := by decide +kernel
theorem subd7_1_439 : subd7_1 [1, 1, -4] = true := by decide +kernel
theorem subd7_1_440 : subd7_1 [1, 1, -3] = true := by decide +kernel
theorem subd7_1_441 : subd7_1 [1, 1, -2] = true := by decide +kernel
theorem subd7_1_442 : subd7_1 [1, 1, -1] = true := by decide +kernel
theorem subd7_1_443 : subd7_1 [1, 1, 0] = true := by decide +kernel
theorem subd7_1_444 : subd7_1 [1, 1, 1] = true := by decide +kernel
theorem subd7_1_445 : subd7_1 [1, 1, 2] = true := by decide +kernel
theorem subd7_1_446 : subd7_1 [1, 1, 3] = true := by decide +kernel
theorem subd7_1_447 : subd7_1 [1, 1, 4] = true := by decide +kernel
theorem sbd7_1_13 : ∀ q ∈ blkd7_1_13, subd7_1 q = true := by
  unfold blkd7_1_13
  exact List.forall_mem_cons.2 ⟨subd7_1_416, List.forall_mem_cons.2 ⟨subd7_1_417, List.forall_mem_cons.2 ⟨subd7_1_418, List.forall_mem_cons.2 ⟨subd7_1_419, List.forall_mem_cons.2 ⟨subd7_1_420, List.forall_mem_cons.2 ⟨subd7_1_421, List.forall_mem_cons.2 ⟨subd7_1_422, List.forall_mem_cons.2 ⟨subd7_1_423, List.forall_mem_cons.2 ⟨subd7_1_424, List.forall_mem_cons.2 ⟨subd7_1_425, List.forall_mem_cons.2 ⟨subd7_1_426, List.forall_mem_cons.2 ⟨subd7_1_427, List.forall_mem_cons.2 ⟨subd7_1_428, List.forall_mem_cons.2 ⟨subd7_1_429, List.forall_mem_cons.2 ⟨subd7_1_430, List.forall_mem_cons.2 ⟨subd7_1_431, List.forall_mem_cons.2 ⟨subd7_1_432, List.forall_mem_cons.2 ⟨subd7_1_433, List.forall_mem_cons.2 ⟨subd7_1_434, List.forall_mem_cons.2 ⟨subd7_1_435, List.forall_mem_cons.2 ⟨subd7_1_436, List.forall_mem_cons.2 ⟨subd7_1_437, List.forall_mem_cons.2 ⟨subd7_1_438, List.forall_mem_cons.2 ⟨subd7_1_439, List.forall_mem_cons.2 ⟨subd7_1_440, List.forall_mem_cons.2 ⟨subd7_1_441, List.forall_mem_cons.2 ⟨subd7_1_442, List.forall_mem_cons.2 ⟨subd7_1_443, List.forall_mem_cons.2 ⟨subd7_1_444, List.forall_mem_cons.2 ⟨subd7_1_445, List.forall_mem_cons.2 ⟨subd7_1_446, List.forall_mem_cons.2 ⟨subd7_1_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_448 : subd7_1 [1, 1, 5] = true := by decide +kernel
theorem subd7_1_449 : subd7_1 [1, 1, 6] = true := by decide +kernel
theorem subd7_1_450 : subd7_1 [1, 1, 7] = true := by decide +kernel
theorem subd7_1_451 : subd7_1 [1, 2, -7] = true := by decide +kernel
theorem subd7_1_452 : subd7_1 [1, 2, -6] = true := by decide +kernel
theorem subd7_1_453 : subd7_1 [1, 2, -5] = true := by decide +kernel
theorem subd7_1_454 : subd7_1 [1, 2, -4] = true := by decide +kernel
theorem subd7_1_455 : subd7_1 [1, 2, -3] = true := by decide +kernel
theorem subd7_1_456 : subd7_1 [1, 2, -2] = true := by decide +kernel
theorem subd7_1_457 : subd7_1 [1, 2, -1] = true := by decide +kernel
theorem subd7_1_458 : subd7_1 [1, 2, 0] = true := by decide +kernel
theorem subd7_1_459 : subd7_1 [1, 2, 1] = true := by decide +kernel
theorem subd7_1_460 : subd7_1 [1, 2, 2] = true := by decide +kernel
theorem subd7_1_461 : subd7_1 [1, 2, 3] = true := by decide +kernel
theorem subd7_1_462 : subd7_1 [1, 2, 4] = true := by decide +kernel
theorem subd7_1_463 : subd7_1 [1, 2, 5] = true := by decide +kernel
theorem subd7_1_464 : subd7_1 [1, 2, 6] = true := by decide +kernel
theorem subd7_1_465 : subd7_1 [1, 2, 7] = true := by decide +kernel
theorem subd7_1_466 : subd7_1 [1, 3] = true := by decide +kernel
theorem subd7_1_467 : subd7_1 [1, 4] = true := by decide +kernel
theorem subd7_1_468 : subd7_1 [1, 5] = true := by decide +kernel
theorem subd7_1_469 : subd7_1 [1, 6] = true := by decide +kernel
theorem subd7_1_470 : subd7_1 [2, -7] = true := by decide +kernel
theorem subd7_1_471 : subd7_1 [2, -6] = true := by decide +kernel
theorem subd7_1_472 : subd7_1 [2, -5] = true := by decide +kernel
theorem subd7_1_473 : subd7_1 [2, -4] = true := by decide +kernel
theorem subd7_1_474 : subd7_1 [2, -3] = true := by decide +kernel
theorem subd7_1_475 : subd7_1 [2, -2, -9] = true := by decide +kernel
theorem subd7_1_476 : subd7_1 [2, -2, -8] = true := by decide +kernel
theorem subd7_1_477 : subd7_1 [2, -2, -7] = true := by decide +kernel
theorem subd7_1_478 : subd7_1 [2, -2, -6] = true := by decide +kernel
theorem subd7_1_479 : subd7_1 [2, -2, -5] = true := by decide +kernel
theorem sbd7_1_14 : ∀ q ∈ blkd7_1_14, subd7_1 q = true := by
  unfold blkd7_1_14
  exact List.forall_mem_cons.2 ⟨subd7_1_448, List.forall_mem_cons.2 ⟨subd7_1_449, List.forall_mem_cons.2 ⟨subd7_1_450, List.forall_mem_cons.2 ⟨subd7_1_451, List.forall_mem_cons.2 ⟨subd7_1_452, List.forall_mem_cons.2 ⟨subd7_1_453, List.forall_mem_cons.2 ⟨subd7_1_454, List.forall_mem_cons.2 ⟨subd7_1_455, List.forall_mem_cons.2 ⟨subd7_1_456, List.forall_mem_cons.2 ⟨subd7_1_457, List.forall_mem_cons.2 ⟨subd7_1_458, List.forall_mem_cons.2 ⟨subd7_1_459, List.forall_mem_cons.2 ⟨subd7_1_460, List.forall_mem_cons.2 ⟨subd7_1_461, List.forall_mem_cons.2 ⟨subd7_1_462, List.forall_mem_cons.2 ⟨subd7_1_463, List.forall_mem_cons.2 ⟨subd7_1_464, List.forall_mem_cons.2 ⟨subd7_1_465, List.forall_mem_cons.2 ⟨subd7_1_466, List.forall_mem_cons.2 ⟨subd7_1_467, List.forall_mem_cons.2 ⟨subd7_1_468, List.forall_mem_cons.2 ⟨subd7_1_469, List.forall_mem_cons.2 ⟨subd7_1_470, List.forall_mem_cons.2 ⟨subd7_1_471, List.forall_mem_cons.2 ⟨subd7_1_472, List.forall_mem_cons.2 ⟨subd7_1_473, List.forall_mem_cons.2 ⟨subd7_1_474, List.forall_mem_cons.2 ⟨subd7_1_475, List.forall_mem_cons.2 ⟨subd7_1_476, List.forall_mem_cons.2 ⟨subd7_1_477, List.forall_mem_cons.2 ⟨subd7_1_478, List.forall_mem_cons.2 ⟨subd7_1_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_480 : subd7_1 [2, -2, -4] = true := by decide +kernel
theorem subd7_1_481 : subd7_1 [2, -2, -3] = true := by decide +kernel
theorem subd7_1_482 : subd7_1 [2, -2, -2] = true := by decide +kernel
theorem subd7_1_483 : subd7_1 [2, -2, -1] = true := by decide +kernel
theorem subd7_1_484 : subd7_1 [2, -2, 0] = true := by decide +kernel
theorem subd7_1_485 : subd7_1 [2, -2, 1] = true := by decide +kernel
theorem subd7_1_486 : subd7_1 [2, -2, 2] = true := by decide +kernel
theorem subd7_1_487 : subd7_1 [2, -2, 3] = true := by decide +kernel
theorem subd7_1_488 : subd7_1 [2, -2, 4] = true := by decide +kernel
theorem subd7_1_489 : subd7_1 [2, -2, 5] = true := by decide +kernel
theorem subd7_1_490 : subd7_1 [2, -1, -8] = true := by decide +kernel
theorem subd7_1_491 : subd7_1 [2, -1, -7] = true := by decide +kernel
theorem subd7_1_492 : subd7_1 [2, -1, -6] = true := by decide +kernel
theorem subd7_1_493 : subd7_1 [2, -1, -5] = true := by decide +kernel
theorem subd7_1_494 : subd7_1 [2, -1, -4] = true := by decide +kernel
theorem subd7_1_495 : subd7_1 [2, -1, -3] = true := by decide +kernel
theorem subd7_1_496 : subd7_1 [2, -1, -2] = true := by decide +kernel
theorem subd7_1_497 : subd7_1 [2, -1, -1] = true := by decide +kernel
theorem subd7_1_498 : subd7_1 [2, -1, 0] = true := by decide +kernel
theorem subd7_1_499 : subd7_1 [2, -1, 1] = true := by decide +kernel
theorem subd7_1_500 : subd7_1 [2, -1, 2] = true := by decide +kernel
theorem subd7_1_501 : subd7_1 [2, -1, 3] = true := by decide +kernel
theorem subd7_1_502 : subd7_1 [2, -1, 4] = true := by decide +kernel
theorem subd7_1_503 : subd7_1 [2, -1, 5] = true := by decide +kernel
theorem subd7_1_504 : subd7_1 [2, -1, 6] = true := by decide +kernel
theorem subd7_1_505 : subd7_1 [2, 0, -8] = true := by decide +kernel
theorem subd7_1_506 : subd7_1 [2, 0, -7] = true := by decide +kernel
theorem subd7_1_507 : subd7_1 [2, 0, -6] = true := by decide +kernel
theorem subd7_1_508 : subd7_1 [2, 0, -5] = true := by decide +kernel
theorem subd7_1_509 : subd7_1 [2, 0, -4] = true := by decide +kernel
theorem subd7_1_510 : subd7_1 [2, 0, -3] = true := by decide +kernel
theorem subd7_1_511 : subd7_1 [2, 0, -2] = true := by decide +kernel
theorem sbd7_1_15 : ∀ q ∈ blkd7_1_15, subd7_1 q = true := by
  unfold blkd7_1_15
  exact List.forall_mem_cons.2 ⟨subd7_1_480, List.forall_mem_cons.2 ⟨subd7_1_481, List.forall_mem_cons.2 ⟨subd7_1_482, List.forall_mem_cons.2 ⟨subd7_1_483, List.forall_mem_cons.2 ⟨subd7_1_484, List.forall_mem_cons.2 ⟨subd7_1_485, List.forall_mem_cons.2 ⟨subd7_1_486, List.forall_mem_cons.2 ⟨subd7_1_487, List.forall_mem_cons.2 ⟨subd7_1_488, List.forall_mem_cons.2 ⟨subd7_1_489, List.forall_mem_cons.2 ⟨subd7_1_490, List.forall_mem_cons.2 ⟨subd7_1_491, List.forall_mem_cons.2 ⟨subd7_1_492, List.forall_mem_cons.2 ⟨subd7_1_493, List.forall_mem_cons.2 ⟨subd7_1_494, List.forall_mem_cons.2 ⟨subd7_1_495, List.forall_mem_cons.2 ⟨subd7_1_496, List.forall_mem_cons.2 ⟨subd7_1_497, List.forall_mem_cons.2 ⟨subd7_1_498, List.forall_mem_cons.2 ⟨subd7_1_499, List.forall_mem_cons.2 ⟨subd7_1_500, List.forall_mem_cons.2 ⟨subd7_1_501, List.forall_mem_cons.2 ⟨subd7_1_502, List.forall_mem_cons.2 ⟨subd7_1_503, List.forall_mem_cons.2 ⟨subd7_1_504, List.forall_mem_cons.2 ⟨subd7_1_505, List.forall_mem_cons.2 ⟨subd7_1_506, List.forall_mem_cons.2 ⟨subd7_1_507, List.forall_mem_cons.2 ⟨subd7_1_508, List.forall_mem_cons.2 ⟨subd7_1_509, List.forall_mem_cons.2 ⟨subd7_1_510, List.forall_mem_cons.2 ⟨subd7_1_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_512 : subd7_1 [2, 0, -1] = true := by decide +kernel
theorem subd7_1_513 : subd7_1 [2, 0, 0] = true := by decide +kernel
theorem subd7_1_514 : subd7_1 [2, 0, 1] = true := by decide +kernel
theorem subd7_1_515 : subd7_1 [2, 0, 2] = true := by decide +kernel
theorem subd7_1_516 : subd7_1 [2, 0, 3] = true := by decide +kernel
theorem subd7_1_517 : subd7_1 [2, 0, 4] = true := by decide +kernel
theorem subd7_1_518 : subd7_1 [2, 0, 5] = true := by decide +kernel
theorem subd7_1_519 : subd7_1 [2, 0, 6] = true := by decide +kernel
theorem subd7_1_520 : subd7_1 [2, 1, -7] = true := by decide +kernel
theorem subd7_1_521 : subd7_1 [2, 1, -6] = true := by decide +kernel
theorem subd7_1_522 : subd7_1 [2, 1, -5] = true := by decide +kernel
theorem subd7_1_523 : subd7_1 [2, 1, -4] = true := by decide +kernel
theorem subd7_1_524 : subd7_1 [2, 1, -3] = true := by decide +kernel
theorem subd7_1_525 : subd7_1 [2, 1, -2] = true := by decide +kernel
theorem subd7_1_526 : subd7_1 [2, 1, -1] = true := by decide +kernel
theorem subd7_1_527 : subd7_1 [2, 1, 0] = true := by decide +kernel
theorem subd7_1_528 : subd7_1 [2, 1, 1] = true := by decide +kernel
theorem subd7_1_529 : subd7_1 [2, 1, 2] = true := by decide +kernel
theorem subd7_1_530 : subd7_1 [2, 1, 3] = true := by decide +kernel
theorem subd7_1_531 : subd7_1 [2, 1, 4] = true := by decide +kernel
theorem subd7_1_532 : subd7_1 [2, 1, 5] = true := by decide +kernel
theorem subd7_1_533 : subd7_1 [2, 1, 6] = true := by decide +kernel
theorem subd7_1_534 : subd7_1 [2, 1, 7] = true := by decide +kernel
theorem subd7_1_535 : subd7_1 [2, 2, -7] = true := by decide +kernel
theorem subd7_1_536 : subd7_1 [2, 2, -6] = true := by decide +kernel
theorem subd7_1_537 : subd7_1 [2, 2, -5] = true := by decide +kernel
theorem subd7_1_538 : subd7_1 [2, 2, -4] = true := by decide +kernel
theorem subd7_1_539 : subd7_1 [2, 2, -3] = true := by decide +kernel
theorem subd7_1_540 : subd7_1 [2, 2, -2] = true := by decide +kernel
theorem subd7_1_541 : subd7_1 [2, 2, -1] = true := by decide +kernel
theorem subd7_1_542 : subd7_1 [2, 2, 0] = true := by decide +kernel
theorem subd7_1_543 : subd7_1 [2, 2, 1] = true := by decide +kernel
theorem sbd7_1_16 : ∀ q ∈ blkd7_1_16, subd7_1 q = true := by
  unfold blkd7_1_16
  exact List.forall_mem_cons.2 ⟨subd7_1_512, List.forall_mem_cons.2 ⟨subd7_1_513, List.forall_mem_cons.2 ⟨subd7_1_514, List.forall_mem_cons.2 ⟨subd7_1_515, List.forall_mem_cons.2 ⟨subd7_1_516, List.forall_mem_cons.2 ⟨subd7_1_517, List.forall_mem_cons.2 ⟨subd7_1_518, List.forall_mem_cons.2 ⟨subd7_1_519, List.forall_mem_cons.2 ⟨subd7_1_520, List.forall_mem_cons.2 ⟨subd7_1_521, List.forall_mem_cons.2 ⟨subd7_1_522, List.forall_mem_cons.2 ⟨subd7_1_523, List.forall_mem_cons.2 ⟨subd7_1_524, List.forall_mem_cons.2 ⟨subd7_1_525, List.forall_mem_cons.2 ⟨subd7_1_526, List.forall_mem_cons.2 ⟨subd7_1_527, List.forall_mem_cons.2 ⟨subd7_1_528, List.forall_mem_cons.2 ⟨subd7_1_529, List.forall_mem_cons.2 ⟨subd7_1_530, List.forall_mem_cons.2 ⟨subd7_1_531, List.forall_mem_cons.2 ⟨subd7_1_532, List.forall_mem_cons.2 ⟨subd7_1_533, List.forall_mem_cons.2 ⟨subd7_1_534, List.forall_mem_cons.2 ⟨subd7_1_535, List.forall_mem_cons.2 ⟨subd7_1_536, List.forall_mem_cons.2 ⟨subd7_1_537, List.forall_mem_cons.2 ⟨subd7_1_538, List.forall_mem_cons.2 ⟨subd7_1_539, List.forall_mem_cons.2 ⟨subd7_1_540, List.forall_mem_cons.2 ⟨subd7_1_541, List.forall_mem_cons.2 ⟨subd7_1_542, List.forall_mem_cons.2 ⟨subd7_1_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_544 : subd7_1 [2, 2, 2] = true := by decide +kernel
theorem subd7_1_545 : subd7_1 [2, 2, 3] = true := by decide +kernel
theorem subd7_1_546 : subd7_1 [2, 2, 4] = true := by decide +kernel
theorem subd7_1_547 : subd7_1 [2, 2, 5] = true := by decide +kernel
theorem subd7_1_548 : subd7_1 [2, 2, 6] = true := by decide +kernel
theorem subd7_1_549 : subd7_1 [2, 2, 7] = true := by decide +kernel
theorem subd7_1_550 : subd7_1 [2, 3] = true := by decide +kernel
theorem subd7_1_551 : subd7_1 [2, 4] = true := by decide +kernel
theorem subd7_1_552 : subd7_1 [2, 5] = true := by decide +kernel
theorem subd7_1_553 : subd7_1 [2, 6] = true := by decide +kernel
theorem subd7_1_554 : subd7_1 [3, -7] = true := by decide +kernel
theorem subd7_1_555 : subd7_1 [3, -6] = true := by decide +kernel
theorem subd7_1_556 : subd7_1 [3, -5] = true := by decide +kernel
theorem subd7_1_557 : subd7_1 [3, -4] = true := by decide +kernel
theorem subd7_1_558 : subd7_1 [3, -3] = true := by decide +kernel
theorem subd7_1_559 : subd7_1 [3, -2] = true := by decide +kernel
theorem subd7_1_560 : subd7_1 [3, -1, -8] = true := by decide +kernel
theorem subd7_1_561 : subd7_1 [3, -1, -7] = true := by decide +kernel
theorem subd7_1_562 : subd7_1 [3, -1, -6] = true := by decide +kernel
theorem subd7_1_563 : subd7_1 [3, -1, -5] = true := by decide +kernel
theorem subd7_1_564 : subd7_1 [3, -1, -4] = true := by decide +kernel
theorem subd7_1_565 : subd7_1 [3, -1, -3] = true := by decide +kernel
theorem subd7_1_566 : subd7_1 [3, -1, -2] = true := by decide +kernel
theorem subd7_1_567 : subd7_1 [3, -1, -1] = true := by decide +kernel
theorem subd7_1_568 : subd7_1 [3, -1, 0] = true := by decide +kernel
theorem subd7_1_569 : subd7_1 [3, -1, 1] = true := by decide +kernel
theorem subd7_1_570 : subd7_1 [3, -1, 2] = true := by decide +kernel
theorem subd7_1_571 : subd7_1 [3, -1, 3] = true := by decide +kernel
theorem subd7_1_572 : subd7_1 [3, -1, 4] = true := by decide +kernel
theorem subd7_1_573 : subd7_1 [3, -1, 5] = true := by decide +kernel
theorem subd7_1_574 : subd7_1 [3, 0, -8] = true := by decide +kernel
theorem subd7_1_575 : subd7_1 [3, 0, -7] = true := by decide +kernel
theorem sbd7_1_17 : ∀ q ∈ blkd7_1_17, subd7_1 q = true := by
  unfold blkd7_1_17
  exact List.forall_mem_cons.2 ⟨subd7_1_544, List.forall_mem_cons.2 ⟨subd7_1_545, List.forall_mem_cons.2 ⟨subd7_1_546, List.forall_mem_cons.2 ⟨subd7_1_547, List.forall_mem_cons.2 ⟨subd7_1_548, List.forall_mem_cons.2 ⟨subd7_1_549, List.forall_mem_cons.2 ⟨subd7_1_550, List.forall_mem_cons.2 ⟨subd7_1_551, List.forall_mem_cons.2 ⟨subd7_1_552, List.forall_mem_cons.2 ⟨subd7_1_553, List.forall_mem_cons.2 ⟨subd7_1_554, List.forall_mem_cons.2 ⟨subd7_1_555, List.forall_mem_cons.2 ⟨subd7_1_556, List.forall_mem_cons.2 ⟨subd7_1_557, List.forall_mem_cons.2 ⟨subd7_1_558, List.forall_mem_cons.2 ⟨subd7_1_559, List.forall_mem_cons.2 ⟨subd7_1_560, List.forall_mem_cons.2 ⟨subd7_1_561, List.forall_mem_cons.2 ⟨subd7_1_562, List.forall_mem_cons.2 ⟨subd7_1_563, List.forall_mem_cons.2 ⟨subd7_1_564, List.forall_mem_cons.2 ⟨subd7_1_565, List.forall_mem_cons.2 ⟨subd7_1_566, List.forall_mem_cons.2 ⟨subd7_1_567, List.forall_mem_cons.2 ⟨subd7_1_568, List.forall_mem_cons.2 ⟨subd7_1_569, List.forall_mem_cons.2 ⟨subd7_1_570, List.forall_mem_cons.2 ⟨subd7_1_571, List.forall_mem_cons.2 ⟨subd7_1_572, List.forall_mem_cons.2 ⟨subd7_1_573, List.forall_mem_cons.2 ⟨subd7_1_574, List.forall_mem_cons.2 ⟨subd7_1_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_576 : subd7_1 [3, 0, -6] = true := by decide +kernel
theorem subd7_1_577 : subd7_1 [3, 0, -5] = true := by decide +kernel
theorem subd7_1_578 : subd7_1 [3, 0, -4] = true := by decide +kernel
theorem subd7_1_579 : subd7_1 [3, 0, -3] = true := by decide +kernel
theorem subd7_1_580 : subd7_1 [3, 0, -2] = true := by decide +kernel
theorem subd7_1_581 : subd7_1 [3, 0, -1] = true := by decide +kernel
theorem subd7_1_582 : subd7_1 [3, 0, 0] = true := by decide +kernel
theorem subd7_1_583 : subd7_1 [3, 0, 1] = true := by decide +kernel
theorem subd7_1_584 : subd7_1 [3, 0, 2] = true := by decide +kernel
theorem subd7_1_585 : subd7_1 [3, 0, 3] = true := by decide +kernel
theorem subd7_1_586 : subd7_1 [3, 0, 4] = true := by decide +kernel
theorem subd7_1_587 : subd7_1 [3, 0, 5] = true := by decide +kernel
theorem subd7_1_588 : subd7_1 [3, 0, 6] = true := by decide +kernel
theorem subd7_1_589 : subd7_1 [3, 1] = true := by decide +kernel
theorem subd7_1_590 : subd7_1 [3, 2] = true := by decide +kernel
theorem subd7_1_591 : subd7_1 [3, 3] = true := by decide +kernel
theorem subd7_1_592 : subd7_1 [3, 4] = true := by decide +kernel
theorem subd7_1_593 : subd7_1 [3, 5] = true := by decide +kernel
theorem subd7_1_594 : subd7_1 [4, -7] = true := by decide +kernel
theorem subd7_1_595 : subd7_1 [4, -6] = true := by decide +kernel
theorem subd7_1_596 : subd7_1 [4, -5] = true := by decide +kernel
theorem subd7_1_597 : subd7_1 [4, -4] = true := by decide +kernel
theorem subd7_1_598 : subd7_1 [4, -3] = true := by decide +kernel
theorem subd7_1_599 : subd7_1 [4, -2] = true := by decide +kernel
theorem subd7_1_600 : subd7_1 [4, -1] = true := by decide +kernel
theorem subd7_1_601 : subd7_1 [4, 0] = true := by decide +kernel
theorem subd7_1_602 : subd7_1 [4, 1] = true := by decide +kernel
theorem subd7_1_603 : subd7_1 [4, 2] = true := by decide +kernel
theorem subd7_1_604 : subd7_1 [4, 3] = true := by decide +kernel
theorem subd7_1_605 : subd7_1 [4, 4] = true := by decide +kernel
theorem subd7_1_606 : subd7_1 [5, -6] = true := by decide +kernel
theorem subd7_1_607 : subd7_1 [5, -5] = true := by decide +kernel
theorem sbd7_1_18 : ∀ q ∈ blkd7_1_18, subd7_1 q = true := by
  unfold blkd7_1_18
  exact List.forall_mem_cons.2 ⟨subd7_1_576, List.forall_mem_cons.2 ⟨subd7_1_577, List.forall_mem_cons.2 ⟨subd7_1_578, List.forall_mem_cons.2 ⟨subd7_1_579, List.forall_mem_cons.2 ⟨subd7_1_580, List.forall_mem_cons.2 ⟨subd7_1_581, List.forall_mem_cons.2 ⟨subd7_1_582, List.forall_mem_cons.2 ⟨subd7_1_583, List.forall_mem_cons.2 ⟨subd7_1_584, List.forall_mem_cons.2 ⟨subd7_1_585, List.forall_mem_cons.2 ⟨subd7_1_586, List.forall_mem_cons.2 ⟨subd7_1_587, List.forall_mem_cons.2 ⟨subd7_1_588, List.forall_mem_cons.2 ⟨subd7_1_589, List.forall_mem_cons.2 ⟨subd7_1_590, List.forall_mem_cons.2 ⟨subd7_1_591, List.forall_mem_cons.2 ⟨subd7_1_592, List.forall_mem_cons.2 ⟨subd7_1_593, List.forall_mem_cons.2 ⟨subd7_1_594, List.forall_mem_cons.2 ⟨subd7_1_595, List.forall_mem_cons.2 ⟨subd7_1_596, List.forall_mem_cons.2 ⟨subd7_1_597, List.forall_mem_cons.2 ⟨subd7_1_598, List.forall_mem_cons.2 ⟨subd7_1_599, List.forall_mem_cons.2 ⟨subd7_1_600, List.forall_mem_cons.2 ⟨subd7_1_601, List.forall_mem_cons.2 ⟨subd7_1_602, List.forall_mem_cons.2 ⟨subd7_1_603, List.forall_mem_cons.2 ⟨subd7_1_604, List.forall_mem_cons.2 ⟨subd7_1_605, List.forall_mem_cons.2 ⟨subd7_1_606, List.forall_mem_cons.2 ⟨subd7_1_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_608 : subd7_1 [5, -4] = true := by decide +kernel
theorem subd7_1_609 : subd7_1 [5, -3] = true := by decide +kernel
theorem subd7_1_610 : subd7_1 [5, -2] = true := by decide +kernel
theorem subd7_1_611 : subd7_1 [5, -1] = true := by decide +kernel
theorem subd7_1_612 : subd7_1 [5, 0] = true := by decide +kernel
theorem subd7_1_613 : subd7_1 [5, 1] = true := by decide +kernel
theorem subd7_1_614 : subd7_1 [5, 2] = true := by decide +kernel
theorem subd7_1_615 : subd7_1 [5, 3] = true := by decide +kernel
theorem subd7_1_616 : subd7_1 [6, -5] = true := by decide +kernel
theorem subd7_1_617 : subd7_1 [6, -4] = true := by decide +kernel
theorem subd7_1_618 : subd7_1 [6, -3] = true := by decide +kernel
theorem subd7_1_619 : subd7_1 [6, -2] = true := by decide +kernel
theorem subd7_1_620 : subd7_1 [6, -1] = true := by decide +kernel
theorem subd7_1_621 : subd7_1 [6, 0] = true := by decide +kernel
theorem subd7_1_622 : subd7_1 [6, 1] = true := by decide +kernel
theorem sbd7_1_19 : ∀ q ∈ blkd7_1_19, subd7_1 q = true := by
  unfold blkd7_1_19
  exact List.forall_mem_cons.2 ⟨subd7_1_608, List.forall_mem_cons.2 ⟨subd7_1_609, List.forall_mem_cons.2 ⟨subd7_1_610, List.forall_mem_cons.2 ⟨subd7_1_611, List.forall_mem_cons.2 ⟨subd7_1_612, List.forall_mem_cons.2 ⟨subd7_1_613, List.forall_mem_cons.2 ⟨subd7_1_614, List.forall_mem_cons.2 ⟨subd7_1_615, List.forall_mem_cons.2 ⟨subd7_1_616, List.forall_mem_cons.2 ⟨subd7_1_617, List.forall_mem_cons.2 ⟨subd7_1_618, List.forall_mem_cons.2 ⟨subd7_1_619, List.forall_mem_cons.2 ⟨subd7_1_620, List.forall_mem_cons.2 ⟨subd7_1_621, List.forall_mem_cons.2 ⟨subd7_1_622, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
