import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_2_288 : subd7_2 [1, 0, -5] = true := by decide +kernel
theorem subd7_2_289 : subd7_2 [1, 0, -4] = true := by decide +kernel
theorem subd7_2_290 : subd7_2 [1, 0, -3] = true := by decide +kernel
theorem subd7_2_291 : subd7_2 [1, 0, -2] = true := by decide +kernel
theorem subd7_2_292 : subd7_2 [1, 0, -1] = true := by decide +kernel
theorem subd7_2_293 : subd7_2 [1, 0, 0] = true := by decide +kernel
theorem subd7_2_294 : subd7_2 [1, 0, 1] = true := by decide +kernel
theorem subd7_2_295 : subd7_2 [1, 0, 2] = true := by decide +kernel
theorem subd7_2_296 : subd7_2 [1, 0, 3] = true := by decide +kernel
theorem subd7_2_297 : subd7_2 [1, 0, 4] = true := by decide +kernel
theorem subd7_2_298 : subd7_2 [1, 0, 5] = true := by decide +kernel
theorem subd7_2_299 : subd7_2 [1, 0, 6] = true := by decide +kernel
theorem subd7_2_300 : subd7_2 [1, 0, 7] = true := by decide +kernel
theorem subd7_2_301 : subd7_2 [1, 1, -7] = true := by decide +kernel
theorem subd7_2_302 : subd7_2 [1, 1, -6] = true := by decide +kernel
theorem subd7_2_303 : subd7_2 [1, 1, -5] = true := by decide +kernel
theorem subd7_2_304 : subd7_2 [1, 1, -4] = true := by decide +kernel
theorem subd7_2_305 : subd7_2 [1, 1, -3] = true := by decide +kernel
theorem subd7_2_306 : subd7_2 [1, 1, -2] = true := by decide +kernel
theorem subd7_2_307 : subd7_2 [1, 1, -1] = true := by decide +kernel
theorem subd7_2_308 : subd7_2 [1, 1, 0] = true := by decide +kernel
theorem subd7_2_309 : subd7_2 [1, 1, 1] = true := by decide +kernel
theorem subd7_2_310 : subd7_2 [1, 1, 2] = true := by decide +kernel
theorem subd7_2_311 : subd7_2 [1, 1, 3] = true := by decide +kernel
theorem subd7_2_312 : subd7_2 [1, 1, 4] = true := by decide +kernel
theorem subd7_2_313 : subd7_2 [1, 1, 5] = true := by decide +kernel
theorem subd7_2_314 : subd7_2 [1, 1, 6] = true := by decide +kernel
theorem subd7_2_315 : subd7_2 [1, 1, 7] = true := by decide +kernel
theorem subd7_2_316 : subd7_2 [1, 2, -6] = true := by decide +kernel
theorem subd7_2_317 : subd7_2 [1, 2, -5] = true := by decide +kernel
theorem subd7_2_318 : subd7_2 [1, 2, -4] = true := by decide +kernel
theorem subd7_2_319 : subd7_2 [1, 2, -3] = true := by decide +kernel
theorem sbd7_2_9 : ∀ q ∈ blkd7_2_9, subd7_2 q = true := by
  unfold blkd7_2_9
  exact List.forall_mem_cons.2 ⟨subd7_2_288, List.forall_mem_cons.2 ⟨subd7_2_289, List.forall_mem_cons.2 ⟨subd7_2_290, List.forall_mem_cons.2 ⟨subd7_2_291, List.forall_mem_cons.2 ⟨subd7_2_292, List.forall_mem_cons.2 ⟨subd7_2_293, List.forall_mem_cons.2 ⟨subd7_2_294, List.forall_mem_cons.2 ⟨subd7_2_295, List.forall_mem_cons.2 ⟨subd7_2_296, List.forall_mem_cons.2 ⟨subd7_2_297, List.forall_mem_cons.2 ⟨subd7_2_298, List.forall_mem_cons.2 ⟨subd7_2_299, List.forall_mem_cons.2 ⟨subd7_2_300, List.forall_mem_cons.2 ⟨subd7_2_301, List.forall_mem_cons.2 ⟨subd7_2_302, List.forall_mem_cons.2 ⟨subd7_2_303, List.forall_mem_cons.2 ⟨subd7_2_304, List.forall_mem_cons.2 ⟨subd7_2_305, List.forall_mem_cons.2 ⟨subd7_2_306, List.forall_mem_cons.2 ⟨subd7_2_307, List.forall_mem_cons.2 ⟨subd7_2_308, List.forall_mem_cons.2 ⟨subd7_2_309, List.forall_mem_cons.2 ⟨subd7_2_310, List.forall_mem_cons.2 ⟨subd7_2_311, List.forall_mem_cons.2 ⟨subd7_2_312, List.forall_mem_cons.2 ⟨subd7_2_313, List.forall_mem_cons.2 ⟨subd7_2_314, List.forall_mem_cons.2 ⟨subd7_2_315, List.forall_mem_cons.2 ⟨subd7_2_316, List.forall_mem_cons.2 ⟨subd7_2_317, List.forall_mem_cons.2 ⟨subd7_2_318, List.forall_mem_cons.2 ⟨subd7_2_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_320 : subd7_2 [1, 2, -2] = true := by decide +kernel
theorem subd7_2_321 : subd7_2 [1, 2, -1] = true := by decide +kernel
theorem subd7_2_322 : subd7_2 [1, 2, 0] = true := by decide +kernel
theorem subd7_2_323 : subd7_2 [1, 2, 1] = true := by decide +kernel
theorem subd7_2_324 : subd7_2 [1, 2, 2] = true := by decide +kernel
theorem subd7_2_325 : subd7_2 [1, 2, 3] = true := by decide +kernel
theorem subd7_2_326 : subd7_2 [1, 2, 4] = true := by decide +kernel
theorem subd7_2_327 : subd7_2 [1, 2, 5] = true := by decide +kernel
theorem subd7_2_328 : subd7_2 [1, 2, 6] = true := by decide +kernel
theorem subd7_2_329 : subd7_2 [1, 2, 7] = true := by decide +kernel
theorem subd7_2_330 : subd7_2 [1, 3] = true := by decide +kernel
theorem subd7_2_331 : subd7_2 [1, 4] = true := by decide +kernel
theorem subd7_2_332 : subd7_2 [1, 5] = true := by decide +kernel
theorem subd7_2_333 : subd7_2 [2, -6] = true := by decide +kernel
theorem subd7_2_334 : subd7_2 [2, -5] = true := by decide +kernel
theorem subd7_2_335 : subd7_2 [2, -4] = true := by decide +kernel
theorem subd7_2_336 : subd7_2 [2, -3] = true := by decide +kernel
theorem subd7_2_337 : subd7_2 [2, -2, -7] = true := by decide +kernel
theorem subd7_2_338 : subd7_2 [2, -2, -6] = true := by decide +kernel
theorem subd7_2_339 : subd7_2 [2, -2, -5] = true := by decide +kernel
theorem subd7_2_340 : subd7_2 [2, -2, -4] = true := by decide +kernel
theorem subd7_2_341 : subd7_2 [2, -2, -3] = true := by decide +kernel
theorem subd7_2_342 : subd7_2 [2, -2, -2] = true := by decide +kernel
theorem subd7_2_343 : subd7_2 [2, -2, -1] = true := by decide +kernel
theorem subd7_2_344 : subd7_2 [2, -2, 0] = true := by decide +kernel
theorem subd7_2_345 : subd7_2 [2, -2, 1] = true := by decide +kernel
theorem subd7_2_346 : subd7_2 [2, -2, 2] = true := by decide +kernel
theorem subd7_2_347 : subd7_2 [2, -2, 3] = true := by decide +kernel
theorem subd7_2_348 : subd7_2 [2, -2, 4] = true := by decide +kernel
theorem subd7_2_349 : subd7_2 [2, -2, 5] = true := by decide +kernel
theorem subd7_2_350 : subd7_2 [2, -2, 6] = true := by decide +kernel
theorem subd7_2_351 : subd7_2 [2, -1, -7] = true := by decide +kernel
theorem sbd7_2_10 : ∀ q ∈ blkd7_2_10, subd7_2 q = true := by
  unfold blkd7_2_10
  exact List.forall_mem_cons.2 ⟨subd7_2_320, List.forall_mem_cons.2 ⟨subd7_2_321, List.forall_mem_cons.2 ⟨subd7_2_322, List.forall_mem_cons.2 ⟨subd7_2_323, List.forall_mem_cons.2 ⟨subd7_2_324, List.forall_mem_cons.2 ⟨subd7_2_325, List.forall_mem_cons.2 ⟨subd7_2_326, List.forall_mem_cons.2 ⟨subd7_2_327, List.forall_mem_cons.2 ⟨subd7_2_328, List.forall_mem_cons.2 ⟨subd7_2_329, List.forall_mem_cons.2 ⟨subd7_2_330, List.forall_mem_cons.2 ⟨subd7_2_331, List.forall_mem_cons.2 ⟨subd7_2_332, List.forall_mem_cons.2 ⟨subd7_2_333, List.forall_mem_cons.2 ⟨subd7_2_334, List.forall_mem_cons.2 ⟨subd7_2_335, List.forall_mem_cons.2 ⟨subd7_2_336, List.forall_mem_cons.2 ⟨subd7_2_337, List.forall_mem_cons.2 ⟨subd7_2_338, List.forall_mem_cons.2 ⟨subd7_2_339, List.forall_mem_cons.2 ⟨subd7_2_340, List.forall_mem_cons.2 ⟨subd7_2_341, List.forall_mem_cons.2 ⟨subd7_2_342, List.forall_mem_cons.2 ⟨subd7_2_343, List.forall_mem_cons.2 ⟨subd7_2_344, List.forall_mem_cons.2 ⟨subd7_2_345, List.forall_mem_cons.2 ⟨subd7_2_346, List.forall_mem_cons.2 ⟨subd7_2_347, List.forall_mem_cons.2 ⟨subd7_2_348, List.forall_mem_cons.2 ⟨subd7_2_349, List.forall_mem_cons.2 ⟨subd7_2_350, List.forall_mem_cons.2 ⟨subd7_2_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_352 : subd7_2 [2, -1, -6] = true := by decide +kernel
theorem subd7_2_353 : subd7_2 [2, -1, -5] = true := by decide +kernel
theorem subd7_2_354 : subd7_2 [2, -1, -4] = true := by decide +kernel
theorem subd7_2_355 : subd7_2 [2, -1, -3] = true := by decide +kernel
theorem subd7_2_356 : subd7_2 [2, -1, -2] = true := by decide +kernel
theorem subd7_2_357 : subd7_2 [2, -1, -1] = true := by decide +kernel
theorem subd7_2_358 : subd7_2 [2, -1, 0] = true := by decide +kernel
theorem subd7_2_359 : subd7_2 [2, -1, 1] = true := by decide +kernel
theorem subd7_2_360 : subd7_2 [2, -1, 2] = true := by decide +kernel
theorem subd7_2_361 : subd7_2 [2, -1, 3] = true := by decide +kernel
theorem subd7_2_362 : subd7_2 [2, -1, 4] = true := by decide +kernel
theorem subd7_2_363 : subd7_2 [2, -1, 5] = true := by decide +kernel
theorem subd7_2_364 : subd7_2 [2, -1, 6] = true := by decide +kernel
theorem subd7_2_365 : subd7_2 [2, 0, -7] = true := by decide +kernel
theorem subd7_2_366 : subd7_2 [2, 0, -6] = true := by decide +kernel
theorem subd7_2_367 : subd7_2 [2, 0, -5] = true := by decide +kernel
theorem subd7_2_368 : subd7_2 [2, 0, -4] = true := by decide +kernel
theorem subd7_2_369 : subd7_2 [2, 0, -3] = true := by decide +kernel
theorem subd7_2_370 : subd7_2 [2, 0, -2] = true := by decide +kernel
theorem subd7_2_371 : subd7_2 [2, 0, -1] = true := by decide +kernel
theorem subd7_2_372 : subd7_2 [2, 0, 0] = true := by decide +kernel
theorem subd7_2_373 : subd7_2 [2, 0, 1] = true := by decide +kernel
theorem subd7_2_374 : subd7_2 [2, 0, 2] = true := by decide +kernel
theorem subd7_2_375 : subd7_2 [2, 0, 3] = true := by decide +kernel
theorem subd7_2_376 : subd7_2 [2, 0, 4] = true := by decide +kernel
theorem subd7_2_377 : subd7_2 [2, 0, 5] = true := by decide +kernel
theorem subd7_2_378 : subd7_2 [2, 0, 6] = true := by decide +kernel
theorem subd7_2_379 : subd7_2 [2, 0, 7] = true := by decide +kernel
theorem subd7_2_380 : subd7_2 [2, 1, -6] = true := by decide +kernel
theorem subd7_2_381 : subd7_2 [2, 1, -5] = true := by decide +kernel
theorem subd7_2_382 : subd7_2 [2, 1, -4] = true := by decide +kernel
theorem subd7_2_383 : subd7_2 [2, 1, -3] = true := by decide +kernel
theorem sbd7_2_11 : ∀ q ∈ blkd7_2_11, subd7_2 q = true := by
  unfold blkd7_2_11
  exact List.forall_mem_cons.2 ⟨subd7_2_352, List.forall_mem_cons.2 ⟨subd7_2_353, List.forall_mem_cons.2 ⟨subd7_2_354, List.forall_mem_cons.2 ⟨subd7_2_355, List.forall_mem_cons.2 ⟨subd7_2_356, List.forall_mem_cons.2 ⟨subd7_2_357, List.forall_mem_cons.2 ⟨subd7_2_358, List.forall_mem_cons.2 ⟨subd7_2_359, List.forall_mem_cons.2 ⟨subd7_2_360, List.forall_mem_cons.2 ⟨subd7_2_361, List.forall_mem_cons.2 ⟨subd7_2_362, List.forall_mem_cons.2 ⟨subd7_2_363, List.forall_mem_cons.2 ⟨subd7_2_364, List.forall_mem_cons.2 ⟨subd7_2_365, List.forall_mem_cons.2 ⟨subd7_2_366, List.forall_mem_cons.2 ⟨subd7_2_367, List.forall_mem_cons.2 ⟨subd7_2_368, List.forall_mem_cons.2 ⟨subd7_2_369, List.forall_mem_cons.2 ⟨subd7_2_370, List.forall_mem_cons.2 ⟨subd7_2_371, List.forall_mem_cons.2 ⟨subd7_2_372, List.forall_mem_cons.2 ⟨subd7_2_373, List.forall_mem_cons.2 ⟨subd7_2_374, List.forall_mem_cons.2 ⟨subd7_2_375, List.forall_mem_cons.2 ⟨subd7_2_376, List.forall_mem_cons.2 ⟨subd7_2_377, List.forall_mem_cons.2 ⟨subd7_2_378, List.forall_mem_cons.2 ⟨subd7_2_379, List.forall_mem_cons.2 ⟨subd7_2_380, List.forall_mem_cons.2 ⟨subd7_2_381, List.forall_mem_cons.2 ⟨subd7_2_382, List.forall_mem_cons.2 ⟨subd7_2_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_384 : subd7_2 [2, 1, -2] = true := by decide +kernel
theorem subd7_2_385 : subd7_2 [2, 1, -1] = true := by decide +kernel
theorem subd7_2_386 : subd7_2 [2, 1, 0] = true := by decide +kernel
theorem subd7_2_387 : subd7_2 [2, 1, 1] = true := by decide +kernel
theorem subd7_2_388 : subd7_2 [2, 1, 2] = true := by decide +kernel
theorem subd7_2_389 : subd7_2 [2, 1, 3] = true := by decide +kernel
theorem subd7_2_390 : subd7_2 [2, 1, 4] = true := by decide +kernel
theorem subd7_2_391 : subd7_2 [2, 1, 5] = true := by decide +kernel
theorem subd7_2_392 : subd7_2 [2, 1, 6] = true := by decide +kernel
theorem subd7_2_393 : subd7_2 [2, 1, 7] = true := by decide +kernel
theorem subd7_2_394 : subd7_2 [2, 2] = true := by decide +kernel
theorem subd7_2_395 : subd7_2 [2, 3] = true := by decide +kernel
theorem subd7_2_396 : subd7_2 [2, 4] = true := by decide +kernel
theorem subd7_2_397 : subd7_2 [2, 5] = true := by decide +kernel
theorem subd7_2_398 : subd7_2 [3, -6] = true := by decide +kernel
theorem subd7_2_399 : subd7_2 [3, -5] = true := by decide +kernel
theorem subd7_2_400 : subd7_2 [3, -4] = true := by decide +kernel
theorem subd7_2_401 : subd7_2 [3, -3] = true := by decide +kernel
theorem subd7_2_402 : subd7_2 [3, -2] = true := by decide +kernel
theorem subd7_2_403 : subd7_2 [3, -1] = true := by decide +kernel
theorem subd7_2_404 : subd7_2 [3, 0] = true := by decide +kernel
theorem subd7_2_405 : subd7_2 [3, 1] = true := by decide +kernel
theorem subd7_2_406 : subd7_2 [3, 2] = true := by decide +kernel
theorem subd7_2_407 : subd7_2 [3, 3] = true := by decide +kernel
theorem subd7_2_408 : subd7_2 [3, 4] = true := by decide +kernel
theorem subd7_2_409 : subd7_2 [4, -5] = true := by decide +kernel
theorem subd7_2_410 : subd7_2 [4, -4] = true := by decide +kernel
theorem subd7_2_411 : subd7_2 [4, -3] = true := by decide +kernel
theorem subd7_2_412 : subd7_2 [4, -2] = true := by decide +kernel
theorem subd7_2_413 : subd7_2 [4, -1] = true := by decide +kernel
theorem subd7_2_414 : subd7_2 [4, 0] = true := by decide +kernel
theorem subd7_2_415 : subd7_2 [4, 1] = true := by decide +kernel
theorem sbd7_2_12 : ∀ q ∈ blkd7_2_12, subd7_2 q = true := by
  unfold blkd7_2_12
  exact List.forall_mem_cons.2 ⟨subd7_2_384, List.forall_mem_cons.2 ⟨subd7_2_385, List.forall_mem_cons.2 ⟨subd7_2_386, List.forall_mem_cons.2 ⟨subd7_2_387, List.forall_mem_cons.2 ⟨subd7_2_388, List.forall_mem_cons.2 ⟨subd7_2_389, List.forall_mem_cons.2 ⟨subd7_2_390, List.forall_mem_cons.2 ⟨subd7_2_391, List.forall_mem_cons.2 ⟨subd7_2_392, List.forall_mem_cons.2 ⟨subd7_2_393, List.forall_mem_cons.2 ⟨subd7_2_394, List.forall_mem_cons.2 ⟨subd7_2_395, List.forall_mem_cons.2 ⟨subd7_2_396, List.forall_mem_cons.2 ⟨subd7_2_397, List.forall_mem_cons.2 ⟨subd7_2_398, List.forall_mem_cons.2 ⟨subd7_2_399, List.forall_mem_cons.2 ⟨subd7_2_400, List.forall_mem_cons.2 ⟨subd7_2_401, List.forall_mem_cons.2 ⟨subd7_2_402, List.forall_mem_cons.2 ⟨subd7_2_403, List.forall_mem_cons.2 ⟨subd7_2_404, List.forall_mem_cons.2 ⟨subd7_2_405, List.forall_mem_cons.2 ⟨subd7_2_406, List.forall_mem_cons.2 ⟨subd7_2_407, List.forall_mem_cons.2 ⟨subd7_2_408, List.forall_mem_cons.2 ⟨subd7_2_409, List.forall_mem_cons.2 ⟨subd7_2_410, List.forall_mem_cons.2 ⟨subd7_2_411, List.forall_mem_cons.2 ⟨subd7_2_412, List.forall_mem_cons.2 ⟨subd7_2_413, List.forall_mem_cons.2 ⟨subd7_2_414, List.forall_mem_cons.2 ⟨subd7_2_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_2_416 : subd7_2 [4, 2] = true := by decide +kernel
theorem subd7_2_417 : subd7_2 [4, 3] = true := by decide +kernel
theorem subd7_2_418 : subd7_2 [5, -4] = true := by decide +kernel
theorem subd7_2_419 : subd7_2 [5, -3] = true := by decide +kernel
theorem subd7_2_420 : subd7_2 [5, -2] = true := by decide +kernel
theorem subd7_2_421 : subd7_2 [5, -1] = true := by decide +kernel
theorem subd7_2_422 : subd7_2 [5, 0] = true := by decide +kernel
theorem subd7_2_423 : subd7_2 [5, 1] = true := by decide +kernel
theorem subd7_2_424 : subd7_2 [5, 2] = true := by decide +kernel
theorem sbd7_2_13 : ∀ q ∈ blkd7_2_13, subd7_2 q = true := by
  unfold blkd7_2_13
  exact List.forall_mem_cons.2 ⟨subd7_2_416, List.forall_mem_cons.2 ⟨subd7_2_417, List.forall_mem_cons.2 ⟨subd7_2_418, List.forall_mem_cons.2 ⟨subd7_2_419, List.forall_mem_cons.2 ⟨subd7_2_420, List.forall_mem_cons.2 ⟨subd7_2_421, List.forall_mem_cons.2 ⟨subd7_2_422, List.forall_mem_cons.2 ⟨subd7_2_423, List.forall_mem_cons.2 ⟨subd7_2_424, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_3 : ldCheck G d7_3.U d7_3.ms ldd7_3 = true := by decide +kernel
theorem pre_okd7_3 : subPre G cell7 d7_3 = true := by decide +kernel
theorem subd7_3_0 : subd7_3 [-4] = true := by decide +kernel
theorem subd7_3_1 : subd7_3 [-3, -2] = true := by decide +kernel
theorem subd7_3_2 : subd7_3 [-3, -1] = true := by decide +kernel
theorem subd7_3_3 : subd7_3 [-3, 0] = true := by decide +kernel
theorem subd7_3_4 : subd7_3 [-3, 1] = true := by decide +kernel
theorem subd7_3_5 : subd7_3 [-3, 2] = true := by decide +kernel
theorem subd7_3_6 : subd7_3 [-3, 3] = true := by decide +kernel
theorem subd7_3_7 : subd7_3 [-3, 4] = true := by decide +kernel
theorem subd7_3_8 : subd7_3 [-2, -4] = true := by decide +kernel
theorem subd7_3_9 : subd7_3 [-2, -3] = true := by decide +kernel
theorem subd7_3_10 : subd7_3 [-2, -2] = true := by decide +kernel
theorem subd7_3_11 : subd7_3 [-2, -1, -7] = true := by decide +kernel
theorem subd7_3_12 : subd7_3 [-2, -1, -6] = true := by decide +kernel
theorem subd7_3_13 : subd7_3 [-2, -1, -5] = true := by decide +kernel
theorem subd7_3_14 : subd7_3 [-2, -1, -4] = true := by decide +kernel
theorem subd7_3_15 : subd7_3 [-2, -1, -3] = true := by decide +kernel
theorem subd7_3_16 : subd7_3 [-2, -1, -2] = true := by decide +kernel
theorem subd7_3_17 : subd7_3 [-2, -1, -1] = true := by decide +kernel
theorem subd7_3_18 : subd7_3 [-2, -1, 0] = true := by decide +kernel
theorem subd7_3_19 : subd7_3 [-2, -1, 1] = true := by decide +kernel
theorem subd7_3_20 : subd7_3 [-2, -1, 2] = true := by decide +kernel
theorem subd7_3_21 : subd7_3 [-2, -1, 3] = true := by decide +kernel
theorem subd7_3_22 : subd7_3 [-2, -1, 4] = true := by decide +kernel
theorem subd7_3_23 : subd7_3 [-2, -1, 5] = true := by decide +kernel
theorem subd7_3_24 : subd7_3 [-2, -1, 6] = true := by decide +kernel
theorem subd7_3_25 : subd7_3 [-2, 0, -8] = true := by decide +kernel
theorem subd7_3_26 : subd7_3 [-2, 0, -7] = true := by decide +kernel
theorem subd7_3_27 : subd7_3 [-2, 0, -6] = true := by decide +kernel
theorem subd7_3_28 : subd7_3 [-2, 0, -5] = true := by decide +kernel
theorem subd7_3_29 : subd7_3 [-2, 0, -4] = true := by decide +kernel
theorem subd7_3_30 : subd7_3 [-2, 0, -3] = true := by decide +kernel
theorem subd7_3_31 : subd7_3 [-2, 0, -2] = true := by decide +kernel
theorem sbd7_3_0 : ∀ q ∈ blkd7_3_0, subd7_3 q = true := by
  unfold blkd7_3_0
  exact List.forall_mem_cons.2 ⟨subd7_3_0, List.forall_mem_cons.2 ⟨subd7_3_1, List.forall_mem_cons.2 ⟨subd7_3_2, List.forall_mem_cons.2 ⟨subd7_3_3, List.forall_mem_cons.2 ⟨subd7_3_4, List.forall_mem_cons.2 ⟨subd7_3_5, List.forall_mem_cons.2 ⟨subd7_3_6, List.forall_mem_cons.2 ⟨subd7_3_7, List.forall_mem_cons.2 ⟨subd7_3_8, List.forall_mem_cons.2 ⟨subd7_3_9, List.forall_mem_cons.2 ⟨subd7_3_10, List.forall_mem_cons.2 ⟨subd7_3_11, List.forall_mem_cons.2 ⟨subd7_3_12, List.forall_mem_cons.2 ⟨subd7_3_13, List.forall_mem_cons.2 ⟨subd7_3_14, List.forall_mem_cons.2 ⟨subd7_3_15, List.forall_mem_cons.2 ⟨subd7_3_16, List.forall_mem_cons.2 ⟨subd7_3_17, List.forall_mem_cons.2 ⟨subd7_3_18, List.forall_mem_cons.2 ⟨subd7_3_19, List.forall_mem_cons.2 ⟨subd7_3_20, List.forall_mem_cons.2 ⟨subd7_3_21, List.forall_mem_cons.2 ⟨subd7_3_22, List.forall_mem_cons.2 ⟨subd7_3_23, List.forall_mem_cons.2 ⟨subd7_3_24, List.forall_mem_cons.2 ⟨subd7_3_25, List.forall_mem_cons.2 ⟨subd7_3_26, List.forall_mem_cons.2 ⟨subd7_3_27, List.forall_mem_cons.2 ⟨subd7_3_28, List.forall_mem_cons.2 ⟨subd7_3_29, List.forall_mem_cons.2 ⟨subd7_3_30, List.forall_mem_cons.2 ⟨subd7_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_32 : subd7_3 [-2, 0, -1] = true := by decide +kernel
theorem subd7_3_33 : subd7_3 [-2, 0, 0] = true := by decide +kernel
theorem subd7_3_34 : subd7_3 [-2, 0, 1] = true := by decide +kernel
theorem subd7_3_35 : subd7_3 [-2, 0, 2] = true := by decide +kernel
theorem subd7_3_36 : subd7_3 [-2, 0, 3] = true := by decide +kernel
theorem subd7_3_37 : subd7_3 [-2, 0, 4] = true := by decide +kernel
theorem subd7_3_38 : subd7_3 [-2, 0, 5] = true := by decide +kernel
theorem subd7_3_39 : subd7_3 [-2, 0, 6] = true := by decide +kernel
theorem subd7_3_40 : subd7_3 [-2, 0, 7] = true := by decide +kernel
theorem subd7_3_41 : subd7_3 [-2, 0, 8] = true := by decide +kernel
theorem subd7_3_42 : subd7_3 [-2, 1, -8] = true := by decide +kernel
theorem subd7_3_43 : subd7_3 [-2, 1, -7] = true := by decide +kernel
theorem subd7_3_44 : subd7_3 [-2, 1, -6] = true := by decide +kernel
theorem subd7_3_45 : subd7_3 [-2, 1, -5] = true := by decide +kernel
theorem subd7_3_46 : subd7_3 [-2, 1, -4] = true := by decide +kernel
theorem subd7_3_47 : subd7_3 [-2, 1, -3] = true := by decide +kernel
theorem subd7_3_48 : subd7_3 [-2, 1, -2] = true := by decide +kernel
theorem subd7_3_49 : subd7_3 [-2, 1, -1] = true := by decide +kernel
theorem subd7_3_50 : subd7_3 [-2, 1, 0] = true := by decide +kernel
theorem subd7_3_51 : subd7_3 [-2, 1, 1] = true := by decide +kernel
theorem subd7_3_52 : subd7_3 [-2, 1, 2] = true := by decide +kernel
theorem subd7_3_53 : subd7_3 [-2, 1, 3] = true := by decide +kernel
theorem subd7_3_54 : subd7_3 [-2, 1, 4] = true := by decide +kernel
theorem subd7_3_55 : subd7_3 [-2, 1, 5] = true := by decide +kernel
theorem subd7_3_56 : subd7_3 [-2, 1, 6] = true := by decide +kernel
theorem subd7_3_57 : subd7_3 [-2, 1, 7] = true := by decide +kernel
theorem subd7_3_58 : subd7_3 [-2, 1, 8] = true := by decide +kernel
theorem subd7_3_59 : subd7_3 [-2, 2, -7] = true := by decide +kernel
theorem subd7_3_60 : subd7_3 [-2, 2, -6] = true := by decide +kernel
theorem subd7_3_61 : subd7_3 [-2, 2, -5] = true := by decide +kernel
theorem subd7_3_62 : subd7_3 [-2, 2, -4] = true := by decide +kernel
theorem subd7_3_63 : subd7_3 [-2, 2, -3] = true := by decide +kernel
theorem sbd7_3_1 : ∀ q ∈ blkd7_3_1, subd7_3 q = true := by
  unfold blkd7_3_1
  exact List.forall_mem_cons.2 ⟨subd7_3_32, List.forall_mem_cons.2 ⟨subd7_3_33, List.forall_mem_cons.2 ⟨subd7_3_34, List.forall_mem_cons.2 ⟨subd7_3_35, List.forall_mem_cons.2 ⟨subd7_3_36, List.forall_mem_cons.2 ⟨subd7_3_37, List.forall_mem_cons.2 ⟨subd7_3_38, List.forall_mem_cons.2 ⟨subd7_3_39, List.forall_mem_cons.2 ⟨subd7_3_40, List.forall_mem_cons.2 ⟨subd7_3_41, List.forall_mem_cons.2 ⟨subd7_3_42, List.forall_mem_cons.2 ⟨subd7_3_43, List.forall_mem_cons.2 ⟨subd7_3_44, List.forall_mem_cons.2 ⟨subd7_3_45, List.forall_mem_cons.2 ⟨subd7_3_46, List.forall_mem_cons.2 ⟨subd7_3_47, List.forall_mem_cons.2 ⟨subd7_3_48, List.forall_mem_cons.2 ⟨subd7_3_49, List.forall_mem_cons.2 ⟨subd7_3_50, List.forall_mem_cons.2 ⟨subd7_3_51, List.forall_mem_cons.2 ⟨subd7_3_52, List.forall_mem_cons.2 ⟨subd7_3_53, List.forall_mem_cons.2 ⟨subd7_3_54, List.forall_mem_cons.2 ⟨subd7_3_55, List.forall_mem_cons.2 ⟨subd7_3_56, List.forall_mem_cons.2 ⟨subd7_3_57, List.forall_mem_cons.2 ⟨subd7_3_58, List.forall_mem_cons.2 ⟨subd7_3_59, List.forall_mem_cons.2 ⟨subd7_3_60, List.forall_mem_cons.2 ⟨subd7_3_61, List.forall_mem_cons.2 ⟨subd7_3_62, List.forall_mem_cons.2 ⟨subd7_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_64 : subd7_3 [-2, 2, -2] = true := by decide +kernel
theorem subd7_3_65 : subd7_3 [-2, 2, -1] = true := by decide +kernel
theorem subd7_3_66 : subd7_3 [-2, 2, 0] = true := by decide +kernel
theorem subd7_3_67 : subd7_3 [-2, 2, 1] = true := by decide +kernel
theorem subd7_3_68 : subd7_3 [-2, 2, 2] = true := by decide +kernel
theorem subd7_3_69 : subd7_3 [-2, 2, 3] = true := by decide +kernel
theorem subd7_3_70 : subd7_3 [-2, 2, 4] = true := by decide +kernel
theorem subd7_3_71 : subd7_3 [-2, 2, 5] = true := by decide +kernel
theorem subd7_3_72 : subd7_3 [-2, 2, 6] = true := by decide +kernel
theorem subd7_3_73 : subd7_3 [-2, 2, 7] = true := by decide +kernel
theorem subd7_3_74 : subd7_3 [-2, 2, 8] = true := by decide +kernel
theorem subd7_3_75 : subd7_3 [-2, 3, -6] = true := by decide +kernel
theorem subd7_3_76 : subd7_3 [-2, 3, -5] = true := by decide +kernel
theorem subd7_3_77 : subd7_3 [-2, 3, -4] = true := by decide +kernel
theorem subd7_3_78 : subd7_3 [-2, 3, -3] = true := by decide +kernel
theorem subd7_3_79 : subd7_3 [-2, 3, -2] = true := by decide +kernel
theorem subd7_3_80 : subd7_3 [-2, 3, -1] = true := by decide +kernel
theorem subd7_3_81 : subd7_3 [-2, 3, 0] = true := by decide +kernel
theorem subd7_3_82 : subd7_3 [-2, 3, 1] = true := by decide +kernel
theorem subd7_3_83 : subd7_3 [-2, 3, 2] = true := by decide +kernel
theorem subd7_3_84 : subd7_3 [-2, 3, 3] = true := by decide +kernel
theorem subd7_3_85 : subd7_3 [-2, 3, 4] = true := by decide +kernel
theorem subd7_3_86 : subd7_3 [-2, 3, 5] = true := by decide +kernel
theorem subd7_3_87 : subd7_3 [-2, 3, 6] = true := by decide +kernel
theorem subd7_3_88 : subd7_3 [-2, 3, 7] = true := by decide +kernel
theorem subd7_3_89 : subd7_3 [-2, 3, 8] = true := by decide +kernel
theorem subd7_3_90 : subd7_3 [-2, 4] = true := by decide +kernel
theorem subd7_3_91 : subd7_3 [-1, -4] = true := by decide +kernel
theorem subd7_3_92 : subd7_3 [-1, -3] = true := by decide +kernel
theorem subd7_3_93 : subd7_3 [-1, -2, -8] = true := by decide +kernel
theorem subd7_3_94 : subd7_3 [-1, -2, -7] = true := by decide +kernel
theorem subd7_3_95 : subd7_3 [-1, -2, -6] = true := by decide +kernel
theorem sbd7_3_2 : ∀ q ∈ blkd7_3_2, subd7_3 q = true := by
  unfold blkd7_3_2
  exact List.forall_mem_cons.2 ⟨subd7_3_64, List.forall_mem_cons.2 ⟨subd7_3_65, List.forall_mem_cons.2 ⟨subd7_3_66, List.forall_mem_cons.2 ⟨subd7_3_67, List.forall_mem_cons.2 ⟨subd7_3_68, List.forall_mem_cons.2 ⟨subd7_3_69, List.forall_mem_cons.2 ⟨subd7_3_70, List.forall_mem_cons.2 ⟨subd7_3_71, List.forall_mem_cons.2 ⟨subd7_3_72, List.forall_mem_cons.2 ⟨subd7_3_73, List.forall_mem_cons.2 ⟨subd7_3_74, List.forall_mem_cons.2 ⟨subd7_3_75, List.forall_mem_cons.2 ⟨subd7_3_76, List.forall_mem_cons.2 ⟨subd7_3_77, List.forall_mem_cons.2 ⟨subd7_3_78, List.forall_mem_cons.2 ⟨subd7_3_79, List.forall_mem_cons.2 ⟨subd7_3_80, List.forall_mem_cons.2 ⟨subd7_3_81, List.forall_mem_cons.2 ⟨subd7_3_82, List.forall_mem_cons.2 ⟨subd7_3_83, List.forall_mem_cons.2 ⟨subd7_3_84, List.forall_mem_cons.2 ⟨subd7_3_85, List.forall_mem_cons.2 ⟨subd7_3_86, List.forall_mem_cons.2 ⟨subd7_3_87, List.forall_mem_cons.2 ⟨subd7_3_88, List.forall_mem_cons.2 ⟨subd7_3_89, List.forall_mem_cons.2 ⟨subd7_3_90, List.forall_mem_cons.2 ⟨subd7_3_91, List.forall_mem_cons.2 ⟨subd7_3_92, List.forall_mem_cons.2 ⟨subd7_3_93, List.forall_mem_cons.2 ⟨subd7_3_94, List.forall_mem_cons.2 ⟨subd7_3_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_3_96 : subd7_3 [-1, -2, -5] = true := by decide +kernel
theorem subd7_3_97 : subd7_3 [-1, -2, -4] = true := by decide +kernel
theorem subd7_3_98 : subd7_3 [-1, -2, -3] = true := by decide +kernel
theorem subd7_3_99 : subd7_3 [-1, -2, -2] = true := by decide +kernel
theorem subd7_3_100 : subd7_3 [-1, -2, -1] = true := by decide +kernel
theorem subd7_3_101 : subd7_3 [-1, -2, 0] = true := by decide +kernel
theorem subd7_3_102 : subd7_3 [-1, -2, 1] = true := by decide +kernel
theorem subd7_3_103 : subd7_3 [-1, -2, 2] = true := by decide +kernel
theorem subd7_3_104 : subd7_3 [-1, -2, 3] = true := by decide +kernel
theorem subd7_3_105 : subd7_3 [-1, -2, 4] = true := by decide +kernel
theorem subd7_3_106 : subd7_3 [-1, -2, 5] = true := by decide +kernel
theorem subd7_3_107 : subd7_3 [-1, -2, 6] = true := by decide +kernel
theorem subd7_3_108 : subd7_3 [-1, -1, -9] = true := by decide +kernel
theorem subd7_3_109 : subd7_3 [-1, -1, -8] = true := by decide +kernel
theorem subd7_3_110 : subd7_3 [-1, -1, -7] = true := by decide +kernel
theorem subd7_3_111 : subd7_3 [-1, -1, -6] = true := by decide +kernel
theorem subd7_3_112 : subd7_3 [-1, -1, -5] = true := by decide +kernel
theorem subd7_3_113 : subd7_3 [-1, -1, -4] = true := by decide +kernel
theorem subd7_3_114 : subd7_3 [-1, -1, -3] = true := by decide +kernel
theorem subd7_3_115 : subd7_3 [-1, -1, -2] = true := by decide +kernel
theorem subd7_3_116 : subd7_3 [-1, -1, -1] = true := by decide +kernel
theorem subd7_3_117 : subd7_3 [-1, -1, 0] = true := by decide +kernel
theorem subd7_3_118 : subd7_3 [-1, -1, 1] = true := by decide +kernel
theorem subd7_3_119 : subd7_3 [-1, -1, 2] = true := by decide +kernel
theorem subd7_3_120 : subd7_3 [-1, -1, 3] = true := by decide +kernel
theorem subd7_3_121 : subd7_3 [-1, -1, 4] = true := by decide +kernel
theorem subd7_3_122 : subd7_3 [-1, -1, 5] = true := by decide +kernel
theorem subd7_3_123 : subd7_3 [-1, -1, 6] = true := by decide +kernel
theorem subd7_3_124 : subd7_3 [-1, -1, 7] = true := by decide +kernel
theorem subd7_3_125 : subd7_3 [-1, -1, 8] = true := by decide +kernel
theorem subd7_3_126 : subd7_3 [-1, 0, -9] = true := by decide +kernel
theorem subd7_3_127 : subd7_3 [-1, 0, -8] = true := by decide +kernel
theorem sbd7_3_3 : ∀ q ∈ blkd7_3_3, subd7_3 q = true := by
  unfold blkd7_3_3
  exact List.forall_mem_cons.2 ⟨subd7_3_96, List.forall_mem_cons.2 ⟨subd7_3_97, List.forall_mem_cons.2 ⟨subd7_3_98, List.forall_mem_cons.2 ⟨subd7_3_99, List.forall_mem_cons.2 ⟨subd7_3_100, List.forall_mem_cons.2 ⟨subd7_3_101, List.forall_mem_cons.2 ⟨subd7_3_102, List.forall_mem_cons.2 ⟨subd7_3_103, List.forall_mem_cons.2 ⟨subd7_3_104, List.forall_mem_cons.2 ⟨subd7_3_105, List.forall_mem_cons.2 ⟨subd7_3_106, List.forall_mem_cons.2 ⟨subd7_3_107, List.forall_mem_cons.2 ⟨subd7_3_108, List.forall_mem_cons.2 ⟨subd7_3_109, List.forall_mem_cons.2 ⟨subd7_3_110, List.forall_mem_cons.2 ⟨subd7_3_111, List.forall_mem_cons.2 ⟨subd7_3_112, List.forall_mem_cons.2 ⟨subd7_3_113, List.forall_mem_cons.2 ⟨subd7_3_114, List.forall_mem_cons.2 ⟨subd7_3_115, List.forall_mem_cons.2 ⟨subd7_3_116, List.forall_mem_cons.2 ⟨subd7_3_117, List.forall_mem_cons.2 ⟨subd7_3_118, List.forall_mem_cons.2 ⟨subd7_3_119, List.forall_mem_cons.2 ⟨subd7_3_120, List.forall_mem_cons.2 ⟨subd7_3_121, List.forall_mem_cons.2 ⟨subd7_3_122, List.forall_mem_cons.2 ⟨subd7_3_123, List.forall_mem_cons.2 ⟨subd7_3_124, List.forall_mem_cons.2 ⟨subd7_3_125, List.forall_mem_cons.2 ⟨subd7_3_126, List.forall_mem_cons.2 ⟨subd7_3_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
