import ReflectZphi.Data.Cert5.C098.Base

namespace ReflectZphi.Data.Cert5.C098
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub7_288 : sub7 [-1, -3, -3] = true := by decide +kernel
theorem sub7_289 : sub7 [-1, -3, -2] = true := by decide +kernel
theorem sub7_290 : sub7 [-1, -3, -1] = true := by decide +kernel
theorem sub7_291 : sub7 [-1, -3, 0] = true := by decide +kernel
theorem sub7_292 : sub7 [-1, -3, 1] = true := by decide +kernel
theorem sub7_293 : sub7 [-1, -3, 2] = true := by decide +kernel
theorem sub7_294 : sub7 [-1, -3, 3] = true := by decide +kernel
theorem sub7_295 : sub7 [-1, -3, 4] = true := by decide +kernel
theorem sub7_296 : sub7 [-1, -3, 5] = true := by decide +kernel
theorem sub7_297 : sub7 [-1, -3, 6] = true := by decide +kernel
theorem sub7_298 : sub7 [-1, -2, -9] = true := by decide +kernel
theorem sub7_299 : sub7 [-1, -2, -8] = true := by decide +kernel
theorem sub7_300 : sub7 [-1, -2, -7] = true := by decide +kernel
theorem sub7_301 : sub7 [-1, -2, -6] = true := by decide +kernel
theorem sub7_302 : sub7 [-1, -2, -5] = true := by decide +kernel
theorem sub7_303 : sub7 [-1, -2, -4] = true := by decide +kernel
theorem sub7_304 : sub7 [-1, -2, -3] = true := by decide +kernel
theorem sub7_305 : sub7 [-1, -2, -2] = true := by decide +kernel
theorem sub7_306 : sub7 [-1, -2, -1] = true := by decide +kernel
theorem sub7_307 : sub7 [-1, -2, 0] = true := by decide +kernel
theorem sub7_308 : sub7 [-1, -2, 1] = true := by decide +kernel
theorem sub7_309 : sub7 [-1, -2, 2] = true := by decide +kernel
theorem sub7_310 : sub7 [-1, -2, 3] = true := by decide +kernel
theorem sub7_311 : sub7 [-1, -2, 4] = true := by decide +kernel
theorem sub7_312 : sub7 [-1, -2, 5] = true := by decide +kernel
theorem sub7_313 : sub7 [-1, -2, 6] = true := by decide +kernel
theorem sub7_314 : sub7 [-1, -2, 7] = true := by decide +kernel
theorem sub7_315 : sub7 [-1, -1, -9] = true := by decide +kernel
theorem sub7_316 : sub7 [-1, -1, -8] = true := by decide +kernel
theorem sub7_317 : sub7 [-1, -1, -7] = true := by decide +kernel
theorem sub7_318 : sub7 [-1, -1, -6] = true := by decide +kernel
theorem sub7_319 : sub7 [-1, -1, -5] = true := by decide +kernel
theorem sb7_9 : ∀ q ∈ blk7_9, sub7 q = true := by
  unfold blk7_9
  exact List.forall_mem_cons.2 ⟨sub7_288, List.forall_mem_cons.2 ⟨sub7_289, List.forall_mem_cons.2 ⟨sub7_290, List.forall_mem_cons.2 ⟨sub7_291, List.forall_mem_cons.2 ⟨sub7_292, List.forall_mem_cons.2 ⟨sub7_293, List.forall_mem_cons.2 ⟨sub7_294, List.forall_mem_cons.2 ⟨sub7_295, List.forall_mem_cons.2 ⟨sub7_296, List.forall_mem_cons.2 ⟨sub7_297, List.forall_mem_cons.2 ⟨sub7_298, List.forall_mem_cons.2 ⟨sub7_299, List.forall_mem_cons.2 ⟨sub7_300, List.forall_mem_cons.2 ⟨sub7_301, List.forall_mem_cons.2 ⟨sub7_302, List.forall_mem_cons.2 ⟨sub7_303, List.forall_mem_cons.2 ⟨sub7_304, List.forall_mem_cons.2 ⟨sub7_305, List.forall_mem_cons.2 ⟨sub7_306, List.forall_mem_cons.2 ⟨sub7_307, List.forall_mem_cons.2 ⟨sub7_308, List.forall_mem_cons.2 ⟨sub7_309, List.forall_mem_cons.2 ⟨sub7_310, List.forall_mem_cons.2 ⟨sub7_311, List.forall_mem_cons.2 ⟨sub7_312, List.forall_mem_cons.2 ⟨sub7_313, List.forall_mem_cons.2 ⟨sub7_314, List.forall_mem_cons.2 ⟨sub7_315, List.forall_mem_cons.2 ⟨sub7_316, List.forall_mem_cons.2 ⟨sub7_317, List.forall_mem_cons.2 ⟨sub7_318, List.forall_mem_cons.2 ⟨sub7_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_320 : sub7 [-1, -1, -4] = true := by decide +kernel
theorem sub7_321 : sub7 [-1, -1, -3] = true := by decide +kernel
theorem sub7_322 : sub7 [-1, -1, -2] = true := by decide +kernel
theorem sub7_323 : sub7 [-1, -1, -1] = true := by decide +kernel
theorem sub7_324 : sub7 [-1, -1, 0] = true := by decide +kernel
theorem sub7_325 : sub7 [-1, -1, 1] = true := by decide +kernel
theorem sub7_326 : sub7 [-1, -1, 2] = true := by decide +kernel
theorem sub7_327 : sub7 [-1, -1, 3] = true := by decide +kernel
theorem sub7_328 : sub7 [-1, -1, 4] = true := by decide +kernel
theorem sub7_329 : sub7 [-1, -1, 5] = true := by decide +kernel
theorem sub7_330 : sub7 [-1, -1, 6] = true := by decide +kernel
theorem sub7_331 : sub7 [-1, -1, 7] = true := by decide +kernel
theorem sub7_332 : sub7 [-1, 0, -9] = true := by decide +kernel
theorem sub7_333 : sub7 [-1, 0, -8] = true := by decide +kernel
theorem sub7_334 : sub7 [-1, 0, -7] = true := by decide +kernel
theorem sub7_335 : sub7 [-1, 0, -6] = true := by decide +kernel
theorem sub7_336 : sub7 [-1, 0, -5] = true := by decide +kernel
theorem sub7_337 : sub7 [-1, 0, -4] = true := by decide +kernel
theorem sub7_338 : sub7 [-1, 0, -3] = true := by decide +kernel
theorem sub7_339 : sub7 [-1, 0, -2] = true := by decide +kernel
theorem sub7_340 : sub7 [-1, 0, -1] = true := by decide +kernel
theorem sub7_341 : sub7 [-1, 0, 0] = true := by decide +kernel
theorem sub7_342 : sub7 [-1, 0, 1] = true := by decide +kernel
theorem sub7_343 : sub7 [-1, 0, 2] = true := by decide +kernel
theorem sub7_344 : sub7 [-1, 0, 3] = true := by decide +kernel
theorem sub7_345 : sub7 [-1, 0, 4] = true := by decide +kernel
theorem sub7_346 : sub7 [-1, 0, 5] = true := by decide +kernel
theorem sub7_347 : sub7 [-1, 0, 6] = true := by decide +kernel
theorem sub7_348 : sub7 [-1, 0, 7] = true := by decide +kernel
theorem sub7_349 : sub7 [-1, 0, 8] = true := by decide +kernel
theorem sub7_350 : sub7 [-1, 1, -9] = true := by decide +kernel
theorem sub7_351 : sub7 [-1, 1, -8] = true := by decide +kernel
theorem sb7_10 : ∀ q ∈ blk7_10, sub7 q = true := by
  unfold blk7_10
  exact List.forall_mem_cons.2 ⟨sub7_320, List.forall_mem_cons.2 ⟨sub7_321, List.forall_mem_cons.2 ⟨sub7_322, List.forall_mem_cons.2 ⟨sub7_323, List.forall_mem_cons.2 ⟨sub7_324, List.forall_mem_cons.2 ⟨sub7_325, List.forall_mem_cons.2 ⟨sub7_326, List.forall_mem_cons.2 ⟨sub7_327, List.forall_mem_cons.2 ⟨sub7_328, List.forall_mem_cons.2 ⟨sub7_329, List.forall_mem_cons.2 ⟨sub7_330, List.forall_mem_cons.2 ⟨sub7_331, List.forall_mem_cons.2 ⟨sub7_332, List.forall_mem_cons.2 ⟨sub7_333, List.forall_mem_cons.2 ⟨sub7_334, List.forall_mem_cons.2 ⟨sub7_335, List.forall_mem_cons.2 ⟨sub7_336, List.forall_mem_cons.2 ⟨sub7_337, List.forall_mem_cons.2 ⟨sub7_338, List.forall_mem_cons.2 ⟨sub7_339, List.forall_mem_cons.2 ⟨sub7_340, List.forall_mem_cons.2 ⟨sub7_341, List.forall_mem_cons.2 ⟨sub7_342, List.forall_mem_cons.2 ⟨sub7_343, List.forall_mem_cons.2 ⟨sub7_344, List.forall_mem_cons.2 ⟨sub7_345, List.forall_mem_cons.2 ⟨sub7_346, List.forall_mem_cons.2 ⟨sub7_347, List.forall_mem_cons.2 ⟨sub7_348, List.forall_mem_cons.2 ⟨sub7_349, List.forall_mem_cons.2 ⟨sub7_350, List.forall_mem_cons.2 ⟨sub7_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_352 : sub7 [-1, 1, -7] = true := by decide +kernel
theorem sub7_353 : sub7 [-1, 1, -6] = true := by decide +kernel
theorem sub7_354 : sub7 [-1, 1, -5] = true := by decide +kernel
theorem sub7_355 : sub7 [-1, 1, -4] = true := by decide +kernel
theorem sub7_356 : sub7 [-1, 1, -3] = true := by decide +kernel
theorem sub7_357 : sub7 [-1, 1, -2] = true := by decide +kernel
theorem sub7_358 : sub7 [-1, 1, -1] = true := by decide +kernel
theorem sub7_359 : sub7 [-1, 1, 0] = true := by decide +kernel
theorem sub7_360 : sub7 [-1, 1, 1] = true := by decide +kernel
theorem sub7_361 : sub7 [-1, 1, 2] = true := by decide +kernel
theorem sub7_362 : sub7 [-1, 1, 3] = true := by decide +kernel
theorem sub7_363 : sub7 [-1, 1, 4] = true := by decide +kernel
theorem sub7_364 : sub7 [-1, 1, 5] = true := by decide +kernel
theorem sub7_365 : sub7 [-1, 1, 6] = true := by decide +kernel
theorem sub7_366 : sub7 [-1, 1, 7] = true := by decide +kernel
theorem sub7_367 : sub7 [-1, 1, 8] = true := by decide +kernel
theorem sub7_368 : sub7 [-1, 2, -8] = true := by decide +kernel
theorem sub7_369 : sub7 [-1, 2, -7] = true := by decide +kernel
theorem sub7_370 : sub7 [-1, 2, -6] = true := by decide +kernel
theorem sub7_371 : sub7 [-1, 2, -5] = true := by decide +kernel
theorem sub7_372 : sub7 [-1, 2, -4] = true := by decide +kernel
theorem sub7_373 : sub7 [-1, 2, -3] = true := by decide +kernel
theorem sub7_374 : sub7 [-1, 2, -2] = true := by decide +kernel
theorem sub7_375 : sub7 [-1, 2, -1] = true := by decide +kernel
theorem sub7_376 : sub7 [-1, 2, 0] = true := by decide +kernel
theorem sub7_377 : sub7 [-1, 2, 1] = true := by decide +kernel
theorem sub7_378 : sub7 [-1, 2, 2] = true := by decide +kernel
theorem sub7_379 : sub7 [-1, 2, 3] = true := by decide +kernel
theorem sub7_380 : sub7 [-1, 2, 4] = true := by decide +kernel
theorem sub7_381 : sub7 [-1, 2, 5] = true := by decide +kernel
theorem sub7_382 : sub7 [-1, 2, 6] = true := by decide +kernel
theorem sub7_383 : sub7 [-1, 2, 7] = true := by decide +kernel
theorem sb7_11 : ∀ q ∈ blk7_11, sub7 q = true := by
  unfold blk7_11
  exact List.forall_mem_cons.2 ⟨sub7_352, List.forall_mem_cons.2 ⟨sub7_353, List.forall_mem_cons.2 ⟨sub7_354, List.forall_mem_cons.2 ⟨sub7_355, List.forall_mem_cons.2 ⟨sub7_356, List.forall_mem_cons.2 ⟨sub7_357, List.forall_mem_cons.2 ⟨sub7_358, List.forall_mem_cons.2 ⟨sub7_359, List.forall_mem_cons.2 ⟨sub7_360, List.forall_mem_cons.2 ⟨sub7_361, List.forall_mem_cons.2 ⟨sub7_362, List.forall_mem_cons.2 ⟨sub7_363, List.forall_mem_cons.2 ⟨sub7_364, List.forall_mem_cons.2 ⟨sub7_365, List.forall_mem_cons.2 ⟨sub7_366, List.forall_mem_cons.2 ⟨sub7_367, List.forall_mem_cons.2 ⟨sub7_368, List.forall_mem_cons.2 ⟨sub7_369, List.forall_mem_cons.2 ⟨sub7_370, List.forall_mem_cons.2 ⟨sub7_371, List.forall_mem_cons.2 ⟨sub7_372, List.forall_mem_cons.2 ⟨sub7_373, List.forall_mem_cons.2 ⟨sub7_374, List.forall_mem_cons.2 ⟨sub7_375, List.forall_mem_cons.2 ⟨sub7_376, List.forall_mem_cons.2 ⟨sub7_377, List.forall_mem_cons.2 ⟨sub7_378, List.forall_mem_cons.2 ⟨sub7_379, List.forall_mem_cons.2 ⟨sub7_380, List.forall_mem_cons.2 ⟨sub7_381, List.forall_mem_cons.2 ⟨sub7_382, List.forall_mem_cons.2 ⟨sub7_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_384 : sub7 [-1, 2, 8] = true := by decide +kernel
theorem sub7_385 : sub7 [-1, 3, -8] = true := by decide +kernel
theorem sub7_386 : sub7 [-1, 3, -7] = true := by decide +kernel
theorem sub7_387 : sub7 [-1, 3, -6] = true := by decide +kernel
theorem sub7_388 : sub7 [-1, 3, -5] = true := by decide +kernel
theorem sub7_389 : sub7 [-1, 3, -4] = true := by decide +kernel
theorem sub7_390 : sub7 [-1, 3, -3] = true := by decide +kernel
theorem sub7_391 : sub7 [-1, 3, -2] = true := by decide +kernel
theorem sub7_392 : sub7 [-1, 3, -1] = true := by decide +kernel
theorem sub7_393 : sub7 [-1, 3, 0] = true := by decide +kernel
theorem sub7_394 : sub7 [-1, 3, 1] = true := by decide +kernel
theorem sub7_395 : sub7 [-1, 3, 2] = true := by decide +kernel
theorem sub7_396 : sub7 [-1, 3, 3] = true := by decide +kernel
theorem sub7_397 : sub7 [-1, 3, 4] = true := by decide +kernel
theorem sub7_398 : sub7 [-1, 3, 5] = true := by decide +kernel
theorem sub7_399 : sub7 [-1, 3, 6] = true := by decide +kernel
theorem sub7_400 : sub7 [-1, 3, 7] = true := by decide +kernel
theorem sub7_401 : sub7 [-1, 3, 8] = true := by decide +kernel
theorem sub7_402 : sub7 [-1, 4, -7] = true := by decide +kernel
theorem sub7_403 : sub7 [-1, 4, -6] = true := by decide +kernel
theorem sub7_404 : sub7 [-1, 4, -5] = true := by decide +kernel
theorem sub7_405 : sub7 [-1, 4, -4] = true := by decide +kernel
theorem sub7_406 : sub7 [-1, 4, -3] = true := by decide +kernel
theorem sub7_407 : sub7 [-1, 4, -2] = true := by decide +kernel
theorem sub7_408 : sub7 [-1, 4, -1] = true := by decide +kernel
theorem sub7_409 : sub7 [-1, 4, 0] = true := by decide +kernel
theorem sub7_410 : sub7 [-1, 4, 1] = true := by decide +kernel
theorem sub7_411 : sub7 [-1, 4, 2] = true := by decide +kernel
theorem sub7_412 : sub7 [-1, 4, 3] = true := by decide +kernel
theorem sub7_413 : sub7 [-1, 4, 4] = true := by decide +kernel
theorem sub7_414 : sub7 [-1, 4, 5] = true := by decide +kernel
theorem sub7_415 : sub7 [-1, 4, 6] = true := by decide +kernel
theorem sb7_12 : ∀ q ∈ blk7_12, sub7 q = true := by
  unfold blk7_12
  exact List.forall_mem_cons.2 ⟨sub7_384, List.forall_mem_cons.2 ⟨sub7_385, List.forall_mem_cons.2 ⟨sub7_386, List.forall_mem_cons.2 ⟨sub7_387, List.forall_mem_cons.2 ⟨sub7_388, List.forall_mem_cons.2 ⟨sub7_389, List.forall_mem_cons.2 ⟨sub7_390, List.forall_mem_cons.2 ⟨sub7_391, List.forall_mem_cons.2 ⟨sub7_392, List.forall_mem_cons.2 ⟨sub7_393, List.forall_mem_cons.2 ⟨sub7_394, List.forall_mem_cons.2 ⟨sub7_395, List.forall_mem_cons.2 ⟨sub7_396, List.forall_mem_cons.2 ⟨sub7_397, List.forall_mem_cons.2 ⟨sub7_398, List.forall_mem_cons.2 ⟨sub7_399, List.forall_mem_cons.2 ⟨sub7_400, List.forall_mem_cons.2 ⟨sub7_401, List.forall_mem_cons.2 ⟨sub7_402, List.forall_mem_cons.2 ⟨sub7_403, List.forall_mem_cons.2 ⟨sub7_404, List.forall_mem_cons.2 ⟨sub7_405, List.forall_mem_cons.2 ⟨sub7_406, List.forall_mem_cons.2 ⟨sub7_407, List.forall_mem_cons.2 ⟨sub7_408, List.forall_mem_cons.2 ⟨sub7_409, List.forall_mem_cons.2 ⟨sub7_410, List.forall_mem_cons.2 ⟨sub7_411, List.forall_mem_cons.2 ⟨sub7_412, List.forall_mem_cons.2 ⟨sub7_413, List.forall_mem_cons.2 ⟨sub7_414, List.forall_mem_cons.2 ⟨sub7_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_416 : sub7 [-1, 4, 7] = true := by decide +kernel
theorem sub7_417 : sub7 [-1, 5] = true := by decide +kernel
theorem sub7_418 : sub7 [-1, 6] = true := by decide +kernel
theorem sub7_419 : sub7 [-1, 7] = true := by decide +kernel
theorem sub7_420 : sub7 [0, -7] = true := by decide +kernel
theorem sub7_421 : sub7 [0, -6] = true := by decide +kernel
theorem sub7_422 : sub7 [0, -5] = true := by decide +kernel
theorem sub7_423 : sub7 [0, -4, -9] = true := by decide +kernel
theorem sub7_424 : sub7 [0, -4, -8] = true := by decide +kernel
theorem sub7_425 : sub7 [0, -4, -7] = true := by decide +kernel
theorem sub7_426 : sub7 [0, -4, -6] = true := by decide +kernel
theorem sub7_427 : sub7 [0, -4, -5] = true := by decide +kernel
theorem sub7_428 : sub7 [0, -4, -4] = true := by decide +kernel
theorem sub7_429 : sub7 [0, -4, -3] = true := by decide +kernel
theorem sub7_430 : sub7 [0, -4, -2] = true := by decide +kernel
theorem sub7_431 : sub7 [0, -4, -1] = true := by decide +kernel
theorem sub7_432 : sub7 [0, -4, 0] = true := by decide +kernel
theorem sub7_433 : sub7 [0, -4, 1] = true := by decide +kernel
theorem sub7_434 : sub7 [0, -4, 2] = true := by decide +kernel
theorem sub7_435 : sub7 [0, -4, 3] = true := by decide +kernel
theorem sub7_436 : sub7 [0, -4, 4] = true := by decide +kernel
theorem sub7_437 : sub7 [0, -4, 5] = true := by decide +kernel
theorem sub7_438 : sub7 [0, -3, -9] = true := by decide +kernel
theorem sub7_439 : sub7 [0, -3, -8] = true := by decide +kernel
theorem sub7_440 : sub7 [0, -3, -7] = true := by decide +kernel
theorem sub7_441 : sub7 [0, -3, -6] = true := by decide +kernel
theorem sub7_442 : sub7 [0, -3, -5] = true := by decide +kernel
theorem sub7_443 : sub7 [0, -3, -4] = true := by decide +kernel
theorem sub7_444 : sub7 [0, -3, -3] = true := by decide +kernel
theorem sub7_445 : sub7 [0, -3, -2] = true := by decide +kernel
theorem sub7_446 : sub7 [0, -3, -1] = true := by decide +kernel
theorem sub7_447 : sub7 [0, -3, 0] = true := by decide +kernel
theorem sb7_13 : ∀ q ∈ blk7_13, sub7 q = true := by
  unfold blk7_13
  exact List.forall_mem_cons.2 ⟨sub7_416, List.forall_mem_cons.2 ⟨sub7_417, List.forall_mem_cons.2 ⟨sub7_418, List.forall_mem_cons.2 ⟨sub7_419, List.forall_mem_cons.2 ⟨sub7_420, List.forall_mem_cons.2 ⟨sub7_421, List.forall_mem_cons.2 ⟨sub7_422, List.forall_mem_cons.2 ⟨sub7_423, List.forall_mem_cons.2 ⟨sub7_424, List.forall_mem_cons.2 ⟨sub7_425, List.forall_mem_cons.2 ⟨sub7_426, List.forall_mem_cons.2 ⟨sub7_427, List.forall_mem_cons.2 ⟨sub7_428, List.forall_mem_cons.2 ⟨sub7_429, List.forall_mem_cons.2 ⟨sub7_430, List.forall_mem_cons.2 ⟨sub7_431, List.forall_mem_cons.2 ⟨sub7_432, List.forall_mem_cons.2 ⟨sub7_433, List.forall_mem_cons.2 ⟨sub7_434, List.forall_mem_cons.2 ⟨sub7_435, List.forall_mem_cons.2 ⟨sub7_436, List.forall_mem_cons.2 ⟨sub7_437, List.forall_mem_cons.2 ⟨sub7_438, List.forall_mem_cons.2 ⟨sub7_439, List.forall_mem_cons.2 ⟨sub7_440, List.forall_mem_cons.2 ⟨sub7_441, List.forall_mem_cons.2 ⟨sub7_442, List.forall_mem_cons.2 ⟨sub7_443, List.forall_mem_cons.2 ⟨sub7_444, List.forall_mem_cons.2 ⟨sub7_445, List.forall_mem_cons.2 ⟨sub7_446, List.forall_mem_cons.2 ⟨sub7_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_448 : sub7 [0, -3, 1] = true := by decide +kernel
theorem sub7_449 : sub7 [0, -3, 2] = true := by decide +kernel
theorem sub7_450 : sub7 [0, -3, 3] = true := by decide +kernel
theorem sub7_451 : sub7 [0, -3, 4] = true := by decide +kernel
theorem sub7_452 : sub7 [0, -3, 5] = true := by decide +kernel
theorem sub7_453 : sub7 [0, -3, 6] = true := by decide +kernel
theorem sub7_454 : sub7 [0, -2, -9] = true := by decide +kernel
theorem sub7_455 : sub7 [0, -2, -8] = true := by decide +kernel
theorem sub7_456 : sub7 [0, -2, -7] = true := by decide +kernel
theorem sub7_457 : sub7 [0, -2, -6] = true := by decide +kernel
theorem sub7_458 : sub7 [0, -2, -5] = true := by decide +kernel
theorem sub7_459 : sub7 [0, -2, -4] = true := by decide +kernel
theorem sub7_460 : sub7 [0, -2, -3] = true := by decide +kernel
theorem sub7_461 : sub7 [0, -2, -2] = true := by decide +kernel
theorem sub7_462 : sub7 [0, -2, -1] = true := by decide +kernel
theorem sub7_463 : sub7 [0, -2, 0] = true := by decide +kernel
theorem sub7_464 : sub7 [0, -2, 1] = true := by decide +kernel
theorem sub7_465 : sub7 [0, -2, 2] = true := by decide +kernel
theorem sub7_466 : sub7 [0, -2, 3] = true := by decide +kernel
theorem sub7_467 : sub7 [0, -2, 4] = true := by decide +kernel
theorem sub7_468 : sub7 [0, -2, 5] = true := by decide +kernel
theorem sub7_469 : sub7 [0, -2, 6] = true := by decide +kernel
theorem sub7_470 : sub7 [0, -2, 7] = true := by decide +kernel
theorem sub7_471 : sub7 [0, -1, -9] = true := by decide +kernel
theorem sub7_472 : sub7 [0, -1, -8] = true := by decide +kernel
theorem sub7_473 : sub7 [0, -1, -7] = true := by decide +kernel
theorem sub7_474 : sub7 [0, -1, -6] = true := by decide +kernel
theorem sub7_475 : sub7 [0, -1, -5] = true := by decide +kernel
theorem sub7_476 : sub7 [0, -1, -4] = true := by decide +kernel
theorem sub7_477 : sub7 [0, -1, -3] = true := by decide +kernel
theorem sub7_478 : sub7 [0, -1, -2] = true := by decide +kernel
theorem sub7_479 : sub7 [0, -1, -1] = true := by decide +kernel
theorem sb7_14 : ∀ q ∈ blk7_14, sub7 q = true := by
  unfold blk7_14
  exact List.forall_mem_cons.2 ⟨sub7_448, List.forall_mem_cons.2 ⟨sub7_449, List.forall_mem_cons.2 ⟨sub7_450, List.forall_mem_cons.2 ⟨sub7_451, List.forall_mem_cons.2 ⟨sub7_452, List.forall_mem_cons.2 ⟨sub7_453, List.forall_mem_cons.2 ⟨sub7_454, List.forall_mem_cons.2 ⟨sub7_455, List.forall_mem_cons.2 ⟨sub7_456, List.forall_mem_cons.2 ⟨sub7_457, List.forall_mem_cons.2 ⟨sub7_458, List.forall_mem_cons.2 ⟨sub7_459, List.forall_mem_cons.2 ⟨sub7_460, List.forall_mem_cons.2 ⟨sub7_461, List.forall_mem_cons.2 ⟨sub7_462, List.forall_mem_cons.2 ⟨sub7_463, List.forall_mem_cons.2 ⟨sub7_464, List.forall_mem_cons.2 ⟨sub7_465, List.forall_mem_cons.2 ⟨sub7_466, List.forall_mem_cons.2 ⟨sub7_467, List.forall_mem_cons.2 ⟨sub7_468, List.forall_mem_cons.2 ⟨sub7_469, List.forall_mem_cons.2 ⟨sub7_470, List.forall_mem_cons.2 ⟨sub7_471, List.forall_mem_cons.2 ⟨sub7_472, List.forall_mem_cons.2 ⟨sub7_473, List.forall_mem_cons.2 ⟨sub7_474, List.forall_mem_cons.2 ⟨sub7_475, List.forall_mem_cons.2 ⟨sub7_476, List.forall_mem_cons.2 ⟨sub7_477, List.forall_mem_cons.2 ⟨sub7_478, List.forall_mem_cons.2 ⟨sub7_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_480 : sub7 [0, -1, 0] = true := by decide +kernel
theorem sub7_481 : sub7 [0, -1, 1] = true := by decide +kernel
theorem sub7_482 : sub7 [0, -1, 2] = true := by decide +kernel
theorem sub7_483 : sub7 [0, -1, 3] = true := by decide +kernel
theorem sub7_484 : sub7 [0, -1, 4] = true := by decide +kernel
theorem sub7_485 : sub7 [0, -1, 5] = true := by decide +kernel
theorem sub7_486 : sub7 [0, -1, 6] = true := by decide +kernel
theorem sub7_487 : sub7 [0, -1, 7] = true := by decide +kernel
theorem sub7_488 : sub7 [0, -1, 8] = true := by decide +kernel
theorem sub7_489 : sub7 [0, 0, -9] = true := by decide +kernel
theorem sub7_490 : sub7 [0, 0, -8] = true := by decide +kernel
theorem sub7_491 : sub7 [0, 0, -7] = true := by decide +kernel
theorem sub7_492 : sub7 [0, 0, -6] = true := by decide +kernel
theorem sub7_493 : sub7 [0, 0, -5] = true := by decide +kernel
theorem sub7_494 : sub7 [0, 0, -4] = true := by decide +kernel
theorem sub7_495 : sub7 [0, 0, -3] = true := by decide +kernel
theorem sub7_496 : sub7 [0, 0, -2] = true := by decide +kernel
theorem sub7_497 : sub7 [0, 0, -1] = true := by decide +kernel
theorem sub7_498 : sub7 [0, 0, 0] = true := by decide +kernel
theorem sub7_499 : sub7 [0, 0, 1] = true := by decide +kernel
theorem sub7_500 : sub7 [0, 0, 2] = true := by decide +kernel
theorem sub7_501 : sub7 [0, 0, 3] = true := by decide +kernel
theorem sub7_502 : sub7 [0, 0, 4] = true := by decide +kernel
theorem sub7_503 : sub7 [0, 0, 5] = true := by decide +kernel
theorem sub7_504 : sub7 [0, 0, 6] = true := by decide +kernel
theorem sub7_505 : sub7 [0, 0, 7] = true := by decide +kernel
theorem sub7_506 : sub7 [0, 0, 8] = true := by decide +kernel
theorem sub7_507 : sub7 [0, 1, -9] = true := by decide +kernel
theorem sub7_508 : sub7 [0, 1, -8] = true := by decide +kernel
theorem sub7_509 : sub7 [0, 1, -7] = true := by decide +kernel
theorem sub7_510 : sub7 [0, 1, -6] = true := by decide +kernel
theorem sub7_511 : sub7 [0, 1, -5] = true := by decide +kernel
theorem sb7_15 : ∀ q ∈ blk7_15, sub7 q = true := by
  unfold blk7_15
  exact List.forall_mem_cons.2 ⟨sub7_480, List.forall_mem_cons.2 ⟨sub7_481, List.forall_mem_cons.2 ⟨sub7_482, List.forall_mem_cons.2 ⟨sub7_483, List.forall_mem_cons.2 ⟨sub7_484, List.forall_mem_cons.2 ⟨sub7_485, List.forall_mem_cons.2 ⟨sub7_486, List.forall_mem_cons.2 ⟨sub7_487, List.forall_mem_cons.2 ⟨sub7_488, List.forall_mem_cons.2 ⟨sub7_489, List.forall_mem_cons.2 ⟨sub7_490, List.forall_mem_cons.2 ⟨sub7_491, List.forall_mem_cons.2 ⟨sub7_492, List.forall_mem_cons.2 ⟨sub7_493, List.forall_mem_cons.2 ⟨sub7_494, List.forall_mem_cons.2 ⟨sub7_495, List.forall_mem_cons.2 ⟨sub7_496, List.forall_mem_cons.2 ⟨sub7_497, List.forall_mem_cons.2 ⟨sub7_498, List.forall_mem_cons.2 ⟨sub7_499, List.forall_mem_cons.2 ⟨sub7_500, List.forall_mem_cons.2 ⟨sub7_501, List.forall_mem_cons.2 ⟨sub7_502, List.forall_mem_cons.2 ⟨sub7_503, List.forall_mem_cons.2 ⟨sub7_504, List.forall_mem_cons.2 ⟨sub7_505, List.forall_mem_cons.2 ⟨sub7_506, List.forall_mem_cons.2 ⟨sub7_507, List.forall_mem_cons.2 ⟨sub7_508, List.forall_mem_cons.2 ⟨sub7_509, List.forall_mem_cons.2 ⟨sub7_510, List.forall_mem_cons.2 ⟨sub7_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_512 : sub7 [0, 1, -4] = true := by decide +kernel
theorem sub7_513 : sub7 [0, 1, -3] = true := by decide +kernel
theorem sub7_514 : sub7 [0, 1, -2] = true := by decide +kernel
theorem sub7_515 : sub7 [0, 1, -1] = true := by decide +kernel
theorem sub7_516 : sub7 [0, 1, 0] = true := by decide +kernel
theorem sub7_517 : sub7 [0, 1, 1] = true := by decide +kernel
theorem sub7_518 : sub7 [0, 1, 2] = true := by decide +kernel
theorem sub7_519 : sub7 [0, 1, 3] = true := by decide +kernel
theorem sub7_520 : sub7 [0, 1, 4] = true := by decide +kernel
theorem sub7_521 : sub7 [0, 1, 5] = true := by decide +kernel
theorem sub7_522 : sub7 [0, 1, 6] = true := by decide +kernel
theorem sub7_523 : sub7 [0, 1, 7] = true := by decide +kernel
theorem sub7_524 : sub7 [0, 1, 8] = true := by decide +kernel
theorem sub7_525 : sub7 [0, 2, -8] = true := by decide +kernel
theorem sub7_526 : sub7 [0, 2, -7] = true := by decide +kernel
theorem sub7_527 : sub7 [0, 2, -6] = true := by decide +kernel
theorem sub7_528 : sub7 [0, 2, -5] = true := by decide +kernel
theorem sub7_529 : sub7 [0, 2, -4] = true := by decide +kernel
theorem sub7_530 : sub7 [0, 2, -3] = true := by decide +kernel
theorem sub7_531 : sub7 [0, 2, -2] = true := by decide +kernel
theorem sub7_532 : sub7 [0, 2, -1] = true := by decide +kernel
theorem sub7_533 : sub7 [0, 2, 0] = true := by decide +kernel
theorem sub7_534 : sub7 [0, 2, 1] = true := by decide +kernel
theorem sub7_535 : sub7 [0, 2, 2] = true := by decide +kernel
theorem sub7_536 : sub7 [0, 2, 3] = true := by decide +kernel
theorem sub7_537 : sub7 [0, 2, 4] = true := by decide +kernel
theorem sub7_538 : sub7 [0, 2, 5] = true := by decide +kernel
theorem sub7_539 : sub7 [0, 2, 6] = true := by decide +kernel
theorem sub7_540 : sub7 [0, 2, 7] = true := by decide +kernel
theorem sub7_541 : sub7 [0, 2, 8] = true := by decide +kernel
theorem sub7_542 : sub7 [0, 3, -7] = true := by decide +kernel
theorem sub7_543 : sub7 [0, 3, -6] = true := by decide +kernel
theorem sb7_16 : ∀ q ∈ blk7_16, sub7 q = true := by
  unfold blk7_16
  exact List.forall_mem_cons.2 ⟨sub7_512, List.forall_mem_cons.2 ⟨sub7_513, List.forall_mem_cons.2 ⟨sub7_514, List.forall_mem_cons.2 ⟨sub7_515, List.forall_mem_cons.2 ⟨sub7_516, List.forall_mem_cons.2 ⟨sub7_517, List.forall_mem_cons.2 ⟨sub7_518, List.forall_mem_cons.2 ⟨sub7_519, List.forall_mem_cons.2 ⟨sub7_520, List.forall_mem_cons.2 ⟨sub7_521, List.forall_mem_cons.2 ⟨sub7_522, List.forall_mem_cons.2 ⟨sub7_523, List.forall_mem_cons.2 ⟨sub7_524, List.forall_mem_cons.2 ⟨sub7_525, List.forall_mem_cons.2 ⟨sub7_526, List.forall_mem_cons.2 ⟨sub7_527, List.forall_mem_cons.2 ⟨sub7_528, List.forall_mem_cons.2 ⟨sub7_529, List.forall_mem_cons.2 ⟨sub7_530, List.forall_mem_cons.2 ⟨sub7_531, List.forall_mem_cons.2 ⟨sub7_532, List.forall_mem_cons.2 ⟨sub7_533, List.forall_mem_cons.2 ⟨sub7_534, List.forall_mem_cons.2 ⟨sub7_535, List.forall_mem_cons.2 ⟨sub7_536, List.forall_mem_cons.2 ⟨sub7_537, List.forall_mem_cons.2 ⟨sub7_538, List.forall_mem_cons.2 ⟨sub7_539, List.forall_mem_cons.2 ⟨sub7_540, List.forall_mem_cons.2 ⟨sub7_541, List.forall_mem_cons.2 ⟨sub7_542, List.forall_mem_cons.2 ⟨sub7_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_544 : sub7 [0, 3, -5] = true := by decide +kernel
theorem sub7_545 : sub7 [0, 3, -4] = true := by decide +kernel
theorem sub7_546 : sub7 [0, 3, -3] = true := by decide +kernel
theorem sub7_547 : sub7 [0, 3, -2] = true := by decide +kernel
theorem sub7_548 : sub7 [0, 3, -1] = true := by decide +kernel
theorem sub7_549 : sub7 [0, 3, 0] = true := by decide +kernel
theorem sub7_550 : sub7 [0, 3, 1] = true := by decide +kernel
theorem sub7_551 : sub7 [0, 3, 2] = true := by decide +kernel
theorem sub7_552 : sub7 [0, 3, 3] = true := by decide +kernel
theorem sub7_553 : sub7 [0, 3, 4] = true := by decide +kernel
theorem sub7_554 : sub7 [0, 3, 5] = true := by decide +kernel
theorem sub7_555 : sub7 [0, 3, 6] = true := by decide +kernel
theorem sub7_556 : sub7 [0, 3, 7] = true := by decide +kernel
theorem sub7_557 : sub7 [0, 3, 8] = true := by decide +kernel
theorem sub7_558 : sub7 [0, 4, -6] = true := by decide +kernel
theorem sub7_559 : sub7 [0, 4, -5] = true := by decide +kernel
theorem sub7_560 : sub7 [0, 4, -4] = true := by decide +kernel
theorem sub7_561 : sub7 [0, 4, -3] = true := by decide +kernel
theorem sub7_562 : sub7 [0, 4, -2] = true := by decide +kernel
theorem sub7_563 : sub7 [0, 4, -1] = true := by decide +kernel
theorem sub7_564 : sub7 [0, 4, 0] = true := by decide +kernel
theorem sub7_565 : sub7 [0, 4, 1] = true := by decide +kernel
theorem sub7_566 : sub7 [0, 4, 2] = true := by decide +kernel
theorem sub7_567 : sub7 [0, 4, 3] = true := by decide +kernel
theorem sub7_568 : sub7 [0, 4, 4] = true := by decide +kernel
theorem sub7_569 : sub7 [0, 4, 5] = true := by decide +kernel
theorem sub7_570 : sub7 [0, 4, 6] = true := by decide +kernel
theorem sub7_571 : sub7 [0, 4, 7] = true := by decide +kernel
theorem sub7_572 : sub7 [0, 4, 8] = true := by decide +kernel
theorem sub7_573 : sub7 [0, 5] = true := by decide +kernel
theorem sub7_574 : sub7 [0, 6] = true := by decide +kernel
theorem sub7_575 : sub7 [1, -8] = true := by decide +kernel
theorem sb7_17 : ∀ q ∈ blk7_17, sub7 q = true := by
  unfold blk7_17
  exact List.forall_mem_cons.2 ⟨sub7_544, List.forall_mem_cons.2 ⟨sub7_545, List.forall_mem_cons.2 ⟨sub7_546, List.forall_mem_cons.2 ⟨sub7_547, List.forall_mem_cons.2 ⟨sub7_548, List.forall_mem_cons.2 ⟨sub7_549, List.forall_mem_cons.2 ⟨sub7_550, List.forall_mem_cons.2 ⟨sub7_551, List.forall_mem_cons.2 ⟨sub7_552, List.forall_mem_cons.2 ⟨sub7_553, List.forall_mem_cons.2 ⟨sub7_554, List.forall_mem_cons.2 ⟨sub7_555, List.forall_mem_cons.2 ⟨sub7_556, List.forall_mem_cons.2 ⟨sub7_557, List.forall_mem_cons.2 ⟨sub7_558, List.forall_mem_cons.2 ⟨sub7_559, List.forall_mem_cons.2 ⟨sub7_560, List.forall_mem_cons.2 ⟨sub7_561, List.forall_mem_cons.2 ⟨sub7_562, List.forall_mem_cons.2 ⟨sub7_563, List.forall_mem_cons.2 ⟨sub7_564, List.forall_mem_cons.2 ⟨sub7_565, List.forall_mem_cons.2 ⟨sub7_566, List.forall_mem_cons.2 ⟨sub7_567, List.forall_mem_cons.2 ⟨sub7_568, List.forall_mem_cons.2 ⟨sub7_569, List.forall_mem_cons.2 ⟨sub7_570, List.forall_mem_cons.2 ⟨sub7_571, List.forall_mem_cons.2 ⟨sub7_572, List.forall_mem_cons.2 ⟨sub7_573, List.forall_mem_cons.2 ⟨sub7_574, List.forall_mem_cons.2 ⟨sub7_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_576 : sub7 [1, -7] = true := by decide +kernel
theorem sub7_577 : sub7 [1, -6] = true := by decide +kernel
theorem sub7_578 : sub7 [1, -5] = true := by decide +kernel
theorem sub7_579 : sub7 [1, -4, -8] = true := by decide +kernel
theorem sub7_580 : sub7 [1, -4, -7] = true := by decide +kernel
theorem sub7_581 : sub7 [1, -4, -6] = true := by decide +kernel
theorem sub7_582 : sub7 [1, -4, -5] = true := by decide +kernel
theorem sub7_583 : sub7 [1, -4, -4] = true := by decide +kernel
theorem sub7_584 : sub7 [1, -4, -3] = true := by decide +kernel
theorem sub7_585 : sub7 [1, -4, -2] = true := by decide +kernel
theorem sub7_586 : sub7 [1, -4, -1] = true := by decide +kernel
theorem sub7_587 : sub7 [1, -4, 0] = true := by decide +kernel
theorem sub7_588 : sub7 [1, -4, 1] = true := by decide +kernel
theorem sub7_589 : sub7 [1, -4, 2] = true := by decide +kernel
theorem sub7_590 : sub7 [1, -4, 3] = true := by decide +kernel
theorem sub7_591 : sub7 [1, -4, 4] = true := by decide +kernel
theorem sub7_592 : sub7 [1, -4, 5] = true := by decide +kernel
theorem sub7_593 : sub7 [1, -4, 6] = true := by decide +kernel
theorem sub7_594 : sub7 [1, -3, -9] = true := by decide +kernel
theorem sub7_595 : sub7 [1, -3, -8] = true := by decide +kernel
theorem sub7_596 : sub7 [1, -3, -7] = true := by decide +kernel
theorem sub7_597 : sub7 [1, -3, -6] = true := by decide +kernel
theorem sub7_598 : sub7 [1, -3, -5] = true := by decide +kernel
theorem sub7_599 : sub7 [1, -3, -4] = true := by decide +kernel
theorem sub7_600 : sub7 [1, -3, -3] = true := by decide +kernel
theorem sub7_601 : sub7 [1, -3, -2] = true := by decide +kernel
theorem sub7_602 : sub7 [1, -3, -1] = true := by decide +kernel
theorem sub7_603 : sub7 [1, -3, 0] = true := by decide +kernel
theorem sub7_604 : sub7 [1, -3, 1] = true := by decide +kernel
theorem sub7_605 : sub7 [1, -3, 2] = true := by decide +kernel
theorem sub7_606 : sub7 [1, -3, 3] = true := by decide +kernel
theorem sub7_607 : sub7 [1, -3, 4] = true := by decide +kernel
theorem sb7_18 : ∀ q ∈ blk7_18, sub7 q = true := by
  unfold blk7_18
  exact List.forall_mem_cons.2 ⟨sub7_576, List.forall_mem_cons.2 ⟨sub7_577, List.forall_mem_cons.2 ⟨sub7_578, List.forall_mem_cons.2 ⟨sub7_579, List.forall_mem_cons.2 ⟨sub7_580, List.forall_mem_cons.2 ⟨sub7_581, List.forall_mem_cons.2 ⟨sub7_582, List.forall_mem_cons.2 ⟨sub7_583, List.forall_mem_cons.2 ⟨sub7_584, List.forall_mem_cons.2 ⟨sub7_585, List.forall_mem_cons.2 ⟨sub7_586, List.forall_mem_cons.2 ⟨sub7_587, List.forall_mem_cons.2 ⟨sub7_588, List.forall_mem_cons.2 ⟨sub7_589, List.forall_mem_cons.2 ⟨sub7_590, List.forall_mem_cons.2 ⟨sub7_591, List.forall_mem_cons.2 ⟨sub7_592, List.forall_mem_cons.2 ⟨sub7_593, List.forall_mem_cons.2 ⟨sub7_594, List.forall_mem_cons.2 ⟨sub7_595, List.forall_mem_cons.2 ⟨sub7_596, List.forall_mem_cons.2 ⟨sub7_597, List.forall_mem_cons.2 ⟨sub7_598, List.forall_mem_cons.2 ⟨sub7_599, List.forall_mem_cons.2 ⟨sub7_600, List.forall_mem_cons.2 ⟨sub7_601, List.forall_mem_cons.2 ⟨sub7_602, List.forall_mem_cons.2 ⟨sub7_603, List.forall_mem_cons.2 ⟨sub7_604, List.forall_mem_cons.2 ⟨sub7_605, List.forall_mem_cons.2 ⟨sub7_606, List.forall_mem_cons.2 ⟨sub7_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_608 : sub7 [1, -3, 5] = true := by decide +kernel
theorem sub7_609 : sub7 [1, -3, 6] = true := by decide +kernel
theorem sub7_610 : sub7 [1, -3, 7] = true := by decide +kernel
theorem sub7_611 : sub7 [1, -2, -9] = true := by decide +kernel
theorem sub7_612 : sub7 [1, -2, -8] = true := by decide +kernel
theorem sub7_613 : sub7 [1, -2, -7] = true := by decide +kernel
theorem sub7_614 : sub7 [1, -2, -6] = true := by decide +kernel
theorem sub7_615 : sub7 [1, -2, -5] = true := by decide +kernel
theorem sub7_616 : sub7 [1, -2, -4] = true := by decide +kernel
theorem sub7_617 : sub7 [1, -2, -3] = true := by decide +kernel
theorem sub7_618 : sub7 [1, -2, -2] = true := by decide +kernel
theorem sub7_619 : sub7 [1, -2, -1] = true := by decide +kernel
theorem sub7_620 : sub7 [1, -2, 0] = true := by decide +kernel
theorem sub7_621 : sub7 [1, -2, 1] = true := by decide +kernel
theorem sub7_622 : sub7 [1, -2, 2] = true := by decide +kernel
theorem sub7_623 : sub7 [1, -2, 3] = true := by decide +kernel
theorem sub7_624 : sub7 [1, -2, 4] = true := by decide +kernel
theorem sub7_625 : sub7 [1, -2, 5] = true := by decide +kernel
theorem sub7_626 : sub7 [1, -2, 6] = true := by decide +kernel
theorem sub7_627 : sub7 [1, -2, 7] = true := by decide +kernel
theorem sub7_628 : sub7 [1, -1, -9] = true := by decide +kernel
theorem sub7_629 : sub7 [1, -1, -8] = true := by decide +kernel
theorem sub7_630 : sub7 [1, -1, -7] = true := by decide +kernel
theorem sub7_631 : sub7 [1, -1, -6] = true := by decide +kernel
theorem sub7_632 : sub7 [1, -1, -5] = true := by decide +kernel
theorem sub7_633 : sub7 [1, -1, -4] = true := by decide +kernel
theorem sub7_634 : sub7 [1, -1, -3] = true := by decide +kernel
theorem sub7_635 : sub7 [1, -1, -2] = true := by decide +kernel
theorem sub7_636 : sub7 [1, -1, -1] = true := by decide +kernel
theorem sub7_637 : sub7 [1, -1, 0] = true := by decide +kernel
theorem sub7_638 : sub7 [1, -1, 1] = true := by decide +kernel
theorem sub7_639 : sub7 [1, -1, 2] = true := by decide +kernel
theorem sb7_19 : ∀ q ∈ blk7_19, sub7 q = true := by
  unfold blk7_19
  exact List.forall_mem_cons.2 ⟨sub7_608, List.forall_mem_cons.2 ⟨sub7_609, List.forall_mem_cons.2 ⟨sub7_610, List.forall_mem_cons.2 ⟨sub7_611, List.forall_mem_cons.2 ⟨sub7_612, List.forall_mem_cons.2 ⟨sub7_613, List.forall_mem_cons.2 ⟨sub7_614, List.forall_mem_cons.2 ⟨sub7_615, List.forall_mem_cons.2 ⟨sub7_616, List.forall_mem_cons.2 ⟨sub7_617, List.forall_mem_cons.2 ⟨sub7_618, List.forall_mem_cons.2 ⟨sub7_619, List.forall_mem_cons.2 ⟨sub7_620, List.forall_mem_cons.2 ⟨sub7_621, List.forall_mem_cons.2 ⟨sub7_622, List.forall_mem_cons.2 ⟨sub7_623, List.forall_mem_cons.2 ⟨sub7_624, List.forall_mem_cons.2 ⟨sub7_625, List.forall_mem_cons.2 ⟨sub7_626, List.forall_mem_cons.2 ⟨sub7_627, List.forall_mem_cons.2 ⟨sub7_628, List.forall_mem_cons.2 ⟨sub7_629, List.forall_mem_cons.2 ⟨sub7_630, List.forall_mem_cons.2 ⟨sub7_631, List.forall_mem_cons.2 ⟨sub7_632, List.forall_mem_cons.2 ⟨sub7_633, List.forall_mem_cons.2 ⟨sub7_634, List.forall_mem_cons.2 ⟨sub7_635, List.forall_mem_cons.2 ⟨sub7_636, List.forall_mem_cons.2 ⟨sub7_637, List.forall_mem_cons.2 ⟨sub7_638, List.forall_mem_cons.2 ⟨sub7_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_640 : sub7 [1, -1, 3] = true := by decide +kernel
theorem sub7_641 : sub7 [1, -1, 4] = true := by decide +kernel
theorem sub7_642 : sub7 [1, -1, 5] = true := by decide +kernel
theorem sub7_643 : sub7 [1, -1, 6] = true := by decide +kernel
theorem sub7_644 : sub7 [1, -1, 7] = true := by decide +kernel
theorem sub7_645 : sub7 [1, -1, 8] = true := by decide +kernel
theorem sub7_646 : sub7 [1, 0, -9] = true := by decide +kernel
theorem sub7_647 : sub7 [1, 0, -8] = true := by decide +kernel
theorem sub7_648 : sub7 [1, 0, -7] = true := by decide +kernel
theorem sub7_649 : sub7 [1, 0, -6] = true := by decide +kernel
theorem sub7_650 : sub7 [1, 0, -5] = true := by decide +kernel
theorem sub7_651 : sub7 [1, 0, -4] = true := by decide +kernel
theorem sub7_652 : sub7 [1, 0, -3] = true := by decide +kernel
theorem sub7_653 : sub7 [1, 0, -2] = true := by decide +kernel
theorem sub7_654 : sub7 [1, 0, -1] = true := by decide +kernel
theorem sub7_655 : sub7 [1, 0, 0] = true := by decide +kernel
theorem sub7_656 : sub7 [1, 0, 1] = true := by decide +kernel
theorem sub7_657 : sub7 [1, 0, 2] = true := by decide +kernel
theorem sub7_658 : sub7 [1, 0, 3] = true := by decide +kernel
theorem sub7_659 : sub7 [1, 0, 4] = true := by decide +kernel
theorem sub7_660 : sub7 [1, 0, 5] = true := by decide +kernel
theorem sub7_661 : sub7 [1, 0, 6] = true := by decide +kernel
theorem sub7_662 : sub7 [1, 0, 7] = true := by decide +kernel
theorem sub7_663 : sub7 [1, 0, 8] = true := by decide +kernel
theorem sub7_664 : sub7 [1, 1, -8] = true := by decide +kernel
theorem sub7_665 : sub7 [1, 1, -7] = true := by decide +kernel
theorem sub7_666 : sub7 [1, 1, -6] = true := by decide +kernel
theorem sub7_667 : sub7 [1, 1, -5] = true := by decide +kernel
theorem sub7_668 : sub7 [1, 1, -4] = true := by decide +kernel
theorem sub7_669 : sub7 [1, 1, -3] = true := by decide +kernel
theorem sub7_670 : sub7 [1, 1, -2] = true := by decide +kernel
theorem sub7_671 : sub7 [1, 1, -1] = true := by decide +kernel
theorem sb7_20 : ∀ q ∈ blk7_20, sub7 q = true := by
  unfold blk7_20
  exact List.forall_mem_cons.2 ⟨sub7_640, List.forall_mem_cons.2 ⟨sub7_641, List.forall_mem_cons.2 ⟨sub7_642, List.forall_mem_cons.2 ⟨sub7_643, List.forall_mem_cons.2 ⟨sub7_644, List.forall_mem_cons.2 ⟨sub7_645, List.forall_mem_cons.2 ⟨sub7_646, List.forall_mem_cons.2 ⟨sub7_647, List.forall_mem_cons.2 ⟨sub7_648, List.forall_mem_cons.2 ⟨sub7_649, List.forall_mem_cons.2 ⟨sub7_650, List.forall_mem_cons.2 ⟨sub7_651, List.forall_mem_cons.2 ⟨sub7_652, List.forall_mem_cons.2 ⟨sub7_653, List.forall_mem_cons.2 ⟨sub7_654, List.forall_mem_cons.2 ⟨sub7_655, List.forall_mem_cons.2 ⟨sub7_656, List.forall_mem_cons.2 ⟨sub7_657, List.forall_mem_cons.2 ⟨sub7_658, List.forall_mem_cons.2 ⟨sub7_659, List.forall_mem_cons.2 ⟨sub7_660, List.forall_mem_cons.2 ⟨sub7_661, List.forall_mem_cons.2 ⟨sub7_662, List.forall_mem_cons.2 ⟨sub7_663, List.forall_mem_cons.2 ⟨sub7_664, List.forall_mem_cons.2 ⟨sub7_665, List.forall_mem_cons.2 ⟨sub7_666, List.forall_mem_cons.2 ⟨sub7_667, List.forall_mem_cons.2 ⟨sub7_668, List.forall_mem_cons.2 ⟨sub7_669, List.forall_mem_cons.2 ⟨sub7_670, List.forall_mem_cons.2 ⟨sub7_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_672 : sub7 [1, 1, 0] = true := by decide +kernel
theorem sub7_673 : sub7 [1, 1, 1] = true := by decide +kernel
theorem sub7_674 : sub7 [1, 1, 2] = true := by decide +kernel
theorem sub7_675 : sub7 [1, 1, 3] = true := by decide +kernel
theorem sub7_676 : sub7 [1, 1, 4] = true := by decide +kernel
theorem sub7_677 : sub7 [1, 1, 5] = true := by decide +kernel
theorem sub7_678 : sub7 [1, 1, 6] = true := by decide +kernel
theorem sub7_679 : sub7 [1, 1, 7] = true := by decide +kernel
theorem sub7_680 : sub7 [1, 1, 8] = true := by decide +kernel
theorem sub7_681 : sub7 [1, 2, -8] = true := by decide +kernel
theorem sub7_682 : sub7 [1, 2, -7] = true := by decide +kernel
theorem sub7_683 : sub7 [1, 2, -6] = true := by decide +kernel
theorem sub7_684 : sub7 [1, 2, -5] = true := by decide +kernel
theorem sub7_685 : sub7 [1, 2, -4] = true := by decide +kernel
theorem sub7_686 : sub7 [1, 2, -3] = true := by decide +kernel
theorem sub7_687 : sub7 [1, 2, -2] = true := by decide +kernel
theorem sub7_688 : sub7 [1, 2, -1] = true := by decide +kernel
theorem sub7_689 : sub7 [1, 2, 0] = true := by decide +kernel
theorem sub7_690 : sub7 [1, 2, 1] = true := by decide +kernel
theorem sub7_691 : sub7 [1, 2, 2] = true := by decide +kernel
theorem sub7_692 : sub7 [1, 2, 3] = true := by decide +kernel
theorem sub7_693 : sub7 [1, 2, 4] = true := by decide +kernel
theorem sub7_694 : sub7 [1, 2, 5] = true := by decide +kernel
theorem sub7_695 : sub7 [1, 2, 6] = true := by decide +kernel
theorem sub7_696 : sub7 [1, 2, 7] = true := by decide +kernel
theorem sub7_697 : sub7 [1, 2, 8] = true := by decide +kernel
theorem sub7_698 : sub7 [1, 3, -7] = true := by decide +kernel
theorem sub7_699 : sub7 [1, 3, -6] = true := by decide +kernel
theorem sub7_700 : sub7 [1, 3, -5] = true := by decide +kernel
theorem sub7_701 : sub7 [1, 3, -4] = true := by decide +kernel
theorem sub7_702 : sub7 [1, 3, -3] = true := by decide +kernel
theorem sub7_703 : sub7 [1, 3, -2] = true := by decide +kernel
theorem sb7_21 : ∀ q ∈ blk7_21, sub7 q = true := by
  unfold blk7_21
  exact List.forall_mem_cons.2 ⟨sub7_672, List.forall_mem_cons.2 ⟨sub7_673, List.forall_mem_cons.2 ⟨sub7_674, List.forall_mem_cons.2 ⟨sub7_675, List.forall_mem_cons.2 ⟨sub7_676, List.forall_mem_cons.2 ⟨sub7_677, List.forall_mem_cons.2 ⟨sub7_678, List.forall_mem_cons.2 ⟨sub7_679, List.forall_mem_cons.2 ⟨sub7_680, List.forall_mem_cons.2 ⟨sub7_681, List.forall_mem_cons.2 ⟨sub7_682, List.forall_mem_cons.2 ⟨sub7_683, List.forall_mem_cons.2 ⟨sub7_684, List.forall_mem_cons.2 ⟨sub7_685, List.forall_mem_cons.2 ⟨sub7_686, List.forall_mem_cons.2 ⟨sub7_687, List.forall_mem_cons.2 ⟨sub7_688, List.forall_mem_cons.2 ⟨sub7_689, List.forall_mem_cons.2 ⟨sub7_690, List.forall_mem_cons.2 ⟨sub7_691, List.forall_mem_cons.2 ⟨sub7_692, List.forall_mem_cons.2 ⟨sub7_693, List.forall_mem_cons.2 ⟨sub7_694, List.forall_mem_cons.2 ⟨sub7_695, List.forall_mem_cons.2 ⟨sub7_696, List.forall_mem_cons.2 ⟨sub7_697, List.forall_mem_cons.2 ⟨sub7_698, List.forall_mem_cons.2 ⟨sub7_699, List.forall_mem_cons.2 ⟨sub7_700, List.forall_mem_cons.2 ⟨sub7_701, List.forall_mem_cons.2 ⟨sub7_702, List.forall_mem_cons.2 ⟨sub7_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_704 : sub7 [1, 3, -1] = true := by decide +kernel
theorem sub7_705 : sub7 [1, 3, 0] = true := by decide +kernel
theorem sub7_706 : sub7 [1, 3, 1] = true := by decide +kernel
theorem sub7_707 : sub7 [1, 3, 2] = true := by decide +kernel
theorem sub7_708 : sub7 [1, 3, 3] = true := by decide +kernel
theorem sub7_709 : sub7 [1, 3, 4] = true := by decide +kernel
theorem sub7_710 : sub7 [1, 3, 5] = true := by decide +kernel
theorem sub7_711 : sub7 [1, 3, 6] = true := by decide +kernel
theorem sub7_712 : sub7 [1, 3, 7] = true := by decide +kernel
theorem sub7_713 : sub7 [1, 3, 8] = true := by decide +kernel
theorem sub7_714 : sub7 [1, 4, -6] = true := by decide +kernel
theorem sub7_715 : sub7 [1, 4, -5] = true := by decide +kernel
theorem sub7_716 : sub7 [1, 4, -4] = true := by decide +kernel
theorem sub7_717 : sub7 [1, 4, -3] = true := by decide +kernel
theorem sub7_718 : sub7 [1, 4, -2] = true := by decide +kernel
theorem sub7_719 : sub7 [1, 4, -1] = true := by decide +kernel
theorem sub7_720 : sub7 [1, 4, 0] = true := by decide +kernel
theorem sub7_721 : sub7 [1, 4, 1] = true := by decide +kernel
theorem sub7_722 : sub7 [1, 4, 2] = true := by decide +kernel
theorem sub7_723 : sub7 [1, 4, 3] = true := by decide +kernel
theorem sub7_724 : sub7 [1, 4, 4] = true := by decide +kernel
theorem sub7_725 : sub7 [1, 4, 5] = true := by decide +kernel
theorem sub7_726 : sub7 [1, 4, 6] = true := by decide +kernel
theorem sub7_727 : sub7 [1, 4, 7] = true := by decide +kernel
theorem sub7_728 : sub7 [1, 5] = true := by decide +kernel
theorem sub7_729 : sub7 [1, 6] = true := by decide +kernel
theorem sub7_730 : sub7 [2, -7] = true := by decide +kernel
theorem sub7_731 : sub7 [2, -6] = true := by decide +kernel
theorem sub7_732 : sub7 [2, -5] = true := by decide +kernel
theorem sub7_733 : sub7 [2, -4] = true := by decide +kernel
theorem sub7_734 : sub7 [2, -3, -8] = true := by decide +kernel
theorem sub7_735 : sub7 [2, -3, -7] = true := by decide +kernel
theorem sb7_22 : ∀ q ∈ blk7_22, sub7 q = true := by
  unfold blk7_22
  exact List.forall_mem_cons.2 ⟨sub7_704, List.forall_mem_cons.2 ⟨sub7_705, List.forall_mem_cons.2 ⟨sub7_706, List.forall_mem_cons.2 ⟨sub7_707, List.forall_mem_cons.2 ⟨sub7_708, List.forall_mem_cons.2 ⟨sub7_709, List.forall_mem_cons.2 ⟨sub7_710, List.forall_mem_cons.2 ⟨sub7_711, List.forall_mem_cons.2 ⟨sub7_712, List.forall_mem_cons.2 ⟨sub7_713, List.forall_mem_cons.2 ⟨sub7_714, List.forall_mem_cons.2 ⟨sub7_715, List.forall_mem_cons.2 ⟨sub7_716, List.forall_mem_cons.2 ⟨sub7_717, List.forall_mem_cons.2 ⟨sub7_718, List.forall_mem_cons.2 ⟨sub7_719, List.forall_mem_cons.2 ⟨sub7_720, List.forall_mem_cons.2 ⟨sub7_721, List.forall_mem_cons.2 ⟨sub7_722, List.forall_mem_cons.2 ⟨sub7_723, List.forall_mem_cons.2 ⟨sub7_724, List.forall_mem_cons.2 ⟨sub7_725, List.forall_mem_cons.2 ⟨sub7_726, List.forall_mem_cons.2 ⟨sub7_727, List.forall_mem_cons.2 ⟨sub7_728, List.forall_mem_cons.2 ⟨sub7_729, List.forall_mem_cons.2 ⟨sub7_730, List.forall_mem_cons.2 ⟨sub7_731, List.forall_mem_cons.2 ⟨sub7_732, List.forall_mem_cons.2 ⟨sub7_733, List.forall_mem_cons.2 ⟨sub7_734, List.forall_mem_cons.2 ⟨sub7_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_736 : sub7 [2, -3, -6] = true := by decide +kernel
theorem sub7_737 : sub7 [2, -3, -5] = true := by decide +kernel
theorem sub7_738 : sub7 [2, -3, -4] = true := by decide +kernel
theorem sub7_739 : sub7 [2, -3, -3] = true := by decide +kernel
theorem sub7_740 : sub7 [2, -3, -2] = true := by decide +kernel
theorem sub7_741 : sub7 [2, -3, -1] = true := by decide +kernel
theorem sub7_742 : sub7 [2, -3, 0] = true := by decide +kernel
theorem sub7_743 : sub7 [2, -3, 1] = true := by decide +kernel
theorem sub7_744 : sub7 [2, -3, 2] = true := by decide +kernel
theorem sub7_745 : sub7 [2, -3, 3] = true := by decide +kernel
theorem sub7_746 : sub7 [2, -3, 4] = true := by decide +kernel
theorem sub7_747 : sub7 [2, -3, 5] = true := by decide +kernel
theorem sub7_748 : sub7 [2, -3, 6] = true := by decide +kernel
theorem sub7_749 : sub7 [2, -3, 7] = true := by decide +kernel
theorem sub7_750 : sub7 [2, -2, -8] = true := by decide +kernel
theorem sub7_751 : sub7 [2, -2, -7] = true := by decide +kernel
theorem sub7_752 : sub7 [2, -2, -6] = true := by decide +kernel
theorem sub7_753 : sub7 [2, -2, -5] = true := by decide +kernel
theorem sub7_754 : sub7 [2, -2, -4] = true := by decide +kernel
theorem sub7_755 : sub7 [2, -2, -3] = true := by decide +kernel
theorem sub7_756 : sub7 [2, -2, -2] = true := by decide +kernel
theorem sub7_757 : sub7 [2, -2, -1] = true := by decide +kernel
theorem sub7_758 : sub7 [2, -2, 0] = true := by decide +kernel
theorem sub7_759 : sub7 [2, -2, 1] = true := by decide +kernel
theorem sub7_760 : sub7 [2, -2, 2] = true := by decide +kernel
theorem sub7_761 : sub7 [2, -2, 3] = true := by decide +kernel
theorem sub7_762 : sub7 [2, -2, 4] = true := by decide +kernel
theorem sub7_763 : sub7 [2, -2, 5] = true := by decide +kernel
theorem sub7_764 : sub7 [2, -2, 6] = true := by decide +kernel
theorem sub7_765 : sub7 [2, -2, 7] = true := by decide +kernel
theorem sub7_766 : sub7 [2, -1, -8] = true := by decide +kernel
theorem sub7_767 : sub7 [2, -1, -7] = true := by decide +kernel
theorem sb7_23 : ∀ q ∈ blk7_23, sub7 q = true := by
  unfold blk7_23
  exact List.forall_mem_cons.2 ⟨sub7_736, List.forall_mem_cons.2 ⟨sub7_737, List.forall_mem_cons.2 ⟨sub7_738, List.forall_mem_cons.2 ⟨sub7_739, List.forall_mem_cons.2 ⟨sub7_740, List.forall_mem_cons.2 ⟨sub7_741, List.forall_mem_cons.2 ⟨sub7_742, List.forall_mem_cons.2 ⟨sub7_743, List.forall_mem_cons.2 ⟨sub7_744, List.forall_mem_cons.2 ⟨sub7_745, List.forall_mem_cons.2 ⟨sub7_746, List.forall_mem_cons.2 ⟨sub7_747, List.forall_mem_cons.2 ⟨sub7_748, List.forall_mem_cons.2 ⟨sub7_749, List.forall_mem_cons.2 ⟨sub7_750, List.forall_mem_cons.2 ⟨sub7_751, List.forall_mem_cons.2 ⟨sub7_752, List.forall_mem_cons.2 ⟨sub7_753, List.forall_mem_cons.2 ⟨sub7_754, List.forall_mem_cons.2 ⟨sub7_755, List.forall_mem_cons.2 ⟨sub7_756, List.forall_mem_cons.2 ⟨sub7_757, List.forall_mem_cons.2 ⟨sub7_758, List.forall_mem_cons.2 ⟨sub7_759, List.forall_mem_cons.2 ⟨sub7_760, List.forall_mem_cons.2 ⟨sub7_761, List.forall_mem_cons.2 ⟨sub7_762, List.forall_mem_cons.2 ⟨sub7_763, List.forall_mem_cons.2 ⟨sub7_764, List.forall_mem_cons.2 ⟨sub7_765, List.forall_mem_cons.2 ⟨sub7_766, List.forall_mem_cons.2 ⟨sub7_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_768 : sub7 [2, -1, -6] = true := by decide +kernel
theorem sub7_769 : sub7 [2, -1, -5] = true := by decide +kernel
theorem sub7_770 : sub7 [2, -1, -4] = true := by decide +kernel
theorem sub7_771 : sub7 [2, -1, -3] = true := by decide +kernel
theorem sub7_772 : sub7 [2, -1, -2] = true := by decide +kernel
theorem sub7_773 : sub7 [2, -1, -1] = true := by decide +kernel
theorem sub7_774 : sub7 [2, -1, 0] = true := by decide +kernel
theorem sub7_775 : sub7 [2, -1, 1] = true := by decide +kernel
theorem sub7_776 : sub7 [2, -1, 2] = true := by decide +kernel
theorem sub7_777 : sub7 [2, -1, 3] = true := by decide +kernel
theorem sub7_778 : sub7 [2, -1, 4] = true := by decide +kernel
theorem sub7_779 : sub7 [2, -1, 5] = true := by decide +kernel
theorem sub7_780 : sub7 [2, -1, 6] = true := by decide +kernel
theorem sub7_781 : sub7 [2, -1, 7] = true := by decide +kernel
theorem sub7_782 : sub7 [2, -1, 8] = true := by decide +kernel
theorem sub7_783 : sub7 [2, 0, -8] = true := by decide +kernel
theorem sub7_784 : sub7 [2, 0, -7] = true := by decide +kernel
theorem sub7_785 : sub7 [2, 0, -6] = true := by decide +kernel
theorem sub7_786 : sub7 [2, 0, -5] = true := by decide +kernel
theorem sub7_787 : sub7 [2, 0, -4] = true := by decide +kernel
theorem sub7_788 : sub7 [2, 0, -3] = true := by decide +kernel
theorem sub7_789 : sub7 [2, 0, -2] = true := by decide +kernel
theorem sub7_790 : sub7 [2, 0, -1] = true := by decide +kernel
theorem sub7_791 : sub7 [2, 0, 0] = true := by decide +kernel
theorem sub7_792 : sub7 [2, 0, 1] = true := by decide +kernel
theorem sub7_793 : sub7 [2, 0, 2] = true := by decide +kernel
theorem sub7_794 : sub7 [2, 0, 3] = true := by decide +kernel
theorem sub7_795 : sub7 [2, 0, 4] = true := by decide +kernel
theorem sub7_796 : sub7 [2, 0, 5] = true := by decide +kernel
theorem sub7_797 : sub7 [2, 0, 6] = true := by decide +kernel
theorem sub7_798 : sub7 [2, 0, 7] = true := by decide +kernel
theorem sub7_799 : sub7 [2, 0, 8] = true := by decide +kernel
theorem sb7_24 : ∀ q ∈ blk7_24, sub7 q = true := by
  unfold blk7_24
  exact List.forall_mem_cons.2 ⟨sub7_768, List.forall_mem_cons.2 ⟨sub7_769, List.forall_mem_cons.2 ⟨sub7_770, List.forall_mem_cons.2 ⟨sub7_771, List.forall_mem_cons.2 ⟨sub7_772, List.forall_mem_cons.2 ⟨sub7_773, List.forall_mem_cons.2 ⟨sub7_774, List.forall_mem_cons.2 ⟨sub7_775, List.forall_mem_cons.2 ⟨sub7_776, List.forall_mem_cons.2 ⟨sub7_777, List.forall_mem_cons.2 ⟨sub7_778, List.forall_mem_cons.2 ⟨sub7_779, List.forall_mem_cons.2 ⟨sub7_780, List.forall_mem_cons.2 ⟨sub7_781, List.forall_mem_cons.2 ⟨sub7_782, List.forall_mem_cons.2 ⟨sub7_783, List.forall_mem_cons.2 ⟨sub7_784, List.forall_mem_cons.2 ⟨sub7_785, List.forall_mem_cons.2 ⟨sub7_786, List.forall_mem_cons.2 ⟨sub7_787, List.forall_mem_cons.2 ⟨sub7_788, List.forall_mem_cons.2 ⟨sub7_789, List.forall_mem_cons.2 ⟨sub7_790, List.forall_mem_cons.2 ⟨sub7_791, List.forall_mem_cons.2 ⟨sub7_792, List.forall_mem_cons.2 ⟨sub7_793, List.forall_mem_cons.2 ⟨sub7_794, List.forall_mem_cons.2 ⟨sub7_795, List.forall_mem_cons.2 ⟨sub7_796, List.forall_mem_cons.2 ⟨sub7_797, List.forall_mem_cons.2 ⟨sub7_798, List.forall_mem_cons.2 ⟨sub7_799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_800 : sub7 [2, 1, -8] = true := by decide +kernel
theorem sub7_801 : sub7 [2, 1, -7] = true := by decide +kernel
theorem sub7_802 : sub7 [2, 1, -6] = true := by decide +kernel
theorem sub7_803 : sub7 [2, 1, -5] = true := by decide +kernel
theorem sub7_804 : sub7 [2, 1, -4] = true := by decide +kernel
theorem sub7_805 : sub7 [2, 1, -3] = true := by decide +kernel
theorem sub7_806 : sub7 [2, 1, -2] = true := by decide +kernel
theorem sub7_807 : sub7 [2, 1, -1] = true := by decide +kernel
theorem sub7_808 : sub7 [2, 1, 0] = true := by decide +kernel
theorem sub7_809 : sub7 [2, 1, 1] = true := by decide +kernel
theorem sub7_810 : sub7 [2, 1, 2] = true := by decide +kernel
theorem sub7_811 : sub7 [2, 1, 3] = true := by decide +kernel
theorem sub7_812 : sub7 [2, 1, 4] = true := by decide +kernel
theorem sub7_813 : sub7 [2, 1, 5] = true := by decide +kernel
theorem sub7_814 : sub7 [2, 1, 6] = true := by decide +kernel
theorem sub7_815 : sub7 [2, 1, 7] = true := by decide +kernel
theorem sub7_816 : sub7 [2, 1, 8] = true := by decide +kernel
theorem sub7_817 : sub7 [2, 2, -7] = true := by decide +kernel
theorem sub7_818 : sub7 [2, 2, -6] = true := by decide +kernel
theorem sub7_819 : sub7 [2, 2, -5] = true := by decide +kernel
theorem sub7_820 : sub7 [2, 2, -4] = true := by decide +kernel
theorem sub7_821 : sub7 [2, 2, -3] = true := by decide +kernel
theorem sub7_822 : sub7 [2, 2, -2] = true := by decide +kernel
theorem sub7_823 : sub7 [2, 2, -1] = true := by decide +kernel
theorem sub7_824 : sub7 [2, 2, 0] = true := by decide +kernel
theorem sub7_825 : sub7 [2, 2, 1] = true := by decide +kernel
theorem sub7_826 : sub7 [2, 2, 2] = true := by decide +kernel
theorem sub7_827 : sub7 [2, 2, 3] = true := by decide +kernel
theorem sub7_828 : sub7 [2, 2, 4] = true := by decide +kernel
theorem sub7_829 : sub7 [2, 2, 5] = true := by decide +kernel
theorem sub7_830 : sub7 [2, 2, 6] = true := by decide +kernel
theorem sub7_831 : sub7 [2, 2, 7] = true := by decide +kernel
theorem sb7_25 : ∀ q ∈ blk7_25, sub7 q = true := by
  unfold blk7_25
  exact List.forall_mem_cons.2 ⟨sub7_800, List.forall_mem_cons.2 ⟨sub7_801, List.forall_mem_cons.2 ⟨sub7_802, List.forall_mem_cons.2 ⟨sub7_803, List.forall_mem_cons.2 ⟨sub7_804, List.forall_mem_cons.2 ⟨sub7_805, List.forall_mem_cons.2 ⟨sub7_806, List.forall_mem_cons.2 ⟨sub7_807, List.forall_mem_cons.2 ⟨sub7_808, List.forall_mem_cons.2 ⟨sub7_809, List.forall_mem_cons.2 ⟨sub7_810, List.forall_mem_cons.2 ⟨sub7_811, List.forall_mem_cons.2 ⟨sub7_812, List.forall_mem_cons.2 ⟨sub7_813, List.forall_mem_cons.2 ⟨sub7_814, List.forall_mem_cons.2 ⟨sub7_815, List.forall_mem_cons.2 ⟨sub7_816, List.forall_mem_cons.2 ⟨sub7_817, List.forall_mem_cons.2 ⟨sub7_818, List.forall_mem_cons.2 ⟨sub7_819, List.forall_mem_cons.2 ⟨sub7_820, List.forall_mem_cons.2 ⟨sub7_821, List.forall_mem_cons.2 ⟨sub7_822, List.forall_mem_cons.2 ⟨sub7_823, List.forall_mem_cons.2 ⟨sub7_824, List.forall_mem_cons.2 ⟨sub7_825, List.forall_mem_cons.2 ⟨sub7_826, List.forall_mem_cons.2 ⟨sub7_827, List.forall_mem_cons.2 ⟨sub7_828, List.forall_mem_cons.2 ⟨sub7_829, List.forall_mem_cons.2 ⟨sub7_830, List.forall_mem_cons.2 ⟨sub7_831, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C098
