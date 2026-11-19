import ReflectZphi.Data.Cert5.C073.Base

namespace ReflectZphi.Data.Cert5.C073
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub6_288 : sub6 [0, 3, 3] = true := by decide +kernel
theorem sub6_289 : sub6 [0, 3, 4] = true := by decide +kernel
theorem sub6_290 : sub6 [0, 4] = true := by decide +kernel
theorem sub6_291 : sub6 [0, 5] = true := by decide +kernel
theorem sub6_292 : sub6 [1, -6] = true := by decide +kernel
theorem sub6_293 : sub6 [1, -5] = true := by decide +kernel
theorem sub6_294 : sub6 [1, -4] = true := by decide +kernel
theorem sub6_295 : sub6 [1, -3] = true := by decide +kernel
theorem sub6_296 : sub6 [1, -2, -6] = true := by decide +kernel
theorem sub6_297 : sub6 [1, -2, -5] = true := by decide +kernel
theorem sub6_298 : sub6 [1, -2, -4] = true := by decide +kernel
theorem sub6_299 : sub6 [1, -2, -3] = true := by decide +kernel
theorem sub6_300 : sub6 [1, -2, -2] = true := by decide +kernel
theorem sub6_301 : sub6 [1, -2, -1] = true := by decide +kernel
theorem sub6_302 : sub6 [1, -2, 0] = true := by decide +kernel
theorem sub6_303 : sub6 [1, -2, 1] = true := by decide +kernel
theorem sub6_304 : sub6 [1, -2, 2] = true := by decide +kernel
theorem sub6_305 : sub6 [1, -2, 3] = true := by decide +kernel
theorem sub6_306 : sub6 [1, -2, 4] = true := by decide +kernel
theorem sub6_307 : sub6 [1, -2, 5] = true := by decide +kernel
theorem sub6_308 : sub6 [1, -2, 6] = true := by decide +kernel
theorem sub6_309 : sub6 [1, -2, 7] = true := by decide +kernel
theorem sub6_310 : sub6 [1, -1, -7] = true := by decide +kernel
theorem sub6_311 : sub6 [1, -1, -6] = true := by decide +kernel
theorem sub6_312 : sub6 [1, -1, -5] = true := by decide +kernel
theorem sub6_313 : sub6 [1, -1, -4] = true := by decide +kernel
theorem sub6_314 : sub6 [1, -1, -3] = true := by decide +kernel
theorem sub6_315 : sub6 [1, -1, -2] = true := by decide +kernel
theorem sub6_316 : sub6 [1, -1, -1] = true := by decide +kernel
theorem sub6_317 : sub6 [1, -1, 0] = true := by decide +kernel
theorem sub6_318 : sub6 [1, -1, 1] = true := by decide +kernel
theorem sub6_319 : sub6 [1, -1, 2] = true := by decide +kernel
theorem sb6_9 : ∀ q ∈ blk6_9, sub6 q = true := by
  unfold blk6_9
  exact List.forall_mem_cons.2 ⟨sub6_288, List.forall_mem_cons.2 ⟨sub6_289, List.forall_mem_cons.2 ⟨sub6_290, List.forall_mem_cons.2 ⟨sub6_291, List.forall_mem_cons.2 ⟨sub6_292, List.forall_mem_cons.2 ⟨sub6_293, List.forall_mem_cons.2 ⟨sub6_294, List.forall_mem_cons.2 ⟨sub6_295, List.forall_mem_cons.2 ⟨sub6_296, List.forall_mem_cons.2 ⟨sub6_297, List.forall_mem_cons.2 ⟨sub6_298, List.forall_mem_cons.2 ⟨sub6_299, List.forall_mem_cons.2 ⟨sub6_300, List.forall_mem_cons.2 ⟨sub6_301, List.forall_mem_cons.2 ⟨sub6_302, List.forall_mem_cons.2 ⟨sub6_303, List.forall_mem_cons.2 ⟨sub6_304, List.forall_mem_cons.2 ⟨sub6_305, List.forall_mem_cons.2 ⟨sub6_306, List.forall_mem_cons.2 ⟨sub6_307, List.forall_mem_cons.2 ⟨sub6_308, List.forall_mem_cons.2 ⟨sub6_309, List.forall_mem_cons.2 ⟨sub6_310, List.forall_mem_cons.2 ⟨sub6_311, List.forall_mem_cons.2 ⟨sub6_312, List.forall_mem_cons.2 ⟨sub6_313, List.forall_mem_cons.2 ⟨sub6_314, List.forall_mem_cons.2 ⟨sub6_315, List.forall_mem_cons.2 ⟨sub6_316, List.forall_mem_cons.2 ⟨sub6_317, List.forall_mem_cons.2 ⟨sub6_318, List.forall_mem_cons.2 ⟨sub6_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_320 : sub6 [1, -1, 3] = true := by decide +kernel
theorem sub6_321 : sub6 [1, -1, 4] = true := by decide +kernel
theorem sub6_322 : sub6 [1, -1, 5] = true := by decide +kernel
theorem sub6_323 : sub6 [1, -1, 6] = true := by decide +kernel
theorem sub6_324 : sub6 [1, -1, 7] = true := by decide +kernel
theorem sub6_325 : sub6 [1, 0, -8] = true := by decide +kernel
theorem sub6_326 : sub6 [1, 0, -7] = true := by decide +kernel
theorem sub6_327 : sub6 [1, 0, -6] = true := by decide +kernel
theorem sub6_328 : sub6 [1, 0, -5] = true := by decide +kernel
theorem sub6_329 : sub6 [1, 0, -4] = true := by decide +kernel
theorem sub6_330 : sub6 [1, 0, -3] = true := by decide +kernel
theorem sub6_331 : sub6 [1, 0, -2] = true := by decide +kernel
theorem sub6_332 : sub6 [1, 0, -1] = true := by decide +kernel
theorem sub6_333 : sub6 [1, 0, 0] = true := by decide +kernel
theorem sub6_334 : sub6 [1, 0, 1] = true := by decide +kernel
theorem sub6_335 : sub6 [1, 0, 2] = true := by decide +kernel
theorem sub6_336 : sub6 [1, 0, 3] = true := by decide +kernel
theorem sub6_337 : sub6 [1, 0, 4] = true := by decide +kernel
theorem sub6_338 : sub6 [1, 0, 5] = true := by decide +kernel
theorem sub6_339 : sub6 [1, 0, 6] = true := by decide +kernel
theorem sub6_340 : sub6 [1, 0, 7] = true := by decide +kernel
theorem sub6_341 : sub6 [1, 1, -8] = true := by decide +kernel
theorem sub6_342 : sub6 [1, 1, -7] = true := by decide +kernel
theorem sub6_343 : sub6 [1, 1, -6] = true := by decide +kernel
theorem sub6_344 : sub6 [1, 1, -5] = true := by decide +kernel
theorem sub6_345 : sub6 [1, 1, -4] = true := by decide +kernel
theorem sub6_346 : sub6 [1, 1, -3] = true := by decide +kernel
theorem sub6_347 : sub6 [1, 1, -2] = true := by decide +kernel
theorem sub6_348 : sub6 [1, 1, -1] = true := by decide +kernel
theorem sub6_349 : sub6 [1, 1, 0] = true := by decide +kernel
theorem sub6_350 : sub6 [1, 1, 1] = true := by decide +kernel
theorem sub6_351 : sub6 [1, 1, 2] = true := by decide +kernel
theorem sb6_10 : ∀ q ∈ blk6_10, sub6 q = true := by
  unfold blk6_10
  exact List.forall_mem_cons.2 ⟨sub6_320, List.forall_mem_cons.2 ⟨sub6_321, List.forall_mem_cons.2 ⟨sub6_322, List.forall_mem_cons.2 ⟨sub6_323, List.forall_mem_cons.2 ⟨sub6_324, List.forall_mem_cons.2 ⟨sub6_325, List.forall_mem_cons.2 ⟨sub6_326, List.forall_mem_cons.2 ⟨sub6_327, List.forall_mem_cons.2 ⟨sub6_328, List.forall_mem_cons.2 ⟨sub6_329, List.forall_mem_cons.2 ⟨sub6_330, List.forall_mem_cons.2 ⟨sub6_331, List.forall_mem_cons.2 ⟨sub6_332, List.forall_mem_cons.2 ⟨sub6_333, List.forall_mem_cons.2 ⟨sub6_334, List.forall_mem_cons.2 ⟨sub6_335, List.forall_mem_cons.2 ⟨sub6_336, List.forall_mem_cons.2 ⟨sub6_337, List.forall_mem_cons.2 ⟨sub6_338, List.forall_mem_cons.2 ⟨sub6_339, List.forall_mem_cons.2 ⟨sub6_340, List.forall_mem_cons.2 ⟨sub6_341, List.forall_mem_cons.2 ⟨sub6_342, List.forall_mem_cons.2 ⟨sub6_343, List.forall_mem_cons.2 ⟨sub6_344, List.forall_mem_cons.2 ⟨sub6_345, List.forall_mem_cons.2 ⟨sub6_346, List.forall_mem_cons.2 ⟨sub6_347, List.forall_mem_cons.2 ⟨sub6_348, List.forall_mem_cons.2 ⟨sub6_349, List.forall_mem_cons.2 ⟨sub6_350, List.forall_mem_cons.2 ⟨sub6_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_352 : sub6 [1, 1, 3] = true := by decide +kernel
theorem sub6_353 : sub6 [1, 1, 4] = true := by decide +kernel
theorem sub6_354 : sub6 [1, 1, 5] = true := by decide +kernel
theorem sub6_355 : sub6 [1, 1, 6] = true := by decide +kernel
theorem sub6_356 : sub6 [1, 2, -8] = true := by decide +kernel
theorem sub6_357 : sub6 [1, 2, -7] = true := by decide +kernel
theorem sub6_358 : sub6 [1, 2, -6] = true := by decide +kernel
theorem sub6_359 : sub6 [1, 2, -5] = true := by decide +kernel
theorem sub6_360 : sub6 [1, 2, -4] = true := by decide +kernel
theorem sub6_361 : sub6 [1, 2, -3] = true := by decide +kernel
theorem sub6_362 : sub6 [1, 2, -2] = true := by decide +kernel
theorem sub6_363 : sub6 [1, 2, -1] = true := by decide +kernel
theorem sub6_364 : sub6 [1, 2, 0] = true := by decide +kernel
theorem sub6_365 : sub6 [1, 2, 1] = true := by decide +kernel
theorem sub6_366 : sub6 [1, 2, 2] = true := by decide +kernel
theorem sub6_367 : sub6 [1, 2, 3] = true := by decide +kernel
theorem sub6_368 : sub6 [1, 2, 4] = true := by decide +kernel
theorem sub6_369 : sub6 [1, 2, 5] = true := by decide +kernel
theorem sub6_370 : sub6 [1, 3] = true := by decide +kernel
theorem sub6_371 : sub6 [1, 4] = true := by decide +kernel
theorem sub6_372 : sub6 [1, 5] = true := by decide +kernel
theorem sub6_373 : sub6 [2, -6] = true := by decide +kernel
theorem sub6_374 : sub6 [2, -5] = true := by decide +kernel
theorem sub6_375 : sub6 [2, -4] = true := by decide +kernel
theorem sub6_376 : sub6 [2, -3] = true := by decide +kernel
theorem sub6_377 : sub6 [2, -2, -6] = true := by decide +kernel
theorem sub6_378 : sub6 [2, -2, -5] = true := by decide +kernel
theorem sub6_379 : sub6 [2, -2, -4] = true := by decide +kernel
theorem sub6_380 : sub6 [2, -2, -3] = true := by decide +kernel
theorem sub6_381 : sub6 [2, -2, -2] = true := by decide +kernel
theorem sub6_382 : sub6 [2, -2, -1] = true := by decide +kernel
theorem sub6_383 : sub6 [2, -2, 0] = true := by decide +kernel
theorem sb6_11 : ∀ q ∈ blk6_11, sub6 q = true := by
  unfold blk6_11
  exact List.forall_mem_cons.2 ⟨sub6_352, List.forall_mem_cons.2 ⟨sub6_353, List.forall_mem_cons.2 ⟨sub6_354, List.forall_mem_cons.2 ⟨sub6_355, List.forall_mem_cons.2 ⟨sub6_356, List.forall_mem_cons.2 ⟨sub6_357, List.forall_mem_cons.2 ⟨sub6_358, List.forall_mem_cons.2 ⟨sub6_359, List.forall_mem_cons.2 ⟨sub6_360, List.forall_mem_cons.2 ⟨sub6_361, List.forall_mem_cons.2 ⟨sub6_362, List.forall_mem_cons.2 ⟨sub6_363, List.forall_mem_cons.2 ⟨sub6_364, List.forall_mem_cons.2 ⟨sub6_365, List.forall_mem_cons.2 ⟨sub6_366, List.forall_mem_cons.2 ⟨sub6_367, List.forall_mem_cons.2 ⟨sub6_368, List.forall_mem_cons.2 ⟨sub6_369, List.forall_mem_cons.2 ⟨sub6_370, List.forall_mem_cons.2 ⟨sub6_371, List.forall_mem_cons.2 ⟨sub6_372, List.forall_mem_cons.2 ⟨sub6_373, List.forall_mem_cons.2 ⟨sub6_374, List.forall_mem_cons.2 ⟨sub6_375, List.forall_mem_cons.2 ⟨sub6_376, List.forall_mem_cons.2 ⟨sub6_377, List.forall_mem_cons.2 ⟨sub6_378, List.forall_mem_cons.2 ⟨sub6_379, List.forall_mem_cons.2 ⟨sub6_380, List.forall_mem_cons.2 ⟨sub6_381, List.forall_mem_cons.2 ⟨sub6_382, List.forall_mem_cons.2 ⟨sub6_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_384 : sub6 [2, -2, 1] = true := by decide +kernel
theorem sub6_385 : sub6 [2, -2, 2] = true := by decide +kernel
theorem sub6_386 : sub6 [2, -2, 3] = true := by decide +kernel
theorem sub6_387 : sub6 [2, -2, 4] = true := by decide +kernel
theorem sub6_388 : sub6 [2, -2, 5] = true := by decide +kernel
theorem sub6_389 : sub6 [2, -2, 6] = true := by decide +kernel
theorem sub6_390 : sub6 [2, -2, 7] = true := by decide +kernel
theorem sub6_391 : sub6 [2, -1, -7] = true := by decide +kernel
theorem sub6_392 : sub6 [2, -1, -6] = true := by decide +kernel
theorem sub6_393 : sub6 [2, -1, -5] = true := by decide +kernel
theorem sub6_394 : sub6 [2, -1, -4] = true := by decide +kernel
theorem sub6_395 : sub6 [2, -1, -3] = true := by decide +kernel
theorem sub6_396 : sub6 [2, -1, -2] = true := by decide +kernel
theorem sub6_397 : sub6 [2, -1, -1] = true := by decide +kernel
theorem sub6_398 : sub6 [2, -1, 0] = true := by decide +kernel
theorem sub6_399 : sub6 [2, -1, 1] = true := by decide +kernel
theorem sub6_400 : sub6 [2, -1, 2] = true := by decide +kernel
theorem sub6_401 : sub6 [2, -1, 3] = true := by decide +kernel
theorem sub6_402 : sub6 [2, -1, 4] = true := by decide +kernel
theorem sub6_403 : sub6 [2, -1, 5] = true := by decide +kernel
theorem sub6_404 : sub6 [2, -1, 6] = true := by decide +kernel
theorem sub6_405 : sub6 [2, -1, 7] = true := by decide +kernel
theorem sub6_406 : sub6 [2, 0, -7] = true := by decide +kernel
theorem sub6_407 : sub6 [2, 0, -6] = true := by decide +kernel
theorem sub6_408 : sub6 [2, 0, -5] = true := by decide +kernel
theorem sub6_409 : sub6 [2, 0, -4] = true := by decide +kernel
theorem sub6_410 : sub6 [2, 0, -3] = true := by decide +kernel
theorem sub6_411 : sub6 [2, 0, -2] = true := by decide +kernel
theorem sub6_412 : sub6 [2, 0, -1] = true := by decide +kernel
theorem sub6_413 : sub6 [2, 0, 0] = true := by decide +kernel
theorem sub6_414 : sub6 [2, 0, 1] = true := by decide +kernel
theorem sub6_415 : sub6 [2, 0, 2] = true := by decide +kernel
theorem sb6_12 : ∀ q ∈ blk6_12, sub6 q = true := by
  unfold blk6_12
  exact List.forall_mem_cons.2 ⟨sub6_384, List.forall_mem_cons.2 ⟨sub6_385, List.forall_mem_cons.2 ⟨sub6_386, List.forall_mem_cons.2 ⟨sub6_387, List.forall_mem_cons.2 ⟨sub6_388, List.forall_mem_cons.2 ⟨sub6_389, List.forall_mem_cons.2 ⟨sub6_390, List.forall_mem_cons.2 ⟨sub6_391, List.forall_mem_cons.2 ⟨sub6_392, List.forall_mem_cons.2 ⟨sub6_393, List.forall_mem_cons.2 ⟨sub6_394, List.forall_mem_cons.2 ⟨sub6_395, List.forall_mem_cons.2 ⟨sub6_396, List.forall_mem_cons.2 ⟨sub6_397, List.forall_mem_cons.2 ⟨sub6_398, List.forall_mem_cons.2 ⟨sub6_399, List.forall_mem_cons.2 ⟨sub6_400, List.forall_mem_cons.2 ⟨sub6_401, List.forall_mem_cons.2 ⟨sub6_402, List.forall_mem_cons.2 ⟨sub6_403, List.forall_mem_cons.2 ⟨sub6_404, List.forall_mem_cons.2 ⟨sub6_405, List.forall_mem_cons.2 ⟨sub6_406, List.forall_mem_cons.2 ⟨sub6_407, List.forall_mem_cons.2 ⟨sub6_408, List.forall_mem_cons.2 ⟨sub6_409, List.forall_mem_cons.2 ⟨sub6_410, List.forall_mem_cons.2 ⟨sub6_411, List.forall_mem_cons.2 ⟨sub6_412, List.forall_mem_cons.2 ⟨sub6_413, List.forall_mem_cons.2 ⟨sub6_414, List.forall_mem_cons.2 ⟨sub6_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_416 : sub6 [2, 0, 3] = true := by decide +kernel
theorem sub6_417 : sub6 [2, 0, 4] = true := by decide +kernel
theorem sub6_418 : sub6 [2, 0, 5] = true := by decide +kernel
theorem sub6_419 : sub6 [2, 0, 6] = true := by decide +kernel
theorem sub6_420 : sub6 [2, 0, 7] = true := by decide +kernel
theorem sub6_421 : sub6 [2, 1, -7] = true := by decide +kernel
theorem sub6_422 : sub6 [2, 1, -6] = true := by decide +kernel
theorem sub6_423 : sub6 [2, 1, -5] = true := by decide +kernel
theorem sub6_424 : sub6 [2, 1, -4] = true := by decide +kernel
theorem sub6_425 : sub6 [2, 1, -3] = true := by decide +kernel
theorem sub6_426 : sub6 [2, 1, -2] = true := by decide +kernel
theorem sub6_427 : sub6 [2, 1, -1] = true := by decide +kernel
theorem sub6_428 : sub6 [2, 1, 0] = true := by decide +kernel
theorem sub6_429 : sub6 [2, 1, 1] = true := by decide +kernel
theorem sub6_430 : sub6 [2, 1, 2] = true := by decide +kernel
theorem sub6_431 : sub6 [2, 1, 3] = true := by decide +kernel
theorem sub6_432 : sub6 [2, 1, 4] = true := by decide +kernel
theorem sub6_433 : sub6 [2, 1, 5] = true := by decide +kernel
theorem sub6_434 : sub6 [2, 1, 6] = true := by decide +kernel
theorem sub6_435 : sub6 [2, 2, -7] = true := by decide +kernel
theorem sub6_436 : sub6 [2, 2, -6] = true := by decide +kernel
theorem sub6_437 : sub6 [2, 2, -5] = true := by decide +kernel
theorem sub6_438 : sub6 [2, 2, -4] = true := by decide +kernel
theorem sub6_439 : sub6 [2, 2, -3] = true := by decide +kernel
theorem sub6_440 : sub6 [2, 2, -2] = true := by decide +kernel
theorem sub6_441 : sub6 [2, 2, -1] = true := by decide +kernel
theorem sub6_442 : sub6 [2, 2, 0] = true := by decide +kernel
theorem sub6_443 : sub6 [2, 2, 1] = true := by decide +kernel
theorem sub6_444 : sub6 [2, 2, 2] = true := by decide +kernel
theorem sub6_445 : sub6 [2, 2, 3] = true := by decide +kernel
theorem sub6_446 : sub6 [2, 2, 4] = true := by decide +kernel
theorem sub6_447 : sub6 [2, 2, 5] = true := by decide +kernel
theorem sb6_13 : ∀ q ∈ blk6_13, sub6 q = true := by
  unfold blk6_13
  exact List.forall_mem_cons.2 ⟨sub6_416, List.forall_mem_cons.2 ⟨sub6_417, List.forall_mem_cons.2 ⟨sub6_418, List.forall_mem_cons.2 ⟨sub6_419, List.forall_mem_cons.2 ⟨sub6_420, List.forall_mem_cons.2 ⟨sub6_421, List.forall_mem_cons.2 ⟨sub6_422, List.forall_mem_cons.2 ⟨sub6_423, List.forall_mem_cons.2 ⟨sub6_424, List.forall_mem_cons.2 ⟨sub6_425, List.forall_mem_cons.2 ⟨sub6_426, List.forall_mem_cons.2 ⟨sub6_427, List.forall_mem_cons.2 ⟨sub6_428, List.forall_mem_cons.2 ⟨sub6_429, List.forall_mem_cons.2 ⟨sub6_430, List.forall_mem_cons.2 ⟨sub6_431, List.forall_mem_cons.2 ⟨sub6_432, List.forall_mem_cons.2 ⟨sub6_433, List.forall_mem_cons.2 ⟨sub6_434, List.forall_mem_cons.2 ⟨sub6_435, List.forall_mem_cons.2 ⟨sub6_436, List.forall_mem_cons.2 ⟨sub6_437, List.forall_mem_cons.2 ⟨sub6_438, List.forall_mem_cons.2 ⟨sub6_439, List.forall_mem_cons.2 ⟨sub6_440, List.forall_mem_cons.2 ⟨sub6_441, List.forall_mem_cons.2 ⟨sub6_442, List.forall_mem_cons.2 ⟨sub6_443, List.forall_mem_cons.2 ⟨sub6_444, List.forall_mem_cons.2 ⟨sub6_445, List.forall_mem_cons.2 ⟨sub6_446, List.forall_mem_cons.2 ⟨sub6_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_448 : sub6 [2, 3] = true := by decide +kernel
theorem sub6_449 : sub6 [2, 4] = true := by decide +kernel
theorem sub6_450 : sub6 [2, 5] = true := by decide +kernel
theorem sub6_451 : sub6 [3, -5] = true := by decide +kernel
theorem sub6_452 : sub6 [3, -4] = true := by decide +kernel
theorem sub6_453 : sub6 [3, -3] = true := by decide +kernel
theorem sub6_454 : sub6 [3, -2] = true := by decide +kernel
theorem sub6_455 : sub6 [3, -1] = true := by decide +kernel
theorem sub6_456 : sub6 [3, 0] = true := by decide +kernel
theorem sub6_457 : sub6 [3, 1] = true := by decide +kernel
theorem sub6_458 : sub6 [3, 2] = true := by decide +kernel
theorem sub6_459 : sub6 [3, 3] = true := by decide +kernel
theorem sub6_460 : sub6 [3, 4] = true := by decide +kernel
theorem sub6_461 : sub6 [4, -5] = true := by decide +kernel
theorem sub6_462 : sub6 [4, -4] = true := by decide +kernel
theorem sub6_463 : sub6 [4, -3] = true := by decide +kernel
theorem sub6_464 : sub6 [4, -2] = true := by decide +kernel
theorem sub6_465 : sub6 [4, -1] = true := by decide +kernel
theorem sub6_466 : sub6 [4, 0] = true := by decide +kernel
theorem sub6_467 : sub6 [4, 1] = true := by decide +kernel
theorem sub6_468 : sub6 [4, 2] = true := by decide +kernel
theorem sub6_469 : sub6 [4, 3] = true := by decide +kernel
theorem sub6_470 : sub6 [4, 4] = true := by decide +kernel
theorem sub6_471 : sub6 [5, -3] = true := by decide +kernel
theorem sub6_472 : sub6 [5, -2] = true := by decide +kernel
theorem sub6_473 : sub6 [5, -1] = true := by decide +kernel
theorem sub6_474 : sub6 [5, 0] = true := by decide +kernel
theorem sub6_475 : sub6 [5, 1] = true := by decide +kernel
theorem sub6_476 : sub6 [5, 2] = true := by decide +kernel
theorem sb6_14 : ∀ q ∈ blk6_14, sub6 q = true := by
  unfold blk6_14
  exact List.forall_mem_cons.2 ⟨sub6_448, List.forall_mem_cons.2 ⟨sub6_449, List.forall_mem_cons.2 ⟨sub6_450, List.forall_mem_cons.2 ⟨sub6_451, List.forall_mem_cons.2 ⟨sub6_452, List.forall_mem_cons.2 ⟨sub6_453, List.forall_mem_cons.2 ⟨sub6_454, List.forall_mem_cons.2 ⟨sub6_455, List.forall_mem_cons.2 ⟨sub6_456, List.forall_mem_cons.2 ⟨sub6_457, List.forall_mem_cons.2 ⟨sub6_458, List.forall_mem_cons.2 ⟨sub6_459, List.forall_mem_cons.2 ⟨sub6_460, List.forall_mem_cons.2 ⟨sub6_461, List.forall_mem_cons.2 ⟨sub6_462, List.forall_mem_cons.2 ⟨sub6_463, List.forall_mem_cons.2 ⟨sub6_464, List.forall_mem_cons.2 ⟨sub6_465, List.forall_mem_cons.2 ⟨sub6_466, List.forall_mem_cons.2 ⟨sub6_467, List.forall_mem_cons.2 ⟨sub6_468, List.forall_mem_cons.2 ⟨sub6_469, List.forall_mem_cons.2 ⟨sub6_470, List.forall_mem_cons.2 ⟨sub6_471, List.forall_mem_cons.2 ⟨sub6_472, List.forall_mem_cons.2 ⟨sub6_473, List.forall_mem_cons.2 ⟨sub6_474, List.forall_mem_cons.2 ⟨sub6_475, List.forall_mem_cons.2 ⟨sub6_476, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C073
