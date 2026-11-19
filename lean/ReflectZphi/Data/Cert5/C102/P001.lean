import ReflectZphi.Data.Cert5.C102.Base

namespace ReflectZphi.Data.Cert5.C102
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub2_288 : sub2 [1, -5] = true := by decide +kernel
theorem sub2_289 : sub2 [1, -4] = true := by decide +kernel
theorem sub2_290 : sub2 [1, -3] = true := by decide +kernel
theorem sub2_291 : sub2 [1, -2, -9] = true := by decide +kernel
theorem sub2_292 : sub2 [1, -2, -8] = true := by decide +kernel
theorem sub2_293 : sub2 [1, -2, -7] = true := by decide +kernel
theorem sub2_294 : sub2 [1, -2, -6] = true := by decide +kernel
theorem sub2_295 : sub2 [1, -2, -5] = true := by decide +kernel
theorem sub2_296 : sub2 [1, -2, -4] = true := by decide +kernel
theorem sub2_297 : sub2 [1, -2, -3] = true := by decide +kernel
theorem sub2_298 : sub2 [1, -2, -2] = true := by decide +kernel
theorem sub2_299 : sub2 [1, -2, -1] = true := by decide +kernel
theorem sub2_300 : sub2 [1, -2, 0] = true := by decide +kernel
theorem sub2_301 : sub2 [1, -2, 1] = true := by decide +kernel
theorem sub2_302 : sub2 [1, -2, 2] = true := by decide +kernel
theorem sub2_303 : sub2 [1, -2, 3] = true := by decide +kernel
theorem sub2_304 : sub2 [1, -2, 4] = true := by decide +kernel
theorem sub2_305 : sub2 [1, -2, 5] = true := by decide +kernel
theorem sub2_306 : sub2 [1, -2, 6] = true := by decide +kernel
theorem sub2_307 : sub2 [1, -1, -9] = true := by decide +kernel
theorem sub2_308 : sub2 [1, -1, -8] = true := by decide +kernel
theorem sub2_309 : sub2 [1, -1, -7] = true := by decide +kernel
theorem sub2_310 : sub2 [1, -1, -6] = true := by decide +kernel
theorem sub2_311 : sub2 [1, -1, -5] = true := by decide +kernel
theorem sub2_312 : sub2 [1, -1, -4] = true := by decide +kernel
theorem sub2_313 : sub2 [1, -1, -3] = true := by decide +kernel
theorem sub2_314 : sub2 [1, -1, -2] = true := by decide +kernel
theorem sub2_315 : sub2 [1, -1, -1] = true := by decide +kernel
theorem sub2_316 : sub2 [1, -1, 0] = true := by decide +kernel
theorem sub2_317 : sub2 [1, -1, 1] = true := by decide +kernel
theorem sub2_318 : sub2 [1, -1, 2] = true := by decide +kernel
theorem sub2_319 : sub2 [1, -1, 3] = true := by decide +kernel
theorem sb2_9 : ∀ q ∈ blk2_9, sub2 q = true := by
  unfold blk2_9
  exact List.forall_mem_cons.2 ⟨sub2_288, List.forall_mem_cons.2 ⟨sub2_289, List.forall_mem_cons.2 ⟨sub2_290, List.forall_mem_cons.2 ⟨sub2_291, List.forall_mem_cons.2 ⟨sub2_292, List.forall_mem_cons.2 ⟨sub2_293, List.forall_mem_cons.2 ⟨sub2_294, List.forall_mem_cons.2 ⟨sub2_295, List.forall_mem_cons.2 ⟨sub2_296, List.forall_mem_cons.2 ⟨sub2_297, List.forall_mem_cons.2 ⟨sub2_298, List.forall_mem_cons.2 ⟨sub2_299, List.forall_mem_cons.2 ⟨sub2_300, List.forall_mem_cons.2 ⟨sub2_301, List.forall_mem_cons.2 ⟨sub2_302, List.forall_mem_cons.2 ⟨sub2_303, List.forall_mem_cons.2 ⟨sub2_304, List.forall_mem_cons.2 ⟨sub2_305, List.forall_mem_cons.2 ⟨sub2_306, List.forall_mem_cons.2 ⟨sub2_307, List.forall_mem_cons.2 ⟨sub2_308, List.forall_mem_cons.2 ⟨sub2_309, List.forall_mem_cons.2 ⟨sub2_310, List.forall_mem_cons.2 ⟨sub2_311, List.forall_mem_cons.2 ⟨sub2_312, List.forall_mem_cons.2 ⟨sub2_313, List.forall_mem_cons.2 ⟨sub2_314, List.forall_mem_cons.2 ⟨sub2_315, List.forall_mem_cons.2 ⟨sub2_316, List.forall_mem_cons.2 ⟨sub2_317, List.forall_mem_cons.2 ⟨sub2_318, List.forall_mem_cons.2 ⟨sub2_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_320 : sub2 [1, -1, 4] = true := by decide +kernel
theorem sub2_321 : sub2 [1, -1, 5] = true := by decide +kernel
theorem sub2_322 : sub2 [1, -1, 6] = true := by decide +kernel
theorem sub2_323 : sub2 [1, -1, 7] = true := by decide +kernel
theorem sub2_324 : sub2 [1, 0, -9] = true := by decide +kernel
theorem sub2_325 : sub2 [1, 0, -8] = true := by decide +kernel
theorem sub2_326 : sub2 [1, 0, -7] = true := by decide +kernel
theorem sub2_327 : sub2 [1, 0, -6] = true := by decide +kernel
theorem sub2_328 : sub2 [1, 0, -5] = true := by decide +kernel
theorem sub2_329 : sub2 [1, 0, -4] = true := by decide +kernel
theorem sub2_330 : sub2 [1, 0, -3] = true := by decide +kernel
theorem sub2_331 : sub2 [1, 0, -2] = true := by decide +kernel
theorem sub2_332 : sub2 [1, 0, -1] = true := by decide +kernel
theorem sub2_333 : sub2 [1, 0, 0] = true := by decide +kernel
theorem sub2_334 : sub2 [1, 0, 1] = true := by decide +kernel
theorem sub2_335 : sub2 [1, 0, 2] = true := by decide +kernel
theorem sub2_336 : sub2 [1, 0, 3] = true := by decide +kernel
theorem sub2_337 : sub2 [1, 0, 4] = true := by decide +kernel
theorem sub2_338 : sub2 [1, 0, 5] = true := by decide +kernel
theorem sub2_339 : sub2 [1, 0, 6] = true := by decide +kernel
theorem sub2_340 : sub2 [1, 0, 7] = true := by decide +kernel
theorem sub2_341 : sub2 [1, 0, 8] = true := by decide +kernel
theorem sub2_342 : sub2 [1, 1, -8] = true := by decide +kernel
theorem sub2_343 : sub2 [1, 1, -7] = true := by decide +kernel
theorem sub2_344 : sub2 [1, 1, -6] = true := by decide +kernel
theorem sub2_345 : sub2 [1, 1, -5] = true := by decide +kernel
theorem sub2_346 : sub2 [1, 1, -4] = true := by decide +kernel
theorem sub2_347 : sub2 [1, 1, -3] = true := by decide +kernel
theorem sub2_348 : sub2 [1, 1, -2] = true := by decide +kernel
theorem sub2_349 : sub2 [1, 1, -1] = true := by decide +kernel
theorem sub2_350 : sub2 [1, 1, 0] = true := by decide +kernel
theorem sub2_351 : sub2 [1, 1, 1] = true := by decide +kernel
theorem sb2_10 : ∀ q ∈ blk2_10, sub2 q = true := by
  unfold blk2_10
  exact List.forall_mem_cons.2 ⟨sub2_320, List.forall_mem_cons.2 ⟨sub2_321, List.forall_mem_cons.2 ⟨sub2_322, List.forall_mem_cons.2 ⟨sub2_323, List.forall_mem_cons.2 ⟨sub2_324, List.forall_mem_cons.2 ⟨sub2_325, List.forall_mem_cons.2 ⟨sub2_326, List.forall_mem_cons.2 ⟨sub2_327, List.forall_mem_cons.2 ⟨sub2_328, List.forall_mem_cons.2 ⟨sub2_329, List.forall_mem_cons.2 ⟨sub2_330, List.forall_mem_cons.2 ⟨sub2_331, List.forall_mem_cons.2 ⟨sub2_332, List.forall_mem_cons.2 ⟨sub2_333, List.forall_mem_cons.2 ⟨sub2_334, List.forall_mem_cons.2 ⟨sub2_335, List.forall_mem_cons.2 ⟨sub2_336, List.forall_mem_cons.2 ⟨sub2_337, List.forall_mem_cons.2 ⟨sub2_338, List.forall_mem_cons.2 ⟨sub2_339, List.forall_mem_cons.2 ⟨sub2_340, List.forall_mem_cons.2 ⟨sub2_341, List.forall_mem_cons.2 ⟨sub2_342, List.forall_mem_cons.2 ⟨sub2_343, List.forall_mem_cons.2 ⟨sub2_344, List.forall_mem_cons.2 ⟨sub2_345, List.forall_mem_cons.2 ⟨sub2_346, List.forall_mem_cons.2 ⟨sub2_347, List.forall_mem_cons.2 ⟨sub2_348, List.forall_mem_cons.2 ⟨sub2_349, List.forall_mem_cons.2 ⟨sub2_350, List.forall_mem_cons.2 ⟨sub2_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_352 : sub2 [1, 1, 2] = true := by decide +kernel
theorem sub2_353 : sub2 [1, 1, 3] = true := by decide +kernel
theorem sub2_354 : sub2 [1, 1, 4] = true := by decide +kernel
theorem sub2_355 : sub2 [1, 1, 5] = true := by decide +kernel
theorem sub2_356 : sub2 [1, 1, 6] = true := by decide +kernel
theorem sub2_357 : sub2 [1, 1, 7] = true := by decide +kernel
theorem sub2_358 : sub2 [1, 1, 8] = true := by decide +kernel
theorem sub2_359 : sub2 [1, 2, -7] = true := by decide +kernel
theorem sub2_360 : sub2 [1, 2, -6] = true := by decide +kernel
theorem sub2_361 : sub2 [1, 2, -5] = true := by decide +kernel
theorem sub2_362 : sub2 [1, 2, -4] = true := by decide +kernel
theorem sub2_363 : sub2 [1, 2, -3] = true := by decide +kernel
theorem sub2_364 : sub2 [1, 2, -2] = true := by decide +kernel
theorem sub2_365 : sub2 [1, 2, -1] = true := by decide +kernel
theorem sub2_366 : sub2 [1, 2, 0] = true := by decide +kernel
theorem sub2_367 : sub2 [1, 2, 1] = true := by decide +kernel
theorem sub2_368 : sub2 [1, 2, 2] = true := by decide +kernel
theorem sub2_369 : sub2 [1, 2, 3] = true := by decide +kernel
theorem sub2_370 : sub2 [1, 2, 4] = true := by decide +kernel
theorem sub2_371 : sub2 [1, 2, 5] = true := by decide +kernel
theorem sub2_372 : sub2 [1, 2, 6] = true := by decide +kernel
theorem sub2_373 : sub2 [1, 2, 7] = true := by decide +kernel
theorem sub2_374 : sub2 [1, 2, 8] = true := by decide +kernel
theorem sub2_375 : sub2 [1, 3] = true := by decide +kernel
theorem sub2_376 : sub2 [1, 4] = true := by decide +kernel
theorem sub2_377 : sub2 [2, -5] = true := by decide +kernel
theorem sub2_378 : sub2 [2, -4] = true := by decide +kernel
theorem sub2_379 : sub2 [2, -3] = true := by decide +kernel
theorem sub2_380 : sub2 [2, -2, -8] = true := by decide +kernel
theorem sub2_381 : sub2 [2, -2, -7] = true := by decide +kernel
theorem sub2_382 : sub2 [2, -2, -6] = true := by decide +kernel
theorem sub2_383 : sub2 [2, -2, -5] = true := by decide +kernel
theorem sb2_11 : ∀ q ∈ blk2_11, sub2 q = true := by
  unfold blk2_11
  exact List.forall_mem_cons.2 ⟨sub2_352, List.forall_mem_cons.2 ⟨sub2_353, List.forall_mem_cons.2 ⟨sub2_354, List.forall_mem_cons.2 ⟨sub2_355, List.forall_mem_cons.2 ⟨sub2_356, List.forall_mem_cons.2 ⟨sub2_357, List.forall_mem_cons.2 ⟨sub2_358, List.forall_mem_cons.2 ⟨sub2_359, List.forall_mem_cons.2 ⟨sub2_360, List.forall_mem_cons.2 ⟨sub2_361, List.forall_mem_cons.2 ⟨sub2_362, List.forall_mem_cons.2 ⟨sub2_363, List.forall_mem_cons.2 ⟨sub2_364, List.forall_mem_cons.2 ⟨sub2_365, List.forall_mem_cons.2 ⟨sub2_366, List.forall_mem_cons.2 ⟨sub2_367, List.forall_mem_cons.2 ⟨sub2_368, List.forall_mem_cons.2 ⟨sub2_369, List.forall_mem_cons.2 ⟨sub2_370, List.forall_mem_cons.2 ⟨sub2_371, List.forall_mem_cons.2 ⟨sub2_372, List.forall_mem_cons.2 ⟨sub2_373, List.forall_mem_cons.2 ⟨sub2_374, List.forall_mem_cons.2 ⟨sub2_375, List.forall_mem_cons.2 ⟨sub2_376, List.forall_mem_cons.2 ⟨sub2_377, List.forall_mem_cons.2 ⟨sub2_378, List.forall_mem_cons.2 ⟨sub2_379, List.forall_mem_cons.2 ⟨sub2_380, List.forall_mem_cons.2 ⟨sub2_381, List.forall_mem_cons.2 ⟨sub2_382, List.forall_mem_cons.2 ⟨sub2_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_384 : sub2 [2, -2, -4] = true := by decide +kernel
theorem sub2_385 : sub2 [2, -2, -3] = true := by decide +kernel
theorem sub2_386 : sub2 [2, -2, -2] = true := by decide +kernel
theorem sub2_387 : sub2 [2, -2, -1] = true := by decide +kernel
theorem sub2_388 : sub2 [2, -2, 0] = true := by decide +kernel
theorem sub2_389 : sub2 [2, -2, 1] = true := by decide +kernel
theorem sub2_390 : sub2 [2, -2, 2] = true := by decide +kernel
theorem sub2_391 : sub2 [2, -2, 3] = true := by decide +kernel
theorem sub2_392 : sub2 [2, -2, 4] = true := by decide +kernel
theorem sub2_393 : sub2 [2, -2, 5] = true := by decide +kernel
theorem sub2_394 : sub2 [2, -2, 6] = true := by decide +kernel
theorem sub2_395 : sub2 [2, -1, -8] = true := by decide +kernel
theorem sub2_396 : sub2 [2, -1, -7] = true := by decide +kernel
theorem sub2_397 : sub2 [2, -1, -6] = true := by decide +kernel
theorem sub2_398 : sub2 [2, -1, -5] = true := by decide +kernel
theorem sub2_399 : sub2 [2, -1, -4] = true := by decide +kernel
theorem sub2_400 : sub2 [2, -1, -3] = true := by decide +kernel
theorem sub2_401 : sub2 [2, -1, -2] = true := by decide +kernel
theorem sub2_402 : sub2 [2, -1, -1] = true := by decide +kernel
theorem sub2_403 : sub2 [2, -1, 0] = true := by decide +kernel
theorem sub2_404 : sub2 [2, -1, 1] = true := by decide +kernel
theorem sub2_405 : sub2 [2, -1, 2] = true := by decide +kernel
theorem sub2_406 : sub2 [2, -1, 3] = true := by decide +kernel
theorem sub2_407 : sub2 [2, -1, 4] = true := by decide +kernel
theorem sub2_408 : sub2 [2, -1, 5] = true := by decide +kernel
theorem sub2_409 : sub2 [2, -1, 6] = true := by decide +kernel
theorem sub2_410 : sub2 [2, -1, 7] = true := by decide +kernel
theorem sub2_411 : sub2 [2, 0, -8] = true := by decide +kernel
theorem sub2_412 : sub2 [2, 0, -7] = true := by decide +kernel
theorem sub2_413 : sub2 [2, 0, -6] = true := by decide +kernel
theorem sub2_414 : sub2 [2, 0, -5] = true := by decide +kernel
theorem sub2_415 : sub2 [2, 0, -4] = true := by decide +kernel
theorem sb2_12 : ∀ q ∈ blk2_12, sub2 q = true := by
  unfold blk2_12
  exact List.forall_mem_cons.2 ⟨sub2_384, List.forall_mem_cons.2 ⟨sub2_385, List.forall_mem_cons.2 ⟨sub2_386, List.forall_mem_cons.2 ⟨sub2_387, List.forall_mem_cons.2 ⟨sub2_388, List.forall_mem_cons.2 ⟨sub2_389, List.forall_mem_cons.2 ⟨sub2_390, List.forall_mem_cons.2 ⟨sub2_391, List.forall_mem_cons.2 ⟨sub2_392, List.forall_mem_cons.2 ⟨sub2_393, List.forall_mem_cons.2 ⟨sub2_394, List.forall_mem_cons.2 ⟨sub2_395, List.forall_mem_cons.2 ⟨sub2_396, List.forall_mem_cons.2 ⟨sub2_397, List.forall_mem_cons.2 ⟨sub2_398, List.forall_mem_cons.2 ⟨sub2_399, List.forall_mem_cons.2 ⟨sub2_400, List.forall_mem_cons.2 ⟨sub2_401, List.forall_mem_cons.2 ⟨sub2_402, List.forall_mem_cons.2 ⟨sub2_403, List.forall_mem_cons.2 ⟨sub2_404, List.forall_mem_cons.2 ⟨sub2_405, List.forall_mem_cons.2 ⟨sub2_406, List.forall_mem_cons.2 ⟨sub2_407, List.forall_mem_cons.2 ⟨sub2_408, List.forall_mem_cons.2 ⟨sub2_409, List.forall_mem_cons.2 ⟨sub2_410, List.forall_mem_cons.2 ⟨sub2_411, List.forall_mem_cons.2 ⟨sub2_412, List.forall_mem_cons.2 ⟨sub2_413, List.forall_mem_cons.2 ⟨sub2_414, List.forall_mem_cons.2 ⟨sub2_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_416 : sub2 [2, 0, -3] = true := by decide +kernel
theorem sub2_417 : sub2 [2, 0, -2] = true := by decide +kernel
theorem sub2_418 : sub2 [2, 0, -1] = true := by decide +kernel
theorem sub2_419 : sub2 [2, 0, 0] = true := by decide +kernel
theorem sub2_420 : sub2 [2, 0, 1] = true := by decide +kernel
theorem sub2_421 : sub2 [2, 0, 2] = true := by decide +kernel
theorem sub2_422 : sub2 [2, 0, 3] = true := by decide +kernel
theorem sub2_423 : sub2 [2, 0, 4] = true := by decide +kernel
theorem sub2_424 : sub2 [2, 0, 5] = true := by decide +kernel
theorem sub2_425 : sub2 [2, 0, 6] = true := by decide +kernel
theorem sub2_426 : sub2 [2, 0, 7] = true := by decide +kernel
theorem sub2_427 : sub2 [2, 1, -7] = true := by decide +kernel
theorem sub2_428 : sub2 [2, 1, -6] = true := by decide +kernel
theorem sub2_429 : sub2 [2, 1, -5] = true := by decide +kernel
theorem sub2_430 : sub2 [2, 1, -4] = true := by decide +kernel
theorem sub2_431 : sub2 [2, 1, -3] = true := by decide +kernel
theorem sub2_432 : sub2 [2, 1, -2] = true := by decide +kernel
theorem sub2_433 : sub2 [2, 1, -1] = true := by decide +kernel
theorem sub2_434 : sub2 [2, 1, 0] = true := by decide +kernel
theorem sub2_435 : sub2 [2, 1, 1] = true := by decide +kernel
theorem sub2_436 : sub2 [2, 1, 2] = true := by decide +kernel
theorem sub2_437 : sub2 [2, 1, 3] = true := by decide +kernel
theorem sub2_438 : sub2 [2, 1, 4] = true := by decide +kernel
theorem sub2_439 : sub2 [2, 1, 5] = true := by decide +kernel
theorem sub2_440 : sub2 [2, 1, 6] = true := by decide +kernel
theorem sub2_441 : sub2 [2, 1, 7] = true := by decide +kernel
theorem sub2_442 : sub2 [2, 1, 8] = true := by decide +kernel
theorem sub2_443 : sub2 [2, 2] = true := by decide +kernel
theorem sub2_444 : sub2 [2, 3] = true := by decide +kernel
theorem sub2_445 : sub2 [3, -4] = true := by decide +kernel
theorem sub2_446 : sub2 [3, -3] = true := by decide +kernel
theorem sub2_447 : sub2 [3, -2] = true := by decide +kernel
theorem sb2_13 : ∀ q ∈ blk2_13, sub2 q = true := by
  unfold blk2_13
  exact List.forall_mem_cons.2 ⟨sub2_416, List.forall_mem_cons.2 ⟨sub2_417, List.forall_mem_cons.2 ⟨sub2_418, List.forall_mem_cons.2 ⟨sub2_419, List.forall_mem_cons.2 ⟨sub2_420, List.forall_mem_cons.2 ⟨sub2_421, List.forall_mem_cons.2 ⟨sub2_422, List.forall_mem_cons.2 ⟨sub2_423, List.forall_mem_cons.2 ⟨sub2_424, List.forall_mem_cons.2 ⟨sub2_425, List.forall_mem_cons.2 ⟨sub2_426, List.forall_mem_cons.2 ⟨sub2_427, List.forall_mem_cons.2 ⟨sub2_428, List.forall_mem_cons.2 ⟨sub2_429, List.forall_mem_cons.2 ⟨sub2_430, List.forall_mem_cons.2 ⟨sub2_431, List.forall_mem_cons.2 ⟨sub2_432, List.forall_mem_cons.2 ⟨sub2_433, List.forall_mem_cons.2 ⟨sub2_434, List.forall_mem_cons.2 ⟨sub2_435, List.forall_mem_cons.2 ⟨sub2_436, List.forall_mem_cons.2 ⟨sub2_437, List.forall_mem_cons.2 ⟨sub2_438, List.forall_mem_cons.2 ⟨sub2_439, List.forall_mem_cons.2 ⟨sub2_440, List.forall_mem_cons.2 ⟨sub2_441, List.forall_mem_cons.2 ⟨sub2_442, List.forall_mem_cons.2 ⟨sub2_443, List.forall_mem_cons.2 ⟨sub2_444, List.forall_mem_cons.2 ⟨sub2_445, List.forall_mem_cons.2 ⟨sub2_446, List.forall_mem_cons.2 ⟨sub2_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_448 : sub2 [3, -1, -7] = true := by decide +kernel
theorem sub2_449 : sub2 [3, -1, -6] = true := by decide +kernel
theorem sub2_450 : sub2 [3, -1, -5] = true := by decide +kernel
theorem sub2_451 : sub2 [3, -1, -4] = true := by decide +kernel
theorem sub2_452 : sub2 [3, -1, -3] = true := by decide +kernel
theorem sub2_453 : sub2 [3, -1, -2] = true := by decide +kernel
theorem sub2_454 : sub2 [3, -1, -1] = true := by decide +kernel
theorem sub2_455 : sub2 [3, -1, 0] = true := by decide +kernel
theorem sub2_456 : sub2 [3, -1, 1] = true := by decide +kernel
theorem sub2_457 : sub2 [3, -1, 2] = true := by decide +kernel
theorem sub2_458 : sub2 [3, -1, 3] = true := by decide +kernel
theorem sub2_459 : sub2 [3, -1, 4] = true := by decide +kernel
theorem sub2_460 : sub2 [3, -1, 5] = true := by decide +kernel
theorem sub2_461 : sub2 [3, -1, 6] = true := by decide +kernel
theorem sub2_462 : sub2 [3, 0, -7] = true := by decide +kernel
theorem sub2_463 : sub2 [3, 0, -6] = true := by decide +kernel
theorem sub2_464 : sub2 [3, 0, -5] = true := by decide +kernel
theorem sub2_465 : sub2 [3, 0, -4] = true := by decide +kernel
theorem sub2_466 : sub2 [3, 0, -3] = true := by decide +kernel
theorem sub2_467 : sub2 [3, 0, -2] = true := by decide +kernel
theorem sub2_468 : sub2 [3, 0, -1] = true := by decide +kernel
theorem sub2_469 : sub2 [3, 0, 0] = true := by decide +kernel
theorem sub2_470 : sub2 [3, 0, 1] = true := by decide +kernel
theorem sub2_471 : sub2 [3, 0, 2] = true := by decide +kernel
theorem sub2_472 : sub2 [3, 0, 3] = true := by decide +kernel
theorem sub2_473 : sub2 [3, 0, 4] = true := by decide +kernel
theorem sub2_474 : sub2 [3, 0, 5] = true := by decide +kernel
theorem sub2_475 : sub2 [3, 0, 6] = true := by decide +kernel
theorem sub2_476 : sub2 [3, 0, 7] = true := by decide +kernel
theorem sub2_477 : sub2 [3, 1] = true := by decide +kernel
theorem sub2_478 : sub2 [3, 2] = true := by decide +kernel
theorem sub2_479 : sub2 [3, 3] = true := by decide +kernel
theorem sb2_14 : ∀ q ∈ blk2_14, sub2 q = true := by
  unfold blk2_14
  exact List.forall_mem_cons.2 ⟨sub2_448, List.forall_mem_cons.2 ⟨sub2_449, List.forall_mem_cons.2 ⟨sub2_450, List.forall_mem_cons.2 ⟨sub2_451, List.forall_mem_cons.2 ⟨sub2_452, List.forall_mem_cons.2 ⟨sub2_453, List.forall_mem_cons.2 ⟨sub2_454, List.forall_mem_cons.2 ⟨sub2_455, List.forall_mem_cons.2 ⟨sub2_456, List.forall_mem_cons.2 ⟨sub2_457, List.forall_mem_cons.2 ⟨sub2_458, List.forall_mem_cons.2 ⟨sub2_459, List.forall_mem_cons.2 ⟨sub2_460, List.forall_mem_cons.2 ⟨sub2_461, List.forall_mem_cons.2 ⟨sub2_462, List.forall_mem_cons.2 ⟨sub2_463, List.forall_mem_cons.2 ⟨sub2_464, List.forall_mem_cons.2 ⟨sub2_465, List.forall_mem_cons.2 ⟨sub2_466, List.forall_mem_cons.2 ⟨sub2_467, List.forall_mem_cons.2 ⟨sub2_468, List.forall_mem_cons.2 ⟨sub2_469, List.forall_mem_cons.2 ⟨sub2_470, List.forall_mem_cons.2 ⟨sub2_471, List.forall_mem_cons.2 ⟨sub2_472, List.forall_mem_cons.2 ⟨sub2_473, List.forall_mem_cons.2 ⟨sub2_474, List.forall_mem_cons.2 ⟨sub2_475, List.forall_mem_cons.2 ⟨sub2_476, List.forall_mem_cons.2 ⟨sub2_477, List.forall_mem_cons.2 ⟨sub2_478, List.forall_mem_cons.2 ⟨sub2_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub2_480 : sub2 [4, -4] = true := by decide +kernel
theorem sub2_481 : sub2 [4, -3] = true := by decide +kernel
theorem sub2_482 : sub2 [4, -2] = true := by decide +kernel
theorem sub2_483 : sub2 [4, -1] = true := by decide +kernel
theorem sub2_484 : sub2 [4, 0] = true := by decide +kernel
theorem sub2_485 : sub2 [4, 1] = true := by decide +kernel
theorem sub2_486 : sub2 [4, 2] = true := by decide +kernel
theorem sb2_15 : ∀ q ∈ blk2_15, sub2 q = true := by
  unfold blk2_15
  exact List.forall_mem_cons.2 ⟨sub2_480, List.forall_mem_cons.2 ⟨sub2_481, List.forall_mem_cons.2 ⟨sub2_482, List.forall_mem_cons.2 ⟨sub2_483, List.forall_mem_cons.2 ⟨sub2_484, List.forall_mem_cons.2 ⟨sub2_485, List.forall_mem_cons.2 ⟨sub2_486, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem sub3_0 : sub3 [-5] = true := by decide +kernel
theorem sub3_1 : sub3 [-4, -4] = true := by decide +kernel
theorem sub3_2 : sub3 [-4, -3] = true := by decide +kernel
theorem sub3_3 : sub3 [-4, -2] = true := by decide +kernel
theorem sub3_4 : sub3 [-4, -1] = true := by decide +kernel
theorem sub3_5 : sub3 [-4, 0] = true := by decide +kernel
theorem sub3_6 : sub3 [-4, 1] = true := by decide +kernel
theorem sub3_7 : sub3 [-4, 2] = true := by decide +kernel
theorem sub3_8 : sub3 [-4, 3] = true := by decide +kernel
theorem sub3_9 : sub3 [-4, 4] = true := by decide +kernel
theorem sub3_10 : sub3 [-3, -5] = true := by decide +kernel
theorem sub3_11 : sub3 [-3, -4] = true := by decide +kernel
theorem sub3_12 : sub3 [-3, -3] = true := by decide +kernel
theorem sub3_13 : sub3 [-3, -2] = true := by decide +kernel
theorem sub3_14 : sub3 [-3, -1] = true := by decide +kernel
theorem sub3_15 : sub3 [-3, 0] = true := by decide +kernel
theorem sub3_16 : sub3 [-3, 1] = true := by decide +kernel
theorem sub3_17 : sub3 [-3, 2] = true := by decide +kernel
theorem sub3_18 : sub3 [-3, 3] = true := by decide +kernel
theorem sub3_19 : sub3 [-3, 4] = true := by decide +kernel
theorem sub3_20 : sub3 [-2, -5] = true := by decide +kernel
theorem sub3_21 : sub3 [-2, -4] = true := by decide +kernel
theorem sub3_22 : sub3 [-2, -3] = true := by decide +kernel
theorem sub3_23 : sub3 [-2, -2] = true := by decide +kernel
theorem sub3_24 : sub3 [-2, -1] = true := by decide +kernel
theorem sub3_25 : sub3 [-2, 0] = true := by decide +kernel
theorem sub3_26 : sub3 [-2, 1] = true := by decide +kernel
theorem sub3_27 : sub3 [-2, 2] = true := by decide +kernel
theorem sub3_28 : sub3 [-2, 3] = true := by decide +kernel
theorem sub3_29 : sub3 [-2, 4] = true := by decide +kernel
theorem sub3_30 : sub3 [-2, 5] = true := by decide +kernel
theorem sub3_31 : sub3 [-1, -6] = true := by decide +kernel
theorem sb3_0 : ∀ q ∈ blk3_0, sub3 q = true := by
  unfold blk3_0
  exact List.forall_mem_cons.2 ⟨sub3_0, List.forall_mem_cons.2 ⟨sub3_1, List.forall_mem_cons.2 ⟨sub3_2, List.forall_mem_cons.2 ⟨sub3_3, List.forall_mem_cons.2 ⟨sub3_4, List.forall_mem_cons.2 ⟨sub3_5, List.forall_mem_cons.2 ⟨sub3_6, List.forall_mem_cons.2 ⟨sub3_7, List.forall_mem_cons.2 ⟨sub3_8, List.forall_mem_cons.2 ⟨sub3_9, List.forall_mem_cons.2 ⟨sub3_10, List.forall_mem_cons.2 ⟨sub3_11, List.forall_mem_cons.2 ⟨sub3_12, List.forall_mem_cons.2 ⟨sub3_13, List.forall_mem_cons.2 ⟨sub3_14, List.forall_mem_cons.2 ⟨sub3_15, List.forall_mem_cons.2 ⟨sub3_16, List.forall_mem_cons.2 ⟨sub3_17, List.forall_mem_cons.2 ⟨sub3_18, List.forall_mem_cons.2 ⟨sub3_19, List.forall_mem_cons.2 ⟨sub3_20, List.forall_mem_cons.2 ⟨sub3_21, List.forall_mem_cons.2 ⟨sub3_22, List.forall_mem_cons.2 ⟨sub3_23, List.forall_mem_cons.2 ⟨sub3_24, List.forall_mem_cons.2 ⟨sub3_25, List.forall_mem_cons.2 ⟨sub3_26, List.forall_mem_cons.2 ⟨sub3_27, List.forall_mem_cons.2 ⟨sub3_28, List.forall_mem_cons.2 ⟨sub3_29, List.forall_mem_cons.2 ⟨sub3_30, List.forall_mem_cons.2 ⟨sub3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C102
