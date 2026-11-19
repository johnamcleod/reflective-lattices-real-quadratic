import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd18_3_320 : subd18_3 [1, -5] = true := by decide +kernel
theorem subd18_3_321 : subd18_3 [1, -4] = true := by decide +kernel
theorem subd18_3_322 : subd18_3 [1, -3] = true := by decide +kernel
theorem subd18_3_323 : subd18_3 [1, -2, -7] = true := by decide +kernel
theorem subd18_3_324 : subd18_3 [1, -2, -6] = true := by decide +kernel
theorem subd18_3_325 : subd18_3 [1, -2, -5] = true := by decide +kernel
theorem subd18_3_326 : subd18_3 [1, -2, -4] = true := by decide +kernel
theorem subd18_3_327 : subd18_3 [1, -2, -3] = true := by decide +kernel
theorem subd18_3_328 : subd18_3 [1, -2, -2] = true := by decide +kernel
theorem subd18_3_329 : subd18_3 [1, -2, -1] = true := by decide +kernel
theorem subd18_3_330 : subd18_3 [1, -2, 0] = true := by decide +kernel
theorem subd18_3_331 : subd18_3 [1, -2, 1] = true := by decide +kernel
theorem subd18_3_332 : subd18_3 [1, -2, 2] = true := by decide +kernel
theorem subd18_3_333 : subd18_3 [1, -2, 3] = true := by decide +kernel
theorem subd18_3_334 : subd18_3 [1, -2, 4] = true := by decide +kernel
theorem subd18_3_335 : subd18_3 [1, -2, 5] = true := by decide +kernel
theorem subd18_3_336 : subd18_3 [1, -2, 6] = true := by decide +kernel
theorem subd18_3_337 : subd18_3 [1, -1, -7] = true := by decide +kernel
theorem subd18_3_338 : subd18_3 [1, -1, -6] = true := by decide +kernel
theorem subd18_3_339 : subd18_3 [1, -1, -5] = true := by decide +kernel
theorem subd18_3_340 : subd18_3 [1, -1, -4] = true := by decide +kernel
theorem subd18_3_341 : subd18_3 [1, -1, -3] = true := by decide +kernel
theorem subd18_3_342 : subd18_3 [1, -1, -2] = true := by decide +kernel
theorem subd18_3_343 : subd18_3 [1, -1, -1] = true := by decide +kernel
theorem subd18_3_344 : subd18_3 [1, -1, 0] = true := by decide +kernel
theorem subd18_3_345 : subd18_3 [1, -1, 1] = true := by decide +kernel
theorem subd18_3_346 : subd18_3 [1, -1, 2] = true := by decide +kernel
theorem subd18_3_347 : subd18_3 [1, -1, 3] = true := by decide +kernel
theorem subd18_3_348 : subd18_3 [1, -1, 4] = true := by decide +kernel
theorem subd18_3_349 : subd18_3 [1, -1, 5] = true := by decide +kernel
theorem subd18_3_350 : subd18_3 [1, -1, 6] = true := by decide +kernel
theorem subd18_3_351 : subd18_3 [1, 0, -8] = true := by decide +kernel
theorem sbd18_3_10 : ∀ q ∈ blkd18_3_10, subd18_3 q = true := by
  unfold blkd18_3_10
  exact List.forall_mem_cons.2 ⟨subd18_3_320, List.forall_mem_cons.2 ⟨subd18_3_321, List.forall_mem_cons.2 ⟨subd18_3_322, List.forall_mem_cons.2 ⟨subd18_3_323, List.forall_mem_cons.2 ⟨subd18_3_324, List.forall_mem_cons.2 ⟨subd18_3_325, List.forall_mem_cons.2 ⟨subd18_3_326, List.forall_mem_cons.2 ⟨subd18_3_327, List.forall_mem_cons.2 ⟨subd18_3_328, List.forall_mem_cons.2 ⟨subd18_3_329, List.forall_mem_cons.2 ⟨subd18_3_330, List.forall_mem_cons.2 ⟨subd18_3_331, List.forall_mem_cons.2 ⟨subd18_3_332, List.forall_mem_cons.2 ⟨subd18_3_333, List.forall_mem_cons.2 ⟨subd18_3_334, List.forall_mem_cons.2 ⟨subd18_3_335, List.forall_mem_cons.2 ⟨subd18_3_336, List.forall_mem_cons.2 ⟨subd18_3_337, List.forall_mem_cons.2 ⟨subd18_3_338, List.forall_mem_cons.2 ⟨subd18_3_339, List.forall_mem_cons.2 ⟨subd18_3_340, List.forall_mem_cons.2 ⟨subd18_3_341, List.forall_mem_cons.2 ⟨subd18_3_342, List.forall_mem_cons.2 ⟨subd18_3_343, List.forall_mem_cons.2 ⟨subd18_3_344, List.forall_mem_cons.2 ⟨subd18_3_345, List.forall_mem_cons.2 ⟨subd18_3_346, List.forall_mem_cons.2 ⟨subd18_3_347, List.forall_mem_cons.2 ⟨subd18_3_348, List.forall_mem_cons.2 ⟨subd18_3_349, List.forall_mem_cons.2 ⟨subd18_3_350, List.forall_mem_cons.2 ⟨subd18_3_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_3_352 : subd18_3 [1, 0, -7] = true := by decide +kernel
theorem subd18_3_353 : subd18_3 [1, 0, -6] = true := by decide +kernel
theorem subd18_3_354 : subd18_3 [1, 0, -5] = true := by decide +kernel
theorem subd18_3_355 : subd18_3 [1, 0, -4] = true := by decide +kernel
theorem subd18_3_356 : subd18_3 [1, 0, -3] = true := by decide +kernel
theorem subd18_3_357 : subd18_3 [1, 0, -2] = true := by decide +kernel
theorem subd18_3_358 : subd18_3 [1, 0, -1] = true := by decide +kernel
theorem subd18_3_359 : subd18_3 [1, 0, 0] = true := by decide +kernel
theorem subd18_3_360 : subd18_3 [1, 0, 1] = true := by decide +kernel
theorem subd18_3_361 : subd18_3 [1, 0, 2] = true := by decide +kernel
theorem subd18_3_362 : subd18_3 [1, 0, 3] = true := by decide +kernel
theorem subd18_3_363 : subd18_3 [1, 0, 4] = true := by decide +kernel
theorem subd18_3_364 : subd18_3 [1, 0, 5] = true := by decide +kernel
theorem subd18_3_365 : subd18_3 [1, 0, 6] = true := by decide +kernel
theorem subd18_3_366 : subd18_3 [1, 1, -8] = true := by decide +kernel
theorem subd18_3_367 : subd18_3 [1, 1, -7] = true := by decide +kernel
theorem subd18_3_368 : subd18_3 [1, 1, -6] = true := by decide +kernel
theorem subd18_3_369 : subd18_3 [1, 1, -5] = true := by decide +kernel
theorem subd18_3_370 : subd18_3 [1, 1, -4] = true := by decide +kernel
theorem subd18_3_371 : subd18_3 [1, 1, -3] = true := by decide +kernel
theorem subd18_3_372 : subd18_3 [1, 1, -2] = true := by decide +kernel
theorem subd18_3_373 : subd18_3 [1, 1, -1] = true := by decide +kernel
theorem subd18_3_374 : subd18_3 [1, 1, 0] = true := by decide +kernel
theorem subd18_3_375 : subd18_3 [1, 1, 1] = true := by decide +kernel
theorem subd18_3_376 : subd18_3 [1, 1, 2] = true := by decide +kernel
theorem subd18_3_377 : subd18_3 [1, 1, 3] = true := by decide +kernel
theorem subd18_3_378 : subd18_3 [1, 1, 4] = true := by decide +kernel
theorem subd18_3_379 : subd18_3 [1, 1, 5] = true := by decide +kernel
theorem subd18_3_380 : subd18_3 [1, 2, -8] = true := by decide +kernel
theorem subd18_3_381 : subd18_3 [1, 2, -7] = true := by decide +kernel
theorem subd18_3_382 : subd18_3 [1, 2, -6] = true := by decide +kernel
theorem subd18_3_383 : subd18_3 [1, 2, -5] = true := by decide +kernel
theorem sbd18_3_11 : ∀ q ∈ blkd18_3_11, subd18_3 q = true := by
  unfold blkd18_3_11
  exact List.forall_mem_cons.2 ⟨subd18_3_352, List.forall_mem_cons.2 ⟨subd18_3_353, List.forall_mem_cons.2 ⟨subd18_3_354, List.forall_mem_cons.2 ⟨subd18_3_355, List.forall_mem_cons.2 ⟨subd18_3_356, List.forall_mem_cons.2 ⟨subd18_3_357, List.forall_mem_cons.2 ⟨subd18_3_358, List.forall_mem_cons.2 ⟨subd18_3_359, List.forall_mem_cons.2 ⟨subd18_3_360, List.forall_mem_cons.2 ⟨subd18_3_361, List.forall_mem_cons.2 ⟨subd18_3_362, List.forall_mem_cons.2 ⟨subd18_3_363, List.forall_mem_cons.2 ⟨subd18_3_364, List.forall_mem_cons.2 ⟨subd18_3_365, List.forall_mem_cons.2 ⟨subd18_3_366, List.forall_mem_cons.2 ⟨subd18_3_367, List.forall_mem_cons.2 ⟨subd18_3_368, List.forall_mem_cons.2 ⟨subd18_3_369, List.forall_mem_cons.2 ⟨subd18_3_370, List.forall_mem_cons.2 ⟨subd18_3_371, List.forall_mem_cons.2 ⟨subd18_3_372, List.forall_mem_cons.2 ⟨subd18_3_373, List.forall_mem_cons.2 ⟨subd18_3_374, List.forall_mem_cons.2 ⟨subd18_3_375, List.forall_mem_cons.2 ⟨subd18_3_376, List.forall_mem_cons.2 ⟨subd18_3_377, List.forall_mem_cons.2 ⟨subd18_3_378, List.forall_mem_cons.2 ⟨subd18_3_379, List.forall_mem_cons.2 ⟨subd18_3_380, List.forall_mem_cons.2 ⟨subd18_3_381, List.forall_mem_cons.2 ⟨subd18_3_382, List.forall_mem_cons.2 ⟨subd18_3_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_3_384 : subd18_3 [1, 2, -4] = true := by decide +kernel
theorem subd18_3_385 : subd18_3 [1, 2, -3] = true := by decide +kernel
theorem subd18_3_386 : subd18_3 [1, 2, -2] = true := by decide +kernel
theorem subd18_3_387 : subd18_3 [1, 2, -1] = true := by decide +kernel
theorem subd18_3_388 : subd18_3 [1, 2, 0] = true := by decide +kernel
theorem subd18_3_389 : subd18_3 [1, 2, 1] = true := by decide +kernel
theorem subd18_3_390 : subd18_3 [1, 2, 2] = true := by decide +kernel
theorem subd18_3_391 : subd18_3 [1, 2, 3] = true := by decide +kernel
theorem subd18_3_392 : subd18_3 [1, 2, 4] = true := by decide +kernel
theorem subd18_3_393 : subd18_3 [1, 2, 5] = true := by decide +kernel
theorem subd18_3_394 : subd18_3 [1, 3] = true := by decide +kernel
theorem subd18_3_395 : subd18_3 [1, 4] = true := by decide +kernel
theorem subd18_3_396 : subd18_3 [1, 5] = true := by decide +kernel
theorem subd18_3_397 : subd18_3 [1, 6] = true := by decide +kernel
theorem subd18_3_398 : subd18_3 [1, 7] = true := by decide +kernel
theorem subd18_3_399 : subd18_3 [2, -8] = true := by decide +kernel
theorem subd18_3_400 : subd18_3 [2, -7] = true := by decide +kernel
theorem subd18_3_401 : subd18_3 [2, -6] = true := by decide +kernel
theorem subd18_3_402 : subd18_3 [2, -5] = true := by decide +kernel
theorem subd18_3_403 : subd18_3 [2, -4] = true := by decide +kernel
theorem subd18_3_404 : subd18_3 [2, -3] = true := by decide +kernel
theorem subd18_3_405 : subd18_3 [2, -2, -7] = true := by decide +kernel
theorem subd18_3_406 : subd18_3 [2, -2, -6] = true := by decide +kernel
theorem subd18_3_407 : subd18_3 [2, -2, -5] = true := by decide +kernel
theorem subd18_3_408 : subd18_3 [2, -2, -4] = true := by decide +kernel
theorem subd18_3_409 : subd18_3 [2, -2, -3] = true := by decide +kernel
theorem subd18_3_410 : subd18_3 [2, -2, -2] = true := by decide +kernel
theorem subd18_3_411 : subd18_3 [2, -2, -1] = true := by decide +kernel
theorem subd18_3_412 : subd18_3 [2, -2, 0] = true := by decide +kernel
theorem subd18_3_413 : subd18_3 [2, -2, 1] = true := by decide +kernel
theorem subd18_3_414 : subd18_3 [2, -2, 2] = true := by decide +kernel
theorem subd18_3_415 : subd18_3 [2, -2, 3] = true := by decide +kernel
theorem sbd18_3_12 : ∀ q ∈ blkd18_3_12, subd18_3 q = true := by
  unfold blkd18_3_12
  exact List.forall_mem_cons.2 ⟨subd18_3_384, List.forall_mem_cons.2 ⟨subd18_3_385, List.forall_mem_cons.2 ⟨subd18_3_386, List.forall_mem_cons.2 ⟨subd18_3_387, List.forall_mem_cons.2 ⟨subd18_3_388, List.forall_mem_cons.2 ⟨subd18_3_389, List.forall_mem_cons.2 ⟨subd18_3_390, List.forall_mem_cons.2 ⟨subd18_3_391, List.forall_mem_cons.2 ⟨subd18_3_392, List.forall_mem_cons.2 ⟨subd18_3_393, List.forall_mem_cons.2 ⟨subd18_3_394, List.forall_mem_cons.2 ⟨subd18_3_395, List.forall_mem_cons.2 ⟨subd18_3_396, List.forall_mem_cons.2 ⟨subd18_3_397, List.forall_mem_cons.2 ⟨subd18_3_398, List.forall_mem_cons.2 ⟨subd18_3_399, List.forall_mem_cons.2 ⟨subd18_3_400, List.forall_mem_cons.2 ⟨subd18_3_401, List.forall_mem_cons.2 ⟨subd18_3_402, List.forall_mem_cons.2 ⟨subd18_3_403, List.forall_mem_cons.2 ⟨subd18_3_404, List.forall_mem_cons.2 ⟨subd18_3_405, List.forall_mem_cons.2 ⟨subd18_3_406, List.forall_mem_cons.2 ⟨subd18_3_407, List.forall_mem_cons.2 ⟨subd18_3_408, List.forall_mem_cons.2 ⟨subd18_3_409, List.forall_mem_cons.2 ⟨subd18_3_410, List.forall_mem_cons.2 ⟨subd18_3_411, List.forall_mem_cons.2 ⟨subd18_3_412, List.forall_mem_cons.2 ⟨subd18_3_413, List.forall_mem_cons.2 ⟨subd18_3_414, List.forall_mem_cons.2 ⟨subd18_3_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_3_416 : subd18_3 [2, -2, 4] = true := by decide +kernel
theorem subd18_3_417 : subd18_3 [2, -2, 5] = true := by decide +kernel
theorem subd18_3_418 : subd18_3 [2, -1, -8] = true := by decide +kernel
theorem subd18_3_419 : subd18_3 [2, -1, -7] = true := by decide +kernel
theorem subd18_3_420 : subd18_3 [2, -1, -6] = true := by decide +kernel
theorem subd18_3_421 : subd18_3 [2, -1, -5] = true := by decide +kernel
theorem subd18_3_422 : subd18_3 [2, -1, -4] = true := by decide +kernel
theorem subd18_3_423 : subd18_3 [2, -1, -3] = true := by decide +kernel
theorem subd18_3_424 : subd18_3 [2, -1, -2] = true := by decide +kernel
theorem subd18_3_425 : subd18_3 [2, -1, -1] = true := by decide +kernel
theorem subd18_3_426 : subd18_3 [2, -1, 0] = true := by decide +kernel
theorem subd18_3_427 : subd18_3 [2, -1, 1] = true := by decide +kernel
theorem subd18_3_428 : subd18_3 [2, -1, 2] = true := by decide +kernel
theorem subd18_3_429 : subd18_3 [2, -1, 3] = true := by decide +kernel
theorem subd18_3_430 : subd18_3 [2, -1, 4] = true := by decide +kernel
theorem subd18_3_431 : subd18_3 [2, -1, 5] = true := by decide +kernel
theorem subd18_3_432 : subd18_3 [2, 0, -8] = true := by decide +kernel
theorem subd18_3_433 : subd18_3 [2, 0, -7] = true := by decide +kernel
theorem subd18_3_434 : subd18_3 [2, 0, -6] = true := by decide +kernel
theorem subd18_3_435 : subd18_3 [2, 0, -5] = true := by decide +kernel
theorem subd18_3_436 : subd18_3 [2, 0, -4] = true := by decide +kernel
theorem subd18_3_437 : subd18_3 [2, 0, -3] = true := by decide +kernel
theorem subd18_3_438 : subd18_3 [2, 0, -2] = true := by decide +kernel
theorem subd18_3_439 : subd18_3 [2, 0, -1] = true := by decide +kernel
theorem subd18_3_440 : subd18_3 [2, 0, 0] = true := by decide +kernel
theorem subd18_3_441 : subd18_3 [2, 0, 1] = true := by decide +kernel
theorem subd18_3_442 : subd18_3 [2, 0, 2] = true := by decide +kernel
theorem subd18_3_443 : subd18_3 [2, 0, 3] = true := by decide +kernel
theorem subd18_3_444 : subd18_3 [2, 0, 4] = true := by decide +kernel
theorem subd18_3_445 : subd18_3 [2, 0, 5] = true := by decide +kernel
theorem subd18_3_446 : subd18_3 [2, 1, -8] = true := by decide +kernel
theorem subd18_3_447 : subd18_3 [2, 1, -7] = true := by decide +kernel
theorem sbd18_3_13 : ∀ q ∈ blkd18_3_13, subd18_3 q = true := by
  unfold blkd18_3_13
  exact List.forall_mem_cons.2 ⟨subd18_3_416, List.forall_mem_cons.2 ⟨subd18_3_417, List.forall_mem_cons.2 ⟨subd18_3_418, List.forall_mem_cons.2 ⟨subd18_3_419, List.forall_mem_cons.2 ⟨subd18_3_420, List.forall_mem_cons.2 ⟨subd18_3_421, List.forall_mem_cons.2 ⟨subd18_3_422, List.forall_mem_cons.2 ⟨subd18_3_423, List.forall_mem_cons.2 ⟨subd18_3_424, List.forall_mem_cons.2 ⟨subd18_3_425, List.forall_mem_cons.2 ⟨subd18_3_426, List.forall_mem_cons.2 ⟨subd18_3_427, List.forall_mem_cons.2 ⟨subd18_3_428, List.forall_mem_cons.2 ⟨subd18_3_429, List.forall_mem_cons.2 ⟨subd18_3_430, List.forall_mem_cons.2 ⟨subd18_3_431, List.forall_mem_cons.2 ⟨subd18_3_432, List.forall_mem_cons.2 ⟨subd18_3_433, List.forall_mem_cons.2 ⟨subd18_3_434, List.forall_mem_cons.2 ⟨subd18_3_435, List.forall_mem_cons.2 ⟨subd18_3_436, List.forall_mem_cons.2 ⟨subd18_3_437, List.forall_mem_cons.2 ⟨subd18_3_438, List.forall_mem_cons.2 ⟨subd18_3_439, List.forall_mem_cons.2 ⟨subd18_3_440, List.forall_mem_cons.2 ⟨subd18_3_441, List.forall_mem_cons.2 ⟨subd18_3_442, List.forall_mem_cons.2 ⟨subd18_3_443, List.forall_mem_cons.2 ⟨subd18_3_444, List.forall_mem_cons.2 ⟨subd18_3_445, List.forall_mem_cons.2 ⟨subd18_3_446, List.forall_mem_cons.2 ⟨subd18_3_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_3_448 : subd18_3 [2, 1, -6] = true := by decide +kernel
theorem subd18_3_449 : subd18_3 [2, 1, -5] = true := by decide +kernel
theorem subd18_3_450 : subd18_3 [2, 1, -4] = true := by decide +kernel
theorem subd18_3_451 : subd18_3 [2, 1, -3] = true := by decide +kernel
theorem subd18_3_452 : subd18_3 [2, 1, -2] = true := by decide +kernel
theorem subd18_3_453 : subd18_3 [2, 1, -1] = true := by decide +kernel
theorem subd18_3_454 : subd18_3 [2, 1, 0] = true := by decide +kernel
theorem subd18_3_455 : subd18_3 [2, 1, 1] = true := by decide +kernel
theorem subd18_3_456 : subd18_3 [2, 1, 2] = true := by decide +kernel
theorem subd18_3_457 : subd18_3 [2, 1, 3] = true := by decide +kernel
theorem subd18_3_458 : subd18_3 [2, 1, 4] = true := by decide +kernel
theorem subd18_3_459 : subd18_3 [2, 1, 5] = true := by decide +kernel
theorem subd18_3_460 : subd18_3 [2, 2, -8] = true := by decide +kernel
theorem subd18_3_461 : subd18_3 [2, 2, -7] = true := by decide +kernel
theorem subd18_3_462 : subd18_3 [2, 2, -6] = true := by decide +kernel
theorem subd18_3_463 : subd18_3 [2, 2, -5] = true := by decide +kernel
theorem subd18_3_464 : subd18_3 [2, 2, -4] = true := by decide +kernel
theorem subd18_3_465 : subd18_3 [2, 2, -3] = true := by decide +kernel
theorem subd18_3_466 : subd18_3 [2, 2, -2] = true := by decide +kernel
theorem subd18_3_467 : subd18_3 [2, 2, -1] = true := by decide +kernel
theorem subd18_3_468 : subd18_3 [2, 2, 0] = true := by decide +kernel
theorem subd18_3_469 : subd18_3 [2, 2, 1] = true := by decide +kernel
theorem subd18_3_470 : subd18_3 [2, 2, 2] = true := by decide +kernel
theorem subd18_3_471 : subd18_3 [2, 2, 3] = true := by decide +kernel
theorem subd18_3_472 : subd18_3 [2, 2, 4] = true := by decide +kernel
theorem subd18_3_473 : subd18_3 [2, 3] = true := by decide +kernel
theorem subd18_3_474 : subd18_3 [2, 4] = true := by decide +kernel
theorem subd18_3_475 : subd18_3 [2, 5] = true := by decide +kernel
theorem subd18_3_476 : subd18_3 [2, 6] = true := by decide +kernel
theorem subd18_3_477 : subd18_3 [2, 7] = true := by decide +kernel
theorem subd18_3_478 : subd18_3 [3, -7] = true := by decide +kernel
theorem subd18_3_479 : subd18_3 [3, -6] = true := by decide +kernel
theorem sbd18_3_14 : ∀ q ∈ blkd18_3_14, subd18_3 q = true := by
  unfold blkd18_3_14
  exact List.forall_mem_cons.2 ⟨subd18_3_448, List.forall_mem_cons.2 ⟨subd18_3_449, List.forall_mem_cons.2 ⟨subd18_3_450, List.forall_mem_cons.2 ⟨subd18_3_451, List.forall_mem_cons.2 ⟨subd18_3_452, List.forall_mem_cons.2 ⟨subd18_3_453, List.forall_mem_cons.2 ⟨subd18_3_454, List.forall_mem_cons.2 ⟨subd18_3_455, List.forall_mem_cons.2 ⟨subd18_3_456, List.forall_mem_cons.2 ⟨subd18_3_457, List.forall_mem_cons.2 ⟨subd18_3_458, List.forall_mem_cons.2 ⟨subd18_3_459, List.forall_mem_cons.2 ⟨subd18_3_460, List.forall_mem_cons.2 ⟨subd18_3_461, List.forall_mem_cons.2 ⟨subd18_3_462, List.forall_mem_cons.2 ⟨subd18_3_463, List.forall_mem_cons.2 ⟨subd18_3_464, List.forall_mem_cons.2 ⟨subd18_3_465, List.forall_mem_cons.2 ⟨subd18_3_466, List.forall_mem_cons.2 ⟨subd18_3_467, List.forall_mem_cons.2 ⟨subd18_3_468, List.forall_mem_cons.2 ⟨subd18_3_469, List.forall_mem_cons.2 ⟨subd18_3_470, List.forall_mem_cons.2 ⟨subd18_3_471, List.forall_mem_cons.2 ⟨subd18_3_472, List.forall_mem_cons.2 ⟨subd18_3_473, List.forall_mem_cons.2 ⟨subd18_3_474, List.forall_mem_cons.2 ⟨subd18_3_475, List.forall_mem_cons.2 ⟨subd18_3_476, List.forall_mem_cons.2 ⟨subd18_3_477, List.forall_mem_cons.2 ⟨subd18_3_478, List.forall_mem_cons.2 ⟨subd18_3_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_3_480 : subd18_3 [3, -5] = true := by decide +kernel
theorem subd18_3_481 : subd18_3 [3, -4] = true := by decide +kernel
theorem subd18_3_482 : subd18_3 [3, -3] = true := by decide +kernel
theorem subd18_3_483 : subd18_3 [3, -2] = true := by decide +kernel
theorem subd18_3_484 : subd18_3 [3, -1] = true := by decide +kernel
theorem subd18_3_485 : subd18_3 [3, 0] = true := by decide +kernel
theorem subd18_3_486 : subd18_3 [3, 1] = true := by decide +kernel
theorem subd18_3_487 : subd18_3 [3, 2] = true := by decide +kernel
theorem subd18_3_488 : subd18_3 [3, 3] = true := by decide +kernel
theorem subd18_3_489 : subd18_3 [3, 4] = true := by decide +kernel
theorem subd18_3_490 : subd18_3 [3, 5] = true := by decide +kernel
theorem subd18_3_491 : subd18_3 [3, 6] = true := by decide +kernel
theorem subd18_3_492 : subd18_3 [4, -7] = true := by decide +kernel
theorem subd18_3_493 : subd18_3 [4, -6] = true := by decide +kernel
theorem subd18_3_494 : subd18_3 [4, -5] = true := by decide +kernel
theorem subd18_3_495 : subd18_3 [4, -4] = true := by decide +kernel
theorem subd18_3_496 : subd18_3 [4, -3] = true := by decide +kernel
theorem subd18_3_497 : subd18_3 [4, -2] = true := by decide +kernel
theorem subd18_3_498 : subd18_3 [4, -1] = true := by decide +kernel
theorem subd18_3_499 : subd18_3 [4, 0] = true := by decide +kernel
theorem subd18_3_500 : subd18_3 [4, 1] = true := by decide +kernel
theorem subd18_3_501 : subd18_3 [4, 2] = true := by decide +kernel
theorem subd18_3_502 : subd18_3 [4, 3] = true := by decide +kernel
theorem subd18_3_503 : subd18_3 [4, 4] = true := by decide +kernel
theorem subd18_3_504 : subd18_3 [4, 5] = true := by decide +kernel
theorem subd18_3_505 : subd18_3 [4, 6] = true := by decide +kernel
theorem subd18_3_506 : subd18_3 [5, -6] = true := by decide +kernel
theorem subd18_3_507 : subd18_3 [5, -5] = true := by decide +kernel
theorem subd18_3_508 : subd18_3 [5, -4] = true := by decide +kernel
theorem subd18_3_509 : subd18_3 [5, -3] = true := by decide +kernel
theorem subd18_3_510 : subd18_3 [5, -2] = true := by decide +kernel
theorem subd18_3_511 : subd18_3 [5, -1] = true := by decide +kernel
theorem sbd18_3_15 : ∀ q ∈ blkd18_3_15, subd18_3 q = true := by
  unfold blkd18_3_15
  exact List.forall_mem_cons.2 ⟨subd18_3_480, List.forall_mem_cons.2 ⟨subd18_3_481, List.forall_mem_cons.2 ⟨subd18_3_482, List.forall_mem_cons.2 ⟨subd18_3_483, List.forall_mem_cons.2 ⟨subd18_3_484, List.forall_mem_cons.2 ⟨subd18_3_485, List.forall_mem_cons.2 ⟨subd18_3_486, List.forall_mem_cons.2 ⟨subd18_3_487, List.forall_mem_cons.2 ⟨subd18_3_488, List.forall_mem_cons.2 ⟨subd18_3_489, List.forall_mem_cons.2 ⟨subd18_3_490, List.forall_mem_cons.2 ⟨subd18_3_491, List.forall_mem_cons.2 ⟨subd18_3_492, List.forall_mem_cons.2 ⟨subd18_3_493, List.forall_mem_cons.2 ⟨subd18_3_494, List.forall_mem_cons.2 ⟨subd18_3_495, List.forall_mem_cons.2 ⟨subd18_3_496, List.forall_mem_cons.2 ⟨subd18_3_497, List.forall_mem_cons.2 ⟨subd18_3_498, List.forall_mem_cons.2 ⟨subd18_3_499, List.forall_mem_cons.2 ⟨subd18_3_500, List.forall_mem_cons.2 ⟨subd18_3_501, List.forall_mem_cons.2 ⟨subd18_3_502, List.forall_mem_cons.2 ⟨subd18_3_503, List.forall_mem_cons.2 ⟨subd18_3_504, List.forall_mem_cons.2 ⟨subd18_3_505, List.forall_mem_cons.2 ⟨subd18_3_506, List.forall_mem_cons.2 ⟨subd18_3_507, List.forall_mem_cons.2 ⟨subd18_3_508, List.forall_mem_cons.2 ⟨subd18_3_509, List.forall_mem_cons.2 ⟨subd18_3_510, List.forall_mem_cons.2 ⟨subd18_3_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_3_512 : subd18_3 [5, 0] = true := by decide +kernel
theorem subd18_3_513 : subd18_3 [5, 1] = true := by decide +kernel
theorem subd18_3_514 : subd18_3 [5, 2] = true := by decide +kernel
theorem subd18_3_515 : subd18_3 [5, 3] = true := by decide +kernel
theorem subd18_3_516 : subd18_3 [5, 4] = true := by decide +kernel
theorem subd18_3_517 : subd18_3 [5, 5] = true := by decide +kernel
theorem subd18_3_518 : subd18_3 [6, -5] = true := by decide +kernel
theorem subd18_3_519 : subd18_3 [6, -4] = true := by decide +kernel
theorem subd18_3_520 : subd18_3 [6, -3] = true := by decide +kernel
theorem subd18_3_521 : subd18_3 [6, -2] = true := by decide +kernel
theorem subd18_3_522 : subd18_3 [6, -1] = true := by decide +kernel
theorem subd18_3_523 : subd18_3 [6, 0] = true := by decide +kernel
theorem subd18_3_524 : subd18_3 [6, 1] = true := by decide +kernel
theorem subd18_3_525 : subd18_3 [6, 2] = true := by decide +kernel
theorem subd18_3_526 : subd18_3 [6, 3] = true := by decide +kernel
theorem subd18_3_527 : subd18_3 [6, 4] = true := by decide +kernel
theorem subd18_3_528 : subd18_3 [7] = true := by decide +kernel
theorem sbd18_3_16 : ∀ q ∈ blkd18_3_16, subd18_3 q = true := by
  unfold blkd18_3_16
  exact List.forall_mem_cons.2 ⟨subd18_3_512, List.forall_mem_cons.2 ⟨subd18_3_513, List.forall_mem_cons.2 ⟨subd18_3_514, List.forall_mem_cons.2 ⟨subd18_3_515, List.forall_mem_cons.2 ⟨subd18_3_516, List.forall_mem_cons.2 ⟨subd18_3_517, List.forall_mem_cons.2 ⟨subd18_3_518, List.forall_mem_cons.2 ⟨subd18_3_519, List.forall_mem_cons.2 ⟨subd18_3_520, List.forall_mem_cons.2 ⟨subd18_3_521, List.forall_mem_cons.2 ⟨subd18_3_522, List.forall_mem_cons.2 ⟨subd18_3_523, List.forall_mem_cons.2 ⟨subd18_3_524, List.forall_mem_cons.2 ⟨subd18_3_525, List.forall_mem_cons.2 ⟨subd18_3_526, List.forall_mem_cons.2 ⟨subd18_3_527, List.forall_mem_cons.2 ⟨subd18_3_528, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C143
