import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_6_320 : subd7_6 [0, 3, 3] = true := by decide +kernel
theorem subd7_6_321 : subd7_6 [0, 3, 4] = true := by decide +kernel
theorem subd7_6_322 : subd7_6 [0, 3, 5] = true := by decide +kernel
theorem subd7_6_323 : subd7_6 [0, 4] = true := by decide +kernel
theorem subd7_6_324 : subd7_6 [0, 5] = true := by decide +kernel
theorem subd7_6_325 : subd7_6 [0, 6] = true := by decide +kernel
theorem subd7_6_326 : subd7_6 [0, 7] = true := by decide +kernel
theorem subd7_6_327 : subd7_6 [1, -7] = true := by decide +kernel
theorem subd7_6_328 : subd7_6 [1, -6] = true := by decide +kernel
theorem subd7_6_329 : subd7_6 [1, -5] = true := by decide +kernel
theorem subd7_6_330 : subd7_6 [1, -4] = true := by decide +kernel
theorem subd7_6_331 : subd7_6 [1, -3] = true := by decide +kernel
theorem subd7_6_332 : subd7_6 [1, -2, -7] = true := by decide +kernel
theorem subd7_6_333 : subd7_6 [1, -2, -6] = true := by decide +kernel
theorem subd7_6_334 : subd7_6 [1, -2, -5] = true := by decide +kernel
theorem subd7_6_335 : subd7_6 [1, -2, -4] = true := by decide +kernel
theorem subd7_6_336 : subd7_6 [1, -2, -3] = true := by decide +kernel
theorem subd7_6_337 : subd7_6 [1, -2, -2] = true := by decide +kernel
theorem subd7_6_338 : subd7_6 [1, -2, -1] = true := by decide +kernel
theorem subd7_6_339 : subd7_6 [1, -2, 0] = true := by decide +kernel
theorem subd7_6_340 : subd7_6 [1, -2, 1] = true := by decide +kernel
theorem subd7_6_341 : subd7_6 [1, -2, 2] = true := by decide +kernel
theorem subd7_6_342 : subd7_6 [1, -2, 3] = true := by decide +kernel
theorem subd7_6_343 : subd7_6 [1, -2, 4] = true := by decide +kernel
theorem subd7_6_344 : subd7_6 [1, -2, 5] = true := by decide +kernel
theorem subd7_6_345 : subd7_6 [1, -2, 6] = true := by decide +kernel
theorem subd7_6_346 : subd7_6 [1, -1, -7] = true := by decide +kernel
theorem subd7_6_347 : subd7_6 [1, -1, -6] = true := by decide +kernel
theorem subd7_6_348 : subd7_6 [1, -1, -5] = true := by decide +kernel
theorem subd7_6_349 : subd7_6 [1, -1, -4] = true := by decide +kernel
theorem subd7_6_350 : subd7_6 [1, -1, -3] = true := by decide +kernel
theorem subd7_6_351 : subd7_6 [1, -1, -2] = true := by decide +kernel
theorem sbd7_6_10 : ∀ q ∈ blkd7_6_10, subd7_6 q = true := by
  unfold blkd7_6_10
  exact List.forall_mem_cons.2 ⟨subd7_6_320, List.forall_mem_cons.2 ⟨subd7_6_321, List.forall_mem_cons.2 ⟨subd7_6_322, List.forall_mem_cons.2 ⟨subd7_6_323, List.forall_mem_cons.2 ⟨subd7_6_324, List.forall_mem_cons.2 ⟨subd7_6_325, List.forall_mem_cons.2 ⟨subd7_6_326, List.forall_mem_cons.2 ⟨subd7_6_327, List.forall_mem_cons.2 ⟨subd7_6_328, List.forall_mem_cons.2 ⟨subd7_6_329, List.forall_mem_cons.2 ⟨subd7_6_330, List.forall_mem_cons.2 ⟨subd7_6_331, List.forall_mem_cons.2 ⟨subd7_6_332, List.forall_mem_cons.2 ⟨subd7_6_333, List.forall_mem_cons.2 ⟨subd7_6_334, List.forall_mem_cons.2 ⟨subd7_6_335, List.forall_mem_cons.2 ⟨subd7_6_336, List.forall_mem_cons.2 ⟨subd7_6_337, List.forall_mem_cons.2 ⟨subd7_6_338, List.forall_mem_cons.2 ⟨subd7_6_339, List.forall_mem_cons.2 ⟨subd7_6_340, List.forall_mem_cons.2 ⟨subd7_6_341, List.forall_mem_cons.2 ⟨subd7_6_342, List.forall_mem_cons.2 ⟨subd7_6_343, List.forall_mem_cons.2 ⟨subd7_6_344, List.forall_mem_cons.2 ⟨subd7_6_345, List.forall_mem_cons.2 ⟨subd7_6_346, List.forall_mem_cons.2 ⟨subd7_6_347, List.forall_mem_cons.2 ⟨subd7_6_348, List.forall_mem_cons.2 ⟨subd7_6_349, List.forall_mem_cons.2 ⟨subd7_6_350, List.forall_mem_cons.2 ⟨subd7_6_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_6_352 : subd7_6 [1, -1, -1] = true := by decide +kernel
theorem subd7_6_353 : subd7_6 [1, -1, 0] = true := by decide +kernel
theorem subd7_6_354 : subd7_6 [1, -1, 1] = true := by decide +kernel
theorem subd7_6_355 : subd7_6 [1, -1, 2] = true := by decide +kernel
theorem subd7_6_356 : subd7_6 [1, -1, 3] = true := by decide +kernel
theorem subd7_6_357 : subd7_6 [1, -1, 4] = true := by decide +kernel
theorem subd7_6_358 : subd7_6 [1, -1, 5] = true := by decide +kernel
theorem subd7_6_359 : subd7_6 [1, -1, 6] = true := by decide +kernel
theorem subd7_6_360 : subd7_6 [1, 0, -7] = true := by decide +kernel
theorem subd7_6_361 : subd7_6 [1, 0, -6] = true := by decide +kernel
theorem subd7_6_362 : subd7_6 [1, 0, -5] = true := by decide +kernel
theorem subd7_6_363 : subd7_6 [1, 0, -4] = true := by decide +kernel
theorem subd7_6_364 : subd7_6 [1, 0, -3] = true := by decide +kernel
theorem subd7_6_365 : subd7_6 [1, 0, -2] = true := by decide +kernel
theorem subd7_6_366 : subd7_6 [1, 0, -1] = true := by decide +kernel
theorem subd7_6_367 : subd7_6 [1, 0, 0] = true := by decide +kernel
theorem subd7_6_368 : subd7_6 [1, 0, 1] = true := by decide +kernel
theorem subd7_6_369 : subd7_6 [1, 0, 2] = true := by decide +kernel
theorem subd7_6_370 : subd7_6 [1, 0, 3] = true := by decide +kernel
theorem subd7_6_371 : subd7_6 [1, 0, 4] = true := by decide +kernel
theorem subd7_6_372 : subd7_6 [1, 0, 5] = true := by decide +kernel
theorem subd7_6_373 : subd7_6 [1, 0, 6] = true := by decide +kernel
theorem subd7_6_374 : subd7_6 [1, 1, -8] = true := by decide +kernel
theorem subd7_6_375 : subd7_6 [1, 1, -7] = true := by decide +kernel
theorem subd7_6_376 : subd7_6 [1, 1, -6] = true := by decide +kernel
theorem subd7_6_377 : subd7_6 [1, 1, -5] = true := by decide +kernel
theorem subd7_6_378 : subd7_6 [1, 1, -4] = true := by decide +kernel
theorem subd7_6_379 : subd7_6 [1, 1, -3] = true := by decide +kernel
theorem subd7_6_380 : subd7_6 [1, 1, -2] = true := by decide +kernel
theorem subd7_6_381 : subd7_6 [1, 1, -1] = true := by decide +kernel
theorem subd7_6_382 : subd7_6 [1, 1, 0] = true := by decide +kernel
theorem subd7_6_383 : subd7_6 [1, 1, 1] = true := by decide +kernel
theorem sbd7_6_11 : ∀ q ∈ blkd7_6_11, subd7_6 q = true := by
  unfold blkd7_6_11
  exact List.forall_mem_cons.2 ⟨subd7_6_352, List.forall_mem_cons.2 ⟨subd7_6_353, List.forall_mem_cons.2 ⟨subd7_6_354, List.forall_mem_cons.2 ⟨subd7_6_355, List.forall_mem_cons.2 ⟨subd7_6_356, List.forall_mem_cons.2 ⟨subd7_6_357, List.forall_mem_cons.2 ⟨subd7_6_358, List.forall_mem_cons.2 ⟨subd7_6_359, List.forall_mem_cons.2 ⟨subd7_6_360, List.forall_mem_cons.2 ⟨subd7_6_361, List.forall_mem_cons.2 ⟨subd7_6_362, List.forall_mem_cons.2 ⟨subd7_6_363, List.forall_mem_cons.2 ⟨subd7_6_364, List.forall_mem_cons.2 ⟨subd7_6_365, List.forall_mem_cons.2 ⟨subd7_6_366, List.forall_mem_cons.2 ⟨subd7_6_367, List.forall_mem_cons.2 ⟨subd7_6_368, List.forall_mem_cons.2 ⟨subd7_6_369, List.forall_mem_cons.2 ⟨subd7_6_370, List.forall_mem_cons.2 ⟨subd7_6_371, List.forall_mem_cons.2 ⟨subd7_6_372, List.forall_mem_cons.2 ⟨subd7_6_373, List.forall_mem_cons.2 ⟨subd7_6_374, List.forall_mem_cons.2 ⟨subd7_6_375, List.forall_mem_cons.2 ⟨subd7_6_376, List.forall_mem_cons.2 ⟨subd7_6_377, List.forall_mem_cons.2 ⟨subd7_6_378, List.forall_mem_cons.2 ⟨subd7_6_379, List.forall_mem_cons.2 ⟨subd7_6_380, List.forall_mem_cons.2 ⟨subd7_6_381, List.forall_mem_cons.2 ⟨subd7_6_382, List.forall_mem_cons.2 ⟨subd7_6_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_6_384 : subd7_6 [1, 1, 2] = true := by decide +kernel
theorem subd7_6_385 : subd7_6 [1, 1, 3] = true := by decide +kernel
theorem subd7_6_386 : subd7_6 [1, 1, 4] = true := by decide +kernel
theorem subd7_6_387 : subd7_6 [1, 1, 5] = true := by decide +kernel
theorem subd7_6_388 : subd7_6 [1, 1, 6] = true := by decide +kernel
theorem subd7_6_389 : subd7_6 [1, 2, -8] = true := by decide +kernel
theorem subd7_6_390 : subd7_6 [1, 2, -7] = true := by decide +kernel
theorem subd7_6_391 : subd7_6 [1, 2, -6] = true := by decide +kernel
theorem subd7_6_392 : subd7_6 [1, 2, -5] = true := by decide +kernel
theorem subd7_6_393 : subd7_6 [1, 2, -4] = true := by decide +kernel
theorem subd7_6_394 : subd7_6 [1, 2, -3] = true := by decide +kernel
theorem subd7_6_395 : subd7_6 [1, 2, -2] = true := by decide +kernel
theorem subd7_6_396 : subd7_6 [1, 2, -1] = true := by decide +kernel
theorem subd7_6_397 : subd7_6 [1, 2, 0] = true := by decide +kernel
theorem subd7_6_398 : subd7_6 [1, 2, 1] = true := by decide +kernel
theorem subd7_6_399 : subd7_6 [1, 2, 2] = true := by decide +kernel
theorem subd7_6_400 : subd7_6 [1, 2, 3] = true := by decide +kernel
theorem subd7_6_401 : subd7_6 [1, 2, 4] = true := by decide +kernel
theorem subd7_6_402 : subd7_6 [1, 2, 5] = true := by decide +kernel
theorem subd7_6_403 : subd7_6 [1, 2, 6] = true := by decide +kernel
theorem subd7_6_404 : subd7_6 [1, 3, -7] = true := by decide +kernel
theorem subd7_6_405 : subd7_6 [1, 3, -6] = true := by decide +kernel
theorem subd7_6_406 : subd7_6 [1, 3, -5] = true := by decide +kernel
theorem subd7_6_407 : subd7_6 [1, 3, -4] = true := by decide +kernel
theorem subd7_6_408 : subd7_6 [1, 3, -3] = true := by decide +kernel
theorem subd7_6_409 : subd7_6 [1, 3, -2] = true := by decide +kernel
theorem subd7_6_410 : subd7_6 [1, 3, -1] = true := by decide +kernel
theorem subd7_6_411 : subd7_6 [1, 3, 0] = true := by decide +kernel
theorem subd7_6_412 : subd7_6 [1, 3, 1] = true := by decide +kernel
theorem subd7_6_413 : subd7_6 [1, 3, 2] = true := by decide +kernel
theorem subd7_6_414 : subd7_6 [1, 3, 3] = true := by decide +kernel
theorem subd7_6_415 : subd7_6 [1, 3, 4] = true := by decide +kernel
theorem sbd7_6_12 : ∀ q ∈ blkd7_6_12, subd7_6 q = true := by
  unfold blkd7_6_12
  exact List.forall_mem_cons.2 ⟨subd7_6_384, List.forall_mem_cons.2 ⟨subd7_6_385, List.forall_mem_cons.2 ⟨subd7_6_386, List.forall_mem_cons.2 ⟨subd7_6_387, List.forall_mem_cons.2 ⟨subd7_6_388, List.forall_mem_cons.2 ⟨subd7_6_389, List.forall_mem_cons.2 ⟨subd7_6_390, List.forall_mem_cons.2 ⟨subd7_6_391, List.forall_mem_cons.2 ⟨subd7_6_392, List.forall_mem_cons.2 ⟨subd7_6_393, List.forall_mem_cons.2 ⟨subd7_6_394, List.forall_mem_cons.2 ⟨subd7_6_395, List.forall_mem_cons.2 ⟨subd7_6_396, List.forall_mem_cons.2 ⟨subd7_6_397, List.forall_mem_cons.2 ⟨subd7_6_398, List.forall_mem_cons.2 ⟨subd7_6_399, List.forall_mem_cons.2 ⟨subd7_6_400, List.forall_mem_cons.2 ⟨subd7_6_401, List.forall_mem_cons.2 ⟨subd7_6_402, List.forall_mem_cons.2 ⟨subd7_6_403, List.forall_mem_cons.2 ⟨subd7_6_404, List.forall_mem_cons.2 ⟨subd7_6_405, List.forall_mem_cons.2 ⟨subd7_6_406, List.forall_mem_cons.2 ⟨subd7_6_407, List.forall_mem_cons.2 ⟨subd7_6_408, List.forall_mem_cons.2 ⟨subd7_6_409, List.forall_mem_cons.2 ⟨subd7_6_410, List.forall_mem_cons.2 ⟨subd7_6_411, List.forall_mem_cons.2 ⟨subd7_6_412, List.forall_mem_cons.2 ⟨subd7_6_413, List.forall_mem_cons.2 ⟨subd7_6_414, List.forall_mem_cons.2 ⟨subd7_6_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_6_416 : subd7_6 [1, 3, 5] = true := by decide +kernel
theorem subd7_6_417 : subd7_6 [1, 4] = true := by decide +kernel
theorem subd7_6_418 : subd7_6 [1, 5] = true := by decide +kernel
theorem subd7_6_419 : subd7_6 [1, 6] = true := by decide +kernel
theorem subd7_6_420 : subd7_6 [1, 7] = true := by decide +kernel
theorem subd7_6_421 : subd7_6 [2, -6] = true := by decide +kernel
theorem subd7_6_422 : subd7_6 [2, -5] = true := by decide +kernel
theorem subd7_6_423 : subd7_6 [2, -4] = true := by decide +kernel
theorem subd7_6_424 : subd7_6 [2, -3] = true := by decide +kernel
theorem subd7_6_425 : subd7_6 [2, -2] = true := by decide +kernel
theorem subd7_6_426 : subd7_6 [2, -1, -7] = true := by decide +kernel
theorem subd7_6_427 : subd7_6 [2, -1, -6] = true := by decide +kernel
theorem subd7_6_428 : subd7_6 [2, -1, -5] = true := by decide +kernel
theorem subd7_6_429 : subd7_6 [2, -1, -4] = true := by decide +kernel
theorem subd7_6_430 : subd7_6 [2, -1, -3] = true := by decide +kernel
theorem subd7_6_431 : subd7_6 [2, -1, -2] = true := by decide +kernel
theorem subd7_6_432 : subd7_6 [2, -1, -1] = true := by decide +kernel
theorem subd7_6_433 : subd7_6 [2, -1, 0] = true := by decide +kernel
theorem subd7_6_434 : subd7_6 [2, -1, 1] = true := by decide +kernel
theorem subd7_6_435 : subd7_6 [2, -1, 2] = true := by decide +kernel
theorem subd7_6_436 : subd7_6 [2, -1, 3] = true := by decide +kernel
theorem subd7_6_437 : subd7_6 [2, -1, 4] = true := by decide +kernel
theorem subd7_6_438 : subd7_6 [2, -1, 5] = true := by decide +kernel
theorem subd7_6_439 : subd7_6 [2, -1, 6] = true := by decide +kernel
theorem subd7_6_440 : subd7_6 [2, 0, -7] = true := by decide +kernel
theorem subd7_6_441 : subd7_6 [2, 0, -6] = true := by decide +kernel
theorem subd7_6_442 : subd7_6 [2, 0, -5] = true := by decide +kernel
theorem subd7_6_443 : subd7_6 [2, 0, -4] = true := by decide +kernel
theorem subd7_6_444 : subd7_6 [2, 0, -3] = true := by decide +kernel
theorem subd7_6_445 : subd7_6 [2, 0, -2] = true := by decide +kernel
theorem subd7_6_446 : subd7_6 [2, 0, -1] = true := by decide +kernel
theorem subd7_6_447 : subd7_6 [2, 0, 0] = true := by decide +kernel
theorem sbd7_6_13 : ∀ q ∈ blkd7_6_13, subd7_6 q = true := by
  unfold blkd7_6_13
  exact List.forall_mem_cons.2 ⟨subd7_6_416, List.forall_mem_cons.2 ⟨subd7_6_417, List.forall_mem_cons.2 ⟨subd7_6_418, List.forall_mem_cons.2 ⟨subd7_6_419, List.forall_mem_cons.2 ⟨subd7_6_420, List.forall_mem_cons.2 ⟨subd7_6_421, List.forall_mem_cons.2 ⟨subd7_6_422, List.forall_mem_cons.2 ⟨subd7_6_423, List.forall_mem_cons.2 ⟨subd7_6_424, List.forall_mem_cons.2 ⟨subd7_6_425, List.forall_mem_cons.2 ⟨subd7_6_426, List.forall_mem_cons.2 ⟨subd7_6_427, List.forall_mem_cons.2 ⟨subd7_6_428, List.forall_mem_cons.2 ⟨subd7_6_429, List.forall_mem_cons.2 ⟨subd7_6_430, List.forall_mem_cons.2 ⟨subd7_6_431, List.forall_mem_cons.2 ⟨subd7_6_432, List.forall_mem_cons.2 ⟨subd7_6_433, List.forall_mem_cons.2 ⟨subd7_6_434, List.forall_mem_cons.2 ⟨subd7_6_435, List.forall_mem_cons.2 ⟨subd7_6_436, List.forall_mem_cons.2 ⟨subd7_6_437, List.forall_mem_cons.2 ⟨subd7_6_438, List.forall_mem_cons.2 ⟨subd7_6_439, List.forall_mem_cons.2 ⟨subd7_6_440, List.forall_mem_cons.2 ⟨subd7_6_441, List.forall_mem_cons.2 ⟨subd7_6_442, List.forall_mem_cons.2 ⟨subd7_6_443, List.forall_mem_cons.2 ⟨subd7_6_444, List.forall_mem_cons.2 ⟨subd7_6_445, List.forall_mem_cons.2 ⟨subd7_6_446, List.forall_mem_cons.2 ⟨subd7_6_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_6_448 : subd7_6 [2, 0, 1] = true := by decide +kernel
theorem subd7_6_449 : subd7_6 [2, 0, 2] = true := by decide +kernel
theorem subd7_6_450 : subd7_6 [2, 0, 3] = true := by decide +kernel
theorem subd7_6_451 : subd7_6 [2, 0, 4] = true := by decide +kernel
theorem subd7_6_452 : subd7_6 [2, 0, 5] = true := by decide +kernel
theorem subd7_6_453 : subd7_6 [2, 0, 6] = true := by decide +kernel
theorem subd7_6_454 : subd7_6 [2, 1, -7] = true := by decide +kernel
theorem subd7_6_455 : subd7_6 [2, 1, -6] = true := by decide +kernel
theorem subd7_6_456 : subd7_6 [2, 1, -5] = true := by decide +kernel
theorem subd7_6_457 : subd7_6 [2, 1, -4] = true := by decide +kernel
theorem subd7_6_458 : subd7_6 [2, 1, -3] = true := by decide +kernel
theorem subd7_6_459 : subd7_6 [2, 1, -2] = true := by decide +kernel
theorem subd7_6_460 : subd7_6 [2, 1, -1] = true := by decide +kernel
theorem subd7_6_461 : subd7_6 [2, 1, 0] = true := by decide +kernel
theorem subd7_6_462 : subd7_6 [2, 1, 1] = true := by decide +kernel
theorem subd7_6_463 : subd7_6 [2, 1, 2] = true := by decide +kernel
theorem subd7_6_464 : subd7_6 [2, 1, 3] = true := by decide +kernel
theorem subd7_6_465 : subd7_6 [2, 1, 4] = true := by decide +kernel
theorem subd7_6_466 : subd7_6 [2, 1, 5] = true := by decide +kernel
theorem subd7_6_467 : subd7_6 [2, 1, 6] = true := by decide +kernel
theorem subd7_6_468 : subd7_6 [2, 2, -7] = true := by decide +kernel
theorem subd7_6_469 : subd7_6 [2, 2, -6] = true := by decide +kernel
theorem subd7_6_470 : subd7_6 [2, 2, -5] = true := by decide +kernel
theorem subd7_6_471 : subd7_6 [2, 2, -4] = true := by decide +kernel
theorem subd7_6_472 : subd7_6 [2, 2, -3] = true := by decide +kernel
theorem subd7_6_473 : subd7_6 [2, 2, -2] = true := by decide +kernel
theorem subd7_6_474 : subd7_6 [2, 2, -1] = true := by decide +kernel
theorem subd7_6_475 : subd7_6 [2, 2, 0] = true := by decide +kernel
theorem subd7_6_476 : subd7_6 [2, 2, 1] = true := by decide +kernel
theorem subd7_6_477 : subd7_6 [2, 2, 2] = true := by decide +kernel
theorem subd7_6_478 : subd7_6 [2, 2, 3] = true := by decide +kernel
theorem subd7_6_479 : subd7_6 [2, 2, 4] = true := by decide +kernel
theorem sbd7_6_14 : ∀ q ∈ blkd7_6_14, subd7_6 q = true := by
  unfold blkd7_6_14
  exact List.forall_mem_cons.2 ⟨subd7_6_448, List.forall_mem_cons.2 ⟨subd7_6_449, List.forall_mem_cons.2 ⟨subd7_6_450, List.forall_mem_cons.2 ⟨subd7_6_451, List.forall_mem_cons.2 ⟨subd7_6_452, List.forall_mem_cons.2 ⟨subd7_6_453, List.forall_mem_cons.2 ⟨subd7_6_454, List.forall_mem_cons.2 ⟨subd7_6_455, List.forall_mem_cons.2 ⟨subd7_6_456, List.forall_mem_cons.2 ⟨subd7_6_457, List.forall_mem_cons.2 ⟨subd7_6_458, List.forall_mem_cons.2 ⟨subd7_6_459, List.forall_mem_cons.2 ⟨subd7_6_460, List.forall_mem_cons.2 ⟨subd7_6_461, List.forall_mem_cons.2 ⟨subd7_6_462, List.forall_mem_cons.2 ⟨subd7_6_463, List.forall_mem_cons.2 ⟨subd7_6_464, List.forall_mem_cons.2 ⟨subd7_6_465, List.forall_mem_cons.2 ⟨subd7_6_466, List.forall_mem_cons.2 ⟨subd7_6_467, List.forall_mem_cons.2 ⟨subd7_6_468, List.forall_mem_cons.2 ⟨subd7_6_469, List.forall_mem_cons.2 ⟨subd7_6_470, List.forall_mem_cons.2 ⟨subd7_6_471, List.forall_mem_cons.2 ⟨subd7_6_472, List.forall_mem_cons.2 ⟨subd7_6_473, List.forall_mem_cons.2 ⟨subd7_6_474, List.forall_mem_cons.2 ⟨subd7_6_475, List.forall_mem_cons.2 ⟨subd7_6_476, List.forall_mem_cons.2 ⟨subd7_6_477, List.forall_mem_cons.2 ⟨subd7_6_478, List.forall_mem_cons.2 ⟨subd7_6_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_6_480 : subd7_6 [2, 2, 5] = true := by decide +kernel
theorem subd7_6_481 : subd7_6 [2, 3, -7] = true := by decide +kernel
theorem subd7_6_482 : subd7_6 [2, 3, -6] = true := by decide +kernel
theorem subd7_6_483 : subd7_6 [2, 3, -5] = true := by decide +kernel
theorem subd7_6_484 : subd7_6 [2, 3, -4] = true := by decide +kernel
theorem subd7_6_485 : subd7_6 [2, 3, -3] = true := by decide +kernel
theorem subd7_6_486 : subd7_6 [2, 3, -2] = true := by decide +kernel
theorem subd7_6_487 : subd7_6 [2, 3, -1] = true := by decide +kernel
theorem subd7_6_488 : subd7_6 [2, 3, 0] = true := by decide +kernel
theorem subd7_6_489 : subd7_6 [2, 3, 1] = true := by decide +kernel
theorem subd7_6_490 : subd7_6 [2, 3, 2] = true := by decide +kernel
theorem subd7_6_491 : subd7_6 [2, 3, 3] = true := by decide +kernel
theorem subd7_6_492 : subd7_6 [2, 3, 4] = true := by decide +kernel
theorem subd7_6_493 : subd7_6 [2, 3, 5] = true := by decide +kernel
theorem subd7_6_494 : subd7_6 [2, 4] = true := by decide +kernel
theorem subd7_6_495 : subd7_6 [2, 5] = true := by decide +kernel
theorem subd7_6_496 : subd7_6 [2, 6] = true := by decide +kernel
theorem subd7_6_497 : subd7_6 [2, 7] = true := by decide +kernel
theorem subd7_6_498 : subd7_6 [3, -6] = true := by decide +kernel
theorem subd7_6_499 : subd7_6 [3, -5] = true := by decide +kernel
theorem subd7_6_500 : subd7_6 [3, -4] = true := by decide +kernel
theorem subd7_6_501 : subd7_6 [3, -3] = true := by decide +kernel
theorem subd7_6_502 : subd7_6 [3, -2] = true := by decide +kernel
theorem subd7_6_503 : subd7_6 [3, -1] = true := by decide +kernel
theorem subd7_6_504 : subd7_6 [3, 0] = true := by decide +kernel
theorem subd7_6_505 : subd7_6 [3, 1, -7] = true := by decide +kernel
theorem subd7_6_506 : subd7_6 [3, 1, -6] = true := by decide +kernel
theorem subd7_6_507 : subd7_6 [3, 1, -5] = true := by decide +kernel
theorem subd7_6_508 : subd7_6 [3, 1, -4] = true := by decide +kernel
theorem subd7_6_509 : subd7_6 [3, 1, -3] = true := by decide +kernel
theorem subd7_6_510 : subd7_6 [3, 1, -2] = true := by decide +kernel
theorem subd7_6_511 : subd7_6 [3, 1, -1] = true := by decide +kernel
theorem sbd7_6_15 : ∀ q ∈ blkd7_6_15, subd7_6 q = true := by
  unfold blkd7_6_15
  exact List.forall_mem_cons.2 ⟨subd7_6_480, List.forall_mem_cons.2 ⟨subd7_6_481, List.forall_mem_cons.2 ⟨subd7_6_482, List.forall_mem_cons.2 ⟨subd7_6_483, List.forall_mem_cons.2 ⟨subd7_6_484, List.forall_mem_cons.2 ⟨subd7_6_485, List.forall_mem_cons.2 ⟨subd7_6_486, List.forall_mem_cons.2 ⟨subd7_6_487, List.forall_mem_cons.2 ⟨subd7_6_488, List.forall_mem_cons.2 ⟨subd7_6_489, List.forall_mem_cons.2 ⟨subd7_6_490, List.forall_mem_cons.2 ⟨subd7_6_491, List.forall_mem_cons.2 ⟨subd7_6_492, List.forall_mem_cons.2 ⟨subd7_6_493, List.forall_mem_cons.2 ⟨subd7_6_494, List.forall_mem_cons.2 ⟨subd7_6_495, List.forall_mem_cons.2 ⟨subd7_6_496, List.forall_mem_cons.2 ⟨subd7_6_497, List.forall_mem_cons.2 ⟨subd7_6_498, List.forall_mem_cons.2 ⟨subd7_6_499, List.forall_mem_cons.2 ⟨subd7_6_500, List.forall_mem_cons.2 ⟨subd7_6_501, List.forall_mem_cons.2 ⟨subd7_6_502, List.forall_mem_cons.2 ⟨subd7_6_503, List.forall_mem_cons.2 ⟨subd7_6_504, List.forall_mem_cons.2 ⟨subd7_6_505, List.forall_mem_cons.2 ⟨subd7_6_506, List.forall_mem_cons.2 ⟨subd7_6_507, List.forall_mem_cons.2 ⟨subd7_6_508, List.forall_mem_cons.2 ⟨subd7_6_509, List.forall_mem_cons.2 ⟨subd7_6_510, List.forall_mem_cons.2 ⟨subd7_6_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_6_512 : subd7_6 [3, 1, 0] = true := by decide +kernel
theorem subd7_6_513 : subd7_6 [3, 1, 1] = true := by decide +kernel
theorem subd7_6_514 : subd7_6 [3, 1, 2] = true := by decide +kernel
theorem subd7_6_515 : subd7_6 [3, 1, 3] = true := by decide +kernel
theorem subd7_6_516 : subd7_6 [3, 1, 4] = true := by decide +kernel
theorem subd7_6_517 : subd7_6 [3, 1, 5] = true := by decide +kernel
theorem subd7_6_518 : subd7_6 [3, 2] = true := by decide +kernel
theorem subd7_6_519 : subd7_6 [3, 3] = true := by decide +kernel
theorem subd7_6_520 : subd7_6 [3, 4] = true := by decide +kernel
theorem subd7_6_521 : subd7_6 [3, 5] = true := by decide +kernel
theorem subd7_6_522 : subd7_6 [3, 6] = true := by decide +kernel
theorem subd7_6_523 : subd7_6 [3, 7] = true := by decide +kernel
theorem subd7_6_524 : subd7_6 [4, -5] = true := by decide +kernel
theorem subd7_6_525 : subd7_6 [4, -4] = true := by decide +kernel
theorem subd7_6_526 : subd7_6 [4, -3] = true := by decide +kernel
theorem subd7_6_527 : subd7_6 [4, -2] = true := by decide +kernel
theorem subd7_6_528 : subd7_6 [4, -1] = true := by decide +kernel
theorem subd7_6_529 : subd7_6 [4, 0] = true := by decide +kernel
theorem subd7_6_530 : subd7_6 [4, 1] = true := by decide +kernel
theorem subd7_6_531 : subd7_6 [4, 2] = true := by decide +kernel
theorem subd7_6_532 : subd7_6 [4, 3] = true := by decide +kernel
theorem subd7_6_533 : subd7_6 [4, 4] = true := by decide +kernel
theorem subd7_6_534 : subd7_6 [4, 5] = true := by decide +kernel
theorem subd7_6_535 : subd7_6 [4, 6] = true := by decide +kernel
theorem subd7_6_536 : subd7_6 [5, -3] = true := by decide +kernel
theorem subd7_6_537 : subd7_6 [5, -2] = true := by decide +kernel
theorem subd7_6_538 : subd7_6 [5, -1] = true := by decide +kernel
theorem subd7_6_539 : subd7_6 [5, 0] = true := by decide +kernel
theorem subd7_6_540 : subd7_6 [5, 1] = true := by decide +kernel
theorem subd7_6_541 : subd7_6 [5, 2] = true := by decide +kernel
theorem subd7_6_542 : subd7_6 [5, 3] = true := by decide +kernel
theorem subd7_6_543 : subd7_6 [5, 4] = true := by decide +kernel
theorem sbd7_6_16 : ∀ q ∈ blkd7_6_16, subd7_6 q = true := by
  unfold blkd7_6_16
  exact List.forall_mem_cons.2 ⟨subd7_6_512, List.forall_mem_cons.2 ⟨subd7_6_513, List.forall_mem_cons.2 ⟨subd7_6_514, List.forall_mem_cons.2 ⟨subd7_6_515, List.forall_mem_cons.2 ⟨subd7_6_516, List.forall_mem_cons.2 ⟨subd7_6_517, List.forall_mem_cons.2 ⟨subd7_6_518, List.forall_mem_cons.2 ⟨subd7_6_519, List.forall_mem_cons.2 ⟨subd7_6_520, List.forall_mem_cons.2 ⟨subd7_6_521, List.forall_mem_cons.2 ⟨subd7_6_522, List.forall_mem_cons.2 ⟨subd7_6_523, List.forall_mem_cons.2 ⟨subd7_6_524, List.forall_mem_cons.2 ⟨subd7_6_525, List.forall_mem_cons.2 ⟨subd7_6_526, List.forall_mem_cons.2 ⟨subd7_6_527, List.forall_mem_cons.2 ⟨subd7_6_528, List.forall_mem_cons.2 ⟨subd7_6_529, List.forall_mem_cons.2 ⟨subd7_6_530, List.forall_mem_cons.2 ⟨subd7_6_531, List.forall_mem_cons.2 ⟨subd7_6_532, List.forall_mem_cons.2 ⟨subd7_6_533, List.forall_mem_cons.2 ⟨subd7_6_534, List.forall_mem_cons.2 ⟨subd7_6_535, List.forall_mem_cons.2 ⟨subd7_6_536, List.forall_mem_cons.2 ⟨subd7_6_537, List.forall_mem_cons.2 ⟨subd7_6_538, List.forall_mem_cons.2 ⟨subd7_6_539, List.forall_mem_cons.2 ⟨subd7_6_540, List.forall_mem_cons.2 ⟨subd7_6_541, List.forall_mem_cons.2 ⟨subd7_6_542, List.forall_mem_cons.2 ⟨subd7_6_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_6_544 : subd7_6 [5, 5] = true := by decide +kernel
theorem subd7_6_545 : subd7_6 [5, 6] = true := by decide +kernel
theorem subd7_6_546 : subd7_6 [6] = true := by decide +kernel
theorem sbd7_6_17 : ∀ q ∈ blkd7_6_17, subd7_6 q = true := by
  unfold blkd7_6_17
  exact List.forall_mem_cons.2 ⟨subd7_6_544, List.forall_mem_cons.2 ⟨subd7_6_545, List.forall_mem_cons.2 ⟨subd7_6_546, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd7_7 : ldCheck G d7_7.U d7_7.ms ldd7_7 = true := by decide +kernel
theorem pre_okd7_7 : subPre G cell7 d7_7 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C128
