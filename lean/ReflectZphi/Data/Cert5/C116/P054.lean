import ReflectZphi.Data.Cert5.C116.Base

namespace ReflectZphi.Data.Cert5.C116

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd11_1_320 : subd11_1 [-1, 3, 1] = true := by decide +kernel
theorem subd11_1_321 : subd11_1 [-1, 3, 2] = true := by decide +kernel
theorem subd11_1_322 : subd11_1 [-1, 3, 3] = true := by decide +kernel
theorem subd11_1_323 : subd11_1 [-1, 3, 4] = true := by decide +kernel
theorem subd11_1_324 : subd11_1 [-1, 3, 5] = true := by decide +kernel
theorem subd11_1_325 : subd11_1 [-1, 3, 6] = true := by decide +kernel
theorem subd11_1_326 : subd11_1 [-1, 3, 7] = true := by decide +kernel
theorem subd11_1_327 : subd11_1 [-1, 4, -9] = true := by decide +kernel
theorem subd11_1_328 : subd11_1 [-1, 4, -8] = true := by decide +kernel
theorem subd11_1_329 : subd11_1 [-1, 4, -7] = true := by decide +kernel
theorem subd11_1_330 : subd11_1 [-1, 4, -6] = true := by decide +kernel
theorem subd11_1_331 : subd11_1 [-1, 4, -5] = true := by decide +kernel
theorem subd11_1_332 : subd11_1 [-1, 4, -4] = true := by decide +kernel
theorem subd11_1_333 : subd11_1 [-1, 4, -3] = true := by decide +kernel
theorem subd11_1_334 : subd11_1 [-1, 4, -2] = true := by decide +kernel
theorem subd11_1_335 : subd11_1 [-1, 4, -1] = true := by decide +kernel
theorem subd11_1_336 : subd11_1 [-1, 4, 0] = true := by decide +kernel
theorem subd11_1_337 : subd11_1 [-1, 4, 1] = true := by decide +kernel
theorem subd11_1_338 : subd11_1 [-1, 4, 2] = true := by decide +kernel
theorem subd11_1_339 : subd11_1 [-1, 4, 3] = true := by decide +kernel
theorem subd11_1_340 : subd11_1 [-1, 4, 4] = true := by decide +kernel
theorem subd11_1_341 : subd11_1 [-1, 4, 5] = true := by decide +kernel
theorem subd11_1_342 : subd11_1 [-1, 4, 6] = true := by decide +kernel
theorem subd11_1_343 : subd11_1 [-1, 5] = true := by decide +kernel
theorem subd11_1_344 : subd11_1 [0, -6] = true := by decide +kernel
theorem subd11_1_345 : subd11_1 [0, -5] = true := by decide +kernel
theorem subd11_1_346 : subd11_1 [0, -4, -6] = true := by decide +kernel
theorem subd11_1_347 : subd11_1 [0, -4, -5] = true := by decide +kernel
theorem subd11_1_348 : subd11_1 [0, -4, -4] = true := by decide +kernel
theorem subd11_1_349 : subd11_1 [0, -4, -3] = true := by decide +kernel
theorem subd11_1_350 : subd11_1 [0, -4, -2] = true := by decide +kernel
theorem subd11_1_351 : subd11_1 [0, -4, -1] = true := by decide +kernel
theorem sbd11_1_10 : ∀ q ∈ blkd11_1_10, subd11_1 q = true := by
  unfold blkd11_1_10
  exact List.forall_mem_cons.2 ⟨subd11_1_320, List.forall_mem_cons.2 ⟨subd11_1_321, List.forall_mem_cons.2 ⟨subd11_1_322, List.forall_mem_cons.2 ⟨subd11_1_323, List.forall_mem_cons.2 ⟨subd11_1_324, List.forall_mem_cons.2 ⟨subd11_1_325, List.forall_mem_cons.2 ⟨subd11_1_326, List.forall_mem_cons.2 ⟨subd11_1_327, List.forall_mem_cons.2 ⟨subd11_1_328, List.forall_mem_cons.2 ⟨subd11_1_329, List.forall_mem_cons.2 ⟨subd11_1_330, List.forall_mem_cons.2 ⟨subd11_1_331, List.forall_mem_cons.2 ⟨subd11_1_332, List.forall_mem_cons.2 ⟨subd11_1_333, List.forall_mem_cons.2 ⟨subd11_1_334, List.forall_mem_cons.2 ⟨subd11_1_335, List.forall_mem_cons.2 ⟨subd11_1_336, List.forall_mem_cons.2 ⟨subd11_1_337, List.forall_mem_cons.2 ⟨subd11_1_338, List.forall_mem_cons.2 ⟨subd11_1_339, List.forall_mem_cons.2 ⟨subd11_1_340, List.forall_mem_cons.2 ⟨subd11_1_341, List.forall_mem_cons.2 ⟨subd11_1_342, List.forall_mem_cons.2 ⟨subd11_1_343, List.forall_mem_cons.2 ⟨subd11_1_344, List.forall_mem_cons.2 ⟨subd11_1_345, List.forall_mem_cons.2 ⟨subd11_1_346, List.forall_mem_cons.2 ⟨subd11_1_347, List.forall_mem_cons.2 ⟨subd11_1_348, List.forall_mem_cons.2 ⟨subd11_1_349, List.forall_mem_cons.2 ⟨subd11_1_350, List.forall_mem_cons.2 ⟨subd11_1_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_352 : subd11_1 [0, -4, 0] = true := by decide +kernel
theorem subd11_1_353 : subd11_1 [0, -4, 1] = true := by decide +kernel
theorem subd11_1_354 : subd11_1 [0, -4, 2] = true := by decide +kernel
theorem subd11_1_355 : subd11_1 [0, -4, 3] = true := by decide +kernel
theorem subd11_1_356 : subd11_1 [0, -4, 4] = true := by decide +kernel
theorem subd11_1_357 : subd11_1 [0, -4, 5] = true := by decide +kernel
theorem subd11_1_358 : subd11_1 [0, -4, 6] = true := by decide +kernel
theorem subd11_1_359 : subd11_1 [0, -4, 7] = true := by decide +kernel
theorem subd11_1_360 : subd11_1 [0, -3, -8] = true := by decide +kernel
theorem subd11_1_361 : subd11_1 [0, -3, -7] = true := by decide +kernel
theorem subd11_1_362 : subd11_1 [0, -3, -6] = true := by decide +kernel
theorem subd11_1_363 : subd11_1 [0, -3, -5] = true := by decide +kernel
theorem subd11_1_364 : subd11_1 [0, -3, -4] = true := by decide +kernel
theorem subd11_1_365 : subd11_1 [0, -3, -3] = true := by decide +kernel
theorem subd11_1_366 : subd11_1 [0, -3, -2] = true := by decide +kernel
theorem subd11_1_367 : subd11_1 [0, -3, -1] = true := by decide +kernel
theorem subd11_1_368 : subd11_1 [0, -3, 0] = true := by decide +kernel
theorem subd11_1_369 : subd11_1 [0, -3, 1] = true := by decide +kernel
theorem subd11_1_370 : subd11_1 [0, -3, 2] = true := by decide +kernel
theorem subd11_1_371 : subd11_1 [0, -3, 3] = true := by decide +kernel
theorem subd11_1_372 : subd11_1 [0, -3, 4] = true := by decide +kernel
theorem subd11_1_373 : subd11_1 [0, -3, 5] = true := by decide +kernel
theorem subd11_1_374 : subd11_1 [0, -3, 6] = true := by decide +kernel
theorem subd11_1_375 : subd11_1 [0, -3, 7] = true := by decide +kernel
theorem subd11_1_376 : subd11_1 [0, -3, 8] = true := by decide +kernel
theorem subd11_1_377 : subd11_1 [0, -2, -9] = true := by decide +kernel
theorem subd11_1_378 : subd11_1 [0, -2, -8] = true := by decide +kernel
theorem subd11_1_379 : subd11_1 [0, -2, -7] = true := by decide +kernel
theorem subd11_1_380 : subd11_1 [0, -2, -6] = true := by decide +kernel
theorem subd11_1_381 : subd11_1 [0, -2, -5] = true := by decide +kernel
theorem subd11_1_382 : subd11_1 [0, -2, -4] = true := by decide +kernel
theorem subd11_1_383 : subd11_1 [0, -2, -3] = true := by decide +kernel
theorem sbd11_1_11 : ∀ q ∈ blkd11_1_11, subd11_1 q = true := by
  unfold blkd11_1_11
  exact List.forall_mem_cons.2 ⟨subd11_1_352, List.forall_mem_cons.2 ⟨subd11_1_353, List.forall_mem_cons.2 ⟨subd11_1_354, List.forall_mem_cons.2 ⟨subd11_1_355, List.forall_mem_cons.2 ⟨subd11_1_356, List.forall_mem_cons.2 ⟨subd11_1_357, List.forall_mem_cons.2 ⟨subd11_1_358, List.forall_mem_cons.2 ⟨subd11_1_359, List.forall_mem_cons.2 ⟨subd11_1_360, List.forall_mem_cons.2 ⟨subd11_1_361, List.forall_mem_cons.2 ⟨subd11_1_362, List.forall_mem_cons.2 ⟨subd11_1_363, List.forall_mem_cons.2 ⟨subd11_1_364, List.forall_mem_cons.2 ⟨subd11_1_365, List.forall_mem_cons.2 ⟨subd11_1_366, List.forall_mem_cons.2 ⟨subd11_1_367, List.forall_mem_cons.2 ⟨subd11_1_368, List.forall_mem_cons.2 ⟨subd11_1_369, List.forall_mem_cons.2 ⟨subd11_1_370, List.forall_mem_cons.2 ⟨subd11_1_371, List.forall_mem_cons.2 ⟨subd11_1_372, List.forall_mem_cons.2 ⟨subd11_1_373, List.forall_mem_cons.2 ⟨subd11_1_374, List.forall_mem_cons.2 ⟨subd11_1_375, List.forall_mem_cons.2 ⟨subd11_1_376, List.forall_mem_cons.2 ⟨subd11_1_377, List.forall_mem_cons.2 ⟨subd11_1_378, List.forall_mem_cons.2 ⟨subd11_1_379, List.forall_mem_cons.2 ⟨subd11_1_380, List.forall_mem_cons.2 ⟨subd11_1_381, List.forall_mem_cons.2 ⟨subd11_1_382, List.forall_mem_cons.2 ⟨subd11_1_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_384 : subd11_1 [0, -2, -2] = true := by decide +kernel
theorem subd11_1_385 : subd11_1 [0, -2, -1] = true := by decide +kernel
theorem subd11_1_386 : subd11_1 [0, -2, 0] = true := by decide +kernel
theorem subd11_1_387 : subd11_1 [0, -2, 1] = true := by decide +kernel
theorem subd11_1_388 : subd11_1 [0, -2, 2] = true := by decide +kernel
theorem subd11_1_389 : subd11_1 [0, -2, 3] = true := by decide +kernel
theorem subd11_1_390 : subd11_1 [0, -2, 4] = true := by decide +kernel
theorem subd11_1_391 : subd11_1 [0, -2, 5] = true := by decide +kernel
theorem subd11_1_392 : subd11_1 [0, -2, 6] = true := by decide +kernel
theorem subd11_1_393 : subd11_1 [0, -2, 7] = true := by decide +kernel
theorem subd11_1_394 : subd11_1 [0, -2, 8] = true := by decide +kernel
theorem subd11_1_395 : subd11_1 [0, -2, 9] = true := by decide +kernel
theorem subd11_1_396 : subd11_1 [0, -1, -10] = true := by decide +kernel
theorem subd11_1_397 : subd11_1 [0, -1, -9] = true := by decide +kernel
theorem subd11_1_398 : subd11_1 [0, -1, -8] = true := by decide +kernel
theorem subd11_1_399 : subd11_1 [0, -1, -7] = true := by decide +kernel
theorem subd11_1_400 : subd11_1 [0, -1, -6] = true := by decide +kernel
theorem subd11_1_401 : subd11_1 [0, -1, -5] = true := by decide +kernel
theorem subd11_1_402 : subd11_1 [0, -1, -4] = true := by decide +kernel
theorem subd11_1_403 : subd11_1 [0, -1, -3] = true := by decide +kernel
theorem subd11_1_404 : subd11_1 [0, -1, -2] = true := by decide +kernel
theorem subd11_1_405 : subd11_1 [0, -1, -1] = true := by decide +kernel
theorem subd11_1_406 : subd11_1 [0, -1, 0] = true := by decide +kernel
theorem subd11_1_407 : subd11_1 [0, -1, 1] = true := by decide +kernel
theorem subd11_1_408 : subd11_1 [0, -1, 2] = true := by decide +kernel
theorem subd11_1_409 : subd11_1 [0, -1, 3] = true := by decide +kernel
theorem subd11_1_410 : subd11_1 [0, -1, 4] = true := by decide +kernel
theorem subd11_1_411 : subd11_1 [0, -1, 5] = true := by decide +kernel
theorem subd11_1_412 : subd11_1 [0, -1, 6] = true := by decide +kernel
theorem subd11_1_413 : subd11_1 [0, -1, 7] = true := by decide +kernel
theorem subd11_1_414 : subd11_1 [0, -1, 8] = true := by decide +kernel
theorem subd11_1_415 : subd11_1 [0, -1, 9] = true := by decide +kernel
theorem sbd11_1_12 : ∀ q ∈ blkd11_1_12, subd11_1 q = true := by
  unfold blkd11_1_12
  exact List.forall_mem_cons.2 ⟨subd11_1_384, List.forall_mem_cons.2 ⟨subd11_1_385, List.forall_mem_cons.2 ⟨subd11_1_386, List.forall_mem_cons.2 ⟨subd11_1_387, List.forall_mem_cons.2 ⟨subd11_1_388, List.forall_mem_cons.2 ⟨subd11_1_389, List.forall_mem_cons.2 ⟨subd11_1_390, List.forall_mem_cons.2 ⟨subd11_1_391, List.forall_mem_cons.2 ⟨subd11_1_392, List.forall_mem_cons.2 ⟨subd11_1_393, List.forall_mem_cons.2 ⟨subd11_1_394, List.forall_mem_cons.2 ⟨subd11_1_395, List.forall_mem_cons.2 ⟨subd11_1_396, List.forall_mem_cons.2 ⟨subd11_1_397, List.forall_mem_cons.2 ⟨subd11_1_398, List.forall_mem_cons.2 ⟨subd11_1_399, List.forall_mem_cons.2 ⟨subd11_1_400, List.forall_mem_cons.2 ⟨subd11_1_401, List.forall_mem_cons.2 ⟨subd11_1_402, List.forall_mem_cons.2 ⟨subd11_1_403, List.forall_mem_cons.2 ⟨subd11_1_404, List.forall_mem_cons.2 ⟨subd11_1_405, List.forall_mem_cons.2 ⟨subd11_1_406, List.forall_mem_cons.2 ⟨subd11_1_407, List.forall_mem_cons.2 ⟨subd11_1_408, List.forall_mem_cons.2 ⟨subd11_1_409, List.forall_mem_cons.2 ⟨subd11_1_410, List.forall_mem_cons.2 ⟨subd11_1_411, List.forall_mem_cons.2 ⟨subd11_1_412, List.forall_mem_cons.2 ⟨subd11_1_413, List.forall_mem_cons.2 ⟨subd11_1_414, List.forall_mem_cons.2 ⟨subd11_1_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_416 : subd11_1 [0, 0, -10] = true := by decide +kernel
theorem subd11_1_417 : subd11_1 [0, 0, -9] = true := by decide +kernel
theorem subd11_1_418 : subd11_1 [0, 0, -8] = true := by decide +kernel
theorem subd11_1_419 : subd11_1 [0, 0, -7] = true := by decide +kernel
theorem subd11_1_420 : subd11_1 [0, 0, -6] = true := by decide +kernel
theorem subd11_1_421 : subd11_1 [0, 0, -5] = true := by decide +kernel
theorem subd11_1_422 : subd11_1 [0, 0, -4] = true := by decide +kernel
theorem subd11_1_423 : subd11_1 [0, 0, -3] = true := by decide +kernel
theorem subd11_1_424 : subd11_1 [0, 0, -2] = true := by decide +kernel
theorem subd11_1_425 : subd11_1 [0, 0, -1] = true := by decide +kernel
theorem subd11_1_426 : subd11_1 [0, 0, 0] = true := by decide +kernel
theorem subd11_1_427 : subd11_1 [0, 0, 1] = true := by decide +kernel
theorem subd11_1_428 : subd11_1 [0, 0, 2] = true := by decide +kernel
theorem subd11_1_429 : subd11_1 [0, 0, 3] = true := by decide +kernel
theorem subd11_1_430 : subd11_1 [0, 0, 4] = true := by decide +kernel
theorem subd11_1_431 : subd11_1 [0, 0, 5] = true := by decide +kernel
theorem subd11_1_432 : subd11_1 [0, 0, 6] = true := by decide +kernel
theorem subd11_1_433 : subd11_1 [0, 0, 7] = true := by decide +kernel
theorem subd11_1_434 : subd11_1 [0, 0, 8] = true := by decide +kernel
theorem subd11_1_435 : subd11_1 [0, 0, 9] = true := by decide +kernel
theorem subd11_1_436 : subd11_1 [0, 1, -10] = true := by decide +kernel
theorem subd11_1_437 : subd11_1 [0, 1, -9] = true := by decide +kernel
theorem subd11_1_438 : subd11_1 [0, 1, -8] = true := by decide +kernel
theorem subd11_1_439 : subd11_1 [0, 1, -7] = true := by decide +kernel
theorem subd11_1_440 : subd11_1 [0, 1, -6] = true := by decide +kernel
theorem subd11_1_441 : subd11_1 [0, 1, -5] = true := by decide +kernel
theorem subd11_1_442 : subd11_1 [0, 1, -4] = true := by decide +kernel
theorem subd11_1_443 : subd11_1 [0, 1, -3] = true := by decide +kernel
theorem subd11_1_444 : subd11_1 [0, 1, -2] = true := by decide +kernel
theorem subd11_1_445 : subd11_1 [0, 1, -1] = true := by decide +kernel
theorem subd11_1_446 : subd11_1 [0, 1, 0] = true := by decide +kernel
theorem subd11_1_447 : subd11_1 [0, 1, 1] = true := by decide +kernel
theorem sbd11_1_13 : ∀ q ∈ blkd11_1_13, subd11_1 q = true := by
  unfold blkd11_1_13
  exact List.forall_mem_cons.2 ⟨subd11_1_416, List.forall_mem_cons.2 ⟨subd11_1_417, List.forall_mem_cons.2 ⟨subd11_1_418, List.forall_mem_cons.2 ⟨subd11_1_419, List.forall_mem_cons.2 ⟨subd11_1_420, List.forall_mem_cons.2 ⟨subd11_1_421, List.forall_mem_cons.2 ⟨subd11_1_422, List.forall_mem_cons.2 ⟨subd11_1_423, List.forall_mem_cons.2 ⟨subd11_1_424, List.forall_mem_cons.2 ⟨subd11_1_425, List.forall_mem_cons.2 ⟨subd11_1_426, List.forall_mem_cons.2 ⟨subd11_1_427, List.forall_mem_cons.2 ⟨subd11_1_428, List.forall_mem_cons.2 ⟨subd11_1_429, List.forall_mem_cons.2 ⟨subd11_1_430, List.forall_mem_cons.2 ⟨subd11_1_431, List.forall_mem_cons.2 ⟨subd11_1_432, List.forall_mem_cons.2 ⟨subd11_1_433, List.forall_mem_cons.2 ⟨subd11_1_434, List.forall_mem_cons.2 ⟨subd11_1_435, List.forall_mem_cons.2 ⟨subd11_1_436, List.forall_mem_cons.2 ⟨subd11_1_437, List.forall_mem_cons.2 ⟨subd11_1_438, List.forall_mem_cons.2 ⟨subd11_1_439, List.forall_mem_cons.2 ⟨subd11_1_440, List.forall_mem_cons.2 ⟨subd11_1_441, List.forall_mem_cons.2 ⟨subd11_1_442, List.forall_mem_cons.2 ⟨subd11_1_443, List.forall_mem_cons.2 ⟨subd11_1_444, List.forall_mem_cons.2 ⟨subd11_1_445, List.forall_mem_cons.2 ⟨subd11_1_446, List.forall_mem_cons.2 ⟨subd11_1_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_448 : subd11_1 [0, 1, 2] = true := by decide +kernel
theorem subd11_1_449 : subd11_1 [0, 1, 3] = true := by decide +kernel
theorem subd11_1_450 : subd11_1 [0, 1, 4] = true := by decide +kernel
theorem subd11_1_451 : subd11_1 [0, 1, 5] = true := by decide +kernel
theorem subd11_1_452 : subd11_1 [0, 1, 6] = true := by decide +kernel
theorem subd11_1_453 : subd11_1 [0, 1, 7] = true := by decide +kernel
theorem subd11_1_454 : subd11_1 [0, 1, 8] = true := by decide +kernel
theorem subd11_1_455 : subd11_1 [0, 1, 9] = true := by decide +kernel
theorem subd11_1_456 : subd11_1 [0, 2, -10] = true := by decide +kernel
theorem subd11_1_457 : subd11_1 [0, 2, -9] = true := by decide +kernel
theorem subd11_1_458 : subd11_1 [0, 2, -8] = true := by decide +kernel
theorem subd11_1_459 : subd11_1 [0, 2, -7] = true := by decide +kernel
theorem subd11_1_460 : subd11_1 [0, 2, -6] = true := by decide +kernel
theorem subd11_1_461 : subd11_1 [0, 2, -5] = true := by decide +kernel
theorem subd11_1_462 : subd11_1 [0, 2, -4] = true := by decide +kernel
theorem subd11_1_463 : subd11_1 [0, 2, -3] = true := by decide +kernel
theorem subd11_1_464 : subd11_1 [0, 2, -2] = true := by decide +kernel
theorem subd11_1_465 : subd11_1 [0, 2, -1] = true := by decide +kernel
theorem subd11_1_466 : subd11_1 [0, 2, 0] = true := by decide +kernel
theorem subd11_1_467 : subd11_1 [0, 2, 1] = true := by decide +kernel
theorem subd11_1_468 : subd11_1 [0, 2, 2] = true := by decide +kernel
theorem subd11_1_469 : subd11_1 [0, 2, 3] = true := by decide +kernel
theorem subd11_1_470 : subd11_1 [0, 2, 4] = true := by decide +kernel
theorem subd11_1_471 : subd11_1 [0, 2, 5] = true := by decide +kernel
theorem subd11_1_472 : subd11_1 [0, 2, 6] = true := by decide +kernel
theorem subd11_1_473 : subd11_1 [0, 2, 7] = true := by decide +kernel
theorem subd11_1_474 : subd11_1 [0, 2, 8] = true := by decide +kernel
theorem subd11_1_475 : subd11_1 [0, 3, -9] = true := by decide +kernel
theorem subd11_1_476 : subd11_1 [0, 3, -8] = true := by decide +kernel
theorem subd11_1_477 : subd11_1 [0, 3, -7] = true := by decide +kernel
theorem subd11_1_478 : subd11_1 [0, 3, -6] = true := by decide +kernel
theorem subd11_1_479 : subd11_1 [0, 3, -5] = true := by decide +kernel
theorem sbd11_1_14 : ∀ q ∈ blkd11_1_14, subd11_1 q = true := by
  unfold blkd11_1_14
  exact List.forall_mem_cons.2 ⟨subd11_1_448, List.forall_mem_cons.2 ⟨subd11_1_449, List.forall_mem_cons.2 ⟨subd11_1_450, List.forall_mem_cons.2 ⟨subd11_1_451, List.forall_mem_cons.2 ⟨subd11_1_452, List.forall_mem_cons.2 ⟨subd11_1_453, List.forall_mem_cons.2 ⟨subd11_1_454, List.forall_mem_cons.2 ⟨subd11_1_455, List.forall_mem_cons.2 ⟨subd11_1_456, List.forall_mem_cons.2 ⟨subd11_1_457, List.forall_mem_cons.2 ⟨subd11_1_458, List.forall_mem_cons.2 ⟨subd11_1_459, List.forall_mem_cons.2 ⟨subd11_1_460, List.forall_mem_cons.2 ⟨subd11_1_461, List.forall_mem_cons.2 ⟨subd11_1_462, List.forall_mem_cons.2 ⟨subd11_1_463, List.forall_mem_cons.2 ⟨subd11_1_464, List.forall_mem_cons.2 ⟨subd11_1_465, List.forall_mem_cons.2 ⟨subd11_1_466, List.forall_mem_cons.2 ⟨subd11_1_467, List.forall_mem_cons.2 ⟨subd11_1_468, List.forall_mem_cons.2 ⟨subd11_1_469, List.forall_mem_cons.2 ⟨subd11_1_470, List.forall_mem_cons.2 ⟨subd11_1_471, List.forall_mem_cons.2 ⟨subd11_1_472, List.forall_mem_cons.2 ⟨subd11_1_473, List.forall_mem_cons.2 ⟨subd11_1_474, List.forall_mem_cons.2 ⟨subd11_1_475, List.forall_mem_cons.2 ⟨subd11_1_476, List.forall_mem_cons.2 ⟨subd11_1_477, List.forall_mem_cons.2 ⟨subd11_1_478, List.forall_mem_cons.2 ⟨subd11_1_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_480 : subd11_1 [0, 3, -4] = true := by decide +kernel
theorem subd11_1_481 : subd11_1 [0, 3, -3] = true := by decide +kernel
theorem subd11_1_482 : subd11_1 [0, 3, -2] = true := by decide +kernel
theorem subd11_1_483 : subd11_1 [0, 3, -1] = true := by decide +kernel
theorem subd11_1_484 : subd11_1 [0, 3, 0] = true := by decide +kernel
theorem subd11_1_485 : subd11_1 [0, 3, 1] = true := by decide +kernel
theorem subd11_1_486 : subd11_1 [0, 3, 2] = true := by decide +kernel
theorem subd11_1_487 : subd11_1 [0, 3, 3] = true := by decide +kernel
theorem subd11_1_488 : subd11_1 [0, 3, 4] = true := by decide +kernel
theorem subd11_1_489 : subd11_1 [0, 3, 5] = true := by decide +kernel
theorem subd11_1_490 : subd11_1 [0, 3, 6] = true := by decide +kernel
theorem subd11_1_491 : subd11_1 [0, 3, 7] = true := by decide +kernel
theorem subd11_1_492 : subd11_1 [0, 4, -8] = true := by decide +kernel
theorem subd11_1_493 : subd11_1 [0, 4, -7] = true := by decide +kernel
theorem subd11_1_494 : subd11_1 [0, 4, -6] = true := by decide +kernel
theorem subd11_1_495 : subd11_1 [0, 4, -5] = true := by decide +kernel
theorem subd11_1_496 : subd11_1 [0, 4, -4] = true := by decide +kernel
theorem subd11_1_497 : subd11_1 [0, 4, -3] = true := by decide +kernel
theorem subd11_1_498 : subd11_1 [0, 4, -2] = true := by decide +kernel
theorem subd11_1_499 : subd11_1 [0, 4, -1] = true := by decide +kernel
theorem subd11_1_500 : subd11_1 [0, 4, 0] = true := by decide +kernel
theorem subd11_1_501 : subd11_1 [0, 4, 1] = true := by decide +kernel
theorem subd11_1_502 : subd11_1 [0, 4, 2] = true := by decide +kernel
theorem subd11_1_503 : subd11_1 [0, 4, 3] = true := by decide +kernel
theorem subd11_1_504 : subd11_1 [0, 4, 4] = true := by decide +kernel
theorem subd11_1_505 : subd11_1 [0, 4, 5] = true := by decide +kernel
theorem subd11_1_506 : subd11_1 [0, 5] = true := by decide +kernel
theorem subd11_1_507 : subd11_1 [1, -6] = true := by decide +kernel
theorem subd11_1_508 : subd11_1 [1, -5] = true := by decide +kernel
theorem subd11_1_509 : subd11_1 [1, -4, -7] = true := by decide +kernel
theorem subd11_1_510 : subd11_1 [1, -4, -6] = true := by decide +kernel
theorem subd11_1_511 : subd11_1 [1, -4, -5] = true := by decide +kernel
theorem sbd11_1_15 : ∀ q ∈ blkd11_1_15, subd11_1 q = true := by
  unfold blkd11_1_15
  exact List.forall_mem_cons.2 ⟨subd11_1_480, List.forall_mem_cons.2 ⟨subd11_1_481, List.forall_mem_cons.2 ⟨subd11_1_482, List.forall_mem_cons.2 ⟨subd11_1_483, List.forall_mem_cons.2 ⟨subd11_1_484, List.forall_mem_cons.2 ⟨subd11_1_485, List.forall_mem_cons.2 ⟨subd11_1_486, List.forall_mem_cons.2 ⟨subd11_1_487, List.forall_mem_cons.2 ⟨subd11_1_488, List.forall_mem_cons.2 ⟨subd11_1_489, List.forall_mem_cons.2 ⟨subd11_1_490, List.forall_mem_cons.2 ⟨subd11_1_491, List.forall_mem_cons.2 ⟨subd11_1_492, List.forall_mem_cons.2 ⟨subd11_1_493, List.forall_mem_cons.2 ⟨subd11_1_494, List.forall_mem_cons.2 ⟨subd11_1_495, List.forall_mem_cons.2 ⟨subd11_1_496, List.forall_mem_cons.2 ⟨subd11_1_497, List.forall_mem_cons.2 ⟨subd11_1_498, List.forall_mem_cons.2 ⟨subd11_1_499, List.forall_mem_cons.2 ⟨subd11_1_500, List.forall_mem_cons.2 ⟨subd11_1_501, List.forall_mem_cons.2 ⟨subd11_1_502, List.forall_mem_cons.2 ⟨subd11_1_503, List.forall_mem_cons.2 ⟨subd11_1_504, List.forall_mem_cons.2 ⟨subd11_1_505, List.forall_mem_cons.2 ⟨subd11_1_506, List.forall_mem_cons.2 ⟨subd11_1_507, List.forall_mem_cons.2 ⟨subd11_1_508, List.forall_mem_cons.2 ⟨subd11_1_509, List.forall_mem_cons.2 ⟨subd11_1_510, List.forall_mem_cons.2 ⟨subd11_1_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_512 : subd11_1 [1, -4, -4] = true := by decide +kernel
theorem subd11_1_513 : subd11_1 [1, -4, -3] = true := by decide +kernel
theorem subd11_1_514 : subd11_1 [1, -4, -2] = true := by decide +kernel
theorem subd11_1_515 : subd11_1 [1, -4, -1] = true := by decide +kernel
theorem subd11_1_516 : subd11_1 [1, -4, 0] = true := by decide +kernel
theorem subd11_1_517 : subd11_1 [1, -4, 1] = true := by decide +kernel
theorem subd11_1_518 : subd11_1 [1, -4, 2] = true := by decide +kernel
theorem subd11_1_519 : subd11_1 [1, -4, 3] = true := by decide +kernel
theorem subd11_1_520 : subd11_1 [1, -4, 4] = true := by decide +kernel
theorem subd11_1_521 : subd11_1 [1, -4, 5] = true := by decide +kernel
theorem subd11_1_522 : subd11_1 [1, -4, 6] = true := by decide +kernel
theorem subd11_1_523 : subd11_1 [1, -4, 7] = true := by decide +kernel
theorem subd11_1_524 : subd11_1 [1, -4, 8] = true := by decide +kernel
theorem subd11_1_525 : subd11_1 [1, -3, -8] = true := by decide +kernel
theorem subd11_1_526 : subd11_1 [1, -3, -7] = true := by decide +kernel
theorem subd11_1_527 : subd11_1 [1, -3, -6] = true := by decide +kernel
theorem subd11_1_528 : subd11_1 [1, -3, -5] = true := by decide +kernel
theorem subd11_1_529 : subd11_1 [1, -3, -4] = true := by decide +kernel
theorem subd11_1_530 : subd11_1 [1, -3, -3] = true := by decide +kernel
theorem subd11_1_531 : subd11_1 [1, -3, -2] = true := by decide +kernel
theorem subd11_1_532 : subd11_1 [1, -3, -1] = true := by decide +kernel
theorem subd11_1_533 : subd11_1 [1, -3, 0] = true := by decide +kernel
theorem subd11_1_534 : subd11_1 [1, -3, 1] = true := by decide +kernel
theorem subd11_1_535 : subd11_1 [1, -3, 2] = true := by decide +kernel
theorem subd11_1_536 : subd11_1 [1, -3, 3] = true := by decide +kernel
theorem subd11_1_537 : subd11_1 [1, -3, 4] = true := by decide +kernel
theorem subd11_1_538 : subd11_1 [1, -3, 5] = true := by decide +kernel
theorem subd11_1_539 : subd11_1 [1, -3, 6] = true := by decide +kernel
theorem subd11_1_540 : subd11_1 [1, -3, 7] = true := by decide +kernel
theorem subd11_1_541 : subd11_1 [1, -3, 8] = true := by decide +kernel
theorem subd11_1_542 : subd11_1 [1, -2, -9] = true := by decide +kernel
theorem subd11_1_543 : subd11_1 [1, -2, -8] = true := by decide +kernel
theorem sbd11_1_16 : ∀ q ∈ blkd11_1_16, subd11_1 q = true := by
  unfold blkd11_1_16
  exact List.forall_mem_cons.2 ⟨subd11_1_512, List.forall_mem_cons.2 ⟨subd11_1_513, List.forall_mem_cons.2 ⟨subd11_1_514, List.forall_mem_cons.2 ⟨subd11_1_515, List.forall_mem_cons.2 ⟨subd11_1_516, List.forall_mem_cons.2 ⟨subd11_1_517, List.forall_mem_cons.2 ⟨subd11_1_518, List.forall_mem_cons.2 ⟨subd11_1_519, List.forall_mem_cons.2 ⟨subd11_1_520, List.forall_mem_cons.2 ⟨subd11_1_521, List.forall_mem_cons.2 ⟨subd11_1_522, List.forall_mem_cons.2 ⟨subd11_1_523, List.forall_mem_cons.2 ⟨subd11_1_524, List.forall_mem_cons.2 ⟨subd11_1_525, List.forall_mem_cons.2 ⟨subd11_1_526, List.forall_mem_cons.2 ⟨subd11_1_527, List.forall_mem_cons.2 ⟨subd11_1_528, List.forall_mem_cons.2 ⟨subd11_1_529, List.forall_mem_cons.2 ⟨subd11_1_530, List.forall_mem_cons.2 ⟨subd11_1_531, List.forall_mem_cons.2 ⟨subd11_1_532, List.forall_mem_cons.2 ⟨subd11_1_533, List.forall_mem_cons.2 ⟨subd11_1_534, List.forall_mem_cons.2 ⟨subd11_1_535, List.forall_mem_cons.2 ⟨subd11_1_536, List.forall_mem_cons.2 ⟨subd11_1_537, List.forall_mem_cons.2 ⟨subd11_1_538, List.forall_mem_cons.2 ⟨subd11_1_539, List.forall_mem_cons.2 ⟨subd11_1_540, List.forall_mem_cons.2 ⟨subd11_1_541, List.forall_mem_cons.2 ⟨subd11_1_542, List.forall_mem_cons.2 ⟨subd11_1_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_544 : subd11_1 [1, -2, -7] = true := by decide +kernel
theorem subd11_1_545 : subd11_1 [1, -2, -6] = true := by decide +kernel
theorem subd11_1_546 : subd11_1 [1, -2, -5] = true := by decide +kernel
theorem subd11_1_547 : subd11_1 [1, -2, -4] = true := by decide +kernel
theorem subd11_1_548 : subd11_1 [1, -2, -3] = true := by decide +kernel
theorem subd11_1_549 : subd11_1 [1, -2, -2] = true := by decide +kernel
theorem subd11_1_550 : subd11_1 [1, -2, -1] = true := by decide +kernel
theorem subd11_1_551 : subd11_1 [1, -2, 0] = true := by decide +kernel
theorem subd11_1_552 : subd11_1 [1, -2, 1] = true := by decide +kernel
theorem subd11_1_553 : subd11_1 [1, -2, 2] = true := by decide +kernel
theorem subd11_1_554 : subd11_1 [1, -2, 3] = true := by decide +kernel
theorem subd11_1_555 : subd11_1 [1, -2, 4] = true := by decide +kernel
theorem subd11_1_556 : subd11_1 [1, -2, 5] = true := by decide +kernel
theorem subd11_1_557 : subd11_1 [1, -2, 6] = true := by decide +kernel
theorem subd11_1_558 : subd11_1 [1, -2, 7] = true := by decide +kernel
theorem subd11_1_559 : subd11_1 [1, -2, 8] = true := by decide +kernel
theorem subd11_1_560 : subd11_1 [1, -2, 9] = true := by decide +kernel
theorem subd11_1_561 : subd11_1 [1, -1, -9] = true := by decide +kernel
theorem subd11_1_562 : subd11_1 [1, -1, -8] = true := by decide +kernel
theorem subd11_1_563 : subd11_1 [1, -1, -7] = true := by decide +kernel
theorem subd11_1_564 : subd11_1 [1, -1, -6] = true := by decide +kernel
theorem subd11_1_565 : subd11_1 [1, -1, -5] = true := by decide +kernel
theorem subd11_1_566 : subd11_1 [1, -1, -4] = true := by decide +kernel
theorem subd11_1_567 : subd11_1 [1, -1, -3] = true := by decide +kernel
theorem subd11_1_568 : subd11_1 [1, -1, -2] = true := by decide +kernel
theorem subd11_1_569 : subd11_1 [1, -1, -1] = true := by decide +kernel
theorem subd11_1_570 : subd11_1 [1, -1, 0] = true := by decide +kernel
theorem subd11_1_571 : subd11_1 [1, -1, 1] = true := by decide +kernel
theorem subd11_1_572 : subd11_1 [1, -1, 2] = true := by decide +kernel
theorem subd11_1_573 : subd11_1 [1, -1, 3] = true := by decide +kernel
theorem subd11_1_574 : subd11_1 [1, -1, 4] = true := by decide +kernel
theorem subd11_1_575 : subd11_1 [1, -1, 5] = true := by decide +kernel
theorem sbd11_1_17 : ∀ q ∈ blkd11_1_17, subd11_1 q = true := by
  unfold blkd11_1_17
  exact List.forall_mem_cons.2 ⟨subd11_1_544, List.forall_mem_cons.2 ⟨subd11_1_545, List.forall_mem_cons.2 ⟨subd11_1_546, List.forall_mem_cons.2 ⟨subd11_1_547, List.forall_mem_cons.2 ⟨subd11_1_548, List.forall_mem_cons.2 ⟨subd11_1_549, List.forall_mem_cons.2 ⟨subd11_1_550, List.forall_mem_cons.2 ⟨subd11_1_551, List.forall_mem_cons.2 ⟨subd11_1_552, List.forall_mem_cons.2 ⟨subd11_1_553, List.forall_mem_cons.2 ⟨subd11_1_554, List.forall_mem_cons.2 ⟨subd11_1_555, List.forall_mem_cons.2 ⟨subd11_1_556, List.forall_mem_cons.2 ⟨subd11_1_557, List.forall_mem_cons.2 ⟨subd11_1_558, List.forall_mem_cons.2 ⟨subd11_1_559, List.forall_mem_cons.2 ⟨subd11_1_560, List.forall_mem_cons.2 ⟨subd11_1_561, List.forall_mem_cons.2 ⟨subd11_1_562, List.forall_mem_cons.2 ⟨subd11_1_563, List.forall_mem_cons.2 ⟨subd11_1_564, List.forall_mem_cons.2 ⟨subd11_1_565, List.forall_mem_cons.2 ⟨subd11_1_566, List.forall_mem_cons.2 ⟨subd11_1_567, List.forall_mem_cons.2 ⟨subd11_1_568, List.forall_mem_cons.2 ⟨subd11_1_569, List.forall_mem_cons.2 ⟨subd11_1_570, List.forall_mem_cons.2 ⟨subd11_1_571, List.forall_mem_cons.2 ⟨subd11_1_572, List.forall_mem_cons.2 ⟨subd11_1_573, List.forall_mem_cons.2 ⟨subd11_1_574, List.forall_mem_cons.2 ⟨subd11_1_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_576 : subd11_1 [1, -1, 6] = true := by decide +kernel
theorem subd11_1_577 : subd11_1 [1, -1, 7] = true := by decide +kernel
theorem subd11_1_578 : subd11_1 [1, -1, 8] = true := by decide +kernel
theorem subd11_1_579 : subd11_1 [1, -1, 9] = true := by decide +kernel
theorem subd11_1_580 : subd11_1 [1, 0, -9] = true := by decide +kernel
theorem subd11_1_581 : subd11_1 [1, 0, -8] = true := by decide +kernel
theorem subd11_1_582 : subd11_1 [1, 0, -7] = true := by decide +kernel
theorem subd11_1_583 : subd11_1 [1, 0, -6] = true := by decide +kernel
theorem subd11_1_584 : subd11_1 [1, 0, -5] = true := by decide +kernel
theorem subd11_1_585 : subd11_1 [1, 0, -4] = true := by decide +kernel
theorem subd11_1_586 : subd11_1 [1, 0, -3] = true := by decide +kernel
theorem subd11_1_587 : subd11_1 [1, 0, -2] = true := by decide +kernel
theorem subd11_1_588 : subd11_1 [1, 0, -1] = true := by decide +kernel
theorem subd11_1_589 : subd11_1 [1, 0, 0] = true := by decide +kernel
theorem subd11_1_590 : subd11_1 [1, 0, 1] = true := by decide +kernel
theorem subd11_1_591 : subd11_1 [1, 0, 2] = true := by decide +kernel
theorem subd11_1_592 : subd11_1 [1, 0, 3] = true := by decide +kernel
theorem subd11_1_593 : subd11_1 [1, 0, 4] = true := by decide +kernel
theorem subd11_1_594 : subd11_1 [1, 0, 5] = true := by decide +kernel
theorem subd11_1_595 : subd11_1 [1, 0, 6] = true := by decide +kernel
theorem subd11_1_596 : subd11_1 [1, 0, 7] = true := by decide +kernel
theorem subd11_1_597 : subd11_1 [1, 0, 8] = true := by decide +kernel
theorem subd11_1_598 : subd11_1 [1, 0, 9] = true := by decide +kernel
theorem subd11_1_599 : subd11_1 [1, 1, -9] = true := by decide +kernel
theorem subd11_1_600 : subd11_1 [1, 1, -8] = true := by decide +kernel
theorem subd11_1_601 : subd11_1 [1, 1, -7] = true := by decide +kernel
theorem subd11_1_602 : subd11_1 [1, 1, -6] = true := by decide +kernel
theorem subd11_1_603 : subd11_1 [1, 1, -5] = true := by decide +kernel
theorem subd11_1_604 : subd11_1 [1, 1, -4] = true := by decide +kernel
theorem subd11_1_605 : subd11_1 [1, 1, -3] = true := by decide +kernel
theorem subd11_1_606 : subd11_1 [1, 1, -2] = true := by decide +kernel
theorem subd11_1_607 : subd11_1 [1, 1, -1] = true := by decide +kernel
theorem sbd11_1_18 : ∀ q ∈ blkd11_1_18, subd11_1 q = true := by
  unfold blkd11_1_18
  exact List.forall_mem_cons.2 ⟨subd11_1_576, List.forall_mem_cons.2 ⟨subd11_1_577, List.forall_mem_cons.2 ⟨subd11_1_578, List.forall_mem_cons.2 ⟨subd11_1_579, List.forall_mem_cons.2 ⟨subd11_1_580, List.forall_mem_cons.2 ⟨subd11_1_581, List.forall_mem_cons.2 ⟨subd11_1_582, List.forall_mem_cons.2 ⟨subd11_1_583, List.forall_mem_cons.2 ⟨subd11_1_584, List.forall_mem_cons.2 ⟨subd11_1_585, List.forall_mem_cons.2 ⟨subd11_1_586, List.forall_mem_cons.2 ⟨subd11_1_587, List.forall_mem_cons.2 ⟨subd11_1_588, List.forall_mem_cons.2 ⟨subd11_1_589, List.forall_mem_cons.2 ⟨subd11_1_590, List.forall_mem_cons.2 ⟨subd11_1_591, List.forall_mem_cons.2 ⟨subd11_1_592, List.forall_mem_cons.2 ⟨subd11_1_593, List.forall_mem_cons.2 ⟨subd11_1_594, List.forall_mem_cons.2 ⟨subd11_1_595, List.forall_mem_cons.2 ⟨subd11_1_596, List.forall_mem_cons.2 ⟨subd11_1_597, List.forall_mem_cons.2 ⟨subd11_1_598, List.forall_mem_cons.2 ⟨subd11_1_599, List.forall_mem_cons.2 ⟨subd11_1_600, List.forall_mem_cons.2 ⟨subd11_1_601, List.forall_mem_cons.2 ⟨subd11_1_602, List.forall_mem_cons.2 ⟨subd11_1_603, List.forall_mem_cons.2 ⟨subd11_1_604, List.forall_mem_cons.2 ⟨subd11_1_605, List.forall_mem_cons.2 ⟨subd11_1_606, List.forall_mem_cons.2 ⟨subd11_1_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_608 : subd11_1 [1, 1, 0] = true := by decide +kernel
theorem subd11_1_609 : subd11_1 [1, 1, 1] = true := by decide +kernel
theorem subd11_1_610 : subd11_1 [1, 1, 2] = true := by decide +kernel
theorem subd11_1_611 : subd11_1 [1, 1, 3] = true := by decide +kernel
theorem subd11_1_612 : subd11_1 [1, 1, 4] = true := by decide +kernel
theorem subd11_1_613 : subd11_1 [1, 1, 5] = true := by decide +kernel
theorem subd11_1_614 : subd11_1 [1, 1, 6] = true := by decide +kernel
theorem subd11_1_615 : subd11_1 [1, 1, 7] = true := by decide +kernel
theorem subd11_1_616 : subd11_1 [1, 1, 8] = true := by decide +kernel
theorem subd11_1_617 : subd11_1 [1, 1, 9] = true := by decide +kernel
theorem subd11_1_618 : subd11_1 [1, 2, -9] = true := by decide +kernel
theorem subd11_1_619 : subd11_1 [1, 2, -8] = true := by decide +kernel
theorem subd11_1_620 : subd11_1 [1, 2, -7] = true := by decide +kernel
theorem subd11_1_621 : subd11_1 [1, 2, -6] = true := by decide +kernel
theorem subd11_1_622 : subd11_1 [1, 2, -5] = true := by decide +kernel
theorem subd11_1_623 : subd11_1 [1, 2, -4] = true := by decide +kernel
theorem subd11_1_624 : subd11_1 [1, 2, -3] = true := by decide +kernel
theorem subd11_1_625 : subd11_1 [1, 2, -2] = true := by decide +kernel
theorem subd11_1_626 : subd11_1 [1, 2, -1] = true := by decide +kernel
theorem subd11_1_627 : subd11_1 [1, 2, 0] = true := by decide +kernel
theorem subd11_1_628 : subd11_1 [1, 2, 1] = true := by decide +kernel
theorem subd11_1_629 : subd11_1 [1, 2, 2] = true := by decide +kernel
theorem subd11_1_630 : subd11_1 [1, 2, 3] = true := by decide +kernel
theorem subd11_1_631 : subd11_1 [1, 2, 4] = true := by decide +kernel
theorem subd11_1_632 : subd11_1 [1, 2, 5] = true := by decide +kernel
theorem subd11_1_633 : subd11_1 [1, 2, 6] = true := by decide +kernel
theorem subd11_1_634 : subd11_1 [1, 2, 7] = true := by decide +kernel
theorem subd11_1_635 : subd11_1 [1, 2, 8] = true := by decide +kernel
theorem subd11_1_636 : subd11_1 [1, 3, -8] = true := by decide +kernel
theorem subd11_1_637 : subd11_1 [1, 3, -7] = true := by decide +kernel
theorem subd11_1_638 : subd11_1 [1, 3, -6] = true := by decide +kernel
theorem subd11_1_639 : subd11_1 [1, 3, -5] = true := by decide +kernel
theorem sbd11_1_19 : ∀ q ∈ blkd11_1_19, subd11_1 q = true := by
  unfold blkd11_1_19
  exact List.forall_mem_cons.2 ⟨subd11_1_608, List.forall_mem_cons.2 ⟨subd11_1_609, List.forall_mem_cons.2 ⟨subd11_1_610, List.forall_mem_cons.2 ⟨subd11_1_611, List.forall_mem_cons.2 ⟨subd11_1_612, List.forall_mem_cons.2 ⟨subd11_1_613, List.forall_mem_cons.2 ⟨subd11_1_614, List.forall_mem_cons.2 ⟨subd11_1_615, List.forall_mem_cons.2 ⟨subd11_1_616, List.forall_mem_cons.2 ⟨subd11_1_617, List.forall_mem_cons.2 ⟨subd11_1_618, List.forall_mem_cons.2 ⟨subd11_1_619, List.forall_mem_cons.2 ⟨subd11_1_620, List.forall_mem_cons.2 ⟨subd11_1_621, List.forall_mem_cons.2 ⟨subd11_1_622, List.forall_mem_cons.2 ⟨subd11_1_623, List.forall_mem_cons.2 ⟨subd11_1_624, List.forall_mem_cons.2 ⟨subd11_1_625, List.forall_mem_cons.2 ⟨subd11_1_626, List.forall_mem_cons.2 ⟨subd11_1_627, List.forall_mem_cons.2 ⟨subd11_1_628, List.forall_mem_cons.2 ⟨subd11_1_629, List.forall_mem_cons.2 ⟨subd11_1_630, List.forall_mem_cons.2 ⟨subd11_1_631, List.forall_mem_cons.2 ⟨subd11_1_632, List.forall_mem_cons.2 ⟨subd11_1_633, List.forall_mem_cons.2 ⟨subd11_1_634, List.forall_mem_cons.2 ⟨subd11_1_635, List.forall_mem_cons.2 ⟨subd11_1_636, List.forall_mem_cons.2 ⟨subd11_1_637, List.forall_mem_cons.2 ⟨subd11_1_638, List.forall_mem_cons.2 ⟨subd11_1_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_640 : subd11_1 [1, 3, -4] = true := by decide +kernel
theorem subd11_1_641 : subd11_1 [1, 3, -3] = true := by decide +kernel
theorem subd11_1_642 : subd11_1 [1, 3, -2] = true := by decide +kernel
theorem subd11_1_643 : subd11_1 [1, 3, -1] = true := by decide +kernel
theorem subd11_1_644 : subd11_1 [1, 3, 0] = true := by decide +kernel
theorem subd11_1_645 : subd11_1 [1, 3, 1] = true := by decide +kernel
theorem subd11_1_646 : subd11_1 [1, 3, 2] = true := by decide +kernel
theorem subd11_1_647 : subd11_1 [1, 3, 3] = true := by decide +kernel
theorem subd11_1_648 : subd11_1 [1, 3, 4] = true := by decide +kernel
theorem subd11_1_649 : subd11_1 [1, 3, 5] = true := by decide +kernel
theorem subd11_1_650 : subd11_1 [1, 3, 6] = true := by decide +kernel
theorem subd11_1_651 : subd11_1 [1, 4] = true := by decide +kernel
theorem subd11_1_652 : subd11_1 [2, -7] = true := by decide +kernel
theorem subd11_1_653 : subd11_1 [2, -6] = true := by decide +kernel
theorem subd11_1_654 : subd11_1 [2, -5] = true := by decide +kernel
theorem subd11_1_655 : subd11_1 [2, -4, -6] = true := by decide +kernel
theorem subd11_1_656 : subd11_1 [2, -4, -5] = true := by decide +kernel
theorem subd11_1_657 : subd11_1 [2, -4, -4] = true := by decide +kernel
theorem subd11_1_658 : subd11_1 [2, -4, -3] = true := by decide +kernel
theorem subd11_1_659 : subd11_1 [2, -4, -2] = true := by decide +kernel
theorem subd11_1_660 : subd11_1 [2, -4, -1] = true := by decide +kernel
theorem subd11_1_661 : subd11_1 [2, -4, 0] = true := by decide +kernel
theorem subd11_1_662 : subd11_1 [2, -4, 1] = true := by decide +kernel
theorem subd11_1_663 : subd11_1 [2, -4, 2] = true := by decide +kernel
theorem subd11_1_664 : subd11_1 [2, -4, 3] = true := by decide +kernel
theorem subd11_1_665 : subd11_1 [2, -4, 4] = true := by decide +kernel
theorem subd11_1_666 : subd11_1 [2, -4, 5] = true := by decide +kernel
theorem subd11_1_667 : subd11_1 [2, -4, 6] = true := by decide +kernel
theorem subd11_1_668 : subd11_1 [2, -4, 7] = true := by decide +kernel
theorem subd11_1_669 : subd11_1 [2, -4, 8] = true := by decide +kernel
theorem subd11_1_670 : subd11_1 [2, -3, -7] = true := by decide +kernel
theorem subd11_1_671 : subd11_1 [2, -3, -6] = true := by decide +kernel
theorem sbd11_1_20 : ∀ q ∈ blkd11_1_20, subd11_1 q = true := by
  unfold blkd11_1_20
  exact List.forall_mem_cons.2 ⟨subd11_1_640, List.forall_mem_cons.2 ⟨subd11_1_641, List.forall_mem_cons.2 ⟨subd11_1_642, List.forall_mem_cons.2 ⟨subd11_1_643, List.forall_mem_cons.2 ⟨subd11_1_644, List.forall_mem_cons.2 ⟨subd11_1_645, List.forall_mem_cons.2 ⟨subd11_1_646, List.forall_mem_cons.2 ⟨subd11_1_647, List.forall_mem_cons.2 ⟨subd11_1_648, List.forall_mem_cons.2 ⟨subd11_1_649, List.forall_mem_cons.2 ⟨subd11_1_650, List.forall_mem_cons.2 ⟨subd11_1_651, List.forall_mem_cons.2 ⟨subd11_1_652, List.forall_mem_cons.2 ⟨subd11_1_653, List.forall_mem_cons.2 ⟨subd11_1_654, List.forall_mem_cons.2 ⟨subd11_1_655, List.forall_mem_cons.2 ⟨subd11_1_656, List.forall_mem_cons.2 ⟨subd11_1_657, List.forall_mem_cons.2 ⟨subd11_1_658, List.forall_mem_cons.2 ⟨subd11_1_659, List.forall_mem_cons.2 ⟨subd11_1_660, List.forall_mem_cons.2 ⟨subd11_1_661, List.forall_mem_cons.2 ⟨subd11_1_662, List.forall_mem_cons.2 ⟨subd11_1_663, List.forall_mem_cons.2 ⟨subd11_1_664, List.forall_mem_cons.2 ⟨subd11_1_665, List.forall_mem_cons.2 ⟨subd11_1_666, List.forall_mem_cons.2 ⟨subd11_1_667, List.forall_mem_cons.2 ⟨subd11_1_668, List.forall_mem_cons.2 ⟨subd11_1_669, List.forall_mem_cons.2 ⟨subd11_1_670, List.forall_mem_cons.2 ⟨subd11_1_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_672 : subd11_1 [2, -3, -5] = true := by decide +kernel
theorem subd11_1_673 : subd11_1 [2, -3, -4] = true := by decide +kernel
theorem subd11_1_674 : subd11_1 [2, -3, -3] = true := by decide +kernel
theorem subd11_1_675 : subd11_1 [2, -3, -2] = true := by decide +kernel
theorem subd11_1_676 : subd11_1 [2, -3, -1] = true := by decide +kernel
theorem subd11_1_677 : subd11_1 [2, -3, 0] = true := by decide +kernel
theorem subd11_1_678 : subd11_1 [2, -3, 1] = true := by decide +kernel
theorem subd11_1_679 : subd11_1 [2, -3, 2] = true := by decide +kernel
theorem subd11_1_680 : subd11_1 [2, -3, 3] = true := by decide +kernel
theorem subd11_1_681 : subd11_1 [2, -3, 4] = true := by decide +kernel
theorem subd11_1_682 : subd11_1 [2, -3, 5] = true := by decide +kernel
theorem subd11_1_683 : subd11_1 [2, -3, 6] = true := by decide +kernel
theorem subd11_1_684 : subd11_1 [2, -3, 7] = true := by decide +kernel
theorem subd11_1_685 : subd11_1 [2, -3, 8] = true := by decide +kernel
theorem subd11_1_686 : subd11_1 [2, -3, 9] = true := by decide +kernel
theorem subd11_1_687 : subd11_1 [2, -2, -8] = true := by decide +kernel
theorem subd11_1_688 : subd11_1 [2, -2, -7] = true := by decide +kernel
theorem subd11_1_689 : subd11_1 [2, -2, -6] = true := by decide +kernel
theorem subd11_1_690 : subd11_1 [2, -2, -5] = true := by decide +kernel
theorem subd11_1_691 : subd11_1 [2, -2, -4] = true := by decide +kernel
theorem subd11_1_692 : subd11_1 [2, -2, -3] = true := by decide +kernel
theorem subd11_1_693 : subd11_1 [2, -2, -2] = true := by decide +kernel
theorem subd11_1_694 : subd11_1 [2, -2, -1] = true := by decide +kernel
theorem subd11_1_695 : subd11_1 [2, -2, 0] = true := by decide +kernel
theorem subd11_1_696 : subd11_1 [2, -2, 1] = true := by decide +kernel
theorem subd11_1_697 : subd11_1 [2, -2, 2] = true := by decide +kernel
theorem subd11_1_698 : subd11_1 [2, -2, 3] = true := by decide +kernel
theorem subd11_1_699 : subd11_1 [2, -2, 4] = true := by decide +kernel
theorem subd11_1_700 : subd11_1 [2, -2, 5] = true := by decide +kernel
theorem subd11_1_701 : subd11_1 [2, -2, 6] = true := by decide +kernel
theorem subd11_1_702 : subd11_1 [2, -2, 7] = true := by decide +kernel
theorem subd11_1_703 : subd11_1 [2, -2, 8] = true := by decide +kernel
theorem sbd11_1_21 : ∀ q ∈ blkd11_1_21, subd11_1 q = true := by
  unfold blkd11_1_21
  exact List.forall_mem_cons.2 ⟨subd11_1_672, List.forall_mem_cons.2 ⟨subd11_1_673, List.forall_mem_cons.2 ⟨subd11_1_674, List.forall_mem_cons.2 ⟨subd11_1_675, List.forall_mem_cons.2 ⟨subd11_1_676, List.forall_mem_cons.2 ⟨subd11_1_677, List.forall_mem_cons.2 ⟨subd11_1_678, List.forall_mem_cons.2 ⟨subd11_1_679, List.forall_mem_cons.2 ⟨subd11_1_680, List.forall_mem_cons.2 ⟨subd11_1_681, List.forall_mem_cons.2 ⟨subd11_1_682, List.forall_mem_cons.2 ⟨subd11_1_683, List.forall_mem_cons.2 ⟨subd11_1_684, List.forall_mem_cons.2 ⟨subd11_1_685, List.forall_mem_cons.2 ⟨subd11_1_686, List.forall_mem_cons.2 ⟨subd11_1_687, List.forall_mem_cons.2 ⟨subd11_1_688, List.forall_mem_cons.2 ⟨subd11_1_689, List.forall_mem_cons.2 ⟨subd11_1_690, List.forall_mem_cons.2 ⟨subd11_1_691, List.forall_mem_cons.2 ⟨subd11_1_692, List.forall_mem_cons.2 ⟨subd11_1_693, List.forall_mem_cons.2 ⟨subd11_1_694, List.forall_mem_cons.2 ⟨subd11_1_695, List.forall_mem_cons.2 ⟨subd11_1_696, List.forall_mem_cons.2 ⟨subd11_1_697, List.forall_mem_cons.2 ⟨subd11_1_698, List.forall_mem_cons.2 ⟨subd11_1_699, List.forall_mem_cons.2 ⟨subd11_1_700, List.forall_mem_cons.2 ⟨subd11_1_701, List.forall_mem_cons.2 ⟨subd11_1_702, List.forall_mem_cons.2 ⟨subd11_1_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_704 : subd11_1 [2, -2, 9] = true := by decide +kernel
theorem subd11_1_705 : subd11_1 [2, -1, -8] = true := by decide +kernel
theorem subd11_1_706 : subd11_1 [2, -1, -7] = true := by decide +kernel
theorem subd11_1_707 : subd11_1 [2, -1, -6] = true := by decide +kernel
theorem subd11_1_708 : subd11_1 [2, -1, -5] = true := by decide +kernel
theorem subd11_1_709 : subd11_1 [2, -1, -4] = true := by decide +kernel
theorem subd11_1_710 : subd11_1 [2, -1, -3] = true := by decide +kernel
theorem subd11_1_711 : subd11_1 [2, -1, -2] = true := by decide +kernel
theorem subd11_1_712 : subd11_1 [2, -1, -1] = true := by decide +kernel
theorem subd11_1_713 : subd11_1 [2, -1, 0] = true := by decide +kernel
theorem subd11_1_714 : subd11_1 [2, -1, 1] = true := by decide +kernel
theorem subd11_1_715 : subd11_1 [2, -1, 2] = true := by decide +kernel
theorem subd11_1_716 : subd11_1 [2, -1, 3] = true := by decide +kernel
theorem subd11_1_717 : subd11_1 [2, -1, 4] = true := by decide +kernel
theorem subd11_1_718 : subd11_1 [2, -1, 5] = true := by decide +kernel
theorem subd11_1_719 : subd11_1 [2, -1, 6] = true := by decide +kernel
theorem subd11_1_720 : subd11_1 [2, -1, 7] = true := by decide +kernel
theorem subd11_1_721 : subd11_1 [2, -1, 8] = true := by decide +kernel
theorem subd11_1_722 : subd11_1 [2, -1, 9] = true := by decide +kernel
theorem subd11_1_723 : subd11_1 [2, 0, -8] = true := by decide +kernel
theorem subd11_1_724 : subd11_1 [2, 0, -7] = true := by decide +kernel
theorem subd11_1_725 : subd11_1 [2, 0, -6] = true := by decide +kernel
theorem subd11_1_726 : subd11_1 [2, 0, -5] = true := by decide +kernel
theorem subd11_1_727 : subd11_1 [2, 0, -4] = true := by decide +kernel
theorem subd11_1_728 : subd11_1 [2, 0, -3] = true := by decide +kernel
theorem subd11_1_729 : subd11_1 [2, 0, -2] = true := by decide +kernel
theorem subd11_1_730 : subd11_1 [2, 0, -1] = true := by decide +kernel
theorem subd11_1_731 : subd11_1 [2, 0, 0] = true := by decide +kernel
theorem subd11_1_732 : subd11_1 [2, 0, 1] = true := by decide +kernel
theorem subd11_1_733 : subd11_1 [2, 0, 2] = true := by decide +kernel
theorem subd11_1_734 : subd11_1 [2, 0, 3] = true := by decide +kernel
theorem subd11_1_735 : subd11_1 [2, 0, 4] = true := by decide +kernel
theorem sbd11_1_22 : ∀ q ∈ blkd11_1_22, subd11_1 q = true := by
  unfold blkd11_1_22
  exact List.forall_mem_cons.2 ⟨subd11_1_704, List.forall_mem_cons.2 ⟨subd11_1_705, List.forall_mem_cons.2 ⟨subd11_1_706, List.forall_mem_cons.2 ⟨subd11_1_707, List.forall_mem_cons.2 ⟨subd11_1_708, List.forall_mem_cons.2 ⟨subd11_1_709, List.forall_mem_cons.2 ⟨subd11_1_710, List.forall_mem_cons.2 ⟨subd11_1_711, List.forall_mem_cons.2 ⟨subd11_1_712, List.forall_mem_cons.2 ⟨subd11_1_713, List.forall_mem_cons.2 ⟨subd11_1_714, List.forall_mem_cons.2 ⟨subd11_1_715, List.forall_mem_cons.2 ⟨subd11_1_716, List.forall_mem_cons.2 ⟨subd11_1_717, List.forall_mem_cons.2 ⟨subd11_1_718, List.forall_mem_cons.2 ⟨subd11_1_719, List.forall_mem_cons.2 ⟨subd11_1_720, List.forall_mem_cons.2 ⟨subd11_1_721, List.forall_mem_cons.2 ⟨subd11_1_722, List.forall_mem_cons.2 ⟨subd11_1_723, List.forall_mem_cons.2 ⟨subd11_1_724, List.forall_mem_cons.2 ⟨subd11_1_725, List.forall_mem_cons.2 ⟨subd11_1_726, List.forall_mem_cons.2 ⟨subd11_1_727, List.forall_mem_cons.2 ⟨subd11_1_728, List.forall_mem_cons.2 ⟨subd11_1_729, List.forall_mem_cons.2 ⟨subd11_1_730, List.forall_mem_cons.2 ⟨subd11_1_731, List.forall_mem_cons.2 ⟨subd11_1_732, List.forall_mem_cons.2 ⟨subd11_1_733, List.forall_mem_cons.2 ⟨subd11_1_734, List.forall_mem_cons.2 ⟨subd11_1_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_736 : subd11_1 [2, 0, 5] = true := by decide +kernel
theorem subd11_1_737 : subd11_1 [2, 0, 6] = true := by decide +kernel
theorem subd11_1_738 : subd11_1 [2, 0, 7] = true := by decide +kernel
theorem subd11_1_739 : subd11_1 [2, 0, 8] = true := by decide +kernel
theorem subd11_1_740 : subd11_1 [2, 0, 9] = true := by decide +kernel
theorem subd11_1_741 : subd11_1 [2, 1, -8] = true := by decide +kernel
theorem subd11_1_742 : subd11_1 [2, 1, -7] = true := by decide +kernel
theorem subd11_1_743 : subd11_1 [2, 1, -6] = true := by decide +kernel
theorem subd11_1_744 : subd11_1 [2, 1, -5] = true := by decide +kernel
theorem subd11_1_745 : subd11_1 [2, 1, -4] = true := by decide +kernel
theorem subd11_1_746 : subd11_1 [2, 1, -3] = true := by decide +kernel
theorem subd11_1_747 : subd11_1 [2, 1, -2] = true := by decide +kernel
theorem subd11_1_748 : subd11_1 [2, 1, -1] = true := by decide +kernel
theorem subd11_1_749 : subd11_1 [2, 1, 0] = true := by decide +kernel
theorem subd11_1_750 : subd11_1 [2, 1, 1] = true := by decide +kernel
theorem subd11_1_751 : subd11_1 [2, 1, 2] = true := by decide +kernel
theorem subd11_1_752 : subd11_1 [2, 1, 3] = true := by decide +kernel
theorem subd11_1_753 : subd11_1 [2, 1, 4] = true := by decide +kernel
theorem subd11_1_754 : subd11_1 [2, 1, 5] = true := by decide +kernel
theorem subd11_1_755 : subd11_1 [2, 1, 6] = true := by decide +kernel
theorem subd11_1_756 : subd11_1 [2, 1, 7] = true := by decide +kernel
theorem subd11_1_757 : subd11_1 [2, 1, 8] = true := by decide +kernel
theorem subd11_1_758 : subd11_1 [2, 2, -7] = true := by decide +kernel
theorem subd11_1_759 : subd11_1 [2, 2, -6] = true := by decide +kernel
theorem subd11_1_760 : subd11_1 [2, 2, -5] = true := by decide +kernel
theorem subd11_1_761 : subd11_1 [2, 2, -4] = true := by decide +kernel
theorem subd11_1_762 : subd11_1 [2, 2, -3] = true := by decide +kernel
theorem subd11_1_763 : subd11_1 [2, 2, -2] = true := by decide +kernel
theorem subd11_1_764 : subd11_1 [2, 2, -1] = true := by decide +kernel
theorem subd11_1_765 : subd11_1 [2, 2, 0] = true := by decide +kernel
theorem subd11_1_766 : subd11_1 [2, 2, 1] = true := by decide +kernel
theorem subd11_1_767 : subd11_1 [2, 2, 2] = true := by decide +kernel
theorem sbd11_1_23 : ∀ q ∈ blkd11_1_23, subd11_1 q = true := by
  unfold blkd11_1_23
  exact List.forall_mem_cons.2 ⟨subd11_1_736, List.forall_mem_cons.2 ⟨subd11_1_737, List.forall_mem_cons.2 ⟨subd11_1_738, List.forall_mem_cons.2 ⟨subd11_1_739, List.forall_mem_cons.2 ⟨subd11_1_740, List.forall_mem_cons.2 ⟨subd11_1_741, List.forall_mem_cons.2 ⟨subd11_1_742, List.forall_mem_cons.2 ⟨subd11_1_743, List.forall_mem_cons.2 ⟨subd11_1_744, List.forall_mem_cons.2 ⟨subd11_1_745, List.forall_mem_cons.2 ⟨subd11_1_746, List.forall_mem_cons.2 ⟨subd11_1_747, List.forall_mem_cons.2 ⟨subd11_1_748, List.forall_mem_cons.2 ⟨subd11_1_749, List.forall_mem_cons.2 ⟨subd11_1_750, List.forall_mem_cons.2 ⟨subd11_1_751, List.forall_mem_cons.2 ⟨subd11_1_752, List.forall_mem_cons.2 ⟨subd11_1_753, List.forall_mem_cons.2 ⟨subd11_1_754, List.forall_mem_cons.2 ⟨subd11_1_755, List.forall_mem_cons.2 ⟨subd11_1_756, List.forall_mem_cons.2 ⟨subd11_1_757, List.forall_mem_cons.2 ⟨subd11_1_758, List.forall_mem_cons.2 ⟨subd11_1_759, List.forall_mem_cons.2 ⟨subd11_1_760, List.forall_mem_cons.2 ⟨subd11_1_761, List.forall_mem_cons.2 ⟨subd11_1_762, List.forall_mem_cons.2 ⟨subd11_1_763, List.forall_mem_cons.2 ⟨subd11_1_764, List.forall_mem_cons.2 ⟨subd11_1_765, List.forall_mem_cons.2 ⟨subd11_1_766, List.forall_mem_cons.2 ⟨subd11_1_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_768 : subd11_1 [2, 2, 3] = true := by decide +kernel
theorem subd11_1_769 : subd11_1 [2, 2, 4] = true := by decide +kernel
theorem subd11_1_770 : subd11_1 [2, 2, 5] = true := by decide +kernel
theorem subd11_1_771 : subd11_1 [2, 2, 6] = true := by decide +kernel
theorem subd11_1_772 : subd11_1 [2, 2, 7] = true := by decide +kernel
theorem subd11_1_773 : subd11_1 [2, 3] = true := by decide +kernel
theorem subd11_1_774 : subd11_1 [2, 4] = true := by decide +kernel
theorem subd11_1_775 : subd11_1 [3, -6] = true := by decide +kernel
theorem subd11_1_776 : subd11_1 [3, -5] = true := by decide +kernel
theorem subd11_1_777 : subd11_1 [3, -4] = true := by decide +kernel
theorem subd11_1_778 : subd11_1 [3, -3, -6] = true := by decide +kernel
theorem subd11_1_779 : subd11_1 [3, -3, -5] = true := by decide +kernel
theorem subd11_1_780 : subd11_1 [3, -3, -4] = true := by decide +kernel
theorem subd11_1_781 : subd11_1 [3, -3, -3] = true := by decide +kernel
theorem subd11_1_782 : subd11_1 [3, -3, -2] = true := by decide +kernel
theorem subd11_1_783 : subd11_1 [3, -3, -1] = true := by decide +kernel
theorem subd11_1_784 : subd11_1 [3, -3, 0] = true := by decide +kernel
theorem subd11_1_785 : subd11_1 [3, -3, 1] = true := by decide +kernel
theorem subd11_1_786 : subd11_1 [3, -3, 2] = true := by decide +kernel
theorem subd11_1_787 : subd11_1 [3, -3, 3] = true := by decide +kernel
theorem subd11_1_788 : subd11_1 [3, -3, 4] = true := by decide +kernel
theorem subd11_1_789 : subd11_1 [3, -3, 5] = true := by decide +kernel
theorem subd11_1_790 : subd11_1 [3, -3, 6] = true := by decide +kernel
theorem subd11_1_791 : subd11_1 [3, -3, 7] = true := by decide +kernel
theorem subd11_1_792 : subd11_1 [3, -3, 8] = true := by decide +kernel
theorem subd11_1_793 : subd11_1 [3, -2, -7] = true := by decide +kernel
theorem subd11_1_794 : subd11_1 [3, -2, -6] = true := by decide +kernel
theorem subd11_1_795 : subd11_1 [3, -2, -5] = true := by decide +kernel
theorem subd11_1_796 : subd11_1 [3, -2, -4] = true := by decide +kernel
theorem subd11_1_797 : subd11_1 [3, -2, -3] = true := by decide +kernel
theorem subd11_1_798 : subd11_1 [3, -2, -2] = true := by decide +kernel
theorem subd11_1_799 : subd11_1 [3, -2, -1] = true := by decide +kernel
theorem sbd11_1_24 : ∀ q ∈ blkd11_1_24, subd11_1 q = true := by
  unfold blkd11_1_24
  exact List.forall_mem_cons.2 ⟨subd11_1_768, List.forall_mem_cons.2 ⟨subd11_1_769, List.forall_mem_cons.2 ⟨subd11_1_770, List.forall_mem_cons.2 ⟨subd11_1_771, List.forall_mem_cons.2 ⟨subd11_1_772, List.forall_mem_cons.2 ⟨subd11_1_773, List.forall_mem_cons.2 ⟨subd11_1_774, List.forall_mem_cons.2 ⟨subd11_1_775, List.forall_mem_cons.2 ⟨subd11_1_776, List.forall_mem_cons.2 ⟨subd11_1_777, List.forall_mem_cons.2 ⟨subd11_1_778, List.forall_mem_cons.2 ⟨subd11_1_779, List.forall_mem_cons.2 ⟨subd11_1_780, List.forall_mem_cons.2 ⟨subd11_1_781, List.forall_mem_cons.2 ⟨subd11_1_782, List.forall_mem_cons.2 ⟨subd11_1_783, List.forall_mem_cons.2 ⟨subd11_1_784, List.forall_mem_cons.2 ⟨subd11_1_785, List.forall_mem_cons.2 ⟨subd11_1_786, List.forall_mem_cons.2 ⟨subd11_1_787, List.forall_mem_cons.2 ⟨subd11_1_788, List.forall_mem_cons.2 ⟨subd11_1_789, List.forall_mem_cons.2 ⟨subd11_1_790, List.forall_mem_cons.2 ⟨subd11_1_791, List.forall_mem_cons.2 ⟨subd11_1_792, List.forall_mem_cons.2 ⟨subd11_1_793, List.forall_mem_cons.2 ⟨subd11_1_794, List.forall_mem_cons.2 ⟨subd11_1_795, List.forall_mem_cons.2 ⟨subd11_1_796, List.forall_mem_cons.2 ⟨subd11_1_797, List.forall_mem_cons.2 ⟨subd11_1_798, List.forall_mem_cons.2 ⟨subd11_1_799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_800 : subd11_1 [3, -2, 0] = true := by decide +kernel
theorem subd11_1_801 : subd11_1 [3, -2, 1] = true := by decide +kernel
theorem subd11_1_802 : subd11_1 [3, -2, 2] = true := by decide +kernel
theorem subd11_1_803 : subd11_1 [3, -2, 3] = true := by decide +kernel
theorem subd11_1_804 : subd11_1 [3, -2, 4] = true := by decide +kernel
theorem subd11_1_805 : subd11_1 [3, -2, 5] = true := by decide +kernel
theorem subd11_1_806 : subd11_1 [3, -2, 6] = true := by decide +kernel
theorem subd11_1_807 : subd11_1 [3, -2, 7] = true := by decide +kernel
theorem subd11_1_808 : subd11_1 [3, -2, 8] = true := by decide +kernel
theorem subd11_1_809 : subd11_1 [3, -1, -7] = true := by decide +kernel
theorem subd11_1_810 : subd11_1 [3, -1, -6] = true := by decide +kernel
theorem subd11_1_811 : subd11_1 [3, -1, -5] = true := by decide +kernel
theorem subd11_1_812 : subd11_1 [3, -1, -4] = true := by decide +kernel
theorem subd11_1_813 : subd11_1 [3, -1, -3] = true := by decide +kernel
theorem subd11_1_814 : subd11_1 [3, -1, -2] = true := by decide +kernel
theorem subd11_1_815 : subd11_1 [3, -1, -1] = true := by decide +kernel
theorem subd11_1_816 : subd11_1 [3, -1, 0] = true := by decide +kernel
theorem subd11_1_817 : subd11_1 [3, -1, 1] = true := by decide +kernel
theorem subd11_1_818 : subd11_1 [3, -1, 2] = true := by decide +kernel
theorem subd11_1_819 : subd11_1 [3, -1, 3] = true := by decide +kernel
theorem subd11_1_820 : subd11_1 [3, -1, 4] = true := by decide +kernel
theorem subd11_1_821 : subd11_1 [3, -1, 5] = true := by decide +kernel
theorem subd11_1_822 : subd11_1 [3, -1, 6] = true := by decide +kernel
theorem subd11_1_823 : subd11_1 [3, -1, 7] = true := by decide +kernel
theorem subd11_1_824 : subd11_1 [3, -1, 8] = true := by decide +kernel
theorem subd11_1_825 : subd11_1 [3, 0, -7] = true := by decide +kernel
theorem subd11_1_826 : subd11_1 [3, 0, -6] = true := by decide +kernel
theorem subd11_1_827 : subd11_1 [3, 0, -5] = true := by decide +kernel
theorem subd11_1_828 : subd11_1 [3, 0, -4] = true := by decide +kernel
theorem subd11_1_829 : subd11_1 [3, 0, -3] = true := by decide +kernel
theorem subd11_1_830 : subd11_1 [3, 0, -2] = true := by decide +kernel
theorem subd11_1_831 : subd11_1 [3, 0, -1] = true := by decide +kernel
theorem sbd11_1_25 : ∀ q ∈ blkd11_1_25, subd11_1 q = true := by
  unfold blkd11_1_25
  exact List.forall_mem_cons.2 ⟨subd11_1_800, List.forall_mem_cons.2 ⟨subd11_1_801, List.forall_mem_cons.2 ⟨subd11_1_802, List.forall_mem_cons.2 ⟨subd11_1_803, List.forall_mem_cons.2 ⟨subd11_1_804, List.forall_mem_cons.2 ⟨subd11_1_805, List.forall_mem_cons.2 ⟨subd11_1_806, List.forall_mem_cons.2 ⟨subd11_1_807, List.forall_mem_cons.2 ⟨subd11_1_808, List.forall_mem_cons.2 ⟨subd11_1_809, List.forall_mem_cons.2 ⟨subd11_1_810, List.forall_mem_cons.2 ⟨subd11_1_811, List.forall_mem_cons.2 ⟨subd11_1_812, List.forall_mem_cons.2 ⟨subd11_1_813, List.forall_mem_cons.2 ⟨subd11_1_814, List.forall_mem_cons.2 ⟨subd11_1_815, List.forall_mem_cons.2 ⟨subd11_1_816, List.forall_mem_cons.2 ⟨subd11_1_817, List.forall_mem_cons.2 ⟨subd11_1_818, List.forall_mem_cons.2 ⟨subd11_1_819, List.forall_mem_cons.2 ⟨subd11_1_820, List.forall_mem_cons.2 ⟨subd11_1_821, List.forall_mem_cons.2 ⟨subd11_1_822, List.forall_mem_cons.2 ⟨subd11_1_823, List.forall_mem_cons.2 ⟨subd11_1_824, List.forall_mem_cons.2 ⟨subd11_1_825, List.forall_mem_cons.2 ⟨subd11_1_826, List.forall_mem_cons.2 ⟨subd11_1_827, List.forall_mem_cons.2 ⟨subd11_1_828, List.forall_mem_cons.2 ⟨subd11_1_829, List.forall_mem_cons.2 ⟨subd11_1_830, List.forall_mem_cons.2 ⟨subd11_1_831, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C116
