import ReflectZphi.Data.Cert5.C101.Base

namespace ReflectZphi.Data.Cert5.C101

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd11_1_320 : subd11_1 [0, 2, 10] = true := by decide +kernel
theorem subd11_1_321 : subd11_1 [0, 2, 11] = true := by decide +kernel
theorem subd11_1_322 : subd11_1 [1, -2] = true := by decide +kernel
theorem subd11_1_323 : subd11_1 [1, -1, -15] = true := by decide +kernel
theorem subd11_1_324 : subd11_1 [1, -1, -14] = true := by decide +kernel
theorem subd11_1_325 : subd11_1 [1, -1, -13] = true := by decide +kernel
theorem subd11_1_326 : subd11_1 [1, -1, -12] = true := by decide +kernel
theorem subd11_1_327 : subd11_1 [1, -1, -11] = true := by decide +kernel
theorem subd11_1_328 : subd11_1 [1, -1, -10] = true := by decide +kernel
theorem subd11_1_329 : subd11_1 [1, -1, -9] = true := by decide +kernel
theorem subd11_1_330 : subd11_1 [1, -1, -8] = true := by decide +kernel
theorem subd11_1_331 : subd11_1 [1, -1, -7] = true := by decide +kernel
theorem subd11_1_332 : subd11_1 [1, -1, -6] = true := by decide +kernel
theorem subd11_1_333 : subd11_1 [1, -1, -5] = true := by decide +kernel
theorem subd11_1_334 : subd11_1 [1, -1, -4] = true := by decide +kernel
theorem subd11_1_335 : subd11_1 [1, -1, -3] = true := by decide +kernel
theorem subd11_1_336 : subd11_1 [1, -1, -2] = true := by decide +kernel
theorem subd11_1_337 : subd11_1 [1, -1, -1] = true := by decide +kernel
theorem subd11_1_338 : subd11_1 [1, -1, 0] = true := by decide +kernel
theorem subd11_1_339 : subd11_1 [1, -1, 1] = true := by decide +kernel
theorem subd11_1_340 : subd11_1 [1, -1, 2] = true := by decide +kernel
theorem subd11_1_341 : subd11_1 [1, -1, 3] = true := by decide +kernel
theorem subd11_1_342 : subd11_1 [1, -1, 4] = true := by decide +kernel
theorem subd11_1_343 : subd11_1 [1, -1, 5] = true := by decide +kernel
theorem subd11_1_344 : subd11_1 [1, -1, 6] = true := by decide +kernel
theorem subd11_1_345 : subd11_1 [1, -1, 7] = true := by decide +kernel
theorem subd11_1_346 : subd11_1 [1, -1, 8] = true := by decide +kernel
theorem subd11_1_347 : subd11_1 [1, -1, 9] = true := by decide +kernel
theorem subd11_1_348 : subd11_1 [1, -1, 10] = true := by decide +kernel
theorem subd11_1_349 : subd11_1 [1, -1, 11] = true := by decide +kernel
theorem subd11_1_350 : subd11_1 [1, -1, 12] = true := by decide +kernel
theorem subd11_1_351 : subd11_1 [1, -1, 13] = true := by decide +kernel
theorem sbd11_1_10 : ∀ q ∈ blkd11_1_10, subd11_1 q = true := by
  unfold blkd11_1_10
  exact List.forall_mem_cons.2 ⟨subd11_1_320, List.forall_mem_cons.2 ⟨subd11_1_321, List.forall_mem_cons.2 ⟨subd11_1_322, List.forall_mem_cons.2 ⟨subd11_1_323, List.forall_mem_cons.2 ⟨subd11_1_324, List.forall_mem_cons.2 ⟨subd11_1_325, List.forall_mem_cons.2 ⟨subd11_1_326, List.forall_mem_cons.2 ⟨subd11_1_327, List.forall_mem_cons.2 ⟨subd11_1_328, List.forall_mem_cons.2 ⟨subd11_1_329, List.forall_mem_cons.2 ⟨subd11_1_330, List.forall_mem_cons.2 ⟨subd11_1_331, List.forall_mem_cons.2 ⟨subd11_1_332, List.forall_mem_cons.2 ⟨subd11_1_333, List.forall_mem_cons.2 ⟨subd11_1_334, List.forall_mem_cons.2 ⟨subd11_1_335, List.forall_mem_cons.2 ⟨subd11_1_336, List.forall_mem_cons.2 ⟨subd11_1_337, List.forall_mem_cons.2 ⟨subd11_1_338, List.forall_mem_cons.2 ⟨subd11_1_339, List.forall_mem_cons.2 ⟨subd11_1_340, List.forall_mem_cons.2 ⟨subd11_1_341, List.forall_mem_cons.2 ⟨subd11_1_342, List.forall_mem_cons.2 ⟨subd11_1_343, List.forall_mem_cons.2 ⟨subd11_1_344, List.forall_mem_cons.2 ⟨subd11_1_345, List.forall_mem_cons.2 ⟨subd11_1_346, List.forall_mem_cons.2 ⟨subd11_1_347, List.forall_mem_cons.2 ⟨subd11_1_348, List.forall_mem_cons.2 ⟨subd11_1_349, List.forall_mem_cons.2 ⟨subd11_1_350, List.forall_mem_cons.2 ⟨subd11_1_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_352 : subd11_1 [1, -1, 14] = true := by decide +kernel
theorem subd11_1_353 : subd11_1 [1, 0, -20] = true := by decide +kernel
theorem subd11_1_354 : subd11_1 [1, 0, -19] = true := by decide +kernel
theorem subd11_1_355 : subd11_1 [1, 0, -18] = true := by decide +kernel
theorem subd11_1_356 : subd11_1 [1, 0, -17] = true := by decide +kernel
theorem subd11_1_357 : subd11_1 [1, 0, -16] = true := by decide +kernel
theorem subd11_1_358 : subd11_1 [1, 0, -15] = true := by decide +kernel
theorem subd11_1_359 : subd11_1 [1, 0, -14] = true := by decide +kernel
theorem subd11_1_360 : subd11_1 [1, 0, -13] = true := by decide +kernel
theorem subd11_1_361 : subd11_1 [1, 0, -12] = true := by decide +kernel
theorem subd11_1_362 : subd11_1 [1, 0, -11] = true := by decide +kernel
theorem subd11_1_363 : subd11_1 [1, 0, -10] = true := by decide +kernel
theorem subd11_1_364 : subd11_1 [1, 0, -9] = true := by decide +kernel
theorem subd11_1_365 : subd11_1 [1, 0, -8] = true := by decide +kernel
theorem subd11_1_366 : subd11_1 [1, 0, -7] = true := by decide +kernel
theorem subd11_1_367 : subd11_1 [1, 0, -6] = true := by decide +kernel
theorem subd11_1_368 : subd11_1 [1, 0, -5] = true := by decide +kernel
theorem subd11_1_369 : subd11_1 [1, 0, -4] = true := by decide +kernel
theorem subd11_1_370 : subd11_1 [1, 0, -3] = true := by decide +kernel
theorem subd11_1_371 : subd11_1 [1, 0, -2] = true := by decide +kernel
theorem subd11_1_372 : subd11_1 [1, 0, -1] = true := by decide +kernel
theorem subd11_1_373 : subd11_1 [1, 0, 0] = true := by decide +kernel
theorem subd11_1_374 : subd11_1 [1, 0, 1] = true := by decide +kernel
theorem subd11_1_375 : subd11_1 [1, 0, 2] = true := by decide +kernel
theorem subd11_1_376 : subd11_1 [1, 0, 3] = true := by decide +kernel
theorem subd11_1_377 : subd11_1 [1, 0, 4] = true := by decide +kernel
theorem subd11_1_378 : subd11_1 [1, 0, 5] = true := by decide +kernel
theorem subd11_1_379 : subd11_1 [1, 0, 6] = true := by decide +kernel
theorem subd11_1_380 : subd11_1 [1, 0, 7] = true := by decide +kernel
theorem subd11_1_381 : subd11_1 [1, 0, 8] = true := by decide +kernel
theorem subd11_1_382 : subd11_1 [1, 0, 9] = true := by decide +kernel
theorem subd11_1_383 : subd11_1 [1, 0, 10] = true := by decide +kernel
theorem sbd11_1_11 : ∀ q ∈ blkd11_1_11, subd11_1 q = true := by
  unfold blkd11_1_11
  exact List.forall_mem_cons.2 ⟨subd11_1_352, List.forall_mem_cons.2 ⟨subd11_1_353, List.forall_mem_cons.2 ⟨subd11_1_354, List.forall_mem_cons.2 ⟨subd11_1_355, List.forall_mem_cons.2 ⟨subd11_1_356, List.forall_mem_cons.2 ⟨subd11_1_357, List.forall_mem_cons.2 ⟨subd11_1_358, List.forall_mem_cons.2 ⟨subd11_1_359, List.forall_mem_cons.2 ⟨subd11_1_360, List.forall_mem_cons.2 ⟨subd11_1_361, List.forall_mem_cons.2 ⟨subd11_1_362, List.forall_mem_cons.2 ⟨subd11_1_363, List.forall_mem_cons.2 ⟨subd11_1_364, List.forall_mem_cons.2 ⟨subd11_1_365, List.forall_mem_cons.2 ⟨subd11_1_366, List.forall_mem_cons.2 ⟨subd11_1_367, List.forall_mem_cons.2 ⟨subd11_1_368, List.forall_mem_cons.2 ⟨subd11_1_369, List.forall_mem_cons.2 ⟨subd11_1_370, List.forall_mem_cons.2 ⟨subd11_1_371, List.forall_mem_cons.2 ⟨subd11_1_372, List.forall_mem_cons.2 ⟨subd11_1_373, List.forall_mem_cons.2 ⟨subd11_1_374, List.forall_mem_cons.2 ⟨subd11_1_375, List.forall_mem_cons.2 ⟨subd11_1_376, List.forall_mem_cons.2 ⟨subd11_1_377, List.forall_mem_cons.2 ⟨subd11_1_378, List.forall_mem_cons.2 ⟨subd11_1_379, List.forall_mem_cons.2 ⟨subd11_1_380, List.forall_mem_cons.2 ⟨subd11_1_381, List.forall_mem_cons.2 ⟨subd11_1_382, List.forall_mem_cons.2 ⟨subd11_1_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_384 : subd11_1 [1, 0, 11] = true := by decide +kernel
theorem subd11_1_385 : subd11_1 [1, 0, 12] = true := by decide +kernel
theorem subd11_1_386 : subd11_1 [1, 0, 13] = true := by decide +kernel
theorem subd11_1_387 : subd11_1 [1, 0, 14] = true := by decide +kernel
theorem subd11_1_388 : subd11_1 [1, 0, 15] = true := by decide +kernel
theorem subd11_1_389 : subd11_1 [1, 0, 16] = true := by decide +kernel
theorem subd11_1_390 : subd11_1 [1, 0, 17] = true := by decide +kernel
theorem subd11_1_391 : subd11_1 [1, 0, 18] = true := by decide +kernel
theorem subd11_1_392 : subd11_1 [1, 0, 19] = true := by decide +kernel
theorem subd11_1_393 : subd11_1 [1, 0, 20] = true := by decide +kernel
theorem subd11_1_394 : subd11_1 [1, 1, -20] = true := by decide +kernel
theorem subd11_1_395 : subd11_1 [1, 1, -19] = true := by decide +kernel
theorem subd11_1_396 : subd11_1 [1, 1, -18] = true := by decide +kernel
theorem subd11_1_397 : subd11_1 [1, 1, -17] = true := by decide +kernel
theorem subd11_1_398 : subd11_1 [1, 1, -16] = true := by decide +kernel
theorem subd11_1_399 : subd11_1 [1, 1, -15] = true := by decide +kernel
theorem subd11_1_400 : subd11_1 [1, 1, -14] = true := by decide +kernel
theorem subd11_1_401 : subd11_1 [1, 1, -13] = true := by decide +kernel
theorem subd11_1_402 : subd11_1 [1, 1, -12] = true := by decide +kernel
theorem subd11_1_403 : subd11_1 [1, 1, -11] = true := by decide +kernel
theorem subd11_1_404 : subd11_1 [1, 1, -10] = true := by decide +kernel
theorem subd11_1_405 : subd11_1 [1, 1, -9] = true := by decide +kernel
theorem subd11_1_406 : subd11_1 [1, 1, -8] = true := by decide +kernel
theorem subd11_1_407 : subd11_1 [1, 1, -7] = true := by decide +kernel
theorem subd11_1_408 : subd11_1 [1, 1, -6] = true := by decide +kernel
theorem subd11_1_409 : subd11_1 [1, 1, -5] = true := by decide +kernel
theorem subd11_1_410 : subd11_1 [1, 1, -4] = true := by decide +kernel
theorem subd11_1_411 : subd11_1 [1, 1, -3] = true := by decide +kernel
theorem subd11_1_412 : subd11_1 [1, 1, -2] = true := by decide +kernel
theorem subd11_1_413 : subd11_1 [1, 1, -1] = true := by decide +kernel
theorem subd11_1_414 : subd11_1 [1, 1, 0] = true := by decide +kernel
theorem subd11_1_415 : subd11_1 [1, 1, 1] = true := by decide +kernel
theorem sbd11_1_12 : ∀ q ∈ blkd11_1_12, subd11_1 q = true := by
  unfold blkd11_1_12
  exact List.forall_mem_cons.2 ⟨subd11_1_384, List.forall_mem_cons.2 ⟨subd11_1_385, List.forall_mem_cons.2 ⟨subd11_1_386, List.forall_mem_cons.2 ⟨subd11_1_387, List.forall_mem_cons.2 ⟨subd11_1_388, List.forall_mem_cons.2 ⟨subd11_1_389, List.forall_mem_cons.2 ⟨subd11_1_390, List.forall_mem_cons.2 ⟨subd11_1_391, List.forall_mem_cons.2 ⟨subd11_1_392, List.forall_mem_cons.2 ⟨subd11_1_393, List.forall_mem_cons.2 ⟨subd11_1_394, List.forall_mem_cons.2 ⟨subd11_1_395, List.forall_mem_cons.2 ⟨subd11_1_396, List.forall_mem_cons.2 ⟨subd11_1_397, List.forall_mem_cons.2 ⟨subd11_1_398, List.forall_mem_cons.2 ⟨subd11_1_399, List.forall_mem_cons.2 ⟨subd11_1_400, List.forall_mem_cons.2 ⟨subd11_1_401, List.forall_mem_cons.2 ⟨subd11_1_402, List.forall_mem_cons.2 ⟨subd11_1_403, List.forall_mem_cons.2 ⟨subd11_1_404, List.forall_mem_cons.2 ⟨subd11_1_405, List.forall_mem_cons.2 ⟨subd11_1_406, List.forall_mem_cons.2 ⟨subd11_1_407, List.forall_mem_cons.2 ⟨subd11_1_408, List.forall_mem_cons.2 ⟨subd11_1_409, List.forall_mem_cons.2 ⟨subd11_1_410, List.forall_mem_cons.2 ⟨subd11_1_411, List.forall_mem_cons.2 ⟨subd11_1_412, List.forall_mem_cons.2 ⟨subd11_1_413, List.forall_mem_cons.2 ⟨subd11_1_414, List.forall_mem_cons.2 ⟨subd11_1_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_416 : subd11_1 [1, 1, 2] = true := by decide +kernel
theorem subd11_1_417 : subd11_1 [1, 1, 3] = true := by decide +kernel
theorem subd11_1_418 : subd11_1 [1, 1, 4] = true := by decide +kernel
theorem subd11_1_419 : subd11_1 [1, 1, 5] = true := by decide +kernel
theorem subd11_1_420 : subd11_1 [1, 1, 6] = true := by decide +kernel
theorem subd11_1_421 : subd11_1 [1, 1, 7] = true := by decide +kernel
theorem subd11_1_422 : subd11_1 [1, 1, 8] = true := by decide +kernel
theorem subd11_1_423 : subd11_1 [1, 1, 9] = true := by decide +kernel
theorem subd11_1_424 : subd11_1 [1, 1, 10] = true := by decide +kernel
theorem subd11_1_425 : subd11_1 [1, 1, 11] = true := by decide +kernel
theorem subd11_1_426 : subd11_1 [1, 1, 12] = true := by decide +kernel
theorem subd11_1_427 : subd11_1 [1, 1, 13] = true := by decide +kernel
theorem subd11_1_428 : subd11_1 [1, 1, 14] = true := by decide +kernel
theorem subd11_1_429 : subd11_1 [1, 1, 15] = true := by decide +kernel
theorem subd11_1_430 : subd11_1 [1, 1, 16] = true := by decide +kernel
theorem subd11_1_431 : subd11_1 [1, 1, 17] = true := by decide +kernel
theorem subd11_1_432 : subd11_1 [1, 1, 18] = true := by decide +kernel
theorem subd11_1_433 : subd11_1 [1, 1, 19] = true := by decide +kernel
theorem subd11_1_434 : subd11_1 [1, 2, -13] = true := by decide +kernel
theorem subd11_1_435 : subd11_1 [1, 2, -12] = true := by decide +kernel
theorem subd11_1_436 : subd11_1 [1, 2, -11] = true := by decide +kernel
theorem subd11_1_437 : subd11_1 [1, 2, -10] = true := by decide +kernel
theorem subd11_1_438 : subd11_1 [1, 2, -9] = true := by decide +kernel
theorem subd11_1_439 : subd11_1 [1, 2, -8] = true := by decide +kernel
theorem subd11_1_440 : subd11_1 [1, 2, -7] = true := by decide +kernel
theorem subd11_1_441 : subd11_1 [1, 2, -6] = true := by decide +kernel
theorem subd11_1_442 : subd11_1 [1, 2, -5] = true := by decide +kernel
theorem subd11_1_443 : subd11_1 [1, 2, -4] = true := by decide +kernel
theorem subd11_1_444 : subd11_1 [1, 2, -3] = true := by decide +kernel
theorem subd11_1_445 : subd11_1 [1, 2, -2] = true := by decide +kernel
theorem subd11_1_446 : subd11_1 [1, 2, -1] = true := by decide +kernel
theorem subd11_1_447 : subd11_1 [1, 2, 0] = true := by decide +kernel
theorem sbd11_1_13 : ∀ q ∈ blkd11_1_13, subd11_1 q = true := by
  unfold blkd11_1_13
  exact List.forall_mem_cons.2 ⟨subd11_1_416, List.forall_mem_cons.2 ⟨subd11_1_417, List.forall_mem_cons.2 ⟨subd11_1_418, List.forall_mem_cons.2 ⟨subd11_1_419, List.forall_mem_cons.2 ⟨subd11_1_420, List.forall_mem_cons.2 ⟨subd11_1_421, List.forall_mem_cons.2 ⟨subd11_1_422, List.forall_mem_cons.2 ⟨subd11_1_423, List.forall_mem_cons.2 ⟨subd11_1_424, List.forall_mem_cons.2 ⟨subd11_1_425, List.forall_mem_cons.2 ⟨subd11_1_426, List.forall_mem_cons.2 ⟨subd11_1_427, List.forall_mem_cons.2 ⟨subd11_1_428, List.forall_mem_cons.2 ⟨subd11_1_429, List.forall_mem_cons.2 ⟨subd11_1_430, List.forall_mem_cons.2 ⟨subd11_1_431, List.forall_mem_cons.2 ⟨subd11_1_432, List.forall_mem_cons.2 ⟨subd11_1_433, List.forall_mem_cons.2 ⟨subd11_1_434, List.forall_mem_cons.2 ⟨subd11_1_435, List.forall_mem_cons.2 ⟨subd11_1_436, List.forall_mem_cons.2 ⟨subd11_1_437, List.forall_mem_cons.2 ⟨subd11_1_438, List.forall_mem_cons.2 ⟨subd11_1_439, List.forall_mem_cons.2 ⟨subd11_1_440, List.forall_mem_cons.2 ⟨subd11_1_441, List.forall_mem_cons.2 ⟨subd11_1_442, List.forall_mem_cons.2 ⟨subd11_1_443, List.forall_mem_cons.2 ⟨subd11_1_444, List.forall_mem_cons.2 ⟨subd11_1_445, List.forall_mem_cons.2 ⟨subd11_1_446, List.forall_mem_cons.2 ⟨subd11_1_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_448 : subd11_1 [1, 2, 1] = true := by decide +kernel
theorem subd11_1_449 : subd11_1 [1, 2, 2] = true := by decide +kernel
theorem subd11_1_450 : subd11_1 [1, 2, 3] = true := by decide +kernel
theorem subd11_1_451 : subd11_1 [1, 2, 4] = true := by decide +kernel
theorem subd11_1_452 : subd11_1 [1, 2, 5] = true := by decide +kernel
theorem subd11_1_453 : subd11_1 [1, 2, 6] = true := by decide +kernel
theorem subd11_1_454 : subd11_1 [1, 2, 7] = true := by decide +kernel
theorem subd11_1_455 : subd11_1 [1, 2, 8] = true := by decide +kernel
theorem subd11_1_456 : subd11_1 [1, 2, 9] = true := by decide +kernel
theorem subd11_1_457 : subd11_1 [1, 2, 10] = true := by decide +kernel
theorem subd11_1_458 : subd11_1 [1, 2, 11] = true := by decide +kernel
theorem subd11_1_459 : subd11_1 [1, 2, 12] = true := by decide +kernel
theorem subd11_1_460 : subd11_1 [2] = true := by decide +kernel
theorem sbd11_1_14 : ∀ q ∈ blkd11_1_14, subd11_1 q = true := by
  unfold blkd11_1_14
  exact List.forall_mem_cons.2 ⟨subd11_1_448, List.forall_mem_cons.2 ⟨subd11_1_449, List.forall_mem_cons.2 ⟨subd11_1_450, List.forall_mem_cons.2 ⟨subd11_1_451, List.forall_mem_cons.2 ⟨subd11_1_452, List.forall_mem_cons.2 ⟨subd11_1_453, List.forall_mem_cons.2 ⟨subd11_1_454, List.forall_mem_cons.2 ⟨subd11_1_455, List.forall_mem_cons.2 ⟨subd11_1_456, List.forall_mem_cons.2 ⟨subd11_1_457, List.forall_mem_cons.2 ⟨subd11_1_458, List.forall_mem_cons.2 ⟨subd11_1_459, List.forall_mem_cons.2 ⟨subd11_1_460, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd12_0 : ldCheck G d12_0.U d12_0.ms ldd12_0 = true := by decide +kernel
theorem pre_okd12_0 : subPre G cell12 d12_0 = true := by decide +kernel
theorem subd12_0_0 : subd12_0 [-3, -2] = true := by decide +kernel
theorem subd12_0_1 : subd12_0 [-3, -1] = true := by decide +kernel
theorem subd12_0_2 : subd12_0 [-3, 0] = true := by decide +kernel
theorem subd12_0_3 : subd12_0 [-3, 1] = true := by decide +kernel
theorem subd12_0_4 : subd12_0 [-3, 2] = true := by decide +kernel
theorem subd12_0_5 : subd12_0 [-3, 3] = true := by decide +kernel
theorem subd12_0_6 : subd12_0 [-2, -3] = true := by decide +kernel
theorem subd12_0_7 : subd12_0 [-2, -2] = true := by decide +kernel
theorem subd12_0_8 : subd12_0 [-2, -1] = true := by decide +kernel
theorem subd12_0_9 : subd12_0 [-2, 0] = true := by decide +kernel
theorem subd12_0_10 : subd12_0 [-2, 1] = true := by decide +kernel
theorem subd12_0_11 : subd12_0 [-2, 2] = true := by decide +kernel
theorem subd12_0_12 : subd12_0 [-2, 3] = true := by decide +kernel
theorem subd12_0_13 : subd12_0 [-2, 4] = true := by decide +kernel
theorem subd12_0_14 : subd12_0 [-1, -4] = true := by decide +kernel
theorem subd12_0_15 : subd12_0 [-1, -3] = true := by decide +kernel
theorem subd12_0_16 : subd12_0 [-1, -2] = true := by decide +kernel
theorem subd12_0_17 : subd12_0 [-1, -1, -8] = true := by decide +kernel
theorem subd12_0_18 : subd12_0 [-1, -1, -7] = true := by decide +kernel
theorem subd12_0_19 : subd12_0 [-1, -1, -6] = true := by decide +kernel
theorem subd12_0_20 : subd12_0 [-1, -1, -5] = true := by decide +kernel
theorem subd12_0_21 : subd12_0 [-1, -1, -4] = true := by decide +kernel
theorem subd12_0_22 : subd12_0 [-1, -1, -3] = true := by decide +kernel
theorem subd12_0_23 : subd12_0 [-1, -1, -2] = true := by decide +kernel
theorem subd12_0_24 : subd12_0 [-1, -1, -1] = true := by decide +kernel
theorem subd12_0_25 : subd12_0 [-1, -1, 0] = true := by decide +kernel
theorem subd12_0_26 : subd12_0 [-1, -1, 1] = true := by decide +kernel
theorem subd12_0_27 : subd12_0 [-1, -1, 2] = true := by decide +kernel
theorem subd12_0_28 : subd12_0 [-1, -1, 3] = true := by decide +kernel
theorem subd12_0_29 : subd12_0 [-1, -1, 4] = true := by decide +kernel
theorem subd12_0_30 : subd12_0 [-1, -1, 5] = true := by decide +kernel
theorem subd12_0_31 : subd12_0 [-1, 0, -8] = true := by decide +kernel
theorem sbd12_0_0 : ∀ q ∈ blkd12_0_0, subd12_0 q = true := by
  unfold blkd12_0_0
  exact List.forall_mem_cons.2 ⟨subd12_0_0, List.forall_mem_cons.2 ⟨subd12_0_1, List.forall_mem_cons.2 ⟨subd12_0_2, List.forall_mem_cons.2 ⟨subd12_0_3, List.forall_mem_cons.2 ⟨subd12_0_4, List.forall_mem_cons.2 ⟨subd12_0_5, List.forall_mem_cons.2 ⟨subd12_0_6, List.forall_mem_cons.2 ⟨subd12_0_7, List.forall_mem_cons.2 ⟨subd12_0_8, List.forall_mem_cons.2 ⟨subd12_0_9, List.forall_mem_cons.2 ⟨subd12_0_10, List.forall_mem_cons.2 ⟨subd12_0_11, List.forall_mem_cons.2 ⟨subd12_0_12, List.forall_mem_cons.2 ⟨subd12_0_13, List.forall_mem_cons.2 ⟨subd12_0_14, List.forall_mem_cons.2 ⟨subd12_0_15, List.forall_mem_cons.2 ⟨subd12_0_16, List.forall_mem_cons.2 ⟨subd12_0_17, List.forall_mem_cons.2 ⟨subd12_0_18, List.forall_mem_cons.2 ⟨subd12_0_19, List.forall_mem_cons.2 ⟨subd12_0_20, List.forall_mem_cons.2 ⟨subd12_0_21, List.forall_mem_cons.2 ⟨subd12_0_22, List.forall_mem_cons.2 ⟨subd12_0_23, List.forall_mem_cons.2 ⟨subd12_0_24, List.forall_mem_cons.2 ⟨subd12_0_25, List.forall_mem_cons.2 ⟨subd12_0_26, List.forall_mem_cons.2 ⟨subd12_0_27, List.forall_mem_cons.2 ⟨subd12_0_28, List.forall_mem_cons.2 ⟨subd12_0_29, List.forall_mem_cons.2 ⟨subd12_0_30, List.forall_mem_cons.2 ⟨subd12_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_32 : subd12_0 [-1, 0, -7] = true := by decide +kernel
theorem subd12_0_33 : subd12_0 [-1, 0, -6] = true := by decide +kernel
theorem subd12_0_34 : subd12_0 [-1, 0, -5] = true := by decide +kernel
theorem subd12_0_35 : subd12_0 [-1, 0, -4] = true := by decide +kernel
theorem subd12_0_36 : subd12_0 [-1, 0, -3] = true := by decide +kernel
theorem subd12_0_37 : subd12_0 [-1, 0, -2] = true := by decide +kernel
theorem subd12_0_38 : subd12_0 [-1, 0, -1] = true := by decide +kernel
theorem subd12_0_39 : subd12_0 [-1, 0, 0] = true := by decide +kernel
theorem subd12_0_40 : subd12_0 [-1, 0, 1] = true := by decide +kernel
theorem subd12_0_41 : subd12_0 [-1, 0, 2] = true := by decide +kernel
theorem subd12_0_42 : subd12_0 [-1, 0, 3] = true := by decide +kernel
theorem subd12_0_43 : subd12_0 [-1, 0, 4] = true := by decide +kernel
theorem subd12_0_44 : subd12_0 [-1, 0, 5] = true := by decide +kernel
theorem subd12_0_45 : subd12_0 [-1, 0, 6] = true := by decide +kernel
theorem subd12_0_46 : subd12_0 [-1, 1, -7] = true := by decide +kernel
theorem subd12_0_47 : subd12_0 [-1, 1, -6] = true := by decide +kernel
theorem subd12_0_48 : subd12_0 [-1, 1, -5] = true := by decide +kernel
theorem subd12_0_49 : subd12_0 [-1, 1, -4] = true := by decide +kernel
theorem subd12_0_50 : subd12_0 [-1, 1, -3] = true := by decide +kernel
theorem subd12_0_51 : subd12_0 [-1, 1, -2] = true := by decide +kernel
theorem subd12_0_52 : subd12_0 [-1, 1, -1] = true := by decide +kernel
theorem subd12_0_53 : subd12_0 [-1, 1, 0] = true := by decide +kernel
theorem subd12_0_54 : subd12_0 [-1, 1, 1] = true := by decide +kernel
theorem subd12_0_55 : subd12_0 [-1, 1, 2] = true := by decide +kernel
theorem subd12_0_56 : subd12_0 [-1, 1, 3] = true := by decide +kernel
theorem subd12_0_57 : subd12_0 [-1, 1, 4] = true := by decide +kernel
theorem subd12_0_58 : subd12_0 [-1, 1, 5] = true := by decide +kernel
theorem subd12_0_59 : subd12_0 [-1, 1, 6] = true := by decide +kernel
theorem subd12_0_60 : subd12_0 [-1, 2, -6] = true := by decide +kernel
theorem subd12_0_61 : subd12_0 [-1, 2, -5] = true := by decide +kernel
theorem subd12_0_62 : subd12_0 [-1, 2, -4] = true := by decide +kernel
theorem subd12_0_63 : subd12_0 [-1, 2, -3] = true := by decide +kernel
theorem sbd12_0_1 : ∀ q ∈ blkd12_0_1, subd12_0 q = true := by
  unfold blkd12_0_1
  exact List.forall_mem_cons.2 ⟨subd12_0_32, List.forall_mem_cons.2 ⟨subd12_0_33, List.forall_mem_cons.2 ⟨subd12_0_34, List.forall_mem_cons.2 ⟨subd12_0_35, List.forall_mem_cons.2 ⟨subd12_0_36, List.forall_mem_cons.2 ⟨subd12_0_37, List.forall_mem_cons.2 ⟨subd12_0_38, List.forall_mem_cons.2 ⟨subd12_0_39, List.forall_mem_cons.2 ⟨subd12_0_40, List.forall_mem_cons.2 ⟨subd12_0_41, List.forall_mem_cons.2 ⟨subd12_0_42, List.forall_mem_cons.2 ⟨subd12_0_43, List.forall_mem_cons.2 ⟨subd12_0_44, List.forall_mem_cons.2 ⟨subd12_0_45, List.forall_mem_cons.2 ⟨subd12_0_46, List.forall_mem_cons.2 ⟨subd12_0_47, List.forall_mem_cons.2 ⟨subd12_0_48, List.forall_mem_cons.2 ⟨subd12_0_49, List.forall_mem_cons.2 ⟨subd12_0_50, List.forall_mem_cons.2 ⟨subd12_0_51, List.forall_mem_cons.2 ⟨subd12_0_52, List.forall_mem_cons.2 ⟨subd12_0_53, List.forall_mem_cons.2 ⟨subd12_0_54, List.forall_mem_cons.2 ⟨subd12_0_55, List.forall_mem_cons.2 ⟨subd12_0_56, List.forall_mem_cons.2 ⟨subd12_0_57, List.forall_mem_cons.2 ⟨subd12_0_58, List.forall_mem_cons.2 ⟨subd12_0_59, List.forall_mem_cons.2 ⟨subd12_0_60, List.forall_mem_cons.2 ⟨subd12_0_61, List.forall_mem_cons.2 ⟨subd12_0_62, List.forall_mem_cons.2 ⟨subd12_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_64 : subd12_0 [-1, 2, -2] = true := by decide +kernel
theorem subd12_0_65 : subd12_0 [-1, 2, -1] = true := by decide +kernel
theorem subd12_0_66 : subd12_0 [-1, 2, 0] = true := by decide +kernel
theorem subd12_0_67 : subd12_0 [-1, 2, 1] = true := by decide +kernel
theorem subd12_0_68 : subd12_0 [-1, 2, 2] = true := by decide +kernel
theorem subd12_0_69 : subd12_0 [-1, 2, 3] = true := by decide +kernel
theorem subd12_0_70 : subd12_0 [-1, 2, 4] = true := by decide +kernel
theorem subd12_0_71 : subd12_0 [-1, 2, 5] = true := by decide +kernel
theorem subd12_0_72 : subd12_0 [-1, 2, 6] = true := by decide +kernel
theorem subd12_0_73 : subd12_0 [-1, 3] = true := by decide +kernel
theorem subd12_0_74 : subd12_0 [-1, 4] = true := by decide +kernel
theorem subd12_0_75 : subd12_0 [0, -5] = true := by decide +kernel
theorem subd12_0_76 : subd12_0 [0, -4] = true := by decide +kernel
theorem subd12_0_77 : subd12_0 [0, -3] = true := by decide +kernel
theorem subd12_0_78 : subd12_0 [0, -2, -8] = true := by decide +kernel
theorem subd12_0_79 : subd12_0 [0, -2, -7] = true := by decide +kernel
theorem subd12_0_80 : subd12_0 [0, -2, -6] = true := by decide +kernel
theorem subd12_0_81 : subd12_0 [0, -2, -5] = true := by decide +kernel
theorem subd12_0_82 : subd12_0 [0, -2, -4] = true := by decide +kernel
theorem subd12_0_83 : subd12_0 [0, -2, -3] = true := by decide +kernel
theorem subd12_0_84 : subd12_0 [0, -2, -2] = true := by decide +kernel
theorem subd12_0_85 : subd12_0 [0, -2, -1] = true := by decide +kernel
theorem subd12_0_86 : subd12_0 [0, -2, 0] = true := by decide +kernel
theorem subd12_0_87 : subd12_0 [0, -2, 1] = true := by decide +kernel
theorem subd12_0_88 : subd12_0 [0, -2, 2] = true := by decide +kernel
theorem subd12_0_89 : subd12_0 [0, -2, 3] = true := by decide +kernel
theorem subd12_0_90 : subd12_0 [0, -2, 4] = true := by decide +kernel
theorem subd12_0_91 : subd12_0 [0, -2, 5] = true := by decide +kernel
theorem subd12_0_92 : subd12_0 [0, -1, -8] = true := by decide +kernel
theorem subd12_0_93 : subd12_0 [0, -1, -7] = true := by decide +kernel
theorem subd12_0_94 : subd12_0 [0, -1, -6] = true := by decide +kernel
theorem subd12_0_95 : subd12_0 [0, -1, -5] = true := by decide +kernel
theorem sbd12_0_2 : ∀ q ∈ blkd12_0_2, subd12_0 q = true := by
  unfold blkd12_0_2
  exact List.forall_mem_cons.2 ⟨subd12_0_64, List.forall_mem_cons.2 ⟨subd12_0_65, List.forall_mem_cons.2 ⟨subd12_0_66, List.forall_mem_cons.2 ⟨subd12_0_67, List.forall_mem_cons.2 ⟨subd12_0_68, List.forall_mem_cons.2 ⟨subd12_0_69, List.forall_mem_cons.2 ⟨subd12_0_70, List.forall_mem_cons.2 ⟨subd12_0_71, List.forall_mem_cons.2 ⟨subd12_0_72, List.forall_mem_cons.2 ⟨subd12_0_73, List.forall_mem_cons.2 ⟨subd12_0_74, List.forall_mem_cons.2 ⟨subd12_0_75, List.forall_mem_cons.2 ⟨subd12_0_76, List.forall_mem_cons.2 ⟨subd12_0_77, List.forall_mem_cons.2 ⟨subd12_0_78, List.forall_mem_cons.2 ⟨subd12_0_79, List.forall_mem_cons.2 ⟨subd12_0_80, List.forall_mem_cons.2 ⟨subd12_0_81, List.forall_mem_cons.2 ⟨subd12_0_82, List.forall_mem_cons.2 ⟨subd12_0_83, List.forall_mem_cons.2 ⟨subd12_0_84, List.forall_mem_cons.2 ⟨subd12_0_85, List.forall_mem_cons.2 ⟨subd12_0_86, List.forall_mem_cons.2 ⟨subd12_0_87, List.forall_mem_cons.2 ⟨subd12_0_88, List.forall_mem_cons.2 ⟨subd12_0_89, List.forall_mem_cons.2 ⟨subd12_0_90, List.forall_mem_cons.2 ⟨subd12_0_91, List.forall_mem_cons.2 ⟨subd12_0_92, List.forall_mem_cons.2 ⟨subd12_0_93, List.forall_mem_cons.2 ⟨subd12_0_94, List.forall_mem_cons.2 ⟨subd12_0_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C101
