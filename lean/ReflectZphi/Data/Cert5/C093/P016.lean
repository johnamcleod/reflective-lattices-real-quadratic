import ReflectZphi.Data.Cert5.C093.Base

namespace ReflectZphi.Data.Cert5.C093

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_0_352 : subd8_0 [-1, -1, -3] = true := by decide +kernel
theorem subd8_0_353 : subd8_0 [-1, -1, -2] = true := by decide +kernel
theorem subd8_0_354 : subd8_0 [-1, -1, -1] = true := by decide +kernel
theorem subd8_0_355 : subd8_0 [-1, -1, 0] = true := by decide +kernel
theorem subd8_0_356 : subd8_0 [-1, -1, 1] = true := by decide +kernel
theorem subd8_0_357 : subd8_0 [-1, -1, 2] = true := by decide +kernel
theorem subd8_0_358 : subd8_0 [-1, -1, 3] = true := by decide +kernel
theorem subd8_0_359 : subd8_0 [-1, -1, 4] = true := by decide +kernel
theorem subd8_0_360 : subd8_0 [-1, -1, 5] = true := by decide +kernel
theorem subd8_0_361 : subd8_0 [-1, -1, 6] = true := by decide +kernel
theorem subd8_0_362 : subd8_0 [-1, -1, 7] = true := by decide +kernel
theorem subd8_0_363 : subd8_0 [-1, -1, 8] = true := by decide +kernel
theorem subd8_0_364 : subd8_0 [-1, 0, -9] = true := by decide +kernel
theorem subd8_0_365 : subd8_0 [-1, 0, -8] = true := by decide +kernel
theorem subd8_0_366 : subd8_0 [-1, 0, -7] = true := by decide +kernel
theorem subd8_0_367 : subd8_0 [-1, 0, -6] = true := by decide +kernel
theorem subd8_0_368 : subd8_0 [-1, 0, -5] = true := by decide +kernel
theorem subd8_0_369 : subd8_0 [-1, 0, -4] = true := by decide +kernel
theorem subd8_0_370 : subd8_0 [-1, 0, -3] = true := by decide +kernel
theorem subd8_0_371 : subd8_0 [-1, 0, -2] = true := by decide +kernel
theorem subd8_0_372 : subd8_0 [-1, 0, -1] = true := by decide +kernel
theorem subd8_0_373 : subd8_0 [-1, 0, 0] = true := by decide +kernel
theorem subd8_0_374 : subd8_0 [-1, 0, 1] = true := by decide +kernel
theorem subd8_0_375 : subd8_0 [-1, 0, 2] = true := by decide +kernel
theorem subd8_0_376 : subd8_0 [-1, 0, 3] = true := by decide +kernel
theorem subd8_0_377 : subd8_0 [-1, 0, 4] = true := by decide +kernel
theorem subd8_0_378 : subd8_0 [-1, 0, 5] = true := by decide +kernel
theorem subd8_0_379 : subd8_0 [-1, 0, 6] = true := by decide +kernel
theorem subd8_0_380 : subd8_0 [-1, 0, 7] = true := by decide +kernel
theorem subd8_0_381 : subd8_0 [-1, 0, 8] = true := by decide +kernel
theorem subd8_0_382 : subd8_0 [-1, 1, -9] = true := by decide +kernel
theorem subd8_0_383 : subd8_0 [-1, 1, -8] = true := by decide +kernel
theorem sbd8_0_11 : ∀ q ∈ blkd8_0_11, subd8_0 q = true := by
  unfold blkd8_0_11
  exact List.forall_mem_cons.2 ⟨subd8_0_352, List.forall_mem_cons.2 ⟨subd8_0_353, List.forall_mem_cons.2 ⟨subd8_0_354, List.forall_mem_cons.2 ⟨subd8_0_355, List.forall_mem_cons.2 ⟨subd8_0_356, List.forall_mem_cons.2 ⟨subd8_0_357, List.forall_mem_cons.2 ⟨subd8_0_358, List.forall_mem_cons.2 ⟨subd8_0_359, List.forall_mem_cons.2 ⟨subd8_0_360, List.forall_mem_cons.2 ⟨subd8_0_361, List.forall_mem_cons.2 ⟨subd8_0_362, List.forall_mem_cons.2 ⟨subd8_0_363, List.forall_mem_cons.2 ⟨subd8_0_364, List.forall_mem_cons.2 ⟨subd8_0_365, List.forall_mem_cons.2 ⟨subd8_0_366, List.forall_mem_cons.2 ⟨subd8_0_367, List.forall_mem_cons.2 ⟨subd8_0_368, List.forall_mem_cons.2 ⟨subd8_0_369, List.forall_mem_cons.2 ⟨subd8_0_370, List.forall_mem_cons.2 ⟨subd8_0_371, List.forall_mem_cons.2 ⟨subd8_0_372, List.forall_mem_cons.2 ⟨subd8_0_373, List.forall_mem_cons.2 ⟨subd8_0_374, List.forall_mem_cons.2 ⟨subd8_0_375, List.forall_mem_cons.2 ⟨subd8_0_376, List.forall_mem_cons.2 ⟨subd8_0_377, List.forall_mem_cons.2 ⟨subd8_0_378, List.forall_mem_cons.2 ⟨subd8_0_379, List.forall_mem_cons.2 ⟨subd8_0_380, List.forall_mem_cons.2 ⟨subd8_0_381, List.forall_mem_cons.2 ⟨subd8_0_382, List.forall_mem_cons.2 ⟨subd8_0_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_384 : subd8_0 [-1, 1, -7] = true := by decide +kernel
theorem subd8_0_385 : subd8_0 [-1, 1, -6] = true := by decide +kernel
theorem subd8_0_386 : subd8_0 [-1, 1, -5] = true := by decide +kernel
theorem subd8_0_387 : subd8_0 [-1, 1, -4] = true := by decide +kernel
theorem subd8_0_388 : subd8_0 [-1, 1, -3] = true := by decide +kernel
theorem subd8_0_389 : subd8_0 [-1, 1, -2] = true := by decide +kernel
theorem subd8_0_390 : subd8_0 [-1, 1, -1] = true := by decide +kernel
theorem subd8_0_391 : subd8_0 [-1, 1, 0] = true := by decide +kernel
theorem subd8_0_392 : subd8_0 [-1, 1, 1] = true := by decide +kernel
theorem subd8_0_393 : subd8_0 [-1, 1, 2] = true := by decide +kernel
theorem subd8_0_394 : subd8_0 [-1, 1, 3] = true := by decide +kernel
theorem subd8_0_395 : subd8_0 [-1, 1, 4] = true := by decide +kernel
theorem subd8_0_396 : subd8_0 [-1, 1, 5] = true := by decide +kernel
theorem subd8_0_397 : subd8_0 [-1, 1, 6] = true := by decide +kernel
theorem subd8_0_398 : subd8_0 [-1, 1, 7] = true := by decide +kernel
theorem subd8_0_399 : subd8_0 [-1, 1, 8] = true := by decide +kernel
theorem subd8_0_400 : subd8_0 [-1, 2, -8] = true := by decide +kernel
theorem subd8_0_401 : subd8_0 [-1, 2, -7] = true := by decide +kernel
theorem subd8_0_402 : subd8_0 [-1, 2, -6] = true := by decide +kernel
theorem subd8_0_403 : subd8_0 [-1, 2, -5] = true := by decide +kernel
theorem subd8_0_404 : subd8_0 [-1, 2, -4] = true := by decide +kernel
theorem subd8_0_405 : subd8_0 [-1, 2, -3] = true := by decide +kernel
theorem subd8_0_406 : subd8_0 [-1, 2, -2] = true := by decide +kernel
theorem subd8_0_407 : subd8_0 [-1, 2, -1] = true := by decide +kernel
theorem subd8_0_408 : subd8_0 [-1, 2, 0] = true := by decide +kernel
theorem subd8_0_409 : subd8_0 [-1, 2, 1] = true := by decide +kernel
theorem subd8_0_410 : subd8_0 [-1, 2, 2] = true := by decide +kernel
theorem subd8_0_411 : subd8_0 [-1, 2, 3] = true := by decide +kernel
theorem subd8_0_412 : subd8_0 [-1, 2, 4] = true := by decide +kernel
theorem subd8_0_413 : subd8_0 [-1, 2, 5] = true := by decide +kernel
theorem subd8_0_414 : subd8_0 [-1, 2, 6] = true := by decide +kernel
theorem subd8_0_415 : subd8_0 [-1, 2, 7] = true := by decide +kernel
theorem sbd8_0_12 : ∀ q ∈ blkd8_0_12, subd8_0 q = true := by
  unfold blkd8_0_12
  exact List.forall_mem_cons.2 ⟨subd8_0_384, List.forall_mem_cons.2 ⟨subd8_0_385, List.forall_mem_cons.2 ⟨subd8_0_386, List.forall_mem_cons.2 ⟨subd8_0_387, List.forall_mem_cons.2 ⟨subd8_0_388, List.forall_mem_cons.2 ⟨subd8_0_389, List.forall_mem_cons.2 ⟨subd8_0_390, List.forall_mem_cons.2 ⟨subd8_0_391, List.forall_mem_cons.2 ⟨subd8_0_392, List.forall_mem_cons.2 ⟨subd8_0_393, List.forall_mem_cons.2 ⟨subd8_0_394, List.forall_mem_cons.2 ⟨subd8_0_395, List.forall_mem_cons.2 ⟨subd8_0_396, List.forall_mem_cons.2 ⟨subd8_0_397, List.forall_mem_cons.2 ⟨subd8_0_398, List.forall_mem_cons.2 ⟨subd8_0_399, List.forall_mem_cons.2 ⟨subd8_0_400, List.forall_mem_cons.2 ⟨subd8_0_401, List.forall_mem_cons.2 ⟨subd8_0_402, List.forall_mem_cons.2 ⟨subd8_0_403, List.forall_mem_cons.2 ⟨subd8_0_404, List.forall_mem_cons.2 ⟨subd8_0_405, List.forall_mem_cons.2 ⟨subd8_0_406, List.forall_mem_cons.2 ⟨subd8_0_407, List.forall_mem_cons.2 ⟨subd8_0_408, List.forall_mem_cons.2 ⟨subd8_0_409, List.forall_mem_cons.2 ⟨subd8_0_410, List.forall_mem_cons.2 ⟨subd8_0_411, List.forall_mem_cons.2 ⟨subd8_0_412, List.forall_mem_cons.2 ⟨subd8_0_413, List.forall_mem_cons.2 ⟨subd8_0_414, List.forall_mem_cons.2 ⟨subd8_0_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_416 : subd8_0 [-1, 2, 8] = true := by decide +kernel
theorem subd8_0_417 : subd8_0 [-1, 3, -7] = true := by decide +kernel
theorem subd8_0_418 : subd8_0 [-1, 3, -6] = true := by decide +kernel
theorem subd8_0_419 : subd8_0 [-1, 3, -5] = true := by decide +kernel
theorem subd8_0_420 : subd8_0 [-1, 3, -4] = true := by decide +kernel
theorem subd8_0_421 : subd8_0 [-1, 3, -3] = true := by decide +kernel
theorem subd8_0_422 : subd8_0 [-1, 3, -2] = true := by decide +kernel
theorem subd8_0_423 : subd8_0 [-1, 3, -1] = true := by decide +kernel
theorem subd8_0_424 : subd8_0 [-1, 3, 0] = true := by decide +kernel
theorem subd8_0_425 : subd8_0 [-1, 3, 1] = true := by decide +kernel
theorem subd8_0_426 : subd8_0 [-1, 3, 2] = true := by decide +kernel
theorem subd8_0_427 : subd8_0 [-1, 3, 3] = true := by decide +kernel
theorem subd8_0_428 : subd8_0 [-1, 3, 4] = true := by decide +kernel
theorem subd8_0_429 : subd8_0 [-1, 3, 5] = true := by decide +kernel
theorem subd8_0_430 : subd8_0 [-1, 3, 6] = true := by decide +kernel
theorem subd8_0_431 : subd8_0 [-1, 3, 7] = true := by decide +kernel
theorem subd8_0_432 : subd8_0 [-1, 3, 8] = true := by decide +kernel
theorem subd8_0_433 : subd8_0 [-1, 4, -6] = true := by decide +kernel
theorem subd8_0_434 : subd8_0 [-1, 4, -5] = true := by decide +kernel
theorem subd8_0_435 : subd8_0 [-1, 4, -4] = true := by decide +kernel
theorem subd8_0_436 : subd8_0 [-1, 4, -3] = true := by decide +kernel
theorem subd8_0_437 : subd8_0 [-1, 4, -2] = true := by decide +kernel
theorem subd8_0_438 : subd8_0 [-1, 4, -1] = true := by decide +kernel
theorem subd8_0_439 : subd8_0 [-1, 4, 0] = true := by decide +kernel
theorem subd8_0_440 : subd8_0 [-1, 4, 1] = true := by decide +kernel
theorem subd8_0_441 : subd8_0 [-1, 4, 2] = true := by decide +kernel
theorem subd8_0_442 : subd8_0 [-1, 4, 3] = true := by decide +kernel
theorem subd8_0_443 : subd8_0 [-1, 4, 4] = true := by decide +kernel
theorem subd8_0_444 : subd8_0 [-1, 4, 5] = true := by decide +kernel
theorem subd8_0_445 : subd8_0 [-1, 4, 6] = true := by decide +kernel
theorem subd8_0_446 : subd8_0 [-1, 4, 7] = true := by decide +kernel
theorem subd8_0_447 : subd8_0 [-1, 5] = true := by decide +kernel
theorem sbd8_0_13 : ∀ q ∈ blkd8_0_13, subd8_0 q = true := by
  unfold blkd8_0_13
  exact List.forall_mem_cons.2 ⟨subd8_0_416, List.forall_mem_cons.2 ⟨subd8_0_417, List.forall_mem_cons.2 ⟨subd8_0_418, List.forall_mem_cons.2 ⟨subd8_0_419, List.forall_mem_cons.2 ⟨subd8_0_420, List.forall_mem_cons.2 ⟨subd8_0_421, List.forall_mem_cons.2 ⟨subd8_0_422, List.forall_mem_cons.2 ⟨subd8_0_423, List.forall_mem_cons.2 ⟨subd8_0_424, List.forall_mem_cons.2 ⟨subd8_0_425, List.forall_mem_cons.2 ⟨subd8_0_426, List.forall_mem_cons.2 ⟨subd8_0_427, List.forall_mem_cons.2 ⟨subd8_0_428, List.forall_mem_cons.2 ⟨subd8_0_429, List.forall_mem_cons.2 ⟨subd8_0_430, List.forall_mem_cons.2 ⟨subd8_0_431, List.forall_mem_cons.2 ⟨subd8_0_432, List.forall_mem_cons.2 ⟨subd8_0_433, List.forall_mem_cons.2 ⟨subd8_0_434, List.forall_mem_cons.2 ⟨subd8_0_435, List.forall_mem_cons.2 ⟨subd8_0_436, List.forall_mem_cons.2 ⟨subd8_0_437, List.forall_mem_cons.2 ⟨subd8_0_438, List.forall_mem_cons.2 ⟨subd8_0_439, List.forall_mem_cons.2 ⟨subd8_0_440, List.forall_mem_cons.2 ⟨subd8_0_441, List.forall_mem_cons.2 ⟨subd8_0_442, List.forall_mem_cons.2 ⟨subd8_0_443, List.forall_mem_cons.2 ⟨subd8_0_444, List.forall_mem_cons.2 ⟨subd8_0_445, List.forall_mem_cons.2 ⟨subd8_0_446, List.forall_mem_cons.2 ⟨subd8_0_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_448 : subd8_0 [-1, 6] = true := by decide +kernel
theorem subd8_0_449 : subd8_0 [0, -7] = true := by decide +kernel
theorem subd8_0_450 : subd8_0 [0, -6] = true := by decide +kernel
theorem subd8_0_451 : subd8_0 [0, -5] = true := by decide +kernel
theorem subd8_0_452 : subd8_0 [0, -4, -8] = true := by decide +kernel
theorem subd8_0_453 : subd8_0 [0, -4, -7] = true := by decide +kernel
theorem subd8_0_454 : subd8_0 [0, -4, -6] = true := by decide +kernel
theorem subd8_0_455 : subd8_0 [0, -4, -5] = true := by decide +kernel
theorem subd8_0_456 : subd8_0 [0, -4, -4] = true := by decide +kernel
theorem subd8_0_457 : subd8_0 [0, -4, -3] = true := by decide +kernel
theorem subd8_0_458 : subd8_0 [0, -4, -2] = true := by decide +kernel
theorem subd8_0_459 : subd8_0 [0, -4, -1] = true := by decide +kernel
theorem subd8_0_460 : subd8_0 [0, -4, 0] = true := by decide +kernel
theorem subd8_0_461 : subd8_0 [0, -4, 1] = true := by decide +kernel
theorem subd8_0_462 : subd8_0 [0, -4, 2] = true := by decide +kernel
theorem subd8_0_463 : subd8_0 [0, -4, 3] = true := by decide +kernel
theorem subd8_0_464 : subd8_0 [0, -4, 4] = true := by decide +kernel
theorem subd8_0_465 : subd8_0 [0, -4, 5] = true := by decide +kernel
theorem subd8_0_466 : subd8_0 [0, -4, 6] = true := by decide +kernel
theorem subd8_0_467 : subd8_0 [0, -3, -9] = true := by decide +kernel
theorem subd8_0_468 : subd8_0 [0, -3, -8] = true := by decide +kernel
theorem subd8_0_469 : subd8_0 [0, -3, -7] = true := by decide +kernel
theorem subd8_0_470 : subd8_0 [0, -3, -6] = true := by decide +kernel
theorem subd8_0_471 : subd8_0 [0, -3, -5] = true := by decide +kernel
theorem subd8_0_472 : subd8_0 [0, -3, -4] = true := by decide +kernel
theorem subd8_0_473 : subd8_0 [0, -3, -3] = true := by decide +kernel
theorem subd8_0_474 : subd8_0 [0, -3, -2] = true := by decide +kernel
theorem subd8_0_475 : subd8_0 [0, -3, -1] = true := by decide +kernel
theorem subd8_0_476 : subd8_0 [0, -3, 0] = true := by decide +kernel
theorem subd8_0_477 : subd8_0 [0, -3, 1] = true := by decide +kernel
theorem subd8_0_478 : subd8_0 [0, -3, 2] = true := by decide +kernel
theorem subd8_0_479 : subd8_0 [0, -3, 3] = true := by decide +kernel
theorem sbd8_0_14 : ∀ q ∈ blkd8_0_14, subd8_0 q = true := by
  unfold blkd8_0_14
  exact List.forall_mem_cons.2 ⟨subd8_0_448, List.forall_mem_cons.2 ⟨subd8_0_449, List.forall_mem_cons.2 ⟨subd8_0_450, List.forall_mem_cons.2 ⟨subd8_0_451, List.forall_mem_cons.2 ⟨subd8_0_452, List.forall_mem_cons.2 ⟨subd8_0_453, List.forall_mem_cons.2 ⟨subd8_0_454, List.forall_mem_cons.2 ⟨subd8_0_455, List.forall_mem_cons.2 ⟨subd8_0_456, List.forall_mem_cons.2 ⟨subd8_0_457, List.forall_mem_cons.2 ⟨subd8_0_458, List.forall_mem_cons.2 ⟨subd8_0_459, List.forall_mem_cons.2 ⟨subd8_0_460, List.forall_mem_cons.2 ⟨subd8_0_461, List.forall_mem_cons.2 ⟨subd8_0_462, List.forall_mem_cons.2 ⟨subd8_0_463, List.forall_mem_cons.2 ⟨subd8_0_464, List.forall_mem_cons.2 ⟨subd8_0_465, List.forall_mem_cons.2 ⟨subd8_0_466, List.forall_mem_cons.2 ⟨subd8_0_467, List.forall_mem_cons.2 ⟨subd8_0_468, List.forall_mem_cons.2 ⟨subd8_0_469, List.forall_mem_cons.2 ⟨subd8_0_470, List.forall_mem_cons.2 ⟨subd8_0_471, List.forall_mem_cons.2 ⟨subd8_0_472, List.forall_mem_cons.2 ⟨subd8_0_473, List.forall_mem_cons.2 ⟨subd8_0_474, List.forall_mem_cons.2 ⟨subd8_0_475, List.forall_mem_cons.2 ⟨subd8_0_476, List.forall_mem_cons.2 ⟨subd8_0_477, List.forall_mem_cons.2 ⟨subd8_0_478, List.forall_mem_cons.2 ⟨subd8_0_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_480 : subd8_0 [0, -3, 4] = true := by decide +kernel
theorem subd8_0_481 : subd8_0 [0, -3, 5] = true := by decide +kernel
theorem subd8_0_482 : subd8_0 [0, -3, 6] = true := by decide +kernel
theorem subd8_0_483 : subd8_0 [0, -3, 7] = true := by decide +kernel
theorem subd8_0_484 : subd8_0 [0, -2, -9] = true := by decide +kernel
theorem subd8_0_485 : subd8_0 [0, -2, -8] = true := by decide +kernel
theorem subd8_0_486 : subd8_0 [0, -2, -7] = true := by decide +kernel
theorem subd8_0_487 : subd8_0 [0, -2, -6] = true := by decide +kernel
theorem subd8_0_488 : subd8_0 [0, -2, -5] = true := by decide +kernel
theorem subd8_0_489 : subd8_0 [0, -2, -4] = true := by decide +kernel
theorem subd8_0_490 : subd8_0 [0, -2, -3] = true := by decide +kernel
theorem subd8_0_491 : subd8_0 [0, -2, -2] = true := by decide +kernel
theorem subd8_0_492 : subd8_0 [0, -2, -1] = true := by decide +kernel
theorem subd8_0_493 : subd8_0 [0, -2, 0] = true := by decide +kernel
theorem subd8_0_494 : subd8_0 [0, -2, 1] = true := by decide +kernel
theorem subd8_0_495 : subd8_0 [0, -2, 2] = true := by decide +kernel
theorem subd8_0_496 : subd8_0 [0, -2, 3] = true := by decide +kernel
theorem subd8_0_497 : subd8_0 [0, -2, 4] = true := by decide +kernel
theorem subd8_0_498 : subd8_0 [0, -2, 5] = true := by decide +kernel
theorem subd8_0_499 : subd8_0 [0, -2, 6] = true := by decide +kernel
theorem subd8_0_500 : subd8_0 [0, -2, 7] = true := by decide +kernel
theorem subd8_0_501 : subd8_0 [0, -2, 8] = true := by decide +kernel
theorem subd8_0_502 : subd8_0 [0, -1, -9] = true := by decide +kernel
theorem subd8_0_503 : subd8_0 [0, -1, -8] = true := by decide +kernel
theorem subd8_0_504 : subd8_0 [0, -1, -7] = true := by decide +kernel
theorem subd8_0_505 : subd8_0 [0, -1, -6] = true := by decide +kernel
theorem subd8_0_506 : subd8_0 [0, -1, -5] = true := by decide +kernel
theorem subd8_0_507 : subd8_0 [0, -1, -4] = true := by decide +kernel
theorem subd8_0_508 : subd8_0 [0, -1, -3] = true := by decide +kernel
theorem subd8_0_509 : subd8_0 [0, -1, -2] = true := by decide +kernel
theorem subd8_0_510 : subd8_0 [0, -1, -1] = true := by decide +kernel
theorem subd8_0_511 : subd8_0 [0, -1, 0] = true := by decide +kernel
theorem sbd8_0_15 : ∀ q ∈ blkd8_0_15, subd8_0 q = true := by
  unfold blkd8_0_15
  exact List.forall_mem_cons.2 ⟨subd8_0_480, List.forall_mem_cons.2 ⟨subd8_0_481, List.forall_mem_cons.2 ⟨subd8_0_482, List.forall_mem_cons.2 ⟨subd8_0_483, List.forall_mem_cons.2 ⟨subd8_0_484, List.forall_mem_cons.2 ⟨subd8_0_485, List.forall_mem_cons.2 ⟨subd8_0_486, List.forall_mem_cons.2 ⟨subd8_0_487, List.forall_mem_cons.2 ⟨subd8_0_488, List.forall_mem_cons.2 ⟨subd8_0_489, List.forall_mem_cons.2 ⟨subd8_0_490, List.forall_mem_cons.2 ⟨subd8_0_491, List.forall_mem_cons.2 ⟨subd8_0_492, List.forall_mem_cons.2 ⟨subd8_0_493, List.forall_mem_cons.2 ⟨subd8_0_494, List.forall_mem_cons.2 ⟨subd8_0_495, List.forall_mem_cons.2 ⟨subd8_0_496, List.forall_mem_cons.2 ⟨subd8_0_497, List.forall_mem_cons.2 ⟨subd8_0_498, List.forall_mem_cons.2 ⟨subd8_0_499, List.forall_mem_cons.2 ⟨subd8_0_500, List.forall_mem_cons.2 ⟨subd8_0_501, List.forall_mem_cons.2 ⟨subd8_0_502, List.forall_mem_cons.2 ⟨subd8_0_503, List.forall_mem_cons.2 ⟨subd8_0_504, List.forall_mem_cons.2 ⟨subd8_0_505, List.forall_mem_cons.2 ⟨subd8_0_506, List.forall_mem_cons.2 ⟨subd8_0_507, List.forall_mem_cons.2 ⟨subd8_0_508, List.forall_mem_cons.2 ⟨subd8_0_509, List.forall_mem_cons.2 ⟨subd8_0_510, List.forall_mem_cons.2 ⟨subd8_0_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_512 : subd8_0 [0, -1, 1] = true := by decide +kernel
theorem subd8_0_513 : subd8_0 [0, -1, 2] = true := by decide +kernel
theorem subd8_0_514 : subd8_0 [0, -1, 3] = true := by decide +kernel
theorem subd8_0_515 : subd8_0 [0, -1, 4] = true := by decide +kernel
theorem subd8_0_516 : subd8_0 [0, -1, 5] = true := by decide +kernel
theorem subd8_0_517 : subd8_0 [0, -1, 6] = true := by decide +kernel
theorem subd8_0_518 : subd8_0 [0, -1, 7] = true := by decide +kernel
theorem subd8_0_519 : subd8_0 [0, -1, 8] = true := by decide +kernel
theorem subd8_0_520 : subd8_0 [0, 0, -9] = true := by decide +kernel
theorem subd8_0_521 : subd8_0 [0, 0, -8] = true := by decide +kernel
theorem subd8_0_522 : subd8_0 [0, 0, -7] = true := by decide +kernel
theorem subd8_0_523 : subd8_0 [0, 0, -6] = true := by decide +kernel
theorem subd8_0_524 : subd8_0 [0, 0, -5] = true := by decide +kernel
theorem subd8_0_525 : subd8_0 [0, 0, -4] = true := by decide +kernel
theorem subd8_0_526 : subd8_0 [0, 0, -3] = true := by decide +kernel
theorem subd8_0_527 : subd8_0 [0, 0, -2] = true := by decide +kernel
theorem subd8_0_528 : subd8_0 [0, 0, -1] = true := by decide +kernel
theorem subd8_0_529 : subd8_0 [0, 0, 0] = true := by decide +kernel
theorem subd8_0_530 : subd8_0 [0, 0, 1] = true := by decide +kernel
theorem subd8_0_531 : subd8_0 [0, 0, 2] = true := by decide +kernel
theorem subd8_0_532 : subd8_0 [0, 0, 3] = true := by decide +kernel
theorem subd8_0_533 : subd8_0 [0, 0, 4] = true := by decide +kernel
theorem subd8_0_534 : subd8_0 [0, 0, 5] = true := by decide +kernel
theorem subd8_0_535 : subd8_0 [0, 0, 6] = true := by decide +kernel
theorem subd8_0_536 : subd8_0 [0, 0, 7] = true := by decide +kernel
theorem subd8_0_537 : subd8_0 [0, 0, 8] = true := by decide +kernel
theorem subd8_0_538 : subd8_0 [0, 1, -9] = true := by decide +kernel
theorem subd8_0_539 : subd8_0 [0, 1, -8] = true := by decide +kernel
theorem subd8_0_540 : subd8_0 [0, 1, -7] = true := by decide +kernel
theorem subd8_0_541 : subd8_0 [0, 1, -6] = true := by decide +kernel
theorem subd8_0_542 : subd8_0 [0, 1, -5] = true := by decide +kernel
theorem subd8_0_543 : subd8_0 [0, 1, -4] = true := by decide +kernel
theorem sbd8_0_16 : ∀ q ∈ blkd8_0_16, subd8_0 q = true := by
  unfold blkd8_0_16
  exact List.forall_mem_cons.2 ⟨subd8_0_512, List.forall_mem_cons.2 ⟨subd8_0_513, List.forall_mem_cons.2 ⟨subd8_0_514, List.forall_mem_cons.2 ⟨subd8_0_515, List.forall_mem_cons.2 ⟨subd8_0_516, List.forall_mem_cons.2 ⟨subd8_0_517, List.forall_mem_cons.2 ⟨subd8_0_518, List.forall_mem_cons.2 ⟨subd8_0_519, List.forall_mem_cons.2 ⟨subd8_0_520, List.forall_mem_cons.2 ⟨subd8_0_521, List.forall_mem_cons.2 ⟨subd8_0_522, List.forall_mem_cons.2 ⟨subd8_0_523, List.forall_mem_cons.2 ⟨subd8_0_524, List.forall_mem_cons.2 ⟨subd8_0_525, List.forall_mem_cons.2 ⟨subd8_0_526, List.forall_mem_cons.2 ⟨subd8_0_527, List.forall_mem_cons.2 ⟨subd8_0_528, List.forall_mem_cons.2 ⟨subd8_0_529, List.forall_mem_cons.2 ⟨subd8_0_530, List.forall_mem_cons.2 ⟨subd8_0_531, List.forall_mem_cons.2 ⟨subd8_0_532, List.forall_mem_cons.2 ⟨subd8_0_533, List.forall_mem_cons.2 ⟨subd8_0_534, List.forall_mem_cons.2 ⟨subd8_0_535, List.forall_mem_cons.2 ⟨subd8_0_536, List.forall_mem_cons.2 ⟨subd8_0_537, List.forall_mem_cons.2 ⟨subd8_0_538, List.forall_mem_cons.2 ⟨subd8_0_539, List.forall_mem_cons.2 ⟨subd8_0_540, List.forall_mem_cons.2 ⟨subd8_0_541, List.forall_mem_cons.2 ⟨subd8_0_542, List.forall_mem_cons.2 ⟨subd8_0_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_544 : subd8_0 [0, 1, -3] = true := by decide +kernel
theorem subd8_0_545 : subd8_0 [0, 1, -2] = true := by decide +kernel
theorem subd8_0_546 : subd8_0 [0, 1, -1] = true := by decide +kernel
theorem subd8_0_547 : subd8_0 [0, 1, 0] = true := by decide +kernel
theorem subd8_0_548 : subd8_0 [0, 1, 1] = true := by decide +kernel
theorem subd8_0_549 : subd8_0 [0, 1, 2] = true := by decide +kernel
theorem subd8_0_550 : subd8_0 [0, 1, 3] = true := by decide +kernel
theorem subd8_0_551 : subd8_0 [0, 1, 4] = true := by decide +kernel
theorem subd8_0_552 : subd8_0 [0, 1, 5] = true := by decide +kernel
theorem subd8_0_553 : subd8_0 [0, 1, 6] = true := by decide +kernel
theorem subd8_0_554 : subd8_0 [0, 1, 7] = true := by decide +kernel
theorem subd8_0_555 : subd8_0 [0, 1, 8] = true := by decide +kernel
theorem subd8_0_556 : subd8_0 [0, 2, -9] = true := by decide +kernel
theorem subd8_0_557 : subd8_0 [0, 2, -8] = true := by decide +kernel
theorem subd8_0_558 : subd8_0 [0, 2, -7] = true := by decide +kernel
theorem subd8_0_559 : subd8_0 [0, 2, -6] = true := by decide +kernel
theorem subd8_0_560 : subd8_0 [0, 2, -5] = true := by decide +kernel
theorem subd8_0_561 : subd8_0 [0, 2, -4] = true := by decide +kernel
theorem subd8_0_562 : subd8_0 [0, 2, -3] = true := by decide +kernel
theorem subd8_0_563 : subd8_0 [0, 2, -2] = true := by decide +kernel
theorem subd8_0_564 : subd8_0 [0, 2, -1] = true := by decide +kernel
theorem subd8_0_565 : subd8_0 [0, 2, 0] = true := by decide +kernel
theorem subd8_0_566 : subd8_0 [0, 2, 1] = true := by decide +kernel
theorem subd8_0_567 : subd8_0 [0, 2, 2] = true := by decide +kernel
theorem subd8_0_568 : subd8_0 [0, 2, 3] = true := by decide +kernel
theorem subd8_0_569 : subd8_0 [0, 2, 4] = true := by decide +kernel
theorem subd8_0_570 : subd8_0 [0, 2, 5] = true := by decide +kernel
theorem subd8_0_571 : subd8_0 [0, 2, 6] = true := by decide +kernel
theorem subd8_0_572 : subd8_0 [0, 2, 7] = true := by decide +kernel
theorem subd8_0_573 : subd8_0 [0, 2, 8] = true := by decide +kernel
theorem subd8_0_574 : subd8_0 [0, 3, -8] = true := by decide +kernel
theorem subd8_0_575 : subd8_0 [0, 3, -7] = true := by decide +kernel
theorem sbd8_0_17 : ∀ q ∈ blkd8_0_17, subd8_0 q = true := by
  unfold blkd8_0_17
  exact List.forall_mem_cons.2 ⟨subd8_0_544, List.forall_mem_cons.2 ⟨subd8_0_545, List.forall_mem_cons.2 ⟨subd8_0_546, List.forall_mem_cons.2 ⟨subd8_0_547, List.forall_mem_cons.2 ⟨subd8_0_548, List.forall_mem_cons.2 ⟨subd8_0_549, List.forall_mem_cons.2 ⟨subd8_0_550, List.forall_mem_cons.2 ⟨subd8_0_551, List.forall_mem_cons.2 ⟨subd8_0_552, List.forall_mem_cons.2 ⟨subd8_0_553, List.forall_mem_cons.2 ⟨subd8_0_554, List.forall_mem_cons.2 ⟨subd8_0_555, List.forall_mem_cons.2 ⟨subd8_0_556, List.forall_mem_cons.2 ⟨subd8_0_557, List.forall_mem_cons.2 ⟨subd8_0_558, List.forall_mem_cons.2 ⟨subd8_0_559, List.forall_mem_cons.2 ⟨subd8_0_560, List.forall_mem_cons.2 ⟨subd8_0_561, List.forall_mem_cons.2 ⟨subd8_0_562, List.forall_mem_cons.2 ⟨subd8_0_563, List.forall_mem_cons.2 ⟨subd8_0_564, List.forall_mem_cons.2 ⟨subd8_0_565, List.forall_mem_cons.2 ⟨subd8_0_566, List.forall_mem_cons.2 ⟨subd8_0_567, List.forall_mem_cons.2 ⟨subd8_0_568, List.forall_mem_cons.2 ⟨subd8_0_569, List.forall_mem_cons.2 ⟨subd8_0_570, List.forall_mem_cons.2 ⟨subd8_0_571, List.forall_mem_cons.2 ⟨subd8_0_572, List.forall_mem_cons.2 ⟨subd8_0_573, List.forall_mem_cons.2 ⟨subd8_0_574, List.forall_mem_cons.2 ⟨subd8_0_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_576 : subd8_0 [0, 3, -6] = true := by decide +kernel
theorem subd8_0_577 : subd8_0 [0, 3, -5] = true := by decide +kernel
theorem subd8_0_578 : subd8_0 [0, 3, -4] = true := by decide +kernel
theorem subd8_0_579 : subd8_0 [0, 3, -3] = true := by decide +kernel
theorem subd8_0_580 : subd8_0 [0, 3, -2] = true := by decide +kernel
theorem subd8_0_581 : subd8_0 [0, 3, -1] = true := by decide +kernel
theorem subd8_0_582 : subd8_0 [0, 3, 0] = true := by decide +kernel
theorem subd8_0_583 : subd8_0 [0, 3, 1] = true := by decide +kernel
theorem subd8_0_584 : subd8_0 [0, 3, 2] = true := by decide +kernel
theorem subd8_0_585 : subd8_0 [0, 3, 3] = true := by decide +kernel
theorem subd8_0_586 : subd8_0 [0, 3, 4] = true := by decide +kernel
theorem subd8_0_587 : subd8_0 [0, 3, 5] = true := by decide +kernel
theorem subd8_0_588 : subd8_0 [0, 3, 6] = true := by decide +kernel
theorem subd8_0_589 : subd8_0 [0, 3, 7] = true := by decide +kernel
theorem subd8_0_590 : subd8_0 [0, 3, 8] = true := by decide +kernel
theorem subd8_0_591 : subd8_0 [0, 4, -7] = true := by decide +kernel
theorem subd8_0_592 : subd8_0 [0, 4, -6] = true := by decide +kernel
theorem subd8_0_593 : subd8_0 [0, 4, -5] = true := by decide +kernel
theorem subd8_0_594 : subd8_0 [0, 4, -4] = true := by decide +kernel
theorem subd8_0_595 : subd8_0 [0, 4, -3] = true := by decide +kernel
theorem subd8_0_596 : subd8_0 [0, 4, -2] = true := by decide +kernel
theorem subd8_0_597 : subd8_0 [0, 4, -1] = true := by decide +kernel
theorem subd8_0_598 : subd8_0 [0, 4, 0] = true := by decide +kernel
theorem subd8_0_599 : subd8_0 [0, 4, 1] = true := by decide +kernel
theorem subd8_0_600 : subd8_0 [0, 4, 2] = true := by decide +kernel
theorem subd8_0_601 : subd8_0 [0, 4, 3] = true := by decide +kernel
theorem subd8_0_602 : subd8_0 [0, 4, 4] = true := by decide +kernel
theorem subd8_0_603 : subd8_0 [0, 4, 5] = true := by decide +kernel
theorem subd8_0_604 : subd8_0 [0, 4, 6] = true := by decide +kernel
theorem subd8_0_605 : subd8_0 [0, 4, 7] = true := by decide +kernel
theorem subd8_0_606 : subd8_0 [0, 5] = true := by decide +kernel
theorem subd8_0_607 : subd8_0 [0, 6] = true := by decide +kernel
theorem sbd8_0_18 : ∀ q ∈ blkd8_0_18, subd8_0 q = true := by
  unfold blkd8_0_18
  exact List.forall_mem_cons.2 ⟨subd8_0_576, List.forall_mem_cons.2 ⟨subd8_0_577, List.forall_mem_cons.2 ⟨subd8_0_578, List.forall_mem_cons.2 ⟨subd8_0_579, List.forall_mem_cons.2 ⟨subd8_0_580, List.forall_mem_cons.2 ⟨subd8_0_581, List.forall_mem_cons.2 ⟨subd8_0_582, List.forall_mem_cons.2 ⟨subd8_0_583, List.forall_mem_cons.2 ⟨subd8_0_584, List.forall_mem_cons.2 ⟨subd8_0_585, List.forall_mem_cons.2 ⟨subd8_0_586, List.forall_mem_cons.2 ⟨subd8_0_587, List.forall_mem_cons.2 ⟨subd8_0_588, List.forall_mem_cons.2 ⟨subd8_0_589, List.forall_mem_cons.2 ⟨subd8_0_590, List.forall_mem_cons.2 ⟨subd8_0_591, List.forall_mem_cons.2 ⟨subd8_0_592, List.forall_mem_cons.2 ⟨subd8_0_593, List.forall_mem_cons.2 ⟨subd8_0_594, List.forall_mem_cons.2 ⟨subd8_0_595, List.forall_mem_cons.2 ⟨subd8_0_596, List.forall_mem_cons.2 ⟨subd8_0_597, List.forall_mem_cons.2 ⟨subd8_0_598, List.forall_mem_cons.2 ⟨subd8_0_599, List.forall_mem_cons.2 ⟨subd8_0_600, List.forall_mem_cons.2 ⟨subd8_0_601, List.forall_mem_cons.2 ⟨subd8_0_602, List.forall_mem_cons.2 ⟨subd8_0_603, List.forall_mem_cons.2 ⟨subd8_0_604, List.forall_mem_cons.2 ⟨subd8_0_605, List.forall_mem_cons.2 ⟨subd8_0_606, List.forall_mem_cons.2 ⟨subd8_0_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_608 : subd8_0 [1, -7] = true := by decide +kernel
theorem subd8_0_609 : subd8_0 [1, -6] = true := by decide +kernel
theorem subd8_0_610 : subd8_0 [1, -5] = true := by decide +kernel
theorem subd8_0_611 : subd8_0 [1, -4, -8] = true := by decide +kernel
theorem subd8_0_612 : subd8_0 [1, -4, -7] = true := by decide +kernel
theorem subd8_0_613 : subd8_0 [1, -4, -6] = true := by decide +kernel
theorem subd8_0_614 : subd8_0 [1, -4, -5] = true := by decide +kernel
theorem subd8_0_615 : subd8_0 [1, -4, -4] = true := by decide +kernel
theorem subd8_0_616 : subd8_0 [1, -4, -3] = true := by decide +kernel
theorem subd8_0_617 : subd8_0 [1, -4, -2] = true := by decide +kernel
theorem subd8_0_618 : subd8_0 [1, -4, -1] = true := by decide +kernel
theorem subd8_0_619 : subd8_0 [1, -4, 0] = true := by decide +kernel
theorem subd8_0_620 : subd8_0 [1, -4, 1] = true := by decide +kernel
theorem subd8_0_621 : subd8_0 [1, -4, 2] = true := by decide +kernel
theorem subd8_0_622 : subd8_0 [1, -4, 3] = true := by decide +kernel
theorem subd8_0_623 : subd8_0 [1, -4, 4] = true := by decide +kernel
theorem subd8_0_624 : subd8_0 [1, -4, 5] = true := by decide +kernel
theorem subd8_0_625 : subd8_0 [1, -3, -9] = true := by decide +kernel
theorem subd8_0_626 : subd8_0 [1, -3, -8] = true := by decide +kernel
theorem subd8_0_627 : subd8_0 [1, -3, -7] = true := by decide +kernel
theorem subd8_0_628 : subd8_0 [1, -3, -6] = true := by decide +kernel
theorem subd8_0_629 : subd8_0 [1, -3, -5] = true := by decide +kernel
theorem subd8_0_630 : subd8_0 [1, -3, -4] = true := by decide +kernel
theorem subd8_0_631 : subd8_0 [1, -3, -3] = true := by decide +kernel
theorem subd8_0_632 : subd8_0 [1, -3, -2] = true := by decide +kernel
theorem subd8_0_633 : subd8_0 [1, -3, -1] = true := by decide +kernel
theorem subd8_0_634 : subd8_0 [1, -3, 0] = true := by decide +kernel
theorem subd8_0_635 : subd8_0 [1, -3, 1] = true := by decide +kernel
theorem subd8_0_636 : subd8_0 [1, -3, 2] = true := by decide +kernel
theorem subd8_0_637 : subd8_0 [1, -3, 3] = true := by decide +kernel
theorem subd8_0_638 : subd8_0 [1, -3, 4] = true := by decide +kernel
theorem subd8_0_639 : subd8_0 [1, -3, 5] = true := by decide +kernel
theorem sbd8_0_19 : ∀ q ∈ blkd8_0_19, subd8_0 q = true := by
  unfold blkd8_0_19
  exact List.forall_mem_cons.2 ⟨subd8_0_608, List.forall_mem_cons.2 ⟨subd8_0_609, List.forall_mem_cons.2 ⟨subd8_0_610, List.forall_mem_cons.2 ⟨subd8_0_611, List.forall_mem_cons.2 ⟨subd8_0_612, List.forall_mem_cons.2 ⟨subd8_0_613, List.forall_mem_cons.2 ⟨subd8_0_614, List.forall_mem_cons.2 ⟨subd8_0_615, List.forall_mem_cons.2 ⟨subd8_0_616, List.forall_mem_cons.2 ⟨subd8_0_617, List.forall_mem_cons.2 ⟨subd8_0_618, List.forall_mem_cons.2 ⟨subd8_0_619, List.forall_mem_cons.2 ⟨subd8_0_620, List.forall_mem_cons.2 ⟨subd8_0_621, List.forall_mem_cons.2 ⟨subd8_0_622, List.forall_mem_cons.2 ⟨subd8_0_623, List.forall_mem_cons.2 ⟨subd8_0_624, List.forall_mem_cons.2 ⟨subd8_0_625, List.forall_mem_cons.2 ⟨subd8_0_626, List.forall_mem_cons.2 ⟨subd8_0_627, List.forall_mem_cons.2 ⟨subd8_0_628, List.forall_mem_cons.2 ⟨subd8_0_629, List.forall_mem_cons.2 ⟨subd8_0_630, List.forall_mem_cons.2 ⟨subd8_0_631, List.forall_mem_cons.2 ⟨subd8_0_632, List.forall_mem_cons.2 ⟨subd8_0_633, List.forall_mem_cons.2 ⟨subd8_0_634, List.forall_mem_cons.2 ⟨subd8_0_635, List.forall_mem_cons.2 ⟨subd8_0_636, List.forall_mem_cons.2 ⟨subd8_0_637, List.forall_mem_cons.2 ⟨subd8_0_638, List.forall_mem_cons.2 ⟨subd8_0_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_640 : subd8_0 [1, -3, 6] = true := by decide +kernel
theorem subd8_0_641 : subd8_0 [1, -2, -9] = true := by decide +kernel
theorem subd8_0_642 : subd8_0 [1, -2, -8] = true := by decide +kernel
theorem subd8_0_643 : subd8_0 [1, -2, -7] = true := by decide +kernel
theorem subd8_0_644 : subd8_0 [1, -2, -6] = true := by decide +kernel
theorem subd8_0_645 : subd8_0 [1, -2, -5] = true := by decide +kernel
theorem subd8_0_646 : subd8_0 [1, -2, -4] = true := by decide +kernel
theorem subd8_0_647 : subd8_0 [1, -2, -3] = true := by decide +kernel
theorem subd8_0_648 : subd8_0 [1, -2, -2] = true := by decide +kernel
theorem subd8_0_649 : subd8_0 [1, -2, -1] = true := by decide +kernel
theorem subd8_0_650 : subd8_0 [1, -2, 0] = true := by decide +kernel
theorem subd8_0_651 : subd8_0 [1, -2, 1] = true := by decide +kernel
theorem subd8_0_652 : subd8_0 [1, -2, 2] = true := by decide +kernel
theorem subd8_0_653 : subd8_0 [1, -2, 3] = true := by decide +kernel
theorem subd8_0_654 : subd8_0 [1, -2, 4] = true := by decide +kernel
theorem subd8_0_655 : subd8_0 [1, -2, 5] = true := by decide +kernel
theorem subd8_0_656 : subd8_0 [1, -2, 6] = true := by decide +kernel
theorem subd8_0_657 : subd8_0 [1, -2, 7] = true := by decide +kernel
theorem subd8_0_658 : subd8_0 [1, -1, -9] = true := by decide +kernel
theorem subd8_0_659 : subd8_0 [1, -1, -8] = true := by decide +kernel
theorem subd8_0_660 : subd8_0 [1, -1, -7] = true := by decide +kernel
theorem subd8_0_661 : subd8_0 [1, -1, -6] = true := by decide +kernel
theorem subd8_0_662 : subd8_0 [1, -1, -5] = true := by decide +kernel
theorem subd8_0_663 : subd8_0 [1, -1, -4] = true := by decide +kernel
theorem subd8_0_664 : subd8_0 [1, -1, -3] = true := by decide +kernel
theorem subd8_0_665 : subd8_0 [1, -1, -2] = true := by decide +kernel
theorem subd8_0_666 : subd8_0 [1, -1, -1] = true := by decide +kernel
theorem subd8_0_667 : subd8_0 [1, -1, 0] = true := by decide +kernel
theorem subd8_0_668 : subd8_0 [1, -1, 1] = true := by decide +kernel
theorem subd8_0_669 : subd8_0 [1, -1, 2] = true := by decide +kernel
theorem subd8_0_670 : subd8_0 [1, -1, 3] = true := by decide +kernel
theorem subd8_0_671 : subd8_0 [1, -1, 4] = true := by decide +kernel
theorem sbd8_0_20 : ∀ q ∈ blkd8_0_20, subd8_0 q = true := by
  unfold blkd8_0_20
  exact List.forall_mem_cons.2 ⟨subd8_0_640, List.forall_mem_cons.2 ⟨subd8_0_641, List.forall_mem_cons.2 ⟨subd8_0_642, List.forall_mem_cons.2 ⟨subd8_0_643, List.forall_mem_cons.2 ⟨subd8_0_644, List.forall_mem_cons.2 ⟨subd8_0_645, List.forall_mem_cons.2 ⟨subd8_0_646, List.forall_mem_cons.2 ⟨subd8_0_647, List.forall_mem_cons.2 ⟨subd8_0_648, List.forall_mem_cons.2 ⟨subd8_0_649, List.forall_mem_cons.2 ⟨subd8_0_650, List.forall_mem_cons.2 ⟨subd8_0_651, List.forall_mem_cons.2 ⟨subd8_0_652, List.forall_mem_cons.2 ⟨subd8_0_653, List.forall_mem_cons.2 ⟨subd8_0_654, List.forall_mem_cons.2 ⟨subd8_0_655, List.forall_mem_cons.2 ⟨subd8_0_656, List.forall_mem_cons.2 ⟨subd8_0_657, List.forall_mem_cons.2 ⟨subd8_0_658, List.forall_mem_cons.2 ⟨subd8_0_659, List.forall_mem_cons.2 ⟨subd8_0_660, List.forall_mem_cons.2 ⟨subd8_0_661, List.forall_mem_cons.2 ⟨subd8_0_662, List.forall_mem_cons.2 ⟨subd8_0_663, List.forall_mem_cons.2 ⟨subd8_0_664, List.forall_mem_cons.2 ⟨subd8_0_665, List.forall_mem_cons.2 ⟨subd8_0_666, List.forall_mem_cons.2 ⟨subd8_0_667, List.forall_mem_cons.2 ⟨subd8_0_668, List.forall_mem_cons.2 ⟨subd8_0_669, List.forall_mem_cons.2 ⟨subd8_0_670, List.forall_mem_cons.2 ⟨subd8_0_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_672 : subd8_0 [1, -1, 5] = true := by decide +kernel
theorem subd8_0_673 : subd8_0 [1, -1, 6] = true := by decide +kernel
theorem subd8_0_674 : subd8_0 [1, -1, 7] = true := by decide +kernel
theorem subd8_0_675 : subd8_0 [1, -1, 8] = true := by decide +kernel
theorem subd8_0_676 : subd8_0 [1, 0, -9] = true := by decide +kernel
theorem subd8_0_677 : subd8_0 [1, 0, -8] = true := by decide +kernel
theorem subd8_0_678 : subd8_0 [1, 0, -7] = true := by decide +kernel
theorem subd8_0_679 : subd8_0 [1, 0, -6] = true := by decide +kernel
theorem subd8_0_680 : subd8_0 [1, 0, -5] = true := by decide +kernel
theorem subd8_0_681 : subd8_0 [1, 0, -4] = true := by decide +kernel
theorem subd8_0_682 : subd8_0 [1, 0, -3] = true := by decide +kernel
theorem subd8_0_683 : subd8_0 [1, 0, -2] = true := by decide +kernel
theorem subd8_0_684 : subd8_0 [1, 0, -1] = true := by decide +kernel
theorem subd8_0_685 : subd8_0 [1, 0, 0] = true := by decide +kernel
theorem subd8_0_686 : subd8_0 [1, 0, 1] = true := by decide +kernel
theorem subd8_0_687 : subd8_0 [1, 0, 2] = true := by decide +kernel
theorem subd8_0_688 : subd8_0 [1, 0, 3] = true := by decide +kernel
theorem subd8_0_689 : subd8_0 [1, 0, 4] = true := by decide +kernel
theorem subd8_0_690 : subd8_0 [1, 0, 5] = true := by decide +kernel
theorem subd8_0_691 : subd8_0 [1, 0, 6] = true := by decide +kernel
theorem subd8_0_692 : subd8_0 [1, 0, 7] = true := by decide +kernel
theorem subd8_0_693 : subd8_0 [1, 0, 8] = true := by decide +kernel
theorem subd8_0_694 : subd8_0 [1, 1, -9] = true := by decide +kernel
theorem subd8_0_695 : subd8_0 [1, 1, -8] = true := by decide +kernel
theorem subd8_0_696 : subd8_0 [1, 1, -7] = true := by decide +kernel
theorem subd8_0_697 : subd8_0 [1, 1, -6] = true := by decide +kernel
theorem subd8_0_698 : subd8_0 [1, 1, -5] = true := by decide +kernel
theorem subd8_0_699 : subd8_0 [1, 1, -4] = true := by decide +kernel
theorem subd8_0_700 : subd8_0 [1, 1, -3] = true := by decide +kernel
theorem subd8_0_701 : subd8_0 [1, 1, -2] = true := by decide +kernel
theorem subd8_0_702 : subd8_0 [1, 1, -1] = true := by decide +kernel
theorem subd8_0_703 : subd8_0 [1, 1, 0] = true := by decide +kernel
theorem sbd8_0_21 : ∀ q ∈ blkd8_0_21, subd8_0 q = true := by
  unfold blkd8_0_21
  exact List.forall_mem_cons.2 ⟨subd8_0_672, List.forall_mem_cons.2 ⟨subd8_0_673, List.forall_mem_cons.2 ⟨subd8_0_674, List.forall_mem_cons.2 ⟨subd8_0_675, List.forall_mem_cons.2 ⟨subd8_0_676, List.forall_mem_cons.2 ⟨subd8_0_677, List.forall_mem_cons.2 ⟨subd8_0_678, List.forall_mem_cons.2 ⟨subd8_0_679, List.forall_mem_cons.2 ⟨subd8_0_680, List.forall_mem_cons.2 ⟨subd8_0_681, List.forall_mem_cons.2 ⟨subd8_0_682, List.forall_mem_cons.2 ⟨subd8_0_683, List.forall_mem_cons.2 ⟨subd8_0_684, List.forall_mem_cons.2 ⟨subd8_0_685, List.forall_mem_cons.2 ⟨subd8_0_686, List.forall_mem_cons.2 ⟨subd8_0_687, List.forall_mem_cons.2 ⟨subd8_0_688, List.forall_mem_cons.2 ⟨subd8_0_689, List.forall_mem_cons.2 ⟨subd8_0_690, List.forall_mem_cons.2 ⟨subd8_0_691, List.forall_mem_cons.2 ⟨subd8_0_692, List.forall_mem_cons.2 ⟨subd8_0_693, List.forall_mem_cons.2 ⟨subd8_0_694, List.forall_mem_cons.2 ⟨subd8_0_695, List.forall_mem_cons.2 ⟨subd8_0_696, List.forall_mem_cons.2 ⟨subd8_0_697, List.forall_mem_cons.2 ⟨subd8_0_698, List.forall_mem_cons.2 ⟨subd8_0_699, List.forall_mem_cons.2 ⟨subd8_0_700, List.forall_mem_cons.2 ⟨subd8_0_701, List.forall_mem_cons.2 ⟨subd8_0_702, List.forall_mem_cons.2 ⟨subd8_0_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_704 : subd8_0 [1, 1, 1] = true := by decide +kernel
theorem subd8_0_705 : subd8_0 [1, 1, 2] = true := by decide +kernel
theorem subd8_0_706 : subd8_0 [1, 1, 3] = true := by decide +kernel
theorem subd8_0_707 : subd8_0 [1, 1, 4] = true := by decide +kernel
theorem subd8_0_708 : subd8_0 [1, 1, 5] = true := by decide +kernel
theorem subd8_0_709 : subd8_0 [1, 1, 6] = true := by decide +kernel
theorem subd8_0_710 : subd8_0 [1, 1, 7] = true := by decide +kernel
theorem subd8_0_711 : subd8_0 [1, 1, 8] = true := by decide +kernel
theorem subd8_0_712 : subd8_0 [1, 2, -9] = true := by decide +kernel
theorem subd8_0_713 : subd8_0 [1, 2, -8] = true := by decide +kernel
theorem subd8_0_714 : subd8_0 [1, 2, -7] = true := by decide +kernel
theorem subd8_0_715 : subd8_0 [1, 2, -6] = true := by decide +kernel
theorem subd8_0_716 : subd8_0 [1, 2, -5] = true := by decide +kernel
theorem subd8_0_717 : subd8_0 [1, 2, -4] = true := by decide +kernel
theorem subd8_0_718 : subd8_0 [1, 2, -3] = true := by decide +kernel
theorem subd8_0_719 : subd8_0 [1, 2, -2] = true := by decide +kernel
theorem subd8_0_720 : subd8_0 [1, 2, -1] = true := by decide +kernel
theorem subd8_0_721 : subd8_0 [1, 2, 0] = true := by decide +kernel
theorem subd8_0_722 : subd8_0 [1, 2, 1] = true := by decide +kernel
theorem subd8_0_723 : subd8_0 [1, 2, 2] = true := by decide +kernel
theorem subd8_0_724 : subd8_0 [1, 2, 3] = true := by decide +kernel
theorem subd8_0_725 : subd8_0 [1, 2, 4] = true := by decide +kernel
theorem subd8_0_726 : subd8_0 [1, 2, 5] = true := by decide +kernel
theorem subd8_0_727 : subd8_0 [1, 2, 6] = true := by decide +kernel
theorem subd8_0_728 : subd8_0 [1, 2, 7] = true := by decide +kernel
theorem subd8_0_729 : subd8_0 [1, 2, 8] = true := by decide +kernel
theorem subd8_0_730 : subd8_0 [1, 3, -8] = true := by decide +kernel
theorem subd8_0_731 : subd8_0 [1, 3, -7] = true := by decide +kernel
theorem subd8_0_732 : subd8_0 [1, 3, -6] = true := by decide +kernel
theorem subd8_0_733 : subd8_0 [1, 3, -5] = true := by decide +kernel
theorem subd8_0_734 : subd8_0 [1, 3, -4] = true := by decide +kernel
theorem subd8_0_735 : subd8_0 [1, 3, -3] = true := by decide +kernel
theorem sbd8_0_22 : ∀ q ∈ blkd8_0_22, subd8_0 q = true := by
  unfold blkd8_0_22
  exact List.forall_mem_cons.2 ⟨subd8_0_704, List.forall_mem_cons.2 ⟨subd8_0_705, List.forall_mem_cons.2 ⟨subd8_0_706, List.forall_mem_cons.2 ⟨subd8_0_707, List.forall_mem_cons.2 ⟨subd8_0_708, List.forall_mem_cons.2 ⟨subd8_0_709, List.forall_mem_cons.2 ⟨subd8_0_710, List.forall_mem_cons.2 ⟨subd8_0_711, List.forall_mem_cons.2 ⟨subd8_0_712, List.forall_mem_cons.2 ⟨subd8_0_713, List.forall_mem_cons.2 ⟨subd8_0_714, List.forall_mem_cons.2 ⟨subd8_0_715, List.forall_mem_cons.2 ⟨subd8_0_716, List.forall_mem_cons.2 ⟨subd8_0_717, List.forall_mem_cons.2 ⟨subd8_0_718, List.forall_mem_cons.2 ⟨subd8_0_719, List.forall_mem_cons.2 ⟨subd8_0_720, List.forall_mem_cons.2 ⟨subd8_0_721, List.forall_mem_cons.2 ⟨subd8_0_722, List.forall_mem_cons.2 ⟨subd8_0_723, List.forall_mem_cons.2 ⟨subd8_0_724, List.forall_mem_cons.2 ⟨subd8_0_725, List.forall_mem_cons.2 ⟨subd8_0_726, List.forall_mem_cons.2 ⟨subd8_0_727, List.forall_mem_cons.2 ⟨subd8_0_728, List.forall_mem_cons.2 ⟨subd8_0_729, List.forall_mem_cons.2 ⟨subd8_0_730, List.forall_mem_cons.2 ⟨subd8_0_731, List.forall_mem_cons.2 ⟨subd8_0_732, List.forall_mem_cons.2 ⟨subd8_0_733, List.forall_mem_cons.2 ⟨subd8_0_734, List.forall_mem_cons.2 ⟨subd8_0_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_736 : subd8_0 [1, 3, -2] = true := by decide +kernel
theorem subd8_0_737 : subd8_0 [1, 3, -1] = true := by decide +kernel
theorem subd8_0_738 : subd8_0 [1, 3, 0] = true := by decide +kernel
theorem subd8_0_739 : subd8_0 [1, 3, 1] = true := by decide +kernel
theorem subd8_0_740 : subd8_0 [1, 3, 2] = true := by decide +kernel
theorem subd8_0_741 : subd8_0 [1, 3, 3] = true := by decide +kernel
theorem subd8_0_742 : subd8_0 [1, 3, 4] = true := by decide +kernel
theorem subd8_0_743 : subd8_0 [1, 3, 5] = true := by decide +kernel
theorem subd8_0_744 : subd8_0 [1, 3, 6] = true := by decide +kernel
theorem subd8_0_745 : subd8_0 [1, 3, 7] = true := by decide +kernel
theorem subd8_0_746 : subd8_0 [1, 3, 8] = true := by decide +kernel
theorem subd8_0_747 : subd8_0 [1, 4, -7] = true := by decide +kernel
theorem subd8_0_748 : subd8_0 [1, 4, -6] = true := by decide +kernel
theorem subd8_0_749 : subd8_0 [1, 4, -5] = true := by decide +kernel
theorem subd8_0_750 : subd8_0 [1, 4, -4] = true := by decide +kernel
theorem subd8_0_751 : subd8_0 [1, 4, -3] = true := by decide +kernel
theorem subd8_0_752 : subd8_0 [1, 4, -2] = true := by decide +kernel
theorem subd8_0_753 : subd8_0 [1, 4, -1] = true := by decide +kernel
theorem subd8_0_754 : subd8_0 [1, 4, 0] = true := by decide +kernel
theorem subd8_0_755 : subd8_0 [1, 4, 1] = true := by decide +kernel
theorem subd8_0_756 : subd8_0 [1, 4, 2] = true := by decide +kernel
theorem subd8_0_757 : subd8_0 [1, 4, 3] = true := by decide +kernel
theorem subd8_0_758 : subd8_0 [1, 4, 4] = true := by decide +kernel
theorem subd8_0_759 : subd8_0 [1, 4, 5] = true := by decide +kernel
theorem subd8_0_760 : subd8_0 [1, 4, 6] = true := by decide +kernel
theorem subd8_0_761 : subd8_0 [1, 4, 7] = true := by decide +kernel
theorem subd8_0_762 : subd8_0 [1, 5] = true := by decide +kernel
theorem subd8_0_763 : subd8_0 [1, 6] = true := by decide +kernel
theorem subd8_0_764 : subd8_0 [2, -6] = true := by decide +kernel
theorem subd8_0_765 : subd8_0 [2, -5] = true := by decide +kernel
theorem subd8_0_766 : subd8_0 [2, -4] = true := by decide +kernel
theorem subd8_0_767 : subd8_0 [2, -3, -8] = true := by decide +kernel
theorem sbd8_0_23 : ∀ q ∈ blkd8_0_23, subd8_0 q = true := by
  unfold blkd8_0_23
  exact List.forall_mem_cons.2 ⟨subd8_0_736, List.forall_mem_cons.2 ⟨subd8_0_737, List.forall_mem_cons.2 ⟨subd8_0_738, List.forall_mem_cons.2 ⟨subd8_0_739, List.forall_mem_cons.2 ⟨subd8_0_740, List.forall_mem_cons.2 ⟨subd8_0_741, List.forall_mem_cons.2 ⟨subd8_0_742, List.forall_mem_cons.2 ⟨subd8_0_743, List.forall_mem_cons.2 ⟨subd8_0_744, List.forall_mem_cons.2 ⟨subd8_0_745, List.forall_mem_cons.2 ⟨subd8_0_746, List.forall_mem_cons.2 ⟨subd8_0_747, List.forall_mem_cons.2 ⟨subd8_0_748, List.forall_mem_cons.2 ⟨subd8_0_749, List.forall_mem_cons.2 ⟨subd8_0_750, List.forall_mem_cons.2 ⟨subd8_0_751, List.forall_mem_cons.2 ⟨subd8_0_752, List.forall_mem_cons.2 ⟨subd8_0_753, List.forall_mem_cons.2 ⟨subd8_0_754, List.forall_mem_cons.2 ⟨subd8_0_755, List.forall_mem_cons.2 ⟨subd8_0_756, List.forall_mem_cons.2 ⟨subd8_0_757, List.forall_mem_cons.2 ⟨subd8_0_758, List.forall_mem_cons.2 ⟨subd8_0_759, List.forall_mem_cons.2 ⟨subd8_0_760, List.forall_mem_cons.2 ⟨subd8_0_761, List.forall_mem_cons.2 ⟨subd8_0_762, List.forall_mem_cons.2 ⟨subd8_0_763, List.forall_mem_cons.2 ⟨subd8_0_764, List.forall_mem_cons.2 ⟨subd8_0_765, List.forall_mem_cons.2 ⟨subd8_0_766, List.forall_mem_cons.2 ⟨subd8_0_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_768 : subd8_0 [2, -3, -7] = true := by decide +kernel
theorem subd8_0_769 : subd8_0 [2, -3, -6] = true := by decide +kernel
theorem subd8_0_770 : subd8_0 [2, -3, -5] = true := by decide +kernel
theorem subd8_0_771 : subd8_0 [2, -3, -4] = true := by decide +kernel
theorem subd8_0_772 : subd8_0 [2, -3, -3] = true := by decide +kernel
theorem subd8_0_773 : subd8_0 [2, -3, -2] = true := by decide +kernel
theorem subd8_0_774 : subd8_0 [2, -3, -1] = true := by decide +kernel
theorem subd8_0_775 : subd8_0 [2, -3, 0] = true := by decide +kernel
theorem subd8_0_776 : subd8_0 [2, -3, 1] = true := by decide +kernel
theorem subd8_0_777 : subd8_0 [2, -3, 2] = true := by decide +kernel
theorem subd8_0_778 : subd8_0 [2, -3, 3] = true := by decide +kernel
theorem subd8_0_779 : subd8_0 [2, -3, 4] = true := by decide +kernel
theorem subd8_0_780 : subd8_0 [2, -3, 5] = true := by decide +kernel
theorem subd8_0_781 : subd8_0 [2, -2, -9] = true := by decide +kernel
theorem subd8_0_782 : subd8_0 [2, -2, -8] = true := by decide +kernel
theorem subd8_0_783 : subd8_0 [2, -2, -7] = true := by decide +kernel
theorem subd8_0_784 : subd8_0 [2, -2, -6] = true := by decide +kernel
theorem subd8_0_785 : subd8_0 [2, -2, -5] = true := by decide +kernel
theorem subd8_0_786 : subd8_0 [2, -2, -4] = true := by decide +kernel
theorem subd8_0_787 : subd8_0 [2, -2, -3] = true := by decide +kernel
theorem subd8_0_788 : subd8_0 [2, -2, -2] = true := by decide +kernel
theorem subd8_0_789 : subd8_0 [2, -2, -1] = true := by decide +kernel
theorem subd8_0_790 : subd8_0 [2, -2, 0] = true := by decide +kernel
theorem subd8_0_791 : subd8_0 [2, -2, 1] = true := by decide +kernel
theorem subd8_0_792 : subd8_0 [2, -2, 2] = true := by decide +kernel
theorem subd8_0_793 : subd8_0 [2, -2, 3] = true := by decide +kernel
theorem subd8_0_794 : subd8_0 [2, -2, 4] = true := by decide +kernel
theorem subd8_0_795 : subd8_0 [2, -2, 5] = true := by decide +kernel
theorem subd8_0_796 : subd8_0 [2, -2, 6] = true := by decide +kernel
theorem subd8_0_797 : subd8_0 [2, -1, -9] = true := by decide +kernel
theorem subd8_0_798 : subd8_0 [2, -1, -8] = true := by decide +kernel
theorem subd8_0_799 : subd8_0 [2, -1, -7] = true := by decide +kernel
theorem sbd8_0_24 : ∀ q ∈ blkd8_0_24, subd8_0 q = true := by
  unfold blkd8_0_24
  exact List.forall_mem_cons.2 ⟨subd8_0_768, List.forall_mem_cons.2 ⟨subd8_0_769, List.forall_mem_cons.2 ⟨subd8_0_770, List.forall_mem_cons.2 ⟨subd8_0_771, List.forall_mem_cons.2 ⟨subd8_0_772, List.forall_mem_cons.2 ⟨subd8_0_773, List.forall_mem_cons.2 ⟨subd8_0_774, List.forall_mem_cons.2 ⟨subd8_0_775, List.forall_mem_cons.2 ⟨subd8_0_776, List.forall_mem_cons.2 ⟨subd8_0_777, List.forall_mem_cons.2 ⟨subd8_0_778, List.forall_mem_cons.2 ⟨subd8_0_779, List.forall_mem_cons.2 ⟨subd8_0_780, List.forall_mem_cons.2 ⟨subd8_0_781, List.forall_mem_cons.2 ⟨subd8_0_782, List.forall_mem_cons.2 ⟨subd8_0_783, List.forall_mem_cons.2 ⟨subd8_0_784, List.forall_mem_cons.2 ⟨subd8_0_785, List.forall_mem_cons.2 ⟨subd8_0_786, List.forall_mem_cons.2 ⟨subd8_0_787, List.forall_mem_cons.2 ⟨subd8_0_788, List.forall_mem_cons.2 ⟨subd8_0_789, List.forall_mem_cons.2 ⟨subd8_0_790, List.forall_mem_cons.2 ⟨subd8_0_791, List.forall_mem_cons.2 ⟨subd8_0_792, List.forall_mem_cons.2 ⟨subd8_0_793, List.forall_mem_cons.2 ⟨subd8_0_794, List.forall_mem_cons.2 ⟨subd8_0_795, List.forall_mem_cons.2 ⟨subd8_0_796, List.forall_mem_cons.2 ⟨subd8_0_797, List.forall_mem_cons.2 ⟨subd8_0_798, List.forall_mem_cons.2 ⟨subd8_0_799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_800 : subd8_0 [2, -1, -6] = true := by decide +kernel
theorem subd8_0_801 : subd8_0 [2, -1, -5] = true := by decide +kernel
theorem subd8_0_802 : subd8_0 [2, -1, -4] = true := by decide +kernel
theorem subd8_0_803 : subd8_0 [2, -1, -3] = true := by decide +kernel
theorem subd8_0_804 : subd8_0 [2, -1, -2] = true := by decide +kernel
theorem subd8_0_805 : subd8_0 [2, -1, -1] = true := by decide +kernel
theorem subd8_0_806 : subd8_0 [2, -1, 0] = true := by decide +kernel
theorem subd8_0_807 : subd8_0 [2, -1, 1] = true := by decide +kernel
theorem subd8_0_808 : subd8_0 [2, -1, 2] = true := by decide +kernel
theorem subd8_0_809 : subd8_0 [2, -1, 3] = true := by decide +kernel
theorem subd8_0_810 : subd8_0 [2, -1, 4] = true := by decide +kernel
theorem subd8_0_811 : subd8_0 [2, -1, 5] = true := by decide +kernel
theorem subd8_0_812 : subd8_0 [2, -1, 6] = true := by decide +kernel
theorem subd8_0_813 : subd8_0 [2, -1, 7] = true := by decide +kernel
theorem subd8_0_814 : subd8_0 [2, 0, -9] = true := by decide +kernel
theorem subd8_0_815 : subd8_0 [2, 0, -8] = true := by decide +kernel
theorem subd8_0_816 : subd8_0 [2, 0, -7] = true := by decide +kernel
theorem subd8_0_817 : subd8_0 [2, 0, -6] = true := by decide +kernel
theorem subd8_0_818 : subd8_0 [2, 0, -5] = true := by decide +kernel
theorem subd8_0_819 : subd8_0 [2, 0, -4] = true := by decide +kernel
theorem subd8_0_820 : subd8_0 [2, 0, -3] = true := by decide +kernel
theorem subd8_0_821 : subd8_0 [2, 0, -2] = true := by decide +kernel
theorem subd8_0_822 : subd8_0 [2, 0, -1] = true := by decide +kernel
theorem subd8_0_823 : subd8_0 [2, 0, 0] = true := by decide +kernel
theorem subd8_0_824 : subd8_0 [2, 0, 1] = true := by decide +kernel
theorem subd8_0_825 : subd8_0 [2, 0, 2] = true := by decide +kernel
theorem subd8_0_826 : subd8_0 [2, 0, 3] = true := by decide +kernel
theorem subd8_0_827 : subd8_0 [2, 0, 4] = true := by decide +kernel
theorem subd8_0_828 : subd8_0 [2, 0, 5] = true := by decide +kernel
theorem subd8_0_829 : subd8_0 [2, 0, 6] = true := by decide +kernel
theorem subd8_0_830 : subd8_0 [2, 0, 7] = true := by decide +kernel
theorem subd8_0_831 : subd8_0 [2, 1, -9] = true := by decide +kernel
theorem sbd8_0_25 : ∀ q ∈ blkd8_0_25, subd8_0 q = true := by
  unfold blkd8_0_25
  exact List.forall_mem_cons.2 ⟨subd8_0_800, List.forall_mem_cons.2 ⟨subd8_0_801, List.forall_mem_cons.2 ⟨subd8_0_802, List.forall_mem_cons.2 ⟨subd8_0_803, List.forall_mem_cons.2 ⟨subd8_0_804, List.forall_mem_cons.2 ⟨subd8_0_805, List.forall_mem_cons.2 ⟨subd8_0_806, List.forall_mem_cons.2 ⟨subd8_0_807, List.forall_mem_cons.2 ⟨subd8_0_808, List.forall_mem_cons.2 ⟨subd8_0_809, List.forall_mem_cons.2 ⟨subd8_0_810, List.forall_mem_cons.2 ⟨subd8_0_811, List.forall_mem_cons.2 ⟨subd8_0_812, List.forall_mem_cons.2 ⟨subd8_0_813, List.forall_mem_cons.2 ⟨subd8_0_814, List.forall_mem_cons.2 ⟨subd8_0_815, List.forall_mem_cons.2 ⟨subd8_0_816, List.forall_mem_cons.2 ⟨subd8_0_817, List.forall_mem_cons.2 ⟨subd8_0_818, List.forall_mem_cons.2 ⟨subd8_0_819, List.forall_mem_cons.2 ⟨subd8_0_820, List.forall_mem_cons.2 ⟨subd8_0_821, List.forall_mem_cons.2 ⟨subd8_0_822, List.forall_mem_cons.2 ⟨subd8_0_823, List.forall_mem_cons.2 ⟨subd8_0_824, List.forall_mem_cons.2 ⟨subd8_0_825, List.forall_mem_cons.2 ⟨subd8_0_826, List.forall_mem_cons.2 ⟨subd8_0_827, List.forall_mem_cons.2 ⟨subd8_0_828, List.forall_mem_cons.2 ⟨subd8_0_829, List.forall_mem_cons.2 ⟨subd8_0_830, List.forall_mem_cons.2 ⟨subd8_0_831, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_832 : subd8_0 [2, 1, -8] = true := by decide +kernel
theorem subd8_0_833 : subd8_0 [2, 1, -7] = true := by decide +kernel
theorem subd8_0_834 : subd8_0 [2, 1, -6] = true := by decide +kernel
theorem subd8_0_835 : subd8_0 [2, 1, -5] = true := by decide +kernel
theorem subd8_0_836 : subd8_0 [2, 1, -4] = true := by decide +kernel
theorem subd8_0_837 : subd8_0 [2, 1, -3] = true := by decide +kernel
theorem subd8_0_838 : subd8_0 [2, 1, -2] = true := by decide +kernel
theorem subd8_0_839 : subd8_0 [2, 1, -1] = true := by decide +kernel
theorem subd8_0_840 : subd8_0 [2, 1, 0] = true := by decide +kernel
theorem subd8_0_841 : subd8_0 [2, 1, 1] = true := by decide +kernel
theorem subd8_0_842 : subd8_0 [2, 1, 2] = true := by decide +kernel
theorem subd8_0_843 : subd8_0 [2, 1, 3] = true := by decide +kernel
theorem subd8_0_844 : subd8_0 [2, 1, 4] = true := by decide +kernel
theorem subd8_0_845 : subd8_0 [2, 1, 5] = true := by decide +kernel
theorem subd8_0_846 : subd8_0 [2, 1, 6] = true := by decide +kernel
theorem subd8_0_847 : subd8_0 [2, 1, 7] = true := by decide +kernel
theorem subd8_0_848 : subd8_0 [2, 1, 8] = true := by decide +kernel
theorem subd8_0_849 : subd8_0 [2, 2, -9] = true := by decide +kernel
theorem subd8_0_850 : subd8_0 [2, 2, -8] = true := by decide +kernel
theorem subd8_0_851 : subd8_0 [2, 2, -7] = true := by decide +kernel
theorem subd8_0_852 : subd8_0 [2, 2, -6] = true := by decide +kernel
theorem subd8_0_853 : subd8_0 [2, 2, -5] = true := by decide +kernel
theorem subd8_0_854 : subd8_0 [2, 2, -4] = true := by decide +kernel
theorem subd8_0_855 : subd8_0 [2, 2, -3] = true := by decide +kernel
theorem subd8_0_856 : subd8_0 [2, 2, -2] = true := by decide +kernel
theorem subd8_0_857 : subd8_0 [2, 2, -1] = true := by decide +kernel
theorem subd8_0_858 : subd8_0 [2, 2, 0] = true := by decide +kernel
theorem subd8_0_859 : subd8_0 [2, 2, 1] = true := by decide +kernel
theorem subd8_0_860 : subd8_0 [2, 2, 2] = true := by decide +kernel
theorem subd8_0_861 : subd8_0 [2, 2, 3] = true := by decide +kernel
theorem subd8_0_862 : subd8_0 [2, 2, 4] = true := by decide +kernel
theorem subd8_0_863 : subd8_0 [2, 2, 5] = true := by decide +kernel
theorem sbd8_0_26 : ∀ q ∈ blkd8_0_26, subd8_0 q = true := by
  unfold blkd8_0_26
  exact List.forall_mem_cons.2 ⟨subd8_0_832, List.forall_mem_cons.2 ⟨subd8_0_833, List.forall_mem_cons.2 ⟨subd8_0_834, List.forall_mem_cons.2 ⟨subd8_0_835, List.forall_mem_cons.2 ⟨subd8_0_836, List.forall_mem_cons.2 ⟨subd8_0_837, List.forall_mem_cons.2 ⟨subd8_0_838, List.forall_mem_cons.2 ⟨subd8_0_839, List.forall_mem_cons.2 ⟨subd8_0_840, List.forall_mem_cons.2 ⟨subd8_0_841, List.forall_mem_cons.2 ⟨subd8_0_842, List.forall_mem_cons.2 ⟨subd8_0_843, List.forall_mem_cons.2 ⟨subd8_0_844, List.forall_mem_cons.2 ⟨subd8_0_845, List.forall_mem_cons.2 ⟨subd8_0_846, List.forall_mem_cons.2 ⟨subd8_0_847, List.forall_mem_cons.2 ⟨subd8_0_848, List.forall_mem_cons.2 ⟨subd8_0_849, List.forall_mem_cons.2 ⟨subd8_0_850, List.forall_mem_cons.2 ⟨subd8_0_851, List.forall_mem_cons.2 ⟨subd8_0_852, List.forall_mem_cons.2 ⟨subd8_0_853, List.forall_mem_cons.2 ⟨subd8_0_854, List.forall_mem_cons.2 ⟨subd8_0_855, List.forall_mem_cons.2 ⟨subd8_0_856, List.forall_mem_cons.2 ⟨subd8_0_857, List.forall_mem_cons.2 ⟨subd8_0_858, List.forall_mem_cons.2 ⟨subd8_0_859, List.forall_mem_cons.2 ⟨subd8_0_860, List.forall_mem_cons.2 ⟨subd8_0_861, List.forall_mem_cons.2 ⟨subd8_0_862, List.forall_mem_cons.2 ⟨subd8_0_863, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C093
