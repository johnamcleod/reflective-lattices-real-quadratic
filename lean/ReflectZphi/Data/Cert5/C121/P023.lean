import ReflectZphi.Data.Cert5.C121.Base

namespace ReflectZphi.Data.Cert5.C121

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_2_352 : subd8_2 [1, 2, -5] = true := by decide +kernel
theorem subd8_2_353 : subd8_2 [1, 2, -4] = true := by decide +kernel
theorem subd8_2_354 : subd8_2 [1, 2, -3] = true := by decide +kernel
theorem subd8_2_355 : subd8_2 [1, 2, -2] = true := by decide +kernel
theorem subd8_2_356 : subd8_2 [1, 2, -1] = true := by decide +kernel
theorem subd8_2_357 : subd8_2 [1, 2, 0] = true := by decide +kernel
theorem subd8_2_358 : subd8_2 [1, 2, 1] = true := by decide +kernel
theorem subd8_2_359 : subd8_2 [1, 2, 2] = true := by decide +kernel
theorem subd8_2_360 : subd8_2 [1, 2, 3] = true := by decide +kernel
theorem subd8_2_361 : subd8_2 [1, 2, 4] = true := by decide +kernel
theorem subd8_2_362 : subd8_2 [1, 2, 5] = true := by decide +kernel
theorem subd8_2_363 : subd8_2 [1, 2, 6] = true := by decide +kernel
theorem subd8_2_364 : subd8_2 [1, 3] = true := by decide +kernel
theorem subd8_2_365 : subd8_2 [1, 4] = true := by decide +kernel
theorem subd8_2_366 : subd8_2 [2, -6] = true := by decide +kernel
theorem subd8_2_367 : subd8_2 [2, -5] = true := by decide +kernel
theorem subd8_2_368 : subd8_2 [2, -4] = true := by decide +kernel
theorem subd8_2_369 : subd8_2 [2, -3] = true := by decide +kernel
theorem subd8_2_370 : subd8_2 [2, -2, -7] = true := by decide +kernel
theorem subd8_2_371 : subd8_2 [2, -2, -6] = true := by decide +kernel
theorem subd8_2_372 : subd8_2 [2, -2, -5] = true := by decide +kernel
theorem subd8_2_373 : subd8_2 [2, -2, -4] = true := by decide +kernel
theorem subd8_2_374 : subd8_2 [2, -2, -3] = true := by decide +kernel
theorem subd8_2_375 : subd8_2 [2, -2, -2] = true := by decide +kernel
theorem subd8_2_376 : subd8_2 [2, -2, -1] = true := by decide +kernel
theorem subd8_2_377 : subd8_2 [2, -2, 0] = true := by decide +kernel
theorem subd8_2_378 : subd8_2 [2, -2, 1] = true := by decide +kernel
theorem subd8_2_379 : subd8_2 [2, -2, 2] = true := by decide +kernel
theorem subd8_2_380 : subd8_2 [2, -2, 3] = true := by decide +kernel
theorem subd8_2_381 : subd8_2 [2, -2, 4] = true := by decide +kernel
theorem subd8_2_382 : subd8_2 [2, -2, 5] = true := by decide +kernel
theorem subd8_2_383 : subd8_2 [2, -2, 6] = true := by decide +kernel
theorem sbd8_2_11 : ∀ q ∈ blkd8_2_11, subd8_2 q = true := by
  unfold blkd8_2_11
  exact List.forall_mem_cons.2 ⟨subd8_2_352, List.forall_mem_cons.2 ⟨subd8_2_353, List.forall_mem_cons.2 ⟨subd8_2_354, List.forall_mem_cons.2 ⟨subd8_2_355, List.forall_mem_cons.2 ⟨subd8_2_356, List.forall_mem_cons.2 ⟨subd8_2_357, List.forall_mem_cons.2 ⟨subd8_2_358, List.forall_mem_cons.2 ⟨subd8_2_359, List.forall_mem_cons.2 ⟨subd8_2_360, List.forall_mem_cons.2 ⟨subd8_2_361, List.forall_mem_cons.2 ⟨subd8_2_362, List.forall_mem_cons.2 ⟨subd8_2_363, List.forall_mem_cons.2 ⟨subd8_2_364, List.forall_mem_cons.2 ⟨subd8_2_365, List.forall_mem_cons.2 ⟨subd8_2_366, List.forall_mem_cons.2 ⟨subd8_2_367, List.forall_mem_cons.2 ⟨subd8_2_368, List.forall_mem_cons.2 ⟨subd8_2_369, List.forall_mem_cons.2 ⟨subd8_2_370, List.forall_mem_cons.2 ⟨subd8_2_371, List.forall_mem_cons.2 ⟨subd8_2_372, List.forall_mem_cons.2 ⟨subd8_2_373, List.forall_mem_cons.2 ⟨subd8_2_374, List.forall_mem_cons.2 ⟨subd8_2_375, List.forall_mem_cons.2 ⟨subd8_2_376, List.forall_mem_cons.2 ⟨subd8_2_377, List.forall_mem_cons.2 ⟨subd8_2_378, List.forall_mem_cons.2 ⟨subd8_2_379, List.forall_mem_cons.2 ⟨subd8_2_380, List.forall_mem_cons.2 ⟨subd8_2_381, List.forall_mem_cons.2 ⟨subd8_2_382, List.forall_mem_cons.2 ⟨subd8_2_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_384 : subd8_2 [2, -1, -7] = true := by decide +kernel
theorem subd8_2_385 : subd8_2 [2, -1, -6] = true := by decide +kernel
theorem subd8_2_386 : subd8_2 [2, -1, -5] = true := by decide +kernel
theorem subd8_2_387 : subd8_2 [2, -1, -4] = true := by decide +kernel
theorem subd8_2_388 : subd8_2 [2, -1, -3] = true := by decide +kernel
theorem subd8_2_389 : subd8_2 [2, -1, -2] = true := by decide +kernel
theorem subd8_2_390 : subd8_2 [2, -1, -1] = true := by decide +kernel
theorem subd8_2_391 : subd8_2 [2, -1, 0] = true := by decide +kernel
theorem subd8_2_392 : subd8_2 [2, -1, 1] = true := by decide +kernel
theorem subd8_2_393 : subd8_2 [2, -1, 2] = true := by decide +kernel
theorem subd8_2_394 : subd8_2 [2, -1, 3] = true := by decide +kernel
theorem subd8_2_395 : subd8_2 [2, -1, 4] = true := by decide +kernel
theorem subd8_2_396 : subd8_2 [2, -1, 5] = true := by decide +kernel
theorem subd8_2_397 : subd8_2 [2, -1, 6] = true := by decide +kernel
theorem subd8_2_398 : subd8_2 [2, -1, 7] = true := by decide +kernel
theorem subd8_2_399 : subd8_2 [2, 0, -7] = true := by decide +kernel
theorem subd8_2_400 : subd8_2 [2, 0, -6] = true := by decide +kernel
theorem subd8_2_401 : subd8_2 [2, 0, -5] = true := by decide +kernel
theorem subd8_2_402 : subd8_2 [2, 0, -4] = true := by decide +kernel
theorem subd8_2_403 : subd8_2 [2, 0, -3] = true := by decide +kernel
theorem subd8_2_404 : subd8_2 [2, 0, -2] = true := by decide +kernel
theorem subd8_2_405 : subd8_2 [2, 0, -1] = true := by decide +kernel
theorem subd8_2_406 : subd8_2 [2, 0, 0] = true := by decide +kernel
theorem subd8_2_407 : subd8_2 [2, 0, 1] = true := by decide +kernel
theorem subd8_2_408 : subd8_2 [2, 0, 2] = true := by decide +kernel
theorem subd8_2_409 : subd8_2 [2, 0, 3] = true := by decide +kernel
theorem subd8_2_410 : subd8_2 [2, 0, 4] = true := by decide +kernel
theorem subd8_2_411 : subd8_2 [2, 0, 5] = true := by decide +kernel
theorem subd8_2_412 : subd8_2 [2, 0, 6] = true := by decide +kernel
theorem subd8_2_413 : subd8_2 [2, 1, -7] = true := by decide +kernel
theorem subd8_2_414 : subd8_2 [2, 1, -6] = true := by decide +kernel
theorem subd8_2_415 : subd8_2 [2, 1, -5] = true := by decide +kernel
theorem sbd8_2_12 : ∀ q ∈ blkd8_2_12, subd8_2 q = true := by
  unfold blkd8_2_12
  exact List.forall_mem_cons.2 ⟨subd8_2_384, List.forall_mem_cons.2 ⟨subd8_2_385, List.forall_mem_cons.2 ⟨subd8_2_386, List.forall_mem_cons.2 ⟨subd8_2_387, List.forall_mem_cons.2 ⟨subd8_2_388, List.forall_mem_cons.2 ⟨subd8_2_389, List.forall_mem_cons.2 ⟨subd8_2_390, List.forall_mem_cons.2 ⟨subd8_2_391, List.forall_mem_cons.2 ⟨subd8_2_392, List.forall_mem_cons.2 ⟨subd8_2_393, List.forall_mem_cons.2 ⟨subd8_2_394, List.forall_mem_cons.2 ⟨subd8_2_395, List.forall_mem_cons.2 ⟨subd8_2_396, List.forall_mem_cons.2 ⟨subd8_2_397, List.forall_mem_cons.2 ⟨subd8_2_398, List.forall_mem_cons.2 ⟨subd8_2_399, List.forall_mem_cons.2 ⟨subd8_2_400, List.forall_mem_cons.2 ⟨subd8_2_401, List.forall_mem_cons.2 ⟨subd8_2_402, List.forall_mem_cons.2 ⟨subd8_2_403, List.forall_mem_cons.2 ⟨subd8_2_404, List.forall_mem_cons.2 ⟨subd8_2_405, List.forall_mem_cons.2 ⟨subd8_2_406, List.forall_mem_cons.2 ⟨subd8_2_407, List.forall_mem_cons.2 ⟨subd8_2_408, List.forall_mem_cons.2 ⟨subd8_2_409, List.forall_mem_cons.2 ⟨subd8_2_410, List.forall_mem_cons.2 ⟨subd8_2_411, List.forall_mem_cons.2 ⟨subd8_2_412, List.forall_mem_cons.2 ⟨subd8_2_413, List.forall_mem_cons.2 ⟨subd8_2_414, List.forall_mem_cons.2 ⟨subd8_2_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_416 : subd8_2 [2, 1, -4] = true := by decide +kernel
theorem subd8_2_417 : subd8_2 [2, 1, -3] = true := by decide +kernel
theorem subd8_2_418 : subd8_2 [2, 1, -2] = true := by decide +kernel
theorem subd8_2_419 : subd8_2 [2, 1, -1] = true := by decide +kernel
theorem subd8_2_420 : subd8_2 [2, 1, 0] = true := by decide +kernel
theorem subd8_2_421 : subd8_2 [2, 1, 1] = true := by decide +kernel
theorem subd8_2_422 : subd8_2 [2, 1, 2] = true := by decide +kernel
theorem subd8_2_423 : subd8_2 [2, 1, 3] = true := by decide +kernel
theorem subd8_2_424 : subd8_2 [2, 1, 4] = true := by decide +kernel
theorem subd8_2_425 : subd8_2 [2, 1, 5] = true := by decide +kernel
theorem subd8_2_426 : subd8_2 [2, 1, 6] = true := by decide +kernel
theorem subd8_2_427 : subd8_2 [2, 2] = true := by decide +kernel
theorem subd8_2_428 : subd8_2 [2, 3] = true := by decide +kernel
theorem subd8_2_429 : subd8_2 [2, 4] = true := by decide +kernel
theorem subd8_2_430 : subd8_2 [3, -6] = true := by decide +kernel
theorem subd8_2_431 : subd8_2 [3, -5] = true := by decide +kernel
theorem subd8_2_432 : subd8_2 [3, -4] = true := by decide +kernel
theorem subd8_2_433 : subd8_2 [3, -3] = true := by decide +kernel
theorem subd8_2_434 : subd8_2 [3, -2] = true := by decide +kernel
theorem subd8_2_435 : subd8_2 [3, -1, -7] = true := by decide +kernel
theorem subd8_2_436 : subd8_2 [3, -1, -6] = true := by decide +kernel
theorem subd8_2_437 : subd8_2 [3, -1, -5] = true := by decide +kernel
theorem subd8_2_438 : subd8_2 [3, -1, -4] = true := by decide +kernel
theorem subd8_2_439 : subd8_2 [3, -1, -3] = true := by decide +kernel
theorem subd8_2_440 : subd8_2 [3, -1, -2] = true := by decide +kernel
theorem subd8_2_441 : subd8_2 [3, -1, -1] = true := by decide +kernel
theorem subd8_2_442 : subd8_2 [3, -1, 0] = true := by decide +kernel
theorem subd8_2_443 : subd8_2 [3, -1, 1] = true := by decide +kernel
theorem subd8_2_444 : subd8_2 [3, -1, 2] = true := by decide +kernel
theorem subd8_2_445 : subd8_2 [3, -1, 3] = true := by decide +kernel
theorem subd8_2_446 : subd8_2 [3, -1, 4] = true := by decide +kernel
theorem subd8_2_447 : subd8_2 [3, -1, 5] = true := by decide +kernel
theorem sbd8_2_13 : ∀ q ∈ blkd8_2_13, subd8_2 q = true := by
  unfold blkd8_2_13
  exact List.forall_mem_cons.2 ⟨subd8_2_416, List.forall_mem_cons.2 ⟨subd8_2_417, List.forall_mem_cons.2 ⟨subd8_2_418, List.forall_mem_cons.2 ⟨subd8_2_419, List.forall_mem_cons.2 ⟨subd8_2_420, List.forall_mem_cons.2 ⟨subd8_2_421, List.forall_mem_cons.2 ⟨subd8_2_422, List.forall_mem_cons.2 ⟨subd8_2_423, List.forall_mem_cons.2 ⟨subd8_2_424, List.forall_mem_cons.2 ⟨subd8_2_425, List.forall_mem_cons.2 ⟨subd8_2_426, List.forall_mem_cons.2 ⟨subd8_2_427, List.forall_mem_cons.2 ⟨subd8_2_428, List.forall_mem_cons.2 ⟨subd8_2_429, List.forall_mem_cons.2 ⟨subd8_2_430, List.forall_mem_cons.2 ⟨subd8_2_431, List.forall_mem_cons.2 ⟨subd8_2_432, List.forall_mem_cons.2 ⟨subd8_2_433, List.forall_mem_cons.2 ⟨subd8_2_434, List.forall_mem_cons.2 ⟨subd8_2_435, List.forall_mem_cons.2 ⟨subd8_2_436, List.forall_mem_cons.2 ⟨subd8_2_437, List.forall_mem_cons.2 ⟨subd8_2_438, List.forall_mem_cons.2 ⟨subd8_2_439, List.forall_mem_cons.2 ⟨subd8_2_440, List.forall_mem_cons.2 ⟨subd8_2_441, List.forall_mem_cons.2 ⟨subd8_2_442, List.forall_mem_cons.2 ⟨subd8_2_443, List.forall_mem_cons.2 ⟨subd8_2_444, List.forall_mem_cons.2 ⟨subd8_2_445, List.forall_mem_cons.2 ⟨subd8_2_446, List.forall_mem_cons.2 ⟨subd8_2_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_448 : subd8_2 [3, -1, 6] = true := by decide +kernel
theorem subd8_2_449 : subd8_2 [3, 0, -7] = true := by decide +kernel
theorem subd8_2_450 : subd8_2 [3, 0, -6] = true := by decide +kernel
theorem subd8_2_451 : subd8_2 [3, 0, -5] = true := by decide +kernel
theorem subd8_2_452 : subd8_2 [3, 0, -4] = true := by decide +kernel
theorem subd8_2_453 : subd8_2 [3, 0, -3] = true := by decide +kernel
theorem subd8_2_454 : subd8_2 [3, 0, -2] = true := by decide +kernel
theorem subd8_2_455 : subd8_2 [3, 0, -1] = true := by decide +kernel
theorem subd8_2_456 : subd8_2 [3, 0, 0] = true := by decide +kernel
theorem subd8_2_457 : subd8_2 [3, 0, 1] = true := by decide +kernel
theorem subd8_2_458 : subd8_2 [3, 0, 2] = true := by decide +kernel
theorem subd8_2_459 : subd8_2 [3, 0, 3] = true := by decide +kernel
theorem subd8_2_460 : subd8_2 [3, 0, 4] = true := by decide +kernel
theorem subd8_2_461 : subd8_2 [3, 0, 5] = true := by decide +kernel
theorem subd8_2_462 : subd8_2 [3, 0, 6] = true := by decide +kernel
theorem subd8_2_463 : subd8_2 [3, 1] = true := by decide +kernel
theorem subd8_2_464 : subd8_2 [3, 2] = true := by decide +kernel
theorem subd8_2_465 : subd8_2 [3, 3] = true := by decide +kernel
theorem subd8_2_466 : subd8_2 [4, -5] = true := by decide +kernel
theorem subd8_2_467 : subd8_2 [4, -4] = true := by decide +kernel
theorem subd8_2_468 : subd8_2 [4, -3] = true := by decide +kernel
theorem subd8_2_469 : subd8_2 [4, -2] = true := by decide +kernel
theorem subd8_2_470 : subd8_2 [4, -1] = true := by decide +kernel
theorem subd8_2_471 : subd8_2 [4, 0] = true := by decide +kernel
theorem subd8_2_472 : subd8_2 [4, 1] = true := by decide +kernel
theorem subd8_2_473 : subd8_2 [4, 2] = true := by decide +kernel
theorem subd8_2_474 : subd8_2 [4, 3] = true := by decide +kernel
theorem subd8_2_475 : subd8_2 [5, -5] = true := by decide +kernel
theorem subd8_2_476 : subd8_2 [5, -4] = true := by decide +kernel
theorem subd8_2_477 : subd8_2 [5, -3] = true := by decide +kernel
theorem subd8_2_478 : subd8_2 [5, -2] = true := by decide +kernel
theorem subd8_2_479 : subd8_2 [5, -1] = true := by decide +kernel
theorem sbd8_2_14 : ∀ q ∈ blkd8_2_14, subd8_2 q = true := by
  unfold blkd8_2_14
  exact List.forall_mem_cons.2 ⟨subd8_2_448, List.forall_mem_cons.2 ⟨subd8_2_449, List.forall_mem_cons.2 ⟨subd8_2_450, List.forall_mem_cons.2 ⟨subd8_2_451, List.forall_mem_cons.2 ⟨subd8_2_452, List.forall_mem_cons.2 ⟨subd8_2_453, List.forall_mem_cons.2 ⟨subd8_2_454, List.forall_mem_cons.2 ⟨subd8_2_455, List.forall_mem_cons.2 ⟨subd8_2_456, List.forall_mem_cons.2 ⟨subd8_2_457, List.forall_mem_cons.2 ⟨subd8_2_458, List.forall_mem_cons.2 ⟨subd8_2_459, List.forall_mem_cons.2 ⟨subd8_2_460, List.forall_mem_cons.2 ⟨subd8_2_461, List.forall_mem_cons.2 ⟨subd8_2_462, List.forall_mem_cons.2 ⟨subd8_2_463, List.forall_mem_cons.2 ⟨subd8_2_464, List.forall_mem_cons.2 ⟨subd8_2_465, List.forall_mem_cons.2 ⟨subd8_2_466, List.forall_mem_cons.2 ⟨subd8_2_467, List.forall_mem_cons.2 ⟨subd8_2_468, List.forall_mem_cons.2 ⟨subd8_2_469, List.forall_mem_cons.2 ⟨subd8_2_470, List.forall_mem_cons.2 ⟨subd8_2_471, List.forall_mem_cons.2 ⟨subd8_2_472, List.forall_mem_cons.2 ⟨subd8_2_473, List.forall_mem_cons.2 ⟨subd8_2_474, List.forall_mem_cons.2 ⟨subd8_2_475, List.forall_mem_cons.2 ⟨subd8_2_476, List.forall_mem_cons.2 ⟨subd8_2_477, List.forall_mem_cons.2 ⟨subd8_2_478, List.forall_mem_cons.2 ⟨subd8_2_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_2_480 : subd8_2 [5, 0] = true := by decide +kernel
theorem subd8_2_481 : subd8_2 [5, 1] = true := by decide +kernel
theorem subd8_2_482 : subd8_2 [6] = true := by decide +kernel
theorem sbd8_2_15 : ∀ q ∈ blkd8_2_15, subd8_2 q = true := by
  unfold blkd8_2_15
  exact List.forall_mem_cons.2 ⟨subd8_2_480, List.forall_mem_cons.2 ⟨subd8_2_481, List.forall_mem_cons.2 ⟨subd8_2_482, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd8_3 : ldCheck G d8_3.U d8_3.ms ldd8_3 = true := by decide +kernel
theorem pre_okd8_3 : subPre G cell8 d8_3 = true := by decide +kernel
theorem subd8_3_0 : subd8_3 [-3] = true := by decide +kernel
theorem subd8_3_1 : subd8_3 [-2, -3] = true := by decide +kernel
theorem subd8_3_2 : subd8_3 [-2, -2] = true := by decide +kernel
theorem subd8_3_3 : subd8_3 [-2, -1] = true := by decide +kernel
theorem subd8_3_4 : subd8_3 [-2, 0] = true := by decide +kernel
theorem subd8_3_5 : subd8_3 [-2, 1] = true := by decide +kernel
theorem subd8_3_6 : subd8_3 [-2, 2] = true := by decide +kernel
theorem subd8_3_7 : subd8_3 [-2, 3] = true := by decide +kernel
theorem subd8_3_8 : subd8_3 [-1, -4] = true := by decide +kernel
theorem subd8_3_9 : subd8_3 [-1, -3] = true := by decide +kernel
theorem subd8_3_10 : subd8_3 [-1, -2] = true := by decide +kernel
theorem subd8_3_11 : subd8_3 [-1, -1] = true := by decide +kernel
theorem subd8_3_12 : subd8_3 [-1, 0] = true := by decide +kernel
theorem subd8_3_13 : subd8_3 [-1, 1] = true := by decide +kernel
theorem subd8_3_14 : subd8_3 [-1, 2] = true := by decide +kernel
theorem subd8_3_15 : subd8_3 [-1, 3] = true := by decide +kernel
theorem subd8_3_16 : subd8_3 [0, -4] = true := by decide +kernel
theorem subd8_3_17 : subd8_3 [0, -3] = true := by decide +kernel
theorem subd8_3_18 : subd8_3 [0, -2] = true := by decide +kernel
theorem subd8_3_19 : subd8_3 [0, -1] = true := by decide +kernel
theorem subd8_3_20 : subd8_3 [0, 0] = true := by decide +kernel
theorem subd8_3_21 : subd8_3 [0, 1] = true := by decide +kernel
theorem subd8_3_22 : subd8_3 [0, 2] = true := by decide +kernel
theorem subd8_3_23 : subd8_3 [0, 3] = true := by decide +kernel
theorem subd8_3_24 : subd8_3 [1, -4] = true := by decide +kernel
theorem subd8_3_25 : subd8_3 [1, -3] = true := by decide +kernel
theorem subd8_3_26 : subd8_3 [1, -2] = true := by decide +kernel
theorem subd8_3_27 : subd8_3 [1, -1] = true := by decide +kernel
theorem subd8_3_28 : subd8_3 [1, 0] = true := by decide +kernel
theorem subd8_3_29 : subd8_3 [1, 1] = true := by decide +kernel
theorem subd8_3_30 : subd8_3 [1, 2] = true := by decide +kernel
theorem subd8_3_31 : subd8_3 [1, 3] = true := by decide +kernel
theorem sbd8_3_0 : ∀ q ∈ blkd8_3_0, subd8_3 q = true := by
  unfold blkd8_3_0
  exact List.forall_mem_cons.2 ⟨subd8_3_0, List.forall_mem_cons.2 ⟨subd8_3_1, List.forall_mem_cons.2 ⟨subd8_3_2, List.forall_mem_cons.2 ⟨subd8_3_3, List.forall_mem_cons.2 ⟨subd8_3_4, List.forall_mem_cons.2 ⟨subd8_3_5, List.forall_mem_cons.2 ⟨subd8_3_6, List.forall_mem_cons.2 ⟨subd8_3_7, List.forall_mem_cons.2 ⟨subd8_3_8, List.forall_mem_cons.2 ⟨subd8_3_9, List.forall_mem_cons.2 ⟨subd8_3_10, List.forall_mem_cons.2 ⟨subd8_3_11, List.forall_mem_cons.2 ⟨subd8_3_12, List.forall_mem_cons.2 ⟨subd8_3_13, List.forall_mem_cons.2 ⟨subd8_3_14, List.forall_mem_cons.2 ⟨subd8_3_15, List.forall_mem_cons.2 ⟨subd8_3_16, List.forall_mem_cons.2 ⟨subd8_3_17, List.forall_mem_cons.2 ⟨subd8_3_18, List.forall_mem_cons.2 ⟨subd8_3_19, List.forall_mem_cons.2 ⟨subd8_3_20, List.forall_mem_cons.2 ⟨subd8_3_21, List.forall_mem_cons.2 ⟨subd8_3_22, List.forall_mem_cons.2 ⟨subd8_3_23, List.forall_mem_cons.2 ⟨subd8_3_24, List.forall_mem_cons.2 ⟨subd8_3_25, List.forall_mem_cons.2 ⟨subd8_3_26, List.forall_mem_cons.2 ⟨subd8_3_27, List.forall_mem_cons.2 ⟨subd8_3_28, List.forall_mem_cons.2 ⟨subd8_3_29, List.forall_mem_cons.2 ⟨subd8_3_30, List.forall_mem_cons.2 ⟨subd8_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_32 : subd8_3 [2, -4] = true := by decide +kernel
theorem subd8_3_33 : subd8_3 [2, -3] = true := by decide +kernel
theorem subd8_3_34 : subd8_3 [2, -2] = true := by decide +kernel
theorem subd8_3_35 : subd8_3 [2, -1] = true := by decide +kernel
theorem subd8_3_36 : subd8_3 [2, 0] = true := by decide +kernel
theorem subd8_3_37 : subd8_3 [2, 1] = true := by decide +kernel
theorem subd8_3_38 : subd8_3 [2, 2] = true := by decide +kernel
theorem subd8_3_39 : subd8_3 [3] = true := by decide +kernel
theorem sbd8_3_1 : ∀ q ∈ blkd8_3_1, subd8_3 q = true := by
  unfold blkd8_3_1
  exact List.forall_mem_cons.2 ⟨subd8_3_32, List.forall_mem_cons.2 ⟨subd8_3_33, List.forall_mem_cons.2 ⟨subd8_3_34, List.forall_mem_cons.2 ⟨subd8_3_35, List.forall_mem_cons.2 ⟨subd8_3_36, List.forall_mem_cons.2 ⟨subd8_3_37, List.forall_mem_cons.2 ⟨subd8_3_38, List.forall_mem_cons.2 ⟨subd8_3_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_0 : ldCheck G d9_0.U d9_0.ms ldd9_0 = true := by decide +kernel
theorem pre_okd9_0 : subPre G cell9 d9_0 = true := by decide +kernel
theorem subd9_0_0 : subd9_0 [-1] = true := by decide +kernel
theorem subd9_0_1 : subd9_0 [0, -2] = true := by decide +kernel
theorem subd9_0_2 : subd9_0 [0, -1] = true := by decide +kernel
theorem subd9_0_3 : subd9_0 [0, 0] = true := by decide +kernel
theorem subd9_0_4 : subd9_0 [0, 1] = true := by decide +kernel
theorem subd9_0_5 : subd9_0 [1] = true := by decide +kernel
theorem sbd9_0_0 : ∀ q ∈ blkd9_0_0, subd9_0 q = true := by
  unfold blkd9_0_0
  exact List.forall_mem_cons.2 ⟨subd9_0_0, List.forall_mem_cons.2 ⟨subd9_0_1, List.forall_mem_cons.2 ⟨subd9_0_2, List.forall_mem_cons.2 ⟨subd9_0_3, List.forall_mem_cons.2 ⟨subd9_0_4, List.forall_mem_cons.2 ⟨subd9_0_5, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd9_1 : ldCheck G d9_1.U d9_1.ms ldd9_1 = true := by decide +kernel
theorem pre_okd9_1 : subPre G cell9 d9_1 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C121
